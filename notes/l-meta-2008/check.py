"""Compile the enclosed sources in dependency order and independently replay each module."""
import concurrent.futures
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

SOURCE = Path(__file__).resolve().parent

def check(directory, requested):
    scratch = Path(directory).resolve()
    env = dict(os.environ, LEAN_PATH=str(scratch) + os.pathsep + os.environ.get("LEAN_PATH", ""))
    sources = {p.stem: p for p in SOURCE.glob("*.lean")}
    dependencies = {m: set(re.findall(r"^import\s+(\w+)", p.read_text(), re.M)) & sources.keys()
                    for m, p in sources.items()}
    finished = set()
    order = []
    def build(module):
        if module in finished:
            return
        for parent in sorted(dependencies[module]):
            build(parent)
        finished.add(module)
        if requested and module not in requested and (scratch / (module + ".olean")).is_file():
            return
        print("Compiling", module, flush=True)
        subprocess.run(["lean", "-j1", "-R", str(SOURCE), "-o", str(scratch / (module + ".olean")),
                        str(sources[module])], env=env, check=True)
        order.append(module)
    for m in sorted(requested or sources.keys()):
        build(m)
    def replay(module):
        subprocess.run(["leanchecker", "-v", module], env=env, check=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        list(executor.map(replay, order))
    print(f"Verified {len(order)} modules.", flush=True)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        check(sys.argv[1], set(sys.argv[2:]))
    else:
        with tempfile.TemporaryDirectory() as scratch:
            check(scratch, set())
