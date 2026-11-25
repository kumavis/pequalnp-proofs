#!/usr/bin/env bash
set -euo pipefail
source_dir=$(cd "$(dirname "$0")" && pwd)
cd "${1:?Supply the path to the project’s built lean directory}"
lake env python3 "$source_dir/check.py"
