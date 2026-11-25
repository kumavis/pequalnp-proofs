"""Check genuine AND sources and same-edge background extensions on two planes."""

from functools import lru_cache
from itertools import combinations

from projection_circuits import Circuit, neighbors, product


def mask(values):
    return sum(1 << i for i in values)


def subsets(indices, cap):
    for size in range(cap + 1):
        for chosen in combinations(indices, size):
            yield mask(chosen)


def make_model(q, modulus, padded):
    n = q * q + q + 1
    field = [[product(a, b, q, modulus) for b in range(q)] for a in range(q)]
    rows = [mask(neighbors(q, p, field)) for p in range(n)]
    circuit = Circuit(2 * n)
    points = list(range(n))
    lines = list(range(n, 2 * n))
    if padded:
        some_point = circuit.fold("or", points)
        some_line = circuit.fold("or", lines)
        common = circuit.gate("and", some_point, some_line)
        points = [circuit.gate("and", p, common) for p in points]
        lines = [circuit.gate("and", l, common) for l in lines]
    answers = []
    for p in range(n):
        hits = circuit.fold("or", [lines[l] for l in range(n) if rows[p] >> l & 1])
        answers.append(circuit.gate("and", points[p], hits))
    root = circuit.fold("or", answers)
    return rows, circuit, root


def examine(q, modulus, padded, with_background):
    rows, circuit, root = make_model(q, modulus, padded)
    n = len(rows)
    background_x = 1 if with_background else 0
    nonneighbor = next(l for l in range(n) if not rows[0] >> l & 1)
    background_y = 1 << nonneighbor if with_background else 0
    cap = 1

    @lru_cache(maxsize=None)
    def evaluate(x, y):
        xs = [(x >> p) & 1 for p in range(n)]
        ys = [(y >> l) & 1 for l in range(n)]
        result = circuit.evaluate(xs + ys)
        assert result[root] == any(xs[p] and rows[p] & y for p in range(n))
        return result

    def active_coordinates(x, y):
        pts = [p for p in range(n) if not rows[p] & y]
        lines = [l for l in range(n) if not any(x >> p & 1 and rows[p] >> l & 1 for p in range(n))]
        return pts, lines

    pts, lines = active_coordinates(background_x, background_y)
    edges = [(p, l) for p in pts for l in lines if rows[p] >> l & 1]
    protected_count = 0
    extensions = 0
    for p, l in edges:
        point_only = evaluate(background_x | (1 << p), background_y)
        line_only = evaluate(background_x, background_y | (1 << l))
        avoid_p = [r for r in lines if not rows[p] >> r & 1]
        avoid_l = [u for u in pts if not rows[u] >> l & 1]
        genuine = []
        for ix, (op, a, b) in enumerate(circuit.gates):
            if op == "and":
                for point_input, line_input in [(a, b), (b, a)]:
                    if (point_only[point_input] and line_only[line_input]
                            and not point_only[line_input] and not line_only[point_input]):
                        genuine.append((2 * n + ix, point_input, line_input))
        assert genuine
        fixes = []
        for gate, a, b in genuine:
            y = next((y for y in subsets(avoid_p, cap) if evaluate(background_x, background_y | y)[b]), None)
            if y is not None:
                fixes.append((gate, background_x, background_y | y))
                continue
            x = next((x for x in subsets(avoid_l, cap) if evaluate(background_x | x, background_y)[a]), None)
            if x is not None:
                fixes.append((gate, background_x | x, background_y))
        if len(fixes) < len(genuine):
            protected_count += 1
            continue
        for gate, x, y in fixes:
            assert not evaluate(x, y)[root]
            new_pts, new_lines = active_coordinates(x, y)
            assert p in new_pts and l in new_lines
            assert evaluate(x | (1 << p), y)[gate] or evaluate(x, y | (1 << l))[gate]
            extensions += 1
    name = "guarded" if padded else "direct"
    start = "one nonincident pair" if with_background else "empty"
    print(f"q={q}, {name}, {start}: {protected_count}/{len(edges)} surviving edges have "
          f"a protected genuine source; {extensions} same-edge gate exclusions checked.")
    assert protected_count == (0 if padded and not with_background else len(edges))


if __name__ == "__main__":
    for order, modulus in [(2, 0b11), (4, 0b111)]:
        for guarded, nonempty in [(False, False), (True, False), (True, True)]:
            examine(order, modulus, guarded, nonempty)
