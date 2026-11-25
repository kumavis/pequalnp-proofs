"""Generate and exhaustively test normalized monotone incidence circuits.

A nonvertical affine line of slope a and intercept c has index a*q+c.
Verticals follow, then the line at infinity. Points (x,y) have index x*q+y,
followed by the q slope directions and the vertical direction. Both variable
sets are allowed to be arbitrary, subject to the stated cap on selected lines.
"""
from itertools import combinations
from math import comb


def product(a, b, q, polynomial):
    answer = 0
    while b:
        if b & 1:
            answer ^= a
        b >>= 1
        a <<= 1
        if a & q:
            a ^= polynomial
    return answer


def cosets(subgroup, q):
    """Return additive coset representatives, and the representative at each x."""
    rep = [-1] * q
    representatives = []
    for x in range(q):
        if rep[x] >= 0:
            continue
        representatives.append(x)
        for u in subgroup:
            rep[x ^ u] = x
    return representatives, rep


class Circuit:
    def __init__(self, inputs):
        self.inputs = inputs
        self.gates = []

    def gate(self, op, a, b):
        if a == b:
            return a
        wire = self.inputs + len(self.gates)
        a, b = sorted((a, b))
        assert 0 <= a < b < wire
        self.gates.append((op, a, b))
        return wire

    def fold(self, op, terms):
        it = iter(terms)
        wire = next(it)
        for term in it:
            wire = self.gate(op, wire, term)
        return wire

    def evaluate(self, inputs):
        assert len(inputs) == self.inputs
        values = list(inputs)
        for op, a, b in self.gates:
            values.append((values[a] | values[b]) if op == "or" else (values[a] & values[b]))
        return values


def build(q, polynomial, b, t):
    n = q*q + q + 1
    c = Circuit(2*n)
    mul = [[product(x, y, q, polynomial) for y in range(q)] for x in range(q)]
    assert all(len(set(row)) == q for row in mul[1:]), "modulus is reducible"

    def power(z, e):
        out = 1
        for _ in range(e):
            out = mul[out][z]
        return out

    base = [z for z in range(q) if power(z, b) == z]
    assert len(base) == b
    slopes, _ = cosets(base, q)
    kernels = sorted({tuple(sorted(mul[k][u] for u in base)) for k in range(1, q)})
    assert len(kernels) == (q-1)//(b-1)
    assert 1 <= t < len(kernels)
    kernels = kernels[:t+1]
    projected = [[] for _ in range(q*q)]
    for kernel in kernels:
        coordinates, rep = cosets(kernel, q)
        # First group intercepts with the same residue modulo the kernel.
        intercept = {(a, z): c.fold("or", (n+a*q+(z^v) for v in kernel))
                     for a in range(q) for z in coordinates}
        # Slopes are A+u, where u is in the base field. For x=X+v, u*v
        # vanishes modulo this kernel, so the pooling is valid for the whole tile.
        pooled = {(A, X, w): c.fold("or", (intercept[A^u, rep[w ^ mul[u][X]]] for u in base))
                  for A in slopes for X in coordinates for w in coordinates}
        flags = {(x, z): c.fold("or", (pooled[A, rep[x], rep[z ^ mul[A][x]]] for A in slopes))
                 for x in range(q) for z in coordinates}
        for x in range(q):
            for y in range(q):
                projected[x*q+y].append(flags[x, rep[y]])

    hits = [c.gate("or", c.fold("and", projected[x*q+y]), n+q*q+x)
            for x in range(q) for y in range(q)]
    for a in range(q):
        incident = [n+a*q+d for d in range(q)] + [2*n-1]
        hits.append(c.fold("or", incident))
    hits.append(c.fold("or", range(n+q*q, 2*n)))
    root = c.fold("or", (c.gate("and", p, hits[p]) for p in range(n)))
    return c, hits, root, kernels, mul


def size(q, b, t):
    h = q // b
    n = q*q + q + 1
    per_projection = q*h*(b-1) + h**3*(b-1) + q*h*(h-1)
    # Finite-point ANDs, vertical flags, all flags at infinity, output dot product.
    return (t+1)*per_projection + t*q*q + 2*q*q + q + 2*n-1


def neighbors(q, p, mul):
    if p < q*q:
        x, y = divmod(p, q)
        return [a*q+(y ^ mul[a][x]) for a in range(q)] + [q*q+x]
    if p == q*q+q:
        return list(range(q*q, q*q+q+1))
    return list(range((p-q*q)*q, (p-q*q+1)*q)) + [q*q+q]


def check(q, polynomial, b, t):
    n = q*q + q + 1
    circuit, hits, root, kernels, mul = build(q, polynomial, b, t)
    assert len(circuit.gates) == size(q, b, t)
    count = sum(comb(n, j) for j in range(t+1))
    extent = (count + 7)//8
    packed = [bytearray(extent) for _ in range(n)]
    idx = 0
    for j in range(t+1):
        for selection in combinations(range(n), j):
            for line in selection:
                packed[line][idx//8] |= 1 << (idx % 8)
            idx += 1
    assert idx == count
    line_values = [int.from_bytes(v, "little") for v in packed]
    values = circuit.evaluate([0]*n + line_values)
    for p, hit in enumerate(hits):
        expected = 0
        for ell in neighbors(q, p, mul):
            expected |= line_values[ell]
        assert values[hit] == expected, (q, t, p)
    # For these horizontal lines every projection gives a hit at the origin,
    # even though the unprojected lines miss it. The cap is sharp for this circuit.
    bad_lines = [next(z for z in K if z) for K in kernels]
    assert len(set(bad_lines)) == t+1 and set(bad_lines).isdisjoint(neighbors(q, 0, mul))
    values = circuit.evaluate([1] + [0]*(n-1) + [int(i in bad_lines) for i in range(n)])
    assert values[root] == 1
    print(f"q={q}, b={b}, cap={t}: {len(circuit.gates):,} gates; {count:,} line sets; "
          f"{count*n:,} point/set comparisons; verified false positive on {len(bad_lines)} lines.")


if __name__ == "__main__":
    check(4, 0b111, 2, 2)
    check(8, 0b1011, 2, 3)
    check(16, 0b10011, 4, 2)
    for b, degree, t in [(512, 2, 512), (1024, 3, 1024**2//1000)]:
        q = b**degree
        n = q*q+q+1
        s = size(q, b, t)
        assert 100*s < n*q
        print(f"Symbolic only: q={q:,}, b={b:,}, cap={t:,}, {s:,} gates, "
              f"100s/(Nq)={100*s/(n*q):.6f}.")
