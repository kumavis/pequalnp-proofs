"""Build a normalized monotone circuit exact on every subset of listed line templates.

The compiler checks the finite coverage certificate for every affine point and
every template. Direct evaluations at order four additionally cover the whole
projective orbit of a punctured quadratic and every sub-selection in that orbit.
"""
from itertools import combinations
from random import Random
from math import ceil, log2
from projection_circuits import Circuit, cosets, neighbors, product


class SquareField:
    def __init__(self, b, modulus):
        self.b, self.q = b, b*b
        q = self.q
        self.mul = [[product(x,y,q,modulus) for y in range(q)] for x in range(q)]
        self.inv = [0] + [row.index(1) for row in self.mul[1:]]
        def power(x,n):
            out = 1
            while n:
                if n & 1:
                    out = self.mul[out][x]
                x = self.mul[x][x]
                n >>= 1
            return out
        self.base = tuple(x for x in range(q) if power(x,b)==x)
        assert len(self.base)==b
        self.kernels = sorted({tuple(sorted(self.mul[k][z] for z in self.base)) for k in range(1,q)})
        self.direction = {z:i for i,K in enumerate(self.kernels) for z in K if z}
        assert len(self.kernels)==b+1 and len(self.direction)==q-1

    def projection(self, line_inputs, C, direction):
        q, mul = self.q, self.mul
        K = self.kernels[direction]
        coords, rep = cosets(K,q)
        slopes, _ = cosets(self.base,q)
        # The sentinel -1 represents false. It is simplified out before a gate is emitted.
        def combine(terms):
            alive = (v for v in terms if v>=0)
            acc = next(alive,-1)
            for term in alive:
                acc = C.gate("or",acc,term)
            return acc
        packed = {(a,z):combine(line_inputs[a*q+(z^v)] for v in K) for a in range(q) for z in coords}
        pooled = {(A,X,w):combine(packed[A^u,rep[w^mul[u][X]]] for u in self.base)
                  for A in slopes for X in coords for w in coords}
        flags = {(x,z):combine(pooled[A,rep[x],rep[z^mul[A][x]]] for A in slopes)
                 for x in range(q) for z in coords}
        return [flags[x,rep[y]] for x in range(q) for y in range(q)]


def schedule(field, templates, slots, rng):
    q = field.q
    # Near-balanced coloring of the entire universe. Retry until the finite
    # certificate succeeds. The analytic existence proof uses independent colors.
    for attempt in range(1,201):
        perm = list(range(q*q))
        rng.shuffle(perm)
        color = [0]*(q*q)
        for i,ell in enumerate(perm):
            color[ell] = i % slots
        masks = set()
        for T in templates:
            bins = {}
            for ell in T:
                if ell<q*q:
                    bins.setdefault(color[ell],[]).append(divmod(ell,q))
            for x in range(q):
                for group in bins.values():
                    hits = [field.mul[a][x]^c for a,c in group]
                    for y in range(q):
                        mask = 0
                        for z in hits:
                            if y != z:
                                mask |= 1 << field.direction[y^z]
                        masks.add(mask)
            if (1<<len(field.kernels))-1 in masks:
                break
        if (1<<len(field.kernels))-1 in masks:
            continue
        uncovered, dirs = masks, []
        while uncovered:
            best = min(range(len(field.kernels)), key=lambda d:sum(bool(m & (1<<d)) for m in uncovered))
            dirs.append(best)
            uncovered = {m for m in uncovered if m & (1<<best)}
        assert dirs and all(any(not (m & (1<<d)) for d in dirs) for m in masks)
        return color, dirs, len(masks), attempt
    raise AssertionError("no schedule found in allocated retries")


def build(field, color, dirs, slots):
    q = field.q
    n = q*q+q+1
    C = Circuit(2*n)
    by_point = [[] for _ in range(q*q)]
    for b in range(slots):
        lines = [n+ell if color[ell]==b else -1 for ell in range(q*q)]
        layers = [field.projection(lines,C,d) for d in dirs]
        for p, clauses in enumerate(zip(*layers)):
            if min(clauses)>=0:
                by_point[p].append(C.fold("and",clauses))
    flags = [C.fold("or", [*terms,n+q*q+p//q]) for p,terms in enumerate(by_point)]
    for a in range(q):
        flags.append(C.fold("or",[*range(n+a*q,n+(a+1)*q),2*n-1]))
    flags.append(C.fold("or",range(n+q*q,2*n)))
    out = C.fold("or",(C.gate("and",p,flags[p]) for p in range(n)))
    assert len(C.gates) <= gate_bound(q,slots,len(dirs))
    return C,flags,out


def gate_bound(q,slots,m):
    n=q*q+q+1
    return 4*q*q*slots*m+5*n


def line_vectors(field):
    q, mul = field.q, field.mul
    all_lines = [(a,1,c) for a in range(q) for c in range(q)] + [(1,0,x) for x in range(q)] + [(0,0,1)]
    def norm(v):
        s = field.inv[next(z for z in v if z)]
        return tuple(mul[s][z] for z in v)
    return all_lines, {norm(v):i for i,v in enumerate(all_lines)}, norm


def orbit(field, seed, full, rng):
    q, mul = field.q, field.mul
    vectors, idx, norm = line_vectors(field)
    if full:
        # Transvections generate SL(3,q), and scalar multiples act trivially
        # on projective lines. At q=4 the orbit size is also checked independently.
        perms = []
        for i in range(3):
            for j in range(3):
                if i==j:
                    continue
                for s in range(1,q):
                    perm = []
                    for old in vectors:
                        v = list(old)
                        v[i] ^= mul[s][v[j]]
                        perm.append(idx[norm(v)])
                    perms.append(perm)
        frontier = [tuple(sorted(seed))]
        seen = set(frontier)
        for a in frontier:
            for perm in perms:
                transformed = tuple(sorted(perm[i] for i in a))
                if transformed not in seen:
                    seen.add(transformed)
                    frontier.append(transformed)
        return list(sorted(seen))
    seen = {tuple(sorted(seed))}
    while len(seen)<384:
        perm = list(range(len(vectors)))
        for _ in range(15):
            i,j = rng.sample(range(3),2)
            s = rng.randrange(1,q)
            nxt = []
            for ell in perm:
                v = list(vectors[ell])
                v[i] ^= mul[s][v[j]]
                nxt.append(idx[norm(v)])
            perm = nxt
        seen.add(tuple(sorted(perm[i] for i in seed)))
    return sorted(seen)


def verify(b, modulus):
    rng = Random(2008+b)
    field=SquareField(b,modulus)
    q=field.q
    n=q*q+q+1
    seed=tuple(a*q+field.mul[a][a] for a in range(1,q))
    images=orbit(field,seed,q==4,rng)
    if q==4:
        from math import comb
        assert len(images)==comb(n,3)-n*comb(q+1,3)==1120
    templates=list(images)
    templates.extend(tuple(neighbors(q,p,field.mul)) for p in range(n))
    if q>4:
        templates.extend(tuple(rng.sample(range(n),q)) for _ in range(256))
    slots=8 if q==4 else 64
    color,dirs,nm,attempts=schedule(field,templates,slots,rng)
    C,flags,_=build(field,color,dirs,slots)
    if q==4:
        selections=set()
        for T in templates:
            for j in range(len(T)+1):
                selections.update(tuple(sorted(u)) for u in combinations(T,j))
        selections=sorted(selections)
    else:
        selections=[tuple(l for l in T if rng.randrange(4)) for T in templates]
    bits=[0]*n
    for i,Y in enumerate(selections):
        for l in Y:
            bits[l] |= 1<<i
    actual=C.evaluate([0]*n+bits)
    for p,wire in enumerate(flags):
        expected=0
        for l in neighbors(q,p,field.mul):
            expected |= bits[l]
        assert actual[wire]==expected
    print(f"q={q}, {len(templates):,} templates, {len(images):,} transformed quadratics, "
          f"{slots} buckets, {len(dirs)} directions, {nm} distinct mask constraints, {attempts} coloring trial(s).")
    print(f"  {len(C.gates):,} gates; {len(selections):,} line sets evaluated at all {n} points; "
          "certificate covers every subset of every template.")


if __name__=="__main__":
    verify(2,0b111)
    verify(4,0b10011)
    b=2**30
    q=b*b
    n=q*q+q+1
    M=q**9
    B=16*b
    m=(M*n*B).bit_length()
    assert (M*B).bit_length()<3*b//8
    s=gate_bound(q,B,m)
    assert 100*s<n*q
    print(f"Symbolic orbit bound: q=2^60, at most q^9 templates, {m} directions, "
          f"100s/(Nq) <= {100*s/(n*q):.8f}.")
