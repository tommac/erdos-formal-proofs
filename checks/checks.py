"""Certified computations for the Erdős 23 / 1171 proofs: sanity checks, not proofs.
Run: python3 checks/checks.py (needs sympy)."""
import itertools, sympy as sp

# 1. The key identity for blowupC5_tight.
n = sp.Symbol('n'); a = sp.symbols('a0:5'); b = [n - ai for ai in a]
S = sum(a[i]*a[(i+1) % 5] + b[i]*b[(i+1) % 5] for i in range(5))
rhs = 2*(a[0]*a[1]*a[4] + a[1]*a[2]*a[3] + a[1]*b[3]*b[4] + a[3]*a[4]*b[1] + b[0]*b[1]*b[4] + b[1]*b[2]*b[3])
print("identity n(S - n^2) - RHS expands to:", sp.expand(n*(S - n**2) - rhs))

# 2. blowupC5_tight by brute force, n <= 3: over all 2-colourings of the 5n vertices, the
# number of monochromatic blow-up edges is >= n^2 (deleting exactly those edges gives the
# best bipartite subgraph for that colouring).
def blowup_edges(n):
    V = [(i, x) for i in range(5) for x in range(n)]
    return V, [((i, x), ((i+1) % 5, y)) for i in range(5) for x in range(n) for y in range(n)]
for nn in (1, 2, 3):
    V, E = blowup_edges(nn)
    best = min(sum(c[u] == c[v] for u, v in E)
               for bits in itertools.product((0, 1), repeat=len(V))
               for c in [dict(zip(V, bits))])
    print(f"blowupC5 n={nn}: {len(E)} edges, minimum deletions over all 2-colourings = {best}, n^2 = {nn*nn}, ok = {best >= nn*nn}")

# 3. n1 by brute force: all 2^10 = 1024 graphs on 5 labelled vertices.
pairs = list(itertools.combinations(range(5), 2))
tf = worst = 0
for mask in range(1 << 10):
    E = [p for k, p in enumerate(pairs) if mask >> k & 1]
    Es = set(E)
    if any({(x, y), (x, z), (y, z)} <= Es for x, y, z in itertools.combinations(range(5), 3)):
        continue
    tf += 1
    d = min(sum(c[u] == c[v] for u, v in E) for c in itertools.product((0, 1), repeat=5))
    worst = max(worst, d)
print(f"n1: 1024 graphs on 5 vertices, {tf} triangle-free, max over them of min deletions = {worst}, ok = {worst <= 1}")
