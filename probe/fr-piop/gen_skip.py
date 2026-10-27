#!/usr/bin/env python3
"""Constants for FRSkip (BLUEPRINT rev. 3 A.1), from an independent shift-and-add reference:
zeta = x^((2^64-1)/255) in BF64, g_i = zeta^i (i < 8), the pinned coordinates rho_j = y^(2^j)
(j = 1..7), the 128 products w_u = prod_j (bit j of u ? rho_j : 1 + rho_j), and the inverse N of
their 128x128 GF(2) bit matrix (row u = the 128 bits of w_u, c0 low): rows n_j with
sum_{j : bit j of w_u} n_j = e_u. Prints Lean literals."""
M = (1 << 64) | 0x1B
def m64(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> 64: a ^= M
    return r
def p64(a, e):
    r = 1
    while e:
        if e & 1: r = m64(r, a)
        a = m64(a, a); e >>= 1
    return r
BETA = 1 << 63
def fmul(a, b):
    (a0, a1), (b0, b1) = a, b
    t = m64(a1, b1)
    return (m64(a0, b0) ^ m64(t, BETA), m64(a0, b1) ^ m64(a1, b0) ^ t)
z = p64(2, ((1 << 64) - 1) // 255)
assert p64(z, 255) == 1 and all(p64(z, 255 // p) != 1 for p in (3, 5, 17))
g = [p64(z, i) for i in range(8)]
def fpow(a, e):
    r = (1, 0)
    while e:
        if e & 1: r = fmul(r, a)
        a = fmul(a, a); e >>= 1
    return r
finv = lambda a: fpow(a, (1 << 128) - 2)
import sys
LEVEL = sys.argv[1] if len(sys.argv) > 1 else "two"
if LEVEL == "one":   # rev. 3: rho_j = y^(2^j), j = 1..7
    y = (0, 1); rho = []; cur = y
    for j in range(1, 8):
        cur = fmul(cur, cur); rho.append(cur)
    gl = None
else:                # rev. 3.1 A.1: g_i = zeta^(2^(i-1)) (i <= 3), y^(2^(i-4)) (i >= 4); rho = g/(1+g)
    gl = [(p64(z, 1 << (i - 1)), 0) for i in (1, 2, 3)] + [fpow((0, 1), 1 << (i - 4)) for i in (4, 5, 6, 7)]
    rho = [fmul(gi, finv((gi[0] ^ 1, gi[1]))) for gi in gl]
    for gi, r in zip(gl, rho):
        assert fmul(r, (gi[0] ^ 1, gi[1])) == gi
w = []
for u in range(128):
    f = (1, 0)
    for j in range(7):
        f = fmul(f, rho[j] if (u >> j) & 1 else (rho[j][0] ^ 1, rho[j][1]))
    w.append(f)
bits = lambda f: f[0] | (f[1] << 64)
rows = [bits(f) for f in w]
# invert over GF(2): find N with M N = I, i.e. row_u(M) . N = e_u
A = [(rows[u], 1 << u) for u in range(128)]   # augmented [M | I]
piv = []
r = 0
A = [list(x) for x in A]
for col in range(128):
    k = next(i for i in range(r, 128) if (A[i][0] >> col) & 1)
    A[r], A[k] = A[k], A[r]
    for i in range(128):
        if i != r and (A[i][0] >> col) & 1:
            A[i][0] ^= A[r][0]; A[i][1] ^= A[r][1]
    r += 1
# now A[col] = (e_col, (M^-1) row col as combination of original rows) : e_col = sum_u c_u row_u
# We need N with M N = I. Row-reduction gives P with P M = I, P[col] = A[col][1]; then N = P.
P = [A[c][1] for c in range(128)]
assert all(A[c][0] == 1 << c for c in range(128))
# check M P = I : row_u(M) . P = sum_{j : bit j of row_u} P[j] = e_u
for u in range(128):
    acc = 0
    for j in range(128):
        if (rows[u] >> j) & 1: acc ^= P[j]
    assert acc == 1 << u, u
f = lambda v: f"⟨⟨0x{v & ((1<<64)-1):016X}⟩, ⟨0x{v >> 64:016X}⟩⟩"
print(f"-- zeta 0x{z:016X}")
print("-- g " + ", ".join(f"0x{x:016X}" for x in g))
if gl: print("-- gl " + ", ".join(f(bits(x)) for x in gl))
print("-- rho " + ", ".join(f(bits(x)) for x in rho))
print("-- w")
for u in range(128):
    print(f"  {f(bits(w[u]))}" + ("," if u < 127 else ""))
print("-- Ninv")
for j in range(128):
    print(f"  {f(P[j])}" + ("," if j < 127 else ""))
