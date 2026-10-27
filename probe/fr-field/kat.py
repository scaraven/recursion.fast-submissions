#!/usr/bin/env python3
"""Known answers for FRFieldControls, from an independent schoolbook reference (no Karatsuba, no
lazy reduction): GF(2^64) = GF(2)[x]/(x^64+x^4+x^3+x+1) by shift-and-add, F = GF(2^64)[y]/(y^2+y+b),
K = F[u]/(u^2+u+a). Prints Lean literals. Usage: kat.py [SEED]."""
import random, sys
M = (1 << 64) | 0x1B
def m64(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> 64: a ^= M
    return r
def fmul(a, b, beta):
    (a0, a1), (b0, b1) = a, b
    # (a0 + a1 y)(b0 + b1 y) = a0 b0 + (a0 b1 + a1 b0) y + a1 b1 y^2, y^2 = y + beta
    t = m64(a1, b1)
    return (m64(a0, b0) ^ m64(t, beta), m64(a0, b1) ^ m64(a1, b0) ^ t)
def fadd(a, b): return (a[0] ^ b[0], a[1] ^ b[1])
def kmul(a, b, beta, alpha):
    (a0, a1), (b0, b1) = a, b
    t = fmul(a1, b1, beta)
    return (fadd(fmul(a0, b0, beta), fmul(t, alpha, beta)),
            fadd(fadd(fmul(a0, b1, beta), fmul(a1, b0, beta)), t))
BETA = 1 << 63
ALPHA = (0, BETA)
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 20261027)
w = lambda: rng.getrandbits(64)
fe = lambda f: f"⟨⟨0x{f[0]:016X}⟩, ⟨0x{f[1]:016X}⟩⟩"
ke = lambda k: f"⟨{fe(k[0])}, {fe(k[1])}⟩"
print("-- F pairs (a, b, a*b)")
FP = [((w(), w()), (w(), w())) for _ in range(8)]
for a, b in FP:
    print(fe(a), fe(b), fe(fmul(a, b, BETA)))
print("-- F: the first product with beta = x^61 (wrong constant)")
print(fe(fmul(FP[0][0], FP[0][1], 1 << 61)))
print("-- K pairs (a, b, a*b)")
KP = [(((w(), w()), (w(), w())), ((w(), w()), (w(), w()))) for _ in range(8)]
for a, b in KP:
    print(ke(a), ke(b), ke(kmul(a, b, BETA, ALPHA)))
print("-- K: the first product with alpha = y (wrong constant, trace 0)")
print(ke(kmul(KP[0][0], KP[0][1], BETA, (0, 1))))
# the cube root of unity in GF(2^64): w = x^((2^64-1)/3), a root of y^2 + y + 1
def p64(a, e):
    r = 1
    while e:
        if e & 1: r = m64(r, a)
        a = m64(a, a); e >>= 1
    return r
om = p64(2, ((1 << 64) - 1) // 3)
assert m64(om, om) ^ om ^ 1 == 0
print(f"-- omega 0x{om:016X}")
# the absolute trace of the monomials x^k, k < 64 (review S-A-m2; kernel: FRFieldControls.trace_one_monomials)
def tr(a):
    s, t = 0, a
    for _ in range(64):
        s ^= t; t = m64(t, t)
    return s
print("-- monomials x^k (k < 64) of trace 1:", [k for k in range(64) if tr(1 << k) == 1],
      "; traces other than 0/1:", [k for k in range(64) if tr(1 << k) not in (0, 1)])
