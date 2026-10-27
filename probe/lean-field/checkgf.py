"""Independent reference (Python integers) for gfbench's `check` output."""
import sys
def clmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def mod(p, m):
    dm = m.bit_length() - 1
    while p.bit_length() - 1 >= dm:
        p ^= m << (p.bit_length() - 1 - dm)
    return p
P128 = (1 << 128) | 0x87
P64 = (1 << 64) | 0x1B
def ref(kind, a, b):
    if kind.startswith("c64"): return clmul(a, b)
    if kind.startswith("g128"): return mod(clmul(a, b), P128)
    if kind.startswith("g64"): return mod(clmul(a, b), P64)
    raise ValueError(kind)
ok = bad = 0; kinds = {}
for line in open(sys.argv[1]):
    if line.startswith("blake2s256 "):
        _, msg, d = line.split()
        good = d == "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"  # RFC 7693 App. B
        kinds.setdefault("blake2s256-abc", [0, 0])[0 if good else 1] += 1
        ok += good; bad += not good
        continue
    k, a, b, r = line.split()
    good = ref(k, int(a, 16), int(b, 16)) == int(r, 16)
    kinds.setdefault(k, [0, 0])[0 if good else 1] += 1
    ok += good; bad += not good
for k, (g, f) in sorted(kinds.items()): print(f"{k}: {g} ok, {f} wrong")
# structured known answers, independent of the Lean output
assert mod(clmul(1 << 127, 2), P128) == 0x87          # x^127 * x = x^7 + x^2 + x + 1
assert mod(clmul(1 << 64, 1 << 64), P128) == 0x87
assert mod(clmul(1 << 63, 2), P64) == 0x1B
print(f"total {ok} ok, {bad} wrong")
sys.exit(1 if bad else 0)
# The GCM spec's test case 2 (McGrew-Viega): X1 = C * H in GHASH's reflected bit order, which is
# this modulus with bit i of the 128-bit block (MSB first) the coefficient of x^i.
def refl(h): return int(bin(int(h, 16))[2:].zfill(128)[::-1], 2)
H, C, X1 = "66e94bd4ef8a2c3b884cfa59ca342b2e", "0388dace60b6a392f328c2b971b2fe78", "f38cbb1ad69223dcc3457ae5b6b0f885"
assert mod(clmul(refl(C), refl(H)), P128) == refl(X1)
print("GCM test case 2 (C*H = X1) agrees with the reference")
