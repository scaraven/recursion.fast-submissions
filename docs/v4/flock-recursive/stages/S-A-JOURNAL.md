# S-A (track L-field): journal

Running notes for a successor. Read "Normative constants" first: the prover (P1) copies them.

## Normative constants

Fixed by S-A on 2026-10-27 (BP-E-M8 of the engineering review asked S-A to choose them). They are
kernel-checked in `submissions/flock-recursive/lean/` and must not change without a new stage.

**Bit and byte conventions.** A GF(2^64) element is a 64-bit word `w`, bit `i` of `w` the
coefficient of `x^i`. Its bytes are the 8 bytes of `w` little-endian (CompPoly's `BF64` layout).

| Object | Value | Lean |
|---|---|---|
| base modulus | `x^64 + x^4 + x^3 + x + 1` (CompPoly `BF64`; reduction constant `0x1B`) | `B64.reduce` |
| **β** | **`x^63`**, the word `0x8000000000000000`; bytes `00 00 00 00 00 00 00 80` | `B64.beta`, `FR.betaBF`, `FR.beta_eq_x_pow` |
| F | `GF(2^64)[y] / (y^2 + y + β)`; element `c₀ + c₁ y`; 16 bytes = `c₀` LE ‖ `c₁` LE | `FR.F`, `FR.BF128`, `FR.f128Params` |
| **α** | **`β y = x^63 · y`**: `c₀ = 0`, `c₁ = 0x8000000000000000`; bytes `00 ×8, 00 00 00 00 00 00 00 80` | `FR.F.alpha`, `FR.alphaE` |
| K | `F[u] / (u^2 + u + α)`; element `f₀ + f₁ u`; 32 bytes = `f₀` (16) ‖ `f₁` (16) | `FR.K`, `FR.BF256`, `FR.f256Params` |

**Why these.** A quadratic `y^2 + y + γ` over a field of `2^n` elements is irreducible iff the
absolute trace `Tr(γ) = Σ_{i<n} γ^(2^i)` is 1. Over this BF64 the trace is linear and the only
monomials `x^k`, `k < 64`, of trace 1 are `x^61` and `x^63` (every word below `2^61` has trace 0;
`probe/fr-field/kat.out` l. 24, printed by `kat.py`). Both are one-bit constants: the product by `x^63`
is `reduce(r << 63, r >> 1)`, one shift pair and one reduction (`B64.mulBeta`); `x^61` would be
`reduce(r << 61, r >> 3)`, equally cheap. `x^63` was taken. Over F, `Tr_{F/GF(2)}(c₀ + c₁ y) =
Tr_{BF64}(c₁)`, so `α = β y` has trace 1 and its product is three `mulBeta`:
`α (z₀ + z₁ y) = β(β z₁) + β(z₀ + z₁) y` (`F.mulAlpha`).

Kernel checks: `FR.B64.frobSum_beta` (Tr β = 1, 64 squarings), `FR.F.frobSum_alpha` (Tr α = 1,
128 squarings in F); irreducibility `FR.f128_irreducible`, `FR.f256_irreducible`.

**Product formulas** (what the Rust prover implements):

- F: `(a₀ + a₁ y)(b₀ + b₁ y) = (a₀b₀ + β a₁b₁) + ((a₀ + a₁)(b₀ + b₁) + a₀b₀) y` (Karatsuba).
- K: `(a₀ + a₁ u)(b₀ + b₁ u) = (a₀b₀ + α a₁b₁) + ((a₀ + a₁)(b₀ + b₁) + a₀b₀) u`.

**KATs** (from `probe/fr-field/kat.py`, an independent schoolbook reference; the same values are
kernel-checked in `FRFieldControls.mul_kat_F`/`mul_kat_K`). An F element is written `(c₀, c₁)`, a
K element `((f₀.c₀, f₀.c₁), (f₁.c₀, f₁.c₁))`; every limb is a 64-bit word in hex, its bytes
little-endian in the encoding.

F:

| a | b | a·b |
|---|---|---|
| `(0x0CC65817272B53A4, 0x2120FC8CCEE55FE9)` | `(0x99363C9930CF43AC, 0x6889C91E3005A706)` | `(0x6BDB7CDE7A2DD504, 0x24D581B7235CF4BE)` |
| `(0x3A31AADC19E3ECBF, 0x071674EE0693E0D9)` | `(0x6BE1E08A7E114E68, 0x8DE424016B820FE4)` | `(0x244BC9B01462D3E5, 0xF3026AA4979DAC65)` |
| `(0x0A727244D2A65227, 0x141337ACF1E2B441)` | `(0x6EDE80A3BA89E31D, 0xC6C4EE2E3B9EFAD5)` | `(0x43BFB2E669825116, 0x8467CA181C3F98D6)` |

K:

| a | b | a·b |
|---|---|---|
| `((0x2641940B4DF62868, 0xC0450C5C86166DEC), (0x5298E4BB63FE5590, 0x5DB1608995CCB6A0))` | `((0x95E30255B5D45D27, 0x18B2BF46EE11E992), (0x91782A4F625E5555, 0xB49F8D70989DA94A))` | `((0xA7076D7E76A71A45, 0xB6C9CAE676ACD4CA), (0x423E1CBA3D46D2A5, 0xFBB4F8964518C30E))` |
| `((0xA52DD713B80A40B6, 0xFD252688627FD848), (0xC02AEDEBA2F6AA9E, 0xC83E8BAF538499D9))` | `((0x5A875486E99ED6AE, 0xA087CC556F4BE6E8), (0x9AA80F8A49B4FA90, 0x24ADBA25E931A56F))` | `((0x0D4F356658BF4069, 0xEBE1DC9188041AEF), (0xD462760B899E75C3, 0x3782A5182D0B1F9E))` |
| `((0x3E60CA3809906D54, 0xE02071366047B633), (0x83FF7FE3E1F0859D, 0x564B1DD7CDEE32A2))` | `((0xCBD2D4944CA05421, 0x9CB9557B327BD25B), (0x0F276F7FD5562BFA, 0xA24590AB86A403FD))` | `((0xD6584FDCF9CF8D2B, 0xC5CDAAD8E827E37C), (0x5A5FCDDDE69A286E, 0x7BB481D0F11023C3))` |

Example encoding: the F element `(0x0807060504030201, 0x100F0E0D0C0B0A09)` is the bytes
`01 02 … 10` (kernel: `FRFieldControls.toBytes_F`).

## Log

- Build tree: `logs/fr-build/` (`gen.sh` writes `lakefile.toml` as `evaluate.py`'s `mkfresh`
  does: requires `logs/org` by path, `packagesDir = logs/pkgs`, one `[[lean_lib]]` whose roots are
  every module of `lean/`, `srcDir` pointing at the entry's `lean/`). Run `./gen.sh` after adding a
  module, then `timeout … lake build FR`.
- `FRFieldBase`/`FRFieldBaseCorrect`: copied from spartan-srom, `SpartanSrom.F` → `FR.B64`.
  `FRFieldBase` imports nothing beyond core (so `ℕ` became `Nat`). The 64×64 product is factored
  as `B64.clmul64` (returns `U128`, unreduced) with `P_clmul64`, so F's product can reduce lazily;
  `P_xor` and `P_shiftLeft` made public for `FRField128`.
- Traps met: `congr 1` on `AdjoinRoot.mk` goals hits max recursion (use `refine congrArg _ ?_`);
  a generic `[Add α]` in `frobSum` made instance unification blow up (pass `add` explicitly);
  `mul_inv_cancel₀` on `BF128` hit max recursion (use `Ext.mul_inv_cancel'`); `ext` on `BF256`
  recurses into the coefficients (use `Ext.ext` once); define `inv` literally as
  `smulBase (norm a)⁻¹ conj`, else the `change` in `toExt_inv` times out on a non-defeq order.
- Multiplication variant: h32 (`clmul32` Karatsuba, spartan-srom's, already proved). h64 (BearSSL
  `bmul64` with bit reversal) was 2–5 % faster in phase 0 (M §3) but needs a new proof of
  the reversal identity; not done in S-A (see RESULT).
- Measurements (VM, one core each, `logs/S-A/bench.txt`): `F.mul` ≈ 81 ns, `K.mul` ≈ 268 ns,
  `B64.mul` ≈ 25 ns, `F.sq` ≈ 15 ns, `F.inv` ≈ 940 ns. The bench tree `logs/fr-bench/` links the
  entry's modules against the organiser's precompiled Mathlib objects (no Mathlib rebuild:
  11.7 s link build).
- Axioms: `logs/S-A/Axioms.lean` (outside the entry; `#print axioms` on 27 declarations), run
  with `lake env lean` in `logs/fr-build/`.
- State at hand-off: S-A done (RESULT written); next stages import `FRField128`/`FRField256`.
- Fix pass (review m1–m5): `LawfulBEq` for `B64`, `F`, `K`; the trace table is now logged in
  `kat.out`, because a kernel theorem for it cost about 15 s of kernel time; `inv_no_conj_ne` and
  `y_sq_ne_x61` replace the toothless negatives; ζ (GF(2^8)) belongs to `FRSkip` (S-C). Private
  build tree `logs/S-A-fix/`. Sequential-elaboration kernel total: 15.1 s (RESULT, Fix pass).
