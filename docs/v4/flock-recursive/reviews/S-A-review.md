# `flock-recursive` stage S-A (field layer): adversarial review

Reviewed: `submissions/flock-recursive/lean/{FRFieldBase,FRFieldBaseCorrect,FRField128,FRField256,
FRFieldControls,FR}.lean` (uncommitted, on `v4/flock-recursive` at `f23a34e`; sha256 in
`logs/S-A-review/sources.sha256`, unchanged during the review), `probe/fr-field/`,
`docs/v4/flock-recursive/stages/S-A-{RESULT,JOURNAL}.md`, against BLUEPRINT §2.1, §5.6, §7, B-4,
`.contract` at `15dac52`, `AGENTS.md`, `CLAUDE.md`. The Rust prover's field
(`submissions/flock-recursive/prover/field.rs`, track P, in progress) was read only to check that
the constants, formulas and byte layout match.

The golf pass was running in `logs/fr-build/` at the same time. So every Lean run below was made on
a snapshot of the six files, in a private tree
(`logs/S-A-review/lakefile.toml`: the same `logs/org` at `15dac52` and `logs/pkgs`, `srcDir` = the
snapshot). Every command ran under `timeout`.

| Check | Result | Log |
|---|---|---|
| clean build `lake build FR` | green, 0 warnings; modules 1.5 / 17 / 7.2 / 6.6 / 6.2 / 3.6 s (RESULT: 1.2 / 16 / 6.8 / 6.4 / 5.7 / 3.4 s). The wall time was 74 s, against the RESULT's 42 s, because another `lake build` was running on the VM. | `logs/S-A-review/build.log` |
| source rule (`.contract/scripts/source-rule.py submissions/flock-recursive`) | 6 files, 0 findings | `source-rule.log` |
| forbidden words (`sorry`, `native_decide`, `implemented_by`, `extern`, `opaque`, `partial`, `unsafe`, `set_option`, …) | none; `noncomputable` only on the proof-side `P`, `Q`, `Φ`, `bpN` and the three `Fintype` instances | grep in this review |
| imports against `logs/org/.lake/rf/allowlist.txt` | `CompPoly.Fields.Extension`, `…BF64.Bytes`, `Mathlib.Algebra.Polynomial.SpecificDegree`, `Mathlib.FieldTheory.Finite.Basic`: all present; `CompPoly.Fields.Extension.Bytes` is absent, which confirms deviation 5 | `allowlist.log` |
| the three imported modules are in the closure of the badge's precompiled objects (`org-setup.sh` step 4: `RecursionFast` + `BF64.Ext3` + `BF64.Bytes` + `Mathlib.Tactic`) | yes, all three | `closure.log` |
| `#print axioms` on 48 declarations (every main statement, every `toExt_*` of mul/sq/inv/add/mulAlpha, `mul_c₀`/`mul_c₁`, bytes, all 15 controls) | `propext`, `Classical.choice`, `Quot.sound` at most | `probe.log`, `Probe.lean` |
| instance coherence: `a⁻¹ = F.inv a`, `a * b = F.mul a b`, the same for `K`, `Field.toCommRing = instCommRing` (all `rfl`) | hold | `probe.log` |
| `kat.py` re-run, and `gen_controls.py` on its output | byte-identical to `kat.out` and to `FRFieldControls.lean` | in this review |
| trace table over `BF64`: monomials `x^k` with trace 1 | exactly `k ∈ {61, 63}` | `check.out` |
| Lean's `F.mul` formula (lazy reduction, `r1 <<< 63`, `r1 >>> 1`) against the schoolbook product, 3,000 random pairs (Python) | 0 mismatches | `check.out` |
| the prover's `red` against true reduction modulo `x^64 + x^4 + x^3 + x + 1`, 20,000 random products | **13,859 mismatches** (Lean's `reduce`: 0) | `check.out`, `rust-red.out` |

## Verdict

**S-A's Lean is accepted.** The specification fields are the right objects. The twins are proved
equal to them with no hypotheses. Irreducibility is proved, not assumed. The controls are generated
from an independent reference, and the reviewer reproduced them byte for byte. The β/α choice is
sound and cheap. No S-A-internal finding is major.

**One major is cross-track (S-A-M1):** the Rust prover's base-field reduction is wrong, and S-A's
known answers are the tool that catches it. They are not yet machine-readable, and checking against
them is not yet an obligation. The fix pass owes the S-A side of M1 and an answer to each minor.
Track P owes the one-line Rust fix.

## Majors

### S-A-M1 (cross-track; the S-A side is the KAT hand-off). The prover's GF(2^64) reduction disagrees with `B64.reduce`; S-A's KATs would catch it but nothing makes the prover run them

`prover/field.rs` `red` (l. ≈104–111):

```rust
let ov = (hi >> 63) ^ (hi >> 61) ^ (hi >> 60);
let h = hi ^ ov ^ (ov << 1) ^ (ov << 3) ^ (ov << 4);   // folds ov by p twice
lo ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4)
```

With `p = x^4 + x^3 + x + 1` this computes `lo + (hi·p mod x^64) + ov·p²`. The correct value is
`… + ov·p`. Lean's `B64.reduce` computes the correct value: it sets `d = hi ^ ov`, then takes
`d·p mod x^64`, and that is proved (`mk_reduce`).

- **Evidence:** on S-A's first F KAT the prover gives `c₀ = 0x6BDB7CDE7A2DD122`,
  `c₁ = 0x24D581B7235CF5E0`. The kernel-checked answer is `0x6BDB7CDE7A2DD504`,
  `0x24D581B7235CF4BE` (`rust-red.out`, `rustc` on the prover's own `clmul_soft` and `red`).
- **Extent:** 69 % of random base-field products are wrong (`check.out`). Associativity fails on
  479 of 500 random triples (`assoc.out`), so the prover's own `field_laws` test would fail; it has
  not been run.
- **Effect:** every F and K product and the `aes_root` search depend on `red`. A prover built on it
  produces proofs that `V` rejects, a completeness failure of the whole entry.
- **Verified fix:** with `let h = hi ^ ov;` the same vector matches the KAT (`t2.rs`,
  `rust-red-fixed.out`).

This is in S-A's scope for two reasons. The review was asked to check "what the Rust prover will
use". And S-A's hand-off to the prover is a recommendation, not an obligation: RESULT §6 q. 4 says
the prover "should cross-check", and JOURNAL prints only 3 of the 8 pairs for each field, as
Markdown.

**Smallest fix.**

- **S-A:** have `kat.py` also write a machine-readable vector file next to `kat.out`, for example
  `probe/fr-field/kat.json` with all 8 + 8 triples, ω, and one bytes example each for F and K. In
  RESULT §6/§7, state as an obligation of P1's definition of done that the prover's `cargo test`
  reads this file and matches every triple, on both the portable and the `pclmulqdq` path.
- **Track P:** `h = hi ^ ov`.

## Minors

### S-A-m1. `BEq` on `B64`, `F` and `K` is custom and has no `LawfulBEq`

`FRFieldBase` l. 39, `FRField128` l. 185 and `FRField256` l. 133 override the `BEq` that
`deriving DecidableEq` would give. `==` resolves to the override (probe:
`(a == b) = (a.c₀.val == b.c₀.val && a.c₁.val == b.c₁.val)` by `rfl`), and `#synth LawfulBEq F`
fails (`probe.log`). spartan-srom compares with `decide`, so it never needed `LawfulBEq`. A
verifier written with `==` (natural for sumcheck checks, and for `Std.HashMap` keys with the
derived `Hashable`) leaves its proof with no bridge from `==` to `=`.

**Fix:** `instance : LawfulBEq F` (and for `B64`, `K`), a few lines each by `decide`/`simp` on
the fields. Or drop the three custom `BEq` instances and let `==` come from `DecidableEq`.

### S-A-m2. The claim "only `x^61` and `x^63` have trace 1" has no evidence in the stage record

RESULT §0 and JOURNAL say "every word below `2^61` has trace 0, so no 'smaller' sparse choice
exists". They cite `kat.py` and "the scratch check", but `kat.py` computes no trace, and no log
holds the check. CLAUDE.md: a claim is a kernel theorem or a logged measurement. The claim is true:
the reviewer recomputed the 64 traces (`check.out`). It is not load-bearing either:
`B64.frobSum_beta` and `absTrace_beta` prove what matters.

**Fix:** add the trace table to `kat.py`'s output and quote `kat.out`, or label the sentence as a
justification. The same applies to `Tr(c₀ + c₁ y) = Tr_BF64(c₁)`, which is used only to motivate
α; `F.frobSum_alpha` evaluates α's trace directly.

### S-A-m3. Two negative controls cannot fail for a reason that matters

- `inv_zero_F`'s second conjunct, `(0 : F)⁻¹ ≠ 1`, follows from the first conjunct and `0 ≠ 1`.
  It tests nothing about `F.inv`.
- `y_sq_ne` (`y·y ≠ y + 1`) only shows that the modulus is not the trace-0 `y² + y + 1`.
  `mul_kat_F_ne` already pins β, so this is weak but harmless.

Every other negative bites:

- `mul_kat_F_ne` uses `x^61`, the only other trace-1 monomial, so it is the most plausible wrong β.
  As expected, `wrongF` differs only in `c₀`, because `c₁` does not depend on β.
- `mul_kat_K_ne` (α = y, trace 0), `toBytes_F_ne` and `not_irreducible_one` (the trace hypothesis
  is needed, with an explicit root ω, recomputed) are meaningful.

**Fix:** replace the second conjunct with a negative a plausible bug would trip. For example, the
"inverse" with the wrong conjugate `⟨c₀, c₁⟩·(norm)⁻¹`, times `katF[0]!.1`, is not `1`. Or move
`inv_zero_F` to the positive column.

### S-A-m4. BP-E-M8's other field-layer constant, the GF(2^8) ⊂ F embedding, is neither fixed nor assigned

BP-E-M8 lists "the GF(2^8) embedding and the skip sets Λ, S_skip" next to β and α. In CompPoly's
polynomial basis, GF(2^8) is not the low byte, so it needs an explicit normative embedding.
BLUEPRINT §8.2's nibble-table kernels and §2.4's "F₂-subfield points" (l. 292) depend on it. The prover has
already chosen one: `field.rs` `aes_root()`, a search over `B64(2 ^ j)`, computed with the faulty
`red` of M1. There is no Lean counterpart, and the RESULT does not say which stage owns it.

**Fix:** RESULT §6 names the owner (`FRSkip`, per §7) and states that the embedding must be
published as hex words with a kernel check, before P1 relies on it. Otherwise the M1 divergence
repeats.

### S-A-m5. Hygiene and record accuracy

- RESULT §5.7 says the lines over 100 characters are spartan-srom's. Two are new:
  `FRFieldBaseCorrect` l. 808 (`have h0 … P_zero`, 101 characters) and l. 813 (the `Q_mulBeta`
  signature, 102).
- The §7 budgets are exceeded without mention: `FRFieldBase` has 106 code lines against 100, and
  `FRFieldBaseCorrect` has 829 against 820 (`loc.py`; the total, 1,815 against 2,220, is under).
- BLUEPRINT §2.1, B-4 and D-9′ still leave β and α open, and B-4 says "≈ 75 ns". The RESULT already
  asks for the β/α edit. Add the measured 81 ns to the same blueprint revision.

**Fix:** wrap the two lines, add the budget overrun to RESULT §5, and fold the B-4 number into the
blueprint revision.

## Pass A: specification (independent of the Rust and of the Lean proofs)

- **The specification objects.**
  - `BF128 := Ext f128Params` over CompPoly's `BF64`. `BF64.basePoly = X^64 + X^4 + X^3 + X + 1`
    (CompPoly `BF64/Basic.lean` l. 82).
  - `f128Params_poly : f128Params.poly = X^2 + X + C betaBF`.
  - `betaBF = toBF64 B64.beta`, with `Q_beta : Q beta.val = mk (X^63)`, so β is `x^63` at the
    specification level, not only in the twin (`beta_eq_x_pow`).
  - `BF256 := Ext f256Params` over `BF128`, with `f256Params_poly : … = X^2 + X + C alphaE` and
    `alphaE = toExt ⟨0, β⟩ = β·y`.
  - `q` is `2^64` and `2^128`, discharged by the proved `Fact`s.
  - These are the objects of B-4 and §2.1.
- **Irreducibility is proved, not assumed.**
  - `quadratic_irreducible` assumes `[Field L] [Finite L] [CharP L 2]`, `Nat.card L = 2^n` and
    `absTrace n γ ≠ 0`. It is the textbook argument: a root telescopes the trace to
    `r^(2^n) + r = 0`.
  - Its hypotheses are discharged at β (`n = 64`) and at α (`n = 128`, the absolute trace over
    GF(2), consistent with `nat_card_BF128`).
  - The traces are kernel evaluations (`frobSum_beta`, `frobSum_alpha`), read as `absTrace` through
    the proved `map_frobSum`.
  - Non-vacuity: `not_irreducible_one` shows the hypothesis cannot be dropped.
  - The `Fact (Irreducible …)` instances feed `Ext.instField`, so CompPoly's field structure rests
    on the proof.
- **Cardinality.** `nat_card_BF128 = 2^128` and `nat_card_BF256 = 2^256` (from `Ext.nat_card_ext`).
  `card_F` and `card_K` are transported by the equivalences.
- **The twins are equal to the specifications for every operation downstream needs, with no
  hypothesis.**
  - Proved: `toExt_{add,sub,neg,mul,sq,inv,div,npow,nsmul,zsmul,natCast,intCast,smulBase/smulF,
    ofB64/ofF,mulAlpha}`, `toBF64_mulBeta`, `frob_eq_pow`, `sq_eq_mul`, `mul_c₀`/`mul_c₁` (the
    lazy reduction), and `ringEquivBF128`/`ringEquivBF256`.
  - `F`/`K` are fields through these (`instField`, with `0⁻¹ = 0` proved, not assumed), and the
    probed instance projections are the compiled functions.
  - Bytes: `bytesEquiv` for F and K. Every 16- or 32-byte string decodes to exactly one element, so
    BLUEPRINT §1.2's uniform challenge reading holds. The `B64` limbs are tied to CompPoly's
    `ByteCodec BF64` (`toBytes_eq`, `ofBytes_eq`).
  - The only operation without a lawfulness bridge is `==` (m1).
- **The β/α choice and the trace criterion.**
  - Tr β = 1: kernel-checked, and recomputed in Python.
  - α = βy has trace 1: kernel-checked. And `Tr_{F/GF(2)}(c₀ + c₁y) = Tr_BF64(c₁)`, since the two
    roots of `y² + y + β` sum to 1.
  - The sparse products are what is claimed: `mulBeta r = reduce (r <<< 63) (r >>> 1)` (one shift
    pair, one reduction, proved), and `mulAlpha z = (β(βz₁), β(z₀ + z₁))` (three `mulBeta`,
    proved; the identity checked by hand from `y² = y + β`).
  - `F.mul` uses the same shift inline on the reduced `a₁b₁` (`mul_c₀`).
- **What the stage leaves to later stages (not findings).** There is no GF(2)-coordinate map
  `F ≃ (Fin 128 → ZMod 2)`, no `Algebra B64 K`/`IsScalarTower`, and no `LawfulBEq` (m1). The first
  two are what `FRRingSwitch` and `FRRS` (the D basis `x^i`, then `y·x^i`) will need. They belong
  in the field layer if more than one module uses them.

## Pass B: fidelity (the Python reference, CompPoly, the Rust prover)

- **The KATs are independent and non-vacuous.**
  - `kat.py` multiplies in GF(2^64) by shift-and-add with `M = x^64 + 0x1B`, in F by the schoolbook
    product (4 base products, `y² = y + β`, no Karatsuba, no lazy reduction), and in K by the
    schoolbook product with the full F product by α (not `mulAlpha`).
  - Random 64-bit limbs exercise the reduction's overflow path (`hi` bits 60–63), which is exactly
    the path M1 gets wrong.
  - The reviewer re-ran `kat.py` and `gen_controls.py`, and both reproduce byte for byte.
  - The KATs are not implied by the symbolic theorems. They anchor the specification's conventions
    (bit order, limb order, β, α) to an implementation outside Lean, and that is their use for the
    prover.
  - `sq_kat_K`, `mul_inv_F` and `mul_inv_K` are Lean-against-Lean. They are redundant with
    `sq_eq_mul` and `instField`, but harmless (evaluation sanity of the compiled path).
- **The byte layout matches the prover.**
  - F: `to_bytes` = `c₀` little-endian ‖ `c₁` little-endian (`lo` = `c₀`, from
    `alpha() = F { lo: ALPHA.0, hi: ALPHA.1 }` with `ALPHA = (c₀, c₁)`).
  - K: `f₀` ‖ `f₁`. Both are as in Lean and BLUEPRINT §1 l. 74–76.
  - The constants: `params::BETA = 1 << 63`, `ALPHA = (0, 1 << 63)`.
  - The F and K product formulas, and both norms, are the same as in Lean.
  - The base-field reduction is not the same (M1).
- **The copied code.** `FRFieldBase` and `FRFieldBaseCorrect` against spartan-srom, after the
  renaming: the only differences are
  - `clmul64` factored out of `mul`;
  - `beta`, `mulBeta`, `Q_beta`, `Q_mulBeta`, `toBF64_mulBeta` added;
  - `P_xor`, `P_shiftLeft` made public;
  - the `BF64.Bytes` import moved to the `Correct` file.

  The diff matches deviation 4 and the provenance comments. Every file carries a provenance or
  "New for" line.

## Pass C: hygiene, cost

- **Kernel cost.**
  - Kernel time is 25.5 s for `FRFieldBaseCorrect` (copied, class R; the `clmul32`/`spread` bit
    lemmas), 3.0 s for `FRField128`, 2.0 s for `FRField256` and 2.6 s for `FRFieldControls`
    (`logs/S-A/profile-*.log`).
  - The `decide +kernel` evaluations are small: 64 `B64` and 128 `F` squarings, 8 + 8 products, one
    `K` inverse. They are in line with M §7.1.
  - No new hot spot.
- **Docstrings** are present on every public definition and main theorem, and the module headers
  state the construction. Lines over 100 characters and the budgets: see m5.
- **The harness has not run.** There is no `Solution.lean` yet, by design (S-I). The checks the
  gate would make here (source rule, allowlist, badge-object closure, axioms, forbidden attributes)
  were repeated by hand above. S-I owes `HARNESS: ACCEPT` with `Solution` importing `FR` (RESULT
  §6 q. 2).
