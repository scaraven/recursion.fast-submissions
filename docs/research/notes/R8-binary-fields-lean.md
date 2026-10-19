<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `notes/R8-binary-fields-lean.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# R8: binary fields in the trusted contract: K = GF(2^64), E = GF(2^192)

Date 2026-10-10. Probe: `probes/r8-binary/` (see its `RESULT.md`).

Tags: [V] means read or run by me. [I] means inference. [S] means from a subagent's code census,
which read the code; I spot-checked it for ArkLib RS, Binius and FRI.

## Revisions

| Repository | Revision |
|---|---|
| ArkLib | `db7005f84a9dbad7ff2abbbb4e8feeeac6f4dfd8` (Lean v4.34.0) |
| CompPoly at ArkLib's pin | `df591bb8c6745126d1d72f5243faae3022b0432a` (tag `v4.34.0-patch2`) |
| CompPoly at leanerVM's pin | `572f997390aa4fc131ef30b1186fa1dcf292ca10` |
| leanerVM | `c6f627082e954a8dfd73a67e113d607d0908e321` (v4.34.1) |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| comparator | `d03acab` |

The two CompPoly pins have **byte-identical `CompPoly/Fields/Binary/**`** (`diff -r`) [V], and
`df591bb` is an ancestor of `572f997`.

The field choice matches leanVM. `README.md:126` says "Binary field of 192 bits (tower of degree 3
over the 64 bit field)". `crates/lean_compiler/zkDSL.md:17` defines
`K = GF(2)[x]/(x^64+x^4+x^3+x+1)` and `E = K[y]/(y^3+y+1)` [V].

## 0. Recommendation (short)

**Option (b').** The contract restates K locally as `structure K where bits : BitVec 64`. It gives
CompPoly's carry-less multiply-and-fold, about 25 code lines, **importing only Lean core**. The
operations are written so that they are **definitionally equal** to CompPoly's `BF64` operations.

The organiser library (untrusted, kernel-checked) then gets everything else from CompPoly in a few
`rfl`s:
- `Field K`, whose data is the contract's own `0, 1, +, *`;
- `card K = 2^64`;
- `K_spec`: irreducibility, plus a `0,1,+,*`-preserving bijection to Mathlib's
  `AdjoinRoot (X^64+X^4+X^3+X+1 : (ZMod 2)[X])`;
- E.

**E is not part of the trusted relation.** Following D1 §2.1, challenge types are submitter-chosen.
The library offers a 3-limb `E` with `Field E`, `card = 2^192` and a 24-byte encoding as the
blessed default. It enters the contract only if a season fixes the challenge space.

What the probe established [V]:
- The design compiles.
- All axioms are standard.
- The kernel evaluates K arithmetic (≈ 39 ms per mul).
- Unpatched comparator replays the whole thing, including CompPoly's Rabin certificate: 101 s.

## 1. Inventory

### 1.1 CompPoly `BF64` / `BF64.Ext3` [V]

Paths are under `CompPoly/Fields/Binary/BF64/`. Author: Nicolas Schleicher. There are 0 `sorry`,
0 `native_decide` and 0 `implemented_by` in `Fields/Binary/**`.

| Item | Location | Notes |
|---|---|---|
| Modulus `basePoly = X^64+X^4+X^3+X+1` over `ZMod 2` | `Basic.lean:82` | `noncomputable`, specification only |
| **`basePoly_irreducible`** | `Basic.lean:130` | Rabin's test via `irreducible_of_rabin_prime_power` (`Data/Polynomial/RabinCertificate.lean:378`). The trace condition is `X^(2^64) ≡ X` (`dvd_X_pow_sub_X_of_runChain` :290), plus one coprimality check at `2^32` (`isCoprime_X_pow_sub_X_of_runChain` :306). The certificate is generated data (`BaseCertificate.lean`, 552 lines), re-checked by `runChain` (:195) with `by rfl`. The section sets `maxHeartbeats 400000` and `maxRecDepth 4000` (`Basic.lean:73-74`). Compiling `Basic.lean` takes 88 s and 4.7 GB (47 s elaborating `rfl`, 34 s kernel). |
| `BF64Quot := AdjoinRoot basePoly` | `Basic.lean:172` | Field and Fintype (noncomputable); `card_bf64Quot` at :185 |
| Carrier `structure BF64 where toBitVec : BitVec 64` | `Impl.lean:58` | Derives `DecidableEq` and `BEq` |
| `mul = reduce ∘ carryLessMul` | `Reduce.lean:137` (`foldStep`), :167 (`reduce`); `Common/Arithmetic.lean:78` (`carryLessMul`, a `Fin.foldl` shift-xor) | Two folds by `0x1B`. `toPoly_reduce` proves it computes `% basePoly`. |
| Bridge to Mathlib | `Impl.lean:130` (`toQuot`), :174 (`toQuot_injective`), :470 (`toQuot_surjective`) | `toQuot_add`, `toQuot_mul`, etc. **The computable operations agree with Mathlib's `AdjoinRoot` model.** |
| `CommRing BF64` | `Impl.lean:305` | Written out field by field, so it stays computable |
| `Field BF64` | `Impl.lean:513` | Inverse is Itoh–Tsujii (`invItohTsujii` :348), proved by `mul_invItohTsujii` |
| Finiteness | `Impl.lean:459` (`Finite`), :462 (`nat_card_bf64`) | **No `Fintype` instance** (deliberate). Consumers must supply one. |
| Bytes | `Bytes.lean` | 8 bytes little-endian (`ByteCodec`, `UInt8`) |
| `ext3Poly = X^3+X+1` over BF64 | `Ext3.lean:127` (`ext3Poly_irreducible`) | No root: a root would have order 7, but `gcd(7, 2^64−1) = 1`. Cheap. |
| `Ext3 := Ext ext3Params` | `Ext3.lean:172` | Generic framework `CompPoly/Fields/Extension/*`. Carrier `Vector BF64 3`; `mul` is a d³ sum (`Extension/Arithmetic.lean:201`, compiled via proved `@[csimp] mul_eq_mulTbl` :355); `inv = x^(q^d−2)` (:445). `Field` at `Extension/Field.lean:137`, `ringEquivQuot` at :93; `nat_card_ext3` |

**Binary towers.** Also in CompPoly (`Tower/Abstract`, `Tower/Concrete`, `Tower/Equiv.lean`), with
`Field (ConcreteBTField k)` at `Tower/Concrete/Field.lean:826`.
- The tower uses a *different bit encoding* from BF64. No isomorphism to BF64 exists in either
  library [S].
- There is also a separate `BF128Ghash`.

**leanerVM** (`LeanerVM/Parameters/Field.lean:71,87`) uses `abbrev K := BF64` and
`abbrev E := BF64.Ext3`. It also adds a proof-only `Fintype K` via `Fintype.ofFinite`, `K.ofBits`,
and `mul_limbs`, the explicit 3-limb product. It flags two things:
- natural-number casts follow characteristic two (`2 : K = 0`);
- from a `module` file the kernel cannot reduce `Ext.ofFn`, because `Array.ofFn` is not exposed
  (:43-51) [V].

leanerVM's protocol is binary-field but uses an **idealized inner-product oracle** (a PCS
abstraction, `Protocol/Field.lean`). It has **no** Reed–Solomon or proximity content
(R5 §3) [V].

### 1.2 Mathlib [V]

- `GaloisField p n := SplittingField (X^(p^n) − X)` (`FieldTheory/Finite/GaloisField.lean:69`) is
  noncomputable. `GaloisField.card` (:130) gives `Nat.card = p^n` only: no `Fintype` instance and
  no decidable equality.
- `AdjoinRoot` over `ZMod 2` is noncomputable because `Polynomial` is `Finsupp`.
- Irreducibility tools: `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` (used for Ext3).
  Mathlib has **no** Rabin or Ben-Or test. CompPoly supplies that
  (`Data/Polynomial/Rabin.lean:113`, `RabinCertificate.lean`).

### 1.3 ArkLib binary-field support

Source: the [S] census, spot-checked [V]. Real `sorry` counts; "clean" means absent from
`scripts/axiom_baseline.json`.

**RS definitions**
- `ReedSolomon.code` (`Data/CodingTheory/ReedSolomon.lean:38,65`): `domain : ι ↪ F` arbitrary,
  `[Semiring F]` only.
- Interleaved RS (`Interleaved.lean:58`) and folded RS (`Folded.lean:127`) are equally generic.
- So RS **over char 2 with an additive (F2-affine) domain is expressible** [V for `code`].
- Constrained RS (WHIR) needs `SmoothCosetFftDomain`, a multiplicative 2-power subgroup. This is
  impossible in char 2, because `|Fˣ|` is odd.

**Proximity gaps usable in char 2.** All clean, with any `domain : ι ↪ F`:
- BCIKS20 unique-decoding correlated agreement for lines,
  `RS_correlatedAgreement_affineLines_uniqueDecodingRegime`
  (`ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean:33`, error `n/|F|`);
- `rs_mcaError_le_of_le_relUDR` (`BCIKS20/EpsCa.lean:160`);
- DKT26 Johnson-range MCA for lines, `mcaError_affineLine_johnson_le`
  (`ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean:41`). It has no
  characteristic hypothesis;
- BCGM25 `isMCAGenerator_of_isMDSGenerator` (`ProximityGenerator/MDSGenerator.lean:837`);
- DG25 unique-decoding, interleaved and tensor gaps (`DG25/*`);
- AHIV22 Lemma 4.5 (`ProximityGap/AHIV22.lean:343`);
- the Johnson bound;
- 2-ary tensor-fold MCA (`ProximityGenerator/BinaryTensorFold*`). "Binary" there means 2-ary
  folds, not characteristic 2.

**Proximity gaps not usable**
- `exists_capacity_mcaError` (DKTZ26, `Capacity.lean:254`) needs `ringChar F = 0 ∨ k−1 < ringChar F`.
  It **fails in char 2 for k > 2**.
- BCIKS20 list-decoding and curve results are sorried or tainted.

**Negative results specific to char 2** (clean): BCHKS25 `exists_rs_epsCa_large_at_johnson_radius`
(`CapacityBounds/JohnsonLower.lean:1423`); CS25 subfield lower bound `subfield_epsCa_lower_bound`
(`CapacityBounds/Subfield.lean:648`); the trace-line constructions (`ReedSolomon/Binary/*`).

**Subfield code, extension challenges.** There is no positive "code over K, challenges from E"
correlated-agreement theorem. [I] A submitter can use the generic results with `F := E` and a
domain inside K, since a K-valued word lies in RS over E with error `n/|E|`. That is enough for
unique-decoding-regime designs.

**Binius**
- `ProofSystem/Binius/BinaryBasefold/*` and `FRIBinius/*` are over an abstract
  `[Field L] [CharP L 2]` with `𝔽q = GF(2)` and an F2-basis `β`. They do not use CompPoly types.
- Sorry counts: BinaryBasefold 23, FRIBinius 9, RingSwitching/Packing 14.
- **Every completeness and RBR-KS theorem is tainted.** A few fold and distance lemmas are clean,
  and RingSwitching `Lift` is proved.

**FRI, STIR, folding**
- FRI and BatchedFRI require `[NonBinaryField F]` (`Fri/Spec/General.lean:37`) [V].
- `ProximityGap/Folding*` uses multiplicative domains.
- So there is **no formal FRI or WHIR for binary fields**.

**Additive NTT** (CompPoly `Fields/Binary/AdditiveNTT/*`, LCH14)
- Sorry-free. `additiveNTT_correctness` (`Correctness.lean:1119`); the executable versions are
  proved equal (`computableAdditiveNTT_eq_additiveNTT` :495, `…Fast…` :597).
- Generic over `[Field L]` with an `𝔽q = GF(2)` algebra and a basis `β`, so not tower-only.
- Concrete instances exist only for towers. [I] BF64 or E needs `Algebra (ZMod 2) _`, `Fintype`
  and a basis with `β 0 = 1`.

**Sumcheck**
- Native `Sumcheck/Interaction/**` has 0 sorry. `execute_soundness` (`ProtocolSoundness.lean:201`)
  is over any `[Field F][Fintype F][DecidableEq F]`, with no characteristic hypothesis.
- The legacy sumcheck is tainted (R4).
- Schwartz–Zippel (`ToMathlib/MvPolynomial/SchwartzZippel.lean:33`) is generic.

## 2. Options for the contract

| Criterion | (a) import CompPoly, `abbrev K := BF64`, `E := BF64.Ext3` | **(b') restate K locally, defeq to BF64; Field via library** | (b) local K with own clmul *and* own Field/irreducibility proofs | (c) Mathlib `GaloisField 2 64` |
|---|---|---|---|---|
| Trusted definitions to read | 49 CompPoly data declarations / 147 lines, plus 15 Mathlib / 31 lines (BFS, `R8Probes/TrustedClosure.lean`), spread over 6+ files, and the instance structure (`npowBinRec`, casts, …) | **~25 lines in one file, core only** (0 CompPoly/Mathlib reached) | as (b'), plus the proofs (not read) | small, but meaningless computationally |
| Pinned-dependency risk | CompPoly is in the trusted cone; an upstream change to a definition changes the relation | CompPoly only in proofs; a change breaks a `rfl`, never the meaning | none | none |
| Readability for cryptographers | `Ext` framework, generic `ExtensionParams`, d³ sums | shift-xor loop, `0x1B` folds, xor, 8-byte LE | same as (b') | `SplittingField (X^(2^64)−X)`: abstract, no encoding |
| Field axioms / card | from CompPoly | from CompPoly via `rfl` bridge (library, 176 code lines) | redo Rabin certificate, toPoly bridge, Itoh–Tsujii (~2–3k lines [I]) | Mathlib |
| Kernel cost / replay | Rabin certificate in every contract replay (~34 s kernel) | contract alone replays in under a second; submissions using `Field K` replay the certificate (comparator 101 s total, **passes unpatched**) | same as (b') | n/a |
| Computability | yes (K fast in kernel; Ext3 2.2 s/mul in kernel; Ext needs classic files) | yes; 3-limb E 0.3 s/mul in kernel | yes | **no** (no decidable equality, no `#eval`, no `Fintype`) |
| Byte encoding | `ByteCodec` (`UInt8` vectors) | explicit 8 LE bytes `BitVec 8`, total decoder (every string canonical) | same | impossible without choosing a basis, i.e. (b) |

**(c) is out.**
- The relation's matrices are literals and must be decidable for the spec and honest-prover
  pipeline.
- The machine's bytes must map to field elements through a fixed basis.
- `GaloisField` has neither a basis nor decidable equality, and its isomorphism to the
  polynomial-basis field is non-canonical. `R8Probes/OptionC.lean`: no `Fintype`, no
  `Decidable (1*1 = 1)`.

**(b) is pointless.** CompPoly's proofs are sorry-free and replay under comparator.

**(b') beats (a)** on trusted surface (25 vs ~180 lines across two libraries) and on decoupling the
meaning from a mutable dependency. It keeps all of CompPoly's proofs.

## 3. Comparator replay

The Proximity Prize had to patch comparator because KoalaBear Ext6's certificate failed
fresh-environment replay (R3 §5).

I ran **unpatched** comparator `d03acab`, as built by P1, on a challenge whose claim depends on:
- `BF64.basePoly_irreducible` (via `K_spec`);
- `ext3Poly_irreducible` (via `Field E`);
- a `decide +kernel` R1CS check.

Result: **accepted**, 101.5 s wall, 3.54 GB (`probes/r8-binary/logs/comparator.log`) [V].

[I] Why BF64 succeeds where Ext6 failed:
- BF64's certificate is a list-based `runChain` over `ZMod 2` coefficient lists. It is checked by
  `rfl` against the kernel's GMP-accelerated `Nat`, and needs `maxRecDepth 4000` only at
  elaboration time.
- Ext6's sextic certificate over a 31-bit prime was evidently deeper.

The organisers should still keep this test in CI, since certificates are regenerated upstream.

## 4. The contract's `Field.lean` (as probed; 93 lines total, 46 code incl. R1CS)

```lean
/-  RecursionFast.Field  (contract draft, TRUSTED). Imports only Lean core. -/
namespace RecursionFast

/-- bit `i` of `bits` is the coefficient of `x^i` in GF(2)[x]/(x^64 + x^4 + x^3 + x + 1). -/
structure K where
  bits : BitVec 64
  deriving DecidableEq

namespace K
/-- Carry-less product of two polynomials of degree < 64 (schoolbook shift-and-xor). -/
def clmul (a b : BitVec 64) : BitVec 128 :=
  Fin.foldl 64 (fun acc i => if a.getLsbD i then acc ^^^ (b.zeroExtend 128 <<< (i : Nat)) else acc) 0
/-- One fold: hi·x^64 + lo ↦ hi·(x^4+x^3+x+1) + lo, since x^64 ≡ 0x1B. -/
def fold (t : BitVec 128) : BitVec 128 :=
  clmul ((t >>> 64).setWidth 64) 0x1B ^^^ (t.setWidth 64).zeroExtend 128
/-- Two folds bring the degree below 64. -/
def reduce (t : BitVec 128) : BitVec 64 := (fold (fold t)).setWidth 64

instance : Zero K := ⟨⟨0⟩⟩
instance : One K := ⟨⟨1⟩⟩
instance : Add K := ⟨fun a b => ⟨a.bits ^^^ b.bits⟩⟩      -- char 2: + = - = xor
instance : Neg K := ⟨fun a => a⟩
instance : Sub K := ⟨fun a b => ⟨a.bits ^^^ b.bits⟩⟩
instance : Mul K := ⟨fun a b => ⟨reduce (clmul a.bits b.bits)⟩⟩

/-- 8 little-endian bytes (Rust `u64::to_le_bytes`). -/
def toBytes (a : K) : List (BitVec 8) :=
  List.ofFn fun i : Fin 8 => (a.bits >>> (8 * i.val)).setWidth 8
/-- Exactly 8 bytes; every 8-byte string is canonical. -/
def ofBytes? : List (BitVec 8) → Option K
  | [b0, b1, b2, b3, b4, b5, b6, b7] => some ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0⟩
  | _ => none
end K
-- … R1CS with z = 1 :: (x ++ w), sparse rows, `Holds`, `Decidable` (probe shape; P2 decides) …
end RecursionFast
```

Sanity theorem to publish alongside. The statement is trusted and the proof lives in the library
(`RecursionFastLib/Field.lean`):

```lean
noncomputable abbrev f64 : (ZMod 2)[X] := X ^ 64 + X ^ 4 + X ^ 3 + X + 1
theorem K_spec : Irreducible f64 ∧ ∃ e : K ≃ AdjoinRoot f64,
    e 0 = 0 ∧ e 1 = 1 ∧ (∀ a b : K, e (a + b) = e a + e b) ∧ (∀ a b : K, e (a * b) = e a * e b)
```

How the library builds `Field K` (verbatim shape): `toBF64 a := BF64.ofBitVec a.bits` and
`toBF64_mul : toBF64 (a * b) = toBF64 a * toBF64 b := rfl`. The remaining operations (`⁻¹`, `/`,
`•`, `^`, casts) are defined as `ofBF64 (op (toBF64 ·))`, and then
`instance : Field K := toBF64_injective.field toBF64 rfl rfl (fun _ _ => rfl) …`. All 18
obligations are `rfl`. `rfl` checks in `R8Probes/Axioms.lean` show that the instance's `*` and `+`
are the contract's.

E in the library:
- `structure E where c0 c1 c2 : K`;
- `mul` is the 9-product formula folded by `y^3 = y+1` (the same as leanerVM `mul_limbs`);
- `Field E` comes from pulling back along `E → BF64.Ext3`. The multiplicativity proof is `lift_mul`,
  6 lines by `linear_combination` with `ext3Gen_pow_three`;
- `card_E = 2^192`, `Algebra K E`;
- `toBytes`: 24 bytes, limbs `c0, c1, c2`, each 8 bytes little-endian.

Pitfalls to document in the contract:
- Numerals ≥ 2 in `K` are characteristic-2 casts (`(2 : K) = 0` once `Field K` is in scope).
  Literal field elements must be written `⟨0x…⟩`, or come from bytes.
- `deriving DecidableEq` gives a kernel-reducible equality. Keep the contract a **classic,
  non-`module` file**, as P1 does: CompPoly and ArkLib are `module`s, and leanerVM reports that
  `module` importers cannot kernel-reduce non-exposed bodies.

## 5. Implications

1. **Trusted lines.** K plus its encoding is about 25 code lines (all of P1-style `Field.lean`,
   including the R1CS, is 46), with no import. Compare the prime-field D1 plan (`ZMod p` plus
   `norm_num` primality): this is similar in size, and Mathlib-free.
2. **Machine encoding.** K is 8 bytes and E is 24 bytes, little-endian per limb. Every byte string
   is canonical, unlike prime fields, so no range check is needed. Fiat–Shamir challenge sampling
   into E is **exactly uniform** from 24 hash bytes [I]. That removes D1 §3.1's bias obligation for
   binary fields.
3. **Kernel and computability budget** [V]:
   - kernel ≈ 39 ms per K mul and ≈ 0.3 s per E mul;
   - E inverse is not kernel-evaluable (Fermat exponent recursion);
   - compiled 28 µs per K mul, interpreted 1 ms per E mul.

   So spec verifiers are fine for `decide` only on tiny instances. Any harness evaluation of an
   honest prover at 2^20+ needs a fast executable implementation, which is missing.
4. **RISC-V cost** [I, from R6 §1.2]. RV64IM has no `clmul`. A K multiply is a 64-step
   shift/xor/branch loop plus two folds, about 300 cycles, or about 150–200 cycles with a 4-bit
   window table. An E multiply (9 K mults) costs about 1.5–3k cycles. BabyBear costs about 10
   cycles per mul. Binary-field verifiers will be dominated by field arithmetic unless the
   contract adds Zbc (`clmul`/`clmulh`; R6 estimates 50–100 trusted lines and 4–10 constructors)
   or a GF(2^64)-multiply ECALL. **This is now a first-order design decision, not a later track.**
5. **What submitters get for binary-field proofs.**
   - Usable now:
     - RS and IRS over E with additive domains;
     - unique-decoding and Johnson-range line MCA (BCIKS20 UD, DKT26, BCGM25, DG25);
     - AHIV22 Lemma 4.5 (Ligero/Brakedown style);
     - tensor-fold MCA;
     - the native sumcheck (soundness in char 2);
     - Schwartz–Zippel;
     - the additive NTT (CompPoly, proved correct).
   - Missing:
     - any proved FRI/STIR/WHIR (FRI requires `NonBinaryField`; WHIR's constrained RS and folding
       need multiplicative domains);
     - every Binius, FRI-Binius and ring-switching security theorem (sorried);
     - capacity-regime MCA in char 2 (the hypothesis excludes it; CS25 and BCHKS25 even give
       char-2 lower bounds);
     - a positive subfield-code / extension-challenge correlated-agreement theorem;
     - a `BF64` ↔ tower isomorphism;
     - `SampleableType` instances for K and E (leanerVM's `Protocol/Field.lean` has the pattern).
   - [I] The cheapest proven path for a binary submission is a Ligero/Brakedown-style or
     unique-decoding RS IOP over E, with an additive domain inside K and sumcheck. Its proofs can
     be assembled from clean ArkLib lemmas.
6. **Comparator.** Use it unpatched. Expect about 100 s per submission for the BF64 and Ext3 proof
   closure. That is well within D1's 3 h budget.

## 6. Verified vs inferred

- **Verified:**
  - all compile, eval, timing, comparator and closure numbers;
  - the CompPoly declarations and line numbers;
  - leanerVM's usage;
  - Mathlib's `GaloisField` limitations;
  - FRI's `NonBinaryField` requirement;
  - `ReedSolomon.code`'s generic domain.
- **From the census (read by a subagent, not re-read by me):** ArkLib theorem hypotheses and taint
  status in §1.3, beyond what is listed as verified.
- **Inferred:**
  - why Ext6 fails replay but BF64 does not;
  - RISC-V cycle estimates;
  - honest-prover time;
  - uniform E sampling;
  - the usability of generic MCA results with `F := E`;
  - the Rabin-from-scratch effort for option (b).
