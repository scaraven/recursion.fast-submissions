# S-D (track L-pcs): RESULT

Stage S-D of `flock-recursive` (BLUEPRINT §9: "`mca_ud_line` over K with `C_mca` fixed and
`≤ 2^60` at every level; `fold_preserves`, `interp_F`, `positions_bad_le`, `cap_binding`;
`FRRS`'s triangularity and tensor identity"). 2026-10-27, branch `v4/flock-recursive` (work
uncommitted on top of `c38bda1`), build tree `logs/fr-build-pcs`, logs under `logs/S-D/`.
Specs read: BLUEPRINT revisions 2 and 3.1 (§2.1–2.2, §5.2–5.6, §7, §9, App. A, §10),
BP-crypto-review (M4, M8, rounds 2 and 3). Evidence tags: **kernel** (theorem name), **measured**
(log).

## 0. Headline

* **`mca_ud_line` is proved in full generality** (any field, any `n` distinct points, `RS[K,x,k]`,
  `2e + k ≤ n`) with **`C_mca(n, k, e) = k e + n`**, then instantiated at `K = GF(2^256)`, `C_K`
  on `D` (**kernel**: `FR.mca_ud_line_cover`, `FR.mca_ud_line`, `FR.mca_ud_line_K`). At the
  largest level (`m = 32`, level 0) `C_mca = 2^37 + 2^20 ≈ 2^37.0 ≤ 2^60`; the P1 row becomes
  `(2^(ℓ−r)(k e + n) + 2)/2^256 ≤ 2^-214.0` (was `≤ 2^-190` with the working value).
* The proof does **not** follow §5.3's plan (rank over `K(Z)`, division in `K(Z)[X]`): a counting
  argument gives the bivariate Berlekamp–Welch pair unconditionally, and no division is needed
  (§3). FR-R8 (the rank argument's risk) is closed.
* The exact statement was probed before proving: no counterexample (§4).
* `fold_preserves` (as an iff, plus `fold_lift`), `interp_F`, `positions_bad_le`, `cap_binding`,
  `colL_prefix`, block-triangularity, the tensor identity, `W_linear`, `C_K = RS[K, D, k]`, and
  computable twins of `Ŵ_v(D[j])`, `Enc` and the tensor weight are proved. 46 declarations
  checked, axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`} (`logs/S-D/axioms.log`); no
  `sorry`, no `native_decide`; source rule 0 findings (`logs/S-D/source-rule.log`).

## 1. What was built

Code lines by the core's `scripts/loc.py` (`logs/S-D/loc.txt`):

| Module | code (total) | §7 budget | Content |
|---|---|---|---|
| `FRRS` | 419 (593) | 600 | **Generic RS code** `rsCode x k`, `agreeSet`, `agreeSet₂`, `rs_eq_of_agree`, `rs_interp` (`interp_agree`, Lagrange), `rs_minDist` (distance `n − k + 1`). **Bits and the tensor identity** (`bitSel`, `bitProd`, `bit_induction`, `eqBits`, `tensor_identity` over any commutative ring). **Novel basis** (`subW` = `W_v = Π_{a<2^v}(X − pt a)`, `normW` = `Ŵ_v`, `novelX` = `X_x`): `natDegree_subW`, `normW_eval_self`, `normW_eval_lt`, `novelX_natDegree` (degree exactly `x`), **block-triangularity** `novelX_eval_zero` / `novelX_eval_lt_msb`, `novelX_tensor`; **`W_linear`** (`subW_add`, `normW_add`) and the LCH recursion `normW_succ` (char 2, additive domain). **`Enc_k`** (`enc`, `encL`, `encCode`, `encPoly`), `exists_encPoly`, `encPoly_ne_zero`, **`encCode_eq_rsCode`** (`C_M = RS[M, pt, k]`), `enc_injective`. **The domain** `D j := (word j, 0) ∈ F`, `D_xor`, `D_injOn` (`[0, 2^64)`), `Dpts`, `encCode_D`. |
| `FRRSEval` | 120 (181) | 300 | Computable twins: `wRow` (table `Ŵ_v(pt 2^i)` by the LCH recursion, `O(N²)`), `wAt` (`Ŵ_v(pt j)` by bits), `encTwin`, `tensorTwin` (`tensorW` of A.5); `wAt_eq`, `encTwin_eq`, `tensorTwin_eq`; protocol instances `wAtD`, `encD` (`D`, `N = 20`), `wAtD_eq`, `encD_eq`. |
| `FRProximityBW` | 42 (74) | 500 | `mul_mem_degreeLT`, `poly_eq_zero_of_vanish`, **`close_unique`**, **`bw_unique`**. |
| `FRProximityLine` | 227 (329) | 1,000 | Coefficient arrays as bivariate polynomials (`polyOf`, `colPoly`, `rowPoly`), the residual `bwRes`, the linear map `bwMap`; `bw_exists` (counting), `bw_E_ne`, `bw_few_zero_cols`, `line_eq_root`; **`lineBad`**, **`cMca`**, **`mca_ud_line_cover`**, **`mca_ud_line`**, **`mca_ud_line_K`**, `round_bad_cover` (the P1 row's union over `m` lines). |
| `FRProximityFold` | 226 (341) | 500 | `jointAgree`, **`JointClose`**, `pairRows`, `foldRows`, `good_line`, **`fold_lift`**, **`fold_preserves`**; `rsCode_map`, **`interp_F`**, `enc_algebraMap`, **`interp_F_D`**; **`positions_card`**, **`positions_bad_le`**; the controls (§2). |
| `FRMerkle` | 212 (333) | 750 | `MerkleEnc` (the query encodings as a parameter with the laws used), `stepQ`, `climb`, `openPath`; `pre`, **`colL`**, `Collision`, `Hit`; `pre_of_mem`, `runLog_query`, **`cap_binding`**, `pre_append`, **`colL_append`**, `pre_none_append`, **`colL_prefix`**, `collision_append`, `hit_append`; a toy encoding `toyEnc` and the controls (§2). Imports `RecursionFast.Contract.Oracle` only. |
| **total** | **1,246** (1,851) | 3,650 | |

Main statements (all **kernel**):

```lean
theorem FR.mca_ud_line_cover {K} [Field K] [DecidableEq K] {n} {x : Fin n → K}
    (hx : Function.Injective x) {k e : ℕ} (h : 2 * e + k ≤ n) (u₀ u₁ : Fin n → K) :
    ∃ B : Finset K, B.card ≤ cMca n k e ∧ lineBad (rsCode x k) e u₀ u₁ ⊆ B
theorem FR.mca_ud_line [Finite K] … : Nat.card (lineBad (rsCode x k) e u₀ u₁) ≤ cMca n k e
theorem FR.mca_ud_line_K (hn : n ≤ 2^64) (hk : k ≤ 2^64) (h : 2 * e + k ≤ n) (u₀ u₁ : Fin n → FR.K) :
    Nat.card (lineBad (encCode (M := FR.K) D n k) e u₀ u₁) ≤ cMca n k e
-- lineBad C e u₀ u₁ = {z | ∃ w ∈ C, n − e ≤ #agreeSet (u₀ + z•(u₁ − u₀)) w ∧
--     ¬ ∃ v₀ ∈ C, ∃ v₁ ∈ C, agreeSet₂ u₀ u₁ v₀ v₁ = agreeSet (u₀ + z•(u₁ − u₀)) w}   (§5.3 verbatim)
-- cMca n k e = k * e + n
theorem FR.fold_preserves (hx) (h : 2 * e + k ≤ n) (hz : ∀ c, z ∉ lineBad (rsCode x k) e (U₀ c) (U₁ c)) A :
    JointClose (rsCode x k) e (pairRows U₀ U₁) A ↔ JointClose (rsCode x k) e (foldRows z U₀ U₁) A
theorem FR.interp_F_D (hn) (hk) (hv : v ∈ encCode (M := K) D n k) (f : Fin n → F) A (hA : k ≤ #A)
    (hvA : ∀ j ∈ A, v j = algebraMap F K (f j)) : ∃ c : Fin k → F, v = enc D n k (algebraMap F K ∘ c)
theorem FR.positions_bad_le (S : Finset (Fin n)) (t e) (hS : #S + e < n) :
    (#{f : Fin t → Fin n | ∀ i, f i ∈ S} : ℚ) / n ^ t ≤ (1 − e / n) ^ t
theorem FR.Merkle.cap_binding (hc : ¬ Collision L) (h : (openPath E col j ss).runLog L = some d) :
    colL E L d ss.length j = some col
theorem FR.tensor_identity (r w : ℕ → R) ℓ :
    ∑ x ∈ range (2^ℓ), eqBits r ℓ x * bitProd w ℓ x = ∏ v ∈ range ℓ, (1 − r v + r v * w v)
theorem FR.novelX_eval_lt_msb (pt) (hx : x ≠ 0) (hj : j < 2 ^ x.log2) : (novelX pt x).eval (pt j) = 0
```

## 2. Controls

All **kernel**; `FRProximityFold` §Controls and `FRMerkle` §Controls.

| Definition | Control | Kind | What it shows |
|---|---|---|---|
| `cMca`, `mca_ud_line` | `pcsLevels_ok` | positive | at all ten levels (`P30`, `L32`): `2e + k ≤ n ≤ 2^64`, `C_mca ≤ 2^60`, `2^6 C_mca + 2 ≤ 2^66` (P1 `≤ 2^-190`), by `decide` |
| `lineBad` | `lineBad_codewords` | positive | a line of codewords has an empty bad set (the definition is not "everything") |
| `lineBad` | `lineBad_nonempty` | negative | over GF(5), points 0, 1, 2, `k = e = 1` (`2e + k ≤ n`): `(0,0,1)`–`(0,1,0)` is bad at `z = 0` (not "nothing"; the bound is not vacuous) |
| `close_unique` | `close_not_unique_at_d` | negative | at `2e = d` (GF(5), `n = 2`, `k = e = 1`) two distinct codewords are equally close: the hypothesis is needed (§5.6's "two-codeword counterexample") |
| `Enc`, `coeffs_of_values` | `enc_D_dist`, `enc_injective` | positive/negative | distinct messages differ in `≥ n − k + 1` positions; a codeword has one message |
| novel basis on `D` | `novel_D_ok` | positive | `D_injOn` discharges the hypotheses: `Ŵ_v(D[2^v]) = 1`, `X_x ≠ 0` of degree `x` |
| block-triangularity | `novel_D_triangular` | negative | `X_{2^v}` vanishes on `D[0…2^v)` but is `1` at `D[2^v]`: the vanishing stops at the bound |
| `D` | `D_two_pow_64` | negative | `D (2^64) = D 0`: injectivity holds only below `2^64` (`D_injOn`) |
| `positions_card` | `positions_card_toy` | positive | `n = 4, t = 2, S = {0, 1}`: 4 of 16 pairs |
| `MerkleEnc` | `toyEnc` | positive | the structure's laws are satisfiable (a toy byte encoding) |
| `cap_binding` | `cap_binding_toy` | positive | its hypotheses hold on a two-entry log; it reads the column under the path's top |
| `cap_binding` | `cap_binding_needs_noCollision` | negative | with two column queries answered alike, a path of `toyCol'` evaluates to `dg 0` but the column read under `dg 0` is `toyCol`: the no-collision hypothesis is needed |

`tensor_identity`, `novelX_tensor`, `fold_preserves` and `interp_F` have no hypotheses that could be
vacuous beyond those discharged above (`hx` by `Dpts_injective`, `2e + k ≤ n` by `pcsLevels_ok`,
`hz` by `round_bad_cover` off a set of `m · C_mca` elements, which is `< |K|`).

## 3. The proof of `mca_ud_line` (why it is shorter than §5.3's plan)

§5.3 plans BCIKS20's route: rank deficiency of an `n × (k+2e+1)` system over `K(Z)` once more than
`e + 1` values `z` are close, a kernel vector with denominators cleared, long division
`N = E Q + R` in `K(Z)[X]`, and `O(k(e+1))` bounds on `Q`'s coefficient degrees. Implemented
instead (`FRProximityLine` docstring):

1. **Counting instead of rank.** Take the error-locator `X`-degree `a := n − k − e` (`≥ e`, the
   largest that keeps BW uniqueness: `deg N < a + k = n − e`) and `Z`-degrees `e` (for `E`) and
   `e + 1` (for `N`). The homogeneous linear system `N(x_j, Z) = E(x_j, Z)(u₀_j + Z(u₁_j − u₀_j))`
   has `(a+1)(e+1) + (n−e)(e+2)` unknowns and `n(e+2)` equations; `(a+1)(e+1) ≥ (e+1)² > e(e+2)`,
   so a nonzero solution exists **for every pair `u₀, u₁`** (`bw_exists`,
   `LinearMap.ker_ne_bot_of_finrank_lt`).
2. `E ≠ 0` (`bw_E_ne`); `E(x_j, Z) = 0` at most at `a` positions (`bw_few_zero_cols`), so there
   are `k` positions `J` with `E(x_j, Z) ≢ 0`; `v₀, v₁ ∈ C` interpolate `u₀, u₁` on `J`.
3. For close `z` off the `≤ k e` roots of the `E(x_j, Z)`, `j ∈ J`: `bw_unique` gives
   `N(X, z) = E(X, z) P` for the close codeword `P`, so `P = u_z` on `J`, so `P = v₀ + z(v₁ − v₀)`
   (two codewords agreeing on `k` points).
4. Off the joint agreement set of `(u₀, u₁)` with `(v₀, v₁)`, each position's difference is a
   nonzero affine function of `z` (`line_eq_root`): `≤ n` more values. Every other close `z` has
   agreement set exactly the joint one.

Bad `z ⊆ S₁ ∪ S₂`, `|S₁| ≤ k e`, `|S₂| ≤ n`. No threshold on the number of close `z`, no rational
functions, no division.

## 4. Probes (**measured**)

* `logs/S-D/mca_exact_probe.py` → `mca_exact_probe.log`: the **exact** §5.3 statement (line
  `u₀ + z(u₁ − u₀)`, conclusion "∃ v₀ v₁ ∈ C with joint agreement set = agreeSet(u_z, w)"), K =
  GF(256), D ⊂ GF(16), exhaustive over the 256 values of z, random / codeword-plus-errors /
  errors-on-a-line words, 25 trials per kind, `(n, k, e)` ∈ {(6,2,2), (8,1,3), (8,2,3), (10,2,4),
  (9,3,3), (12,2,5), (12,4,4)} at the full UD radius. Worst bad count `e + 1`; bound `k e + n`
  never approached; no counterexample.
* `logs/S-D/mca_beyond_ud_probe.py` → `mca_beyond_ud_probe.log`: at `2e = d` (one past the
  hypothesis), `n = 4, k = 1, e = 2`, the worst count over 40 random lines was 6 = `k e + n`.
  Whether `mca_ud_line` itself fails at `2e = d` is open (not needed); the negative control of the
  hypothesis is `close_not_unique_at_d`.

## 5. Build and kernel times (**measured**, development VM, shared)

| Measure | Value | Log |
|---|---|---|
| `lake build FRRS FRRSEval FRProximityBW FRProximityLine FRProximityFold FRMerkle` (field modules cached) | 20.0 s wall; per module 4.6–6.5 s | `logs/S-D/build.log` |
| axioms of 46 declarations | the three standard ones | `logs/S-D/axioms.log` |
| source rule (whole `submissions/flock-recursive`) | 32 files, 0 findings | `logs/S-D/source-rule.log` |

Per module, `lake env lean -DElab.async=false --profile` pinned to one core (`taskset -c 7`), as
TRACK-RULES now asks; "kernel" is the profiler's `type checking`:

| Module | wall | kernel | elaboration | import | Log |
|---|---|---|---|---|---|
| `FRRS` | 14.1 s | 0.49 s | 0.54 s | 4.0 s | `profile-FRRS.log` |
| `FRRSEval` | 8.3 s | 0.11 s | 0.22 s | 4.0 s | `profile-FRRSEval.log` |
| `FRProximityBW` | 7.5 s | 0.10 s | 0.06 s | 4.0 s | `profile-FRProximityBW.log` |
| `FRProximityLine` | 12.0 s | 0.65 s | 0.21 s | 4.0 s | `profile-FRProximityLine.log` |
| `FRProximityFold` | 10.4 s | 0.25 s | 0.30 s | 3.8 s | `profile-FRProximityFold.log` |
| `FRMerkle` | 10.4 s | 2.55 s | 1.01 s | 1.3 s | `profile-FRMerkle.log` |

Kernel total ≈ 4.2 s; `FRMerkle`'s 2.55 s is the `decide` controls on byte arrays.

## 6. Deviations from the blueprint (and blueprint changes requested)

1. **`C_mca n k e := k e + n`**, not the working value `4 n (k+1)(e+1)` (§5.3 lets the closing
   proof fix it). **Change requested**: §5.3's working value and proof plan (steps (2)–(4) → the
   counting route of §3 above), B-5's "by the bivariate Berlekamp–Welch rank argument", §5.2 P1
   row `C_mca = k e + n` (worst `2^-214.0`, level 0, `m = 32`); FR-R8 closed.
2. **Hypothesis `2 * e + k ≤ n`** for §5.3's `2e < n − k + 1`: the integer reading (with `ℕ`
   subtraction, `n − k + 1` would be `1` for `k > n`); `pcsLevels_ok` discharges it at every level.
3. **Two forms of the statement**: `mca_ud_line_cover` (any field: the bad set is inside a
   `Finset` of `≤ C_mca` elements) and `mca_ud_line` (`Nat.card` for a finite field, §5.3's form).
   The cover form is the one to use in `step` (it does not depend on `Nat.card` of a set being
   finite).
4. **`fold_preserves` is one round, for an arbitrary pairing** `(U₀ c, U₁ c)`, as an iff with
   the same `A`, plus `fold_lift` (the lifted codewords fold to the given ones). The `ℓ`-round
   iteration is left to `ligerito_final` (L-cert), because which row bit a round folds first is
   the transcript's (S-0) convention. `round_bad_cover` gives the round's union bound
   `m · C_mca`.
5. **`interp_F`** is stated for codewords (generic `interp_F`) and as "`Enc_K` of an `F`-message"
   on `D` (`interp_F_D`).
6. **`positions_bad_le`** counts index tuples (`Fin t → Fin n`, repetition allowed, as R2-M3
   requires); the map from squeeze answers to indices (`idxOf`) and the probability over answers
   are L-cert's.
7. **`FRMerkle` is parametric in the query encodings** (`MerkleEnc`), as instructed; the blueprint
   §7 lists `FRMerkle` under L-cert, the orchestrator assigned it to L-pcs. Digests are the full
   32-byte BLAKE2s outputs (no truncation, unlike spartan-srom). The verifier's path (`openPath`)
   is the semantics of A.5's `askCol`, `askNode`, `bitOf`, `selectHalf` sequence.
8. **Controls live in the modules** (`FRProximityFold` §Controls, `FRMerkle` §Controls) rather
   than in `FRControls` (L-cert's). `FRProximityFold` declares the instance
   `Fact (Nat.Prime 5)` for the GF(5) controls.
9. `D` is defined in `FRRS` (`D j = F.ofB64 ⟨UInt64.ofNat j⟩`) with `D_injOn` on `[0, 2^64)`
   (A.1 names `D_inj`, "decide on words"; it is proved symbolically).
10. `FR.lean` (L-cert's) does not import the S-D modules; see open question 4.

## 7. Open questions

1. **`MerkleEnc` for the protocol** (S-0 / L-cert): instantiate with
   `FRTranscriptDefs.nodeQ i`, `colQ i` and parse functions (`parseNode` = strip `tagNode i`, split
   64 bytes; `parseCol` = strip `tagCol i`); the laws are those `toyEnc` proves for a toy layout.
2. **`carried` vs the in-play windows** (S-0 / L-cert): `colL_prefix` needs "no answer equal to a
   digest carried in an earlier input", for the node queries' children and the cap entries in the
   cap's absorb. BLUEPRINT §5.1's Bad covers **16-byte-aligned** 32-byte windows. In the node query
   `"FRMNOD" ‖ i ‖ 0 ‖ l ‖ r` the children sit at query offsets 8 and 40, so they are windows only
   if the hashed stream places each query at an offset `≡ 8 (mod 16)`; the same question for the
   cap entries inside `"FRABS000" ‖ st ‖ msg` (offset 40 + 32·index). S-0's stream framing must
   make every carried digest an aligned window, or `Bad` must list them explicitly.
3. **`eqBits` vs `FRMLE.eq`**: `eqBits r ℓ x = Π_v (r_v if bit v of x else 1 − r_v)` is
   `FRMLE.eq r (cube x)` (bit `v` ↔ coordinate `v`, little-endian, both). A one-line bridge belongs
   wherever both are imported (L-cert).
4. `FR.lean` should import `FRRS`, `FRRSEval`, `FRProximityBW`, `FRProximityLine`,
   `FRProximityFold`, `FRMerkle` (L-cert owns it).
5. The computable twins recompute the table row per call (`O(v N)` field operations per
   `Ŵ_v(D[j])`); if the IR interpreter evaluates `tensorW` through `wAtD`, it should precompute
   the `20 × 20` table once (a `wRow`-based array with the same spec lemma).

## 8. Definition of done (BLUEPRINT §9, S-D)

| Item | Status |
|---|---|
| `mca_ud_line` over K with `C_mca` fixed and `≤ 2^60` at every level | `mca_ud_line_K`, `cMca = k e + n`, `pcsLevels_ok` |
| `fold_preserves` | `fold_preserves`, `fold_lift`, `round_bad_cover` |
| `interp_F` | `interp_F`, `interp_F_D` |
| `positions_bad_le` | `positions_card`, `positions_bad_le` |
| `cap_binding` | `FR.Merkle.cap_binding`, `colL_prefix`, `colL_append` (parametric in the encoding) |
| `FRRS`'s triangularity and tensor identity | `novelX_eval_zero`, `novelX_eval_lt_msb`, `tensor_identity`, `novelX_tensor`, `tensorTwin_eq` |
| controls | §2 |
| axioms, `sorry`, `native_decide`, source rule | three axioms; none; none; 0 findings |

Not committed (TRACK-RULES).
