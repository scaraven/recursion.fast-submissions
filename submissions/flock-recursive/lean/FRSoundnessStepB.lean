-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2; stage S-G1b). The round doom follows
-- `submissions/spartan-srom/lean/SpartanSromSoundnessDefs.lean` (`SumWrong`, `clOut`) and
-- `SpartanSromSoundnessKS.lean` (the round rows), re-stated for Flock's positions.
import FRSoundnessStepA
import FRSumcheck

/-!
# The step law at `εR = 15/2^124`, and the degree-3 sumcheck rounds (BLUEPRINT §5.1–§5.2)

* **Part A: the error.** `epsR = 15/2^124` (the contract's per-query error of this entry) is
  split (§10 changes 15) into the Hide potential's `epsH = 2^-142 + 2^-238` and the doom
  potential's `epsD = εR − ε_H` (`epsD_add_epsH`); `deltaR = εD − 2^-142` is the rows' budget,
  after the H row's `2^-142`. `StepObl D rnd δ N` packages `hloc_of`'s five per-position
  obligations; **`step_epsD`** turns them, at `δ = deltaR` and `N ≤ 2^256·deltaR`, into the
  contract's `KState.step` law with error `εD`.
* **Part B: one phase end to end, the degree-3 F rounds** (Z3; also the shape of Lr2 and E2). The
  phase starts at Fiat–Shamir position `b` and has `nMax` items `(absorb, squeeze)`; the first
  `nr κ` rounds are real for kind `κ` (the rest are dummies, which keep the claim). Round `l`'s
  message is `c₀ ‖ c₁ ‖ c₂` and the verifier sets `c₃ := claim + (c₁ + c₂)` (`roundOpsF … 3`), so
  the round always passes its check (`g3_check`). The **truth** is a parameter: the initial claim
  `c0 L es` and the tables `T L es` (sizes `2^(nr κ)`) of an expression `e` of degree 3, read off
  the log and the chain's entries before the phase. **`D3`**: past the phase's first absorb, the
  running claim after the answered rounds is not the true sum of the bound tables.
  **`rounds3_obl`** proves the five obligations with `N = 3·2^128` (`round_escape_le`,
  `card_chF_fiber`), and **`rounds3_step`** the contract's step law with error `εD`.
* **Part C: Z3** (`b = 15`, 26 items, `m − 6` real rounds): `z3_step`.

What the truth must satisfy is explicit: it reads the entries before `b` only (`hTc`), its tables
have the right sizes (`hsz`), and it reads the same values off the charging log `L.take i` and
`L` (`hst`, the stage-review ruling of §10 changes 10).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

/-! ## Part A: the error `εR` and the obligations -/

/-- The entry's per-query knowledge error: `εR = 15/2^124 ≈ 2^-120.093`. -/
noncomputable def epsR : ℝ≥0 := 15 / 2 ^ 124

/-- **The Hide potential's per-query error** (§10 changes 15): its H row `2^-142` and its rounds'
`2^18/2^256 = 2^-238` (at most `eᵢ ≤ 2^18` hiding challenges per P1.i round). -/
noncomputable def epsH : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 142 + (2 : ℝ≥0)⁻¹ ^ 238

/-- **The doom potential's per-query error**: `εD = εR − ε_H`, so that `εD + ε_H = εR`. -/
noncomputable def epsD : ℝ≥0 := epsR - epsH

/-- The rows' budget: `εD − 2^-142` (the H row takes `2^-142`, `badCount_frac_le`). -/
noncomputable def deltaR : ℝ≥0 := epsD - (2 : ℝ≥0)⁻¹ ^ 142

theorem h_le_epsR : (2 : ℝ≥0)⁻¹ ^ 142 ≤ epsR := by
  rw [epsR, inv_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

theorem epsH_le_epsR : epsH ≤ epsR := by
  rw [← NNReal.coe_le_coe, epsH, epsR]
  push_cast
  norm_num

theorem epsD_coe : (epsD : ℝ) = 15 / 2 ^ 124 - 1 / 2 ^ 142 - 1 / 2 ^ 238 := by
  rw [epsD, NNReal.coe_sub epsH_le_epsR, epsH, epsR]
  push_cast
  norm_num

theorem h_le_epsD : (2 : ℝ≥0)⁻¹ ^ 142 ≤ epsD := by
  rw [← NNReal.coe_le_coe, epsD_coe]
  push_cast
  norm_num

/-- **The two potentials' errors add up to `εR`** (kernel-checked: `ε_H ≤ εR`). -/
theorem epsD_add_epsH : epsD + epsH = epsR := tsub_add_cancel_of_le epsH_le_epsR

theorem deltaR_coe : (deltaR : ℝ) = 15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 := by
  rw [deltaR, NNReal.coe_sub h_le_epsD, epsD_coe]
  push_cast
  ring

/-- **The doom potential's error**: the H row and the rows' budget fit `εD`. -/
theorem err_le_epsD : (badCount : ℝ≥0) / 2 ^ 256 + deltaR ≤ epsD :=
  calc (badCount : ℝ≥0) / 2 ^ 256 + deltaR ≤ (2 : ℝ≥0)⁻¹ ^ 142 + deltaR := by
        gcongr; exact badCount_frac_le
    _ = epsD := add_tsub_cancel_of_le h_le_epsD

/-- A single-squeeze row of `N` answers fits the budget when `N/2^256 ≤ deltaR` (in ℝ). -/
theorem N_le_deltaR {N : ℕ} (h : (N : ℝ) / 2 ^ 256 ≤ 15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238) :
    (N : ℝ≥0) ≤ 2 ^ 256 * deltaR := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, deltaR_coe]
  push_cast
  rw [div_le_iff₀ (by positivity)] at h
  linarith

open Classical in
/-- **The five per-position obligations of `hloc_of`** for a doom predicate `D`, the phase map
`rnd`, the multi-squeeze budget `δ` and the single-squeeze count `N`. -/
structure StepObl (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ)) (δ : ℝ≥0) (N : ℕ) :
    Prop where
  habs : ∀ L es x len, Matches (es ++ [x]) → fsItems[es.length]? = some (.absorb len) →
    D L es → D L (es ++ [x])
  hmid : ∀ L es x s0 r, Matches (es ++ [x]) → rnd es.length = some (s0, r) →
    es.length < s0 + r → (D L (es ++ [x]) ↔ D L es)
  hsingle : ∀ L es, Matches es → fsItems[es.length]? = some .squeeze → rnd es.length = none →
    (Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ N
  hround : ∀ L es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
    rnd (s0 + 1) = some (s0, r) → condCount D L es₀ r [] ≤ δ
  hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ k as,
    (D (L.take i) (ext ((entriesOf L (pathOf L i)).take k) as) ↔
      D L (ext ((entriesOf L (pathOf L i)).take k) as))

open Classical in
/-- **`step_epsD`**: the contract's `KState.step` law with error `εD = εR − ε_H` for the potential
`muG D (pRoundG D fsRnd)`, from the obligations at `δ = deltaR` and `N ≤ 2^256·deltaR`. -/
theorem step_epsD {D : Log → Log → Prop} {N : ℕ} (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR)
    (ob : StepObl D fsRnd deltaR N) (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : muG D (pRoundG D fsRnd) L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D (pRoundG D fsRnd) (L ++ [(q, a)]) ≤
      (muG D (pRoundG D fsRnd) L + epsD) * 2 ^ 256 :=
  (muG_step_of fsRnd_ok fsRnd_zero deltaR N hN ob.habs ob.hmid ob.hsingle ob.hround ob.hstab hl
    hμ hq).trans (by gcongr; exact err_le_epsD)

/-- A multi-squeeze phase on which `D` cannot escape is charged nothing. -/
theorem condCount_eq_zero {D : Log → Log → Prop} {L es₀ : Log} {r : ℕ}
    (h : ∀ as : List Digest, as.length = r → ¬ EscAtG D L (ext es₀ as)) :
    condCount D L es₀ r [] = 0 := by
  classical
  unfold condCount extCount
  rw [Finset.filter_false_of_mem fun v _ => h _ (by simp)]
  simp

/-! ## Part B: the degree-3 F rounds -/

/-- Binding one more challenge is mapping `bind0`. -/
theorem bindAll_append {R : Type*} [CommRing R] (ts : Array (Array R)) (rs : List R) (r : R) :
    bindAll ts (rs ++ [r]) = (bindAll ts rs).map (bind0 · r) := by
  induction rs generalizing ts with
  | nil => rfl
  | cons r' rs ih => exact ih _

theorem bindAll_size {R : Type*} [CommRing R] {m : ℕ} :
    ∀ (rs : List R) (ts : Array (Array R)), (∀ t ∈ ts, t.size = 2 ^ (rs.length + m)) →
      ∀ t ∈ bindAll ts rs, t.size = 2 ^ m
  | [], ts, h => fun t ht => by simpa using h t ht
  | r :: rs, ts, h => bindAll_size rs _ (map_bind0_size ts r fun t ht => by
      rw [h t ht]; congr 1; simp; omega)

section Rounds3

variable (b : ℕ)

/-- Round `l`'s coefficients from claim `c`: `c₀, c₁, c₂` from the message at `b + 2l`, and
`c₃ = c + (c₁ + c₂)` (`roundOpsF … 3`, `FRVIRSpec.g3`). -/
def g3At (es : Log) (l : ℕ) (c : F) : Array F :=
  #[readF (msgAt es (b + 2 * l)) 0, readF (msgAt es (b + 2 * l)) 16,
    readF (msgAt es (b + 2 * l)) 32,
    c + (readF (msgAt es (b + 2 * l)) 16 + readF (msgAt es (b + 2 * l)) 32)]

/-- Round `l`'s challenge: the first F coordinate of the answer at `b + 2l + 1`. -/
def rch (es : Log) (l : ℕ) : F := fAt es (b + 2 * l + 1) 0

/-- The first `l` challenges. -/
def rchs (es : Log) (l : ℕ) : List F := (List.range l).map (rch b es)

variable (c0 : Log → Log → F)

/-- The running claims: `c0`, then `g_l(r_l)`. -/
def clR (L es : Log) : ℕ → F
  | 0 => c0 L es
  | l + 1 => peval (g3At b es l (clR L es l)) (rch b es l)

variable (nr : Kind → ℕ)

/-- The rounds answered by the entries `es`: `min (nr (kindOf es)) ⌊(|es| − b)/2⌋`. -/
def ans3 (es : Log) : ℕ := min (nr (kindOf es)) ((es.length - b) / 2)

variable (e : Expr) (T : Log → Log → Array (Array F))

/-- The claim after `l` rounds is not the true sum of the tables bound at the first `l`
challenges. -/
def Wrong3 (L es : Log) (l : ℕ) : Prop :=
  clR b c0 L es l ≠ trueSum e (bindAll (T L es) (rchs b es l)) (nr (kindOf es) - l)

/-- **The round doom** (§5.2 row Z3): past the phase's first absorb, the running claim after the
answered rounds is false. -/
def D3 (L es : Log) : Prop := b < es.length ∧ Wrong3 b c0 nr e T L es (ans3 b nr es)

variable {b c0 nr e T}

theorem peval_four (x0 x1 x2 x3 r : F) :
    peval #[x0, x1, x2, x3] r = x0 + r * (x1 + r * (x2 + r * x3)) := by
  simp [peval_eq_sum, Finset.sum_range_succ]
  ring

/-- The round's check always passes (`c₃` is set from the claim; characteristic two). -/
theorem g3_check (es : Log) (l : ℕ) (c : F) :
    peval (g3At b es l c) 0 + peval (g3At b es l c) 1 = c := by
  unfold g3At
  generalize readF (msgAt es (b + 2 * l)) 0 = x0
  generalize readF (msgAt es (b + 2 * l)) 16 = x1
  generalize readF (msgAt es (b + 2 * l)) 32 = x2
  rw [peval_four, peval_four]
  linear_combination (x0 + x1 + x2) * CharTwo.two_eq_zero (R := F)

theorem g3_size (es : Log) (l : ℕ) (c : F) : (g3At b es l c).size = 4 := rfl

theorem rchs_succ (es : Log) (l : ℕ) : rchs b es (l + 1) = rchs b es l ++ [rch b es l] := by
  simp [rchs, List.range_succ]

theorem rchs_congr {es es' : Log} {l : ℕ} (h : Agree es es' (b + 2 * l)) :
    rchs b es l = rchs b es' l := by
  unfold rchs rch fAt ansAt
  refine List.map_congr_left fun j hj => ?_
  rw [h _ (by simp at hj; omega)]

theorem clR_congr {L es es' : Log} (hc : c0 L es = c0 L es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) → clR b c0 L es l = clR b c0 L es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR]
    rw [clR_congr hc (h.mono (by omega))]
    simp only [g3At, rch, fAt, ansAt, msgAt, h (b + 2 * l) (by omega),
      h (b + 2 * l + 1) (by omega)]

theorem clR_log_congr {L L' es : Log} (hc : c0 L' es = c0 L es) :
    ∀ l, clR b c0 L' es l = clR b c0 L es l
  | 0 => hc
  | l + 1 => by simp only [clR, clR_log_congr hc l]

/-- What the truth must satisfy: it reads the entries before `b` only. -/
def TruthLocal (b : ℕ) (c0 : Log → Log → F) (T : Log → Log → Array (Array F)) : Prop :=
  ∀ L es es', Agree es es' b → T L es = T L es' ∧ c0 L es = c0 L es'

theorem wrong3_congr (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) : Wrong3 b c0 nr e T L es l ↔ Wrong3 b c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong3, clR_congr hc h, rchs_congr h, hT, kindOf_congr (hb.mono hb1)]

theorem kindOf_append {es : Log} (x : ByteArray × Digest) (h : 0 < es.length) :
    kindOf (es ++ [x]) = kindOf es :=
  kindOf_congr (agree_append es [x] h)

/-- When the next position is not a real round's squeeze, appending keeps the answered rounds and
the doom. -/
theorem D3_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2) :
    D3 b c0 nr e T L (es ++ [x]) ↔ D3 b c0 nr e T L es := by
  have hk := kindOf_append x (show 0 < es.length by omega)
  have ha : ans3 b nr (es ++ [x]) = ans3 b nr es := by
    simp only [ans3, hk, List.length_append, List.length_singleton]
    rcases hc with hc | hc
    · rw [show (es.length + 1 - b) / 2 = (es.length - b) / 2 by omega]
    · rw [min_eq_left hc, min_eq_left (le_trans hc (Nat.div_le_div_right (by omega)))]
  have hle : b + 2 * ans3 b nr es ≤ es.length := by
    have : ans3 b nr es ≤ (es.length - b) / 2 := min_le_right _ _
    omega
  simp only [D3, ha, List.length_append, List.length_singleton]
  rw [wrong3_congr hb1 hTc (agree_append es [x] hle)]
  exact ⟨fun h => ⟨hlen, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem not_D3_short {L es : Log} (h : es.length ≤ b) : ¬ D3 b c0 nr e T L es :=
  fun hd => by have := hd.1; omega

theorem entAt_ext1 (es : Log) (a : Digest) : (entAt (ext1 es a) es.length).2 = a := by
  simp [entAt, ext1]

/-- At a real round's squeeze, the extension answers one more round, and its claim and truth
are the round polynomial and the bound tables at the answer's first F coordinate. -/
theorem wrong3_ext1 (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (L es : Log) (a : Digest) {j : ℕ}
    (hj : es.length = b + 2 * j + 1) :
    Wrong3 b c0 nr e T L (ext1 es a) (j + 1) ↔
      peval (g3At b es j (clR b c0 L es j)) (chF a 0) ≠
        trueSum e ((bindAll (T L es) (rchs b es j)).map (bind0 · (chF a 0)))
          (nr (kindOf es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
  have hr : rch b (ext1 es a) j = chF a 0 := by
    simp only [rch, fAt, ansAt]
    rw [← hj, entAt_ext1]
  obtain ⟨hT, hc0⟩ := hTc L (ext1 es a) es (hA.mono (by omega))
  have hcl : clR b c0 L (ext1 es a) j = clR b c0 L es j :=
    clR_congr (l := j) hc0 (hA.mono (by omega))
  have hg : g3At b (ext1 es a) j (clR b c0 L es j) = g3At b es j (clR b c0 L es j) := by
    simp only [g3At, msgAt, hA (b + 2 * j) (by omega)]
  have hrs : rchs b (ext1 es a) j = rchs b es j := rchs_congr (l := j) (hA.mono (by omega))
  simp only [Wrong3, clR, hcl, hg, hr, rchs_succ, hrs, hT, hk, bindAll_append]

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **The round row** (§5.2 Z3): from a doomed claim, at most `3·2^128` answers make the next
claim true. -/
theorem D3_single (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (he : e.deg = 3)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOf es)) (L es : Log) :
    (Finset.univ.filter fun a => D3 b c0 nr e T L es ∧ ¬ D3 b c0 nr e T L (ext1 es a)).card ≤
      3 * 2 ^ 128 := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D3_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2 ((D3_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOf es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong3 b c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs b es j), t.size = 2 ^ (nr (kindOf es) - j - 1 + 1) := by
    refine bindAll_size (rchs b es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs b es j)) hts
    (claim := clR b c0 L es j) (by
      rw [show nr (kindOf es) - j - 1 + 1 = nr (kindOf es) - j by omega]; exact hw)
    (g3At b es j (clR b c0 L es j))
  refine le_trans (Finset.card_le_card (t := Finset.univ.filter fun a : Digest => chF a 0 ∈ _)
    fun a ha => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  have hnd : ¬ D3 b c0 nr e T L (ext1 es a) := by
    rw [Finset.mem_filter] at ha; exact ha.2.2
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong3 b c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong3_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨by rw [he]; rfl, g3_check es j _⟩, ?_⟩
  rw [hnw, show nr (kindOf es) - (j + 1) = nr (kindOf es) - j - 1 by omega]

theorem length_ext : ∀ (as : List Digest) (es : Log), (ext es as).length = es.length + as.length
  | [], _ => rfl
  | a :: as, es => by
    rw [show ext es (a :: as) = ext (ext1 es a) as from rfl, length_ext as]
    simp [ext1]; omega

theorem D3_log_congr {L L' X : Log} (hT : T L' X = T L X) (hc : c0 L' X = c0 L X) :
    D3 b c0 nr e T L' X ↔ D3 b c0 nr e T L X := by
  simp only [D3, Wrong3, clR_log_congr hc, hT]

/-- **The position facts of a rounds phase**: it starts at `b ≥ 1`, has `nMax ≥ 1` items
`(absorb, squeeze)` of which at most `nMax` are real, and no multi-squeeze phase meets it. -/
structure RoundsPhase (b nMax : ℕ) (nr : Kind → ℕ) : Prop where
  hb1 : 1 ≤ b
  hn0 : 0 < nMax
  hnr : ∀ κ, nr κ ≤ nMax
  hsq : ∀ j < nMax, fsItems[b + 2 * j + 1]? = some .squeeze
  hph : ∀ p s0 r, fsRnd p = some (s0, r) → p < b ∨ b + 2 * nMax ≤ p

/-- What the truth must read the same off the charging log and the whole log (§10 changes 10). -/
def TruthStable (c0 : Log → Log → F) (T : Log → Log → Array (Array F)) : Prop :=
  ∀ L i, ¬ Bad L → IsChain L i → ∀ k as,
    T (L.take i) (ext ((entriesOf L (pathOf L i)).take k) as) =
        T L (ext ((entriesOf L (pathOf L i)).take k) as) ∧
      c0 (L.take i) (ext ((entriesOf L (pathOf L i)).take k) as) =
        c0 L (ext ((entriesOf L (pathOf L i)).take k) as)

/-- **The five obligations for the round doom** at `δ = deltaR`, `N = 3·2^128`. -/
theorem rounds3_obl {nMax : ℕ} (P : RoundsPhase b nMax nr) (hTc : TruthLocal b c0 T)
    (he : e.deg = 3) (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOf es))
    (hst : TruthStable c0 T) : StepObl (D3 b c0 nr e T) fsRnd deltaR (3 * 2 ^ 128) where
  habs L es x len _ hit hd := by
    refine (D3_append_iff P.hb1 hTc x hd.1 ?_).mpr hd
    by_contra hc
    simp only [not_or, not_le] at hc
    have h := P.hsq ((es.length - b) / 2) (lt_of_lt_of_le hc.2 (P.hnr _))
    rw [show b + 2 * ((es.length - b) / 2) + 1 = es.length by have := hd.1; omega, hit] at h
    cases h
  hmid L es x s0 r _ hr _ := by
    rcases P.hph _ _ _ hr with h | h
    · exact ⟨fun hd => absurd hd (not_D3_short (by simp; omega)),
        fun hd => absurd hd (not_D3_short (by omega))⟩
    · exact D3_append_iff P.hb1 hTc x (by have := P.hn0; omega)
        (Or.inr (le_trans (P.hnr _) (by omega)))
  hsingle L es _ _ _ := D3_single P.hb1 hTc he hsz L es
  hround L es₀ s0 r _ hl hr := by
    rw [condCount_eq_zero]
    · exact zero_le
    intro as has ⟨_, hd, hnd⟩
    obtain ⟨-, hpr, hspec⟩ := fsRnd_ok _ _ _ hr
    have hlen := length_ext as es₀
    have hne : ext es₀ as ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have hdl : (ext es₀ as).dropLast.length = s0 + r := by
      rw [List.length_dropLast, hlen]; omega
    by_cases hfar : b + 2 * nMax ≤ s0 + 1
    · have := (D3_append_iff P.hb1 hTc ((ext es₀ as).getLast hne)
        (by have := P.hn0; omega) (Or.inr (le_trans (P.hnr _) (by omega)))).mpr hd
      rw [List.dropLast_append_getLast hne] at this
      exact hnd this
    · have h1 : s0 + 1 < b := (P.hph _ _ _ (hspec (s0 + 1) (by omega) hpr).2).resolve_right
        (by omega)
      have h2 : s0 + r < b := by
        rcases P.hph _ _ _ (hspec (s0 + r) (by omega) le_rfl).2 with h | h
        · exact h
        · have := P.hph _ _ _ (hspec b (by omega) (by omega)).2
          have := P.hn0
          omega
      exact not_D3_short (by omega) hd
  hstab L i hb hci k as := by
    obtain ⟨hT, hc⟩ := hst L i hb hci k as
    exact D3_log_congr hT hc

theorem three_le_deltaR : ((3 * 2 ^ 128 : ℕ) : ℝ≥0) ≤ 2 ^ 256 * deltaR :=
  N_le_deltaR (by push_cast; norm_num)

open Classical in
/-- **The contract's step law for the round doom**, with error `εD = εR − ε_H`. -/
theorem rounds3_step {nMax : ℕ} (P : RoundsPhase b nMax nr) (hTc : TruthLocal b c0 T)
    (he : e.deg = 3) (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOf es))
    (hst : TruthStable c0 T) (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : muG (D3 b c0 nr e T) (pRoundG (D3 b c0 nr e T) fsRnd) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG (D3 b c0 nr e T) (pRoundG (D3 b c0 nr e T) fsRnd) (L ++ [(q, a)]) ≤
      (muG (D3 b c0 nr e T) (pRoundG (D3 b c0 nr e T) fsRnd) L + epsD) * 2 ^ 256 :=
  step_epsD three_le_deltaR (rounds3_obl P hTc he hsz hst) L q hl hμ hq

end Rounds3

/-! ## Part C: Z3 (`b = 15`, 26 items, `m − 6` real rounds) -/

/-- Z3's odd offsets are squeezes (checked on `fsItems`). -/
theorem z3_sq_check : (List.range 26).all (fun j => fsItems[16 + 2 * j]? == some .squeeze) = true :=
  by decide +kernel

theorem z3_phase : RoundsPhase 15 26 (mm 6) where
  hb1 := by norm_num
  hn0 := by norm_num
  hnr κ := by cases κ <;> decide
  hsq j hj := by
    have := z3_sq_check
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at this
    rw [show 15 + 2 * j + 1 = 16 + 2 * j by omega]
    exact this j hj
  hph p s0 r h := by
    have hmem := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    rw [fsRanges_eq] at hmem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem z3_start : phStart 5 = 15 := by rw [phStart, fsStarts_eq]; rfl

open Classical in
/-- **Z3's step law** (§5.2 row Z3, error `εD`), for any truth of degree 3 that reads the entries
before Z3 only and is stable under the charging log. -/
theorem z3_step {e : Expr} {T : Log → Log → Array (Array F)} {c0 : Log → Log → F}
    (hTc : TruthLocal 15 c0 T) (he : e.deg = 3)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ mm 6 (kindOf es)) (hst : TruthStable c0 T)
    (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : muG (D3 15 c0 (mm 6) e T) (pRoundG (D3 15 c0 (mm 6) e T) fsRnd) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG (D3 15 c0 (mm 6) e T) (pRoundG (D3 15 c0 (mm 6) e T) fsRnd) (L ++ [(q, a)]) ≤
      (muG (D3 15 c0 (mm 6) e T) (pRoundG (D3 15 c0 (mm 6) e T) fsRnd) L + epsD) * 2 ^ 256 :=
  rounds3_step z3_phase hTc he hsz hst L q hl hμ hq

/-! ## Part D: the other degree-3 F round phases, Lr2 (`b = 178`) and E2 (`b = 256`) -/

theorem fsRnd_mem {p s0 r : ℕ} (h : fsRnd p = some (s0, r)) :
    (s0, r) ∈ fsRanges ∧ s0 < p ∧ p ≤ s0 + r := by
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- A rounds phase from a checked item range and a checked gap between the multi-squeeze
phases. -/
theorem roundsPhase_of {b nMax : ℕ} {nr : Kind → ℕ} (hb1 : 1 ≤ b) (hn0 : 0 < nMax)
    (hnr : ∀ κ, nr κ ≤ nMax)
    (hsq : (List.range nMax).all (fun j => fsItems[b + 2 * j + 1]? == some .squeeze) = true)
    (hgap : fsRanges.all (fun x => decide (x.1 + x.2 < b ∨ b + 2 * nMax ≤ x.1 + 1)) = true) :
    RoundsPhase b nMax nr where
  hb1 := hb1
  hn0 := hn0
  hnr := hnr
  hsq j hj := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hsq
    exact hsq j hj
  hph p s0 r h := by
    obtain ⟨hmem, h1, h2⟩ := fsRnd_mem h
    simp only [List.all_eq_true, decide_eq_true_eq] at hgap
    have := hgap _ hmem
    omega

theorem lr2_phase : RoundsPhase 178 15 (nodeOnly 15) :=
  roundsPhase_of (by norm_num) (by norm_num) (fun κ => by cases κ <;> decide)
    (by decide +kernel) (by rw [fsRanges_eq]; decide)

theorem e2_phase : RoundsPhase 256 21 (nodeOnly 21) :=
  roundsPhase_of (by norm_num) (by norm_num) (fun κ => by cases κ <;> decide)
    (by decide +kernel) (by rw [fsRanges_eq]; decide)

/-! ## Controls -/

/-- Control (positive): a false initial claim dooms the chain at the phase's first absorb. -/
theorem D3_first_absorb (nr : Kind → ℕ) (L : Log) :
    D3 15 (fun _ _ => 1) nr (.var 0) (fun _ _ => #[]) L (List.replicate 16 default) := by
  refine ⟨by simp, ?_⟩
  simp [Wrong3, ans3, clR, trueSum, tbl, rchs, bindAll, Expr.eval]

/-- Control (negative): before the phase's first absorb nothing is doomed. -/
theorem not_D3_before (nr : Kind → ℕ) (L : Log) (c0 : Log → Log → F)
    (T : Log → Log → Array (Array F)) (e : Expr) :
    ¬ D3 15 c0 nr e T L (List.replicate 15 default) :=
  not_D3_short (by simp)

end FR.Snd
