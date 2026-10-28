-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-1): the position-free
-- declarations of the 3.x soundness modules that revision 4.1 reuses, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessLigerito` (1), `FRSoundnessHide` (11),
-- `FRSoundnessWalk` (10), `FRSoundnessPhases` (3). Content: `eqBits_eq_eq`, Hide's `bindL_mle`,
-- `hEll`, `err_total`, the `fsCheck` facts, the forest-walk lemmas on prefixes (`pathOf_take`,
-- `entriesOf_take`, `not_bad_take`) and the batch counts (`batch_single`, `batch_N_le`). The 3.x
-- modules import this one.
import FRSoundnessCoreSteps

/-! ## From `FRSoundnessLigerito` (1 declaration) -/

namespace FR

variable {R : Type*} [CommRing R]

/-- **`eqBits_eq_eq`**: `eqBits` is `eq` at the cube point, coordinate `v` against bit `v`. -/
theorem eqBits_eq_eq (r : ℕ → R) (ℓ : ℕ) (u : Fin (2 ^ ℓ)) :
    eqBits r ℓ u = eq (fun v : Fin ℓ => r v) (cube u) := by
  rw [eq_cube, eqBits, bitSel,
    Finset.prod_range (fun i => if (u : ℕ).testBit i then r i else 1 - r i)]

end FR

/-! ## From `FRSoundnessHide` (11 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- P1.i's rounds `ℓᵢ` (the same for every kind, `lvl_ell`). -/
def hEll (i : ℕ) : ℕ := (lvlStar i).ell

theorem fsCheck_absorb_squeezeQ (len : ℕ) (st : Digest) :
    fsCheck (.absorb len) (squeezeQ st) = false := by
  have h8 : (squeezeQ st).data.toList.take 8 = tagSqz := by
    rw [squeezeQ_data, List.take_append_of_le_length (by decide)]; rfl
  simp only [fsCheck, h8, Bool.and_eq_false_iff]
  left; decide

theorem fsCheck_absorb_default (len : ℕ) :
    fsCheck (.absorb len) (default : ByteArray × Digest).1 = false := by
  simp only [fsCheck, Bool.and_eq_false_iff]
  left; decide

/-- **A formal extension's entries past its prefix pass no absorb check** (they are squeezes, or
past the end). -/
theorem fsCheck_ext_ge (es₀ : Log) (as : List Digest) {p : ℕ} (hp : es₀.length ≤ p) (len : ℕ) :
    fsCheck (.absorb len) (entAt (ext es₀ as) p).1 = false := by
  induction as using List.reverseRecOn with
  | nil =>
    rw [ext_nil, entAt, List.getD_eq_default _ _ hp]; exact fsCheck_absorb_default len
  | append_singleton as a ih =>
    rw [ext_append, ext1]
    rcases Nat.lt_or_ge p (ext es₀ as).length with h | h
    · rw [entAt_append _ _ h]; exact ih
    · rcases Nat.lt_or_ge (ext es₀ as).length p with h' | h'
      · rw [entAt, List.getD_eq_default _ _ (by simp; omega)]; exact fsCheck_absorb_default len
      · have : p = (ext es₀ as).length := by omega
        subst this
        simp only [entAt, List.getD_eq_getElem?_getD, List.getElem?_concat_length,
          Option.getD_some]
        exact fsCheck_absorb_squeezeQ len _

theorem entAt_ext_lt (es₀ : Log) (as : List Digest) {p : ℕ} (hp : p < es₀.length) :
    entAt (ext es₀ as) p = entAt es₀ p := by
  conv_rhs => rw [← take_ext es₀ as]
  simp only [entAt, List.getD_eq_getElem?_getD, List.getElem?_take, hp, ite_true]

theorem entAt_take {es : Log} {k p : ℕ} (hp : p < k) : entAt (es.take k) p = entAt es p := by
  simp only [entAt, List.getD_eq_getElem?_getD, List.getElem?_take, hp, ite_true]

theorem hide_N_le : ((2 ^ 18 : ℕ) : ℝ≥0) ≤ 2 ^ 256 * (2 : ℝ≥0)⁻¹ ^ 238 := by
  rw [← NNReal.coe_le_coe]; push_cast; norm_num

/-- The Hide potential's error: its H row and its rounds fit `ε_H`. -/
theorem err_le_epsH : (badCount : ℝ≥0) / 2 ^ 256 + (2 : ℝ≥0)⁻¹ ^ 238 ≤ epsH := by
  rw [epsH]; gcongr; exact badCount_frac_le

/-- **Binding every variable evaluates the MLE** (`mle_fix0`, `tbl_bind0`). -/
theorem bindL_mle {R : Type*} [CommRing R] :
    ∀ (cs : List R) (t : Array R), t.size = 2 ^ cs.length →
      tbl 0 (bindL t cs) 0 = mle (tbl cs.length t) (pt cs)
  | [], t, _ => (mle_zero _ _).symm
  | c :: cs, t, ht => by
    have ht' : t.size = 2 ^ (cs.length + 1) := by simpa using ht
    have hs : (bind0 t c).size = 2 ^ cs.length := by
      rw [bind0_size, ht', pow_succ, Nat.mul_div_cancel _ two_pos]
    show tbl 0 (bindL (bind0 t c) cs) 0 = mle (tbl (cs.length + 1) t) (pt (c :: cs))
    rw [bindL_mle cs _ hs, pt_cons, mle_fix0, Fin.cons_zero, Fin.tail_cons, tbl_bind0 t c ht']

/-- **The errors add up** (kernel-checked): the doom potential's `badCount/2^256 + deltaR` and the
Hide potential's `badCount/2^256 + 2^-238` sum to at most `εR = 15/2^124`. -/
theorem err_total : ((badCount : ℝ≥0) / 2 ^ 256 + deltaR) +
    ((badCount : ℝ≥0) / 2 ^ 256 + (2 : ℝ≥0)⁻¹ ^ 238) ≤ epsR := by
  rw [← epsD_add_epsH]; exact add_le_add err_le_epsD err_le_epsH

/-- Control (toy, `mlDoom` over ℚ): the nonzero table `(1, 0)` is doomed before its challenge,
and the challenge `1` hides it (`1 + 1·(0 − 1) = 0`). -/
theorem mlDoom_toy : mlDoom 1 (#[1, 0] : Array ℚ) [] ∧ ¬ mlDoom 1 (#[1, 0] : Array ℚ) [1] := by
  refine ⟨fun h => ?_, fun h => h (funext fun u => ?_)⟩
  · have := congrFun h 0
    simp [tbl, bindL] at this
  · obtain ⟨u, hu⟩ := u
    obtain rfl : u = 0 := by simp at hu; omega
    simp [tbl, bindL, bind0]

end FR.Snd

/-! ## From `FRSoundnessWalk` (10 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle

theorem predIdx_take (L : Log) {t j : ℕ} (hj : j < t) :
    predIdx (L.take t) j = (predIdx L j).bind (Option.guard fun i => i < t) := by
  simp only [predIdx, List.getElem?_take, hj, ite_true]
  cases L[j]? with
  | none => rfl
  | some e =>
    simp only [Option.bind_some]
    cases stateIn e.1 with
    | none => rfl
    | some st => simp only [Option.bind_some, ansIdx, List.findIdx?_take]

theorem back_take (L : Log) {t : ℕ} : ∀ f j, j < t → back (L.take t) f j = back L f j := by
  intro f
  induction f with
  | zero => intro _ _; rfl
  | succ f ih =>
    intro j hj
    simp only [back, predIdx_take L hj]
    cases hp : predIdx L j with
    | none => rfl
    | some i =>
      by_cases hit : i < t
      · have hg : (some i).bind (Option.guard fun i => decide (i < t)) = some i := by
          simp [Option.guard, hit]
        rw [hg]
        dsimp only
        split_ifs with h
        · rw [ih i (by omega)]
        · rfl
      · have hg : (some i).bind (Option.guard fun i => decide (i < t)) = none := by
          simp [Option.guard, hit]
        rw [hg]
        dsimp only
        rw [ite_eq_right (show ¬ i < j by omega)]

/-- **A path that ends before `t` is the same in `L.take t`.** -/
theorem pathOf_take (L : Log) {t j : ℕ} (hj : j < t) : pathOf (L.take t) j = pathOf L j :=
  back_take L _ _ hj

theorem entriesOf_take (L : Log) {t : ℕ} {is : List ℕ} (h : ∀ i ∈ is, i < t) :
    entriesOf (L.take t) is = entriesOf L is := by
  unfold entriesOf
  refine List.map_congr_left fun i hi => ?_
  simp only [getElem!_def, List.getElem?_take, h i hi, ite_true]

theorem entriesOf_pathOf_take (L : Log) {t j : ℕ} (hj : j < t) :
    entriesOf (L.take t) (pathOf (L.take t) j) = entriesOf L (pathOf L j) := by
  rw [pathOf_take L hj, entriesOf_take L fun i hi => lt_of_le_of_lt (mem_pathOf_le hi) hj]

/-- **A prefix of a non-bad log is non-bad.** -/
theorem not_bad_take {L : Log} (hb : ¬ Bad L) (t : ℕ) : ¬ Bad (L.take t) := by
  rintro (⟨e₁, h₁, e₂, h₂, h⟩ | ⟨i, j, hij, hj, h⟩ | ⟨i, j, hij, hj, h⟩ | h)
  · exact hb (Or.inl ⟨e₁, List.mem_of_mem_take h₁, e₂, List.mem_of_mem_take h₂, h⟩)
  · have hj' : j < L.length := lt_of_lt_of_le hj (by simp)
    refine hb (Or.inr (Or.inl ⟨i, j, hij, hj', ?_⟩))
    simpa only [List.getElem_take] using h
  · have hj' : j < L.length := lt_of_lt_of_le hj (by simp)
    refine hb (Or.inr (Or.inr (Or.inl ⟨i, j, hij, hj', ?_⟩)))
    simpa only [List.getElem_take] using h
  · refine hb (Or.inr (Or.inr (Or.inr fun hn => h ?_)))
    rw [List.map_take]
    exact hn.sublist (List.take_sublist _ _)

/-- The path to `j` is the path to its predecessor, then `j`. -/
theorem pathOf_eq (L : Log) (j : ℕ) :
    pathOf L j = match predIdx L j with
      | some i => if i < j then pathOf L i ++ [j] else [j]
      | none => [j] := by
  rw [pathOf, back.eq_2]
  cases predIdx L j with
  | none => rfl
  | some i =>
    simp only
    split_ifs with h
    · rw [back_fuel L j i h]; rfl
    · rfl

/-- **The path to an entry of a path is the path's prefix.** -/
theorem pathOf_prefix (L : Log) :
    ∀ j k (hk : k < (pathOf L j).length), pathOf L (pathOf L j)[k] = (pathOf L j).take (k + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k hk
    have hp := pathOf_eq L j
    cases hq : predIdx L j with
    | none =>
      rw [hq] at hp
      simp only [hp, List.length_singleton] at hk
      obtain rfl : k = 0 := by omega
      rw [show (pathOf L j)[0] = j by simp [hp], hp]; rfl
    | some i =>
      rw [hq] at hp
      by_cases hij : i < j
      · simp only [hij, ite_true] at hp
        simp only [hp, List.length_append, List.length_singleton] at hk ⊢
        by_cases hkl : k < (pathOf L i).length
        · rw [List.getElem_append_left hkl, ih i hij k hkl,
            List.take_append_of_le_length (by omega)]
        · have : k = (pathOf L i).length := by omega
          subst this
          rw [List.getElem_append_right (le_refl _)]
          simp only [Nat.sub_self, List.getElem_singleton]
          rw [List.take_of_length_le (by simp), ← hp]
      · simp only [hij, ite_false] at hp
        simp only [hp, List.length_singleton] at hk
        obtain rfl : k = 0 := by omega
        rw [show (pathOf L j)[0] = j by simp [hp], hp]; rfl

theorem pathOf_lt {L : Log} {j k : ℕ} (hk : k + 1 < (pathOf L j).length) :
    (pathOf L j)[k] < (pathOf L j)[k + 1] := by
  have h1 := pathOf_prefix L j (k + 1) hk
  have hle : (pathOf L j)[k] ≤ (pathOf L j)[k + 1] := by
    apply mem_pathOf_le (j := (pathOf L j)[k + 1])
    rw [h1]
    exact List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  · have h0 := pathOf_prefix L j k (by omega)
    rw [h, h1] at h0
    have := congrArg List.length h0
    simp at this
    omega

/-- The prefix of chain `i` ending at its `m`-th entry is the chain of that entry. -/
theorem entriesOf_prefix (L : Log) (i : ℕ) {m : ℕ} (hm : m < (pathOf L i).length) :
    entriesOf L (pathOf L (pathOf L i)[m]) = (entriesOf L (pathOf L i)).take (m + 1) := by
  rw [pathOf_prefix L i m hm, entriesOf, entriesOf, List.map_take]

end FR.Snd

/-! ## From `FRSoundnessPhases` (3 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

open Classical in
/-- **A single-squeeze batching row** (A.10 L1, L3, Lr3, E3, B′): if the doom before the squeeze
means some of the `k + 1` claims `v` differs from its truth `t`, and the doom after it fails only
when the batch `Σ_i κ^i v_i` at the answer's first F coordinate `κ` equals the true batch, then at
most `k·2^128` answers escape. -/
theorem batch_single {k : ℕ} (D : Log → Log → Prop) (v t : Fin (k + 1) → F) (L es : Log)
    (hpre : D L es → v ≠ t)
    (hpost : ∀ a, D L es → ¬ D L (ext1 es a) →
      ∑ i, chF a 0 ^ i.val * v i = ∑ i, chF a 0 ^ i.val * t i) :
    (univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ k * 2 ^ 128 := by
  by_cases hD : D L es
  · have hS := batch_pow_bad_le (R := F) (hpre hD)
    convert single_F_le (fun a => D L es ∧ ¬ D L (ext1 es a)) _ hS fun a ha =>
      mem_filter.mpr ⟨mem_univ _, hpost a ha.1 ha.2⟩ using 2
    ext a; simp
  · rw [filter_false_of_mem fun a _ ha => hD ha.1]; simp

/-- Every batching count fits the single-squeeze budget (`k ≤ 239`; A.10's largest is B′'s
`J_f − 1 ≤ 20`). -/
theorem batch_N_le {k : ℕ} (hk : k ≤ 239) : ((k * 2 ^ 128 : ℕ) : ℝ≥0) ≤ 2 ^ 256 * deltaR := by
  have h := coord_le_deltaR hk
  rw [div_le_iff₀ (by positivity)] at h
  calc ((k * 2 ^ 128 : ℕ) : ℝ≥0) = (k : ℝ≥0) * 2 ^ 128 := by push_cast; ring
    _ ≤ deltaR * 2 ^ 128 * 2 ^ 128 := by gcongr
    _ = 2 ^ 256 * deltaR := by ring

/-- Control (positive): with all claims true nothing is doomed, so nothing escapes. -/
theorem batch_single_true {k : ℕ} (v : Fin (k + 1) → F) (L es : Log) :
    (univ.filter fun a => (fun (_ _ : Log) => v ≠ v) L es ∧
      ¬ (fun (_ _ : Log) => v ≠ v) L (ext1 es a)).card = 0 := by
  simp

end FR.Snd
