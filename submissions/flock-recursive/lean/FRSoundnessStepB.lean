-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2; stage S-G1b). The round doom follows
-- `submissions/spartan-srom/lean/SpartanSromSoundnessDefs.lean` (`SumWrong`, `clOut`) and
-- `SpartanSromSoundnessKS.lean` (the round rows), re-stated for Flock's positions.
-- RET-1: position-free declarations moved to `FRSoundnessCoreSteps`.
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreTruths`.
import FRSoundnessStepA
import FRSumcheck
import FRSoundnessCoreSteps
import FRSoundnessCoreTruths

/-!
# The step law at `εR = 15/2^124`, and the degree-3 sumcheck rounds (BLUEPRINT §5.1–§5.2)

* **Part A: the error.** `epsR = 15/2^124` (the contract's per-query error of this entry) is
  split (§10 changes 15) into the Hide potential's `epsH = 2^-142 + 2^-238` and the doom
  potential's `epsD = εR − ε_H` (`epsD_add_epsH`); `deltaR = εD − 2^-142` is the rows' budget,
  after the H row's `2^-142`. `StepObl D rnd δ N` packages `hloc_of`'s five per-position
  obligations; **`step_epsD`** turns them, at `δ = deltaR` and `N ≤ 2^256·deltaR`, into the
  library's `KState.step` law with error `εD`.
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
  hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ X, StabExt rnd (entriesOf L (pathOf L i)) X →
    (D (L.take i) X ↔ D L X)

open Classical in
/-- **`step_epsD`**: the library's `KState.step` law with error `εD = εR − ε_H` for the potential
`muG D (pRoundG D fsRnd)`, from the obligations at `δ = deltaR` and `N ≤ 2^256·deltaR`. -/
theorem step_epsD {D : Log → Log → Prop} {N : ℕ} (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR)
    (ob : StepObl D fsRnd deltaR N) (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : muG D (pRoundG D fsRnd) L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D (pRoundG D fsRnd) (L ++ [(q, a)]) ≤
      (muG D (pRoundG D fsRnd) L + epsD) * 2 ^ 256 :=
  (muG_step_of fsRnd_ok fsRnd_zero deltaR N hN ob.habs ob.hmid ob.hsingle ob.hround ob.hstab hl
    hμ hq).trans (by gcongr; exact err_le_epsD)

/-! ## Part B: the degree-3 F rounds -/

section Rounds3

variable (b : ℕ)

variable (c0 : Log → Log → F)

variable (nr : Kind → ℕ)

variable (e : Expr) (T : Log → Log → Array (Array F))

variable {b c0 nr e T}

/-- **The position facts of a rounds phase**: it starts at `b ≥ 1`, has `nMax ≥ 1` items
`(absorb, squeeze)` of which at most `nMax` are real, and no multi-squeeze phase meets it. -/
structure RoundsPhase (b nMax : ℕ) (nr : Kind → ℕ) : Prop where
  hb1 : 1 ≤ b
  hn0 : 0 < nMax
  hnr : ∀ κ, nr κ ≤ nMax
  hsq : ∀ j < nMax, fsItems[b + 2 * j + 1]? = some .squeeze
  hph : ∀ p s0 r, fsRnd p = some (s0, r) → p < b ∨ b + 2 * nMax ≤ p

/-- What the truth must read the same off the charging log and the whole log, on `hloc_of`'s
extensions (`StabExt`; §10 changes 10). -/
def TruthStable (c0 : Log → Log → F) (T : Log → Log → Array (Array F)) : Prop :=
  ∀ L i, ¬ Bad L → IsChain L i → ∀ X, StabExt fsRnd (entriesOf L (pathOf L i)) X →
    T (L.take i) X = T L X ∧ c0 (L.take i) X = c0 L X

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
  hstab L i hb hci X hX := by
    obtain ⟨hT, hc⟩ := hst L i hb hci X hX
    exact D3_log_congr hT hc

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

theorem e2_phase : RoundsPhase 221 21 (nodeOnly 21) :=
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
