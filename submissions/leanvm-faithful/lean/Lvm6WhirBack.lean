-- lvm6 X8b (W1 F-W2-4 (b), RG's "open for X"): the opening's facts read backwards. From `OpenSem` (the facts an
-- accepting opening leaves, `Lvm6WhirGW`) a level-0 tuple of the ball satisfies the opening's claim: the final
-- polynomial's claim is taken back through every round (`ClaimBack`) and every transition (`TailBackP`). New.
import Lvm6WhirGW

/-!
# The opening, backwards

* `card_le_agree_of_nearT`: a near tuple loses at most one column of the agreement set.
* **`roundsBack`**: `GoodRs` over `j` rounds takes a tuple `P` of degree `≤ d` agreeing with the folded word on
  `aOut` columns and satisfying the folded claim back to a tuple `T` of degree `≤ d` agreeing with the level's
  word on `a` columns with `W T = σ` (one `ClaimBack` per round, one column lost per round, W1's threshold chain).
* **`openBack`**: on a ladder with `LadOK` and an admitted first weight, `OpenSem … w σ a cs l` gives a first-level
  tuple of degree `≤ lad.d`, agreeing with the first level's word on `a` columns, with `den w U = σ` (final level:
  the final polynomial; mid level: `TailBackP` at the next level's tuple, `hWH` drops the high part).
* **`openBack18`**: at `P18` (`lad18`, `w₀ cl`, a multiaffine claim): a level-0 tuple `U` in the list of commitment
  0's word with `den (w₀ cl) U = cl.2`; **`back18_holds`**: then `dec18 U ∈ ball18 h` and `cl.Holds 25 (dec18 U)`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.Whir
open scoped ENNReal

section Rounds

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n m : ℕ} (dom : Fin n ↪ F)

omit [Fintype F] [DecidableEq F] in
open Classical in
/-- A near tuple loses at most one column of the agreement set. -/
theorem card_le_agree_of_nearT {Q : Wd F n (m + 1)} {d : ℕ} {S : Finset (Fin n)} {T : Tup F (m + 1)}
    (h : NearT dom Q d S T) : S.card ≤ (agree dom T Q).card + 1 := by
  obtain ⟨-, hb⟩ := h
  refine le_trans ?_ (Nat.add_le_add_left hb _)
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  by_cases hx' : ∃ v, (T v).eval (dom x) ≠ Q v x
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hx'⟩)
  · exact Finset.mem_union_left _ ((mem_agree _ _ _ _).mpr fun v ↦ by
      by_contra hne
      exact hx' ⟨v, hne⟩)

omit [DecidableEq F] in
/-- **The rounds, backwards**: from `GoodRs` (one `ClaimBack` per round), a tuple satisfying the claim after
`j` rounds on `aOut` columns of the folded word comes from a tuple satisfying the level's claim on `a` columns
of the level's word. -/
theorem roundsBack {Ar : ℕ → ℕ} {d : ℕ} : ∀ (j t : ℕ) (rs : List (Rnd F)) (Q : Wd F n (m + j))
    (W : Tup F (m + j) →ₗ[F] F) (σ : F) (a : ℕ),
    GoodRs dom Ar d j t rs Q W σ →
    (∀ s, t ≤ s → s + 1 < t + j → Ar s ≤ Ar (s + 1) - 1) →
    (0 < j → a ≤ Ar t - 1) →
    ∀ P : Tup F m, DegLE d P → aOut Ar a t j ≤ (agree dom P (foldsQ dom j rs Q)).card →
      foldsW j rs W P = foldsC j rs σ →
      ∃ T : Tup F (m + j), DegLE d T ∧ a ≤ (agree dom T Q).card ∧ W T = σ
  | 0, _, _, _, _, _, _, _, _, _, P, hP, hA, hW => ⟨P, hP, hA, hW⟩
  | j + 1, t, rs, Q, W, σ, a, hG, hch, ha, P, hP, hA, hW => by
    obtain ⟨⟨-, hcb⟩, hG'⟩ := hG
    obtain ⟨T₁, hT₁, hA₁, hW₁⟩ := roundsBack j (t + 1) rs.tail _ _ _ (Ar t) hG'
      (fun s h1 h2 ↦ hch s (by omega) (by omega)) (fun _ ↦ hch t le_rfl (by omega)) P hP hA hW
    obtain ⟨T, hN, hWT⟩ := hcb T₁ hT₁ hA₁ hW₁
    refine ⟨T, hN.1, ?_, hWT⟩
    have h1 := card_le_agree_of_nearT dom hN
    have h2 := ha (Nat.succ_pos j)
    omega

end Rounds

section Ladder

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {WI : WtIface F} {I : ChalIface F} {εmax : ℝ≥0∞}

/-- **The opening, backwards**: on a ladder with its hypotheses and an admitted first weight, the opening's facts
give a first-level tuple of degree `≤ lad.d` agreeing with the first level's word on `a` columns and satisfying
the first claim. -/
theorem openBack : ∀ {n ℓ : ℕ} (lad : Lad F WI n ℓ) (a : ℕ), LadOK I εmax lad a →
    ∀ (w : WI.Wt (0 + ℓ)) (σ : F) (cs : List (ℕ × ℕ × Word)) (l : List Ev), lad.WOK w →
      OpenSem WI I lad w σ a cs l →
      ∃ U : Tup F (0 + ℓ), DegLE lad.d U ∧ a ≤ (agree lad.dom U (lad.word (cs.take (lad.i + 1)))).card ∧
        WI.den w U = σ
  | _, ℓ, .fin V, a, hok, w, σ, cs, l, hw, hs => by
    have hok' : FinOK I εmax V a := hok
    obtain ⟨rs, l₁, l₂, -, -, hG, s, l₃, l₄, -, -, hA, hC⟩ := hs
    have hC' := hC hw
    rw [den_wFolds] at hC'
    exact roundsBack V.Fv.dom ℓ V.t₀ rs _ _ σ a hG hok'.hchain hok'.ha (V.Fv.fpoly s) (V.Fv.fdeg s) hA hC'
  | _, ℓ, .mid M rest, a, hok, w, σ, cs, l, hw, hs => by
    obtain ⟨h, hrest⟩ := hok
    obtain ⟨rs, l₁, l₂, -, -, hG, o, l₃, l₄, -, -, htf, hs'⟩ := hs
    obtain ⟨-, htb, hc⟩ := htf
    obtain ⟨U, hU, hUa, hUw⟩ := openBack rest M.A' hrest _ _ cs l₄ (h.hglue w hw rs o) hs'
    rw [h.den_wGlue w hw rs o, hc] at hUw
    have hi : rest.i + 1 = M.i + 2 := by rw [h.hi']
    rw [hi, h.hdom'] at hUa
    rw [h.hd'] at hU
    obtain ⟨hq, hA⟩ := htb U ((mem_tupleList _ _ _ _ _).mpr ⟨hU, hUa⟩) hUw
    have hq0 := congrFun hq 0
    simp only [coefQ, Fin.cons_zero, Pi.zero_apply] at hq0
    have hWc : WI.den (wFolds WI ℓ rs w) (M.L.cand o.hi U) = foldsC ℓ rs σ := by
      rw [TailIface.cand, map_add, h.hWH w hw rs o.hi, add_zero]
      exact sub_eq_zero.mp hq0
    rw [den_wFolds] at hWc
    exact roundsBack M.L.dom ℓ M.t₀ rs _ _ σ a hG h.hchain h.ha (M.L.cand o.hi U) (M.L.cand_deg U o.hi hU)
      hA hWc

end Ladder

/-! ## At `P18` -/

/-- Level 0's word reads commitment `0` only. -/
theorem lad18_word_take (cs : List (ℕ × ℕ × Word)) :
    lad18.word (cs.take (lad18.i + 1)) = wordE true 0 (0 + 6) 21 cs := by
  funext u p
  show wordE true 0 (0 + 6) 21 (cs.take 1) u p = wordE true 0 (0 + 6) 21 cs u p
  simp only [wordE, List.getElem?_take, Nat.zero_lt_one, ite_true]

/-- **The opening, backwards, at `P18`**: for a multiaffine claim, an accepting opening's facts give a level-0
tuple in the list of commitment 0's word (degree `≤ 2^19 + 5`, agreement `≥ 1,053,294`) satisfying the claim. -/
theorem openBack18 (cl : StackClaim6) (hma : cl.Multiaffine 25) (cs : List (ℕ × ℕ × Word)) (l : List Ev)
    (hs : OpenSem WtE chalE2 lad18 (w₀ cl) cl.2 (1053300 - 6) cs l) :
    ∃ U : Tup E2 (0 + 6), DegLE (2 ^ 19 - 1 + 6) U ∧
      1053300 - 6 ≤ (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 cs)).card ∧
      WtE.den (w₀ cl) U = cl.2 := by
  obtain ⟨U, hU, hA, hW⟩ := openBack lad18 _ lad18_ok (w₀ cl) cl.2 cs l ⟨rfl, MA_w₀ cl hma⟩ hs
  rw [lad18_word_take] at hA
  exact ⟨U, hU, hA, hW⟩

/-- **The tuple's stack is in the ball and satisfies the claim.** -/
theorem back18_holds (cl : StackClaim6) (h : List Ev) (U : Tup E2 (0 + 6)) (hU : DegLE (2 ^ 19 - 1 + 6) U)
    (hA : 1053300 - 6 ≤ (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 (commits h))).card)
    (hW : WtE.den (w₀ cl) U = cl.2) : dec18 U ∈ ball18 h ∧ cl.Holds 25 (dec18 U) := by
  refine ⟨?_, hhold18 cl (commits h) U hU hA hW⟩
  rw [ball18_eq]
  exact ⟨U, (mem_tupleList _ _ _ _ _).mpr ⟨hU, hA⟩, rfl⟩

/-- `P18` is the deployed opening's shape. -/
theorem openKey_P18 : openKey P18 = true := by decide

/-- **A level-0 tuple of the list satisfying the claim `cl`** (the history's commitment 0). -/
def Back18 (cl : StackClaim6) (h : List Ev) (U : Tup E2 (0 + 6)) : Prop :=
  DegLE (2 ^ 19 - 1 + 6) U ∧
    1053300 - 6 ≤ (agree (domE 21 (by norm_num)) U (wordE true 0 (0 + 6) 21 (commits h))).card ∧
    WtE.den (w₀ cl) U = cl.2

/-- **From the opening's facts for a multiaffine claim, a level-0 tuple of the list satisfying it.** -/
theorem back18_of_GW (cl : StackClaim6) (h : List Ev) (hma : cl.Multiaffine 25) (hg : GW18c P18 cl h) :
    ∃ U, Back18 cl h U :=
  let ⟨_, _, _, hs⟩ := hg openKey_P18
  openBack18 cl hma (commits h) _ hs

end Lvm6.Whir
