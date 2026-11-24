-- New for lvm6 K1: `TreeSpecStmt` (season 1's doom-spec shape) gives WP S's `Stmt.treeSpec treeProgS`.
import Lvm6KTree

/-!
# The bridge to WP S's `Stmt.treeSpec`

* `doomSpec_of`: a specification in season 1's shape (every stable candidate map on a finite type
  with at most one candidate, follower lead `0`) gives S's `DoomSpec` (a candidate map stable only
  after histories satisfying a guard `G`, candidates in `Stack`). Per start `h₀`, the constant map
  on the subtype `C h₀` is stable and finite; the fields of a `Spec` speak of one start at a time.
* `eqPt_boolPt`: S's weights `eqPt a (boolPt n x)` are `eqAtF a x`.
* **`tree_bridge : TreeBridgeStmt`**: `treeSpec` at every `κ ≥ 5` gives `Stmt.treeSpec treeProgS`.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.ASM (εS)
open RecursionFast
open Finset
open scoped ENNReal

/-! ## The doom calculus: season 1's shape to S's -/

theorem εS_eq_εI : εS = εI := rfl

open Classical in
/-- **Season 1's doom-spec shape gives S's `DoomSpec`.** -/
theorem doomSpec_of {α : Type} {p : VerifierProgram α} {Good : Stack → Prop}
    {Holds : α → Stack → Prop}
    (H : ∀ {β : Type} [Finite β] (C : List Ev → Set β), Stable C → (∀ hh, (C hh).ncard ≤ 1) →
      ∀ (stk : β → Stack) (R : β → Prop),
        Nonempty (Spec p (Doomed C (fun q ↦ Good (stk q) ∧ R q))
          (fun out hist ↦ Doomed C (fun q ↦ Holds out (stk q) ∧ R q) hist) εS 0 0)) :
    DoomSpec p Good Holds := by
  intro C R G hG hsub
  let C' : List Ev → Set Stack := fun h₀ ↦ {q | G h₀ ∧ q ∈ C h₀}
  have hsub' : ∀ h₀, (C' h₀).Subsingleton := fun h₀ _ ha _ hb ↦ hsub h₀ ha.1 ha.2 hb.2
  have hfin : ∀ h₀, Finite ↥(C' h₀) := fun h₀ ↦ (hsub' h₀).finite.to_subtype
  have hcard : ∀ h₀ (hh : List Ev), (Set.univ : Set ↥(C' h₀)).ncard ≤ 1 := fun h₀ _ ↦ by
    rw [Set.ncard_univ]
    haveI : Subsingleton ↥(C' h₀) := Set.subsingleton_coe _ |>.2 (hsub' h₀)
    haveI := hfin h₀
    exact Finite.card_le_one_iff_subsingleton.2 inferInstance
  let S : ∀ h₀ : List Ev, Spec p
      (Doomed (fun _ ↦ (Set.univ : Set ↥(C' h₀))) (fun q ↦ Good q.1 ∧ R q.1))
      (fun out hist ↦ Doomed (fun _ ↦ (Set.univ : Set ↥(C' h₀))) (fun q ↦ Holds out q.1 ∧ R q.1)
        hist) εS 0 0 :=
    fun h₀ ↦ (@H ↥(C' h₀) (hfin h₀) (fun _ ↦ Set.univ) (fun _ _ _ ↦ rfl) (hcard h₀) Subtype.val
      (fun q ↦ R q.1)).some
  refine ⟨{
    D := fun h₀ l ↦ G h₀ ∧ (S h₀).D h₀ l
    V := fun h₀ l ↦ if G h₀ then (S h₀).V h₀ l else 1
    le_one := ?_, start_D := ?_, start_V := ?_, read := ?_, grind := ?_, commit := ?_,
    sample := ?_, query := ?_, moveEnd := ?_, retEnd := ?_, retDoom := ?_, post := ?_,
    bound := ?_ }⟩
  · intro h₀ l
    split_ifs
    · exact (S h₀).le_one h₀ l
    · exact le_rfl
  · intro h₀ hP
    exact ⟨hP.1, (S h₀).start_D h₀ fun q _ hq ↦ hP.2 q.1 q.2.2 hq⟩
  · intro h₀ hP
    simp only [if_pos hP.1]
    exact (S h₀).start_V h₀ fun q _ hq ↦ hP.2 q.1 q.2.2 hq
  · intro h₀ l k x hl ha hD
    exact ⟨hD.1, (S h₀).read x hl ha hD.2⟩
  · intro h₀ l b k hl ha hD
    exact ⟨hD.1, (S h₀).grind hl ha hD.2⟩
  · intro h₀ l ht w k word hl ha hw hD
    exact ⟨hD.1, (S h₀).commit word hl ha hw hD.2⟩
  · intro h₀ l k hl ha
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).sample hl ha
    · simp only [if_neg hg]
      rw [Finset.sum_const, Finset.card_univ, nsmul_one]
      exact le_of_eq (ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _))
  · intro h₀ l i ps k rows hl ha hans
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).query hl ha hans
    · simp only [if_neg hg, le_refl]
  · intro h₀ l q hl ha hm hD
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).moveEnd hl ha hm fun h ↦ hD ⟨hg, h⟩
    · simp only [if_neg hg, le_refl]
  · intro h₀ l a hl ha hD
    by_cases hg : G h₀
    · simp only [if_pos hg]
      exact (S h₀).retEnd hl ha fun h ↦ hD ⟨hg, h⟩
    · simp only [if_neg hg, le_refl]
  · intro h₀ l a hl ha hD
    simp only [if_pos hD.1]
    exact (S h₀).retDoom hl ha hD.2
  · intro h₀ l a hl ha hD q hq hh
    rw [hG h₀ l hD.1] at hq
    exact (S h₀).post hl ha hD.2 ⟨q, hD.1, hq⟩ (Set.mem_univ _) hh
  · intro h₀ l hl hne hm hD
    simp only [if_pos hD.1]
    exact εS_eq_εI ▸ (S h₀).bound hl hne hm hD.2

/-! ## Claims: S's form and ours -/

theorem eqPt_boolPt : ∀ (a : List E2) (x : ℕ), eqPt a (boolPt a.length x) = eqAtF a x
  | [], _ => by simp [eqPt, boolPt, eqAtF]
  | r :: rs, x => by
    have hb : boolPt (rs.length + 1) x = (if x.testBit 0 then 1 else 0) :: boolPt rs.length (x / 2) := by
      simp only [boolPt, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ ↦ ?_
      simp only [Function.comp, Nat.testBit_succ]
    rw [List.length_cons, hb, eqPt, List.zipWith_cons_cons, List.prod_cons, ← eqPt,
      eqPt_boolPt rs (x / 2), eqAtF]
    congr 1
    rw [Nat.testBit_zero]
    by_cases h : x % 2 = 1 <;> simp [h, CharTwo.add_self_eq_zero]

theorem stepMleK_eq_holds (q : Stack) (c : SClaim) :
    (∑ x : Fin (2 ^ c.1.length), (fun pt ↦ eqPt c.1 pt) (boolPt c.1.length x) *
      algebraMap K E2 (q x)) = stepMleK c.1.length c.1 q := by
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ eqPt c.1 (boolPt c.1.length x) * algebraMap K E2 (q x))]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [eqPt_boolPt]

theorem bitE_eq (w : K) (z : ℕ) : bitE w z = bitF (w.toBitVec.getLsbD z) := by
  unfold bitE bitF; rfl

theorem treeCols_len {κ : ℕ} (hκ : 1 ≤ κ) {out : TreeOut} (hs : TreeShape κ out) (h : Digest) :
    ∀ c ∈ treeCols κ h out, c.1.length = κ + 6 := by
  have hρ := hs.2.1
  have hm := hs.2.2.2.2.2.2.1
  intro c hc
  simp only [treeCols, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hc
  rcases hc with ((⟨m, -, rfl⟩ | ⟨m, -, rfl⟩) | ⟨m, -, rfl⟩) | rfl <;>
    simp [hρ, hm] <;> omega

/-- S's claims at `κ + 6` variables give ours, with the lengths of the output. -/
theorem treeClaims_of_holds {κ : ℕ} (hκ : 1 ≤ κ) {out : TreeOut} (hs : TreeShape κ out) (h : Digest)
    (q : Stack) (hH : (toS κ h out).Holds (κ + 6) q) : TreeClaims κ q h out := by
  refine ⟨fun c hc ↦ ?_, hs.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2, fun i hi ↦ ?_⟩
  · have hl := treeCols_len hκ hs h c hc
    have := hH.2 _ (List.mem_map_of_mem (f := fun c ↦ ((fun pt ↦ eqPt c.1 pt), c.2))
      ((treeColsS_perm κ h out).mem_iff.2 hc))
    unfold StackClaim6.Holds at this
    refine ⟨hl, ?_⟩
    rw [← this, ← hl]
    exact (stepMleK_eq_holds q c).symm
  · have h1 := hH.1
    unfold SliceClaim.Holds at h1
    have := h1 ⟨i, hi⟩
    simp only [toS] at this
    rw [← this, Fin.sum_univ_eq_sum_range (fun x ↦ eqPt out.en.pt (boolPt (κ + 6) x) * bitE (q x) i)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← hs.2.2.2.2.2.2.2.2.1, eqPt_boolPt, bitE_eq]

/-! ## The bridge -/

/-- **The bridge**: `treeSpec` at every `κ ≥ 5` gives WP S's `Stmt.treeSpec treeProgS`. -/
theorem tree_bridge : TreeBridgeStmt := by
  intro H sh x
  by_cases hs : sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN
  · simp only [treeProgS, if_pos hs]
    have hμ : sh.M = sh.logN + 1 + 6 := by omega
    refine doomSpec_of fun {β} _ C hst hcard stk R ↦ ?_
    obtain ⟨S⟩ := H (sh.logN + 1) (by omega) C hst hcard stk x.h R 0 zero_le
    refine ⟨(S.mono (fun _ hd ↦ Doomed.mono hd fun q ⟨hq, hR⟩ ↦
      ⟨treeOkG_treeOkAt sh.logN (stk q) x.h hq, hR⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun out ↦ (Spec.ret (Post := fun o hist ↦
        Doomed C (fun q ↦ o.Holds sh.M (stk q) ∧ R q) hist) (toS (sh.logN + 1) x.h out)).mono
      (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hh, hR⟩ ↦
        ⟨treeClaims_of_holds (by omega) hd.1 x.h (stk q) (hμ ▸ hh), hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩
  · simp only [treeProgS, if_neg hs]
    intro C R G _ _
    exact ⟨Spec.fail⟩

end Lvm6.K
