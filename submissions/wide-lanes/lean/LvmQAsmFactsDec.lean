-- New for lvm (WP-16a2, FIN-TF): every kernel decision of the table-level static facts that reads the
-- placement record `data20` or `P20`'s numbers (re-run after each re-freeze).
-- adapted from rf-lvm-QFX/submissions/leanvm-inspired/lean/LvmQAsmFactsSk.lean (uncommitted, WP-16a-QFX).
import LvmQAsmFactsSk

/-!
# The record's decisions

All on the tables' skeletons or on `P20`'s numbers; none evaluates Q_arith (the tables read the
cache `M3.G20` only inside fixed columns' closures, which no check forces).

* (lvm2 roll 8, wave L: the bus tables' decision `chkFit_P20` and its parts `chkB_P20`, `fitsR_P20`,
  `shpOk_P20` are deleted, dead on the typed path. Kept: `ShpOk`, the aux tables' placement check `auxOffB`
  with `layOkB_aux`, `colsFitB_aux`, and the splits `chkB_eq`, `fitsR_eq`, `tabsP20_GA`.)
* `posCellsB_P20`: the position classes' output cells below `nK cfg20`, through each opening's
  region ends and the lane classes' spare end (`posCellsB`, `posCell_lt`; WP-16b: 12.5 s → < 1 s of kernel;
  EV-DIET B: 2.3 s, of which ≈ 1.5 s evaluate `opens P20`);
* `hashedLen_nK20`: the hashed stream below `nK cfg20` (≈ 1 s);
* `inOkB_P20`: the input arrays tile the input cells, at `default` (< 1 s).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.M3

/-- **HAR's table phase facts on the sumcheck tables' shapes `S`** (`HarStatic`'s `htT`, `hpubT`,
`hpubτ`, `hRmax`, `hnf`, `hzL`, `hP4` with `accZ0` written out): the phase ends inside the stream's `T`
lanes, `PUB` is a sumcheck table of height `2^10`, the tallest table has `τ ≥ tableRounds`, the fixed
columns fit `2^accLog`, and phase 3b's zero scalar lies inside the stream, 24 bytes before `P4`. -/
def ShpOk (p : Params) (S : List Har.TShape) (T P4 : ℕ) : Prop :=
  Har.tabEnd S p.tableRounds (Har.tabPos p) + 40 ≤ 8 * T ∧ p.pubTab < S.length ∧
  (S.map (·.τ)).getD p.pubTab 0 = 10 ∧ (∃ s ∈ S, p.tableRounds ≤ s.τ) ∧
  (Har.fixIdx S p.pubTab).length ≤ 2 ^ p.accLog ∧
  Har.tabEnd S p.tableRounds (Har.tabPos p) / 8 + 9 * p.accLog + 3 * (accVars + 1) + 9 + 5 + 2 < T ∧
  8 * (Har.tabEnd S p.tableRounds (Har.tabPos p) / 8 + 9 * p.accLog + 3 * (accVars + 1) + 9) + 24 = P4

section Aux
open Lvm.SigBits Lvm.BitsTab

/-! ## The aux tables' placements, one pass per class -/

/-- A `C_main` column of `2^τ` rows at `off`: aligned, inside `2^nu` words. -/
def offOk (τ nu off : ℕ) : Bool := off % 2 ^ τ == 0 && decide (off + 2 ^ τ ≤ 2 ^ nu)

/-- **The aux tables' committed columns**: class `k`'s placements (and the default `0`) aligned
inside `C_main`, one pass over each placement list. -/
def auxOffB (nu : ℕ) (C : QCfg) (D : QData) : Bool :=
  (bspecs C D).zipIdx.all fun x => offOk x.1.τ nu 0 && (D.bpl.getD x.2 []).all (offOk x.1.τ nu)

theorem posSpecs_length (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ) : (posSpecs C bpl).length = nPosCls C := by
  simp [posSpecs]

theorem posSpecs_pl (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ) (i : ℕ) (h : i < (posSpecs C bpl).length) :
    ((posSpecs C bpl)[i]).pl = bpl i := by
  simp only [posSpecs, List.getElem_map, List.getElem_range, posSpec_pl]

attribute [local irreducible] Lvm.schedule in
theorem bspecs_pl (C : QCfg) (D : QData) (i : ℕ) (h : i < (bspecs C D).length) :
    ((bspecs C D)[i]).pl = bplOf D i := by
  have hs : (sigSpecs (sigIn C) (sigOut C) (bplOf D)).length = 6 := rfl
  unfold bspecs at h ⊢
  rw [List.getElem_append]
  split
  · rename_i h1
    rw [List.getElem_append]
    split
    · rename_i h2
      rw [hs] at h2
      interval_cases i <;> rfl
    · rename_i h2
      rw [posSpecs_pl, hs]
      congr 1
      rw [hs] at h2
      omega
  · rename_i h1
    simp only [List.length_append, hs, posSpecs_length] at h1 h
    simp only [List.length_cons, List.length_nil] at h
    obtain ⟨k, rfl⟩ : ∃ k, i = 6 + nPosCls C + k := ⟨i - (6 + nPosCls C), by omega⟩
    have hk : k < 2 := by omega
    simp only [List.length_append, hs, posSpecs_length, Nat.add_sub_cancel_left]
    interval_cases k
    · show bplOf D (6 + nPosCls C) = bplOf D (6 + nPosCls C + 0)
      rfl
    · show bplOf D (7 + nPosCls C) = bplOf D (6 + nPosCls C + 1)
      congr 1; omega

theorem getD_mem_or {α : Type} (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · left; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · right; exact List.getD_eq_default _ _ hi

/-- Every committed column of a `BITS` table placed by `bplOf D k` is in `C_main`, at one of the
class's placements or `0`. -/
theorem bspec_com {S : BSpec} {D : QData} {k : ℕ} (hpl : S.pl = bplOf D k) {c : ColSrc}
    (hc : c ∈ S.tab.cols) {rec : Bool} {off : ℕ} (he : c = .com rec off) :
    rec = false ∧ (off ∈ D.bpl.getD k [] ∨ off = 0) := by
  simp only [BSpec.tab, List.mem_map, List.mem_range] at hc
  obtain ⟨j, -, rfl⟩ := hc
  unfold BSpec.col at he
  split at he
  · cases he
  · split at he
    · rw [hpl] at he
      simp only [bplOf, ColSrc.com.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, getD_mem_or _ _ _⟩
    · split at he <;> cases he

theorem aux_com {nu : ℕ} {C : QCfg} {D : QData} (h : auxOffB nu C D = true) :
    ∀ t ∈ aux C D, ∀ c ∈ t.cols, ∀ (rec : Bool) (off : ℕ), c = .com rec off →
      rec = false ∧ offOk t.τ nu off = true := by
  intro t ht c hc rec off he
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hS
  have hz : ((bspecs C D)[i], i) ∈ (bspecs C D).zipIdx := by
    have hi' : i < ((bspecs C D).zipIdx).length := by simpa using hi
    have := List.getElem_mem hi'
    rwa [List.getElem_zipIdx, Nat.zero_add] at this
  have hx := List.all_eq_true.mp h _ hz
  simp only [Bool.and_eq_true, List.all_eq_true] at hx
  obtain ⟨hr, ho⟩ := bspec_com (bspecs_pl C D i hi) hc he
  refine ⟨hr, ?_⟩
  rcases ho with ho | rfl
  · exact hx.2 off ho
  · exact hx.1

theorem layOkB_aux {L : Lay} {C : QCfg} {D : QData} (h : auxOffB L.nuMain C D = true)
    (hL : L.nuRec ≤ L.nuMain) : layOkB L (aux C D) = true := by
  unfold layOkB
  rw [List.all_eq_true]
  intro t ht
  rw [List.all_eq_true]
  intro c hc
  cases c with
  | fix _ _ => rfl
  | com rec off =>
    obtain ⟨rfl, hok⟩ := aux_com h t ht _ hc rec off rfl
    simp only [offOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [colOkB, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, ite_false]
    exact ⟨hok, hL⟩

theorem colsFitB_aux {p : Params} {C : QCfg} {D : QData} (h : auxOffB p.nuMain C D = true)
    (hp : p.nuRec ≤ p.nuMain) : colsFitB p (aux C D) = true := by
  unfold colsFitB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hp, fun t ht c hc => ?_⟩
  cases c with
  | fix _ _ => rfl
  | com rec off =>
    obtain ⟨rfl, hok⟩ := aux_com h t ht _ hc rec off rfl
    simpa [offOk] using hok

/-! ## `chkB`, `fitsR` without the placements -/

/-- `chkB` without the layout check. -/
def chkB0 (ts : List Tab) : Bool :=
  ts.all (fun t => t.reads.all fun r => decide (r.2 < t.w)) &&
  decide (nReads ts < 2 ^ 64 - 1) &&
  ts.all (fun t => (t.reads.all fun r => decide (r.1.val.length ≤ 13)) &&
    t.seeds.all fun s => decide (s.1.val.length ≤ 13)) &&
  ts.all (fun t => decide (0 < t.w)) &&
  decide ((ts.map fun t => t.cons.length).sum ≤ 2 ^ 48) &&
  ts.all (fun t => !t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty)

theorem chkB_eq (L : Lay) (ts : List Tab) : chkB L ts = (chkB0 ts && layOkB L ts) := by
  unfold chkB chkB0
  cases layOkB L ts <;> simp only [Bool.and_true, Bool.and_false, Bool.false_and]

/-- `fitsR` without the committed columns' alignment. -/
def fitsR0 (p : Params) (tabs : List Tab) : Bool :=
  let st := sumcheckTabs tabs
  p.leafdecReads == 1 && p.busDepth == log2Ceil (pushLeavesR tabs) && decide (1 ≤ p.busDepth) &&
    decide (p.busDepth ≤ 22) && p.tableRounds == (st.map (·.τ)).foldl max 0 &&
    p.tableEvals == (st.map (·.w)).sum && tabs.all (fun t => decide (t.τ ≤ p.nuMain + 1)) &&
    tabs.all (fun t => t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty) &&
    decide (p.tableRounds ≤ accVars) && decide ((fixColsR st p.pubTab).length ≤ 2 ^ p.accLog) &&
    decide (p.pubTab < st.length) && decide (pubLanes ≤ 2 ^ ((st.map (·.τ)).getD p.pubTab 0)) &&
    (st.map col0Fix).getD p.pubTab false

theorem fitsR_eq (p : Params) (ts : List Tab) : fitsR p ts = (fitsR0 p ts && colsFitB p ts) := by
  unfold fitsR fitsR0
  cases colsFitB p ts <;> simp only [Bool.and_true, Bool.and_false, Bool.false_and]

theorem layOkB_append (L : Lay) (a b : List Tab) : layOkB L (a ++ b) = (layOkB L a && layOkB L b) := by
  simp [layOkB, List.all_append]

theorem colsFitB_append (p : Params) (a b : List Tab) :
    colsFitB p (a ++ b) = (colsFitB p a && colsFitB p b) := by
  unfold colsFitB
  rw [List.all_append]
  cases decide (p.nuRec ≤ p.nuMain) <;> simp

/-- The group and array tables (`M3.tabsP20 P` without the aux tables). -/
def tabsGA (P : Pub) : List Tab := lvmTabsC M3.G20 (plOf data20) data20.groups (arrs cfg20 data20 P) []

theorem tabsP20_GA (P : Pub) : M3.tabsP20 P = tabsGA P ++ aux cfg20 data20 := by
  simp [M3.tabsP20, tabs, tabsGA, lvmTabsC]

end Aux

/-! ## The position classes' cells through their regions' ends

`posCellsB` (`LvmQAsmFactsSk`) checks per opening that its bit region, its spare cells and its fields end
below `N`, and that the lane classes' spare cells do (`posCell_lt`: every output cell lies in one of
them; WP-16b: 12.5 s → < 1 s of kernel; with the lane classes' spare end 2.3 s). -/

set_option maxRecDepth 200000 in
/-- The position classes' output cells are input cells (decided per opening and lane class, `posCellsB`). -/
theorem posCellsB_P20 : posCellsB cfg20 (nK cfg20) = true := by
  show posCellsB ⟨P20, 14, 20, 11, 8, 18, 10, 13, 15⟩ (nK cfg20) = true
  rw [P20_eq]
  decide +kernel

set_option maxRecDepth 200000 in
/-- The hashed stream's lanes are input cells. -/
theorem hashedLen_nK20 : hashedLen cfg20.p / 8 + 5 ≤ nK cfg20 := by
  rw [show cfg20.p = P20 from rfl, P20_eq]
  decide +kernel

set_option maxRecDepth 200000 in
/-- The input arrays tile the input cells (at `default`; `InOk` reads no public value). -/
theorem inOkB_P20 : inOkB Q20n (arrs cfg20 data20 default) = true := by decide +kernel

end Lvm.QAsm
