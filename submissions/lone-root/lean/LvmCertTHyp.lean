-- New for lvm2 (roll 8 = B1, wave L, L-W): `THyp` of the typed instance at `P20` (`LvmCertT20.thyp20`): the
-- region maps' fit (`NT20.okB`), `acc_in`'s 43 coordinates, the word `1`'s region (the guard's `oneOkB`), the
-- mini-bus's table facts (by the shape of `mbT`, and `fitsMiniB` from the guard) and the error terms at the mini-bus
-- instance (B-DES §1.7; M′ `S2GM`: `μBus = 12`, no constraints, `L₀ = 37,696`). No kernel decision on `QB20`/`layT20`/`mbT20`.
import LvmCertTInst

/-!
# `THyp` at `P20`, glue

* **`mapsFit_inst`**: `(N.inst Q lay).MapsFit ⟨23, 19⟩` from `N.layOk lay` and `N.okB 23 19` (any instance; M′:
  `σ′`'s word is `off` modulo `2^19`, `TNat.inst`).
* **`src_one_of`**: `(N.inst Q lay).src? lay.one = some .one` from the guard's `oneOkB lay`.
* **`accLen`**: every statement's `acc_in` has `phiVars = 43` coordinates (`accVars = 43`).
* **The mini-bus's tables** `mbT C wk fin cnt` (any placement): `tabsOkB` (`AllSc`, widths, `KeysOk`), `FixOk`, a
  `C_main` column per table, no constraints; with `fitsMiniB`: heights `≤ 22`, `LayOk`, `μBus = busDepth`, the widths'
  sum `= tableEvals`.
* **`errs_at`**: `TErrs 37696 I εS LkSJ` for any instance with `μBus = 12` and `B = 0` (M′ `S2GM`; B1: 13).
-/

set_option autoImplicit false

namespace Lvm.CT

open Lvm Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.M3 Lvm.QAsm
open Lvm.VEq (pubX)
open scoped ENNReal NNReal

/-- `P20`'s record: `ν = (23, 19)`, the mini-bus's depth and evaluations. -/
theorem p20_facts : P20.nuMain = 23 ∧ P20.nuRec = 19 ∧ P20.busDepth = 12 ∧ P20.tableEvals = 633 := by
  decide +kernel

/-! ## The word space -/

/-- The region maps of `N.inst Q lay` land in a `ν = (23, 19)` commitment pair when `N` passes its shape check. -/
theorem mapsFit_inst (N : TNat) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (hl : N.layOk lay = true)
    (hok : N.okB 23 19 = true) : (N.inst Q lay).MapsFit lay26 := by
  intro y
  rw [src?_inst N Q lay hl y]
  cases hr : N.regAt y with
  | none => trivial
  | some r =>
    have hmem : r ∈ N.regs := List.mem_of_find?_eq_some hr
    have hp := List.find?_some hr
    simp only [decide_eq_true_eq] at hp
    have hoff : N.off y = r.dst + (y - r.base) := by simp [TNat.off, hr]
    unfold TNat.okB at hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    have hr' := hok.1.1.1.1.1 r hmem
    simp only [beq_iff_eq, decide_eq_true_eq] at hr'
    obtain ⟨-, hsrc⟩ := hr'
    simp only [Option.map_some]
    cases hs : r.src <;> simp only [hs] at hsrc <;>
      simp only [TNat.inst, hoff, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true, posBits] at hsrc ⊢
    all_goals first
      | trivial
      | exact Nat.mod_lt _ (Nat.two_pow_pos 19)
      | (simp only [lay26]; omega)
      | omega
      | (have h1 : r.dst + (y - r.base) < 2 ^ 19 := by omega
         unfold sflatWord
         split <;> simp only [sPos, sLanes, recRowBits, recStreamCols] at * <;> omega)

/-- `acc_in` has `phiVars = 43` coordinates on every statement (`pubOf` reads `accVars = 43`). -/
theorem accLen : ∀ x, (pubX x).accIn.pt.length = phiVars := by
  intro x
  simp only [pubX, pubOf, List.length_map, List.length_range]
  rfl

/-- **The word `1` lies in a `1` region** when the guard's `oneOkB` holds. -/
theorem src_one_of (N : TNat) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (h : Lvm.T.oneOkB lay = true) :
    (N.inst Q lay).src? lay.one = some .one := by
  simpa [Lvm.T.oneOkB, TInst.src?, TNat.inst] using h

/-! ## The mini-bus's tables -/

/-- The mini-bus's tables pass `tabsOkB` (every table reads or seeds, widths, key sizes), by their shape. -/
theorem tabsOkB_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) :
    tabsOkB (mbT C wk fin cnt) = true := by
  simp [tabsOkB, mbT, mbArrs, capReads, readTab, InArr.tab, InArr.vcols, readKey, List.all_append,
    List.all_map, Tab.w]

/-- A seed array's fixed column is its address column's closed form (`inArr_eval_eq`). -/
theorem fixOk_arrT {C : QCfg} {fin : ℕ → Bool × ℕ} (a : InArr) (ha : a ∈ mbArrs C fin) {f : ℕ → FK}
    {ev : List FE → FE} (hfe : ColSrc.fix f ev ∈ a.tab.cols) (r : List FE) (hr : r.length = a.tab.τ) :
    ev r = Loop.mle r fun x ↦ FE.ofK (f x) := by
  have hpub : a.pub = none := by
    unfold mbArrs at ha
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; rfl
  simp only [InArr.tab, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hfe
  rcases hfe with hv | hv | hv
  · unfold InArr.vcols at hv
    rw [hpub] at hv
    obtain ⟨_, -, hv⟩ := List.mem_map.mp hv
    cases hv
  · cases hv
  · simp only [ColSrc.fix.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact inArr_eval_eq a r

/-- **`FixOk`** of the mini-bus's tables: the seed arrays' address columns; the read tables have none. -/
theorem fixOk_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) :
    FixOk (mbT C wk fin cnt) := by
  intro t ht f ev hfe r hr
  unfold mbT at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact fixOk_arrT a ha hfe r hr
  · unfold capReads at ht
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht
    simp [readTab] at hfe

/-- Every table of `mbT` has a `C_main` column (the read tables' columns, the seed arrays' finalize column). -/
theorem com_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) (hfin : ∀ k, (fin k).1 = false) :
    ∀ t ∈ mbT C wk fin cnt, ∃ off, ColSrc.com false off ∈ t.cols := by
  intro t ht
  unfold mbT at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    unfold mbArrs at ha
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha
    exact ⟨(fin y.2).2, by simp [InArr.tab, ← hfin y.2]⟩
  · unfold capReads at ht
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht
    exact ⟨wk (adrCell (qlinkProg C) x.1.1 x.1.2 0), by simp [readTab]⟩

/-- A table with a `C_main` column off `D` (`colsHiB`) is at most `2^22` high. -/
theorem hτ_of_hi {tabs : List Tab} (hc : ∀ t ∈ tabs, ∃ off, ColSrc.com false off ∈ t.cols)
    (h : colsHiB tabs = true) : ∀ t ∈ tabs, t.τ ≤ (⟨23, 19⟩ : M3.Lay).μ := by
  intro t ht
  obtain ⟨off, hoff⟩ := hc t ht
  simp only [colsHiB, List.all_eq_true] at h
  have := h t ht _ hoff
  simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [Lay.μ]; omega

/-- **`LayOk`** from `colsFitB` at `ν = (23, 19)` (`Fit.layOk`'s proof). -/
theorem layOk_of_fit {p : Params} {tabs : List Tab} (hp : p.nuMain = 23 ∧ p.nuRec = 19)
    (h : colsFitB p tabs = true) : LayOk ⟨23, 19⟩ tabs := by
  apply layOk_of_B
  simp only [colsFitB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  simp only [layOkB, List.all_eq_true]
  intro t ht c hc
  have := h.2 t ht c hc
  cases c with
  | com rec off =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    simp only [colOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← hp.1, ← hp.2]
    exact ⟨⟨this.1, this.2⟩, h.1⟩
  | fix f ev => rfl

/-- Tables that all read or seed are all sumcheck tables. -/
theorem sc_all (tabs : List Tab) (h : AllSc tabs) : sumcheckTabs tabs = tabs := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases h t ht with h1 | h1 <;> simp [h1]

/-- The mini-bus's tables have no constraints (so the batching count `B` is `0`). -/
theorem cons_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) :
    ((mbT C wk fin cnt).map fun t ↦ t.cons.length).sum = 0 := by
  refine List.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
  unfold mbT at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht; rfl
  · unfold capReads at ht
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht; rfl

open LeanVM.Protocol.KeccakGkr (errE errE_mono) in
open LeanVM.Protocol.EndToEnd.Front in
open Lvm.ASM in
/-- **The typed phases' error terms** (`TErrs`) at `L₀ = 37,696` against `εS` with follower `LkSJ`, for an instance
of depth `12` (M′ `S2GM`; B1: 13) without constraints: every term is `errE d` with `d ≤ 2^63` (`errE_le_εS`). -/
theorem errs_at (I : LeanVM.Protocol.M3Instance) (hμ : I.μBus = 12) (hB : I.B = 0) :
    TErrs 37696 I εS LkSJ := by
  have hab : abError I 37696 = errE (37696 * (4 * 2 ^ 12)) := by
    rw [abError, coe_overE, errE_smul, hμ]
  have hr : ∀ d, roundError 37696 d = errE (37696 * d) := fun d ↦ by
    rw [roundError, coe_div_card, errE_smul]
  have hl : lambdaError 37696 = errE (37696 * 2) := by
    rw [lambdaError, coe_div_card, errE_smul]
  have hu : unitError 37696 = errE (37696 * 1) := by
    rw [← errE_smul]; simp [unitError, errE]
  have hx : xiError I 37696 = errE (37696 * (I.B + 3 - 1)) := by
    rw [xiError, coe_div_card, errE_smul]
  have hlead : leadT 37696 = errE (20 * (37696 * 1)) := by
    simp only [leadT, add_zero, errE_smul, Lvm.Typed.xVars]
  have h2 : (2 : ℝ≥0∞) * errE 1 = errE (2 * 1) := by rw [← errE_smul]; norm_num
  have hM : leadMaxT 37696 I LkSJ ≤ errE (37696 * (4 * 2 ^ 12)) := by
    unfold leadMaxT
    rw [hlead, hab, add_zero, h2, LkSJ_eq]
    exact max_le (errE_mono (by norm_num)) (max_le le_rfl (max_le (errE_mono (by norm_num))
      (errE_mono (by norm_num))))
  have fin : ∀ a : ℕ, a ≤ 2 ^ 62 → errE a + leadMaxT 37696 I LkSJ ≤ εS := by
    intro a ha
    calc errE a + leadMaxT 37696 I LkSJ ≤ errE a + errE (37696 * (4 * 2 ^ 12)) := by gcongr
      _ = errE (a + 37696 * (4 * 2 ^ 12)) := errE_add _ _
      _ ≤ εS := errE_le_εS (Nat.le_trans (Nat.add_le_add_right ha _) (by norm_num))
  refine ⟨?_, fun d hd ↦ ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hlead]; exact errE_le_εS (by norm_num)
  · rw [hr]; exact fin _ (by omega)
  · exact fin _ (by norm_num [Lvm.Typed.phiVars, Lvm.Typed.xVars, Lvm.Typed.yVars])
  · rw [hab]; exact lt_of_le_of_lt (errE_le_εS (by norm_num)) εS_lt_one
  · rw [hab]; exact fin _ (by norm_num)
  · rw [interpLead_eq, hu, hl, errE_smul, errE_add]; exact fin _ (by norm_num)
  · rw [hl]; exact fin _ (by norm_num)
  · rw [hx, hB]; exact fin _ (by norm_num)
  · exact hM.trans (errE_le_εS (by norm_num))

end Lvm.CT
