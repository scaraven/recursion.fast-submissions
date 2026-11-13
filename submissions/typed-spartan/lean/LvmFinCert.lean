-- New for lvm (WP-16a2, FIN-DEC): roll 7's final assembly of the bus program (BLUEPRINT A24, WP-16a2 §3). Lvm2 roll 8
-- (B1, wave L): the bus certificate is gone (the typed one is `LvmCertT20`); what is left are a few bus-program
-- facts (`shapes20`, `rest20`, `hnk20`), the small layout's generic `colsRegB` lemmas and the guard's generic
-- lemmas. Outside `certified`'s import closure.
import LvmFinDec
import LvmQAsmFactsNode
import LvmFinHB
import LvmFinGuard
import LvmCertSFinal20
import LvmVFast

/-!
# The certificate

* **`colsRegB_aux`**: the aux tables' regularity from `auxRegB` (generic); `certificateR_guard`, `subG_F`: the
  bus `V_S`'s guard lemmas.
* (lvm2 roll 8, B1, wave L: roll 7's `harStatic20`, `nodeBase20`, `colsRegGA_P20`, `auxReg_P20`, `colsReg20`,
  `bv20`, `hinbL20`, `openFin` and `certificateFin`, the bus certificate of `subG staticOkB VF.VS20F`, are gone: the schedule is the
  typed one, so the bus `P_S` no longer follows it and `refines_VSL` is gone; the typed certificate is
  `LvmCertT20.certificateT20`.)
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits
open Lvm.NS Lvm.VEq Lvm.ASM Lvm.QAsm
open scoped NNReal

/-! ## HAR's static facts at `P20` -/

/-- The table phase's shapes are those of the sumcheck tables at `default`. -/
theorem shapes20 : Har.shapesOf cfg20 data20 = (sumcheckTabs (M3.tabsP20 default)).map Tab.shape :=
  Har.shapesOf_eq cfg20 data20 M3.G20 default

/-! ## `NodeBase` of the `P20` node program -/

/-- The aux tables after Q_sig's six `BITS` tables (`haux20`): the position classes, the `s'` shifts. -/
abbrev rest20 : List Tab :=
  ((posSpecs cfg20 fun c => bplOf data20 (6 + c)) ++ [sSpec cfg20 (bplOf data20 (6 + nPosCls cfg20)),
    powSpec cfg20 (bplOf data20 (7 + nPosCls cfg20))]).map
    BitsTab.BSpec.tab

theorem hnk20 : hashedLen P20 / 8 + 5 ≤ nK cfg20 := by
  have h := hashedLen_nK20; rw [show cfg20.p = P20 from rfl] at h; exact h

/-! ## Roll 7: the small layout's fit at `P20` (`colsRegB`)

One decision at `default` (skeleton invariance, as `fitsR`'s `fit20_of`): the group and array tables
directly, the aux tables on their placement lists (`auxRegB`, one pass per class, as `auxOffB`). -/

section Reg

open Lvm.SigBits Lvm.BitsTab

theorem colsRegB_sk (ts : List Tab) : colsRegB (ts.map tabSk) = colsRegB ts := by
  unfold colsRegB
  rw [List.all_map]
  refine List.all_congr rfl fun t => ?_
  simp only [Function.comp_apply, tabSk, List.all_map]
  exact List.all_congr rfl fun c => by cases c <;> rfl

theorem colsRegB_append (a b : List Tab) : colsRegB (a ++ b) = (colsRegB a && colsRegB b) := by
  unfold colsRegB
  rw [List.all_append]

/-- **The aux tables' committed columns are regular**: class `k`'s placement list covers its committed
columns (none falls back to `bplOf`'s default `0`), and each placement is a regular block of the class's
height (`RegP`, written with `Nat.ble`/`Nat.blt` for the kernel). -/
def auxRegB (C : QCfg) (D : QData) : Bool :=
  (bspecs C D).zipIdx.all fun x =>
    Nat.ble x.1.ab ((D.bpl.getD x.2 []).length + 1) && Nat.ble x.1.τ 20 &&
    (D.bpl.getD x.2 []).all fun off =>
      off % 2 ^ x.1.τ == 0 && Nat.ble (4 * 2 ^ 20) off && Nat.blt off (7 * 2 ^ 20)

/-- A committed column of a `BITS` table placed by `bplOf D k`, with the class's list long enough, is in
`C_main` at one of the class's placements. -/
theorem bspec_com_mem {S : BSpec} {D : QData} {k : ℕ} (hpl : S.pl = bplOf D k)
    (hab : S.ab ≤ (D.bpl.getD k []).length + 1) {c : ColSrc} (hc : c ∈ S.tab.cols) {rec : Bool} {off : ℕ}
    (he : c = .com rec off) : rec = false ∧ off ∈ D.bpl.getD k [] := by
  simp only [BSpec.tab, List.mem_map, List.mem_range] at hc
  obtain ⟨j, -, rfl⟩ := hc
  unfold BSpec.col at he
  split at he
  · cases he
  · rename_i h66
    split at he
    · rename_i hj
      rw [hpl] at he
      simp only [bplOf, ColSrc.com.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨rfl, ?_⟩
      have hab' : 67 ≤ S.ab := by unfold BSpec.ab; omega
      have hi : (if j ≤ 65 then j else j - 1) < (D.bpl.getD k []).length := by split <;> omega
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem _
    · split at he <;> cases he

theorem colsRegB_aux {C : QCfg} {D : QData} (h : auxRegB C D = true) : colsRegB (aux C D) = true := by
  unfold colsRegB
  rw [List.all_eq_true]
  intro t ht
  rw [List.all_eq_true]
  intro c hc
  cases c with
  | fix _ _ => rfl
  | com rec off =>
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hS
    have hz : ((bspecs C D)[i], i) ∈ (bspecs C D).zipIdx := by
      have hi' : i < ((bspecs C D).zipIdx).length := by simpa using hi
      have := List.getElem_mem hi'
      rwa [List.getElem_zipIdx, Nat.zero_add] at this
    have hx := List.all_eq_true.mp h _ hz
    simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hx
    obtain ⟨⟨hab, hτ⟩, ho⟩ := hx
    obtain ⟨rfl, hm⟩ := bspec_com_mem (bspecs_pl C D i hi) hab hc rfl
    obtain ⟨⟨h1, h2⟩, h3⟩ := ho off hm
    simp only [Bool.false_or, decide_eq_true_eq]
    exact ⟨hτ, h1, h2, h3⟩

end Reg

/-! ## The certificate -/

theorem subG_true : subG true Lvm.VS20 = Lvm.T.submission := rfl

/-- **The certificate of the guarded submission** from the open obligations under `b = true`. -/
theorem certificateR_guard {b : Bool} (h : b = true → Lvm.T.Open) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subG b Lvm.VS20) :=
  certificateR_guardT Lvm.M3.tabsP20 h

/-- The compiled guarded submission (`VS20F`, V-PERF) is the specified one. -/
theorem subG_F (b : Bool) : subG b Lvm.VF.VS20F = subG b Lvm.VS20 := by rw [Lvm.VF.VS20F_eq]

end Lvm.Fin
