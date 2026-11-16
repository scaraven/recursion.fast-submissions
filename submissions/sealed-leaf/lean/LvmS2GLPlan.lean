-- New for lvm2 MB-LIN (MBL-LA, 2026-11-16): the plan's and Q_link's static stream facts at S2GL (`P20L`), one
-- decision (`LvmS2GUPlan`'s `planFacts_of` over S2GU's phase literals without the phase `tables`), and S2GU's `KS`
-- bridge (UTAPE-STMT 12-14) generic in the wire's first `cont` interval `[1, b]` (RE-FREEZE R1: S2GL is `b = 3,842`).
import LvmS2GUPlan
import LvmS2GUGood
import LvmS2GLSched

/-!
# The S2GL plan's facts and the `KS` bridge at any `b`

* **`phases_P20L_lit`**, **`schedule_P20L_lit`**: `phases P20L` is `phasesU20` without the phase `tables`
  (`LvmS2GUSchedLit`'s literals); **`P20L_eqL`**: `P20L` with its WHIR levels written out.
* **`passR_P20L`**: the one-pass decision at `P20L` (3,642 entries, `Σ clen = 268,328`, `Σ (40 + len) = 522,527`;
  the cap queries at entries 2, 997 and 2,416 [measured, a probe evaluation of the plan: S2GU's 1,004 and 2,423 less
  the seven FS queries of the phase `tables`]).
* **`planSt_P20L`**: `PlanOk P20L`; **`streamOk_P20L`**; **`qOkF_P20L`** (Q_link's static checks at S2GU's layout).
* **`spongeRel_of_GkB`**, **`traceDigest_of_GkB`** (any schedule `P` of `b + 1` sponge blocks with Q_link's stream
  facts), **`sigKSin_of_GkB`** (`b < ks_split`): S2GU's proofs (`spongeRel_of_GkU`, `traceDigest_of_GkU`,
  `sigKSin_of_GkU`) with `contU` replaced by `contB b`.
-/

set_option autoImplicit false

namespace Lvm

/-- **`phases P20L`**, phase by phase: S2GU's literals without the phase `tables`. -/
def phasesL20 : List (Phase × List Item) :=
  [(.commit, ph20U_commit), (.bus, ph20U_bus), (.tape, ph20U_tape), (.wire, ph20U_wire),
   (.openMain, ph20U_openMain)]

set_option maxRecDepth 100000 in
/-- **The phases at `P20L` are `phasesL20`** (by `rfl` after the stage dispatch). -/
theorem phases_P20L_lit : phases P20L = phasesL20 := by
  rw [phases_P20L]; rfl

/-- **`schedule P20L`** (`schedule_P20L_lit`): S2GU's phase literals without the phase `tables`, in order. -/
def schedL20 : List Item := ph20U_commit ++ ph20U_bus ++ ph20U_tape ++ ph20U_wire ++ ph20U_openMain

/-- **The schedule at `P20L` is `schedL20`.** -/
theorem schedule_P20L_lit : schedule P20L = schedL20 := by
  rw [schedule, phases_P20L_lit]
  simp only [phasesL20, schedL20, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- `P20L` with its WHIR levels written out (proof help: `P20L_eqL`). -/
def P20LL : Params := { P20L with mainLevels := P20UL.mainLevels }

/-- **`P20L` is `P20LL`** (`P20U_eqL`'s levels). -/
theorem P20L_eqL : P20L = P20LL := by
  have h : P20L.mainLevels = P20LL.mainLevels := by
    show P20U.mainLevels = P20UL.mainLevels
    rw [← P20U_eqL]
  show P20L = { P20L with mainLevels := P20LL.mainLevels }
  rw [← h]

end Lvm

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- The cap entries at `P20L` and their lengths (the FS queries that absorb the caps). -/
def tblL20 : List (ℕ × ℕ) := [(2, 8224), (997, 4176), (2416, 4176)]

set_option maxRecDepth 200000 in
/-- **The plan's facts at `P20L`** in one kernel evaluation (the walk over `schedL20` at `P20LL`). -/
private theorem planFactsL :
    passR (capLk tblL20) 3642 268328 522527 (plan P20L) tblL20 0 0 0 = true ∧
      (PlanOk P20L ∧ (planAll P20L).2.i = 3642) ∧ qOkF P20L (lay cfgU20) = true :=
  planFacts_of schedule_P20L_lit P20L_eqL sizes_P20L.1.2.2.1 (by decide +kernel)

/-- **The one decision at `P20L`.** -/
theorem passR_P20L : passR (capLk tblL20) 3642 268328 522527 (plan P20L) tblL20 0 0 0 = true :=
  planFactsL.1

/-- `PlanOk P20L` and the walk's last entry. -/
theorem planSt_P20L : PlanOk P20L ∧ (planAll P20L).2.i = 3642 :=
  planFactsL.2.1

/-- **Q_link's stream facts at `P20L`.** -/
theorem streamOk_P20L : StreamOk P20L := streamOk_ofR passR_P20L sizes_P20L.1.2.2.1

/-- Q_link's static checks at S2GL as `qOkF` (at S2GU's layout `lay cfgU20`; from `planFactsL`). -/
theorem qOkF_P20L : qOkF P20L (lay cfgU20) = true :=
  planFactsL.2.2

end Lvm.E2Q

namespace Lvm.E2U

open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **The sponge half is a sponge table** for any first `cont` interval `[1, b]` (`spongeRel_of_GkU`'s proof). -/
theorem spongeRel_of_GkB {b : ℕ} {x : List UInt8} {p : Column CMain.nu20 × Column 19} (hG : GkB b x p) :
    SpongeRel 13 (ksVirt 13 (YqU p.1) (MqU p.1) (contB b)) (YqU p.1) (MqU p.1) (contB b) where
  out i hi l hl := by
    rw [YqU, hG.2 i hi l hl, tapeInB, tapeIn, if_neg (by (clear * -; omega)), if_pos (by (clear * - hi; omega)),
      Nat.add_sub_cancel_left]
  link i hi l hl := by
    rw [ksVirt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 13), Nat.div_eq_of_lt hi, zero_add]
  cont0 := by simp [contB, contIvB]

/-- The trace rows `1 … b` continue a sponge. -/
theorem contB_of {b i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ b) : contB b i = true := by
  simp only [contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl ⟨h1, h2⟩

/-- **The sponge half outputs the child's trace digest** at row `B − 1` for a schedule `P` of `B = b + 1` sponge
blocks with Q_link's stream facts (`traceDigest_of_GkU`'s proof, generic in the schedule). -/
theorem traceDigest_of_GkB {P : Params} {b : ℕ} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hst : StreamOk P) (hb : spongeBlocks P = b + 1) (hsb : spongeBlocks P = Lvm.KSponge.nBlk (hashedLen P))
    (hB : spongeBlocks P ≤ 7680)
    (hG : GkB b x (qm, qr)) (hS : SBlkU qm qr) (hL : LaneLink P (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P)) :
    Lvm.KSponge.stDigest (yState (YqU qm) (spongeBlocks P - 1)) =
      traceDigest (decode P (wsOf (Lvm.X.laneOf (wOfCol qr)))) := by
  have H := spongeRel_of_GkB hG
  have hS' := stream_of_laneLink hst hL
  have hsz : hashedLen P ≤ (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).length := by
    rw [wordsBytes_length]; exact hL.size
  have hin : ∀ i, 0 < i → i < Lvm.KSponge.nBlk (hashedLen P) → contB b i = true :=
    fun i h1 h2 => contB_of h1 (by rw [← hsb, hb] at h2; omega)
  rw [hsb] at hB ⊢
  obtain ⟨L, hL⟩ : ∃ L, hashedLen P = L := ⟨_, rfl⟩
  rw [hL] at hS' hsz hpad hB hin ⊢
  have hnbL : Lvm.KSponge.nBlk L = L / 136 + 1 := rfl
  refine traceDigest_of_KS 13 _ (YqU qm) (MqU qm) _ H L (le_trans hB (by norm_num)) hin ?_ _ ?_
  · intro p h1 h2
    have h2' : p < 136 * Lvm.KSponge.nBlk L := h2
    have := msgBytes_eq_streamU hS (p := p) (by show p / 136 < 2 ^ 14; omega)
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, this, ← padAt_eq]
    exact hpad p h1 (by rw [nBlk_eq]; omega)
  · rw [← hS']
    refine List.ext_getElem (by rw [Lvm.KSponge.streamOf_length, List.length_take]; omega) fun p h1 h2 => ?_
    have hp : p < L := by rw [Lvm.KSponge.streamOf_length] at h1; exact h1
    simp only [Lvm.KSponge.streamOf, List.getElem_ofFn, List.getElem_take]
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl,
      msgBytes_eq_streamU hS (by show p / 136 < 2 ^ 14; omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **Q_sig's `KS` hypothesis** for any first `cont` interval `[1, b]` below the split (`sigKSin_of_GkU`'s proof). -/
theorem sigKSin_of_GkB {b : ℕ} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} {I : SigIn}
    {v : ℕ → FK} (hb : b < 7680)
    (hG : GkB b x (qm, qr))
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 430 + t) l))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 447) l))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 448) l)) :
    SigKSin I v := by
  have H := spongeRel_of_GkB hG
  have hrow : ∀ r < 449, ksSplit P20 + r < 2 ^ 13 := fun r hr => by rw [ksSplit_P20]; omega
  have hcF : ∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) →
      contB b (ksSplit P20 + r) = false := fun r h1 h2 => by
    simp only [contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff,
      decide_eq_false_iff_not, ksSplit_P20]; omega
  have hcT : ∀ r, 400 ≤ r → r ≤ 430 → contB b (ksSplit P20 + r) = true := fun r h1 h2 => by
    simp only [contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq,
      ksSplit_P20]; omega
  -- a one-block row
  have one : ∀ r < 449, ¬ (400 ≤ r ∧ r ≤ 430) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l)) →
      OneHash v (fun l => I.xs + 17 * r + l) y := fun r hr hn y hy =>
    ⟨yState (YqU qm) (ksSplit P20 + r), by
      rw [xorMsg_cellsU (qm := qm) (r := r) (fun l hl => hx r hr l hl)]
      exact oneRow_perm 13 _ (YqU qm) (MqU qm) _ H (hrow r hr) (hcF r hr hn),
      digAt_of_cells hy⟩
  refine ⟨fun r hr => one r (by (clear * - hr; omega)) (by (clear * - hr; omega)) _ (hys r hr), ?_, fun t ht => ?_,
    one 447 (by (clear * -; omega)) (by (clear * -; omega)) _ hyls,
    one 448 (by (clear * -; omega)) (by (clear * -; omega)) _ hyns⟩
  · -- the key leaf: rows `S + 399 … S + 430`
    refine ⟨fun u => prevState (YqU qm) (contB b) (ksSplit P20 + (399 + u)),
      fun u => yState (YqU qm) (ksSplit P20 + (399 + u)), ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · simp only [prevState, Nat.add_zero, hcF 399 (by (clear * -; omega)) (by (clear * -; omega))]; rfl
    · rw [xorMsg_cellsU (qm := qm) (r := 399 + u) (fun l hl => hx _ (by (clear * - hu; omega)) l hl)]
      exact row_perm 13 _ (YqU qm) (MqU qm) _ H (hrow _ (by (clear * - hu; omega)))
    · simp only [prevState, hcT (399 + (u + 1)) (by (clear * - hu; omega)) (by (clear * - hu; omega)), if_true]
      congr 1
    · refine digAt_of_cells fun l hl => ?_
      have := hyc 0 (by (clear * -; omega)) l hl
      simpa using this
  · -- path node `t`: row `S + 431 + t`
    refine one (431 + t) (by (clear * - ht; omega)) (by (clear * - ht; omega)) _ fun l hl => ?_
    have := hyc (t + 1) (by (clear * - ht; omega)) l hl
    rw [show ksSplit P20 + 430 + (t + 1) = ksSplit P20 + (431 + t) by (clear * -; omega)] at this
    exact this

end Lvm.E2U
