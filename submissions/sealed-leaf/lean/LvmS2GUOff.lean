/- `LvmS2GUOff` (SLF-K off-path move, group 1 of 1): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmS2GUSched, LvmS2GUFront, LvmS2GUSchedLit, LvmS2GUPlan, LvmE2QFrontU, LvmS2GUGood, LvmE2QNodeU, LvmE2URef,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is the SLF-K moved.tsv. -/
import LvmS2GUSched
import LvmS2GUFront
import LvmS2GUSchedLit
import LvmS2GUPlan
import LvmE2QFrontU
import LvmS2GUGood
import LvmE2QNodeU
import LvmE2URef

-- ===== from `LvmS2GUSched` =====

section
set_option autoImplicit false
namespace Lvm
open RecursionFast

/-- **The width of the `i`-th read** at S2GU (24 past the schedule). -/
def rwU20 (i : Nat) : Nat := (readWidthsP P20U).getD i eBytes

/-- **UTAPE-STMT 1** (owner L): `phases` dispatches stage `3` to `phasesS2GU` (pins the `LvmSchedule` edit). -/
theorem phases_P20U : phases P20U = phasesS2GU P20U := by
  rw [phases, ite_eq_right (show P20U.stage ≠ 1 by decide), ite_eq_right (show P20U.stage ≠ 2 by decide),
    ite_eq_left (show P20U.stage = 3 by decide), if_neg (show ¬ P20U.mbLin = true by decide)]

/-- **UTAPE-STMT 2** (owner L): S2GU's header is S2GT's, 5,664 bytes (`acc_in`: 46 scalars of 16 B). -/
theorem headerBytesP_P20U : headerBytesP P20U = 5664 ∧ seedLenP P20U = 5688 ∧ P20U.accV = Lvm.VEq.accVT := by
  decide

/-- Proof help (GOLF3-U, `LvmS2GTSched`'s private `readWidthsP_all_of`): a read width is `eBytes` or a `readW` item's
width, so `readWidthsP`'s check is one walk of the items. -/
private theorem readWidthsP_all_ofU (p : Params) (g : Nat → Bool) (he : g eBytes = true)
    (h : (schedule p).all (fun it => match it with | .readW _ w => g w | _ => true) = true) :
    (readWidthsP p).all g = true := by
  rw [List.all_eq_true] at h ⊢
  intro w hw
  rw [readWidthsP] at hw
  obtain ⟨it, hit, hw⟩ := List.mem_flatMap.mp hw
  have hi := h it hit
  cases it with
  | read m => rw [List.eq_of_mem_replicate hw]; exact he
  | readW m w' => rw [List.eq_of_mem_replicate hw]; exact hi
  | cap => simp at hw
  | sample => simp at hw
  | positions => simp at hw
  | opening => simp at hw

set_option maxRecDepth 100000 in
/-- Proof help (GOLF3-U): S2GU's sizes, read widths (as one walk of the items) and query bound in one kernel evaluation
of the schedule (the three decisions each rebuilt it: 17.9 → 10.1 M heartbeats). -/
private theorem schedFactsU : ((piSize P20U = 283960 ∧ qS P20U = 3649 ∧ hashedLen P20U = 538656 ∧
    streamLanes P20U = 67332 ∧ spongeBlocks P20U = 3961 ∧ (schedule P20U).length = 2835 ∧
    (P20U.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20U = true ∧
    (100 * streamLanes P20U ≤ 95 * streamCap P20U ∧ 100 * qS P20U ≤ 95 * 16384 ∧
      100 * spongeBlocks P20U ≤ 95 * 2 ^ P20U.recRowsLog)) ∧
    (schedule P20U).all (fun it => match it with | .readW _ w => decide (0 < w) | _ => true) = true ∧
    (2 + qcItems P20U (schedule P20U) 0 ≤ 16384) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 3** (owner L): **S2GU's sizes** (`ref/utape.py --occ 46` [exact]; one kernel evaluation of the
tally): `|π| = 283,960`, `qS = 3,649`, `L = 538,656`, `T = 67,332`, 3,961 sponge blocks, 2,835 items (`utape-items.tsv` has 2,835 lines), the root leaf of
368 B, the length rule, the 95 % caps. -/
theorem sizes_P20U : (piSize P20U = 283960 ∧ qS P20U = 3649 ∧ hashedLen P20U = 538656 ∧
    streamLanes P20U = 67332 ∧ spongeBlocks P20U = 3961 ∧ (schedule P20U).length = 2835 ∧
    (P20U.level ⟨.main, 0⟩).row = 368) ∧
    lengthRule P20U = true ∧
    (100 * streamLanes P20U ≤ 95 * streamCap P20U ∧ 100 * qS P20U ≤ 95 * 16384 ∧
      100 * spongeBlocks P20U ≤ 95 * 2 ^ P20U.recRowsLog) :=
  schedFactsU.1

set_option maxRecDepth 100000 in
/-- Every read width of the S2GU schedule is positive (one kernel evaluation of `readWidthsP P20U`). -/
theorem readWidthsP_pos_P20U : (readWidthsP P20U).all (fun w ↦ decide (0 < w)) = true :=
  readWidthsP_all_ofU P20U _ (by decide) schedFactsU.2.1

/-- **UTAPE-STMT 4** (owner L): every read width of the S2GU schedule is positive. -/
theorem rwU20_pos : ∀ n, 0 < rwU20 n := fun n ↦ by
  unfold rwU20
  rw [List.getD_eq_getElem?_getD]
  cases h : (readWidthsP P20U)[n]? with
  | none => exact Nat.zero_lt_succ _
  | some w =>
    exact of_decide_eq_true (List.all_eq_true.mp readWidthsP_pos_P20U w (List.mem_of_getElem? h))

set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 5** (owner L): S2GU's query bound (one kernel evaluation of the schedule's query count). -/
theorem qcItems_P20U : 2 + qcItems P20U (schedule P20U) 0 ≤ 16384 :=
  schedFactsU.2.2

end Lvm
end

section
set_option autoImplicit false
namespace Lvm.CT
open Lvm Lvm.ASM

/-- **S2GU's format**: `rwU20`, `|π| = piSize P20U`, header `headerBytesP P20U`, the occupied words `occOfU`. -/
def fmtU20 : SFmt := ⟨rwU20, rwU20_pos, piSize P20U, headerBytesP P20U, occOfU⟩

end Lvm.CT
end

-- ===== from `LvmS2GUFront` =====

section
set_option autoImplicit false
namespace Lvm.E2U
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal
variable {b : ℕ}
variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-- **UTAPE-STMT 7** (owner V): **the S2GU wire** from doom of the GKR's input claim on the tape's virtual inputs
(`2^21` rows) to doom of the three row claims on `C_main` (`D`, `Y`, `M`: 23 variables each); wire and slot rounds
`c = 2`, every row switch with the follower's `T`. -/
theorem wireSpecB (hcb : 1 ≤ b ∧ b < 8080) (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest) {n : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ 20) (claim : KClaim E2) (hρ : claim.point.length + 4 = 21)
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Nonempty (Spec (wireProgB b s n claim)
      (Doomed C (fun q ↦ E2V.InClaimTrueF 21 (tapeInB b s n (colM q)) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = 20 ∧ out.d.sl.1.length = 2 ∧ out.y.sl.1.length = 5 ∧
        out.m.sl.1.length = 5 ∧
        Doomed C (fun q ↦ RowColTrue 23 (colM q) out.d.row ∧ RowColTrue 23 (colM q) out.y.row ∧
          RowColTrue 23 (colM q) out.m.row ∧ R q) hist) εS 0 T) :=
  ⟨wireSpecBW hcb hst hcard s hn hN claim hρ colM R hrT⟩

/-- **UTAPE-STMT 8** (owner V): **T1's region formula, the sponge half**: on the tape's relation and the `Y` word
claims `Ỹ_l(r_{<13}) = b_l`, the sponge half's output lane `l` at `r_{<20}` is `e·b_l + (1 − e)·z*_l` (rows
`j < 2^13` are `Y`, the void rows `Keccak-f(0)`). With the chain half (`TapeOut`, `D̃_l(r_{<20}) = a_l` for `l < 4`,
`a_l` free for `l ≥ 4`) and `r_20` drawn after `a ‖ b`, the GKR's output claim `t1ValsF` is the tape's. -/
theorem t1_spongeB (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (r ab : List E2) (hr : r.length = 21)
    (hout : TapeRelB b s n col) (hY : TiedYF (yU col) r ab) :
    ∀ l < 25, E2V.stepMleF 20 (r.take 20) (fun j ↦ laneWord (keccakF1600 (tapeInB b s n col (2 ^ 20 + j))) l) =
      eTailF 13 20 r * ab.getD (25 + l) 0 + (1 - eTailF 13 20 r) * kF (zStarK l) := by
  intro l hl
  set pt := r.take 20 with hpt
  have hptl : pt.length = 20 := by rw [hpt, List.length_take, hr]; rfl
  have ha : (pt.take 13).length = 13 := by rw [List.length_take, hptl]; rfl
  have hs : (pt.drop 13).length = 7 := by rw [List.length_drop, hptl]
  have hat : pt.take 13 = r.take 13 := by rw [hpt, List.take_take]; rfl
  -- the sponge half's rows: `Y` below `2^13`, `Keccak-f(0)` above
  have hf : ∀ j, laneWord (keccakF1600 (tapeInB b s n col (2 ^ 20 + j))) l =
      if j < 2 ^ 13 then yU col j l else zStarK l := fun j ↦ by
    split
    · rename_i hj; exact (hout.2 j hj l hl).symm
    · rename_i hj
      have e : tapeInB b s n col (2 ^ 20 + j) = Lvm.KSponge.zeroSt := by
        unfold tapeInB tapeIn
        rw [if_neg (by (clear * - ; omega)), if_neg (by (clear * - hj; omega))]
      rw [e]; rfl
  have he : eTailF 13 20 r = E2V.eqAtF (pt.drop 13) 0 := by
    have g : ∀ (c : List E2) (acc : E2), (c.map fun x ↦ 1 - x).foldl (· * ·) acc = acc * E2V.eqAtF c 0 := by
      intro c
      induction c with
      | nil => intro acc; simp [E2V.eqAtF]
      | cons x c ih =>
        intro acc
        rw [List.map_cons, List.foldl_cons, ih, E2V.eqAtF, if_neg (by (clear * - ; omega)), CharTwo.sub_eq_add,
          Nat.zero_div]
        ring
    rw [eTailF, E2V.prodF, g, one_mul]
  have hinner : ∀ o ∈ range (2 ^ 7), ∑ x ∈ range (2 ^ 13), E2V.eqAtF (pt.take 13) x *
      kF (laneWord (keccakF1600 (tapeInB b s n col (2 ^ 20 + (x + 2 ^ 13 * o)))) l) =
      kF (zStarK l) + if o = 0 then ab.getD (25 + l) 0 - kF (zStarK l) else 0 := by
    intro o _
    by_cases ho : o = 0
    · subst ho
      rw [if_pos rfl, add_sub_cancel, ← hY l hl, E2V.stepMleF, ← hat]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rw [Nat.mul_zero, Nat.add_zero, hf, if_pos (Finset.mem_range.1 hx)]
    · rw [if_neg ho, add_zero]
      have e : ∀ x ∈ range (2 ^ 13), E2V.eqAtF (pt.take 13) x *
          kF (laneWord (keccakF1600 (tapeInB b s n col (2 ^ 20 + (x + 2 ^ 13 * o)))) l) =
          E2V.eqAtF (pt.take 13) x * kF (zStarK l) := fun x _ ↦ by
        rw [hf, if_neg (by have : 1 ≤ o := Nat.pos_of_ne_zero ho; nlinarith)]
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
      have h1 := E2V.sum_eqAtF (pt.take 13)
      rw [ha] at h1
      rw [h1, one_mul]
  have hsum := E2V.sum_eqAtF (pt.drop 13)
  rw [hs] at hsum
  rw [E2V.stepMleF]
  conv_lhs => rw [← List.take_append_drop 13 pt, show 20 = 13 + (pt.drop 13).length by rw [hs]]
  rw [E2V.col_splitF ha, hs, Finset.sum_congr rfl fun o ho ↦ by rw [hinner o ho], he]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_range, Nat.two_pow_pos, if_true]
  ring

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal
variable {b : ℕ}
variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-- **UTAPE-STMT 9** (owner V): **the S2GU tape caller** (`tapeSpecE2`'s successor, V_S's CHtape and CHwire at
S2GU), round by round at `L₀ = 1`: from doom of `TapeRelB b` and `R` to doom of the three row claims, the `D` and `Y`
word claims and `R`. Lead `0`; every ground group `≤ εS` (`(1,1)`, `(2,2)`, `(3,2)`, `(46,6)` and the GKR's); the row
switches with the follower's `T`. -/
theorem tapeSpecB (hcb : 1 ≤ b ∧ b < 8080) (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest) {n : ℕ}
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Nonempty (Spec (tapeProgB b s n) (Doomed C (fun q ↦ TapeRelB b s n (colM q) ∧ R q))
      (TapePostU (C := C) colM R) εS 0 T) :=
  ⟨tapeSpecBW hcb hst hcard s colM R hrT⟩

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal
variable {b : ℕ}
variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-- `cont` at S2GU as a row predicate. -/
def contU (j : ℕ) : Bool := contB 3960 j

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal
variable {b : ℕ}
variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-- The S2GU tape's input column. -/
def tapeInU (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) : ℕ → KeccakState := tapeInB 3960 s n col

/-- The S2GU tape's relation on a `C_main` column. -/
def TapeRelU (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) : Prop := TapeRelB 3960 s n col

end Lvm.E2U
end

-- ===== from `LvmS2GUSchedLit` =====

section
set_option autoImplicit false
namespace Lvm
open RecursionFast

/-- The items of phase `.tables` at `P20U`. -/
def ph20U_tables : List Item := [
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 633]

end Lvm
end

section
set_option autoImplicit false
namespace Lvm
open RecursionFast

/-- **`phases P20U`**, phase by phase (`phases_P20U_lit`). -/
def phasesU20 : List (Phase × List Item) :=
  [(.commit, ph20U_commit),
   (.bus, ph20U_bus),
   (.tables, ph20U_tables),
   (.tape, ph20U_tape),
   (.wire, ph20U_wire),
   (.openMain, ph20U_openMain)]

set_option maxRecDepth 100000 in
/-- **The phases at `P20U` are `phasesU20`** (by `rfl` after the stage dispatch: the kernel unfolds the builders against
the literal). -/
theorem phases_P20U_lit : phases P20U = phasesU20 := by
  rw [phases_P20U]; rfl

/-- **`schedule P20U`** as one list (`schedule_P20U_lit`). -/
def schedU20 : List Item := [
    .cap 8 ⟨.main, 0⟩, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .read 1, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8,
    .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8,
    .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 9 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 12 16, .readW 4 16, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 1 16, .readW 1 8, .sample, .readW 1 8,
    .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 46 16, .readW 1 8, .sample, .readW 1 16, .sample, .sample,
    .sample, .sample, .sample, .read 2, .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4,
    .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample,
    .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample,
    .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample,
    .read 12, .sample, .sample, .read 1, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 633, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8,
    .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8,
    .sample, .readW 1 8, .sample, .readW 50 16, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16,
    .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16,
    .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16, .sample,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 47 16,
    .sample, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16,
    .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8,
    .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample, .readW 3 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 3 16, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 64 16, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 64 16,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 64 16, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .cap 7 ⟨.main, 1⟩, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .read 1, .read 2, .sample, .read 1, .sample,
    .positions ⟨.main, 0⟩, .sample, .opening ⟨.main, 0⟩, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .cap 7 ⟨.main, 2⟩, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .read 1, .read 2, .sample, .read 1, .sample, .positions ⟨.main, 1⟩,
    .sample, .opening ⟨.main, 1⟩, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .read 512, .sample, .read 1, .sample, .positions ⟨.main, 2⟩, .sample, .opening ⟨.main, 2⟩, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample]

set_option maxRecDepth 100000 in
/-- **The schedule at `P20U` is `schedU20`** (by `rfl` from `phases_P20U_lit`). -/
theorem schedule_P20U_lit : schedule P20U = schedU20 := by
  rw [schedule, phases_P20U_lit]; rfl

end Lvm
end

-- ===== from `LvmS2GUPlan` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

/-- The cap entries at `P20U` and their lengths (the FS queries that absorb the caps). -/
def tblU20 : List (ℕ × ℕ) := [(2, 8224), (1004, 4176), (2423, 4176)]

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay Lvm.PlanChk

set_option maxRecDepth 200000 in
/-- **The plan's facts at `P20U`** in one kernel evaluation (the walk over `schedU20` at `P20UL`). -/
private theorem planFactsU :
    passR (capLk tblU20) 3649 283952 538655 (plan P20U) tblU20 0 0 0 = true ∧
      (PlanOk P20U ∧ (planAll P20U).2.i = 3649) ∧ qOkF P20U (lay cfgU20) = true :=
  planFacts_of schedule_P20U_lit P20U_eqL sizes_P20U.1.2.2.1 (by decide +kernel)

/-- **The one decision at `P20U`.** -/
theorem passR_P20U : passR (capLk tblU20) 3649 283952 538655 (plan P20U) tblU20 0 0 0 = true :=
  planFactsU.1

/-- `PlanOk P20U` and the walk's last entry. -/
theorem planSt_P20U : PlanOk P20U ∧ (planAll P20U).2.i = 3649 :=
  planFactsU.2.1

/-- **Q_link's stream facts at `P20U`.** -/
theorem streamOk_P20U : StreamOk P20U := streamOk_ofR passR_P20U sizes_P20U.1.2.2.1

/-- Q_link's static checks at S2GU as `qOkF` (`hQU20`'s decision, from `planFactsU`). -/
theorem qOkF_P20U : qOkF P20U (lay cfgU20) = true :=
  planFactsU.2.2

end Lvm.E2Q
end

-- ===== from `LvmE2QFrontU` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

set_option maxRecDepth 100000 in
/-- The first items of `P20U`'s phases (proof help, GOLF3-U: one walk of the literal `phasesU20`). -/
private theorem phaseItem0_P20U : phaseItem0 P20U .commit = 0 ∧ phaseItem0 P20U .bus = 25 ∧
    phaseItem0 P20U .tape = 371 ∧ phaseItem0 P20U .wire = 2609 ∧ phaseItem0 P20U .openMain = 2730 := by
  simp only [phaseItem0, phases_P20U_lit]; decide +kernel

/-- The phases' suffixes at `P20U` from one another (proof help: `.wire` and `.openMain` from `.tape`'s suffix). -/
private theorem drop_chainU (l : List Nat) :
    l.drop 2730 = ((l.drop 371).drop 2238).drop 121 ∧ l.drop 2609 = (l.drop 371).drop 2238 := by
  constructor <;> simp only [List.drop_drop]

set_option maxRecDepth 200000 in
/-- **`P20U`'s positions** (one kernel evaluation of the schedule's lanes): the pin's start after the cap, its first
answer, its value, its end at the typed phases, and the lanes of the phase `bus`. -/
theorem posU20 : startByte P20U + nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap = posOf P20U 1 ∧
    posOf P20U 1 + 40 = 8 * phaseLane P20U .commit 1 ∧
    phaseLane P20U .commit (P20U.nuMain + 1) = phaseLane P20U .commit 1 + 9 * P20U.nuMain ∧
    posOf P20U 1 + 72 * P20U.nuMain + 24 = typedPosF P20U ∧ busLanesB P20U = true ∧
    ((∀ i < 20, 8 * phaseLane P20U .tape (2 + 2 * i) = posOf P20U (phaseItem0 P20U .tape) + 120 + 80 * i) ∧
      8 * phaseLane P20U .tape 41 = posOf P20U (phaseItem0 P20U .tape) + 1712 ∧
      8 * phaseLane P20U .tape 43 = posOf P20U (phaseItem0 P20U .tape) + 2520 ∧
      8 * phaseLane P20U .tape 45 = posOf P20U (phaseItem0 P20U .tape) + 2600 ∧
      posOf P20U (phaseItem0 P20U .wire) = 8 * Lvm.Q1.tapeEnd2 16 (phaseLane P20U .tape 45) - 40 ∧
      8 * phaseLane P20U .wire 0 = posOf P20U (phaseItem0 P20U .wire) + 40 ∧
      posOf P20U (phaseItem0 P20U .openMain) = posOf P20U (phaseItem0 P20U .wire) + 8216 ∧
      posOf P20U (phaseItem0 P20U .tape) % 8 = 0) := by
  -- GOLF3-U: the lanes over the literals `phasesU20`, `schedU20` and `P20UL`, one suffix per phase (`unfold P20U P20T;
  -- rw [P20_eq]` left the kernel the builders, a defeq through the rewritten motive and ~40 lookups from the head)
  simp only [posOf_drop, phaseLane_drop, typedPosF, busLanesB, busL_drop, phaseItem0_P20U.1, phaseItem0_P20U.2.1,
    phaseItem0_P20U.2.2.1, phaseItem0_P20U.2.2.2.1, phaseItem0_P20U.2.2.2.2]
  rw [itemLanes, schedule_P20U_lit, P20U_eqL, (drop_chainU _).1, (drop_chainU _).2, itemLanesAux_eq_R]
  simp only [← dropLN_eq, ← getDLN_eq, iZR, iWR, iRR, getDLN_add]
  decide +kernel

theorem hbU : Lvm.Har.pos (RS.startH (headerBytesP P20U)) + nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap =
    posOf P20U 1 := by
  rw [pos_startH]; exact posU20.1

theorem pinHPU : posOf P20U 1 + 40 = 8 * phaseLane P20U .commit 1 := posU20.2.1

theorem pinQaU : phaseLane P20U .commit (P20U.nuMain + 1) = phaseLane P20U .commit 1 + 9 * P20U.nuMain :=
  posU20.2.2.1

theorem pinEndU : posOf P20U 1 + 72 * P20U.nuMain + 24 = typedPosF P20U := posU20.2.2.2.1

theorem busLanesB_P20U : busLanesB P20U = true := posU20.2.2.2.2.1

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped
section WirePh
open Lvm.Q2 DM

set_option maxHeartbeats 1000000 in
/-- **V's S2GU wire by phases** (`wireUDG rowSwitchDR`, `w = 20`, from `P`, first message lane `q`): the wire
sumcheck, `g_D, g_Y, g_M`, the final check (`hfin`), the slot reductions of `D` (2 rounds, from `P + 2288`), `Y`
(5, from `+ 1752`) and `M` (5, from `+ 2088`) with their checks. -/
theorem wireUDG_phase {sig : ByteArray} {q P : ℕ} (p : Params) (hw : p.logN = 20) (hk : p.ksLog = 13) (s : List FK)
    (n : ℕ) (claim : E2V.KClaim FE2) (hq : 8 * q = P + 40)
    (hpw : ∀ k < 20, powOKR E2V.gC2 (feAt sig (P + 80 + 112 * k)) = true)
    (hpD : ∀ k < 2, powOKR E2V.gC2 (feAt sig (P + 2288 + 80 + 112 * k)) = true)
    (hpY : ∀ k < 5, powOKR E2V.gC2 (feAt sig (P + 4040 + 80 + 112 * k)) = true)
    (hpM : ∀ k < 5, powOKR E2V.gC2 (feAt sig (P + 6128 + 80 + 112 * k)) = true)
    (hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 q (wireTargetDF (sBitsD s) n claim) =
      E2V.msEvalF claim.point claim.mu (scPts sig P 20) 0 (n - 1) * fe2At sig (P + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig P 20) *
          (Lvm.E2U.kksF Lvm.E2U.contIvU claim.point claim.mu ((scPts sig P 20).take 13) (2 ^ 20) *
              fe2At sig (P + 2296) +
            E2V.ikEvalP claim.point claim.mu ((scPts sig P 20).take 13) (2 ^ 20) * fe2At sig (P + 2312)))
    (hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((P + 2288 + 40) / 8) (fe2At sig (P + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claim.weights.toArray) (scPts sig (P + 2288) 2) z *
        (readsE2 sig (P + 2288 + 112 * 2) 64).getD z 0))
    (hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 4040 + 40) / 8) (fe2At sig (P + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claim.weights) (scPts sig (P + 4040) 5) z *
        (readsE2 sig (P + 4040 + 112 * 5) 64).getD z 0))
    (hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 6128 + 40) / 8) (fe2At sig (P + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claim.weights) (scPts sig (P + 6128) 5) z *
        (readsE2 sig (P + 6128 + 112 * 5) 64).getD z 0)) :
    PhaseAt (Lvm.E2U.wireUDG rowSwitchDR p s n claim) sig P (P + 8216)
      ⟨(scPts sig P 20, scFold2 (fun k => fe2At sig (8 * k)) 20 q (wireTargetDF (sBitsD s) n claim)),
        readsE2 sig (P + 2240) 3,
        ((scPts sig (P + 2288) 2, scFold2 (fun k => fe2At sig (8 * k)) 2 ((P + 2288 + 40) / 8) (fe2At sig (P + 2280))),
          readsE2 sig (P + 2288 + 112 * 2) 64,
          (rowSwitchDR (scPts sig P 20 ++ scPts sig (P + 2288) 2 ++ Lvm.E2V.selPtF (dSel p) (dSelBits p))
            (readsE2 sig (P + 2288 + 112 * 2) 64) sig ⟨P + 2288 + 112 * 2 + 1024, 0, true⟩).1),
        ((scPts sig (P + 4040) 5, scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 4040 + 40) / 8) (fe2At sig (P + 2296))),
          readsE2 sig (P + 4040 + 112 * 5) 64,
          (rowSwitchDR ((scPts sig P 20).take 13 ++ scPts sig (P + 4040) 5 ++
              Lvm.E2V.selPtF ((layout0 p).ks / 2 ^ (p.ksLog + 5)) (p.nuMain - (p.ksLog + 5)))
            (readsE2 sig (P + 4040 + 112 * 5) 64) sig ⟨P + 4040 + 112 * 5 + 1024, 0, true⟩).1),
        ((scPts sig (P + 6128) 5, scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 6128 + 40) / 8) (fe2At sig (P + 2312))),
          readsE2 sig (P + 6128 + 112 * 5) 64,
          (rowSwitchDR ((scPts sig P 20).take 13 ++ [0] ++ scPts sig (P + 6128) 5 ++
              Lvm.E2V.selPtF ((layout0 p).s / 2 ^ p.nuRec) (p.nuMain - p.nuRec))
            (readsE2 sig (P + 6128 + 112 * 5) 64) sig ⟨P + 6128 + 112 * 5 + 1024, 0, true⟩).1)⟩ := by
  unfold Lvm.E2U.wireUDG
  rw [hw, hk]
  simp only [Lvm.E2U.slotBitsU]
  refine phaseAt_bind (sumcheckD_phase hq hpw) (phaseAt_bind readE2s_phase (phaseAt_bind
    (phaseAt_require ?_) ?_))
  · have g0 : (readsE2 sig (P + 112 * 20) 3).getD 0 0 = fe2At sig (P + 2280) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g1 : (readsE2 sig (P + 112 * 20) 3).getD 1 0 = fe2At sig (P + 2296) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g2 : (readsE2 sig (P + 112 * 20) 3).getD 2 0 = fe2At sig (P + 2312) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    dsimp only
    rw [beq_iff_eq, g0, g1, g2]
    exact hfin
  · have hP8 : P % 8 = 0 := by omega
    have e1 : P + 112 * 20 + 16 * 3 = P + 2288 := by ring
    have hr : readsE2 sig (P + 112 * 20) 3 = readsE2 sig (P + 2240) 3 := by rw [show 112 * 20 = 2240 by rfl]
    dsimp only
    rw [e1, hr]
    have g0 : (readsE2 sig (P + 2240) 3).getD 0 0 = fe2At sig (P + 2280) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g1 : (readsE2 sig (P + 2240) 3).getD 1 0 = fe2At sig (P + 2296) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g2 : (readsE2 sig (P + 2240) 3).getD 2 0 = fe2At sig (P + 2312) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    rw [g0, g1, g2]
    refine phaseAt_bind (slotDFG_phase (q := (P + 2288 + 40) / 8) (by omega) hpD hD) ?_
    rw [show P + 2288 + 112 * 2 + 1024 + 504 = P + 4040 by ring, Lvm.E2U.slotDFW_yWG]
    refine phaseAt_bind (slotDFG_phase (q := (P + 4040 + 40) / 8) (by omega) hpY hY) ?_
    rw [show P + 4040 + 112 * 5 + 1024 + 504 = P + 6128 by ring, Lvm.E2U.slotDFW_mWG,
      show Lvm.E2U.slotBitsU = 5 from rfl]
    refine phaseAt_bind (slotDFG_phase (q := (P + 6128 + 40) / 8) (by omega) hpM hM) ?_
    rw [show P + 6128 + 112 * 5 + 1024 + 504 = P + 8216 by ring]
    exact phaseAt_pure

end WirePh
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped
section WirePh
open Lvm.Q2 DM

set_option maxHeartbeats 1000000 in
/-- **V's merged tape by phases** (`tapeUDG rowSwitchDR`, `w = 20`, from `P`): the separator, `r_{<20}` (answers
`8 q₀ = P + 120`), the 50 scalars, `r₂₀` (answer at `P + 2520`), the GKR on T1's values (`htg`, from `P + 2552`),
`n`'s range, the wire (`hwire`). -/
theorem tapeUDG_phase {sig : ByteArray} {q0 P P5 P6 : ℕ} (p : Params) (hw : p.logN = 20) (hk : p.ksLog = 13)
    (s : List FK) (n : ℕ) {claim : E2V.KClaim FE2} {wo : Lvm.E2U.WireU RowZ} (hq0 : 8 * q0 = P + 120)
    (hpowR : Lvm.Q1.PowOkV (feAt sig) (chalsG q0 E2V.gC1 20))
    (hpow20 : powOKR E2V.gC1 (feAt sig (P + 2520)) = true)
    (htg : PhaseAt (tapeGkrDF 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)))
      sig (P + 2552) P5 claim)
    (hn : 1 ≤ n ∧ n ≤ 2 ^ 20) (hwire : PhaseAt (Lvm.E2U.wireUDG rowSwitchDR p s n claim) sig P5 P6 wo) :
    PhaseAt (Lvm.E2U.tapeUDG rowSwitchDR p s n) sig P P6
      ⟨sampsG sig (P + 72) 20, fe2At sig (P + 2520), readsE2 sig (P + 1672) 50, claim, wo⟩ := by
  unfold Lvm.E2U.tapeUDG
  rw [hw, hk]
  refine phaseAt_bind sepE2_phase (phaseAt_bind (samplesG_phase (by omega) hpowR) (phaseAt_bind readE2s_phase ?_))
  rw [show P + 72 + 80 * 20 + 16 * (2 * 25) = P + 2472 by ring,
    show P + 72 + 80 * 20 = P + 1672 by ring]
  refine phaseAt_bind (sampleG_phase (by rw [show P + 2472 + 48 = P + 2520 by ring]; exact hpow20)) ?_
  rw [show P + 2472 + 48 = P + 2520 by ring, show P + 2472 + 80 = P + 2552 by ring]
  exact phaseAt_bind htg (phaseAt_bind (phaseAt_require (decide_eq_true hn)) (phaseAt_bind hwire phaseAt_pure))

end WirePh
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

/-- The lanes of `CHwire` at `P20U` (the slices of the three slot reductions, the row switches' answers). -/
abbrev wlU : Lvm.Q2.WireLanesU := Lvm.Q2.wireLanesU P20U.logN (phaseLane P20U .wire 0)

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped
section FrontU
open Lvm.Q2 Lvm.QShape
variable {M : Mem}

theorem ksSplit_P20U' : ksSplit P20U = 7680 := by decide

end FrontU
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped
section FrontU
open Lvm.Q2 Lvm.QShape
variable {M : Mem}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **UTAPE-STMT 25b (`front_phasesU`)**: the front's phases at `P20U` (`front_phasesT`'s twin for `frontU`): from the
front's rows and assertions (gate on), the proof-of-work answers (`powFrontU`), the three row switches' words (the
`rowAux` blocks on `tBu`), `n'`'s bits and range and the bits of `s'`, V_S's merged tape with the wire runs from the
tape's first item to the opening's, the front's claims stand for `frontItemsU`'s, and `mb` is `n' − 1`'s selector. -/
theorem front_phasesU {c : Ctx} {M : Mem} {sig : ByteArray} {q : Ptr}
    (hS : Lvm.Q1.Streamed M sig (streamLanes P20U))
    (hTo : posOf P20U (phaseItem0 P20U .openMain) + 48 ≤ 8 * streamLanes P20U)
    (hg : M.k (pbB cfgU20) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFrontU P20U))
    (hrD : ∀ j < 128, M.k (tBu cfgU20 0 + j) = rowWordD (Lvm.Q2.slicesOf M wlU.slicesD) j)
    (hrY : ∀ j < 128, M.k (tBu cfgU20 1 + j) = rowWordD (Lvm.Q2.slicesOf M wlU.slicesY) j)
    (hrM : ∀ j < 128, M.k (tBu cfgU20 2 + j) = rowWordD (Lvm.Q2.slicesOf M wlU.slicesM) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn cfgU20).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB cfgU20 + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontU cfgU20) q) :
    ∃ tp : Lvm.E2U.TapeU Lvm.RowZ,
      Lvm.Har.PhaseAt (Lvm.E2U.tapeUDG Lvm.rowSwitchDR P20U pub.s pub.n) sig
        (posOf P20U (phaseItem0 P20U .tape)) (posOf P20U (phaseItem0 P20U .openMain)) tp ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontU cfgU20 q).1.cs
        ((Lvm.E2U.frontItemsU Lvm.rowAccR P20U pub tp).flatMap Lvm.FItem.flat) ∧
      vs M (frontU cfgU20 q).1.mb = selectorPoint (pub.n - 1) 20 := by
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨T, hTl⟩ : ∃ T, streamLanes P20U = T := ⟨_, rfl⟩
  rw [hTl] at hS hTo
  -- GOLF3-U: no `streamLanes P20U` fact left: every later `omega` listed it as an atom and the kernel evaluated the
  -- tally while checking each certificate (0.2–0.5 M heartbeats per `omega`)
  clear hTl
  have hgv : (kc (pbB cfgU20)).val M = 1 := by rw [Cell.val_K, hg, ofK_one]
  have hp : cfgU20.p = P20U := rfl
  -- the positions
  obtain ⟨pR, pOut, p20, pQs, pW, pQw, pOp, -⟩ := posU20.2.2.2.2.2
  simp only [phaseLane] at pR pOut p20 pQs pW pQw
  simp only [wlU, phaseLane, logN_P20U] at hrD hrY hrM
  -- the proof of work, by phase
  simp only [powFrontU, getD_toArray, logN_P20U, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hpow
  obtain ⟨hp3, hpW⟩ := powOkV_append hpow
  obtain ⟨hp2, hpT⟩ := powOkV_append hp3
  obtain ⟨hpR, hp20⟩ := powOkV_append hp2
  clear hpow hp3 hp2
  -- the front's gadgets
  obtain ⟨fo, hfo⟩ : ∃ fo, (frontU cfgU20 q).1 = fo := ⟨_, rfl⟩
  rw [hfo]
  simp only [frontU, hp, getD_toArray, Lvm.Q1.tapeGadgetE2F_eq, logN_P20U, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub] at h hfo
  obtain ⟨q1, hZ, h1, E⟩ := ok_bindE h
  clear h
  rw [E] at hfo
  rw [show (const .E 0 (kc 0) q).1 = ec q.e from rfl] at h1 hfo
  obtain ⟨q2, hO, h2, E⟩ := ok_bindE h1
  clear h1
  rw [E] at hfo
  rw [show (const .E 1 (kc 0) q1).1 = ec q1.e from rfl] at h2 hfo
  obtain ⟨q3, hZK, h3, E⟩ := ok_bindE h2
  clear h2
  rw [E] at hfo
  rw [show (const .K 0 (kc 0) q2).1 = kc q2.k from rfl] at h3 hfo
  obtain ⟨q4, hOK, h4, E⟩ := ok_bindE h3
  clear h3
  rw [E] at hfo
  rw [show (const .K 1 (kc 0) q3).1 = kc q3.k from rfl] at h4 hfo
  have hz : M.e q.e = 0 := (const_val hZ.1).trans ofK_zero
  have ho : M.e q1.e = 1 := (const_val hO.1).trans ofK_one
  have hzk : (kc q2.k).val M = 0 := (const_val hZK.1).trans ofK_zero
  have hok : M.k q3.k = 1 := congrArg FE.c₀ ((const_val hOK.1).trans ofK_one.symm)
  clear hZ hO hZK hOK
  obtain ⟨q5, hV, h5, E⟩ := ok_bindE h4
  clear h4
  rw [E] at hfo
  obtain ⟨q6, hT, h6, E⟩ := ok_bindE h5
  clear h5
  rw [E] at hfo
  obtain ⟨q7, hB, h7, E⟩ := ok_bindE h6
  clear h6
  rw [E] at hfo
  obtain ⟨q8, hW, h8, E⟩ := ok_bindE h7
  clear h7
  rw [E] at hfo
  obtain ⟨q9, hRD, h9, E⟩ := ok_bindE h8
  clear h8
  rw [E] at hfo
  obtain ⟨q10, hND, h10, E⟩ := ok_bindE h9
  clear h9
  rw [E] at hfo
  obtain ⟨q11, hRY, h11, E⟩ := ok_bindE h10
  clear h10
  rw [E] at hfo
  obtain ⟨q12, hNY, h12, E⟩ := ok_bindE h11
  clear h11
  rw [E] at hfo
  obtain ⟨q13, hRM, h13, E⟩ := ok_bindE h12
  clear h12
  rw [E] at hfo
  obtain ⟨q14, hNM, h14, E⟩ := ok_bindE h13
  clear h13
  rw [E] at hfo
  obtain ⟨q15, hME, -, E⟩ := ok_bindE h14
  clear h14
  rw [E] at hfo
  clear E
  -- names
  -- GOLF3-U: `generalize`, not `set`: as `let` values the positions were closed atoms of every later `omega`, which
  -- the kernel evaluated (the lanes' walk) while checking the certificates
  have hq0' : 8 * laneOf P20U (phaseItem0 P20U .tape + 2) = posOf P20U (phaseItem0 P20U .tape) + 120 := by
    have := pR 0 (by norm_num); simpa using this
  generalize posOf P20U (phaseItem0 P20U .tape) = Pt at *
  generalize posOf P20U (phaseItem0 P20U .wire) = Pw at *
  generalize posOf P20U (phaseItem0 P20U .openMain) = Pop at *
  generalize laneOf P20U (phaseItem0 P20U .tape + 45) = qs at *
  generalize laneOf P20U (phaseItem0 P20U .wire + 0) = qw at *
  generalize laneOf P20U (phaseItem0 P20U .tape + 41) = tOut at *
  generalize laneOf P20U (phaseItem0 P20U .tape + 43) = r43 at *
  generalize laneOf P20U (phaseItem0 P20U .tape + 2) = q0 at *
  have hri : ∀ i < 20, laneOf P20U (phaseItem0 P20U .tape + (2 + 2 * i)) = q0 + 10 * i := fun i hi => by
    have := pR i hi; omega
  have htE : qs + 49 ≤ Lvm.Q1.tapeEnd2 16 qs := by unfold Lvm.Q1.tapeEnd2 Lvm.Q1.tapeQ2; omega
  have hqwE : qw = Lvm.Q1.tapeEnd2 16 qs := by omega
  have hTw : qw + 1027 < T := by omega
  -- GOLF3-U: the tape's end as a variable too (as a closed `omega` atom the kernel evaluated `lay02 16`); the link kept
  -- as a `HEq`, which `omega` does not read
  generalize hE : Lvm.Q1.tapeEnd2 16 qs = E at *
  have hEh : HEq (Lvm.Q1.tapeEnd2 16 qs) E := heq_of_eq hE
  clear hE
  -- T1's values and the tape GKR
  set F : FCtx := ⟨ec q.e, ec q1.e, kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc q3.k, kc q2.k⟩, false⟩ with hF
  set r : List C2 := (List.range 20).map fun i => Lvm.Q1.laneC2 (laneOf P20U (phaseItem0 P20U .tape + (2 + 2 * i)))
    with hr
  set r20 := Lvm.Q1.laneC2 r43 with hr20
  set a : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 2 * l) with ha
  set bb : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 50 + 2 * l) with hbb
  have hz2v : F.z2.val M = 0 := by
    show (⟨((kc q2.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 0
    rw [hzk]; rfl
  have ho2v : F.o2.val M = 1 := by
    show (⟨((kc q3.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 1
    rw [Cell.val_K, hok, ofK_one, hzk]; rfl
  have hrl : r.length = 20 := by simp [hr]
  have hrv : r.map (C2.val M) = sampsG sig (Pt + 72) 20 := by
    rw [hr, List.map_map]
    unfold sampsG
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [hri i hi', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hr20v : r20.val M = fe2At sig (Pt + 2520) := by rw [hr20, Lvm.Q1.laneC2_val hS (by omega), p20]
  have hav : (List.range 25).map (fun l => (a.getD l default).val M) = readsE2 sig (Pt + 1672) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [ha, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hbv : (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672 + 16 * 25) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [hbb, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have habv : ((List.range 25).map fun l => (a.getD l default).val M) ++
      (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672) 50 := by
    rw [hav, hbv, show 50 = 25 + 25 from rfl, readsE2_add]
  have hV1 := hs_tOneU F hz2v ho2v r hrl r20 a bb q4 hV.1
  have hinst : (List.range (16 + 5)).map (fun i => ((r ++ [r20]).getD i default).val M) =
      sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)] := by
    rw [show 16 + 5 = (r ++ [r20]).length by simp [hrl], map_range_getD, List.map_append, hrv, List.map_singleton,
      hr20v]
  have hout : (List.range 25).map (fun l => ((tOneU F r r20 a bb q4).1.getD l default).val M) =
      Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50) := by
    rw [List.map_congr_left fun l hl => hV1 l (List.mem_range.mp hl), hrv, hr20v, habv]
    conv_rhs => unfold Lvm.E2U.t1ValsF
    exact List.map_congr_left fun l hl => by
      unfold Lvm.E2U.t1ValsF; exact getD_map_range0 _ (List.mem_range.mp hl)
  have TG := tapeGkr_phaseU hS (P := Pt) (qs := qs) pQs (by rw [eq_of_heq hEh]; omega) hT.1 hT.2 hgv hpT hinst hout
  obtain ⟨TG1, hR⟩ := TG
  set claimV := (tapeGkrD 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (Lvm.E2U.t1ValsF 20 13
    (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)) sig ⟨Pt + 2552, 0, true⟩).1
    with hclaimV
  set cv := (Lvm.Q1.tapeGadgetE2 16 qs (fun i => (r ++ [r20]).getD i default)
    (fun l => ((tOneU F r r20 a bb q4).1).getD l default) (kc (pbB cfgU20)) q5).1.cv with hcv
  -- `n' − 1`'s bits
  have hmbv := borrowK_vs (N := pub.n) (show M.k (kc q3.k).n = 1 from hok) (fun j hj => hnb j hj) hn1 hB.1
  have hmb := kC2_bits (m := 20) hzk hmbv
  -- the wire gadget
  have hsbl : (sbCells cfgU20).length = 256 := by simp [sbCells]
  have hBs : spongeBlocks P20U - 1 < 2 ^ 13 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have hKs : ksSplit P20U + 399 + 31 < 2 ^ 13 := by rw [ksSplit_P20U']; norm_num
  obtain ⟨wo, hwo, WS⟩ := hsA_out (wireGU_sound qw cv _ (sbCells cfgU20) (spongeBlocks P20U) (ksSplit P20U + 399)
    (kc q2.k) (kc (pbB cfgU20)) (pub.n - 1) hzk hgv hsbl hmb (by omega) hBs hKs) hW
  rw [wireLanesU_20] at WS
  dsimp only at WS
  obtain ⟨hs1, hd1, hy1, hm1, hfinW, hDW, hYW, hMW⟩ := WS
  have hpt : cvRho M 16 cv = claimV.point := hR.point
  have hmu : cvMu M cv = claimV.mu := hR.mu
  have hω : ∀ j < 1600, claimV.weights.getD j 0 = omegaF M 16 cv j := fun j hj => Lvm.Q1.rep2_lt_posF hR hj
  have htgt : targetF M 16 cv (((sbCells cfgU20).map fun b => kC2 b (kc q2.k)).map (C2.val M)) (pub.n - 1) =
      wireTargetDF (sBitsD pub.s) pub.n claimV := by
    rw [wireTargetDF_eq]
    exact targetF_eq 16 cv claimV pub.s pub.n _ hR.value.symm hmu.symm hpt.symm hω (sb_vals hzk pub.s hsb)
  have hσ : wo.sigma.map (C2.val M) = scPts sig Pw 20 := by rw [hs1]; exact sc2_vals hS pQw (by omega)
  have hτD : wo.tauD.map (C2.val M) = scPts sig (Pw + 2288) 2 := by rw [hd1]; exact sc2_vals hS (by omega) (by omega)
  have hτY : wo.tauY.map (C2.val M) = scPts sig (Pw + 4040) 5 := by rw [hy1]; exact sc2_vals hS (by omega) (by omega)
  have hτM : wo.tauM.map (C2.val M) = scPts sig (Pw + 6128) 5 := by rw [hm1]; exact sc2_vals hS (by omega) (by omega)
  have hg0 : (ld2 (qw + 280)).val M = fe2At sig (Pw + 2280) := by rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg1 : (ld2 (qw + 280 + 2)).val M = fe2At sig (Pw + 2296) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg2 : (ld2 (qw + 280 + 4)).val M = fe2At sig (Pw + 2312) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hcont : [(1, spongeBlocks P20U - 1), (ksSplit P20U + 399 + 1, ksSplit P20U + 399 + 31)] = Lvm.E2U.contIvU := by
    rw [sizes_P20U.1.2.2.2.2.1, ksSplit_P20U']; rfl
  have hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 qw (wireTargetDF (sBitsD pub.s) pub.n claimV) =
      E2V.msEvalF claimV.point claimV.mu (scPts sig Pw 20) 0 (pub.n - 1) * fe2At sig (Pw + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig Pw 20) *
          (Lvm.E2U.kksF Lvm.E2U.contIvU claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) *
              fe2At sig (Pw + 2296) +
            E2V.ikEvalP claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) * fe2At sig (Pw + 2312)) := by
    rw [← htgt, ← scFold2_ld2 hS (by omega), hfinW, hpt, hmu, hσ, hg0, hg1, hg2, hcont]
  have hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((Pw + 2288 + 40) / 8) (fe2At sig (Pw + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claimV.weights.toArray) (scPts sig (Pw + 2288) 2) z *
        (readsE2 sig (Pw + 2288 + 112 * 2) 64).getD z 0) := by
    rw [show (Pw + 2288 + 40) / 8 = qw + 286 by omega, ← hg0, ← scFold2_ld2 hS (by omega), hDW, E2V.sumF_eq_sum,
      dWA_eq]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτD, slotW_eq _ _ (by simp [scPts]) _ hω zz hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 4040 + 40) / 8) (fe2At sig (Pw + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claimV.weights) (scPts sig (Pw + 4040) 5) z *
        (readsE2 sig (Pw + 4040 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 4040 + 40) / 8 = qw + 505 by omega, ← hg1, ← scFold2_ld2 hS (by omega), hYW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτY, slotWF_yWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 6128 + 40) / 8) (fe2At sig (Pw + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claimV.weights) (scPts sig (Pw + 6128) 5) z *
        (readsE2 sig (Pw + 6128 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 6128 + 40) / 8 = qw + 766 by omega, ← hg2, ← scFold2_ld2 hS (by omega), hMW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτM, slotWF_mWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  obtain ⟨hpw, hpD, hpY, hpM⟩ := powW_of pQw hpW
  have WP := wireUDG_phase (P := Pw) (q := qw) P20U rfl rfl pub.s pub.n claimV pQw hpw hpD hpY hpM hfin hD hY hM
  have TG1' : Lvm.Har.PhaseAt (tapeGkrDF 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)))
      sig (Pt + 2552) Pw claimV := by rw [pW, ← eq_of_heq hEh]; exact TG1
  have hp20' : DM.powOKR E2V.gC1 (feAt sig (Pt + 2520)) = true := by
    have := hp20 _ List.mem_cons_self; rwa [p20] at this
  have TP := tapeUDG_phase (P := Pt) (q0 := q0) P20U rfl rfl pub.s pub.n hq0' hpR hp20' TG1' ⟨hn1, hn2⟩ WP
  rw [pOp]
  refine ⟨_, TP, ?_, ?_⟩
  · rw [← hfo]
    subst hwo
    simp only [wireLanesU_20] at hrD hrY hrM
    have hsD := slicesOf_reads hS (a := qw + 314) (P := Pw + 2288 + 112 * 2) (by omega) (by omega)
    have hsY := slicesOf_reads hS (a := qw + 575) (P := Pw + 4040 + 112 * 5) (by omega) (by omega)
    have hsM := slicesOf_reads hS (a := qw + 836) (P := Pw + 6128 + 112 * 5) (by omega) (by omega)
    rw [hsD] at hrD
    rw [hsY] at hrY
    rw [hsM] at hrM
    have hTD : (wireLanesU 20 qw).ringD + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTY : (wireLanesU 20 qw).ringY + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTM : (wireLanesU 20 qw).ringM + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    refine front_claimsU (zc := zc) (b := b) (pub := pub) (F := F) (r := r) (a := a) (bb := bb)
      (sY := E2V.selPtF ((layout0 P20U).ks / 2 ^ (P20U.ksLog + 5)) (P20U.nuMain - (P20U.ksLog + 5)))
      (sM := E2V.selPtF ((layout0 P20U).s / 2 ^ P20U.nuRec) (P20U.nuMain - P20U.nuRec))
      (eqD := (rowG (wireLanesU 20 qw).ringD (tBu cfgU20 0) (ec q.e).n (ec q1.e).n q8).1.eqR.map (Cell.val M))
      (eqY := (rowG (wireLanesU 20 qw).ringY (tBu cfgU20 1) (ec q.e).n (ec q1.e).n q10).1.eqR.map (Cell.val M))
      (eqM := (rowG (wireLanesU 20 qw).ringM (tBu cfgU20 2) (ec q.e).n (ec q1.e).n q12).1.eqR.map (Cell.val M))
      hz2v ho2v ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hz ho ?_ hrl ?_ ?_ hrv.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hσ.symm hτD.symm ?_
      ?_ ?_ ?_ ?_ ?_ ?_ hh hsm hn1
    · intro x hx
      rw [hr] at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
    · intro l hl; rw [ha, getD_map_range _ (by omega)]; exact ⟨rfl, rfl⟩
    · intro l hl; rw [hbb, getD_map_range _ hl]; exact ⟨rfl, rfl⟩
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD l 0 = _
      rw [← habv, List.getD_append _ _ _ _ (by simp; omega), getD_map_range0 _ (by omega)]
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD (25 + l) 0 = _
      rw [← habv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, getD_map_range0 _ hl]
    · rw [hs1]; exact ld2_K _
    · rw [hs1]; simp [sc2Ans]
    · rw [hd1]; exact ld2_K _
    · rw [hd1]; simp [sc2Ans]
    · rw [hy1]; exact ld2_K _
    · rw [hy1]; simp [sc2Ans]
    · rw [hm1]; exact ld2_K _
    · rw [hm1]; simp [sc2Ans]
    · show ((rowSwitchDR _ _ sig ⟨Pw + 2288 + 112 * 2 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTD hRD.1 (by simp only [wireLanesU_20]; omega) _ _ hrD, hσ, hτD]
    · exact rowNuOk_of hS hz ho hTD hRD.1 hND.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 4040 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTY hRY.1 (by simp only [wireLanesU_20]; omega) _ _ hrY, hσ, hτY]
    · exact rowNuOk_of hS hz ho hTY hRY.1 hNY.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 6128 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTM hRM.1 (by simp only [wireLanesU_20]; omega) _ _ hrM, hσ, hτM]
    · exact rowNuOk_of hS hz ho hTM hRM.1 hNM.1
    · exact (mapB_add_vs (by rw [Cell.val_E, hz]) _ _ hME.1).trans (by rw [hmbv, selectorPoint_bits])
  · rw [← hfo]
    exact hmbv.trans (selectorPoint_bits _ _).symm

end FrontU
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm DM Lvm.E2T Lvm.E2U

private theorem bind_runU {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runU {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl
private theorem skip_runU (n : Nat) (sig : ByteArray) (s : RS) :
    skip n sig s = ((), { s with msg := s.msg + n }) := (skip_run' n sig s).trans rfl
private theorem read_runU (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) :=
  (read_run' sig s).trans rfl
private theorem stRunU {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

theorem core_of_phasesU (p pT : Params) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P1 P2 P3 : Nat} {pin : BlockClaim} {acc : Acc} {ti : List FItem}
    {evals : List (List FE × List FE)} {tp : TapeU RowZ}
    (hb : pos (RS.startH (headerBytesP p)) + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (dTypedTG pT N (m3G N p) (pubG vk c sig) (typedItemsND N p)) sig P1 P2 (acc, ti, evals))
    (htape : PhaseAt (tapeUDG rowSwitchDR p (pubG vk c sig).s (pubG vk c sig).n) sig P2 P3 tp)
    (hopen : ∀ s : RS, pos s = P3 → s.ok = true →
      let o := dOpenF p (TypedV.smallT p (pubG vk c sig)) pin
        ((ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals ++ frontItemsU rowAccR p (pubG vk c sig) tp).flatMap
          FItem.flat) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, decideProgUG p pT N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧ s₉.ok = true ∧
      s₉.ent = sig.size ∧ s₉.msg = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : RS, RS.startH (headerBytesP p) = s₀ := ⟨_, rfl⟩
  have h₀ : s₀.ok = true := by rw [← hs₀]; rfl
  rw [hs₀] at hb ⊢
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = { s₀ with msg := s₀.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← hb, hs1]; simp only [pos]; omega
  obtain ⟨a1, a2, a3⟩ := hpin s1 e1 (by rw [hs1]; exact h₀)
  generalize hA : pinD p.nuMain sig s1 = AA at a1 a2 a3
  obtain ⟨av, s2⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨b1, b2, b3⟩ := htyped s2 a3 a2
  generalize hB : dTypedTG pT N (m3G N p) (pubG vk c sig) (typedItemsND N p) sig s2 = BB at b1 b2 b3
  obtain ⟨bv, s3⟩ := BB
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s3 b3 b2
  generalize hC : tapeUDG rowSwitchDR p (pubG vk c sig).s (pubG vk c sig).n sig s3 = CC at c1 c2 c3
  obtain ⟨cv, s4⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨o1, o2, o3⟩ := hopen s4 c3 c2
  rw [← dOpenFFI_eq] at o1 o2 o3
  generalize hO : dOpenFFI p (TypedV.smallT p (pubG vk c sig)) pin (ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals)
    (frontItemsU rowAccR p (pubG vk c sig) tp) sig s4 = OO at o1 o2 o3
  obtain ⟨ov, s5⟩ := OO
  simp only at o1 o2 o3
  refine ⟨s5, ?_, o1, o2, o3⟩
  unfold decideProgUG
  simp only [bind_runU, read_runU, skip_runU, pure_runU]
  rw [← hs1, hA]
  simp only
  rw [hB]
  simp only
  rw [hC]
  simp only
  rw [hO]

/-- **`decideFUG` accepts** when its run (from the cursor after S2GU's header) ends accepting with the accumulator
`acc` and `Φ_Q` at `E2` holds at it. -/
theorem decideFUG_of (p pT : Params) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, decideProgUG p pT N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phiT (acc.pt.map Lvm.e2OfFE) = Lvm.e2OfFE acc.y) :
    decideFUG p pT N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  -- `delta` and a non-`rfl` `StateT.run` step (as `decideFGX_of`): `unfold` and the `rfl` lemma `StateT.run` left the
  -- kernel a check that ran `decideProgUG` symbolically
  have eD : @decideFUG = @decideFUG := rfl
  conv at eD => rhs; delta decideFUG
  rw [eD]
  beta_reduce
  rw [DM.runOnH, stRunU, h1]
  simp only [h2, h3, h4, hphi, beq_self_eq_true, Bool.and_self]

/-- `dMiniT` reads only the bus depth, the leaf reads, the table rounds and the record's `busFinal` and tables
(`Lvm.VEq.dMiniT_congr`'s copy). -/
theorem dMiniT_congrU (p p' : Params) (m m' : M3) (tabs : List M3.Tab) (pub : Pub) (h1 : p.busDepth = p'.busDepth)
    (h2 : p.leafdecReads = p'.leafdecReads) (h3 : p.tableRounds = p'.tableRounds) (hb : m.busFinal = m'.busFinal)
    (ht : m.tables = m'.tables) : TypedV.dMiniT p m tabs pub = TypedV.dMiniT p' m' tabs pub := by
  unfold TypedV.dMiniT
  rw [h1, h2, h3, hb, ht]

end Lvm.Har
end

-- ===== from `LvmS2GUGood` =====

section
set_option autoImplicit false
namespace Lvm.E2U
open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **The S2GU trace's sponge blocks** (`ref/utape.py --occ 46`: 3,961). -/
abbrev spongeBlocksGU : ℕ := 3961

/-- **The sponge rows that continue a sponge** at S2GU: the trace rows `1 … B − 1` and rows 1–31 of the WOTS key
leaf (`ks_split + 400 …`). -/
def contRowsU : List ℕ :=
  (List.range (spongeBlocksGU - 1)).map (· + 1) ++ (List.range 31).map (ksSplit P20 + 399 + 1 + ·)

/-- **UTAPE-STMT 10** (owner L): the literal is the S2GU trace's sponge-block count (decided). -/
theorem spongeBlocksGU_eq : spongeBlocks P20U = spongeBlocksGU := sizes_P20U.1.2.2.2.2.1

/-- **UTAPE-STMT 11** (owner L): the wire's `cont` intervals are the continuation rows. -/
theorem contU_iff (j : ℕ) : contU j = decide (j ∈ contRowsU) := by
  have hk : ksSplit P20 = 7680 := Lvm.ksSplit_P20
  have hm : j ∈ contRowsU ↔ (1 ≤ j ∧ j ≤ 3960) ∨ (8080 ≤ j ∧ j ≤ 8110) := by
    simp only [contRowsU, spongeBlocksGU, List.mem_append, List.mem_map, List.mem_range, hk]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> (clear * - ha; omega)
    · rintro (h | h)
      · exact Or.inl ⟨j - 1, by (clear * - h; omega), by (clear * - h; omega)⟩
      · exact Or.inr ⟨j - 8080, by (clear * - h; omega), by (clear * - h; omega)⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hm]
  simp only [contU, contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **The Keccak half of a good pair at S2GU** (`GkB` at `b = 3,960`, RE-FREEZE RF-2). -/
def GkU (x : List UInt8) (p : Column CMain.nu20 × Column 19) : Prop := GkB 3960 x p

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **UTAPE-STMT 12** (owner L): **the sponge half is a sponge table** (`spongeRel_of_tape`'s instance at `w = 20`,
`hs = 13`, `cont = contU`; whence K2-LS's `traceDigest_of_KS`, `row_perm`, `oneRow_perm`, `wots*_of_KS`). -/
theorem spongeRel_of_GkU {x : List UInt8} {p : Column CMain.nu20 × Column 19} (hG : GkU x p) :
    SpongeRel 13 (ksVirt 13 (YqU p.1) (MqU p.1) contU) (YqU p.1) (MqU p.1) contU where
  out i hi l hl := by
    rw [YqU, hG.2 i hi l hl, tapeInB, tapeIn, if_neg (by (clear * -; omega)), if_pos (by (clear * - hi; omega)),
      Nat.add_sub_cancel_left]
    rfl
  link i hi l hl := by
    rw [ksVirt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 13), Nat.div_eq_of_lt hi, zero_add]
  cont0 := by decide

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- The trace rows continue a sponge. -/
theorem contU_of {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 3960) : contU i = true := by
  simp only [contU, contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl ⟨h1, h2⟩

/-- **UTAPE-STMT 13** (owner L): **the sponge half outputs the child's trace digest** at row `B − 1`
(`traceDigest_of_goodKP`'s port: the stream's lane `17 i + l` is message lane `l` of row `i`, read from `qm`'s stream
block, which is `qr`). -/
theorem traceDigest_of_GkU {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GkU x (qm, qr)) (hS : SBlkU qm qr) (hL : LaneLink P20U (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P20U)) :
    Lvm.KSponge.stDigest (yState (YqU qm) (spongeBlocks P20U - 1)) =
      traceDigest (decode P20U (wsOf (Lvm.X.laneOf (wOfCol qr)))) := by
  have H := spongeRel_of_GkU hG
  have hS' := stream_of_laneLink Lvm.E2Q.streamOk_P20U hL
  have hsz : hashedLen P20U ≤ (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).length := by
    rw [wordsBytes_length]; exact hL.size
  have hsb : spongeBlocks P20U = Lvm.KSponge.nBlk (hashedLen P20U) := by
    rw [sizes_P20U.1.2.2.2.2.1, sizes_P20U.1.2.2.1]; rfl
  have hB : spongeBlocks P20U ≤ 7680 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have hin : ∀ i, 0 < i → i < Lvm.KSponge.nBlk (hashedLen P20U) → contU i = true :=
    fun i h1 h2 => contU_of h1 (by rw [← hsb, sizes_P20U.1.2.2.2.2.1] at h2; omega)
  rw [hsb] at hB ⊢
  -- `L` opaque (`obtain`, not `generalize`, whose `L` is substituted back): the `omega`s below then do not make the
  -- kernel compute `hashedLen P20U` (GOLF3: 3.8 M heartbeats)
  obtain ⟨L, hL⟩ : ∃ L, hashedLen P20U = L := ⟨_, rfl⟩
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

end Lvm.E2U
end

section
set_option autoImplicit false
namespace Lvm.E2U
open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **UTAPE-STMT 14** (owner L): **Q_sig's `KS` hypothesis at S2GU** (`sigKSin_of_goodKP`'s port: the `X` rows are
the stream block's rows from `ks_split`, the digest cells the `Y` block's lanes 0–3). -/
theorem sigKSin_of_GkU {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} {I : SigIn} {v : ℕ → FK}
    (hG : GkU x (qm, qr))
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 430 + t) l))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 447) l))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 448) l)) :
    SigKSin I v := by
  have H := spongeRel_of_GkU hG
  have hrow : ∀ r < 449, ksSplit P20 + r < 2 ^ 13 := fun r hr => by rw [ksSplit_P20]; omega
  have hcF : ∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) →
      contU (ksSplit P20 + r) = false := fun r h1 h2 => by
    simp only [contU, contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff, Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, ksSplit_P20]; omega
  have hcT : ∀ r, 400 ≤ r → r ≤ 430 → contU (ksSplit P20 + r) = true := fun r h1 h2 => by
    simp only [contU, contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq, ksSplit_P20]; omega
  -- a one-block row
  have one : ∀ r < 449, ¬ (400 ≤ r ∧ r ≤ 430) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l)) →
      OneHash v (fun l => I.xs + 17 * r + l) y := fun r hr hn y hy =>
    ⟨yState (YqU qm) (ksSplit P20 + r), by
      rw [xorMsg_cellsU (qm := qm) (r := r) (fun l hl => hx r hr l hl)]
      exact oneRow_perm 13 _ (YqU qm) (MqU qm) _ H (hrow r hr) (hcF r hr hn),
      digAt_of_cells hy⟩
  refine ⟨fun r hr => one r (by (clear * - hr; omega)) (by (clear * - hr; omega)) _ (hys r hr), ?_, fun t ht => ?_,
    one 447 (by (clear * -; omega)) (by (clear * -; omega)) _ hyls, one 448 (by (clear * -; omega)) (by (clear * -; omega)) _ hyns⟩
  · -- the key leaf: rows `S + 399 … S + 430`
    refine ⟨fun u => prevState (YqU qm) contU (ksSplit P20 + (399 + u)),
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
end

-- ===== from `LvmE2QNodeU` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol

/-- **The input map's bundles from the check at S2GU** (`inMap_of_okGL`'s twin on `inMapBGL cfgU20`). -/
theorem inMap_of_okGLU (B nPub : ℕ) (N : TNat) (pl : Lvm.Pub → List FK) (Q : Program) (tl : Typed.Lay)
    (hlay : tl.Ok Q) (pub : Lvm.Pub) (qm : Column CMain.nu20) (qr : Column 19)
    (hS : SBlkS CMain.sOffU20 qm qr) (hok : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (h : inMapBGL B nPub cfgU20 Q tl N = true) :
    let M := memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)
    CellsAt M.k lay26 qm qr 17 14 (Lvm.QAsm.lay cfgU20).sb true (fun l ↦ l * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 1 10 (sigIn cfgU20).sg true (fun _ ↦ 17 * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 17 9 (sigIn cfgU20).xs false (fun l ↦ xCol P20U l) ∧
      CellsAt M.k lay26 qm qr 4 9 (sigIn cfgU20).ys false (fun l ↦ ksYCol P20U l + ksSplit P20U) ∧
      CellsAt M.k lay26 qm qr 4 0 (sigIn cfgU20).md false (fun l ↦ ksYCol P20U l + (B - 1)) ∧
      ∀ j < nPub, M.k ((sigIn cfgU20).flag + j) = (pl pub).getD j 0 := by
  intro M
  have hs : (layout0 cfgU20.p).s = CMain.sOffU20 := by rw [show cfgU20.p = P20U from rfl, layout0_P20U]
  simp only [inMapBGL, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hSt, hG⟩, hX⟩, hY⟩, hMd⟩, hP⟩ := h
  rw [hs] at hSt hG hX hY hMd hP
  have f1 : ∀ j < 17 * 2 ^ 14, j % 17 * 2 ^ 14 + j / 17 < 2 ^ 19 := fun j hj ↦ by omega
  have f2 : ∀ j < 1 * 2 ^ 10, 17 * 2 ^ 14 + j / 1 < 2 ^ 19 := fun j hj ↦ by omega
  refine ⟨bundleS_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ f1
      (fun l r ↦ by rw [show cfgU20.p = P20U from rfl, sCol_P20U, Nat.add_assoc]) hSt,
    bundleS_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ f2
      (fun l r ↦ by rw [show cfgU20.p = P20U from rfl, sCol_P20U, Nat.add_assoc]) hG,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ (fun l r ↦ rfl) hX,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ (fun l r ↦ rfl) hY,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ (fun l r ↦ rfl) hMd,
    fun j hj ↦ ?_⟩
  exact cell_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay pub qm qr hS hok hl hσ
    (List.all_eq_true.mp hP j (List.mem_range.mpr hj))

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol

/-- **The input map on a pair's memory at S2GU** (`inMapTGL`'s twin: `InMapMBU`, the stream block at
`CMain.sOffU20`). -/
theorem inMapTGLU (B nPub : ℕ) (N : TNat) (pl : Lvm.Pub → List FK) (Q : Program) (tl : Typed.Lay)
    (pb : List UInt8 → Lvm.Pub) (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (hin : inMapBGL B nPub cfgU20 Q tl N = true) (hB : B ≤ 2 ^ 13)
    (hm : 2 ^ (lay cfgU20).m ≤ 17 * 2 ^ 14) (hn : 615 ≤ nPub) (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} {x : List UInt8} (qm : Column CMain.nu20) (qr : Column 19)
    (hSB : SBlkS CMain.sOffU20 qm qr) (hok : okS vk c x = true) (hb1 : (hdrOf x).b = 1) :
    InMapMBU B nPub (lay cfgU20) (sigIn cfgU20) (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)) vk x qm qr := by
  obtain ⟨hS, hG, hX, hY, hMd, hP⟩ := inMap_of_okGLU B nPub N pl Q tl hlay (pb x) qm qr hSB hreg hl hσ hin
  have hP' : ∀ j < nPub, (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn cfgU20).flag + j) =
      hdrLane x j := fun j hj ↦ (hP j hj).trans (hpub x j hj)
  have hPC : PubCells (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k x (sigIn cfgU20).flag :=
    fun j hj ↦ hP' j (lt_of_lt_of_le hj hn)
  have hy := ys_vU hY rfl rfl rfl
  exact ⟨fun j hj ↦ stream_v hS (lt_of_lt_of_le hj hm), flag_v hPC hb1, xs_vU hX, hy.1, hy.2.1, hy.2.2.1,
    hy.2.2.2, (vk_v hPC).trans (okS_vk hok), cL_v hPC, sl_v hPC, md_vU hB hMd, sg_v hG, hd_v hS rfl, hP'⟩

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol

theorem cfgU20_rl : cfgU20.rl = 14 := rfl

/-- **`ReaddOk` on a stream-block pair's memory at S2GU** (`readdTGL`'s twin). -/
theorem readdTGLU (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) (pl : Lvm.Pub → List FK)
    (pub : Lvm.Pub) (B nPub : ℕ) (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (hchk : nodeChkBGL B nPub cfgU20 F Q tl N = true) (hc : nK cfgU20 ≤ Q.cells .K)
    {qm : Column CMain.nu20} {qr : Column 19} (hτ : ∀ t ∈ mbTOf cfgU20 F, t.τ ≤ lay26.μ)
    (hLay : LayOk lay26 (mbTOf cfgU20 F)) (hM : M3Holds (inst lay26 (mbTOf cfgU20 F) hτ) () (stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) (hlin : NonReaddHolds Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)) := by
  have hs : (layout0 cfgU20.p).s = CMain.sOffU20 := by rw [show cfgU20.p = P20U from rfl, layout0_P20U]
  have hnK : 17 * 2 ^ 14 ≤ nK cfgU20 := by decide
  simp only [nodeChkBGL, Bool.and_eq_true] at hchk
  obtain ⟨⟨hin, hrd⟩, hsd⟩ := hchk
  rw [hs] at hrd
  simp only [mbSeedsOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsd
  obtain ⟨hblk, hlen⟩ := hsd
  have hS := (inMap_of_okGLU B nPub N pl Q tl hlay pub qm qr hSB hreg hl hσ hin).1
  refine readdOk_of_chkLS sOffU20_mod sOffU20_fit cfgU20 F Q tl N pl hlay pub qm qr hSB hreg hl hσ hrd ?_ ?_ hlin
  · intro τ wa wv hp y hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    exact mbRead_seeded cfgU20 F lay26 hτ qm qr hLay hM hlen hk hy
  · intro lq hlq x' hx'
    obtain ⟨hl17, hq⟩ := hblk lq hlq
    rw [cfgU20_rl] at hq
    have hx'16 : x' < 16 := hx'
    have hj : 17 * (lq.2 + x') + lq.1 < 17 * 2 ^ 14 := by omega
    have e : (Lvm.QAsm.lay cfgU20).sb + 17 * lq.2 + lq.1 + 17 * x' =
        (Lvm.QAsm.lay cfgU20).sb + (17 * (lq.2 + x') + lq.1) := by ring
    have h16 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    refine ⟨?_, ?_⟩
    · have hsb : (Lvm.QAsm.lay cfgU20).sb = 0 := rfl
      rw [e, hsb]
      (clear * - hj hnK hc; omega)
    · have h1 := hS (17 * (lq.2 + x') + lq.1) hj
      beta_reduce at h1
      have e2 : (17 * (lq.2 + x') + lq.1) % 17 * 2 ^ 14 + (17 * (lq.2 + x') + lq.1) / 17 =
          lq.1 * 2 ^ cfgU20.rl + lq.2 + x' := by
        rw [cfgU20_rl, h16]; omega
      have hs' : Lvm.sCol cfgU20.p lq.1 + lq.2 + x' = CMain.sOffU20 + (lq.1 * 2 ^ cfgU20.rl + lq.2 + x') := by
        rw [show cfgU20.p = P20U from rfl, sCol_P20U, cfgU20_rl]
        omega
      rw [e, h1, e2, hs', comCell_SS sOffU20_fit hSB (by rw [cfgU20_rl, h16]; omega)]

/-- **Q_link's static checks at S2GU** (`qOkB` decided as `qOkF` in `LvmS2GUPlan`'s shared decision). -/
theorem hQU20 : QOk P20U (lay cfgU20) :=
  qOk_of streamOk_P20U (by rw [← qOkF_eq]; exact qOkF_P20U)

/-- S2GU's plan facts. -/
theorem planC_P20U : PlanC P20U :=
  planC_ofR passR_P20U planSt_P20U.1 (by decide) sizes_P20U.1.1 (by norm_num) sizes_P20U.1.2.2.1
    (by norm_num) (by norm_num) rfl

/-- S2GU's node statics. -/
theorem nodeStU20 : NodeStC cfgU20 :=
  ⟨streamOk_P20U, hQU20, by decide,
    by rw [show cfgU20.p = P20U from rfl, sizes_P20U.1.2.2.2.2.1]; norm_num,
    by rw [show cfgU20.p = P20U from rfl, sizes_P20U.1.2.2.2.2.1, sizes_P20U.1.2.2.1]; rfl, rfl,
    by decide, by decide, planC_P20U⟩

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol
section PairU
variable {B nPub : ℕ} {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat}
  (S : NodeGCL cfgU20 B nPub F Q tl N) (pl : Lvm.Pub → List FK) (pb : List UInt8 → Lvm.Pub)
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

theorem regsU : N.okB 23 19 = true := S.st.regs

theorem sigU : SigInSL CMain.sOffU20 N := by
  have h := S.sig
  rwa [show (layout0 cfgU20.p).s = CMain.sOffU20 by rw [show cfgU20.p = P20U from rfl, layout0_P20U]] at h

theorem hqltCU (Ti : TInst) (hTi : Ti.lay = tl) :
    ∀ y < (qltData cfgU20.p (lay cfgU20)).length,
      (memTX Ti pb x qm qr).k ((lay cfgU20).qt + y) = (qltData cfgU20.p (lay cfgU20)).getD y 0 := by
  subst hTi
  exact hqltG cfgU20 _ S.st.cst _

theorem hlinCU (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    NonReaddHolds Q (memTX (N.instL pl Q tl) pb x qm qr) :=
  nonReadd_of_wiringX Q tl _ S.st.wf S.st.twins S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW

theorem readdCU (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : LayOk lay26 N.mbT) (hM : M3Holds (inst lay26 N.mbT hτ) () (stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    ReaddOk Q (memTX (N.instL pl Q tl) pb x qm qr) := by
  have hτ' : ∀ t ∈ mbTOf cfgU20 F, t.τ ≤ lay26.μ := fun t ht ↦ hτ t (by rw [S.mb]; exact ht)
  have hL' : LayOk lay26 (mbTOf cfgU20 F) := by rwa [S.mb] at hL
  exact readdTGLU F Q tl N pl (pb x) B nPub S.st.hlay (regsU S) S.st.hlayOk (sigU S) S.chk S.cells hτ' hL'
    (m3Holds_eq S.mb hM) hSB (hlinCU S pl pb hone hW)

theorem hholdsCU (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : LayOk lay26 N.mbT) (hM : M3Holds (inst lay26 N.mbT hτ) () (stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    (N.instL pl Q tl).Q.Holds (memTX (N.instL pl Q tl) pb x qm qr) ∧
      (N.instL pl Q tl).Q.Asserts (memTX (N.instL pl Q tl) pb x qm qr) :=
  holds_memTX S.st.wf S.st.twins S.st.hlay hone hW (readdCU S pl pb hone hW hτ hL hM hSB)

theorem hmapCU (hB : B ≤ 2 ^ 13) (hn : 615 ≤ nPub) (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    InMapMBU B nPub (lay cfgU20) (sigIn cfgU20) (memTX (N.instL pl Q tl) pb x qm qr) vk x qm qr := by
  have hchk := S.chk
  simp only [nodeChkBGL, Bool.and_eq_true] at hchk
  exact inMapTGLU _ _ N pl Q tl pb S.st.hlay (regsU S) S.st.hlayOk (sigU S) hchk.1.1 hB (by decide) hn hpub qm qr
    hSB hok hb

theorem outsOnCU (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    OutsOnC cfgU20 (memTX (N.instL pl Q tl) pb x qm qr).k := by
  obtain ⟨bw, haux⟩ := S.aux
  exact outsOnC_of cfgU20 tl _ bw haux fun hk hj hr ↦
    auxRow_of_wiringX Q tl _ S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW hk hj hr

set_option maxRecDepth 100000 in
theorem hposCU (hB : B ≤ 2 ^ 13) (hn : 615 ≤ nPub)
    (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) {vk c : RecursionFast.Digest}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hSB : SBlkS CMain.sOffU20 qm qr) :
    ∀ k < (opens cfgU20.p).length, ∀ j < ((opens cfgU20.p).getD k default).L.t,
      ∀ z < ((opens cfgU20.p).getD k default).L.height,
      (memTX (N.instL pl Q tl) pb x qm qr).k
          (bitBase cfgU20.p (lay cfgU20) k + ((opens cfgU20.p).getD k default).L.height * j + z) =
        if ansBit cfgU20.p (wsC qr) (((opens cfgU20.p).getD k default).pe + j / 8)
          (j % 8 * ((opens cfgU20.p).getD k default).L.height + z) then 1 else 0 :=
  hposTC (C := cfgU20) streamOk_P20U hQU20
    (outsOnCU S pl pb hone hW) (hmapCU S pl pb hB hn hpub hok hb hSB).stream

theorem hbitsCU (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    SigBits (sigIn cfgU20) (qsig (sigIn cfgU20) (p1P (lay cfgU20) (nK cfgU20) 0 P20U)).1
      (memTX (N.instL pl Q tl) pb x qm qr).k :=
  sigBits_ofC cfgU20 (outsOnCU S pl pb hone hW) ⟨by decide, by decide⟩

end PairU
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol

/-- **`NodeSound` at S2GU from the parts** (`nodeSoundC`'s twin at `cfgU20`: the Keccak half `GkU` with the
boundary claims `BndS` and the stream block at `CMain.sOffU20`; Q_sig's `KS` facts from `sigKSin_of_GkU`, the trace
digest from `traceDigest_of_GkU`; the input map `InMapMBU`). -/
theorem nodeSoundCU (VS : SProg) (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (hVS : ∀ vk c π, VS vk c π = if parseOk P20U vk c π then drive P20U π (D vk c) else .ret false)
    (nPub : ℕ) (pb : List UInt8 → Lvm.Pub)
    (vk : RecursionFast.Digest) (Ti : TInst) (qa : BM Unit) (G : GoodRel)
    (hQ : Ti.Q = toProgram (nK cfgU20) 0 (qprogP P20U (lay cfgU20) (sigIn cfgU20) qa))
    (hinj : GInj (max (Ti.Q.cells .K) (Ti.Q.cells .E)))
    (hGK : ∀ c x qm qr, okS vk c x = true → G x qm qr →
      Lvm.E2U.GkU x (qm, qr) ∧ BndS x qm ∧ Lvm.E2U.SBlkU qm qr)
    (hholds : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      Ti.Q.Holds (memTX Ti pb x qm qr) ∧ Ti.Q.Asserts (memTX Ti pb x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMBU (spongeBlocks P20U) nPub (lay cfgU20) (sigIn cfgU20) (memTX Ti pb x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ y < (qltData cfgU20.p (lay cfgU20)).length,
        (memTX Ti pb x qm qr).k ((lay cfgU20).qt + y) = (qltData cfgU20.p (lay cfgU20)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ k < (opens cfgU20.p).length, ∀ j < ((opens cfgU20.p).getD k default).L.t,
        ∀ z < ((opens cfgU20.p).getD k default).L.height,
        (memTX Ti pb x qm qr).k (bitBase cfgU20.p (lay cfgU20) k + ((opens cfgU20.p).getD k default).L.height * j + z) =
          if ansBit cfgU20.p (wsC qr) (((opens cfgU20.p).getD k default).pe + j / 8)
            (j % 8 * ((opens cfgU20.p).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      SigBits (sigIn cfgU20) (qsig (sigIn cfgU20) (p1P (lay cfgU20) (nK cfgU20) 0 cfgU20.p)).1 (memTX Ti pb x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMBU (spongeBlocks P20U) nPub (lay cfgU20) (sigIn cfgU20) (memTX Ti pb x qm qr) vk x qm qr →
      LaneLink P20U (wsC qr) → LinkOk P20U (decode P20U (wsC qr)) →
      Ok (ctxOf Ti.Q) (memTX Ti pb x qm qr) qa (p2P (lay cfgU20) (sigIn cfgU20) (nK cfgU20) 0 P20U) →
      D vk (hdrOf x).cL (traceBytesB (decode P20U (wsC qr))) = true) :
    NodeSound VS vk G (childSP P20U) := by
  have St := nodeStU20
  refine nodeSound_of (fun c x qm qr hok hG ↦ ?_) fun c x qm qr hok hb hG ↦ ?_
  · obtain ⟨hK, hBn, -⟩ := hGK c x qm qr hok hG
    exact Lvm.KG.chain_of_tape (okS_n hok).1 (okS_n hok).2 ⟨hK.1, hBn (okS_n hok).2⟩
  have hK := hGK c x qm qr hok hG
  obtain ⟨hH, hA⟩ := hholds c x qm qr hok hb hG
  have hinj' := hinj
  rw [hQ] at hH hA hinj'
  have P := parts_of_holdsP hH hA
  have mp := hmap c x qm qr hok hb hG
  have hwsl : 2 ^ (lay cfgU20).m ≤ (wsC qr).length := by
    rw [wsC, wsOf, List.length_map, List.length_range]; exact St.wsl
  have hqin : QIn cfgU20.p (lay cfgU20) (wsC qr) (memTX Ti pb x qm qr) :=
    ⟨mp.flag, mp.stream, hqlt c x qm qr hok hb hG, hpos c x qm qr hok hb hG⟩
  have hN : (ctxOf (toProgram (nK cfgU20) 0 (qprogP P20U (lay cfgU20) (sigIn cfgU20) qa))).cells .K ≤
      max ((toProgram (nK cfgU20) 0 (qprogP P20U (lay cfgU20) (sigIn cfgU20) qa)).cells .K)
        ((toProgram (nK cfgU20) 0 (qprogP P20U (lay cfgU20) (sigIn cfgU20) qa)).cells .E) := by
    rw [NS.ctxOf_cells]; exact le_max_left _ _
  have hNs : (lay cfgU20).sb + 2 ^ (lay cfgU20).m ≤
      max ((toProgram (nK cfgU20) 0 (qprogP P20U (lay cfgU20) (sigIn cfgU20) qa)).cells .K)
        ((toProgram (nK cfgU20) 0 (qprogP P20U (lay cfgU20) (sigIn cfgU20) qa)).cells .E) :=
    le_trans St.ns (le_trans (nK_le_cells _ _ _) (le_max_left _ _))
  obtain ⟨hLL, hpad⟩ := qlink_sound St.stream St.qok hqin hwsl hinj' hN hNs P.1.1 P.1.2
  have hlink := linkOk_of_laneLink St.stream hLL
  have hks := Lvm.E2U.sigKSin_of_GkU hK.1 mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨hsig, hchild⟩ := qsig_sound_in (by rw [St.ln]; omega) P.2.1 mp.flag hks
    (hbits c x qm qr hok hb hG) fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
  have hmd := (digAt_of_cells mp.md).trans (Lvm.E2U.traceDigest_of_GkU hK.1 hK.2.2 hLL hpad)
  have har := harith c x qm qr hok hb hG mp hLL hlink (by rw [hQ]; exact P.2.2)
  exact accV_childC P20U VS D hVS St.plan qr hlink har hsig hchild St.ln mp.vk mp.cL mp.sl hmd mp.sg mp.hd
    (okS_sig hok hb)

end Lvm.E2Q
end

-- ===== from `LvmE2URef` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

theorem mainOod_P20U : P20U.mainOod = true := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)
section Ref
variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's S2GU tape on the data** refines `tapeProgU`, its value through `mapTU`. -/
theorem refW_tapeUDG (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUDG rowSwitchDR P20U s n) (tapeProgU d n) (fun t o ↦ TapeURelW (mapTU t) o)
      (i + wTapeU.length) :=
  RefAtW.of_map (by rw [tapeUDG_R]; exact refW_tapeUD s d hs n hw)

end Ref
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

theorem retD_wireUDG (p : Params) (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (ColsW p) (wireUDG rowSwitchDR p s n claim) := by
  unfold wireUDG
  exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotDFW _ _ _ _ _ _).bind fun _ hy ↦ (retD_slotDFW _ _ _ _ _ _).bind fun _ hm ↦ RetD.pure ⟨hy, hm⟩

/-- **What V_S's S2GU tape on the data returns**: the closures' shape (`TapeShapeU`) and the block rows' points. -/
theorem retD_tapeUDG (s : List FK) (n : ℕ) :
    RetD (fun t : TapeU RowZ ↦ TapeShapeU (mapTU t) ∧ ColsW P20U t.wo) (tapeUDG rowSwitchDR P20U s n) := by
  refine RetD.and (RetD.of_map (f := mapTU) ?_) ?_
  · rw [tapeUDG_R]; exact retD_tapeUD s n
  · unfold tapeUDG
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUDG _ _ _ _).bind fun _ h ↦ RetD.pure h

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

theorem monoD_dTypedTG {α : Type} (p : Params) (N : TNatT) (m : M3) (pub : Pub)
    (mk : List FE2 → List FE2 → List FE2 → FE2 → α) : MonoD (dTypedTG p N m pub mk) :=
  E2T.monoD_dZeroT.bind fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- The typed phases' claims are their items' flattening. -/
theorem dTypedTG_items (pT p : Params) (N : TNatT) (m : M3) (pub : Pub) :
    dTypedTG pT N m pub (typedClaimsND N p) =
      (fun r ↦ (r.1, r.2.1.flatMap FItem.flat, r.2.2)) <$> dTypedTG pT N m pub (typedItemsND N p) := by
  unfold dTypedTG
  simp only [map_bind, map_pure, typedItemsND_flat]

/-- The typed phases on S2GU's mini-bus instance are those on the record's (`dMiniT` reads neither `PUB`'s check
nor the stage). -/
theorem dTypedTG_m3GU {α : Type} (N : TNatT) (pub : Pub) (mk : List FE2 → List FE2 → List FE2 → FE2 → α) :
    dTypedTG P20 N (m3G N P20U) pub mk = dTypedTG P20 N (N.toN.m3 P20) pub mk := by
  unfold dTypedTG
  rw [dMiniT_congr P20 P20 (m3G N P20U) (N.toN.m3 P20) N.mbT pub rfl rfl rfl rfl rfl]

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)
section Ref
variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's typed phases at S2GU** (items on `P20U`'s layout) refine `typedProgT`, their items through `FItem.flat`
(`ref_dTypedTO` at `P20U`). -/
theorem ref_dTypedTU (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = Typed.phiVarsT) {i : ℕ} (hw : WAt rw i wTypedT) :
    RefAtWP cap occ shp rw sig i (dTypedTG P20 N (m3G N P20U) pub (typedItemsND N P20U))
      (typedProgT (N.inst Q lay) pub) (fun r a ↦ TRelTTO P20U N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedT.length) := by
  have h := ref_dTypedTO (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) P20U N Q lay H pub hacc hw
  rw [dTypedTG_items, ← dTypedTG_m3GU N pub] at h
  have h' := RefAtWP.of_map h
  exact h'

end Ref
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **The pinned middle phases at S2GU as one chain**: the root, the pin, the typed phases, the merged tape,
`C_main`'s opening on the pin's claim and `ordMk 4` of `assembleU₂`'s relocated pair. -/
theorem psU_eq (Ti : Typed.TInst) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU Ti))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        typedProgT Ti (pubXT x) >>= fun a ↦ tapeProgU (hdX x).s (pubX x).n >>= fun k ↦
          LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
            Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) >>= fun _ ↦
              pure true := by
  unfold Lvm.ASM.PSWithM Lvm.E2F.midP Lvm.ASM.midMk midGU midGB tapeProgU
  rw [commitRootUd_mainT]
  simp only [bind_assoc, ret_bindM, pure_bind]

theorem monoD_tapeUD (s : List FK) (n : ℕ) : MonoD (tapeUD s n) :=
  monoD_sepE2.bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _

theorem monoD_tapeUDG (s : List FK) (n : ℕ) : MonoD (tapeUDG rowSwitchDR P20U s n) :=
  MonoD.of_map (f := mapTU) (by rw [tapeUDG_R]; exact monoD_tapeUD s n)

theorem monoD_dOpenFFI (p : Params) (s : Bool) (pin : BlockClaim) (ti items : List FItem) :
    MonoD (dOpenFFI p s pin ti items) := by
  rw [dOpenFFI_eq]; exact monoD_dOpenF _ _ _ _

theorem skip_P20U : nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap = 32 * 2 ^ capS 19 64 := by decide

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **V_S's read widths at S2GU** in the decision's order: the pin's read, the typed phases', the tape's, the
opening's (`asO`). -/
def wDecU (asO : List Atom) : List ℕ := [24] ++ wTypedT ++ wTapeU ++ widthsA asO

/-- **V_S's S2GU decision refines the pinned S2GU middle phases** at `occOfU`, with read widths `wDecU asO` from read
`0`, under the promise that its value passes `Φ_Q` at `E2`, given the claims' relation (`hcl`). -/
theorem ref_decideGU (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (vk c : RecursionFast.Digest) (x : List UInt8) {sig : ByteArray} (hpub : pubG vk c sig = pubXT x)
    (asO : List Atom) {rw : ℕ → ℕ}
    (hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl) asO pp fun _ _ ↦ True)
    (h24O : ∀ w ∈ widthsA asO, w = 24) (hw : WAt rw 0 (wDecU asO))
    (hacc : (pubXT x).accIn.pt.length = Typed.phiVarsT) (hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s)
    (hcl : ∀ t a', TRelTTO P20U N Q lay t a' → ∀ (tp : TapeVU) (k : TapeOutU), TapeURelW tp k → TapeShapeU tp →
      (t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).all
        (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
          (((t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).filter
            (·.1 == .main)).map (·.2)))
        (Lvm.ASM.ordMk 4 ((assembleU₂ x a' k).1.map (relocU20 x)) (assembleU₂ x a' k).2)) :
    RefAtPW capS occOfU shpS rw sig 0 (decideProgUG P20U P20 N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecU asO).length := by
  rw [wDecU, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw0, hwT⟩, hwF⟩, hwO⟩ := hw
  replace hwF := WAt.idx_eq hwF (j := 0 + [24].length + wTypedT.length)
    (by simp only [List.length_append]; omega)
  replace hwO := WAt.idx_eq hwO (j := 0 + [24].length + wTypedT.length + wTapeU.length)
    (by simp only [List.length_append]; omega)
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.toT.sc_eq
  rw [psU_eq]
  unfold decideProgUG
  refine RefAtPW.read_left ?_
  dsimp only
  rw [hpub]
  -- the cap
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    ((refW_skip (n := nodeBytes * 2 ^ (P20U.level ⟨.main, 0⟩).cap) (ht := 19) (w := 64) skip_P20U).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro - - - -
  -- the pin
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ ((refW_pinD (WAt.cons.mp hw0).1).toPW _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro pin za ⟨z, a, rfl, rfl⟩ -
  -- the typed phases
  have hT0 : RefAtPW capS occOfU shpS rw sig (0 + [24].length) (dTypedTG P20 N (m3G N P20U) (pubXT x) (typedItemsND N P20U))
      (typedProgT (N.inst Q lay) (pubXT x)) (fun r a ↦ TRelTTO P20U N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) (0 + [24].length + wTypedT.length) :=
    ref_dTypedTU N Q lay H (pubXT x) hacc hwT
  refine RefAtPW.bind (Q := fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) ?_ hT0 ?_ ?_
  rotate_left
  · intro b s hs'
    refine promise_of_retDG (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) ?_ hs'
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.pure rfl
  rintro ⟨acc, ti, evals⟩ a' hT -
  dsimp only
  -- the tape
  rw [show (pubXT x).n = (pubX x).n from rfl]
  have hTp1 := refW_tapeUDG (cap := capS) (occ := occOfU) (shp := shpS) (sig := sig) (pubXT x).s (hdX x).s hs
    (pubX x).n hwF
  have hTp2 := hTp1.retD (retD_tapeUDG (pubXT x).s (pubX x).n)
  have hTp := hTp2.toPW (fun _ ↦ True)
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ hTp (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro tp k ⟨hk, hsh, hcols⟩ -
  -- the opening, on the closures' claims
  have hsh' := hsh
  obtain ⟨-, hl20, -, -, hy5, -, hm5, -⟩ := hsh'
  have e : dOpenFFI P20U (TypedV.smallT P20U (pubXT x)) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals)
      (frontItemsU rowAccR P20U (pubXT x) tp) =
      dOpenF P20U (Shape.small x) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti.flatMap FItem.flat ++ Shape.zeroTails (M3.tableClaimsR N.mbT evals) ++
        frontClaimsUD P20U (pubXT x) (mapTU tp)) := by
    rw [smallT_P20U, dOpenFFI_eq]
    refine dOpenF_congr _ _ _ ?_
    rw [List.flatMap_append, List.flatMap_append, tabItemsR_flat, hsc, List.map_append, List.map_append,
      List.map_append, List.map_append, frontU_stk _ _ tp hcols hl20 hy5 hm5]
  rw [e]
  have hO := RefAtP.toPW (ref_dOpenFO (sig := sig) P20U rfl rfl rfl corrMainU _ _ (screl_pinW z a) (Shape.small x) _ _
    (hcl (acc, ti.flatMap FItem.flat, evals) a' hT (mapTU tp) k hk hsh))
    (cap' := capS) (shp' := shpS) (idx := idxS) (hFO _) hwO h24O
  refine RefAtPW.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) hO (fun _ _ _ ↦ trivial) ?_
  rintro - - - -
  exact ((RefAtW.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) rfl).idx
    (by simp only [wDecU, List.length_append, List.length_singleton])).toPW _
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_pinD _) | (with_reducible exact monoD_dTypedTG _ _ _ _ _)
    | (with_reducible exact monoD_tapeUDG _ _) | (with_reducible exact monoD_dOpenFFI _ _ _ _ _)
    | (with_reducible exact monoD_dOpenF _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **V_S's claim list at S2GU (after the pin) against `ordMk 4` of `assembleU₂`'s relocated pair** (both shapes):
where V_S's `require` held (every claim on `C_main`), the typed claims (`TRelTTO P20U`: the relayout's and `σ′`'s
halves relocated onto S2GU's `S`, the committed block's and `KS`'s halves), the mini-bus's and the front's
(`front_relU`), on the statement's shape's stack, are the spec's in V_S's order. -/
theorem claimsU_rel (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (x : List UInt8)
    (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims)
    (hT : TRelTTO P20U N Q lay t a) (tp : TapeVU) (k : TapeOutU) (hk : TapeURelW tp k) (hsh : TapeShapeU tp)
    (hall : (t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).all
      (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
        (((t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsUD P20U (pubXT x) tp).filter
          (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, -, -, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.toT.fits
  have hall' : ∀ e ∈ t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++
      frontClaimsUD P20U (pubXT x) tp, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he]]
  have hok := H.ok
  rw [nuMain_P20] at hok
  have hS : (layout0 P20U).s = CMain.sOffU20 := by rw [layout0_P20U]
  -- the typed claims
  have hrelay := vrel_splitMAt (s := Shape.small x) CMain.sOffU20 [(1, ⟨P20U.nuRec, (layout0 P20U).s⟩, rr)]
    (by simpa using offOK_relayU) vR [(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)]
    (by simp [E2V.partE, shiftS2At, hS, Lvm.FE2.toE2_one]; rfl)
    (by simp only [List.mem_singleton, forall_eq]; exact relocOKAt_relayU _) (toE2 vR) rfl
  have hsg := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .sigma (.inr (.inr rfl)) ry hry
    (rv.getD 2 0)
  rw [regClaimT_relocSAt N Q lay 23 P20.nuRec hok H.hlay CMain.sOffU20 (by decide) (hS ▸ hσ)] at hsg
  have hcom := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .com (.inl rfl) ry hry (rv.getD 0 0)
  have hks := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .ks (.inr (.inl rfl)) ry hry
    (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      ((E2V.splitE2 19 ⟨[(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)], toE2 vR⟩).map
          (fun c ↦ relocSAt CMain.sOffU20 c.onStack) ++
        (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map toE2) (toE2 (rv.getD 2 0))).map
          (relocSAt CMain.sOffU20) ++
        regClaimT (N.inst Q lay) .com N.toN.off (ry.map toE2) (toE2 (rv.getD 0 0)) ++
        regClaimT (N.inst Q lay) .ks N.toN.off (ry.map toE2) (toE2 (rv.getD 3 0))) := by
    rw [ht1]
    unfold typedClaimsND
    exact Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append hrelay hsg) hcom) hks
  -- the mini-bus's claims
  have hZrel : List.Forall₂ CRelM ((Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2)).map fun e ↦ (e.1, e.2.1))
      (tableClaimsE N.mbT (M3.claimsOfEvs N.mbT t.2.2)) := by
    rw [Shape.zeroTails, List.map_map]
    simpa [Function.comp_def] using hcl.imp fun _ _ h ↦ CRel.crelM h
  have hZm : ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main := fun e he ↦
    hall' e (List.mem_append_left _ (List.mem_append_right _ he))
  have hZt : Shape.small x = true → ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main →
      Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1 := by
    intro _ e he hm
    rw [Shape.zeroTails] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have h := Shape.table_tails N.mbT N.mbT (fun _ h ↦ h) t.2.2 hfc hfh e' he' hm
    exact ⟨h.inStack, h.tail.symm⟩
  have hZV := forall₂_crelM (s := Shape.small x) hZrel hZm hZt
  -- the front
  have hFV := front_relU (s := Shape.small x) x tp k hk hsh (fun hs ↦ of_decide_eq_true hs)
    (by simp [pubX, pubOf])
  have hV := forall₂_onStackZsF (Lk.forall₂_append (Lk.forall₂_append hTV hZV) hFV)
  -- the spec's list in V_S's order
  have hmbE := main_of_crel hcl fun e he ↦ by
    have := hZm (e.1, e.2, 0) (List.mem_map.2 ⟨e, he, rfl⟩)
    exact this
  convert hV using 1
  have hmb : (N.inst Q lay).mbT = N.mbT := rfl
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (relocU20 x) = (l.map (relocSAt CMain.sOffU20)).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold assembleU₂ typedClaimsT Typed.miniClaims
  rw [hmb, filter_main_self hmbE, filter_crec_nil hmbE]
  dsimp only
  rw [onStackZs_eq_map, hρ, ordMk_of_length 4 _ _ (by simp [E2V.splitE2, regClaimT]), ← List.map_append,
    inplM_main hmbE]
  simp only [List.map_append, List.map_map, List.append_assoc, List.append_nil, Function.comp_def, List.map_nil,
    List.nil_append, E2V.pointE2, E2T.kv_toE2_getD]
  rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **S2GU's atoms are `P20`'s** (`P20U`'s levels differ from `P20`'s in the root's row only). -/
theorem atomsOf_U (its : List Item) : atomsOf P20U its = atomsOf P20 its :=
  atomsOf_congrL P20U P20 (fun r ↦ by
    obtain ⟨c, lv⟩ := r
    cases c
    · exact withRow0_getD P20.mainLevels 46 lv
    · exact ⟨rfl, rfl⟩) its

theorem atomsOf_scheduleU : atomsOf P20U (schedule P20U) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20U (midItemsU P20U) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleU_eq _ rfl, atomsOf_append, atomsOf_append, atomsOf_append, atomsOf_nil, atomsOf_U (openMainI P20U),
    atomsOf_U (commitI P20U), show openMainI P20U = openMainI P20 from rfl,
    show commitI P20U = commitI P20 from rfl, atomsOf_commitI]

/-- **S2GU's `P_S` follows the schedule** at `P20U`: the root, the pin, the typed phases at `E2`, the merged tape,
`C_main`'s opening (`P20`'s atoms), from no pending positions (`fol_PSOfT`'s proof). -/
theorem fol_PSOfU (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20U.leafdecReads = 1) (hd : P20U.busDepth = Typed.miniDepth)
    (hr : P20U.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20U.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGU Ti))) x)
      (atomsOf P20U (schedule P20U)) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleU]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGU Ti)) x) _
    (atomsOf P20U (midItemsU P20U)) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPU reloc Ti hl hd hr he x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

set_option maxRecDepth 200000 in
/-- **The static check at S2GU** at the occupied words `occOfU` (one kernel evaluation over the items). -/
theorem stA_P20U : stA P20U (atomsOf P20U (schedule P20U)) 0 [] [] occOfU = true := by
  rw [stA_atomsOf]
  decide +kernel

/-- **`rwU20` is the S2GU schedule's read widths** from read `0`. -/
theorem wAt_rwU20 : WAt rwU20 0 (widthsA (atomsOf P20U (schedule P20U))) := by
  rw [← readWidthsP_eqAP]
  exact wAt_getD _ _

/-- **The S2GU schedule's read widths** in V_S's decision order (`wDecU`). -/
theorem widthsA_scheduleU : widthsA (atomsOf P20U (schedule P20U)) = wDecU (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  have hT : widthsA (atomsOf P20U (typedIT P20U)) = wTypedT := by
    rw [atomsOf_U, show typedIT P20U = typedIT P20T from rfl, ← atomsOf_T, widthsA_typedIT]
  have hF : widthsA (atomsOf P20U (tapeU P20U ++ wireU P20U)) = wTapeU := by
    rw [widthsA_atomsOf]
    simp only [tapeU, wireU, slotRedI, show P20U.logN = 20 from rfl, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, wI_tapeLayersE2I, wI_smp,
      show sepI.flatMap itemW = [] from rfl, wTapeU, wWireU, wTapeGkr, wSlot, List.nil_append, List.append_assoc]
    rfl
  rw [atomsOf_scheduleU, midItemsU, atomsOf_append P20U (pinI _), atomsOf_append P20U (typedIT _), atomsOf_pinIU]
  simp only [widthsA_append, hp, hT, hF, List.append_nil, List.nil_append, List.append_assoc, wDecU]
  rfl

/-- **V_S's S2GU decision refines the pinned S2GU middle phases on the stream with S2GU's read widths** under the
promise that its value passes `Φ_Q` at `E2` (`ref_decideGU` with `claimsU_rel`, the opening's atoms and widths). -/
theorem ref_decideGUX (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8) (hpub : pubG vk c sig = pubXT x) :
    RefAtPW capS occOfU shpS rwU20 sig 0 (decideProgUG P20U P20 N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))) x) (fun _ b ↦ b = true)
      (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (wDecU (atomsOf P20 (openMainI P20))).length := by
  have hw : WAt rwU20 0 (wDecU (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwU20
    rw [widthsA_scheduleU] at h
    exact h
  have hacc : (pubXT x).accIn.pt.length = Typed.phiVarsT := length_pubOfW _ _ _ _ _ _
  have hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXT x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  exact ref_decideGU N Q lay H vk c x hpub _ (fun cl pp ↦ fol_openMain cl pp)
    (fun w hw' ↦ mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')) hw hacc hs
    (fun t a' hT tp k hk hsh hall ↦ claimsU_rel N Q lay H hσ x t a' hT tp k hk hsh hall)

/-- **V_S's S2GU public values are the statement's** (16-B `acc_in` scalars; the stream holds the header bytes). -/
theorem pubGU_eq {vk c : RecursionFast.Digest} {π : ByteArray} (h : parseOk P20U vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytesP P20U - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubG vk c sig = pubXT (xOfH (headerBytesP P20U) π) :=
  pubOfW_eq h fe16At 16 accVT (fun _ _ _ h ↦ fe16At_congr h) (hdrFix_le_P _)
    (by rw [headerBytesP_P20U.1]; decide) hsig

/-- `decideFUG` at `P20U` holds: the run's checks held and its folded claim passes `Φ_Q` at `E2`. -/
theorem decideFUG_ok {N : TNatT} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFUG P20U P20 N vk c sig = true) :
    (runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U))).2.ok = true ∧
      N.phiT ((runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U))).1.pt.map Lvm.e2OfFE) =
        Lvm.e2OfFE (runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U))).1.y := by
  unfold decideFUG DM.runOnH at h
  have e : (decideProgUG P20U P20 N vk c sig).run (RS.startH (headerBytesP P20U)) =
      runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U)) := rfl
  rw [e] at h
  rcases hr : runD (decideProgUG P20U P20 N vk c) sig (RS.startH (headerBytesP P20U)) with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, fe2_beq h.2⟩

/-- **UTAPE-STMT 22's proof**: a `V_S` driving `decideFUG P20U P20 N` after `parseOk P20U` refines the specification's
scheme at `fmtU20`, the middle phases `midMk 4 relocU20 (midGU _)` (`refines_seqOfGO` at `occOfU` with
`ref_decideGUX`, `fol_PSOfU`, `stA_P20U`, `wAt_rwU20`). -/
theorem refinesU20_of (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypT N Q lay)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (VS : Lvm.T.SProg)
    (hVS : ∀ vk c π, VS vk c π = if parseOk P20U vk c π then drive P20U π (decideFUG P20U P20 N vk c) else .ret false) :
    ∀ (vk : RecursionFast.Digest) (L : RecursionFast.Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof),
      Lvm.T.isS π = true → (VS vk c π).runLog L = some true →
      ((Lvm.ASM.schemeSW Lvm.CT.fmtU20 vk
        (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.toT.fits
  exact fun vk L c π _ h ↦ runLog_of_seq (fun tr ht ↦ refines_seqOfGO
    (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGU (N.inst Q lay)))))
    (wDecU (atomsOf P20 (openMainI P20))).length P20U Lvm.CT.fmtU20 VS
    (fun vk c sig ↦ decideFUG P20U P20 N vk c sig) (decideProgUG P20U P20 N)
    (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (fun sig vk c x ↦ pubG vk c sig = pubXT x) hVS
    (fun _ _ _ hF ↦ decideFUG_ok hF) (fun _ _ _ _ hp hs ↦ pubGU_eq hp hs)
    (fun sig vk c x hpub ↦ ref_decideGUX N Q lay H hσ sig vk c x hpub) rfl rfl rfl
    (by rw [headerBytesP_P20U.1]; decide) (fun _ _ _ hp ↦ okS_of_parseOkH hp (hdrFix_le_P _))
    (fol_PSOfU relocU20 (N.inst Q lay) hl busDepth_P20 hr he) stA_P20U wAt_rwU20 vk c π tr ht) L h

end Lvm.VEq
end
