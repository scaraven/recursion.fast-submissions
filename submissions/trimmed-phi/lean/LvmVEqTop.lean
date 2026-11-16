-- New for lvm (WP-14a, H3): the per-phase value refinements of V_S's phases 4–7 (`dKg`) against `kgProgS`, and the
-- claim lists they return. lvm2 roll 11 (M′, R11-IR): the bus path's top (`dTop`, `ref_dMid`, `ref_decide`) is gone;
-- the typed top is `LvmTypedVEqTop`.
import LvmVEqWire
import LvmVEqParse
import LvmVEqKec
import LvmVEqBus
import LvmVEqWhir
import LvmCertS
import LvmAccNodeFold
import LvmShape
import LvmVEqClaims
import LvmVEqSum
import LvmMPVEqReloc
-- (GOLF2 import pruning: dropped LvmVEqTape: unused by this module.)

-- (GOLF2: 63 declarations that `certified` does not use moved verbatim to `LvmVEqTopOff`, outside its import closure.)

-- ===== merged from `LvmShapeVR` (GOLF module merge: `LvmShapeVR.lean` is now a stub importing `LvmVEqTop`) =====
section
-- New for lvm2 (CR-V, roll 7 SH2-Z; CR-DES §1.5): V_S's small `C_main` claims against `onStackZs`.
-- The wire phase with the ring coefficients (`dWireC`) refines as `dWire` does; at `P20` every
-- `C_main` claim of `dClaimsT` is an aligned block inside the stack and carries its tail value
-- (`tails_main`).

/-!
# V_S's small claims refine `onStackZs`

* **`ref_dWireC`**: `dWireC` refines T-W's wiring program with `WireRel` and `WireRing` (the ring
  claim's weight is `ringWeight` at `wirePt` with the returned coefficients).
* **`dClaimsT_fst`**: without the tails, `dClaimsT` is `dClaims`.
* **Tails per claim kind at `P20`** (each from `LvmShape`'s closed forms, none assumed):
  `table_tails` (`colsFitB`, `colsHiB`: blocks from word `2^22`), `ks_tails` (`KS`'s two claims),
  `ksOut_tails` (`KS`'s 25 output lanes), `ksLink_tails` (the link's four sums, M′: all on `C_main`),
  `tape_tails` (`D`'s point claims `tailDF`, the ring claim `ringTailN`, the boundary claims `0`);
  **`tails_main`**: every `C_main` claim of `dClaimsT` is `InStack` and its tail is `tailValueF`.
* (B1's two-commitment `ref_dOpenZ` is gone at M′ `S2GM`; the M′ opening is `LvmTypedVEqTop.ref_dOpenT`.)
-/

set_option autoImplicit false

namespace Lvm.Shape

open Lvm Lvm.VEq DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The wire phase with the ring coefficients -/

/-! ## The claims without their tails -/

/-! ## Tails per claim kind at `P20` -/

/-- A block from word `2^22`, at most `2^22` words, aligned, inside the stack. -/
def OffOK (b : Placement) : Prop :=
  2 ^ 22 ≤ b.index ∧ b.variableCount ≤ 22 ∧ b.index < 2 ^ CMain.nu20 ∧ b.index % 2 ^ b.variableCount = 0

instance (b : Placement) : Decidable (OffOK b) := by unfold OffOK; infer_instance

instance (b : Placement) : Decidable (InStack b) := by unfold InStack; infer_instance

theorem OffOK.inStack {b : Placement} (h : OffOK b) : InStack b :=
  ⟨by have := h.2.1; unfold CMain.nu20; (clear * - this; omega), h.2.2.2, h.2.2.1⟩

theorem OffOK.tail {c : BlockClaim} (h : OffOK c.block) : tailValueF c.onStack.1 = 0 :=
  tailValueF_off c h.1 h.2.1 h.2.2.1

theorem nuMain_P20 : P20.nuMain = CMain.nu20 := by decide +kernel

/-- `KS`'s block at `P20`. -/
theorem offOK_ks : OffOK ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ := by
  rw [layout0_P20]; decide +kernel

/-- `KS`'s `Y` lanes at `P20`. -/
theorem offOK_ksY (l : ℕ) (hl : l < 25) (pt : List FE) : OffOK (ksYPart P20 (layout0 P20) l pt).1 := by
  unfold ksYPart
  split_ifs
  · exact offOK_ks
  · rw [layout0_P20]
    have : ∀ l < 25, ¬ l < 14 → OffOK ⟨P20.ksLog, CMain.ksY2Off20 + (l - 14) * 2 ^ P20.ksLog⟩ := by
      decide +kernel
    exact this l hl (by assumption)

/-- **The tables' `C_main` claims** have no tail (`colsFitB`: aligned inside the stack; `colsHiB`: from
word `2^22`, at most `2^22` words). -/
theorem table_tails (T T₀ : List M3.Tab) (hT : ∀ t ∈ T, t ∈ T₀) (evs : List (List FE × List FE))
    (hc : M3.colsFitB P20 T₀ = true) (hh : M3.colsHiB T₀ = true) :
    ∀ e ∈ M3.tableClaimsR T evs, e.1 = .main → OffOK e.2.block := by
  intro e he hm
  unfold M3.tableClaimsR at he
  obtain ⟨⟨t, pt, ev⟩, htz, he⟩ := List.mem_flatMap.mp he
  have ht : t ∈ T₀ := hT t (List.of_mem_zip htz).1
  obtain ⟨⟨c, i⟩, hci, hce⟩ := List.mem_filterMap.mp he
  have hc' : c ∈ t.cols := List.fst_mem_of_mem_zipIdx hci
  unfold M3.colsFitB at hc
  unfold M3.colsHiB at hh
  simp only [Bool.and_eq_true, List.all_eq_true] at hc hh
  have h1 := hc.2 t ht c hc'
  have h2 := hh t ht c hc'
  cases c with
  | fix f ev' => simp at hce
  | com rec off =>
    simp only [Option.some.injEq] at hce
    subst hce
    cases rec with
    | true => simp at hm
    | false =>
      simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.false_eq_true,
        ite_false] at h1 h2
      refine ⟨h2.1, h2.2, ?_, h1.1⟩
      rw [nuMain_P20] at h1
      have := Nat.one_le_two_pow (n := t.τ)
      simp only [BlockClaim.point]
      (clear * - h1; omega)

/-- `M`'s columns at `P20` (M′: the stream block's column `l`, `2^ksLog` rows from `S + l·2^recRowsLog`). -/
theorem offOK_m (l : ℕ) (hl : l < 17) :
    OffOK ⟨P20.ksLog, (layout0 P20).s + l * 2 ^ P20.recRowsLog⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨P20.ksLog, CMain.sOff20 + l * 2 ^ P20.recRowsLog⟩ := by decide +kernel
  exact this l hl

/-- `M`'s top rows at `P20` (`2^ksXLog` rows of column `l` from the split). -/
theorem offOK_mx (l : ℕ) (hl : l < 17) :
    OffOK ⟨ksXLog P20, (layout0 P20).s + l * 2 ^ P20.recRowsLog + ksSplit P20⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨ksXLog P20, CMain.sOff20 + l * 2 ^ P20.recRowsLog + ksSplit P20⟩ := by decide +kernel
  exact this l hl

/-- `X`'s columns at `P20` (M′: column `l`'s rows from the split, `X` at `S + ksSplit`, stride `2^recRowsLog`). -/
theorem offOK_xs (l : ℕ) (hl : l < 17) :
    OffOK ⟨ksXLog P20, (layout0 P20).x + l * 2 ^ P20.recRowsLog⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨ksXLog P20, CMain.xOff20 + l * 2 ^ P20.recRowsLog⟩ := by decide +kernel
  exact this l hl

/-! ## The openings in both shapes -/

end Lvm.Shape
end
-- ===== end of `LvmShapeVR` =====

-- ===== merged from `LvmVEqLinkArith` (GOLF module merge: `LvmVEqLinkArith.lean` is now a stub importing `LvmVEqTop`) =====
section
-- New for lvm (WP-14a, H3): V_S's CH/KS link formulas (LvmDecideV0: `shiftEval`, `eqMasked`, `omegaCH`,
-- `padWeight`, `padConst`, the link targets and checks, `contShift`) and its caller-placed ring switch
-- (LvmDecide `ringRaw`) over `E`: WP-8's `shiftEvalE`, `eqMaskedE`, `omegaE`, `padWeightE`, `padConstE`,
-- `chShiftTargetE`, `chSc2TargetE`, `wtE`, `contShiftE` and leanVM's `ringSwitch` (LvmVCore).

/-!
# The link formulas over `E`

`FE.toExt3` of each native link formula is WP-8's `E` formula at the mapped arguments. V_S's
equality kernels are tables (`eqKernel`, `eqKernelA`) where WP-8 uses `eqAt`; they agree below
`2^|p|` (`toExt3_getD_eqKernel`, `toExt3_getD_eqKernelA`, WP-2's `eqKernel_getD`), so the lemmas
take the lengths of the challenge lists (`λ` 3, `ζ` 6, `μ` 2, the `KS` points 13 at KS13, B1; roll 7: 14 at KS14, lvm2 CR-K).

`ringRaw s` (V_S's caller-placed ring switch: target and Frobenius coefficients) refines leanVM's
`ringSwitch pt s` at any point `pt`: same target, weight `ringWeight pt · coeffs` (`ref_ringRaw`).
The lengths of the native `samples`, `readEs`, `sumcheck` values (`length_*`) enter through
`refAt_withD`. Everything here is in `Lvm.VEq.Lk`.
-/

set_option autoImplicit false

namespace Lvm.VEq.Lk

open Lvm Lvm.VEq DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr Finset
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK)

/-! ## Folds and sums -/

/-! ## Equality kernels -/

/-! ## `shiftEval`, `eqMasked` -/

/-! ## The `CH` link's weights -/

/-! ## The `KS` link -/

/-! ## Ring switching -/

/-! ## Native lengths and the ring switch's refinement -/

theorem length_readEs : ∀ (n : ℕ) (sig : ByteArray) (s : RS), (runD (DM.readEs n) sig s).1.length = n
  | 0, _, _ => rfl
  | n + 1, sig, _ => congrArg (· + 1) (length_readEs n sig _)

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- A fact about the native step's value. -/
theorem refAt_withD {α β : Type} {d : DM β} {P : LeanVM.Protocol.Compile.VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAt cap occ shp sig d P R) (hq : ∀ s, Q (runD d sig s).1) :
    RefAt cap occ shp sig d P fun b a ↦ R b a ∧ Q b := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hq s⟩

end Ref

end Lvm.VEq.Lk
end
-- ===== end of `LvmVEqLinkArith` =====

-- ===== merged from `LvmVEqLink` (GOLF module merge: `LvmVEqLink.lean` is now a stub importing `LvmVEqTop`) =====
section
-- New for lvm (WP-14a, H3): V_S's phases 5 and 7 (LvmVEqPhases `dChLink`, `dKsLink`, the CH and KS links of
-- `M3.real P20`) refine WP-8's DSL programs (`Lvm.KG.chLinkProg`, `ksLinkProg`) on the stream, their claims
-- related by `CRel` to LvmVEqMid's `chLinkClaimsE`, `ksLinkClaimsE`.

/-!
# The `CH` and `KS` links: V_S refines the verifier language

(lvm2 S2: v1's `CH` link is gone from V_S, so `ref_dChLink` is deleted.) v1's `ref_dChLink`: wherever V_S's phase 5 ends with its checks held, WP-8's `chLinkProg 20 52` read off
the stream returns `lo` at the same cursor with V_S's link claims `CRel`-related to
`chLinkClaimsE lo`; `ref_dKsLink` the same for phase 7, `ksLinkProg 13 9 (contRows P20)` (KS13, lvm2 roll 8, B1;
roll 7: `ksLinkProg 14 10`, KS14) and
`ksLinkClaimsE`. Read for read: the samples and scalars by `ref_samples`/`ref_readEs`, the sumchecks
by H1's `ref_sumcheck` (their claims transported by LvmVEqLinkArith), the caller-placed ring switches
by `ref_ringRaw`, the final `require` by the transported check (`toExt3_chOk`, `toExt3_ksOk`).
`monoD_dChLink`, `monoD_dKsLink` hold for every `p`, `m`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr Finset Lk
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK FE_eq_of_beq)

/-! ## `MonoD` -/

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

namespace Lk

theorem forall₂_map_both {α β γ δ : Type} {R : γ → δ → Prop} {f : α → γ} {g : β → δ} {l : List α}
    {l' : List β} (h : List.Forall₂ (fun a b ↦ R (f a) (g b)) l l') :
    List.Forall₂ R (l.map f) (l'.map g) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 h)

theorem ref_readEsL (n : ℕ) :
    RefAt cap occ shp sig (DM.readEs n) (Compile.VerifierProgram.readScalars n)
      fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n :=
  refAt_withD (ref_readEs n) (Q := fun xs ↦ xs.length = n) (length_readEs n sig)

end Lk

/-- **A native claim against a spec claim, M′** (lvm2 roll 11, `S2GM`): the same claim (`CRel`), or V_S's `C_main`
claim on the stream block `S` against a `C_rec` claim, through the relocation `relocS`. -/
def CRelM (a : Com × Lvm.BlockClaim) (b : Com × BClaim) : Prop :=
  CRel a b ∨ (a.1 = .main ∧ b.1 = .crec ∧ SCRel a.2.onStack (relocS b.2.onStack))

theorem CRel.crelM {a : Com × Lvm.BlockClaim} {b : Com × BClaim} (h : CRel a b) : CRelM a b := Or.inl h

end Ref

end Lvm.VEq
end
-- ===== end of `LvmVEqLink` =====

/-!
# V_S's phases 4–7 refine `kgProgS`

`dBusTab` (the bus path's phases 2–3b, dead at B1), `dKg` (phases 4–7, grouped as `kgProgS`); against `kgProgS`:
phases 4–5 by `ref_dTapeW` (`ref_dTape`, `ref_dWire`), phase 6 by H2's `ref_dKec`, phase 7 by `ref_dKsLink`
(**`ref_dKg`**, relation `KgRel`); `dClaims_rel`: the claims of the tape, `KS` and its output lanes, claim for claim
(`CRel`); the `KS` link's by `CRelM` (M′: `M` on `S`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Lk
open LeanVM.Protocol.Whir.Sound (cfgMain24G)

/-! ## `decideProg` grouped as `P_S` -/

/-- The native result of a Keccak phase (`dKec`). -/
abbrev KecN : Type := List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE))

/-! ## `MonoD` -/

/-! ## The claims -/

/-! ## `s` from the statement -/

theorem get!_hdX_x (x : List UInt8) (t : ℕ) :
    (⟨(List.replicate 8 0 ++ x).toArray⟩ : ByteArray).get! (8 + t) = x.getD t 0 := by
  rw [get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem get!_sigOfX_x' (x : List UInt8) (t : ℕ) : (sigOfX x).get! (headerAt 8 + t) = x.getD t 0 := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

/-- **The statement's chain start**: V_S's `s` lanes are the header digest `s`'s (lvm2 S2: the wire
phase's `Pad43(s)`). -/
theorem pubX_s (x : List UInt8) : (pubX x).s = digestLanes (hdX x).s := by
  have e : ∀ i < 4, ∀ j < 8, ((hdX x).s.toArray.getD (8 * i + j) 0) =
      (sigOfX x).get! (headerAt 80 + 8 * i + j) := by
    intro i hi j hj
    rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_eq_getElem (by omega)]
    simp only [hdX, Header.ofProof, digestAt, Vector.getElem_ofFn, Option.getD_some, offS]
    rw [show 80 + (8 * i + j) = 8 + (72 + 8 * i + j) by (clear * -; omega), get!_hdX_x,
      show headerAt 80 + 8 * i + j = headerAt 8 + (72 + 8 * i + j) by simp only [headerAt]; (clear * -; omega),
      get!_sigOfX_x']
  unfold pubX pubOf digestLanes
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have e0 := e i hi' 0 (by (clear * -; omega))
  simp only [Nat.add_zero] at e0
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e i hi' 1 (by (clear * -; omega)), e i hi' 2 (by (clear * -; omega)), e i hi' 3 (by (clear * -; omega)),
    e i hi' 4 (by (clear * -; omega)), e i hi' 5 (by (clear * -; omega)), e i hi' 6 (by (clear * -; omega)), e i hi' 7 (by (clear * -; omega)), kAt, laneAt,
    UInt64.zero_or, Nat.add_zero, Nat.add_assoc]

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

theorem smallP_P20 (x : List UInt8) : Shape.smallP P20 (pubX x) = Shape.small x := by
  unfold Shape.smallP Shape.small
  rw [show (P20.logN == 20 && P20.nuMain == CMain.nu20) = true by decide +kernel, Bool.true_and]

end Ref

end Lvm.VEq
