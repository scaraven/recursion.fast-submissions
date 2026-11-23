-- New for lvm2 S1 (E2-F, E2F-V): V_S's small phases of the `E2` front refine the spec's on the width-aware stream:
-- the row switch (`rowSwitchD` ⇄ `rowSwitch`), the root pin (`pinD` ⇄ `Lvm.E2F.pinProg`), the `KS` link
-- (`ksLinkD` ⇄ `ksLinkProgE2`).
import LvmE2VEqRounds
import LvmE2FPin

/-!
# The row switch, the pin and the `KS` link

* **`refW_rowSwitchD`**: the switched target and weight agree through `FE.toExt3` (`toBF64_rowWordD`,
  `tensorWD_getD`); seven `E3` samples, no read;
* **`refW_pinD`**: `ν` `E3` samples and one 24-byte read; the claim's point and value;
* **`refW_ksLinkD`**: `hk + 5` ground coordinates, `hk` plain rounds, four `E2` scalars, the check.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)

theorem toE2_getD (l : List FE2) (n : ℕ) : toE2 (l.getD n 0) = (l.map toE2).getD n 0 := by
  rw [← Lvm.FE2.toE2_zero, List.getD_map]

theorem toExt3_sumE_range' (f : ℕ → FE) (n : ℕ) :
    FE.toExt3 (Lvm.sumE ((List.range n).map f)) = ∑ j ∈ range n, FE.toExt3 (f j) := by
  rw [toExt3_sumE, List.map_map, LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]
  rfl

/-- The equality weights of `7` challenges at `j < 128`. -/
theorem toExt3_eqKernel_getD (rr : List FE) (hr : rr.length = 7) {j : ℕ} (hj : j < 128) :
    FE.toExt3 ((Lvm.eqKernel rr).getD j 0) =
      LeanVM.Protocol.KeccakGkr.eqAt (rr.map FE.toExt3) j := by
  rw [← getD_map_toExt3, map_eqKernel, LeanVM.Protocol.KeccakGkr.eqKernel_getD, List.length_map, hr,
    if_pos (by norm_num; omega)]

theorem monoD_rowSwitchD (z sv : List FE2) : MonoD (rowSwitchD z sv) :=
  (monoD_samples 7).bind fun _ ↦ MonoD.pure _

theorem monoD_pinD (nu : ℕ) : MonoD (pinD nu) :=
  (monoD_samples nu).bind fun _ ↦ monoD_readE.bind fun _ ↦ MonoD.pure _

theorem monoD_ksLinkD (hk xl : ℕ) (rows : List ℕ) : MonoD (ksLinkD hk xl rows) :=
  (monoD_samplesG _ _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind
    fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

/-- What the row switch's two sides relate: the target, and the weight at every point. -/
def RowRel (xs : (FE × (List FE → FE)) × List FE) (ys : E × (List E → E)) : Prop :=
  ys.1 = FE.toExt3 xs.1.1 ∧ ∀ r : List FE, ys.2 (r.map FE.toExt3) = FE.toExt3 (xs.1.2 r)

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- `n` challenges, with the native list's length. -/
theorem refW_samplesL : ∀ (n : ℕ) {i : ℕ}, RefAtW cap occ shp rw sig i (DM.samples n)
    (VerifierProgram.sampleChallenges n) (fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n) i
  | 0, _ => RefAtW.pure ⟨rfl, rfl⟩
  | n + 1, _ => by
    refine RefAtW.bind (fun _ ↦ (monoD_samples n).bind fun _ ↦ MonoD.pure _) refW_sampleE ?_
    intro x y hxy
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_samplesL n) ?_
    intro xs ys hs
    exact RefAtW.pure ⟨by simp [hxy, hs.1], by simp [hs.2]⟩

/-- **The row switch.** -/
theorem refW_rowSwitchD (z sv : List FE2) {i : ℕ} :
    RefAtW cap occ shp rw sig i (rowSwitchD z sv) (E2V.rowSwitch (z.map toE2) (sv.map toE2)) RowRel i := by
  unfold rowSwitchD E2V.rowSwitch
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_samplesL 7) ?_
  rintro rr rr' ⟨hrr, hl⟩
  subst hrr
  refine RefAtW.pure ⟨?_, fun r ↦ ?_⟩
  · simp only [E2V.rowTarget]
    rw [toExt3_sumE_range']
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Lvm.M3.tE_mul, toExt3_eqKernel_getD rr hl (Finset.mem_range.1 hj), FE.toExt3_ofK, ← E2V.toBF64_rowWordD]
    rfl
  · simp only [E2V.rowWeight]
    rw [toExt3_sumE_range']
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Lvm.M3.tE_mul, toExt3_eqKernel_getD rr hl (Finset.mem_range.1 hj), E2V.tensorWD_getD]

/-- **The root pin** (`ν` samples, one 24-byte read). -/
theorem refW_pinD {i : ℕ} (hw : rw i = 24) :
    RefAtW cap occ shp rw sig i (pinD CMain.nu20) Lvm.E2F.pinProg
      (fun c za ↦ ∃ z a, c = BlockClaim.point ⟨CMain.nu20, 0⟩ z a ∧ za = (z.map FE.toExt3, FE.toExt3 a))
      (i + 1) := by
  unfold pinD Lvm.E2F.pinProg
  refine RefAtW.bind (fun _ ↦ monoD_readE.bind fun _ ↦ MonoD.pure _) (refW_samples _) ?_
  intro z z' hz
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_readE hw) ?_
  intro a a' ha
  exact RefAtW.pure ⟨z, a, rfl, by rw [hz, ha]⟩

/-- The widths of the `KS` link. -/
def wKsLink (hk : ℕ) : List ℕ := List.replicate (hk + 5) 8 ++ wSc 3 hk ++ wReads 4

/-- **The `KS` link.** -/
theorem refW_ksLinkD (hk xl : ℕ) (rows : List ℕ) {i : ℕ} (hw : WAt rw i (wKsLink hk)) :
    RefAtW cap occ shp rw sig i (ksLinkD hk xl rows) (E2V.ksLinkProgE2 hk xl rows)
      (fun xs ys ↦ ys.1 = xs.1.map toE2 ∧ ys.2.1.1 = xs.2.1.1.map toE2 ∧ ys.2.1.2 = toE2 xs.2.1.2 ∧
        ys.2.2 = xs.2.2.map toE2) (i + (wKsLink hk).length) := by
  rw [wKsLink, WAt.append, WAt.append] at hw
  obtain ⟨⟨h1, h2⟩, h3⟩ := hw
  unfold ksLinkD E2V.ksLinkProgE2
  refine RefAtW.bind (fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind
    fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (refW_samplesG E2V.gC1 (hk + 5) h1) ?_
  intro kchal kchal' hk'
  have hsc := refW_sumcheckD (cap := cap) (occ := occ) (shp := shp) (sig := sig) E2V.gC2 3 (by norm_num)
    (List.replicate hk none) 0 (by simpa using h2)
  have hm : (List.replicate hk (none : Option FE2)).map (Option.map toE2) = List.replicate hk none := by
    simp
  rw [hm, Lvm.FE2.toE2_zero] at hsc
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    hsc ?_
  intro ks ks' hks
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 4 (by simpa [length_wSc, Nat.add_assoc] using h3)) ?_
  intro vals vals' hv
  subst hk' hv
  obtain ⟨hks1, hks2, -⟩ := hks
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    rw [hks1, hks2, h']
    simp only [Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, E2V.toE2_contShiftF, E2V.toE2_eqEvalF,
      E2V.toE2_selXF, toE2_getD, List.map_take]
  · refine (RefAtW.pure ⟨rfl, hks1, hks2, rfl⟩).idx ?_
    simp [wKsLink, length_wSc, length_wReads]
    omega

end Ref

end Lvm.VEq
