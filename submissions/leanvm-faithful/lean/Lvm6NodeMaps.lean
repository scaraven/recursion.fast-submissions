-- New for lvm6 (WP NODE3, STARTUP ST-2, coordinator's decision 1). The deployed word maps are region-affine by
-- construction (`regW6`, MBT): `regW6_affine` on pairwise disjoint regions, the instance shape `MapsReg`, and CC's
-- region claims (`RegAff com`) checked per region (`ccRegsRB`), the `KS` regions word by word (29 small regions).
import Lvm6NodeMbT
import Lvm6NodeYRegs
import Lvm6NodeBits

/-!
# Region-affine word maps (WP NODE3, STARTUP ST-2)

* **`regW6_affine`**: on pairwise disjoint regions (`yDisjB`), `regW6 P lay s` maps word `r.base + i` of a region
  `r` of source `s` to `P.tgt r + i`.
* **`MapsReg Ti`**: `Ti`'s `com`, `S_flat` and `σ′` maps are `regW6 (mbPar6 Ti.lay) Ti.lay` (true by `rfl` for MBT's
  `tiOfL`).
* **`ccRegsRB`/`ccRegsRB_sound`**: `ccRegsB`'s facts, the `com` regions per region (alignment only), the `KS`
  regions as before.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm.Typed
open Lvm6.Ty (TInst6)
open Lvm6.Node.Mb (MbPar regW6)

/-- **`regW6` is affine on each region** of its source. -/
theorem regW6_affine (P : MbPar) {lay : Lay} (hd : yDisjB lay.yregs = true) {r : YReg} (hr : r ∈ lay.yregs)
    {s : YSrc} (hs : r.src = s) {i : ℕ} (hi : i < 2 ^ r.log) : regW6 P lay s (r.base + i) = P.tgt r + i := by
  have hp : (fun r' : YReg ↦ r'.src == s && decide (r'.base ≤ r.base + i ∧ r.base + i < r'.base + 2 ^ r'.log)) r
      = true := by simp [hs, hi]
  obtain ⟨r', hr'⟩ : ∃ r', lay.yregs.find? (fun r' : YReg ↦ r'.src == s &&
      decide (r'.base ≤ r.base + i ∧ r.base + i < r'.base + 2 ^ r'.log)) = some r' := by
    cases h : lay.yregs.find? (fun r' : YReg ↦ r'.src == s &&
        decide (r'.base ≤ r.base + i ∧ r.base + i < r'.base + 2 ^ r'.log)) with
    | none => exact absurd (List.find?_eq_none.mp h r hr) (by simp [hs, hi])
    | some r' => exact ⟨r', rfl⟩
  have hm' := List.mem_of_find?_eq_some hr'
  have hp' := List.find?_some hr'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have he : r' = r := by
    have := List.all_eq_true.mp (List.all_eq_true.mp hd r' hm') r hr
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with e | e
    · exact e
    · exact (yDisj_not e (y := r.base + i) (by simp [yMem]; omega) (by simp [yMem]; omega)).elim
  unfold regW6
  rw [hr', he]
  simp

/-- **The instance's word maps are `regW6`'s** (MBT's `tiOfL`, by `rfl`). -/
def MapsReg (Ti : TInst6) : Prop :=
  Ti.comW = regW6 (mbPar6 Ti.lay) Ti.lay .com ∧ Ti.sflatW = regW6 (mbPar6 Ti.lay) Ti.lay .sflat ∧
    Ti.sigmaW = regW6 (mbPar6 Ti.lay) Ti.lay .sigma

theorem regsOf_fst (lay : Lay) (s : YSrc) :
    (lay.yregs.filter fun r ↦ r.src == s) = (regsOf lay s).map Prod.fst := by
  simp only [regsOf, List.map_map]
  exact (List.map_id' _).symm

/-- **CC's region claims, per region**: the `com` regions aligned (their words map affinely by `MapsReg`), the `KS`
regions word by word (`regAffB`). -/
def ccRegsRB (Ti : TInst6) : Bool :=
  yDisjB Ti.lay.yregs &&
    (regsOf Ti.lay .com).all (fun p ↦ decide (p.1.base % 2 ^ p.1.log = 0) && decide (p.2 % 2 ^ p.1.log = 0)) &&
    regAffB Ti .ks Ti.ksW (regsOf Ti.lay .ks)

theorem ccRegsRB_sound {Ti : TInst6} (hM : MapsReg Ti) (h : ccRegsRB Ti = true) :
    QC.RegAff Ti .com Ti.comW (regsOf Ti.lay .com) ∧ QC.RegAff Ti .ks Ti.ksW (regsOf Ti.lay .ks) := by
  simp only [ccRegsRB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hd, ha⟩, hk⟩ := h
  refine ⟨⟨regsOf_fst Ti.lay .com, fun p hp ↦ ⟨(ha p hp).1, (ha p hp).2, fun i hi ↦ ?_⟩⟩, regAffB_sound hk⟩
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Ti.lay.yregs.filter (fun r ↦ r.src == .com), (r, regTgt Ti.lay r) = p := by
    simpa [regsOf] using hp
  rw [List.mem_filter] at hr
  rw [hM.1, regW6_affine _ hd hr.1 (by simpa using hr.2) hi]
  rfl

/-- **The node layout's facts with F2 and B1, region form** (`nodeLayB`, the `BITS` classes, `ccRegsRB`). -/
def nodeLayB3 (Ti : TInst6) : Bool := nodeLayB Ti && bitsAuxInB Ti.lay && ccRegsRB Ti

end Lvm6.Node.Dep
