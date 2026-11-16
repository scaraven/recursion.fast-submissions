-- New for lvm2 E2-FT (E2F-V2-FOL): S2GF's `P_S` (`PSWithM (midP (midM reloc (midF₂ Ti)))`) follows S2GF's schedule
-- (`Fol`, LvmVEqShape) at `P20F.withF accVF`: the pin, the coordinate-split typed phases, the `E2` front
-- (LvmE2VFolFront), `C_main`'s opening (roll 11's); the static check `stA` and the read widths `rwF20`.
import LvmE2VFolFront
import LvmE2FPin
import LvmMPVEq
import LvmTypedVEqTop

-- (GOLF2: 25 declarations that `certified` does not use moved verbatim to `LvmE2VWidthsFOff`, outside its import closure.)

/-!
# S2GF's `P_S` follows the schedule

At `P20F.withF accVF` (S2GF's record: `P20`'s levels, stage `1`, A23 at 44 variables):

* the schedule by phase (`phasesF_eq`, `scheduleF_eq`; the items `pinI`, `zeroIX`, `wiringIX`, `accIX`, `typedIX`,
  `midItemsF`; the front's `tapeIF` … `ksLinkIF` are LvmE2VFolFront's);
* `folP_zeroProgX`, `folP_wireProgX`, `folP_accProgQX`, **`folP_typedProgX`**: the coordinate-split typed phases
  (`ω`, 6 values at `r_x`, 8 matrix values, `κ` of 3, `h` of `accV + 1 = 45`) against `typedIX`;
* `folP_pinProg`, `folP_midP`, `folP_midF₂`, **`folP_midPF`**: the pinned middle phases against `midItemsF`;
  **`fol_PSOfF`**: the whole `P_S` against the whole schedule (roll 11's `fol_PSOfM` pattern, `C_main`'s opening at
  `P20`'s levels);
* **`stA_P20F`**: the static check, one kernel evaluation on the record with literal levels (`PF_eq`);
* `widthsA_atomsOf` (the atoms' read widths are the items'), **`wAt_rwF20`** (`rwF20` reads them), and
  `mem_widthsA_pinF`, `mem_widthsA_typedF`, `mem_widthsA_openF` (those phases read 24-byte scalars only).

A `Fol` at concrete atoms is applied with `@` (the default application elaborator would unfold it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

/-! ## The S2GF items -/

section Items

variable (p : Params)

/-- The root OOD pin: `ν` samples, one read. -/
def pinI : List Item := smp p.nuMain ++ rd 1
end Items

/-! ## The coordinate-split typed phases -/

section Typed

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

end Typed

/-! ## The pinned middle phases -/

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **The root OOD pin**: `ν = 23` samples, one read. -/
theorem folP_pinProg :
    FolP cap shp idx Lvm.E2F.pinProg (List.replicate CMain.nu20 .sm ++ [.rd]) fun _ ↦ True := by
  unfold Lvm.E2F.pinProg
  exact (folP_sampleChallenges _).bind fun _ _ ↦ folP_readScalar.bind_ret fun _ _ ↦ trivial

/-- `midP` follows the pin's atoms, then what `mid x` follows. -/
theorem folP_midP (mid : List UInt8 → VerifierProgram (List Verifier.StackClaim)) (x : List UInt8)
    (as : List Atom) (h : FolP cap shp idx (mid x) as fun _ ↦ True) :
    FolP cap shp idx (Lvm.E2F.midP mid x) ((List.replicate CMain.nu20 .sm ++ [.rd]) ++ as) fun _ ↦ True := by
  unfold Lvm.E2F.midP
  exact folP_pinProg.bind fun _ _ ↦ h.bind_ret fun _ _ ↦ trivial

end Mid

/-! ## The whole `P_S` -/

theorem atomsOf_F (its : List Item) : atomsOf (P20F.withF accVF) its = atomsOf P20 its := by
  unfold atomsOf
  congr 1

theorem openMainI_F : openMainI (P20F.withF accVF) = openMainI P20 := rfl

/-! ## The static check -/

/-! ## Read widths -/

/-- The read widths of an item (`read m`: `m` × 24 B; `readW m w`: `m` × `w` B). -/
def itemW : Item → List ℕ
  | .read m => List.replicate m 24
  | .readW m w => List.replicate m w
  | _ => []

theorem widthsA_replicate_rdw (w : ℕ) : ∀ m, widthsA (List.replicate m (.rdw w)) = List.replicate m w
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, List.replicate_succ, ← widthsA_replicate_rdw w m]; rfl

theorem widthsA_itemAtoms (p : Params) (it : Item) : widthsA (itemAtoms p it) = itemW it := by
  cases it with
  | read m => exact widthsA_replicate_rd m
  | readW m w => exact widthsA_replicate_rdw w m
  | positions r => exact widthsA_posAtoms _ _ _
  | _ => rfl

/-- **The atoms' read widths are the items'.** -/
theorem widthsA_atomsOf (p : Params) : ∀ its : List Item, widthsA (atomsOf p its) = its.flatMap itemW
  | [] => rfl
  | it :: its => by
    rw [atomsOf_cons, widthsA_append, widthsA_itemAtoms, widthsA_atomsOf p its, List.flatMap_cons]

theorem wAt_getD (l : List ℕ) (d : ℕ) : WAt (fun i ↦ l.getD i d) 0 l := fun k hk ↦ by
  show l.getD (0 + k) d = l.getD k 0
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]

/-! ### Phases that read 24-byte scalars only -/

theorem noWB_append (a b : List Item) : noWB (a ++ b) = (noWB a && noWB b) := List.all_append

theorem noWB_rd (m : ℕ) : noWB (rd m) = true := by unfold rd; split <;> rfl

theorem noWB_smp : ∀ n, noWB (smp n) = true
  | 0 => rfl
  | n + 1 => noWB_smp n

theorem noWB_flatten_replicate (l : List Item) (hl : noWB l = true) :
    ∀ n, noWB (List.replicate n l).flatten = true
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, noWB_append, hl, noWB_flatten_replicate l hl n]; rfl

theorem noWB_sumcheckI (n d : ℕ) : noWB (sumcheckI n d) = true :=
  noWB_flatten_replicate _ (by rw [noWB_append, noWB_rd]; rfl) n

theorem noWB_rdsmp (a b : ℕ) : noWB (rd a ++ smp b) = true := by
  rw [noWB_append, noWB_rd, noWB_smp]; rfl

theorem noWB_gpLayersI : ∀ fuel layer point, noWB (gpLayersI fuel layer point) = true
  | 0, _, _ => rfl
  | fuel + 1, layer, point => by
    rw [gpLayersI]
    split
    · rfl
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, noWB_append, noWB_smp, noWB_rd,
        noWB_gpLayersI fuel, noWB_flatten_replicate _ (noWB_rdsmp _ _), Bool.and_self]

/-- `C_main`'s opening reads 24-byte scalars only (it is `P20`'s, which has no `readW`). -/
theorem mem_widthsA_openF :
    ∀ x ∈ widthsA (atomsOf (P20F.withF accVF) (openMainI (P20F.withF accVF))), x = 24 := by
  have h := noWB_P20
  rw [schedule_eq P20 (by decide)] at h
  simp only [noWB_append, Bool.and_eq_true] at h
  rw [openMainI_F]
  exact mem_widthsA_atomsOf _ _ h.2.2.2.2.2.2.1

end Lvm.VEq
