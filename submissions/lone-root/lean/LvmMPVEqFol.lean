-- New for lvm2 roll 11 (M′, R11-IR): M′'s middle phases `midM reloc (midT₂ Ti)` and the IOP verifier
-- `PSWithM (midM reloc (midT₂ Ti))` follow the schedule at `P20` (`S2GM`: one root, `C_main`'s opening), and
-- WP-14d's shape obligation `MidFollows` for them (R11-X's `ext_eqM20` reads it).
import LvmTypedVEqTop
import LvmMPMidT

/-!
# M′'s `P_S` follows the schedule

* `folP_midM`: `midM reloc mid x` follows what `mid x` follows (the relocation and `ordM` read nothing);
* **`fol_PSTM`**: `PSWithM (midM reloc (midT₂ Ti)) x` against the whole schedule (`fol_PSOfM`);
* `midFollows_midM`: `MidFollows mid` gives `MidFollows (midM reloc mid)`;
* **`midFollowsM20`**: `MidFollows (midM reloc (midT₂ Ti20))` for every relocation, from the guard's facts
  (`LvmTypedVEqTop.midFollowsT20L`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

section

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- `midM` follows what its pair-form phases follow. -/
theorem folP_midM (reloc : List UInt8 → VStackClaim → VStackClaim)
    (mid : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims) (x : List UInt8) (as : List Atom)
    (h : FolP cap shp idx (mid x) as fun _ ↦ True) :
    FolP cap shp idx (Lvm.ASM.midM reloc mid x) as fun _ ↦ True :=
  h.bind_ret fun _ _ ↦ trivial

end

/-- **M′'s typed `P_S` follows the schedule** at P20. -/
theorem fol_PSTM (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : P20.leafdecReads = 1) (hd : P20.busDepth = Typed.miniDepth)
    (hr : P20.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : P20.tableEvals = (Ti.mbT.map (·.w)).sum)
    (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.ASM.midM reloc (Typed.midT₂ Ti)) x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True :=
  fol_PSOfM _ (fun x ↦ folP_midM reloc _ x _ (folP_midT₂ Ti hl hd hr he x)) x

/-- **`MidFollows` through the relocation**: `midM` adds no transcript item. -/
theorem midFollows_midM (reloc : List UInt8 → VStackClaim → VStackClaim)
    {mid : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims} (h : Lvm.ASM.MidFollows mid) :
    Lvm.ASM.MidFollows (Lvm.ASM.midM reloc mid) := by
  intro x l a hl
  obtain ⟨b, l₁, l₂, rfl, h1, h2⟩ := Lvm.ASM.after_bind_ret hl
  cases l₂ with
  | nil => simpa using h x l₁ b h1
  | cons e l₂ => simp [VerifierProgram.after] at h2

open Lvm.CT Lvm.QTyped in
/-- **`MidFollows` at M′, `P20`** (R11-X's `ext_eqM20`): M′'s middle phases follow `midItems`, for every
relocation (in particular `LvmCertM20.reloc20`). -/
theorem midFollowsM20 (S : SF20) (H : Typed.THyp Ti20)
    (reloc : List UInt8 → VStackClaim → VStackClaim) :
    Lvm.ASM.MidFollows (Lvm.ASM.midM reloc (Typed.midT₂ Ti20)) :=
  midFollows_midM reloc (midFollowsT20L S H)

end Lvm.VEq
