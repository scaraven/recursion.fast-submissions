-- New for lvm2 S1 (E2-F, E2F-V2), E2AC-DES §6 statement 15 (`refinesF20`): `VSFX N` refines the compiled verifier
-- of `PSWithM (midP (midM reloc20 (midF₂ (N.inst Q lay))))` at S2GF's format `fmtF20` (roll 11's `refinesM20`
-- shape with the pin and the read widths).
import LvmE2VTopF
import LvmE2VWidthsF
import LvmE2VDecRef

/-!
# Statement 15: `refinesF20`

For every native typed record `N` meeting E2F-Q's `TRefHypX N Q lay` (`N.phi` the specification's coordinate-split
`Φ_Q`) with `σ′`'s regions in the stream block (`SigInS N`): whenever `VSFX N` accepts a proof on a log, so does the
compiled verifier of the pinned middle phases at S2GF's format (read widths `rwF20`, `|π|`, header `headerF 44`).
-/

set_option autoImplicit false

namespace Lvm.E2V

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.VEq Lvm.TypedV LeanVM.Parameters LeanVM.Protocol.Compile

/-- **Statement 15 (`refinesF20`)**: `VSFX N` refines the compiled verifier of the pinned middle phases at S2GF. -/
theorem refinesF20 (N : TNat) (Q : Lvm.Loop.Program) (lay : Lvm.Typed.Lay) (H : TRefHypX N Q lay)
    (hσ : SigInS N) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSFX N vk c π).runLog L = some true →
      ((schemeSW fmtF20 vk (PSWithM (Lvm.E2F.midP (midM reloc20 (midF₂ (N.inst Q lay)))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.toT.fits
  have hw : WAt rwF20 0 (wDecF (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF)))
      (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwF20
    rw [widthsA_scheduleF] at h
    exact h
  have h24O : ∀ w ∈ widthsA (atomsOf P20 (openMainI P20)), w = 24 := fun w hw' ↦
    mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')
  exact refinesF20_of N Q lay _
    (fun sig vk c x hpub ↦ ref_decideFX N Q lay H hσ vk c x hpub _ _ (fun _ ↦ True)
      (folP_typedProgX (P20F.withF accVF) (N.inst Q lay) (pubXF x) rfl hl busDepth_P20 hr he)
      (fun cl pp ↦ fol_openMain cl pp) mem_widthsA_typedF h24O hw)
    (fol_PSOfF reloc20 (N.inst Q lay) hl busDepth_P20 hr he) stA_P20F wAt_rwF20

end Lvm.E2V
