-- New for `flock-recursive` (revision 4.4.2, the reserve; track RSV-S2a): the node implementation's
-- stacked `evalM` in the form `FRSoundness4R4FrE.e_fin4` takes (`hM`).
import FRVerifierImplNode4F
import FRSoundness4RsvStack

/-!
# `hM` for `implN4F` (RSV2 §2.2)

`NI4F.implN4F_hMX` gives the stacked call at a 32-entry row point as `Σ_κ ⟨s_κ, M̃_κ⟩` with
`dot3`/`sOf`; **`implN4F_hMS`** restates it as `P4b.mStack` of the point's entries (`s` the entries
`23 …`, the row point the entries `0 …`, the column point `σ`), the form of `e_fin4`'s `hM`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

theorem implN4F_hMS (base : NodeKind → OpImpl) (ν : NodeKind) :
    ∀ τ σ : Array F, τ.size = 32 → (NI4F.implN4F base ν).evalM τ σ =
      (P4b.mStack NI4F.srcE4 (fun i => τ.getD (23 + i) 0) (fun j => τ.getD j 0) (fun j => σ.getD j 0), 0, 0) :=
  fun τ σ h => by
    rw [NI4F.implN4F_hMX base ν τ σ h]
    simp only [P4b.mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      NI4F.dot3, NI4F.sOf, NodeKind.ix]
    rfl

end FR.Snd.R4
