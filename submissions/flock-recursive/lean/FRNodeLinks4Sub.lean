-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; track S-L4): `Open4`'s `Links4` (the
-- named `hL` of `sub4`) from `Gaps4` and the H signature, for S-H4's decoder.
import FRNodeLinks4Run
import FRSubmission4Cert

/-!
# `Links4` of `sub4` from `Gaps4` and `SigH4`

**`links4_of_gaps`**: for a node decoder `D` whose links follow from `LinksD4` and whose witness is
`readW4 sg` (S-H4's `nd`), `Links4 nd D` follows from `Open4.gap` (`Gaps4`, S-E13a's route at
`pf4`: `resid4_of ∘ gap4_of_rows`, as `resid4H_of`) and **`SigH4 sg`** at every key. So once `nd`
lands, `Open4.dec` is `SigH4 sg` (S-G/S-E's `sig_of_H`) and nothing else.
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4

/-- **`Links4` from the circuit's gaps and the H signature.** -/
theorem links4_of_gaps {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg)
    (hsig : ∀ vk, Snd.L4.SigH4 sg vk) (hG : Gaps4) : Links4 nd D := fun vk =>
  Snd.L4.hL_of_sig (Impl.finC finPf) Layout.lRows 0 sub4 vk sub4_V sub4_qV D hLk hW (hsig vk)
    (N4s.I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _) (N4s.I4_rows _ _ _ _)
    fun κ w c₁ c₂ hS => N4s.resid4_of _ _ X.pf4 hS (N4s.gap4_of_rows X.pf4 pfHdr_pf4 hS (hG vk κ w c₁ c₂ hS))

/-- **`Resid4H` of `sub4`** from the same: `resid4H_of` with `links4_of_gaps`. -/
theorem resid4H_of_gaps {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c)
    {sg : NodeKind → ℕ → Circ.Asg → Sig} (hW : D.readW = X.readW4 sg)
    (hsig : ∀ vk, Snd.L4.SigH4 sg vk) (hG : Gaps4) (vk : Digest) :
    Snd.R4.Resid4H (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk :=
  resid4H_of hG (links4_of_gaps D hLk hW hsig hG) vk

end FR.Sub4
