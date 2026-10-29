-- New for `flock-recursive` (BLUEPRINT revision 4.3, (A)(ii); track S-L4): `Links4` for S-H4's
-- decoder at the H signature reader `sigH` (S-H4 pass 8's `readW4_sigH`, `sig_of_H`).
import FRNodeLinks4Sub
import FRXSig4H

/-!
# `Links4` at `readW4 sigH`

S-H4 pass 8 proves `sig_of_H` from `StmtN4` alone, and its bridge **`readW4_sigH`**: on `StmtN4` at
`wF κ L es`, `readW4 sigH κ L es` is `rd4 pf4`'s node witness. So:

* **`readW4_sigH_law`**: `readW4 sigH` meets the read law `ReadW4` at `rd4 pf4`, at every key;
* **`sigH4_sigH`**: `SigH4 sigH vk` (S-L4's name for `sig_of_H`);
* **`links4_sigH`**: for a decoder with links `⊇ LinksD4` and witness `readW4 sigH`,
  `Links4 nd D` follows from `Gaps4` alone. `Open4`'s `dec` then needs nothing beyond `gap`.
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4

/-- **`readW4 sigH` meets the read law at `rd4 pf4`** (`readW4_sigH`, `wF = T4.fF`). -/
theorem readW4_sigH_law (vk : Digest) : Snd.L4.ReadW4 (X.readW4 X.sigH) (N4s.rd4 X.pf4) vk := by
  intro κ L es c₁ c₂ hS
  rw [← Snd.L4.wF_eq_fF] at hS ⊢
  exact X.readW4_sigH hS

/-- **`sig_of_H` is `SigH4 sigH`.** -/
theorem sigH4_sigH (vk : Digest) : Snd.L4.SigH4 X.sigH vk := fun _ _ _ _ hS => X.sig_of_H hS

/-- **`Links4` of S-H4's decoder from `Gaps4` alone** (links `⊇ LinksD4`, witness `readW4 sigH`). -/
theorem links4_sigH {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c) (hW : D.readW = X.readW4 X.sigH)
    (hG : Gaps4) : Links4 nd D :=
  links4_of_gaps D hLk hW sigH4_sigH hG

/-- **`Resid4HR` of `sub4`** for that decoder, from `Gaps4` alone. -/
theorem resid4H_sigH {nd : X.XIR} (D : NodeDec4 nd)
    (hLk : ∀ κ L es π c, X.LinksD4 κ L es π c → D.Links κ L es π c) (hW : D.readW = X.readW4 X.sigH)
    (hG : Gaps4) (vk : Digest) : Snd.R4.Resid4HR (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk :=
  resid4H_of hG (links4_sigH D hLk hW hG) vk

end FR.Sub4
