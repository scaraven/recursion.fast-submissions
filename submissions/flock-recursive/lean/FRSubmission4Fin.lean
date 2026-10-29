-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-H4, pass 11, item 5: the plug,
-- coordinator's ruling of 2026-10-29). The certificate of `sub4` from `Gaps4` alone.
import FRSubmission4Cert
import FRNodeLinks4SigH

/-!
# `certificate_sub4F`: the certificate of `sub4` from `Gaps4`

With S-H4's node branch `nd` (`FRXNd4`: decode law `nodeDec4_nd`, links `LinksD4`, witness
`readW4 sigH`) and S-L4's `links4_sigH` (`Links4 nd D` from `Gaps4` for every decoder whose links
contain `LinksD4` and whose witness is `readW4 sigH`), `Open4`'s `dec` follows from its `gap`. What
the certificate still assumes is

**`Open4F := Gaps4`**: on every witness of the node statement `StmtN4`, the slots' circuit gaps
`Gap4R` at the proof decoder `pf4` (S-E13a's residual; owners B1′ … B4, A1′).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4

/-- **What the certificate of `sub4` still assumes**: the circuit's gaps. -/
def Open4F : Prop := Gaps4

/-- **`Open4` from `Open4F`**: `dec` is `links4_sigH` at S-H4's decoder. -/
theorem open4_of_F (h : Open4F) : Open4 := ⟨h, links4_sigH nodeDec4_nd (fun _ _ _ _ _ h => h) rfl h⟩

/-- **The contract's `Certificate` of `sub4`, given `Open4F`.** -/
theorem certificate_sub4F (h : Open4F) : Certificate sub4 := certificate_sub4 (open4_of_F h)

/-- **The certificate against a declared claim**, given `Open4F`. -/
theorem certificateR_sub4F (D : Declared) (hb : boundsOK D) (h : Open4F) : CertificateR D sub4 :=
  ⟨certificate_sub4F h, hb⟩

/-! ## Controls -/

/-- (+) The decoder's links are exactly `LinksD4` and its witness `readW4 sigH` (the two side
conditions of `links4_sigH` hold by `rfl`). -/
theorem nodeDec4_nd_parts : nodeDec4_nd.Links = X.LinksD4 ∧ nodeDec4_nd.readW = X.readW4 X.sigH := ⟨rfl, rfl⟩

/-- (−) **The submission's node branch is not the empty one**: `sub4.ext` runs `nd`, not `ndNone`. -/
theorem sub4_ext_ne_none : sub4.ext = ext4With nd ∧ nd ≠ ndNone := ⟨rfl, nd_ne_ndNone⟩

end FR.Sub4
