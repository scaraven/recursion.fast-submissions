-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-I, items 1–3): the certificate of
-- the revision 4.1 submission `sub4` from INT-10's `certificate_rev4H`, with the residuals other
-- tracks still own bundled as one hypothesis, and the bounds against the rendered claim.
import FRSubmission4
import FRSoundness4XRunG
import FRNodeRows4PackSound
import FRXOut4
import FRXSig4H
import FRXSig4W

/-!
# `certificateR_sub4`: the certificate of `sub4`, given the open residuals

**`Open4`** is what INT-10's `certificate_rev4H` (at `fin := finC finPf`, `lRows := Layout.lRows`,
`κs₀ := 0`, where `implC` is `implB` by `Impl.implCN_eq`) still asks for `sub4`, stated over
S-E13a's route (S-H4 pass 7, `reviews/PATH-review.md` F1): `Resid4H.slots` is `I4`, `rd4 pf4` and
`resid4_of ∘ gap4_of_rows`, so what remains of it is `Gap4R` at `pf4 = reassemble4 seq4`
(`PfHdr pf4` is `pfHdr_reassemble4`). X4's rows 1 (`FrontHi`) and 2 (`RunFacts4`) are closed;
rows 8–9 are `complete_rev4`, `delta_rev4`; row 7 (`DecOk4`) is `decOk4_nd`, proved (S-H4 pass 11).

| field | what | owner |
|---|---|---|
| `gap` | `StmtN4 → Gap4R` at `pf4` (`imp`, `aggChk`; A1′ closed `kindS`/`wf`) | B3 (`gap4Imp_of_run`), B4 |
| `dec` | **`Links4 nd nodeDec4_nd`** (`hL`) | S-L4 (`links4_sigH`: from `gap`, `FRSubmission4Fin`) |

**The signature reader is fixed** (S-H4 pass 8): `sg := sigH` (H's message slots, rows 4–7), and
`readW4_sigH` (`readW4_eq` with **`sig_of_H`**, no hypothesis beyond `StmtN4`) is the bridge
`hL_of_res` uses; `sigWords_sigH` gives its output words as shifted H message words.

**The node branch is S-H4's `nd`** (`FRXNd4`, pass 11) in `sub4.E`/`sub4.ext` and in `Open4`: its
decode law `nodeDec4_nd` has links `LinksD4` and witness `readW4 sigH`, so `Open4.dec` is S-L4's
`links4_sigH` from `Open4.gap` (`FRSubmission4Fin`: `Open4F := Gaps4`).

**`certificateR_sub4`**: `Open4 → CertificateR D sub4` for every declared claim `D` whose numbers
are at least the submission's and whose fuel is within the budget (`boundsOK`); **`boundsOK_claim`**
checks them at `claim.json`'s numbers (`15/2^124`, `0`, `36000`, `3 · 2^46 + 2^13 t`).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4
open scoped NNReal

/-- The node verifier `sub4` runs (`sub4_V`). -/
abbrev Vnode4 : NodeProgs := VnodeC (NI4F.implN4F fun _ => implB) N4c.cells4

/-- **The node links `hL`** (S-L4's `hL_of_res`): on a good log, an accepted in-domain node run
has a transcript `es` meeting the decode law's links, and the witness read off it is a witness of
the relation. -/
def Links4 (nd : X.XIR) (D : NodeDec4 nd) : Prop :=
  ∀ vk κ L c π, Snd.X4.GoodX Snd.P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (Vnode4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (sub4.acc vk) c (D.readW κ L es)

/-- **The circuit's open gaps** at the slots' proof decoder `pf4` (S-E13a's `Gap4R`). -/
def Gaps4 : Prop :=
  ∀ vk κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
    N4s.Gap4R implB (fun _ => implB) X.pf4 κ vk c₁ c₂ w

/-- **The residuals of revision 4.1's certificate still open** (owners in the module doc). -/
structure Open4 : Prop where
  gap : Gaps4
  dec : Links4 nd nodeDec4_nd

/-- `PfHdr pf4` (`pfHdr_reassemble4`). -/
theorem pfHdr_pf4 : N4s.PfHdr X.pf4 := fun e tr => X.pfHdr_reassemble4 e tr

/-- **`Resid4H` from `Open4`'s parts**: the slots are `I4`, `rd4 pf4` with
`resid4_of ∘ gap4_of_rows`; the links are `Links4`. -/
theorem resid4H_of {nd : X.XIR} {D : NodeDec4 nd} (hG : Gaps4) (hL : Links4 nd D) (vk : Digest) :
    Snd.R4.Resid4H (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk := by
  exact ⟨⟨N4s.I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _, N4s.rd4 X.pf4,
    N4s.I4_rows _ _ _ _, fun κ w c₁ c₂ hS => N4s.resid4_of _ _ X.pf4 hS
      (N4s.gap4_of_rows X.pf4 pfHdr_pf4 hS (hG vk κ w c₁ c₂ hS))⟩,
    fun κ L c π hG' hk hd hr => hL vk κ L c π hG' hk hd hr⟩

/-- **The contract's `Certificate` of `sub4`, given `Open4`** (INT-10's `certificate_rev4H`, with
`DecOk4 nd` proved, `decOk4_nd`). -/
theorem certificate_sub4 (h : Open4) : Certificate sub4 :=
  Snd.R4.certificate_rev4H (Impl.finC finPf) Layout.lRows 0 sub4 sub4_V sub4_qV sub4_E sub4_ε
    sub4_ext sub4_fuel decOk4_nd nodeDec4_nd (resid4H_of h.gap h.dec) complete_rev4 delta_rev4

/-- **The bounds of `CertificateR`** against a declared claim `D`. -/
def boundsOK (D : Declared) : Prop :=
  sub4.ε ≤ D.ε ∧ sub4.δ ≤ D.δ ∧ sub4.qV ≤ D.qV ∧ ∀ t, sub4.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t

/-- **The certificate against a declared claim**, given `Open4`. -/
theorem certificateR_sub4 (D : Declared) (hb : boundsOK D) (h : Open4) : CertificateR D sub4 :=
  ⟨certificate_sub4 h, hb⟩

/-- **The bounds at `claim.json`'s numbers** (the rendered forms of `render-challenge.py`). -/
theorem boundsOK_claim :
    boundsOK ⟨(15 : ℝ≥0) / 21267647932558653966460912964485513216, (0 : ℝ≥0) / 1, 36000,
      fun t => 211106232532992 + 8192 * t⟩ := by
  refine ⟨?_, by simp [sub4, sub0], le_of_eq rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
  · rw [sub4_ε, Snd.epsR]; norm_num
  · simp [sub4, sub0, X.fuel, X.fuelBase, X.fuelPerWord]
  · simp only [extractorBudget]; omega

/-- (−) **The bounds are not vacuous**: a declared query bound below `qV4` fails them. -/
theorem not_boundsOK_qV :
    ¬ boundsOK ⟨(15 : ℝ≥0) / 21267647932558653966460912964485513216, 0, qV4 - 1,
      fun t => 211106232532992 + 8192 * t⟩ := fun h => by
  have h1 := h.2.2.1
  have h2 : 0 < qV4 := by decide
  simp only [sub4, sub0] at h1
  omega

end FR.Sub4
