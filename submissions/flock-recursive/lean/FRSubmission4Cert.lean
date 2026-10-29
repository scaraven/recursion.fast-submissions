-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5; stage S-I, items 1–3): the certificate of
-- the revision 4.1 submission `sub4` from INT-10's `certificate_rev4H`, with the residuals other
-- tracks still own bundled as one hypothesis, and the bounds against the rendered claim.
import FRSubmission4
import FRSoundness4XRunG

/-!
# `certificateR_sub4`: the certificate of `sub4`, given the open residuals

**`Open4`** is what INT-10's `certificate_rev4H` (at `fin := finC finPf`, `lRows := Layout.lRows`,
`κs₀ := 0`, where `implC` is `implB` by `Impl.implCN_eq`) still asks for `sub4`. X4's rows 1
(`FrontHi`, P4f) and 2 (`RunFacts4`, R4i and INT-10) are closed; rows 8–9 (completeness,
`δ`) are `complete_rev4`, `delta_rev4`; row 7 (`DecOk4`) is `decOk4_ndNone`.

| field | X4 row | owner |
|---|---|---|
| `D : NodeDec4 ndNone` | 5 | S-H4 (the node decoder) |
| `resid vk : Resid4H …`, `slots` (`SlotIface4`, `NodeResid4`) | 3, 4 | S-N2 (instance `I4`, `rd4`; `Gap4` open) |
| `resid vk`, `links` | 6 | S-H4 |

**`Open4` is not satisfiable as it stands** whenever an accepted node proof lies in the extractor's
domain: `ndNone` extracts nothing from a node (`not_nodeDec4_ndNone`). It is the statement of what
is missing, not a claim that it holds: the node branch `nd` (S-H4) replaces `ndNone` in
`sub4.E`/`sub4.ext` and in `Open4`.

**`certificateR_sub4`**: `Open4 → CertificateR D sub4` for every declared claim `D` whose numbers
are at least the submission's and whose fuel is within the budget (`boundsOK`); **`boundsOK_claim`**
checks them at `claim.json`'s numbers (`15/2^124`, `0`, `36000`, `3 · 2^46 + 2^13 t`).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4 FR.X.X4
open scoped NNReal

/-- **The residuals of revision 4.1's certificate still open** (owners in the module doc). -/
structure Open4 : Prop where
  resid : ∃ D : NodeDec4 ndNone, ∀ vk, Snd.R4.Resid4H (Impl.finC finPf) Layout.lRows 0 sub4 ndNone D vk

/-- **The contract's `Certificate` of `sub4`, given `Open4`** (INT-10's `certificate_rev4H`). -/
theorem certificate_sub4 (h : Open4) : Certificate sub4 := by
  obtain ⟨D, hR⟩ := h.resid
  exact Snd.R4.certificate_rev4H (Impl.finC finPf) Layout.lRows 0 sub4 sub4_V sub4_qV sub4_E sub4_ε
    sub4_ext sub4_fuel decOk4_ndNone D hR complete_rev4 delta_rev4

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
    ¬ boundsOK ⟨(15 : ℝ≥0) / 21267647932558653966460912964485513216, 0, 35999,
      fun t => 211106232532992 + 8192 * t⟩ := fun h => by
  have := h.2.2.1; simp [sub4, sub0, qV4] at this

end FR.Sub4
