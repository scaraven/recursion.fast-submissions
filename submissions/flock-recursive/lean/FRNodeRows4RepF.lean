-- New for `flock-recursive` (track REPF; C1-RESULT §5, C1b-RESULT §5): the replay part of `Gaps4`
-- discharged — the previous node's five ops and the segment's `linkWAll` are rows of `nodeIRows4`.
import FRNodeRun4AskT
import FRSubmission4Cert
import FRNodeRows4RepLT

/-!
# The replay discharged

`nodeIRows4` folds `repIRowsW rtC1c` (`FRNodeRows4.repAllRows`, gated by `ArFit` and `RepFit`), and
`RepOk`/`RepHolds`/`repIRows4` are the `RTOkW` forms (`FRNodeRows4Rep`; B3's `compileFromX_run` takes
the replay rows at an assignment agreeing with the slot's below `repB`). So the two replay hypotheses of
B3's/SRA's/ASK-T's/IMPC's `Gap4.imp` theorems hold at `rt := rtC1c` for the certificate's ops:

* **`repFit_of`**: the statement's rows give `ProtoFit`, `ArFit` and `RepFit` (else a rejecting row
  `one · one = 0` is a row of `nodeIRows4`);
* **`repFold`**: the replay fold `hfoldR` (every slot's `repIRows4 rtC1c` rows are rows of `nodeIRows4`);
* **`repOk_rtC1cB`**: `RepOk rtC1c implB (fun _ => implB)` (C1/R3/C1b's `repOkW_rtC1c` at `implB`);
* **`gap4Imp_rtC1c`**: ASK-T's `gap4Imp_of_askT` at `rt := rtC1c` with both discharged: `Gap4.imp` from
  `StmtN4R` and `SlotRunA (rtC1c π) (withImpc askAq π)` alone;
* **`gaps4_of_runA`**: `Gaps4` from that residual (`SlotRunA` at `rtC1c`: the five previous-node ops
  and the segment's `linkWAll` are no longer imports there).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-- **The fits from the statement's rows**: if the prototypes, the arenas or the replay rows did not
fit, `nodeIRows4` would hold a rejecting row. -/
theorem repFit_of {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ProtoFit ∧ ArFit ∧ RepFit := by
  have hF := protoFit_of hone hE
  have hA := arFit_of hone hE
  refine ⟨hF, hA, ?_⟩
  by_contra hR
  have hm : (repSegB, rejR κ) ∈ nodeIRows4 κ :=
    mem_node_rep hF (by rw [repAllRows, if_pos hA, if_neg hR]; exact List.mem_singleton_self _)
  have h := hE _ hm
  exact rejectRows_ctl κ w hone fun p hp => by
    simp only [rejectRows, List.mem_singleton] at hp; subst hp; exact h

/-- **The replay fold** (`hfoldR` of `gap4Imp_of_run`/`_rsv`/`_askT`/`_impc` at `rt := rtC1c`). -/
theorem repFold {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ repIRows4 rtC1c κ v, p ∈ nodeIRows4 κ := by
  obtain ⟨hF, hA, hR⟩ := repFit_of hone hE
  intro v hv p hp
  exact mem_node_rep hF (by
    rw [repAllRows, if_pos hA, if_pos hR]
    exact List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, (repIRows4_eq rtC1c κ v) ▸ hp⟩)

/-- **The replay templates are sound at the certificate's ops** (`RepOk`, the `RTOkW` form). -/
theorem repOk_rtC1cB : RepOk rtC1c Sub4.implB (fun _ => Sub4.implB) :=
  repOk_iff.2 (repOkW_rtC1c (fun _ _ => rfl) (fun _ => rfl))

theorem implT_implB : ImplT Sub4.implB := by
  unfold Sub4.implB Impl.implCN
  exact Impl.implCWith_implT _ _

end N4s
end FR
