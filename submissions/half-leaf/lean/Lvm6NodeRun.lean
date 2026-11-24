-- New for lvm6 (WP NODE3, STARTUP ST-3). The deployed circuit built once with its outputs: `famQ6o` returns
-- `node6E`'s output cells, `Q_sig`'s pointer and `Q_sig`'s outputs, so the guard's `BITS` specs need no second run of
-- `node6E`/`qlink6`. Additive (PFW rule 3): `famQ6`, `progQ6`, `pS` are unchanged; the equations tie them.
import Lvm6NodeSlots

/-!
# One build of the deployed circuit (`famQ6o`, WP NODE3 / STARTUP ST-3)

* **`famQ6o lay`**: `famQ6 lay`'s families in the same order, with a `getPtr` before `Q_sig` and the outputs
  returned: `⟨o, ps, so⟩` (`node6E`'s cells, `Q_sig`'s pointer, `qsig6`'s outputs).
* **`famQ6o_segs`**: its segments at every pointer are `famQ6 lay`'s; **`progQ6_eq_o`**: `progQ6 lay` is
  `toProgramF nK 0 (famQ6o lay)`, so the program (and the blob) is the same.
* **`famQ6o_ps`**, **`famQ6o_so`**, **`famQ6o_o`**: the returned pointer is `pS lay p`, the outputs are
  `qsig6 sigI sigIl sbC (pS lay p)`'s and `n6 lay p`'s.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm6 Lvm6.QD Lvm6.Node Lvm6.QK Lvm.QSig
open Lvm6.Q (qlink6 opensP17 qsig6)

/-- What one build of the deployed circuit hands the guard. -/
structure FamOut where
  /-- `node6E`'s output cells. -/
  o : NodeOutE
  /-- `Q_sig`'s pointer. -/
  ps : Ptr
  /-- `qsig6`'s outputs. -/
  so : SigOut × WalkC

/-- **The deployed circuit with its outputs** (`famQ6`'s families, same order). -/
def famQ6o (lay : Lay) : BM FamOut :=
  node6E (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun o ↦
    qlink6 P6 opensP17 lay6 >>= fun _ ↦ getPtr >>= fun ps ↦ qsig6 sigI sigIl sbC >>= fun so ↦
      sigLeafCopy6 dstC (sgC + 597) (pbC + 1) >>= fun _ ↦ ccGo o lay (mbTD lay) ccbC gateC >>= fun _ ↦ pure ⟨o, ps, so⟩

/-! ## `BM`'s monad laws (as function equalities, so `simp` rewrites under binders without unfolding pointers) -/

theorem bm_bind_assoc {α β γ : Type} (m : BM α) (f : α → BM β) (g : β → BM γ) :
    (m >>= f) >>= g = m >>= fun x ↦ f x >>= g := by
  funext p
  simp only [bind_apply, List.append_assoc, Ptr.adv_append]

theorem bm_pure_bind {α β : Type} (a : α) (f : α → BM β) : ((pure a : BM α) >>= f) = f a := by
  funext p
  simp only [bind_apply, pure_apply, Ptr.adv_nil, List.nil_append]

theorem bm_getPtr_bind {β : Type} (m : BM β) : (getPtr >>= fun _ ↦ m) = m := by
  funext p
  simp only [bind_apply, getPtr, Ptr.adv_nil, List.nil_append]

theorem bm_bind_pure_unit (m : BM Unit) : (m >>= fun _ ↦ (pure () : BM Unit)) = m := by
  funext p
  simp only [bind_apply, pure_apply, List.append_nil]

/-- **`famQ6o` with its outputs dropped is `famQ6`.** -/
theorem famQ6o_unit (lay : Lay) : (famQ6o lay >>= fun _ ↦ (pure () : BM Unit)) = famQ6 lay := by
  simp only [famQ6o, famQ6, famR, bm_bind_assoc, bm_pure_bind, bm_getPtr_bind, bm_bind_pure_unit]

theorem famQ6o_segs (lay : Lay) (p : Ptr) : (famQ6o lay p).2 = (famQ6 lay p).2 := by
  rw [← famQ6o_unit lay, bind_apply]
  simp only [pure_apply, List.append_nil]

/-- **The same program** (and blob). -/
theorem progQ6_eq_o (lay : Lay) : progQ6 lay = Lvm.VF.toProgramF nK 0 (famQ6o lay) := by
  unfold progQ6 Lvm.VF.toProgramF
  rw [famQ6o_segs]

theorem fst_bind {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

/-- `famQ6o`'s output, by steps along its binds (no evaluation of the families). -/
theorem famQ6o_out (lay : Lay) (p : Ptr) :
    (famQ6o lay p).1 = ⟨(n6 lay p).1, pS lay p, (qsig6 sigI sigIl sbC (pS lay p)).1⟩ := by
  unfold famQ6o
  rw [fst_bind]
  try dsimp only
  rw [fst_bind]
  try dsimp only
  rw [fst_bind]
  try dsimp only [getPtr]
  rw [fst_bind]
  try dsimp only
  rw [fst_bind]
  try dsimp only
  rw [fst_bind]
  try dsimp only [pure_apply]
  simp only [pS, pL, n6, Ptr.adv_nil]

theorem famQ6o_ps (lay : Lay) (p : Ptr) : (famQ6o lay p).1.ps = pS lay p := by
  rw [famQ6o_out]

theorem famQ6o_so (lay : Lay) (p : Ptr) : (famQ6o lay p).1.so = (qsig6 sigI sigIl sbC (pS lay p)).1 := by
  rw [famQ6o_out]

theorem famQ6o_o (lay : Lay) (p : Ptr) : (famQ6o lay p).1.o = (n6 lay p).1 := by
  rw [famQ6o_out]

end Lvm6.Node.Dep
