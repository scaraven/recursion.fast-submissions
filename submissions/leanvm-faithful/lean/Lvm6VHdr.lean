-- New for lvm6 (WP-V1, part 2): S's bridge `Stmt.hdrView_okV`: a header the scheme's check accepts
-- (`V.hdrOkWith` on its bytes, `u64At`/`digestAt`) has a well-formed view (`hdrView`, `rdU64`/`rdD`) whose
-- statement is `c` and whose key is `vk`.
import Lvm6Stmt
import Lvm6VFast

/-!
# The header codec bridge

* `toNat_rdU64`: S's `rdU64 x o` is `Lvm.u64At` of the same bytes (`toNat_kOfBytes`, `toNat_laneAt`);
* `rdD_eq`: S's `rdD x o` is `Lvm.digestAt` of the same bytes;
* **`hdrView_okV`**: `Stmt.hdrView_okV` (S `5697db44`, `Lvm6Stmt`).
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters Lvm.Replay

theorem toNat_rdU64 (x : List UInt8) (o : Nat) : (rdU64 x o).toNat = Lvm.u64At ⟨x.toArray⟩ o := by
  show (Lvm.FS.kOfBytes (x.drop o)).toBitVec.toNat = (Lvm.laneAt ⟨x.toArray⟩ o).toNat
  rw [Lvm.VEq.toNat_kOfBytes, Lvm.VEq.toNat_laneAt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lvm.VEq.getD_drop_bytes, get!_bl, bl_mk]

theorem rdD_eq (x : List UInt8) (o : Nat) : rdD x o = Lvm.digestAt ⟨x.toArray⟩ o := by
  apply Vector.ext
  intro i hi
  simp only [rdD, Lvm.FS.dg, Lvm.digestAt, Vector.getElem_ofFn]
  rw [Lvm.VEq.getD_drop_bytes, get!_bl, bl_mk]

theorem rdU64_eq_zero (x : List UInt8) (o : Nat) : rdU64 x o = 0 ↔ Lvm.u64At ⟨x.toArray⟩ o = 0 := by
  rw [← toNat_rdU64]
  exact ⟨fun h => by rw [h]; rfl, fun h => UInt64.toNat_inj.mp (by rw [h]; rfl)⟩

theorem rdU64_eq_one (x : List UInt8) (o : Nat) : rdU64 x o = 1 ↔ Lvm.u64At ⟨x.toArray⟩ o = 1 := by
  rw [← toNat_rdU64]
  exact ⟨fun h => by rw [h]; rfl, fun h => UInt64.toNat_inj.mp (by rw [h]; rfl)⟩

/-- **`Stmt.hdrView_okV`** (S `5697db44`: the key read at offset 88 is the checked `vk`). -/
theorem hdrView_okV : Stmt.hdrView_okV := by
  intro vk c x _ h
  simp only [V.hdrOkWith, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hvk⟩, hb⟩, hn⟩, hc'⟩, hc⟩ := h
  have hst : stmtOf (hdrView P18 x) = V.stmtWith leafStmt nodeStmt ⟨x.toArray⟩ := by
    simp only [stmtOf, hdrView, V.stmtWith, rdU64_eq_zero, rdD_eq, toNat_rdU64, leafStmtF_eq, nodeStmtF_eq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [hdrView, rdU64_eq_zero, rdU64_eq_one]; exact hb
  · simp only [hdrView, toNat_rdU64]; exact hn
  · intro h0
    simp only [hdrView, rdU64_eq_zero] at h0
    simp only [hdrView, rdD_eq]
    rcases hc' with h1 | h1
    · exact absurd h0 h1
    · exact h1
  · simp [hdrView]
  · simp only [stmtOk, decide_eq_true_eq, hst]; exact hc
  · simp only [hdrView, rdD_eq]; exact hvk

end Lvm6
