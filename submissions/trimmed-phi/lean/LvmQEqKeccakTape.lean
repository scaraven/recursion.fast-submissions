-- New for lvm2 (T-Q): Q_arith_eq for the tape's layer loops (S2, BLUEPRINT2 T2). The layer proof is
-- v1's (`layer_coreI`, `LvmQEqKeccakLayer`); the block proof is v1's `layers_spec` (`LvmQEqKeccakGkr`)
-- generalised to a block of `2^d` real layers starting at layer `j0`.
import LvmQEqKeccakGkr
import LvmDecideTape

-- (GOLF2: 37 declarations that `certified` does not use moved verbatim to `LvmQEqKeccakTapeOff`, outside its import closure.)

/-!
# The tape's layers (`layerT_spec`, `layersT_spec`)

**`F` side.** `tChain v ls C₀ p L j0 k`: the claim after `k` tape layers from `C₀`, layer `k` (the
tape's layer `j0 + k`, `ι` term `iotaT (j0 + k)` = `RC[23 − step]`'s bits, one segment) read at
position `p + k·L` (`layerSpecI`). `tChain_add`: the chain from `j0` continued by the chain from
`j0 + n` at its end, so two blocks compose.

**Circuit side.** `layerT_spec`: one iteration of v1's layer template whose two constant slots both
hold `RC[23 − step]`'s bits computes the tape layer (`(1 + σ)·ι + σ·ι = ι`). `layersT_spec`: a loop
`[d]` of the template whose constants are `cstKT (j0 + jf)` carries `tChain … j0 (2^d)`; with the gate
`1`, its assertions hold iff every layer's two checks do.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## `F`'s tape layers on a view -/

/-! ## One tape layer -/

/-! ## A block of tape layers -/

/-! ## The tape's constants -/

theorem cstIT_ty (b : Src) (t : Nat) : (cstIT b t).ty = .K := by unfold cstIT; split <;> rfl

theorem cstIT_op (b : Src) (t : Nat) : ∃ k k', (cstIT b t).op = .lin k k' := by
  unfold cstIT; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem cstInsT_w (b : Src) : ∀ i ∈ cstInsT b, Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
  intro i hi
  simp only [cstInsT, List.mem_map, List.mem_range] at hi
  obtain ⟨t, -, rfl⟩ := hi
  obtain ⟨k, k', hk⟩ := cstIT_op b t
  simp [Row.w, Row.writes, hk, cstIT_ty]

/-- **The tape's constants block**: cell `p.k + t` holds constant `t % 16` of layer `t / 16`, the
gate `b` in slot `15`. -/
theorem cstT_spec {c : Ctx} {M : Mem} {p : Ptr} {bc : Cell}
    (h : SegsHold c M p (loop [] (tplOf (cstInsT (gkS bc))) p).2) {t : Nat} (ht : t < 16 * tapeDepth) :
    FE.ofK (M.k (p.k + t)) = if t % 16 = 15 then bc.val M else FE.ofK (cstKT (t / 16) (t % 16)) := by
  have hH := thold_of_loop h (jf := 0) (by simp)
  have hg : (cstInsT (gkS bc)).getD t default = cstIT (gkS bc) t := by
    simp [cstInsT, List.getD_eq_getElem?_getD, ht]
  have := hH t (by simp [cstInsT]; omega)
    (by rw [hg]; obtain ⟨k, k', hk⟩ := cstIT_op (gkS bc) t; exact Or.inr (Or.inl ⟨k, k', hk⟩))
  rw [Nat.zero_add, hg] at this
  have hc : iterF M (loop [] (tplOf (cstInsT (gkS bc))) p).1 0 t = FE.ofK (M.k (p.k + t)) := by
    rw [gk_loop_fst]
    show Cell.val M (LoopOut.cell ⟨p, [], tplOf (cstInsT (gkS bc))⟩ t 0) = _
    have hty : ((tplOf (cstInsT (gkS bc))).getD t default).ty = .K := by
      rw [tplOf_getD _ (by simp [cstInsT]; omega), hg]; exact cstIT_ty _ _
    simp only [LoopOut.cell, hty, Cell.val, Ptr.at,
      lrank_ones (δ := cstInsT (gkS bc)) (cstInsT_w _) (show t ≤ (cstInsT (gkS bc)).length by simp [cstInsT]; omega),
      Nat.mul_zero, Nat.add_zero]
    rfl
  rw [← hc, this]
  have hb : (gkS bc).valF (iterXv M (loop [] (tplOf (cstInsT (gkS bc))) p).1 0)
      (iterF M (loop [] (tplOf (cstInsT (gkS bc))) p).1 0) = bc.val M := gk_iterXv_gkS M _ 0 bc
  unfold cstIT
  split_ifs with h1
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_zero, zero_mul, add_zero]
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_one, one_mul, FE_add_self, zero_add]

/-! ## The tape's first claim -/

/-! ## `F`'s tape (T-V's `tapeGkrF`) on a view -/

end Lvm.Q1
