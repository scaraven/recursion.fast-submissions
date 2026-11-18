-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXBfly,
-- part "The basis table": rdF_add_one, wRow_zero_getD … wtabIR_sem).
-- New for lvm (WP-13b); namespace `FR.X` → `Lvm.X`. Re-targeted from FR's two-word `F` and
-- domain `D` to lvm's one-word `K = BF64` and domain `ptK` (row `0` is the word `2^i`; element
-- stride 2 → 1, row stride 40 → 15, 20 rows of 20 → 15 of 15).
import LvmXNtt2

-- (GOLF2: 8 declarations that `certified` does not use moved verbatim to `LvmXSComputesOff`, outside its import closure.)

/-!
# The basis table on the machine

**`wtabIR_sem`**: `wtabIR tb` writes the rows `wRow ptK 15 v`, `v < 15`, at `tb + 15 v + i`
(`wtabIR_normW`: entry `(v, i)` is `Ŵ_v(ptK 2^i)`, `Lvm.Nb.wRow_spec`) and keeps the heap outside
`[tb, tb + 225)`. Row `0` is `ptK (2^i)` (`row0IR_sem`); row `j + 1` is
`R i (R i + 1) (b (b + 1))⁻¹` with `b = R (j + 1)` (`rowIR_sem`, LCH's recursion `wRow`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

theorem wK_add_one (a : Word) : wK (a ^^^ 1) = wK a + 1 := wK_xor a 1

theorem wf_row0Body : WF row0Body := by
  simp +decide only [row0Body, WF, Prim.dst, fG, rTa, uI, cTmp, and_true]

/-- `a + 1` on the machine: `fW := fU + 1`. -/
theorem plusOne_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rdK (semXIR I (.blk [.op .xor fW fU cOne]) s).M fW = rdK s.M fU + 1 ∧
    ∀ x, x ≠ fW → rd (semXIR I (.blk [.op .xor fW fU cOne]) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun x h1 => rd_runPrims_of_not_writes (by
    simp [Prim.dst]; exact Ne.symm h1) _⟩
  simp only [semXIR, runPrims, List.foldl, Prim.run, rdK]
  simp (disch := first | decide | (simp only [size_set, fW]; omega)) only [rd_set_self, rd_set_ne]
  rw [show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor]
  exact wK_add_one _

theorem wf_plusOne : WF (.blk [.op .xor fW fU cOne]) := by
  simp +decide only [WF, Prim.dst, fW]

end Lvm.X
