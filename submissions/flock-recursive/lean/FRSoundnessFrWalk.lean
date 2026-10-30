-- New for `flock-recursive` (BLUEPRINT A.8 `walkAB`/`maskRows`/`rowW`, A.9 `finLc` (ii), revision
-- 3.16; stage S-G12′).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreWalk`.
import FRSoundnessFrLN
import FRSoundnessAccEq
import FRSoundnessLigerito
import FRVerifierImplOps
import FRVIRFinals
import FRVIRFinalsSG
import FRSoundnessCoreWalk

/-!
# The walk bridge: `finLc` (ii)'s walk is the lincheck's per-kind sum

The verifier's walk (A.8) evaluates `Â(rowW′, eq(r_k, ·)) + α B̂(rowW′, eq(r_k, ·))` with the row
weights masked per kind, `rowW′ = maskRows w rowW`. The soundness front states the lincheck's
last claim per kind, `Σ_j v′_j · M̃_j(r_k)` with `M_j = linM (zlmFR.Ak j) (zlmFR.Bk j) rowW α`.

* **`maskOf_eq`**: `maskOf w k = Σ_{j<9} [kind j does not pin row k] · w_j` (kinds in
  `blockKinds` order, as `zlmFR`'s `bkOf`).
* **`walk_bridge`** (spec level): with `w_free = 0`, the walk at the specification functions
  (`walkSpecA`/`walkSpecB`, `rowWS`, `eqTab`) is `Σ_j w_j · M̃_j(r_k)`.
* **`free_term`**: the `free` kind's column weight at `r_k` is `(1 + α)·lcFree`'s closed form
  (`FRSpartan.linM_free_mle` at `zlmFR`'s `free` matrix, which is the identity).

Controls: `maskOf_ctl` (row 0 is pinned by `chain`, so `w_chain` drops out there) and
`maskOf_ctl_neg` (row 300 is pinned by no kind but `chain`'s `0 … 255` does not cover it: every
weight counts).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

/-! ## `maskOf` as a sum over the kinds -/

/-! ## The walk at the specification -/

section Alg
variable {N : ℕ} {ι : Type*} [Fintype ι] (A B : Fin N → Fin N → Bool) (rw e : Fin N → F) (α : F)
  (zr : ι → Fin N → Bool) (w : ι → F)

end Alg

/-! ## The `free` term -/

/-! ## `finLc` (ii) at the verifier's registers -/

/-! ## Controls -/

/-- (+) **`maskOf` at row 0**: only `stream`, `streamEnd41`, `hashB2` and `free` leave row 0
unpinned, so only their weights count there. -/
theorem maskOf_row0 (w : Array F) :
    maskOf w 0 = w.getD 1 0 + w.getD 3 0 + w.getD 6 0 + w.getD 8 0 := by
  rw [maskOf_eq]
  simp [Fin.sum_univ_succ, bkOf, blockKinds, isZeroRow, zeroRows]
  ring

/-- (−) **The chain kind's weight is masked at its pinned row 0**: a weight on `chain` alone gives
`0` there (the unmasked walk would count it). -/
theorem maskOf_chain_row0 : maskOf (Array.ofFn fun j : Fin 9 => if j = 0 then (1 : F) else 0) 0 = 0 := by
  rw [maskOf_row0]; simp

/-- (+) **A leaf's weights**: `v₀` on `chain`, nothing at `free`. -/
theorem lcWts_leaf_ctl (v : List F) (hv : v.length = 8) (j : Fin 9) :
    (if j = 8 then 0 else (lcWts .L32 v).getD j 0) = if j.val = 0 then v.getD 0 0 else 0 := by
  have h := lcWts_vM .L32 hv 0 (by simp [Kind.isNode]) j
  rw [if_neg (by decide : ¬ Kind.L32.isNode = true)] at h
  exact h

end FR.Snd
