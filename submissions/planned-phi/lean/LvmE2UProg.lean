-- New for lvm2 U-TAPE (UT-V): V_S's twins of stage S2GU's front algebra over a field `F` (the statement layer is
-- `LvmS2GUFront`): `Ĩ_ks` with the pack bits' `eq` as one product (`ikEvalP`, `eqEvalF`), the `Y` and `M` blocks'
-- slot weights over any `F` (`yWG`, `mWG`; the statement's `yWF`/`mWF` are at `E2`).
import LvmE2VProg

/-!
# V_S's twins of the S2GU front's algebra

* **`ikEvalP ρ μ σ base`**: `LvmS2GUFront.ikEvalF` with `Σ_y eq(ρ', y)·eq(σ'', y)` as `eqEvalF ρ' σ''` (T-K's
  `ikEval`: `w − 4` products instead of a sum over `2^(w−4)` points);
* **`yWG ω`**, **`mWG ω`**: the slot weights of the `Y` block (lane `l < 25` in slot `l`) and of the stream block
  (message lane `l < 17` in column `l`), `W(l, z) = ω_{64l + z}`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters

section Alg

variable {F : Type} [Field F]

/-- **`Σ_{x<2^w} eq(σ, x)·ι(base + x)` over `F`** (T-K's `ikEval`, `w = |σ|`): the low digit's `μ` sum, `eq` of the
pack bits as one product, the bits of `base` above `w`. -/
def ikEvalP (ρ μ σ : List F) (base : ℕ) : F :=
  sumF ((List.range 16).map fun d => eqAtF (σ.take 4) d * μ.getD d 0) *
    eqEvalF (ρ.take (σ.length - 4)) (σ.drop 4) * eqAtF (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length)

/-- The `Y` block's slot weights: lane `l < 25` in slot `l`, `W(l, z) = ω_{64l + z}`; the slots above, `0`. -/
def yWG (ω : List F) (o z : ℕ) : F := if o < 25 then ω.getD (64 * o + z) 0 else 0

/-- The stream block's slot weights: message lane `l < 17` in column `l`, `W(l, z) = ω_{64l + z}` (the rate); the
columns above, `0`. -/
def mWG (ω : List F) (o z : ℕ) : F := if o < 17 then ω.getD (64 * o + z) 0 else 0

end Alg

end Lvm.E2V
