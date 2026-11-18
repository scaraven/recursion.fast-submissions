-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Field.lean` (formal rev 40f877dc) as `LvmProtoField` for lvm (WP-2).
import LvmFieldFacts
import LvmInnerProduct
import LvmMlBasic

-- (GOLF2: 3 declarations that `certified` does not use moved verbatim to `LvmM3MidOff`, outside its import closure.)

/-!
# Fields for the proof system

leanVM's columns take values in `K` and its challenges in `E`, the cubic extension of `K`. This
module keeps, of leanVM's `LeanVM.Protocol.Field`:

* `Column n`, the value table of a `K`-multilinear on `n` variables;
* the equivalences `finEquivK : Fin (2^64) ≃ K` and `limbsEquiv : Vector K 3 ≃ E`;
* `card_E`: `Fintype.card E = 2^192`, the one cardinality fact every error bound rewrites with;
* `answer_eqWeight`: pairing the equality kernel with a column evaluates its extension.

lvm cut (WP-2): leanVM's VCVio `SampleableType` samplers and ArkLib's `OracleInterface` instance
on `Column`. Uniform sampling is stated directly as sums over `Fintype E` (`card_E`), and the
inner-product oracle is `Weight.pair` (`LvmInnerProduct`).
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly

section

/-! ## Columns -/

/-- A column of height `2^n`: the values of a `K`-multilinear on the cube, low bit first. A
structure rather than an abbreviation so that its oracle interface below does not overlap
ArkLib's position-query interface on `Vector`. -/
structure Column (n : ℕ) where
  /-- The value table, CompPoly's hypercube representation. -/
  values : CMlPolynomialEval K n

/-! ## Sampling -/

/-- `|E| = 2^192`: the size of the challenge space in every error bound. -/
theorem card_E : Fintype.card E = 2 ^ 192 := BF64.card_ext3

/-! ## The inner-product oracle -/

end
end LeanVM.Protocol
