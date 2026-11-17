-- New for lvm2 σ_LEAF (SLF-C, variant C, lead decision D8): the leaf signature's constant digits and the chain order
-- `permC` in which the node stores `σ_leaf`'s chain values (shared with SLF-L's extractor).
import RecursionFast.Contract.Signature

/-!
# The leaf walk's digits and chain order

* **`dLeaf`**: the 133 WOTS digits of `traceDigest []` (written out; **`dLeaf_eq`**: they are
  `wotsDigits (traceDigest [])`, one Keccak in the kernel).
* **`grpC d`**: the chains of digit `d`; **`permC`**: digit `0`'s chains, then `1`'s, `2`'s, `3`'s; **`gOffC d`**: group
  `d`'s first position in `permC`; **`posC i`**: chain `i`'s position. **`permC_ok`**: `permC` lists every chain `< 133`
  once (`posC` inverts it).
-/

set_option autoImplicit false

namespace Lvm.QSig

/-- The digits the leaf signature signs (`traceDigest []`'s 133 WOTS digits, `dLeaf_eq`). -/
def dLeaf : List Nat :=
  [0, 1, 0, 2, 3, 2, 2, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 2, 2, 3, 0, 3, 1, 0, 2, 2, 3, 3, 1, 0, 1, 0,
    1, 3, 0, 0, 2, 3, 0, 0, 3, 1, 2, 2, 0, 3, 2, 3, 1, 0, 2, 1, 2, 0, 2, 1, 3, 1, 2, 2, 2, 0, 1, 0,
    3, 2, 3, 0, 2, 1, 3, 1, 3, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 3, 0, 2, 3, 1, 3, 2, 0, 3, 0, 0,
    2, 3, 0, 3, 1, 3, 2, 3, 1, 0, 1, 1, 3, 0, 0, 1, 0, 2, 1, 0, 3, 2, 3, 0, 1, 0, 1, 0, 0, 3, 3, 3,
    2, 0, 0, 3, 0]

/-- **`dLeaf` are the WOTS digits of `traceDigest []`.** -/
theorem dLeaf_eq : dLeaf = RecursionFast.wotsDigits (RecursionFast.traceDigest []) := by
  decide +kernel

/-- The chains of digit `d`, in order. -/
def grpC (d : Nat) : List Nat := (List.range 133).filter fun i => dLeaf.getD i 0 == d

/-- The chain order: digit `0`'s chains, then `1`'s, `2`'s, `3`'s. -/
def permC : List Nat := grpC 0 ++ grpC 1 ++ grpC 2 ++ grpC 3

/-- The first position of group `d` in `permC`. -/
def gOffC (d : Nat) : Nat := ((List.range d).map fun e => (grpC e).length).sum

/-- The position of chain `i` in `permC`. -/
def posC (i : Nat) : Nat := permC.idxOf i

/-- **`permC` is a permutation of the chains `< 133`**: it has 133 entries, each below 133, and `posC` inverts it. -/
theorem permC_ok : permC.length = 133 ∧ (List.range 133).all (fun i => posC i < 133 && permC.getD (posC i) 0 == i) = true ∧
    permC.all (· < 133) = true := by
  decide +kernel

end Lvm.QSig
