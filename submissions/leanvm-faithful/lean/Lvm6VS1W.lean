-- New for lvm6 (VS1): the kind test of a proof read off its byte array (`isSB = isS`), and `VwithT` behind it.
import Lvm6VWFast

/-!
# VS1: the kind test without a copy

`isS π` reads `π.data.getD 0 0`; `π.data` turns the proof's byte array into an `Array UInt8` (a boxed copy of
every byte, `lean_byte_array_data`), about 1 ms a check in VS1's profile. `isSB` reads byte `0` of the byte array
itself.

* **`isSB`**, **`isSB_eq : isSB π = isS π`**;
* **`VwithS VS`**: the `S` branch behind `isSB`, else `VwithT VS`; **`VwithS_eq : VwithS VS = VwithT VS`**.
-/

set_option autoImplicit false

namespace Lvm6.VTw

open RecursionFast Lvm.T

/-- **`isS` off the byte array**: byte `0` (`0` past the end) is `sByte`. -/
def isSB (π : Proof) : Bool := (if h : 0 < π.size then π[0] else 0) == sByte

theorem isSB_eq (π : Proof) : isSB π = isS π := by
  rcases π with ⟨d⟩
  simp only [isSB, isS, Array.getD_eq_getD_getElem?]
  split
  · rename_i h
    simp only [ByteArray.size] at h
    simp only [Array.getElem?_eq_getElem h, Option.getD_some]
    rfl
  · rename_i h
    simp only [ByteArray.size, Nat.not_lt, Nat.le_zero, Array.size_eq_zero_iff] at h
    simp [h]

/-- **`VwithT` behind the kind test `isSB`.** -/
def VwithS (VS : SProg) (vk c : Digest) (π : Proof) : OProg Bool :=
  if isSB π then VS vk c π else VwithT VS vk c π

theorem VwithS_eq (VS : SProg) : VwithS VS = VwithT VS := by
  funext vk c π
  unfold VwithS
  rw [isSB_eq]
  by_cases hS : isS π = true
  · simp only [hS, ite_true]
    rw [VwithT]
    simp only [hS, ite_true]
  · simp only [hS, Bool.false_eq_true, ite_false]

end Lvm6.VTw
