-- lvm6 X1 (PORT17): the openings at `P17` and the ties of the deployed front's heights and caps to `xg17`.
import Lvm6XGeo
import Lvm6XFront6P18
import Lvm6P17Memo

/-!
# The front's walk at `P17`

* **`tP17 i`**: the openings of level `i` at `P17` (110, 45, 28, 21, 18); `tPD_eq_tP17` (W1's `tPD` at `P17`).
* The walk itself is the deployed `frontD` (`Lvm6XFront6P18`, at `P17` since PORT17 X1): its caps are
  `(ht6 i, zp6 i + occ6 i)` at `8 (capW6 i − 5)`, and `ht6_eq_ht17`, `capW6_eq_capW17` tie them to `xg17`.
* `chainOK6_P17`, `nCh6_P17`, `contig6_P17` (1,055 chain targets `< 2^11`) live in `Lvm6XChain`.
-/

set_option autoImplicit false

namespace Lvm6.X

/-- The openings of level `i` at `P17`. -/
def tP17 (i : ℕ) : ℕ := (P17.levs.getD i default).t

/-- The deployed heights and caps are the `P17` ones (`frontD` checks them against the schedule). -/
theorem ht6_eq_ht17 : ∀ i, ht6 i = ht17 i
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

theorem capW6_eq_capW17 : ∀ i, capW6 i = capW17 i
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

theorem tPD_eq_tP17 : tPD = tP17 := rfl

end Lvm6.X
