-- lvm6 EXF (DP6 §2 item 1, part 2): the operation walk of `trun_front` at `P17` (PORT17 X1), by kernel evaluation.
import Lvm6XFront6Run
import Lvm6LenP18
import Lvm6XTop

/-!
# The front's walk at `P17`

* **`zp6 i`**: the zero words before the leaf's in W1's row of level `i` (IDX.md: level 0's 64-word row is 18 zero
  words, then the 46 committed ones; levels 1–4 carry their 32 words).
* **`frontD`** (one `decide +kernel` over L1's memos): at `P17`, with the scheme's cap levels, occupied words, read widths and
  `tPD` openings, the walk's messages are the chain's (`msgs6` after the seed), every opening finds an empty
  buffer, the caps are `(ht6 i, zp6 i + occ6 i)` at π offset `8 (capW6 i − 5)` for `i < 5` (X5's `capW6`, now
  kernel-checked), and the scheme gives that shape the cap level `lv6 i` and `occ6 i` occupied words.
-/

set_option autoImplicit false

namespace Lvm6.X

/-- The zero words before the leaf's in level `i`'s row (`64 − 46` at level 0). -/
def zp6 : ℕ → ℕ
  | 0 => 18
  | _ => 0

/-- **The walk at `P17`** (PORT17 X1; over L1's memo literals `opsP17`, `schedP17`). -/
theorem frontD :
    (msgs6 P17).drop 1 = msgsOp (V.capOfL P17.levs) (V.occL P17.levs) tPD [] (V.widths (sched6 P17))
      (hdrLen P17) 0 (opsOf P17.levs (sched6 P17)) ∧
    contigOp (V.capOfL P17.levs) [] (V.widths (sched6 P17)) 0 (opsOf P17.levs (sched6 P17)) = true ∧
    capsOp (V.capOfL P17.levs) (V.occL P17.levs) tPD [] (V.widths (sched6 P17)) (hdrLen P17)
      (opsOf P17.levs (sched6 P17)) = (List.range 5).map (fun i => (ht6 i, zp6 i + occ6 i, 8 * (capW6 i - 5))) ∧
    (List.range 5).all (fun i => V.capOfL P17.levs (ht6 i) (zp6 i + occ6 i) == lv6 i &&
      V.occL P17.levs (ht6 i) (zp6 i + occ6 i) == occ6 i && 5 ≤ capW6 i) = true := by
  unfold msgs6
  rw [opsOf_P17, sched6_P17_eq]
  decide +kernel

/-- Level `i`'s shape at `P17`: cap level `lv6 i`, `occ6 i` occupied words. -/
theorem levD {i : ℕ} (hi : i < 5) : V.capOfL P17.levs (ht6 i) (zp6 i + occ6 i) = lv6 i ∧
    V.occL P17.levs (ht6 i) (zp6 i + occ6 i) = occ6 i ∧ 5 ≤ capW6 i := by
  have h := List.all_eq_true.1 frontD.2.2.2 i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Lvm6.X
