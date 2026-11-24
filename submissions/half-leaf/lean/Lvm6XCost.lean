-- lvm6 X2 (part 2): the descent's cost at every level (X1's open item: `fd1_cost` at levels 1–4) and the
-- extractor's budget against the declared fuel `2^47 + 8192·t`. New.
import Lvm6XRead
import Lvm6FDCost

/-!
# The descent's cost and the budget

* **`descCost6`**: the decoder's cost over the five levels: per level `i`, `rds i` runs of `lamIR` (one a fold
  round) and `lns i` runs of `laneIR` (one a `K`-lane), on the level's domain `2^ht6 i` with the table
  dimension `ht6 i + 1` and `|S| ≤ 2^ht6 i` (costs are monotone in `|S|`, `lamCost_mono`, `laneCost_mono`).
  Level 0: six rounds, 130 lanes (62 `E`-lanes of rounds 2–6 and the six window lanes); levels 1–4: four
  rounds, at most 64 `K`-lanes a round (an over-count: the folded words have 16, 8, 4, 2 `E` entries).
* **`descCost6_le`**: `descCost6 ≤ 2^45` (it is `≈ 2^43.45` at `P17`, PORT17).
* **`descCost6_mono`**: any `|S|` within the domain costs at most `descCost6`.
* **`budget6`**: the five tree readers (`cost6_reads`, `≈ 2^37.44`), the descent, a constant part up to `2^44`
  and `8000` steps per tape word (index, chain, copies) fit `2^47 + 8192·t` (`fuel6` of `Lvm6Stmt`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm6.FD

/-- Fold rounds decoded at level `i`. -/
def rds : ℕ → ℕ
  | 0 => 6
  | _ => 4

/-- `K`-lanes decoded at level `i` (an upper bound at levels 1–4). -/
def lns : ℕ → ℕ
  | 0 => 130
  | _ => 256

/-- One level's decoder cost at `|S| = m`. -/
def descLvl (i m : ℕ) : ℕ :=
  rds i * lamCost (ht6 i + 1) (ht6 i) m + lns i * laneCost (ht6 i + 1) (ht6 i) m

/-- **The descent's cost** over the five levels, at `|S| = 2^ht6 i`. -/
def descCost6 : ℕ :=
  descLvl 0 (2 ^ ht6 0) + descLvl 1 (2 ^ ht6 1) + descLvl 2 (2 ^ ht6 2) + descLvl 3 (2 ^ ht6 3) +
    descLvl 4 (2 ^ ht6 4)

theorem descLvl_mono (i : ℕ) {m m' : ℕ} (h : m ≤ m') : descLvl i m ≤ descLvl i m' :=
  Nat.add_le_add (Nat.mul_le_mul_left _ (lamCost_mono h)) (Nat.mul_le_mul_left _ (laneCost_mono h))

/-- **Any agreement sets within the domains** cost at most `descCost6`. -/
theorem descCost6_mono (m : ℕ → ℕ) (hm : ∀ i < 5, m i ≤ 2 ^ ht6 i) :
    descLvl 0 (m 0) + descLvl 1 (m 1) + descLvl 2 (m 2) + descLvl 3 (m 3) + descLvl 4 (m 4) ≤ descCost6 :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (descLvl_mono 0 (hm 0 (by norm_num)))
    (descLvl_mono 1 (hm 1 (by norm_num)))) (descLvl_mono 2 (hm 2 (by norm_num))))
    (descLvl_mono 3 (hm 3 (by norm_num)))) (descLvl_mono 4 (hm 4 (by norm_num)))

theorem descLvl_0 : descLvl 0 (2 ^ ht6 0) ≤ 6000000000000 := by
  simp only [descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl_1 : descLvl 1 (2 ^ ht6 1) ≤ 4000000000000 := by
  simp only [descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl_2 : descLvl 2 (2 ^ ht6 2) ≤ 1900000000000 := by
  simp only [descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl_3 : descLvl 3 (2 ^ ht6 3) ≤ 850000000000 := by
  simp only [descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl_4 : descLvl 4 (2 ^ ht6 4) ≤ 380000000000 := by
  simp only [descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

/-- **The descent fits `2^45`** (`≈ 2^43.45` at `P17`; `2^44.60` at `P18`). -/
theorem descCost6_le : descCost6 ≤ 2 ^ 45 := by
  have := descLvl_0; have := descLvl_1; have := descLvl_2; have := descLvl_3; have := descLvl_4
  simp only [descCost6]; omega

/-- **The budget**: readers, descent, a constant part and `8000` steps a tape word fit the declared fuel. -/
theorem budget6 (bX pL : ℕ) (capW wB : ℕ → ℕ) (t d x : ℕ) (hd : d ≤ descCost6) (hx : x ≤ 2 ^ 44) :
    (List.range 5).foldr (fun i a => cost (read6IR i bX pL (capW i) (wB i)) t + a) 0 + d + x + 8000 * t ≤
      2 ^ 47 + 8192 * t := by
  rw [cost6_reads]
  have := descCost6_le
  omega

end Lvm6.X
