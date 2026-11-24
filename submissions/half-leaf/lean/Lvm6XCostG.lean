-- lvm6 X1 (PORT17): the descent's cost and the level budgets over any tree heights (`Lvm6XCost.descCost6`,
-- `Lvm6XLv18.lvB` with `ht6` a parameter), with the deployed ones at `ht6` (`rfl`; `ht6 = ht17` pointwise since PORT17) and the `P17`
-- numbers at `ht17`.
import Lvm6XGeo
import Lvm6XDescProg

/-!
# The descent's cost at any heights

* **`descLvlAt ht i m`**, **`descCostAt ht`**: `descLvl`, `descCost6` with the heights `ht` (`descLvl_eq`,
  `descCost6_eq`: `ht6` gives the deployed ones, by `rfl`). **`descCostAt_mono`**: any `|S|` within the domains costs
  at most `descCostAt ht`.
* At `P17` (`ht17 = 20, 19, 18, 17, 16`): **`descCost17_le`**: `descCostAt ht17 ≤ 2^44` (it is 12,031,155,739,006 `≈ 2^43.45`; `P18`'s is
  `≈ 2^44.6`, within `2^45`).
* **`lvBAt ht i R Ln G`** (`Lvm6XLv18.lvB` with the heights: `lvB i = lvBAt ht6 i` by `rfl`), **`budget17`**: the five levels at their actual rounds and
  columns (6 rounds and 191 columns at level 0, 4 and 128 at levels 1–4) and the level-0 map fit
  `descCostAt ht17 + 2^43` (`budgetD`'s statement at `ht17`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm6.FD

/-- One level's decoder cost at `|S| = m`, heights `ht`. -/
def descLvlAt (ht : ℕ → ℕ) (i m : ℕ) : ℕ :=
  rds i * lamCost (ht i + 1) (ht i) m + lns i * laneCost (ht i + 1) (ht i) m

/-- **The descent's cost** over the five levels at heights `ht`, at `|S| = 2^ht i`. -/
def descCostAt (ht : ℕ → ℕ) : ℕ :=
  descLvlAt ht 0 (2 ^ ht 0) + descLvlAt ht 1 (2 ^ ht 1) + descLvlAt ht 2 (2 ^ ht 2) + descLvlAt ht 3 (2 ^ ht 3) +
    descLvlAt ht 4 (2 ^ ht 4)

theorem descLvl_eq (i m : ℕ) : descLvl i m = descLvlAt ht6 i m := rfl

theorem descCost6_eq : descCost6 = descCostAt ht6 := rfl

theorem descLvlAt_mono (ht : ℕ → ℕ) (i : ℕ) {m m' : ℕ} (h : m ≤ m') : descLvlAt ht i m ≤ descLvlAt ht i m' :=
  Nat.add_le_add (Nat.mul_le_mul_left _ (lamCost_mono h)) (Nat.mul_le_mul_left _ (laneCost_mono h))

/-- **Any agreement sets within the domains** cost at most `descCostAt ht`. -/
theorem descCostAt_mono (ht m : ℕ → ℕ) (hm : ∀ i < 5, m i ≤ 2 ^ ht i) :
    descLvlAt ht 0 (m 0) + descLvlAt ht 1 (m 1) + descLvlAt ht 2 (m 2) + descLvlAt ht 3 (m 3) + descLvlAt ht 4 (m 4) ≤
      descCostAt ht :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (descLvlAt_mono ht 0 (hm 0 (by norm_num)))
    (descLvlAt_mono ht 1 (hm 1 (by norm_num)))) (descLvlAt_mono ht 2 (hm 2 (by norm_num))))
    (descLvlAt_mono ht 3 (hm 3 (by norm_num)))) (descLvlAt_mono ht 4 (hm 4 (by norm_num)))

theorem descLvl17_0 : descLvlAt ht17 0 (2 ^ ht17 0) ≤ 6000000000000 := by
  simp only [descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl17_1 : descLvlAt ht17 1 (2 ^ ht17 1) ≤ 4000000000000 := by
  simp only [descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl17_2 : descLvlAt ht17 2 (2 ^ ht17 2) ≤ 1900000000000 := by
  simp only [descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl17_3 : descLvlAt ht17 3 (2 ^ ht17 3) ≤ 850000000000 := by
  simp only [descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

theorem descLvl17_4 : descLvlAt ht17 4 (2 ^ ht17 4) ≤ 380000000000 := by
  simp only [descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC]
  norm_num

/-- **The descent at `P17` fits `2^44`.** -/
theorem descCost17_le : descCostAt ht17 ≤ 2 ^ 44 := by
  have := descLvl17_0; have := descLvl17_1; have := descLvl17_2; have := descLvl17_3; have := descLvl17_4
  simp only [descCostAt]; omega

/-- A level's bound at its actual rounds `R`, columns `Ln` and groups `G`, heights `ht` (`lvB` at `ht6`). -/
def lvBAt (ht : ℕ → ℕ) (i R Ln G : ℕ) : ℕ :=
  trCap + 4 + R * (lamCost (ht i + 1) (ht i) (2 ^ ht i) + 2 ^ 27 + 23) +
    Ln * (laneCost (ht i + 1) (ht i) (2 ^ ht i) + ldCap + 25 + 13 * 2 ^ ht i + 2 ^ (ht i + 13)) + 11 * G

/-- **The numbers at `P17`**: five levels at their actual rounds and columns, and `fin`, within
`descCostAt ht17 + 2^43`. -/
theorem budget17 :
    lvBAt ht17 0 6 191 6 + lvBAt ht17 1 4 128 1 + lvBAt ht17 2 4 128 1 + lvBAt ht17 3 4 128 1 +
      lvBAt ht17 4 4 128 1 + finCap + 5 ≤ descCostAt ht17 + 2 ^ 43 := by
  simp only [lvBAt, descCostAt, descLvlAt, rds, lns, ht17, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC,
    wtabC, trCap, ldCap, finCap]
  norm_num

end Lvm6.X
