-- New for lvm6 (WP-PHIV3, lever G): the gather kind of `Φ_Q`'s class evaluator. A loop block's entries that no
-- class or run covers (per-iteration coefficients, irregular word reads: QLT's `CONST`s, Q_sig's BITS reads) sit
-- at slots `x₀ + j` (`x₀` aligned to `2^l`, `j < 2^l`): `eq(m, x₀ + j) = eq(m_lo, j)·eq(m_hi, x₀ / 2^l)`, the low
-- factor off the shared slot kernel. Per row two products, per high-word group one, per word (column) one, per line
-- one more at a coefficient `≠ 1` (PHIV4). Flat layout: groups, columns and lines are offset ranges into scalar
-- arrays; coefficients are indices into a table of the distinct ones.
import Lvm6PhiStrF

/-!
# The gather kind

* **`GK`** (`l`; rows `(x₀, o, g₀, g₁)` with groups `[g₀, g₁)`; group `h`: high word `gh[h]`, columns
  `[go[h], go[h+1])`; column `c`: low word `cw[c]`, lines `[co[c], co[c+1])`; line `t`: slot offset `lj[t]`,
  coefficient index `lk[t]` into the packed table `cv` (`rdE`; `0`: the coefficient `1`)), **`GK.ents`** (line
  `(coef t, o, x₀ + lj[t], cw[c] + 2^11·gh[h])`), **`GK.okB`** (start-up: `l ≤ 20`, `x₀` aligned, `cw < 2^11`,
  every line's `lj < 2^l`).
* `goSum` (a sum over an index range, `goSum_eq`); **`GK.valW`** (weights `fa`, `xlo = eq(m.take l, ·)`,
  `xhi = eq(m.drop l, ·)`, `ylo = eq(b.take 11, ·)`, `yhi = eq(b.drop 11, ·)`): per row
  `fa(o)·xhi(x₀/2^l)·Σ_h yhi(gh[h])·Σ_c ylo(cw[c])·Σ_t coef t·xlo(lj[t])`; **`GK.valW_eq`**: the sum of the
  entries' `qv`. PHIV4: a column costs one product (was two: `eq(b, y)` and the column sum), a group one.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-- `acc + Σ_{a ≤ i < b} f i`. -/
@[specialize] def goSum (f : ℕ → FE2) (a b : ℕ) (acc : FE2) : FE2 :=
  if a < b then goSum f (a + 1) b (acc + f a) else acc
termination_by b - a

theorem goSum_eq (f : ℕ → FE2) (b : ℕ) : ∀ (d a : ℕ) (acc : FE2), b - a = d →
    goSum f a b acc = acc + ((List.range' a (b - a)).map f).sum
  | 0, a, acc, hd => by
    rw [goSum, if_neg (by omega), hd]; simp
  | d + 1, a, acc, hd => by
    rw [goSum, if_pos (by omega), goSum_eq f b d (a + 1) _ (by omega),
      show b - a = (b - (a + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons, add_assoc]

/-- PHIV5: `c·v` by the coefficient's shape: `1` free, `X` a shift (`mX`), `c ∈ K` two `K` products (`mK`), else
three. -/
@[inline] def cmulK (c v : FE2) : FE2 :=
  if c.im.val = 0 then (if c.re.val = 1 then v else KT.mK v c.re)
  else if c.re.val = 0 ∧ c.im.val = 1 then KT.mX v else mulE c v

theorem cmulK_eq (c v : FE2) : cmulK c v = c * v := by
  obtain ⟨⟨r⟩, ⟨i⟩⟩ := c
  unfold cmulK
  dsimp only
  split
  · rename_i hi
    subst hi
    split
    · rename_i hr
      subst hr
      exact (one_mul v).symm
    · rw [KT.mK_eq, mul_comm]
      rfl
  · split
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := hx
      exact KT.mX_eq v
    · exact mulE_eq _ _

/-- A little-endian word at byte `o` (`0` past the end). -/
@[inline] def rd64 (a : ByteArray) (o : ℕ) : UInt64 :=
  if h : o + 8 ≤ a.size then
    a[o].toUInt64 ||| (a[o + 1].toUInt64 <<< 8) ||| (a[o + 2].toUInt64 <<< 16) ||| (a[o + 3].toUInt64 <<< 24) |||
      (a[o + 4].toUInt64 <<< 32) ||| (a[o + 5].toUInt64 <<< 40) ||| (a[o + 6].toUInt64 <<< 48) |||
      (a[o + 7].toUInt64 <<< 56)
  else 0

/-- Entry `k` of a packed table: sixteen bytes, `re` first (a contiguous table: no pointer per entry). -/
@[inline] def rdE (a : ByteArray) (k : ℕ) : FE2 := ⟨⟨rd64 a (16 * k)⟩, ⟨rd64 a (16 * k + 8)⟩⟩

/-- **A gather kind** (PHIV4: words split, columns grouped by their high word, coefficients by index): rows
`(x₀, o, g₀, g₁)` own the groups `[g₀, g₁)`; group `h` has the high word `gh[h]` and the columns `[go[h], go[h+1])`;
column `c` reads the word `cw[c] + 2^11·gh[h]` on its lines `[co[c], co[c+1])`; line `t` sits at the slot
`x₀ + lj[t]` with the coefficient `coef t` (`lk[t] = 0`: `1`, else entry `lk[t] − 1` of the packed table `cv`). -/
structure GK where
  l : ℕ
  rows : Array (ℕ × ℕ × ℕ × ℕ)
  gh : Array ℕ
  go : Array ℕ
  cw : Array ℕ
  co : Array ℕ
  lj : Array ℕ
  lk : Array ℕ
  cv : ByteArray
  deriving Inhabited

/-- Line `t`'s coefficient. -/
def GK.coef (g : GK) (t : ℕ) : FE2 := if g.lk.getD t 0 = 0 then 1 else rdE g.cv (g.lk.getD t 0 - 1)

/-- `coef t · v`, no product at index `0`. -/
@[inline] def GK.cmul (g : GK) (t : ℕ) (v : FE2) : FE2 :=
  let k := g.lk.getD t 0
  if k = 0 then v else cmulK (rdE g.cv (k - 1)) v

theorem GK.cmul_eq (g : GK) (t : ℕ) (v : FE2) : g.cmul t v = g.coef t * v := by
  unfold GK.cmul GK.coef
  by_cases h : g.lk.getD t 0 = 0
  · simp [h]
  · simp only [h, ↓reduceIte, cmulK_eq]

/-- The index range `[a[i], a[i+1])`. -/
def rg (a : Array ℕ) (i : ℕ) : List ℕ := List.range' (a.getD i 0) (a.getD (i + 1) 0 - a.getD i 0)

/-- **Its entries.** -/
def GK.ents (g : GK) : List Q4 :=
  g.rows.toList.flatMap fun r => (List.range' r.2.2.1 (r.2.2.2 - r.2.2.1)).flatMap fun h =>
    (rg g.go h).flatMap fun c => (rg g.co c).map fun t =>
      (g.coef t, r.2.1, r.1 + g.lj.getD t 0, g.cw.getD c 0 + 2 ^ 11 * g.gh.getD h 0)

/-- **Its start-up check**: the base slots aligned, every column's low word below `2^11`, every line's slot
offset below `2^l`. -/
def GK.okB (g : GK) : Bool :=
  decide (g.l ≤ 20) && g.rows.toList.all fun r => r.1 % 2 ^ g.l == 0 &&
    (List.range' r.2.2.1 (r.2.2.2 - r.2.2.1)).all fun h => (rg g.go h).all fun c =>
      decide (g.cw.getD c 0 < 2 ^ 11) && (rg g.co c).all fun t => decide (g.lj.getD t 0 < 2 ^ g.l)

/-- **Its value** with its weights (`xlo`, `xhi`: slot bits below and from `l`; `ylo`, `yhi`: word bits below and
from `11`): per row `fa(o)·xhi(x₀/2^l)·Σ_h yhi(gh[h])·Σ_c ylo(cw[c])·Σ_t coef t·xlo(lj[t])`: one product a column,
one a group, one a line at an index `≠ 0`. -/
@[specialize] def GK.valW (g : GK) (fa xlo xhi ylo yhi : ℕ → FE2) : FE2 :=
  g.rows.foldl (fun s r => s + mulE (mulE (fa r.2.1) (xhi (r.1 / 2 ^ g.l)))
    (goSum (fun h => mulE (yhi (g.gh.getD h 0))
      (goSum (fun c => mulE (ylo (g.cw.getD c 0))
        (goSum (fun t => g.cmul t (xlo (g.lj.getD t 0))) (g.co.getD c 0) (g.co.getD (c + 1) 0) 0))
        (g.go.getD h 0) (g.go.getD (h + 1) 0) 0))
      r.2.2.1 r.2.2.2 0)) 0

/-- **The gather kind is the sum of its entries.** -/
theorem GK.valW_eq (g : GK) (hok : g.okB = true) (fa : ℕ → FE2) (m b : List FE2) (hm : m.length = 20)
    (hb : b.length = 21) (xlo xhi ylo yhi : ℕ → FE2) (hlo : ∀ j, xlo j = eqAtF (m.take g.l) j)
    (hhi : ∀ v, xhi v = eqAtF (m.drop g.l) v) (hylo : ∀ w, w < 2 ^ 11 → ylo w = eqAtF (b.take 11) w)
    (hyhi : ∀ v, yhi v = eqAtF (b.drop 11) v) :
    g.valW fa xlo xhi ylo yhi = (g.ents.map (qv fa (eqAtF m) (eqAtF b))).sum := by
  simp only [GK.okB, rg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨hl, hrows⟩ := hok
  unfold GK.valW GK.ents rg
  rw [← Array.foldl_toList, foldl_add_eq, zero_add, sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  obtain ⟨hx, hhs⟩ := hrows r hr
  rw [goSum_eq _ _ _ _ _ rfl, zero_add, sum_map_flatMap, mulE_eq, mulE_eq, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun h hh => ?_)
  rw [goSum_eq _ _ _ _ _ rfl, zero_add, sum_map_flatMap, mulE_eq, ← List.sum_map_mul_left,
    ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun c hc => ?_)
  obtain ⟨hw, hcs⟩ := hhs h hh c hc
  rw [goSum_eq _ _ _ _ _ rfl, zero_add, mulE_eq, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
    ← List.sum_map_mul_left, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have hj := hcs t ht
  have h1 : (r.1 + g.lj.getD t 0) % 2 ^ g.l = g.lj.getD t 0 := by
    rw [Nat.add_mod, hx, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj]
  have h2 : (r.1 + g.lj.getD t 0) / 2 ^ g.l = r.1 / 2 ^ g.l := by
    obtain ⟨q, hq⟩ : 2 ^ g.l ∣ r.1 := Nat.dvd_of_mod_eq_zero hx
    rw [hq, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hj, add_zero, Nat.mul_div_cancel_left _ (by positivity)]
  have hx' : eqAtF m (r.1 + g.lj.getD t 0) =
      eqAtF (m.take g.l) (g.lj.getD t 0) * eqAtF (m.drop g.l) (r.1 / 2 ^ g.l) := by
    rw [← eq_ysplit m g.l (r.1 + g.lj.getD t 0) (by omega), h1, h2]
  have hy' := eq_split b 11 (g.cw.getD c 0) (g.gh.getD h 0) (by omega) hw
  simp only [Function.comp_apply, GK.cmul_eq, qv, hlo, hhi, hylo _ hw, hyhi, hx', hy']
  ring

end Lvm6.V
