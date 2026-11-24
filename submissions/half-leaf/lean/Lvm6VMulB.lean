-- New for lvm6 (MUL, VQ's lever B1): a cheaper `E2` product for V. `KT.m2` takes nine `clmul32` (144 integer
-- multiplies); `m2B` takes six `bmul64` (96) and seven bit reversals. `m2B_eq`: it is `KT.m2`.
import LvmE2VPhiT
import LvmFieldKCorrect

/-!
# The `E2` product on 64-bit low halves

* `bmul64 x y`: the low word of the carry-less product of two words, with sixteen integer products (the
  operands split into the bits of each residue class mod 4, as `FK.clmul32`, BearSSL's `bmul64`).
  **`bmul64_eq_lo`**: it is `(FK.clmul64 x y).lo`.
* `rev64`: the bit reversal of a word. **`clmul64_hi_eq`**: the high word of the carry-less product is the
  reversed low word of the reversed operands' product, shifted right once.
* **`m2B`**, **`m2B_eq`**: `KT.m2` with both, `m2B a b = KT.m2 a b` (`m2B_fun` under binders).

## How `bmul64` is proved

As `clmul32` (`LvmFieldKCorrect`): a word is the value at `2` of the `ℕ`-polynomial of its bits (`bpN`); the
product of the class-`r` part of `x` and the class-`s` part of `y` has its coefficients at positions `≡ r + s`.
Below position `60` every coefficient is at most `15` (at most one term per four positions), so a coefficient
never carries into the next position of its class below bit `64` (`testBit_eval_two_sparse`); the carry out of
position `60` (a coefficient `16`) lands at bit `64`, which the word product drops.

## How the reversal is proved

The word polynomials have degree `≤ 63`; the reversal is `reflect 63` (`P_rev64`), and Mathlib's `reflect_mul`
turns the product of the reflections into the reflection of the product at `126`.
-/

set_option autoImplicit false

namespace Lvm6.V

open Polynomial Lvm Lvm.FK

/-! ## The words -/

/-- The low word of the carry-less product of two words: the bits of each class mod 4, sixteen integer products. -/
@[inline] def bmul64 (x y : UInt64) : UInt64 :=
  let x0 := x &&& 0x1111111111111111
  let x1 := x &&& 0x2222222222222222
  let x2 := x &&& 0x4444444444444444
  let x3 := x &&& 0x8888888888888888
  let y0 := y &&& 0x1111111111111111
  let y1 := y &&& 0x2222222222222222
  let y2 := y &&& 0x4444444444444444
  let y3 := y &&& 0x8888888888888888
  (((x0 * y0) ^^^ (x1 * y3) ^^^ (x2 * y2) ^^^ (x3 * y1)) &&& 0x1111111111111111) |||
    (((x0 * y1) ^^^ (x1 * y0) ^^^ (x2 * y3) ^^^ (x3 * y2)) &&& 0x2222222222222222) |||
    (((x0 * y2) ^^^ (x1 * y1) ^^^ (x2 * y0) ^^^ (x3 * y3)) &&& 0x4444444444444444) |||
    (((x0 * y3) ^^^ (x1 * y2) ^^^ (x2 * y1) ^^^ (x3 * y0)) &&& 0x8888888888888888)

/-- The bit reversal of a word: swap bits, pairs, nibbles, bytes, half-words and words. -/
@[inline] def rev64 (x : UInt64) : UInt64 :=
  let x := ((x &&& 0x5555555555555555) <<< 1) ||| ((x >>> 1) &&& 0x5555555555555555)
  let x := ((x &&& 0x3333333333333333) <<< 2) ||| ((x >>> 2) &&& 0x3333333333333333)
  let x := ((x &&& 0x0F0F0F0F0F0F0F0F) <<< 4) ||| ((x >>> 4) &&& 0x0F0F0F0F0F0F0F0F)
  let x := ((x &&& 0x00FF00FF00FF00FF) <<< 8) ||| ((x >>> 8) &&& 0x00FF00FF00FF00FF)
  let x := ((x &&& 0x0000FFFF0000FFFF) <<< 16) ||| ((x >>> 16) &&& 0x0000FFFF0000FFFF)
  (x <<< 32) ||| (x >>> 32)

/-- **The `E2` product on `bmul64`**: `KT.m2`'s three carry-less products, each low word by `bmul64`, each high
word as the reversed low word of the reversed operands (`h0`, `h1`, `hm`; the reversal is `xor`-linear, so the
high words' sums are reversed once). -/
@[inline] def m2B (a b : FE2) : FE2 :=
  let ar := a.re.val; let ai := a.im.val; let br := b.re.val; let bi := b.im.val
  let l0 := bmul64 ar br
  let l1 := bmul64 ai bi
  let lm := bmul64 (ar ^^^ ai) (br ^^^ bi)
  let rar := rev64 ar; let rai := rev64 ai; let rbr := rev64 br; let rbi := rev64 bi
  let h0 := bmul64 rar rbr
  let h1 := bmul64 rai rbi
  let hm := bmul64 (rar ^^^ rai) (rbr ^^^ rbi)
  let rl := l0 ^^^ l1
  let rh := rev64 (h0 ^^^ h1) >>> 1
  let p1h := rev64 h1 >>> 1
  let mh := rev64 (hm ^^^ h0 ^^^ h1) >>> 1
  ⟨⟨FK.reduce rl rh⟩, ⟨FK.reduce (lm ^^^ rl ^^^ (l1 <<< 1)) (mh ^^^ ((p1h <<< 1) ||| (l1 >>> 63)))⟩⟩

/-! ## Words as polynomials -/

theorem coeff_P (w : UInt64) (n : ℕ) : (P w).coeff n = if w.toBitVec.getLsbD n then 1 else 0 := by
  rw [P, BinaryField.toPoly_coeff]
  by_cases h : n < 64
  · simp [h, BitVec.getLsb, BitVec.getLsbD]
  · simp [h, BitVec.getLsbD_of_ge w.toBitVec n (by omega)]

theorem coeff_P_of_ge (w : UInt64) {n : ℕ} (hn : 64 ≤ n) : (P w).coeff n = 0 := by
  rw [coeff_P, BitVec.getLsbD_of_ge _ _ hn]; rfl

theorem natDegree_P_le (w : UInt64) : (P w).natDegree ≤ 63 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun n hn => coeff_P_of_ge w (by
    omega)

theorem P_inj {a b : UInt64} (h : P a = P b) : a = b := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have hc := congrArg (fun p => p.coeff i) h
  simp only [coeff_P] at hc
  revert hc
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> simp

theorem coeff_P_shiftRight_one (w : UInt64) (n : ℕ) : (P (w >>> 1)).coeff n = (P w).coeff (n + 1) := by
  have hs : (w >>> 1).toBitVec = w.toBitVec >>> 1 := by simp
  rw [coeff_P, coeff_P, hs, BitVec.getLsbD_ushiftRight, Nat.add_comm 1 n]

/-- The low word of `clmul64` holds the product's coefficients below `64`. -/
theorem coeff_clmul64_lo (x y : UInt64) {n : ℕ} (hn : n < 64) :
    (P (FK.clmul64 x y).lo).coeff n = (P x * P y).coeff n := by
  rw [← P_clmul64, coeff_add, coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h => absurd h (by omega)), add_zero]

/-- The high word of `clmul64` holds the product's coefficients from `64` on. -/
theorem coeff_clmul64_hi (x y : UInt64) (n : ℕ) :
    (P (FK.clmul64 x y).hi).coeff n = (P x * P y).coeff (n + 64) := by
  rw [← P_clmul64, coeff_add, coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
    coeff_P_of_ge (FK.clmul64 x y).lo (n := n + 64) (by omega), zero_add, Nat.add_sub_cancel]

/-! ## `bmul64`: the integer products of the residue classes

Proof help, after `LvmFieldKCorrect`'s `clmul32` section with full words (positions below `64`) and the word
product's truncation. -/

private theorem eval_two_divX (D : ℕ[X]) : D.eval 2 = 2 ^ 1 * (divX D).eval 2 + D.coeff 0 := by
  conv_lhs => rw [← divX_mul_X_add D]
  simp only [eval_add, eval_mul, eval_X, eval_C]; ring

/-- A polynomial with coefficients below `2` evaluates at `2` to the number with those bits. -/
private theorem testBit_eval_two_dense (n : ℕ) : ∀ (D : ℕ[X]), (∀ k, D.coeff k < 2) →
    (D.eval 2).testBit n = decide (D.coeff n = 1) := by
  induction n with
  | zero =>
    intro D h
    rw [eval_two_divX, Nat.testBit_two_pow_mul_add _ (h 0)]
    rw [ite_eq_left (by norm_num), Nat.testBit_zero]
    rcases (by have := h 0; (clear * - this; omega) : D.coeff 0 = 0 ∨ D.coeff 0 = 1) with h' | h' <;> simp [h']
  | succ n ih =>
    intro D h
    rw [eval_two_divX, Nat.testBit_two_pow_mul_add _ (h 0), ite_eq_right (by (clear * -; omega)),
      Nat.add_sub_cancel, ih _ fun k => by rw [coeff_divX]; exact h _, coeff_divX]

/-- **Bit `n` of a sparse polynomial's value at `2`** is its coefficient's parity, when the coefficients sit at
positions of `n`'s class mod 4 and those at least four below `n` are below `16` (no carry reaches `n`). -/
private theorem testBit_eval_two_sparse (n : ℕ) : ∀ (D : ℕ[X]) (t : ℕ), (∀ k, k + 4 ≤ n → D.coeff k < 16) →
    (∀ k, D.coeff k ≠ 0 → k % 4 = t) → n % 4 = t →
    (D.eval 2).testBit n = decide (D.coeff n % 2 = 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D t hb hs hn
  by_cases h0 : D.coeff 0 = 0
  · rw [eval_two_divX, h0, Nat.testBit_two_pow_mul_add _ (show 0 < 2 ^ 1 by norm_num)]
    split_ifs with hlt
    · obtain rfl : n = 0 := by (clear * - hn hlt; omega)
      simp [h0]
    · rw [ih (n - 1) (by (clear * - hn hlt; omega)) (divX D) ((t + 3) % 4)
          (fun k hk => by rw [coeff_divX]; exact hb _ (by (clear * - hk hlt; omega)))
          (fun k hk => by rw [coeff_divX] at hk; have := hs _ hk; (clear * - this; omega)) (by (clear * - hn hlt; omega)),
        coeff_divX, Nat.sub_add_cancel (by (clear * - hn hlt; omega))]
  · have ht : t = 0 := by have := hs 0 h0; (clear * - this; omega)
    have z : ∀ k, k % 4 ≠ 0 → D.coeff k = 0 := fun k hk => by
      by_contra hne; exact hk (by rw [hs k hne, ht])
    set D4 := divX (divX (divX (divX D)))
    have c4 : ∀ k, D4.coeff k = D.coeff (k + 4) := fun k => by simp only [D4, coeff_divX]
    have e : D.eval 2 = 2 ^ 4 * D4.eval 2 + D.coeff 0 := by
      rw [eval_two_divX D, eval_two_divX (divX D), eval_two_divX (divX (divX D)),
        eval_two_divX (divX (divX (divX D)))]
      simp only [coeff_divX, z 1 (by decide), z 2 (by decide), z 3 (by decide)]
      ring
    by_cases hn0 : n = 0
    · subst hn0
      rw [e, Nat.testBit_zero, show (2 ^ 4 * D4.eval 2 + D.coeff 0) % 2 = D.coeff 0 % 2 by omega]
    rw [e, Nat.testBit_two_pow_mul_add _ (hb 0 (by (clear * - hn ht hn0; omega)))]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by (clear * - hn ht hn0; omega))),
      ih (n - 4) (by (clear * - hn ht hn0; omega)) D4 0
        (fun k hk => by rw [c4]; exact hb _ (by (clear * - hk; omega)))
        (fun k hk => by rw [c4] at hk; have := hs _ hk; (clear * - ht this; omega)) (by (clear * - hn ht hn0; omega)), c4,
      Nat.sub_add_cancel (by (clear * - hn ht hn0; omega))]

/-- The `ℕ`-polynomial of the bits of `u` below `2^64`. -/
private noncomputable def bpN (u : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range 64, monomial i (if u.testBit i then 1 else 0)

private theorem coeff_bpN (u n : ℕ) : (bpN u).coeff n = if n < 64 ∧ u.testBit n then 1 else 0 := by
  rw [bpN, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range 64) n (fun i => if u.testBit i then 1 else 0)]
  simp only [Finset.mem_range]
  by_cases hn : n < 64 <;> simp [hn]

private theorem testBit_lt_of_lt {x k : ℕ} (hx : x < 2 ^ k) {i : ℕ} (hi : k ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

private theorem eval_bpN {u : ℕ} (hu : u < 2 ^ 64) : (bpN u).eval 2 = u :=
  Nat.eq_of_testBit_eq fun n => by
    rw [testBit_eval_two_dense n _ (fun k => by rw [coeff_bpN]; split_ifs <;> (clear * -; omega)), coeff_bpN]
    by_cases hn : n < 64
    · by_cases hb : u.testBit n <;> simp [hn, hb]
    · simp [hn, testBit_lt_of_lt hu (show 64 ≤ n by (clear * - hn; omega))]

/-- `u` has bits only at positions `≡ r (mod 4)`. -/
private def Holes (u r : ℕ) : Prop := ∀ i, u.testBit i = true → i % 4 = r

private theorem Holes.coeff_le {u r : ℕ} (h : Holes u r) (i : ℕ) :
    (bpN u).coeff i ≤ if i % 4 = r then 1 else 0 := by
  rw [coeff_bpN]
  split_ifs with h1 h2 <;> first | omega | exact absurd (h i h1.2) h2

private theorem support_holes {u v r s : ℕ} (hu : Holes u r) (hv : Holes v s) {n : ℕ}
    (h : (bpN u * bpN v).coeff n ≠ 0) : n % 4 = (r + s) % 4 := by
  rw [coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_bpN, coeff_bpN] at hne
  split_ifs at hne with h1 h2
  · have r1 := hu _ h1.2; have s1 := hv _ h2.2; (clear * - hx r1 s1; omega)
  all_goals simp at hne

/-- Below position `60` a coefficient of a class product counts at most fifteen terms. -/
private theorem coeff_holes_lt {u v r : ℕ} (hu : Holes u r) (hr : r < 4) {n : ℕ} (hn : n < 60) :
    (bpN u * bpN v).coeff n < 16 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (bpN u).coeff i *
    (bpN v).coeff j)]
  calc ∑ i ∈ Finset.range n.succ, (bpN u).coeff i * (bpN v).coeff (n - i)
      ≤ ∑ i ∈ Finset.range n.succ, if i % 4 = r then 1 else 0 :=
        Finset.sum_le_sum fun i _ => by
          have h1 := hu.coeff_le i
          have h2 : (bpN v).coeff (n - i) ≤ 1 := by rw [coeff_bpN]; split_ifs <;> (clear * -; omega)
          calc (bpN u).coeff i * (bpN v).coeff (n - i) ≤ (bpN u).coeff i * 1 :=
                Nat.mul_le_mul_left _ h2
            _ ≤ _ := by rw [Nat.mul_one]; exact h1
    _ ≤ ∑ i ∈ Finset.range 60, if i % 4 = r then 1 else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => by simp only [Finset.mem_range] at hi ⊢; (clear * - hi hn; omega)) (fun _ _ _ => Nat.zero_le _)
    _ < 16 := by
        rcases (by (clear * - hr; omega) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> decide

/-- **The integer product of two words with holes**, read below bit `64` at the positions of its residue class,
is the carry-less product. -/
private theorem testBit_mul_holes {u v r s : ℕ} (hu : Holes u r) (hv : Holes v s) (hr : r < 4)
    (hu64 : u < 2 ^ 64) (hv64 : v < 2 ^ 64) {n : ℕ} (hn64 : n < 64) (hn : n % 4 = (r + s) % 4) :
    (u * v).testBit n = decide ((bpN u * bpN v).coeff n % 2 = 1) := by
  have e : u * v = (bpN u * bpN v).eval 2 := by rw [eval_mul, eval_bpN hu64, eval_bpN hv64]
  rw [e]
  exact testBit_eval_two_sparse n _ ((r + s) % 4)
    (fun k hk => coeff_holes_lt (v := v) hu hr (by (clear * - hk hn64; omega)))
    (fun k hk => support_holes hu hv hk) hn

/-- The bits of a constant below `2^k`, from its bits below `k`. -/
private theorem testBit_const {m k : ℕ} {p : ℕ → Bool} (hm : m < 2 ^ k)
    (h : ∀ i < k, m.testBit i = p i) (hp : ∀ i, k ≤ i → p i = false) (i : ℕ) :
    m.testBit i = p i := by
  by_cases hi : i < k
  · exact h i hi
  · rw [hp i (by (clear * - hi; omega)), testBit_lt_of_lt hm (by (clear * - hi; omega))]

/-- The class masks: bits `≡ r (mod 4)`. -/
private def mask : ℕ → ℕ
  | 0 => 0x1111111111111111
  | 1 => 0x2222222222222222
  | 2 => 0x4444444444444444
  | _ => 0x8888888888888888

private theorem testBit_mask {r : ℕ} (hr : r < 4) (i : ℕ) :
    (mask r).testBit i = decide (i % 4 = r ∧ i < 64) := by
  refine testBit_const (k := 64) (p := fun i => decide (i % 4 = r ∧ i < 64)) ?_ ?_
    (fun i hi => by simp; (clear * - hi; omega)) i <;>
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> decide

private theorem holes_mask (u : ℕ) {r : ℕ} (hr : r < 4) : Holes (u &&& mask r) r := by
  intro i hi
  rw [Nat.testBit_and, testBit_mask hr, Bool.and_eq_true, decide_eq_true_eq] at hi
  exact hi.2.1

private theorem bpN_split (x : ℕ) : bpN x = ∑ r ∈ Finset.range 4, bpN (x &&& mask r) := by
  ext i
  rw [finsetSum_coeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, coeff_bpN, Nat.testBit_and,
    testBit_mask (r := 0) (by norm_num), testBit_mask (r := 1) (by norm_num),
    testBit_mask (r := 2) (by norm_num), testBit_mask (r := 3) (by norm_num)]
  by_cases hb : x.testBit i
  · by_cases hi : i < 64
    · simp only [hb, hi, and_true, Bool.true_and, decide_eq_true_eq, true_and]
      split_ifs <;> omega
    · simp [hi]
  · simp [hb]

private theorem coeff_mul_split (x y : ℕ) (n : ℕ) :
    (bpN x * bpN y).coeff n =
      ∑ r ∈ Finset.range 4, (bpN (x &&& mask r) * bpN (y &&& mask ((n + 4 - r) % 4))).coeff n := by
  rw [bpN_split x, bpN_split y, Finset.sum_mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [finsetSum_coeff]
  refine Finset.sum_eq_single_of_mem _ (by simp; (clear * -; omega)) fun s hs hne => ?_
  rw [Finset.mem_range] at hs
  by_contra h
  have := support_holes (holes_mask x hr) (holes_mask y hs) h
  omega

private theorem decide_odd_add (a b : ℕ) :
    decide ((a + b) % 2 = 1) = (decide (a % 2 = 1) ^^ decide (b % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;> simp [Nat.add_mod, h, h']

private theorem prod_bit (x y : UInt64) {r s : ℕ} (hr : r < 4) (hs : s < 4) {mr ms : UInt64}
    (hmr : mr.toNat = mask r) (hms : ms.toNat = mask s) {n : ℕ} (hn64 : n < 64) (hn : n % 4 = (r + s) % 4) :
    ((x &&& mr) * (y &&& ms)).toNat.testBit n =
      decide ((bpN (x.toNat &&& mask r) * bpN (y.toNat &&& mask s)).coeff n % 2 = 1) := by
  rw [UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_and, hmr, hms, Nat.testBit_mod_two_pow,
    decide_eq_true hn64, Bool.true_and]
  exact testBit_mul_holes (holes_mask _ hr) (holes_mask _ hs) hr
    (lt_of_le_of_lt Nat.and_le_left x.toNat_lt) (lt_of_le_of_lt Nat.and_le_left y.toNat_lt) hn64 hn

/-- One residue class of the low word: the four integer products whose classes add up to `t`. -/
private theorem z_bit (x y : UInt64) {n t : ℕ} (hn64 : n < 64) (ht : n % 4 = t) {m0 m1 m2 m3 : UInt64}
    (h0 : m0.toNat = mask ((t + 4) % 4)) (h1 : m1.toNat = mask ((t + 3) % 4))
    (h2 : m2.toNat = mask ((t + 2) % 4)) (h3 : m3.toNat = mask ((t + 1) % 4)) :
    ((x &&& 0x1111111111111111) * (y &&& m0) ^^^ (x &&& 0x2222222222222222) * (y &&& m1) ^^^
      (x &&& 0x4444444444444444) * (y &&& m2) ^^^ (x &&& 0x8888888888888888) * (y &&& m3)).toNat.testBit n =
      decide ((bpN x.toNat * bpN y.toNat).coeff n % 2 = 1) := by
  simp only [UInt64.toNat_xor, Nat.testBit_xor]
  rw [prod_bit x y (r := 0) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h0 hn64 (by (clear * - ht; omega)),
    prod_bit x y (r := 1) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h1 hn64 (by (clear * - ht; omega)),
    prod_bit x y (r := 2) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h2 hn64 (by (clear * - ht; omega)),
    prod_bit x y (r := 3) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h3 hn64 (by (clear * - ht; omega)),
    coeff_mul_split x.toNat y.toNat]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, decide_odd_add]
  rw [show (n + 4 - 0) % 4 = (t + 4) % 4 by (clear * - ht; omega), show (n + 4 - 1) % 4 = (t + 3) % 4 by (clear * - ht; omega),
    show (n + 4 - 2) % 4 = (t + 2) % 4 by (clear * - ht; omega), show (n + 4 - 3) % 4 = (t + 1) % 4 by (clear * - ht; omega)]

private theorem testBit_maskOut {t : ℕ} (ht : t < 4) {n : ℕ} (hn : n < 64) :
    (mask t).testBit n = decide (n % 4 = t) := by
  rw [testBit_mask ht]; simp [hn]

private theorem or4_bit (z0 z1 z2 z3 : UInt64) {n : ℕ} (hn : n < 64) :
    ((z0 &&& 0x1111111111111111) ||| (z1 &&& 0x2222222222222222) |||
      (z2 &&& 0x4444444444444444) ||| (z3 &&& 0x8888888888888888)).toNat.testBit n =
    ((decide (n % 4 = 0) && z0.toNat.testBit n) || (decide (n % 4 = 1) && z1.toNat.testBit n) ||
      (decide (n % 4 = 2) && z2.toNat.testBit n) ||
      (decide (n % 4 = 3) && z3.toNat.testBit n)) := by
  simp only [UInt64.toNat_or, UInt64.toNat_and, Nat.testBit_or, Nat.testBit_and]
  rw [show (0x1111111111111111 : UInt64).toNat = mask 0 from rfl,
    show (0x2222222222222222 : UInt64).toNat = mask 1 from rfl,
    show (0x4444444444444444 : UInt64).toNat = mask 2 from rfl,
    show (0x8888888888888888 : UInt64).toNat = mask 3 from rfl,
    testBit_maskOut (by norm_num) hn, testBit_maskOut (by norm_num) hn,
    testBit_maskOut (by norm_num) hn, testBit_maskOut (by norm_num) hn]
  simp only [Bool.and_comm]

/-- **The bits of `bmul64`** below `64` are the coefficients of the carry-less product. -/
private theorem testBit_bmul64 (x y : UInt64) {n : ℕ} (hn : n < 64) :
    (bmul64 x y).toNat.testBit n = decide ((bpN x.toNat * bpN y.toNat).coeff n % 2 = 1) := by
  simp only [bmul64]
  rw [or4_bit _ _ _ _ hn]
  rcases (by (clear * -; omega) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
    simp only [h, Nat.reduceEqDiff, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_or, Bool.or_false] <;>
    refine z_bit x y hn h ?_ ?_ ?_ ?_ <;> rfl

private theorem P_eq_map (w : UInt64) : P w = (bpN w.toNat).map (Nat.castRingHom (ZMod 2)) := by
  ext n
  rw [coeff_map, coeff_bpN, coeff_P]
  change (if w.toNat.testBit n then _ else _) = _
  by_cases hn : n < 64
  · by_cases hb : w.toNat.testBit n <;> simp [hn, hb]
  · rw [testBit_lt_of_lt w.toNat_lt (by omega)]; simp [hn]

/-- **`bmul64` is the low word of the carry-less product.** -/
theorem bmul64_eq_lo (x y : UInt64) : bmul64 x y = (FK.clmul64 x y).lo := by
  apply P_inj
  ext n
  by_cases hn : n < 64
  · rw [coeff_clmul64_lo x y hn, P_eq_map x, P_eq_map y, ← Polynomial.map_mul, coeff_map, coeff_P]
    change (if (bmul64 x y).toNat.testBit n then _ else _) = _
    rw [testBit_bmul64 x y hn]
    generalize (bpN x.toNat * bpN y.toNat).coeff n = c
    show _ = (c : ZMod 2)
    rw [← ZMod.natCast_mod]
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]
  · rw [coeff_P_of_ge _ (by omega), coeff_P_of_ge _ (by omega)]

/-! ## The reversal -/

/-- One swap stage of `rev64`: bit `j` of the result is bit `j + c` or `j - c` of the input, by `j`'s position
in its block of `2 c`. -/
private def swapIx (c j : ℕ) : ℕ := if j % (2 * c) < c then j + c else j - c

private theorem swap_stage (c : ℕ) (s m : UInt64) (f : ℕ → ℕ) (x y : UInt64)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j = x.toBitVec.getLsbD (f j))
    (hs : s.toNat % 64 = c)
    (hm : ∀ j < 64, m.toBitVec.getLsbD j = decide (j % (2 * c) < c))
    (hc : ∀ j < 64, swapIx c j < 64 ∧ (j % (2 * c) < c → c ≤ j → ¬ (j - c) % (2 * c) < c) ∧
      (¬ j % (2 * c) < c → c ≤ j ∧ (j - c) % (2 * c) < c)) :
    ∀ j < 64, (((y &&& m) <<< s) ||| ((y >>> s) &&& m)).toBitVec.getLsbD j =
      x.toBitVec.getLsbD (f (swapIx c j)) := by
  intro j hj
  have hsl : ((y &&& m) <<< s).toBitVec = (y &&& m).toBitVec <<< c := by simp [hs]
  have hsr : (y >>> s).toBitVec = y.toBitVec >>> c := by simp [hs]
  obtain ⟨hlt, h1, h2⟩ := hc j hj
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, hsl, hsr, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hm j hj]
  by_cases hmc : j % (2 * c) < c
  · have e : swapIx c j = j + c := by simp only [swapIx, hmc, ↓reduceIte]
    rw [e] at hlt ⊢
    rw [← hy _ hlt]
    by_cases hcj : c ≤ j
    · rw [hm (j - c) (by omega)]
      simp [hmc, h1 hmc hcj, Nat.add_comm c j]
    · simp [hmc, show j < c by omega, Nat.add_comm c j]
  · obtain ⟨hcj, h3⟩ := h2 hmc
    have e : swapIx c j = j - c := by simp only [swapIx, hmc, ↓reduceIte]
    rw [e] at hlt ⊢
    rw [← hy _ hlt, hm (j - c) (by omega)]
    simp [hmc, h3, hj, show ¬ j < c by omega]

private theorem rot_stage (x y : UInt64) (f : ℕ → ℕ)
    (hy : ∀ j < 64, y.toBitVec.getLsbD j = x.toBitVec.getLsbD (f j)) :
    ∀ j < 64, ((y <<< 32) ||| (y >>> 32)).toBitVec.getLsbD j = x.toBitVec.getLsbD (f (swapIx 32 j)) := by
  intro j hj
  have hsl : (y <<< 32).toBitVec = y.toBitVec <<< 32 := by simp
  have hsr : (y >>> 32).toBitVec = y.toBitVec >>> 32 := by simp
  simp only [UInt64.toBitVec_or, hsl, hsr, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · have e : swapIx 32 j = j + 32 := by simp only [swapIx, show j % (2 * 32) < 32 by omega, ↓reduceIte]
    rw [e, ← hy (j + 32) (by omega)]
    simp [h, Nat.add_comm 32 j]
  · have e : swapIx 32 j = j - 32 := by simp only [swapIx, show ¬ j % (2 * 32) < 32 by omega, ↓reduceIte]
    rw [e, ← hy (j - 32) (by omega), BitVec.getLsbD_of_ge y.toBitVec (32 + j) (by omega)]
    simp [h, hj]

/-! Proof help: the stage facts, decided once each. -/

private theorem sw1 : ∀ j < 64, swapIx 1 j < 64 ∧ (j % (2 * 1) < 1 → 1 ≤ j → ¬ (j - 1) % (2 * 1) < 1) ∧
    (¬ j % (2 * 1) < 1 → 1 ≤ j ∧ (j - 1) % (2 * 1) < 1) := by decide +kernel
private theorem sw2 : ∀ j < 64, swapIx 2 j < 64 ∧ (j % (2 * 2) < 2 → 2 ≤ j → ¬ (j - 2) % (2 * 2) < 2) ∧
    (¬ j % (2 * 2) < 2 → 2 ≤ j ∧ (j - 2) % (2 * 2) < 2) := by decide +kernel
private theorem sw4 : ∀ j < 64, swapIx 4 j < 64 ∧ (j % (2 * 4) < 4 → 4 ≤ j → ¬ (j - 4) % (2 * 4) < 4) ∧
    (¬ j % (2 * 4) < 4 → 4 ≤ j ∧ (j - 4) % (2 * 4) < 4) := by decide +kernel
private theorem sw8 : ∀ j < 64, swapIx 8 j < 64 ∧ (j % (2 * 8) < 8 → 8 ≤ j → ¬ (j - 8) % (2 * 8) < 8) ∧
    (¬ j % (2 * 8) < 8 → 8 ≤ j ∧ (j - 8) % (2 * 8) < 8) := by decide +kernel
private theorem sw16 : ∀ j < 64, swapIx 16 j < 64 ∧ (j % (2 * 16) < 16 → 16 ≤ j → ¬ (j - 16) % (2 * 16) < 16) ∧
    (¬ j % (2 * 16) < 16 → 16 ≤ j ∧ (j - 16) % (2 * 16) < 16) := by decide +kernel
private theorem mk1 : ∀ j < 64, (0x5555555555555555 : UInt64).toBitVec.getLsbD j = decide (j % (2 * 1) < 1) := by
  decide +kernel
private theorem mk2 : ∀ j < 64, (0x3333333333333333 : UInt64).toBitVec.getLsbD j = decide (j % (2 * 2) < 2) := by
  decide +kernel
private theorem mk4 : ∀ j < 64, (0x0F0F0F0F0F0F0F0F : UInt64).toBitVec.getLsbD j = decide (j % (2 * 4) < 4) := by
  decide +kernel
private theorem mk8 : ∀ j < 64, (0x00FF00FF00FF00FF : UInt64).toBitVec.getLsbD j = decide (j % (2 * 8) < 8) := by
  decide +kernel
private theorem mk16 : ∀ j < 64, (0x0000FFFF0000FFFF : UInt64).toBitVec.getLsbD j = decide (j % (2 * 16) < 16) := by
  decide +kernel
private theorem rev_ix : ∀ j < 64,
    swapIx 1 (swapIx 2 (swapIx 4 (swapIx 8 (swapIx 16 (swapIx 32 j))))) = 63 - j := by decide +kernel

/-- **`rev64` reverses the bits.** -/
theorem rev64_getLsbD (x : UInt64) {j : ℕ} (hj : j < 64) :
    (rev64 x).toBitVec.getLsbD j = x.toBitVec.getLsbD (63 - j) := by
  have h := rot_stage x _ _
    (swap_stage 16 16 0x0000FFFF0000FFFF _ x _
    (swap_stage 8 8 0x00FF00FF00FF00FF _ x _
    (swap_stage 4 4 0x0F0F0F0F0F0F0F0F _ x _
    (swap_stage 2 2 0x3333333333333333 _ x _
    (swap_stage 1 1 0x5555555555555555 id x x (fun _ _ => rfl) (by decide) mk1 sw1)
      (by decide) mk2 sw2) (by decide) mk4 sw4) (by decide) mk8 sw8) (by decide) mk16 sw16)
  rw [rev64, h j hj]
  exact congrArg _ (rev_ix j hj)

theorem P_rev64 (x : UInt64) : P (rev64 x) = reflect 63 (P x) := by
  ext n
  rw [coeff_reflect, coeff_P, coeff_P]
  by_cases hn : n < 64
  · rw [rev64_getLsbD x hn, revAt_le (by omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), revAt_eq_self_of_lt (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem rev64_xor (x y : UInt64) : rev64 (x ^^^ y) = rev64 x ^^^ rev64 y := by
  apply P_inj
  rw [P_xor, P_rev64, P_rev64, P_rev64, P_xor, reflect_add]

theorem shiftRight_one_xor (x y : UInt64) : (x ^^^ y) >>> 1 = (x >>> 1) ^^^ (y >>> 1) := by
  apply P_inj
  ext n
  rw [coeff_P_shiftRight_one, P_xor, P_xor, coeff_add, coeff_add, coeff_P_shiftRight_one, coeff_P_shiftRight_one]

/-- **The high word of the carry-less product** is the reversed low word of the reversed operands' product,
shifted right once. -/
theorem clmul64_hi_eq (x y : UInt64) :
    (FK.clmul64 x y).hi = rev64 (bmul64 (rev64 x) (rev64 y)) >>> 1 := by
  apply P_inj
  ext n
  rw [coeff_clmul64_hi, coeff_P_shiftRight_one, P_rev64, coeff_reflect]
  by_cases hn : n < 63
  · rw [revAt_le (by omega), bmul64_eq_lo, coeff_clmul64_lo _ _ (by omega), P_rev64, P_rev64,
      ← reflect_mul _ _ (natDegree_P_le x) (natDegree_P_le y), coeff_reflect, revAt_le (by omega)]
    congr 1
    omega
  · rw [revAt_eq_self_of_lt (by omega), coeff_P_of_ge _ (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_mul_le.trans
      (Nat.add_le_add (natDegree_P_le x) (natDegree_P_le y))) (by omega))

/-! ## The products -/

/-- **`m2B` is `KT.m2`.** -/
theorem m2B_eq (a b : FE2) : m2B a b = Lvm.Typed.KT.m2 a b := by
  simp only [m2B, Lvm.Typed.KT.m2, ← bmul64_eq_lo, clmul64_hi_eq, rev64_xor, shiftRight_one_xor, UInt64.xor_assoc]

/-- `m2B` as a function, for rewriting under binders (`autoStepP2B_eq`). -/
theorem m2B_fun : m2B = Lvm.Typed.KT.m2 := funext fun a => funext fun b => m2B_eq a b

end Lvm6.V
