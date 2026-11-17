-- New for lvm2 (WP T-K): the tape's wiring kernels `ι`, `MS` and the threshold sum, their verifier
-- evaluators (automata over the bits) and the multilinear-extension lemmas (BLUEPRINT2 §1.2 T3,
-- "Closed forms"). Pattern: v1's `LvmShift` (adapted from flock-recursive `FRShift.lean`).
import LvmShift

-- (GOLF2: 16 declarations that `certified` does not use moved verbatim to `LvmE2QNodeChkGOff`, outside its import closure.)

/-!
# The wiring kernels

The tape's GKR ends at the input claim `C_in = Σ_i ι(i)·⟨ω, in(i)⟩` with

* `iota ρ μ i = eq(ρ, i ≫ 5)·μ[i & 31]` (`ρ` the last pack point, `μ` the sixteen slot weights;
  `μ` is not a tensor, so the low four bits of `i` are one digit of sixteen values).

The wiring sumcheck (T3) needs three closed forms, generic in a row offset `base` (a multiple of
`2^w`) and a width `w ≥ 4` (`|σ| = w`, `|ρ| ≥ w − 4`):

* **`sum_msK`**: `MS_w^base(σ; t) = Σ_{x<2^w} eq(σ, x)·ι(base + x + 1)·[x + 1 ≤ t]` for `t < 2^w` is
  `msEval`, a four-state automaton over the bits, low bit first, state `(c, s)` = (carry of the
  `+1`, "the low bits of `x + 1` exceed those of `t`"); the low four bits are one sixteen-valued
  digit, and the bits of `base` above `w` give the fixed factor `eq(ρ_{≥ w−4}, base / 2^w)`.
  `K̃_ch(σ) = MS_20^0(σ; m)` (`sum_msK_zero`); an interval `[a, b]` is a difference of two
  (`sum_msIntK`), so `K̃_ks` is four evaluations.
* **`sum_ikK`**: `Σ_{x<2^w} eq(σ, x)·ι(base + x) = (Σ_d eq(σ_{<4}, d)·μ[d])·eq(ρ_{<w−4}, σ_{≥4})·
  eq(ρ_{≥w−4}, base / 2^w)` (`ikEval`; `Ĩ_ks` at `w = 15`, `base = 2^20`).
* **`thrEval_eq`**: `Σ_{i ≤ t} ι(i)` is `thrEval`, the two-state threshold automaton;
  `sum_range_iota_succ`: `Σ_{i=1}^{t} ι(i) = thrEval − ι(0)` (T3's `const`).
* `sum_eqAt_lowPad`: a table supported on `x < 2^w` has the extension of its low part times
  `eq(σ_{≥w}, 0)` (T3's factor `e'`).

For the circuit (T-Q), `msEvalA` and `thrEvalA` take the bits of `t` as field elements (`bitsE`; the low digit's
five bits against `ltE`) and use no comparison on `t` (`msEvalA_bitsE`, `thrEvalA_bitsE`).

All of it is over `E`, characteristic two; the verifier's `FE` twins are T-V's.
-/

set_option autoImplicit false

namespace Lvm.WK

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

/-! ## The weight `ι` and the kernels -/

/-- The input claim's row weight `ι(i) = eq(ρ, i ≫ 5)·μ[i & 31]`. -/
def iota (ρ μ : List E) (i : ℕ) : E := eqAt ρ (i / 32) * μ.getD (i % 32) 0

/-- The equality weight of one bit. -/
def eqBit (a : E) (b : Bool) : E := if b then a else 1 + a

/-- `MS`'s kernel on the cube: `ι(base + x + 1)·[x + 1 ≤ t]` (`K_ch` at `base = 0`, `t = m`). -/
def msK (ρ μ : List E) (base t x : ℕ) : E := if x + 1 ≤ t then iota ρ μ (base + x + 1) else 0

/-- The interval kernel `ι(base + x + 1)·[a ≤ x + 1 ≤ b]` (one interval of `cont` in `K_ks`). -/
def msIntK (ρ μ : List E) (base a b x : ℕ) : E :=
  if a ≤ x + 1 ∧ x + 1 ≤ b then iota ρ μ (base + x + 1) else 0

/-- The unshifted kernel `ι(base + x)` (`I_ks` at `base = 2^20`). -/
def ikK (ρ μ : List E) (base x : ℕ) : E := iota ρ μ (base + x)

/-! ## The `MS` automaton -/

/-- The automaton's value vector, `v c s` for the carry `c` and the strict flag `s`. -/
structure MS4 where
  v00 : E
  v01 : E
  v10 : E
  v11 : E

/-- Entry `(c, s)`. -/
def MS4.get (q : MS4) : Bool → Bool → E
  | false, false => q.v00
  | false, true => q.v01
  | true, false => q.v10
  | true, true => q.v11

/-- The strict flag after a bit: `[y₀ + s > t₀]` for the output bit `y₀` and `t`'s bit `t₀`. -/
def nextS (y0 s tb : Bool) : Bool := if tb then y0 && s else y0 || s

/-- One bit `(σ_k, ρ_k, t_k)` of `MS`, from the value vector `q` of the higher bits: the input bit
`b` has weight `eq(σ_k, b)`, the output bit `y₀ = b ⊕ c` weight `eq(ρ_k, y₀)`, the carry becomes
`b ∧ c`. -/
def msStep (a r : E) (tb : Bool) (q : MS4) : MS4 :=
  let f : Bool → Bool → E := fun c s =>
    (1 + a) * eqBit r c * q.get false (nextS c s tb) + a * eqBit r (!c) * q.get c (nextS (!c) s tb)
  ⟨f false false, f false true, f true false, f true true⟩

/-- The automaton over the high bits, highest bit innermost; at the top no carry is left and the
strict flag needs `1 ≤ t ≫ |σ|`. -/
def msTail : List E → List E → ℕ → MS4
  | a :: σ, r :: ρ, t => msStep a r (t % 2 == 1) (msTail σ ρ (t / 2))
  | _, _, t => ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩

/-- **`MS_w^base(σ; t)`, the verifier's evaluator** (`w = |σ|`): the low digit `d = x mod 16` gives
`y = (d + 1) mod 16`, carry `[d = 15]`, flag `[y > t mod 16]`; the high bits run `msTail`; the bits
of `base` above `w` give `eq(ρ_{≥ w−4}, base / 2^w)`. About `16 + 8(w − 4)` products. -/
def msEval (ρ μ σ : List E) (base t : ℕ) : E :=
  let q := msTail (σ.drop 5) (ρ.take (σ.length - 5)) (t / 32)
  eqAt (ρ.drop (σ.length - 5)) (base / 2 ^ σ.length) *
    sumE ((List.range 32).map fun d =>
      eqAt (σ.take 5) d * μ.getD ((d + 1) % 32) 0 * q.get (d == 31) (decide (t % 32 < (d + 1) % 32)))

/-! ## The threshold automaton and `Ĩ` -/

/-- The two-state threshold automaton (`(s = false, s = true)`) over the bits of the pack index. -/
def thrTail : List E → ℕ → E × E
  | r :: ρ, t =>
    let q := thrTail ρ (t / 2)
    let tb := t % 2 == 1
    let g : Bool → E := fun s =>
      (1 + r) * (if nextS false s tb then q.2 else q.1) + r * (if nextS true s tb then q.2 else q.1)
    (g false, g true)
  | [], t => (1, if 1 ≤ t then 1 else 0)

/-- **`Σ_{i ≤ t} ι(i)`, the verifier's evaluator**: the low digit `d` with flag `[d > t mod 16]`. -/
def thrEval (ρ μ : List E) (t : ℕ) : E :=
  let q := thrTail ρ (t / 32)
  sumE ((List.range 32).map fun d => μ.getD d 0 * (if t % 32 < d then q.2 else q.1))

/-- **`Σ_{x<2^w} eq(σ, x)·ι(base + x)`, the verifier's evaluator** (`w = |σ|`). -/
def ikEval (ρ μ σ : List E) (base : ℕ) : E :=
  sumE ((List.range 32).map fun d => eqAt (σ.take 5) d * μ.getD d 0) *
    eqEval (ρ.take (σ.length - 5)) (σ.drop 5) * eqAt (ρ.drop (σ.length - 5)) (base / 2 ^ σ.length)

/-! ## Arithmetic twins for the circuit: `t` as field bits -/

/-- `msStep` with `t`'s bit as a field element (`0` or `1`): a selection by `tb`. -/
def msStepA (a r tb : E) (q : MS4) : MS4 :=
  let q1 := msStep a r true q
  let q0 := msStep a r false q
  ⟨tb * q1.v00 + (1 + tb) * q0.v00, tb * q1.v01 + (1 + tb) * q0.v01,
    tb * q1.v10 + (1 + tb) * q0.v10, tb * q1.v11 + (1 + tb) * q0.v11⟩

/-- `msTail` on `t`'s bits (as many as `σ`'s coordinates; nothing above them). -/
def msTailA : List E → List E → List E → MS4
  | a :: σ, r :: ρ, b :: tb => msStepA a r b (msTailA σ ρ tb)
  | _, _, _ => ⟨1, 0, 0, 0⟩

/-- `[u < e]` for the five low bits `tb4` of `u`: `Σ_{j<e} eq(tb4, j)`. -/
def ltE (tb4 : List E) (e : ℕ) : E := sumE ((List.range e).map (eqAt tb4))

/-- `msEval` on `t`'s bits `tb` (`|tb| = |σ|`) with the top factor `cTop` given:
`q(c, s) = q(c, 0) + s·(q(c, 1) + q(c, 0))`, the flag `[t mod 32 < e]` as `ltE`. -/
def msEvalA (ρ μ σ tb : List E) (cTop : E) : E :=
  let q := msTailA (σ.drop 5) (ρ.take (σ.length - 5)) (tb.drop 5)
  let A : ℕ → E := fun d => eqAt (σ.take 5) d * μ.getD ((d + 1) % 32) 0
  cTop * (sumE ((List.range 31).map A) * q.v00 + A 31 * q.v10 +
    (q.v01 + q.v00) * sumE ((List.range 31).map fun d => A d * ltE (tb.take 5) (d + 1)))

/-- `thrTail` on the bits of `t` (as many as `ρ`'s coordinates). -/
def thrTailA : List E → List E → E × E
  | r :: ρ, b :: tb =>
    let q := thrTailA ρ tb
    -- t's bit 1: s' = y₀ ∧ s; bit 0: s' = y₀ ∨ s
    let g1 : Bool → E := fun s =>
      (1 + r) * (if nextS false s true then q.2 else q.1) + r * (if nextS true s true then q.2 else q.1)
    let g0 : Bool → E := fun s =>
      (1 + r) * (if nextS false s false then q.2 else q.1) + r * (if nextS true s false then q.2 else q.1)
    (b * g1 false + (1 + b) * g0 false, b * g1 true + (1 + b) * g0 true)
  | _, _ => (1, 0)

/-- `thrEval` on `t`'s bits `tb` (`|tb| = |ρ| + 5`). -/
def thrEvalA (ρ μ tb : List E) : E :=
  let q := thrTailA ρ (tb.drop 5)
  sumE ((List.range 32).map fun d => μ.getD d 0) * q.1 +
    (q.2 + q.1) * sumE ((List.range 32).map fun d => μ.getD d 0 * ltE (tb.take 5) d)

/-! ## Semantics of the automata (proof help) -/

/-- What `msTail σ ρ t` computes in state `(c, s)`:
`Σ_x eq(σ, x)·eq(ρ, x + c)·[x + c < 2^|σ|]·[x + c + s ≤ t]`. -/
def msSem (σ ρ : List E) (c s : Bool) (t : ℕ) : E :=
  ∑ x ∈ range (2 ^ σ.length),
    if x + c.toNat < 2 ^ σ.length ∧ x + c.toNat + s.toNat ≤ t then eqAt σ x * eqAt ρ (x + c.toNat)
    else 0

/-- What `thrTail ρ t` computes in state `s`: `Σ_y eq(ρ, y)·[y + s ≤ t]`. -/
def thrSem (ρ : List E) (s : Bool) (t : ℕ) : E :=
  ∑ y ∈ range (2 ^ ρ.length), if y + s.toNat ≤ t then eqAt ρ y else 0

theorem eqAt_cons_bit (r : E) (ρ : List E) (y : ℕ) (b : Bool) :
    eqAt (r :: ρ) (2 * y + b.toNat) = eqBit r b * eqAt ρ y := by
  cases b
  · rw [Bool.toNat_false, add_zero, eqAt_cons, if_neg (by (clear * - y; omega)), show 2 * y / 2 = y by (clear * - y; omega)]; rfl
  · rw [Bool.toNat_true, eqAt_cons, if_pos (by (clear * - y; omega)), show (2 * y + 1) / 2 = y by (clear * - y; omega)]; rfl

/-- The comparison passes to the high bits through the strict flag. -/
theorem le_iff_nextS (y0 s : Bool) (y t : ℕ) :
    2 * y + y0.toNat + s.toNat ≤ t ↔ y + (nextS y0 s (t % 2 == 1)).toNat ≤ t / 2 := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> cases y0 <;> cases s <;>
    simp [nextS, h] <;> (clear * - y t h; omega)

theorem ite_mul_congr {P Q : Prop} [Decidable P] [Decidable Q] (hPQ : P ↔ Q) (X Y k : E)
    (hXY : X = k * Y) : (if P then X else 0) = k * (if Q then Y else 0) := by
  by_cases hq : Q
  · rw [if_pos (hPQ.2 hq), if_pos hq, hXY]
  · rw [if_neg (fun hp ↦ hq (hPQ.1 hp)), if_neg hq, mul_zero]

theorem msStep_get (a r : E) (tb : Bool) (q : MS4) (c s : Bool) :
    (msStep a r tb q).get c s = eqBit a false * eqBit r c * q.get false (nextS c s tb) +
      eqBit a true * eqBit r (!c) * q.get c (nextS (!c) s tb) := by
  cases c <;> cases s <;> rfl

/-- One term of `msSem` on `a :: σ` at the input `2y + b`: the output bit is `b ⊕ c`, the carry
`b ∧ c`. -/
theorem msSem_term (a r : E) (σ ρ : List E) (n y t : ℕ) (b c s : Bool) :
    (if 2 * y + b.toNat + c.toNat < 2 ^ (n + 1) ∧ 2 * y + b.toNat + c.toNat + s.toNat ≤ t then
        eqAt (a :: σ) (2 * y + b.toNat) * eqAt (r :: ρ) (2 * y + b.toNat + c.toNat) else 0) =
      eqBit a b * eqBit r (b ^^ c) *
        (if y + (b && c).toNat < 2 ^ n ∧
            y + (b && c).toNat + (nextS (b ^^ c) s (t % 2 == 1)).toNat ≤ t / 2 then
          eqAt σ y * eqAt ρ (y + (b && c).toNat) else 0) := by
  have hsplit : 2 * y + b.toNat + c.toNat = 2 * (y + (b && c).toNat) + (b ^^ c).toNat := by
    cases b <;> cases c <;> simp <;> (clear * - y; omega)
  refine ite_mul_congr ?_ _ _ _ ?_
  · rw [hsplit, add_assoc, ← le_iff_nextS, pow_succ]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨by cases b <;> cases c <;> simp at h1 ⊢ <;> (clear * - h1; omega), by (clear * - h2; omega)⟩
    · rintro ⟨h1, h2⟩; refine ⟨by cases b <;> cases c <;> simp at h1 ⊢ <;> (clear * - h1; omega), by (clear * - h2; omega)⟩
  · rw [hsplit, eqAt_cons_bit, eqAt_cons_bit]
    ring

theorem msTail_get : ∀ (σ ρ : List E), σ.length = ρ.length → ∀ (t : ℕ) (c s : Bool),
    (msTail σ ρ t).get c s = msSem σ ρ c s t
  | [], [], _, t, c, s => by
    cases c <;> cases s <;>
      simp only [msTail, MS4.get, msSem, List.length_nil, pow_zero, Finset.sum_range_one, eqAt_nil,
        mul_one, Bool.toNat_false, Bool.toNat_true, zero_add, add_zero] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: σ, r :: ρ, h, t, c, s => by
    have h' : σ.length = ρ.length := by simpa using h
    rw [msTail, msStep_get, msTail_get σ ρ h' (t / 2), msTail_get σ ρ h' (t / 2), msSem, msSem, msSem,
      List.length_cons, sum_cube_succ, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun y _ ↦ ?_) (Finset.sum_congr rfl fun y _ ↦ ?_)
    · have := msSem_term a r σ ρ σ.length y t false c s
      simp only [Bool.toNat_false, add_zero, Bool.false_xor, Bool.false_and] at this
      rw [this]; simp only [Bool.toNat_false, add_zero]
    · have := msSem_term a r σ ρ σ.length y t true c s
      simp only [Bool.toNat_true, Bool.true_xor, Bool.true_and] at this
      rw [this]

theorem thrTail_get : ∀ (ρ : List E) (t : ℕ) (s : Bool),
    (if s then (thrTail ρ t).2 else (thrTail ρ t).1) = thrSem ρ s t
  | [], t, s => by
    cases s <;>
      simp only [thrTail, thrSem, List.length_nil, pow_zero, Finset.sum_range_one, eqAt_nil,
        Bool.toNat_false, Bool.toNat_true, zero_add, add_zero, ite_true, ite_false] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  | r :: ρ, t, s => by
    have ih := thrTail_get ρ (t / 2)
    have hterm : ∀ (y : ℕ) (y0 : Bool), (if 2 * y + y0.toNat + s.toNat ≤ t then
        eqAt (r :: ρ) (2 * y + y0.toNat) else 0) =
        eqBit r y0 * (if y + (nextS y0 s (t % 2 == 1)).toNat ≤ t / 2 then eqAt ρ y else 0) :=
      fun y y0 ↦ ite_mul_congr (le_iff_nextS y0 s y t) _ _ _ (eqAt_cons_bit r ρ y y0)
    have e0 := ih (nextS false s (t % 2 == 1))
    have e1 := ih (nextS true s (t % 2 == 1))
    rw [thrSem, List.length_cons, sum_cube_succ, Finset.sum_add_distrib]
    have h0 : ∀ y, (if 2 * y + s.toNat ≤ t then eqAt (r :: ρ) (2 * y) else 0) =
        eqBit r false * (if y + (nextS false s (t % 2 == 1)).toNat ≤ t / 2 then eqAt ρ y else 0) := by
      intro y; have := hterm y false; simpa using this
    have h1 : ∀ y, (if 2 * y + 1 + s.toNat ≤ t then eqAt (r :: ρ) (2 * y + 1) else 0) =
        eqBit r true * (if y + (nextS true s (t % 2 == 1)).toNat ≤ t / 2 then eqAt ρ y else 0) := by
      intro y; have := hterm y true; simpa using this
    simp only [h0, h1, ← Finset.mul_sum]
    rw [← thrSem, ← thrSem, ← e0, ← e1]
    cases s <;> simp only [thrTail, eqBit] <;> simp

/-- `ι` at a row of an aligned block: the low digit, the low `w − 5` pack bits, and `base`'s bits. -/
theorem iota_block (ρ μ : List E) (w base y : ℕ) (h4 : 5 ≤ w) (hρ : w - 5 ≤ ρ.length)
    (hb : 2 ^ w ∣ base) (hy : y < 2 ^ w) :
    iota ρ μ (base + y) =
      eqAt (ρ.take (w - 5)) (y / 32) * μ.getD (y % 32) 0 * eqAt (ρ.drop (w - 5)) (base / 2 ^ w) := by
  obtain ⟨k, rfl⟩ := hb
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 5 := ⟨w - 5, by (clear * - h4; omega)⟩
  rw [Nat.add_sub_cancel] at hρ ⊢
  have hP : 0 < 2 ^ v := Nat.two_pow_pos v
  have h16 : 2 ^ (v + 5) = 32 * 2 ^ v := by rw [pow_add]; ring
  have hz : y / 32 < 2 ^ v := by (clear * - hy h16; omega)
  have hlen : (ρ.take v).length = v := by simp; (clear * - hρ; omega)
  have hsplit : 2 ^ (v + 5) * k + y = 32 * (2 ^ v * k) + y := by rw [h16]; ring
  have e1 : (2 ^ (v + 5) * k + y) / 32 = 2 ^ v * k + y / 32 := by rw [hsplit]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - v k y; omega))
  have e3 : (2 ^ (v + 5) * k + y) % 32 = y % 32 := by rw [hsplit]; (clear * - e1; omega)
  have e2 : (2 ^ v * k + y / 32) % 2 ^ v = y / 32 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hz]
  have e4 : (2 ^ v * k + y / 32) / 2 ^ v = k := by
    rw [Nat.mul_add_div hP, Nat.div_eq_of_lt hz, add_zero]
  have e5 : 2 ^ (v + 5) * k / 2 ^ (v + 5) = k := Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)
  rw [iota, e1, e3, e5]
  conv_lhs => rw [← List.take_append_drop v ρ]
  rw [eqAt_append, hlen, eqAt_mod (ρ.take v), hlen, e2, e4]
  ring

/-! ## The closed forms -/

/-- **`MS`'s extension is the automaton** (`K̃_ch`, and the ends of `K̃_ks`'s intervals). -/
theorem sum_msK (ρ μ σ : List E) (base t : ℕ) (h4 : 5 ≤ σ.length) (hρ : σ.length - 5 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) (ht : t < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * msK ρ μ base t x = msEval ρ μ σ base t := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 5 := ⟨σ.length - 5, by (clear * - h4; omega)⟩
  have hσh : (σ.drop 5).length = v := by simp; (clear * - h4 hv; omega)
  have hσ4 : (σ.take 5).length = 5 := by simp; (clear * - h4; omega)
  have hρh : (ρ.take (σ.length - 5)).length = v := by simp; (clear * - h4 hρ hv hσh; omega)
  have hpow : 2 ^ σ.length = 2 ^ v * 32 := by rw [hv, pow_add]; norm_num
  have key : ∀ d ∈ range 32, ∀ x' ∈ range (2 ^ v),
      eqAt σ (32 * x' + d) * msK ρ μ base t (32 * x' + d) =
        eqAt (ρ.drop (σ.length - 5)) (base / 2 ^ σ.length) *
          (eqAt (σ.take 5) d * μ.getD ((d + 1) % 32) 0 *
            (if x' + (d == 31).toNat < 2 ^ v ∧
                x' + (d == 31).toNat + (decide (t % 32 < (d + 1) % 32)).toNat ≤ t / 32 then
              eqAt (σ.drop 5) x' * eqAt (ρ.take (σ.length - 5)) (x' + (d == 31).toNat) else 0)) := by
    intro d hd x' hx'
    have hd' := Finset.mem_range.1 hd
    have hx'' := Finset.mem_range.1 hx'
    have hes : eqAt σ (32 * x' + d) = eqAt (σ.take 5) d * eqAt (σ.drop 5) x' := by
      conv_lhs => rw [← List.take_append_drop 5 σ]
      rw [eqAt_append, hσ4, eqAt_mod (σ.take 5), hσ4,
        show (32 * x' + d) % 2 ^ 5 = d by norm_num; (clear * - hd'; omega),
        show (32 * x' + d) / 2 ^ 5 = x' by norm_num; (clear * - hd'; omega)]
    have hcv : ((32 * x' + d + 1 ≤ t) ↔ (x' + (d == 31).toNat < 2 ^ v ∧
        x' + (d == 31).toNat + (decide (t % 32 < (d + 1) % 32)).toNat ≤ t / 32)) ∧
        (32 * x' + d + 1) / 32 = x' + (d == 31).toNat ∧ (32 * x' + d + 1) % 32 = (d + 1) % 32 := by
      rcases (show d = 31 ∨ d < 31 by (clear * - hd'; omega)) with h | h
      · subst h; simp; (clear * - ht hpow hx''; omega)
      · have h15 : (d == 31) = false := by simp; (clear * - hd' h; omega)
        rw [h15, Nat.mod_eq_of_lt (show d + 1 < 32 by (clear * - hd' h; omega))]
        by_cases hs : t % 32 < d + 1 <;> simp [hs] <;> (clear * - hd' hx'' h hs; omega)
    rw [msK]
    by_cases hc' : 32 * x' + d + 1 ≤ t
    · rw [if_pos hc', if_pos (hcv.1.1 hc'), show base + (32 * x' + d) + 1 = base + (32 * x' + d + 1) by ring,
        iota_block ρ μ σ.length base _ h4 hρ hb (by (clear * - ht hpow hcv hc'; omega)), hcv.2.1, hcv.2.2, hes]
      ring
    · rw [if_neg hc', if_neg (fun h ↦ hc' (hcv.1.2 h))]
      ring
  have hq : ∀ c s, (msTail (σ.drop 5) (ρ.take (σ.length - 5)) (t / 32)).get c s =
      msSem (σ.drop 5) (ρ.take (σ.length - 5)) c s (t / 32) :=
    msTail_get _ _ (by rw [hσh, hρh]) _
  simp only [msEval]
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]
  conv_lhs => rw [hpow, sum_range_mul]
  simp only [hq, msSem, hσh, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun x' hx' ↦ key d hd x' hx'

/-- `sum_msK` at `base = 0` (`K̃_ch(σ) = MS_20^0(σ; m)`). -/
theorem sum_msK_zero (ρ μ σ : List E) (t : ℕ) (h4 : 5 ≤ σ.length) (hρ : σ.length - 5 ≤ ρ.length)
    (ht : t < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * msK ρ μ 0 t x = msEval ρ μ σ 0 t :=
  sum_msK ρ μ σ 0 t h4 hρ (dvd_zero _) ht

/-- **An interval `[a, b]` is a difference of two `MS`** (`1 ≤ a ≤ b < 2^w`). -/
theorem sum_msIntK (ρ μ σ : List E) (base a b : ℕ) (h4 : 5 ≤ σ.length)
    (hρ : σ.length - 5 ≤ ρ.length) (hb : 2 ^ σ.length ∣ base) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbw : b < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * msIntK ρ μ base a b x =
      msEval ρ μ σ base b - msEval ρ μ σ base (a - 1) := by
  have hk : ∀ x, msIntK ρ μ base a b x = msK ρ μ base b x - msK ρ μ base (a - 1) x := by
    intro x
    simp only [msIntK, msK]
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [hk, mul_sub, Finset.sum_sub_distrib]
  rw [sum_msK ρ μ σ base b h4 hρ hb hbw, sum_msK ρ μ σ base (a - 1) h4 hρ hb (by (clear * - ha hab hbw; omega))]

/-- **`Ĩ`'s closed form** (`Ĩ_ks(σ')` at `w = 31`, `base = 2^20`). -/
theorem sum_ikK (ρ μ σ : List E) (base : ℕ) (h4 : 5 ≤ σ.length) (hρ : σ.length - 5 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * ikK ρ μ base x = ikEval ρ μ σ base := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 5 := ⟨σ.length - 5, by (clear * - h4; omega)⟩
  have hσh : (σ.drop 5).length = v := by simp; (clear * - h4 hv; omega)
  have hσ4 : (σ.take 5).length = 5 := by simp; (clear * - h4; omega)
  have hρh : (ρ.take (σ.length - 5)).length = v := by simp; (clear * - h4 hρ hv hσh; omega)
  have hpow : 2 ^ σ.length = 2 ^ v * 32 := by rw [hv, pow_add]; norm_num
  have key : ∀ d ∈ range 32, ∀ x' ∈ range (2 ^ v),
      eqAt σ (32 * x' + d) * ikK ρ μ base (32 * x' + d) =
        eqAt (σ.take 5) d * μ.getD d 0 * (eqAt (ρ.take (σ.length - 5)) x' * eqAt (σ.drop 5) x') *
          eqAt (ρ.drop (σ.length - 5)) (base / 2 ^ σ.length) := by
    intro d hd x' hx'
    have hd' := Finset.mem_range.1 hd
    have hx'' := Finset.mem_range.1 hx'
    have hes : eqAt σ (32 * x' + d) = eqAt (σ.take 5) d * eqAt (σ.drop 5) x' := by
      conv_lhs => rw [← List.take_append_drop 5 σ]
      rw [eqAt_append, hσ4, eqAt_mod (σ.take 5), hσ4,
        show (32 * x' + d) % 2 ^ 5 = d by norm_num; (clear * - hd'; omega),
        show (32 * x' + d) / 2 ^ 5 = x' by norm_num; (clear * - hd'; omega)]
    rw [ikK, iota_block ρ μ σ.length base _ h4 hρ hb (by (clear * - hpow hd' hx''; omega)), hes,
      show (32 * x' + d) / 32 = x' by (clear * - hd'; omega), show (32 * x' + d) % 32 = d by (clear * - hd'; omega)]
    ring
  rw [ikEval, LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range,
    ← Lvm.KG.sum_eqAt_mul_eqAt _ _ (by rw [hρh, hσh]), hρh, Finset.sum_mul_sum, Finset.sum_mul]
  conv_lhs => rw [hpow, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x' hx' ↦ key d hd x' hx'

/-- **The threshold sum** `Σ_{i ≤ t} ι(i)` is the two-state automaton. -/
theorem thrEval_eq (ρ μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ.length + 5)) :
    ∑ i ∈ range (t + 1), iota ρ μ i = thrEval ρ μ t := by
  have hpow : 2 ^ (ρ.length + 5) = 2 ^ ρ.length * 32 := by rw [pow_add]; norm_num
  have hsub : range (t + 1) ⊆ range (2 ^ (ρ.length + 5)) := Finset.range_subset_range.2 (by (clear * - t ρ ht hpow; omega))
  have h1 : ∑ i ∈ range (t + 1), iota ρ μ i =
      ∑ i ∈ range (2 ^ (ρ.length + 5)), if i ≤ t then iota ρ μ i else 0 := by
    rw [← Finset.sum_subset hsub (fun x _ hx ↦ by rw [if_neg (by simp at hx; (clear * - hx; omega))])]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [if_pos (by simp at hi; (clear * - hi; omega))]
  rw [h1, hpow, sum_range_mul, Finset.sum_comm]
  simp only [thrEval]
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Finset.mem_range.1 hd
  have hq : (if t % 32 < d then (thrTail ρ (t / 32)).2 else (thrTail ρ (t / 32)).1) =
      thrSem ρ (decide (t % 32 < d)) (t / 32) := by
    rw [← thrTail_get ρ (t / 32) (decide (t % 32 < d))]
    simp
  rw [hq, thrSem, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [iota, show (32 * y + d) / 32 = y by (clear * - hd'; omega), show (32 * y + d) % 32 = d by (clear * - hd'; omega), mul_ite, mul_zero]
  by_cases hs : t % 32 < d
  · simp only [hs, decide_true, Bool.toNat_true]
    split_ifs <;> first | (exfalso; omega) | ring
  · simp only [hs, decide_false, Bool.toNat_false, add_zero]
    split_ifs <;> first | (exfalso; omega) | ring

/-- `Σ_{i=1}^{t} ι(i) = thrEval − ι(0)` (T3's `const` at `t = m`). -/
theorem sum_range_iota_succ (ρ μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ.length + 5)) :
    ∑ i ∈ range t, iota ρ μ (i + 1) = thrEval ρ μ t - iota ρ μ 0 := by
  rw [← thrEval_eq ρ μ t ht, Finset.sum_range_succ']
  ring

/-! ## The circuit's twins agree on bits -/

end Lvm.WK
