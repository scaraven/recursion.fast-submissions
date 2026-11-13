-- New for lvm2 (roll 10, R10 V-slice): the correlation automaton of `LvmKeccakSym`.
import LvmKeccakSymAdj
import LvmFieldCorrect

/-!
# `Σ_z eq(q, z)·eq(p, (z + r) mod 64)` by a carry automaton
-/

set_option autoImplicit false

namespace Lvm

/-! ## The correlation automaton -/

/-- Per bit `k`: `(m₀₁, m₁₀, m₀₀ + m₁₁)` with `m_{zo} = eq(q_k, z)·eq(p_k, o)`. -/
def corrTab (q p : List FE) : Array (FE × FE × FE) :=
  ((List.range 6).map fun k =>
    let qk := q.getD k 0
    let pk := p.getD k 0
    ((1 + qk) * pk, qk * (1 + pk), (1 + qk) * (1 + pk) + qk * pk)).toArray

/-- `corr(r)` by the carry of `z + r`, low bit first. State `(v₀, v₁)` = carry `0`, `1`. On a bit of `r` equal to 0:
`(v₀ (m₀₀ + m₁₁) + v₁ m₀₁, v₁ m₁₀)`. On a 1: `(v₀ m₀₁, v₀ m₁₀ + v₁ (m₀₀ + m₁₁))`. The carry out of bit 5 is
dropped (mod 64). -/
def corrA (t : Array (FE × FE × FE)) (r : Nat) : FE := Id.run do
  let mut v0 : FE := 1
  let mut v1 : FE := 0
  for k in [:6] do
    let (m01, m10, d) := t.getD k (0, 0, 0)
    if (r >>> k) % 2 == 0 then
      (v0, v1) := (v0 * d + v1 * m01, v1 * m10)
    else
      (v0, v1) := (v0 * m01, v0 * m10 + v1 * d)
  return v0 + v1

/-! ## Proof helpers -/

open Finset

private theorem eqKernelA_snoc (l : List FE) (x : FE) :
    eqKernelA (l ++ [x]) = (eqKernelA l).map (· * (1 + x)) ++ (eqKernelA l).map (· * x) := by
  simp only [eqKernelA, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem size_eqKernelA' (l : List FE) : (eqKernelA l).size = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [eqKernelA_snoc, Array.size_append, Array.size_map, Array.size_map, ih]
    simp [pow_succ, mul_two]

/-- `eq(x, b)` for a bit `b`. -/
private def eqB (x : FE) (b : Nat) : FE := if b = 0 then 1 + x else x

private theorem getD_snoc (l : List FE) (x : FE) {n e o : Nat} (hn : l.length = n) (he : e < 2 ^ n)
    (ho : o < 2) : (eqKernelA (l ++ [x])).getD (e + 2 ^ n * o) 0 = (eqKernelA l).getD e 0 * eqB x o := by
  have hs := size_eqKernelA' l
  rw [hn] at hs
  rw [eqKernelA_snoc]
  rcases (by omega : o = 0 ∨ o = 1) with rfl | rfl
  · simp [eqB, Array.getElem?_append_left, hs, he]
  · simp [eqB, hs, he]

/-- The carry-`c` part of the `k`-bit correlation: `z < 2^k` with `⌊(z + ρ) / 2^k⌋ = c`. -/
private def S (qs ps : List FE) (ρ c : Nat) : FE :=
  ∑ z ∈ range (2 ^ qs.length), if (z + ρ) / 2 ^ qs.length = c then
    (eqKernelA qs).getD z 0 * (eqKernelA ps).getD ((z + ρ) % 2 ^ qs.length) 0 else 0

/-- One bit's transfer weight from carry `c` to carry `c'` on a bit `rk` of `r`. -/
private def T (x y : FE) (rk c c' : Nat) : FE :=
  ∑ b ∈ range 2, if (c + b + rk) / 2 = c' then eqB x b * eqB y ((c + b + rk) % 2) else 0

private theorem idx {N w m : Nat} (hN : 0 < N) :
    (w + N * m) / (2 * N) = (w / N + m) / 2 ∧ (w + N * m) % (2 * N) = w % N + N * ((w / N + m) % 2) := by
  rw [Nat.div_mod_unique (by omega)]
  have h1 := Nat.div_add_mod w N
  have h2 := Nat.div_add_mod (w / N + m) 2
  have h3 := Nat.mod_lt w hN
  have h4 := Nat.mod_lt (w / N + m) (by omega : 0 < 2)
  constructor
  · calc w % N + N * ((w / N + m) % 2) + 2 * N * ((w / N + m) / 2)
        = w % N + N * (2 * ((w / N + m) / 2) + (w / N + m) % 2) := by ring
      _ = w + N * m := by rw [h2, mul_add]; omega
  · have : N * ((w / N + m) % 2) ≤ N * 1 := Nat.mul_le_mul_left _ (by omega)
    omega

private theorem S_step (qs ps : List FE) (x y : FE) {n : Nat} (hq : qs.length = n) (hp : ps.length = n)
    {ρ rk : Nat} (hρ : ρ < 2 ^ n) (hrk : rk < 2) (c' : Nat) :
    S (qs ++ [x]) (ps ++ [y]) (ρ + 2 ^ n * rk) c' =
      S qs ps ρ 0 * T x y rk 0 c' + S qs ps ρ 1 * T x y rk 1 c' := by
  have hl : (qs ++ [x]).length = n + 1 := by simp [hq]
  unfold S
  rw [hl, hq, pow_succ, mul_two, Finset.sum_range_add, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz := mem_range.mp hz
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have key : ∀ b, b < 2 → (if (z + 2 ^ n * b + (ρ + 2 ^ n * rk)) / (2 ^ n + 2 ^ n) = c' then
      (eqKernelA (qs ++ [x])).getD (z + 2 ^ n * b) 0 *
        (eqKernelA (ps ++ [y])).getD ((z + 2 ^ n * b + (ρ + 2 ^ n * rk)) % (2 ^ n + 2 ^ n)) 0 else 0) =
      if ((z + ρ) / 2 ^ n + (b + rk)) / 2 = c' then
        (eqKernelA qs).getD z 0 * eqB x b *
          ((eqKernelA ps).getD ((z + ρ) % 2 ^ n) 0 * eqB y (((z + ρ) / 2 ^ n + (b + rk)) % 2)) else 0 := by
    intro b hb
    have he : z + 2 ^ n * b + (ρ + 2 ^ n * rk) = (z + ρ) + 2 ^ n * (b + rk) := by ring
    obtain ⟨i1, i2⟩ := idx (w := z + ρ) (m := b + rk) hN
    rw [he, ← two_mul, i1, i2, getD_snoc qs x hq hz hb,
      getD_snoc ps y hp (Nat.mod_lt _ hN) (Nat.mod_lt _ (by omega))]
  have k0 := key 0 (by omega)
  have k1 := key 1 (by omega)
  simp only [mul_zero, add_zero] at k0
  rw [show 2 ^ n + z = z + 2 ^ n * 1 by ring, k0, k1]
  have hc : (z + ρ) / 2 ^ n < 2 := by
    rw [Nat.div_lt_iff_lt_mul hN]; omega
  generalize (z + ρ) / 2 ^ n = c at *
  generalize (eqKernelA qs).getD z 0 = B
  generalize (eqKernelA ps).getD ((z + ρ) % 2 ^ n) 0 = A
  unfold T
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  clear key k0 k1
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rcases (by omega : rk = 0 ∨ rk = 1) with rfl | rfl <;>
    rcases c' with _ | _ | c' <;> simp [eqB] <;> ring

/-- One step of `corrA`'s loop. -/
private def stepA (t : Array (FE × FE × FE)) (r : Nat) (v : FE × FE) (k : Nat) : FE × FE :=
  let (m01, m10, d) := t.getD k (0, 0, 0)
  if (r >>> k) % 2 == 0 then (v.1 * d + v.2 * m01, v.2 * m10) else (v.1 * m01, v.1 * m10 + v.2 * d)

private theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private theorem corrA_foldl (t : Array (FE × FE × FE)) (r : Nat) :
    corrA t r = ((List.range 6).foldl (stepA t r) (1, 0)).1 + ((List.range 6).foldl (stepA t r) (1, 0)).2 := by
  simp only [corrA, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield, List.forIn_pure_yield_eq_foldl]
  rfl

private theorem corrTab_getD (q p : List FE) {k : Nat} (hk : k < 6) :
    (corrTab q p).getD k (0, 0, 0) = ((1 + q.getD k 0) * p.getD k 0, q.getD k 0 * (1 + p.getD k 0),
      (1 + q.getD k 0) * (1 + p.getD k 0) + q.getD k 0 * p.getD k 0) := by
  simp [corrTab, hk]

private theorem take_succ' (l : List FE) {k : Nat} (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l.getD k 0] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

private theorem inv (q p : List FE) (hq : q.length = 6) (hp : p.length = 6) (r : Nat) :
    ∀ k, k ≤ 6 → (List.range k).foldl (stepA (corrTab q p) r) (1, 0) =
      (S (q.take k) (p.take k) (r % 2 ^ k) 0, S (q.take k) (p.take k) (r % 2 ^ k) 1)
  | 0, _ => by simp [S, eqKernelA, Nat.mod_one]
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, inv q p hq hp r k (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hlq : (q.take k).length = k := by simp [hq]; omega
    have hlp : (p.take k).length = k := by simp [hp]; omega
    have hρ : r % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hrk : r / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by omega)
    rw [take_succ' q (by omega), take_succ' p (by omega), Nat.mod_pow_succ,
      S_step _ _ _ _ hlq hlp hρ hrk, S_step _ _ _ _ hlq hlp hρ hrk]
    unfold stepA
    rw [corrTab_getD q p (by omega), Nat.shiftRight_eq_div_pow]
    generalize r / 2 ^ k % 2 = rk at *
    generalize S (q.take k) (p.take k) (r % 2 ^ k) 0 = v0
    generalize S (q.take k) (p.take k) (r % 2 ^ k) 1 = v1
    generalize q.getD k 0 = x
    generalize p.getD k 0 = y
    unfold T
    rcases (by omega : rk = 0 ∨ rk = 1) with rfl | rfl <;>
      simp [Finset.sum_range_succ, eqB]

private theorem list_sum_range (f : Nat → FE) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

private theorem sumE_sum (l : List FE) : sumE l = l.sum := by
  suffices h : ∀ a : FE, l.foldl (· + ·) a = a + l.sum by rw [sumE, h, zero_add]
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-! ## The statement -/

/-- **The correlation automaton** on two six-coordinate equality kernels. -/
theorem corrA_eq (q p : List FE) (hq : q.length = 6) (hp : p.length = 6) (r : Nat) :
    corrA (corrTab q p) r = corrG (eqKernelA p) (eqKernelA q) r := by
  rw [corrA_foldl, inv q p hq hp r 6 le_rfl, List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)]
  simp only
  unfold S corrG
  rw [hq, show (2 : Nat) ^ 6 = 64 from rfl, ← Finset.sum_add_distrib, sumE_sum, list_sum_range]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz := mem_range.mp hz
  have hm : (z + r % 64) % 64 = (z + r) % 64 := by omega
  have hc : (z + r % 64) / 64 < 2 := by omega
  rw [hm]
  rcases (by omega : (z + r % 64) / 64 = 0 ∨ (z + r % 64) / 64 = 1) with h | h <;> simp [h]

end Lvm
