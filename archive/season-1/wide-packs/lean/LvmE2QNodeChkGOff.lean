/- `LvmE2QNodeChkGOff` (GOLF2 off-path move, group 7 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmEqLemmas, LvmWireKernel, LvmVFastQ, LvmTypedLayQ, LvmE2QNodeChkG,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmEqLemmas
import LvmWireKernel
import LvmVFastQ
import LvmTypedLayQ
import LvmE2QNodeChkG
import LvmM3MidCertOff
import LvmMlListLemmas
import LvmQAsmHar47

-- ===== from `LvmEqLemmas` =====

section
namespace LeanVM.Protocol.Whir.Complete
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset
section

/-- A cube point of `n + k` coordinates whose index is `y + 2^n·z` is `y`'s point, then `z`'s. -/
theorem boolPoint_add (n k y z : ℕ) (hy : y < 2 ^ n) :
    boolPoint (n + k) (y + 2 ^ n * z) = boolPoint n y ++ boolPoint k z := by
  simp only [boolPoint, List.range_add, List.map_append, List.map_map]
  rw [show y + 2 ^ n * z = 2 ^ n * z + y by ring]
  congr 1
  · refine List.map_congr_left fun i hi ↦ ?_
    rw [Nat.testBit_two_pow_mul_add _ hy]
    simp [List.mem_range.mp hi]
  · refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply]
    rw [Nat.testBit_two_pow_mul_add _ hy]
    simp

end
end LeanVM.Protocol.Whir.Complete
end

section
namespace LeanVM.Protocol.Whir.Complete
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset
section

/-- `y + N·z < N·M` for `y < N` and `z < M`. -/
theorem add_mul_lt {y z N M : ℕ} (hy : y < N) (hz : z < M) : y + N * z < N * M := by
  calc y + N * z < N + N * z := by (clear * - hy; omega)
    _ = N * (z + 1) := by ring
    _ ≤ N * M := Nat.mul_le_mul_left _ hz

theorem length_foldPairs (r : E) : ∀ t : List E, (foldPairs r t).length = t.length / 2
  | [] => by simp [foldPairs]
  | [_] => by simp [foldPairs]
  | a :: b :: t => by
    simp only [foldPairs, List.length_cons, length_foldPairs r t]
    omega

/-- Entry `j` of a fold: the pair `(t[2j], t[2j+1])` interpolated at `r`. -/
theorem getD_foldPairs (r : E) : ∀ (t : List E) (j : ℕ), 2 * j + 1 < t.length →
    (foldPairs r t).getD j 0 = t.getD (2 * j) 0 * (1 + r) + t.getD (2 * j + 1) 0 * r
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: t, 0, _ => by simp [foldPairs]
  | a :: b :: t, j + 1, h => by
    simp only [foldPairs, List.getD_cons_succ, List.length_cons] at h ⊢
    rw [getD_foldPairs r t j (by omega)]
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp

end
end LeanVM.Protocol.Whir.Complete
end

section
namespace LeanVM.Protocol.Whir.Complete
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset
section

theorem multilinearEval_eq_foldAll (t r : List E) :
    multilinearEval t r = (foldAll t r).headD 0 := rfl

end
end LeanVM.Protocol.Whir.Complete
end

section
namespace LeanVM.Protocol.Whir.Complete
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset
section

theorem foldAll_cons (t : List E) (c : E) (r : List E) :
    foldAll t (c :: r) = foldAll (foldPairs c t) r := rfl

theorem foldAll_append (t r r' : List E) : foldAll t (r ++ r') = foldAll (foldAll t r) r' := by
  simp [foldAll, List.foldl_append]

theorem foldAll_concat (t r : List E) (c : E) :
    foldAll t (r ++ [c]) = foldPairs c (foldAll t r) := by
  rw [foldAll_append]; rfl

theorem multilinearEval_cons (t : List E) (c : E) (p : List E) :
    multilinearEval t (c :: p) = multilinearEval (foldPairs c t) p := rfl

/-- Fixing `|r|` coordinates of a table on `|r| + n` variables leaves `2^n` entries. -/
theorem length_foldAll : ∀ (r t : List E) (n : ℕ), t.length = 2 ^ (r.length + n) →
    (foldAll t r).length = 2 ^ n
  | [], t, n, h => by simpa using h
  | c :: r, t, n, h => by
    rw [foldAll_cons]
    refine length_foldAll r _ n ?_
    rw [length_foldPairs, h, List.length_cons, show r.length + 1 + n = r.length + n + 1 by ring,
      pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- **Part-way evaluation.** Fixing the first `k = |r|` coordinates at `r` leaves at `x` the sum
`Σ_j eq(j, r)·t[j + 2^k·x]`. -/
theorem getD_foldAll : ∀ (r t : List E) (n x : ℕ), t.length = 2 ^ (r.length + n) → x < 2 ^ n →
    (foldAll t r).getD x 0 =
      ∑ j ∈ range (2 ^ r.length), eqEval (boolPoint r.length j) r * t.getD (j + 2 ^ r.length * x) 0
  | [], t, n, x, _, _ => by simp
  | c :: r, t, n, x, h, hx => by
    rw [foldAll_cons]
    have hlen : (foldPairs c t).length = 2 ^ (r.length + n) := by
      rw [length_foldPairs, h, List.length_cons, show r.length + 1 + n = r.length + n + 1 by ring,
        pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [getD_foldAll r _ n x hlen hx, List.length_cons, pow_succ, mul_comm (2 ^ r.length) 2,
      sum_range_two_mul]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    have hlt : j + 2 ^ r.length * x < 2 ^ (r.length + n) := by
      rw [pow_add]; exact add_mul_lt hj' hx
    rw [getD_foldPairs c t _ (by rw [h, List.length_cons, show r.length + 1 + n =
      r.length + n + 1 by ring, pow_succ]; (clear * - hlt; omega)), boolPoint_two_mul,
      boolPoint_two_mul_add_one, eqEval_cons, eqEval_cons]
    have e1 : 2 * (j + 2 ^ r.length * x) = 2 * j + 2 * 2 ^ r.length * x := by ring
    have e2 : 2 * (j + 2 ^ r.length * x) + 1 = 2 * j + 1 + 2 * 2 ^ r.length * x := by ring
    rw [e2, e1]
    linear_combination (-(eqEval (boolPoint r.length j) r *
      t.getD (2 * j + 1 + 2 * 2 ^ r.length * x) 0)) * two_eq_zero_E

/-- **The multilinear extension.** `multilinearEval t p = Σ_i t[i]·eq(i, p)`. -/
theorem multilinearEval_eq_sum (m : ℕ) (t p : List E) (ht : t.length = 2 ^ m)
    (hp : p.length = m) :
    multilinearEval t p = ∑ i ∈ range (2 ^ m), t.getD i 0 * eqEval (boolPoint m i) p := by
  subst hp
  rw [multilinearEval_eq_foldAll, List.headD_eq_getD,
    getD_foldAll p t 0 0 (by simpa using ht) (by simp)]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, eqEval_comm]
  simp

/-- One step of `eqKernel`. -/
private theorem eqKernel_step (out : List E) (r : E) (p : List E) :
    p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r))
      (out.map (· * (1 + r)) ++ out.map (· * r)) =
    (r :: p).foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out := rfl

end
end LeanVM.Protocol.Whir.Complete
end

section
namespace LeanVM.Protocol.Whir.Complete
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset
section

/-- Pairing a table of `2^|p|` entries with the equality kernel at `p` is its multilinear
extension at `p`. -/
theorem dot_eqKernel (t p : List E) (ht : t.length = 2 ^ p.length) :
    dot t (eqKernel p) =
      ∑ j ∈ range (2 ^ p.length), t.getD j 0 * eqEval (boolPoint p.length j) p := by
  rw [dot_eq_sum _ _ (by rw [ht, length_eqKernel]), ht]
  exact sum_congr rfl fun j hj ↦ by rw [getD_eqKernel p j (mem_range.mp hj)]

/-- The constant coefficient `h(0) = Σ_x W(0,x)·g(0,x)` of the round polynomial. -/
def roundC0 : List E → List E → E
  | w0 :: _ :: ws, g0 :: _ :: gs => w0 * g0 + roundC0 ws gs
  | _, _ => 0

/-- The quadratic coefficient `Σ_x (W(0,x) + W(1,x))·(g(0,x) + g(1,x))` of the round
polynomial. -/
def roundC2 : List E → List E → E
  | w0 :: w1 :: ws, g0 :: g1 :: gs => (w0 + w1) * (g0 + g1) + roundC2 ws gs
  | _, _ => 0

/-- The round polynomial the verifier builds from the two scalars `roundC0`, `roundC2` and the
claim (`sumcheckRoundPoly 3 claim none`): the linear coefficient is `claim + c2`. -/
def roundQuad (claim : E) (W g : List E) : List E :=
  [roundC0 W g, claim + sumE [roundC2 W g], roundC2 W g]

theorem polyEval_three (a b d c : E) : polyEval [a, b, d] c = a + b * c + d * c ^ 2 := by
  simp [polyEval]; ring

/-- **The sumcheck round.** If the claim is `Σ W·g`, the round polynomial at `c` is the sum of
the product of the tables with their first coordinate fixed at `c`. -/
theorem polyEval_roundQuad (c : E) : ∀ (W g : List E), W.length = g.length → Even W.length →
    polyEval (roundQuad (dot W g) W g) c = dot (foldPairs c W) (foldPairs c g)
  | [], [], _, _ => by simp [roundQuad, roundC0, roundC2, polyEval, sumE, foldPairs]
  | [_], _, _, he => by simp at he
  | w0 :: w1 :: ws, g0 :: g1 :: gs, hl, he => by
    have ih := polyEval_roundQuad c ws gs (by simpa using hl)
      (by simpa [Nat.even_add_one] using he)
    simp only [roundQuad, polyEval_three, sumE_eq, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
    simp only [roundC0, roundC2, dot_cons, foldPairs]
    linear_combination ih + (w1 * g1 * c) * two_eq_zero_E
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _ :: _, [], hl, _ => by simp at hl
  | _ :: _ :: _, [_], hl, _ => by simp at hl

/-- `W + s·T`, entrywise. -/
def axpy (s : E) (W T : List E) : List E := List.zipWith (fun a b ↦ a + s * b) W T

theorem length_axpy (s : E) (W T : List E) (h : W.length = T.length) :
    (axpy s W T).length = W.length := by
  simp [axpy, h]

/-- `roundC0` is linear in the weight table. -/
theorem roundC0_axpy (s : E) : ∀ (W T g : List E), W.length = T.length →
    roundC0 (axpy s W T) g = roundC0 W g + s * roundC0 T g
  | [], [], g, _ => by simp [axpy, roundC0]
  | [], _ :: _, _, h => by simp at h
  | [_], [], _, h => by simp at h
  | [_], [_], g, _ => by simp [axpy, roundC0]
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [], _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h
  | w0 :: w1 :: ws, t0 :: t1 :: ts, g, h =>
    match g with
    | [] => by simp [axpy, roundC0]
    | [_] => by simp [axpy, roundC0]
    | g0 :: g1 :: gs => by
      have ih := roundC0_axpy s ws ts gs (by simpa using h)
      simp only [axpy] at ih ⊢
      simp only [List.zipWith_cons_cons, roundC0]
      rw [ih]; ring

/-- `roundC2` is linear in the weight table. -/
theorem roundC2_axpy (s : E) : ∀ (W T g : List E), W.length = T.length →
    roundC2 (axpy s W T) g = roundC2 W g + s * roundC2 T g
  | [], [], g, _ => by simp [axpy, roundC2]
  | [], _ :: _, _, h => by simp at h
  | [_], [], _, h => by simp at h
  | [_], [_], g, _ => by simp [axpy, roundC2]
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [], _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h
  | w0 :: w1 :: ws, t0 :: t1 :: ts, g, h =>
    match g with
    | [] => by simp [axpy, roundC2]
    | [_] => by simp [axpy, roundC2]
    | g0 :: g1 :: gs => by
      have ih := roundC2_axpy s ws ts gs (by simpa using h)
      simp only [axpy] at ih ⊢
      simp only [List.zipWith_cons_cons, roundC2]
      rw [ih]; ring

/-- `dot` is linear in its first argument. -/
theorem dot_axpy (s : E) : ∀ (W T g : List E), W.length = T.length →
    dot (axpy s W T) g = dot W g + s * dot T g
  | [], [], _, _ => by simp [axpy]
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by simp [axpy]
  | w :: ws, t :: ts, x :: g, h => by
    have ih := dot_axpy s ws ts g (by simpa using h)
    simp only [axpy] at ih ⊢
    simp only [List.zipWith_cons_cons, dot_cons]
    rw [ih]; ring

/-- Folding is linear. -/
theorem foldPairs_axpy (s c : E) : ∀ (W T : List E), W.length = T.length →
    foldPairs c (axpy s W T) = axpy s (foldPairs c W) (foldPairs c T)
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | w0 :: w1 :: ws, t0 :: t1 :: ts, h => by
    have ih := foldPairs_axpy s c ws ts (by simpa using h)
    simp only [axpy] at ih ⊢
    simp only [List.zipWith_cons_cons, foldPairs]
    rw [ih, List.cons.injEq]
    exact ⟨by ring, rfl⟩
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h
  | [_], _ :: _ :: _, h => by simp at h

/-- The multilinear extension is linear in the table. -/
theorem multilinearEval_axpy (s : E) : ∀ (p W T : List E), W.length = T.length →
    multilinearEval (axpy s W T) p = multilinearEval W p + s * multilinearEval T p
  | [], [], [], _ => by simp [multilinearEval, axpy]
  | [], w :: _, t :: _, _ => by simp [multilinearEval, axpy]
  | [], _ :: _, [], h => by simp at h
  | [], [], _ :: _, h => by simp at h
  | c :: p, W, T, h => by
    rw [multilinearEval_cons, foldPairs_axpy s c W T h, multilinearEval_axpy s p _ _
      (by rw [length_foldPairs, length_foldPairs, h])]
    rfl

end
end LeanVM.Protocol.Whir.Complete
end

section
namespace LeanVM.Protocol.Whir.Complete
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset
section

theorem getD_tableOf (m : ℕ) (w : List E → E) (i : ℕ) (hi : i < 2 ^ m) :
    (tableOf m w).getD i 0 = w (boolPoint m i) := by
  simp [tableOf, hi]

/-- `IsMultilinearFn` with the sum over the cube as a sum over the indices. -/
theorem isMultilinearFn_iff (m : ℕ) (w : List E → E) :
    IsMultilinearFn m w ↔ ∀ p : List E, p.length = m →
      w p = ∑ x ∈ range (2 ^ m), w (boolPoint m x) * eqEval (boolPoint m x) p := by
  unfold IsMultilinearFn
  refine forall_congr' fun p ↦ imp_congr_right fun _ ↦ ?_
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ w (boolPoint m x) * eqEval (boolPoint m x) p)]

/-- **A multilinear function is the extension of its table.** -/
theorem multilinearEval_tableOf {m : ℕ} {w : List E → E} (hw : IsMultilinearFn m w)
    (p : List E) (hp : p.length = m) : multilinearEval (tableOf m w) p = w p := by
  rw [multilinearEval_eq_sum m _ p (by simp) hp, (isMultilinearFn_iff m w).mp hw p hp]
  exact sum_congr rfl fun i hi ↦ by rw [getD_tableOf _ _ _ (mem_range.mp hi)]

/-- Pairing a function's table with a table. -/
theorem dot_tableOf (m : ℕ) (w : List E → E) (g : List E) (hg : g.length = 2 ^ m) :
    dot (tableOf m w) g = ∑ i ∈ range (2 ^ m), w (boolPoint m i) * g.getD i 0 := by
  rw [dot_eq_sum _ _ (by simp [hg]), length_tableOf]
  exact sum_congr rfl fun i hi ↦ by rw [getD_tableOf _ _ _ (mem_range.mp hi)]

theorem isMultilinearFn_congr {m : ℕ} {w w' : List E → E} (hw : IsMultilinearFn m w)
    (h : ∀ p : List E, p.length = m → w p = w' p) : IsMultilinearFn m w' := by
  rw [isMultilinearFn_iff] at hw ⊢
  intro p hp
  rw [← h p hp, hw p hp]
  exact sum_congr rfl fun x _ ↦ by rw [h _ (length_boolPoint m x)]

theorem isMultilinearFn_add {m : ℕ} {w w' : List E → E} (hw : IsMultilinearFn m w)
    (hw' : IsMultilinearFn m w') : IsMultilinearFn m fun p ↦ w p + w' p := by
  rw [isMultilinearFn_iff] at hw hw' ⊢
  intro p hp
  rw [hw p hp, hw' p hp, ← sum_add_distrib]
  exact sum_congr rfl fun x _ ↦ by ring

theorem isMultilinearFn_const_mul {m : ℕ} {w : List E → E} (hw : IsMultilinearFn m w) (a : E) :
    IsMultilinearFn m fun p ↦ a * w p := by
  rw [isMultilinearFn_iff] at hw ⊢
  intro p hp
  rw [hw p hp, mul_sum]
  exact sum_congr rfl fun x _ ↦ by ring

theorem isMultilinearFn_const_zero (m : ℕ) : IsMultilinearFn m fun _ ↦ 0 := by
  rw [isMultilinearFn_iff]; intro p _; simp

/-- A linear combination over a list of multilinear functions is multilinear. -/
theorem isMultilinearFn_list_sum {ι : Type} {m : ℕ} (L : List ι) (c : ι → E)
    (w : ι → List E → E) (hw : ∀ i ∈ L, IsMultilinearFn m (w i)) :
    IsMultilinearFn m fun p ↦ (L.map fun i ↦ c i * w i p).sum := by
  induction L with
  | nil => simpa using isMultilinearFn_const_zero m
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact isMultilinearFn_add (isMultilinearFn_const_mul (hw i (by simp)) (c i))
      (ih fun j hj ↦ hw j (by simp [hj]))

/-- A product of affine factors, the `i`-th factor `a i + b i·p_i`. -/
def affProd (a b : ℕ → E) : List E → E
  | [] => 1
  | c :: p => (a 0 + b 0 * c) * affProd (fun i ↦ a (i + 1)) (fun i ↦ b (i + 1)) p

/-- **A product of affine factors is multilinear.** -/
theorem isMultilinearFn_affProd (m : ℕ) : ∀ (a b : ℕ → E), IsMultilinearFn m (affProd a b) := by
  induction m with
  | zero =>
    intro a b
    rw [isMultilinearFn_iff]
    intro p hp
    obtain rfl : p = [] := List.eq_nil_of_length_eq_zero hp
    simp [affProd]
  | succ m ih =>
    intro a b
    rw [isMultilinearFn_iff]
    intro p hp
    obtain ⟨c, p, rfl⟩ : ∃ c p', p = c :: p' := List.exists_cons_of_length_eq_add_one hp
    have hp' : p.length = m := by simpa using hp
    have h := (isMultilinearFn_iff m _).mp (ih (fun i ↦ a (i + 1)) (fun i ↦ b (i + 1))) p hp'
    rw [pow_succ, mul_comm, sum_range_two_mul]
    simp only [boolPoint_two_mul, boolPoint_two_mul_add_one, affProd, eqEval_cons]
    rw [h, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    linear_combination (-(a 0 * c + a 0 + b 0) * affProd (fun i ↦ a (i + 1)) (fun i ↦ b (i + 1))
      (boolPoint m x) * eqEval (boolPoint m x) p) * two_eq_zero_E

/-- The equality kernel at `z` as a product of affine factors. -/
theorem eqEval_eq_affProd : ∀ (z p : List E), z.length = p.length →
    eqEval z p = affProd (fun i ↦ 1 + z.getD i 0) (fun _ ↦ 1) p
  | [], [], _ => by simp [affProd]
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | x :: z, c :: p, h => by
    rw [eqEval_cons, affProd, eqEval_eq_affProd z p (by simpa using h)]
    simp

/-- `eq(z, ·)` is multilinear. -/
theorem isMultilinearFn_eqEval (z : List E) : IsMultilinearFn z.length (eqEval z) :=
  isMultilinearFn_congr (isMultilinearFn_affProd z.length _ _)
    fun p hp ↦ (eqEval_eq_affProd z p hp.symm).symm

/-- The index of the rotated cube point: `i ↦ ⌊i / 2^k⌋ + 2^n·(i mod 2^k)`. -/
def rotIndex (k n i : ℕ) : ℕ := i / 2 ^ k + 2 ^ n * (i % 2 ^ k)

/-- The rotated index stays on the cube. -/
theorem rotIndex_lt {k n i : ℕ} (hi : i < 2 ^ (k + n)) : rotIndex k n i < 2 ^ (n + k) := by
  rw [rotIndex, pow_add]
  refine add_mul_lt ?_ (Nat.mod_lt _ (by positivity))
  rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_add]
  exact hi

/-- Rotating back undoes the rotation. -/
theorem rotIndex_rotIndex {k n i : ℕ} (hi : i < 2 ^ (k + n)) :
    rotIndex n k (rotIndex k n i) = i := by
  have hq : i / 2 ^ k < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_add]; exact hi
  simp only [rotIndex]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hq, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq, Nat.mod_add_div]

/-- The cube point of the rotated index is the rotated point. -/
theorem boolPoint_rotIndex (k n i : ℕ) (hi : i < 2 ^ (k + n)) :
    boolPoint (n + k) (rotIndex k n i) =
      (boolPoint (k + n) i).drop k ++ (boolPoint (k + n) i).take k := by
  have hq : i / 2 ^ k < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_add]; exact hi
  have hsplit : boolPoint (k + n) i = boolPoint k (i % 2 ^ k) ++ boolPoint n (i / 2 ^ k) := by
    conv_lhs => rw [← Nat.mod_add_div i (2 ^ k)]
    exact boolPoint_add k n _ _ (Nat.mod_lt _ (by positivity))
  rw [rotIndex, boolPoint_add n k _ _ hq, hsplit]
  simp [length_boolPoint]

/-- Rotating both points keeps the equality kernel. -/
theorem eqEval_rotate (k : ℕ) (a b : List E) (h : a.length = b.length) :
    eqEval (a.drop k ++ a.take k) (b.drop k ++ b.take k) = eqEval a b := by
  rw [eqEval_append _ _ _ _ (by simp [h]), mul_comm, ← eqEval_append _ _ _ _ (by simp [h]),
    List.take_append_drop, List.take_append_drop]

/-- Reindex a sum over the cube by the rotation. -/
theorem sum_rotIndex (k n : ℕ) (f : ℕ → E) :
    ∑ i ∈ range (2 ^ (k + n)), f (rotIndex k n i) = ∑ x ∈ range (2 ^ (n + k)), f x := by
  refine sum_nbij' (rotIndex k n) (rotIndex n k) (fun i hi ↦ ?_) (fun x hx ↦ ?_)
    (fun i hi ↦ ?_) (fun x hx ↦ ?_) (fun _ _ ↦ rfl)
  · exact mem_range.mpr (rotIndex_lt (mem_range.mp hi))
  · exact mem_range.mpr (rotIndex_lt (mem_range.mp hx))
  · exact rotIndex_rotIndex (mem_range.mp hi)
  · exact rotIndex_rotIndex (mem_range.mp hx)

/-- **A function of the rotated point is multilinear** when the function is. -/
theorem isMultilinearFn_rotate {k n : ℕ} {w : List E → E} (hw : IsMultilinearFn (n + k) w) :
    IsMultilinearFn (k + n) fun p ↦ w (p.drop k ++ p.take k) := by
  rw [isMultilinearFn_iff] at hw ⊢
  intro p hp
  rw [hw _ (by simp [hp]), ← sum_rotIndex k n]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [boolPoint_rotIndex k n i (mem_range.mp hi), eqEval_rotate _ _ _
    (by rw [length_boolPoint, hp])]

end
end LeanVM.Protocol.Whir.Complete
end

-- ===== from `LvmWireKernel` =====

section
set_option autoImplicit false
namespace Lvm.WK
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

end Lvm.WK
end

section
set_option autoImplicit false
namespace Lvm.WK
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

end Lvm.WK
end

section
set_option autoImplicit false
namespace Lvm.WK
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

/-- The threshold sum with `ρ`'s top coordinates `ρ''` above `t`'s range is `eq(ρ'', 0)` times the sum on
`ρ'` (at `|ρ| = 17`, `m < 2^20`: `(1 + ρ_16)·thrEval ρ_{<16}`, so 20 bits of `m` suffice). -/
theorem thrEval_append (ρ' ρ'' μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ'.length + 5)) :
    thrEval (ρ' ++ ρ'') μ t = eqAt ρ'' 0 * thrEval ρ' μ t := by
  have ht' : t < 2 ^ ((ρ' ++ ρ'').length + 5) :=
    lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by simp))
  rw [← thrEval_eq _ μ t ht', ← thrEval_eq _ μ t ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have h16 : i / 32 < 2 ^ ρ'.length := by rw [pow_add] at ht; (clear * - ht hi'; omega)
  rw [iota, iota, eqAt_append, Nat.div_eq_of_lt h16]
  ring

/-- `MS` at `t = 0` is zero (an interval starting at `a = 1` needs one evaluation). -/
theorem msEval_zero (ρ μ σ : List E) (base : ℕ) (h4 : 5 ≤ σ.length) (hρ : σ.length - 5 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) : msEval ρ μ σ base 0 = 0 := by
  rw [← sum_msK ρ μ σ base 0 h4 hρ hb (Nat.two_pow_pos _)]
  exact Finset.sum_eq_zero fun x _ ↦ by simp [msK]

/-- A table supported on `x < 2^w`: its extension is the low part's times `eq(σ_{≥w}, 0)`. -/
theorem sum_eqAt_lowPad (σ : List E) (w : ℕ) (hw : w ≤ σ.length) (f : ℕ → E) :
    ∑ x ∈ range (2 ^ σ.length), eqAt σ x * (if x < 2 ^ w then f x else 0) =
      (∑ x ∈ range (2 ^ w), eqAt (σ.take w) x * f x) * eqAt (σ.drop w) 0 := by
  have hlen : (σ.take w).length = w := by simp; omega
  have hsub : range (2 ^ w) ⊆ range (2 ^ σ.length) :=
    Finset.range_subset_range.2 (Nat.pow_le_pow_right (by norm_num) hw)
  rw [← Finset.sum_subset hsub (fun x _ hx ↦ by rw [if_neg (by simpa using hx), mul_zero]),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  rw [if_pos hx']
  conv_lhs => rw [← List.take_append_drop w σ]
  rw [eqAt_append, hlen, Nat.div_eq_of_lt hx']
  ring

theorem bitsE_add : ∀ (t m k : ℕ), bitsE t (m + k) = bitsE t m ++ bitsE (t / 2 ^ m) k
  | t, 0, k => by simp [bitsE]
  | t, m + 1, k => by
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [bitsE, bitsE_add (t / 2) m k, List.cons_append, Nat.div_div_eq_div_mul, pow_succ,
      mul_comm 2 (2 ^ m)]

theorem bitsE_mod : ∀ (t m : ℕ), bitsE t m = bitsE (t % 2 ^ m) m
  | t, 0 => rfl
  | t, m + 1 => by
    simp only [bitsE]
    rw [Nat.mod_mod_of_dvd t (dvd_pow_self 2 (Nat.succ_ne_zero m)), pow_succ',
      Nat.mod_mul_right_div_self, ← bitsE_mod (t / 2) m]

theorem msStepA_bit (a r : E) (b : Bool) (q : MS4) :
    msStepA a r (if b then 1 else 0) q = msStep a r b q := by
  cases b <;> simp [msStepA, LeanVM.Protocol.Whir.Complete.one_add_one_E]

theorem msTailA_bitsE (σ ρ : List E) (h : σ.length = ρ.length) (t : ℕ) (ht : t < 2 ^ σ.length) :
    msTailA σ ρ (bitsE t σ.length) = msTail σ ρ t := by
  induction σ generalizing ρ t with
  | nil =>
    cases ρ with
    | nil =>
      have : t = 0 := by simpa using ht
      subst this; rfl
    | cons _ _ => simp at h
  | cons a σ ih =>
    cases ρ with
    | nil => simp at h
    | cons r ρ =>
      have h' : σ.length = ρ.length := by simpa using h
      have ht' : t / 2 < 2 ^ σ.length := by
        rw [List.length_cons, pow_succ] at ht; (clear * - ht; omega)
      simp only [List.length_cons, bitsE, msTailA, ih ρ h' (t / 2) ht', msTail]
      by_cases h1 : t % 2 = 1
      · rw [show (t % 2 == 1) = true by simp [h1], ← msStepA_bit, if_pos h1]; rfl
      · rw [show (t % 2 == 1) = false by simp [h1], ← msStepA_bit, if_neg h1]; rfl

/-- `ltE` on the bits of `u < 32` is `[u < e]`. -/
theorem ltE_bitsE (u e : ℕ) (hu : u < 32) (he : e ≤ 32) :
    ltE (bitsE u 5) e = if u < e then 1 else 0 := by
  rw [ltE, LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range,
    Finset.sum_congr rfl fun j hj ↦ eqAt_bitsE_lt (m := 5) (z := u) (w := j) (by norm_num; omega)
      (by have := Finset.mem_range.1 hj; norm_num; (clear * - he this; omega)),
    Finset.sum_ite_eq']
  by_cases h : u < e <;> simp [h]

theorem bits_split (t v : ℕ) :
    (bitsE t (v + 5)).take 5 = bitsE (t % 32) 5 ∧ (bitsE t (v + 5)).drop 5 = bitsE (t / 32) v := by
  rw [add_comm v 5, bitsE_add, bitsE_mod t 5]
  simp

/-- **The circuit's `MS`** on the bits of `t` and the top factor is `msEval`. -/
theorem msEvalA_bitsE (ρ μ σ : List E) (base t : ℕ) (h4 : 5 ≤ σ.length)
    (hρ : σ.length - 5 ≤ ρ.length) (ht : t < 2 ^ σ.length) :
    msEvalA ρ μ σ (bitsE t σ.length) (eqAt (ρ.drop (σ.length - 5)) (base / 2 ^ σ.length)) =
      msEval ρ μ σ base t := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 5 := ⟨σ.length - 5, by (clear * - h4; omega)⟩
  have hσh : (σ.drop 5).length = v := by simp; (clear * - h4 hv; omega)
  have hρh : (ρ.take (σ.length - 5)).length = v := by simp; (clear * - h4 hρ hv hσh; omega)
  have hpow : 2 ^ σ.length = 2 ^ v * 32 := by rw [hv, pow_add]; norm_num
  have hq : msTailA (σ.drop 5) (ρ.take (σ.length - 5)) (bitsE (t / 32) v) =
      msTail (σ.drop 5) (ρ.take (σ.length - 5)) (t / 32) := by
    have := msTailA_bitsE (σ.drop 5) (ρ.take (σ.length - 5)) (by rw [hσh, hρh]) (t / 32)
      (by rw [hσh]; (clear * - ht hpow; omega))
    rwa [hσh] at this
  have hb := bits_split t v
  rw [← hv] at hb
  simp only [msEvalA, msEval, hb.1, hb.2, hq]
  set q := msTail (σ.drop 5) (ρ.take (σ.length - 5)) (t / 32)
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, LeanVM.Protocol.Whir.Complete.sumE_eq,
    LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range, Lvm.KG.list_sum_map_range,
    Lvm.KG.list_sum_map_range, Finset.sum_range_succ _ 31]
  have hB : ∀ d ∈ range 31, eqAt (σ.take 5) d * μ.getD ((d + 1) % 32) 0 *
      q.get (d == 31) (decide (t % 32 < (d + 1) % 32)) =
      eqAt (σ.take 5) d * μ.getD ((d + 1) % 32) 0 * q.v00 + (q.v01 + q.v00) *
        (eqAt (σ.take 5) d * μ.getD ((d + 1) % 32) 0 * ltE (bitsE (t % 32) 5) (d + 1)) := by
    intro d hd
    have hd' := Finset.mem_range.1 hd
    have h15 : (d == 31) = false := by simp; (clear * - hd'; omega)
    rw [h15, Nat.mod_eq_of_lt (show d + 1 < 32 by (clear * - hd'; omega)), ltE_bitsE _ _ (by (clear * -; omega)) (by (clear * - hd'; omega))]
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    by_cases hs : t % 32 < d + 1
    · simp only [hs, decide_true, if_true, MS4.get]
      linear_combination (-(eqAt (σ.take 5) d * μ.getD (d + 1) 0 * q.v00)) * h2
    · simp only [hs, decide_false, if_false, MS4.get]
      ring
  rw [Finset.sum_congr rfl hB, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [show (31 == 31) = true from rfl, show (31 + 1) % 32 = 0 from rfl, Nat.not_lt_zero,
    decide_false, MS4.get]
  ring

theorem thrTailA_bitsE (ρ : List E) (t : ℕ) (ht : t < 2 ^ ρ.length) :
    thrTailA ρ (bitsE t ρ.length) = thrTail ρ t := by
  induction ρ generalizing t with
  | nil =>
    have : t = 0 := by simpa using ht
    subst this; rfl
  | cons r ρ ih =>
    have ht' : t / 2 < 2 ^ ρ.length := by
      rw [List.length_cons, pow_succ] at ht; (clear * - ht; omega)
    simp only [List.length_cons, bitsE, thrTailA, ih (t / 2) ht', thrTail]
    rcases Nat.mod_two_eq_zero_or_one t with h1 | h1 <;>
      simp [h1, nextS, LeanVM.Protocol.Whir.Complete.one_add_one_E]

/-- **The circuit's threshold sum** on the bits of `t` is `thrEval`. -/
theorem thrEvalA_bitsE (ρ μ : List E) (t : ℕ) (ht : t < 2 ^ (ρ.length + 5)) :
    thrEvalA ρ μ (bitsE t (ρ.length + 5)) = thrEval ρ μ t := by
  have hb := bits_split t ρ.length
  have hq : thrTailA ρ (bitsE (t / 32) ρ.length) = thrTail ρ (t / 32) :=
    thrTailA_bitsE ρ (t / 32) (by rw [pow_add] at ht; (clear * - ht; omega))
  simp only [thrEvalA, thrEval, hb.1, hb.2, hq]
  set q := thrTail ρ (t / 32)
  rw [LeanVM.Protocol.Whir.Complete.sumE_eq, LeanVM.Protocol.Whir.Complete.sumE_eq,
    LeanVM.Protocol.Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range, Lvm.KG.list_sum_map_range,
    Lvm.KG.list_sum_map_range, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Finset.mem_range.1 hd
  rw [ltE_bitsE _ _ (by (clear * -; omega)) (by (clear * - hd'; omega))]
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  by_cases hs : t % 32 < d
  · simp only [hs, if_true]
    linear_combination (μ.getD d 0 * q.1) * h2
  · simp only [hs, if_false]
    ring

end Lvm.WK
end

-- ===== from `LvmVFastQ` =====

section
set_option autoImplicit false
namespace Lvm.VF
open Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.M3 Lvm.Q1

/-- `QAsm.qprogT` with `phases47F` (the assembler's fixed-point iteration). -/
def qprogTF (C : QCfg) (D : QData) : BM Unit := do
  qlink C.p (lay C)
  let _ ← Lvm.QSig.qsig (sigIn C)
  phases47F C >>= Lvm.Har.qarithT C D

/-- **The node program on the record `D`, built in linear time.** -/
def QTF (C : QCfg) (D : QData) : Program := toProgramF (nK C) 0 (qprogTF C D)

theorem QTF_eq (C : QCfg) (D : QData) : QTF C D = QAsm.QT C D := by
  unfold QTF QAsm.QT qprogTF QAsm.qprogT phases47F Lvm.Har.phases47
  rw [tapeGadgetF_eq, gkrGadgetF_eq, toProgramF_eq]

/-- `Block.pieces` with the template as an array (`rowsOf` indexes the template list per row:
quadratic in a glue block's length, ≈ 8 s on the node program). -/
def blockPiecesF (B : Block) (b : Nat) : List Piece :=
  let A := B.tpl.toArray
  B.shapes.flatMap fun σ =>
    let rs := (List.range B.tpl.length).filter fun t => (A.getD t default).shape = σ
    (chunks (binParts rs.length) rs).map fun (a, ts) => ⟨b, σ, a, ts⟩

theorem blockPiecesF_eq (B : Block) (b : Nat) : blockPiecesF B b = B.pieces b := by
  unfold blockPiecesF Block.pieces Block.rowsOf
  simp only [toArray_getD]

/-- **`Program.pieces`**, blocks and templates as arrays. -/
def piecesF (Q : Program) : List Piece :=
  let bs := Q.blocks.toArray
  (List.range Q.blocks.length).flatMap fun b => blockPiecesF (bs.getD b default) b

theorem piecesF_eq (Q : Program) : piecesF Q = Q.pieces := by
  unfold piecesF Program.pieces Program.blk
  simp only [toArray_getD, blockPiecesF_eq]

/-- `cache` on the pieces `ps` (`cacheP Q Q.pieces = cache Q`). -/
def cacheP (Q : Program) (ps : List Piece) : PC :=
  let sK := psums (Q.blocks.map fun B => B.tw .K * B.size) Q.nInK
  let sE := psums (Q.blocks.map fun B => B.tw .E * B.size) Q.nInE
  ⟨Q, ((Q.blocks.zip (sK.zip sE)).map fun (B, k, e) => mkBC B k e).toArray,
    (ps.map fun p => (p, p.ts.toArray)).toArray,
    (ps.filter fun p => Q.glue.contains p.blk).flatMap fun p =>
      (p.shape.fcols.filter (· != .F)).map fun c => (p, c)⟩

theorem cacheP_eq (Q : Program) : cacheP Q Q.pieces = cache Q := rfl

/-- `BC.rank` with the template's length read off the array (`BC.rank` takes the list's length per
call: quadratic over a glue block's coefficients, ≈ 5.6 s at `P20`). -/
def rankF (bc : BC) (τ : Ty) (t : Nat) : Nat :=
  if t ≤ bc.tpl.size then (match τ with | .K => bc.rK | .E => bc.rE).getD t 0 else bc.B.rank τ t

/-- `colAffineF` with `rankF`. -/
def colAffineFF (bc : BC) (c : FCol) (t : Nat) : Nat × List Nat :=
  let r := bc.tpl.getD t default
  match c with
  | .res => (bc.start r.ty + rankF bc r.ty t, Loop.scaledStrides bc.B.dims (bc.tw r.ty))
  | .arg o => ((r.args.getD o default).base, (r.args.getD o default).strides)
  | _ => (0, [])

/-- `coefS` with `colAffineFF`. -/
def coefSF (bc : BC) (ts : Array Nat) (c : FCol) (i : Nat) : FE :=
  match c with
  | .res | .arg _ => FE.ofK (FK.x ^ (colAffineFF bc c (ts.getD i 0)).1)
  | .k | .k' => FE.ofK (kOf c (bc.tpl.getD (ts.getD i 0) default).op)
  | .F => 0

/-- `mkPE` with `coefSF`. -/
def mkPEF (bc : BC) (p : Piece) : M3.PE :=
  let ts := p.ts.toArray
  ⟨p, ts, (p.shape.fcols.filter (· != .F)).map fun c => (c, Array.ofFn (n := 2 ^ p.a) fun i => coefSF bc ts c i.val)⟩

theorem mkPEF_eq (bc : BC) (h : bc.tpl.size = bc.B.tpl.length) (p : Piece) : mkPEF bc p = mkPE bc p := by
  have hr : ∀ τ t, rankF bc τ t = bc.rank τ t := fun τ t => by
    unfold rankF BC.rank; rw [h]; cases τ <;> rfl
  have hc : ∀ c t, colAffineFF bc c t = colAffineF bc c t := fun c t => by
    unfold colAffineFF colAffineF; cases c <;> simp only [hr]
  have hs : ∀ ts c i, coefSF bc ts c i = coefS bc ts c i := fun ts c i => by
    unfold coefSF coefS; cases c <;> simp only [hc]
  unfold mkPEF mkPE
  simp only [hs]

theorem cache_bc_size (Q : Program) (b : Nat) : ((cache Q).bc b).tpl.size = ((cache Q).bc b).B.tpl.length := by
  rw [cache_bc]; simp [mkBC]

/-- **`cacheG`**: the pieces computed once (`cacheG` builds them three times), the coefficients with
`mkPEF`, one entry per glue piece. -/
def cacheGF (Q : Program) : PG :=
  let ps := piecesF Q
  let C := cacheP Q ps
  ⟨C, (ps.map fun p => mkPEF (C.bc p.blk) p).toArray,
    (ps.filter fun p => Q.glue.contains p.blk).flatMap fun p =>
      let pe := mkPEF (C.bc p.blk) p
      (p.shape.fcols.filter (· != .F)).map fun c => (pe, c)⟩

theorem cacheGF_eq (Q : Program) : cacheGF Q = cacheG Q := by
  unfold cacheGF cacheG
  simp only [piecesF_eq, cacheP_eq, Program.glueCols, List.map_flatMap, List.map_map,
    mkPEF_eq _ (cache_bc_size Q _)]
  rfl

end Lvm.VF
end

-- ===== from `LvmTypedLayQ` =====

section
section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har

/-- **The typed phases' end**: after the mini-bus's table phase (`tabEnd`). The schedule's tape phase must start
here (assumption 7; INT checks `phaseByte p .tape = typedEnd (typedPos p) + …` by `decide` at the refreeze). -/
def typedEnd (T : TData) (P : Nat) : Nat := tabEnd T.mbS T.mbR (busEndD T.mbD (mbP P))

end Lvm.QTyped
end
end

section
section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink

/-- **A cap read's target lies in its region**: `lo + 4·idx + r < lo + 4·2^c` for `idx < 2^c`, `r < 4`. -/
theorem capTarget_mem {lo c idx r : Nat} (hi : idx < 2 ^ c) (hr : r < 4) :
    lo ≤ lo + 4 * idx + r ∧ lo + 4 * idx + r < lo + 4 * 2 ^ c := by
  constructor <;> omega

/-- `K` aligned blocks of `m` rows from `x0`'s block reach every `x < x0 + c` (`K = ⌊(c + m − 2)/m⌋ + 1`). -/
theorem blocks_span {q0 x c m : Nat} (hm : 0 < m) (hx : x < q0 + c) :
    x / m - q0 / m < (c + m - 2) / m + 1 := by
  have e1 := Nat.div_add_mod q0 m
  have e2 := Nat.mod_lt q0 hm
  have e3 := Nat.div_mul_le_self x m
  have e5 := Nat.div_add_mod (c + m - 2) m
  have e6 := Nat.mod_lt (c + m - 2) hm
  have key : (x / m - q0 / m) * m < ((c + m - 2) / m + 1) * m := by
    rw [Nat.sub_mul, Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm] at e1 e5
    omega
  exact Nat.lt_of_mul_lt_mul_right key

/-- **The blocks cover the lane class's rows**: a lane `p ∈ [a, a + n)` of class `p % 17` lies in a block. -/
theorem laneBlocks_cover {a n t p : Nat} (hp : a ≤ p) (hpn : p < a + n) :
    ∃ q ∈ laneBlocks a n (p % 17) t, q ≤ p / 17 ∧ p / 17 < q + 2 ^ t := by
  have h17 := Nat.div_add_mod p 17
  have hl : p % 17 < 17 := Nat.mod_lt _ (by decide)
  have ht : 0 < 2 ^ t := Nat.two_pow_pos t
  have hq0 : (a + 16 - p % 17) / 17 ≤ p / 17 := by
    have : (a + 16 - p % 17) / 17 < p / 17 + 1 := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    omega
  have hq1 : p / 17 < (a + 16 - p % 17) / 17 + (n + 16) / 17 := by
    have h1 := Nat.div_add_mod (a + 16 - p % 17) 17
    have h2 := Nat.mod_lt (a + 16 - p % 17) (show 17 > 0 by decide)
    have h3 := Nat.div_add_mod (n + 16) 17
    have h4 := Nat.mod_lt (n + 16) (show 17 > 0 by decide)
    omega
  have hb : (a + 16 - p % 17) / 17 / 2 ^ t ≤ p / 17 / 2 ^ t := Nat.div_le_div_right hq0
  refine ⟨p / 17 / 2 ^ t * 2 ^ t, ?_, Nat.div_mul_le_self _ _, ?_⟩
  · simp only [laneBlocks, laneRows, List.mem_map, List.mem_range]
    exact ⟨p / 17 / 2 ^ t - (a + 16 - p % 17) / 17 / 2 ^ t, blocks_span ht hq1,
      by rw [Nat.add_sub_cancel' hb]⟩
  · have h5 := Nat.div_add_mod (p / 17) (2 ^ t)
    have h6 := Nat.mod_lt (p / 17) ht
    rw [Nat.mul_comm] at h5
    omega

/-- **Every cap cell is seeded**: a lane `p` of a cap region `(a, c)` of `capRegions` lies in a seeded block
`(p % 17, q)` of `mbBlocks`. -/
theorem mbSeed_cover {p : Params} {a c x : Nat} (hc : (a, c) ∈ capRegions p) (h1 : a ≤ x)
    (h2 : x < a + 4 * 2 ^ c) :
    ∃ q, (x % 17, q) ∈ mbBlocks p ∧ q ≤ x / 17 ∧ x / 17 < q + 2 ^ mbBlk := by
  obtain ⟨q, hq, hq1, hq2⟩ := laneBlocks_cover (t := mbBlk) h1 h2
  refine ⟨q, ?_, hq1, hq2⟩
  simp only [mbBlocks, List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨(a, c), hc, x % 17, Nat.mod_lt _ (by decide), q, hq, rfl⟩

/-- **A cap read is seeded**: the target `lo + 4·idx + r` of a read of region `(lo, c)` lies in a seeded block. -/
theorem capRead_seeded {p : Params} {lo c idx r : Nat} (hc : (lo, c) ∈ capRegions p) (hi : idx < 2 ^ c)
    (hr : r < 4) :
    ∃ q, ((lo + 4 * idx + r) % 17, q) ∈ mbBlocks p ∧ q ≤ (lo + 4 * idx + r) / 17 ∧
      (lo + 4 * idx + r) / 17 < q + 2 ^ mbBlk :=
  mbSeed_cover hc (capTarget_mem hi hr).1 (capTarget_mem hi hr).2

/-- **Seeded blocks are disjoint**: two blocks of `mbBlocks` sharing a cell are equal (aligned blocks of one
size). -/
theorem mbBlocks_disjoint {p : Params} {l l' q q' x : Nat} (hb : (l, q) ∈ mbBlocks p) (hb' : (l', q') ∈ mbBlocks p)
    (hx : q ≤ x ∧ x < q + 2 ^ mbBlk) (hx' : q' ≤ x ∧ x < q' + 2 ^ mbBlk) : q = q' := by
  have al : ∀ {l q}, (l, q) ∈ mbBlocks p → q % 2 ^ mbBlk = 0 := by
    intro l q h
    simp only [mbBlocks, List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_range, laneBlocks] at h
    obtain ⟨_, _, _, _, _, ⟨i, _, rfl⟩, he⟩ := h
    cases he
    exact Nat.mul_mod_left _ _
  have h1 := al hb
  have h2 := al hb'
  simp only [show (2 : Nat) ^ mbBlk = 16 from rfl] at h1 h2 hx hx'
  omega

end Lvm.QTyped
end
end

section
section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig

/-- The B program on the placeholder record. -/
def QBP (C : QCfg) : Program := QB C (tdataP C)

end Lvm.QTyped
end
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm

/-- **The typed layout of the B program `QB C T`** (the dense intervals to a fixpoint; offline). -/
def layB (C : QCfg) (T : QTyped.TData) : Lay := let Q := QTyped.QB C T; mkLay Q (specQ C Q)

/-- **The typed layout of `QB C T` on frozen dense intervals** `dints` (the fixpoint's result, a record as
`QData`: what V and the prover build at start-up). -/
def layBD (C : QCfg) (T : QTyped.TData) (dints : Array (Ty × ℕ × ℕ)) : Lay :=
  let Q := QTyped.QB C T; (mkLayD Q (specQ C Q) dints).1

end Lvm.Typed
end

-- ===== from `LvmE2QNodeChkG` =====

section
set_option autoImplicit false
namespace Lvm.QTyped
open Lvm Lvm.Loop Lvm.QAsm Lvm.Typed Lvm.TypedV

theorem nodeChkB_eq (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) :
    nodeChkB C F Q lay N = nodeChkBG (spongeBlocks P20) pubLanes C F Q lay N := rfl

end Lvm.QTyped
end
