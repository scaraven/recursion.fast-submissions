-- New for `flock-recursive` (BLUEPRINT A.11, stage S-E3; track L-circ).
import FRVIRTplTab

/-!
# Replay templates: Lagrange weights, `eqZ`, `lagrangeS`, `eqTableK`, `dotKF`

BLUEPRINT A.11. Each template mirrors its op's implementation in `implC` gate for gate
(`FRVerifierImplOps`' `lagW`, `eqZI`, `lagrangeSI`; `FRVIR`'s `eqTab` over `K` and `dotKF`), and
its `tplX_ok` is the identity between the gate equations and that implementation.

* `lagG`: the `N` weights `lagW x N den z` at a form `z` (prefix and suffix running products,
  then one product per weight; `lagG_ev`);
* `mulKG`: one `K` product over forms (Karatsuba, three gates; `mulKG_ev`); `eqTblKG`: `eqTab`
  over `K`, one `K` product per new entry (`eqTblKG_ev`).
-/

namespace FR
namespace Tpl
open Circ

variable {e : Env}

/-! ## Helpers -/

theorem nlocs_appendL (a b : List Gate) : nlocs (a ++ b) = nlocs a + nlocs b := by
  simp [nlocs]

theorem ev_getD_lag (l : List LinT) (i : ℕ) :
    (l.getD i []).ev e = (l.map (LinT.ev e)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- `Σ_{i<n} f i` as a form. -/
def sumLT (n : ℕ) (f : ℕ → LinT) : LinT := (List.range n).flatMap f

theorem ev_sumLT (n : ℕ) (f : ℕ → LinT) :
    (sumLT n f).ev e = ∑ i ∈ Finset.range n, (f i).ev e := by
  induction n with
  | zero => simp [sumLT]
  | succ n ih =>
    rw [sumLT, List.range_succ, List.flatMap_append, ev_append, ← sumLT, ih,
      Finset.sum_range_succ]
    simp

theorem ofFn_getD_lag {n : ℕ} (f : Fin n → F) {u : ℕ} (hu : u < n) :
    (Array.ofFn f).getD u 0 = f ⟨u, hu⟩ := by
  simp [Array.getD_eq_getD_getElem?, hu]

theorem dot_eq_sum (t s : Array F) {n : ℕ} (ht : t.size = n) :
    dot t s = ∑ u ∈ Finset.range n, t.getD u 0 * s.getD u 0 := by
  rw [dot, sumTo_eq, ht]

/-! ## Lagrange weights (`Impl.lagW`) -/

/-- The factor `z − x_j`. -/
def lfac (x : ℕ → F) (z : LinT) (j : ℕ) : LinT := z ++ C (-x j)

theorem lfac_ev (h1 : e.one = 1) (x : ℕ → F) (z : LinT) (j : ℕ) :
    (lfac x z j).ev e = z.ev e - x j := by
  simp [lfac, h1, sub_eq_add_neg]

/-- **The `N` Lagrange weights** `numL x N i z · den_i` at a form `z`, locals from `k`: the prefix
products `Π_{j<i} (z − x_j)` and the suffix products `Π_{i<j<N} (z − x_j)` (two running products
of `N − 1` gates each, the second over the factors in reverse), then one product per weight;
weight `i` is `den_i` times the last. -/
def lagG (x : ℕ → F) (N : ℕ) (den : Array F) (z : LinT) (k : ℕ) : List Gate × List LinT :=
  let p := scanG (C 1) ((List.range (N - 1)).map (lfac x z)) k
  let s := scanG (C 1) ((List.range (N - 1)).map fun t => lfac x z (N - 1 - t)) (k + (N - 1))
  (p.1 ++ s.1 ++
      mulsG N (fun i => p.2.getD i []) (fun i => s.2.getD (N - 1 - i) []),
    (List.range N).map fun i => sc (den.getD i 0) (L (k + (N - 1) + (N - 1) + i)))

theorem lagG_nlocs (x : ℕ → F) (N : ℕ) (den : Array F) (z : LinT) (k : ℕ) :
    nlocs (lagG x N den z k).1 = 2 * (N - 1) + N := by
  simp only [lagG, nlocs_appendL, scanG_nlocs, mulsG_nlocs, List.length_map, List.length_range]
  omega

theorem lagW_size (x : ℕ → F) (N : ℕ) (den : Array F) (z : F) : (Impl.lagW x N den z).size = N := by
  simp [Impl.lagW]

theorem lagG_length (x : ℕ → F) (N : ℕ) (den : Array F) (z : LinT) (k : ℕ) :
    (lagG x N den z k).2.length = N := by
  simp [lagG]

theorem scanl_mul_getD (a : F) (l : List F) {i : ℕ} (hi : i ≤ l.length) :
    (List.scanl (· * ·) a l).getD i 0 = a * (l.take i).prod := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_scanl]
  simpa using foldl_mul_eq (fun y : F => y) (l.take i) a

theorem othersN_eq {N i : ℕ} (hi : i < N) :
    Impl.othersN N i = List.range i ++ List.range' (i + 1) (N - (i + 1)) := by
  have hN : List.range N = List.range i ++ i :: List.range' (i + 1) (N - (i + 1)) := by
    have := List.range'_append_1 (s := 0) (m := i) (n := N - i)
    rw [zero_add] at this
    rw [List.range_eq_range', List.range_eq_range', ← List.range'_succ,
      show N - (i + 1) + 1 = N - i by omega, this]
    congr 1; omega
  rw [Impl.othersN, hN, List.filter_append, List.filter_cons_of_neg (by simp),
    List.filter_eq_self.2, List.filter_eq_self.2]
  · intro a ha; simp only [List.mem_range'_1] at ha; simp; omega
  · intro a ha; simp only [List.mem_range] at ha; simp; omega

theorem range_rev {N i : ℕ} (hi : i < N) :
    (List.range (N - 1 - i)).map (fun t => N - 1 - t) =
      (List.range' (i + 1) (N - (i + 1))).reverse := by
  refine List.ext_getElem (by simp; omega) fun t h₁ h₂ => ?_
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.getElem_range',
    List.length_range']
  omega

/-- **The weights**: under the gate equations, weight `i` is `(lagW x N den z).getD i 0`. -/
theorem lagG_ev (h1 : e.one = 1) (x : ℕ → F) (N : ℕ) (den : Array F) (z : LinT) (k : ℕ)
    (h : Eqns e (lagG x N den z k).1 k) {i : ℕ} (hi : i < N) :
    ((lagG x N den z k).2.getD i []).ev e = (Impl.lagW x N den (z.ev e)).getD i 0 := by
  simp only [lagG, Eqns.append, nlocs_appendL, scanG_nlocs, List.length_map,
    List.length_range] at h
  obtain ⟨⟨hp, hs⟩, hm⟩ := h
  have hp' := scanG_ev _ _ _ hp
  have hs' := scanG_ev _ _ _ hs
  have hm' := mulsG_eqns hm i hi
  have hg : ∀ j, (lfac x z j).ev e = z.ev e - x j := lfac_ev h1 x z
  show (((List.range N).map fun i => sc (den.getD i 0) (L (k + (N - 1) + (N - 1) + i))).getD i
    []).ev e = _
  have hpre : ((scanG (C 1) ((List.range (N - 1)).map (lfac x z)) k).2.getD i []).ev e =
      ((List.range i).map fun j => z.ev e - x j).prod := by
    rw [ev_getD_lag, hp',
      scanl_mul_getD _ _ (by simp only [List.length_map, List.length_range]; omega), ev_C, h1,
      mul_one, one_mul, List.map_map, ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
    exact congrArg List.prod (List.map_congr_left fun j _ => hg j)
  have hsuf : ((scanG (C 1) ((List.range (N - 1)).map fun t => lfac x z (N - 1 - t))
      (k + (N - 1))).2.getD (N - 1 - i) []).ev e =
      ((List.range' (i + 1) (N - (i + 1))).map fun j => z.ev e - x j).prod := by
    rw [ev_getD_lag, hs',
      scanl_mul_getD _ _ (by simp only [List.length_map, List.length_range]; omega), ev_C, h1,
      mul_one, one_mul, List.map_map, ← List.map_take, List.take_range, Nat.min_eq_left (by omega),
      ← List.prod_reverse (List.map _ (List.range' _ _)), ← List.map_reverse, ← range_rev hi,
      List.map_map]
    exact congrArg List.prod (List.map_congr_left fun t _ => hg _)
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range, ev_sc, ev_L]
  rw [Nat.add_assoc k (N - 1) (N - 1), hm', hpre, hsuf, Impl.lagW_getD _ _ _ _ hi, Impl.numL,
    foldl_mul_eq, one_mul, othersN_eq hi, List.map_append, List.prod_append]
  ring

/-! ## `eqZ` (`Impl.eqZI`) -/

/-- **`eqZ`** (inputs `λ`, `ρ₁`): the 64 weights `L_j(λ)` on `S` (`lagG`), then `L_j · ρ₁`
(64 gates); output `i < 64` is `L_i − L_i ρ₁`, output `64 + j` is `L_j ρ₁`. -/
def tplEqZ : Tpl :=
  let g := lagG Impl.xT 64 Impl.denS (I 0) 0
  ⟨g.1 ++ mulsG 64 (fun j => g.2.getD j []) (fun _ => I 1),
    (List.range 128).map fun i =>
      if i < 64 then g.2.getD i [] ++ sc (-1) (L (nlocs g.1 + i)) else L (nlocs g.1 + (i - 64))⟩

theorem eqZI_size (l ρ : F) : (Impl.eqZI l ρ).size = 128 := Array.size_ofFn ..

theorem tplEqZ_ok (h1 : e.one = 1) {l ρ : F} (hi : InpIs e [l, ρ])
    (h : Eqns e tplEqZ.gates 0) :
    tplEqZ.outs.map (LinT.ev e) = encV (.af (Impl.eqZI l ρ)) := by
  simp only [tplEqZ, Eqns.append, zero_add] at h
  have hl : (I 0).ev e = l := by rw [ev_I, hi]; rfl
  have hr : (I 1).ev e = ρ := by rw [ev_I, hi]; rfl
  have hw := fun j (hj : j < 64) => lagG_ev h1 _ _ _ _ _ h.1 hj
  rw [hl] at hw
  have hm := mulsG_eqns h.2
  simp only [hr] at hm
  simp only [tplEqZ, encV]
  refine List.ext_getElem (by simp only [List.length_map, List.length_range, Array.length_toList,
    eqZI_size]) fun i h₁ h₂ => ?_
  have hi : i < 128 := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Impl.eqZI,
    Array.getElem_ofFn]
  by_cases hlo : i < 64
  · have hb : i.testBit 6 = false := Nat.testBit_lt_two_pow (by norm_num; omega)
    simp only [hlo, hb, Bool.false_eq_true, ↓reduceIte]
    rw [ev_append, ev_sc, ev_L, hm i hlo, hw i hlo, Nat.mod_eq_of_lt hlo]
    ring
  · have hb : i.testBit 6 = true := by rw [Nat.testBit_eq_decide_div_mod_eq]; simp; omega
    simp only [hlo, hb, ↓reduceIte]
    rw [ev_L, hm (i - 64) (by omega), hw _ (by omega),
      show i % 64 = i - 64 by omega]

/-- `eqZ`'s locals (one per gate): `190 + 64`. -/
theorem tplEqZ_nlocs : nlocs tplEqZ.gates = 254 := by
  simp only [tplEqZ, nlocs_appendL, lagG_nlocs, mulsG_nlocs]

/-! ## `lagrangeS` (`Impl.lagrangeSI`) -/

/-- Input `off + k` if `k < n`, else `0`. -/
def segIn (off n k : ℕ) : LinT := if k < n then I (off + k) else []

theorem segIn_ev {xs ys : List F} {a : Array F} (hi : InpIs e (xs ++ a.toList ++ ys)) (k : ℕ) :
    (segIn xs.length a.size k).ev e = a.getD k 0 := by
  by_cases hk : k < a.size
  · simp only [segIn, hk, ↓reduceIte]
    rw [ev_I, hi, List.append_assoc, getD_append_right,
      getD_append_left (by simpa using hk), arr_getD]
  · simp only [segIn, hk, ↓reduceIte]
    rw [ev_nil, ← arr_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega)]
    rfl

/-- `P^z`'s weights at a node of `S`: an array of 64. -/
theorem lamAtS_size {b : ℕ} (hb : b < 64) : (Impl.lamAtS.getD b #[]).size = 64 := by
  rw [Array.getD_eq_getD_getElem?, Impl.lamAtS, Array.getElem?_ofFn]
  simp [hb, Impl.lagW]

/-- The value form `vals_b` of `lagrangeSI` (inputs `v` from `0`, `pe` from `n + 1`). -/
def valT (n m b : ℕ) : LinT :=
  if b < 64 then
    sumLT 64 (fun u => sc ((Impl.lamAtS.getD b #[]).getD u 0) (segIn 0 n u)) ++ segIn (n + 1) m b
  else segIn 0 n b

/-- **`lagrangeS`** for `v : AF n`, `λ`, `pe : AF m` (inputs in that order): the 127 weights on
`S ∪ Λ₀…₆₂` and the 64 on `Λ` at `λ` (`lagG`), the 127 products with the value forms `vals_b`
(linear: the constant weights `lamAtS`), the 64 products with `v₀…₆₃`; the two sums. -/
def tplLagrangeS (n m : ℕ) : Tpl :=
  let a := lagG Impl.xT 127 Impl.den127 (I n) 0
  let b := lagG Impl.lamX 64 Impl.denL (I n) (nlocs a.1)
  let k := nlocs a.1 + nlocs b.1
  ⟨a.1 ++ b.1 ++ mulsG 127 (fun j => a.2.getD j []) (valT n m) ++
      mulsG 64 (fun u => b.2.getD u []) (segIn 0 n),
    [sumLT 127 fun j => L (k + j), sumLT 64 fun u => L (k + 127 + u)]⟩

theorem tplLagrangeS_ok (h1 : e.one = 1) {v pe : Array F} {l : F}
    (hi : InpIs e (v.toList ++ [l] ++ pe.toList))
    (h : Eqns e (tplLagrangeS v.size pe.size).gates 0) :
    (tplLagrangeS v.size pe.size).outs.map (LinT.ev e) =
      encV (.f (Impl.lagrangeSI v l pe).1) ++ encV (.f (Impl.lagrangeSI v l pe).2) := by
  have hv : ∀ u, (segIn 0 v.size u).ev e = v.getD u 0 := segIn_ev (xs := [])
    (ys := [l] ++ pe.toList) (fun i => by rw [hi]; simp)
  have hp : ∀ u, (segIn (v.size + 1) pe.size u).ev e = pe.getD u 0 := by
    have := segIn_ev (xs := v.toList ++ [l]) (ys := []) (a := pe) (fun i => by rw [hi]; simp)
    simpa using this
  have hl : (I v.size).ev e = l := by
    rw [ev_I, hi, ← Array.length_toList, List.append_assoc, ← add_zero v.toList.length,
      getD_append_right]; rfl
  simp only [tplLagrangeS, Eqns.append, nlocs_appendL, mulsG_nlocs, zero_add] at h
  obtain ⟨⟨⟨ha, hb⟩, hm1⟩, hm2⟩ := h
  have hwa := fun j (hj : j < 127) => lagG_ev h1 _ _ _ _ _ ha hj
  have hwb := fun j (hj : j < 64) => lagG_ev h1 _ _ _ _ _ hb hj
  rw [hl] at hwa hwb
  have hm1' := mulsG_eqns hm1
  have hm2' := mulsG_eqns hm2
  simp only [tplLagrangeS, List.map_cons, List.map_nil, encV, List.cons_append, List.nil_append,
    List.cons.injEq, and_true, ev_sumLT, ev_L, Impl.lagrangeSI]
  constructor
  · rw [dot_eq_sum _ _ (lagW_size ..)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    rw [hm1' j hj, hwa j hj, ofFn_getD_lag _ hj]
    congr 1
    unfold valT
    split_ifs with hj'
    · rw [ev_append, ev_sumLT, hp, dot_eq_sum _ _ (lamAtS_size hj')]
      congr 1
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [ev_sc, hv, ofFn_getD_lag _ (Finset.mem_range.1 hu)]
    · exact hv j
  · rw [dot_eq_sum _ _ (lagW_size ..)]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu := Finset.mem_range.1 hu
    rw [hm2' u hu, hwb u hu, hv, ofFn_getD_lag _ hu]

/-- `lagrangeS`'s locals (one per gate): `379 + 190 + 127 + 64`. -/
theorem tplLagrangeS_nlocs (n m : ℕ) : nlocs (tplLagrangeS n m).gates = 760 := by
  simp only [tplLagrangeS, nlocs_appendL, lagG_nlocs, mulsG_nlocs]

/-! ## `K` products over forms -/

/-- A `K` value of a pair of forms (its two `F` components). -/
def evK (e : Env) (p : LinT × LinT) : K := ⟨p.1.ev e, p.2.ev e⟩

theorem K_ext' {x y : K} (h0 : x.f₀ = y.f₀) (h1 : x.f₁ = y.f₁) : x = y := by
  obtain ⟨a0, a1⟩ := x; obtain ⟨b0, b1⟩ := y
  dsimp only at h0 h1; subst h0; subst h1; rfl

theorem K_add_f₀ (a b : K) : (a + b).f₀ = a.f₀ + b.f₀ := rfl
theorem K_add_f₁ (a b : K) : (a + b).f₁ = a.f₁ + b.f₁ := rfl
theorem K_one_sub_f₀ (x : K) : (1 - x).f₀ = 1 + x.f₀ := rfl
theorem K_one_sub_f₁ (x : K) : (1 - x).f₁ = 0 + x.f₁ := rfl

/-- `t (1 − x) = t + t x` in `K` (characteristic 2). -/
theorem K_mul_one_sub (t x : K) : t * (1 - x) = t + t * x := by
  apply K_ext'
  · rw [K_mul_f₀, K_add_f₀, K_mul_f₀, K_one_sub_f₀, K_one_sub_f₁]; ring
  · rw [K_mul_f₁, K_add_f₁, K_mul_f₁, K_one_sub_f₀, K_one_sub_f₁]
    linear_combination t.f₀ * (CharTwo.two_eq_zero (R := F))

/-- **A `K` product** `a · b` over forms, locals `k, k+1, k+2`: `a₀b₀`, `a₁b₁`,
`(a₀+a₁)(b₀+b₁)` (Karatsuba, as `K.mul`). -/
def mulKG (a b : LinT × LinT) (k : ℕ) : List Gate × (LinT × LinT) :=
  ([.mul a.1 b.1, .mul a.2 b.2, .mul (a.1 ++ a.2) (b.1 ++ b.2)],
    (L k ++ sc F.alpha (L (k + 1)), L (k + 2) ++ L k))

theorem mulKG_nlocs (a b : LinT × LinT) (k : ℕ) : nlocs (mulKG a b k).1 = 3 := rfl

theorem mulKG_ev (a b : LinT × LinT) (k : ℕ) (h : Eqns e (mulKG a b k).1 k) :
    evK e (mulKG a b k).2 = evK e a * evK e b := by
  simp only [mulKG, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  have h2' : e.loc (k + 2) = (a.1 ++ a.2).ev e * (b.1 ++ b.2).ev e := h2
  apply K_ext'
  · rw [K_mul_f₀]; simp only [evK, mulKG, ev_append, ev_sc, ev_L, h0, h1]
  · rw [K_mul_f₁]; simp only [evK, mulKG, ev_append, ev_L, h0, h2']

/-! ## `eqTableK` (`FR.eqTab` over `K`) -/

/-- Per table entry `t`: the `K` product `p = t · x` (3 gates), and the pair `(t + p, p)`, i.e.
`t (1 − x)` and `t x`. -/
def mulTblKG (x : LinT × LinT) :
    List (LinT × LinT) → ℕ → List Gate × List ((LinT × LinT) × (LinT × LinT))
  | [], _ => ([], [])
  | t :: ts, k =>
    let m := mulKG t x k
    let r := mulTblKG x ts (k + 3)
    (m.1 ++ r.1, ((t.1 ++ m.2.1, t.2 ++ m.2.2), m.2) :: r.2)

theorem mulTblKG_nlocs (x : LinT × LinT) :
    ∀ (ts : List (LinT × LinT)) (k : ℕ), nlocs (mulTblKG x ts k).1 = 3 * ts.length
  | [], _ => rfl
  | t :: ts, k => by
    rw [mulTblKG, nlocs_appendL, mulKG_nlocs, mulTblKG_nlocs x ts, List.length_cons]; ring

theorem mulTblKG_ev (x : LinT × LinT) :
    ∀ (ts : List (LinT × LinT)) (k : ℕ), Eqns e (mulTblKG x ts k).1 k →
      (mulTblKG x ts k).2.map (fun q => evK e q.1) = (ts.map (evK e)).map (· * (1 - evK e x)) ∧
      (mulTblKG x ts k).2.map (fun q => evK e q.2) = (ts.map (evK e)).map (· * evK e x)
  | [], _, _ => ⟨rfl, rfl⟩
  | t :: ts, k, h => by
    rw [mulTblKG, Eqns.append, mulKG_nlocs] at h
    have hm := mulKG_ev _ _ _ h.1
    have ih := mulTblKG_ev x ts (k + 3) h.2
    simp only [mulTblKG, List.map_cons, ih.1, ih.2, List.cons.injEq, and_true]
    refine ⟨?_, hm⟩
    rw [K_mul_one_sub, ← hm]
    exact K_ext' (by simp only [evK, ev_append, K_add_f₀]) (by simp only [evK, ev_append, K_add_f₁])

/-- **`eqTab` over forms**: per coordinate `x` (the first first), the table `t` becomes
`t (1 − x) ++ t x`. -/
def eqTblKG : List (LinT × LinT) → List (LinT × LinT) → ℕ → List Gate × List (LinT × LinT)
  | [], t, _ => ([], t)
  | x :: xs, t, k =>
    let m := mulTblKG x t k
    let r := eqTblKG xs (m.2.map Prod.fst ++ m.2.map Prod.snd) (k + 3 * t.length)
    (m.1 ++ r.1, r.2)

theorem mulTblKG_length (x : LinT × LinT) :
    ∀ (ts : List (LinT × LinT)) (k : ℕ), (mulTblKG x ts k).2.length = ts.length
  | [], _ => rfl
  | t :: ts, k => by rw [mulTblKG, List.length_cons, mulTblKG_length x ts, List.length_cons]

theorem eqTblKG_size : ∀ (xs t : List (LinT × LinT)) (k : ℕ),
    (eqTblKG xs t k).2.length = t.length * 2 ^ xs.length ∧
      nlocs (eqTblKG xs t k).1 + 3 * t.length = 3 * t.length * 2 ^ xs.length
  | [], t, k => by simp [eqTblKG, nlocs]
  | x :: xs, t, k => by
    have ih := eqTblKG_size xs ((mulTblKG x t k).2.map Prod.fst ++ (mulTblKG x t k).2.map Prod.snd)
      (k + 3 * t.length)
    simp only [List.length_append, List.length_map, mulTblKG_length] at ih
    simp only [eqTblKG, nlocs_appendL, mulTblKG_nlocs, List.length_cons, pow_succ]
    constructor
    · rw [ih.1]; ring
    · linarith [ih.2]

/-- One step of `eqTab`, on lists. -/
def eqStepL (t : List K) (x : K) : List K := t.map (· * (1 - x)) ++ t.map (· * x)

theorem eqTblKG_ev : ∀ (xs t : List (LinT × LinT)) (k : ℕ), Eqns e (eqTblKG xs t k).1 k →
    (eqTblKG xs t k).2.map (evK e) = (xs.map (evK e)).foldl eqStepL (t.map (evK e))
  | [], t, k, _ => rfl
  | x :: xs, t, k, h => by
    rw [eqTblKG, Eqns.append, mulTblKG_nlocs] at h
    have hm := mulTblKG_ev x t k h.1
    simp only [eqTblKG, List.map_cons, List.foldl_cons]
    rw [eqTblKG_ev xs _ _ h.2, List.map_append, List.map_map, List.map_map, Function.comp_def,
      Function.comp_def, hm.1, hm.2]
    rfl

theorem eqTab_toList (r : Array K) : (eqTab r).toList = r.toList.foldl eqStepL [1] := by
  have : ∀ (l : List K) (a : Array K),
      (l.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) a).toList =
        l.foldl eqStepL a.toList := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x l ih => intro a; rw [List.foldl_cons, ih, List.foldl_cons]; simp [eqStepL]
  rw [eqTab, ← Array.foldl_toList, this]

theorem length_flatMap_encK (l : List K) : (l.flatMap encK).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.length_append, ih, encK]; simp; ring

theorem encK_getD (l : List K) (j : ℕ) :
    (l.flatMap encK).getD (2 * j) 0 = (l.getD j 0).f₀ ∧
      (l.flatMap encK).getD (2 * j + 1) 0 = (l.getD j 0).f₁ := by
  induction l generalizing j with
  | nil => exact ⟨by simp; rfl, by simp; rfl⟩
  | cons x l ih =>
    cases j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j =>
      rw [List.flatMap_cons, encK, List.cons_append, List.cons_append, List.nil_append,
        show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
        List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ]
      exact ih j

theorem flat_evK (l : List (LinT × LinT)) :
    (l.flatMap fun p => [p.1, p.2]).map (LinT.ev e) = (l.map (evK e)).flatMap encK := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [List.flatMap_cons, ih, evK, encK]

/-- **`eqTableK`** for `r : AK v` (coordinate `j` at inputs `2j`, `2j+1`): `eqTab` over forms
from the table `[1]`; outputs the `2·2^v` components. -/
def tplEqTableK (v : ℕ) : Tpl :=
  let g := eqTblKG ((List.range v).map fun j => (I (2 * j), I (2 * j + 1))) [(C 1, [])] 0
  ⟨g.1, g.2.flatMap fun p => [p.1, p.2]⟩

theorem tplEqTableK_ok (h1 : e.one = 1) {r : Array K} (hi : InpIs e (r.toList.flatMap encK))
    (h : Eqns e (tplEqTableK r.size).gates 0) :
    (tplEqTableK r.size).outs.map (LinT.ev e) = encV (.ak (eqTab r)) := by
  have hx : ((List.range r.size).map fun j => (I (2 * j), I (2 * j + 1))).map (evK e) =
      r.toList := by
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    have := encK_getD r.toList j
    rw [List.getD_eq_getElem _ _ h₂] at this
    simp only [List.getElem_map, List.getElem_range, evK, ev_I]
    exact K_ext' ((hi _).trans this.1) ((hi _).trans this.2)
  simp only [tplEqTableK, encV] at h ⊢
  rw [flat_evK, eqTblKG_ev _ _ _ h, hx, eqTab_toList]
  congr 2
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact K_ext' (by simp [evK, h1]; rfl) (by simp [evK]; rfl)

/-- `eqTableK`'s locals (one per gate): `3 (2^v − 1)`. -/
theorem tplEqTableK_nlocs (v : ℕ) : nlocs (tplEqTableK v).gates + 3 = 3 * 2 ^ v := by
  simpa [tplEqTableK] using (eqTblKG_size ((List.range v).map fun j => (I (2 * j), I (2 * j + 1)))
    [(C 1, [])] 0).2

/-! ## `dotKF` (`FR.dotKF`) -/

theorem foldl_smulF (cs : List F) :
    ∀ (ws : List K) (a : K),
      (((List.zipWith (fun c x => K.smulF c x) cs ws).foldl (· + ·) a).f₀ =
        a.f₀ + ∑ b ∈ Finset.range ws.length, cs.getD b 0 * (ws.getD b 0).f₀) ∧
      (((List.zipWith (fun c x => K.smulF c x) cs ws).foldl (· + ·) a).f₁ =
        a.f₁ + ∑ b ∈ Finset.range ws.length, cs.getD b 0 * (ws.getD b 0).f₁) := by
  induction cs with
  | nil => intro ws a; simp
  | cons c cs ih =>
    intro ws a
    cases ws with
    | nil => simp
    | cons w ws =>
      rw [List.zipWith_cons_cons, List.foldl_cons, (ih ws _).1, (ih ws _).2, List.length_cons,
        Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, K_add_f₀, K_add_f₁, K.smulF]
      constructor <;> ring

/-- **`dotKF`** for `w : AK n` (inputs `0 … 2n−1`) and the column's `F` elements (inputs
`2n … 3n−1`): `c_b · w_b` componentwise (`K.smulF`, 2 gates per `b`); the last two gates also add
the other products (`mulAdd`, S-E5), so the outputs are two locals and the template keeps `2n`
rows. -/
def tplDotKF : ℕ → Tpl
  | 0 => ⟨[], [[], []]⟩
  | n + 1 =>
    ⟨mulsG (2 * n) (fun v => I (2 * (n + 1) + v / 2)) I ++
      [.mulAdd (I (2 * (n + 1) + n)) (I (2 * n)) (sumLT n fun b => L (2 * b)),
       .mulAdd (I (2 * (n + 1) + n)) (I (2 * n + 1)) (sumLT n fun b => L (2 * b + 1))],
     [L (2 * n), L (2 * n + 1)]⟩

theorem tplDotKF_ok {n : ℕ} {w : Array K} {col : ByteArray} (hw : w.size = n)
    (hi : InpIs e (w.toList.flatMap encK ++ (List.range n).map fun b => (felems col).getD b 0))
    (h : Eqns e (tplDotKF n).gates 0) :
    (tplDotKF n).outs.map (LinT.ev e) = encV (.k (dotKF w col)) := by
  cases n with
  | zero =>
    obtain rfl : w = #[] := Array.eq_empty_of_size_eq_zero hw
    have hd := foldl_smulF (felems col).toList ([] : List K) 0
    simp only [tplDotKF, List.map_cons, List.map_nil, encV, encK, dotKF, ← Array.foldl_toList,
      Array.toList_zipWith, List.cons.injEq, and_true]
    rw [hd.1, hd.2]
    simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero]
    exact ⟨rfl, rfl⟩
  | succ n =>
    simp only [tplDotKF, Eqns.append, mulsG_nlocs, Eqns.cons, Gate.Eqn, Gate.nloc,
      zero_add] at h
    obtain ⟨h, g1, g2, -⟩ := h
    have hm := mulsG_eqns h
    have hlen : (w.toList.flatMap encK).length = 2 * (n + 1) := by
      rw [length_flatMap_encK, Array.length_toList, hw]
    have hw0 : ∀ b < n + 1, e.inp (2 * b) = (w.toList.getD b 0).f₀ := fun b hb => by
      rw [hi, getD_append_left (by omega), (encK_getD _ _).1]
    have hw1 : ∀ b < n + 1, e.inp (2 * b + 1) = (w.toList.getD b 0).f₁ := fun b hb => by
      rw [hi, getD_append_left (by omega), (encK_getD _ _).2]
    have hc : ∀ b < n + 1, e.inp (2 * (n + 1) + b) = (felems col).toList.getD b 0 := fun b hb => by
      rw [hi, ← hlen, getD_append_right, List.getD_eq_getElem _ _ (by simpa using hb),
        List.getElem_map, List.getElem_range, arr_getD]
    have hd := foldl_smulF (felems col).toList w.toList 0
    rw [Array.length_toList, hw] at hd
    simp only [tplDotKF, List.map_cons, List.map_nil, ev_L, g1, g2, ev_sumLT, ev_I]
    simp only [encV, encK, dotKF, ← Array.foldl_toList,
      Array.toList_zipWith, hd.1, hd.2, List.cons.injEq, and_true]
    constructor
    · rw [Finset.sum_range_succ, show (0 : K).f₀ = 0 from rfl, zero_add, hc n (by omega),
        hw0 n (by omega), add_comm]
      congr 1
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb := Finset.mem_range.1 hb
      rw [← zero_add (2 * b), hm (2 * b) (by omega), ev_I, ev_I,
        show 2 * b / 2 = b by omega, hc b (by omega), hw0 b (by omega)]
    · rw [Finset.sum_range_succ, show (0 : K).f₁ = 0 from rfl, zero_add, hc n (by omega),
        hw1 n (by omega), add_comm]
      congr 1
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb := Finset.mem_range.1 hb
      rw [← zero_add (2 * b + 1), hm (2 * b + 1) (by omega), ev_I, ev_I,
        show (2 * b + 1) / 2 = b by omega, hc b (by omega), hw1 b (by omega)]

/-- `dotKF`'s locals (one per gate): `2n`. -/
theorem tplDotKF_nlocs (n : ℕ) : nlocs (tplDotKF n).gates = 2 * n := by
  cases n with
  | zero => rfl
  | succ n =>
    have := mulsG_nlocs (2 * n) (fun v => I (2 * (n + 1) + v / 2)) I
    simp only [tplDotKF, nlocs, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      Gate.nloc, List.sum_cons, List.sum_nil] at this ⊢
    omega

end Tpl
end FR
