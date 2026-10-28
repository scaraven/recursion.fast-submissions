-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-1): the position-free
-- declarations of the 3.x soundness modules that revision 4.1 reuses, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessTail` (14), `FRSoundnessTailD` (1),
-- `FRSoundnessTailO` (2), `FRSoundnessCompose` (1), `FRSoundnessLigFinal` (11). Content: the tail's
-- position-free lemmas (`tabs`, `e2`, `trueSum_tabs_fold`, `bindL_range_getD`, `getD_bindAll`,
-- `clR2_same`, `agree_ext`, `hEll_le`, `N_le`) and LigFinal's `mleP` padding lemmas. The 3.x
-- modules import this one.
import FRSoundnessCoreWeights

/-! ## From `FRSoundnessTail` (14 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

variable {L es L' es' : Log} {p : ℕ}

theorem eqBits_congr {R : Type*} [CommRing R] {r r' : ℕ → R} {ℓ : ℕ}
    (h : ∀ v < ℓ, r v = r' v) (x : ℕ) : eqBits r ℓ x = eqBits r' ℓ x := by
  unfold eqBits bitSel; exact prod_congr rfl fun v hv => by simp only [h v (mem_range.1 hv)]

/-- The product summand of the K sumchecks (P1.i, Pf). -/
def e2 : Expr := .mul (.var 0) (.var 1)

theorem e2_deg : e2.deg = 2 := rfl

/-- Two tables of size `2^m`. -/
noncomputable def tabs (W f : ℕ → K) (m : ℕ) : Array (Array K) :=
  #[Array.ofFn (n := 2 ^ m) fun y => W y, Array.ofFn (n := 2 ^ m) fun y => f y]

theorem tabs_size (W f : ℕ → K) (m : ℕ) : ∀ t ∈ tabs W f m, t.size = 2 ^ m := by
  intro t ht
  simp only [tabs, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact Array.size_ofFn

theorem getD_bindAll {R : Type*} [CommRing R] :
    ∀ (rs : List R) (ts : Array (Array R)) (k : ℕ),
      (bindAll ts rs).getD k #[] = bindL (ts.getD k #[]) rs
  | [], _, _ => rfl
  | r :: rs, ts, k => by
    rw [bindAll, getD_bindAll rs, getD_map_bind0]; rfl

/-- The top-bit split of an `eq`-weighted sum (as in `pf_succ`). -/
theorem sum_eqBits_succ {R : Type*} [CommRing R] (s : ℕ → R) (ℓ x : ℕ) (G : ℕ → R) :
    ∑ u ∈ range (2 ^ (ℓ + 1)), eqBits s (ℓ + 1) u * G (u + 2 ^ (ℓ + 1) * x) =
      ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * G (u + 2 ^ ℓ * (2 * x)) +
        s ℓ * (∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * G (u + 2 ^ ℓ * (2 * x + 1)) -
          ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * G (u + 2 ^ ℓ * (2 * x))) := by
  have hr : range (2 ^ (ℓ + 1)) = range (2 ^ ℓ + 2 ^ ℓ) := by congr 1; ring
  have s1 : ∑ u ∈ range (2 ^ ℓ), eqBits s (ℓ + 1) u * G (u + 2 ^ (ℓ + 1) * x) =
      ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * (1 - s ℓ) * G (u + 2 ^ ℓ * (2 * x)) :=
    sum_congr rfl fun u hu => by
      rw [show eqBits s (ℓ + 1) u = _ from bitSel_succ_lo _ _ (mem_range.1 hu),
        show u + 2 ^ (ℓ + 1) * x = u + 2 ^ ℓ * (2 * x) by ring]; rfl
  have s2 : ∑ u ∈ range (2 ^ ℓ), eqBits s (ℓ + 1) (2 ^ ℓ + u) *
      G (2 ^ ℓ + u + 2 ^ (ℓ + 1) * x) =
      ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * s ℓ * G (u + 2 ^ ℓ * (2 * x + 1)) :=
    sum_congr rfl fun u hu => by
      rw [show eqBits s (ℓ + 1) (2 ^ ℓ + u) = _ from bitSel_succ_hi _ _ (mem_range.1 hu),
        show 2 ^ ℓ + u + 2 ^ (ℓ + 1) * x = u + 2 ^ ℓ * (2 * x + 1) by ring]; rfl
  rw [hr, sum_range_add, s1, s2, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun u _ => by ring

/-- **Binding the first `ℓ` variables** at `s 0, …, s (ℓ−1)`: entry `x` of the bound table is
`Σ_{u<2^ℓ} eq(s, u)·t[u + 2^ℓ x]`. -/
theorem bindL_range_getD {R : Type*} [CommRing R] (s : ℕ → R) :
    ∀ (ℓ m : ℕ) (t : Array R), t.size = 2 ^ (ℓ + m) → ∀ x < 2 ^ m,
      (bindL t ((List.range ℓ).map s)).getD x 0 =
        ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * t.getD (u + 2 ^ ℓ * x) 0
  | 0, m, t, _, x, _ => by simp [bindL, eqBits, bitSel]
  | ℓ + 1, m, t, ht, x, hx => by
    rw [List.range_succ, List.map_append, List.map_singleton, bindL_append,
      sum_eqBits_succ s ℓ x (fun y => t.getD y 0)]
    have hs : (bindL t ((List.range ℓ).map s)).size = 2 ^ (m + 1) :=
      bindL_size _ t (by rw [ht, List.length_map, List.length_range]; congr 1; ring)
    have ih := bindL_range_getD s ℓ (m + 1) t (by rw [ht]; congr 1; ring)
    rw [← ih (2 * x) (by rw [pow_succ]; omega), ← ih (2 * x + 1) (by rw [pow_succ]; omega)]
    have h2 : 2 * x + 1 < (bindL t ((List.range ℓ).map s)).size := by rw [hs, pow_succ]; omega
    simp only [bind0, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hs,
      show x < 2 ^ (m + 1) / 2 by rw [pow_succ, Nat.mul_div_cancel _ two_pos]; exact hx,
      dite_true, Option.getD_some, Array.getElem?_eq_getElem h2,
      Array.getElem?_eq_getElem (show 2 * x < (bindL t ((List.range ℓ).map s)).size by omega)]

/-- The two-table summand's true sum. -/
theorem trueSum_e2 (ts : Array (Array K)) (m : ℕ) :
    trueSum e2 ts m = ∑ u ∈ range (2 ^ m), (ts.getD 0 #[]).getD u 0 * (ts.getD 1 #[]).getD u 0 := by
  rw [trueSum, ← Fin.sum_univ_eq_sum_range (fun u => (ts.getD 0 #[]).getD u 0 *
    (ts.getD 1 #[]).getD u 0)]
  exact sum_congr rfl fun u _ => by simp only [e2, Expr.eval, tbl]

theorem tabs_getD0 (W f : ℕ → K) (m : ℕ) :
    (tabs W f m).getD 0 #[] = Array.ofFn (n := 2 ^ m) fun y => W y := rfl

theorem tabs_getD1 (W f : ℕ → K) (m : ℕ) :
    (tabs W f m).getD 1 #[] = Array.ofFn (n := 2 ^ m) fun y => f y := rfl

theorem ofFn_getD {n y : ℕ} (g : ℕ → K) (h : y < n) :
    (Array.ofFn (n := n) fun x => g x).getD y 0 = g y := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem trueSum_tabs (W f : ℕ → K) (m : ℕ) :
    trueSum e2 (tabs W f m) m = ∑ y ∈ range (2 ^ m), W y * f y := by
  rw [trueSum_e2]
  refine sum_congr rfl fun y hy => ?_
  rw [tabs_getD0, tabs_getD1, ofFn_getD _ (mem_range.1 hy), ofFn_getD _ (mem_range.1 hy)]

/-- **After `ℓ` rounds the true sum is the folded inner product** `⟨foldW W, fold(f)⟩`. -/
theorem trueSum_tabs_fold (s : ℕ → K) (ℓ m : ℕ) (W f : ℕ → K) :
    trueSum e2 (bindAll (tabs W f (ℓ + m)) ((List.range ℓ).map s)) m =
      ∑ x ∈ range (2 ^ m), foldW ℓ s W x *
        ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * f (u + 2 ^ ℓ * x) := by
  rw [trueSum_e2, getD_bindAll, getD_bindAll]
  refine sum_congr rfl fun x hx => ?_
  have hx' := mem_range.1 hx
  have hsz := tabs_size W f (ℓ + m)
  rw [tabs_getD0, tabs_getD1, bindL_range_getD s ℓ m _ Array.size_ofFn x hx',
    bindL_range_getD s ℓ m _ Array.size_ofFn x hx', foldW,
    Fin.sum_univ_eq_sum_range (fun u => eqBits s ℓ u * W (u + 2 ^ ℓ * x)) (2 ^ ℓ)]
  refine congrArg₂ (· * ·) (sum_congr rfl fun u hu => ?_) (sum_congr rfl fun u hu => ?_)
  · have : u + 2 ^ ℓ * x < 2 ^ (ℓ + m) := by
      have := mem_range.1 hu; rw [pow_add]; nlinarith
    rw [ofFn_getD _ this]
  · have : u + 2 ^ ℓ * x < 2 ^ (ℓ + m) := by
      have := mem_range.1 hu; rw [pow_add]; nlinarith
    rw [ofFn_getD _ this]

end FR.Snd

/-! ## From `FRSoundnessTailD` (1 declaration) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

theorem clR2_same {R : Type*} [Field R] {b wd : ℕ} {rd : ByteArray → ℕ → R} {ch : Digest → R}
    {c0 : Log → Log → R} {L L' es es' : Log} (hc : c0 L es = c0 L' es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) →
      clR2 b wd rd ch c0 L es l = clR2 b wd rd ch c0 L' es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR2]
    simp only [g2At, rch2, ansAt, msgAt, h (b + 2 * l) (by omega), h (b + 2 * l + 1) (by omega)]

end FR.Snd

/-! ## From `FRSoundnessTailO` (2 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

theorem agree_ext (es₀ : Log) (as : List Digest) : Agree (ext es₀ as) es₀ es₀.length :=
  fun q hq => by rw [← entAt_take (es := ext es₀ as) hq, take_ext]

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem hEll_le {i : ℕ} (hi : i < 5) : hEll i ≤ 6 := by
  unfold hEll lvlStar; interval_cases i <;> decide

end FR.Snd

/-! ## From `FRSoundnessCompose` (1 declaration) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

variable {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K}
  {c₀ : Log → Log → K}

theorem N_le : ((239 * 2 ^ 128 : ℕ) : ℝ≥0) ≤ 2 ^ 256 * deltaR := batch_N_le le_rfl

end FR.Snd

/-! ## From `FRSoundnessLigFinal` (11 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

theorem length_take_succ {es : Log} {p : ℕ} (hp : p < es.length) :
    (es.take (p + 1)).length = p + 1 := by
  rw [List.length_take]; omega

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

/-- Binding every variable of a table of `2^n` entries at a list of `n` challenges evaluates its
extension there. -/
theorem bindL_ofFn_mle {n : ℕ} (g : ℕ → K) (cs : List K) (hl : cs.length = n) :
    tbl 0 (bindL (Array.ofFn (n := 2 ^ n) fun y => g y) cs) 0 = mleN n g (ptOf n cs) := by
  subst hl
  rw [bindL_mle _ _ (Array.size_ofFn ..), mleN, pt_eq_ptOf]
  congr 1
  funext u; exact ofFn_getD g u.2

/-- The extension of `W`'s first `2^n` entries at the ℕ-indexed point `ρ`. -/
noncomputable def mleP (n : ℕ) (W ρ : ℕ → K) : K := mleN n W (fun v => ρ v)

theorem fin_append_nat {a b : ℕ} (s ρ : ℕ → K) (v : Fin (a + b)) :
    Fin.append (fun u : Fin a => s u) (fun u : Fin b => ρ u) v =
      if (v : ℕ) < a then s v else ρ (v - a) := by
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · simp [Fin.append_left, u.2]
  · simp [Fin.append_right]

theorem mleP_zero (W ρ : ℕ → K) : mleP 0 W ρ = W 0 := by
  rw [mleP, mleN, mle_zero]; rfl

/-- The point of a table indexed by `ℕ` (`Fin.append` of a prefix and the rest, as in
`mle_split`). -/
theorem mleP_pt_split (m k : ℕ) (W ρ : ℕ → K) :
    mleP (m + k) W ρ = mle (fun u : Fin (2 ^ (m + k)) => W u)
      (Fin.append (fun v : Fin m => ρ v) (fun v : Fin k => ρ (m + v))) := by
  unfold mleP mleN
  congr 1
  funext v
  rw [fin_append_nat ρ (fun u => ρ (m + u))]
  split_ifs with h
  · rfl
  · congr 1; omega

/-- **Zero padding** (A.9 `finPf`'s `P30` factor): a table zero from `2^m` on has, over `n ≥ m`
variables, the extension over `m` times `Π_{m ≤ v < n} (1 − ρ_v)`. -/
theorem mleP_pad {m n : ℕ} (hmn : m ≤ n) {W : ℕ → K} (hW : ∀ x, 2 ^ m ≤ x → W x = 0)
    (ρ : ℕ → K) : mleP n W ρ = mleP m W ρ * ∏ v ∈ Ico m n, (1 - ρ v) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [mleP_pt_split, mle_split]
  have hin : ∀ u₁ : Fin (2 ^ m), mle (fun u₂ : Fin (2 ^ k) =>
      (fun u : Fin (2 ^ (m + k)) => W u) (join u₁ u₂)) (fun v : Fin k => ρ (m + v)) =
      (∏ v ∈ Ico m (m + k), (1 - ρ v)) * W u₁ := fun u₁ => by
    have hf : (fun u₂ : Fin (2 ^ k) => (fun u : Fin (2 ^ (m + k)) => W u) (join u₁ u₂)) =
        fun u₂ => if u₂ = 0 then W u₁ else 0 := by
      funext u₂
      simp only [join]
      split_ifs with h
      · subst h; simp
      · refine hW _ ?_
        have : 1 ≤ u₂.val := Nat.one_le_iff_ne_zero.mpr fun h' => h (Fin.ext h')
        nlinarith [u₁.2, Nat.one_le_two_pow (n := m)]
    rw [hf, mle]
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true, eq_cube]
    congr 1
    rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel_left, ← Fin.prod_univ_eq_prod_range]
    exact prod_congr rfl fun v _ => by simp
  refine (sum_congr rfl fun u₁ _ => congrArg _ (hin u₁)).trans ?_
  unfold mleP mleN mle
  rw [sum_mul]
  exact sum_congr rfl fun u _ => by ring

theorem bytesAt_empty (o n : ℕ) : bytesAt ByteArray.empty o n = Vector.replicate n 0 := by
  ext k hk; simp [bytesAt, byteAt, Vector.getElem_ofFn]

theorem msgAt_nil (p : ℕ) : msgAt [] p = ByteArray.empty := by
  simp [msgAt, entAt]; decide

theorem K_ofBytes_zero : K.ofBytes (Vector.replicate 32 0) = 0 := by decide

theorem readK_nil (p o : ℕ) : readK (msgAt [] p) o = 0 := by
  rw [readK, msgAt_nil, bytesAt_empty, K_ofBytes_zero]

end FR.Snd
