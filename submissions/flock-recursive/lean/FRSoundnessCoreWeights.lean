-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-1): the position-free
-- declarations of the 3.x soundness modules that revision 4.1 reuses, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessPIOP` (1), `FRSoundnessWeights` (12),
-- `FRSoundnessFold` (11). Content: `algebraMap_f₀`, the weights' multilinear algebra (`mleN`,
-- `bitProd`, `eqCell`, `w0F`, `foldW`, `mleN_foldW`) and the fold's generic part (`CloseN`,
-- `closeN_unfold`, `foldN`, `mlDoomF_step`). The 3.x modules import this one.
import FRSoundnessCoreHide

/-! ## From `FRSoundnessPIOP` (1 declaration) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

theorem algebraMap_f₀ (c : F) : (algebraMap F K c).f₀ = c := rfl

end FR.Snd

/-! ## From `FRSoundnessWeights` (12 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

/-- The multilinear extension of the table `W` on its first `2^n` entries. -/
noncomputable def mleN (n : ℕ) (W : ℕ → K) (ρ : Fin n → K) : K := mle (fun u : Fin (2 ^ n) => W u) ρ

theorem uK_sub_one : K.u - 1 = 1 + K.u := by
  rw [sub_eq_add_neg, CharTwo.neg_eq, add_comm]

/-- Binding level `i`'s `ℓ` row variables at `s` (row bits low: `y = r + 2^ℓ·x`). -/
noncomputable def foldW (ℓ : ℕ) (s : ℕ → K) (W : ℕ → K) (x : ℕ) : K :=
  ∑ r : Fin (2 ^ ℓ), eqBits s ℓ r * W (r + 2 ^ ℓ * x)

/-- **Binding is evaluating**: the extension of the bound table at `ρ` is `W̃(s, ρ)`. -/
theorem mleN_foldW (ℓ n : ℕ) (s : ℕ → K) (W : ℕ → K) (ρ : Fin n → K) :
    mleN n (foldW ℓ s W) ρ = mleN (ℓ + n) W (Fin.append (fun v : Fin ℓ => s v) ρ) := by
  rw [mleN, mleN, mle_split]
  simp only [foldW]
  rw [mle_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [eqBits_eq_eq]
  congr 2
  funext u
  simp only [join]
  congr 1; ring

/-- `bitProd` splits off its lowest bit. -/
theorem bitProd_dbl (a : ℕ → K) (n : ℕ) (u : Fin (2 ^ n)) (b : Bool) :
    bitProd a (n + 1) (dbl u b).val =
      (if b then a 0 else 1) * bitProd (fun v => a (v + 1)) n u := by
  simp only [bitProd, bitSel, dbl]
  rw [prod_range_succ']
  have h0 : (2 * u.val + b.toNat).testBit 0 = b := by
    cases b <;> simp [Nat.testBit_zero, Nat.mul_mod_right]
  have hs : ∀ i, (2 * u.val + b.toNat).testBit (i + 1) = u.val.testBit i := fun i => by
    cases b <;> simp [Nat.testBit_succ, Nat.mul_add_div]
  simp only [h0, hs]
  rw [mul_comm]
  cases b <;> simp

/-- **A product-of-bits table's extension** is the tensor product
`Π_v (1 − ρ_v + ρ_v a_v)`. -/
theorem mle_bitProd : ∀ (n : ℕ) (a : ℕ → K) (ρ : Fin n → K),
    mle (fun u : Fin (2 ^ n) => bitProd a n u) ρ = ∏ v : Fin n, (1 - ρ v + ρ v * a v)
  | 0, a, ρ => by rw [mle_zero]; simp [bitProd, bitSel]
  | n + 1, a, ρ => by
    rw [mle_fix0]
    have : fix0 (fun u : Fin (2 ^ (n + 1)) => bitProd a (n + 1) u) (ρ 0) =
        fun u : Fin (2 ^ n) => (1 - ρ 0 + ρ 0 * a 0) * bitProd (fun v => a (v + 1)) n u := by
      funext u
      simp only [fix0, bitProd_dbl, Bool.false_eq_true, ite_false, ite_true]
      ring
    rw [this, mle_smul, mle_bitProd n, Fin.prod_univ_succ]
    rfl

section Level0

/-- **Level 0's table** (A.9 `Ŵ₀`, F-valued on the cube; revision 3.13): the RS weight `Wrs` (all
four claims, E4's included) and the public cells' indicators weighted `κ′^(k+2)` (A.7's order). -/
def w0F (Wrs : ℕ → F) (cells : List ℕ) (kp : F) (y : ℕ) : F :=
  Wrs y + ∑ k ∈ range cells.length, kp ^ (k + 2) * if y = cells.getD k 0 then 1 else 0

theorem foldl_mulK (g : ℕ → K) :
    ∀ (xs : List ℕ) (c : K), (xs.map g).foldl (· * ·) c = c * (xs.map g).prod
  | [], c => by simp
  | x :: xs, c => by
    rw [List.map_cons, List.foldl_cons, foldl_mulK g xs, List.prod_cons]; ring

/-- `eq(ρ, cube(c))` at a natural `c` (bit `v` of `c` against coordinate `v`). -/
def eqCell {n : ℕ} (ρ : Fin n → K) (c : ℕ) : K := ∏ v : Fin n, if c.testBit v then ρ v else 1 - ρ v

/-- A cell's indicator table extends to `eqCell`. -/
theorem mle_ind {n c : ℕ} (hc : c < 2 ^ n) (ρ : Fin n → K) :
    mle (fun u : Fin (2 ^ n) => if (u : ℕ) = c then (1 : K) else 0) ρ = eqCell ρ c := by
  rw [mle, sum_eq_single (⟨c, hc⟩ : Fin (2 ^ n)) (fun u _ hu => by
    rw [ite_eq_right fun h => absurd (Fin.ext h) hu, mul_zero]) (by simp), ite_eq_left rfl,
    mul_one, eq_cube]
  rfl

/-- **Level 0's extension** (`w0V`'s shape): the RS weight's and `Σ_k κ′^(k+2) eq(cell_k, ρ)`. -/
theorem mleN_w0F (Wrs : ℕ → F) (cells : List ℕ) (kp : F) {n : ℕ}
    (hc : ∀ c ∈ cells, c < 2 ^ n) (ρ : Fin n → K) :
    mleN n (fun y => algebraMap F K (w0F Wrs cells kp y)) ρ =
      mleN n (fun y => algebraMap F K (Wrs y)) ρ +
        ∑ k ∈ range cells.length, algebraMap F K (kp ^ (k + 2)) * eqCell ρ (cells.getD k 0) := by
  have h : (fun u : Fin (2 ^ n) => algebraMap F K (w0F Wrs cells kp u)) =
      (fun u : Fin (2 ^ n) => algebraMap F K (Wrs u)) +
        fun u : Fin (2 ^ n) => ∑ k ∈ range cells.length, algebraMap F K (kp ^ (k + 2)) *
          (if (u : ℕ) = cells.getD k 0 then (1 : K) else 0) := by
    funext u
    simp only [w0F, map_add, map_mul, map_sum, Pi.add_apply]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [mleN, h, mle_add, mle_sum]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [mle_ind (hc _ (by rw [List.getD_eq_getElem _ _ (mem_range.mp hk)]; exact List.getElem_mem _))]

/-- Control (positive): with no RS weight and one cell `c`, level 0's table reads `f[c]` weighted
`κ′²`. -/
theorem w0F_cell (kp : F) (c y : ℕ) :
    w0F (fun _ => 0) [c] kp y = if y = c then kp ^ 2 else 0 := by
  simp [w0F]

end Level0

end FR.Snd

/-! ## From `FRSoundnessFold` (11 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

section Generic

variable {K' : Type*} [Field K'] [DecidableEq K'] {n : ℕ}

/-- `ι`-indexed rows are close iff their reindexing is. -/
theorem jointClose_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (σ : ι' ≃ ι)
    {C : Submodule K' (Fin n → K')} {e : ℕ} {U : ι → Fin n → K'} {A : Finset (Fin n)} :
    JointClose C e (U ∘ σ) A ↔ JointClose C e U A := by
  constructor
  · rintro ⟨hA, V, hV, rfl⟩
    refine ⟨hA, V ∘ σ.symm, fun i => hV _, ?_⟩
    ext j
    simp only [mem_jointAgree, Function.comp_apply]
    exact ⟨fun h i' => by simpa using h (σ i'), fun h i => by simpa using h (σ.symm i)⟩
  · rintro ⟨hA, V, hV, rfl⟩
    refine ⟨hA, V ∘ σ, fun i => hV _, ?_⟩
    ext j
    simp only [mem_jointAgree, Function.comp_apply]
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i' => h (σ i')⟩

/-- Rows `0 … 2m−1` as (parity, half). -/
def evOdd (m : ℕ) : Fin (2 * m) ≃ Bool × Fin m where
  toFun r := (r.val % 2 = 1, ⟨r.val / 2, by omega⟩)
  invFun p := ⟨2 * p.2.val + (if p.1 then 1 else 0), by have := p.2.2; split <;> omega⟩
  left_inv r := by
    ext
    simp only [decide_eq_true_eq]
    split <;> omega
  right_inv p := by
    obtain ⟨b, c⟩ := p
    cases b <;> refine Prod.ext ?_ (Fin.ext ?_)
    all_goals simp
    all_goals omega

/-- The first `m` ℕ-indexed rows are jointly close. -/
def CloseN (C : Submodule K' (Fin n → K')) (e m : ℕ) (U : ℕ → Fin n → K') : Prop :=
  ∃ A, JointClose C e (fun r : Fin m => U r) A

/-- One fold of rows `2c`, `2c + 1` at `z`. -/
def foldN (z : K') (U : ℕ → Fin n → K') (c : ℕ) : Fin n → K' :=
  U (2 * c) + z • (U (2 * c + 1) - U (2 * c))

/-- **Closeness survives a fold** (no bad-set condition: fold the codewords too). -/
theorem closeN_fold {C : Submodule K' (Fin n → K')} {e m : ℕ} {U : ℕ → Fin n → K'} (z : K')
    (h : CloseN C e (2 * m) U) : CloseN C e m (foldN z U) := by
  classical
  obtain ⟨A, hA, V, hV, hVA⟩ := h
  let V' : Fin m → Fin n → K' := fun c =>
    V ⟨2 * c, by omega⟩ + z • (V ⟨2 * c + 1, by omega⟩ - V ⟨2 * c, by omega⟩)
  refine ⟨_, ?_, V', fun c => add_mem (hV _) (Submodule.smul_mem _ _ (sub_mem (hV _) (hV _))),
    rfl⟩
  refine hA.trans (card_le_card fun j hj => ?_)
  rw [← hVA, mem_jointAgree] at hj
  rw [mem_jointAgree]
  intro c
  have h0 := hj ⟨2 * c, by omega⟩
  have h1 := hj ⟨2 * c + 1, by omega⟩
  simp only [foldN, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, V'] at h0 h1 ⊢
  rw [h0, h1]

/-- **A fold that becomes close from far rows hit a bad line** (`fold_lift`): if the fold at `z`
is close and `z` is in no line's bad set, the rows were close. -/
theorem closeN_unfold {x : Fin n → K'} (hx : Function.Injective x) {k e m : ℕ}
    (hk : 2 * e + k ≤ n) {U : ℕ → Fin n → K'} {z : K'}
    (hz : ∀ c : Fin m, z ∉ lineBad (rsCode x k) e (U (2 * c)) (U (2 * c + 1)))
    (h : CloseN (rsCode x k) e m (foldN z U)) : CloseN (rsCode x k) e (2 * m) U := by
  obtain ⟨A, hA, W, hW, hWA⟩ := h
  obtain ⟨V₀, V₁, hV₀, hV₁, -, hV⟩ := fold_lift (U₀ := fun c : Fin m => U (2 * c))
    (U₁ := fun c : Fin m => U (2 * c + 1)) hx hk hz hA hW hWA
  have hc : JointClose (rsCode x k) e (pairRows (fun c : Fin m => U (2 * c))
      (fun c : Fin m => U (2 * c + 1))) A :=
    ⟨hA, pairRows V₀ V₁, fun ⟨b, c⟩ => by cases b <;> simp [hV₀, hV₁], hV⟩
  refine ⟨A, ?_⟩
  rw [← jointClose_equiv (evOdd m)] at hc
  convert hc using 2
  funext r
  simp only [Function.comp_apply, evOdd, Equiv.coe_fn_mk, pairRows, decide_eq_true_eq]
  split <;> congr 1 <;> omega

end Generic

theorem two_pow_sub {ℓ l : ℕ} (h : l < ℓ) : 2 ^ (ℓ - l) = 2 * 2 ^ (ℓ - (l + 1)) := by
  rw [← pow_succ']; congr 1; omega

theorem sum_eqBits_one {R : Type*} [CommRing R] (r : ℕ → R) (ℓ : ℕ) :
    ∑ q ∈ range (2 ^ ℓ), eqBits r ℓ q = 1 := by
  have := tensor_identity r (fun _ => 1) ℓ
  simp only [bitProd, mul_one, sub_add_cancel, prod_const_one] at this
  rw [← this]
  refine sum_congr rfl fun q _ => ?_
  simp [bitSel]

theorem algebraMap_eqBits (r : ℕ → F) (ℓ q : ℕ) :
    algebraMap F K (eqBits r ℓ q) = eqBits (fun v => algebraMap F K (r v)) ℓ q := by
  simp only [eqBits, bitSel, map_prod, apply_ite, map_sub, map_one]

open Classical in
/-- **Binding F coordinates (embedded in K) of a K table**: each loses at most one value. -/
theorem mlDoomF_step {n : ℕ} {t : Array K} (ht : t.size = 2 ^ n) (l : List F)
    (hd : mlDoom n t (l.map (algebraMap F K))) :
    (univ.filter fun c : F => ¬ mlDoom n t ((l ++ [c]).map (algebraMap F K))).card ≤
      if l.length < n then 1 else 0 := by
  classical
  have h := mlDoom_step ht _ hd
  rw [List.length_map] at h
  refine le_trans ?_ h
  rw [← card_map ⟨algebraMap F K, (algebraMap F K).injective⟩]
  refine card_le_card fun c hc => ?_
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hc ⊢
  obtain ⟨c', hc', rfl⟩ := hc
  simpa using hc'

/-- `¬ mlDoom` at nine F coordinates: the table's extension at them vanishes. -/
theorem not_mlDoom_nine {t : Array K} (ht : t.size = 2 ^ 9) (l : List K) (hl : 9 ≤ l.length) :
    ¬ mlDoom 9 t l ↔ ∑ q : Fin (2 ^ 9), eqBits (fun v => l.getD v 0) 9 q * tbl 9 t q = 0 := by
  have hk : (l.take 9).length = 9 := by simp; omega
  have key : tbl 0 (bindL t (l.take 9)) 0 =
      ∑ q : Fin (2 ^ 9), eqBits (fun v => l.getD v 0) 9 q * tbl 9 t q := by
    rw [bindL_mle _ _ (by rw [ht, hk]), ← mleEval_eq, mleEval_eq' t _ hk, mle]
    refine sum_congr rfl fun u _ => ?_
    rw [eqBits_eq_eq]
    congr 2
    funext v
    simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_take, v.2, ite_true]
  rw [mlDoom, hk, Nat.sub_self, not_not, ← key]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    funext u
    obtain ⟨u, hu⟩ := u
    obtain rfl : u = 0 := by simp at hu; omega
    exact h

end FR.Snd
