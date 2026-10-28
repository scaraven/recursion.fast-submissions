-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `rsWeight` claim 2's kind factor at the
-- 4.1 node layouts; stage S-T2).
import FRKindWeight
import FRNodeKinds4

/-!
# Claim 2's kind factor at the revision 4.1 node layouts (`kf4`), fast

3.x's `KW.kwS` weights claim 2 by 3.x's node layout (`Layout.nodeLayout`, 16 block bits). A 4.1
node `ν` (`N2`/`N4`/`N8`) has its own layout `N4c.nodeLayout4 ν` (17 or 18 block bits) and its
kind factor `N4c.kf4 ν β t = Σ_{i<8} β^i [nodeKinds_i = nodeBK4 ν t]` (the factor P4b's `KfInd`
batches).

* **Specification** `kwS4 ν n β q ρ = Σ_{t < 2^n} kf4 ν β t · eq(q, t) · eq(ρ, t)`.
* **The endpoint form** (`kf4_ends`): on `[0, 2^n)`, `kf4 ν β t = Σ_{(i, x) ∈ ends4} β^i [t < x]`,
  where `ends4` lists each layout interval's two ends with its kind's exponent, and the `free` tail
  `[blocks, 2^n)` (characteristic two: an interval is `[t < hi] + [t < lo]`). The proof reads the
  tiling certificate `layout_contig` (`contig_sum`: at most one interval holds a block).
* **The fast form** (`kwS4_eq`, `kwS4_fast`): each `[0, x)` is a union of dyadic blocks
  (`KW.psum_cubes`); the blocks of all endpoints, merged per level (`grpL`), are the skeleton
  `skel4 ν n`. A stage is one Horner sum over the levels (`kwKS`); with the claim point in `F`,
  each block's factor is an `F` part times a `K` part (`KW.mkEnt`), as S-T1's `KW.kwS_fast`.
* Controls: `kwS4_cube`, `kwS4_hashA` (+), `kwS4_ne_3x` (−: 3.x's factor at 18 bits differs),
  `skel4_levels`.
-/

namespace FR
namespace KW4
open Finset RecursionFast Rev4 KW

/-! ## Specification -/

/-- A block kind's exponent in the kind factor (its index in `nodeKinds`; `N4c.kf4_eq`). -/
def ex (b : BlockKind) : ℕ := (N4c.bkIdx4 b).val - 1

/-- **Claim 2's kind-weighted block weight at a 4.1 node** (one Frobenius stage):
`Σ_{t < 2^n} kf4 ν β t · eq(q, t) · eq(ρ, t)` over `n` block coordinates. -/
def kwS4 (ν : NodeKind) (n : ℕ) (β : F) (q ρ : Fin n → K) : K :=
  ∑ t : Fin (2 ^ n), K.ofF (N4c.kf4 ν β t) * eq q (cube t) * eq ρ (cube t)

/-! ## Implementation data: endpoints, blocks, the skeleton -/

/-- The layout's endpoints `(exponent, x)`: both ends of each interval, and the `free` tail
`[blocks, 2^n)`. -/
def ends4 (ν : NodeKind) (n : ℕ) : List (ℕ × ℕ) :=
  (N4c.nodeLayout4 ν).flatMap (fun iv => [(ex iv.kind, iv.hi), (ex iv.kind, iv.lo)]) ++
    [(ex .free, 2 ^ n), (ex .free, ν.blocks)]

/-- Every endpoint's dyadic blocks `(exponent, level, high part)`. -/
def allKeys4 (ν : NodeKind) (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (ends4 ν n).flatMap fun p => (cubesOf n p.2).map fun c => (p.1, c.1, c.2)

/-- A block of level `j`, as `(u, [exponent])`. -/
def selL (j : ℕ) (p : ℕ × ℕ × ℕ) : Option (ℕ × List ℕ) :=
  if p.2.1 = j then some (p.2.2, [p.1]) else none

/-- Level `j`'s blocks of `L`, merged by key: `(u, exponents)`. -/
def grpL (L : List (ℕ × ℕ × ℕ)) (j : ℕ) : List (ℕ × List ℕ) :=
  mergeAdj ((L.filterMap (selL j)).mergeSort fun a b => decide (a.1 ≤ b.1))

/-- **The 4.1 layout's merged blocks**, levels `0 … n`, as fixed-bit lists with exponents. -/
def skel4 (ν : NodeKind) (n : ℕ) : List (List (List (ℕ × Bool) × List ℕ)) :=
  (List.range (n + 1)).map fun j => (grpL (allKeys4 ν n) j).map fun p => (fixB n j p.1, p.2)

/-- A skeleton's stage value in `K`: `Σ_j (Π_{l<j} s_l) Σ_{blocks} (Σ_i β^i) Π_{fixed} e_l(b)`. -/
def kwKS (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (e : ℕ → Bool → K) (s : ℕ → K) :
    K :=
  hornerK s 0 (sk.map fun g => (g.map fun p =>
    K.ofF ((p.2.map (β ^ ·)).sum) * (p.1.map fun b => e b.1 b.2).prod).sum)

/-! ## The endpoint form -/

theorem ofF_one' : K.ofF 1 = 1 := map_one K.ofFRingHom
theorem ofF_zero' : K.ofF 0 = 0 := map_zero K.ofFRingHom
theorem ofF_mul4 (a b : F) : K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom a b

/-- Over a tiling list, a block's interval sum is the value at its interval (`ivAt`). -/
theorem contig_sum {M : Type*} [AddCommMonoid M] (f : N4c.TIv → M) :
    ∀ {ivs : List N4c.TIv} {a b : ℕ}, N4c.contig ivs a b = true → ∀ t,
      (ivs.map fun iv => if iv.mem t then f iv else 0).sum = ((N4c.ivAt ivs t).map f).getD 0
  | [], _, _, _, t => by simp [N4c.ivAt]
  | iv :: ivs, a, b, h, t => by
    simp only [N4c.contig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, -⟩, h⟩ := h
    simp only [N4c.ivAt, List.find?_cons, List.map_cons, List.sum_cons]
    by_cases hm : iv.mem t = true
    · simp only [hm, if_true, Option.map_some, Option.getD_some]
      rw [List.sum_eq_zero fun x hx => ?_, add_zero]
      obtain ⟨iv', hiv', rfl⟩ := List.mem_map.1 hx
      have := ((N4c.contig_bounds h).2 iv' hiv').1
      simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hm
      rw [if_neg (by simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, if_false, zero_add]
      exact contig_sum f h t

/-- **The kind factor by endpoints** (characteristic two): on `[0, 2^n)`,
`kf4 ν β t = Σ_{(i, x) ∈ ends4} β^i [t < x]`. -/
theorem kf4_ends (ν : NodeKind) (n : ℕ) (β : F) {t : ℕ} (ht : t < 2 ^ n) :
    N4c.kf4 ν β t = ((ends4 ν n).map fun p => β ^ p.1 * (if t < p.2 then 1 else 0)).sum := by
  have hiv : ∀ iv ∈ N4c.nodeLayout4 ν, (([(ex iv.kind, iv.hi), (ex iv.kind, iv.lo)].map
      fun p => β ^ p.1 * (if t < p.2 then (1 : F) else 0)).sum) =
        if iv.mem t then β ^ ex iv.kind else 0 := by
    intro iv hiv
    have := (N4c.layout_bounds ν hiv).1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, N4c.TIv.mem,
      Bool.and_eq_true, decide_eq_true_eq]
    by_cases h1 : t < iv.lo
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega), mul_one, CharTwo.add_self_eq_zero]
    · by_cases h2 : t < iv.hi
      · rw [if_pos h2, if_neg h1, if_pos ⟨by omega, h2⟩]; simp
      · rw [if_neg h2, if_neg h1, if_neg (by omega)]; simp
  rw [ends4, List.map_append, List.sum_append, sum_flatMap, List.map_congr_left hiv,
    contig_sum (fun iv => β ^ ex iv.kind) (N4c.layout_contig ν) t, N4c.kf4_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, if_pos ht,
    mul_one]
  rcases e : N4c.ivAt (N4c.nodeLayout4 ν) t with _ | iv
  · have hb : ν.blocks ≤ t := by
      by_contra hlt
      obtain ⟨iv, -, -, hf, -⟩ := N4c.layout_at ν (lt_of_not_ge hlt)
      rw [hf] at e; cases e
    have hk : N4c.nodeBK4 ν t = .free := by simp [N4c.nodeBK4, e]
    rw [hk, if_neg (by omega)]
    simp [ex]
  · have hm := List.mem_of_find?_eq_some e
    have hk' : iv.mem t = true := by simpa using List.find?_some e
    have hb : t < ν.blocks := by
      have := (N4c.layout_bounds ν hm).2
      simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk'; omega
    have hk : N4c.nodeBK4 ν t = iv.kind := by simp [N4c.nodeBK4, e]
    rw [hk, if_pos hb, mul_one, CharTwo.add_self_eq_zero, add_zero]
    rfl

/-- The spec as a sum of `β^i`-weighted prefix sums over the endpoints. -/
theorem kwS4_ends (ν : NodeKind) (n : ℕ) (β : F) (qf ρf : ℕ → K) :
    kwS4 ν n β (fun l : Fin n => qf l) (fun l : Fin n => ρf l) =
      ((ends4 ν n).map fun p => K.ofF (β ^ p.1) * psum (ew qf ρf) n p.2).sum := by
  have hk : ∀ t ∈ range (2 ^ n), K.ofF (N4c.kf4 ν β t) * prodE (ew qf ρf) n t =
      ((ends4 ν n).map fun p => K.ofF (β ^ p.1) *
        (if t < p.2 then prodE (ew qf ρf) n t else 0)).sum := by
    intro t ht
    rw [kf4_ends ν n β (mem_range.1 ht), ofF_lsum, List.map_map, ← List.sum_map_mul_right]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply, ofF_mul4]
    split_ifs <;> simp [ofF_one', ofF_zero']
  rw [kwS4]
  simp only [mul_assoc, eq_mul_eq]
  rw [Fin.sum_univ_eq_sum_range (fun t => K.ofF (N4c.kf4 ν β t) * prodE (ew qf ρf) n t) (2 ^ n),
    sum_congr rfl hk, sum_lsum]
  exact congrArg _ (List.map_congr_left fun p _ => by rw [psum, mul_sum])

/-- … and as a sum over all endpoints' dyadic blocks. -/
theorem kwS4_keys (ν : NodeKind) (n : ℕ) (β : F) (qf ρf : ℕ → K) :
    kwS4 ν n β (fun l : Fin n => qf l) (fun l : Fin n => ρf l) =
      ((allKeys4 ν n).map fun p => K.ofF (β ^ p.1) * cubeW (ew qf ρf) n p.2.1 p.2.2).sum := by
  rw [kwS4_ends, allKeys4, sum_flatMap]
  refine congrArg _ (List.map_congr_left fun p _ => ?_)
  rw [psum_cubes, List.map_map, ← List.sum_map_mul_left]
  rfl

theorem allKeys4_lvl {ν : NodeKind} {n : ℕ} {p : ℕ × ℕ × ℕ} (h : p ∈ allKeys4 ν n) :
    p.2.1 < n + 1 := by
  simp only [allKeys4, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, -, c, hc, rfl⟩ := h
  have := cubesOf_le hc
  simp only; omega

/-- **Blocks regrouped by level and merged by key.** -/
theorem grpL_sum {R : Type*} [CommRing R] (w : ℕ → R) (V : ℕ → ℕ → R) (L : List (ℕ × ℕ × ℕ))
    (N : ℕ) (hL : ∀ p ∈ L, p.2.1 < N) :
    (L.map fun p => w p.1 * V p.2.1 p.2.2).sum =
      ∑ j ∈ range N, ((grpL L j).map fun p => (p.2.map w).sum * V j p.1).sum := by
  have hj : ∀ j, ((grpL L j).map fun p => (p.2.map w).sum * V j p.1).sum =
      (L.map fun p => (selL j p).elim 0 fun q => (q.2.map w).sum * V j q.1).sum := fun j => by
    rw [grpL, mergeAdj_sum w (V j), ((List.mergeSort_perm _ _).map _).sum_eq, sum_filterMap]
  simp only [hj, sum_lsum]
  refine congrArg _ (List.map_congr_left fun p hp => ?_)
  rw [sum_eq_single p.2.1]
  · simp [selL]
  · intro j _ hj; simp [selL, Ne.symm hj]
  · intro h; exact absurd (mem_range.2 (hL p hp)) h

/-- **The spec is the skeleton's stage value** (any claim point; `s_l = e_l(0) + e_l(1)`). -/
theorem kwS4_eq (ν : NodeKind) (n : ℕ) (β : F) (qf ρf : ℕ → K) (s : ℕ → K)
    (hs : ∀ l < n, s l = ew qf ρf l false + ew qf ρf l true) :
    kwS4 ν n β (fun l : Fin n => qf l) (fun l : Fin n => ρf l) = kwKS (skel4 ν n) β (ew qf ρf) s := by
  rw [kwS4_keys, grpL_sum (fun i => K.ofF (β ^ i)) (fun j u => cubeW (ew qf ρf) n j u) _ (n + 1)
    (fun p hp => allKeys4_lvl hp), kwKS, hornerK_eq, skel4, List.map_map, List.length_map,
    List.length_range]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.1 hj
  rw [getD_range_map _ _ hj]
  simp only [Function.comp_apply, List.map_map]
  rw [← List.sum_map_mul_left]
  refine congrArg _ (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp_apply, cubeW, min_eq_left (show j ≤ n by omega), ofF_lsum, List.map_map]
  rw [prod_congr rfl fun l hl => (hs l (by have := mem_range.1 hl; omega)).symm]
  simp only [zero_add, Function.comp_def, ofF_pow]
  ring

/-- **One stage, fast** (the claim point's block coordinates in `F`): `KW.mkEnt`'s split blocks
and one Horner sum (`s_l = 1 + q_l + ρ_l`). -/
theorem kwS4_fast (ν : NodeKind) (n : ℕ) (β : F) (qF : ℕ → F) (ρf : ℕ → K) (s : ℕ → K)
    (hs : ∀ l < n, s l = K.ofF (qF l) + (1 + ρf l)) :
    kwS4 ν n β (fun l : Fin n => K.ofF (qF l)) (fun l : Fin n => ρf l) =
      hornerK s 0 ((skel4 ν n).map fun g => gsum (mkEnt (β ^ ·)
        (fun l b => if b then qF l else 1 - qF l) (fun l b => if b then ρf l else 1 - ρf l) g)) := by
  have h2 := CharTwo.two_eq_zero (R := K)
  refine (kwS4_eq ν n β (fun l => K.ofF (qF l)) ρf s fun l hl => ?_).trans ?_
  · rw [hs l hl]
    simp only [ew, if_true, Bool.false_eq_true, if_false]
    linear_combination (K.ofF (qF l) + ρf l - K.ofF (qF l) * ρf l) * h2
  rw [kwKS]
  congr 1
  refine List.map_congr_left fun g _ => ?_
  rw [gsum_mkEnt]
  refine congrArg _ (List.map_congr_left fun p _ => ?_)
  rw [prod_fix_ofF]

/-! ## Controls -/

/-- (+) At a Boolean point the weight is the block's kind factor. -/
theorem kwS4_cube (ν : NodeKind) (n : ℕ) (β : F) (t₀ : Fin (2 ^ n)) :
    kwS4 ν n β (cube t₀) (cube t₀) = K.ofF (N4c.kf4 ν β t₀) := by
  rw [kwS4, sum_eq_single t₀]
  · simp [eq_cube_cube]
  · intro t _ ht; simp [eq_cube_cube, Ne.symm ht]
  · simp

/-- `N4`'s first aggregate's `c_A` block (`hashA`). -/
def tA4 : Fin (2 ^ 18) := ⟨N4c.cAB .N4 0, by decide⟩

/-- (+) **The factor at the `c_A` block is `β^3`** (`hashA`), at 18 block bits. -/
theorem kwS4_hashA (β : F) : kwS4 .N4 18 β (cube tA4) (cube tA4) = K.ofF (β ^ 3) := by
  rw [kwS4_cube]; exact congrArg K.ofF (N4c.kf4_chainLk_ctrl β).2.1

/-- A block of `N4`'s second main chain (`stream`, exponent 0), past 3.x's `wmBase` (3.x: `free`). -/
def tS4 : Fin (2 ^ 18) := ⟨50000, by decide⟩

theorem selOf_tS4 : ∀ i < 8, (selOf (ivsQ 18 (nodeKinds.getD i .free)) tS4 : ℤ) =
    if i = 7 then 1 else 0 := by decide +kernel

/-- (−) **3.x's kind factor is not the 4.1 one**: at `β = 0` and block `50000` of `N4`, the 4.1
weight is `1` (`stream`), 3.x's weight at 18 bits (`KW.kwS`, the stand-in) is `0` (`free`). -/
theorem kwS4_ne_3x : kwS4 .N4 18 0 (cube tS4) (cube tS4) ≠ kwS 18 0 (cube tS4) (cube tS4) := by
  have h4 : kwS4 .N4 18 0 (cube tS4) (cube tS4) = 1 := by
    rw [kwS4_cube, N4c.kf4_eq, show N4c.nodeBK4 .N4 tS4 = .stream by decide]
    simp [N4c.bkIdx4, ofF_one']
  have h3 : kwS 18 0 (cube tS4) (cube tS4) = 0 := by
    rw [kwS_cube, sum_eq_single 7]
    · rw [selOf_cast, selOf_tS4 7 (by norm_num), if_pos rfl]; simp
    · intro i hi h7
      rw [selOf_cast, selOf_tS4 i (mem_range.1 hi), if_neg h7, Int.cast_zero, mul_zero]
    · simp
  rw [h4, h3]
  exact one_ne_zero

/-- (+) The skeleton has one level per block bit and the full cube (`n + 1`). -/
theorem skel4_levels (ν : NodeKind) (n : ℕ) : (skel4 ν n).length = n + 1 := by
  simp [skel4]

end KW4
end FR
