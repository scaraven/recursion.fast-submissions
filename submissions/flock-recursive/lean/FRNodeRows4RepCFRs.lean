-- G6: this module also holds the former modules `FRKindWeight4`, `FRVIRTplChain`, `FRVerifierImplOps4`, `FRNodeRows4RepRsV`, `FRNodeRows4RepRs`, `FRVIRTplCF` (one section each, in import order).
import FRVerifierImplOps
import FRNodeKinds4
import FRVIRTplLag
import FRVIRTplEval

section G6_FRKindWeight4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `rsWeight` claim 2's kind factor at the
-- 4.1 node layouts; stage S-T2).

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

end G6_FRKindWeight4

section G6_FRVIRTplChain

-- New for `flock-recursive` (R-OPS §5.2, stage R3: the chain template library).

/-!
# Chain templates: a gadget builder with value lemmas

Replay templates (`Tpl`) are gate lists with locals numbered in gate order. Writing one by hand means
tracking every stage's first local (`FRVIRTplRepLW`'s `lwK8 … lwK13`). This module gives a builder
that tracks the locals itself, and Hoare-style value lemmas that compose without offset arithmetic.

* **`GM α`**: from a first local `k`, a gate list and a result (forms over the template's wires).
  `ret`, `bind` (the second part's locals follow the first's), `gate`.
* **`GM.Ok e g P`**: wherever the gate equations of `g` hold at `e` (from any first local), its
  result satisfies `P`. `ok_ret`, `ok_bind`, `ok_mono`; `ok_mapL`, `ok_foldL`, `ok_iterL` for the
  list combinators `mapL` (independent instances), `foldL` (a chain through a list), `iterL` (a
  chain of `n` steps returning every value).
* **Gadgets on `F`** (one gate each): `mulF`; on **`K`** as a pair of `F` forms (`KF`, value `evK`):
  `mulK` (Karatsuba, `mulKG`), `sqK` (two gates), `smulK` (an `F` form times a `K` pair, two
  gates), and the linear ones `oneK`, `zeroK`, `addK`, `sumK`, `ofFK`, `oneSubK` (no gates).
* **The chains** (R-OPS §5.2's shapes): `sqChainF`/`sqChainK` (`x^(2^i)`, `i ≤ n`; `sqIter`),
  `powF` (`x^i`, `i ≤ n`), `prodK` (a product chain), `hornerKG` (`KW.hornerK`), `phiG`
  (`phiTable`'s tree).

Every lemma is generic in the template's wires: the gadgets are reusable by any replay template.
-/

namespace FR
namespace Tpl
open Circ

/-- **A gadget builder**: from its first local, its gates and its result. -/
abbrev GM (α : Type) := ℕ → List Gate × α

namespace GM

variable {α β γ : Type} {e : Env}

/-- No gates. -/
def ret (a : α) : GM α := fun _ => ([], a)

/-- `g`, then `f` of its result, whose locals follow `g`'s. -/
def bind (g : GM α) (f : α → GM β) : GM β := fun k =>
  ((g k).1 ++ (f (g k).2 (k + nlocs (g k).1)).1, (f (g k).2 (k + nlocs (g k).1)).2)

/-- `g`, its result mapped (no gates; no copy of `g`'s gates). -/
def map (g : GM α) (h : α → β) : GM β := fun k => ((g k).1, h (g k).2)

/-- One gate, its result read from its first local. -/
def gate (g : Gate) (out : ℕ → α) : GM α := fun k => ([g], out k)

/-- **`g` computes `P`**: wherever its gate equations hold at `e`, its result satisfies `P`. -/
def Ok (e : Env) (g : GM α) (P : α → Prop) : Prop := ∀ k, Eqns e (g k).1 k → P (g k).2

theorem ok_ret {P : α → Prop} {a : α} (h : P a) : Ok e (ret a) P := fun _ _ => h

theorem ok_bind {g : GM α} {f : α → GM β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hf : ∀ a, P a → Ok e (f a) Q) : Ok e (g.bind f) Q := fun k h => by
  have h' := Eqns.append.1 h
  exact hf _ (hg k h'.1) _ h'.2

theorem ok_map {g : GM α} {h : α → β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hh : ∀ a, P a → Q (h a)) : Ok e (g.map h) Q := fun k hk => hh _ (hg k hk)

theorem ok_mono {g : GM α} {P Q : α → Prop} (hg : Ok e g P) (h : ∀ a, P a → Q a) : Ok e g Q :=
  fun k hk => h _ (hg k hk)

/-! ## List combinators -/

/-- Independent instances, one per element. -/
def mapL (f : α → GM β) : List α → GM (List β)
  | [] => ret []
  | a :: as => (f a).bind fun b => (mapL f as).map fun bs => b :: bs

theorem ok_mapL {f : α → GM β} {E : β → γ} {v : α → γ} :
    ∀ l : List α, (∀ a ∈ l, Ok e (f a) fun b => E b = v a) → Ok e (mapL f l) fun bs => bs.map E = l.map v
  | [], _ => ok_ret rfl
  | a :: as, h =>
    ok_bind (h a (List.mem_cons_self ..)) fun b hb =>
      ok_map (ok_mapL as fun x hx => h x (List.mem_cons_of_mem _ hx)) fun bs hbs => by
        simp [hb, hbs]

/-- **A chain through a list**: `b ↦ f b a` for each element in turn. -/
def foldL (f : β → α → GM β) : β → List α → GM β
  | b, [] => ret b
  | b, a :: as => (f b a).bind fun b' => foldL f b' as

theorem ok_foldL {f : β → α → GM β} {E : β → γ} {g : γ → α → γ} :
    ∀ (l : List α) (b : β), (∀ b a, a ∈ l → Ok e (f b a) fun b' => E b' = g (E b) a) →
      Ok e (foldL f b l) fun b' => E b' = l.foldl g (E b)
  | [], _, _ => ok_ret rfl
  | a :: as, b, h =>
    ok_bind (h b a (List.mem_cons_self ..)) fun b' hb' =>
      ok_mono (ok_foldL as b' fun c x hx => h c x (List.mem_cons_of_mem _ hx)) fun r hr => by
        rw [hr, hb', List.foldl_cons]

/-- **A chain of `n` steps**, every value: `[b, f b, f (f b), …]` (`n + 1` entries). -/
def iterL (f : β → GM β) : ℕ → β → GM (List β)
  | 0, b => ret [b]
  | n + 1, b => (f b).bind fun b' => (iterL f n b').map fun bs => b :: bs

theorem ok_iterL {f : β → GM β} {E : β → γ} {g : γ → γ} (hf : ∀ b, Ok e (f b) fun b' => E b' = g (E b)) :
    ∀ (n : ℕ) (b : β), Ok e (iterL f n b) fun bs => bs.map E = (List.range (n + 1)).map fun i => g^[i] (E b)
  | 0, _ => ok_ret rfl
  | n + 1, b =>
    ok_bind (hf b) fun b' hb' => ok_map (ok_iterL hf n b') fun bs hbs => (by
      rw [List.map_cons, hbs, List.range_succ_eq_map (n := n + 1), List.map_cons, List.map_map]
      simp only [Function.comp_def, Function.iterate_succ_apply, hb', Function.iterate_zero_apply])

theorem iterL_length {f : β → GM β} : ∀ (n : ℕ) (b : β) (k : ℕ), ((iterL f n b) k).2.length = n + 1
  | 0, _, _ => rfl
  | n + 1, b, k => by
    simp only [iterL, bind, map, List.length_cons, iterL_length n]

end GM

open GM

variable {e : Env}

/-! ## Gadgets -/

/-- A `K` value as its two `F` forms. -/
abbrev KF := LinT × LinT

/-- An `F` product (one gate). -/
def mulF (a b : LinT) : GM LinT := gate (.mul a b) L

theorem ok_mulF (a b : LinT) : Ok e (mulF a b) fun o => o.ev e = a.ev e * b.ev e := fun k h => by
  have := (Eqns.cons.1 h).1
  simpa [mulF, gate, Gate.Eqn] using this

/-- A `K` product (Karatsuba, three gates: `mulKG`). -/
def mulK (a b : KF) : GM KF := mulKG a b

theorem ok_mulK (a b : KF) : Ok e (mulK a b) fun o => evK e o = evK e a * evK e b :=
  fun k h => mulKG_ev a b k h

/-- **A `K` square** (two gates): `(a₀² + α a₁², a₁²)`. -/
def sqK (a : KF) : GM KF := fun k =>
  ([.mul a.1 a.1, .mul a.2 a.2], (L k ++ sc F.alpha (L (k + 1)), L (k + 1)))

theorem ok_sqK (a : KF) : Ok e (sqK a) fun o => evK e o = evK e a * evK e a := fun k h => by
  simp only [sqK, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
  obtain ⟨h0, h1⟩ := h
  apply K_ext'
  · rw [K_mul_f₀]; simp only [evK, sqK, ev_append, ev_sc, ev_L, h0, h1]
  · rw [K_mul_f₁]; simp only [evK, sqK, ev_L, h1]
    linear_combination (-(a.1.ev e * a.1.ev e) - a.1.ev e * a.2.ev e) * CharTwo.two_eq_zero (R := F)

/-- **An `F` form times a `K` pair** (two gates). -/
def smulK (c : LinT) (a : KF) : GM KF := fun k => ([.mul c a.1, .mul c a.2], (L k, L (k + 1)))

theorem ok_smulK (c : LinT) (a : KF) : Ok e (smulK c a) fun o => evK e o = K.ofF (c.ev e) * evK e a :=
  fun k h => by
    simp only [smulK, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
    obtain ⟨h0, h1⟩ := h
    rw [← K.smulF_eq_mul]
    exact K_ext' (by simp only [evK, smulK, ev_L, h0]; rfl) (by simp only [evK, smulK, ev_L, h1]; rfl)

/-- `1`, `0`, `a + b`, a sum, an `F` form in `K`, `1 − a` (linear: no gates). -/
def oneK : KF := (C 1, [])
def zeroK : KF := ([], [])
def addK (a b : KF) : KF := (a.1 ++ b.1, a.2 ++ b.2)
def sumK (l : List KF) : KF := (l.flatMap (·.1), l.flatMap (·.2))
def ofFK (c : LinT) : KF := (c, [])
def oneSubK (a : KF) : KF := (C 1 ++ a.1, a.2)

theorem evK_oneK (h1 : e.one = 1) : evK e oneK = 1 := by
  apply K_ext' <;> simp [evK, oneK, h1] <;> rfl
theorem evK_zeroK : evK e zeroK = 0 := rfl
theorem evK_addK (a b : KF) : evK e (addK a b) = evK e a + evK e b :=
  K_ext' (by simp only [evK, addK, ev_append, K_add_f₀]) (by simp only [evK, addK, ev_append, K_add_f₁])
theorem evK_sumK : ∀ l : List KF, evK e (sumK l) = (l.map (evK e)).sum
  | [] => rfl
  | a :: l => by
    have ih := evK_sumK l
    simp only [sumK, List.flatMap_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    exact K_ext' (by simp only [evK, ev_append, K_add_f₀]) (by simp only [evK, ev_append, K_add_f₁])
theorem evK_ofFK (c : LinT) : evK e (ofFK c) = K.ofF (c.ev e) := rfl
theorem evK_oneSubK (h1 : e.one = 1) (a : KF) : evK e (oneSubK a) = 1 - evK e a :=
  K_ext' (by simp only [evK, oneSubK, ev_append, ev_C, h1, mul_one, K_one_sub_f₀])
    (by simp only [evK, oneSubK, K_one_sub_f₁, zero_add])

/-! ## Chains -/

theorem iterate_sq {R : Type*} [CommRing R] : ∀ (i : ℕ) (x : R), (fun y => y * y)^[i] x = sqIter i x
  | 0, _ => rfl
  | i + 1, x => by rw [Function.iterate_succ_apply, iterate_sq i, sqIter]

/-- **The squaring chain in `F`**: `x^(2^i)` for `i ≤ n`. -/
def sqChainF (n : ℕ) (x : LinT) : GM (List LinT) := iterL (fun y => mulF y y) n x

theorem ok_sqChainF (n : ℕ) (x : LinT) :
    Ok e (sqChainF n x) fun ys => ys.map (LinT.ev e) = (List.range (n + 1)).map fun i => sqIter i (x.ev e) :=
  ok_mono (ok_iterL (g := fun y => y * y) (fun y => ok_mulF y y) n x) fun ys h => by
    rw [h]; exact List.map_congr_left fun i _ => iterate_sq i _

/-- **The squaring chain in `K`**: `x^(2^i)` for `i ≤ n` (two gates per step). -/
def sqChainK (n : ℕ) (x : KF) : GM (List KF) := iterL sqK n x

theorem ok_sqChainK (n : ℕ) (x : KF) :
    Ok e (sqChainK n x) fun ys => ys.map (evK e) = (List.range (n + 1)).map fun i => sqIter i (evK e x) :=
  ok_mono (ok_iterL (g := fun y => y * y) ok_sqK n x) fun ys h => by
    rw [h]; exact List.map_congr_left fun i _ => iterate_sq i _

theorem iterate_mul {R : Type*} [CommMonoid R] (i : ℕ) (x : R) : (fun y => y * x)^[i] 1 = x ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ]

/-- **The powers** `x^i`, `i ≤ n` (one gate per step). -/
def powF (n : ℕ) (x : LinT) : GM (List LinT) := iterL (fun y => mulF y x) n (C 1)

theorem ok_powF (h1 : e.one = 1) (n : ℕ) (x : LinT) :
    Ok e (powF n x) fun ys => ys.map (LinT.ev e) = (List.range (n + 1)).map fun i => x.ev e ^ i :=
  ok_mono (ok_iterL (g := fun y => y * x.ev e) (fun y => ok_mulF y x) n (C 1)) fun ys h => by
    rw [h]
    refine List.map_congr_left fun i _ => ?_
    rw [ev_C, h1, mul_one]
    exact iterate_mul i _

theorem foldl_mul_map {R : Type*} [CommMonoid R] {α : Type*} (g : α → R) :
    ∀ (l : List α) (c : R), l.foldl (fun y x => y * g x) c = c * (l.map g).prod
  | [], c => by simp
  | x :: l, c => by rw [List.foldl_cons, foldl_mul_map g l, List.map_cons, List.prod_cons, mul_assoc]

/-- **A product chain in `K`**: `Π l` (`|l| − 1` products; `1` for the empty list). -/
def prodK : List KF → GM KF
  | [] => ret oneK
  | a :: as => foldL mulK a as

theorem ok_prodK (h1 : e.one = 1) : ∀ l : List KF, Ok e (prodK l) fun o => evK e o = (l.map (evK e)).prod
  | [] => ok_ret (evK_oneK h1)
  | a :: as => ok_mono (ok_foldL (g := fun y x => y * evK e x) as a fun b x _ => ok_mulK b x) fun o h => by
      rw [h, List.map_cons, List.prod_cons, foldl_mul_map]

/-- **Horner in `K`**: `Σ_j (Π_{l<j} s (o + l)) y_j` (`KW.hornerK`), one product per entry. -/
def hornerKG (s : ℕ → KF) : ℕ → List KF → GM KF
  | _, [] => ret zeroK
  | o, y :: ys => (hornerKG s (o + 1) ys).bind fun h => (mulK (s o) h).map (addK y)

theorem ok_hornerKG (s : ℕ → KF) : ∀ (o : ℕ) (ys : List KF),
    Ok e (hornerKG s o ys) fun h => evK e h = KW.hornerK (fun l => evK e (s l)) o (ys.map (evK e))
  | _, [] => ok_ret rfl
  | o, y :: ys =>
    ok_bind (ok_hornerKG s (o + 1) ys) fun h hh => ok_map (ok_mulK (s o) h) fun m hm => by
      rw [evK_addK, hm, hh, List.map_cons, KW.hornerK]

/-- **`phiTable`'s tree** over `F` forms: the later stages' table `t`, then `t_e · f^(2^e)`. -/
def phiG : List LinT → GM (List LinT)
  | [] => ret [C 1]
  | f :: fs => (phiG fs).bind fun t => (sqChainF (t.length - 1) f).bind fun pw =>
      (mapL (fun p : LinT × LinT => mulF p.1 p.2) (t.zip pw)).map fun m => t ++ m

theorem phiTable_cons_toList {R : Type*} [CommRing R] (f : R) (fs : List R) :
    (phiTable (f :: fs)).toList = (phiTable fs).toList ++
      ((List.range (phiTable fs).size).map fun i => (phiTable fs).toList.getD i 0 * sqIter i f) := by
  rw [phiTable, Array.toList_append, Array.toList_ofFn]
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  simp

/-- **`phiG` computes `phiTable`.** -/
theorem ok_phiG (h1 : e.one = 1) : ∀ fs : List LinT,
    Ok e (phiG fs) fun t => t.map (LinT.ev e) = (phiTable (fs.map (LinT.ev e))).toList
  | [] => ok_ret (by simp [phiTable, ev_C, h1])
  | f :: fs => ok_bind (ok_phiG h1 fs) fun t ht => ok_bind (ok_sqChainF _ f) fun pw hpw =>
      ok_map (ok_mapL (E := LinT.ev e) (v := fun p : LinT × LinT => p.1.ev e * p.2.ev e) _
        fun p _ => ok_mulF p.1 p.2) fun m hm => (by
      have hl : t.length = (phiTable (fs.map (LinT.ev e))).size := by
        simpa using congrArg List.length ht
      have hpos : 0 < t.length := by rw [hl, phiTable_size]; exact Nat.two_pow_pos _
      rw [List.map_append, hm, ht, List.map_cons, phiTable_cons_toList, ← hl]
      congr 1
      have hpl : pw.length = t.length := by
        have := congrArg List.length hpw; simp at this; omega
      refine List.ext_getElem (by simp [hpl]) fun i h1' h2' => ?_
      simp only [List.length_map, List.length_zip, hpl, min_self] at h1'
      have hpi : (pw.map (LinT.ev e))[i]'(by simp [hpl, h1']) = sqIter i (f.ev e) := by
        rw [List.getElem_of_eq hpw]; simp
      simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
      rw [← ht, List.getD_eq_getElem _ _ (by simpa using h1'), List.getElem_map]
      simp only [List.getElem_map] at hpi
      rw [hpi])

end Tpl
end FR

end G6_FRVIRTplChain

section G6_FRVerifierImplOps4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `rsWeight` at the 4.1 node layouts;
-- stage S-T2).

/-!
# `rsWeight` at a revision 4.1 node (`kf4`), fast

3.x's `rsWeightS` weights claim 2 by 3.x's node layout (`KW.kwS`), and its fast path `wEvalKF` is
built for 3.x's 23 coordinates. A 4.1 node `ν`'s claims have `7 + nbN ν` coordinates (24 for
`N2`, 25 for `N4`/`N8`), and its kind factor is `N4c.kf4 ν` over `nodeLayout4 ν`.

* **Specification** `rsWeightS4 ν`: `rsWeightS` with claim 2's stage weight `kwSL4 ν` (`eq` on the
  7 high coordinates times `KW4.kwS4 ν` on the `|ρ| − 7` block coordinates).
* **Implementation** `rsWeightF4 ν`: a claim point in `F` runs `wEvalKF4` (claim 2: the 4.1
  skeleton `KW4.skel4 ν n`, cached for `n = nbN ν` as `skelN2`/`skelN4`/`skelN8`; per stage one
  `smulF` per block and one Horner sum) or 3.x's `wEvalCF`; otherwise `wEvalKC4` (the same
  skeleton in `K`) or `wEvalC`.
* **`rsWeightF4_meets`**: `rsWeightF4 ν = rsWeightS4 ν` for every input with `|r″| = 7`.
* **`withRS4`/`withRS4_meets`**: an `OpImpl` with `rsWeight := rsWeightF4 ν` meets its spec with
  `rsWeight := rsWeightS4 ν` whenever the base does (the wiring for `implN4`'s `base ν`).
-/

namespace FR
namespace Impl
open Finset RecursionFast Rev4

/-! ## Specification -/

/-- Claim 2's weight at one Frobenius stage at a 4.1 node `ν`: `eq(q_hi, ρ_hi)` on the 7 high
coordinates times `KW4.kwS4 ν` on the `|ρ| − 7` block coordinates. -/
def kwSL4 (ν : NodeKind) (β : F) (q ρ : List K) : K :=
  eqPts (q.take 7) (ρ.take 7) *
    KW4.kwS4 ν (ρ.length - 7) β (ptOf (ρ.length - 7) (q.drop 7)) (ptOf (ρ.length - 7) (ρ.drop 7))

/-- **`rsWeight`'s specification at a 4.1 node `ν`**: `rsWeightS` with claim 2 (index 1) weighted
by `ν`'s kind factor `kf4` at `β^(2^k)`. -/
def rsWeightS4 (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 * ∑ k ∈ range 128,
    K.ofF ((phiTable r.toList).getD k 0) *
      (if p.2 = 1 then kwSL4 ν (sqIter k β) (p.1.toList.map (sqIter k)) ρ.toList
       else eqPts (p.1.toList.map (sqIter k)) ρ.toList)).sum

/-! ## Implementation -/

/-- The skeletons at the node kinds' block bits (closed constants, computed once). -/
def skelN2 : List (List (List (ℕ × Bool) × List ℕ)) := KW4.skel4 .N2 17
def skelN4 : List (List (List (ℕ × Bool) × List ℕ)) := KW4.skel4 .N4 18
def skelN8 : List (List (List (ℕ × Bool) × List ℕ)) := KW4.skel4 .N8 18

/-- `KW4.skel4 ν n`, from the cache at the kind's block bits. -/
def skelAt (ν : NodeKind) (n : ℕ) : List (List (List (ℕ × Bool) × List ℕ)) :=
  match ν with
  | .N2 => if n = 17 then skelN2 else KW4.skel4 .N2 n
  | .N4 => if n = 18 then skelN4 else KW4.skel4 .N4 n
  | .N8 => if n = 18 then skelN8 else KW4.skel4 .N8 n

theorem skelAt_eq (ν : NodeKind) (n : ℕ) : skelAt ν n = KW4.skel4 ν n := by
  cases ν <;> simp only [skelAt] <;> split_ifs with h <;> first | rfl | (subst h; rfl)

/-- One stage of `wEvalKF4`: add `c_k eq(q_hi, ρ_hi) T_k` (`T_k` the Horner sum over the levels),
then square the point and the blocks' `F` factors. -/
def kfStep4 (c : Array K) (ρh : List K) (oρ : Array K) (k : ℕ)
    (st : K × Array F × List (List (F × K))) : K × Array F × List (List (F × K)) :=
  let q := st.2.1
  let s : ℕ → K := fun l => K.ofF (q.getD (7 + l) 0) + oρ.getD l 0
  (st.1 + c.getD k 0 * (eqPtsC ((q.toList.take 7).map K.ofF) ρh *
      KW.hornerK s 0 (st.2.2.map KW.gsum)),
    q.map F.sq, KW.sqG st.2.2)

/-- **Claim 2's stage fold at a 4.1 node, fast** (`wEvalKF4_eq`): the claim point `r` in `F`. -/
def wEvalKF4 (ν : NodeKind) (c : Array K) (β : F) (r : Array F) (ρ : List K) : K :=
  let ρb := (ρ.drop 7).toArray
  let gK : ℕ → Bool → K := fun l b => if b then ρb.getD l 0 else 1 - ρb.getD l 0
  let fF : ℕ → Bool → F := fun l b => if b then r.getD (7 + l) 0 else 1 - r.getD (7 + l) 0
  (Nat.fold c.size (fun k _ => kfStep4 c (ρ.take 7) (ρb.map (1 + ·)) k)
    (0, r, (skelAt ν (ρ.length - 7)).map (KW.mkEnt (β ^ ·) fF gK))).1

/-- Claim 2's stage weight in `K` from the skeleton (any claim point). -/
def kwSL4I (ν : NodeKind) (β : F) (q ρ : List K) : K :=
  let qa := (q.drop 7).toArray
  let ρa := (ρ.drop 7).toArray
  let e := KW.ew (fun l => qa.getD l 0) (fun l => ρa.getD l 0)
  eqPtsC (q.take 7) (ρ.take 7) * KW4.kwKS (skelAt ν (ρ.length - 7)) β e fun l => e l false + e l true

/-- Claim 2's stage sum in `K` (a claim point outside `F`). -/
def wEvalKC4 (ν : NodeKind) (c : Array K) (β : F) (r ρ : List K) : K :=
  ((List.range c.size).map fun k => c.getD k 0 * kwSL4I ν (sqIter k β) (r.map (sqIter k)) ρ).sum

/-- **`rsWeight` at a 4.1 node, fast** (`rsWeightF4_meets`): a claim point in `F` runs `wEvalKF4`
(claim 2) or `wEvalCF`; otherwise `wEvalKC4` or `wEvalC`. -/
def rsWeightF4 (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 *
    (if p.1.all (·.f₁ == 0) then
      (if p.2 = 1 then wEvalKF4 ν c β (p.1.map (·.f₀)) ρ.toList
       else wEvalCF c (p.1.map (·.f₀)) ρ.toList)
     else
      (if p.2 = 1 then wEvalKC4 ν c β p.1.toList ρ.toList else wEvalC c p.1.toList ρ.toList))).sum

/-! ## Proofs -/

/-- The fast fold's invariant (`kf_fold` over any skeleton). -/
theorem kf_fold4 (c : Array K) (ρh : List K) (oρ : Array K) (β : F) (r : Array F)
    (gK : ℕ → Bool → K) (sk : List (List (List (ℕ × Bool) × List ℕ))) : ∀ n,
    Nat.fold n (fun k _ => kfStep4 c ρh oρ k) (0, r, gmK sk β r gK 0) =
    (∑ k ∈ range n, c.getD k 0 * (eqPtsC (((r.map (sqIter k)).toList.take 7).map K.ofF) ρh *
        KW.hornerK (fun l => K.ofF ((r.map (sqIter k)).getD (7 + l) 0) + oρ.getD l 0) 0
            ((gmK sk β r gK k).map KW.gsum)),
      r.map (sqIter n), gmK sk β r gK n)
  | 0 => by simp [sqIter]
  | n + 1 => by
    rw [Nat.fold_succ, kf_fold4 c ρh oρ β r gK sk n, kfStep4]
    simp only [sum_range_succ, sqG_gmK, Array.map_map, Function.comp_def, F.sq_eq_mul,
      ← sqIter_succ']

theorem getD_map_zero {α : Type*} [Zero α] (A : Array α) (f : α → α) (hf : f 0 = 0) (i : ℕ) :
    (A.map f).getD i 0 = f (A.getD i 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[i]? <;> simp [hf]

theorem ptOf_drop (n : ℕ) (L : List K) : ptOf n (L.drop 7) = fun l : Fin n => L.getD (7 + l) 0 := by
  funext l
  simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **`wEvalKF4` meets claim 2's stage sum** at a point in `F` (any sizes). -/
theorem wEvalKF4_eq (ν : NodeKind) (c : Array K) (β : F) (r : Array F) (ρ : List K) :
    wEvalKF4 ν c β r ρ = ∑ k ∈ range c.size,
      c.getD k 0 * kwSL4 ν (sqIter k β) ((r.toList.map K.ofF).map (sqIter k)) ρ := by
  unfold wEvalKF4
  rw [skelAt_eq]
  refine (congrArg Prod.fst (kf_fold4 c (ρ.take 7) ((ρ.drop 7).toArray.map (1 + ·)) β r
    (fun l b => if b then (ρ.drop 7).toArray.getD l 0 else 1 - (ρ.drop 7).toArray.getD l 0)
      (KW4.skel4 ν (ρ.length - 7)) c.size)).trans ?_
  dsimp only
  refine sum_congr rfl fun k _ => congrArg _ ?_
  rw [kwSL4, eqPtsC_eq]
  congr 1
  · simp [Array.toList_map, List.map_take, List.map_map, Function.comp_def, sqIter_ofF]
  · have hq : ptOf (ρ.length - 7) (((r.toList.map K.ofF).map (sqIter k)).drop 7) =
        fun l : Fin (ρ.length - 7) => K.ofF (sqIter k (r.getD (7 + l) 0)) := by
      rw [ptOf_drop]
      funext l
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
        Array.getElem?_toList]
      cases r[7 + l.val]? <;> simp [sqIter_ofF, sqIter_zeroF, KW4.ofF_zero']
    have hρ' : ptOf (ρ.length - 7) (ρ.drop 7) =
        fun l : Fin (ρ.length - 7) => (ρ.drop 7).toArray.getD l 0 := by
      funext l; simp only [ptOf, toArray_getD_list]
    rw [hq, hρ', gmK, List.map_map]
    refine (KW4.kwS4_fast ν _ _ (fun l => sqIter k (r.getD (7 + l) 0)) _ _ fun l hl => ?_).symm
    have hb : ((ρ.drop 7).toArray).size = ρ.length - 7 := by simp
    rw [getD_map_zero _ _ (sqIter_zeroF k), getD_map_lt _ _ _ (by rw [hb]; exact hl)]

theorem kwSL4I_eq (ν : NodeKind) (β : F) (q ρ : List K) : kwSL4I ν β q ρ = kwSL4 ν β q ρ := by
  unfold kwSL4I kwSL4
  dsimp only
  rw [skelAt_eq, eqPtsC_eq]
  congr 1
  have hq : ptOf (ρ.length - 7) (q.drop 7) =
      fun l : Fin (ρ.length - 7) => (q.drop 7).toArray.getD l 0 := by
    funext l; simp only [ptOf, toArray_getD_list]
  have hρ' : ptOf (ρ.length - 7) (ρ.drop 7) =
      fun l : Fin (ρ.length - 7) => (ρ.drop 7).toArray.getD l 0 := by
    funext l; simp only [ptOf, toArray_getD_list]
  rw [hq, hρ']
  exact (KW4.kwS4_eq ν _ β _ _ _ fun _ _ => rfl).symm

/-- **`rsWeightF4` meets `rsWeightS4`** (`r″` of 7 coordinates, any claims and `ρ`). -/
theorem rsWeightF4_meets (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F)
    (ρ : Array K) (hr : r.size = 7) : rsWeightF4 ν r ps κ β ρ = rsWeightS4 ν r ps κ β ρ := by
  unfold rsWeightF4 rsWeightS4
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  have hc : ((phiTable r.toList).map K.ofF).size = 128 := by
    rw [Array.size_map, phiTable_size, Array.length_toList, hr]; norm_num
  have hg : ∀ k, ((phiTable r.toList).map K.ofF).getD k 0 = K.ofF ((phiTable r.toList).getD k 0) :=
    fun k => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases (phiTable r.toList)[k]? <;> rfl
  split_ifs with hF h1 h1
  · rw [wEvalKF4_eq, ofF_f0 _ hF, hc]
    exact sum_congr rfl fun k _ => by rw [hg]
  · rw [wEvalCF_eq, ofF_f0 _ hF, wEvalC_eq, hc]
    exact sum_congr rfl fun k _ => by rw [hg]
  · rw [wEvalKC4, KW.lsum_range, hc]
    exact sum_congr rfl fun k _ => by rw [hg, kwSL4I_eq]
  · rw [wEvalC_eq, hc]
    exact sum_congr rfl fun k _ => by rw [hg]

/-! ## Wiring -/

/-- An `OpImpl` with `rsWeight` at the 4.1 node `ν` (for `implN4`'s `base ν`). -/
def withRS4 (base : OpImpl) (ν : NodeKind) : OpImpl := { base with rsWeight := rsWeightF4 ν }

/-- Its specification. -/
def withRS4S (spec : OpSpec) (ν : NodeKind) : OpSpec := { spec with rsWeight := rsWeightS4 ν }

/-- **`withRS4` keeps `Meets`**, with `rsWeight`'s spec the 4.1 one. -/
theorem withRS4_meets {base : OpImpl} {spec : OpSpec} (ν : NodeKind) (h : base.Meets spec) :
    (withRS4 base ν).Meets (withRS4S spec ν) := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, fun r ps k b p hr _ => rsWeightF4_meets ν r ps k b p hr, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17⟩

/-! ## Controls -/

/-- (+) The cache is the kind's skeleton at its block bits: `N4` at 18 reads `skelN4`. -/
theorem skelAt_pos : skelAt .N4 18 = skelN4 := rfl

/-- (−) … and at other sizes the skeleton is built on the call (the cache is not read). -/
theorem skelAt_neg : skelAt .N4 17 = KW4.skel4 .N4 17 := rfl

end Impl
end FR

end G6_FRVerifierImplOps4

section G6_FRNodeRows4RepRsV

-- New for `flock-recursive` (R-OPS §5.2, stage R3: `rsWeight`'s replay at the previous-node slot).

/-!
# `rsWeight` in the replay template's form

The replay template of `rsWeight` (`FRNodeRows4RepRs`) computes `rsWeightF4 ν` from the operands'
cells for **every** claim point in `K` (the template has no branch on data: `rsWeightF4`'s `F` fast
path is a branch on `f₁ = 0`). Claim 2's kind factor (`kwSL4I`) is a sum over the skeleton's blocks
of products over each block's fixed bits; computed afresh at each of the 128 Frobenius stages it
would cost ≈ 2,000 `K` products per stage. The template instead uses that `x ↦ x^(2^k)` is a ring
map (characteristic two):

* per block `p`, once: `W₀(p) = (Σ_{i ∈ p} β^i)·Π_{b fixed} q_b` and `G(p) = Π_{b fixed} ρ_b`
  (`q_b`, `ρ_b`: the coordinate or one minus it, by the fixed bit);
* per stage `k`: the block's term is `W₀(p)^(2^k)·G(p)` (`block_frob`), one squaring chain per block.

This module states the template's arithmetic as a function of values, **`rsRef`**, and proves
**`rsWeightF4_ref`**: `rsWeightF4 ν r ps κ β ρ = rsRef ν r ps κ β ρ` when `|r| = 7`.
-/

namespace FR
namespace RsR
open Finset RecursionFast Rev4 Impl

/-! ## Frobenius -/

theorem sqIter_hom {R : Type*} [CommRing R] [ExpChar R 2] (k : ℕ) (x : R) :
    sqIter k x = iterateFrobenius R 2 k x := by
  rw [sqIter_eq, iterateFrobenius_def]

theorem sqIter_zeroK (k : ℕ) : sqIter k (0 : K) = 0 := by rw [sqIter_eq]; simp

/-! ## The template's values -/

/-- A fixed bit's factor: the coordinate (bit `1`) or one minus it (bit `0`). -/
def selV (x : ℕ → K) (b : ℕ × Bool) : K := if b.2 then x b.1 else 1 - x b.1

/-- A block's stage-0 `F`-side weight: `(Σ_{i ∈ exps} β^i)·Π_{fixed} q_b`. -/
def w0V (β : F) (q : ℕ → K) (p : List (ℕ × Bool) × List ℕ) : K :=
  K.ofF ((p.2.map (β ^ ·)).sum) * (p.1.map (selV q)).prod

/-- A block's `ρ` side: `Π_{fixed} ρ_b` (stage-independent). -/
def gV (ρ : ℕ → K) (p : List (ℕ × Bool) × List ℕ) : K := (p.1.map (selV ρ)).prod

/-- **Claim 2's block factor at stage `k`**, the template's way: Horner over the levels with
`s_l = 1 + q_l^(2^k) + ρ_l`, each level `Σ_p W₀(p)^(2^k)·G(p)`. -/
def kindV (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (q ρ : ℕ → K) (k : ℕ) : K :=
  KW.hornerK (fun l => 1 + sqIter k (q l) + ρ l) 0
    (sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum)

/-- Claim `j`'s stage-`k` term. -/
def termV (ν : NodeKind) (β : F) (ρ p : List K) (j k : ℕ) : K :=
  if j = 1 then
    eqPtsC ((p.map (sqIter k)).take 7) (ρ.take 7) *
      kindV (skelAt ν (ρ.length - 7)) β (fun l => (p.drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0) k
  else eqPtsC (p.map (sqIter k)) ρ

/-- **`rsWeight` as the template computes it.** -/
def rsRef (ν : NodeKind) (r : List F) (ps : List (List K)) (κ β : F) (ρ : List K) : K :=
  (ps.zipIdx.map fun p => K.ofF (κ ^ p.2) *
    ((List.range 128).map fun k => K.ofF ((phiTable r).toList.getD k 0) * termV ν β ρ p.1 p.2 k).sum).sum

/-! ## The identities -/

theorem ew_sel (q ρ : ℕ → K) (b : ℕ × Bool) : KW.ew q ρ b.1 b.2 = selV q b * selV ρ b := by
  obtain ⟨l, c⟩ := b; cases c <;> rfl

theorem sqIter_mulK (k : ℕ) (a b : K) : sqIter k (a * b) = sqIter k a * sqIter k b := by
  simp only [sqIter_hom, map_mul]

theorem sqIter_prodK (k : ℕ) (l : List K) : sqIter k l.prod = (l.map (sqIter k)).prod := by
  rw [sqIter_hom, map_list_prod]
  exact congrArg _ (List.map_congr_left fun x _ => (sqIter_hom k x).symm)

theorem sqIter_expSum (k : ℕ) (β : F) (es : List ℕ) :
    sqIter k (es.map (β ^ ·)).sum = (es.map ((sqIter k β) ^ ·)).sum := by
  simp only [sqIter_hom, map_list_sum, List.map_map]
  exact congrArg _ (List.map_congr_left fun i _ => by simp [map_pow])

theorem sqIter_sel (k : ℕ) (q : ℕ → K) (b : ℕ × Bool) :
    sqIter k (selV q b) = selV (fun l => sqIter k (q l)) b := by
  unfold selV; split_ifs <;> simp [sqIter_hom, map_sub, map_one]

/-- **One block at stage `k`**: the kind factor's block term is `W₀^(2^k)·G`. -/
theorem block_frob (k : ℕ) (β : F) (q ρ : ℕ → K) (p : List (ℕ × Bool) × List ℕ) :
    K.ofF ((p.2.map ((sqIter k β) ^ ·)).sum) * (p.1.map fun b => KW.ew (fun l => sqIter k (q l)) ρ b.1 b.2).prod =
      sqIter k (w0V β q p) * gV ρ p := by
  simp only [ew_sel, List.prod_map_mul, w0V, gV, sqIter_mulK, sqIter_ofF, sqIter_expSum, sqIter_prodK,
    List.map_map, Function.comp_def, sqIter_sel]
  ring

theorem ew_s (q ρ : ℕ → K) (l : ℕ) : KW.ew q ρ l false + KW.ew q ρ l true = 1 + q l + ρ l := by
  simp only [KW.ew, Bool.false_eq_true, ite_false, ite_true]
  linear_combination (q l * ρ l - q l - ρ l) * CharTwo.two_eq_zero (R := K)

/-- **`kwSL4I` at the stage-`k` point is the template's value.** -/
theorem kwSL4I_ref (ν : NodeKind) (β : F) (p ρ : List K) (k : ℕ) :
    kwSL4I ν (sqIter k β) (p.map (sqIter k)) ρ =
      eqPtsC ((p.map (sqIter k)).take 7) (ρ.take 7) *
        kindV (skelAt ν (ρ.length - 7)) β (fun l => (p.drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0) k := by
  unfold kwSL4I
  dsimp only
  congr 1
  have hq : ∀ l, ((p.map (sqIter k)).drop 7).toArray.getD l 0 = sqIter k ((p.drop 7).getD l 0) := fun l => by
    rw [toArray_getD_list, ← List.map_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases (p.drop 7)[l]? <;> simp [sqIter_zeroK]
  have hρ : ∀ l, (ρ.drop 7).toArray.getD l 0 = (ρ.drop 7).getD l 0 := fun l => toArray_getD_list _ l
  simp only [hq, hρ, KW4.kwKS, kindV, ew_s]
  congr 1
  refine List.map_congr_left fun g _ => congrArg _ (List.map_congr_left fun b _ => ?_)
  exact block_frob k β _ _ b

theorem arrF_getD (a : Array F) (k : ℕ) : a.getD k 0 = a.toList.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- One claim's stage sum, spec against template. -/
theorem claim_ref (ν : NodeKind) (c : Array F) (β : F) (ρ : Array K) (a : Array K) (j : ℕ) :
    ∑ k ∈ range 128, K.ofF (c.getD k 0) *
      (if j = 1 then kwSL4 ν (sqIter k β) (a.toList.map (sqIter k)) ρ.toList
       else eqPts (a.toList.map (sqIter k)) ρ.toList) =
    ((List.range 128).map fun k => K.ofF (c.toList.getD k 0) * termV ν β ρ.toList a.toList j k).sum := by
  rw [KW.lsum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [arrF_getD]
  congr 1
  unfold termV
  split_ifs with h
  · rw [← kwSL4I_eq, kwSL4I_ref]
  · rw [eqPtsC_eq]

/-- **`rsWeightF4` is the template's value** (`|r| = 7`, any claims and `ρ`). -/
theorem rsWeightF4_ref (ν : NodeKind) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K)
    (hr : r.size = 7) :
    rsWeightF4 ν r ps κ β ρ = rsRef ν r.toList (ps.map Array.toList) κ β ρ.toList := by
  rw [rsWeightF4_meets ν r ps κ β ρ hr]
  unfold rsWeightS4 rsRef
  rw [List.zipIdx_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  obtain ⟨a, j⟩ := p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [show K.ofF κ ^ j = K.ofF (κ ^ j) from (map_pow K.ofFRingHom κ j).symm, claim_ref]

end RsR
end FR

end G6_FRNodeRows4RepRsV

section G6_FRNodeRows4RepRs

-- New for `flock-recursive` (R-OPS §5.2, stage R3: `rsWeight`'s replay at the previous-node slot).

/-!
# The replay template of a node's `rsWeight` (`rsWeightF4 ν`, the kind factor included)

One node kind's sub-template, built with the chain library (`FRVIRTplChain`) and computing
`RsR.rsRef` (= `rsWeightF4 ν` by `RsR.rsWeightF4_ref`) for **any** claim points in `K`:

* `phiG`: the 128 coefficients `c_k(r″)` (`phiTable`'s tree, `F`);
* per claim, per coordinate, a `K` squaring chain of 127 steps (`sqChainK`: the stage points);
* per block of the kind skeleton, once: `W₀` and `G` (`prodK` over the fixed bits; the exponent sum
  from `β`'s powers `powF`), then `W₀`'s squaring chain (`blockG`);
* per claim and stage: claim 2 (`j = 1`) the product `eq(q_hi, ρ_hi)` and the kind factor (per level
  `Σ W₀^(2^k)·G`, Horner over the levels: `kindG`); the other claims `eq(q, ρ)` (`prodK`); each
  times `c_k` (`smulK`);
* `Σ_j κ^j v_j`.

**`ok_rsG`**: under the gate equations, the output is `rsRef ν r ps κ β ρ` at the inputs' values.
-/

namespace FR
namespace Tpl
open Circ GM Rev4 RsR Impl

variable {e : Env}

/-! ## Pieces -/

/-- `1 + a + b` (one factor of `eqPtsC`; linear). -/
def addE (a b : KF) : KF := addK (addK oneK a) b

theorem evK_addE (h1 : e.one = 1) (a b : KF) : evK e (addE a b) = 1 + evK e a + evK e b := by
  rw [addE, evK_addK, evK_addK, evK_oneK h1]

/-- A fixed bit's factor as a pair of forms. -/
def selK (x : ℕ → KF) (b : ℕ × Bool) : KF := if b.2 then x b.1 else oneSubK (x b.1)

theorem evK_selK (h1 : e.one = 1) {x : ℕ → KF} {v : ℕ → K} (hx : ∀ l, evK e (x l) = v l) (b : ℕ × Bool) :
    evK e (selK x b) = selV v b := by
  unfold selK selV; split_ifs <;> simp [hx, evK_oneSubK h1]

/-- `Σ_{i ∈ es} β^i` from the powers' forms. -/
def expSum (βp : List LinT) (es : List ℕ) : LinT := es.flatMap fun i => βp.getD i []

theorem ev_getD_pow {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {i : ℕ} (hi : i ≤ E) :
    (βp.getD i []).ev e = β ^ i := by
  have hl : βp.length = E + 1 := by simpa using congrArg List.length hβ
  rw [List.getD_eq_getElem _ _ (by omega)]
  have := congrArg (fun l => l[i]?) hβ
  simp only [List.getElem?_map, List.getElem?_range (show i < E + 1 by omega)] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  simpa using this

theorem ev_expSum {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {es : List ℕ} (hes : ∀ i ∈ es, i ≤ E) :
    (expSum βp es).ev e = (es.map (β ^ ·)).sum := by
  induction es with
  | nil => rfl
  | cons i es ih =>
    rw [expSum, List.flatMap_cons, ev_append, ← expSum, ih fun j hj => hes j (List.mem_cons_of_mem _ hj),
      ev_getD_pow hβ (hes i (List.mem_cons_self ..)), List.map_cons, List.sum_cons]

theorem evK_getD (l : List KF) (k : ℕ) : evK e (l.getD k zeroK) = (l.map (evK e)).getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

/-- The largest exponent of a skeleton. -/
def maxE (sk : List (List (List (ℕ × Bool) × List ℕ))) : ℕ :=
  ((sk.flatten).flatMap (·.2)).foldr max 0

theorem le_foldr_max : ∀ {l : List ℕ} {i : ℕ}, i ∈ l → i ≤ l.foldr max 0
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (le_foldr_max h) (le_max_right _ _)

theorem le_maxE {sk : List (List (List (ℕ × Bool) × List ℕ))} {g : List (List (ℕ × Bool) × List ℕ)}
    (hg : g ∈ sk) {p : List (ℕ × Bool) × List ℕ} (hp : p ∈ g) {i : ℕ} (hi : i ∈ p.2) : i ≤ maxE sk :=
  le_foldr_max (List.mem_flatMap.2 ⟨p, List.mem_flatten.2 ⟨g, hg, hp⟩, hi⟩)

/-! ## A block of the kind skeleton (once) -/

/-- **A block, once**: `W₀ = (Σ β^i)·Π q_b`, `G = Π ρ_b`, and `W₀`'s squaring chain (128 values). -/
def blockG (βp : List LinT) (qa ρa : ℕ → KF) (p : List (ℕ × Bool) × List ℕ) : GM (List KF × KF) :=
  (prodK (ofFK (expSum βp p.2) :: p.1.map (selK qa))).bind fun w0 =>
  (prodK (p.1.map (selK ρa))).bind fun g =>
  (sqChainK 127 w0).map fun ws => (ws, g)

/-- A block's values: `W₀`'s 128 Frobenius images, and `G`. -/
def blockV (β : F) (q ρ : ℕ → K) (p : List (ℕ × Bool) × List ℕ) : List K × K :=
  ((List.range 128).map fun i => sqIter i (w0V β q p), gV ρ p)

/-- The value of a built block. -/
def blockE (e : Env) (wg : List KF × KF) : List K × K := (wg.1.map (evK e), evK e wg.2)

theorem ok_blockG (h1 : e.one = 1) {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {qa ρa : ℕ → KF} {q ρ : ℕ → K}
    (hq : ∀ l, evK e (qa l) = q l) (hρ : ∀ l, evK e (ρa l) = ρ l) (p : List (ℕ × Bool) × List ℕ)
    (hp : ∀ i ∈ p.2, i ≤ E) : Ok e (blockG βp qa ρa p) fun wg => blockE e wg = blockV β q ρ p :=
  ok_bind (ok_prodK h1 _) fun w0 hw0 => ok_bind (ok_prodK h1 _) fun g hg =>
    ok_map (ok_sqChainK 127 w0) fun ws hws => (by
      have hw : evK e w0 = w0V β q p := by
        rw [hw0, List.map_cons, List.prod_cons, evK_ofFK, ev_expSum hβ hp, List.map_map, w0V]
        exact congrArg _ (congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hq b))
      have hg' : evK e g = gV ρ p := by
        rw [hg, List.map_map, gV]
        exact congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hρ b)
      simp only [blockE, blockV, hws, hw, hg'])

/-! ## Claim 2's kind factor at one stage -/

/-- One level at stage `k`: `Σ_p W₀(p)^(2^k)·G(p)`. -/
def levelG (k : ℕ) (lvl : List (List KF × KF)) : GM KF :=
  (mapL (fun wg : List KF × KF => mulK (wg.1.getD k zeroK) wg.2) lvl).map sumK

theorem ok_levelG {k : ℕ} (hk : k < 128) {β : F} {q ρ : ℕ → K} {lvl : List (List KF × KF)}
    {g : List (List (ℕ × Bool) × List ℕ)} (hl : lvl.map (blockE e) = g.map (blockV β q ρ)) :
    Ok e (levelG k lvl) fun y => evK e y = (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum :=
  ok_map (ok_mapL (E := evK e) (v := fun wg => (blockE e wg).1.getD k 0 * (blockE e wg).2) lvl
    fun wg _ => ok_mono (ok_mulK _ _) fun o ho => by rw [ho, evK_getD]; rfl) fun ms hms => (by
    rw [evK_sumK, hms]
    have := congrArg (List.map fun x : List K × K => x.1.getD k 0 * x.2) hl
    simp only [List.map_map] at this
    rw [show (fun wg : List KF × KF => (blockE e wg).1.getD k 0 * (blockE e wg).2) =
      (fun x : List K × K => x.1.getD k 0 * x.2) ∘ blockE e from rfl, this]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply, blockV]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp)

/-- **Claim 2's block factor at stage `k`**: the levels, then Horner with `s_l = 1 + q_l + ρ_l`. -/
def kindG (bl : List (List (List KF × KF))) (qk ρa : ℕ → KF) (k : ℕ) : GM KF :=
  (mapL (levelG k) bl).bind fun ys => hornerKG (fun l => addE (qk l) (ρa l)) 0 ys

theorem ok_kindG (h1 : e.one = 1) {k : ℕ} (hk : k < 128) {β : F} {q ρ : ℕ → K} {qk ρa : ℕ → KF}
    (hqk : ∀ l, evK e (qk l) = sqIter k (q l)) (hρ : ∀ l, evK e (ρa l) = ρ l)
    {bl : List (List (List KF × KF))} {sk : List (List (List (ℕ × Bool) × List ℕ))}
    (hbl : bl.map (List.map (blockE e)) = sk.map (List.map (blockV β q ρ))) :
    Ok e (kindG bl qk ρa k) fun y => evK e y = kindV sk β q ρ k := by
  have hlen : bl.length = sk.length := by simpa using congrArg List.length hbl
  refine ok_bind (P := fun ys => ys.map (evK e) =
      sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum) ?_ fun ys hys =>
    ok_mono (ok_hornerKG _ 0 ys) fun y hy => by
      rw [hy, hys, kindV]
      congr 1
      funext l
      rw [evK_addE h1, hqk, hρ]
  -- the levels, pairwise
  have key : ∀ (bl : List (List (List KF × KF))) (sk : List (List (List (ℕ × Bool) × List ℕ))),
      bl.map (List.map (blockE e)) = sk.map (List.map (blockV β q ρ)) →
      Ok e (mapL (levelG k) bl) fun ys => ys.map (evK e) =
        sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum := by
    intro bl
    induction bl with
    | nil => intro sk h; cases sk with
      | nil => exact ok_ret rfl
      | cons _ _ => simp at h
    | cons lv bl ih => intro sk h; cases sk with
      | nil => simp at h
      | cons g sk =>
        simp only [List.map_cons, List.cons.injEq] at h
        exact ok_bind (ok_levelG hk h.1) fun y hy => ok_map (ih sk h.2) fun ys hys => by
          simp [hy, hys]
  exact key bl sk hbl

/-! ## One claim -/

/-- The stage-`k` point from the coordinates' chains. -/
def stagePt (chs : List (List KF)) (k : ℕ) : List KF := chs.map (·.getD k zeroK)

theorem stagePt_ev {k : ℕ} (hk : k < 128) {chs : List (List KF)} {p : List K}
    (h : chs.map (List.map (evK e)) = p.map fun x => (List.range 128).map fun i => sqIter i x) :
    (stagePt chs k).map (evK e) = p.map (sqIter k) := by
  have := congrArg (List.map fun l : List K => l.getD k 0) h
  simp only [List.map_map] at this
  rw [stagePt, List.map_map]
  refine (List.map_congr_left fun ch _ => ?_).trans (this.trans (List.map_congr_left fun x _ => ?_))
  · simp only [Function.comp_apply, evK_getD]
  · simp only [Function.comp_apply]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp

theorem map_zipWith_addE (h1 : e.one = 1) (a b : List KF) :
    (List.zipWith addE a b).map (evK e) = List.zipWith (fun x y => 1 + x + y) (a.map (evK e)) (b.map (evK e)) := by
  induction a generalizing b with
  | nil => rfl
  | cons x a ih => cases b with
    | nil => rfl
    | cons y b => simp only [List.zipWith_cons_cons, List.map_cons, ih, evK_addE h1]

theorem ok_eqPtsC (h1 : e.one = 1) (a b : List KF) :
    Ok e (prodK (List.zipWith addE a b)) fun o => evK e o = eqPtsC (a.map (evK e)) (b.map (evK e)) :=
  ok_mono (ok_prodK h1 _) fun o ho => by rw [ho, map_zipWith_addE h1]; rfl

/-- Claim `j`'s stage-`k` term (claim 2: `eq(q_hi, ρ_hi)` times the kind factor). -/
def termG (ρI : List KF) (bl : List (List (List KF × KF))) (chs : List (List KF)) (j k : ℕ) : GM KF :=
  if j = 1 then
    (prodK (List.zipWith addE ((stagePt chs k).take 7) (ρI.take 7))).bind fun hi =>
    (kindG bl (fun l => ((stagePt chs k).drop 7).getD l zeroK) (fun l => (ρI.drop 7).getD l zeroK) k).bind
      fun kf => mulK hi kf
  else prodK (List.zipWith addE (stagePt chs k) ρI)

theorem take_drop_getD (l : List KF) (l' : ℕ) :
    evK e ((l.drop 7).getD l' zeroK) = ((l.map (evK e)).drop 7).getD l' 0 := by
  rw [evK_getD, List.map_drop]

theorem ok_termG (h1 : e.one = 1) (ν : NodeKind) {k : ℕ} (hk : k < 128) {β : F} {ρI : List KF} {ρ : List K}
    (hρ : ρI.map (evK e) = ρ) {bl : List (List (List KF × KF))} {chs : List (List KF)} {p : List K} {j : ℕ}
    (hch : chs.map (List.map (evK e)) = p.map fun x => (List.range 128).map fun i => sqIter i x)
    (hbl : j = 1 → bl.map (List.map (blockE e)) = (skelAt ν (ρ.length - 7)).map
      (List.map (blockV β (fun l => (p.drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0)))) :
    Ok e (termG ρI bl chs j k) fun o => evK e o = termV ν β ρ p j k := by
  have hst := stagePt_ev hk hch
  unfold termG termV
  split_ifs with hj
  · refine ok_bind (ok_eqPtsC h1 _ _) fun hi hhi => ok_bind (ok_kindG h1 hk (q := fun l => (p.drop 7).getD l 0)
      (ρ := fun l => (ρ.drop 7).getD l 0) (fun l => ?_) (fun l => ?_) (hbl hj)) fun kf hkf =>
      ok_mono (ok_mulK hi kf) fun o ho => by
        rw [ho, hhi, hkf, List.map_take, List.map_take, hst, hρ]
    · rw [take_drop_getD, hst, ← List.map_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_map]
      cases (p.drop 7)[l]? <;> simp [sqIter_zeroK]
    · rw [take_drop_getD, hρ]
  · exact ok_mono (ok_eqPtsC h1 _ _) fun o ho => by rw [ho, hst, hρ]

/-- **One claim**: its coordinates' squaring chains, then `Σ_k c_k · term_k`. -/
def claimG (ρI : List KF) (bl : List (List (List KF × KF))) (cT : List LinT) (pj : List KF × ℕ) : GM KF :=
  (mapL (sqChainK 127) pj.1).bind fun chs =>
  (mapL (fun k => (termG ρI bl chs pj.2 k).bind fun t => smulK (cT.getD k []) t) (List.range 128)).map sumK

/-- A claim's value. -/
def claimV (ν : NodeKind) (c : List F) (β : F) (ρ p : List K) (j : ℕ) : K :=
  ((List.range 128).map fun k => K.ofF (c.getD k 0) * termV ν β ρ p j k).sum

theorem ok_claimG (h1 : e.one = 1) (ν : NodeKind) {β : F} {ρI : List KF} {ρ : List K}
    (hρ : ρI.map (evK e) = ρ) {bl : List (List (List KF × KF))} {cT : List LinT} {c : List F}
    (hc : cT.map (LinT.ev e) = c) (a : List KF) (j : ℕ)
    (hbl : j = 1 → bl.map (List.map (blockE e)) = (skelAt ν (ρ.length - 7)).map
      (List.map (blockV β (fun l => ((a.map (evK e)).drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0)))) :
    Ok e (claimG ρI bl cT (a, j)) fun o => evK e o = claimV ν c β ρ (a.map (evK e)) j :=
  ok_bind (ok_mapL (E := List.map (evK e)) (v := fun x => (List.range 128).map fun i => sqIter i (evK e x)) a
    fun x _ => ok_sqChainK 127 x) fun chs hch =>
  ok_map (ok_mapL (E := evK e) (v := fun k => K.ofF (c.getD k 0) * termV ν β ρ (a.map (evK e)) j k) _
    fun k hk => ok_bind (ok_termG h1 ν (List.mem_range.1 hk) hρ (by rw [hch, List.map_map]; rfl) hbl)
      fun t ht => ok_mono (ok_smulK _ t) fun o ho => by rw [ho, ht, ev_getD_lag, hc]) fun ts hts =>
  (by rw [evK_sumK, hts, claimV])

/-! ## The template -/

theorem getD_map_nil {α β : Type} (f : List α → List β) (hf : f [] = []) (l : List (List α)) (j : ℕ) :
    (l.map f).getD j [] = f (l.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp [hf]

/-- **The node kind `ν`'s `rsWeight` template** over input forms: `r″` (`F`), the claims (`K`
coordinates), `κ`, `β` (`F`), `ρ` (`K`). -/
def rsG (ν : NodeKind) (rI : List LinT) (pI : List (List KF)) (κI βI : LinT) (ρI : List KF) : GM KF :=
  (phiG rI).bind fun cT =>
  (powF (maxE (skelAt ν (ρI.length - 7))) βI).bind fun βp =>
  (mapL (mapL (blockG βp (fun l => ((pI.getD 1 []).drop 7).getD l zeroK) (fun l => (ρI.drop 7).getD l zeroK)))
    (skelAt ν (ρI.length - 7))).bind fun bl =>
  (powF pI.length κI).bind fun κp =>
  (mapL (fun aj : List KF × ℕ => (claimG ρI bl cT aj).bind fun v => smulK (κp.getD aj.2 []) v) pI.zipIdx).map
    sumK

/-- **`rsG` computes `rsRef`** at the inputs' values. -/
theorem ok_rsG (h1 : e.one = 1) (ν : NodeKind) {rI : List LinT} {pI : List (List KF)} {κI βI : LinT}
    {ρI : List KF} {r : List F} {ps : List (List K)} {κ β : F} {ρ : List K}
    (hr : rI.map (LinT.ev e) = r) (hp : pI.map (List.map (evK e)) = ps) (hκ : κI.ev e = κ)
    (hβ : βI.ev e = β) (hρ : ρI.map (evK e) = ρ) :
    Ok e (rsG ν rI pI κI βI ρI) fun o => evK e o = rsRef ν r ps κ β ρ := by
  have hlρ : ρI.length = ρ.length := by rw [← hρ, List.length_map]
  have hq0 : ∀ l, evK e (((pI.getD 1 []).drop 7).getD l zeroK) = ((ps.getD 1 []).drop 7).getD l 0 := fun l => by
    rw [take_drop_getD, ← hp, getD_map_nil _ rfl]
  refine ok_bind (ok_phiG h1 rI) fun cT hcT => ok_bind (ok_powF h1 _ βI) fun βp hβp =>
    ok_bind (P := fun bl => bl.map (List.map (blockE e)) = (skelAt ν (ρI.length - 7)).map
        (List.map (blockV β (fun l => ((ps.getD 1 []).drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0))))
      (ok_mapL _ fun g hg => ok_mapL _ fun p hp' => ok_blockG h1 (hβ ▸ hβp) hq0
        (fun l => by rw [take_drop_getD, hρ]) p fun i hi => le_maxE hg hp' hi) fun bl hbl =>
    ok_bind (ok_powF h1 pI.length κI) fun κp hκp =>
    ok_map (ok_mapL (E := evK e) (v := fun aj : List KF × ℕ =>
        K.ofF (κ ^ aj.2) * claimV ν (phiTable r).toList β ρ (aj.1.map (evK e)) aj.2) pI.zipIdx
      fun aj haj => ?_) fun vs hvs => ?_
  · obtain ⟨a, j⟩ := aj
    obtain ⟨-, hjl, ha⟩ := List.mem_zipIdx haj
    simp only [zero_add, Nat.sub_zero] at hjl ha
    refine ok_bind (ok_claimG h1 ν hρ (c := (phiTable r).toList) (by rw [hcT, hr]) a j fun hj => ?_)
      fun v hv => ok_mono (ok_smulK _ v) fun o ho => by
        rw [ho, hv, ev_getD_pow hκp (by omega), hκ]
    subst hj
    rw [hbl, hlρ, ← hp, getD_map_nil _ rfl, List.getD_eq_getElem _ _ hjl, ha]
  · rw [evK_sumK, hvs, rsRef, ← hp, List.zipIdx_map, List.map_map]
    rfl

end Tpl
end FR

end G6_FRNodeRows4RepRs

section G6_FRVIRTplCF

-- New for `flock-recursive` (track CF: closed-form evaluation of the replay templates).

/-!
# Repeated patterns in a template, and their rows' MLE in closed form

A replay template's rows are evaluated by the plan as a multilinear extension: row `X + i` of the
template, its forms over the wires. Most rows of the large templates are **instances of one
pattern**: the same gates `n` times, instance `s` at local `K + s·2^p`, its inputs read through
**placeholders** (`σ s i`, a form over the template's wires per instance).

* **`rowsAt gs k`**: a gate list's rows from local `k` (`Tpl.rows = rowsAt · 0`); `rowsAt_sub`:
  substituted gates (`Gate.sub`) have the substituted rows.
* **`tm s t e X rows`**: rows `X, X+1, …` at the row point `t` (20 coordinates), the forms at the
  wires `e` (matrix `s`); `tm_sub` (substitution is a pull-back of the wires), `tm_append`.
* **`Rep`**: `n` instances of a pattern padded to `2^p` rows and locals (`Rep.gates`).
* **`tm_rep`**: the rows' value in closed form. Instance `s`'s row `r` is row
  `X + s·2^p + r = 2^p·(⌊X/2^p⌋ + s + c_r) + lo_r`: the carry `c_r` and the low part `lo_r` depend on
  `r` only, so `eq(t, ·)` splits into a pattern factor and an instance factor `T(s + c_r)` for **any**
  offset `X`; a local of instance `s` likewise. The value is one pass over the pattern's rows with,
  per wire, an instance sum (`cW`).
-/

namespace FR
namespace Tpl
open Circ TEval Finset

/-! ## Rows from a first local -/

/-- A gate list's rows, its first local at `k`. -/
def rowsAt (gs : List Gate) (k : ℕ) : List RowT := (gatesAt gs k).flatMap fun p => p.2.rows p.1

@[simp] theorem rowsAt_nil (k : ℕ) : rowsAt [] k = [] := rfl

theorem rowsAt_cons (g : Gate) (gs : List Gate) (k : ℕ) :
    rowsAt (g :: gs) k = g.rows k ++ rowsAt gs (k + g.nloc) := by
  simp [rowsAt, gatesAt]

theorem rowsAt_append (a b : List Gate) (k : ℕ) :
    rowsAt (a ++ b) k = rowsAt a k ++ rowsAt b (k + nlocs a) := by
  simp [rowsAt, gatesAt_append]

theorem tpl_rows_eq (T : Tpl) : T.rows = rowsAt T.gates 0 := rfl

/-- A gate's row count (independent of its first local). -/
def Gate.nrow : Gate → ℕ
  | .mul .. => 1
  | .inv _ => 3
  | .mulAdd .. => 1
  | .pad r _ => r

theorem Gate.rows_length (g : Gate) (k : ℕ) : (g.rows k).length = g.nrow := by
  cases g <;> simp [Gate.rows, Gate.nrow]

/-- A gate list's row count. -/
def nrows (gs : List Gate) : ℕ := (gs.map Gate.nrow).sum

theorem rowsAt_length : ∀ (gs : List Gate) (k : ℕ), (rowsAt gs k).length = nrows gs
  | [], _ => rfl
  | g :: gs, k => by
    rw [rowsAt_cons, List.length_append, Gate.rows_length, rowsAt_length gs]; simp [nrows]

theorem nrows_append (a b : List Gate) : nrows (a ++ b) = nrows a + nrows b := by simp [nrows]

theorem nlocs_app (a b : List Gate) : nlocs (a ++ b) = nlocs a + nlocs b := by simp [nlocs]

/-! ## Substitution -/

/-- A row with its forms substituted. -/
def RowT.sub (σ : ℕ → LinT) (k0 : ℕ) (r : RowT) : RowT := ⟨subW σ k0 r.a, subW σ k0 r.b, subW σ k0 r.c⟩

theorem subW_L (σ : ℕ → LinT) (k0 k : ℕ) : subW σ k0 (L k) = L (k0 + k) := rfl

theorem subW_C (σ : ℕ → LinT) (k0 : ℕ) (c : F) : subW σ k0 (C c) = C c := rfl

theorem subW_app (σ : ℕ → LinT) (k0 : ℕ) (a b : LinT) : subW σ k0 (a ++ b) = subW σ k0 a ++ subW σ k0 b := by
  simp [subW, List.flatMap_append]

theorem subW_sc (σ : ℕ → LinT) (k0 : ℕ) (c : F) : ∀ l : LinT, subW σ k0 (sc c l) = sc c (subW σ k0 l)
  | [] => rfl
  | t :: l => by
    obtain ⟨w, x⟩ := t
    have ih := subW_sc σ k0 c l
    simp only [sc, List.map_cons] at ih ⊢
    rw [subW_cons, subW_cons σ k0 (w, x), List.map_append, ih]
    congr 1
    cases w <;> simp [subW, sc, mul_assoc]

theorem Gate.rows_sub (σ : ℕ → LinT) (k0 k : ℕ) (g : Gate) :
    (g.sub σ k0).rows (k0 + k) = (g.rows k).map (RowT.sub σ k0) := by
  cases g with
  | mul a b => rfl
  | inv a =>
    simp only [Gate.sub, Gate.rows, List.map_cons, List.map_nil, RowT.sub, subW_L, subW_app, subW_C,
      subW_sc, Nat.add_assoc]
    rfl
  | mulAdd a b c =>
    simp only [Gate.sub, Gate.rows, List.map_cons, List.map_nil, RowT.sub, subW_L, subW_app, subW_sc]
  | pad r l => simp only [Gate.sub, Gate.rows, List.map_replicate]; rfl

theorem rowsAt_sub (σ : ℕ → LinT) (k0 : ℕ) :
    ∀ (gs : List Gate) (k : ℕ), rowsAt (gs.map (Gate.sub σ k0)) (k0 + k) = (rowsAt gs k).map (RowT.sub σ k0)
  | [], _ => rfl
  | g :: gs, k => by
    rw [List.map_cons, rowsAt_cons, rowsAt_cons, nloc_sub, Gate.rows_sub, Nat.add_assoc, rowsAt_sub σ k0 gs,
      List.map_append]

theorem nrows_sub (σ : ℕ → LinT) (k0 : ℕ) (gs : List Gate) : nrows (gs.map (Gate.sub σ k0)) = nrows gs := by
  simp only [nrows, List.map_map]; congr 1; exact List.map_congr_left fun g _ => by cases g <;> rfl

theorem nlocs_subL (σ : ℕ → LinT) (k0 : ℕ) (gs : List Gate) : nlocs (gs.map (Gate.sub σ k0)) = nlocs gs := by
  simp only [nlocs, List.map_map]; congr 1; exact List.map_congr_left fun g _ => nloc_sub σ k0 g

/-! ## The rows' value -/

/-- **Rows `X, X+1, …`' value** (matrix `s`): `Σ_i eq(t, X + i)·⟨form_i, e⟩` over 20 row coordinates. -/
def tm (s : Mat) (t : ℕ → F) (e : Env) : ℕ → List RowT → F
  | _, [] => 0
  | X, r :: rs => gN 20 t X * (s.t r).ev e + tm s t e (X + 1) rs

theorem tm_append (s : Mat) (t : ℕ → F) (e : Env) :
    ∀ (X : ℕ) (a b : List RowT), tm s t e X (a ++ b) = tm s t e X a + tm s t e (X + a.length) b
  | _, [], _ => by simp [tm]
  | X, r :: a, b => by
    rw [List.cons_append, tm, tm, tm_append s t e (X + 1) a b, List.length_cons]
    rw [show X + 1 + a.length = X + (a.length + 1) by omega]; ring

theorem Mat.t_sub (s : Mat) (σ : ℕ → LinT) (k0 : ℕ) (r : RowT) : s.t (r.sub σ k0) = subW σ k0 (s.t r) := by
  cases s <;> rfl

/-- **Substituted rows are the rows at the pulled-back wires.** -/
theorem tm_sub (s : Mat) (t : ℕ → F) (e : Env) (σ : ℕ → LinT) (k0 : ℕ) :
    ∀ (X : ℕ) (rows : List RowT), tm s t e X (rows.map (RowT.sub σ k0)) = tm s t (pullE e σ k0) X rows
  | _, [] => rfl
  | X, r :: rs => by rw [List.map_cons, tm, tm, Mat.t_sub, subW_ev, tm_sub s t e σ k0 (X + 1) rs]

theorem tm_eq_sum (s : Mat) (t : ℕ → F) (e : Env) :
    ∀ (X : ℕ) (rows : List RowT), tm s t e X rows = ((rows.zipIdx X).map fun q => gN 20 t q.2 * (s.t q.1).ev e).sum
  | _, [] => rfl
  | X, r :: rs => by rw [tm, tm_eq_sum s t e (X + 1) rs, List.zipIdx_cons, List.map_cons, List.sum_cons]

/-- Empty rows have value `0`. -/
theorem tm_empty (s : Mat) (t : ℕ → F) (e : Env) : ∀ (X n : ℕ), tm s t e X (List.replicate n ⟨[], [], []⟩) = 0
  | _, 0 => rfl
  | X, n + 1 => by
    rw [List.replicate_succ, tm, tm_empty s t e (X + 1) n]; cases s <;> simp [Mat.t]


/-! ## Repeated patterns -/

/-- A placeholder: one form for every instance (`cst`), or one per instance (`var`). -/
inductive Ph where
  | cst (f : LinT)
  | var (fs : Array LinT)

/-- The placeholder's form at instance `s`. -/
def Ph.at : Ph → ℕ → LinT
  | .cst f, _ => f
  | .var fs, s => fs.getD s []

/-- **A repeated pattern**: `n` instances of the gates `pat`, padded to `2^p` rows and `2^p` locals;
instance `s` reads the pattern's input `i` as the form `σ s i` (placeholder `ph[i]`). -/
structure Rep where
  n : ℕ
  p : ℕ
  pat : List Gate
  ph : Array Ph

namespace Rep
variable (R : Rep)

/-- Instance `s`'s input `i`. -/
def σ (s i : ℕ) : LinT := (R.ph.getD i (.cst [])).at s

/-- The pattern padded to `2^p` rows and locals. -/
def padP : List Gate := R.pat ++ [.pad (2 ^ R.p - nrows R.pat) (2 ^ R.p - nlocs R.pat)]

/-- The first `m` instances' gates, the first one's locals from `K`. -/
def gatesN (m K : ℕ) : List Gate :=
  (List.range m).flatMap fun s => R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))

/-- **The repeated pattern's gates**, from local `K`. -/
def gates (K : ℕ) : List Gate := R.gatesN R.n K

/-- The pattern fits its stride. -/
def Fit : Prop := nrows R.pat ≤ 2 ^ R.p ∧ nlocs R.pat ≤ 2 ^ R.p

theorem nrows_padP (h : R.Fit) : nrows R.padP = 2 ^ R.p := by
  simp only [padP, nrows_append]; simp [nrows, Gate.nrow]; have := h.1; simp only [nrows] at this; omega

theorem nlocs_padP (h : R.Fit) : nlocs R.padP = 2 ^ R.p := by
  simp only [padP, nlocs_app]; simp [nlocs, Gate.nloc]; have := h.2; simp only [nlocs] at this; omega

theorem nlocs_gatesN (K : ℕ) : ∀ m, nlocs (R.gatesN m K) = m * nlocs R.padP
  | 0 => by simp [gatesN, nlocs]
  | m + 1 => by
    simp only [gatesN, List.range_succ, List.flatMap_append, List.flatMap_singleton, nlocs_app] at *
    rw [show nlocs ((List.range m).flatMap fun s => R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))) =
      nlocs (R.gatesN m K) from rfl, nlocs_gatesN K m, nlocs_subL]; ring

theorem nrows_gatesN (K : ℕ) : ∀ m, nrows (R.gatesN m K) = m * nrows R.padP
  | 0 => by simp [gatesN, nrows]
  | m + 1 => by
    simp only [gatesN, List.range_succ, List.flatMap_append, List.flatMap_singleton, nrows_append] at *
    rw [show nrows ((List.range m).flatMap fun s => R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))) =
      nrows (R.gatesN m K) from rfl, nrows_gatesN K m, nrows_sub]; ring

/-- The rows of the first `m` instances: the pattern's rows, substituted per instance. -/
theorem rowsAt_gatesN (h : R.Fit) (K : ℕ) : ∀ m, rowsAt (R.gatesN m K) K =
    (List.range m).flatMap fun s => (rowsAt R.padP 0).map (RowT.sub (R.σ s) (K + s * 2 ^ R.p))
  | 0 => rfl
  | m + 1 => by
    have e : R.gatesN (m + 1) K = R.gatesN m K ++ R.padP.map (Gate.sub (R.σ m) (K + m * 2 ^ R.p)) := by
      simp [gatesN, List.range_succ, List.flatMap_append]
    have hs := rowsAt_sub (R.σ m) (K + m * 2 ^ R.p) R.padP 0
    rw [Nat.add_zero] at hs
    rw [e, rowsAt_append, rowsAt_gatesN h K m, nlocs_gatesN, nlocs_padP R h, hs, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

end Rep

/-- The pattern's rows are the padded pattern's, less empty rows. -/
theorem tm_padP (R : Rep) (s : Mat) (t : ℕ → F) (e : Env) (X : ℕ) :
    tm s t e X (rowsAt R.padP 0) = tm s t e X (rowsAt R.pat 0) := by
  rw [Rep.padP, rowsAt_append, tm_append, rowsAt_cons]
  simp only [Gate.rows, rowsAt_nil, List.append_nil, tm_empty, add_zero]

/-- **The rows of a repeated pattern, instance by instance**: instance `s` is the pattern's rows at
`X + s·2^p`, at the wires it sees. -/
theorem tm_repI (R : Rep) (h : R.Fit) (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) :
    tm s t e X (rowsAt (R.gates K) K) =
      ∑ i ∈ range R.n, tm s t (pullE e (R.σ i) (K + i * 2 ^ R.p)) (X + i * 2 ^ R.p) (rowsAt R.pat 0) := by
  rw [Rep.gates, Rep.rowsAt_gatesN R h]
  have hl : ∀ i, ((rowsAt R.padP 0).map (RowT.sub (R.σ i) (K + i * 2 ^ R.p))).length = 2 ^ R.p := fun i => by
    rw [List.length_map, rowsAt_length, R.nrows_padP h]
  suffices ∀ m, tm s t e X ((List.range m).flatMap fun i => (rowsAt R.padP 0).map (RowT.sub (R.σ i) (K + i * 2 ^ R.p))) =
      ∑ i ∈ range m, tm s t (pullE e (R.σ i) (K + i * 2 ^ R.p)) (X + i * 2 ^ R.p) (rowsAt R.pat 0) from this R.n
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, tm_append, ih, Finset.sum_range_succ,
      tm_sub, tm_padP]
    congr 2
    rw [List.length_flatMap]
    simp only [hl, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-! ## The closed form -/

/-- The split of a row (or cell) `Y + i·2^p + r` at bit `p`: the low part and the carry depend on `r`. -/
theorem gN_spl {p : ℕ} (hp : p ≤ 20) (t : ℕ → F) (Y i r : ℕ) :
    gN 20 t (Y + i * 2 ^ p + r) = eqN p t ((Y % 2 ^ p + r) % 2 ^ p) *
      gN (20 - p) (fun l => t (p + l)) (Y / 2 ^ p + (i + (Y % 2 ^ p + r) / 2 ^ p)) := by
  have hP : 0 < 2 ^ p := Nat.two_pow_pos p
  have h1 := Nat.div_add_mod Y (2 ^ p)
  have h2 := Nat.div_add_mod (Y % 2 ^ p + r) (2 ^ p)
  have e : Y + i * 2 ^ p + r = 2 ^ p * (Y / 2 ^ p + (i + (Y % 2 ^ p + r) / 2 ^ p)) + (Y % 2 ^ p + r) % 2 ^ p := by
    rw [mul_add, mul_add]
    nlinarith [h1, h2]
  rw [e, gN_split hp t _ (Nat.mod_lt _ hP)]

/-- Sums commute with a list sum. -/
theorem sum_listSum {α : Type*} (n : ℕ) (f : ℕ → α → F) :
    ∀ l : List α, ∑ i ∈ range n, (l.map (f i)).sum = (l.map fun a => ∑ i ∈ range n, f i a).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, sum_listSum n f l]

namespace Rep
variable (R : Rep)

/-- The instance factor of the rows: `eq(t_hi, ⌊X/2^p⌋ + h)`. -/
def Tf (t : ℕ → F) (X h : ℕ) : F := gN (20 - R.p) (fun l => t (R.p + l)) (X / 2 ^ R.p + h)

/-- The carry of pattern row (or local) `r` at offset `Y`. -/
def car (Y r : ℕ) : ℕ := (Y % 2 ^ R.p + r) / 2 ^ R.p

/-- The low part of pattern row (or local) `r` at offset `Y`. -/
def low (Y r : ℕ) : ℕ := (Y % 2 ^ R.p + r) % 2 ^ R.p

/-- **A wire's instance sum** for pattern row `r`: `Σ_s T(s + c_r)·(wire at instance s)`. -/
def cW (t : ℕ → F) (e : Env) (X K r : ℕ) (w : Wire) : F :=
  ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) * w.ev (pullE e (R.σ i) (K + i * 2 ^ R.p))

/-- The closed form over the pattern's rows from pattern row `r`. -/
def passV (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) : ℕ → List RowT → F
  | _, [] => 0
  | r, row :: rows => eqN R.p t (R.low X r) * ((s.t row).map fun τ => τ.2 * R.cW t e X K r τ.1).sum +
      passV s t e X K (r + 1) rows

theorem passV_eq (hp : R.p ≤ 20) (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) :
    ∀ (r : ℕ) (rows : List RowT), ∑ i ∈ range R.n, tm s t (pullE e (R.σ i) (K + i * 2 ^ R.p)) (X + i * 2 ^ R.p + r) rows =
      R.passV s t e X K r rows
  | _, [] => by simp [tm, passV]
  | r, row :: rows => by
    simp only [tm, passV, Finset.sum_add_distrib]
    rw [← passV_eq hp s t e X K (r + 1) rows]
    congr 1
    · simp only [gN_spl hp, LinT.ev, cW, Tf, car, low]
      rw [← List.sum_map_mul_left]
      simp only [Finset.mul_sum]
      rw [← sum_listSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun τ _ => by ring)

end Rep


theorem lsum_range (n : ℕ) (f : ℕ → F) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

namespace Rep
variable (R : Rep)

/-- **The rows of a repeated pattern in closed form** (one pass over the pattern's rows). -/
theorem tm_rep (h : R.Fit) (hp : R.p ≤ 20) (s : Mat) (t : ℕ → F) (e : Env) (X K : ℕ) :
    tm s t e X (rowsAt (R.gates K) K) = R.passV s t e X K 0 (rowsAt R.pat 0) := by
  rw [tm_repI R h, ← R.passV_eq hp s t e X K 0]; simp only [Nat.add_zero]

/-! ### The wires' instance sums -/

theorem cW_one (t : ℕ → F) (e : Env) (X K r : ℕ) :
    R.cW t e X K r .one = e.one * ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) := by
  simp only [cW, Wire.ev, pullE, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cW_inp (t : ℕ → F) (e : Env) (X K r j : ℕ) :
    R.cW t e X K r (.inp j) = ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) * (R.σ i j).ev e := rfl

theorem cW_loc (hp : R.p ≤ 20) (t u : ℕ → F) (e : Env) (lam : F) (cl X K r k : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    R.cW t e X K r (.loc k) = lam * eqN R.p u (R.low (cl + K) k) *
      ∑ i ∈ range R.n, R.Tf t X (i + R.car X r) * R.Tf u (cl + K) (i + R.car (cl + K) k) := by
  simp only [cW, Wire.ev, pullE, he, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show cl + (K + i * 2 ^ R.p + k) = (cl + K) + i * 2 ^ R.p + k by ring, gN_spl hp]; simp only [Tf, low, car]; ring

/-! ### The evaluation: per-call sums once, then one pass over the pattern -/

/-- `Tf` at `h < n + 2` (the carries of rows and locals below `2^p` are `0` or `1`). -/
def tArr (t : ℕ → F) (X : ℕ) : Array F :=
  (Array.range (R.n + 2)).map fun h => gNL (20 - R.p) (fun l => t (R.p + l)) (X / 2 ^ R.p + h)

/-- `Tf` from the array, directly past it. -/
def tAt (A : Array F) (t : ℕ → F) (X h : ℕ) : F := if h < R.n + 2 then A.getD h 0 else R.Tf t X h

theorem tAt_eq (t : ℕ → F) (X h : ℕ) : R.tAt (R.tArr t X) t X h = R.Tf t X h := by
  unfold tAt
  split_ifs with hh
  · simp [tArr, Array.getD_eq_getD_getElem?, hh, gNL_eq, Tf]
  · rfl

def sS (A : Array F) (t : ℕ → F) (X c : ℕ) : F := sumL (fun i => R.tAt A t X (i + c)) (List.range R.n)

def sD (A B : Array F) (t u : ℕ → F) (X Y c c' : ℕ) : F :=
  sumL (fun i => R.tAt A t X (i + c) * R.tAt B u Y (i + c')) (List.range R.n)

def sZ (A : Array F) (t : ℕ → F) (e : Env) (X j c : ℕ) : F :=
  match R.ph.getD j (.cst []) with
  | .cst f => f.ev e * R.sS A t X c
  | .var fs => sumL (fun i => R.tAt A t X (i + c) * (fs.getD i []).ev e) (List.range R.n)

/-- A repeated pattern's per-call sums. -/
structure Cx where
  tA : Array F
  uA : Array F
  S0 : F
  S1 : F
  D : Array F
  Z : Array (F × F)
  tl : Array F
  ul : Array F

/-- **The per-call sums** (row point `t`, cell point `u`, wires `e` with locals `lam·eq(u, cl + ·)`,
rows from `X`, the pattern's first local `K`). -/
def ctx (t u : ℕ → F) (e : Env) (cl X K : ℕ) : Cx :=
  let tA := R.tArr t X
  let uA := R.tArr u (cl + K)
  ⟨tA, uA, R.sS tA t X 0, R.sS tA t X 1,
    #[R.sD tA uA t u X (cl + K) 0 0, R.sD tA uA t u X (cl + K) 0 1, R.sD tA uA t u X (cl + K) 1 0,
      R.sD tA uA t u X (cl + K) 1 1],
    (Array.range R.ph.size).map fun j => (R.sZ tA t e X j 0, R.sZ tA t e X j 1), loTab R.p t, loTab R.p u⟩

/-- A wire's instance sum from the context (carry `c` of its row). -/
def wv (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K c : ℕ) : Wire → F
  | .one => e.one * (if c = 0 then cx.S0 else if c = 1 then cx.S1 else R.sS cx.tA t X c)
  | .inp j => if c < 2 ∧ j < cx.Z.size then (if c = 0 then (cx.Z.getD j (0, 0)).1 else (cx.Z.getD j (0, 0)).2)
      else R.sZ cx.tA t e X j c
  | .loc k => lam * cx.ul.getD (R.low (cl + K) k) 0 *
      (if c < 2 ∧ R.car (cl + K) k < 2 then cx.D.getD (2 * c + R.car (cl + K) k) 0
       else R.sD cx.tA cx.uA t u X (cl + K) c (R.car (cl + K) k))

/-- **One pass over the pattern's rows** (from pattern row `r`). -/
def pass (s : Mat) (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) : ℕ → List RowT → F
  | _, [] => 0
  | r, row :: rows => cx.tl.getD (R.low X r) 0 * sumL (fun τ => τ.2 * R.wv cx t u e lam cl X K (R.car X r) τ.1) (s.t row) +
      pass s cx t u e lam cl X K (r + 1) rows

theorem sS_eq (t : ℕ → F) (X c : ℕ) : R.sS (R.tArr t X) t X c = ∑ i ∈ range R.n, R.Tf t X (i + c) := by
  simp only [sS, sumL_eq, tAt_eq, lsum_range]

theorem sD_eq (t u : ℕ → F) (X Y c c' : ℕ) :
    R.sD (R.tArr t X) (R.tArr u Y) t u X Y c c' = ∑ i ∈ range R.n, R.Tf t X (i + c) * R.Tf u Y (i + c') := by
  simp only [sD, sumL_eq, tAt_eq, lsum_range]

theorem sZ_eq (t : ℕ → F) (e : Env) (X j c : ℕ) :
    R.sZ (R.tArr t X) t e X j c = ∑ i ∈ range R.n, R.Tf t X (i + c) * (R.σ i j).ev e := by
  unfold sZ σ
  split
  · rename_i f hf
    rw [sS_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hf]; simp only [Ph.at]; ring
  · rename_i fs hf
    simp only [sumL_eq, tAt_eq, lsum_range, hf, Ph.at]

theorem wv_eq (hp : R.p ≤ 20) (t u : ℕ → F) (e : Env) (lam : F) (cl X K r : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) (w : Wire) :
    R.wv (R.ctx t u e cl X K) t u e lam cl X K (R.car X r) w = R.cW t e X K r w := by
  cases w with
  | one =>
    rw [cW_one, wv]
    congr 1
    simp only [ctx]
    split_ifs with h0 h1
    · rw [h0, sS_eq]
    · rw [h1, sS_eq]
    · rw [sS_eq]
  | inp j =>
    rw [cW_inp, wv, ← sZ_eq]
    simp only [ctx, Array.size_map, Array.size_range]
    split_ifs with h h0
    · simp [Array.getD_eq_getD_getElem?, h.2, h0]
    · have : R.car X r = 1 := by omega
      simp [Array.getD_eq_getD_getElem?, h.2, this]
    · rfl
  | loc k =>
    rw [cW_loc R hp t u e lam cl X K r k he, wv]
    simp only [ctx]
    rw [loTab_getD _ _ (show R.low (cl + K) k < 2 ^ R.p from Nat.mod_lt _ (Nat.two_pow_pos _))]
    congr 1
    rw [← sD_eq]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      interval_cases hc : R.car X r <;> interval_cases hc' : R.car (cl + K) k <;> rfl
    · rfl

theorem pass_eq (hp : R.p ≤ 20) (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    ∀ (r : ℕ) (rows : List RowT), R.pass s (R.ctx t u e cl X K) t u e lam cl X K r rows = R.passV s t e X K r rows
  | _, [] => rfl
  | r, row :: rows => by
    rw [pass, passV, pass_eq hp s t u e lam cl X K he (r + 1) rows, sumL_eq]
    congr 1
    rw [show (R.ctx t u e cl X K).tl = loTab R.p t from rfl,
      loTab_getD _ _ (show R.low X r < 2 ^ R.p from Nat.mod_lt _ (Nat.two_pow_pos _))]
    congr 1
    exact congrArg List.sum (List.map_congr_left fun τ _ => by rw [R.wv_eq hp t u e lam cl X K r he])

/-- **A repeated pattern's rows, evaluated** (the per-call sums, then one pass over the pattern's
rows `PR = rowsAt pat 0`). -/
theorem eval_eq (h : R.Fit) (hp : R.p ≤ 20) (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    R.pass s (R.ctx t u e cl X K) t u e lam cl X K 0 (rowsAt R.pat 0) = tm s t e X (rowsAt (R.gates K) K) := by
  rw [R.tm_rep h hp, R.pass_eq hp s t u e lam cl X K he]

end Rep


/-! ## Segments: irregular gates and repeated patterns -/

/-- A template segment: irregular gates, or a repeated pattern. -/
inductive SG where
  | irr (gs : List Gate)
  | rep (R : Rep)

/-- A segment's locals. -/
def SG.nl : SG → ℕ
  | .irr gs => nlocs gs
  | .rep R => R.n * nlocs R.padP

/-- A segment's gates, its first local at `K`. -/
def SG.gates : SG → ℕ → List Gate
  | .irr gs, _ => gs
  | .rep R, K => R.gates K

theorem SG.nlocs_gates (g : SG) (K : ℕ) : nlocs (g.gates K) = g.nl := by
  cases g with
  | irr gs => rfl
  | rep R => exact R.nlocs_gatesN K R.n

/-- The segments' locals. -/
def sgNl (l : List SG) : ℕ := (l.map SG.nl).sum

/-- **The segments' gates** from local `K`. -/
def sgGates : List SG → ℕ → List Gate
  | [], _ => []
  | g :: gs, K => g.gates K ++ sgGates gs (K + g.nl)

theorem nlocs_sgGates : ∀ (l : List SG) (K : ℕ), nlocs (sgGates l K) = sgNl l
  | [], _ => rfl
  | g :: gs, K => by rw [sgGates, nlocs_app, SG.nlocs_gates, nlocs_sgGates gs]; simp [sgNl]

theorem sgGates_append : ∀ (a b : List SG) (K : ℕ), sgGates (a ++ b) K = sgGates a K ++ sgGates b (K + sgNl a)
  | [], _, K => by simp [sgGates, sgNl]
  | g :: a, b, K => by
    rw [List.cons_append, sgGates, sgGates, sgGates_append a b, List.append_assoc]
    simp [sgNl, Nat.add_assoc]

/-! ## The segment builder -/

/-- **A segment builder**: from its first local, its segments and its result (as `GM`). -/
abbrev SM (α : Type) := ℕ → List SG × α

namespace SM
variable {α β : Type} {e : Env}

def ret (a : α) : SM α := fun _ => ([], a)

/-- `g`, then `f` of its result, whose locals follow `g`'s. -/
def bind (g : SM α) (f : α → SM β) : SM β := fun k =>
  let r := g k
  let r' := f r.2 (k + sgNl r.1)
  (r.1 ++ r'.1, r'.2)

def map (g : SM α) (h : α → β) : SM β := fun k => ((g k).1, h (g k).2)

/-- An irregular gadget. -/
def lift (g : GM α) : SM α := fun k => ([.irr (g k).1], (g k).2)

/-- **`n` instances of the pattern `pat`** (built at local `0`, stride `2^p`), instance `s` reading its
inputs as `ph`'s forms at `s`; the result: each instance's result forms, substituted. -/
def rep (n p : ℕ) (pat : GM (List LinT)) (ph : Array Ph) : SM (ℕ → List LinT) := fun k =>
  -- CF2: the pattern built once per call (the result closure no longer re-runs `pat 0`)
  let q := pat 0
  ([.rep ⟨n, p, q.1, ph⟩], fun s => q.2.map (subW (Rep.σ ⟨n, p, q.1, ph⟩ s) (k + s * 2 ^ p)))

/-- **`g` computes `P`**: wherever its gates' equations hold at `e`, its result satisfies `P`. -/
def Ok (e : Env) (g : SM α) (P : α → Prop) : Prop := ∀ k, Eqns e (sgGates (g k).1 k) k → P (g k).2

theorem ok_ret {P : α → Prop} {a : α} (h : P a) : Ok e (ret a) P := fun _ _ => h

theorem ok_bind {g : SM α} {f : α → SM β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hf : ∀ a, P a → Ok e (f a) Q) : Ok e (g.bind f) Q := fun k h => by
  simp only [bind, sgGates_append, Eqns.append, nlocs_sgGates] at h
  exact hf _ (hg k h.1) _ h.2

theorem ok_map {g : SM α} {h : α → β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hh : ∀ a, P a → Q (h a)) : Ok e (g.map h) Q := fun k hk => hh _ (hg k hk)

theorem ok_mono {g : SM α} {P Q : α → Prop} (hg : Ok e g P) (h : ∀ a, P a → Q a) : Ok e g Q :=
  fun k hk => h _ (hg k hk)

theorem ok_lift {g : GM α} {P : α → Prop} (hg : GM.Ok e g P) : Ok e (lift g) P := fun k h => by
  simp only [lift, sgGates, SG.gates, List.append_nil] at h
  exact hg k h

theorem eqns_gatesN (R : Rep) (h : R.Fit) (K : ℕ) : ∀ m, Eqns e (R.gatesN m K) K →
    ∀ s < m, Eqns e (R.padP.map (Gate.sub (R.σ s) (K + s * 2 ^ R.p))) (K + s * 2 ^ R.p)
  | 0, _, s, hs => absurd hs (Nat.not_lt_zero _)
  | m + 1, hE, s, hs => by
    have e1 : R.gatesN (m + 1) K = R.gatesN m K ++ R.padP.map (Gate.sub (R.σ m) (K + m * 2 ^ R.p)) := by
      simp [Rep.gatesN, List.range_succ, List.flatMap_append]
    rw [e1, Eqns.append, R.nlocs_gatesN, R.nlocs_padP h] at hE
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · exact eqns_gatesN R h K m hE.1 s hs
    · exact hE.2

/-- **A repeated pattern computes `V s` at instance `s`**, if the pattern does at any wires whose
inputs are the placeholders' values. -/
theorem ok_rep {n p : ℕ} {pat : GM (List LinT)} {ph : Array Ph} (hfit : Rep.Fit ⟨n, p, (pat 0).1, ph⟩)
    (V : ℕ → List F)
    (hpat : ∀ s < n, ∀ e' : Env, e'.one = e.one → (∀ i, e'.inp i = (Rep.σ ⟨n, p, (pat 0).1, ph⟩ s i).ev e) →
      Eqns e' (pat 0).1 0 → (pat 0).2.map (LinT.ev e') = V s) :
    Ok e (rep n p pat ph) fun res => ∀ s < n, (res s).map (LinT.ev e) = V s := fun k hE s hs => by
  simp only [rep, sgGates, SG.gates, List.append_nil, Rep.gates] at hE
  have h1 := eqns_gatesN _ hfit k n hE s hs
  have h2 := (eqns_sub _ _ _ 0).1 (by simpa using h1)
  rw [Rep.padP, Eqns.append] at h2
  have := hpat s hs (pullE e (Rep.σ ⟨n, p, (pat 0).1, ph⟩ s) (k + s * 2 ^ p)) rfl (fun i => rfl) h2.1
  simp only [rep, List.map_map, Function.comp_def, subW_ev]
  exact this

end SM

/-! ## The segments' rows' value -/

instance (R : Rep) : Decidable R.Fit := inferInstanceAs (Decidable (_ ∧ _))

/-- **The segments' rows' value**: irregular rows sparse, a fitting repeated pattern in closed form
(`Rep.pass`). -/
def sgVal (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl : ℕ) : ℕ → ℕ → List SG → F
  | _, _, [] => 0
  | X, K, .irr gs :: l => tm s t e X (rowsAt gs K) + sgVal s t u e lam cl (X + nrows gs) (K + nlocs gs) l
  | X, K, .rep R :: l =>
    (if R.p ≤ 20 ∧ R.Fit then R.pass s (R.ctx t u e cl X K) t u e lam cl X K 0 (rowsAt R.pat 0)
     else tm s t e X (rowsAt (R.gates K) K)) +
      sgVal s t u e lam cl (X + R.n * nrows R.padP) (K + R.n * nlocs R.padP) l


theorem sgVal_eq (s : Mat) (t u : ℕ → F) (e : Env) (lam : F) (cl : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    ∀ (X K : ℕ) (l : List SG), sgVal s t u e lam cl X K l = tm s t e X (rowsAt (sgGates l K) K)
  | _, _, [] => rfl
  | X, K, .irr gs :: l => by
    rw [sgVal, sgGates, rowsAt_append, tm_append, sgVal_eq s t u e lam cl he _ _ l, rowsAt_length]; rfl
  | X, K, .rep R :: l => by
    rw [sgVal, sgGates, rowsAt_append, tm_append, sgVal_eq s t u e lam cl he _ _ l, rowsAt_length]
    simp only [SG.gates, SG.nl, Rep.gates, R.nlocs_gatesN, R.nrows_gatesN]
    congr 1
    split_ifs with h
    · exact R.eval_eq h.2 h.1 s t u e lam cl X K he
    · rfl

end Tpl
end FR

end G6_FRVIRTplCF

section G6_FRNodeRows4RepCFRs

-- New for `flock-recursive` (track CF): `rsWeight`'s replay template as repeated patterns.

/-!
# `rsWeight`'s replay template, laid out as repeated patterns

R3's `rsG` computes `rsRef` gate by gate; 93 % of its rows are 128-step squaring chains and the
128 Frobenius stages. **`rsGS`** computes the same value (`ok_rsGS`) with those parts as repeated
patterns (`FRVIRTplCF.Rep`), whose rows' MLE the plan evaluates in closed form:

* the blocks once (`W₀`, `G`; irregular), then **one chain per block** (`chainS`: the pattern is a
  127-step `K` squaring chain, its seed a placeholder);
* **one chain per claim coordinate** (`chainS`);
* **stage group A** (`patA`, 128 instances): per claim `j ≠ 1`, `c_k · eq(p_j^(2^k), ρ)`; for claim 1
  the `eq` of its first seven coordinates;
* **stage group B** (`patB`, 128 instances): claim 1's kind factor at stage `k` (`kindG`), times A's
  prefix, times `c_k`;
* per claim, `κ^j · Σ_k` (irregular).

A pattern reads its inputs through placeholders: input `0` is `c_k`, slot `v` (inputs `1 + 2v`,
`2 + 2v`) a `K` value (`kv v`), each a constant or one form per stage (`Src`).
-/

namespace FR
namespace Tpl
open Circ GM Rev4 RsR Impl

variable {e : Env}

/-! ## Flat `K` lists -/

/-- `K` pairs, flat. -/
def flatK (l : List KF) : List LinT := l.flatMap fun x => [x.1, x.2]

/-- `K` values, flat. -/
def flatV (l : List K) : List F := l.flatMap fun x => [x.f₀, x.f₁]

/-- The `i`-th `K` pair of a flat list. -/
def kfAt (l : List LinT) (i : ℕ) : KF := (l.getD (2 * i) [], l.getD (2 * i + 1) [])

theorem flatK_ev (l : List KF) : (flatK l).map (LinT.ev e) = flatV (l.map (evK e)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [flatK, flatV, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [ih]; rfl

theorem flatV_getD : ∀ (vs : List K) (i : ℕ) (hi : i < vs.length),
    (flatV vs).getD (2 * i) 0 = (vs[i]'hi).f₀ ∧ (flatV vs).getD (2 * i + 1) 0 = (vs[i]'hi).f₁
  | [], _, hi => absurd hi (by simp)
  | v :: vs, 0, _ => by simp [flatV]
  | v :: vs, i + 1, hi => by
    have := flatV_getD vs i (by simpa using hi)
    simp only [flatV, List.flatMap_cons] at this ⊢
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 1 = (2 * i + 1) + 2 by ring]
    simpa [List.getD_eq_getElem?_getD] using this

theorem evK_kfAt {l : List LinT} {vs : List K} (h : l.map (LinT.ev e) = flatV vs) {i : ℕ} (hi : i < vs.length) :
    evK e (kfAt l i) = vs[i] := by
  have := flatV_getD vs i hi
  rw [← h] at this
  apply K_ext'
  · show (l.getD (2 * i) []).ev e = _; rw [ev_getD_lag]; exact this.1
  · show (l.getD (2 * i + 1) []).ev e = _; rw [ev_getD_lag]; exact this.2

/-! ## Shapes -/

/-- `l` cut into the lengths of `L`'s lists. -/
def unflat {α β : Type} : List (List α) → List β → List (List β)
  | [], _ => []
  | g :: gs, l => l.take g.length :: unflat gs (l.drop g.length)

theorem unflat_map {α β γ : Type} (f : β → γ) : ∀ (L : List (List α)) (l : List β),
    unflat L (l.map f) = (unflat L l).map (List.map f)
  | [], _ => rfl
  | g :: gs, l => by
    simp only [unflat, List.map_cons, List.map_take]; rw [← List.map_drop, unflat_map f gs]

theorem unflat_flatten {α β : Type} : ∀ (L : List (List α)) (M : List (List β)),
    M.map List.length = L.map List.length → unflat L M.flatten = M
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | g :: gs, x :: xs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [unflat, List.flatten_cons, ← h.1, List.take_left', List.drop_left', unflat_flatten gs xs h.2]

theorem range_map_getElem {α β : Type} (l : List α) (f : α → β) (g : ℕ → β)
    (h : ∀ i (hi : i < l.length), g i = f l[i]) : (List.range l.length).map g = l.map f :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp [h i (by simpa using h1)]

/-! ## Placeholders: `c_k` and `K` slots -/

/-- Slot `v`'s `K` input. -/
def kv (v : ℕ) : KF := (I (1 + 2 * v), I (2 + 2 * v))

/-- A slot's source: one pair for every instance, or one per instance. -/
inductive Src where
  | cst (x : KF)
  | var (a : Array KF)

def Src.at : Src → ℕ → KF
  | .cst x, _ => x
  | .var a, s => a.getD s zeroK

def Src.ph : Src → List Ph
  | .cst x => [.cst x.1, .cst x.2]
  | .var a => [.var (a.map (·.1)), .var (a.map (·.2))]

/-- The placeholders: `c_k` (input `0`), then the slots. -/
def phOf (c : Array LinT) (sl : List Src) : Array Ph := (Ph.var c :: sl.flatMap Src.ph).toArray

theorem getD_pairs {α : Type} (d : α) (g : Src → List α) (hg : ∀ x, (g x).length = 2) :
    ∀ (sl : List Src) (v : ℕ) (hv : v < sl.length),
      (sl.flatMap g).getD (2 * v) d = (g sl[v]).getD 0 d ∧ (sl.flatMap g).getD (2 * v + 1) d = (g sl[v]).getD 1 d
  | [], _, hv => absurd hv (by simp)
  | x :: sl, 0, _ => by
    have := hg x
    match h : g x, this with
    | [a, b], _ => simp [h]
  | x :: sl, v + 1, hv => by
    have ih := getD_pairs d g hg sl v (by simpa using hv)
    have hx := hg x
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 2 * (v + 1) = (2 * v) + (g x).length by rw [hx]; ring,
      show 2 * v + (g x).length + 1 = (2 * v + 1) + (g x).length by ring]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_left _ _),
      Nat.add_sub_cancel] at ih ⊢
    exact ih

theorem Src.at_ph (x : Src) (s : ℕ) :
    ((x.ph.getD 0 (.cst [])).at s, (x.ph.getD 1 (.cst [])).at s) = x.at s := by
  cases x with
  | cst y => rfl
  | var a =>
    simp only [Src.ph, Src.at, List.getD_cons_zero, List.getD_cons_succ, Ph.at]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases a[s]? <;> rfl

/-- **A pattern's inputs at instance `s`**: `c_k` and the slots' values. -/
theorem phOf_inp {n p : ℕ} {g : List Gate} {c : Array LinT} {sl : List Src} {e' : Env} {s : ℕ}
    (h : ∀ i, e'.inp i = (Rep.σ ⟨n, p, g, phOf c sl⟩ s i).ev e) :
    (I 0).ev e' = (c.getD s []).ev e ∧ ∀ v (hv : v < sl.length), evK e' (kv v) = evK e (sl[v].at s) := by
  refine ⟨by rw [ev_I, h]; rfl, fun v hv => ?_⟩
  have hp := getD_pairs (Ph.cst []) Src.ph (fun x => by cases x <;> rfl) sl v hv
  have e0 : (phOf c sl).getD (1 + 2 * v) (.cst []) = (sl.flatMap Src.ph).getD (2 * v) (.cst []) := by
    simp [phOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Nat.add_comm 1]
  have e1 : (phOf c sl).getD (2 + 2 * v) (.cst []) = (sl.flatMap Src.ph).getD (2 * v + 1) (.cst []) := by
    simp [phOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, show 2 + 2 * v = (2 * v + 1) + 1 by ring]
  have := Src.at_ph sl[v] s
  rw [← hp.1, ← hp.2, ← e0, ← e1] at this
  apply K_ext'
  · show (I (1 + 2 * v)).ev e' = _; rw [ev_I, h, ← this]; rfl
  · show (I (2 + 2 * v)).ev e' = _; rw [ev_I, h, ← this]; rfl

/-! ## Repeated patterns at their own stride -/

/-- The stride of a pattern: the least `p` with `2^p` above its rows and locals. -/
def pOf (g : GM (List LinT)) : ℕ := Nat.clog 2 (max (nrows (g 0).1) (nlocs (g 0).1))

theorem fit_pOf (n : ℕ) (g : GM (List LinT)) (ph : Array Ph) : Rep.Fit ⟨n, pOf g, (g 0).1, ph⟩ := by
  have := Nat.le_pow_clog (by norm_num : 1 < 2) (max (nrows (g 0).1) (nlocs (g 0).1))
  exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩

/-- `n` instances of `g` at its stride. -/
def repA (n : ℕ) (g : GM (List LinT)) (ph : Array Ph) : SM (ℕ → List LinT) := SM.rep n (pOf g) g ph

theorem ok_repA {n : ℕ} {g : GM (List LinT)} {ph : Array Ph} (V : ℕ → List F)
    (hpat : ∀ s < n, ∀ e' : Env, e'.one = e.one → (∀ i, e'.inp i = (Rep.σ ⟨n, pOf g, (g 0).1, ph⟩ s i).ev e) →
      Eqns e' (g 0).1 0 → (g 0).2.map (LinT.ev e') = V s) :
    SM.Ok e (repA n g ph) fun res => ∀ s < n, (res s).map (LinT.ev e) = V s :=
  SM.ok_rep (fit_pOf n g ph) V hpat

/-! ## Chains -/

/-- The 127-step squaring chain of the `K` seed on inputs `0`, `1`, flat (`x^(2^i)`, `i ≤ 127`). -/
def chainP : GM (List LinT) := (sqChainK 127 (I 0, I 1)).map flatK

/-- **One chain per seed.** -/
def chainS (seeds : List KF) : SM (ℕ → List LinT) :=
  repA seeds.length chainP #[.var (seeds.map (·.1)).toArray, .var (seeds.map (·.2)).toArray]

theorem ok_chainS (seeds : List KF) :
    SM.Ok e (chainS seeds) fun res => ∀ b < seeds.length,
      (res b).map (LinT.ev e) = flatV ((List.range 128).map fun i => sqIter i (evK e (seeds.getD b zeroK))) := by
  refine ok_repA _ fun s hs e' _ hinp hE => ?_
  have h := ok_sqChainK (e := e') 127 (I 0, I 1) 0 hE
  have hseed : evK e' (I 0, I 1) = evK e (seeds.getD s zeroK) := by
    rw [List.getD_eq_getElem _ _ hs]
    apply K_ext'
    · show (I 0).ev e' = _; rw [ev_I, hinp]
      simp [Rep.σ, Ph.at, Array.getD_eq_getD_getElem?, hs, evK]
    · show (I 1).ev e' = _; rw [ev_I, hinp]
      simp [Rep.σ, Ph.at, Array.getD_eq_getD_getElem?, hs, evK]
  show (flatK _).map (LinT.ev e') = _
  rw [flatK_ev, h, hseed]

/-- A chain's stage-`k` value. -/
theorem evK_chain {l : List LinT} {x : K} (h : l.map (LinT.ev e) = flatV ((List.range 128).map fun i => sqIter i x))
    {k : ℕ} (hk : k < 128) : evK e (kfAt l k) = sqIter k x := by
  rw [evK_kfAt h (by simpa using hk)]; simp

/-! ## The blocks once -/

/-- A block's `W₀` and `G` (irregular: the fixed bits differ per block). -/
def blockOG (βp : List LinT) (qa ρa : ℕ → KF) (p : List (ℕ × Bool) × List ℕ) : GM (KF × KF) :=
  (prodK (ofFK (expSum βp p.2) :: p.1.map (selK qa))).bind fun w0 =>
  (prodK (p.1.map (selK ρa))).map fun g => (w0, g)

theorem ok_blockOG (h1 : e.one = 1) {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {qa ρa : ℕ → KF} {q ρ : ℕ → K}
    (hq : ∀ l, evK e (qa l) = q l) (hρ : ∀ l, evK e (ρa l) = ρ l) (p : List (ℕ × Bool) × List ℕ)
    (hp : ∀ i ∈ p.2, i ≤ E) : Ok e (blockOG βp qa ρa p) fun wg => (evK e wg.1, evK e wg.2) = (w0V β q p, gV ρ p) :=
  ok_bind (ok_prodK h1 _) fun w0 hw0 => ok_map (ok_prodK h1 _) fun g hg => (by
    have hw : evK e w0 = w0V β q p := by
      rw [hw0, List.map_cons, List.prod_cons, evK_ofFK, ev_expSum hβ hp, List.map_map, w0V]
      exact congrArg _ (congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hq b))
    have hg' : evK e g = gV ρ p := by
      rw [hg, List.map_map, gV]
      exact congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hρ b)
    simp only [hw, hg'])

/-! ## The kind factor at a stage (values per stage) -/

theorem ok_levelGS {k0 k : ℕ} {β : F} {q ρ : ℕ → K} {lvl : List (List KF × KF)}
    {g : List (List (ℕ × Bool) × List ℕ)}
    (hl : lvl.map (fun wg => (evK e (wg.1.getD k0 zeroK), evK e wg.2)) = g.map fun p => (sqIter k (w0V β q p), gV ρ p)) :
    Ok e (levelG k0 lvl) fun y => evK e y = (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum := by
  unfold levelG
  refine ok_map (ok_mapL (f := fun wg : List KF × KF => mulK (wg.1.getD k0 zeroK) wg.2) (E := evK e)
    (v := fun wg => evK e (wg.1.getD k0 zeroK) * evK e wg.2) lvl fun wg _ => ok_mulK _ _) fun ms hms => ?_
  rw [evK_sumK, hms]
  have := congrArg (fun l => (List.map (fun x : K × K => x.1 * x.2) l).sum) hl
  simp only [List.map_map] at this
  exact this

theorem ok_kindGS (h1 : e.one = 1) {k0 k : ℕ} {β : F} {q ρ : ℕ → K} {qk ρa : ℕ → KF}
    (hqk : ∀ l, evK e (qk l) = sqIter k (q l)) (hρ : ∀ l, evK e (ρa l) = ρ l)
    {bl : List (List (List KF × KF))} {sk : List (List (List (ℕ × Bool) × List ℕ))}
    (hbl : bl.map (List.map fun wg => (evK e (wg.1.getD k0 zeroK), evK e wg.2)) =
      sk.map (List.map fun p => (sqIter k (w0V β q p), gV ρ p))) :
    Ok e (kindG bl qk ρa k0) fun y => evK e y = kindV sk β q ρ k := by
  refine ok_bind (P := fun ys => ys.map (evK e) =
      sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum) ?_ fun ys hys =>
    ok_mono (ok_hornerKG _ 0 ys) fun y hy => by
      rw [hy, hys, kindV]
      congr 1
      funext l
      rw [evK_addE h1, hqk, hρ]
  have key : ∀ (bl : List (List (List KF × KF))) (sk : List (List (List (ℕ × Bool) × List ℕ))),
      bl.map (List.map fun wg => (evK e (wg.1.getD k0 zeroK), evK e wg.2)) =
        sk.map (List.map fun p => (sqIter k (w0V β q p), gV ρ p)) →
      Ok e (mapL (levelG k0) bl) fun ys => ys.map (evK e) =
        sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum := by
    intro bl
    induction bl with
    | nil => intro sk h; cases sk with
      | nil => exact ok_ret rfl
      | cons _ _ => simp at h
    | cons lv bl ih => intro sk h; cases sk with
      | nil => simp at h
      | cons g sk =>
        simp only [List.map_cons, List.cons.injEq] at h
        exact ok_bind (ok_levelGS h.1) fun y hy => ok_map (ih sk h.2) fun ys hys => by
          simp [hy, hys]
  exact key bl sk hbl


/-! ## Index lemmas -/

theorem getD_pairR {α : Type} (x y : ℕ → α) (d : α) : ∀ (n b : ℕ), b < n →
    ((List.range n).flatMap fun b => [x b, y b]).getD (2 * b) d = x b ∧
      ((List.range n).flatMap fun b => [x b, y b]).getD (2 * b + 1) d = y b
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, b, h => by
    have hl : ((List.range n).flatMap fun b => [x b, y b]).length = 2 * n := by
      simp [List.length_flatMap]; ring
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact getD_pairR x y d n b h
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
      simp

theorem phOf_inpD {n p : ℕ} {g : List Gate} {c : Array LinT} {sl : List Src} {e' : Env} {s : ℕ}
    (h : ∀ i, e'.inp i = (Rep.σ ⟨n, p, g, phOf c sl⟩ s i).ev e) :
    (I 0).ev e' = (c.getD s []).ev e ∧ ∀ v < sl.length, evK e' (kv v) = evK e ((sl.getD v (.cst zeroK)).at s) := by
  refine ⟨(phOf_inp h).1, fun v hv => ?_⟩
  rw [(phOf_inp h).2 v hv, List.getD_eq_getElem _ _ hv]

/-! ## The stage groups -/

/-- **Stage group A's pattern** (`m = |ρ|`; the claims' shapes `pI`): per claim `j`, `c_k · eq` of its
stage coordinates with `ρ` (`j ≠ 1`), or `eq` of the first seven (`j = 1`: the kind factor's prefix).
Slots: `ρ` (`0 … m−1`), then the claims' stage coordinates, flat. -/
def patA (m : ℕ) (pI : List (List KF)) : GM (List LinT) :=
  (mapL (fun cj : List KF × ℕ => if cj.2 = 1 then
      prodK (List.zipWith addE (cj.1.take 7) (((List.range m).map kv).take 7))
    else (prodK (List.zipWith addE cj.1 ((List.range m).map kv))).bind (smulK (I 0)))
    (unflat pI ((List.range pI.flatten.length).map fun i => kv (m + i))).zipIdx).map flatK

/-- Group A's values: per claim. -/
def vA (ρ : List K) (c : F) (Q : List (List K)) : List K :=
  Q.zipIdx.map fun qj => if qj.2 = 1 then eqPtsC (qj.1.take 7) (ρ.take 7) else K.ofF c * eqPtsC qj.1 ρ

theorem unflat_vals {α : Type} {L : List (List α)} {Q : List (List K)} (hQ : Q.map List.length = L.map List.length)
    (f : ℕ → KF) (hq : ∀ i < L.flatten.length, evK e (f i) = Q.flatten.getD i 0) :
    (unflat L ((List.range L.flatten.length).map f)).map (List.map (evK e)) = Q := by
  have hn : L.flatten.length = Q.flatten.length := by simp [List.length_flatten, hQ]
  rw [← unflat_map, List.map_map, hn]
  rw [range_map_getElem Q.flatten id (evK e ∘ f) fun i hi => by
    simp only [Function.comp_apply, id]; rw [hq i (by omega), List.getD_eq_getElem _ _ hi]]
  rw [List.map_id]; exact unflat_flatten L Q hQ

theorem ok_patA (h1 : e.one = 1) {m : ℕ} {pI : List (List KF)} {ρ : List K} {c : F} {Q : List (List K)}
    (hρ : ((List.range m).map kv).map (evK e) = ρ) (hc : (I 0).ev e = c)
    (hQ : Q.map List.length = pI.map List.length)
    (hq : ∀ i < pI.flatten.length, evK e (kv (m + i)) = Q.flatten.getD i 0) :
    Ok e (patA m pI) fun r => r.map (LinT.ev e) = flatV (vA ρ c Q) := by
  have hcs := unflat_vals hQ (fun i => kv (m + i)) hq
  unfold patA
  refine ok_map (ok_mapL (E := evK e) (v := fun cj : List KF × ℕ => if cj.2 = 1 then
      eqPtsC ((cj.1.map (evK e)).take 7) (ρ.take 7) else K.ofF c * eqPtsC (cj.1.map (evK e)) ρ) _
    fun cj _ => ?_) fun ys hys => ?_
  · by_cases hj : cj.2 = 1
    · simp only [hj, if_true]
      exact ok_mono (ok_eqPtsC h1 _ _) fun o ho => by rw [ho, List.map_take, List.map_take, hρ]
    · simp only [hj, if_false]
      exact ok_bind (ok_eqPtsC h1 _ _) fun x hx => ok_mono (ok_smulK (I 0) x) fun o ho => by
        rw [ho, hx, hc, hρ]
  · rw [flatK_ev, hys, vA, ← hcs, List.zipIdx_map, List.map_map]
    rfl

/-- **Stage group B's pattern** (skeleton `sk`, `m = |ρ|`, `n1` claim 1's length): claim 1's kind factor
at the stage, times A's prefix, times `c_k`. Slots: per block `W₀^(2^k)` and `G` (`2b`, `2b+1`), `ρ`
(from `2nB`), claim 1's stage coordinates (from `2nB + m`), the prefix (`2nB + m + n1`). -/
def patB (sk : List (List (List (ℕ × Bool) × List ℕ))) (m n1 : ℕ) : GM (List LinT) :=
  ((kindG (unflat sk ((List.range sk.flatten.length).map fun b => ([kv (2 * b)], kv (2 * b + 1))))
      (fun l => (((List.range n1).map fun l => kv (2 * sk.flatten.length + m + l)).drop 7).getD l zeroK)
      (fun l => (((List.range m).map fun l => kv (2 * sk.flatten.length + l)).drop 7).getD l zeroK) 0).bind
    fun kf => (mulK (kv (2 * sk.flatten.length + m + n1)) kf).bind fun v => smulK (I 0) v).map
    fun x => [x.1, x.2]

theorem ok_patB (h1 : e.one = 1) {sk : List (List (List (ℕ × Bool) × List ℕ))} {m n1 k : ℕ} {β : F}
    {q ρ : ℕ → K} {qq ρl : List K} {H : K} {c : F}
    (hb : ∀ b < sk.flatten.length, evK e (kv (2 * b)) = sqIter k (w0V β q (sk.flatten.getD b ([], []))) ∧
      evK e (kv (2 * b + 1)) = gV ρ (sk.flatten.getD b ([], [])))
    (hq : ((List.range n1).map fun l => kv (2 * sk.flatten.length + m + l)).map (evK e) = qq)
    (hqq : ∀ l, (qq.drop 7).getD l 0 = sqIter k (q l))
    (hρl : ((List.range m).map fun l => kv (2 * sk.flatten.length + l)).map (evK e) = ρl)
    (hρ : ∀ l, (ρl.drop 7).getD l 0 = ρ l)
    (hH : evK e (kv (2 * sk.flatten.length + m + n1)) = H) (hc : (I 0).ev e = c) :
    Ok e (patB sk m n1) fun r => r.map (LinT.ev e) = flatV [K.ofF c * (H * kindV sk β q ρ k)] := by
  unfold patB
  have hbl : (unflat sk ((List.range sk.flatten.length).map fun b => ([kv (2 * b)], kv (2 * b + 1)))).map
      (List.map fun wg => (evK e (wg.1.getD 0 zeroK), evK e wg.2)) =
      sk.map (List.map fun p => (sqIter k (w0V β q p), gV ρ p)) := by
    rw [← unflat_map, List.map_map]
    rw [range_map_getElem sk.flatten (fun p => (sqIter k (w0V β q p), gV ρ p)) _ fun b hb' => by
      simp only [Function.comp_apply, List.getD_cons_zero]
      rw [(hb b hb').1, (hb b hb').2, List.getD_eq_getElem _ _ hb']]
    rw [List.map_flatten]
    exact unflat_flatten sk _ (by simp)
  refine ok_map (P := fun x => evK e x = K.ofF c * (H * kindV sk β q ρ k))
    (ok_bind (ok_kindGS (k0 := 0) h1 (q := q) (ρ := ρ) (fun l => ?_) (fun l => ?_) hbl) fun kf hkf =>
      ok_bind (ok_mulK _ kf) fun v hv => ok_mono (ok_smulK (I 0) v) fun o ho => ?_) fun x hx => ?_
  · rw [evK_getD, List.map_drop, hq, hqq]
  · rw [evK_getD, List.map_drop, hρl, hρ]
  · rw [ho, hv, hkf, hH, hc]
  · simp only [List.map_cons, List.map_nil, flatV, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← hx]; rfl


/-! ## The template -/

/-- Chain `i`'s stage values (a slot source). -/
def srcCh (res : ℕ → List LinT) (i : ℕ) : Src :=
  let r := res i
  .var ((List.range 128).map fun k => kfAt r k).toArray

/-- A stage group's `j`-th result per stage (a slot source). -/
def srcSt (res : ℕ → List LinT) (j : ℕ) : Src := .var ((List.range 128).map fun k => kfAt (res k) j).toArray

theorem rarr_getD {α : Type} (f : ℕ → α) (d : α) {s : ℕ} (hs : s < 128) :
    ((List.range 128).map f).toArray.getD s d = f s := by
  simp [Array.getD_eq_getD_getElem?, hs]

/-- **The node kind `ν`'s `rsWeight` template as segments** (inputs as `rsG`'s). -/
def rsGS (ν : NodeKind) (rI : List LinT) (pI : List (List KF)) (κI βI : LinT) (ρI : List KF) : SM KF :=
  (SM.lift (phiG rI)).bind fun cT =>
  (SM.lift (powF (maxE (skelAt ν (ρI.length - 7))) βI)).bind fun βp =>
  (SM.lift (mapL (blockOG βp (fun l => ((pI.getD 1 []).drop 7).getD l zeroK) (fun l => (ρI.drop 7).getD l zeroK))
    (skelAt ν (ρI.length - 7)).flatten)).bind fun bo =>
  (chainS (bo.map (·.1))).bind fun wch =>
  (SM.lift (powF pI.length κI)).bind fun κp =>
  (chainS pI.flatten).bind fun cch =>
  (repA 128 (patA ρI.length pI) (phOf ((List.range 128).map fun k => cT.getD k []).toArray
    (ρI.map Src.cst ++ (List.range pI.flatten.length).map (srcCh cch)))).bind fun ra =>
  (repA 128 (patB (skelAt ν (ρI.length - 7)) ρI.length (pI.getD 1 []).length)
    (phOf ((List.range 128).map fun k => cT.getD k []).toArray
      (((List.range (skelAt ν (ρI.length - 7)).flatten.length).flatMap fun b =>
        [srcCh wch b, Src.cst (bo.getD b (zeroK, zeroK)).2]) ++ (ρI.map Src.cst ++
        ((List.range (pI.getD 1 []).length).map (fun l => srcCh cch ((pI.getD 0 []).length + l)) ++
        [srcSt ra 1]))))).bind fun rb =>
  (SM.lift (mapL (fun j => smulK (κp.getD j []) (sumK ((List.range 128).map fun k =>
      if j = 1 then kfAt (rb k) 0 else kfAt (ra k) j))) (List.range pI.length))).map sumK

theorem getD_appR {α : Type} (P M : List α) (d : α) (x : ℕ) : (P ++ M).getD (P.length + x) d = M.getD x d := by
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem flatten_getD_one {α : Type} (L : List (List α)) (d : α) {l : ℕ} (hl : l < (L.getD 1 []).length) :
    L.flatten.getD ((L.getD 0 []).length + l) d = (L.getD 1 []).getD l d := by
  match L, hl with
  | a :: b :: L, hl =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hl ⊢
    rw [List.flatten_cons, List.flatten_cons, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ hl]

/-- **`rsGS` computes `rsRef`** at the inputs' values. -/
theorem ok_rsGS (h1 : e.one = 1) (ν : NodeKind) {rI : List LinT} {pI : List (List KF)} {κI βI : LinT}
    {ρI : List KF} {r : List F} {ps : List (List K)} {κ β : F} {ρ : List K}
    (hr : rI.map (LinT.ev e) = r) (hp : pI.map (List.map (evK e)) = ps) (hκ : κI.ev e = κ)
    (hβ : βI.ev e = β) (hρ : ρI.map (evK e) = ρ) :
    SM.Ok e (rsGS ν rI pI κI βI ρI) fun o => evK e o = rsRef ν r ps κ β ρ := by
  have hlρ : ρI.length = ρ.length := by rw [← hρ, List.length_map]
  have hq0 : ∀ l, evK e (((pI.getD 1 []).drop 7).getD l zeroK) = ((ps.getD 1 []).drop 7).getD l 0 := fun l => by
    rw [take_drop_getD, ← hp, getD_map_nil _ rfl]
  have hρ0 : ∀ l, evK e ((ρI.drop 7).getD l zeroK) = (ρ.drop 7).getD l 0 := fun l => by
    rw [take_drop_getD, hρ]
  have hpf : pI.flatten.map (evK e) = ps.flatten := by rw [List.map_flatten, hp]
  have hpl : pI.length = ps.length := by rw [← hp, List.length_map]
  -- the values used below
  have hsq : ∀ s (x : List K) l, ((x.map (sqIter s)).drop 7).getD l 0 = sqIter s ((x.drop 7).getD l 0) := by
    intro s x l
    rw [← List.map_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (x.drop 7)[l]? <;> simp [sqIter_zeroK]
  set sk := skelAt ν (ρI.length - 7) with hsk
  simp only [rsGS]
  refine SM.ok_bind (SM.ok_lift (ok_phiG h1 rI)) fun cT hcT => ?_
  refine SM.ok_bind (SM.ok_lift (ok_powF h1 _ βI)) fun βp hβp => ?_
  refine SM.ok_bind (P := fun bo => bo.map (fun wg => (evK e wg.1, evK e wg.2)) = sk.flatten.map fun p =>
      (w0V β (fun l => ((ps.getD 1 []).drop 7).getD l 0) p, gV (fun l => (ρ.drop 7).getD l 0) p))
    (SM.ok_lift (ok_mapL _ fun p hp' => ok_blockOG h1 (hβ ▸ hβp) hq0 hρ0 p fun i hi => by
      obtain ⟨g, hg, hpg⟩ := List.mem_flatten.1 hp'
      exact le_maxE hg hpg hi)) fun bo hbo => ?_
  have hbl : bo.length = sk.flatten.length := by
    have := congrArg List.length hbo; rwa [List.length_map, List.length_map] at this
  have hbo' : ∀ b < sk.flatten.length, evK e (bo.getD b (zeroK, zeroK)).1 =
      w0V β (fun l => ((ps.getD 1 []).drop 7).getD l 0) (sk.flatten.getD b ([], [])) ∧
      evK e (bo.getD b (zeroK, zeroK)).2 = gV (fun l => (ρ.drop 7).getD l 0) (sk.flatten.getD b ([], [])) := by
    intro b hb
    have := congrArg (fun l => l[b]?) hbo
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show b < bo.length by omega),
      List.getElem?_eq_getElem hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hb]
    exact this
  refine SM.ok_bind (ok_chainS _) fun wch hwch => ?_
  refine SM.ok_bind (SM.ok_lift (ok_powF h1 pI.length κI)) fun κp hκp => ?_
  refine SM.ok_bind (ok_chainS _) fun cch hcch => ?_
  -- the stage values
  have hch : ∀ i < pI.flatten.length, ∀ s < 128, evK e (kfAt (cch i) s) = sqIter s (ps.flatten.getD i 0) := by
    intro i hi s hs
    rw [evK_chain (hcch i hi) hs, ← hpf, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
  set c : ℕ → F := fun s => (phiTable r).toList.getD s 0 with hc
  have hcs : ∀ s < 128, (((List.range 128).map fun k => cT.getD k []).toArray.getD s []).ev e = c s := by
    intro s hs
    rw [rarr_getD _ _ hs, ev_getD_lag, hcT, hr]
  have hsrc : ∀ (res : ℕ → List LinT) i s, s < 128 → (srcCh res i).at s = kfAt (res i) s := fun res i s hs => by
    simp only [srcCh, Src.at]; exact rarr_getD _ _ hs
  have hsrcS : ∀ (res : ℕ → List LinT) j s, s < 128 → (srcSt res j).at s = kfAt (res s) j := fun res j s hs => by
    simp only [srcSt, Src.at]; exact rarr_getD _ _ hs
  -- stage group A
  refine SM.ok_bind (ok_repA (fun s => flatV (vA ρ (c s) (ps.map (List.map (sqIter s)))))
    fun s hs e' hone hinp hE => ?_) fun ra hra => ?_
  · obtain ⟨hc0, hsl⟩ := phOf_inpD hinp
    have hlen : (ρI.map Src.cst ++ (List.range pI.flatten.length).map (srcCh cch)).length =
        ρI.length + pI.flatten.length := by simp
    refine ok_patA (e := e') (by rw [hone, h1]) (ρ := ρ) (c := c s) (Q := ps.map (List.map (sqIter s))) ?_
      (by rw [hc0, hcs s hs]) (by rw [← hp]; simp [Function.comp_def]) ?_ 0 hE
    · refine List.ext_getElem (by simp [hlρ]) fun v h1' h2' => ?_
      have hv : v < ρI.length := by simpa using h1'
      rw [List.getElem_map, List.getElem_map, List.getElem_range, hsl v (by rw [hlen]; omega),
        List.getD_append _ _ _ _ (by simpa using hv), List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map]
      simp only [Src.at]; subst hρ; simp
    · intro i hi
      have hi' : i < ps.flatten.length := by rw [← hpf, List.length_map]; exact hi
      rw [hsl (ρI.length + i) (by rw [hlen]; omega),
        show ρI.length + i = (ρI.map Src.cst).length + i by rw [List.length_map], getD_appR,
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range, hsrc _ _ _ hs,
        hch i hi s hs, ← List.map_flatten, List.getD_eq_getElem _ _ hi',
        List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi'), List.getElem_map]
  -- stage group B
  refine SM.ok_bind (ok_repA (fun s => flatV [K.ofF (c s) * (evK e (kfAt (ra s) 1) *
      kindV sk β (fun l => ((ps.getD 1 []).drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0) s)])
    fun s hs e' hone hinp hE => ?_) fun rb hrb => ?_
  · obtain ⟨hc0, hsl⟩ := phOf_inpD hinp
    set nB := sk.flatten.length with hnB
    set n1 := (pI.getD 1 []).length with hn1d
    set P := (List.range nB).flatMap fun b => [srcCh wch b, Src.cst (bo.getD b (zeroK, zeroK)).2] with hP
    set Cs := (List.range n1).map (fun l => srcCh cch ((pI.getD 0 []).length + l)) with hCs
    have hlP : P.length = 2 * nB := by simp [hP, List.length_flatMap]; ring
    have hn1 : n1 = (ps.getD 1 []).length := by rw [hn1d, ← hp, getD_map_nil _ rfl, List.length_map]
    have hlen : (P ++ (ρI.map Src.cst ++ (Cs ++ [srcSt ra 1]))).length = 2 * nB + (ρI.length + (n1 + 1)) := by
      simp [hlP, hCs]
    have hsl' : ∀ x < ρI.length + (n1 + 1), evK e' (kv (2 * nB + x)) =
        evK e (((ρI.map Src.cst ++ (Cs ++ [srcSt ra 1])).getD x (.cst zeroK)).at s) := fun x hx => by
      rw [hsl _ (by rw [hlen]; omega), ← hlP, getD_appR]
    refine ok_patB (e := e') (by rw [hone, h1]) (k := s) (β := β) (q := fun l => ((ps.getD 1 []).drop 7).getD l 0)
      (ρ := fun l => (ρ.drop 7).getD l 0) (qq := (ps.getD 1 []).map (sqIter s)) (ρl := ρ)
      (H := evK e (kfAt (ra s) 1)) (c := c s) (fun b hb => ?_) ?_ (fun l => hsq s _ l) ?_ (fun l => rfl) ?_
      (by rw [hc0, hcs s hs]) 0 hE
    · rw [← hnB] at hb
      have hp2 := getD_pairR (fun b => srcCh wch b) (fun b => Src.cst (bo.getD b (zeroK, zeroK)).2) (Src.cst zeroK) nB b hb
      have hw := hwch b (by rw [List.length_map]; omega)
      have hb0 : (bo.map (·.1)).getD b zeroK = (bo.getD b (zeroK, zeroK)).1 := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getD_eq_getElem _ _ (by omega),
          List.getElem_map]
      constructor
      · rw [hsl (2 * b) (by rw [hlen]; omega), List.getD_append _ _ _ _ (by rw [hlP]; omega), hp2.1,
          hsrc _ _ _ hs, evK_chain hw hs, hb0, (hbo' b hb).1]
      · rw [hsl (2 * b + 1) (by rw [hlen]; omega), List.getD_append _ _ _ _ (by rw [hlP]; omega), hp2.2]
        exact (hbo' b hb).2
    · refine List.ext_getElem (by simp [hn1]) fun l h1' h2' => ?_
      have hl : l < n1 := by simpa using h1'
      have h2 : 2 ≤ pI.length := by
        by_contra hc'; push_neg at hc'
        have : n1 = 0 := by rw [hn1d, List.getD_eq_default _ _ (by omega)]; rfl
        omega
      have hlt : (pI.getD 0 []).length + l < pI.flatten.length := by
        match pI, h2 with
        | a :: b :: L, _ =>
          simp only [List.getD_cons_zero, List.getD_cons_succ, hn1d] at hl ⊢
          simp only [List.flatten_cons, List.length_append]; omega
      rw [List.getElem_map, List.getElem_map, List.getElem_range, show 2 * nB + ρI.length + l = 2 * nB + (ρI.length + l) by ring,
        hsl' _ (by omega), show ρI.length + l = (ρI.map Src.cst).length + l by rw [List.length_map], getD_appR,
        List.getD_append _ _ _ _ (by simpa [hCs] using hl), List.getD_eq_getElem _ _ (by simpa [hCs] using hl)]
      simp only [hCs, List.getElem_map, List.getElem_range]
      rw [hsrc _ _ _ hs, hch _ hlt s hs]
      congr 1
      have := flatten_getD_one ps 0 (l := l) (by rw [← hn1]; exact hl)
      rw [show (pI.getD 0 []).length = (ps.getD 0 []).length by rw [← hp, getD_map_nil _ rfl, List.length_map],
        this, List.getD_eq_getElem _ _ (by rw [← hn1]; exact hl)]
    · refine List.ext_getElem (by simp [hlρ]) fun v h1' h2' => ?_
      have hv : v < ρI.length := by simpa using h1'
      rw [List.getElem_map, List.getElem_map, List.getElem_range, hsl' v (by omega),
        List.getD_append _ _ _ _ (by simpa using hv), List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map]
      simp only [Src.at]; subst hρ; simp
    · rw [show 2 * nB + ρI.length + n1 = 2 * nB + (ρI.length + n1) by ring, hsl' _ (by omega),
        show ρI.length + n1 = (ρI.map Src.cst).length + n1 by rw [List.length_map], getD_appR,
        show n1 = Cs.length by simp [hCs], List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [hsrcS _ _ _ hs]
  -- the claims
  refine SM.ok_map (SM.ok_lift (ok_mapL (E := evK e)
    (v := fun j => K.ofF (κ ^ j) * claimV ν (phiTable r).toList β ρ (ps.getD j []) j) (List.range pI.length)
    fun j hj => ok_mono (ok_smulK _ _) fun o ho => ?_)) fun vs hvs => ?_
  · have hj0 := List.mem_range.1 hj
    have hj' : j < ps.length := by rw [← hpl]; exact hj0
    rw [ho, ev_getD_pow hκp (by omega), hκ, evK_sumK, List.map_map, claimV]
    refine congrArg _ (congrArg List.sum (List.map_congr_left fun k hk => ?_))
    have hk' := List.mem_range.1 hk
    have hA := hra k hk'
    have hlA : (vA ρ (c k) (ps.map (List.map (sqIter k)))).length = ps.length := by simp [vA]
    simp only [Function.comp_apply]
    by_cases h1j : j = 1
    · subst h1j
      rw [if_pos rfl, evK_kfAt (hrb k hk') (by simp), List.getElem_singleton, evK_kfAt hA (by rw [hlA]; exact hj')]
      simp only [vA, List.getElem_map, List.getElem_zipIdx, if_true, termV, hlρ, sk]
      rw [List.getD_eq_getElem _ _ hj']
    · rw [if_neg h1j, evK_kfAt hA (by rw [hlA]; exact hj')]
      simp only [vA, List.getElem_map, List.getElem_zipIdx, termV, h1j, if_false, zero_add]
      rw [List.getD_eq_getElem _ _ hj']
  · rw [evK_sumK, hvs, rsRef]
    refine congrArg List.sum (List.ext_getElem (by simp [hpl]) fun j h1' h2' => ?_)
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, zero_add, claimV]
    rw [List.getD_eq_getElem _ _ (by simpa [hpl] using h1')]

end Tpl
end FR

end G6_FRNodeRows4RepCFRs
