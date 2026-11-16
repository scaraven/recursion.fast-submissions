-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Weights.lean` (formal rev 40f877dc) as `LvmWhirWeights` for lvm (WP-7).
/-
  LeanVM.Protocol.Whir.Sound.Weights

  The weights of the deployed WHIR verifier as multiaffine functions with known cube values: the
  out-of-domain weight `eq_eval(z, ·)`, the batched consistency weight `induced_weight`, the
  rotated opening weight, and the lane fold `dot(row, eq_kernel(folds))`.
-/
import LvmWhirCode
import LvmClaims
import LvmVCore
import LvmNovelBasis
import LvmInnerProduct
import LvmCpMultilinear

-- ===== merged from `LvmColumnWeight` (GOLF module merge: `LvmColumnWeight.lean` is now a stub importing `LvmWhirWeights`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/ColumnWeight.lean` (formal rev 40f877dc) as `LvmColumnWeight` for lvm
-- (WP-7). 4.34.1 drift fix: `subspaceRoots_eq` closed `[ofK (K.ofBits (2^0))] = [1]` by `decide +kernel`, which no longer
-- reduces (CompPoly 572f9973, S0-LVF §6); it is now `K.ofBits 1 = 1` (`rfl`) and `map_one`.
/-
  LeanVM.Protocol.Whir.ColumnWeight

  The column weights of leanVM's binary Reed-Solomon code: a codeword entry is the inner product
  of the message with a tensor weight, whose multilinear extension is a `κ`-factor product; and the
  verifier's batched query weight, transcribed and proved equal to the sum of those extensions.
-/

/-!
# Column weights

Two parts, both against leanVM pin `40f877dc2c858f013c5974ab71ca594b31a7aec9`.

**Annex D**, Lemma `lem:colweight` (`doc/leanvm/body/d-novel-basis.tex:99-117`; in
Annex B until `127510d1`): for `x ∈ D_{κ,R}` the weight
`W_x(u) = ∏_i Ŵ_i(x)^{u_i}` (`colWeight`) satisfies

* `Enc_{κ,R}(g)[x] = ⟨W_x, g⟩ = Σ_u W_x(u)·g(u)` (`enc_eq_sum_colWeight`, for `κ ≤ 64`), and
* `mle(W_x)(r) = ∏_{i<κ} ((1 + r_i) + r_i·Ŵ_i(x))` (`eval₂Mle_colWeightTable`), where
  `colWeightTable κ x` is `W_x` as CompPoly's value table (bit `i` of the index is `u_i`) and the
  extension is `CMlPolynomialEval.eval₂Mle` into `E`, the one `answer_eqWeight` speaks of.

`colWeightE κ x` packages the two as a `Weight E κ` of the inner-product interface
(`LeanVM.Protocol.ToArkLib.InnerProduct`), whose evaluator is the product; `enc_eq_pair` reads
a codeword entry as `Weight.pair` against the message table `msgTable g`.

**The verifier**, `crates/verifier/src/whir.rs:92-126`: `subspaceRoots` transcribes
`subspace_roots` and `inducedWeight` transcribes `induced_weight`, line by line: the roots
`W_i(e_i)` by the layer recurrence `value ← value² + root·value`, their inverses (zero kept as
zero), and per query the running product `product ← product·(1 + p_i·(1 + basis·inverse_i))` with
`basis ← basis² + root_i·basis` starting from `basis = K(query)`, i.e. `x_query`. The Rust's
`require` on the point's length is the `none` branch, and so is a length mismatch of the queries
and their weights, which the Rust's `zip` would truncate (it never sees one: the weights are
`powers(lam, queries.len())`, `whir.rs:191`).

* `subspaceRoots_eq`: `subspace_roots(n)` is `[W_0(e_0), …, W_n(e_n)]`;
* `inducedWeight_eq`: on well-formed input, `induced_weight(n, qs, ws, p)` is
  `Σ_q w_q·mle(W_{x_q})(p)`. In characteristic two the verifier's factor `1 + p(1 + Ŵ)` is the
  Annex's `(1 + p) + p·Ŵ`.

## Wrong readings excluded

* The Rust builds `K(1 << i)` and `K(query)` from 64-bit words; the Lean reads them with
  `K.ofBits`, which reduces modulo `2^64`. The verifier only calls these with `message_log ≤ 28`
  and queries below the block length, where the two agree. The Rust computes the roots in `K`, the
  Lean in `E` through `K`'s embedding, which commutes with the field operations.
* `Ŵ_i` is evaluated through the *unnormalized* recurrence and one inverse per coordinate; the
  recurrence is Annex Lemma `lem:subspace` (i) evaluated (`vanishingAt_succ`), the same update as
  the Rust `next_s` (`crates/pcs/src/ntt.rs`, `crates/pcs/src/whir_induce.rs`).
* `mle(W_x)` is the multilinear extension of the weight over the *message* cube `{0,1}^κ`, not
  over the domain.
-/

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

section

/-! ## The column weight -/

/-- The column weight `W_x(u) = ∏_i Ŵ_i(x)^{u_i}`. -/
def colWeight {κ : ℕ} (x : K) (u : Fin κ → Bool) : K :=
  ∏ i : Fin κ, if u i then normVanishingAt i x else 1

/-- Lemma `lem:colweight`, first identity: `Enc_{κ,R}(g)[x_v] = Σ_u W_{x_v}(u)·g(u)`. -/
theorem enc_eq_sum_colWeight {κ : ℕ} (R : ℕ) (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E)
    (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = ∑ u, ofK (colWeight (K.ofBits v) u) * g u := by
  rw [enc_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [novelAt_bitsToNat hκ, colWeight, mul_comm]

/-- `W_x` as a value table on `κ` variables: entry `j` is `W_x` at the cube point with bits
`j`, bit `0` first. -/
def colWeightTable (κ : ℕ) (x : K) : CMlPolynomialEval K κ :=
  Vector.ofFn fun j ↦ colWeight x ((bitsEquiv κ).symm j)

/-- A message as a value table on `κ` variables. -/
def msgTable {κ : ℕ} (g : (Fin κ → Bool) → E) : CMlPolynomialEval E κ :=
  Vector.ofFn fun j ↦ g ((bitsEquiv κ).symm j)

/-- Lemma `lem:colweight`, second identity: `mle(W_x)(r) = ∏_{i<κ} ((1 + r_i) + r_i·Ŵ_i(x))`. -/
theorem eval₂Mle_colWeightTable (κ : ℕ) (x : K) (r : Vector E κ) :
    eval₂Mle (colWeightTable κ x) (algebraMap K E) r =
      ∏ i : Fin κ, ((1 + r[i]) + r[i] * ofK (normVanishingAt i x)) := by
  set f : Fin κ → Bool → E := fun i b ↦ if b then r[i] * ofK (normVanishingAt i x) else 1 + r[i]
  have hterm : ∀ j : Fin (2 ^ κ),
      (map (algebraMap K E) (colWeightTable κ x))[j] * (lagrangeBasis r)[j] =
        ∏ i : Fin κ, f i ((bitsEquiv κ).symm j i) := by
    intro j
    simp only [Fin.getElem_fin]
    rw [lagrangeBasis_getElem_nat r j.isLt]
    simp only [map, colWeightTable, colWeight, Vector.getElem_map, Vector.getElem_ofFn, map_prod,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [bitsEquiv_symm_apply]
    simp only [f, CharTwo.sub_eq_add]
    split
    · rw [mul_comm]
      rfl
    · rw [map_one, one_mul]
  rw [eval₂Mle, evalMle_eq_sum, Finset.sum_congr rfl fun j _ ↦ hterm j,
    Equiv.sum_comp (bitsEquiv κ).symm (fun u ↦ ∏ i, f i (u i)), ← Fintype.prod_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [f, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  ring

/-- `W_x` as a weight of the inner-product interface: its cube values, and the product as the
evaluator of its extension. -/
def colWeightE (κ : ℕ) (x : K) : Weight E κ where
  onCube := map (algebraMap K E) (colWeightTable κ x)
  mle r := ∏ i : Fin κ, ((1 + r[i]) + r[i] * ofK (normVanishingAt i x))
  mle_eq r := (eval₂Mle_colWeightTable κ x r).symm

/-! ## The verifier's induced weight -/

/-- `subspace_roots(log_n)` (`whir.rs:92-104`):

```rust
let mut roots = vec![K(1)];
let mut layer: Vec<K> = (1..=log_n).map(|i| K(1 << i)).collect();
for _ in 0..log_n {
    let root = roots[roots.len() - 1];
    for value in &mut layer {
        *value = value.square() + root * *value;
    }
    roots.push(layer.remove(0));
}
roots
``` -/
def subspaceRoots (logN : ℕ) : List E :=
  loop logN [1] ((List.range' 1 logN).map fun i ↦ ofK (K.ofBits (2 ^ i)))
where
  /-- The `for` loop: `k` iterations remain. -/
  loop : ℕ → List E → List E → List E
    | 0, roots, _ => roots
    | k + 1, roots, layer =>
      let layer := layer.map fun value ↦ value ^ 2 + roots.getLastD 0 * value
      loop k (roots ++ [layer.headD 0]) layer.tail

/-- `induced_weight(message_log, queries, query_weights, point)` (`whir.rs:106-126`):

```rust
require(point.len() == message_log, VerifierError::InducedBasisDimensions)?;
let roots = subspace_roots(message_log);
let inverses: Vec<K> = roots.iter().map(|value| value.inv()).collect();
let mut total = ZERO;
for (&weight, &query) in query_weights.iter().zip(queries) {
    let mut basis = K(query);
    let mut product = weight;
    for (coordinate, &challenge) in point.iter().enumerate() {
        product *= ONE + challenge * (K(1) + basis * inverses[coordinate]);
        basis = basis.square() + roots[coordinate] * basis;
    }
    total += product;
}
Ok(total)
```

`K::inv` maps zero to zero. A failed `require`, or a length mismatch of the weights and the
queries (which the Rust's `zip` would truncate), is `none`. -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights : List E)
    (point : List E) : Option E :=
  if point.length = messageLog ∧ queryWeights.length = queries.length then
    let roots := subspaceRoots messageLog
    let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
    some <| (queryWeights.zip queries).foldl (fun total wq ↦
      total + (point.zipIdx.foldl (fun pb cc ↦
          (pb.1 * (1 + cc.1 * (1 + pb.2 * inverses.getD cc.2 0)),
            pb.2 ^ 2 + roots.getD cc.2 0 * pb.2))
        (wq.1, ofK (K.ofBits wq.2))).1) 0
  else none

/-! ## Correctness of the transcription -/

/-- The root `W_i(e_i)`, in `E`. -/
private abbrev root (i : ℕ) : E := ofK (vanishingAt i (basisVec i))

/-- `ofK` preserves powers. -/
private theorem ofK_pow (a : K) (m : ℕ) : ofK (a ^ m) = ofK a ^ m := map_pow (algebraMap K E) a m

/-- `ofK` preserves inverses. -/
private theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

/-- `W_0` is the identity. -/
private theorem vanishingAt_zero_left (a : K) : vanishingAt 0 a = a := by
  simp [vanishingAt]

/-- The loop invariant of `subspace_roots`: after `j` iterations the roots are
`W_0(e_0), …, W_j(e_j)` and the layer is `W_j(e_{j+1}), …`. -/
private theorem subspaceRoots_loop (k j : ℕ) :
    subspaceRoots.loop k ((List.range (j + 1)).map root)
        ((List.range' (j + 1) k).map fun c ↦ ofK (vanishingAt j (basisVec c))) =
      (List.range (j + k + 1)).map root := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [subspaceRoots.loop, List.range'_succ]
    have hlast : ((List.range (j + 1)).map root).getLastD 0 = root j := by
      rw [List.range_succ, List.map_append, List.map_singleton, List.getLastD_concat]
    have hstep : ∀ c, ofK (vanishingAt j (basisVec c)) ^ 2 +
        root j * ofK (vanishingAt j (basisVec c)) = ofK (vanishingAt (j + 1) (basisVec c)) := by
      intro c
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow]
    simp only [hlast, List.map_cons, List.map_map, Function.comp_def, hstep, List.headD_cons,
      List.tail_cons]
    have h := ih (j + 1)
    rw [show j + 1 + k + 1 = j + (k + 1) + 1 by (clear * -; omega)] at h
    rw [← h, List.range_succ (n := j + 1), List.map_append, List.map_singleton]

/-- `K.ofBits 1` is the unit of `K` (lvm WP-7: replaces leanVM's `decide +kernel` on
`[ofK (K.ofBits (2^0))] = [1]`, which no longer reduces at Lean 4.34.1 / CompPoly `572f9973`). -/
private theorem K_ofBits_one : K.ofBits 1 = 1 := rfl

/-- `subspace_roots(n) = [W_0(e_0), …, W_n(e_n)]`. -/
theorem subspaceRoots_eq (n : ℕ) :
    subspaceRoots n = (List.range (n + 1)).map fun i ↦ ofK (vanishingAt i (basisVec i)) := by
  have h := subspaceRoots_loop n 0
  simp only [Nat.zero_add] at h
  change _ = (List.range (n + 1)).map root
  rw [← h, subspaceRoots, show List.map root (List.range 1) = [1] by
    rw [List.range_one, List.map_singleton, root, vanishingAt_zero_left, basisVec, pow_zero,
      K_ofBits_one]; exact congrArg (· :: []) (map_one (algebraMap K E))]
  refine congrArg (subspaceRoots.loop n [1]) (List.map_congr_left fun c _ ↦ ?_)
  rw [vanishingAt_zero_left, basisVec]

/-- The inner loop of `induced_weight`: after the coordinates `l`, starting at coordinate `s`
with `basis = W_s(x)`, the product has gained `∏ (1 + p_c·(1 + W_c(x)·W_c(e_c)⁻¹))` and the
basis is `W_{s+|l|}(x)`. -/
private theorem inner_fold (roots inverses : List E) (x : K) (l : List E) (s : ℕ) (p : E)
    (hr : ∀ c, s ≤ c → c < s + l.length → roots.getD c 0 = root c)
    (hi : ∀ c, s ≤ c → c < s + l.length → inverses.getD c 0 = (root c)⁻¹) :
    (l.zipIdx s).foldl (fun pb cc ↦
        (pb.1 * (1 + cc.1 * (1 + pb.2 * inverses.getD cc.2 0)),
          pb.2 ^ 2 + roots.getD cc.2 0 * pb.2)) (p, ofK (vanishingAt s x)) =
      (p * ∏ i : Fin l.length, ((1 + l[i]) + l[i] * ofK (normVanishingAt (s + i) x)),
        ofK (vanishingAt (s + l.length) x)) := by
  induction l generalizing s p with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.foldl_cons]
    have hs : s < s + (a :: l).length := by simp
    simp only [hr s le_rfl hs, hi s le_rfl hs]
    have hW : ofK (vanishingAt s x) ^ 2 + root s * ofK (vanishingAt s x) =
        ofK (vanishingAt (s + 1) x) := by
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow]
    rw [hW, ih (s + 1) _ (fun c h1 h2 ↦ hr c (by omega) (by simp; omega))
      (fun c h1 h2 ↦ hi c (by omega) (by simp; omega))]
    have hn : ofK (vanishingAt s x) * (root s)⁻¹ = ofK (normVanishingAt s x) := by
      rw [normVanishingAt, ofK_mul, ofK_inv]
    refine Prod.ext ?_ ?_
    · change _ * _ * _ = p * ∏ i : Fin (l.length + 1), _
      rw [Fin.prod_univ_succ, hn]
      have hprod : ∏ i : Fin l.length, (1 + l[i] + l[i] * ofK (normVanishingAt (s + 1 + i) x)) =
          ∏ i : Fin l.length, (1 + (a :: l)[(i.succ : ℕ)] +
            (a :: l)[(i.succ : ℕ)] * ofK (normVanishingAt (s + (i.succ : ℕ)) x)) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        simp only [Fin.val_succ, List.getElem_cons_succ, Fin.getElem_fin]
        rw [show s + 1 + (i : ℕ) = s + ((i : ℕ) + 1) by omega]
      rw [hprod]
      simp only [Fin.val_zero, add_zero, List.getElem_cons_zero, Fin.getElem_fin]
      ring
    · change ofK (vanishingAt (s + 1 + l.length) x) = ofK (vanishingAt (s + (l.length + 1)) x)
      rw [show s + 1 + l.length = s + (l.length + 1) by omega]

/-- The outer loop of `induced_weight` is a sum. -/
private theorem foldl_add_eq_sum {α : Type*} (f : α → E) (t : E)
    (m : List α) : m.foldl (fun total a ↦ total + f a) t = t + (m.map f).sum := by
  induction m generalizing t with
  | nil => simp
  | cons a m ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

/-- The verifier's `induced_weight` computes `Σ_q w_q·mle(W_{x_q})(p)`: the batched
column weights of `lem:colweight` at the point. -/
theorem inducedWeight_eq (n : ℕ) (queries : List ℕ) (queryWeights : List E) (point : Vector E n)
    (h : queryWeights.length = queries.length) :
    inducedWeight n queries queryWeights point.toList =
      some ((queryWeights.zip queries).map fun wq ↦
        wq.1 * eval₂Mle (colWeightTable n (K.ofBits wq.2)) (algebraMap K E) point).sum := by
  simp only [inducedWeight, Vector.length_toList, h, and_self, ↓reduceIte]
  rw [foldl_add_eq_sum, zero_add]
  congr 2
  refine List.map_congr_left fun wq _ ↦ ?_
  have hroots : ∀ c, c < n + 1 → (subspaceRoots n).getD c 0 = root c := by
    intro c hc
    rw [List.getD_eq_getElem _ _ (by rw [subspaceRoots_eq]; simpa using hc)]
    simp [subspaceRoots_eq, root]
  have hb0 : ofK (K.ofBits wq.2) = ofK (vanishingAt 0 (K.ofBits wq.2)) := by
    rw [vanishingAt_zero_left]
  have hlen : point.toList.length = n := by simp
  rw [hb0, inner_fold _ _ _ _ 0 _ (fun c _ h2 ↦ hroots c (by (clear * - hlen h2; omega))) ?inv,
    eval₂Mle_colWeightTable]
  · dsimp only
    rw [← Fin.prod_congr' _ hlen]
    refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
    simp [Vector.getElem_toList]
  · intro c _ h2
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, subspaceRoots_eq]; simp; (clear * - hlen h2; omega))]
    rw [List.getElem_map]
    have := hroots c (by (clear * - hlen h2; omega))
    rw [List.getD_eq_getElem _ _ (by rw [subspaceRoots_eq]; simp; (clear * - hlen h2; omega))] at this
    rw [this]
    split
    · rename_i h0
      rw [h0, inv_zero]
    · rfl

end
end LeanVM.Protocol.Whir
end
-- ===== end of `LvmColumnWeight` =====

/-!
# The verifier's weights

The deployed verifier (`LeanVM.Protocol.Verifier`, transcribing `verify_whir` at leanVM
`40f877dc`, `crates/verifier/src/whir.rs:92-265`) evaluates
three kinds of weights at the terminal point and computes one kind of value from opened rows.
This module proves what the round-by-round analysis needs of each:

* **products of affine factors** are multiaffine (`isMultiaffine_prod`);
* `eqEval z` (the out-of-domain claim's weight) is multiaffine (`isMultiaffine_eqEval`), and its
  inner product with a message is the message's multilinear extension at `z`
  (`sum_eqEval_mul_eq_evalMle`);
* the verifier's `inducedWeight` (`induced_weight`) is the column-weight sum of Annex D
  `lem:colweight` (`inducedWeight_eq_sum`, through `LeanVM.Protocol.Whir.inducedWeight_eq`; the
  verifier's own `subspaceRoots` is the Annex's roots, `subspaceRoots_eq_closed`), hence
  multiaffine (`isMultiaffine_inducedWeight`), and its inner product with a message is the batched
  codeword entries, `Σ_q w_q Enc(G)[x_q]` (`sum_inducedWeight_mul`);
* the opening weight read at the rotated point, `w(p[ℓ₀:] ++ p[:ℓ₀])`, is multiaffine when `w` is
  the multilinear extension of its cube values (`IsMultilinearFn`,
  `isMultiaffine_of_isMultilinearFn`, `isMultiaffine_rotL`);
* `dot(row, eq_kernel(folds))`, the lane fold of an opened row (`enforcedSum`), is the row folded
  by `foldsN` (`dot_eqKernel`).

`joinMsg` regroups a message split into lanes and message bits into one message on the full
cube, `sum_joinMsg` relating the two inner products: the level interface, where the next
oracle's lanes are the first variables of the current level's message.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd Finset CompPoly CMlPolynomialEval

section

/-! ## Products of affine factors -/

/-- A function of one variable is affine. -/
def IsAffine1 (f : E → E) : Prop := ∀ X, f X = (1 - X) * f 0 + X * f 1

theorem getD_set (l : List E) {k : ℕ} (hk : k < l.length) (i : ℕ) (X : E) :
    (l.set k X).getD i 0 = if i = k then X else l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- **Products of affine factors are multiaffine.** -/
theorem isMultiaffine_prod (n : ℕ) (f : ℕ → E → E) (hf : ∀ i, IsAffine1 (f i)) :
    IsMultiaffine n fun l ↦ ∏ i : Fin n, f i (l.getD i 0) := by
  intro l hl k hk X
  have key : ∀ Y, ∏ i : Fin n, f i ((l.set k Y).getD i 0) =
      f k Y * ∏ i ∈ univ.erase (⟨k, hk⟩ : Fin n), f i (l.getD i 0) := by
    intro Y
    rw [← Finset.mul_prod_erase univ _ (mem_univ (⟨k, hk⟩ : Fin n))]
    congr 1
    · rw [getD_set l (hl ▸ hk)]; simp
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [getD_set l (hl ▸ hk)]
      have : (i : ℕ) ≠ k := fun h ↦ (Finset.mem_erase.mp hi).1 (Fin.ext h)
      simp [this]
  simp only [key]
  rw [hf k X]
  ring

/-- `foldl (*)` from `a` is `a` times the product. -/
theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/-- `foldl (+)` from `a` is `a` plus the sum. -/
theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-! ## The out-of-domain weight -/

/-- `eq_eval(z, x)` is the product of its coordinate factors. -/
theorem eqEval_eq_prod (z x : List E) (h : x.length = z.length) :
    eqEval z x = ∏ i : Fin z.length, (1 + z.getD i 0 + x.getD i 0) := by
  rw [eqEval, foldl_mul_eq, one_mul]
  induction z generalizing x with
  | nil => simp
  | cons a z ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      simp only [List.zipWith_cons_cons, List.prod_cons, List.length_cons, Fin.prod_univ_succ,
        Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
      rw [ih x (by simpa using h)]

/-- `eq_eval(z, ·)` is multiaffine on `|z|` coordinates. -/
theorem isMultiaffine_eqEval (z : List E) : IsMultiaffine z.length (eqEval z) := by
  have hp := isMultiaffine_prod z.length (fun i X ↦ 1 + z.getD i 0 + X) fun i X ↦ by ring
  intro l hl k hk X
  rw [eqEval_eq_prod z _ (by simp [hl]), eqEval_eq_prod z _ (by simp [hl]),
    eqEval_eq_prod z _ (by simp [hl])]
  exact hp l hl k hk X

/-- At a cube point, `eq_eval(z, p)` is the Lagrange weight `Π (p_b ? z_b : 1 − z_b)`. -/
theorem eqEval_bitsL {n : ℕ} (z : List E) (hz : z.length = n) (p : Fin n → Bool) :
    eqEval z (bitsL p) = ∏ b : Fin n, if p b then z.getD b 0 else 1 - z.getD b 0 := by
  subst hz
  rw [eqEval_eq_prod z _ (by simp)]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  have : (bitsL p).getD b 0 = bitE (p b) := by simp [bitsL, List.getD_eq_getElem?_getD]
  rw [this]
  cases p b
  · simp [bitE, CharTwo.sub_eq_add]
  · simp only [bitE, ite_true]
    rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The table of a message on the cube, in CompPoly's indexing. -/
def tableOf {n : ℕ} (G : (Fin n → Bool) → E) : CMlPolynomialEval E n :=
  Vector.ofFn fun j ↦ G ((bitsEquiv n).symm j)

/-- A point as a vector. -/
def vecOf (z : List E) : Vector E z.length := ⟨z.toArray, by simp⟩

/-! ## The rotated opening weight -/

/-- `p[j:] ++ p[:j]`, the verifier's rotation of the terminal point. -/
def rotL (j : ℕ) (l : List E) : List E := l.drop j ++ l.take j

theorem length_rotL (j : ℕ) (l : List E) : (rotL j l).length = l.length := by
  simp only [rotL, List.length_append, List.length_drop, List.length_take]
  omega

theorem rotL_set (j : ℕ) (l : List E) (hj : j ≤ l.length) {k : ℕ} (hk : k < l.length) (X : E) :
    rotL j (l.set k X) = (rotL j l).set (if k < j then l.length - j + k else k - j) X := by
  simp only [rotL, List.drop_set, List.take_set]
  split_ifs with h
  · rw [List.set_append_right _ _ (by simp)]
    congr 2
    simp
  · rw [List.set_eq_of_length_le (l := l.take j) (by simp; (clear * - h; omega)),
      List.set_append_left _ _ (by simp; omega)]

/-- Rotating the point keeps a weight multiaffine. -/
theorem isMultiaffine_rotL {n j : ℕ} {w : List E → E} (hw : IsMultiaffine n w) (hj : j ≤ n) :
    IsMultiaffine n fun l ↦ w (rotL j l) := by
  intro l hl k hk X
  simp only [rotL_set j l (hl ▸ hj) (hl ▸ hk)]
  exact hw _ (by rw [length_rotL, hl]) _ (by split_ifs <;> (clear hw; omega)) X

/-- A multilinear extension of its cube values is multiaffine. -/
theorem isMultiaffine_of_isMultilinearFn {μ : ℕ} {w : List E → E} (hw : IsMultilinearFn μ w) :
    IsMultiaffine μ w := by
  have hb : ∀ x, (boolPoint μ x).length = μ := fun x ↦ by simp [boolPoint]
  have hsum : IsMultiaffine μ fun l ↦ ∑ x : Fin (2 ^ μ), w (boolPoint μ x) *
      eqEval (boolPoint μ x) l :=
    IsMultiaffine.sum _ _ fun x _ ↦ by
      have := (isMultiaffine_eqEval (boolPoint μ x)).const_mul (w (boolPoint μ x))
      rwa [hb] at this
  intro l hl k hk X
  have hlen : ∀ Y, (l.set k Y).length = μ := fun Y ↦ by simp [hl]
  rw [hw _ (hlen X), hw _ (hlen 0), hw _ (hlen 1)]
  exact hsum l hl k hk X

/-! ## The induced weight -/

/-- The root `W_i(e_i)`, in `E`. -/
abbrev rootE (i : ℕ) : E := ofK (vanishingAt i (basisVec i))

private theorem ofK_pow' (a : K) (m : ℕ) : ofK (a ^ m) = ofK a ^ m :=
  map_pow (algebraMap K E) a m

private theorem vanishingAt_zero' (a : K) : vanishingAt 0 a = a := by
  simp [vanishingAt]

private theorem subspaceRootsAux_eq (k j : ℕ) :
    subspaceRootsAux k (rootE j)
        ((List.range' (j + 1) k).map fun c ↦ ofK (vanishingAt j (basisVec c))) =
      (List.range' (j + 1) k).map rootE := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have hstep : ∀ c, ofK (vanishingAt j (basisVec c)) ^ 2 +
        rootE j * ofK (vanishingAt j (basisVec c)) = ofK (vanishingAt (j + 1) (basisVec c)) := by
      intro c
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow']
    rw [List.range'_succ]
    simp only [subspaceRootsAux, List.map_cons, List.map_map, Function.comp_def, hstep]
    have := ih (j + 1)
    simp only [show j + 1 + 1 = j + 2 by (clear * -; omega)] at this ⊢
    rw [this]

/-- The verifier's `subspace_roots(n)` is `[W_0(e_0), …, W_n(e_n)]`. -/
theorem subspaceRoots_eq_closed (n : ℕ) :
    Verifier.subspaceRoots n = (List.range (n + 1)).map rootE := by
  have h1 : rootE 0 = 1 := by simp [rootE, vanishingAt_zero', basisVec_zero]
  have hl : (List.range n).map (fun i ↦ eOfNat (2 ^ (i + 1))) =
      (List.range' (0 + 1) n).map fun c ↦ ofK (vanishingAt 0 (basisVec c)) := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
    simp [eOfNat, vanishingAt_zero', basisVec, add_comm]
  rw [Verifier.subspaceRoots, hl, ← h1, subspaceRootsAux_eq n 0, List.range_eq_range',
    List.range'_succ, List.map_cons]

/-- The verifier's `subspace_roots` is the Annex transcription's. -/
theorem subspaceRoots_eq_whir (n : ℕ) : Verifier.subspaceRoots n = Whir.subspaceRoots n := by
  rw [subspaceRoots_eq_closed, Whir.subspaceRoots_eq]

/-- The verifier's `induced_weight` is the Annex transcription's on well-formed input. -/
theorem inducedWeight_eq_whir (n : ℕ) (qs : List ℕ) (ws p : List E) (hp : p.length = n)
    (hw : ws.length = qs.length) :
    Verifier.inducedWeight n qs ws p = (Whir.inducedWeight n qs ws p).getD 0 := by
  simp only [Verifier.inducedWeight, Whir.inducedWeight, hp, hw, and_self, ite_true,
    Option.getD_some, subspaceRoots_eq_whir]
  rfl

/-- The per-query factor of the induced weight at coordinate `i`: `(1 + r) + r·Ŵ_i(x_q)`. -/
def colFactor (q i : ℕ) (r : E) : E := (1 + r) + r * ofK (normVanishingAt i (K.ofBits q))

/-- **The induced weight in closed form**: `Σ_q w_q Π_i ((1 + r_i) + r_i Ŵ_i(x_q))`. -/
theorem inducedWeight_eq_sum (n : ℕ) (qs : List ℕ) (ws l : List E) (hl : l.length = n)
    (hw : ws.length = qs.length) :
    Verifier.inducedWeight n qs ws l =
      ((ws.zip qs).map fun wq ↦ wq.1 * ∏ i : Fin n, colFactor wq.2 i (l.getD i 0)).sum := by
  rw [inducedWeight_eq_whir n qs ws l hl hw]
  have hv : (⟨l.toArray, by simp [hl]⟩ : Vector E n).toList = l := by simp
  have := Whir.inducedWeight_eq n qs ws ⟨l.toArray, by simp [hl]⟩ hw
  rw [hv] at this
  rw [this, Option.getD_some]
  refine congrArg List.sum (List.map_congr_left fun wq _ ↦ ?_)
  rw [eval₂Mle_colWeightTable]
  refine congrArg (wq.1 * ·) (Finset.prod_congr rfl fun i _ ↦ ?_)
  simp [colFactor, List.getD_eq_getElem?_getD, hl, Vector.getElem_mk]

/-- A list-indexed linear combination of multiaffine weights is multiaffine. -/
theorem isMultiaffine_listSum {n : ℕ} {α : Type*} (xs : List α) (c : α → E)
    (F : α → List E → E) (hF : ∀ a, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ (xs.map fun a ↦ c a * F a l).sum := by
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hF a).const_mul (c a)).add ih

/-- The verifier's induced weight is multiaffine on `n` coordinates. -/
theorem isMultiaffine_inducedWeight (n : ℕ) (qs : List ℕ) (ws : List E)
    (hw : ws.length = qs.length) : IsMultiaffine n (Verifier.inducedWeight n qs ws) := by
  have h := isMultiaffine_listSum (n := n) (ws.zip qs) (fun wq ↦ wq.1)
    (fun wq l ↦ ∏ i : Fin n, colFactor wq.2 i (l.getD i 0))
    fun wq ↦ isMultiaffine_prod n _ fun i X ↦ by simp only [colFactor]; ring
  intro l hl k hk X
  have hlen : ∀ Y, (l.set k Y).length = n := fun Y ↦ by simp [hl]
  rw [inducedWeight_eq_sum n qs ws _ (hlen X) hw, inducedWeight_eq_sum n qs ws _ (hlen 0) hw,
    inducedWeight_eq_sum n qs ws _ (hlen 1) hw]
  exact h l hl k hk X

/-- At a cube point the column factors multiply to the column weight. -/
theorem prod_colFactor_bitsL {n : ℕ} (q : ℕ) (p : Fin n → Bool) :
    ∏ i : Fin n, colFactor q i ((bitsL p).getD i 0) = ofK (colWeight (K.ofBits q) p) := by
  rw [colWeight]
  change _ = algebraMap K E _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have : (bitsL p).getD i 0 = bitE (p i) := by simp [bitsL, List.getD_eq_getElem?_getD]
  rw [this, colFactor]
  cases p i
  · simp [bitE]
  · simp only [bitE, ite_true, one_mul]
    rw [CharTwo.add_self_eq_zero, zero_add]
    rfl

/-- A codeword entry at an integer position (`0` outside the domain). -/
noncomputable def encAt (n R : ℕ) (G : (Fin n → Bool) → E) (q : ℕ) : E :=
  if h : q < 2 ^ (n + R) then enc n R G ⟨q, h⟩ else 0

/-- Exchange a cube sum with a list sum of scaled terms. -/
theorem sum_listSum_mul {n : ℕ} {α : Type*} (L : List α) (c : α → E)
    (F : α → (Fin n → Bool) → E) (G : (Fin n → Bool) → E) :
    ∑ p, (L.map fun a ↦ c a * F a p).sum * G p = (L.map fun a ↦ c a * ∑ p, F a p * G p).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun p _ ↦ by ring) rfl

/-- **The consistency claims read the codeword.** The inner product of the verifier's induced
weight with a message is the batched codeword entries `Σ_q w_q Enc(G)[x_q]`, for queries in the
domain. -/
theorem sum_inducedWeight_mul {n : ℕ} (R : ℕ) (hn : n ≤ 64) (qs : List ℕ) (ws : List E)
    (hw : ws.length = qs.length) (hq : ∀ q ∈ qs, q < 2 ^ (n + R)) (G : (Fin n → Bool) → E) :
    ∑ p, Verifier.inducedWeight n qs ws (bitsL p) * G p =
      ((ws.zip qs).map fun wq ↦ wq.1 * encAt n R G wq.2).sum := by
  simp_rw [inducedWeight_eq_sum n qs ws _ (length_bitsL _) hw, prod_colFactor_bitsL]
  rw [sum_listSum_mul (ws.zip qs) (fun wq ↦ wq.1) (fun wq p ↦ ofK (colWeight (K.ofBits wq.2) p))]
  refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
  have hlt := hq wq.2 (List.of_mem_zip hwq).2
  simp only [encAt, hlt, ↓reduceDIte, enc_eq_sum_colWeight R hn G ⟨wq.2, hlt⟩]

end
end LeanVM.Protocol.Whir.Sound
