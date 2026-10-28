-- New for `flock-recursive` (BLUEPRINT A.9 `finP i`/`finPf`, A.10 P1.i–P3.i, B′; stage S-G1h).
-- RET-1: position-free declarations moved to `FRSoundnessCoreWeights`, `FRSoundnessCoreSG`.
import FRSoundnessPIOP
import FRVIRFinalsSG
import FRSoundnessCoreWeights
import FRSoundnessCoreSG

/-!
# The Ligerito weight tables and their extensions (A.9, A.10)

Level `i`'s claim is `⟨Wᵢ, f⁽ⁱ⁾⟩` over level `i`'s variables (`truthP1`, row bits low). This module
gives the tables level by level and their multilinear extensions, which are what `finPf`
evaluates (`lvStepV`, `w0V`).

* **Part A: extensions of ℕ-indexed tables.** `mleN n W ρ` (the MLE of `W` on `2^n` points).
  **`mleN_wSplit`**: the coordinate split's extension is `û(ρ₀)·W̃(ρ₁…)` (A.9's fold factor
  `uHat`); **`mleN_foldW`**: binding the row variables at `s` is evaluating at `s ++ ρ`
  (`foldW`, `mle_split`); **`mle_bitProd`**: a product-of-bits table's extension is
  `Π_v (1 − ρ_v + ρ_v a_v)`, so **`mleN_gW`**: the codeword weight `G_p`'s extension is the
  tensor weight `tensorTwin D logNMax` (A.1, the spec of `tensorW`); **`mleN_wNext`**: P3.i's table
  adds `Σ_q eq(κ_c, bits₉(q))·tensorW(p_q, ·)`.
* **Part B: the next level.** **`nextW W = wSplit (wNext (foldW W))`** (A.10 P3.i → P1.(i+1)).
  **`truthP1_next`**: if P1.i's folded claim is `⟨foldW W, fold_z(f⁽ⁱ⁾)⟩`, with `truthC` and
  `truthP3`, then `truthP1 (i+1) (nextW W) (vNext c)` (`vNext_eq`, `wSplit_sum`).
  **`mleN_nextW`**: its extension is `û(ρ₀)·(W̃(sᵢ ++ ρ₁…) + Σ_q eq(κ_c, q)·tensorW(p_q, ρ₁…))`,
  `finPf`'s level step `lvStepV` at the spec.
* **Part C: level 0** (A.9 `finPf`'s `Ŵ₀`, A.10 B′). `wE`: the E claim's weight
  `(A + κ_E B + κ_E² C)(r_E2, ·)` over the M rows (`rowMat`); **`sum_wE`**: its inner product with
  `f⁽⁰⁾` is `â_M + κ_E b̂_M + κ_E² ĉ_M` at `r_E2` (`mle_matVec`); **`mle_wE`**: its extension is
  `M̃(r_E2, ρ)` (`evalM`'s spec, `mle_matMle`; since revision 3.12 `finE` evaluates it at the F
  point `r′`). **`w0F Wrs cells κ′`**: the RS weight (E4's claim is RS claim 4, inside it) and the
  cells' indicators; **`truthP1_zero`**: from the RS claim's truth and the B′ truth,
  `truthP1 0 (ι ∘ w0F …) (ι v*)`; **`mleN_w0F`** with **`eqCellK_eq`**: its extension is `w0V`'s
  shape (`rsWeight + Σ_k κ′^(k+2) eq(cell_k, ρ)`).

What is left for `ligerito_final` (S-G2): the RS weight's extension (`weight_mle`, S-C) and the
fold rounds' binding (the D2 doom's end), which are not stated here.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## Part A: extensions of ℕ-indexed tables -/

/-- **The codeword weight's extension is the tensor weight** (A.1; `tensorTwin`, the spec of
`tensorW`): `G̃_p(ρ) = Π_v (1 − ρ_v + ρ_v Ŵ_v(D[p]))`. -/
theorem mleN_gW (κ : Kind) (i p : ℕ) (ρ : Fin (mLog κ i) → K) :
    mleN (mLog κ i) (gW κ i p) ρ =
      tensorTwin D logNMax (mLog κ i) (fun v => if h : v < mLog κ i then ρ ⟨v, h⟩ else 0) p := by
  simp only [mleN, gW]
  rw [mle_bitProd, tensorTwin, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun v _ => ?_
  simp [wAtD]

/-- **P3.i's table's extension** (A.9 `finP i`): the folded weight's plus the queried positions'
tensor weights. -/
theorem mleN_wNext (κ : Kind) (es : Log) (i : ℕ) (Wf : ℕ → K) (ρ : Fin (mLog κ i) → K) :
    mleN (mLog κ i) (wNext κ es i Wf) ρ = mleN (mLog κ i) Wf ρ +
      ∑ q ∈ range (lvl κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
        mleN (mLog κ i) (gW κ i (qPos κ es i q)) ρ := by
  have h : (fun u : Fin (2 ^ mLog κ i) => wNext κ es i Wf u) =
      (fun u : Fin (2 ^ mLog κ i) => Wf u) + fun u : Fin (2 ^ mLog κ i) =>
      ∑ q ∈ range (lvl κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
        gW κ i (qPos κ es i q) u := by
    funext u; simp only [wNext, Pi.add_apply, K.smulF_eq_mul]; rfl
  rw [mleN, h, mle_add, mle_sum]
  rfl

/-! ## Part B: the next level's table -/

/-- **Level `i + 1`'s table** (A.10 P3.i → P1.(i+1)): level `i`'s table bound at `sᵢ`, plus
the queried codeword weights, split. -/
noncomputable def nextW (κ : Kind) (es : Log) (i : ℕ) (W : ℕ → K) : ℕ → K :=
  wSplit (wNext κ es i (foldW (lvl κ i).ell (sAt es i) W))

/-- **The claim moves to the next level** (A.10 P1.i, C.i, P2.i, P3.i): if P1.i's folded claim
is `⟨foldW W, fold_z(f⁽ⁱ⁾)⟩`, the next message is the fold (`truthC`) and every query is
consistent (`truthP3`), the batched claim is `⟨nextW W, f⁽ⁱ⁺¹⁾⟩`. -/
theorem truthP1_next {κ : Kind} {L es : Log} {i : ℕ} (hi : i + 1 < 5) {W : ℕ → K} {c : K}
    (hc : c = ∑ x ∈ range (2 ^ mLog κ i), foldW (lvl κ i).ell (sAt es i) W x * foldMsg κ L es i x)
    (hC : truthC κ L es i) (h3 : truthP3 κ L es i) :
    truthP1 κ L es (i + 1) (nextW κ es i W) (vNext κ L es i c) := fun _ => by
  rw [nextW, wSplit_sum hi, vNext_eq hc hC h3]

/-- **`finPf`'s level step at the spec** (`lvStepV`): the next table's extension at
`(β, ρ)` is `û(β)·(W̃(sᵢ, ρ) + Σ_q eq(κ_c, bits₉(q))·tensorW(p_q, ρ))`. -/
theorem mleN_nextW (κ : Kind) (es : Log) (i : ℕ) (W : ℕ → K) (ρ : Fin (mLog κ i + 1) → K) :
    mleN (mLog κ i + 1) (nextW κ es i W) ρ = uHat (ρ 0) *
      (mleN ((lvl κ i).ell + mLog κ i) W (Fin.append (fun v : Fin (lvl κ i).ell => sAt es i v)
          (Fin.tail ρ)) +
        ∑ q ∈ range (lvl κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
          tensorTwin D logNMax (mLog κ i)
            (fun v => if h : v < mLog κ i then Fin.tail ρ ⟨v, h⟩ else 0) (qPos κ es i q)) := by
  rw [nextW, mleN_wSplit, mleN_wNext, mleN_foldW]
  simp only [mleN_gW]

/-! ## Part C: level 0 -/

section Level0
open Circ

/-- **The E claim's weight** over the cells (A.9 `finPf`'s `evalM(r_E2, ·)` term):
`(A + κ_E B + κ_E² C)(r_E2, y)` for the M rows' matrices. -/
noncomputable def wE (rows : List Row) (rE : Fin 21 → F) (kE : F) (y : Fin (2 ^ 23)) : F :=
  ∑ x : Fin (2 ^ 21), eq rE (cube x) * (rowMat Row.a rows 21 23 x y +
    kE * rowMat Row.b rows 21 23 x y + kE ^ 2 * rowMat Row.c rows 21 23 x y)

/-- **The E claim's inner product** (A.10 Eend): `⟨wE, f⟩ = â_M + κ_E b̂_M + κ_E² ĉ_M` with the
claims `(Mf)~(r_E2)`. -/
theorem sum_wE (rows : List Row) (rE : Fin 21 → F) (kE : F) (f : Fin (2 ^ 23) → F) :
    ∑ y, wE rows rE kE y * f y =
      mle (matVec (rowMat Row.a rows 21 23) f) rE +
        kE * mle (matVec (rowMat Row.b rows 21 23) f) rE +
        kE ^ 2 * mle (matVec (rowMat Row.c rows 21 23) f) rE := by
  simp only [mle_matVec, matMle_cube, wE, mul_sum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => by ring

/-- **The E weight's extension** at an F point (`evalM`'s spec, `finE` (iv)). -/
theorem mle_wE (rows : List Row) (rE : Fin 21 → F) (kE : F) (ρ : Fin 23 → F) :
    mle (wE rows rE kE) ρ = matMle (rowMat Row.a rows 21 23) rE ρ +
      kE * matMle (rowMat Row.b rows 21 23) rE ρ +
        kE ^ 2 * matMle (rowMat Row.c rows 21 23) rE ρ := by
  have h : wE rows rE kE = fun y => matMle (rowMat Row.a rows 21 23) rE (cube y) +
      kE * matMle (rowMat Row.b rows 21 23) rE (cube y) +
        kE ^ 2 * matMle (rowMat Row.c rows 21 23) rE (cube y) := by
    funext y; simp only [wE, matMle_cube, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [h, mle_comb, mle_matMle, mle_matMle, mle_matMle]

/-- **Level 0's claim** (A.10 B′ → P1.0): if `v_RS = ⟨Wrs, f⟩` (RS's truth) and `v*` is the B′
truth with cells inside level 0's `2^n` elements, then `v* = ⟨w0F, f⁽⁰⁾⟩`: `truthP1 0` at
`ι ∘ w0F` and `ι v*`. -/
theorem truthP1_zero {κ : Kind} {L es : Log} {Wrs : ℕ → F} {cells : List ℕ}
    {kp vRS vS : F}
    (hrs : vRS = ∑ y ∈ range (2 ^ ((lvl κ 0).ell + mLog κ 0)), Wrs y * fF κ L es y)
    (hc : ∀ c ∈ cells, c < 2 ^ ((lvl κ 0).ell + mLog κ 0))
    (hB : truthB' κ L es cells kp vRS vS) :
    truthP1 κ L es 0 (fun y => algebraMap F K (w0F Wrs cells kp y)) (algebraMap F K vS) := by
  intro hfar
  set N := 2 ^ ((lvl κ 0).ell + mLog κ 0)
  have hf : ∀ y, fTab κ L es 0 y = algebraMap F K (fF κ L es y) := fTab_F hfar
  simp only [hf, ← map_mul, ← map_sum]
  congr 1
  rw [hB, hrs]
  simp only [w0F, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
  congr 1
  rw [sum_mul_sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk' : cells.getD k 0 < N := hc _ (by
    rw [List.getD_eq_getElem _ _ (mem_range.mp hk)]; exact List.getElem_mem _)
  rw [← mul_sum]
  congr 1
  rw [sum_eq_single (cells.getD k 0) (fun y _ hy => by rw [ite_eq_right hy, zero_mul])
    (fun h => absurd (mem_range.mpr hk') h)]
  simp
where
  sum_mul_sum_comm {N : ℕ} {cs : List ℕ} {kp : F} {g : ℕ → F} :
      ∑ y ∈ range N, (∑ k ∈ range cs.length, kp ^ (k + 2) *
        (if y = cs.getD k 0 then (1 : F) else 0)) * g y =
      ∑ k ∈ range cs.length, ∑ y ∈ range N, kp ^ (k + 2) *
        ((if y = cs.getD k 0 then (1 : F) else 0) * g y) := by
    simp only [sum_mul]; rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end Level0

end FR.Snd
