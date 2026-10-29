-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `rsWeight` claim 2 at the 4.1 node layouts,
-- A.9 `finPf`'s `w0V`; track R4f). The 3.x template is `FRSoundnessFrW0V`'s spec side.
-- RET-2: import re-pointed at Core: `FRSoundnessFrW0V` → `FRSoundnessCoreRows`.
import FRSoundness4P4bB
import FRVerifierImplOps4
import FRSoundnessCoreRows
import FRSoundness4TailLig

/-!
# The RS weight's extension at revision 4.1 (`wrsL4` against `rsWeightS4`)

P4b's level-0 weight `wrsL4 kf κ es` (A.8's table `y ↦ Σ_j κ^j Φ_{r″}(eq(p_j, y)·f_j(y))`, claim 2
weighted by the kind factor `kf ν β (y / 2^7)`) is the table whose extension `finPf`'s `rsWeight`
computes. At the 4.1 kind factor `kf := N4c.kf4` this is 3.x's `rsWeight_kind_eq` (A.8's Φ form):

* **`kf4_frob`**: `kf4 ν β t^(2^k) = kf4 ν (β^(2^k)) t` (`kf4_eq`: one monomial per block);
* **`mle_kind4`**: the extension of `eq(q, ·)·kf4_γ(block)` over `7 + n` coordinates is
  `Impl.kwSL4 ν γ q ρ` (`eq` on the 7 low coordinates times `KW4.kwS4` on the block ones);
* **`termK4`**: claim 2's weight on a node, in `rsWeightS4`'s form;
* **`mleW_node4`**: the extension of `wrsL4 N4c.kf4 (.node ν) es` is `Impl.rsWeightS4 ν` at the log's
  claim points, `r″`, `κ` and L3β's `β`; **`mleW_seg4`**: a segment's (any `kf`) is 3.x's
  `rsWeightS` at `β = 1` (the segment program's `rsWeight` spec, `act = false`);
* **`wHat0_spec4`**: T4's `Ŵ₀(P₀)` (`wHatL (W₀L4 N4c.kf4 cells) … 0`) is the kind's RS weight spec
  (`rsWS4`) plus a node's public cells' sum (`mleN_w0F`'s form).

The fast path is S-T2's (`KW4.kwS4_eq`, `kwS4_fast`, `Impl.rsWeightF4_meets`): it computes
`rsWeightS4 ν`, so with these the program's `rsWeight` value is `Ŵ₀`'s RS part.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl Finset

/-! ## Claim 2's kind factor -/

/-- **The kind factor under Frobenius**: `kf4 ν β t` is the monomial `β^e`, so its `2^k`-th power is
`kf4 ν (β^(2^k)) t`. -/
theorem kf4_frob (ν : NodeKind) (β : F) (t k : ℕ) :
    algebraMap F K (N4c.kf4 ν β t) ^ 2 ^ k = algebraMap F K (N4c.kf4 ν (sqIter k β) t) := by
  rw [← map_pow, N4c.kf4_eq, N4c.kf4_eq, sqIter_eq, ← pow_mul, ← pow_mul, mul_comm]

theorem join_div7 {n : ℕ} (u₁ : Fin (2 ^ 7)) (u₂ : Fin (2 ^ n)) : (join u₁ u₂).val / 2 ^ 7 = u₂.val := by
  simp only [join]
  rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt u₁.isLt, add_zero]

/-- **The extension of `eq(q, ·)·kf4_γ(block)`** over `7 + n` coordinates (the block the high `n`
bits) is `kwSL4`: `eq` on the 7 low coordinates times `KW4.kwS4 ν n γ` on the block ones. -/
theorem mle_kind4 (ν : NodeKind) (n : ℕ) (γ : F) (q ρ : List K) (hq : q.length = 7 + n)
    (hρ : ρ.length = 7 + n) :
    mle (fun y : Fin (2 ^ (7 + n)) => eq (ptOf (7 + n) q) (cube y) *
        algebraMap F K (N4c.kf4 ν γ (y.val / 2 ^ 7))) (ptOf (7 + n) ρ) =
      Impl.kwSL4 ν γ q ρ := by
  rw [ptOfK_split (a := 7) (b := n) ρ, mle_split]
  simp only [ptOfK_split (a := 7) (b := n) q, eq_append_join, join_div7]
  have hin : ∀ u₁ : Fin (2 ^ 7), mle (fun u₂ : Fin (2 ^ n) => eq (ptOf 7 q) (cube u₁) *
      eq (ptOf n (q.drop 7)) (cube u₂) * algebraMap F K (N4c.kf4 ν γ u₂)) (ptOf n (ρ.drop 7)) =
      eq (ptOf 7 q) (cube u₁) * KW4.kwS4 ν n γ (ptOf n (q.drop 7)) (ptOf n (ρ.drop 7)) := by
    intro u₁
    simp only [mul_assoc]
    rw [mle_smul]
    refine congrArg _ (sum_congr rfl fun t _ => ?_)
    beta_reduce
    rw [K.algebraMap_eq_ofF]
    ring
  simp only [hin, ← mul_assoc, ← sum_mul]
  rw [show ∑ u : Fin (2 ^ 7), eq (ptOf 7 ρ) (cube u) * eq (ptOf 7 q) (cube u) = eq (ptOf 7 q) (ptOf 7 ρ)
    from mle_eqPt _ _]
  have ht : ∀ r : List K, r.length = 7 + n → ptOf 7 (r.take 7) = ptOf 7 r := fun r hr => by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_take, l.isLt, ite_true]
  unfold Impl.kwSL4
  rw [hρ, Nat.add_sub_cancel_left, eqPts_eq (ℓ := 7) _ _ (by simp [hq]) (by simp [hρ]), ht q hq,
    ht ρ hρ]

/-- **Claim 2's weight on a node**, in `rsWeightS4`'s form (`kwSL4` at `β^(2^k)`). -/
theorem termK4 (ν : NodeKind) (fs : List F) {n : ℕ} {p : List F} (hp : p.length = 7 + n) (β : F)
    (ρ : List K) (hρ : ρ.length = 7 + n) :
    mle (fun y : Fin (2 ^ (7 + n)) => algebraMap F K
        (Phi fs (eqPts p (bitsL (7 + n) y) * N4c.kf4 ν β (y.val / 2 ^ 7)))) (ptOf (7 + n) ρ) =
      ∑ k ∈ range (2 ^ fs.length), K.ofF ((phiTable fs).getD k 0) *
        Impl.kwSL4 ν (sqIter k β) ((p.map (algebraMap F K)).map (sqIter k)) ρ := by
  simp only [iota_Phi, map_mul, iota_eqPts_bits hp, mul_pow, eq_frob, kf4_frob]
  rw [mle_sum]
  refine sum_congr rfl fun k _ => congrArg _ ?_
  rw [ptOf_sq, mle_kind4 ν n _ _ ρ (by simp [hp]) hρ]

/-! ## The weight table's extension, claim by claim -/

section Zip
variable (r : List F) (κ' : F) (n : ℕ) (fac : ℕ → F) (w2 : ℕ → List K → K) (ρ : List K)

/-- The weight table with claim 2 weighted by `fac` (`wrsL4`'s body over a claim list). -/
noncomputable def wTab (ps : List (List F)) (i₀ : ℕ) (y : ℕ) : F :=
  ((ps.zipIdx i₀).map fun p => κ' ^ p.2 * Phi r (eqPts p.1 (bitsL p.1.length y) *
    if p.2 = 1 then fac (y / 2 ^ 7) else 1)).sum

/-- **Claim by claim**: if claim 2's term is `Σ_k c_k w2 k (p^(2^k))` (`h2`), the table's extension is
`Σ_j κ^j Σ_k c_k w_{j,k}` with `w_{1,k} = w2 k …` and the plain `eqPts` otherwise. -/
theorem mle_wTab (hr : r.length = 7)
    (h2 : ∀ p : List F, p.length = n → mle (fun y : Fin (2 ^ n) => algebraMap F K
        (Phi r (eqPts p (bitsL n y) * fac (y.val / 2 ^ 7)))) (ptOf n ρ) =
      ∑ k ∈ range 128, K.ofF ((phiTable r).getD k 0) * w2 k ((p.map (algebraMap F K)).map (sqIter k)))
    (hρ : ρ.length = n) :
    ∀ (ps : List (List F)) (i₀ : ℕ), (∀ p ∈ ps, p.length = n) →
      mle (fun y : Fin (2 ^ n) => algebraMap F K (wTab r κ' fac ps i₀ y)) (ptOf n ρ) =
        ((ps.zipIdx i₀).map fun p => K.ofF κ' ^ p.2 * ∑ k ∈ range 128,
          K.ofF ((phiTable r).getD k 0) *
            (if p.2 = 1 then w2 k ((p.1.map (algebraMap F K)).map (sqIter k))
             else eqPts ((p.1.map (algebraMap F K)).map (sqIter k)) ρ)).sum
  | [], _, _ => by simp [mle, wTab]
  | p :: ps, i₀, h => by
    have hp := h p List.mem_cons_self
    have h128 : (128 : ℕ) = 2 ^ r.length := by rw [hr]; rfl
    have ih := mle_wTab hr h2 hρ ps (i₀ + 1) fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [wTab] at ih ⊢
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, map_add, mle_add', map_mul,
      map_pow, mle_smul, hp]
    rw [ih, K.algebraMap_eq_ofF κ']
    refine congrArg (· + _) (congrArg (_ * ·) ?_)
    by_cases hi : i₀ = 1
    · simp only [hi, ↓reduceIte]
      exact h2 p hp
    · simp only [hi, ↓reduceIte, mul_one]
      rw [termP _ hp ρ hρ, ← h128]

end Zip

/-! ## `wrsL4`'s extension is the kind's `rsWeight` spec -/

theorem rsRL4_length (es : Log) : (P4b.rsRL4 es).length = 7 := by simp [P4b.rsRL4]

theorem rsPtsL4_len (κ : CKind) (es : Log) : ∀ p ∈ P4b.rsPtsL4 κ es, p.length = κ.m - 7 := by
  intro p hp
  rcases κ with σ | ν
  · simp only [P4b.rsPtsL4, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> cases σ <;>
      simp [zPtL, lcPtL, shPtL, CKind.m, SegKind.m]
  · simp only [P4b.rsPtsL4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> cases ν <;>
      simp [zPtL, lcPtL, shPtL, P4b.ePtL4, P4b.ncR, CKind.m, NodeKind.m]

/-- `wrsL4` is `wTab` over the log's claims. -/
theorem wrsL4_wTab (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) :
    P4b.wrsL4 kf κ es = wTab (P4b.rsRL4 es) (P4b.rsKL4 es) (P4b.kfT4 kf κ es) (P4b.rsPtsL4 κ es) 0 :=
  rfl

/-- The node's block bits: `ν.m − 7 = 7 + (ν.m − 14)`. -/
theorem node_m7 (ν : NodeKind) : (CKind.node ν).m - 7 = 7 + (ν.m - 14) := by
  cases ν <;> decide

/-- **The RS weight bridge at a node** (A.8's Φ form, 3.x's `mleW_spec`): the extension of P4b's
`wrsL4` at the 4.1 kind factor `N4c.kf4` is `Impl.rsWeightS4 ν` at the log's claim points, RS1's
`r″`, `κ` and L3β's `β`. -/
theorem mleW_node4 (ν : NodeKind) (es : Log) (ρ : List K) (hρ : ρ.length = (CKind.node ν).m - 7) :
    mleN ((CKind.node ν).m - 7) (fun y => algebraMap F K (P4b.wrsL4 N4c.kf4 (.node ν) es y))
        (ptOf _ ρ) =
      Impl.rsWeightS4 ν (P4b.rsRL4 es).toArray
        ((P4b.rsPtsL4 (.node ν) es).map fun p => (p.map (algebraMap F K)).toArray)
        (P4b.rsKL4 es) (fAt es 98 0) ρ.toArray := by
  unfold mleN Impl.rsWeightS4
  rw [wrsL4_wTab]
  have h := mle_wTab (P4b.rsRL4 es) (P4b.rsKL4 es) ((CKind.node ν).m - 7) (P4b.kfT4 N4c.kf4 (.node ν) es)
    (fun k q => Impl.kwSL4 ν (sqIter k (fAt es 98 0)) q ρ) ρ (rsRL4_length es) (fun p hp => by
      have hp' : p.length = 7 + (ν.m - 14) := hp.trans (node_m7 ν)
      have hρ' : ρ.length = 7 + (ν.m - 14) := hρ.trans (node_m7 ν)
      have e := termK4 ν (P4b.rsRL4 es) hp' (fAt es 98 0) ρ hρ'
      rw [rsRL4_length] at e
      revert hp hρ
      rw [node_m7 ν]
      intro _ _
      exact e) hρ (P4b.rsPtsL4 (.node ν) es) 0 (rsPtsL4_len _ es)
  rw [h, List.zipIdx_map, List.map_map]
  rfl

/-- **The RS weight bridge at a segment** (any `kf`: a segment's kind factor is `1`): 3.x's
`rsWeightS` at `β = 1`, the segment program's `rsWeight` spec (its `act` is `false`). -/
theorem mleW_seg4 (σ : SegKind) (kf : NodeKind → F → ℕ → F) (es : Log) (ρ : List K)
    (hρ : ρ.length = (CKind.seg σ).m - 7) :
    mleN ((CKind.seg σ).m - 7) (fun y => algebraMap F K (P4b.wrsL4 kf (.seg σ) es y)) (ptOf _ ρ) =
      Impl.rsWeightS (P4b.rsRL4 es).toArray
        ((P4b.rsPtsL4 (.seg σ) es).map fun p => (p.map (algebraMap F K)).toArray)
        (P4b.rsKL4 es) 1 ρ.toArray := by
  have h23 : 23 ≤ ρ.length := by rw [hρ]; cases σ <;> decide
  unfold mleN Impl.rsWeightS
  rw [wrsL4_wTab]
  have h := mle_wTab (P4b.rsRL4 es) (P4b.rsKL4 es) ((CKind.seg σ).m - 7) (P4b.kfT4 kf (.seg σ) es)
    (fun k q => kwSL (sqIter k (K.ofF 1)) q ρ) ρ (rsRL4_length es) (fun p hp => by
      have hk : ∀ t, P4b.kfT4 kf (.seg σ) es t = 1 := fun t => rfl
      simp only [hk, mul_one]
      rw [termP _ hp ρ hρ, rsRL4_length]
      refine sum_congr rfl fun k _ => ?_
      rw [show K.ofF 1 = 1 from map_one (algebraMap F K), sqIter_eq, one_pow,
        kwSL_one _ _ (by simp [hp, hρ]) h23]) hρ (P4b.rsPtsL4 (.seg σ) es) 0 (rsPtsL4_len _ es)
  rw [h, List.zipIdx_map, List.map_map]
  rfl

/-! ## T4's `Ŵ₀(P₀)` -/

/-- **The kind's RS weight spec at the log's values** (`finPf`'s `rsWeight` call: a node's
`rsWeightS4 ν` at L3β's `β`, a segment's `rsWeightS` at `β = 1`). -/
noncomputable def rsWS4 (κ : CKind) (es : Log) (ρ : List K) : K :=
  match κ with
  | .node ν => Impl.rsWeightS4 ν (P4b.rsRL4 es).toArray
      ((P4b.rsPtsL4 (.node ν) es).map fun p => (p.map (algebraMap F K)).toArray)
      (P4b.rsKL4 es) (fAt es 98 0) ρ.toArray
  | .seg σ => Impl.rsWeightS (P4b.rsRL4 es).toArray
      ((P4b.rsPtsL4 (.seg σ) es).map fun p => (p.map (algebraMap F K)).toArray)
      (P4b.rsKL4 es) 1 ρ.toArray

/-- **`wrsL4`'s extension is `rsWS4`**, every kind (at `kf := N4c.kf4`). -/
theorem mleW_spec4 (κ : CKind) (es : Log) (ρ : List K) (hρ : ρ.length = κ.m - 7) :
    mleN (κ.m - 7) (fun y => algebraMap F K (P4b.wrsL4 N4c.kf4 κ es y)) (ptOf _ ρ) = rsWS4 κ es ρ := by
  cases κ with
  | node ν => exact mleW_node4 ν es ρ hρ
  | seg σ => exact mleW_seg4 σ N4c.kf4 es ρ hρ

theorem nrP_zero4 (κ : CKind) : T4.nrP 0 κ = κ.m - 7 := by
  rcases κ with σ | ν <;> [cases σ; cases ν] <;> decide

/-- **T4's `Ŵ₀(P₀)`** (`wHatL W₀ L es 0`, `W₀ := P4b.W₀L4 N4c.kf4 cells`) is the kind's RS weight spec
at `P₀` plus the public cells' sum `Σ_k κ′^(k+2) eq(P₀, cell_k)` (none on a segment). -/
theorem wHat0_spec4 (cells : NodeKind → List ℕ) (hc : ∀ ν, ∀ c ∈ cells ν, c < 2 ^ P4b.ncR ν)
    (L es : Log) (ρ : List K) (hρ : ρ.length = (kindOfC es).m - 7)
    (hρv : ∀ v < (kindOfC es).m - 7, ρ.getD v 0 = T4.ptL es 0 v) :
    T4.wHatL (P4b.W₀L4 N4c.kf4 cells) L es 0 =
      rsWS4 (kindOfC es) es ρ + ∑ k ∈ range (P4b.cellsC cells (kindOfC es)).length,
        algebraMap F K (P4b.kpL4 es ^ (k + 2)) *
          eqCell (ptOf ((kindOfC es).m - 7) ρ) ((P4b.cellsC cells (kindOfC es)).getD k 0) := by
  rw [T4.wHatL, mleP]
  unfold P4b.W₀L4
  rw [nrP_zero4]
  have hpt : (fun v : Fin ((kindOfC es).m - 7) => T4.ptL es 0 v) = ptOf _ ρ := by
    funext v; exact (hρv v v.isLt).symm
  rw [hpt, mleN_w0F _ _ _ (P4b.cellsC_lt hc _), mleW_spec4 _ es ρ hρ]

end FR.Snd.R4
