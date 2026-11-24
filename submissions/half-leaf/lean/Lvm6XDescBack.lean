-- lvm6 DP6 (F-X8b-2): the opening read backwards, per level and per round, against the descent's decoder. Per
-- round, the decoded tuple *is* the backward chain's (FD1 on the first `d + 3` agreement positions recovers every
-- near tuple of that set: `descend6_near`), so the descent needs no MCA condition (`GoodL`), only W1's `ClaimBack`;
-- per level, `LvBack` exposes the start tuple's facts at every level of the ladder (`lvBack_of_open`, openBack's
-- proof). New.
import Lvm6XDesc
import Lvm6WhirBack

/-!
# The backward chain, exposed per level and per round

* **`descend6_near`** (one round): if `T` is a near tuple of `Q` on `agree P (fold Q)` (W1's `NearT`: degree `≤ d`,
  at most one column lost) and `Tc` holds `P`'s coefficients, the descent's step `stepD` holds `T`'s coefficients.
  Uniqueness per round: the decoded tuple is every such `T`, so two near tuples of one agreement set coincide
  (`nearT_unique`, by `card_agree_inter_le` through the decoder).
* **`roundsBackD`** (a level's rounds): W1's `roundsBack` with the descent: from `GoodRs` (one `ClaimBack` a round),
  a start tuple `P` held as coefficients `Tc` with the start facts, the level's decoded coefficients
  `descD … (rs.map (α, β)) Q Tc` hold a tuple `T` of degree `≤ d` with `a ≤ |agree T Q|` and `W T = σ`.
* **`StartOK`**, **`LvBack`**: per level of a ladder, the rounds' `GoodRs` and the start tuple's facts (final level:
  the final polynomial; mid level: `cand hi U` for **every** tuple `U` of the next level's list satisfying the next
  claim). **`lvBack_of_open`**: `OpenSem` gives `LvBack` (openBack's proof, per level). **`openBack_of_lvBack`**:
  `LvBack` gives openBack's first-level tuple (so `LvBack` keeps all of openBack's content).
-/

set_option autoImplicit false

namespace Lvm6.X

open Polynomial Finset Lvm.Nb Lvm.X Lvm6.FD Lvm6.Whir LeanVM.Protocol.Whir.AffineCombiner

section

variable {F : Type} [Field F] [Algebra BF64 F] {ι : Type} [Fintype ι]
  (b : Module.Basis ι BF64 F) {ℓ : ℕ} {dom : Fin (2 ^ ℓ) ↪ F}

/-- **One round, against a near tuple**: FD1 on the first `d + 3` positions where the decoded folded tuple `P`
agrees with the fold returns the coefficients of any near tuple `T` of `Q` on that agreement set. -/
theorem descend6_near {m N d : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F} {P : Tup F m}
    {Tc : CT F m} (hR : RepT d Tc P) (hA : d + 3 ≤ (agree dom P (foldQ dom α β Q)).card) {T : Tup F (m + 1)}
    (hT : NearT dom Q d (agree dom P (foldQ dom α β Q)) T) : RepT d (stepD b N d dom Q (α, β) Tc) T := by
  classical
  obtain ⟨hnd, hlen, hS⟩ := agreeS_spec (k := d + 1) (good := goodAt d Tc (foldQ dom α β Q)) (dom := dom)
    (w := foldQ dom α β Q) (T := P) (fun i h ↦ by
      have hR' : ∀ u, P u = _ := hR
      simp only [goodAt, mem_agree, hR', eval_dom hdom, wAtN, h, ↓reduceDIte]) (by omega)
  intro v
  obtain ⟨c, hc⟩ := exists_novel (by omega) hd (T v) (hT.1 v)
  have hone : ∃ e, ∀ j ∈ agreeS ℓ (d + 1) (goodAt d Tc (foldQ dom α β Q)), j ≠ e →
      wAtN (Q v) j = encN ptK c j := by
    have hl : ((agree dom P (foldQ dom α β Q)).filter fun x ↦ ∃ v, (T v).eval (dom x) ≠ Q v x).card ≤ 1 := hT.2
    have tail : ∀ j (h : j < 2 ^ ℓ), (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom P (foldQ dom α β Q) →
        (⟨j, h⟩ : Fin (2 ^ ℓ)) ∉ ((agree dom P (foldQ dom α β Q)).filter fun x ↦
          ∃ v, (T v).eval (dom x) ≠ Q v x) → wAtN (Q v) j = encN ptK c j := by
      intro j h hA hb
      have hv : (T v).eval (dom ⟨j, h⟩) = Q v ⟨j, h⟩ := by
        by_contra hne
        exact hb (Finset.mem_filter.mpr ⟨hA, v, hne⟩)
      rw [wAtN, dite_cond_eq_true (eq_true h), ← hv, hc, eval_dom hdom]
    by_cases hne : ((agree dom P (foldQ dom α β Q)).filter fun x ↦ ∃ v, (T v).eval (dom x) ≠ Q v x).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      refine ⟨x0.val, fun j hj hje ↦ ?_⟩
      obtain ⟨h, hA⟩ := hS j hj
      exact tail j h hA fun hm ↦ hje (congrArg Fin.val (Finset.card_le_one.1 hl _ hm _ hx0))
    · refine ⟨0, fun j hj _ ↦ ?_⟩
      obtain ⟨h, hA⟩ := hS j hj
      exact tail j h hA fun hm ↦ hne ⟨_, hm⟩
  have hdec := fd1F_correct b hN hN64 hnd hlen (fun j hj ↦ (hS j hj).1) hone
  rw [hc]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hx := hdec x (by omega)
  simp only [x.2, ↓reduceDIte] at hx
  simp only [stepD, hx]

include b in
/-- **Uniqueness per round**: two near tuples of `Q` on the agreement set of a tuple `P` with the fold (at least
`d + 3` columns) coincide (both are the decoder's output; `ℓ + 1 ≤ 64` for FD1). -/
theorem nearT_unique {m d : ℕ} (hℓ : ℓ + 1 ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F} {P : Tup F m}
    (hP : DegLE d P) (hA : d + 3 ≤ (agree dom P (foldQ dom α β Q)).card) {T T' : Tup F (m + 1)}
    (hT : NearT dom Q d (agree dom P (foldQ dom α β Q)) T)
    (hT' : NearT dom Q d (agree dom P (foldQ dom α β Q)) T') : T = T' := by
  obtain ⟨Tc, hR⟩ : ∃ Tc : CT F m, RepT d Tc P := by
    choose c hc using fun u ↦ exists_novel (by omega) hd (P u) (hP u)
    exact ⟨fun u x ↦ if h : x < d + 1 then c u ⟨x, h⟩ else 0, fun u ↦ by
      rw [hc u]; exact Finset.sum_congr rfl fun x _ ↦ by simp [x.2]⟩
  have h1 := descend6_near b (N := ℓ + 1) le_rfl hℓ hd hdom hR hA hT
  have h2 := descend6_near b (N := ℓ + 1) le_rfl hℓ hd hdom hR hA hT'
  funext v
  rw [h1 v, h2 v]

omit [Algebra BF64 F] in
/-- The pairs of the rounds, head first. -/
theorem headD_map_ab (rs : List (Rnd F)) :
    (rs.map fun r ↦ (r.α, r.β)).headD (0, 0) = ((rs.headD default).α, (rs.headD default).β) := by
  cases rs <;> rfl

theorem descD_succ_map {m N d j : ℕ} (rs : List (Rnd F)) (Q : Wd F (2 ^ ℓ) (m + (j + 1))) (Tc : CT F m) :
    descD b N d dom (j + 1) (rs.map fun r ↦ (r.α, r.β)) Q Tc =
      stepD b N d dom Q ((rs.headD default).α, (rs.headD default).β)
        (descD b N d dom j (rs.tail.map fun r ↦ (r.α, r.β))
          (foldQ dom (rs.headD default).α (rs.headD default).β Q) Tc) := by
  cases rs <;> rfl

/-- **A level's rounds, backwards, on the descent's decoder**: from `GoodRs` (one `ClaimBack` a round, thresholds
`≥ d + 3`) and a start tuple `P` held as coefficients `Tc` with W1's start facts, the level's decoded coefficients
hold a tuple `T` of degree `≤ d` agreeing with the level's word on `a` columns and satisfying the level's claim. -/
theorem roundsBackD [Fintype F] [DecidableEq F] {Ar : ℕ → ℕ} {N d : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) {m : ℕ} :
    ∀ (j t : ℕ) (rs : List (Rnd F)) (Q : Wd F (2 ^ ℓ) (m + j)) (W : Tup F (m + j) →ₗ[F] F) (σ : F) (a : ℕ),
    GoodRs dom Ar d j t rs Q W σ →
    (∀ s, t ≤ s → s + 1 < t + j → Ar s ≤ Ar (s + 1) - 1) →
    (0 < j → a ≤ Ar t - 1) →
    (∀ s, t ≤ s → s < t + j → d + 3 ≤ Ar s) →
    ∀ (Tc : CT F m) (P : Tup F m), RepT d Tc P → DegLE d P →
      aOut Ar a t j ≤ (agree dom P (foldsQ dom j rs Q)).card →
      foldsW j rs W P = foldsC j rs σ →
      ∃ T : Tup F (m + j), RepT d (descD b N d dom j (rs.map fun r ↦ (r.α, r.β)) Q Tc) T ∧ DegLE d T ∧
        a ≤ (agree dom T Q).card ∧ W T = σ
  | 0, _, _, _, _, _, _, _, _, _, _, Tc, P, hR, hP, hA, hW => ⟨P, hR, hP, hA, hW⟩
  | j + 1, t, rs, Q, W, σ, a, hG, hch, ha, h3, Tc, P, hR, hP, hA, hW => by
    obtain ⟨⟨-, hcb⟩, hG'⟩ := hG
    obtain ⟨T₁, hR₁, hT₁, hA₁, hW₁⟩ := roundsBackD hN hN64 hd hdom j (t + 1) rs.tail _ _ _ (Ar t) hG'
      (fun s h1 h2 ↦ hch s (by omega) (by omega)) (fun _ ↦ hch t le_rfl (by omega))
      (fun s h1 h2 ↦ h3 s (by omega) (by omega)) Tc P hR hP hA hW
    obtain ⟨T, hN', hWT⟩ := hcb T₁ hT₁ hA₁ hW₁
    have h3t := h3 t le_rfl (by omega)
    refine ⟨T, ?_, hN'.1, ?_, hWT⟩
    · rw [descD_succ_map]
      exact descend6_near b hN hN64 hd hdom hR₁ (by omega) hN'
    · have h1 := card_le_agree_of_nearT dom hN'
      have h2 := ha (Nat.succ_pos j)
      omega

end

end Lvm6.X

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.Whir
open scoped ENNReal

section Ladder

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {WI : WtIface F} {I : ChalIface F} {εmax : ℝ≥0∞}

/-- **A level's start facts** for a start tuple `P` (one lane): degree, agreement with the word folded by the level's
rounds at the level's output threshold, the folded claim. -/
def StartOK {n ℓ : ℕ} (dom : Fin n ↪ F) (d : ℕ) (Ar : ℕ → ℕ) (t₀ : ℕ) (Q : Wd F n (0 + ℓ))
    (W : Tup F (0 + ℓ) →ₗ[F] F) (σ : F) (a : ℕ) (rs : List (Rnd F)) (P : Tup F 0) : Prop :=
  DegLE d P ∧ aOut Ar a t₀ ℓ ≤ (agree dom P (foldsQ dom ℓ rs Q)).card ∧ foldsW ℓ rs W P = foldsC ℓ rs σ

/-- **The opening backwards, per level**: each level's rounds `GoodRs` and its start facts (final level: the final
polynomial; mid level: the candidate `cand hi U` of **every** tuple `U` of the next level's list satisfying the
next level's claim), the next level likewise. -/
def LvBack : {n ℓ : ℕ} → Lad F WI n ℓ → WI.Wt (0 + ℓ) → F → ℕ → List (ℕ × ℕ × Word) → Prop
  | _, ℓ, .fin V, w, σ, a, cs =>
    ∃ (rs : List (Rnd F)) (s : _),
      GoodRs V.Fv.dom (fun t ↦ (V.par t).A) V.Fv.d ℓ V.t₀ rs (V.word (cs.take (V.i + 1))) (WI.den w) σ ∧
      StartOK V.Fv.dom V.Fv.d (fun t ↦ (V.par t).A) V.t₀ (V.word (cs.take (V.i + 1))) (WI.den w) σ a rs
        (V.Fv.fpoly s)
  | _, ℓ, .mid M rest, w, σ, a, cs =>
    ∃ (rs : List (Rnd F)) (o : TailOut F M.L.ko M.L.t _),
      GoodRs M.L.dom (fun t ↦ (M.par t).A) M.L.d ℓ M.t₀ rs (M.word (cs.take (M.i + 1))) (WI.den w) σ ∧
      LvBack rest (M.wGlue (wFolds WI ℓ rs w) o) (gluedC (foldsC ℓ rs σ) o.y o.lam o.c) M.A' cs ∧
      ∀ U, DegLE rest.d U → M.A' ≤ (agree rest.dom U (rest.word (cs.take (rest.i + 1)))).card →
        WI.den (M.wGlue (wFolds WI ℓ rs w) o) U = gluedC (foldsC ℓ rs σ) o.y o.lam o.c →
        StartOK M.L.dom M.L.d (fun t ↦ (M.par t).A) M.t₀ (M.word (cs.take (M.i + 1))) (WI.den w) σ a rs
          (M.L.cand o.hi U)

/-- **`OpenSem` gives the per-level facts** (openBack's proof, without the backward composition). -/
theorem lvBack_of_open : ∀ {n ℓ : ℕ} (lad : Lad F WI n ℓ) (a : ℕ), LadOK I εmax lad a →
    ∀ (w : WI.Wt (0 + ℓ)) (σ : F) (cs : List (ℕ × ℕ × Word)) (l : List Ev), lad.WOK w →
      OpenSem WI I lad w σ a cs l → LvBack lad w σ a cs
  | _, ℓ, .fin V, a, _, w, σ, cs, l, hw, hs => by
    obtain ⟨rs, l₁, l₂, -, -, hG, s, l₃, l₄, -, -, hA, hC⟩ := hs
    have hC' := hC hw
    rw [den_wFolds] at hC'
    exact ⟨rs, s, hG, V.Fv.fdeg s, hA, hC'⟩
  | _, ℓ, .mid M rest, a, hok, w, σ, cs, l, hw, hs => by
    obtain ⟨h, hrest⟩ := hok
    obtain ⟨rs, l₁, l₂, -, -, hG, o, l₃, l₄, -, -, htf, hs'⟩ := hs
    obtain ⟨-, htb, hc⟩ := htf
    refine ⟨rs, o, hG, lvBack_of_open rest M.A' hrest _ _ cs l₄ (h.hglue w hw rs o) hs', fun U hU hUa hUw ↦ ?_⟩
    rw [h.den_wGlue w hw rs o, hc] at hUw
    have hi : rest.i + 1 = M.i + 2 := by rw [h.hi']
    rw [hi, h.hdom'] at hUa
    rw [h.hd'] at hU
    obtain ⟨hq, hA⟩ := htb U ((mem_tupleList _ _ _ _ _).mpr ⟨hU, hUa⟩) hUw
    have hq0 := congrFun hq 0
    simp only [coefQ, Fin.cons_zero, Pi.zero_apply] at hq0
    have hWc : WI.den (wFolds WI ℓ rs w) (M.L.cand o.hi U) = foldsC ℓ rs σ := by
      rw [TailIface.cand, map_add, h.hWH w hw rs o.hi, add_zero]
      exact sub_eq_zero.mp hq0
    rw [den_wFolds] at hWc
    exact ⟨M.L.cand_deg U o.hi hU, hA, hWc⟩

/-- **The per-level facts give openBack's first-level tuple** (W1's `roundsBack` per level, last level first). -/
theorem openBack_of_lvBack : ∀ {n ℓ : ℕ} (lad : Lad F WI n ℓ) (a : ℕ), LadOK I εmax lad a →
    ∀ (w : WI.Wt (0 + ℓ)) (σ : F) (cs : List (ℕ × ℕ × Word)), LvBack lad w σ a cs →
      ∃ U : Tup F (0 + ℓ), DegLE lad.d U ∧ a ≤ (agree lad.dom U (lad.word (cs.take (lad.i + 1)))).card ∧
        WI.den w U = σ
  | _, ℓ, .fin V, a, hok, w, σ, cs, hb => by
    have hok' : FinOK I εmax V a := hok
    obtain ⟨rs, s, hG, hP, hA, hC⟩ := hb
    exact roundsBack V.Fv.dom ℓ V.t₀ rs _ _ σ a hG hok'.hchain hok'.ha (V.Fv.fpoly s) hP hA hC
  | _, ℓ, .mid M rest, a, hok, w, σ, cs, hb => by
    obtain ⟨h, hrest⟩ := hok
    obtain ⟨rs, o, hG, hb', hS⟩ := hb
    obtain ⟨U, hU, hUa, hUw⟩ := openBack_of_lvBack rest M.A' hrest _ _ cs hb'
    obtain ⟨hP, hA, hC⟩ := hS U hU hUa hUw
    exact roundsBack M.L.dom ℓ M.t₀ rs _ _ σ a hG h.hchain h.ha (M.L.cand o.hi U) hP hA hC

end Ladder

end Lvm6.Whir
