-- New for lvm6 (WP W1, first slice). The fold round of the affine WHIR opening against the
-- agreement-set descent invariant, field-generic. Ported from leanVM `formal/lean_vm/LeanVM/Protocol/
-- Whir/Sound/{Tuple,FoldRound,FoldRoundCwyz}.lean` @ fdb317982 (Apache-2.0, see `LICENSE-leanVM`):
-- `TViol`, `foldQ`, `joinT`, `NearT`, `pullT`, `foldEsc` and `card_foldEsc_le` keep leanVM's
-- shape. Changed: the field is any finite field `F` (leanVM: its `E`), and a claim is a linear
-- functional on tuples (leanVM: `tclaim κ Φ`, a weight read through the novel basis's low part),
-- so the module needs neither the novel basis nor multiaffinity; `foldFn` is leanVM's
-- `tclaim_head`/`tclaim_joinT` taken as the definition of the folded weight.
import Lvm6Aff

/-!
# The fold round in descent form (BLUEPRINT T3, W1)

A level's word on `m` lane variables is `Q : (Fin m → Bool) → Fin n → F` over the evaluation
domain `dom : Fin n ↪ F`; a tuple is `U : (Fin m → Bool) → F[X]`; a claim is a pair `(W, σ)`,
`W` a linear functional on tuples.

* `TViol dom Q W σ a d B`: **the descent invariant** (leanVM's `TViol`, Annex B `thm:rbr`
  relativised): every tuple of degree `≤ d` agreeing with `Q` on `≥ a` columns and satisfying `B`
  violates `W U = σ`. With `B` true it is the Annex's invariant; the agreement-set extractor
  takes `B` = "the tuple's descent is bad", so `TViol` is the "`Bad = ∅`" invariant.
* `foldQ dom α β Q`: the affine fold `G + (α + β x) F` of the halves (`F` lanes with first bit
  `0`, `G` with first bit `1`), M1's `foldW`.
* `foldFn W α`: the folded weight `(1 − α) W(·, 0) + α W(0, ·)`; `foldClaim`: the verifier's next
  claim value (the Annex's form, characteristic free).
* `pullT dom Q A d α β B`: `B` pulled back through the fold (leanVM's `pullT`): if `U` agrees with
  the fold on `≥ A` columns, every near tuple (`NearT`, agreement loss one) of that agreement set
  satisfies `B`.
* **`card_foldEsc_le`**: from `TViol` at `A − 1`, at most `nAff + 2 jl n (A − 1) d |F|` pairs
  `(α, β)` break `TViol` at `A` for the fold with `pullT B` (M1's `card_foldBadR_le_nAff`).
* `tupleList`, `card_tupleList_le_jl`: the list and its Johnson count, for the level's tail.
-/

namespace Lvm6.Whir

open Finset Polynomial LeanVM.Protocol.Whir.AffineCombiner

section

variable {F : Type*} [Field F] {n m : ℕ}

/-- The tuples on `m` lane variables. -/
abbrev Tup (F : Type*) [Field F] (m : ℕ) : Type _ := (Fin m → Bool) → F[X]

/-- A word on `m` lane variables over `n` columns. -/
abbrev Wd (F : Type*) (n m : ℕ) : Type _ := (Fin m → Bool) → Fin n → F

/-! ## The invariant -/

/-- **The descent invariant**: every tuple of degree at most `d` agreeing with `Q` on at least
`a` columns and satisfying `B` violates the claim `(W, σ)`. -/
def TViol (dom : Fin n ↪ F) (Q : Wd F n m) (W : Tup F m → F) (σ : F) (a d : ℕ)
    (B : Tup F m → Prop) : Prop :=
  ∀ U : Tup F m, DegLE d U → a ≤ (agree dom U Q).card → B U → W U ≠ σ

/-- A higher threshold, a lower degree and a stronger predicate keep the invariant. -/
theorem TViol.mono {dom : Fin n ↪ F} {Q : Wd F n m} {W : Tup F m → F} {σ : F} {a a' d d' : ℕ}
    {B B' : Tup F m → Prop} (h : TViol dom Q W σ a d B) (ha : a ≤ a') (hd : d' ≤ d)
    (hB : ∀ U, B' U → B U) : TViol dom Q W σ a' d' B' :=
  fun U hU hag hb ↦ h U (fun r ↦ (hU r).trans hd) (ha.trans hag) (hB U hb)

/-! ## The fold -/

/-- **The affine fold**: lane `u` is `G_u + (α + β x) F_u`, `F_u`, `G_u` the lanes `(0, u)`, `(1, u)`. -/
def foldQ (dom : Fin n ↪ F) (α β : F) (Q : Wd F n (m + 1)) : Wd F n m :=
  fun u x ↦ Q (Fin.cons true u) x + (α + β * dom x) * Q (Fin.cons false u) x

/-- The verifier's claim after a fold round: `u₀ + α (σ − u₀) + α² w + β c₀ + α β (c₁ − c₀)`. -/
def foldClaim (σ α β u₀ w c₀ c₁ : F) : F :=
  u₀ + α * (σ - u₀) + α ^ 2 * w + β * c₀ + α * β * (c₁ - c₀)

/-- The tuple with halves `F` and `G`. -/
noncomputable def joinT (P G : Tup F m) : Tup F (m + 1) :=
  fun v ↦ if v 0 then G (Fin.tail v) else P (Fin.tail v)

@[simp] theorem joinT_false (P G : Tup F m) (u : Fin m → Bool) :
    joinT P G (Fin.cons false u) = P u := by simp [joinT]

@[simp] theorem joinT_true (P G : Tup F m) (u : Fin m → Bool) :
    joinT P G (Fin.cons true u) = G u := by simp [joinT]

theorem joinT_add (P G P' G' : Tup F m) : joinT (P + P') (G + G') = joinT P G + joinT P' G' := by
  funext v; simp only [joinT, Pi.add_apply]; split <;> rfl

theorem joinT_smul (c : F) (P G : Tup F m) : joinT (c • P) (c • G) = c • joinT P G := by
  funext v; simp only [joinT, Pi.smul_apply]; split <;> rfl

/-- The left half embedding `P ↦ (P, 0)`. -/
noncomputable def inlT : Tup F m →ₗ[F] Tup F (m + 1) where
  toFun P := joinT P 0
  map_add' P P' := by rw [← joinT_add, add_zero]
  map_smul' c P := by rw [RingHom.id_apply, ← joinT_smul, smul_zero]

/-- The right half embedding `G ↦ (0, G)`. -/
noncomputable def inrT : Tup F m →ₗ[F] Tup F (m + 1) where
  toFun G := joinT 0 G
  map_add' G G' := by rw [← joinT_add, add_zero]
  map_smul' c G := by rw [RingHom.id_apply, ← joinT_smul, smul_zero]

theorem joinT_eq (P G : Tup F m) : joinT P G = inlT P + inrT G := by
  simp only [inlT, inrT, LinearMap.coe_mk, AddHom.coe_mk, ← joinT_add, add_zero, zero_add]

/-- **The folded weight**: `(1 − α) W(·, 0) + α W(0, ·)`. -/
noncomputable def foldFn (W : Tup F (m + 1) →ₗ[F] F) (α : F) : Tup F m →ₗ[F] F :=
  (1 - α) • (W ∘ₗ inlT) + α • (W ∘ₗ inrT)

theorem foldFn_apply (W : Tup F (m + 1) →ₗ[F] F) (α : F) (P : Tup F m) :
    foldFn W α P = (1 - α) * W (inlT P) + α * W (inrT P) := by
  simp [foldFn]

/-- The weight against a joined tuple is the sum of the halves' weights. -/
theorem map_joinT (W : Tup F (m + 1) →ₗ[F] F) (P G : Tup F m) :
    W (joinT P G) = W (inlT P) + W (inrT G) := by
  rw [joinT_eq, map_add]

/-! ## Near tuples and the pull-back -/

section Near

variable (dom : Fin n ↪ F)

theorem degLE_joinT {P G : Tup F m} {d : ℕ} (hF : DegLE d P) (hG : DegLE d G) :
    DegLE d (joinT P G) := fun v ↦ by
  unfold joinT
  split
  · exact hG _
  · exact hF _

theorem forall_cube_succ {P : (Fin (m + 1) → Bool) → Prop} :
    (∀ v, P v) ↔ (∀ u, P (Fin.cons false u)) ∧ ∀ u, P (Fin.cons true u) := by
  refine ⟨fun h ↦ ⟨fun u ↦ h _, fun u ↦ h _⟩, fun h v ↦ ?_⟩
  rw [← Fin.cons_self_tail v]
  cases v 0
  · exact h.1 _
  · exact h.2 _

theorem exists_cube_succ {P : (Fin (m + 1) → Bool) → Prop} :
    (∃ v, P v) ↔ ∃ u, P (Fin.cons false u) ∨ P (Fin.cons true u) := by
  refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ hu.elim (fun h ↦ ⟨_, h⟩) fun h ↦ ⟨_, h⟩⟩
  rw [← Fin.cons_self_tail v] at hv
  cases h0 : v 0
  · exact ⟨Fin.tail v, Or.inl (by rwa [h0] at hv)⟩
  · exact ⟨Fin.tail v, Or.inr (by rwa [h0] at hv)⟩

theorem agree_joinT (P G : Tup F m) (Q : Wd F n (m + 1)) :
    agree dom (joinT P G) Q =
      agree dom P (fun u ↦ Q (Fin.cons false u)) ∩ agree dom G (fun u ↦ Q (Fin.cons true u)) := by
  ext x
  simp only [mem_agree, Finset.mem_inter]
  rw [forall_cube_succ]
  simp

open Classical in
/-- **A near tuple** of `Q` on `S`: degree at most `d`, agreeing with `Q` on all of `S` but at
most one column (the agreement loss of `thm:mca-affine`). -/
def NearT (Q : Wd F n (m + 1)) (d : ℕ) (S : Finset (Fin n)) (T : Tup F (m + 1)) : Prop :=
  DegLE d T ∧ (S.filter fun x ↦ ∃ v, (T v).eval (dom x) ≠ Q v x).card ≤ 1

/-- **The pull-back of `B` through the fold** at threshold `A`. -/
def pullT (Q : Wd F n (m + 1)) (A d : ℕ) (α β : F) (B : Tup F (m + 1) → Prop) :
    Tup F m → Prop :=
  fun U ↦ A ≤ (agree dom U (foldQ dom α β Q)).card →
    ∀ T, NearT dom Q d (agree dom U (foldQ dom α β Q)) T → B T

/-- A near pair of the halves is a near tuple. -/
theorem nearT_joinT {Q : Wd F n (m + 1)} {d : ℕ} {S : Finset (Fin n)} {P G : Tup F m}
    (h : NearPair dom (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u)) d S (P, G)) :
    NearT dom Q d S (joinT P G) := by
  classical
  obtain ⟨hF, hG, hloss⟩ := h
  refine ⟨degLE_joinT hF hG, le_trans (le_of_eq (congrArg Finset.card ?_)) hloss⟩
  ext x
  simp only [Finset.mem_filter, exists_cube_succ, joinT_false, joinT_true]

theorem foldQ_eq (α β : F) (Q : Wd F n (m + 1)) :
    foldQ dom α β Q = foldW dom (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u)) α β :=
  rfl

end Near

/-! ## The round -/

section Round

variable [Fintype F] [DecidableEq F] (dom : Fin n ↪ F)

open Classical in
/-- The pairs `(α, β)` after which the fold escapes the invariant at `(A, d)` with the pulled-back
predicate, for the round's table `u₀ w c₀ c₁`. -/
noncomputable def foldEsc (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F) (A d : ℕ)
    (B : Tup F (m + 1) → Prop) (u₀ w c₀ c₁ : F) : Finset (F × F) :=
  univ.filter fun t ↦ ¬ TViol dom (foldQ dom t.1 t.2 Q) (foldFn W t.1)
    (foldClaim σ t.1 t.2 u₀ w c₀ c₁) A d (pullT dom Q A d t.1 t.2 B)

/-- **A fold round in descent form** (Annex B `lem:fold-list` with CWYZ26's MCA, leanVM's
`card_foldEsc_le` + `foldRoundBound_of_admissible`): from the invariant at `(A − 1, d)`, every table
leaves at most `nAff + 2 jl n (A − 1) d |F|` escaping pairs `(α, β)`. -/
theorem card_foldEsc_le (Q : Wd F n (m + 1)) (W : Tup F (m + 1) →ₗ[F] F) (σ : F)
    {A d mm D Bb : ℕ} (hgap : n * d < (A - 1) * (A - 1)) (hadm : Admissible n d A mm D Bb)
    {B : Tup F (m + 1) → Prop} (hv : TViol dom Q W σ (A - 1) d B) (u₀ w c₀ c₁ : F) :
    ((foldEsc dom Q W σ A d B u₀ w c₀ c₁).card : ℚ) ≤
      nAff (Fintype.card F) n d A mm D Bb + 2 * jl n (A - 1) d * (Fintype.card F : ℚ) := by
  classical
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have h := Lvm6.Aff.card_foldBadR_le_nAff dom (fun u ↦ Q (Fin.cons false u))
    (fun u ↦ Q (Fin.cons true u)) (d := d) (A := A) (m := mm) (D := D) (B := Bb)
    (by rwa [hn]) (by rwa [hn]) (W ∘ₗ inlT) (W ∘ₗ inrT) σ (fun p ↦ B (joinT p.1 p.2))
    (fun p hp hb ↦ by
      rw [mem_pairList] at hp
      have := hv (joinT p.1 p.2) (degLE_joinT hp.1 hp.2.1) (by rw [agree_joinT]; exact hp.2.2) hb
      rwa [map_joinT] at this) u₀ w c₀ c₁
  rw [hn] at h
  refine le_trans ?_ h
  refine Nat.cast_le.mpr (Finset.card_le_card fun t ht ↦ ?_)
  rw [foldEsc, Finset.mem_filter] at ht
  simp only [TViol, not_forall, not_not, exists_prop] at ht
  obtain ⟨P, hP, hag, hpull, hc⟩ := ht.2
  rw [foldBadR, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, P, ?_, fun p hnear ↦ ?_, ?_⟩
  · rw [mem_tupleList]
    exact ⟨hP, hag⟩
  · exact hpull hag _ (nearT_joinT dom (P := p.1) (G := p.2) hnear)
  · rw [ClaimHolds, ← foldClaim, ← hc, foldFn_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply]

end Round

/-! ## Lists and the Johnson count -/

section Lists

variable [Fintype F] (dom : Fin n ↪ F)

omit [Fintype F] in
/-- Two distinct tuples of degree at most `d` agree on at most `d` common columns of a word. -/
theorem card_agree_inter_le {d : ℕ} {U V : Tup F m} (hU : DegLE d U) (hV : DegLE d V)
    (hne : U ≠ V) (Q : Wd F n m) : (agree dom U Q ∩ agree dom V Q).card ≤ d := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, U r ≠ V r := by
    by_contra h
    exact hne (funext fun r ↦ not_not.mp ((not_exists.mp h) r))
  have hD : U r - V r ≠ 0 := sub_ne_zero.mpr hr
  calc (agree dom U Q ∩ agree dom V Q).card
      ≤ (U r - V r).roots.toFinset.card :=
        Finset.card_le_card_of_injOn dom (fun x hx ↦ by
          rw [Finset.mem_coe, Finset.mem_inter, mem_agree, mem_agree] at hx
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD, IsRoot, eval_sub,
            hx.1 r, hx.2 r, sub_self]) dom.injective.injOn
    _ ≤ (U r - V r).roots.card := Multiset.toFinset_card_le _
    _ ≤ (U r - V r).natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le _ _).trans (max_le (hU r) (hV r))

/-- **The Johnson count of a list**: with `a² > n d`, at most `jl n a d` tuples. -/
theorem card_tupleList_le_jl (Q : Wd F n m) (a d : ℕ) (hgap : n * d < a * a) :
    (tupleList dom Q a d).card ≤ jl n a d := by
  classical
  have h := card_le_jl (tupleList dom Q a d) (fun U ↦ agree dom U Q) a d
    (fun U hU ↦ ((mem_tupleList dom Q a d U).mp hU).2)
    (fun U hU V hV hne ↦ card_agree_inter_le dom ((mem_tupleList dom Q a d U).mp hU).1
      ((mem_tupleList dom Q a d V).mp hV).1 hne Q) (by simpa using hgap)
  simpa using h

end Lists

end

end Lvm6.Whir
