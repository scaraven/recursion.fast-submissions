-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{Escape,Interface,Defs,GroupEscape}.lean` (formal rev
-- 0b850750) as `LvmWhirEscapeJ` for lvm2 (WP JB-L): the out-of-domain path our unique-decoding port cut (`QueryGood`,
-- `exists_agreeSet`, `card_glue_bad_le`, `claimSum_glue2`, `card_lambda_bad_le`, `eOod`, `eQuery`,
-- `escRet_sampleN_le`, `escRet_queryFrag_le`), restored against `LvmWhirEscape`/`LvmWhirInterface`/`LvmWhirDefs`/
-- `LvmWhirGroupEscape`. Changed: `escRet_queryFrag_le` takes lvm's `queryFrag per (κ + R) t c` (positions `per` per
-- challenge, commitment index `c`, side conditions `1 ≤ per`, `per·(κ + R) ≤ 192`) as `escRet_queryFrag_le_ud` does;
-- no proof-of-work discount. Statements and proofs are otherwise leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.EscapeJ

  The escapes of a WHIR level interface with an out-of-domain step, for a list of the next oracle
  with up to `listMax'` members: the out-of-domain point separates the list except with
  probability `C(L', 2)·κ/|E|`; the query positions catch the one candidate consistent with the
  out-of-domain answer except with probability `((A − 1)/n)^t`; and `λ` keeps every member
  violating the glued claim except at `(t + 1)·L'` values.
-/
import LvmWhirGroupEscape
import LvmWhirLanes
import LvmCpMultilinear

-- ===== merged from `LvmWhirOod` (GOLF module merge: `LvmWhirOod.lean` is now a stub importing `LvmWhirEscapeJ`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/Whir/Ood.lean` and the out-of-domain part of
-- `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Escape.lean` (formal rev 0b850750) as `LvmWhirOod` for lvm2 (WP JB-L).
-- Changed: one module in namespace `LeanVM.Protocol.Whir.Sound`; the helpers of the count (`evens`, `odds`,
-- `evalMle_evalMleStep`, `evalMle_succ`, `eq_of_evens_eq_of_odds_eq`, `card_affine_eq_zero_le`,
-- `card_vector_eq_pow`) live in the sub-namespace `Ood` (CompPoly's `CMlPolynomialEval.evalMle_succ` is opened);
-- VCVio's `instFintypeVector` is replaced by the local `Ood.instFintypeVector` through `Ood.vectorEquivFun`
-- (`Vector F κ ≃ (Fin κ → F)`). Statements and proofs are otherwise leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.Ood

  Out-of-domain separation: the number of points at which two distinct multilinear tables have
  the same extension, and at which some pair of a finite list collides; the out-of-domain value of
  a member of the next oracle's list, and the count of points that leave two members with equal
  values.
-/

/-!
# Out-of-domain separation

Annex B of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:ood`, in count form, for CompPoly's
hypercube tables `CMlPolynomialEval F κ` and their multilinear extension `evalMle`, evaluated at
points `z : Vector F κ`.

* `card_evalMle_eq_le`: the Schwartz-Zippel count for multilinear extensions. Two distinct
  tables on `κ` variables have the same extension at at most `κ |F|^(κ-1)` points. The proof is
  an induction on `κ` through CompPoly's recursive evaluation, which interpolates the low
  coordinate first (`Ood.evalMle_evalMleStep`): at a point whose tail separates neither half the
  extension is affine in the head and vanishes once, elsewhere it can vanish everywhere.
* `card_ood_collision_le`: for a finite set `L` of tables, at most `C(|L|, 2) κ |F|^(κ-1)` points
  `z` have two distinct members with equal extensions at `z`, a union over the `C(|L|, 2)`
  unordered pairs.
* `card_ood_collision_image_le`: the same for a list decoded injectively into tables, the form the
  round-by-round analysis consumes (distinct interleaved codewords decode to distinct tables).
* `OodSep P Q z`: the members of the list of `Q` have pairwise distinct out-of-domain values
  `oodVal z` (`claimSum (eqEval z)` of their decoded messages). `card_oodSep_bad_le`: at most
  `C(listMax, 2)·κ·|E|^(κ−1)` points `z` break it (`card_ood_collision_image_le`, with the
  injectivity of decoding `decode_injOn`, `tableOf_injective`, `joinMsg_injective`, and
  `sum_eqEval_vec`: the out-of-domain claim reads the table's extension).

Points are counted in `Vector F κ` with the finite-type instance `Ood.instFintypeVector`
(through `Vector F κ ≃ (Fin κ → F)`); `Ood.card_vector_eq_pow` gives its size `|F|^κ`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset CompPoly
  CMlPolynomialEval

section

namespace Ood

/-- Vectors of length `κ` are functions on `Fin κ`. -/
def vectorEquivFun (F : Type*) (κ : ℕ) : Vector F κ ≃ (Fin κ → F) where
  toFun v j := v[j]
  invFun f := Vector.ofFn f
  left_inv v := by ext i hi; simp
  right_inv f := by funext j; simp

/-- The points of `F^κ` as vectors form a finite type (stands in for VCVio's
`instFintypeVector`). -/
instance instFintypeVector {F : Type*} [Fintype F] (κ : ℕ) : Fintype (Vector F κ) :=
  Fintype.ofEquiv _ (vectorEquivFun F κ).symm

variable {F : Type*} [CommRing F]

/-- The even-indexed half of a table on `κ + 1` variables: its restriction to coordinate `0`
equal to `0`. -/
def evens {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) : CMlPolynomialEval F κ :=
  Vector.ofFn fun j : Fin (2 ^ κ) ↦ g.get ⟨2 * j.val, by have := j.isLt; rw [pow_succ]; omega⟩

/-- The odd-indexed half of a table on `κ + 1` variables: its restriction to coordinate `0`
equal to `1`. -/
def odds {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) : CMlPolynomialEval F κ :=
  Vector.ofFn fun j : Fin (2 ^ κ) ↦ g.get ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ]; omega⟩

/-- One interpolation step is the affine combination of the two halves' extensions. -/
theorem evalMle_evalMleStep {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) (a : F)
    (w : Vector F κ) :
    evalMle (evalMleStep g a) w = (1 - a) * evalMle (evens g) w + a * evalMle (odds g) w := by
  simp only [evalMle_eq_sum, evalMleStep, evens, odds, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  ring

/-- The extension at a point is the affine combination, at its head, of the halves' extensions at
its tail. -/
theorem evalMle_succ {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) (z : Vector F (κ + 1)) :
    evalMle g z = (1 - z.head) * evalMle (evens g) z.tail + z.head * evalMle (odds g) z.tail := by
  rw [← evalMle_evalMleStep]
  rfl

omit [CommRing F] in
/-- Two tables with the same halves are equal. -/
theorem eq_of_evens_eq_of_odds_eq {κ : ℕ} {g g' : CMlPolynomialEval F (κ + 1)}
    (he : evens g = evens g') (ho : odds g = odds g') : g = g' := by
  ext i hi
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · have hj : j < 2 ^ κ := by rw [pow_succ] at hi; (clear * - hi; omega)
    have := congrArg (·[j]) he
    simpa [evens, Vector.get_eq_getElem] using this
  · have hj : j < 2 ^ κ := by rw [pow_succ] at hi; (clear * - hi; omega)
    have := congrArg (·[j]) ho
    simpa [odds, Vector.get_eq_getElem] using this

omit [CommRing F] in
/-- There are `|F|^κ` points. -/
theorem card_vector_eq_pow [Fintype F] (κ : ℕ) :
    Fintype.card (Vector F κ) = Fintype.card F ^ κ := by
  rw [Fintype.card_congr (vectorEquivFun F κ), Fintype.card_fun, Fintype.card_fin]

/-- An affine function `A + a (B - A)` of `a` that is not identically zero vanishes at most once. -/
theorem card_affine_eq_zero_le [IsDomain F] [Fintype F] [DecidableEq F] (A B : F)
    (h : ¬ (A = 0 ∧ B = 0)) :
    (univ.filter fun a : F ↦ (1 - a) * A + a * B = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a₁ h₁ a₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  by_contra hne
  have hBA : B = A := by
    have : (a₁ - a₂) * (B - A) = 0 := by linear_combination h₁.2 - h₂.2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact sub_eq_zero.mp h
  apply h
  have hA : A = 0 := by rw [hBA] at h₁; linear_combination h₁.2
  exact ⟨hA, hBA.trans hA⟩

end Ood

open Ood

section Count

variable {F : Type*} [CommRing F] [IsDomain F] [Fintype F] [DecidableEq F]

/-- **Schwartz-Zippel for multilinear extensions.** Two distinct tables on `κ` variables have the
same multilinear extension at at most `κ |F|^(κ-1)` points. -/
theorem card_evalMle_eq_le : ∀ {κ : ℕ} {g g' : CMlPolynomialEval F κ}, g ≠ g' →
    (univ.filter fun z : Vector F κ ↦ evalMle g z = evalMle g' z).card ≤
      κ * Fintype.card F ^ (κ - 1)
  | 0, g, g', hne => by
    refine (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun z _ hz ↦ hne ?_)).le
    ext i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simpa [evalMle_zero, Vector.get_eq_getElem] using hz
  | κ + 1, g, g', hne => by
    set q := Fintype.card F
    -- The differences of the halves' extensions.
    let A : Vector F κ → F := fun w ↦ evalMle (evens g) w - evalMle (evens g') w
    let B : Vector F κ → F := fun w ↦ evalMle (odds g) w - evalMle (odds g') w
    -- The doubly degenerate tails are few, by induction on a separated half.
    have hdeg : (univ.filter fun w : Vector F κ ↦ A w = 0 ∧ B w = 0).card ≤
        κ * q ^ (κ - 1) := by
      by_cases he : evens g = evens g'
      · have ho : odds g ≠ odds g' := fun ho ↦ hne (eq_of_evens_eq_of_odds_eq he ho)
        refine (Finset.card_le_card fun w hw ↦ ?_).trans (card_evalMle_eq_le ho)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hw ⊢
        exact sub_eq_zero.mp hw.2
      · refine (Finset.card_le_card fun w hw ↦ ?_).trans (card_evalMle_eq_le he)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hw ⊢
        exact sub_eq_zero.mp hw.1
    -- Split a point into its head and tail.
    let P : F × Vector F κ → Prop := fun p ↦ (1 - p.1) * A p.2 + p.1 * B p.2 = 0
    have hsplit : (univ.filter fun z : Vector F (κ + 1) ↦ evalMle g z = evalMle g' z).card ≤
        (univ.filter P).card := by
      refine Finset.card_le_card_of_injOn (fun z ↦ (z.head, z.tail)) (fun z hz ↦ ?_)
        (fun z₁ _ z₂ _ h ↦ ?_)
      · simp only [coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
        rw [Ood.evalMle_succ, Ood.evalMle_succ] at hz
        simp only [P, A, B]
        linear_combination hz
      · simp only [Prod.mk.injEq] at h
        ext i hi
        cases i with
        | zero => simpa [Vector.head] using h.1
        | succ i =>
          have := congrArg (·[i]) h.2
          simpa [Vector.tail, Nat.add_comm] using this
    have hfiber : (univ.filter P).card =
        ∑ w : Vector F κ, (univ.filter fun a : F ↦ (1 - a) * A w + a * B w = 0).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun w _ ↦ (Finset.card_filter _ _).symm
    have hbound : ∀ w : Vector F κ,
        (univ.filter fun a : F ↦ (1 - a) * A w + a * B w = 0).card ≤
          1 + q * (if A w = 0 ∧ B w = 0 then 1 else 0) := by
      intro w
      split_ifs with h
      · exact (Finset.card_le_univ _).trans (by omega)
      · exact (card_affine_eq_zero_le _ _ h).trans (by omega)
    have hsum : ∑ w : Vector F κ, (1 + q * (if A w = 0 ∧ B w = 0 then 1 else 0)) =
        q ^ κ + q * (univ.filter fun w : Vector F κ ↦ A w = 0 ∧ B w = 0).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
      simp [card_vector_eq_pow, q]
    calc
      _ ≤ (univ.filter P).card := hsplit
      _ ≤ q ^ κ + q * (κ * q ^ (κ - 1)) := by
        rw [hfiber, ← add_le_add_iff_left 0, zero_add, zero_add]
        exact (Finset.sum_le_sum fun w _ ↦ hbound w).trans
          (hsum.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_left q hdeg) _))
      _ = (κ + 1) * q ^ (κ + 1 - 1) := by
        rcases κ with _ | κ
        · simp
        · simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- **Out-of-domain separation** (Annex B, `lem:ood`, count form). For a finite set `L` of tables
on `κ` variables, at most `C(|L|, 2) κ |F|^(κ-1)` points `z` have two distinct members whose
extensions agree at `z`. -/
theorem card_ood_collision_le {κ : ℕ} (L : Finset (CMlPolynomialEval F κ))
    [DecidablePred fun z : Vector F κ ↦ ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z] :
    (univ.filter fun z : Vector F κ ↦
        ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z).card ≤
      L.card.choose 2 * (κ * Fintype.card F ^ (κ - 1)) := by
  classical
  let bad : Finset (CMlPolynomialEval F κ) → Finset (Vector F κ) := fun P ↦
    univ.filter fun z ↦ ∀ g ∈ P, ∀ g' ∈ P, evalMle g z = evalMle g' z
  calc
    _ ≤ ((L.powersetCard 2).biUnion bad).card := by
      refine Finset.card_le_card fun z hz ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨g, hg, g', hg', hne, heq⟩ := hz
      refine Finset.mem_biUnion.mpr ⟨{g, g'}, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.insert_subset hg (Finset.singleton_subset_iff.mpr hg'),
          Finset.card_pair hne⟩
      · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        rintro a (rfl | rfl) b (rfl | rfl) <;> simp [heq]
    _ ≤ ∑ P ∈ L.powersetCard 2, (bad P).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ L.powersetCard 2, κ * Fintype.card F ^ (κ - 1) := by
      refine Finset.sum_le_sum fun P hP ↦ ?_
      obtain ⟨g, g', hne, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
      refine (Finset.card_le_card fun z hz ↦ ?_).trans (card_evalMle_eq_le hne)
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz g (by simp) g' (by simp)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

/-- **Out-of-domain separation for a decoded list.** If a finite list decodes injectively into
tables on `κ` variables, at most `C(|L|, 2) κ |F|^(κ-1)` points separate two distinct members
badly, i.e. give their decoded tables equal extensions. -/
theorem card_ood_collision_image_le {X : Type*} {κ : ℕ} (L : Finset X)
    (dec : X → CMlPolynomialEval F κ) (hinj : Set.InjOn dec L)
    [DecidablePred fun z : Vector F κ ↦
      ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ evalMle (dec U) z = evalMle (dec U') z] :
    (univ.filter fun z : Vector F κ ↦
        ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ evalMle (dec U) z = evalMle (dec U') z).card ≤
      L.card.choose 2 * (κ * Fintype.card F ^ (κ - 1)) := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  refine (Finset.card_le_card fun z hz ↦ ?_).trans (card_ood_collision_le (L.image dec))
  rw [Finset.mem_filter] at hz ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨U, hU, U', hU', hne, heq⟩ := hz.2
  exact ⟨dec U, Finset.mem_image_of_mem _ hU, dec U', Finset.mem_image_of_mem _ hU',
    fun h ↦ hne (hinj hU hU' h), heq⟩

end Count

/-! ## Out-of-domain separation of the next list -/

/-- The out-of-domain value of a decoded member: its claim against `eq_eval(z, ·)`. -/
def oodVal {m κ : ℕ} (z : List E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) : E :=
  claimSum (eqEval z) g

/-- The members of the list of `Q` have pairwise distinct out-of-domain values at `z`. -/
def OodSep (P : LevelCode) {m : ℕ} (Q : (Fin m → Bool) → Fin P.n → E) (z : List E) : Prop :=
  ∀ V ∈ iList P.code P.thr Q, ∀ V' ∈ iList P.code P.thr Q, V ≠ V' →
    oodVal z (decode P V) ≠ oodVal z (decode P V')

/-- The out-of-domain claim against a vector point reads the extension of the table. -/
theorem sum_eqEval_vec {κ : ℕ} (v : Vector E κ) (G : (Fin κ → Bool) → E) :
    ∑ p, eqEval v.toList (bitsL p) * G p = evalMle (tableOf G) v := by
  rw [evalMle_eq_sum, ← Equiv.sum_comp (bitsEquiv κ)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have ht : (tableOf G)[bitsEquiv κ p] = G p := by
    simp [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hl : (lagrangeBasis v)[bitsEquiv κ p] = eqEval v.toList (bitsL p) := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (bitsEquiv κ p).isLt,
      eqEval_bitsL v.toList (by simp)]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [bitsEquiv_val, testBit_bitsToNat]
    simp [List.getD_eq_getElem?_getD]
  rw [ht, hl, mul_comm]

/-- Decoding is injective on interleaved codewords. -/
theorem decode_injOn (P : LevelCode) {ρ : Type*} {V V' : ρ → Fin P.n → E}
    (hV : IsInterleavedCodeword P.code V) (hV' : IsInterleavedCodeword P.code V')
    (h : decode P V = decode P V') : V = V' := by
  funext u
  rw [← enc_decode P hV u, ← enc_decode P hV' u, h]

/-- The table of a message is injective in the message. -/
theorem tableOf_injective {κ : ℕ} : Function.Injective (tableOf (n := κ)) := by
  intro G G' h
  funext p
  have := congrArg (fun t : CMlPolynomialEval E κ ↦ t[bitsEquiv κ p]) h
  simpa [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply] using this

/-- Joining is injective in the split message. -/
theorem joinMsg_injective {n m κ' : ℕ} (hn : n = m + κ') :
    Function.Injective (fun g : (Fin m → Bool) → (Fin κ' → Bool) → E ↦ joinMsg hn g) := by
  subst hn
  intro g g' h
  funext u x
  have := congrFun h (Fin.append u x)
  simpa [joinMsg] using this

open Classical in
/-- **Out-of-domain separation** (Annex B, `lem:ood`): at most `C(listMax, 2)·κ·|E|^(κ−1)` points
`z` leave two members of the list of `Q` with equal out-of-domain values. -/
theorem card_oodSep_bad_le (P : LevelCode) {m κ : ℕ} (hκ : κ = m + P.κ)
    (Q : (Fin m → Bool) → Fin P.n → E) :
    (univ.filter fun v : Vector E κ ↦ ¬ OodSep P Q v.toList).card ≤
      P.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) := by
  set L := iList P.code P.thr Q
  let dec : ((Fin m → Bool) → Fin P.n → E) → CMlPolynomialEval E κ :=
    fun V ↦ tableOf (joinMsg hκ (decode P V))
  have hval : ∀ V (v : Vector E κ), oodVal v.toList (decode P V) = evalMle (dec V) v := by
    intro V v
    rw [oodVal, ← sum_joinMsg hκ, sum_eqEval_vec]
  have hinj : Set.InjOn dec L := by
    intro V hV V' hV' h
    exact decode_injOn P ((mem_iList _ _ _ _).mp hV).1 ((mem_iList _ _ _ _).mp hV').1
      (joinMsg_injective hκ (tableOf_injective h))
  refine (Finset.card_le_card fun v hv ↦ ?_).trans
    ((card_ood_collision_image_le L dec hinj).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (P.card_iList_le Q))))
  have hv' := (Finset.mem_filter.mp hv).2
  simp only [OodSep, not_forall, not_not, exists_prop] at hv'
  obtain ⟨V, hV, V', hV', hne, heq⟩ := hv'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, V, hV, V', hV', hne, by
    rw [← hval, ← hval, heq]⟩

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirOod` =====

/-!
# Escapes at the level interface with an out-of-domain step

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "OOD
challenge", "Query message" and "Batching challenge", for the deployed order of messages
(`verify_whir`, `crates/verifier/src/whir.rs:167-232` at `40f877dc`): commitment of the next
oracle `O'`, the out-of-domain point `z` and answer `y` with its intro polynomial, the query
positions, `λ`, the openings, the query intro polynomial. The level's claims are glued with powers
of `λ`: the running claim with `λ⁰`, the out-of-domain claim with `λ`, the `t` consistency claims
with `λ^(2+q)`.

* `QueryGood`: after positions `qs`, every member `V` of the next list violates the running claim,
  or the out-of-domain claim, or the consistency claim at some queried column. `exists_agreeSet`:
  under the doom before the positions and `OodSep` (`LvmWhirOod`), there is a set `A` of at most
  `thr − 1` columns such that positions breaking `QueryGood` all lie in `A`.
* `card_glue_bad_le`: a nonzero discrepancy polynomial of degree `t + 1` in `λ` has at most
  `t + 1` roots; `card_lambda_bad_le`: under `QueryGood`, at most `(t + 1)·listMax'` values `λ`
  break `Viol` for the glued claim (`claimSum_glue2`).
* `eOod P' κ = C(L', 2)·κ/|E|` and `eQuery P P' t = ((A − 1)/n)^t + (t + 1)·L'/|E|`.
* `escRet_sampleN_le`: the out-of-domain group (`sampleChallenges κ`) escapes `OodSep` with
  probability at most `eOod P' κ` (`card_oodSep_bad_le`, `retExp_sampleN`).
* `escRet_queryFrag_le`: the query group escapes the glued claim's doom with probability at most
  `eQuery P P' t` (`exists_agreeSet`, `retExp_queryFrag_le`, `card_lambda_bad_le`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The query step -/

/-- After positions `qs`, every member of the list of `Q'` violates the running claim `(Φ, σ)`,
the out-of-domain claim `(eq_eval(z, ·), y)`, or the consistency claim at a queried column of the
folded word `C`. -/
def QueryGood (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) ≠ σ ∨ oodVal z (decode P' V) ≠ y ∨
    ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- **The query step.** Under the doom before the positions (every member of the list of the
folded word `C` violates `(Φ, σ)`, and the out-of-domain values separate the list of `Q'`), the
positions breaking `QueryGood` all lie in a set of at most `thr − 1` columns. -/
theorem exists_agreeSet (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGood P P' hκ Q' C Φ σ z y qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ ∧
      oodVal z (decode P' V) = y
  · obtain ⟨V₀, hV₀, hclaim, hood⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt))
        (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGood, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨V, hV, hc, ho, hall⟩ := hqs
      have hVV : V = V₀ := by
        by_contra hne
        exact hsep V hV V₀ hV₀ hne (ho.trans hood.symm)
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    by_contra h
    simp only [not_or, not_not] at h
    exact hex ⟨V, hV, h.1, h.2.1⟩

/-! ## The batching challenge -/

/-- **The batching step.** If a member violates one of the running, out-of-domain and `t`
consistency claims, the glued claim with powers `1, λ, λ^2, …, λ^(t+1)` holds at at most `t + 1`
values `λ`. -/
theorem card_glue_bad_le {t : ℕ} (a σ b y : E) (e c : Fin t → E)
    (h : a ≠ σ ∨ b ≠ y ∨ ∃ k, e k ≠ c k) :
    (univ.filter fun lam : E ↦ a + lam * b + lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k =
        σ + lam * y + lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k).card ≤ t + 1 := by
  let d : Fin (t + 2) → E := Fin.cons (a - σ) (Fin.cons (b - y) fun k ↦ e k - c k)
  have hd : ∃ k, d k ≠ 0 := by
    rcases h with h | h | ⟨k, hk⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨1, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨k.succ.succ, by simpa [d, sub_eq_zero] using hk⟩
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_powerBatch_eq_zero_le d hd)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  have hs : ∑ k : Fin t, (e k - c k) * lam ^ ((k : ℕ) + 1 + 1) =
      lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k -
        lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

theorem claimSum_glue2 {m κ : ℕ} (Φ Ψ₁ Ψ₂ : List E → E) (a b : E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ Φ r + a * Ψ₁ r + b * Ψ₂ r) g =
      claimSum Φ g + a * claimSum Ψ₁ g + b * claimSum Ψ₂ g := by
  simp only [claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

open Classical in
/-- **The batching step of a level with a next commitment.** -/
theorem card_lambda_bad_le (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGood P P' hκ Q' C Φ σ z y qs) :
    (univ.filter fun lam : E ↦ ¬ Viol P' Q'
        (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])).card ≤
      (qs.length + 1) * P'.listMax := by
  set L := iList P'.code P'.thr Q'
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans
    ((card_filter_exists_le L (fun V lam ↦
        claimSum Φ (decode P' V) + lam * oodVal z (decode P' V) + lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k] =
        σ + lam * y + lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])
      (N := qs.length + 1) fun V hV ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Viol, not_forall, not_not,
      exists_prop] at hlam ⊢
    obtain ⟨V, hV, heq⟩ := hlam
    refine ⟨V, hV, ?_⟩
    rw [claimSum_glue2, claimSum_inducedWeight P hκ qs hqs lam] at heq
    rw [oodVal]
    simpa only [one_mul] using heq
  · refine card_glue_bad_le _ σ _ y _ _ ?_
    rcases hgood V hV with h | h | ⟨q, hq, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      exact Or.inr (Or.inr ⟨⟨k, hk⟩, hne⟩)
  · rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P'.card_iList_le Q')

/-! ## Escape bounds -/

/-- The out-of-domain escape: `C(L', 2)·κ / |E|`. -/
noncomputable def eOod (P' : LevelCode) (κ : ℕ) : ENNReal :=
  ((P'.listMax.choose 2 * κ : ℕ) : ENNReal) / Fintype.card E

/-- The query group's escape: `((A − 1)/n)^t + (t + 1)·L' / |E|`. -/
noncomputable def eQuery (P P' : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + (((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-! ## The groups -/

open Classical in
/-- **The out-of-domain group.** -/
theorem escRet_sampleN_le (P' : LevelCode) {κ ℓ' : ℕ} (hκ : κ = ℓ' + P'.κ) (hκ1 : 1 ≤ κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (J : List E → List (ℕ × ℕ × Word) → Prop)
    (h₀ : List Ev) (hJ : ∀ z : List E, z.length = κ → OodSep P' Q' z → J z (commits h₀)) :
    escRet (fun z h ↦ J z (commits h)) h₀ [] (sampleChallenges κ) ≤ eOod P' κ := by
  unfold escRet
  rw [retExp_commits (fun z cs ↦ if J z cs then 0 else 1), List.append_nil, retExp_sampleN]
  set N := (univ.filter fun v : Vector E κ ↦ ¬ OodSep P' Q' v.toList).card
  have hsum : ∑ f : Fin κ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ENNReal) ≤ N := by
    calc ∑ f : Fin κ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ENNReal)
        ≤ ∑ f : Fin κ → E, (if OodSep P' Q' (List.ofFn f) then 0 else 1 : ENNReal) := by
          gcongr with f
          by_cases hs : OodSep P' Q' (List.ofFn f)
          · simp [hs, hJ _ (List.length_ofFn) hs]
          · split_ifs <;> simp
      _ = ((univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q' (List.ofFn f)).card : ENNReal) := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun f _ ↦ by
            by_cases h : OodSep P' Q' (List.ofFn f) <;> simp [h]
      _ = N := by
          have hcard : (univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q' (List.ofFn f)).card = N := by
            refine Finset.card_bij' (fun f _ ↦ Vector.ofFn f) (fun v _ ↦ fun j : Fin κ ↦ v[j.val])
              ?_ ?_ ?_ ?_
            · intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
              rwa [Vector.toList_ofFn]
            · intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
              rwa [← Vector.toList_ofFn, Vector.ofFn_getElem]
            · intro f _; funext j; simp
            · intro v _; exact Vector.ofFn_getElem
          rw [hcard]
  have hN : (N : ENNReal) ≤ ((P'.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) : ℕ) :
      ENNReal) := by exact_mod_cast card_oodSep_bad_le P' hκ Q'
  calc (Fintype.card E : ENNReal)⁻¹ ^ κ * ∑ f : Fin κ → E, _
      ≤ (Fintype.card E : ENNReal)⁻¹ ^ κ *
        ((P'.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) : ℕ) : ENNReal) := by
        gcongr; exact hsum.trans hN
    _ = eOod P' κ := by
        obtain ⟨k, rfl⟩ : ∃ k, κ = k + 1 := ⟨κ - 1, by (clear * - κ P' ℓ' hκ hκ1; omega)⟩
        rw [eOod, ENNReal.div_eq_inv_mul, Nat.add_sub_cancel]
        push_cast
        rw [pow_succ, mul_comm ((Fintype.card E : ENNReal)⁻¹ ^ k), mul_assoc]
        have h1 : (Fintype.card E : ENNReal)⁻¹ ^ k * (Fintype.card E : ENNReal) ^ k = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
        calc (Fintype.card E : ENNReal)⁻¹ * ((Fintype.card E : ENNReal)⁻¹ ^ k *
              ((P'.listMax.choose 2 : ENNReal) * ((k + 1 : ENNReal) * (Fintype.card E) ^ k)))
            = (Fintype.card E : ENNReal)⁻¹ * ((P'.listMax.choose 2 : ENNReal) * (k + 1)) *
              ((Fintype.card E : ENNReal)⁻¹ ^ k * (Fintype.card E : ENNReal) ^ k) := by ring
          _ = _ := by rw [h1, mul_one]

open Classical in
/-- **The query group of a level with a next commitment.** -/
theorem escRet_queryFrag_le (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQuery P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet P P' hκ Q' C Φ σ z y hviol hsep
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    ((((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGood P P' hκ Q' C Φ σ z y qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le P P' hκ Q' C Φ σ z y qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ Viol P' Q'
          (fun r ↦ Φ r + 1 * lam * eqEval z r +
            1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * y + 1 * lam * lam *
            ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQuery]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

end
end LeanVM.Protocol.Whir.Sound
