-- lvm6 X4 (BLUEPRINT §3 step 2, X2 §1b `descend6`): the extractor's per-level descent over the one-error
-- decoder FD1 (X1), from the agreement set, against W1's descent invariant (`Lvm6WhirTuple`). New.
import Lvm6WhirTuple
import Lvm6FDCorrect
import Lvm6XFold

/-!
# The agreement-set descent over `FD1`

A level's word `Q : Wd F (2^ℓ) (m + 1)` lives on the positions `dom j = K(ptK j)` (`F` a field over
`K = BF64` with a `K`-basis `b`, the deployed `E`). One descent round has the decoded tuple `P` of the
folded word `foldQ α β Q` (W1's fold, `G + (α + β x) F`), takes `S` = the first `d + 3` positions where
`P` agrees with it, and decodes every lane of `Q` from its values on `S` with FD1, one `K`-component at a
time (`fd1F`).

* **`descend6`** (one round): if the round's challenge is outside the MCA escape (W1/M1's `IsWitness`:
  `P = U + (α + β X) V`, the halves agree with `Q` on `agree P` but at most one column), FD1 returns the
  novel-basis coefficients of the halves `joinT V U`, lane by lane. `OneErr` is derived, not assumed.
* **`descend6_inv`**: the decoded tuple `U★ = joinT V U` meets the premises of W1's invariant at `A − 1`:
  degree `≤ d`, `A − 1 ≤ |agree U★ Q|`, and `B U★` whenever `pullT … B P` (W1's pulled-back predicate);
  `descend6_viol`: hence `TViol … (A − 1) d B → W U★ ≠ σ`.
* **`witness_of_good`**: the witness exists when `(α, β) ∉ excSet` (the exceptional pairs W1's
  `card_foldEsc_le` prices).
* **`agreeS`**, **`agreeS_spec`**: the extractor's `S` (first `k + 2` agreement positions) is a valid FD1
  input whenever the agreement is at least `k + 2`.
* **`descD`**, **`descD_correct`** (a level): the rounds last to first (`stepD`), on coefficient tuples;
  under the per-round MCA conditions (`GoodL`) and `d + 3 + j ≤ a`, the output holds the coefficients of a
  tuple `T₀` of degree `≤ d` with `a − j ≤ |agree T₀ Q|`: the decoded level stack.
-/

set_option autoImplicit false

namespace Lvm6.X

open Polynomial Finset Lvm.Nb Lvm.X Lvm6.FD Lvm6.Whir LeanVM.Protocol.Whir.AffineCombiner

section

variable {F : Type} [Field F] [Algebra BF64 F] {ι : Type} [Fintype ι] (b : Module.Basis ι BF64 F)

/-! ## One lane over an extension of `K` -/

/-- A `K`-component of a codeword is the codeword of the components. -/
theorem encN_coord (i : ι) {k : ℕ} (c : Fin k → F) (j : ℕ) :
    b.coord i (encN ptK c j) = encN ptK (fun x ↦ b.coord i (c x)) j := by
  have h : ∀ (w : BF64) (z : F), z * algebraMap BF64 F w = w • z := fun w z ↦ by
    rw [Algebra.smul_def, mul_comm]
  simp only [encN, map_sum, h, LinearMap.map_smul, smul_eq_mul, Algebra.algebraMap_self_apply]
  exact Finset.sum_congr rfl fun x _ ↦ mul_comm _ _

/-- **The extractor's lane decoder over `F`**: FD1 on each `K`-component, recombined in the basis. -/
noncomputable def fd1F (N ℓ : ℕ) (S : List ℕ) (v : ℕ → F) (x : ℕ) : F :=
  ∑ i, fd1 N ℓ S (fun j ↦ b.coord i (v j)) x • b i

/-- **FD1 over `F`**: one error on `S` of an `F`-valued codeword is corrected in every component. -/
theorem fd1F_correct {N ℓ k : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) {S : List ℕ} {v : ℕ → F}
    {c : Fin k → F} (hnd : S.Nodup) (hlen : S.length = k + 2) (hS : ∀ j ∈ S, j < 2 ^ ℓ)
    (he : ∃ e, ∀ j ∈ S, j ≠ e → v j = encN ptK c j) :
    ∀ x < 2 ^ ℓ, fd1F b N ℓ S v x = if hx : x < k then c ⟨x, hx⟩ else 0 := by
  obtain ⟨e, he⟩ := he
  intro x hx
  have h1 : ∀ i, fd1 N ℓ S (fun j ↦ b.coord i (v j)) x =
      if hx : x < k then b.coord i (c ⟨x, hx⟩) else 0 := fun i ↦
    fd1_correct (c := fun x ↦ b.coord i (c x)) hN hN64 ⟨hnd, hlen, hS, e, fun j hj hje ↦ by
      show b.coord i (v j) = _
      rw [he j hj hje, encN_coord]⟩ x hx
  simp only [fd1F, h1]
  split_ifs with hk
  · simp only [Module.Basis.coord_apply]
    exact b.sum_repr _
  · simp

/-! ## Tuples as novel-basis codewords -/

/-- A polynomial of degree `≤ d < 2^ℓ` has novel-basis coefficients. -/
theorem exists_novel {ℓ d : ℕ} (hℓ : ℓ ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ) (P : F[X]) (hP : P.natDegree ≤ d) :
    ∃ c : Fin (d + 1) → F, P = ∑ x : Fin (d + 1), C (c x) * novM ptK x :=
  novel_expand (ptK_injOn hℓ) (d + 1) hd P (by
    rw [degree_lt_iff_coeff_zero]
    intro j hj
    have : d + 1 ≤ j := by exact_mod_cast hj
    exact coeff_eq_zero_of_natDegree_lt (by omega))

/-- A word on `Fin n` read at position `j : ℕ` (zero outside). -/
def wAtN {n : ℕ} (w : Fin n → F) (j : ℕ) : F := if h : j < n then w ⟨j, h⟩ else 0

variable {ℓ : ℕ} {dom : Fin (2 ^ ℓ) ↪ F}

theorem eval_dom (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) {k : ℕ} (c : Fin k → F)
    (j : Fin (2 ^ ℓ)) : (∑ x : Fin k, C (c x) * novM ptK x).eval (dom j) = encN ptK c j := by
  rw [hdom, encN_eq_eval]

/-! ## One round -/

open Classical in
/-- The witness's loss set: agreement columns of `P` where a half disagrees with `Q`. -/
noncomputable def lossSet {m : ℕ} (dom : Fin (2 ^ ℓ) ↪ F) (Q : Wd F (2 ^ ℓ) (m + 1)) (α β : F)
    (P U V : Tup F m) : Finset (Fin (2 ^ ℓ)) :=
  (agree dom P (foldQ dom α β Q)).filter fun x ↦
    ∃ r, (U r).eval (dom x) ≠ Q (Fin.cons true r) x ∨ (V r).eval (dom x) ≠ Q (Fin.cons false r) x

theorem eval_joinT_of_good {m : ℕ} {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F} {P U V : Tup F m}
    {x : Fin (2 ^ ℓ)} (hx : x ∈ agree dom P (foldQ dom α β Q)) (hb : x ∉ lossSet dom Q α β P U V) :
    ∀ v, (joinT V U v).eval (dom x) = Q v x := by
  classical
  simp only [lossSet, Finset.mem_filter, not_and, not_exists, not_or, ne_eq, not_not] at hb
  have h := hb hx
  exact forall_cube_succ.2 ⟨fun u ↦ by rw [joinT_false]; exact (h u).2,
    fun u ↦ by rw [joinT_true]; exact (h u).1⟩

/-- **One error on `S`**: off the witness's loss column, the unfolded word is the codeword of the halves. -/
theorem oneErr_of_witness (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) {d m : ℕ}
    {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F} {P U V : Tup F m}
    (hw : IsWitness dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d α β P U V)
    {S : List ℕ} (hS : ∀ j ∈ S, ∃ h : j < 2 ^ ℓ, (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom P (foldQ dom α β Q))
    (v : Fin (m + 1) → Bool) {k : ℕ} {c : Fin k → F}
    (hc : joinT V U v = ∑ x : Fin k, C (c x) * novM ptK x) :
    ∃ e, ∀ j ∈ S, j ≠ e → wAtN (Q v) j = encN ptK c j := by
  classical
  have hl : (lossSet dom Q α β P U V).card ≤ 1 := hw.2.2.2
  have tail : ∀ j (h : j < 2 ^ ℓ), (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom P (foldQ dom α β Q) →
      (⟨j, h⟩ : Fin (2 ^ ℓ)) ∉ lossSet dom Q α β P U V → wAtN (Q v) j = encN ptK c j := by
    intro j h hA hb
    rw [wAtN, dite_cond_eq_true (eq_true h), ← eval_joinT_of_good hA hb v, hc, eval_dom hdom]
  by_cases hne : (lossSet dom Q α β P U V).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨x0.val, fun j hj hje ↦ ?_⟩
    obtain ⟨h, hA⟩ := hS j hj
    exact tail j h hA fun hm ↦ hje (congrArg Fin.val (Finset.card_le_one.1 hl _ hm _ hx0))
  · refine ⟨0, fun j hj _ ↦ ?_⟩
    obtain ⟨h, hA⟩ := hS j hj
    exact tail j h hA fun hm ↦ hne ⟨_, hm⟩

/-- **`descend6`, one round**: on the first `d + 3` agreement positions of the decoded folded tuple,
FD1 returns the novel-basis coefficients of the MCA witness's halves, lane by lane. -/
theorem descend6 {N d m : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64)
    (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F}
    {P U V : Tup F m}
    (hw : IsWitness dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d α β P U V)
    {S : List ℕ} (hnd : S.Nodup) (hlen : S.length = d + 3)
    (hS : ∀ j ∈ S, ∃ h : j < 2 ^ ℓ, (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom P (foldQ dom α β Q))
    (v : Fin (m + 1) → Bool) {c : Fin (d + 1) → F}
    (hc : joinT V U v = ∑ x : Fin (d + 1), C (c x) * novM ptK x) :
    ∀ x < 2 ^ ℓ, fd1F b N ℓ S (wAtN (Q v)) x = if hx : x < d + 1 then c ⟨x, hx⟩ else 0 :=
  fd1F_correct b hN hN64 hnd (by omega) (fun j hj ↦ (hS j hj).1) (oneErr_of_witness hdom hw hS v hc)

/-- **The decoded tuple re-enters W1's invariant** one column lower: degree `≤ d`, agreement
`≥ A − 1` with the unfolded word, and the pulled-back predicate holds for it. -/
theorem descend6_inv {d m A : ℕ} {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F} {P U V : Tup F m}
    (hw : IsWitness dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d α β P U V)
    (hA : A ≤ (agree dom P (foldQ dom α β Q)).card) {B : Tup F (m + 1) → Prop} :
    DegLE d (joinT V U) ∧ A - 1 ≤ (agree dom (joinT V U) Q).card ∧
      (pullT dom Q A d α β B P → B (joinT V U)) := by
  classical
  obtain ⟨hU, hV, -, hl⟩ := hw
  have hV' : DegLE d V := fun r ↦ (hV r).trans (Nat.sub_le d 1)
  refine ⟨degLE_joinT hV' hU, ?_, fun hp ↦ hp hA _ (nearT_joinT dom ⟨hV', hU, ?_⟩)⟩
  · have hsub : agree dom P (foldQ dom α β Q) ⊆ agree dom (joinT V U) Q ∪ lossSet dom Q α β P U V := by
      intro x hx
      by_cases hb : x ∈ lossSet dom Q α β P U V
      · exact Finset.mem_union_right _ hb
      · exact Finset.mem_union_left _ ((mem_agree dom _ _ _).2 (eval_joinT_of_good hx hb))
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hl' : (lossSet dom Q α β P U V).card ≤ 1 := hl
    omega
  · refine le_trans (le_of_eq (congrArg Finset.card ?_)) hl
    ext x
    simp only [Finset.mem_filter]
    exact and_congr Iff.rfl (exists_congr fun r ↦ or_comm)

/-- **Consistency with W1's invariant**: under `TViol` at `A − 1`, the decoded tuple violates the claim. -/
theorem descend6_viol {d m A : ℕ} {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F} {P U V : Tup F m}
    (hw : IsWitness dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d α β P U V)
    (hA : A ≤ (agree dom P (foldQ dom α β Q)).card) {W : Tup F (m + 1) → F} {σ : F}
    {B : Tup F (m + 1) → Prop} (hv : TViol dom Q W σ (A - 1) d B) (hp : pullT dom Q A d α β B P) :
    W (joinT V U) ≠ σ :=
  let h := descend6_inv hw hA (B := B)
  hv _ h.1 h.2.1 (h.2.2 hp)

/-- **The witness exists** outside W1's exceptional pairs (the escape `card_foldEsc_le` prices). -/
theorem witness_of_good [Fintype F] {d A m : ℕ} {Q : Wd F (2 ^ ℓ) (m + 1)} {α β : F}
    (hg : (α, β) ∉ excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d A)
    {P : Tup F m} (hP : DegLE d P) (hA : A ≤ (agree dom P (foldQ dom α β Q)).card) :
    ∃ U V, IsWitness dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d α β P U V := by
  by_contra h
  exact hg ((mem_excSet _ _ _ _ _ _).2 ⟨P, hP, hA, h⟩)

/-! ## The agreement set -/

open Classical in
/-- **The extractor's `S`**: the first `k + 2` positions `j < 2^ℓ` where `good` holds. -/
noncomputable def agreeS (ℓ k : ℕ) (good : ℕ → Prop) : List ℕ :=
  ((List.range (2 ^ ℓ)).filter fun j ↦ decide (good j)).take (k + 2)

theorem agreeS_spec {k m : ℕ} {good : ℕ → Prop} {T : Tup F m} {w : Wd F (2 ^ ℓ) m}
    (hg : ∀ j (h : j < 2 ^ ℓ), good j ↔ (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom T w)
    (hA : k + 2 ≤ (agree dom T w).card) :
    (agreeS ℓ k good).Nodup ∧ (agreeS ℓ k good).length = k + 2 ∧
      ∀ j ∈ agreeS ℓ k good, ∃ h : j < 2 ^ ℓ, (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom T w := by
  classical
  have hmem : ∀ j, j ∈ (List.range (2 ^ ℓ)).filter (fun j ↦ decide (good j)) ↔
      ∃ h : j < 2 ^ ℓ, (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ agree dom T w := by
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (hg j h1).1 h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, (hg j h1).2 h2⟩⟩
  have hcard : (agree dom T w).card ≤ ((List.range (2 ^ ℓ)).filter (fun j ↦ decide (good j))).length := by
    rw [← Finset.card_map Fin.valEmbedding]
    refine (Finset.card_le_card fun x hx ↦ ?_).trans (List.toFinset_card_le _)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
    exact List.mem_toFinset.2 ((hmem a).2 ⟨a.2, ha⟩)
  refine ⟨((List.nodup_range).filter _).sublist (List.take_sublist _ _), ?_,
    fun j hj ↦ (hmem j).1 (List.mem_of_mem_take hj)⟩
  rw [agreeS, List.length_take]
  convert min_eq_left (hA.trans hcard)

/-! ## A level: the rounds last to first -/

/-- The word folded by the challenges `ch`, first round first (W1's `foldsQ` on the pairs `(α, β)`). -/
def foldsQX {n m : ℕ} (dom : Fin n ↪ F) : (j : ℕ) → List (F × F) → Wd F n (m + j) → Wd F n m
  | 0, _, Q => Q
  | j + 1, ch, Q => foldsQX dom j ch.tail (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q)

/-- A decoded tuple as the extractor holds it: novel-basis coefficients per lane. -/
abbrev CT (F : Type) (m : ℕ) : Type := (Fin m → Bool) → ℕ → F

/-- `Tc` holds the coefficients of `T` (degree `≤ d`). -/
def RepT {m : ℕ} (d : ℕ) (Tc : CT F m) (T : Tup F m) : Prop :=
  ∀ u, T u = ∑ x : Fin (d + 1), C (Tc u x) * novM ptK x

/-- The positions where the tuple's values (from its coefficients) agree with the word `w`. -/
def goodAt {m : ℕ} (d : ℕ) (Tc : CT F m) (w : Wd F (2 ^ ℓ) m) (j : ℕ) : Prop :=
  ∀ u, encN ptK (fun x : Fin (d + 1) ↦ Tc u x) j = wAtN (w u) j

/-- **One descent round** of the extractor: `S` = the first `d + 3` positions where the decoded tuple
agrees with the folded word, then FD1 on every lane of the unfolded word. -/
noncomputable def stepD {m : ℕ} (N d : ℕ) (dom : Fin (2 ^ ℓ) ↪ F) (Q : Wd F (2 ^ ℓ) (m + 1))
    (ch : F × F) (Tc : CT F m) : CT F (m + 1) :=
  fun v x ↦ fd1F b N ℓ (agreeS ℓ (d + 1) (goodAt d Tc (foldQ dom ch.1 ch.2 Q))) (wAtN (Q v)) x

/-- **A level's descent**: `j` rounds, the last round decoded first. -/
noncomputable def descD {m : ℕ} (N d : ℕ) (dom : Fin (2 ^ ℓ) ↪ F) :
    (j : ℕ) → List (F × F) → Wd F (2 ^ ℓ) (m + j) → CT F m → CT F (m + j)
  | 0, _, _, Tc => Tc
  | j + 1, ch, Q, Tc => stepD b N d dom Q (ch.headD (0, 0))
      (descD N d dom j ch.tail (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q) Tc)

/-- **The MCA conditions of a level** at start agreement `a`: round `s` (of `j`) is outside W1's
exceptional pairs at threshold `a − (j − 1 − s)`. -/
def GoodL [Fintype F] {m : ℕ} (d : ℕ) (dom : Fin (2 ^ ℓ) ↪ F) :
    (j : ℕ) → List (F × F) → Wd F (2 ^ ℓ) (m + j) → ℕ → Prop
  | 0, _, _, _ => True
  | j + 1, ch, Q, a =>
      GoodL d dom j ch.tail (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q) a ∧
        ch.headD (0, 0) ∉ excSet dom (fun u ↦ Q (Fin.cons true u)) (fun u ↦ Q (Fin.cons false u)) d (a - j)

/-- **`descend6` over a level**: from a tuple `T` of degree `≤ d` held as coefficients, agreeing with the
level's word folded by all `j` rounds on `a ≥ d + 3 + j` columns, and the rounds' MCA conditions, the
descent outputs the coefficients of a tuple `T₀` of degree `≤ d` agreeing with the level's committed word
on `a − j` columns. -/
theorem descD_correct [Fintype F] {m N d : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hdom : ∀ j, dom j = algebraMap BF64 F (ptK j)) :
    ∀ (j : ℕ) (ch : List (F × F)) (Q : Wd F (2 ^ ℓ) (m + j)) (a : ℕ) (Tc : CT F m)
      (T : Tup F m), d + 3 + j ≤ a → GoodL d dom j ch Q a → RepT d Tc T → DegLE d T →
      a ≤ (agree dom T (foldsQX dom j ch Q)).card →
      ∃ T₀ : Tup F (m + j), RepT d (descD b N d dom j ch Q Tc) T₀ ∧ DegLE d T₀ ∧
        a - j ≤ (agree dom T₀ Q).card
  | 0, _, _, _, _, T, _, _, hR, hT, hA => ⟨T, hR, hT, by simpa [foldsQX] using hA⟩
  | j + 1, ch, Q, a, Tc, T, hj, hG, hR, hT, hA => by
    classical
    obtain ⟨T₁, hR₁, hT₁, hA₁⟩ := descD_correct hN hN64 hd hdom j ch.tail
      (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q) a Tc T (by omega) hG.1 hR hT hA
    obtain ⟨U, V, hw⟩ := witness_of_good hG.2 hT₁ hA₁
    obtain ⟨hT₀, hA₀, -⟩ := descend6_inv hw hA₁ (B := fun _ ↦ True)
    refine ⟨joinT V U, fun v ↦ ?_, hT₀, by omega⟩
    obtain ⟨c, hc⟩ := exists_novel (by omega) hd (joinT V U v) (hT₀ v)
    obtain ⟨hnd, hlen, hS⟩ := agreeS_spec (k := d + 1)
      (good := goodAt d (descD b N d dom j ch.tail (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q) Tc)
        (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q)) (dom := dom)
      (w := foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q) (T := T₁) (fun i h ↦ by
          have hR₁' : ∀ u, T₁ u = _ := hR₁
          simp only [goodAt, mem_agree, hR₁', eval_dom hdom, wAtN, h, ↓reduceDIte]) (by omega)
    have hdec := descend6 b hN hN64 hdom hw hnd hlen hS v hc
    rw [hc]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hx := hdec x (by omega)
    simp only [x.2, ↓reduceDIte] at hx
    simp only [descD, stepD, hx]

end

end Lvm6.X
