-- New for lvm6 (WP RS): ring switching and the stacked-claim batch as a specification of season 1's
-- DSL. The program and claims transcribe leanVM fdb317982 `crates/verifier/src/{ring_switch,lib}.rs`
-- (`ring_switch`, step 7 of `walk`, `verify_stacked_opening`); the group escape follows leanVM's
-- `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/RingSwitch.lean` (`escRet_ring_le`, `ringSpec`).
import Lvm6RingMap
import LvmE2VSample

/-!
# Ring switching and the stacked claim (BLUEPRINT T4', `ringSpec6`)

leanVM's verifier ends its reduction phases with `ring_switch` and `verify_stacked_opening`: one
grind, sixteen challenges `f_0..f_7, g_0..g_7`, then the batching challenge `λ₀`; the 64 slice claims
of `q_keccak` become the ring claim `(eq_above · W, T)` on the stack, and the ring claim and the other
stack claims (the column claims, the OOD claim) are batched by `powers(λ₀, n)` into one stack claim
for the opening. In v6 the grind is season 1's in-challenge form: a nonce, then the first answer
carries `powOK g` in lane 2 (`e2Sample`), and the further sixteen answers are plain draws; every value
is the answer's lanes 0–1 (`e2OfE`).

* `Claim`, `Claim.Holds`, `batch`, `block`, `ringClaim`, `stackClaim`, `ringProg`: the transcriptions.
* **`card_stackBad_le`**: for one stack whose slices or claims are false, at most `(n + 1)·|E2|^16` of
  the `|E2|^17` challenge triples `(f, g, λ₀)` make the stack claim true, `n = |cs| + 1` claims
  (`2/|E2|` from `card_ringBad_le`, `(n - 1)/|E2|` from the batch polynomial).
* **`stackClaim_complete`**: honest slices and claims give a true stack claim at every challenge.
* **`ringClaim_weight_mle`**: the ring claim's weight is the multilinear extension of its cube values,
  the form the opening evaluates.
* **`ringSpec6`**: the group as a `Spec` of the DSL, from doom of "slices true, claims true, `R`" to
  doom of "stack claim true, `R`"; lead `0` (the nonce is a move), the group's escape
  `grpEpsE L₀ (|cs| + 2) g = L₀ · 2^-g · (|cs| + 2)/2^128` charged at the nonce's boundary.
-/

set_option autoImplicit false

namespace Lvm6.Ring

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound Lvm Lvm.E2V Finset
open scoped ENNReal

/-! ## Specification -/

/-- A stack claim at `E2` (`lib.rs` `StackClaim`): the weight on the stack's point, the value. -/
abbrev Claim : Type := (List E2 → E2) × E2

/-- The claim holds of a stack `q` of `M` variables: `Σ_u W(u) · q(u) = v` over the cube. -/
def Claim.Holds (M : ℕ) (c : Claim) (q : (Fin M → Bool) → K) : Prop :=
  ∑ u : Fin M → Bool, c.1 (List.ofFn (bitV u)) * ofK2 (q u) = c.2

instance (M : ℕ) (c : Claim) (q : (Fin M → Bool) → K) : Decidable (c.Holds M q) :=
  inferInstanceAs (Decidable (_ = _))

/-- `verify_stacked_opening`: weights and values combined by `powers(λ, n)`. -/
def batch (lam : E2) (cs : List Claim) : Claim :=
  (fun x ↦ dotF (powersF lam cs.length) (cs.map fun c ↦ c.1 x),
    dotF (powersF lam cs.length) (cs.map (·.2)))

/-- The block of the stack at selector bits `off` (`q_keccak`'s placement): low variables its own. -/
def block {μ a : ℕ} (off : Fin a → Bool) (q : (Fin (μ + a) → Bool) → K) : (Fin μ → Bool) → K :=
  fun u ↦ q (Fin.append u off)

/-- `lib.rs` step 7: the ring claim on the stack, `eq_above(x) · ring_weight(x[..μ])`, target
`ring_target`. -/
def ringClaim (μ : ℕ) (r sv off f g : List E2) : Claim :=
  (fun x ↦ eqEvalF off (x.drop μ) * ringWeight r (x.take μ) (ringCoefficients f g),
    ringTarget genE2 sv f g)

/-- The opening's one claim: the ring claim first, then `cs`, batched by `λ₀ = out.2.2`. -/
def stackClaim (μ : ℕ) (r sv off : List E2) (cs : List Claim) (out : List E2 × List E2 × E2) :
    Claim :=
  batch out.2.2 (ringClaim μ r sv off out.1 out.2.1 :: cs)

/-- The group: a nonce, 17 answers (`f`, `g`, `λ₀`), `powOK g` on the first. -/
def ringProg (g : ℕ) : VerifierProgram (List E2 × List E2 × E2) :=
  VerifierProgram.readScalar >>= fun _ ↦ VerifierProgram.sampleChallenges 17 >>= fun cs ↦
    VerifierProgram.require (powOK g (cs.headD 0)) >>= fun _ ↦
      pure ((cs.take 8).map e2OfE, ((cs.drop 8).take 8).map e2OfE, e2OfE (cs.getD 16 0))

/-! ## Proof helpers: claims as defects -/

/-- The defect of a claim on a stack: `Σ_u W(u) q(u) - v`. -/
def defect (M : ℕ) (c : Claim) (q : (Fin M → Bool) → K) : E2 :=
  ∑ u : Fin M → Bool, c.1 (List.ofFn (bitV u)) * ofK2 (q u) - c.2

theorem holds_iff_defect (M : ℕ) (c : Claim) (q : (Fin M → Bool) → K) :
    c.Holds M q ↔ defect M c q = 0 := by
  rw [Claim.Holds, defect, sub_eq_zero]

private theorem foldl_dot_powers (lam : E2) : ∀ (l : List E2) (acc s : E2),
    (List.zipWith (· * ·) (powersFromF acc lam l.length) l).foldl (· + ·) s =
      s + acc * polyEvalF l lam
  | [], acc, s => by simp [powersFromF, polyEvalF]
  | c :: l, acc, s => by
    rw [List.length_cons, powersFromF, List.zipWith_cons_cons, List.foldl_cons,
      foldl_dot_powers lam l, polyEvalF_cons]
    ring

/-- `dot(powers(λ, n), l) = Σ_j λ^j l_j`, Horner's form. -/
theorem dotF_powersF (lam : E2) (l : List E2) : dotF (powersF lam l.length) l = polyEvalF l lam := by
  rw [dotF, powersF, foldl_dot_powers, zero_add, one_mul]

theorem batch_fst (lam : E2) (cs : List Claim) (x : List E2) :
    (batch lam cs).1 x = polyEvalF (cs.map fun c ↦ c.1 x) lam := by
  rw [batch, ← dotF_powersF, List.length_map]

theorem batch_snd (lam : E2) (cs : List Claim) :
    (batch lam cs).2 = polyEvalF (cs.map (·.2)) lam := by
  rw [batch, ← dotF_powersF, List.length_map]

/-- **The batch's defect is the batch polynomial of the defects.** -/
theorem defect_batch (M : ℕ) (lam : E2) (cs : List Claim) (q : (Fin M → Bool) → K) :
    defect M (batch lam cs) q = polyEvalF (cs.map fun c ↦ defect M c q) lam := by
  rw [defect, batch_snd]
  simp only [batch_fst]
  induction cs with
  | nil => simp [polyEvalF]
  | cons c cs ih =>
    have e : ∀ x : Fin M → Bool,
        polyEvalF ((c :: cs).map fun c ↦ c.1 (List.ofFn (bitV x))) lam * ofK2 (q x) =
          polyEvalF (cs.map fun c ↦ c.1 (List.ofFn (bitV x))) lam * ofK2 (q x) * lam +
            c.1 (List.ofFn (bitV x)) * ofK2 (q x) := fun x ↦ by
      rw [List.map_cons, polyEvalF_cons]; ring
    rw [Finset.sum_congr rfl fun x _ ↦ e x, Finset.sum_add_distrib, ← Finset.sum_mul,
      List.map_cons, List.map_cons, polyEvalF_cons, polyEvalF_cons, ← ih, defect]
    ring

theorem polyEvalF_eq_zero_of_forall (lam : E2) :
    ∀ l : List E2, (∀ x ∈ l, x = 0) → polyEvalF l lam = 0
  | [], _ => rfl
  | c :: l, h => by
    rw [polyEvalF_cons, polyEvalF_eq_zero_of_forall lam l fun x hx ↦ h x (by simp [hx]),
      h c (by simp)]
    ring

/-- A batch polynomial with a nonzero coefficient vanishes at `|l| - 1` points at most. -/
theorem card_polyEvalF_zero_le (l : List E2) (h : ∃ x ∈ l, x ≠ 0) :
    (univ.filter fun lam : E2 ↦ polyEvalF l lam = 0).card ≤ l.length - 1 := by
  classical
  obtain ⟨x, hx, hx0⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hP : listPolyF l ≠ 0 := by
    intro h0
    have hc := congrArg (fun P : Polynomial E2 ↦ P.coeff j) h0
    simp only [listPolyF, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j (fun b _ hb ↦ if_neg (Ne.symm hb))
      (fun hj' ↦ absurd (Finset.mem_range.mpr hj) hj'), if_pos rfl,
      List.getD_eq_getElem _ _ hj] at hc
    exact hx0 hc
  have hsub : (univ.filter fun lam : E2 ↦ polyEvalF l lam = 0) ⊆ (listPolyF l).roots.toFinset := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr (by
      rw [Polynomial.IsRoot.def, eval_listPolyF]; exact hy))
  exact ((Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)).trans
    ((Polynomial.card_roots' _).trans (natDegree_listPolyF l))

/-! ## Proof helpers: the ring claim on the stack -/

section Split

variable {μ a : ℕ}

theorem ofFn_split {α : Type} (y : Fin (μ + a) → α) :
    List.ofFn y = List.ofFn (fun i ↦ y (Fin.castAdd a i)) ++ List.ofFn (fun j ↦ y (Fin.natAdd μ j)) :=
  List.ofFn_add

theorem take_ofFn_split {α : Type} (y : Fin (μ + a) → α) :
    (List.ofFn y).take μ = List.ofFn (fun i ↦ y (Fin.castAdd a i)) := by
  rw [ofFn_split, List.take_left' (by simp)]

theorem drop_ofFn_split {α : Type} (y : Fin (μ + a) → α) :
    (List.ofFn y).drop μ = List.ofFn (fun j ↦ y (Fin.natAdd μ j)) := by
  rw [ofFn_split, List.drop_left' (by simp)]

theorem eqP_split (y z : Fin (μ + a) → E2) :
    eqP y z = eqP (fun i ↦ y (Fin.castAdd a i)) (fun i ↦ z (Fin.castAdd a i)) *
      eqP (fun j ↦ y (Fin.natAdd μ j)) (fun j ↦ z (Fin.natAdd μ j)) := by
  rw [eqP, eqP, eqP, Fin.prod_univ_add]

/-- `eq` at two cube points is the indicator of their equality. -/
theorem eqP_bitV {n : ℕ} (u w : Fin n → Bool) :
    eqP (bitV u : Fin n → E2) (bitV w) = if u = w then 1 else 0 := by
  have h2 : (2 : E2) = 0 := CharTwo.two_eq_zero
  split_ifs with h
  · subst h
    refine Finset.prod_eq_one fun i _ ↦ ?_
    simp only [bitV]
    split_ifs
    · linear_combination h2
    · simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp only [bitV]
    cases hu : u i <;> cases hw : w i <;> simp_all <;> linear_combination h2

/-- A sum over the cube of `μ + a` variables, by its low and high halves. -/
theorem sum_cube_split {M : Type} [AddCommMonoid M] (G : (Fin (μ + a) → Bool) → M) :
    ∑ u, G u = ∑ v : Fin μ → Bool, ∑ w : Fin a → Bool, G (Fin.append v w) := by
  rw [← (Fin.appendEquiv μ a).sum_comp, Fintype.sum_prod_type]
  rfl

theorem bitV_append_castAdd (v : Fin μ → Bool) (w : Fin a → Bool) :
    (fun i ↦ (bitV (Fin.append v w) : Fin (μ + a) → E2) (Fin.castAdd a i)) = bitV v := by
  funext i; simp [bitV]

theorem bitV_append_natAdd (v : Fin μ → Bool) (w : Fin a → Bool) :
    (fun j ↦ (bitV (Fin.append v w) : Fin (μ + a) → E2) (Fin.natAdd μ j)) = bitV w := by
  funext j; simp [bitV]

/-- The ring claim's weight at a cube point: the selector times `Φ(eq(r, low))`. -/
theorem ringClaim_cube (r : Fin μ → E2) (sv : List E2) (off : Fin a → Bool) (f g : Fin 8 → E2)
    (v : Fin μ → Bool) (w : Fin a → Bool) :
    (ringClaim μ (List.ofFn r) sv (List.ofFn (bitV off)) (List.ofFn f) (List.ofFn g)).1
        (List.ofFn (bitV (Fin.append v w))) =
      (if off = w then 1 else 0) * frobPhi 8 f g (eqP r (bitV v)) := by
  simp only [ringClaim]
  rw [take_ofFn_split, drop_ofFn_split, bitV_append_castAdd, bitV_append_natAdd, eqEvalF_ofFn,
    eqP_bitV, ringWeight_ofFn, frobPhi_eqP]

/-- **The ring claim paired with a stack** is `Σ_v Φ(eq(r, v)) q_block(v)`. -/
theorem pair_ringClaim (r : Fin μ → E2) (sv : List E2) (off : Fin a → Bool) (f g : Fin 8 → E2)
    (q : (Fin (μ + a) → Bool) → K) :
    ∑ u : Fin (μ + a) → Bool,
        (ringClaim μ (List.ofFn r) sv (List.ofFn (bitV off)) (List.ofFn f) (List.ofFn g)).1
          (List.ofFn (bitV u)) * ofK2 (q u) =
      ∑ v : Fin μ → Bool, frobPhi 8 f g (eqP r (bitV v)) * ofK2 (block off q v) := by
  rw [sum_cube_split]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [ringClaim_cube, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [block]

/-- The ring claim's defect: the honest value minus the target. -/
theorem defect_ringClaim (r : Fin μ → E2) (sv : Fin 64 → E2) (off : Fin a → Bool)
    (f g : Fin 8 → E2) (q : (Fin (μ + a) → Bool) → K) :
    defect (μ + a) (ringClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) (List.ofFn f)
        (List.ofFn g)) q =
      ∑ i : Fin 64, ringW i * frobPhi 8 f g (sliceExt (block off q) r i) -
        ringTarget genE2 (List.ofFn sv) (List.ofFn f) (List.ofFn g) := by
  rw [defect, pair_ringClaim, ring_complete]
  rfl

end Split

/-! ## Load-bearing lemmas -/

/-- **Completeness**: honest slices and claims give a true stack claim at every challenge. -/
theorem stackClaim_complete {μ a : ℕ} (r : Fin μ → E2) (sv : Fin 64 → E2) (off : Fin a → Bool)
    (cs : List Claim) (q : (Fin (μ + a) → Bool) → K) (hs : ∀ i, sliceExt (block off q) r i = sv i)
    (hc : ∀ c ∈ cs, c.Holds (μ + a) q) (f g : Fin 8 → E2) (lam : E2) :
    (stackClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) cs
      (List.ofFn f, List.ofFn g, lam)).Holds (μ + a) q := by
  rw [holds_iff_defect, stackClaim, defect_batch]
  refine polyEvalF_eq_zero_of_forall lam _ fun x hx ↦ ?_
  simp only [List.map_cons, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨c, hc', rfl⟩
  · rw [defect_ringClaim, ringTarget_eq, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hs i]
  · exact (holds_iff_defect _ _ _).mp (hc c hc')

/-- **The opening's evaluation of the ring claim's weight** is the multilinear extension of its cube
values. -/
theorem ringClaim_weight_mle {μ a : ℕ} (r : Fin μ → E2) (sv : List E2) (off : Fin a → Bool)
    (f g : Fin 8 → E2) (x : Fin (μ + a) → E2) :
    (ringClaim μ (List.ofFn r) sv (List.ofFn (bitV off)) (List.ofFn f) (List.ofFn g)).1 (List.ofFn x) =
      ∑ u : Fin (μ + a) → Bool, (ringClaim μ (List.ofFn r) sv (List.ofFn (bitV off)) (List.ofFn f)
        (List.ofFn g)).1 (List.ofFn (bitV u)) * eqP (bitV u) x := by
  rw [sum_cube_split]
  simp only [ringClaim_cube, eqP_split (bitV _) x, bitV_append_castAdd, bitV_append_natAdd]
  have hsel : ∀ v : Fin μ → Bool, ∑ w : Fin a → Bool,
      (if off = w then (1 : E2) else 0) * frobPhi 8 f g (eqP r (bitV v)) *
        (eqP (bitV v) (fun i ↦ x (Fin.castAdd a i)) * eqP (bitV w) (fun j ↦ x (Fin.natAdd μ j))) =
      eqP (bitV off) (fun j ↦ x (Fin.natAdd μ j)) *
        (frobPhi 8 f g (eqP r (bitV v)) * eqP (bitV v) (fun i ↦ x (Fin.castAdd a i))) := by
    intro v
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  rw [Finset.sum_congr rfl fun v _ ↦ hsel v, ← Finset.mul_sum, ringWeight_mle]
  simp only [ringClaim]
  rw [take_ofFn_split, drop_ofFn_split, eqEvalF_ofFn]


/-- A claim's weight is the multilinear extension of its cube values (what the opening evaluates
at its point). -/
def Claim.Mle (M : ℕ) (c : Claim) : Prop :=
  ∀ x : Fin M → E2, c.1 (List.ofFn x) = ∑ u : Fin M → Bool, c.1 (List.ofFn (bitV u)) * eqP (bitV u) x

/-- **The batch keeps multilinear weights.** -/
theorem mle_batch (M : ℕ) (lam : E2) : ∀ cs : List Claim, (∀ c ∈ cs, c.Mle M) →
    (batch lam cs).Mle M
  | [], _ => fun x ↦ by simp [batch_fst, polyEvalF]
  | c :: cs, h => fun x ↦ by
    have ih := mle_batch M lam cs (fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')) x
    have hc := h c List.mem_cons_self x
    simp only [batch_fst] at ih ⊢
    simp only [List.map_cons, polyEvalF_cons]
    rw [ih, hc, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [add_mul, mul_right_comm]

/-- The ring claim's weight is multilinear (`ringClaim_weight_mle`), so the stack claim's is too
when the claims `cs` are. -/
theorem mle_stackClaim {μ a : ℕ} (r : Fin μ → E2) (sv : Fin 64 → E2) (off : Fin a → Bool)
    (cs : List Claim) (hcs : ∀ c ∈ cs, c.Mle (μ + a)) (f g : Fin 8 → E2) (lam : E2) :
    (stackClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) cs
      (List.ofFn f, List.ofFn g, lam)).Mle (μ + a) := by
  refine mle_batch _ lam _ fun c hc ↦ ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · exact fun x ↦ ringClaim_weight_mle r _ off f g x
  · exact hcs c hc

/-- The challenges of a product, split by the first coordinate. -/
private theorem card_filter_prod_fst {α γ : Type} [Fintype α] [Fintype γ] (P : α × γ → Prop)
    [DecidablePred P] :
    (univ.filter P).card = ∑ x : α, (univ.filter fun y : γ ↦ P (x, y)).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.card_filter]

/-- **The field-level count behind `ringSpec6`**: for a stack whose slices or claims are false, at
most `(|cs| + 2)·|E2|^16` of the challenge triples `(f, g, λ₀)` make the stack claim true. -/
theorem card_stackBad_le {μ a : ℕ} (r : Fin μ → E2) (sv : Fin 64 → E2) (off : Fin a → Bool)
    (cs : List Claim) (q : (Fin (μ + a) → Bool) → K)
    (h : ¬ ((∀ i, sliceExt (block off q) r i = sv i) ∧ ∀ c ∈ cs, c.Holds (μ + a) q)) :
    (Finset.univ.filter fun v : (Fin 8 → E2) × (Fin 8 → E2) × E2 ↦
      (stackClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) cs
        (List.ofFn v.1, List.ofFn v.2.1, v.2.2)).Holds (μ + a) q).card ≤
      (cs.length + 2) * (2 ^ 128) ^ 16 := by
  classical
  let z : Fin 64 → E2 := fun i ↦ sliceExt (block off q) r i
  let Dr : (Fin 8 → E2) × (Fin 8 → E2) → E2 := fun fg ↦ defect (μ + a)
    (ringClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) (List.ofFn fg.1)
      (List.ofFn fg.2)) q
  let csD : List E2 := cs.map fun c ↦ defect (μ + a) c q
  let P : (Fin 8 → E2) × (Fin 8 → E2) → E2 → Prop := fun fg lam ↦ polyEvalF (Dr fg :: csD) lam = 0
  have hcard : (Finset.univ.filter fun v : (Fin 8 → E2) × (Fin 8 → E2) × E2 ↦
      (stackClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) cs
        (List.ofFn v.1, List.ofFn v.2.1, v.2.2)).Holds (μ + a) q).card =
      (univ.filter fun w : ((Fin 8 → E2) × (Fin 8 → E2)) × E2 ↦ P w.1 w.2).card := by
    refine Finset.card_equiv (Equiv.prodAssoc _ _ _).symm fun v ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, holds_iff_defect, stackClaim,
      defect_batch]
    rfl
  rw [hcard, card_filter_prod_fst]
  have hE : Fintype.card E2 = 2 ^ 128 := card_E2
  have hfg : ∀ fg, (univ.filter fun lam ↦ P fg lam).card ≤
      cs.length + (if Dr fg = 0 ∧ ∀ x ∈ csD, x = 0 then 2 ^ 128 else 0) := by
    intro fg
    split_ifs with h0
    · exact (Finset.card_le_univ _).trans (by rw [hE]; omega)
    · have hex : ∃ x ∈ Dr fg :: csD, x ≠ 0 := by
        by_contra hall
        simp only [not_exists, not_and, not_not] at hall
        exact h0 ⟨hall _ List.mem_cons_self, fun x hx ↦ hall x (List.mem_cons_of_mem _ hx)⟩
      have := card_polyEvalF_zero_le _ hex
      simp only [List.length_cons, csD, List.length_map, Nat.add_sub_cancel] at this
      omega
  have hbad : (univ.filter fun fg ↦ Dr fg = 0 ∧ ∀ x ∈ csD, x = 0).card ≤ 2 * (2 ^ 128) ^ 15 := by
    by_cases hz : z = sv
    · have hcs : ¬ ∀ x ∈ csD, x = 0 := by
        intro hall
        refine h ⟨fun i ↦ congrFun hz i, fun c hc ↦ (holds_iff_defect _ _ _).mpr
          (hall _ (List.mem_map_of_mem hc))⟩
      simp [hcs]
    · refine (Finset.card_le_card fun fg hfg ↦ ?_).trans (card_ringBad_le (Ne.symm hz))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfg ⊢
      have h1 := hfg.1
      simp only [Dr, defect_ringClaim] at h1
      exact (sub_eq_zero.mp h1).symm
  have huniv : Fintype.card ((Fin 8 → E2) × (Fin 8 → E2)) = (2 ^ 128) ^ 16 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hE, ← pow_add]
  calc ∑ fg, (univ.filter fun lam ↦ P fg lam).card
      ≤ ∑ fg, (cs.length + if Dr fg = 0 ∧ ∀ x ∈ csD, x = 0 then 2 ^ 128 else 0) :=
        Finset.sum_le_sum fun fg _ ↦ hfg fg
    _ = (2 ^ 128) ^ 16 * cs.length +
          (univ.filter fun fg ↦ Dr fg = 0 ∧ ∀ x ∈ csD, x = 0).card * 2 ^ 128 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, huniv, smul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    _ ≤ (2 ^ 128) ^ 16 * cs.length + 2 * (2 ^ 128) ^ 15 * 2 ^ 128 :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hbad) _
    _ = (cs.length + 2) * (2 ^ 128) ^ 16 := by ring

/-! ## The group in the DSL -/

section Dsl

variable {β : Type}

/-- A doom postcondition read at the base history: along a run with no commitment the candidates
do not change (`Stable`). -/
theorem escRet_doomed_stable {α : Type} {C : List Ev → Set β} (hst : Stable C)
    (A' : α → β → Prop) (h₀ : List Ev) :
    ∀ (p : VerifierProgram α) (l : List Ev), commits l = [] →
      VerifierProgram.escRet (fun x h ↦ Doomed C (A' x) h) h₀ l p = VerifierProgram.escRet (fun x _ ↦ Doomed C (A' x) h₀) h₀ l p
  | .ret x, l, hl => by
    simp only [VerifierProgram.escRet, VerifierProgram.retExp]
    have hd := Doomed.append (A := A' x) hst (h₀ := h₀) hl
    by_cases h1 : Doomed C (A' x) h₀
    · simp only [hd.mpr h1, h1, ↓reduceIte]
    · have h2 : ¬ Doomed C (A' x) (h₀ ++ l) := fun h ↦ h1 (hd.mp h)
      simp only [h1, h2, ↓reduceIte]
  | .fail, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .read _, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .grind _ _, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .commit _ _ _, _, _ => by simp [VerifierProgram.escRet, VerifierProgram.retExp]
  | .sample k, l, hl => by
    simp only [VerifierProgram.escRet, VerifierProgram.retExp]
    congr 1
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    exact escRet_doomed_stable hst A' h₀ (k c) _ (by rw [commits_append_sample, hl])
  | .query i ps k, l, hl => by
    simp only [VerifierProgram.escRet, VerifierProgram.retExp]
    split
    · exact escRet_doomed_stable hst A' h₀ _ _ (by rw [commits_append_query, hl])
    · rfl

/-- The 17 answers as `E2` challenges `(f, g, λ₀)`. -/
def outOf (c : Fin 17 → E) : (Fin 8 → E2) × (Fin 8 → E2) × E2 :=
  (fun i ↦ e2OfE (c ⟨i, by omega⟩), fun j ↦ e2OfE (c ⟨8 + j, by omega⟩), e2OfE (c 16))

theorem ringOut_ofFn (c : Fin 17 → E) :
    ((((List.ofFn c).take 8).map e2OfE, (((List.ofFn c).drop 8).take 8).map e2OfE,
        e2OfE ((List.ofFn c).getD 16 0)) : List E2 × List E2 × E2) =
      (List.ofFn (outOf c).1, List.ofFn (outOf c).2.1, (outOf c).2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [outOf]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [outOf]
  · simp [outOf]

/-- **The product-set count of the group**: the accepted answer lists whose challenges lie in `B`
are at most `2^(64-g) · |K|^16 · |B|`. -/
theorem card_powOK_outOf_le {g : ℕ} (hg : g ≤ 64)
    (B : (Fin 8 → E2) × (Fin 8 → E2) × E2 → Prop) [DecidablePred B] :
    (univ.filter fun c : Fin 17 → E ↦ powOK g (c 0) ∧ B (outOf c)).card ≤
      2 ^ (64 - g) * (2 ^ 64) ^ 16 * (univ.filter B).card := by
  classical
  let Ψ : (Fin 17 → E2) → (Fin 8 → E2) × (Fin 8 → E2) × E2 := fun y ↦
    (fun i ↦ y ⟨i, by omega⟩, fun j ↦ y ⟨8 + j, by omega⟩, y 16)
  let Y := univ.filter fun y : Fin 17 → E2 ↦ B (Ψ y)
  let Ks := univ.filter fun k : Fin 17 → K ↦ kToNat (k 0) < 2 ^ (64 - g)
  have h1 : (univ.filter fun c : Fin 17 → E ↦ powOK g (c 0) ∧ B (outOf c)).card ≤ (Y ×ˢ Ks).card := by
    refine Finset.card_le_card_of_injOn (fun c ↦ (fun i ↦ e2OfE (c i), fun i ↦ (c i).limb 2))
      (fun c hc ↦ ?_) (fun c _ c' _ he ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Y, Ks]
      exact ⟨hc.2, (powOK_iff_lane2 hg _).mp hc.1⟩
    · funext i
      have e1 := congrFun (congrArg Prod.fst he) i
      have e2 := congrFun (congrArg Prod.snd he) i
      exact eSplit.injective (Prod.ext e1 e2)
  have hY : Y.card ≤ (univ.filter B).card := by
    refine Finset.card_le_card_of_injOn Ψ (fun y hy ↦ ?_) (fun y _ y' _ he ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Y] at hy ⊢
      exact hy
    · funext t
      have e1 := congrArg Prod.fst he
      have e2 := congrArg (fun p ↦ p.2.1) he
      have e3 := congrArg (fun p ↦ p.2.2) he
      simp only [Ψ] at e1 e2 e3
      by_cases ht : t.val < 8
      · exact congrFun e1 ⟨t.val, ht⟩
      · by_cases ht' : t.val < 16
        · have := congrFun e2 ⟨t.val - 8, by omega⟩
          simp only at this
          rwa [show (⟨8 + (t.val - 8), by omega⟩ : Fin 17) = t from Fin.ext (by simp; omega)]
            at this
        · rwa [show (16 : Fin 17) = t from Fin.ext (by simp; omega)] at e3
  have hK : Ks.card ≤ 2 ^ (64 - g) * (2 ^ 64) ^ 16 := by
    refine (Finset.card_le_card_of_injOn (fun k ↦ (k 0, fun i : Fin 16 ↦ k i.succ))
      (t := (univ.filter fun x : K ↦ kToNat x < 2 ^ (64 - g)) ×ˢ univ)
      (fun k hk ↦ ?_) (fun k _ k' _ he ↦ ?_)).trans ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Ks] at hk
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_univ, and_true]
      exact hk
    · funext t
      refine Fin.cases ?_ (fun i ↦ ?_) t
      · exact congrArg Prod.fst he
      · exact congrFun (congrArg Prod.snd he) i
    · rw [Finset.card_product, card_kToNat_lt (by omega), Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
      simp only [BF64.card_bf64, le_refl]
  rw [Finset.card_product] at h1
  calc _ ≤ Y.card * Ks.card := h1
    _ ≤ (univ.filter B).card * (2 ^ (64 - g) * (2 ^ 64) ^ 16) := Nat.mul_le_mul hY hK
    _ = _ := by ring

private theorem two_inv_pow_mul_two_pow (m n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (m + n) * 2 ^ m = 2⁻¹ ^ n := by
  rw [pow_add, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ m), mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-- The group's escape in the certificate's units. -/
private theorem escape_arith (L n g : ℕ) (hg : g ≤ 64) :
    (Fintype.card E : ℝ≥0∞)⁻¹ ^ 17 *
        ((L : ℝ≥0∞) * ((2 ^ (64 - g) * (2 ^ 64) ^ 16 * (n * (2 ^ 128) ^ 16) : ℕ) : ℝ≥0∞)) =
      grpEpsE L n g := by
  rw [card_E, grpEpsE]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have key : ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 17 * (2 ^ (64 - g) * (2 ^ 64) ^ 16 * (2 ^ 128) ^ 16) =
      2⁻¹ ^ g * (2 ^ 128)⁻¹ := by
    rw [ENNReal.inv_pow, ENNReal.inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
      show 192 * 17 = (64 - g + 64 * 16 + 128 * 16) + (g + 128) by omega,
      two_inv_pow_mul_two_pow, pow_add]
  calc _ = (L : ℝ≥0∞) * (n * (((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 17 *
          (2 ^ (64 - g) * (2 ^ 64) ^ 16 * (2 ^ 128) ^ 16))) := by ring
    _ = _ := by rw [key]; ring

/-- **T4' (`ringSpec6`)**: the group of a nonce and 17 answers turns doom of "the 64 slice claims
and the claims `cs` are true, and `R`" into doom of "the stack claim is true, and `R`"; lead `0`,
the group's escape `L₀ · 2^-g · (|cs| + 2)/2^128` charged at the nonce's boundary. -/
theorem ringSpec6 {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}
    (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g μ a : ℕ} (hg : g ≤ 64)
    (r : Fin μ → E2) (sv : Fin 64 → E2) (off : Fin a → Bool) (cs : List Claim)
    (stk : β → (Fin (μ + a) → Bool) → K) (R : β → Prop)
    (he1 : grpEpsE L₀ (cs.length + 2) g < 1) (he : grpEpsE L₀ (cs.length + 2) g + T ≤ εmax) :
    Nonempty (Spec (ringProg g)
      (Doomed C fun q ↦ (∀ i, sliceExt (block off (stk q)) r i = sv i) ∧
        (∀ c ∈ cs, c.Holds (μ + a) (stk q)) ∧ R q)
      (fun out h ↦ Doomed C (fun q ↦ (stackClaim μ (List.ofFn r) (List.ofFn sv)
        (List.ofFn (bitV off)) cs out).Holds (μ + a) (stk q) ∧ R q) h) εmax 0 T) := by
  classical
  let A : β → Prop := fun q ↦ (∀ i, sliceExt (block off (stk q)) r i = sv i) ∧
    (∀ c ∈ cs, c.Holds (μ + a) (stk q)) ∧ R q
  let A' : List E2 × List E2 × E2 → β → Prop := fun out q ↦
    (stackClaim μ (List.ofFn r) (List.ofFn sv) (List.ofFn (bitV off)) cs out).Holds (μ + a) (stk q) ∧
      R q
  let out : List E → List E2 × List E2 × E2 := fun l ↦
    ((l.take 8).map e2OfE, ((l.drop 8).take 8).map e2OfE, e2OfE (l.getD 16 0))
  let body : VerifierProgram (List E2 × List E2 × E2) :=
    (VerifierProgram.sampleChallenges 17).bind fun l ↦
      (VerifierProgram.require (powOK g (l.headD 0))).bind fun _ ↦ VerifierProgram.ret (out l)
  have hreq : ∀ P : Prop, ∀ [Decidable P], NoMoves (VerifierProgram.require P) := by
    intro P _
    unfold VerifierProgram.require
    split
    · exact NoMoves.ret ()
    · exact NoMoves.fail
  have hnm : NoMoves body :=
    (noMoves_sampleN 17).bind fun l ↦ (hreq _).bind fun _ ↦ NoMoves.ret _
  have hesc : ∀ h₀, Doomed C A h₀ → VerifierProgram.escRet (fun o h ↦ Doomed C (A' o) h) h₀ [] body ≤
      grpEpsE L₀ (cs.length + 2) g := by
    intro h₀ hpre
    have hfin : (C h₀).Finite := Set.toFinite _
    rw [escRet_doomed_stable hst A' h₀ body [] rfl]
    unfold VerifierProgram.escRet
    rw [retExp_bind]
    let G : List E → ℝ≥0∞ := fun l ↦
      if powOK g (l.headD 0) then (if Doomed C (A' (out l)) h₀ then 0 else 1) else 0
    have hin : (fun (l : List E) (h : List Ev) ↦ VerifierProgram.retExp (fun o (_ : List Ev) ↦
        if Doomed C (A' o) h₀ then (0 : ℝ≥0∞) else 1) h []
          ((VerifierProgram.require (powOK g (l.headD 0))).bind fun _ ↦
            VerifierProgram.ret (out l))) = fun l _ ↦ G l := by
      funext l h
      simp only [G, VerifierProgram.require]
      split_ifs <;> simp_all [VerifierProgram.bind, VerifierProgram.retExp]
    rw [hin, retExp_sampleN]
    -- each accepted bad answer list is bad for some candidate
    have hcover : ∀ f : Fin 17 → E, G (List.ofFn f) ≤ ∑ q ∈ hfin.toFinset,
        (if powOK g (f 0) ∧ A' (List.ofFn (outOf f).1, List.ofFn (outOf f).2.1, (outOf f).2.2) q
          then 1 else 0 : ℝ≥0∞) := by
      intro f
      have hhead : (List.ofFn f).headD 0 = f 0 := by simp [List.ofFn_succ]
      have hout : out (List.ofFn f) =
          (List.ofFn (outOf f).1, List.ofFn (outOf f).2.1, (outOf f).2.2) := ringOut_ofFn f
      simp only [G, hhead, hout]
      split_ifs with hp hd
      · exact zero_le
      · simp only [Doomed, not_forall, not_not, exists_prop] at hd
        obtain ⟨q, hq, hA⟩ := hd
        refine le_trans ?_ (Finset.single_le_sum (f := fun q ↦ (if powOK g (f 0) ∧
          A' (List.ofFn (outOf f).1, List.ofFn (outOf f).2.1, (outOf f).2.2) q then 1 else 0 :
            ℝ≥0∞)) (fun _ _ ↦ zero_le) (hfin.mem_toFinset.2 hq))
        rw [if_pos ⟨hp, hA⟩]
      · exact zero_le
    -- one candidate's count
    have hone : ∀ q ∈ C h₀, (univ.filter fun f : Fin 17 → E ↦ powOK g (f 0) ∧
        A' (List.ofFn (outOf f).1, List.ofFn (outOf f).2.1, (outOf f).2.2) q).card ≤
          2 ^ (64 - g) * (2 ^ 64) ^ 16 * ((cs.length + 2) * (2 ^ 128) ^ 16) := by
      intro q hq
      refine (card_powOK_outOf_le hg (fun v ↦ A' (List.ofFn v.1, List.ofFn v.2.1, v.2.2) q)).trans
        (Nat.mul_le_mul_left _ ?_)
      by_cases hR : R q
      · refine (Finset.card_le_card fun v hv ↦ ?_).trans
          (card_stackBad_le r sv off cs (stk q) fun hsc ↦ hpre q hq ⟨hsc.1, hsc.2, hR⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A'] at hv ⊢
        exact hv.1
      · have : (univ.filter fun v : (Fin 8 → E2) × (Fin 8 → E2) × E2 ↦
            A' (List.ofFn v.1, List.ofFn v.2.1, v.2.2) q) = ∅ := by
          ext v; simp [A', hR]
        rw [this, Finset.card_empty]
        exact Nat.zero_le _
    calc (Fintype.card E : ℝ≥0∞)⁻¹ ^ 17 * ∑ f : Fin 17 → E, G (List.ofFn f)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ 17 * ∑ f : Fin 17 → E, ∑ q ∈ hfin.toFinset,
            (if powOK g (f 0) ∧ A' (List.ofFn (outOf f).1, List.ofFn (outOf f).2.1, (outOf f).2.2) q
              then 1 else 0 : ℝ≥0∞) := by
          gcongr with f; exact hcover f
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ ^ 17 * ∑ q ∈ hfin.toFinset,
            ((univ.filter fun f : Fin 17 → E ↦ powOK g (f 0) ∧
              A' (List.ofFn (outOf f).1, List.ofFn (outOf f).2.1, (outOf f).2.2) q).card : ℝ≥0∞) := by
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          rw [Finset.sum_boole]
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ 17 * ∑ _q ∈ hfin.toFinset,
            ((2 ^ (64 - g) * (2 ^ 64) ^ 16 * ((cs.length + 2) * (2 ^ 128) ^ 16) : ℕ) : ℝ≥0∞) := by
          gcongr with q hq
          exact_mod_cast hone q (hfin.mem_toFinset.1 hq)
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ 17 * ((L₀ : ℝ≥0∞) *
            ((2 ^ (64 - g) * (2 ^ 64) ^ 16 * ((cs.length + 2) * (2 ^ 128) ^ 16) : ℕ) : ℝ≥0∞)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact_mod_cast hcard h₀
      _ = grpEpsE L₀ (cs.length + 2) g := escape_arith L₀ (cs.length + 2) g hg
  exact ⟨(doomRead hst A he).bind' fun _ ↦ Spec.ofNoMove hnm.noMove he1 hesc⟩

end Dsl

end Lvm6.Ring
