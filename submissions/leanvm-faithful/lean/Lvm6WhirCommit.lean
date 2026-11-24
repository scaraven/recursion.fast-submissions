-- New for lvm6 (WP W1). T3a `commitSpec6` for ASM's §6.1 program `commit6` with W1's seam `I6`:
-- from the empty history, the commitment, the bind, the OOD group `G(18), D(24)` and `y₀` reach a
-- pinned history (the OOD answer present, at most one candidate) with one commitment on which the
-- returned claim 0 ties the candidates to the level-0 ball. The OOD group's escape is the pin's
-- collision: two distinct ball members (at most 111) with equal multilinear extensions at `z₀`,
-- `C(111, 2)·25` points per `|E2|^24` (Schwartz–Zippel, `card_mle_eq_le`), admitted by PARAM at
-- grind 18. The claim is tied to the history by the run's trace (`Spec.traceAnd`).
import Lvm6WhirIface
import Lvm6AsmProg
import LvmE2VBaseLemmas

/-!
# `commitSpec6` (W1)

* `Spec.traceAnd`: a postcondition fact about the whole run, from the precondition and the run.
* `after_bind_ret` and the run lemmas of `readCommitment`, `e2Sep`, `grp6`, `e2Read`; `commit6_run`.
* `evalS w q`, `GoodW w cs`: no two distinct ball members have the same value under the weight `w`;
  `card_collide_le`, `grpE_good_le`.
* **`commitSpec6_W1 : Stmt.commitSpec6 I6 commit6`**.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Verifier
  Lvm.E2V Finset
open scoped ENNReal

/-! ## A trace fact in the postcondition -/

open Classical in
/-- **A run fact joins the postcondition**: if every run from a history in `Pre` returning `a`
satisfies `R a`, the specification also gives `R`. -/
noncomputable def _root_.LeanVM.Protocol.Compile.Spec.traceAnd {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞} (S : Spec p Pre Post εmax L T)
    (R : α → List Ev → Prop)
    (hR : ∀ h₀ l a, Pre h₀ → p.Reach h₀ l → p.after l = some (.ret a) → R a (h₀ ++ l)) :
    Spec p Pre (fun a h ↦ Post a h ∧ R a h) εmax L T where
  D h₀ l := S.D h₀ l ∧ Pre h₀
  V h₀ l := if Pre h₀ then S.V h₀ l else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one _ _, le_rfl]
  start_D h₀ hp := ⟨S.start_D h₀ hp, hp⟩
  start_V h₀ hp := by rw [if_pos hp]; exact S.start_V h₀ hp
  read x hr ha hD := ⟨S.read x hr ha hD.1, hD.2⟩
  grind hr ha hD := ⟨S.grind hr ha hD.1, hD.2⟩
  commit word hr ha hws hD := ⟨S.commit word hr ha hws hD.1, hD.2⟩
  sample {h₀ l k} hr ha := by
    by_cases hp : Pre h₀
    · simp only [if_pos hp]; exact S.sample hr ha
    · simp only [if_neg hp]; exact avg_le_one _ fun _ ↦ le_rfl
  query {h₀ l i ps k rows} hr ha hans := by
    by_cases hp : Pre h₀
    · simp only [if_pos hp]; exact S.query hr ha hans
    · simp only [if_neg hp]; exact le_rfl
  moveEnd {h₀ l q} hr ha hm hnD := by
    by_cases hp : Pre h₀
    · rw [if_pos hp]; exact S.moveEnd hr ha hm fun h ↦ hnD ⟨h, hp⟩
    · rw [if_neg hp]
  retEnd {h₀ l a} hr ha hnD := by
    by_cases hp : Pre h₀
    · rw [if_pos hp]; exact S.retEnd hr ha fun h ↦ hnD ⟨h, hp⟩
    · rw [if_neg hp]
  retDoom hr ha hD := by rw [if_pos hD.2]; exact S.retDoom hr ha hD.1
  post hr ha hD := ⟨S.post hr ha hD.1, hR _ _ _ hD.2 hr ha⟩
  bound hr hne hem hD := by rw [if_pos hD.2]; exact S.bound hr hne hem hD.1

/-! ## Runs of the §6.1 pieces -/

section Runs

variable {α β : Type}

theorem after_ret_eq {a : α} {l : List Ev} {q : VerifierProgram α}
    (h : (VerifierProgram.ret a).after l = some q) : l = [] ∧ q = .ret a := by
  cases l with
  | nil => simp [VerifierProgram.after] at h; exact ⟨rfl, h.symm⟩
  | cons e es => cases e <;> simp [VerifierProgram.after] at h

theorem bind_ret_eq {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β}
    (h : p.bind f = .ret b) : ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [VerifierProgram.bind]

/-- **A return of a bind** splits into a return of each part. -/
theorem after_bind_ret {p : VerifierProgram α} {f : α → VerifierProgram β} {l : List Ev} {b : β}
    (h : (p.bind f).after l = some (.ret b)) :
    ∃ a l₁ l₂, l = l₁ ++ l₂ ∧ p.after l₁ = some (.ret a) ∧ (f a).after l₂ = some (.ret b) := by
  rcases VerifierProgram.after_bind_cases f h with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, hl, h1, _, h2⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_ret_eq hr.symm
    exact ⟨a, l, [], by simp, hq, by simp [VerifierProgram.after, hfa]⟩
  · exact ⟨a, l₁, l₂, hl, h1, h2⟩

theorem readCommitment_run {ht w : ℕ} {l : List Ev} {a : Unit}
    (h : (VerifierProgram.readCommitment ht w).after l = some (.ret a)) :
    ∃ W, l = [Ev.commit ht w W] := by
  rcases l with _ | ⟨e, es⟩
  · simp [VerifierProgram.readCommitment, VerifierProgram.after] at h
  · cases e <;> simp [VerifierProgram.readCommitment, VerifierProgram.after] at h
    rename_i ht' w' W
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    obtain ⟨rfl, -⟩ := after_ret_eq h
    exact ⟨W, rfl⟩

theorem e2Sep_run {l : List Ev} {a : Unit} (h : e2Sep.after l = some (.ret a)) :
    ∃ b, l = [Ev.sample b] := by
  rcases l with _ | ⟨e, es⟩
  · simp [e2Sep, VerifierProgram.after, VerifierProgram.sampleChallenge, VerifierProgram.bind] at h
  · cases e <;> simp [e2Sep, VerifierProgram.after, VerifierProgram.sampleChallenge,
      VerifierProgram.bind] at h
    rename_i b
    obtain ⟨rfl, -⟩ := after_ret_eq h
    exact ⟨b, rfl⟩

theorem e2Read_run {l : List Ev} {y : E2} (h : e2Read.after l = some (.ret y)) :
    ∃ x, l = [Ev.read x] ∧ y = e2OfE x := by
  rcases l with _ | ⟨e, es⟩
  · simp [e2Read, VerifierProgram.after, VerifierProgram.readScalar, VerifierProgram.bind] at h
  · cases e <;> simp [e2Read, VerifierProgram.after, VerifierProgram.readScalar,
      VerifierProgram.bind] at h
    rename_i x
    obtain ⟨rfl, h2⟩ := after_ret_eq h
    exact ⟨x, rfl, (by simpa using h2.symm : e2OfE x = y).symm⟩

theorem drawN_run {γ : Type} {f : List E → VerifierProgram γ} {c : γ} :
    ∀ (n : ℕ) (l : List Ev), (drawN n f).after l = some (.ret c) →
      ∃ cs l', cs.length = n ∧ l = cs.map Ev.sample ++ l' ∧ (f cs).after l' = some (.ret c)
  | 0, l, h => ⟨[], l, rfl, rfl, h⟩
  | n + 1, l, h => by
    rcases l with _ | ⟨e, es⟩
    · simp [drawN, VerifierProgram.after] at h
    · cases e <;> simp [drawN, VerifierProgram.after] at h
      rename_i c₀
      obtain ⟨cs, l', hlen, rfl, hf⟩ := drawN_run (f := fun cs ↦ f (c₀ :: cs)) n es h
      exact ⟨c₀ :: cs, l', by simp [hlen], rfl, hf⟩

/-- **A run of a group** to its values: the nonce, the ground draw, `k` draws. -/
theorem grp6_run {g k : ℕ} {l : List Ev} {ys : List E2} (h : (grp6 g k).after l = some (.ret ys)) :
    ∃ (x c : E) (cs : List E), l = Ev.read x :: Ev.sample c :: cs.map Ev.sample ∧ cs.length = k ∧
      ys = e2OfE c :: cs.map e2OfE := by
  rcases l with _ | ⟨e, es⟩
  · simp [grp6, VerifierProgram.after, VerifierProgram.readScalar, VerifierProgram.bind] at h
  · cases e <;> simp [grp6, VerifierProgram.after, VerifierProgram.readScalar,
      VerifierProgram.bind] at h
    rename_i x
    rcases es with _ | ⟨e, es⟩
    · simp [draws6, VerifierProgram.after] at h
    · cases e <;> simp [draws6, VerifierProgram.after] at h
      rename_i c
      split at h
      · obtain ⟨cs, l', hlen, rfl, hf⟩ := drawN_run k es h
        obtain ⟨rfl, hr⟩ := after_ret_eq hf
        exact ⟨x, c, cs, by simp, hlen,
          (by simpa using hr.symm : e2OfE c :: cs.map e2OfE = ys).symm⟩
      · cases es <;> simp [VerifierProgram.after] at h

end Runs

/-! ## The run of §6.1 -/

theorem commit6_run {ht wd : ℕ} {l : List Ev} {c₀ : StackClaim6}
    (h : (VerifierProgram.readCommitment ht wd >>= fun _ ↦ e2Sep >>= fun _ ↦ grp6 18 24 >>= fun z ↦
      e2Read >>= fun y ↦ (pure (fun pt ↦ eqPt z pt, y) : VerifierProgram StackClaim6)).after l =
      some (.ret c₀)) :
    ∃ (W : Word) (b x c : E) (cs : List E) (y : E),
      l = [Ev.commit ht wd W, Ev.sample b, Ev.read x, Ev.sample c] ++
      (cs.map Ev.sample ++ [Ev.read y]) ∧ cs.length = 24 ∧
      c₀ = (fun pt ↦ eqPt (e2OfE c :: cs.map e2OfE) pt, e2OfE y) := by
  obtain ⟨_, l₁, r₁, rfl, h1, hA⟩ := after_bind_ret h
  obtain ⟨W, rfl⟩ := readCommitment_run h1
  obtain ⟨_, l₂, r₂, rfl, h2, hB⟩ := after_bind_ret hA
  obtain ⟨b, rfl⟩ := e2Sep_run h2
  obtain ⟨z, l₃, r₃, rfl, h3, hC⟩ := after_bind_ret hB
  obtain ⟨x, c, cs, rfl, hlen, rfl⟩ := grp6_run h3
  obtain ⟨y, l₄, r₄, rfl, h4, hD⟩ := after_bind_ret hC
  obtain ⟨y', rfl, rfl⟩ := e2Read_run h4
  obtain ⟨rfl, hc⟩ := after_ret_eq hD
  refine ⟨W, b, x, c, cs, y', by simp, hlen, ?_⟩
  exact (by simpa using hc.symm :
    ((fun pt ↦ eqPt (e2OfE c :: cs.map e2OfE) pt, e2OfE y') : StackClaim6) = c₀).symm

theorem claim0_run {ht wd : ℕ} (W : Word) (b x c y : E) (cs : List E) (hcs : cs.length = 24) :
    claim0 ([Ev.commit ht wd W, Ev.sample b, Ev.read x, Ev.sample c] ++
      (cs.map Ev.sample ++ [Ev.read y])) =
      (fun pt ↦ eqPt (e2OfE c :: cs.map e2OfE) pt, e2OfE y) ∧
    HasOod ([Ev.commit ht wd W, Ev.sample b, Ev.read x, Ev.sample c] ++
      (cs.map Ev.sample ++ [Ev.read y])) := by
  have hf : firstCommit ([Ev.commit ht wd W, Ev.sample b, Ev.read x, Ev.sample c] ++
      (cs.map Ev.sample ++ [Ev.read y])) = 0 := rfl
  refine ⟨?_, ⟨by simp [commits], by rw [hf]; simp [hcs]⟩⟩
  unfold claim0 oodZ oodY
  rw [hf]
  have hz : ((([Ev.commit ht wd W, Ev.sample b, Ev.read x, Ev.sample c] ++
      (cs.map Ev.sample ++ [Ev.read y])).drop 3).take 25).map evVal = e2OfE c :: cs.map e2OfE := by
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]
    rw [List.take_succ_cons, List.take_append_of_le_length (by simp [hcs]),
      List.take_of_length_le (by simp [hcs])]
    simp [evVal, Function.comp_def]
  have hy : (([Ev.commit ht wd W, Ev.sample b, Ev.read x, Ev.sample c] ++
      (cs.map Ev.sample ++ [Ev.read y]))[0 + 28]?.map evVal).getD 0 = e2OfE y := by
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp [hcs])]
    simp [hcs, evVal]
  rw [hz, hy]

/-! ## The pin's collision count -/

/-- The level-0 ball of a list of commitments. -/
noncomputable def ballC (cs : List (ℕ × ℕ × Word)) : Set Stack :=
  dec18 '' ↑(tupleList (domE 21 (by norm_num)) (wordE true 0 (0 + 6) 21 cs) (1053300 - 6)
    (2 ^ 19 - 1 + 6))

theorem ball18_ballC (h : List Ev) : ball18 h = ballC (commits h) := ball18_eq h

/-- A weight's value on a stack (the left side of `Holds 25`). -/
noncomputable def evalS (w : List E2 → E2) (q : Stack) : E2 :=
  ∑ x : Fin (2 ^ 25), w (boolPt 25 x) * algebraMap K E2 (q x)

/-- No two distinct ball members have the same value under `w`. -/
def GoodW (w : List E2 → E2) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∀ q ∈ ballC cs, ∀ q' ∈ ballC cs, q ≠ q' → evalS w q ≠ evalS w q'

/-- A stack's cube table. -/
noncomputable def tabQ (q : Stack) : (Fin 25 → Bool) → E2 := fun b ↦ algebraMap K E2 (q (bitsToNat b))

theorem eqPt_ofFn {n : ℕ} (u v : Fin n → E2) :
    eqPt (List.ofFn u) (List.ofFn v) = ∏ i, (u i * v i + (1 + u i) * (1 + v i)) := by
  have : List.zipWith (fun r t ↦ r * t + (1 + r) * (1 + t)) (List.ofFn u) (List.ofFn v) =
      List.ofFn fun i ↦ u i * v i + (1 + u i) * (1 + v i) :=
    List.ext_getElem (by simp) fun i h1 h2 ↦ by simp
  rw [eqPt, this, List.prod_ofFn]

theorem boolPt_bits (b : Fin 25 → Bool) :
    boolPt 25 (bitsToNat b) = List.ofFn fun i : Fin 25 ↦ if b i then (1 : E2) else 0 := by
  rw [boolPt_eq]
  exact List.ofFn_inj.mpr (funext fun i ↦ by rw [testBit_bitsToNat])

theorem evalS_eq_mle (u : Fin 25 → E2) (q : Stack) :
    evalS (fun pt ↦ eqPt (List.ofFn u) pt) q = mleEval u (tabQ q) := by
  unfold evalS
  rw [← (bitsEquiv 25).sum_comp]
  simp only [mleEval, mlePoly, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul,
    MvPolynomial.eval_C, map_prod]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [bitsEquiv_val, boolPt_bits, eqPt_ofFn, mul_comm]
  unfold tabQ
  refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
  by_cases hb : b i
  · simp only [hb, ↓reduceIte, mul_one, CharTwo.add_self_eq_zero, mul_zero, add_zero,
      MvPolynomial.eval_X]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add, add_zero, mul_one,
      map_sub, MvPolynomial.eval_X, map_one]
    rw [CharTwo.sub_eq_add]

theorem dec18_periodic (U : Tup E2 (0 + 6)) (x : ℕ) :
    dec18 U x = dec18 U (bitsToNat fun i : Fin 25 ↦ x.testBit i) := by
  have e1 : (fun i : Fin (0 + 6) ↦ (bitsToNat fun i : Fin 25 ↦ x.testBit i).testBit (19 + i)) =
      fun i : Fin (0 + 6) ↦ x.testBit (19 + i) := funext fun i ↦
    testBit_bitsToNat (fun i : Fin 25 ↦ x.testBit i) (Fin.natAdd 19 i)
  have e2 : (fun i : Fin 19 ↦ (bitsToNat fun i : Fin 25 ↦ x.testBit i).testBit i) =
      fun i : Fin 19 ↦ x.testBit i := funext fun i ↦
    testBit_bitsToNat (fun i : Fin 25 ↦ x.testBit i) (Fin.castAdd 6 i)
  show _ = (lowMsgF 19 (U fun i ↦ (bitsToNat fun i : Fin 25 ↦ x.testBit i).testBit (19 + i))
    fun i ↦ (bitsToNat fun i : Fin 25 ↦ x.testBit i).testBit i).re
  rw [e1, e2]
  rfl

theorem tabQ_ne {cs : List (ℕ × ℕ × Word)} {q q' : Stack} (hq : q ∈ ballC cs) (hq' : q' ∈ ballC cs)
    (hne : q ≠ q') : tabQ q ≠ tabQ q' := by
  obtain ⟨U, -, rfl⟩ := hq
  obtain ⟨U', -, rfl⟩ := hq'
  intro ht
  apply hne
  funext x
  rw [dec18_periodic U x, dec18_periodic U' x]
  exact (algebraMap K E2).injective (congrFun ht _)

theorem ballC_finite (cs : List (ℕ × ℕ × Word)) : (ballC cs).Finite :=
  Set.Finite.image _ (Finset.finite_toSet _)

theorem ballC_card (cs : List (ℕ × ℕ × Word)) : (ballC_finite cs).toFinset.card ≤ 111 := by
  rw [← Set.ncard_eq_toFinset_card _ (ballC_finite cs)]
  have := ball18_card ([Ev.commit 0 0 fun _ ↦ []] ++ [])
  unfold ballC
  refine (Set.ncard_image_le (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine (card_tupleList_le_jl _ _ _ _ (by norm_num)).trans ?_
  decide +kernel

open Classical in
/-- **The pin's bad points**: at most `C(111, 2)·25·|E2|^24`. -/
theorem card_collide_le (cs : List (ℕ × ℕ × Word)) :
    (univ.filter fun u : Fin 25 → E2 ↦ ¬ GoodW (fun pt ↦ eqPt (List.ofFn u) pt) cs).card ≤
      Nat.choose 111 2 * 25 * Fintype.card E2 ^ 24 := by
  set B := (ballC_finite cs).toFinset
  let bad : Finset Stack → Finset (Fin 25 → E2) := fun s ↦
    univ.filter fun u ↦ ∃ q ∈ s, ∃ q' ∈ s, q ≠ q' ∧ mleEval u (tabQ q) = mleEval u (tabQ q')
  have hsub : (univ.filter fun u : Fin 25 → E2 ↦ ¬ GoodW (fun pt ↦ eqPt (List.ofFn u) pt) cs) ⊆
      (B.powersetCard 2).biUnion bad := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, GoodW, not_forall, not_not,
      exists_prop] at hu
    obtain ⟨q, hq, q', hq', hne, he⟩ := hu
    refine Finset.mem_biUnion.mpr ⟨{q, q'}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hne⟩, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact (ballC_finite cs).mem_toFinset.mpr hq
      · rw [Finset.mem_singleton.mp hr]; exact (ballC_finite cs).mem_toFinset.mpr hq'
    · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨q, by simp, q', by simp, hne, ?_⟩
      rwa [evalS_eq_mle, evalS_eq_mle] at he
  have hbad : ∀ s ∈ B.powersetCard 2, (bad s).card ≤ 25 * Fintype.card E2 ^ 24 := by
    intro s hs
    obtain ⟨hsB, hs2⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨q, q', hne, rfl⟩ := Finset.card_eq_two.mp hs2
    have hq := (ballC_finite cs).mem_toFinset.mp (hsB (Finset.mem_insert_self q {q'}))
    have hq' := (ballC_finite cs).mem_toFinset.mp
      (hsB (Finset.mem_insert_of_mem (Finset.mem_singleton_self q')))
    refine le_trans (Finset.card_le_card fun u hu ↦ ?_) (card_mle_eq_le (tabQ_ne hq hq' hne))
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨a, ha, b, hb, hab, he⟩ := hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact he
    · exact he.symm
    · exact absurd rfl hab
  calc _ ≤ ((B.powersetCard 2).biUnion bad).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ B.powersetCard 2, (bad s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ B.powersetCard 2, 25 * Fintype.card E2 ^ 24 := Finset.sum_le_sum hbad
    _ = B.card.choose 2 * (25 * Fintype.card E2 ^ 24) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    _ ≤ Nat.choose 111 2 * (25 * Fintype.card E2 ^ 24) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (ballC_card cs))
    _ = _ := by ring

/-- The OOD group's escape at `P18`. -/
noncomputable def eOod0 : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ 18 * ((Nat.choose 111 2 * 25 : ℕ) : ℝ≥0∞) / (Fintype.card E2 : ℝ≥0∞)

theorem eOod0_le : eOod0 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  unfold eOod0
  rw [card_E2]
  exact adm_le (by decide)

open Classical in
theorem grpE_good_le (cs : List (ℕ × ℕ × Word)) :
    grpE E2 18 24 (fun u ↦ ¬ (cs.length = 1 ∧ GoodW (fun pt ↦ eqPt (List.ofFn u) pt) cs)) ≤
      eOod0 ∨ cs.length ≠ 1 := by
  by_cases hl : cs.length = 1
  · left
    unfold grpE eOod0
    have hq : Fintype.card E2 ≠ 0 := Fintype.card_ne_zero
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 18 * (((Nat.choose 111 2 * 25 : ℕ) : ℝ≥0∞) *
            (Fintype.card E2 : ℝ≥0∞) ^ 24) / (Fintype.card E2 : ℝ≥0∞) ^ (24 + 1) := by
          gcongr
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card (t := univ.filter fun u ↦
            ¬ GoodW (fun pt ↦ eqPt (List.ofFn u) pt) cs) fun u hu ↦ ?_)) ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            exact fun h ↦ hu ⟨hl, h⟩
          · exact_mod_cast card_collide_le cs
      _ = _ := by rw [← mul_assoc, ennr_div_pow _ hq]
  · exact Or.inr hl

/-! ## The specification -/

theorem avgN_zero_le : ∀ (n : ℕ), avgN n (fun _ ↦ (0 : ℝ≥0∞)) ≤ 0
  | 0 => le_rfl
  | n + 1 => avgE_le_of_le fun _ ↦ avgN_zero_le n

theorem grpEsc_false {g k : ℕ} {P : Prop} (hP : ¬ P) : grpEsc g k (fun _ ↦ P) ≤ 0 := by
  unfold grpEsc
  refine avgE_le_of_le fun c ↦ ?_
  split_ifs
  · simp only [indE_of_not hP]
    exact avgN_zero_le k
  · exact le_rfl

/-- A group keeps an invariant of the commitments, at any grind (escape `0`). -/
noncomputable def grp6_keep (g k : ℕ) (Inv : List (ℕ × ℕ × Word) → Prop) :
    Spec (grp6 g k) (fun h ↦ Inv (commits h)) (fun _ h ↦ Inv (commits h)) Lvm6.εI 0 0 :=
  (Spec.exPre (Pre := fun cs₀ h ↦ Doomed (cmap cs₀) (onTrue (¬ Inv cs₀)) h) fun cs₀ ↦
    (doomGrp6 (εmax := Lvm6.εI) (T := 0) (cmap_stable cs₀) (cmap_card cs₀) (onTrue (¬ Inv cs₀))
      (fun _ ↦ onTrue (¬ Inv cs₀)) 0 (fun q hq ↦ by
        cases q with
        | false => exact absurd trivial hq
        | true => exact grpEsc_false (P := ¬ Inv cs₀) hq) εI_lt_one (by simp)).mono (fun _ h ↦ h)
      (fun _ h hp ↦ by
        obtain ⟨hc, hI⟩ := doomed_onTrue.mp hp.2
        rw [hc]
        exact not_not.mp hI) le_rfl le_rfl le_rfl).mono
    (fun h hI ↦ ⟨commits h, doomed_onTrue.mpr ⟨rfl, not_not.mpr hI⟩⟩) (fun _ _ h ↦ h) le_rfl
    le_rfl le_rfl

theorem ofFn_gv {n : ℕ} {z : List E2} (hz : z.length = n) : List.ofFn (gv (k := n) z) = z :=
  List.ext_getElem (by simp [hz]) fun i h1 h2 ↦ by
    simp only [List.getElem_ofFn, gv]
    rw [List.getD_eq_getElem _ _ h2]

/-- The §6.1 program with `P18`'s OOD constants. -/
noncomputable def commitP18 (ht wd : ℕ) : VerifierProgram StackClaim6 :=
  VerifierProgram.readCommitment ht wd >>= fun _ ↦ e2Sep >>= fun _ ↦ grp6 18 24 >>= fun z ↦
    e2Read >>= fun y ↦ pure (fun pt ↦ eqPt z pt, y)

noncomputable def cCommit (ht wd : ℕ) :
    Spec (VerifierProgram.readCommitment ht wd) (fun h ↦ h = [])
      (fun _ h ↦ (commits h).length = 1) Lvm6.εI 0 0 :=
  Spec.commitP (Pre := fun h ↦ h = []) (Post := fun _ h ↦ (commits h).length = 1) ht wd
    (fun h₀ W hP _ ↦ by subst hP; rfl) (by positivity)

noncomputable def cSep : Spec e2Sep (fun h ↦ (commits h).length = 1)
    (fun _ h ↦ (commits h).length = 1) Lvm6.εI 0 0 :=
  chalE2.sepSpec (fun cs ↦ cs.length = 1) Lvm6.εI 0

noncomputable def cGrp0 : Spec (grp6 18 24) (fun h ↦ (commits h).length = 1)
    (fun z h ↦ ((commits h).length = 1 ∧ GoodW (fun pt ↦ eqPt (List.ofFn (gv (k := 25) z)) pt)
      (commits h)) ∧ z.length = 25) Lvm6.εI 0 0 :=
  ((chalE2.grpSpec 18 24 (by show 18 ≤ 64; norm_num) (fun cs ↦ cs.length = 1)
      (fun u cs ↦ cs.length = 1 ∧ GoodW (fun pt ↦ eqPt (List.ofFn u) pt) cs) eOod0
      (eOod0_le.trans_lt εI_lt_one)
      (fun cs hl ↦ (grpE_good_le cs).resolve_right fun h ↦ h hl)).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) eOod0_le le_rfl le_rfl).traceAnd (fun z _ ↦ z.length = 25)
    (fun _ _ _ _ _ ha ↦ by
      obtain ⟨x, c, cs, -, hl, rfl⟩ := grp6_run ha
      simp [hl])

noncomputable def cGrp : Spec (grp6 18 24) (fun h ↦ (commits h).length = 1)
    (fun z h ↦ (commits h).length = 1 ∧ GoodW (fun pt ↦ eqPt z pt) (commits h)) Lvm6.εI 0 0 :=
  cGrp0.mono (fun _ h ↦ h) (fun z h hp ↦ by
      obtain ⟨⟨hl, hg⟩, hz⟩ := hp
      rw [ofFn_gv hz] at hg
      exact ⟨hl, hg⟩) le_rfl le_rfl le_rfl

noncomputable def cRead (z : List E2) : Spec e2Read
    (fun h ↦ (commits h).length = 1 ∧ GoodW (fun pt ↦ eqPt z pt) (commits h))
    (fun _ h ↦ (commits h).length = 1 ∧ GoodW (fun pt ↦ eqPt z pt) (commits h)) Lvm6.εI 0 0 :=
  readFSpec chalE2 (εmax := Lvm6.εI)
    (Inv := fun cs ↦ cs.length = 1 ∧ GoodW (fun pt ↦ eqPt z pt) cs) (by positivity)

/-- The core's postcondition: one commitment, and claim 0's weight separates the ball. -/
def CorePost (c₀ : StackClaim6) (h : List Ev) : Prop :=
  (commits h).length = 1 ∧ ∃ z : List E2, ∃ y : E2, c₀ = (fun pt ↦ eqPt z pt, y) ∧
    GoodW (fun pt ↦ eqPt z pt) (commits h)

/-- The core: one commitment, and no two ball members with the same value of claim 0. -/
noncomputable def commitCore (ht wd : ℕ) :
    Spec (commitP18 ht wd) (fun h ↦ h = []) CorePost Lvm6.εI 0 0 :=
  (cCommit ht wd).bind' fun _ ↦ cSep.bind' fun _ ↦ cGrp.bind' fun z ↦ (cRead z).bind' fun y ↦
    (Spec.ret (Post := CorePost) (fun pt ↦ eqPt z pt, y)).mono
      (fun _ hp ↦ ⟨hp.1, z, y, rfl, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

theorem holds_iff (c : StackClaim6) (q : Stack) : c.Holds 25 q ↔ evalS c.1 q = c.2 := Iff.rfl

/-- **§6.1 at a keyed shape**: pinned, one commitment, claim 0 tied. -/
noncomputable def commitSpecKey (ht wd : ℕ) :
    Spec (commitP18 ht wd) (fun h ↦ h = [])
      (fun c₀ h ↦ I18.pinned h ∧ (commits h).length = 1 ∧ I18.Tied 25 c₀ h) Lvm6.εI 0 0 :=
  ((commitCore ht wd).traceAnd (fun c₀ h ↦ c₀ = claim0 h ∧ HasOod h)
    (fun h₀ l c₀ hp _ ha ↦ by
      subst hp
      obtain ⟨W, b, x, c, cs, y, rfl, hcs, rfl⟩ := commit6_run ha
      obtain ⟨h1, h2⟩ := claim0_run (ht := ht) (wd := wd) W b x c y cs hcs
      simpa using ⟨h1.symm, h2⟩)).mono (fun _ h ↦ h)
    (fun c₀ h hp ↦ by
      obtain ⟨⟨hl, z, y, hc0, hg⟩, hcl, hood⟩ := hp
      have h1 : (claim0 h).1 = fun pt ↦ eqPt z pt := by rw [← hcl, hc0]
      refine ⟨⟨hood, fun q hq q' hq' ↦ ?_⟩, hl, fun q hqb ↦ ?_⟩
      · by_contra hne
        have hb := ball18_ballC h
        have e1 := (holds_iff _ _).mp hq.2
        have e2 := (holds_iff _ _).mp hq'.2
        rw [h1] at e1 e2
        exact hg q (hb ▸ hq.1) q' (hb ▸ hq'.1) hne (e1.trans e2.symm)
      · rw [hcl]
        exact ⟨fun hh ↦ ⟨hqb, hh⟩, fun hh ↦ hh.2⟩) le_rfl le_rfl le_rfl

noncomputable def cReadT : Spec e2Read (fun h ↦ (commits h).length = 1)
    (fun _ h ↦ (commits h).length = 1) Lvm6.εI 0 0 :=
  readFSpec chalE2 (εmax := Lvm6.εI) (Inv := fun cs ↦ cs.length = 1) (by positivity)

/-- **§6.1 elsewhere**: one commitment (the seam is empty). -/
noncomputable def commitSpecTriv (sh : Shape) :
    Spec (commit6 sh) (fun h ↦ h = [])
      (fun c₀ h ↦ Itriv.pinned h ∧ (commits h).length = 1 ∧ Itriv.Tied sh.M c₀ h) Lvm6.εI 0 0 :=
  ((cCommit _ _).bind' fun _ ↦ cSep.bind' fun _ ↦
    (grp6_keep _ _ (fun cs ↦ cs.length = 1)).bind' fun z ↦ cReadT.bind' fun y ↦
    Spec.ret (Post := fun c₀ h ↦ (commits h).length = 1) (fun pt ↦ eqPt z pt, y)).mono
    (fun _ h ↦ h) (fun _ _ hl ↦ ⟨trivial, hl, fun q hq ↦ absurd hq (Set.notMem_empty q)⟩) le_rfl
    le_rfl le_rfl

theorem commit6_key {sh : Shape} (hk : openKey sh = true) :
    commit6 sh = commitP18 (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd := by
  simp only [openKey, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hM : sh.M = 25 := by rw [hk.1.1.1.1.1.1]; rfl
  have hg : (sh.lvl 0).gOod = 18 := by
    simp only [Shape.lvl, hk.1.1.1.1.2]
    rfl
  unfold commit6 commitP18
  rw [hM, hg]

/-- **T3a `commitSpec6`** (W1): ASM's §6.1 program meets `commitSpec6` with W1's seam `I6`. -/
theorem commitSpec6_W1 : Stmt.commitSpec6 I6 commit6 := fun sh ↦ by
  by_cases hk : openKey sh = true
  · rw [show I6 sh = I18 from if_pos hk, openKey_M hk, commit6_key hk]
    exact ⟨commitSpecKey _ _⟩
  · rw [show I6 sh = Itriv from if_neg hk]
    exact ⟨commitSpecTriv sh⟩

end Lvm6.Whir
