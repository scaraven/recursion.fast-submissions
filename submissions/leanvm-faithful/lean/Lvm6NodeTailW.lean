-- New for lvm6 (WP N4-tail). The opening's query nodes: `whirP18`'s `j`-th opening asks for commitment `j` at
-- the positions W1's level `j` computes from the draws just before it (`QN F18`), so V1's openings agree
-- (`QAgree`) as soon as they carry the same (`RowsF F18`).
import Lvm6NodeTailQ
import Lvm6WhirFollow

/-!
# The opening's queries (WP N4-tail)

* `qcount`, `lastS`: the number of openings among the events, the values of the last `m` draws.
* `qcount_of_follows`: a run of a program following `os` to a return has as many openings as `os`.
* `grp6_after`: a ground group's run is the nonce, then its `k + 1` draws, and returns their values.
* **`F18 E = (qcount E, posAt (qcount E) E)`**: level `j`'s positions (`qPos` of `mid_j`, `fPos` of `fin18`)
  of the last draws of its query group.
* **`qn_whirP18 : QN F18 (whirP18 cl) []`** (any `cl`): every query node of the opening asks for `F18`.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open LeanVM.Parameters

/-! ## Counting openings, the last draws -/

def isQ : Ev → Bool
  | .query _ => true
  | _ => false

def isOpn : Op → Bool
  | .opn _ => true
  | _ => false

/-- The openings among the events. -/
def qcount (E : List Ev) : ℕ := E.countP fun e ↦ isQ e

def sampleVal : Ev → Option E
  | .sample c => some c
  | _ => none

/-- The values of the last `m` draws. -/
def lastS (E : List Ev) (m : ℕ) : List E2 :=
  (((E.filterMap sampleVal).reverse.take m).reverse).map e2OfE

theorem qcount_append (l₁ l₂ : List Ev) : qcount (l₁ ++ l₂) = qcount l₁ + qcount l₂ := by
  simp [qcount, List.countP_append]

/-- **A run to a return has the openings of the operations it follows.** -/
theorem qcount_of_follows {α : Type} : ∀ (p : VerifierProgram α) (os : List Op) (l : List Ev) {a : α},
    Follows p os → p.after l = some (.ret a) → qcount l = os.countP fun o ↦ isOpn o
  | .ret _, os, [], _, h, _ => by
    have h' : os = [] := h
    subst h'
    rfl
  | .ret _, _, _ :: _, _, _, he => by simp [VerifierProgram.after] at he
  | .fail, _, [], _, _, he => by simp [VerifierProgram.after] at he
  | .fail, _, _ :: _, _, _, he => by simp [VerifierProgram.after] at he
  | .grind _ _, _, _, _, h, _ => h.elim
  | .read _, _, [], _, _, he => by simp [VerifierProgram.after] at he
  | .sample _, _, [], _, _, he => by simp [VerifierProgram.after] at he
  | .commit _ _ _, _, [], _, _, he => by simp [VerifierProgram.after] at he
  | .query _ _ _, _, [], _, _, he => by simp [VerifierProgram.after] at he
  | .read k, os, e :: l, _, h, he => by
    obtain ⟨o, os', rfl⟩ : ∃ o os', os = o :: os' := by
      cases os with
      | nil => exact absurd h.1 (by simp)
      | cons o os' => exact ⟨o, os', rfl⟩
    obtain rfl : o = .rd := Option.some.inj h.1
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    have := qcount_of_follows _ os' l (h.2 _) he
    simp only [qcount, List.countP_cons, isQ, isOpn] at this ⊢
    simpa using this
  | .sample k, os, e :: l, _, h, he => by
    obtain ⟨o, os', rfl⟩ : ∃ o os', os = o :: os' := by
      cases os with
      | nil => exact absurd h.1 (by simp)
      | cons o os' => exact ⟨o, os', rfl⟩
    obtain rfl : o = .smp := Option.some.inj h.1
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    have := qcount_of_follows _ os' l (h.2 _) he
    simp only [qcount, List.countP_cons, isQ, isOpn] at this ⊢
    simpa using this
  | .commit ht w k, os, e :: l, _, h, he => by
    obtain ⟨o, os', rfl⟩ : ∃ o os', os = o :: os' := by
      cases os with
      | nil => exact absurd h.1 (by simp)
      | cons o os' => exact ⟨o, os', rfl⟩
    obtain rfl : o = .cap ht w := Option.some.inj h.1
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    split at he
    · have := qcount_of_follows _ os' l h.2 he
      simp only [qcount, List.countP_cons, isQ, isOpn] at this ⊢
      simpa using this
    · simp at he
  | .query i ps k, os, e :: l, _, h, he => by
    obtain ⟨o, os', rfl⟩ : ∃ o os', os = o :: os' := by
      cases os with
      | nil => exact absurd h.1 (by simp)
      | cons o os' => exact ⟨o, os', rfl⟩
    obtain rfl : o = .opn i := Option.some.inj h.1
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    have := qcount_of_follows _ os' l (h.2 _) he
    simp only [qcount, List.countP_cons, isQ, isOpn] at this ⊢
    simpa using this

/-! ## A ground group's run -/

theorem drawN_after {α : Type} : ∀ (n : ℕ) (f : List E → VerifierProgram α) (l : List Ev) {b : α},
    (Lvm6.drawN n f).after l = some (.ret b) →
      ∃ cs l₂, cs.length = n ∧ l = cs.map Ev.sample ++ l₂ ∧ (f cs).after l₂ = some (.ret b)
  | 0, f, l, _, h => ⟨[], l, rfl, rfl, h⟩
  | n + 1, f, [], _, h => by simp [Lvm6.drawN, VerifierProgram.after] at h
  | n + 1, f, e :: l, _, h => by
    cases e <;> simp only [Lvm6.drawN, VerifierProgram.after, reduceCtorEq] at h
    rename_i c
    obtain ⟨cs, l₂, hl, rfl, h2⟩ := drawN_after n _ l h
    exact ⟨c :: cs, l₂, by simp [hl], rfl, h2⟩

theorem ret_after_eq {α : Type} {a b : α} {l : List Ev} (h : (VerifierProgram.ret a).after l = some (.ret b)) :
    l = [] ∧ a = b := by
  cases l with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at h
    exact ⟨rfl, h⟩
  | cons e l => simp [VerifierProgram.after] at h

/-- **A ground group's run**: the nonce, then `k + 1` draws, whose values it returns. -/
theorem grp6_after {g k : ℕ} {l : List Ev} {qv : List E2} (h : (grp6 g k).after l = some (.ret qv)) :
    ∃ (x : E) (cs : List E), l = .read x :: cs.map Ev.sample ∧ cs.length = k + 1 ∧ qv = cs.map e2OfE := by
  have e : grp6 g k = .read fun _ ↦ draws6 g k := rfl
  rw [e] at h
  cases l with
  | nil => simp [VerifierProgram.after] at h
  | cons e l =>
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    rename_i x
    cases l with
    | nil => simp [draws6, VerifierProgram.after] at h
    | cons e l =>
      cases e <;> simp only [draws6, VerifierProgram.after, reduceCtorEq] at h
      rename_i c
      split at h
      · obtain ⟨cs, l₂, hl, rfl, h2⟩ := drawN_after k _ l h
        obtain ⟨rfl, rfl⟩ := ret_after_eq h2
        exact ⟨x, c :: cs, by simp, by simp [hl], by simp⟩
      · cases l <;> simp [VerifierProgram.after] at h

theorem lastS_grp (A : List Ev) (x : E) (cs : List E) :
    lastS (A ++ Ev.read x :: cs.map Ev.sample) cs.length = cs.map e2OfE := by
  have hf : (A ++ Ev.read x :: cs.map Ev.sample).filterMap sampleVal = A.filterMap sampleVal ++ cs := by
    rw [List.filterMap_append, List.filterMap_cons]
    simp only [sampleVal, List.filterMap_map, Function.comp_def]
    simp
  rw [lastS, hf, List.reverse_append, List.take_left' (List.length_reverse), List.reverse_reverse]

theorem qcount_grp (x : E) (cs : List E) : qcount (Ev.read x :: cs.map Ev.sample) = 0 := by
  simp [qcount, isQ]

/-! ## Query nodes of the pieces -/

theorem countP_opn_eq_zero {os : List Op} (hno : ∀ i, Op.opn i ∉ os) : os.countP (fun o ↦ isOpn o) = 0 :=
  List.countP_eq_zero.mpr fun o ho ↦ by
    cases o <;> simp [isOpn]
    exact hno _ ho

/-- `QN` along a bind whose first part has no openings. -/
theorem qn_bind_noq {F : List Ev → ℕ × List ℕ} {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {os : List Op} {E : List Ev} (hp : Follows p os) (hno : ∀ i, Op.opn i ∉ os)
    (hf : ∀ l a, p.after l = some (.ret a) → qcount l = 0 → QN F (f a) (E ++ l)) : QN F (p >>= f) E :=
  qn_bind (qn_of_follows F hp hno E) fun l a h ↦
    hf l a h ((qcount_of_follows p os l hp h).trans (countP_opn_eq_zero hno))

theorem qn_ret {F : List Ev → ℕ × List ℕ} {α : Type} (a : α) (E : List Ev) : QN F (VerifierProgram.ret a) E := by
  intro l i ps k h
  cases l <;> simp [VerifierProgram.after] at h

theorem qn_fail {F : List Ev → ℕ × List ℕ} {α : Type} (E : List Ev) : QN F (VerifierProgram.fail : VerifierProgram α) E := by
  intro l i ps k h
  cases l <;> simp [VerifierProgram.after] at h

theorem qn_ite {F : List Ev → ℕ × List ℕ} {α : Type} {c : Prop} [Decidable c] {p q : VerifierProgram α}
    {E : List Ev} (hp : c → QN F p E) (hq : ¬ c → QN F q E) : QN F (if c then p else q) E := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

theorem qn_query {F : List Ev → ℕ × List ℕ} {i : ℕ} {ps : List ℕ} {E : List Ev} (h : F E = (i, ps)) :
    QN F (VerifierProgram.queryOpenings i ps) E := by
  intro l i' ps' k he
  cases l with
  | nil =>
    simp only [VerifierProgram.queryOpenings, VerifierProgram.after, Option.some.injEq,
      VerifierProgram.query.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    rw [List.append_nil, h]
  | cons e l =>
    cases e <;> simp only [VerifierProgram.queryOpenings, VerifierProgram.after,
      reduceCtorEq] at he
    cases l <;> simp [VerifierProgram.after] at he

theorem no_opn_replicate_rd (n : ℕ) : ∀ i, Op.opn i ∉ List.replicate n Op.rd := by
  intro i h
  simp [List.mem_replicate] at h

theorem no_opn_rounds (n : ℕ) : ∀ i, Op.opn i ∉ (List.replicate n Whir.roundOps).flatten := by
  intro i h
  simp [List.mem_flatten, List.mem_replicate, Whir.roundOps] at h

theorem no_opn_grp (k : ℕ) : ∀ i, Op.opn i ∉ (Op.rd :: List.replicate (k + 1) Op.smp) := by
  intro i h
  simp [List.mem_replicate] at h

theorem no_opn_sum (n : ℕ) : ∀ i, Op.opn i ∉ Whir.sumOps n := by
  intro i h
  simp [Whir.sumOps, List.mem_flatten, List.mem_replicate] at h

/-- **A level interface's query node** asks for commitment `i` at `qPos` of its query group's draws, when
`F` reads that off the events. -/
theorem qn_tailP {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m') (ht wd i gO gQ : ℕ)
    (vals : List E2 → (Fin L.t → Fin n) → List (List K) → Fin L.t → E2) (F : List Ev → ℕ × List ℕ)
    (E : List Ev) (hF : ∀ l, qcount l = 0 →
      F (E ++ l) = (i, List.ofFn fun k ↦ (Whir.qPos L (lastS (E ++ l) (L.kq + 2)) k : ℕ))) :
    QN F (Whir.tailP L Whir.chalE2 ht wd i gO gQ vals) E := by
  unfold Whir.tailP
  refine qn_bind_noq (Whir.follows_readFs _) (no_opn_replicate_rd _) fun l1 _ _ c1 ↦ ?_
  refine qn_bind_noq (os := [.cap ht wd]) ⟨rfl, rfl⟩ (by simp) fun l2 _ _ c2 ↦ ?_
  refine qn_bind_noq (os := [.smp]) ⟨rfl, fun _ ↦ rfl⟩ (by simp) fun l3 _ _ c3 ↦ ?_
  refine qn_bind_noq (Whir.follows_grp _ _) (no_opn_grp _) fun l4 _ _ c4 ↦ ?_
  refine qn_bind_noq Whir.follows_readF (by simp) fun l5 _ _ c5 ↦ ?_
  refine qn_bind (qn_of_follows F (Whir.follows_grp _ _) (no_opn_grp _) _) fun l6 qv h6 ↦ ?_
  obtain ⟨x, cs, rfl, hcs, rfl⟩ := grp6_after (g := gQ) (k := L.kq + 1) h6
  refine qn_bind (qn_query ?_) fun _ _ _ ↦ qn_ret _ _
  have h := hF (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ Ev.read x :: cs.map Ev.sample)
    (by simp only [qcount_append, c1, c2, c3, c4, c5, qcount_grp])
  have hl := lastS_grp (E ++ l1 ++ l2 ++ l3 ++ l4 ++ l5) x cs
  simp only [List.append_assoc] at h hl ⊢
  rw [h, ← hcs, hl]

/-- **The final level's query node** (`fin18`): commitment `4` at `fPos` of the position group's draws. -/
theorem qn_fin18 (F : List Ev → ℕ × List ℕ) (E : List Ev) (hF : ∀ l, qcount l = 0 →
      F (E ++ l) = (4, List.ofFn fun k ↦ (Whir.fPos Whir.fin18.Fv (lastS (E ++ l) (2 + 1)) k : ℕ)))
    (w : Whir.WtE.Wt (0 + 4)) (σ : E2) : QN F (Whir.ladP Whir.chalE2 (.fin Whir.fin18) w σ) E := by
  rw [Whir.ladP]
  unfold Whir.finP
  refine qn_bind_noq (Whir.follows_roundsP 10 4) (no_opn_rounds _) fun l1 _ _ c1 ↦ ?_
  refine qn_bind_noq (Whir.follows_readFs 12) (no_opn_replicate_rd _) fun l2 _ _ c2 ↦ ?_
  refine qn_bind (qn_of_follows F (Whir.follows_grp 13 2) (no_opn_grp _) _) fun l3 qv h3 ↦ ?_
  obtain ⟨x, cs, rfl, hcs, rfl⟩ := grp6_after (g := 13) (k := 2) h3
  refine qn_bind (qn_query ?_) fun _ _ _ ↦ qn_ite
    (fun _ ↦ qn_of_follows F (Whir.follows_sumP 2 _ _ 3 [] _) (no_opn_sum 3) _) fun _ ↦ qn_fail _
  have h := hF (l1 ++ l2 ++ Ev.read x :: cs.map Ev.sample)
    (by simp only [qcount_append, c1, c2, qcount_grp])
  have hl := lastS_grp (E ++ l1 ++ l2) x cs
  simp only [List.append_assoc] at h hl ⊢
  rw [h, ← hcs, hl]
  rfl

/-- **A level with a next one**: its interface's query node asks for `F`'s level positions, the rest's
after one more opening. -/
theorem qn_mid {n ℓ n' ℓ' : ℕ} (M : Whir.MidLv E2 Whir.WtE n ℓ n' ℓ') (rest : Whir.Lad E2 Whir.WtE n' ℓ')
    (F : List Ev → ℕ × List ℕ) (E : List Ev) (hF : ∀ l, qcount l = 0 →
      F (E ++ l) = (M.i, List.ofFn fun k ↦ (Whir.qPos M.L (lastS (E ++ l) (M.L.kq + 2)) k : ℕ)))
    (hrest : ∀ l w σ, qcount l = 1 → QN F (Whir.ladP Whir.chalE2 rest w σ) (E ++ l))
    (w : Whir.WtE.Wt (0 + ℓ)) (σ : E2) : QN F (Whir.ladP Whir.chalE2 (.mid M rest) w σ) E := by
  rw [Whir.ladP]
  refine qn_bind_noq (Whir.follows_roundsP _ _) (no_opn_rounds _) fun l1 rs _ c1 ↦ ?_
  refine qn_bind (qn_tailP _ _ _ _ _ _ _ F _ fun l hl ↦ ?_) fun l2 o h2 ↦ ?_
  · have h := hF (l1 ++ l) (by rw [qcount_append, c1, hl])
    simpa only [List.append_assoc] using h
  · have c2 := qcount_of_follows _ _ l2 (Whir.follows_tailP _ _ _ _ _ _ _) h2
    have h := hrest (l1 ++ l2) (M.wGlue (Whir.wFolds Whir.WtE ℓ rs w) o)
      (Whir.gluedC (Whir.foldsC ℓ rs σ) o.y o.lam o.c) (by
      rw [qcount_append, c1, c2]
      simp [Whir.tailOps, isOpn, List.countP_append, List.countP_replicate])
    simpa only [List.append_assoc] using h

/-! ## The opening at `P18` -/

/-- Level `j`'s positions of the last draws of the events (`qPos` of `mid_j`, then `fPos` of `fin18`). -/
noncomputable def posAt : ℕ → List Ev → List ℕ
  | 0, E => List.ofFn fun k ↦ (Whir.qPos Whir.mid0.L (lastS E (Whir.mid0.L.kq + 2)) k : ℕ)
  | 1, E => List.ofFn fun k ↦ (Whir.qPos Whir.mid1.L (lastS E (Whir.mid1.L.kq + 2)) k : ℕ)
  | 2, E => List.ofFn fun k ↦ (Whir.qPos Whir.mid2.L (lastS E (Whir.mid2.L.kq + 2)) k : ℕ)
  | 3, E => List.ofFn fun k ↦ (Whir.qPos Whir.mid3.L (lastS E (Whir.mid3.L.kq + 2)) k : ℕ)
  | _, E => List.ofFn fun k ↦ (Whir.fPos Whir.fin18.Fv (lastS E (2 + 1)) k : ℕ)

/-- **What the `j`-th opening asks for**: commitment `j` (`j` openings before it) at level `j`'s positions
of the draws just before it. -/
noncomputable def F18 (E : List Ev) : ℕ × List ℕ := (qcount E, posAt (qcount E) E)

/-- **Every query node of the deployed opening asks for `F18`** (any weight and claim). -/
theorem qn_whirP18 (w : Whir.WtE.Wt (0 + 6)) (σ : E2) : QN F18 (Whir.ladP Whir.chalE2 Whir.lad18 w σ) [] := by
  refine qn_mid Whir.mid0 _ F18 [] (fun l hl ↦ ?_) (fun l1 w1 σ1 h1 ↦ ?_) w σ
  · simp only [F18, List.nil_append, hl]
    rfl
  refine qn_mid Whir.mid1 _ F18 _ (fun l hl ↦ ?_) (fun l2 w2 σ2 h2 ↦ ?_) w1 σ1
  · simp only [F18, List.nil_append, qcount_append, h1, hl]
    rfl
  refine qn_mid Whir.mid2 _ F18 _ (fun l hl ↦ ?_) (fun l3 w3 σ3 h3 ↦ ?_) w2 σ2
  · simp only [F18, List.nil_append, qcount_append, h1, h2, hl]
    rfl
  refine qn_mid Whir.mid3 _ F18 _ (fun l hl ↦ ?_) (fun l4 w4 σ4 h4 ↦ ?_) w3 σ3
  · simp only [F18, List.nil_append, qcount_append, h1, h2, h3, hl]
    rfl
  refine qn_fin18 F18 _ (fun l hl ↦ ?_) w4 σ4
  simp only [F18, List.nil_append, qcount_append, h1, h2, h3, h4, hl]
  rfl

/-- **The opening's `(i, ps)` agreement**: V1's openings that carry `F18` agree with `whirP18`'s queries. -/
theorem qAgree_whirP18 (cl : (List E2 → E2) × E2) {vo : List V.Val} (h : RowsF F18 [] vo) :
    QAgree (Whir.whirP18 cl) vo :=
  qAgree_of_qn F18 _ vo [] (qn_whirP18 _ _) h

end Lvm6.Node
