-- New for lvm6 (WP N4-tail). `RunsO → afterV` with openings: the one check `replay` makes that `after` does not
-- (an opening value's commitment index and positions are the ones the program asks for), as `QAgree`.
import Lvm6NodeChildOk
import Lvm6QCRun

/-!
# `afterV` with openings (WP N4-tail)

`after` on events never sees an opening's `(i, ps)` (the event `.query rows` carries the rows only), `afterV`
(`replay`) checks them against the value `.rows i ps r`. **`QAgree p vs`**: walking `p` along `vs`, every
opening value carries the index and positions of the program's query at that point. **`afterV_of_after_q`**:
`after` on the events plus `QAgree` gives `afterV`; **`afterV_of_runsO_q`**: CC's `RunsO` on matching values
with `QAgree` returns on them. `qAgree_of_noRows`, `qAgree_bind_append` and `qAgree_query` decompose
`QAgree` along a program's binds.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open LeanVM.Parameters

/-- **The opening values carry the program's queries**: walking `p` along `vs`, each `.rows i' ps' r` met at
a `.query i ps` has `i' = i` and `ps' = ps` (nothing is asked elsewhere). -/
def QAgree {α : Type} : VerifierProgram α → List V.Val → Prop
  | .read k, .e x :: tr => QAgree (k x) tr
  | .sample k, .c x :: tr => QAgree (k x) tr
  | .commit ht w k, .cap ht' w' :: tr => ht = ht' ∧ w = w' → QAgree k tr
  | .query i ps k, .rows i' ps' r :: tr => i = i' ∧ ps = ps' ∧ QAgree (k r) tr
  | _, _ => True

/-- **`after` on the events and `QAgree` give `afterV`.** -/
theorem afterV_of_after_q {α : Type} : ∀ (p : VerifierProgram α) (vs : List V.Val) {q : VerifierProgram α},
    QAgree p vs → p.after (vs.map toEv) = some q → afterV p vs = some q
  | p, [], _, _, h => by simpa [afterV, VerifierProgram.after] using h
  | p, v :: vs, _, hq, h => by
    cases p <;> cases v <;> simp only [List.map_cons, toEv, VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact afterV_of_after_q _ vs hq h
      | (split at h
         · rename_i hc
           simp only [afterV, hc, and_self, ↓reduceIte]
           exact afterV_of_after_q _ vs (hq hc) h
         · simp at h)
      | (obtain ⟨rfl, rfl, hq⟩ := hq
         simp only [afterV, and_self, ↓reduceIte]
         exact afterV_of_after_q _ vs hq h)

/-- **A phase that `RunsO` on its slots returns on matching values whose openings agree.** -/
theorem afterV_of_runsO_q {β : Type} {M : Mem} {lay : List QC.OEv} {p : VerifierProgram β} {P : β → Prop}
    (h : QC.RunsO M lay p P) (hp : QC.PowLayO M lay) {vs : List V.Val}
    (he : QC.OEvMatch M lay (vs.map toEv)) (hq : QAgree p vs) :
    ∃ out, afterV p vs = some (.ret out) ∧ P out := by
  obtain ⟨out, h1, h2⟩ := h hp _ he
  exact ⟨out, afterV_of_after_q p vs hq h1, h2⟩

/-- Without opening values, `QAgree` holds. -/
theorem qAgree_of_noRows {α : Type} : ∀ (p : VerifierProgram α) (vs : List V.Val), NoRows vs → QAgree p vs
  | p, [], _ => by cases p <;> trivial
  | p, v :: vs, hn => by
    have hn' : NoRows vs := fun w hw ↦ hn w (List.mem_cons_of_mem _ hw)
    cases v with
    | rows i ps r => exact absurd rfl (hn _ (by simp) i ps r)
    | _ => cases p <;> first | trivial | exact qAgree_of_noRows _ vs hn' |
        exact fun _ ↦ qAgree_of_noRows _ vs hn'

/-- An opening at the query's index and positions. -/
theorem qAgree_query {α : Type} {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α}
    {r : List (List K)} {tr : List V.Val} (h : QAgree (k r) tr) :
    QAgree (.query i ps k) (.rows i ps r :: tr) :=
  ⟨rfl, rfl, h⟩

/-- **`QAgree` along a bind**: on the first part up to a return, then on the continuation. -/
theorem qAgree_bind_append {α β : Type} (f : α → VerifierProgram β) : ∀ (p : VerifierProgram α)
    (l₁ l₂ : List V.Val) {a : α}, QAgree p l₁ → afterV p l₁ = some (.ret a) → QAgree (f a) l₂ →
      QAgree (p >>= f) (l₁ ++ l₂)
  | p, [], l₂, _, _, h, h2 => by
    simp only [afterV, Option.some.injEq] at h
    subst h
    exact h2
  | p, v :: l₁, l₂, _, h1, h, h2 => by
    cases p <;> cases v <;> simp only [afterV, reduceCtorEq] at h
    all_goals first
      | exact qAgree_bind_append f _ l₁ l₂ h1 h h2
      | (split at h
         · rename_i hc
           exact fun _ ↦ qAgree_bind_append f _ l₁ l₂ (h1 hc) h h2
         · simp at h)
      | (split at h
         · rename_i hc
           obtain ⟨rfl, rfl⟩ := hc
           exact ⟨rfl, rfl, qAgree_bind_append f _ l₁ l₂ h1.2.2 h h2⟩
         · simp at h)

/-! ## Query nodes asking for a function of the events -/

/-- **Every query node `p` reaches asks for `F` of the events so far** (`E` before `p`, then `l`). -/
def QN (F : List Ev → ℕ × List ℕ) {α : Type} (p : VerifierProgram α) (E : List Ev) : Prop :=
  ∀ l i ps k, p.after l = some (.query i ps k) → (i, ps) = F (E ++ l)

/-- **V1's opening values are `F`'s**: each `.rows i ps r` of `vs` carries `F` of the events before it. -/
def RowsF (F : List Ev → ℕ × List ℕ) (E : List Ev) (vs : List V.Val) : Prop :=
  ∀ pre i ps r post, vs = pre ++ V.Val.rows i ps r :: post → (i, ps) = F (E ++ pre.map toEv)

theorem rowsF_cons {F : List Ev → ℕ × List ℕ} {E : List Ev} {v : V.Val} {tr : List V.Val}
    (h : RowsF F E (v :: tr)) : RowsF F (E ++ [toEv v]) tr := by
  intro pre i ps r post he
  have := h (v :: pre) i ps r post (by rw [he]; rfl)
  rw [this, List.map_cons, List.append_assoc]
  rfl

theorem qn_step {F : List Ev → ℕ × List ℕ} {α : Type} {p q : VerifierProgram α} {E : List Ev} {e : Ev}
    (h : QN F p E) (hs : ∀ l, p.after (e :: l) = q.after l) : QN F q (E ++ [e]) := by
  intro l i ps k hq
  rw [← hs] at hq
  rw [h _ i ps k hq, List.append_assoc]
  rfl

/-- **`QAgree` from the program's and V1's sides** of the same `F`. -/
theorem qAgree_of_qn (F : List Ev → ℕ × List ℕ) {α : Type} :
    ∀ (p : VerifierProgram α) (vs : List V.Val) (E : List Ev), QN F p E → RowsF F E vs → QAgree p vs
  | p, [], _, _, _ => by cases p <;> trivial
  | p, v :: tr, E, hq, hr => by
    have hr' := rowsF_cons hr
    cases p <;> cases v
    all_goals first
      | trivial
      | exact qAgree_of_qn F _ tr _ (qn_step hq fun _ ↦ rfl) hr'
      | (intro hc
         obtain ⟨rfl, rfl⟩ := hc
         refine qAgree_of_qn F _ tr _ (qn_step hq fun l ↦ ?_) hr'
         simp [toEv, VerifierProgram.after])
      | (rename_i i ps k i' ps' r
         have e1 := hq [] i ps k rfl
         have e2 := hr [] i' ps' r tr rfl
         rw [List.map_nil, ← e1] at e2
         obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
         exact ⟨rfl, rfl, qAgree_of_qn F _ tr _ (qn_step hq fun _ ↦ rfl) hr'⟩)

/-- **`QN` along a bind.** -/
theorem qn_bind {F : List Ev → ℕ × List ℕ} {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {E : List Ev} (hp : QN F p E) (hf : ∀ l a, p.after l = some (.ret a) → QN F (f a) (E ++ l)) :
    QN F (p >>= f) E := by
  intro l i ps k h
  rcases VerifierProgram.after_bind_cases f h with ⟨q, hq, he⟩ | ⟨a, l₁, l₂, rfl, h1, -, h2⟩
  · cases q with
    | ret a =>
      have he' : VerifierProgram.query i ps k = f a := he
      exact (hf l a hq [] i ps k (by rw [← he']; rfl)).trans (by rw [List.append_nil])
    | query i' ps' k' =>
      simp only [VerifierProgram.bind, VerifierProgram.query.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact hp l _ _ k' hq
    | _ => simp [VerifierProgram.bind] at he
  · rw [hf l₁ a h1 l₂ i ps k h2, List.append_assoc]

/-- A program following operations without openings reaches no query. -/
theorem noQuery_of_follows {α : Type} : ∀ (p : VerifierProgram α) {os : List Op}, Follows p os →
    (∀ i, Op.opn i ∉ os) → ∀ l i ps k, p.after l ≠ some (.query i ps k)
  | .query i _ _, os, h, hno, [], _, _, _, _ => hno i (List.mem_of_mem_head? h.1)
  | .ret _, _, _, _, [], _, _, _, he => by simp [VerifierProgram.after] at he
  | .fail, _, _, _, [], _, _, _, he => by simp [VerifierProgram.after] at he
  | .grind _ _, _, h, _, _, _, _, _, _ => h.elim
  | .read _, _, _, _, [], _, _, _, he => by simp [VerifierProgram.after] at he
  | .sample _, _, _, _, [], _, _, _, he => by simp [VerifierProgram.after] at he
  | .commit _ _ _, _, _, _, [], _, _, _, he => by simp [VerifierProgram.after] at he
  | .ret _, _, _, _, _ :: _, _, _, _, he => by simp [VerifierProgram.after] at he
  | .fail, _, _, _, _ :: _, _, _, _, he => by simp [VerifierProgram.after] at he
  | .read k, os, h, hno, e :: l, i, ps, k', he => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    exact noQuery_of_follows _ (h.2 _) (fun j hj ↦ hno j (List.mem_of_mem_tail hj)) l i ps k' he
  | .sample k, os, h, hno, e :: l, i, ps, k', he => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    exact noQuery_of_follows _ (h.2 _) (fun j hj ↦ hno j (List.mem_of_mem_tail hj)) l i ps k' he
  | .commit _ _ k, os, h, hno, e :: l, i, ps, k', he => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at he
    split at he
    · exact noQuery_of_follows _ h.2 (fun j hj ↦ hno j (List.mem_of_mem_tail hj)) l i ps k' he
    · simp at he
  | .query i _ _, os, h, hno, _ :: _, _, _, _, _ => hno i (List.mem_of_mem_head? h.1)

/-- **No query node in a program without openings.** -/
theorem qn_of_follows (F : List Ev → ℕ × List ℕ) {α : Type} {p : VerifierProgram α} {os : List Op}
    (h : Follows p os) (hno : ∀ i, Op.opn i ∉ os) (E : List Ev) : QN F p E :=
  fun l i ps k he ↦ absurd he (noQuery_of_follows p h hno l i ps k)

end Lvm6.Node
