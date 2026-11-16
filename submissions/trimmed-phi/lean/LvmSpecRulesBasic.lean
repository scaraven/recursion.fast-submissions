-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Compile/SpecRules/Basic.lean` (formal rev 40f877dc) as `LvmSpecRulesBasic` for lvm (WP-2).
/-
  LeanVM.Protocol.Compile.SpecRules.Basic

  Runs of a sequenced verifier program: where a run of `p.bind f` leaves `p`, the program and the
  local runs of a `bind` in terms of those of its parts, and the local runs from the empty
  history as the interactive runs.
-/
import LvmDslProg

-- ===== merged from `LvmDslSpec` (GOLF module merge: `LvmDslSpec.lean` is now a stub importing `LvmSpecRulesBasic`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Compile/Spec.lean` (formal rev 40f877dc) as `LvmDslSpec` for lvm (WP-2).
/-
  LeanVM.Protocol.Compile.Spec

  A compositional calculus for doom certificates: specifications of sub-programs of the verifier
  language with a doom predicate and an escape potential, composed through `bind`, and the
  doom certificate of a whole program they yield.
-/

/-!
# Specifications of verifier programs

A `Cert` (`LeanVM.Protocol.Compile.VerifierProgram`) is stated on whole histories of a whole
program. The
leanVM verifier is a long `do`-block of sub-programs (sumcheck rounds, the bus, the WHIR levels),
and its groups of challenges straddle sub-programs (the ring-switching challenges and the
opening's batching challenge; the query positions and the level's `λ`). `Spec` is a
specification of a sub-program, run after any history `h₀`, that composes through `bind` and
gives a `Cert` for the whole program (`Spec.toCert`).

A specification `Spec p Pre Post εmax L T` carries

* `D h₀ l`, a doom predicate on the local history `l` of a run of `p` after `h₀`, meaningful at
  boundaries (after a prover move), before moves, and where `p` returns;
* `V h₀ l ≤ 1`, an *escape potential*: an upper bound on the probability, over the challenges
  still to come in the current group, that the group ends outside doom, *including* the lead of
  whatever runs after `p` when `p` returns within the group. It is a supermartingale over
  challenges (`sample`), does not grow at openings (`query`), is `1` wherever doom fails at the
  end of a group or at a return (`moveEnd`, `retEnd`), is at least the follower's lead `T`
  (capped at `1`) at a return in doom (`retDoom`), and at every boundary in doom, discounted by
  the proof of work just passed, is at most `εmax` (`bound`);
* the lead `L`, the potential at the start under `Pre`.

`Pre` makes doom hold at the start; `Post` holds where `p` returns in doom. The fields other than
the start conditions hold for every `h₀`: a specification sets `V := 1` where its assumptions
fail.

Composition (`Spec.bind`): from `Spec p Pre Post εmax Lp Lf` and `Spec (f a) (Post a) Q εmax Lf T`
for every `a`, `Spec (p.bind f) Pre Q εmax Lp T`: inside `p` the potential is `p`'s, at a return
of `p` in doom it is `f`'s start (at most `Lf`, hence at most `p`'s by `retDoom`), and after it
`f`'s. An earlier formulation charged the follower's lead through a return probability in
`bound`; it double-counted returns outside doom and its `bind` rule was false (a checked
counterexample is recorded in the branch's notes). The leaves: `ret`, `fail`, a read, a sample
(with its bad-challenge count), a proof of work (whose boundary discounts the follower's lead), a
commitment, an opening, and a joint bound for a sub-program with no prover move
(`Spec.ofNoMove`), which is how the query positions of a WHIR level get their product bound.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

section

variable {α β : Type}

/-! ## Local runs -/

namespace VerifierProgram

/-- The node is a prover move: a read, a proof of work or a commitment. -/
def IsMove : VerifierProgram α → Prop
  | read _ => True
  | grind _ _ => True
  | commit _ _ _ => True
  | _ => False

/-- The runs of `p` started after the history `h₀`: local histories, every opening answered from
the words committed in `h₀` and before it in the run. -/
inductive Reach (p : VerifierProgram α) (h₀ : List Ev) : List Ev → Prop where
  | nil : Reach p h₀ []
  | read {l k} (x : E) : Reach p h₀ l → p.after l = some (read k) →
      Reach p h₀ (l ++ [Ev.read x])
  | sample {l k} (c : E) : Reach p h₀ l → p.after l = some (sample k) →
      Reach p h₀ (l ++ [Ev.sample c])
  | grind {l b k} : Reach p h₀ l → p.after l = some (grind b k) →
      Reach p h₀ (l ++ [Ev.grind b])
  | commit {l ht w k} (word : Word) : Reach p h₀ l → p.after l = some (commit ht w k) →
      WellShaped w word → Reach p h₀ (l ++ [Ev.commit ht w word])
  | query {l i ps k rows} : Reach p h₀ l → p.after l = some (query i ps k) →
      answer (h₀ ++ l) i ps = some rows → Reach p h₀ (l ++ [Ev.query rows])

end VerifierProgram

/-- A local history ends with a prover move. -/
def EndsMove (l : List Ev) : Prop :=
  match l.getLast? with
  | some (Ev.read _) => True
  | some (Ev.grind _) => True
  | some (Ev.commit _ _ _) => True
  | _ => False

/-! ## Specifications -/

/-- A **specification** of the sub-program `p`: see the module docstring. -/
structure Spec (p : VerifierProgram α) (Pre : List Ev → Prop) (Post : α → List Ev → Prop)
    (εmax L T : ENNReal) where
  /-- Doom, on the local history after `h₀`. -/
  D : List Ev → List Ev → Prop
  /-- The escape potential. -/
  V : List Ev → List Ev → ENNReal
  /-- The potential is a probability bound. -/
  le_one : ∀ h₀ l, V h₀ l ≤ 1
  /-- Doom at the start. -/
  start_D : ∀ h₀, Pre h₀ → D h₀ []
  /-- The lead. -/
  start_V : ∀ h₀, Pre h₀ → V h₀ [] ≤ L
  /-- A scalar keeps doom. -/
  read : ∀ {h₀ l k} (x : E), p.Reach h₀ l → p.after l = some (.read k) → D h₀ l →
    D h₀ (l ++ [Ev.read x])
  /-- A proof of work keeps doom. -/
  grind : ∀ {h₀ l b k}, p.Reach h₀ l → p.after l = some (.grind b k) → D h₀ l →
    D h₀ (l ++ [Ev.grind b])
  /-- A well-shaped commitment keeps doom. -/
  commit : ∀ {h₀ l ht w k} (word : Word), p.Reach h₀ l → p.after l = some (.commit ht w k) →
    WellShaped w word → D h₀ l → D h₀ (l ++ [Ev.commit ht w word])
  /-- The potential is a supermartingale over a challenge. -/
  sample : ∀ {h₀ l k}, p.Reach h₀ l → p.after l = some (.sample k) →
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, V h₀ (l ++ [Ev.sample c]) ≤ V h₀ l
  /-- An opening does not raise the potential. -/
  query : ∀ {h₀ l i ps k rows}, p.Reach h₀ l → p.after l = some (.query i ps k) →
    answer (h₀ ++ l) i ps = some rows → V h₀ (l ++ [Ev.query rows]) ≤ V h₀ l
  /-- Before a prover move outside doom, the potential is `1`. -/
  moveEnd : ∀ {h₀ l q}, p.Reach h₀ l → p.after l = some q → q.IsMove → ¬ D h₀ l → 1 ≤ V h₀ l
  /-- At a return outside doom, the potential is `1`. -/
  retEnd : ∀ {h₀ l a}, p.Reach h₀ l → p.after l = some (.ret a) → ¬ D h₀ l → 1 ≤ V h₀ l
  /-- At a return in doom, the potential covers the follower's lead. -/
  retDoom : ∀ {h₀ l a}, p.Reach h₀ l → p.after l = some (.ret a) → D h₀ l → min 1 T ≤ V h₀ l
  /-- Returning in doom gives the postcondition. -/
  post : ∀ {h₀ l a}, p.Reach h₀ l → p.after l = some (.ret a) → D h₀ l → Post a (h₀ ++ l)
  /-- At a boundary in doom, the discounted potential is at most `εmax`. -/
  bound : ∀ {h₀ l}, p.Reach h₀ l → l ≠ [] → EndsMove l → D h₀ l →
    (2 : ENNReal)⁻¹ ^ grindBits l * V h₀ l ≤ εmax

end
end LeanVM.Protocol.Compile
end
-- ===== end of `LvmDslSpec` =====

/-!
# Runs of a sequenced program

A run of `p.bind f` is a run of `p` until `p` returns a value `a`, then a run of `f a`.
`VerifierProgram.retSplit p l` finds the point at which `p` returns along the history `l`: it is
`some (a, l₁, l₂)` exactly when `l = l₁ ++ l₂` and `p` returns `a` after `l₁`
(`retSplit_eq_some_iff`), and otherwise `p` has not returned along `l` and `p.bind f` is at
`p`'s node, followed by `f` (`after_bind_of_retSplit_eq_none`).

## Main results

* `VerifierProgram.after_bind_of_after`, `VerifierProgram.after_bind_append`,
  `VerifierProgram.after_bind_cases`: the program after a history of `p.bind f`, inside `p`, after a
  return of `p`, and the converse decomposition.
* `Prog.reach_bind_cases`: a local run of `p.bind f` is a run of `p`, or a run of `p` to a
  return at `l₁` followed by a run of `f a` after `h₀ ++ l₁`.
* `VerifierProgram.reach_nil_iff`: the local runs from the empty history are the interactive runs.
* `endsMove_iff_boundary`: a nonempty history ends with a prover move exactly when it is a
  boundary.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

section

variable {α β : Type}

/-! ## Following a history in pieces

Moved here from leanVM's `LeanVM.Protocol.Compile.Prover` (the honest prover, which lvm does not
port), names and proofs kept. -/

/-- Following a history in two pieces. -/
theorem VerifierProgram.after_append {α : Type} :
    ∀ (P : VerifierProgram α) (h h' : List Ev), P.after (h ++ h') = (P.after h).bind fun p ↦
        p.after h'
  | _, [], _ => by simp [VerifierProgram.after]
  | P, e :: es, h' => by
    cases P <;> cases e <;> simp only [List.cons_append, VerifierProgram.after,
        Option.bind_none] <;>
      first
      | exact VerifierProgram.after_append _ es h'
      | (split <;> simp [VerifierProgram.after_append _ es h'])

/-- One more event, after a history that leads to `p`, is read by `p`. -/
theorem VerifierProgram.after_append_single {α : Type} {P p : VerifierProgram α} {h : List Ev}
    (e : Ev)
    (ha : P.after h = some p) : P.after (h ++ [e]) = p.after [e] := by
  rw [VerifierProgram.after_append, ha, Option.bind_some]

namespace VerifierProgram

/-! ## Where a run leaves `p` -/

/-- The point at which `p` returns along the history `l`: the value returned, the history up to
the return, and the rest; `none` if `p` does not return along `l`. -/
def retSplit : VerifierProgram α → List Ev → Option (α × List Ev × List Ev)
  | ret a, l => some (a, [], l)
  | read k, Ev.read x :: es =>
    ((k x).retSplit es).map fun s ↦ (s.1, Ev.read x :: s.2.1, s.2.2)
  | sample k, Ev.sample c :: es =>
    ((k c).retSplit es).map fun s ↦ (s.1, Ev.sample c :: s.2.1, s.2.2)
  | grind b k, Ev.grind b' :: es =>
    if b = b' then (k.retSplit es).map fun s ↦ (s.1, Ev.grind b' :: s.2.1, s.2.2) else none
  | commit h w k, Ev.commit h' w' word :: es =>
    if h = h' ∧ w = w' then
      (k.retSplit es).map fun s ↦ (s.1, Ev.commit h' w' word :: s.2.1, s.2.2)
    else none
  | query _ _ k, Ev.query rows :: es =>
    ((k rows).retSplit es).map fun s ↦ (s.1, Ev.query rows :: s.2.1, s.2.2)
  | _, _ => none

/-- `retSplit` finds a return of `p`. -/
theorem retSplit_spec : ∀ (p : VerifierProgram α) (l : List Ev) {a : α} {l₁ l₂ : List Ev},
    p.retSplit l = some (a, l₁, l₂) → l = l₁ ++ l₂ ∧ p.after l₁ = some (ret a)
  | ret _, l, _, _, _, h => by
    simp only [retSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [after]
  | fail, l, _, _, _, h => by cases l <;> simp [retSplit] at h
  | read k, [], _, _, _, h => by simp [retSplit] at h
  | sample k, [], _, _, _, h => by simp [retSplit] at h
  | grind _ k, [], _, _, _, h => by simp [retSplit] at h
  | commit _ _ k, [], _, _, _, h => by simp [retSplit] at h
  | query _ _ k, [], _, _, _, h => by simp [retSplit] at h
  | read k, e :: es, _, _, _, h => by
    cases e <;> simp only [retSplit, Option.map_eq_some_iff, reduceCtorEq] at h
    obtain ⟨⟨a', m₁, m₂⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨rfl, h2⟩ := retSplit_spec _ es hs
    exact ⟨rfl, by simpa [after] using h2⟩
  | sample k, e :: es, _, _, _, h => by
    cases e <;> simp only [retSplit, Option.map_eq_some_iff, reduceCtorEq] at h
    obtain ⟨⟨a', m₁, m₂⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨rfl, h2⟩ := retSplit_spec _ es hs
    exact ⟨rfl, by simpa [after] using h2⟩
  | query _ _ k, e :: es, _, _, _, h => by
    cases e <;> simp only [retSplit, Option.map_eq_some_iff, reduceCtorEq] at h
    obtain ⟨⟨a', m₁, m₂⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨rfl, h2⟩ := retSplit_spec _ es hs
    exact ⟨rfl, by simpa [after] using h2⟩
  | grind b k, e :: es, _, _, _, h => by
    cases e <;> simp only [retSplit, reduceCtorEq] at h
    rename_i b'
    split at h
    · subst b'
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨a', m₁, m₂⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨rfl, h2⟩ := retSplit_spec _ es hs
      exact ⟨rfl, by simpa [after] using h2⟩
    · simp at h
  | commit ht w k, e :: es, _, _, _, h => by
    cases e <;> simp only [retSplit, reduceCtorEq] at h
    rename_i ht' w' word
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨a', m₁, m₂⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨rfl, h2⟩ := retSplit_spec _ es hs
      exact ⟨rfl, by simpa [after] using h2⟩
    · simp at h

/-- A return of `p` is the one `retSplit` finds. -/
theorem retSplit_of_after : ∀ (p : VerifierProgram α) (l₁ l₂ : List Ev) {a : α},
    p.after l₁ = some (ret a) → p.retSplit (l₁ ++ l₂) = some (a, l₁, l₂)
  | p, [], l₂, _, h => by
    simp only [after, Option.some.injEq] at h
    subst h
    rfl
  | p, e :: es, l₂, _, h => by
    cases p <;> cases e <;> simp only [after, reduceCtorEq] at h
    all_goals first
      | (simp only [List.cons_append, retSplit, retSplit_of_after _ es l₂ h, Option.map_some])
      | (split at h
         · rename_i hc
           simp only [List.cons_append, retSplit, hc, and_self, ↓reduceIte,
             retSplit_of_after _ es l₂ h, Option.map_some]
         · simp at h)

/-- `retSplit` characterised. -/
theorem retSplit_eq_some_iff {p : VerifierProgram α} {l : List Ev} {a : α} {l₁ l₂ : List Ev} :
    p.retSplit l = some (a, l₁, l₂) ↔ l = l₁ ++ l₂ ∧ p.after l₁ = some (ret a) :=
  ⟨retSplit_spec p l, fun ⟨h1, h2⟩ ↦ h1 ▸ retSplit_of_after p l₁ l₂ h2⟩

/-- Where `retSplit` finds nothing, `p` is not at a return. -/
theorem after_ne_ret_of_retSplit_eq_none {p : VerifierProgram α} {l : List Ev}
    (hs : p.retSplit l = none) (a : α) : p.after l ≠ some (ret a) := fun h ↦ by
  simpa [hs] using retSplit_of_after p l [] h

/-- Extending a history past a return of `p` extends the rest. -/
theorem retSplit_append {p : VerifierProgram α} {l : List Ev} {a : α} {l₁ l₂ : List Ev} (l' :
    List Ev)
    (hs : p.retSplit l = some (a, l₁, l₂)) : p.retSplit (l ++ l') = some (a, l₁, l₂ ++ l') := by
  obtain ⟨rfl, h⟩ := retSplit_eq_some_iff.1 hs
  exact retSplit_eq_some_iff.2 ⟨by simp, h⟩

/-- One event after a history along which `p` has not returned: if `p` returns now, it returns
at the new history. -/
theorem retSplit_concat {p : VerifierProgram α} {l : List Ev} {e : Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = none) (hs' : p.retSplit (l ++ [e]) = some (a, l₁, l₂)) :
    l₁ = l ++ [e] ∧ l₂ = [] := by
  obtain ⟨he, h⟩ := retSplit_eq_some_iff.1 hs'
  rcases List.eq_nil_or_concat l₂ with rfl | ⟨L, e', rfl⟩
  · simpa using he.symm
  · rw [List.concat_eq_append, ← List.append_assoc] at he
    obtain ⟨rfl, -⟩ := List.append_inj' he rfl
    simp [retSplit_of_after p l₁ L h] at hs

/-- One more event after a history that leads to `p` is read by `p`. -/
theorem after_snoc {P p : VerifierProgram α} {l : List Ev} (e : Ev) (ha : P.after l = some p) :
    P.after (l ++ [e]) = p.after [e] :=
  after_append_single e ha

/-! ## The program after a history of a `bind` -/

/-- Inside `p`, `p.bind f` is at `p`'s node followed by `f`. -/
theorem after_bind_of_after (f : α → VerifierProgram β) :
    ∀ (p : VerifierProgram α) (l : List Ev) {q : VerifierProgram α}, p.after l = some q →
      (p.bind f).after l = some (q.bind f)
  | p, [], _, h => by simp only [after, Option.some.injEq] at h; simp [after, h]
  | p, e :: es, _, h => by
    cases p <;> cases e <;> simp only [after, reduceCtorEq] at h
    all_goals first
      | exact after_bind_of_after f _ es h
      | (split at h
         · rename_i hc
           simp only [bind, after, hc, and_self, ↓reduceIte]
           exact after_bind_of_after f _ es h
         · simp at h)

/-- After a return of `p` at `l₁`, `p.bind f` runs `f a`. -/
theorem after_bind_append (f : α → VerifierProgram β) {p : VerifierProgram α} {l₁ : List Ev} {a : α}
    (h : p.after l₁ = some (ret a)) (l₂ : List Ev) :
    (p.bind f).after (l₁ ++ l₂) = (f a).after l₂ := by
  rw [VerifierProgram.after_append, after_bind_of_after f p l₁ h]
  rfl

/-- Where `retSplit` finds the return of `p`, `p.bind f` runs `f`. -/
theorem after_bind_of_retSplit_eq_some (f : α → VerifierProgram β) {p : VerifierProgram α} {l : List
    Ev} {a : α}
    {l₁ l₂ : List Ev} (hs : p.retSplit l = some (a, l₁, l₂)) :
    (p.bind f).after l = (f a).after l₂ := by
  obtain ⟨rfl, h⟩ := retSplit_eq_some_iff.1 hs
  exact after_bind_append f h l₂

/-- Where `retSplit` finds nothing, `p.bind f` is at `p`'s node, followed by `f`. -/
theorem after_bind_of_retSplit_eq_none (f : α → VerifierProgram β) :
    ∀ (p : VerifierProgram α) (l : List Ev), p.retSplit l = none →
      (p.bind f).after l = (p.after l).map fun q ↦ q.bind f
  | p, [], _ => by simp [after]
  | ret a, e :: es, h => by simp [retSplit] at h
  | fail, e :: es, _ => by simp [bind, after]
  | p, e :: es, h => by
    cases p <;> cases e <;> simp only [retSplit, reduceCtorEq, Option.map_eq_none_iff] at h <;>
      simp only [bind, after, Option.map_none]
    all_goals first
      | exact after_bind_of_retSplit_eq_none f _ es h
      | (split at h
         · rename_i hc
           simp only [hc, and_self, ↓reduceIte]
           exact after_bind_of_retSplit_eq_none f _ es (Option.map_eq_none_iff.1 h)
         · rename_i hc
           simp [hc])

/-- The converse decomposition: a node of `p.bind f` is `p`'s followed by `f`, or `f a`'s after
a return of `p` and at least one more event. -/
theorem after_bind_cases (f : α → VerifierProgram β) {p : VerifierProgram α} {l : List Ev} {r :
    VerifierProgram β}
    (h : (p.bind f).after l = some r) :
    (∃ q, p.after l = some q ∧ r = q.bind f) ∨
      ∃ a l₁ l₂, l = l₁ ++ l₂ ∧ p.after l₁ = some (ret a) ∧ l₂ ≠ [] ∧ (f a).after l₂ = some r := by
  rcases hs : p.retSplit l with _ | ⟨a, l₁, l₂⟩
  · rw [after_bind_of_retSplit_eq_none f p l hs] at h
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .inl ⟨q, hq, rfl⟩
  · obtain ⟨rfl, h1⟩ := retSplit_eq_some_iff.1 hs
    rw [after_bind_append f h1] at h
    by_cases h2 : l₂ = []
    · subst h2
      simp only [after, Option.some.injEq] at h
      exact .inl ⟨ret a, by simpa using h1, h.symm⟩
    · exact .inr ⟨a, l₁, l₂, rfl, h1, h2, h⟩

/-- A node of `p.bind f` inside `p` is `p`'s node followed by `f`: of the same kind, unless `p`
returns. -/
theorem bind_isMove {q : VerifierProgram α} {f : α → VerifierProgram β} (hq : ∀ a, q ≠ ret a) :
    (q.bind f).IsMove ↔ q.IsMove := by
  cases q with
  | ret a => exact absurd rfl (hq a)
  | _ => simp [bind, IsMove]

/-! ## Local runs of a `bind` -/

/-- A local run reaches a node. -/
theorem Reach.after_isSome {p : VerifierProgram α} {h₀ l : List Ev} (hl : p.Reach h₀ l) :
    ∃ q, p.after l = some q := by
  induction hl with
  | nil => simp [after]
  | read _ _ ha | sample _ _ ha | grind _ ha | commit _ _ ha | query _ ha =>
    rw [after_append_single _ ha]
    simp [after]

/-- The two cases of a local run of `p.bind f`. -/
private def BindRun (p : VerifierProgram α) (f : α → VerifierProgram β) (h₀ l : List Ev) : Prop :=
  (p.retSplit l = none → p.Reach h₀ l) ∧
    ∀ a l₁ l₂, p.retSplit l = some (a, l₁, l₂) → p.Reach h₀ l₁ ∧ (f a).Reach (h₀ ++ l₁) l₂

private theorem bindRun_step {p : VerifierProgram α} {f : α → VerifierProgram β} {h₀ l : List Ev}
    (e : Ev)
    (ih : BindRun p f h₀ l)
    (hp : p.Reach h₀ l → p.retSplit l = none → p.Reach h₀ (l ++ [e]))
    (hf : ∀ a l₁ l₂, l = l₁ ++ l₂ → (f a).Reach (h₀ ++ l₁) l₂ →
      (f a).after l₂ = (p.bind f).after l → (f a).Reach (h₀ ++ l₁) (l₂ ++ [e])) :
    BindRun p f h₀ (l ++ [e]) := by
  rcases hs : p.retSplit l with _ | ⟨a, l₁, l₂⟩
  · have hr := hp (ih.1 hs) hs
    refine ⟨fun _ ↦ hr, fun a l₁ l₂ hs' ↦ ?_⟩
    obtain ⟨rfl, rfl⟩ := retSplit_concat hs hs'
    exact ⟨hr, .nil⟩
  · obtain ⟨h1, h2⟩ := ih.2 a l₁ l₂ hs
    have hs' := retSplit_append [e] hs
    refine ⟨fun h ↦ by simp [h] at hs', fun a' l₁' l₂' h ↦ ?_⟩
    rw [hs'] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨h1, hf a l₁ l₂ (retSplit_eq_some_iff.1 hs).1 h2
      (after_bind_of_retSplit_eq_some f hs).symm⟩

private theorem bindRun {p : VerifierProgram α} {f : α → VerifierProgram β} {h₀ l : List Ev}
    (hl : (p.bind f).Reach h₀ l) : BindRun p f h₀ l := by
  induction hl with
  | nil => exact ⟨fun _ ↦ .nil, fun a l₁ l₂ h ↦ by
      obtain ⟨he, h1⟩ := retSplit_eq_some_iff.1 h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
      exact ⟨.nil, .nil⟩⟩
  | @read l k x _ ha ih =>
    refine bindRun_step _ ih (fun hr hs ↦ ?_) (fun a l₁ l₂ _ hf he ↦ .read x hf (he.trans ha))
    obtain ⟨q, hq⟩ := hr.after_isSome
    rw [after_bind_of_retSplit_eq_none f p l hs, hq] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    cases q <;> simp [bind] at ha
    · exact absurd hq (after_ne_ret_of_retSplit_eq_none hs _)
    · exact .read x hr hq
  | @sample l k c _ ha ih =>
    refine bindRun_step _ ih (fun hr hs ↦ ?_) (fun a l₁ l₂ _ hf he ↦ .sample c hf (he.trans ha))
    obtain ⟨q, hq⟩ := hr.after_isSome
    rw [after_bind_of_retSplit_eq_none f p l hs, hq] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    cases q <;> simp [bind] at ha
    · exact absurd hq (after_ne_ret_of_retSplit_eq_none hs _)
    · exact .sample c hr hq
  | @grind l b k _ ha ih =>
    refine bindRun_step _ ih (fun hr hs ↦ ?_) (fun a l₁ l₂ _ hf he ↦ .grind hf (he.trans ha))
    obtain ⟨q, hq⟩ := hr.after_isSome
    rw [after_bind_of_retSplit_eq_none f p l hs, hq] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    cases q <;> simp [bind] at ha
    · exact absurd hq (after_ne_ret_of_retSplit_eq_none hs _)
    · obtain ⟨rfl, -⟩ := ha
      exact .grind hr hq
  | @commit l ht w k word _ ha hw ih =>
    refine bindRun_step _ ih (fun hr hs ↦ ?_)
      (fun a l₁ l₂ _ hf he ↦ .commit word hf (he.trans ha) hw)
    obtain ⟨q, hq⟩ := hr.after_isSome
    rw [after_bind_of_retSplit_eq_none f p l hs, hq] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    cases q <;> simp [bind] at ha
    · exact absurd hq (after_ne_ret_of_retSplit_eq_none hs _)
    · obtain ⟨rfl, rfl, -⟩ := ha
      exact .commit word hr hq hw
  | @query l i ps k rows _ ha hans ih =>
    refine bindRun_step _ ih (fun hr hs ↦ ?_) (fun a l₁ l₂ hl hf he ↦
      .query hf (he.trans ha) (by rw [List.append_assoc, ← hl]; exact hans))
    obtain ⟨q, hq⟩ := hr.after_isSome
    rw [after_bind_of_retSplit_eq_none f p l hs, hq] at ha
    simp only [Option.map_some, Option.some.injEq] at ha
    cases q <;> simp [bind] at ha
    · exact absurd hq (after_ne_ret_of_retSplit_eq_none hs _)
    · obtain ⟨rfl, rfl, -⟩ := ha
      exact .query hr hq hans

/-- A local run of `p.bind f` along which `p` has not returned is a run of `p`. -/
theorem reach_of_reach_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {h₀ l : List Ev}
    (hl : (p.bind f).Reach h₀ l) (hs : p.retSplit l = none) : p.Reach h₀ l :=
  (bindRun hl).1 hs

/-- A local run of `p.bind f` past a return of `p` is a run of `p` to the return followed by a
run of `f a`. -/
theorem reach_of_reach_bind_of_retSplit {p : VerifierProgram α} {f : α → VerifierProgram β} {h₀ l :
    List Ev}
    {a : α} {l₁ l₂ : List Ev} (hl : (p.bind f).Reach h₀ l) (hs : p.retSplit l = some (a, l₁, l₂)) :
    p.Reach h₀ l₁ ∧ (f a).Reach (h₀ ++ l₁) l₂ :=
  (bindRun hl).2 a l₁ l₂ hs

/-! ## Runs from the empty history -/

/-- The local runs from the empty history are the interactive runs. -/
theorem reach_nil_iff {P : VerifierProgram α} {l : List Ev} : P.Reach [] l ↔ P.Reachable l := by
  constructor
  · intro hl
    induction hl with
    | nil => exact .nil
    | read x _ ha ih => exact .read x ih ha
    | sample c _ ha ih => exact .sample c ih ha
    | grind _ ha ih => exact .grind ih ha
    | commit word _ ha hw ih => exact .commit word ih ha hw
    | query _ ha hans ih => exact .query ih ha (by simpa using hans)
  · intro hl
    induction hl with
    | nil => exact .nil
    | read x _ ha ih => exact .read x ih ha
    | sample c _ ha ih => exact .sample c ih ha
    | grind _ ha ih => exact .grind ih ha
    | commit word _ ha hw ih => exact .commit word ih ha hw
    | query _ ha hans ih => exact .query ih ha (by simpa using hans)

end VerifierProgram

/-! ## Boundaries -/

/-- A nonempty history ends with a prover move exactly when it is a boundary. -/
theorem endsMove_iff_boundary {l : List Ev} (hl : l ≠ []) : EndsMove l ↔ Boundary l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons e es => rfl

/-- Ending with a prover move is decided by a nonempty suffix. -/
theorem endsMove_append {l₁ l₂ : List Ev} (h : l₂ ≠ []) : EndsMove (l₁ ++ l₂) ↔ EndsMove l₂ := by
  unfold EndsMove
  rw [List.getLast?_append_of_ne_nil _ h]

/-- The proof-of-work bits ending a history are decided by a nonempty suffix. -/
theorem grindBits_append {l₁ l₂ : List Ev} (h : l₂ ≠ []) : grindBits (l₁ ++ l₂) = grindBits l₂ := by
  unfold grindBits
  rw [List.getLast?_append_of_ne_nil _ h]

end
end LeanVM.Protocol.Compile
