-- New for lvm6 (WP LEN, F-X8b-1): the bytes an accepting compiled run consumes, counted from the
-- operations the program follows (`Follows`) with each operation's width.
import Lvm6AsmProg

/-!
# The body length of an accepting run (LEN)

`Follows p os` fixes the kinds of the transcript operations but not how many positions a query
opens. Here:

* **`QLen t p`**: every query of `p` to commitment `i` opens `t i` positions. A program following an
  operation list without openings has it for every `t` (`qlen_of_follows`); it composes through
  `bind` (`QLen.bind`).
* **`opB cO oc t cs ws os`**: the bytes of `os` when the reads take the widths `ws` in order (8 past
  the end), a cap of `2^ht` rows of `w` words takes `32 · 2^(cO ht w)` bytes and records its shape,
  and an opening of commitment `i` (shape `(ht, w, lv)` in `cs`) takes `t i · (8 · min (oc ht w) w +
  32 · (ht − lv))` bytes (leaf and path, `Scheme.openAll`).
* **`trun_len`**: an accepting `Scheme.trun` of a program that follows `os` and has `QLen t` consumes
  exactly `opB S.capOf S.occ t (shapes of caps) ws os` bytes of its body, when the scheme's read
  widths from the history's read index on are `ws`.
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters LeanVM.Protocol.Compile Lvm.FS

/-! ## `QLen`: the number of positions each query opens -/

/-- **Every query to commitment `i` opens `t i` positions.** -/
def QLen {α : Type} (t : ℕ → ℕ) : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .grind _ k => QLen t k
  | .read k => ∀ x, QLen t (k x)
  | .sample k => ∀ c, QLen t (k c)
  | .commit _ _ k => QLen t k
  | .query i ps k => ps.length = t i ∧ ∀ r, QLen t (k r)

/-- An operation list without openings. -/
def NoOpn (os : List Op) : Prop := ∀ i, Op.opn i ∉ os

section QLen

variable {α β : Type} {t : ℕ → ℕ}

theorem QLen.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : QLen t p)
    (hf : ∀ a, QLen t (f a)) : QLen t (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | grind _ _ ih => exact ih hp
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | commit _ _ _ ih => exact ih hp
  | query i ps k ih => exact ⟨hp.1, fun r ↦ ih r (hp.2 r)⟩

theorem QLen.bind' {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : QLen t p)
    (hf : ∀ a, QLen t (f a)) : QLen t (p >>= f) :=
  QLen.bind hp hf

theorem NoOpn.tail {o : Op} {os : List Op} (h : NoOpn (o :: os)) : NoOpn os :=
  fun i hi ↦ h i (List.mem_cons_of_mem _ hi)

theorem NoOpn.tail' {os : List Op} (h : NoOpn os) : NoOpn os.tail := by
  cases os with
  | nil => exact h
  | cons o os => exact h.tail

/-- **A program following an operation list without openings asks no query.** -/
theorem qlen_of_follows : ∀ {p : VerifierProgram α} {os : List Op}, Follows p os → NoOpn os →
    QLen t p
  | .ret _, _, _, _ => trivial
  | .fail, _, _, _ => trivial
  | .grind _ _, _, h, _ => h.elim
  | .read _, _, h, ho => fun x ↦ qlen_of_follows (h.2 x) ho.tail'
  | .sample _, _, h, ho => fun c ↦ qlen_of_follows (h.2 c) ho.tail'
  | .commit _ _ k, _, h, ho => qlen_of_follows (p := k) h.2 ho.tail'
  | .query i _ _, os, h, ho => by
    obtain ⟨h1, -⟩ := h
    exfalso
    cases os with
    | nil => simp at h1
    | cons o os =>
      have h2 : o = .opn i := by simpa using h1
      exact ho i (h2 ▸ List.mem_cons_self)

theorem qlen_ite {c : Prop} [Decidable c] {p q : VerifierProgram α} (hp : c → QLen t p)
    (hq : ¬ c → QLen t q) : QLen t (if c then p else q) := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

end QLen

/-- An operation list without openings, as a Boolean. -/
def noOpnB (os : List Op) : Bool := os.all fun o ↦ match o with | .opn _ => false | _ => true

theorem noOpn_of (os : List Op) (h : noOpnB os = true) : NoOpn os := by
  intro i hi
  have := List.all_eq_true.1 h _ hi
  simp at this

/-! ## Counting bytes -/

/-- **The bytes of an operation list** (see the module docstring); `cs` holds the shapes
`(ht, w, lv)` of the commitments so far, `ws` the widths of the reads to come. -/
def opB (cO oc : ℕ → ℕ → ℕ) (t : ℕ → ℕ) : List (ℕ × ℕ × ℕ) → List ℕ → List Op → ℕ
  | _, _, [] => 0
  | cs, ws, .rd :: os => ws.getD 0 8 + opB cO oc t cs ws.tail os
  | cs, ws, .smp :: os => opB cO oc t cs ws os
  | cs, ws, .cap ht w :: os => 32 * 2 ^ cO ht w + opB cO oc t (cs ++ [(ht, w, cO ht w)]) ws os
  | cs, ws, .opn i :: os =>
    (match cs[i]? with
      | some (ht, w, lv) => t i * (8 * min (oc ht w) w + 32 * (ht - lv))
      | none => 0) + opB cO oc t cs ws os

/-- The shape of a commitment record. -/
def shp (ci : CapI) : ℕ × ℕ × ℕ := (ci.ht, ci.wd, ci.lv)

namespace Len

variable (S : Scheme) (L : Log)

theorem climb_len : ∀ (n : ℕ) (d : Digest) (q : ℕ) (body : Bytes) (top : Digest) (rest : Bytes),
    (Scheme.climb n d q body).runLog L = some (some (top, rest)) → body.length = 32 * n + rest.length
  | 0, d, q, body, top, rest, h => by
    simp only [Scheme.climb, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp
  | n + 1, d, q, body, top, rest, h => by
    unfold Scheme.climb at h
    split at h
    · simp [OProg.runLog] at h
    · rename_i hb
      simp only [OProg.runLog] at h
      obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.1 h
      have := climb_len n e.2 (q / 2) (body.drop 32) top rest h
      rw [List.length_drop] at this
      omega

theorem openOne_len (ci : CapI) (p : ℕ) (body : Bytes) (r : List K) (rest : Bytes)
    (h : (S.openOne ci p body).runLog L = some (some (r, rest))) :
    body.length = S.lb ci + 32 * (ci.ht - ci.lv) + rest.length := by
  unfold Scheme.openOne at h
  split at h
  · simp [OProg.runLog] at h
  · rename_i hb
    simp only [OProg.runLog] at h
    obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.1 h
    try simp only at h
    rw [OProgFacts.runLog_bind] at h
    obtain ⟨o, hc, h⟩ := Option.bind_eq_some_iff.1 h
    rcases o with _ | ⟨top, rest'⟩
    · simp [OProg.runLog] at h
    · simp only [OProg.runLog] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := climb_len L _ _ _ _ _ _ hc
        rw [List.length_drop] at this
        omega
      · simp at h

theorem openAll_len (ci : CapI) : ∀ (ps : List ℕ) (body : Bytes) (rows : List (List K)) (rest : Bytes),
    (S.openAll ci ps body).runLog L = some (some (rows, rest)) →
    body.length = ps.length * (S.lb ci + 32 * (ci.ht - ci.lv)) + rest.length
  | [], body, rows, rest, h => by
    simp only [Scheme.openAll, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp
  | p :: ps, body, rows, rest, h => by
    simp only [Scheme.openAll] at h
    rw [OProgFacts.runLog_bind] at h
    obtain ⟨o, h1, h⟩ := Option.bind_eq_some_iff.1 h
    rcases o with _ | ⟨r, rest₁⟩
    · simp [OProg.runLog] at h
    · try simp only at h
      rw [OProgFacts.runLog_bind] at h
      obtain ⟨o', h2, h⟩ := Option.bind_eq_some_iff.1 h
      rcases o' with _ | ⟨rs, rest₂⟩
      · simp [OProg.runLog] at h
      · simp only [OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have e1 := openOne_len S L ci p body r rest₁ h1
        have e2 := openAll_len ci ps rest₁ rs rest₂ h2
        rw [List.length_cons, e1, e2]
        ring

theorem getD_tail (ws : List ℕ) (k : ℕ) : ws.tail.getD k 8 = ws.getD (k + 1) 8 := by
  cases ws <;> simp

/-- **An accepting run consumes `opB` bytes**: if `trun` accepts a program that follows `os`, whose
queries open `t i` positions, and the reads from the history's index on take the widths `ws`, the
body has `opB S.capOf S.occ t (shapes of caps) ws os` bytes. -/
theorem trun_len (t : ℕ → ℕ) : ∀ (p : VerifierProgram Bool) (os : List Op) (ws : List ℕ)
    (st : Digest) (buf : Bytes) (caps : List CapI) (body : Bytes) (h h' : List Ev),
    Follows p os → QLen t p → (∀ k, S.rw (nReads h + k) = ws.getD k 8) →
    S.trun L p st buf caps body h = some (true, h') →
    body.length = opB S.capOf S.occ t (caps.map shp) ws os := by
  intro p
  induction p with
  | ret b =>
    intro os ws st buf caps body h h' hF _ _ hr
    have hos : os = [] := hF
    subst hos
    simp only [Scheme.trun, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hr
    have := hr.1.2
    simp only [List.isEmpty_iff] at this
    simp [this, opB]
  | fail => intro _ _ _ _ _ _ _ _ _ _ _ hr; simp [Scheme.trun] at hr
  | grind _ _ _ => intro _ _ _ _ _ _ _ _ hF; exact hF.elim
  | read k ih =>
    intro os ws st buf caps body h h' hF hQ hw hr
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      have ho : o = .rd := by simpa using h1
      subst ho
      simp only [Scheme.trun] at hr
      split at hr
      · simp at hr
      · rename_i hb
        have hw' : ∀ j, S.rw (nReads (h ++ [Ev.read (S.decE (List.take (S.rw (nReads h)) body))]) + j) =
            ws.tail.getD j 8 := by
          intro j
          rw [getD_tail, ← hw (j + 1), nReads_read, Nat.add_assoc, Nat.add_comm 1 j]
        have := ih _ os ws.tail st _ caps _ _ h' (h2 _) (hQ _) hw' hr
        rw [List.length_drop] at this
        have h0 := hw 0
        simp only [Nat.add_zero] at h0
        simp only [opB]
        omega
  | sample k ih =>
    intro os ws st buf caps body h h' hF hQ hw hr
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      have ho : o = .smp := by simpa using h1
      subst ho
      simp only [Scheme.trun] at hr
      split at hr
      · obtain ⟨e, -, hr⟩ := Option.bind_eq_some_iff.1 hr
        have hw' : ∀ j, S.rw (nReads (h ++ [Ev.sample (S.chal e.2)]) + j) = ws.getD j 8 := by
          intro j; rw [nReads_sample]; exact hw j
        exact ih _ os ws _ _ caps body _ h' (h2 _) (hQ _) hw' hr
      · simp at hr
  | commit ht w k ih =>
    intro os ws st buf caps body h h' hF hQ hw hr
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      have ho : o = .cap ht w := by simpa using h1
      subst ho
      simp only [Scheme.trun] at hr
      split at hr
      · simp at hr
      · rename_i hb
        have hw' : ∀ j, S.rw (nReads (h ++ [Ev.commit ht w (S.wordOf L (S.capI ht w body))]) + j) =
            ws.getD j 8 := by
          intro j; rw [nReads_commit]; exact hw j
        have := ih os ws st _ _ _ _ h' h2 hQ hw' hr
        rw [List.length_drop, List.map_append] at this
        simp only [opB]
        have hc : S.capBytes ht w = 32 * 2 ^ S.capOf ht w := rfl
        have hs : shp (S.capI ht w body) = (ht, w, S.capOf ht w) := rfl
        rw [List.map_singleton, hs] at this
        rw [← hc]
        omega
  | query i ps k ih =>
    intro os ws st buf caps body h h' hF hQ hw hr
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      have ho : o = .opn i := by simpa using h1
      subst ho
      obtain ⟨hq1, hq2⟩ := hQ
      simp only [Scheme.trun] at hr
      split at hr
      next => simp at hr
      next ci hci =>
        obtain ⟨o, ho, hr⟩ := Option.bind_eq_some_iff.1 hr
        rcases o with _ | ⟨rows, rest⟩
        · simp at hr
        · have hw' : ∀ j, S.rw (nReads (h ++ [Ev.query rows]) + j) = ws.getD j 8 := by
            intro j; rw [nReads_query]; exact hw j
          have e1 := ih rows os ws st buf caps rest _ h' (h2 rows) (hq2 rows) hw' hr
          have e2 := openAll_len S L ci ps body rows rest ho
          have hm : (caps.map shp)[i]? = some (ci.ht, ci.wd, ci.lv) := by
            rw [List.getElem?_map, hci]; rfl
          simp only [opB, hm]
          rw [e2, e1, hq1]
          simp only [Scheme.lb]

end Len

end Lvm6
