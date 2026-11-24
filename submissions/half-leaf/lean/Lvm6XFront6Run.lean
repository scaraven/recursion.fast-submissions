-- lvm6 EXF (DP6 §2 item 1, part 1): the accepting replay of any program that follows an operation list, read
-- against the chain scan's messages and the proof's bytes. New; the invariant is X3's `RS` (`Lvm6XChainRun`), the
-- induction LEN's `trun_len` (`Lvm6LenRun`), here over `Follows` instead of V1's walk.
import Lvm6LenRun
import Lvm6XChainRun

/-!
# The replay's challenges and commitments, from its operations

X3's `chain6_spec` is about V1's walk; the composed program `prog6 Φ` only *follows* the walk's operations
(`prog6_sched`). Here the replay of any program `p` with `Follows p os` and `QLen t p`:

* **`opnB`**, **`msgsOp`**, **`capsOp`**, **`contigOp`**: the bytes of an opening, the chain's messages
  `(offset, length)` (as `msgsAux`), the caps `(ht, w, offset)`, and "every opening finds an empty buffer", walking
  `os` from π offset `o` with `b` buffered bytes (`opB`'s widths and shapes).
* **`ChainHist sh π L H`**: sample `j` of `H` is `chalOf` of chain position `j + 2`, inside the scan (`j + 2 < nCh6`).
* **`trun_front`**: an accepting replay from `RS` ends with `ChainHist`, and its commitments are the ones before
  followed by `capsOp`'s caps, each the word `wordOf L (capI ht w (π.drop o))` of the cap at its offset.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS
open LeanVM.Protocol.Compile (Ev VerifierProgram commits)

/-! ## The walk over operations -/

/-- The source of a replayed event. -/
inductive Src
  | rd (off w : ℕ)
  | smp (p : ℕ)
  | cap
  | opn
  deriving DecidableEq, Inhabited

section Walk

variable (cO oc : ℕ → ℕ → ℕ) (t : ℕ → ℕ)

/-- The bytes the openings of commitment `i` take (`opB`'s term). -/
def opnB (cs : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ :=
  match cs[i]? with
  | some (ht, w, lv) => t i * (8 * min (oc ht w) w + 32 * (ht - lv))
  | none => 0

/-- **The chain's messages** of an operation list: one `(o − b, b)` per draw. -/
def msgsOp : List (ℕ × ℕ × ℕ) → List ℕ → ℕ → ℕ → List Op → List (ℕ × ℕ)
  | _, _, _, _, [] => []
  | cs, ws, o, b, .rd :: os => msgsOp cs ws.tail (o + ws.getD 0 8) (b + ws.getD 0 8) os
  | cs, ws, o, b, .smp :: os => (o - b, b) :: msgsOp cs ws o 0 os
  | cs, ws, o, b, .cap ht w :: os =>
    msgsOp (cs ++ [(ht, w, cO ht w)]) ws (o + 32 * 2 ^ cO ht w) (b + 32 * 2 ^ cO ht w) os
  | cs, ws, o, b, .opn i :: os => msgsOp cs ws (o + opnB oc t cs i) b os

/-- **The caps** of an operation list: `(ht, w, π offset)` each. -/
def capsOp : List (ℕ × ℕ × ℕ) → List ℕ → ℕ → List Op → List (ℕ × ℕ × ℕ)
  | _, _, _, [] => []
  | cs, ws, o, .rd :: os => capsOp cs ws.tail (o + ws.getD 0 8) os
  | cs, ws, o, .smp :: os => capsOp cs ws o os
  | cs, ws, o, .cap ht w :: os => (ht, w, o) :: capsOp (cs ++ [(ht, w, cO ht w)]) ws (o + 32 * 2 ^ cO ht w) os
  | cs, ws, o, .opn i :: os => capsOp cs ws (o + opnB oc t cs i) os

/-- **Every opening finds an empty buffer.** -/
def contigOp : List (ℕ × ℕ × ℕ) → List ℕ → ℕ → List Op → Bool
  | _, _, _, [] => true
  | cs, ws, b, .rd :: os => contigOp cs ws.tail (b + ws.getD 0 8) os
  | cs, ws, _, .smp :: os => contigOp cs ws 0 os
  | cs, ws, b, .cap ht w :: os => contigOp (cs ++ [(ht, w, cO ht w)]) ws (b + 32 * 2 ^ cO ht w) os
  | cs, ws, b, .opn _ :: os => b == 0 && contigOp cs ws b os

/-- **The source of each event** of the replay: a read's π offset and width, a draw's chain position. -/
def srcsOp : List (ℕ × ℕ × ℕ) → List ℕ → ℕ → ℕ → List Op → List Src
  | _, _, _, _, [] => []
  | cs, ws, o, P, .rd :: os => .rd o (ws.getD 0 8) :: srcsOp cs ws.tail (o + ws.getD 0 8) P os
  | cs, ws, o, P, .smp :: os => .smp (P + 1) :: srcsOp cs ws o (P + 1) os
  | cs, ws, o, P, .cap ht w :: os => .cap :: srcsOp (cs ++ [(ht, w, cO ht w)]) ws (o + 32 * 2 ^ cO ht w) P os
  | cs, ws, o, P, .opn i :: os => .opn :: srcsOp cs ws (o + opnB oc t cs i) P os

end Walk

/-- **An event and its source**: a read is the scheme's scalar of its bytes of π, a draw the challenge of the chain's
answer at its position. -/
def EvSrc (S : Scheme) (sh : Shape) (π : Proof) (L : Log) : Src → Ev → Prop
  | .rd off w, .read x => x = S.decE ((π.data.toList.drop off).take w)
  | .smp p, .sample c => ∃ a, fmAns (fsQ6 sh π) zeroDL L p = some a ∧ c = Lvm.FS.chalOf a
  | .cap, .commit _ _ _ => True
  | .opn, .query _ => True
  | _, _ => False

/-- **A returning run of a following program has one event per operation.** -/
theorem after_length {α : Type} (p : VerifierProgram α) :
    ∀ {os : List Op} {l : List Ev} {a : α}, Follows p os → p.after l = some (.ret a) → l.length = os.length := by
  induction p with
  | ret r =>
    intro os l a hF h
    have hos : os = [] := hF
    subst hos
    cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [VerifierProgram.after] at h
  | fail =>
    intro os l a _ h
    cases l with
    | nil => simp [VerifierProgram.after] at h
    | cons e es => cases e <;> simp [VerifierProgram.after] at h
  | grind _ _ _ => intro _ _ _ hF; exact hF.elim
  | read k ih =>
    intro os l a hF h
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      cases l with
      | nil => simp [VerifierProgram.after] at h
      | cons e es =>
        cases e <;> simp [VerifierProgram.after] at h
        rename_i x
        simpa using ih x (h2 x) h
  | sample k ih =>
    intro os l a hF h
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      cases l with
      | nil => simp [VerifierProgram.after] at h
      | cons e es =>
        cases e <;> simp [VerifierProgram.after] at h
        rename_i x
        simpa using ih x (h2 x) h
  | commit ht w k ih =>
    intro os l a hF h
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      cases l with
      | nil => simp [VerifierProgram.after] at h
      | cons e es =>
        cases e <;> simp [VerifierProgram.after] at h
        simpa using ih h2 h.2
  | query i ps k ih =>
    intro os l a hF h
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o os =>
      cases l with
      | nil => simp [VerifierProgram.after] at h
      | cons e es =>
        cases e <;> simp [VerifierProgram.after] at h
        rename_i x
        simpa using ih x (h2 x) h

/-- **The history's challenges are the scan's chain**, inside the scan's targets. -/
def ChainHist (sh : Shape) (π : Proof) (L : Log) (H : List Ev) : Prop :=
  ∀ j (hj : j < (samples H).length), ∃ a, fmAns (fsQ6 sh π) zeroDL L (j + 2) = some a ∧
    (samples H)[j] = Lvm.FS.chalOf a ∧ j + 2 < nCh6 sh

theorem commits_snoc (h : List Ev) (e : Ev) :
    commits (h ++ [e]) = commits h ++ commits [e] := by
  induction h with
  | nil => simp [commits]
  | cons e' h ih => cases e' <;> simp [commits, ih]

/-- The commitment record of a cap at π offset `o`, as the history holds it. -/
def capEnt (S : Scheme) (L : Log) (π : Proof) (c : ℕ × ℕ × ℕ) : ℕ × ℕ × LeanVM.Protocol.Compile.Word :=
  (c.1, c.2.1, S.wordOf L (S.capI c.1 c.2.1 (π.data.toList.drop c.2.2)))

/-! ## The induction -/

/-- **The replay of a following program**: from `RS` at chain position `P` (π offset `o`, `b` buffered bytes),
with the messages still to come those of `os`, an accepting replay's history has the chain's challenges and
its commitments are `capsOp`'s caps. -/
theorem trun_front (S : Scheme) (hc : ∀ a, S.chal a = Lvm.FS.chalOf a) (sh : Shape) (π : Proof) (L : Log)
    (t : ℕ → ℕ) :
    ∀ (p : VerifierProgram Bool) (os : List Op) (ws : List ℕ) (P o b : ℕ) (st : Digest) (buf : List UInt8)
      (caps : List CapI) (body : List UInt8) (h h' : List Ev),
    Follows p os → QLen t p → (∀ k, S.rw (nReads h + k) = ws.getD k 8) →
    RS sh π L P o b st buf body h → P ≤ (msgs6 sh).length →
    (msgs6 sh).drop P = msgsOp S.capOf S.occ t (caps.map shp) ws o b os →
    contigOp S.capOf (caps.map shp) ws b os = true →
    S.trun L p st buf caps body h = some (true, h') →
    ChainHist sh π L h' ∧
      commits h' = commits h ++ (capsOp S.capOf S.occ t (caps.map shp) ws o os).map (capEnt S L π) ∧
      ∃ evs, h' = h ++ evs ∧ List.Forall₂ (EvSrc S sh π L) (srcsOp S.capOf S.occ t (caps.map shp) ws o P os) evs := by
  intro p
  induction p with
  | ret r =>
    intro os ws P o b st buf caps body h h' hF _ _ hR hP _ _ hT
    have hos : os = [] := hF
    subst hos
    have hH := trun_ret S L hT
    subst hH
    refine ⟨fun j hj => ?_, by simp [capsOp], [], by simp, by simp [srcsOp]⟩
    obtain ⟨a, ha1, ha2⟩ := hR.hist j hj
    have := hR.len
    exact ⟨a, ha1, ha2, by simp only [nCh6]; omega⟩
  | fail => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT; exact (trun_fail S L hT).elim
  | grind _ _ _ => intro _ _ _ _ _ _ _ _ _ _ _ hF; exact hF.elim
  | read k ih =>
    intro os ws P o b st buf caps body h h' hF hQ hw hR hP hm hct hT
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o' os =>
      have ho : o' = .rd := by simpa using h1
      subst ho
      have hT' := trun_read S L hT
      have h0 : S.rw (nReads h) = ws.getD 0 8 := by simpa using hw 0
      rw [h0] at hT'
      have hw' : ∀ j, S.rw (nReads (h ++ [Ev.read (S.decE (body.take (ws.getD 0 8)))]) + j) =
          ws.tail.getD j 8 := by
        intro j
        rw [Len.getD_tail, ← hw (j + 1), nReads_read, Nat.add_assoc, Nat.add_comm 1 j]
      have hR' := hR.absorb (ws.getD 0 8) (h ++ [Ev.read (S.decE (body.take (ws.getD 0 8)))])
        (samples_read _ _)
      obtain ⟨e1, e2, evs, e3, e4⟩ := ih _ os ws.tail P _ _ st _ caps _ _ h' (h2 _) (hQ _) hw' hR' hP
        (by rw [hm]; rfl) (by rw [← hct]; rfl) hT'
      refine ⟨e1, ?_, Ev.read (S.decE (body.take (ws.getD 0 8))) :: evs, by rw [e3, List.append_assoc]; rfl,
        List.Forall₂.cons ?_ e4⟩
      · rw [e2, commits_snoc]
        simp [commits, capsOp]
      · show _ = _
        rw [hR.body]
  | sample k ih =>
    intro os ws P o b st buf caps body h h' hF hQ hw hR hP hm hct hT
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o' os =>
      have ho : o' = .smp := by simpa using h1
      subst ho
      obtain ⟨e, hf, hT'⟩ := trun_sample S L hT
      rw [msgsOp] at hm
      obtain ⟨hm1, hm2⟩ := msgs_cons hm
      have hPl : P < (msgs6 sh).length := by
        by_contra hc'
        rw [List.drop_eq_nil_of_le (by omega)] at hm
        exact List.cons_ne_nil _ _ hm.symm
      have hfm : fmAns (fsQ6 sh π) zeroDL L (P + 1) = some e.2 := by
        simp only [fmAns, hR.fm, Option.bind_some]
        rw [fsQ6_msg hm1, ← hR.buf, hf]; rfl
      have hR' : RS sh π L (P + 1) o 0 e.2 [] body (h ++ [Ev.sample (S.chal e.2)]) := by
        refine ⟨hR.body, by simp, Nat.zero_le _, hfm, ?_, ?_⟩
        · rw [samples_sample, List.length_append, List.length_singleton, hR.len]
        · intro j hj
          rw [samples_sample, List.length_append, List.length_singleton] at hj
          by_cases hjl : j < (samples h).length
          · obtain ⟨a, ha1, ha2⟩ := hR.hist j hjl
            refine ⟨a, ha1, ?_⟩
            simp only [samples_sample, List.getElem_append_left hjl, ha2]
          · have hj' : j = (samples h).length := by omega
            subst hj'
            refine ⟨e.2, by rw [show (samples h).length + 2 = P + 1 by have := hR.len; omega]; exact hfm, ?_⟩
            simp [samples_sample, hc]
      have hw' : ∀ j, S.rw (nReads (h ++ [Ev.sample (S.chal e.2)]) + j) = ws.getD j 8 := by
        intro j; rw [nReads_sample]; exact hw j
      obtain ⟨e1, e2, evs, e3, e4⟩ := ih _ os ws (P + 1) o 0 e.2 [] caps body _ h' (h2 _) (hQ _) hw' hR'
        (by omega) hm2 (by rw [← hct]; rfl) hT'
      refine ⟨e1, ?_, Ev.sample (S.chal e.2) :: evs, by rw [e3, List.append_assoc]; rfl,
        List.Forall₂.cons ⟨e.2, hfm, hc _⟩ e4⟩
      rw [e2, commits_snoc]
      simp [commits, capsOp]
  | commit ht w k ih =>
    intro os ws P o b st buf caps body h h' hF hQ hw hR hP hm hct hT
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o' os =>
      have ho : o' = .cap ht w := by simpa using h1
      subst ho
      have hT' := trun_commit S L hT
      have hcb : S.capBytes ht w = 32 * 2 ^ S.capOf ht w := rfl
      rw [hcb] at hT'
      have hR' := hR.absorb (32 * 2 ^ S.capOf ht w)
        (h ++ [Ev.commit ht w (S.wordOf L (S.capI ht w body))]) (samples_commit _ _ _ _)
      have hw' : ∀ j, S.rw (nReads (h ++ [Ev.commit ht w (S.wordOf L (S.capI ht w body))]) + j) =
          ws.getD j 8 := by
        intro j; rw [nReads_commit]; exact hw j
      have hs : (caps ++ [S.capI ht w body]).map shp = caps.map shp ++ [(ht, w, S.capOf ht w)] := by
        rw [List.map_append]; rfl
      obtain ⟨e1, e2, evs, e3, e4⟩ := ih os ws P _ _ st _ _ _ _ h' h2 hQ hw' hR' hP
        (by rw [hm, hs]; rfl) (by rw [← hct, hs]; rfl) hT'
      rw [hs] at e4
      refine ⟨e1, ?_, Ev.commit ht w (S.wordOf L (S.capI ht w body)) :: evs, by rw [e3, List.append_assoc]; rfl,
        List.Forall₂.cons trivial e4⟩
      rw [e2, commits_snoc, hs, hR.body]
      simp [commits, capsOp, capEnt]
  | query i ps k ih =>
    intro os ws P o b st buf caps body h h' hF hQ hw hR hP hm hct hT
    obtain ⟨h1, h2⟩ := hF
    cases os with
    | nil => simp at h1
    | cons o' os =>
      have ho : o' = .opn i := by simpa using h1
      subst ho
      obtain ⟨hq1, hq2⟩ := hQ
      simp only [contigOp, Bool.and_eq_true, beq_iff_eq] at hct
      obtain ⟨hb, hct⟩ := hct
      subst hb
      obtain ⟨ci, rows, rest, hci, ho, hT'⟩ := trun_query S L hT
      have hrest := openAll_rest S L ci ps body rest rows ho
      have hm' : (caps.map shp)[i]? = some (ci.ht, ci.wd, ci.lv) := by
        rw [List.getElem?_map, hci]; rfl
      have hn : opnB S.occ t (caps.map shp) i = ps.length * (S.lb ci + 32 * (ci.ht - ci.lv)) := by
        rw [opnB, hm', hq1]; rfl
      have hbuf : buf = [] := by rw [hR.buf]; simp
      have hR' : RS sh π L P (o + ps.length * (S.lb ci + 32 * (ci.ht - ci.lv))) 0 st buf rest
          (h ++ [Ev.query rows]) :=
        ⟨by rw [hrest, hR.body, List.drop_drop], by rw [hbuf]; simp, Nat.zero_le _, hR.fm,
          by rw [samples_query]; exact hR.len, by rw [samples_query]; exact hR.hist⟩
      have hw' : ∀ j, S.rw (nReads (h ++ [Ev.query rows]) + j) = ws.getD j 8 := by
        intro j; rw [nReads_query]; exact hw j
      obtain ⟨e1, e2, evs, e3, e4⟩ := ih rows os ws P _ 0 st buf caps rest _ h' (h2 rows) (hq2 rows) hw' hR'
        hP (by rw [hm, msgsOp, hn]) hct hT'
      rw [← hn] at e4
      refine ⟨e1, ?_, Ev.query rows :: evs, by rw [e3, List.append_assoc]; rfl, List.Forall₂.cons trivial e4⟩
      rw [e2, commits_snoc]
      simp [commits, capsOp, hn]

end Lvm6.X
