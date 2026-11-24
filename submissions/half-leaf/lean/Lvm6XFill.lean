-- lvm6 EXF phase 2 (F-EXG-2): the fill block's generic parts. The copy program `cpsIR` (one word a copy, from the heap
-- or from the tape), its semantics, cost and size (moved to `Lvm6XFillG` by X1, PORT17); the run lemmas of W1's pieces (reads, rounds, the tail's high parts)
-- that say which event of a returning run each value is. New.
import Lvm6XFront6
import Lvm6WhirFollow
import Lvm6XFillG

/-!
# Word copies and the opening's runs

* **`cp1IR (b, src, dst)`**: `M[dst] := M[src]` (`b`) or tape word `src`; **`cpsIR tab`** the copies in order.
  **`cpsIR_sem`**: for copies whose destinations are distinct and lie in `[lo, hi)`, above every heap source,
  `M'[dst] = cpV I M e` for each copy, every other cell `≥ regs` kept, `Inv`, no output, same size.
* **`readF_run`**, **`readFs_run`**, **`roundP_run`**, **`roundsP_run`**, **`tailP_hi`**: the values of W1's returning
  runs are `e2OfE` of their events at fixed indices (round `k`'s `α`, `β`: events `7k + 5`, `7k + 6`; a tail's high
  part `k`: event `k`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm6.Whir
open LeanVM.Protocol.Compile (Ev VerifierProgram)
open LeanVM.Parameters (E E2 e2OfE)

/-! ## The opening's runs, value by event -/

theorem readF_run {l : List Ev} {y : E2} (h : (readF chalE2).after l = some (.ret y)) :
    ∃ x, l = [Ev.read x] ∧ y = e2OfE x := by
  rcases l with _ | ⟨e, es⟩
  · simp [readF, VerifierProgram.after, VerifierProgram.readScalar, VerifierProgram.bind] at h
  · cases e <;> simp [readF, VerifierProgram.after, VerifierProgram.readScalar, VerifierProgram.bind] at h
    rename_i x
    obtain ⟨rfl, h2⟩ := after_ret_eq h
    refine ⟨x, rfl, ?_⟩
    have h3 : VerifierProgram.ret (chalE2.rd x) = VerifierProgram.ret y := h2.symm
    exact (VerifierProgram.ret.inj h3).symm

theorem readFs_run : ∀ (n : ℕ) {l : List Ev} {ys : List E2}, (readFs chalE2 n).after l = some (.ret ys) →
    l.length = n ∧ ∀ k < n, ∃ x, l[k]? = some (Ev.read x) ∧ ys.getD k 0 = e2OfE x
  | 0, l, ys, h => by
    obtain ⟨rfl, -⟩ := after_ret_eq h
    exact ⟨rfl, fun k hk => absurd hk (by omega)⟩
  | n + 1, l, ys, h => by
    obtain ⟨y, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
    obtain ⟨x, rfl, rfl⟩ := readF_run h1
    obtain ⟨ys', l₃, l₄, rfl, h3, h4⟩ := after_bind_ret h2
    obtain ⟨rfl, h5⟩ := after_ret_eq h4
    have h6 : ys = e2OfE x :: ys' := VerifierProgram.ret.inj h5
    subst h6
    obtain ⟨hl, hv⟩ := readFs_run n h3
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => exact ⟨x, by simp, rfl⟩
    | succ k =>
      obtain ⟨x', h7, h8⟩ := hv k (by omega)
      exact ⟨x', by simpa using h7, by simpa using h8⟩

theorem roundP_run {g : ℕ} {l : List Ev} {r : Rnd E2} (h : (roundP chalE2 g).after l = some (.ret r)) :
    ∃ c c' : E, l[5]? = some (Ev.sample c) ∧ l[6]? = some (Ev.sample c') ∧ r.α = e2OfE c ∧ r.β = e2OfE c' := by
  obtain ⟨_, l₁, r₁, rfl, h1, hA⟩ := after_bind_ret h
  obtain ⟨_, rfl, -⟩ := readF_run h1
  obtain ⟨_, l₂, r₂, rfl, h2, hB⟩ := after_bind_ret hA
  obtain ⟨_, rfl, -⟩ := readF_run h2
  obtain ⟨_, l₃, r₃, rfl, h3, hC⟩ := after_bind_ret hB
  obtain ⟨_, rfl, -⟩ := readF_run h3
  obtain ⟨_, l₄, r₄, rfl, h4, hD⟩ := after_bind_ret hC
  obtain ⟨_, rfl, -⟩ := readF_run h4
  obtain ⟨v, l₅, r₅, rfl, h5, hE⟩ := after_bind_ret hD
  obtain ⟨x, c, cs, rfl, hlen, rfl⟩ := grp6_run h5
  obtain ⟨rfl, h6⟩ := after_ret_eq hE
  match cs, hlen with
  | [c'], _ =>
    have h7 := (VerifierProgram.ret.inj h6).symm
    subst h7
    exact ⟨c, c', by simp, by simp, rfl, rfl⟩

theorem roundsP_run {g : ℕ} : ∀ (j : ℕ) {l : List Ev} {rs : List (Rnd E2)},
    (roundsP chalE2 g j).after l = some (.ret rs) →
    rs.length = j ∧ ∀ k < j, ∃ c c' : E, l[7 * k + 5]? = some (Ev.sample c) ∧ l[7 * k + 6]? = some (Ev.sample c') ∧
      (rs.getD k default).α = e2OfE c ∧ (rs.getD k default).β = e2OfE c'
  | 0, l, rs, h => by
    obtain ⟨rfl, h2⟩ := after_ret_eq h
    have h3 : rs = [] := VerifierProgram.ret.inj h2
    exact ⟨by simp [h3], fun k hk => absurd hk (by omega)⟩
  | j + 1, l, rs, h => by
    obtain ⟨r, l₁, l₂, rfl, h1, hA⟩ := after_bind_ret h
    obtain ⟨rs', l₃, l₄, rfl, h3, h4⟩ := after_bind_ret hA
    obtain ⟨rfl, h5⟩ := after_ret_eq h4
    have h6 : rs = r :: rs' := VerifierProgram.ret.inj h5
    subst h6
    have hl1 : l₁.length = 7 := after_length _ (follows_roundP g) h1
    obtain ⟨hl, hv⟩ := roundsP_run j h3
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero =>
      obtain ⟨c, c', a1, a2, a3, a4⟩ := roundP_run h1
      exact ⟨c, c', by rw [List.getElem?_append_left (by omega)]; exact a1,
        by rw [List.getElem?_append_left (by omega)]; exact a2, a3, a4⟩
    | succ k =>
      obtain ⟨c, c', a1, a2, a3, a4⟩ := hv k (by omega)
      refine ⟨c, c', ?_, ?_, by simpa using a3, by simpa using a4⟩
      · rw [List.getElem?_append_right (by omega), hl1, show 7 * (k + 1) + 5 - 7 = 7 * k + 5 by omega,
          List.append_nil]
        exact a1
      · rw [List.getElem?_append_right (by omega), hl1, show 7 * (k + 1) + 6 - 7 = 7 * k + 6 by omega,
          List.append_nil]
        exact a2

/-- **A tail's high parts** are its first `nh` reads. -/
theorem tailP_hi {n n' m' : ℕ} (L : TailIface E2 n n' m') (ht wd i gO gQ : ℕ) (vals)
    {l : List Ev} {o : TailOut E2 L.ko L.t n} (h : (tailP L chalE2 ht wd i gO gQ vals).after l = some (.ret o)) :
    ∀ k < L.nh, ∃ x, l[k]? = some (Ev.read x) ∧ o.hi.getD k 0 = e2OfE x := by
  obtain ⟨hi, l₁, l₂, rfl, h1, hA⟩ := after_bind_ret h
  obtain ⟨hl, hv⟩ := readFs_run L.nh h1
  have ho : o.hi = hi := by
    obtain ⟨_, _, l₃, rfl, -, hB⟩ := after_bind_ret hA
    obtain ⟨_, _, l₄, rfl, -, hC⟩ := after_bind_ret hB
    obtain ⟨_, _, l₅, rfl, -, hD⟩ := after_bind_ret hC
    obtain ⟨_, _, l₆, rfl, -, hE⟩ := after_bind_ret hD
    obtain ⟨_, _, l₇, rfl, -, hF⟩ := after_bind_ret hE
    obtain ⟨_, _, l₈, rfl, -, hG⟩ := after_bind_ret hF
    obtain ⟨-, hH⟩ := after_ret_eq hG
    rw [VerifierProgram.ret.inj hH]
  intro k hk
  obtain ⟨x, h1, h2⟩ := hv k hk
  exact ⟨x, by rw [List.getElem?_append_left (by omega)]; exact h1, by rw [ho]; exact h2⟩

end Lvm6.X
