-- New for lvm (AC-N, A23): V_S's phase 3b (AC-V's `accFold`) refines its reading over `E`
-- (AC-S's `Acc.accProgV`, `Acc.accProg` on the instance), under the promise that the folded
-- claim holds (V_S checks `AccOk` after the run, `decideF`; the language checks it in the phase).
-- Built on WP-14a's primitives (`ref_samples`, `ref_readEsL`, `ref_sampleE`, `ref_readE`), WP-9b's
-- `colLoc_raw` and AC-S's `phiE`.
import LvmVEqMid
import LvmVEqBus
import LvmVEqCore

-- (GOLF2: 28 declarations that `certified` does not use moved verbatim to `LvmTypedVEqPhasesXOff`, outside its import closure.)

-- ===== merged from `LvmAccNodeRef` (GOLF module merge: `LvmAccNodeRef.lean` is now a stub importing `LvmAccNodeFold`) =====
section
-- New for lvm (AC-N, A23): refinement of a native step under a promise on its value (`RefAtP`),
-- for the accumulator check that the native `F` runs after the whole program (`decideF`: `AccOk` of
-- `decideProg`'s value) and the verifier language runs right after phase 3b (`require` of the folded
-- claim). Extends WP-14a's `RefAt` (LvmVEqCore); the bind rule is `RefAt.bind`'s proof.

/-!
# Refinement under a promise

**`RefAtP sig d P R Q`**: wherever the native step `d` ends with every check held *and its value
satisfies `Q`*, the program `P` read off the stream returns a value related by `R` at the same
cursor. `RefAt` is `RefAtP` with `Q = True` (`RefAt.toP`, `RefAtP.toRefAt`).

* `RefAtP.bind`: composition, the promise on the continuation's value pulled back to the first
  step's (`hQ`: e.g. a continuation that returns the first step's value);
* `RefAtP.require_ret`: a language `require` justified by the promise, against a native `pure`;
  `RefAtP.read_left`: reading the stream.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Compile

section Ref

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)

/-- **`d` refines `P` under the promise `Q` on `d`'s value.** -/
def RefAtP {α β : Type} (sig : ByteArray) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop)
    (Q : β → Prop) : Prop :=
  ∀ s, (runD d sig s).2.ok = true → Q (runD d sig s).1 →
    ∃ a, (ivp cap occ shp P sig s).1 = some a ∧ (ivp cap occ shp P sig s).2.ent = (runD d sig s).2.ent ∧
      (ivp cap occ shp P sig s).2.msg = (runD d sig s).2.msg ∧ R (runD d sig s).1 a

variable {cap occ shp} {sig : ByteArray}

theorem RefAt.toP {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAt cap occ shp sig d P R) (Q : β → Prop) : RefAtP cap occ shp sig d P R Q :=
  fun s hok _ ↦ h s hok

theorem RefAtP.mono {α β : Type} {d : DM β} {P : VerifierProgram α} {R R' : β → α → Prop}
    {Q : β → Prop} (h : RefAtP cap occ shp sig d P R Q) (hR : ∀ b a, R b a → R' b a) :
    RefAtP cap occ shp sig d P R' Q :=
  fun s hok hq ↦ by
    obtain ⟨a, h1, h2, h3, h4⟩ := h s hok hq
    exact ⟨a, h1, h2, h3, hR _ _ h4⟩

/-- **Composition under a promise**: the continuation's promise implies the first step's. -/
theorem RefAtP.bind {α α' β β' : Type} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop} {Q : β → Prop}
    {Q' : β' → Prop} (hm : ∀ b, MonoD (d' b)) (h : RefAtP cap occ shp sig d P R Q)
    (hQ : ∀ b s, Q' (runD (d' b) sig s).1 → Q b)
    (h' : ∀ b a, R b a → Q b → RefAtP cap occ shp sig (d' b) (P' a) R' Q') :
    RefAtP cap occ shp sig (d >>= d') (P.bind P') R' Q' := by
  intro s hok hq
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok hq ⊢
  have hq1 := hQ _ _ hq
  obtain ⟨a, ha, he, hmsg, hR⟩ := h s (hm _ sig _ hok) hq1
  obtain ⟨a', ha', he', hm', hR'⟩ := h' _ _ hR hq1 _ hok hq
  refine ⟨a', ?_⟩
  rw [ivp_bind]
  rcases hP : ivp cap occ shp P sig s with ⟨_ | a₀, s₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg
    simp only [Option.some.injEq] at ha
    subst ha
    obtain ⟨c1, c2, c3⟩ := ivp_congr (cap := cap) (occ := occ) (shp := shp) (P' a₀) sig he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', hR'⟩

/-- Reading the stream itself, then the rest (under a promise). -/
theorem RefAtP.read_left {α β : Type} {d : ByteArray → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAtP cap occ shp sig (d sig) P R Q) :
    RefAtP cap occ shp sig (MonadReader.read >>= d) P R Q :=
  fun s hok hq ↦ h s hok hq

end Ref

end Lvm.VEq
end
-- ===== end of `LvmAccNodeRef` =====

/-!
# Phase 3b: `accFold` refines `accProgV`

With `cl = claimsOfEvs T evs` (the table phase's claims of the native evaluations, `ref_dTab`):

* `claimAt_claimsOfEvs`: the claim of column `(j, i)` is the native evaluation's;
* `pubOkV_of`, `fixSentV_eq`, `tablePointV_eq'`: `PUB`'s check, the sent fixed evaluations and the
  table point read over `E` are V_S's through `FE.toExt3`;
* **`ref_accFold`**: `accFold P20 (M3.real P20 tabs) pub evs` refines `accProgV P20 tabs pub cl` under
  the promise `AccOk` on its value.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)

/-! ## Refinement rules under a promise -/

section Rules

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **A native `require` with no language step**: the rest refines, knowing the check held. -/
theorem RefAtP.require_left {α β : Type} {c : Bool} {d : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (hm : ∀ u, MonoD (d u))
    (h : c = true → RefAtP cap occ shp sig (d ()) P R Q) : RefAtP cap occ shp sig (DM.require c >>= d) P R Q := by
  intro s hok hq
  have e : runD (DM.require c >>= d) sig s = runD (d ()) sig { s with ok := c && s.ok } := rfl
  rw [e] at hok hq ⊢
  have hc : c = true := (Bool.and_eq_true _ _ ▸ hm () sig _ hok).1
  obtain ⟨a, h1, h2, h3, h4⟩ := h hc _ hok hq
  obtain ⟨c1, c2, c3⟩ := ivp_congr (cap := cap) (occ := occ) (shp := shp) P sig
    (s := s) (s' := { s with ok := c && s.ok }) rfl rfl
  exact ⟨a, c1.trans h1, c2.trans h2, c3.trans h3, h4⟩

/-- **A language `require` against a native value**, justified by the promise and what is known. -/
theorem RefAtP.pure_require {β : Type} {b : β} {q : Prop} [Decidable q] {Q : β → Prop}
    (hq : Q b → q) :
    RefAtP cap occ shp sig (Pure.pure b : DM β) (VerifierProgram.require q) (fun _ _ ↦ True) Q := by
  intro s _ hQ
  have e : VerifierProgram.require q = VerifierProgram.ret () := by
    simp only [VerifierProgram.require, hq hQ, ↓reduceIte]
  rw [e]
  exact ⟨(), rfl, rfl, rfl, trivial⟩

end Rules

/-! ## The claims of the native evaluations -/

section Claims

variable (T : List Tab) (evs : List (List FE × List FE))

end Claims


/-! ## Arithmetic over `E` -/

theorem hEval_map (x : FE) : ∀ l : List FE,
    Lvm.Acc.hEval (l.map FE.toExt3) (FE.toExt3 x) = FE.toExt3 (Lvm.polyEval l x)
  | [] => by simp [Lvm.Acc.hEval, Lvm.polyEval]
  | c :: l => by
    rw [List.map_cons, Lvm.Acc.hEval_cons, hEval_map x l]
    simp only [Lvm.polyEval, List.foldr_cons] at *
    rw [FE.toExt3_add, FE.toExt3_mul]
    ring

theorem line_map (t : FE) : ∀ a b : List FE,
    Lvm.Acc.line (a.map FE.toExt3) (b.map FE.toExt3) (FE.toExt3 t) = (accLine a b t).map FE.toExt3
  | [], _ => by simp [Lvm.Acc.line, accLine]
  | _ :: _, [] => by simp [Lvm.Acc.line, accLine]
  | x :: a, y :: b => by
    have ih := line_map t a b
    simp only [Lvm.Acc.line, accLine, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih, FE.toExt3_add, FE.toExt3_mul, FE.toExt3_add]

theorem sumE_map (l : List FE) : (l.map FE.toExt3).sum = FE.toExt3 (Lvm.sumE l) := by
  rw [toExt3_sumE, Verifier.sumE, ← List.sum_eq_foldl]

/-! ## Values of native steps (the evaluations' count) -/

/-- Every run's value satisfies `P`. -/
def ValP {β : Type} (d : DM β) (P : β → Prop) : Prop := ∀ sig s, P (runD d sig s).1

theorem ValP.bind {β β' : Type} {d : DM β} {d' : β → DM β'} {P : β → Prop} {P' : β' → Prop}
    (h : ValP d P) (h' : ∀ b, P b → ValP (d' b) P') : ValP (d >>= d') P' :=
  fun sig s ↦ h' _ (h sig s) sig _

theorem ValP.pure {β : Type} {b : β} {P : β → Prop} (h : P b) : ValP (Pure.pure b : DM β) P :=
  fun _ _ ↦ h

/-! ## Phase 3b -/

section Fold

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

end Fold

end Lvm.VEq
