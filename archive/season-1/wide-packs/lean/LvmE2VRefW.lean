-- New for lvm2 E2-FT (E2F-V2): refinement with read widths under a promise (`RefAtPW`), and the lift of roll 11's
-- 24-byte refinements (`RefAtP`, read off the stream by `ivp`) to read widths, for a program that follows atoms
-- whose reads all take 24 bytes (`ivpW_of_fol`, `RefAtP.toPW`).
import LvmE2VEqCore
import LvmAccNodeFold
import LvmVEqShape

/-!
# Refinement with read widths under a promise

* **`RefAtPW … sig i d P R Q j`**: `RefAtW` (from read index `i` to `j`) where the native value meets the promise
  `Q`; rules `mono`, `bind`, `read_left`, `require_left`, `RefAtW.toPW`.
* **`ivpW_of_fol`**: a program that follows atoms `as` whose reads take 24 bytes reads off the stream with read
  widths `rw` (24 at the indices `i … i + |widthsA as| − 1`) as `ivp` does, ending at index `i + |widthsA as|`.
* **`RefAtP.toPW`**: so a 24-byte refinement (`RefAtP`, roll 11's typed phases, the opening) is one with read
  widths.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile

section Ref

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (rw : ℕ → ℕ)

/-- **`RefAtW` under a promise** `Q` on the native value. -/
def RefAtPW {α β : Type} (sig : ByteArray) (i : ℕ) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop)
    (Q : β → Prop) (j : ℕ) : Prop :=
  ∀ s, (runD d sig s).2.ok = true → Q (runD d sig s).1 →
    ∃ a, (ivpW cap occ shp rw P sig s i).1 = some a ∧
      (ivpW cap occ shp rw P sig s i).2.1.ent = (runD d sig s).2.ent ∧
      (ivpW cap occ shp rw P sig s i).2.1.msg = (runD d sig s).2.msg ∧
      (ivpW cap occ shp rw P sig s i).2.2 = j ∧ R (runD d sig s).1 a

variable {cap occ shp rw} {sig : ByteArray}

theorem RefAtW.toPW {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAtW cap occ shp rw sig i d P R j) (Q : β → Prop) : RefAtPW cap occ shp rw sig i d P R Q j :=
  fun s hok _ ↦ h s hok

theorem RefAtPW.mono {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R R' : β → α → Prop}
    {Q : β → Prop} (h : RefAtPW cap occ shp rw sig i d P R Q j) (hR : ∀ b a, R b a → R' b a) :
    RefAtPW cap occ shp rw sig i d P R' Q j :=
  fun s hok hq ↦ by
    obtain ⟨a, h1, h2, h3, h4, h5⟩ := h s hok hq
    exact ⟨a, h1, h2, h3, h4, hR _ _ h5⟩

/-- **Composition under promises.** -/
theorem RefAtPW.bind {α α' β β' : Type} {i j k : ℕ} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop} {Q : β → Prop}
    {Q' : β' → Prop} (hm : ∀ b, MonoD (d' b)) (h : RefAtPW cap occ shp rw sig i d P R Q j)
    (hQ : ∀ b s, Q' (runD (d' b) sig s).1 → Q b)
    (h' : ∀ b a, R b a → Q b → RefAtPW cap occ shp rw sig j (d' b) (P' a) R' Q' k) :
    RefAtPW cap occ shp rw sig i (d >>= d') (P.bind P') R' Q' k := by
  intro s hok hq
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok hq ⊢
  have hq1 := hQ _ _ hq
  obtain ⟨a, ha, he, hmsg, hj, hR⟩ := h s (hm _ sig _ hok) hq1
  obtain ⟨a', ha', he', hm', hk, hR'⟩ := h' _ _ hR hq1 _ hok hq
  refine ⟨a', ?_⟩
  rw [ivpW_bind]
  rcases hP : ivpW cap occ shp rw P sig s i with ⟨_ | a₀, s₂, i₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg hj
    simp only [Option.some.injEq] at ha
    subst ha
    simp only at hj
    subst hj
    obtain ⟨c1, c2, c3, c4⟩ := ivpW_congr (cap := cap) (occ := occ) (shp := shp) (rw := rw) (P' a₀) sig i₂
      he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', c4.trans hk, hR'⟩

/-- Reading the stream itself, then the rest. -/
theorem RefAtPW.read_left {α β : Type} {i j : ℕ} {d : ByteArray → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAtPW cap occ shp rw sig i (d sig) P R Q j) :
    RefAtPW cap occ shp rw sig i (MonadReader.read >>= d) P R Q j :=
  fun s hok hq ↦ h s hok hq

/-- **V_S's strict `require`, then the rest.** -/
theorem RefAtPW.require_left {α β : Type} {i j : ℕ} {c : Bool} {d : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (hm : ∀ u, MonoD (d u))
    (h : c = true → RefAtPW cap occ shp rw sig i (d ()) P R Q j) :
    RefAtPW cap occ shp rw sig i (DM.require c >>= d) P R Q j := by
  intro s hok hq
  have e : runD (DM.require c >>= d) sig s = runD (d ()) sig { s with ok := c && s.ok } := rfl
  rw [e] at hok hq ⊢
  have hc : c = true := (Bool.and_eq_true _ _ ▸ hm () sig _ hok).1
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := h hc _ hok hq
  obtain ⟨c1, c2, c3, c4⟩ := ivpW_congr (cap := cap) (occ := occ) (shp := shp) (rw := rw) P sig i
    (s := s) (s' := { s with ok := c && s.ok }) rfl rfl
  exact ⟨a, c1.trans h1, c2.trans h2, c3.trans h3, c4.trans h4, h5⟩

end Ref

/-! ## The lift from 24-byte reads -/

section Lift

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray} {cap' : ℕ → ℕ → ℕ} {shp' : ℕ → ℕ × ℕ}
  {idx : Ref → ℕ}

/-- **A program that follows atoms of 24-byte reads reads off the stream as `ivp` does**, with read widths that
are 24 there, and ends at the index after its reads. -/
theorem ivpW_of_fol {α : Type} : ∀ (as : List Atom) (P : VerifierProgram α) (pp : List ℕ)
    (Qf : α → List ℕ → Prop) (s : RS) (i : ℕ) (a : α),
    Fol cap' shp' idx P as pp Qf → WAt rw i (widthsA as) → (∀ x ∈ widthsA as, x = 24) →
    (ivp cap occ shp P sig s).1 = some a →
    ivpW cap occ shp rw P sig s i = (some a, (ivp cap occ shp P sig s).2, i + (widthsA as).length)
  | [], P, pp, Qf, s, i, a, hF, _, _, hv => by
    cases P with
    | ret b => simp only [ivp, Option.some.injEq] at hv; subst hv; rfl
    | fail => simp [ivp] at hv
    | _ => exact hF.elim
  | .rd :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | read k =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have := ivpW_of_fol as _ pp Qf _ (i + 1) a (hF _) hw' (fun x hx ↦ h24 x (List.mem_cons_of_mem _ hx)) hv
      simp only [ivpW, ivp, hw0] at this ⊢
      rw [this]; congr 2; simp only [widthsA, List.length_cons]; omega
    | fail => simp [ivp] at hv
    | _ => exact hF.elim
  | .rdw w :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | read k =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have hw24 : rw i = 24 := hw0.trans (h24 w List.mem_cons_self)
      have := ivpW_of_fol as _ pp Qf _ (i + 1) a (hF _) hw' (fun x hx ↦ h24 x (List.mem_cons_of_mem _ hx)) hv
      simp only [ivpW, ivp, hw24] at this ⊢
      rw [this]; congr 2; simp only [widthsA, List.length_cons]; omega
    | fail => simp [ivp] at hv
    | _ => exact hF.elim
  | .sm :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | sample k =>
      simp only [ivpW, ivp] at hv ⊢
      exact ivpW_of_fol as _ pp Qf _ i a (hF _) hw h24 hv
    | fail => simp [ivp] at hv
    | _ => exact hF.elim
  | .ps h n :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | sample k =>
      simp only [ivpW, ivp] at hv ⊢
      exact ivpW_of_fol as _ _ Qf _ i a (hF _) hw h24 hv
    | fail => simp [ivp] at hv
    | _ => exact hF.elim
  | .pclr :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    rw [fol_pclr] at hF
    exact ivpW_of_fol as P [] Qf s i a hF hw h24 hv
  | .cap c r :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | commit ht w k =>
      simp only [ivpW, ivp] at hv ⊢
      exact ivpW_of_fol as _ pp Qf _ i a hF.2.2 hw h24 hv
    | fail => simp [ivp] at hv
    | _ => exact hF.elim
  | .op r :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | query i' ps k =>
      simp only [ivpW, ivp] at hv ⊢
      exact ivpW_of_fol as _ pp Qf _ i a (hF.2.2 _) hw h24 hv
    | fail => simp [ivp] at hv
    | _ => exact hF.elim

/-- **A 24-byte refinement is one with read widths**, for a program that follows atoms of 24-byte reads (from
every pending position list) at widths that are 24 there. -/
theorem RefAtP.toPW {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop} {Q : β → Prop}
    {as : List Atom} {Qf : α → List ℕ → Prop} {i : ℕ} (h : RefAtP cap occ shp sig d P R Q)
    (hF : ∀ pp, Fol cap' shp' idx P as pp Qf) (hw : WAt rw i (widthsA as)) (h24 : ∀ x ∈ widthsA as, x = 24) :
    RefAtPW cap occ shp rw sig i d P R Q (i + (widthsA as).length) := by
  intro s hok hq
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok hq
  have e := ivpW_of_fol (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) as P [] Qf s i a (hF [])
    hw h24 h1
  rw [e]
  exact ⟨a, rfl, h2, h3, rfl, h4⟩

end Lift

end Lvm.VEq
