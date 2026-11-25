-- New for lvm6 (WP CB). The `V` side of CB's HARs: a DSL program run on events read off the
-- stream lanes (`Runs`), its composition along `>>=`, and the reading primitives of FORMAT6 §6.
import Lvm6QKStmt

/-!
# Running a DSL program on the stream (`Runs`)

**`Runs M lay p P`**: with the grinds of the slots passing, every event list matching the slots
makes `p` return a value with `P`. `Har gate g prog lay Rep` is `HsA` of `Runs M lay prog (Rep M o)`
(`har_iff`). The calculus: `runs_bind` (along `>>=`, the slots appended), `runs_pure`,
`runs_mono`, and the primitives: `runs_e2Read(s)`, `runs_kRead(s)`, `runs_e2Sample` (a nonce slot
and a ground draw: the value is the answer's lanes 0–1, the grind holds by `PowLay`),
`runs_dDraw(s)`, `runs_gPoint`, `runs_e2Samples`. `layItems_append` splits the layout of a list of
items. `ev2_ld2`: the value of a stream scalar is its two lanes.
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K
open Lvm6 (Item rep rnd)

/-! ## Layouts -/

theorem layItems_append : ∀ (l₁ l₂ : List Item) (a : ℕ),
    layItems (l₁ ++ l₂) a = layItems l₁ a ++ layItems l₂ (layEnd l₁ a)
  | [], _, _ => rfl
  | it :: its, l₂, a => by
    cases it <;> simp only [List.cons_append, layItems, layEnd, layItems_append its l₂,
      List.append_assoc]

theorem layEnd_append : ∀ (l₁ l₂ : List Item) (a : ℕ),
    layEnd (l₁ ++ l₂) a = layEnd l₂ (layEnd l₁ a)
  | [], _, _ => rfl
  | it :: its, l₂, a => by cases it <;> simp only [List.cons_append, layEnd, layEnd_append its l₂]

/-! ## Events -/

theorem evMatch_nil (M : Mem) : EvMatch M [] [] := List.Forall₂.nil

/-- A match of an appended layout splits. -/
theorem evMatch_append {M : Mem} : ∀ {l₁ l₂ : List LEv} {evs : List Ev},
    EvMatch M (l₁ ++ l₂) evs → ∃ e₁ e₂, evs = e₁ ++ e₂ ∧ EvMatch M l₁ e₁ ∧ EvMatch M l₂ e₂
  | [], _, evs, h => ⟨[], evs, rfl, List.Forall₂.nil, h⟩
  | x :: l₁, l₂, evs, h => by
    cases h with
    | cons hx hr =>
      obtain ⟨e₁, e₂, rfl, h1, h2⟩ := evMatch_append hr
      exact ⟨_ :: e₁, e₂, rfl, List.Forall₂.cons hx h1, h2⟩

theorem powLay_append {M : Mem} {l₁ l₂ : List LEv} (h : PowLay M (l₁ ++ l₂)) :
    PowLay M l₁ ∧ PowLay M l₂ :=
  ⟨fun a g hm ↦ h a g (List.mem_append_left _ hm), fun a g hm ↦ h a g (List.mem_append_right _ hm)⟩

/-- The value of a stream scalar is its two lanes. -/
theorem ev2_ld2 (M : Mem) (a : ℕ) : ev2 M (ld2 a) = ⟨lk M a, lk M (a + 1)⟩ := rfl

/-! ## `Runs` -/

/-- **`p` runs on the slots `lay`** to a value with `P`. -/
def Runs {β : Type} (M : Mem) (lay : List LEv) (p : VerifierProgram β) (P : β → Prop) : Prop :=
  PowLay M lay → ∀ evs, EvMatch M lay evs → ∃ out, p.after evs = some (.ret out) ∧ P out

theorem har_iff {α β : Type} (gate : Cell) (g : BM α) (prog : VerifierProgram β) (lay : List LEv)
    (Rep : Mem → α → β → Prop) :
    Har gate g prog lay Rep ↔ ∀ c M, gate.val M = 1 → HsA c M g fun o ↦ Runs M lay prog (Rep M o) :=
  Iff.rfl

theorem runs_mono {β : Type} {M : Mem} {lay : List LEv} {p : VerifierProgram β} {P Q : β → Prop}
    (h : Runs M lay p P) (hPQ : ∀ b, P b → Q b) : Runs M lay p Q := fun hp evs he ↦ by
  obtain ⟨out, h1, h2⟩ := h hp evs he
  exact ⟨out, h1, hPQ _ h2⟩

theorem runs_pure {β : Type} {M : Mem} {b : β} {P : β → Prop} (h : P b) :
    Runs M [] (pure b : VerifierProgram β) P := fun _ evs he ↦ by
  cases he
  exact ⟨b, rfl, h⟩

theorem runs_bind {β γ : Type} {M : Mem} {l₁ l₂ : List LEv} {p : VerifierProgram β}
    {f : β → VerifierProgram γ} {P : β → Prop} {Q : γ → Prop} (hp : Runs M l₁ p P)
    (hf : ∀ b, P b → Runs M l₂ (f b) Q) : Runs M (l₁ ++ l₂) (p >>= f) Q := fun hpw evs he ↦ by
  obtain ⟨hw1, hw2⟩ := powLay_append hpw
  obtain ⟨e₁, e₂, rfl, h1, h2⟩ := evMatch_append he
  obtain ⟨b, hb, hPb⟩ := hp hw1 e₁ h1
  obtain ⟨out, ho, hQ⟩ := hf b hPb hw2 e₂ h2
  refine ⟨out, ?_, hQ⟩
  show (p.bind f).after (e₁ ++ e₂) = _
  rw [VerifierProgram.after_bind_append f hb e₂, ho]

/-- `runs_bind` with the slots given as one list. -/
theorem runs_bind' {β γ : Type} {M : Mem} {l₁ l₂ l : List LEv} {p : VerifierProgram β}
    {f : β → VerifierProgram γ} {P : β → Prop} {Q : γ → Prop} (hl : l = l₁ ++ l₂)
    (hp : Runs M l₁ p P) (hf : ∀ b, P b → Runs M l₂ (f b) Q) : Runs M l (p >>= f) Q :=
  hl ▸ runs_bind hp hf

/-- A `require` that holds reads nothing. -/
theorem runs_require {M : Mem} {c : Prop} [Decidable c] (hc : c) :
    Runs M [] (VerifierProgram.require c) fun _ ↦ True :=
  fun _ evs he ↦ by
    cases he
    exact ⟨(), by simp [VerifierProgram.require, hc, VerifierProgram.after], trivial⟩

/-! ## Reading primitives -/

theorem runs_e2Read (M : Mem) (a : ℕ) : Runs M [.e a] e2Read (· = ev2 M (ld2 a)) := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | read x => exact ⟨e2OfE x, rfl, hx⟩
    | _ => exact absurd hx (by simp [EvM])

theorem runs_kRead (M : Mem) (a : ℕ) : Runs M [.k a] kRead (· = lk M a) := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | read x => exact ⟨x.limb 0, rfl, hx⟩
    | _ => exact absurd hx (by simp [EvM])

theorem runs_dDraw (M : Mem) (a : ℕ) : Runs M [.d a 0] dDraw (· = ev2 M (ld2 a)) := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | sample x =>
      refine ⟨e2OfE x, rfl, ?_⟩
      obtain ⟨h0, h1, -⟩ := hx
      rw [ev2_ld2, e2OfE, h0, h1]
    | _ => exact absurd hx (by simp [EvM])

/-- **A ground draw**: the nonce slot, the answer; the grind holds on the PoW lane. -/
theorem runs_e2Sample (M : Mem) {g : ℕ} (hg : g ≤ 64) (a : ℕ) :
    Runs M [.k a, .d (a + 1) g] (e2Sample g) (· = ev2 M (ld2 (a + 1))) := fun hpw evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr with
    | cons hy hr' =>
      cases hr'
      rename_i e1 e2
      cases e1 with
      | read n =>
        cases e2 with
        | sample x =>
          obtain ⟨h0, h1, h2⟩ := hy
          have hp : powOK g x := by
            rw [powOK_iff_lane2 hg, h2]
            exact hpw (a + 1) g (by simp)
          refine ⟨e2OfE x, ?_, by rw [ev2_ld2, e2OfE, h0, h1]⟩
          simp [e2Sample, VerifierProgram.after, VerifierProgram.readScalar,
            VerifierProgram.sampleChallenge, VerifierProgram.require, hp, bind,
            VerifierProgram.bind, pure]
        | _ => exact absurd hy (by simp [EvM])
      | _ => exact absurd hx (by simp [EvM])

/-! ## Lists of reads and draws -/

/-- The values of `n` stream scalars from lane `a` (2 lanes apart). -/
def scal (M : Mem) (a n : ℕ) : List E2 := (List.range n).map fun i ↦ ev2 M (ld2 (a + 2 * i))

/-- The words of `n` lanes from `a`. -/
def words (M : Mem) (a n : ℕ) : List K := (List.range n).map fun i ↦ lk M (a + i)

/-- The values of `n` further draws from lane `a` (9 lanes apart). -/
def draws (M : Mem) (a n : ℕ) : List E2 := (List.range n).map fun i ↦ ev2 M (ld2 (a + 9 * i))

theorem scal_succ (M : Mem) (a n : ℕ) : scal M a (n + 1) = ev2 M (ld2 a) :: scal M (a + 2) n := by
  simp only [scal, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply, Nat.succ_eq_add_one]; congr 2; omega

theorem words_succ (M : Mem) (a n : ℕ) : words M a (n + 1) = lk M a :: words M (a + 1) n := by
  simp only [words, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply, Nat.succ_eq_add_one]; congr 1; omega

theorem draws_succ (M : Mem) (a n : ℕ) : draws M a (n + 1) = ev2 M (ld2 a) :: draws M (a + 9) n := by
  simp only [draws, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply, Nat.succ_eq_add_one]; congr 2; omega

theorem layE_succ (a n : ℕ) : (List.range (n + 1)).map (fun i ↦ LEv.e (a + 2 * i)) =
    LEv.e a :: (List.range n).map (fun i ↦ LEv.e (a + 2 + 2 * i)) := by
  simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply]; congr 1; omega

theorem layK_succ (a n : ℕ) : (List.range (n + 1)).map (fun i ↦ LEv.k (a + i)) =
    LEv.k a :: (List.range n).map (fun i ↦ LEv.k (a + 1 + i)) := by
  simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply]; congr 1; omega

theorem layD_succ (a n : ℕ) : (List.range (n + 1)).map (fun i ↦ LEv.d (a + 9 * i) 0) =
    LEv.d a 0 :: (List.range n).map (fun i ↦ LEv.d (a + 9 + 9 * i) 0) := by
  simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply]; congr 1; omega

theorem runs_e2Reads (M : Mem) : ∀ (n a : ℕ),
    Runs M ((List.range n).map fun i ↦ LEv.e (a + 2 * i)) (e2Reads n) (· = scal M a n)
  | 0, a => runs_pure rfl
  | n + 1, a => by
    rw [layE_succ]
    refine runs_bind' (l₁ := [_]) rfl (runs_e2Read M a) fun x hx ↦ runs_bind' (l₂ := [])
      (List.append_nil _).symm (runs_e2Reads M n (a + 2)) fun xs hxs ↦ runs_pure ?_
    rw [scal_succ, hx, hxs]

theorem runs_kReads (M : Mem) : ∀ (n a : ℕ),
    Runs M ((List.range n).map fun i ↦ LEv.k (a + i)) (kReads n) (· = words M a n)
  | 0, a => runs_pure rfl
  | n + 1, a => by
    rw [layK_succ]
    refine runs_bind' (l₁ := [_]) rfl (runs_kRead M a) fun x hx ↦ runs_bind' (l₂ := [])
      (List.append_nil _).symm (runs_kReads M n (a + 1)) fun xs hxs ↦ runs_pure ?_
    rw [words_succ, hx, hxs]

theorem runs_dDraws (M : Mem) : ∀ (n a : ℕ),
    Runs M ((List.range n).map fun i ↦ LEv.d (a + 9 * i) 0) (dDraws n) (· = draws M a n)
  | 0, a => runs_pure rfl
  | n + 1, a => by
    rw [layD_succ]
    refine runs_bind' (l₁ := [_]) rfl (runs_dDraw M a) fun x hx ↦ runs_bind' (l₂ := [])
      (List.append_nil _).symm (runs_dDraws M n (a + 9)) fun xs hxs ↦ runs_pure ?_
    rw [draws_succ, hx, hxs]

/-- **A ground group with further draws** `G(g) D(n)`, laid from `a`. -/
theorem runs_gPoint (M : Mem) {g : ℕ} (hg : g ≤ 64) (n a : ℕ) :
    Runs M (layItems [.G g, .D n] a) (gPoint g n) (· = ev2 M (ld2 (a + 1)) :: draws M (a + 10) n) := by
  simp only [layItems, List.append_nil]
  exact runs_bind' (l₁ := [_, _]) rfl (runs_e2Sample M hg a) fun x hx ↦ runs_bind' (l₂ := [])
    (List.append_nil _).symm (runs_dDraws M n (a + 10)) fun xs hxs ↦ runs_pure (by rw [hx, hxs])

/-- The values of `n` ground draws `G(g)` from lane `a` (answers at `a + 1 + 10 i`). -/
def gdraws (M : Mem) (a n : ℕ) : List E2 := (List.range n).map fun i ↦ ev2 M (ld2 (a + 1 + 10 * i))

theorem gdraws_succ (M : Mem) (a n : ℕ) :
    gdraws M a (n + 1) = ev2 M (ld2 (a + 1)) :: gdraws M (a + 10) n := by
  simp only [gdraws, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ by simp only [Function.comp_apply, Nat.succ_eq_add_one]; congr 2; omega

/-- **`n` ground draws** `G(g)` each, laid from `a`. -/
theorem runs_e2Samples (M : Mem) {g : ℕ} (hg : g ≤ 64) : ∀ (n a : ℕ),
    Runs M (layItems (rep n [.G g]) a) (e2Samples g n) (· = gdraws M a n)
  | 0, a => runs_pure rfl
  | n + 1, a => by
    rw [show rep (n + 1) [V.Item.G g] = [V.Item.G g] ++ rep n [V.Item.G g] from rfl, layItems_append]
    refine runs_bind' (l₁ := [_, _]) (by simp [layItems, layEnd]) (runs_e2Sample M hg a)
      fun x hx ↦ runs_bind' (l₂ := []) (List.append_nil _).symm (runs_e2Samples M hg n (a + 10))
        fun xs hxs ↦ runs_pure ?_
    rw [gdraws_succ, hx, hxs]

end Lvm6.QK
