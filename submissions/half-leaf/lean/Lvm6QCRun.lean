-- New for lvm6 (WP CC). The `V` side of CC's HARs: CB's `Runs` over the opening slots (`RunsO`),
-- its composition, the lift of CB's slots, and the reading primitives of W1's programs at `chalE2`
-- (scalars, ground groups, the bind, a commitment, an opening) and of RS's ring group.
import Lvm6QCStmt
import Lvm6QKRun
import Lvm6KGroup

/-!
# Running a DSL program on the opening slots (`RunsO`)

`RunsO M lay p P` is CB's `Runs` over `OEv`: with the grinds of the slots passing, every event list
matching the slots makes `p` return a value with `P`; `HarO gate g prog lay Rep` is `HsA` of it
(`harO_iff`). `runsO_bind`, `runsO_pure`, `runsO_mono`; `runsO_lift` takes any CB `Runs` fact to the
`.b` slots, and `harO_map_b` says CB's `Har` is `HarO` on them, so CB's and CC's gadgets compose.
Primitives: `runsO_readFs` (W1's `readFs chalE2 = e2Reads`), `runsO_ground` (a ground group
`G(g) D(k)`: the answers' values are the lanes, the grind holds by `PowLayO`), `runsO_sep`,
`runsO_commit`, `runsO_query` (the rows are the slot's words), `runsO_ringProg`.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level)

/-! ## Slots -/

theorem bl_append (l₁ l₂ : List LEv) : bl (l₁ ++ l₂) = bl l₁ ++ bl l₂ := List.map_append

theorem oevMatch_append {M : Mem} : ∀ {l₁ l₂ : List OEv} {evs : List Ev},
    OEvMatch M (l₁ ++ l₂) evs → ∃ e₁ e₂, evs = e₁ ++ e₂ ∧ OEvMatch M l₁ e₁ ∧ OEvMatch M l₂ e₂
  | [], _, evs, h => ⟨[], evs, rfl, List.Forall₂.nil, h⟩
  | x :: l₁, l₂, evs, h => by
    cases h with
    | cons hx hr =>
      obtain ⟨e₁, e₂, rfl, h1, h2⟩ := oevMatch_append hr
      exact ⟨_ :: e₁, e₂, rfl, List.Forall₂.cons hx h1, h2⟩

theorem powLayO_append {M : Mem} {l₁ l₂ : List OEv} (h : PowLayO M (l₁ ++ l₂)) :
    PowLayO M l₁ ∧ PowLayO M l₂ :=
  ⟨fun a g hm ↦ h a g (List.mem_append_left _ hm), fun a g hm ↦ h a g (List.mem_append_right _ hm)⟩

theorem oevMatch_bl {M : Mem} : ∀ {l : List LEv} {evs : List Ev},
    OEvMatch M (bl l) evs ↔ EvMatch M l evs
  | [], evs => by cases evs <;> simp [OEvMatch, EvMatch, bl]
  | x :: l, evs => by
    cases evs with
    | nil => simp [OEvMatch, EvMatch, bl]
    | cons e es =>
      have ih := @oevMatch_bl M l es
      simp only [OEvMatch, EvMatch, bl, List.map_cons, List.forall₂_cons, OEvM] at ih ⊢
      rw [ih]

theorem powLayO_bl {M : Mem} {l : List LEv} : PowLayO M (bl l) ↔ PowLay M l := by
  simp only [PowLayO, PowLay, bl, List.mem_map, OEv.b.injEq]
  exact ⟨fun h a g hm ↦ h a g ⟨_, hm, rfl⟩, fun h a g ⟨_, hm, he⟩ ↦ by subst he; exact h a g hm⟩

/-! ## `RunsO` -/

/-- **`p` runs on the slots `lay`** to a value with `P`. -/
def RunsO {β : Type} (M : Mem) (lay : List OEv) (p : VerifierProgram β) (P : β → Prop) : Prop :=
  PowLayO M lay → ∀ evs, OEvMatch M lay evs → ∃ out, p.after evs = some (.ret out) ∧ P out

theorem harO_iff {α β : Type} (gate : Cell) (g : BM α) (prog : VerifierProgram β) (lay : List OEv)
    (Rep : Mem → α → β → Prop) :
    HarO gate g prog lay Rep ↔ ∀ c M, gate.val M = 1 → HsA c M g fun o ↦ RunsO M lay prog (Rep M o) :=
  Iff.rfl

/-- **CB's slots lift**: a `Runs` fact is a `RunsO` fact on the `.b` slots. -/
theorem runsO_lift {β : Type} {M : Mem} {lay : List LEv} {p : VerifierProgram β} {P : β → Prop}
    (h : Runs M lay p P) : RunsO M (bl lay) p P := fun hp evs he ↦
  h (powLayO_bl.mp hp) evs (oevMatch_bl.mp he)

/-- **CB's `Har` is `HarO` on the `.b` slots.** -/
theorem harO_map_b {α β : Type} (gate : Cell) (g : BM α) (prog : VerifierProgram β) (lay : List LEv)
    (Rep : Mem → α → β → Prop) : Har gate g prog lay Rep ↔ HarO gate g prog (bl lay) Rep := by
  constructor
  · intro h c M hg
    exact hsA_mono (h c M hg) fun o ho hp evs he ↦ ho (powLayO_bl.mp hp) evs (oevMatch_bl.mp he)
  · intro h c M hg
    exact hsA_mono (h c M hg) fun o ho hp evs he ↦ ho (powLayO_bl.mpr hp) evs (oevMatch_bl.mpr he)

theorem runsO_mono {β : Type} {M : Mem} {lay : List OEv} {p : VerifierProgram β} {P Q : β → Prop}
    (h : RunsO M lay p P) (hPQ : ∀ b, P b → Q b) : RunsO M lay p Q := fun hp evs he ↦ by
  obtain ⟨out, h1, h2⟩ := h hp evs he
  exact ⟨out, h1, hPQ _ h2⟩

theorem runsO_pure {β : Type} {M : Mem} {b : β} {P : β → Prop} (h : P b) :
    RunsO M [] (pure b : VerifierProgram β) P := fun _ evs he ↦ by
  cases he
  exact ⟨b, rfl, h⟩

theorem runsO_bind {β γ : Type} {M : Mem} {l₁ l₂ : List OEv} {p : VerifierProgram β}
    {f : β → VerifierProgram γ} {P : β → Prop} {Q : γ → Prop} (hp : RunsO M l₁ p P)
    (hf : ∀ b, P b → RunsO M l₂ (f b) Q) : RunsO M (l₁ ++ l₂) (p >>= f) Q := fun hpw evs he ↦ by
  obtain ⟨hw1, hw2⟩ := powLayO_append hpw
  obtain ⟨e₁, e₂, rfl, h1, h2⟩ := oevMatch_append he
  obtain ⟨b, hb, hPb⟩ := hp hw1 e₁ h1
  obtain ⟨out, ho, hQ⟩ := hf b hPb hw2 e₂ h2
  refine ⟨out, ?_, hQ⟩
  show (p.bind f).after (e₁ ++ e₂) = _
  rw [VerifierProgram.after_bind_append f hb e₂, ho]

/-- `runsO_bind` with the slots given as one list. -/
theorem runsO_bind' {β γ : Type} {M : Mem} {l₁ l₂ l : List OEv} {p : VerifierProgram β}
    {f : β → VerifierProgram γ} {P : β → Prop} {Q : γ → Prop} (hl : l = l₁ ++ l₂)
    (hp : RunsO M l₁ p P) (hf : ∀ b, P b → RunsO M l₂ (f b) Q) : RunsO M l (p >>= f) Q :=
  hl ▸ runsO_bind hp hf

/-! ## Primitives -/

/-- W1's reads at `chalE2` are K1's `E2` reads. -/
theorem readFs_eq : ∀ n, Whir.readFs Whir.chalE2 n = e2Reads n
  | 0 => rfl
  | n + 1 => by
    show (Whir.readF Whir.chalE2 >>= fun x ↦ Whir.readFs Whir.chalE2 n >>= fun xs ↦ pure (x :: xs)) = _
    rw [readFs_eq n]
    rfl

theorem runsO_readFs (M : Mem) (n a : ℕ) :
    RunsO M (bl (layItems [.E n] a)) (Whir.readFs Whir.chalE2 n) (· = scal M a n) := by
  rw [readFs_eq]
  simp only [layItems, List.append_nil]
  exact runsO_lift (runs_e2Reads M n a)

theorem runsO_readF (M : Mem) (a : ℕ) :
    RunsO M (bl (layItems [.E 1] a)) (Whir.readF Whir.chalE2) (· = ev2 M (ld2 a)) := by
  simp only [layItems, List.append_nil, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
    Nat.add_zero]
  exact runsO_lift (runs_e2Read M a)

/-- One draw: its value is the answer's lanes 0–1. -/
theorem runsO_sample (M : Mem) (a g : ℕ) :
    RunsO M [.b (.d a g)] VerifierProgram.sampleChallenge (fun x ↦ e2OfE x = ev2 M (ld2 a) ∧
      x.limb 2 = lk M (a + 2)) := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | sample x =>
      obtain ⟨h0, h1, h2⟩ := hx
      exact ⟨x, rfl, by rw [ev2_ld2, e2OfE, h0, h1], h2⟩
    | _ => exact absurd hx (by simp [OEvM, EvM])

/-- The values of `k` draws from lane `a` (9 lanes apart). -/
theorem runsO_samples (M : Mem) : ∀ (k a : ℕ),
    RunsO M (bl ((List.range k).map fun i ↦ LEv.d (a + 9 * i) 0)) (VerifierProgram.sampleChallenges k)
      (fun cs ↦ cs.map e2OfE = draws M a k)
  | 0, a => runsO_pure rfl
  | k + 1, a => by
    rw [layD_succ]
    refine runsO_bind' (l₁ := [_]) rfl (runsO_sample M a 0) fun x hx ↦ runsO_bind' (l₂ := [])
      (List.append_nil _).symm (runsO_samples M k (a + 9)) fun xs hxs ↦ runsO_pure ?_
    rw [draws_succ, List.map_cons, hx.1, hxs]

theorem runsO_require {M : Mem} {c : Prop} [Decidable c] (hc : c) :
    RunsO M [] (VerifierProgram.require c) fun _ ↦ True :=
  fun _ evs he ↦ by
    cases he
    exact ⟨(), by simp [VerifierProgram.require, hc, VerifierProgram.after], trivial⟩

/-- **A ground group** `G(g) D(k)` from lane `a` (W1's `chalE2.grp` = F1's `grp6` = K1's `gPoint`):
the values are the lanes (the ground answer at `a + 1`, the further draws from `a + 10`), the grind
holds on the PoW lane. -/
theorem runsO_ground (M : Mem) {g : ℕ} (hg : g ≤ 64) (k a : ℕ) :
    RunsO M (bl (layItems [.G g, .D k] a)) (Whir.chalE2.grp g k)
      (· = ev2 M (ld2 (a + 1)) :: draws M (a + 10) k) := by
  show RunsO M _ (grp6 g k) _
  rw [← Lvm6.K.gPoint_eq_grp6]
  exact runsO_lift (runs_gPoint M hg k a)

/-- The answer `j` of a ground group with its nonce at `a`: the ground answer, then the draws. -/
def ansAt (a j : ℕ) : C2 := if j = 0 then ld2 (a + 1) else ld2 (a + 10 + 9 * (j - 1))

theorem ground_ans {M : Mem} {a k : ℕ} {v : List E2}
    (hv : v = ev2 M (ld2 (a + 1)) :: draws M (a + 10) k) {j : ℕ} (hj : j ≤ k) :
    v.getD j 0 = ev2 M (ansAt a j) := by
  subst hv
  rcases j with _ | j
  · simp [ansAt]
  · simp only [List.getD_cons_succ, draws, ansAt]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp

/-- The same for raw answers decoded by `e2OfE`. -/
theorem ground_ansE {M : Mem} {a k : ℕ} {v : List E}
    (hv : v.map e2OfE = ev2 M (ld2 (a + 1)) :: draws M (a + 10) k) {j : ℕ} (hj : j ≤ k) :
    e2OfE (v.getD j 0) = ev2 M (ansAt a j) := by
  have hlen : v.length = k + 1 := by
    have := congrArg List.length hv
    simpa [draws] using this
  have hj' : j < v.length := by omega
  have h3 : (v.map e2OfE)[j]? = some (e2OfE (v.getD j 0)) := by
    rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rfl
  rw [hv] at h3
  rcases j with _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h3
    simp [ansAt, h3]
  · simp only [List.getElem?_cons_succ, draws, List.getElem?_map,
      List.getElem?_range (by omega : j < k), Option.map_some, Option.some.injEq] at h3
    rw [← h3]
    simp [ansAt]

/-- **A bind** (FORMAT6 §4 `B`, W1's `chalE2.sep` = `e2Sep`): one draw at `a`, value discarded. -/
theorem runsO_sep (M : Mem) (a : ℕ) : RunsO M [.b (.d a 0)] Whir.chalE2.sep fun _ ↦ True :=
  runsO_bind' (l₂ := []) (List.append_nil _).symm (runsO_sample M a 0) fun _ _ ↦
    runsO_pure (P := fun _ : Unit ↦ True) trivial

/-- **A commitment** of the slot's shape. -/
theorem runsO_commit (M : Mem) (ht wd : ℕ) :
    RunsO M [.c ht wd] (VerifierProgram.readCommitment ht wd) fun _ ↦ True := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | commit h w word =>
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨(), by simp [VerifierProgram.readCommitment, VerifierProgram.after], trivial⟩
    | _ => exact absurd hx (by simp [OEvM])

/-- **An opening**: the rows are the slot's words. -/
theorem runsO_query (M : Mem) (i : ℕ) (ps : List ℕ) (rows : List (List (Option ℕ))) :
    RunsO M [.o rows] (VerifierProgram.queryOpenings i ps) (· = rowsOf M rows) := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | query rs =>
      exact ⟨rs, by simp [VerifierProgram.queryOpenings, VerifierProgram.after], hx⟩
    | _ => exact absurd hx (by simp [OEvM])

end Lvm6.QC
