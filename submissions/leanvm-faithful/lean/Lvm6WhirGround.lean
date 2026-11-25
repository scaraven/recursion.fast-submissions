-- New for lvm6 (WP W1). The challenge field and its group rule as a parameter (`ChalIface`): a
-- group `G(g), D(k)` is a program `grp g k` returning `k + 1` values, specified by its count
-- `grpE` (`2^-g · |bad values| / |F|^(k+1)`); a bind `B` is `sep`. The deployed instance is F1's
-- `grp6`/`doomGrp6`/`doomSep6` (`Lvm6WhirE2`). `PwIface` and `card_pw_tuple`/`pwCount_le` are the
-- answer counts behind it (season 1's grind fact). `NoMv` is season 1's `NoMoves`
-- (`LvmWhirGroupEscape`, which v6 drops) under a new name.
import LvmSpecRulesLeaves
import LvmWhirProb

/-!
# Groups of challenges (BLUEPRINT §1 "Field", §4; FORMAT6 §4; W1)

* `PwIface F`: answers `c : E` with values `dec c ∈ F`, the proof of work `pw g c`, `m` answers per
  value (`|E| = m |F|`) and the grind fact `card_pw`. `card_pw_tuple`, `pwCount_le`: the answer tuples
  with values in `S` that pass the work have measure at most `2^-g · |S| / |F|^(k+1)`.
* `grpE F g k P`: **a group's escape** for bad values `P ⊆ F^(k+1)`: `2^-g · |P| / |F|^(k+1)`.
* `ChalIface F`: **the challenge field and its group rule**: reads `rd`, the group `grp g k`, the bind
  `sep`, with `grpSpec` (from an invariant of the commitments to good values, escape `e` whenever the
  bad values count at most `e`, lead `0`) and `sepSpec` (the bind keeps an invariant).
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
open scoped ENNReal

section

variable {α β : Type}

/-! ## Move-free programs (season 1's `NoMoves`) -/

/-- Every node of the program is a sample, an opening, a return or a rejection. -/
inductive NoMv : VerifierProgram α → Prop where
  | ret (a : α) : NoMv (VerifierProgram.ret a)
  | fail : NoMv VerifierProgram.fail
  | sample {k : E → VerifierProgram α} : (∀ c, NoMv (k c)) → NoMv (VerifierProgram.sample k)
  | query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} :
      (∀ rows, NoMv (k rows)) → NoMv (VerifierProgram.query i ps k)

theorem NoMv.after {p q : VerifierProgram α} (hp : NoMv p) :
    ∀ {l : List Ev}, p.after l = some q → NoMv q := by
  intro l
  induction l generalizing p with
  | nil => intro h; simp [VerifierProgram.after] at h; exact h ▸ hp
  | cons e l ih =>
    intro h
    cases hp with
    | ret a => cases e <;> simp [VerifierProgram.after] at h
    | fail => cases e <;> simp [VerifierProgram.after] at h
    | sample hk =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih (hk _) h
    | query hk =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih (hk _) h

theorem NoMv.not_isMove {q : VerifierProgram α} (hq : NoMv q) : ¬ q.IsMove := by
  cases hq <;> simp [VerifierProgram.IsMove]

/-- The hypothesis of `Spec.ofNoMove`. -/
theorem NoMv.noMove {p : VerifierProgram α} (hp : NoMv p) :
    ∀ {h₀ l : List Ev} {q : VerifierProgram α}, p.Reach h₀ l → p.after l = some q → ¬ q.IsMove :=
  fun _ ha ↦ (hp.after ha).not_isMove

theorem NoMv.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoMv p)
    (hf : ∀ a, NoMv (f a)) : NoMv (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact NoMv.fail
  | sample _ ih => exact NoMv.sample ih
  | query _ ih => exact NoMv.query ih

theorem noMv_sampleE : NoMv sampleChallenge := NoMv.sample fun c ↦ NoMv.ret c

theorem noMv_queryP (i : ℕ) (ps : List ℕ) : NoMv (queryOpenings i ps) :=
  NoMv.query fun rows ↦ NoMv.ret rows

theorem noMv_sampleN : ∀ n, NoMv (sampleChallenges n)
  | 0 => NoMv.ret []
  | n + 1 => noMv_sampleE.bind fun _ ↦ (noMv_sampleN n).bind fun _ ↦ NoMv.ret _

theorem noMv_require (c : Prop) [Decidable c] : NoMv (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split
  · exact NoMv.ret ()
  · exact NoMv.fail

/-- A read leaves the commitments. -/
theorem commits_append_read (h : List Ev) (x : E) : commits (h ++ [Ev.read x]) = commits h := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

end

/-! ## Proof of work on answers -/

/-- **Answers with a proof of work** (the facts behind a group's count): values of answers, the
proof of work, and the grind fact. -/
structure PwIface (F : Type) [Field F] [Fintype F] [DecidableEq F] where
  /-- The challenge value of an answer (deployed: lanes 0–1, `e2OfE`). -/
  dec : E → F
  /-- The proof of work of `g` bits on an answer (deployed: `powOK g`, lane 2). -/
  pw : ℕ → E → Prop
  pwDec : ∀ g c, Decidable (pw g c)
  /-- The answers per value. -/
  m : ℕ
  card_E : Fintype.card E = m * Fintype.card F
  fiber : ∀ y : F, (univ.filter fun c : E ↦ dec c = y).card = m
  /-- The largest grind the fact covers. -/
  gmax : ℕ
  /-- **The grind fact**: at most `2^-g · m · |P|` answers pass `g` bits with a value in `P`. -/
  card_pw : ∀ g ≤ gmax, ∀ P : Finset F,
    (@Finset.card E (@Finset.filter E (fun c ↦ pw g c ∧ dec c ∈ P)
      (fun c ↦ @instDecidableAnd _ _ (pwDec g c) inferInstance) univ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ g * (m * P.card)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (P : PwIface F)

instance PwIface.decPw (g : ℕ) : DecidablePred (P.pw g) := P.pwDec g

/-- The values of a list of answers. -/
def PwIface.decV {k : ℕ} (v : List E) : Fin k → F := fun i ↦ P.dec (v.getD i 0)

theorem PwIface.decV_ofFn {k : ℕ} (f : Fin k → E) :
    P.decV (List.ofFn f) = fun i ↦ P.dec (f i) := by
  funext i
  simp [PwIface.decV, List.getD_eq_getElem?_getD]

/-- **Answer tuples with values in `S`** that pass the proof of work: at most `2^-g m^(k+1) |S|`. -/
theorem card_pw_tuple {g : ℕ} (hg : g ≤ P.gmax) (k : ℕ) (S : Finset (Fin (k + 1) → F)) :
    ((univ.filter fun f : Fin (k + 1) → E ↦ P.pw g (f 0) ∧ (fun i ↦ P.dec (f i)) ∈ S).card :
      ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ g * (P.m : ℝ≥0∞) ^ (k + 1) * S.card := by
  classical
  let s : (Fin (k + 1) → F) → Fin (k + 1) → Finset E := fun u i ↦
    if i = 0 then univ.filter fun c ↦ P.pw g c ∧ P.dec c ∈ ({u 0} : Finset F)
    else univ.filter fun c ↦ P.dec c = u i
  have hsub : (univ.filter fun f : Fin (k + 1) → E ↦ P.pw g (f 0) ∧ (fun i ↦ P.dec (f i)) ∈ S) ⊆
      S.biUnion fun u ↦ Fintype.piFinset (s u) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_biUnion]
    refine ⟨_, hf.2.2, Fintype.mem_piFinset.mpr fun i ↦ ?_⟩
    by_cases hi : i = 0
    · subst hi
      simp [s, hf.2.1]
    · simp [s, hi]
  have hcard : ∀ u, ((Fintype.piFinset (s u)).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ g * (P.m : ℝ≥0∞) ^ (k + 1) := by
    intro u
    rw [Fintype.card_piFinset, Nat.cast_prod, Fin.prod_univ_succ]
    have h0 : ((s u 0).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ g * (P.m * 1) := by
      have := P.card_pw g hg {u 0}
      simpa [s] using this
    have hs : ∀ i : Fin k, ((s u i.succ).card : ℝ≥0∞) = P.m := by
      intro i
      simp only [s, Fin.succ_ne_zero, ↓reduceIte]
      exact_mod_cast P.fiber (u i.succ)
    simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_one] at h0 ⊢
    calc ((s u 0).card : ℝ≥0∞) * (P.m : ℝ≥0∞) ^ k ≤ (2 : ℝ≥0∞)⁻¹ ^ g * P.m * (P.m : ℝ≥0∞) ^ k := by
          gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ g * (P.m : ℝ≥0∞) ^ (k + 1) := by ring
  calc ((univ.filter fun f : Fin (k + 1) → E ↦ P.pw g (f 0) ∧ (fun i ↦ P.dec (f i)) ∈ S).card : ℝ≥0∞)
      ≤ ((S.biUnion fun u ↦ Fintype.piFinset (s u)).card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S, ((Fintype.piFinset (s u)).card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, (2 : ℝ≥0∞)⁻¹ ^ g * (P.m : ℝ≥0∞) ^ (k + 1) := Finset.sum_le_sum fun u _ ↦ hcard u
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring


open Classical in
/-- **The measure of the passing answer tuples** with values in `S`: `2^-g · |S| / |F|^(k+1)`. -/
theorem pwCount_le {g : ℕ} (hg : g ≤ P.gmax) (k : ℕ) (S : Finset (Fin (k + 1) → F)) :
    (Fintype.card E : ℝ≥0∞)⁻¹ ^ (k + 1) *
        ((univ.filter fun f : Fin (k + 1) → E ↦ P.pw g (f 0) ∧ (fun i ↦ P.dec (f i)) ∈ S).card :
          ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ g * S.card / (Fintype.card F : ℝ≥0∞) ^ (k + 1) := by
  have hF : (Fintype.card F : ℝ≥0∞) ≠ 0 := by simp
  have hm : (P.m : ℝ≥0∞) ≠ 0 := by
    intro h
    have := P.card_E
    have hE : 0 < Fintype.card E := Fintype.card_pos
    rw [Nat.cast_eq_zero.mp h, zero_mul] at this
    omega
  calc _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ (k + 1) * ((2 : ℝ≥0∞)⁻¹ ^ g * (P.m : ℝ≥0∞) ^ (k + 1) *
          S.card) := by
        gcongr; exact card_pw_tuple P hg k S
    _ = (2 : ℝ≥0∞)⁻¹ ^ g * S.card / (Fintype.card F : ℝ≥0∞) ^ (k + 1) := by
        rw [P.card_E, Nat.cast_mul, ENNReal.mul_inv (Or.inl hm) (Or.inr hF), mul_pow,
          div_eq_mul_inv, ENNReal.inv_pow]
        have hmk : ((P.m : ℝ≥0∞)⁻¹) ^ (k + 1) * (P.m : ℝ≥0∞) ^ (k + 1) = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel hm (by simp), one_pow]
        calc (P.m : ℝ≥0∞)⁻¹ ^ (k + 1) * (Fintype.card F : ℝ≥0∞)⁻¹ ^ (k + 1) *
              ((2 : ℝ≥0∞)⁻¹ ^ g * (P.m : ℝ≥0∞) ^ (k + 1) * S.card)
            = ((P.m : ℝ≥0∞)⁻¹ ^ (k + 1) * (P.m : ℝ≥0∞) ^ (k + 1)) *
                ((2 : ℝ≥0∞)⁻¹ ^ g * S.card * (Fintype.card F : ℝ≥0∞)⁻¹ ^ (k + 1)) := by ring
          _ = _ := by rw [hmk, one_mul]

/-! ## The challenge field and its group rule -/

open Classical in
/-- **A group's escape** for the bad values `P ⊆ F^(k+1)`: `2^-g · |P| / |F|^(k+1)`. -/
noncomputable def grpE (F : Type) [Fintype F] (g k : ℕ) (P : (Fin (k + 1) → F) → Prop) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ g * ((univ.filter P).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ (k + 1)

/-- The values of a group's list, as a tuple. -/
def gv {F : Type} [Zero F] {k : ℕ} (v : List F) : Fin k → F := fun i ↦ v.getD i 0

/-- **The challenge field and its group rule** (the first half of `OpeningIface`). -/
structure ChalIface (F : Type) [Field F] [Fintype F] [DecidableEq F] where
  /-- The value of a read scalar. -/
  rd : E → F
  /-- The group `G(g), D(k)`: its `k + 1` values. -/
  grp : ℕ → ℕ → VerifierProgram (List F)
  /-- The bind `B`. -/
  sep : VerifierProgram Unit
  /-- The largest grind the rule covers. -/
  gmax : ℕ
  /-- **The group rule**: from an invariant of the commitments, the values are good, escape `e`. -/
  grpSpec : ∀ (g k : ℕ), g ≤ gmax → ∀ (Inv : List (ℕ × ℕ × Word) → Prop)
    (Good : (Fin (k + 1) → F) → List (ℕ × ℕ × Word) → Prop) (e : ℝ≥0∞), e < 1 →
    (∀ cs, Inv cs → grpE F g k (fun u ↦ ¬ Good u cs) ≤ e) →
    Spec (grp g k) (fun h ↦ Inv (commits h)) (fun v h ↦ Good (gv v) (commits h)) e 0 0
  /-- **The bind rule**: an invariant of the commitments survives. -/
  sepSpec : ∀ (Inv : List (ℕ × ℕ × Word) → Prop) (εmax T : ℝ≥0∞),
    Spec sep (fun h ↦ Inv (commits h)) (fun _ h ↦ Inv (commits h)) εmax T T

end Lvm6.Whir
