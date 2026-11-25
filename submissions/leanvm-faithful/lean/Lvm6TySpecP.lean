-- New for lvm6 Y1 (2026-11-22): merged module (build cost: one import load), parts:
--   Lvm6TyZero: the zerocheck at `E2` (`zeroProgE`): the relation's table on 20 bits, `τ` by the
--   Lvm6TyRegion: the region facts of the typed phases at `E2` (season 1's `LvmE2TRegion` on
--   Lvm6TyAcc: A23 at `E2` over `Φ_Q` in 43 variables (`accProgE`): season 1's `LvmE2TAcc`
--   Lvm6TyWire: the wiring and the relayout at `E2` (`wireProgE`, `relayProgE`): season 1's
--   Lvm6TySpecP: the proof of `TypedSpecEStmt` from the mini-bus's frozen statement: the zerocheck,
import Lvm6TyProg
import LvmE2TSum
import LvmE2VZero
import LvmAccSpec
import Lvm6MbSample
import Lvm6Params

/-! ### Part `Lvm6TyZero` (was its own module) -/
section

/-!
# The zerocheck at `E2` (lvm6)

* **The entries fit** (`entsX_fit`, `entsT_fit`): every entry of a checked layout has `x < 2^20`, `y < 2^21`
  (and `o' < 12` at `E2`); off the cube the matrices vanish (`matZT_out`).
* **The table** `deltaZE x = rel(x)` (`relE` read in `E2`) on 20 bits; `wiringRelE_of_zeroOn`: the table vanishing
  on the cube is `WiringRelE` (off the cube no slot has entries).
* **The summand** `zeroGE pt = Ã(pt)·B̃(pt) + C̃(pt)` (the three columns' extensions), degree 2 per coordinate;
  on the cube it is the table (`zeroGE_bits`), so the equality cube sum at `τ` is the folded table
  (`zeroGE_cube`).
* **`zeroSpecE`**: from doom of the table on the cube to doom of "the three values are the columns' extensions at
  `r_x`"; lead `0`; groups `τ_i` (`errG gTau 1`) and the rounds (`errG gZero 2`).
-/

set_option autoImplicit false

namespace Lvm6.Ty

open Lvm (FE2 FK)
open Lvm.Loop Lvm.Typed Lvm.E2V Lvm.E2T LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Finset
open scoped ENNReal

/-! ## The entries fit -/

/-- An entry of `instEntsX`: matrix `o < 8`, its instance's slot, a word of a cell or the word `1`. -/
theorem instEntsX_mem (Q : Program) (lay : Lay) (i : Inst) {e : Ent} (he : e ∈ instEntsX Q lay i) :
    e.o < 8 ∧ e.x = lay.slot i.blk i.t i.jf ∧ (e.y = lay.one ∨ ∃ τ n w, (e.y, e.c) ∈ lay.cellEnts τ n w) := by
  unfold instEntsX at he
  split at he
  · simp only [List.mem_append] at he
    rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he <;> obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he <;>
      exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
  · simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he <;> obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he
    · refine ⟨by omega, h2, ?_⟩
      simp only [List.mem_append, List.mem_singleton] at h3
      rcases h3 with (h3 | h3) | h3
      · exact Or.inr ⟨_, _, _, h3⟩
      · exact Or.inr ⟨_, _, _, h3⟩
      · exact Or.inl (Prod.mk.inj h3).1
    · refine ⟨by omega, h2, ?_⟩
      simp only [List.mem_append, List.mem_singleton] at h3
      rcases h3 with (h3 | h3) | h3
      · exact Or.inr ⟨_, _, _, h3⟩
      · exact Or.inr ⟨_, _, _, h3⟩
      · exact Or.inl (Prod.mk.inj h3).1
    · exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
    · exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
  · exact absurd he List.not_mem_nil
  · obtain ⟨h1, h2, h3⟩ := lh_instEnts_mem Q lay i he
    exact ⟨by omega, h2, h3⟩

/-- **Every entry of `entsX` lies on the cube** (a checked layout): `o < 8`, `x < 2^20`, `y < 2^21`. -/
theorem entsX_fit (Q : Program) (lay : Lay) (hlay : lay.Ok Q) :
    ∀ e ∈ entsX Q lay, e.o < 8 ∧ e.x < 2 ^ xVars ∧ e.y < 2 ^ yVars := by
  have hone := (lh_ok hlay).2.2.2.2.2.2.2.2.1
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, jf, hjf, t, -, rfl⟩ := lh_mem_insts hi
    obtain ⟨h1, h2, h3⟩ := instEntsX_mem Q lay _ he
    refine ⟨h1, h2 ▸ lh_slot_lt hlay hb hjf t, ?_⟩
    rcases h3 with h3 | ⟨τ, n, w, h3⟩
    · rw [h3]; exact hone
    · exact lh_cellEnts_lt hlay τ n w _ h3
  · have := ents_fit Q lay hlay e (List.mem_append_right _ he)
    exact ⟨by omega, this.2.1, this.2.2⟩

/-- Every entry at `E2` sits in one of the twelve used slots `m + 4j` (`m < 4`, `j < 3`). -/
theorem entsT_o (Q : Program) (lay : Lay) : ∀ e ∈ entsT Q lay, e.o < 12 := by
  intro e he
  unfold entsT at he
  obtain ⟨e₀, -, he₀⟩ := List.mem_flatMap.mp he
  unfold splitEnt at he₀
  obtain ⟨j, hj, hje⟩ := List.mem_filterMap.mp he₀
  have hj3 : j < 3 := List.mem_range.mp hj
  split at hje
  · exact absurd hje (by simp)
  · rw [Option.some.injEq] at hje
    rw [← hje]
    dsimp only
    (clear * - e₀ j hj3; omega)

/-- **Every entry at `E2` lies on the cube** (a checked layout): `o' < 12`, `x < 2^20`, `y < 2^21`. -/
theorem entsT_fit (Q : Program) (lay : Lay) (hlay : lay.Ok Q) :
    ∀ e ∈ entsT Q lay, e.o < 12 ∧ e.x < 2 ^ xVars ∧ e.y < 2 ^ yVars := by
  intro e he
  refine ⟨entsT_o Q lay e he, ?_⟩
  obtain ⟨e₀, he₀, hs⟩ := List.mem_flatMap.mp he
  obtain ⟨j, -, hje⟩ := List.mem_filterMap.mp hs
  have hf := entsX_fit Q lay hlay e₀ he₀
  split at hje
  · exact absurd hje (by simp)
  · rw [Option.some.injEq] at hje
    rw [← hje]
    exact ⟨hf.2.1, hf.2.2⟩

/-- **Off the cube the matrices vanish** (a checked layout). -/
theorem matZT_out (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) {x : ℕ} (hx : ¬ x < 2 ^ xVars)
    (o : ℕ) : matZT Q lay o z x = 0 := by
  unfold matZT
  rw [List.filter_eq_nil_iff.mpr fun e he ↦ by
    have := (entsT_fit Q lay hlay e he).2.1
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro _ hex; omega]
  rfl

/-! ## The table and the relation -/

/-- **The relation as a table on 20 bits**: `rel(x)` in `E2`. -/
def deltaZE (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : E2 := FE2.toE2 (relE Q lay z x)

/-- **The table vanishing on the cube is the relation** (a checked layout: off the cube no slot has entries). -/
theorem wiringRelE_of_zeroOn (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK)
    (h : ZeroOnF (deltaZE Q lay z) [] xVars) : WiringRelE Q lay z := by
  rw [zeroOnF_nil] at h
  intro x
  by_cases hx : x < 2 ^ xVars
  · exact FE2.toE2_injective ((h x hx).trans FE2.toE2_zero.symm)
  · simp [relE, matZT_out Q lay hlay z hx]

/-- **Without `E3` rows every entry at `E2` is coordinate 0** (`o' < 4`). -/
theorem entsT_o_noE3 (Q : Program) (lay : Lay) (h : NoE3 Q lay) : ∀ e ∈ entsT Q lay, e.o < 4 := by
  intro e he
  obtain ⟨e₀, he₀, hs⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, hje⟩ := List.mem_filterMap.mp hs
  have hj3 : j < 3 := List.mem_range.mp hj
  obtain ⟨h1, h2⟩ := h e₀ he₀
  split at hje
  · exact absurd hje (by simp)
  · rename_i hne
    rw [Option.some.injEq] at hje
    rw [← hje]
    dsimp only
    have hj0 : j = 0 := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rfl
      · exact absurd (by simp [feCoord, h1]) hne
      · exact absurd (by simp [feCoord, h2]) hne
    subst hj0
    omega

/-- Without `E3` rows the matrices `o' ≥ 4` vanish. -/
theorem matZT_hi (Q : Program) (lay : Lay) (h : NoE3 Q lay) (z : ℕ → FK) (x : ℕ) {o : ℕ} (ho : 4 ≤ o) :
    matZT Q lay o z x = 0 := by
  unfold matZT
  rw [List.filter_eq_nil_iff.mpr fun e he ↦ by
    have := entsT_o_noE3 Q lay h e he
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro heo; omega]
  rfl

/-- **Without `E3` rows the relation at `E2` is season 1's** (`relT`'s coordinates 1 and 2 vanish, coordinate 0
is `relE`). -/
theorem wiringRelE_iff {Q : Program} {lay : Lay} {z : ℕ → FK} (_hlay : lay.Ok Q) (h : NoE3 Q lay) :
    WiringRelE Q lay z ↔ WiringRelT Q lay z := by
  have hz : ∀ x o, 4 ≤ o → matZT Q lay o z x = 0 := fun x o ho ↦ matZT_hi Q lay h z x ho
  have h0 : ∀ x, relT Q lay z x 0 = relE Q lay z x := fun x ↦ by
    simp [relT, mulY3, relE, hz]
  constructor
  · intro hE x k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · rw [h0]; exact hE x
    · simp [relT, mulY3, hz]
    · simp [relT, mulY3, hz]
  · intro hT x
    rw [← h0]; exact hT x 0 (by norm_num)

/-! ## The columns and the summand -/

/-- The three columns at slot `x`: `A = M_0 z`, `B = M_1 z`, `C = M_2 z + M_3 z`, in `E2`. -/
def colE (Q : Program) (lay : Lay) (z : ℕ → FK) (j x : ℕ) : E2 :=
  if j = 0 then FE2.toE2 (matZT Q lay 0 z x)
  else if j = 1 then FE2.toE2 (matZT Q lay 1 z x)
  else FE2.toE2 (matZT Q lay 2 z x + matZT Q lay 3 z x)

/-- A column's extension at a point (`r_x`: 20 coordinates). The range is `2^|pt|`, never a literal (the kernel
must never evaluate the `2^20`-element range in a defeq check). -/
def mleXE (pt : List E2) (f : ℕ → E2) : E2 := ∑ w ∈ range (2 ^ pt.length), eqAtF pt w * f w

/-- The three columns' extensions at `pt`. -/
def vals3 (Q : Program) (lay : Lay) (z : ℕ → FK) (pt : List E2) : List E2 :=
  [mleXE pt (colE Q lay z 0), mleXE pt (colE Q lay z 1), mleXE pt (colE Q lay z 2)]

/-- The zerocheck's final value on three values: `A·B + C`. -/
def zfinE (v : List E2) : E2 := v.getD 0 0 * v.getD 1 0 + v.getD 2 0

/-- **The zerocheck's summand**: `A·B + C` of the three columns' extensions. -/
def zeroGE (Q : Program) (lay : Lay) (z : ℕ → FK) (pt : List E2) : E2 := zfinE (vals3 Q lay z pt)

theorem polyLEF_mleXE (pre post : List E2) (f : ℕ → E2) : PolyLEF 1 fun x ↦ mleXE (pre ++ x :: post) f :=
  (polyLEF_mle pre post (2 ^ (pre.length + post.length + 1)) f).congr fun x ↦ by
    rw [mleXE, List.length_append, List.length_cons, Nat.add_assoc]

/-- **The summand has degree 2 in each coordinate.** -/
theorem polyLEF_zeroGE (Q : Program) (lay : Lay) (z : ℕ → FK) (pre post : List E2) :
    PolyLEF 2 fun x ↦ zeroGE Q lay z (pre ++ x :: post) :=
  PolyLEF.add (PolyLEF.mul (polyLEF_mleXE pre post _) (polyLEF_mleXE pre post _))
    ((polyLEF_mleXE pre post _).mono (by norm_num))

theorem mleXE_bits {u : ℕ} (hu : u < 2 ^ xVars) (f : ℕ → E2) : mleXE (bitsF u xVars) f = f u := by
  rw [mleXE, bitsF_length]
  exact sum_eqAtF_bitsF hu f

/-- **On the cube, the summand is the table.** -/
theorem zeroGE_bits (Q : Program) (lay : Lay) (z : ℕ → FK) {u : ℕ} (hu : u < 2 ^ xVars) :
    zeroGE Q lay z (bitsF u xVars) = deltaZE Q lay z u := by
  simp only [zeroGE, zfinE, vals3, List.getD_cons_zero, List.getD_cons_succ, mleXE_bits hu, colE, deltaZE,
    relE, FE2.toE2_add, FE2.fe2_mul_eq]
  simp

/-- **The zerocheck's start**: the equality cube sum of the summand at `τ` is the folded table. -/
theorem zeroGE_cube (Q : Program) (lay : Lay) (z : ℕ → FK) {τ : List E2} (hτ : τ.length = xVars) :
    eqCubeSumF τ xVars (zeroGE Q lay z) [] = foldTF (deltaZE Q lay z) τ 0 := by
  rw [eqCubeSumF_nil, foldTF, hτ]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [zeroGE_bits Q lay z (Finset.mem_range.mp hu), mul_zero, add_zero]

/-! ## The phase -/

section Phase

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}
variable (Q : Program) (lay : Lay) (zq : β → ℕ → FK) (R : β → Prop)

/-- **The zerocheck at `E2`**: from doom of the relation's table on the cube to doom of "the three values are the
columns' extensions at `r_x`"; lead `0`; groups `τ_i` (`errG gTau 1`) and the rounds (`errG gZero 2`), each with
follower `0`. -/
noncomputable def zeroSpecE (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (hτ : (L₀ : ℝ≥0∞) * errG gTau 1 + 0 ≤ εmax) (hz : (L₀ : ℝ≥0∞) * errG gZero 2 + 0 ≤ εmax) (hT : T ≤ εmax) :
    Spec zeroProgE (Doomed C (fun q ↦ ZeroOnF (deltaZE Q lay (zq q)) [] xVars ∧ R q))
      (fun r h ↦ r.1.length = xVars ∧ r.2.length = 3 ∧
        Doomed C (fun q ↦ r.2 = vals3 Q lay (zq q) r.1 ∧ R q) h) εmax 0 T := by
  unfold zeroProgE
  refine (zeroSpecE2 (T := 0) hst hcard (g := gTau) (by norm_num) (fun q ↦ deltaZE Q lay (zq q)) R
    (n := xVars) (m := xVars - 1) (by norm_num) hτ).bind' fun τ ↦ ?_
  exact if hτl : τ.length = xVars then
    ((eqSumcheckGSpec (T := 0) hst hcard R (Fm := fun q acc ↦ eqCubeSumF τ xVars (zeroGE Q lay (zq q)) acc)
        (eqCubeSumF_eqFamily τ xVars 2 hτl _ fun q pre post ↦ polyLEF_zeroGE Q lay (zq q) pre post)
        (count := 3) (by norm_num) (by norm_num) (g := gZero) (by norm_num) hz τ [] 0 (by simp)).mono
      (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ ⟨fun v hv ↦ by
          rw [hτl, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hv
          rw [hv, ← zeroGE_cube Q lay (zq q) hτl]
          exact hq.1.symm, hq.2⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl zero_le).bind' fun rf ↦
    if hrf : rf.1.length = xVars then
      ((e2ReadsSpec hst (fun q ↦ rf.2 = eqCubeSumF τ xVars (zeroGE Q lay (zq q)) ([] ++ rf.1) ∧ R q)
          hT 2).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl zero_le le_rfl).bind' fun v ↦
        (Spec.require (Pre := fun h ↦ v.length = 3 ∧ Doomed C (fun q ↦
            rf.2 = eqCubeSumF τ xVars (zeroGE Q lay (zq q)) ([] ++ rf.1) ∧ R q) h)
          (Post := fun _ h ↦ v.length = 3 ∧ Doomed C (fun q ↦ v = vals3 Q lay (zq q) rf.1 ∧ R q) h)
          fun _ hp hc ↦ ⟨hp.1, Doomed.mono hp.2 fun q hq ↦ ⟨by
            rw [List.nil_append, eqCubeSumF_full _ _ _ hrf hτl, hc, zeroGE, hq.1]; rfl, hq.2⟩⟩).bind' fun _ ↦
          (Spec.ret (Post := fun r h ↦ r.1.length = xVars ∧ r.2.length = 3 ∧
              Doomed C (fun q ↦ r.2 = vals3 Q lay (zq q) r.1 ∧ R q) h) (rf.1, v)).mono
            (fun _ hp ↦ ⟨hrf, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hrf (hp.1.trans (by simp [hτl]))) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hτl (hp.1.trans (by norm_num))) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Phase

end Lvm6.Ty
end -- part Lvm6TyZero

/-! ### Part `Lvm6TyRegion` (was its own module) -/
section

/-!
# The typed phases' region facts at `E2` (lvm6)

* **Region sums, generic** (`regSumW` over any `AddCommMonoid`): `sum_regionsW`, `regSumW_sources`,
  `regSumW_congr`, `sum_regSumW`, `regSumW_mul`.
* **The instance** (`TInst6`): sorted regions (`yregs_pairwise`), a region's words have its source (`src?_mem`),
  `comCell_of_lt`.
* **`zwE`** (a word in `E2`), **`mleYE`** (`z̃` on the `2^21` words); **`mleZ_zOfE`**: `z̃(r_y)` of a candidate's
  words is the committed, `S_flat`, `σ′`, `KS` region sums and the executable `virtE`.
* **The relayout's family**: `recE`, `relayGE` (kernel times `C_rec`'s extension, degree 2 per coordinate),
  **`relay_trueE`** (its cube sum is `S_flat`'s true region sum).
* **The claims mean the true values**: **`holds_regClaimE`** (a region claim holds iff the region sum of the
  column's words is its value), `holds_comE`, `holds_ksE`, `holds_sigmaE`; **`holds_relayPointE`** (the
  relayout's point claim on `C_rec` gives `v_R = C̃_rec(r)`).
-/

set_option autoImplicit false

namespace Lvm6.Ty

open Lvm (FE2 FK)
open Lvm.Typed Lvm.E2V Lvm.E2T LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open Lvm6.Mb (ClaimE BClaimG eqAboveG kG)

/-! ## Region sums over any commutative monoid -/

section Gen

variable {M : Type} [AddCommMonoid M]

theorem listRange_sumW (n : ℕ) (f : ℕ → M) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A finite sum of list sums is the list sum of the finite sums. -/
theorem sum_list_swapW {α ι : Type} (s : Finset ι) (l : List α) (F : α → ι → M) :
    ∑ u ∈ s, (l.map fun a ↦ F a u).sum = (l.map fun a ↦ ∑ u ∈ s, F a u).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **The cube sum splits into the regions' sums** (sorted regions inside `[0, N)`, `f` zero off them). -/
theorem sum_regionsW (N : ℕ) : ∀ (L : List YReg), L.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base) →
    (∀ r ∈ L, r.base + 2 ^ r.log ≤ N) → ∀ (f : ℕ → M), (∀ y, (∀ reg ∈ L, ¬ reg.Has y) → f y = 0) →
    ∑ y ∈ range N, f y = (L.map fun reg ↦ ∑ i ∈ range (2 ^ reg.log), f (reg.base + i)).sum
  | [], _, _, f, hf => by
    simp only [List.map_nil, List.sum_nil]
    exact Finset.sum_eq_zero fun y _ ↦ hf y (by simp)
  | r :: rs, hP, hN, f, hf => by
    have hrN := hN r (List.mem_cons_self ..)
    have hsplit : ∑ y ∈ range N, f y = ∑ y ∈ range N, (if r.Has y then f y else 0) +
        ∑ y ∈ range N, (if r.Has y then 0 else f y) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> simp
    have h1 : ∑ y ∈ range N, (if r.Has y then f y else 0) = ∑ i ∈ range (2 ^ r.log), f (r.base + i) := by
      rw [← Finset.sum_filter]
      have hset : (range N).filter (fun y ↦ r.Has y) = Finset.Ico r.base (r.base + 2 ^ r.log) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, YReg.Has]; omega
      rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have h2 := sum_regionsW N rs (List.Pairwise.of_cons hP) (fun x hx ↦ hN x (List.mem_cons_of_mem _ hx))
      (fun y ↦ if r.Has y then 0 else f y) (fun y hy ↦ by
        split_ifs with hr
        · rfl
        · exact hf y fun reg hreg ↦ by
            rcases List.mem_cons.mp hreg with rfl | hreg
            · exact hr
            · exact hy reg hreg)
    rw [hsplit, h1, h2, List.map_cons, List.sum_cons]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ Finset.sum_congr rfl fun i _ ↦ ?_)
    have hle := List.rel_of_pairwise_cons hP hreg
    rw [ite_eq_right (by simp only [YReg.Has]; omega)]

variable (Ti : TInst6)

/-- **The seven sources' region sums** add up to the regions' sums. -/
theorem regSumW_sources (f : ℕ → M) :
    regSumW Ti (· == .com) f + regSumW Ti (· == .sflat) f + regSumW Ti (· == .sigma) f +
        regSumW Ti (· == .ks) f + (regSumW Ti (· == .pub) f + regSumW Ti (· == .qlt) f +
          regSumW Ti (· == .one) f) =
      (Ti.lay.yregs.map fun reg ↦ ∑ i ∈ range (2 ^ reg.log), f (reg.base + i)).sum := by
  unfold regSumW
  generalize Ti.lay.yregs = L
  induction L with
  | nil => simp
  | cons reg L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, listRange_sumW]
    cases reg.src <;> simp <;> abel

/-- Region sums agree when their functions agree on the regions' words. -/
theorem regSumW_congr (S : YSrc → Bool) {f g : ℕ → M}
    (h : ∀ reg ∈ Ti.lay.yregs, S reg.src = true → ∀ i < 2 ^ reg.log, f (reg.base + i) = g (reg.base + i)) :
    regSumW Ti S f = regSumW Ti S g := by
  unfold regSumW
  refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ ?_)
  split_ifs with hS
  · refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    rw [h reg hreg hS i (List.mem_range.mp hi)]
  · rfl

/-- A finite sum of region sums is the region sum of the finite sums. -/
theorem sum_regSumW {ι : Type} (S : YSrc → Bool) (s : Finset ι) (G : ι → ℕ → M) :
    ∑ u ∈ s, regSumW Ti S (G u) = regSumW Ti S fun y ↦ ∑ u ∈ s, G u y := by
  unfold regSumW
  rw [sum_list_swapW]
  refine congrArg List.sum (List.map_congr_left fun reg _ ↦ ?_)
  split_ifs
  · exact sum_list_swapW s _ _
  · exact Finset.sum_const_zero

end Gen

/-- A region sum times a constant. -/
theorem regSumW_mul {R : Type} [CommSemiring R] (Ti : TInst6) (S : YSrc → Bool) (f : ℕ → R) (c : R) :
    regSumW Ti S f * c = regSumW Ti S fun y ↦ f y * c := by
  unfold regSumW
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun reg _ ↦ ?_)
  split_ifs
  · rw [← List.sum_map_mul_right]
  · exact zero_mul c

/-- A list sum of functions of degree `d` has degree `d`. -/
theorem polyLEF_listSumE {F : Type} [Field F] {α : Type} (d : ℕ) (l : List α) (G : α → F → F)
    (h : ∀ a ∈ l, PolyLEF d (G a)) : PolyLEF d fun x ↦ (l.map fun a ↦ G a x).sum := by
  induction l with
  | nil => exact (PolyLEF.const d 0).congr fun _ ↦ rfl
  | cons a l ih =>
    exact (PolyLEF.add (h a (List.mem_cons_self ..))
      (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))).congr fun _ ↦ rfl

/-! ## The instance -/

section Inst

variable (Ti : TInst6) (L : Lvm.M3.Lay)

theorem src?_eq (y : ℕ) : Ti.src? y = ysrcL Ti.lay.yregs y := rfl

/-- **The regions of a checked instance are sorted, disjoint and inside the word space.** -/
theorem yregs_pairwise (hTi : Ti.Ok) :
    Ti.lay.yregs.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base) ∧
      ∀ r ∈ Ti.lay.yregs, r.base + 2 ^ r.log ≤ 2 ^ yVars := by
  have h := hTi.1
  unfold Lay.Ok Lay.okB at h
  simp only [Bool.and_eq_true] at h
  exact yregsSorted_pairwise _ h.1.1.1.1.2

/-- A region's words have its source. -/
theorem src?_mem (hTi : Ti.Ok) {reg : YReg} (hreg : reg ∈ Ti.lay.yregs) {i : ℕ} (hi : i < 2 ^ reg.log) :
    Ti.src? (reg.base + i) = some reg.src :=
  ysrcL_of_mem (yregs_pairwise Ti hTi).1 hreg hi

/-- A commitment's cell inside it is its word's entry. -/
theorem comCell_of_lt (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) {n : ℕ}
    (hn : n < 2 ^ (if rec then L.nuRec else L.nuMain)) :
    TInst6.comCell L qm qr rec n = if rec then qr.values.getD n 0 else qm.values.getD n 0 := by
  cases rec
  · simp only [Bool.false_eq_true, ite_false] at hn ⊢
    simp [TInst6.comCell, hn, Vector.getD, Array.getD]
  · simp only [ite_true] at hn ⊢
    simp [TInst6.comCell, hn, Vector.getD, Array.getD]

end Inst

/-! ## Words at `E2` -/

/-- A word at `E2`. -/
def zwE (z : ℕ → FK) (y : ℕ) : E2 := kG (z y)

/-- `z̃` at `E2` on the `2^|pt|` words (`r_y`: 21 coordinates; the range never a literal). -/
def mleYE (pt : List E2) (f : ℕ → E2) : E2 := ∑ y ∈ range (2 ^ pt.length), eqAtF pt y * f y

theorem kG_ofBF64 (b : K) : kG (FK.ofBF64 b) = algebraMap K E2 b := by
  rw [kG, Lvm.FE2.toE2_ofK, FK.toBF64_ofBF64]; rfl

theorem kG_zero : kG 0 = 0 := by
  rw [kG, Lvm.FE2.toE2_ofK, FK.toBF64_zero, Lvm.Quad.C_eq_algebraMap, map_zero]

theorem kG_one : kG 1 = 1 := by
  rw [kG, Lvm.FE2.toE2_ofK, FK.toBF64_one, Lvm.Quad.C_eq_algebraMap, map_one]

/-! ## The claims at `E2` -/

/-- **A region claim holds iff the region sum of the column's words through the map is its value** (the map
inside the column). -/
theorem holds_regClaimE (Ti : TInst6) (μ : ℕ) (s : YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) (q : Column μ)
    (hw : ∀ reg ∈ Ti.lay.yregs, reg.src = s → ∀ i < 2 ^ reg.log, w (reg.base + i) < 2 ^ μ) :
    ClaimE.Holds μ (regClaimE Ti s w r v) q ↔
      regSumT Ti (fun s' ↦ s' == s) (fun y ↦ algebraMap K E2 (q.values.getD (w y) 0)) r = v := by
  unfold ClaimE.Holds regClaimE
  refine Eq.congr_left ?_
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ regSumT Ti (fun s' ↦ s' == s) (fun y ↦ eqAtF (bitsF x μ) (w y)) r *
    algebraMap K E2 (q.values.getD x 0)) (2 ^ μ)]
  simp only [regSumT, regSumW_mul]
  rw [sum_regSumW]
  refine regSumW_congr Ti _ fun reg hreg hS i hi ↦ ?_
  have hwl := hw reg hreg (by simpa using hS) i hi
  rw [Finset.sum_eq_single (w (reg.base + i))]
  · rw [eqAtF_bitsF_lt hwl hwl, ite_eq_left rfl, mul_one]
  · intro u hu hne
    rw [eqAtF_bitsF_lt (Finset.mem_range.mp hu) hwl, ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hwl) h

/-- `eq_eval` at a cube point is the equality weight of its index. -/
theorem eqEvalF_bitsF : ∀ (rr : List E2) (x : ℕ), eqEvalF rr (bitsF x rr.length) = eqAtF rr x
  | [], _ => rfl
  | r :: rs, x => by
    have ih := eqEvalF_bitsF rs (x / 2)
    unfold eqEvalF at ih ⊢
    rw [List.length_cons, bitsF, List.zipWith_cons_cons, ← List.prod_eq_foldl, List.prod_cons,
      List.prod_eq_foldl, ih, eqAtF_succ]
    split_ifs
    · rw [add_comm (1 : E2) r, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [add_zero]

/-- **The relayout's point claim** (`C_rec`'s whole `⟨19, 0⟩`) holding on `C_rec` gives its value: `C_rec`'s
extension at the point. -/
theorem holds_relayPointE {μ : ℕ} (hμ : μ = relayRounds) (rr : List E2) (hrr : rr.length = relayRounds) (v : E2)
    (qr : Column μ) (h : ClaimE.Holds μ (BClaimG.point ⟨relayRounds, 0⟩ rr v).onStack qr) :
    v = ∑ w ∈ range (2 ^ μ), eqAtF rr w * algebraMap K E2 (qr.values.getD w 0) := by
  subst hμ
  unfold ClaimE.Holds BClaimG.onStack BClaimG.point at h
  dsimp only at h
  rw [← h, Fin.sum_univ_eq_sum_range (fun x ↦ eqAboveG ⟨relayRounds, 0⟩ (bitsF x relayRounds) *
    eqEvalF rr ((bitsF x relayRounds).take relayRounds) * algebraMap K E2 (qr.values.getD x 0)) (2 ^ relayRounds)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have ha : eqAboveG ⟨relayRounds, 0⟩ (bitsF x relayRounds : List E2) = 1 := by
    simp [eqAboveG, selPtF, eqEvalF]
  have he : eqEvalF rr (bitsF x relayRounds) = eqAtF rr x := by rw [← eqEvalF_bitsF rr x, hrr]
  rw [ha, one_mul, List.take_of_length_le (by simp), he]

/-! ## The instance's facts -/

section Facts

variable (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK)

/-- **`z̃(r_y)` at `E2` is the regions' sums** (the committed, `S_flat`, `σ′`, `KS` parts and the executable
`virtE`). -/
theorem mleZ_zOfE (hTi : Ti.Ok) (qm : Column L.nuMain) (qr : Column L.nuRec) {ry : List E2}
    (hry : ry.length = yVars) :
    mleYE ry (zwE (Ti.zOf L pw qm qr)) =
      regSumT Ti (· == .com) (zwE (Ti.zOf L pw qm qr)) ry + regSumT Ti (· == .sflat) (zwE (Ti.zOf L pw qm qr)) ry +
        regSumT Ti (· == .sigma) (zwE (Ti.zOf L pw qm qr)) ry + regSumT Ti (· == .ks) (zwE (Ti.zOf L pw qm qr)) ry +
          virtE Ti pw ry := by
  obtain ⟨hP, hfit⟩ := yregs_pairwise Ti hTi
  rw [mleYE, hry]
  rw [sum_regionsW (2 ^ yVars) _ hP hfit (fun y ↦ eqAtF ry y * zwE (Ti.zOf L pw qm qr) y) (fun y hy ↦ by
    simp only [zwE, TInst6.zOf, src?_eq, ysrcL_none hy, kG_zero, mul_zero])]
  rw [← regSumW_sources Ti fun y ↦ eqAtF ry y * zwE (Ti.zOf L pw qm qr) y]
  have hc : ∀ (s : YSrc) (f : ℕ → E2), (∀ y, Ti.src? y = some s → f y = zwE (Ti.zOf L pw qm qr) y) →
      regSumT Ti (· == s) f ry = regSumW Ti (· == s) (fun y ↦ eqAtF ry y * zwE (Ti.zOf L pw qm qr) y) :=
    fun s f hf ↦ regSumW_congr Ti (· == s) fun reg hreg hS i hi ↦ by
      rw [hf _ (by rw [src?_mem Ti hTi hreg hi]; simpa using hS)]
  have hv : virtE Ti pw ry =
      regSumW Ti (· == .pub) (fun y ↦ eqAtF ry y * zwE (Ti.zOf L pw qm qr) y) +
        regSumW Ti (· == .qlt) (fun y ↦ eqAtF ry y * zwE (Ti.zOf L pw qm qr) y) +
          regSumW Ti (· == .one) (fun y ↦ eqAtF ry y * zwE (Ti.zOf L pw qm qr) y) := by
    unfold virtE
    rw [hc .pub _ fun y hy ↦ by simp only [zwE, TInst6.zOf, hy],
      hc .qlt _ fun y hy ↦ by simp only [zwE, TInst6.zOf, hy],
      hc .one _ fun y hy ↦ by simp only [zwE, TInst6.zOf, hy, kG_one]]
  rw [hv]
  rfl

/-- **A region claim holds iff the region's true value is its value**, when the candidate's words on the source's
regions are the column's words through the map, inside the column. -/
theorem holds_regTrueE (hTi : Ti.Ok) {μ : ℕ} (s : YSrc) (w : ℕ → ℕ) (q : Column μ) (z : ℕ → FK) (ry : List E2)
    (v : E2) (hz : ∀ y, Ti.src? y = some s → w y < 2 ^ μ ∧ zwE z y = algebraMap K E2 (q.values.getD (w y) 0)) :
    ClaimE.Holds μ (regClaimE Ti s w ry v) q ↔ regSumT Ti (· == s) (zwE z) ry = v := by
  have hm : ∀ reg ∈ Ti.lay.yregs, reg.src = s → ∀ i < 2 ^ reg.log, Ti.src? (reg.base + i) = some s :=
    fun reg hreg hS i hi ↦ by rw [src?_mem Ti hTi hreg hi, hS]
  rw [holds_regClaimE Ti μ s w ry v q fun reg hreg hS i hi ↦ (hz _ (hm reg hreg hS i hi)).1]
  refine Eq.congr_left (regSumW_congr Ti _ fun reg hreg hS i hi ↦ ?_)
  rw [(hz _ (hm reg hreg (by simpa using hS) i hi)).2]

/-- The committed block's claim. -/
theorem holds_comE (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E2) (v : E2) :
    ClaimE.Holds L.nuMain (regClaimE Ti .com Ti.comW ry v) qm ↔
      regSumT Ti (· == .com) (zwE (Ti.zOf L pw qm qr)) ry = v :=
  holds_regTrueE Ti hTi .com Ti.comW qm _ ry v fun y hy ↦ by
    have hb : Ti.comW y < 2 ^ L.nuMain := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwE, TInst6.zOf, hy, comCell_of_lt L qm qr false (by simpa using hb)]
    exact kG_ofBF64 _

/-- The `KS` aliases' claim. -/
theorem holds_ksE (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E2) (v : E2) :
    ClaimE.Holds L.nuMain (regClaimE Ti .ks Ti.ksW ry v) qm ↔
      regSumT Ti (· == .ks) (zwE (Ti.zOf L pw qm qr)) ry = v :=
  holds_regTrueE Ti hTi .ks Ti.ksW qm _ ry v fun y hy ↦ by
    have hb : Ti.ksW y < 2 ^ L.nuMain := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwE, TInst6.zOf, hy, comCell_of_lt L qm qr false (by simpa using hb)]
    exact kG_ofBF64 _

/-- `σ′`'s claim. -/
theorem holds_sigmaE (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E2) (v : E2) :
    ClaimE.Holds L.nuRec (regClaimE Ti .sigma Ti.sigmaW ry v) qr ↔
      regSumT Ti (· == .sigma) (zwE (Ti.zOf L pw qm qr)) ry = v :=
  holds_regTrueE Ti hTi .sigma Ti.sigmaW qr _ ry v fun y hy ↦ by
    have hb : Ti.sigmaW y < 2 ^ L.nuRec := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwE, TInst6.zOf, hy, comCell_of_lt L qm qr true (by simpa using hb)]
    exact kG_ofBF64 _

end Facts

/-! ## The relayout's family at `E2` -/

/-- A column's words at `E2`. -/
def recE {μ : ℕ} (q : Column μ) (w : ℕ) : E2 := algebraMap K E2 (q.values.getD w 0)

/-- **The relayout's summand at `E2`**: the kernel times the column's extension. -/
def relayGE (Ti : TInst6) (ry : List E2) (n : ℕ) (col : ℕ → E2) (pt : List E2) : E2 :=
  relayKernE Ti ry pt * ∑ w ∈ range (2 ^ n), eqAtF pt w * col w

/-- The relayout's summand has degree 2 in each coordinate. -/
theorem polyLEF_relayGE (Ti : TInst6) (ry : List E2) (n : ℕ) (col : ℕ → E2) (pre post : List E2) :
    PolyLEF 2 fun x ↦ relayGE Ti ry n col (pre ++ x :: post) := by
  have hk : PolyLEF 1 fun x ↦ relayKernE Ti ry (pre ++ x :: post) := by
    unfold relayKernE regSumT regSumW
    refine polyLEF_listSumE 1 _ _ fun reg _ ↦ ?_
    split_ifs
    · exact polyLEF_listSumE 1 _ _ fun i _ ↦ PolyLEF.const_mul (polyLEF_eqAtF pre post _) _
    · exact PolyLEF.const 1 0
  exact PolyLEF.mul hk (polyLEF_mle pre post (2 ^ n) col)

/-- **The relayout's claim is `S_flat`'s true region sum** (the map inside `C_rec`). -/
theorem relay_trueE (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (hTi : Ti.Ok) (hmaps : Ti.MapsFit L)
    (qm : Column L.nuMain) (qr : Column L.nuRec) (ry : List E2) :
    tCubeSumF L.nuRec (relayGE Ti ry L.nuRec (recE qr)) [] =
      regSumT Ti (· == .sflat) (zwE (Ti.zOf L pw qm qr)) ry := by
  have hb : ∀ y, Ti.src? y = some .sflat → Ti.sflatW y < 2 ^ L.nuRec := fun y hy ↦ by
    have := hmaps y; simp only [hy] at this; exact this
  rw [tCubeSumF_nil]
  unfold relayGE
  rw [Finset.sum_congr rfl fun u hu ↦ by
    rw [sum_eqAtF_bitsF (Finset.mem_range.mp hu), relayKernE, regSumT, regSumW_mul]]
  rw [sum_regSumW]
  refine regSumW_congr Ti _ fun reg hreg hS i hi ↦ ?_
  have hy : Ti.src? (reg.base + i) = some .sflat := by rw [src?_mem Ti hTi hreg hi]; simpa using hS
  have hw := hb _ hy
  rw [Finset.sum_eq_single (Ti.sflatW (reg.base + i))]
  · rw [eqAtF_bitsF_lt hw hw, ite_eq_left rfl, mul_one]
    simp only [zwE, TInst6.zOf, hy, comCell_of_lt L qm qr true (by simpa using hw), ite_true]
    rw [kG_ofBF64]; rfl
  · intro u hu hne
    rw [eqAtF_bitsF_lt (Finset.mem_range.mp hu) hw, ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hw) h

end Lvm6.Ty
end -- part Lvm6TyRegion

/-! ### Part `Lvm6TyAcc` (was its own module) -/
section

/-!
# A23 at `E2` (`accProgE`, lvm6)

`accProgE` samples `κ ∈ E2^2` (`e2Samples gKappa 2`, one nonce each), reads the 44 coefficients of the line
polynomial `h`, samples `t` (`e2Sample gT`) and checks `h(0) = y_in`, `h(1) = y_own(κ)` and
`Φ_Q(line(a, κ ++ r_xy, t)) = h(t)`.

* `Φ_Q` as a sparse sum (`phiQE_eq_sum`): `Σ_{e ∈ entsE} e.c·eq(pt, idxE e)`; matrix `o`'s extension `matMleE`
  likewise; every entry of `entsE` has `o < 4`;
* **`phiQE_fold`**: the selector split `y_own(κ) − Φ_Q(κ ++ r_xy) = Σ_{w<4} eq(κ, w)·δ_w`;
* **`lineDegE`**: `Φ_Q` on a line is a polynomial of degree `≤ 43`;
* **`accBadSpecE`**: outside `AccGoodE` the phase never returns in doom: `κ` by the zero test (`errG gKappa 1`
  each), `t` by a wrong line polynomial (`errG gT 43`), the reads keep doom;
* **`accSpecQE`**: from `¬AccGoodE ∨ M` to `M` (`Spec.orStable`).
-/

set_option autoImplicit false

namespace Lvm6.Ty

open Lvm (FE2 FK)
open Lvm.Loop Lvm.Typed Lvm.E2V Lvm.Acc LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Polynomial Finset
open scoped ENNReal

/-! ## The line and the line polynomial -/

theorem lineE_zero : ∀ (a b : List E2), a.length = b.length → lineE a b 0 = a
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | x :: a, v :: b, h => by
    have ih := lineE_zero a b (by simpa using h)
    simp only [lineE, List.zipWith_cons_cons, zero_mul, add_zero] at ih ⊢
    rw [ih]

theorem lineE_one : ∀ (a b : List E2), a.length = b.length → lineE a b 1 = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, v :: b, h => by
    have ih := lineE_one a b (by simpa using h)
    simp only [lineE, List.zipWith_cons_cons, one_mul] at ih ⊢
    rw [ih, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem hEvalE_cons (c : E2) (hs : List E2) (t : E2) : hEvalE (c :: hs) t = c + t * hEvalE hs t := rfl

/-- The polynomial of a coefficient list. -/
noncomputable def hPolyE (hs : List E2) : E2[X] := hs.foldr (fun c acc ↦ C c + X * acc) 0

theorem eval_hPolyE (hs : List E2) (t : E2) : (hPolyE hs).eval t = hEvalE hs t := by
  induction hs with
  | nil => simp [hPolyE, hEvalE]
  | cons c hs ih =>
    simp only [hPolyE, List.foldr_cons, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X] at ih ⊢
    rw [ih]; rfl

theorem natDegree_hPolyE : ∀ (hs : List E2) (n : ℕ), hs.length ≤ n + 1 → (hPolyE hs).natDegree ≤ n
  | [], _, _ => by simp [hPolyE]
  | c :: hs, n, h => by
    simp only [hPolyE, List.foldr_cons]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    rcases hs with _ | ⟨c', hs'⟩
    · simp
    · have hn : 1 ≤ n := by simp at h; (clear * - n hs' h; omega)
      refine (natDegree_mul_le).trans ?_
      have := natDegree_hPolyE (c' :: hs') (n - 1) (by simp at h ⊢; (clear * - hs' n hn h; omega))
      have hX : (X : E2[X]).natDegree ≤ 1 := natDegree_X_le
      simp only [hPolyE] at this
      (clear * - c' hs' n c hn this hX; omega)

/-- `eq(line(t), w)` as a polynomial in `t`. -/
noncomputable def eqPolyE : List E2 → List E2 → ℕ → E2[X]
  | x :: a, v :: b, w =>
    (if w % 2 = 1 then C x + X * C (x + v) else 1 + (C x + X * C (x + v))) * eqPolyE a b (w / 2)
  | _, _, _ => 1

theorem eval_eqPolyE : ∀ (a b : List E2) (w : ℕ) (t : E2),
    (eqPolyE a b w).eval t = eqAtF (lineE a b t) w
  | [], _, _, _ => by simp [eqPolyE, lineE]
  | _ :: _, [], _, _ => by simp [eqPolyE, lineE]
  | x :: a, v :: b, w, t => by
    simp only [eqPolyE, lineE, List.zipWith_cons_cons, eval_mul, eqAtF_succ]
    rw [← lineE, ← eval_eqPolyE a b (w / 2) t]
    split_ifs <;> simp

theorem natDegree_eqPolyE : ∀ (a b : List E2) (w : ℕ), (eqPolyE a b w).natDegree ≤ a.length
  | [], _, _ => by simp [eqPolyE]
  | _ :: _, [], _ => by simp [eqPolyE]
  | x :: a, v :: b, w => by
    simp only [eqPolyE, List.length_cons]
    have ha := natDegree_eqPolyE a b (w / 2)
    have hl : (C x + X * C (x + v) : E2[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_mul_le).trans (by
        have := natDegree_X_le (R := E2); simp only [natDegree_C]; (clear * - this; omega))))
    split_ifs
    · exact (natDegree_mul_le).trans (by (clear * - x v a b w ha hl; omega))
    · refine (natDegree_mul_le).trans ?_
      have : (1 + (C x + X * C (x + v)) : E2[X]).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) hl)
      (clear * - x v a b w ha this; omega)

/-- **The line-degree lemma**: on the line from `a` to `b`, a sparse sum `Σ_{(n, c)} c·eq(·, n)` is a polynomial
of degree at most `|a|` in `t`. -/
theorem lineDeg_sparseE (es : List (ℕ × E2)) (a b : List E2) :
    ∃ g : E2[X], g.natDegree ≤ a.length ∧
      ∀ t, g.eval t = (es.map fun p ↦ p.2 * eqAtF (lineE a b t) p.1).sum := by
  induction es with
  | nil => exact ⟨0, by simp, fun t ↦ by simp⟩
  | cons p es ih =>
    obtain ⟨g, hg, hgv⟩ := ih
    refine ⟨C p.2 * eqPolyE a b p.1 + g, ?_, fun t ↦ ?_⟩
    · exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_C_mul_le _ _).trans (natDegree_eqPolyE a b p.1)) hg)
    · rw [eval_add, eval_mul, eval_C, eval_eqPolyE, hgv, List.map_cons, List.sum_cons]

/-! ## `Φ_Q` and the matrices as sums -/

theorem toE2_ofE2E (y : E2) : FE2.toE2 (ofE2 y) = y := rfl

/-- The executable equality weight read over `E2`. -/
theorem toE2_eqWE : ∀ (l : List E2) (w : ℕ), FE2.toE2 (eqWT (l.map ofE2) w) = eqAtF l w
  | [], _ => by simp [eqWT, eqAtF]
  | r :: l, w => by
    simp only [List.map_cons, eqWT, eqAtF_succ, FE2.fe2_mul_eq, toE2_eqWE l]
    split_ifs
    · rw [toE2_ofE2E]
    · rw [FE2.toE2_add, FE2.toE2_one, toE2_ofE2E]

/-- A fold of a sum, read over `E2`, is the sum of the read terms. -/
theorem toE2_foldrE {α : Type} (l : List α) (g : α → FE2) :
    FE2.toE2 (l.foldr (fun e acc ↦ g e + acc) 0) = (l.map fun e ↦ FE2.toE2 (g e)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => rw [List.foldr_cons, FE2.toE2_add, ih, List.map_cons, List.sum_cons]

/-- **`Φ_Q` at `E2` is the sparse multilinear sum** of the four matrices' entries. -/
theorem phiQE_eq_sum (Q : Program) (lay : Lay) (pt : List E2) :
    PhiQE Q lay pt = ((entsE Q lay).map fun e ↦ FE2.toE2 e.c * eqAtF pt (EntT.idxE e)).sum := by
  unfold PhiQE PhiQFE
  rw [toE2_foldrE]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE2.fe2_mul_eq, toE2_eqWE])

/-- **Matrix `o`'s extension at `E2`** (`o < 4`) at `rxy = r_x ++ r_y`: its entries' sum. -/
def matMleE (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E2) : E2 :=
  (((entsE Q lay).filter fun e ↦ e.o == o).map fun e ↦ FE2.toE2 e.c * eqAtF rxy (e.x + 2 ^ xVars * e.y)).sum

/-- Every entry of `entsE` is one of the four matrices'. -/
theorem entsE_o (Q : Program) (lay : Lay) : ∀ e ∈ entsE Q lay, e.o < 4 := fun e he ↦ by
  have := (List.mem_filter.mp he).2
  simpa using this

/-- A selector-weighted sum of the per-matrix sums is the weighted sum over all entries (every `o < 4`). -/
theorem sum_sel_filterE (g : ℕ → E2) (f : EntT → E2) :
    ∀ l : List EntT, (∀ e ∈ l, e.o < 4) →
      ∑ w ∈ range (2 ^ selBitsE), g w * ((l.filter fun e ↦ e.o == w).map f).sum =
        (l.map fun e ↦ g e.o * f e).sum
  | [], _ => by simp
  | e :: l, hl => by
    have ih := sum_sel_filterE g f l fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have he : e.o < 2 ^ selBitsE := hl e (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih]
    rw [Finset.sum_congr rfl fun w _ ↦ show g w * ((((e :: l).filter fun e ↦ e.o == w)).map f).sum =
        (if e.o = w then g e.o * f e else 0) + g w * ((l.filter fun e ↦ e.o == w).map f).sum by
      by_cases h : e.o = w
      · subst h; simp [mul_add]
      · simp [h]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr he)]

/-! ## The instance -/

/-- **The matrices' errors** (`o < 4`). -/
def deltaE (Q : Program) (lay : Lay) (vs rxy : List E2) (o : ℕ) : E2 := vs.getD o 0 - matMleE Q lay o rxy

/-- **Nothing to fold away**: the incoming claim is true (`Φ_Q(a) = y_in`) and every matrix value is (`δ = 0`). -/
def AccGoodE (yIn : E2) (a : List E2) (Q : Program) (lay : Lay) (vs rxy : List E2) : Prop :=
  PhiQE Q lay a = yIn ∧ ∀ w < 2 ^ selBitsE, deltaE Q lay vs rxy w = 0

/-- `y_own(κ)` as the selector-weighted sum of the four values. -/
theorem yOwnE_eq (vs κ : List E2) (hvs : vs.length = 4) (hκ : κ.length = selBitsE) :
    yOwnE vs κ = ∑ w ∈ range (2 ^ selBitsE), eqAtF κ w * vs.getD w 0 := by
  have hn : vs.length ≤ 2 ^ κ.length := by rw [hvs, hκ]; norm_num
  have hk : (eqKernelF κ).take vs.length = eqKernelF κ := by
    rw [List.take_of_length_le]
    rw [eqKernelF_length, hκ, hvs]; norm_num
  unfold yOwnE
  rw [← hk, dot_eqKernelF κ vs hn, hvs]
  rfl

/-- **The selector split**: at `κ ++ r_xy`, `y_own − Φ_Q` is the selector extension of the matrices' errors. -/
theorem phiQE_fold (Q : Program) (lay : Lay) (rxy vs : List E2) (hvs : vs.length = 4) (κ : List E2)
    (hκ : κ.length = selBitsE) :
    yOwnE vs κ - PhiQE Q lay (κ ++ rxy) = ∑ w ∈ range (2 ^ selBitsE), eqAtF κ w * deltaE Q lay vs rxy w := by
  have hphi : PhiQE Q lay (κ ++ rxy) = ∑ w ∈ range (2 ^ selBitsE), eqAtF κ w * matMleE Q lay w rxy := by
    simp only [matMleE]
    rw [sum_sel_filterE (eqAtF κ) _ _ (entsE_o Q lay), phiQE_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    have ho := entsE_o Q lay e he
    rw [eqAtF_append, hκ, eqAtF_mod κ, hκ, Lvm6.Ty.EntT.idxE,
      show (e.o + 4 * (e.x + 2 ^ xVars * e.y)) % 2 ^ selBitsE = e.o by
        rw [show (2 : ℕ) ^ selBitsE = 4 from rfl]; (clear * - e ho; omega),
      show (e.o + 4 * (e.x + 2 ^ xVars * e.y)) / 2 ^ selBitsE = e.x + 2 ^ xVars * e.y by
        rw [show (2 : ℕ) ^ selBitsE = 4 from rfl]; (clear * - e ho; omega)]
    ring
  rw [yOwnE_eq vs κ hvs hκ, hphi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [deltaE, mul_sub]

/-- **The line-degree bound at `Φ_Q`**: on the line from `a` to `b`, `Φ_Q` is a polynomial of degree at most
`43`. -/
theorem lineDegE (Q : Program) (lay : Lay) (a b : List E2) (ha : a.length = phiVarsE) :
    ∃ g : E2[X], g.natDegree ≤ phiVarsE ∧ ∀ t, g.eval t = PhiQE Q lay (lineE a b t) := by
  obtain ⟨g, hg, hgv⟩ := lineDeg_sparseE ((entsE Q lay).map fun e ↦ (EntT.idxE e, FE2.toE2 e.c)) a b
  refine ⟨g, ha ▸ hg, fun t ↦ ?_⟩
  rw [hgv, phiQE_eq_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ rfl)

theorem length_bOfE (κ rxy : List E2) (a : List E2) (ha : a.length = phiVarsE)
    (hr : rxy.length = xVars + yVars) (hκ : κ.length = selBitsE) : a.length = (κ ++ rxy).length := by
  rw [List.length_append, ha, hr, hκ]
  rfl

/-! ## Outside `AccGoodE`: the phase never returns in doom -/

section Bad

variable {Q : Program} {lay : Lay} {yIn : E2} {a rxy vs : List E2} {εmax T : ℝ≥0∞}

/-- The checks at `t`. -/
def PassE (Q : Program) (lay : Lay) (yIn : E2) (a rxy vs κ hs : List E2) (t : E2) : Prop :=
  hEvalE hs 0 = yIn ∧ hEvalE hs 1 = yOwnE vs κ ∧ hEvalE hs t = PhiQE Q lay (lineE a (κ ++ rxy) t)

/-- The zero test's alive predicate after `κ` (its length carried inside). -/
def AliveKE (Q : Program) (lay : Lay) (yIn : E2) (a rxy vs κ : List E2) (_ : Unit) : Prop :=
  κ.length = selBitsE → ZeroOnF (deltaE Q lay vs rxy) κ selBitsE ∧ PhiQE Q lay a = yIn

/-- `AliveKE` after `h` (its length carried inside). -/
def AliveHE (Q : Program) (lay : Lay) (yIn : E2) (a rxy vs κ hs : List E2) (q : Unit) : Prop :=
  hs.length = phiVarsE + 1 → AliveKE Q lay yIn a rxy vs κ q

/-- **The escape at `t`**: a wrong line polynomial agrees with `Φ_Q ∘ line` at an accepted challenge with
probability `≤ errG gT 43`. -/
theorem escape_tE (ha : a.length = phiVarsE) (hr : rxy.length = xVars + yVars) (hvs : vs.length = 4)
    (κ hs : List E2) (q : Unit) (hq : ¬ AliveHE Q lay yIn a rxy vs κ hs q) :
    avgE (fun c ↦ indE (powOK gT c ∧ PassE Q lay yIn a rxy vs κ hs (e2OfE c))) ≤ errG gT phiVarsE := by
  unfold AliveHE AliveKE at hq
  have hhs : hs.length = phiVarsE + 1 := not_imp.mp hq |>.1
  have hκ : κ.length = selBitsE := not_imp.mp (not_imp.mp hq).2 |>.1
  have hd := not_imp.mp (not_imp.mp hq).2 |>.2
  by_cases hp : hEvalE hs 0 = yIn ∧ hEvalE hs 1 = yOwnE vs κ
  · obtain ⟨g, hg, hgv⟩ := lineDegE Q lay a (κ ++ rxy) ha
    have hlen := length_bOfE κ rxy a ha hr hκ
    have hne : hPolyE hs ≠ g := by
      intro he
      have e0 := hgv 0
      have e1 := hgv 1
      rw [← he, eval_hPolyE, lineE_zero _ _ hlen] at e0
      rw [← he, eval_hPolyE, lineE_one _ _ hlen] at e1
      refine hd ⟨(zeroOnF_full _ hκ).mpr ?_, by rw [← e0, hp.1]⟩
      rw [← phiQE_fold Q lay rxy vs hvs κ hκ, ← e1, hp.2, sub_self]
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
      (sampleG_escape (by norm_num) hne (natDegree_hPolyE hs phiVarsE hhs.le) hg)
    rw [eval_hPolyE, hgv]
    exact hc.2.2.2
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ ?_).trans
      ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
    exact hp ⟨hc.2.1, hc.2.2.1⟩

/-- **Outside `AccGoodE` the phase never returns in doom**: each `κ_j` escapes with `errG gKappa 1` (lead `0`:
every sample follows its nonce), `t` with `errG gT 43` (its follower `T`), the reads keep doom, the checks reject. -/
noncomputable def accBadSpecE (ha : a.length = phiVarsE) (hr : rxy.length = xVars + yVars)
    (hvs : vs.length = 4) (hκ : errG gKappa 1 ≤ εmax) (ht : errG gT phiVarsE + T ≤ εmax) :
    Spec (accProgE Q lay yIn a rxy vs) (fun _ ↦ ¬ AccGoodE yIn a Q lay vs rxy) (fun _ _ ↦ False)
      εmax 0 T :=
  ((zeroSpecE2 (C := unitC) (L₀ := 1) (T := 0) (εmax := εmax) stable_unitC ncard_unitC (g := gKappa)
      (by norm_num) (fun _ ↦ deltaE Q lay vs rxy) (fun _ ↦ PhiQE Q lay a = yIn)
      (n := selBitsE) (m := 1) le_rfl (by rw [Nat.cast_one, one_mul, add_zero]; exact hκ)).bind' fun κ ↦
    ((e2ReadsSpec (T := 0) (εmax := εmax) stable_unitC (AliveKE Q lay yIn a rxy vs κ) zero_le
        phiVarsE).mono
      (fun _ ⟨hl, hd⟩ ↦ Doomed.mono hd fun _ hk ↦ hk hl) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun hs ↦
      ((doomE2SampleSpec (T := T) (εmax := εmax) stable_unitC ncard_unitC (g := gT)
          (AliveHE Q lay yIn a rxy vs κ hs) (fun t _ ↦ PassE Q lay yIn a rxy vs κ hs t)
          (errG gT phiVarsE) (escape_tE ha hr hvs κ hs)
          (by rw [Nat.cast_one, one_mul]; exact ht)).mono
        (fun _ ⟨hl, hd⟩ ↦ Doomed.mono hd fun _ hk ↦ hk hl) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
        fun t ↦
          Spec.require (Pre := Doomed unitC fun _ ↦ PassE Q lay yIn a rxy vs κ hs t)
            (Post := fun _ _ ↦ False)
            fun _ hd hc ↦ doomed_unitC.mp hd ⟨hc.1, hc.2.1, hc.2.2.symm⟩).mono
    (fun _ hg ↦ by
      rw [doomed_unitC]
      rintro ⟨hz, hΦ⟩
      exact hg ⟨hΦ, (zeroOnF_nil _ _).mp hz⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Bad

/-! ## The phase's specification -/

/-- **A23's specification at `E2`**: from `¬AccGoodE ∨ M` to `M`, for a predicate `M` of the history the phase
keeps. Escape `errG gKappa 1` per `κ_j`, `errG gT 43` at `t` (follower `0`); lead `0`. -/
noncomputable def accSpecQE (Q : Program) (lay : Lay) {yIn : E2} (a rxy vs : List E2) (ha : a.length = phiVarsE)
    (hr : rxy.length = xVars + yVars) (hvs : vs.length = 4)
    (M : List Ev → Prop) (hM : ∀ h₀ l, (accProgE Q lay yIn a rxy vs).Reach h₀ l → M h₀ → M (h₀ ++ l))
    {εmax : ℝ≥0∞} (hκ : errG gKappa 1 ≤ εmax) (ht : errG gT phiVarsE ≤ εmax) :
    Spec (accProgE Q lay yIn a rxy vs) (fun h ↦ ¬ AccGoodE yIn a Q lay vs rxy ∨ M h)
      (fun _ h ↦ M h) εmax 0 0 :=
  ((accBadSpecE (T := 0) ha hr hvs hκ (by rw [add_zero]; exact ht)).orStable hM zero_le).mono (fun _ h ↦ h)
    (fun _ _ h ↦ h) le_rfl (max_le zero_le le_rfl) le_rfl

end Lvm6.Ty
end -- part Lvm6TyAcc

/-! ### Part `Lvm6TyWire` (was its own module) -/
section

/-!
# The wiring and the relayout at `E2` (lvm6)

* **The entry form** (`colE_sum`, `vals3_batch`): `wBatchE γ (vals3 r_x) = Σ_{e ∈ entsE} γ^{kE(e.o)}·eq(r_x, x_e)·c_e·z(y_e)`,
  `kE` the value index of matrix `o` (`A ↦ 0`, `B ↦ 1`, `D, W ↦ 2`).
* **The family** (`wireGE`): `wireME γ r_x pt · z̃(pt)`, degree 2 in each of `y`'s coordinates; its cube sum is the
  batch (`wire_nilE`).
* **`γ`'s escape** (`gamma_escapeE`): two different triples batched by `γ` agree at a root of a nonzero polynomial
  of degree `≤ 2`.
* **`wireSpecE`**: from doom of "the three values are true" to doom of "the four matrix values and the region
  values are true"; **`relaySpecE`**: from the region values to `C_rec`'s extension at the relayout's point.
-/

set_option autoImplicit false

namespace Lvm6.Ty

open Lvm (FE2 FK)
open Lvm.Loop Lvm.Typed Lvm.E2V Lvm.E2T LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Polynomial Finset
open scoped ENNReal

/-! ## The entries at `E2` -/

/-- **Every entry of `entsE` lies on the cube** (a checked layout): `o < 4`, `x < 2^20`, `y < 2^21`. -/
theorem entsE_fit (Q : Program) (lay : Lay) (hlay : lay.Ok Q) :
    ∀ e ∈ entsE Q lay, e.o < 4 ∧ e.x < 2 ^ xVars ∧ e.y < 2 ^ yVars := fun e he ↦
  ⟨entsE_o Q lay e he, (entsT_fit Q lay hlay e (List.mem_filter.mp he).1).2⟩

/-- The value index of matrix `o`: `A ↦ 0`, `B ↦ 1`, `D, W ↦ 2`. -/
def kE (o : ℕ) : ℕ := if o = 0 then 0 else if o = 1 then 1 else 2

/-- Matrix `o` contributes to value `k`. -/
def inOE (k o : ℕ) : Prop := (k = 0 ∧ o = 0) ∨ (k = 1 ∧ o = 1) ∨ (k = 2 ∧ (o = 2 ∨ o = 3))

instance (k o : ℕ) : Decidable (inOE k o) := by unfold inOE; infer_instance

theorem sum_inOE (γ : E2) {o : ℕ} (ho : o < 4) :
    ∑ k ∈ range 3, (if inOE k o then γ ^ k else 0) = γ ^ kE o := by
  interval_cases o <;> simp [inOE, kE]

/-- `toE2` of a filtered fold is the indicator sum. -/
theorem toE2_foldr_filterE (l : List EntT) (p : EntT → Bool) (g : EntT → FE2) :
    FE2.toE2 ((l.filter p).foldr (fun e acc ↦ g e + acc) 0) =
      (l.map fun e ↦ if p e then FE2.toE2 (g e) else 0).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    by_cases hp : p e
    · simp [hp, FE2.toE2_add, ih]
    · simp [hp, ih]

/-- A sum over a filtered list is the sum over the list when the dropped terms vanish. -/
theorem sum_map_filter_of {α : Type} (l : List α) (p : α → Bool) (F : α → E2)
    (h : ∀ e ∈ l, p e = false → F e = 0) : ((l.filter p).map F).sum = (l.map F).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun e he ↦ h e (List.mem_cons_of_mem _ he)
    by_cases hp : p a
    · simp [hp, ih']
    · simp [hp, ih', h a List.mem_cons_self (by simpa using hp)]

/-- **A matrix (`o < 4`) at a slot as an entry sum over `entsE`.** -/
theorem toE2_matZT (Q : Program) (lay : Lay) (z : ℕ → FK) {o : ℕ} (ho : o < 4) (x : ℕ) :
    FE2.toE2 (matZT Q lay o z x) = ((entsE Q lay).map fun e ↦
      if e.o = o ∧ e.x = x then FE2.toE2 e.c * zwE z e.y else 0).sum := by
  unfold matZT
  rw [toE2_foldr_filterE, entsE, sum_map_filter_of _ _ _ fun e _ he ↦ by
    have : ¬ e.o < 4 := by simpa using he
    rw [ite_eq_right (by omega)]]
  refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
  simp only [Bool.and_eq_true, beq_iff_eq, FE2.fe2_mul_eq, zwE, Lvm6.Mb.kG]

/-- **A column at a slot as an entry sum.** -/
theorem colE_sum (Q : Program) (lay : Lay) (z : ℕ → FK) {k : ℕ} (hk : k < 3) (x : ℕ) :
    colE Q lay z k x = ((entsE Q lay).map fun e ↦
      if inOE k e.o ∧ e.x = x then FE2.toE2 e.c * zwE z e.y else 0).sum := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [colE, ite_eq_left rfl, toE2_matZT Q lay z (by norm_num)]
    exact congrArg List.sum (List.map_congr_left fun e _ ↦ by simp [inOE])
  · rw [colE, ite_eq_right (by norm_num), ite_eq_left rfl, toE2_matZT Q lay z (by norm_num)]
    exact congrArg List.sum (List.map_congr_left fun e _ ↦ by simp [inOE])
  · rw [colE, ite_eq_right (by norm_num), ite_eq_right (by norm_num), FE2.toE2_add, toE2_matZT Q lay z (by norm_num),
      toE2_matZT Q lay z (by norm_num), ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun e _ ↦ ?_)
    by_cases h2 : e.o = 2
    · simp [inOE, h2]
    · by_cases h3 : e.o = 3
      · simp [inOE, h3]
      · simp [inOE, h2, h3]

/-- **Collapsing a slot sum**: a weighted sum over the slots of per-slot entry sums is the entry sum. -/
theorem sum_slot_collapseE (l : List EntT) (N : ℕ) (hl : ∀ e ∈ l, e.x < N) (P : EntT → Prop) [DecidablePred P]
    (w : ℕ → E2) (f : EntT → E2) :
    ∑ x ∈ range N, w x * (l.map fun e ↦ if P e ∧ e.x = x then f e else 0).sum =
      (l.map fun e ↦ if P e then w e.x * f e else 0).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := hl e (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib,
      ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')]
    congr 1
    by_cases hP : P e
    · simp only [hP, true_and, ite_true]
      rw [Finset.sum_eq_single e.x (fun b _ hb ↦ by rw [ite_eq_right (Ne.symm hb), mul_zero])
        (fun h ↦ absurd (Finset.mem_range.mpr he) h), ite_eq_left rfl]
    · simp [hP]

/-- **A column's extension at `r_x` as an entry sum** (the entries' slots are on the cube). -/
theorem mleXE_colE (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) {k : ℕ} (hk : k < 3)
    {rx : List E2} (hrx : rx.length = xVars) :
    mleXE rx (colE Q lay z k) = ((entsE Q lay).map fun e ↦
      if inOE k e.o then eqAtF rx e.x * (FE2.toE2 e.c * zwE z e.y) else 0).sum := by
  have hb : ∀ e ∈ entsE Q lay, e.x < 2 ^ rx.length := fun e he ↦ hrx ▸ (entsE_fit Q lay hlay e he).2.1
  rw [mleXE, ← sum_slot_collapseE _ _ hb (fun e ↦ inOE k e.o) _ _]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [colE_sum Q lay z hk x]

/-- **Collapsing the value index**: `Σ_k γ^k·(entries of value k)` is the entry sum at `γ^{kE}`. -/
theorem sum_k_collapseE (l : List EntT) (hl : ∀ e ∈ l, e.o < 4) (γ : E2) (a : EntT → E2) :
    ∑ k ∈ range 3, γ ^ k * (l.map fun e ↦ if inOE k e.o then a e else 0).sum =
      (l.map fun e ↦ γ ^ kE e.o * a e).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib,
      ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')]
    congr 1
    rw [← sum_inOE γ (hl e (List.mem_cons_self ..)), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> simp

/-- **Collapsing a position sum**: `Σ_{u<N} (entries at position u)` is the entry sum. -/
theorem sum_pos_collapseE {α : Type} (l : List α) (pos : α → ℕ) (N : ℕ) (hl : ∀ e ∈ l, pos e < N)
    (f : α → E2) : ∑ u ∈ range N, (l.map fun e ↦ if pos e = u then f e else 0).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib,
      ih fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (hl e (List.mem_cons_self ..)))]

theorem wBatchE_eq (γ : E2) (v : List E2) : wBatchE γ v = ∑ k ∈ range 3, γ ^ k * v.getD k 0 := by
  simp [wBatchE, Finset.sum_range_succ]

/-- **The three values batched by `γ`, as an entry sum.** -/
theorem vals3_batch (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E2) {rx : List E2}
    (hrx : rx.length = xVars) :
    wBatchE γ (vals3 Q lay z rx) = ((entsE Q lay).map fun e ↦
      γ ^ kE e.o * (eqAtF rx e.x * (FE2.toE2 e.c * zwE z e.y))).sum := by
  have hb : wBatchE γ (vals3 Q lay z rx) = ∑ k ∈ range 3, γ ^ k * mleXE rx (colE Q lay z k) := by
    simp [wBatchE, vals3, Finset.sum_range_succ]
  rw [hb, Finset.sum_congr rfl fun k hk ↦ by rw [mleXE_colE Q lay hlay z (Finset.mem_range.mp hk) hrx]]
  exact sum_k_collapseE _ (entsE_o Q lay) γ _

/-! ## The family -/

/-- **The four matrices batched by `γ`** at `(r_x, pt)`, as an entry sum. -/
def wireME (Q : Program) (lay : Lay) (γ : E2) (rx pt : List E2) : E2 :=
  ((entsE Q lay).map fun e ↦ γ ^ kE e.o * (FE2.toE2 e.c * eqAtF (rx ++ pt) (e.x + 2 ^ xVars * e.y))).sum

/-- **The wiring's summand**: the batched matrices times `z̃`. -/
def wireGE (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E2) (rx pt : List E2) : E2 :=
  wireME Q lay γ rx pt * mleYE pt (zwE z)

theorem polyLEF_wireME (Q : Program) (lay : Lay) (γ : E2) (rx pre post : List E2) :
    PolyLEF 1 fun x ↦ wireME Q lay γ rx (pre ++ x :: post) := by
  refine polyLEF_listSumE 1 _ _ fun e _ ↦ PolyLEF.const_mul (PolyLEF.const_mul ?_ _) _
  have := polyLEF_eqAtF (rx ++ pre) post (e.x + 2 ^ xVars * e.y)
  simpa only [List.append_assoc] using this

theorem polyLEF_mleYE (pre post : List E2) (f : ℕ → E2) : PolyLEF 1 fun x ↦ mleYE (pre ++ x :: post) f :=
  (polyLEF_mle pre post (2 ^ (pre.length + post.length + 1)) f).congr fun x ↦ by
    rw [mleYE, List.length_append, List.length_cons, Nat.add_assoc]

/-- **The summand has degree 2 in each of `y`'s coordinates.** -/
theorem polyLEF_wireGE (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E2) (rx pre post : List E2) :
    PolyLEF 2 fun x ↦ wireGE Q lay z γ rx (pre ++ x :: post) :=
  PolyLEF.mul (polyLEF_wireME Q lay γ rx pre post) (polyLEF_mleYE pre post (zwE z))

/-- `wire_nilE` at a symbolic number `n = yVars` of `y`'s coordinates (no literal range meets a defeq check). -/
theorem wire_nil_genE (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E2) {rx : List E2}
    (hrx : rx.length = xVars) (n : ℕ) (hn : yVars = n) :
    tCubeSumF n (wireGE Q lay z γ rx) [] = wBatchE γ (vals3 Q lay z rx) := by
  have hfit := entsE_fit Q lay hlay
  have hy : ∀ e ∈ entsE Q lay, e.y < 2 ^ n := fun e he ↦ hn ▸ (hfit e he).2.2
  rw [tCubeSumF_nil, vals3_batch Q lay hlay z γ hrx]
  have hpt : ∀ u < 2 ^ n, ∀ e ∈ entsE Q lay,
      eqAtF (rx ++ bitsF u n) (e.x + 2 ^ xVars * e.y) = eqAtF rx e.x * (if e.y = u then 1 else 0) :=
    fun u hu e he ↦ by
      have hx := (hfit e he).2.1
      rw [eqAtF_append, eqAtF_mod rx, hrx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add, eqAtF_bitsF_lt hu (hy e he)]
  have hmle : ∀ u < 2 ^ n, mleYE (bitsF u n) (zwE z) = zwE z u := fun u hu ↦ by
    rw [mleYE, bitsF_length]
    exact sum_eqAtF_bitsF hu _
  have hu : ∀ u ∈ range (2 ^ n), wireGE Q lay z γ rx (bitsF u n) =
      ((entsE Q lay).map fun e ↦ if e.y = u then
        γ ^ kE e.o * (eqAtF rx e.x * (FE2.toE2 e.c * zwE z e.y)) else 0).sum := fun u hu ↦ by
    have hu' := Finset.mem_range.mp hu
    rw [wireGE, wireME, hmle u hu', ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    rw [hpt u hu' e he]
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [Finset.sum_congr rfl hu]
  exact sum_pos_collapseE (entsE Q lay) EntT.y (2 ^ n) hy _

/-- **The wiring's start is the batch of the three true values** (`r_x` of 20 coordinates). -/
theorem wire_nilE (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E2) {rx : List E2}
    (hrx : rx.length = xVars) :
    tCubeSumF yVars (wireGE Q lay z γ rx) [] = wBatchE γ (vals3 Q lay z rx) :=
  wire_nil_genE Q lay hlay z γ hrx yVars rfl

/-! ## `γ`'s escape -/

/-- **`γ`'s escape** (degree 2): two different triples batched by an accepted `γ` agree with probability at most
`errG g 2`. -/
theorem gamma_escapeE {g : ℕ} (hg : g ≤ 64) {v w : List E2} (hv : v.length = 3) (hw : w.length = 3)
    (hne : v ≠ w) :
    avgE (fun c ↦ indE (powOK g c ∧ wBatchE (e2OfE c) v = wBatchE (e2OfE c) w)) ≤ errG g 2 := by
  set p : E2[X] := ∑ k ∈ range 3, C (v.getD k 0 - w.getD k 0) * X ^ k with hp
  obtain ⟨k, hk, hvk⟩ : ∃ k < 3, v.getD k 0 ≠ w.getD k 0 := by
    by_contra hall
    push Not at hall
    refine hne (List.ext_getElem (hv.trans hw.symm) fun i hi _ ↦ ?_)
    have := hall i (by (clear * - i g v w hv hi; omega))
    rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at this
  have hp0 : p ≠ 0 := by
    intro h
    have hc := congrArg (coeff · k) h
    simp only [hp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, coeff_zero] at hc
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hk)] at hc
    exact hvk (sub_eq_zero.mp hc)
  have hdeg : p.natDegree ≤ 2 := by
    rw [hp]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  refine (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨h.1, ?_⟩).trans (sampleG_escape hg hp0 (q := 0) hdeg (by simp))
  rw [eval_zero, hp, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have h2 := h.2
  rw [wBatchE_eq, wBatchE_eq] at h2
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
  exact (Finset.sum_congr rfl fun i _ ↦ by ring).trans h2

/-! ## The final check -/

theorem wGE_eq (γ : E2) (vs : List E2) : wGE γ vs = ∑ o ∈ range (2 ^ selBitsE), γ ^ kE o * vs.getD o 0 := by
  simp only [wGE, show (2 : ℕ) ^ selBitsE = 4 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, kE]
  norm_num
  ring

/-- **The batched matrices at `(r_x, r_y)` are the four matrix values batched** (`wGE`), when they are true. -/
theorem wireME_vs (Q : Program) (lay : Lay) (γ : E2) (rx ry vs : List E2)
    (hV : ∀ o < 4, vs.getD o 0 = matMleE Q lay o (rx ++ ry)) : wireME Q lay γ rx ry = wGE γ vs := by
  rw [wGE_eq, Finset.sum_congr rfl fun o ho ↦ by
    rw [hV o (by simpa [selBitsE] using Finset.mem_range.mp ho)]]
  simp only [matMleE]
  rw [sum_sel_filterE (fun o ↦ γ ^ kE o) _ _ (entsE_o Q lay)]
  rfl

theorem sumF_fourE (rv : List E2) (h : rv.length = 4) :
    sumF rv = rv.getD 0 0 + rv.getD 1 0 + rv.getD 2 0 + rv.getD 3 0 := by
  match rv, h with
  | [a, b, c, d], _ => simp [sumF_eq_sum, add_assoc]

/-! ## The phases -/

section Phase

variable (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (R : Column L.nuMain × Column L.nuRec → Prop)

/-- A candidate's words. -/
abbrev zE (q : Column L.nuMain × Column L.nuRec) : ℕ → FK := Ti.zOf L pw q.1 q.2

/-- The four matrix values are the matrices' extensions at `r_x ++ r_y`. -/
def VsTrueE (rxy vs : List E2) : Prop := ∀ o < 4, vs.getD o 0 = matMleE Ti.Q Ti.lay o rxy

/-- The four region values (committed, `S_flat`, `σ′`, `KS`) are true at `r_y`. -/
def RegsE (ry rv : List E2) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  rv.getD 0 0 = regSumT Ti (· == .com) (zwE (zE Ti L pw q)) ry ∧
    rv.getD 1 0 = regSumT Ti (· == .sflat) (zwE (zE Ti L pw q)) ry ∧
    rv.getD 2 0 = regSumT Ti (· == .sigma) (zwE (zE Ti L pw q)) ry ∧
    rv.getD 3 0 = regSumT Ti (· == .ks) (zwE (zE Ti L pw q)) ry

/-- The committed, `σ′` and `KS` region values are true at `r_y` (`RegsE` without `S_flat`'s, which the relayout
consumes). -/
def Regs3E (ry rv : List E2) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  rv.getD 0 0 = regSumT Ti (· == .com) (zwE (zE Ti L pw q)) ry ∧
    rv.getD 2 0 = regSumT Ti (· == .sigma) (zwE (zE Ti L pw q)) ry ∧
    rv.getD 3 0 = regSumT Ti (· == .ks) (zwE (zE Ti L pw q)) ry

variable {L₀ : ℕ} {εmax T : ℝ≥0∞} {C : List Ev → Set (Column L.nuMain × Column L.nuRec)}

/-- **The wiring at `E2`** (`γ`, 21 plain rounds, the four matrix and four region values, the final check): from
doom of "the three values are true at `r_x`" to doom of "the matrix values and the region values are true"; lead
`0`; groups `γ` (`errG gGamma 2`) and the rounds (`errG gWire 2`). -/
noncomputable def wireSpecE (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (hTi : Ti.Ok)
    (hγ : (L₀ : ℝ≥0∞) * errG gGamma 2 + 0 ≤ εmax) (hw : (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax) (hT : T ≤ εmax)
    (rx v : List E2) :
    Spec (wireProgE Ti pw v)
      (fun h ↦ rx.length = xVars ∧ v.length = 3 ∧
        Doomed C (fun q ↦ v = vals3 Ti.Q Ti.lay (zE Ti L pw q) rx ∧ R q) h)
      (fun w h ↦ w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4 ∧
        Doomed C (fun q ↦ VsTrueE Ti (rx ++ w.1) w.2.1 ∧ RegsE Ti L pw w.1 w.2.2 q ∧ R q) h) εmax 0 T := by
  exact if hz : rx.length = xVars ∧ v.length = 3 then by
    unfold wireProgE
    refine ((doomE2SampleSpec (T := 0) hst hcard (fun q ↦ v = vals3 Ti.Q Ti.lay (zE Ti L pw q) rx ∧ R q)
      (fun γ q ↦ wBatchE γ v = tCubeSumF yVars (wireGE Ti.Q Ti.lay (zE Ti L pw q) γ rx) [] ∧ R q)
      (errG gGamma 2) (fun q hq ↦ by
        by_cases hR : R q
        · have hne : v ≠ vals3 Ti.Q Ti.lay (zE Ti L pw q) rx := fun h ↦ hq ⟨h, hR⟩
          refine (avgE_mono fun c ↦ indE_mono fun h ↦ ⟨h.1, ?_⟩).trans
            (gamma_escapeE (by norm_num) hz.2 (by simp [vals3]) hne)
          rw [h.2.1, wire_nilE Ti.Q Ti.lay hTi.1 _ _ hz.1]
        · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
            ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)) hγ).mono
      (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun γ ↦ ?_
    refine (sumcheckGSpec (T := 0) hst hcard R
      (Fm := fun q acc ↦ tCubeSumF yVars (wireGE Ti.Q Ti.lay (zE Ti L pw q) γ rx) acc)
      (tCubeSumF_plainFamily yVars 2 _ fun q pre post ↦ polyLEF_wireGE _ _ _ γ rx pre post)
      (count := 3) (by norm_num) (by norm_num) (g := gWire) (by norm_num) hw yVars [] _ (by simp)).bind'
      fun rf ↦ ?_
    exact if hry : rf.1.length = yVars then
      ((e2ReadsSpec hst (fun q ↦ rf.2 = tCubeSumF yVars (wireGE Ti.Q Ti.lay (zE Ti L pw q) γ rx) ([] ++ rf.1) ∧
          R q) zero_le 3).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun vs ↦
      if hvs : vs.length = 4 then
        ((e2ReadsSpec hst (fun q ↦ rf.2 = tCubeSumF yVars (wireGE Ti.Q Ti.lay (zE Ti L pw q) γ rx) ([] ++ rf.1) ∧
            R q) hT 3).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun rv ↦
        if hrv : rv.length = 4 then
          (Spec.require (Pre := fun h ↦ rv.length = 3 + 1 ∧ Doomed C (fun q ↦
              rf.2 = tCubeSumF yVars (wireGE Ti.Q Ti.lay (zE Ti L pw q) γ rx) ([] ++ rf.1) ∧ R q) h)
            (Post := fun _ h ↦ Doomed C (fun q ↦ VsTrueE Ti (rx ++ rf.1) vs ∧ RegsE Ti L pw rf.1 rv q ∧ R q) h)
            fun _ hp hc ↦ Doomed.mono hp.2 fun q ⟨hV, ⟨h0, h1, h2, h3⟩, hR⟩ ↦ ⟨by
              rw [List.nil_append, tCubeSumF_full _ _ hry, wireGE, wireME_vs Ti.Q Ti.lay γ rx rf.1 vs hV,
                mleZ_zOfE Ti L pw hTi q.1 q.2 hry, hc, sumF_fourE rv hrv, h0, h1, h2, h3], hR⟩).bind' fun _ ↦
            (Spec.ret (Post := fun w h ↦ w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4 ∧
                Doomed C (fun q ↦ VsTrueE Ti (rx ++ w.1) w.2.1 ∧ RegsE Ti L pw w.1 w.2.2 q ∧ R q) h)
              (rf.1, vs, rv)).mono (fun _ hp ↦ ⟨hry, hvs, hrv, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hp ↦ hrv hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
      else Spec.dead.mono (fun _ hp ↦ hvs hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ hp ↦ hry hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hz ⟨hp.1, hp.2.1⟩) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **The relayout at `E2`** (19 plain rounds, `v_R`, the final check): from doom of the region values at `r_y` to
doom of `C_rec`'s extension at the point with the other three region values, the rest carried; lead `0`, follower
`Tf`. -/
noncomputable def relaySpecE (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (hTi : Ti.Ok) (hmaps : Ti.MapsFit L)
    (hrec : L.nuRec = relayRounds) (hw : (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax) {Tf : ℝ≥0∞} (hTf : Tf ≤ εmax)
    (A : Column L.nuMain × Column L.nuRec → Prop) (ry rv : List E2) :
    Spec (relayProgE Ti ry (rv.getD 1 0))
      (Doomed C (fun q ↦ RegsE Ti L pw ry rv q ∧ A q))
      (fun r h ↦ r.1.length = relayRounds ∧ Doomed C (fun q ↦
        r.2 = (∑ w ∈ range (2 ^ L.nuRec), eqAtF r.1 w * recE q.2 w) ∧ Regs3E Ti L pw ry rv q ∧ A q) h)
      εmax 0 Tf := by
  unfold relayProgE
  refine ((sumcheckGSpec (T := 0) hst hcard (fun q ↦ Regs3E Ti L pw ry rv q ∧ A q)
    (Fm := fun q acc ↦ tCubeSumF L.nuRec (relayGE Ti ry L.nuRec (recE q.2)) acc)
    (tCubeSumF_plainFamily L.nuRec 2 _ fun q pre post ↦ polyLEF_relayGE Ti ry L.nuRec (recE q.2) pre post)
    (count := 3) (by norm_num) (by norm_num) (g := gWire) (by norm_num) hw relayRounds [] _
    (by simp [hrec])).mono
    (fun _ hp ↦ Doomed.mono hp fun q hq ↦ ⟨⟨hq.2.1.1, by rw [hq.1, relay_trueE Ti L pw hTi hmaps q.1 q.2 ry],
      hq.2.1.2⟩, hq.2.2⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun rf ↦ ?_
  exact if hrr : rf.1.length = relayRounds then
    ((e2ReadSpec hst (fun q ↦ rf.2 = tCubeSumF L.nuRec (relayGE Ti ry L.nuRec (recE q.2)) ([] ++ rf.1) ∧
        Regs3E Ti L pw ry rv q ∧ A q) hTf).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
      fun vR ↦
      (Spec.require (Pre := Doomed C (fun q ↦
            rf.2 = tCubeSumF L.nuRec (relayGE Ti ry L.nuRec (recE q.2)) ([] ++ rf.1) ∧ Regs3E Ti L pw ry rv q ∧ A q))
          (Post := fun _ h ↦ Doomed C (fun q ↦
            vR = (∑ w ∈ range (2 ^ L.nuRec), eqAtF rf.1 w * recE q.2 w) ∧ Regs3E Ti L pw ry rv q ∧ A q) h)
          fun _ hp hc ↦ Doomed.mono hp fun q hq ↦ ⟨by
            rw [List.nil_append, tCubeSumF_full _ _ (hrr.trans hrec.symm), relayGE, hc, hq.1], hq.2⟩).bind'
        fun _ ↦
        (Spec.ret (Post := fun r h ↦ r.1.length = relayRounds ∧ Doomed C (fun q ↦
            r.2 = (∑ w ∈ range (2 ^ L.nuRec), eqAtF r.1 w * recE q.2 w) ∧ Regs3E Ti L pw ry rv q ∧ A q) h)
          (rf.1, vR)).mono (fun _ hp ↦ ⟨hrr, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hrr hp.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Phase

end Lvm6.Ty
end -- part Lvm6TyWire

/-! ### Part `Lvm6TySpecP` (was its own module) -/
section

/-!
# The typed phases at `E2`: the proof (lvm6)

* `TErrsE.factsE`: the error side conditions in the phases' forms.
* **`typedSpecInE`**: on a fixed candidate set, the phases composed; the mini-bus step is `MiniSpecL6` with the
  carried predicate `aRmE` (the relayout's and the region values' meaning, and `R`).
* **`typedSpecGE`**: generic in the candidate set (`Lvm.M3.Spec.glue`); **`typedSpecE_of_mini`**: the frozen
  statement `TypedSpecEStmt` from `MiniSpecL6Stmt`.
* **Non-vacuity of the errors**: `εI_lt_one`, `errsE_at : TErrsE 1 εI 0` (every group admitted by PARAM's rule
  `8c ≤ 7·2^g`, `Lvm6.Params.group_le_εI`).
-/

set_option autoImplicit false

namespace Lvm6.Ty

open Lvm (FE2 FK)
open Lvm.Loop Lvm.Typed Lvm.E2V Lvm.E2T LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Verifier
open Lvm.M3 (Tab inst KeysOk AllSc LayOk FixOk)
open Lvm6.Mb (ClaimE BClaimG miniBusLProg6 mbLinB6 miniDepth stackOf gAB gLam gRd gY gYl MiniSpecL6
  MiniSpecL6Stmt)
open Finset
open scoped ENNReal NNReal

/-- The typed phases' program, unfolded. -/
theorem typedProgE_eq (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (acc : List E2 × E2) :
    typedProgE Ti L pw acc =
      (zeroProgE >>= fun z ↦ wireProgE Ti pw z.2 >>= fun w ↦ relayProgE Ti w.1 (w.2.2.getD 1 0) >>= fun r ↦
        accProgE Ti.Q Ti.lay acc.2 acc.1 (z.1 ++ w.1) w.2.1 >>= fun _ ↦
          miniBusLProg6 L Ti.mbT miniDepth >>= fun cl ↦ pure (typedClaimsE Ti w.1 w.2.2 r.1 r.2 cl)) := by
  rw [typedProgE]

theorem errG_mono_cE (g : ℕ) {c c' : ℕ} (h : c ≤ c') : errG g c ≤ errG g c' := by
  unfold errG
  gcongr

/-- **The error side conditions in the phases' forms.** -/
theorem TErrsE.factsE {L₀ : ℕ} {εmax T : ℝ≥0∞} (h : TErrsE L₀ εmax T) :
    (L₀ : ℝ≥0∞) * errG gTau 1 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errG gZero 2 + 0 ≤ εmax ∧
      (L₀ : ℝ≥0∞) * errG gGamma 2 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errG gWire 2 + 0 ≤ εmax ∧
      errG gKappa 1 ≤ εmax ∧ errG gT phiVarsE ≤ εmax :=
  ⟨by rw [add_zero]; exact h.tau,
    by rw [add_zero]; exact le_trans (by gcongr; exact errG_mono_cE _ (by norm_num)) h.zero,
    by rw [add_zero]; exact h.gamma, by rw [add_zero]; exact h.wire, h.kappa, h.t⟩

section Phases

variable (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (acc : List E2 × E2) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- The carried predicate: the mini-bus relation, `R`, the incoming accumulator. -/
def aR0E (q : Column L.nuMain × Column L.nuRec) : Prop :=
  M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ R q ∧ AccOkE Ti acc

/-- **Carried through the mini-bus**: the typed claims' meaning (`C_rec`'s extension at the relayout's point; the
committed, `σ′` and `KS` region values) and `R`. -/
def aRmE (w : List E2 × List E2 × List E2) (r : List E2 × E2) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  (r.2 = (∑ w' ∈ range (2 ^ L.nuRec), eqAtF r.1 w' * recE q.2 w') ∧
    w.2.2.getD 0 0 = regSumT Ti (· == .com) (zwE (zE Ti L pw q)) w.1 ∧
    w.2.2.getD 2 0 = regSumT Ti (· == .sigma) (zwE (zE Ti L pw q)) w.1 ∧
    w.2.2.getD 3 0 = regSumT Ti (· == .ks) (zwE (zE Ti L pw q)) w.1) ∧ R q

/-- **The typed phases at `E2` on a fixed candidate set**: the zerocheck, the wiring, the relayout, A23 and the
mini-bus (`MiniSpecL6`, from its frozen statement) composed; the first commitment's word carried to the
mini-bus. -/
noncomputable def typedSpecInE (hmini : MiniSpecL6Stmt) {L₀ : ℕ} {εmax : ℝ≥0∞}
    (S : Set (Column L.nuMain × Column L.nuRec)) (hS : S.ncard ≤ L₀) (hfin : S.Finite)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds) (hacc : acc.1.length = phiVarsE)
    (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT) (hfix : FixOk Ti.mbT)
    (hlin : mbLinB6 Ti.mbT = true) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth) {T : ℝ≥0∞} (hε : εmax < 1)
    (herr : TErrsE L₀ εmax T) :
    Spec (typedProgE Ti L pw acc)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ TGoodE Ti L hτL pw p ∧ R p ∧ AccOkE Ti acc) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHoldE L out p ∧ R p) h) εmax 0 T := by
  obtain ⟨hτ, hz, hγ, hwr, hκ, ht⟩ := herr.factsE
  have hst : Stable (fun _ : List Ev ↦ S) := fun _ _ _ ↦ rfl
  have hcard : ∀ h : List Ev, ((fun _ : List Ev ↦ S) h).ncard ≤ L₀ := fun _ ↦ hS
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  rw [typedProgE_eq]
  refine (((zeroSpecE (C := fun _ ↦ S) (T := 0) Ti.Q Ti.lay (zE Ti L pw) (aR0E Ti L acc hτL R) hst hcard
      hτ hz zero_le).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.2 fun q hq ↦ ⟨⟨wiringRelE_of_zeroOn _ _ hTi.1 _ hq.1, hq.2.1⟩, hq.2.2.1,
      hq.2.2.2⟩, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun z ↦ ?_
  by_cases hz' : z.1.length = xVars ∧ z.2.length = 3
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hz' ⟨hp.1.1, hp.1.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((wireSpecE (C := fun _ ↦ S) (T := 0) Ti L pw (aR0E Ti L acc hτL R) hst hcard hTi hγ hwr zero_le
      z.1 z.2).frame _ (hJ _)).mono (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind'
    fun w ↦ ?_
  by_cases hw' : w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hw' ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((relaySpecE (C := fun _ ↦ S) Ti L pw hst hcard hTi hmaps hrec hwr (Tf := 0) zero_le
      (fun q ↦ VsTrueE Ti (z.1 ++ w.1) w.2.1 ∧ aR0E Ti L acc hτL R q) w.1 w.2.2).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.1.2.2.2 fun q hq ↦ ⟨hq.2.1, hq.1, hq.2.2⟩, hp.2⟩)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun r ↦ ?_
  by_cases hr' : r.1.length = relayRounds
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hr' hp.1.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  refine (((accSpecQE Ti.Q Ti.lay (yIn := acc.2) acc.1 (z.1 ++ w.1) w.2.1 hacc
      (by rw [List.length_append, hz'.1, hw'.1]) hw'.2.1
      (Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
        aRmE Ti L pw R w r q))
      (fun _ _ _ h ↦ h) hκ ht).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨by
      by_cases hg : AccGoodE acc.2 acc.1 Ti.Q Ti.lay w.2.1 (z.1 ++ w.1)
      · refine .inr (Doomed.mono hp.1.2 fun q ⟨hm, hp', hR⟩ ↦ ⟨hp'.1, hp'.2, fun o ho ↦ ?_, hm, hR, hg.1⟩)
        have h0 := hg.2 o (by simp only [selBitsE]; omega)
        rw [deltaE, sub_eq_zero] at h0
        exact h0
      · exact .inl hg, hp.2⟩)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun _ ↦ ?_
  refine ((Classical.choice (hmini L Ti.mbT hτL S (aRmE Ti L pw R w r) hfin hS hsc hlay hkey hfix hlin hμ hε
      herr.ab herr.lam herr.rd herr.y herr.yl)).mono
    (fun _ hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind' fun cl ↦ ?_
  exact (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHoldE L out p ∧ R p) h)
      (typedClaimsE Ti w.1 w.2.2 r.1 r.2 cl)).mono
    (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ by
      obtain ⟨⟨h1, h2⟩, hR⟩ := hq
      refine ⟨fun c hc ↦ h2 c (List.mem_append_right _ hc), ⟨?_, ?_, ?_, ?_⟩, hR⟩
      · exact holds_relayPointE hrec r.1 hr' r.2 q.2 (h1 _ List.mem_cons_self)
      · exact ((holds_comE Ti L pw hTi hmaps q.1 q.2 w.1 _).mp
          (h2 _ (List.mem_append_left _ List.mem_cons_self))).symm
      · exact ((holds_sigmaE Ti L pw hTi hmaps q.1 q.2 w.1 _).mp
          (h1 _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm
      · exact ((holds_ksE Ti L pw hTi hmaps q.1 q.2 w.1 _).mp
          (h2 _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))).symm)
    (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

end Phases

/-- **The typed phases at `E2`, generic in the candidate sets** (glued, as season 1's `typedSpecGT`). -/
noncomputable def typedSpecGE (hmini : MiniSpecL6Stmt) (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK)
    (acc : List E2 × E2) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds) (hacc : acc.1.length = phiVarsE)
    (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT) (hfix : FixOk Ti.mbT)
    (hlin : mbLinB6 Ti.mbT = true) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀) (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hε : εmax < 1) (herr : TErrsE L₀ εmax T) :
    Spec (typedProgE Ti L pw acc)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGoodE Ti L hτL pw p ∧ R p ∧ AccOkE Ti acc) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHoldE L out p ∧ R p) h) εmax 0 T :=
  (Lvm.M3.Spec.glue (ι := {S : Set (Column L.nuMain × Column L.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecInE Ti L pw acc hτL R hmini S.1 S.2.2 S.2.1 hTi hmaps hrec hacc hsc hlay hkey hfix hlin
        hμ hε herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

/-- **The typed phases' frozen statement, from the mini-bus's** (`TypedSpecEStmt` given `MiniSpecL6Stmt`). -/
theorem typedSpecE_of_mini (hmini : MiniSpecL6Stmt) : TypedSpecEStmt := by
  intro Ti L pw acc hτL C R L₀ εmax T G hTi hmaps hrec hacc hsc hlay hkey hfix hlin hμ hCG hf hc hε herr
  exact ⟨typedSpecGE hmini Ti L pw acc hτL C R G hTi hmaps hrec hacc hsc hlay hkey hfix hlin hμ hCG hf hc hε herr⟩

/-! ## The error side conditions are satisfiable -/

/-- **An admitted group fits `εI`** (PARAM's rule `8c ≤ 7·2^g`): `errG g c ≤ εI`. -/
theorem errG_le_εI {c g : ℕ} (h : Lvm6.Params.admits c g = true) : errG g c ≤ εI := by
  have h2 : (((c : ℝ≥0) * (2 : ℝ≥0)⁻¹ ^ (128 + g) : ℝ≥0) : ℝ≥0∞) ≤ ((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr (Lvm6.Params.group_le_εI h)
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.coe_inv_two, ENNReal.coe_ofNat]
    at h2
  unfold errG εI
  rw [ENNReal.inv_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ g * (c * (2 : ℝ≥0∞)⁻¹ ^ 128) = c * (2 : ℝ≥0∞)⁻¹ ^ (128 + g) := by rw [pow_add]; ring
    _ ≤ _ := h2

/-- **`εI < 1`.** -/
theorem εI_lt_one : εI < 1 := by
  have h : (7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0) < 1 := by norm_num
  have h2 : ((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0) : ℝ≥0∞) < 1 := ENNReal.coe_lt_one_iff.mpr h
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two, ENNReal.coe_ofNat] at h2
  exact h2

/-- **The typed errors at one candidate against `εI`** (non-vacuity of `TErrsE`): every group is admitted by
PARAM's rule, the follower's lead `0`. -/
theorem errsE_at : TErrsE 1 εI 0 := by
  have hg : ∀ {c g : ℕ}, Lvm6.Params.admits c g = true → ((1 : ℕ) : ℝ≥0∞) * errG g c ≤ εI := fun h ↦ by
    rw [Nat.cast_one, one_mul]; exact errG_le_εI h
  have hg0 : ∀ {c g : ℕ}, Lvm6.Params.admits c g = true → ((1 : ℕ) : ℝ≥0∞) * errG g c + 0 ≤ εI := fun h ↦ by
    rw [add_zero]; exact hg h
  exact ⟨hg (by decide), hg (by decide), hg (by decide), hg (by decide), errG_le_εI (by decide),
    errG_le_εI (by decide), hg0 (by decide), hg0 (by decide), hg0 (by decide), hg0 (by decide),
    hg0 (by decide)⟩

end Lvm6.Ty
end -- part Lvm6TySpecP
