-- New for lvm2 E2F (slice S1, E2F-Q-S12): the proof of statement 12 (`typedSpecX`, LvmTypedSpecX): roll 8's
-- `typedSpecR` (LvmTypedSpec, LvmTypedSpecP, LvmTypedAcc) ported to the coordinate-split relation, eight matrices
-- and `Φ_Q` in 44 variables.
import LvmTypedSpecXD

/-!
# The typed phases with `E2` rows: the proof of `typedSpecX`

The phases and the side conditions are `LvmTypedSpecXD`'s; `typedSpecX` (LvmTypedSpecX) is `typedSpecXP`.

* **Entries** (`entsX_fit`): every entry of `entsX` has `o < 8`, `x < 2^20`, `y < 2^21` (a checked layout).
* **Zerocheck**: the 21-coordinate zero test of `zdelX` (`δ'(x) = rel₀(x)`, `δ'(x + 2^20) = rel₀(x) + rel₁(x)`):
  `τ` and `ω` are its 21 challenges (`zeroOn_snocX`: at `τ ++ [ω]` it is `Σ eq(τ, x)·(rel₀ + ω rel₁)`), one group
  of lead `21·L₀/|E|`; then equality-mode rounds of degree 2 on `zeroGTX`, the six values (`aZX`).
* **Wiring**: `γ` escapes at `5/|E|` (`polyN_escape`); 21 plain rounds on `wireGTX`; the eight matrix values
  (`VsTrueX`), the region values.
* **Relayout, mini-bus**: roll 8's, with the carried predicates' copies (`aR0X`, `aR1X`, `aWX`, `aRlX`).
* **A23** at `Φ_Q` in 44 variables (`accHypQX`: three selector bits).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd.Complete
open Lvm.M3 (Tab inst stackOf comCell NoCG KeysOk AllSc LayOk FixOk)
open Lvm.ASM (OpenClaims)
open Lvm.Acc (AccHyp AccGood line_zero line_one)
open Finset
open scoped ENNReal NNReal

/-! ## The entries -/

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

/-- **Every entry of `entsX` lies on `Φ_Q`'s cube** (a checked layout): `o < 8`, `x < 2^20`, `y < 2^21`. -/
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

/-! ## The matrices over `E` -/

/-- `(M_o z)(x)` over `E`, eight matrices. -/
noncomputable def matEX (Q : Program) (lay : Lay) (z : ℕ → FK) (o x : ℕ) : E := FE.toExt3 (matZX Q lay o z x)

theorem matEX_eq (Q : Program) (lay : Lay) (z : ℕ → FK) (o x : ℕ) :
    matEX Q lay z o x = (((entsX Q lay).filter fun e ↦ e.o == o && e.x == x).map fun e ↦
      FE.toExt3 e.c * zwE z e.y).sum := by
  unfold matEX matZX
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul]; rfl)

/-- A matrix's slot extension at `r` is its entries' sum (a checked layout). -/
theorem mleZ_matEX (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (o : ℕ) (r : List E) :
    mleZ xVars (matEX Q lay z o) r = (((entsX Q lay).filter fun e ↦ e.o == o).map fun e ↦
      eqAt r e.x * (FE.toExt3 e.c * zwE z e.y)).sum := by
  unfold mleZ
  simp only [matEX_eq]
  exact mle_filter xVars o r _ _ fun e he ↦ (entsX_fit Q lay hlay e he).2.1

/-- Off the cube the matrices are zero. -/
theorem matZX_out (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) {x : ℕ} (hx : ¬ x < 2 ^ xVars)
    (o : ℕ) : matZX Q lay o z x = 0 := by
  unfold matZX
  rw [List.filter_eq_nil_iff.mpr fun e he ↦ by
    have := (entsX_fit Q lay hlay e he).2.1
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro _ hex; omega]
  rfl

theorem mleZ_add (n : ℕ) (f g : ℕ → E) (r : List E) :
    mleZ n (fun x ↦ f x + g x) r = mleZ n f r + mleZ n g r := by
  simp only [mleZ, mul_add, Finset.sum_add_distrib]

/-- `x` read over `E` is `g`. -/
theorem toExt3_x : FE.toExt3 (FE.ofK FK.x) = ofK g := by
  rw [FE.toExt3_ofK]; rfl

/-- Coordinate `1` of the slot relation over `E`. -/
noncomputable def rel0E (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : E :=
  matEX Q lay z 0 x * matEX Q lay z 1 x + matEX Q lay z 4 x * matEX Q lay z 5 x +
    (matEX Q lay z 2 x + matEX Q lay z 3 x)

/-- Coordinate `X` of the slot relation over `E`. -/
noncomputable def rel1E (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : E :=
  matEX Q lay z 0 x * matEX Q lay z 5 x + matEX Q lay z 4 x * matEX Q lay z 1 x +
    ofK g * (matEX Q lay z 4 x * matEX Q lay z 5 x) + (matEX Q lay z 6 x + matEX Q lay z 7 x)

theorem rel0E_eq (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) :
    rel0E Q lay z x = FE.toExt3 (relX0 Q lay z x) := by
  simp only [rel0E, relX0, matEX, FE.toExt3_add, FE.toExt3_mul]
  ring

theorem rel1E_eq (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) :
    rel1E Q lay z x = FE.toExt3 (relX1 Q lay z x) := by
  simp only [rel1E, relX1, matEX, FE.toExt3_add, FE.toExt3_mul, toExt3_x]
  ring

/-! ## The zerocheck's zero test: 21 coordinates -/

/-- **The zero test's table** on 21 bits: `rel₀(x)` below `2^20`, `rel₀(x) + rel₁(x)` at `x + 2^20`. -/
noncomputable def zdelX (Q : Program) (lay : Lay) (z : ℕ → FK) (v : ℕ) : E :=
  if v < 2 ^ xVars then rel0E Q lay z v else rel0E Q lay z (v - 2 ^ xVars) + rel1E Q lay z (v - 2 ^ xVars)

/-- **The zero test on the cube gives the coordinate-split relation** (a checked layout). -/
theorem wiringRelX_of_zeroOn (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK)
    (h : ZeroOn (zdelX Q lay z) [] (xVars + 1)) : WiringRelX Q lay z := by
  rw [zeroOn_nil] at h
  have hp : (2 : ℕ) ^ (xVars + 1) = 2 ^ xVars + 2 ^ xVars := by rw [pow_succ]; omega
  intro x
  by_cases hx : x < 2 ^ xVars
  · have h0 := h x (by omega)
    have h1 := h (x + 2 ^ xVars) (by omega)
    simp only [zdelX, hx, ite_true] at h0
    simp only [zdelX, show ¬ (x + 2 ^ xVars < 2 ^ xVars) by omega, ite_false, Nat.add_sub_cancel, h0,
      zero_add] at h1
    rw [rel0E_eq, ← FE.toExt3_zero] at h0
    rw [rel1E_eq, ← FE.toExt3_zero] at h1
    exact ⟨FE.toExt3_injective h0, FE.toExt3_injective h1⟩
  · simp [relX0, relX1, matZX_out Q lay hlay z hx]

/-- **At `τ ++ [ω]` the zero test is `Σ eq(τ, x)·(rel₀(x) + ω·rel₁(x))`** (characteristic 2). -/
theorem zeroOn_snocX (Q : Program) (lay : Lay) (z : ℕ → FK) (τ : List E) (hτ : τ.length = xVars) (ω : E) :
    ZeroOn (zdelX Q lay z) (τ ++ [ω]) (xVars + 1) ↔
      ∑ w ∈ range (2 ^ xVars), eqAt τ w * (rel0E Q lay z w + ω * rel1E Q lay z w) = 0 := by
  have hl : (τ ++ [ω]).length = xVars + 1 := by simp [hτ]
  have key : foldT (zdelX Q lay z) (τ ++ [ω]) 0 =
      ∑ w ∈ range (2 ^ xVars), eqAt τ w * (rel0E Q lay z w + ω * rel1E Q lay z w) := by
    rw [foldT_snoc]
    unfold foldT
    rw [hτ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.mp hw
    simp only [zdelX, Nat.mul_zero, Nat.zero_add, Nat.mul_one, add_zero, hw', ite_true,
      show ¬ (w + 2 ^ xVars < 2 ^ xVars) by omega, ite_false, Nat.add_sub_cancel]
    linear_combination (ω * eqAt τ w * rel0E Q lay z w) * (CharTwo.two_eq_zero (R := E))
  unfold ZeroOn
  rw [hl, Nat.sub_self, pow_zero]
  constructor
  · intro h; rw [← key]; exact h 0 (by norm_num)
  · intro h v hv
    obtain rfl : v = 0 := by omega
    rw [key]; exact h

/-! ## The zerocheck's summand -/

/-- **The zerocheck's summand** at `ω`: `A₀B₀ + A₁B₁ + C₀ + ω·(A₀B₁ + A₁B₀ + x·A₁B₁ + C₁)` of the slot extensions. -/
noncomputable def zeroGTX (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E) (pt : List E) : E :=
  mleZ xVars (matEX Q lay z 0) pt * mleZ xVars (matEX Q lay z 1) pt +
    mleZ xVars (matEX Q lay z 4) pt * mleZ xVars (matEX Q lay z 5) pt +
    mleZ xVars (fun x ↦ matEX Q lay z 2 x + matEX Q lay z 3 x) pt +
    ω * (mleZ xVars (matEX Q lay z 0) pt * mleZ xVars (matEX Q lay z 5) pt +
      mleZ xVars (matEX Q lay z 4) pt * mleZ xVars (matEX Q lay z 1) pt +
      ofK g * (mleZ xVars (matEX Q lay z 4) pt * mleZ xVars (matEX Q lay z 5) pt) +
      mleZ xVars (fun x ↦ matEX Q lay z 6 x + matEX Q lay z 7 x) pt)

/-- **The zerocheck's claim**: before any round, the `eq(τ, ·)`-weighted relation batched by `ω`. -/
theorem zero_nilX (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E) (τ : List E) :
    eqCubeSum τ xVars (zeroGTX Q lay z ω) [] =
      ∑ w ∈ range (2 ^ xVars), eqAt τ w * (rel0E Q lay z w + ω * rel1E Q lay z w) := by
  rw [eqCubeSum_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.mp hu
  unfold zeroGTX mleZ rel0E rel1E
  simp only [sum_eqAt_bitsE hu']

theorem polyLE_zeroGX (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E) (pre post : List E) :
    PolyLE 2 fun x ↦ zeroGTX Q lay z ω (pre ++ x :: post) := by
  have m : ∀ f : ℕ → E, PolyLE 1 fun x ↦ mleZ xVars f (pre ++ x :: post) := fun f ↦ polyLE_mleZ _ _ pre post
  exact ((((m _).mul (m _)).add ((m _).mul (m _))).add ((m _).mono (by norm_num))).add
    (PolyLE.const_mul (((((m _).mul (m _)).add ((m _).mul (m _))).add
      (PolyLE.const_mul ((m _).mul (m _)) _)).add ((m _).mono (by norm_num))) ω)

/-- The six true values at `r_x`, in the zerocheck's order `A₀, A₁, B₀, B₁, C₀, C₁`. -/
noncomputable def tvX (Q : Program) (lay : Lay) (z : ℕ → FK) (rx : List E) : ℕ → E
  | 0 => mleZ xVars (matEX Q lay z 0) rx
  | 1 => mleZ xVars (matEX Q lay z 4) rx
  | 2 => mleZ xVars (matEX Q lay z 1) rx
  | 3 => mleZ xVars (matEX Q lay z 5) rx
  | 4 => mleZ xVars (fun x ↦ matEX Q lay z 2 x + matEX Q lay z 3 x) rx
  | _ => mleZ xVars (fun x ↦ matEX Q lay z 6 x + matEX Q lay z 7 x) rx

/-- **The zerocheck's final check** at the six true values. -/
theorem zero_reqX (Q : Program) (lay : Lay) (z : ℕ → FK) (ω : E) (rx v : List E)
    (hv : ∀ k ≤ 5, v.getD k 0 = tvX Q lay z rx k) :
    v.getD 0 0 * v.getD 2 0 + v.getD 1 0 * v.getD 3 0 + v.getD 4 0 +
      ω * (v.getD 0 0 * v.getD 3 0 + v.getD 1 0 * v.getD 2 0 + ofK g * (v.getD 1 0 * v.getD 3 0) +
        v.getD 5 0) = zeroGTX Q lay z ω rx := by
  rw [hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num), hv 4 (by norm_num),
    hv 5 (by norm_num)]
  rfl

/-! ## The wiring's family -/

/-- The power of `γ` weighting matrix `o` (`A₀ B₀ D₀ W₀ A₁ B₁ D₁ W₁` at `0 2 4 4 1 3 5 5`). -/
def kX (o : ℕ) : ℕ :=
  if o = 0 then 0 else if o = 1 then 2 else if o = 4 then 1 else if o = 5 then 3 else if o < 4 then 4 else 5

/-- The wiring's batching weight of matrix `o`. -/
def wGXo (γ : E) (o : ℕ) : E := γ ^ kX o

/-- **The wiring's matrix weight** at `(r_x, pt)`, eight matrices. -/
noncomputable def wireMX (Q : Program) (lay : Lay) (γ : E) (rx pt : List E) : E :=
  ((entsX Q lay).map fun e ↦ wGXo γ e.o * FE.toExt3 e.c * eqAt rx e.x * eqAt pt e.y).sum

/-- **The wiring's summand**, eight matrices. -/
noncomputable def wireGTX (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E) (rx pt : List E) : E :=
  wireMX Q lay γ rx pt * mleZ yVars (zwE z) pt

/-- A selector-weighted sum of the per-matrix sums is the weighted sum over all entries (every `o < 8`). -/
theorem sum_sel_filter8 (g : ℕ → E) (f : Ent → E) :
    ∀ l : List Ent, (∀ e ∈ l, e.o < 8) →
      ∑ w ∈ range (2 ^ 3), g w * ((l.filter fun e ↦ e.o == w).map f).sum = (l.map fun e ↦ g e.o * f e).sum
  | [], _ => by simp
  | e :: l, hl => by
    have ih := sum_sel_filter8 g f l fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have he : e.o < 2 ^ 3 := hl e (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih]
    rw [Finset.sum_congr rfl fun w _ ↦ show g w * ((((e :: l).filter fun e ↦ e.o == w)).map f).sum =
        (if e.o = w then g e.o * f e else 0) + g w * ((l.filter fun e ↦ e.o == w).map f).sum by
      by_cases h : e.o = w
      · subst h; simp [mul_add]
      · simp [h]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr he)]

theorem sum_wGXo (γ : E) (S : ℕ → E) :
    ∑ w ∈ range (2 ^ 3), wGXo γ w * S w =
      S 0 + γ * S 4 + γ ^ 2 * S 1 + γ ^ 3 * S 5 + γ ^ 4 * (S 2 + S 3) + γ ^ 5 * (S 6 + S 7) := by
  simp [Finset.sum_range_succ, wGXo, kX]
  ring

/-- The wiring sumcheck's claim before any round, selector-weighted (a checked layout). -/
theorem wire_nil8 (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E) (rx : List E) :
    tCubeSum yVars (wireGTX Q lay z γ rx) [] =
      ∑ w ∈ range (2 ^ 3), wGXo γ w * mleZ xVars (matEX Q lay z w) rx := by
  have hfit := entsX_fit Q lay hlay
  simp only [mleZ_matEX Q lay hlay]
  rw [sum_sel_filter8 (wGXo γ) _ _ fun e he ↦ (hfit e he).1, tCubeSum_nil]
  unfold wireGTX wireMX
  have hz : ∀ u < 2 ^ yVars, mleZ yVars (zwE z) (bitsE u yVars) = zwE z u := fun u hu ↦ by
    unfold mleZ; exact sum_eqAt_bitsE hu _
  rw [Finset.sum_congr rfl fun u hu ↦ by rw [hz u (Finset.mem_range.mp hu), ← List.sum_map_mul_right],
    sum_list_swap]
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  have hy := (hfit e he).2.2
  rw [Finset.sum_congr rfl fun u hu ↦ by
    rw [eqAt_bitsE_lt (Finset.mem_range.mp hu) hy]]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (range (2 ^ yVars)) e.y, ite_eq_left (Finset.mem_range.mpr hy)]
  ring

/-- **The wiring sumcheck's claim** before any round: the six true values batched by `γ^0 … γ^5`. -/
theorem wire_nilX (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E) (rx : List E) :
    tCubeSum yVars (wireGTX Q lay z γ rx) [] = ∑ k ∈ range 6, γ ^ k * tvX Q lay z rx k := by
  rw [wire_nil8 Q lay hlay, sum_wGXo]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h4 : tvX Q lay z rx 4 = mleZ xVars (matEX Q lay z 2) rx + mleZ xVars (matEX Q lay z 3) rx :=
    mleZ_add _ _ _ _
  have h5 : tvX Q lay z rx 5 = mleZ xVars (matEX Q lay z 6) rx + mleZ xVars (matEX Q lay z 7) rx :=
    mleZ_add _ _ _ _
  rw [h4, h5]
  change _ = 0 + γ ^ 0 * mleZ xVars (matEX Q lay z 0) rx + γ ^ 1 * mleZ xVars (matEX Q lay z 4) rx +
    γ ^ 2 * mleZ xVars (matEX Q lay z 1) rx + γ ^ 3 * mleZ xVars (matEX Q lay z 5) rx + _ + _
  ring

/-- Matrix `o`'s extension over `E` is the sum over its entries. -/
theorem matMleX_eq_sum (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E) :
    matMleX Q lay o rxy = (((entsX Q lay).filter fun e ↦ e.o == o).map fun e ↦
      FE.toExt3 e.c * eqAt rxy (e.x + 2 ^ xVars * e.y)).sum := by
  unfold matMleX matMleFX
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul, toExt3_eqW'])

/-- **The wiring's final matrix weight** is the eight matrices' values batched by `γ` (`|r_x| = 20`). -/
theorem wireMX_full (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (γ : E) (rx ry : List E)
    (hrx : rx.length = xVars) :
    wireMX Q lay γ rx ry = ∑ o ∈ range (2 ^ 3), wGXo γ o * matMleX Q lay o (rx ++ ry) := by
  have hfit := entsX_fit Q lay hlay
  simp only [matMleX_eq_sum]
  rw [sum_sel_filter8 (wGXo γ) _ _ fun e he ↦ (hfit e he).1]
  unfold wireMX
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  have hx := (hfit e he).2.1
  rw [eqAt_append, hrx, eqAt_mod rx (e.x + 2 ^ xVars * e.y), hrx,
    show (e.x + 2 ^ xVars * e.y) % 2 ^ xVars = e.x by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx],
    show (e.x + 2 ^ xVars * e.y) / 2 ^ xVars = e.y by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]]
  ring

theorem polyLE_wireMX (Q : Program) (lay : Lay) (γ : E) (rx pre post : List E) :
    PolyLE 1 fun x ↦ wireMX Q lay γ rx (pre ++ x :: post) :=
  polyLE_listSum 1 _ _ fun e _ ↦ PolyLE.const_mul (polyLE_eqAt pre post e.y) _

theorem polyLE_wireGX (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E) (rx pre post : List E) :
    PolyLE 2 fun x ↦ wireGTX Q lay z γ rx (pre ++ x :: post) :=
  PolyLE.mul (polyLE_wireMX Q lay γ rx pre post) (polyLE_mleZ _ _ pre post)

open Polynomial in
/-- **`Σ_{k ≤ n} γ^k a_k` against a different tuple agrees at `n/|E|` of the `γ`** (Schwartz–Zippel). -/
theorem polyN_escape (n : ℕ) (a b : ℕ → E) (hne : ∃ k ≤ n, a k ≠ b k) :
    avgE (fun c ↦ indE (∑ k ∈ range (n + 1), c ^ k * a k = ∑ k ∈ range (n + 1), c ^ k * b k)) ≤ errE n := by
  have hp : ∀ f : ℕ → E, (∑ k ∈ range (n + 1), Polynomial.C (f k) * X ^ k).natDegree ≤ n := fun f ↦
    natDegree_sum_le_of_forall_le _ _ fun k hk ↦
      (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.mp hk; omega)
  have hcoeff : ∀ (f : ℕ → E) (k : ℕ), k ≤ n →
      (∑ i ∈ range (n + 1), Polynomial.C (f i) * X ^ i).coeff k = f k := fun f k hk ↦ by
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by omega))]
  obtain ⟨k, hk, hab⟩ := hne
  have hne' : (∑ i ∈ range (n + 1), Polynomial.C (a i) * X ^ i) ≠
      ∑ i ∈ range (n + 1), Polynomial.C (b i) * X ^ i := fun h ↦
    hab (by rw [← hcoeff a k hk, ← hcoeff b k hk, h])
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans (sz_escape hne' (hp a) (hp b))
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  simpa only [mul_comm] using hc

/-! ## A23 at `Φ_Q` in 44 variables -/

/-- **`Φ_Q` over `E`, coordinate-split, is the sparse multilinear sum** of the eight matrices' entries. -/
theorem phiQX_eq_sum (Q : Program) (lay : Lay) (pt : List E) :
    PhiQX Q lay pt = ((entsX Q lay).map fun e ↦ FE.toExt3 e.c * eqAt pt e.idxX).sum := by
  unfold PhiQX PhiQFX
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul, toExt3_eqW'])

/-- The fixed claims' errors, eight matrices: `δ_o = v_o − M̃_o(r_x, r_y)` for `o < 8`. -/
noncomputable def deltaQX (Q : Program) (lay : Lay) (vs rxy : List E) (o : ℕ) : E :=
  if o < 8 then vs.getD o 0 - matMleX Q lay o rxy else 0

/-- **The selector split, three bits**: at `κ ++ r_x ++ r_y`, `y_own − Φ_Q` is the selector extension of the
eight matrices' errors. -/
theorem phiQX_fold (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (rxy vs : List E) (hvs : vs.length = 8)
    (κ : List E) (hκ : κ.length = 3) :
    yOwnQ vs κ - PhiQX Q lay (bOfQ rxy κ) = ∑ w ∈ range (2 ^ 3), eqAt κ w * deltaQX Q lay vs rxy w := by
  have hfit := entsX_fit Q lay hlay
  have hk8 : (Verifier.eqKernel κ).length = 2 ^ 3 := by rw [eqKernel_length, hκ]
  have hown : yOwnQ vs κ = ∑ w ∈ range (2 ^ 3), eqAt κ w * vs.getD w 0 := by
    unfold yOwnQ
    rw [LeanVM.Protocol.KeccakGkr.dot_eq _ _ (by rw [hk8, hvs]; rfl), hk8]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [eqKernel_getD, hκ, ite_eq_left (Finset.mem_range.mp hw)]
  have hphi : PhiQX Q lay (bOfQ rxy κ) = ∑ w ∈ range (2 ^ 3), eqAt κ w * matMleX Q lay w rxy := by
    simp only [matMleX_eq_sum]
    rw [sum_sel_filter8 (eqAt κ) _ _ fun e he ↦ (hfit e he).1, phiQX_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    have ho := (hfit e he).1
    unfold bOfQ
    rw [eqAt_append, hκ, eqAt_mod κ, hκ, Ent.idxX,
      show (e.o + 8 * (e.x + 2 ^ xVars * e.y)) % 2 ^ 3 = e.o by omega,
      show (e.o + 8 * (e.x + 2 ^ xVars * e.y)) / 2 ^ 3 = e.x + 2 ^ xVars * e.y by omega]
    ring
  rw [hown, hphi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  rw [deltaQX, ite_eq_left (by simpa using hw), mul_sub]

/-- **`AccHyp` at `Φ_Q` in 44 variables**: `dk = 3` (the selector), `D = 44`. -/
theorem accHypQX (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (a rxy vs : List E) (ha : a.length = phiVarsX)
    (hr : rxy.length = xVars + yVars) (hvs : vs.length = 8) :
    AccHyp 3 phiVarsX a (yOwnQ vs) (bOfQ rxy) (PhiQX Q lay) (deltaQX Q lay vs rxy) where
  line_deg κ _ := by
    obtain ⟨g, hg, hgv⟩ := lineDeg_sparse ((entsX Q lay).map fun e ↦ (e.idxX, FE.toExt3 e.c)) a (bOfQ rxy κ)
    refine ⟨g, ha ▸ hg, fun t ↦ ?_⟩
    rw [hgv, phiQX_eq_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun e _ ↦ rfl)
  at0 κ hκ := line_zero _ _ (by simp [bOfQ, ha, hr, hκ, phiVarsX]; omega)
  at1 κ hκ := line_one _ _ (by simp [bOfQ, ha, hr, hκ, phiVarsX]; omega)
  fold κ hκ := phiQX_fold Q lay hlay rxy vs hvs κ hκ

theorem errE5_le_lead (L₀ : ℕ) : (L₀ : ℝ≥0∞) * errE 5 + 0 ≤ leadTX L₀ := by
  unfold leadTX errE
  rw [add_zero, add_zero, Nat.cast_one, one_mul,
    show (L₀ : ℝ≥0∞) * ((5 : ℕ) * (Fintype.card E : ℝ≥0∞)⁻¹) = (5 : ℕ) * ((L₀ : ℝ≥0∞) * (Fintype.card E : ℝ≥0∞)⁻¹)
      by ring]
  gcongr
  norm_num

/-- **The error side conditions, unpacked.** -/
theorem TErrsX.facts {L₀ : ℕ} {I : M3Instance} {εmax T : ℝ≥0∞} (h : TErrsX L₀ I εmax T) :
    (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax ∧ (L₀ : ℝ≥0∞) * errE 5 + 0 ≤ εmax ∧
      max (3 * errE 1) (abError I L₀ + 0) ≤ εmax ∧ errE phiVarsX ≤ εmax ∧
      abError I L₀ + 0 ≤ εmax ∧ abError I L₀ < 1 ∧ roundError L₀ 4 ≤ εmax ∧
      interpLead L₀ 2 (lambdaError L₀) ≤ εmax ∧ lambdaError L₀ + 0 ≤ εmax ∧ roundError L₀ 3 + T ≤ εmax ∧
      T ≤ εmax ∧ ∀ n, xiError I L₀ + sumcheckLead (List.replicate n none) T ≤ εmax := by
  have hM1 : abError I L₀ + 0 ≤ leadMaxTX L₀ I T := le_max_of_le_right (le_max_left _ _)
  have hM2 : 3 * errE 1 ≤ leadMaxTX L₀ I T := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hM3 : T ≤ leadMaxTX L₀ I T := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hle : ∀ a : ℝ≥0∞, a ≤ a + leadMaxTX L₀ I T := fun a ↦ le_self_add
  refine ⟨?_, (errE5_le_lead L₀).trans h.lead, (max_le hM2 hM1).trans h.follow, (hle _).trans h.acc,
    hM1.trans h.follow, h.ab.1, (hle _).trans (h.rounds 4 le_rfl), (hle _).trans h.lam.1, ?_, ?_,
    hM3.trans h.follow, fun n ↦ ?_⟩
  · rw [← roundError_eq, add_zero]; exact (hle _).trans (h.rounds 2 (by norm_num))
  · rw [add_zero]; exact (hle _).trans h.lam.2
  · exact (add_le_add le_rfl hM3).trans (h.rounds 3 (by norm_num))
  · exact (add_le_add le_rfl ((sumcheckLead_le _ _).trans hM3)).trans h.xi

/-! ## The phases' specifications -/

section Phases

variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- The carried predicate: the mini-bus relation, `R`, `AccOk acc_in` at `Φ_Q` in 44 variables. -/
def aR0X (q : Column L.nuMain × Column L.nuRec) : Prop :=
  M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧ R q ∧
    PhiQX Ti.Q Ti.lay (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y

/-- **After the zerocheck**: the six values are the slot extensions at `r_x`. -/
def aZX (z : List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  (∀ k ≤ 5, z.2.getD k 0 = tvX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) z.1 k) ∧ aR0X Ti L pub hτL R q

/-- The eight matrix values are the matrices' extensions at `r_x ++ r_y`. -/
def VsTrueX (rxy vs : List E) : Prop := ∀ o < 8, vs.getD o 0 = matMleX Ti.Q Ti.lay o rxy

/-- Carried through the relayout. -/
def aR1X (z : List E × List E) (w : List E × List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  VsTrueX Ti (z.1 ++ w.1) w.2.1 ∧ aRegs Ti L pub w.1 w.2.2 q ∧ aR0X Ti L pub hτL R q

/-- **After the wiring**: `S_flat`'s value is true, with the rest. -/
def aWX (z : List E × List E) (w : List E × List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  w.2.2.getD 1 0 = regSum Ti (· == .sflat) (zwE (Ti.zOf L pub q.1 q.2)) w.1 ∧ aR1X Ti L pub hτL R z w q

/-- **After the relayout**: `C_rec`'s extension at the point, with the rest. -/
def aRlX (z : List E × List E) (w : List E × List E × List E) (r : List E × E)
    (q : Column L.nuMain × Column L.nuRec) : Prop :=
  r.2 = mleZ L.nuRec (recE L q) r.1 ∧ aR1X Ti L pub hτL R z w q

variable {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column L.nuMain × Column L.nuRec)) (hS : S.ncard ≤ L₀)

theorem leadTX_split (L₀ : ℕ) :
    ((xVars : ℕ) : ℝ≥0∞) * ((L₀ : ℝ≥0∞) * errE 1) + ((L₀ : ℝ≥0∞) * errE 1 + 0) ≤ leadTX L₀ := by
  unfold leadTX
  refine le_of_eq ?_
  push_cast
  ring

/-- **The zerocheck** (`τ`, `ω`: the 21-coordinate zero test; 20 equality-mode rounds; the six values): from doom
of the zero test on the cube to doom of the six values at `r_x`; lead `21·L₀/|E|`. -/
noncomputable def zeroSpecTX (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) (hTz : (L₀ : ℝ≥0∞) * errE 5 + 0 ≤ εmax) :
    Spec zeroProgX
      (Doomed (fun _ ↦ S) (fun q ↦ ZeroOn (zdelX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) [] (xVars + 1) ∧
        aR0X Ti L pub hτL R q))
      (fun z h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aZX Ti L pub hτL R z) h) εmax (leadTX L₀)
      ((L₀ : ℝ≥0∞) * errE 5 + 0) := by
  unfold zeroProgX
  refine ((Lvm.KG.zeroSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
    (fun q ↦ zdelX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) (aR0X Ti L pub hτL R) (n := xVars + 1) (m := xVars)
    (by omega) (εmax := εmax) (T := (L₀ : ℝ≥0∞) * errE 1 + 0)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
    (leadTX_split L₀) le_rfl).bind fun τ ↦ ?_
  exact if hτ : τ.length = xVars then
    ((doomSample (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (fun q ↦ ZeroOn (zdelX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) τ (xVars + 1) ∧ aR0X Ti L pub hτL R q)
      (fun ω q ↦ ZeroOn (zdelX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) (τ ++ [ω]) (xVars + 1) ∧
        aR0X Ti L pub hτL R q) (errE 1)
      (fun q hq ↦ (Lvm.KG.zero_escape (fun q ↦ zdelX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2)) (aR0X Ti L pub hτL R)
        (xVars + 1) τ q hq).trans (le_of_eq (ite_eq_left (by rw [hτ]; omega))))
      (εmax := εmax) (T := 0)).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun ω ↦
      ((eqSumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS) (aR0X Ti L pub hτL R)
          (F := fun q acc ↦ eqCubeSum τ xVars (zeroGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) ω) acc)
          (eqCubeSum_eqFamily τ xVars 2 hτ _ fun q pre post ↦ polyLE_zeroGX _ _ _ _ pre post)
          (count := 3) (by norm_num) (by norm_num) zero_le he τ [] 0 (by simp)).mono
        (fun _ hp ↦ Doomed.mono hp fun q hq ↦ ⟨(zeroOn_snocX _ _ _ τ hτ ω).mpr (by
          rw [← zero_nilX]; exact hq.1.symm), hq.2⟩)
        (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun rf ↦
        if hrf : rf.1.length = xVars then
          ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
              (fun q ↦ rf.2 = eqCubeSum τ xVars (zeroGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) ω) ([] ++ rf.1) ∧
                aR0X Ti L pub hτL R q) hTz 5).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
              le_rfl).bind fun v ↦
            (Spec.require (Pre := fun h ↦ v.length = 5 + 1 ∧ Doomed (fun _ ↦ S) (fun q ↦ rf.2 =
                eqCubeSum τ xVars (zeroGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) ω) ([] ++ rf.1) ∧
                  aR0X Ti L pub hτL R q) h)
              (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aZX Ti L pub hτL R (rf.1, v)) h)
              fun _ hp hc ↦ Doomed.mono hp.2 fun q ⟨hv, hR⟩ ↦ ⟨by
                rw [List.nil_append, eqCubeSum_full τ xVars _ hrf hτ, hc]
                exact zero_reqX _ _ _ ω rf.1 v hv, hR⟩).bind fun _ ↦
              (Spec.ret (Post := fun z h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aZX Ti L pub hτL R z) h)
                (rf.1, v)).mono (fun _ hp ↦ ⟨hrf, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hp ↦ hrf (hp.1.trans hτ)) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hτ hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **`γ`'s escape**: a wrong six-tuple batched by `γ^0 … γ^5` meets the true one at `5/|E|` of the `γ`. -/
theorem wire_escapeX (hTi : Ti.Ok) (z : List E × List E) (q : Column L.nuMain × Column L.nuRec)
    (hq : ¬ aZX Ti L pub hτL R z q) :
    avgE (fun γ ↦ indE (((List.range 6).map fun k ↦ γ ^ k * z.2.getD k 0).sum =
      tCubeSum yVars (wireGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) [] ∧ aR0X Ti L pub hτL R q)) ≤
      errE 5 := by
  by_cases hR : aR0X Ti L pub hτL R q
  · have hne : ∃ k ≤ 5, z.2.getD k 0 ≠ tvX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) z.1 k := by
      by_contra hn
      push Not at hn
      exact hq ⟨hn, hR⟩
    refine (avgE_mono fun γ ↦ indE_mono fun hγ ↦ ?_).trans
      (polyN_escape 5 (fun k ↦ z.2.getD k 0) (tvX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) z.1) hne)
    have h := hγ.1
    rw [listRange_sum, wire_nilX _ _ hTi.1] at h
    exact h
  · refine (avgE_mono fun γ ↦ indE_mono (q := False) fun h ↦ hR h.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

/-- `wGX` is the selector-weighted sum of the eight values. -/
theorem wGX_eq (γ : E) (vs : List E) : wGX γ vs = ∑ o ∈ range (2 ^ 3), wGXo γ o * vs.getD o 0 := by
  rw [sum_wGXo]; rfl

/-- **The wiring** (`γ`, 21 plain rounds, the matrix and region values, the final check): from doom of the six
values at `r_x` to doom of the region values at `r_y` and the eight matrix values; lead `L₀·5/|E|`. -/
noncomputable def wireSpecTX (hTi : Ti.Ok) (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) (z : List E × List E) :
    Spec (wireProgX Ti pub z.2)
      (fun h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aZX Ti L pub hτL R z) h)
      (fun w h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 ∧ w.2.2.length = 4 ∧
        Doomed (fun _ ↦ S) (aWX Ti L pub hτL R z w) h) εmax ((L₀ : ℝ≥0∞) * errE 5 + 0) 0 := by
  exact if hz : z.1.length = xVars then by
    unfold wireProgX
    refine ((doomSample (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS) (aZX Ti L pub hτL R z)
      (fun γ q ↦ ((List.range 6).map fun k ↦ γ ^ k * z.2.getD k 0).sum =
        tCubeSum yVars (wireGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) [] ∧ aR0X Ti L pub hτL R q)
      (errE 5) (fun q hq ↦ wire_escapeX Ti L pub hτL R hTi z q hq) (εmax := εmax) (T := 0)).mono
      (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun γ ↦ ?_
    refine (LeanVM.Protocol.KeccakGkr.sumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (aR0X Ti L pub hτL R)
      (F := fun q acc ↦ tCubeSum yVars (wireGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) acc)
      (tCubeSum_plainFamily yVars 2 _ fun q pre post ↦ polyLE_wireGX _ _ _ _ _ pre post)
      (count := 3) (by norm_num) (by norm_num) zero_le he yVars [] _ (by simp)).bind fun rf ↦ ?_
    exact if hry : rf.1.length = yVars then
      ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
          (fun q ↦ rf.2 = tCubeSum yVars (wireGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
            aR0X Ti L pub hτL R q) (zero_le) 7).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
          le_rfl).bind fun vs ↦
        if hvs : vs.length = 8 then
          ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
              (fun q ↦ rf.2 = tCubeSum yVars (wireGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
                aR0X Ti L pub hτL R q) (zero_le) 3).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
              le_rfl).bind fun rv ↦
            if hrv : rv.length = 4 then
              (Spec.require (Pre := fun h ↦ rv.length = 3 + 1 ∧ Doomed (fun _ ↦ S) (fun q ↦ rf.2 =
                  tCubeSum yVars (wireGTX Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
                    aR0X Ti L pub hτL R q) h)
                (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aWX Ti L pub hτL R z (rf.1, vs, rv)) h)
                fun _ hp hc ↦ Doomed.mono hp.2 fun q ⟨hS1, hV, ⟨h0, h2, h3⟩, hR⟩ ↦ ⟨by
                  have hsum : ∑ o ∈ range (2 ^ 3), wGXo γ o * vs.getD o 0 =
                      ∑ o ∈ range (2 ^ 3), wGXo γ o * matMleX Ti.Q Ti.lay o (z.1 ++ rf.1) :=
                    Finset.sum_congr rfl fun o ho ↦ by
                      rw [hV o ((Finset.mem_range.mp ho).trans_eq (by norm_num))]
                  rw [List.nil_append, tCubeSum_full _ _ hry, wireGTX, wireMX_full _ _ hTi.1 _ _ _ hz,
                    mleZ_zOf Ti L pub hTi, hc, sum_four rv hrv, wGX_eq, hsum]
                  simp only at hS1 h0 h2 h3
                  rw [h0, hS1, h2, h3], hR⟩).bind fun _ ↦
                (Spec.ret (Post := fun w h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 ∧
                    w.2.2.length = 4 ∧ Doomed (fun _ ↦ S) (aWX Ti L pub hτL R z w) h) (rf.1, vs, rv)).mono
                  (fun _ hp ↦ ⟨hz, hry, hvs, hrv, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
            else Spec.dead.mono (fun _ hp ↦ hrv hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
        else Spec.dead.mono (fun _ hp ↦ hvs hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ hp ↦ hry hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hz hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **The `S_flat` relayout** (roll 8's, the carried predicates coordinate-split). -/
noncomputable def relaySpecTX (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) {Tf : ℝ≥0∞} (hTf : Tf ≤ εmax) (z : List E × List E)
    (w : List E × List E × List E) :
    Spec (relayProg Ti w.1 (w.2.2.getD 1 0))
      (fun h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 ∧ w.2.2.length = 4 ∧
        Doomed (fun _ ↦ S) (aWX Ti L pub hτL R z w) h)
      (fun r h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 ∧ r.1.length = relayRounds ∧
        Doomed (fun _ ↦ S) (aRlX Ti L pub hτL R z w r) h) εmax 0 Tf := by
  exact if hl : z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 then by
    unfold relayProg
    refine ((LeanVM.Protocol.KeccakGkr.sumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (aR1X Ti L pub hτL R z w)
      (F := fun q acc ↦ tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) acc)
      (tCubeSum_plainFamily L.nuRec 2 _ fun q pre post ↦ polyLE_relayG _ _ _ _ _ pre post)
      (count := 3) (by norm_num) (by norm_num) zero_le he relayRounds [] _ (by simp [hrec])).mono
      (fun _ hp ↦ Doomed.mono hp.2.2.2.2 fun q hq ↦ ⟨by
        rw [hq.1, relay_true Ti L pub hTi hmaps q.1 q.2 w.1], hq.2⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun rf ↦ ?_
    exact if hrr : rf.1.length = relayRounds then
      ((doomRead (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
          (fun q ↦ rf.2 = tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) ([] ++ rf.1) ∧
            aR1X Ti L pub hτL R z w q) hTf).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind
        fun vR ↦
        (Spec.require (Pre := Doomed (fun _ ↦ S) (fun q ↦
              rf.2 = tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) ([] ++ rf.1) ∧
                aR1X Ti L pub hτL R z w q))
            (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aRlX Ti L pub hτL R z w (rf.1, vR)) h)
            fun _ hp hc ↦ Doomed.mono hp fun q hq ↦ ⟨by
              have h1 : vR = mleZ L.nuRec (recE L q) rf.1 := hq.1
              rw [List.nil_append, tCubeSum_full _ _ (hrr.trans hrec.symm), relayGT, hc, h1]
              rfl, hq.2⟩).bind fun _ ↦
          (Spec.ret (Post := fun r h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 ∧
              r.1.length = relayRounds ∧ Doomed (fun _ ↦ S) (aRlX Ti L pub hτL R z w r) h) (rf.1, vR)).mono
            (fun _ hp ↦ ⟨hl.1, hl.2.1, hl.2.2, hrr, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hrr hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hl ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **A23 at `Φ_Q` in 44 variables** (`accSpecG` at `accHypQX`): outside `AccGood` the phase's own escape bounds
the run; inside it, the eight matrix values and `AccOk acc_in` are true and leave the carried predicate. -/
noncomputable def accSpecTyX (hTi : Ti.Ok) (hacc : pub.accIn.pt.length = phiVarsX) {Tm : ℝ≥0∞}
    (hD : errE phiVarsX ≤ εmax) (hTm : Tm ≤ εmax) (z : List E × List E) (w : List E × List E × List E)
    (r : List E × E) :
    Spec (accProgQX Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1)
      (fun h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 ∧ r.1.length = relayRounds ∧
        Doomed (fun _ ↦ S) (aRlX Ti L pub hτL R z w r) h)
      (fun _ h ↦ Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
        aRm Ti L pub R w r q) h) εmax (max (3 * errE 1) Tm) Tm :=
  if hl : z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 8 then
    (Lvm.Acc.accSpecG (ok := true) (yIn := FE.toExt3 pub.accIn.y)
        (accHypQX Ti.Q Ti.lay hTi.1 (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1
          (by rw [List.length_map, hacc]) (by rw [List.length_append, hl.1, hl.2.1]) hl.2.2)
        (Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
          aRm Ti L pub R w r q)) (fun _ _ _ h ↦ h) hD hTm).mono
      (fun _ hp ↦ by
        by_cases hg : AccGood 3 true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (PhiQX Ti.Q Ti.lay)
            (deltaQX Ti.Q Ti.lay w.2.1 (z.1 ++ w.1))
        · refine .inr (Doomed.mono hp.2.2.2.2 fun q ⟨hm, ⟨hv, hrg⟩, hR⟩ ↦ ⟨hv, fun o ho ↦ ?_, hrg, hm, hR, hg.2.1⟩)
          have h0 := hg.2.2 o (by norm_num; omega)
          rw [deltaQX, ite_eq_left ho, sub_eq_zero] at h0
          exact h0
        · exact .inl hg)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hl ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

theorem typedProgX_eqP (pub : Lvm.Pub) : typedProgX Ti pub =
    zeroProgX.bind fun z ↦ (wireProgX Ti pub z.2).bind fun w ↦ (relayProg Ti w.1 (w.2.2.getD 1 0)).bind fun r ↦
      (accProgQX Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1).bind
        fun _ ↦ (miniBusProg Ti).bind fun cl ↦ VerifierProgram.ret (typedClaims Ti w.1 w.2.2 r.1 r.2 cl) := by
  unfold typedProgX; rfl

/-- **The typed phases on a fixed candidate set**, coordinate-split. -/
noncomputable def typedSpecInX (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsX) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (hfin : S.Finite) {T : ℝ≥0∞} (herr : TErrsX L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProgX Ti pub)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ (WiringRelX Ti.Q Ti.lay (Ti.zOf L pub p.1 p.2) ∧
          M3Holds (inst L Ti.mbT hτL) () (stackOf L p.1 p.2)) ∧ R p ∧
          PhiQX Ti.Q Ti.lay (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadTX L₀) T := by
  obtain ⟨he, hTz, hLacc, hD, hTm, hab, he4, hTl, hlam, he3, hTf, hxi⟩ := herr.facts
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  rw [typedProgX_eqP]
  refine (((zeroSpecTX Ti L pub hτL R S hS he hTz).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.2 fun q hq ↦ ⟨⟨wiringRelX_of_zeroOn _ _ hTi.1 _ hq.1, hq.2.1⟩, hq.2.2.1,
      hq.2.2.2⟩, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun z ↦ ?_
  refine ((wireSpecTX Ti L pub hτL R S hS hTi he z).frame _ (hJ _)).bind fun w ↦ ?_
  refine ((relaySpecTX Ti L pub hτL R S hS hTi hmaps hrec he hLacc z w).frame _ (hJ _)).bind fun r ↦ ?_
  exact if hr1 : r.1.length = relayRounds then
    ((accSpecTyX Ti L pub hτL R S hTi hacc hD hTm z w r).frame _ (hJ _)).bind fun _ ↦
      ((miniSpecTy Ti L pub hτL R S hS hfin hsc hlay hkey hw hfix hμ hab he4 hTl hlam he3 hTf (hxi _) w r).mono
        (fun _ hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun cl ↦
        (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h)
          (typedClaims Ti w.1 w.2.2 r.1 r.2 cl)).mono
          (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ by
            obtain ⟨⟨h1, h2⟩, hR⟩ := hq
            refine ⟨blockHolds_mini L hlay hp.1
                (fun c hc ↦ h1 c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
                (fun c hc ↦ h2 c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))), ⟨?_, ?_, ?_, ?_⟩, hR⟩
            · exact ((holds_relayPoint L hrec r.1 hr1 r.2 q.2).mp (h1 _ (List.mem_cons_self ..))).symm
            · exact ((holds_com Ti L pub hTi hmaps q.1 q.2 w.1 _).mp (h2 _ (List.mem_cons_self ..))).symm
            · exact ((holds_sigma Ti L pub hTi hmaps q.1 q.2 w.1 _).mp
                (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).symm
            · exact ((holds_ks Ti L pub hTi hmaps q.1 q.2 w.1 _).mp
                (h2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).symm)
          (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hr1 hp.1.2.2.2.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

end Phases

/-- **`typedSpecX` on the restated program** (statement 12's proof; `Spec.glue` over the candidate sets). -/
noncomputable def typedSpecXP (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVarsX) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrsX L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProgX Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ (WiringRelX Ti.Q Ti.lay (Ti.zOf L pub p.1 p.2) ∧
          M3Holds (inst L Ti.mbT hτL) () (stackOf L p.1 p.2)) ∧ R p ∧
          PhiQX Ti.Q Ti.lay (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadTX L₀) T :=
  (Lvm.M3.Spec.glue (ι := {S : Set (Column L.nuMain × Column L.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecInX Ti L pub hτL R S.1 S.2.2 hTi hmaps hrec hacc hsc hlay hkey hw hfix hμ S.2.1 herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

end Lvm.Typed
