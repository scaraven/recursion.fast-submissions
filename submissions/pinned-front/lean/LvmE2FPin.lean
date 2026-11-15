-- New for lvm2 slice S1 (E2-F, E2F-LEAD freeze 2026-11-13): the root OOD pin of `C_main` (E2AC-DES §1.3,
-- E2-S-switch §7). Definitions are final; the `sorry`s are frozen statements (owner: E2F-LEAD). A proof never
-- changes its statement; a needed change is reported old → new.
import LvmMPCert
import LvmMPMidT
import LvmCertSMid3Blk

/-!
# The root OOD pin (statements 1–3 of E2AC-DES §6)

M′ runs its middle phases under `C_main`'s whole list (`candM`, at most 124 members), so an `E2` group would pay
`124 · c · 2^-g / 2^128`. The pin samples one out-of-domain point `z ∈ E^23` right after the root's cap and reads
the claimed value `a = C̃_main(z)`. The list members consistent with `(z, a)` number at most one, except with
probability `C(124, 2) · 23 / |E|` (Schwartz–Zippel on the pairs, `LvmWhirOod.card_ood_collision_le`). The middle
phases then run under `candZ (z, a)`, which has at most one element **by construction** (empty if two or more
members are consistent), so their specs hold at `L₀ = 1`. The members outside `candZ` fail the pin's claim, which
is the first claim of the opening's list.

* `pinProg`, `pinClaim`, `PinOK`, **`candZ`** (statement 1): `candZ_subsingleton`, `candZ_ncard_le`, `candZ_stable`;
* `PinPost`, **`pin_escape`** (statement 2): the pin's spec from `RootShapeM`, lead `errE (C(124,2)·23) + T`;
* `PinOut`, **`pinOut_of_post`**, **`pinOut_append`** (statement 3, the `Stable` invariant through `mid`),
  `MidPostZ`, **`openPostP_of`** (`OpenPostM` with the pin's claim first);
* `midP` (the pin, then the middle phases, the pin's claim first), `MidSpecPin` (the middle phases' obligation at
  `candZ`), consumed by `LvmE2FCert`.
-/

set_option autoImplicit false

namespace Lvm.E2F

open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front (Stable)
open scoped NNReal ENNReal

/-! ## Statement 1: the pin and its candidate set -/

/-- **The root OOD pin**: `ν = 23` challenges (the point `z`, coordinate `0` first), then one prover scalar (the
claimed `C̃_main(z)`). -/
def pinProg : VerifierProgram (List E × E) := do
  let z ← VerifierProgram.sampleChallenges CMain.nu20
  let a ← VerifierProgram.readScalar
  return (z, a)

/-- **The pin's claim** on `C_main`: weight `eq(z, ·)`, value `a`. -/
def pinClaim (za : List E × E) : LeanVM.Protocol.Verifier.StackClaim := (fun x ↦ LeanVM.Protocol.Verifier.eqEval za.1 x, za.2)

/-- The members of `C_main`'s list consistent with the pin. -/
def pinCons (za : List E × E) (h : List Ev) : Set (Column CMain.nu20) :=
  {q | q ∈ candM h ∧ StackClaim.Holds CMain.nu20 (pinClaim za) q}

/-- **The pin succeeded**: at most one member of the list is consistent with it. -/
def PinOK (za : List E × E) (h : List Ev) : Prop := (pinCons za h).Subsingleton

open Classical in
/-- **The middle phases' candidate set**: the consistent members if there is at most one, else none. It has at
most one element whatever the history (`candZ_subsingleton`), as `tapeSpec`'s unconditional `hcard` needs. -/
noncomputable def candZ (za : List E × E) (h : List Ev) : Set (Column CMain.nu20) :=
  if PinOK za h then pinCons za h else ∅

theorem candZ_subsingleton (za : List E × E) (h : List Ev) : (candZ za h).Subsingleton := by
  unfold candZ; split_ifs with hp
  · exact hp
  · exact Set.subsingleton_empty

theorem candZ_ncard_le (za : List E × E) (h : List Ev) : (candZ za h).ncard ≤ 1 :=
  Set.ncard_le_one_iff_subsingleton.mpr (candZ_subsingleton za h)

theorem pinCons_stable (za : List E × E) : Stable (pinCons za) := fun h₀ l hl ↦ by
  simp only [pinCons, Lvm.Typed.candM_stable h₀ l hl]

theorem candZ_stable (za : List E × E) : Stable (candZ za) := fun h₀ l hl ↦ by
  unfold candZ PinOK; rw [pinCons_stable za h₀ l hl]

theorem candZ_sub (za : List E × E) (h : List Ev) : candZ za h ⊆ candM h := by
  unfold candZ; split_ifs
  · exact fun _ hq ↦ hq.1
  · exact Set.empty_subset _

/-! ## Statement 2: the pin's escape -/

/-- **After the pin**: the root's shape, and the pin succeeded. -/
def PinPost (za : List E × E) (h : List Ev) : Prop := RootShapeM h ∧ PinOK za h

/-- The pin group's numerator: `C(124, 2)` pairs of list members times `ν = 23` (Schwartz–Zippel). -/
abbrev pinNum : ℕ := Nat.choose 124 2 * CMain.nu20

/-- **The pin's point separates the list** (a function of the commitments): the root's shape, and at every value
`a` at most one list member is consistent with `(z, a)`: `RootShapeM ∧ ∀ a, PinOK (z, a)` restated over the commitments
(definitionally equal at `commits h`), so that `retExp_commits` applies. -/
def PinSepC (z : List E) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) : Prop :=
  (∃ W, cs = [(19, 64, W)] ∧ WellShaped 64 W) ∧
    ∀ a : E, {q | q ∈ Candidates CMain.nu20 2 thrMain (wordOf cs 0) ∧
      StackClaim.Holds CMain.nu20 (pinClaim (z, a)) q}.Subsingleton

/-- A separating point gives `PinPost` after any read value. -/
theorem pinPost_of_sepC {z : List E} {h : List Ev} (hs : PinSepC z (commits h)) (a : E) :
    PinPost (z, a) h :=
  ⟨hs.1, hs.2 a⟩

/-- The extension table of a column over `E`. -/
noncomputable def colE (q : Column CMain.nu20) : CompPoly.CMlPolynomialEval E CMain.nu20 :=
  CompPoly.CMlPolynomialEval.map (algebraMap K E) q.values

/-- Distinct columns have distinct tables over `E` (`K → E` is injective). -/
theorem colE_injective : Function.Injective colE := by
  rintro ⟨v⟩ ⟨v'⟩ h
  congr 1
  apply Vector.ext
  intro i hi
  have := congrArg (·[i]) h
  simp only [colE, CompPoly.CMlPolynomialEval.map, Vector.getElem_map] at this
  exact (algebraMap K E).injective this

/-- The arithmetic of the OOD count: `|E|^-κ · c·κ·|E|^(κ-1) = errE (c·κ)`. -/
theorem errE_pin_ood (c κ k : ℕ) (hκ : κ = k + 1) :
    (Fintype.card E : ℝ≥0∞)⁻¹ ^ κ * ((c * (κ * Fintype.card E ^ (κ - 1)) : ℕ) : ℝ≥0∞) =
      KeccakGkr.errE (c * κ) := by
  subst hκ
  rw [KeccakGkr.errE, Nat.add_sub_cancel]
  push_cast
  have h1 : (Fintype.card E : ℝ≥0∞)⁻¹ ^ k * (Fintype.card E : ℝ≥0∞) ^ k = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
  calc (Fintype.card E : ℝ≥0∞)⁻¹ ^ (k + 1) * ((c : ℝ≥0∞) * ((k + 1 : ℝ≥0∞) * (Fintype.card E) ^ k))
      = (c : ℝ≥0∞) * (k + 1) * (Fintype.card E : ℝ≥0∞)⁻¹ *
        ((Fintype.card E : ℝ≥0∞)⁻¹ ^ k * (Fintype.card E : ℝ≥0∞) ^ k) := by ring
    _ = _ := by rw [h1, mul_one]

/-- A sum over `κ`-tuples is a sum over vectors (`Ood.vectorEquivFun`). -/
theorem sum_ofFn_eq_vec {κ : ℕ} (g : List E → ℝ≥0∞) :
    ∑ f : Fin κ → E, g (List.ofFn f) = ∑ v : Vector E κ, g v.toList := by
  rw [← (Ood.vectorEquivFun E κ).sum_comp]
  refine Finset.sum_congr rfl fun v _ ↦ congrArg g ?_
  rw [show (Ood.vectorEquivFun E κ v) = fun j ↦ v[j] from rfl]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

open Classical in
/-- **The pin's escape**: from the root's shape, at most `errE pinNum` of the points `z` leave two list members
with equal extensions at `z` (`card_ood_collision_image_le`, `stackClaim_holds_eqEval_iff`). -/
theorem escRet_pin_le (h₀ : List Ev) (hr : RootShapeM h₀) :
    VerifierProgram.escRet (fun z h ↦ PinSepC z (commits h)) h₀ []
      (VerifierProgram.sampleChallenges CMain.nu20) ≤ KeccakGkr.errE pinNum := by
  unfold VerifierProgram.escRet
  rw [retExp_commits (fun z cs ↦ if PinSepC z cs then 0 else 1), List.append_nil, retExp_sampleN]
  have hfin : (candM h₀).Finite := Set.toFinite _
  set L := hfin.toFinset
  have hinj : Set.InjOn colE (L : Set (Column CMain.nu20)) := colE_injective.injOn
  have hsum : ∑ f : Fin CMain.nu20 → E, (if PinSepC (List.ofFn f) (commits h₀) then 0 else 1 : ℝ≥0∞) ≤
      ((Finset.univ.filter fun v : Vector E CMain.nu20 ↦
        ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ CompPoly.CMlPolynomialEval.evalMle (colE U) v =
          CompPoly.CMlPolynomialEval.evalMle (colE U') v).card : ℝ≥0∞) := by
    rw [sum_ofFn_eq_vec (fun z ↦ if PinSepC z (commits h₀) then 0 else 1), Finset.card_filter,
      Nat.cast_sum]
    refine Finset.sum_le_sum fun v _ ↦ ?_
    by_cases hs : PinSepC v.toList (commits h₀)
    · simp only [hs, ↓reduceIte]; exact zero_le
    · simp only [hs, ↓reduceIte]
      have hbad : ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ CompPoly.CMlPolynomialEval.evalMle (colE U) v =
          CompPoly.CMlPolynomialEval.evalMle (colE U') v := by
        have h2 : ¬ ∀ a : E, {q | q ∈ Candidates CMain.nu20 2 thrMain (wordOf (commits h₀) 0) ∧
            StackClaim.Holds CMain.nu20 (pinClaim (v.toList, a)) q}.Subsingleton := fun h2 ↦ hs ⟨hr, h2⟩
        obtain ⟨a, ha⟩ := not_forall.mp h2
        simp only [Set.Subsingleton, Set.mem_ofPred_eq, not_forall] at ha
        obtain ⟨q, ⟨hq, hqa⟩, q', ⟨hq', hqa'⟩, hne⟩ := ha
        refine ⟨q, hfin.mem_toFinset.mpr hq, q', hfin.mem_toFinset.mpr hq', hne, ?_⟩
        exact ((Front.stackClaim_holds_eqEval_iff v a q).mp hqa).trans
          ((Front.stackClaim_holds_eqEval_iff v a q').mp hqa').symm
      simp only [hbad, ↓reduceIte, Nat.cast_one, le_refl]
  have hL : L.card ≤ 124 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]; exact Lvm.Typed.candM_ncard_le h₀
  have hN : (Finset.univ.filter fun v : Vector E CMain.nu20 ↦
      ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ CompPoly.CMlPolynomialEval.evalMle (colE U) v =
        CompPoly.CMlPolynomialEval.evalMle (colE U') v).card ≤
      Nat.choose 124 2 * (CMain.nu20 * Fintype.card E ^ (CMain.nu20 - 1)) :=
    (card_ood_collision_image_le L colE hinj).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hL))
  calc (Fintype.card E : ℝ≥0∞)⁻¹ ^ CMain.nu20 * ∑ f : Fin CMain.nu20 → E, _
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ ^ CMain.nu20 *
        ((Nat.choose 124 2 * (CMain.nu20 * Fintype.card E ^ (CMain.nu20 - 1)) : ℕ) : ℝ≥0∞) := by
        gcongr; exact hsum.trans (by exact_mod_cast hN)
    _ = _ := errE_pin_ood _ _ 22 rfl

/-- `C(124,2)·23 = 175,398 ≤ 2^63`. -/
theorem pinNum_le : pinNum ≤ 2 ^ 63 := by
  rw [pinNum, Nat.choose_two_right]; norm_num

/-- The pin's escape is below `1` (`Spec.ofNoMove`'s side condition). -/
theorem errE_pinNum_lt_one : KeccakGkr.errE pinNum < 1 :=
  (errE_le_εS pinNum_le).trans_lt εS_lt_one

/-- **Statement 2 (`pin_escape`)**: the pin's spec. From the root's shape, the pin ends with at most one consistent
list member except with probability `errE pinNum = C(124,2)·23/|E| ≈ 2^-174.6`; the lead is that plus the
follower's. -/
theorem pin_escape (T : ℝ≥0∞) (hT : T ≤ εS) :
    Nonempty (Spec pinProg RootShapeM PinPost εS (LeanVM.Protocol.KeccakGkr.errE pinNum + T) T) :=
  ⟨((Spec.ofNoMove (p := VerifierProgram.sampleChallenges CMain.nu20) (Pre := RootShapeM)
      (Post := fun z h ↦ PinSepC z (commits h)) (εmax := εS) (T := 0) (noMoves_sampleN _).noMove
      errE_pinNum_lt_one escRet_pin_le).bind' fun z ↦
    (Spec.readE (Pre := fun h ↦ PinSepC z (commits h)) (Post := fun a h ↦ PinPost (z, a) h)
      (fun h₀ a hs ↦ pinPost_of_sepC (by rw [commits_append]; simpa [commits] using hs) a) hT).bind'
      fun a ↦ Spec.ret (Post := PinPost) (z, a)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
    (by rw [add_zero]; exact le_self_add) le_rfl⟩

/-! ## Statement 3: the members outside `candZ` fail the pin's claim -/

/-- **The invariant**: every list member outside `candZ` fails the pin's claim. -/
def PinOut (za : List E × E) (h : List Ev) : Prop :=
  ∀ q ∈ candM h, q ∉ candZ za h → ¬ StackClaim.Holds CMain.nu20 (pinClaim za) q

/-- The pin's postcondition gives the invariant. -/
theorem pinOut_of_post {za : List E × E} {h : List Ev} (hp : PinOK za h) : PinOut za h := by
  intro q hq hz hh
  exact hz (by unfold candZ; rw [if_pos hp]; exact ⟨hq, hh⟩)

/-- **The invariant is `Stable`**: it survives every history extension that commits nothing (the middle phases
commit nothing: `MidShapeM.noCommit`). -/
theorem pinOut_append {za : List E × E} {h₀ : List Ev} (l : List Ev) (hl : commits l = [])
    (hI : PinOut za h₀) : PinOut za (h₀ ++ l) := by
  intro q hq hz
  rw [Lvm.Typed.candM_stable h₀ l hl] at hq
  rw [candZ_stable za h₀ l hl] at hz
  exact hI q hq hz

/-- **The middle phases' postcondition at `candZ`**: every non-good member of `candZ` fails a claim; the root's
shape; multiaffine claims, fewer than `2^40`. -/
def MidPostZ (Good : GoodRelM) (x : List UInt8) (za : List E × E)
    (cl : List LeanVM.Protocol.Verifier.StackClaim) (h : List Ev) : Prop :=
  (∀ q ∈ candZ za h, ¬ Good x q → ∃ c ∈ cl, ¬ StackClaim.Holds CMain.nu20 c q) ∧
  RootShapeM h ∧ (∀ c ∈ cl, IsMultiaffine CMain.nu20 c.1) ∧ cl.length < 2 ^ 40

/-- **Statement 3 (`openPostP_of`)**: the invariant and the middle phases' postcondition at `candZ` give M′'s
`OpenPostM` for the list with the pin's claim first. -/
theorem openPostP_of {Good : GoodRelM} {x : List UInt8} {za : List E × E}
    {cl : List LeanVM.Protocol.Verifier.StackClaim} {h : List Ev}
    (hI : PinOut za h) (hm : MidPostZ Good x za cl h) : OpenPostM Good x (pinClaim za :: cl) h := by
  obtain ⟨hz, hr, ha, hlen⟩ := hm
  refine ⟨fun q hq hg ↦ ?_, hr, ?_, by simp only [List.length_cons]; omega⟩
  · by_cases hqz : q ∈ candZ za h
    · obtain ⟨c, hc, hn⟩ := hz q hqz hg
      exact ⟨c, List.mem_cons_of_mem _ hc, hn⟩
    · exact ⟨pinClaim za, List.mem_cons_self, hI q hq hqz⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.ASM.isMultiaffine_eqEvalN _ _
    · exact ha c hc

/-! ## The pinned middle phases -/

/-- **The middle phases after the pin**: the pin, then `mid`, the pin's claim first in the list. -/
def midP (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8) :
    VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim) := do
  let za ← pinProg
  let cl ← mid x
  return pinClaim za :: cl

/-- **Obligation `MidSpecPin`**: from the pin's postcondition, the middle phases end in `MidPostZ` at `candZ`,
every group's escape at most `εm`, lead `Lm`, for every follower's allowance `T ≤ εm`. The candidate set has at
most one element, so every front group is priced at `L₀ = 1`. -/
def MidSpecPin (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (Good : GoodRelM)
    (εm Lm : ℝ≥0∞) : Prop :=
  ∀ x (za : List E × E) (T : ℝ≥0∞), T ≤ εm →
    Nonempty (Spec (mid x) (PinPost za) (MidPostZ Good x za) εm Lm T)

end Lvm.E2F
