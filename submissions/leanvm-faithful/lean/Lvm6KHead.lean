-- New for lvm6 K1: rows 6–9 of `FORMAT6.md` §6.2 (`kHead6`) in the doom calculus: the start group
-- `G(3) D(5)`, `c_st`, leanVM's first claim, 12 layers, the middle-state opening on slots `base + ℓ`.
import Lvm6KGroup
import Lvm6KStmt
import Lvm6KLayer
import LvmE2VKec

/-!
# The head of a v6 Keccak reduction

* the middle-state opening's algebra: `wmF` (slice-0 weight of slot `o`), `WmF`, `QmF`, `FmF`;
  `FmF_nil` (before the slot rounds: `OpenTrueV`'s value with the middle state on slots `base + ℓ`),
  `WmF_eq` (`midWt`), `QmF_full` (the column at `(inst, ϱ)`);
* `grp_le`: a group of numerator `c` at `g` bits with one candidate fits `εS`;
* **`headSpec`**: `kHead6 P base inst output` from doom of season 1's start claims
  (`outClaimsTrueMidV`, `midAgreeV`) on any inputs `I` whose segment-1 lanes are the table's slots
  `base + ℓ`, to doom of "the claim after the layers holds of `I` and the middle word claim holds".
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (States Shape statesOfS laneWord segStateS)
open Lvm.E2V Lvm6.KPack
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-! ## The middle-state opening's algebra -/

/-- The slice-0 weight of slot `o` (`open(first, 1, 1, ·)` on slots `base + ℓ`). -/
def wmF (base : ℕ) (rseg : E2) (rlane : List E2) (o : ℕ) : E2 :=
  if base ≤ o ∧ o < base + 25 then (1 + rseg) * eqAtF rlane (o - base) else 0

/-- The weights extended over the slot bits. -/
def WmF (base : ℕ) (rseg : E2) (rlane pt : List E2) : E2 :=
  ∑ o ∈ range (2 ^ 6), eqAtF pt o * wmF base rseg rlane o

/-- The table's slots at the steps' point `inst`, extended over the slot bits. -/
def QmF (h : ℕ) (col : ℕ → K) (inst pt : List E2) : E2 :=
  ∑ o ∈ range (2 ^ 6), eqAtF pt o * stepMleK h inst (fun x ↦ col (x + 2 ^ h * o))

/-- The middle-state opening's family. -/
def FmF (h : ℕ) (col : ℕ → K) (inst : List E2) (base : ℕ) (rseg : E2) (rlane acc : List E2) : E2 :=
  cubeSumF (fun pt ↦ WmF base rseg rlane pt * QmF h col inst pt) 6 acc

theorem FmF_plain {β : Type} (h : ℕ) (col : β → ℕ → K) (inst : List E2) (base : ℕ) (rseg : E2)
    (rlane : List E2) : PlainFamilyF (fun q acc ↦ FmF h (col q) inst base rseg rlane acc) 2 6 :=
  cube_plainFamilyF (fun q pt ↦ WmF base rseg rlane pt * QmF h (col q) inst pt) 6
    fun _ pre post ↦ polyLEF_mle_mul _ _ _ _ pre post

/-- A sum over the 64 slots of a function supported on the window `base … base + 24`. -/
theorem sum_window {base : ℕ} (hb : base + 25 ≤ 64) (f : ℕ → E2) :
    ∑ o ∈ range (2 ^ 6), (if base ≤ o ∧ o < base + 25 then f o else 0) =
      ∑ l ∈ range 25, f (base + l) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ 6 = base + (25 + m) := ⟨39 - base, by norm_num; omega⟩
  rw [hm, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ o ∈ range base, (if base ≤ o ∧ o < base + 25 then f o else 0) = 0 :=
    Finset.sum_eq_zero fun o ho ↦ by rw [if_neg (by have := Finset.mem_range.1 ho; omega)]
  have h3 : ∑ o ∈ range m, (if base ≤ base + (25 + o) ∧ base + (25 + o) < base + 25 then
      f (base + (25 + o)) else 0) = 0 :=
    Finset.sum_eq_zero fun o _ ↦ by rw [if_neg (by omega)]
  rw [h1, h3, zero_add, add_zero]
  exact Finset.sum_congr rfl fun l hl ↦ by
    rw [if_pos (by have := Finset.mem_range.1 hl; omega)]

theorem FmF_nil (h : ℕ) (col : ℕ → K) (inst : List E2) {base : ℕ} (hb : base + 25 ≤ 64)
    (rseg : E2) (rlane : List E2) :
    FmF h col inst base rseg rlane [] =
      (1 + rseg) * ∑ l ∈ range 25, eqAtF rlane l * stepMleK h inst (fun x ↦ col (x + 2 ^ h * (base + l))) := by
  rw [FmF, cubeSumF_nil]
  have hu : ∀ u ∈ range (2 ^ 6), WmF base rseg rlane (bitsF u 6) * QmF h col inst (bitsF u 6) =
      (if base ≤ u ∧ u < base + 25 then (1 + rseg) * eqAtF rlane (u - base) *
        stepMleK h inst (fun x ↦ col (x + 2 ^ h * u)) else 0) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [WmF, QmF, sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu', wmF]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hu, sum_window hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Nat.add_sub_cancel_left]; ring

theorem WmF_eq {base : ℕ} (hb : base + 25 ≤ 64) (rseg : E2) (rlane pt : List E2) :
    WmF base rseg rlane pt = midWt base rseg rlane pt := by
  rw [WmF, midWt]
  have : ∀ o, eqAtF pt o * wmF base rseg rlane o =
      if base ≤ o ∧ o < base + 25 then (1 + rseg) * (eqAtF pt o * eqAtF rlane (o - base)) else 0 := by
    intro o; rw [wmF]; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun o _ ↦ this o, sum_window hb, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [Nat.add_sub_cancel_left]

theorem QmF_full {h : ℕ} (col : ℕ → K) {inst pt : List E2} (ha : inst.length = h)
    (hpt : pt.length = 6) : QmF h col inst pt = stepMleK (h + 6) (inst ++ pt) col := by
  rw [stepMleK, ← hpt, col_splitF ha, QmF, hpt]
  rfl

/-! ## Groups within `εS` -/

theorem errG_zero_one : errG 0 1 = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by simp [errG]

/-- A group of `c` draws with escape `errG 0 1` each, after a `g`-bit grind, fits `εS`. -/
theorem grp_le {c g : ℕ} (h : grpEps 1 c g ≤ epsS) :
    (2 : ℝ≥0∞)⁻¹ ^ g * ((c : ℕ) * errG 0 1) + 0 ≤ εS := by
  have := errG_le_εS h
  rw [errG_zero_one]
  rwa [Nat.cast_one, one_mul, errG] at this

theorem εS_lt_one : εS < 1 := by
  rw [εS, epsS_eq]; exact ENNReal.ofReal_lt_one.2 (by unfold epsS; norm_num)

theorem grp_lt {c g : ℕ} (h : grpEps 1 c g ≤ epsS) : (2 : ℝ≥0∞)⁻¹ ^ g * ((c : ℕ) * errG 0 1) < 1 :=
  lt_of_le_of_lt ((le_of_eq (add_zero _).symm).trans (grp_le h)) εS_lt_one

/-! ## The head in the doom calculus -/

variable {β : Type} {C : List Ev → Set β} [Finite β]

/-- What the head leaves: the lengths, and doom of "the claim after the layers holds of the inputs
`I` and the middle word claim holds". -/
abbrev HeadPost (P : ℕ) (I : β → ℕ → ℕ → KeccakState) (col : β → ℕ → K) (R : β → Prop)
    (inst : List E2) (out : HeadOut) (hist : List Ev) : Prop :=
  out.sl.length = 6 ∧ ClaimShapeF P out.claim ∧ out.ϱm.length = 6 ∧
    Doomed C (fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (I q) 12) P out.claim ∧
      stepMleK (P + 4 + 6) (inst ++ out.ϱm) (col q) = out.cout ∧ R q) hist

/-- `kHead6` with `c_st`'s read and the layers' shape written out. -/
def kHead6Flat (P base : ℕ) (inst output : List E2) : VerifierProgram HeadOut :=
  gPoint gSeg 5 >>= fun sl ↦
  VerifierProgram.readScalar >>= fun c ↦
  layers6Sh Shape.v1 (Shape.v1.logSteps P) (List.range' 0 (11 + 1))
    (firstClaimSF Shape.v1 inst (sl.take 1) (sl.drop 1) output (e2OfE c)) >>= fun claim ↦
  sumcheckE2 gC2 (e2OfE c) 3 (List.replicate 6 none) >>= fun om ↦
  e2Read >>= fun cout ↦
  VerifierProgram.require (midWt base (sl.headD 0) (sl.drop 1) om.1 * cout = om.2) >>= fun _ ↦
  pure ⟨sl, e2OfE c, claim, om.1, cout⟩

theorem kHead6_flat (P base : ℕ) (inst output : List E2) :
    kHead6 P base inst output = kHead6Flat P base inst output := by
  have h : List.range 12 = List.range' 0 (11 + 1) := by rw [List.range_eq_range']
  simp only [kHead6, kHead6Flat, layers6_eq, h]
  rfl

theorem take_one_eq {sl : List E2} (h : sl.length = 6) : sl.take 1 = [sl.headD 0] := by
  match sl, h with
  | a :: _, _ => rfl

open Classical in
/-- **Rows 6–9** (`kHead6`): from doom of the start claims at `inst` on the inputs `I` (segment 1's
lanes are the table's slots `base + ℓ`) to `HeadPost`. Lead `0`; groups: the start `G(3) D(5)`
(numerator 6), the layers', the six slot rounds `(2, 2)`; the follower's `T` after `c_out`. -/
noncomputable def headSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (I : β → ℕ → ℕ → KeccakState) (col : β → ℕ → K) (P base : ℕ) (hb : base + 25 ≤ 64)
    (hI : ∀ q x, ∀ l < 25, laneWord (I q 1 x) l = col q (x + 2 ^ (P + 4) * (base + l)))
    {inst output : List E2} (hi : inst.length = P + 4) (ho : output.length = 25) {T : ℝ≥0∞}
    (hT : T ≤ εS) :
    Spec (kHead6 P base inst output)
      (Doomed C (fun q ↦ outClaimsTrueMidV (P + 4) (I q) inst output ∧
        midAgreeV (P + 4) (I q) inst ∧ R q))
      (HeadPost (C := C) P I col R inst) εS 0 T :=
  Spec.congr (kHead6_flat P base inst output).symm <|
  let δ : β → ℕ → E2 := fun q ↦ startDeltaV (P + 4) (I q) inst output
  ((gPointSpec (T := 0) hst hcard (g := gSeg) (by norm_num) 5 (ZeroAliveF δ R 6) (errG 0 1)
      (fun acc q hq ↦ zeroAliveG_escape (g := 0) (by norm_num) δ R 6 acc q hq)
      εS_lt_one (grp_le (by unfold grpEps epsS; norm_num))).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨_, hz, hR⟩ ↦ by
      obtain ⟨h1, h2⟩ := claims_of_zeroOnV (P + 4) (I q) inst output hz
      exact ⟨h1, h2, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sl ↦
  if hsl : sl.length = 6 then
    have hs : (sl.take 1).length = 0 + 1 := by simp [hsl]
    have hl : (sl.drop 1).length = 4 + 1 := by simp [hsl]
    ((doomRead (T := 0) hst (fun q ↦ ZeroAliveF δ R 6 sl q) zero_le).mono (fun _ hd ↦ hd.2)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦
    ((layersSpec6 (T := 0) Shape.v1_ok hst hcard
        (fun q ↦ OpenTrueV (P + 4) (I q) inst (sl.take 1) (sl.drop 1) (e2OfE c) ∧ R q)
        I P errG_c2' 11 0 rfl _ (firstClaimSV_shape (e2OfE c) hi hs)).mono
      (fun _ hd ↦ Doomed.mono hd fun q ⟨hct, hop, hR⟩ ↦
        ⟨hsl.le, by
          have := zeroOn_of_firstV P (I q) hi hs hl ho _ hop hct
          rwa [List.take_append_drop] at this, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun claim ↦
    if hc : ClaimShapeF P claim then
      let R' : β → Prop := fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (I q) 12) P claim ∧ R q
      ((sumcheckGSpec (T := 0) hst hcard R' (FmF_plain (P + 4) col inst base (sl.headD 0) (sl.drop 1))
          (count := 3) (by norm_num) (by norm_num) (g := gC2) (by norm_num) errG_c2 6 [] (e2OfE c)
          (by simp)).mono
        (fun _ (hd : ClaimShapeF P claim ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hct, hR⟩ ↦
          ⟨hct, by
            have hsum : ∑ l ∈ range 25, eqAtF (sl.drop 1) l *
                stepMleK (P + 4) inst (fun x ↦ col q (x + 2 ^ (P + 4) * (base + l))) =
                ∑ l ∈ range 25, eqAtF (sl.drop 1) l *
                stepMleK (P + 4) inst (fun x ↦ laneWord (I q 1 x) l) :=
              Finset.sum_congr rfl fun l hl' ↦ by
                rw [show (fun x ↦ col q (x + 2 ^ (P + 4) * (base + l))) =
                  (fun x ↦ laneWord (I q 1 x) l) from
                    funext fun x ↦ (hI q x l (Finset.mem_range.1 hl')).symm]
            rw [OpenTrueV, hv, FmF_nil (P + 4) (col q) inst hb, hsum, take_one_eq hsl]
            simp [eqAtF], hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun om ↦
      if hom : om.1.length = 6 then
        ((e2ReadSpec (T := T) hst _ hT).mono (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl
          le_rfl).bind' fun cout ↦
        (Spec.require
          (Pre := Doomed C (fun q ↦ om.2 = FmF (P + 4) (col q) inst base (sl.headD 0) (sl.drop 1)
            ([] ++ om.1) ∧ R' q))
          (Post := fun _ h ↦ Doomed C (fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (I q) 12) P claim ∧
            stepMleK (P + 4 + 6) (inst ++ om.1) (col q) = cout ∧ R q) h)
          fun _ hd hcheck ↦ Doomed.mono hd fun q ⟨hct, hcol, hR⟩ ↦ ⟨by
            rw [List.nil_append, FmF, cubeSumF_full _ hom, ← hcheck, WmF_eq hb,
              QmF_full _ hi hom, hcol], hct, hR⟩).bind' fun _ ↦
        (Spec.ret (Post := HeadPost (C := C) P I col R inst)
          (⟨sl, e2OfE c, claim, om.1, cout⟩ : HeadOut)).mono
          (fun _ hd ↦ ⟨hsl, hc, hom, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ hom hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hsl hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm6.K

/-! ## The tree batch's inputs -/

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics
open LeanVM.Protocol.KeccakGkr (laneWord)

/-- **The tree batch's GKR inputs**: segment 0 is the input map of the slots (`inTree`, not
committed), segment 1 the committed middle state (`midTree`, slots `8 … 32`). -/
def Itree (κ : ℕ) (q : Stack) (m x : ℕ) : KeccakState := if m = 0 then inTree κ q x else midTree κ q x

theorem laneWord_Itree_one (κ : ℕ) (q : Stack) (x : ℕ) {l : ℕ} (hl : l < 25) :
    laneWord (Itree κ q 1 x) l = q (x + 2 ^ κ * (8 + l)) := by
  rw [Itree, if_neg one_ne_zero, laneWord, midTree, LeanVM.Protocol.KeccakGkr.lane_eq _ hl,
    Vector.getElem_ofFn]
  rfl

end Lvm6.K
