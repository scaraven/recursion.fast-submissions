-- New for lvm2 S1 (E2-F, E2F-V), E2AC-DES §6 statements 6 and 7 (tape, wire, slots): the `E2` front's tape
-- caller in the doom calculus at `L₀ = 1` (the root pin's `candZ`), every group `≤ εS = 7·2^-131` with
-- S2GF's grinding (`(c, g)` = (1,1) (2,2) (3,2) (46,6)).
import LvmE2VProg
import LvmE2VWireAlg
import LvmE2VWireKer
import LvmE2VZero
import LvmE2VGkrSpec
import LvmKeccakCallerTape
import LvmCertSNoGen

/-!
# The tape caller at `E2`, round by round

Candidates `C` with `Stable C` and at most one element (`Lvm.E2F.candZ`); `εmax = εS`. The claims'
meaning at `E2` (`F`-generic, used at `E2`):
* `stepMleE2 w pt f = Σ_{x<2^w} eq(pt, x)·f(x)` (the word claim of a `K` column at an `E2` point);
* `claimSumF`/`ClaimTrueE2`: the GKR's claims on the states (`LvmKeccakLayerAlg.claimSum`);
* `InClaimTrueE2`: the GKR's input claim on the virtual chain inputs (`LvmWireSpec.InClaimTrue`);
* `slotSumE2`: a block's slot sum (`LvmWireSpec.slotSum`).

Statements (each a `Spec` at `εS`; the group bounds are `errG g c ≤ εS`, E2-S's `table_min`):
* **`tapeGkrSpecE2`** (6): the `24 × 1` GKR, lanes `c = 1`, per layer `s` (46), 16 pack and 11
  position rounds (3), `β` (2); lead `0` (every challenge follows its nonce);
* **`slotSpecE2`** (7): `b` slot rounds (2), the slices, the row switch (`rowSwitchSpec`);
* **`wireSpecE2`** (7): the chain wiring's `w` rounds (2), `g_D`, then `D`'s slot reduction;
* **`tapeSpecE2`** (6): the caller: the separator, `r` (`w` coordinates, 1), 25 scalars, the GKR,
  `n`'s range, the wiring; from doom of `TapeOut` to doom of the row claim on `C_main` and the four
  tied lanes' `E2` word claims.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (States stAt laneWord tapeStates sbit errE Shape)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.KG (TapeOut dOf chainIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-! ## Claims at `E2` -/

section Claims

variable {F : Type} [Field F] [Algebra K F]

/-- A `K` table's word claim at an `F` point: `Σ_{x<2^w} eq(pt, x)·f(x)`. -/
def stepMleF (w : ℕ) (pt : List F) (f : ℕ → K) : F := ∑ x ∈ range (2 ^ w), eqAtF pt x * kF (f x)

-- `claimSumF`, `ClaimTrueF`, `ClaimShapeF` (the GKR's claims on the states) moved verbatim to
-- `LvmE2VGkrLayer` (imported through `LvmE2VGkrSpec`), so the shape-generic layer specifications can
-- state them.

/-- `⟨ω, a⟩` on a state's bits (`omegaDot`). -/
def omegaDotF (ω : List F) (a : KeccakState) : F := ∑ j ∈ range 1600, ω.getD j 0 * bitF (sbit a j)

/-- **The GKR's input claim** on the virtual inputs (`InClaimTrue`). -/
def InClaimTrueF (lg : ℕ) (inp : ℕ → KeccakState) (claim : KClaim F) : Prop :=
  claim.value = ∑ i ∈ range (2 ^ lg), iotaF claim.point claim.mu i * omegaDotF claim.weights (inp i)

/-- A block's bit slices at `pt` (`slotSlice`). -/
def slotSliceF (k b blk : ℕ) (col : ℕ → K) (pt : List F) (o z : ℕ) : F :=
  ∑ x ∈ range (2 ^ k), eqAtF pt x * bitF ((col (x + 2 ^ k * (o + 2 ^ b * blk))).toBitVec.getLsbD z)

/-- The slot weights paired with the block's slices (`slotSum`). -/
def slotSumF (k b blk : ℕ) (W : ℕ → ℕ → F) (col : ℕ → K) (pt : List F) : F :=
  ∑ o ∈ range (2 ^ b), ∑ z ∈ range 64, W o z * slotSliceF k b blk col pt o z

/-- T1's tied claims at `E2`: `D̃_l(r) = a_l` for the four digest lanes (`TiedD`). -/
def TiedDF (w : ℕ) (D : ℕ → ℕ → K) (r v : List F) : Prop :=
  ∀ l < 4, stepMleF w r (fun x ↦ D x l) = v.getD l 0

end Claims

/-- The row switch's lead at one candidate. -/
theorem rowLead_eq (T : ℝ≥0∞) :
    (∑ _i ∈ range 7, ((1 : ℕ) : ℝ≥0∞) * errE 1) + T = (∑ _i ∈ range 7, errE 1) + T := by
  simp only [Nat.cast_one, one_mul]

/-! ## The slot family at `F` -/

section SlotAlg

variable {F : Type} [Field F]

/-- The slot rounds' family (`slotF`): `Σ_z W̃_z(τ)·S̃_z(pt, τ)` over the slot bits not bound. -/
def slotFF (k b blk : ℕ) (W : ℕ → ℕ → F) (col : ℕ → K) (pt acc : List F) : F :=
  cubeSumF (fun τ ↦ ∑ z ∈ range 64, slotWF b W τ z *
    ∑ o ∈ range (2 ^ b), eqAtF τ o * slotSliceF k b blk col pt o z) b acc

theorem slotWF_eq (b : ℕ) (W : ℕ → ℕ → F) (τ : List F) (z : ℕ) :
    slotWF b W τ z = ∑ o ∈ range (2 ^ b), eqAtF τ o * W o z := by
  rw [slotWF, sumF_map_range]

theorem slotFF_plain {β : Type} (k b blk : ℕ) (W : ℕ → ℕ → F) (col : β → ℕ → K) (pt : List F) :
    PlainFamilyF (fun q acc ↦ slotFF k b blk W (col q) pt acc) 2 b :=
  cube_plainFamilyF _ b fun q pre post ↦ PolyLEF.sum _ fun z _ ↦
    (polyLEF_mle_mul (fun o ↦ W o z) (fun o ↦ slotSliceF k b blk (col q) pt o z) _ _ pre post).congr
      fun x ↦ by rw [slotWF_eq]

theorem slotFF_end (k b blk : ℕ) (W : ℕ → ℕ → F) (col : ℕ → K) (pt : List F) {τ : List F}
    (hτ : τ.length = b) :
    slotFF k b blk W col pt τ = ∑ z ∈ range 64, slotWF b W τ z *
      ∑ o ∈ range (2 ^ b), eqAtF τ o * slotSliceF k b blk col pt o z := by
  rw [slotFF, cubeSumF_full _ hτ]

variable [CharP F 2]

theorem slotFF_nil (k b blk : ℕ) (W : ℕ → ℕ → F) (col : ℕ → K) (pt : List F) :
    slotFF k b blk W col pt [] = slotSumF k b blk W col pt := by
  rw [slotFF, cubeSumF_nil, slotSumF]
  refine Finset.sum_congr rfl fun u hu ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [slotWF_eq, sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu']

/-- **The slices of a block** (`sliceExt_slot`): the column's slice claims at `(pt, τ, sel(blk))`
are the block's slices at `pt` weighted by `eq(τ, ·)`. -/
theorem slices_slotF {k b sb blk : ℕ} (hblk : blk < 2 ^ sb) (col : ℕ → K) {pt τ : List F}
    (hpt : pt.length = k) (hτ : τ.length = b) (i : ℕ) :
    ∑ n ∈ range (2 ^ (pt ++ τ ++ selPtF blk sb).length),
        (if (col n).toBitVec.getLsbD i then eqAtF (pt ++ τ ++ selPtF blk sb) n else 0) =
      ∑ o ∈ range (2 ^ b), eqAtF τ o * slotSliceF k b blk col pt o i := by
  have hite : ∀ n, (if (col n).toBitVec.getLsbD i then eqAtF (pt ++ τ ++ selPtF blk sb) n else 0) =
      eqAtF (pt ++ (τ ++ selPtF blk sb)) n * bitF ((col n).toBitVec.getLsbD i) := by
    intro n
    rw [List.append_assoc]
    unfold bitF
    split_ifs <;> simp
  have hsl : (pt ++ τ ++ selPtF blk sb).length = k + (τ ++ selPtF blk sb).length := by
    simp [hpt]
  rw [Finset.sum_congr rfl fun n _ ↦ hite n, hsl, col_splitF hpt]
  have e2 := col_splitF (h := b) (a := τ) (s := (selPtF blk sb : List F)) hτ
    (fun o ↦ ∑ x ∈ range (2 ^ k), eqAtF pt x * bitF ((col (x + 2 ^ k * o)).toBitVec.getLsbD i))
  rw [show (selPtF blk sb : List F).length = sb by simp [selPtF]] at e2
  have hl2 : (τ ++ (selPtF blk sb : List F)).length = b + sb := by simp [hτ, selPtF]
  rw [hl2, e2, selPtF_eq_bitsF, sum_eqAtF_bitsF hblk]
  rfl

end SlotAlg

/-! ## The wiring identity and family at `F` -/

section WireAlg

variable {F : Type} [Field F]

theorem padDotF_eq (ω : List F) (y : ℕ → Bool) :
    padDotF ω y = ∑ j ∈ range 1600, ω.getD j 0 * bitF (Lvm.KG.pad43Bit y j) := by
  rw [padDotF, sumF_map_range]

theorem omegaDotF_pad43 (ω : List F) (y : ℕ → Bool) :
    omegaDotF ω (Lvm.KG.pad43St y) = padDotF ω y := by
  rw [padDotF_eq]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [← Lvm.KG.stBit_eq_sbit _ hj', Lvm.KG.pad43St, Lvm.KSponge.stBit_ofBits _ hj']

theorem omegaDotF_zero (ω : List F) : omegaDotF ω Lvm.KSponge.zeroSt = 0 :=
  Finset.sum_eq_zero fun j hj ↦ by
    rw [← Lvm.KG.stBit_eq_sbit _ (Finset.mem_range.1 hj), Lvm.KSponge.stBit_zeroSt, bitF, if_neg
      Bool.false_ne_true, mul_zero]

/-- `Pad43`'s pairing splits into the constant bits and the digest bits. -/
theorem padDotF_split (ω : List F) (y : ℕ → Bool) :
    padDotF ω y = padDotF ω (fun _ ↦ false) + ∑ p ∈ range 256, ω.getD (8 + p) 0 * bitF (y p) := by
  have hj : ∀ j, (bitF (Lvm.KG.pad43Bit y j) : F) = bitF (Lvm.KG.pad43Bit (fun _ ↦ false) j) +
      if 8 ≤ j ∧ j < 264 then bitF (y (j - 8)) else 0 := by
    intro j
    unfold Lvm.KG.pad43Bit
    split_ifs <;> first | omega | simp [bitF]
  rw [padDotF_eq, padDotF_eq, Finset.sum_congr rfl fun j _ ↦ by rw [hj j, mul_add],
    Finset.sum_add_distrib]
  refine congrArg (HAdd.hAdd _) ?_
  rw [show 1600 = 8 + (256 + 1336) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ range 8, ω.getD j 0 * (if 8 ≤ j ∧ j < 264 then (bitF (y (j - 8)) : F) else 0) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [if_neg (by have := Finset.mem_range.1 hj; (clear * - j this; omega)), mul_zero]
  have h3 : ∑ j ∈ range 1336, ω.getD (8 + (256 + j)) 0 *
      (if 8 ≤ 8 + (256 + j) ∧ 8 + (256 + j) < 264 then (bitF (y (8 + (256 + j) - 8)) : F) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by rw [if_neg (by (clear * - j; omega)), mul_zero]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [if_pos (by have := Finset.mem_range.1 hp; (clear * - p this; omega)), Nat.add_sub_cancel_left]

/-- The digest part of a row: `G_D(x) = Σ_{p<256} ω_{8+p}·bit_p(D[x])`. -/
def gDTF (ω : List F) (D : ℕ → ℕ → K) (x : ℕ) : F :=
  ∑ p ∈ range 256, ω.getD (8 + p) 0 * bitF (Lvm.KG.rowBits D x p)

/-- **The wiring identity (chain)** over `F` (`wire_identity_ch`). -/
theorem wire_identity_chF (ρ μ ω : List F) (s : RecursionFast.Digest) {n : ℕ} (D : ℕ → ℕ → K)
    {w : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w) :
    ∑ i ∈ range (2 ^ w), iotaF ρ μ i * omegaDotF ω (chainIn s n D i) =
      iotaF ρ μ 0 * padDotF ω (Lvm.KG.digestBits s) +
        padDotF ω (fun _ ↦ false) * ∑ i ∈ range (n - 1), iotaF ρ μ (i + 1) +
        ∑ x ∈ range (2 ^ w), msKF ρ μ 0 (n - 1) x * gDTF ω D x := by
  have hp := Nat.two_pow_pos w
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ w = M + 1 := ⟨2 ^ w - 1, by (clear * - w n hp; omega)⟩
  have hrow : ∀ x, iotaF ρ μ (x + 1) * omegaDotF ω (chainIn s n D (x + 1)) =
      msKF ρ μ 0 (n - 1) x * (padDotF ω (fun _ ↦ false) + gDTF ω D x) := by
    intro x
    rw [chainIn, if_neg (by (clear * - x n w M; omega)), msKF, Nat.zero_add]
    split_ifs with h1 h2 h2
    · rw [omegaDotF_pad43, padDotF_split, Nat.add_sub_cancel, gDTF]
    · omega
    · omega
    · rw [omegaDotF_zero, mul_zero, zero_mul]
  have hlast : msKF ρ μ 0 (n - 1) M * (padDotF ω (fun _ ↦ false) + gDTF ω D M) = 0 := by
    rw [msKF, if_neg (by (clear * - M n w hn hN hM; omega)), zero_mul]
  have hK : ∑ x ∈ range (2 ^ w), msKF ρ μ 0 (n - 1) x = ∑ i ∈ range (n - 1), iotaF ρ μ (i + 1) := by
    rw [show 2 ^ w = (n - 1) + (2 ^ w - (n - 1)) by (clear * - w n hn hN M hM; omega), Finset.sum_range_add]
    rw [Finset.sum_eq_zero (s := range (2 ^ w - (n - 1))) fun x _ ↦ by rw [msKF, if_neg (by (clear * - n x w M; omega))],
      add_zero]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [msKF, if_pos (by have := Finset.mem_range.1 hi; (clear * - i n w M this; omega)), Nat.zero_add]
  rw [hM] at hK
  rw [hM, Finset.sum_range_succ', Finset.sum_congr rfl fun x _ ↦ hrow x]
  rw [show (∑ x ∈ range M, msKF ρ μ 0 (n - 1) x * (padDotF ω (fun _ ↦ false) + gDTF ω D x)) =
      ∑ x ∈ range (M + 1), msKF ρ μ 0 (n - 1) x * (padDotF ω (fun _ ↦ false) + gDTF ω D x) by
    rw [Finset.sum_range_succ, hlast, add_zero]]
  rw [← hK, chainIn, if_pos rfl, omegaDotF_pad43, Finset.mul_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [mul_comm (padDotF ω (fun _ ↦ false))]
  ring

/-- The extension of a table over `2^k` rows at `pt`. -/
def extF (k : ℕ) (pt : List F) (f : ℕ → F) : F := ∑ x ∈ range (2 ^ k), eqAtF pt x * f x

/-- The wiring sumcheck's family (chain) over `F` (`wireChF`). -/
def wireChFF (w : ℕ) (ρ μ ω : List F) (m : ℕ) (D : ℕ → ℕ → K) (acc : List F) : F :=
  cubeSumF (fun pt ↦ extF w pt (msKF ρ μ 0 m) * extF w pt (gDTF ω D)) w acc

theorem wireChFF_plain {β : Type} (w : ℕ) (ρ μ ω : List F) (m : ℕ) (D : β → ℕ → ℕ → K) :
    PlainFamilyF (fun q acc ↦ wireChFF w ρ μ ω m (D q) acc) 2 w :=
  cube_plainFamilyF _ w fun _ pre post ↦ polyLEF_mle_mul _ _ _ _ pre post

theorem wireChFF_end {w : ℕ} (ρ μ ω : List F) {m : ℕ} (D : ℕ → ℕ → K) {σ : List F}
    (hσ : σ.length = w) (h4 : 4 ≤ w) (hρ : w - 4 ≤ ρ.length) (hm : m < 2 ^ w) :
    wireChFF w ρ μ ω m D σ = msEvalF ρ μ σ 0 m * extF w σ (gDTF ω D) := by
  subst hσ
  rw [wireChFF, cubeSumF_full _ rfl, extF, sum_msKF_zero ρ μ σ m h4 hρ hm]

/-- **`G̃_D` is `D`'s slot sum.** -/
theorem gD_slotF (w dsel : ℕ) (ω : List F) (col : ℕ → K) (pt : List F) :
    extF w pt (gDTF ω (dOf w dsel col)) = slotSumF w 2 dsel (dWF ω) col pt := by
  simp only [extF, gDTF, slotSumF, slotSliceF, Finset.mul_sum]
  rw [Finset.sum_comm, show 256 = 4 * 64 from rfl, sum_range_mulB, show (2 : ℕ) ^ 2 = 4 from rfl]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦
    Finset.sum_congr rfl fun x _ ↦ ?_
  have hz' := Finset.mem_range.1 hz
  simp only [Lvm.KG.rowBits, dOf, dWF, show (64 * l + z) / 64 = l by (clear * - l z hz'; omega),
    show (64 * l + z) % 64 = z by (clear * - l z hz'; omega), show 8 + (64 * l + z) = 8 + 64 * l + z by (clear * - l z; omega)]
  ring

variable [CharP F 2]

theorem wireChFF_nil (w : ℕ) (ρ μ ω : List F) (m : ℕ) (D : ℕ → ℕ → K) :
    wireChFF w ρ μ ω m D [] = ∑ x ∈ range (2 ^ w), msKF ρ μ 0 m x * gDTF ω D x := by
  rw [wireChFF, cubeSumF_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [extF, extF, sum_eqAtF_bitsF hu', sum_eqAtF_bitsF hu']

/-- **The wiring sumcheck's claim is the input claim** (`inClaim_of_target`). -/
theorem inClaim_of_targetF {w : ℕ} (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w)
    (claim : KClaim F) (hρ : claim.point.length + 4 = w) (D : ℕ → ℕ → K)
    (hv : wireTargetF s n claim = wireChFF w claim.point claim.mu claim.weights (n - 1) D []) :
    InClaimTrueF w (chainIn s n D) claim := by
  rw [wireChFF_nil] at hv
  have hS := sum_range_iotaF_succ claim.point claim.mu (n - 1) (by rw [hρ]; (clear * - n w F hn hN claim; omega))
  rw [CharTwo.sub_eq_add] at hS
  rw [InClaimTrueF, wire_identity_chF _ _ _ s D hn hN, hS]
  rw [wireTargetF] at hv
  linear_combination hv - (iotaF claim.point claim.mu 0 * padDotF claim.weights
    (Lvm.KG.digestBits s) + padDotF claim.weights (fun _ ↦ false) *
      (thrEvalF claim.point claim.mu (n - 1) + iotaF claim.point claim.mu 0)) *
      CharTwo.two_eq_zero (R := F)

end WireAlg

variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-! ## Statement 7: the slot reduction -/

open Classical in
/-- The witness of `slotSpecE2`. -/
noncomputable def slotSpecE2W (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) {k b sb blk m : ℕ}
    (hk : k + b + sb = m) (hblk : blk < 2 ^ sb) (W : ℕ → ℕ → E2) (col : β → ℕ → K) (R : β → Prop)
    {pt : List E2} (hpt : pt.length = k) (v : E2)
    (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (slotProgE2 b sb blk W pt v)
      (Doomed C (fun q ↦ v = slotSumF k b blk W (col q) pt ∧ R q))
      (fun out hist ↦ out.sl.1.length = b ∧ out.sv.length = 64 ∧
        Doomed C (fun q ↦ RowColTrue m (col q) out.row ∧ R q) hist) εS 0 T :=
  have hrT' : (∑ _i ∈ range 7, ((1 : ℕ) : ℝ≥0∞) * errE 1) + T ≤ εS := by rw [rowLead_eq]; exact hrT
  ((sumcheckGSpec (T := 0) (L₀ := 1) hst hcard R (slotFF_plain k b blk W col pt) (count := 3)
      (by norm_num) (by norm_num) (g := gC2) (by norm_num) errG_c2 b [] v (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨hv.trans (slotFF_nil k b blk W (col q) pt), hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sl ↦
  if hm : sl.1.length = b then
    ((e2ReadsSpec (T := (∑ _i ∈ range 7, ((1 : ℕ) : ℝ≥0∞) * errE 1) + T) hst
        (fun q ↦ sl.2 = slotFF k b blk W (col q) pt ([] ++ sl.1) ∧ R q) hrT' 63).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sv ↦
    if hy : sv.length = 64 then
      (Spec.require (Pre := fun hist ↦ sv.length = 63 + 1 ∧
          Doomed C (fun q ↦ sl.2 = slotFF k b blk W (col q) pt ([] ++ sl.1) ∧ R q) hist)
        (Post := fun _ hist ↦ Doomed C (fun q ↦
          SlicesTrueE2 (col q) (pt ++ sl.1 ++ selPtF blk sb) sv ∧ R q) hist)
        (fun _ hd hcond ↦ Doomed.mono hd.2 fun q (hq : SlicesTrueE2 (col q)
            (pt ++ sl.1 ++ selPtF blk sb) sv ∧ R q) ↦ ⟨by
          rw [List.nil_append, slotFF_end _ _ _ _ _ _ hm, hcond, sumF_map_range]
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          rw [hq.1.2 z (Finset.mem_range.1 hz), slices_slotF hblk (col q) hpt hm z], hq.2⟩)).bind'
        fun _ ↦
      ((Classical.choice (rowSwitchSpec (εmax := εS) (T := T) (L₀ := 1) hst hcard col R
          (pt ++ sl.1 ++ selPtF blk sb) sv hy))).bind' fun row ↦
        (Spec.ret (⟨sl, sv, row⟩ : SlotOutE2)).mono (fun _ hd ↦ ⟨hm, hy, by
            have hzl : (pt ++ sl.1 ++ (selPtF blk sb : List E2)).length = m := by
              simp [hpt, hm, selPtF]; omega
            rw [hzl] at hd
            exact hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hm hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## Statement 6: the GKR -/

section FirstClaim

/-- A lane word over `F`, bit by bit. -/
theorem kF_ofLane {F : Type} [Field F] [Algebra K F] (w : UInt64) :
    (kF (K.ofLane w) : F) = ∑ z ∈ range 64, bitF (w.toBitVec.getLsbD z) * nF (2 ^ z) := by
  rw [K.ofLane, LeanVM.Protocol.KeccakGkr.word_eq_sum, kF, map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  cases w.toBitVec.getLsbD z <;> simp [nF, bitF]

/-- The first claim's weights read a state's lanes as words. -/
theorem sum_firstWeightsF {lanesPt : List E2} (hl : lanesPt.length = 5) (a : KeccakState) :
    ∑ j ∈ range 1600, (firstWeightsF lanesPt).getD j 0 * bitF (sbit a j) =
      ∑ l ∈ range 25, eqAtF lanesPt l * kF (laneWord a l) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mulB]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [laneWord, kF_ofLane, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have hj : 64 * l + z < 1600 := by (clear * - l z lanesPt hl'' hz'; omega)
  rw [firstWeightsF, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  have e1 : (64 * l + z) / 64 = l := by (clear * - l z lanesPt hz'; omega)
  have e2 : (64 * l + z) % 64 = z := by (clear * - l z lanesPt e1; omega)
  rw [e1, e2, eqKernelF_getD, hl, ite_eq_left (by (clear * - l lanesPt hl'' z e1; omega)),
    LeanVM.Protocol.KeccakGkr.sbit_lane a l hz']
  ring

/-- The tape's states at depth `0` (the outputs), at `(z, i)`. -/
theorem stAt_tape0 (P : ℕ) (I : ℕ → KeccakState) (z i j : ℕ) :
    stAt (tapeStates P I 0) P z i j = sbit (keccakF1600 (I (i + 16 * z))) j := by
  have h := Nat.mod_add_div z (2 ^ P)
  have : i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P) = i + 16 * z := by
    calc i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)
        = i + 16 * (z % 2 ^ P + 2 ^ P * (z / 2 ^ P)) := by rw [pow_add]; ring
      _ = i + 16 * z := by rw [h]
  show sbit (LeanVM.Protocol.KeccakGkr.roundsFrom (24 * 0) (24 - 0)
    (I (i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)))) j = _
  rw [this]; rfl

/-- **The first claim's sum on the tape's outputs**: the lanes' word claims at `inst`, combined at
`lanesPt`. -/
theorem firstClaim_sumE2 (P : ℕ) (I : ℕ → KeccakState) {inst lanesPt : List E2}
    (hi : inst.length = P + 5) (hl : lanesPt.length = 5) (output : List E2) :
    claimSumF (tapeStates P I 0) P
        (firstClaimSF Shape.tape inst [] lanesPt output 0).point
        (firstClaimSF Shape.tape inst [] lanesPt output 0).mu
        (firstClaimSF Shape.tape inst [] lanesPt output 0).weights =
      ∑ l ∈ range 25, eqAtF lanesPt l *
        stepMleF (P + 5) inst (fun x ↦ laneWord (keccakF1600 (I x)) l) := by
  have ha : (inst.take 4).length = 4 := by simp [hi]
  have hb : (inst.drop 4).length = P + 1 := by simp [hi]
  have hmu : ∀ i ∈ range 16, (eqKernelF (inst.take 4)).getD i 0 = eqAtF (inst.take 4) i :=
    fun i hi' ↦ by
      rw [eqKernelF_getD, ha, ite_eq_left (show i < 2 ^ 4 by
        have := Finset.mem_range.1 hi'; simpa using this)]
  simp only [firstClaimSF, claimSumF, List.append_nil, stAt_tape0, sum_firstWeightsF hl]
  have hsplit : ∀ x, eqAtF inst x = eqAtF (inst.take 4) (x % 16) *
      eqAtF (inst.drop 4) (x / 16) := by
    intro x
    conv_lhs => rw [← List.take_append_drop 4 inst]
    rw [eqAtF_append, ha, eqAtF_mod (inst.take 4), ha]
    norm_num
  have hpow : (2 : ℕ) ^ (P + 5) = 2 ^ (P + 1) * 16 := by
    rw [show P + 5 = (P + 1) + 4 by (clear * - P inst lanesPt; omega), pow_add]; norm_num
  simp only [stepMleF, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm, hpow, sum_range_mulB]
  refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i hi' ↦
    Finset.sum_congr rfl fun l _ ↦ ?_
  have hi'' := Finset.mem_range.1 hi'
  rw [hmu i hi', hsplit, show (16 * z + i) % 16 = i by (clear * - z i P inst lanesPt hi''; omega), show (16 * z + i) / 16 = z by (clear * - z i P inst lanesPt hi''; omega),
    show i + 16 * z = 16 * z + i by ring]
  ring

/-- The lanes' zero-test table: the mismatch of output lane `t` (`t < 25`). -/
def laneDelta (P : ℕ) (inst output : List E2) (I : ℕ → KeccakState) (t : ℕ) : E2 :=
  if t < 25 then stepMleF (P + 5) inst (fun x ↦ laneWord (keccakF1600 (I x)) t) + output.getD t 0
  else 0

theorem laneDelta_of_zeroOn_nil (P : ℕ) (inst output : List E2) (I : ℕ → KeccakState)
    (h : ZeroOnF (laneDelta P inst output I) [] 5) :
    ∀ l < 25, stepMleF (P + 5) inst (fun x ↦ laneWord (keccakF1600 (I x)) l) = output.getD l 0 := by
  rw [zeroOnF_nil] at h
  intro l hl
  have := h l (by (clear * - l hl; omega))
  rw [laneDelta, if_pos hl] at this
  exact (add_eq_zero_iff_eq_neg.1 this).trans (CharTwo.neg_eq _)

/-- **The first claim is the lanes' zero test at `lanesPt`.** -/
theorem laneDelta_zeroOn_of_first (P : ℕ) {inst lanesPt output : List E2} (I : ℕ → KeccakState)
    (hi : inst.length = P + 5) (hl : lanesPt.length = 5) (ho : output.length = 25)
    (htrue : ClaimTrueF (tapeStates P I 0) P (firstClaimSF Shape.tape inst [] lanesPt output 0)) :
    ZeroOnF (laneDelta P inst output I) lanesPt 5 := by
  rw [zeroOnF_full _ hl]
  rw [ClaimTrueF, firstClaim_sumE2 P I hi hl output] at htrue
  have hv : (firstClaimSF Shape.tape inst [] lanesPt output 0).value =
      ∑ l ∈ range 25, eqAtF lanesPt l * output.getD l 0 := by
    simp only [firstClaimSF]
    rw [eqKernelF_getD, if_pos (by decide), show Shape.tape.segments - 1 = 0 from rfl]
    simp only [eqAtF_nil, zero_add, one_mul]
    rw [← ho, dot_eqKernelF lanesPt output (by rw [hl, ho]; norm_num)]
  rw [hv] at htrue
  rw [show 2 ^ 5 = 25 + 7 from rfl, Finset.sum_range_add]
  have h7 : ∑ x ∈ range 7, eqAtF lanesPt (25 + x) * laneDelta P inst output I (25 + x) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by rw [laneDelta, if_neg (by (clear * - x P inst lanesPt output; omega)), mul_zero]
  rw [h7, add_zero, Finset.sum_congr rfl fun l hl' ↦ by
    rw [laneDelta, if_pos (Finset.mem_range.1 hl'), mul_add], Finset.sum_add_distrib, ← htrue]
  exact CharTwo.add_self_eq_zero _

theorem firstClaim_shapeE2 {P : ℕ} {inst lanesPt output : List E2} (hi : inst.length = P + 5) :
    ClaimShapeF P (firstClaimSF Shape.tape inst [] lanesPt output 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [firstClaimSF]; rw [eqKernelF_length]; simp [hi]
  · simp only [firstClaimSF]; simp [hi]
  · simp only [firstClaimSF, firstWeightsF, List.length_map, List.length_range]; rfl

end FirstClaim


open Classical in
/-- The witness of `tapeGkrSpecE2`: the lanes' zero test (`zeroSpecE2`, `(1, 1)`), then the 24
layers (`layersSpecE2`). -/
noncomputable def tapeGkrSpecE2W (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Iq : β → ℕ → KeccakState) (P : ℕ) {inst output : List E2} (hi : inst.length = P + 5)
    (ho : output.length = 25) (hT : errG gC2 2 + T ≤ εS) :
    Spec (tapeGkrE2 (P + 5) inst output)
      (Doomed C (fun q ↦ (∀ l < 25, stepMleF (P + 5) inst
        (fun x ↦ laneWord (keccakF1600 (Iq q x)) l) = output.getD l 0) ∧ R q))
      (fun c h ↦ ClaimShapeF P c ∧ Doomed C (fun q ↦ ClaimTrueF (tapeStates P (Iq q) 24) P c ∧ R q) h)
      εS 0 T :=
  ((zeroSpecE2 (T := 0) (L₀ := 1) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ laneDelta P inst output (Iq q)) R (n := 5) (m := 4) le_rfl errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ ⟨laneDelta_of_zeroOn_nil P inst output (Iq q) hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun lanesPt ↦
  if hl : lanesPt.length = 5 then
    Spec.congr (p := keccakLayersE2 Shape.tape (Shape.tape.logSteps P) (List.range' 0 (23 + 1))
        (firstClaimSF Shape.tape inst [] lanesPt output 0))
      (by rw [List.range_eq_range']; rfl)
      ((layersSpecE2 (T := T) LeanVM.Protocol.KeccakGkr.Shape.tape_ok hst hcard R (fun q _ ↦ Iq q) P hT
          23 0 rfl _ (firstClaim_shapeE2 hi)).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨htrue, hR⟩ ↦
          ⟨laneDelta_zeroOn_of_first P (Iq q) hi hl ho htrue, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
  else Spec.dead.mono (fun _ hd ↦ hl hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Statement 6 (`tapeGkrSpecE2`)**: the tape's reduction at `E2`, from doom of the 25 output-lane
word claims at `inst` to doom of the returned claim on the inputs' states (`24` layers below the
output). One candidate at most; every group `≤ εS`; the last group (`β`, `c = 2`) with the
follower's `T`. -/
theorem tapeGkrSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (Iq : β → ℕ → KeccakState) (P : ℕ) {inst output : List E2} (hi : inst.length = P + 5)
    (ho : output.length = 25) (hT : errG gC2 2 + T ≤ εS) :
    Nonempty (Spec (tapeGkrE2 (P + 5) inst output)
      (Doomed C (fun q ↦ (∀ l < 25, stepMleF (P + 5) inst
        (fun x ↦ laneWord (keccakF1600 (Iq q x)) l) = output.getD l 0) ∧ R q))
      (fun c h ↦ ClaimShapeF P c ∧ Doomed C (fun q ↦ ClaimTrueF (tapeStates P (Iq q) 24) P c ∧ R q) h)
      εS 0 T) :=
  ⟨tapeGkrSpecE2W hst hcard R Iq P hi ho hT⟩

/-! ## Statement 7: slots and wiring -/

/-- **Statement 7 (`slotSpecE2`)**: a slot reduction at `E2`, from doom of `v = slotSum ∧ R` to doom
of the row switch's claim on the column (`k + b + sb = m` variables) and `R`. Rounds `c = 2`; the
row switch's seven `E3` samples with the follower's `T`. -/
theorem slotSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) {k b sb blk m : ℕ}
    (hk : k + b + sb = m) (hblk : blk < 2 ^ sb) (W : ℕ → ℕ → E2) (col : β → ℕ → K) (R : β → Prop)
    {pt : List E2} (hpt : pt.length = k) (v : E2)
    (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Nonempty (Spec (slotProgE2 b sb blk W pt v)
      (Doomed C (fun q ↦ v = slotSumF k b blk W (col q) pt ∧ R q))
      (fun out hist ↦ out.sl.1.length = b ∧ out.sv.length = 64 ∧
        Doomed C (fun q ↦ RowColTrue m (col q) out.row ∧ R q) hist) εS 0 T) :=
  ⟨slotSpecE2W hst hcard hk hblk W col R hpt v hrT⟩

open Classical in
/-- The witness of `wireSpecE2` (`wireChSpec` at `E2`). -/
noncomputable def wireSpecE2W (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1)
    {w sb dsel h : ℕ} (hw : w + 2 + sb = h + 6) (hsel : dsel < 2 ^ sb)
    (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w)
    (claim : KClaim E2) (hρ : claim.point.length + 4 = w)
    (colM : β → ℕ → K) (R : β → Prop)
    (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (wireChProgE2 w sb dsel s n claim)
      (Doomed C (fun q ↦ InClaimTrueF w (chainIn s n (dOf w dsel (colM q))) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = w ∧ out.d.sl.1.length = 2 ∧
        Doomed C (fun q ↦ RowColTrue (h + 6) (colM q) out.d.row ∧ R q) hist) εS 0 T :=
  have h4 : 4 ≤ w := by omega
  have hρ' : w - 4 ≤ claim.point.length := by omega
  ((sumcheckGSpec (T := 0) (L₀ := 1) hst hcard R (wireChFF_plain w claim.point claim.mu claim.weights
      (n - 1) (fun q ↦ dOf w dsel (colM q))) (count := 3) (by norm_num) (by norm_num) (g := gC2)
      (by norm_num) errG_c2 w [] (wireTargetF s n claim) (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦
      ⟨inClaim_of_targetF s hn hN claim hρ (dOf w dsel (colM q)) hv, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc ↦
  if hs : sc.1.length = w then
    ((e2ReadsSpec (T := 0) hst (fun q ↦ sc.2 = wireChFF w claim.point claim.mu claim.weights (n - 1)
        (dOf w dsel (colM q)) ([] ++ sc.1) ∧ R q) zero_le 0).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun g ↦
    (Spec.require (Pre := fun hist ↦ g.length = 0 + 1 ∧ Doomed C (fun q ↦ sc.2 =
        wireChFF w claim.point claim.mu claim.weights (n - 1) (dOf w dsel (colM q)) ([] ++ sc.1) ∧
          R q) hist)
      (Post := fun _ hist ↦ Doomed C (fun q ↦
        g.getD 0 0 = slotSumF w 2 dsel (dWF claim.weights) (colM q) sc.1 ∧ R q) hist)
      (fun _ hd hcond ↦ Doomed.mono hd.2 fun q (hq : g.getD 0 0 =
          slotSumF w 2 dsel (dWF claim.weights) (colM q) sc.1 ∧ R q) ↦ ⟨by
        rw [List.nil_append, wireChFF_end _ _ _ _ hs h4 hρ' (by omega), hcond, hq.1, gD_slotF],
        hq.2⟩)).bind' fun _ ↦
    (slotSpecE2W (T := T) hst hcard (k := w) (b := 2) hw hsel (dWF claim.weights) colM R hs
        (g.getD 0 0) hrT).bind' fun d ↦
    (Spec.ret (⟨sc, g, d⟩ : WireChOutE2)).mono (fun _ hd ↦ ⟨hs, hd.1, hd.2.2⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Statement 7 (`wireSpecE2`)**: the chain wiring phase at `E2`, from doom of the GKR's input claim
on the virtual chain inputs and `R` to doom of the row claim on `D`'s block of `C_main` (`h + 6`
variables) and `R`. Wire and slot rounds `c = 2`; the row switch with the follower's `T`. -/
theorem wireSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1)
    {w sb dsel h : ℕ} (hw : w + 2 + sb = h + 6) (hsel : dsel < 2 ^ sb)
    (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ w)
    (claim : KClaim E2) (hρ : claim.point.length + 4 = w)
    (colM : β → ℕ → K) (R : β → Prop)
    (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Nonempty (Spec (wireChProgE2 w sb dsel s n claim)
      (Doomed C (fun q ↦ InClaimTrueF w (chainIn s n (dOf w dsel (colM q))) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = w ∧ out.d.sl.1.length = 2 ∧
        Doomed C (fun q ↦ RowColTrue (h + 6) (colM q) out.d.row ∧ R q) hist) εS 0 T) :=
  ⟨wireSpecE2W hst hcard hw hsel s hn hN claim hρ colM R hrT⟩

/-! ## Statement 6: the caller -/

/-- The postcondition of the tape caller at `E2`. -/
def TapePostE2 (w h dsel : ℕ) (colM : β → ℕ → K) (R : β → Prop) (out : TapeOutE2)
    (hist : List Ev) : Prop :=
  out.1.length = w ∧ out.2.1.length = 25 ∧ out.2.2.2.sc.1.length = w ∧
    out.2.2.2.d.sl.1.length = 2 ∧
    Doomed C (fun q ↦ RowColTrue (h + 6) (colM q) out.2.2.2.d.row ∧
      TiedDF w (dOf w dsel (colM q)) out.1 out.2.1 ∧ R q) hist

/-! ### T1's zero test and the glue to the wiring -/

/-- **T1's zero-test table at `E2`** on `w + 2` variables (`tapeDelta`). -/
def tapeDeltaE2 (w : ℕ) (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K) (v : ℕ) : E2 :=
  if v / 2 ^ w < 4 then
    kF (D (v % 2 ^ w) (v / 2 ^ w)) + kF (laneWord (keccakF1600 (chainIn s n D (v % 2 ^ w))) (v / 2 ^ w))
  else 0

/-- The table vanishing gives `TapeOut` (`zeroOn_tapeDelta_iff`'s direction). -/
theorem tapeOut_of_zeroOnE2 (w : ℕ) (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K)
    (hz : ZeroOnF (tapeDeltaE2 w s n D) [] (w + 2)) : TapeOut w s n D := by
  rw [zeroOnF_nil] at hz
  have hp := Nat.two_pow_pos w
  intro x hx l hl
  have := hz (x + 2 ^ w * l) (by rw [pow_add]; nlinarith)
  have e1 : (x + 2 ^ w * l) / 2 ^ w = l := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, zero_add]
  have e2 : (x + 2 ^ w * l) % 2 ^ w = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  simp only [tapeDeltaE2, e1, e2, hl, ite_true] at this
  exact (algebraMap K E2).injective ((add_eq_zero_iff_eq_neg.1 this).trans (CharTwo.neg_eq _))

/-- The table's extension vanishes at `r` under the output claims and the tied lanes' claims. -/
theorem tapeDelta_zeroOnE2 {w : ℕ} (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K)
    {r v : List E2} (hr : r.length = w)
    (hout : ∀ l < 25, stepMleF w r (fun x ↦ laneWord (keccakF1600 (chainIn s n D x)) l) =
      v.getD l 0)
    (htied : TiedDF w D r v) : ZeroOnF (tapeDeltaE2 w s n D) r (w + 2) := by
  intro t ht
  rw [hr, show w + 2 - w = 2 by (clear * - w r t; omega)] at ht
  have ht4 : t < 4 := lt_of_lt_of_eq ht (by norm_num)
  unfold foldTF
  rw [hr]
  have hp := Nat.two_pow_pos w
  have e : ∀ x ∈ range (2 ^ w), tapeDeltaE2 w s n D (x + 2 ^ w * t) =
      kF (D x t) + kF (laneWord (keccakF1600 (chainIn s n D x)) t) := by
    intro x hx
    have hx' := Finset.mem_range.1 hx
    have e1 : (x + 2 ^ w * t) / 2 ^ w = t := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx', zero_add]
    have e2 : (x + 2 ^ w * t) % 2 ^ w = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
    simp only [tapeDeltaE2, e1, e2, ht4, ite_true]
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [e x hx]]
  have h3 := htied t ht4
  have h4 := hout t (by (clear * - t w r ht; omega))
  simp only [stepMleF] at h3 h4
  simp only [mul_add, Finset.sum_add_distrib, h3, h4]
  exact CharTwo.add_self_eq_zero _

/-- The tape's states at depth `24` (the inputs), at `(z, i)`. -/
theorem stAt_tape24 (P : ℕ) (I : ℕ → KeccakState) (z i j : ℕ) :
    stAt (tapeStates P I 24) P z i j = sbit (I (i + 16 * z)) j := by
  have h := Nat.mod_add_div z (2 ^ P)
  have : i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P) = i + 16 * z := by
    calc i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)
        = i + 16 * (z % 2 ^ P + 2 ^ P * (z / 2 ^ P)) := by rw [pow_add]; ring
      _ = i + 16 * z := by rw [h]
  show sbit (LeanVM.Protocol.KeccakGkr.roundsFrom (24 * 0) (24 - 24)
    (I (i + 16 * (z % 2 ^ P) + 2 ^ (P + 4) * (z / 2 ^ P)))) j = _
  rw [this]; rfl

/-- **The GKR's end is the input claim** (`claimTrue_of_inClaim` at `E2`). -/
theorem claimTrue_of_inClaimF {P : ℕ} (I : ℕ → KeccakState) (c : KClaim E2)
    (h : InClaimTrueF (P + 5) I c) : ClaimTrueF (tapeStates P I 24) P c := by
  have hpow : (2 : ℕ) ^ (P + 5) = 2 ^ (P + 1) * 16 := by
    rw [show P + 5 = (P + 1) + 4 by (clear * - P; omega), pow_add]; norm_num
  rw [InClaimTrueF] at h
  rw [ClaimTrueF, h, claimSumF, hpow, sum_range_mulB]
  simp only [stAt_tape24]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  rw [iotaF, omegaDotF, show (16 * z + i) / 16 = z by (clear * - z i P hi'; omega), show (16 * z + i) % 16 = i by (clear * - z i P hi'; omega),
    show i + 16 * z = 16 * z + i by ring]
  ring

open Classical in
/-- The witness of `tapeSpecE2` (`tapeSpec` at `E2`). -/
noncomputable def tapeSpecE2W (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) {P sb dsel h : ℕ}
    (hw : P + 5 + 2 + sb = h + 6) (hsel : dsel < 2 ^ sb) (s : RecursionFast.Digest) {n : ℕ}
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (tapeProgE2 (P + 5) sb dsel s n)
      (Doomed C (fun q ↦ TapeOut (P + 5) s n (dOf (P + 5) dsel (colM q)) ∧ R q))
      (TapePostE2 (C := C) (P + 5) h dsel colM R) εS 0 T :=
  (sepSpec (T' := 0) hst hcard _).bind' fun _ ↦
  ((zeroSpecE2 (T := 0) (L₀ := 1) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ tapeDeltaE2 (P + 5) s n (dOf (P + 5) dsel (colM q))) R (n := P + 5 + 2) (m := P + 4)
      (by omega) errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ ⟨tapeOut_of_zeroOnE2 _ s n _ hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = P + 5 then
    ((e2ReadsSpec (T := 0) hst
        (fun q ↦ ZeroOnF (tapeDeltaE2 (P + 5) s n (dOf (P + 5) dsel (colM q))) r (P + 5 + 2) ∧ R q)
        zero_le 24).mono
      (fun _ hd ↦ by rw [show P + 4 + 1 = P + 5 by omega] at hd; exact hd.2) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl).bind' fun v ↦
    if hv : v.length = 25 then
      ((tapeGkrSpecE2W (T := 0) hst hcard
          (fun q ↦ TiedDF (P + 5) (dOf (P + 5) dsel (colM q)) r v ∧ R q)
          (fun q ↦ chainIn s n (dOf (P + 5) dsel (colM q))) P hr hv
          (by simpa using errG_c2)).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hout, htied, hR⟩ ↦
          ⟨tapeDelta_zeroOnE2 s n _ hr hout htied, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun claim ↦
      if hc : claim.point.length + 4 = P + 5 then
        (Spec.require (T := 0) (c := 1 ≤ n ∧ n ≤ 2 ^ (P + 5))
          (Post := fun _ hist ↦ (1 ≤ n ∧ n ≤ 2 ^ (P + 5)) ∧ (ClaimShapeF P claim ∧
            Doomed C (fun q ↦ ClaimTrueF (tapeStates P (chainIn s n (dOf (P + 5) dsel (colM q))) 24) P
              claim ∧ (TiedDF (P + 5) (dOf (P + 5) dsel (colM q)) r v ∧ R q)) hist))
          (fun _ hp hcond ↦ ⟨hcond, hp⟩)).bind' fun _ ↦
        if hb : 1 ≤ n ∧ n ≤ 2 ^ (P + 5) then
          ((wireSpecE2W (T := T) hst hcard hw hsel s hb.1 hb.2 claim hc colM
              (fun q ↦ TiedDF (P + 5) (dOf (P + 5) dsel (colM q)) r v ∧ R q) hrT).mono
            (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hin, hR⟩ ↦ ⟨claimTrue_of_inClaimF _ claim hin, hR⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun wo ↦
          (Spec.ret (r, v, claim, wo)).mono (fun _ hd ↦ ⟨hr, hv, hd.1, hd.2.1, hd.2.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hb hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ (hd : ClaimShapeF P claim ∧ _) ↦ hc (by
          obtain ⟨-, h1, -⟩ := hd.1; omega)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hv hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr (by simpa using hd.1)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Statement 6 (`tapeSpecE2`)**: the tape caller at `E2` (V_S's CHtape and CHwire at S2GF,
`w = P + 5`), round by round at `L₀ = 1`: from doom of "`D` is the permutation's output on the
virtual chain inputs at every row (`TapeOut`), and `R`" to doom of "the row claim on `C_main`, the
tied lanes' `E2` word claims `D̃_l(r) = v_l`, and `R`". Lead `0` (the separator escapes nothing);
every ground group `≤ εS` (`(1,1)`, `(2,2)`, `(3,2)`, `(46,6)`); the row switch's group with the
follower's `T`. -/
theorem tapeSpecE2 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) {P sb dsel h : ℕ}
    (hw : P + 5 + 2 + sb = h + 6) (hsel : dsel < 2 ^ sb) (s : RecursionFast.Digest) {n : ℕ}
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Nonempty (Spec (tapeProgE2 (P + 5) sb dsel s n)
      (Doomed C (fun q ↦ TapeOut (P + 5) s n (dOf (P + 5) dsel (colM q)) ∧ R q))
      (TapePostE2 (C := C) (P + 5) h dsel colM R) εS 0 T) :=
  ⟨tapeSpecE2W hst hcard hw hsel s colM R hrT⟩

end Lvm.E2V
