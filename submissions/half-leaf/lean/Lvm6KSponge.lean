-- New for lvm6 K1: the sponge batch (`FORMAT6.md` §6.3, §T) in the doom calculus: season 1's caller
-- (`r`, the 25 scalars) around the v6 core (`kHead6 (h-4) 25`, `spongeEnd6`), statement
-- `SpongeSpecStmt` (frozen in `Lvm6KStmt`).
import Lvm6KHead

/-!
# The sponge batch

* the sponge end's ten plain rounds as one family `FeSp` (season 1's four instance rounds `FlF`, then
  its six slot rounds `FsF`): `FeSp_plain`, `FeSp_nil`;
* the end's weight in closed form: `drop_eq_getD` (the segment point), `spWt_eq` (`spWt` is season
  1's `WsF`); `final_spF` (with true slices the final check gives the family's last claim);
* `endSpec` (row 10 of §6.3, `spongeEnd6`), `coreSpec` (`spongeCore6`: `headSpec` on the inputs
  `inState`, then `endSpec`), `spongeSpecW` (`spCaller6`: season 1's zero test of `callDeltaF` for
  `r`, the 25 scalars, the core);
* **`spongeSpec6`**: `SpongeSpecStmt h nt` for `5 ≤ h`, `nt ≤ 25`.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (Shape statesOfS laneWord inState RegionValid)
open Lvm.E2V
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-! ## The end's ten rounds as one family -/

section End

variable (P : ℕ)

/-- **The sponge end's family** (ten plain rounds): season 1's instance rounds `FlF` on the first
four challenges, then its slot rounds `FsF` at the instance point `acc.take 4`. -/
def FeSp (col : ℕ → K) (claim : KClaim E2) (acc : List E2) : E2 :=
  if acc.length ≤ 4 then FlF P col claim acc else FsF P col claim (acc.take 4) (acc.drop 4)

theorem FeSp_nil (col : ℕ → K) (claim : KClaim E2) : FeSp P col claim [] = FlF P col claim [] := by
  rw [FeSp, ite_eq_left (by simp)]

theorem FeSp_plain {β : Type} (qk : β → ℕ → K) (claim : KClaim E2) (hshape : ClaimShapeF P claim) :
    PlainFamilyF (fun q acc ↦ FeSp P (qk q) claim acc) 2 10 := by
  intro q acc hacc
  beta_reduce
  by_cases h4 : acc.length < 4
  · obtain ⟨h1, h2⟩ := FlF_plain P qk claim q acc h4
    beta_reduce at h1 h2
    have e : ∀ x, FeSp P (qk q) claim (acc ++ [x]) = FlF P (qk q) claim (acc ++ [x]) := fun x ↦ by
      rw [FeSp, ite_eq_left (by simp; omega)]
    refine ⟨h1.congr fun x ↦ (e x).symm, ?_⟩
    rw [e, e, FeSp, ite_eq_left (by omega)]
    exact h2
  · have ht : ∀ x : E2, (acc ++ [x]).take 4 = acc.take 4 := fun x ↦
      List.take_append_of_le_length (by omega)
    have hd : ∀ x : E2, (acc ++ [x]).drop 4 = acc.drop 4 ++ [x] := fun x ↦
      List.drop_append_of_le_length (by omega)
    have e : ∀ x, FeSp P (qk q) claim (acc ++ [x]) =
        FsF P (qk q) claim (acc.take 4) (acc.drop 4 ++ [x]) := fun x ↦ by
      rw [FeSp, ite_eq_right (by simp; omega), ht, hd]
    obtain ⟨h1, h2⟩ := FsF_plain P qk claim (acc.take 4) q (acc.drop 4) (by simp; omega)
    beta_reduce at h1 h2
    refine ⟨h1.congr fun x ↦ (e x).symm, ?_⟩
    rw [e, e, ← h2]
    by_cases h5 : acc.length = 4
    · rw [FeSp, ite_eq_left (by omega), FlF, cubeSumF_full _ h5, List.take_of_length_le (by omega),
        List.drop_eq_nil_of_le (by omega), FsF_nil P (qk q) claim hshape h5]
    · rw [FeSp, ite_eq_right (by omega)]

/-- A point of `P + 1` coordinates, past its first `P`, is its coordinate `P`. -/
theorem drop_eq_getD {l : List E2} (hl : l.length = P + 1) : l.drop P = [l.getD P 0] := by
  have h1 : (l.drop P).length = 1 := by simp [hl]
  match hd : l.drop P, h1 with
  | [a], _ =>
    have : l[P]? = some a := by rw [← Nat.add_zero P, ← List.getElem?_drop, hd]; rfl
    rw [List.getD_eq_getElem?_getD, this]
    rfl

/-- **The sponge end's weight is season 1's slot weight**: `spWt` at `(r'_seg, w, ϱs)` is `W̃_z(ϱs)`
(`WsF`, slots `25m + ℓ`). -/
theorem spWt_eq (claim : KClaim E2) (hshape : ClaimShapeF P claim) (slot : List E2) {z : ℕ}
    (hz : z < 64) : spWt (claim.point.getD P 0) claim.weights slot z = WsF P claim z slot := by
  have hd := drop_eq_getD P hshape.2.1
  rw [WsF, show 2 ^ 6 = 2 * 25 + 14 from rfl, Finset.sum_range_add, sum_range_mulK 2 25]
  have hzero : ∑ x ∈ range 14, eqAtF slot (2 * 25 + x) *
      slotWtF (eqKernelF (claim.point.drop P)) claim.weights 0 2 (2 * 25 + x) z = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by rw [slotWtF, ite_eq_right (by omega), mul_zero]
  rw [hzero, add_zero, spWt]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.1 hl
  rw [slotWtF, ite_eq_left (show 25 * 0 ≤ 25 * m + l ∧ 25 * m + l < 25 * (0 + 2) ∧ z < 64 by omega),
    show (25 * m + l) / 25 - 0 = m by omega, show (25 * m + l) % 25 = l by omega, eqKernelF_getD,
    hd, ite_eq_left (by simp; omega)]
  ring

/-- **The final check** of the sponge end: with true slices at `(λ, r_pack, ϱs)`, the check gives
the family's last claim. -/
theorem final_spF (col : ℕ → K) (claim : KClaim E2) (hshape : ClaimShapeF P claim)
    {lv slices : List E2} (hlv : lv.length = 10) (value : E2)
    (hs : SlicesTrue6 (P + 4 + 6) col (lv.take 4 ++ claim.point.take P ++ lv.drop 4) slices)
    (hc : multilinearEvalF claim.mu (lv.take 4) *
      ∑ z ∈ range 64, spWt (claim.point.getD P 0) claim.weights (lv.drop 4) z * slices.getD z 0 =
        value) :
    value = FeSp P col claim lv := by
  have hlow : (lv.take 4).length = 4 := by simp [hlv]
  have hslot : (lv.drop 4).length = 6 := by simp [hlv]
  have ha : (lv.take 4 ++ claim.point.take P).length = P + 4 := by
    simp [hlv, hshape.2.1]; omega
  rw [FeSp, ite_eq_right (by omega), FsF, cubeSumF_full _ hslot, ← hc, multilinearEvalF_mu hshape.1 hlow]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun z hz ↦ ?_)
  have hz' := Finset.mem_range.1 hz
  rw [spWt_eq P claim hshape _ hz', hs.2.2 z hz', slices_eqF P col ha hslot z]

end End

/-! ## The sponge batch in the doom calculus -/

variable {β : Type} {C : List Ev → Set β} [Finite β]

open Classical in
/-- **The sponge end** (`spongeEnd6`, row 10 of §6.3): ten plain rounds (`c = 2`), the 64 slices,
the check. From doom of the claim after the layers on the inputs `inState` to doom of the slice
claims. Lead `0`; the follower's `T` after the slices. -/
noncomputable def endSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) (claim : KClaim E2) (hshape : ClaimShapeF P claim) {T : ℝ≥0∞}
    (hT : T ≤ εS) :
    Spec (spongeEnd6 P claim)
      (Doomed C (fun q ↦ ClaimTrueF (statesOfS Shape.v1 P (inState (P + 4) (qk q)) 12) P claim ∧
        R q))
      (fun en h ↦ en.ϱ.length = 10 ∧ en.pt.length = P + 4 + 6 ∧ en.s.length = 64 ∧
        Doomed C (fun q ↦ SlicesTrue6 (P + 4 + 6) (qk q) en.pt en.s ∧ R q) h) εS 0 T :=
  ((sumcheckGSpec (T := 0) hst hcard R (FeSp_plain P qk claim hshape) (count := 3) (by norm_num)
      (by norm_num) (g := gC2) (by norm_num) errG_c2 10 [] claim.value (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦
      ⟨by rw [ClaimTrueF, ← FlF_nil, ← FeSp_nil]; exact hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun lv ↦
  if hy : lv.1.length = 10 then
    ((e2ReadsSpec (T := T) hst _ hT 63).mono (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl
      le_rfl).bind' fun s ↦
    (Spec.require
      (Pre := fun h ↦ s.length = 63 + 1 ∧
        Doomed C (fun q ↦ lv.2 = FeSp P (qk q) claim ([] ++ lv.1) ∧ R q) h)
      (Post := fun _ h ↦ s.length = 63 + 1 ∧ Doomed C (fun q ↦
        SlicesTrue6 (P + 4 + 6) (qk q) (lv.1.take 4 ++ claim.point.take P ++ lv.1.drop 4) s ∧
          R q) h)
      fun _ hd hc ↦ ⟨hd.1, Doomed.mono hd.2 fun q ⟨hs, hR⟩ ↦ ⟨by
        rw [List.nil_append]
        exact final_spF P (qk q) claim hshape hy _ hs hc, hR⟩⟩).bind' fun _ ↦
    (Spec.ret (⟨lv.1, lv.1.take 4 ++ claim.point.take P ++ lv.1.drop 4, s⟩ : EndOut)).mono
      (fun _ hd ↦ ⟨hy, by simp [hy, hshape.2.1]; omega, hd.1, hd.2⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- What the sponge core leaves: the lengths, and doom of the middle word claim at `(r, ϱm)` and
the slice claims. -/
abbrev CorePost (P : ℕ) (sp : β → ℕ → K) (R : β → Prop) (r : List E2) (res : HeadOut × EndOut)
    (hist : List Ev) : Prop :=
  res.1.sl.length = 6 ∧ ClaimShapeF P res.1.claim ∧ res.1.ϱm.length = 6 ∧ res.2.ϱ.length = 10 ∧
    res.2.pt.length = P + 4 + 6 ∧ res.2.s.length = 64 ∧
    Doomed C (fun q ↦ ColTrue (P + 4 + 6) (sp q) (r ++ res.1.ϱm, res.1.cout) ∧
      SlicesTrue6 (P + 4 + 6) (sp q) res.2.pt res.2.s ∧ R q) hist

open Classical in
/-- **The sponge core** (`spongeCore6`, rows 6–10 of §6.3): `headSpec` on the inputs `inState`
(segment 1's lanes are slots `25 + ℓ`), then `endSpec`. Lead `0`; the follower's `T` after the
slices. -/
noncomputable def coreSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (R : β → Prop)
    (sp : β → ℕ → K) (P : ℕ) {r v : List E2} (hr : r.length = P + 4) (hv : v.length = 25)
    {T : ℝ≥0∞} (hT : T ≤ εS) :
    Spec (spongeCore6 P r v)
      (Doomed C (fun q ↦ outClaimsTrueMidV (P + 4) (inState (P + 4) (sp q)) r v ∧
        midAgreeV (P + 4) (inState (P + 4) (sp q)) r ∧ R q))
      (CorePost (C := C) P sp R r) εS 0 T :=
  (headSpec (T := 0) hst hcard R (fun q ↦ inState (P + 4) (sp q)) sp P 25 (by norm_num)
      (fun q x l hl ↦ by
        show laneWord (inState (P + 4) (sp q) 1 x) l = _
        rw [LeanVM.Protocol.KeccakGkr.laneWord_inState _ _ _ _ hl, mul_one])
      hr hv zero_le).bind' fun hd ↦
  if hh : hd.sl.length = 6 ∧ ClaimShapeF P hd.claim ∧ hd.ϱm.length = 6 then
    ((endSpec (T := T) hst hcard
        (fun q ↦ stepMleK (P + 4 + 6) (r ++ hd.ϱm) (sp q) = hd.cout ∧ R q) sp P hd.claim hh.2.1
        hT).mono
      (fun _ hp ↦ hp.2.2.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun en ↦
    (Spec.ret (hd, en)).mono
      (fun _ hp ↦ ⟨hh.1, hh.2.1, hh.2.2, hp.1, hp.2.1, hp.2.2.1,
        Doomed.mono hp.2.2.2 fun q ⟨hcol, hs, hR⟩ ↦ ⟨hs, hcol.2, hR⟩⟩)
      (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hh ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
    le_rfl

theorem spCaller6_eq (P : ℕ) :
    spCaller6 (P + 4) = (e2Samples gC1 (P + 3 + 1) >>= fun r ↦ e2Reads (24 + 1) >>= fun v ↦
      spongeCore6 P r v >>= fun res ↦ pure (r, v, res)) := by
  rw [spCaller6, Nat.add_sub_cancel]

/-- What the sponge caller leaves (`SpongeSpecStmt`'s postcondition). -/
abbrev SpPost (h nt : ℕ) (sp : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop) (out : SpOut)
    (hist : List Ev) : Prop :=
  SpongeShape h out ∧ Doomed C (fun q ↦ SpongeClaims h nt (sp q) (Y q) out ∧ R q) hist

open Classical in
/-- **The sponge caller** (`spCaller6 (P + 4)`): `r` (season 1's zero test of `callDeltaF`,
`c = 1`), the 25 scalars, the core. Lead `0`; the follower's `T` after the slices. -/
noncomputable def spongeSpecW (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (P nt : ℕ)
    (hnt : nt ≤ 25) (sp : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop) {T : ℝ≥0∞}
    (hT : T ≤ εS) :
    Spec (spCaller6 (P + 4))
      (Doomed C (fun q ↦ RegionValid (P + 4) (sp q) ∧ Lvm.KG.OutRel (P + 4) nt (sp q) (Y q) ∧ R q))
      (SpPost (C := C) (P + 4) nt sp Y R) εS 0 T :=
  Spec.congr (spCaller6_eq P).symm <|
  ((zeroSpecE2 (T := 0) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ callDeltaF (P + 4) nt (sp q) (Y q)) R (n := P + 4 + 6) (m := P + 3) (by omega)
      errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦
      ⟨(valid_of_callDeltaF_zero (P + 4) nt (sp q) (Y q) hnt hz).1,
        (valid_of_callDeltaF_zero (P + 4) nt (sp q) (Y q) hnt hz).2, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = P + 4 then
    ((e2ReadsSpec (T := 0) hst
        (fun q ↦ ZeroOnF (callDeltaF (P + 4) nt (sp q) (Y q)) r (P + 4 + 6) ∧ R q) zero_le 24).mono
      (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun v ↦
    if hv : v.length = 25 then
      ((coreSpec (T := T) hst hcard
          (fun q ↦ (∀ l < nt, stepMleK (P + 4) r (Y q l) = v.getD l 0) ∧ R q) sp P hr hv hT).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hout, hmid, htied, hR⟩ ↦
          ⟨callDeltaF_zeroOn (P + 4) nt (sp q) (Y q) hr hnt hout hmid htied, hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun res ↦
      (Spec.ret (r, v, res)).mono
        (fun _ hp ↦ ⟨⟨hr, hv, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩,
          Doomed.mono hp.2.2.2.2.2.2 fun q ⟨⟨hcol, hs, htied⟩, hR⟩ ↦ ⟨hcol, hs, htied, hR⟩⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hv hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- **The sponge caller** (`SpongeSpecStmt`): `spCaller6 h` with `nt ≤ 25` tied lanes, from doom of
season 1's sponge relation and `R` to doom of the claims it leaves and `R`; lead `0`, every group
`≤ εS`, the follower's `T` after the slices. -/
theorem spongeSpec6 (h nt : ℕ) (hh : 5 ≤ h) (hnt : nt ≤ 25) : SpongeSpecStmt h nt := by
  obtain ⟨P, rfl⟩ : ∃ P, h = P + 4 := ⟨h - 4, by omega⟩
  intro β _ C hst hcard sp Y R T hT
  exact ⟨spongeSpecW hst hcard P nt hnt sp Y R hT⟩

end Lvm6.K
