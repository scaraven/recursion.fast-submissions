-- New for lvm6 (WP-V1b): fast twins of K1's reduction head (`kHead6`: the segment and lane point, `c_st`, the first
-- claim, twelve layers, the middle-state opening) and of the tree batch (`treeProg`, §6.2 rows 1–10) and its phase
-- form (`treeProgS`: the column claims as point claims, the slices to ring switching).
import Lvm6VTwL
import Lvm6KStmt

/-!
# Fast twins: the reduction head and the tree phase

* `tw_dDraw`, `tw_dDraws`, `tw_gPoint`, `tw_kRead`, `tw_kReads` (`decK`: lane 0 of a read at its offset).
* `firstWArr` (the first claim's weights with the lane kernel and the powers `x^z` tabulated), `fFirst`, `fFirst_dec`.
* **`fKHead6`**, **`tw_kHead6`**; `toKF` (the weights materialized once, after the layers).
* **`fTreeProg`**, **`tw_treeProg`**; `TreeSF` (point claims), **`fTreeProgS`**, **`tw_treeProgS`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open LeanVM.Protocol.KeccakGkr (Shape)
open Finset

/-! ## Draws, points, words -/

/-- Fast `dDraw`: one answer's lanes 0–1. -/
def fDDraw : VF FE2 := VF.bind fSample fun a => VF.pure (fe2OfAns a)

theorem tw_dDraw : TwinF FE2.toE2 Lvm6.K.dDraw fDDraw := tw_sample fun a => tw_pure (e2OfE_chal a).symm

/-- Fast `dDraws n`. -/
def fDDraws : ℕ → VF (List FE2)
  | 0 => VF.pure []
  | n + 1 => VF.bind fDDraw fun x => VF.bind (fDDraws n) fun xs => VF.pure (x :: xs)

theorem tw_dDraws : ∀ n, TwinF (List.map FE2.toE2) (Lvm6.K.dDraws n) (fDDraws n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun x => Lvm6.K.dDraws n >>= fun xs => pure (x :: xs)) tw_dDraw fun x =>
      tw_bind (tw_dDraws n) fun xs => tw_pure rfl

/-- Fast `gPoint g n`. -/
def fGPoint (g n : ℕ) : VF (List FE2) :=
  VF.bind (fE2Sample g) fun c => VF.bind (fDDraws n) fun cs => VF.pure (c :: cs)

theorem tw_gPoint (g n : ℕ) : TwinF (List.map FE2.toE2) (Lvm6.K.gPoint g n) (fGPoint g n) :=
  tw_bind (tw_e2Sample g) fun c => tw_bind (tw_dDraws n) fun cs => tw_pure rfl

/-- A read's lane 0 as a `K` word (8 bytes or more: the word at its offset). -/
def decK (π : ByteArray) (o w : ℕ) : K :=
  if 8 ≤ w then FK.toBF64 (kAt π o) else (eOfBytes (((bl π).drop o).take w)).limb 0

theorem decK_eq (π : ByteArray) (o w : ℕ) : decK π o w = (eOfBytes (((bl π).drop o).take w)).limb 0 := by
  unfold decK
  split
  · rw [limb_eOfBytes]
    refine Lvm.VEq.toBF64_kAt_of π o _ fun i hi => ?_
    rw [show 8 * (0 : Fin 3).val = 0 from rfl, List.drop_zero, get!_bl, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
  · rfl

/-- Fast `kRead`. -/
def fKRead : VF K := fun π tr => (fRead π tr).map fun r => (decK π r.1.1 r.1.2, r.2)

theorem tw_kRead : TwinF id Lvm6.K.kRead fKRead :=
  twin_map' (R := readR) (fun x => x.limb 0) (fun π ow => decK π ow.1 ow.2) twin_read fun π ow x hR => by
    simp only [readR] at hR
    show decK π ow.1 ow.2 = _
    rw [decK_eq, hR]

/-- Fast `kReads n`. -/
def fKReads : ℕ → VF (List K)
  | 0 => VF.pure []
  | n + 1 => VF.bind fKRead fun x => VF.bind (fKReads n) fun xs => VF.pure (x :: xs)

theorem tw_kReads : ∀ n, TwinF id (Lvm6.K.kReads n) (fKReads n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun x => Lvm6.K.kReads n >>= fun xs => pure (x :: xs)) tw_kRead fun x =>
      tw_bind (tw_kReads n) fun xs => tw_pure rfl

/-! ## The first claim -/

theorem toE2_algebraMap (k : K) : FE2.toE2 (algebraMap K FE2 k) = algebraMap K E2 k := by
  apply QuadraticAlgebra.ext <;> rfl

/-- `x^z = nF (2^z)` for `z < 64`, in the word field. -/
def xsTab : Array FE2 := ((List.range 64).map fun z => (nF (2 ^ z) : FE2)).toArray

theorem xsTab_getD {z : ℕ} (hz : z < 64) : xsTab.getD z 0 = nF (2 ^ z) := by
  simp [xsTab, array_getD_toArrayF, List.getD_eq_getElem?_getD, hz]

/-- The first claim's weights (`firstWeightsF`) with the lane kernel and the powers tabulated. -/
def firstWArr (lp : List FE2) : Array FE2 :=
  let E := eqKernelAF lp
  ((List.range keccakBits).map fun j => E.getD (j / 64) 0 * xsTab.getD (j % 64) 0).toArray

theorem firstWArr_dec (lp : List FE2) :
    (firstWArr lp).toList.map FE2.toE2 = firstWeightsF (lp.map FE2.toE2) := by
  simp only [firstWArr, List.toList_toArray, List.map_map, firstWeightsF]
  refine List.map_congr_left fun j hj => ?_
  have hj : j < 1600 := by simpa [keccakBits] using hj
  simp only [Function.comp_apply]
  rw [xsTab_getD (Nat.mod_lt _ (by norm_num)), toE2_mul', arr_getD_toList, eqKernelAF_toList, toE2_getD,
    ← coe_tE, map_eqKernelF]
  congr 1
  all_goals exact toE2_algebraMap _

/-- The fast first claim (`firstClaimSF Shape.v1`). -/
def fFirst (inst segment lanesPt output : List FE2) (committed : FE2) : LClaim :=
  ⟨committed + (eqKernelF segment).getD (Shape.v1.segments - 1) 0 * dotF ((eqKernelF lanesPt).take 25) output,
    eqKernelF (inst.take 4), inst.drop 4 ++ segment, .mat (firstWArr lanesPt)⟩

theorem fFirst_dec (inst segment lanesPt output : List FE2) (committed : FE2) :
    (fFirst inst segment lanesPt output committed).dec = firstClaimSF Shape.v1 (inst.map FE2.toE2)
      (segment.map FE2.toE2) (lanesPt.map FE2.toE2) (output.map FE2.toE2) (FE2.toE2 committed) := by
  simp only [fFirst, LClaim.dec, WRep.dec, firstClaimSF, firstWArr_dec]
  simp only [← coe_tE, map_add, map_mul, map_getD, map_eqKernelF, map_dotF, List.map_take, List.map_drop,
    List.map_append]

/-! ## The reduction head -/

/-- `midWt` in the word field. -/
def midWtF (base : ℕ) (rseg : FE2) (rlane ϱ : List FE2) : FE2 :=
  (1 + rseg) * ∑ l ∈ range 25, eqAtF ϱ (base + l) * eqAtF rlane l

theorem toE2_midWtF (base : ℕ) (rseg : FE2) (rlane ϱ : List FE2) :
    FE2.toE2 (midWtF base rseg rlane ϱ) = Lvm6.K.midWt base (FE2.toE2 rseg) (rlane.map FE2.toE2) (ϱ.map FE2.toE2) := by
  simp only [midWtF, Lvm6.K.midWt, ← coe_tE, map_mul, map_add, map_one, map_sum, map_eqAtF]

/-- The head's output in the word field. -/
structure HeadOutF where
  sl : List FE2
  cst : FE2
  claim : LClaim
  ϱm : List FE2
  cout : FE2

/-- Its value in `E2`. -/
def HeadOutF.dec (h : HeadOutF) : Lvm6.K.HeadOut :=
  ⟨h.sl.map FE2.toE2, FE2.toE2 h.cst, h.claim.dec, h.ϱm.map FE2.toE2, FE2.toE2 h.cout⟩

/-- **Fast `kHead6 P base inst output`.** -/
def fKHead6 (P base : ℕ) (inst output : List FE2) : VF HeadOutF :=
  VF.bind (fGPoint Lvm6.K.gSeg 5) fun sl =>
  VF.bind fReadF fun cst =>
  VF.bind (fLayers (P + 4) (List.range 12) (fFirst inst (sl.take 1) (sl.drop 1) output cst)) fun claim =>
  VF.bind (fSumcheck gC2 cst 3 (List.replicate 6 none)) fun om =>
  VF.bind fReadF fun cout =>
  VF.guard (decide (midWtF base (sl.headD 0) (sl.drop 1) om.1 * cout = om.2))
    (VF.pure ⟨sl, cst, claim, om.1, cout⟩)

theorem toE2_headD (l : List FE2) : FE2.toE2 (l.headD 0) = (l.map FE2.toE2).headD 0 := map_headD tE l

theorem tw_kHead6 (P base : ℕ) (inst output : List FE2) :
    TwinF HeadOutF.dec (Lvm6.K.kHead6 P base (inst.map FE2.toE2) (output.map FE2.toE2))
      (fKHead6 P base inst output) := by
  unfold Lvm6.K.kHead6
  refine tw_bind (tw_gPoint _ _) fun sl => tw_bind tw_e2Read fun cst => ?_
  rw [← List.map_take, ← List.map_drop, ← fFirst_dec]
  refine tw_bind (tw_layers6 _ _ _) fun claim => ?_
  refine tw_bind (tw_sumcheckPlain gC2 3 6 cst) fun om => ?_
  refine tw_bind tw_e2Read fun cout => ?_
  refine tw_guard _ _ ?_ (tw_pure rfl)
  refine Iff.trans (Eq.congr_left ?_) (toE2_eq_iff _ _)
  rw [toE2_mul', toE2_midWtF, toE2_headD]
  rfl

/-! ## The tree batch -/

/-- The weights materialized (after the layers). -/
def WRep.arr : WRep → Array FE2
  | .mat w => w
  | .tro _ A ℓ _ _ => (linearTransposeF (outerUGF A ℓ)).toArray

/-- A claim with materialized weights. -/
def toKF (c : LClaim) : KClaimF := ⟨c.value, c.mu, c.point, c.W.arr⟩

theorem toKF_dec (c : LClaim) : (toKF c).dec = c.dec := by
  cases c with
  | mk v mu pt W =>
    cases W with
    | mat w => rfl
    | tro pA A ℓ hp hA =>
      simp only [toKF, KClaimF.dec, LClaim.dec, WRep.arr, WRep.dec, List.toList_toArray]
      rw [← coe_tE, map_linearTransposeF, map_outerUGF]

/-- `oLow` in the word field. -/
def oLowF (u : FE2) (dd : List FE2) : List FE2 :=
  (List.range 4).map fun m => (1 + u) * dd.getD m 0 + u * dd.getD (4 + m) 0

theorem map_oLowF (u : FE2) (dd : List FE2) : (oLowF u dd).map FE2.toE2 = Lvm6.K.oLow (FE2.toE2 u) (dd.map FE2.toE2) := by
  simp only [oLowF, Lvm6.K.oLow, List.map_map, Function.comp_def, ← coe_tE, map_add, map_mul, map_one, map_getD]

/-- The tree batch's output in the word field. -/
structure TreeOutF where
  δ : List K
  ρ : List FE2
  dd : List FE2
  u : FE2
  o : List FE2
  hd : HeadOutF
  en : EndOutF

/-- Its value in `E2`. -/
def TreeOutF.dec (t : TreeOutF) : Lvm6.K.TreeOut :=
  ⟨t.δ, t.ρ.map FE2.toE2, t.dd.map FE2.toE2, FE2.toE2 t.u, t.o.map FE2.toE2, t.hd.dec, t.en.dec⟩

/-- **Fast `treeProg κ`.** -/
def fTreeProg (κ : ℕ) : VF TreeOutF :=
  VF.bind (fKReads 4) fun δ =>
  VF.bind (fGPoint Lvm6.K.gRho (κ - 2)) fun ρ =>
  VF.bind (fE2Reads 8) fun dd =>
  VF.bind (fE2Sample Lvm6.K.gU) fun u =>
  VF.bind (fE2Reads 21) fun o' =>
  VF.bind (fKHead6 (κ - 4) 8 (u :: ρ) (oLowF u dd ++ o')) fun hd =>
  VF.bind (fTreeEnd6 (κ - 4) (toKF hd.claim)) fun en =>
  VF.pure ⟨δ, ρ, dd, u, oLowF u dd ++ o', hd, en⟩

theorem tw_treeProg (κ : ℕ) : TwinF TreeOutF.dec (Lvm6.K.treeProg κ) (fTreeProg κ) := by
  unfold Lvm6.K.treeProg
  refine tw_bind (tw_kReads 4) fun δ => tw_bind (tw_gPoint _ _) fun ρ => tw_bind (tw_e2Reads 8) fun dd =>
    tw_bind (tw_e2Sample _) fun u => tw_bind (tw_e2Reads 21) fun o' => ?_
  rw [← List.map_cons, ← map_oLowF, ← List.map_append]
  refine tw_bind (tw_kHead6 _ _ _ _) fun hd => ?_
  rw [show (HeadOutF.dec hd).claim = (toKF hd.claim).dec from (toKF_dec _).symm]
  exact tw_bind (tw_treeEnd6 _ _) fun en => tw_pure rfl

/-! ## The tree phase -/

/-- The tree phase's output in the word field: the slices and the column claims as point claims. -/
structure TreeSF where
  pt : List FE2
  s : List FE2
  cols : List (List FE2 × FE2)

/-- A point claim's value: `(eq(p, ·), v)`. -/
def pcDec (c : List FE2 × FE2) : StackClaim6 := (fun q => eqPt (c.1.map FE2.toE2) q, FE2.toE2 c.2)

/-- Its value in `E2` (WP S's `TreeOut`). -/
def TreeSF.dec (t : TreeSF) : Lvm6.TreeOut :=
  ⟨⟨t.pt.map FE2.toE2, fun z => (t.s.map FE2.toE2).getD z 0⟩, t.cols.map pcDec⟩

/-- `treeColsS` (ORD's order: `c_out` first, then the wiring and root claims) in the word field. -/
def treeColsF (κ : ℕ) (h : Digest) (out : TreeOutF) : List (List FE2 × FE2) :=
  ((out.u :: out.ρ) ++ out.hd.ϱm, out.hd.cout) ::
    ((List.range 4).map (fun m ↦ (out.ρ ++ [0] ++ bitsF m 6,
      out.dd.getD m 0 + eqAtF out.ρ 0 * algebraMap K FE2 (out.δ.getD m 0))) ++
    (List.range 4).map (fun m ↦ (out.ρ ++ [0] ++ bitsF (4 + m) 6, out.dd.getD (4 + m) 0)) ++
    (List.range 4).map (fun m ↦ (bitsF 0 κ ++ bitsF (4 + m) 6, algebraMap K FE2 (K.ofLane (dLane h m)))))

theorem map_bitsF {F F' : Type} [Field F] [Field F'] (φ : F →+* F') :
    ∀ (z m : ℕ), (bitsF z m : List F).map φ = bitsF z m
  | _, 0 => rfl
  | z, m + 1 => by simp only [bitsF, List.map_cons, apply_ite (⇑φ), map_one, map_zero, map_bitsF φ (z / 2) m]

theorem treeColsF_dec (κ : ℕ) (h : Digest) (out : TreeOutF) :
    (treeColsF κ h out).map (fun c => (c.1.map FE2.toE2, FE2.toE2 c.2)) = Lvm6.K.treeColsS κ h out.dec := by
  have hA : ∀ k : K, tE (algebraMap K FE2 k) = algebraMap K E2 k := toE2_algebraMap
  simp only [treeColsF, Lvm6.K.treeColsS, TreeOutF.dec, HeadOutF.dec, List.map_append, List.map_map,
    Function.comp_def, List.map_cons, List.map_nil, ← coe_tE, map_add, map_mul, map_zero, map_eqAtF, map_getD,
    map_bitsF tE, hA, kF]

/-- `toS` in the word field. -/
def toSF (κ : ℕ) (h : Digest) (out : TreeOutF) : TreeSF := ⟨out.en.pt, out.en.s, treeColsF κ h out⟩

theorem toSF_dec (κ : ℕ) (h : Digest) (out : TreeOutF) : (toSF κ h out).dec = Lvm6.K.toS κ h out.dec := by
  unfold toSF TreeSF.dec Lvm6.K.toS
  rw [← treeColsF_dec, List.map_map]
  rfl

/-- **Fast `treeProgS sh x`.** -/
def fTreeProgS (sh : Lvm6.Shape) (x : Lvm6.Hdr) : VF TreeSF :=
  if sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN then
    VF.bind (fTreeProg (sh.logN + 1)) fun out => VF.pure (toSF (sh.logN + 1) x.h out)
  else fun _ _ => none

theorem tw_treeProgS (sh : Lvm6.Shape) (x : Lvm6.Hdr) : TwinF TreeSF.dec (Lvm6.K.treeProgS sh x) (fTreeProgS sh x) := by
  unfold Lvm6.K.treeProgS fTreeProgS
  split
  · exact tw_bind (tw_treeProg _) fun out => tw_pure (toSF_dec _ _ _)
  · intro π tr
    rw [replayP_fail]
    exact Option.Rel.none

end Lvm6.V
