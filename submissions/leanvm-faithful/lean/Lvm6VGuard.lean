-- New for lvm6 (WP V1c): the static guard of `V_S` (season 1's A24 pattern, `Lvm.Fin.VSg`, `subGF`): the facts about
-- the deployed typed instance that the kernel cannot evaluate are one closed Bool (`staticOk6`), evaluated by the
-- compiled `V` once per process; with it true the instance `inst6` is built from `staticOk6_sound`'s proof and `V_S`
-- runs the fast decision `F`; with it false every `S` proof is rejected. The guarded verifiers are equal
-- (`VSF6_eq`), whatever the guard's value.
import Lvm6VTwF
import Lvm6VTwFPhi
import Lvm6VPhiChkQ
import Lvm6VPhiChkG
import Lvm6NodeBits
import Lvm6NodeGuardC
import Lvm6NodeKS
import Lvm6NodeMaps
import Lvm6Chk
import Lvm6NodeAsmChk
import Lvm6LayOkF
import Lvm6GspGrd
import Lvm6GspAsm
import Lvm6GspKS
import Lvm6NodeLayF
import Lvm6NodeLay

/-!
# The static guard (A24, v6)

* `VSg b VS` (season 1's `Lvm.Fin.VSg`): `VS` when `b`, else `.ret false`.
* **`TyBase6`**: what the typed instance's owners supply from the exporter's definitions (at NODE3's lanes and
  LAY5's `bOf`): the instance `Ti`, the class table `P`, and its facts proved by construction.
* `tyLayOkB` (word by word, kept for `staticOk6_ref`) and **`tyLayOkRB`**, **`tyLayOkRB_sound`** (per region, given
  `MapsReg`): `TyLayOk` at run time, `StreamRegs6`'s witnesses given.
* **`staticOk6 B`** = `lay.okB Q && regsOkB && phiChk Q lay P && mbLinB6 && tyLayOkRB && oneB && mapsFitRB
  && nodeLayB3 && grdB && ksAliasChk.b && asmChk6.b` (NODE3, GRD, KSA, NODE5b), each run as a fast twin with a
  proved `_eq` (GSP's `okBX`, `regsOkBH`, `grdBX`, `ksAliasBH`, `asmB6H`; PHF's `phiChkG`; SU2's `nodeLayB3C`); its facts as named fields: `StaticOk6`, `Deployed6`,
  **`staticOk6_ok`**, `staticChk6`; **`staticOk6_sound`** (a corollary). No budget conjunct (decision 2026-11-23: no
  theorem read it; `V`'s time is the harness's cap and the timing gates; `PhiBudget` stays frozen, unused).
  `staticOk6_ref B budget` (development only, STARTUP F5): the guard as of NODE3c `bd9af9e3`. The class table is
  checked by ST-4's `phiChk` (rows of `Q`, `cancelChk`), its fact `PhiOk P.eval Q lay` by `phiChk_ok`. The layout
  check runs GSP's `okBX` (`okBX_eq`: `Lay.okB` and `noE3B`'s auxiliary rows).
* **`inst6 B h`**: the deployed `TyInst6` at a header, from the guard's proof `h`.
* `VSF6`/`VSspec6`: `V_S` with `F`, resp. ASM's `VSasm`, behind the guard; **`VSF6_eq`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-- **`V_S` behind the guard `b`** (season 1's `Lvm.Fin.VSg`): `VS` when `b`, else reject. -/
def VSg (b : Bool) (VS : Digest → Digest → Proof → OProg Bool) : Digest → Digest → Proof → OProg Bool :=
  fun vk c π => if b then VS vk c π else OProg.ret false

theorem VSg_true (VS : Digest → Digest → Proof → OProg Bool) : VSg true VS = VS := rfl

theorem VSg_false (VS : Digest → Digest → Proof → OProg Bool) (vk c : Digest) (π : Proof) :
    VSg false VS vk c π = OProg.ret false := rfl

/-- **`TyLayOk` at run time**, with the witnesses of `StreamRegs6` (the `S_flat` and `σ` region bases) given. -/
def tyLayOkB (Ti : Ty.TInst6) (bs bg : ℕ) : Bool :=
  decide (Ti.lay.yregs.filter (fun r ↦ r.src == .sflat) = [⟨bs, Ty.relayRounds, .sflat⟩]) &&
  decide (Ti.lay.yregs.filter (fun r ↦ r.src == .sigma) = [⟨bg, QD.sigLog, .sigma⟩]) &&
  (List.range (2 ^ Ty.relayRounds)).all (fun p => decide (Ti.sflatW (bs + p) = p)) &&
  (List.range (2 ^ QD.sigLog)).all (fun j => decide (Ti.sigmaW (bg + j) = QD.sB + j)) &&
  decide (Ti.lay.yregs.filter (fun r ↦ r.src == .pub) = [⟨QD.pubBase Ti, 10, .pub⟩]) &&
  Ti.lay.yregs.all (fun r => decide (r.src ≠ .qlt))

theorem tyLayOkB_sound {Ti : Ty.TInst6} {bs bg : ℕ} (h : tyLayOkB Ti bs bg = true) : QD.TyLayOk Ti := by
  simp only [tyLayOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨⟨bs, bg, h1, h2, fun p hp => h3 p hp, fun j hj => h4 j hj⟩, h5, fun r hr => h6 r hr⟩

/-- **The word `1` lies in a `one` region**, at run time (NODE3: was `TyBase6.one`). -/
def oneB (Ti : Ty.TInst6) : Bool := decide (Ti.src? Ti.lay.one = some .one)

theorem oneB_sound {Ti : Ty.TInst6} (h : oneB Ti = true) : Ti.src? Ti.lay.one = some .one := of_decide_eq_true h

/-- One word's region map lands in its commitment (`Ty.TInst6.MapsFit`'s case for `y`). -/
def mapOkB (Ti : Ty.TInst6) (L : Lvm.M3.Lay) (y : ℕ) : Bool :=
  match Ti.src? y with
  | some .com => decide (Ti.comW y < 2 ^ L.nuMain)
  | some .ks => decide (Ti.ksW y < 2 ^ L.nuMain)
  | some .sflat => decide (Ti.sflatW y < 2 ^ L.nuRec)
  | some .sigma => decide (Ti.sigmaW y < 2 ^ L.nuRec)
  | _ => true

/-- **`MapsFit` at run time** (NODE3: was `TyBase6.maps`): every word of every region. -/
def mapsFitB (Ti : Ty.TInst6) (L : Lvm.M3.Lay) : Bool :=
  Ti.lay.yregs.all fun r ↦ (List.range (2 ^ r.log)).all fun j ↦ mapOkB Ti L (r.base + j)

theorem mapsFitB_sound {Ti : Ty.TInst6} {L : Lvm.M3.Lay} (h : mapsFitB Ti L = true) : Ti.MapsFit L := by
  intro y
  have key : mapOkB Ti L y = true ∨ Ti.src? y = none := by
    cases hs : Ti.src? y with
    | none => exact Or.inr rfl
    | some s =>
      left
      unfold Ty.TInst6.src? at hs
      obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp hs
      have hp := List.find?_some hr
      have hm := List.mem_of_find?_eq_some hr
      simp only [decide_eq_true_eq] at hp
      simp only [mapsFitB, List.all_eq_true, List.mem_range] at h
      have := h r hm (y - r.base) (by omega)
      rwa [show r.base + (y - r.base) = y by omega] at this
  rcases key with hk | hk
  · unfold mapOkB at hk
    split at hk <;> rename_i heq <;> simp only [heq] <;> simp_all
  · simp only [hk]


/-- **`MapsFit` per region** (STARTUP ST-2, coordinator's decision 1): a `com`/`S_flat`/`σ′` region's target and size
fit the commitment (its words map affinely, `MapsReg`, `regW6_affine`); a `KS` region word by word. -/
def mapsFitRB (Ti : Ty.TInst6) (L : Lvm.M3.Lay) : Bool :=
  Lvm6.Node.Dep.yDisjB Ti.lay.yregs && Ti.lay.yregs.all fun r ↦
    match r.src with
    | .com => decide (Lvm6.Node.Dep.regTgt Ti.lay r + 2 ^ r.log ≤ 2 ^ L.nuMain)
    | .sflat => decide (Lvm6.Node.Dep.regTgt Ti.lay r + 2 ^ r.log ≤ 2 ^ L.nuRec)
    | .sigma => decide (Lvm6.Node.Dep.regTgt Ti.lay r + 2 ^ r.log ≤ 2 ^ L.nuRec)
    | .ks => (List.range (2 ^ r.log)).all fun j ↦ decide (Ti.ksW (r.base + j) < 2 ^ L.nuMain)
    | _ => true

theorem mapsFitRB_sound {Ti : Ty.TInst6} {L : Lvm.M3.Lay} (hM : Lvm6.Node.Dep.MapsReg Ti)
    (h : mapsFitRB Ti L = true) : Ti.MapsFit L := by
  simp only [mapsFitRB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hd, hr⟩ := h
  refine mapsFitB_sound (List.all_eq_true.mpr fun r hrm ↦ List.all_eq_true.mpr fun j hj ↦ ?_)
  have hj' : j < 2 ^ r.log := List.mem_range.mp hj
  have hsrc := Lvm6.Node.Dep.src?_of_mem hd hrm (y := r.base + j) ⟨by omega, by omega⟩
  have hR := hr r hrm
  unfold mapOkB
  rw [hsrc]
  rcases hs : r.src with _ | _ | _ | _ | _ | _ | _ <;> simp only [hs] at hR ⊢
  · rw [hM.1, Lvm6.Node.Dep.regW6_affine _ hd hrm hs hj']
    simp only [decide_eq_true_eq] at hR ⊢
    show Lvm6.Node.Dep.regTgt Ti.lay r + j < _
    omega
  · rw [hM.2.1, Lvm6.Node.Dep.regW6_affine _ hd hrm hs hj']
    simp only [decide_eq_true_eq] at hR ⊢
    show Lvm6.Node.Dep.regTgt Ti.lay r + j < _
    omega
  · rw [hM.2.2, Lvm6.Node.Dep.regW6_affine _ hd hrm hs hj']
    simp only [decide_eq_true_eq] at hR ⊢
    show Lvm6.Node.Dep.regTgt Ti.lay r + j < _
    omega
  · exact List.all_eq_true.mp hR j hj

/-- **`TyLayOk` per region** (STARTUP ST-2): the regions disjoint, the `S_flat`/`σ`/`PUB` regions as `TyLayOk`
names them, no `QLT` region; the words of the `S_flat` and `σ` regions follow from `MapsReg` (`regW6_affine`),
no loop over their `2^19 + 2^11` words. -/
def tyLayOkRB (Ti : Ty.TInst6) (bs bg : ℕ) : Bool :=
  Lvm6.Node.Dep.yDisjB Ti.lay.yregs &&
  decide (Ti.lay.yregs.filter (fun r ↦ r.src == .sflat) = [⟨bs, Ty.relayRounds, .sflat⟩]) &&
  decide (Ti.lay.yregs.filter (fun r ↦ r.src == .sigma) = [⟨bg, QD.sigLog, .sigma⟩]) &&
  decide (Ti.lay.yregs.filter (fun r ↦ r.src == .pub) = [⟨QD.pubBase Ti, 10, .pub⟩]) &&
  Ti.lay.yregs.all (fun r => decide (r.src ≠ .qlt))

theorem tyLayOkRB_sound {Ti : Ty.TInst6} {bs bg : ℕ} (hM : Lvm6.Node.Dep.MapsReg Ti) (h : tyLayOkRB Ti bs bg = true) :
    QD.TyLayOk Ti := by
  simp only [tyLayOkRB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hd, h1⟩, h2⟩, h5⟩, h6⟩ := h
  have hr1 : (⟨bs, Ty.relayRounds, .sflat⟩ : Lvm.Typed.YReg) ∈ Ti.lay.yregs :=
    (List.mem_filter.mp (h1 ▸ List.mem_singleton_self _)).1
  have hr2 : (⟨bg, QD.sigLog, .sigma⟩ : Lvm.Typed.YReg) ∈ Ti.lay.yregs :=
    (List.mem_filter.mp (h2 ▸ List.mem_singleton_self _)).1
  refine ⟨⟨bs, bg, h1, h2, fun p hp => ?_, fun j hj => ?_⟩, h5, fun r hr => h6 r hr⟩
  · rw [hM.2.1]
    exact (Lvm6.Node.Dep.regW6_affine _ hd hr1 rfl hp).trans (Nat.zero_add p)
  · rw [hM.2.2]
    exact Lvm6.Node.Dep.regW6_affine _ hd hr2 rfl hj

/-- **The stream and signature regions** (named, for NODE5b's readers): the regions disjoint, the `S_flat` region at
`bs`, the `σ` region at `bg`. -/
structure StreamRegsAt6 (Ti : Ty.TInst6) (bs bg : ℕ) : Prop where
  disj : Lvm6.Node.Dep.yDisjB Ti.lay.yregs = true
  sflat : (⟨bs, Ty.relayRounds, .sflat⟩ : Lvm.Typed.YReg) ∈ Ti.lay.yregs
  sigma : (⟨bg, QD.sigLog, .sigma⟩ : Lvm.Typed.YReg) ∈ Ti.lay.yregs

theorem tyLayOkRB_regs {Ti : Ty.TInst6} {bs bg : ℕ} (h : tyLayOkRB Ti bs bg = true) : StreamRegsAt6 Ti bs bg := by
  simp only [tyLayOkRB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hd, h1⟩, h2⟩, -⟩, -⟩ := h
  exact ⟨hd, (List.mem_filter.mp (h1 ▸ List.mem_singleton_self _)).1,
    (List.mem_filter.mp (h2 ▸ List.mem_singleton_self _)).1⟩

/-- **The deployed typed instance's base**: the instance and its class table, with the facts its owners prove by
construction (the exporter's definitions at NODE3's lanes and LAY5's `bOf`). -/
structure TyBase6 where
  Ti : Ty.TInst6
  P : PT
  /-- The witnesses of `StreamRegs6`: the bases of the `S_flat` and `σ` regions. -/
  bs : ℕ
  bg : ℕ
  hτ : ∀ t ∈ Ti.mbT, t.τ ≤ Ty.L6.μ
  sc : Lvm.M3.AllSc Ti.mbT
  lay : Lvm.M3.LayOk Ty.L6 Ti.mbT
  keys : Lvm.M3.KeysOk Ti.mbT
  fix : Lvm.M3.FixOk Ti.mbT
  μBus : (Lvm.M3.inst Ty.L6 Ti.mbT hτ).μBus = Lvm6.Mb.miniDepth
  /-- The word maps are region-affine by construction (`regW6`; NODE3, STARTUP ST-2). -/
  mapsReg : Lvm6.Node.Dep.MapsReg Ti

/-- **The runtime guard**: the layout of `Q`, the factored region claims, the class table against `Q`'s rows
(ST-4's `phiChk`, run as PHF's fused twin `phiChkG`; `phiChkG_eq`), the mini-bus's linear tables, the regions (`tyLayOkRB`, `mapsFitRB`: per region), the node's cells
(`nodeLayB3`, by SU2's equal `nodeLayB3C` with the deployed layout's pointer cache; GRD's `grdB`, KSA's
`ksAliasChk`), NODE5b's `asmChk6` (cell count, stream cells, `readd`). No budget
conjunct (decision of 2026-11-23). GSP: `ksAliasChk`, `asmChk6` run as their twins (`ksAliasBH_eq`, `asmB6H_eq`);
`Lay.okB` and `grdB` as `okBX` (`okBX_eq`: `okB` and `noE3B`'s auxiliary rows, walked once) and `grdBX`
(`grdB_of_grdBX`); `regsOkB` as `regsOkBH` (`regsOkB_of_regsOkBH`, given `MapsReg`). -/
def staticOk6 (B : TyBase6) : Bool :=
  Lvm6.Gsp.okBX B.Ti.lay B.Ti.Q && Lvm6.Gsp.regsOkBH B.Ti && phiChkG B.Ti.Q B.Ti.lay B.P && Lvm6.Mb.mbLinB6 B.Ti.mbT &&
    tyLayOkRB B.Ti B.bs B.bg && oneB B.Ti && mapsFitRB B.Ti Ty.L6 &&
    Lvm6.Node.Dep.nodeLayB3C Lvm6.Node.LayQ.layR6 Lvm6.Node.LayQ.pS0 B.Ti &&
    Lvm6.Gsp.grdBX B.Ti (Lvm6.Node.Dep.cellPar6 B.bs B.bg) && Lvm6.Gsp.ksAliasBH B.Ti &&
    Lvm6.Gsp.asmB6H B.Ti

/-- **Development only (STARTUP F5)**: the guard as of NODE3c `bd9af9e3` (with its `budget` argument and the
word-by-word `tyLayOkB`), kept so that INT, R7 and the KATs run with a relaxed local `badge_start_s`; not
submittable. -/
def staticOk6_ref (B : TyBase6) (budget : Bool) : Bool :=
  B.Ti.lay.okB B.Ti.Q && regsOkB B.Ti && ptCheck B.P (Ty.entsE B.Ti.Q B.Ti.lay) && Lvm6.Mb.mbLinB6 B.Ti.mbT &&
    budget && tyLayOkB B.Ti B.bs B.bg && oneB B.Ti && mapsFitRB B.Ti Ty.L6 && Lvm6.Node.Dep.nodeLayB3 B.Ti &&
    Lvm6.Node.Dep.grdB B.Ti (Lvm6.Node.Dep.cellPar6 B.bs B.bg) && (Lvm6.Node.Dep.ksAliasChk B.Ti).b

/-! ## The guard's facts as named fields (PF-1) -/

/-- **The node's deployed run-time facts** (PFW `NodeLay.Deployed`), one named field each. -/
structure Deployed6 (Ti : Ty.TInst6) (bs bg : ℕ) : Prop where
  pow : ∀ a ∈ Lvm6.Node.Dep.powAns, ∃ bw, Lvm.Q2.powBlk a.2 bw a.1 ∈ Ti.lay.aux
  cst : Ti.lay.cst = [(Lvm6.Node.Dep.zC, [0]), (Lvm6.Node.Dep.qtC, Lvm6.Q.qltData6 Lvm6.Node.P6 Lvm6.Node.Dep.lay6)]
  pub : ∀ l < 2 ^ 10, Ti.lay.cst? (Lvm6.Node.Dep.pbC + l) = none ∧
    Ti.lay.wordK (Lvm6.Node.Dep.pbC + l) = QD.pubBase Ti + l ∧ Ti.src? (QD.pubBase Ti + l) = some .pub
  noPub : (∀ j < 2 ^ 19, Ti.src? (Ti.lay.wordK (Lvm6.Node.Dep.sbC + j)) ≠ some .pub) ∧
    (∀ i < 597, Ti.src? (Ti.lay.wordK (Lvm6.Node.Dep.sgC + i)) ≠ some .pub) ∧
    (∀ i < 597, Ti.src? (Ti.lay.wordK (Lvm6.Node.Dep.dstC + i)) ≠ some .pub)
  bits : ∀ S ∈ Lvm6.Node.Dep.bitsSpecs6 Ti.lay, ∀ x < S.n, ∃ w, Lvm6.Node.Dep.boolBlk6 S w x ∈ Ti.lay.aux ∧
    Lvm6.Node.Dep.outBlk6 S w x ∈ Ti.lay.aux
  regCom : QC.RegAff Ti .com Ti.comW (Lvm6.Node.Dep.regsOf Ti.lay .com)
  regKs : QC.RegAff Ti .ks Ti.ksW (Lvm6.Node.Dep.regsOf Ti.lay .ks)
  grd : Lvm6.Node.Dep.GrdFacts Ti (Lvm6.Node.Dep.cellPar6 bs bg)
  ks : Lvm6.Node.Dep.KSAliasOk Ti

/-- **The static guard's facts** (PFW `StaticOk6`), one named field each. -/
structure StaticOk6 (B : TyBase6) : Prop where
  lay : B.Ti.lay.okB B.Ti.Q = true
  regs : regsOkB B.Ti = true
  /-- The class table against `Q`'s rows (ST-4; `phiChk_ok` gives `PhiOk`). -/
  phi : phiChk B.Ti.Q B.Ti.lay B.P = true
  mbLin : Lvm6.Mb.mbLinB6 B.Ti.mbT = true
  tyLay : QD.TyLayOk B.Ti
  one : B.Ti.src? B.Ti.lay.one = some .one
  maps : B.Ti.MapsFit Ty.L6
  node : Deployed6 B.Ti B.bs B.bg
  /-- The stream and signature regions (from `tyLayOkRB`). -/
  streamRegs : StreamRegsAt6 B.Ti B.bs B.bg
  /-- NODE5b's assembly facts (`asmChk6`). -/
  asm : Lvm6.Node.Asm.AsmOk6 B.Ti

/-- **The guard's Bool gives its facts.** -/
theorem staticOk6_ok {B : TyBase6} (h : staticOk6 B = true) : StaticOk6 B := by
  simp only [staticOk6, Lvm6.Gsp.okBX_eq, phiChkG_eq,
    Lvm6.Node.Dep.nodeLayB3C_eq Lvm6.Node.LayQ.pS0_eq, Lvm6.Node.Dep.nodeLayB3, Lvm6.Node.Dep.nodeLayB,
    Lvm6.Gsp.ksAliasBH_eq, Lvm6.Gsp.asmB6H_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hax⟩, hreg⟩, hpt⟩, hlin⟩, hty⟩, hone⟩, hmaps⟩,
    ⟨⟨⟨⟨⟨hpow, hqlt⟩, hpub⟩, hnp⟩, hbits⟩, hcc⟩⟩, hgrd⟩, hksa⟩, hasm⟩ := h
  have hcr := Lvm6.Node.Dep.ccRegsRB_sound B.mapsReg hcc
  exact ⟨hok, Lvm6.Gsp.regsOkB_of_regsOkBH B.mapsReg hreg, hpt, hlin, tyLayOkRB_sound B.mapsReg hty, oneB_sound hone, mapsFitRB_sound B.mapsReg hmaps,
    ⟨Lvm6.Node.Dep.powAuxInB_sound hpow, Lvm6.Node.Dep.qltCstB_sound hqlt,
      Lvm6.Node.Dep.pubCellsB_sound hok hpub, Lvm6.Node.Dep.noPubB_sound hok hnp,
      Lvm6.Node.Dep.bitsAuxInB_sound hbits, hcr.1, hcr.2, Lvm6.Node.Dep.grdB_sound hok (Lvm6.Gsp.grdB_of_grdBX hax hgrd),
      (Lvm6.Node.Dep.ksAliasChk B.Ti).sound hksa⟩, tyLayOkRB_regs hty, (Lvm6.Node.Asm.asmChk6 B.Ti).sound hasm⟩

/-- **The guard as a `Chk`** (PF-0): the Bool `staticOk6`, its facts `StaticOk6`. -/
def staticChk6 (B : TyBase6) : Lvm6.Node.Chk (StaticOk6 B) :=
  Lvm6.Node.Chk.ofBool (staticOk6 B) staticOk6_ok

/-- `staticOk6_sound` (a corollary of `staticOk6_ok`, kept until INT moves its consumers to the fields). -/
theorem staticOk6_sound {B : TyBase6} (h : staticOk6 B = true) :
    B.Ti.lay.okB B.Ti.Q = true ∧ regsOkB B.Ti = true ∧ phiChk B.Ti.Q B.Ti.lay B.P = true ∧
      Lvm6.Mb.mbLinB6 B.Ti.mbT = true ∧ QD.TyLayOk B.Ti ∧
      B.Ti.src? B.Ti.lay.one = some .one ∧ B.Ti.MapsFit Ty.L6 ∧ Deployed6 B.Ti B.bs B.bg :=
  let o := staticOk6_ok h
  ⟨o.lay, o.regs, o.phi, o.mbLin, o.tyLay, o.one, o.maps, o.node⟩

/-- The accumulator of a header, `phiVarsE` coordinates (padded or cut; a parsed header has exactly that many). -/
def accFix (x : Hdr) : List E2 × E2 :=
  ((x.accIn.1 ++ List.replicate Ty.phiVarsE 0).take Ty.phiVarsE, x.accIn.2)

theorem accFix_len (x : Hdr) : (accFix x).1.length = Ty.phiVarsE := by
  simp [accFix]

/-- **The deployed typed instance at a header** (public words `pwOf` of the header's bytes, accumulator `accFix`),
built from the guard's proof. -/
def inst6 (B : TyBase6) (h : staticOk6 B = true) (x : Hdr) :
    Ty.TyInst6 :=
  ⟨B.Ti, QD.pwOf B.Ti (Lvm6.hdrBytes x), accFix x, B.hτ, ⟨(staticOk6_ok h).lay, (staticOk6_ok h).one⟩,
    (staticOk6_ok h).maps, accFix_len x, B.sc, B.lay, B.keys, B.fix, (staticOk6_ok h).mbLin, B.μBus⟩

/-- **`V_S` with the fast decision behind the guard.** -/
def VSF6 (B : TyBase6) (sh : Lvm6.Shape) : Digest → Digest → Proof → OProg Bool :=
  fun vk c π => if h : staticOk6 B = true then VS6 (toV sh) (F (inst6 B h) B.P sh) vk c π else OProg.ret false

/-- **ASM's `V_S` behind the guard** (the specified verifier). -/
noncomputable def VSspec6 (B : TyBase6) (sh : Lvm6.Shape) : Digest → Digest → Proof → OProg Bool :=
  fun vk c π => if h : staticOk6 B = true then VSasm (phasesV (inst6 B h)) sh vk c π else OProg.ret false

/-- **The guarded verifiers are equal**, for either value of the guard: off, both reject; on, `F_VS` with the
instance built from the guard's proof (`F_VS_phi`, `PhiOk` by `phiChk_ok`). `hMA` is the multiaffinity the fast opening needs (W1's `openSpec18`);
C1: on shapes with `P18`'s `M` (`hM`; `Lvm6CertMA.VSF6_eqP18` discharges both at `P18`). -/
theorem VSF6_eq (B : TyBase6) (sh : Lvm6.Shape) (hM : sh.M = P18.M)
    (hMA : ∀ h : staticOk6 B = true, MAOK (inst6 B h)) : VSF6 B sh = VSspec6 B sh := by
  funext vk c π
  unfold VSF6 VSspec6
  split
  · rename_i h
    exact F_VS_phi (inst6 B h) B.P (fun _ => (staticOk6_ok h).tyLay)
      (fun _ => phiChk_ok (staticOk6_ok h).lay (staticOk6_ok h).phi)
      (fun _ => (staticOk6_ok h).regs) (hMA h) sh hM vk c π
  · rfl

end Lvm6.V
