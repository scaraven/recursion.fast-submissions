-- New for lvm2 (roll 8 = B1; statements by L-D, proofs owner L-H): the typed HAR, the circuit-soundness half of
-- `nodeT20`. Roll 7's `harith20` (`LvmFinHB`) / `harith_core` (`LvmQAsmHarMain`) for the B program: wherever the B
-- program's Q_arith (`qaB = phases47 >>= qarithB`) holds and asserts on a pair's memory, V_S's typed decision on the
-- child's stream accepts and folds to the statement's incoming accumulator. `harithT20`'s statement is L-D's (the form
-- `LvmNodeSoundT.nodeSoundT` consumes); L-H's proofs, with the parts in `LvmQTypedHar{T,G,C,Z,R,A,M}`.
import LvmNodeSoundT
import LvmQAsmHarP47
import LvmQAsmHarLink20
import LvmQTypedHarT
import LvmQTypedHarC
import LvmQTypedHarG
import LvmQAsmArith2WhirP
import LvmAccNodePub

/-!
# The typed HAR at `P20`

**Headline** (fixed; `nodeT20` consumes it with L-D's glue: `decideFT = decideCoreT ∧ Φ_Q(acc_out) = y`, the last
from `AccOkT` and `PhiQC_eq` through `S.cache`):

* **`harithT20 S H`**: on a node statement (`okS`, `b = 1`) and a good pair, with the input map on the pair's memory
  (`InMapM`), the child's stream a trace of the schedule (`LaneLink`, `LinkOk`), `qaB`'s segments holding and
  asserting at Q_arith's pointer, and the memory facts of the `BITS` rows (`BVT`, roll 7's `BVFacts` on `memT`;
  L-D proves them from the typed `BITS` rows): `decideCoreT P20 NT20 vk c_L Σ' = true` and
  `accOutOfT P20 NT20 vk c_L Σ' = acc_in`.

**Parts** (the static `Bool` check they need, `harChkB`, is L-W's guard field `S.har`, as roll 7's `S.hwr`, `S.hwm`,
`S.hwz`):

1. **`core_of_phasesT`** (`LvmQTypedHarT`; the composition, as `core_of_phases`): `decideCoreT ∧ accOutOfT = acc` from the typed phases'
   `PhaseAt` (`dTypedT`), phases 4–7 (`tapePh`, `wirePhC`, `ksPh`, `ksLinkPh`, unchanged) and the openings
   (`dOpenT` at `smallT`).
2. **`typedG_replays`** (the typed core gadget; restated with the guard `S` and the stream bounds): `typedG` replays `dTypedT` from `typedPos P20` to
   `typedEnd tdata20 (typedPos P20)`; its values are the cells' (the folded accumulator is `PUB`'s `acc_in`, the
   typed claims are `typedClaimsN` of the cells, the mini-bus's evaluations the table cells').
3. **Phases 4–7**: roll 7's `p47_at` (`LvmQAsmHarP47`), unchanged, at `P4 = typedEnd tdata20 (typedPos P20)`.
4. **`openT_at`** (the openings at ν = 23, both shapes): `openG`'s rows give `dOpenT P20 (smallT P20 pub)` on the
   cells' claims (`claimsT M cs`), as roll 7's `open_at` gives `openPhZ`.
-/

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

/-! ## The static facts at `P20` (L-H) -/

/-- **The typed HAR's numbers at `P20`** (one kernel decision): phases 4–7's positions (roll 7's `P47Pos`), the
lane bounds, the sizes, the typed phases' and the openings' positions (`T` the stream's lanes). -/
def HarNumT (T P4 P5 P6 P7 P8 : Nat) : Prop :=
  (P4 + 40 = 8 * aLane P20 0 ∧ P4 + 72 * P20.logN + 40 = 8 * aLane P20 1 ∧
    8 * aLane P20 2 - 40 = P4 + 72 * P20.logN + 600 ∧
    Lvm.Q1.tapeEnd (P20.logN - 5) (aLane P20 2) = aLane P20 3 ∧ 8 * aLane P20 3 - 40 = P5 ∧
    8 * Lvm.Q1.wireEnd (P20.logN - 5) (aLane P20 3) - 40 = P6 ∧ P6 + 40 = 8 * aLane P20 4 ∧
    kV P20.ksLog P6 + 40 = 8 * aLane P20 5 ∧ kG P20.ksLog P6 = 8 * aLane P20 6 - 40 ∧
    8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40 + 72 * ringStages = P7 ∧ P7 + 40 = 8 * aLane P20 7 ∧
    ksP2 P20 P7 + 96 = P8) ∧
  5 ≤ P20.logN ∧ 4 ≤ P20.ksLog ∧ 5 ≤ aLane P20 2 ∧ 5 ≤ aLane P20 3 ∧ 5 ≤ aLane P20 6 ∧
  Lvm.Q1.wireEnd (P20.logN - 5) (aLane P20 3) + 2 ≤ T ∧ gkrEnd (P20.ksLog - 4) (aLane P20 6) + 48 ≤ T ∧
  aLane P20 0 + 9 * P20.logN + 2 < T ∧ aLane P20 1 + 3 * 25 + 2 < T ∧
  aLane P20 4 + 9 * P20.ksLog + 2 < T ∧ aLane P20 5 + 3 * 25 + 2 < T ∧
  P20.logN ≤ 2 ^ Lvm.QAsm.clog2 P20.logN ∧ P20.ksLog ≤ 2 ^ Lvm.QAsm.clog2 P20.ksLog ∧
  ksQV P20.ksLog (aLane P20 7) + 3 * 4 + 3 ≤ T ∧
  aLane P20 7 + 9 * (P20.ksLog + laneBits) + 15 * P20.ksLog + 12 ≤ T ∧
  1 ≤ spongeBlocks P20 ∧ spongeBlocks P20 ≤ 2 ^ P20.ksLog ∧ ksSplit P20 + 431 ≤ 2 ^ P20.ksLog ∧
  29 ≤ T ∧ P20.logN ≤ 64 ∧ 11 + pubLanes ≤ T ∧ P4 + 40 ≤ 8 * T ∧ P8 = 8 * openU P20 ∧
  (P20.recLevels.length ≤ (opens P20).length ∧
    P20.recLevels.length + P20.mainLevels.length ≤ (opens P20).length) ∧
  P20.leafdecReads = 1 ∧ P20.nuRec = 19 ∧ P20.nuMain = 23 ∧ P20.logN = 20 ∧ typedPos P20 % 8 = 0 ∧
  busEndD P20.busDepth (mbP (typedPos P20)) + 72 + 144 * P20.tableRounds = phaseByte P20 .tape ∧
  RS.start.ent + (nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap + nodeBytes * 2 ^ (P20.level ⟨.crec, 0⟩).cap) =
    typedPos P20

set_option maxRecDepth 200000 in
/-- **`HarNumT` at `P20`** (kernel). -/
theorem harNumT20 : HarNumT (streamLanes P20) (phaseByte P20 .tape + 24 * P20.tableEvals) (phaseByte P20 .wire)
    (phaseByte P20 .ks) (phaseByte P20 .ksLink) (8 * openU P20) := by
  unfold HarNumT; decide +kernel

/-- `KS`'s layer check at `P20` (KS13: `layOk 9`). -/
theorem layOk_9T : layOk 9 = true := by rw [Lvm.Q1.layOk_eq_lit]; decide +kernel

/-- **`SLok` of `KS`'s block E at `P20`** (`LvmFinDec.okE_P20`'s text; the typed closure does not import
`LvmFinDec`). -/
theorem okE_P20T (Q : ℕ) (gate : Cell) (sh : LoopOut) : SLok (ksBlockE P20 Q sh gate) = true := by
  rw [ksBlockE, if_pos (by decide), ksSelC_P20, sizes_P20.2.2.2.2.2.2.2.2, ksSplit_P20,
    show P20.ksLog = 13 from rfl]
  rw [← SLok_shape]
  simp only [ksGlueE14, List.map_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  rw [loadsAt_shape, loadsAt_shape (q := ksQV 13 Q), preRecIns_shape, preRecIns_shape (n := 13 * 13 + 6),
    preRecIns_shape (n := 25 * 13 + 6), mulChainIns_shape (n := 38 * 13 + 8),
    mulChainIns_shape (n := 39 * 13 + 8)]
  simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI,
    shape_linI, shape_addI, shape_loc, rho'C, preP, shape_ins_mk, shape_getD_mapCellSrc, sumSrc,
    reduceCtorEq, if_false, List.length_cons, List.length_nil]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

/-- `D`'s block and selector at `P20` (`tapeTails_eq`'s `hD`, `hds`). -/
theorem hDzT : Lvm.dBlock P20 = ⟨22, 0⟩ ∧ dSel P20 = 0 := ⟨by decide +kernel, by decide +kernel⟩

/-! ## The guard check `harChkB` at `P20` -/

theorem phases47S_eqT (C : QCfg) : phases47S C = phases47 C := by
  rw [phases47S_eq]; unfold VF.phases47F phases47; rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]

/-- **What `harChkB` gives** (L-W's guard field `SF20.har`): the regions, and the B program's claim parts at Q_arith's
pointer are well formed in both shapes. -/
theorem harChk_sound {C : QCfg} {T : TData} {N : TypedV.TNat} (h : harChkB C T N = true) :
    TdOk T N ∧ claimsOkB C (qarithBParts C T (phases47 C (p2C C)).1 ((p2C C).adv (phases47 C (p2C C)).2)).1 = true := by
  simp only [harChkB, phases47S_eqT, Bool.and_eq_true] at h
  exact ⟨tdOk_of h.2, h.1⟩

/-! ## Glue (`LvmFinHB`'s, which the typed closure does not import) -/

theorem vk_cellsT {M : Mem} {x : List UInt8} {pb : ℕ} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = Lvm.NS.hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pb + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, hpub _ hj, Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some]
  have hv : (pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- Accumulators equal coordinate-wise (`LvmAccNodeLen.acc_eq_of`'s text; that module imports the bus refinement). -/
theorem acc_eq_ofT {a b : Acc} (ha : a.pt.length = accVars) (hb : b.pt.length = accVars)
    (hpt : ∀ i < accVars, a.pt.getD i 0 = b.pt.getD i 0) (hy : a.y = b.y) : a = b := by
  obtain ⟨pa, ya⟩ := a
  obtain ⟨pb, yb⟩ := b
  simp only at ha hb hpt hy
  subst hy
  congr
  refine List.ext_getElem (by rw [ha, hb]) fun i h1 h2 ↦ ?_
  have := hpt i (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem accC_eqT {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = Lvm.NS.hdrLane x j) : Lvm.QAcc.accC M pb = (pubX x).accIn := by
  have hP : ∀ j a, j < pubLanes → a = pb + j → M.k a = Lvm.NS.hdrLane x j := fun j a hj ha => ha ▸ hpub j hj
  have hL : pubLanes = 747 := pubLanes_eq
  have hA : accVars = 43 := rfl
  refine acc_eq_ofT (by simp only [Lvm.QAcc.accC, List.length_map, List.length_range])
    (by rw [pubX]; simp [pubOf]) (fun i hi => ?_) ?_
  · rw [accIn_pt_lanes x hi]
    simp only [Lvm.QAcc.accC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    rw [hP (615 + 3 * i) _ (by omega) (by omega), hP (616 + 3 * i) _ (by omega) (by omega),
      hP (617 + 3 * i) _ (by omega) (by omega)]
  · rw [accIn_y_lanes x]
    simp only [Lvm.QAcc.accC]
    rw [hP (615 + 3 * accVars) _ (by omega) (by omega), hP (616 + 3 * accVars) _ (by omega) (by omega),
      hP (617 + 3 * accVars) _ (by omega) (by omega)]

theorem sigma_sizeT {p : Params} {ws : List Word} (h : hashedLen p ≤ 8 * ws.length) :
    (sigma p ws).size = hashedLen p := by
  simp only [sigma, ByteArray.size, List.size_toArray, List.length_take, wordsBytes_length]
  omega

/-! ## The headline -/

/-- The child's trace bytes `Σ'` of a `C_rec` candidate. -/
abbrev sigC (qr : Column 19) : ByteArray := traceBytesB (decode P20 (wsC qr))

/-- **The memory facts of the `BITS` rows the HAR reads** (roll 7's `BVFacts` fields on the B program's memory
`memT`; L-D proves them from the typed `BITS` rows `bitsAux`): `s'`'s bits, `n'`'s bits and range, the positions of
both openings, the proof-of-work fields. -/
structure BVT (vk : RecursionFast.Digest) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  sb : Lvm.Q1.SBitsS (memT x qm qr).k (sigIn cfg20).hd (bsB cfg20)
  nb : NBits (memT x qm qr).k ((sigIn cfg20).bn + 2) P20.logN
  n1 : 1 ≤ (pubOf vk (hdrOf x).cL (sigC qr)).n
  nN : (pubOf vk (hdrOf x).cL (sigC qr)).n ≤ 2 ^ P20.logN
  posr : PosOk (cfgRec P20 (posBase cfg20) (pwBase cfg20)) (memT x qm qr) (sigC qr) 0 P20.recLevels (openU P20 + 15)
  posm : PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) (memT x qm qr) (sigC qr) 0 P20.mainLevels
    (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15)
  pw : ∀ k < (Lvm.QLink.opens P20).length, ((memT x qm qr).k (pwB cfg20 + k)).val.toNat < 2 ^ (64 - P20.grind)


/-! ## The parts -/

-- Part 1, the composition `core_of_phasesT`: proved in `LvmQTypedHarT` (L-D's statement, unchanged).

/-! ## The mini-bus's record at `P20` (from the guard's `fitsMiniB`) -/

theorem tdataOf_mb (C : QCfg) (F : TFrz) : (tdataOf C F).mbS = (mbTOf C F).map M3.Tab.shape ∧
    (tdataOf C F).mbR = ((mbTOf C F).map (·.τ)).foldl max 0 ∧
    (tdataOf C F).mbD = log2Ceil (M3.pushLeavesR (mbTOf C F)) ∧ (tdataOf C F).mbFix = mbFixOf C := by
  simp only [tdataOf, and_self]

theorem NT20_mbT : NT20.mbT = mbTOf cfg20 frz20 := by rw [NT20_eq]; simp only [tnatOf]
theorem tdata20_mbS : tdata20.mbS = (mbTOf cfg20 frz20).map M3.Tab.shape := by rw [tdata20_eq]; exact (tdataOf_mb _ _).1
theorem tdata20_mbR : tdata20.mbR = ((mbTOf cfg20 frz20).map (·.τ)).foldl max 0 := by
  rw [tdata20_eq]; exact (tdataOf_mb _ _).2.1
theorem tdata20_mbD : tdata20.mbD = log2Ceil (M3.pushLeavesR (mbTOf cfg20 frz20)) := by
  rw [tdata20_eq]; exact (tdataOf_mb _ _).2.2.1
theorem tdata20_mbFix : tdata20.mbFix = mbFixOf cfg20 := by rw [tdata20_eq]; exact (tdataOf_mb _ _).2.2.2


/-- **The circuit's mini-bus record is V_S's** at `P20`: the tables are all sumcheck tables, the rounds and depth are
the record's, and the typed phases end where the tape starts. -/
theorem mini20 (S : Lvm.CT.SF20) : M3.sumcheckTabs NT20.mbT = NT20.mbT ∧ tdata20.mbR = P20.tableRounds ∧
    tdata20.mbD = P20.busDepth ∧ typedEnd tdata20 (typedPos P20) = phaseByte P20 .tape + 24 * P20.tableEvals := by
  have hsc : M3.sumcheckTabs (mbTOf cfg20 frz20) = mbTOf cfg20 frz20 := mbT_sumcheck cfg20 _ _ _
  have hm := S.mini
  rw [NT20_mbT, show cfg20.p = P20 from rfl] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, hR⟩, hE⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR hE
  have hR' : tdata20.mbR = P20.tableRounds := by rw [tdata20_mbR, hR]
  have hD' : tdata20.mbD = P20.busDepth := by rw [tdata20_mbD, hD]
  refine ⟨by rw [NT20_mbT, hsc], hR', hD', ?_⟩
  have hW : (tdata20.mbS.map (·.cols.length)).sum = P20.tableEvals := by
    rw [hE, tdata20_mbS, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun t _ => by simp [M3.Tab.shape, M3.Tab.w])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbe, -⟩ := harNumT20
  unfold typedEnd tabEnd
  rw [hW, hR', hD', ← hbe]

/-- **Part 2: the typed core gadget** (`typedG` replays `dTypedT`, as `busG_replays`, `tabG_replays`,
`qacc_replays` replay roll 7's phases 2, 3, 3b): the folded accumulator is `PUB`'s `acc_in`, the typed claims are
`typedClaimsN` of the cells, the mini-bus's evaluations are its table cells'. -/
theorem typedG_replays (S : Lvm.CT.SF20) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem} {sig : ByteArray}
    {T : Nat} (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T)
    (hT : typedEnd tdata20 (typedPos P20) + 40 ≤ 8 * T) (hg : M.k (pbB cfg20) = 1)
    (hvk : ∀ i < 4, M.k (pbB cfg20 + 1 + i) = (digestLanes vk).getD i 0)
    {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E) (hz : z.val M = 0) (ho : one.val M = 1) (q : Ptr)
    (hq : 1 ≤ q.e) :
    Replays c M sig (TypedV.dTypedT P20 NT20 (NT20.m3 P20) (pubOf vk cL sig))
      (typedG tdata20 (pbB cfg20) (typedPos P20) z one) q (typedPos P20) (typedEnd tdata20 (typedPos P20))
      fun v t ↦ v.1 = Lvm.QAcc.accC M (pbB cfg20) ∧
        v.2.1 = TypedV.typedClaimsN NT20 P20 (vs M t.ry) (vs M t.rv) (vs M t.rr) (t.vR.val M) ∧
        v.2.2 = t.tab.map fun e ↦ (vs M e.1, vs M e.2) := by
  obtain ⟨hsc, hR, hD, -⟩ := mini20 S
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hld, -⟩ := harNumT20
  have hfix : FixListed NT20.mbT tdata20.mbFix := by rw [NT20_mbT, tdata20_mbFix]; exact mbT_fix cfg20 _ _ _
  exact typedG_replaysG vk cL hS hH hg hvk hzE hoE hz ho P20 hld (harChk_sound S.har).1 hsc
    (by rw [tdata20_mbS, NT20_mbT]) hR hD hfix busPos_mod_P20 hT q hq

/-- **The openings at ν = 23, generic in the parameters** (the proof of part 4) (roll 7's `open_at` on `dOpenT`): from `openG`'s rows (gate on),
`dOpenT p (smallT p pub)` on the cells' claims, from phase 8's start with `ok`, keeps `ok`, reads `Σ'` to its end
and leaves no message pending. -/
theorem openT_atG (p : Params) (hnu : p.nuMain = 23) {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hg : M.k (pbB cfg20) = 1)
    (hlr : LayOk (cfgRec p (posBase cfg20) (pwBase cfg20)) T = true)
    (hlm : LayOk (cfgMain p (posBase cfg20) (pwBase cfg20)) T = true)
    (hop : p.recLevels.length ≤ (Lvm.QLink.opens p).length ∧
      p.recLevels.length + p.mainLevels.length ≤ (Lvm.QLink.opens p).length)
    (hposr : PosOk (cfgRec p (posBase cfg20) (pwBase cfg20)) M sig 0 p.recLevels (openU p + 15))
    (hposm : PosOk (cfgMain p (posBase cfg20) (pwBase cfg20)) M sig 0 p.mainLevels
      (stackEndL p.grind p.recOod p.recLevels (openU p + 15) + 15))
    (hend : 8 * stackEndL p.grind p.mainOod p.mainLevels
      (stackEndL p.grind p.recOod p.recLevels (openU p + 15) + 15) = sig.size)
    (hpw : ∀ x < (Lvm.QLink.opens p).length, p.grind ≠ 0 → (M.k (pwB cfg20 + x)).val.toNat < 2 ^ (64 - p.grind))
    (cs : List CClaim) (hwr : ClaimsWF p.nuRec (onCom cs .crec) = true)
    (hwm : ClaimsWF p.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e) (pub : Pub) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF z cc = true)
    (h : Lvm.QSig.Ok c M (openG (cfgRec p (posBase cfg20) (pwBase cfg20)) (cfgMain p (posBase cfg20) (pwBase cfg20))
      (p.logN == 20 && p.nuMain == CMain.nu20) cs mb z one (kc (pbB cfg20))) q) :
    ∀ s : RS, pos s = 8 * openU p → s.ok = true →
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.ok = true ∧
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.ent = sig.size ∧
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.msg = 0 := by
  intro s hs hok
  have e : TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) = openPhZ p pub (claimsT M cs) := by
    have h1 : TypedV.smallT p pub = Shape.smallP p pub := by
      simp only [TypedV.smallT, Shape.smallP, hnu]
    rw [h1, openPhZ]
    unfold TypedV.dOpenT Shape.dOpenZ Shape.onStackZsF
    rw [hnu, TypedV.onStackZBN_23]
  rw [e]
  obtain ⟨o1, o2, o3⟩ := openPhZ_run p pub (cfgRec p (posBase cfg20) (pwBase cfg20))
    (cfgMain p (posBase cfg20) (pwBase cfg20)) _ cs mb z one (kc (pbB cfg20))
    hS rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ => hσ) (fun _ => hzw) rfl hlr hlm hwr hwm hz ho hzE hoE
    (gate_val cfg20 hg) rfl hposr hposm
    (fun i hi hg0 => hpw (0 + i) (by have := hop; simp only [cfgRec] at hi; omega) hg0)
    (fun i hi hg0 => hpw (p.recLevels.length + (0 + i)) (by have := hop; simp only [cfgMain] at hi; omega) hg0)
    hq h s (by rw [hs]; rfl)
  refine ⟨o1.trans hok, ?_, o3⟩
  simp only [pos] at o2
  have e : 8 * stackEndL p.grind p.mainOod (cfgMain p (posBase cfg20) (pwBase cfg20)).levels
      ((cfgMain p (posBase cfg20) (pwBase cfg20)).U + 15) = sig.size := hend
  omega

/-- **Part 4: the openings at ν = 23, both shapes** (roll 7's `open_at` on `dOpenT`): from `openG`'s rows (gate on),
`dOpenT P20 (smallT P20 pub)` on the cells' claims, from phase 8's start with `ok`, keeps `ok`, reads `Σ'` to its end
and leaves no message pending. -/
theorem openT_at {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hg : M.k (pbB cfg20) = 1)
    (hlr : LayOk (cfgRec P20 (posBase cfg20) (pwBase cfg20)) T = true)
    (hlm : LayOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) T = true)
    (hop : P20.recLevels.length ≤ (Lvm.QLink.opens P20).length ∧
      P20.recLevels.length + P20.mainLevels.length ≤ (Lvm.QLink.opens P20).length)
    (hposr : PosOk (cfgRec P20 (posBase cfg20) (pwBase cfg20)) M sig 0 P20.recLevels (openU P20 + 15))
    (hposm : PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) M sig 0 P20.mainLevels
      (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15))
    (hend : 8 * stackEndL P20.grind P20.mainOod P20.mainLevels
      (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15) = sig.size)
    (hpw : ∀ x < (Lvm.QLink.opens P20).length, P20.grind ≠ 0 → (M.k (pwB cfg20 + x)).val.toNat < 2 ^ (64 - P20.grind))
    (cs : List CClaim) (hwr : ClaimsWF P20.nuRec (onCom cs .crec) = true)
    (hwm : ClaimsWF P20.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e) (pub : Pub) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF z cc = true)
    (h : Lvm.QSig.Ok c M (openG (cfgRec P20 (posBase cfg20) (pwBase cfg20)) (cfgMain P20 (posBase cfg20) (pwBase cfg20))
      (P20.logN == 20 && P20.nuMain == CMain.nu20) cs mb z one (kc (pbB cfg20))) q) :
    ∀ s : RS, pos s = 8 * openU P20 → s.ok = true →
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.ok = true ∧
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.ent = sig.size ∧
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.msg = 0 := by
  exact openT_atG P20 rfl hS hg hlr hlm hop hposr hposm hend hpw cs hwr hwm hzE hoE hz ho hq pub mb hσ hzw h

/-- **What phases 4–7's output cells are** (generic in the configuration and the pointer: roll 7's `claims_at`
steps; at the instance a `simp` on `phases47 cfg20 (p2C cfg20)` is slow): the tape's 25 values, `KS`'s 25 lanes,
`logN` point cells, and `KS`'s GKR slices are the stream's. -/
theorem p47_out_facts (C : QCfg) {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {p2 : Ptr} {o : P47Out}
    (h47 : Lvm.QSig.Ok c M (phases47 C) p2) (ho47 : (phases47 C p2).1 = o) (hS : Streamed M sig T)
    (hlayk : layOk (C.p.ksLog - 4) = true) (hqk : 5 ≤ aLane C.p 6) (hT : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) ≤ T) :
    o.v.length = 25 ∧ o.vk.length = 25 ∧ o.r.length = C.p.logN ∧
      (o.kko.vals M).slices = slAt sig (gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 192) := by
  have hO : (phases47 C p2).1 = o := ho47
  simp only [phases47, bind_apply, pure_apply] at hO
  have ekko := congrArg P47Out.kko hO
  have ev : o.v.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have evk : o.vk.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have erl : o.r.length = C.p.logN := by rw [← hO]; simp only [List.length_map, List.length_range]
  dsimp only at ekko
  clear hO
  obtain ⟨hh, -⟩ := h47
  simp only [phases47] at hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, -⟩ := hh
  have sK := gkrGadget_slices hlayk hqk hS hT hhGk
  rw [ekko] at sK
  exact ⟨ev, evk, erl, sK⟩

/-- **`claimsOkB`'s parts** (by rewriting a generic tuple: a `simp` on the instance's claim list is slow). -/
theorem claimsOkB_parts {C : QCfg} {z : Cell} {a b c d e f : List CClaim}
    (h : claimsOkB C (z, a, b, c, d, e, f) = true) :
    ClaimsWF C.p.nuRec (onCom (a ++ b ++ (c ++ d) ++ e ++ f) .crec) = true ∧
      ClaimsWF C.p.nuMain (onCom (a ++ b ++ (c ++ d) ++ e ++ f) .main) = true ∧
      (∀ cc ∈ onCom (a ++ b ++ (c ++ d) ++ e ++ f) .main, Lvm.QShape.ZWF z cc = true) ∧
      b.all noDRB = true ∧ (d ++ e ++ f).all noDRB = true := by
  simp only [claimsOkB, csB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [List.all_append, Bool.and_eq_true] at h4
  obtain ⟨⟨⟨⟨-, h5⟩, h6⟩, h7⟩, h8⟩ := h4
  exact ⟨h1, h2, List.all_eq_true.mp h3, h5, by simp only [List.all_append, h6, h7, h8, Bool.and_self]⟩

/-- `M3.real`'s table claims on a native instance's tables. -/
theorem m3_tableClaimsT (N : TypedV.TNat) (p : Params) (pub : Pub) (ev : List (List FE × List FE)) :
    (N.m3 p).tableClaims pub ev = M3.tableClaimsR (M3.sumcheckTabs N.mbT) ev := rfl

/-- `M3.real`'s `KS` block on a native instance. -/
theorem m3_ksBlockT (N : TypedV.TNat) (p : Params) : (N.m3 p).ksBlock = ⟨p.ksLog + slotLog, (layout0 p).ks⟩ := rfl

/-- Q_arith's pointer (a rewrite: a definitional check would run Q_link's and Q_sig's builders). -/
theorem p2_eqT : p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0 = p2C cfg20 := by
  unfold p2 p1 p0 p2C p1C
  rw [show cfg20.p = P20 from rfl]

set_option maxHeartbeats 4000000 in
/-- **The typed HAR at `P20`** (L-H): the B program's Q_arith on a good node pair's memory accepts the child's stream
under V_S's typed decision and folds to the statement's `acc_in`. -/
theorem harithT20 (S : Lvm.CT.SF20) (H : THyp Lvm.CT.Ti20) {vk c : RecursionFast.Digest} {x : List UInt8}
    {qm : Column CMain.nu20} {qr : Column 19} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : GoodT Lvm.CT.Ti20 H x qm qr) (hin : InMapM (lay cfg20) (sigIn cfg20) (memT x qm qr) vk x qm qr)
    (hL : LaneLink P20 (wsC qr)) (hLk : LinkOk P20 (decode P20 (wsC qr)))
    (hrun : Lvm.QSig.Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr) qaB
      (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0))
    (hbv : BVT vk x qm qr) :
    TypedV.decideCoreT P20 NT20 vk (hdrOf x).cL (sigC qr) = true ∧
      TypedV.accOutOfT P20 NT20 vk (hdrOf x).cL (sigC qr) = (pubX x).accIn := by
  obtain ⟨htd, hcl⟩ := harChk_sound S.har
  obtain ⟨hpos, hn, hk, hql2, hql3, hql6, hTw, hTgk, hTr, hTv, hTrk, hTvk, hD, hDk, hTlk, hTlk', hB, hB2, hK, hT29,
    hlog, hH, hT4, hP8, hop, hld, hnuR, hnuM, hlogN, hmod, hbe, h0⟩ := harNumT20
  obtain ⟨hsc, -, -, hTE⟩ := mini20 S
  -- the stream, the gate, `vk`, the end of `Σ'`
  have hT := hQ20.hT
  have hsz := hL.size
  have hTL : streamLanes P20 = hashedLen P20 / 8 := by
    rw [sizes_P20.2.2.2.2.2.2.1, sizes_P20.2.2.2.2.2.1]
  have hT' : hashedLen P20 / 8 + 17 ≤ 2 ^ (lay cfg20).m := hT
  have hsz' : hashedLen P20 ≤ 8 * (wsC qr).length := hsz
  have e1 : streamLanes P20 ≤ 2 ^ (lay cfg20).m := by
    rw [hTL]; generalize hashedLen P20 = H at hT' ⊢; generalize 2 ^ (lay cfg20).m = K at hT' ⊢; omega
  have e2 : 8 * streamLanes P20 ≤ hashedLen cfg20.p := by
    rw [show cfg20.p = P20 from rfl, hTL]; generalize hashedLen P20 = H; omega
  have e3 : streamLanes P20 ≤ (wsC qr).length := by
    rw [hTL]; generalize hashedLen P20 = H at hsz' ⊢; generalize (wsC qr).length = K at hsz' ⊢; omega
  have hS : Streamed (memT x qm qr) (sigC qr) (streamLanes P20) := streamed_child cfg20 hS20 hL hin.stream e1 e2 e3
  have hpub : ∀ j < pubLanes, (memT x qm qr).k (pbB cfg20 + j) = Lvm.NS.hdrLane x j := hin.pub
  have hg : (memT x qm qr).k (pbB cfg20) = 1 := hin.flag
  have hgv : (kc (pbB cfg20)).val (memT x qm qr) = 1 := gate_val cfg20 hg
  have hvk := vk_cellsT hpub (okS_vk hok)
  have hend : 8 * stackEndL P20.grind P20.mainOod P20.mainLevels
      (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15) = (sigC qr).size := by
    rw [(lay20 (posBase cfg20) (pwBase cfg20)).2.2.2.1, sigC, traceBytesB_decode hS20 hL, sigma_sizeT hsz]
  -- Q_arith: phases 4–7, then `qarithB`
  rw [p2_eqT] at hrun
  have h : Lvm.QSig.Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) (memT x qm qr)
      (phases47 cfg20 >>= qarithB cfg20 tdata20) (p2C cfg20) := hrun
  obtain ⟨h47, hR⟩ := okb h
  obtain ⟨o, ho47⟩ : ∃ o, (phases47 cfg20 (p2C cfg20)).1 = o := ⟨_, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q0, (p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2 = q0 := ⟨_, rfl⟩
  simp only [ho47, hq0] at hR hcl
  simp only [qarithB] at hR
  simp only [qarithBParts, bind_apply, pure_apply] at hcl
  -- the constants
  obtain ⟨hZ, hR⟩ := okb hR
  have hzv : (ec q0.e).val (memT x qm qr) = 0 := (constE_val hZ.1).trans ofK_zero
  have ez : (const .E 0 (kc 0) q0).1 = ec q0.e := rfl
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR hcl
  obtain ⟨hO1, hR⟩ := okb hR
  have hov : (ec (q0.e + 1)).val (memT x qm qr) = 1 := (constE_val hO1.1).trans ofK_one
  have eo : (const .E 1 (kc 0) ⟨q0.k, q0.e + 1⟩).1 = ec (q0.e + 1) := rfl
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR hcl
  -- the typed core
  obtain ⟨hTy, hR⟩ := okb hR
  generalize ht : (typedG tdata20 (pbB cfg20) (typedPos cfg20.p) (ec q0.e) (ec (q0.e + 1))
    ⟨q0.k, q0.e + 1 + 1⟩).1 = t at hR hcl
  generalize hq2 : (⟨q0.k, q0.e + 1 + 1⟩ : Ptr).adv (typedG tdata20 (pbB cfg20) (typedPos cfg20.p) (ec q0.e)
    (ec (q0.e + 1)) ⟨q0.k, q0.e + 1 + 1⟩).2 = q2 at hR hcl
  obtain ⟨hTC, hR⟩ := okb hR
  generalize htc : (typedClaimsC (ec q0.e) (ec (q0.e + 1)) tdata20 cfg20.p.nuMain t q2).1 = tc at hR hcl
  generalize hq3 : q2.adv (typedClaimsC (ec q0.e) (ec (q0.e + 1)) tdata20 cfg20.p.nuMain t q2).2 = q3 at hR hcl
  obtain ⟨h8, hR⟩ := okb hR
  generalize hq4 : q3.adv (ringGkr (cfg20.p.ksLog - 4) (aLane cfg20.p 6) q0.e q3).2 = q4 at hR hcl
  obtain ⟨h9, hR⟩ := okb hR
  generalize hq5 : q4.adv (ksLinkG cfg20.p (aLane cfg20.p 7) q0.e (q0.e + 1) q4).2 = q5 at hR hcl
  -- the typed phases
  have hq1 : 1 ≤ (⟨q0.k, q0.e + 1 + 1⟩ : Ptr).e := by simp
  have RT := typedG_replays S vk (hdrOf x).cL (c := ctxOf (Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0)) hS hH
    (by rw [hTE]; exact hT4) hg hvk (z := ec q0.e) (one := ec (q0.e + 1)) rfl rfl hzv hov ⟨q0.k, q0.e + 1 + 1⟩ hq1
  have htyped : PhaseAt (TypedV.dTypedT P20 NT20 (NT20.m3 P20) (pubOf vk (hdrOf x).cL (sigC qr))) (sigC qr) (typedPos P20)
      (phaseByte P20 .tape + 24 * P20.tableEvals)
      (Lvm.QAcc.accC (memT x qm qr) (pbB cfg20), TypedV.typedClaimsN NT20 P20 (vs (memT x qm qr) t.ry) (vs (memT x qm qr) t.rv) (vs (memT x qm qr) t.rr) (t.vR.val (memT x qm qr)),
        t.tab.map fun e => (vs (memT x qm qr) e.1, vs (memT x qm qr) e.2)) := by
    rw [← hTE]
    refine phaseAt_of RT hTy fun a ha => ?_
    rw [show typedPos P20 = typedPos cfg20.p from rfl, ht] at ha
    obtain ⟨a1, a2, a3⟩ := ha
    exact Prod.ext a1 (Prod.ext a2 a3)
  -- phases 4–7
  have hnb' : ∀ j < cfg20.p.logN, (kc ((sigIn cfg20).bn + 2 + j)).val (memT x qm qr) = bitE (pubOf vk (hdrOf x).cL (sigC qr)).n j := by
    intro j hj
    rw [pub_n hS hT29 vk (hdrOf x).cL, Cell.val_K]
    exact bitE_out1 (by rw [show cfg20.p = P20 from rfl] at hj; omega) (hbv.nb j hj)
  have hsl : (pubOf vk (hdrOf x).cL (sigC qr)).s = (List.range 4).map fun l => (memT x qm qr).k ((sigIn cfg20).hd + 9 + l) := by
    rw [pub_s hS hT29 vk (hdrOf x).cL]
    refine List.map_congr_left fun l _ => ?_
    rw [sLane_eq]; rfl
  have hlay : layOk (cfg20.p.logN - 5) = true := by
    rw [show cfg20.p = P20 from rfl, hlogN]; exact Lvm.Q1.layOk_15
  have hlayk : layOk (cfg20.p.ksLog - 4) = true := by
    rw [show cfg20.p.ksLog - 4 = 9 from rfl]; exact layOk_9T
  have hposS : P47Pos P20 (phaseByte P20 .tape + 24 * P20.tableEvals) (phaseByte P20 .wire) (phaseByte P20 .ks)
      (phaseByte P20 .ksLink) (8 * openU P20) := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hpos
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  have hTgk' := le_trans (Nat.le_add_right _ 48) hTgk
  rw [show (P20 : Params) = cfg20.p from rfl] at hposS hn hk hql2 hql3 hql6 hTw hTgk' hTr hTv hTrk hTvk hD hDk hTlk hB hB2 hK
  obtain ⟨tp, wo, htp, -, hwiC, htw, hks, hksl, hokK⟩ := p47_at cfg20 (pubOf vk (hdrOf x).cL (sigC qr)) hposS hn hk hlay hlayk hql2 hql3 hql6 hS hTw
    hTgk' hTr hTv hTrk hTvk hD hDk hTlk hB hB2 hK (fun sh => okE_P20T _ _ sh) hnb' hbv.n1 hbv.nN hbv.sb hsl hgv
    h47 o ho47 (NT20.m3 P20) (real_eq _ _)
  rw [show cfg20.p = P20 from rfl] at htp hwiC hks hksl hokK
  generalize hkl : (NT20.m3 P20).ksLink (ksLinkView P20 (NT20.m3 P20) (feAt (sigC qr)) (phaseByte P20 .ksLink) (vs (memT x qm qr) o.rk) (pubOf vk (hdrOf x).cL (sigC qr)))
    = KL at hksl hokK
  obtain ⟨okK, kL⟩ := KL
  -- the openings
  have key := core_of_phasesT P20 NT20 vk (hdrOf x).cL (sigC qr) h0 htyped htp hwiC hks hksl hokK
  refine (fun hc => ⟨hc.1, hc.2.trans (accC_eqT hpub)⟩) (key ?_)
  intro s hs hok
  dsimp only
  -- the claim checks
  obtain ⟨hwr, hwm, hzw, hnd2, hnd⟩ := claimsOkB_parts hcl
  -- the openings' run on the circuit's claims
  rw [show cfg20.p = P20 from rfl] at hR hwr hwm hzw hnd
  have hq5 : 1 ≤ q5.e := by
    have e2 := adv_e_le (⟨q0.k, q0.e + 1 + 1⟩ : Ptr) (typedG tdata20 (pbB cfg20) (typedPos cfg20.p) (ec q0.e)
      (ec (q0.e + 1)) ⟨q0.k, q0.e + 1 + 1⟩).2
    have e3 := adv_e_le q2 (typedClaimsC (ec q0.e) (ec (q0.e + 1)) tdata20 cfg20.p.nuMain t q2).2
    have e4 := adv_e_le q3 (ringGkr (cfg20.p.ksLog - 4) (aLane cfg20.p 6) q0.e q3).2
    have e5 := adv_e_le q4 (ksLinkG cfg20.p (aLane cfg20.p 7) q0.e (q0.e + 1) q4).2
    rw [hq2] at e2; rw [hq3] at e3; rw [hq4] at e4; rw [hq5] at e5
    exact le_trans (Nat.le_add_left 1 (q0.e + 1)) (le_trans e2 (le_trans e3 (le_trans e4 e5)))
  have hσ : (1 + (o.mb.getD 18 default).val (memT x qm qr)) * (1 + (o.mb.getD 19 default).val (memT x qm qr)) =
      if decide ((pubOf vk (hdrOf x).cL (sigC qr)).n ≤ 2 ^ CMain.smallLogN20) then 1 else 0 := by
    have hmb := htw.mb
    rw [show cfg20.p.logN = 20 from hlogN] at hmb
    exact sigma_val o.mb _ hmb hbv.n1 (by have := hbv.nN; rw [hlogN] at this; exact this)
  have hOT := openT_at hS hg (lay20 (posBase cfg20) (pwBase cfg20)).1 (lay20 (posBase cfg20) (pwBase cfg20)).2.1
    hop hbv.posr hbv.posm hend (fun k hk _ => hbv.pw k hk) _ hwr hwm rfl rfl hzv hov hq5 (pubOf vk (hdrOf x).cL (sigC qr)) o.mb hσ hzw hR s
    (by rw [hs]) hok
  -- the parts of the claim list
  obtain ⟨ev, evk, erl, sK⟩ := p47_out_facts cfg20 h47 ho47 hS hlayk hql6 hTgk'
  rw [show cfg20.p = P20 from rfl] at sK h8 h9 hql6 hTgk' hposS erl
  have hze : (memT x qm qr).e q0.e = 0 := hzv
  have hoe : (memT x qm qr).e (q0.e + 1) = 1 := hov
  have rK := ringGkr_rel _ hql6 sK hS hTgk hze h8.1
  have hh4 : (pubOf vk (hdrOf x).cL (sigC qr)).h = (List.range 4).map fun l => (memT x qm qr).k (hLane l) := pub_h hS hT29 vk (hdrOf x).cL
  -- the typed claims
  obtain ⟨T1, T2, C1, C2⟩ := typedClaimsC_val hzv hov htd P20.nuMain t NT20.mbT (by rw [tdata20_mbS, NT20_mbT]) q2
    hTC.1
  rw [show cfg20.p.nuMain = P20.nuMain from rfl] at htc
  rw [htc] at T1 T2 C1 C2
  rw [← hsc, ← m3_tableClaimsT NT20 P20 (pubOf vk (hdrOf x).cL (sigC qr))] at T1 T2
  -- the rest's tails in the small shape
  have htt : TypedV.smallT P20 (pubOf vk (hdrOf x).cL (sigC qr)) = true → (tapeClaimsC P20 q0.e (q0.e + 1) o).map (Lvm.QShape.tailC (memT x qm qr)) =
      Shape.tapeTails P20 tp wo (vs (memT x qm qr) o.wire.ring.cs) (pubOf vk (hdrOf x).cL (sigC qr)) := by
    intro hsm
    rw [smallT_P20] at hsm
    have hmR : (⟨.main, .ring ⟨P20.nuMain, 0⟩ (o.wire.sigma ++ o.wire.tau ++ selC q0.e (q0.e + 1) (dSel P20)
        (dSelBits P20)) o.wire.ring.cs, o.wire.ring.target⟩ : CClaim) ∈
        onCom (tc.1 ++ tc.2 ++ (tapeClaimsC P20 q0.e (q0.e + 1) o ++
          kClaimsC ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ o.kko (ringGkr (P20.ksLog - 4) (aLane P20 6) q0.e q3).1) ++
          ksOutC P20 o.rk o.vk q0.e (q0.e + 1) ++ (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1) .main := by
      refine List.mem_filter.mpr ⟨?_, rfl⟩
      simp only [List.mem_append, tapeClaimsC, List.mem_singleton, true_or, or_true]
    have zR := hzw _ hmR
    simp only [Lvm.QShape.ZWF, hnuM, if_true, Bool.and_eq_true, decide_eq_true_eq, List.length_append, selC,
      List.length_map, List.length_range] at zR
    have hdb : dSelBits P20 = 1 := by rw [dSelBits, hnuM, hlogN]
    have hστ : (o.wire.sigma ++ o.wire.tau).length = 22 := by
      have := zR.1.1
      simp only [hdb, show CMain.nu20 = 23 from rfl, List.length_append] at this ⊢
      first | exact this | exact Nat.succ.inj this
    exact tapeTails_eq cfg20 hze hoe htw (by rw [erl, hlogN]) hστ (by rw [hh4]; simp) hsm hDzT.1 hDzT.2 hbv.n1
  -- the rest's values (each stated in V_S's form, so that the last step matches syntactically)
  have htape' : (tapeClaimsC P20 q0.e (q0.e + 1) o).map (CClaim.val (memT x qm qr)) =
      (tapeClaims P20 tp wo (pubOf vk (hdrOf x).cL (sigC qr))).map (.main, ·) := by
    have e := tapeClaimsC_val cfg20 hze hoe htw ev hh4
    rw [show cfg20.p = P20 from rfl] at e
    exact e
  have hks' : (kClaimsC ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ o.kko (ringGkr (P20.ksLog - 4) (aLane P20 6) q0.e q3).1).map
      (CClaim.val (memT x qm qr)) = (keccakClaims (NT20.m3 P20).ksBlock (o.kko.vals (memT x qm qr))
        (ringAt (feAt (sigC qr)) (8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40) (o.kko.vals (memT x qm qr)).slicePoint
        (o.kko.vals (memT x qm qr)).slices)).map (.main, ·) := by
    rw [m3_ksBlockT]; exact kClaimsC_val _ o.kko _ _ rK
  have hko' : (ksOutC P20 o.rk o.vk q0.e (q0.e + 1)).map (CClaim.val (memT x qm qr)) =
      (NT20.m3 P20).ksOutputClaims (vs (memT x qm qr) o.rk) (vs (memT x qm qr) o.vk) := by
    rw [show NT20.m3 P20 = M3.real P20 (fun _ => NT20.mbT) from rfl, real_eq]
    exact ksOutC_val P20 o.rk o.vk hze hoe evk
  have hkl' : (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1.map (CClaim.val (memT x qm qr)) = kL := by
    have e : (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1.map (CClaim.val (memT x qm qr)) =
        ((M3.real P20 (fun _ => NT20.mbT)).ksLink (ksLinkView P20 (M3.real P20 (fun _ => NT20.mbT)) (feAt (sigC qr))
          (phaseByte P20 .ksLink) (vs (memT x qm qr) o.rk) (pubOf vk (hdrOf x).cL (sigC qr)))).2 := by
      rw [real_eq]; exact ksLinkG_val' P20 _ _ hk hposS.l7 hS hTlk' hze hoe h9.1
    rw [e, show M3.real P20 (fun _ => NT20.mbT) = NT20.m3 P20 from rfl, hkl]
  have eq := openClaimsT_eq P20 (TypedV.smallT P20 (pubOf vk (hdrOf x).cL (sigC qr))) NT20 (NT20.m3 P20) (pubOf vk (hdrOf x).cL (sigC qr)) (ec q0.e) hzv t.ry t.rv t.rr t.vR
    (t.tab.map fun e => (vs (memT x qm qr) e.1, vs (memT x qm qr) e.2)) tp wo (vs (memT x qm qr) o.wire.ring.cs) (vs (memT x qm qr) o.rk) (vs (memT x qm qr) o.vk)
    (keccakClaims (NT20.m3 P20).ksBlock (o.kko.vals (memT x qm qr))
      (ringAt (feAt (sigC qr)) (8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40) (o.kko.vals (memT x qm qr)).slicePoint
        (o.kko.vals (memT x qm qr)).slices)) kL tc.1 tc.2
    (tapeClaimsC P20 q0.e (q0.e + 1) o)
    (kClaimsC ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ o.kko (ringGkr (P20.ksLog - 4) (aLane P20 6) q0.e q3).1)
    (ksOutC P20 o.rk o.vk q0.e (q0.e + 1)) (ksLinkG P20 (aLane P20 7) q0.e (q0.e + 1) q4).1 hnuR T1 T2 C1 C2 hnd2
    htape' hks' hko' hkl' htt hnd
  rw [eq]
  rw [show (ec q0.e).n = q0.e from rfl, show (ec (q0.e + 1)).n = q0.e + 1 from rfl] at hOT
  exact hOT

end Lvm.Har
