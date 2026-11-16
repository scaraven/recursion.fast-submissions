-- New for lvm2 E2-FT (E2F-QH6): `nodeSoundF`'s circuit-side hypotheses at S2GF (`hholds`, `hmap`, `hqlt`, `hpos`,
-- `hbits`, and the Keccak half `hGK`) discharged from the guard's facts, on roll 11's typed wrappers generalised over
-- the configuration (`LvmNodeSoundTIn`/`T20`/`TBits`/`TBV`: `inMapTG`, `readdTG`, `hqltG`, `outsOnC_of`, `hposTC`,
-- `sigBits_ofC`); the coordinate-split relation's auxiliary rows (`auxRow_of_wiringX`) and `PUB` at `acc_in` of `accV`
-- coordinates (`pubOfA_hdrLanes`).
import LvmE2QNodeSkel
import LvmE2QNodeChkG
import LvmE2QAsmSpec
import LvmE2QTypedGuard
import LvmCertM20
import LvmNodeSoundTBV
import LvmE2QTypedSpec
import LvmE2VMidSpec

/-!
# `nodeSoundF`'s hypotheses at S2GF

* **`auxRow_of_wiringX`**: the coordinate-split relation `WiringRelX` makes every auxiliary (`BITS`) row hold (its
  coordinate `1` at the row's slot, where only the row has entries, all of matrices `< 4`).
* **`nonReadd_of_wiringX`**: the non-`readd` rows hold (`rowDef_of_wiringX`).
* `aux_specQF`: the S2GF layout (`mkLayD` on `specQF`) holds every `BITS` class's chunk blocks.
* `pubOfA_hdrLanes`, **`pubXF_lane`**: `PUB`'s `pubLanesX accV` lanes of `pubOfA accV` are the header's.
* **`NodeGF F Q tl N`**: the facts the S2GF guard gives for these (`StaticFactsTX`, the node checks `nodeChkBG` at
  `B = spongeBlocks P20F`, `pubLanesX accVF`, `σ′` in `S`, the program's `K` cells, the mini-bus's tables, the `BITS`
  blocks); **`nodeGF_of`** from the guard's Bools.
* On a pair `GoodTF (N.inst Q tl) H ∧ SBlk`: **`hholdsF`**, **`hmapF`**, **`hqltF`**, **`hposF`**, **`hbitsF`**,
  `goodKF_of`; **`nodeSoundFG`**: `nodeSoundF` with all of them, leaving `harith`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol
open Lvm.VEq (pubXF)

/-! ## The auxiliary rows from the coordinate-split relation -/

section Aux

variable {Q : Program} {lay : Typed.Lay}

/-- A constraint row's slot is no auxiliary row's slot. -/
theorem slot_ne_auxSlot (hlay : lay.Ok Q) {b t jf : ℕ} (hb : b < Q.blocks.length) (ht : t < (Q.blk b).tpl.length)
    (hjf : jf < 2 ^ (Q.blk b).lsize) (hcon : Row.isCon ((Q.blk b).tpl.getD t default) = true) {k r j : ℕ}
    (hk : k < lay.aux.length) (hr : r < (lay.aux.getD k default).rows.length)
    (hj : j < 2 ^ (lay.aux.getD k default).l) : lay.slot b t jf ≠ lay.auxSlot k r j := by
  intro hx
  obtain ⟨c, hc, hcl⟩ := lh_aux_chunk hlay hk hr
  obtain ⟨c', hcr, hx1, hl⟩ := lh_con_chunk hlay hb ht hcon
  unfold Lay.slot at hx
  rw [hcr] at hx
  have := (lh_slotR_inj hlay hx1 hc (hl ▸ hjf) (hcl ▸ hj) hx).1
  have : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
  omega

/-- **At an auxiliary slot the eight matrices' entries are the four's** (only the row's own, `s = 0`). -/
theorem entsX_at_aux (hlay : lay.Ok Q) {k r j : ℕ} (hk : k < lay.aux.length)
    (hr : r < (lay.aux.getD k default).rows.length) (hj : j < 2 ^ (lay.aux.getD k default).l) (o : ℕ) :
    (entsX Q lay).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) =
      (ents Q lay).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) := by
  have h0 : ∀ f : Inst → List Ent, (∀ i e, e ∈ f i → e.x = lay.slot i.blk i.t i.jf ∧ Row.isCon i.row = true) →
      (Q.insts.flatMap f).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) = [] := by
    intro f hf
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := lh_mem_insts hi
    obtain ⟨hx, hcon⟩ := hf _ e he
    exact slot_ne_auxSlot hlay hb ht hjf hcon hk hr hj (hx.symm.trans hp.2)
  rw [entsX, ents, List.filter_append, List.filter_append, h0 _ fun i e he ↦ lhx_instEntsX_slot Q lay i he,
    h0 _ fun i e he ↦ ⟨(lh_instEnts_mem Q lay i he).2.1, lh_instEnts_con Q lay i he⟩]

/-- **The auxiliary (`BITS`) rows hold from the coordinate-split relation** (`auxRow_of_wiring`'s twin): on a
checked layout, with `z(one) = 1`, row `r` of auxiliary block `k` at iteration `j` meets `A·B + D + W = 0`. -/
theorem auxRow_of_wiringX (Q : Program) (lay : Typed.Lay) (z : ℕ → FK) (hlay : lay.Ok Q) (hone : z lay.one = 1)
    (h : WiringRelX Q lay z) {k r j : ℕ} (hk : k < lay.aux.length) (hj : j < 2 ^ (lay.aux.getD k default).l)
    (hr : r < (lay.aux.getD k default).rows.length) :
    ARowHolds lay z j ((lay.aux.getD k default).rows.getD r default) := by
  have := (h (lay.auxSlot k r j)).1
  simp only [relX0, lhx_matZX_eq, entsX_at_aux hlay hk hr hj, lh_ents_at_aux hlay hk hr hj, lh_auxVal hone] at this
  have h4 : aRowMat lay z j ((lay.aux.getD k default).rows.getD r default) 4 = 0 := by
    unfold aRowMat
    rw [List.filter_eq_nil_iff.mpr fun e he hp ↦ by
      have := ((lh_aux hlay hk).1 _ (lh_getD_mem _ hr) e he).1
      simp only [beq_iff_eq] at hp; omega]
    rfl
  rw [h4, zero_mul, add_zero] at this
  exact this

end Aux

/-- **The non-`readd` rows hold from the coordinate-split relation** (`rowDef_of_wiringX`). -/
theorem nonReadd_of_wiringX (Q : Program) (lay : Typed.Lay) (z : ℕ → FK) (hwf : Q.wf = true)
    (htw : Q.twinsOk = true) (hlay : lay.Ok Q) (hone : z lay.one = 1) (h : WiringRelX Q lay z) :
    NonReaddHolds Q (memOf lay z) :=
  fun _ hi hop ↦ (rowDef_of_wiringX Q lay z hwf htw hlay hone h hi fun lo m h' ↦ absurd h' (hop lo m)).1

/-- **The S2GF layout holds every `BITS` class's chunk blocks** (`mkLayD` on `specQF`, as `aux_specQ`). -/
theorem aux_specQF (C : QCfg) (Q : Program) (pw : List (ℕ × ℕ)) (d : Array (Ty × ℕ × ℕ)) :
    ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ (mkLayD Q (specQF C Q pw) d).1.aux := by
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQF C Q pw) d
  refine ⟨f, fun i S c hS hc ↦ ?_⟩
  rw [hf]
  show _ ∈ (specQ C Q).auxOf f ++ _ ++ _
  exact List.mem_append_left _ (List.mem_append_left _ (mem_specQ_auxOf C Q f hS hc))

/-! ## `PUB` at `acc_in` of `accV` coordinates -/

/-- **The public values' header lanes, as words of the stream**, at `acc_in` of `accV + 1` scalars of `w` lanes each,
read by `rd` and laid out by `lw` (`pubX_hdrLanes` generalised; `hflat`: the scalars' lanes are the header's words). -/
theorem pubOfW_hdrLanesW (rd : ByteArray → ℕ → FE) (w : ℕ) (lw : FE → List FK) (accV : ℕ) (x : List UInt8)
    (hflat : ∀ n, ((List.range n).map fun i ↦ rd (Lvm.VEq.sigOfX x) (headerAt offAcc + 8 * w * i)).flatMap lw =
      (List.range (w * n)).map fun j ↦ kAt (Lvm.VEq.sigOfX x) (headerAt offAcc + 8 * j)) :
    (pubOfW rd (8 * w) accV (Lvm.VEq.hdX x).vk (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x)).hdrLanesW lw =
      (List.range (615 + w * (accV + 1))).map fun k ↦ kAt (Lvm.VEq.sigOfX x) (headerAt 8 + 8 * k) := by
  rw [show 615 + w * (accV + 1) = 1 + 4 + 4 + 4 + 1 + 4 + 597 + w * (accV + 1) by omega]
  simp only [map_range_add]
  have hd : (Lvm.VEq.hdX x).vk = digestAt (hdrBytesX x) 16 := rfl
  have hacc : ((List.range accV).map fun i ↦ rd (Lvm.VEq.sigOfX x) (headerAt (offAcc + 8 * w * i))) ++
      [rd (Lvm.VEq.sigOfX x) (headerAt (offAcc + 8 * w * accV))] =
      (List.range (accV + 1)).map fun i ↦ rd (Lvm.VEq.sigOfX x) (headerAt offAcc + 8 * w * i) := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun i _ ↦ ?_) ?_
    · exact congrArg (rd (Lvm.VEq.sigOfX x)) (by simp only [headerAt, offAcc]; omega)
    · exact congrArg (fun o ↦ [rd (Lvm.VEq.sigOfX x) o]) (by simp only [headerAt, offAcc]; omega)
  unfold Pub.hdrLanesW pubOfW pubOf
  simp only [hd, digestLanes_digestAt, List.append_assoc, hacc, hflat]
  refine congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_
    (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_))))))
  · simp [kAt]
  · refine List.map_congr_left fun i _ ↦ ?_
    rw [kAt_sigOfX, show 8 + 8 * (1 + i) = 16 + 8 * i by omega]
    rfl
  · exact seg _ 48 5 4 rfl
  · exact seg _ 80 9 4 rfl
  · simp [kAt, headerAt]
  · exact seg _ 120 14 4 rfl
  · rw [show sigBytes / 8 = 597 from rfl]; exact seg _ 152 18 597 rfl
  · exact List.map_congr_left fun j _ ↦
      congrArg (kAt (Lvm.VEq.sigOfX x)) (by simp only [headerAt, offAcc, sigBytes]; omega)

/-- **The public values' header lanes, as words of the stream** (`pubX_hdrLanes` at `acc_in` of `accV`
coordinates: `pubLanesX accV` lanes). -/
theorem pubOfA_hdrLanes (accV : ℕ) (x : List UInt8) :
    (pubOfA accV (Lvm.VEq.hdX x).vk (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x)).hdrLanes =
      (List.range (pubLanesX accV)).map fun k ↦ kAt (Lvm.VEq.sigOfX x) (headerAt 8 + 8 * k) := by
  rw [show pubLanesX accV = 615 + 3 * (accV + 1) by unfold pubLanesX; omega]
  exact pubOfW_hdrLanesW feAt 3 FE.lanes accV x (flatMap_lanes _ _)

/-- Two-lane `E2` scalars of 16 bytes are consecutive header words (`flatMap_lanes` at S2GT, re-freeze A2). -/
theorem flatMap_lanes2 (b : ByteArray) (o : ℕ) :
    ∀ n, ((List.range n).map fun i ↦ fe16At b (o + 8 * 2 * i)).flatMap FE.lanes2 =
      (List.range (2 * n)).map fun j ↦ kAt b (o + 8 * j)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_lanes2 b o n,
      show 2 * (n + 1) = 2 * n + 2 by ring, map_range_add, List.map_singleton, List.flatMap_singleton]
    refine congrArg₂ (· ++ ·) rfl ?_
    simp only [FE.lanes2, fe16At, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
    refine congrArg₂ List.cons (congrArg (kAt b) (by ring)) (congrArg₂ List.cons (congrArg (kAt b) (by ring)) rfl)

/-- **S2GT's `PUB` lanes are the header's** (`pubXT`'s `hdrLanesT`, `pubLanesT = 707` lanes; re-freeze A2). -/
theorem pubXT_lane (x : List UInt8) {j : ℕ} (hj : j < 615 + 2 * (Lvm.VEq.accVT + 1)) :
    (Lvm.VEq.pubXT x).hdrLanesT.getD j 0 = hdrLane x j := by
  rw [show (Lvm.VEq.pubXT x).hdrLanesT = (pubOfW fe16At (8 * 2) Lvm.VEq.accVT (Lvm.VEq.hdX x).vk
      (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x)).hdrLanesW FE.lanes2 from rfl,
    pubOfW_hdrLanesW fe16At 2 FE.lanes2 Lvm.VEq.accVT x (flatMap_lanes2 _ _), hdrLane_eq_kAt]
  simp [List.getD_eq_getElem?_getD, hj]

/-- **S2GF's `PUB` lanes are the header's** (`pubXF`, `pubLanesX accVF = 750` lanes). -/
theorem pubXF_lane (x : List UInt8) {j : ℕ} (hj : j < pubLanesX accVF) :
    (pubXF x).hdrLanes.getD j 0 = hdrLane x j := by
  rw [show pubXF x = pubOfA accVF (Lvm.VEq.hdX x).vk (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x) from rfl,
    pubOfA_hdrLanes, hdrLane_eq_kAt]
  simp [List.getD_eq_getElem?_getD, hj]

/-! ## The guard's facts at a stage -/

/-- **The facts a guard gives `nodeSoundF`'s circuit-side hypotheses** at a configuration `C` with `B` sponge blocks
and `nPub` `PUB` lanes: `StaticFactsTX`, the node checks `nodeChkBG B nPub`, `σ′` in `S`, the program's `K` cells
past the inputs, the mini-bus's tables, the layout's `BITS` blocks. -/
structure NodeGC (C : QCfg) (B nPub : ℕ) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) : Prop where
  st : StaticFactsTX C F Q tl N
  chk : nodeChkBG B nPub C F Q tl N = true
  sig : SigInS N
  cells : nK C ≤ Q.cells .K
  mb : N.mbT = mbTOf C F
  aux : ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
    (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ tl.aux

/-- **The facts the S2GF guard gives** (`NodeGC` at `cfgF20`, `B = spongeBlocks P20F`, `pubLanesX accVF`). -/
abbrev NodeGF (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) : Prop :=
  NodeGC cfgF20 (spongeBlocks P20F) (pubLanesX accVF) F Q tl N

/-- **`NodeGC` from the guard's Bools** (`staticOkTX`, `nodeChkBG`, `sigInSB`) on the layout shape `specQF C`. -/
theorem nodeGC_of {C : QCfg} {B' nPub : ℕ} {F : TFrz} {δ : List Seg} {Q : Program} {tl : Typed.Lay} {N : TNat}
    {B : BM Unit} {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)} (hQ : Q = toProgram (nK C) 0 B)
    (hδ : δ = (B ⟨nK C, 0⟩).2) (hl : tl = (mkLayD Q (specQF C Q pw) d).1)
    (hmb : N.mbT = mbTOf C F) (hst : staticOkTX C F δ Q tl N = true)
    (hchk : nodeChkBG B' nPub C F Q tl N = true) (hσ : sigInSB N = true) :
    NodeGC C B' nPub F Q tl N :=
  ⟨staticFactsTX hQ hδ hst, hchk, sigInS_of hσ, by rw [hQ]; exact nK_le_cells _ _ _, hmb,
    by rw [hl]; exact aux_specQF C Q pw d⟩

/-- **`NodeGF` from the guard's Bools** on the S2GF layout shape. -/
theorem nodeGF_of {F : TFrz} {δ : List Seg} {Q : Program} {tl : Typed.Lay} {N : TNat} {B : BM Unit}
    {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)} (hQ : Q = toProgram (nK cfgF20) 0 B)
    (hδ : δ = (B ⟨nK cfgF20, 0⟩).2) (hl : tl = (mkLayD Q (specQF cfgF20 Q pw) d).1)
    (hmb : N.mbT = mbTOf cfgF20 F) (hst : staticOkTX cfgF20 F δ Q tl N = true)
    (hchk : nodeChkBG (spongeBlocks P20F) (pubLanesX accVF) cfgF20 F Q tl N = true) (hσ : sigInSB N = true) :
    NodeGF F Q tl N :=
  nodeGC_of hQ hδ hl hmb hst hchk hσ

/-! ## The hypotheses on a pair, at a stage -/

/-- The word `1` holds `1` on a pair's words (`THypX.ok`). -/
theorem one_zTX {Q : Program} {tl : Typed.Lay} {N : TNat} (H : THypX (N.inst Q tl)) (pb : List UInt8 → Lvm.Pub)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} : zTX (N.inst Q tl) pb x qm qr tl.one = 1 :=
  zOf_one (N.inst Q tl) H.ok.2 lay26 (pb x) qm qr

section PairC

/-- The stage's static facts the pair lemmas read (`P20`'s shape: `ν = 23`, `ν_rec = 19`, `C_rec` of `2^14` rows,
the stream block at `CMain.sOff20`, `ln = 20`, `B ≤ 2^13`, `PUB` covering the fixed header). -/
structure StageC (C : QCfg) (B nPub : ℕ) : Prop where
  nu : C.p.nuMain = 23
  nuRec : C.p.nuRec = 19
  rl : C.rl = 14
  s0 : (layout0 C.p).s = CMain.sOff20
  rr : C.p.recRowsLog = 14
  hnK : 17 * 2 ^ 14 ≤ nK C
  hB : B ≤ 2 ^ 13
  hm : 2 ^ (lay C).m ≤ 17 * 2 ^ 14
  hn : 615 ≤ nPub
  ln : 1 ≤ C.ln ∧ C.ln ≤ 62

variable {C : QCfg} {B nPub : ℕ} {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat}
  (S : NodeGC C B nPub F Q tl N) (pl : Lvm.Pub → List FK) (pb : List UInt8 → Lvm.Pub)
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

/-- V_S's region check at `ν = 23`, `ν_rec = 19`. -/
theorem regsC (G : StageC C B nPub) : N.okB 23 19 = true := by
  have h := S.st.regs
  rwa [G.nu, G.nuRec] at h

/-- **`hqlt`**: QLT's cells hold `qltData` (any pair). -/
theorem hqltC (Ti : TInst) (hTi : Ti.lay = tl) :
    ∀ y < (qltData C.p (lay C)).length,
      (memTX Ti pb x qm qr).k ((lay C).qt + y) = (qltData C.p (lay C)).getD y 0 := by
  subst hTi
  exact hqltG C _ S.st.cst _

/-- **The non-`readd` rows hold** on the memory of a pair whose words meet the coordinate-split relation. -/
theorem hlinC (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    NonReaddHolds Q (memTX (N.instL pl Q tl) pb x qm qr) :=
  nonReadd_of_wiringX Q tl _ S.st.wf S.st.twins S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW

/-- **`ReaddOk` on a stream-block pair's memory** (`readdTGL`), from the relation and the mini-bus's balance. -/
theorem readdC (G : StageC C B nPub) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : LayOk lay26 N.mbT) (hM : M3Holds (inst lay26 N.mbT hτ) () (stackOf lay26 qm qr)) (hSB : SBlk qm qr) :
    ReaddOk Q (memTX (N.instL pl Q tl) pb x qm qr) := by
  have hτ' : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ := fun t ht ↦ hτ t (by rw [S.mb]; exact ht)
  have hL' : LayOk lay26 (mbTOf C F) := by rwa [S.mb] at hL
  exact readdTGL C F Q tl N pl (pb x) B nPub S.st.hlay (regsC S G) S.st.hlayOk S.sig S.chk G.rl G.s0 G.rr G.hnK
    S.cells hτ' hL' (m3Holds_eq S.mb hM) hSB (hlinC S pl pb hone hW)

/-- **`hholds`**: the program's rows hold and assert on a stream-block pair's memory. -/
theorem hholdsC (G : StageC C B nPub) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : LayOk lay26 N.mbT) (hM : M3Holds (inst lay26 N.mbT hτ) () (stackOf lay26 qm qr)) (hSB : SBlk qm qr) :
    (N.instL pl Q tl).Q.Holds (memTX (N.instL pl Q tl) pb x qm qr) ∧
      (N.instL pl Q tl).Q.Asserts (memTX (N.instL pl Q tl) pb x qm qr) :=
  holds_memTX S.st.wf S.st.twins S.st.hlay hone hW (readdC S pl pb G hone hW hτ hL hM hSB)

/-- **`hmap`**: the input map (`InMapMB B nPub`), `PUB`'s cells the header's lanes (`hpub`). -/
theorem hmapC (G : StageC C B nPub) (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hSB : SBlk qm qr) :
    InMapMB B nPub (lay C) (sigIn C) (memTX (N.instL pl Q tl) pb x qm qr) vk x qm qr := by
  have hchk := S.chk
  simp only [nodeChkBG, Bool.and_eq_true] at hchk
  exact inMapTGL _ _ C N pl Q tl pb S.st.hlay (regsC S G) S.st.hlayOk S.sig hchk.1.1 G.hB G.hm G.hn hpub qm qr hSB
    hok hb

/-- The `BITS` classes' outputs on a pair's memory (`outsOnC_of`, `auxRow_of_wiringX`). -/
theorem outsOnC (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    OutsOnC C (memTX (N.instL pl Q tl) pb x qm qr).k := by
  obtain ⟨bw, haux⟩ := S.aux
  exact outsOnC_of C tl _ bw haux fun hk hj hr ↦
    auxRow_of_wiringX Q tl _ S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW hk hj hr

/-- **`hpos`**: Q_link's position bit cells are the answers' bits (`hposTC`). -/
theorem hposC (G : StageC C B nPub) (hSt : StreamOk C.p) (hQ : QOk C.p (lay C))
    (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) {vk c : RecursionFast.Digest}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hSB : SBlk qm qr) :
    ∀ k < (opens C.p).length, ∀ j < ((opens C.p).getD k default).L.t,
      ∀ z < ((opens C.p).getD k default).L.height,
      (memTX (N.instL pl Q tl) pb x qm qr).k
          (bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z) =
        if ansBit C.p (wsC qr) (((opens C.p).getD k default).pe + j / 8)
          (j % 8 * ((opens C.p).getD k default).L.height + z) then 1 else 0 :=
  hposTC hSt hQ (outsOnC S pl pb hone hW) (hmapC S pl pb G hpub hok hb hSB).stream

/-- **`hbits`**: Q_sig's `SigBits` on a pair's memory (`sigBits_ofC`). -/
theorem hbitsC (G : StageC C B nPub) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    SigBits (sigIn C) (qsig (sigIn C) (p1P (lay C) (nK C) 0 C.p)).1 (memTX (N.instL pl Q tl) pb x qm qr).k :=
  sigBits_ofC C (outsOnC S pl pb hone hW) G.ln

end PairC

/-! ## At S2GF -/

/-- S2GF's stage facts. -/
theorem stageF20 : StageC cfgF20 (spongeBlocks P20F) (pubLanesX accVF) :=
  ⟨by decide +kernel, by decide +kernel, rfl, by show (layout0 P20F).s = _; decide +kernel, by decide +kernel,
    by decide, by rw [spongeBlocks_P20F.1]; norm_num, by decide, by decide, ⟨by decide, by decide⟩⟩

section Pair

variable {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat} (S : NodeGF F Q tl N) (H : THypX (N.inst Q tl))
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

/-- V_S's region check at S2GF's `ν = 23`, `ν_rec = 19`. -/
theorem regsF : N.okB 23 19 = true := regsC S stageF20

/-- **`hqlt` at S2GF**: QLT's cells hold `qltData` (any pair). -/
theorem hqltF (Ti : TInst) (hTi : Ti.lay = tl) :
    ∀ y < (qltData P20F (lay cfgF20)).length,
      (memF Ti x qm qr).k ((lay cfgF20).qt + y) = (qltData P20F (lay cfgF20)).getD y 0 :=
  hqltC S pubXF Ti hTi

include H

/-- **The non-`readd` rows hold** on a good pair's memory at S2GF. -/
theorem hlinF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) : NonReaddHolds Q (memF (N.inst Q tl) x qm qr) :=
  hlinC S Pub.hdrLanes pubXF H.ok.2 hG.1.1.1.1

/-- **`ReaddOk` on a good stream-block pair's memory** at S2GF (`readdTG`). -/
theorem readdF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    ReaddOk Q (memF (N.inst Q tl) x qm qr) :=
  readdC S Pub.hdrLanes pubXF stageF20 H.ok.2 hG.1.1.1.1.1 H.hτ H.layOk hG.1.1.1.1.2 hG.2

/-- **`hholds` at S2GF**: the program's rows hold and assert on a good stream-block pair's memory. -/
theorem hholdsF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    (N.inst Q tl).Q.Holds (memF (N.inst Q tl) x qm qr) ∧ (N.inst Q tl).Q.Asserts (memF (N.inst Q tl) x qm qr) :=
  hholdsC S Pub.hdrLanes pubXF stageF20 H.ok.2 hG.1.1.1.1.1 H.hτ H.layOk hG.1.1.1.1.2 hG.2

/-- **`hmap` at S2GF**: the input map (`InMapMB` at `B = 4,295`, `PUB` of `pubLanesX 44` lanes). -/
theorem hmapF {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF (N.inst Q tl) x qm qr)
      vk x qm qr :=
  hmapC S Pub.hdrLanes pubXF stageF20 (fun x _ hj ↦ pubXF_lane x hj) hok hb hG.2

/-- The `BITS` classes' outputs on a good pair's memory at S2GF (`outsOnC_of`, `auxRow_of_wiringX`). -/
theorem outsOnF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) : OutsOnC cfgF20 (memF (N.inst Q tl) x qm qr).k :=
  outsOnC S Pub.hdrLanes pubXF H.ok.2 hG.1.1.1.1

/-- **`hpos` at S2GF**: Q_link's position bit cells are the answers' bits (`hposTC`). -/
theorem hposF {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    ∀ k < (opens P20F).length, ∀ j < ((opens P20F).getD k default).L.t,
      ∀ z < ((opens P20F).getD k default).L.height,
      (memF (N.inst Q tl) x qm qr).k (bitBase P20F (lay cfgF20) k + ((opens P20F).getD k default).L.height * j + z) =
        if ansBit P20F (wsC qr) (((opens P20F).getD k default).pe + j / 8)
          (j % 8 * ((opens P20F).getD k default).L.height + z) then 1 else 0 := by
  have h := hposC S Pub.hdrLanes pubXF stageF20 streamOk_P20F hQF20 (fun x _ hj ↦ pubXF_lane x hj) H.ok.2
    hG.1.1.1.1.1 hok hb hG.2
  rw [show cfgF20.p = P20F from rfl] at h
  exact h

/-- **`hbits` at S2GF**: Q_sig's `SigBits` on a good pair's memory (`sigBits_ofC`). -/
theorem hbitsF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) :
    SigBits (sigIn cfgF20) (qsig (sigIn cfgF20) (p1P (lay cfgF20) (nK cfgF20) 0 P20F)).1
      (memF (N.inst Q tl) x qm qr).k :=
  hbitsC S Pub.hdrLanes pubXF stageF20 H.ok.2 hG.1.1.1.1

end Pair

/-- **The Keccak half of S2GF's good pair** (`GoodKP P20F`; `goodK_of`'s twin on `GkF`). -/
theorem goodKF_of {Ti : TInst} {H : THypX Ti} {vk c : RecursionFast.Digest} {x : List UInt8}
    {qm : Column CMain.nu20} {qr : Column 19} (hok : okS vk c x = true) (hG : E2V.GoodTF Ti H x qm qr) :
    GoodKP P20F x (qm, qr) :=
  ⟨hG.2.1, by rw [← contRowsF_eq]; exact hG.2.2, hG.1.1.2 (okS_n hok).2⟩

/-- **`nodeSoundF` at S2GF's good pair `GoodTF ∧ SBlk`**, every circuit-side hypothesis discharged from the guard's
facts `NodeGF`; what remains is Q_arith's soundness (`harith`). -/
theorem nodeSoundFG {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat} (S : NodeGF F Q tl N)
    (H : THypX (N.inst Q tl)) (vk : RecursionFast.Digest) (Nv : TypedV.TNat) (qa : BM Unit)
    (hQ : Q = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qa))
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 →
      E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr →
      InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF (N.inst Q tl) x qm qr) vk x qm qr →
      LaneLink P20F (wsC qr) → LinkOk P20F (decode P20F (wsC qr)) →
      Ok (ctxOf (N.inst Q tl).Q) (memF (N.inst Q tl) x qm qr) qa (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F) →
      E2V.decideFFX P20F Nv vk (hdrOf x).cL (traceBytesB (decode P20F (wsC qr))) = true) :
    NodeSound (E2V.VSFX Nv) vk (fun x qm qr ↦ E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) (childSP P20F) :=
  nodeSoundF vk Nv (N.inst Q tl) qa _ hQ S.st.inj (fun _ _ _ _ hok hG ↦ goodKF_of hok hG.1)
    (fun _ _ _ _ _ _ hG ↦ hholdsF S H hG) (fun _ _ _ _ hok hb hG ↦ hmapF S H hok hb hG)
    (fun _ _ _ _ _ _ _ ↦ hqltF S _ rfl) (fun _ _ _ _ hok hb hG ↦ hposF S H hok hb hG)
    (fun _ _ _ _ _ _ hG ↦ hbitsF S H hG.1) harith

end Lvm.E2Q
