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

/-- **The public values' header lanes, as words of the stream** (`pubX_hdrLanes` at `acc_in` of `accV`
coordinates: `pubLanesX accV` lanes). -/
theorem pubOfA_hdrLanes (accV : ℕ) (x : List UInt8) :
    (pubOfA accV (Lvm.VEq.hdX x).vk (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x)).hdrLanes =
      (List.range (pubLanesX accV)).map fun k ↦ kAt (Lvm.VEq.sigOfX x) (headerAt 8 + 8 * k) := by
  have hp : pubLanesX accV = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 3 * (accV + 1) := by unfold pubLanesX; omega
  rw [hp]
  simp only [map_range_add]
  have hd : (Lvm.VEq.hdX x).vk = digestAt (hdrBytesX x) 16 := rfl
  have hacc : ((List.range accV).map fun i ↦ feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i))) ++
      [feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * accV))] =
      (List.range (accV + 1)).map fun i ↦ feAt (Lvm.VEq.sigOfX x) (headerAt offAcc + 24 * i) := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun i _ ↦ ?_) ?_
    · exact congrArg (feAt (Lvm.VEq.sigOfX x)) (by simp only [headerAt, offAcc, eBytes]; omega)
    · exact congrArg (fun o ↦ [feAt (Lvm.VEq.sigOfX x) o]) (by simp only [headerAt, offAcc, eBytes]; omega)
  unfold Pub.hdrLanes pubOfA pubOf
  simp only [hd, digestLanes_digestAt, List.append_assoc, hacc, flatMap_lanes]
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

/-- **S2GF's `PUB` lanes are the header's** (`pubXF`, `pubLanesX accVF = 750` lanes). -/
theorem pubXF_lane (x : List UInt8) {j : ℕ} (hj : j < pubLanesX accVF) :
    (pubXF x).hdrLanes.getD j 0 = hdrLane x j := by
  rw [show pubXF x = pubOfA accVF (Lvm.VEq.hdX x).vk (Lvm.VEq.hdX x).stmt (Lvm.VEq.sigOfX x) from rfl,
    pubOfA_hdrLanes, hdrLane_eq_kAt]
  simp [List.getD_eq_getElem?_getD, hj]

/-! ## The S2GF guard's facts -/

/-- **The facts the S2GF guard gives `nodeSoundF`'s circuit-side hypotheses**: `StaticFactsTX`, the node checks at
S2GF's `B = spongeBlocks P20F` and `pubLanesX accVF` `PUB` lanes, `σ′` in `S`, the program's `K` cells past the
inputs, the mini-bus's tables, the layout's `BITS` blocks. -/
structure NodeGF (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) : Prop where
  st : StaticFactsTX cfgF20 F Q tl N
  chk : nodeChkBG (spongeBlocks P20F) (pubLanesX accVF) cfgF20 F Q tl N = true
  sig : SigInS N
  cells : nK cfgF20 ≤ Q.cells .K
  mb : N.mbT = mbTOf cfgF20 F
  aux : ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs cfgF20 noData)[i]? = some S → c ∈ S.chunks →
    (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ tl.aux

/-- **`NodeGF` from the guard's Bools** (`staticOkTX`, `nodeChkBG`, `sigInSB`) on the S2GF layout shape. -/
theorem nodeGF_of {F : TFrz} {δ : List Seg} {Q : Program} {tl : Typed.Lay} {N : TNat} {B : BM Unit}
    {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)} (hQ : Q = toProgram (nK cfgF20) 0 B)
    (hδ : δ = (B ⟨nK cfgF20, 0⟩).2) (hl : tl = (mkLayD Q (specQF cfgF20 Q pw) d).1)
    (hmb : N.mbT = mbTOf cfgF20 F) (hst : staticOkTX cfgF20 F δ Q tl N = true)
    (hchk : nodeChkBG (spongeBlocks P20F) (pubLanesX accVF) cfgF20 F Q tl N = true) (hσ : sigInSB N = true) :
    NodeGF F Q tl N :=
  ⟨staticFactsTX hQ hδ hst, hchk, sigInS_of hσ, by rw [hQ]; exact nK_le_cells _ _ _, hmb,
    by rw [hl]; exact aux_specQF cfgF20 Q pw d⟩

/-! ## The hypotheses on a good pair -/

/-- The word `1` holds `1` on a pair's words (`THypX.ok`). -/
theorem one_zTX {Q : Program} {tl : Typed.Lay} {N : TNat} (H : THypX (N.inst Q tl)) (pb : List UInt8 → Lvm.Pub)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} : zTX (N.inst Q tl) pb x qm qr tl.one = 1 :=
  zOf_one (N.inst Q tl) H.ok.2 lay26 (pb x) qm qr

section Pair

variable {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat} (S : NodeGF F Q tl N) (H : THypX (N.inst Q tl))
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

/-- V_S's region check at S2GF's `ν = 23`, `ν_rec = 19`. -/
theorem regsF : N.okB 23 19 = true := by
  have h := S.st.regs
  rwa [show cfgF20.p.nuMain = 23 by decide +kernel, show cfgF20.p.nuRec = 19 by decide +kernel] at h

/-- **`hqlt` at S2GF**: QLT's cells hold `qltData` (any pair). -/
theorem hqltF (Ti : TInst) (hTi : Ti.lay = tl) :
    ∀ y < (qltData P20F (lay cfgF20)).length,
      (memF Ti x qm qr).k ((lay cfgF20).qt + y) = (qltData P20F (lay cfgF20)).getD y 0 := by
  subst hTi
  exact hqltG cfgF20 _ S.st.cst _

include H

/-- **The non-`readd` rows hold** on a good pair's memory at S2GF. -/
theorem hlinF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) : NonReaddHolds Q (memF (N.inst Q tl) x qm qr) :=
  nonReadd_of_wiringX Q tl _ S.st.wf S.st.twins S.st.hlay (one_zTX H pubXF) hG.1.1.1.1

/-- **`ReaddOk` on a good stream-block pair's memory** at S2GF (`readdTG`). -/
theorem readdF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    ReaddOk Q (memF (N.inst Q tl) x qm qr) := by
  have hmb : (N.inst Q tl).mbT = mbTOf cfgF20 F := S.mb
  have hτ : ∀ t ∈ mbTOf cfgF20 F, t.τ ≤ lay26.μ := fun t ht ↦ H.hτ t (by rw [hmb]; exact ht)
  have hL : LayOk lay26 (mbTOf cfgF20 F) := by have := H.layOk; rwa [hmb] at this
  exact readdTG cfgF20 F Q tl N (pubXF x) _ _ S.st.hlay (regsF S) S.st.hlayOk S.sig S.chk rfl
    (by show (layout0 P20F).s = _; decide +kernel) (by decide +kernel) (by decide) S.cells hτ hL
    (m3Holds_eq S.mb hG.1.1.1.1.2) hG.2 (hlinF S H hG.1)

/-- **`hholds` at S2GF**: the program's rows hold and assert on a good stream-block pair's memory. -/
theorem hholdsF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    (N.inst Q tl).Q.Holds (memF (N.inst Q tl) x qm qr) ∧ (N.inst Q tl).Q.Asserts (memF (N.inst Q tl) x qm qr) :=
  holds_memTX S.st.wf S.st.twins S.st.hlay H.ok.2 hG.1.1.1.1.1 (readdF S H hG)

/-- **`hmap` at S2GF**: the input map (`InMapMB` at `B = 4,295`, `PUB` of `pubLanesX 44` lanes). -/
theorem hmapF {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF (N.inst Q tl) x qm qr)
      vk x qm qr := by
  have hchk := S.chk
  simp only [nodeChkBG, Bool.and_eq_true] at hchk
  exact inMapTG _ _ cfgF20 N Q tl pubXF S.st.hlay (regsF S) S.st.hlayOk S.sig hchk.1.1
    (by rw [spongeBlocks_P20F.1]; norm_num) (by decide) (by decide) (fun x _ hj ↦ pubXF_lane x hj) qm qr hG.2 hok hb

/-- The `BITS` classes' outputs on a good pair's memory at S2GF (`outsOnC_of`, `auxRow_of_wiringX`). -/
theorem outsOnF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) : OutsOnC cfgF20 (memF (N.inst Q tl) x qm qr).k := by
  obtain ⟨bw, haux⟩ := S.aux
  exact outsOnC_of cfgF20 tl _ bw haux fun hk hj hr ↦
    auxRow_of_wiringX Q tl _ S.st.hlay (one_zTX H pubXF) hG.1.1.1.1 hk hj hr

/-- **`hpos` at S2GF**: Q_link's position bit cells are the answers' bits (`hposTC`). -/
theorem hposF {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr ∧ SBlk qm qr) :
    ∀ k < (opens P20F).length, ∀ j < ((opens P20F).getD k default).L.t,
      ∀ z < ((opens P20F).getD k default).L.height,
      (memF (N.inst Q tl) x qm qr).k (bitBase P20F (lay cfgF20) k + ((opens P20F).getD k default).L.height * j + z) =
        if ansBit P20F (wsC qr) (((opens P20F).getD k default).pe + j / 8)
          (j % 8 * ((opens P20F).getD k default).L.height + z) then 1 else 0 :=
  by
  have h := hposTC (C := cfgF20) streamOk_P20F hQF20 (outsOnF S H hG.1) (hmapF S H hok hb hG).stream
  rw [show cfgF20.p = P20F from rfl] at h
  exact h

/-- **`hbits` at S2GF**: Q_sig's `SigBits` on a good pair's memory (`sigBits_ofC`). -/
theorem hbitsF (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) :
    SigBits (sigIn cfgF20) (qsig (sigIn cfgF20) (p1P (lay cfgF20) (nK cfgF20) 0 P20F)).1
      (memF (N.inst Q tl) x qm qr).k :=
  sigBits_ofC cfgF20 (outsOnF S H hG) ⟨by decide, by decide⟩

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
