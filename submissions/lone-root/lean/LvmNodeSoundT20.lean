-- New for lvm2 (roll 8 = B1, L-D): the guard-side pieces of `nodeT20` (L-W's stub `LvmCertT20.nodeT20`): of
-- `nodeSoundT`'s (`LvmNodeSoundT`) hypotheses, `ReaddOk` (`LvmNodeSoundTRd`, from the guard's `rdChkB`, the
-- mini-bus's `M3Holds` and L-B's `rowDef_of_wiring`), the input map and QLT (`LvmNodeSoundTIn`), Q_arith through the
-- typed HAR (`LvmQTypedHarS.harithT20`, L-H) and `Φ_Q` (`PhiQC_eq`, `AccOkT`). The `BITS` rows' facts (`hpos`,
-- `hbits`, `BVT`) and the assembly: `LvmNodeSoundT20B.nodeT20B`.
import LvmNodeSoundTRd
import LvmQTypedHarS

/-!
# `nodeT20`'s guard-side pieces

* **`hlinT`**: the non-`readd` rows hold on a good pair's memory (`rowDef_of_wiring`, L-B).
* **`readdT`**: `ReaddOk` on it (`readdOk_of_chk` with `mbRead_seeded` on `GoodT`'s mini-bus `M3Holds` and the
  stream's cells from `inMapB`).
* **`decideFT_of`**: `decideFT = decideCoreT && Φ_Q(acc_out) == y`: the HAR gives the first and `acc_out = acc_in`,
  `AccOkT` (in `GoodT`) and `PhiQC_eq` (the guard's `cache`, rewritten by `cacheT20_eq`) the second.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

theorem mbT_TiB : TiB.mbT = mbTOf cfg20 frz20 := rfl

theorem m3Holds_eq {L : Lvm.M3.Lay} {t t' : List Tab} (h : t = t') {hτ : ∀ u ∈ t, u.τ ≤ L.μ}
    {hτ' : ∀ u ∈ t', u.τ ≤ L.μ} {q : Column L.μ} (hm : M3Holds (inst L t hτ) () q) :
    M3Holds (inst L t' hτ') () q := by
  subst h; exact hm

/-- **The non-`readd` rows hold** on a good pair's memory (L-B's `rowDef_of_wiring`). -/
theorem hlinT (S : Lvm.CT.SF20) {H : THyp TiB} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : NonReaddHolds QB20 (memT x qm qr) :=
  fun _ hi hop ↦ rowDef_of_wiring QB20 layT20 (zT x qm qr) S.wf S.hlay (zT_one H x qm qr) (goodT_wiring hG) hi hop

/-- `V_S`'s regions fit `ν = 23`, `ν_rec = 19` (the guard's `regs`). -/
theorem okB20 (S : Lvm.CT.SF20) : NT20.okB 23 19 = true := by
  have h := S.regs
  rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, show P20.nuMain = 23 by decide +kernel,
    show P20.nuRec = 19 by decide +kernel] at h

/-- **`ReaddOk` on a good pair's memory** from the guard's checks (M′ `S2GM`: on a stream-block pair, `SBlk`; the
seeds are `S`'s `C_main` words). -/
theorem readdT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ReaddOk QB20 (memT x qm qr) := by
  simp only [nodeChkB, Bool.and_eq_true] at hchk
  obtain ⟨⟨hin, hrd⟩, hsd⟩ := hchk
  simp only [mbSeedsOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsd
  obtain ⟨hblk, hlen⟩ := hsd
  have hτ : ∀ t ∈ mbTOf cfg20 frz20, t.τ ≤ lay26.μ := fun t ht ↦ H.hτ t (by rw [mbT_TiB]; exact ht)
  have hlay : LayOk lay26 (mbTOf cfg20 frz20) := by have := H.layOk; rwa [mbT_TiB] at this
  have hM : M3Holds (inst lay26 (mbTOf cfg20 frz20) hτ) () (stackOf lay26 qm qr) :=
    m3Holds_eq mbT_TiB hG.1.1.1.2
  have hS := (inMap_of_ok NT20 QB20 layT20 S.hlay x qm qr hSB (okB20 S) S.hlayOk S.sig hin).1
  refine readdOk_of_chk cfg20 frz20 QB20 layT20 NT20 S.hlay (pubX x) qm qr hSB (okB20 S) S.hlayOk S.sig hrd ?_ ?_
    (hlinT S hG)
  · intro τ wa wv hp y hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    exact mbRead_seeded cfg20 frz20 lay26 hτ qm qr hlay hM hlen hk hy
  · intro lq hlq x' hx'
    obtain ⟨hl, hq⟩ := hblk lq hlq
    have hrl : cfg20.rl = 14 := rfl
    rw [hrl] at hq
    have hx'16 : x' < 16 := hx'
    have hj : 17 * (lq.2 + x') + lq.1 < 17 * 2 ^ 14 := by omega
    have e : (Lvm.QAsm.lay cfg20).sb + 17 * lq.2 + lq.1 + 17 * x' =
        (Lvm.QAsm.lay cfg20).sb + (17 * (lq.2 + x') + lq.1) := by ring
    have h16 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    refine ⟨?_, ?_⟩
    · have hsb : (Lvm.QAsm.lay cfg20).sb = 0 := rfl
      have hnK : 17 * 2 ^ 14 ≤ nK cfg20 := by decide
      have hc : nK cfg20 ≤ QB20.cells .K := by rw [QB20_qn]; exact nK_le_cells _ _ _
      rw [e, hsb]
      omega
    · have h1 := hS (17 * (lq.2 + x') + lq.1) hj
      beta_reduce at h1
      have e2 : (17 * (lq.2 + x') + lq.1) % 17 * 2 ^ 14 + (17 * (lq.2 + x') + lq.1) / 17 =
          lq.1 * 2 ^ cfg20.rl + lq.2 + x' := by
        rw [hrl, h16]; omega
      have hs : Lvm.sCol cfg20.p lq.1 + lq.2 + x' = CMain.sOff20 + (lq.1 * 2 ^ cfg20.rl + lq.2 + x') := by
        have e3 : (layout0 P20).s = CMain.sOff20 := by rw [Lvm.layout0_P20]
        simp only [Lvm.sCol, show cfg20.p = P20 from rfl, e3, show P20.recRowsLog = 14 by decide, hrl]
        omega
      rw [e, h1, e2, hs, comCell_S hSB (by rw [hrl, h16]; omega)]

/-- `Φ_Q` at the incoming accumulator is its claim (`AccOkT`), through the cache (`PhiQC_eq`, `cacheT20_eq`). -/
theorem phi_accIn (S : Lvm.CT.SF20) (H : THyp TiB) (x : List UInt8) (hacc : AccOkT TiB (pubX x)) :
    PhiQC cacheT20 (pubX x).accIn.pt = (pubX x).accIn.y := by
  have hc := S.cache
  rw [cacheT20_eq] at hc ⊢
  rw [PhiQC_eq QB20 layT20 S.hlay hc _ (H.acc x)]
  have h := hacc
  unfold AccOkT PhiQ at h
  rw [Q_TiB, lay_TiB, List.map_map] at h
  simp only [Function.comp_def, FE.ofExt3_toExt3, List.map_id'] at h
  exact FE.toExt3_injective h

theorem NT20_phi : NT20.phi = PhiQC cacheT20 := rfl

/-- **`decideFT` from the HAR and the incoming accumulator.** -/
theorem decideFT_of (S : Lvm.CT.SF20) (H : THyp TiB) {vk cL : RecursionFast.Digest} {sig : ByteArray}
    {x : List UInt8} (hacc : AccOkT TiB (pubX x)) (hc : decideCoreT P20 NT20 vk cL sig = true)
    (ha : accOutOfT P20 NT20 vk cL sig = (pubX x).accIn) : decideFT P20 NT20 vk cL sig = true := by
  rw [decideFT_eq, hc, ha, NT20_phi, phi_accIn S H x hacc]
  simp

end Lvm.NS
