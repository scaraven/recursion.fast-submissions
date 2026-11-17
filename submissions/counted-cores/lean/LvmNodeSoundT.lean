-- New for lvm2 (roll 8 = B1, L-D): `NodeSound` for the typed backend's good pair `GoodT` (B-DES §2). WP-14c's
-- `nodeSound_main` (`LvmNodeSoundMain`) restated on the B program `QB20` and the memory read off the pair's words
-- (`memOf layT20 (zOf …)`): `holds_of_wiring` replaces `segs_of_aux` (the bus's `loopir_sound`); Q_link's, Q_sig's and
-- `KS`'s theorems (`qlink_sound`, `qsig_sound_in`, `sigKSin_of_goodK`, `traceDigest_of_goodK`) are used as they are.
import LvmNodeSoundFields
import LvmNodeSoundTr
import LvmQAsmFactsL
import LvmQSigSound
import LvmCertTInst

-- (GOLF2: 11 declarations that `certified` does not use moved verbatim to `LvmNodeSoundTOff`, outside its import closure.)

/-!
# `NodeSound` for the typed backend

The B program at `P20` is `QB20 = Qn (lay cfg20) (sigIn cfg20) qaB (nK cfg20) 0` (`QB20_qn`): Q_link, Q_sig, then
`qaB = phases47 cfg20 >>= qarithB cfg20 tdata20`. The typed instance `TiB = NT20.inst QB20 layT20` is V_S's; a
candidate pair's words are `zT x qm qr = TiB.zOf lay26 (pubX x) qm qr` and its memory `memT x qm qr = memOf layT20 (zT …)`.

* **`holds_memT`**: on a good pair, with the layout check (`StaticFactsT.hlay`) and `ReaddOk`, `QB20`'s rows hold and
  assert on `memT` (`holds_of_wiring`; the word `1` from `THyp.ok`). No interpreter is needed: the gadget theorems
  read any memory where the segments hold (`toProgram_holds`, `parts_of_holds`), so `typed_sound`'s `inb` is not
  needed here (`holds_of_wiring` takes the guard's `S.wf`).
* **`accV_childW_ofT`**: the left child is accepted by the typed `V_S` (`VST`'s replay, `drive_replay`).
* **`nodeSoundT`**: `NodeSound VSB20 vk (GoodT TiB H) childS` from the guard's facts `S`, and on a good node pair:
  `ReaddOk` on `memT` (`hrd`: the mini-bus and QLT's static reads), the input map on `memT` (`hmap`, `hqlt`: the
  layout's input regions through `zOf`, QLT's constants), the position bits (`hpos`) and Q_sig's `BITS` (`hbits`)
  (the typed `BITS` rows), and the B program's Q_arith (`harith`: `qaB`'s segments ⇒ `decideFT … = true`, the typed
  HAR).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig
open Lvm.TypedV (TNat decideFT)

/-! ## The typed `V_S` accepts a reassembled child -/

section Typed

open Lvm.Loop.Build Lvm.M3 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

/-! ## The parts on any memory where the program holds -/

/-- **The three parts' segments** on any memory where the node program's rows hold and assert. -/
theorem parts_of_holdsP {α : Type} {p : Params} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ} {M : Mem}
    (hH : (toProgram nK nE (qprogP p lay I qa)).Holds M) (hA : (toProgram nK nE (qprogP p lay I qa)).Asserts M) :
    Ok (ctxOf (toProgram nK nE (qprogP p lay I qa))) M (qlink p lay) (p0 nK nE) ∧
      Ok (ctxOf (toProgram nK nE (qprogP p lay I qa))) M (qsig I) (p1P lay nK nE p) ∧
      Ok (ctxOf (toProgram nK nE (qprogP p lay I qa))) M qa (p2P lay I nK nE p) := by
  rw [toProgram_holds] at hH
  rw [toProgram_asserts] at hA
  have e : qprogP p lay I qa = (qlink p lay >>= fun _ => (qsig I >>= fun _ => qa)) := rfl
  have hh : SegsHold (ctxOf (toProgram nK nE (qprogP p lay I qa))) M (p0 nK nE) (qprogP p lay I qa (p0 nK nE)).2 :=
    hH
  have ha : SegsAssert M (p0 nK nE) (qprogP p lay I qa (p0 nK nE)).2 := hA
  rw [e, hold_bind, hold_bind] at hh
  rw [e, assert_bind, assert_bind] at ha
  exact ⟨⟨hh.1, ha.1⟩, ⟨hh.2.1, ha.2.1⟩, ⟨hh.2.2, ha.2.2⟩⟩

/-! ## The B program at `P20` -/

/-- **The typed instance at `P20`**: V_S's `NT20` on the B program and its layout (L-W's `Ti20`). -/
noncomputable abbrev TiB : TInst := Lvm.CT.Ti20

/-- **A candidate pair's words** (statement `x`). -/
noncomputable def zT (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : ℕ → FK :=
  TiB.zOf lay26 (pubX x) qm qr

/-- **The memory read off a candidate pair's words.** -/
noncomputable def memT (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Mem :=
  memOf layT20 (zT x qm qr)

theorem lay_TiB : TiB.lay = layT20 := rfl
theorem Q_TiB : TiB.Q = QB20 := rfl

/-- A candidate pair's word `1` holds `1` when the word lies in a `one` region (generic in the instance: the kernel
must not meet `zOf`'s match at the closed `TiB`). -/
theorem zOf_one (Ti : TInst) (h : Ti.src? Ti.lay.one = some .one) (L : Lvm.M3.Lay) (pub : Lvm.Pub)
    (qm : Column L.nuMain) (qr : Column L.nuRec) : Ti.zOf L pub qm qr Ti.lay.one = 1 := by
  unfold TInst.zOf
  rw [h]

/-- The word `1` holds `1` (`THyp.ok`: it lies in a `one` region). -/
theorem zT_one (H : THyp TiB) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) :
    zT x qm qr layT20.one = 1 := by
  have h := zOf_one TiB H.ok.2 lay26 (pubX x) qm qr
  rw [lay_TiB] at h
  exact h

/-- **The good pair's halves**: the wiring relation on its words, the mini-bus, the boundary claims, the incoming
accumulator, the Keccak relations. -/
theorem goodT_wiring {H : THyp TiB} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : WiringRel QB20 layT20 (zT x qm qr) := by
  have h := hG.1.1.1.1
  rw [Q_TiB, lay_TiB] at h
  exact h

/-! ## `NodeSound` -/

/-- **The input map on a memory** (`InMapN`'s fields on any memory). -/
structure InMapMB (B nPub : ℕ) (lay : Layout) (I : SigIn) (M : Mem) (vk : RecursionFast.Digest) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  /-- The stream lanes (Q_link's and Q_sig's stream region; `C_rec`'s stream columns). -/
  stream : ∀ j < 2 ^ lay.m, M.k (lay.sb + j) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j
  /-- Q_sig's gate is on. -/
  flag : M.k I.flag = 1
  /-- `KS`'s `X` message lanes on Q_sig's message cells. -/
  xs : ∀ r < 449, ∀ l < 17, M.k (I.xs + 17 * r + l) = FK.ofBF64 (msgX qm r l)
  /-- `KS`'s output lanes `0 … 3` on Q_sig's digest cells. -/
  ys : ∀ r < 399, ∀ l < 4, M.k (I.ys + 4 * r + l) = FK.ofBF64 (Yq qm (ksSplit P20 + r) l)
  yc : ∀ t ≤ 16, ∀ l < 4, M.k (I.yc + 4 * t + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 430 + t) l)
  yls : ∀ l < 4, M.k (I.yls + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 447) l)
  yns : ∀ l < 4, M.k (I.yns + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 448) l)
  /-- `PUB`: the key, the left statement, the leaf signature. -/
  vk : digAt M.k I.vk = vk
  cL : digAt M.k I.cL = (hdrOf x).cL
  sl : sigAt' M.k I.sl = (hdrOf x).sig
  /-- The trace-digest cells: `KS` row `B − 1`'s output lanes `0 … 3`. -/
  md : ∀ l < 4, M.k (I.md + l) = FK.ofBF64 (Yq qm (B - 1) l)
  /-- `σ'`'s cells: `C_rec`'s column 17. -/
  sg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr))
  /-- Q_sig's child-header cells are the stream's lanes `11 …`. -/
  hd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k)
  /-- The whole `PUB` array from `I.flag`: the header's lanes. -/
  pub : ∀ j < nPub, M.k (I.flag + j) = hdrLane x j

/-- **The input map at `P20`** (`B = spongeBlocks P20`, `PUB` of `pubLanes` lanes; lvm2 E2-FT: `InMapMB` at any stage,
S2GF's `B = 4,295` and `pubLanesX 44`). -/
abbrev InMapM (lay : Layout) (I : SigIn) (M : Mem) (vk : RecursionFast.Digest) (x : List UInt8)
    (qm : Column CMain.nu20) (qr : Column 19) : Prop :=
  InMapMB (spongeBlocks P20) pubLanes lay I M vk x qm qr

/-- The child's stream lanes of a `C_rec` candidate. -/
abbrev wsC (qr : Column 19) : List Word := wsOf (Lvm.X.laneOf (wOfCol qr))

end Typed

end Lvm.NS
