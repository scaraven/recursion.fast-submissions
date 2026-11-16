-- New for lvm2 E2-FT (E2F-QH6): the facts S2GF's typed HAR (`harithF20`, E2F-C) reads besides the gadgets' phase
-- lemmas: the child's stream on the node memory (`Streamed`), `Σ'`'s size, the incoming accumulator from `PUB` at
-- `acc_in` of 44 coordinates, and V's proof-of-work checks on the ground answers from the PoW blocks (`powBlk_ok`).
import LvmE2QHarGen
import LvmE2QNodeG
import LvmE2QWPhase
import LvmQAsmHarTails
import LvmQTypedHarS

/-!
# The HAR's facts at S2GF

* **`sigCF qr`**: the child's trace bytes `Σ'` at S2GF; **`sigCF_size`**: `|Σ'| = hashedLen P20F`.
* **`streamedF`**: the node memory's stream cells are `Σ'`'s lanes (`Streamed … (streamLanes P20F)`).
* **`accCA n M pb`**: `acc_in` read off its `PUB` cells at `n` coordinates (`accC` at `accVars`, `accCA_accVars`);
  **`accCA_pubXF`**: at `accVF = 44` it is the statement's `(pubXF x).accIn`.
* **`powOk_of_blks`**: on a layout built with `specQF … pw`, where the coordinate-split relation holds, every
  answer `(q, g)` of `pw` whose lanes are streamed has V's check `powOKR g (feAt Σ (8q))`; so `PowOkV (feAt Σ) L` for
  every challenge list `L ⊆ pw`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.NS Lvm.Typed Lvm.QTyped
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-! ## `Σ'` and the stream -/

/-- **The child's trace bytes `Σ'`** of a `C_rec` candidate at S2GF. -/
abbrev sigCF (qr : Column 19) : ByteArray := traceBytesB (decode P20F (wsC qr))

/-- `|Σ'| = hashedLen P20F` on a linked stream. -/
theorem sigCF_size {qr : Column 19} (hL : LaneLink P20F (wsC qr)) : (sigCF qr).size = hashedLen P20F := by
  rw [sigCF, traceBytesB_decode streamOk_P20F hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams `Σ'`** (`streamed_child` at `cfgF20`, `T = streamLanes P20F = 73,001`). -/
theorem streamedF {M : Mem} {qr : Column 19}
    (hst : ∀ j < 2 ^ (lay cfgF20).m, M.k ((lay cfgF20).sb + j) = laneK (wsC qr) j) (hL : LaneLink P20F (wsC qr)) :
    Lvm.Q1.Streamed M (sigCF qr) (streamLanes P20F) := by
  have hh : hashedLen P20F = 584008 := spongeBlocks_P20F.2
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  have h := Lvm.Har.streamed_child cfgF20 streamOk_P20F hL hst (T := streamLanes P20F)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgF20.p = P20F from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)
  rwa [show cfgF20.p = P20F from rfl] at h

/-! ## `acc_in` from `PUB` at 44 coordinates -/

/-- **`acc_in` read off its `PUB` cells** at `n` coordinates (three lanes per scalar from `pb + 615`). -/
def accCA (n : ℕ) (M : Mem) (pb : ℕ) : Acc :=
  ⟨(List.range n).map fun i => ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1), M.k (pb + 615 + 3 * i + 2)⟩,
    ⟨M.k (pb + 615 + 3 * n), M.k (pb + 615 + 3 * n + 1), M.k (pb + 615 + 3 * n + 2)⟩⟩

theorem accCA_accVars (M : Mem) (pb : ℕ) : accCA accVars M pb = Lvm.QAcc.accC M pb := rfl

/-- `PUB` cell `pb + 615 + 3i + t` is the header's word at stream byte `headerAt (offAcc + 24 i) + 8 t`. -/
theorem pub_acc_lane {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanesX accVF, M.k (pb + j) = hdrLane x j) {i t : ℕ} (hi : i ≤ accVF) (ht : t < 3) :
    M.k (pb + 615 + 3 * i + t) = kAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i) + 8 * t) := by
  have hj : 615 + 3 * i + t < pubLanesX accVF := by
    unfold pubLanesX; rw [show accVF = 44 from rfl] at hi ⊢; omega
  rw [show pb + 615 + 3 * i + t = pb + (615 + 3 * i + t) by omega, hpub _ hj, hdrLane_eq_kAt]
  congr 1
  simp only [headerAt, offAcc, eBytes, sigBytes]
  omega

/-- **`acc_in` from `PUB` at S2GF** is the statement's (`accVF = 44` coordinates, `pubLanesX 44 = 750` lanes). -/
theorem accCA_pubXF {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanesX accVF, M.k (pb + j) = hdrLane x j) : accCA accVF M pb = (pubXF x).accIn := by
  have e : (pubXF x).accIn = ⟨(List.range accVF).map fun i =>
      feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i)),
      feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * accVF))⟩ := rfl
  rw [e]
  unfold accCA
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' : i ≤ accVF := Nat.le_of_lt (List.mem_range.mp hi)
    have h0 := pub_acc_lane hpub hi' (t := 0) (by omega)
    have h1 := pub_acc_lane hpub hi' (t := 1) (by omega)
    have h2 := pub_acc_lane hpub hi' (t := 2) (by omega)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, h1, h2]
    rfl
  · have h0 := pub_acc_lane hpub (le_refl accVF) (t := 0) (by omega)
    have h1 := pub_acc_lane hpub (le_refl accVF) (t := 1) (by omega)
    have h2 := pub_acc_lane hpub (le_refl accVF) (t := 2) (by omega)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, h1, h2]
    rfl

-- `powRecRows_mem`, `boolRuns_cover`, `auxRow_mem`, `powOk_of_blks` are in `LvmE2QHarGen` (moved, lvm2 U-TAPE).

/-- **V's proof-of-work checks at S2GF** on a good pair's memory (`powOk_of_blks` at `cfgF20`, the pair's words). -/
theorem powOkF {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TypedV.TNat} (S : NodeGF F Q tl N)
    (H : THypX (N.inst Q tl)) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)}
    (hl : tl = (mkLayD Q (specQF cfgF20 Q pw) d).1) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memF (N.inst Q tl) x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ pw)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blks cfgF20 hl S.st.hlay (one_zTX H pubXF) hG.1.1.1.1 hS hL hpw

/-- `PUB`'s first `pubLanes` cells from S2GF's input map (`pubLanesX 44 = 750 ≥ 747`; roll 11's `PUB` glue,
`Lvm.Har.vk_cellsT`, reads them). -/
theorem pub747F {M : Mem} {vk : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hin : InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) M vk x qm qr) :
    ∀ j < pubLanes, M.k ((sigIn cfgF20).flag + j) = hdrLane x j :=
  fun j hj ↦ hin.pub j (lt_of_lt_of_le hj (by decide))

end Lvm.E2Q
