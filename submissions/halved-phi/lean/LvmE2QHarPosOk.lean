-- New for lvm2 E2-FT (E2F-C7): `C_main`'s opening reads its positions from Q_link's position cells at S2GF (roll 11's
-- `posOkMT`: `posOk_of`, `posCellsT`, `out1_entryT` for any configuration, then at `cfgF20`).
import LvmE2QHarIn
import LvmFinPos

/-!
# `PosOk` at S2GF

* **`out1_entryC`**, **`posVal_onC`**: a position class's output, the two position fields' sum (`posVal_on`), for any
  configuration (roll 11's `out1_entryT`/`posVal_onT` at `cfg20`).
* **`posOk_ofG`**: `PosOk` from the position cells' values (`posOk_of` for any parameter set).
* **`posCellsF`**: Q_link's position cells hold `kOf (posL …)` of the child's stream on a good S2GF pair.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har
open LeanVM.Protocol (Column)

section OnC

variable {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v)
include hv

/-- An output of a position class's row, in `Out1` form (`out1_entryT` for any configuration). -/
theorem out1_entryC {k l x : ℕ} {o : OpenInfo} (hk : k < (opens C.p).length)
    (ho : (opens C.p).getD k default = o) (hl : l < QAsm.nLanes o.L.height) (hx : x < nRows o)
    {e : BOut × ℕ × ℕ} (he : e ∈ laneOuts o.L.height l) (hve : e.1.Valid) :
    Out1 v (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e) := by
  subst ho
  obtain ⟨S, hS, -, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ :=
    posSpecs_hit C (fun c ↦ bplOf noData (6 + c)) hk hl hx he
  exact out1_ofC hv (posSpecs_memC C hS) hrd hy hjo hwc hoc hout hve

/-- `posVal_on` from the position classes' outputs (`posVal_onT` for any configuration). -/
theorem posVal_onC (hS : StreamOk C.p) (hQ : QOk C.p (lay C)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, v ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    v ((lay C).fl + posIdx C.p k j) + v ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8)
        (j % 8 * ((opens C.p).getD k default).L.height) ((opens C.p).getD k default).L.height) :=
  posVal_on C (out1_entryC hv) hS hQ hs hk hH hj

end OnC

/-- **`PosOk` from the position cells' values** (`Lvm.Fin.posOk_of` for any parameter set `p = Cq.p`). -/
theorem posOk_ofG (p : Params) (Cq : QCfg) (hp : Cq.p = p) (C : SCfg) (k0 : ℕ)
    (hpb : ∀ i, C.pb i = posBase Cq (k0 + i)) {Ls : List Level} {V : ℕ}
    (hPL : Lvm.Fin.PosLanes p C.g C.ood Ls V k0) {M : Mem} {ws : List Word} (hS : StreamOk p) (hL : LaneLink p ws)
    (hQ : QOk p (lay Cq))
    (hcell : ∀ k < (opens p).length, ((opens p).getD k default).L.height ≤ 64 →
      ∀ j < ((opens p).getD k default).L.t, M.k (nK Cq + posIdx p k j) =
        kOf (posL p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height)
          ((opens p).getD k default).L.height)) :
    PosOk C M (traceBytesB (decode p ws)) 0 Ls V := by
  intro i hi j hj
  obtain ⟨hk, hLeq, hH, hP⟩ := hPL i hi
  rw [traceBytesB_decode hS hL, hpb, Nat.zero_add]
  have hjt : j < ((opens p).getD (k0 + i) default).L.t := by rw [hLeq]; exact hj
  have ho : (opens p).getD (k0 + i) default ∈ opens p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hjt
  have hin := lanes_in hS h1 hlt
  have hab := ansLane_bound hS hL.size hlt
  have e1 : posBase Cq (k0 + i) + j = nK Cq + posIdx p (k0 + i) j := by
    simp only [posBase, posIdx, hp]; (clear * -; omega)
  rw [e1, hcell _ hk (by rw [hLeq]; exact hH) j hjt]
  have hx : j / 8 < nAns ((opens p).getD (k0 + i) default) := by unfold nAns; (clear * - hjt e1; omega)
  have hb : j % 8 * (Ls.getD i default).height + (Ls.getD i default).height ≤ 192 := by rw [← hLeq]; exact h192
  have hlen : 8 * ansLane p (((opens p).getD (k0 + i) default).pe + j / 8) + 24 ≤ hashedLen p := by
    simp only [ansLane, if_neg (show ((opens p).getD (k0 + i) default).pe + j / 8 ≠ 0 by (clear * - h1; omega))]
    (clear * - hin; omega)
  rw [Lvm.Har.qsAt_posL p ws _ _ _ j hj (hP _ hx) hb hlen (by (clear * - hab; omega)), hLeq]
  rfl

section Pair

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- **Q_link's position cells hold `kOf (posL …)` of the child's stream** on a good S2GF pair (`posCellsT`). -/
theorem posCellsF (S : NodeGF frzF20 QF20 layF20 NTF20) (H : THypX TiF20) {vk c : RecursionFast.Digest}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : E2V.GoodTF TiF20 H x qm qr ∧ SBlk qm qr) :
    ∀ k < (opens P20F).length, ((opens P20F).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20F).getD k default).L.t,
      (memF TiF20 x qm qr).k (nK cfgF20 + posIdx P20F k j) =
        kOf (posL P20F (wsC qr) (((opens P20F).getD k default).pe + j / 8)
          (j % 8 * ((opens P20F).getD k default).L.height) ((opens P20F).getD k default).L.height) := by
  intro k hk hH j hj
  obtain ⟨hH', hA⟩ := hholdsF S H hG
  have hH'' : QF20.Holds (memF TiF20 x qm qr) := hH'
  have hA' : QF20.Asserts (memF TiF20 x qm qr) := hA
  rw [QF20_eq] at hH'' hA'
  have P := parts_of_holdsP hH'' hA'
  have mp := hmapF S H hok hb hG
  have hp : cfgF20.p = P20F := rfl
  have hk' : k < (opens cfgF20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgF20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgF20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := posVal_onC (C := cfgF20) (outsOnF S H hG.1) (by rw [hp]; exact streamOk_P20F)
    (by rw [hp]; exact hQF20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := qlink_pos (pt := p0 (nK cfgF20) 0) hQF20 P.1.1 hk hj
  exact hq.trans hv

end Pair

end Lvm.E2Q
