-- New for lvm2 E2-FT (E2F-QH3): linear-time twins of QH1/QH4's Keccak GKR gadgets at `E2` for the native builder
-- (`VF.loopF`: `Build.loop` ranks its template in quadratic time), equal to them (`_eq`), as roll 11's
-- `wireGadgetF`/`VF.gkrGadgetF`.
import LvmE2QKGkr
import LvmVFastQ

/-!
# `tapeGadgetE2F`, `gkrGadgetE2F`

The texts of `Lvm.Q1.tapeGadgetE2` and `Lvm.Q1.gkrGadgetE2` with `VF.loopF` for `loop` (`VF.loopF_eq`). The S2GF
node program is built with these (`LvmE2QAsmFront.frontF`); its statements go through `_eq` to QH4's specs.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- `gkrGadgetE2` with `VF.loopF`. -/
def gkrGadgetE2F (P qs : Nat) (inst out : Nat → C2) (b : Cell) : BM GkrOutE2 :=
  getPtr >>= fun p =>
  VF.loopF [] (tplOf (cstIns (gkS b))) >>= fun _ =>
  let F0 := preTB2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) 0
  VF.loopF [] (tplOf F0.2) >>= fun pre =>
  VF.loopF [] (tplOf (cpIns2 (F0.1.carried.map (S2.gkOut pre)))) >>= fun _ =>
  VF.loopF [4] (layTpl2 P (qs + 61) p.k) >>= fun lay =>
  let qO := gkrQO2 P qs
  let lc := lastC2 P lay
  scGadget2 3 2 qO (F0.1.com.gkCell pre) >>= fun sc1 =>
  scGadget2 2 2 (qO + 86) (lc 0) >>= fun sc2 =>
  scGadget2 3 2 (qO + 142) (scClaim2 sc2 2 3) >>= fun sc3 =>
  let ch1 := (List.range 6).map fun i => scChal2 2 qO i
  let ch2 := (List.range 4).map fun i => scChal2 2 (qO + 86) i
  let ch3 := (List.range 6).map fun i => scChal2 2 (qO + 142) i
  let G := fin1TB2 qO (gkS b) (ch1.map C2.s2) (ch3.map C2.s2) ((List.range 6).map fun i => (lc (44 + P + i)).s2)
    (F0.1.seg.gkOut pre) (scClaim2 sc1 2 5).s2 (F0.1.lanes.map (S2.gkOut pre)) 0
  VF.loopF [] (tplOf G.2) >>= fun f1 =>
  VF.loopF [6] (tplOf (rotIns2 (G.1.ea.map (S2.gkOut f1)) f1.p.k (G.1.z.gkOut f1))) >>= fun rot =>
  VF.loopF [] (tplOf (fin2TB2 (gkS b) (G.1.z.gkOut f1)
    ((List.range 25).map fun l => (lc (19 + P + l)).s2)
    (fun s => (rot.cell2 126 ((64 - s) % 64)).s2) (G.1.e3.map (S2.gkOut f1))
    (lc (18 + P)).s2 ((List.range 16).map fun i => (lc (1 + i)).s2)
    (ch2.map C2.s2) (scClaim2 sc3 2 5).s2 0).2) >>= fun _ =>
  pure ⟨(List.range (P + 4)).map inst ++ ch1, laneC2 (qO + 84),
    ch2 ++ (List.range P).map (fun i => lc (18 + i)) ++ ch3,
    (List.range 64).map fun k => laneC2 (qO + 226 + 2 * k)⟩

theorem gkrGadgetE2F_eq : gkrGadgetE2F = gkrGadgetE2 := by
  funext P qs inst out b
  unfold gkrGadgetE2F gkrGadgetE2
  rw [VF.loopF_eq]

/-- `tapeGadgetE2` with `VF.loopF`. -/
def tapeGadgetE2F (P qs : Nat) (inst out : Nat → C2) (b : Cell) : BM TapeOutE2 :=
  getPtr >>= fun p =>
  VF.loopF [] (tplOf (cstInsT (gkS b))) >>= fun _ =>
  let F0 := preTBT2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) 0
  VF.loopF [] (tplOf F0.2) >>= fun pre =>
  VF.loopF [] (tplOf (cpIns2 (F0.1.carried.map (S2.gkOut pre)))) >>= fun _ =>
  VF.loopF [4] (layTpl2 P (tapeQ2 qs) p.k) >>= fun _ =>
  VF.loopF [3] (layTpl2 P (tapeQ2 qs + 16 * (lay02 P).str2) (p.k + 16 * 16)) >>= fun lay =>
  pure ⟨fun j => lay.cell2 (cbOf2 P + 2 * j) 7⟩

theorem tapeGadgetE2F_eq : tapeGadgetE2F = tapeGadgetE2 := by
  funext P qs inst out b
  unfold tapeGadgetE2F tapeGadgetE2
  rw [VF.loopF_eq]

end Lvm.Q1
