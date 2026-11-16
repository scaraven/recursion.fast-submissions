-- New for lvm2 U-TAPE (UT-C): the node program at stage S2GU (`QU`): S2GT's (`QG`) with the `E2` front of the merged
-- tape (`frontU`: T1 in R-BP2's B1 order, the 21-variable tape GKR, the S2GU wire with three slot reductions and row
-- switches); the `KS` GKR, its row switch and the `KS` link are gone.
import LvmE2QAsmT
import LvmE2QWU

/-!
# The S2GU node program

**Stream positions** (`schedule p` at stage `3`, `LvmSchedule.phasesS2GU`; item `j` of a phase is `pl ph j`):

* **tape** (`CHtape`): item 0 the separator; items `1 + 2i`, `2 + 2i` the nonce and answer of `r_i`, `i < logN`;
  item `2 logN + 1` the 50 scalars (`a_l` at lane `+ 2l`, `b_l` at `+ 50 + 2l`); items `2 logN + 2`, `+ 3` the nonce
  and answer of `r_logN`; the five lane challenges from item `2 logN + 5` (the tape gadget's `qs`).
* **wire** (`CHwire`): item 0 the first wiring round's message (`wireLanesU` gives the rest).

**T1** (`tOneU`): `e = Π_{k=13}^{19}(1 + r_k)`, `v_l = a_l + r₂₀·a_l + f·b_l + (r₂₀ + f)·z*_l` with `f = r₂₀·e`
(`(1 − r₂₀)·a_l + r₂₀·(e·b_l + (1 − e)·z*_l)` in characteristic 2).

**Claims** (`frontU`'s list, V's order for S2GU, lead decision D-ORD): `D`'s four word claims (halves, point
`r_{<20} ‖ sel(l)`); the `Y` block's 25 word claims (halves, `Y` lane `l` at point `r_{<13}`); `D`'s row claim, the `Y`
block's row claim (`σ' ‖ τ_Y`), the stream block's row claim (`σ' ‖ 0 ‖ τ_M`); the four boundary claims
`D̃_l(bits(m)) = h_l`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped Lvm.Typed

/-- The free `K` cells `t_j` of the three row switches (`D`, `Y`, `M`; 128 each), after the lane classes' spares. -/
def tBu (C : QCfg) (i : Nat) : Nat := spEnd C + 128 * i

/-- **T1's output scalars** `v_l` (`l < 25`) from `r` (`r_0 … r_{logN−1}`), `r₂₀` and the 50 scalars `a`, `b`. -/
def tOneU (F : Lvm.Q2.FCtx) (r : List C2) (r20 : C2) (a b : List C2) : BM (List C2) :=
  Lvm.Q2.g2Eq0 F.z2 F.o2 ((r.drop 13).take 7) >>= fun e =>
  Lvm.Q2.g2Mul r20 e F.z2 >>= fun f =>
  Lvm.Q2.g2Add r20 f >>= fun w =>
  Lvm.Q2.mapB (fun l =>
    Lvm.Q2.g2Mul r20 (a.getD l default) (a.getD l default) >>= fun x1 =>
    Lvm.Q2.g2Mul f (b.getD l default) x1 >>= fun x2 =>
    Lvm.Q2.g2Lin (zStarE2 l).re 0 x2 w) (List.range 25)

/-- **The `E2` front at S2GU**: the gadgets at the schedule's lanes, then the front's claims in V's order. -/
def frontU (C : QCfg) : BM FrontF := do
  let p := C.p
  let A := (itemLanes p).toArray
  let pl (ph : Phase) (j : Nat) : Nat := A.getD (phaseItem0 p ph + j) 0
  let g := kc (pbB C)
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let onek ← const .K 1 (kc 0)
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨onek, zk⟩, false⟩
  -- T1
  let r : List C2 := (List.range p.logN).map fun i => Lvm.Q1.laneC2 (pl .tape (2 + 2 * i))
  let tOut := pl .tape (2 * p.logN + 1)
  let a : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 2 * l)
  let b : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 50 + 2 * l)
  let r20 := Lvm.Q1.laneC2 (pl .tape (2 * p.logN + 3))
  let v ← tOneU F r r20 a b
  -- T2: the tape GKR on `(r ‖ r₂₀, v)`
  let ri := r ++ [r20]
  let tp ← Lvm.Q1.tapeGadgetE2F (p.logN - 4) (pl .tape (2 * p.logN + 5)) (fun i => ri.getD i default)
    (fun l => v.getD l default) g
  -- T3, T4: the wire and the three row switches
  let mb ← borrowK ((sigIn C).bn + 2) onek.n p.logN
  let qw := pl .wire 0
  let wo ← Lvm.Q2.wireGU (p.logN - 4) p.logN qw tp.cv mb (sbCells C) (spongeBlocks p) (ksSplit p + 399) zk g
  let WL := Lvm.Q2.wireLanesU p.logN qw
  let rD ← Lvm.Q2.rowG WL.ringD (tBu C 0) z.n one.n
  let nuD ← Lvm.Q2.rowNuGL rD z.n one.n
  let rY ← Lvm.Q2.rowG WL.ringY (tBu C 1) z.n one.n
  let nuY ← Lvm.Q2.rowNuGL rY z.n one.n
  let rM ← Lvm.Q2.rowG WL.ringM (tBu C 2) z.n one.n
  let nuM ← Lvm.Q2.rowNuGL rM z.n one.n
  -- the boundary claims' point: `n' − 1`'s bits as `E` cells
  let mbE ← Lvm.Q2.mapB (fun b => add b z) mb
  let L := layout0 p
  let blkD := dBlock p
  let sg' := wo.sigma.take p.ksLog
  let dw : List Lvm.Q2.FClaim :=
    (List.range dLanes).flatMap fun l =>
      let zl := r ++ selC2 F l 2
      let vl := a.getD l default
      [.dhalf false zl vl.re, .dhalf true zl vl.im]
  let yw : List Lvm.Q2.FClaim := (List.range 25).flatMap fun l =>
    halves [(F.o2, (⟨p.ksLog, L.ks + l * 2 ^ p.ksLog⟩ : Placement), r.take p.ksLog)] (b.getD l default)
  let rows : List Lvm.Q2.FClaim :=
    [.drow (wo.sigma ++ wo.tauD ++ selC2 F (dSel p) (dSelBits p)) nuD rD.target,
     .row ⟨p.ksLog + 5, L.ks⟩ (sg' ++ wo.tauY) nuY rY.target,
     .row ⟨p.recRowsLog + 5, L.s⟩ (sg' ++ [F.z2] ++ wo.tauM) nuM rM.target]
  let hs : List Lvm.Q2.FClaim :=
    (List.range 4).map fun l => .e3 ⟨.main, .point blkD (mbE ++ Lvm.Har.selC z.n one.n l 2), kc (hLane l)⟩
  pure ⟨dw ++ yw ++ rows ++ hs, mb⟩

/-- **What follows Q_link and Q_sig at S2GU**: the root pin, the `E2` front `frontU`, S2GT's Q_arith (`qarithG`). -/
def qaU (C : QCfg) (T : TData) : BM Unit := do
  let pin ← pinF C.p
  let o ← frontU C
  qarithG C T pin o

/-- **The S2GU node program** on the static data `T`. -/
def QU (C : QCfg) (T : TData) : Program := VF.toProgramF (nK C) 0 (do qlink C.p (lay C); let _ ← qsig (sigIn C); qaU C T)

/-- **The front's ground challenges at S2GU** `(answer lane, g)`: `r_{<logN}`, `r_logN`, the tape GKR, the wire. -/
def powFrontU (p : Params) : List (Nat × Nat) :=
  let A := (itemLanes p).toArray
  let pl (ph : Phase) (j : Nat) : Nat := A.getD (phaseItem0 p ph + j) 0
  Lvm.Q2.chalsG (pl .tape 2) Lvm.E2V.gC1 p.logN ++ [(pl .tape (2 * p.logN + 3), Lvm.E2V.gC1)] ++
    Lvm.Q1.tapeChals2 (p.logN - 4) (pl .tape (2 * p.logN + 5)) ++ Lvm.Q2.wireChalsU p.logN (pl .wire 0)

/-- **The ground challenges of the S2GU node program**: the front's and the typed phases'. -/
def powU (p : Params) : List (Nat × Nat) := powFrontU p ++ typedChalsT p

/-- **The S2GU layout specification**: `specQ`'s, the three row switches' bit blocks (looped, `rowAuxL`) on the
free cells `tBu C i` and the slice lanes, the PoW bits (`powBlksL`). -/
def specQU (C : QCfg) (Q : Program) (pw : List (Nat × Nat)) : LSpec :=
  let S := specQ C Q
  let n := S.auxWords.length
  let WL := Lvm.Q2.wireLanesU C.p.logN (phaseLane C.p .wire 0)
  { S with
    auxWords := S.auxWords ++ [Lvm.Q2.rowAuxWords, Lvm.Q2.rowAuxWords, Lvm.Q2.rowAuxWords, Lvm.Q2.powWords pw]
    auxOf := fun bw => S.auxOf bw ++ (Lvm.Q2.rowAuxL (bw n) (tBu C 0) WL.slicesD ++
      Lvm.Q2.rowAuxL (bw (n + 1)) (tBu C 1) WL.slicesY ++ Lvm.Q2.rowAuxL (bw (n + 2)) (tBu C 2) WL.slicesM) ++
      powBlksL (bw (n + 3)) pw }

end Lvm.E2Q
