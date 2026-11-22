-- New for lvm2 σ_LEAF (SLF-C, stage S2GS, lead decisions D2/D8): the S2GS node program. The front's wire kernel
-- takes a list of `cont` intervals (the node's own key leaf's), the typed A23 gadget reads `acc_in` after a header
-- without `σ_leaf`, and Q_sig is `qsigSC` (no `σ_leaf'` check; the node's own leaf signature walked at the constant
-- digits of `traceDigest []`, `LvmQSigLeaf`).
import LvmE2QTypedL

/-!
# The S2GS node program (`QS`)

* **`kernS`**, **`wireGS`**: `kernU`, `wireGU` with the `cont` intervals `[1, B − 1]` and `[K + 1, K + 31]`, `K ∈ Ks`.
* **`ksKs p`**: Q_sig's key-leaf start `ksSplit + 399`, and with `leafOut` the leaf walk's `ksSplit − 48`.
* **`hdrFixL`**, **`pubLanesS`**, **`qaccGS`**, **`typedGS`**, **`qarithS`**: the header before `acc_in` has 18 lanes with
  `leafOut` (615 before); `PUB` has `pubLanesS` lanes.
* **`frontS`**, **`qaS`**, **`QS C T`**: `frontU`/`qaL`/`QL` with these, and `qsigSC (sigIn C) (sigInLC C)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build
/-- **The kernels at S2GS**: `kernU` with the cont intervals `[1, B − 1]` and `[K + 1, K + 31]` for every `K ∈ Ks`. -/
def kernS (z one : C2) (rho mu σ mb lt : List C2) (B : Nat) (Ks : List Nat) : BM KernU :=
  g2Ms z one rho mu σ mb lt >>= fun ms =>
  g2One (rho.getD 15 default) >>= fun r16 =>
  g2Mul ms r16 z >>= fun kch =>
  g2Eq0 z (rho.getD 15 default) ((rho.drop 8).take 7) >>= fun cTop =>
  g2EqTab z [one] (σ.take 5) >>= fun e4 =>
  mapB (fun d => g2Mul (e4.getD d default) (mu.getD ((d + 1) % 32) default) z) (List.range 32) >>= fun A =>
  mapB (fun k => msCoef z (σ.getD (5 + k) default) (rho.getD k default)) (List.range 8) >>= fun cs =>
  msConstU z one cs A (B - 1) >>= fun m1 =>
  mapB (fun K => msConstU z one cs A (K + 31) >>= fun a => msConstU z one cs A K >>= fun b => pure [a, b]) Ks >>= fun ms2 =>
  g2Sum m1 ms2.flatten >>= fun ms3 =>
  g2Mul ms3 cTop z >>= fun kks =>
  g2Dot z ((List.range 32).map fun d => (e4.getD d default, mu.getD d default)) >>= fun dg =>
  mapB (fun k => g2Add (rho.getD k default) (σ.getD (5 + k) default) >>= g2One) (List.range 8) >>= fun fs =>
  g2Prod z dg fs >>= fun ik0 =>
  g2Mul ik0 cTop z >>= fun iks =>
  g2Eq0 z one ((σ.drop 13).take 7) >>= fun e' =>
  pure ⟨kch, kks, iks, e'⟩

/-- `wireGU` with `kernS`. -/
def wireGS (P w qw : Nat) (cv : Nat → C2) (mb sb : List Cell) (B : Nat) (Ks : List Nat) (zk gate : Cell) : BM WireOutU :=
  let L := wireLanesU w qw
  let mb2 := mb.map fun b => kC2 b zk
  let sb2 := sb.map fun b => kC2 b zk
  let mu := (List.range 32).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (34 + i)
  let Bv := (List.range 25).map fun l => cv (35 + P + l)
  preWU P cv mb2 sb2 >>= fun G =>
  sc2 w qw G.target >>= fun sc =>
  let gD := ld2 L.g3
  let gY := ld2 (L.g3 + 2)
  let gM := ld2 (L.g3 + 4)
  kernS G.z G.one rho mu sc.1 mb2 G.lt B Ks >>= fun k =>
  g2Mul k.kks gY G.z >>= fun t1 => g2Mul k.iks gM t1 >>= fun t2 =>
  g2Mul k.e' t2 sc.2 >>= fun t3 => g2Mul k.kch gD t3 >>= fun fin =>
  g2Assert fin gate >>= fun _ =>
  sc2 2 L.slotD gD >>= fun sd =>
  slotW2 L.slicesD G.om sd.1 G.z G.one sd.2 gate >>= fun _ =>
  sc2 5 L.slotY gY >>= fun sy =>
  slotWU L.slicesY 25 Bv G.eZ sy.1 G.z G.one sy.2 gate >>= fun _ =>
  sc2 5 L.slotM gM >>= fun sm =>
  slotWU L.slicesM 17 Bv G.eZ sm.1 G.z G.one sm.2 gate >>= fun _ =>
  pure ⟨sc.1, sd.1, sy.1, sm.1, G.z, G.one⟩
end Lvm.Q2

namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped Lvm.Q2

/-- The header lanes before `acc_in` (615; 18 with `leafOut`). -/
def hdrFixL (p : Params) : Nat := if p.leafOut then 18 else 615

/-- The child's `PUB` lanes (`pubLanesTC` with `leafOut`). -/
def pubLanesS (p : Params) : Nat := hdrFixL p + 2 * (p.accV + 1)

/-- The cont intervals' starts past the trace: `Q_sig`'s key leaf, then (with `leafOut`) the leaf walk's. -/
def ksKs (p : Params) : List Nat :=
  [ksSplit p + 399] ++ (if p.leafOut then [ksSplit p - (Lvm.QSig.nStepRowsC + 48) + Lvm.QSig.nStepRowsC] else [])

/-- `qaccGT` at a header of `hf` lanes before `acc_in`. -/
def qaccGS (hf : Nat) (z2 o2 : C2) (pb : Nat) (L : Nat → Nat) (rx ry vs : List C2) : BM Unit := do
  let g := kc pb
  let kap := (List.range 4).map fun j => ld2 (L (iKap j))
  let h := ld2s (L iH) (tVarsT + 1)
  let t := ld2 (L iT)
  let zz := ld2 (L iZ)
  let ain := (List.range (tVarsT + 1)).map fun j => ld2 (11 + hf + 2 * j)
  assertEq2 (h.getD 0 z2) (ain.getD tVarsT z2) g
  let sh ← g2Sum z2 h
  let y ← eqDot2 z2 o2 kap 2 vs
  assertEq2 sh y g
  assertEq2 zz z2 g
  let bc := kap ++ rx ++ ry
  let pts ← mapB (fun i => do
    let x := ain.getD i z2
    let d ← g2Add x (bc.getD i z2)
    g2Mul t d x) (List.range tVarsT)
  let hv ← horner2 t h.reverse z2
  let pc := (List.range (tVarsT + 1)).map fun j => ld2 (pb + hf + 2 * j)
  let _ ← mapB (fun i => assertEq2 (pts.getD i z2) (pc.getD i z2) g) (List.range tVarsT)
  assertEq2 hv (pc.getD tVarsT z2) g

/-- `typedGL` with `qaccGS`. -/
def typedGS (T : TData) (p : Params) (pb n : Nat) (z o zk ok : Cell) : BM (TypedCT × List CClaim) := do
  let g := kc pb
  let L := busL p
  let z2 : C2 := ⟨zk, zk⟩
  let o2 : C2 := ⟨ok, zk⟩
  let zr ← zeroGT z2 g L
  let w ← wireGT z2 o2 g T pb n L zr.2
  let r ← relayGT z2 o2 g T L w.1 (w.2.2.getD 1 z2)
  qaccGS (hdrFixL p) z2 o2 pb L zr.1 w.1 w.2.1
  let bc ← busGD T.mbD z o g (mbPT p)
  let cs ← mbLinG z o T bc
  pure (⟨zr.1, w.1, zr.2, w.2.1, w.2.2, r.1, r.2, bc, []⟩, cs)

/-- `qarithL` with `typedGS`. -/
def qarithS (C : QCfg) (T : TData) (pin : CClaim) (o : FrontF) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let ok ← const .K 1 (kc 0)
  let t ← typedGS T p (pbB C) (pubLanesS p) z one zk ok
  let tc ← typedClaimsGL z ⟨zk, zk⟩ ⟨ok, zk⟩ T (layout0 p).s t.1 t.2
  let a ← addK (o.mb.getD 18 default) 1
  let b ← addK (o.mb.getD 19 default) 1
  let sK ← mulAdd .K a b zk
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨ok, zk⟩, true⟩
  Lvm.Q2.openGF (cfgMainF p (posBase C) (pwBase C)) (p.logN == 20 && p.nuMain == CMain.nu20) F pin (tc ++ o.cs)
    o.mb sK g

/-- **The `E2` front at S2GS**: `frontU` with `wireGS` (the leaf walk's cont interval). -/
def frontS (C : QCfg) : BM FrontF := do
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
  let tp ← Lvm.Q1.tapeGadgetE2F (p.logN - 5) (pl .tape (2 * p.logN + 5)) (fun i => ri.getD i default)
    (fun l => v.getD l default) g
  -- T3, T4: the wire and the three row switches
  let mb ← borrowK ((sigIn C).bn + 2) onek.n p.logN
  let qw := pl .wire 0
  let wo ← Lvm.Q2.wireGS (p.logN - 5) p.logN qw tp.cv mb (sbCells C) (spongeBlocks p) (ksKs p) zk g
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


/-- **What follows Q_link and Q_sig at S2GS**. -/
def qaS (C : QCfg) (T : TData) : BM Unit := do
  let pin ← pinF C.p
  let o ← frontS C
  qarithS C T pin o

/-- **The DEV S2GS node program** on the static data `T`. -/
def QS (C : QCfg) (T : TData) : Program :=
  VF.toProgramF (nK C) 0 (do qlink C.p (lay C); let _ ← qsigSC (sigIn C) (sigInLC C); qaS C T)

end Lvm.E2Q
