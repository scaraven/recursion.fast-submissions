-- New for lvm2 E2-FT (E2F-QH3): the `E2` front of the S2GF node program (phases CHtape, CHwire, KS, KSlink with
-- their row switches), assembled from QH1's Keccak GKR gadgets and QH2's wire/link/row-switch gadgets at the lanes of
-- `LvmE2QPlan.itemLanes`.
import LvmE2QAsm
import LvmE2QAsmFast
import LvmE2QW
import LvmE2QL
import LvmQRingRow
import LvmE2QPinOpen

/-!
# The `E2` front at S2GF (`frontF`)

The stream positions are the items of `schedule P20F` (`phaseLane p ph j`: item `j` of phase `ph`):

* **tape** (`CHtape`): item 0 the separator; items `1 + 2i`, `2 + 2i` the nonce and the answer of `r_i` (`i < logN`);
  item `2 logN + 1` the 25 output scalars; the five lane challenges from item `2 logN + 3` (QH1's `qs`).
* **wire** (`CHwire`): item 0 the first wiring round's message (QH2's `qw`); the row switch's seven `E3` samples
  are the phase's last seven items.
* **`KS`**: items `2i`, `2i + 1` the nonce and answer of the instance coordinate `i < ksLog`; item `2 ksLog` the 25
  output scalars; the segment challenge's answer at item `2 ksLog + 2` (QH1's `qs`); the row switch's samples the
  phase's last seven items.
* **`KS` link**: the first `kchal` answer at item 1.
* The root pin: the `ν` answers from item 1 of `commit`, the value at item `ν + 1`.

`borrowK`: `n' − 1`'s bits as `K` cells (QH2's `wireG2` takes them so).

The front's claims are built in `V_S`'s order (`LvmDecideE2.frontClaimsD`) as QH2's opening forms (`FClaim`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.QSig Lvm.QTyped

/-- **The bits `0 … n − 1` of `N − 1` as `K` cells** (`borrow` with the `K` cell `o` holding `1`). -/
def borrowK (nb o n : Nat) : BM (List Cell) :=
  match n with
  | 0 => pure []
  | k + 1 => do
    let d0 ← add (kc nb) (kc o)
    let ds ← borrowGo nb 1 k d0
    pure (d0 :: ds)

/-- The global index of the first item of the phase after `ph` (the end of `ph`). -/
def phaseEnd (p : Params) : Phase → Nat
  | .tape => phaseItem0 p .wire
  | .wire => phaseItem0 p .ks
  | .ks => phaseItem0 p .ksLink
  | .ksLink => phaseItem0 p .openMain
  | ph => phaseItem0 p ph

/-- The first row-switch answer lane of phase `ph` (its last seven items). -/
def ringLane (p : Params) (ph : Phase) : Nat := laneOf p (phaseEnd p ph - 7)

/-- The free `K` cells `t_j` of the two row switches (128 each), after the lane classes' spares. -/
def tBw (C : QCfg) : Nat := spEnd C
def tBk (C : QCfg) : Nat := spEnd C + 128

/-- **The root pin** at `p` (QH2's `pinG` at the commit phase's lanes). -/
def pinF (p : Params) : BM CClaim := Lvm.Q2.pinG p.nuMain (phaseLane p .commit 1) (phaseLane p .commit (p.nuMain + 1))

/-- `selPtF sel len` as `E2` constant cells (`F.z2`, `F.o2`), lowest bit first. -/
def selC2 (F : Lvm.Q2.FCtx) (sel len : Nat) : List C2 :=
  (List.range len).map fun b => if (sel >>> b) % 2 = 1 then F.o2 else F.z2

/-- The two halves (re, then im) of an `E2` claim with the given parts and value. -/
def halves (parts : List (C2 × Placement × List C2)) (v : C2) : List Lvm.Q2.FClaim :=
  [.half false parts v.re, .half true parts v.im]

/-- `KS`'s `Y` lane `l` at `E2` (`ksYPartD` on cells). -/
def ksYPart2 (p : Params) (F : Lvm.Q2.FCtx) (l : Nat) (pt : List C2) : Placement × List C2 :=
  if l < 14 then (⟨p.ksLog + slotLog, (layout0 p).ks⟩, pt ++ selC2 F (50 + l) slotLog)
  else (⟨p.ksLog, (layout0 p).ksY2 + (l - 14) * 2 ^ p.ksLog⟩, pt)

/-- **The `E2` front**: the gadgets at the schedule's lanes, then the front's claims in `V_S`'s order
(`frontClaimsD`): the tape's four `D` word claims (halves), its row claim, the four boundary claims `D̃_l(bits(m)) =
h_l`; `KS`'s output word claim (halves) and row claim; the 25 output lanes (halves); the link's `Y`, `in` (halves),
`X_re`, `M` (halves), `X_im`. -/
def frontF (C : QCfg) : BM FrontF := do
  let p := C.p
  -- the lanes, evaluated once (`phaseLane` walks the schedule)
  let A := (itemLanes p).toArray
  let pl (ph : Phase) (j : Nat) : Nat := A.getD (phaseItem0 p ph + j) 0
  let tI := phaseItem0 p .tape
  let kI := phaseItem0 p .ks
  let g := kc (pbB C)
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let onek ← const .K 1 (kc 0)
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨onek, zk⟩, false⟩
  -- tape
  let r : List C2 := (List.range p.logN).map fun i => Lvm.Q1.laneC2 (A.getD (tI + 2 + 2 * i) 0)
  let tOut := pl .tape (2 * p.logN + 1)
  let v : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 2 * l)
  let tp ← Lvm.Q1.tapeGadgetE2F (p.logN - 5) (pl .tape (2 * p.logN + 3)) (fun i => r.getD i default)
    (fun l => v.getD l default) g
  -- wire, and its row switch
  let mb ← borrowK ((sigIn C).bn + 2) onek.n p.logN
  let wo ← Lvm.Q2.wireG2 (p.logN - 5) (pl .wire 0) tp.cv mb (sbCells C) zk g
  let rw ← Lvm.Q2.rowG (A.getD (phaseEnd p .wire - 7) 0) (tBw C) z.n one.n
  let nuW ← Lvm.Q2.rowNuGL rw z.n one.n
  -- KS, and its row switch
  let ki : List C2 := (List.range p.ksLog).map fun i => Lvm.Q1.laneC2 (A.getD (kI + 2 * i + 1) 0)
  let kOut := pl .ks (2 * p.ksLog)
  let kv : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (kOut + 2 * l)
  let ko ← Lvm.Q1.gkrGadgetE2F (p.ksLog - 4) (pl .ks (2 * p.ksLog + 2)) (fun i => ki.getD i default)
    (fun l => kv.getD l default) g
  let rk ← Lvm.Q2.rowG (A.getD (phaseEnd p .ks - 7) 0) (tBk C) z.n one.n
  let nuK ← Lvm.Q2.rowNuGL rk z.n one.n
  -- the KS link
  let kl ← Lvm.Q2.ksLinkG2 p.ksLog (ksXLog p) (spongeBlocks p) (ksSplit p + 399) (pl .ksLink 1) g
  -- the boundary claims' point: `n' − 1`'s bits as `E` cells
  let mbE ← Lvm.Q2.mapB (fun b => add b z) mb
  -- the link's `M` coefficients `ω_l · sel`
  let omS ← Lvm.Q2.mapB (fun l => Lvm.Q2.g2Mul (kl.om.getD l default) kl.sel F.z2) (List.range 17)
  let L := layout0 p
  let blkD := dBlock p
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let rho' := kl.shift
  let xlo := rho'.take xl
  let om := kl.om
  let tape : List Lvm.Q2.FClaim :=
    ((List.range dLanes).flatMap fun l =>
      let zl := r ++ selC2 F l 2
      let vl := v.getD l default
      [.dhalf false zl vl.re, .dhalf true zl vl.im]) ++
    [.drow (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)) nuW rw.target] ++
    (List.range 4).map fun l => .e3 ⟨.main, .point blkD (mbE ++ Lvm.Har.selC z.n one.n l 2), kc (hLane l)⟩
  let ks : List Lvm.Q2.FClaim :=
    halves [(F.o2, ksBlk, ko.wordPoint)] ko.word ++ [.row ksBlk ko.slicePoint nuK rk.target]
  let ksOut : List Lvm.Q2.FClaim := (List.range 25).flatMap fun l =>
    let bz := ksYPart2 p F l ki
    halves [(F.o2, bz.1, bz.2)] (kv.getD l default)
  let yParts := (List.range 25).map fun l => let bz := ksYPart2 p F l rho'; (om.getD l default, bz.1, bz.2)
  let inParts := (List.range 25).map fun l => (om.getD l default, ksBlk, rho' ++ selC2 F l slotLog)
  let mParts := (List.range 17).map (fun l => (om.getD l default, (⟨p.ksLog, L.s + l * R⟩ : Placement), rho')) ++
    (List.range 17).map (fun l => (omS.getD l default, (⟨xl, L.s + l * R + ksSplit p⟩ : Placement), xlo))
  let xParts := (List.range 17).map fun l => (om.getD l default, (⟨xl, L.x + l * R⟩ : Placement), xlo)
  let vY := kl.vals.getD 0 default
  let vIn := kl.vals.getD 1 default
  let vM := kl.vals.getD 2 default
  let vX := kl.vals.getD 3 default
  let link : List Lvm.Q2.FClaim :=
    halves yParts vY ++ halves inParts vIn ++ [.half false xParts vX.re] ++ halves mParts vM ++
      [.half true xParts vX.im]
  pure ⟨tape ++ ks ++ ksOut ++ link, mb⟩

/-- The S2GF program with the front and the pin (claims of the front pending). -/
def QFF (C : QCfg) (T : TData) : Program := QF C T frontF pinF

end Lvm.E2Q
