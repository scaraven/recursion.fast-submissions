-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, B-12, B-13; stage S-F4).
import FRVIR4
import FRVIRFinalsSG

/-!
# The phase-final checks over an item sequence (`finalsOf`), and the relocation to `S`'s format

A.9's nine fields (`FRVIRFinals`, `FRVIRFinalsSF`, `FRVIRFinalsSG`) hard-code 3.x's sizes (Z3 26,
S2 28, Lr 15, E2 21, E4 23, the final message `2^7`, the cells' 23 coordinates), its kinds (the KC
tables `κ.m`, `κ.isNode`, `is32`, `rsPtIx`) and its format (`piElem f o` resolves `f` with 3.x's
field offsets). Here every one of them is a parameter (`FinP`):

* `S : Seq`: the rounds, the coordinates, the ladder (`S.lv`), the in-field phase offsets
  (`phaseOffOf S`), the final message `2^S.pf`;
* `kv : KV`: the kind tables the finals read (3.x: from the run's `Kind`; a revision-4 program is
  fixed-kind, so its tables are constants);
* the node's real Lr/E2/E4 counts, `finPf`'s second point family `mB` (3.x: `m = 30`), the node's
  public cells and their coordinates, and `vn`: the **variable last block** of a segment (B-12; the
  shift's `bnd` and its masked successor read `L = n − 1` from `stmt`, `FRVIR4.lastOps`).

`finalsOf P : Finals` is the nine generalised fields. **`finalsOf_seq3`**: at `fin3P` (3.x's
sequence, kind tables, counts) it **is** today's finals `sfFinals finP finPf`, field by field
(`gFinZ_3` …), so its flags are A.9's relations (`flag_finZ` … as proved). A revision-4 program
addresses the proof absolutely (`FRVIR4`): `finOps4 P` is `finalsOf P`'s ops relocated to `S`'s
field offsets (`reloc`); at `seq3` the relocation changes no op's value (`evalOp_reloc_seq3`,
`exec_reloc_seq3`), so **`finOps4_seq3`**: `fin3P`'s relocated finals run exactly as 3.x's.
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## Parameters -/

/-- The kind tables the finals read. -/
structure KV where
  m : Kind → ℕ
  node : Kind → Bool
  /-- `finPf`: the kind's points are the `m*` family (3.x `is32`), else the `mB` family. -/
  selA : Kind → Bool
  /-- `finPf`: the claim points of `rsWeight`, indices into `gPfPts` (3.x `rsPtIx`). -/
  ptIx : Kind → List ℕ

/-- **The finals' parameters.** -/
structure FinP where
  S : Seq
  kv : KV
  /-- The node's real Lr coordinates, E2 coordinates, E4 rounds (3.x: 15, 21, 23). -/
  lrR : ℕ
  e2R : ℕ
  e4R : ℕ
  /-- `finPf`'s second point family (3.x: 30). -/
  mB : ℕ
  /-- The node's public cells (3.x `pfCells`) and their coordinates (3.x 23). -/
  cells : List ℕ
  nc : ℕ
  /-- The variable last block (a segment, B-12). -/
  vn : Bool

/-- 3.x's kind tables. -/
def kv3 : KV := ⟨Kind.m, Kind.isNode, is32, rsPtIx⟩

/-- **3.x's parameters.** -/
def fin3P : FinP := ⟨seq3, kv3, 15, 21, 23, 30, pfCells, 23, false⟩

/-! ## S-0's fields -/

def gFinZ (P : FinP) : FinField := fun fi b =>
  let co := coordsR fi "Z1"; let rs := chals fi "Z3" P.S.z3
  (pinOps ++
   [.packFK (fun κ => [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6] ++ co.take (P.kv.m κ - 13)),
    .packFK (fun κ => rs.take (P.kv.m κ - 6)), .eqPt (b + 7) (b + 8),
    .piElem fZend 0, .piElem fZend 16, .mulF (b + 9) (b + 10), .mulF (b + 12) (b + 11),
    .assertEq (b + 13) (claimN fi "Z3") allK,
    .assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK],
   [b + 10, b + 11, (outsOf fi "Z2").getD 2 0])

def gLcHead (P : FinP) (fi : FinIn) (b : ℕ) : List Op :=
  let α := (outsOf fi "L1").headD 0; let β := (outsOf fi "L3β").headD 0
  let oL3 := phaseOffOf P.S (phaseIx "L3") fL2
  let v := (List.range 8).map fun i => b + (6 + i)
  [.piElem fZend 0, .piElem fZend 16, .mulF α (b + 1), .addF b (b + 2),
    .assertEq (b + 3) (claim0 fi "L2") allK,
    .packFK (fun _ => (chals fi "Z3" P.S.z3).take 8), .rowW ((outsOf fi "Z2").headD 0) (b + 4)] ++
   (List.range 8).map (fun i => .piElem fL2 (oL3 + 16 * i)) ++
   [.const (fun _ => .f 0),
    .packFK (fun κ => if P.kv.node κ then (b + 14) :: (v.take 7 ++ [b + 14])
      else (b + 6) :: List.replicate 8 (b + 14)),
    .maskRows (b + 15) (b + 5), .packF (chals fi "L2" 14), .eqTable (b + 17),
    .walkAB (b + 16) (b + 18), .mulF α (b + 20), .addF (b + 19) (b + 21)] ++
   hornerOps β b ++
   [.assertEq (b + 36) (fi.zhat.getD 1 0) allK,
    .keep P.kv.node (b + 13) (b + 14), .eqZ ((outsOf fi "Z2").headD 0) (b + 14),
    .packF ((chals fi "L2" 14).take 6), .eqTable (b + 39)]

def gFinLc (P : FinP) : FinField := fun fi b =>
  (gLcHead P fi b ++ dotOps (b + 38) (b + 40) (b + 14) (b + 41) 64 ++ lcTail fi b (b + 297), [b + 36])

/-- The variable last block's registers (`FRVIR4.lastOuts`, `stmt`'s outputs from 1): the zero
register, then the 18 bits of `L = n − 1`. -/
def zeroReg (fi : FinIn) : Reg := (outsOf fi "stmt").getD 1 0
def lastRegs (fi : FinIn) : List Reg := (outsOf fi "stmt").drop 2

/-- `bndOps` (revision 3.15) with the last block from the statement when `vn` (B-12). -/
def gBndOps (P : FinP) (fi : FinIn) (b : ℕ) : List Op :=
  [.piElem fHdr 16, .piElem fHdr 32, .piElem fStmt 1, .piElem fStmt 17,
   .const (fun _ => .f 0), .const (fun _ => .f 0), .const (fun _ => .f 1),
   .packFK (fun κ => (if P.kv.node κ then [b + 4, b + 5, b + 4, b + 5] else [b, b + 1, b + 2, b + 3]) ++
     cond P.vn (lastRegs fi)
       (List.replicate (P.kv.m κ - 14) (b + 6) ++ List.replicate (P.S.mStar - P.kv.m κ) (b + 4)))]

/-- `padB` over `S`'s `m*`. -/
def gPadB (P : FinP) (κ : Kind) (xs : List Reg) (z : Reg) : List Reg :=
  xs.take (P.kv.m κ - 14) ++ List.replicate (P.S.mStar - P.kv.m κ) z

/-- `finSh`'s ops from `b₀`, with the masked-shift operand `tm` (3.x: `τ`, register `b₀ + 8`). With
`vn`, `E`, `Sh`, `E₀` are `shiftMask`'s (the segment's: `FRSegTarget4`). -/
def gShCore (P : FinP) (fi : FinIn) (b₀ tm : ℕ) : List Op × List Reg :=
  let co := coordsR fi "S1"; let rs := chals fi "S2" P.S.s2; let nb := P.S.mStar - 14
  let ks := co.getD (nb + 10) 0
  let b := b₀ + 8
  let mk : KC Bool := cond P.vn (fun _ => true) P.kv.node
  (gBndOps P fi b₀ ++
   [.packFK (fun κ => gPadB P κ co (b₀ + 4)), .packF ((co.drop nb).take 10),
    .shiftTarget b (b + 1) (b₀ + 7) ks,
    .assertEq (b + 2) (claim0 fi "S2") allK,
    .packFK (fun κ => gPadB P κ rs (b₀ + 4)), .packFK (fun κ => (rs.drop (P.kv.m κ - 14)).take 10),
    .eqPt b (b + 3), .shiftEq b (b + 3), .const (fun _ => .af (Array.replicate nb 0)),
    .eqPt (b + 7) (b + 3), .shiftMask tm (b + 3),
    .keep mk (b + 9) (b + 5), .keep mk (b + 10) (b + 6),
    .keep mk (b + 11) (b + 8),
    .slotW 0 (b + 1) (b + 4), .mulF (b + 12) (b + 15),
    .mulF ks (b + 14), .addF (b + 13) (b + 17),
    .slotW 1 (b + 1) (b + 4), .slotW 2 (b + 1) (b + 4), .keep P.kv.node (b + 20) (b + 19),
    .mulF (b + 18) (b + 21),
    .packFK (fun κ => co.take (P.kv.m κ - 14) ++ (co.drop nb).take 10),
    .packFK (fun κ => rs.take (P.kv.m κ - 14) ++ (rs.drop (P.kv.m κ - 14)).take 10),
    .linkWAll (b + 23) (b + 24), .mulF ks ks] ++
   linkOps ks b ++
   [.addF (b + 16) (b + 57), .mulF (b + 59) (fi.zhat.getD 2 0),
    .assertEq (b + 60) (claimN fi "S2") allK],
   [b + 16, b + 57])

/-- **`finSh`**: 3.x's; with `vn`, first the masked shift's operand `τ ‖ L` (`τ` zero-padded by the
statement's zero register; register `b₀`). -/
def gFinSh (P : FinP) : FinField := fun fi b₀ =>
  cond P.vn
    ((Op.packFK (fun κ => gPadB P κ (coordsR fi "S1") (zeroReg fi) ++ lastRegs fi)) ::
      (gShCore P fi (b₀ + 1) b₀).1, (gShCore P fi (b₀ + 1) b₀).2)
    (gShCore P fi b₀ (b₀ + 8))

def gFinLr (P : FinP) : FinField := fun fi b =>
  let kL := (outsOf fi "Lr3").headD 0
  ([.piElem fLrEnd 0, .piElem fLrEnd 16, .piElem fLrEnd 32,
    .packF ((coordsR fi "Lr1").take P.lrR), .packF (chals fi "Lr2" P.lrR), .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "Lr2") P.kv.node,
    .mulF kL (b + 1), .mulF kL kL, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11)],
   [b + 13, b + 4])

/-! ## S-F's fields -/

def gRsTail (P : FinP) (kap t₀ t₁ t₂ t₃ d : ℕ) : List Op :=
  [.const (fun _ => .f 0), .addF t₃ d, .keep P.kv.node (d + 1) d,
   .mulF kap (d + 2), .addF t₂ (d + 3), .mulF kap (d + 4), .addF t₁ (d + 5), .mulF kap (d + 6),
   .addF t₀ (d + 7), .piField fRS0 (rsOff 3 0) 2048, .assertZero (d + 9) (fun κ => !P.kv.node κ)]

def gFinRS (P : FinP) : FinField := fun fi b =>
  let kap := (coordsR fi "RS1").getD 7 0
  let lam := (outsOf fi "Z2").headD 0
  let c₀ := b + 7
  let cw := 1 + 128 * elemW
  let d := c₀ + 4 * cw
  ([.const (fun _ => .f (pinnedRho 0)), .eqZ lam b,
    .packF ((chals fi "L2" 14).take 7), .eqTable (b + 2),
    .packFK (fun κ => ((chals fi "S2" P.S.s2).drop (P.kv.m κ - 14)).take 7), .eqTable (b + 4),
    .packF (rsFsRegs fi)] ++
   claimOps 0 (fun i => .getF (b + 1) i) (b + 6) c₀ ++
   claimOps 1 (fun i => .getF (b + 3) i) (b + 6) (c₀ + cw) ++
   claimOps 2 (fun i => .getF (b + 5) i) (b + 6) (c₀ + 2 * cw) ++
   claimOps 3 (fun i => .const (fun _ => .f (bb i))) (b + 6) (c₀ + 3 * cw) ++
   gRsTail P kap (c₀ + cw - 1) (c₀ + 2 * cw - 1) (c₀ + 3 * cw - 1) (c₀ + 4 * cw - 1) d,
   (List.range 4).map (fun j => c₀ + j * cw + 127 * elemW + 4) ++ [d + 8])

/-- E4 end's message inside the E field of `S`'s format. -/
def gOE4end (S : Seq) : ℕ := phaseOffOf S (phaseIx "E4end") fE

def gFinE (P : FinP) : FinField := fun fi b =>
  let kE := (outsOf fi "E3").headD 0
  let kL := (outsOf fi "Lr3").headD 0
  let fz := fi.zhat.getD 3 0
  let o := gOE4end P.S
  ([.piElem fEEnd 0, .piElem fEEnd 16, .piElem fEEnd 32,
    .packF ((coordsR fi "E1").take P.e2R), .packF (chals fi "E2" P.e2R), .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "E2") P.kv.node,
    .mulF kE (b + 1), .mulF kE kE, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11),
    .mulF (b + 10) kE, .mulF (b + 14) (lrEx fi 0), .addF (b + 13) (b + 15),
    .assertEq (b + 16) (claim0 fi "E4") P.kv.node,
    .packF (chals fi "E4" P.e4R), .evalM (b + 4) (b + 17), .mulF kE (b + 19), .mulF (b + 10) (b + 20),
    .addF (b + 18) (b + 21), .addF (b + 23) (b + 22),
    .evalL (lrEx fi 1) (b + 17), .mulF kL (b + 26), .mulF kL kL, .mulF (b + 29) (b + 27),
    .addF (b + 25) (b + 28), .addF (b + 31) (b + 30),
    .mulF (b + 14) (b + 32), .addF (b + 24) (b + 33), .mulF (b + 34) fz,
    .assertEq (b + 35) (claimN fi "E4") P.kv.node,
    .piElem fE o, .assertEq (b + 36) fz allK, .piField fE (o + 16) 16,
    .assertZero (b + 37) allK],
   [b + 17])

def gFinB' (P : FinP) : FinField := fun fi b =>
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  ([.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0), .keep P.kv.node (b + 27) (b + 28),
    .addF vRS (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 31) (b + 30), .assertEq (b + 32) (claim0 fi "P1") allK],
   [b + 30])

/-! ## S-G's fields -/

/-- `encOps` over a final message of `2^pf` K elements. -/
def gEncOps (pf : ℕ) (units fin : List Reg) (j y b : ℕ) : List Op :=
  (List.range pf).map (fun v => .tensorW j (units.getD v 0)) ++
    hornerKOps ((List.range pf).map (b + ·)) pf fin (b + pf) ++
    [.assertEq (hornerKOut pf fin (b + pf)) y allK]

def gUnitK (pf v : ℕ) : Array K := ((List.range pf).map fun u => if u = v then (1 : K) else 0).toArray

def gEncW (pf : ℕ) : ℕ := pf + 2 * (2 ^ pf - 1)

/-- `finP 4` over `2^S.pf`. -/
def gFinPTop (P : FinP) : FinField := fun fi b =>
  let pf := P.S.pf
  let fin := (List.range (2 ^ pf)).map (b + ·)
  let units := (List.range pf).map (b + 2 ^ pf + ·)
  ((List.range (2 ^ pf)).map (fun c => .piElemK fFinal (32 * c)) ++
    (List.range pf).map (fun v => .const fun _ => .ak (gUnitK pf v)) ++
    (List.range (ysOf fi 4).length).flatMap (fun q =>
      gEncOps pf units fin ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0)
        (b + (2 ^ pf + pf) + gEncW pf * q)) ++
    [.assertEq (claim0 fi "Pf") (p1ClaimN fi 4) allK], [])

def gFinP (P : FinP) (i : ℕ) : FinField := if i < 4 then finPLow i else gFinPTop P

def gSRegs (S : Seq) (fi : FinIn) (i : ℕ) : List Reg := ((lvOuts fi i 0).drop 1).take (S.lv i).ell

def gTailRegs (S : Seq) (fi : FinIn) (m k : ℕ) : List Reg :=
  (List.range' k (5 - k)).flatMap (fun j => (gSRegs S fi j).drop 1) ++ (chals fi "Pf" S.pf).take (m - 25)

def gP0Regs (S : Seq) (fi : FinIn) (m : ℕ) : List Reg := gSRegs S fi 0 ++ gTailRegs S fi m 1

def gLcSrc (S : Seq) (fi : FinIn) (m : ℕ) : List PtSrc :=
  ((chals fi "L2" 14).drop 7).map .f ++ (((chals fi "Z3" S.z3).take (m - 6)).drop 8).map .f

def gShSrc (S : Seq) (fi : FinIn) (m : ℕ) : List PtSrc :=
  (((chals fi "S2" S.s2).drop (m - 7)).take 3).map .f ++ List.replicate 4 (.c 0) ++
    ((chals fi "S2" S.s2).take (m - 14)).map .f

/-- The points: claims `0 … 6` (the `m*` and `mB` families, E4's `r′`), the tails (`7 … 10`,
`11 … 14`), `P₀` (`15`, `16`). -/
def gPfPts (P : FinP) (fi : FinIn) : List (List PtSrc) :=
  let S := P.S; let mA := S.mStar; let mB := P.mB
  [zSrc fi mA, zSrc fi mB, gLcSrc S fi mA, gLcSrc S fi mB, gShSrc S fi mA, gShSrc S fi mB,
    (chals fi "E4" P.e4R).map .f] ++
    (List.range 4).map (fun k => (gTailRegs S fi mA (k + 1)).map .k) ++
    (List.range 4).map (fun k => (gTailRegs S fi mB (k + 1)).map .k) ++
    [(gP0Regs S fi mA).map .k, (gP0Regs S fi mB).map .k]

/-- `cellOps` over `nc` coordinates (width `nc + 3`). -/
def gCellOps (nc : ℕ) (one g h kp : Reg) (cell acc pw b : ℕ) : List Op :=
  prodKOps ((List.range nc).map fun v => if cell.testBit v then g + v else h + v) one b ++
    [.mulKF (b + (nc - 1)) pw, .addK acc (b + nc), .mulF pw kp]

def gCellsOps (nc : ℕ) (one g h kp : Reg) : List ℕ → Reg → Reg → ℕ → List Op
  | [], _, _, _ => []
  | c :: cs, acc, pw, b =>
    gCellOps nc one g h kp c acc pw b ++ gCellsOps nc one g h kp cs (b + (nc + 1)) (b + (nc + 2)) (b + (nc + 3))

def gCellsAcc (nc : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], acc, _ => acc
  | _ :: cs, _, b => gCellsAcc nc cs (b + (nc + 1)) (b + (nc + 3))

def gLvOps (S : Seq) (fi : FinIn) (k : ℕ) (one cu T W b : Reg) : List Op :=
  let ys := ysOf fi (k - 1)
  let a := b + 2 + 4 * ys.length
  [.packF (kcOf fi (k - 1)), .eqTable b] ++
    (List.range ys.length).map (fun q => .tensorW (ys.getD q 0 - 3) T) ++
    accOps (b + 1) (tRegs fi (k - 1) b) 0 W (b + 2 + ys.length) ++
    [.mulK ((gSRegs S fi k).headD 0) cu, .addK one a,
     .mulK (a + 1) (accOut W (b + 2 + ys.length) (tRegs fi (k - 1) b))]

def gLvsOps (S : Seq) (fi : FinIn) (one cu Ts : Reg) : List ℕ → Reg → ℕ → List Op
  | [], _, _ => []
  | k :: ks, W, b => gLvOps S fi k one cu (Ts + (k - 1)) W b ++
      gLvsOps S fi one cu Ts ks (b + lvW fi k - 1) (b + lvW fi k)

/-- `Π_{x ∈ sf[μ .. pf)} (1 + x)`: the factors (`k` registers from `pd`), their product. -/
def padOps (one pd μ k : ℕ) (sf : List Reg) : List Op :=
  (List.range k).map (fun i => .addK one (sf.getD (μ + i) 0)) ++
    prodKOps ((List.range (k - 1)).map (pd + 1 + ·)) pd (pd + k)

/-- The register of `padOps`' product (`one` if empty). -/
def padReg (one pd k : ℕ) : ℕ := if k = 0 then one else pd + (2 * k - 2)

def gFinPf (P : FinP) : FinField := fun fi b =>
  let S := P.S; let nc := P.nc
  let one := b
  let cu := b + 1
  let z0 := b + 2
  let pts := gPfPts P fi
  let Pp := ptsOut pts (b + 3)
  let sb := b + 3 + ptsW pts
  let wb := sb + 5
  let rs1 := coordsR fi "RS1"
  let kp := (outsOf fi "B'").headD 0
  let cb := wb + (2 + 2 * nc)
  let ce := cb + 1 + (nc + 3) * P.cells.length
  let lb := ce + 2
  let fb := lb + lvsW fi [1, 2, 3, 4]
  let pd := fb + 2 + 4 * 2 ^ S.pf
  let sf := chals fi "Pf" S.pf
  let μ := P.mB - 25
  let k := S.pf - μ
  let nP := k + (k - 1)
  ([.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)] ++
   ptsOps one z0 pts (b + 3) ++
   [.keep P.kv.selA (Pp 7) (Pp 11), .keep P.kv.selA (Pp 8) (Pp 12), .keep P.kv.selA (Pp 9) (Pp 13),
    .keep P.kv.selA (Pp 10) (Pp 14), .keep P.kv.selA (Pp 15) (Pp 16)] ++
   [.packF ((List.range 7).map fun p => rs1.getD p 0),
    .rsWeight wb (fun κ => (P.kv.ptIx κ).map Pp) (rs1.getD 7 0) ((outsOf fi "L3β").headD 0)
      P.kv.node (sb + 4)] ++
   (List.range nc).map (fun v => .getK (sb + 4) v) ++
   (List.range nc).map (fun v => .addK one (wb + 2 + v)) ++
   [.mulF kp kp] ++
   gCellsOps nc one (wb + 2) (wb + (nc + 2)) kp P.cells z0 cb (cb + 1) ++
   [.keep P.kv.node (gCellsAcc nc P.cells z0 (cb + 1)) z0, .addK (wb + 1) ce] ++
   gLvsOps S fi one cu sb [1, 2, 3, 4] (ce + 1) lb ++
   [.packK sf, .eqTableK fb] ++ fhOps (fb + 1) (List.range (2 ^ S.pf)) z0 (fb + 2) ++
   padOps one pd μ k sf ++
   [.keep P.kv.selA one (padReg one pd k),
    .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) lb) (pd + nP),
    .mulK (pd + nP + 1) (fhOut (List.range (2 ^ S.pf)) z0 (fb + 2)),
    .assertEq (pd + nP + 2) (claimN fi "Pf") allK], [])

/-! ## `finalsOf` -/

/-- **The finals over `P`.** -/
def finalsOf (P : FinP) : Finals :=
  ⟨gFinRS P, gFinZ P, gFinLc P, gFinSh P, gFinLr P, gFinE P, gFinB' P, gFinP P, gFinPf P⟩

/-! ## At `seq3`: today's finals -/

theorem phaseOffOf_seq3 (n f : ℕ) : phaseOffOf seq3 n f = phaseOff n f := by
  have h : seq3.lv = lvlStar := by rw [seq3_eq]; rfl
  rw [phaseOffOf, ← phasesOf_seq3, ← List.map_take, List.map_map, h, phaseOff]
  exact congrArg List.sum (List.map_congr_left fun p _ => p.shape.bytesToL_toSh f)

theorem fin3P_S : fin3P.S = ⟨32, 19, 26, 28, 15, 21, 23, 7, 32, 6⟩ := seq3_eq

theorem gFinZ_3 : gFinZ fin3P = finZ := by
  funext fi b; simp only [gFinZ, finZ, fin3P_S]; rfl

theorem gFinLc_3 : gFinLc fin3P = finLc := by
  funext fi b
  simp only [gFinLc, finLc, gLcHead, lcHead, show (fin3P).S = seq3 from rfl, phaseOffOf_seq3]
  (try rw [seq3_eq]); rfl

theorem gFinSh_3 : gFinSh fin3P = finSh := by
  funext fi b; simp only [gFinSh, gShCore, finSh, gBndOps, bndOps, gPadB, padB, fin3P_S]; rfl

theorem gFinLr_3 : gFinLr fin3P = finLr := by
  funext fi b; rfl

theorem gFinRS_3 : gFinRS fin3P = finRS := by
  funext fi b; simp only [gFinRS, finRS, gRsTail, rsTail, fin3P_S]; rfl

theorem gFinE_3 : gFinE fin3P = finE := by
  funext fi b
  simp only [gFinE, finE, gOE4end, oE4end, show (fin3P).S = seq3 from rfl, phaseOffOf_seq3]
  (try rw [seq3_eq]); rfl

theorem gFinB'_3 : gFinB' fin3P = finB' := by
  funext fi b; rfl

theorem gFinP_3 : gFinP fin3P = finP := by
  funext i fi b; simp only [gFinP, finP]
  split_ifs
  · rfl
  · simp only [gFinPTop, finP4, gEncOps, encOps, gUnitK, unitK, gEncW, encW, fin3P_S]; rfl

theorem gCellsOps_23 (one g h kp : Reg) : ∀ (cs : List ℕ) (acc pw b : ℕ),
    gCellsOps 23 one g h kp cs acc pw b = cellsOps one g h kp cs acc pw b
  | [], _, _, _ => rfl
  | c :: cs, acc, pw, b => by
    rw [gCellsOps, cellsOps, gCellsOps_23 one g h kp cs]; rfl

theorem gCellsAcc_23 : ∀ (cs : List ℕ) (acc b : ℕ), gCellsAcc 23 cs acc b = cellsAcc cs acc b
  | [], _, _ => rfl
  | _ :: cs, _, b => by rw [gCellsAcc, cellsAcc, gCellsAcc_23 cs]

theorem gLvsOps_3 (fi : FinIn) (one cu Ts : Reg) : ∀ (ks : List ℕ) (W b : ℕ),
    gLvsOps seq3 fi one cu Ts ks W b = lvsOps fi one cu Ts ks W b
  | [], _, _ => rfl
  | k :: ks, W, b => by
    rw [gLvsOps, lvsOps, gLvsOps_3 fi one cu Ts ks]
    have h : seq3.lv = lvlStar := by rw [seq3_eq]; rfl
    simp only [gLvOps, lvOps, gSRegs, sRegs, h]

theorem gPfPts_3 (fi : FinIn) : gPfPts fin3P fi = pfPts fi := by
  have h : seq3.lv = lvlStar := by rw [seq3_eq]; rfl
  simp only [gPfPts, pfPts, gTailRegs, tailRegs, gP0Regs, p0Regs, gSRegs, sRegs, gLcSrc, lcSrc,
    gShSrc, shSrc, eSrc, show (fin3P).S = seq3 from rfl, h]
  (try rw [seq3_eq]); rfl

theorem gFinPf_3 : gFinPf fin3P = finPf := by
  funext fi b
  simp only [gFinPf, finPf, gPfPts_3, show (fin3P).S = seq3 from rfl, show (fin3P).nc = 23 from rfl,
    show (fin3P).cells = pfCells from rfl, gCellsOps_23, gCellsAcc_23, gLvsOps_3,
    show (fin3P).kv = kv3 from rfl, show (fin3P).mB = 30 from rfl]
  simp only [seq3_eq, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, kv3]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- **The generalised finals at 3.x's sequence and kinds are today's finals** (field by field). -/
theorem finalsOf_seq3 : finalsOf fin3P = sfFinals finP finPf := by
  simp only [finalsOf, sfFinals, s0Finals, gFinZ_3, gFinLc_3, gFinSh_3, gFinLr_3, gFinRS_3, gFinE_3,
    gFinB'_3, gFinP_3, gFinPf_3]

/-! ## Relocation to `S`'s format -/

/-- **`reloc S`**: a proof read at field `f < 19`, offset `o` becomes the absolute read
`fieldOffOf S f + o` (field `0`, offset `0`: `absOff 0 x = x`). -/
def reloc (S : Seq) : Op → Op
  | .piField f o len => if f < 19 then .piField 0 (fieldOffOf S f + o) len else .piField f o len
  | .piElem f o => if f < 19 then .piElem 0 (fieldOffOf S f + o) else .piElem f o
  | .piElemK f o => if f < 19 then .piElemK 0 (fieldOffOf S f + o) else .piElemK f o
  | .piDigest f o => if f < 19 then .piDigest 0 (fieldOffOf S f + o) else .piDigest f o
  | .piDigestAt f o k => if f < 19 then .piDigestAt 0 (fieldOffOf S f + o) k else .piDigestAt f o k
  | op => op

theorem absOff_zero (x : ℕ) : absOff 0 x = x := by
  simp [absOff, fieldOffA, fieldOff]

theorem absOff_seq3 {f : ℕ} (hf : f < 19) (o : ℕ) : absOff 0 (fieldOffOf seq3 f + o) = absOff f o := by
  have h : fieldOffOf seq3 f = fieldOff f := by
    have := congrArg (·[f]?) fieldOffs.1
    simpa [List.getElem?_map, hf] using this
  rw [absOff_zero, h, absOff, fieldOffA]
  have hf' : f < nFields + 1 := by simp only [nFields]; omega
  simp [Array.getD_eq_getD_getElem?, hf']

/-- **At `seq3` the relocation changes no op's value.** -/
theorem evalOp_reloc_seq3 (impl : OpImpl) (κ : Kind) (inp : Input) (regs : Array Val) (op : Op) :
    evalOp impl κ inp regs (reloc seq3 op) = evalOp impl κ inp regs op := by
  cases op with
  | piField f o len => dsimp only [reloc]; split_ifs with hf <;> [simp only [evalOp, absOff_seq3 hf]; rfl]
  | piElem f o => dsimp only [reloc]; split_ifs with hf <;> [simp only [evalOp, absOff_seq3 hf]; rfl]
  | piElemK f o => dsimp only [reloc]; split_ifs with hf <;> [simp only [evalOp, absOff_seq3 hf]; rfl]
  | piDigest f o => dsimp only [reloc]; split_ifs with hf <;> [simp only [evalOp, absOff_seq3 hf]; rfl]
  | piDigestAt f o k => dsimp only [reloc]; split_ifs with hf <;> [simp only [evalOp, absOff_seq3 hf]; rfl]
  | _ => rfl

theorem outs_reloc (S : Seq) (op : Op) : (reloc S op).outs = op.outs := by
  cases op <;> first | rfl | (dsimp only [reloc]; split_ifs <;> rfl)

theorem item_reloc (S : Seq) (op : Op) : (reloc S op).item? = op.item? := by
  cases op <;> first | rfl | (dsimp only [reloc]; split_ifs <;> rfl)

theorem opsOut_reloc (S : Seq) (ops : List Op) : opsOut (ops.map (reloc S)) = opsOut ops := by
  simp only [opsOut, List.map_map, Function.comp_def, outs_reloc]

theorem exec_reloc_seq3 (impl : OpImpl) (κ : Kind) (inp : Input) :
    ∀ (ops : List Op) (s : St) (tr : Trace),
      exec impl κ inp (ops.map (reloc seq3)) s tr = exec impl κ inp ops s tr
  | [], _, _ => rfl
  | op :: ops, s, tr => by
    simp only [List.map_cons, exec, evalOp_reloc_seq3]
    rcases evalOp impl κ inp s.regs op with ⟨vs, ok⟩ | q
    · exact exec_reloc_seq3 impl κ inp ops _ _
    · rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · rfl
      · simp only [exec_reloc_seq3 impl κ inp ops]

/-- **The relocated finals** (`FRVIR4.gen4`'s `fin`). -/
def finOps4 (P : FinP) : FinOps := fun outs b => ((finalsOf P).ops outs b).map (reloc P.S)

/-- **At 3.x's parameters the relocated finals run exactly as today's.** -/
theorem finOps4_seq3 (impl : OpImpl) (κ : Kind) (inp : Input) (outs : Array (List Reg)) (b : ℕ)
    (s : St) (tr : Trace) :
    exec impl κ inp (finOps4 fin3P outs b) s tr = exec impl κ inp ((sfFinals finP finPf).ops outs b) s tr := by
  show exec impl κ inp (((finalsOf fin3P).ops outs b).map (reloc seq3)) s tr = _
  rw [exec_reloc_seq3, finalsOf_seq3]

/-! ## Controls -/

/-- (−) **At `seq4` the node's E4 point has 25 coordinates** (3.x: 23), and E4 end moves inside
the E field (`L32`'s finals are not 3.x's). -/
theorem gOE4end_seq4 : gOE4end seq4 ≠ gOE4end seq3 := by
  rw [gOE4end, gOE4end, seq4_eq, seq3_eq]; decide +kernel

/-- (−) **The relocation is not the identity at `seq4`**: E's field moves. -/
theorem reloc_seq4_moves : fieldOffOf seq4 fE ≠ fieldOff fE := by
  rw [seq4_eq]; decide +kernel

end Rev4
end FR
