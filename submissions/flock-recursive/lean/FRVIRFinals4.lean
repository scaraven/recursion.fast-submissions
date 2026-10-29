-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, B-12, B-13; stage S-F4).
import FRVIR4
import FRVIRFinalsCoreSG

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
* the node's real Lr/E2/E4 counts, `finPf`'s point families besides `m*` (`fams`; 3.x `[30]`) and
  E4 point lengths (`e4s`; 3.x `[23]`), the node's public cells and their coordinates, and `vn`: the
  **variable last block** of a segment (B-12; the shift's `bnd` and its masked successor read
  `L = n − 1` from `stmt`, `FRVIR4.lastOps`).

**Revision 4.3 (route (A)): one program per group.** Every generator takes a count source `P` and a
last argument `Q : Kind → FinP` (default `fun _ => P`): the per-kind data (`kv`, `lrR`, `e2R`, `e4R`,
the cells) are read in kind tables from `Q κ`, the counts (ops, registers) from `P` only. So the
kinds of a group, given the group's counts (`FRVerifierC4.segFinP`/`nodeFinP`: `nc = 25`, the
group's families, `ck`), have one op list up to kind tables, and the group program is the same list
with `Q` the kinds per index (`FRVIR4Mux`, `FRVIR4At`, `FRVIR4Uni`). In `finPf`: every family's
points, tails, `P₀` and pad chain are computed and the kind's selected by tables (`selOps`, `fsel`,
`selA`); `nc` is the group's (a shorter kind's extra coordinate is a factor `1`: `P₀` has `m − 7`
entries, `getK` past them reads `0`, the cell's bit is `0`); with `ck` the cells' bits are kind
tables (`gCellOpsK`); the kind's final zero tail (`FRVIR4.finalOps4`'s before 4.3) is checked at the
end (`gTailOps`, after the exports: no earlier register moves).

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
  /-- `finPf`: the kind's points are the `m*` family (3.x `is32`), else its family `fsel`. -/
  selA : Kind → Bool
  /-- `finPf`: the claim points of `rsWeight`, indices into `gPfPts` (3.x `rsPtIx`). -/
  ptIx : Kind → List ℕ
  /-- `finPf`: the kind's family in `FinP.fams` when not `selA` (3.x: `0`, its one family). -/
  fsel : Kind → ℕ

/-- **The finals' parameters**: per-kind data and counts (revision 4.3, route (A)). The ops'
number and registers depend on the counts only; a group program (`FRVIR4Mux`) reads the counts from
one `FinP` and the per-kind data of index `κ` in kind tables from `Q κ`, a fixed-kind program reads
both from its own (`Q := fun _ => P`, every generator's last argument). -/
structure FinP where
  /-- Count: the sequence. -/
  S : Seq
  /-- Per kind: the kind tables. -/
  kv : KV
  /-- Per kind: the node's real Lr coordinates, E2 coordinates, E4 rounds (3.x: 15, 21, 23). -/
  lrR : ℕ
  e2R : ℕ
  e4R : ℕ
  /-- Count: `finPf`'s point families besides the `m*` one (3.x: `[30]`). -/
  fams : List ℕ
  /-- Count: `finPf`'s E4 claim points, by length (3.x: `[23]`). -/
  e4s : List ℕ
  /-- Per kind: the public cells (3.x `pfCells`; without `ck`, index `.L32`'s for every kind). -/
  cells : List ℕ
  /-- Count: the cells' coordinates (3.x 23; revision 4.3: the group's largest, 25). -/
  nc : ℕ
  /-- Count: the variable last block (a segment, B-12). -/
  vn : Bool
  /-- Count: the kind's points and cells are read from kind tables (`packFK`; one `keep` per cell
  coordinate, `ncell` cells; revision 4.3), else from `P` (3.x: `packF`, register choices). -/
  ck : Bool
  ncell : ℕ
  /-- Count: the final message's zero tails checked at the end of `finPf`, one per `m < m*` of the
  group, each gated by the kind's `m` (revision 4.3; the skeleton's `finalOps4` reads `m*`'s). -/
  tails : List ℕ

/-- 3.x's kind tables. -/
def kv3 : KV := ⟨Kind.m, Kind.isNode, is32, rsPtIx, fun _ => 0⟩

/-- **3.x's parameters.** -/
def fin3P : FinP := ⟨seq3, kv3, 15, 21, 23, [30], [23], pfCells, 23, false, false, 0, []⟩

/-! ## S-0's fields -/

def gFinZ (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let co := coordsR fi "Z1"; let rs := chals fi "Z3" P.S.z3
  (pinOps ++
   ([.packFK (fun κ => [b, b + 1, b + 2, b + 3, b + 4, b + 5, b + 6] ++ co.take ((Q κ).kv.m κ - 13)),
    .packFK (fun κ => rs.take ((Q κ).kv.m κ - 6)), .eqPt (b + 7) (b + 8),
    .piElem fZend 0, .piElem fZend 16, .mulF (b + 9) (b + 10), .mulF (b + 12) (b + 11),
    .assertEq (b + 13) (claimN fi "Z3") allK,
    .assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK] : List Op),
   [b + 10, b + 11, (outsOf fi "Z2").getD 2 0])

def gLcHead (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op :=
  let α := (outsOf fi "L1").headD 0; let β := (outsOf fi "L3β").headD 0
  let oL3 := phaseOffOf P.S (phaseIx "L3") fL2
  let v := (List.range 8).map fun i => b + (6 + i)
  ([.piElem fZend 0, .piElem fZend 16, .mulF α (b + 1), .addF b (b + 2),
    .assertEq (b + 3) (claim0 fi "L2") allK,
    .packFK (fun _ => (chals fi "Z3" P.S.z3).take 8),
    .rowW ((outsOf fi "Z2").headD 0) (b + 4)] : List Op) ++
   ((List.range 8).map (fun i => .piElem fL2 (oL3 + 16 * i)) : List Op) ++
   ([.const (fun _ => .f 0),
    .packFK (fun κ => if (Q κ).kv.node κ then (b + 14) :: (v.take 7 ++ [b + 14])
      else (b + 6) :: List.replicate 8 (b + 14)),
    .maskRows (b + 15) (b + 5), .packF (chals fi "L2" 14), .eqTable (b + 17),
    .walkAB (b + 16) (b + 18), .mulF α (b + 20), .addF (b + 19) (b + 21)] : List Op) ++
   hornerOps β b ++
   ([.assertEq (b + 36) (fi.zhat.getD 1 0) allK,
    .keep (fun κ => (Q κ).kv.node κ) (b + 13) (b + 14), .eqZ ((outsOf fi "Z2").headD 0) (b + 14),
    .packF ((chals fi "L2" 14).take 6), .eqTable (b + 39)] : List Op)

def gFinLc (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  (gLcHead P fi b Q ++ dotOps (b + 38) (b + 40) (b + 14) (b + 41) 64 ++ lcTail fi b (b + 297), [b + 36])

/-- The variable last block's registers (`FRVIR4.lastOuts`, `stmt`'s outputs from 1): the zero
register, then the 18 bits of `L = n − 1`. -/
def zeroReg (fi : FinIn) : Reg := (outsOf fi "stmt").getD 1 0
def lastRegs (fi : FinIn) : List Reg := (outsOf fi "stmt").drop 2

/-- `bndOps` (revision 3.15) with the last block from the statement when `vn` (B-12). -/
def gBndOps (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op :=
  [.piElem fHdr 16, .piElem fHdr 32, .piElem fStmt 1, .piElem fStmt 17,
   .const (fun _ => .f 0), .const (fun _ => .f 0), .const (fun _ => .f 1),
   .packFK (fun κ => (if (Q κ).kv.node κ then [b + 4, b + 5, b + 4, b + 5] else [b, b + 1, b + 2, b + 3]) ++
     cond P.vn (lastRegs fi)
       (List.replicate ((Q κ).kv.m κ - 14) (b + 6) ++ List.replicate (P.S.mStar - (Q κ).kv.m κ) (b + 4)))]

/-- `padB` over `S`'s `m*`. -/
def gPadB (P : FinP) (κ : Kind) (xs : List Reg) (z : Reg) (Q : Kind → FinP := fun _ => P) : List Reg :=
  xs.take ((Q κ).kv.m κ - 14) ++ List.replicate (P.S.mStar - (Q κ).kv.m κ) z

/-- `finSh`'s ops from `b₀`, with the masked-shift operand `tm` (3.x: `τ`, register `b₀ + 8`). With
`vn`, `E`, `Sh`, `E₀` are `shiftMask`'s (the segment's: `FRSegTarget4`). -/
def gShCore (P : FinP) (fi : FinIn) (b₀ tm : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let co := coordsR fi "S1"; let rs := chals fi "S2" P.S.s2; let nb := P.S.mStar - 14
  let ks := co.getD (nb + 10) 0
  let b := b₀ + 8
  let node : KC Bool := fun κ => (Q κ).kv.node κ
  let mk : KC Bool := cond P.vn (fun _ => true) node
  (gBndOps P fi b₀ Q ++
   ([.packFK (fun κ => gPadB P κ co (b₀ + 4) Q), .packF ((co.drop nb).take 10),
    .shiftTarget b (b + 1) (b₀ + 7) ks,
    .assertEq (b + 2) (claim0 fi "S2") allK,
    .packFK (fun κ => gPadB P κ rs (b₀ + 4) Q), .packFK (fun κ => (rs.drop ((Q κ).kv.m κ - 14)).take 10),
    .eqPt b (b + 3), .shiftEq b (b + 3), .const (fun _ => .af (Array.replicate nb 0)),
    .eqPt (b + 7) (b + 3), .shiftMask tm (b + 3),
    .keep mk (b + 9) (b + 5), .keep mk (b + 10) (b + 6),
    .keep mk (b + 11) (b + 8),
    .slotW 0 (b + 1) (b + 4), .mulF (b + 12) (b + 15),
    .mulF ks (b + 14), .addF (b + 13) (b + 17),
    .slotW 1 (b + 1) (b + 4), .slotW 2 (b + 1) (b + 4), .keep node (b + 20) (b + 19),
    .mulF (b + 18) (b + 21),
    .packFK (fun κ => co.take ((Q κ).kv.m κ - 14) ++ (co.drop nb).take 10),
    .packFK (fun κ => rs.take ((Q κ).kv.m κ - 14) ++ (rs.drop ((Q κ).kv.m κ - 14)).take 10),
    .linkWAll (b + 23) (b + 24), .mulF ks ks] : List Op) ++
   linkOps ks b ++
   ([.addF (b + 16) (b + 57), .mulF (b + 59) (fi.zhat.getD 2 0),
    .assertEq (b + 60) (claimN fi "S2") allK] : List Op),
   [b + 16, b + 57])

/-- **`finSh`**: 3.x's; with `vn`, first the masked shift's operand `τ ‖ L` (`τ` zero-padded by the
statement's zero register; register `b₀`). -/
def gFinSh (P : FinP) (fi : FinIn) (b₀ : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  cond P.vn
    ((Op.packFK (fun κ => gPadB P κ (coordsR fi "S1") (zeroReg fi) Q ++ lastRegs fi)) ::
      (gShCore P fi (b₀ + 1) b₀ Q).1, (gShCore P fi (b₀ + 1) b₀ Q).2)
    (gShCore P fi b₀ (b₀ + 8) Q)

/-- `finLr`: the Lr point is the kind's (`lrR`; a kind table if `ck`). -/
def gFinLr (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let kL := (outsOf fi "Lr3").headD 0
  ([.piElem fLrEnd 0, .piElem fLrEnd 16, .piElem fLrEnd 32,
    cond P.ck (.packFK fun κ => (coordsR fi "Lr1").take (Q κ).lrR)
      (.packF ((coordsR fi "Lr1").take (Q .L32).lrR)),
    cond P.ck (.packFK fun κ => chals fi "Lr2" (Q κ).lrR) (.packF (chals fi "Lr2" (Q .L32).lrR)),
    .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "Lr2") (fun κ => (Q κ).kv.node κ),
    .mulF kL (b + 1), .mulF kL kL, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11)],
   [b + 13, b + 4])

/-! ## S-F's fields -/

def gRsTail (P : FinP) (kap t₀ t₁ t₂ t₃ d : ℕ) (Q : Kind → FinP := fun _ => P) : List Op :=
  [.const (fun _ => .f 0), .addF t₃ d, .keep (fun κ => (Q κ).kv.node κ) (d + 1) d,
   .mulF kap (d + 2), .addF t₂ (d + 3), .mulF kap (d + 4), .addF t₁ (d + 5), .mulF kap (d + 6),
   .addF t₀ (d + 7), .piField fRS0 (rsOff 3 0) 2048, .assertZero (d + 9) (fun κ => !(Q κ).kv.node κ)]

def gFinRS (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let kap := (coordsR fi "RS1").getD 7 0
  let lam := (outsOf fi "Z2").headD 0
  let c₀ := b + 7
  let cw := 1 + 128 * elemW
  let d := c₀ + 4 * cw
  (([.const (fun _ => .f (pinnedRho 0)), .eqZ lam b,
    .packF ((chals fi "L2" 14).take 7), .eqTable (b + 2),
    .packFK (fun κ => ((chals fi "S2" P.S.s2).drop ((Q κ).kv.m κ - 14)).take 7), .eqTable (b + 4),
    .packF (rsFsRegs fi)] : List Op) ++
   claimOps 0 (fun i => .getF (b + 1) i) (b + 6) c₀ ++
   claimOps 1 (fun i => .getF (b + 3) i) (b + 6) (c₀ + cw) ++
   claimOps 2 (fun i => .getF (b + 5) i) (b + 6) (c₀ + 2 * cw) ++
   claimOps 3 (fun i => .const (fun _ => .f (bb i))) (b + 6) (c₀ + 3 * cw) ++
   gRsTail P kap (c₀ + cw - 1) (c₀ + 2 * cw - 1) (c₀ + 3 * cw - 1) (c₀ + 4 * cw - 1) d Q,
   (List.range 4).map (fun j => c₀ + j * cw + 127 * elemW + 4) ++ [d + 8])

/-- E4 end's message inside the E field of `S`'s format. -/
def gOE4end (S : Seq) : ℕ := phaseOffOf S (phaseIx "E4end") fE

/-- `finE`: the E2 and E4 points are the kind's (`e2R`, `e4R`; kind tables if `ck`). -/
def gFinE (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let kE := (outsOf fi "E3").headD 0
  let kL := (outsOf fi "Lr3").headD 0
  let fz := fi.zhat.getD 3 0
  let o := gOE4end P.S
  let node : KC Bool := fun κ => (Q κ).kv.node κ
  ([.piElem fEEnd 0, .piElem fEEnd 16, .piElem fEEnd 32,
    cond P.ck (.packFK fun κ => (coordsR fi "E1").take (Q κ).e2R)
      (.packF ((coordsR fi "E1").take (Q .L32).e2R)),
    cond P.ck (.packFK fun κ => chals fi "E2" (Q κ).e2R) (.packF (chals fi "E2" (Q .L32).e2R)),
    .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "E2") node,
    .mulF kE (b + 1), .mulF kE kE, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11),
    .mulF (b + 10) kE, .mulF (b + 14) (lrEx fi 0), .addF (b + 13) (b + 15),
    .assertEq (b + 16) (claim0 fi "E4") node,
    cond P.ck (.packFK fun κ => chals fi "E4" (Q κ).e4R) (.packF (chals fi "E4" (Q .L32).e4R)),
    .evalM (b + 4) (b + 17), .mulF kE (b + 19),
    .mulF (b + 10) (b + 20),
    .addF (b + 18) (b + 21), .addF (b + 23) (b + 22),
    .evalL (lrEx fi 1) (b + 17), .mulF kL (b + 26), .mulF kL kL, .mulF (b + 29) (b + 27),
    .addF (b + 25) (b + 28), .addF (b + 31) (b + 30),
    .mulF (b + 14) (b + 32), .addF (b + 24) (b + 33), .mulF (b + 34) fz,
    .assertEq (b + 35) (claimN fi "E4") node,
    .piElem fE o, .assertEq (b + 36) fz allK, .piField fE (o + 16) 16,
    .assertZero (b + 37) allK],
   [b + 17])

def gFinB' (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  ([.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0),
    .keep (fun κ => (Q κ).kv.node κ) (b + 27) (b + 28),
    .addF vRS (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 31) (b + 30), .assertEq (b + 32) (claim0 fi "P1") allK],
   [b + 30])

/-! ## S-G's fields -/

/-- `encOps` over a final message of `2^pf` K elements. -/
def gEncOps (pf : ℕ) (units fin : List Reg) (j y b : ℕ) : List Op :=
  ((List.range pf).map (fun v => .tensorW j (units.getD v 0)) : List Op) ++
    hornerKOps ((List.range pf).map (b + ·)) pf fin (b + pf) ++
    ([.assertEq (hornerKOut pf fin (b + pf)) y allK] : List Op)

def gUnitK (pf v : ℕ) : Array K := ((List.range pf).map fun u => if u = v then (1 : K) else 0).toArray

def gEncW (pf : ℕ) : ℕ := pf + 2 * (2 ^ pf - 1)

/-- `finP 4` over `2^S.pf`. -/
def gFinPTop (P : FinP) : FinField := fun fi b =>
  let pf := P.S.pf
  let fin := (List.range (2 ^ pf)).map (b + ·)
  let units := (List.range pf).map (b + 2 ^ pf + ·)
  (((List.range (2 ^ pf)).map (fun c => .piElemK fFinal (32 * c)) : List Op) ++
    ((List.range pf).map (fun v => .const fun _ => .ak (gUnitK pf v)) : List Op) ++
    (List.range (ysOf fi 4).length).flatMap (fun q =>
      gEncOps pf units fin ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0)
        (b + (2 ^ pf + pf) + gEncW pf * q)) ++
    ([.assertEq (claim0 fi "Pf") (p1ClaimN fi 4) allK] : List Op), [])

def gFinP (P : FinP) (i : ℕ) : FinField := if i < 4 then finPLow i else gFinPTop P

def gSRegs (S : Seq) (fi : FinIn) (i : ℕ) : List Reg := ((lvOuts fi i 0).drop 1).take (S.lv i).ell

def gTailRegs (S : Seq) (fi : FinIn) (m k : ℕ) : List Reg :=
  (List.range' k (5 - k)).flatMap (fun j => (gSRegs S fi j).drop 1) ++ (chals fi "Pf" S.pf).take (m - 25)

def gP0Regs (S : Seq) (fi : FinIn) (m : ℕ) : List Reg := gSRegs S fi 0 ++ gTailRegs S fi m 1

def gLcSrc (S : Seq) (fi : FinIn) (m : ℕ) : List PtSrc :=
  (((chals fi "L2" 14).drop 7).map .f : List PtSrc) ++
    ((((chals fi "Z3" S.z3).take (m - 6)).drop 8).map .f : List PtSrc)

def gShSrc (S : Seq) (fi : FinIn) (m : ℕ) : List PtSrc :=
  ((((chals fi "S2" S.s2).drop (m - 7)).take 3).map .f : List PtSrc) ++
    (List.replicate 4 (.c 0) : List PtSrc) ++
    (((chals fi "S2" S.s2).take (m - 14)).map .f : List PtSrc)

/-- The points: the claims (Z, Lc, Sh of the `m*` family, then of each family of `fams`; E4's `r′`
of each length of `e4s`), the tails `P₁ … P₄` (`m*`, then each family), `P₀` (`m*`, then each
family). At 3.x (`fams = [30]`, `e4s = [23]`): claims `0 … 6`, tails `7 … 14`, `P₀` `15`, `16`. -/
def gPfPts (P : FinP) (fi : FinIn) : List (List PtSrc) :=
  let S := P.S; let mA := S.mStar
  let tl : ℕ → List (List PtSrc) := fun m => (List.range 4).map fun k => (gTailRegs S fi m (k + 1)).map .k
  [zSrc fi mA] ++ P.fams.map (zSrc fi) ++ [gLcSrc S fi mA] ++ P.fams.map (gLcSrc S fi) ++
    [gShSrc S fi mA] ++ P.fams.map (gShSrc S fi) ++ P.e4s.map (fun e => (chals fi "E4" e).map .f) ++
    tl mA ++ P.fams.flatMap tl ++ [(gP0Regs S fi mA).map .k] ++ P.fams.map (fun m => (gP0Regs S fi m).map .k)

/-- The register of family `i`'s candidate for slot `s` (tails `P₁ … P₄` at `s < 4`, `P₀` at `4`). -/
def pfCand (P : FinP) (Pp : ℕ → ℕ) (i s : ℕ) : Reg :=
  if s < 4 then Pp (7 + 3 * P.fams.length + P.e4s.length + 4 * i + s)
  else Pp (8 + 7 * P.fams.length + P.e4s.length + i)

/-- The `m*` family's candidate for slot `s`. -/
def pfCandA (P : FinP) (Pp : ℕ → ℕ) (s : ℕ) : Reg :=
  if s < 4 then Pp (3 + 3 * P.fams.length + P.e4s.length + s) else Pp (7 + 7 * P.fams.length + P.e4s.length)

/-- **One of `n` candidates by a kind table** (`sel i`: candidate `i` is the kind's; candidate `0` by
default): `n − 1` `keep`s from register `pb`. -/
def selOps (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n pb : ℕ) : List Op :=
  (List.range (n - 1)).map fun i =>
    .keep (sel (i + 1)) (cand (i + 1)) (if i = 0 then cand 0 else pb + (i - 1))

/-- The register `selOps` leaves its choice in. -/
def selOut (cand : ℕ → Reg) (n pb : ℕ) : Reg := if n ≤ 1 then cand 0 else pb + (n - 2)

/-- `cellOps` over `nc` coordinates (width `nc + 3`). -/
def gCellOps (nc : ℕ) (one g h kp : Reg) (cell acc pw b : ℕ) : List Op :=
  prodKOps ((List.range nc).map fun v => if cell.testBit v then g + v else h + v) one b ++
    ([.mulKF (b + (nc - 1)) pw, .addK acc (b + nc), .mulF pw kp] : List Op)

def gCellsOps (nc : ℕ) (one g h kp : Reg) : List ℕ → Reg → Reg → ℕ → List Op
  | [], _, _, _ => []
  | c :: cs, acc, pw, b =>
    gCellOps nc one g h kp c acc pw b ++ gCellsOps nc one g h kp cs (b + (nc + 1)) (b + (nc + 2)) (b + (nc + 3))

def gCellsAcc (nc : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], acc, _ => acc
  | _ :: cs, _, b => gCellsAcc nc cs (b + (nc + 1)) (b + (nc + 3))

/-- **One cell by kind table** (width `2 nc + 3`; revision 4.3): per coordinate `v`, `ρ_v` or
`1 + ρ_v` by the kind's cell bit (`keep`), their product, then `gCellOps`' tail. -/
def gCellOpsK (nc : ℕ) (one g h kp : Reg) (cell : KC ℕ) (acc pw b : ℕ) : List Op :=
  ((List.range nc).map (fun v => .keep (fun κ => (cell κ).testBit v) (g + v) (h + v)) : List Op) ++
    prodKOps ((List.range nc).map (b + ·)) one (b + nc) ++
    ([.mulKF (b + nc + (nc - 1)) pw, .addK acc (b + 2 * nc), .mulF pw kp] : List Op)

/-- `n` cells by kind table from cell `j` (`cells j κ`: the kind's cell `j`). -/
def gCellsOpsK (nc : ℕ) (one g h kp : Reg) (cells : ℕ → KC ℕ) : ℕ → ℕ → Reg → Reg → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, j, acc, pw, b => gCellOpsK nc one g h kp (cells j) acc pw b ++
      gCellsOpsK nc one g h kp cells n (j + 1) (b + (2 * nc + 1)) (b + (2 * nc + 2)) (b + (2 * nc + 3))

def gCellsAccK (nc : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, acc, _ => acc
  | n + 1, _, b => gCellsAccK nc n (b + (2 * nc + 1)) (b + (2 * nc + 3))

def gLvOps (S : Seq) (fi : FinIn) (k : ℕ) (one cu T W b : Reg) : List Op :=
  let ys := ysOf fi (k - 1)
  let a := b + 2 + 4 * ys.length
  ([.packF (kcOf fi (k - 1)), .eqTable b] : List Op) ++
    ((List.range ys.length).map (fun q => .tensorW (ys.getD q 0 - 3) T) : List Op) ++
    accOps (b + 1) (tRegs fi (k - 1) b) 0 W (b + 2 + ys.length) ++
    ([.mulK ((gSRegs S fi k).headD 0) cu, .addK one a,
     .mulK (a + 1) (accOut W (b + 2 + ys.length) (tRegs fi (k - 1) b))] : List Op)

def gLvsOps (S : Seq) (fi : FinIn) (one cu Ts : Reg) : List ℕ → Reg → ℕ → List Op
  | [], _, _ => []
  | k :: ks, W, b => gLvOps S fi k one cu (Ts + (k - 1)) W b ++
      gLvsOps S fi one cu Ts ks (b + lvW fi k - 1) (b + lvW fi k)

/-- `Π_{x ∈ sf[μ .. pf)} (1 + x)`: the factors (`k` registers from `pd`), their product. -/
def padOps (one pd μ k : ℕ) (sf : List Reg) : List Op :=
  ((List.range k).map (fun i => .addK one (sf.getD (μ + i) 0)) : List Op) ++
    prodKOps ((List.range (k - 1)).map (pd + 1 + ·)) pd (pd + k)

/-- The register of `padOps`' product (`one` if empty). -/
def padReg (one pd k : ℕ) : ℕ := if k = 0 then one else pd + (2 * k - 2)

/-- The registers of family `m`'s pad chain. -/
def padW (pf m : ℕ) : ℕ := (pf - (m - 25)) + (pf - (m - 25) - 1)

/-- **The pad chains of the families** (`padOps` at `μ = m − 25` for each `m`, from `pd`). -/
def padsOps (one : Reg) (sf : List Reg) (pf : ℕ) : List ℕ → ℕ → List Op
  | [], _ => []
  | m :: ms, pd => padOps one pd (m - 25) (pf - (m - 25)) sf ++ padsOps one sf pf ms (pd + padW pf m)

/-- The product register of family `i`'s pad chain. -/
def padsReg (one : Reg) (pf : ℕ) (ms : List ℕ) (pd i : ℕ) : Reg :=
  padReg one (pd + ((ms.take i).map (padW pf)).sum) (pf - (ms.getD i 0 - 25))

/-- **The kind's final zero tails** (revision 4.3: `FRVIR4.finalOps4`'s, moved after `finPf`'s exports):
for each `m` of `ms`, the final message beyond `2^(m − 25)` K elements, zero if the kind's `m` is `m`. -/
def gTailOps (Q : Kind → FinP) (pf : ℕ) : List ℕ → ℕ → List Op
  | [], _ => []
  | t :: ts, r => ([.piField fFinal (2 ^ (t - 25) * 32) ((2 ^ pf - 2 ^ (t - 25)) * 32),
      .assertZero r (fun κ => decide ((Q κ).kv.m κ = t))] : List Op) ++ gTailOps Q pf ts (r + 1)

def gFinPf (P : FinP) (fi : FinIn) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op × List Reg :=
  let S := P.S; let nc := P.nc; let nf := P.fams.length
  let one := b
  let cu := b + 1
  let z0 := b + 2
  let pts := gPfPts P fi
  let Pp := ptsOut pts (b + 3)
  let pb := b + 3 + ptsW pts
  let sb := pb + 5 * (nf - 1)
  let wb := sb + 5
  let rs1 := coordsR fi "RS1"
  let kp := (outsOf fi "B'").headD 0
  let cb := wb + (2 + 2 * nc)
  let ce := cond P.ck (cb + 1 + (2 * nc + 3) * P.ncell) (cb + 1 + (nc + 3) * (Q .L32).cells.length)
  let lb := ce + 2
  let fb := lb + lvsW fi [1, 2, 3, 4]
  let pd := fb + 2 + 4 * 2 ^ S.pf
  let sf := chals fi "Pf" S.pf
  let pe := pd + (P.fams.map (padW S.pf)).sum
  let sel : ℕ → KC Bool := fun i κ => decide ((Q κ).kv.fsel κ = i)
  let selA : KC Bool := fun κ => (Q κ).kv.selA κ
  let node : KC Bool := fun κ => (Q κ).kv.node κ
  (([.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)] : List Op) ++
   ptsOps one z0 pts (b + 3) ++
   (List.range 5).flatMap (fun s => selOps sel (fun i => pfCand P Pp i s) nf (pb + s * (nf - 1))) ++
   (List.range 5).map (fun s =>
     .keep selA (pfCandA P Pp s) (selOut (fun i => pfCand P Pp i s) nf (pb + s * (nf - 1)))) ++
   ([.packF ((List.range 7).map fun p => rs1.getD p 0),
    .rsWeight wb (fun κ => ((Q κ).kv.ptIx κ).map Pp) (rs1.getD 7 0) ((outsOf fi "L3β").headD 0)
      node (sb + 4)] : List Op) ++
   ((List.range nc).map (fun v => .getK (sb + 4) v) : List Op) ++
   ((List.range nc).map (fun v => .addK one (wb + 2 + v)) : List Op) ++
   ([.mulF kp kp] : List Op) ++
   cond P.ck (gCellsOpsK nc one (wb + 2) (wb + (nc + 2)) kp (fun j κ => ((Q κ).cells).getD j 0) P.ncell 0
       z0 cb (cb + 1))
     (gCellsOps nc one (wb + 2) (wb + (nc + 2)) kp (Q .L32).cells z0 cb (cb + 1)) ++
   ([.keep node (cond P.ck (gCellsAccK nc P.ncell z0 (cb + 1)) (gCellsAcc nc (Q .L32).cells z0 (cb + 1))) z0,
    .addK (wb + 1) ce] : List Op) ++
   gLvsOps S fi one cu sb [1, 2, 3, 4] (ce + 1) lb ++
   ([.packK sf, .eqTableK fb] : List Op) ++ fhOps (fb + 1) (List.range (2 ^ S.pf)) z0 (fb + 2) ++
   padsOps one sf S.pf P.fams pd ++
   selOps sel (padsReg one S.pf P.fams pd) nf pe ++
   ([.keep selA one (selOut (padsReg one S.pf P.fams pd) nf pe),
    .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) lb) (pe + (nf - 1)),
    .mulK (pe + nf) (fhOut (List.range (2 ^ S.pf)) z0 (fb + 2)),
    .assertEq (pe + nf + 1) (claimN fi "Pf") allK] : List Op) ++
   gTailOps Q S.pf P.tails (pe + nf + 2), [])

/-! ## The revision-4.3 generators ask nothing -/

theorem noAsk_selOps (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n pb : ℕ) :
    (selOps sel cand n pb).filterMap Op.item? = [] := noAsk_map _ _ fun _ => rfl

theorem noAsk_padsOps (one : Reg) (sf : List Reg) (pf : ℕ) :
    ∀ ms pd, (padsOps one sf pf ms pd).filterMap Op.item? = []
  | [], _ => rfl
  | m :: ms, pd => by
    rw [padsOps, List.filterMap_append, padOps, List.filterMap_append, noAsk_prodKOps,
      noAsk_map _ _ fun _ => rfl, noAsk_padsOps one sf pf ms]; rfl

theorem noAsk_gCellsOpsK (nc : ℕ) (one g h kp : Reg) (cells : ℕ → KC ℕ) :
    ∀ n j acc pw b, (gCellsOpsK nc one g h kp cells n j acc pw b).filterMap Op.item? = []
  | 0, _, _, _, _ => rfl
  | n + 1, j, acc, pw, b => by
    rw [gCellsOpsK, gCellOpsK, List.filterMap_append, List.filterMap_append, List.filterMap_append,
      noAsk_map _ _ fun _ => rfl, noAsk_prodKOps, noAsk_gCellsOpsK nc one g h kp cells n]; rfl

theorem noAsk_gTailOps (Q : Kind → FinP) (pf : ℕ) : ∀ ts r, (gTailOps Q pf ts r).filterMap Op.item? = []
  | [], _ => rfl
  | t :: ts, r => by rw [gTailOps, List.filterMap_append, noAsk_gTailOps Q pf ts]; rfl

/-! ## `finalsOf` -/

/-- **The finals over `P`** (the counts) **and `Q`** (the per-kind data of each index; a fixed kind's
own by default). -/
def finalsOf (P : FinP) (Q : Kind → FinP := fun _ => P) : Finals :=
  ⟨fun fi b => gFinRS P fi b Q, fun fi b => gFinZ P fi b Q, fun fi b => gFinLc P fi b Q,
    fun fi b => gFinSh P fi b Q, fun fi b => gFinLr P fi b Q, fun fi b => gFinE P fi b Q,
    fun fi b => gFinB' P fi b Q, gFinP P, fun fi b => gFinPf P fi b Q⟩

/-! ## At `seq3`: today's finals -/

theorem phaseOffOf_seq3 (n f : ℕ) : phaseOffOf seq3 n f = phaseOff n f := by
  have h : seq3.lv = lvlStar := by rw [seq3_eq]; rfl
  rw [phaseOffOf, ← phasesOf_seq3, ← List.map_take, List.map_map, h, phaseOff]
  exact congrArg List.sum (List.map_congr_left fun p _ => p.shape.bytesToL_toSh f)

theorem fin3P_S : fin3P.S = ⟨32, 19, 26, 28, 15, 21, 23, 7, 32, 6, false, 7⟩ := seq3_eq

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
  rfl

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
  simp only [gFinPf, finPf, selOps, selOut, padsReg, pfCand, pfCandA]
  simp only [gPfPts_3, show (fin3P).S = seq3 from rfl, show (fin3P).nc = 23 from rfl,
    show (fin3P).cells = pfCells from rfl, show (fin3P).fams = [30] from rfl,
    show (fin3P).e4s = [23] from rfl, show (fin3P).ck = false from rfl, show (fin3P).tails = [] from rfl,
    Bool.cond_false, gCellsOps_23, gCellsAcc_23, gLvsOps_3, show (fin3P).kv = kv3 from rfl]
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.take_zero, List.getD_cons_zero, List.range_succ, List.range_zero, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, seq3_eq, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, kv3, ite_true, ite_false, List.append_assoc,
    List.cons_append, Nat.add_zero, Nat.zero_add, le_refl, padReg, padW, gTailOps, Nat.reduceEqDiff]
  rfl

/-- **The generalised finals at 3.x's sequence and kinds are today's finals** (field by field). -/
theorem finalsOf_seq3 : finalsOf fin3P = sfFinals finP finPf := by
  simp only [finalsOf, sfFinals, s0Finals, gFinZ_3, gFinLc_3, gFinSh_3, gFinLr_3, gFinRS_3, gFinE_3,
    gFinB'_3, gFinP_3, gFinPf_3]

/-! ## Relocation to `S`'s format -/

/-- **`reloc S`**: a proof read at field `f < 19`, offset `o` becomes the absolute read
`fieldOffOf S f + o` (field `0`, offset `0`: `absOff 0 x = x`). The bound stays 3.x's `19` (fields
`0 … 17` and `fD`): field 19 (`fA`) has no 3.x offset, so relocating it would break
`evalOp_reloc_seq3`; the cap check's reads of `fA` (and the positions' of `fD`) are absolute
already (`macAOps`, `FRVIR4.dOff4`; PB-m1's honest-proof failure does not arise). -/
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

/-! ## The batched cap check (revision 4.4.1, PACK-4.4 §11, B2 (β′))

The positions no longer compare their path's root with the cap entry at the witness index
`k = j >>> sib` (3.x's dynamic `piDigestAt; assertEq`). Instead each position asserts its root equal
to its **committed** path digest `D_r` (a static read of field `fD`, `FRVIR4.posOps4`), and after
`Pf` the phases `CapD` (absorb `D`), `CapZeta` (squeeze `ζ`), `CapChk` (absorb `A`, field `fA`;
`A_k` meant to be `Σ_{r : offᵢ + k_r = k} ζ^r`) and `CapChkZ` (squeeze `z`) run. With the reads
`r = 0 … 870` in item order (`k_r` the cap index, `offᵢ` its level's first entry), the finals check

* (I) `Σ_r ζ^r·D_r = Σ_k A_k·cap[k]`, one identity per F half of a digest;
* (II) `Σ_r ζ^r·z^{offᵢ + k_r} = Σ_k A_k·z^k`.

Every summand is in the chain before the challenge it is multiplied by (`D`, the caps and the `k_r`
before `ζ`; `A` before `z`): that is what A2′'s form, with `ζ` from `P3.4` and the uncommitted
roots, lacked (A3′'s attack).

**Interim form** (track A2″): existing ops, in five **regular op families**, one per future keyed
template (PACK-4.4 §11.7, track B2′), each a run of equal-width blocks at a constant stride:

1. the head: the constants `1`, `0`, `ζ`, `z`, the squarings `z^{2^t}` (`tplSqChain`), the level
   weights `z^{offᵢ}`;
2. the power chains `ζ^r` (`r < 871`) and `z^k` (`k < 1,536`): one `mulK` each (`tplPowChain`);
3. per read, the bit power `z^{offᵢ}·Π_{t < capMax} (bit t of k_r ? z^{2^t} : 1)`: width `3·capMax`,
   the same for every read and level (`tplBitPow`);
4. per read, the MACs `ζ^r·D_r` (two F halves) and `ζ^r·z^{offᵢ + k_r}` into the running sums:
   width 8 (`tplMacD`);
5. per cap entry, the MACs `A_k·cap[k]` and `A_k·z^k`: width 9 (`tplMacA`);

then the three `assertEq`. No register before the cap check moves: its ops follow every other
final. The π reads are absolute (field `0`; `reloc` keeps them). -/

/-- The largest cap depth (`seq4`: 9): `z^{2^t}` is needed for `t ≤ capMax`. -/
def capMax (S : Seq) : ℕ := ((List.range nLevels).map fun i => (S.lv i).cap).foldr Nat.max 0

/-- **A power chain** (`tplPowChain`): `g^1 … g^n` at registers `pb … pb + n − 1`, each one `mulK`
(`powReg`). -/
def powChainOps (one g : Reg) (n pb : ℕ) : List Op :=
  (List.range n).map fun r => Op.mulK (if r = 0 then one else pb + r - 1) g

/-- Register of `g^r` in `powChainOps one g _ pb` (`g^0` is `one`). -/
def powReg (one pb r : ℕ) : Reg := if r = 0 then one else pb + r - 1

/-- A read: its committed path digest `D_r`, its cap index, its level's weight `z^{offᵢ}`. -/
structure CapRead where
  d : Reg
  k : Reg
  w : Reg

/-- **The bit power of one read** (`tplBitPow`; registers from `c`, width `3·nb`): per bit `t < nb`
of `k`, the bit, `z^{2^t}` or `1`, the running product from `w`. Output `c + 3·nb − 1`. (Constructors
written out: the dot forms cost seconds of elaboration here.) -/
def bitPowOps (one : Reg) (zp : ℕ → Reg) (nb : ℕ) (rd : CapRead) (c : ℕ) : List Op :=
  (List.range nb).flatMap fun t =>
    [Op.bitOf rd.k t, Op.selectHalf (c + 3 * t) one (zp t),
     Op.mulK (if t = 0 then rd.w else c + 3 * t - 1) (c + 3 * t + 1)]

/-- **The MACs of one read** (`tplMacD`; registers from `c`, width 8): split `D_r`, add `ζ^r·lo`,
`ζ^r·hi`, `ζ^r·zk` to the sums `aL`, `aH`, `aZ`. Outputs `aL` at `c + 3`, `aH` at `c + 5`, `aZ` at
`c + 7`. -/
def macDOps (rd : CapRead) (p zk aL aH aZ c : ℕ) : List Op :=
  [Op.splitDigest rd.d, Op.mulKF p c, Op.addK aL (c + 2), Op.mulKF p (c + 1), Op.addK aH (c + 4),
   Op.mulK p zk, Op.addK aZ (c + 6)]

/-- **The MACs of one cap entry `k`** (`tplMacA`; registers from `c`, width 9): `A_k` (absolute
`aO + 32k`), the entry's two F halves (absolute `cO + 32k`, `+ 16`), `A_k·cap[k]` into `sL`/`sH`,
`A_k·z^k` into `sZ`. Outputs `sL` at `c + 4`, `sH` at `c + 6`, `sZ` at `c + 8`. -/
def macAOps (aO cO : ℕ) (k zk sL sH sZ c : ℕ) : List Op :=
  [Op.piElemK 0 (aO + 32 * k), Op.piElem 0 (cO + 32 * k), Op.piElem 0 (cO + 32 * k + 16),
   Op.mulKF c (c + 1), Op.addK sL (c + 3), Op.mulKF c (c + 2), Op.addK sH (c + 5), Op.mulK c zk,
   Op.addK sZ (c + 7)]

/-- The reads of `S`'s levels, in item order (`FinIn`'s column folds `y`: `FRVIR4.dOfY`/`kOfY`),
level `i`'s weight register `w i`. -/
def capReads (S : Seq) (fi : FinIn) (w : ℕ → Reg) : List CapRead :=
  (List.range nLevels).flatMap fun i =>
    (ysOf fi i).map fun y => ⟨dOfY (S.lv i).sib y, kOfY (S.lv i).sib y, w i⟩

/-- **`capChkOps S outs b`**: the batched cap check after the other finals (registers from `b`);
empty unless `S.capChk`. Registers: `b` the K constant `1`, `b + 1` `0`, `b + 2` `ζ` (`chK` of
`CapZeta`'s answer), `b + 3 + t` `z^{2^t}` (`t ≤ capMax`; `z` the `chK` of `CapChkZ`'s answer), the
levels' weights `z^{offᵢ}` (`i = 1 … 4`); then the families 2–5 (module doc) and three `assertEq`. -/
def capChkOps (S : Seq) (outs : Array (List Reg)) (b : ℕ) : List Op :=
  if S.capChk then
    let fi : FinIn := ⟨outs, [], #[]⟩
    let nP := (phasesOf S).length
    let zetaA := (fi.outs.getD (nP - 3) []).headD 0 - 1
    let za := (fi.outs.getD (nP - 1) []).headD 0 - 1
    let M := capMax S
    let zp := fun t => b + 3 + t
    let wb := b + 4 + M
    let w := fun i => if i = 0 then b else wb + (i - 1)
    let head : List Op :=
      [Op.const (fun _ => Val.k 1), Op.const (fun _ => Val.k 0), Op.chK zetaA, Op.chK za] ++
      (List.range M).map (fun t => Op.mulK (zp t) (zp t)) ++
      (List.range (nLevels - 1)).map (fun i => Op.mulK (w i) (zp (S.lv i).cap))
    let rds := capReads S fi w
    let R := rds.length
    let E := capEntries S
    let pb := wb + (nLevels - 1)
    let qb := pb + (R - 1)
    let bb := qb + (E - 1)
    let db := bb + 3 * M * R
    let ab := db + 8 * R
    let zr := fun r => bb + 3 * M * r + 3 * M - 1
    let aD := fun r j => if r = 0 then b + 1 else db + 8 * (r - 1) + j
    let aA := fun k j => if k = 0 then b + 1 else ab + 9 * (k - 1) + j
    head ++ powChainOps b (b + 2) (R - 1) pb ++ powChainOps b (b + 3) (E - 1) qb ++
      (rds.zipIdx.flatMap fun x => bitPowOps b zp M x.1 (bb + 3 * M * x.2)) ++
      (rds.zipIdx.flatMap fun x => macDOps x.1 (powReg b pb x.2) (zr x.2) (aD x.2 3) (aD x.2 5)
        (aD x.2 7) (db + 8 * x.2)) ++
      ((List.range E).flatMap fun k => macAOps (fieldOffOf S fA) (fieldOffOf S fCaps) k (powReg b qb k)
        (aA k 4) (aA k 6) (aA k 8) (ab + 9 * k)) ++
      [Op.assertEq (aD R 3) (aA E 4) allK, Op.assertEq (aD R 5) (aA E 6) allK,
        Op.assertEq (aD R 7) (aA E 8) allK]
  else []

/-- **The cap check asks nothing** (its four items are the skeleton's `CapD` … `CapChkZ`). -/
theorem noAsk_capChkOps (S : Seq) (outs : Array (List Reg)) (b : ℕ) :
    (capChkOps S outs b).filterMap Op.item? = [] := by
  unfold capChkOps
  split
  · simp [powChainOps, bitPowOps, macDOps, macAOps, List.filterMap_flatMap, List.filterMap_cons,
      Op.item?, List.filterMap_eq_nil_iff]
  · rfl

/-- (−) **No cap check without the flag**: 3.x's sequence gets none. -/
theorem capChkOps_off (outs : Array (List Reg)) (b : ℕ) : capChkOps seq3 outs b = [] := by
  rw [capChkOps, seq3_eq]; rfl

/-- (+) **The cap check's head at `seq4`**: the constants `1`, `0`, then `ζ` and `z` as K elements
(`chK`), then `z^{2^t}` for `t ≤ 9` (`capMax seq4 = 9`). -/
theorem capChkOps_head (outs : Array (List Reg)) (b : ℕ) : capMax seq4 = 9 ∧
    ((capChkOps seq4 outs b).take 4).map Op.outs = [1, 1, 1, 1] := by
  refine ⟨by rw [seq4_eq]; decide, ?_⟩
  rw [capChkOps, if_pos (by rw [seq4_eq])]
  rfl

/-- **The relocated finals** (`FRVIR4.gen4`'s `fin`; a group program's with `Q`); revision 4.4.1:
then the cap check. -/
def finOps4 (P : FinP) (outs : Array (List Reg)) (b : ℕ) (Q : Kind → FinP := fun _ => P) : List Op :=
  ((finalsOf P Q).ops outs b ++ capChkOps P.S outs (b + opsOut ((finalsOf P Q).ops outs b))).map
    (reloc P.S)

/-- **At 3.x's parameters the relocated finals run exactly as today's.** -/
theorem finOps4_seq3 (impl : OpImpl) (κ : Kind) (inp : Input) (outs : Array (List Reg)) (b : ℕ)
    (s : St) (tr : Trace) :
    exec impl κ inp (finOps4 fin3P outs b) s tr = exec impl κ inp ((sfFinals finP finPf).ops outs b) s tr := by
  have h : capChkOps fin3P.S outs (b + opsOut ((finalsOf fin3P).ops outs b)) = [] := capChkOps_off _ _
  show exec impl κ inp (((finalsOf fin3P).ops outs b ++ _).map (reloc seq3)) s tr = _
  rw [h, List.append_nil, exec_reloc_seq3, finalsOf_seq3]

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
