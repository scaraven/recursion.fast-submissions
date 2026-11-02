-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-7, B-11 … B-13, A.4, A.8; stage S-0′).
import FRSoundness4Pos
import FRVIR

/-!
# Revision 4.0's verifier programs: the skeleton generator `gen4`

`FRVIR.genPhase` with its two 3.x constants made parameters: the **sequence** `S` (its phase table
`phasesOf S`, its ladder `S.lv`, its field layout `fieldSizeOf S`) and the **kind** `p`
(its dimensions: per-phase real round counts, its ladder `S.lvK p.d.m` for the positions and the
Merkle depths, its header, node or segment). The ops are 3.x's `Op`; a 4.0 program is
**fixed-kind**, so every kind table is a constant (`fun _ => v`), and its mode is `.fixed p.tix`
with `p.tix` the 3.x kind whose `hashStmt` it shares (`.L32`: `leafStmt`; `.N30`: `nodeStmt`).

Differences from 3.x's `genPhase` (each forced by the 4.0 shapes):
* **Addresses** are absolute (`piField 0 (fieldOffOf S f + o)`): `evalOp` resolves fields with
  3.x's offsets, which `seq4`'s format (larger node-phase fields) does not have.
* **Seed**: no `kindSel`/`assertOneHot` (3.x's three kind bytes; a fixed program checks its kind
  through `hdr`'s first 16 bytes, as 3.x does too).
* **Statement** (`stmtOps4`): a segment asserts the leaf tag and zero bytes 41–127, **not**
  `n = 2^(m − 14)`: its length is variable and range-checked by `V_A` (B-12); a node asserts the
  node tag, zero bytes 65–127 and `hdr.pub = vk`. Revision 4.3: the statement's digest is the
  imported `c` (`.input 1`); the fact `stmtOk4` is checked outside the program (`FRVerifierC4`).
* **Final message**: zero beyond the kind's `2^(m − 25)` K elements (`2^(m − 19 − ell0)` at the
  ruling's `ell0 = 6` only: R-4-m3). Revision 4.3: checked at the end of the finals
  (`FRVIRFinals4.gTailOps`); the skeleton reads `m*`'s (empty) tail, the same for every kind.

**Revision 4.3 (route (A)).** Within a group (`FRVIR4Mux.nodeGrp`, `segGrp`) the programs differ in
kind tables only, so the group program read at index `ι` is `gen4 (G ι)` (`FRVIR4At`).

* **The variable last block** (a segment; S-F4): the `stmt` phase also reads `L = n − 1` from the
  statement (`lastOps`, its outputs `b :: lastOuts`), and Z2's `targetS` operand is Z1's point
  zero-padded, then `L` (`segPtOp`), for the segment's masked target (`FRSegTarget4`).

The **phase-final checks** are the parameter `fin : FinOps`: the finals over the sequence
(`FRVIRFinals4.finOps4`; the programs `FRVerifierC4.progSeg`/`progNode`).
-/

namespace FR
namespace Rev4
open RecursionFast

/-- A 4.0 program's kind: the 3.x table index, the dimensions, the kind byte. -/
structure KindP where
  tix : Kind
  d : Dims
  byte : UInt8

def KindP.ofSeg (κ : SegKind) : KindP := ⟨.L32, κ.dims, κ.byte⟩
def KindP.ofNode (κ : NodeKind) : KindP := ⟨.N30, κ.dims, κ.byte⟩

/-- Field `f`'s offset in `S`'s format. -/
def fieldOffOf (S : Seq) (f : ℕ) : ℕ := ((List.range f).map (fieldSizeOf S)).sum

/-- The offset inside field `f` of phase `n`'s first byte. -/
def phaseOffOf (S : Seq) (n f : ℕ) : ℕ :=
  (((phasesOf S).take n).map fun p => p.2.bytesToL S.lv f).sum

/-- The kind's real rounds of a sumcheck phase (dummies after them; P1 and Pf are real for every
kind: the ladders' rows and the final rounds do not depend on `m`). -/
def realRounds (p : KindP) (name : String) (n : ℕ) : ℕ :=
  match name with
  | "Z3" => p.d.seq.z3 | "S2" => p.d.seq.s2 | "Lr2" => p.d.seq.lr | "E2" => p.d.seq.e2
  | "E4" => p.d.seq.e4 | _ => n

/-- Seed: `hdr`, the seed query, `hdr`'s first 16 bytes against the kind's constant. -/
def seedOps4 (p : KindP) (b : ℕ) : List Op :=
  [.piField 0 0 48, .askSeed b, .piElem 0 0,
   .const (fun _ => .f (F.ofBytes (bytesAt (bytesOf ([p.byte, p.d.m.toUInt8] ++ List.replicate 46 0)) 0 16))),
   .assertEq (b + 2) (b + 3) allK]

/-- The statement's checks (`stmt` at absolute offset `so`; `msg` its register). **Revision 4.3**
(S-E12c (c)): the statement's digest is not computed here (`hashStmt` reads the run's kind, which a
group program does not fix): the op is `.input 1`, the digest `c` imported, and the fact
`stmtDigest p.tix stmt = c` (`stmtOk4`) is checked by `FRVerifierC4.VsegC`/`VnodeC` after the run and
carried by the node circuit's slot interface (bound by H's `hashStmt` blocks). -/
def stmtOps4 (p : KindP) (so _msg b : ℕ) : List Op :=
  [.input 1, .input 1, .assertEq b (b + 1) allK,
   .piField 0 so 1, .const (fun _ => .b (bytesOf [if p.d.node then RecursionFast.tagNode else tagLeaf])),
   .assertEq (b + 2) (b + 3) allK] ++
  (if p.d.node then
    [.piField 0 (so + 65) 63, .assertZero (b + 4) allK, .piDigest 0 16, .input 0,
     .assertEq (b + 5) (b + 6) allK]
   else [.piField 0 (so + 41) 87, .assertZero (b + 4) allK])

/-- The final message's zero tail at `m*` (`ell0 = 6`; empty at `seq4`). **Revision 4.3**: one read,
the same for every kind (a group program reads one field); the kind's own tail (zero beyond its
`2^(m − 25)` K elements) is checked at the end of the finals (`FRVIRFinals4.gTailOps`). -/
def finalOps4 (S : Seq) (_p : KindP) (fo b : ℕ) : List Op :=
  [.piField 0 (fo + 2 ^ (S.mStar - 25) * 32) ((2 ^ S.pf - 2 ^ (S.mStar - 25)) * 32), .assertZero b allK]

/-- The Merkle steps of one position (3.x's `merkleOps`, the kind's depth a constant). -/
def merkleOps4 (sib : ℕ) (i : ℕ) (j : Reg) : ℕ → ℕ → Reg → ℕ → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, h, cur, so, b =>
    let act : KC Bool := fun _ => decide (h < sib)
    [.piDigest 0 so, .bitOf j h, .selectHalf (b + 1) cur b, .selectHalf (b + 1) b cur,
     .askNode i h (b + 2) (b + 3) act, .keep act (b + 4) cur,
     .assertZero b (fun κ => !act κ)] ++ merkleOps4 sib i j n (h + 1) (b + 5) (so + 32) (b + 6)

/-- **The variable last block** (a segment, B-12; S-F4). From `stmt`'s `enc64 n` (bytes 33–40 at
absolute offset `so`; bytes 41–127 are asserted zero), registers from `b`: the digest at byte 33
(`b`), `n mod 2^24` (`b + 1`, `idx`), the constants `0` (`b + 2`) and `1` (`b + 3`), then for
`k < 18` `n`'s bit `k` (`bitOf`, `b + 4 + 2k`) as `0`/`1` (`selectHalf`, `b + 5 + 2k`), then the
borrow chain of `L = n − 1`: `L_k = n_k + c_k`, `1 + n_k`, `c_{k+1} = (1 + n_k)·c_k` (registers
`b + 40 + 3k`, `+ 1`, `+ 2`; `c₀ = 1`; characteristic two). 94 registers. -/
def lastOps (so b : ℕ) : List Op :=
  [.piDigest 0 (so + 33), .idx (fun _ => b) (fun _ => 24) (fun _ => 0),
   .const (fun _ => .f 0), .const (fun _ => .f 1)] ++
  (List.range 18).flatMap (fun k => [.bitOf (b + 1) k, .selectHalf (b + 4 + 2 * k) (b + 2) (b + 3)]) ++
  (List.range 18).flatMap (fun k =>
    let c := if k = 0 then b + 3 else b + 42 + 3 * (k - 1)
    [.addF (b + 5 + 2 * k) c, .addF (b + 3) (b + 5 + 2 * k), .mulF (b + 41 + 3 * k) c])

/-- `lastOps`' outputs: the zero register, then `L`'s 18 bits (`stmt`'s outputs from 1). -/
def lastOuts (b : ℕ) : List Reg := (b + 2) :: (List.range 18).map (b + 40 + 3 * ·)

/-- **Z2's `targetS` operand of a segment** (S-F4): Z1's position coordinate and `m − 14` block
coordinates, zero-padded to `m* − 14`, then `L`'s 18 bits (`19 + 18` entries; the segment's
`targetS` scales the chain target by `Σ_{t ≤ L} eq(r_blk, t)`, `FRSegTarget4`). -/
def segPtOp (S : Seq) (p : KindP) (outs : Array (List Reg)) : Op :=
  let st := outs.getD 1 []
  .packF (((outs.getD 3 []).drop 1).take (p.d.m - 13) ++ List.replicate (S.mStar - p.d.m) (st.getD 1 0) ++
    st.drop 2)

/-- **A position's path digest**, from its column fold `y` (`= b + 3`): the last Merkle step's
`keep` (`b + 4 + 6·sL − 1`), or the column's answer (`b + 2`) at `sL = 0`. -/
def curOfY (sL y : Reg) : Reg := if sL = 0 then y - 1 else y + 6 * sL

/-- One position `p` of level `i` (3.x's `posOps`; absolute offsets `co`, `so`, `dO`). **Revision
4.4.1** (PACK-4.4 §11.1, (β′)): the position ends with its cap index `k = j >>> sib` (`shrN`,
register `b + 4 + 6·sL`), then a **static** read of its committed path digest `D_r` (field `fD`,
absolute offset `dO + 32·p`, register `b + 4 + 6·sL + 1`; `D` is absorbed before the cap check's
challenge `ζ`) and `assertEq cur D_r`, `cur` the path's root (register `b + 4 + 6·sL − 1`, or the
column's `b + 2` at `sL = 0`). The cap entry is not read here (3.x's dynamic `piDigestAt`): the
finals' batched cap check `capChkOps` (`FRVIRFinals4`) checks `D` against the caps. -/
def posOps4 (S : Seq) (k : KindP) (i co so dO : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) : List Op :=
  let L := S.lv i
  let K := S.lvK k.d.m i
  [.idx (fun _ => ans.getD (p / K.per) 0) (fun _ => K.logN) (fun _ => p % K.per),
   .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (b + 1), .dotKF w (b + 1)] ++
  merkleOps4 K.sib i b L.sib 0 (b + 2) (so + p * L.sib * 32) (b + 4) ++
  [.shrN b (fun _ => K.sib), .piDigest 0 (dO + 32 * p),
   .assertEq (curOfY L.sib (b + 3)) (b + 4 + 6 * L.sib + 1) allK]

/-- The width of one position of level `i` in `S` (revision 4.4.1: the cap index, then `D_r`). -/
def posW4 (S : Seq) (i : ℕ) : ℕ := 4 + 6 * (S.lv i).sib + 2

/-- **A position's cap index** `k = j >>> sib` (`shrN`, `b + 4 + 6·sL`), from its column fold `y`. -/
def kOfY (sL y : Reg) : Reg := y + 6 * sL + 1

/-- **A position's committed path digest** `D_r` (`piDigest`, `b + 4 + 6·sL + 1`), from its column
fold `y`: the register `posOps4` asserts equal to `curOfY`, and `capChkOps` reads. -/
def dOfY (sL y : Reg) : Reg := y + 6 * sL + 2

/-- **Level `i`'s first committed path digest** (absolute): `D`'s field offset plus 32 bytes per
read of the levels below (PACK-4.4 §11.4 item 4, PB-m4: one offset, no field-relative read). -/
def dOff4 (S : Seq) (i : ℕ) : ℕ := fieldOffOf S fD + 32 * capReadsBelow S i

/-- Level `i`'s cap in the caps field. -/
def capOff4 (S : Seq) (i : ℕ) : ℕ := ((List.range i).map fun i' => 2 ^ (S.lv i').cap * 32).sum

/-! ## Revision `flock-128` (D128 §2.1, §4.1, §5.5): the proof of work, the nonces, derived `c₂`

**Every number is read from I1's table** (`FRSoundness4Pos`, stage I12): a round message's bytes
(`Sh.rbytes`: K 96, F degree 3 `c₀ ‖ c₁ ‖ c₂ ‖ nonce` 64, F degree 2 `c₀ ‖ c₁ ‖ nonce` 48), the absorb
lengths with their nonces (`Seq.nb`), the `N` items (`Seq.nonce`), the squeeze counts (`Seq.sqC`,
`Seq.sqP`), the field offsets (`fNonce` included), the caps' offsets (`FRVIRFinals4.capShift`), E4
end's pad (`Seq.e4end`). The generator emits the `flock-128` format for every F round (its table
flag `pw` holds for every F round of `seq4`, `pw_seq4`), and grinds exactly the phases of the
table's `grinds` (`irGrinds_seq4`). `nonceAbs` names the two absorbs whose segment-only zero check
covers the whole message (`Lrend`, `Eend`): it leaves their nonce (`Seq.nb` bytes) out. -/

/-- **A round message's bytes in the `flock-128` format** (`Sh.rbytes … pw` with the nonce on every F
round): K 96, F degree 3 64, F degree 2 48. -/
def roundBytesD (deg : ℕ) (inK : Bool) : ℕ := Sh.rbytes deg inK !inK

/-- The absorbs whose segment-only zero-assert must leave the appended nonce out (D128 §2.1). -/
def nonceAbs (f : ℕ) : Bool := f = fLrEnd ∨ f = fEEnd

/-- **The round format the generator reads**: every F round with the nonce (`pw`), no K round. -/
def Sh.pwOK : Sh → Bool
  | .rounds _ _ _ inK pw => pw == !inK
  | _ => true

/-- (+) `seq4`'s table has the generator's round format (`pw` on every F round, on no K round). -/
theorem pw_seq4 : (phasesOf seq4).all (fun ph => ph.2.pwOK) = true := by
  rw [seq4_eq]; decide +kernel

/-- The K challenges' phases (the cap check's `ζ`, `z`): not grinded (D128 §0, §3). -/
def kSqueeze (name : String) : Bool := name = "CapZeta" ∨ name = "CapChkZ"

/-- **The proof of work on answer `a`** (D128 §2.1, §5.5; A.8's ops only): `idx a 8 31` is byte 31 of
`a` (`n`, register `b`), `shrN n 0` its copy (`b + 1`), the copy's eight bits (`bitOf`, `b + 2 … b + 9`),
each asserted zero, ungated (`allK`). Ten registers. In the circuit: `idx` and `shrN` untracked, eight
L-bit imports, eight gated rows. The `shrN` bounds the compiler's Merkle look-ahead from this `idx`
(`FRVIRCompile.alignOf`/`stepsAhead`: an `idx` is laid out as a position block up to the next
`shrN`), so that the proof of work is not padded as an 11-step position (64 rows each). -/
def powOps (a b : ℕ) : List Op :=
  .idx (fun _ => a) (fun _ => 8) (fun _ => 31) :: .shrN b (fun _ => 0) ::
    ((List.range 8).map (fun h => Op.bitOf (b + 1) h) ++
      (List.range 8).map (fun h => Op.assertZero (b + 2 + h) allK))

/-- The registers `powOps` appends. -/
def powW : ℕ := 10

/-- **A univariate round** (Z2, D128): 3.x's `uniOps` without the pad's zero-assert (the pad is the
nonce), then the proof of work on its squeeze's answer (`b + 2`). Outputs as 3.x's (`λ` at `b + 3`,
`lagrangeS`'s two values at `b + 133`, `b + 134`); the proof of work's registers from `b + 135`. -/
def uniOps4 (f o st pt b : ℕ) : List Op :=
  uniHead f o st b ++ uniElems f o ++
    [.packF ((List.range 127).map (b + 4 + ·)), .targetS pt, .lagrangeS (b + 131) (b + 3) (b + 132)] ++
    powOps (b + 2) (b + 135)

/-- The width of one F round (D128): degree 3 `27`, degree 2 `23`; a K round `13` (unchanged). -/
def roundW4 (deg : ℕ) (inK : Bool) : ℕ := if inK then 13 else if deg = 3 then 27 else 23

/-- **One sumcheck round over F** (D128 §2.1, §4.1): absorb (`roundBytesD`), squeeze `r` (`b + 3`),
the proof of work on the squeeze's answer (`b + 4 … b + 13`); degree 3: `c₃ := claim + c₁ + c₂`;
**degree 2: `c₂ := claim + c₁`** (the third slot is the nonce; the round's `c₁ + c₂ = claim` holds
by construction, so 3.x's `assertEq` is gone); the next claim `g(r)` (Horner). A dummy round (`real`
fails) keeps the claim and asserts zero **all but the nonce** (`[o, o + 48)` resp. `[o, o + 32)`:
the orchestrator's ruling on the D128 review, finding 1: every kind grinds every round). -/
def roundOpsF4 (f o deg : ℕ) (real : KC Bool) (st claim b : ℕ) : List Op :=
  [.piField f o (roundBytesD deg false), .askAbsorb st b (roundBytesD deg false), .askSqueeze (b + 1),
   .chF (b + 2) 0] ++ powOps (b + 2) (b + 4) ++
  (if deg = 3 then
    [.piElem f o, .piElem f (o + 16), .piElem f (o + 32), .addF (b + 15) (b + 16), .addF claim (b + 17),
     .mulF (b + 3) (b + 18), .addF (b + 16) (b + 19), .mulF (b + 3) (b + 20), .addF (b + 15) (b + 21),
     .mulF (b + 3) (b + 22), .addF (b + 14) (b + 23),
     .piField f o 48, .assertZero (b + 25) (fun κ => !real κ), .keep real (b + 24) claim]
   else
    [.piElem f o, .piElem f (o + 16), .addF claim (b + 15),
     .mulF (b + 3) (b + 16), .addF (b + 15) (b + 17), .mulF (b + 3) (b + 18), .addF (b + 14) (b + 19),
     .piField f o 32, .assertZero (b + 21) (fun κ => !real κ), .keep real (b + 20) claim])

/-- `n` rounds from round `j` (3.x's `roundsOps` with `roundOpsF4`, `roundBytesD`, `roundW4`): the
next state is the squeeze answer `b + 2`, the next claim the round's last register. -/
def roundsOps4 (f o deg : ℕ) (inK : Bool) (real : KC ℕ) : ℕ → ℕ → Reg → Reg → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, j, st, claim, b =>
    let o' := o + j * roundBytesD deg inK
    (if inK then roundOpsK f o' (fun κ => decide (j < real κ)) st claim b
     else roundOpsF4 f o' deg (fun κ => decide (j < real κ)) st claim b) ++
    roundsOps4 f o deg inK real n (j + 1) (b + 2) (b + roundW4 deg inK - 1) (b + roundW4 deg inK)

/-- The number of the (first) phase called `name` in `S`'s table. -/
def ixOf (S : Seq) (name : String) : ℕ := (phasesOf S).findIdx (·.1 = name)

/-- The absolute offset of phase `name`'s bytes in field `f`. -/
def msgOff (S : Seq) (name : String) (f : ℕ) : ℕ := fieldOffOf S f + phaseOffOf S (ixOf S name) f

/-- Phase `name`'s outputs. -/
def outsAt (S : Seq) (outs : Array (List Reg)) (name : String) : List Reg := outs.getD (ixOf S name) []

/-- **L2's initial claim** `â + α b̂` (A.9 `finLc` (i); `Zend`'s message, `L1`'s `α`), registers from
`b`; the claim at `b + 3`. -/
def initL2 (S : Seq) (outs : Array (List Reg)) (b : ℕ) : List Op :=
  let zO := msgOff S "Zend" fZend
  [.piElem 0 zO, .piElem 0 (zO + 16), .mulF ((outsAt S outs "L1").headD 0) (b + 1), .addF b (b + 2)]

/-- **E4's initial claim** `â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L + κ_E⁴ m̂*` (A.9 `finE` (iii″),
`FRVIRFinals4.gFinE0`/`rsvEOps`; `v_L = â_L + κ_L b̂_L + κ_L² ĉ_L`, `finLr` (iii)): `Eend`'s four
values, `Lrend`'s three, `E3`'s `κ_E`, `Lr3`'s `κ_L`; registers from `b`, the claim at `b + 22`. -/
def initE4 (S : Seq) (outs : Array (List Reg)) (b : ℕ) : List Op :=
  let eO := msgOff S "Eend" fEEnd; let lO := msgOff S "Lrend" fLrEnd
  let kE := (outsAt S outs "E3").headD 0; let kL := (outsAt S outs "Lr3").headD 0
  [.piElem 0 eO, .piElem 0 (eO + 16), .piElem 0 (eO + 32), .piElem 0 (eO + 48),
   .piElem 0 lO, .piElem 0 (lO + 16), .piElem 0 (lO + 32),
   .mulF kL (b + 5), .mulF kL kL, .mulF (b + 8) (b + 6), .addF (b + 4) (b + 7), .addF (b + 10) (b + 9),
   .mulF kE (b + 1), .mulF kE kE, .mulF (b + 13) (b + 2), .addF b (b + 12), .addF (b + 15) (b + 14),
   .mulF (b + 13) kE, .mulF (b + 17) (b + 11), .addF (b + 16) (b + 18),
   .mulF (b + 13) (b + 13), .mulF (b + 20) (b + 3), .addF (b + 19) (b + 21)]

/-- **S2's boundary operand** (`FRVIRFinals4.gBndOps`' list at registers `b … b + 6`): a node's zeros
and its last block `1^(m−14) ‖ 0^(m*−m)`, a segment's `s`, `h` halves and `L`'s 18 bits (`stmt`'s
outputs from 2). -/
def bndList (S : Seq) (d : Dims) (stOuts : List Reg) (b : ℕ) : List Reg :=
  if d.node then [b + 4, b + 5, b + 4, b + 5] ++ List.replicate (d.m - 14) (b + 6) ++
    List.replicate (S.mStar - d.m) (b + 4)
  else [b, b + 1, b + 2, b + 3] ++ stOuts.drop 2

/-- S1's block coordinates for `shiftTarget`, padded to `m* − 14` by the zero register `z`
(`FRVIRFinals4.gPadB`). -/
def tauList (S : Seq) (d : Dims) (co : List Reg) (z : Reg) : List Reg :=
  co.take (d.m - 14) ++ List.replicate (S.mStar - d.m) z

/-- **S2's initial claim** `shiftTarget τ θ bnd` (A.9 `finSh` (i), `FRVIRFinals4.gShCore`'s first
eleven ops, same operands), registers from `b`; the claim at `b + 10`. `pk` packs a kind-dependent
list (`packF` in a fixed program, `packFK` in a group program: `FRVIR4Mux`). -/
def initS2 (S : Seq) (outs : Array (List Reg)) (pk : (Dims → List Reg) → Op) (b : ℕ) : List Op :=
  let hO := fieldOffOf S fHdr; let sO := msgOff S "stmt" fStmt
  let co := (outsAt S outs "S1").drop 1; let nb := S.mStar - 14
  [.piElem 0 (hO + 16), .piElem 0 (hO + 32), .piElem 0 (sO + 1), .piElem 0 (sO + 17),
   .const (fun _ => .f 0), .const (fun _ => .f 0), .const (fun _ => .f 1),
   pk fun d => bndList S d (outsAt S outs "stmt") b, pk fun d => tauList S d co (b + 4),
   .packF ((co.drop nb).take 10), .shiftTarget (b + 8) (b + 9) (b + 7) (co.getD (nb + 10) 0)]

/-- **The first claim's ops and its register** (D128; ruling (A) on the free degree-2 claims): K
phases and the `uni`/`zero` claims as 3.x's `initOps`; the free F claims (L2, S2, E4) are **the
verifier's target**, computed here from the earlier phases (3.x read them as `c₁ + c₂` of the first
message, whose third slot is now the nonce; the finals' (i)/(iii) asserts become identities). -/
def initOps4 (S : Seq) (outs : Array (List Reg)) (pk : (Dims → List Reg) → Op) (name : String)
    (f o : ℕ) (inK : Bool) (uni b : ℕ) : List Op × Reg :=
  match initClaim name, inK with
  | .free, false =>
    if name = "L2" then (initL2 S outs b, b + 3)
    else if name = "S2" then (initS2 S outs pk b, b + 10)
    else if name = "E4" then (initE4 S outs b, b + 22)
    else ([.const fun _ => .f 0], b)
  | i, _ => initOps i f o inK uni b

/-- **The phases the generator grinds** (`powOps` after their last squeeze): the univariate round,
every F round, every squeeze phase but the cap check's two K challenges. -/
def irGrinds : String × Sh → Bool
  | (_, .uni _) => true
  | (_, .rounds _ _ _ inK _) => !inK
  | (nm, .squeezes _ _) => !kSqueeze nm
  | _ => false

/-- **The generator grinds exactly the table's grinded phases** at `seq4` (I1's `grinds`, whose last
squeezes are `powPos`: 154 positions). -/
theorem irGrinds_seq4 : (phasesOf seq4).all (fun ph => irGrinds ph == grinds ph) = true := by
  rw [seq4_eq]; decide +kernel

/-- **One phase** (number `n` of `phasesOf S`) of kind `p`: its ops and the next context. -/
def genPhase4 (S : Seq) (p : KindP) (n : ℕ) (ph : String × Sh) (c : GCtx) : List Op × GCtx :=
  let b := c.next
  let o := fun f => fieldOffOf S f + phaseOffOf S n f
  let rec_ := fun (ops : List Op) (st : Reg) (out : List Reg) =>
    (ops, { c with next := b + opsOut ops, st := st, outs := c.outs.push out })
  match ph.2 with
  | .seed => rec_ (seedOps4 p b) (b + 1) [b + 1]
  | .absorb f len =>
    if f = fStmt then
      if p.d.node then rec_ (absorbOps 0 (o f) len c.st b ++ stmtOps4 p (o f) b (b + 2)) (b + 1) [b]
      else
        let b₂ := b + 2 + opsOut (stmtOps4 p (o f) b (b + 2))
        rec_ (absorbOps 0 (o f) len c.st b ++ stmtOps4 p (o f) b (b + 2) ++ lastOps (o f) b₂) (b + 1)
          (b :: lastOuts b₂)
    else if f = fFinal then rec_ (absorbOps 0 (o f) len c.st b ++ finalOps4 S p (o f) (b + 2)) (b + 1) [b]
    else if nonceAbs f then
      rec_ (absorbOps 0 (o f) len c.st b ++
        [.piField 0 (o f) (len - S.nb), .assertZero (b + 2) (fun _ => !p.d.node)]) (b + 1) [b]
    else rec_ (absorbOps 0 (o f) len c.st b) (b + 1) [b]
  | .squeezes k ch =>
    -- D128: the proof of work on the phase's last answer, after the phase's own ops (not for `ζ`, `z`)
    let pw := fun (a e : ℕ) => if kSqueeze ph.1 then [] else powOps a e
    match ch with
    | .coords =>
      let rs := (List.range (2 * k)).map fun x => b + 3 * (x / 2) + 1 + x % 2
      let (ops, c') := rec_ (sqzCoordOps k c.st b ++ [.packF rs] ++ pw (b + 3 * k - 3) (b + 3 * k + 1))
        (b + 3 * k - 3) ((b + 3 * k) :: rs)
      (ops, { c' with pt := b + 3 * k })
    | .one => rec_ (sqzOps k c.st b ++ [.chF b 0] ++ pw (b + k - 1) (b + k + 1)) (b + k - 1) [b + k]
    | .pos _ =>
      let ans := (List.range k).map (b + ·)
      let (ops, c') := rec_ (sqzOps k c.st b ++ pw (b + k - 1) (b + k)) (b + k - 1) ans
      (ops, { c' with posAns := ans })
  | .uni f =>
    if p.d.node then
      let (ops, c') := rec_ (uniOps4 0 (o f) c.st c.pt b) (b + 2) [b + 3, b + 133, b + 134]
      (ops, { c' with uni := b + 133 })
    else
      let (ops, c') := rec_ (segPtOp S p c.outs :: uniOps4 0 (o f) c.st b (b + 1)) (b + 3)
        [b + 4, b + 134, b + 135]
      (ops, { c' with uni := b + 134 })
  | .rounds f k deg inK _ =>
    let (iops, cl) := initOps4 S c.outs (fun l => .packF (l p.d)) ph.1 0 (o f) inK c.uni b
    let b' := b + opsOut iops
    let w := roundW4 deg inK
    let rs := (List.range k).map fun j => b' + w * j + 3
    let real : KC ℕ := fun _ => realRounds p ph.1 k
    let (ops, c') := rec_ (iops ++ roundsOps4 0 (o f) deg inK real k 0 c.st cl b')
      (if k = 0 then c.st else b' + w * k - w + 2)
      (cl :: rs ++ [if k = 0 then cl else b' + w * k - 1])
    (ops, if inK then { c' with foldR := rs } else c')
  | .queries i =>
    -- the offsets once per phase, not per position (INIT: the programs' compile at start-up)
    let L := S.lv i
    let co := o fCols; let so := o fSibs; let dO := dOff4 S i
    let pw := posW4 S i
    let ops := [.packK c.foldR, .eqTableK b] ++ (List.range L.t).flatMap fun q =>
      posOps4 S p i co so dO c.posAns (b + 1) q (b + 2 + pw * q)
    rec_ ops c.st ((List.range L.t).map fun q => b + 2 + pw * q + 3)

/-- The phases from number `n`. -/
def genPhases4 (S : Seq) (p : KindP) : List (String × Sh) → ℕ → GCtx → List Op × GCtx
  | [], _, c => ([], c)
  | ph :: ps, n, c =>
    let r₁ := genPhase4 S p n ph c
    let r₂ := genPhases4 S p ps (n + 1) r₁.2
    (r₁.1 ++ r₂.1, r₂.2)

/-- **The skeleton of kind `p` in sequence `S`**: every phase, from register `0`. -/
def skeleton4 (S : Seq) (p : KindP) : List Op × GCtx :=
  genPhases4 S p (phasesOf S) 0 ⟨0, 0, 0, [], [], 0, #[]⟩

/-- **`gen4 S p fin`**: the skeleton, the phase-final checks `fin`, `accept`. -/
def gen4 (S : Seq) (p : KindP) (fin : FinOps) : VProg :=
  ⟨.fixed p.tix, (skeleton4 S p).1 ++ fin (skeleton4 S p).2.outs (skeleton4 S p).2.next ++ [.accept]⟩

/-- The statement's bytes: `stmt`'s absorb (phase 1, 128 bytes at `fieldOffOf S fStmt + phaseOffOf S 1
fStmt`), the message `stmtOps4`'s `msg` register held. -/
def stmtBytes4 (S : Seq) (π : ByteArray) : ByteArray :=
  π.extract (fieldOffOf S fStmt + phaseOffOf S 1 fStmt) (fieldOffOf S fStmt + phaseOffOf S 1 fStmt + 128)

/-- **The statement fact** (revision 4.3): the statement's digest, for the kind's table index
(`.L32`: `leafStmt`; `.N30`: `nodeStmt`), is `c`. -/
def stmtOk4 (S : Seq) (p : KindP) (inp : Input) : Bool :=
  decide (stmtDigest p.tix (stmtBytes4 S inp.π) = inp.c)

/-- (+) **The committed digests tile `D`**: level 0's first read is `D`'s first byte, and the 871
reads end exactly where `A` begins. -/
theorem dOff4_ctl : dOff4 seq4 0 = fieldOffOf seq4 fD ∧ dOff4 seq4 nLevels = fieldOffOf seq4 fA := by
  rw [dOff4, dOff4, seq4_eq]; decide +kernel

/-- The programs of the segment and node kinds (one sequence, `seq4`). -/
def genSeg (κ : SegKind) (fin : FinOps) : VProg := gen4 seq4 (.ofSeg κ) fin
def genNode (κ : NodeKind) (fin : FinOps) : VProg := gen4 seq4 (.ofNode κ) fin

/-- `seq3`'s field offsets are 3.x's (A.3); `seq4`'s, which every 4.1 program uses, are not. -/
theorem fieldOffs : (List.range 19).map (fieldOffOf seq3) = (List.range 19).map fieldOff ∧
    fieldOffOf seq4 fCols ≠ fieldOff fCols := by
  rw [seq3_eq, seq4_eq]; decide +kernel

end Rev4
end FR
