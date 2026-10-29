-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-7, B-11 … B-13, A.4, A.8; stage S-0′).
import FRShape4
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

/-- One position `p` of level `i` (3.x's `posOps`; absolute offsets `co`, `so`). **Revision 4.4.1**
(PACK-4.4 §3.3, (β)): the position ends with its cap index `k = j >>> sib` (`shrN`); the path's
digest (register `b + 4 + 6·sL − 1`, or the column's `b + 2` at `sL = 0`) is **not** compared with
the cap entry here (3.x's `piDigestAt; assertEq`): the finals' batched cap check `capChkOps`
(`FRVIRFinals4`) reads both registers after the cap check's challenges. -/
def posOps4 (S : Seq) (k : KindP) (i co so : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) : List Op :=
  let L := S.lv i
  let K := S.lvK k.d.m i
  [.idx (fun _ => ans.getD (p / K.per) 0) (fun _ => K.logN) (fun _ => p % K.per),
   .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (b + 1), .dotKF w (b + 1)] ++
  merkleOps4 K.sib i b L.sib 0 (b + 2) (so + p * L.sib * 32) (b + 4) ++
  [.shrN b (fun _ => K.sib)]

/-- The width of one position of level `i` in `S` (revision 4.4.1: the cap index last). -/
def posW4 (S : Seq) (i : ℕ) : ℕ := 4 + 6 * (S.lv i).sib + 1

/-- **A position's path digest**, from its column fold `y` (`= b + 3`): the last Merkle step's
`keep` (`b + 4 + 6·sL − 1`), or the column's answer (`b + 2`) at `sL = 0`. -/
def curOfY (sL y : Reg) : Reg := if sL = 0 then y - 1 else y + 6 * sL

/-- **A position's cap index** `k = j >>> sib` (`shrN`, `b + 4 + 6·sL`), from its column fold `y`. -/
def kOfY (sL y : Reg) : Reg := y + 6 * sL + 1

/-- Level `i`'s cap in the caps field. -/
def capOff4 (S : Seq) (i : ℕ) : ℕ := ((List.range i).map fun i' => 2 ^ (S.lv i').cap * 32).sum

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
    else if f = fLrEnd ∨ f = fEEnd then
      rec_ (absorbOps 0 (o f) len c.st b ++ [.assertZero b (fun _ => !p.d.node)]) (b + 1) [b]
    else rec_ (absorbOps 0 (o f) len c.st b) (b + 1) [b]
  | .squeezes k ch =>
    match ch with
    | .coords =>
      let rs := (List.range (2 * k)).map fun x => b + 3 * (x / 2) + 1 + x % 2
      let (ops, c') := rec_ (sqzCoordOps k c.st b ++ [.packF rs]) (b + 3 * k - 3) ((b + 3 * k) :: rs)
      (ops, { c' with pt := b + 3 * k })
    | .one => rec_ (sqzOps k c.st b ++ [.chF b 0]) (b + k - 1) [b + k]
    | .pos _ =>
      let ans := (List.range k).map (b + ·)
      let (ops, c') := rec_ (sqzOps k c.st b) (b + k - 1) ans
      (ops, { c' with posAns := ans })
  | .uni f =>
    if p.d.node then
      let (ops, c') := rec_ (uniOps 0 (o f) c.st c.pt b) (b + 2) [b + 3, b + 133, b + 134]
      (ops, { c' with uni := b + 133 })
    else
      let (ops, c') := rec_ (segPtOp S p c.outs :: uniOps 0 (o f) c.st b (b + 1)) (b + 3)
        [b + 4, b + 134, b + 135]
      (ops, { c' with uni := b + 134 })
  | .rounds f k deg inK =>
    let init := initClaim ph.1
    let (iops, cl) := initOps init 0 (o f) inK c.uni b
    let b' := b + init.width
    let w := if inK then 13 else roundW deg
    let rs := (List.range k).map fun j => b' + w * j + 3
    let real : KC ℕ := fun _ => realRounds p ph.1 k
    let (ops, c') := rec_ (iops ++ roundsOps 0 (o f) deg inK real k 0 c.st cl b')
      (if k = 0 then c.st else b' + w * k - w + 2)
      (cl :: rs ++ [if k = 0 then cl else b' + w * k - 1])
    (ops, if inK then { c' with foldR := rs } else c')
  | .queries i =>
    let L := S.lv i
    let ops := [.packK c.foldR, .eqTableK b] ++ (List.range L.t).flatMap fun q =>
      posOps4 S p i (o fCols) (o fSibs) c.posAns (b + 1) q (b + 2 + posW4 S i * q)
    rec_ ops c.st ((List.range L.t).map fun q => b + 2 + posW4 S i * q + 3)

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

/-- The programs of the segment and node kinds (one sequence, `seq4`). -/
def genSeg (κ : SegKind) (fin : FinOps) : VProg := gen4 seq4 (.ofSeg κ) fin
def genNode (κ : NodeKind) (fin : FinOps) : VProg := gen4 seq4 (.ofNode κ) fin

/-- `seq3`'s field offsets are 3.x's (A.3); `seq4`'s, which every 4.1 program uses, are not. -/
theorem fieldOffs : (List.range 19).map (fieldOffOf seq3) = (List.range 19).map fieldOff ∧
    fieldOffOf seq4 fCols ≠ fieldOff fCols := by
  rw [seq3_eq, seq4_eq]; decide +kernel

end Rev4
end FR
