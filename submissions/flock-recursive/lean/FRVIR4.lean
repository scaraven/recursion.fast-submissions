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
  node tag, zero bytes 65–127 and `hdr.pub = vk`.
* **Final message**: zero beyond the kind's `2^(m − 25)` K elements.

The **phase-final checks** are the parameter `fin : FinOps`. The 3.x finals (`FRVIRFinals*`)
hard-code 3.x sizes (`τ` of 18, `"S2" 28`, `"Z3" 26`, `32 − κ.m`), so the 4.0 programs need
finals generalised over `Seq` (S-0′ RESULT, "For S-E12′"); and the variable last block of a
segment needs `finSh`'s `bnd` from the statement and the target's free blocks (S-C).
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

/-- The statement's checks (`stmt` at absolute offset `so`; `msg` its register). -/
def stmtOps4 (p : KindP) (so msg b : ℕ) : List Op :=
  [.hashStmt msg, .input 1, .assertEq b (b + 1) allK,
   .piField 0 so 1, .const (fun _ => .b (bytesOf [if p.d.node then RecursionFast.tagNode else tagLeaf])),
   .assertEq (b + 2) (b + 3) allK] ++
  (if p.d.node then
    [.piField 0 (so + 65) 63, .assertZero (b + 4) allK, .piDigest 0 16, .input 0,
     .assertEq (b + 5) (b + 6) allK]
   else [.piField 0 (so + 41) 87, .assertZero (b + 4) allK])

/-- The final message is zero beyond the kind's `2^(m − 25)` K elements. -/
def finalOps4 (S : Seq) (p : KindP) (fo b : ℕ) : List Op :=
  [.piField 0 (fo + 2 ^ (p.d.m - 25) * 32) ((2 ^ S.pf - 2 ^ (p.d.m - 25)) * 32), .assertZero b allK]

/-- The Merkle steps of one position (3.x's `merkleOps`, the kind's depth a constant). -/
def merkleOps4 (sib : ℕ) (i : ℕ) (j : Reg) : ℕ → ℕ → Reg → ℕ → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, h, cur, so, b =>
    let act : KC Bool := fun _ => decide (h < sib)
    [.piDigest 0 so, .bitOf j h, .selectHalf (b + 1) cur b, .selectHalf (b + 1) b cur,
     .askNode i h (b + 2) (b + 3) act, .keep act (b + 4) cur,
     .assertZero b (fun κ => !act κ)] ++ merkleOps4 sib i j n (h + 1) (b + 5) (so + 32) (b + 6)

/-- One position `p` of level `i` (3.x's `posOps`; absolute offsets `co`, `so`, `cap`). -/
def posOps4 (S : Seq) (k : KindP) (i co so capO : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) : List Op :=
  let L := S.lv i
  let K := S.lvK k.d.m i
  let cur := b + 4 + 6 * L.sib - 1
  [.idx (fun _ => ans.getD (p / K.per) 0) (fun _ => K.logN) (fun _ => p % K.per),
   .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (b + 1), .dotKF w (b + 1)] ++
  merkleOps4 K.sib i b L.sib 0 (b + 2) (so + p * L.sib * 32) (b + 4) ++
  [.shrN b (fun _ => K.sib), .piDigestAt 0 capO (b + 4 + 6 * L.sib),
   .assertEq (if L.sib = 0 then b + 2 else cur) (b + 4 + 6 * L.sib + 1) allK]

/-- The width of one position of level `i` in `S`. -/
def posW4 (S : Seq) (i : ℕ) : ℕ := 4 + 6 * (S.lv i).sib + 2

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
    if f = fStmt then rec_ (absorbOps 0 (o f) len c.st b ++ stmtOps4 p (o f) b (b + 2)) (b + 1) [b]
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
    let (ops, c') := rec_ (uniOps 0 (o f) c.st c.pt b) (b + 2) [b + 3, b + 133, b + 134]
    (ops, { c' with uni := b + 133 })
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
      posOps4 S p i (o fCols) (o fSibs) (fieldOffOf S fCaps + capOff4 S i) c.posAns (b + 1) q
        (b + 2 + posW4 S i * q)
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

/-- The programs of the segment and node kinds (one sequence, `seq4`). -/
def genSeg (κ : SegKind) (fin : FinOps) : VProg := gen4 seq4 (.ofSeg κ) fin
def genNode (κ : NodeKind) (fin : FinOps) : VProg := gen4 seq4 (.ofNode κ) fin

/-- The segment format's field offsets are 3.x's (A.3), the node format's are not. -/
theorem fieldOffs : (List.range 19).map (fieldOffOf seq3) = (List.range 19).map fieldOff ∧
    fieldOffOf seq4 fCols ≠ fieldOff fCols := by
  rw [seq3_eq, seq4_eq]; decide +kernel

end Rev4
end FR
