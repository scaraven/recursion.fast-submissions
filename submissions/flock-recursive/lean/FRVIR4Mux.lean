-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, §4.3 "The mux", changes 26; stage S-E12b,
-- track L-circ).
import FRVIR4At
import FRVerifierC4
import FRNodeLayout4

/-!
# Revision 4.1's slot programs: the group mux `gen4G` (revision 4.3: uniform groups)

A 4.1 node replays `1 + k` children (B-13): the previous step's node, muxed over `{N2, N4, N8}`,
and `k` segment sub-slots, each muxed over `{L30, L31, L32}` (changes 26, item 5). Each group has
three kinds, so the compiler's three-way selector (`Circ.Params.sel : Kind → Lin`, `muxP`) serves it
unchanged: a **group** `G : Kind → KindP` names the kind each selector index stands for
(`nodeGrp`, `segGrp`), and `gen4G S G fin` is `FRVIR4.gen4` with every kind-dependent datum a table
over the index (`fun ι => … (G ι) …`) instead of a constant.

**Revision 4.3 (route (A)).** The kinds of a group now differ in kind tables only (`FRVIRFinals4`:
the finals read the counts from one `FinP` and the per-kind data of index `ι` from `Q ι`; the final
tail and `hashStmt` are uniform, `FRVIR4`). The group programs are

* `progNodeGK cells = gen4G seq4 nodeGrp (finals of nodeQ cells)`, `nodeQ cells ι` the finals'
  parameters of `nodeAt ι` with its cells `cells (nodeAt ι)`;
* `progSegG = gen4G seq4 segGrp (finals of segQ)`.

**The group program read at `ι` is `gen4 (G ι)`** (`FRVIR4Uni`): op for op (`Op.at`), and so its
run at `ι` is the kind's program's run (`progNodeGK_exec`, `progSegG_exec`).
-/

namespace FR
namespace Rev4
open RecursionFast

/-- **A slot group**: the kind each of the compiler's three selector indices stands for. -/
abbrev Grp := Kind → KindP

/-- The node kind at each selector index (`N4`, `N2`, `N8` at `L32`, `P30`, `N30`). -/
def nodeAt : Kind → NodeKind
  | .L32 => .N4
  | .P30 => .N2
  | .N30 => .N8

/-- The segment kind at each selector index (`L32`, `L30`, `L31` at `L32`, `P30`, `N30`). -/
def segAt : Kind → SegKind
  | .L32 => .L32
  | .P30 => .L30
  | .N30 => .L31

/-- **The previous-node group** `{N4, N2, N8}` at indices `L32, P30, N30`. -/
def nodeGrp : Grp := fun ι => .ofNode (nodeAt ι)

/-- **The segment group** `{L32, L30, L31}` at indices `L32, P30, N30`. -/
def segGrp : Grp := fun ι => .ofSeg (segAt ι)

/-- **A kind table, evaluated once** (its three values computed before the closure is built, so that
an op's table costs a `match`, not a recomputation; `kt_eq`). -/
def kt {α : Type} (f : Kind → α) : Kind → α :=
  let a := f .L32; let b := f .P30; let c := f .N30
  fun ι => match ι with | .L32 => a | .P30 => b | .N30 => c

theorem kt_eq {α : Type} (f : Kind → α) : kt f = f := funext fun ι => by cases ι <;> rfl

/-- The group's representative (index `L32`): its node flag. -/
def Grp.rep (G : Grp) : KindP := G .L32

/-- Seed: `hdr`'s first 16 bytes against the selected kind's constant. -/
def seedOpsG (G : Grp) (b : ℕ) : List Op :=
  [.piField 0 0 48, .askSeed b, .piElem 0 0,
   .const (kt fun ι => .f (F.ofBytes (bytesAt (bytesOf ([(G ι).byte, (G ι).d.m.toUInt8] ++
     List.replicate 46 0)) 0 16))),
   .assertEq (b + 2) (b + 3) allK]

/-- The Merkle steps of one position (`merkleOps4`, the depth per kind). -/
def merkleOpsG (sib : Kind → ℕ) (i : ℕ) (j : Reg) : ℕ → ℕ → Reg → ℕ → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, h, cur, so, b =>
    let act : KC Bool := kt fun ι => decide (h < sib ι)
    [.piDigest 0 so, .bitOf j h, .selectHalf (b + 1) cur b, .selectHalf (b + 1) b cur,
     .askNode i h (b + 2) (b + 3) act, .keep act (b + 4) cur,
     .assertZero b (fun ι => !act ι)] ++ merkleOpsG sib i j n (h + 1) (b + 5) (so + 32) (b + 6)

/-- Z2's `targetS` operand of a segment (`segPtOp`) per kind: one length for the group. -/
def segPtOpG (S : Seq) (G : Grp) (outs : Array (List Reg)) : Op :=
  let st := outs.getD 1 []
  .packFK fun ι => ((outs.getD 3 []).drop 1).take ((G ι).d.m - 13) ++
    List.replicate (S.mStar - (G ι).d.m) (st.getD 1 0) ++ st.drop 2

/-- One position `p` of level `i` (`posOps4`, the kind's ladder per index). -/
def posOpsG (L : Level) (K : Kind → Level) (i co so capO : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) :
    List Op :=
  let cur := b + 4 + 6 * L.sib - 1
  [.idx (kt fun ι => ans.getD (p / (K ι).per) 0) (fun ι => (K ι).logN) (kt fun ι => p % (K ι).per),
   .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (b + 1), .dotKF w (b + 1)] ++
  merkleOpsG (fun ι => (K ι).sib) i b L.sib 0 (b + 2) (so + p * L.sib * 32) (b + 4) ++
  [.shrN b (fun ι => (K ι).sib), .piDigestAt 0 capO (b + 4 + 6 * L.sib),
   .assertEq (if L.sib = 0 then b + 2 else cur) (b + 4 + 6 * L.sib + 1) allK]

/-- **One phase** of the group program (`genPhase4` with the kind tables per index). -/
def genPhaseG (S : Seq) (G : Grp) (n : ℕ) (ph : String × Sh) (c : GCtx) : List Op × GCtx :=
  let p := G.rep
  let b := c.next
  let o := fun f => fieldOffOf S f + phaseOffOf S n f
  let rec_ := fun (ops : List Op) (st : Reg) (out : List Reg) =>
    (ops, { c with next := b + opsOut ops, st := st, outs := c.outs.push out })
  match ph.2 with
  | .seed => rec_ (seedOpsG G b) (b + 1) [b + 1]
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
      let (ops, c') := rec_ (segPtOpG S G c.outs :: uniOps 0 (o f) c.st b (b + 1)) (b + 3)
        [b + 4, b + 134, b + 135]
      (ops, { c' with uni := b + 134 })
  | .rounds f k deg inK =>
    let init := initClaim ph.1
    let (iops, cl) := initOps init 0 (o f) inK c.uni b
    let b' := b + init.width
    let w := if inK then 13 else roundW deg
    let rs := (List.range k).map fun j => b' + w * j + 3
    let real : KC ℕ := kt fun ι => realRounds (G ι) ph.1 k
    let (ops, c') := rec_ (iops ++ roundsOps 0 (o f) deg inK real k 0 c.st cl b')
      (if k = 0 then c.st else b' + w * k - w + 2)
      (cl :: rs ++ [if k = 0 then cl else b' + w * k - 1])
    (ops, if inK then { c' with foldR := rs } else c')
  | .queries i =>
    let L := S.lv i
    let K := kt fun ι => S.lvK (G ι).d.m i
    let co := o fCols; let so := o fSibs; let capO := fieldOffOf S fCaps + capOff4 S i
    let pw := posW4 S i
    let ops := [.packK c.foldR, .eqTableK b] ++ (List.range L.t).flatMap fun q =>
      posOpsG L K i co so capO c.posAns (b + 1) q (b + 2 + pw * q)
    rec_ ops c.st ((List.range L.t).map fun q => b + 2 + pw * q + 3)

/-- The phases from number `n`. -/
def genPhasesG (S : Seq) (G : Grp) : List (String × Sh) → ℕ → GCtx → List Op × GCtx
  | [], _, c => ([], c)
  | ph :: ps, n, c =>
    let r₁ := genPhaseG S G n ph c
    let r₂ := genPhasesG S G ps (n + 1) r₁.2
    (r₁.1 ++ r₂.1, r₂.2)

/-- **The group's skeleton**: every phase, from register `0`. -/
def skeletonG (S : Seq) (G : Grp) : List Op × GCtx :=
  genPhasesG S G (phasesOf S) 0 ⟨0, 0, 0, [], [], 0, #[]⟩

/-- **The group program `gen4G S G fin`**: the skeleton, the phase-final checks, `accept`; in mux
mode (the selector picks the kind). -/
def gen4G (S : Seq) (G : Grp) (fin : FinOps) : VProg :=
  ⟨.mux, (skeletonG S G).1 ++ fin (skeletonG S G).2.outs (skeletonG S G).2.next ++ [.accept]⟩

/-- The field offsets of `S`, once. -/
def fieldOffT (S : Seq) : Array ℕ := ((List.range 19).map (fieldOffOf S)).toArray

theorem fieldOffT_get (S : Seq) {f : ℕ} (hf : f < 19) : (fieldOffT S).getD f 0 = fieldOffOf S f := by
  simp [fieldOffT, Array.getD_eq_getD_getElem?, hf]

/-- **`reloc` by the offset table** (`relocT_eq`). -/
def relocT (_S : Seq) (tab : Array ℕ) : Op → Op
  | .piField f o len => if f < 19 then .piField 0 (tab.getD f 0 + o) len else .piField f o len
  | .piElem f o => if f < 19 then .piElem 0 (tab.getD f 0 + o) else .piElem f o
  | .piElemK f o => if f < 19 then .piElemK 0 (tab.getD f 0 + o) else .piElemK f o
  | .piDigest f o => if f < 19 then .piDigest 0 (tab.getD f 0 + o) else .piDigest f o
  | .piDigestAt f o k => if f < 19 then .piDigestAt 0 (tab.getD f 0 + o) k else .piDigestAt f o k
  | op => op

theorem relocT_eq (S : Seq) : relocT S (fieldOffT S) = reloc S := funext fun op => by
  cases op <;> simp only [relocT, reloc] <;> split_ifs with h <;> first | rfl | simp [fieldOffT_get S h]

/-- **`finOps4` with the table relocation** (`finOps4F_eq`). -/
def finOps4F (P : FinP) (Q : Kind → FinP) : FinOps := fun outs b =>
  let tab := fieldOffT P.S
  ((finalsOf P Q).ops outs b).map (relocT P.S tab)

theorem finOps4F_eq (P : FinP) (Q : Kind → FinP) (outs : Array (List Reg)) (b : ℕ) :
    finOps4F P Q outs b = finOps4 P outs b Q := by
  simp only [finOps4F, finOps4, relocT_eq]

/-- **The node group's finals' parameters** (revision 4.3): index `ι`'s are its kind's, with its
cells (`cells`: each node kind's public cells). -/
def nodeQ (cells : NodeKind → List ℕ) : Kind → FinP := fun ι => nodeFinP (nodeAt ι) (cells (nodeAt ι))

/-- **The segment group's.** -/
def segQ : Kind → FinP := fun ι => segFinP (segAt ι)

/-- **The previous-node slot's program** (`cells`: each node kind's public cells; index `ι` verifies a
child of kind `nodeAt ι` with its cells). The counts are index `L32`'s (every index's: `FRVIR4Uni`). -/
def progNodeGK (cells : NodeKind → List ℕ) : VProg :=
  gen4G seq4 nodeGrp (finOps4F (nodeQ cells .L32) (nodeQ cells))

/-- The previous-node slot's program with one cell list for every kind (revision 4.1's signature;
the slot programs use `progNodeGK` with each kind's cells). -/
def progNodeG (cells : List ℕ) : VProg := progNodeGK fun _ => cells

/-- **A segment sub-slot's program.** -/
def progSegG : VProg := gen4G seq4 segGrp (finOps4F (segQ .L32) segQ)

/-- The slot programs' finals are `finOps4`'s. -/
theorem progG_fin (cells : NodeKind → List ℕ) :
    progNodeGK cells = gen4G seq4 nodeGrp (fun outs b => finOps4 (nodeQ cells .L32) outs b (nodeQ cells)) ∧
      progSegG = gen4G seq4 segGrp (fun outs b => finOps4 (segQ .L32) outs b segQ) := by
  simp only [progNodeGK, progSegG, ← finOps4F_eq]; exact ⟨trivial, trivial⟩

/-! ## Controls -/

/-- (+) The groups: the representative's kinds, and a smaller `m` at another index. -/
theorem grp_ctl : nodeGrp.rep = .ofNode .N4 ∧ segGrp.rep = .ofSeg .L32 ∧
    (nodeGrp .P30).d.m = 31 ∧ (segGrp .N30).d.m = 31 := ⟨rfl, rfl, rfl, rfl⟩

/-- (+) The seed constant reads the selected kind's byte: `N2`'s at index `P30`; (−) the indices
name distinct kinds. -/
theorem grp_bytes : (nodeGrp .P30).byte = 0x4D ∧ (nodeGrp .L32).byte ≠ (nodeGrp .P30).byte ∧
    (segGrp .P30).byte = 0x50 ∧ (segGrp .N30).byte ≠ (segGrp .L32).byte := by decide

/-- (+) A segment's Merkle step is active below its kind's depth only: at level 0, step 9 is active
for `L32` and not for `L30` (depth 9 at level 0). -/
theorem merkleOpsG_ctl :
    (fun ι => decide (9 < (seq4.lvK (segGrp ι).d.m 0).sib)) .L32 = true ∧
      (fun ι => decide (9 < (seq4.lvK (segGrp ι).d.m 0).sib)) .P30 = false := by
  decide

end Rev4
end FR
