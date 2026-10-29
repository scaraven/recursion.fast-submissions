-- New for `flock-recursive` (track REPF; C1b-RESULT §5.3): the definitions the node's replay rows
-- need, below `FRNodeRows4`, so that `nodeIRows4` folds them (definitions only, moved verbatim).
import FRVIR4Mux
import FRVIRTplFast
import FRVIRTplSet
import FRNodeKinds4
import FRNodeRows4Hint
import FRVIRTplKMux
import FRVIRTplRepLW
import FRVIRTplRepLD
import FRVIRTplRepT
import FRNodeRows4RepRs

/-!
# The prototypes and the replay templates, definitions only

`nodeIRows4` (`FRNodeRows4`) folds the previous node's replay rows (`repIRowsW rtC1c`), whose
definitions lived in modules above `FRNodeRows4` (they import the soundness chain). This module holds
those definitions, moved verbatim with their names and namespaces, so `FRNodeRows4` can name them:

* from `FRNodeRows4`: the moves (`mapC`, `rowMapC`, `mvC`), the slot cells (`selIx`, `oneR`, `selR`,
  `baseR`), the prototypes (`protoP`, `isPrevSlot`, `protoOf`, `protoProg`, `protoLay`, `protoF`,
  `nodeOf`, `maskQ`, `protoR`);
* from `FRNodeRows4Rep*` and `FRNodeRows4RepRsK`, `FRNodeRows4RepLT`: the replay templates (`RT`,
  `repRowsX`, `RT.orElse`, `KOp`, `kRows`, `rtK`, `rtST0`, `kLW`, `rtLinkSegW`, `kRS`, `rtRs`, `kTS`,
  `kEvL`, `rtN0c`, `rtC1c`), the prototype's replay rows `repRowsP` and their place at the node
  (`repB`, `repMapC`, `repRow0`, `repIRowsW`).

The theorems about them stay where they were (those modules import this one through `FRNodeRows4`).
-/

namespace FR
namespace Rev4

-- from `FRNodeRows4`
section
open RecursionFast Circ TEval

/-- A form with its cells mapped. -/
def mapC (f : ℕ → ℕ) (l : Lin) : Lin := l.map fun t => (f t.1, t.2)

/-- A row with its cells mapped. -/
def rowMapC (f : ℕ → ℕ) (r : Row) : Row := ⟨mapC f r.a, mapC f r.b, mapC f r.c⟩

/-- The selector index's offset in a slot's selector cells. -/
def selIx : Kind → ℕ | .L32 => 0 | .P30 => 1 | .N30 => 2

/-- Slot `σ`'s `one` copy (M-relative). -/
def oneR (σ : ℕ) : ℕ := σ * slotM4

/-- Slot `σ`'s selector copies (M-relative). -/
def selR (σ : ℕ) (ι : Kind) : ℕ := σ * slotM4 + 1 + selIx ι

/-- Slot `σ`'s first compiled cell (M-relative). -/
def baseR (σ : ℕ) : ℕ := σ * slotM4 + 4

/-- **Slot `σ`'s selector forms** (M-relative). -/
def protoP (σ : ℕ) : Params := ⟨Lin.cell (oneR σ), fun ι => Lin.cell (selR σ ι)⟩

/-- Whether slot `σ` replays the previous node. -/
def isPrevSlot (κ : NodeKind) (σ : ℕ) : Bool := κ.hasPrev && σ == 0

/-- **Slot `σ`'s prototype**: `0` (the previous-node program) or `1` (the segment program). -/
def protoOf (κ : NodeKind) (σ : ℕ) : ℕ := if isPrevSlot κ σ then 0 else 1

/-- **Prototype `π`'s program**: INT-8's group-uniform programs (blueprint 4.3 route (A)), the
previous-node group with each kind's own public cells `N4c.cells4` (S-E12a: `c_A` from `hashA`;
INT-9: was `progNodeG (cells4 .N4)`, `N4`'s cells at every index), and the segment group. -/
def protoProg (π : ℕ) : VProg := if π = 0 then progNodeGK N4c.cells4 else progSegG

/-- **Prototype `π`'s layout**: `layOf`'s two-pass layout at S-E12b's programs, as constants
(`FRNodeRows4Hint`; S-E12c: the process start then compiles each prototype once). Any layout is
sound (`compileT_sound`); that the rows fit is `ProtoFit`, checked. -/
def protoLay (π : ℕ) : TLay := if π = 0 then hintLay0 else hintLay1

/-- **Prototype `π`'s template set** (S-E12d, revision 4.3 (a)): revision 4.1's (`keys41`: 3.x's
`shiftMask` template left out) for both prototypes; the 4.1 `shiftMask` templates (`.shiftSeg`,
`.maskN`) are in it, and the route `protoR` picks one (S-E12e). -/
def protoF (_π : ℕ) : TFilt := keys41

/-- The node kind selector index `ι` stands for in the previous-node group (`nodeGrp`). -/
def nodeOf : Kind → NodeKind
  | .L32 => .N4
  | .P30 => .N2
  | .N30 => .N8

/-- A node kind's `shiftMask` constants `(nb, chLen₀, chLen₁)` (`NI4.shiftMask4I`'s). -/
def maskQ (ν : NodeKind) : ℕ × ℕ × ℕ := (ν.m - 14, N4c.chLen ν 0, N4c.chLen ν 1)

/-- **Prototype `π`'s `shiftMask` route** (S-E12e): the node's kind-muxed `chainLk4` template over
the group's kinds in selector order (prototype 0), the segment's `shiftSegI` template (prototype 1). -/
def protoR (π : ℕ) : ShR := if π = 0 then .node (Circ.kinds.map fun ι => maskQ (nodeOf ι)) else .seg

/-- A cell or row moved from region `π` to region `σ`. -/
def mvC (π σ c : ℕ) : ℕ := c - π * slotM4 + σ * slotM4

end


end Rev4

namespace Circ

-- from `FRNodeRows4Rep`
section
open RecursionFast

/-- **A replay template**: the ops it covers, and for a compile state, an op and the op's output
slots, the rows that compute the outputs from the operands' slots. -/
structure RT where
  cov : Op → Bool
  rows : Params → CS → Op → List Slot → List Row

/-- The template that covers nothing. -/
def RT.none : RT := ⟨fun _ => false, fun _ _ _ _ => []⟩

/-- **The replay rows along the compile's trail** (the alignment and the step exactly as
`compileFromX`). -/
def repRowsX (X : Ext) (P : Params) (rt : RT) : CS → List Op → List Row
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if rt.cov op then rt.rows P c op (stepOut X P c op).slots else []) ++
      repRowsX X P rt (c.add op (stepOut X P c op)) ops

/-- A form's cells are below `B`. -/
def linLt (B : ℕ) (l : Lin) : Bool := l.all fun t => decide (t.1 < B)

end

end Circ

namespace N4s

-- from `FRNodeRows4Rep`
section
open RecursionFast Rev4 Circ

/-- Prototype `π`'s compiler extension (`protoCS π = compileX (Xof π) …`). -/
def Xof (π : ℕ) : Ext := tplExt4 (protoF π) (protoR π) (protoLay π).ctx

/-- **Prototype `π`'s replay rows** (its frame: M-relative cells of region `π`). -/
def repRowsP (rt : RT) (π : ℕ) : List Row := repRowsX (Xof π) (protoP π) rt (CS.init (baseR π)) (protoProg π).ops

/-- **The replay rows' first row in a slot region** (`23·2^15`: after the prototypes' 730,493 rows
and a 3 % gap, `2^18` rows before the link region). -/
def repBase : ℕ := 23 * 2 ^ 15

end

-- from `FRNodeRows4RepS`
section
open RecursionFast Rev4 Circ

/-- **`one · ℓ = 0` per output cell** of an `af 8` slot; the rejecting row on any other slot. -/
def zeroRows (P : Params) : List Slot → List Row
  | [some (t, ls)] =>
    if t = .af 8 ∧ ls.length = 8 then ls.map fun l => ⟨P.one, l, []⟩ else [⟨P.one, P.one, []⟩]
  | _ => [⟨P.one, P.one, []⟩]

/-- Whether an op is `linkWAll`. -/
def isLinkW : Op → Bool
  | .linkWAll .. => true
  | _ => false

end

-- from `FRNodeRows4RepK`
section
open RecursionFast Rev4 Circ Tpl

/-- **`rt₁` where it covers, else `rt₂`.** -/
def _root_.FR.Circ.RT.orElse (rt₁ rt₂ : RT) : RT :=
  ⟨fun op => rt₁.cov op || rt₂.cov op,
   fun P cs op outs => if rt₁.cov op then rt₁.rows P cs op outs else rt₂.rows P cs op outs⟩

/-- The rejecting row `one · one = 0`. -/
def rejRow (P : Params) : Row := ⟨P.one, P.one, []⟩

/-- The output slots have the types `tys`, each with one form per component. -/
def outsOk : List Ty → List Slot → Bool
  | [], [] => true
  | t :: ts, some (t', ls) :: os => t == t' && ls.length == t.len && outsOk ts os
  | _, _ => false

/-- The output slots' forms, in order. -/
def outF (outs : List Slot) : List Lin := outs.flatMap fun s => match s with
  | some (_, ls) => ls
  | none => []

/-- **The copy rows** `one · out_c = o_c` (`o`: the instantiated template outputs). -/
def copyRows (P : Params) (outs : List Slot) (o : List Lin) : List Row :=
  (outF outs).zipIdx.map fun p => ⟨P.one, p.1, o.getD p.2 []⟩

/-- **The operands' types and forms at index `ι`** (`none` if one has no slot or the wrong number
of forms). -/
def kOps (cs : CS) (ι : Kind) : List ℕ → Option (List Ty × List Lin)
  | [] => some ([], [])
  | a :: as => match cs.slotK a ι, kOps cs ι as with
    | some (t, ls), some (ts, fs) => if ls.length = t.len then some (t :: ts, ls ++ fs) else none
    | _, _ => none

/-- **A kind-muxed op replay**: the op's operand registers at each index, its sub-template per node
kind and operand types, its output types. -/
structure KOp where
  cov : Op → Bool
  args : Op → Kind → List ℕ
  /-- The operand types the sub-templates serve (checked at every index). -/
  inOk : List Ty → Bool
  T : Op → NodeKind → List Ty → Tpl
  tys : List Ty

/-- The selector index of a kind (its position in `Circ.kinds`). -/
def kIx : Kind → ℕ
  | .L32 => 0
  | .P30 => 1
  | .N30 => 2

/-- The three indices' operand blocks, in `Circ.kinds`' order. -/
def kBlocks (K : KOp) (cs : CS) (op : Op) : Option (List (List Ty × List Lin)) :=
  match kOps cs .L32 (K.args op .L32), kOps cs .P30 (K.args op .P30), kOps cs .N30 (K.args op .N30) with
  | some a, some b, some c => some [a, b, c]
  | _, _, _ => none

/-- What sub-template `j` reads as its input `i`: block `j` (widths `ws`); `0` past it. -/
def kSig (ws : List ℕ) (j i : ℕ) : LinT := if i < ws.getD j 0 then I ((ws.take j).sum + i) else []

/-- **The op's kind-muxed template** over the blocks `bs` (inputs: the blocks, then the three
selectors). -/
def kTpl (K : KOp) (op : Op) (bs : List (List Ty × List Lin)) : Tpl :=
  let ws := bs.map fun b => b.2.length
  kmuxT (kSig ws) ws.sum (K.tys.map Ty.len).sum
    [K.T op .N4 (bs.getD 0 ([], [])).1, K.T op .N2 (bs.getD 1 ([], [])).1, K.T op .N8 (bs.getD 2 ([], [])).1]

/-- The instance's input forms: the blocks' forms, then the selectors. -/
def kIns (P : Params) (bs : List (List Ty × List Lin)) : List Lin :=
  (bs.map (·.2)).flatten ++ kinds.map P.sel

/-- `gatesAt` with an accumulator (tail-recursive, REPF): the process start builds templates of up to
150 k gates in a constant's initializer, on the 8 MB thread stack, where `gatesAt` overflows. -/
def gatesAtGo : List Gate → ℕ → List (ℕ × Gate) → List (ℕ × Gate)
  | [], _, acc => acc
  | g :: gs, k, acc => gatesAtGo gs (k + g.nloc) ((k, g) :: acc)

/-- `Tpl.rows` by `gatesAtGo` (`rowsTR_eq`). -/
def rowsTR (T : Tpl) : List RowT := (gatesAtGo T.gates 0 []).reverse.flatMap fun p => p.2.rows p.1

/-- **The replay rows of a kind-muxed op**, its locals from cell `cb`. -/
def kRows (K : KOp) (B cb : ℕ) (P : Params) (cs : CS) (op : Op) (outs : List Slot) : List Row :=
  match kBlocks K cs op with
  | some bs =>
    if outsOk K.tys outs && bs.all (fun b => K.inOk b.1) && (kIns P bs ++ outF outs).all (linLt B) then
      (rowsTR (kTpl K op bs)).map (instRow P.one (kIns P bs) cb) ++
        copyRows P outs ((kTpl K op bs).outs.map (instLin P.one (kIns P bs) cb))
    else [rejRow P]
  | none => [rejRow P]

/-- **The replay template of a kind-muxed op.** -/
def rtK (K : KOp) (B cb : ℕ) : RT := ⟨K.cov, fun P cs op outs => if K.cov op then kRows K B cb P cs op outs else []⟩

/-- A form whose coefficients are all zero (`0` at every assignment). -/
def zeroLin (l : Lin) : Bool := l.all fun t => t.2 == 0

/-- **`bnd`'s two digests are the zero forms at every index** (its first four forms). -/
def bndZ (cs : CS) (bd : ℕ) : Bool :=
  kinds.all fun ι => match cs.slotK bd ι with
    | some (.af _, ls) => (List.range 4).all fun j => zeroLin (ls.getD j [])
    | _ => false

/-- Whether an op is `shiftTarget`. -/
def isST : Op → Bool
  | .shiftTarget .. => true
  | _ => false

/-- `one · out = 0` on the import's cell, if `bnd`'s digests are zero; else the rejecting row. -/
def stOut (B : ℕ) (P : Params) (cs : CS) (bd : ℕ) : List Slot → List Row
  | [some (.f, [o])] => if bndZ cs bd && linLt B o then [⟨P.one, o, []⟩] else [rejRow P]
  | _ => [rejRow P]

/-- The rows of a `shiftTarget` (`stOut`); the rejecting row on any other op. -/
def stRows (B : ℕ) (P : Params) (cs : CS) : Op → List Slot → List Row
  | .shiftTarget _ _ bd _ => stOut B P cs bd
  | _ => fun _ => [rejRow P]

/-- **Prototype 0's `shiftTarget` replay.** -/
def rtST0 (B : ℕ) : RT := ⟨isST, fun P cs op outs => if isST op then stRows B P cs op outs else []⟩

end

-- from `FRNodeRows4RepN`
section
open RecursionFast Rev4 Circ Tpl

/-- Whether an op is `linkWAll`. -/
def isLW : Op → Bool
  | .linkWAll .. => true
  | _ => false

/-- `linkWAll`'s operands (`tt`, `rr`) at every index. -/
def lwArgs : Op → Kind → List ℕ
  | .linkWAll t p, _ => [t, p]
  | _, _ => []

/-- The operand types the template serves: two `AF`s. -/
def lwIn : List Ty → Bool
  | [.af _, .af _] => true
  | _ => false

/-- The sub-template at node kind `ν` (`tplLW` on two `AF`s; eight empty outputs otherwise, which
`lwIn` rejects). -/
def lwT : Op → Rev4.NodeKind → List Ty → Tpl
  | _, ν, [.af a, .af b] => tplLW ν a b
  | _, _, _ => ⟨[], List.replicate nLinkFam []⟩

/-- **`linkWAll`'s kind-muxed replay.** -/
def kLW : KOp := ⟨isLW, lwArgs, lwIn, lwT, [.af nLinkFam]⟩

/-- **S-E14's segment `linkWAll` replay** with its output cells checked below `B`. -/
def rtLinkSegW (B : ℕ) : RT :=
  ⟨isLinkW, fun P _ op outs =>
    if isLinkW op then (if (outF outs).all (linLt B) then zeroRows P outs else [rejRow P]) else []⟩

/-- **The replay frame's bound**: every cell of a prototype's compile is below it (its frame is two
regions, `< 2^21`); the replay templates' locals are above it (`FRNodeRows4RepW.repMapC` puts them
in the spare region). -/
def repB : ℕ := 2 ^ 40

/-- `linkWAll`'s locals (the first block above the frame). -/
def cbLW : ℕ := repB

/-- **Prototype 0's replay templates**: `shiftTarget` (zero) and `linkWAll`. -/
def rtN0 : RT := (rtST0 repB).orElse (rtK kLW repB cbLW)

end

-- from `FRNodeRows4RepW`
section
open RecursionFast Rev4 Circ

/-- **Where a replay cell lives** (slot `v` of a node of kind `κ`): a frame cell where the slot's
assignment reads it; a local (`c ≥ repB`) in the spare region, from cell `κ.vslots·2^20`. -/
def repMapC (κ : Rev4.NodeKind) (v c : ℕ) : ℕ :=
  if c < repB then mvC (protoOf κ v) v c + κ.oneCell else κ.vslots * slotM4 + (c - repB) + κ.oneCell

/-- **A segment slot's replay rows' first row in its region** (REPF): `31·2^15 − 2^10`, the last
`2^10` rows before the link region (`31·2^15`; IMPC2's layout: the template rows and bits below it);
S-E14's `repBase` lies in ASK-T's template-row range `[arR2, arR2 + arR2N)`. Room: `2^10` rows
(prototype 1 has 8). -/
def repSegB : ℕ := 31 * 2 ^ 15 - 2 ^ 10

/-- **Slot `v`'s replay rows' first row**: slot 0 of a node with a previous node (prototype 0) in
the spare region (`κ.vslots·2^20`); a segment slot at `v·2^20 + repSegB`. -/
def repRow0 (κ : Rev4.NodeKind) (v : ℕ) : ℕ := if protoOf κ v = 0 then κ.vslots * slotM4 else v * slotM4 + repSegB

/-- **Slot `v`'s replay rows** (absolute cells: `repMapC`). -/
def repIRowsW (rt : ℕ → RT) (κ : Rev4.NodeKind) (v : ℕ) : List (ℕ × Row) :=
  (repRowsP (rt (protoOf κ v)) (protoOf κ v)).zipIdx.map fun p =>
    (repRow0 κ v + p.2, rowMapC (repMapC κ v) p.1)

end

-- from `FRNodeRows4RepRsK`
section
open RecursionFast Rev4 Circ Tpl

/-- All `AK`: their sizes. -/
def akS : List Ty → Option (List ℕ)
  | [] => some []
  | .ak n :: r => (akS r).map (n :: ·)
  | _ => none

/-- The operand types `af 7, f, f, ak m, ak n₀, …`: `(m, [n₀, …])`. -/
def rsShape : List Ty → Option (ℕ × List ℕ)
  | .af 7 :: .f :: .f :: .ak m :: r => (akS r).map (m, ·)
  | _ => none

/-- `K` inputs `o, o+1, …`: `n` pairs. -/
def kIn (o n : ℕ) : List KF := (List.range n).map fun l => (I (o + 2 * l), I (o + 2 * l + 1))

/-- The claims' inputs from `o`, sizes `ns`. -/
def cIn : ℕ → List ℕ → List (List KF)
  | _, [] => []
  | o, n :: ns => kIn o n :: cIn (o + 2 * n) ns

/-- **The node kind `ν`'s `rsWeight` sub-template.** -/
def rsT (ν : NodeKind) (ts : List Ty) : Tpl :=
  match rsShape ts with
  | some (m, ns) =>
    let g := rsG ν ((List.range 7).map I) (cIn (9 + 2 * m) ns) (I 7) (I 8) (kIn 9 m) 0
    ⟨g.1, [g.2.1, g.2.2]⟩
  | none => ⟨[], [[], []]⟩

/-- An `rsWeight` op active at every index. -/
def isRS : Op → Bool
  | .rsWeight _ _ _ _ act _ => act .L32 && act .P30 && act .N30
  | _ => false

/-- `rsWeight`'s operands at index `ι`: `r″`, `κ`, `β`, `ρ`, then the claims. -/
def rsArgs : Op → Kind → List ℕ
  | .rsWeight r ps κ β _ ρ, ι => [r, κ, β, ρ] ++ ps ι
  | _, _ => []

/-- The operand types the template serves. -/
def rsIn (ts : List Ty) : Bool := (rsShape ts).isSome

/-- **`rsWeight`'s kind-muxed replay.** -/
def kRS : KOp := ⟨isRS, rsArgs, rsIn, fun _ ν ts => rsT ν ts, [.k]⟩

/-- `rsWeight`'s locals: after `linkWAll`'s (42,592 < `2^16`). -/
def cbRS : ℕ := repB + 2 ^ 16

/-- **`rsWeight`'s replay template** (prototype 0). -/
def rtRs : RT := rtK kRS repB cbRS

/-- **Prototype 0's replay templates with `rsWeight`**: C1's `rtN0`, then `rtRs`. -/
def rtN0R : RT := rtN0.orElse rtRs

end

-- from `FRNodeRows4RepLT`
section
open RecursionFast Rev4 Circ Tpl

def isTS : Op → Bool
  | .targetS .. => true
  | _ => false

def tsArgs : Op → Kind → List ℕ
  | .targetS r, _ => [r]
  | _, _ => []

def tsIn : List Ty → Bool
  | [.af _] => true
  | _ => false

def tsTpl : Op → Rev4.NodeKind → List Ty → Tpl
  | _, ν, [.af a] => tplTS ν a
  | _, _, _ => ⟨[], List.replicate 64 []⟩

/-- **`targetS`'s kind-muxed replay.** -/
def kTS : KOp := ⟨isTS, tsArgs, tsIn, tsTpl, [.af 64]⟩

def isEvL : Op → Bool
  | .evalL .. => true
  | _ => false

def evArgs : Op → Kind → List ℕ
  | .evalL t s, _ => [t, s]
  | _, _ => []

def evIn : List Ty → Bool
  | [.af _, .af _] => true
  | _ => false

def evTpl : Op → Rev4.NodeKind → List Ty → Tpl
  | _, ν, [.af a, .af b] => tplEvL ν a b
  | _, _, _ => ⟨[], List.replicate 3 []⟩

/-- **`evalL`'s kind-muxed replay.** -/
def kEvL : KOp := ⟨isEvL, evArgs, evIn, evTpl, [.f, .f, .f]⟩

/-- `targetS`'s locals (`kTS`'s instance): above `linkWAll`'s (from `repB`, 42,592) and R3's
`rsWeight` (from `cbRS = repB + 2^16`, 472,310: up to `repB + 537,846`). -/
def cbTS : ℕ := repB + (2 ^ 19 + 2 ^ 14)

/-- `evalL`'s locals, above `targetS`'s (11.8 k). -/
def cbEvL : ℕ := repB + (2 ^ 19 + 2 ^ 15)

/-- **Prototype 0's replay templates with R3's `rsWeight`** (`rtN0R`): `shiftTarget`, `linkWAll`,
`rsWeight`, `targetS`, `evalL`. -/
def rtN0c : RT := rtN0R.orElse ((rtK kTS repB cbTS).orElse (rtK kEvL repB cbEvL))

/-- **The replay templates per prototype**, all five of prototype 0. -/
def rtC1c (π : ℕ) : RT := if π = 0 then rtN0c else if π = 1 then rtLinkSegW repB else RT.none

end

end N4s
end FR
