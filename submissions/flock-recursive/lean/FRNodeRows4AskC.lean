-- New for `flock-recursive` (track SIB): the siblings' generator (`sibTG`) and the closure generator
-- (`TG.close`), below `FRNodeRows4`.
import FRNodeRows4AskB

/-!
# The siblings' rows and the closure generator

* **`sibTG`**: IMPC2's sibling rows (`bitTGR`'s sibling half) with the checks their `ATImp` needs made at
  process start: the node item's place (`sibAt`: phase, level, position, depth, item), and, at every kind
  whose depth is active, that the position bit is the cell the decomposition rows give bit
  `(p mod per)·logN + h` of the position's answer, the answer of the P2 phase just before the queries
  phase (`sibPosOk`). A failed check is a failing row.
* **`TG.close`**: `A` closed: it also covers every op that can be an import or a foreign flag, except
  the asks, the `bitOf`s and the replay ops (`isRep`), and gives a failing row at such an op the compile
  made an import that `A` does not cover, or a foreign flag that no class discharges (`zPinT`,
  `stFlagT`); at the first ask it checks that every `bitOf` is followed by a `selectHalf` on it
  (`bitNxAll`). On the honest compile it gives no row. Its residual (the run facts left) is then the replay ops' imports and the
  `felems` auxiliary cells, by definition (`FRNodeRun4C`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## Siblings -/

/-- The proof's sibling parts (`pSegs`' `fSibs` parts, one per queries phase). -/
def sibSegs : List PSeg := pSegs.filter fun s => s.f == fSibs

/-- **A sibling read's place**: `(phase, level, position, depth, node item)` of the `fSibs` byte `o` (a
32-byte boundary of a queries phase's sibling part, at `seq4`'s ladder). -/
def sibAt (o : ℕ) : Option (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  match sibSegs.find? (fun s => decide (s.st ≤ o ∧ o < s.st + s.len)) with
  | some s =>
    match (phasesA.getD s.n ("", .seed)).2 with
    | .queries i =>
      let sib := (seq4.lv i).sib
      let d := o - s.st
      if d % 32 = 0 ∧ 0 < sib then
        some (s.n, i, d / 32 / sib, d / 32 % sib, phIxA.getD s.n 0 + (1 + sib) * (d / 32 / sib) + 1 + d / 32 % sib)
      else none
    | _ => none
  | none => none

/-- **The position bit under kind `ι`** (queries phase `n`, level `i`, position `p`, depth `h`): where the
depth is active, phase `n − 1` squeezes the level's position answers, and the position cell is the cell
of bit `(p mod per)·logN + h` of answer `p / per` (`ansCell`). -/
def sibPosOk (T : BTab) (n i p h : ℕ) (ι : Kind) : Bool :=
  let K := T.lvl ι i
  if h < K.sib then
    match (phasesA.getD (n - 1) ("", .seed)).2 with
    | .squeezes sq (.pos i') =>
      decide (1 ≤ n ∧ i' = i ∧ p / K.per < sq) &&
        T.ansCell ι (phIxA.getD (n - 1) 0 + p / K.per) ((p % K.per) * K.logN + h) == some (posCell i p h)
    | _ => false
  else true

/-- **A sibling's rows**: per half `c`, `b·(A₁(l_c) − A₁(r_c)) = sib_c − A₁(r_c)` (`b` the position bit,
`l`, `r` the node query's halves on arena₁), and `g·sib_c = 0` at the kinds whose depth `h` is inactive;
a failing row unless the item is the node query, the operand a digest, the item not in the segment's
last block and every kind's position bit placed (`sibPosOk`). -/
def sibRowsS (T : BTab) (P : Params) (π : ℕ) (sl : List Slot) (n i p h k : ℕ) : List Row :=
  match itemsT[k]?, sl with
  | some (.node i' h'), [some (.d, [s₀, s₁])] =>
    if i' = i ∧ h' = h ∧ 1 + offT.getD k 0 + (Item.node i h).slen + 64 ≤ N4c.segB ∧
        kinds.all (sibPosOk T n i p h) then
      let q := qElT k (.node i h)
      let b := Lin.cell (bitC π (posCell i p h))
      let ina : KC Bool := fun ι => decide ((T.lvl ι i).sib ≤ h)
      let pr := fun (s : Lin) (c : ℕ) =>
        (⟨b, subN (Lin.cell (arC π (q + c))) (Lin.cell (arC π (q + 2 + c))),
          subN s (Lin.cell (arC π (q + 2 + c)))⟩ : Row)
      [pr s₀ 0, pr s₁ 1] ++
        (if kinds.any ina then [⟨gateS P ina, s₀, []⟩, ⟨gateS P ina, s₁, []⟩] else [])
    else [failRT P]
  | _, _ => [failRT P]

/-- **The sibling reads** (`piDigest`s `sibAt` places). -/
def sibCov : Op → Bool
  | .piDigest f o => (sibAt (absOff f o)).isSome
  | _ => false

/-- **The siblings' generator** of prototype `π` (extension `X`, the template-free context). -/
def sibTG (X : Ext) (π : ℕ) (T : BTab) : TG :=
  ⟨sibCov, fun P cs _ op _ =>
    match op with
    | .piDigest f o =>
      match sibAt (absOff f o) with
      | some (n, i, p, h, k) => sibRowsS T P π (stepOut X P cs op).slots n i p h k
      | none => []
    | _ => []⟩

/-! ## The closure -/

/-- **The replay ops** (C1/R3/C1b's templates; REPF covers prototype 0's, SEG-R decides prototype 1's):
left to the residual. -/
def isRep : Op → Bool
  | .shiftTarget .. | .linkWAll .. | .rsWeight .. | .targetS .. | .evalL .. | .evalM .. => true
  | _ => false

/-- Whether an op is a `bitOf`. -/
def isBitOf : Op → Bool
  | .bitOf .. => true
  | _ => false

/-- **The ops `opOut` makes imports** (`opImp_eq`). -/
def opImp : Op → Bool
  | .input _ | .piElem .. | .piElemK .. | .piDigest .. | .piDigestAt .. | .askSeed _ | .askAbsorb ..
  | .askSqueeze _ | .askNode .. | .askCol .. | .chF .. | .chK _ | .bitOf .. | .walkAB .. | .phiRS ..
  | .shiftTarget .. | .slotW .. | .kindFoldWeight .. | .eqZ .. | .rsWeight .. | .lagrangeS .. | .targetS ..
  | .tensorW .. | .dotKF .. | .evalM .. | .evalL .. | .hashStmt _ | .eqPt .. | .shiftEq .. | .linkWAll ..
  | .shiftMask .. | .rowW .. | .kindSel => true
  | _ => false

/-- **The ops `opOut` may make foreign** (`forCap_of`). -/
def forCap : Op → Bool
  | .assertEq .. | .assertZero .. | .assertOneHot .. | .assertBit .. | .eqTableK _ | .kindInd _
  | .maskRows .. => true
  | _ => false

/-- `FRNodeRun4BR.bitNx`, below `FRNodeRows4`: a `bitOf` followed by a `selectHalf` on its result. -/
def bitNxT : Op → List Op → ℕ → Bool
  | .bitOf _ _, .selectHalf b _ _ :: _, n => decide (b = n)
  | _, _, _ => false

/-- **Every `bitOf` of `ops` is followed by a `selectHalf` on it** (`n` the register count; tail-recursive). -/
def bitNxAll : ℕ → List Op → Bool
  | _, [] => true
  | n, op :: ops => (!isBitOf op || bitNxT op ops n) && bitNxAll (n + op.nOut) ops

/-- `FRNodeRows4AskIR.zPin`, below `FRNodeRows4`. -/
def zPinT (pv : List (ℕ × ℕ × ℕ × ℕ)) (p : Op × ℕ) : Bool :=
  match p.1 with
  | .assertZero a _ =>
    match provOf pv a with
    | some (f, o, len) => decide (a < p.2) && winsOk f o len
    | none => false
  | _ => false

/-- `FRNodeRun4BR.stFlag`, below `FRNodeRows4`. -/
def stFlagT (T : BTab) (p : Op × ℕ) : Bool :=
  match T.st, p.1 with
  | some s, .assertEq a b _ =>
    match T.rt.getD a .none, T.rt.getD b .none with
    | .pf o 1, .cb bs => decide (o = s.so ∧ bs.data = #[s.t] ∧ s.t ≠ 0 ∧ a < p.2 ∧ b < p.2)
    | _, _ => false
  | some s, .assertZero a _ =>
    match T.rt.getD a .none with
    | .pf o len => decide (o = s.so + s.z ∧ o + len = s.so + s.L ∧ a < p.2)
    | _ => false
  | _, _ => false

/-- **The ops the closure covers**: the possible imports and foreign flags, less the asks, the `bitOf`s
and the replay ops. -/
def closeCov (op : Op) : Bool :=
  !op.item?.isSome && !isRep op && !isBitOf op && (opImp op || forCap op)

/-- **`opOut`'s foreign flag**, without its rows (`opForeign_eq`). -/
def opForeign (cs : CS) : Op → Bool
  | .assertEq a b act =>
    if offK act then false else
    match (cs.slot a).ty?, (cs.slot b).ty? with
    | some _, some _ => false
    | _, _ => true
  | .assertZero a act => if offK act then false else (cs.slot a).ty?.isNone
  | .assertOneHot a b c => !((cs.slot a).isSome && (cs.slot b).isSome && (cs.slot c).isSome)
  | .assertBit .. | .eqTableK _ | .kindInd _ | .maskRows .. => true
  | _ => false

/-- **The ops a template may take** (`tplExt4`'s: `extCan_none`). -/
def extCan : Op → Bool
  | .eqPt .. | .shiftEq .. | .phiRS .. | .kindFoldWeight .. | .shiftMask .. | .walkAB .. | .slotW ..
  | .maskRows .. | .eqZ .. | .lagrangeS .. | .eqTableK _ | .dotKF .. | .rowW .. | .tensorW .. | .keep ..
  | .packFK _ | .getK .. => true
  | _ => false

/-- **The closure's import rows** (at a possible import `A` does not cover): a failing row if the compile
made it an import (no template took it; the extension is asked only at the ops it may take, `extCan`). -/
def impRows (X : Ext) (P : Params) (cs : CS) (op : Op) : List Row :=
  if !extCan op || (X P cs op).isNone then [failRT P] else []

/-- **The closure's flag rows** (at a possible foreign flag): a failing row if it is one (no template,
`opOut`'s flag) that neither the zero pins nor the statement's flags discharge. -/
def forRows (X : Ext) (pv : List (ℕ × ℕ × ℕ × ℕ)) (T : BTab) (P : Params) (cs : CS) (op : Op) : List Row :=
  if opForeign cs op && (!extCan op || (X P cs op).isNone) && !zPinT pv (op, cs.slots.size) &&
      !stFlagT T (op, cs.slots.size) then [failRT P]
  else []

/-- **`A` closed** (`X` the template-free context, `pv` the `piField` registers, `T` the bit tables, `nx`
the program's `bitNxAll`, computed once by the caller): it covers `A`'s ops and the possible imports and
foreign flags (`closeCov`). At a possible import, `A`'s rows if `A` covers it, else `impRows`; at a
possible foreign flag, `A`'s rows (if it covers it) and `forRows`; elsewhere `A`'s rows, and at the first
ask (`k = 0`) a failing row unless `nx` (every `bitOf` is followed by a `selectHalf` on it). `closeCov` is tested first, so that `A`'s cover is evaluated once per
op (`impcTG`'s window test at the proof reads is the costly one). -/
def TG.close (A : TG) (X : Ext) (pv : List (ℕ × ℕ × ℕ × ℕ)) (T : BTab) (nx : Bool) : TG :=
  ⟨fun op => closeCov op || A.cov op, fun P cs pre op k =>
    if closeCov op then
      if opImp op then (if A.cov op then A.rows P cs pre op k else impRows X P cs op)
      else (if A.cov op then A.rows P cs pre op k else []) ++ forRows X pv T P cs op
    else A.rows P cs pre op k ++
      (if k = 0 && op.item?.isSome && !nx then [failRT P] else [])⟩

/-- **`A` failing at the replay ops `rc` does not cover** (SEG-R2; `rc` the replay templates' cover): at a
replay op (`isRep`) neither `A` nor `rc` covers, the failing row; elsewhere `A`'s rows. So the replay ops'
imports left to the run facts (`impQX`) are none (`FRNodeRun4CB.impQX_repF`), and the circuit rejects a
replay op no template replays instead of trusting it. -/
def TG.repF (A : TG) (rc : Op → Bool) : TG :=
  ⟨fun op => A.cov op || (isRep op && !rc op), fun P cs pre op k =>
    if !A.cov op && isRep op && !rc op then [failRT P] else A.rows P cs pre op k⟩

/-- **`B` beside `A`, `A` not asked at `B`'s ops** (`TG.addD` without asking `A` there): for a `B` whose
ops `A` does not cover (the siblings), so that `A`'s cover is not evaluated again at them. -/
def TG.addE (A B : TG) : TG :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k =>
    if B.cov op then B.rows P cs pre op k ++ (if op.item?.isSome then A.rows P cs pre op k else [])
    else A.rows P cs pre op k ++ (if op.item?.isSome then B.rows P cs pre op k else [])⟩

end Rev4
end FR
