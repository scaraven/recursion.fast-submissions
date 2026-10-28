-- New for `flock-recursive` (BLUEPRINT §4.4 "The walk", A.11 `walkAB`, revision 3.15; stage
-- S-E10, track L-circ).
import FRVIRTemplates
import FRVIREval

/-!
# The walk as the node's own XOR DAG: the gadget program that emits rows

BLUEPRINT §4.4 (revision 3.15, changes 22 (a)): `walkAB rowW′ colW` is materialised as the BLAKE2s
gadget DAG — **one linear row per XOR** and two product rows per gate. This file is the row-emitting
interpretation of `FRBlake2sGeneric`'s gadget program: the same gadgets, statement for statement,
where a value is a **single-wire form** (`LinT`: an input `rowW′[k]`/`colW[k]`, a local, or `[]`
for zero), `xor` is a **program step** that emits the row `loc = a + b` (`dxor`; free when an
operand is `0`), and the product gate at position `k` emits `p_A = rowW′[k]·a + p_A`,
`p_B = rowW′[k]·b + p_B` (`dmul`: the two walk accumulators as running sums, single cells) and
returns `colW[k]`.

**Layout** (`dgW`): every `G` gadget starts at a fresh block (`Gate.pad`), so the 80 instances
(10 rounds × 8) sit at one stride, and their locals at fixed offsets.

The correctness theorem (`tplWalkAB_ok`, `FRVIRTplWalk`) relates this program to the walk
interpretation (`walkOps`) of the generic program by a relational simulation (`RelT`).
-/

namespace FR
namespace Tpl
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## The builder -/

/-- The DAG builder's state: the next gate position, the gates so far, their locals and rows, the
two accumulators' wires. -/
structure DSt where
  next : ℕ
  gs : Array Gate
  nl : ℕ
  nr : ℕ
  accA : LinT
  accB : LinT

/-- The DAG builder. -/
abbrev DB := StateM DSt

/-- Emit a gate; its first local. -/
def emit (g : Gate) : DB LinT :=
  modifyGet fun s =>
    (L s.nl, ⟨s.next, s.gs.push g, s.nl + g.nloc, s.nr + (g.rows 0).length, s.accA, s.accB⟩)

/-- Pad the locals and the rows to the next multiples of `2^b` (a fresh block). -/
def padTo (b : ℕ) : DB Unit :=
  modify fun s => ⟨s.next, s.gs.push (.pad (Circ.alignUp s.nr b - s.nr) (Circ.alignUp s.nl b - s.nl)),
    Circ.alignUp s.nl b, Circ.alignUp s.nr b, s.accA, s.accB⟩

/-- **XOR** of two forms: their formal sum (no row; characteristic 2). -/
def dx (a b : LinT) : LinT := a ++ b

/-- **A form as a cell**: a linear row `loc = l` when `l` has two terms or more (an XOR chain's
row); a single wire or `0` is kept as it is. -/
def dcell (l : LinT) : DB LinT := if l.length ≤ 1 then pure l else emit (.mulAdd [] [] l)

/-- A copy row `loc = a`, always (gives every bit of a constant word its own cell). -/
def dcopy (a : LinT) : DB LinT := emit (.mulAdd [] [] a)

variable (ri ci : ℕ → LinT)

/-- **The product gate** at the next position `k`: `p_A ← rowW′[k]·a + p_A`,
`p_B ← rowW′[k]·b + p_B` (two rows, two locals); its value is `colW[k]`. -/
def dmul (a b : LinT) : DB LinT :=
  modifyGet fun s =>
    let k := (pos (m := Blake2sCircuit.m) s.next).val
    (ci k, ⟨s.next + 1, (s.gs.push (.mulAdd (ri k) a s.accA)).push (.mulAdd (ri k) b s.accB),
      s.nl + 2, s.nr + 2, L s.nl, L (s.nl + 1)⟩)

/-- `n` values from a program per index, in order. -/
def dvec {β : Type} : (n : ℕ) → (Fin n → DB β) → DB (Vector β n)
  | 0, _ => pure #v[]
  | n + 1, f => do
    let v ← dvec n fun i => f i.castSucc
    let x ← f (Fin.last n)
    pure (v.push x)

/-- A word's bits as cells. -/
def dcellW (x : Vector LinT 32) : DB (Vector LinT 32) := dvec 32 fun i => dcell x[i]

/-- The form of a position: `colW[k]`. -/
def dvar (k : Pos Blake2sCircuit.m) : LinT := ci k.val

/-- `xorW` (forms). -/
def dxorW (x y : Vector LinT 32) : Vector LinT 32 := Vector.ofFn fun i => dx x[i] y[i]

/-- `litW`. -/
def dlitW (c : UInt32) : Vector LinT 32 :=
  Vector.ofFn fun i => if c.toNat.testBit i then dvar ci constPos else []

/-- `inW`. -/
def dinW (b : ℕ) : Vector LinT 32 := Vector.ofFn fun i => dvar ci (pos (b + i))

/-- `addCarries` (each carry a cell). -/
def daddCarries (x y : Vector LinT 32) : (n : ℕ) → LinT → DB (List LinT)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    let g ← dmul ri ci (dx (x[i]'(by omega)) c) (dx (y[i]'(by omega)) c)
    let c' ← dcell (dx c g)
    let rest ← daddCarries x y n c'
    pure (c :: rest)

/-- `sumW`: each output bit a cell (one row of `p ⊕ q ⊕ c`). -/
def dsumW (p q : Vector LinT 32) (cs : List LinT) : DB (Vector LinT 32) :=
  dvec 32 fun i => dcell (dx (dx p[i] q[i]) (cs.getD i []))

/-- `addW`. -/
def daddW (x y : Vector LinT 32) : DB (Vector LinT 32) :=
  daddCarries ri ci x y 31 [] >>= dsumW x y

/-- `majorities` (the majority bits are forms). -/
def dmajorities (x y z : Vector LinT 32) : (n : ℕ) → DB (List LinT)
  | 0 => pure []
  | n + 1 => do
    let i := 30 - n
    let g ← dmul ri ci (dx (x[i]'(by omega)) (z[i]'(by omega))) (dx (y[i]'(by omega)) (z[i]'(by omega)))
    let rest ← dmajorities x y z n
    pure (dx g (z[i]'(by omega)) :: rest)

/-- `rippleCarries` (each carry a cell). -/
def drippleCarries (p q : Vector LinT 32) : (n : ℕ) → LinT → DB (List LinT)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    if 1 ≤ i then
      let g ← dmul ri ci (dx (p[i]'(by omega)) c) (dx (q[i]'(by omega)) c)
      let c' ← dcell (dx c g)
      let rest ← drippleCarries p q n c'
      pure (c :: rest)
    else
      let rest ← drippleCarries p q n c
      pure (c :: rest)

/-- `xor3W` (forms). -/
def dxor3W (x y z : Vector LinT 32) : Vector LinT 32 := Vector.ofFn fun i => dx (dx x[i] y[i]) z[i]

/-- `shiftW`. -/
def dshiftW (ms : List LinT) : Vector LinT 32 :=
  Vector.ofFn fun i => if i.val = 0 then [] else ms.getD (i.val - 1) []

/-- `add3W`. -/
def dadd3W (x y z : Vector LinT 32) : DB (Vector LinT 32) := do
  let ms ← dmajorities ri ci x y z 31
  let cs ← drippleCarries ri ci (dxor3W x y z) (dshiftW ms) 31 []
  dsumW (dxor3W x y z) (dshiftW ms) cs

/-- The row bits of a `G` block. -/
def gBits : ℕ := 10

/-- `gW`, in a fresh block of `2^gBits` rows and locals; its four output words are cells. -/
def dgW (v : Vector (Vector LinT 32) 16) (a b c d : Fin 16) (mx my : Vector LinT 32) :
    DB (Vector (Vector LinT 32) 16) := do
  padTo gBits
  let a1 ← dadd3W ri ci v[a] v[b] mx
  let d1 := GOps.rotrW (dxorW v[d] a1) 16
  let c1 ← daddW ri ci v[c] d1
  let b1 := GOps.rotrW (dxorW v[b] c1) 12
  let a2 ← dadd3W ri ci a1 b1 my
  let d2 := GOps.rotrW (← dcellW (dxorW d1 a2)) 8
  let c2 ← daddW ri ci c1 d2
  let b2 := GOps.rotrW (← dcellW (dxorW b1 c2)) 7
  pure ((((v.set a a2).set b b2).set c c2).set d d2)

/-- `roundW`. -/
def droundW (v m' : Vector (Vector LinT 32) 16) (s : Vector (Fin 16) 16) :
    DB (Vector (Vector LinT 32) 16) := do
  let v ← dgW ri ci v 0 4 8 12 m'[s[0]] m'[s[1]]
  let v ← dgW ri ci v 1 5 9 13 m'[s[2]] m'[s[3]]
  let v ← dgW ri ci v 2 6 10 14 m'[s[4]] m'[s[5]]
  let v ← dgW ri ci v 3 7 11 15 m'[s[6]] m'[s[7]]
  let v ← dgW ri ci v 0 5 10 15 m'[s[8]] m'[s[9]]
  let v ← dgW ri ci v 1 6 11 12 m'[s[10]] m'[s[11]]
  let v ← dgW ri ci v 2 7 8 13 m'[s[12]] m'[s[13]]
  dgW ri ci v 3 4 9 14 m'[s[14]] m'[s[15]]

/-- `initW`, word `w` (the compression runs `dvec 16 dinitWord`): the words built from the IV get a cell per bit (`dcopy`), so that every `G` reads
single, distinct cells. -/
def dinitWord (w : Fin 16) : DB (Vector LinT 32) :=
  if w.val < 8 then pure (dinW ci (32 * w))
  else if w.val < 12 then dvec 32 fun i => dcopy (dlitW ci iv[w.val - 8])[i]
  else dvec 32 fun i => dcopy (dxorW (dlitW ci iv[w.val - 8]) (dinW ci (counterLo + 32 * (w.val - 12))))[i]

/-- Output word `w` of the compression: `v[w] ⊕ v[w+8] ⊕ h[w]`, its bits as cells. -/
def dfinWord (v : Vector (Vector LinT 32) 16) (w : Fin 8) : DB (Vector LinT 32) :=
  dcellW (dxorW (dxorW v[w] v[w.val + 8]) (dinW ci (32 * w)))

/-- `compressW`. -/
def dcompressW : DB (Vector (Vector LinT 32) 8) := do
  let msg : Vector (Vector LinT 32) 16 := Vector.ofFn fun w => dinW ci (msgBase + 32 * w)
  let v0 ← dvec 16 (dinitWord ci)
  let v ← sigma.toList.foldlM (fun v s => droundW ri ci v msg s) v0
  padTo gBits
  dvec 8 (dfinWord ci v)

/-- A product row into accumulator `A` (`B` if `b`): `p ← rowW′[k]·a + p`. -/
def dacc (b : Bool) (k : ℕ) (a : LinT) : DB Unit :=
  modifyGet fun s => ((), ⟨s.next, s.gs.push (.mulAdd (ri k) a (if b then s.accB else s.accA)),
    s.nl + 1, s.nr + 1, if b then s.accA else L s.nl, if b then L s.nl else s.accB⟩)

/-- The accumulations after the compression (`walkABF`'s order): per output row the form into `A`
and the constant into `B`; per input position `colW[k]` into `A` and the constant into `B`; the
constant's row into both. -/
def accOps (r : Vector (Vector LinT 32) 8) : List (Bool × ℕ × LinT) :=
  (outPairs r).flatMap (fun p => [(false, p.1.val, p.2), (true, p.1.val, dvar ci constPos)]) ++
    Eval.inPos.map (fun k => (false, k, dvar ci (pos k))) ++
    Eval.inPos.map (fun k => (true, k, dvar ci constPos)) ++
    [(false, constPos.val, dvar ci constPos), (true, constPos.val, dvar ci constPos)]

/-- Row weight `k` (`0` past `n`): input `k`. -/
def rowI (n k : ℕ) : LinT := if k < n then I k else []

/-- Column weight `j` (`0` past `m`): input `n + j`, after the `n` row weights. -/
def colI (n m j : ℕ) : LinT := if j < m then I (n + j) else []

/-- The builder's start: gate position `gateBase`, nothing emitted. -/
def dst0 : DSt := ⟨gateBase, #[], 0, 0, [], []⟩

/-- **The walk's DAG**, the builder's final state for `rowW′ : AF n`, `colW : AF m`: the compression,
then the accumulations. -/
def dwalkRun (n m : ℕ) : DSt :=
  let p := (dcompressW (rowI n) (colI n m)).run dst0
  (((accOps (colI n m) p.1).forM fun t => dacc (rowI n) t.1 t.2.1 t.2.2).run p.2).2

/-- **The `walkAB` template** for `rowW′ : AF n`, `colW : AF m` (inputs `rowW′`, then `colW`): the
DAG's gates; outputs the two accumulators. Irreducible: no unification evaluates the DAG. -/
@[irreducible] def tplWalkG (n m : ℕ) : Tpl :=
  ⟨(dwalkRun n m).gs.toList, [(dwalkRun n m).accA, (dwalkRun n m).accB]⟩

/-! ## Controls -/

/-- (+) A form of two terms becomes a cell: one gate is emitted. -/
theorem dcell_emits (a b : Wire × F) (s : DSt) : ((dcell [a, b]).run s).2.gs.size = s.gs.size + 1 := by
  show (s.gs.push _).size = _
  exact Array.size_push ..

/-- (−) A single wire stays a wire: no gate. -/
theorem dcell_free (a : Wire × F) (s : DSt) : ((dcell [a]).run s).2 = s := rfl

/-- (+) Padding: `r` empty rows and `l` locals, its equation trivial. -/
theorem pad_rows : (Gate.pad 2 3).rows 0 = [⟨[], [], []⟩, ⟨[], [], []⟩] ∧ (Gate.pad 2 3).nloc = 3 :=
  ⟨rfl, rfl⟩

/-- (−) An XOR row constrains its cell: `loc 2 = loc 0 + loc 1` fails at `(0, 0, 1)`. -/
theorem xor_row_neg :
    ¬ (Gate.mulAdd [] [] [(.loc 0, 1), (.loc 1, 1)]).Eqn ⟨1, fun _ => 0, fun k => if k = 2 then 1 else 0⟩ 2 := by
  simp [Gate.Eqn, LinT.ev, Wire.ev]

end Tpl
end FR
