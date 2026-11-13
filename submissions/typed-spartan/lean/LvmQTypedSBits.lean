-- New for lvm2 (roll 8 = B1, B1-IX-S): the typed V_S's start-up. The `BITS` classes (`bspecs`) and QLT's data
-- with their parameters computed once: `bspecsF = bspecs`, `qltPaddedF = qltPadded`, `qltCstF = qltCst`.
-- Adapts V-PERF's `posCellF`/`posOcF` (`LvmVFast`, not imported: it imports a submission) and `qltEntriesF`.
import LvmQTypedBits
import LvmVFastQ

/-!
# The `BITS` classes and QLT's data, fast

`opens p`, `plan p`, `spB C`, `bsB C`, `pwB C`, `ansLane p i`, `bitBase p lay k` each cost about a millisecond
[measured, P20], and the lane classes' cell functions (`posSpec`'s `wc`, `oc`), the `s'` class's and the PoW
class's call them at every row: B1-Q's chunking (`BSpec.ablks`) took 36–65 s at P20. Here the same classes with
those values computed once per class:

* **`bspecsF C D = bspecs C D`** (`bspecsF_eq`): `posSpecF` (lane classes; the openings' bases tabulated, the
  rows as an array with their `laneOuts`, `ansLaneF`), `sSpecF`, `powSpecF`;
* **`qltPaddedF = qltPadded`**, **`qltCstF = qltCst`** (V-PERF's `qltEntriesF`, `qltDataF`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.QAsm Lvm.QLink Lvm.BitsTab Lvm.Bits Lvm.VF Lvm.Replay Lvm.SigBits

/-! ## `posCell`, `posOc` with their bases passed in (V-PERF's `posCellF`, `posOcF`) -/

/-- `posCell C k o x` with `bb = bitBase`, `sb = spB C + spBefore`, `fl = flB C`, `pa2 = 2^pa`,
`px = posIdx … k 0` (`H`, `t`, `pT`, `nR` the opening's height, `t`, `padT t`, `nRows`). -/
def posCellS (H t pT nR bb sb fl pa2 px x : Nat) : BOut × Nat × Nat → Nat
  | (_, 0, n) =>
    let j := 8 * x + n / H
    if j < pT then bb + H * j + n % H else sb + 2 * (8 * nR - t) + H * (j - pT) + n % H
  | (_, kind, i) =>
    let j := 8 * x + i
    if j < t then fl + (if kind = 1 then 0 else pa2) + (px + j) else sb + 2 * (j - t) + (kind - 1)

theorem posCellS_eq (C : QCfg) (k : Nat) (o : OpenInfo) (x : Nat) (u : BOut × Nat × Nat) :
    posCellS o.L.height o.L.t (padT o.L.t) (nRows o) (bitBase C.p (lay C) k)
      (spB C + spBefore C.p k) (flB C) (2 ^ C.pa) (posIdx C.p k 0) x u = posCell C k o x u := by
  obtain ⟨b, kind, n⟩ := u
  cases kind with
  | zero => rfl
  | succ kind =>
    have hp : posIdx C.p k (8 * x + n) = posIdx C.p k 0 + (8 * x + n) := by unfold posIdx; omega
    simp only [posCellS, posCell]
    rw [hp]

/-- `posOc C l U r j` with `u = U[j]`, the opening's bases `b`, the row's outputs `LO = laneOuts H l`, `fl`,
`pa2` passed in. -/
def posOcS (l : Nat) (u : BOut) (LO : List (BOut × Nat × Nat)) (fl pa2 : Nat) (b : Nat × Nat × Nat)
    (r : Nat × OpenInfo × Nat × Nat) (j : Nat) : Nat :=
  match LO.find? (fun e => e.1 == u) with
  | some e => posCellS r.2.1.L.height r.2.1.L.t (padT r.2.1.L.t) (nRows r.2.1) b.1 b.2.1 fl pa2 b.2.2 r.2.2.1 e
  | none => r.2.2.2 + (j - QAsm.laneBits r.2.1.L.height l)

theorem posOcS_eq (C : QCfg) (l : Nat) (U : List BOut) (r : Nat × OpenInfo × Nat × Nat) (j : Nat) :
    posOcS l (U.getD j (.bit 0)) (laneOuts r.2.1.L.height l) (flB C) (2 ^ C.pa)
      (bitBase C.p (lay C) r.1, spB C + spBefore C.p r.1, posIdx C.p r.1 0) r j = posOc C l U r j := by
  unfold posOcS posOc
  generalize (laneOuts r.2.1.L.height l).find? (fun e => e.1 == U.getD j (.bit 0)) = d
  cases d with
  | none => rfl
  | some e => exact posCellS_eq C r.1 r.2.1 r.2.2.1 e

/-! ## The openings' bases, once -/

/-- An opening's bases `(bitBase, spB + spBefore, posIdx … 0)`. -/
def opBase (C : QCfg) (k : Nat) : Nat × Nat × Nat := (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0)

/-- **The openings' bases, tabulated** on the openings computed once (`opBaseT_eq`). -/
def opBaseT (C : QCfg) : Array (Nat × Nat × Nat) :=
  let OP := opens C.p
  let bb := (lay C).bb
  let sp := spB C
  (Array.range OP.length).map fun k =>
    (bb + ((OP.take k).map fun o => padT o.L.t * o.L.height).sum, sp + ((OP.take k).map spOf).sum,
      ((OP.take k).map fun o => o.L.t).sum + 0)

/-- A tabulated function with its fallback. -/
def tabOr {α : Type} (A : Array α) (f : Nat → α) (k : Nat) : α := if h : k < A.size then A[k] else f k

theorem tabOr_eq {α : Type} (n : Nat) (f : Nat → α) (A : Array α) (hA : A = (Array.range n).map f) :
    tabOr A f = f := by
  funext k
  unfold tabOr
  split
  · subst hA; simp
  · rfl

theorem opBaseT_eq (C : QCfg) : tabOr (opBaseT C) (opBase C) = opBase C :=
  tabOr_eq (opens C.p).length (opBase C) (opBaseT C) rfl

/-! ## The lane classes -/

/-- Row `y`'s data in lane class `l` (class rows `R`, bases `BT`): the class row, its `laneOuts`, its opening's
bases. -/
def rdOf (C : QCfg) (l : Nat) (R : List (Nat × OpenInfo × Nat × Nat)) (BT : Array (Nat × Nat × Nat)) (y : Nat) :
    (Nat × OpenInfo × Nat × Nat) × List (BOut × Nat × Nat) × (Nat × Nat × Nat) :=
  let r := R.getD y default
  (r, laneOuts r.2.1.L.height l, tabOr BT (opBase C) r.1)

/-- Lane class `l`'s output cell `j` at row `y`, from the row data (`RD`, `rd` its fallback). -/
def ocT (l fl pa2 : Nat) (UA : Array BOut)
    (RD : Array ((Nat × OpenInfo × Nat × Nat) × List (BOut × Nat × Nat) × (Nat × Nat × Nat)))
    (rd : Nat → (Nat × OpenInfo × Nat × Nat) × List (BOut × Nat × Nat) × (Nat × Nat × Nat)) (j y : Nat) : Nat :=
  let d := tabOr RD rd y
  posOcS l (UA.getD j (.bit 0)) d.2.1 fl pa2 d.2.2 d.1 j

theorem ocT_spec (C : QCfg) (l j y : Nat) :
    ocT l (flB C) (2 ^ C.pa) (lnOuts C.p l).toArray
      ((Array.range (posRows C l).length).map (rdOf C l (posRows C l) (opBaseT C)))
      (rdOf C l (posRows C l) (opBaseT C)) j y = posOc C l (lnOuts C.p l) ((posRows C l).getD y default) j := by
  unfold ocT
  rw [tabOr_eq _ _ _ rfl]
  simp only [rdOf, opBaseT_eq, opBase, toArray_getD]
  exact posOcS_eq C l _ _ j

/-- Lane class `l`'s word cell at row `y` (`RA` the class rows). -/
def wcT (C : QCfg) (l : Nat) (O0 : Array Nat) (PA : Array Replay.PE) (RA : Array (Nat × OpenInfo × Nat × Nat))
    (y : Nat) : Nat :=
  let r := RA.getD y default
  ansLaneF O0 PA C.p (r.2.1.pe + r.2.2.1) + l

theorem wcT_spec (C : QCfg) (l y : Nat) :
    wcT C l (offs C.p) (plan C.p).toArray (posRows C l).toArray y =
      ansLane C.p (((posRows C l).getD y default).2.1.pe + ((posRows C l).getD y default).2.2.1) + l := by
  simp only [wcT, toArray_getD, ansLaneF_eq']

/-- **Lane class `l`** (`posSpec`) with its row data tabulated (`posSpecF_eq`). -/
def posSpecF (C : QCfg) (bpl : Nat → Nat → Bool × Nat) (l : Nat) : BSpec :=
  let U := lnOuts C.p l
  let R := posRows C l
  let rd := rdOf C l R (opBaseT C)
  let RD := (Array.range R.length).map rd
  let fl := flB C
  let pa2 := 2 ^ C.pa
  let UA := U.toArray
  let O0 := offs C.p
  let PA := (plan C.p).toArray
  let RA := R.toArray
  { τ := clog2 R.length, n := R.length, outs := U, rd := true,
    wc := wcT C l O0 PA RA,
    oc := ocT l fl pa2 UA RD rd,
    pl := bpl l, sh := lnSh C.p l,
    hsh := fun j hj x hx => (ocT_spec C l j x).trans
      ((posOc_sh C l j hj x hx).trans (congrArg (· + j) (ocT_spec C l 0 x).symm)) }

theorem posSpecF_eq (C : QCfg) (bpl : Nat → Nat → Bool × Nat) (l : Nat) : posSpecF C bpl l = posSpec C bpl l := by
  unfold posSpecF posSpec
  simp only [BSpec.mk.injEq, true_and, and_true]
  exact ⟨funext fun y => wcT_spec C l y, funext fun j => funext fun y => ocT_spec C l j y⟩

/-- **The lane classes** (`posSpecs`). -/
def posSpecsF (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : List BSpec := (List.range (nPosCls C)).map (posSpecF C bpl)

theorem posSpecsF_eq (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : posSpecsF C bpl = posSpecs C bpl := by
  unfold posSpecsF posSpecs
  rw [show posSpecF C bpl = posSpec C bpl from funext (posSpecF_eq C bpl)]

/-! ## The `s'` and PoW classes -/

/-- **The `s'` bit class** (`sSpec`) with `sigIn`'s `hd` and `bsB` computed once. -/
def sSpecF (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  let hd := (sigIn C).hd
  let bs := bsB C
  ⟨2, 4, (List.range 64).map BOut.bit, true, fun x => hd + 9 + x, fun j x => bs + 64 * x + j, pl,
    64, by intros; omega⟩

theorem sSpecF_eq (C : QCfg) (pl : Nat → Bool × Nat) : sSpecF C pl = sSpec C pl := rfl

/-- **The PoW class** (`powSpec`) with the openings, `pwB` and the plan's offsets computed once. -/
def powSpecF (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  let OP := opens C.p
  let OA := OP.toArray
  let O0 := offs C.p
  let PA := (plan C.p).toArray
  let pw := pwB C
  ⟨clog2 OP.length, OP.length, [BOut.fld 0 (64 - C.p.grind) 0], true,
    fun x => ansLaneF O0 PA C.p ((OA.getD x default).pe - 1) + 2, fun _ x => pw + x, pl, 0,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem powSpecF_eq (C : QCfg) (pl : Nat → Bool × Nat) : powSpecF C pl = powSpec C pl := by
  unfold powSpecF powSpec
  simp only [BSpec.mk.injEq, true_and, and_true]
  funext x
  rw [toArray_getD, ansLaneF_eq']

/-! ## The classes -/

/-- **The node program's `BITS` classes** (`bspecs`), fast. -/
def bspecsF (C : QCfg) (D : QData) : List BSpec :=
  sigSpecs (sigIn C) (sigOut C) (bplOf D) ++ posSpecsF C (fun c => bplOf D (6 + c)) ++
    [sSpecF C (bplOf D (6 + nPosCls C)), powSpecF C (bplOf D (7 + nPosCls C))]

theorem bspecsF_eq (C : QCfg) (D : QData) : bspecsF C D = bspecs C D := by
  unfold bspecsF bspecs
  rw [posSpecsF_eq, sSpecF_eq, powSpecF_eq]

/-! ## QLT's entries -/

/-- `qltPadded` on V-PERF's `qltEntriesF`. -/
def qltPaddedF (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  let E := qltEntriesF p lay
  E ++ List.replicate (2 ^ lay.aQ - E.length) (lay.sb, lay.sb + 1, lane0C)

theorem qltPaddedF_eq (p : Params) (lay : Layout) : qltPaddedF p lay = qltPadded p lay := by
  unfold qltPaddedF qltPadded
  rw [qltEntriesF_eq]

end Lvm.QTyped
