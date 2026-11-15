-- New for lvm2 (roll 8 = B1, B1-IX): the B program's static data from its typed layout. The frozen placements
-- (`TFrz`: the word space's regions with their `C_main`/`C_rec` targets, the mini-bus's column words) give B1-Q's
-- `TData` (the circuit's) and B1-V's `TNat` (V_S's); `frzOf` computes them from a layout (the generator,
-- `qasm genb`, writes them as data, `LvmQAsmDataB20`/`B8`).
import LvmTypedLayQ
import LvmTypedV
import LvmKS14Layout

/-!
# The B program's static data

* **Targets** (B1-IX's layout of `C_main`, `layout0`): the committed region `[0, 2^comLog)` of the word space is
  `C_main`'s typed region `T` from `(layout0 p).t`; a `KS` alias region (`inRegs`' `xs` column `l`, `ys` lane `l`,
  `md` word `l`) is its `C_main` run (`ksDst`: `X_l` from row 0, `KS` lane `l` from the split, lane `l`'s last trace
  row; M′: `X_l` is the stream block's column `l` from the split, `xCol`); `σ′`'s region is the stream block's column
17 from row 0 (`sCol p 17`, a `C_main` word); `S_flat`'s is the stream from position 0; `PUB`'s the header
  from lane 0.
* **The mini-bus's columns** sit past the fixed blocks (`(layout0 p).freeLo`), largest first, aligned (`mbPlace`):
  the read tables' count columns and the seeds' finalize columns; the read tables' address and value columns are the
  layout's words of `capTpl`'s cells (`mbW`).
* **`tdataOf C F`** (the circuit's `TData`) and **`tnatOf C lay F c`** (V_S's `TNat`, `Φ_Q` = `PhiQC c`) read one
  `TFrz`, so the circuit and V_S see the same regions and tables.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR sumcheckTabs)

/-- **The frozen placements** of the B program's static data. -/
structure TFrz where
  /-- The committed regions (word space → `C_main`). -/
  com : List TReg
  /-- The `KS` alias regions (word space → `C_main`'s `KS` blocks). -/
  ks : List TReg
  /-- `σ′`'s regions (word space → `C_main`: M′, the stream block's column 17). -/
  sig : List TReg
  /-- `S_flat`'s base in the word space. -/
  sflat : Nat
  /-- `PUB`'s base. -/
  pub : Nat
  /-- The word `1`. -/
  one : Nat
  /-- The `C_main` word of each `K` cell a read table reads (`capTpl`'s address and result cells at iteration 0). -/
  mbW : List (Nat × Nat)
  /-- The seeds' finalize columns (`C_main` words). -/
  mbFin : List Nat
  /-- The read tables' count columns (`C_main` words). -/
  mbCnt : List Nat
  deriving Repr, Inhabited, DecidableEq

/-- The `C_main` word of a read table's cell. -/
def TFrz.wordK (F : TFrz) (n : Nat) : Nat := ((F.mbW.find? (·.1 == n)).map (·.2)).getD 0

/-- **The mini-bus's tables** at the frozen placements (B1-Q's `mbT`). -/
def mbTOf (C : QCfg) (F : TFrz) : List Tab :=
  mbT C F.wordK (fun k => (false, F.mbFin.getD k 0)) (fun k => F.mbCnt.getD k 0)

/-- **The circuit's static data** at the frozen placements (QLT's cells are constants of `Φ_Q`: no region). -/
def tdataOf (C : QCfg) (F : TFrz) : TData :=
  let ts := mbTOf C F
  ⟨F.com, F.ks, F.sig, F.sflat, F.pub, F.one, none, ts.map Tab.shape, (ts.map (·.τ)).foldl max 0, mbFixOf C,
    log2Ceil (pushLeavesR ts)⟩

/-- The target of a word-space region of base `b` (the frozen `com`, `ks`, `σ′` regions; `0` for the others). -/
def TFrz.dst (F : TFrz) (b : Nat) : Nat :=
  (((F.com ++ F.ks ++ F.sig).find? (·.base == b)).map (·.off)).getD 0

/-- **V_S's regions**: the layout's, with the frozen targets. -/
def nregsOf (lay : Typed.Lay) (F : TFrz) : List TypedV.NReg := lay.yregs.map fun y => ⟨y.base, y.log, y.src, F.dst y.base⟩

/-- The native regions are the layout's (`TypedV.TNat.layOk`, restated here so that V's instance does not import the
specification; `layOkN_eq` in `LvmSubmissionST`). -/
def layOkN (N : TypedV.TNat) (lay : Typed.Lay) : Bool :=
  lay.yregs == N.regs.map fun r ↦ (⟨r.base, r.log, r.src⟩ : YReg)

/-- **V_S's typed instance** on a layout, the frozen placements and an evaluator cache. -/
def tnatOf (C : QCfg) (lay : Typed.Lay) (F : TFrz) (c : PhiCache) : TypedV.TNat := ⟨nregsOf lay F, PhiQC c, mbTOf C F⟩

/-! ## The placements of a layout (the generator) -/

/-- The `C_main` word of the `KS` alias region from input cell `lo` (`inRegs`' entries). -/
def ksDst (C : QCfg) (lo : Nat) : Nat :=
  let p := C.p
  let L := layout0 p
  if lo < ysB C then Lvm.xCol p ((lo - xsB C) / 2 ^ 9) + (lo - xsB C) % 2 ^ 9
  else if lo < mdB C then L.ks + 2 ^ p.ksLog * (50 + (lo - ysB C) / 2 ^ 9) + ksSplit p + (lo - ysB C) % 2 ^ 9
  else L.ks + 2 ^ p.ksLog * (50 + (lo - mdB C)) + (spongeBlocks p - 1)

/-- The `C_main` word of lane `l`'s row 0 of a lane-split `KS` alias region from input cell `lo` (`xs`: `X_l`;
`ys`: `KS` output lane `l` from the split). -/
def ksDstL (C : QCfg) (lo l : Nat) : Nat :=
  let p := C.p
  let L := layout0 p
  if lo < ysB C then Lvm.xCol p l else L.ks + 2 ^ p.ksLog * (50 + l) + ksSplit p

/-- Offsets for items of log-heights `items`, largest first (stable), aligned, from `lo` (by item index). -/
def mbPlace (items : List Nat) (lo : Nat) : List Nat := Id.run do
  let sorted := items.zipIdx.mergeSort fun a b => decide (b.1 ≤ a.1)
  let top := (sorted.head?.map (·.1)).getD 0
  let mut off := (lo + 2 ^ top - 1) / 2 ^ top * 2 ^ top
  let mut out := Array.replicate items.length 0
  for (τ, i) in sorted do
    out := out.set! i off
    off := off + 2 ^ τ
  return out.toList

/-- The read tables' `(block, row)`s and their log-heights. -/
def readRowsOf (C : QCfg) : List ((Nat × Nat) × Nat) :=
  let Q := qlinkProg C
  (capReadRows Q).map fun x => (x, (Q.blk x.1).lsize)

/-- **The placements of a layout** (`qasm genb`). -/
def frzOf (C : QCfg) (lay : Typed.Lay) : TFrz :=
  let p := C.p
  let L := layout0 p
  let ins := (inRegs C).zip lay.inp
  let reg (e : (ℕ × ℕ × YSrc) × DReg) (dst : Nat) : TReg := ⟨e.2.bases.headD 0, Typed.clog2 (e.1.2.1 - e.1.1), dst⟩
  let comLog := (lay.yregs.headD default).log
  let Q := qlinkProg C
  let rr := readRowsOf C
  let nSeed := (mbBlocks p).length
  let offs := mbPlace (rr.map (·.2) ++ List.replicate nSeed mbBlk) L.freeLo
  { com := [⟨0, comLog, L.t⟩]
    ks := (ins.filter (·.1.2.2 == .ks)).flatMap fun e =>
      if e.2.lanes ≤ 1 then [reg e (ksDst C e.1.1)]
      else (List.range e.2.lanes).map fun l =>
        ⟨e.2.laneBases.getD l 0, Typed.clog2 (e.2.n / e.2.lanes), ksDstL C e.1.1 l⟩
    sig := (ins.filter (·.1.2.2 == .sigma)).map fun e => reg e (Lvm.sCol p recStreamCols)
    sflat := ((ins.find? (·.1.2.2 == .sflat)).map (·.2.bases.headD 0)).getD 0
    pub := ((ins.find? (·.1.2.2 == .pub)).map (·.2.bases.headD 0)).getD 0
    one := lay.one
    mbW := rr.flatMap fun x =>
      [(adrCell Q x.1.1 x.1.2 0, L.t + lay.wordK (adrCell Q x.1.1 x.1.2 0)),
       (resCell Q x.1.1 x.1.2 0, L.t + lay.wordK (resCell Q x.1.1 x.1.2 0))]
    mbFin := offs.drop rr.length
    mbCnt := offs.take rr.length }

/-- The words the mini-bus's columns occupy past `freeLo` (their end). -/
def mbTop (C : QCfg) (F : TFrz) : Nat :=
  let rr := readRowsOf C
  ((rr.zip F.mbCnt).map (fun (x : ((Nat × Nat) × Nat) × Nat) => x.2 + 2 ^ x.1.2) ++
    F.mbFin.map (· + 2 ^ mbBlk)).foldl max (layout0 C.p).freeLo

end Lvm.QTyped
