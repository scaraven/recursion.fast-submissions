-- New for lvm2 (roll 8 = B1, L-D): native checks of the typed layout that the typed `NodeSound` needs and the
-- guard `staticOkT20` does not give (L-W ANDs them into the submission's guard, as `oneOkB`). Definitions only
-- (computable, no closed constants, imports at the guard's level); their soundness is in `LvmNodeSoundTIn`/`TRd`.
import LvmQTypedGuard

/-!
# The typed layout's checks for `NodeSound`

The kernel cannot evaluate the layout `layT20` (built from the B program), so what `NodeSound` reads of it is checked
natively at start-up, through the layout's array caches (`K.FL`, `K.fl_wordK`, `K.fl_cst`).

* **`tgtN N lay y`**: what the specification's `zOf` reads at word `y` (`TNat.inst N Q lay`): `S_flat`'s and `σ′`'s
  `C_rec` word, a committed or `KS` word's `C_main` word, `PUB`'s lane. **`cellOkB`**: cell `c` has no constant and its
  word's target is `t`.
* **`inMapB C Q lay N`**: the input map's cells (Q_link's stream, Q_sig's `σ′`, `KS`'s `X` and output lanes, the
  trace-digest row, `PUB`) have their targets.
* **`rdChkB C F Q lay N`**: every `readd` instance of `Q` either is a **static** read whose layout target `e`
  (`CSrc.alias`) shares the result cell's word, whose address cell is the constant `g^e` or the result of a `lin`
  row `g^l·α` on a constant `α = g^{e−l}` (QLT's address rows), or is **committed**: its address and result cells are
  row `jf` of a mini-bus read table (`capParams`: `capReads`' columns at the frozen words).
* **`mbSeedsOkB C`**: the mini-bus's seed blocks lie in the stream (lane class `< 17`, rows `< 2^rl`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.TypedV
open Lvm.M3 (Tab nReads)

/-! ## A cell through its word's region -/

/-- What `zOf` reads at a word: `C_rec`'s word, `C_main`'s word, the header's lane. -/
inductive CTgt where
  /-- `C_rec`'s word. -/
  | crec (w : ℕ)
  /-- `C_main`'s word. -/
  | cmain (w : ℕ)
  /-- The header's lane. -/
  | cpub (k : ℕ)
  deriving DecidableEq

/-- `TNat.off` (the target of word `y` in its region; restated so that this module does not import the
specification). -/
def offN (N : TNat) (y : ℕ) : ℕ :=
  match N.regs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log) with
  | some r => r.dst + (y - r.base)
  | none => 0

/-- **The target of word `y`** on the layout `lay` with V_S's instance `N` (M′, lvm2 roll 11 `S2GM`: `S_flat` and `σ′`
read `C_main`'s stream block at `P20`, `CMain.sOff20`; `.crec` targets are no longer made). -/
def tgtN (N : TNat) (lay : Typed.Lay) (y : ℕ) : Option CTgt :=
  match (lay.yregs.find? fun r ↦ decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)).map (·.src) with
  | some YSrc.sflat => some (.cmain (CMain.sOff20 + sflatWord (offN N y)))
  | some YSrc.sigma => some (.cmain (offN N y))
  | some YSrc.com => some (.cmain (offN N y))
  | some YSrc.ks => some (.cmain (offN N y))
  | some YSrc.pub => some (.cpub (offN N y))
  | _ => none

/-- **A cell checked natively**: no constant, and its word's target is `t`. -/
def cellOkB (F : K.FL) (lay : Typed.Lay) (N : TNat) (c : ℕ) (t : CTgt) : Bool :=
  F.cst c == none && tgtN N lay (F.wordK c) == some t

/-- Every cell `base + j` (`j < s·2^τ`) of a bundle has target `tg (j % s) (j / s)`. -/
def bundleOkB (F : K.FL) (lay : Typed.Lay) (N : TNat) (s τ base : ℕ) (tg : ℕ → ℕ → CTgt) : Bool :=
  (List.range (s * 2 ^ τ)).all fun j ↦ cellOkB F lay N (base + j) (tg (j % s) (j / s))

/-! ## The input map -/

/-- **The input map's cells, checked** (M′: all on `C_main`): the stream (17 lanes of `2^14`, the stream block's
columns), `σ′` (its column 17), `KS`'s `X` lanes (17 of `2^9`, the columns' rows from the split), `KS`'s output lanes 0–3 from the split (4 of `2^9`), the trace-digest
row, `PUB`'s lanes. -/
def inMapB (C : QCfg) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  let F := K.FL.ofLay Q lay
  let I := sigIn C
  bundleOkB F lay N 17 14 (Lvm.QAsm.lay C).sb (fun l r ↦ .cmain (CMain.sW20 l r)) &&
  bundleOkB F lay N 1 10 I.sg (fun _ r ↦ .cmain (CMain.sW20 17 r)) &&
  bundleOkB F lay N 17 9 I.xs (fun l r ↦ .cmain (CMain.ksXW20 l 0 + r)) &&
  bundleOkB F lay N 4 9 I.ys (fun l r ↦ .cmain (CMain.ksYW20 l (ksSplit P20) + r)) &&
  bundleOkB F lay N 4 0 I.md (fun l r ↦ .cmain (CMain.ksYW20 l (spongeBlocks P20 - 1) + r)) &&
  (List.range pubLanes).all fun j ↦ cellOkB F lay N (I.flag + j) (.cpub j)

/-! ## The `readd` instances -/

/-- **The mini-bus's read tables' parameters** `(τ, wa, wv)`: `capReads`' heights and address and value columns at
the frozen read words (`TFrz.wordK`), in `capReads`' order. -/
def capParams (C : QCfg) (F : TFrz) : List (ℕ × ℕ × ℕ) :=
  let Q := qlinkProg C
  (capReadRows Q).map fun x ↦ ((Q.blk x.1).lsize, F.wordK (adrCell Q x.1 x.2 0), F.wordK (resCell Q x.1 x.2 0))

/-- **A committed read** (address cell `a`, result cell `c`, iteration `jf`): row `jf` of some read table holds both
cells' words. -/
def capOkB (Fl : K.FL) (lay : Typed.Lay) (N : TNat) (ps : List (ℕ × ℕ × ℕ)) (a c jf : ℕ) : Bool :=
  ps.any fun p ↦ decide (jf < 2 ^ p.1) && cellOkB Fl lay N a (.cmain (p.2.1 + jf)) &&
    cellOkB Fl lay N c (.cmain (p.2.2 + jf))

/-- **QLT's address row**: cell `a` is the result, at iteration `jf` of block `b`, of a `lin (g^l + 1) 0` row on one
constant cell `α = g^{e − l}` (so `a = g^l·α = g^e`, characteristic 2), `1 ≤ l ≤ 4`. -/
def linOkB (Q : Program) (Fl : K.FL) (b jf a e : ℕ) : Bool :=
  let B := Q.blk b
  let j := unflat B.dims jf
  B.tpl.zipIdx.any fun x ↦
    match x.1.op, x.1.args with
    | .lin k k', [α₀, α₁] =>
      x.1.ty == .K && k' == 0 && α₀.ty == .K && α₁.ty == .K && α₀.at j == α₁.at j &&
        Q.start .K b + B.tw .K * jf + B.rank .K x.2 == a &&
        [1, 2, 3, 4].any fun l ↦ decide (l ≤ e) && k == Build.gpow l + 1 &&
          Fl.cst (α₀.at j) == some (Build.gpow (e - l))
    | _, _ => false

/-- **A static read** with target `e`: `e` an input cell with no constant, the result cell's word is `e`'s, and the
address is `g^e` (a constant, or QLT's address row). -/
def aliasOkB (Q : Program) (Fl : K.FL) (b jf a c e : ℕ) : Bool :=
  decide (e < Q.nInK) && Fl.cst e == none && Fl.cst c == none && Fl.wordK c == Fl.wordK e &&
    (Fl.cst a == some (Build.gpow e) || linOkB Q Fl b jf a e)

/-- **Every `readd` instance of `Q` reads its cell** (natively): per block and `readd` row (a `K` row on a `K`
address), at every iteration, the static read of its layout target (`CSrc.alias`) or a committed read of the mini-bus
(`capParams C F`). -/
def rdChkB (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  let Fl := K.FL.ofLay Q lay
  let ps := capParams C F
  Q.blocks.zipIdx.all fun bx ↦
    let B := bx.1
    let b := bx.2
    B.tpl.zipIdx.all fun tx ↦
      match tx.1.op with
      | .readd _ _ =>
        tx.1.ty == .K && (tx.1.args.getD 0 default).ty == .K &&
          (List.range B.size).all fun jf ↦
            let a := (tx.1.args.getD 0 default).at (unflat B.dims jf)
            let c := Q.start .K b + B.tw .K * jf + B.rank .K tx.2
            match (Fl.srcKA.getD b #[]).getD (B.rank .K tx.2) default with
            | .alias tgt => aliasOkB Q Fl b jf a c (tgt.getD jf 0)
            | _ => capOkB Fl lay N ps a c jf
      | _ => true

/-- **The mini-bus's seed blocks lie in the stream**: lane class `< 17`, rows `[q, q + 2^4)` below `2^rl`; and the
reads are fewer than `2^64 − 1` (`mem_lookup`). -/
def mbSeedsOkB (C : QCfg) (F : TFrz) : Bool :=
  (mbBlocks C.p).all (fun lq ↦ decide (lq.1 < 17 ∧ lq.2 + 2 ^ mbBlk ≤ 2 ^ C.rl)) &&
    decide (nReads (mbTOf C F) < 2 ^ 64 - 1)

/-- **The checks `NodeSound` reads** (for the guard). -/
def nodeChkB (C : QCfg) (F : TFrz) (Q : Program) (lay : Typed.Lay) (N : TNat) : Bool :=
  inMapB C Q lay N && rdChkB C F Q lay N && mbSeedsOkB C F

end Lvm.QTyped
