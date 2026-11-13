-- New for lvm2 (roll 8 = B1, B1-K): the layout specification of the node program (`LSpec`): its input regions
-- (`LvmQAsmLay`), QLT's static `readd` targets (`qltPadded`, B1-P1P2 §1 "Row kinds"), the `BITS` tables
-- (`bspecs`); and the typed layouts `layQ C D`. Adapted from B1-W's `mkWorld` (its probe tool).
import LvmTypedLay
import LvmQAsmProg
import LvmQTypedProg
import LvmQTypedBits
import LvmQTypedSBits

/-!
# The node program's layout

* `inRegs C`: `S_flat` (`[0, 17·2^rl)`), `σ′`, the `KS` aliases (`xs`, `ys`, `md`), `PUB`, `QLT` (virtual) and the
  `BITS` outputs (committed, B1-P1P2 §5.3).
* `qltAlias C Q`: a `readd` whose address operand is QLT's `α` or `β` column, or a `lin (g^l + 1) 0` of one in the
  same block, reads stream cell `e₁ + l` (resp. `e₂ + l`) of the iteration's padded QLT entry: a static alias.
  Every other `readd` (`capTpl`'s) is committed (the mini-bus).
* `bitsOf C D`: the `BITS` tables of `bspecs` as `BitsSpec`.
* **`specQ C D`**, **`layQ C D`** (`mkLay` of `QT C D`).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm

/-- The input regions of the node program (QLT has none: its cells are constants of `Φ_Q`, `qltCst`). The `KS`
aliases (B1-IX): `xs` and `ys` are row-major (the program's arrays read lane `l`'s row `x` at `xsB + 17x + l`,
`ysB + 4x + l`), so they are lane-split (`inLanes`: 17 and 4 lanes of `2^9` rows, each lane its own word region,
mapped affinely onto its `C_main` run: `X_l` from row 0, `KS` lane `l` from the split); `md`'s 4 words (lane `l`'s
last trace row) one region each. -/
def inRegs (C : QCfg) : List (ℕ × ℕ × YSrc) :=
  [(0, nStream C, .sflat), (sgB C, sgB C + 2 ^ 10, .sigma), (xsB C, ysB C, .ks), (ysB C, mdB C, .ks)] ++
    (List.range 4).map (fun l ↦ (mdB C + l, mdB C + l + 1, YSrc.ks)) ++
    [(pbB C, pbB C + 2 ^ 10, .pub), (obB C, nK C, .com)]

/-- The lanes of `inRegs`' regions: `xs` 17, `ys` 4, the others 1. -/
def inLanesQ : List ℕ := [1, 1, 17, 4, 1, 1, 1, 1, 1, 1]

/-- **QLT's cells as constants** (B1-Q's decision, B-DES §1.3): `qltData` (per padded entry `g^e₁, g^e₂, v`), zero
to the region's end. -/
def qltCst (C : QCfg) : List (ℕ × List FK) :=
  let vs := Lvm.QLink.qltData C.p (lay C)
  [(qtB C, vs ++ List.replicate (2 ^ C.aQT - vs.length) 0)]

/-- `qltCst` on V-PERF's `qltDataF` (B1-IX-S: `qltData` costs 3.6 s at P20, `qltDataF` 8 ms [measured]). -/
def qltCstF (C : QCfg) : List (ℕ × List FK) :=
  let vs := Lvm.VF.qltDataF C.p (lay C)
  [(qtB C, vs ++ List.replicate (2 ^ C.aQT - vs.length) 0)]

theorem qltCstF_eq (C : QCfg) : qltCstF C = qltCst C := by
  unfold qltCstF qltCst
  rw [Lvm.VF.qltDataF_eq]

/-- `l` with `g^l + 1 = k`, for `l ≤ 4`. -/
def gpowL (k : FK) : Option ℕ := [1, 2, 3, 4].find? fun l ↦ Build.gpow l + (1 : FK) == k

/-- QLT's static `readd` targets in `Q` from QLT's padded entries `pad` (`qltAlias`, `qltAliasF`). -/
def qltAliasE (C : QCfg) (Q : Program) (pad : List (ℕ × ℕ × ℕ)) : Array (Array (Option (List ℕ))) :=
  let qt := qtB C
  let ents := pad.toArray
  let qb := Q.blocks.toArray
  let stK := K.psumA (qb.map fun B ↦ B.tw .K * B.size) Q.nInK
  (Array.range qb.size).map fun b ↦
    let B := qb.getD b default
    let tp := B.tpl.toArray
    let rk := K.psumA (tp.map (Row.w .K)) 0
    tp.map fun r ↦
      match r.op with
      | .readd .. =>
        let a := r.args.getD 0 default
        let srcL : Option (ℕ × ℕ) :=
          if a.base == qt then some (0, 0) else if a.base == qt + 1 then some (1, 0) else
          -- a cell of this block's iteration: its writer
          let st := stK.getD b 0
          if a.base ≥ st && a.base < st + B.tw .K then
            match (List.range tp.size).find? fun t' ↦ rk.getD t' 0 == a.base - st && (tp.getD t' default).w .K == 1 with
            | some t' =>
              let r' := tp.getD t' default
              match r'.op with
              | .lin k _ =>
                let a' := r'.args.getD 0 default
                match gpowL k with
                | some l => if a'.base == qt then some (0, l) else if a'.base == qt + 1 then some (1, l) else none
                | none => none
              | _ => none
            | none => none
          else none
        srcL.map fun (src, l) ↦ (List.range B.size).map fun jf ↦
          let e := ents.getD jf (0, 0, 0)
          (if src == 0 then e.1 else e.2.1) + l
      | _ => none

/-- **QLT's static `readd` targets** in `Q` (blocks whose `readd` reads QLT's `α`/`β` columns), per block and
template row (a table: built once). -/
def qltAlias (C : QCfg) (Q : Program) : Array (Array (Option (List ℕ))) := qltAliasE C Q (Lvm.QLink.qltPadded C.p (lay C))

/-- `qltAlias` on `qltPaddedF` (B1-IX-S: `qltPadded` costs 3.4 s at P20 [measured]). -/
def qltAliasF (C : QCfg) (Q : Program) : Array (Array (Option (List ℕ))) :=
  qltAliasE C Q (QTyped.qltPaddedF C.p (lay C))

theorem qltAliasF_eq (C : QCfg) (Q : Program) : qltAliasF C Q = qltAlias C Q := by
  unfold qltAliasF qltAlias
  rw [QTyped.qltPaddedF_eq]

/-- An auxiliary block with its free words moved by `d`. -/
def moveAux (d : ℕ) (A : ABlk) : ABlk :=
  let mv : AOp → AOp := fun
    | .word b s => .word (b + d) s
    | a => a
  ⟨A.l, A.rows.map fun r ↦ ⟨r.ops.map fun e ↦ (e.1, mv e.2.1, e.2.2)⟩⟩

/-- **The layout specification of a node program `Q` of `C`**, reference form (the bus program `QT` or the B
program `QB`): the input regions, QLT's aliases, `BITS` as typed rows (B1-Q's `bitsAux`, 64 words per real row). -/
def specQRef (C : QCfg) (Q : Program) : LSpec :=
  let al := qltAlias C Q
  -- B1-Q's blocks per class at base `0`, built once, then moved to the solver's bases (`QTyped.bitsAux C bw`)
  let blks0 : Array (List ABlk) := ((bspecs C QTyped.noData).map fun S ↦ S.ablks 0).toArray
  ⟨inRegs C, fun b t ↦ (al.getD b #[]).getD t none, QTyped.bitsWords C,
    fun bw ↦ (List.range blks0.size).flatMap (fun k ↦ (blks0.getD k []).map (moveAux (bw k))), qltCst C,
    inLanesQ⟩

/-- **The layout specification of a node program `Q` of `C`**: `specQRef` (`specQ_eq`) with the `BITS` classes'
cell functions and QLT's entries computed on their parameters once (B1-IX-S: `bspecsF`, `qltAliasF`, `qltCstF`). -/
def specQ (C : QCfg) (Q : Program) : LSpec :=
  let al := qltAliasF C Q
  let bs := QTyped.bspecsF C QTyped.noData
  let blks0 : Array (List ABlk) := (bs.map fun S ↦ S.ablks 0).toArray
  ⟨inRegs C, fun b t ↦ (al.getD b #[]).getD t none, bs.map fun S ↦ 64 * S.n,
    fun bw ↦ (List.range blks0.size).flatMap (fun k ↦ (blks0.getD k []).map (moveAux (bw k))), qltCstF C,
    inLanesQ⟩

theorem specQ_eq (C : QCfg) (Q : Program) : specQ C Q = specQRef C Q := by
  unfold specQ specQRef
  rw [qltAliasF_eq, QTyped.bspecsF_eq, qltCstF_eq]
  rfl

/-- **The typed layout of the B program `QB C T`** (the dense intervals to a fixpoint; offline). -/
def layB (C : QCfg) (T : QTyped.TData) : Lay := let Q := QTyped.QB C T; mkLay Q (specQ C Q)

/-- **The typed layout of `QB C T` on frozen dense intervals** `dints` (the fixpoint's result, a record as
`QData`: what V and the prover build at start-up). -/
def layBD (C : QCfg) (T : QTyped.TData) (dints : Array (Ty × ℕ × ℕ)) : Lay :=
  let Q := QTyped.QB C T; (mkLayD Q (specQ C Q) dints).1

end Lvm.Typed
