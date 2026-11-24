-- New for lvm6 (WP V1c3, moved from WP NODE5b's `Lvm6NodeAsmR`/`Lvm6NodeAsmG`, text unchanged): the run-time check of the
-- deployed node's `readd` instances (`readdChk6B`) and `AsmOk6`/`asmChk6`, below `Lvm6VGuard` so that the static guard
-- can carry `asmChk6` as a field (`StaticOk6.asm`). NODE3 (G0 item 1): `readdChk6F`, its run-time twin (`asmB6` calls it).
import Lvm6NodeMbT
import Lvm6NodeDeploy
import LvmQBuild
import Lvm6Chk
import LvmWiring

/-!
# The node's assembly check (`AsmOk6`, `asmChk6`, `readdChk6B`)

Moved from WP NODE5b (`Lvm6NodeAsmR`: `linOk6B`, `aliasInstB`, `capInstB`, `rdRowB`, `readdChk6B`; `Lvm6NodeAsmG`:
`AsmOk6`, `asmB6`, `asmB6_sound`, `asmChk6`), names, namespace and text unchanged.
-/

set_option autoImplicit false

namespace Lvm6.Node.Asm

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Typed LeanVM.Protocol
open Lvm6.Ty (TInst6)
open Lvm6.Node.Mb Lvm6.Node.Dep Lvm6.Node

/-! ## The check -/

/-- **QLT's address row** at iteration `jf` of block `b` (season 1's `linOkB` on the layout's constants): a `lin`
row of the block whose result cell is `a`, on one cell `α` twice, `k = g^l + 1`, `k' = 0`, `α` the constant
`g^(e − l)` (`l ≤ 4`, `l ≤ e`), so `a = g^e`. -/
def linOk6B (Q : Program) (lay : Lay) (b jf a e : ℕ) : Bool :=
  let B := Q.blk b
  let j := unflat B.dims jf
  B.tpl.zipIdx.any fun x ↦
    match x.1.op, x.1.args with
    | .lin k k', [α₀, α₁] =>
      x.1.ty == .K && k' == 0 && α₀.ty == .K && α₁.ty == .K && α₀.at j == α₁.at j &&
        Q.start .K b + B.tw .K * jf + B.rank .K x.2 == a &&
        [1, 2, 3, 4].any fun l ↦ decide (l ≤ e) && k == Build.gpow l + 1 &&
          lay.cst? (α₀.at j) == some (Build.gpow (e - l))
    | _, _ => false

/-- **A static read** (address cell `a`, result cell `c`, target `e`): `e` an existing cell, neither `e` nor `c` a
constant, `c`'s word is `e`'s, the address is `g^e` (a constant, or QLT's address row). -/
def aliasInstB (Q : Program) (lay : Lay) (b jf a c e : ℕ) : Bool :=
  decide (e < Q.cells .K) && (lay.cst? e).isNone && (lay.cst? c).isNone && lay.wordK c == lay.wordK e &&
    (lay.cst? a == some (Build.gpow e) || linOk6B Q lay b jf a e)

/-- **A cap read** at iteration `jf` (address cell `a`, result cell `c`): both cells committed words (no constant,
source `com`), and some read table of `Ti.mbT` (after the seeds) has `jf` among its rows and its address and value
columns at `a`'s and `c`'s `C_main` words minus `jf` (the words are looked up once, not per table). -/
def capInstB (Ti : TInst6) (jf a c : ℕ) : Bool :=
  let ya := Ti.lay.wordK a
  let yc := Ti.lay.wordK c
  let ca := Ti.comW ya
  let cc := Ti.comW yc
  (Ti.lay.cst? a).isNone && (Ti.lay.cst? c).isNone && decide (Ti.src? ya = some .com) &&
    decide (Ti.src? yc = some .com) &&
    (List.range capTaus6.length).any fun k ↦
      match Ti.mbT[seedBlocks6.length + k]? with
      | some T => decide (jf < 2 ^ T.τ) &&
        match T.cols with
        | [.com false wa, .com false wv, _] => decide (ca = wa + jf) && decide (cc = wv + jf)
        | _ => false
      | none => false

/-- **A template row's `readd` instances** (block `B` = `Ti.Q`'s block `b`, row `r` = its template row `t`): a `K`
row on a `K` address; aliased by the layout: every iteration a static read of its target; otherwise every iteration
a cap read. -/
def rdRowB (Ti : TInst6) (B : Block) (b : ℕ) (r : Row) (t : ℕ) : Bool :=
  match r.op with
  | .readd _ _ =>
    r.ty == .K && (r.args.getD 0 default).ty == .K &&
      match (Ti.lay.blocks.getD b default).srcK.getD (B.rank .K t) default with
      | .alias tgt => decide (tgt.length = B.size) && tgt.zipIdx.all fun x ↦
          aliasInstB Ti.Q Ti.lay b x.2 ((r.args.getD 0 default).at (unflat B.dims x.2))
            (Ti.Q.start .K b + B.tw .K * x.2 + B.rank .K t) x.1
      | _ => (List.range B.size).all fun jf ↦
          capInstB Ti jf ((r.args.getD 0 default).at (unflat B.dims jf)) (Ti.Q.start .K b + B.tw .K * jf + B.rank .K t)
  | _ => true

/-- **Every `readd` instance reads its cell** (run time): one pass over the blocks' template rows. -/
def readdChk6B (Ti : TInst6) : Bool :=
  Ti.Q.blocks.zipIdx.all fun bx ↦ bx.1.tpl.zipIdx.all fun tx ↦ rdRowB Ti bx.1 bx.2 tx.1 tx.2

/-! ## The run-time twin (NODE3, G0 item 1)

`readdChk6B` recomputed `Q.start .K b` (a pass over every earlier template row), `Q.cells .K` and `B.tw .K` per
`readd` instance and once more per template row in `linOk6B`; per instance `Lay.wordK` scans the blocks with
`List.getD` (`owner?`) and `Lay.cst?` indexes the QLT constants with `List.getD`. `readdChkP` is `readdChk6B` with
these as arguments (`readdChkP_orig`, `rfl`); `readdChk6F` passes prefix sums (`psumA`), the owners list
(`fl_ownL`, once), the constants as arrays, each proved equal (`stOf_eq`, `wordKO_eq`, `cstOfA_eq`), so
`readdChk6F_eq : readdChk6F = readdChk6B`; `asmB6` below (the guard) calls the twin (INT5: the core's source rule
bans the compiler-rewrite attribute). No statement changes. -/

/-- `linOk6B`, the constants `cs`, `B := Q.blk b`, `Q.start .K b` and `B.tw .K` given. -/
def linOkP (cs : ℕ → Option FK) (B : Block) (st tw jf a e : ℕ) : Bool :=
  let j := unflat B.dims jf
  B.tpl.zipIdx.any fun x ↦
    match x.1.op, x.1.args with
    | .lin k k', [α₀, α₁] =>
      x.1.ty == .K && k' == 0 && α₀.ty == .K && α₁.ty == .K && α₀.at j == α₁.at j &&
        st + tw * jf + B.rank .K x.2 == a &&
        [1, 2, 3, 4].any fun l ↦ decide (l ≤ e) && k == Build.gpow l + 1 &&
          cs (α₀.at j) == some (Build.gpow (e - l))
    | _, _ => false

/-- `aliasInstB`, the constants `cs`, the words `wk`, `Q.cells .K` and `linOk6B`'s values given. -/
def aliasInstP (cs : ℕ → Option FK) (wk : ℕ → ℕ) (cK : ℕ) (Bq : Block) (st twq jf a c e : ℕ) : Bool :=
  decide (e < cK) && (cs e).isNone && (cs c).isNone && wk c == wk e &&
    (cs a == some (Build.gpow e) || linOkP cs Bq st twq jf a e)

/-- `capInstB`, the constants `cs` and the words `wk` given. -/
def capInstP (Ti : TInst6) (cs : ℕ → Option FK) (wk : ℕ → ℕ) (jf a c : ℕ) : Bool :=
  let ya := wk a
  let yc := wk c
  let ca := Ti.comW ya
  let cc := Ti.comW yc
  (cs a).isNone && (cs c).isNone && decide (Ti.src? ya = some .com) &&
    decide (Ti.src? yc = some .com) &&
    (List.range capTaus6.length).any fun k ↦
      match Ti.mbT[seedBlocks6.length + k]? with
      | some T => decide (jf < 2 ^ T.τ) &&
        match T.cols with
        | [.com false wa, .com false wv, _] => decide (ca = wa + jf) && decide (cc = wv + jf)
        | _ => false
      | none => false

/-- `rdRowB`'s `readd` case, the row's source and rank and the block's values given. -/
def rdReaddP (Ti : TInst6) (cs : ℕ → Option FK) (wk : ℕ → ℕ) (cK : ℕ) (B Bq : Block) (st tw twq rk : ℕ) (r : Row)
    (src : CSrc) : Bool :=
  r.ty == .K && (r.args.getD 0 default).ty == .K &&
    match src with
    | .alias tgt => decide (tgt.length = B.size) && tgt.zipIdx.all fun x ↦
        aliasInstP cs wk cK Bq st twq x.2 ((r.args.getD 0 default).at (unflat B.dims x.2)) (st + tw * x.2 + rk) x.1
    | _ => (List.range B.size).all fun jf ↦
        capInstP Ti cs wk jf ((r.args.getD 0 default).at (unflat B.dims jf)) (st + tw * jf + rk)

/-- `rdRowB`, the block's values given (rank and source only on `readd` rows). -/
def rdRowP (Ti : TInst6) (cs : ℕ → Option FK) (wk : ℕ → ℕ) (cK : ℕ) (B : Block) (b : ℕ) (Bq : Block)
    (st tw twq : ℕ) (r : Row) (t : ℕ) : Bool :=
  match r.op with
  | .readd _ _ =>
    rdReaddP Ti cs wk cK B Bq st tw twq (B.rank .K t) r
      ((Ti.lay.blocks.getD b default).srcK.getD (B.rank .K t) default)
  | _ => true

/-- One block of `readdChk6B`, its values given. -/
def rdBlkP (Ti : TInst6) (cs : ℕ → Option FK) (wk : ℕ → ℕ) (cK : ℕ) (B : Block) (b : ℕ) (Bq : Block)
    (st tw twq : ℕ) : Bool :=
  B.tpl.zipIdx.all fun tx ↦ rdRowP Ti cs wk cK B b Bq st tw twq tx.1 tx.2

/-- **`readdChk6B` with its sums, constants and words as arguments** (`twf b` = block `b`'s `tw .K`). -/
def readdChkP (Ti : TInst6) (cs : ℕ → Option FK) (wk : ℕ → ℕ) (cK : ℕ) (stf twf : ℕ → ℕ) : Bool :=
  Ti.Q.blocks.zipIdx.all fun bx ↦ rdBlkP Ti cs wk cK bx.1 bx.2 (Ti.Q.blk bx.2) (stf bx.2) (twf bx.2) (twf bx.2)

theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

theorem readdChkP_orig (Ti : TInst6) :
    readdChk6B Ti = readdChkP Ti Ti.lay.cst? Ti.lay.wordK (Ti.Q.cells .K) (Ti.Q.start .K)
      (fun b ↦ (Ti.Q.blk b).tw .K) := by
  unfold readdChk6B readdChkP
  apply all_congr_mem
  intro bx hm
  have hb : Ti.Q.blk bx.2 = bx.1 := by
    rw [List.mem_zipIdx_iff_getElem?] at hm
    simp [Program.blk, List.getD_eq_getElem?_getD, hm]
  have e : rdBlkP Ti Ti.lay.cst? Ti.lay.wordK (Ti.Q.cells .K) bx.1 bx.2 (Ti.Q.blk bx.2) (Ti.Q.start .K bx.2)
      ((Ti.Q.blk bx.2).tw .K) ((Ti.Q.blk bx.2).tw .K) =
      rdBlkP Ti Ti.lay.cst? Ti.lay.wordK (Ti.Q.cells .K) bx.1 bx.2 (Ti.Q.blk bx.2) (Ti.Q.start .K bx.2)
      (bx.1.tw .K) ((Ti.Q.blk bx.2).tw .K) := by rw [hb]
  rw [e]
  rfl

/-- The constants from arrays. -/
def cstOfA (cA : List (ℕ × Array FK)) (n : ℕ) : Option FK :=
  (cA.find? fun r ↦ decide (r.1 ≤ n ∧ n < r.1 + r.2.size)).map fun r ↦ r.2.getD (n - r.1) 0

theorem cstOfA_eq (lay : Lay) : cstOfA (lay.cst.map fun r ↦ (r.1, r.2.toArray)) = lay.cst? := by
  funext n
  unfold cstOfA Lay.cst?
  rw [List.find?_map]
  simp only [Function.comp_def, List.size_toArray, Option.map_map]
  congr 1
  funext r
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `Lay.wordK` with the owners list given (`fl_ownL lay .K`, built once). -/
def wordKO (ol : List (ℕ × ℕ × ℕ)) (lay : Lay) (n : ℕ) : ℕ :=
  match (ol.find? fun x ↦ decide (x.1 ≤ n ∧ n < x.2.1)).map (·.2.2) with
  | some b =>
    let B := lay.blocks.getD b default
    let off := n - B.stK
    match B.srcK.getD (off % B.twK) default with
    | .slot s => lay.wordC B .K n s (off / B.twK) 0
    | .alias tgt => lay.wordD .K (tgt.getD (off / B.twK) 0) 0
    | .load _ => 0
  | none => lay.wordD .K n 0

theorem wordKO_eq (lay : Lay) : wordKO (Lvm.Typed.K.fl_ownL lay .K) lay = lay.wordK := by
  funext n
  unfold wordKO Lay.wordK
  rw [Lvm.Typed.K.fl_owner?_ownL]
  rfl

/-- `Q.start .K b` from the prefix sums (`Q.start` itself past the blocks, never reached). -/
def stOf (Q : Program) (ps : Array ℕ) (b : ℕ) : ℕ := if b ≤ Q.blocks.length then ps.getD b 0 else Q.start .K b

/-- The prefix sums of the blocks' `K` cell counts, from their `tw .K`s `tws`. -/
def stPsW (Q : Program) (tws : List ℕ) : Array ℕ :=
  Lvm.Typed.K.psumA (List.zipWith (· * ·) tws (Q.blocks.map (·.size))).toArray (Q.nIn .K)

/-- The prefix sums of the blocks' `K` cell counts. -/
def stPs (Q : Program) : Array ℕ := stPsW Q (Q.blocks.map (·.tw .K))

theorem stOf_eq (Q : Program) : stOf Q (stPs Q) = Q.start .K := by
  funext b
  unfold stOf
  split
  · rename_i hb
    rw [stPs, stPsW, Lvm.Typed.K.fl_psumA_getD _ _ _ (by simpa [List.length_zipWith] using hb), Program.start]
    simp [List.map_take, List.zipWith_map, List.zipWith_self]
  · rfl

theorem cells_stOf (Q : Program) : (stPs Q).getD Q.blocks.length 0 = Q.cells .K := by
  have := congrFun (stOf_eq Q) Q.blocks.length
  simpa [stOf, Program.cells] using this

/-- `(Q.blk b).tw .K` from the array of the blocks' `tw .K` (`0` past them, as the default block's). -/
theorem twA_eq (Q : Program) :
    (fun b ↦ (Q.blocks.map (·.tw .K)).toArray.getD b 0) = fun b ↦ (Q.blk b).tw .K := by
  funext b
  simp only [Program.blk, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases h : Q.blocks[b]? with
  | none => simp only [Option.map_none, Option.getD_none]; rfl
  | some B => simp [h]

/-- **`readdChk6B`, each sum once, the constants and the owners as arrays.** -/
def readdChk6F (Ti : TInst6) : Bool :=
  readdGo Ti (Ti.lay.cst.map fun r ↦ (r.1, r.2.toArray)) (Lvm.Typed.K.fl_ownL Ti.lay .K) (Ti.Q.blocks.map (·.tw .K))
where
  readdGo (Ti : TInst6) (cA : List (ℕ × Array FK)) (ol : List (ℕ × ℕ × ℕ)) (tws : List ℕ) : Bool :=
    readdGo2 Ti cA ol tws.toArray (stPsW Ti.Q tws)
  readdGo2 (Ti : TInst6) (cA : List (ℕ × Array FK)) (ol : List (ℕ × ℕ × ℕ)) (twA ps : Array ℕ) : Bool :=
    readdChkP Ti (cstOfA cA) (wordKO ol Ti.lay) (ps.getD Ti.Q.blocks.length 0) (stOf Ti.Q ps) (fun b ↦ twA.getD b 0)

theorem readdChk6F_eq : @readdChk6F = @readdChk6B := by
  funext Ti
  rw [readdChkP_orig, readdChk6F, readdChk6F.readdGo, readdChk6F.readdGo2, ← stPs, cstOfA_eq, wordKO_eq, cells_stOf,
    stOf_eq, twA_eq]

/-! ## The run-time facts this module adds (`asmChk6`) -/

/-- **The node's further run-time facts**: the `K` cell count below `g`'s order, the stream cells exist, every
`readd` instance checked (`readdChk6B`). -/
structure AsmOk6 (Ti : TInst6) : Prop where
  cellsLt : Ti.Q.cells .K < 2 ^ 64 - 1
  streamIn : sbC + 2 ^ 19 ≤ Ti.Q.cells .K
  readd : readdChk6B Ti = true

/-- The Bool of `AsmOk6` (two comparisons over the block count, one pass over the template rows). -/
def asmB6 (Ti : TInst6) : Bool :=
  decide (Ti.Q.cells .K < 2 ^ 64 - 1) && decide (sbC + 2 ^ 19 ≤ Ti.Q.cells .K) && readdChk6F Ti

theorem asmB6_sound {Ti : TInst6} (h : asmB6 Ti = true) : AsmOk6 Ti := by
  simp only [asmB6, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, readdChk6F_eq ▸ h.2⟩

/-- **`AsmOk6` as one `Chk`** (PF-0): to join the guard as a field. -/
def asmChk6 (Ti : TInst6) : Chk (AsmOk6 Ti) := Chk.ofBool (asmB6 Ti) asmB6_sound

end Lvm6.Node.Asm
