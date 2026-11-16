-- New for lvm2 MB-LIN (MBL-C, 2026-11-16): the node program at stage S2GL (`QL`): S2GU's (`QU`) without the child's
-- mini-bus table phase. After the mini-bus's GKR (`busGD`), the gadget `mbLinG` turns its three final claims into
-- three `K`-linear claims on `C_main` (`e3` sum claims), which stand where the 446 table claims stood in the opening.
import LvmE2QAsmU

/-!
# The S2GL node program

The child's mini-bus (211 tables, every table a full aligned block of each tree, every flush coordinate `Const`, `Col`
or `GCol`, no constraints) ends its GKR at the point `ζ` (`bc.pt`, `busDepth` coordinates) with the values `v_s` of
the three trees (push, pull, count). Each leaf is an affine map of one row of its table, so for side `s`

`v_s = (1 + Σ_b w_b) + Σ_b w_b·(c_{s,b} + Σ_i eq(α, i)·coord_{s,b,i}~(ζ.take τ_b))`, `w_b = eq(ζ.drop κ_b, off_b >> κ_b)`

(characteristic 2). **`mbLinG`** computes, from `α`, `β`, `ζ` and the `v_s`:

* the block weights `w_b` (`bwsG`, as the table phase did) and the padding masses `Σ_b w_b`;
* **the parts** of side `s`: for each table `t` (mini-bus order), each committed column `c` of `t` (column order) that
  a monomial of a side-`s` leaf form of `t` names, the coefficient `Σ w_b·k·eq(α, i)` over those monomials (`k` the
  monomial's constant, `i` its coordinate slot), on the block `⟨τ_t, off_c⟩` at `ζ.take τ_t`;
* **the values** `v_s + 1 + Σ_b w_b + Σ_b w_b·(β + eq(α, 0)·sep_b + Σ_{const} k·eq(α, i) +
  Σ_{fixed} k·eq(α, i)·g^{base}·powEval(ζ.take τ)(g^{stride}))` for push and pull (`mbFix`'s closed form of the
  seeds' address columns, the `powEval` part once per `(stride, τ)`), `v_count + 1 + Σ_b w_b` for count.

Every grouping is a static plan of the shapes (`linPlan`): coefficients shared by the push and the pull side (the
same block weight and slot) are built once, as are the constants' classes and the fixed columns' sums.

The claims are `e3` sum claims on `C_main` (`ν = 23`): `C_main`'s opening takes them as it takes any sum claim on
regular blocks. They follow the typed phases' halves and precede the front's claims (`typedClaimsGL`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped

/-! ## The static plan -/

/-- A monomial of a leaf form: coordinate slot, constant, columns (`[]` a constant, `[c]` column `c`). -/
abbrev LMon := Nat × FK × List Nat

/-- The monomials of a coordinate polynomial at slot `i`. -/
def monsAt (i : Nat) (P : CPoly) : List LMon := P.map fun m => (i, m.1, m.2)

/-- **The non-constant-term monomials of a block's leaf form** on the push (`true`) or pull side
(`leafForm eqα β key cnt` is `β + eq(α, 0)·sep` plus these, each times `eq(α, i)`). -/
def leafMons (b : SBlk) (push : Bool) : List LMon :=
  monsAt 1 b.key.addr ++ monsAt 2 (if push then cntPush b else CPoly.var b.col) ++
    b.key.val.zipIdx.flatMap fun (P, l) => monsAt (3 + l) P

/-- A coefficient's terms: (index of the block weight in `wpp ++ wc`, `(slot, k)` or `none` for weight one). -/
abbrev CKey := List (Nat × Option (Nat × FK))

/-- The empty shape (past the list's end). -/
def shape0 : TShape := ⟨0, [], [], [], []⟩

/-- Column `c` of shape `t`, when committed to `C_main`: its offset. -/
def comOff (t : TShape) (c : Nat) : Option Nat :=
  match t.cols.getD c none with
  | some (false, off) => some off
  | _ => none

/-- The push/pull blocks of table `j` with their weight indices. -/
def ppOf (S : List TShape) (j : Nat) : List (SBlk × Nat) :=
  ((ppS S).zipIdx.filter fun x => x.1.1.tab == j).map fun x => (x.1.1, x.2)

/-- The count blocks of table `j` with their weight indices (after the push/pull weights). -/
def cntOf (S : List TShape) (j : Nat) : List ((Nat × Nat × Nat) × Nat) :=
  ((cS S).zipIdx.filter fun x => x.1.1.1 == j).map fun x => (x.1.1, (ppS S).length + x.2)

/-- **The key of column `c`'s coefficient** on side `s` (`0` push, `1` pull, `2` count) of table `j`. -/
def colKey (S : List TShape) (s j c : Nat) : CKey :=
  if s = 2 then (cntOf S j).filterMap fun x => if x.1.2.2 = c then some (x.2, none) else none
  else (ppOf S j).flatMap fun x =>
    (leafMons x.1 (s = 0)).filterMap fun m => if m.2.2 = [c] then some (x.2, some (m.1, m.2.1)) else none

/-- **The parts' plan** of side `s`: `(table, column, key)` for each committed column with a nonzero key. -/
def partsPlan (S : List TShape) (s : Nat) : List (Nat × Nat × CKey) :=
  S.zipIdx.flatMap fun (t, j) => (List.range t.cols.length).filterMap fun c =>
    match comOff t c with
    | some _ => if colKey S s j c = [] then none else some (j, c, colKey S s j c)
    | none => none

/-- The distinct coefficient keys of the three sides. -/
def keysPlan (S : List TShape) : List CKey :=
  ((List.range 3).flatMap fun s => (partsPlan S s).map (·.2.2)).eraseDups

/-- The distinct `(slot, k)` with `k ≠ 1` of the coefficient keys and the fixed monomials. -/
def ekPlan (S : List TShape) (fx : List (Nat × FK)) : List (Nat × FK) :=
  (((keysPlan S).flatMap fun k => k.filterMap (·.2)) ++ fx).eraseDups.filter fun x => x.2 != 1

/-- A constant class: separator and constant monomials `(slot, k)`. -/
abbrev K0Key := FK × List (Nat × FK)

/-- The constant class of a block on side `s`. -/
def k0Of (b : SBlk) (push : Bool) : K0Key :=
  (b.key.sep, (leafMons b push).filterMap fun m => if m.2.2 = [] then some (m.1, m.2.1) else none)

/-- A fixed monomial of a block: (slot, k, base, stride, `τ`). -/
abbrev FxMon := Nat × FK × Nat × Nat × Nat

/-- The fixed monomials of block `b` on side `s` (`mbFix`'s `(table, column, base, stride)`). -/
def fxOf (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) (b : SBlk) (push : Bool) : List FxMon :=
  (leafMons b push).filterMap fun m => match m.2.2 with
    | [c] => match comOff (S.getD b.tab shape0) c with
      | some _ => none
      | none => (fix.find? fun f => f.1 == b.tab && f.2.1 == c).map fun f =>
        (m.1, m.2.1, f.2.2.1, f.2.2.2, (S.getD b.tab shape0).τ)
    | _ => none

/-- A fixed group: (slot, k, stride, `τ`) and its members `(weight index, base)`. -/
abbrev FxKey := (Nat × FK × Nat × Nat) × List (Nat × Nat)

/-- **The constants' plan** of side `s` (`0` push, `1` pull): the classes with their member weights, the fixed
groups. -/
def constPlan (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) (s : Nat) :
    List (K0Key × List Nat) × List FxKey :=
  let bs := (ppS S).zipIdx.map fun x => (x.1.1, x.2)
  let ks := (bs.map fun x => k0Of x.1 (s = 0)).eraseDups
  let fm := bs.flatMap fun x => (fxOf S fix x.1 (s = 0)).map fun f => (x.2, f)
  let gs := (fm.map fun x => (x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2)).eraseDups
  (ks.map fun k => (k, (bs.filter fun x => k0Of x.1 (s = 0) == k).map (·.2)),
   gs.map fun g => (g, (fm.filter fun x => (x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2) == g).map
     fun x => (x.1, x.2.2.2.1)))

/-- The distinct `(stride, τ)` of the fixed groups. -/
def powPlan (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat) :=
  ((constPlan S fix 0).2 ++ (constPlan S fix 1).2).map (fun g => (g.1.2.2.1, g.1.2.2.2)) |>.eraseDups

/-- The distinct weight sums of the constant classes and the distinct fixed groups' members. -/
def wsPlan (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) : List (List Nat) :=
  ((constPlan S fix 0).1 ++ (constPlan S fix 1).1).map (·.2) |>.eraseDups

def gsPlan (S : List TShape) (fix : List (Nat × Nat × Nat × Nat)) : List (List (Nat × Nat)) :=
  ((constPlan S fix 0).2 ++ (constPlan S fix 1).2).map (·.2) |>.eraseDups

/-! ## The gadget -/

/-- Cell `j` of a built list (`z` past its end). -/
def atC (z : Cell) (l : List Cell) (j : Nat) : Cell := l.getD j z

/-- `k·eq(α, i)`: the table's cell for `k = 1`, else the plan's. -/
def ekC (z : Cell) (eb : Nat) (ekP : List (Nat × FK)) (ek : List Cell) (x : Nat × FK) : Cell :=
  if x.2 == 1 then ec (eb + x.1) else atC z ek (ekP.idxOf x)

/-- A coefficient from its key: `Σ w_j·f_j` (`f_j = 1` for `none`; one weight with `f = 1` is the weight's cell). -/
def coefG (z : Cell) (w : List Cell) (f : Option (Nat × FK) → Cell) : CKey → BM Cell
  | [(j, none)] => pure (atC z w j)
  | ts => ts.foldlM (fun acc t => match t.2 with
      | none => add acc (atC z w t.1)
      | some _ => mulAdd .E (atC z w t.1) (f t.2) acc) z

/-- A constant class's value `β + eq(α, 0)·sep + Σ k·eq(α, i)`. -/
def k0G (be : Cell) (eb : Nat) (k : K0Key) : BM Cell := do
  let a ← lin .E k.1 0 be (ec eb)
  k.2.foldlM (fun acc m => lin .E m.2 0 acc (ec (eb + m.1))) a

/-- **The mini-bus's three claims** from its GKR's outputs (`bc`): push, pull, count, each an `e3` sum claim on
`C_main`. -/
def mbLinG (z o : Cell) (T : TData) (bc : BusC) : BM (List CClaim) := do
  let S := T.mbS
  let D := bc.pt.length
  let eb ← eqTab (fun i => bc.al.getD i z) z o false bc.al.length
  let facs ← facG bc.pt
  let lv := planLv D (allKO S)
  let lt ← lvlsG z o bc.pt lv
  let hi ← hisG z o facs (planHi D lv (allKO S))
  let wpp ← bwsG z o facs lt hi D ((ppS S).map fun bo => (bo.1.κ, bo.2))
  let wc ← bwsG z o facs lt hi D ((cS S).map fun bo => (bo.1.2.1, bo.2))
  let w := wpp ++ wc
  let spp ← sumG z wpp
  let scc ← sumG z wc
  -- the slots' scaled weights, the coefficients
  let cp0 := constPlan S T.mbFix 0
  let cp1 := constPlan S T.mbFix 1
  let ekP := ekPlan S ((cp0.2 ++ cp1.2).map fun g => (g.1.1, g.1.2.1))
  let ek ← seqAll (ekP.map fun x => lin .E x.2 0 z (ec (eb + x.1)))
  let f : Option (Nat × FK) → Cell := fun x => match x with
    | none => o
    | some y => ekC z eb ekP ek y
  let kP := keysPlan S
  let cs ← seqAll (kP.map (coefG z w f))
  -- the constants: classes, their weight sums, the fixed groups
  let ws ← seqAll ((wsPlan S T.mbFix).map fun l => sumG z (l.map (atC z w)))
  let pw ← seqAll ((powPlan S T.mbFix).map fun x => powColG z 0 x.1 (bc.pt.take x.2))
  let gs ← seqAll ((gsPlan S T.mbFix).map fun l => l.foldlM (fun acc m => lin .E (FK.x ^ m.2) 0 acc (atC z w m.1)) z)
  let valG (v : Cell) (cp : List (K0Key × List Nat) × List FxKey) : BM Cell := do
    let t ← lin .E 1 1 v spp
    let t ← cp.1.foldlM (fun acc k => do
      let c ← k0G bc.be eb k.1
      mulAdd .E c (atC z ws ((wsPlan S T.mbFix).idxOf k.2)) acc) t
    cp.2.foldlM (fun acc g => do
      let pg ← mulAdd .E (atC z pw ((powPlan S T.mbFix).idxOf (g.1.2.2.1, g.1.2.2.2)))
        (atC z gs ((gsPlan S T.mbFix).idxOf g.2)) z
      mulAdd .E (f (some (g.1.1, g.1.2.1))) pg acc) t
  let v0 ← valG (bc.vals.getD 0 z) cp0
  let v1 ← valG (bc.vals.getD 1 z) cp1
  let v2 ← lin .E 1 1 (bc.vals.getD 2 z) scc
  let parts (s : Nat) : List (Cell × Placement × List Cell) := (partsPlan S s).map fun x =>
    let t := S.getD x.1 shape0
    (atC z cs (kP.idxOf x.2.2), ⟨t.τ, (comOff t x.2.1).getD 0⟩, bc.pt.take t.τ)
  pure [⟨.main, .sum CMain.nu20 (parts 0), v0⟩, ⟨.main, .sum CMain.nu20 (parts 1), v1⟩,
    ⟨.main, .sum CMain.nu20 (parts 2), v2⟩]

/-! ## The typed phases and the program -/

/-- **The typed backend's verifier at S2GL** (`typedGT` with the mini-bus ending at its GKR, then `mbLinG`): the
typed outputs (no table point or evaluations) and the mini-bus's three claims. -/
def typedGL (T : TData) (p : Params) (pb n : Nat) (z o zk ok : Cell) : BM (TypedCT × List CClaim) := do
  let g := kc pb
  let L := busL p
  let z2 : C2 := ⟨zk, zk⟩
  let o2 : C2 := ⟨ok, zk⟩
  let zr ← zeroGT z2 g L
  let w ← wireGT z2 o2 g T pb n L zr.2
  let r ← relayGT z2 o2 g T L w.1 (w.2.2.getD 1 z2)
  qaccGT z2 o2 pb L zr.1 w.1 w.2.1
  let bc ← busGD T.mbD z o g (mbPT p)
  let cs ← mbLinG z o T bc
  pure (⟨zr.1, w.1, zr.2, w.2.1, w.2.2, r.1, r.2, bc, []⟩, cs)

/-- **The typed phases' end at S2GL** (after the mini-bus's GKR, its leaf read and trailing zero). -/
def typedEndL (T : TData) (p : Params) : Nat := busEndD T.mbD (mbPT p)

/-- **The typed phases' claims at S2GL**: S2GT's halves, then the mini-bus's three claims. -/
def typedClaimsGL (z : Cell) (z2 o2 : C2) (T : TData) (sOff : Nat) (t : TypedCT) (cs : List CClaim) :
    BM (List Lvm.Q2.FClaim) := do
  let l ← typedClaimsGT z z2 o2 T sOff t
  pure (l ++ cs.map Lvm.Q2.FClaim.e3)

/-- **Q_arith at S2GL** (`qarithG` with `typedGL`, `typedClaimsGL`). -/
def qarithL (C : QCfg) (T : TData) (pin : CClaim) (o : FrontF) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let ok ← const .K 1 (kc 0)
  let t ← typedGL T p (pbB C) (pubLanesTC p) z one zk ok
  let tc ← typedClaimsGL z ⟨zk, zk⟩ ⟨ok, zk⟩ T (layout0 p).s t.1 t.2
  let a ← addK (o.mb.getD 18 default) 1
  let b ← addK (o.mb.getD 19 default) 1
  let sK ← mulAdd .K a b zk
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨ok, zk⟩, true⟩
  Lvm.Q2.openGF (cfgMainF p (posBase C) (pwBase C)) (p.logN == 20 && p.nuMain == CMain.nu20) F pin (tc ++ o.cs)
    o.mb sK g

/-- **What follows Q_link and Q_sig at S2GL**: the root pin, the `E2` front `frontU`, `qarithL`. -/
def qaL (C : QCfg) (T : TData) : BM Unit := do
  let pin ← pinF C.p
  let o ← frontU C
  qarithL C T pin o

/-- **The S2GL node program** on the static data `T`. -/
def QL (C : QCfg) (T : TData) : Program := VF.toProgramF (nK C) 0 (do qlink C.p (lay C); let _ ← qsig (sigIn C); qaL C T)

end Lvm.E2Q
