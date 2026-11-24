-- New for lvm6 (GSP, guard speed): NODE5b's `asmB6` with `Q.cells .K` from the prefix sums and the blocks' `tw .K` in one pass each
-- (`Lvm6GspRows`): `asmB6` computed `Q.cells .K` twice and `readdChk6F` mapped every block through `Block.tw`
-- (about 190 ms a pass over the deployed program's rows). No statement changes.
import Lvm6NodeAsmChk
import Lvm6GspRows

/-!
# `asmB6H` (`asmB6`, the Bool of `asmChk6`)

* `allRk`, `anyRk` (**`allRk_eq`**, **`anyRk_eq`**: the walk with the running rank is the indexed `all`/`any` at
  `Block.rank`); `linOkK`, `aliasInstK`, `rdReaddK` (**`rdReaddK_eq`**), `rdRowK`,
  `readdChkK` (**`readdChkK_eq : readdChkK = readdChkP`**).
* **`asmB6H_eq : asmB6H Ti = (asmChk6 Ti).b`**.
-/

set_option autoImplicit false

namespace Lvm6.Gsp

open Lvm.Loop Lvm.Typed Lvm6.Node Lvm6.Node.Asm
open Lvm6.Ty (TInst6)

/-! ## The template walk with the running rank -/

/-- `f` at every row and its rank among the `K` writers (from `k`), the rank counted along the walk. -/
def allRk (f : Row → ℕ → Bool) : List Row → ℕ → Bool
  | [], _ => true
  | r :: rs, k => f r k && allRk f rs (k + wF .K r)

theorem rank_succ {B : Block} {n : ℕ} {r : Row} {rs : List Row} (h : B.tpl.drop n = r :: rs) :
    B.rank .K (n + 1) = B.rank .K n + r.w .K := by
  have hr : B.tpl[n]? = some r := by rw [← List.head?_drop, h, List.head?_cons]
  rw [Block.rank, Block.rank, List.take_add_one, hr, Option.toList_some, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

theorem allRk_drop (f : Row → ℕ → Bool) (B : Block) : ∀ (rs : List Row) (n : ℕ), B.tpl.drop n = rs →
    allRk f rs (B.rank .K n) = (rs.zipIdx n).all fun tx ↦ f tx.1 (B.rank .K tx.2)
  | [], _, _ => rfl
  | r :: rs, n, h => by
    have h' : B.tpl.drop (n + 1) = rs := by rw [← List.drop_drop, h, List.drop_one, List.tail_cons]
    rw [allRk, List.zipIdx_cons, List.all_cons, wF_eq, ← rank_succ h, allRk_drop f B rs (n + 1) h']

/-- **The walk is the indexed `all` at `Block.rank`.** -/
theorem allRk_eq (f : Row → ℕ → Bool) (B : Block) :
    allRk f B.tpl 0 = B.tpl.zipIdx.all fun tx ↦ f tx.1 (B.rank .K tx.2) := by
  have h0 : B.rank .K 0 = 0 := by simp [Block.rank]
  have h := allRk_drop f B B.tpl 0 List.drop_zero
  rw [h0] at h
  exact h

/-- `f` at some row and its rank among the `K` writers (from `k`), the rank counted along the walk. -/
def anyRk (f : Row → ℕ → Bool) : List Row → ℕ → Bool
  | [], _ => false
  | r :: rs, k => f r k || anyRk f rs (k + wF .K r)

theorem anyRk_drop (f : Row → ℕ → Bool) (B : Block) : ∀ (rs : List Row) (n : ℕ), B.tpl.drop n = rs →
    anyRk f rs (B.rank .K n) = (rs.zipIdx n).any fun tx ↦ f tx.1 (B.rank .K tx.2)
  | [], _, _ => rfl
  | r :: rs, n, h => by
    have h' : B.tpl.drop (n + 1) = rs := by rw [← List.drop_drop, h, List.drop_one, List.tail_cons]
    rw [anyRk, List.zipIdx_cons, List.any_cons, wF_eq, ← rank_succ h, anyRk_drop f B rs (n + 1) h']

theorem anyRk_eq (f : Row → ℕ → Bool) (B : Block) :
    anyRk f B.tpl 0 = B.tpl.zipIdx.any fun tx ↦ f tx.1 (B.rank .K tx.2) := by
  have h0 : B.rank .K 0 = 0 := by simp [Block.rank]
  have h := anyRk_drop f B B.tpl 0 List.drop_zero
  rw [h0] at h
  exact h

/-- `linOkP`'s test of one row at its rank `rk` (`j` the loop index of `jf`). -/
def linRowK (cs : ℕ → Option Lvm.FK) (st tw jf a e : ℕ) (j : List ℕ) (r : Row) (rk : ℕ) : Bool :=
  match r.op, r.args with
  | .lin k k', [α₀, α₁] =>
    r.ty == .K && k' == 0 && α₀.ty == .K && α₁.ty == .K && α₀.at j == α₁.at j &&
      st + tw * jf + rk == a &&
      [1, 2, 3, 4].any fun l ↦ decide (l ≤ e) && k == Lvm.Loop.Build.gpow l + 1 &&
        cs (α₀.at j) == some (Lvm.Loop.Build.gpow (e - l))
  | _, _ => false

/-- `linOkP`, the template walked with its running rank. -/
def linOkK (cs : ℕ → Option Lvm.FK) (B : Block) (st tw jf a e : ℕ) : Bool :=
  anyRk (linRowK cs st tw jf a e (unflat B.dims jf)) B.tpl 0

theorem linOkK_eq (cs : ℕ → Option Lvm.FK) (B : Block) (st tw jf a e : ℕ) :
    linOkK cs B st tw jf a e = linOkP cs B st tw jf a e := by
  simp only [linOkK, linOkP, anyRk_eq]
  rfl

/-- `o == some (g^e)`, the power only when `o` is a value. -/
def eqGpow (o : Option Lvm.FK) (e : ℕ) : Bool :=
  match o with
  | some v => v == Lvm.Loop.Build.gpow e
  | none => false

theorem eqGpow_eq (o : Option Lvm.FK) (e : ℕ) : eqGpow o e = (o == some (Lvm.Loop.Build.gpow e)) := by
  cases o <;> simp [eqGpow]

/-- `aliasInstP` with `linOkK` and `eqGpow`. -/
def aliasInstK (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (cK : ℕ) (Bq : Block) (st twq jf a c e : ℕ) : Bool :=
  decide (e < cK) && (cs e).isNone && (cs c).isNone && wk c == wk e &&
    (eqGpow (cs a) e || linOkK cs Bq st twq jf a e)

/-- `rdReaddP` with `aliasInstK`. -/
def rdReaddK (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (cK : ℕ) (B Bq : Block) (st tw twq rk : ℕ)
    (r : Row) (src : CSrc) : Bool :=
  r.ty == .K && (r.args.getD 0 default).ty == .K &&
    match src with
    | .alias tgt => decide (tgt.length = B.size) && tgt.zipIdx.all fun x ↦
        aliasInstK cs wk cK Bq st twq x.2 ((r.args.getD 0 default).at (unflat B.dims x.2)) (st + tw * x.2 + rk) x.1
    | _ => (List.range B.size).all fun jf ↦
        capInstP Ti cs wk jf ((r.args.getD 0 default).at (unflat B.dims jf)) (st + tw * jf + rk)

theorem rdReaddK_eq (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (cK : ℕ) (B Bq : Block)
    (st tw twq rk : ℕ) (r : Row) (src : CSrc) :
    rdReaddK Ti cs wk cK B Bq st tw twq rk r src = rdReaddP Ti cs wk cK B Bq st tw twq rk r src := by
  simp only [rdReaddK, rdReaddP, aliasInstK, aliasInstP, linOkK_eq, eqGpow_eq]
  rfl

/-- `rdRowP` at the row's rank `k`. -/
def rdRowK (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (cK : ℕ) (B : Block) (b : ℕ) (Bq : Block)
    (st tw twq : ℕ) (r : Row) (k : ℕ) : Bool :=
  match r.op with
  | .readd _ _ => rdReaddK Ti cs wk cK B Bq st tw twq k r ((Ti.lay.blocks.getD b default).srcK.getD k default)
  | _ => true

/-- `readdChkP`, each template walked with its running rank. -/
def readdChkK (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (cK : ℕ) (stf twf : ℕ → ℕ) : Bool :=
  Ti.Q.blocks.zipIdx.all fun bx ↦
    allRk (rdRowK Ti cs wk cK bx.1 bx.2 (Ti.Q.blk bx.2) (stf bx.2) (twf bx.2) (twf bx.2)) bx.1.tpl 0

theorem readdChkK_eq (Ti : TInst6) (cs : ℕ → Option Lvm.FK) (wk : ℕ → ℕ) (cK : ℕ) (stf twf : ℕ → ℕ) :
    readdChkK Ti cs wk cK stf twf = readdChkP Ti cs wk cK stf twf := by
  simp only [readdChkK, readdChkP, rdBlkP, allRk_eq, rdRowK, rdReaddK_eq]
  rfl

/-! ## `asmB6` -/

/-- **`asmB6`**: the cell count once, the blocks' `tw .K` by `twF`, the templates walked with the rank. -/
def asmB6H (Ti : TInst6) : Bool :=
  let tws := Ti.Q.blocks.map (twF .K)
  let ps := stPsW Ti.Q tws
  let twA := tws.toArray
  let cK := ps.getD Ti.Q.blocks.length 0
  decide (cK < 2 ^ 64 - 1) && decide (Dep.sbC + 2 ^ 18 ≤ cK) &&
    readdChkK Ti (cstOfA (Ti.lay.cst.map fun r ↦ (r.1, r.2.toArray))) (wordKO (Lvm.Typed.K.fl_ownL Ti.lay .K) Ti.lay)
      cK (stOf Ti.Q ps) (fun b ↦ twA.getD b 0)

theorem asmB6H_eq (Ti : TInst6) : asmB6H Ti = (asmChk6 Ti).b := by
  have hc : (stPsW Ti.Q (Ti.Q.blocks.map (·.tw .K))).getD Ti.Q.blocks.length 0 = Ti.Q.cells .K := cells_stOf Ti.Q
  simp only [asmB6H, asmChk6, Lvm6.Node.Chk.ofBool, asmB6, twF_fun, hc, readdChk6F, readdChk6F.readdGo,
    readdChk6F.readdGo2, readdChkK_eq]

end Lvm6.Gsp
