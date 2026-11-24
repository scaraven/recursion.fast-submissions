-- New for lvm6 (GSP, guard speed): GRD's `grdB` with its template walks in one pass each. `wfB` took `tw .K`,
-- `tw .E` of every block twice (the template walk's arguments and `Ptr.advBs`) and advanced the row pointer through
-- a one-segment list; `noE3B` builds `List.range n` per row. The twins count by matching (`Lvm6GspRows`). No
-- statement changes.
import Lvm6NodeGuardC
import Lvm6GspRows

/-!
# `grdBH` (`grdB`)

* `advR` (**`advR_eq`**), `typeOkF` (**`typeOkF_eq`**), `rowOkH` (**`rowOkH_eq`**: `rowOkC` at counters), `tplOkLH`,
  `blocksOkLH` (**`blocksOkLH_eq`**), `wfBH`
  (**`wfBH_eq : wfBH Q = wfB Q`**).
* `argsKH` (**`argsKH_eq : argsKH r.args n = argsKB r n`**), `rowNoE3BH`, `noE3BH` (**`noE3BH_eq`**).
* `twinsTplH`, `twinsOkBH` (**`twinsOkBH_eq`**): the twin check by matching.
* **`grdBH_eq : grdBH Ti c = grdB Ti c`**.
* The auxiliary rows once: `auxOkX` (**`auxOkX_eq`**), **`okBX_eq : okBX lay Q = (lay.okB Q && auxN lay.aux)`**;
  `tplOkLN`, `blocksOkLN`, `wfBN` (**`wfBN_eq : wfBN Q = (wfBH Q && noE3Rows Q)`**: one walk of the templates);
  `grdBX` (`grdBH` without `auxN`, `wfBN` for `wfBH`, `noE3Rows`), **`grdB_of_grdBX : auxN Ti.lay.aux = true → grdBX Ti c = true → grdB Ti c = true`**.
-/

set_option autoImplicit false

namespace Lvm6.Gsp

open Lvm.Loop Lvm.Loop.Build Lvm.Typed Lvm6.Node.Dep
open Lvm6.Ty (TInst6)

/-! ## `wfB` -/

/-- The pointer after one row. -/
def advR (c : Ptr) (r : Row) : Ptr := ⟨c.k + wF .K r, c.e + wF .E r⟩

theorem advR_eq (c : Ptr) (r : Row) : advR c r = c.adv [.row r] := by
  simp [advR, Ptr.adv, segsW, Seg.w, wF_eq]

/-- `cl τ` from its two values. -/
def clAt (k e : ℕ) : Ty → ℕ
  | .K => k
  | .E => e

/-- Every operand is a `K` cell (`ts.all (· == .K)` on the operands' memories). -/
def allK : List Addr → Bool
  | [] => true
  | a :: as => (match a.ty with | .K => true | .E => false) && allK as

theorem allK_eq : ∀ as : List Addr, allK as = (as.map (·.ty)).all (· == .K)
  | [] => rfl
  | a :: as => by
    rw [allK, allK_eq as, List.map_cons, List.all_cons]
    cases a.ty <;> rfl

/-- `Row.typeOk` without the list of memories (but for `loadE`, `readd`). -/
def typeOkF (r : Row) : Bool :=
  match r.op with
  | .muladd => r.args.length == 3 && (r.ty == .E || allK r.args)
  | .lin .. => r.args.length == 2 && (r.ty == .E || allK r.args)
  | .assert0 => r.args.length == 2
  | .loadE => r.args.map (·.ty) == [.K, .K, .K] && r.ty == .E
  | .fixmul => r.args.length == 2 && (r.ty == .E || allK r.args)
  | .readd .. => r.args.map (·.ty) == [.K]
  | .e2 f _ => r.args.length == f.arity && allK r.args && r.ty == .K

theorem typeOkF_eq (r : Row) : typeOkF r = r.typeOk := by
  obtain ⟨op, ty, args⟩ := r
  cases op <;> simp only [typeOkF, Row.typeOk, allK_eq, List.length_map]

/-- `rowOkC` at the cells `clAt k e` defined before the row. -/
def rowOkH (k e : ℕ) (dims : List ℕ) (tK tE : ℕ) (r : Row) : Bool :=
  typeOkF r &&
  r.args.all (fun a => decide (a.base + maxExcess a.strides dims (twOf tK tE a.ty) < clAt k e a.ty)) &&
  match r.op with
  | .readd lo m => decide (lo + 2 ^ m ≤ clAt k e r.ty)
  | _ => true

theorem rowOkH_eq (p c : Ptr) (dims : List ℕ) (tK tE : ℕ) (r : Row) :
    rowOkH (p.k + c.k) (p.e + c.e) dims tK tE r = rowOkC (fun τ ↦ p.at τ + c.at τ) dims (twOf tK tE) r := by
  have e : clAt (p.k + c.k) (p.e + c.e) = fun τ ↦ p.at τ + c.at τ := by
    funext τ
    cases τ <;> rfl
  simp only [rowOkH, rowOkC, typeOkF_eq, e]
  rfl

/-- `tplOkL`, the cells defined before the row as two counters (from `p`). -/
def tplOkLH (dims : List ℕ) (tK tE : ℕ) : ℕ → ℕ → List Row → Bool
  | _, _, [] => true
  | k, e, r :: rs => rowOkH k e dims tK tE r && tplOkLH dims tK tE (k + wF .K r) (e + wF .E r) rs

theorem tplOkLH_eq (p : Ptr) (dims : List ℕ) (tK tE : ℕ) :
    ∀ (c : Ptr) (rs : List Row), tplOkLH dims tK tE (p.k + c.k) (p.e + c.e) rs = tplOkL p dims tK tE c rs
  | _, [] => rfl
  | c, r :: rs => by
    rw [tplOkLH, tplOkL, rowOkH_eq, ← advR_eq, ← tplOkLH_eq p dims tK tE (advR c r) rs]
    simp only [advR, Nat.add_assoc]

/-- `blocksOkL`, each block's counts once. -/
def blocksOkLH : Ptr → List Block → Bool
  | _, [] => true
  | p, B :: bs =>
    let c := cntF B
    tplOkLH B.dims c.1 c.2.1 p.k p.e B.tpl && blocksOkLH ⟨p.k + c.1 * B.size, p.e + c.2.1 * B.size⟩ bs

theorem blocksOkLH_eq : ∀ (p : Ptr) (bs : List Block), blocksOkLH p bs = blocksOkL p bs
  | _, [] => rfl
  | p, B :: bs => by
    have e : (⟨p.k + B.tw .K * B.size, p.e + B.tw .E * B.size⟩ : Ptr) = p.advBs [B] := by simp [Ptr.advBs]
    have h := tplOkLH_eq p B.dims (B.tw .K) (B.tw .E) ⟨0, 0⟩ B.tpl
    simp only [Nat.add_zero] at h
    simp only [blocksOkLH, blocksOkL, cntF_eq, h, e, blocksOkLH_eq _ bs]

/-- **`wfB`, the counts in one pass.** -/
def wfBH (Q : Program) : Bool := blocksOkLH ⟨Q.nInK, Q.nInE⟩ Q.blocks

theorem wfBH_eq (Q : Program) : wfBH Q = wfB Q := blocksOkLH_eq _ _

/-! ## `noE3B` -/

/-- Operands `0 … n-1` of `as` are `K` cells (past the end: the default operand, a `K` cell). -/
def argsKH : List Addr → ℕ → Bool
  | _, 0 => true
  | [], _ + 1 => true
  | a :: as, n + 1 => a.ty == .K && argsKH as n

theorem argsKH_getD : ∀ (as : List Addr) (n : ℕ),
    argsKH as n = (List.range n).all fun k ↦ (as.getD k default).ty == .K
  | as, 0 => by cases as <;> rfl
  | [], n + 1 => by
    rw [argsKH, eq_comm, List.all_eq_true]
    intro _ _
    rfl
  | a :: as, n + 1 => by
    rw [argsKH, argsKH_getD as n, List.range_succ_eq_map, List.all_cons, List.all_map]
    rfl

theorem argsKH_eq (r : Row) (n : ℕ) : argsKH r.args n = argsKB r n := argsKH_getD r.args n

/-- `rowNoE3B` with `argsKH`. -/
def rowNoE3BH (r : Row) : Bool :=
  match r.op with
  | .muladd => argsKH r.args 3 && r.ty == .K
  | .lin _ _ => argsKH r.args 2 && r.ty == .K
  | .assert0 => argsKH r.args 2
  | .fixmul => argsKH r.args 2 && r.ty == .K
  | .e2 .mul false => argsKH r.args 6 && r.ty == .K
  | .e2 (.lin _ _ _) false => argsKH r.args 4 && r.ty == .K
  | _ => true

theorem rowNoE3BH_eq (r : Row) : rowNoE3BH r = rowNoE3B r := by
  obtain ⟨op, ty, args⟩ := r
  rcases op with _ | _ | _ | _ | _ | _ | ⟨f, h⟩
  all_goals try (simp only [rowNoE3BH, rowNoE3B, ← argsKH_eq]; done)
  cases f <;> cases h <;> simp only [rowNoE3BH, rowNoE3B, ← argsKH_eq]

theorem rowNoE3BH_fun : rowNoE3BH = rowNoE3B := funext rowNoE3BH_eq

/-- **`noE3B`, without index lists.** -/
def noE3BH (Q : Program) (lay : Lay) : Bool :=
  Q.blocks.all (fun B ↦ B.tpl.all rowNoE3BH) &&
    lay.aux.all fun A ↦ A.rows.all fun r ↦ r.ops.all fun e ↦ isKB e.2.2 && aopNoE3B e.2.1

theorem noE3BH_eq (Q : Program) (lay : Lay) : noE3BH Q lay = noE3B Q lay := by
  simp only [noE3BH, noE3B, rowNoE3BH_fun]

/-! ## `twinsOk` -/

/-- `twinsTpl` by matching on the row (no `Option` of the twin built per row). -/
def twinsTplH : List Row → Bool
  | [] => true
  | [r] =>
    match r.op with
    | .e2 _ _ => false
    | _ => true
  | r :: r' :: rs =>
    match r.op with
    | .e2 f false => r'.op == .e2 f true && r'.args == r.args && r'.ty == r.ty && twinsTplH rs
    | .e2 _ true => false
    | _ => twinsTplH (r' :: rs)

theorem twinsTplH_eq : ∀ rs : List Row, twinsTplH rs = twinsTpl rs
  | [] => rfl
  | [r] => by
    obtain ⟨op, ty, args⟩ := r
    cases op with
    | e2 f h => cases h <;> rfl
    | _ => rfl
  | r :: r' :: rs => by
    obtain ⟨op, ty, args⟩ := r
    cases op with
    | e2 f h =>
      cases h
      · simp [twinsTplH, twinsTpl, Op.twin?, twinsTplH_eq rs]
      · rfl
    | _ => simp [twinsTplH, twinsTpl, Op.twin?, Op.isHi, twinsTplH_eq (r' :: rs)]

/-- **`Program.twinsOk`** with `twinsTplH`. -/
def twinsOkBH (Q : Program) : Bool := Q.blocks.all fun B ↦ twinsTplH B.tpl

theorem twinsOkBH_eq (Q : Program) : twinsOkBH Q = twinsOkB Q := by
  simp only [twinsOkBH, twinsOkB, Program.twinsOk, twinsTplH_eq]

/-! ## The auxiliary rows walked once for `okB` and `noE3B` -/

theorem all_and2 {α : Type} (l : List α) (p q : α → Bool) :
    (l.all fun x ↦ p x && q x) = (l.all p && l.all q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, List.all_cons, ih]
    cases p a <;> cases q a <;> simp

/-- `noE3B`'s auxiliary part. -/
def auxN (As : List ABlk) : Bool :=
  As.all fun A ↦ A.rows.all fun r ↦ r.ops.all fun e ↦ isKB e.2.2 && aopNoE3B e.2.1

theorem auxN_cons (A : ABlk) (As : List ABlk) :
    auxN (A :: As) = ((A.rows.all fun r ↦ r.ops.all fun e ↦ isKB e.2.2 && aopNoE3B e.2.1) && auxN As) := rfl

theorem and_shuffle (a n c r m : Bool) : ((a && n) && c && (r && m)) = ((a && c && r) && (n && m)) := by
  cases a <;> cases n <;> cases c <;> cases r <;> cases m <;> rfl

theorem and_pull (x a n : Bool) : (x && (a && n)) = ((x && a) && n) := by
  cases x <;> cases a <;> cases n <;> rfl

theorem and_swap_right (p n y : Bool) : ((p && n) && y) = ((p && y) && n) := by
  cases p <;> cases n <;> cases y <;> rfl

/-- `auxOkH` and `auxN` in one walk of the auxiliary rows. -/
def auxOkX (G : ℕ → List XChunk) : ℕ → List ABlk → Bool
  | _, [] => true
  | k, A :: As =>
    (let m := 2 ^ A.l - 1
     A.rows.all fun r ↦ r.ops.all fun e ↦
      (decide (e.1 < 4) && aopFitsM m e.2.1) && (isKB e.2.2 && aopNoE3B e.2.1)) &&
      chunksCover A.l (G k) 0 A.rows.length && auxOkX G (k + 1) As

theorem auxOkX_eq (G : ℕ → List XChunk) :
    ∀ (k : ℕ) (As : List ABlk), auxOkX G k As = (auxOkH G k As && auxN As)
  | _, [] => rfl
  | k, A :: As => by
    rw [auxOkX, auxOkX_eq G (k + 1) As, auxOkH, auxN_cons]
    simp only [all_and2]
    exact and_shuffle _ _ _ _ _

/-- **`Lay.okB` and `noE3B`'s auxiliary part**, the auxiliary rows walked once. -/
def okBX (lay : Lay) (Q : Program) : Bool :=
  let G := grpX lay.xs
  lay.nInK == Q.nInK && lay.nInE == Q.nInE && lay.blocks.length == Q.blocks.length &&
    blocksOkH lay.nInK (fun k ↦ G.getD k []) 0 Q.nInK Q.nInE lay.blocks Q.blocks &&
    auxOkX (fun k ↦ G.getD k []) lay.blocks.length lay.aux &&
    xsSorted lay.xs && yregsSorted lay.yregs &&
    lay.inp.all dregFits && lay.dense.all dregFits && decide (lay.one < 2 ^ yVars) &&
    cstOkH lay.cst lay.nInK lay.blocks Q.blocks

theorem okBX_eq (lay : Lay) (Q : Program) : okBX lay Q = (lay.okB Q && auxN lay.aux) := by
  rw [← okBH_eq]
  simp only [okBX, okBH, auxOkX_eq]
  rw [and_pull _ _ (auxN lay.aux)]
  repeat rw [and_swap_right _ (auxN lay.aux)]

/-! ## `grdB` -/

/-- **`grdB`, its walks in one pass each.** -/
def grdBH (Ti : TInst6) (c : CellPar) : Bool :=
  wfBH Ti.Q && twinsOkBH Ti.Q && noE3BH Ti.Q Ti.lay && streamCellsB Ti c && sigCellsB Ti c

theorem grdBH_eq (Ti : TInst6) (c : CellPar) : grdBH Ti c = grdB Ti c := by
  rw [grdBH, grdB, wfBH_eq, twinsOkBH_eq, noE3BH_eq]

/-- `noE3B`'s template part. -/
def noE3Rows (Q : Program) : Bool := Q.blocks.all fun B ↦ B.tpl.all rowNoE3BH

theorem and_swap4 (a n r m : Bool) : ((a && n) && (r && m)) = ((a && r) && (n && m)) := by
  cases a <;> cases n <;> cases r <;> cases m <;> rfl

/-- `tplOkLH` and `rowNoE3BH` in one walk. -/
def tplOkLN (dims : List ℕ) (tK tE : ℕ) : ℕ → ℕ → List Row → Bool
  | _, _, [] => true
  | k, e, r :: rs =>
    (rowOkH k e dims tK tE r && rowNoE3BH r) && tplOkLN dims tK tE (k + wF .K r) (e + wF .E r) rs

theorem tplOkLN_eq (dims : List ℕ) (tK tE : ℕ) :
    ∀ (k e : ℕ) (rs : List Row), tplOkLN dims tK tE k e rs = (tplOkLH dims tK tE k e rs && rs.all rowNoE3BH)
  | _, _, [] => rfl
  | k, e, r :: rs => by
    rw [tplOkLN, tplOkLH, List.all_cons, tplOkLN_eq dims tK tE _ _ rs, and_swap4]

/-- `blocksOkLH` and `noE3Rows` in one walk. -/
def blocksOkLN : Ptr → List Block → Bool
  | _, [] => true
  | p, B :: bs =>
    let c := cntF B
    tplOkLN B.dims c.1 c.2.1 p.k p.e B.tpl && blocksOkLN ⟨p.k + c.1 * B.size, p.e + c.2.1 * B.size⟩ bs

theorem blocksOkLN_eq : ∀ (p : Ptr) (bs : List Block),
    blocksOkLN p bs = (blocksOkLH p bs && bs.all fun B ↦ B.tpl.all rowNoE3BH)
  | _, [] => rfl
  | p, B :: bs => by
    simp only [blocksOkLN, blocksOkLH, List.all_cons, tplOkLN_eq, blocksOkLN_eq _ bs, and_swap4]

/-- **`wfB` and `noE3B`'s template part**, one walk of the templates. -/
def wfBN (Q : Program) : Bool := blocksOkLN ⟨Q.nInK, Q.nInE⟩ Q.blocks

theorem wfBN_eq (Q : Program) : wfBN Q = (wfBH Q && noE3Rows Q) := blocksOkLN_eq _ _

/-- **`grdB` but `noE3B`'s auxiliary part** (`auxN`, walked by `okBX`), the templates walked once for `wfB` and
`noE3B`. -/
def grdBX (Ti : TInst6) (c : CellPar) : Bool :=
  wfBN Ti.Q && twinsOkBH Ti.Q && streamCellsB Ti c && sigCellsB Ti c

theorem grdB_of_grdBX {Ti : TInst6} {c : CellPar} (ha : auxN Ti.lay.aux = true) (h : grdBX Ti c = true) :
    grdB Ti c = true := by
  rw [← grdBH_eq]
  simp only [auxN] at ha
  simp only [grdBX, grdBH, wfBN_eq, noE3BH, noE3Rows, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨h.1.1.1.1, h.1.1.2⟩, h.1.1.1.2, ha⟩, h.1.2⟩, h.2⟩

end Lvm6.Gsp
