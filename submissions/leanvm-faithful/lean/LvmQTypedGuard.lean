-- New for lvm2 (roll 8 = B1, B1-IX): the B program's one-pass builder, the typed static guard and its facts, generic
-- in the configuration (split out of `LvmQTypedInst` so that `P8`'s instance, `LvmQTypedInst8`, does not import
-- `P20`'s closed constants: every executable initialises the closed constants of the modules it imports).
import LvmQTypedData
import LvmVFastQ
import LvmBusILookup
import LvmWiringKF
import LvmTyped
import LvmQBuildWf
import LvmQTypedSWire

-- (GOLF2: 16 declarations that `certified` does not use moved verbatim to `LvmE2VWidthsFOff`, outside its import closure.)

-- ===== merged from `LvmFinSegs` (GOLF module merge: `LvmFinSegs.lean` is now a stub importing `LvmQTypedGuard`) =====
section
-- Split out of `LvmFinStatic` (lvm2 roll 8, B1-IX): QL's one-pass program check (`segsOkF`, `segsOkF_eq`), generic
-- in the program, so that the typed path's static guard (`LvmQTypedInst`) reads it without importing the bus
-- program's closed constants.

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## The program check in one pass per block (adapted from WP-16a-QFX's uncommitted
`LvmQAsmFactsFast`): `blockOkAt` recomputes a row's rank (a prefix of the template) per row, quadratic
in the template (6.3 s natively at `P20`); `rowsOkF` advances a pointer, with the block's widths
computed once. -/

/-- A block's rows from the pointer `c` on (the pointer advanced past each row). -/
def rowsOkF (dims : List Nat) (tw : Ty → Nat) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC c.at dims tw r && rowsOkF dims tw (c.adv [.row r]) rs

/-- The widths `k`, `e` as a function of the memory (built inside the per-row check: the compiler
must not re-evaluate `B.tw` per operand). -/
def twKE (k e : Nat) : Ty → Nat
  | .K => k
  | .E => e

/-- A block's rows with the widths passed as numbers (evaluated once, at the call). -/
def rowsOkKE (dims : List Nat) (k e : Nat) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC c.at dims (twKE k e) r && rowsOkKE dims k e (c.adv [.row r]) rs

theorem rowsOkKE_eq (dims : List Nat) (k e : Nat) : ∀ (c : Ptr) (rs : List Row),
    rowsOkKE dims k e c rs = rowsOkF dims (twKE k e) c rs
  | _, [] => rfl
  | c, r :: rs => by rw [rowsOkKE, rowsOkF, rowsOkKE_eq dims k e _ rs]

theorem twKE_tw (B : Block) : twKE (B.tw .K) (B.tw .E) = B.tw := by
  funext τ; cases τ <;> rfl

/-- `blockOkAt` in one pass. -/
def blockOkF (p : Ptr) (B : Block) : Bool := rowsOkKE B.dims (B.tw .K) (B.tw .E) p B.tpl

/-- `segsOk` with `blockOkF`. -/
def segsOkF : Ptr → List Seg → Bool
  | _, [] => true
  | p, .row r :: δ => rowOkC p.at [] (fun _ => 0) r && segsOkF (p.adv [.row r]) δ
  | p, .blk B :: δ => blockOkF p B && segsOkF (p.adv [.blk B]) δ

theorem adv_row_at (c : Ptr) (r : Row) (τ : Ty) : (c.adv [.row r]).at τ = c.at τ + r.w τ := by
  cases τ <;> simp [Ptr.adv, Ptr.at, segsW, Seg.w]

theorem rowsOkF_eq (dims : List Nat) (tw : Ty → Nat) : ∀ (c : Ptr) (rs : List Row),
    rowsOkF dims tw c rs = (List.range rs.length).all fun t =>
      rowOkC (fun τ => c.at τ + ((rs.take t).map (Row.w τ)).sum) dims tw (rs.getD t default)
  | c, [] => by simp [rowsOkF]
  | c, r :: rs => by
    rw [rowsOkF, rowsOkF_eq dims tw _ rs, List.length_cons, List.range_succ_eq_map, List.all_cons,
      List.all_map]
    have h0 : (fun τ => c.at τ + (((r :: rs).take 0).map (Row.w τ)).sum) = c.at := by
      funext τ; simp
    have h1 : ∀ t, (fun τ => c.at τ + (((r :: rs).take (t + 1)).map (Row.w τ)).sum) =
        fun τ => (c.adv [.row r]).at τ + ((rs.take t).map (Row.w τ)).sum := fun t => by
      funext τ; rw [adv_row_at]; simp [Nat.add_assoc]
    simp only [h0, List.getD_cons_zero, Function.comp_def, h1, List.getD_cons_succ]

theorem blockOkF_eq (p : Ptr) (B : Block) : blockOkF p B = blockOkAt p B := by
  rw [blockOkF, rowsOkKE_eq, twKE_tw, rowsOkF_eq]; rfl

theorem segsOkF_eq : ∀ (p : Ptr) (δ : List Seg), segsOkF p δ = segsOk p δ
  | _, [] => rfl
  | p, .row r :: δ => by rw [segsOkF, segsOk, segsOkF_eq _ δ]
  | p, .blk B :: δ => by rw [segsOkF, segsOk, segsOkF_eq _ δ, blockOkF_eq]

end Lvm.Fin
end
-- ===== end of `LvmFinSegs` =====

-- ===== merged from `LvmQTypedSCache` (GOLF module merge: `LvmQTypedSCache.lean` is now a stub importing `LvmQTypedGuard`) =====
section
-- New for lvm2 (roll 8 = B1, B1-IX-S): the typed V_S's start-up. `Φ_Q`'s entries tabulated once (`EntTab`), read
-- by the class derivation and by the class check: one enumeration instead of two.

/-!
# One table of the entries

`EntTab.of G`: every row's entries at every iteration (`FLF`'s), as arrays: `rows[b][t][jf]`, `aux[k][r][j]`.
`EntTab.get`: a lookup, else the entries (`EntTab.get_of`: it *is* the entry function, at every row and
iteration). The derivation (`deriveTermsG`) and the check (`checkTermsGA`) both read it.
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-- A function of three indices tabulated on `i < n`, `j < m i`, `l < k i j`. -/
def tab3 {α : Type} (n : ℕ) (m : ℕ → ℕ) (k : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ → α) : Array (Array (Array α)) :=
  (Array.range n).map fun i ↦ (Array.range (m i)).map fun j ↦ (Array.range (k i j)).map fun l ↦ f i j l

/-- A lookup in a three-index table, else `d ()`. -/
def look3 {α : Type} (A : Array (Array (Array α))) (i j l : ℕ) (d : Unit → α) : α :=
  match (A[i]?.bind (·[j]?)).bind (·[l]?) with
  | some x => x
  | none => d ()

/-- **Every row's entries at every iteration**, as arrays. -/
structure EntTab where
  /-- `rows[b][t][jf]`: template row `t` of block `b`. -/
  rows : Array (Array (Array (Array Ent)))
  /-- `aux[k][r][j]`: row `r` of auxiliary block `k`. -/
  aux : Array (Array (Array (Array Ent)))

/-- **The table of `FLF`'s entries.** -/
def EntTab.of (G : FLF) : EntTab :=
  ⟨tab3 G.F.qb.size (fun b ↦ (G.F.tpls.getD b #[]).size) (fun b t ↦ 2 ^ G.F.srcL (.row b t))
      (fun b t jf ↦ (G.srcEnts (.row b t) jf).toArray),
    tab3 G.F.lay.aux.length (fun k ↦ (G.F.lay.aux.getD k default).rows.length) (fun k r ↦ 2 ^ G.F.srcL (.aux k r))
      (fun k r j ↦ (G.srcEnts (.aux k r) j).toArray)⟩

/-- A row's entries at an iteration, from the table (else computed). -/
def EntTab.get (E : EntTab) (G : FLF) : TSrc → ℕ → Array Ent
  | .row b t, jf => look3 E.rows b t jf fun _ ↦ (G.srcEnts (.row b t) jf).toArray
  | .aux k r, j => look3 E.aux k r j fun _ ↦ (G.srcEnts (.aux k r) j).toArray

/-- **The terms and their check on one table** (`G = FLF.ofLay Q lay`): `(terms, check)`. -/
def termsChecked (G : FLF) : Array CTerm × Bool :=
  let ea := (EntTab.of G).get G
  let ts := deriveTermsG ea G.F
  (ts, checkTermsGA ea CTerm.atF ts)

end Lvm.Typed.K
end
-- ===== end of `LvmQTypedSCache` =====

/-!
# The typed static guard, generic in the configuration

The B program's one-pass builder (`qprogBF`, V-PERF's phases 4–7 with `wireGadgetF`), the mini-bus read tables' fit
(`mbFitB`, `mbFitBF`), the typed static guard (`staticOkTC`, `staticOkTS`, `staticOkTOf`) and the facts it gives
(`StaticFactsT`, `staticFactsTC`/`TS`/`TOf`), the cache of a term array (`cacheOfTerms`). The instances are
`LvmQTypedInst` (`P20`, the badge's) and `LvmQTypedInst8` (`P8`); this module has no closed constants of either.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

/-! ## The B program's segments in one pass (V-PERF's phases 4–7) -/

section
open Lvm.Har Lvm.Loop.QRing Lvm.Q1

/-- QW's `wireGadget` with V-PERF's `loopF` (its text otherwise; B1-IX-S: `loop`'s ranks are quadratic in its
template, and the wiring's glue templates are long: 3.7 s of the builder's 4.5 s at P20 [measured]). -/
def wireGadgetF (P qw : Nat) (cv : Nat → Cell) (mb sb : List Cell) (b : Cell) (zE : Nat) : BM Lvm.Q1.WireOut :=
  let w := P + 5
  let D := Nat.log2 (2 * w - 1)
  let G := Lvm.Q1.preW P (fun j => gkS (cv j)) (mb.map gkS) (sb.map gkS) (gkS b) 0
  VF.loopF [] (tplOf G.2) >>= fun pre =>
  scGadget D 2 qw .plain (G.1.target.gkCell pre) >>= fun sc =>
  let σ := (List.range w).map fun i => sc.cell 2 i
  let H := Lvm.Q1.postW P (qw + 15 * w) (fun j => gkS (cv j)) (mb.map gkS) (σ.map gkS)
    (G.1.lt.map (Src.gkOut pre)) (G.1.z.gkOut pre) (G.1.one.gkOut pre) (gkS (sc.cell 5 (w - 1))) (gkS b) 0
  VF.loopF [] (tplOf H.2) >>= fun post =>
  scGadget 1 2 (qw + 15 * w + 3) .plain (H.1.gkCell post) >>= fun sl =>
  let τ := (List.range 2).map fun i => sl.cell 2 i
  VF.loopF [] (tplOf (Lvm.Q1.slotW (qw + 15 * w + 33) (G.1.om.map (Src.gkOut pre)) (τ.map gkS) (G.1.z.gkOut pre)
    (G.1.one.gkOut pre) (gkS (sl.cell 5 1)) (gkS b) 0).2) >>= fun _ =>
  ringG (qw + 15 * w + 225) (qw + 15 * w + 33) zE >>= fun rg =>
  pure ⟨σ, H.1.gkCell post, τ, rg⟩

/-- V-PERF's `phases47F` with `wireGadgetF`. -/
def phases47S (C : QCfg) : BM Lvm.Har.P47Out := do
  let g := kc (pbB C)
  let p := C.p
  let r ← Lvm.Har.loadEs (QAsm.clog2 p.logN) (Lvm.Har.aLane p 0) 9
  let v ← Lvm.Har.loadEs 5 (Lvm.Har.aLane p 1) 3
  let tp ← VF.tapeGadgetF (p.logN - 5) (Lvm.Har.aLane p 2) (fun i => r.cell 0 i) (fun l => v.cell 0 l) g
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let mb ← Lvm.Har.borrow ((sigIn C).bn + 2) one.n p.logN
  let wo ← wireGadgetF (p.logN - 5) (Lvm.Har.aLane p 3) tp.cv mb (Lvm.Har.sbCells C) g z.n
  let rk ← Lvm.Har.loadEs (QAsm.clog2 p.ksLog) (Lvm.Har.aLane p 4) 9
  let vk ← Lvm.Har.loadEs 5 (Lvm.Har.aLane p 5) 3
  let kko ← VF.gkrGadgetF (p.ksLog - 4) (Lvm.Har.aLane p 6) (fun i => rk.cell 0 i) (fun l => vk.cell 0 l) g
  Lvm.Q1.ksLinkGadget p (QAsm.clog2 p.ksLog) (Lvm.Har.aLane p 7) g
  pure ⟨(List.range p.logN).map (r.cell 0), (List.range 25).map (v.cell 0), tp, mb, wo,
    (List.range p.ksLog).map (rk.cell 0), (List.range 25).map (vk.cell 0), kko⟩

end

/-- The B program's segments with V-PERF's linear-time phases 4–7 (`wireGadgetF`: B1-IX-S). -/
def qprogBF (C : QCfg) (T : TData) : BM Unit := do
  Lvm.QLink.qlink C.p (lay C)
  let _ ← Lvm.QSig.qsig (sigIn C)
  phases47S C >>= qarithB C T

/-! ## The layout's fit of the mini-bus's read tables -/

/-- **`MbFit`, decided** on a word map `wk` of `K` cells (`C_main` words). -/
def mbFitBW (C : QCfg) (wk : Nat → Nat) : Bool :=
  let Q := qlinkProg C
  (capReadRows Q).all fun x =>
    (List.range (2 ^ (Q.blk x.1).lsize)).all fun jf =>
      wk (adrCell Q x.1 x.2 jf) == wk (adrCell Q x.1 x.2 0) + jf &&
        wk (resCell Q x.1 x.2 jf) == wk (resCell Q x.1 x.2 0) + jf

/-- **`MbFit`, decided** on the layout's words (`C_main` words from `T`'s offset). -/
def mbFitB (C : QCfg) (lay : Typed.Lay) : Bool := mbFitBW C fun n => (layout0 C.p).t + lay.wordK n

/-- `mbFitB` on the layout's array caches (B1-IX-S: `K.FL.wordK`'s owner is a binary search, `Lay.wordK`'s a scan of
the blocks; `mbFitBF_eq` on a checked layout). -/
def mbFitBF (C : QCfg) (Q : Program) (lay : Typed.Lay) : Bool :=
  let t := (layout0 C.p).t
  let F := K.FL.ofLay Q lay
  mbFitBW C fun n => t + F.wordK n

theorem mbFitBF_eq (C : QCfg) (Q : Program) (lay : Typed.Lay) (hlay : lay.Ok Q) : mbFitBF C Q lay = mbFitB C lay := by
  unfold mbFitBF mbFitB
  simp only [K.fl_wordK Q lay hlay]

theorem mbFit_of (C : QCfg) (lay : Typed.Lay) (h : mbFitB C lay = true) :
    MbFit C fun n => (layout0 C.p).t + lay.wordK n := by
  intro x hx jf hjf
  simp only [mbFitB, mbFitBW, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h x hx jf hjf

/-! ## The static guard -/

/-- **The facts the typed guard gives**, in their consumers' forms. -/
structure StaticFactsT (C : QCfg) (T : TData) (F : TFrz) (Q : Program) (lay : Typed.Lay) (c : PhiCache)
    (N : TypedV.TNat) : Prop where
  /-- `typed_sound`'s `hwf`. -/
  wf : Q.wf = true
  /-- `typed_sound`'s `hlay`, `PhiQC_eq`'s `hlay`. -/
  hlay : lay.Ok Q
  /-- `PhiQC_eq`'s `hc`. -/
  cache : c.okB Q lay = true
  /-- V_S's region check (B1-V's closed forms). -/
  regs : N.okB C.p.nuMain C.p.nuRec = true
  /-- V_S's regions are the layout's (`TNat.layOk`, `layOkN_eq`; `src?_inst`). -/
  hlayOk : layOkN N lay = true
  /-- The record is the mini-bus's. -/
  mini : TypedV.fitsMiniB C.p N.mbT = true
  /-- The layout places the read tables' cells consecutively (`MbFit`). -/
  mbFit : MbFit C fun n => (layout0 C.p).t + lay.wordK n
  /-- The frozen read words are the layout's. -/
  mbW : ∀ e ∈ F.mbW, e.2 = (layout0 C.p).t + lay.wordK e.1
  /-- **QLT's cells are the layout's constants** (`typed_sound`'s `Inputs` on QLT, L-D's `NodeSound`). -/
  cst : lay.cst = qltCst C
  /-- `typed_sound`'s `hinj` (`g`-injectivity below the cell bound). -/
  inj : GInj (max (Q.cells .K) (Q.cells .E))
  /-- lvm2 E2F: no `E2` row (the old typed path's `holds_of_wiring`). -/
  noE2 : Typed.NoE2 Q

/-! ## The cache of a term array -/

/-- The cache of a term array (`cacheW`'s form, compiled by the fast `K.compileTF`, which is `K.compileT`:
`K.compileTF_eq`; CTF). -/
def cacheOfTerms (ts : Array CTerm) : PhiCache := ⟨ts.toList, K.compileTF ts⟩

end Lvm.QTyped
