-- New for lvm6 (SU2, start-up): `nodeLayB3`'s fast twin. Additive: no definition or statement changes; the guard
-- (`staticOk6`) calls `nodeLayB3F`, and `nodeLayB3F_eq` makes its facts `nodeLayB3`'s.
import Lvm6NodeMaps
import Lvm6NodeAux
import Lvm6NodeBuildF

/-!
# `nodeLayB3F` (SU2)

G0/ST-6 timed `nodeLayB3` at 1.5–4.2 s. Its cost was three things, each replaced by an equal computation:
* **`qltCstB`** built `qltData6 P6 lay6`, quadratic in the plan: **`qltCstBF`** compares with `cstOf6` (built once,
  by `qltData6F`; `cstOf6_eq`).
* **`pS lay ⟨nK, 0⟩`** (the `BITS` classes' pointer) ran `node6E` in `BM`, whose `bind` is quadratic: **`pSF`** runs
  ST-5's `FM` twin (`node6EF`, `rep_node6E`) and reads the pointer of the final state (`pushAll_p`); **`pSF_eq`**.
* **`pairsB`** built every expected `BITS` block (`rowRows6`, twice per row) and compared lists of operand lists:
  **`pairsBF`** compares each aux row with its expected entries as they are generated (`matchMap`), the booleanity
  rows against `boolOps`, the word and output rows against `outRowsF`; **`pairsBF_eq`**.

**`nodeLayB3F_eq : nodeLayB3F Ti = nodeLayB3 Ti`**, for every instance; **`nodeLayB3C c`** reads the pointer from a
cache `(cl, cp)` when the regions agree (`pS_congrY`: `pS` depends on `lay.yregs` only), **`nodeLayB3C_eq`**
given `cp = pS cl ⟨nK, 0⟩`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits Lvm.QSig Lvm.Q2 Lvm.QTyped Lvm.Loop.Build
open Lvm6.Q (qsig6 qlink6 opensP18)
open Lvm6.Ty (TInst6)
open Lvm6.BF (FM St lift node6EF rep_node6E pushAll pushAll_p bind_def)

/-! ## The QLT constants -/

/-- **`qltCstB` against `cstOf6`** (the table built once, by `qltData6F`). -/
def qltCstBF (lay : Lay) : Bool := decide (lay.cst = cstOf6)

theorem qltCstBF_eq (lay : Lay) : qltCstBF lay = qltCstB lay := by
  rw [qltCstBF, qltCstB, cstOf6_eq]

/-! ## `Q_sig`'s pointer by the fast builder -/

/-- `node6E`'s twin, then `Q_link`, from the state at `p` (no blocks). -/
def preSF (lay : Lay) : FM Unit :=
  node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun _ ↦ lift (qlink6 P6 opensP18 lay6)

/-- **`Q_sig`'s pointer, fast**: the pointer of `preSF`'s final state. -/
def pSF (lay : Lay) (p : Ptr) : Ptr := (preSF lay ⟨p, #[], []⟩).2.p

theorem lift_snd_p {α : Type} (m : BM α) (s : Lvm6.BF.St) : (lift m s).2.p = s.p.adv (m s.p).2 :=
  pushAll_p s (m s.p).2

theorem pSF_eq (lay : Lay) (p : Ptr) : pSF lay p = pS lay p := by
  have h1 : (node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC ⟨p, #[], []⟩).2.p = pL lay p := by
    rw [rep_node6E, pushAll_p]
    rfl
  rw [pSF, preSF, bind_def, lift_snd_p, h1]
  rfl

/-! ## `Q_sig`'s pointer from the layout's regions only

`node6E` reads its instance's layout only through the regions `lay.yregs` (`pubBase`, `sflatBase`, `onesOf`;
`qacc6` ignores it), so `pS lay p` depends on `lay.yregs` alone: a pointer computed once for one layout serves every
layout with the same regions (`pSC`). -/

theorem ty6_congrY {Ti Ti' : TInst6} (h : Ti.lay.yregs = Ti'.lay.yregs) : Lvm6.QD.ty6 Ti = Lvm6.QD.ty6 Ti' := by
  funext pubC ain yIn own ownY a gate
  simp only [Lvm6.QD.ty6, Lvm6.QD.wire6, Lvm6.QD.relay6, Lvm6.QD.pubBase, Lvm6.QD.sflatBase, Lvm6.QD.onesOf, h,
    Lvm6.QD.qacc6]

theorem n6_congrY {lay lay' : Lay} (h : lay.yregs = lay'.yregs) : n6 lay = n6 lay' := by
  have hb : Lvm6.QD.pubBase (tiOf lay) = Lvm6.QD.pubBase (tiOf lay') := by
    simp only [Lvm6.QD.pubBase, tiOf, h]
  have hp : pubCOf lay = pubCOf lay' := by
    funext y
    unfold pubCOf
    rw [hb]
  have ht : Lvm6.QD.ty6 (tiOf lay) = Lvm6.QD.ty6 (tiOf lay') := ty6_congrY h
  simp only [n6, Lvm6.Node.node6E, ht, hp]

theorem pS_congrY {lay lay' : Lay} (h : lay.yregs = lay'.yregs) (p : Ptr) : pS lay p = pS lay' p := by
  simp only [pS, pL, n6_congrY h]

/-- **`pS lay ⟨nK, 0⟩` with a cache**: a layout `cl` and its pointer `cp`, used when the regions agree. -/
def pSC (cl : Lay) (cp : Ptr) (lay : Lay) : Ptr := if lay.yregs = cl.yregs then cp else pSF lay ⟨nK, 0⟩

theorem pSC_eq {cl : Lay} {cp : Ptr} (hc : cp = pS cl ⟨nK, 0⟩) (lay : Lay) : pSC cl cp lay = pS lay ⟨nK, 0⟩ := by
  unfold pSC
  split
  · rename_i h
    rw [hc, pS_congrY h]
  · exact pSF_eq lay _

/-! ## The `BITS` rows, matched as generated -/

/-- `l` is `s.map g`, element by element, `R a b` deciding `a = g b`. -/
def matchMap {α β : Type} (R : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => R a b && matchMap R as bs
  | _, _ => false

theorem matchMap_map {α β γ : Type} [DecidableEq γ] {R : α → β → Bool} {p : α → γ} {g : β → γ}
    (hR : ∀ a b, R a b = decide (p a = g b)) :
    ∀ (l : List α) (s : List β), matchMap R l s = decide (l.map p = s.map g)
  | [], [] => rfl
  | [], _ :: _ => by simp [matchMap]
  | _ :: _, [] => by simp [matchMap]
  | a :: as, b :: bs => by
    rw [matchMap, hR, matchMap_map hR as bs, List.map_cons, List.map_cons]
    simp only [List.cons.injEq, Bool.decide_and]

theorem matchMap_eq {α β : Type} [DecidableEq α] {R : α → β → Bool} {g : β → α} (hR : ∀ a b, R a b = decide (a = g b))
    (l : List α) (s : List β) : matchMap R l s = decide (l = s.map g) := by
  rw [matchMap_map (p := id) hR, List.map_id]

/-- An entry's equality, field by field. -/
def entEqB (a b : ℕ × AOp × FE) : Bool := decide (a.1 = b.1) && decide (a.2.1 = b.2.1) && decide (a.2.2 = b.2.2)

theorem entEqB_eq (a b : ℕ × AOp × FE) : entEqB a b = decide (a = b) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [entEqB, Prod.mk.injEq, Bool.decide_and, Bool.and_assoc]

/-- Two entry lists are equal (`entEqB` per entry). -/
def opsEqB (l l' : List (ℕ × AOp × FE)) : Bool := matchMap entEqB l l'

theorem opsEqB_eq (l l' : List (ℕ × AOp × FE)) : opsEqB l l' = decide (l = l') := by
  rw [opsEqB, matchMap_eq (g := id) (fun a b ↦ entEqB_eq a b), List.map_id]

/-- The booleanity row `z` of a row whose bits start at word `w`. -/
def boolOps (w z : ℕ) : List (ℕ × AOp × FE) := [(0, bitOp w 0 z, 1), (1, bitOp w 0 z, 1), (2, bitOp w 0 z, 1)]

/-- The word row's bit entries. -/
def wordOps (w : ℕ) : List (ℕ × AOp × FE) := (List.range 64).map fun z ↦ (2, bitOp w 0 z, FE.ofK (wt z))

/-- An output's bits with a nonzero coefficient. -/
def outBitsO (o : BOut) : List ℕ := (List.range 64).filter fun z ↦ o.coef z != 0

/-- An output's bit entries. -/
def outOpsO (o : BOut) (w : ℕ) : List (ℕ × AOp × FE) :=
  (outBitsO o).map fun z ↦ (2, bitOp w 0 z, FE.ofK (o.coef z))

/-- Output `j`'s bit entries. -/
def outOps (S : BSpec) (w j : ℕ) : List (ℕ × AOp × FE) := outOpsO (S.out j) w

/-- A map over the indices of `l` reading `l.getD j d` is a map over `l.zipIdx` (no `getD`). -/
theorem range_map_getD {α β : Type} (l : List α) (d : α) (f : ℕ → α → β) :
    (List.range l.length).map (fun j ↦ f j (l.getD j d)) = l.zipIdx.map fun p ↦ f p.2 p.1 := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- Output `j` of row `x` (its cell, then its bit entries), with `o` the output. -/
def outRowO (S : BSpec) (w x : ℕ) (p : BOut × ℕ) : ARow := ⟨(2, .cell ⟨.K, S.oc p.2 x, [0]⟩, 1) :: outOpsO p.1 w⟩

theorem outRows_zipIdx (S : BSpec) (w x : ℕ) :
    (List.range S.outs.length).map (fun j ↦ (⟨(2, .cell ⟨.K, S.oc j x, [0]⟩, 1) :: outOps S w j⟩ : ARow)) =
      S.outs.zipIdx.map (outRowO S w x) :=
  range_map_getD S.outs (.bit 0) fun j o ↦ (⟨(2, .cell ⟨.K, S.oc j x, [0]⟩, 1) :: outOpsO o w⟩ : ARow)

/-- The address of a cell function on a one-row chunk. -/
theorem cellAddr_one (f : ℕ → ℕ) : cellAddr f 0 0 = ⟨.K, f 0, [0]⟩ := by
  simp [cellAddr, affOn]

/-- **Row `x`'s rows of class `S`** (`rowRows6`), spelled out: the booleanity rows, then the word and output rows. -/
theorem rowRows6_eq (S : BSpec) (w x : ℕ) : rowRows6 S w x =
    (List.range 64).map (fun z ↦ (⟨boolOps w z⟩ : ARow)) ++
      ((if S.rd then [⟨(2, .cell ⟨.K, S.wc x, [0]⟩, 1) :: wordOps w⟩] else []) ++
        (List.range S.outs.length).map fun j ↦ (⟨(2, .cell ⟨.K, S.oc j x, [0]⟩, 1) :: outOps S w j⟩ : ARow)) := by
  simp only [rowRows6, BSpec.chunkRows, cellAddr_one, List.append_assoc]
  rfl

theorem boolBlk6_rows (S : BSpec) (w x : ℕ) :
    (boolBlk6 S w x).rows = (List.range 64).map (fun z ↦ (⟨boolOps w z⟩ : ARow)) := by
  rw [boolBlk6, rowRows6_eq, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

theorem outBlk6_rows (S : BSpec) (w x : ℕ) : (outBlk6 S w x).rows =
    (if S.rd then [⟨(2, .cell ⟨.K, S.wc x, [0]⟩, 1) :: wordOps w⟩] else []) ++
      (List.range S.outs.length).map fun j ↦ (⟨(2, .cell ⟨.K, S.oc j x, [0]⟩, 1) :: outOps S w j⟩ : ARow) := by
  rw [outBlk6, rowRows6_eq, List.drop_left' (by simp)]

/-- Booleanity row `z`: `boolOps w z`, entry by entry. -/
def boolRowB (w : ℕ) (r : ARow) (z : ℕ) : Bool := opsEqB r.ops (boolOps w z)

/-- A row is a cell entry `(2, cell c, 1)` then the entries `t`, matched by `R`. -/
def cellRowB {β : Type} (c : ℕ) (R : (ℕ × AOp × FE) → β → Bool) (t : List β) (r : ARow) : Bool :=
  match r.ops with
  | e :: es => entEqB e (2, .cell ⟨.K, c, [0]⟩, 1) && matchMap R es t
  | [] => false

theorem cellRowB_eq {β : Type} {c : ℕ} {R : (ℕ × AOp × FE) → β → Bool} {g : β → ℕ × AOp × FE}
    (hR : ∀ a b, R a b = decide (a = g b)) (t : List β) (r : ARow) :
    cellRowB c R t r = decide (r.ops = (2, .cell ⟨.K, c, [0]⟩, 1) :: t.map g) := by
  unfold cellRowB
  split
  · rename_i e es h
    rw [h, entEqB_eq, matchMap_eq hR]
    simp only [List.cons.injEq, Bool.decide_and]
  · rename_i h
    rw [h]
    simp

/-- The word and output rows of row `x` of class `S`, bits at `w`, matched as generated. -/
def outRowsB (S : BSpec) (w x : ℕ) (rows : List ARow) : Bool :=
  let outs := matchMap (fun r (p : BOut × ℕ) ↦ cellRowB (S.oc p.2 x)
    (fun e z ↦ entEqB e (2, bitOp w 0 z, FE.ofK (p.1.coef z))) (outBitsO p.1) r)
  if S.rd then
    match rows with
    | r :: rs => cellRowB (S.wc x) (fun e z ↦ entEqB e (2, bitOp w 0 z, FE.ofK (wt z))) (List.range 64) r &&
        outs rs S.outs.zipIdx
    | [] => false
  else outs rows S.outs.zipIdx

theorem outRowB_eq (S : BSpec) (w x : ℕ) (p : BOut × ℕ) (r : ARow) :
    cellRowB (S.oc p.2 x) (fun e z ↦ entEqB e (2, bitOp w 0 z, FE.ofK (p.1.coef z))) (outBitsO p.1) r =
      decide (r.ops = (outRowO S w x p).ops) :=
  cellRowB_eq (g := fun z ↦ (2, bitOp w 0 z, FE.ofK (p.1.coef z))) (fun _ _ ↦ entEqB_eq _ _) _ r

theorem outRowsB_eq (S : BSpec) (w x : ℕ) (rows : List ARow) :
    outRowsB S w x rows = decide (rows.map ARow.ops = (outBlk6 S w x).rows.map ARow.ops) := by
  have ho : ∀ rs : List ARow, matchMap (fun r (p : BOut × ℕ) ↦ cellRowB (S.oc p.2 x)
      (fun e z ↦ entEqB e (2, bitOp w 0 z, FE.ofK (p.1.coef z))) (outBitsO p.1) r) rs S.outs.zipIdx =
      decide (rs.map ARow.ops = ((List.range S.outs.length).map fun j ↦
        (⟨(2, .cell ⟨.K, S.oc j x, [0]⟩, 1) :: outOps S w j⟩ : ARow)).map ARow.ops) := fun rs ↦ by
    rw [outRows_zipIdx, List.map_map]
    exact matchMap_map (fun r p ↦ outRowB_eq S w x p r) rs _
  have hw : ∀ r : ARow, cellRowB (S.wc x) (fun e z ↦ entEqB e (2, bitOp w 0 z, FE.ofK (wt z))) (List.range 64) r =
      decide (r.ops = (2, .cell ⟨.K, S.wc x, [0]⟩, 1) :: wordOps w) :=
    cellRowB_eq (g := fun z ↦ (2, bitOp w 0 z, FE.ofK (wt z))) (fun _ _ ↦ entEqB_eq _ _) _
  rw [outBlk6_rows]
  unfold outRowsB
  cases hrd : S.rd
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    exact ho rows
  · simp only [↓reduceIte, List.cons_append, List.nil_append]
    cases rows with
    | nil => simp
    | cons r rs =>
      simp only
      rw [hw, ho, List.map_cons, List.map_cons]
      simp only [List.cons.injEq, Bool.decide_and]

/-- **A `BITS` row's two blocks** (booleanity at the block's bit base, then the word and output rows), matched as
generated. -/
def blkPairB (b c : ABlk) (S : BSpec) (x : ℕ) : Bool :=
  decide (b.l = 0) && matchMap (boolRowB (blkBw b)) b.rows (List.range 64) &&
    (decide (c.l = 0) && outRowsB S (blkBw b) x c.rows)

theorem blkPairB_eq (b c : ABlk) (S : BSpec) (x : ℕ) :
    blkPairB b c S x = ablksEqB [b, c] [boolBlk6 S (blkBw b) x, outBlk6 S (blkBw b) x] := by
  have hb : matchMap (boolRowB (blkBw b)) b.rows (List.range 64) =
      decide (b.rows.map ARow.ops = (boolBlk6 S (blkBw b) x).rows.map ARow.ops) := by
    rw [boolBlk6_rows, List.map_map]
    exact matchMap_map (p := ARow.ops) (g := boolOps (blkBw b)) (fun r z ↦ opsEqB_eq r.ops _) _ _
  rw [blkPairB, hb, outRowsB_eq]
  simp only [ablksEqB, Bool.and_true]
  rfl

/-- **`pairsB`, rows matched as generated.** -/
def pairsBF : List ABlk → List (BSpec × ℕ) → Bool
  | _, [] => true
  | b :: c :: bs, (S, x) :: rs => blkPairB b c S x && pairsBF bs rs
  | _, _ :: _ => false

theorem pairsBF_eq : ∀ (bs : List ABlk) (rs : List (BSpec × ℕ)), pairsBF bs rs = pairsB bs rs
  | _, [] => by simp [pairsBF, pairsB]
  | [], _ :: _ => by simp [pairsBF, pairsB]
  | [_], _ :: _ => by simp [pairsBF, pairsB]
  | b :: c :: bs, (S, x) :: rs => by rw [pairsBF, pairsB, blkPairB_eq, pairsBF_eq bs rs]

/-- **`bitsAuxInB`, fast**: the pointer by `pSF`, the rows matched as generated. -/
def bitsAuxInBF (lay : Lay) : Bool :=
  pairsBF (lay.aux.drop powAns.length) (bitsRowsS (qsig6 sigI sigIl sbC (pSF lay ⟨nK, 0⟩)).1)

theorem bitsAuxInBF_eq (lay : Lay) : bitsAuxInBF lay = bitsAuxInB lay := by
  rw [bitsAuxInBF, pSF_eq, pairsBF_eq]
  rfl

/-! ## The auxiliary blocks, built directly (the layout's start-up build) -/

/-- The booleanity rows of a row whose bits start at `w`. -/
def boolRowsF (w : ℕ) : List ARow := (List.range 64).map fun z ↦ (⟨boolOps w z⟩ : ARow)

/-- The word and output rows of row `x` of class `S`, bits at `w`. -/
def outRowsL (S : BSpec) (w x : ℕ) : List ARow :=
  (if S.rd then [⟨(2, .cell ⟨.K, S.wc x, [0]⟩, 1) :: wordOps w⟩] else []) ++ S.outs.zipIdx.map (outRowO S w x)

theorem boolBlk6_eq (S : BSpec) (w x : ℕ) : boolBlk6 S w x = ⟨0, boolRowsF w⟩ := by
  show ABlk.mk 0 ((rowRows6 S w x).take 64) = ABlk.mk 0 (boolRowsF w)
  exact congrArg (ABlk.mk 0) (boolBlk6_rows S w x)

theorem outBlk6_eq (S : BSpec) (w x : ℕ) : outBlk6 S w x = ⟨0, outRowsL S w x⟩ := by
  show ABlk.mk 0 ((rowRows6 S w x).drop 64) = ABlk.mk 0 (outRowsL S w x)
  exact congrArg (ABlk.mk 0) ((outBlk6_rows S w x).trans (by rw [outRows_zipIdx]; rfl))

/-- **`auxOf6`, built directly**: each `BITS` row's two blocks from `boolRowsF`/`outRowsL` (not two `rowRows6`
builds and a `take`/`drop`). -/
def auxOf6F (so : SigOut × WalkC) (base : ℕ → ℕ) : List ABlk :=
  ((List.range powAns.length).map fun k ↦ powBlk (powAns.getD k (0, 0)).2 (base k) (powAns.getD k (0, 0)).1) ++
    ((bitsRowsS so).zipIdx).flatMap fun (r, i) ↦
      [⟨0, boolRowsF (base (powAns.length + 2 * i))⟩, ⟨0, outRowsL r.1 (base (powAns.length + 2 * i)) r.2⟩]

theorem auxOf6F_eq (so : SigOut × WalkC) (base : ℕ → ℕ) : auxOf6F so base = auxOf6 so base := by
  simp only [auxOf6F, auxOf6, boolBlk6_eq, outBlk6_eq]

/-- **`bitsAuxInB` with the pointer cache `(cl, cp)`.** -/
def bitsAuxInBC (cl : Lay) (cp : Ptr) (lay : Lay) : Bool :=
  pairsBF (lay.aux.drop powAns.length) (bitsRowsS (qsig6 sigI sigIl sbC (pSC cl cp lay)).1)

theorem bitsAuxInBC_eq {cl : Lay} {cp : Ptr} (hc : cp = pS cl ⟨nK, 0⟩) (lay : Lay) :
    bitsAuxInBC cl cp lay = bitsAuxInB lay := by
  rw [bitsAuxInBC, pSC_eq hc, pairsBF_eq]
  rfl

/-! ## The guard's Bool -/

/-- **`nodeLayB3`, fast** (the same conjuncts in the same order, `qltCstBF`, `bitsAuxInBF`). -/
def nodeLayB3F (Ti : TInst6) : Bool :=
  powAuxInB Ti.lay && qltCstBF Ti.lay && pubCellsB Ti && noPubB Ti && bitsAuxInBF Ti.lay && ccRegsRB Ti

theorem nodeLayB3F_eq (Ti : TInst6) : nodeLayB3F Ti = nodeLayB3 Ti := by
  rw [nodeLayB3F, nodeLayB3, nodeLayB, qltCstBF_eq, bitsAuxInBF_eq]

/-- **`nodeLayB3`, fast, with the pointer cache `(cl, cp)`** (`nodeLayB3F` with `bitsAuxInBC`). -/
def nodeLayB3C (cl : Lay) (cp : Ptr) (Ti : TInst6) : Bool :=
  powAuxInB Ti.lay && qltCstBF Ti.lay && pubCellsB Ti && noPubB Ti && bitsAuxInBC cl cp Ti.lay && ccRegsRB Ti

theorem nodeLayB3C_eq {cl : Lay} {cp : Ptr} (hc : cp = pS cl ⟨nK, 0⟩) (Ti : TInst6) :
    nodeLayB3C cl cp Ti = nodeLayB3 Ti := by
  rw [nodeLayB3C, nodeLayB3, nodeLayB, qltCstBF_eq, bitsAuxInBC_eq hc]

end Lvm6.Node.Dep
