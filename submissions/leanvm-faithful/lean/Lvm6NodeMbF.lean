-- New for lvm6 (WP MBF, STARTUP). The mini-bus tables' fast twin: `mbTL`'s cap cells by one pass over the program
-- (no quadratic `readdRows`, no per-row `Program.start`), and the tables read from one shared build of the program
-- before CC. Additive (PFW rule 3): `mbTL`, `mbTD`, `progR`, `famQ6`, `progQ6` are unchanged; the equations tie them.
import Lvm6NodeRun

/-!
# The mini-bus tables, fast (`mbTLF`, `mbTDF`, `run6M`; WP MBF)

* **`capCellsF Q`**: the address and result cells of every cap `readd` (`capReadRows Q`'s order, iteration `0`),
  in one tail-recursive pass over the blocks (`capGo`, with the running `Program.start`) and, per block, one over
  its template (`rdGo`, with the running `rank`). **`capCellsF_eq`**: it is `capReadRows Q` mapped by
  `adrCell`/`resCell`, for every `Q`. The reference `readdRows` reads `tpl.getD t` for each `t`: quadratic in a
  block's template.
* **`mbTLF P Q lay`** with **`mbTLF_eq : mbTLF P Q lay = mbTL P Q lay`** (every `P`, `Q`, `lay`).
* **`mbTDF lay`** with **`mbTDF_eq : mbTDF lay = mbTD lay`**: the same build of `progR lay`, fast tables.
* **`capCellsS`**: the cap cells read off the segments directly (`segGo`, no grouping) when no glue row is a
  `readd`; **`capCellsS_eq`**: the program's cap cells (`capGo` on `groupF δ`), by `groupF`'s fold.
* **One build** (`run6M lay`): the families before CC run once (`preO`); their segments give the tables
  (`capCellsS`, `mbTC`); CC continues from the same segments. **`run6M_segR`**, **`run6M_T`**, **`run6M_Q`**: the
  parts are `progR lay`'s segments, `mbTD lay` and `progQ6 lay`.

Every recursion here is a tail call or a core list function with a tail-recursive implementation (the badge's stack
is the default 8 MB).
-/

set_option autoImplicit false

namespace Lvm6.Node.Mb

open Lvm Lvm.M3 Lvm.Loop

/-! ## The cap cells in one pass -/

/-- Whether a template row is a `readd` (`readdRows`' test). -/
def isReadd (r : Row) : Bool :=
  match r.op with
  | .readd _ _ => true
  | _ => false

/-- The address cell of a `readd` row at iteration `0` (`adrCell`'s body). -/
def adrOf (dims : List ℕ) (r : Row) : ℕ := (r.args.getD 0 default).at (unflat dims 0)

/-- A row's `K` width (`Row.w .K`, without the `Option`). -/
def kW (r : Row) : ℕ :=
  match r.op with
  | .assert0 => 0
  | _ => match r.ty with
    | .K => 1
    | .E => 0

theorem kW_eq (r : Row) : kW r = Row.w .K r := by
  obtain ⟨op, ty, args⟩ := r
  cases op <;> cases ty <;> rfl

/-- One block's `readd` rows `(address cell, result cell)` at iteration `0`, the block's results starting at `st`,
`rk` `K` writers before the rest `l` of the template; `acc` reversed; also the `K` writers in all (one pass,
tail-recursive). -/
def rdGo (dims : List ℕ) (st : ℕ) : List Row → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) × ℕ
  | [], rk, acc => (acc.reverse, rk)
  | r :: rs, rk, acc =>
    rdGo dims st rs (rk + kW r) (if isReadd r then (adrOf dims r, st + rk) :: acc else acc)

/-- A block's cap cells (its `readd` rows' cells if it has four, `capReadRows`' test, else none) and its `K`
results. -/
def blkStep (B : Block) (st : ℕ) : List (ℕ × ℕ) × ℕ :=
  let r := rdGo B.dims st B.tpl 0 []
  (if r.1.length = 4 then r.1 else [], r.2 * B.size)

/-- A block's cap cells. -/
def blkCells (B : Block) (st : ℕ) : List (ℕ × ℕ) := (blkStep B st).1

/-- A block's `K` results (`Program.start`'s summand). -/
def wszK (B : Block) : ℕ := B.tw .K * B.size

/-- The blocks' cap cells, the first block's results starting at `st`; `acc` reversed (tail-recursive). -/
def capGo : List Block → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], _, acc => acc.reverse
  | B :: bs, st, acc =>
    let x := blkStep B st
    capGo bs (st + x.2) (x.1.reverse ++ acc)

/-- **The cap cells of a program**, one pass. -/
def capCellsF (Q : Program) : List (ℕ × ℕ) := capGo Q.blocks Q.nInK []

theorem rdGo_spec (dims : List ℕ) (st : ℕ) : ∀ (l : List Row) (rk : ℕ) (acc : List (ℕ × ℕ)),
    rdGo dims st l rk acc = (acc.reverse ++ ((List.range l.length).filter fun t ↦ isReadd (l.getD t default)).map
      fun t ↦ (adrOf dims (l.getD t default), st + rk + ((l.take t).map (Row.w .K)).sum),
      rk + (l.map (Row.w .K)).sum)
  | [], rk, acc => by simp [rdGo]
  | r :: rs, rk, acc => by
    rw [rdGo, rdGo_spec dims st rs, List.length_cons, List.range_succ_eq_map, List.filter_cons,
      List.filter_map, kW_eq]
    by_cases h : isReadd r <;>
      simp [h, Function.comp_def, Nat.add_assoc]

theorem blkStep_snd (B : Block) (st : ℕ) : (blkStep B st).2 = wszK B := by
  simp [blkStep, rdGo_spec, wszK, Block.tw]

theorem capGo_spec : ∀ (l : List Block) (st : ℕ) (acc : List (ℕ × ℕ)),
    capGo l st acc = acc.reverse ++ (List.range l.length).flatMap fun i ↦
      blkCells (l.getD i default) (st + ((l.take i).map wszK).sum)
  | [], st, acc => by simp [capGo]
  | B :: bs, st, acc => by
    rw [capGo, blkStep_snd, capGo_spec bs, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp [blkCells, Nat.add_assoc]

theorem blkCells_eq (Q : Program) (b : ℕ) :
    blkCells (Q.blk b) (Q.start .K b) = (if (QTyped.readdRows (Q.blk b)).length = 4 then
      (QTyped.readdRows (Q.blk b)).map (b, ·) else []).map
        fun x ↦ (QTyped.adrCell Q x.1 x.2 0, QTyped.resCell Q x.1 x.2 0) := by
  have e : (rdGo (Q.blk b).dims (Q.start .K b) (Q.blk b).tpl 0 []).1 =
      (QTyped.readdRows (Q.blk b)).map fun t ↦ (QTyped.adrCell Q b t 0, QTyped.resCell Q b t 0) := by
    rw [rdGo_spec]
    simp only [List.reverse_nil, List.nil_append, Nat.add_zero, QTyped.readdRows, QTyped.adrCell,
      QTyped.resCell, Nat.mul_zero, Block.rank, adrOf]
    rfl
  unfold blkCells blkStep
  simp only [e, List.length_map]
  split <;> simp [List.map_map, Function.comp_def]

/-- **The cap cells, one pass**: `capReadRows Q` mapped by `adrCell`/`resCell` at iteration `0`, every `Q`. -/
theorem capCellsF_eq (Q : Program) :
    capCellsF Q = (QTyped.capReadRows Q).map fun x ↦ (QTyped.adrCell Q x.1 x.2 0, QTyped.resCell Q x.1 x.2 0) := by
  rw [capCellsF, capGo_spec, QTyped.capReadRows, List.map_flatMap]
  simp only [List.reverse_nil, List.nil_append]
  refine List.flatMap_congr fun b hb ↦ ?_
  have hb' : b < Q.blocks.length := List.mem_range.mp hb
  have hs : Q.nInK + ((Q.blocks.take b).map wszK).sum = Q.start .K b := rfl
  rw [hs, show Q.blocks.getD b default = Q.blk b from rfl, blkCells_eq]

/-! ## The tables -/

/-- The stack words `(address, value)` of cap cells. -/
def wordsOf (P : MbPar) (cells : List (ℕ × ℕ)) (lay : Typed.Lay) : Array (ℕ × ℕ) :=
  (cells.map fun c ↦ (regW6 P lay .com (lay.wordK c.1), regW6 P lay .com (lay.wordK c.2))).toArray

/-- The tables of cap cells (`mbTL`'s body after `capWords6`). -/
def mbTC (P : MbPar) (cells : List (ℕ × ℕ)) (lay : Typed.Lay) : List Tab :=
  let cw := wordsOf P cells lay
  mbTOf6 P (fun k => (cw.getD k (0, 0)).1) (fun k => (cw.getD k (0, 0)).2)

/-- **`capWords6`, fast**: the stack words of the cap cells. -/
def capWords6F (P : MbPar) (Q : Program) (lay : Typed.Lay) : Array (ℕ × ℕ) := wordsOf P (capCellsF Q) lay

theorem capWords6F_eq (P : MbPar) (Q : Program) (lay : Typed.Lay) : capWords6F P Q lay = capWords6 P Q lay := by
  rw [capWords6F, wordsOf, capCellsF_eq, List.map_map]
  rfl

/-- **`mbTL`, fast.** -/
def mbTLF (P : MbPar) (Q : Program) (lay : Typed.Lay) : List Tab := mbTC P (capCellsF Q) lay

/-- **The fast tables are `mbTL`'s**, for every parameter record, program and layout. -/
theorem mbTLF_eq (P : MbPar) (Q : Program) (lay : Typed.Lay) : mbTLF P Q lay = mbTL P Q lay := by
  have h := capWords6F_eq P Q lay
  unfold capWords6F at h
  unfold mbTLF mbTC mbTL
  rw [h]

/-! ## The cap cells from the segments (no grouping) -/

section Segs

open Lvm.Loop.Build

/-- The cap cells read off a program's segments, left to right: a loop block's by `blkStep`; a glue row only
advances the start. `none` if a glue row is a `readd` (then the glue grouping would matter). Tail-recursive. -/
def segGo : List Seg → ℕ → List (ℕ × ℕ) → Option (List (ℕ × ℕ))
  | [], _, acc => some acc.reverse
  | .row r :: δ, st, acc => if isReadd r then none else segGo δ (st + kW r) acc
  | .blk B :: δ, st, acc =>
    let x := blkStep B st
    segGo δ (st + x.2) (x.1.reverse ++ acc)

/-- **The cap cells of the program of segments `δ`** (`progOfSegs`), without grouping them when no glue row is a
`readd`. -/
def capCellsS (nInK : ℕ) (δ : List Seg) (dflt : Unit → List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  match segGo δ nInK [] with
  | some c => c
  | none => dflt ()

/-- `groupF`'s output from the fold's state. -/
def outG (g : List Row × ℕ × List Block) : List Block :=
  if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2

theorem groupF_outG (δ : List Seg) : Lvm.VF.groupF δ = outG (δ.foldr Lvm.VF.gStepN ([], 0, [])) := by
  simp only [Lvm.VF.groupF, List.foldr_toArray, outG]

theorem glueStep (rows : List Row) (st : ℕ) (h : ∀ r ∈ rows, isReadd r = false) :
    blkStep ⟨[], rows⟩ st = ([], (rows.map (Row.w .K)).sum) := by
  have hf : ((List.range rows.length).filter fun t ↦ isReadd (rows.getD t default)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    have ht' := List.mem_range.mp ht
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
    simp [h _ (List.getElem_mem ht')]
  unfold blkStep
  rw [rdGo_spec]
  simp only [hf]
  simp [Block.size, Block.lsize]

theorem capGo_row (r : Row) (g : List Row × ℕ × List Block) (st : ℕ) (acc : List (ℕ × ℕ))
    (hr : isReadd r = false) (hg : ∀ r' ∈ g.1, isReadd r' = false) :
    capGo (outG (Lvm.VF.gStepN (.row r) g)) st acc = capGo (outG g) (st + kW r) acc := by
  obtain ⟨run, n, bs⟩ := g
  have h1 : blkStep ⟨[], [r]⟩ st = ([], Row.w .K r) := by
    rw [glueStep [r] st (by simpa using hr)]; simp
  simp only [Lvm.VF.gStepN]
  split
  · simp only [outG, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, capGo, h1, List.reverse_nil,
      List.nil_append, kW_eq]
  · simp only [outG, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, capGo]
    rw [glueStep (r :: run) st (fun x hx ↦ by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hg x hx)]
    cases run with
    | nil => simp [kW_eq]
    | cons r' rs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, capGo]
      rw [glueStep (r' :: rs) _ hg]
      simp [kW_eq, Nat.add_assoc]

theorem foldr_rows : ∀ (δ : List Seg) (r : Row), r ∈ (δ.foldr Lvm.VF.gStepN ([], 0, [])).1 → Seg.row r ∈ δ
  | [], r, h => by simp at h
  | .row r' :: δ, r, h => by
    rw [List.foldr_cons] at h
    simp only [Lvm.VF.gStepN] at h
    split at h
    · simp only [List.mem_singleton] at h
      subst h; exact List.mem_cons_self
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (foldr_rows δ r h)
  | .blk B :: δ, r, h => by
    rw [List.foldr_cons] at h
    simp [Lvm.VF.gStepN] at h

theorem segGo_spec : ∀ (δ : List Seg) (st : ℕ) (acc c : List (ℕ × ℕ)), segGo δ st acc = some c →
    (∀ r, Seg.row r ∈ δ → isReadd r = false) ∧ c = capGo (Lvm.VF.groupF δ) st acc
  | [], st, acc, c, h => by
    simp only [segGo, Option.some.injEq] at h
    subst h
    refine ⟨fun r hr ↦ by simp at hr, ?_⟩
    simp [groupF_outG, outG, capGo]
  | .row r :: δ, st, acc, c, h => by
    simp only [segGo] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hr
      have hr' : isReadd r = false := by simpa using hr
      obtain ⟨hδ, hc⟩ := segGo_spec δ _ _ _ h
      refine ⟨fun r' hr'' ↦ ?_, ?_⟩
      · rcases List.mem_cons.mp hr'' with h' | h'
        · cases h'; exact hr'
        · exact hδ r' h'
      · rw [hc, groupF_outG, groupF_outG, List.foldr_cons,
          capGo_row r _ st acc hr' fun r' h' ↦ hδ r' (foldr_rows δ r' h')]
  | .blk B :: δ, st, acc, c, h => by
    simp only [segGo] at h
    obtain ⟨hδ, hc⟩ := segGo_spec δ _ _ _ h
    refine ⟨fun r' hr'' ↦ ?_, ?_⟩
    · rcases List.mem_cons.mp hr'' with h' | h'
      · cases h'
      · exact hδ r' h'
    · rw [hc, groupF_outG, groupF_outG, List.foldr_cons]
      simp only [Lvm.VF.gStepN, outG, List.isEmpty_nil, ↓reduceIte, capGo]

/-- **The cap cells from the segments are the program's** (`capGo` on `groupF δ`, i.e. `capCellsF` of the
program of `δ`), whenever the fallback is. -/
theorem capCellsS_eq (nInK : ℕ) (δ : List Seg) (dflt : Unit → List (ℕ × ℕ))
    (hd : dflt () = capGo (Lvm.VF.groupF δ) nInK []) : capCellsS nInK δ dflt = capGo (Lvm.VF.groupF δ) nInK [] := by
  unfold capCellsS
  split
  · rename_i c h; exact (segGo_spec δ nInK [] c h).2
  · exact hd

end Segs

end Lvm6.Node.Mb

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm6 Lvm6.QD Lvm6.Node Lvm6.QK Lvm.QSig
open Lvm6.Node.Mb (mbTLF mbTLF_eq)

/-- **`mbTD`, fast** (the same `progR lay`, the tables by `mbTLF`). -/
def mbTDF (lay : Lay) : List Lvm.M3.Tab := mbTLF (mbPar6 lay) (progR lay) lay

/-- **The deployed mini-bus tables, fast**, for every layout. -/
theorem mbTDF_eq (lay : Lay) : mbTDF lay = mbTD lay := mbTLF_eq _ _ _

/-! ## One build: the tables from the program before CC, then CC -/

/-- The families before CC (`node6E`, `famR`), returning `node6E`'s cells. -/
def preO (lay : Lay) : BM NodeOutE :=
  node6E (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun o ↦ famR >>= fun _ ↦ pure o

/-- A program from its segments (`toProgramF`'s body). -/
def progOfSegs (nInK nInE : ℕ) (δ : List Seg) : Program :=
  let bs := Lvm.VF.groupF δ
  ⟨nInK, nInE, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem toProgramF_segs {α : Type} (nInK nInE : ℕ) (m : BM α) :
    Lvm.VF.toProgramF nInK nInE m = progOfSegs nInK nInE (m ⟨nInK, nInE⟩).2 := rfl

theorem preO_unit (lay : Lay) : (preO lay >>= fun _ ↦ (pure () : BM Unit)) =
    (node6E (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun _ ↦ famR) := by
  simp only [preO, bm_bind_assoc, bm_pure_bind, bm_bind_pure_unit]

/-- **`progR` is the program of `preO`'s segments.** -/
theorem progR_preO (lay : Lay) : progR lay = progOfSegs nK 0 (preO lay ⟨nK, 0⟩).2 := by
  rw [progR, ← preO_unit, toProgramF_segs, bind_apply]
  simp only [pure_apply, List.append_nil]

/-- `famQ6` is `preO` followed by CC. -/
theorem famQ6_preO (lay : Lay) :
    famQ6 lay = preO lay >>= fun o ↦ ccG18o o lay (mbTD lay) ccbC gateC := by
  simp only [famQ6, preO, bm_bind_assoc, bm_pure_bind]

/-- What one build hands on: the segments before CC, the mini-bus tables, the whole program. -/
structure Run6M where
  /-- The segments of the families before CC (`progR`'s). -/
  segR : List Seg
  /-- The mini-bus tables (`mbTD`). -/
  T : List Lvm.M3.Tab
  /-- The deployed program (`progQ6`). -/
  Q : Program

/-- **One build**: the families before CC once; the tables from their segments (`capCellsS`: no grouping, no
second build); CC continues on the same segments. -/
def run6M (lay : Lay) : Run6M :=
  let p0 : Ptr := ⟨nK, 0⟩
  let r := preO lay p0
  let T := Lvm6.Node.Mb.mbTC (mbPar6 lay)
    (Lvm6.Node.Mb.capCellsS nK r.2 fun _ ↦ Lvm6.Node.Mb.capCellsF (progOfSegs nK 0 r.2)) lay
  let r2 := ccG18o r.1 lay T ccbC gateC (p0.adv r.2)
  ⟨r.2, T, progOfSegs nK 0 (r.2 ++ r2.2)⟩

theorem capCellsF_progOfSegs (δ : List Seg) :
    Lvm6.Node.Mb.capCellsF (progOfSegs nK 0 δ) = Lvm6.Node.Mb.capGo (Lvm.VF.groupF δ) nK [] := rfl

theorem capCellsS_progOfSegs (δ : List Seg) :
    Lvm6.Node.Mb.capCellsS nK δ (fun _ ↦ Lvm6.Node.Mb.capCellsF (progOfSegs nK 0 δ)) =
      Lvm6.Node.Mb.capCellsF (progOfSegs nK 0 δ) :=
  (Lvm6.Node.Mb.capCellsS_eq nK δ _ (capCellsF_progOfSegs δ)).trans (capCellsF_progOfSegs δ).symm

theorem run6M_segR (lay : Lay) : progOfSegs nK 0 (run6M lay).segR = progR lay := (progR_preO lay).symm

theorem run6M_T (lay : Lay) : (run6M lay).T = mbTD lay := by
  show Lvm6.Node.Mb.mbTC (mbPar6 lay) (Lvm6.Node.Mb.capCellsS nK (preO lay ⟨nK, 0⟩).2
    fun _ ↦ Lvm6.Node.Mb.capCellsF (progOfSegs nK 0 (preO lay ⟨nK, 0⟩).2)) lay = mbTD lay
  rw [capCellsS_progOfSegs, ← progR_preO]
  exact mbTDF_eq lay

/-- **The one build's program is the deployed program.** -/
theorem run6M_Q (lay : Lay) : (run6M lay).Q = progQ6 lay := by
  have hT := run6M_T lay
  simp only [run6M] at hT ⊢
  rw [hT, progQ6, toProgramF_segs, famQ6_preO, bind_apply]

end Lvm6.Node.Dep
