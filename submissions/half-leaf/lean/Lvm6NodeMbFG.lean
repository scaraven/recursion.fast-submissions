-- New for lvm6 (PORT17 L2: split from `Lvm6NodeMbF`, WP MBF). The mini-bus tables' cap cells in one pass
-- (`capCellsF`, `mbTLF`, `mbTLF_eq`), without the node theorem's modules: the circuit's source (`Lvm6NodeBuildF`,
-- `Lvm6PlaceMb`) imports this part only, so it builds before the node theorem (N1) does.
import Lvm6NodeMbT

/-!
# The mini-bus tables' cap cells, fast (`capCellsF`, `mbTLF`; WP MBF, first part)

* **`capCellsF Q`**: the address and result cells of every cap `readd` in one tail-recursive pass (`capGo`,
  `rdGo`); **`capCellsF_eq`**: it is `capReadRows Q` mapped by `adrCell`/`resCell`, for every `Q`.
* **`mbTLF P Q lay`** with **`mbTLF_eq : mbTLF P Q lay = mbTL P Q lay`** (every `P`, `Q`, `lay`).

The rest of WP MBF (`capCellsS`, `mbTDF`, `run6M`) is in `Lvm6NodeMbF`.
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

end Lvm6.Node.Mb
