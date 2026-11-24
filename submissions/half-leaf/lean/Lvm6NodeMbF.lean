-- New for lvm6 (WP MBF, STARTUP). The mini-bus tables' fast twin: `mbTL`'s cap cells by one pass over the program
-- (no quadratic `readdRows`, no per-row `Program.start`), and the tables read from one shared build of the program
-- before CC. Additive (PFW rule 3): `mbTL`, `mbTD`, `progR`, `famQ6`, `progQ6` are unchanged; the equations tie them.
import Lvm6NodeRun
import Lvm6NodeMbFG

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
    famQ6 lay = preO lay >>= fun o ↦ ccGo o lay (mbTD lay) ccbC gateC := by
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
  let r2 := ccGo r.1 lay T ccbC gateC (p0.adv r.2)
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
