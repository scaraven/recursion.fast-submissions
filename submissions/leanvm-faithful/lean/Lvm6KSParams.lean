-- New for lvm6 (WP KSA, RV4 B2): the `KS` alias regions as parameters — families of input cells laid by lanes,
-- each lane one `KS` region mapped onto an aligned window of the stack — with their `Ok` interface, the deployed
-- word map they define, and the region targets claim 49 uses.
import LvmTypedLayout

/-!
# `KS` alias parameters

A **family** `f : KSFam` is the input cells `f.c0 + f.w·r + l` (`l < f.w` lanes, `r < 2^f.cap` rows; the first
`f.rows` rows are aliased). The layout lays it lane by lane (`f.w` regions of `2^f.cap` words, `specOf`'s
multiplicity `f.w`); lane `l`, row `r` is the stack word `f.tgt r l = f.tb + l·f.ts + r`.

* **`KSParams`**: the families; **`KSParams.cellTgt`**: an input cell's stack word (`0` off the families).
* **`cellOfWord lay y`**: the input cell whose word is `y` (the inverse of `DReg.word` on the `K` input regions).
* **`ksWOf P lay`** (`= P.cellTgt ∘ cellOfWord lay`): the deployed `KS` word map. On every lane region it is the
  shift onto `f.tb + l·f.ts`; **`ksTgt P lay r`**: a `KS` region's target base (its first word's image).
* **`KSFam.Ok`**, **`KSParams.Ok`** (the interface an instance proves once): lanes and rows fit (`0 < w`,
  `rows ≤ 2^cap`), every lane's target base is `2^cap`-aligned (CLG's `RegAff` needs aligned shifts), the
  families' cell windows are disjoint. The stack side (which family is which sponge column) is the instance's
  lemma; the guard (`Lvm6NodeKS.ksAliasPB`) and its soundness lemma are generic in `P`.
-/

set_option autoImplicit false

namespace Lvm6.KSP

open Lvm.Typed

/-- **A family of `KS` alias cells**: cells `c0 + w·r + l`, lane `l < w`, row `r < 2^cap` (aliased rows
`r < rows`); lane `l`, row `r` ↦ stack word `tb + l·ts + r`. -/
structure KSFam where
  /-- The first cell. -/
  c0 : ℕ
  /-- The lanes. -/
  w : ℕ
  /-- `log₂` of a lane's words. -/
  cap : ℕ
  /-- The aliased rows. -/
  rows : ℕ
  /-- The stack word of lane `0`, row `0`. -/
  tb : ℕ
  /-- The stack stride between lanes. -/
  ts : ℕ
  deriving Repr, Inhabited, DecidableEq

namespace KSFam

variable (f : KSFam)

/-- The cell after the family's window. -/
def cellHi : ℕ := f.c0 + f.w * 2 ^ f.cap

/-- Cell `n` lies in the family's window. -/
def holds (n : ℕ) : Bool := decide (f.c0 ≤ n ∧ n < f.cellHi)

/-- **The stack word of lane `l`, row `r`.** -/
def tgt (r l : ℕ) : ℕ := f.tb + l * f.ts + r

/-- The stack word of cell `n` (row `(n − c0)/w`, lane `(n − c0) mod w`). -/
def tgtOf (n : ℕ) : ℕ := f.tgt ((n - f.c0) / f.w) ((n - f.c0) % f.w)

/-- **A family's interface**: lanes, rows within a lane, aligned lane targets. -/
structure Ok : Prop where
  w_pos : 0 < f.w
  rows_le : f.rows ≤ 2 ^ f.cap
  aligned : ∀ l < f.w, (f.tb + l * f.ts) % 2 ^ f.cap = 0

instance : Decidable f.Ok :=
  decidable_of_iff (0 < f.w ∧ f.rows ≤ 2 ^ f.cap ∧ ∀ l < f.w, (f.tb + l * f.ts) % 2 ^ f.cap = 0)
    ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩⟩

/-- Cell `c0 + w·r + l` of the window is lane `l`, row `r`. -/
theorem tgtOf_cell (h : f.Ok) {r l : ℕ} (hl : l < f.w) : f.tgtOf (f.c0 + f.w * r + l) = f.tgt r l := by
  have hw := h.w_pos
  unfold tgtOf
  rw [show f.c0 + f.w * r + l - f.c0 = l + f.w * r by omega, Nat.add_mul_div_left _ _ hw,
    Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl, Nat.zero_add]

/-- A row `r < rows` lies in the window. -/
theorem holds_cell (h : f.Ok) {r l : ℕ} (hr : r < f.rows) (hl : l < f.w) : f.holds (f.c0 + f.w * r + l) = true := by
  have h1 : r < 2 ^ f.cap := lt_of_lt_of_le hr h.rows_le
  have h2 : f.w * r + l < f.w * 2 ^ f.cap := by
    calc f.w * r + l < f.w * r + f.w := by omega
      _ = f.w * (r + 1) := by ring
      _ ≤ f.w * 2 ^ f.cap := Nat.mul_le_mul_left _ h1
  unfold holds cellHi
  exact decide_eq_true ⟨Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _), by
    rw [Nat.add_assoc]; exact Nat.add_lt_add_left h2 _⟩

end KSFam

/-- **The `KS` alias parameters**: the families. -/
structure KSParams where
  /-- The families. -/
  fams : List KSFam
  deriving Repr, Inhabited

namespace KSParams

variable (P : KSParams)

/-- **The parameters' interface**: every family is `Ok`, the families' cell windows are disjoint. -/
structure Ok : Prop where
  fams : ∀ f ∈ P.fams, f.Ok
  disjoint : P.fams.Pairwise fun f g ↦ f.cellHi ≤ g.c0 ∨ g.cellHi ≤ f.c0

instance : Decidable P.Ok :=
  decidable_of_iff ((∀ f ∈ P.fams, f.Ok) ∧ P.fams.Pairwise fun f g ↦ f.cellHi ≤ g.c0 ∨ g.cellHi ≤ f.c0)
    ⟨fun ⟨a, b⟩ ↦ ⟨a, b⟩, fun ⟨a, b⟩ ↦ ⟨a, b⟩⟩

/-- **An input cell's stack word** (the first family holding it). -/
def cellTgt (n : ℕ) : ℕ :=
  match P.fams.find? (·.holds n) with
  | some f => f.tgtOf n
  | none => 0

/-- The `specOf` entries of the families: `(first cell, end, lanes)`. -/
def regs : List (ℕ × ℕ × ℕ) := P.fams.map fun f ↦ (f.c0, f.cellHi, f.w)

/-- With disjoint windows, cell `n` of family `f`'s window has `f`'s stack word. -/
theorem cellTgt_of_mem (h : P.Ok) {f : KSFam} (hf : f ∈ P.fams) {n : ℕ} (hn : f.holds n = true) :
    P.cellTgt n = f.tgtOf n := by
  unfold cellTgt
  have hd := h.disjoint
  generalize P.fams = fs at hf hd
  induction fs with
  | nil => simp at hf
  | cons g gs ih =>
    rw [List.find?_cons]
    by_cases hg : g.holds n = true
    · rw [hg]
      rcases List.mem_cons.mp hf with rfl | hmem
      · rfl
      · have := List.rel_of_pairwise_cons hd hmem
        simp only [KSFam.holds, decide_eq_true_eq] at hg hn
        omega
    · rw [Bool.not_eq_true] at hg
      rw [hg]
      rcases List.mem_cons.mp hf with rfl | hmem
      · rw [hn] at hg; exact absurd hg (by decide)
      · exact ih hmem (List.Pairwise.of_cons hd)

end KSParams

/-! ## The targets and the cells (PFW's `KSTgt`) -/

/-- **The `C_main` targets of the `KS` aliases** (PFW `NodeLay.ks`): `Y` lane `l`, row `x` is the stack word
`yBase + l·yLane + x`, `X` lane `l`, row `i` is `xBase + l·xLane + i`; `ys` starts at `Y`'s row `rowY`, `ysl` at
`rowYl`, `md` is row `rowMd`. -/
structure KSTgt where
  yBase : ℕ
  xBase : ℕ
  yLane : ℕ
  xLane : ℕ
  rowY : ℕ
  rowYl : ℕ
  rowMd : ℕ
  deriving Repr, Inhabited, DecidableEq

/-- **The alias cells**: the four families' first cells, lanes, aliased rows and `log₂` lane lengths. -/
structure KSCells where
  xs : ℕ
  ys : ℕ
  ysl : ℕ
  md : ℕ
  xLanes : ℕ
  xRows : ℕ
  xCap : ℕ
  yLanes : ℕ
  yRows : ℕ
  yCap : ℕ
  ylRows : ℕ
  ylCap : ℕ
  deriving Repr, Inhabited, DecidableEq

namespace KSTgt

variable (T : KSTgt) (C : KSCells)

/-- `xs`: lane `l`, row `r` ↦ `X(r, l)`. -/
def xFam : KSFam := ⟨C.xs, C.xLanes, C.xCap, C.xRows, T.xBase, T.xLane⟩
/-- `ys`: lane `l`, row `r` ↦ `Y_l(rowY + r)`. -/
def yFam : KSFam := ⟨C.ys, C.yLanes, C.yCap, C.yRows, T.yBase + T.rowY, T.yLane⟩
/-- `ysl`: lane `l`, row `r` ↦ `Y_l(rowYl + r)`. -/
def ylFam : KSFam := ⟨C.ysl, C.yLanes, C.ylCap, C.ylRows, T.yBase + T.rowYl, T.yLane⟩
/-- `md`: lane `l` ↦ `Y_l(rowMd)`. -/
def mdFam : KSFam := ⟨C.md, C.yLanes, 0, 1, T.yBase + T.rowMd, T.yLane⟩

/-- **The parameters of `T` on the cells `C`.** -/
def params : KSParams := ⟨[T.xFam C, T.yFam C, T.ylFam C, T.mdFam C]⟩

theorem xFam_tgt (r l : ℕ) : (T.xFam C).tgt r l = T.xBase + l * T.xLane + r := rfl
theorem yFam_tgt (r l : ℕ) : (T.yFam C).tgt r l = T.yBase + l * T.yLane + (T.rowY + r) := by
  simp only [yFam, KSFam.tgt]; omega
theorem ylFam_tgt (r l : ℕ) : (T.ylFam C).tgt r l = T.yBase + l * T.yLane + (T.rowYl + r) := by
  simp only [ylFam, KSFam.tgt]; omega
theorem mdFam_tgt (l : ℕ) : (T.mdFam C).tgt 0 l = T.yBase + l * T.yLane + T.rowMd := by
  simp only [mdFam, KSFam.tgt]; omega

end KSTgt

/-! ## The deployed word map -/

/-- Word `y` lies in lane `l`'s words of input region `d` (all its words if it is not laned). -/
def inLane (d : DReg) (l y : ℕ) : Bool :=
  if d.lanes ≤ 1 then decide (d.bases.headD 0 ≤ y ∧ y < d.bases.headD 0 + d.n)
  else decide (d.laneBases.getD l 0 ≤ y ∧ y < d.laneBases.getD l 0 + d.n / d.lanes)

/-- **The input cell of word `y`** (`K` input regions; the inverse of `DReg.word`). -/
def cellOfWord (lay : Lay) (y : ℕ) : ℕ :=
  match lay.inp.find? (fun d ↦ d.ty == .K && (List.range (max d.lanes 1)).any fun l ↦ inLane d l y) with
  | some d =>
    if d.lanes ≤ 1 then d.lo + (y - d.bases.headD 0)
    else
      let l := ((List.range d.lanes).find? fun l ↦ inLane d l y).getD 0
      d.lo + d.lanes * (y - d.laneBases.getD l 0) + l
  | none => 0

/-- **The deployed `KS` word map**: a word goes to its input cell's stack word. -/
def ksWOf (P : KSParams) (lay : Lay) (y : ℕ) : ℕ := P.cellTgt (cellOfWord lay y)

/-- **A `KS` region's target base** (its first word's image; `ksWOf` is a shift on it when `regAffB` holds). -/
def ksTgt (P : KSParams) (lay : Lay) (r : YReg) : ℕ := ksWOf P lay r.base

end Lvm6.KSP
