-- lvm6 X1 (PORT17; P17-freeze §3.3, §4): the extractor's geometry as one record. `xg18` is `P18`'s (in `Lvm6P18Park` since INT11), `xg17` is
-- `P17`'s, and the deployed constants (moved to `P17` in place) are `xg17`'s fields (`rfl`). Both are tied to their placement record
-- (L2's `Place`) and shape by one decided `Placed`, and the slot map the extractor relies on is checked against
-- `place17` (`xg17_slots`).
import Lvm6XTop
import Lvm6Place

/-!
# The extractor's geometry

* **`XGeo`**: the tree heights `ht`, the decoded stack (`colB`, slot stride `stride`, leaf rows `nLeaf`), the
  `STREAM` window (`tB`, `σ′` at `sB`, `σ_leaf` at `sLB`), the proof size `pz` and its log-count word `pL`, the cap
  words `capW` and the rows' bases `wB` of the five trees.
* **`xg18`**: `P18`'s geometry as literals (`ht18 = 21 … 17`, `stride = 2^19`, `nLeaf = 2^18`, `tB = colB6 + 33·2^19`,
  `pz = 238,152`, `capW18`): the deployed constants before PORT17. Since PORT17 the deployed constants (`ht6`,
  `stride6`, `nD`, `tB6`, `sB6`, `sLB6`, `pz6`, `pL6`, `capW6`, `wB6`) are `xg17`'s (`xg17_*`, `rfl`).
* **`xg17`** (P17-freeze §4): `ht = 20, 19, 18, 17, 16`, `stride = 2^18`, `nLeaf = 2^17`, `tB = colB6 + 33·2^18 =
  75,759,616`, `sB = tB + 2^17`, `sLB = sB + 597`, `pz = 230,424`, `pL = posL pz = 28,808`, the caps at tape words
  `capW17` (byte offsets 824, 63,936, 152,608, 184,256, 204,480: `front17`), the rows' bases `wB6` (each level's
  rows halve, so the `P18` bases stay disjoint).
* **`XGeo.Placed g pl sh`**: the fields are the placement's and the shape's: `stride = 2^slotLog`, `nLeaf = 2^logN`,
  `tB = colB + recOff`, `sB = tB + pl.sB`, `sLB = sB + 597` (`= tB + pl.sLB`, the stream word), `pz = piLenOf sh`, `pL = posL pz`,
  `ht i` = level `i`'s height. **`xg18_placed`**, **`xg17_placed`**.
* **`XGeo.Ok g`**: the numeric side conditions of the output stage's semantics (`regs` below every base, the
  addresses below `2^64`, the stream below `2^40`). **`xg18_ok`**, **`xg17_ok`**.
* **`xg17_slots`** (P17-freeze §3.3 with the coordinator's `X` at slot 42): the extractor reads the tree slots 0–32 and
  `STREAM` (slot 33) only; slots 0–33 end where `SP` starts (`34·2^18 = place17.spOff`, slots 34–35), below `com`
  (36–39), `Y` (40), the counts (41) and `X` (slot 42, `xBase = 42·2^18`). In slot 33 the stream's 64,866 words end
  below `σ′` at `2^17`, and `σ_leaf`'s 597 words end inside the slot.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X

/-- **The extractor's geometry.** -/
structure XGeo where
  /-- Level `i`'s tree height (`2^ht` positions). -/
  ht : ℕ → ℕ
  /-- The decoded stack's base. -/
  colB : ℕ
  /-- A slot's words. -/
  stride : ℕ
  /-- The leaf rows the right child reads. -/
  nLeaf : ℕ
  /-- The trace stream's base (`STREAM`, `tB = 0` in the stream). -/
  tB : ℕ
  /-- `σ′`'s base. -/
  sB : ℕ
  /-- `σ_leaf`'s base. -/
  sLB : ℕ
  /-- The `S` proof size. -/
  pz : ℕ
  /-- The tape word of the log count. -/
  pL : ℕ
  /-- Level `i`'s cap: its tape word. -/
  capW : ℕ → ℕ
  /-- Level `i`'s rows: their base. -/
  wB : ℕ → ℕ

/-! ## The instances -/

/-- Level `i`'s tree height at `P18` (FORMAT6 v2.5.3 §5; the deployed `ht6` before PORT17). -/
def ht18 : ℕ → ℕ
  | 0 => 21
  | 1 => 20
  | 2 => 19
  | 3 => 18
  | _ => 17

/-- Level `i`'s tree height at `P17` (FORMAT6 v2.6 §5). -/
def ht17 : ℕ → ℕ
  | 0 => 20
  | 1 => 19
  | 2 => 18
  | 3 => 17
  | _ => 16

/-- Level `i`'s cap at `P17`: tape word `5 + off/8` (`off` = 824, 63,936, 152,608, 184,256, 204,480: `front17`). -/
def capW17 : ℕ → ℕ
  | 0 => 108
  | 1 => 7997
  | 2 => 19081
  | 3 => 23037
  | _ => 25565

/-- **The `P17` geometry** (P17-freeze §4). -/
def xg17 : XGeo := ⟨ht17, colB6, 262144, 131072, 75759616, 75890688, 75891285, 230424, 28808, capW17, wB6⟩

/-- **The deployed constants are `xg17`'s** (PORT17: `Lvm6XNode`, `Lvm6XTop` at `P17`). -/
theorem xg17_colB : xg17.colB = colB6 := rfl
theorem xg17_stride : xg17.stride = stride6 := rfl
theorem xg17_nLeaf : xg17.nLeaf = nD := rfl
theorem xg17_tB : xg17.tB = tB6 := rfl
theorem xg17_sB : xg17.sB = sB6 := rfl
theorem xg17_sLB : xg17.sLB = sLB6 := rfl
theorem xg17_pz : xg17.pz = pz6 := rfl
theorem xg17_pL : xg17.pL = pL6 := rfl
theorem xg17_wB : xg17.wB = wB6 := rfl

theorem ht17_le (i : ℕ) : ht17 i ≤ 21 := by unfold ht17; split <;> omega

theorem lv6_le_ht17 (i : ℕ) : lv6 i ≤ ht17 i := by unfold lv6 ht17; split <;> split <;> omega

/-! ## Tied to the placement and the shape -/

/-- **The geometry is the placement's and the shape's.** `colB`, `capW` and `wB` are the extractor's own memory
layout and are not constrained here; `capW` is checked against the schedule by `frontD` (`capW6_eq_capW17`). -/
def XGeo.Placed (g : XGeo) (pl : Place) (sh : Shape) : Prop :=
  g.stride = 2 ^ pl.slotLog ∧ g.nLeaf = 2 ^ sh.logN ∧ g.tB = g.colB + pl.recOff ∧ g.sB = g.tB + pl.sB ∧
    g.sLB = g.sB + 597 ∧ g.pz = piLenOf sh ∧ g.pL = posL g.pz ∧ ∀ i < 5, g.ht i = (sh.levels.getD i default).ht

theorem xg17_placed : xg17.Placed place17 P17 :=
  ⟨rfl, rfl, rfl, rfl, rfl, piLen_P17.symm, rfl, by decide⟩

/-- `σ_leaf` in the stream: the placement's stream word `sLB` (`sB + 597`) from the stream's base. -/
theorem XGeo.sLB_place {g : XGeo} {pl : Place} {sh : Shape} (h : g.Placed pl sh) : g.sLB = g.tB + pl.sLB := by
  obtain ⟨-, -, -, h4, h5, -⟩ := h
  rw [h5, h4, Place.sLB]
  omega

/-! ## The output stage's side conditions -/

/-- **The numeric side conditions** of the output stage (`leftOutIR_sem`, `rightOutIR_sem`, `leafOutIR_sem`). -/
structure XGeo.Ok (g : XGeo) : Prop where
  colR : regs ≤ g.colB
  colW : g.colB + 2 * g.nLeaf + 3 * g.stride < 2 ^ 64
  tR : regs ≤ g.tB
  tW : g.tB + g.stride < 2 ^ 40
  sR : regs ≤ g.sB
  sW : g.sB + 597 < 2 ^ 64
  slR : regs ≤ g.sLB
  slW : g.sLB + 597 < 2 ^ 64
  nW : g.nLeaf < 2 ^ 64
  pzW : g.pz < 2 ^ 32
  pzP : 0 < g.pz

theorem xg17_ok : xg17.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [xg17, regs, colB6] <;> norm_num

/-! ## The slot map at `P17` -/

/-- **The extractor's part of P17-freeze's slot map**: the tree slots and `STREAM` (slots 0–33) end where `SP`
starts, below `com`, `Y`, the counts and `X` (slot 42); in slot 33 the stream's 64,866 words end below `σ′` and
`σ_leaf` ends inside the slot. -/
theorem xg17_slots :
    place17.recSlot = 33 ∧ 34 * 2 ^ place17.slotLog = place17.spOff ∧ place17.spOff < place17.comOff ∧
      place17.comOff < place17.yBase ∧ place17.yBase < place17.cnt0 ∧ place17.cnt0 < place17.xBase ∧
      place17.xBase = 42 * 2 ^ place17.slotLog ∧
      xg17.tB + 64866 ≤ xg17.sB ∧ xg17.sLB + 597 ≤ xg17.tB + xg17.stride ∧
      xg17.colB + 34 * xg17.stride = xg17.colB + place17.spOff ∧ xg17.nLeaf ≤ xg17.stride := by
  decide

end Lvm6.X
