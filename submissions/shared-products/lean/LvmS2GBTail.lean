-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): S2GB's π tail, the proof a trace carries at S2GB, the size
-- range, the extractor's stage and the left child read from the window (lead D-X1, D-X2).
import LvmS2GBSched
import LvmXSLayout
import LvmXSWinU
import LvmXSStage
import LvmS2GBHarB

/-!
# The π tail at S2GB

* **`tailB p tr`**: per opening (schedule order), at its first heap entry (slot `k = 2^m − 1`), the layer nodes
  `x < 2^m` in ascending order that no path covers (`x ∉ {posVal tr pe h j >>> path | j < t}`), each the half
  `x % 2` of the query of heap slot `2^(m−1) + x / 2` (lead freeze P0 (3), (4), (6)).
* **`reassembleB p tr`**: `'S' ‖ 0^7 ‖` the contributions (`bodyFrom`, the static part) `‖ tailB p tr`.
* **`SzB π`**: `piStatic P20B ≤ |π| ≤ piStatic P20B + tailMax P20B` (V_S's `parseOkB` range).
* **`stB20`**: S2GB's extractor stage (the static part of π: `pz = piStatic P20B`); **`childB20 x w`**: the left
  child read from S2GB's window (`childS20`'s twin with `reassembleB`).
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-- **Layer node `x` is covered**: some path `j < t` of the opening (positions from entry `pe`, `h` bits, `path`
inline levels) tops at `x`. -/
def coveredB (tr : Trace) (pe h t path x : Nat) : Bool :=
  (List.range t).any fun j => posVal tr pe h j >>> path == x

/-- Half `b` of entry `i`'s query: its first 32 bytes for `b = 0`, the rest otherwise. -/
def halfB (tr : Trace) (i b : Nat) : List UInt8 :=
  if b = 0 then (bl (qOf tr i)).take 32 else (bl (qOf tr i)).drop 32

/-- **The tail bytes entry `i` carries**: at an opening's first heap entry (slot `2^m − 1`) the opening's uncovered
layer nodes in ascending `x`, node `x` the half `x % 2` of heap slot `2^(m−1) + x / 2` (entry `i + 2^(m−1) − 1 − x / 2`);
nothing elsewhere. -/
def tailEntB (tr : Trace) (i : Nat) (e : PE) : List UInt8 :=
  match e.k with
  | .heap pe h t path _ m k _ =>
    if k + 1 = 2 ^ m then
      (List.range (2 ^ m)).flatMap fun x =>
        if coveredB tr pe h t path x then [] else halfB tr (i + 2 ^ (m - 1) - 1 - x / 2) (x % 2)
    else []
  | _ => []

/-- **S2GB's π tail** of a trace: the entries' tail bytes in trace order. -/
def tailB (p : Params) (tr : Trace) : List UInt8 :=
  (List.range (plan p).length).flatMap fun i => tailEntB tr i ((plan p).getD i default)

/-- **The proof a trace carries at S2GB**: `'S' ‖ 0^7 ‖` the contributions `‖` the π tail. -/
def reassembleB (p : Params) (tr : Trace) : ByteArray := ⟨(hdr8 ++ bodyFrom tr (plan p) 0 ++ tailB p tr).toArray⟩

end Lvm.Replay

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-- **S2GB's size range** (`parseOkB`'s): `piStatic P20B ≤ |π| ≤ piStatic P20B + tailMax P20B`. -/
def SzB (π : Proof) : Prop := piStatic P20B ≤ π.size ∧ π.size ≤ piStatic P20B + tailMax P20B

instance (π : Proof) : Decidable (SzB π) := inferInstanceAs (Decidable (_ ∧ _))

/-- **S2GB's extractor stage**: `P20B`'s schedule, the header, the static part of π (`piStatic P20B`), S2GU's leaf
lengths, `openMain` after the fourth phase, the root's 46 occupied words. -/
def stB20 : XStage :=
  ⟨P20B, headerBytesP P20B, piStatic P20B, leafLensU, (((phases P20B).take 4).flatMap (·.2)).length, 46⟩

/-- **The left child of the words `w`** at a stage under `capPrune` (`childWS` with `reassembleB`). -/
def childWB (st : XStage) (w : ℕ → Word) : Signed :=
  ⟨reassembleB st.p (readTraceLS st (laneOf w)), readTraceLS st (laneOf w), sigOfF (sigCol w)⟩

/-- **S2GB's left child read from its stream window** (`childS20`'s twin). -/
def childB20 (x : List UInt8) (w : List BF64) : Signed :=
  childWB stB20 fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (Lvm.CT.sIdxU x i) 0) else BF64.toBitVec 0

/-- S2GB's static part's size. -/
theorem stB20_pz : stB20.pz = 269336 := sizes_P20B.1.1

/-- Proof help: `OutOK`'s per-block checks and sums over a block list in one `List.rec` pass. -/
def outSumsB (bs : List Blk) : Bool × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  bs.rec (true, 0, 0, 0, 0, 0, 0) fun b _ ih =>
    (blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b) && ih.1, blkPOutsL b + ih.2.1, b.lanes + ih.2.2.1,
      b.count + ih.2.2.2.1, blkPCostL b + blkTCostL b + ih.2.2.2.2.1, blkTOutsL b + ih.2.2.2.2.2.1,
      blkPSizeL b + blkTSizeL b + ih.2.2.2.2.2.2)

theorem outSumsB_eq (bs : List Blk) : outSumsB bs =
    (bs.all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)), (bs.map blkPOutsL).sum,
      (bs.map Blk.lanes).sum, (bs.map Blk.count).sum, (bs.map blkPCostL).sum + (bs.map blkTCostL).sum,
      (bs.map blkTOutsL).sum, (bs.map blkPSizeL).sum + (bs.map blkTSizeL).sum) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [show outSumsB (b :: bs) = (blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b) && (outSumsB bs).1,
      blkPOutsL b + (outSumsB bs).2.1, b.lanes + (outSumsB bs).2.2.1, b.count + (outSumsB bs).2.2.2.1,
      blkPCostL b + blkTCostL b + (outSumsB bs).2.2.2.2.1, blkTOutsL b + (outSumsB bs).2.2.2.2.2.1,
      blkPSizeL b + blkTSizeL b + (outSumsB bs).2.2.2.2.2.2) from rfl, ih]
    simp only [List.all_cons, List.map_cons, List.sum_cons, Prod.mk.injEq]
    exact ⟨trivial, trivial, trivial, trivial, by omega, trivial, by omega⟩

set_option maxRecDepth 200000 in
/-- S2GB's output facts (`outOK_allS`'s at `stB20`; the heap entries are `.one .q0 64` blocks): the walk's `ok` is
`planOkB_P20B`'s, the blocks' checks and sums one kernel evaluation of `outSumsB`. -/
theorem outOK_allB :
    (Replay.planItems stB20.p Replay.w0 stB20.items).2.ok = true ∧
    (blocksS stB20).all (fun b => blkOkS b && okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true ∧
    8 + 8 * ((blocksS stB20).map blkPOutsL).sum = stB20.pz ∧ 4928 ≤ stB20.pz ∧ stB20.pz < 2 ^ 64 ∧
    6 + ((blocksS stB20).map Blk.lanes).sum ≤ nCp ∧ qSS stB20 < 2 ^ 64 ∧
    ((blocksS stB20).map blkPCostL).sum + ((blocksS stB20).map blkTCostL).sum ≤ 7100000 ∧
    ((blocksS stB20).map blkPOutsL).sum + ((blocksS stB20).map blkTOutsL).sum ≤ 163533 ∧
    ((blocksS stB20).map blkPSizeL).sum + ((blocksS stB20).map blkTSizeL).sum ≤ 240000 := by
  have hp : Replay.planItems stB20.p Replay.w0 stB20.items = Replay.planAll P20B := rfl
  have hb : blocksS stB20 = .one .seed (seedLenP P20B) :: itemBlks P20B schLA 0 := by
    rw [← schedule_P20B_litA]; rfl
  have hf : outSumsB (blocksS stB20) = (true, 33666, 71895, 4133, 4512070, 71895, 144181) := by
    rw [hb]; decide +kernel
  rw [outSumsB_eq] at hf
  simp only [Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  -- `qSS` by `rw`, never `show`: a `show` makes the kernel evaluate the sum (4 M hb)
  rw [hp]
  refine ⟨Lvm.E2Q.planOkB_P20B.1, h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stB20_pz, h2]
  · rw [stB20_pz]; decide
  · rw [stB20_pz]; decide
  · rw [h3]; decide
  · rw [qSS, h4]; decide
  · rw [h5]; decide
  · rw [h2, h6]; decide
  · rw [h7]; decide

/-- **S2GB's extractor output facts** (`OutOK stB20`). -/
theorem outOK_stB20 : OutOK stB20 :=
  let h := outOK_allB
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

end Lvm.XB
