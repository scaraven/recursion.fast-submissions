-- New for lvm2 E2F (E2F-L, 2026-11-13): the extractor's static layout, generic in the stage (S2GF, S2GT): the stage's
-- parameters `p` carry its schedule (`schedule p`, route A: `Item.readW`), so the FS messages, the trace's blocks, the
-- plan and the child's reassembly are `LvmXLayout`'s/`LvmReassemble`'s/`LvmXOut`'s at `p`, with the stage's header,
-- size, leaf lengths and root occupancy.
import LvmXTop
import LvmScheduleF
import LvmReassemble

/-!
# The extractor's layout at a stage

* **`XStage`**: the parameters `p` (the schedule `schedule p`), the header's bytes `hb`, the proof's size `pz`, the
  leaf lengths, `openMain`'s first item `nOpen`, the root's occupied words `occ0`.
* **`fsMsgsS`**: the chain's messages (`fsPre` at the stage's header).
* **`blocksS`** (`blocks p`), `lensLS`, `entLS`, **`readTraceLS`**: the child's trace from its stream lanes.
* **`planS`** (`plan p`), **`reassembleS`** (`reassemble p`): the replay's plan and the proof a trace carries.
* **`childWS`**: the left child of the words `w` at the stage (`childW`'s generalisation).
* `stF20`: S2GF's stage.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X Lvm.Replay

/-- **A stage of the `S` branch**, as the extractor sees it: the parameters `p` (whose `schedule p` is the stage's
schedule, `LvmSchedule`'s route A), the header's bytes, `|π|`, the leaf lengths, `openMain`'s first item, the root's
occupied words. -/
structure XStage where
  /-- The parameters (levels, rows, positions, stage). -/
  p : Params
  /-- The header's bytes (the seed absorbs `π[8, hb)`). -/
  hb : ℕ
  /-- The proof's size. -/
  pz : ℕ
  /-- The leaf lengths (the commitments' rows). -/
  leafLens : List ℕ
  /-- The index of `openMain`'s first item in the schedule (item 0 is `C_main`'s root cap; items `1 … nOpen − 1` are
  the pinned middle phases). -/
  nOpen : ℕ
  /-- The occupied words of `C_main`'s root rows (`47` at S2GM and S2GF, `46` at S2GT). -/
  occ0 : ℕ

/-- The stage's schedule. -/
abbrev XStage.items (st : XStage) : List Item := schedule st.p

/-- The seed query's length. -/
def XStage.seedLen (st : XStage) : ℕ := 32 + st.hb - 8

/-! ## The chain's messages -/

/-- **The chain's messages** at a stage: position `k ≥ 1` absorbs entry `k − 1` (the seed first; `fsMsgs` with the
stage's header). -/
def fsMsgsS (st : XStage) : List (ℕ × ℕ) := (8, st.hb - 8) :: fsPre st.p st.items st.hb st.hb

/-! ## The child's trace -/

/-- **The trace after `q₀`** at a stage (`blocks`). -/
abbrev blocksS (st : XStage) : List Blk := blocks st.p

/-- The query lengths after `q₀`. -/
def lensLS (st : XStage) : List ℕ := (blocksS st).flatMap fun b => b.queries.map Prod.snd

/-- The entries after `q₀`: lane and length (from lane 6). -/
def entLS (st : XStage) : List (ℕ × ℕ) := walk 6 (lensLS st)

/-- **The child's trace read off its stream lanes** at a stage (`readTraceL`). -/
def readTraceLS (st : XStage) (W : ℕ → Word) : Trace := q0Ent W :: (entLS st).map fun x => entAt W x.1 x.2

/-! ## The plan and the reassembly -/

/-- **The plan** at a stage (`plan`). -/
abbrev planS (st : XStage) : List PE := plan st.p

/-- **The proof a trace carries** at a stage (`reassemble`). -/
abbrev reassembleS (st : XStage) (tr : Trace) : ByteArray := reassemble st.p tr

/-! ## The child -/

/-- **The left child of the words `w`** at a stage (`Lvm.NS.childW`'s generalisation). -/
def childWS (st : XStage) (w : ℕ → Word) : Signed :=
  ⟨reassembleS st (readTraceLS st (laneOf w)), readTraceLS st (laneOf w), sigOfF (sigCol w)⟩

/-! ## The reads and `C_main`'s opening in the chain -/

/-- The read widths of the items, in order. -/
def readWidthsS (st : XStage) : List ℕ :=
  st.items.flatMap fun
    | .readW m w => List.replicate m w
    | .read m => List.replicate m eBytes
    | _ => []

/-- The `n`-th read's width (`rw` of the stage's format). -/
def rwS (st : XStage) (n : ℕ) : ℕ := (readWidthsS st).getD n eBytes

/-- The items of the pinned middle phases (after the root cap, before `openMain`). -/
def midItemsS (st : XStage) : List Item := (st.items.take st.nOpen).drop 1

/-- The FS queries before `openMain`. -/
def nPreS (st : XStage) : ℕ := (fsPre st.p (st.items.take st.nOpen) st.hb st.hb).length

/-- `C_main`'s level `i`. -/
def mainLS (st : XStage) (i : ℕ) : Level := st.p.level ⟨.main, i⟩

/-- The FS queries of a non-final level (`lvlFsM`). -/
def lvlFsS (st : XStage) (i : ℕ) : ℕ :=
  (mainLS st i).fold + (if st.p.mainOod then (mainLS st i).kappa else 0) + gQs st.p + (mainLS st i).nPosQ + 1

/-- **The chain position of level `i`'s fold challenge `α_{i,j}`** (`foldPosM`). -/
def foldPosS (st : XStage) (i j : ℕ) : ℕ :=
  nPreS st + 3 + (if i = 0 then 0 else if i = 1 then lvlFsS st 0 else lvlFsS st 0 + lvlFsS st 1) + j

/-- The chain position of fold challenge `k < 14` (`6 + 4 + 4`). -/
def foldPosKS (st : XStage) (k : ℕ) : ℕ :=
  if k < 6 then foldPosS st 0 k else if k < 10 then foldPosS st 1 (k - 6) else foldPosS st 2 (k - 10)

/-- **The chain's targets** `0 … nChainS st − 1`: through the last fold challenge of level 2. -/
def nChainS (st : XStage) : ℕ := foldPosS st 2 ((mainLS st 2).fold - 1) + 1

/-- **The π offset of level `i`'s cap** (level 0's right after the header). -/
def capOffS (st : XStage) : ℕ → ℕ
  | 0 => st.hb
  | 1 => ((fsMsgsS st).getD (foldPosS st 0 ((mainLS st 0).fold - 1)) (0, 0)).1 + 2 * eBytes
  | _ => ((fsMsgsS st).getD (foldPosS st 1 ((mainLS st 1).fold - 1)) (0, 0)).1 + 2 * eBytes

/-- **The π offset of the residual.** -/
def resOffS (st : XStage) : ℕ := ((fsMsgsS st).getD (nChainS st - 1) (0, 0)).1 + 2 * eBytes

/-- The chain's message of position `p ≥ 1`. -/
def msgLS (st : XStage) (p : ℕ) : ℕ × ℕ := (fsMsgsS st).getD (p - 1) (0, 0)

/-- The number of trace entries (`qS`): `q₀` and the blocks' entries. -/
def qSS (st : XStage) : ℕ := 1 + ((blocksS st).map Blk.count).sum

/-! ## S2GF -/

/-- **S2GF's stage**: `P20F`'s schedule (`accV = 44`), header `headerF 44`, `|π| = piSizeF P20F 44`, M′'s rows, the
root's 47 occupied words. -/
def stF20 : XStage :=
  ⟨P20F, headerF accVF, piSizeF P20F accVF, leafLens, (((phases P20F).take 7).flatMap (·.2)).length, 47⟩

end Lvm.XS
