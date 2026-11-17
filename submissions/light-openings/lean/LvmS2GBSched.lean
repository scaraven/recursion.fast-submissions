-- New for lvm2 MP-B cap pruning (CAP-L, 2026-11-17): stage S2GB's parameters and its schedule sizes (lead freeze P0).
import LvmS2GSSched
import LvmS2GUPlan

/-!
# The S2GB schedule (Lean stage `3` with `mbLin`, `leafOut` and `capPrune`)

* **`P20B`**: `P20S` with `capPrune` and `capKeep = [1]` (MP-B, lead freeze P0 and RE-FREEZE P1). The item list and the
  level records are S2GS's; the flags enter the tally only through `Params.capSendBits` (a cap item sends `2^c_r` nodes,
  absorbed by the next FS query: 64 B at `L0`, the root at `L1`, `L2`) and `Params.heapQ` (every opening asks
  `2^cap − 2^c_r` heap node queries after its paths).
* **`piStatic`**: the static part of `π` (header and body: scalars, roots, rows, siblings) = `piSize`; under
  `capPrune` the π tail of the uncovered cap-layer nodes follows it, at most `tailMax p` bytes
  (`32 · Σ (2^cap − 1)` over the opened levels: each covers at least one node).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The S2GB parameters**: `P20S`'s with `capPrune`; `L0` sends 2 cap nodes, `L1` and `L2` their roots
(RE-FREEZE P1); the mini-bus GKR one layer deeper (`busDepth` 13: the layer's seeds, 5,440 push leaves) and 888 table
columns (RE-FREEZE P2). -/
def P20B : Params :=
  { P20S with name := "P20B", capPrune := true, capKeep := [1], busDepth := 13, tableEvals := 888 }

/-- **The static part of `π`** (header and body in schedule order; the cap items count `2^capSendBits` nodes). -/
def piStatic (p : Params) : Nat := piSize p

/-- The cap-layer nodes an opened level may send in the π tail, `Σ (2^cap − 1)` over the schedule's openings (every
level covers at least one layer node: `t ≥ 1`; lead decision). -/
def capLayerNodes (p : Params) : Nat :=
  (schedule p).foldl (fun a it => match it with | .opening r => a + (2 ^ (p.level r).cap - 1) | _ => a) 0

/-- **The π tail's bound**: `32 · Σ (2^cap − 1)` over the opened levels under `capPrune`, else `0`. -/
def tailMax (p : Params) : Nat := if p.capPrune then nodeBytes * capLayerNodes p else 0

/-- **`V_S`'s queries per item at S2GB** (`qcItems` with an opening's `heapQ` heap node queries). -/
def qcItemsB (p : Params) : List Item → ℕ → ℕ
  | [], _ => 0
  | .read _ :: rest, b => qcItemsB p rest b
  | .readW _ _ :: rest, b => qcItemsB p rest b
  | .cap _ _ :: rest, b => qcItemsB p rest b
  | .sample :: rest, b => 1 + qcItemsB p rest b
  | .positions r :: rest, _ => (p.level r).nPosQ + qcItemsB p rest (p.level r).t
  | .opening r :: rest, b => b * (1 + (p.level r).path) + p.heapQ r.lv (p.level r).cap + qcItemsB p rest b

/-! ## `P20B`'s literals (proof help) -/

/-- The items of phase `.bus` at `P20B` (`ph20U_bus` with the mini-bus GKR at depth 13). -/
def ph20B_bus : List Item := [
    .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 9 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 12 16, .readW 4 16, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16,
    .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8,
    .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample, .readW 2 16, .readW 1 8, .sample,
    .readW 2 16, .readW 1 8, .sample, .readW 1 16, .readW 1 8, .sample, .readW 1 8, .sample, .readW 1 8, .sample,
    .readW 1 8, .sample, .readW 46 16, .readW 1 8, .sample, .readW 1 16, .sample, .sample, .sample, .sample, .sample,
    .read 2, .sample, .read 6, .sample, .sample, .read 4, .sample, .read 12, .sample, .sample, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 12,
    .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 12, .sample, .sample, .read 1]

/-- **`phases P20B`**, phase by phase. -/
def phasesB20 : List (Phase × List Item) :=
  [(.commit, ph20U_commit), (.bus, ph20B_bus), (.tape, ph20U_tape), (.wire, ph20U_wire),
   (.openMain, ph20U_openMain)]

set_option maxRecDepth 100000 in
/-- The phases at `P20B` are `phasesB20` (by `rfl` after the stage dispatch). -/
theorem phases_P20B_lit : phases P20B = phasesB20 := by
  rw [phases, ite_eq_right (show P20B.stage ≠ 1 by decide), ite_eq_right (show P20B.stage ≠ 2 by decide),
    ite_eq_left (show P20B.stage = 3 by decide), if_pos (show P20B.mbLin = true by decide)]
  rfl

/-- **`schedule P20B`**: the phase literals in order. -/
def schedB20 : List Item := ph20U_commit ++ ph20B_bus ++ ph20U_tape ++ ph20U_wire ++ ph20U_openMain

/-- The schedule at `P20B` is `schedB20`. -/
theorem schedule_P20B_lit : schedule P20B = schedB20 := by
  rw [schedule, phases_P20B_lit]
  simp only [phasesB20, schedB20, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- **`schedule P20B` in `appL` form** (proof help): the phase literals joined by `appL`, so a decision walks one
literal list (`++` costs a structural recursion per item and level). -/
noncomputable def schLA : List Item :=
  E2Q.appL ph20U_commit (E2Q.appL ph20B_bus (E2Q.appL ph20U_tape (E2Q.appL ph20U_wire ph20U_openMain)))

/-- The schedule at `P20B` is `schLA` (no evaluation). -/
theorem schedule_P20B_litA : schedule P20B = schLA := by
  rw [schedule_P20B_lit]
  simp only [schLA, schedB20, E2Q.appL_eq, List.append_assoc]

/-! `insertSorted` by `Nat.blt`/`Nat.beq` tests (`LvmSchedule`'s private `insF`, copied). -/

/-- `insertSorted` with `Nat.blt`/`Nat.beq` tests (proof help). -/
def insFB (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => bif Nat.blt x y then x :: y :: ys else bif Nat.beq x y then y :: ys else y :: insFB x ys

theorem insFB_eq (x : Nat) : ∀ l, insFB x l = insertSorted x l
  | [] => rfl
  | y :: ys => by
    rw [insFB, insertSorted, insFB_eq x ys]
    by_cases h1 : x < y
    · rw [if_pos h1, show Nat.blt x y = true from Nat.blt_eq.mpr h1, Bool.cond_true]
    · rw [if_neg h1, show Nat.blt x y = false from Bool.eq_false_iff.mpr (fun h => h1 (Nat.blt_eq.mp h)),
        Bool.cond_false]
      by_cases h2 : x = y
      · rw [if_pos h2, show Nat.beq x y = true from Nat.beq_eq.mpr h2, Bool.cond_true]
      · rw [if_neg h2, show Nat.beq x y = false from Bool.eq_false_iff.mpr (fun h => h2 (Nat.beq_eq.mp h)),
          Bool.cond_false]

/-! ## S2GB's sizes in one `List.rec` pass (proof help)

`TallyB` carries the tally's fields that the sizes read, the π tail's cap-layer nodes, the item count and `V_S`'s
query count; `runTallyB` walks the items once (`runTallyB_tally`, `runTallyB_cln`, `runTallyB_len`, `runTallyB_qc`
relate it to `Tally.run`, `capLayerNodes`, `List.length` and `qcItemsB`, by induction, no evaluation). -/

/-- The walk's state (proof help). -/
structure TallyB where
  pend : ℕ
  entries : ℕ
  trace : ℕ
  bScalars : ℕ
  bCaps : ℕ
  bRows : ℕ
  bSibs : ℕ
  pendOk : Bool
  fsl : List ℕ
  cln : ℕ
  len : ℕ
  qc : ℕ
  qb : ℕ

/-- An FS query of `32 + pend` bytes (`Tally.fs`). -/
def TallyB.fs (s : TallyB) : TallyB :=
  { s with entries := s.entries + 1, trace := s.trace + 1 * (40 + (32 + s.pend)), pend := 0,
           fsl := insFB (32 + s.pend) s.fsl }

/-- One item (`Tally.step`'s fields, the cap-layer nodes, the count, `qcItemsB`'s step). -/
def stepTallyB (p : Params) (s : TallyB) : Item → TallyB
  | .readW m w => { s with pend := s.pend + w * m, bScalars := s.bScalars + w * m, len := s.len + 1 }
  | .read m => { s with pend := s.pend + eBytes * m, bScalars := s.bScalars + eBytes * m, len := s.len + 1 }
  | .cap c r => { s with pend := s.pend + nodeBytes * 2 ^ p.capSendBits r.lv c,
                         bCaps := s.bCaps + nodeBytes * 2 ^ p.capSendBits r.lv c, len := s.len + 1 }
  | .sample => { s.fs with len := s.len + 1, qc := s.qc + 1 }
  | .positions r =>
    { s.fs with entries := s.fs.entries + ((p.level r).nPosQ - 1),
                trace := s.fs.trace + ((p.level r).nPosQ - 1) * (40 + 32),
                fsl := bif Nat.ble 2 (p.level r).nPosQ then insFB 32 s.fs.fsl else s.fs.fsl, len := s.len + 1,
                qc := s.qc + (p.level r).nPosQ, qb := (p.level r).t }
  | .opening r =>
    { s with entries := s.entries + (p.level r).t + (p.level r).t * (p.level r).path + p.heapQ r.lv (p.level r).cap,
             trace := s.trace + (p.level r).t * (40 + (p.level r).row) + (p.level r).t * (p.level r).path * (40 + 64) +
               p.heapQ r.lv (p.level r).cap * (40 + 64),
             bRows := s.bRows + (p.level r).t * (p.level r).row,
             bSibs := s.bSibs + (p.level r).t * (p.level r).path * nodeBytes,
             pendOk := s.pendOk && s.pend == 0, cln := s.cln + (2 ^ (p.level r).cap - 1), len := s.len + 1,
             qc := s.qc + (s.qb * (1 + (p.level r).path) + p.heapQ r.lv (p.level r).cap) }

/-- The walk over the items, in `List.rec` form. -/
noncomputable def runTallyB (p : Params) (l : List Item) : TallyB → TallyB :=
  l.rec (fun s => s) fun it _ ih s => ih (stepTallyB p s it)

/-- The tally's part of the state. -/
def TallyB.tp (s : TallyB) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Bool × List ℕ :=
  (s.pend, s.entries, s.trace, s.bScalars, s.bCaps, s.bRows, s.bSibs, s.pendOk, s.fsl)

/-- The same fields of a tally. -/
def Tally.tpB (t : Tally) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Bool × List ℕ :=
  (t.pend, t.entries, t.trace, t.bScalars, t.bCaps, t.bRows, t.bSibs, t.pendOk, t.fsLens)

theorem stepTallyB_tp (p : Params) (s : TallyB) (t : Tally) (h : s.tp = t.tpB) (it : Item) :
    (stepTallyB p s it).tp = (Tally.step p t it).tpB := by
  simp only [TallyB.tp, Tally.tpB, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases it with
  | positions r =>
    simp only [stepTallyB, Tally.step, TallyB.fs, Tally.fs, Tally.entry, TallyB.tp, Tally.tpB, h1, h2, h3, h4, h5,
      h6, h7, h8, h9, insFB_eq]
    by_cases hn : 2 ≤ (p.level r).nPosQ
    · rw [if_pos hn, show Nat.ble 2 (p.level r).nPosQ = true from Nat.ble_eq.mpr hn, Bool.cond_true]
    · rw [if_neg hn, show Nat.ble 2 (p.level r).nPosQ = false from
        Bool.eq_false_iff.mpr (fun e => hn (Nat.ble_eq.mp e)), Bool.cond_false]
  | _ =>
    simp only [stepTallyB, Tally.step, TallyB.fs, Tally.fs, Tally.entry, TallyB.tp, Tally.tpB, h1, h2, h3, h4, h5,
      h6, h7, h8, h9, insFB_eq]

theorem runTallyB_tally (p : Params) : ∀ (l : List Item) (s : TallyB) (t : Tally), s.tp = t.tpB →
    (runTallyB p l s).tp = (Tally.run p t l).tpB
  | [], _, _, h => h
  | it :: l, s, t, h => runTallyB_tally p l (stepTallyB p s it) (Tally.step p t it) (stepTallyB_tp p s t h it)

/-- An item's cap-layer nodes (`capLayerNodes`'s step). -/
def clnStepB (p : Params) : Item → ℕ
  | .opening r => 2 ^ (p.level r).cap - 1
  | _ => 0

theorem runTallyB_cln (p : Params) (f : ℕ → Item → ℕ) (hf : ∀ a it, f a it = a + clnStepB p it) :
    ∀ (l : List Item) (s : TallyB), (runTallyB p l s).cln = l.foldl f s.cln
  | [], _ => rfl
  | it :: l, s => by
    rw [List.foldl_cons, hf, show runTallyB p (it :: l) s = runTallyB p l (stepTallyB p s it) from rfl,
      runTallyB_cln p f hf l]
    congr 1
    cases it <;> rfl

theorem runTallyB_len (p : Params) : ∀ (l : List Item) (s : TallyB), (runTallyB p l s).len = s.len + l.length
  | [], _ => rfl
  | it :: l, s => by
    rw [show runTallyB p (it :: l) s = runTallyB p l (stepTallyB p s it) from rfl, runTallyB_len p l,
      List.length_cons, show (stepTallyB p s it).len = s.len + 1 by cases it <;> rfl]
    omega

theorem runTallyB_qc (p : Params) : ∀ (l : List Item) (s : TallyB),
    (runTallyB p l s).qc = s.qc + qcItemsB p l s.qb
  | [], _ => rfl
  | it :: l, s => by
    rw [show runTallyB p (it :: l) s = runTallyB p l (stepTallyB p s it) from rfl, runTallyB_qc p l]
    cases it <;> simp only [stepTallyB, TallyB.fs, qcItemsB] <;> omega

/-- The walk's start at `p` (`Tally.initP`'s fields). -/
def tallyB0 (p : Params) : TallyB :=
  ⟨0, (Tally.initP p).entries, (Tally.initP p).trace, 0, 0, 0, 0, true, [], 0, 0, 0, 0⟩

set_option maxRecDepth 100000 in
/-- Proof help: S2GB's sizes and its query bound from one kernel evaluation of `runTallyB` over `schLA`. -/
private theorem schedFactsB0 : ((piStatic P20B = 269336 ∧ qS P20B = 4134 ∧ hashedLen P20B = 575208 ∧
    streamLanes P20B = 71901 ∧ spongeBlocks P20B = 4230 ∧ (schedule P20B).length = 2764 ∧ tailMax P20B = 16288) ∧
    lengthRule P20B = true ∧
    (100 * streamLanes P20B ≤ 95 * streamCap P20B ∧ 100 * qS P20B ≤ 95 * 16384 ∧
      100 * spongeBlocks P20B ≤ 95 * 2 ^ P20B.recRowsLog ∧ spongeBlocks P20B ≤ 4295)) ∧
    2 + qcItemsB P20B (schedule P20B) 0 ≤ 16384 := by
  have hD : (fun s : TallyB => s.entries == 4134 && s.trace == 575207 && s.bScalars == 100368 && s.bCaps == 128 &&
      s.bRows == 94160 && s.bSibs == 73792 && s.pendOk &&
      s.fsl == [32, 40, 48, 56, 72, 80, 88, 96, 104, 112, 120, 128, 176, 184, 320, 328, 776, 840, 1056, 1712, 12368] &&
      s.cln == 509 && s.len == 2764 && s.qc == 4132) (runTallyB P20B schLA (tallyB0 P20B)) = true := by
    decide +kernel
  simp only [Bool.and_eq_true, beq_iff_eq] at hD
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨d2, d3⟩, d4⟩, d5⟩, d6⟩, d7⟩, d8⟩, d9⟩, dc⟩, dl⟩, dq⟩ := hD
  have hT := runTallyB_tally P20B schLA (tallyB0 P20B) (Tally.initP P20B) rfl
  simp only [TallyB.tp, Tally.tpB, Prod.mk.injEq] at hT
  obtain ⟨-, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hT
  have hcl : capLayerNodes P20B = 509 := by
    rw [capLayerNodes, schedule_P20B_litA, ← dc]
    exact (runTallyB_cln P20B _ (fun a it => by cases it <;> rfl) schLA (tallyB0 P20B)).symm
  have hlen : (schedule P20B).length = 2764 := by
    have h0 : (tallyB0 P20B).len = 0 := rfl
    rw [schedule_P20B_litA, ← dl, runTallyB_len, h0, Nat.zero_add]
  have hqc : qcItemsB P20B (schedule P20B) 0 = 4132 := by
    have h0 : (tallyB0 P20B).qc = 0 := rfl
    have h1 : (tallyB0 P20B).qb = 0 := rfl
    rw [schedule_P20B_litA, ← dq, runTallyB_qc, h0, h1, Nat.zero_add]
  rw [lengthRule, piStatic, piSize, streamLanes, spongeBlocks, tailMax, hcl, qS, hashedLen, hlen, hqc, tally,
    schedule_P20B_litA, ← t2, ← t3, ← t4, ← t5, ← t6, ← t7, ← t8, ← t9, d2, d3, d4, d5, d6, d7, d8, d9]
  decide +kernel

/-- **S2GB's sizes** (CAP-L K2, [exact] by decide; lead freeze P0, RE-FREEZE P1, P2): `piStatic = 269,336`,
`qS = 4,134` (S2GS's 3,618, 254 + 127 + 127 heap queries, 8 FS queries of the bus GKR's 13th layer), `L = 575,208`,
`T = 71,901`, 4,230 sponge blocks (at most 4,295, the `nodeChkBG` bound), 2,764 items, the π tail at most 16,288 B,
the length rule and the 95 % caps. -/
theorem sizes_P20B : (piStatic P20B = 269336 ∧ qS P20B = 4134 ∧ hashedLen P20B = 575208 ∧
    streamLanes P20B = 71901 ∧ spongeBlocks P20B = 4230 ∧ (schedule P20B).length = 2764 ∧ tailMax P20B = 16288) ∧
    lengthRule P20B = true ∧
    (100 * streamLanes P20B ≤ 95 * streamCap P20B ∧ 100 * qS P20B ≤ 95 * 16384 ∧
      100 * spongeBlocks P20B ≤ 95 * 2 ^ P20B.recRowsLog ∧ spongeBlocks P20B ≤ 4295) :=
  schedFactsB0.1

/-- **CAP-FRZ L** (proved): `phases` dispatches `P20B` to `phasesS2GL` (the flags do not enter the phases). -/
theorem phases_P20B : phases P20B = phasesS2GL P20B := by
  rw [phases, ite_eq_right (show P20B.stage ≠ 1 by decide), ite_eq_right (show P20B.stage ≠ 2 by decide),
    ite_eq_left (show P20B.stage = 3 by decide), if_pos (show P20B.mbLin = true by decide)]

/-- **CAP-FRZ L** (proved): S2GB's header and seed are S2GS's (888 and 912 bytes). -/
theorem headerBytesP_P20B : headerBytesP P20B = 888 ∧ seedLenP P20B = 912 ∧ P20B.accV = Lvm.VEq.accVT := by
  decide

/-- **CAP-FRZ L** (proved): S2GB's query bound. -/
theorem qcItemsB_P20B : 2 + qcItemsB P20B (schedule P20B) 0 ≤ 16384 :=
  schedFactsB0.2

end Lvm
