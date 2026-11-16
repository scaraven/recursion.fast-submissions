-- New for lvm2 E2F (E2F-L, 2026-11-13): the replay's static facts generic in the stage (`LvmMPXExtRun.openMain_P20`
-- and `LvmMPXLayout.layoutM_P20`'s facts with the stage's middle items, read widths and offsets), checked by one
-- Boolean evaluation per stage (`replayOkB`).
import LvmXSReplay
import LvmXSLayout
import LvmXSKinds
import LvmMPXExtEq

/-!
# The replay's facts at a stage

The pinned middle phases' items (`midItemsS st`) are reads (of any width) and samples; `openMain` is `P20`'s
(`mainHeadA1 … mainHeadB2`). With the widths as a list (`offK2L ws`, `pendK2L ws`, `fsPreK2L ws`: a read takes the
next width, so a stage is checked by one linear evaluation), the replay's segments (`A1` = the middle phases, `ρ`,
the intro and level 0's fold rounds; `A2`; level 0's opening; `B1`; `A3`; level 1's opening; `B2`; the residual)
absorb the chain's messages `fsMsgsS st` and end at the stage's offsets (`capOffS`, `resOffS`): **`replayOkB st`**.
`offK2W_eq_L` (and the `pend`/`fsPre` twins) turn the list forms into `trun_simK2W`'s.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.XS

/-! ## Kinds of `ItemF` -/

/-- The kinds of items (`itemK2` over `ItemF`: `readW m w` is `m` reads). -/
def itemK2F (p : Params) (sh : Ref → ℕ × ℕ) : List Item → List K2
  | [] => []
  | .readW m _ :: its => List.replicate m .read ++ itemK2F p sh its
  | .read m :: its => List.replicate m .read ++ itemK2F p sh its
  | .sample :: its => .sample :: itemK2F p sh its
  | .cap c r :: its => itemK2 p sh [.cap c r] ++ itemK2F p sh its
  | .positions r :: its => itemK2 p sh [.positions r] ++ itemK2F p sh its
  | .opening r :: its => itemK2 p sh [.opening r] ++ itemK2F p sh its

/-- Items of reads and samples only (`RSItems` over `ItemF`). -/
def RSItemsF : List Item → Bool
  | [] => true
  | .readW _ _ :: its => RSItemsF its
  | .read _ :: its => RSItemsF its
  | .sample :: its => RSItemsF its
  | _ :: _ => false

theorem itemK2F_rs (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item), RSItemsF its = true →
    itemK2F p sh its = (itemKindsS its).map toK2
  | [], _ => rfl
  | .readW m _ :: its, h => by
    rw [itemK2F, itemKindsS, itemK2F_rs p sh its h, List.map_append, List.map_replicate]; rfl
  | .read m :: its, h => by
    rw [itemK2F, itemKindsS, itemK2F_rs p sh its h, List.map_append, List.map_replicate]; rfl
  | .sample :: its, h => by
    rw [itemK2F, itemKindsS, itemK2F_rs p sh its h]; rfl
  | .cap _ _ :: _, h => by simp [RSItemsF] at h
  | .positions _ :: _, h => by simp [RSItemsF] at h
  | .opening _ :: _, h => by simp [RSItemsF] at h

theorem other_not_mem_F : ∀ (its : List Item), RSItemsF its = true → EvK.other ∉ itemKindsS its
  | [], _ => by simp [itemKindsS]
  | .readW m _ :: its, h => by
    simpa [itemKindsS] using other_not_mem_F its h
  | .read m :: its, h => by
    simpa [itemKindsS] using other_not_mem_F its h
  | .sample :: its, h => by
    simp only [itemKindsS, List.mem_cons, not_or]
    exact ⟨by decide, other_not_mem_F its h⟩
  | .cap _ _ :: _, h => by simp [RSItemsF] at h
  | .positions _ :: _, h => by simp [RSItemsF] at h
  | .opening _ :: _, h => by simp [RSItemsF] at h

/-! ## The offsets with a list of widths -/

/-- The body offset after the kinds, the widths a list (a read takes the next). -/
def offK2L : List ℕ → List K2 → ℕ → ℕ
  | _, [], off => off
  | ws, .read :: ks, off => offK2L ws.tail ks (off + ws.headD eBytes)
  | ws, .sample :: ks, off => offK2L ws ks off
  | ws, .commit _ _ nb :: ks, off => offK2L ws ks (off + nb)

/-- The first pending byte after the kinds, the widths a list. -/
def pendK2L : List ℕ → List K2 → ℕ → ℕ → ℕ
  | _, [], _, pend => pend
  | ws, .read :: ks, off, pend => pendK2L ws.tail ks (off + ws.headD eBytes) pend
  | ws, .sample :: ks, off, _ => pendK2L ws ks off off
  | ws, .commit _ _ nb :: ks, off, pend => pendK2L ws ks (off + nb) pend

/-- The slices the samples absorb, the widths a list. -/
def fsPreK2L : List ℕ → List K2 → ℕ → ℕ → List (ℕ × ℕ)
  | _, [], _, _ => []
  | ws, .read :: ks, off, pend => fsPreK2L ws.tail ks (off + ws.headD eBytes) pend
  | ws, .sample :: ks, off, pend => (pend, off - pend) :: fsPreK2L ws ks off off
  | ws, .commit _ _ nb :: ks, off, pend => fsPreK2L ws ks (off + nb) pend

theorem headD_eq_getD (ws : List ℕ) : ws.headD eBytes = ws.getD 0 eBytes := by cases ws <;> rfl

theorem getD_tail (ws : List ℕ) (i : ℕ) : ws.tail.getD i eBytes = ws.getD (i + 1) eBytes := by
  cases ws <;> simp

/-- The list forms are `trun_simK2W`'s when the widths from index `n` are the list's. -/
theorem offK2W_eq_L (rw : ℕ → ℕ) : ∀ (ks : List K2) (n : ℕ) (ws : List ℕ) (off pend : ℕ),
    (∀ i, rw (n + i) = ws.getD i eBytes) →
    offK2W rw ks n off = offK2L ws ks off ∧ pendK2W rw ks n off pend = pendK2L ws ks off pend ∧
      fsPreK2W rw ks n off pend = fsPreK2L ws ks off pend
  | [], _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | .read :: ks, n, ws, off, pend, h => by
    have h0 : rw n = ws.headD eBytes := by rw [headD_eq_getD, ← h 0, Nat.add_zero]
    have h1 : ∀ i, rw (n + 1 + i) = ws.tail.getD i eBytes := fun i => by
      rw [getD_tail, ← h (i + 1), Nat.add_right_comm, Nat.add_assoc, Nat.add_comm i]
    obtain ⟨a, b, c⟩ := offK2W_eq_L rw ks (n + 1) ws.tail (off + rw n) pend h1
    simp only [offK2W, pendK2W, fsPreK2W, offK2L, pendK2L, fsPreK2L, ← h0]
    exact ⟨a, b, c⟩
  | .sample :: ks, n, ws, off, pend, h => by
    obtain ⟨a, b, c⟩ := offK2W_eq_L rw ks n ws off off h
    simp only [offK2W, pendK2W, fsPreK2W, offK2L, pendK2L, fsPreK2L]
    exact ⟨a, b, by rw [c]⟩
  | .commit _ _ nb :: ks, n, ws, off, pend, h => by
    obtain ⟨a, b, c⟩ := offK2W_eq_L rw ks n ws (off + nb) pend h
    simp only [offK2W, pendK2W, fsPreK2W, offK2L, pendK2L, fsPreK2L]
    exact ⟨a, b, c⟩

/-! ## A stage's segments -/

/-- The middle items' kinds. -/
def kMS (st : XStage) : List K2 := itemK2F st.p shMain (midItemsS st)

/-- Segment `A1`: the middle phases, `ρ`, the intro, level 0's fold rounds. -/
def kA1S (st : XStage) : List K2 := kMS st ++ itemK2 P20 shMain mainHeadA1

/-- The reads before segments `A2`, `B1`, `A3`, `B2` and the residual. -/
def nr1 (st : XStage) : ℕ := readsK2 (kA1S st)
def nr2 (st : XStage) : ℕ := nr1 st + readsK2 (itemK2 P20 shMain mainHeadA2)
def nr3 (st : XStage) : ℕ := nr2 st + readsK2 (itemK2 P20 shMain mainHeadB1)
def nr4 (st : XStage) : ℕ := nr3 st + readsK2 (itemK2 P20 shMain mainHeadA3)
def nr5 (st : XStage) : ℕ := nr4 st + readsK2 (itemK2 P20 shMain mainHeadB2)

/-- The root cap's end. -/
def o1S (st : XStage) : ℕ := st.hb + 8192

/-- Segment `A1`'s end. -/
def offA1 (st : XStage) : ℕ := offK2L (readWidthsS st) (kA1S st) (o1S st)
def pendA1 (st : XStage) : ℕ := pendK2L (readWidthsS st) (kA1S st) (o1S st) st.hb
/-- Segment `A2`'s end (level 0's opening's start). -/
def offA2 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st)
def pendA2 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st)
/-- Level 0's opening's end: `115` positions of `8·occ0 + 32·11` bytes. -/
def q0End (st : XStage) : ℕ := offA2 st + 115 * (8 * st.occ0 + 32 * 11)
/-- Segment `B1`'s end (level 2's cap's start). -/
def offB1 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st)
def pendB1 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st)
/-- Segment `A3`'s end (level 1's opening's start). -/
def offA3 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st)
def pendA3 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st)
/-- Level 1's opening's end: `77` positions of `8·48 + 32·9` bytes. -/
def q1End (st : XStage) : ℕ := offA3 st + 77 * (8 * 48 + 32 * 9)
/-- Segment `B2`'s end (the residual's start). -/
def offB2 (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st)
def pendB2 (st : XStage) : ℕ :=
  pendK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st)

/-- The middle phases' samples. -/
def nMidS (st : XStage) : ℕ := (itemKindsS (midItemsS st)).count .sample

/-- **The replay's static facts at a stage** (one evaluation per stage; right-nested). -/
def replayOkB (st : XStage) : Bool :=
  RSItemsF (midItemsS st) && (
  fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb == ((fsMsgsS st).drop 1).take (nMidS st + 7) && (
  offA1 st == capOffS st 1 && (
  fsPreK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st) ==
    ((fsMsgsS st).drop (nMidS st + 8)).take 35 && (
  offA2 st == pendA2 st && (
  fsPreK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st) ==
    ((fsMsgsS st).drop (nMidS st + 43)).take 4 && (
  offB1 st == capOffS st 2 && (
  fsPreK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st) ==
    ((fsMsgsS st).drop (nMidS st + 47)).take 26 && (
  offA3 st == pendA3 st && (
  fsPreK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st) ==
    ((fsMsgsS st).drop (nMidS st + 73)).take 4 && (
  offB2 st == resOffS st && (
  ((readWidthsS st).drop (nr5 st)).take (2 ^ 9) == List.replicate (2 ^ 9) eBytes && (
  foldPosS st 0 0 == nMidS st + 3 && (foldPosS st 1 0 == nMidS st + 44 && (foldPosS st 2 0 == nMidS st + 74 && (
  nChainS st == nMidS st + 78 && (
  st.hb % 8 == 0 && (capOffS st 1 % 8 == 0 && (capOffS st 2 % 8 == 0 && (resOffS st % 8 == 0 && (
  decide ((if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb) && (decide (8 ≤ st.hb) && (decide (st.occ0 ≤ 64) && (
  decide (o1S st ≤ st.pz) && (decide (capOffS st 1 + 32 * 2 ^ 7 ≤ st.pz) && (
  decide (capOffS st 2 + 32 * 2 ^ 7 ≤ st.pz) && decide (resOffS st + 24 * 2 ^ 9 ≤ st.pz))))))))))))))))))))))))))

/-- **The replay's facts at a stage.** -/
structure ReplayOK (st : XStage) : Prop where
  rs : RSItemsF (midItemsS st) = true
  fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7)
  oA1 : offA1 st = capOffS st 1
  fA2 : fsPreK2L ((readWidthsS st).drop (nr1 st)) (itemK2 P20 shMain mainHeadA2) (offA1 st) (pendA1 st) =
    ((fsMsgsS st).drop (nMidS st + 8)).take 35
  oA2 : offA2 st = pendA2 st
  fB1 : fsPreK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0End st) (q0End st) =
    ((fsMsgsS st).drop (nMidS st + 43)).take 4
  oB1 : offB1 st = capOffS st 2
  fA3 : fsPreK2L ((readWidthsS st).drop (nr3 st)) (itemK2 P20 shMain mainHeadA3) (offB1 st) (pendB1 st) =
    ((fsMsgsS st).drop (nMidS st + 47)).take 26
  oA3 : offA3 st = pendA3 st
  fB2 : fsPreK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1End st) (q1End st) =
    ((fsMsgsS st).drop (nMidS st + 73)).take 4
  oB2 : offB2 st = resOffS st
  r24 : ((readWidthsS st).drop (nr5 st)).take (2 ^ 9) = List.replicate (2 ^ 9) eBytes
  fp0 : foldPosS st 0 0 = nMidS st + 3
  fp1 : foldPosS st 1 0 = nMidS st + 44
  fp2 : foldPosS st 2 0 = nMidS st + 74
  nc : nChainS st = nMidS st + 78
  a0 : st.hb % 8 = 0
  a1 : capOffS st 1 % 8 = 0
  a2 : capOffS st 2 % 8 = 0
  ar : resOffS st % 8 = 0
  /-- The header's fixed part (without `σ_leaf` at `leafOut`, lvm2 σ_LEAF) fits the header. -/
  hl : (if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb
  h8 : 8 ≤ st.hb
  oc : st.occ0 ≤ 64
  s0 : o1S st ≤ st.pz
  s1 : capOffS st 1 + 32 * 2 ^ 7 ≤ st.pz
  s2 : capOffS st 2 + 32 * 2 ^ 7 ≤ st.pz
  sr : resOffS st + 24 * 2 ^ 9 ≤ st.pz

/-- The evaluation gives the facts. -/
theorem replayOK_of {st : XStage} (h : replayOkB st = true) : ReplayOK st := by
  simp only [replayOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨rs, fA1, oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, fp0, fp1, fp2, nc, a0, a1, a2, ar, hl, h8, oc,
    s0, s1, s2, sr⟩ := h
  exact ⟨rs, fA1, oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, fp0, fp1, fp2, nc, a0, a1, a2, ar, hl, h8, oc,
    s0, s1, s2, sr⟩

/-! ## The run-length checker

`replayOkB` expands every run `readW m w` into `m` kinds and `m` widths (≈ 7 k entries at S2GF, ≈ 16 s of kernel
time). `replayOkR` walks the middle items once by runs (`endF`, `sampR`), and checks the segments after them with the
widths of `openMain`'s items only; `replayOK_ofR` turns it into `ReplayOK` for every stage. -/

/-- An item's read widths. -/
def wsI : Item → List ℕ
  | .readW m w => List.replicate m w
  | .read m => List.replicate m eBytes
  | _ => []

theorem readWidthsS_eq (st : XStage) : readWidthsS st = st.items.flatMap wsI := by
  unfold readWidthsS
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

/-- `fsPre`'s body offset and first pending byte after the items. -/
def endF (p : Params) : List Item → ℕ → ℕ → ℕ × ℕ
  | [], off, pend => (off, pend)
  | .read m :: r, off, pend => endF p r (off + eBytes * m) pend
  | .readW m w :: r, off, pend => endF p r (off + w * m) pend
  | .cap c _ :: r, off, pend => endF p r (off + nodeBytes * 2 ^ c) pend
  | .sample :: r, off, _ => endF p r off off
  | .positions _ :: r, off, _ => endF p r off off
  | .opening ref :: r, off, _ =>
      endF p r (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))
        (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))

theorem fsPre_append (p : Params) : ∀ (a b : List Item) (off pend : ℕ),
    Lvm.X.fsPre p (a ++ b) off pend =
      Lvm.X.fsPre p a off pend ++ Lvm.X.fsPre p b (endF p a off pend).1 (endF p a off pend).2
  | [], _, _, _ => rfl
  | it :: a, b, off, pend => by
    cases it <;> simp only [List.cons_append, Lvm.X.fsPre, endF, fsPre_append p a b, List.append_assoc]

theorem endF_append (p : Params) : ∀ (a b : List Item) (off pend : ℕ),
    endF p (a ++ b) off pend = endF p b (endF p a off pend).1 (endF p a off pend).2
  | [], _, _, _ => rfl
  | it :: a, b, off, pend => by cases it <;> simp only [List.cons_append, endF, endF_append p a b]

/-- The samples among the items. -/
def sampR : List Item → ℕ
  | [] => 0
  | .sample :: r => sampR r + 1
  | .readW _ _ :: r | .read _ :: r | .cap _ _ :: r | .positions _ :: r | .opening _ :: r => sampR r

theorem fsPre_length_rs (p : Params) : ∀ (its : List Item) (off pend : ℕ), RSItemsF its = true →
    (Lvm.X.fsPre p its off pend).length = sampR its
  | [], _, _, _ => rfl
  | .readW _ _ :: its, _, _, h | .read _ :: its, _, _, h => by
    rw [Lvm.X.fsPre, sampR]; exact fsPre_length_rs p its _ _ h
  | .sample :: its, _, _, h => by
    rw [Lvm.X.fsPre, sampR, List.length_cons, fsPre_length_rs p its _ _ h]
  | .cap _ _ :: _, _, _, h | .positions _ :: _, _, _, h | .opening _ :: _, _, _, h => by simp [RSItemsF] at h

theorem count_sample_rs : ∀ (its : List Item), RSItemsF its = true → (itemKindsS its).count .sample = sampR its
  | [], _ => rfl
  | .readW _ _ :: its, h | .read _ :: its, h => by
    simp [itemKindsS, sampR, List.count_append, List.count_replicate, count_sample_rs its h]
  | .sample :: its, h => by
    simp [itemKindsS, sampR, List.count_cons, count_sample_rs its h]
  | .cap _ _ :: _, h | .positions _ :: _, h | .opening _ :: _, h => by simp [RSItemsF] at h

theorem readsK2_append : ∀ (a b : List K2), readsK2 (a ++ b) = readsK2 a + readsK2 b
  | [], b => (Nat.zero_add _).symm
  | .read :: a, b => by
    rw [List.cons_append, readsK2, readsK2, readsK2_append a b, Nat.add_right_comm]
  | .sample :: a, b => readsK2_append a b
  | .commit _ _ _ :: a, b => readsK2_append a b

theorem K2L_rep (w : ℕ) (ws : List ℕ) (ks : List K2) : ∀ (m off pend : ℕ),
    offK2L (List.replicate m w ++ ws) (List.replicate m .read ++ ks) off = offK2L ws ks (off + w * m) ∧
    pendK2L (List.replicate m w ++ ws) (List.replicate m .read ++ ks) off pend = pendK2L ws ks (off + w * m) pend ∧
    fsPreK2L (List.replicate m w ++ ws) (List.replicate m .read ++ ks) off pend =
      fsPreK2L ws ks (off + w * m) pend ∧
    readsK2 (List.replicate m .read ++ ks) = m + readsK2 ks
  | 0, off, pend => by simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      and_self]
  | m + 1, off, pend => by
    obtain ⟨a, b, c, d⟩ := K2L_rep w ws ks m (off + w) pend
    have e : off + w * (m + 1) = off + w + w * m := by rw [Nat.mul_succ, Nat.add_comm (w * m), Nat.add_assoc]
    simp only [List.replicate_succ, List.cons_append, offK2L, pendK2L, fsPreK2L, readsK2, List.headD_cons,
      List.tail_cons, a, b, c, d, e, Nat.add_right_comm m 1, and_self]

/-- **The middle items by runs**: the list forms over `items ++ rest` are the run walk (`endF`, `fsPre`) followed by
the list forms over `rest`. -/
theorem K2L_items (p : Params) (sh : Ref → ℕ × ℕ) : ∀ (its : List Item) (ws : List ℕ) (ks : List K2) (off pend : ℕ),
    RSItemsF its = true →
    offK2L (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) off = offK2L ws ks (endF p its off pend).1 ∧
    pendK2L (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) off pend =
      pendK2L ws ks (endF p its off pend).1 (endF p its off pend).2 ∧
    fsPreK2L (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) off pend =
      Lvm.X.fsPre p its off pend ++ fsPreK2L ws ks (endF p its off pend).1 (endF p its off pend).2 ∧
    readsK2 (itemK2F p sh its ++ ks) = (its.flatMap wsI).length + readsK2 ks
  | [], ws, ks, off, pend, _ => by
    simp only [List.flatMap_nil, List.nil_append, itemK2F, endF, Lvm.X.fsPre, List.length_nil, Nat.zero_add,
      and_self]
  | .readW m w :: its, ws, ks, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_items p sh its ws ks (off + w * m) pend h
    obtain ⟨a', b', c', d'⟩ := K2L_rep w (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) m off pend
    simp only [List.flatMap_cons, wsI, itemK2F, List.append_assoc, endF, Lvm.X.fsPre, a', b', c', d', a, b, c, d,
      List.length_append, List.length_replicate, Nat.add_assoc, and_self]
  | .read m :: its, ws, ks, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_items p sh its ws ks (off + eBytes * m) pend h
    obtain ⟨a', b', c', d'⟩ := K2L_rep eBytes (its.flatMap wsI ++ ws) (itemK2F p sh its ++ ks) m off pend
    simp only [List.flatMap_cons, wsI, itemK2F, List.append_assoc, endF, Lvm.X.fsPre, a', b', c', d', a, b, c, d,
      List.length_append, List.length_replicate, Nat.add_assoc, and_self]
  | .sample :: its, ws, ks, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_items p sh its ws ks off off h
    refine ⟨a, b, ?_, d⟩
    rw [List.flatMap_cons, show wsI .sample = [] from rfl, List.nil_append, itemK2F, List.cons_append, fsPreK2L,
      Lvm.X.fsPre, endF, List.cons_append]
    exact congrArg _ c
  | .cap _ _ :: _, _, _, _, _, h | .positions _ :: _, _, _, _, _, h | .opening _ :: _, _, _, _, _, h => by
    simp [RSItemsF] at h

/-- The chain offset of level `i`'s fold rounds after `foldPosS`'s `nPreS st + 3`. -/
def lvOffS (st : XStage) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then lvlFsS st 0 else lvlFsS st 0 + lvlFsS st 1

/-- Level `i`'s cap offset (`i < 2`) or the residual's (`i = 2`), read off `R`, the chain's messages after the middle
phases' (`capOffS`, `resOffS`). -/
def capR (st : XStage) (R : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  (R.getD (2 + lvOffS st i + ((mainLS st i).fold - 1)) (0, 0)).1 + 2 * eBytes

/-- The segments after `A1` (`replayOkB`'s conjuncts from `oA1` on), with `ws0` the widths after `A1`, `oA`/`pA`
`A1`'s end, `nM` the middle phases' samples and `R` the chain's messages after theirs. -/
def replayOkG (st : XStage) (ws0 : List ℕ) (oA pA nM : ℕ) (R : List (ℕ × ℕ)) : Bool :=
  let w2 := ws0.drop (readsK2 (itemK2 P20 shMain mainHeadA2))
  let w3 := w2.drop (readsK2 (itemK2 P20 shMain mainHeadB1))
  let w4 := w3.drop (readsK2 (itemK2 P20 shMain mainHeadA3))
  let w5 := w4.drop (readsK2 (itemK2 P20 shMain mainHeadB2))
  let q0 := offK2L ws0 (itemK2 P20 shMain mainHeadA2) oA + 115 * (8 * st.occ0 + 32 * 11)
  let oB1 := offK2L w2 (itemK2 P20 shMain mainHeadB1) q0
  let pB1 := pendK2L w2 (itemK2 P20 shMain mainHeadB1) q0 q0
  let q1 := offK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 + 77 * (8 * 48 + 32 * 9)
  oA == capR st R 0 && (
  fsPreK2L ws0 (itemK2 P20 shMain mainHeadA2) oA pA == (R.drop 7).take 35 && (
  offK2L ws0 (itemK2 P20 shMain mainHeadA2) oA == pendK2L ws0 (itemK2 P20 shMain mainHeadA2) oA pA && (
  fsPreK2L w2 (itemK2 P20 shMain mainHeadB1) q0 q0 == (R.drop 42).take 4 && (
  oB1 == capR st R 1 && (
  fsPreK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 pB1 == (R.drop 46).take 26 && (
  offK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 == pendK2L w3 (itemK2 P20 shMain mainHeadA3) oB1 pB1 && (
  fsPreK2L w4 (itemK2 P20 shMain mainHeadB2) q1 q1 == (R.drop 72).take 4 && (
  offK2L w4 (itemK2 P20 shMain mainHeadB2) q1 == capR st R 2 && (
  w5.take (2 ^ 9) == List.replicate (2 ^ 9) eBytes && (
  lvOffS st 0 == 0 && (lvOffS st 1 == 41 && (lvOffS st 2 == 71 && (
  lvOffS st 2 + ((mainLS st 2).fold - 1) == 74 && (
  st.hb % 8 == 0 && (capR st R 0 % 8 == 0 && (capR st R 1 % 8 == 0 && (capR st R 2 % 8 == 0 && (
  decide ((if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb) && (decide (8 ≤ st.hb) && (decide (st.occ0 ≤ 64) && (
  decide (o1S st ≤ st.pz) && (decide (capR st R 0 + 32 * 2 ^ 7 ≤ st.pz) && (
  decide (capR st R 1 + 32 * 2 ^ 7 ≤ st.pz) && decide (capR st R 2 + 24 * 2 ^ 9 ≤ st.pz))))))))))))))))))))))))

/-- **The run-length checker** at a split `st.items = pre ++ rest` (`pre`: the root cap and the middle phases): the
first item has no reads or messages and ends at `o1S`; the middle items `pre.drop 1` are reads and samples, walked
once by runs; `A1`'s slices; `replayOkG` at the walk's end, with the messages of `rest` from there. -/
def replayOkR (st : XStage) (pre rest : List Item) : Bool :=
  let e := endF st.p (pre.drop 1) (o1S st) st.hb
  let ws := rest.flatMap wsI
  let R := Lvm.X.fsPre st.p rest e.1 e.2
  let kA := itemK2 P20 shMain mainHeadA1
  !pre.isEmpty && (
  ((pre.take 1).flatMap wsI).isEmpty && (
  (Lvm.X.fsPre st.p (pre.take 1) st.hb st.hb).isEmpty && (
  endF st.p (pre.take 1) st.hb st.hb == (o1S st, st.hb) && (
  RSItemsF (pre.drop 1) && (
  fsPreK2L ws kA e.1 e.2 == R.take 7 &&
  replayOkG st (ws.drop (readsK2 kA)) (offK2L ws kA e.1) (pendK2L ws kA e.1 e.2) (sampR (pre.drop 1)) R)))))

theorem getD_msgs (x : ℕ × ℕ) (F R : List (ℕ × ℕ)) (k : ℕ) :
    (x :: (F ++ R)).getD (F.length + 1 + k) (0, 0) = R.getD k (0, 0) := by
  rw [List.getD_eq_getElem?_getD, show F.length + 1 + k = F.length + k + 1 by (clear * - F k; omega), List.getElem?_cons_succ,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

theorem drop_msgs (x : ℕ × ℕ) (F R : List (ℕ × ℕ)) (k : ℕ) :
    (x :: (F ++ R)).drop (F.length + 1 + k) = R.drop k := by
  rw [show F.length + 1 + k = F.length + k + 1 by (clear * - F k; omega), List.drop_succ_cons, List.drop_append,
    List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left]

/-- `replayOkG` at the stage's own `A1` values gives `ReplayOK`, the chain's messages being `F ++ R` after the seed
with `F` the middle phases' (`nMidS st = nPreS st = |F|`). -/
theorem replayOK_ofG {st : XStage} (F R : List (ℕ × ℕ)) (rs : RSItemsF (midItemsS st) = true)
    (fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7))
    (hmsg : fsMsgsS st = (8, st.hb - 8) :: (F ++ R)) (hnM : nMidS st = F.length) (hnP : nPreS st = F.length)
    (h : replayOkG st ((readWidthsS st).drop (nr1 st)) (offA1 st) (pendA1 st) F.length R = true) :
    ReplayOK st := by
  have hfp : ∀ i j, foldPosS st i j = F.length + 1 + (2 + lvOffS st i + j) := fun i j => by
    rw [show foldPosS st i j = nPreS st + 3 + lvOffS st i + j from rfl, hnP]; (clear * - F st i j; omega)
  have hc : ∀ i, (fsMsgsS st).getD (foldPosS st i ((mainLS st i).fold - 1)) (0, 0) =
      R.getD (2 + lvOffS st i + ((mainLS st i).fold - 1)) (0, 0) := fun i => by
    rw [hfp, hmsg, getD_msgs]
  have hc1 : capOffS st 1 = capR st R 0 := congrArg (·.1 + 2 * eBytes) (hc 0)
  have hc2 : capOffS st 2 = capR st R 1 := congrArg (·.1 + 2 * eBytes) (hc 1)
  have hcr : resOffS st = capR st R 2 := by
    rw [resOffS, nChainS, Nat.add_sub_cancel]; exact congrArg (·.1 + 2 * eBytes) (hc 2)
  have hd : ∀ k n, n = nMidS st + 1 + k → (fsMsgsS st).drop n = R.drop k := fun k n hn => by
    rw [hn, hmsg, hnM, drop_msgs]
  simp only [replayOkG, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.drop_drop] at h
  obtain ⟨oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, l0, l1, l2, l3, a0, a1, a2, ar, hl, h8, oc,
    s0, s1, s2, sr⟩ := h
  refine ⟨rs, fA1, by rw [hc1]; exact oA1, by rw [hd 7 _ (by (clear * - st F R; omega))]; exact fA2, oA2,
    by rw [hd 42 _ (by (clear * - st F R; omega))]; exact fB1, by rw [hc2]; exact oB1, by rw [hd 46 _ (by (clear * - st F R; omega))]; exact fA3, oA3,
    by rw [hd 72 _ (by (clear * - st F R; omega))]; exact fB2, by rw [hcr]; exact oB2, r24, ?_, ?_, ?_, ?_, a0, by rw [hc1]; exact a1,
    by rw [hc2]; exact a2, by rw [hcr]; exact ar, hl, h8, oc, s0, by rw [hc1]; exact s1, by rw [hc2]; exact s2,
    by rw [hcr]; exact sr⟩
  · have := hfp 0 0; (clear * - st F R hnM hnP l0 this; omega)
  · have := hfp 1 0; (clear * - st F R hnM hnP l1 this; omega)
  · have := hfp 2 0; (clear * - st F R hnM hnP l2 this; omega)
  · have := hfp 2 ((mainLS st 2).fold - 1); rw [nChainS]; (clear * - st F R hnM hnP l2 l3 this; omega)

/-- **The run-length checker gives the replay's facts** (every stage, at any split of its items with `pre` of
length `st.nOpen`). -/
theorem replayOK_ofR {st : XStage} {pre rest : List Item} (hs : st.items = pre ++ rest)
    (hn : st.nOpen = pre.length) (h : replayOkR st pre rest = true) : ReplayOK st := by
  simp only [replayOkR, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨-, hw1, hf1, he1, rs, fA, hG⟩ := h
  have hmid : midItemsS st = pre.drop 1 := by rw [midItemsS, hs, hn, List.take_append_length]
  have hrest : st.items.drop st.nOpen = rest := by rw [hs, hn, List.drop_left' rfl]
  have hpre : pre = pre.take 1 ++ pre.drop 1 := (List.take_append_drop 1 pre).symm
  rw [← hmid] at rs fA hG
  rw [← hmid] at hpre
  have hW : readWidthsS st = (midItemsS st).flatMap wsI ++ rest.flatMap wsI := by
    rw [readWidthsS_eq, hs, hpre, List.flatMap_append, List.flatMap_append, hw1, List.nil_append]
  obtain ⟨ho, hp, hf, hr⟩ := K2L_items st.p shMain (midItemsS st) (rest.flatMap wsI)
    (itemK2 P20 shMain mainHeadA1) (o1S st) st.hb rs
  have hoA : offA1 st = offK2L (rest.flatMap wsI) (itemK2 P20 shMain mainHeadA1)
      (endF st.p (midItemsS st) (o1S st) st.hb).1 := by
    rw [offA1, hW]; exact ho
  have hpA : pendA1 st = pendK2L (rest.flatMap wsI) (itemK2 P20 shMain mainHeadA1)
      (endF st.p (midItemsS st) (o1S st) st.hb).1 (endF st.p (midItemsS st) (o1S st) st.hb).2 := by
    rw [pendA1, hW]; exact hp
  have hnr : (readWidthsS st).drop (nr1 st) = (rest.flatMap wsI).drop (readsK2 (itemK2 P20 shMain mainHeadA1)) := by
    rw [show nr1 st = readsK2 (itemK2F st.p shMain (midItemsS st) ++ itemK2 P20 shMain mainHeadA1) from rfl, hr, hW,
      List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left]
  have hpreF : Lvm.X.fsPre st.p pre st.hb st.hb = Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb := by
    rw [hpre, fsPre_append, hf1, he1, List.nil_append]
  have hfs : Lvm.X.fsPre st.p st.items st.hb st.hb = Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb ++
      Lvm.X.fsPre st.p rest (endF st.p (midItemsS st) (o1S st) st.hb).1
        (endF st.p (midItemsS st) (o1S st) st.hb).2 := by
    have hend : endF st.p pre st.hb st.hb = endF st.p (midItemsS st) (o1S st) st.hb := by
      rw [hpre, endF_append, he1]
    rw [hs, fsPre_append, hpreF, hend]
  have hlen : (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length = sampR (midItemsS st) :=
    fsPre_length_rs _ _ _ _ rs
  have hnM : nMidS st = (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length := by
    rw [hlen]; exact count_sample_rs _ rs
  have hmsg : fsMsgsS st = (8, st.hb - 8) :: (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb ++
      Lvm.X.fsPre st.p rest (endF st.p (midItemsS st) (o1S st) st.hb).1
        (endF st.p (midItemsS st) (o1S st) st.hb).2) := by
    rw [fsMsgsS, hfs]
  have hnP : nPreS st = (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length := by
    rw [nPreS, hs, hn, List.take_append_length, hpreF]
  have hle : (Lvm.X.fsPre st.p (midItemsS st) (o1S st) st.hb).length ≤ nMidS st + 7 := by
    rw [hnM]; exact Nat.le_add_right _ _
  have fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1S st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7) := by
    rw [hW]
    refine hf.trans ?_
    rw [hmsg, List.drop_one, List.tail_cons, fA, List.take_append, List.take_of_length_le hle, hnM,
      Nat.add_sub_cancel_left]
  refine replayOK_ofG _ _ rs fA1 hmsg hnM hnP ?_
  rw [hnr, hoA, hpA, hlen]
  exact hG

end Lvm.ASM
