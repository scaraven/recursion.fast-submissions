-- New for lvm2 MP-B cap pruning (CAP-X5, 2026-11-17): S2GB's replay record over the expanded proof (`ReplayOK`'s
-- twin for `ext_eqB_gen`: the scheme reads `fillB P20B π w`, the root cap 64 bytes, the level caps 32, the paths 18/16
-- levels), one run-length evaluation, and the expansion's byte copies of π.
import LvmS2GBFillEq
import LvmS2GBTail
import LvmXSExtEqS

/-!
# S2GB's replay record

The scheme `schemeSWB fmtB20` reads the expanded proof `π' = fillB P20B π w`: π's static bytes with `m − c` upper
siblings per path inserted (`t·32·(m − c)` bytes per opening). Before level 0's opening the offsets of π' are π's; after
it they are shifted by `25,760`, after level 1's opening by `43,008`. The extractor reads π (`stB20`).

* **`ReplayOKB`**: the replay facts at the scheme's offsets (`o1B`, `offA1B` … `offB2B`, the caps' commits of 32 bytes,
  `kA2B`/`kA3B`), with the chain's messages as π's shifted (`shM`), and the static stretches of π' between the
  openings; **`replayOKB_stB20`** decides it once (`replayOkRB`, run-length, as `replayOkR`).
* **`copyR0`/`copyR1`/`copyR2`**: π' copies π's bytes before level 0's opening, between the openings 0 and 1, and between
  the openings 1 and 2, with their shifts.
* **`K2L_mono`**: the slices a kind walk absorbs lie between its first pending byte and its end.
* **`chainTB`**: `chainTS` over π' (the messages shifted, the bytes copied).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.XB Lvm.FS
open LeanVM.Protocol.Compile hiding Proof Bytes

/-! ## The scheme's offsets on π' -/

/-- A commit kind with `nb` bytes (the sent caps at S2GB). -/
def fixK (nb : ℕ) : K2 → K2
  | .commit ht w _ => .commit ht w nb
  | k => k

/-- Segment `A2`'s kinds at S2GB: level 1's cap is its root (32 bytes). -/
def kA2B : List K2 := (itemK2 P20 shMain mainHeadA2).map (fixK 32)
/-- Segment `A3`'s kinds at S2GB: level 2's cap is its root (32 bytes). -/
def kA3B : List K2 := (itemK2 P20 shMain mainHeadA3).map (fixK 32)

/-- The root cap's end on π' (two nodes). -/
def o1B (st : XStage) : ℕ := st.hb + 64
def offA1B (st : XStage) : ℕ := offK2L (readWidthsS st) (kA1S st) (o1B st)
def pendA1B (st : XStage) : ℕ := pendK2L (readWidthsS st) (kA1S st) (o1B st) st.hb
def offA2B (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr1 st)) kA2B (offA1B st)
def pendA2B (st : XStage) : ℕ := pendK2L ((readWidthsS st).drop (nr1 st)) kA2B (offA1B st) (pendA1B st)
/-- Level 0's opening's end on π': `115` positions of `8·occ0 + 32·18` bytes. -/
def q0EndB (st : XStage) : ℕ := (offA2B st) + 115 * (8 * st.occ0 + 32 * 18)
def offB1B (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0EndB st)
def pendB1B (st : XStage) : ℕ := pendK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0EndB st) (q0EndB st)
def offA3B (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr3 st)) kA3B (offB1B st)
def pendA3B (st : XStage) : ℕ := pendK2L ((readWidthsS st).drop (nr3 st)) kA3B (offB1B st) (pendB1B st)
/-- Level 1's opening's end on π': `77` positions of `8·48 + 32·16` bytes. -/
def q1EndB (st : XStage) : ℕ := (offA3B st) + 77 * (8 * 48 + 32 * 16)
def offB2B (st : XStage) : ℕ := offK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1EndB st)
def pendB2B (st : XStage) : ℕ := pendK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1EndB st) (q1EndB st)

/-- Messages shifted by `s`. -/
def shM (s : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.map fun m => (m.1 + s, m.2)

theorem shM_zero (l : List (ℕ × ℕ)) : shM 0 l = l := by
  simp [shM]

/-- **One walk of the items**: at every opening its index and the static/expanded sums before and after it; the
totals last. -/
def openScan (p : Params) : List Item → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)
  | [], i, s, e => [(i, s, e, s, e)]
  | it :: r, i, s, e =>
    if isOpenI it then (i, s, e, s + fillStat p it, e + fillExp p it) ::
      openScan p r (i + 1) (s + fillStat p it) (e + fillExp p it)
    else openScan p r (i + 1) (s + fillStat p it) (e + fillExp p it)

/-- `P20B`'s openings (items 2698, 2729, 2745 of 2764) and totals. -/
def oscB : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2698, 87144, 0, 169944, 25760), (2729, 170312, 25760, 222056, 43008), (2745, 234608, 43008, 268016, 56000),
    (2764, 268448, 56000, 268448, 56000)]

/-- The length of a list all of whose entries pass `q` (`none` otherwise), one walk. -/
def allCnt (q : ℕ × ℕ → Bool) : List (ℕ × ℕ) → Option ℕ
  | [] => some 0
  | m :: l => if q m then (allCnt q l).map (· + 1) else none

theorem allCnt_spec (q : ℕ × ℕ → Bool) : ∀ (l : List (ℕ × ℕ)) (n : ℕ), allCnt q l = some n →
    l.all q = true ∧ l.length = n
  | [], n, h => by simp only [allCnt, Option.some.injEq] at h; subst h; simp
  | m :: l, n, h => by
    unfold allCnt at h
    split at h
    · rename_i hm
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h1, h2⟩ := allCnt_spec q l k hk
      simp [hm, h1, h2]
    · simp at h

/-- **S2GB's replay facts** (`ReplayOK`'s at the scheme's offsets on π', plus the static stretches of π'). -/
structure ReplayOKB (st : XStage) : Prop where
  rs : RSItemsF (midItemsS st) = true
  fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1B st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7)
  oA1 : (offA1B st) = capOffS st 1
  fA2 : fsPreK2L ((readWidthsS st).drop (nr1 st)) kA2B (offA1B st) (pendA1B st) =
    ((fsMsgsS st).drop (nMidS st + 8)).take 35
  oA2 : (offA2B st) = (pendA2B st)
  fB1 : fsPreK2L ((readWidthsS st).drop (nr2 st)) (itemK2 P20 shMain mainHeadB1) (q0EndB st) (q0EndB st) =
    shM 25760 (((fsMsgsS st).drop (nMidS st + 43)).take 4)
  oB1 : (offB1B st) = capOffS st 2 + 25760
  fA3 : fsPreK2L ((readWidthsS st).drop (nr3 st)) kA3B (offB1B st) (pendB1B st) =
    shM 25760 (((fsMsgsS st).drop (nMidS st + 47)).take 26)
  oA3 : (offA3B st) = (pendA3B st)
  fB2 : fsPreK2L ((readWidthsS st).drop (nr4 st)) (itemK2 P20 shMain mainHeadB2) (q1EndB st) (q1EndB st) =
    shM 43008 (((fsMsgsS st).drop (nMidS st + 73)).take 4)
  oB2 : (offB2B st) = resOffS st + 43008
  r24 : ((readWidthsS st).drop (nr5 st)).take (2 ^ 9) = List.replicate (2 ^ 9) eBytes
  fp0 : foldPosS st 0 0 = nMidS st + 3
  fp1 : foldPosS st 1 0 = nMidS st + 44
  fp2 : foldPosS st 2 0 = nMidS st + 74
  nc : nChainS st = nMidS st + 78
  nm : nMidS st = 972
  /-- The chain's messages (`ProgOK`'s `nCh_le`, `msgs`, `qcap` at `|π| = 269,336`). -/
  fl : nChainS st ≤ (fsMsgsS st).length
  fm : ((fsMsgsS st).take (nChainS st)).all (msgOkP 269336) = true
  fq : (fsMsgsS st).all (fun m => 32 + m.2 ≤ queryCap) = true
  a0 : st.hb % 8 = 0
  a1 : capOffS st 1 % 8 = 0
  a2 : capOffS st 2 % 8 = 0
  ar : resOffS st % 8 = 0
  hl : (if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb
  oc : st.occ0 ≤ 64
  hb : st.hb = 888
  e0 : (offA2B st) = 88032
  e1 : (q0EndB st) = 170832 + 25760
  e2 : (offA3B st) = 171200 + 25760
  e3 : (q1EndB st) = 222944 + 43008
  c1 : capOffS st 1 + 32 ≤ 88032
  c2l : 170832 ≤ capOffS st 2
  c2 : capOffS st 2 + 32 ≤ 171200
  rl : 222944 ≤ resOffS st
  sr : resOffS st + 24 * 2 ^ 9 ≤ 235496
  /-- The schedule's openings (index, static and expanded sums before and after) and totals, one walk. -/
  osc : openScan st.p (schedule st.p) 0 0 0 = oscB
  hh : headerBytesP st.p = 888

/-! ## The run-length checker -/

/-- The schedule's facts (`ReplayOKB`'s `osc`, `hh`). -/
def schedOkB (p : Params) (sch : List Item) : Bool := openScan p sch 0 0 0 == oscB && headerBytesP p == 888

/-- The segments after `A1` at S2GB (`replayOkG`'s twin on π'). -/
def replayOkGB (st : XStage) (ws0 : List ℕ) (oA pA : ℕ) (R : List (ℕ × ℕ)) : Bool :=
  let w2 := ws0.drop (readsK2 (itemK2 P20 shMain mainHeadA2))
  let w3 := w2.drop (readsK2 (itemK2 P20 shMain mainHeadB1))
  let w4 := w3.drop (readsK2 (itemK2 P20 shMain mainHeadA3))
  let w5 := w4.drop (readsK2 (itemK2 P20 shMain mainHeadB2))
  let oA2 := offK2L ws0 kA2B oA
  let q0 := oA2 + 115 * (8 * st.occ0 + 32 * 18)
  let oB1 := offK2L w2 (itemK2 P20 shMain mainHeadB1) q0
  let pB1 := pendK2L w2 (itemK2 P20 shMain mainHeadB1) q0 q0
  let oA3 := offK2L w3 kA3B oB1
  let q1 := oA3 + 77 * (8 * 48 + 32 * 16)
  oA == capR st R 0 && (
  fsPreK2L ws0 kA2B oA pA == (R.drop 7).take 35 && (
  oA2 == pendK2L ws0 kA2B oA pA && (
  fsPreK2L w2 (itemK2 P20 shMain mainHeadB1) q0 q0 == shM 25760 ((R.drop 42).take 4) && (
  oB1 == capR st R 1 + 25760 && (
  fsPreK2L w3 kA3B oB1 pB1 == shM 25760 ((R.drop 46).take 26) && (
  oA3 == pendK2L w3 kA3B oB1 pB1 && (
  fsPreK2L w4 (itemK2 P20 shMain mainHeadB2) q1 q1 == shM 43008 ((R.drop 72).take 4) && (
  offK2L w4 (itemK2 P20 shMain mainHeadB2) q1 == capR st R 2 + 43008 && (
  w5.take (2 ^ 9) == List.replicate (2 ^ 9) eBytes && (
  lvOffS st 0 == 0 && (lvOffS st 1 == 41 && (lvOffS st 2 == 71 && (
  lvOffS st 2 + ((mainLS st 2).fold - 1) == 74 && (
  st.hb % 8 == 0 && (capR st R 0 % 8 == 0 && (capR st R 1 % 8 == 0 && (capR st R 2 % 8 == 0 && (
  decide ((if st.p.leafOut then hdrFixS else hdrFix) ≤ st.hb) && (decide (st.occ0 ≤ 64) && (
  st.hb == 888 && (oA2 == 88032 && (q0 == 170832 + 25760 && (oA3 == 171200 + 25760 && (q1 == 222944 + 43008 && (
  decide (capR st R 0 + 32 ≤ 88032) && (decide (170832 ≤ capR st R 1) && (decide (capR st R 1 + 32 ≤ 171200) && (
  decide (222944 ≤ capR st R 2) && decide (capR st R 2 + 24 * 2 ^ 9 ≤ 235496)))))))))))))))))))))))))))))

/-- **The run-length checker at S2GB** (`replayOkR`'s twin: the root cap ends at `o1B`) with the schedule's stretches. -/
def replayOkRB (st : XStage) (pre rest : List Item) : Bool :=
  let e := endF st.p (pre.drop 1) (st.hb + 64) st.hb
  let ws := rest.flatMap wsI
  let R := Lvm.X.fsPre st.p rest e.1 e.2
  let kA := itemK2 P20 shMain mainHeadA1
  !pre.isEmpty && (
  ((pre.take 1).flatMap wsI).isEmpty && (
  (Lvm.X.fsPre st.p (pre.take 1) st.hb st.hb).isEmpty && (
  endF st.p (pre.take 1) st.hb st.hb == (st.hb + 64, st.hb) && (
  RSItemsF (pre.drop 1) && (
  allCnt (msgOkP 269336) (Lvm.X.fsPre st.p (pre.drop 1) (st.hb + 64) st.hb) == some 972 && (
  msgOkP 269336 (8, st.hb - 8) && (decide (32 + (st.hb - 8) ≤ queryCap) && (
  (R.take 77).all (msgOkP 269336) && ((R.all fun m => decide (32 + m.2 ≤ queryCap)) && (decide (77 ≤ R.length) && (
  fsPreK2L ws kA e.1 e.2 == R.take 7 && (
  schedOkB st.p (pre ++ rest) &&
  replayOkGB st (ws.drop (readsK2 kA)) (offK2L ws kA e.1) (pendK2L ws kA e.1 e.2) R))))))))))))

theorem replayOKB_ofG {st : XStage} (F R : List (ℕ × ℕ)) (rs : RSItemsF (midItemsS st) = true)
    (fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1B st) st.hb = ((fsMsgsS st).drop 1).take (nMidS st + 7))
    (hmsg : fsMsgsS st = (8, st.hb - 8) :: (F ++ R)) (hnM : nMidS st = F.length)
    (hnP : nPreS st = F.length) (hm : nMidS st = 972) (hF : F.all (msgOkP 269336) = true)
    (hs1 : msgOkP 269336 (8, st.hb - 8) = true) (hs2 : 32 + (st.hb - 8) ≤ queryCap)
    (hR1 : (R.take 77).all (msgOkP 269336) = true) (hR2 : (R.all fun m => decide (32 + m.2 ≤ queryCap)) = true)
    (hR3 : 77 ≤ R.length) (hS : schedOkB st.p (schedule st.p) = true)
    (h : replayOkGB st ((readWidthsS st).drop (nr1 st)) (offA1B st) (pendA1B st) R = true) : ReplayOKB st := by
  have hfp : ∀ i j, foldPosS st i j = F.length + 1 + (2 + lvOffS st i + j) := fun i j => by
    rw [show foldPosS st i j = nPreS st + 3 + lvOffS st i + j from rfl, hnP]; omega
  have hc : ∀ i, (fsMsgsS st).getD (foldPosS st i ((mainLS st i).fold - 1)) (0, 0) =
      R.getD (2 + lvOffS st i + ((mainLS st i).fold - 1)) (0, 0) := fun i => by
    rw [hfp, hmsg, getD_msgs]
  have hc1 : capOffS st 1 = capR st R 0 := congrArg (·.1 + 2 * eBytes) (hc 0)
  have hc2 : capOffS st 2 = capR st R 1 := congrArg (·.1 + 2 * eBytes) (hc 1)
  have hcr : resOffS st = capR st R 2 := by
    rw [resOffS, nChainS, Nat.add_sub_cancel]; exact congrArg (·.1 + 2 * eBytes) (hc 2)
  have hd : ∀ k n, n = nMidS st + 1 + k → (fsMsgsS st).drop n = R.drop k := fun k n hn => by
    rw [hn, hmsg, hnM, drop_msgs]
  simp only [replayOkGB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.drop_drop] at h
  obtain ⟨oA1, fA2, oA2, fB1, oB1, fA3, oA3, fB2, oB2, r24, l0, l1, l2, l3, a0, a1, a2, ar, hl, oc,
    hb, e0, e1, e2, e3, c1, c2l, c2, rl, sr⟩ := h
  simp only [schedOkB, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨osc, hh⟩ := hS
  refine ⟨rs, fA1, by rw [hc1]; exact oA1, by rw [hd 7 _ (by omega)]; exact fA2, oA2,
    by rw [hd 42 _ (by omega)]; exact fB1, by rw [hc2]; exact oB1, by rw [hd 46 _ (by omega)]; exact fA3, ?_,
    by rw [hd 72 _ (by omega)]; exact fB2, by rw [hcr]; exact oB2, by unfold nr5 nr4 nr3 nr2; exact r24, ?_, ?_, ?_, ?_, hm, ?_, ?_, ?_, a0, by rw [hc1]; exact a1,
    by rw [hc2]; exact a2, by rw [hcr]; exact ar, hl, oc, hb, e0, by unfold q0EndB offA2B; exact e1,
    by unfold offA3B offB1B q0EndB offA2B nr3 nr2; exact e2,
    by unfold q1EndB offA3B offB1B q0EndB offA2B nr3 nr2; exact e3, by rw [hc1]; exact c1,
    by rw [hc2]; exact c2l, by rw [hc2]; exact c2, by rw [hcr]; exact rl, by rw [hcr]; exact sr,
    osc, hh⟩
  · unfold offA3B pendA3B offB1B pendB1B q0EndB offA2B nr3 nr2; exact oA3
  · have := hfp 0 0; omega
  · have := hfp 1 0; omega
  · have := hfp 2 0; omega
  · have := hfp 2 ((mainLS st 2).fold - 1); rw [nChainS]; omega
  · have := hfp 2 ((mainLS st 2).fold - 1)
    rw [hmsg, nChainS]
    simp only [List.length_cons, List.length_append]
    omega
  · have hn : nChainS st = F.length + 1 + 77 := by
      have := hfp 2 ((mainLS st 2).fold - 1); rw [nChainS]; omega
    have hFt : F.take (F.length + 77) = F := List.take_of_length_le (by omega)
    rw [hmsg, hn, List.take_succ_cons, List.take_append, hFt, Nat.add_sub_cancel_left]
    simp only [List.all_cons, List.all_append, hs1, hF, hR1, Bool.and_self]
  · have hFq : (F.all fun m => decide (32 + m.2 ≤ queryCap)) = true :=
      List.all_eq_true.2 fun m hm => by
        have := List.all_eq_true.1 hF m hm
        simp only [msgOkP, Bool.and_eq_true, decide_eq_true_eq] at this
        exact decide_eq_true this.2
    rw [hmsg]
    simp only [List.all_cons, List.all_append, hFq, hR2, decide_eq_true hs2, Bool.and_self]

/-- **The run-length checker gives S2GB's replay facts** (at a split of `st`'s items with `pre` of length
`st.nOpen`). -/
theorem replayOKB_ofR {st : XStage} {pre rest : List Item} (hs : st.items = pre ++ rest)
    (hn : st.nOpen = pre.length) (h : replayOkRB st pre rest = true) : ReplayOKB st := by
  simp only [replayOkRB, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨-, hw1, hf1, he1, rs, hsm, hs1, hs2, hR1, hR2, hR3, fA, hS, hG⟩ := h
  rw [← hs] at hS
  rw [show st.hb + 64 = (o1B st) from rfl] at fA hG hsm hR1 hR2 hR3
  have hmid : midItemsS st = pre.drop 1 := by rw [midItemsS, hs, hn, List.take_append_length]
  have hpre : pre = pre.take 1 ++ pre.drop 1 := (List.take_append_drop 1 pre).symm
  rw [← hmid] at rs fA hG hsm hR1 hR2 hR3
  obtain ⟨hF, hFl⟩ := allCnt_spec _ _ _ hsm
  rw [← hmid] at hpre
  have hW : readWidthsS st = (midItemsS st).flatMap wsI ++ rest.flatMap wsI := by
    rw [readWidthsS_eq, hs, hpre, List.flatMap_append, List.flatMap_append, hw1, List.nil_append]
  obtain ⟨ho, hp, hf, hr⟩ := K2L_items st.p shMain (midItemsS st) (rest.flatMap wsI)
    (itemK2 P20 shMain mainHeadA1) (o1B st) st.hb rs
  have hoA : (offA1B st) = offK2L (rest.flatMap wsI) (itemK2 P20 shMain mainHeadA1)
      (endF st.p (midItemsS st) (o1B st) st.hb).1 := by
    rw [offA1B, hW]; exact ho
  have hpA : (pendA1B st) = pendK2L (rest.flatMap wsI) (itemK2 P20 shMain mainHeadA1)
      (endF st.p (midItemsS st) (o1B st) st.hb).1 (endF st.p (midItemsS st) (o1B st) st.hb).2 := by
    rw [pendA1B, hW]; exact hp
  have hnr : (readWidthsS st).drop (nr1 st) =
      (rest.flatMap wsI).drop (readsK2 (itemK2 P20 shMain mainHeadA1)) := by
    rw [show nr1 st = readsK2 (itemK2F st.p shMain (midItemsS st) ++ itemK2 P20 shMain mainHeadA1) from rfl,
      hr, hW, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left]
  have hpreF : Lvm.X.fsPre st.p pre st.hb st.hb = Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb := by
    rw [hpre, fsPre_append, hf1, he1, List.nil_append] <;> rfl
  have hfs : Lvm.X.fsPre st.p st.items st.hb st.hb = Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb ++
      Lvm.X.fsPre st.p rest (endF st.p (midItemsS st) (o1B st) st.hb).1
        (endF st.p (midItemsS st) (o1B st) st.hb).2 := by
    have hend : endF st.p pre st.hb st.hb = endF st.p (midItemsS st) (o1B st) st.hb := by
      rw [hpre, endF_append, he1] <;> rfl
    rw [hs, fsPre_append, hpreF, hend]
  have hlen : (Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb).length = sampR (midItemsS st) :=
    fsPre_length_rs _ _ _ _ rs
  have hnM : nMidS st = (Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb).length := by
    rw [hlen]; exact count_sample_rs _ rs
  have hmsg : fsMsgsS st = (8, st.hb - 8) :: (Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb ++
      Lvm.X.fsPre st.p rest (endF st.p (midItemsS st) (o1B st) st.hb).1
        (endF st.p (midItemsS st) (o1B st) st.hb).2) := by
    rw [fsMsgsS, hfs]
  have hnP : nPreS st = (Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb).length := by
    rw [nPreS, hs, hn, List.take_append_length, hpreF]
  have hle : (Lvm.X.fsPre st.p (midItemsS st) (o1B st) st.hb).length ≤ nMidS st + 7 := by
    rw [hnM]; exact Nat.le_add_right _ _
  have fA1 : fsPreK2L (readWidthsS st) (kA1S st) (o1B st) st.hb =
      ((fsMsgsS st).drop 1).take (nMidS st + 7) := by
    rw [hW]
    refine hf.trans ?_
    rw [hmsg, List.drop_one, List.tail_cons, fA, List.take_append, List.take_of_length_le hle, hnM,
      Nat.add_sub_cancel_left]
  refine replayOKB_ofG _ _ rs fA1 hmsg hnM hnP (by rw [hnM]; exact hFl) hF hs1 (of_decide_eq_true hs2) hR1 hR2 (of_decide_eq_true hR3) hS ?_
  rw [hnr, hoA, hpA]
  exact hG

set_option maxRecDepth 200000 in
/-- **S2GB's replay facts**, one kernel evaluation (the split after the fourth phase, over the `appL` literals of
`schLA`). -/
theorem replayOKB_stB20 : ReplayOKB stB20 :=
  replayOKB_ofR (pre := E2Q.appL ph20U_commit (E2Q.appL ph20B_bus (E2Q.appL ph20U_tape ph20U_wire)))
    (rest := ph20U_openMain)
    (by show schedule P20B = _; rw [schedule_P20B_litA, schLA]; simp only [E2Q.appL_eq, List.append_assoc])
    (by
      have h4 : phasesB20.take 4 = [(.commit, ph20U_commit), (.bus, ph20B_bus), (.tape, ph20U_tape),
          (.wire, ph20U_wire)] := rfl
      show (((phases P20B).take 4).flatMap (·.2)).length = _
      rw [phases_P20B_lit, h4]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, E2Q.appL_eq, List.append_assoc])
    (by decide +kernel)

/-! ## The schedule's static stretches -/

theorem openScan_ne (p : Params) : ∀ (l : List Item) (i s e : ℕ), openScan p l i s e ≠ []
  | [], _, _, _ => by simp [openScan]
  | it :: r, i, s, e => by
    unfold openScan
    split
    · simp
    · exact openScan_ne p r _ _ _

/-- **The walk's first entry**: an opening-free prefix of `k` items, then the opening (or the end). -/
theorem openScan_spec (p : Params) : ∀ (l : List Item) (i s e j a b a' b' : ℕ) (rest : List (ℕ × ℕ × ℕ × ℕ × ℕ)),
    openScan p l i s e = (j, a, b, a', b') :: rest →
    ∃ k, j = i + k ∧ ((l.take k).all fun it => !isOpenI it) = true ∧
      a = s + ((l.take k).map (fillStat p)).sum ∧ b = e + ((l.take k).map (fillExp p)).sum ∧
      ((k = l.length ∧ rest = []) ∨ (k < l.length ∧ a' = s + ((l.take (k + 1)).map (fillStat p)).sum ∧
        b' = e + ((l.take (k + 1)).map (fillExp p)).sum ∧ rest = openScan p (l.drop (k + 1)) (j + 1) a' b'))
  | [], i, s, e, j, a, b, a', b', rest, h => by
    simp only [openScan, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, -, -⟩, rfl⟩ := h
    exact ⟨0, rfl, rfl, by simp, by simp, Or.inl ⟨rfl, rfl⟩⟩
  | it :: r, i, s, e, j, a, b, a', b', rest, h => by
    unfold openScan at h
    split at h
    · rename_i ho
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := h
      refine ⟨0, rfl, by simp, by simp, by simp, Or.inr ⟨by simp, by simp, by simp, by simp⟩⟩
    · rename_i ho
      obtain ⟨k, hj, hall, ha, hb, hk⟩ := openScan_spec p r _ _ _ j a b a' b' rest h
      refine ⟨k + 1, by omega, by simp [ho, hall], by simp [ha]; omega, by simp [hb]; omega, ?_⟩
      rcases hk with ⟨hk, hr⟩ | ⟨hk, ha', hb', hr⟩
      · exact Or.inl ⟨by simp [hk], hr⟩
      · refine Or.inr ⟨by simp; omega, by simp [ha']; omega, by simp [hb']; omega, ?_⟩
        rw [hr, show j + 1 = j + 1 from rfl]
        simp

/-- The static sum. -/
abbrev statS (p : Params) (l : List Item) : ℕ := (l.map (fillStat p)).sum
/-- The expanded sum. -/
abbrev expS (p : Params) (l : List Item) : ℕ := (l.map (fillExp p)).sum

theorem sum_take_add (f : Item → ℕ) (l : List Item) (m n : ℕ) :
    ((l.take (m + n)).map f).sum = ((l.take m).map f).sum + (((l.drop m).take n).map f).sum := by
  rw [List.take_add, List.map_append, List.sum_append]

/-- **`P20B`'s static stretches** from the walk. -/
theorem regionsB (p : Params) (h : openScan p (schedule p) 0 0 0 = oscB) :
    ((schedule p).take 2698).all (fun it => !isOpenI it) = true ∧ statS p ((schedule p).take 2698) = 87144 ∧
    statS p ((schedule p).take 2699) = 169944 ∧ expS p ((schedule p).take 2699) = 25760 ∧
    (((schedule p).drop 2699).take 30).all (fun it => !isOpenI it) = true ∧
      statS p (((schedule p).drop 2699).take 30) = 368 ∧
    statS p ((schedule p).take 2730) = 222056 ∧ expS p ((schedule p).take 2730) = 43008 ∧
    (((schedule p).drop 2730).take 15).all (fun it => !isOpenI it) = true ∧
      statS p (((schedule p).drop 2730).take 15) = 12552 ∧
    statS p (schedule p) = 268448 ∧ expS p (schedule p) = 56000 := by
  set l := schedule p
  obtain ⟨k0, hj0, hall0, ha0, -, hk0⟩ := openScan_spec p l 0 0 0 _ _ _ _ _ _ h
  rcases hk0 with ⟨-, h0⟩ | ⟨-, ha0', hb0', hr0⟩
  · exact absurd h0 (by simp)
  obtain rfl : k0 = 2698 := by omega
  obtain ⟨k1, hj1, hall1, ha1, -, hk1⟩ := openScan_spec p _ _ _ _ _ _ _ _ _ _ hr0.symm
  rcases hk1 with ⟨-, h1⟩ | ⟨-, ha1', hb1', hr1⟩
  · exact absurd h1 (by simp)
  obtain rfl : k1 = 30 := by omega
  obtain ⟨k2, hj2, hall2, ha2, -, hk2⟩ := openScan_spec p _ _ _ _ _ _ _ _ _ _ hr1.symm
  rcases hk2 with ⟨-, h2⟩ | ⟨-, ha2', hb2', hr2⟩
  · exact absurd h2 (by simp)
  obtain rfl : k2 = 15 := by omega
  obtain ⟨k3, -, -, ha3, hb3, hk3⟩ := openScan_spec p _ _ _ _ _ _ _ _ _ _ hr2.symm
  rcases hk3 with ⟨hk3, -⟩ | ⟨-, -, -, h3⟩
  swap
  · exact absurd h3.symm (openScan_ne _ _ _ _ _)
  simp only [List.drop_drop, Nat.reduceAdd] at hall1 ha1 ha1' hb1' hall2 ha2 ha2' hb2'
  simp only [List.drop_drop, Nat.reduceAdd, Nat.zero_add] at ha3 hb3 hk3 ha0' hb0'
  rw [hk3, List.take_length] at ha3 hb3
  have t1 := sum_take_add (fillStat p) l 2699 31
  have t1e := sum_take_add (fillExp p) l 2699 31
  have t2 := sum_take_add (fillStat p) l 2730 16
  have t2e := sum_take_add (fillExp p) l 2730 16
  have t3 := List.take_append_drop 2746 l
  have t3s := congrArg (fun l => (l.map (fillStat p)).sum) t3
  have t3e := congrArg (fun l => (l.map (fillExp p)).sum) t3
  simp only [List.map_append, List.sum_append] at t3s t3e
  simp only [Nat.reduceAdd] at t1 t1e t2 t2e
  simp only [statS, expS]
  refine ⟨hall0, by omega, by omega, by omega, hall1, by omega, by omega, by omega, hall2, by omega, by omega, by omega⟩

/-- **π' copies π's static stretch** `[hb + a, hb + a + y)` of items `k … k + n − 1` (opening-free) shifted by the
upper siblings `s` of the items before. -/
theorem copyB (p : Params) (π : ByteArray) (w : List UInt8) (k n : ℕ) {a s y : ℕ}
    (hy : (((schedule p).drop k).take n).all (fun it => !isOpenI it) = true)
    (hS : statS p ((schedule p).take k) = a) (hE : expS p ((schedule p).take k) = s)
    (hY : statS p (((schedule p).drop k).take n) = y)
    (hπ : headerBytesP p + a + y ≤ π.size) (hw : s ≤ w.length) {o m : ℕ} (ho : headerBytesP p + a ≤ o)
    (hm : o + m ≤ headerBytesP p + a + y) :
    sl (fillB p π w).data.toList (o + s) m = sl π.data.toList o m := by
  obtain ⟨j, rfl⟩ : ∃ j, o = headerBytesP p + a + j := ⟨o - (headerBytesP p + a), by omega⟩
  simp only [statS, expS] at hS hE hY
  have e := fillB_sl p π w ((schedule p).take k) (((schedule p).drop k).take n) (((schedule p).drop k).drop n)
    (by rw [List.append_assoc, List.take_append_drop, List.take_append_drop]) hy
    (by rw [hS, hY]; exact hπ) (by rw [hE]; exact hw) (j := j) (n := m) (by rw [hY]; omega)
  rw [hS, hE] at e
  unfold sl
  rw [show headerBytesP p + a + j + s = headerBytesP p + a + s + j by omega]
  exact e

/-! ## The kinds' walk stays in its segment -/

theorem K2L_mono : ∀ (ks : List K2) (ws : List ℕ) (off pend : ℕ), pend ≤ off →
    pend ≤ pendK2L ws ks off pend ∧ pendK2L ws ks off pend ≤ offK2L ws ks off ∧ off ≤ offK2L ws ks off ∧
    ∀ m ∈ fsPreK2L ws ks off pend, pend ≤ m.1 ∧ m.1 + m.2 ≤ offK2L ws ks off
  | [], _, _, _, h => by simp [pendK2L, offK2L, fsPreK2L, h]
  | .read :: ks, ws, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_mono ks ws.tail (off + ws.headD eBytes) pend (by omega)
    simp only [pendK2L, offK2L, fsPreK2L]
    exact ⟨a, b, by omega, d⟩
  | .sample :: ks, ws, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_mono ks ws off off le_rfl
    simp only [pendK2L, offK2L, fsPreK2L, List.mem_cons, forall_eq_or_imp]
    refine ⟨by omega, b, c, ⟨le_rfl, by omega⟩, fun m hm => ?_⟩
    have := d m hm
    omega
  | .commit _ _ nb :: ks, ws, off, pend, h => by
    obtain ⟨a, b, c, d⟩ := K2L_mono ks ws (off + nb) pend (by omega)
    simp only [pendK2L, offK2L, fsPreK2L]
    exact ⟨a, b, by omega, d⟩

/-! ## The chain over π' -/

/-- **`chainTS` over π'**: the scheme absorbs π's messages shifted by `s`, whose bytes π' copies. -/
theorem chainTB (st : XStage) (π : RecursionFast.Proof) (B : List UInt8) {rw : ℕ → ℕ} {ks : List K2}
    {n off pend D N s : ℕ} (hPre : fsPreK2W rw ks n off pend = shM s (((fsMsgsS st).drop D).take N))
    (hcp : ∀ m ∈ ((fsMsgsS st).drop D).take N, sl B (m.1 + s) m.2 = sl π.data.toList m.1 m.2) :
    ∀ i (hi : i < (fsPreK2W rw ks n off pend).length) (a : RecursionFast.Digest),
      fsQLS st π (D + 1 + i) a =
        toQ (a.toList ++ sl B ((fsPreK2W rw ks n off pend)[i]).1 ((fsPreK2W rw ks n off pend)[i]).2) := by
  intro i hi a
  have hi' : i < (((fsMsgsS st).drop D).take N).length := by
    have := hi
    rw [hPre, shM, List.length_map] at this
    exact this
  have he := List.getElem_of_eq hPre hi
  rw [he]
  simp only [shM, List.getElem_map]
  rw [hcp _ (List.getElem_mem hi'), fsQLS_eq st π (by omega), msgLS]
  have hg : (fsMsgsS st).getD (D + 1 + i - 1) (0, 0) = (((fsMsgsS st).drop D).take N)[i] := by
    rw [show D + 1 + i - 1 = D + i by omega, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem _ _ (by have := hi'; simp only [List.length_take, List.length_drop] at this; omega)]
  rw [hg]

/-! ## Digests at an offset -/

theorem digestsOf_off (π : RecursionFast.Proof) (o n : ℕ) (h8 : o % 8 = 0) (hs : o + 32 * n ≤ π.size) :
    digestsOf ((π.data.toList.drop o).take (32 * n)) n = (List.range n).map fun e => hdD π (o / 8 + 4 * e) := by
  have hB : π.data.toList.length = π.size := Array.length_toList
  unfold digestsOf
  refine List.map_congr_left fun e he => ?_
  have he' : e < n := List.mem_range.1 he
  rw [Lvm.X.hdD_eq_digestAt, show 8 * (o / 8 + 4 * e) = o + 32 * e by omega]
  apply Vector.ext
  intro j hj
  simp only [dg, digestAt, Vector.getElem_ofFn]
  rw [get!_eq_getD, List.getD_eq_getElem _ _ (by simp only [List.length_drop, List.length_take]; omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_drop, List.getElem_take]
  congr 1
  omega

/-! ## The format -/

/-- **S2GB's format agrees with a stage** (`FmtOK` with the expanded size `325,336`). -/
def FmtOKB (st : XStage) (f : SFmt) : Prop :=
  (∀ n, f.rw n = (readWidthsS st).getD n eBytes) ∧ f.pz = 325336 ∧ f.hb = st.hb ∧ f.occ 19 64 = st.occ0 ∧
    f.occ 16 48 = 48 ∧ f.occ 13 48 = 48

/-- `stB20`'s read widths are `readWidthsP P20B`. -/
theorem readWidthsS_stB20 : readWidthsS stB20 = readWidthsP P20B := by
  unfold readWidthsS readWidthsP
  exact List.flatMap_congr fun it _ => by cases it <;> rfl

theorem fmtOKB_stB20 : FmtOKB stB20 Lvm.CT.fmtB20 :=
  ⟨fun n => by show rwB20 n = _; rw [rwB20, readWidthsS_stB20], pzB_P20B, rfl, rfl, rfl, rfl⟩

/-! ## The extractor program's static facts -/

/-- **`progFacts_stB20`'s facts from the replay record** (the chain's messages checked in `replayOkRB`'s walk). -/
theorem progFactsG (st : XStage) (hr : ReplayOKB st) : st.occ0 ≤ 64 ∧ 269336 < 2 ^ 32 ∧ nChainS st < 2 ^ 11 ∧
    nChainS st ≤ (fsMsgsS st).length ∧
    ((fsMsgsS st).take (nChainS st)).all (msgOkP 269336) = true ∧
    (fsMsgsS st).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    (∀ k < 14, foldPosKS st k < nChainS st) ∧
    capOffS st 0 / 8 + 4 * 2 ^ 8 ≤ 269336 / 8 ∧ capOffS st 1 / 8 + 4 * 2 ^ 7 ≤ 269336 / 8 ∧
    capOffS st 2 / 8 + 4 * 2 ^ 7 ≤ 269336 / 8 ∧ resOffS st / 8 + 3 * 2 ^ 9 ≤ 269336 / 8 ∧
    capWS st 0 + 4 * 2 ^ 8 < 2 ^ 62 ∧ capWS st 1 + 4 * 2 ^ 7 < 2 ^ 62 ∧ capWS st 2 + 4 * 2 ^ 7 < 2 ^ 62 ∧
    resWS st + 3 * 2 ^ 9 < 2 ^ 63 ∧ posL 269336 ≤ 2 ^ 60 ∧ 15 ≤ 269336 / 8 := by
  have h0 : capOffS st 0 = st.hb := rfl
  have hb := hr.hb
  have c1 := hr.c1
  have c2 := hr.c2
  have sr := hr.sr
  have nc := hr.nc
  have nm := hr.nm
  have hfold : ∀ k < 14, foldPosKS st k < nChainS st := fun k hk => by
    unfold foldPosKS
    split_ifs with h6 h10
    · rw [foldPosS_add, hr.fp0]; omega
    · rw [foldPosS_add, hr.fp1]; omega
    · rw [foldPosS_add, hr.fp2]; omega
  refine ⟨hr.oc, by norm_num, by omega, hr.fl, hr.fm, hr.fq, hfold, by omega, by omega, by omega, by omega, ?_, ?_, ?_,
    ?_, by unfold posL; norm_num, by norm_num⟩ <;> simp only [capWS, resWS] <;> omega

end Lvm.ASM
