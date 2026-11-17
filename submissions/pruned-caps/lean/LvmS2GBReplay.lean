-- New for lvm2 MP-B cap pruning (CAP-C8, 2026-11-17): the replay of S2GB's driver (proof help for `nodeB20`'s left
-- child): `driveB` on `reassembleB` asks exactly the trace (`drive_replayP`'s twin, `LvmReplay`, with the π tail's
-- cursor and the heap entries), and the π tail's bound `tailMax`.
import LvmS2GBDrive
import LvmS2GBTail
import LvmReplay
import LvmQLinkSound

/-!
# Replay of the S2GB driver

`InvB` is `Inv` (`LvmReplay`) with the body followed by the π tail (`… ++ tailB p tr`) and the tail cursor `t`
(`(bl π).drop t = tailFrom …`: the tail bytes of the entries from the walk's next entry on). Per opening
(`openLoopB_run`): the paths (`pathsB_run`, the climbs as S2GS's without the inline cap check), the layer
(`layer_fold`: a covered node is the first covering path's top, an uncovered one the next 32 tail bytes; either is
the half of its heap-bottom slot's query), the covered check, the heap (`heapB_run`: each query is its two children,
layer halves or earlier heap answers), and the sent-cap check (the heap answers of slots `2^c …` are the sent cap's
bytes, `Good`'s cap condition and `CapsRel`). The tail cursor moves by at most `2^cap − 1` nodes per opening (path 0
covers one layer node), so the π tail fits `tailMax`.
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## The π tail from an entry on -/

/-- The tail bytes of the entries `i, i + 1, …` of the plan `P`. -/
def tailFrom (tr : Trace) (P : List PE) (i : Nat) : List UInt8 :=
  (List.range' i (P.length - i)).flatMap fun k => tailEntB tr k (P.getD k default)

theorem tailFrom_cons (tr : Trace) (P : List PE) {i : Nat} (hi : i < P.length) :
    tailFrom tr P i = tailEntB tr i (P.getD i default) ++ tailFrom tr P (i + 1) := by
  unfold tailFrom
  rw [show P.length - i = (P.length - (i + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem tailFrom_end (tr : Trace) (P : List PE) {i : Nat} (hi : P.length ≤ i) : tailFrom tr P i = [] := by
  simp [tailFrom, show P.length - i = 0 by omega]

theorem tailB_eq (p : Params) (tr : Trace) : tailB p tr = tailFrom tr (plan p) 0 := by
  simp only [tailB, tailFrom, Nat.sub_zero, List.range_eq_range']

/-- Entries that carry nothing are skipped. -/
theorem fm_skip (g : Nat → List UInt8) (L : Nat) : ∀ (n i : Nat), i + n ≤ L → (∀ x < n, g (i + x) = []) →
    (List.range' i (L - i)).flatMap g = (List.range' (i + n) (L - (i + n))).flatMap g
  | 0, i, _, _ => rfl
  | n + 1, i, hl, h => by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [show L - i = (L - (i + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons, h0, List.nil_append,
      fm_skip g L n (i + 1) (by omega) (fun x hx => by
        have := h (x + 1) (by omega); rwa [show i + (x + 1) = i + 1 + x by omega] at this),
      show i + 1 + n = i + (n + 1) by omega]

theorem bodyFrom_skip (tr : Trace) (P : List PE) (n i : Nat) (hl : i + n ≤ P.length)
    (h : ∀ x < n, contrib tr (i + x) (P.getD (i + x) default) = []) : bodyFrom tr P i = bodyFrom tr P (i + n) :=
  fm_skip _ _ n i hl h

theorem tailFrom_skip (tr : Trace) (P : List PE) (n i : Nat) (hl : i + n ≤ P.length)
    (h : ∀ x < n, tailEntB tr (i + x) (P.getD (i + x) default) = []) : tailFrom tr P i = tailFrom tr P (i + n) :=
  fm_skip _ _ n i hl h

/-! ## The invariant -/

/-- **The driver's state matches the walk's at S2GB**: `Inv` with the body followed by the π tail, and the tail
cursor `t` at the tail bytes of the entries from `w.i` on. -/
structure InvB (p : Params) (tr : Trace) (π : ByteArray) (s : DSt) (w : WS) (t : Nat) : Prop where
  log : s.log = (tr.take w.i).reverse
  st : s.st = aOf tr w.st
  off : s.off = s.pend + w.pend
  body : (bl π).drop s.pend = bodyFrom tr (plan p) w.i ++ tailB p tr
  le : s.pend ≤ π.size
  caps : CapsRel tr π s.pend w.pend w.pcaps s.caps w.caps
  tail : (bl π).drop t = tailFrom tr (plan p) w.i
  tle : t ≤ π.size

/-! ## FS queries and positions (`fs_step`, `posLoop_run` with the tail) -/

theorem fs_stepB {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w : WS} {t : Nat} (hI : InvB p tr π s w t)
    (hi : w.i < tr.length) (hn : tr.length = (plan p).length)
    (hP : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩) (hG : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩)
    (k : DSt → Digest → OProg Bool) :
    (fsQuery π s k).runSeq (tr.drop w.i) = (k (dStep tr w.i s) (aOf tr w.i)).runSeq (tr.drop (w.i + 1)) ∧
      InvB p tr π (dStep tr w.i s) w.stepFS t := by
  obtain ⟨hlen, hpre⟩ := hG
  simp only at hlen hpre
  have hbody : (bl π).drop s.pend =
      (bl (qOf tr w.i)).drop 32 ++ (bodyFrom tr (plan p) (w.i + 1) ++ tailB p tr) := by
    rw [hI.body, bodyFrom_cons _ _ (by omega), hP, List.append_assoc]; rfl
  have hcl : ((bl (qOf tr w.i)).drop 32).length = w.pend := by
    rw [List.length_drop, ← size_bl, hlen]; omega
  have hq : digestBytes s.st ++ π.extract s.pend s.off = qOf tr w.i := by
    apply ba_ext
    rw [bl_append, bl_digestBytes, hI.st, hI.off, bl_extract_body hbody hcl, ← hpre, List.take_append_drop]
  refine ⟨?_, ⟨?_, rfl, by simp [dStep, WS.stepFS], ?_, ?_, ?_, ?_, hI.tle⟩⟩
  · rw [fsQuery, drop_cons_getD tr hi, ask_run _ _ _ (qOf tr w.i, aOf tr w.i) _ hq.symm, hq]; rfl
  · simp only [dStep, WS.stepFS, WS.settle]; rw [take_succ_rev tr hi, hI.log]
  · simp only [dStep, WS.stepFS, WS.settle]
    rw [hI.off, ← hcl]; exact drop_body hbody
  · simp only [dStep]; rw [hI.off, ← hcl]; exact le_of_body hbody hI.le
  · simp only [dStep, WS.stepFS, WS.settle]
    refine capsRel_settle (fun y hy => ?_) _ _ _ _ hI.caps
    rw [get!_body hbody (by omega), get!_bl, getD_drop']
  · simp only [WS.stepFS, WS.settle]
    rw [hI.tail, tailFrom_cons _ _ (by omega), hP]; rfl

theorem posLoop_runB {p : Params} {tr : Trace} {π : ByteArray} {t : Nat} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (h : Nat) (k : DSt → OProg Bool) :
    ∀ (n rem : Nat) (s : DSt) (w : WS), InvB p tr π s w t → w.i + n ≤ tr.length →
    (∀ x < n, (plan p).getD (w.i + x) default =
      ⟨.fs (if x = 0 then w.st else w.i + x - 1), if x = 0 then 32 + w.pend else 32⟩) →
    ∃ s', InvB p tr π s' (WS.stepFS^[n] w) t ∧ s'.pos = s.pos ++ posOut tr h w.i n rem ∧
      (posLoop π h n rem s k).runSeq (tr.drop w.i) = (k s').runSeq (tr.drop (w.i + n))
  | 0, rem, s, w, hI, _, _ => ⟨s, hI, by simp [posOut], by simp [posLoop]⟩
  | n + 1, rem, s, w, hI, hl, hP => by
    have hP0 := hP 0 (by omega)
    simp only [ite_true, Nat.add_zero] at hP0
    have hG0 : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by rw [← hP0]; exact hG _ (by omega)
    have hI' := (fs_stepB (k := fun _ _ => OProg.ret false) hI (by omega) hn hP0 hG0).2
    have hI2 : InvB p tr π { (dStep tr w.i s) with
        pos := (dStep tr w.i s).pos ++ posBatch tr h w.i (min positionsPerAnswer rem) } w.stepFS t :=
      ⟨hI'.log, hI'.st, hI'.off, hI'.body, hI'.le, hI'.caps, hI'.tail, hI'.tle⟩
    obtain ⟨s', hI3, hpos3, hrun3⟩ := posLoop_runB hn hG h k n (rem - min positionsPerAnswer rem) _ _ hI2
      (by simp [WS.stepFS, WS.settle]; omega) (fun x hx => by
        have := hP (x + 1) (by omega)
        rw [show w.i + (x + 1) = w.stepFS.i + x by simp [WS.stepFS, WS.settle]; omega] at this
        rw [this]
        rcases x with _ | x <;> simp [WS.stepFS, WS.settle] <;> omega)
    refine ⟨s', by rw [Function.iterate_succ_apply]; exact hI3, ?_, ?_⟩
    · rw [hpos3]; simp [dStep, posOut, posBatch, List.append_assoc, WS.stepFS, WS.settle]
    · rw [posLoop, (fs_stepB hI (by omega) hn hP0 hG0 _).1]
      rw [show w.i + (n + 1) = w.stepFS.i + n by simp [WS.stepFS, WS.settle]; omega, ← hrun3]
      rfl

/-! ## Merkle paths (`climb_run` with the tail after the body) -/

theorem climb_runB {p : Params} {tr : Trace} {π : ByteArray} (R : List UInt8) (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (pe h j : Nat) (k : DSt → Digest → OProg Bool) :
    ∀ (m lvl : Nat) (cur : Digest) (s : DSt) (i : Nat),
    s.log = (tr.take i).reverse → (bl π).drop s.off = bodyFrom tr (plan p) i ++ R → s.off ≤ π.size →
    cur = aOf tr (i - 1) → i + m ≤ tr.length →
    (∀ x < m, ∃ cap, (plan p).getD (i + x) default = ⟨.node pe h j (lvl + x) cap, 64⟩) →
    (climb π (posVal tr pe h j) m lvl cur s k).runSeq (tr.drop i) =
      (k { s with off := s.off + 32 * m, log := (tr.take (i + m)).reverse }
        (if m = 0 then cur else aOf tr (i + m - 1))).runSeq (tr.drop (i + m)) ∧
      (bl π).drop (s.off + 32 * m) = bodyFrom tr (plan p) (i + m) ++ R ∧ s.off + 32 * m ≤ π.size
  | 0, lvl, cur, s, i, hlog, hb, hle, _, _, _ => by
    refine ⟨?_, by simpa using hb, by simpa using hle⟩
    simp only [climb, Nat.mul_zero, Nat.add_zero, ite_true]
    rw [← hlog]
  | m + 1, lvl, cur, s, i, hlog, hb, hle, hcur, hl, hP => by
    obtain ⟨cap, hPi⟩ := hP 0 (by omega)
    simp only [Nat.add_zero] at hPi
    obtain ⟨hlen, hhalf, -⟩ :=
      (show Good tr i ⟨.node pe h j lvl cap, 64⟩ by rw [← hPi]; exact hG i (by omega))
    have hq64 : (bl (qOf tr i)).length = 64 := by rw [← size_bl]; exact hlen
    have hbody : (bl π).drop s.off =
        (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).drop 32 else (bl (qOf tr i)).take 32) ++
          (bodyFrom tr (plan p) (i + 1) ++ R) := by
      rw [hb, bodyFrom_cons _ _ (by omega), hPi, List.append_assoc]
      congr 1
      show (if (bl (qOf tr i)).take 32 = (aOf tr (i - 1)).toList then (bl (qOf tr i)).drop 32
        else (bl (qOf tr i)).take 32) = _
      exact compare_rule hq64 hhalf
    have hcl : (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).drop 32
        else (bl (qOf tr i)).take 32).length = 32 := by
      split <;> simp [hq64]
    have hq : (if (posVal tr pe h j >>> lvl) % 2 = 0 then
        digestBytes cur ++ π.extract s.off (s.off + 32) else π.extract s.off (s.off + 32) ++ digestBytes cur) =
        qOf tr i := by
      apply ba_ext
      split
      · next h0 =>
        rw [bl_append, bl_digestBytes, bl_extract_body hbody hcl, if_pos h0, hcur, ← hhalf, if_pos h0,
          List.take_append_drop]
      · next h0 =>
        rw [bl_append, bl_digestBytes, bl_extract_body hbody hcl, if_neg h0, hcur, ← hhalf, if_neg h0,
          List.take_append_drop]
    have hl' : s.off + 32 ≤ π.size := by rw [← hcl]; exact le_of_body hbody hle
    have hb' : (bl π).drop (s.off + 32) = bodyFrom tr (plan p) (i + 1) ++ R := by
      rw [← hcl]; exact drop_body hbody
    obtain ⟨ih1, ih2, ih3⟩ := climb_runB R hn hG pe h j k m (lvl + 1) (aOf tr i)
      { s with off := s.off + 32, log := (qOf tr i, aOf tr i) :: s.log } (i + 1)
      (by simp only; rw [take_succ_rev tr (by omega), hlog]) hb' hl' (by simp) (by omega)
      (fun x hx => by
        obtain ⟨c, hc⟩ := hP (x + 1) (by omega)
        exact ⟨c, by rw [show i + 1 + x = i + (x + 1) by omega, hc]; congr 2; omega⟩)
    refine ⟨?_, ?_, ?_⟩
    · rw [climb, drop_cons_getD tr (by omega)]
      rw [ask_run _ _ _ (qOf tr i, aOf tr i) _ hq.symm, hq]
      simp only at ih1
      rw [ih1]
      have e1 : i + 1 + m = i + (m + 1) := by omega
      have e3 : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
      have e2 : (if m = 0 then aOf tr i else aOf tr (i + 1 + m - 1)) =
          (if m + 1 = 0 then cur else aOf tr (i + (m + 1) - 1)) := by
        rcases m with _ | m
        · simp
        · simp only [Nat.add_one_ne_zero, ite_false]; congr 1; omega
      rw [e2, e3, e1]
    · simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 32, show i + 1 + m = i + (m + 1) by omega] using ih2
    · have : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
      simp only at ih3
      omega

/-- The entries of positions `j₀ … j₀ + m − 1` of an opening's paths under `capPrune` (no inline cap). -/
def openPartN (L : Level) (pe j₀ m : Nat) : List PE :=
  (List.range' j₀ m).flatMap fun j => ⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
    ⟨.node pe L.height j lvl none, 64⟩

theorem openPlanN_eq (L : Level) (pe : Nat) : openPlanN L pe = openPartN L pe 0 L.t := by
  simp [openPlanN, openPartN, List.range_eq_range']

theorem openPartN_length (L : Level) (pe j₀ : Nat) : ∀ m, (openPartN L pe j₀ m).length = m * (1 + L.path)
  | 0 => by simp [openPartN]
  | m + 1 => by
    have := openPartN_length L pe (j₀ + 1) m
    simp only [openPartN, List.range'_succ, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_map, List.length_range] at this ⊢
    rw [this]; ring

/-- **The paths of an opening** (`pathsB`): per position the leaf query and the climb; the tops in sample order. -/
theorem pathsB_run {p : Params} {tr : Trace} {π : ByteArray} (R : List UInt8) (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (L : Level) (pe i0 : Nat) (hp1 : 1 ≤ L.path) (k : DSt → List Digest → OProg Bool) :
    ∀ (m j₀ : Nat) (s : DSt) (acc : List Digest), s.log = (tr.take (i0 + j₀ * (1 + L.path))).reverse →
    (bl π).drop s.off = bodyFrom tr (plan p) (i0 + j₀ * (1 + L.path)) ++ R → s.off ≤ π.size →
    Al (plan p) (i0 + j₀ * (1 + L.path)) (openPartN L pe j₀ m) →
    (pathsB π L ((List.range' j₀ m).map (posVal tr pe L.height)) s acc k).runSeq
        (tr.drop (i0 + j₀ * (1 + L.path))) =
      (k { s with off := s.off + m * (L.row + 32 * L.path),
                  log := (tr.take (i0 + (j₀ + m) * (1 + L.path))).reverse }
        (acc.reverse ++ (List.range' j₀ m).map fun j => aOf tr (i0 + j * (1 + L.path) + L.path))).runSeq
        (tr.drop (i0 + (j₀ + m) * (1 + L.path))) ∧
      (bl π).drop (s.off + m * (L.row + 32 * L.path)) =
        bodyFrom tr (plan p) (i0 + (j₀ + m) * (1 + L.path)) ++ R ∧
      s.off + m * (L.row + 32 * L.path) ≤ π.size
  | 0, j₀, s, acc, hlog, hb, hle, _ => by
    refine ⟨?_, by simpa using hb, by simpa using hle⟩
    simp only [List.range'_zero, List.map_nil, pathsB, Nat.zero_mul, Nat.add_zero, List.append_nil]
    rw [← hlog]
  | m + 1, j₀, s, acc, hlog, hb, hle, hal => by
    obtain ⟨i, hi_def⟩ : ∃ i, i = i0 + j₀ * (1 + L.path) := ⟨_, rfl⟩
    rw [← hi_def] at hlog hb hal ⊢
    have hsplit : openPartN L pe j₀ (m + 1) = (⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
        (⟨.node pe L.height j₀ lvl none, 64⟩ : PE)) ++ openPartN L pe (j₀ + 1) m := by
      simp [openPartN, List.range'_succ]
    rw [hsplit, Al_append] at hal
    obtain ⟨hal1, hal2⟩ := hal
    obtain ⟨hi, hPi⟩ := Al_head hal1
    have hal1' := Al_tail hal1
    simp only [List.length_cons, List.length_map, List.length_range] at hal2
    have hlt : i + 1 + L.path ≤ tr.length := by have := hal1.1; simp at this; omega
    obtain ⟨hlen, -⟩ := (show Good tr i ⟨.leaf, L.row⟩ by rw [← hPi]; exact hG i (by omega))
    have hbody : (bl π).drop s.off = bl (qOf tr i) ++ (bodyFrom tr (plan p) (i + 1) ++ R) := by
      rw [hb, bodyFrom_cons _ _ hi, hPi, List.append_assoc]; rfl
    have hcl : (bl (qOf tr i)).length = L.row := by rw [← size_bl]; exact hlen
    have hq : π.extract s.off (s.off + L.row) = qOf tr i := ba_ext (bl_extract_body hbody hcl)
    have hb1 : (bl π).drop (s.off + L.row) = bodyFrom tr (plan p) (i + 1) ++ R := by
      rw [← hcl]; exact drop_body hbody
    have hle1 : s.off + L.row ≤ π.size := by rw [← hcl]; exact le_of_body hbody hle
    have hi1 : i0 + (j₀ + 1) * (1 + L.path) = i + 1 + L.path := by rw [hi_def]; ring
    obtain ⟨c1, c2, c3⟩ := climb_runB R hn hG pe L.height j₀
      (fun s top => pathsB π L ((List.range' (j₀ + 1) m).map (posVal tr pe L.height)) s (top :: acc) k)
      L.path 0 (aOf tr i) { s with off := s.off + L.row, log := (qOf tr i, aOf tr i) :: s.log } (i + 1)
      (by simp only; rw [take_succ_rev tr (by omega), hlog]) hb1 hle1 (by simp) hlt
      (fun x hx => ⟨none, by
        have := hal1'.2 x (by simpa using hx)
        rw [this]; simp [List.getD_eq_getElem?_getD, hx]⟩)
    obtain ⟨d1, d2, d3⟩ := pathsB_run R hn hG L pe i0 hp1 k m (j₀ + 1)
      { s with off := s.off + L.row + 32 * L.path, log := (tr.take (i + 1 + L.path)).reverse }
      (aOf tr (i + L.path) :: acc) (by rw [hi1]) (by rw [hi1]; simpa using c2) (by simpa using c3)
      (by rw [hi1, show i + 1 + L.path = i + (L.path + 1) by omega]; exact hal2)
    have e1 : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) =
        s.off + (m + 1) * (L.row + 32 * L.path) := by ring
    have e2 : i0 + (j₀ + 1 + m) * (1 + L.path) = i0 + (j₀ + (m + 1)) * (1 + L.path) := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [List.range'_succ, List.map_cons, pathsB, drop_cons_getD tr (by omega)]
      rw [ask_run _ _ _ (qOf tr i, aOf tr i) _ hq.symm, hq]
      simp only at c1
      rw [c1]
      simp only [show L.path ≠ 0 by omega, ite_false, show i + 1 + L.path - 1 = i + L.path by omega]
      simp only at d1
      rw [hi1] at d1
      rw [d1, e1, e2]
      congr 2
      simp [List.range'_succ, hi_def]
    · rw [← e1, ← e2]; simpa using d2
    · rw [← e1]; simpa using d3

/-! ## The layer -/

/-- A digest read where the bytes `l` (32 of them) lie. -/
theorem digestAt_body {π : ByteArray} {a : Nat} {l rest : List UInt8} (h : (bl π).drop a = l ++ rest)
    (hl : l.length = 32) : (digestAt π a).toList = l := by
  apply List.ext_getElem (by simp [hl])
  intro y h1 h2
  simp only [digestAt, Vector.toList_ofFn, List.getElem_ofFn]
  rw [get!_body h (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- One step of `layerB`'s fold. -/
def layStep (π : ByteArray) (D : Nat) (qt : List (Nat × Digest)) (acc : Array Digest × Nat) (x : Nat) :
    Array Digest × Nat :=
  match qt.find? (fun e => e.1 >>> D == x) with
  | some e => (acc.1.push e.2, acc.2)
  | none => (acc.1.push (digestAt π acc.2), acc.2 + nodeBytes)

theorem layerB_eq (π : ByteArray) (m D : Nat) (qt : List (Nat × Digest)) (tail : Nat) :
    layerB π m D qt tail = (List.range (2 ^ m)).foldl (layStep π D qt) (#[], tail) := rfl

theorem getD_push_lt {a : Array Digest} {d : Digest} {x : Nat} (hx : x < a.size) :
    (a.push d).getD x zeroDigest = a.getD x zeroDigest := by
  simp [Array.getElem?_push, show x ≠ a.size by omega]

theorem getD_push_eq {a : Array Digest} {d : Digest} : (a.push d).getD a.size zeroDigest = d := by
  simp [Array.getElem?_push]

/-- **The layer's fold**: after the first `N` nodes, the layer holds `f x` at every `x < N` (a covered node is a
covering path's top, `hcov`; an uncovered one the next 32 tail bytes) and the tail cursor is at the uncovered
nodes from `N` on. -/
theorem layer_fold (π : ByteArray) (m D : Nat) (qt : List (Nat × Digest)) (f : Nat → List UInt8)
    (R : List UInt8) (tail : Nat) (hcov : ∀ e ∈ qt, f (e.1 >>> D) = e.2.toList)
    (hlen : ∀ x < 2 ^ m, (f x).length = 32)
    (ht : (bl π).drop tail = (List.range' 0 (2 ^ m)).flatMap
      (fun x => if qt.any (fun e => e.1 >>> D == x) then [] else f x) ++ R) (hle : tail ≤ π.size) :
    ∀ N, N ≤ 2 ^ m →
      ((List.range N).foldl (layStep π D qt) (#[], tail)).1.size = N ∧
      (∀ x < N, (((List.range N).foldl (layStep π D qt) (#[], tail)).1.getD x zeroDigest).toList = f x) ∧
      (bl π).drop ((List.range N).foldl (layStep π D qt) (#[], tail)).2 = (List.range' N (2 ^ m - N)).flatMap
        (fun x => if qt.any (fun e => e.1 >>> D == x) then [] else f x) ++ R ∧
      ((List.range N).foldl (layStep π D qt) (#[], tail)).2 ≤ π.size
  | 0, _ => by simpa using ⟨ht, hle⟩
  | N + 1, hN => by
    obtain ⟨h1, h2, h3, h4⟩ := layer_fold π m D qt f R tail hcov hlen ht hle N (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range N).foldl (layStep π D qt) (#[], tail) = acc at h1 h2 h3 h4
    rw [show 2 ^ m - N = (2 ^ m - (N + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons,
      List.append_assoc] at h3
    unfold layStep
    cases hf : qt.find? (fun e => e.1 >>> D == N) with
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have hx : e.1 >>> D = N := by simpa using List.find?_some hf
      have hany : qt.any (fun e => e.1 >>> D == N) = true := List.any_eq_true.mpr ⟨e, he, by simpa using hx⟩
      rw [hany, if_pos rfl, List.nil_append] at h3
      refine ⟨by simp [h1], fun x hx' => ?_, h3, h4⟩
      by_cases hxN : x < N
      · rw [getD_push_lt (by omega), h2 x hxN]
      · rw [show x = acc.1.size by omega, getD_push_eq, ← hcov e he, hx, h1]
    | none =>
      have hany : qt.any (fun e => e.1 >>> D == N) = false := by
        rw [List.any_eq_false]; intro e he; have := List.find?_eq_none.mp hf e he; simpa using this
      rw [hany, if_neg (by simp)] at h3
      have hfl := hlen N (by omega)
      refine ⟨by simp [h1], fun x hx' => ?_, ?_, ?_⟩
      · by_cases hxN : x < N
        · rw [getD_push_lt (by omega), h2 x hxN]
        · rw [show x = acc.1.size by omega, getD_push_eq, digestAt_body h3 hfl, h1]
      · show (bl π).drop (acc.2 + 32) = _
        rw [← hfl]; exact drop_body h3
      · show acc.2 + 32 ≤ π.size
        rw [← hfl]; exact le_of_body h3 h4

/-- The bytes of a list of at most-32-byte pieces. -/
theorem fm_len_le (g : Nat → List UInt8) : ∀ n, (∀ x < n, (g x).length ≤ 32) →
    ((List.range n).flatMap g).length ≤ 32 * n
  | 0, _ => by simp
  | n + 1, hg => by
    have := fm_len_le g n (fun x hx => hg x (by omega))
    have h1 := hg n (by omega)
    rw [List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

/-- With one empty piece, at most `n − 1` pieces of 32 bytes. -/
theorem fm_len_le1 (g : Nat → List UInt8) (x0 : Nat) (h0 : g x0 = []) : ∀ n, x0 < n →
    (∀ x < n, (g x).length ≤ 32) → ((List.range n).flatMap g).length ≤ 32 * (n - 1)
  | 0, h, _ => absurd h (by omega)
  | n + 1, hx0, hg => by
    rw [List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hx : x0 < n
    · have := fm_len_le1 g x0 h0 n hx (fun x hx => hg x (by omega))
      have h1 := hg n (by omega)
      have : 1 ≤ n := by omega
      rw [show n + 1 - 1 = n by omega]
      rw [show 32 * n = 32 * (n - 1) + 32 by omega]
      omega
    · rw [show x0 = n by omega] at h0
      rw [h0, List.length_nil, Nat.add_zero, show n + 1 - 1 = n by omega]
      exact fm_len_le g n (fun x hx => hg x (by omega))

/-! ## The heap -/

theorem getD_set! {A : Array Digest} {kk k' : Nat} {d : Digest} (hk : kk < A.size) :
    (A.set! kk d).getD k' zeroDigest = if k' = kk then d else A.getD k' zeroDigest := by
  by_cases h : k' = kk
  · subst h; simp [Array.set!, Array.getElem?_setIfInBounds, hk]
  · simp [Array.set!, Array.getElem?_setIfInBounds, h, Ne.symm h]

/-- **The heap** (`heapB`): each query is its two children (the layer's halves at the bottom, earlier heap answers
inside), so the driver asks the heap entries; afterwards `A` holds their answers at the slots `2^c …`. -/
theorem heapB_run {p : Params} {tr : Trace} (hn : tr.length = (plan p).length) (hG : AllGood p tr)
    (pe h t path i0 m c ce co hs : Nat) (hhs : i0 + t * (1 + path) = hs) (hm : 1 ≤ m) (lay : Array Digest)
    (hlay : ∀ x < 2 ^ m, (lay.getD x zeroDigest).toList = halfB tr (hs + 2 ^ (m - 1) - 1 - x / 2) (x % 2))
    (HP : ∀ kk, 2 ^ c ≤ kk → kk < 2 ^ m → (plan p).getD (hs + (2 ^ m - 1 - kk)) default =
      ⟨.heap pe h t path i0 m kk (if kk < 2 ^ (c + 1) then some (ce, co, c) else none), 64⟩)
    (hlt : hs + (2 ^ m - 2 ^ c) ≤ tr.length) :
    ∀ (n kk : Nat) (A : Array Digest) (s : DSt), kk + 1 = 2 ^ c + n → kk < 2 ^ m → A.size = 2 ^ m →
      (∀ k', kk < k' → k' < 2 ^ m → A.getD k' zeroDigest = aOf tr (hs + (2 ^ m - 1 - k'))) →
      s.log = (tr.take (hs + (2 ^ m - 1 - kk))).reverse →
      ∃ A' : Array Digest, A'.size = 2 ^ m ∧
        (∀ k', 2 ^ c ≤ k' → k' < 2 ^ m → A'.getD k' zeroDigest = aOf tr (hs + (2 ^ m - 1 - k'))) ∧
        ∀ k : DSt → Array Digest → OProg Bool,
        (heapB lay m n kk A s k).runSeq (tr.drop (hs + (2 ^ m - 1 - kk))) =
          (k { s with log := (tr.take (hs + (2 ^ m - 2 ^ c))).reverse } A').runSeq
            (tr.drop (hs + (2 ^ m - 2 ^ c)))
  | 0, kk, A, s, hkk, _, hA, hAinv, hlog => by
    have hc1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    refine ⟨A, hA, fun k' h1 h2 => hAinv k' (by (clear * - hkk h1; omega)) h2, fun k => ?_⟩
    have e : hs + (2 ^ m - 1 - kk) = hs + (2 ^ m - 2 ^ c) := by (clear * - hkk hc1; omega)
    rw [heapB, ← e, ← hlog]
  | n + 1, kk, A, s, hkk, hkm, hA, hAinv, hlog => by
    have hc1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    have hpm : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
    have hck : 2 ^ c ≤ kk := by (clear * - hkk; omega)
    have hk1 : 1 ≤ kk := le_trans hc1 hck
    obtain ⟨idx, hidx⟩ : ∃ idx, idx = hs + (2 ^ m - 1 - kk) := ⟨_, rfl⟩
    have hidx1 : hs + (2 ^ m - 1 - (kk - 1)) = idx + 1 := by (clear * - hidx hkm hk1; omega)
    rw [← hidx] at hlog ⊢
    have hi : idx < tr.length := by (clear * - hidx hlt hck hkm; omega)
    have hPk := HP kk hck hkm
    rw [← hidx] at hPk
    obtain ⟨hlen, hcond, -⟩ := (show Good tr idx
      ⟨.heap pe h t path i0 m kk (if kk < 2 ^ (c + 1) then some (ce, co, c) else none), 64⟩ by
        rw [← hPk]; exact hG idx hi)
    simp only at hlen hcond
    have hq : digestBytes (nodeB lay A m (2 * kk)) ++ digestBytes (nodeB lay A m (2 * kk + 1)) = qOf tr idx := by
      apply ba_ext
      rw [bl_append, bl_digestBytes, bl_digestBytes]
      conv_rhs => rw [← List.take_append_drop 32 (bl (qOf tr idx))]
      by_cases hb : 2 ^ (m - 1) ≤ kk
      · obtain ⟨y, hy⟩ : ∃ y, kk = 2 ^ (m - 1) + y := ⟨kk - 2 ^ (m - 1), (Nat.add_sub_cancel' hb).symm⟩
        have h1 : 2 ^ m ≤ 2 * kk := hpm ▸ Nat.mul_le_mul_left 2 hb
        have e0 : 2 * kk - 2 ^ m = 2 * y := by rw [hy, hpm, Nat.mul_add, Nat.add_sub_cancel_left]
        have e1 : 2 * kk + 1 - 2 ^ m = 2 * y + 1 := by
          rw [hy, hpm, Nat.mul_add, Nat.add_assoc, Nat.add_sub_cancel_left]
        have hyl : 2 * y + 1 < 2 ^ m := by rw [hpm]; (clear * - hy hkm hpm; omega)
        have hyi : hs + 2 ^ (m - 1) - 1 - y = idx := by (clear * - hidx hy hpm hkm; omega)
        rw [nodeB, if_pos h1, nodeB, if_pos (Nat.le_succ_of_le h1), e0, e1, hlay _ (Nat.lt_of_succ_lt hyl),
          hlay _ hyl, Nat.mul_div_cancel_left y (by decide), Nat.mul_add_div (by decide), Nat.mul_mod_right,
          Nat.mul_add_mod]
        simp [halfB, hyi]
      · rw [if_neg hb] at hcond
        have hlt2 : 2 * kk + 1 < 2 ^ m := by rw [hpm]; (clear * - hb; omega)
        rw [nodeB, if_neg (Nat.not_le.mpr (Nat.lt_of_succ_lt hlt2)), nodeB, if_neg (Nat.not_le.mpr hlt2),
          hAinv _ (by (clear * - hk1; omega)) (Nat.lt_of_succ_lt hlt2), hAinv _ (by (clear * -; omega)) hlt2,
          hcond.1, hcond.2, hhs]
    have hA' : (A.set! kk (aOf tr idx)).size = 2 ^ m := by simp [hA]
    obtain ⟨A', h1, h2, h3⟩ := heapB_run hn hG pe h t path i0 m c ce co hs hhs hm lay hlay HP hlt n (kk - 1)
      (A.set! kk (aOf tr idx)) { s with log := (qOf tr idx, aOf tr idx) :: s.log } (by (clear * - hkk hk1; omega))
      (lt_of_le_of_lt (Nat.sub_le kk 1) hkm) hA'
      (fun k' h1 h2 => by
        rw [getD_set! (hA ▸ hkm)]
        split
        · next he => subst he; rw [hidx]
        · next hne => exact hAinv k' (by (clear * - h1 hne; omega)) h2)
      (by simp only; rw [hidx1, take_succ_rev tr hi, hlog])
    refine ⟨A', h1, h2, fun k => ?_⟩
    have h3k := h3 k
    rw [hidx1] at h3k
    rw [heapB, drop_cons_getD tr hi, ask_run _ _ _ (qOf tr idx, aOf tr idx) _ hq.symm, hq]
    exact h3k

/-! ## One opening -/

theorem tailEntB_openN {tr : Trace} {L : Level} {pe : Nat} {e : PE} (he : e ∈ openPlanN L pe) (i : Nat) :
    tailEntB tr i e = [] := by
  simp only [openPlanN, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map] at he
  obtain ⟨j, -, he | ⟨lvl, -, rfl⟩⟩ := he
  · subst he; rfl
  · rfl

theorem contrib_heap {tr : Trace} {L : Level} {pe i0 c ce co : Nat} {e : PE} (he : e ∈ heapPlan L pe i0 c ce co)
    (i : Nat) : contrib tr i e = [] := by
  simp only [heapPlan, List.mem_map, List.mem_range] at he
  obtain ⟨n, -, rfl⟩ := he
  rfl

theorem getD_mem {P : List PE} {x : Nat} (hx : x < P.length) : P.getD x default ∈ P := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]; exact List.getElem_mem hx

/-- **One S2GB opening** (`openLoopB`): the paths, the layer (the first covering path's top, else the next tail
node), the covered check, the heap and the sent-cap check pass; the body cursor moves over the paths' bytes, the
tail cursor over the opening's uncovered layer nodes (at most `2^cap − 1`). -/
theorem openLoopB_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (L : Level) (c capOff pe i0 ce co : Nat) (R : List UInt8) (s : DSt) (t : Nat)
    (hcap : ∀ x < nodeBytes * 2 ^ c, π.get! (capOff + x) = (qOf tr ce).get! (co + x))
    (hp1 : 1 ≤ L.path) (hph : L.path + L.cap = L.height) (hc : c < L.cap) (ht1 : 1 ≤ L.t)
    (hpos : s.pos = (List.range L.t).map (posVal tr pe L.height)) (hlog : s.log = (tr.take i0).reverse)
    (hb : (bl π).drop s.off = bodyFrom tr (plan p) i0 ++ R) (hle : s.off ≤ π.size)
    (htl : (bl π).drop t = tailFrom tr (plan p) i0) (htle : t ≤ π.size)
    (hal : Al (plan p) i0 (openPlanN L pe ++ heapPlan L pe i0 c ce co)) (k : DSt → Nat → OProg Bool) :
    ∃ t', (openLoopB π L c capOff s t k).runSeq (tr.drop i0) =
        (k { s with off := s.off + L.t * (L.row + 32 * L.path),
                    log := (tr.take (i0 + L.t * (1 + L.path) + (2 ^ L.cap - 2 ^ c))).reverse } t').runSeq
          (tr.drop (i0 + L.t * (1 + L.path) + (2 ^ L.cap - 2 ^ c))) ∧
      (bl π).drop (s.off + L.t * (L.row + 32 * L.path)) =
        bodyFrom tr (plan p) (i0 + L.t * (1 + L.path) + (2 ^ L.cap - 2 ^ c)) ++ R ∧
      s.off + L.t * (L.row + 32 * L.path) ≤ π.size ∧
      (bl π).drop t' = tailFrom tr (plan p) (i0 + L.t * (1 + L.path) + (2 ^ L.cap - 2 ^ c)) ∧ t' ≤ π.size ∧
      t' ≤ t + nodeBytes * (2 ^ L.cap - 1) := by
  obtain ⟨hs, hhs⟩ : ∃ hs, i0 + L.t * (1 + L.path) = hs := ⟨_, rfl⟩
  rw [hhs]
  have hc1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hm1 : 1 ≤ L.cap := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  have hpm : 2 ^ L.cap = 2 * 2 ^ (L.cap - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hm1]
  have hcm : 2 ^ c ≤ 2 ^ (L.cap - 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt hc)
  have hc2 : 2 ^ (c + 1) ≤ 2 ^ L.cap := Nat.pow_le_pow_right (by norm_num) hc
  have hcC : 2 ^ c ≤ 2 ^ L.cap := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt hc)
  have hP1 : 2 ^ L.cap - 1 < 2 ^ L.cap := Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
  have hP2 : 2 ^ L.cap - 1 + 1 = 2 ^ L.cap := Nat.sub_add_cancel Nat.one_le_two_pow
  have hc2' : 2 ^ (c + 1) = 2 * 2 ^ c := Nat.pow_succ'
  -- the plan: the paths, then the heap
  rw [Al_append] at hal
  obtain ⟨hal1, hal2⟩ := hal
  have hlenN : (openPlanN L pe).length = L.t * (1 + L.path) := by rw [openPlanN_eq, openPartN_length]
  rw [hlenN, hhs] at hal2
  have hlenH : (heapPlan L pe i0 c ce co).length = 2 ^ L.cap - 2 ^ c := by simp [heapPlan]
  have hend : hs + (2 ^ L.cap - 2 ^ c) ≤ tr.length := by have := hal2.1; rw [hlenH, ← hn] at this; exact this
  have HP : ∀ kk, 2 ^ c ≤ kk → kk < 2 ^ L.cap → (plan p).getD (hs + (2 ^ L.cap - 1 - kk)) default =
      ⟨.heap pe L.height L.t L.path i0 L.cap kk (if kk < 2 ^ (c + 1) then some (ce, co, c) else none), 64⟩ := by
    intro kk h1 h2
    have hx : 2 ^ L.cap - 1 - kk < (heapPlan L pe i0 c ce co).length := by rw [hlenH]; (clear * - h1 h2 hc1; omega)
    rw [hal2.2 _ hx]
    rw [hlenH] at hx
    simp only [heapPlan, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx, Option.map_some,
      Option.getD_some]
    rw [Nat.sub_sub_self (Nat.le_sub_one_of_lt h2)]
  have GH : ∀ kk, 2 ^ c ≤ kk → kk < 2 ^ L.cap → Good tr (hs + (2 ^ L.cap - 1 - kk))
      ⟨.heap pe L.height L.t L.path i0 L.cap kk (if kk < 2 ^ (c + 1) then some (ce, co, c) else none), 64⟩ := by
    intro kk h1 h2
    rw [← HP kk h1 h2]; exact hG _ (by (clear * - h1 h2 hend; omega))
  -- the paths
  obtain ⟨P1, P2, P3⟩ : (∀ K : DSt → List Digest → OProg Bool,
      (pathsB π L s.pos s [] K).runSeq (tr.drop i0) =
        (K { s with off := s.off + L.t * (L.row + 32 * L.path), log := (tr.take hs).reverse }
          ((List.range L.t).map fun j => aOf tr (i0 + j * (1 + L.path) + L.path))).runSeq (tr.drop hs)) ∧
      (bl π).drop (s.off + L.t * (L.row + 32 * L.path)) = bodyFrom tr (plan p) hs ++ R ∧
      s.off + L.t * (L.row + 32 * L.path) ≤ π.size := by
    have H := fun K => pathsB_run R hn hG L pe i0 hp1 K L.t 0 s [] (by simpa using hlog) (by simpa using hb) hle
      (by simpa [openPlanN_eq] using hal1)
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, List.reverse_nil, List.nil_append, hhs] at H
    refine ⟨fun K => ?_, (H fun _ _ => .ret false).2.1, (H fun _ _ => .ret false).2.2⟩
    conv_lhs => rw [hpos]
    rw [List.range_eq_range', (H K).1]
  -- the layer
  have hlen32 : ∀ kk, 2 ^ c ≤ kk → kk < 2 ^ L.cap → (bl (qOf tr (hs + (2 ^ L.cap - 1 - kk)))).length = 64 := by
    intro kk h1 h2
    obtain ⟨hl, -⟩ := GH kk h1 h2
    rw [← size_bl]; exact hl
  set qt := (List.range L.t).map fun j => (posVal tr pe L.height j, aOf tr (i0 + j * (1 + L.path) + L.path))
    with hqt
  set f : Nat → List UInt8 := fun x => halfB tr (hs + 2 ^ (L.cap - 1) - 1 - x / 2) (x % 2) with hf
  have hx_lt : ∀ j, posVal tr pe L.height j >>> L.path < 2 ^ L.cap := fun j => by
    have := shiftRight_lt_pow (posVal_lt tr pe L.height j) (hph ▸ Nat.le_add_right _ _ : L.path ≤ L.height)
    rwa [show L.height - L.path = L.cap by rw [← hph, Nat.add_sub_cancel_left]] at this
  have hk2' : ∀ x < 2 ^ L.cap, 2 ^ (L.cap - 1) + x / 2 < 2 ^ L.cap := fun x hx => by (clear * - hx hpm; omega)
  have hidxx : ∀ x < 2 ^ L.cap,
      hs + 2 ^ (L.cap - 1) - 1 - x / 2 = hs + (2 ^ L.cap - 1 - (2 ^ (L.cap - 1) + x / 2)) :=
    fun x hx => by (clear * - hx hpm; omega)
  have hcov : ∀ e ∈ qt, f (e.1 >>> L.path) = e.2.toList := by
    intro e he
    rw [hqt, List.mem_map] at he
    obtain ⟨j, hj, rfl⟩ := he
    rw [List.mem_range] at hj
    have hx := hx_lt j
    obtain ⟨x, hxd⟩ : ∃ x, x = posVal tr pe L.height j >>> L.path := ⟨_, rfl⟩
    rw [← hxd] at hx ⊢
    have hk1 : 2 ^ c ≤ 2 ^ (L.cap - 1) + x / 2 := le_trans hcm (Nat.le_add_right _ _)
    have hk2 := hk2' x hx
    obtain ⟨-, hcond, -⟩ := GH _ hk1 hk2
    simp only [if_pos (Nat.le_add_right (2 ^ (L.cap - 1)) (x / 2))] at hcond
    have := hcond (x % 2) (Nat.mod_lt _ (by decide)) j hj
      (by rw [← hxd, Nat.add_sub_cancel_left, Nat.div_add_mod])
    simp only [hf, halfB]
    rw [hidxx x hx]
    exact this
  have hlen : ∀ x < 2 ^ L.cap, (f x).length = 32 := by
    intro x hx
    have h64 := hlen32 (2 ^ (L.cap - 1) + x / 2) (le_trans hcm (Nat.le_add_right _ _)) (hk2' x hx)
    simp only [hf, halfB]
    rw [hidxx x hx]
    split <;> simp [h64]
  -- the opening's tail bytes
  set G : Nat → List UInt8 := fun x => if qt.any (fun e => e.1 >>> L.path == x) then [] else f x with hG'
  have htail : (bl π).drop t = (List.range' 0 (2 ^ L.cap)).flatMap G ++
      tailFrom tr (plan p) (hs + (2 ^ L.cap - 2 ^ c)) := by
    rw [htl, tailFrom_skip tr (plan p) (L.t * (1 + L.path)) i0
      (by rw [← hn, hhs]; exact le_trans (Nat.le_add_right _ _) hend) (fun x hx => by
      rw [hal1.2 x (by rw [hlenN]; exact hx)]
      exact tailEntB_openN (getD_mem (by rw [hlenN]; exact hx)) _), hhs,
      tailFrom_cons _ _ (by rw [← hn]; (clear * - hend hcm hpm hc1; omega))]
    have H0 := HP (2 ^ L.cap - 1)
      (Nat.le_sub_one_of_lt (lt_of_le_of_lt hcm (Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt hm1 Nat.one_pos))))
      hP1
    rw [Nat.sub_self, Nat.add_zero] at H0
    rw [H0, tailFrom_skip tr (plan p) (2 ^ L.cap - 2 ^ c - 1) (hs + 1)
      (by rw [← hn]; (clear * - hend hc1 hcm hpm; omega)) (fun x hx => by
      have := HP (2 ^ L.cap - 2 - x) (by (clear * - hx hc1 hcm hpm; omega))
        (lt_of_le_of_lt (Nat.sub_le _ x) (Nat.sub_lt (Nat.two_pow_pos _) Nat.two_pos))
      rw [show hs + (2 ^ L.cap - 1 - (2 ^ L.cap - 2 - x)) = hs + 1 + x by (clear * - hx hc1 hcm hpm; omega)] at this
      rw [this]
      simp only [tailEntB]
      rw [if_neg (by (clear * - hpm hc1 hcm; omega))]),
      show hs + 1 + (2 ^ L.cap - 2 ^ c - 1) = hs + (2 ^ L.cap - 2 ^ c) by (clear * - hc1 hcm hpm; omega)]
    congr 1
    simp only [tailEntB, if_pos hP2, ← List.range_eq_range']
    refine List.flatMap_congr fun x _ => ?_
    simp only [hG', hf, coveredB, hqt, List.any_map, Function.comp_def]
    simp [beq_iff_eq]
  have hlay := layer_fold π L.cap L.path qt f _ t hcov hlen htail htle (2 ^ L.cap) le_rfl
  rw [← layerB_eq] at hlay
  obtain ⟨ly1, ly2, ly3, ly4⟩ := hlay
  rw [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.nil_append] at ly3
  -- the run
  unfold openLoopB
  rw [P1]
  try simp only
  have hz : s.pos.zip ((List.range L.t).map fun j => aOf tr (i0 + j * (1 + L.path) + L.path)) = qt := by
    rw [hpos, List.zip_map']
  rw [hz]
  have hall : (qt.all fun e => e.2 == (layerB π L.cap L.path qt t).1.getD (e.1 >>> L.path) zeroDigest) = true := by
    rw [List.all_eq_true]
    intro e he
    have hx : e.1 >>> L.path < 2 ^ L.cap := by
      rw [hqt, List.mem_map] at he; obtain ⟨j, -, rfl⟩ := he; exact hx_lt j
    rw [beq_iff_eq]
    exact (digest_ext (by rw [ly2 _ hx, hcov e he])).symm
  rw [if_pos hall]
  obtain ⟨A', hA1, hA2, hA3⟩ := heapB_run hn hG pe L.height L.t L.path i0 L.cap c ce co hs hhs hm1
    (layerB π L.cap L.path qt t).1 ly2 HP hend (2 ^ L.cap - 2 ^ c) (2 ^ L.cap - 1)
    (Array.replicate (2 ^ L.cap) zeroDigest)
    { s with off := s.off + L.t * (L.row + 32 * L.path), log := (tr.take hs).reverse }
    (by rw [hP2, Nat.add_sub_cancel' hcC]) hP1
    (by simp) (fun k' h1 h2 => absurd h1 (Nat.not_lt.mpr (Nat.le_sub_one_of_lt h2))) (by simp)
  simp only [Nat.sub_self, Nat.add_zero] at hA3
  rw [hA3]
  have hcapc : ((List.range (2 ^ c)).all fun i => nodeB (layerB π L.cap L.path qt t).1 A' L.cap (2 ^ c + i) ==
      digestAt π (capOff + nodeBytes * i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    have hci : 2 ^ c + i < 2 ^ (c + 1) := by rw [hc2']; (clear * - hi; omega)
    have hci' : 2 ^ c + i < 2 ^ L.cap := lt_of_lt_of_le hci hc2
    rw [beq_iff_eq, nodeB, if_neg (Nat.not_le.mpr hci'), hA2 _ (Nat.le_add_right _ _) hci']
    obtain ⟨-, -, hcg⟩ := GH (2 ^ c + i) (Nat.le_add_right _ _) hci'
    simp only [if_pos hci] at hcg
    rw [hcg, digestAt]
    apply Vector.ext; intro x hx
    simp only [Vector.getElem_ofFn]
    rw [Nat.add_assoc capOff, hcap _ (by simp only [nodeBytes] at hx ⊢; (clear * - hi hx; omega))]
    congr 1
    simp only [nodeBytes]; rw [Nat.add_sub_cancel_left, Nat.add_assoc]
  rw [if_pos hcapc]
  have hlen2 := congrArg List.length htail
  have hlen3 := congrArg List.length ly3
  simp only [List.length_drop, List.length_append, ← size_bl] at hlen2 hlen3
  have hfm : ((List.range' 0 (2 ^ L.cap)).flatMap G).length ≤ 32 * (2 ^ L.cap - 1) := by
    rw [← List.range_eq_range']
    refine fm_len_le1 G (posVal tr pe L.height 0 >>> L.path) ?_ _ (hx_lt 0) (fun x hx => ?_)
    · simp only [hG']
      rw [if_pos (List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr ht1, rfl⟩, by simp⟩)]
    · simp only [hG']; split
      · simp
      · rw [hlen x hx]
  refine ⟨(layerB π L.cap L.path qt t).2, rfl, ?_, P3, ly3, ly4, ?_⟩
  · rw [P2, bodyFrom_skip tr (plan p) (2 ^ L.cap - 2 ^ c) hs (by rw [← hn]; exact hend) (fun x hx => by
      rw [hal2.2 x (by rw [hlenH]; exact hx)]
      exact contrib_heap (getD_mem (by rw [hlenH]; exact hx)) _)]
  · simp only [nodeBytes]; (clear * - hlen2 hlen3 hfm ly4 htle; omega)

/-! ## The items -/

theorem InvB.congr {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w₁ w₂ : WS} {t : Nat}
    (h : InvB p tr π s w₁ t) (hi : w₁.i = w₂.i) (hp : w₁.pend = w₂.pend) (hs : w₁.st = w₂.st)
    (hpc : w₁.pcaps = w₂.pcaps) (hc : w₁.caps = w₂.caps) : InvB p tr π s w₂ t :=
  ⟨hi ▸ h.log, hs ▸ h.st, hp ▸ h.off, hi ▸ h.body, h.le, hp ▸ hpc ▸ hc ▸ h.caps, hi ▸ h.tail, h.tle⟩

/-- The layer nodes an item may read from the π tail: `2^cap − 1` for an opening, else none. -/
def capLI (p : Params) : Item → Nat
  | .opening r => 2 ^ (p.level r).cap - 1
  | _ => 0

theorem foldl_capLI (p : Params) (g : Nat → Item → Nat) (hg : ∀ a it, g a it = a + capLI p it) :
    ∀ (its : List Item) (a : Nat), its.foldl g a = a + (its.map (capLI p)).sum
  | [], a => by simp
  | it :: its, a => by
    rw [List.foldl_cons, foldl_capLI p g hg its, hg, List.map_cons, List.sum_cons]; omega

theorem capLayerNodes_eq (p : Params) : capLayerNodes p = ((schedule p).map (capLI p)).sum := by
  unfold capLayerNodes
  rw [foldl_capLI p _ (fun a it => by cases it <;> rfl), Nat.zero_add]

/-- A level whose cap is at least 1 is a level of the parameters, at its index. -/
theorem level_lv {p : Params} (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
    ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv) (r : Ref) (h : 1 ≤ (p.level r).cap) :
    (p.level r).level = r.lv := by
  rcases r with ⟨com, lv⟩
  unfold Params.level at h ⊢
  cases com <;> simp only [Params.levels] at h ⊢
  · by_cases hl : lv < p.mainLevels.length
    · exact hlv.1 lv hl
    · rw [List.getD_eq_default _ _ (by omega)] at h; exact absurd h (by decide)
  · by_cases hl : lv < p.recLevels.length
    · exact hlv.2 lv hl
    · rw [List.getD_eq_default _ _ (by omega)] at h; exact absurd h (by decide)

/-- **One item at S2GB** (`item_step`'s twin): the driver runs it on its entries and continues with the rest; the
tail cursor moves by at most `capLI` nodes. -/
theorem item_stepB {p : Params} {tr : Trace} {π : ByteArray} (hcp : p.capPrune = true)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    (hn : tr.length = (plan p).length) (hG : AllGood p tr) (k : DSt → Nat → OProg Bool) (its : List Item)
    (it : Item) (w : WS) (s : DSt) (t : Nat)
    (hI : InvB p tr π s w t) (hPo : PosInv p tr s w) (hok : (planItem p w it).2.ok = true)
    (hal : Al (plan p) w.i (planItem p w it).1)
    (hc : ∀ o ∈ Lvm.QLink.openItem p w it, p.capSendBits o.L.level o.L.cap < o.L.cap) :
    ∃ s1 t1, InvB p tr π s1 (planItem p w it).2 t1 ∧ PosInv p tr s1 (planItem p w it).2 ∧
      t1 ≤ t + nodeBytes * capLI p it ∧
      (driveItemsB p π (it :: its) s t k).runSeq (tr.drop w.i) =
        (driveItemsB p π its s1 t1 k).runSeq (tr.drop (planItem p w it).2.i) := by
  have hlen := hal.1
  cases it with
  | read m =>
    refine ⟨{ s with off := s.off + eBytes * m }, t, ⟨hI.log, hI.st, ?_, hI.body, hI.le,
      capsRel_wpend (by simp [planItem]) _ _ _ hI.caps, hI.tail, hI.tle⟩, hPo, by simp [capLI], rfl⟩
    simp only [planItem]; rw [hI.off]; omega
  | readW m wd =>
    refine ⟨{ s with off := s.off + wd * m }, t, ⟨hI.log, hI.st, ?_, hI.body, hI.le,
      capsRel_wpend (by simp [planItem]) _ _ _ hI.caps, hI.tail, hI.tle⟩, hPo, by simp [capLI], rfl⟩
    simp only [planItem]; rw [hI.off]; omega
  | cap c r =>
    refine ⟨{ s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ p.capSendBits r.lv c }, t,
      ⟨hI.log, hI.st, ?_, hI.body, hI.le,
        ⟨rfl, hI.off, by simp [planItem], capsRel_wpend (by simp [planItem]) _ _ _ hI.caps⟩, hI.tail, hI.tle⟩,
      hPo, by simp [capLI], rfl⟩
    simp only [planItem]; rw [hI.off]; omega
  | sample =>
    have hP0 : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩ := by
      simpa [planItem] using (Al_head (es := []) (by simpa [planItem] using hal)).2
    have hG0 : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by
      rw [← hP0]; exact hG _ (by simp [planItem] at hlen; omega)
    obtain ⟨hrun, hI1⟩ := fs_stepB hI (by simp [planItem] at hlen; omega) hn hP0 hG0
      (fun s _ => driveItemsB p π its s t k)
    exact ⟨dStep tr w.i s, t, hI1, fun r hr => hPo r hr, by simp [capLI], hrun⟩
  | positions r =>
    have hn1 : 1 ≤ (p.level r).nPosQ := by
      simp only [planItem, WS.settle, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    have hPx : ∀ x < (p.level r).nPosQ, (plan p).getD (w.i + x) default =
        ⟨.fs (if x = 0 then w.st else w.i + x - 1), if x = 0 then 32 + w.pend else 32⟩ := by
      intro x hx
      rw [hal.2 x (by simpa [planItem] using hx)]
      simp only [planItem]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx]
      simp only [Option.map_some, Option.getD_some]
      split_ifs <;> rfl
    obtain ⟨s', hI', hpos', hrun'⟩ := posLoop_runB (π := π) (t := t) hn hG (p.level r).height
      (fun s => driveItemsB p π its s t k) (p.level r).nPosQ (p.level r).t { s with pos := [] } w
      ⟨hI.log, hI.st, hI.off, hI.body, hI.le, hI.caps, hI.tail, hI.tle⟩
      (by simp [planItem] at hlen; omega) hPx
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepFS_iter w _ hn1
    refine ⟨s', t, hI'.congr (by simp [planItem, WS.settle, h1]) (by simp [planItem, WS.settle, h2])
      (by simp [planItem, WS.settle, h3]) (by simp [planItem, WS.settle, h4])
      (by simp [planItem, h5]), fun r' hr' => ?_, by simp [capLI], ?_⟩
    · simp only [planItem, WS.settle, Option.some.injEq] at hr'
      subst hr'
      rw [hpos', List.nil_append, posOut_eq _ _ _ _ _ (nPosQ_ge _)]
      simp [planItem, WS.settle, posVal]
    · rw [driveItemsB, hrun']
      simp [planItem, WS.settle]
  | opening r =>
    cases hf : w.caps.find? (·.1 == r) with
    | none => simp [planItem, hf] at hok
    | some cc =>
      obtain ⟨r', ce, co, nb⟩ := cc
      have hcr0 := hc ⟨w.i, p.level r, w.pe, ce, co⟩ (by simp [Lvm.QLink.openItem, hf])
      simp only [planItem, hf, hcp, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, List.isEmpty_iff] at hok hal hlen ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hpend⟩, hpc⟩, hpr⟩, hp1⟩, hph⟩, hm1⟩, -⟩, hnb⟩, hrow⟩, hnp⟩, -⟩ := hok
      simp only at hcr0
      rw [level_lv hlv r hm1] at hcr0
      have hcr := hI.caps
      rw [hpc] at hcr
      obtain ⟨capOff, hco, hbytes⟩ := capsRel_find r _ _ hcr hf
      have hpos := hPo r hpr
      have hoff : s.off = s.pend := by rw [hI.off, hpend, Nat.add_zero]
      have ht1 : 1 ≤ (p.level r).t := by simp only [positionsPerAnswer] at hnp; omega
      obtain ⟨t', o1, o2, o3, o4, o5, o6⟩ := openLoopB_run (π := π) hn hG (p.level r)
        (p.capSendBits r.lv (p.level r).cap) capOff w.pe w.i ce co (tailB p tr) s t
        (by rw [hnb]; exact hbytes) hp1 hph hcr0 ht1 hpos hI.log (by rw [hoff]; exact hI.body)
        (by rw [hoff]; exact hI.le) hI.tail hI.tle hal
        (fun s t => driveItemsB p π its { s with pend := s.off } t k)
      have hq : p.heapQ r.lv (p.level r).cap =
          2 ^ (p.level r).cap - 2 ^ p.capSendBits r.lv (p.level r).cap := by
        simp [Params.heapQ, hcp]
      refine ⟨{ s with
            off := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path)
            log := (tr.take (w.i + (p.level r).t * (1 + (p.level r).path) +
              (2 ^ (p.level r).cap - 2 ^ p.capSendBits r.lv (p.level r).cap))).reverse
            pend := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path) }, t',
        ⟨by simp [hq], hI.st, by simp [hpend], by simpa [hq] using o2, o3,
          by show CapsRel tr π _ _ w.pcaps s.caps w.caps; rw [hpc]; exact hcr, by simpa [hq] using o4, o5⟩,
        fun r' hr' => hPo r' hr', by simpa [capLI] using o6, ?_⟩
      rw [driveItemsB]
      simp only [capOffset, hco, hrow, ite_true]
      rw [o1, hq]

/-- **The items at S2GB** (`items_run`'s twin, with the tail cursor's bound). -/
theorem items_runB {p : Params} {tr : Trace} {π : ByteArray} (hcp : p.capPrune = true)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    (hn : tr.length = (plan p).length) (hG : AllGood p tr) (k : DSt → Nat → OProg Bool) :
    ∀ (its : List Item) (w : WS) (s : DSt) (t : Nat), InvB p tr π s w t → PosInv p tr s w →
    (planItems p w its).2.ok = true → Al (plan p) w.i (planItems p w its).1 →
    (∀ o ∈ Lvm.QLink.openItems p w its, p.capSendBits o.L.level o.L.cap < o.L.cap) →
    ∃ s' t', InvB p tr π s' (planItems p w its).2 t' ∧ PosInv p tr s' (planItems p w its).2 ∧
      t' ≤ t + nodeBytes * (its.map (capLI p)).sum ∧
      (driveItemsB p π its s t k).runSeq (tr.drop w.i) = (k s' t').runSeq (tr.drop (planItems p w its).2.i)
  | [], w, s, t, hI, hPo, _, _, _ => ⟨s, t, hI, hPo, by simp, by simp only [planItems, driveItemsB]⟩
  | it :: its, w, s, t, hI, hPo, hok, hal, hc => by
    obtain ⟨hal1, hal2⟩ := Al_planItems p hal
    have hok1 : (planItem p w it).2.ok = true := planItems_ok p _ its hok
    simp only [Lvm.QLink.openItems, List.mem_append] at hc
    obtain ⟨s1, t1, hI1, hPo1, ht1, hrun1⟩ :=
      item_stepB hcp hlv hn hG k its it w s t hI hPo hok1 hal1 (fun o ho => hc o (Or.inl ho))
    obtain ⟨s', t', hI', hPo', ht', hrun'⟩ :=
      items_runB hcp hlv hn hG k its _ s1 t1 hI1 hPo1 hok hal2 (fun o ho => hc o (Or.inr ho))
    refine ⟨s', t', hI', hPo', ?_, by rw [hrun1, hrun']; rfl⟩
    simp only [List.map_cons, List.sum_cons]; rw [Nat.mul_add]; omega

/-- **Replay of the S2GB driver** (`drive_replayP`'s twin, any `capPrune` stage whose openings keep fewer cap nodes
than their layer): on a trace of the schedule, `driveB` on `reassembleB` asks exactly the trace and returns `F` of
its stream; the π tail fits `tailMax`. -/
theorem drive_replayBP (p : Params) (hcp : p.capPrune = true) (hP : PlanOkB p)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    (hc : ∀ o ∈ Lvm.QLink.opens p, p.capSendBits o.L.level o.L.cap < o.L.cap) (tr : Trace) (hL : LinkOk p tr)
    (hsz : (reassemble p tr).size = piStatic p) (F : ByteArray → Bool) :
    (driveB p (reassembleB p tr) F).runSeq tr = some (F (traceBytesB tr)) ∧ (tailB p tr).length ≤ tailMax p := by
  obtain ⟨hn, hG⟩ := hL
  have hsl : seedLenP p = 32 + (headerBytesP p - 8) := seedLenP_eq p
  have h8 : 8 ≤ headerBytesP p := eight_le_hdrP p
  have hlen2 : 2 ≤ tr.length := by rw [hn, plan_length]; omega
  have hP0 : (plan p).getD 0 default = ⟨.q0, 7⟩ := rfl
  have hP1 : (plan p).getD 1 default = ⟨.fs 0, seedLenP p⟩ := rfl
  obtain ⟨-, hq0⟩ := (show Good tr 0 ⟨.q0, 7⟩ by rw [← hP0]; exact hG 0 (by omega))
  obtain ⟨hs1, hq1⟩ := (show Good tr 1 ⟨.fs 0, seedLenP p⟩ by rw [← hP1]; exact hG 1 (by omega))
  simp only at hq0 hq1 hs1
  have hPl : 2 ≤ (plan p).length := by rw [← hn]; exact hlen2
  have hblπ : bl (reassembleB p tr) = hdr8 ++ (bodyFrom tr (plan p) 0 ++ tailB p tr) := by
    rw [reassembleB, bl_mk, List.append_assoc]
  have hbody0 : (bl (reassembleB p tr)).drop 8 =
      (bl (qOf tr 1)).drop 32 ++ (bodyFrom tr (plan p) 2 ++ tailB p tr) := by
    rw [hblπ, List.drop_left' (by rfl : hdr8.length = 8), bodyFrom_cons _ _ (by omega),
      bodyFrom_cons _ _ (by omega), hP0, hP1]
    have c0 : contrib tr 0 ⟨.q0, 7⟩ = [] := rfl
    have c1 : contrib tr (0 + 1) ⟨.fs 0, seedLenP p⟩ = (bl (qOf tr 1)).drop 32 := rfl
    rw [c0, c1, List.nil_append, List.append_assoc]
  have hsizeπ : (reassembleB p tr).size = piStatic p + (tailB p tr).length := by
    rw [size_bl, hblπ, ← List.append_assoc, List.length_append, ← hsz, size_bl, bl_reassemble]
  set π := reassembleB p tr with hπ
  have hcl1 : ((bl (qOf tr 1)).drop 32).length = headerBytesP p - 8 := by
    rw [List.length_drop, ← size_bl, hs1, hsl]; omega
  have hseed : seedQuery π (aOf tr 0) (headerBytesP p) = qOf tr 1 := by
    apply ba_ext
    rw [seedQuery, bl_append, bl_digestBytes, ← hq1,
      show headerBytesP p = 8 + (headerBytesP p - 8) by omega, bl_extract_body hbody0 hcl1, List.take_append_drop]
  have hle8 : 8 ≤ π.size := by rw [size_bl, hblπ]; simp [hdr8]
  have hbodyH : (bl π).drop (headerBytesP p) = bodyFrom tr (plan p) 2 ++ tailB p tr := by
    rw [show headerBytesP p = 8 + ((bl (qOf tr 1)).drop 32).length by rw [hcl1]; omega, ← List.drop_drop,
      hbody0, List.drop_left]
  have hleH : headerBytesP p ≤ π.size := by
    have := le_of_body hbody0 hle8; rw [hcl1] at this; omega
  have htail0 : (bl π).drop (piStatic p) = tailFrom tr (plan p) 2 := by
    rw [hblπ, ← List.append_assoc, ← hsz, size_bl, bl_reassemble, List.drop_left, tailB_eq,
      tailFrom_cons _ _ (by omega), tailFrom_cons _ _ (by omega), hP0, hP1]
    rfl
  have hI0 : InvB p tr π ⟨headerBytesP p, headerBytesP p, aOf tr 1,
      [(seedQuery π (aOf tr 0) (headerBytesP p), aOf tr 1), (q0Query, aOf tr 0)], [], []⟩ w0 (piStatic p) := by
    refine ⟨?_, rfl, rfl, hbodyH, hleH, List.Forall₂.nil, htail0, by rw [hsizeπ]; omega⟩
    show _ = (tr.take 2).reverse
    rw [hseed, ← hq0]
    have e0 := entry_eq tr (i := 0) (by omega)
    have e1 := entry_eq tr (i := 1) (by omega)
    rw [show 2 = 0 + 1 + 1 from rfl, List.take_add_one, List.take_add_one, List.take_zero,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), ← e0, ← e1]
    rfl
  have hal : Al (plan p) w0.i (planAll p).1 := by
    refine ⟨by simp only [w0, plan_length]; omega, fun x hx => ?_⟩
    simp only [w0, plan, List.getD_eq_getElem?_getD]
    rw [show 2 + x = x + 1 + 1 by omega]
    simp
  obtain ⟨hok, hpend, -⟩ := hP
  obtain ⟨s', t', hI', -, ht', hrun⟩ := items_runB (π := π) hcp hlv hn hG
    (fun s t => .ret (s.off == piStatic p && t == π.size && F (streamOf s.log))) (schedule p) w0 _ _ hI0
    (fun _ h => by simp [w0] at h) hok hal hc
  have hend : (planAll p).2.i = tr.length := by
    rw [planAll, planItems_i, hn, plan_length]; simp [w0, planAll]
  have hoff : s'.off = piStatic p := by
    have h1 := hI'.off
    have h2 := hI'.body
    have h3 := hI'.le
    rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl] at h1 h2
    rw [hpend] at h1
    rw [hend, hn, bodyFrom_end _ _ le_rfl, List.nil_append] at h2
    have := congrArg List.length h2
    rw [List.length_drop, ← size_bl, hsizeπ] at this
    omega
  have htend : t' = π.size := by
    have h2 := hI'.tail
    rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, hn, tailFrom_end _ _ le_rfl,
      List.drop_eq_nil_iff, ← size_bl] at h2
    have := hI'.tle; omega
  have hlog : s'.log = tr.reverse := by
    rw [hI'.log, show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, List.take_length]
  have hTail : (tailB p tr).length ≤ tailMax p := by
    rw [tailMax, if_pos hcp, capLayerNodes_eq]
    rw [htend, hsizeπ] at ht'
    omega
  refine ⟨?_, hTail⟩
  have htr : tr = (qOf tr 0, aOf tr 0) :: (qOf tr 1, aOf tr 1) :: tr.drop 2 := by
    rw [← drop_cons_getD tr (i := 1) (by omega), ← drop_cons_getD tr (i := 0) (by omega)]; rfl
  have hrun' := hrun
  rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, List.drop_length] at hrun'
  conv_lhs => rw [htr]
  simp only [driveB, OProg.runSeq, hq0, ite_true, hseed]
  simp only [w0, hseed] at hrun'
  rw [hrun']
  simp [OProg.runSeq, hoff, htend, hlog, streamOf]

end Lvm.Replay
