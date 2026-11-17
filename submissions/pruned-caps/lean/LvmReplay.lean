-- New for lvm (WP-11b-QL): the replay theorem of BLUEPRINT §4.6 for lvm's driver. The statement's
-- shape is FR's (`FRVIRSpecCore.runSeq_runIR`, `FRNodeReadCore.readTrace_of_stream`; rf-k@8bff272b).
import LvmVerifierS
import LvmSchedLit
import LvmReplayBase

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmSubmissionSOff`, outside its import closure.)

-- ===== merged from `LvmReplayDrive` (GOLF module merge: `LvmReplayDrive.lean` is now a stub importing `LvmReplay`) =====
section
-- New for lvm (WP-11b-QL). FR's replay (`FRVIRSpecCore.runSeq_runIR`, `exec_append`) is for its IR
-- interpreter, not for a CPS driver; the shape of the statement (`runSeq` of the program on the trace
-- = the semantics on the trace) is FR's, the induction over `driveItems` is new.

/-!
# Replay, part 2: the driver on `reassemble tr` asks exactly `tr`

`items_run`: if the trace meets its plan (`Good` at every entry), the proof `π` holds the trace's
contributions (`(bl π).drop pend = bodyFrom …`), and the driver's state matches the walk's (`Inv`,
`PosInv`), then `driveItems` over the schedule items consumes exactly the items' entries of the
trace and continues with a state that again matches. Proved by induction over the items, with one
lemma per driver function: `fs_step` (one Fiat–Shamir query), `posLoop_run` (the positions
queries), `climb_run` (a Merkle path), `openLoop_run` (an opening), and the cap check from the caps
relation `CapsRel`.
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## The invariant -/

/-- The driver's caps (π offsets) against the walk's: pending caps sit at `pend + P` with
`P + bytes ≤ wpend`; absorbed caps hold, byte for byte, the bytes of their FS query. -/
def CapsRel (tr : Trace) (π : ByteArray) (pend wpend : Nat) :
    List (Ref × Nat × Nat) → List (Ref × Nat) → List (Ref × Nat × Nat × Nat) → Prop
  | [], dc, wc => List.Forall₂ (fun d c => d.1 = c.1 ∧
      ∀ x < c.2.2.2, π.get! (d.2 + x) = (qOf tr c.2.1).get! (c.2.2.1 + x)) dc wc
  | c :: pc, d :: dc, wc => d.1 = c.1 ∧ d.2 = pend + c.2.1 ∧ c.2.1 + c.2.2 ≤ wpend ∧
      CapsRel tr π pend wpend pc dc wc
  | _ :: _, [], _ => False

/-- **The driver's state matches the walk's** on the trace `tr` and the proof `π`. -/
structure Inv (p : Params) (tr : Trace) (π : ByteArray) (s : DSt) (w : WS) : Prop where
  log : s.log = (tr.take w.i).reverse
  st : s.st = aOf tr w.st
  off : s.off = s.pend + w.pend
  body : (bl π).drop s.pend = bodyFrom tr (plan p) w.i
  le : s.pend ≤ π.size
  caps : CapsRel tr π s.pend w.pend w.pcaps s.caps w.caps
  /-- `drive`'s walk: no cap pruning (`PlanOk`). -/
  cp : p.capPrune = false

/-- The driver's positions are the walk's oracle's. -/
def PosInv (p : Params) (tr : Trace) (s : DSt) (w : WS) : Prop :=
  ∀ r, w.posRef = some r → s.pos = (List.range (p.level r).t).map (posVal tr w.pe (p.level r).height)

/-- The trace meets its plan at every entry. -/
def AllGood (p : Params) (tr : Trace) : Prop := ∀ i < tr.length, Good tr i ((plan p).getD i default)

/-! ## Small facts -/

theorem entry_eq (tr : Trace) {i : Nat} (hi : i < tr.length) : (qOf tr i, aOf tr i) = tr[i] := by
  simp [qOf, aOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem drop_cons_getD (tr : Trace) {i : Nat} (hi : i < tr.length) :
    tr.drop i = (qOf tr i, aOf tr i) :: tr.drop (i + 1) := by
  rw [entry_eq tr hi]; exact List.drop_eq_getElem_cons hi

theorem take_succ_rev (tr : Trace) {i : Nat} (hi : i < tr.length) :
    (tr.take (i + 1)).reverse = (qOf tr i, aOf tr i) :: (tr.take i).reverse := by
  rw [entry_eq tr hi, List.take_add_one, List.getElem?_eq_getElem hi]
  simp

theorem getD_drop' (l : List UInt8) (a b : Nat) : (l.drop a).getD b 0 = l.getD (a + b) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem ask_run (q : ByteArray) (s : DSt) (k : DSt → Digest → OProg Bool) (e : ByteArray × Digest)
    (rest : Trace) (h : e.1 = q) :
    (ask q s k).runSeq (e :: rest) = (k { s with log := (q, e.2) :: s.log } e.2).runSeq rest := by
  obtain ⟨q', a⟩ := e
  simp only at h
  subst h
  simp [ask, OProg.runSeq]

/-- A byte of `π` inside the body read at `pend`. -/
theorem get!_body {π : ByteArray} {pend : Nat} {c rest : List UInt8} (h : (bl π).drop pend = c ++ rest)
    {y : Nat} (hy : y < c.length) : π.get! (pend + y) = c.getD y 0 := by
  rw [get!_bl, ← getD_drop', h, List.getD_append _ _ _ _ hy]

/-- The bytes `[a, a + n)` of `π`, inside the body read at `a`. -/
theorem bl_extract_body {π : ByteArray} {a : Nat} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest)
    {n : Nat} (hn : c.length = n) : bl (π.extract a (a + n)) = c := by
  rw [bl_extract, h, Nat.add_sub_cancel_left, List.take_left' hn]

theorem le_of_body {π : ByteArray} {a : Nat} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest)
    (ha : a ≤ π.size) : a + c.length ≤ π.size := by
  have := congrArg List.length h
  rw [List.length_drop, List.length_append, ← size_bl] at this
  (clear * - ha this; omega)

theorem drop_body {π : ByteArray} {a : Nat} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest) :
    (bl π).drop (a + c.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

/-! ## Caps -/

theorem capsRel_wpend {tr : Trace} {π : ByteArray} {pend wpend wpend' : Nat} (hw : wpend ≤ wpend') :
    ∀ (pc : List (Ref × Nat × Nat)) (dc : List (Ref × Nat)) (wc : List (Ref × Nat × Nat × Nat)),
    CapsRel tr π pend wpend pc dc wc → CapsRel tr π pend wpend' pc dc wc
  | [], dc, wc, h => h
  | c :: pc, d :: dc, wc, ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, by (clear * - hw h3; omega), capsRel_wpend hw pc dc wc h4⟩
  | _ :: _, [], _, h => h.elim

theorem capsRel_settle {tr : Trace} {π : ByteArray} {pend wpend i : Nat}
    (hb : ∀ y < wpend, π.get! (pend + y) = (qOf tr i).get! (32 + y)) (pend' : Nat) :
    ∀ (pc : List (Ref × Nat × Nat)) (dc : List (Ref × Nat)) (wc : List (Ref × Nat × Nat × Nat)),
    CapsRel tr π pend wpend pc dc wc →
      CapsRel tr π pend' 0 [] dc (pc.map (fun c => (c.1, i, 32 + c.2.1, c.2.2)) ++ wc)
  | [], dc, wc, h => h
  | c :: pc, d :: dc, wc, ⟨h1, h2, h3, h4⟩ => by
    refine List.Forall₂.cons ⟨h1, fun x hx => ?_⟩ (capsRel_settle hb pend' pc dc wc h4)
    simp only at hx ⊢
    rw [h2, Nat.add_assoc, hb _ (by (clear * - h3 hx; omega)), Nat.add_assoc]
  | _ :: _, [], _, h => h.elim

/-- With no pending cap, the driver finds a ref's cap where the walk does, with the same bytes. -/
theorem capsRel_find {tr : Trace} {π : ByteArray} (r : Ref) :
    ∀ (dc : List (Ref × Nat)) (wc : List (Ref × Nat × Nat × Nat)),
    List.Forall₂ (fun d c => d.1 = c.1 ∧
      ∀ x < c.2.2.2, π.get! (d.2 + x) = (qOf tr c.2.1).get! (c.2.2.1 + x)) dc wc →
    ∀ {r' : Ref} {ce co nb : Nat}, wc.find? (·.1 == r) = some (r', ce, co, nb) →
    ∃ capOff, (dc.find? (·.1 == r)).map (·.2) = some capOff ∧
      ∀ x < nb, π.get! (capOff + x) = (qOf tr ce).get! (co + x)
  | [], [], _, _, _, _, _, h => by simp at h
  | d :: dc, ⟨r'', ce', co', nb'⟩ :: wc, h, r', ce, co, nb, hf => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := List.forall₂_cons.mp h
    simp only at h1 h2
    by_cases hc : r'' = r
    · subst hc
      simp only [List.find?_cons, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      exact ⟨d.2, by simp [List.find?_cons, h1], h2⟩
    · have hne : (r'' == r) = false := by simpa using hc
      have hf' : wc.find? (·.1 == r) = some (r', ce, co, nb) := by
        simpa [List.find?_cons, hne] using hf
      obtain ⟨o, ho, hb⟩ := capsRel_find r dc wc h3 hf'
      exact ⟨o, by simpa [List.find?_cons, h1, hne] using ho, hb⟩
  | [], _ :: _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _, _ => by simp at h

/-! ## One Fiat–Shamir query -/

/-- The walk after one FS query at entry `w.i`. -/
def WS.stepFS (w : WS) : WS := { w.settle with i := w.i + 1, pend := 0, st := w.i }

/-- The driver after one FS query answered by entry `i`. -/
def dStep (tr : Trace) (i : Nat) (s : DSt) : DSt :=
  { s with log := (qOf tr i, aOf tr i) :: s.log, st := aOf tr i, pend := s.off }

theorem fs_step {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w : WS} (hI : Inv p tr π s w)
    (hi : w.i < tr.length) (hn : tr.length = (plan p).length)
    (hP : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩) (hG : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩)
    (k : DSt → Digest → OProg Bool) :
    (fsQuery π s k).runSeq (tr.drop w.i) = (k (dStep tr w.i s) (aOf tr w.i)).runSeq (tr.drop (w.i + 1)) ∧
      Inv p tr π (dStep tr w.i s) w.stepFS := by
  obtain ⟨hlen, hpre⟩ := hG
  simp only at hlen hpre
  have hbody : (bl π).drop s.pend = (bl (qOf tr w.i)).drop 32 ++ bodyFrom tr (plan p) (w.i + 1) := by
    rw [hI.body, bodyFrom_cons _ _ (by (clear * - hi hn; omega)), hP]; rfl
  have hcl : ((bl (qOf tr w.i)).drop 32).length = w.pend := by
    rw [List.length_drop, ← size_bl, hlen]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - w; omega))
  have hq : digestBytes s.st ++ π.extract s.pend s.off = qOf tr w.i := by
    apply ba_ext
    rw [bl_append, bl_digestBytes, hI.st, hI.off, bl_extract_body hbody hcl, ← hpre, List.take_append_drop]
  refine ⟨?_, ⟨?_, rfl, by simp [dStep, WS.stepFS], ?_, ?_, ?_, hI.cp⟩⟩
  · rw [fsQuery, drop_cons_getD tr hi, ask_run _ _ _ (qOf tr w.i, aOf tr w.i) _ hq.symm, hq]; rfl
  · simp only [dStep, WS.stepFS, WS.settle]; rw [take_succ_rev tr hi, hI.log]
  · simp only [dStep, WS.stepFS, WS.settle]
    rw [hI.off, ← hcl]; exact drop_body hbody
  · simp only [dStep]; rw [hI.off, ← hcl]; exact le_of_body hbody hI.le
  · simp only [dStep, WS.stepFS, WS.settle]
    refine capsRel_settle (fun y hy => ?_) _ _ _ _ hI.caps
    rw [get!_body hbody (by (clear * - hcl hy; omega)), get!_bl, getD_drop']

/-! ## The positions -/

/-- The positions `posLoop` draws from the answers of entries `e, e + 1, …` (`n` answers, `rem`
positions still to draw). -/
def posOut (tr : Trace) (h : Nat) : (e n rem : Nat) → List Nat
  | _, 0, _ => []
  | e, n + 1, rem =>
    (List.range (min positionsPerAnswer rem)).map (fun j => (answerBits (aOf tr e) >>> (j * h)) % 2 ^ h) ++
      posOut tr h (e + 1) n (rem - min positionsPerAnswer rem)

/-- The positions one answer gives (`posLoop`'s `ps`). -/
def posBatch (tr : Trace) (h e cnt : Nat) : List Nat :=
  (List.range cnt).map fun j => (answerBits (aOf tr e) >>> (j * h)) % 2 ^ h

theorem posOut_eq (tr : Trace) (h : Nat) : ∀ (n e rem : Nat), rem ≤ positionsPerAnswer * n →
    posOut tr h e n rem =
      (List.range rem).map fun j => (answerBits (aOf tr (e + j / 8)) >>> (j % 8 * h)) % 2 ^ h
  | 0, e, rem, hr => by simp [posOut, show rem = 0 by simpa [positionsPerAnswer] using hr]
  | n + 1, e, rem, hr => by
    simp only [posOut]
    rw [posOut_eq tr h n (e + 1) _ (by simp [positionsPerAnswer] at hr ⊢; (clear * - rem n hr; omega))]
    have hc : min positionsPerAnswer rem + (rem - min positionsPerAnswer rem) = rem := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - rem; omega))
    conv_rhs => rw [← hc, List.range_add, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      have : j < 8 := by simp [positionsPerAnswer] at hj; (clear * - hj; omega)
      rw [Nat.div_eq_of_lt this, Nat.mod_eq_of_lt this, Nat.add_zero]
    · refine List.map_congr_left fun j hj => ?_
      simp only [Function.comp, positionsPerAnswer] at hj ⊢
      by_cases h8 : 8 ≤ rem
      · rw [show min 8 rem = 8 by (clear * - hc h8; omega), show (8 + j) / 8 = j / 8 + 1 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - j; omega)),
          show (8 + j) % 8 = j % 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - j; omega)), Nat.add_comm (j / 8) 1, ← Nat.add_assoc]
      · simp at hj; (clear * - hc h8 hj; omega)

theorem stepFS_iter (w : WS) : ∀ n, 1 ≤ n →
    (WS.stepFS^[n] w).i = w.i + n ∧ (WS.stepFS^[n] w).pend = 0 ∧ (WS.stepFS^[n] w).st = w.i + n - 1 ∧
      (WS.stepFS^[n] w).pcaps = [] ∧ (WS.stepFS^[n] w).caps = w.settle.caps
  | 0, h => absurd h (by omega)
  | 1, _ => by simp [WS.stepFS, WS.settle]
  | n + 2, _ => by
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepFS_iter w.stepFS (n + 1) (by (clear * - n; omega))
    refine ⟨by rw [h1]; simp [WS.stepFS, WS.settle]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), h2, by rw [h3]; simp [WS.stepFS, WS.settle]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega),
      h4, by rw [h5]; simp [WS.stepFS, WS.settle]⟩

theorem posLoop_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (h : Nat) (k : DSt → OProg Bool) :
    ∀ (n rem : Nat) (s : DSt) (w : WS), Inv p tr π s w → w.i + n ≤ tr.length →
    (∀ x < n, (plan p).getD (w.i + x) default =
      ⟨.fs (if x = 0 then w.st else w.i + x - 1), if x = 0 then 32 + w.pend else 32⟩) →
    ∃ s', Inv p tr π s' (WS.stepFS^[n] w) ∧ s'.pos = s.pos ++ posOut tr h w.i n rem ∧
      (posLoop π h n rem s k).runSeq (tr.drop w.i) = (k s').runSeq (tr.drop (w.i + n))
  | 0, rem, s, w, hI, _, _ => ⟨s, hI, by simp [posOut], by simp [posLoop]⟩
  | n + 1, rem, s, w, hI, hl, hP => by
    have hP0 := hP 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - n; omega)))
    simp only [ite_true, Nat.add_zero] at hP0
    have hG0 : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by rw [← hP0]; exact hG _ (by (clear * - hn hl; omega))
    have hI' := (fs_step (k := fun _ _ => OProg.ret false) hI (by (clear * - hn hl; omega)) hn hP0 hG0).2
    have hI2 : Inv p tr π { (dStep tr w.i s) with
        pos := (dStep tr w.i s).pos ++ posBatch tr h w.i (min positionsPerAnswer rem) } w.stepFS :=
      ⟨hI'.log, hI'.st, hI'.off, hI'.body, hI'.le, hI'.caps, hI'.cp⟩
    obtain ⟨s', hI3, hpos3, hrun3⟩ := posLoop_run hn hG h k n (rem - min positionsPerAnswer rem) _ _ hI2
      (by simp [WS.stepFS, WS.settle]; (clear * - hn hl; omega)) (fun x hx => by
        have := hP (x + 1) (by (clear * - hx; omega))
        rw [show w.i + (x + 1) = w.stepFS.i + x by simp [WS.stepFS, WS.settle]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)] at this
        rw [this]
        rcases x with _ | x <;> simp [WS.stepFS, WS.settle] <;> omega)
    refine ⟨s', by rw [Function.iterate_succ_apply]; exact hI3, ?_, ?_⟩
    · rw [hpos3]; simp [dStep, posOut, posBatch, List.append_assoc, WS.stepFS, WS.settle]
    · rw [posLoop, (fs_step hI (by (clear * - hn hl; omega)) hn hP0 hG0 _).1]
      rw [show w.i + (n + 1) = w.stepFS.i + n by simp [WS.stepFS, WS.settle]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), ← hrun3]
      rfl

/-! ## Merkle paths and openings -/

/-- **The compare rule is the position rule** on a node entry that meets its plan. -/
theorem compare_rule {q : List UInt8} {cur : List UInt8} {b : Prop} [Decidable b] (hq : q.length = 64)
    (h : (if b then q.take 32 else q.drop 32) = cur) :
    (if q.take 32 = cur then q.drop 32 else q.take 32) = (if b then q.drop 32 else q.take 32) := by
  by_cases hb : b
  · rw [if_pos hb] at h; rw [if_pos h, if_pos hb]
  · rw [if_neg hb] at h
    rw [if_neg hb]
    split
    · next h' => rw [h', ← h]
    · rfl

theorem climb_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (pe h j : Nat) (k : DSt → Digest → OProg Bool) :
    ∀ (m lvl : Nat) (cur : Digest) (s : DSt) (i : Nat),
    s.log = (tr.take i).reverse → (bl π).drop s.off = bodyFrom tr (plan p) i → s.off ≤ π.size →
    cur = aOf tr (i - 1) → i + m ≤ tr.length →
    (∀ x < m, ∃ cap, (plan p).getD (i + x) default = ⟨.node pe h j (lvl + x) cap, 64⟩) →
    (climb π (posVal tr pe h j) m lvl cur s k).runSeq (tr.drop i) =
      (k { s with off := s.off + 32 * m, log := (tr.take (i + m)).reverse }
        (if m = 0 then cur else aOf tr (i + m - 1))).runSeq (tr.drop (i + m)) ∧
      (bl π).drop (s.off + 32 * m) = bodyFrom tr (plan p) (i + m) ∧ s.off + 32 * m ≤ π.size
  | 0, lvl, cur, s, i, hlog, hb, hle, _, _, _ => by
    refine ⟨?_, by simpa using hb, by simpa using hle⟩
    simp only [climb, Nat.mul_zero, Nat.add_zero, ite_true]
    rw [← hlog]
  | m + 1, lvl, cur, s, i, hlog, hb, hle, hcur, hl, hP => by
    obtain ⟨cap, hPi⟩ := hP 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - m; omega)))
    simp only [Nat.add_zero] at hPi
    obtain ⟨hlen, hhalf, -⟩ := (show Good tr i ⟨.node pe h j lvl cap, 64⟩ by rw [← hPi]; exact hG i (by (clear * - hn hl; omega)))
    have hq64 : (bl (qOf tr i)).length = 64 := by rw [← size_bl]; exact hlen
    have hbody : (bl π).drop s.off =
        (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).drop 32 else (bl (qOf tr i)).take 32) ++
          bodyFrom tr (plan p) (i + 1) := by
      rw [hb, bodyFrom_cons _ _ (by (clear * - hn hl; omega)), hPi]
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
    have hb' : (bl π).drop (s.off + 32) = bodyFrom tr (plan p) (i + 1) := by
      rw [← hcl]; exact drop_body hbody
    obtain ⟨ih1, ih2, ih3⟩ := climb_run hn hG pe h j k m (lvl + 1) (aOf tr i)
      { s with off := s.off + 32, log := (qOf tr i, aOf tr i) :: s.log } (i + 1)
      (by simp only; rw [take_succ_rev tr (by (clear * - hn hl; omega)), hlog]) hb' hl' (by simp) (by (clear * - hn hl; omega))
      (fun x hx => by
        obtain ⟨c, hc⟩ := hP (x + 1) (by (clear * - hx; omega))
        exact ⟨c, by rw [show i + 1 + x = i + (x + 1) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), hc]; congr 2; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)⟩)
    refine ⟨?_, ?_, ?_⟩
    · rw [climb, drop_cons_getD tr (by (clear * - hn hl; omega))]
      rw [ask_run _ _ _ (qOf tr i, aOf tr i) _ hq.symm, hq]
      simp only at ih1
      rw [ih1]
      have e1 : i + 1 + m = i + (m + 1) := by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
      have e3 : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
      have e2 : (if m = 0 then aOf tr i else aOf tr (i + 1 + m - 1)) =
          (if m + 1 = 0 then cur else aOf tr (i + (m + 1) - 1)) := by
        rcases m with _ | m
        · simp
        · simp only [Nat.add_one_ne_zero, ite_false]; congr 1; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
      rw [e2, e3, e1]
    · simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 32, show i + 1 + m = i + (m + 1) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)] using ih2
    · have : s.off + 32 + 32 * m = s.off + 32 * (m + 1) := by ring
      simp only at ih3
      (clear * - ih3; omega)

theorem shiftRight_lt_pow {n h k : Nat} (hn : n < 2 ^ h) (hk : k ≤ h) : n >>> k < 2 ^ (h - k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add,
    Nat.sub_add_cancel hk]
  exact hn

theorem posVal_lt (tr : Trace) (pe h j : Nat) : posVal tr pe h j < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos h)

/-- The entries of positions `j₀ … j₀ + m − 1` of an opening. -/
def openPart (L : Level) (pe ce co j₀ m : Nat) : List PE :=
  (List.range' j₀ m).flatMap fun j => ⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
    ⟨.node pe L.height j lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩

theorem openPlan_eq (L : Level) (pe ce co : Nat) : openPlan L pe ce co = openPart L pe ce co 0 L.t := by
  simp [openPlan, openPart, List.range_eq_range']

theorem openLoop_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (L : Level) (capOff pe ce co nb : Nat)
    (hcap : ∀ x < nb, π.get! (capOff + x) = (qOf tr ce).get! (co + x))
    (hnb : nodeBytes * 2 ^ (L.height - L.path) ≤ nb) (hp1 : 1 ≤ L.path) (hph : L.path ≤ L.height)
    (k : DSt → OProg Bool) :
    ∀ (m j₀ : Nat) (s : DSt) (i : Nat), s.log = (tr.take i).reverse →
    (bl π).drop s.off = bodyFrom tr (plan p) i → s.off ≤ π.size →
    Al (plan p) i (openPart L pe ce co j₀ m) →
    (openLoop π L capOff ((List.range' j₀ m).map (posVal tr pe L.height)) s k).runSeq (tr.drop i) =
      (k { s with
            off := s.off + m * (L.row + 32 * L.path)
            log := (tr.take (i + m * (1 + L.path))).reverse }).runSeq (tr.drop (i + m * (1 + L.path))) ∧
      (bl π).drop (s.off + m * (L.row + 32 * L.path)) = bodyFrom tr (plan p) (i + m * (1 + L.path)) ∧
      s.off + m * (L.row + 32 * L.path) ≤ π.size
  | 0, j₀, s, i, hlog, hb, hle, _ => by
    refine ⟨?_, by simpa using hb, by simpa using hle⟩
    simp only [List.range'_zero, List.map_nil, openLoop, Nat.zero_mul, Nat.add_zero]
    rw [← hlog]
  | m + 1, j₀, s, i, hlog, hb, hle, hal => by
    have hsplit : openPart L pe ce co j₀ (m + 1) = (⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
        (⟨.node pe L.height j₀ lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩ : PE)) ++
        openPart L pe ce co (j₀ + 1) m := by
      simp [openPart, List.range'_succ]
    rw [hsplit, Al_append] at hal
    obtain ⟨hal1, hal2⟩ := hal
    obtain ⟨hi, hPi⟩ := Al_head hal1
    have hal1' := Al_tail hal1
    simp only [List.length_cons, List.length_map, List.length_range] at hal2
    have hlt : i + 1 + L.path ≤ tr.length := by have := hal1.1; simp at this; (clear * - hn this; omega)
    obtain ⟨hlen, -⟩ := (show Good tr i ⟨.leaf, L.row⟩ by rw [← hPi]; exact hG i (by (clear * - hn hi; omega)))
    have hbody : (bl π).drop s.off = bl (qOf tr i) ++ bodyFrom tr (plan p) (i + 1) := by
      rw [hb, bodyFrom_cons _ _ hi, hPi]; rfl
    have hcl : (bl (qOf tr i)).length = L.row := by rw [← size_bl]; exact hlen
    have hq : π.extract s.off (s.off + L.row) = qOf tr i := ba_ext (bl_extract_body hbody hcl)
    have hb1 : (bl π).drop (s.off + L.row) = bodyFrom tr (plan p) (i + 1) := by
      rw [← hcl]; exact drop_body hbody
    have hle1 : s.off + L.row ≤ π.size := by rw [← hcl]; exact le_of_body hbody hle
    obtain ⟨c1, c2, c3⟩ := climb_run hn hG pe L.height j₀
      (fun s top => if top == digestAt π (capOff + nodeBytes * (posVal tr pe L.height j₀ >>> L.path)) then
        openLoop π L capOff ((List.range' (j₀ + 1) m).map (posVal tr pe L.height)) s k else .ret false)
      L.path 0 (aOf tr i) { s with off := s.off + L.row, log := (qOf tr i, aOf tr i) :: s.log } (i + 1)
      (by simp only; rw [take_succ_rev tr (by (clear * - hn hi; omega)), hlog]) hb1 hle1 (by simp) hlt
      (fun x hx => ⟨if x + 1 = L.path then some (ce, co, L.path) else none, by
        have := hal1'.2 x (by simpa using hx)
        rw [this]; simp [List.getD_eq_getElem?_getD, hx]⟩)
    -- the cap check holds
    have hlast : Good tr (i + L.path) ((plan p).getD (i + L.path) default) := hG _ (by (clear * - hn hlt; omega))
    have hPl : (plan p).getD (i + L.path) default =
        ⟨.node pe L.height j₀ (L.path - 1) (some (ce, co, L.path)), 64⟩ := by
      have := hal1'.2 (L.path - 1) (by simp; (clear * - hp1; omega))
      rw [show i + 1 + (L.path - 1) = i + L.path by (clear * - hp1; omega)] at this
      rw [this]; simp [List.getD_eq_getElem?_getD, show L.path - 1 < L.path by (clear * - hp1; omega),
        show L.path - 1 + 1 = L.path by (clear * - hp1; omega)]
    rw [hPl] at hlast
    obtain ⟨-, -, hcapEq⟩ := hlast
    simp only at hcapEq
    have hidx := shiftRight_lt_pow (posVal_lt tr pe L.height j₀) hph
    have htop : aOf tr (i + L.path) = digestAt π (capOff + nodeBytes * (posVal tr pe L.height j₀ >>> L.path)) := by
      rw [hcapEq, digestAt]
      apply Vector.ext; intro x hx
      simp only [Vector.getElem_ofFn]
      have hb32 : nodeBytes * (posVal tr pe L.height j₀ >>> L.path) + nodeBytes ≤
          nodeBytes * 2 ^ (L.height - L.path) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hidx
      rw [Nat.add_assoc capOff, hcap _ (by simp only [nodeBytes] at hb32 hnb ⊢; (clear * - hnb hidx hx; omega)), Nat.add_assoc]
    obtain ⟨d1, d2, d3⟩ := openLoop_run hn hG L capOff pe ce co nb hcap hnb hp1 hph k m (j₀ + 1)
      { s with off := s.off + L.row + 32 * L.path, log := (tr.take (i + 1 + L.path)).reverse } (i + 1 + L.path)
      rfl (by simpa using c2) (by simpa using c3) (by rw [show i + 1 + L.path = i + (L.path + 1) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]; exact hal2)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.range'_succ, List.map_cons, openLoop, drop_cons_getD tr (by (clear * - hn hi; omega))]
      rw [ask_run _ _ _ (qOf tr i, aOf tr i) _ hq.symm, hq]
      simp only at c1
      rw [c1]
      simp only [show L.path ≠ 0 by (clear * - hp1; omega), ite_false, show i + 1 + L.path - 1 = i + L.path by (clear * - hp1; omega), ← htop,
        beq_self_eq_true, ite_true]
      simp only at d1
      rw [d1]
      have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) =
          s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      have e' : i + 1 + L.path + m * (1 + L.path) = i + (m + 1) * (1 + L.path) := by ring
      rw [e, e']
    · have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) = s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      have e' : i + 1 + L.path + m * (1 + L.path) = i + (m + 1) * (1 + L.path) := by ring
      simpa [e, e'] using d2
    · have e : s.off + L.row + 32 * L.path + m * (L.row + 32 * L.path) = s.off + (m + 1) * (L.row + 32 * L.path) := by ring
      simp only at d3
      (clear * - d3 e; omega)

/-! ## The items -/

theorem Inv.congr {p : Params} {tr : Trace} {π : ByteArray} {s : DSt} {w₁ w₂ : WS} (h : Inv p tr π s w₁)
    (hi : w₁.i = w₂.i) (hp : w₁.pend = w₂.pend) (hs : w₁.st = w₂.st) (hpc : w₁.pcaps = w₂.pcaps)
    (hc : w₁.caps = w₂.caps) : Inv p tr π s w₂ :=
  ⟨hi ▸ h.log, hs ▸ h.st, hp ▸ h.off, hi ▸ h.body, h.le, hp ▸ hpc ▸ hc ▸ h.caps, h.cp⟩

theorem nPosQ_ge (L : Level) : L.t ≤ positionsPerAnswer * L.nPosQ := by
  simp only [Level.nPosQ, positionsPerAnswer]; (clear * - L; omega)

/-- **One item**: the driver runs it on its entries and continues with the rest. -/
theorem item_step {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (k : DSt → OProg Bool) (its : List Item) (it : Item) (w : WS) (s : DSt)
    (hI : Inv p tr π s w) (hPo : PosInv p tr s w) (hok : (planItem p w it).2.ok = true)
    (hal : Al (plan p) w.i (planItem p w it).1) :
    ∃ s1, Inv p tr π s1 (planItem p w it).2 ∧ PosInv p tr s1 (planItem p w it).2 ∧
      (driveItems p π (it :: its) s k).runSeq (tr.drop w.i) =
        (driveItems p π its s1 k).runSeq (tr.drop (planItem p w it).2.i) := by
  have hlen := hal.1
  cases it with
  | read m =>
    refine ⟨{ s with off := s.off + eBytes * m }, ⟨hI.log, hI.st, ?_, hI.body, hI.le,
      capsRel_wpend (by simp [planItem]) _ _ _ hI.caps, hI.cp⟩, hPo, rfl⟩
    simp only [planItem]; rw [hI.off]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  | readW m wd =>
    refine ⟨{ s with off := s.off + wd * m }, ⟨hI.log, hI.st, ?_, hI.body, hI.le,
      capsRel_wpend (by simp [planItem]) _ _ _ hI.caps, hI.cp⟩, hPo, rfl⟩
    simp only [planItem]; rw [hI.off]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  | cap c r =>
    have hcs : p.capSendBits r.lv c = c := by simp [Params.capSendBits, hI.cp]
    refine ⟨{ s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c },
      ⟨hI.log, hI.st, ?_, hI.body, hI.le, ⟨rfl, hI.off, by simp [planItem, hcs], capsRel_wpend (by simp [planItem]) _ _ _ hI.caps⟩,
        hI.cp⟩,
      hPo, rfl⟩
    simp only [planItem, hcs]; rw [hI.off]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  | sample =>
    have hP0 : (plan p).getD w.i default = ⟨.fs w.st, 32 + w.pend⟩ := by
      simpa [planItem] using (Al_head (es := []) (by simpa [planItem] using hal)).2
    have hG0 : Good tr w.i ⟨.fs w.st, 32 + w.pend⟩ := by rw [← hP0]; exact hG _ (by simp [planItem] at hlen; (clear * - hn hlen; omega))
    obtain ⟨hrun, hI1⟩ := fs_step hI (by simp [planItem] at hlen; (clear * - hn hlen; omega)) hn hP0 hG0
      (fun s _ => driveItems p π its s k)
    exact ⟨dStep tr w.i s, hI1, fun r hr => hPo r hr, hrun⟩
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
    obtain ⟨s', hI', hpos', hrun'⟩ := posLoop_run (π := π) hn hG (p.level r).height
      (fun s => driveItems p π its s k) (p.level r).nPosQ (p.level r).t { s with pos := [] } w
      ⟨hI.log, hI.st, hI.off, hI.body, hI.le, hI.caps, hI.cp⟩ (by simp [planItem] at hlen; (clear * - hn hlen; omega)) hPx
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepFS_iter w _ hn1
    refine ⟨s', hI'.congr (by simp [planItem, WS.settle, h1]) (by simp [planItem, WS.settle, h2])
      (by simp [planItem, WS.settle, h3]) (by simp [planItem, WS.settle, h4])
      (by simp [planItem, h5]), fun r' hr' => ?_, ?_⟩
    · simp only [planItem, WS.settle, Option.some.injEq] at hr'
      subst hr'
      rw [hpos', List.nil_append, posOut_eq _ _ _ _ _ (nPosQ_ge _)]
      simp [planItem, WS.settle, posVal]
    · rw [driveItems, hrun']
      simp [planItem, WS.settle]
  | opening r =>
    cases hf : w.caps.find? (·.1 == r) with
    | none => simp [planItem, hf] at hok
    | some c =>
      obtain ⟨r', ce, co, nb⟩ := c
      simp only [planItem, hf, hI.cp, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq, List.isEmpty_iff] at hok hal hlen ⊢
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hpend⟩, hpc⟩, hpr⟩, hp1⟩, hph⟩, hnb⟩, hrow⟩, -⟩, -⟩ := hok
      have hcr := hI.caps
      rw [hpc] at hcr
      obtain ⟨capOff, hco, hbytes⟩ := capsRel_find r _ _ hcr hf
      have hpos := hPo r hpr
      have hoff : s.off = s.pend := by rw [hI.off, hpend, Nat.add_zero]
      obtain ⟨o1, o2, o3⟩ := openLoop_run (π := π) hn hG (p.level r) capOff w.pe ce co nb hbytes hnb hp1 hph
        (fun s => driveItems p π its { s with pend := s.off } k) (p.level r).t 0 s w.i hI.log
        (by rw [hoff]; exact hI.body) (by rw [hoff]; exact hI.le) (by rw [← openPlan_eq]; exact hal)
      refine ⟨{ s with
            off := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path)
            log := (tr.take (w.i + (p.level r).t * (1 + (p.level r).path))).reverse
            pend := s.off + (p.level r).t * ((p.level r).row + 32 * (p.level r).path) },
        ⟨by simp [Nat.mul_comm], hI.st, by simp [hpend], by simpa [Nat.mul_comm] using o2,
          by simpa using o3, by show CapsRel tr π _ _ w.pcaps s.caps w.caps; rw [hpc]; exact hcr, hI.cp⟩,
        fun r' hr' => hPo r' hr', ?_⟩
      rw [driveItems]
      simp only [capOffset, hco, hrow, ite_true]
      rw [hpos, List.range_eq_range', o1]
      simp only [Nat.mul_comm]
      rw [← List.range_eq_range', ← hpos]

end Lvm.Replay
end
-- ===== end of `LvmReplayDrive` =====

/-!
# Replay (BLUEPRINT §4.6)

**`VS_replay`**: for every parameter set whose plan passes its static checks (`PlanOk`), every
trace `tr` that is a trace of the schedule (`LinkOk p tr`: the plan's length, and at every entry
the plan's query length and link, which is what Q_link asserts on the stream), and a header that
`V_S` accepts natively,

  `(V_S vk c (reassemble p tr)).runSeq tr = some (F vk c (traceBytesB tr))`,

where `F = decideF p m vk c` is `V_S`'s decision on the stream `Σ = tagTrace ‖ traceBytes tr`.
`drive_replay` is the driver alone (no header check), for any decision `F`.

The proof (`LvmReplayDrive`) runs the driver item by item against the walk that defines the plan:
every query the driver forms from `π = reassemble p tr` and the answers so far is the trace's
entry, because `π` is the concatenation of the entries' contributions and every entry starts with
the state, holds the current node in the half its position bit selects, and ends each path on the
cap node. At the end every body byte has been read (`off = |π|`) and the log is `tr`.

`PlanOk P20`, `PlanOk P8` are decided; `plan_P20`/`plan_P8` check the plan against
WP-11a's schedule tallies (`qS`, `piSize`, the query lengths of `queryList`).
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

theorem items_run {p : Params} {tr : Trace} {π : ByteArray} (hn : tr.length = (plan p).length)
    (hG : AllGood p tr) (k : DSt → OProg Bool) :
    ∀ (its : List Item) (w : WS) (s : DSt), Inv p tr π s w → PosInv p tr s w →
    (planItems p w its).2.ok = true → Al (plan p) w.i (planItems p w its).1 →
    ∃ s', Inv p tr π s' (planItems p w its).2 ∧ PosInv p tr s' (planItems p w its).2 ∧
      (driveItems p π its s k).runSeq (tr.drop w.i) = (k s').runSeq (tr.drop (planItems p w its).2.i)
  | [], w, s, hI, hPo, _, _ => ⟨s, hI, hPo, by simp only [planItems, driveItems]⟩
  | it :: its, w, s, hI, hPo, hok, hal => by
    obtain ⟨hal1, hal2⟩ := Al_planItems p hal
    have hok1 : (planItem p w it).2.ok = true := planItems_ok p _ its hok
    obtain ⟨s1, hI1, hPo1, hrun1⟩ := item_step hn hG k its it w s hI hPo hok1 hal1
    obtain ⟨s', hI', hPo', hrun'⟩ := items_run hn hG k its _ s1 hI1 hPo1 hok hal2
    exact ⟨s', hI', hPo', by rw [hrun1, hrun']; rfl⟩

theorem plan_length (p : Params) : (plan p).length = 2 + (planAll p).1.length := by
  simp [plan]; (clear * - p; omega)

theorem bl_reassemble (p : Params) (tr : Trace) : bl (reassemble p tr) = hdr8 ++ bodyFrom tr (plan p) 0 :=
  bl_mk _

/-- **Replay of the driver**: on a trace of the schedule, the driver on the reassembled proof asks
exactly the trace and returns `F` of its stream (any stage: the header to `headerBytesP p`). -/
theorem drive_replayP (p : Params) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr)
    (F : ByteArray → Bool) :
    (drive p (reassemble p tr) F).runSeq tr = some (F (traceBytesB tr)) := by
  obtain ⟨hn, hG⟩ := hL
  have hH8 : 8 ≤ headerBytes := by decide
  have hsl : seedLenP p = 32 + (headerBytesP p - 8) := seedLenP_eq p
  have h8 : 8 ≤ headerBytesP p := eight_le_hdrP p
  have hlen2 : 2 ≤ tr.length := by rw [hn, plan_length]; (clear * - p tr; omega)
  set π := reassemble p tr with hπ
  set P := plan p with hPdef
  -- the first two entries
  have hP0 : P.getD 0 default = ⟨.q0, 7⟩ := rfl
  have hP1 : P.getD 1 default = ⟨.fs 0, seedLenP p⟩ := rfl
  obtain ⟨-, hq0⟩ := (show Good tr 0 ⟨.q0, 7⟩ by rw [← hP0]; exact hG 0 (by (clear * - tr p hlen2 hn; omega)))
  obtain ⟨hs1, hq1⟩ := (show Good tr 1 ⟨.fs 0, seedLenP p⟩ by rw [← hP1]; exact hG 1 (by (clear * - tr p hlen2 hn; omega)))
  simp only at hq0 hq1 hs1
  have hPl : 2 ≤ (plan p).length := by rw [← hPdef, ← hn]; exact hlen2
  have hbody0 : (bl π).drop 8 = (bl (qOf tr 1)).drop 32 ++ bodyFrom tr P 2 := by
    rw [hπ, bl_reassemble, List.drop_left' (by rfl : hdr8.length = 8), bodyFrom_cons _ _ (by (clear * - p tr hPl; omega)),
      bodyFrom_cons _ _ (by (clear * - p tr hPl; omega)), hP0, hP1]
    -- the two contributions by name: a closing `rfl` here sent the kernel through `bodyFrom tr (plan p)` (the
    -- schedule's items) to align `[] ++ (c ++ b)` with `c ++ b` (GOLF-DEC2: 4.4 s of kernel time)
    have c0 : contrib tr 0 ⟨.q0, 7⟩ = [] := rfl
    have c1 : contrib tr (0 + 1) ⟨.fs 0, seedLenP p⟩ = (bl (qOf tr 1)).drop 32 := rfl
    rw [c0, c1, List.nil_append]
  have hcl1 : ((bl (qOf tr 1)).drop 32).length = headerBytesP p - 8 := by
    rw [List.length_drop, ← size_bl, hs1, hsl]; (clear * - p tr hsl hs1; omega)
  have hseed : seedQuery π (aOf tr 0) (headerBytesP p) = qOf tr 1 := by
    apply ba_ext
    rw [seedQuery, bl_append, bl_digestBytes, ← hq1,
      show headerBytesP p = 8 + (headerBytesP p - 8) by (clear * - p tr hsl h8 hs1 hcl1; omega), bl_extract_body hbody0 hcl1, List.take_append_drop]
  have hle8 : 8 ≤ π.size := by rw [size_bl, hπ, bl_reassemble]; simp [hdr8]
  have hbodyH : (bl π).drop (headerBytesP p) = bodyFrom tr P 2 := by
    rw [show headerBytesP p = 8 + ((bl (qOf tr 1)).drop 32).length by rw [hcl1]; (clear * - p tr hsl h8 hs1 hcl1; omega), ← List.drop_drop,
      hbody0, List.drop_left]
  have hleH : headerBytesP p ≤ π.size := by
    have := le_of_body hbody0 hle8; rw [hcl1] at this
    (clear * - p π tr hsl h8 hs1 hcl1 this; omega)
  -- the walk from entry 2
  have hI0 : Inv p tr π ⟨headerBytesP p, headerBytesP p, aOf tr 1,
      [(seedQuery π (aOf tr 0) (headerBytesP p), aOf tr 1), (q0Query, aOf tr 0)], [], []⟩ w0 := by
    refine ⟨?_, rfl, rfl, hbodyH, hleH, List.Forall₂.nil, hP.2.2.2⟩
    show _ = (tr.take 2).reverse
    rw [hseed, ← hq0]
    have e0 := entry_eq tr (i := 0) (by (clear * - tr p hlen2 hn; omega))
    have e1 := entry_eq tr (i := 1) (by (clear * - tr p hlen2 hn; omega))
    rw [show 2 = 0 + 1 + 1 from rfl, List.take_add_one, List.take_add_one, List.take_zero,
      List.getElem?_eq_getElem (by (clear * - tr p hlen2 hn; omega)), List.getElem?_eq_getElem (by (clear * - tr p hlen2 hn; omega)), ← e0, ← e1]
    rfl
  have hal : Al P w0.i (planAll p).1 := by
    refine ⟨by simp only [w0, hPdef, plan_length]; (clear * - p tr; omega), fun x hx => ?_⟩
    simp only [w0, hPdef, plan, List.getD_eq_getElem?_getD]
    rw [show 2 + x = x + 1 + 1 by (clear * - x p tr; omega)]
    simp
  obtain ⟨hok, hpend, -⟩ := hP
  obtain ⟨s', hI', -, hrun⟩ := items_run (π := π) hn hG
    (fun s => .ret (s.off == π.size && F (streamOf s.log))) (schedule p) w0 _ hI0
    (fun _ h => by simp [w0] at h) hok hal
  have hend : (planAll p).2.i = tr.length := by
    rw [planAll, planItems_i, hn, plan_length]; simp [w0, planAll]
  have hoff : s'.off = π.size := by
    have h1 := hI'.off
    have h2 := hI'.body
    have h3 := hI'.le
    rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl] at h1 h2
    rw [hpend] at h1
    rw [hend, hn, bodyFrom_end _ _ le_rfl, List.drop_eq_nil_iff, ← size_bl] at h2
    (clear * - s' π p tr h1 h2 h3; omega)
  have hlog : s'.log = tr.reverse := by
    rw [hI'.log, show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, List.take_length]
  -- run
  have htr : tr = (qOf tr 0, aOf tr 0) :: (qOf tr 1, aOf tr 1) :: tr.drop 2 := by
    rw [← drop_cons_getD tr (i := 1) (by (clear * - tr p hlen2 hn s' hend; omega)), ← drop_cons_getD tr (i := 0) (by (clear * - tr p hlen2 hn s' hend; omega))]; rfl
  have hrun' := hrun
  rw [show (planItems p w0 (schedule p)).2 = (planAll p).2 from rfl, hend, List.drop_length] at hrun'
  conv_lhs => rw [htr]
  simp only [drive, OProg.runSeq, hq0, ite_true, hseed]
  simp only [w0, hseed] at hrun'
  rw [hrun']
  simp [OProg.runSeq, hoff, hlog, streamOf]

/-! ## The production and test sets -/

/-- `P20` with its WHIR levels written out (`levels_P20`, `t_P20`), so that the kernel does not
recompute the query counts at every use. -/
def P20L : Params := { P20 with
  mainLevels := [⟨0, 6, 17, 2, 19, 8, 11, 115, 376⟩, ⟨1, 4, 13, 3, 16, 7, 9, 77, 384⟩,
    ⟨2, 4, 9, 4, 13, 7, 6, 58, 384⟩]
  recLevels := [] }

theorem P20_eq : P20 = P20L := by
  have h1 : P20.mainLevels = P20L.mainLevels := by decide +kernel
  have h2 : P20.recLevels = P20L.recLevels := by decide +kernel
  show P20 = { P20 with mainLevels := P20L.mainLevels, recLevels := P20L.recLevels }
  rw [← h1, ← h2]

set_option maxRecDepth 200000 in
/-- `PlanOk P20` and the walk's last entry (WP-16b: one decision; the plan's length from it by
`plan_length`, `planItems_i`, without evaluating the entries). -/
theorem planSt_P20 : PlanOk P20 ∧ (planAll P20).2.i = 3860 := by
  -- the schedule from `phases_P20_lit` (GOLF-MID's literal), not rebuilt here (GOLF-DEC3)
  rw [PlanOk, planAll, schedule, phases_P20_lit, P20_eq]; decide +kernel

theorem planOk_P20 : PlanOk P20 := planSt_P20.1

end Lvm.Replay
