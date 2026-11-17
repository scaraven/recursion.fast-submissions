-- New for lvm (WP-13a), after FR's `FRXSpec` (`parse_isK`, `tape_byte0`, `E_W`), `FRXLeaf` (`E_leaf`) and
-- `FRXNodeRun` (`E_node`, `E_node_out`; rf-k/submissions/flock-recursive/lean@kk/base): what `EX` returns.
import LvmXTop
import LvmLog
import LvmXRead1
import LvmXOut
import LvmXOutSeg
import LvmReassemble
import LvmReplay

-- (GOLF2: 16 declarations that `certified` does not use moved verbatim to `LvmSubmissionSOff`, outside its import closure.)

-- ===== merged from `LvmXReasm` (GOLF module merge: `LvmXReasm.lean` is now a stub importing `LvmXSpec`) =====
section
-- New for lvm (WP-13a): the extractor's reassembled proof is WP-11b-QL's reassemble.

/-!
# `reassembleL` is `Lvm.Replay.reassemble` on the extractor's trace

`Lvm.Replay.reassemble p tr` (WP-11b-QL) walks the plan: entry `i`'s contribution is picked by its
planned class (`contrib`). `reassembleL` (the extractor's, `LvmXOut`) picks it by the query's length
(`piece`), after the previous entry's answer. On the extractor's trace `readTraceL W` they agree:

* `ra_pieces_eq`: `pieces` as a `flatMap` over entry indices;
* `ra_contrib`: per entry, `contrib = piece` when the query has the planned length and the planned
  class agrees with that length (`raOk`);
* `ra_plan_chk` (static): the plan's lengths are `7 :: lensL` and every class agrees with its length
  (from `planOk_P20` and `blocks_ok`, `ra_plan_chk_of`);
* `ra_len_readTraceL`: entry `i` of `readTraceL W` has `(7 :: lensL).getD i 0` query bytes.
-/

set_option autoImplicit false

namespace Lvm.X

open RecursionFast Lvm Lvm.Replay

/-! ## `pieces` by index -/

theorem ra_pieces_eq : ∀ (prev : Digest) (tr : Trace),
    pieces prev tr = (List.range tr.length).flatMap fun i =>
      piece (if i = 0 then prev else (tr.getD (i - 1) dflt).2) (tr.getD i dflt)
  | _, [] => rfl
  | prev, e :: tr => by
    rw [pieces, ra_pieces_eq e.2 tr, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp only [List.getD_cons_zero]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    cases i with
    | zero => rfl
    | succ i => simp

/-- The plan's bodies as a `flatMap` over entry indices, entry by entry equal to `pieces`'. -/
theorem ra_body (tr : Trace) (P : List PE) (hl : P.length = tr.length)
    (h : ∀ i < tr.length, contrib tr i (P.getD i default) =
      piece (if i = 0 then Vector.replicate 32 0 else (tr.getD (i - 1) dflt).2) (tr.getD i dflt)) :
    bodyFrom tr P 0 = pieces (Vector.replicate 32 0) tr := by
  rw [bodyFrom, Nat.sub_zero, ← List.range_eq_range', hl, ra_pieces_eq]
  exact List.flatMap_congr fun i hi => h i (List.mem_range.mp hi)

/-! ## One entry -/

/-- The planned class agrees with the planned length (the length rule): `q₀` 7 bytes, a leaf one of
`leafLens` (`pX`'s rows), a node 64, an FS query none of these. -/
def raOk (e : PE) : Bool :=
  match e.k with
  | .q0 => e.len == 7
  | .fs _ => !(e.len == 7 || e.len == 64 || decide (e.len ∈ leafLens))
  | .leaf => decide (e.len ∈ leafLens)
  | .node .. => e.len == 64
  | .heap .. => false

theorem ra_contrib (tr : Trace) (i : ℕ) (e : PE) (prev : Digest) (hok : raOk e = true)
    (hlen : (bl (qOf tr i)).length = e.len) (hprev : e.len = 64 → prev = aOf tr (i - 1)) :
    contrib tr i e = piece prev (tr.getD i dflt) := by
  obtain ⟨k, len⟩ := e
  have hq : (tr.getD i dflt).1.data.toList = bl (qOf tr i) := rfl
  simp only at hlen hprev
  unfold piece
  rw [hq, hlen]
  cases k with
  | q0 =>
    simp only [raOk, beq_iff_eq] at hok
    subst hok
    rfl
  | fs st =>
    simp only [raOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not] at hok
    obtain ⟨⟨h7, h64⟩, hl⟩ := hok
    rw [ite_eq_right h7, ite_eq_right h64, ite_eq_right hl]
    rfl
  | leaf =>
    simp only [raOk, decide_eq_true_eq] at hok
    have h64 := ne64_of_leaf hok
    rw [ite_eq_right (by simp only [leafLens, List.mem_cons, List.not_mem_nil, or_false] at hok; (clear * - len tr i hok; omega)),
      ite_eq_right h64, ite_eq_left hok]
    rfl
  | heap pe h t path i0 m k cap => simp [raOk] at hok
  | node pe h j lvl cap =>
    simp only [raOk, beq_iff_eq] at hok
    rw [ite_eq_right (by (clear * - len tr i hok; omega)), ite_eq_left hok, hprev hok]
    rfl

/-! ## The static facts -/

/-- The plan has lengths `L`, and every class agrees with its length. -/
def raChk : List PE → List ℕ → Bool
  | [], [] => true
  | e :: P, l :: L => (e.len == l && raOk e) && raChk P L
  | _, _ => false

/-! The plan against the blocks: `planItems` and `itemBlks` walk the same items, so (when the walk's
static flag holds, `PlanOk`) the plan's lengths are the blocks' and every class agrees with its
length when every block is one the extractor reassembles (`blkOk`). Both facts are already decided
(`planOk_P20`, `blocks_ok`), so the kernel evaluates neither the 5,464-entry plan nor `lensL` here
(a `decide` took 10–14 s). -/

private theorem ra_chk_of : ∀ (P : List PE) (L : List ℕ), P.map PE.len = L → P.all raOk = true → raChk P L = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | e :: P, l :: L, h, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.all_cons, Bool.and_eq_true] at h2
    simp only [raChk, h.1, beq_self_eq_true, h2.1, Bool.and_self, Bool.true_and]
    exact ra_chk_of P L h.2 h2.2

private theorem ra_item_ok (p : Params) (w : WS) (it : Item) (h : (planItem p w it).2.ok = true) : w.ok = true := by
  cases it with
  | read m => exact h
  | readW m wd => exact h
  | cap c r => exact h
  | sample => exact h
  | positions r => simp only [planItem, Bool.and_eq_true] at h; exact h.1
  | opening r =>
    simp only [planItem] at h
    split at h
    · simp at h
    · split at h
      · simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1.1.1
      · simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1

private theorem ra_items_ok (p : Params) : ∀ (its : List Item) (w : WS), (planItems p w its).2.ok = true → w.ok = true
  | [], _, h => h
  | it :: its, w, h => ra_item_ok p w it (ra_items_ok p its _ h)

private theorem ra_ok_fs (st len : ℕ) (h : len != 64 && !decide (len ∈ leafLens)) (h32 : 32 ≤ len) :
    raOk ⟨.fs st, len⟩ = true := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  simp only [raOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    decide_eq_false_iff_not]
  exact ⟨⟨by (clear * - len h32; omega), h.1⟩, h.2⟩

private theorem ra_map_range {α : Type} (n : ℕ) (a : α) : (List.range n).map (fun _ => a) = List.replicate n a := by
  rw [List.map_const', List.length_range]

private theorem ra_flatMap_range {α : Type} (n : ℕ) (l : List α) :
    (List.range n).flatMap (fun _ => l) = (List.replicate n l).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatten_append]; simp

private theorem ra_flatMap_replicate {α β : Type} (m : ℕ) (b : α) (f : α → List β) :
    (List.replicate m b).flatMap f = (List.replicate m (f b)).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]

private theorem ra_pos_lens (m st i pend : ℕ) :
    ((List.range (m + 1)).map (fun k => if k = 0 then (⟨.fs st, 32 + pend⟩ : PE) else ⟨.fs (i + k - 1), 32⟩)).map
      PE.len = (32 + pend) :: List.replicate m 32 := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
  simp only [ite_true, Function.comp_def, Nat.succ_ne_zero, ite_false]
  rw [ra_map_range]

private theorem ra_pos_ok (m st i pend : ℕ) (h : blkOk (.one .fs (32 + pend)) = true) :
    ((List.range (m + 1)).map (fun k => if k = 0 then (⟨.fs st, 32 + pend⟩ : PE) else ⟨.fs (i + k - 1), 32⟩)).all
      raOk = true := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.all_cons]
  simp only [ite_true, Function.comp_def, Nat.succ_ne_zero, ite_false]
  rw [ra_ok_fs _ _ h (by (clear * - pend; omega)), Bool.true_and, List.all_map, List.all_eq_true]
  intro x _
  rfl

private theorem ra_open_lens (L : Level) (pe ce co : ℕ) :
    (openPlan L pe ce co).map PE.len = lensB (.opn L.t L.row L.path) := by
  simp only [openPlan, lensB, Blk.queries, List.map_flatMap, List.map_cons, List.map_map,
    Function.comp_def, ra_map_range, ra_flatMap_range, List.map_flatten, List.map_replicate]

private theorem ra_open_ok (L : Level) (pe ce co : ℕ) (h : blkOk (.opn L.t L.row L.path) = true) :
    (openPlan L pe ce co).all raOk = true := by
  simp only [openPlan, List.all_flatMap, List.all_cons, List.all_map, List.all_eq_true]
  intro j _
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨h, fun _ _ => rfl⟩

private theorem ra_plan_lens (p : Params) (hcp : p.capPrune = false) :
    ∀ (its : List Item) (w : WS), (planItems p w its).2.ok = true →
    (itemBlks p its w.pend).all blkOk = true →
    (planItems p w its).1.map PE.len = (itemBlks p its w.pend).flatMap lensB ∧
      (planItems p w its).1.all raOk = true
  | [], w, _, _ => ⟨rfl, rfl⟩
  | it :: its, w, hok, hb => by
    have hok' : (planItems p (planItem p w it).2 its).2.ok = true := hok
    have ih := ra_plan_lens p hcp its (planItem p w it).2 hok'
    have hstep := ra_items_ok p its _ hok'
    show ((planItem p w it).1 ++ (planItems p (planItem p w it).2 its).1).map PE.len = _ ∧
      ((planItem p w it).1 ++ (planItems p (planItem p w it).2 its).1).all raOk = true
    rw [List.map_append, List.all_append]
    cases it with
    | read m => exact ⟨(ih hb).1, (ih hb).2⟩
    | readW m wd => exact ⟨(ih hb).1, (ih hb).2⟩
    | cap c r => exact ⟨(ih hb).1, (ih hb).2⟩
    | sample =>
      have hb' : blkOk (.one .fs (32 + w.pend)) = true ∧ (itemBlks p its 0).all blkOk = true := by
        simpa only [itemBlks, List.all_cons, Bool.and_eq_true] using hb
      obtain ⟨h1, h2⟩ := ih hb'.2
      rw [h1, h2, Bool.and_true]
      exact ⟨rfl, show raOk ⟨.fs w.st, 32 + w.pend⟩ && true = true by rw [ra_ok_fs _ _ hb'.1 (by (clear * - w; omega))]; rfl⟩
    | positions r =>
      have hn : 1 ≤ (p.level r).nPosQ := by
        have : (w.ok && decide (1 ≤ (p.level r).nPosQ)) = true := hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      obtain ⟨m, hm⟩ : ∃ m, (p.level r).nPosQ = m + 1 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
      have hb' : blkOk (.one .fs (32 + w.pend)) = true ∧ (itemBlks p its 0).all blkOk = true := by
        simp only [itemBlks, List.all_cons, List.all_append, Bool.and_eq_true] at hb
        exact ⟨hb.1, hb.2.2⟩
      obtain ⟨h1, h2⟩ := ih hb'.2
      rw [h1, h2, Bool.and_true]
      have e1 : (planItem p w (.positions r)).1 = (List.range (m + 1)).map (fun k =>
          if k = 0 then (⟨.fs w.st, 32 + w.pend⟩ : PE) else ⟨.fs (w.i + k - 1), 32⟩) := by
        rw [← hm]; rfl
      have e2 : itemBlks p (.positions r :: its) w.pend =
          .one .fs (32 + w.pend) :: (List.replicate m (.one .fs 32) ++ itemBlks p its 0) := by
        rw [itemBlks, hm, Nat.add_sub_cancel]
      rw [e1, e2, ra_pos_lens, ra_pos_ok _ _ _ _ hb'.1]
      refine ⟨?_, rfl⟩
      rw [List.flatMap_cons, List.flatMap_append, ra_flatMap_replicate]
      simp only [lensB, Blk.queries, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      have e3 : ∀ k : ℕ, (List.replicate k [32]).flatten = List.replicate k 32 := fun k => by
        induction k with
        | zero => rfl
        | succ k ih => rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ih]; rfl
      rw [e3]
      rfl
    | opening r =>
      have hb' : blkOk (.opn (p.level r).t (p.level r).row (p.level r).path) = true ∧
          (itemBlks p its 0).all blkOk = true := by
        simpa only [itemBlks, Params.heapQ, hcp, Bool.false_eq_true, ↓reduceIte, List.replicate_zero, List.nil_append,
          List.all_cons, Bool.and_eq_true] using hb
      cases hc : w.caps.find? (·.1 == r) with
      | none =>
        have : (planItem p w (.opening r)).2.ok = false := by simp only [planItem, hc]
        rw [this] at hstep; exact absurd hstep (by decide)
      | some c =>
        obtain ⟨x, ce, co, nb⟩ := c
        have e1 : (planItem p w (.opening r)).1 = openPlan (p.level r) w.pe ce co := by
          simp only [planItem, hc, hcp, Bool.false_eq_true, ↓reduceIte]
        have e2 : (planItem p w (.opening r)).2.pend = 0 := by
          have h0 : (planItem p w (.opening r)).2.pend = w.pend := by
            simp only [planItem, hc, hcp, Bool.false_eq_true, ↓reduceIte]
          have h3 : (planItem p w (.opening r)).2.ok = true := hstep
          simp only [planItem, hc, hcp, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h3
          rw [h0]; exact h3.1.1.1.1.1.1.1.1.2
        have hb2 : (itemBlks p its (planItem p w (.opening r)).2.pend).all blkOk = true := by
          rw [e2]; exact hb'.2
        obtain ⟨h1, h2⟩ := ih hb2
        rw [h1, h2, Bool.and_true, e1, e2, ra_open_lens, ra_open_ok _ _ _ _ hb'.1]
        refine ⟨?_, rfl⟩
        simp only [itemBlks, List.flatMap_cons, Params.heapQ, hcp, Bool.false_eq_true, ↓reduceIte, List.replicate_zero,
          List.nil_append]

private theorem ra_plan_chk_of (p : Params) (hP : PlanOk p) (hb : (blocks p).all blkOk = true) :
    raChk (plan p) (7 :: (blocks p).flatMap lensB) = true := by
  rw [blocks, List.all_cons, Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := ra_plan_lens p hP.2.2.2 (schedule p) w0 hP.1 hb.2
  -- both goals are rewritten until they are `h1`, `h2` up to unfolding `planAll`/`w0` (left as `_ && _` or
  -- `[seedLen] ++ _`, the kernel unfolded `List.all`/`List.flatMap` over the walk of the schedule; GOLF-DEC2)
  have hw : w0.pend = 0 := rfl
  rw [hw] at h1
  refine ra_chk_of _ _ ?_ ?_
  · rw [plan, blocks, List.map_cons, List.map_cons, List.flatMap_cons]
    exact congrArg (7 :: ·) (congrArg (seedLenP p :: ·) h1)
  · rw [plan, List.all_cons, List.all_cons, ra_ok_fs 0 (seedLenP p) hb.1 (by
      rw [seedLenP_eq]; (clear * - p; omega))]
    exact h2

/-- **The plan at `pX`**: lengths `7 :: lensL` (`q₀`, then the extractor's), classes agreeing. -/
theorem ra_plan_chk : raChk (plan pX) (7 :: lensL) = true := ra_plan_chk_of pX planOk_P20 blocks_ok

theorem ra_chk_spec : ∀ (P : List PE) (L : List ℕ), raChk P L = true →
    P.length = L.length ∧ ∀ i < P.length, (P.getD i default).len = L.getD i 0 ∧ raOk (P.getD i default) = true
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by simp [raChk] at h
  | _ :: _, [], h => by simp [raChk] at h
  | e :: P, l :: L, h => by
    simp only [raChk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hl, hok⟩, hr⟩ := h
    obtain ⟨ih1, ih2⟩ := ra_chk_spec P L hr
    refine ⟨by simp [ih1], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨hl, hok⟩
    | succ i =>
      simp only [List.getD_cons_succ]
      exact ih2 i (by simpa using hi)

/-! ## The extractor's entries' lengths -/

theorem ra_walk_snd : ∀ (u : ℕ) (l : List ℕ), (walk u l).map Prod.snd = l
  | _, [] => rfl
  | u, len :: r => by simp [walk, ra_walk_snd _ r]

theorem ra_entL_snd : entL.map Prod.snd = lensL := ra_walk_snd 6 lensL

theorem ra_len_readTraceL (W : ℕ → Word) (i : ℕ) (hi : i < (readTraceL W).length) :
    (bl (qOf (readTraceL W) i)).length = (7 :: lensL).getD i 0 := by
  cases i with
  | zero =>
    simp only [bl, qOf, readTraceL, List.getD_cons_zero, q0Ent, bArr_data, List.length_drop,
      wordBytes_length]
  | succ k =>
    have hk : k < entL.length := by
      rw [readTraceL, List.length_cons, List.length_map] at hi; (clear * - k hi; omega)
    have e1 : (entL.map fun x => entAt W x.1 x.2).getD k dflt = entAt W entL[k].1 entL[k].2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    have e2 : lensL.getD k 0 = entL[k].2 := by
      rw [← ra_entL_snd, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    have hmem : entL[k].2 ∈ lensL := by
      rw [← ra_entL_snd]
      exact List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩
    have h8 := (List.all_eq_true.mp lensL_facts.2) _ hmem
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h8
    rw [List.getD_cons_succ, e2, bl, qOf, readTraceL, List.getD_cons_succ, e1]
    simp only [entAt, bArr_data, wordsBytes_length, length_wsAt]
    (clear * - k hk W h8; omega)

/-! ## The theorem -/

/-- **The extractor's reassembled proof is `V_S`'s**: on the trace read off the child's stream,
`reassembleL` (by query lengths, the compare rule) is WP-11b-QL's `reassemble` (by the plan). -/
theorem reassemble_readTraceL (W : ℕ → Word) :
    Lvm.Replay.reassemble pX (readTraceL W) = reassembleL (readTraceL W) := by
  obtain ⟨hl, hP⟩ := ra_chk_spec _ _ ra_plan_chk
  have hlt : (plan pX).length = (readTraceL W).length := by
    rw [hl, length_readTraceL, List.length_cons, lensL_facts.1]
  have hb : bodyFrom (readTraceL W) (plan pX) 0 = pieces (Vector.replicate 32 0) (readTraceL W) := by
    refine ra_body _ _ hlt fun i hi => ?_
    obtain ⟨hlen, hok⟩ := hP i (lt_of_lt_of_eq hi hlt.symm)
    refine ra_contrib _ i _ _ hok (by rw [ra_len_readTraceL W i hi, hlen]) fun h64 => ?_
    cases i with
    | zero => exact absurd (h64.symm.trans hlen) (by rw [List.getD_cons_zero]; decide)
    | succ i => rw [ite_eq_right (Nat.succ_ne_zero i), aOf]
  rw [Lvm.Replay.reassemble, reassembleL, bArr, hb, show hdr8 = header0 from rfl]

end Lvm.X
end
-- ===== end of `LvmXReasm` =====

/-!
# What the extractor returns (BLUEPRINT §6.2)

On an `S` proof (`π[0] = 'S'`, `|π| = piSize`):

* **`EX_leaf`** (`b = 0`, every log): `leafW π = leaf s n` from the header;
* (`b ≠ 0`, in the domain: the node branch at `S2GM` is M′'s `decXM`, R11-X's `LvmMPX*` modules; the `C_rec`
  node theorem `EX_node` was removed in roll 11 with the dead `C_rec` extractor);
* **`EX_node_out`** (`b ≠ 0`, outside the domain): the search under π's `vk`.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## The inputs of the decoder, as pure functions of π and the log -/

/-- Word `m` of a digest. -/
def dw (d : Digest) (m : ℕ) : Word := (packBytes d.toList).getD m 0

/-- A fold challenge from its chain answer: lanes 0–2 as an `E` element (`rdE`'s coordinates). -/
def alphaE (d : Digest) : BF64.Ext3 := mkE (wK (dw d 0)) (wK (dw d 1)) (wK (dw d 2))

/-! ## WP-5's bad events give no state hit -/

theorem notStateHit_of_notBad {L : Log} (h : ¬ Lvm.FS.Bad L) : ¬ StateHit L := by
  rintro ⟨i, j, hij, hj, hs⟩
  refine h (Or.inr (Or.inr ⟨i, j, hij, hj, ?_⟩))
  unfold stateIn at hs
  split_ifs at hs with hc
  refine ⟨hc.2, 0, hc.1, ?_⟩
  have e := (Option.some.inj hs).symm
  rw [e]
  apply Vector.ext
  intro k hk
  simp [Lvm.FS.win, Lvm.FS.dg, Lvm.FS.qb]

/-! ## The header fields: packed words and `V_S`'s byte reads -/

/-- **`hdD` is `V_S`'s `digestAt`** (`LvmDriver`) at the aligned offset `8j`. -/
theorem hdD_eq_digestAt (π : Proof) (j : ℕ) : hdD π j = digestAt π (8 * j) := by
  apply Vector.ext
  intro i hi
  simp only [hdD, digW, digestAt, Vector.getElem_ofFn]
  rw [← wordByte_eq_getD]
  have e : wordByte (wsAt (pw π) j 4) i = wordByte (packBytes π.data.toList) (8 * j + i) := by
    simp only [wordByte, wsAt, pw]
    rw [List.getD_eq_getElem _ _ (by simp; (clear * - i hi; omega)), List.getElem_map, List.getElem_range,
      show (8 * j + i) / 8 = j + i / 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - j i; omega)), show (8 * j + i) % 8 = i % 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - j i; omega))]
  rw [e, wordByte_packBytes]
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  first
    | rfl
    | (simp only [ByteArray.get!]; rfl)
    | (cases π; simp only [ByteArray.get!, getElem!_def]; split <;> simp_all <;> rfl)

/-! ## The parse on an `S` proof -/

theorem lowByte (w : Word) : (w &&& 0xFF).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and, show (0xFF : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The low byte of tape word 5 is the proof's first byte (FR `tape_byte0`). -/
theorem tape_byte0 (c : Digest) (π : Proof) (L : Log) {b : UInt8} (h0 : π.data[0]? = some b) :
    ((extractorInput c π L).getD 5 0).toNat % 256 = b.toNat := by
  have hpos : 0 < π.size := by
    rcases Nat.eq_zero_or_pos π.size with h | h
    · simp [ByteArray.size, Array.size_eq_zero_iff.mp h] at h0
    · exact h
  have := tape_getD_proof c π L (j := 0) (by (clear * - hpos; omega))
  rw [Nat.add_zero] at this
  rw [this]
  have hw := wordByte_packBytes π.data.toList 0
  simp only [wordByte, Nat.zero_div, Nat.zero_mod, pow_zero, Nat.div_one] at hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [packBytes_length, ← WitnessSending.size_eq_length]; (clear * - hpos; omega)), Option.getD_some] at hw
  have h1 : π.data.toList.getD 0 0 = b := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, h0, Option.getD_some]
  rw [h1] at hw
  rw [← hw, Nat.toUInt8_eq, UInt8.toNat_ofNat']

theorem parse_isK (pz : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I (parseIR pz) s).M rIsK = (if I.getD 5 0 &&& 0xFF = kindS then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIR, readAt, kindPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | (clear * - s hs; omega) | (simp only [size_set]; (clear * - s hs; omega))) [rd_set_self, rd_set_ne, XOp.eval]

/-! ## The leaf -/

theorem readAt_val (I : Array Word) (s : St) (hM : Inv s.M) {d pos : ℕ} (hd : d < regs) (hd4 : 4 ≤ d)
    (hda : d ≠ rA) (hp : pos < 2 ^ 64) :
    rd (semXIR I (readAt d pos) s).M d = I.getD pos 0 ∧
    (∀ y, y ≠ d → y ≠ rA → rd (semXIR I (readAt d pos) s).M y = rd s.M y) ∧
    Inv (semXIR I (readAt d pos) s).M ∧ (semXIR I (readAt d pos) s).M.size = s.M.size ∧
    (semXIR I (readAt d pos) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs hd
  refine ⟨rd_readAt I s hM hd hp, fun y h1 h2 => ?_, inv_sem I (by
    simp only [readAt, WF, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false, forall_eq, rA]
    exact ⟨by decide, hd4⟩) hM, size_sem .., rfl⟩
  simp only [readAt, semXIR, runPrims, List.foldl, Prim.run]
  rw [rd_set_ne (Ne.symm h1), rd_set_ne (Ne.symm h2)]

/-! ## The node -/

theorem hasOut_storesIR : ∀ (b : ℕ) (ws : List Word), hasOut (storesIR b ws) = false
  | _, [] => rfl
  | b, _ :: ws => by simp only [storesIR, hasOut, hasOut_storesIR (b + 1) ws, Bool.or_false]

/-- `hasOut` of a `seq`, as a rewrite (not an `rfl`-lemma: `simp` records the step, so the kernel
does not re-derive it by evaluating `hasOut` on the operands). -/
theorem hasOut_seq (p q : XIR) : hasOut (.seq p q) = (hasOut p || hasOut q) :=
  (rfl : hasOut (.seq p q) = _).trans rfl

theorem blk_const_val (I : Array Word) (s : St) (hM : Inv s.M) {d : ℕ} (hd : d < regs) (w : Word) :
    rd (semXIR I (.blk [.const d w]) s).M d = w := by
  have hs := hM.1
  rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
  exact rd_set_self (by (clear * - hd hs; omega))

theorem blk_const_ne (I : Array Word) (s : St) {d : ℕ} (w : Word) {y : ℕ} (hy : y ≠ d) :
    rd (semXIR I (.blk [.const d w]) s).M y = rd s.M y :=
  rd_blk_of_not_dst I _ s (by simp [Prim.dst]; exact Ne.symm hy)

theorem rdK_toBitVec (M : Mem) (a : ℕ) : BF64.toBitVec (rdK M a) = rd M a := rfl

theorem rdE_eq (M : Mem) (a : ℕ) : rdE M a = mkE (wK (rd M a)) (wK (rd M (a + 1))) (wK (rd M (a + 2))) := rfl

/-- One 3-word copy of the `α` copies. -/
theorem mcp3 (I : Array Word) (s : St) (hM : Inv s.M) (hsz : 2 ^ 25 ≤ s.M.size) {src dst : ℕ}
    (hd : regs ≤ dst) (hd2 : dst + 3 ≤ 2 ^ 24) (hsr : 2 ^ 24 ≤ src) (hsr2 : src + 3 ≤ 2 ^ 25) :
    (∀ i < 3, rd (semXIR I (mcpIR 3 src 1 dst) s).M (dst + i) = rd s.M (src + i)) ∧
    (∀ r, regs ≤ r → (r < dst ∨ dst + 3 ≤ r) → rd (semXIR I (mcpIR 3 src 1 dst) s).M r = rd s.M r) ∧
    Inv (semXIR I (mcpIR 3 src 1 dst) s).M ∧ (semXIR I (mcpIR 3 src 1 dst) s).M.size = s.M.size ∧
    (semXIR I (mcpIR 3 src 1 dst) s).o = s.o := by
  obtain ⟨a1, a2, a3⟩ := mcpIR_sem I s hM (n := 3) (src := src) (str := 1) (dst := dst) (by norm_num)
    (by (clear * - hsr hsr2; omega)) (by norm_num) hd (by (clear * - hd2; omega)) (by (clear * - hsz hd2; omega)) (fun i hi => .inr (by (clear * - hd2 hsr hsr2 hi; omega)))
    (fun i hi => by simp only [regs] at *; (clear * - hsr hsr2 hi; omega))
  exact ⟨fun i hi => by rw [a1 i hi, Nat.one_mul], a2, a3, size_sem .., sem_o I _ s rfl⟩

/-- **The `α₁` copies** (generic): three words of each of `n` chain answers. -/
theorem acp3IR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hsz : 2 ^ 25 ≤ s.M.size) {src dst : ℕ}
    (hd : regs ≤ dst) (hsr : 2 ^ 24 ≤ src) : ∀ n, dst + 3 * n ≤ 2 ^ 24 → src + 4 * n ≤ 2 ^ 25 →
    (∀ j < n, ∀ m < 3, rd (semXIR I (acp3IR src dst n) s).M (dst + 3 * j + m) = rd s.M (src + 4 * j + m)) ∧
    (∀ r, regs ≤ r → (r < dst ∨ dst + 3 * n ≤ r) → rd (semXIR I (acp3IR src dst n) s).M r = rd s.M r) ∧
    Inv (semXIR I (acp3IR src dst n) s).M ∧ (semXIR I (acp3IR src dst n) s).M.size = s.M.size ∧
    (semXIR I (acp3IR src dst n) s).o = s.o
  | 0, _, _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, hM, rfl, rfl⟩
  | n + 1, h1, h2 => by
    obtain ⟨p1, q1, i1, z1, o1⟩ := acp3IR_sem I s hM hsz hd hsr n (by (clear * - h1; omega)) (by (clear * - h2; omega))
    rw [acp3IR, semXIR_seq]
    generalize semXIR I (acp3IR src dst n) s = s1 at p1 q1 i1 z1 o1
    obtain ⟨p2, q2, i2, z2, o2⟩ := mcp3 I s1 i1 (by rw [z1]; exact hsz) (src := src + 4 * n)
      (dst := dst + 3 * n) (by (clear * - hd hsr h2; omega)) (by omega) (by (clear * - hsr; omega)) (by (clear * - h2; omega))
    refine ⟨fun j hj m hm => ?_, fun r hr h => ?_, i2, by rw [z2, z1], by rw [o2, o1]⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [q2 _ (by (clear * - hd hsr h2 hm hj; omega)) (.inl (by (clear * - hm hj; omega))), p1 j hj m hm]
      · rw [p2 m hm, q1 _ (by simp only [regs] at hd ⊢; (clear * - hd hsr hm h1 h2; omega)) (.inr (by (clear * - hsr hm h1 h2; omega)))]
    · rw [q2 r hr (by (clear * - hsr h2 h; omega)), q1 r hr (by (clear * - h; omega))]

/-! ## The `W` kind (FR `run_W_tape`, `run_W`, `E_W`) -/

theorem run_W_tape (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → ¬ (inp.toArray.getD 5 0 &&& 0xFF = kindS)) :
    extX.run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hd := decOk_decX
  have hwf := wf_extIRWith (pz := piSize pX) hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I (parseIR (piSize pX)) s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs _ I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)),
      piSize_eq] at this
    (clear * - this; omega)
  have hk' : a ≠ 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsK = 0 := fun h => by
    rw [parse_isK _ I s0 h0, if_neg (hk h)]
  have hpo : (semXIR I (parseIR (piSize pX)) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I (parseIR (piSize pX)) s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith (piSize pX) decX) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by (clear * - hlen hw; omega))) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith (piSize pX) decX) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith (piSize pX) decX) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by (clear * - ha hw; omega)), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith (piSize pX) decX) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **`EX` on a `W` proof** (first byte not `'S'`), on every log: `WitnessSending.decode π`. -/
theorem EX_W (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hW : π.data[0]? ≠ some 0x53) : EX A c π L = WitnessSending.decode π := by
  by_cases hD : InDomE c π L
  · rw [EX, if_pos hD, EdX]
    have hπ : π.size < 2 ^ 64 := by have := hD.1; rw [outCap] at this; (clear * - this; omega)
    have hrun := run_W_tape (extractorInput c π L) π.size hπ (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) (fun hne he => by
        obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
          rcases h : π.data[0]? with _ | b
          · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
          · exact ⟨b, rfl⟩
        have h1 := tape_byte0 c π L hb
        have h2 := congrArg BitVec.toNat he
        rw [lowByte, getD_toArray, h1] at h2
        exact hW (by rw [hb]; congr 1; exact UInt8.toNat_inj.mp h2))
    rw [Eden, ← den_of_run (by simp only [regs, memX]; norm_num) (wf_extIRWith decOk_decX.wf) hrun,
      WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [EX, if_neg hD, EoutX, if_neg hW]

/-- **The node witness with WP-11b-QL's `reassemble`** (`LvmReassemble`): the left child's proof is
`reassemble pX tr'` of its trace. -/
theorem Xwit_eq_replay (π : Proof) (w : ℕ → Word) : Xwit π w =
    .node (hdD π 6) (leafStmt (hdD π 15) (pw π 14).toNat)
      ⟨Lvm.Replay.reassemble pX (readTraceL (laneOf w)), readTraceL (laneOf w), sigOfF (sigCol w)⟩
      ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩ := by
  rw [Xwit, reassemble_readTraceL]

end Lvm.X
