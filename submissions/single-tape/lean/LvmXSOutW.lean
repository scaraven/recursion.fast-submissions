-- New for lvm2 E2F (E2F-L H1, 2026-11-13): the node output's words at a stage. Ports of `LvmXOut` (`readTraceL`'s
-- words, the reassembled proof's words and size), `LvmXOutSeg` (the segments' words, `readTraceL_congr`) and
-- `LvmXReasm` (the plan's reassembly on the extractor's trace) with `blocksS st` in place of `blocks pX`. The proof's
-- pieces are chosen by the query's CLASS (seed/FS message, leaf row, node sibling), as `blkPSeg` and `contrib` do,
-- not by its length (`LvmXOut.piece`, which needs `leafLens`): no leaf length enters, and an FS query of a leaf's or a
-- node's length (16-B `E2` scalars) is harmless.
import LvmXSOutIR

/-!
# The node output's words at a stage

* `qsLS st` (the queries after `q₀` with their classes), `walkC` (`walk` with the classes);
* **`trWordsS`**, `logWords_readTraceLS`, `segOut_trSegS`: the child's trace and its words;
* `pieceWC`, **`pWordsS`**, `segOut_pSegS`: the reassembled proof's words, by class;
* `plan_cls`: the plan's classes are the blocks' (`ra_plan_lens` by class); **`packBytes_reassembleS`**,
  **`size_reassembleS`**: the plan's reassembly (`reassembleS`, `LvmReassemble`) of the trace read off the stream;
* `readTraceLS_congr`: the trace reads the stream's lanes only; `segsS_ok`: the segments' static facts.
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X Lvm.Replay

/-! ## The queries with their classes -/

/-- **The queries after `q₀`** at a stage: class and length. -/
def qsLS (st : XStage) : List (QClass × ℕ) := (blocksS st).flatMap Blk.queries

/-- Lanes, classes and lengths of a run of entries from lane `u` (`walk` with the classes). -/
def walkC : ℕ → List (QClass × ℕ) → List (ℕ × QClass × ℕ)
  | _, [] => []
  | u, q :: r => (u, q) :: walkC (u + 5 + q.2 / 8) r

theorem walkC_map : ∀ (u : ℕ) (l : List (QClass × ℕ)),
    (walkC u l).map (fun x => (x.1, x.2.2)) = walk u (l.map Prod.snd)
  | _, [] => rfl
  | u, q :: r => by simp only [walkC, walk, List.map_cons, walkC_map _ r]

theorem walkC_snd : ∀ (u : ℕ) (l : List (QClass × ℕ)), (walkC u l).map (fun x => x.2) = l
  | _, [] => rfl
  | u, q :: r => by simp only [walkC, List.map_cons, walkC_snd _ r]

theorem lensLS_eq (st : XStage) : lensLS st = (qsLS st).map Prod.snd := by
  rw [lensLS, qsLS, List.map_flatMap]

theorem entLS_eq (st : XStage) : entLS st = (walkC 6 (qsLS st)).map fun x => (x.1, x.2.2) := by
  rw [entLS, lensLS_eq, walkC_map]

theorem walk_snd : ∀ (u : ℕ) (l : List ℕ), (walk u l).map Prod.snd = l
  | _, [] => rfl
  | u, len :: r => by simp only [walk, List.map_cons, walk_snd _ r]

theorem queries_length (b : Blk) : b.queries.length = b.count := by
  cases b with
  | one c len => rfl
  | opn t row path =>
    simp only [Blk.queries, Blk.count, List.length_flatten, List.map_replicate, List.sum_replicate,
      List.length_cons, List.length_replicate, smul_eq_mul]
    ring

theorem length_qsLS (st : XStage) : (qsLS st).length + 1 = qSS st := by
  rw [qsLS, List.length_flatMap, qSS]
  simp only [queries_length]
  exact Nat.add_comm _ _

theorem length_readTraceLS (st : XStage) (W : ℕ → Word) : (readTraceLS st W).length = qSS st := by
  rw [readTraceLS, List.length_cons, List.length_map, entLS, length_walk, lensLS_eq, List.length_map,
    length_qsLS]

/-! ## The static facts per block -/

/-- **A block of the stage** (decided per stage): a seed or FS query, or an opening; its lengths lane-aligned. -/
def blkOkS : Blk → Bool
  | .one .seed len | .one .fs len => len % 8 == 0
  | .opn _ row _ => row % 8 == 0
  | _ => false

/-- A query of a stage's block: lane-aligned, not `q₀`, a node query of 64 bytes. -/
def QryOkS (q : QClass × ℕ) : Prop := q.2 % 8 = 0 ∧ q.1 ≠ .q0 ∧ (q.1 = .node → q.2 = 64)

theorem qryOk_of_blk (b : Blk) (hb : blkOkS b = true) : ∀ q ∈ b.queries, QryOkS q := by
  cases b with
  | one c len =>
    intro q hq
    simp only [Blk.queries, List.mem_singleton] at hq
    subst hq
    cases c <;> simp_all [blkOkS, QryOkS]
  | opn t row path =>
    intro q hq
    simp only [blkOkS, beq_iff_eq] at hb
    simp only [Blk.queries, List.mem_flatten, List.mem_replicate] at hq
    obtain ⟨l, ⟨-, rfl⟩, hq⟩ := hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hb, nofun, nofun⟩
    · rw [(List.mem_replicate.mp hq).2]; exact ⟨rfl, nofun, fun _ => rfl⟩

theorem qryOk_qsLS (st : XStage) (hb : (blocksS st).all blkOkS = true) : ∀ q ∈ qsLS st, QryOkS q := by
  intro q hq
  obtain ⟨b, hb', hq⟩ := List.mem_flatMap.mp hq
  exact qryOk_of_blk b (List.all_eq_true.mp hb b hb') q hq

/-! ## The trace's words -/

/-- **The trace's output words** at a stage (`trWords`). -/
def trWordsS (st : XStage) (W : ℕ → Word) : List Word :=
  toWord (qSS st) :: (toWord 7 :: (W 1 >>> 8) :: wsAt W 2 4) ++ (entLS st).flatMap fun x => entW W x.1 x.2

/-- **The trace's output words** are `trWordsS` (`logWords_readTraceL`). -/
theorem logWords_readTraceLS (st : XStage) (hb : (blocksS st).all blkOkS = true) (W : ℕ → Word) :
    logWords (readTraceLS st W) = trWordsS st W := by
  have hal : ∀ x ∈ entLS st, x.2 % 8 = 0 := by
    intro x hx
    rw [entLS_eq, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hq : y.2 ∈ qsLS st := by
      rw [← walkC_snd 6 (qsLS st)]; exact List.mem_map_of_mem hy
    exact (qryOk_qsLS st hb _ hq).1
  rw [logWords, length_readTraceLS, readTraceLS, trWordsS]
  generalize entLS st = E at hal ⊢
  rw [List.flatMap_cons, entryWords_q0, List.flatMap_map,
    List.flatMap_congr fun x hx => entryWords_entAt W x.1 x.2 (hal x hx)]
  rfl

/-- **The trace's segment denotes the trace's words** (`segOut_trSegL`). -/
theorem segOut_trSegS (st : XStage) (W : ℕ → Word) (κ : Bool) : segOut W κ 0 (trSegS st) = trWordsS st W := by
  simp only [trSegS, segOut, segOut_blkTSegs, trWordsS, entLS, lensLS, wsAt, Nat.zero_add,
    List.cons_append, List.nil_append]
  rfl

/-! ## The proof's words, by class -/

/-- **An entry's contribution in lanes, by its class** (`pieceW`; `blkPSeg`'s): a seed or FS query its message, a
leaf its row, a node its compared sibling. -/
def pieceWC (W : ℕ → Word) (u : ℕ) : QClass → ℕ → List Word
  | .seed, len | .fs, len => wsAt W (u + 5) ((len - 32) / 8)
  | .leaf, len => wsAt W (u + 1) (len / 8)
  | .node, _ => sibWs W u
  | .q0, _ => []

/-- **The proof's output words** at a stage (without the length word; `pWords`). -/
def pWordsS (st : XStage) (W : ℕ → Word) : List Word :=
  toWord 0x53 :: (walkC 6 (qsLS st)).flatMap fun x => pieceWC W x.1 x.2.1 x.2.2

theorem walkC_append : ∀ (u : ℕ) (l₁ l₂ : List (QClass × ℕ)),
    walkC u (l₁ ++ l₂) = walkC u l₁ ++ walkC (u + lanesOf (l₁.map Prod.snd)) l₂
  | _, [], _ => by simp [lanesOf, walkC]
  | u, q :: r, l₂ => by
    simp only [List.cons_append, walkC, walkC_append _ r l₂, lanesOf, List.map_cons, List.sum_cons]
    congr 3; omega

theorem walkC_rep64 : ∀ (w path : ℕ),
    walkC w (List.replicate path (.node, 64)) = (List.range path).map fun h => (w + 13 * h, (.node, 64))
  | _, 0 => rfl
  | w, path + 1 => by
    rw [List.replicate_succ, walkC, walkC_rep64 _ path, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.mul_zero, Nat.add_zero]
    congr 1
    exact List.map_congr_left fun h _ => by simp only [Prod.mk.injEq, and_true]; omega

theorem walkC_reps (row path : ℕ) : ∀ (u t : ℕ),
    walkC u (List.replicate t ((.leaf, row) :: List.replicate path (.node, 64))).flatten =
      (List.range t).flatMap fun j => walkC (u + opS row path * j) ((.leaf, row) :: List.replicate path (.node, 64))
  | _, 0 => rfl
  | u, t + 1 => by
    have hl : lanesOf (((QClass.leaf, row) :: List.replicate path (QClass.node, 64)).map Prod.snd) = opS row path := by
      rw [List.map_cons, List.map_replicate, lanesOf_pos]
    rw [List.replicate_succ, List.flatten_cons, walkC_append, hl, walkC_reps row path _ t,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.mul_zero, Nat.add_zero]
    congr 1
    exact List.flatMap_congr fun j _ => by congr 1; rw [Nat.succ_eq_add_one]; ring

theorem segOut_blkPSegC (W : ℕ → Word) (κ : Bool) (b u : ℕ) (blk : Blk) (hb : blkOkS blk = true) :
    segOut W κ b (blkPSeg u blk) = (walkC (b + u) blk.queries).flatMap fun x => pieceWC W x.1 x.2.1 x.2.2 := by
  cases blk with
  | one c len =>
    cases c <;> simp only [blkOkS, reduceCtorEq] at hb <;>
    · simp only [blkPSeg, segOut, Blk.queries, walkC, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        pieceWC, wsAt, Nat.add_assoc]
  | opn t row path =>
    simp only [Blk.queries]
    rw [walkC_reps, List.flatMap_assoc]
    simp only [blkPSeg, segOut]
    refine List.flatMap_congr fun j _ => ?_
    rw [walkC, walkC_rep64, List.flatMap_cons, List.flatMap_map]
    generalize opS row path * j = A
    simp only [pieceWC, wsAt]
    congr 1
    · exact List.map_congr_left fun k _ => by congr 1; omega
    · refine List.flatMap_congr fun h _ => ?_
      rw [sibWs]
      simp only [wsAt]
      have e1 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) + 1 + k = b + u + A + 5 + row / 8 + 13 * h + 1 + k :=
        fun k => by omega
      have e2 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) - 4 + k = b + u + A + 5 + row / 8 + 13 * h - 4 + k :=
        fun k => by omega
      have e3 : ∀ k, b + A + 13 * h + (u + 5 + row / 8) + 5 + k = b + u + A + 5 + row / 8 + 13 * h + 5 + k :=
        fun k => by omega
      simp only [e1, e2, e3]
      exact if_congr Iff.rfl rfl rfl

theorem segOut_blkPSegsC (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ (u : ℕ) (bs : List Blk),
    bs.all blkOkS = true → segOut W κ b (blkPSegs u bs) =
      (walkC (b + u) (bs.flatMap Blk.queries)).flatMap fun x => pieceWC W x.1 x.2.1 x.2.2
  | _, [], _ => rfl
  | u, blk :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [blkPSegs, segOut, segOut_blkPSegC W κ b u blk h.1, segOut_blkPSegsC W κ b _ bs h.2,
      List.flatMap_cons, walkC_append, List.flatMap_append, lanes_eq, Nat.add_assoc]
    rfl

/-- **The proof's segment denotes the reassembled proof's words** (`segOut_pSegL`). -/
theorem segOut_pSegS (st : XStage) (hb : (blocksS st).all blkOkS = true) (W : ℕ → Word) (κ : Bool) :
    segOut W κ 0 (pSegS st) = pWordsS st W := by
  show [toWord 0x53] ++ segOut W κ 0 (blkPSegs 6 (blocksS st)) = _
  rw [segOut_blkPSegsC W κ 0 6 _ hb, Nat.zero_add, pWordsS, qsLS, List.singleton_append]

theorem segLen_blkPSegs (κ : Bool) : ∀ (u : ℕ) (bs : List Blk), segLen κ (blkPSegs u bs) = (bs.map blkPOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    have : segLen κ (blkPSeg u b) = blkPOutsL b := by
      rcases b with ⟨c, len⟩ | ⟨t, row, path⟩
      · cases c <;> rfl
      · rfl
    rw [blkPSegs, segLen, this, segLen_blkPSegs κ _ bs, List.map_cons, List.sum_cons]

theorem length_pWordsS (st : XStage) (hb : (blocksS st).all blkOkS = true) (W : ℕ → Word) :
    (pWordsS st W).length = 1 + ((blocksS st).map blkPOutsL).sum := by
  rw [← segOut_pSegS st hb W false, segOut_length, pSegS, segLen, segLen_blkPSegs]
  rfl

/-! ## The plan's reassembly, by class

`contrib` (`LvmReassemble`) picks an entry's bytes by its planned class; on the trace read off the stream the
classes are the blocks' (`planS_cls`), so the reassembled proof is `pWordsS`' bytes. -/

/-- An entry's contribution by class, after the previous answer `prev` (`contrib`'s rule). -/
def pieceC (prev : Digest) (c : QClass) (e : ByteArray × Digest) : List UInt8 :=
  match c with
  | .q0 => []
  | .seed | .fs => (bl e.1).drop 32
  | .leaf => bl e.1
  | .node => if (bl e.1).take 32 = prev.toList then (bl e.1).drop 32 else (bl e.1).take 32

/-- A planned entry's class. -/
def ekC : EK → QClass
  | .q0 => .q0
  | .fs _ => .fs
  | .leaf => .leaf
  | .node .. => .node

/-- A query's class as planned (the seed is an FS query). -/
def qcN : QClass → QClass
  | .seed => .fs
  | c => c

theorem pieceC_qcN (prev : Digest) (c : QClass) (e : ByteArray × Digest) : pieceC prev (qcN c) e = pieceC prev c e := by
  cases c <;> rfl

theorem contrib_eq (tr : Trace) (i : ℕ) (e : PE) :
    contrib tr i e = pieceC (aOf tr (i - 1)) (ekC e.k) (tr.getD i dflt) := by
  obtain ⟨k, len⟩ := e
  cases k <;> rfl

/-- The contributions of a trace's entries by the classes `cs`, each after the previous entry's answer. -/
def piecesC : Digest → List QClass → Trace → List UInt8
  | prev, c :: cs, e :: tr => pieceC prev c e ++ piecesC e.2 cs tr
  | _, _, _ => []

theorem piecesC_eq : ∀ (prev : Digest) (cs : List QClass) (tr : Trace), cs.length = tr.length →
    piecesC prev cs tr = (List.range tr.length).flatMap fun i =>
      pieceC (if i = 0 then prev else (tr.getD (i - 1) dflt).2) (cs.getD i .q0) (tr.getD i dflt)
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)
  | prev, c :: cs, e :: tr, h => by
    rw [piecesC, piecesC_eq e.2 cs tr (by simpa using h), List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, ite_true]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    cases i with
    | zero => rfl
    | succ i => simp

/-- The plan's body by class. -/
theorem bodyFrom_eq (tr : Trace) (P : List PE) (hl : P.length = tr.length) :
    bodyFrom tr P 0 = piecesC (aOf tr 0) (P.map fun e => ekC e.k) tr := by
  rw [bodyFrom, Nat.sub_zero, ← List.range_eq_range', hl, piecesC_eq _ _ _ (by rw [List.length_map, hl])]
  refine List.flatMap_congr fun i _ => ?_
  rw [contrib_eq, show (QClass.q0) = (fun e : PE => ekC e.k) default from rfl, List.getD_map]
  cases i <;> rfl

/-! ### The plan's classes are the blocks' -/

theorem planItem_ok (p : Params) (w : WS) (it : Item) (h : (planItem p w it).2.ok = true) : w.ok = true := by
  cases it with
  | readW m wd => exact h
  | read m => exact h
  | cap c r => exact h
  | sample => exact h
  | positions r => simp only [planItem, planItem, Bool.and_eq_true] at h; exact h.1
  | opening r =>
    simp only [planItem, planItem] at h
    split at h
    · simp at h
    · simp only [Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1

theorem planItems_ok (p : Params) : ∀ (its : List Item) (w : WS), (planItems p w its).2.ok = true → w.ok = true
  | [], _, h => h
  | it :: its, w, h => planItem_ok p w it (planItems_ok p its _ h)

theorem map_range_const {α : Type} (n : ℕ) (a : α) : (List.range n).map (fun _ => a) = List.replicate n a := by
  rw [List.map_const', List.length_range]

theorem flatMap_range_const {α : Type} (n : ℕ) (l : List α) :
    (List.range n).flatMap (fun _ => l) = (List.replicate n l).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatten_append]; simp

theorem flatMap_rep_fs {β : Type} (m : ℕ) (f : Blk → List β) :
    (List.replicate m (Blk.one .fs 32)).flatMap f = (List.replicate m (f (.one .fs 32))).flatten := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]

theorem flatten_rep_single {α : Type} (a : α) : ∀ m : ℕ, (List.replicate m [a]).flatten = List.replicate m a
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, flatten_rep_single a m]; rfl

/-- **The plan's entries are the blocks' queries** (class and length; `ra_plan_lens`), when the walk's static flag
holds. -/
theorem plan_ent (p : Params) : ∀ (its : List Item) (w : WS), (planItems p w its).2.ok = true →
    (planItems p w its).1.map (fun e => (ekC e.k, e.len)) =
      (itemBlks p its w.pend).flatMap fun b => b.queries.map fun q => (qcN q.1, q.2)
  | [], _, _ => rfl
  | it :: its, w, hok => by
    have hok' : (planItems p (planItem p w it).2 its).2.ok = true := hok
    have ih := plan_ent p its (planItem p w it).2 hok'
    have hstep := planItems_ok p its _ hok'
    show ((planItem p w it).1 ++ (planItems p (planItem p w it).2 its).1).map _ = _
    rw [List.map_append, ih]
    cases it with
    | readW m wd => rfl
    | read m => rfl
    | cap c r => rfl
    | sample => rfl
    | positions r =>
      have hn : 1 ≤ (p.level r).nPosQ := by
        have : (w.ok && decide (1 ≤ (p.level r).nPosQ)) = true := hstep
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      obtain ⟨m, hm⟩ : ∃ m, (p.level r).nPosQ = m + 1 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
      have e1 : ((planItem p w (.positions r)).1).map (fun e => (ekC e.k, e.len)) =
          (QClass.fs, 32 + w.pend) :: List.replicate m (QClass.fs, 32) := by
        show ((List.range (p.level r).nPosQ).map _).map _ = _
        rw [hm, List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
        simp only [Function.comp_def, ↓reduceIte, Nat.add_one_ne_zero, ekC, map_range_const]
      have e2 : itemBlks p (.positions r :: its) w.pend =
          .one .fs (32 + w.pend) :: (List.replicate m (.one .fs 32) ++ itemBlks p its 0) := by
        rw [itemBlks, hm, Nat.add_sub_cancel]
      rw [e1, e2, List.flatMap_cons, List.flatMap_append, flatMap_rep_fs,
        show (planItem p w (.positions r)).2.pend = 0 from rfl]
      simp only [Blk.queries, List.map_cons, List.map_nil, qcN, flatten_rep_single, List.cons_append,
        List.nil_append]
    | opening r =>
      cases hc : w.caps.find? (·.1 == r) with
      | none =>
        have : (planItem p w (.opening r)).2.ok = false := by
          simp only [planItem, planItem, hc]
        rw [this] at hstep; exact absurd hstep (by decide)
      | some c =>
        obtain ⟨x, ce, co, nb⟩ := c
        have e1 : (planItem p w (.opening r)).1 = openPlan (p.level r) w.pe ce co := by
          simp only [planItem, planItem, hc]
        have e2 : (planItem p w (.opening r)).2.pend = 0 := by
          have h0 : (planItem p w (.opening r)).2.pend = w.pend := by simp only [planItem, planItem, hc]
          have h3 : (planItem p w (.opening r)).2.ok = true := hstep
          simp only [planItem, planItem, hc, Bool.and_eq_true, beq_iff_eq] at h3
          rw [h0]; exact h3.1.1.1.1.1.1.1.1.2
        rw [e1, e2, itemBlks, List.flatMap_cons]
        congr 1
        simp only [openPlan, Blk.queries, List.map_flatMap, List.map_cons, List.map_map, Function.comp_def,
          ekC, qcN, map_range_const, flatMap_range_const, List.map_flatten, List.map_replicate]

/-- **The plan's classes are the blocks'** (`plan_ent`'s first components). -/
theorem plan_cls (p : Params) (its : List Item) (w : WS) (hok : (planItems p w its).2.ok = true) :
    (planItems p w its).1.map (fun e => ekC e.k) =
      (itemBlks p its w.pend).flatMap fun b => b.queries.map fun q => qcN q.1 := by
  have h := congrArg (List.map Prod.fst) (plan_ent p its w hok)
  simpa only [List.map_map, List.map_flatMap, Function.comp_def] using h

/-- **The plan's lengths are the blocks'** (`plan_ent`'s second components). -/
theorem plan_lens (p : Params) (its : List Item) (w : WS) (hok : (planItems p w its).2.ok = true) :
    (planItems p w its).1.map PE.len = (itemBlks p its w.pend).flatMap fun b => b.queries.map Prod.snd := by
  have h := congrArg (List.map Prod.snd) (plan_ent p its w hok)
  simpa only [List.map_map, List.map_flatMap, Function.comp_def] using h

/-- **The plan's classes at a stage**: `q₀`, then the blocks' queries' (the seed an FS query). -/
theorem planS_cls (st : XStage) (hP : (planItems st.p w0 st.items).2.ok = true) :
    (planS st).map (fun e => ekC e.k) = .q0 :: (qsLS st).map fun q => qcN q.1 := by
  rw [show planS st = ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP st.p⟩ :: (planItems st.p w0 st.items).1 from rfl, List.map_cons,
    List.map_cons, plan_cls _ _ _ hP, qsLS,
    show blocksS st = .one .seed (seedLenP st.p) :: itemBlks st.p st.items 0 from rfl, List.flatMap_cons,
    List.map_append, List.map_flatMap]
  rfl

/-! ### The reassembled proof -/

theorem pieceC_entAt (W : ℕ → Word) {u : ℕ} {q : QClass × ℕ} (hq : QryOkS q) :
    pieceC (digW (wsAt W (u - 4) 4)) q.1 (entAt W u q.2) = wordsBytes (pieceWC W u q.1 q.2) := by
  obtain ⟨c, len⟩ := q
  obtain ⟨h8, -, h64⟩ := hq
  simp only at h8 h64
  have hb : bl (entAt W u len).1 = wordsBytes (wsAt W (u + 1) (len / 8)) := rfl
  have hd : ∀ n, (wordsBytes (wsAt W (u + 1) n)).drop 32 = wordsBytes (wsAt W (u + 5) (n - 4)) := fun n => by
    rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_drop, wsAt_drop]
  cases c with
  | q0 => rfl
  | seed | fs =>
    simp only [pieceC, pieceWC, hb, hd]
    congr 3; omega
  | leaf => rfl
  | node =>
    obtain rfl := h64 rfl
    have t1 : (wordsBytes (wsAt W (u + 1) (64 / 8))).take 32 = wordsBytes (wsAt W (u + 1) 4) := by
      rw [show (32 : ℕ) = 8 * 4 from rfl, wordsBytes_take, wsAt_take _ _ _ _ (by norm_num)]
    simp only [pieceC, pieceWC, hb, hd, t1, digW_toList (length_wsAt _ _ _), sibWs]
    by_cases he : wsAt W (u + 1) 4 = wsAt W (u - 4) 4
    · rw [ite_eq_left (by rw [he]), ite_eq_left he]
    · rw [ite_eq_right (fun h => he (wordsBytes_inj h)), ite_eq_right he]

theorem piecesC_walk (W : ℕ → Word) : ∀ (l : List (QClass × ℕ)) (u : ℕ), 4 ≤ u → (∀ q ∈ l, QryOkS q) →
    piecesC (digW (wsAt W (u - 4) 4)) (l.map fun q => qcN q.1) ((walkC u l).map fun x => entAt W x.1 x.2.2) =
      wordsBytes ((walkC u l).flatMap fun x => pieceWC W x.1 x.2.1 x.2.2)
  | [], _, _, _ => rfl
  | q :: r, u, hu, hq => by
    simp only [walkC, List.map_cons, piecesC, List.flatMap_cons, wordsBytes_append]
    rw [pieceC_qcN, pieceC_entAt W (hq q List.mem_cons_self)]
    congr 1
    have e : (entAt W u q.2).2 = digW (wsAt W (u + 5 + q.2 / 8 - 4) 4) := by
      rw [entAt, show u + 5 + q.2 / 8 - 4 = u + 1 + q.2 / 8 by omega]
    rw [e]
    exact piecesC_walk W r _ (by omega) fun y hy => hq y (List.mem_cons_of_mem _ hy)

theorem length_planS (st : XStage) (hP : (planItems st.p w0 st.items).2.ok = true) (W : ℕ → Word) :
    (planS st).length = (readTraceLS st W).length := by
  have := congrArg List.length (planS_cls st hP)
  rw [List.length_map, List.length_cons, List.length_map] at this
  rw [this, length_readTraceLS, length_qsLS]

/-- **The proof's bytes** are `pWordsS`' bytes (`reassembleL_data`, with `reassemble_readTraceL`). -/
theorem reassembleS_data (st : XStage) (hP : (planItems st.p w0 st.items).2.ok = true)
    (hb : (blocksS st).all blkOkS = true) (W : ℕ → Word) :
    (reassembleS st (readTraceLS st W)).data.toList = wordsBytes (pWordsS st W) := by
  have hw := piecesC_walk W (qsLS st) 6 (by norm_num) (qryOk_qsLS st hb)
  have e1 : (readTraceLS st W) = q0Ent W :: (walkC 6 (qsLS st)).map fun x => entAt W x.1 x.2.2 := by
    rw [readTraceLS, entLS_eq, List.map_map]; rfl
  rw [show reassembleS st (readTraceLS st W) = ⟨(hdr8 ++ bodyFrom (readTraceLS st W) (planS st) 0).toArray⟩ from rfl,
    bodyFrom_eq _ _ (length_planS st hP W), planS_cls st hP, e1, piecesC,
    show (q0Ent W).2 = digW (wsAt W (6 - 4) 4) from rfl, hw]
  show hdr8 ++ ([] ++ _) = _
  rw [List.nil_append, show hdr8 = header0 from rfl, header0_eq]
  rfl

/-- **The proof's packed words** are `pWordsS`. -/
theorem packBytes_reassembleS (st : XStage) (hP : (planItems st.p w0 st.items).2.ok = true)
    (hb : (blocksS st).all blkOkS = true) (W : ℕ → Word) :
    packBytes (reassembleS st (readTraceLS st W)).data.toList = pWordsS st W := by
  rw [reassembleS_data st hP hb, packBytes_wordsBytes]

/-- **The reassembled proof has `8 + 8 Σ blkPOutsL` bytes.** -/
theorem size_reassembleS (st : XStage) (hP : (planItems st.p w0 st.items).2.ok = true)
    (hb : (blocksS st).all blkOkS = true) (W : ℕ → Word) :
    (reassembleS st (readTraceLS st W)).size = 8 + 8 * ((blocksS st).map blkPOutsL).sum := by
  rw [ByteArray.size, ← Array.length_toList, reassembleS_data st hP hb, wordsBytes_length, length_pWordsS st hb]
  ring

/-! ## The trace reads the stream's lanes only -/

theorem lanesOf_flatMapB : ∀ bs : List Blk, lanesOf (bs.flatMap lensB) = (bs.map Blk.lanes).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← lanesOf_flatMapB bs, lanes_eq]
    simp only [lanesOf, List.map_append, List.sum_append]

/-- **The trace reads lanes below `6 + Σ lanes` only** (`readTraceL_congr`). -/
theorem readTraceLS_congr (st : XStage) {W W' : ℕ → Word}
    (h : ∀ v < 6 + ((blocksS st).map Blk.lanes).sum, W v = W' v) : readTraceLS st W = readTraceLS st W' := by
  have hT : lanesOf (lensLS st) = ((blocksS st).map Blk.lanes).sum := lanesOf_flatMapB _
  have h6 : ∀ v < 6, W v = W' v := fun v hv => h v (by omega)
  have hq : q0Ent W = q0Ent W' := by
    have e : wsAt W 2 4 = wsAt W' 2 4 := List.map_congr_left fun j hj => h6 _ (by simp at hj; omega)
    simp only [q0Ent, e, h6 1 (by norm_num)]
  unfold readTraceLS
  rw [hq]
  refine congrArg _ (List.map_congr_left fun x hx => entAt_congr fun v hv => h v ?_)
  have := walk_lt 6 (lensLS st) x hx
  omega

/-! ## The segments' static facts -/

theorem okSeg_blkTSegS (u : ℕ) (b : Blk) : okSeg (blkTSeg u b) = okSeg (blkTSeg 0 b) := by
  cases b <;> simp [blkTSeg, okSeg]

theorem okSeg_blkPSegS (u : ℕ) (b : Blk) : okSeg (blkPSeg u b) = okSeg (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> simp [blkPSeg, okSeg]
  | opn t row path =>
    simp only [blkPSeg, okSeg]
    rw [decide_eq_true (by omega : 4 ≤ u + 5 + row / 8), decide_eq_true (by omega : 4 ≤ 5 + row / 8)]

theorem okSeg_blkTSegsS : ∀ (u : ℕ) (bs : List Blk), okSeg (blkTSegs u bs) = bs.all fun b => okSeg (blkTSeg 0 b)
  | _, [] => rfl
  | u, b :: bs => by rw [blkTSegs, okSeg, okSeg_blkTSegS, okSeg_blkTSegsS _ bs, List.all_cons]

theorem okSeg_blkPSegsS : ∀ (u : ℕ) (bs : List Blk), okSeg (blkPSegs u bs) = bs.all fun b => okSeg (blkPSeg 0 b)
  | _, [] => rfl
  | u, b :: bs => by rw [blkPSegs, okSeg, okSeg_blkPSegS, okSeg_blkPSegsS _ bs, List.all_cons]

theorem depthSeg_blkTSegsS : ∀ (u : ℕ) (bs : List Blk), depthSeg (blkTSegs u bs) ≤ 2
  | _, [] => by simp [blkTSegs, depthSeg]
  | u, b :: bs => by
    rw [blkTSegs, depthSeg]
    refine max_le ?_ (depthSeg_blkTSegsS _ bs)
    cases b <;> simp [blkTSeg, depthSeg]

theorem depthSeg_blkPSegsS : ∀ (u : ℕ) (bs : List Blk), depthSeg (blkPSegs u bs) ≤ 2
  | _, [] => by simp [blkPSegs, depthSeg]
  | u, b :: bs => by
    rw [blkPSegs, depthSeg]
    refine max_le ?_ (depthSeg_blkPSegsS _ bs)
    cases b with
    | one c len => cases c <;> simp [blkPSeg, depthSeg]
    | opn t row path => simp [blkPSeg, depthSeg]

/-- **The segments' static facts** at a stage (`segs_ok`), from the blocks' `okSeg`s. -/
theorem segsS_ok (st : XStage) (h : (blocksS st).all (fun b => okSeg (blkTSeg 0 b) && okSeg (blkPSeg 0 b)) = true) :
    okSeg (trSegS st) = true ∧ depthSeg (trSegS st) ≤ 2 ∧ okSeg (pSegS st) = true ∧ depthSeg (pSegS st) ≤ 2 := by
  have h' := List.all_eq_true.mp h
  simp only [Bool.and_eq_true] at h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [trSegS, okSeg, okSeg_blkTSegsS, Bool.and_eq_true, List.all_eq_true]
    exact ⟨trivial, trivial, trivial, by decide, fun b hb => (h' b hb).1⟩
  · simp only [trSegS, depthSeg]
    simpa using depthSeg_blkTSegsS 6 (blocksS st)
  · simp only [pSegS, okSeg, okSeg_blkPSegsS, Bool.and_eq_true, List.all_eq_true]
    exact ⟨trivial, fun b hb => (h' b hb).2⟩
  · simp only [pSegS, depthSeg]
    simpa using depthSeg_blkPSegsS 6 (blocksS st)

end Lvm.XS
