-- New for `flock-recursive` (stage S-N2): the controls of `FRNodeSound4`, `FRNodeRead4`, `FRNodeRead4W`,
-- `FRNodeSound4R` and `FRNodeSound4K`.
import FRNodeSound4K

/-!
# Controls for the 4.1 slot interface, its reader and the gaps

| Definition | (+) | (−) |
|---|---|---|
| `SelN`/`SelS` | `selN_ctl`: `N4`'s slot 0 with its `L32` copy set selects `N4` | `selN_neg`: `N8` has no previous-node slot; `N4`'s slot 0 is no segment slot |
| `SlotImp` | `slotImp_idle`: a slot that selects no index owes nothing | `slotImp_stmt`: at a selected index a false statement fact fails it |
| `kAct` | `kAct_ctl`: active, active, inactive gives `2` | `kAct_ctl`: not `3` |
| `aggPf` | `aggPf_kind`: `π_A` is an aggregate (`'A'`), with the circuit's `k` (`kA_rd4`) | — |
| `WfAt` | `wfAt_ctl`: a squeeze's length word `enc64 40` | `wfAt_ctl`: zero bytes are not a length word |
| `I4`, `Gap4` | `ks_rev4H` (used); `I4_rows`; **`gap4_of_resid`**: on `StmtN4`, `NodeResid4` gives `Gap4` (with `resid4_of`, `Gap4` asks exactly what `NodeResid4` asks beyond the rows and the reader) | `gap4_kindN`: a previous-node proof whose byte 0 is not the selected kind's has no `Gap4` |
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-- (−) An `N8` node has no previous-node slot, and `N4`'s slot 0 is not a segment slot. -/
theorem selN_neg (w : Asg) (κ' : NodeKind) (κs : SegKind) : ¬ SelN .N8 0 w κ' ∧ ¬ SelS .N4 0 w κs :=
  ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide)⟩

/-- The assignment with `N4`'s `one` and slot 0's `L32` selector copy set. -/
def wSel : Asg := fun c => if c = NodeKind.N4.oneCell ∨ c = NodeKind.N4.oneCell + selR 0 .L32 then 1 else 0

/-- (+) `N4`'s slot 0, its `L32` copy set, selects the node kind `N4` (`nodeAt .L32`). -/
theorem selN_ctl : SelN .N4 0 wSel .N4 := by
  refine ⟨rfl, .L32, rfl, ?_, fun ι => ?_⟩
  · simp [protoP, oneR, slotAsg, mvC, protoOf, isPrevSlot, wSel, Lin.ev_cell]
  · cases ι <;> simp [protoP, selR, selIx, slotAsg, mvC, protoOf, isPrevSlot, wSel, Lin.ev_cell,
      NodeKind.hasPrev] <;> omega

/-- (+) A slot whose selectors pick no index owes nothing (an inactive sub-slot). -/
theorem slotImp_idle (impl₀ : OpImpl) (base : NodeKind → OpImpl) (κ : NodeKind) (v : ℕ) (w : Asg)
    (inp : Input) (tr : Trace) (h : ∀ ι, ¬ SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι) :
    SlotImp impl₀ base κ v w inp tr := fun ι hι => absurd hι (h ι)

/-- (−) At a selected index, a false statement fact fails `SlotImp` (it is not vacuous). -/
theorem slotImp_stmt {impl₀ : OpImpl} {base : NodeKind → OpImpl} {κ : NodeKind} {v : ℕ} {w : Asg}
    {inp : Input} {tr : Trace} {ι : Kind} (hι : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι)
    (hs : stmtOk4 seq4 (kindP (protoOf κ v) ι) inp = false) : ¬ SlotImp impl₀ base κ v w inp tr :=
  fun h => by rw [(h ι hι).2] at hs; exact Bool.noConfusion hs

/-- (+/−) An aggregate whose sub-slots are active, active, inactive has `k = 2` (not `3`). -/
theorem kAct_ctl (w : Asg) (h0 : (selSum .N4 (N4c.sub .N4 0 0)).ev w = 1)
    (h1 : (selSum .N4 (N4c.sub .N4 0 1)).ev w = 1) (h2 : (selSum .N4 (N4c.sub .N4 0 2)).ev w = 0) :
    kAct .N4 0 w = 2 ∧ kAct .N4 0 w ≠ 3 := by
  classical
  have : kAct .N4 0 w = 2 := by
    unfold kAct
    rw [Nat.find_eq_iff]
    refine ⟨Or.inr (by rw [h2]; exact zero_ne_one), fun n hn => ?_⟩
    interval_cases n
    · rintro (h | h)
      · exact absurd h (by decide)
      · exact h h0
    · rintro (h | h)
      · exact absurd h (by decide)
      · exact h h1
  exact ⟨this, by omega⟩

/-- (+) The read `π_A` is an aggregate leaf: its byte 0 is `'A'`. -/
theorem aggPf_kind (pf : Trace → Proof) (κ : NodeKind) (a : ℕ) (w : Asg) : kindOf4 (aggPf pf κ a w) = .agg := by
  have h : byteAt (aggPf pf κ a w) 0 = aggByte := by simp [aggPf, aggHdr]
  unfold kindOf4; dsimp only; rw [if_pos h]

/-- (+/−) `WfAt`: a squeeze's 80 bytes with the length word `enc64 40` pass; 80 zero bytes do not. -/
theorem wfAt_ctl : WfAt (enc64 40 ++ List.replicate 72 0) 0 [.squeeze] ∧
    ¬ WfAt (List.replicate 80 0) 0 [.squeeze] := by
  refine ⟨⟨by decide, trivial⟩, fun h => absurd h.1 (by decide)⟩

/-- (−) `Gap4` binds the previous node's kind byte: if slot 0 selects `ι` and the read proof's byte 0
is not `nodeAt ι`'s, there is no `Gap4`. -/
theorem gap4_kindN {impl₀ : OpImpl} {base : NodeKind → OpImpl} {pf : Trace → Proof} {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} (hp : κ.hasPrev = true) {ι : Kind}
    (hι : SelOk (slotAsg κ 0 w) (protoP 0) ι) (hb : byteAt ((rd4 pf).sgn κ 0 w).π 0 ≠ (nodeAt ι).byte) :
    ¬ Gap4 impl₀ base pf κ vk c₁ c₂ w := fun h => hb (h.kindN hp ι hι)

/-! ## `Gap4` asks no more than `NodeResid4` (the converse of `resid4_of`) -/

theorem selOk_unique {w : Asg} {P : Params} {ι ι' : Kind} (h : SelOk w P ι) (h' : SelOk w P ι') : ι = ι' := by
  by_contra hne
  have a := h.2 ι'
  rw [h'.2 ι', if_pos rfl, if_neg (Ne.symm hne)] at a
  exact one_ne_zero a

theorem nodeKind_ofByte?_eq {b : UInt8} {ν : NodeKind} (h : NodeKind.ofByte? b = some ν) : b = ν.byte := by
  unfold NodeKind.ofByte? at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> assumption

theorem segKind_ofByte?_eq {b : UInt8} {κ : SegKind} (h : SegKind.ofByte? b = some κ) : b = κ.byte := by
  unfold SegKind.ofByte? at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> assumption

theorem byte_of_kindOf4 {π : Proof} {ν : NodeKind} (h : kindOf4 π = .node ν) : byteAt π 0 = ν.byte := by
  unfold kindOf4 at h; dsimp only at h
  by_cases ha : byteAt π 0 = aggByte
  · rw [if_pos ha] at h; cases h
  · rw [if_neg ha] at h
    cases hκ : NodeKind.ofByte? (byteAt π 0) with
    | none => rw [hκ] at h; dsimp only at h; split_ifs at h
    | some κ =>
      rw [hκ] at h; dsimp only at h; split_ifs at h
      cases h; exact nodeKind_ofByte?_eq hκ

theorem byte_of_segView {π : Proof} {v : SegView} (h : segView π = some v) : byteAt π 0 = v.kind.byte := by
  unfold segView at h
  obtain ⟨κ, hκ, rfl⟩ := Option.map_eq_some_iff.1 h
  exact segKind_ofByte?_eq hκ

theorem readItems_sizes (B : List UInt8) : ∀ (its : List Item) (o : ℕ), o + slenS its ≤ B.length →
    (Read.readItems B o its).map (fun e => e.1.size) = its.map Item.qlen
  | [], _, _ => rfl
  | it :: its, o, hl => by
    have hs : slenS (it :: its) = it.slen + slenS its := by simp [slenS]
    have hsl : it.slen = 8 + it.qlen + 32 := rfl
    rw [hs] at hl
    rw [Read.readItems, List.map_cons, List.map_cons, readItems_sizes B its _ (by omega)]
    congr 1
    show ((B.drop (o + 8)).take it.qlen).toArray.size = _
    rw [List.size_toArray, List.length_take, List.length_drop]; omega

theorem traceBytes_length_of {tr : Trace} {its : List Item} (h : tr.map (fun e => e.1.size) = its.map Item.qlen) :
    (traceBytes tr).length = slenS its := by
  induction its generalizing tr with
  | nil => cases tr <;> simp_all [traceBytes, slenS]
  | cons it its ih =>
    cases tr with
    | nil => simp at h
    | cons e tr =>
      simp only [List.map_cons, List.cons.injEq] at h
      have := ih h.2
      simp only [slenS, List.map_cons, List.sum_cons] at this ⊢
      rw [Read.traceBytes_cons', List.length_append, this]
      have he : e.1.data.toList.length = it.qlen := by rw [← h.1, Array.length_toList]; rfl
      simp only [List.length_append, enc64_length, Vector.length_toList, he, Item.slen]

theorem wfAt_of_take (B : List UInt8) : ∀ (its : List Item) (tr : Trace) (o : ℕ),
    tr.map (fun e => e.1.size) = its.map Item.qlen → o + slenS its ≤ B.length →
    (B.drop o).take (slenS its) = traceBytes tr → WfAt B o its
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, h, _, _ => by simp at h
  | it :: its, e :: tr, o, h, hl, ht => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hs : slenS (it :: its) = it.slen + slenS its := by simp [slenS]
    have hsl : it.slen = 8 + it.qlen + 32 := rfl
    rw [hs] at hl ht
    rw [List.take_add, List.drop_drop, Read.traceBytes_cons'] at ht
    have hd : e.1.data.toList.length = e.1.size := by rw [Array.length_toList]; rfl
    have hlen : ((B.drop o).take it.slen).length = (enc64 e.1.size ++ e.1.data.toList ++ e.2.toList).length := by
      rw [List.length_take, List.length_drop, List.length_append, List.length_append, enc64_length, hd,
        Vector.length_toList, h.1]
      omega
    obtain ⟨h1, h2⟩ := List.append_inj ht hlen
    refine ⟨?_, wfAt_of_take B its tr _ h.2 (by omega) h2⟩
    have : ((B.drop o).take it.slen).take 8 = (B.drop o).take 8 := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [← this, h1, List.append_assoc, List.take_left' (enc64_length _), h.1]

/-- The reader's trace of signed child `σ` is `V_A`'s trace of its stream's segments read at their
offsets (R-A′: the spacer entries between them; one segment and no spacer for a previous node). -/
theorem sgn4_tr (pf : Trace → Proof) {κ : NodeKind} {σ : ℕ} (hσ : σ < 2) (w : Asg) :
    ((rd4 pf).sgn κ σ w).tr = aggTrace
      (fun i => spAnsB (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128))
      ((List.range (nSeg κ σ w)).map fun i =>
        Read.readItems (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB) (itemsOf seq4)) := by
  by_cases hA : N4c.isAgg κ σ = true
  · obtain ⟨ha, hc⟩ := N4c.agg_of_isAgg κ hσ hA
    have hk : N4c.kOf (rd4 pf) κ w σ = kAct κ (N4c.aggOf κ σ) w := by
      rw [N4c.kOf, if_pos hA, kA_rd4 pf κ ha]
    rw [nSeg, if_pos hA, hk]
    show (sgn4 pf κ σ w).tr = _
    conv_lhs => rw [← hc]
    rw [sgn4_agg pf κ ha]
    dsimp only
    rw [hc]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [slotTr4_sub κ ha (lt_of_lt_of_le (List.mem_range.1 hi) (kAct_le κ _ w)) w, hc]
    rfl
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      cases κ <;> simp_all [N4c.isAgg, NodeKind.hasPrev]
    obtain ⟨hp, rfl⟩ := hp
    rw [nSeg, if_neg hA, N4c.kOf, if_neg hA]
    simp only [rd4, sgn4, if_neg hA, slotTr4, isPrevSlot, hp, Bool.true_and, beq_self_eq_true, if_true,
      List.range_one, List.map_cons, List.map_nil, aggTrace, aggTrAt, List.nil_append, List.append_nil,
      zero_mul, add_zero]
    rfl

theorem chain_len (pf : Trace → Proof) {κ : NodeKind} {σ : ℕ} (hσ : σ < 2) (w : Asg) :
    (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).length = N4c.aggB (nSeg κ σ w) := by
  rw [N4c.chainBytes4, Stream.streamBytes_length, N4c.streamB, nSeg, N4c.kOf]
  by_cases hA : N4c.isAgg κ σ = true
  · obtain ⟨ha, -⟩ := N4c.agg_of_isAgg κ hσ hA
    rw [if_pos hA, if_pos hA, if_pos hA, kA_rd4 pf κ ha]
  · rw [if_neg hA, if_neg hA]; rfl

theorem aggB_mono {m m' : ℕ} (h : m ≤ m') : N4c.aggB m ≤ N4c.aggB m' := by
  simp only [N4c.aggB]
  have := Nat.mul_le_mul_right (N4c.segB - 1) h
  have := Nat.mul_le_mul_right N4c.spacerB (Nat.sub_le_sub_right h 1)
  omega

theorem aggB_step (i : ℕ) : N4c.aggB (i + 1) - N4c.aggB i = (if i = 0 then 0 else 129) + (N4c.segB - 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [N4c.aggB]
  · rw [N4c.aggB_succ i hi, if_neg (by omega)]; simp only [N4c.spacerB]; omega

theorem traceBytes_flatten' (trs : List Trace) : traceBytes trs.flatten = (trs.map traceBytes).flatten := by
  induction trs with
  | nil => rfl
  | cons t ts ih => simp only [List.flatten_cons, traceBytes, List.flatMap_append, List.map_cons] at ih ⊢; rw [ih]

/-- **The stream of `0x54 ‖ V_A`'s trace has its constant bytes** (the converse of `stream_of_wf`). -/
theorem wf_of_eq {B : List UInt8} {n : ℕ} (hl : B.length = N4c.aggB n)
    (h : B = tagTrace :: traceBytes (aggTrace (fun i => spAnsB B (i * N4c.strideB - 128))
      ((List.range n).map fun i => Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4)))) :
    B.head? = some tagTrace ∧ ∀ i < n, WfAt B (1 + i * N4c.strideB) (itemsOf seq4) ∧
      (0 < i → SpAt B (i * N4c.strideB - 128)) := by
  rw [aggTrace_range] at h
  set g : ℕ → Trace := fun i => (if i = 0 then [] else [spEntry (spAnsB B (i * N4c.strideB - 128))]) ++
    Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4) with hg
  have hT := slenS_seq4
  have hfit : ∀ i < n, 1 + i * N4c.strideB + slenS (itemsOf seq4) ≤ B.length := fun i hi => by
    have := aggB_mono (show i + 1 ≤ n by omega)
    rw [hl, hT]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [N4c.aggB] at this ⊢; omega
    · have h1 := N4c.aggB_succ i hi0
      have h2 := (N4c.aggB_blocks hi0).2.2
      have : 128 ≤ i * N4c.strideB := le_trans (by decide) (Nat.le_mul_of_pos_left N4c.strideB hi0)
      simp only [N4c.spacerB] at h1; omega
  have hsz : ∀ i < n, (traceBytes (Read.readItems B (1 + i * N4c.strideB) (itemsOf seq4))).length =
      N4c.segB - 1 := fun i hi => by
    rw [traceBytes_length_of (readItems_sizes B _ _ (hfit i hi)), hT]
  have hgl : ∀ i < n, (traceBytes (g i)).length = N4c.aggB (i + 1) - N4c.aggB i := fun i hi => by
    rw [aggB_step, hg]; dsimp only
    rw [traceBytes_append, List.length_append, hsz i hi]
    split_ifs
    · rfl
    · rw [spacer_entry_length]
  have hpre : ∀ m ≤ n, (traceBytes ((List.range m).map g).flatten).length = N4c.aggB m - 1 := by
    intro m
    induction m with
    | zero => intro _; simp [N4c.aggB, traceBytes]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.flatten_append, traceBytes_append, List.length_append,
        ih (by omega), List.map_singleton, List.flatten_singleton, hgl m (by omega)]
      have := aggB_mono (Nat.le_add_right m 1)
      have : 1 ≤ N4c.aggB m := by simp only [N4c.aggB]; omega
      omega
  -- block `i`: `B.drop (aggB i)` starts with `traceBytes (g i)`
  have hblk : ∀ i < n, (B.drop (N4c.aggB i)).take (N4c.aggB (i + 1) - N4c.aggB i) = traceBytes (g i) := by
    intro i hi
    have hr : List.range n = List.range i ++ i :: List.range' (i + 1) (n - (i + 1)) := by
      obtain ⟨d, rfl⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
      rw [show i + 1 + d - (i + 1) = d by omega, List.range_eq_range', List.range_eq_range',
        show i + 1 + d = i + (d + 1) by omega, ← List.range'_append, List.range'_succ]
      simp
    have hb1 : 1 ≤ N4c.aggB i := by simp only [N4c.aggB]; omega
    rw [hr, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, traceBytes_append,
      traceBytes_append] at h
    conv_lhs => rw [h]
    rw [show N4c.aggB i = (N4c.aggB i - 1) + 1 by omega, List.drop_succ_cons,
      List.drop_left' (hpre i (by omega)), Nat.sub_add_cancel hb1, ← hgl i hi, List.take_left' rfl]
  refine ⟨by rw [h]; rfl, fun i hi => ?_⟩
  have hb := hblk i hi
  rw [aggB_step, hg] at hb
  dsimp only at hb
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- segment 0
    have hb0 : (B.drop 1).take (slenS (itemsOf seq4)) = traceBytes (Read.readItems B 1 (itemsOf seq4)) := by
      rw [hT]; simpa [N4c.aggB] using hb
    have hf0 : 1 + slenS (itemsOf seq4) ≤ B.length := by simpa using hfit 0 hi
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    simp only [Nat.zero_mul, Nat.add_zero]
    exact wfAt_of_take B _ _ _ (readItems_sizes B _ _ hf0) hf0 hb0
  · simp only [if_neg (Nat.pos_iff_ne_zero.1 hi0)] at hb
    rw [traceBytes_append, List.take_add] at hb
    have e1 : i * N4c.strideB - 128 = N4c.aggB i := (N4c.aggB_blocks hi0).2.2.symm
    have e2 : N4c.aggB i + 129 = 1 + i * N4c.strideB := by
      have h3 : N4c.strideB ≤ i * N4c.strideB := Nat.le_mul_of_pos_left _ hi0
      have h4 : 128 ≤ N4c.strideB := by simp only [N4c.strideB, N4c.segB, N4c.spacerB]; omega
      omega
    have hfi := hfit i hi
    rw [hT, ← e2] at hfi
    rw [e1] at hb ⊢
    rw [← e2] at hb ⊢
    generalize N4c.aggB i = o at hb hfi ⊢
    have hsl := spacer_entry_length (spAnsB B o)
    obtain ⟨h1, h2⟩ := List.append_inj hb (by rw [List.length_take, List.length_drop, hsl]; omega)
    have hfit' : o + 129 + slenS (itemsOf seq4) ≤ B.length := by rw [hT]; omega
    refine ⟨wfAt_of_take B _ _ _ (readItems_sizes B _ _ hfit') hfit' ?_, fun _ => ?_⟩
    · rw [List.drop_drop] at h2
      rw [hT, h2]
    · unfold SpAt
      have : ((B.drop o).take 129).take 97 = (B.drop o).take 97 := by
        rw [List.take_take]; rfl
      have h97 : (enc64 spacerQ.size ++ spacerQ.data.toList).length = 97 := by
        rw [List.length_append, enc64_length, Array.length_toList]; exact congrArg (8 + ·) spacerQ_size
      rw [← this, h1, traceBytes, List.flatMap_singleton]
      show (enc64 spacerQ.size ++ spacerQ.data.toList ++ _).take 97 = _
      rw [List.take_left' h97, spacerQ_size]

/-- **The well-formedness gap from `chainMsg`**: if the stream is `0x54 ‖ traceBytes` of the read
trace, its tag, its length words and its spacers' constant bytes are in place. -/
theorem wf_of_chainMsg (pf : Trace → Proof) {κ : NodeKind} {σ : ℕ} {w : Asg} (hσ : σ < 2)
    (h : N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w = tagTrace :: traceBytes ((rd4 pf).sgn κ σ w).tr) :
    (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w).head? = some tagTrace ∧
      ∀ i < nSeg κ σ w, WfAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (1 + i * N4c.strideB)
        (itemsOf seq4) ∧
      (0 < i → SpAt (N4c.chainBytes4 κ σ (N4c.kOf (rd4 pf) κ w σ) w) (i * N4c.strideB - 128)) := by
  rw [sgn4_tr pf hσ w] at h
  exact wf_of_eq (chain_len pf (κ := κ) hσ w) h

/-- **`Gap4` asks no more than `NodeResid4`**: on the node's truths, the residual at `I4`, `rd4 pf`
gives every field of `Gap4`. -/
theorem gap4_of_resid {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (pf : Trace → Proof) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}
    (hR : N4c.NodeResid4 (I4 impl₀ base hT₀ hT) (rd4 pf) κ vk c₁ c₂ w) : Gap4 impl₀ base pf κ vk c₁ c₂ w where
  imp := hR.imp
  kindN hp ι hι := by
    obtain ⟨κ', ⟨-, ι', rfl, hι'⟩, hk⟩ := hR.selP hp
    rw [selOk_unique hι hι']
    exact byte_of_kindOf4 hk
  kindS a ha i hi ι hι := by
    obtain ⟨v, hv, -, ι', hk, hι'⟩ := hR.selA a ha i (by rw [kA_rd4 pf κ ha]; exact hi)
    rw [selOk_unique hι hι', hk]
    exact byte_of_segView hv
  wf σ hσ := wf_of_chainMsg pf hσ (hR.chainMsg σ hσ)
  aggChk := hR.aggChk
  aggPad := hR.aggPad
  wots := hR.wots

end N4s
end FR
