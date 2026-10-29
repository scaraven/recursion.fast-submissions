-- New for `flock-recursive` (BLUEPRINT B-12, B-13, §5.1; stage S-G13, item (e): the per-program
-- query bounds that INT-7's `ks_queries4` takes).
import FRVerifierC4
import FRVIRSpec

/-!
# The revision 4.1 programs ask the item sequence `itemsOf seq4` (8,907 queries)

* **`items_genPhase4`**: one phase of `gen4 S p` asks exactly its shape's items under `S.lv`
  (`Sh.itemsL`), for every kind `p` (a segment's `lastOps` and Z2 operand ask nothing; a level's
  Merkle steps ask `(S.lv i).sib` nodes, whatever the kind's own depth).
* **`items_gen4`**: `gen4 S p fin` asks `itemsOf S` when `fin` asks nothing; **`noAsk_finOps4`**:
  the relocated finals `finOps4 P` ask nothing (each of `finalsOf P`'s nine fields).
* **`queries_VsegC`**, **`queries_VnodeC`**: every segment and node program asks
  `(itemsOf seq4).length = 8,907` queries under every oracle. **`ks_queriesC4`**: `KS`'s first
  conjunct for `VC4` at `qV4` (INT-7's `ks_queries4` with `qS = 8,907`).
-/

namespace FR.Rev4
open RecursionFast FR

/-! ## The skeleton -/

theorem items_merkleOps4 (sib i : ℕ) (j : Reg) (n h cur so b : ℕ) :
    (merkleOps4 sib i j n h cur so b).filterMap Op.item? = (List.range n).map fun k => .node i (h + k) := by
  induction n generalizing h cur so b with
  | zero => rfl
  | succ n ih =>
    simp only [merkleOps4, List.filterMap_append, ih, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp [List.filterMap_cons, Op.item?, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem items_posOps4 (S : Seq) (k : KindP) (i co so : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) :
    (posOps4 S k i co so ans w p b).filterMap Op.item? = posItemsL S.lv i := by
  simp [posOps4, posItemsL, List.filterMap_cons, Op.item?, items_merkleOps4]

theorem noAsk_lastOps (so b : ℕ) : (lastOps so b).filterMap Op.item? = [] := by
  simp only [lastOps, List.filterMap_append, List.filterMap_flatMap]
  simp [List.filterMap_cons, Op.item?]

theorem noAsk_stmtOps4 (p : KindP) (so msg b : ℕ) : (stmtOps4 p so msg b).filterMap Op.item? = [] := by
  unfold stmtOps4; split <;> simp [List.filterMap_cons, Op.item?]

/-- **One phase of `gen4 S p` asks its shape's items** (`Sh.itemsL S.lv`). -/
theorem items_genPhase4 (S : Seq) (p : KindP) (n : ℕ) (ph : String × Sh) (c : GCtx) :
    (genPhase4 S p n ph c).1.filterMap Op.item? = ph.2.itemsL S.lv := by
  obtain ⟨name, sh⟩ := ph
  cases sh with
  | seed => simp [genPhase4, seedOps4, List.filterMap_cons, Op.item?, Sh.itemsL]
  | absorb f len =>
    simp only [genPhase4, Sh.itemsL]
    split_ifs <;>
      simp [absorbOps, finalOps4, List.filterMap_cons, List.filterMap_append, Op.item?,
        noAsk_stmtOps4, noAsk_lastOps]
  | squeezes k ch =>
    cases ch <;> simp [genPhase4, Sh.itemsL, items_sqzCoordOps, items_sqzOps, List.filterMap_cons,
      List.filterMap_append, Op.item?]
  | uni f =>
    simp only [genPhase4, Sh.itemsL]
    split_ifs <;> simp [segPtOp, uniOps, uniHead, uniElems, uniTail, List.filterMap_cons,
      List.filterMap_append, Op.item?, Function.comp_def]
  | rounds f k deg inK =>
    simp only [genPhase4, Sh.itemsL]
    rw [List.filterMap_append, items_roundsOps]
    rcases initClaim name with _ | _ | _ <;> cases inK <;>
      simp [initOps, List.filterMap_cons, Op.item?]
  | queries i =>
    simp only [genPhase4, Sh.itemsL]
    rw [List.filterMap_append, List.filterMap_flatMap]
    simp only [items_posOps4]
    rw [flatMap_range_const _ _ _ fun _ => rfl]; rfl

theorem items_genPhases4 (S : Seq) (p : KindP) (ps : List (String × Sh)) (n : ℕ) (c : GCtx) :
    (genPhases4 S p ps n c).1.filterMap Op.item? = ps.flatMap fun ph => ph.2.itemsL S.lv := by
  induction ps generalizing n c with
  | nil => rfl
  | cons ph ps ih => simp [genPhases4, ih, items_genPhase4]

/-- **`gen4 S p fin` asks `itemsOf S`**, for every phase-final fragment that asks nothing. -/
theorem items_gen4 (S : Seq) (p : KindP) (fin : FinOps)
    (hfin : ∀ outs b, (fin outs b).filterMap Op.item? = []) :
    (gen4 S p fin).ops.filterMap Op.item? = itemsOf S := by
  simp [gen4, skeleton4, items_genPhases4, hfin, List.filterMap_cons, Op.item?, itemsOf]

/-! ## The finals over `FinP` ask nothing -/

/-! ## The finals over `FinP` ask nothing -/

theorem noAsk_gCellsOps (nc : ℕ) (one g h kp : Reg) :
    ∀ cs acc pw b, (gCellsOps nc one g h kp cs acc pw b).filterMap Op.item? = []
  | [], _, _, _ => rfl
  | c :: cs, acc, pw, b => by
    rw [gCellsOps, gCellOps, List.filterMap_append, List.filterMap_append, noAsk_prodKOps,
      noAsk_gCellsOps nc one g h kp cs]
    rfl

theorem noAsk_gLvsOps (S : Seq) (fi : FinIn) (one cu Ts : Reg) :
    ∀ ks W b, (gLvsOps S fi one cu Ts ks W b).filterMap Op.item? = []
  | [], _, _ => rfl
  | k :: ks, W, b => by
    have ht : ((List.range (ysOf fi (k - 1)).length).map fun q =>
        Op.tensorW ((ysOf fi (k - 1)).getD q 0 - 3) (Ts + (k - 1))).filterMap Op.item? = [] :=
      noAsk_map _ _ fun _ => rfl
    rw [gLvsOps, gLvOps, List.filterMap_append, noAsk_gLvsOps S fi one cu Ts ks]
    simp only [List.filterMap_append, noAsk_accOps, ht]
    rfl

theorem noAsk_padOps (one pd μ k : ℕ) (sf : List Reg) : (padOps one pd μ k sf).filterMap Op.item? = [] := by
  rw [padOps, List.filterMap_append, noAsk_prodKOps, noAsk_map _ _ fun _ => rfl]; rfl

theorem noAsk_gEncOps (pf : ℕ) (units fin : List Reg) (j y b : ℕ) :
    (gEncOps pf units fin j y b).filterMap Op.item? = [] := by
  simp [gEncOps, Op.item?, noAsk_hornerKOps, List.filterMap_eq_nil_iff]

theorem noAsk_gFinZ (P : FinP) (fi : FinIn) (b : ℕ) : (gFinZ P fi b).1.filterMap Op.item? = [] := by
  simp [gFinZ, pinOps, Op.item?]

theorem noAsk_gFinLc (P : FinP) (fi : FinIn) (b : ℕ) : (gFinLc P fi b).1.filterMap Op.item? = [] := by
  simp only [gFinLc, List.filterMap_append, dotOps_noAsk, List.append_nil]
  simp [gLcHead, lcTail, hornerOps, Op.item?]
  aesop

theorem noAsk_gShCore (P : FinP) (fi : FinIn) (b₀ tm : ℕ) :
    (gShCore P fi b₀ tm).1.filterMap Op.item? = [] := by
  simp [gShCore, gBndOps, linkOps, Op.item?]
  aesop

theorem noAsk_gFinSh (P : FinP) (fi : FinIn) (b : ℕ) : (gFinSh P fi b).1.filterMap Op.item? = [] := by
  unfold gFinSh
  cases P.vn
  · exact noAsk_gShCore P fi b (b + 8)
  · simp only [cond, List.filterMap_cons, Op.item?]; exact noAsk_gShCore P fi (b + 1) b

theorem noAsk_gFinLr (P : FinP) (fi : FinIn) (b : ℕ) : (gFinLr P fi b).1.filterMap Op.item? = [] := by
  cases hc : P.ck <;> simp [gFinLr, Op.item?, hc]

theorem noAsk_gFinRS (P : FinP) (fi : FinIn) (b : ℕ) : (gFinRS P fi b).1.filterMap Op.item? = [] := by
  simp only [gFinRS, List.filterMap_append,
    noAsk_claimOps _ (fun i => Op.getF _ i) (fun _ => rfl),
    noAsk_claimOps _ (fun i => Op.const (fun _ => .f (bb i))) (fun _ => rfl), List.append_nil]
  rfl

theorem noAsk_gFinE (P : FinP) (fi : FinIn) (b : ℕ) : (gFinE P fi b).1.filterMap Op.item? = [] := by
  cases hc : P.ck <;> simp [gFinE, Op.item?, hc]

theorem noAsk_gFinB' (P : FinP) (fi : FinIn) (b : ℕ) : (gFinB' P fi b).1.filterMap Op.item? = [] := by
  simp [gFinB', Op.item?]

theorem noAsk_gFinP (P : FinP) (i : ℕ) (fi : FinIn) (b : ℕ) :
    (gFinP P i fi b).1.filterMap Op.item? = [] := by
  unfold gFinP
  split_ifs with h
  · simp only [finPLow, List.filterMap_append, List.filterMap_cons, Op.item?, noAsk_accOps]; rfl
  · simp [gFinPTop, Op.item?, noAsk_gEncOps, List.filterMap_flatMap, List.filterMap_eq_nil_iff]

theorem noAsk_gFinPf (P : FinP) (fi : FinIn) (b : ℕ) : (gFinPf P fi b).1.filterMap Op.item? = [] := by
  have h1 : ∀ (a : Reg) (n : ℕ),
      ((List.range n).map fun v => Op.getK a v).filterMap Op.item? = [] :=
    fun _ _ => noAsk_map _ _ fun _ => rfl
  have h2 : ∀ (a c : Reg) (n : ℕ),
      ((List.range n).map fun v => Op.addK a (c + v)).filterMap Op.item? = [] :=
    fun _ _ _ => noAsk_map _ _ fun _ => rfl
  have h3 : ∀ (sel : KC Bool) (c : ℕ → Reg) (n pb : ℕ),
      ((List.range n).map fun s => Op.keep sel (c s) (pb + s)).filterMap Op.item? = [] :=
    fun _ _ _ _ => noAsk_map _ _ fun _ => rfl
  cases hc : P.ck <;>
  simp only [gFinPf, hc, Bool.cond_true, Bool.cond_false, List.filterMap_append, noAsk_ptsOps,
    noAsk_gCellsOps, noAsk_gCellsOpsK, noAsk_gLvsOps, noAsk_fhOps, noAsk_padsOps, noAsk_selOps,
    noAsk_gTailOps, List.filterMap_flatMap, List.filterMap_cons, Op.item?, h1, h2] <;>
  simp [noAsk_map _ _ (fun _ => rfl : ∀ s : ℕ, (Op.keep _ _ _ : Op).item? = none)]

/-- **Every field of `finalsOf P` asks nothing** (`accept_chain`'s hypothesis form). -/
theorem noAsk_finalsOf (P : FinP) : ∀ f ∈ (finalsOf P).finRS :: (finalsOf P).rest,
    ∀ fi b, (f fi b).1.filterMap Op.item? = [] := by
  intro f hf fi b
  simp only [Finals.rest, finalsOf, nLevels, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | ((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, -, rfl⟩) | rfl
  exacts [noAsk_gFinRS P fi b, noAsk_gFinZ P fi b, noAsk_gFinLc P fi b, noAsk_gFinSh P fi b,
    noAsk_gFinLr P fi b, noAsk_gFinE P fi b, noAsk_gFinB' P fi b, noAsk_gFinP P i fi b,
    noAsk_gFinPf P fi b]

/-- The finals' ops ask nothing when every field does. -/
theorem noAsk_ops (fin : Finals) (h : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (outs : Array (List Reg)) (b : ℕ) : (fin.ops outs b).filterMap Op.item? = [] := by
  have hrs := h _ (List.mem_cons_self ..)
  have hst : ∀ (fs : List FinField), (∀ f ∈ fs, ∀ fi b, (f fi b).1.filterMap Op.item? = []) →
      ∀ acc : List Op × ℕ × Array (List Reg), acc.1.filterMap Op.item? = [] →
      (fs.foldl (fun (acc : List Op × ℕ × Array (List Reg)) (f : FinField) =>
        let x := f ⟨outs, (fin.finRS ⟨outs, [], #[]⟩ b).2, acc.2.2⟩ acc.2.1
        (acc.1 ++ x.1, acc.2.1 + opsOut x.1, acc.2.2.push x.2)) acc).1.filterMap Op.item? = [] := by
    intro fs
    induction fs with
    | nil => intro _ acc ha; exact ha
    | cons f fs ih =>
      intro hfs acc ha
      exact ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _
        (by rw [List.filterMap_append, ha, hfs f (List.mem_cons_self ..)]; rfl)
  simp only [Finals.ops, List.filterMap_append, hrs, List.nil_append]
  exact hst _ (fun f hf => h f (List.mem_cons_of_mem _ hf)) _ rfl

/-- **The relocated finals ask nothing.** -/
theorem noAsk_finOps4 (P : FinP) (outs : Array (List Reg)) (b : ℕ) :
    (finOps4 P outs b).filterMap Op.item? = [] := by
  rw [finOps4, List.filterMap_map]
  have : (Op.item? ∘ reloc P.S) = Op.item? := funext fun op => item_reloc P.S op
  rw [this, List.filterMap_append, noAsk_ops _ (noAsk_finalsOf P) outs b, noAsk_capChkOps]; rfl

/-! ## The bounds -/

theorem itemsOf_seq4_len : (itemsOf seq4).length = 8907 := itemsOf_seq4_length

/-- **Every segment program asks 8,907 queries** under every oracle. -/
theorem queries_VsegC (impl₀ : OpImpl) (H : ByteArray → Digest) (κ : SegKind) (vk c : Digest) (π : Proof) :
    ((VsegC impl₀ κ vk c π).queries H).length = 8907 := by
  rw [VsegC, runStmt_queries, queries_runIR, progSeg, genSeg, items_gen4 _ _ _ (noAsk_finOps4 _),
    itemsOf_seq4_len]

/-- **Every node program asks 8,907 queries** under every oracle. -/
theorem queries_VnodeC (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ) (H : ByteArray → Digest)
    (κ : NodeKind) (vk c : Digest) (π : Proof) :
    ((VnodeC implN cells κ vk c π).queries H).length = 8907 := by
  rw [VnodeC, runStmt_queries, queries_runIR, progNode, genNode, items_gen4 _ _ _ (noAsk_finOps4 _),
    itemsOf_seq4_len]

/-- **`KS`'s first conjunct for `VC4`** at `qV4` (`ks_queries4` with `qS = 8,907`). -/
theorem ks_queriesC4 (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4) (vk : Digest) :
    ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV :=
  ks_queries4 (VsegC impl₀) (VnodeC implN cells) S hV hq
    (fun H κ vk c π => (queries_VsegC impl₀ H κ vk c π).le)
    (fun H κ vk c π => (queries_VnodeC implN cells H κ vk c π).le.trans (by decide)) (by rw [← itemsOf_seq4_len]; exact traces_le_qV) vk

end FR.Rev4
