-- New for `flock-recursive` (BLUEPRINT §4.3 `node_sound`, A.7; stage S-N1).
import FRSoundnessExtLinks
import FRNodeReadLayout
import FRNodeReadP

/-!
# The node's assembly: from the statement on `f⁽⁰⁾` to `node_sound`'s hypotheses

What the statement `StmtN` gives `node_sound` (`FRNodeCircuit`), and what it does not:

* **`PubOK` → `PubCells`** (definitional on a node), and **`PubCells` binds the children's
  statements**: `readStmt w (σ + 1)` is `PubCells`' `c_σ` (**`readStmt_of_pubCells`**, through
  `digestOf_halves`: a digest's two F halves read back as the digest).
* **The format facts** of `readSigned σ w` (**`readSigned_fmt`**): `|π| = piSize ≤ proofCap`,
  `|tr| = 8,891 ≤ qV`, every query at most `queryCap` (**`items_qlen_le`**, per phase shape).
* **`truthLr` → the selector cells are bits** (`SlotHolds.bits`, **`selBits_of_truthLr`**).
* **The children are SNARKs** (`W`-kind children excluded): `SlotHolds`' one-hot rows and run fix
  a kind `κ` with `π.data[0]? = κ.byte`, and `|π| = piSize` (**`child_kind`**).
* **Not given** (S-N1 RESULT, findings O1 and O2): the rest of `SlotHolds` (`SlotRest`: the one-hot
  rows, the compiled rows and template rows of `compileT`, and the run with its imports and
  foreign flags) and the two signatures. They are the residual **`NodeResid`**.
* **`rel_readWit`**: with `PubCells`, `c = nodeStmt c₁ c₂`, the L rows and `NodeResid`,
  `readWit w` is a node witness of the relation (`node_sound`).
-/

namespace FR.Snd
open RecursionFast Finset Circ

set_option linter.constructorNameAsVariable false

/-! ## Bytes of digests and field elements -/

theorem toListLE_eq_ofFn : ∀ (n x : ℕ),
    CompPoly.Bytes.toListLE n x = List.ofFn fun i : Fin n => (x / 256 ^ i.val).toUInt8
  | 0, _ => rfl
  | n + 1, x => by
    rw [CompPoly.Bytes.toListLE, toListLE_eq_ofFn n (x / 256), List.ofFn_succ]
    congr 1
    · apply UInt8.toNat_inj.mp; simp [Nat.toUInt8]
    · refine congrArg List.ofFn (funext fun i => ?_)
      rw [Fin.val_succ, Nat.div_div_eq_div_mul, pow_succ', Nat.mul_comm]

theorem enc64_toListLE (n : ℕ) : enc64 n = CompPoly.Bytes.toListLE 8 n := by
  rw [toListLE_eq_ofFn, enc64]

/-- A word decoded from eight bytes encodes back to them. -/
theorem wordBytes_ofBytes (v : Vector UInt8 8) : wordBytes (B64.ofBytes v).val.toBitVec = v.toList := by
  have h := congrArg Vector.toList (B64.toBytes_ofBytes v)
  rw [B64.toBytes_toList] at h
  rw [wordBytes, enc64_toListLE]
  exact h

/-- An F element decoded from 16 bytes: its two coefficient words are those bytes. -/
theorem wordsBytes_elemWords (v : Vector UInt8 16) :
    wordsBytes (Read.elemWords (F.ofBytes v)) = v.toList := by
  simp only [Read.elemWords, wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    F.ofBytes, wordBytes_ofBytes]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split_ifs with h
  · rfl
  · congr 1; simp at h1; omega

/-- **A digest's two F halves read back as the digest.** -/
theorem digestOf_halves {w : ℕ → F} {a b : ℕ} {d : Digest} (ha : w a = dlo d) (hb : w b = dhi d) :
    Read.digestOf w a b = d := by
  apply Vector.toList_inj.mp
  rw [Read.digestOf, Read.digestW_toList (by simp [Read.elemWords]), wordsBytes, List.flatMap_append,
    ← wordsBytes, ← wordsBytes, ha, hb, dlo, dhi, wordsBytes_elemWords, wordsBytes_elemWords]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.toList_ofFn, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
    Vector.getElem_toList]
  split_ifs with h
  · rfl
  · congr 1; simp at h1; omega

/-! ## `PubCells` binds the children's statements -/

/-- The public cells' values (`PubCells`, A.7's order). -/
theorem pubCells_vals {w : Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂) :
    w (Node.seedCell 0 2) = dlo c₁ ∧ w (Node.seedCell 0 3) = dhi c₁ ∧
      w (Node.seedCell 1 2) = dlo c₂ ∧ w (Node.seedCell 1 3) = dhi c₂ := by
  simp only [Node.PubCells, Node.pubCells, Node.pubVals, Node.halves, List.range_succ,
    List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.cons.injEq] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

/-- **The children's statements are `PubCells`' digests.** -/
theorem readStmt_of_pubCells {w : Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂) :
    Read.readStmt w 1 = c₁ ∧ Read.readStmt w 2 = c₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := pubCells_vals h
  exact ⟨by rw [Read.readStmt_cells w 0]; exact digestOf_halves h1 h2,
    by rw [Read.readStmt_cells w 1]; exact digestOf_halves h3 h4⟩

/-- **`PubOK` on a node is `PubCells`** of the log's `vk`, `c₁`, `c₂`. -/
theorem pubCells_of_pubOK {L es : Log} (h : PubOK .N30 L es) :
    Node.PubCells (fF .N30 L es) (vkL es) (stL es 0) (stL es 1) := h rfl

/-! ## The format facts of a read child -/

/-- A phase shape's largest query. -/
def shapeQ : Shape → ℕ
  | .seed => 119
  | .absorb _ len => 40 + len
  | .squeezes _ _ => 40
  | .uni _ => 40 + uniBytes
  | .rounds _ _ _ inK _ => 40 + roundBytes inK
  | .queries i => max (8 + colBytes i) 72

theorem shape_qlen (sh : Shape) : ∀ it ∈ sh.items, it.qlen ≤ shapeQ sh := by
  intro it hit
  cases sh with
  | seed => simp [Shape.items] at hit; subst hit; rfl
  | absorb f len => simp [Shape.items] at hit; subst hit; simp [Item.qlen, shapeQ]
  | squeezes n ch =>
    simp only [Shape.items, List.mem_replicate] at hit; rw [hit.2]; simp [Item.qlen, shapeQ]
  | uni f =>
    simp only [Shape.items, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> simp [Item.qlen, shapeQ] <;> omega
  | rounds f n deg inK real =>
    simp only [Shape.items, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp [Item.qlen, shapeQ] <;> omega
  | queries i =>
    simp only [Shape.items, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hit
    simp only [posItems, List.mem_cons, List.mem_map, List.mem_range] at hl
    rcases hl with rfl | ⟨h, -, rfl⟩ <;> simp [Item.qlen, shapeQ]

/-- Every phase's largest query is within `queryCap` (52 phases, their shape parameters). -/
theorem phases_shapeQ : phases.all (fun p => decide (shapeQ p.shape ≤ queryCap)) = true := by
  decide +kernel

/-- **Every item's query is within `queryCap`.** -/
theorem items_qlen_le : ∀ it ∈ items, it.qlen ≤ queryCap := by
  intro it hit
  simp only [items, List.mem_flatMap] at hit
  obtain ⟨p, hp, hit⟩ := hit
  have := List.all_eq_true.1 phases_shapeQ p hp
  simp only [decide_eq_true_eq] at this
  exact (shape_qlen _ it hit).trans this

theorem readItems_qlen (B : List UInt8) : ∀ (o : ℕ) (its : List Item), ∀ e ∈ Read.readItems B o its,
    ∃ it ∈ its, e.1.size ≤ it.qlen
  | _, [], e, he => by simp [Read.readItems] at he
  | o, it :: its, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨it, List.mem_cons_self .., ?_⟩
      simp only [Read.entryAt, ByteArray.size, List.size_toArray]
      exact List.length_take_le _ _
    · obtain ⟨it', hit', h⟩ := readItems_qlen B _ its e he
      exact ⟨it', List.mem_cons_of_mem _ hit', h⟩

/-- **A read child's format facts**: its proof, trace and queries are within the caps. -/
theorem readSigned_fmt (w : ℕ → F) (σ : ℕ) :
    (readSigned σ w).π.size ≤ proofCap ∧ (readSigned σ w).tr.length ≤ qV ∧
      ∀ e ∈ (readSigned σ w).tr, e.1.size ≤ queryCap := by
  refine ⟨?_, ?_, fun e he => ?_⟩
  · have h : (readSigned σ w).π.size = piSize := Read.reassemble_size w σ
    rw [h, piSize_eq]; decide
  · have h : (readSigned σ w).tr.length = 8891 := Read.readTrace_length w σ
    rw [h]; decide
  · obtain ⟨it, hit, h⟩ := readItems_qlen _ 1 items e he
    exact h.trans (items_qlen_le it hit)

/-! ## The selector bits and the children's kinds -/

/-- **`truthLr` makes the selector cells bits** (`SlotHolds.bits`). -/
theorem selBits_of_lRows {w : Asg} (hone : w Layout.oneCell = 1) (h : ∀ r ∈ Layout.lRows, r.Holds w)
    {σ : ℕ} (hσ : σ < 2) : ∀ κ, IsBitCell w (Layout.selCells σ κ) :=
  fun κ => Layout.lRows_sound hone h (Layout.selCells_mem σ hσ κ)

/-- A proof of `piSize` bytes whose first byte is a kind byte is a SNARK of that kind. -/
theorem kindOf_of_byte {π : Proof} {k : Kind} (hb : π.data[0]? = some k.byte) (hs : π.size = piSize) :
    FR.kindOf π = .snark k := by
  simp [FR.kindOf, hb, Kind.ofByte?_byte, hs]

/-- **What `SlotHolds` asks beyond the selector bits** (the residual's per-slot part). -/
structure SlotRest (impl : OpImpl) (fin : Finals) (σ : ℕ) (w : Asg) (inp : Input)
    (tr : Trace) : Prop where
  oneHot : OneHotRows w Layout.oneCell (Layout.selCells σ)
  rows : ∀ r ∈ (TEval.slotCST fin σ).rows, r.Holds w
  trows : ∀ r ∈ (TEval.slotCST fin σ).tplRows (TEval.slotLay fin σ).ctx (TEval.slotP σ).one,
    r.Holds w
  run : ∀ κ, SelOk w (TEval.slotP σ) κ →
    inp.π.data[0]? = some κ.byte ∧ ∃ s : St, exec impl κ inp (gen fin .mux).ops St.init tr =
      some (s, []) ∧
      (∀ a ∈ (TEval.slotCST fin σ).aux,
        a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
      (∀ i ∈ (TEval.slotCST fin σ).imp, RepS w ((TEval.slotCST fin σ).slot i) (rd s.regs i)) ∧
      (∀ p ∈ (TEval.slotCST fin σ).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true)

/-- `SlotHolds` from the selector bits and the rest. -/
theorem slotHolds_of {impl : OpImpl} {fin : Finals} {σ : ℕ} {w : Asg} {inp : Input} {tr : Trace}
    (hb : ∀ κ, IsBitCell w (Layout.selCells σ κ)) (h : SlotRest impl fin σ w inp tr) :
    Node.SlotHolds impl fin σ w inp tr :=
  ⟨hb, h.oneHot, h.rows, h.trows, h.run⟩

/-- **A slot's child is a SNARK** (not `W`): the one-hot selector and the run fix its kind byte. -/
theorem child_kind {impl : OpImpl} {fin : Finals} {σ : ℕ} {w : Asg} {inp : Input} {tr : Trace}
    (hone : w Layout.oneCell = 1) (h : Node.SlotHolds impl fin σ w inp tr)
    (hs : inp.π.size = piSize) : ∃ k, FR.kindOf inp.π = .snark k := by
  obtain ⟨κ, hκ⟩ := oneHot_of_rows hone h.bits h.oneHot
  exact ⟨κ, kindOf_of_byte (h.run κ hκ).1 hs⟩

/-! ## The residual and the node witness -/

/-- **The node's residual** (S-N1 findings O1, O2): what `StmtN` does not give `node_sound`,
per slot: `SlotRest` (`compileT`'s rows and template rows, the one-hot rows, the run with its
imports and foreign flags) and the signature on the read trace. -/
structure NodeResid (impl : OpImpl) (fin : Finals) (vk : Digest) (w : Asg) : Prop where
  slot₁ : SlotRest impl fin 0 w ⟨vk, Read.readStmt w 1, (readSigned 1 w).π⟩ (readSigned 1 w).tr
  slot₂ : SlotRest impl fin 1 w ⟨vk, Read.readStmt w 2, (readSigned 2 w).π⟩ (readSigned 2 w).tr
  sig₁ : SigOk vk (traceDigest (readSigned 1 w).tr) (readSigned 1 w).σ = true
  sig₂ : SigOk vk (traceDigest (readSigned 2 w).tr) (readSigned 2 w).σ = true

/-- **The read node witness is a witness** (`node_sound`): `PubCells`, the statement
`c = nodeStmt c₁ c₂`, the L rows and the residual. -/
theorem rel_readWit {impl : OpImpl} {fin : Finals} {vk c c₁ c₂ : Digest} {w : Asg}
    (hT : ImplT impl) (hp : Node.PubCells w vk c₁ c₂) (hc : c = nodeStmt c₁ c₂)
    (hLr : ∀ r ∈ Layout.lRows, r.Holds w) (hR : NodeResid impl fin vk w) :
    Rel (accV impl fin vk) c (FR.readWit w) := by
  obtain ⟨e₁, e₂⟩ := readStmt_of_pubCells hp
  have hone := hp.one
  have h₁ := slotHolds_of (selBits_of_lRows hone hLr (by norm_num)) hR.slot₁
  have h₂ := slotHolds_of (selBits_of_lRows hone hLr (by norm_num)) hR.slot₂
  have hs : ∀ σ, (readSigned σ w).π.size = piSize := fun σ => Read.reassemble_size w σ
  obtain ⟨k₁, hk₁⟩ := child_kind hone h₁ (hs 1)
  obtain ⟨k₂, hk₂⟩ := child_kind hone h₂ (hs 2)
  rw [e₁] at h₁; rw [e₂] at h₂
  have := Node.node_sound hT hp hk₁ hk₂ (readSigned_fmt w 1) (readSigned_fmt w 2) hR.sig₁ hR.sig₂ h₁ h₂
  show c = nodeStmt (Read.readStmt w 1) (Read.readStmt w 2) ∧ _ ∧ _
  rw [e₁, e₂]
  exact ⟨hc, this⟩

/-! ## Controls -/

/-- Control (positive): any digest's two halves, placed in cells `0` and `1`, read back. -/
theorem digestOf_ctl (d : Digest) :
    Read.digestOf (fun e => if e = 0 then dlo d else dhi d) 0 1 = d :=
  digestOf_halves (by simp) (by simp)

/-- Control (positive / negative) of the query bound: every phase passes it, and an absorb of
`queryCap` bytes would not (its query has 40 more bytes). -/
theorem shapeQ_ctl : shapeQ (.absorb 0 queryCap) > queryCap ∧ shapeQ .seed = 119 := by
  simp [shapeQ, queryCap]

/-- Control (negative): `readStmt_of_pubCells` reads `c₁`'s cells, not `vk`'s: with different
`vk` and `c₁`, slot 1's statement is `c₁`, so it is not `vk`. -/
theorem readStmt_not_vk {w : Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂)
    (hne : vk ≠ c₁) : Read.readStmt w 1 ≠ vk := by
  rw [(readStmt_of_pubCells h).1]; exact hne.symm

/-- Control (negative): `NodeResid` is not trivial: it fails on any assignment whose slot-1 run
part rejects (here: no kind is selected and the one-hot rows fail because all selectors are
zero with `one = 1`). -/
theorem not_slotRest_zero {impl : OpImpl} {fin : Finals} {inp : Input} {tr : Trace} :
    ¬ SlotRest impl fin 0 (fun e => if e = Layout.oneCell then 1 else 0) inp tr := by
  intro h
  have h4 := h.oneHot.2.2.2
  have hne : ∀ κ, Layout.selCells 0 κ ≠ Layout.oneCell := by
    intro κ; cases κ <;> simp [Layout.selCells, Layout.oneCell, Layout.lBase, Layout.mBase]
  simp only [hne, ite_false, ite_true, add_zero, mul_zero] at h4
  exact zero_ne_one h4

end FR.Snd
