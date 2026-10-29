-- New for `flock-recursive` (BLUEPRINT A.6, A.7, A.9, A.10; stage S-G1j).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessCompose
import FRNodeCircuit
import FRSoundnessCoreRows

/-!
# The PIOP front: reads, the frame, the node's block order, the B′ cells, the 3.13 order

* **Part A: reads.** **`Reads p P`**: `P` reads only what lies before position `p` (the chain's
  entries and the words of earlier caps, `Same`), on chains of at least `p` entries. A phase's
  doom is `Bg ∨ U` with a **background** `Bg` (the other sub-protocols' pending claims and
  not-yet-reduced statements) that reads only entries before the phase, and the phase's own
  part `U`. **`Reads.append`/`Reads.ext1`/`Reads.ext`** (locality), **`Reads.stab`** (`hstab`)
  and **`Reads.chain`** (`FrontChainStab`) carry `Bg` through; **`card_frame`** and
  **`esc_msD_frame`** reduce a single squeeze's count and a multi-squeeze phase's escape to the
  phase's own part.
* **Part B: the node's WOTS order** against S-E3's export: **`nodeBK`** is `nodeKind`'s block
  class; **`nodeBK_wots`** (it is `Layout.wotsKindAt` on every WOTS block of both slots),
  **`ind_nodeBK`** (it agrees with `nodeLayout`'s `Ind` on every block of the node),
  **`nodeKind_wots`** (`nodeKind`'s WOTS targets are determined by `wotsKindAt`'s class and the
  offset), **`nodeKind_eq_none_iff`**.
* **Part C: B′'s cells.** **`pfCells_eq`**: `finPf`'s nine cells are `Node.pubCells` (no padding
  cells); **`cellsOf`**, **`truthBN`** (the B′ truth over them) and **`cells_sum_of_pub`** (on a
  word whose cells hold the public values, the cells' batched sum is the public values').
* **Part D: S-G1j's two defects, fixed by revision 3.13** (S-G1j RESULT §1; INT-2):
  **`e4_before_rs0`** (the control of the fixed order: E4's 23 challenges `r′` at 265 … 310, E4
  end at 311, then RS0's partials at 312 and RS1 from 313; S-G1j's `rs0_before_e4` no longer
  holds and is withdrawn), and **`evalL_short_zero`**, kept as the negative control of `finE`'s
  `evalL` point: at a cell point of at most 15 coordinates `evalL` is identically `0` (every L
  row reads cells at or above `2^15`), which is why `finE` passes all 23 of E4's challenges
  (`FRVIRFinalsSF.finE_evalL_point`); Lr4, whose 15 challenges were that point, is withdrawn.
* **`frontLocal_of`**: `FrontLocal` from congruence under `Same` up to P1.0.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: reads and the frame -/

variable {p : ℕ} {P Q : Log → Log → Prop}

theorem Reads.mono (h : Reads p P) {q : ℕ} (hq : p ≤ q) : Reads q P :=
  fun L es L' es' h1 h2 hS => h L es L' es' (by omega) (by omega) (hS.mono hq)

theorem Reads.or (hP : Reads p P) (hQ : Reads p Q) : Reads p fun L es => P L es ∨ Q L es :=
  fun L es L' es' h1 h2 hS => or_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem Reads.and (hP : Reads p P) (hQ : Reads p Q) : Reads p fun L es => P L es ∧ Q L es :=
  fun L es L' es' h1 h2 hS => and_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem Reads.not (hP : Reads p P) : Reads p fun L es => ¬ P L es :=
  fun L es L' es' h1 h2 hS => not_congr (hP L es L' es' h1 h2 hS)

theorem reads_false (p : ℕ) : Reads p fun _ _ => False := fun _ _ _ _ _ _ _ => Iff.rfl

/-- Locality: appending to a chain of at least `p` entries does not change `P`. -/
theorem Reads.append (h : Reads p P) (L es xs : Log) (hp : p ≤ es.length) :
    P L (es ++ xs) ↔ P L es :=
  h L _ L es (by simp; omega) hp ((same_append L es xs).mono hp)

theorem Reads.ext1 (h : Reads p P) (L es : Log) (a : Digest) (hp : p ≤ es.length) :
    P L (ext1 es a) ↔ P L es := h.append L es _ hp

theorem Reads.ext (h : Reads p P) (L es : Log) (as : List Digest) (hp : p ≤ es.length) :
    P L (ext es as) ↔ P L es := by
  obtain ⟨ys, hy⟩ := ext_eq_append es as
  rw [hy]; exact h.append L es ys hp

/-- Stability (`hstab`) on `hloc_of`'s extensions. -/
theorem Reads.stab (h : Reads p P) {L : Log} (hb : ¬ Bad L) {i : ℕ} (hci : IsChain L i) {X : Log}
    (hX : StabExt fsRnd (entriesOf L (pathOf L i)) X) (hp : p ≤ X.length) :
    P (L.take i) X ↔ P L X :=
  h _ X L X hp hp ((same_stabX hb hci hX).mono hp)

/-- Stability on the chain itself (`FrontChainStab`). -/
theorem Reads.chain (h : Reads p P) {L : Log} (hb : ¬ Bad L) {j : ℕ} (hci : IsChain L j)
    (hp : p ≤ (entriesOf L (pathOf L j)).length) :
    P (L.take j) (entriesOf L (pathOf L j)) ↔ P L (entriesOf L (pathOf L j)) :=
  h _ _ L _ hp hp ((same_chain hb hci).mono hp)

/-- A predicate of the level-0 word and the entries before `p` reads before `p` (`p > capPos 0`). -/
theorem reads_of_same {f : Log → Log → Prop}
    (h : ∀ L es L' es', Same L es L' es' p → (f L es ↔ f L' es')) : Reads p f :=
  fun L es L' es' _ _ hS => h L es L' es' hS

open Classical in
/-- **The frame at a single squeeze**: a background that reads before the squeeze never
escapes, so only the phase's own part counts. -/
theorem card_frame {Bg U U' : Log → Log → Prop} (hBg : Reads p Bg) (L es : Log)
    (hp : p ≤ es.length) :
    (univ.filter fun a => (Bg L es ∨ U L es) ∧ ¬ (Bg L (ext1 es a) ∨ U' L (ext1 es a))).card ≤
      (univ.filter fun a => U L es ∧ ¬ U' L (ext1 es a)).card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and, not_or] at ha ⊢
  refine ⟨ha.1.resolve_left fun hb => ha.2.1 ((hBg.ext1 L es a hp).mpr hb), ha.2.2⟩

/-- **The frame in a multi-squeeze phase**: an escape of `msD (Bg ∨ U) (Bg ∨ U')` is an escape of
the phase's own part with the background false. -/
theorem esc_msD_frame {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges)
    {Bg U U' : Log → Log → Prop} (hBg : Reads (s0 + 1) Bg)
    (hprev : Dk (phOf s0) = fun L es => Bg L es ∨ U L es)
    (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) (fun L es => Bg L es ∨ U' L es) s0 r)
    {L es₀ : Log} (hl : es₀.length = s0 + 1) (as : List Digest) (has : as.length = r)
    (he : EscAtG (DPos (Dp Dk)) L (ext es₀ as)) :
    ¬ Bg L es₀ ∧ U L es₀ ∧ ¬ U' L (ext es₀ as) := by
  obtain ⟨hd, hnf⟩ := esc_msD hmem hfin hl as has he
  rw [hprev] at hd
  simp only [not_or] at hnf
  have hb : ¬ Bg L es₀ := fun hb => hnf.1 ((hBg.ext L es₀ as (by omega)).mpr hb)
  exact ⟨hb, hd.resolve_left hb, hnf.2⟩

/-- **`FrontLocal`** from congruence under `Same` up to P1.0's first absorb. -/
theorem frontLocal_of {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (hW : ∀ L es L' es', Same L es L' es' (p1Start 0) → W₀ L es = W₀ L' es')
    (hc : ∀ L es L' es', Same L es L' es' (p1Start 0) → c₀ L es = c₀ L' es') :
    FrontLocal W₀ c₀ := fun L es L' es' _ hS hp =>
  ⟨hW L es L' es' (hS.mono hp), hc L es L' es' (hS.mono hp)⟩

/-! ## Part B: the node's WOTS block order (S-E3's export) -/

theorem wots_blk {σ off : ℕ} (hσ : σ < 2) (ho : off < Layout.wotsSlot) :
    ¬ Layout.wotsBase + Layout.wotsSlot * σ + off < 2 * Layout.chainN ∧
    ¬ Layout.wotsBase + Layout.wotsSlot * σ + off < Layout.wotsBase ∧
    Layout.wotsBase + Layout.wotsSlot * σ + off < Layout.wmBase ∧
    (Layout.wotsBase + Layout.wotsSlot * σ + off - Layout.wotsBase) % Layout.wotsSlot = off := by
  simp only [Layout.wotsBase, Layout.wmBase, Layout.stmtBase] at *
  refine ⟨by omega, by omega, by rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> omega, ?_⟩
  rw [show 2 * Layout.chainN + 6 + Layout.wotsSlot * σ + off - (2 * Layout.chainN + 6) =
    off + Layout.wotsSlot * σ by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho]

/-- **`nodeKind`'s WOTS order is S-E3's**: on every WOTS block of both slots, the class is
`Layout.wotsKindAt` of the offset. -/
theorem nodeBK_wots {σ off : ℕ} (hσ : σ < 2) (ho : off < Layout.wotsSlot) :
    nodeBK (Layout.wotsBase + Layout.wotsSlot * σ + off) = Layout.wotsKindAt off := by
  obtain ⟨h1, h2, h3, h4⟩ := wots_blk hσ ho
  simp only [nodeBK, h1, h2, h3, h4, ite_false, ite_true]

open FR.Kinds FR.Stream in
/-- WOTS block `off`'s target, from its class (`wotsKindAt`) and its offset. -/
def wotsTgt (off : ℕ) : Block.Target :=
  match Layout.wotsKindAt off with
  | .w43 => (w43 (off / 3).toUInt8 (off % 3).toUInt8).target
  | .hashB1 =>
    (hashB1 (if off = 399 then RecursionFast.tagWotsLeaf else RecursionFast.tagSigNode)).target
  | .stream => streamTarget 4265 (off - 399)
  | .streamEnd41 => streamEnd41.target
  | _ => hashB2.target

/-- **`nodeKind`'s WOTS targets are `wotsTgt`**: the class is S-E3's `wotsKindAt`. -/
theorem nodeKind_wots {σ off : ℕ} (hσ : σ < 2) (ho : off < Layout.wotsSlot) :
    nodeKind (Layout.wotsBase + Layout.wotsSlot * σ + off) = some (wotsTgt off) := by
  obtain ⟨h1, h2, h3, h4⟩ := wots_blk hσ ho
  have hw : Layout.wotsSlot = 498 := rfl
  simp only [nodeKind, h1, h2, h3, h4, ite_false, ite_true, wotsTgt, Layout.wotsKindAt]
  by_cases a1 : off < 399
  · simp [a1]
  by_cases a2 : off = 399
  · subst a2; simp
  by_cases a3 : off < 465
  · simp [a1, a2, a3]
  by_cases a4 : off = 465
  · subst a4; simp
  by_cases a5 : (off - 466) % 2 = 0 <;> simp [a1, a2, a3, a4, a5]

theorem nodeKind_eq_none_iff (blk : ℕ) : nodeKind blk = none ↔ Layout.wmBase ≤ blk := by
  have : Layout.wotsBase ≤ Layout.wmBase := by simp [Layout.wmBase]
  have : 2 * Layout.chainN ≤ Layout.wotsBase := by simp [Layout.wotsBase, Layout.stmtBase]
  unfold nodeKind
  split_ifs <;> simp <;> omega

theorem nodeBK_eq_free_iff (blk : ℕ) : nodeBK blk = .free ↔ Layout.wmBase ≤ blk := by
  have : Layout.wotsBase ≤ Layout.wmBase := by simp [Layout.wmBase]
  have : 2 * Layout.chainN ≤ Layout.wotsBase := by simp [Layout.wotsBase, Layout.stmtBase]
  unfold nodeBK Layout.wotsKindAt
  split_ifs <;> simp <;> omega

/-- **`nodeKind`'s classes agree with `nodeLayout`** on every block of the node: `Ind (nodeBK blk)
blk`. -/
theorem ind_nodeBK {blk : ℕ} (h : blk < Layout.nodeBlocks) :
    Layout.Ind (nodeBK blk) blk = true := by
  have hc : Layout.chainN = 23146 := rfl
  have hw : Layout.wotsSlot = 498 := rfl
  by_cases h1 : blk < 2 * Layout.chainN
  · have hσ : blk / Layout.chainN < 2 := by rw [hc] at h1 ⊢; omega
    have hm := Nat.mod_lt blk (show 0 < Layout.chainN by rw [hc]; norm_num)
    obtain ⟨σ, hσ2, hb⟩ : ∃ σ < 2, blk = σ * Layout.chainN + blk % Layout.chainN :=
      ⟨blk / Layout.chainN, hσ, by rw [Nat.div_add_mod']⟩
    have hmem : ∀ iv ∈ Layout.chainIvs σ, iv ∈ Layout.nodeLayout := fun iv hiv => by
      unfold Layout.nodeLayout
      rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> simp [hiv]
    simp only [nodeBK, h1, ite_true]
    by_cases h2 : blk % Layout.chainN = 0
    · simp only [h2, ite_true]
      exact Layout.ind_of_mem (iv := ⟨.streamStart, σ * Layout.chainN, σ * Layout.chainN + 1⟩)
        (hmem _ (by simp [Layout.chainIvs])) (by simp; omega) (by simp; omega)
    · simp only [h2, ite_false]
      exact Layout.ind_of_mem (iv := ⟨.stream, σ * Layout.chainN + 1, (σ + 1) * Layout.chainN⟩)
        (hmem _ (by simp [Layout.chainIvs])) (by simp; omega) (by simp only; rw [add_mul]; omega)
  by_cases h2 : blk < Layout.wotsBase
  · have hs : Layout.stmtBase = 2 * Layout.chainN := rfl
    have hwb : Layout.wotsBase = Layout.stmtBase + 6 := rfl
    obtain ⟨j, hj, rfl⟩ : ∃ j < 6, blk = Layout.stmtBase + j := ⟨blk - Layout.stmtBase, by omega,
      by omega⟩
    simp only [nodeBK, h1, h2, ite_false, ite_true, Nat.add_sub_cancel_left]
    interval_cases j <;> decide
  by_cases h3 : blk < Layout.wmBase
  · have hwm : Layout.wmBase = Layout.wotsBase + 2 * Layout.wotsSlot := rfl
    have hq : blk - Layout.wotsBase < 2 * 498 := by rw [hwm, hw] at h3; omega
    have hdm := Nat.div_add_mod (blk - Layout.wotsBase) Layout.wotsSlot
    obtain ⟨σ, off, hσ, ho, rfl⟩ : ∃ σ off, σ < 2 ∧ off < Layout.wotsSlot ∧
        blk = Layout.wotsBase + Layout.wotsSlot * σ + off :=
      ⟨(blk - Layout.wotsBase) / Layout.wotsSlot, (blk - Layout.wotsBase) % Layout.wotsSlot,
        by rw [hw]; omega, Nat.mod_lt _ (by rw [hw]; norm_num), by omega⟩
    rw [nodeBK_wots hσ ho]
    exact Layout.ind_wots hσ ho
  · simp only [nodeBK, h1, h2, h3, ite_false]
    exact Layout.ind_of_mem (iv := ⟨.free, Layout.wmBase, Layout.nodeBlocks⟩)
      (by simp [Layout.nodeLayout]) (by simp; omega) (by simpa using h)

/-! ## Part C: B′'s cells -/

/-- **`finPf`'s cells are the node circuit's public cells** (A.7's nine; no padding cells). -/
theorem pfCells_eq : pfCells = Node.pubCells := rfl

/-- The public cells of a kind: the node's nine; a leaf claims none (`finB′`'s `keep isNode`). -/
def cellsOf (κ : Kind) : List ℕ := if κ.isNode then Node.pubCells else []

/-- **The B′ truth over the kind's cells** (A.10 B′, revision 3.12). -/
def truthBN (κ : Kind) (L es : Log) (κ' vRS vStar : F) : Prop :=
  truthB' κ L es (cellsOf κ) κ' vRS vStar

/-- **The cells' batched sum is the public values'** on a word whose cells hold them
(`Node.PubCells`): the B′ truth's cell part is `finB′`'s `κ′²·pubH` part. -/
theorem cells_sum_of_pub {w : Circ.Asg} {vk c₁ c₂ : Digest} (h : Node.PubCells w vk c₁ c₂)
    (κ' : F) :
    ∑ k ∈ range Node.pubCells.length, κ' ^ (k + 2) * w (Node.pubCells.getD k 0) =
      ∑ k ∈ range Node.pubCells.length, κ' ^ (k + 2) * (Node.pubVals vk c₁ c₂).getD k 0 := by
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < Node.pubCells.length := mem_range.1 hk
  congr 1
  rw [List.getD_eq_getElem _ _ hk', ← h, List.getD_eq_getElem _ _ (by simpa using hk'),
    List.getElem_map]

/-! ## Part D: S-G1j's defects under revision 3.13 -/

/-- **Control: E before RS** (revision 3.13, fixing S-G1j defect 1). E4 is phase 21 (its rounds
from position 265, its last challenge `r′₂₂` at 310), E4 end (`f̂(r′) ‖ 0^16`, 32 bytes) phase 22
at 311, RS0 (the `4 × 128` partials, claim 4's `s_{3,i}` included) phase 23 at 312, RS1 (`r″`,
`κ`) from 313: every claim's point is drawn before RS0 absorbs its slices. -/
theorem e4_before_rs0 :
    (piopPhases[21]?.map (·.name)) = some "E4" ∧ (piopPhases[22]?.map (·.name)) = some "E4end" ∧
    (piopPhases[23]?.map (·.name)) = some "RS0" ∧ (piopPhases[24]?.map (·.name)) = some "RS1" ∧
    phStart 21 = 265 ∧ phStart 22 = 311 ∧ phStart 23 = 312 ∧ phStart 24 = 313 ∧
    fsItems[310]? = some .squeeze ∧ fsItems[311]? = some (.absorb 32) ∧
    fsItems[312]? = some (.absorb (4 * 128 * 16)) ∧ fsItems[313]? = some .squeeze := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (rw [phStart, fsStarts_eq]; rfl) | decide +kernel

theorem lRows_cell_ge {r : Circ.Row} (hr : r ∈ Layout.lRows) {t : ℕ × F}
    (ht : t ∈ r.a ++ r.b ++ r.c) : 2 ^ 15 ≤ t.1 ∧ t.1 < 2 ^ 23 := by
  simp only [Layout.lRows, List.mem_map, List.mem_flatMap, List.mem_range, Layout.lBitCells]
    at hr
  obtain ⟨b, ⟨σ, hσ, j, hj, rfl⟩, rfl⟩ := hr
  simp only [Circ.Lin.cell, Circ.Lin.sub, Circ.Lin.smul, List.append_nil, List.mem_append,
    List.mem_cons, List.map_cons, List.map_nil, List.not_mem_nil, or_false] at ht
  simp only [Layout.lBase, Layout.oneCell, Layout.mBase] at ht ⊢
  rcases ht with ((rfl | rfl) | rfl | rfl) | (rfl | rfl) <;> simp <;> omega

/-- `eq` at a point whose coordinates `15 …` are `0` vanishes at every cube point `≥ 2^15`. -/
theorem eq_short_zero {σ : Array F} (hσ : σ.size ≤ 15) (y : Fin (2 ^ 23)) (hy : 2 ^ 15 ≤ y.val) :
    eq (Eval.ptOf 23 σ) (cube y) = 0 := by
  obtain ⟨l, hl, hb⟩ : ∃ l, 15 ≤ l ∧ y.val.testBit l = true := by
    by_contra hc
    push Not at hc
    have := Nat.lt_pow_two_of_testBit y.val fun i hi => by simpa using hc i hi
    omega
  have hl23 : l < 23 := by
    by_contra hc
    have := Nat.testBit_lt_two_pow (show y.val < 2 ^ l from
      lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb] at this; exact absurd this (by decide)
  refine Finset.prod_eq_zero (i := ⟨l, hl23⟩) (mem_univ _) ?_
  have h0 : Eval.ptOf 23 σ ⟨l, hl23⟩ = 0 := by
    simp only [Eval.ptOf, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_none (by omega)]; rfl
  simp [h0, cube, hb]

/-- **Negative control of `finE`'s `evalL` point** (S-G1j defect 2, fixed by revision 3.13): at a
cell point of at most 15 coordinates, which `evalL` reads as 23 (`ptOf 23`: the last 8 are `0`),
`evalL` is `(0, 0, 0)` at every row point, because every L row reads cells `≥ 2^15` (the L bits
at `lBase·128 + …`, M's `one` cell). Revision 3.12's `finLr` (iv) passed Lr4's 15 challenges and
was vacuous; `finE` passes E4's 23 (`finE_evalL_point`). -/
theorem evalL_short_zero (τ σ : Array F) (hσ : σ.size ≤ 15) :
    Eval.evalLImpl Layout.lRows τ σ = (0, 0, 0) := by
  have key : ∀ sel : Circ.Row → Circ.Lin, (∀ r, ∀ t ∈ sel r, t ∈ r.a ++ r.b ++ r.c) →
      Eval.matMLE (Eval.entriesOf sel Layout.lRows) (Eval.ptOf 15 τ) (Eval.ptOf 23 σ) = 0 := by
    intro sel hsel
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : 2 ^ 15 ≤ y.val
    · rw [eq_short_zero hσ y hy]; ring
    · have : Eval.entry (Eval.entriesOf sel Layout.lRows) x y = 0 := by
        unfold Eval.entry
        rw [List.filter_eq_nil_iff.mpr, List.map_nil, List.sum_nil]
        intro e he hc
        simp only [decide_eq_true_eq] at hc
        simp only [Eval.entriesOf, List.mem_flatMap, List.mem_map] at he
        obtain ⟨q, hq, t, ht, rfl⟩ := he
        have := (lRows_cell_ge (List.fst_mem_of_mem_zipIdx hq) (hsel _ t ht)).1
        simp only at hc; omega
      rw [this, mul_zero]
  rw [Eval.evalL_eq, Eval.evalRowsSpec, key _ (fun r t h => by simp [h]),
    key _ (fun r t h => by simp [h]), key _ (fun r t h => by simp [h])]

end FR.Snd
