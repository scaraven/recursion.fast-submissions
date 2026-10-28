-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13; A.6, A.7 generalised; stage S-E12a).
import FRNodeLayout4
import FRNodeTarget

/-!
# The revision 4.1 node's block-kind map, targets and indicators (`N2`/`N4`/`N8`)

3.x's `Layout.nodeLayout`/`Snd.nodeBK`/`Snd.nodeKind` (one node kind, `2^16` blocks) for the three
node kinds of revision 4.1, over `FRNodeLayout4`'s regions. **The interval list is the source of
truth**: `nodeLayout4 κ` lists, in address order, intervals `TIv` that carry a kind and the
targets of their blocks; the block kind `nodeBK4`, the target `nodeKind4`, the indicators `Ind4`
and `Sel4` are read off it. One checked certificate per kind (`layout_contig`: the intervals are
nonempty and tile `[0, blocks)`) gives every per-block fact by a generic argument (`ivAt_spec`,
`ind4_iff`), with no evaluation over blocks.

**H** (blocks of `2^14` positions), in order:
* the signed children's digest chains: `N2`/`N4` the previous node's trace (`23,168` blocks,
  `0x54 ‖ tr`) and the aggregate's (`aggChainLen maxK` blocks, `0x54 ‖ tr₁ ‖ … ‖ tr_maxK`); `N8`
  two aggregates. Block 0 `streamStart`, then `stream` with the full chain's counters (the last
  block is final at `k = maxK`);
* `hashStmt` (`hashA`, `hashB1 tagNode`, `hashB2`) per verifier slot; WOTS per signed child
  (3.x's order, `Layout.wotsIvs`); `WM` (146 per verifier slot, S-0′) and 8 spare: `free`;
* **new (R-4-m2, O-1)**, from `hUsed`, per aggregate `a`, `maxK` blocks: the **candidate final
  blocks** `F_{a,k′}` (`k′ = 1 … maxK − 1`, kind `stream`, the counter and final flag of a stream of
  `aggB k′ = 1 + k′(S − 1)` bytes: its last block), then `c_A`'s `hashA` block (`leafStmt e n`).
  An aggregate of `k < maxK` segments ends at `F_{a,k}` (its `h_in` and message prefix are the main
  chain's, its padding zero: `NodeResid4.aggPad`); `k = maxK` ends at the main chain's last block;
* then `free` to the end (L and M are `free`, `A₀ = B₀ = I`, as 3.x).

**Indicators and targets for the PIOP** (`FRSoundness4P4aNames.zlm4`'s `indN`/`etN`, P4b's `kf`,
`cells`): `indN4`, `etN4`, `kf4`, `cells4`, with `hcells4` (nine cells, inside `f`), `indN4_chain`
(no node block is `chain`: `ZLM4.IndKinds`), `kf4_eq` (the kind factor is `β^(index of the
block's kind)`), `nodeKind4_none_iff` (`free` ⇔ no target), `nodeKind4_kind` (a block's target
is of its kind's form), the chain mask `chainLk4` and the WOTS link families' rebased blocks
(`srcB4`, `mirB4`, `mir4_fits`).
-/

namespace FR
namespace N4c
open RecursionFast Rev4 Kinds FR.Stream

/-! ## Numbers (literals, with their fidelity to `FRShape4`/`FRNodeLayout4`) -/

/-- One trace's stream `0x54 ‖ traceBytes tr` at `seq4`, in bytes. -/
def segB : ℕ := 1482752
/-- Its digest chain's blocks. -/
def cLen : ℕ := 23168
/-- The aggregate stream `0x54 ‖ tr₁ ‖ … ‖ tr_k`, in bytes. -/
def aggB (k : ℕ) : ℕ := 1 + k * (segB - 1)
/-- Its digest chain's blocks. -/
def aggL (k : ℕ) : ℕ := (aggB k + 63) / 64

theorem segB_eq : segB = streamBytesOf seq4 := streamBytesOf_seq4.symm
theorem cLen_eq : cLen = chainLenOf seq4 := chainLenOf_seq4.1.symm
theorem aggL_eq (k : ℕ) : aggL k = aggChainLen k := by
  simp only [aggL, aggB, aggChainLen, segB_eq]

/-- Aggregate children: `N2`/`N4` one (signed child 1), `N8` two. -/
def nAgg (κ : NodeKind) : ℕ := if κ.hasPrev then 1 else 2
/-- Signed child `σ` is an aggregate. -/
def isAgg (κ : NodeKind) (σ : ℕ) : Bool := !κ.hasPrev || σ != 0
/-- Aggregate `a`'s signed child. -/
def aggChild (κ : NodeKind) (a : ℕ) : ℕ := if κ.hasPrev then 1 else a

/-- Signed child `σ`'s main chain: blocks and stream bytes. -/
def chLen (κ : NodeKind) (σ : ℕ) : ℕ := if isAgg κ σ then aggL κ.maxK else cLen
def chBytes (κ : NodeKind) (σ : ℕ) : ℕ := if isAgg κ σ then aggB κ.maxK else segB
/-- Its first block (`σ < 2`). -/
def chBase (κ : NodeKind) (σ : ℕ) : ℕ := σ * chLen κ 0
/-- `hashStmt`'s first block. -/
def stmtB (κ : NodeKind) : ℕ := chLen κ 0 + chLen κ 1
/-- Signed child `σ`'s first WOTS block. -/
def wotsB (κ : NodeKind) (σ : ℕ) : ℕ := stmtB κ + 3 * κ.vslots + wotsSlot4 * σ
/-- Signed child `σ`'s first `WM` block (its WOTS run's mirrors). -/
def wmB (κ : NodeKind) (σ : ℕ) : ℕ := wotsB κ 2 + wmSlot4 * σ
/-- H's used blocks (`FRNodeLayout4.hUsed`, `hUsedN_eq`). -/
def hUsedN (κ : NodeKind) : ℕ := wotsB κ 2 + wmSlot4 * κ.vslots + 8
/-- Aggregate `a`'s candidate final blocks and `c_A` block start here. -/
def finB (κ : NodeKind) (a : ℕ) : ℕ := hUsedN κ + a * κ.maxK
/-- The end of H. -/
def hEnd (κ : NodeKind) : ℕ := finB κ (nAgg κ)
/-- `c_A`'s `hashA` block. -/
def cAB (κ : NodeKind) (a : ℕ) : ℕ := finB κ a + (κ.maxK - 1)

theorem hUsedN_eq (κ : NodeKind) : hUsedN κ = κ.hUsed := by
  have h := hUsed_eq
  cases κ <;> simp only [h] <;> rfl

/-! ## Intervals -/

/-- **A block interval** `[lo, hi)` of one kind; `tgt o` is block `lo + o`'s public target. -/
structure TIv where
  kind : BlockKind
  lo : ℕ
  hi : ℕ
  tgt : ℕ → Option Block.Target

/-- Signed child `σ`'s main chain. -/
def chainIvs (κ : NodeKind) (σ : ℕ) : List TIv :=
  [⟨.streamStart, chBase κ σ, chBase κ σ + 1, fun _ => some streamStart.target⟩,
   ⟨.stream, chBase κ σ + 1, chBase κ σ + chLen κ σ,
     fun o => some (streamTarget (chBytes κ σ) (o + 1))⟩]

/-- `hashStmt`'s blocks A, B1, B2 per verifier slot. -/
def stmtIvs (κ : NodeKind) : List TIv :=
  (List.range κ.vslots).flatMap fun v =>
    [⟨.hashA, stmtB κ + 3 * v, stmtB κ + 3 * v + 1, fun _ => some hashA.target⟩,
     ⟨.hashB1, stmtB κ + 3 * v + 1, stmtB κ + 3 * v + 2, fun _ => some (hashB1 RecursionFast.tagNode).target⟩,
     ⟨.hashB2, stmtB κ + 3 * v + 2, stmtB κ + 3 * v + 3, fun _ => some hashB2.target⟩]

/-- Signed child `σ`'s WOTS run: 3.x's intervals (`Layout.wotsIvs 0`) rebased, with 3.x's targets
(`NodeT.wotsTgt` of the WOTS offset). -/
def wotsIvs (κ : NodeKind) (σ : ℕ) : List TIv :=
  (Layout.wotsIvs 0).map fun iv =>
    ⟨iv.kind, iv.lo - Layout.wotsBase + wotsB κ σ, iv.hi - Layout.wotsBase + wotsB κ σ,
      fun o => some (NodeT.wotsTgt (iv.lo - Layout.wotsBase + o))⟩

/-- Aggregate `a`'s candidate final blocks (`k′ = j + 1`) and its `c_A` block. -/
def tailIvs (κ : NodeKind) (a : ℕ) : List TIv :=
  (List.range (κ.maxK - 1)).map (fun j => (⟨.stream, finB κ a + j, finB κ a + j + 1,
    fun _ => some (streamTarget (aggB (j + 1)) (aggL (j + 1) - 1))⟩ : TIv)) ++
  [⟨.hashA, cAB κ a, cAB κ a + 1, fun _ => some hashA.target⟩]

/-- A `free` interval. -/
def freeIv (lo hi : ℕ) : TIv := ⟨.free, lo, hi, fun _ => none⟩

/-- **`nodeLayout4 κ`**: the node's intervals in address order. -/
def nodeLayout4 (κ : NodeKind) : List TIv :=
  chainIvs κ 0 ++ chainIvs κ 1 ++ stmtIvs κ ++ wotsIvs κ 0 ++ wotsIvs κ 1 ++
    [freeIv (wmB κ 0) (hUsedN κ)] ++ (List.range (nAgg κ)).flatMap (tailIvs κ) ++
    [freeIv (hEnd κ) κ.blocks]

/-! ## Reading the list -/

/-- Block `blk` lies in `iv`. -/
def TIv.mem (iv : TIv) (blk : ℕ) : Bool := iv.lo ≤ blk && blk < iv.hi

/-- **The intervals tile `[a, b)`**: each is nonempty and starts where the previous ended. -/
def contig : List TIv → ℕ → ℕ → Bool
  | [], a, b => a == b
  | iv :: ivs, a, b => iv.lo == a && decide (iv.lo < iv.hi) && contig ivs iv.hi b

/-- The interval holding `blk`. -/
def ivAt (ivs : List TIv) (blk : ℕ) : Option TIv := ivs.find? fun iv => iv.mem blk

/-- **The block kind** (A.6's class) of block `blk` of a `κ` node. -/
def nodeBK4 (κ : NodeKind) (blk : ℕ) : BlockKind := ((ivAt (nodeLayout4 κ) blk).map TIv.kind).getD .free

/-- **The public target** of block `blk` (`none`: a `free` block). -/
def nodeKind4 (κ : NodeKind) (blk : ℕ) : Option Block.Target :=
  (ivAt (nodeLayout4 κ) blk).bind fun iv => iv.tgt (blk - iv.lo)

/-- **`Ind_kind`** (A.6): block `blk` is of kind `b`. -/
def Ind4 (κ : NodeKind) (b : BlockKind) (blk : ℕ) : Bool :=
  (nodeLayout4 κ).any fun iv => iv.kind == b && iv.mem blk

/-- **`Sel`**: block `blk` is in some interval. -/
def Sel4 (κ : NodeKind) (blk : ℕ) : Bool := (nodeLayout4 κ).any fun iv => iv.mem blk

/-- A kind's intervals (the verifier's kind-weight ranges). -/
def kindIvs4 (κ : NodeKind) (b : BlockKind) : List (ℕ × ℕ) :=
  ((nodeLayout4 κ).filter fun iv => iv.kind == b).map fun iv => (iv.lo, iv.hi)

/-! ## The certificates -/

/-- **The intervals tile the node** (checked per kind on the 110 endpoints at most). -/
theorem layout_contig (κ : NodeKind) : contig (nodeLayout4 κ) 0 κ.blocks = true := by
  cases κ <;> decide

/-- No interval is `chain` (a node block is never a leaf chain block). -/
theorem layout_no_chain (κ : NodeKind) : (nodeLayout4 κ).all (fun iv => iv.kind != .chain) = true := by
  cases κ <;> decide

theorem layout_length : (nodeLayout4 .N2).length = 89 ∧ (nodeLayout4 .N4).length = 97 ∧
    (nodeLayout4 .N8).length = 110 := by decide

/-! ## Generic facts on a tiling -/

theorem contig_bounds : ∀ {ivs : List TIv} {a b : ℕ}, contig ivs a b = true →
    a ≤ b ∧ ∀ iv ∈ ivs, a ≤ iv.lo ∧ iv.lo < iv.hi ∧ iv.hi ≤ b
  | [], a, b, h => ⟨by simp [contig] at h; omega, by simp⟩
  | iv :: ivs, a, b, h => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hlt⟩, h⟩ := h
    obtain ⟨hb, hm⟩ := contig_bounds h
    refine ⟨by omega, fun iv' hiv' => ?_⟩
    rcases List.mem_cons.1 hiv' with rfl | hiv'
    · exact ⟨le_rfl, hlt, hb⟩
    · have := hm iv' hiv'; omega

/-- **Covering**: every block of `[a, b)` lies in some interval. -/
theorem contig_cover : ∀ {ivs : List TIv} {a b : ℕ}, contig ivs a b = true → ∀ blk, a ≤ blk → blk < b →
    ∃ iv ∈ ivs, iv.mem blk = true
  | [], a, b, h, blk, h1, h2 => by simp [contig] at h; omega
  | iv :: ivs, a, b, h, blk, h1, h2 => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, -⟩, h⟩ := h
    by_cases hb : blk < iv.hi
    · exact ⟨iv, List.mem_cons_self .., by simp [TIv.mem, h1, hb]⟩
    · obtain ⟨iv', hm, hk⟩ := contig_cover h blk (by omega) h2
      exact ⟨iv', List.mem_cons_of_mem _ hm, hk⟩

/-- **Uniqueness**: two intervals holding `blk` are the same. -/
theorem contig_unique : ∀ {ivs : List TIv} {a b : ℕ}, contig ivs a b = true → ∀ {blk : ℕ} {i j : TIv},
    i ∈ ivs → j ∈ ivs → i.mem blk = true → j.mem blk = true → i = j
  | [], _, _, _, _, _, _, hi, _, _, _ => by simp at hi
  | iv :: ivs, a, b, h, blk, i, j, hi, hj, hki, hkj => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, -⟩, h⟩ := h
    have hrest := (contig_bounds h).2
    simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hki hkj
    rcases List.mem_cons.1 hi with hi | hi <;> rcases List.mem_cons.1 hj with hj | hj
    · rw [hi, hj]
    · have := hrest j hj; rw [hi] at hki; omega
    · have := hrest i hi; rw [hj] at hkj; omega
    · exact contig_unique h hi hj (by simp [TIv.mem]; omega) (by simp [TIv.mem]; omega)

/-- **`ivAt` on a tiling**: the interval holding `blk`, and only it. -/
theorem ivAt_spec {ivs : List TIv} {a b : ℕ} (h : contig ivs a b = true) {blk : ℕ} (h1 : a ≤ blk)
    (h2 : blk < b) : ∃ iv ∈ ivs, iv.mem blk = true ∧ ivAt ivs blk = some iv ∧
      ∀ j ∈ ivs, j.mem blk = true → j = iv := by
  obtain ⟨iv, hm, hk⟩ := contig_cover h blk h1 h2
  obtain ⟨iv', hf⟩ : ∃ iv', ivAt ivs blk = some iv' := by
    rcases e : ivAt ivs blk with _ | iv'
    · exact absurd hk (by simpa using List.find?_eq_none.1 e iv hm)
    · exact ⟨iv', rfl⟩
  have hm' := List.mem_of_find?_eq_some hf
  have hk' : iv'.mem blk = true := by simpa using List.find?_some hf
  exact ⟨iv', hm', hk', hf, fun j hj hkj => contig_unique h hj hm' hkj hk'⟩

/-! ## The node's per-block facts -/

/-- Block `blk < blocks` of a `κ` node: its interval. -/
theorem layout_at (κ : NodeKind) {blk : ℕ} (h : blk < κ.blocks) :
    ∃ iv ∈ nodeLayout4 κ, iv.mem blk = true ∧ ivAt (nodeLayout4 κ) blk = some iv ∧
      nodeBK4 κ blk = iv.kind ∧ ∀ j ∈ nodeLayout4 κ, j.mem blk = true → j = iv := by
  obtain ⟨iv, hm, hk, hf, hu⟩ := ivAt_spec (layout_contig κ) (Nat.zero_le blk) h
  exact ⟨iv, hm, hk, hf, by simp [nodeBK4, hf], hu⟩

/-- **`Ind4` is `nodeBK4`'s class** on every block of the node. -/
theorem ind4_iff (κ : NodeKind) {blk : ℕ} (h : blk < κ.blocks) (b : BlockKind) :
    Ind4 κ b blk = true ↔ b = nodeBK4 κ blk := by
  obtain ⟨iv, hm, hk, -, hb, hu⟩ := layout_at κ h
  rw [hb]
  constructor
  · intro hI
    obtain ⟨j, hj, hj'⟩ := List.any_eq_true.1 hI
    simp only [Bool.and_eq_true, beq_iff_eq] at hj'
    rw [← hj'.1, hu j hj hj'.2]
  · rintro rfl
    exact List.any_eq_true.2 ⟨iv, hm, by simp [hk]⟩

/-- **`Sel4 ≡ 1`** on the node. -/
theorem sel4_true (κ : NodeKind) {blk : ℕ} (h : blk < κ.blocks) : Sel4 κ blk = true := by
  obtain ⟨iv, hm, hk, -⟩ := layout_at κ h
  exact List.any_eq_true.2 ⟨iv, hm, hk⟩

/-- **A node block is never `chain`.** -/
theorem nodeBK4_ne_chain (κ : NodeKind) (blk : ℕ) : nodeBK4 κ blk ≠ .chain := by
  unfold nodeBK4
  rcases e : ivAt (nodeLayout4 κ) blk with _ | iv
  · simp
  · have hm := List.mem_of_find?_eq_some e
    have := List.all_eq_true.1 (layout_no_chain κ) iv hm
    simpa using this

/-- The kind intervals are `Ind4`'s. -/
theorem ind4_kindIvs (κ : NodeKind) (b : BlockKind) (blk : ℕ) :
    Ind4 κ b blk = (kindIvs4 κ b).any fun p => p.1 ≤ blk && blk < p.2 := by
  simp only [Ind4, kindIvs4, List.any_map, List.any_filter, TIv.mem, Function.comp_def]

/-! ## Targets -/

/-- **The targets of a kind** (the forms `kindPins` reads: each pins its kind's `zeroRows`). -/
def KindTgt : BlockKind → Block.Target → Prop
  | .stream, t => ∃ L i, t = streamTarget L i
  | .streamStart, t => t = streamStart.target
  | .streamEnd41, t => t = streamEnd41.target
  | .hashA, t => t = hashA.target
  | .hashB1, t => ∃ tag, t = (hashB1 tag).target
  | .hashB2, t => t = hashB2.target
  | .w43, t => ∃ i s, t = (w43 i s).target
  | .chain, _ => False
  | .free, _ => False

/-- An interval's targets are of its kind's form (`free`: none). -/
def TIv.TgtOk (iv : TIv) : Prop :=
  ∀ o < iv.hi - iv.lo, (iv.kind = .free → iv.tgt o = none) ∧
    (iv.kind ≠ .free → ∃ t, iv.tgt o = some t ∧ KindTgt iv.kind t)

set_option maxRecDepth 8000 in
/-- 3.x's WOTS offsets: `wotsTgt o` is of `wotsKindAt o`'s form. -/
theorem wotsTgt_kind (o : ℕ) : KindTgt (Layout.wotsKindAt o) (NodeT.wotsTgt o) := by
  unfold Layout.wotsKindAt NodeT.wotsTgt
  by_cases h1 : o < 399
  · rw [if_pos h1, if_pos h1]; exact ⟨_, _, rfl⟩
  rw [if_neg h1, if_neg h1]
  by_cases h2 : o = 399
  · rw [if_pos h2, if_pos h2]; exact ⟨_, rfl⟩
  rw [if_neg h2, if_neg h2]
  by_cases h3 : o < 465
  · rw [if_pos h3, if_pos h3]; exact ⟨_, _, rfl⟩
  rw [if_neg h3, if_neg h3]
  by_cases h4 : o = 465
  · rw [if_pos h4, if_pos h4]; exact (rfl : streamEnd41.target = streamEnd41.target)
  rw [if_neg h4, if_neg h4]
  by_cases h5 : (o - 466) % 2 = 0
  · rw [if_pos h5, if_pos h5]; exact ⟨_, rfl⟩
  · rw [if_neg h5, if_neg h5]; exact (rfl : hashB2.target = hashB2.target)

theorem wotsIvs0_kind {iv : Layout.Iv} (h : iv ∈ Layout.wotsIvs 0) {o : ℕ} (ho : o < iv.hi - iv.lo) :
    Layout.wotsKindAt (iv.lo - Layout.wotsBase + o) = iv.kind := by
  have hw : Layout.wotsBase = 46298 := rfl
  simp only [Layout.wotsIvs, Layout.wotsSlot, mul_zero, add_zero, List.mem_append, List.mem_cons,
    List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl | rfl) | ⟨t, ht, rfl | rfl⟩ <;>
    simp only [hw, Layout.wotsKindAt] at ho ⊢ <;> split_ifs <;> first | rfl | omega

theorem wotsKindAt_ne_free (o : ℕ) : Layout.wotsKindAt o ≠ .free := by
  unfold Layout.wotsKindAt; split_ifs <;> simp

/-- **Every interval's targets are of its kind's form.** -/
theorem layout_tgtOk (κ : NodeKind) : ∀ iv ∈ nodeLayout4 κ, iv.TgtOk := by
  have hch : ∀ σ, ∀ iv ∈ chainIvs κ σ, iv.TgtOk := fun σ iv h => by
    simp only [chainIvs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> intro o _ <;> simp [KindTgt]
  have hst : ∀ iv ∈ stmtIvs κ, iv.TgtOk := fun iv h => by
    simp only [stmtIvs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨v, -, rfl | rfl | rfl⟩ := h <;> intro o _ <;> simp [KindTgt]; exact ⟨_, rfl⟩
  have hw : ∀ σ, ∀ iv ∈ wotsIvs κ σ, iv.TgtOk := fun σ iv h => by
    simp only [wotsIvs, List.mem_map] at h
    obtain ⟨iv₀, h₀, rfl⟩ := h
    have hlo : Layout.wotsBase ≤ iv₀.lo := by
      simp only [Layout.wotsIvs, Layout.wotsSlot, mul_zero, add_zero, List.mem_append, List.mem_cons,
        List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at h₀
      rcases h₀ with (rfl | rfl | rfl | rfl) | ⟨t, ht, rfl | rfl⟩ <;> simp <;> omega
    intro o ho
    have ho' : o < iv₀.hi - iv₀.lo := by simp only at ho; omega
    have hk := wotsIvs0_kind h₀ ho'
    refine ⟨fun hf => absurd (hk.trans hf) (wotsKindAt_ne_free _), fun _ => ⟨_, rfl, ?_⟩⟩
    simp only
    rw [← hk]; exact wotsTgt_kind _
  have hfr : ∀ lo hi, (freeIv lo hi).TgtOk := fun lo hi o _ => by simp [freeIv]
  have htl : ∀ a, ∀ iv ∈ tailIvs κ a, iv.TgtOk := fun a iv h => by
    simp only [tailIvs, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with ⟨j, -, rfl⟩ | rfl <;> intro o _ <;> simp [KindTgt]
  intro iv h
  simp only [nodeLayout4, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at h
  rcases h with ((((((h | h) | h) | h) | h) | rfl) | ⟨a, -, h⟩) | rfl
  · exact hch 0 iv h
  · exact hch 1 iv h
  · exact hst iv h
  · exact hw 0 iv h
  · exact hw 1 iv h
  · exact hfr _ _
  · exact htl a iv h
  · exact hfr _ _

/-- **A block's target is of its kind's form.** -/
theorem nodeKind4_kind {κ : NodeKind} {blk : ℕ} {t : Block.Target} (h : nodeKind4 κ blk = some t) :
    KindTgt (nodeBK4 κ blk) t := by
  unfold nodeKind4 at h
  rcases e : ivAt (nodeLayout4 κ) blk with _ | iv
  · simp [e] at h
  · simp only [e, Option.bind_some] at h
    have hm := List.mem_of_find?_eq_some e
    have hk : iv.mem blk = true := by simpa using List.find?_some e
    simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk
    have hb : nodeBK4 κ blk = iv.kind := by simp [nodeBK4, e]
    rw [hb]
    have := layout_tgtOk κ iv hm (blk - iv.lo) (by omega)
    by_cases hf : iv.kind = .free
    · rw [this.1 hf] at h; cases h
    · obtain ⟨t', h', hk'⟩ := this.2 hf
      rw [h'] at h; cases h; exact hk'

/-- **`free` ⇔ no target** on the node's blocks. -/
theorem nodeKind4_none_iff (κ : NodeKind) {blk : ℕ} (hb : blk < κ.blocks) :
    nodeKind4 κ blk = none ↔ nodeBK4 κ blk = .free := by
  obtain ⟨iv, hm, hk, hf, hbk, -⟩ := layout_at κ hb
  simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk
  have := layout_tgtOk κ iv hm (blk - iv.lo) (by omega)
  rw [nodeKind4, hf, Option.bind_some, hbk]
  by_cases h : iv.kind = .free
  · simp [h, this.1 h]
  · obtain ⟨t, ht, -⟩ := this.2 h
    simp [h, ht]

/-! ## Membership gives the kind and the target -/

theorem layout_bounds (κ : NodeKind) {iv : TIv} (h : iv ∈ nodeLayout4 κ) : iv.lo < iv.hi ∧ iv.hi ≤ κ.blocks :=
  ((contig_bounds (layout_contig κ)).2 iv h).2

/-- **A listed interval decides its blocks' kind** (by uniqueness). -/
theorem bk_of_mem {κ : NodeKind} {iv : TIv} (h : iv ∈ nodeLayout4 κ) {blk : ℕ} (hk : iv.mem blk = true) :
    nodeBK4 κ blk = iv.kind := by
  have hb : blk < κ.blocks := by
    have := layout_bounds κ h; simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk; omega
  obtain ⟨iv', hm', hk', -, hbk, hu⟩ := layout_at κ hb
  rw [hbk, hu iv h hk]

/-- **… and their targets.** -/
theorem tgt_of_mem {κ : NodeKind} {iv : TIv} (h : iv ∈ nodeLayout4 κ) {blk : ℕ} (hk : iv.mem blk = true) :
    nodeKind4 κ blk = iv.tgt (blk - iv.lo) := by
  have hb : blk < κ.blocks := by
    have := layout_bounds κ h; simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk; omega
  obtain ⟨iv', hm', hk', hf, -, hu⟩ := layout_at κ hb
  rw [nodeKind4, hf, Option.bind_some, hu iv h hk]

/-! ## Region facts -/

/-- **H fits before L** (with the new tail): `hEnd ≤ lBase`, so H, L, M are disjoint
(`regions_fit`). `N2` 70,957 ≤ 71,168; `N4` 117,593 ≤ 117,760; `N8` 187,548 ≤ 187,648. -/
theorem hEnd_le (κ : NodeKind) : hEnd κ ≤ κ.lBase ∧ hUsedN κ + nAgg κ * κ.maxK = hEnd κ := by
  refine ⟨?_, by simp [hEnd, finB]⟩
  rw [NodeKind.lBase, ← hUsedN_eq]; cases κ <;> decide

theorem hEnd_eq : hEnd .N2 = 70957 ∧ hEnd .N4 = 117593 ∧ hEnd .N8 = 187548 := by decide

/-- A candidate final block is **the last block of a stream of `aggB k′` bytes**: its target's
counter is `aggB k′` and its final flag is set. -/
theorem aggL_nBlocks (k : ℕ) : nBlocks (aggB k) = aggL k := by
  simp only [nBlocks, aggL, aggB]; omega

theorem ctr_final (k : ℕ) :
    ctrAt (aggB k) (aggL k - 1) = aggB k ∧ flagAt (aggB k) (aggL k - 1) = 0xFFFFFFFF := by
  have h1 : 1 ≤ aggL k := by simp only [aggL, aggB]; omega
  simp only [ctrAt, flagAt, aggL_nBlocks k, Nat.sub_add_cancel h1, if_true, and_self]

/-! ## The indicators, the targets, the kind factor (the PIOP's parameters) -/

/-- The index of a kind in `blockKinds` (3.x's `Snd.bkIdx`). -/
def bkIdx4 : BlockKind → Fin 9
  | .chain => 0 | .stream => 1 | .streamStart => 2 | .streamEnd41 => 3 | .hashA => 4
  | .hashB1 => 5 | .hashB2 => 6 | .w43 => 7 | .free => 8

theorem bkIdx4_getD (b : BlockKind) : blockKinds.getD (bkIdx4 b).val .free = b := by cases b <;> rfl

/-- **`indN`** (`zlm4`'s node indicators): `1` when kind `j` is the block's. -/
def indN4 (κ : NodeKind) (j : Fin 9) (t : ℕ) : F := if blockKinds.getD j.val .free = nodeBK4 κ t then 1 else 0

/-- **`etN`** (`zlm4`'s node targets): the block's target bits (`NodeT.tgtE`), `0` on `free`. -/
def etN4 (κ : NodeKind) (t : ℕ) (p : Fin (2 ^ 14)) : F :=
  match nodeKind4 κ t with
  | some tgt => NodeT.tgtE tgt p.val
  | none => 0

/-- **`kf`** (P4b's kind factor): `B_β(t) = Σ_{i<8} β^i Ind_{nodeKinds[i]}(t)`. -/
def kf4 (κ : NodeKind) (β : F) (t : ℕ) : F :=
  ∑ i ∈ Finset.range 8, β ^ i * (if blockKinds.tail.getD i .free = nodeBK4 κ t then 1 else 0)

/-- No node indicator is `chain` (`ZLM4.IndKinds`' node half). -/
theorem indN4_chain (κ : NodeKind) (t : ℕ) : indN4 κ 0 t = 0 := by
  have := nodeBK4_ne_chain κ t
  simp only [indN4]; rw [if_neg (fun h => this (h.symm.trans rfl))]

/-- **One indicator per block**: kind `j`'s is `1` exactly at the block's kind's index. -/
theorem indN4_eq (κ : NodeKind) (j : Fin 9) (t : ℕ) :
    indN4 κ j t = if j = bkIdx4 (nodeBK4 κ t) then 1 else 0 := by
  unfold indN4
  congr 1
  apply propext
  constructor
  · intro h; rw [← h]; fin_cases j <;> rfl
  · rintro rfl; exact bkIdx4_getD _

theorem kf_sum (β : F) (b : BlockKind) (hb : b ≠ .chain) :
    ∑ i ∈ Finset.range 8, β ^ i * (if blockKinds.tail.getD i .free = b then 1 else 0) =
      β ^ ((bkIdx4 b).val - 1) := by
  cases b <;> first | exact absurd rfl hb | simp [Finset.sum_range_succ, blockKinds, bkIdx4]

/-- **The kind factor in closed form**: `β^(i)` with `i` the block's kind's index in `nodeKinds`. -/
theorem kf4_eq (κ : NodeKind) (β : F) (t : ℕ) : kf4 κ β t = β ^ ((bkIdx4 (nodeBK4 κ t)).val - 1) :=
  kf_sum β _ (nodeBK4_ne_chain κ t)

/-! ## The public cells (A.7 per kind; P4b's `hcells`) -/

/-- Aggregate index of signed child `σ` (`N2`/`N4`: child 1 is aggregate 0). -/
def aggOf (κ : NodeKind) (σ : ℕ) : ℕ := if κ.hasPrev then σ - 1 else σ

/-- Signed child `σ`'s seed payload element `e` (the stream's element `1 + e`, as 3.x's
`Node.seedCell`): `e = 0, 1` are `vk`'s halves, `e = 2, 3` the child statement's. -/
def seedC (κ : NodeKind) (σ e : ℕ) : ℕ := (chBase κ σ + (1 + e) / 4) * 128 + 4 + (1 + e) % 4

/-- **Signed child `σ`'s statement cells**: a previous node's seed payload; an aggregate's `c_A`
block's output `h_out` (elements 2, 3; O-1: the aggregate's statement `leafStmt e n` is not in its
trace). -/
def stC (κ : NodeKind) (σ h : ℕ) : ℕ := if isAgg κ σ then cAB κ (aggOf κ σ) * 128 + 2 + h else seedC κ σ (2 + h)

/-- **The nine public cells** (`pubVals`' order): M's `one`, then per signed child `vk`'s and its
statement's halves. -/
def cells4 (κ : NodeKind) : List ℕ :=
  κ.oneCell :: (List.range 2).flatMap fun σ => [seedC κ σ 0, seedC κ σ 1, stC κ σ 0, stC κ σ 1]

/-- **`hcells`** (P4b's `single_B4`): nine cells, inside `f` (`2^(m − 7)` cells), distinct. -/
theorem hcells4 (κ : NodeKind) :
    (cells4 κ).length = 9 ∧ (∀ c ∈ cells4 κ, c < 2 ^ (κ.m - 7)) ∧ (cells4 κ).Nodup := by
  cases κ <;> decide

/-! ## The chain mask and the link families (S, `linkWAll`) -/

/-- **The chain mask**: block `y`'s `h_out` is block `y + 1`'s `h_in` (both in one main chain). -/
def chainLk4 (κ : NodeKind) (y : ℕ) : Bool :=
  decide (y + 1 < chLen κ 0) || (decide (chLen κ 0 ≤ y) && decide (y + 1 < chLen κ 0 + chLen κ 1))

theorem chainIvs_mem (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) : ∀ iv ∈ chainIvs κ σ, iv ∈ nodeLayout4 κ := by
  intro iv h
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> simp [nodeLayout4, h]

/-- **A masked block's successor is a `stream` block** (its `h_in` is not pinned: `zeroRows`). -/
theorem chainLk4_stream {κ : NodeKind} {y : ℕ} (h : chainLk4 κ y = true) : nodeBK4 κ (y + 1) = .stream := by
  simp only [chainLk4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hpos : 0 < chLen κ 0 := by cases κ <;> decide
  rcases h with h | ⟨h1, h2⟩
  · exact bk_of_mem (iv := ⟨.stream, chBase κ 0 + 1, chBase κ 0 + chLen κ 0,
      fun o => some (streamTarget (chBytes κ 0) (o + 1))⟩)
      (chainIvs_mem κ (σ := 0) (by norm_num) _ (by simp [chainIvs]))
      (by simp [TIv.mem, chBase]; omega)
  · exact bk_of_mem (iv := ⟨.stream, chBase κ 1 + 1, chBase κ 1 + chLen κ 1,
      fun o => some (streamTarget (chBytes κ 1) (o + 1))⟩)
      (chainIvs_mem κ (σ := 1) (by norm_num) _ (by simp [chainIvs]))
      (by simp [TIv.mem, chBase]; omega)

/-- 3.x's WOTS intervals as a tiling of `[wotsBase, wotsBase + 498)`. -/
def wots0 : List TIv := (Layout.wotsIvs 0).map fun iv => ⟨iv.kind, iv.lo, iv.hi, fun _ => none⟩

theorem wots0_contig : contig wots0 Layout.wotsBase (Layout.wotsBase + wotsSlot4) = true := by decide

/-- **The WOTS order is 3.x's** (`ind_wots`): block `off` of signed child `σ`'s run has kind
`wotsKindAt off`. -/
theorem nodeBK4_wots (κ : NodeKind) {σ off : ℕ} (hσ : σ < 2) (ho : off < wotsSlot4) :
    nodeBK4 κ (wotsB κ σ + off) = Layout.wotsKindAt off := by
  obtain ⟨iv, hm, hk⟩ := contig_cover wots0_contig (Layout.wotsBase + off) (by omega) (by omega)
  simp only [wots0, List.mem_map] at hm
  obtain ⟨iv₀, h₀, rfl⟩ := hm
  simp only [TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk
  have hw : Layout.wotsBase ≤ iv₀.lo := by
    simp only [Layout.wotsIvs, Layout.wotsSlot, mul_zero, add_zero, List.mem_append, List.mem_cons,
      List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at h₀
    rcases h₀ with (rfl | rfl | rfl | rfl) | ⟨t, ht, rfl | rfl⟩ <;> simp <;> omega
  have hmem : (⟨iv₀.kind, iv₀.lo - Layout.wotsBase + wotsB κ σ, iv₀.hi - Layout.wotsBase + wotsB κ σ,
      fun o => some (NodeT.wotsTgt (iv₀.lo - Layout.wotsBase + o))⟩ : TIv) ∈ nodeLayout4 κ := by
    have : _ ∈ wotsIvs κ σ := List.mem_map.2 ⟨iv₀, h₀, rfl⟩
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> simp [nodeLayout4, this]
  rw [bk_of_mem hmem (by simp [TIv.mem]; omega)]
  have := wotsIvs0_kind h₀ (o := Layout.wotsBase + off - iv₀.lo) (by omega)
  rw [← this, show iv₀.lo - Layout.wotsBase + (Layout.wotsBase + off - iv₀.lo) = off by omega]

/-- Link family `f`'s source `t` of signed child `σ` (`NodeT.srcB` rebased). -/
def srcB4 (κ : NodeKind) (σ f t : ℕ) : ℕ := wotsB κ σ + (NodeT.fam f).src t
/-- Its mirror's block (`NodeT.mirB` rebased: `WM` source `g` in block `wmB σ + ⌊g/4⌋`). -/
def mirB4 (κ : NodeKind) (σ f t : ℕ) : ℕ := wmB κ σ + (NodeT.fam f).mir t / 4

/-- **The mirrors lie in `WM`**, a `free` interval after both WOTS runs and before the tail. -/
theorem mir4_fits (κ : NodeKind) {σ g : ℕ} (hσ : σ < 2) (hg : g < Layout.mirSources) :
    wotsB κ 2 ≤ wmB κ σ + g / 4 ∧ wmB κ σ + g / 4 < hUsedN κ ∧ nodeBK4 κ (wmB κ σ + g / 4) = .free := by
  have hv : 2 ≤ κ.vslots := by cases κ <;> decide
  simp only [Layout.mirSources] at hg
  have h1 : wotsB κ 2 ≤ wmB κ σ + g / 4 := by simp only [wmB]; omega
  have h2 : wmB κ σ + g / 4 < hUsedN κ := by
    simp only [wmB, hUsedN, wmSlot4]
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> omega
  have h0 : wmB κ 0 ≤ wmB κ σ := by simp [wmB]
  refine ⟨h1, h2, bk_of_mem (iv := freeIv (wmB κ 0) (hUsedN κ)) (by simp [nodeLayout4]) ?_⟩
  simp only [TIv.mem, freeIv, Bool.and_eq_true]
  exact ⟨decide_eq_true (by omega), decide_eq_true h2⟩

/-! ## Controls -/

/-- (+) The kinds at the regions' first blocks (`N4`): the previous node's chain, the aggregate's,
`hashStmt`, WOTS, `WM`, the candidate final block `F_{0,1}`, `c_A`'s `hashA`, M. -/
theorem nodeBK4_controls :
    nodeBK4 .N4 0 = .streamStart ∧ nodeBK4 .N4 1 = .stream ∧ nodeBK4 .N4 cLen = .streamStart ∧
    nodeBK4 .N4 (stmtB .N4) = .hashA ∧ nodeBK4 .N4 (stmtB .N4 + 4) = .hashB1 ∧
    nodeBK4 .N4 (wotsB .N4 1 + 465) = .streamEnd41 ∧ nodeBK4 .N4 (wmB .N4 0) = .free ∧
    nodeBK4 .N4 (finB .N4 0) = .stream ∧ nodeBK4 .N4 (cAB .N4 0) = .hashA ∧
    nodeBK4 .N8 (cAB .N8 1) = .hashA ∧ nodeBK4 .N2 (NodeKind.N2.mBase) = .free := by
  decide

/-- (+) Candidate final block `F_{0,2}` of `N4` carries the target of a 2-segment aggregate's last
block (counter `aggB 2`, final). -/
theorem nodeKind4_fin2 : nodeKind4 .N4 (finB .N4 0 + 1) = some (streamTarget (aggB 2) (aggL 2 - 1)) := by
  have hm : (⟨.stream, finB .N4 0 + 1, finB .N4 0 + 1 + 1,
      fun _ => some (streamTarget (aggB (1 + 1)) (aggL (1 + 1) - 1))⟩ : TIv) ∈ nodeLayout4 .N4 := by
    simp only [nodeLayout4, List.mem_append, List.mem_flatMap, List.mem_range]
    exact .inl (.inr ⟨0, by decide, by simp [tailIvs]; decide⟩)
  rw [tgt_of_mem hm (by simp [TIv.mem])]

/-- (−) **Why the candidate blocks**: in `N4`'s main aggregate chain the block where a 2-segment
aggregate ends is not final (its counter is `64 · aggL 2`, not `aggB 2`; R-4-m2). -/
theorem main_not_final2 :
    nodeKind4 .N4 (cLen + aggL 2 - 1) = some (streamTarget (aggB 4) (aggL 2 - 1)) ∧
      ctrAt (aggB 4) (aggL 2 - 1) ≠ aggB 2 := by
  refine ⟨?_, by decide⟩
  have hm := chainIvs_mem .N4 (σ := 1) (by norm_num) ⟨.stream, chBase .N4 1 + 1, chBase .N4 1 + chLen .N4 1,
    fun o => some (streamTarget (chBytes .N4 1) (o + 1))⟩ (by simp [chainIvs])
  rw [tgt_of_mem hm (by decide)]
  congr 2

/-- (−) A block past the node has no interval; the `chain` kind indicates nothing; an
overlapping list fails the tiling check. -/
theorem layout_neg : Sel4 .N2 NodeKind.N2.blocks = false ∧ Ind4 .N8 .chain 0 = false ∧
    contig [⟨.stream, 0, 2, fun _ => none⟩, ⟨.hashA, 1, 3, fun _ => none⟩] 0 3 = false := by
  decide

/-- (+/−) The kind factor: `1` on a `stream` block (`nodeKinds`' index 0), `β^3` on `hashA`; the chain mask links the
aggregate's blocks but not the previous node's last block to the aggregate's first. -/
theorem kf4_chainLk_ctrl (β : F) : kf4 .N4 β 1 = 1 ∧ kf4 .N4 β (cAB .N4 0) = β ^ 3 ∧
    chainLk4 .N4 cLen = true ∧ chainLk4 .N4 (cLen - 1) = false := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · rw [kf4_eq, show nodeBK4 .N4 1 = .stream by decide]; simp [bkIdx4]
  · rw [kf4_eq, show nodeBK4 .N4 (cAB .N4 0) = .hashA by decide]; rfl

end N4c
end FR
