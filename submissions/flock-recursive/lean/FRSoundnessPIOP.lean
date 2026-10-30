-- New for `flock-recursive` (BLUEPRINT A.7, A.10; stage S-G1g).
-- RET-1: position-free declarations moved to `FRSoundnessCoreWeights`.
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessHide
import FRAgg
import FRRingSwitch
import FRBlockKinds
import FRVerifierImplOps
import FRSoundness4TailStep
import FRSoundnessCoreFront
import FRNodeLayout

/-!
# The PIOP truths over the decoded witness (A.10), part 1: `f⁽⁰⁾` in F, `z = unpack f⁽⁰⁾`

* **Part A: the level-0 message in F.** The committed word is F-valued, so each decoded row of a
  close word is `Enc_K` of an F-message (`interp_F_D` on the joint agreement set, which has
  `n₀ − e₀ ≥ k₀` positions). **`fF`** is A.10's `f⁽⁰⁾` in F (`f[e] = fTab … 0 e`, row bits first,
  A.7's element order); **`fTab_F`**: on a close level-0 word, `fTab … 0 = ι ∘ fF`.
* **Part B: the witness bits.** **`zW`**: `z = unpack f⁽⁰⁾` (A.7's pack map: bit `128e + k` of
  `z` is bit `k` of `f[e]`, `FRRingSwitch.unpack`); **`zBlk blk`** is block `blk`'s 2^14
  positions (element `k` of block `blk` is `f[blk·128 + k]`). **`zBlk_bool`**: the bits are
  Boolean by construction (`unpack_boolean`), which is `leaf_sound`'s `hbool`.
* **Part C: the Z truth and B′.** **`truthZ tgt nb`**: every used block satisfies its kind's block
  R1CS with its public target (`HoldsE`, A.10 Z1's identity `(A₀z)(B₀z) = z + E` per block).
  **`leaf_of_truthZ`**: with the chain links (S's truth), `leaf_sound` gives `chainEnd s n = h`.
  **`truthB'`** (A.10 B′, parametric in the cell list while S-E3 changes `pubVals`): `v*` is the
  batched true value with the cells' true values `f[cell_k]`.

* **Part D: the node's per-block targets** (A.6, §4.2–§4.3; S-G1h). **`nodeKind blk`**: the
  public target of node block `blk` (`none` for the `free` blocks `WM`, spares, L, M):
  `streamStart` then `streamTarget streamBytes` per digest chain, `hashA`/`hashB1 tagNode`/`hashB2`
  per slot, and per slot's WOTS run chain `i`'s steps `w43 i s` at offset `3i + s`, the key leaf
  (`hashB1 tagWotsLeaf`, `streamTarget 4265 k`, `streamEnd41`), the path's `hashB1 tagSigNode`,
  `hashB2` pairs. **`truthZN`**: the node's Z truth over `nodeKind`.
* **Part E: the E and Lr truths** (A.10 E1–Eend, Lr1–Lr3; S-G1h). `rowMat sel rows`: a row list's
  `A`/`B`/`C` matrix (`FRVIREval.entriesOf`, as `evalM`/`evalL` read it); **`matVec_rowMat`**: its
  product with `w` is the rows' linear forms; **`sat_rowMat_iff`**: on rows that fit
  (`RowsFit`), the zerocheck tables' R1CS (`FRSpartan.Sat`) is "every row holds". **`truthE`**
  (every compiled M row holds on `f⁽⁰⁾`, `SlotHolds.rows`) and **`truthLr`** (every L row,
  `lRows_sound`), with `truthE_iff`, `truthLr_iff`.
* **Part F: the RS truth** (A.10 RS0/RS1; S-G1h). `rsQ`: the bit planes of `f⁽⁰⁾` (`Q_i(u)` = bit
  `i` of `f[u]`, A.7's pack); **`truthRS0 g s`**: every claim's partials are the true bit-plane
  claims; **`rs1_of_not_truthRS0`**: a wrong slice claim leaves at most `(7 + J′)·|F|^7` of RS1's draws
  undetected (`rs1_joint` with `rsQ_bool`).

* **Part G: the L truth** (A.10 Zend/L1/L2; S-G1h). `zN`: `z` over 14 position and `q` block
  bits (`zN_join`); **`truthLc`**: Zend's `â`, `b̂` are `linAK` of the kinds' block matrices;
  **`trueSum_of_truthLc`**: then `â + α b̂` is L2's true sum (`lin_trueSum_kinds`).

The node's S truth (the link families of §4.2) and the handoffs are not built here (S-G1h
RESULT).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## Part A: the level-0 message in F -/

/-- **A close level-0 word decodes to F-messages** (`interp_F_D`): every decoded row's message is
F-valued. -/
theorem msgOf_F {κ : Kind} {L es : Log} (hfar : ¬ farL κ L es 0) (r x : ℕ) :
    msgOf κ L es 0 r x = algebraMap F K (msgOf κ L es 0 r x).f₀ := by
  by_cases hr : r < (lvl κ 0).rows
  swap
  · simp only [msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ mLog κ 0
  swap
  · simp only [msgOf, hr, hx, dite_true, dite_false]; rfl
  obtain ⟨hek, hN, -, hk, hn⟩ := lv_params κ (i := 0) (by norm_num)
  have hkN : 2 ^ mLog κ 0 ≤ nMax := by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN
  have hnN : 2 ^ (lvl κ 0).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := decodeL_spec hfar
  set rr : Fin (lvl κ 0).rows := ⟨r, hr⟩
  have hv := hV rr
  rw [codeK, hk, ← encCode_D hkN] at hv
  have hA : 2 ^ mLog κ 0 ≤ (jointAgree (wordK κ L es 0) (decodeL κ L es 0)).card := by
    have : lvK κ 0 ≤ 2 ^ (lvl κ 0).logN - lvE κ 0 := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  obtain ⟨c, hc⟩ := interp_F_D hnN hkN hv (fun j => wordOf κ L es 0 rr j) _ hA fun j hj => by
    rw [mem_jointAgree] at hj; rw [← hj rr]; rfl
  have := msgOf_eq (i := 0) (by norm_num) (r := rr) hc.symm ⟨x, hx⟩
  rw [this, algebraMap_f₀]

/-- **`f⁽⁰⁾` is F-valued**: on a close level-0 word, `fTab … 0 = ι ∘ fF`. -/
theorem fTab_F {κ : Kind} {L es : Log} (hfar : ¬ farL κ L es 0) (e : ℕ) :
    fTab κ L es 0 e = algebraMap F K (fF κ L es e) := msgOf_F hfar _ _

/-! ## Part B: the witness bits `z = unpack f⁽⁰⁾` -/

/-- **A.10's `z := unpack f⁽⁰⁾`** (A.7's pack map): bit `b` of `z` is bit `b mod 128` of
`f[b / 128]`. -/
noncomputable def zW (κ : Kind) (L es : Log) (b : ℕ) : F :=
  unpack (fF κ L es (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

/-- Block `blk`'s positions (A.7: block element `k` is `f[blk·128 + k]`, `2^14` bits). -/
noncomputable def zBlk (κ : Kind) (L es : Log) (blk : ℕ) : Block.Pos → F :=
  fun k => zW κ L es (blk * 2 ^ Blake2sCircuit.m + k.val)

/-- Block `blk`'s element `k` is `f[blk·128 + k]`: its bits are positions `128k … 128k + 127`. -/
theorem zBlk_elem (κ : Kind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    zBlk κ L es blk k = unpack (fF κ L es (blk * 128 + k.val / 128))
      ⟨k.val % 128, Nat.mod_lt _ (by norm_num)⟩ := by
  have hm : (2 : ℕ) ^ Blake2sCircuit.m = 128 * 128 := by decide
  have h1 : (blk * (128 * 128) + k.val) / 128 = blk * 128 + k.val / 128 := by omega
  have h2 : (blk * (128 * 128) + k.val) % 128 = k.val % 128 := by omega
  simp only [zBlk, zW, hm, h1, h2]

/-- **The unpacked witness is Boolean** (`leaf_sound`'s `hbool`). -/
theorem zBlk_bool (κ : Kind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    BlockR1CS.IsBool (zBlk κ L es blk k) :=
  unpack_boolean _ _

/-! ## Part C: the Z truth, the leaf, and B′ -/

/-- **The Z truth** (A.10 Z1, per block): each of the `nb` used blocks satisfies its kind's block
R1CS with its public target, `(A₀z)·(B₀z) = z + E` (`HoldsE`). -/
def truthZ (tgt : ℕ → Block.Target) (nb : ℕ) (κ : Kind) (L es : Log) : Prop :=
  ∀ blk < nb, Block.HoldsE (Block.blockR1CS (tgt blk)) (Block.targetVal F (tgt blk))
    (zBlk κ L es blk)

/-- **From the leaf's truths to the leaf's statement**: the Z truth with every block a chain block
and the chain links of the decoded witness give `chainEnd s n = h` (`leaf_sound` over F). -/
theorem leaf_of_truthZ {κ : Kind} {L es : Log} {n : ℕ} (hn : 1 ≤ n) {s h : Digest}
    (hZ : truthZ (fun _ => Chain.chainTarget) n κ L es)
    (hlinks : Leaf.ChainLinks n (zBlk κ L es) s h) : chainEnd s n = h :=
  Leaf.leaf_sound hn (zBlk κ L es) s h (fun i _ k => zBlk_bool κ L es i k) hZ hlinks

/-- **The B′ truth** (A.10 B′; `finB′`'s `v*`, revision 3.12): the batched value is
`v_RS + Σ_k κ′^(k+2)·f[cell_k]` with the true value `vRS` (E4's claim is RS claim 4, inside
`v_RS`) and the cells' true values. Parametric in the cell list: A.7's nine cells are
`Node.pubCells []` once S-E3 drops the padding cells. -/
def truthB' (κ : Kind) (L es : Log) (cells : List ℕ) (κ' vRS vStar : F) : Prop :=
  vStar = vRS + ∑ k ∈ range cells.length, κ' ^ (k + 2) * fF κ L es (cells.getD k 0)

/-- Control (positive): the B′ truth holds at its own batched value. -/
theorem truthB'_self (κ : Kind) (L es : Log) (cells : List ℕ) (κ' vRS : F) :
    truthB' κ L es cells κ' vRS (vRS +
      ∑ k ∈ range cells.length, κ' ^ (k + 2) * fF κ L es (cells.getD k 0)) := rfl

/-- Control (negative): with no cells, a wrong batched value fails the B′ truth. -/
theorem not_truthB'_of_ne (κ : Kind) (L es : Log) {κ' vRS v : F}
    (h : v ≠ vRS) : ¬ truthB' κ L es [] κ' vRS v := by
  simpa [truthB'] using h

/-! ## Part D: the node's per-block targets (A.6) -/

open FR.Kinds FR.Stream in
/-- **The public target of node block `blk`** (A.6, §4.2's consecutive WOTS layout, §4.3's region
table; `none`: the `free` blocks). The digest chains' counters are `streamTarget streamBytes`
(`streamBytes_eq`: `1,481,344`); a WOTS slot's offset `o` is chain `⌊o/3⌋`'s step `o mod 3`
(`o < 399`, `w43_step`), the key leaf (`399 … 465`: 67 blocks of a 4,265-byte stream), then the
16 path steps (`hashB1 tagSigNode`, `hashB2`). -/
def nodeKind (blk : ℕ) : Option Block.Target :=
  if blk < 2 * Layout.chainN then
    if blk % Layout.chainN = 0 then some streamStart.target
    else some (streamTarget 1481344 (blk % Layout.chainN))
  else if blk < Layout.wotsBase then
    let o := (blk - Layout.stmtBase) % 3
    some (if o = 0 then hashA.target else if o = 1 then (hashB1 RecursionFast.tagNode).target
      else hashB2.target)
  else if blk < Layout.wmBase then
    let o := (blk - Layout.wotsBase) % Layout.wotsSlot
    some (if o < 399 then (w43 (o / 3).toUInt8 (o % 3).toUInt8).target
      else if o = 399 then (hashB1 RecursionFast.tagWotsLeaf).target
      else if o < 465 then streamTarget 4265 (o - 399)
      else if o = 465 then streamEnd41.target
      else if (o - 466) % 2 = 0 then (hashB1 RecursionFast.tagSigNode).target else hashB2.target)
  else none

/-- **The node's Z truth** (A.10 Z1 per block): every non-free block satisfies its kind's block
R1CS with its public target (the `free` blocks' rows `z_k² = z_k` hold by `zBlk_bool`). -/
def truthZN (κ : Kind) (L es : Log) : Prop :=
  ∀ blk < Layout.nodeBlocks, ∀ tgt, nodeKind blk = some tgt →
    Block.HoldsE (Block.blockR1CS tgt) (Block.targetVal F tgt) (zBlk κ L es blk)

/-- Control (positive): the kinds at the regions' first blocks, and `free` from `WM` on, as in
`nodeLayout` (`Ind`). -/
theorem nodeKind_controls :
    nodeKind 0 = some Kinds.streamStart.target ∧
    nodeKind Layout.chainN = some Kinds.streamStart.target ∧
    nodeKind Layout.stmtBase = some Kinds.hashA.target ∧
    nodeKind (Layout.stmtBase + 4) = some (Kinds.hashB1 RecursionFast.tagNode).target ∧
    nodeKind (Layout.wotsBase + 5) = some (Kinds.w43 1 2).target ∧
    nodeKind (Layout.wotsBase + Layout.wotsSlot + 465) = some Kinds.streamEnd41.target ∧
    nodeKind Layout.wmBase = none ∧
    Layout.Ind .streamStart 0 = true ∧ Layout.Ind .hashA Layout.stmtBase = true ∧
    Layout.Ind .w43 (Layout.wotsBase + 5) = true ∧
    Layout.Ind .streamEnd41 (Layout.wotsBase + Layout.wotsSlot + 465) = true ∧
    Layout.Ind .free Layout.wmBase = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- Control (negative): a digest chain's inner block is not pinned to `h0` (its `h_in` is the
previous output), unlike its first. -/
theorem nodeKind_inner : nodeKind 1 ≠ some Kinds.streamStart.target := by
  intro h
  have h1 : nodeKind 1 = some (Stream.streamTarget 1481344 1) := rfl
  rw [h1, Option.some.injEq] at h
  have := congrFun h 0
  simp [Stream.streamTarget, Stream.blockTarget, Kinds.Kind.target, Kinds.streamStart] at this

/-! ## Part E: the E and Lr truths (row residuals) -/

section Rows
open Circ Eval

/-- **The E truth** (A.10 E1–Eend; `SlotHolds.rows`): every compiled M row of both slots holds on
`f⁽⁰⁾`. -/
def truthE (fin : Finals) (κ : Kind) (L es : Log) : Prop :=
  ∀ r ∈ Layout.nodeRows fin, r.Holds (fF κ L es)

/-- **The Lr truth** (A.10 Lr1–Lr3, E4; `lRows_sound`): every L row holds on `f⁽⁰⁾`. -/
def truthLr (κ : Kind) (L es : Log) : Prop := ∀ r ∈ Layout.lRows, r.Holds (fF κ L es)

/-- E2's tables are the R1CS of the M rows (`evalM`'s matrices, 21 row and 23 cell variables). -/
theorem truthE_iff (fin : Finals) (hf : RowsFit (Layout.nodeRows fin) 21 23) (κ : Kind)
    (L es : Log) :
    truthE fin κ L es ↔ Sat (rowMat Row.a (Layout.nodeRows fin) 21 23)
      (rowMat Row.b (Layout.nodeRows fin) 21 23) (rowMat Row.c (Layout.nodeRows fin) 21 23)
      (fun y => fF κ L es y) :=
  (sat_rowMat_iff _ hf _).symm

/-- L's rows fit `2^15` rows and `2^23` cells. -/
theorem lRows_fit : RowsFit Layout.lRows 15 23 := by
  refine ⟨by rw [Layout.lRows_length]; norm_num, fun r hr t ht => ?_⟩
  simp only [Layout.lRows, List.mem_map, List.mem_flatMap, List.mem_range, Layout.lBitCells]
    at hr
  obtain ⟨b, ⟨σ, hσ, j, hj, rfl⟩, rfl⟩ := hr
  simp only [Lin.cell, Lin.sub, Lin.smul, List.append_nil, List.mem_append, List.mem_cons,
    List.map_cons, List.map_nil, List.not_mem_nil, or_false] at ht
  simp only [Layout.lBase, Layout.oneCell, Layout.mBase] at ht ⊢
  rcases ht with ((rfl | rfl) | rfl | rfl) | (rfl | rfl) <;> simp <;> omega

/-- Lr2's tables are the R1CS of L's rows (`evalL`'s matrices, 15 row and 23 cell variables). -/
theorem truthLr_iff (κ : Kind) (L es : Log) :
    truthLr κ L es ↔ Sat (rowMat Row.a Layout.lRows 15 23) (rowMat Row.b Layout.lRows 15 23)
      (rowMat Row.c Layout.lRows 15 23) (fun y => fF κ L es y) :=
  (sat_rowMat_iff _ lRows_fit _).symm

/-- Control (negative): a row `1 · 1 = 0` makes the R1CS fail. -/
theorem not_sat_one_row (w : Asg) (hw : w 0 = 1) :
    ¬ Sat (rowMat Row.a [⟨Lin.cell 0, Lin.cell 0, []⟩] 0 1)
      (rowMat Row.b [⟨Lin.cell 0, Lin.cell 0, []⟩] 0 1)
      (rowMat Row.c [⟨Lin.cell 0, Lin.cell 0, []⟩] 0 1) (fun y => w y) := by
  rw [sat_rowMat_iff _ ⟨by simp, by simp [Lin.cell]⟩]
  intro h
  have := h _ List.mem_cons_self
  simp [Row.Holds, hw] at this

/-- Control (positive): the empty row list is satisfied by every assignment. -/
theorem sat_nil (a b : ℕ) (w : Asg) :
    Sat (rowMat Row.a [] a b) (rowMat Row.b [] a b) (rowMat Row.c [] a b) (fun y => w y) :=
  (sat_rowMat_iff [] ⟨by simp, by simp⟩ w).mpr (by simp)

end Rows

/-! ## Part F: the RS truth -/

/-- **The bit planes of `f⁽⁰⁾`** over `2^ℓ` elements (A.7's pack: `Q_i(u)` is bit `i` of `f[u]`,
i.e. `z[128u + i]`). -/
noncomputable def rsQ (κ : Kind) (L es : Log) (ℓ : ℕ) : Fin 128 → Fin (2 ^ ℓ) → F :=
  fun i u => unpack (fF κ L es u) i

theorem rsQ_bool (κ : Kind) (L es : Log) (ℓ : ℕ) (i : Fin 128) (u : Fin (2 ^ ℓ)) :
    rsQ κ L es ℓ i u = 0 ∨ rsQ κ L es ℓ i u = 1 := unpack_boolean _ _

theorem rsQ_eq_zW (κ : Kind) (L es : Log) (ℓ : ℕ) (i : Fin 128) (u : Fin (2 ^ ℓ)) :
    rsQ κ L es ℓ i u = zW κ L es (128 * u.val + i.val) := by
  have h1 : (128 * u.val + i.val) / 128 = u.val := by omega
  have h2 : (128 * u.val + i.val) % 128 = i.val := by omega
  simp only [rsQ, zW, h1, h2]

/-- **The RS0 truth** (A.10 RS0): every claim's 128 partials `s j` are the true bit-plane claims
`Σ_u g_j(u)·Q_i(u)` with the claims' weights `g_j` (`eq` at the Z, Lc, Sh, Lr points). -/
def truthRS0 {J ℓ : ℕ} (κ : Kind) (L es : Log) (g : Fin J → Fin (2 ^ ℓ) → F)
    (s : Fin J → Fin 128 → F) : Prop :=
  ∀ j i, s j i = ∑ u, g j u * algebraMap F F (rsQ κ L es ℓ i u)

open Classical in
/-- **RS1's count from a false RS0 truth** (A.10 RS1, `rs1_joint`): if some slice claim is wrong, at
most `(7 + J′)·|F|^7` of the `|F|^8` draws `(r″, κ)` make the batched switched claim equal its
true value. -/
theorem rs1_of_not_truthRS0 {J' ℓ : ℕ} {κ : Kind} {L es : Log} {g : Fin (J' + 1) → Fin (2 ^ ℓ) → F}
    {s : Fin (J' + 1) → Fin 128 → F} (h : ¬ truthRS0 κ L es g s) :
    (univ.filter fun p : (Fin 7 → F) × F =>
      ∑ j, p.2 ^ j.val * rsT s p.1 j = ∑ j, p.2 ^ j.val * rsTruth (rsQ κ L es ℓ) g p.1 j).card ≤
      (7 + J') * Fintype.card F ^ 7 := by
  refine rs1_joint _ (rsQ_bool κ L es ℓ) g s ?_
  unfold truthRS0 at h
  push Not at h
  obtain ⟨j, i, hji⟩ := h
  exact ⟨j, fun hz => hji (sub_eq_zero.mp (congrFun hz i))⟩

/-- Control (positive): the true partials satisfy the RS0 truth. -/
theorem truthRS0_true {J ℓ : ℕ} (κ : Kind) (L es : Log) (g : Fin J → Fin (2 ^ ℓ) → F) :
    truthRS0 κ L es g fun j i => ∑ u, g j u * algebraMap F F (rsQ κ L es ℓ i u) :=
  fun _ _ => rfl

/-! ## Part G: the L truth (the lincheck on the kinds' folded columns) -/

/-- The witness bits as a table over `14` position bits (low) and `q` block bits (high): position
`k` of block `t` is `z[2^14·t + k]` (`join`, A.7). -/
noncomputable def zN (κ : Kind) (L es : Log) (q : ℕ) : Fin (2 ^ (14 + q)) → F :=
  fun b => zW κ L es b

theorem zN_join (κ : Kind) (L es : Log) {q : ℕ} (k : Fin (2 ^ 14)) (t : Fin (2 ^ q)) :
    zN κ L es q (join k t) = zBlk κ L es t k := by
  simp only [zN, zBlk, join, Blake2sCircuit.m]
  congr 1; ring

/-- **The L truth** (A.10 Zend → L1/L2, `lin_trueSum_kinds`): Zend's absorbed `â`, `b̂` are the
kinds' block matrices applied to `z` at the lincheck's row weights `rw` and block point `rb`
(`linAK`, `A = Σ_κ Ind_κ ⊗ A₀^κ`). -/
def truthLc {K q : ℕ} (Ak Bk : Fin (K + 1) → Fin (2 ^ 14) → Fin (2 ^ 14) → F)
    (Ind : Fin (K + 1) → Fin (2 ^ q) → F) (rw : Fin (2 ^ 14) → F) (rb : Fin q → F) (κ : Kind)
    (L es : Log) (va vb : F) : Prop :=
  va = linAK Ak Ind rw rb (zN κ L es q) ∧ vb = linAK Bk Ind rw rb (zN κ L es q)

/-- **L2's initial claim from the L truth**: then `â + α b̂` is the true sum of L2's kind tables
(`lin_trueSum_kinds`), so a false L2 claim is a false `â` or `b̂` (L1's `Wrong`). -/
theorem trueSum_of_truthLc {K q : ℕ} {Ak Bk : Fin (K + 1) → Fin (2 ^ 14) → Fin (2 ^ 14) → F}
    {Ind : Fin (K + 1) → Fin (2 ^ q) → F} {rw : Fin (2 ^ 14) → F} {rb : Fin q → F} {κ : Kind}
    {L es : Log} {va vb : F} (h : truthLc Ak Bk Ind rw rb κ L es va vb) (α : F) :
    trueSum (kindExpr K) (kindTables (fun k => linM (Ak k) (Bk k) rw α)
      (zfoldK Ind rb (zN κ L es q))) 14 = va + α * vb := by
  rw [lin_trueSum_kinds, h.1, h.2]

/-- Control (negative): a wrong `â` fails the L truth. -/
theorem not_truthLc_of_ne {K q : ℕ} {Ak Bk : Fin (K + 1) → Fin (2 ^ 14) → Fin (2 ^ 14) → F}
    {Ind : Fin (K + 1) → Fin (2 ^ q) → F} {rw : Fin (2 ^ 14) → F} {rb : Fin q → F} {κ : Kind}
    {L es : Log} {va vb : F} (h : va ≠ linAK Ak Ind rw rb (zN κ L es q)) :
    ¬ truthLc Ak Bk Ind rw rb κ L es va vb := fun h' => h h'.1

end FR.Snd
