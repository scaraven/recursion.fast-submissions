-- New for `flock-recursive` (BLUEPRINT A.6, A.8 `targetS`/`maskRows`, A.10 Z1; stage S-G8).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreFront`.
import FRSoundnessFrBind
import FRSoundnessCoreFront

/-!
# The kinds' matrices `zlmFR`: Z's statement is the per-block R1CS

* **`zlmFR`**: the `ZLM` of A.6. Kind `j` is `blockKinds[j]`; its matrices are the circuit's rows
  where the kind pins nothing (`isZeroRow`, the mask `maskRows` applies), the identity for `free`;
  a node's indicators are `nodeLayout`'s `Ind` (the verifier's `kindInd`), a leaf's are `chain`
  everywhere; the target bits are `nodeE` (a node, `targetSNodeS`'s) and `chainE` (a leaf).
* **`kindPins`**: each target `nodeKind` assigns pins exactly its class's `zeroRows`
  (`nodeBK`); `chainTarget` pins `chain`'s.
* **`zHolds_iff_truthZN`** (a node) and **`zHolds_iff_truthZ`** (a leaf: every block a `chain`
  block): `ZHolds zlmFR` is the per-block statement.
* **`peL_node`**, **`peL_leaf`**: Z2's `P^e` is the verifier's `targetS` (`specC`) at Z1's
  register point.
* **`ind_iff`**: `nodeLayout`'s `Ind` (the verifier's kind intervals) is `nodeBK`'s class.
* The leaf's Lc claim: **`trueL_one`** (every kind: RS claim 2's true value is `ẑ(r_k, r_blk)`
  weighted by the kind factor `kfT`, revision 3.16),
  **`zfL_leaf`**, **`pendLc_pendBad`** (L3β's pending doom is RS0's `PendBad` at claim 2), and
  **`rejLc2_ok`** (`finLc` (ii)'s failure on a leaf is a `RejOK`). The node's L3/L3β wait for
  revision 3.16 (INT-5).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset FR.Impl ProductCircuit

set_option linter.constructorNameAsVariable false

/-! ## The pins of the targets -/

section Pins

end Pins

/-! ## `nodeLayout`'s indicators are `nodeBK`'s classes -/

section Layout
open Layout

theorem chained_head_lt : ∀ {a : Iv} {l : List Iv}, chained (a :: l) = true → a.lo < a.hi
  | _, [], h => by simpa [chained] using h
  | _, _ :: _, h => by simp only [chained, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem chained_tail : ∀ {a : Iv} {l : List Iv}, chained (a :: l) = true → chained l = true
  | _, [], _ => rfl
  | _, _ :: _, h => by simp only [chained, Bool.and_eq_true] at h; exact h.2

theorem chained_hi_le : ∀ {a : Iv} {l : List Iv}, chained (a :: l) = true → ∀ iv ∈ l, a.hi ≤ iv.lo
  | _, [], _ => by simp
  | a, b :: t, h => by
    have hb := chained_tail h
    have h1 : a.hi ≤ b.lo := by
      simp only [chained, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
    intro iv hiv
    rcases List.mem_cons.mp hiv with rfl | hiv
    · exact h1
    · have := chained_hi_le hb iv hiv
      have := chained_head_lt hb
      omega

theorem chained_unique : ∀ {l : List Iv}, chained l = true → ∀ {iv₁ iv₂ : Iv} {x : ℕ},
    iv₁ ∈ l → iv₂ ∈ l → iv₁.lo ≤ x → x < iv₁.hi → iv₂.lo ≤ x → x < iv₂.hi → iv₁ = iv₂
  | [], _, _, _, _, h, _, _, _, _, _ => by simp at h
  | a :: l, h, iv₁, iv₂, x, h1, h2, a1, b1, a2, b2 => by
    have hl := chained_hi_le h
    rcases List.mem_cons.mp h1 with e1 | m1 <;> rcases List.mem_cons.mp h2 with e2 | m2
    · rw [e1, e2]
    · subst e1; have := hl _ m2; omega
    · subst e2; have := hl _ m1; omega
    · exact chained_unique (chained_tail h) m1 m2 a1 b1 a2 b2

/-- **`nodeLayout`'s `Ind` is `nodeBK`'s class** on every block of the node (`ind_nodeBK`, and
the intervals do not overlap: `nodeLayout_chained`). -/
theorem ind_iff {blk : ℕ} (h : blk < nodeBlocks) (b : BlockKind) : Ind b blk = true ↔ b = nodeBK blk := by
  refine ⟨fun hb => ?_, fun hb => hb ▸ ind_nodeBK h⟩
  have h2 := ind_nodeBK h
  simp only [Ind, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb h2
  obtain ⟨iv₁, m₁, ⟨⟨k₁, l₁⟩, u₁⟩⟩ := hb
  obtain ⟨iv₂, m₂, ⟨⟨k₂, l₂⟩, u₂⟩⟩ := h2
  rw [← k₁, ← k₂, chained_unique nodeLayout_chained m₁ m₂ l₁ u₁ l₂ u₂]

end Layout

/-! ## The matrices -/

theorem zlmFR_bits : zlmFR.Bits := by
  refine ⟨kMat_bit _, kMat_bit _, fun κ j t => ?_, fun κ t p => ?_⟩
  · simp only [zlmFR]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl
  · simp only [zlmFR, NodeT.nodeE, NodeT.tgtE, NodeT.bF, chainE]
    split_ifs <;> (try split) <;> (try split_ifs) <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem nodeBK_ne_chain (t : ℕ) : nodeBK t ≠ .chain := by
  unfold nodeBK Layout.wotsKindAt; split_ifs <;> simp

theorem zlmFR_indKinds : zlmFR.IndKinds := fun κ t => by
  refine ⟨fun hn => ?_, fun hn j hj => ?_⟩
  · have : bkOf 0 ≠ nodeBK t := fun h => nodeBK_ne_chain t (h ▸ rfl)
    simp [zlmFR, hn, this]
  · simp [zlmFR, hn, Fin.val_ne_iff.mpr hj, hj]

/-! ## Z's statement block by block -/

/-- **`ZHolds` block by block**: on each of the `2^(m−14)` blocks, at each position, the kinds'
rows `(A z)(B z) = z + E`. -/
theorem zHolds_iff_blocks (M : ZLM) (L es : Log) : ZHolds M L es ↔
    ∀ t < 2 ^ qL (kindOf es), ∀ p : Fin (2 ^ 14),
      mvZ M M.Ak (kindOf es) L es t p * mvZ M M.Bk (kindOf es) L es t p =
        zBk (kindOf es) L es t p + M.Et (kindOf es) t p := by
  have hℓ := mm6_q (kindOf es)
  simp only [ZHolds, BHolds]
  constructor
  · intro h t ht p
    have hp := p.isLt
    have hu : p.val / 64 + 256 * t < 2 ^ mm 6 (kindOf es) := by
      rw [hℓ, pow_add]; norm_num at hp ⊢; omega
    have := h ⟨p.val % 64, Nat.mod_lt _ (by norm_num)⟩ ⟨_, hu⟩
    have h1 : (p.val / 64 + 256 * t) / 256 = t := by omega
    have h2 : pAt ⟨p.val % 64, Nat.mod_lt _ (by norm_num)⟩ (p.val / 64 + 256 * t) = p := by
      ext; simp only [pAt]; norm_num at hp; omega
    simpa only [aZ, bZ, zZ, eZ, h1, h2] using this
  · intro h σ u
    have h8 : 2 ^ mm 6 (kindOf es) = 256 * 2 ^ qL (kindOf es) := by rw [hℓ, pow_add]; norm_num
    have hu : u.val / 256 < 2 ^ qL (kindOf es) := by
      have := lt_of_lt_of_eq u.isLt h8; omega
    exact h _ hu (pAt σ u.val)

/-- The kind index of block `t` of a `κ` proof under `zlmFR`. -/
def jOf (κ : Kind) (t : ℕ) : Fin 9 := if κ.isNode then bkIdx (nodeBK t) else 0

theorem ind_jOf (κ : Kind) (t : ℕ) (j : Fin 9) : zlmFR.Ind κ j t = if j = jOf κ t then 1 else 0 := by
  by_cases hn : κ.isNode = true
  · have hJ : jOf κ t = bkIdx (nodeBK t) := by simp [jOf, hn]
    rw [hJ]; simp only [zlmFR]; rw [if_pos hn]
    by_cases hj : j = bkIdx (nodeBK t)
    · rw [if_pos ((bkOf_eq_iff _ _).mpr hj), if_pos hj]
    · rw [if_neg (mt (bkOf_eq_iff _ _).mp hj), if_neg hj]
  · have hJ : jOf κ t = 0 := by simp [jOf, hn]
    rw [hJ]; simp only [zlmFR]; rw [if_neg hn]
    exact if_congr Fin.val_eq_zero_iff rfl rfl

theorem mvZ_jOf (C : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F) (κ : Kind) (L es : Log) (t : ℕ)
    (p : Fin (2 ^ 14)) : mvZ zlmFR C κ L es t p = ∑ k, C (jOf κ t) p k * zBk κ L es t k := by
  unfold mvZ
  rw [sum_eq_single (jOf κ t) (fun j _ hj => by rw [ind_jOf, if_neg hj, zero_mul])
    (fun h => absurd (mem_univ _) h), ind_jOf, if_pos rfl, one_mul]

theorem zBk_eq_zBlk (κ : Kind) (L es : Log) (t : ℕ) (k : Fin (2 ^ 14)) :
    zBk κ L es t k = zBlk κ L es t k := by
  simp only [zBk, zBlk, mul_comm]

theorem nodeTgt_eq (blk : ℕ) : NodeT.nodeTgt blk = nodeKind blk := rfl

/-- **Each target `nodeKind` assigns pins exactly its class's rows** (`nodeBK`, A.6's `zeroRows`). -/
theorem nodeKind_pins {blk : ℕ} {tgt : Block.Target} (h : nodeKind blk = some tgt) (p : Block.Pos) :
    (tgt p).isNone = !isZeroRow (nodeBK blk) p.val := by
  unfold nodeKind at h
  unfold nodeBK Layout.wotsKindAt
  dsimp only at h
  split_ifs at h ⊢ <;> cases h <;>
    first
    | with_reducible exact pins_streamStart p | with_reducible exact pins_stream _ _ p
    | with_reducible exact pins_hashA p | with_reducible exact pins_hashB1 _ p
    | with_reducible exact pins_hashB2 p | with_reducible exact pins_w43 _ _ p
    | with_reducible exact pins_streamEnd41 p

/-- **A node's Z statement is `truthZN`** (the free blocks' rows `z² = z` hold on bits). -/
theorem zHolds_iff_truthZN {L es : Log} (hn : kindOf es = .N30) :
    ZHolds zlmFR L es ↔ truthZN (kindOf es) L es := by
  rw [zHolds_iff_blocks]
  generalize kindOf es = κ at hn ⊢
  subst hn
  have hq : 2 ^ qL Kind.N30 = Layout.nodeBlocks := rfl
  simp only [mvZ_jOf, jOf, Kind.isNode, if_true, hq]
  have hE : ∀ t (p : Fin (2 ^ 14)), zlmFR.Et .N30 t p = NodeT.nodeE t p.val := fun _ _ => rfl
  have hz : ∀ t, zBk .N30 L es t = zBlk .N30 L es t := fun t => funext (zBk_eq_zBlk _ _ _ t)
  constructor
  · intro h blk hblk tgt ht k
    have hb : nodeBK blk ≠ .free := fun e => by
      rw [nodeBK_eq_free_iff, ← nodeKind_eq_none_iff, ht] at e; cases e
    have := h blk hblk k
    rw [show zlmFR.Ak = kMat Block.circuitR1CS.A from rfl, show zlmFR.Bk = kMat Block.circuitR1CS.B from rfl,
      kMat_mulVec _ hb (nodeKind_pins ht), kMat_mulVec _ hb (nodeKind_pins ht)] at this
    simp only [hE, NodeT.nodeE, nodeTgt_eq, ht, tgtE_eq, hz] at this
    exact this
  · intro h t ht p
    rw [show zlmFR.Ak = kMat Block.circuitR1CS.A from rfl, show zlmFR.Bk = kMat Block.circuitR1CS.B from rfl,
      hE, NodeT.nodeE, nodeTgt_eq]
    rcases hk : nodeKind t with _ | tgt
    · have hb : nodeBK t = .free := (nodeBK_eq_free_iff t).mpr ((nodeKind_eq_none_iff t).mp hk)
      rw [hb, kMat_free, kMat_free]
      exact bit_sq (zBk_bit _ _ _ _ _)
    · have hb : nodeBK t ≠ .free := fun e => by
        rw [nodeBK_eq_free_iff, ← nodeKind_eq_none_iff, hk] at e; cases e
      rw [kMat_mulVec _ hb (nodeKind_pins hk), kMat_mulVec _ hb (nodeKind_pins hk)]
      simp only [tgtE_eq, hz]
      exact h t ht tgt hk p

/-- **A leaf's Z statement is `truthZ` with every block a `chain` block** (`leaf_of_truthZ`'s
hypothesis, over the `2^(m−14)` blocks). -/
theorem zHolds_iff_truthZ {L es : Log} (hn : (kindOf es).isNode = false) :
    ZHolds zlmFR L es ↔ truthZ (fun _ => Chain.chainTarget) (2 ^ qL (kindOf es)) (kindOf es) L es := by
  rw [zHolds_iff_blocks]
  generalize kindOf es = κ at hn ⊢
  have hj : ∀ t, jOf κ t = bkIdx .chain := fun t => by simp [jOf, hn]; rfl
  have hE : ∀ t (p : Fin (2 ^ 14)), zlmFR.Et κ t p = chainE p.val := fun _ _ => by simp [zlmFR, hn]
  have hz : ∀ t, zBk κ L es t = zBlk κ L es t := fun t => funext (zBk_eq_zBlk _ _ _ t)
  have hb : BlockKind.chain ≠ .free := by decide
  simp only [mvZ_jOf, hj, hE]
  rw [show zlmFR.Ak = kMat Block.circuitR1CS.A from rfl, show zlmFR.Bk = kMat Block.circuitR1CS.B from rfl]
  simp only [kMat_mulVec _ hb pins_chain, chainE_eq, hz, zBk_eq_zBlk]
  rfl

/-! ## Z2's `P^e` is the verifier's `targetS` -/

/-- `P^e` as a range sum. -/
theorem peL_range (M : ZLM) (es : Log) (σ : Fin 64) : peL M es σ =
    ∑ u ∈ range (2 ^ mm 6 (kindOf es)), eqAtR (ptOf (mm 6 (kindOf es)) (zrL es)) u *
      M.Et (kindOf es) (u / 256) (pAt σ u) := by
  unfold peL eZ
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf (mm 6 (kindOf es)) (zrL es)) u *
    M.Et (kindOf es) (u / 256) (pAt σ u))]
  exact sum_congr rfl fun u _ => by rw [eq_cube_eqAtR]

theorem zrL_getD (es : Log) (l : ℕ) (hl : l < (kindOf es).m - 6) :
    (zrL es).getD l 0 = if h : l < 7 then pinnedRho ⟨l, h⟩ else coordAt es 2 (l - 7) := by
  have hm := kind_m (kindOf es)
  unfold zrL
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
      List.getElem?_ofFn, dif_pos h, Option.getD_some]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_map, List.getElem?_range (show l - 7 < (kindOf es).m - 13 by omega),
      Option.map_some, Option.getD_some]

/-- **Z1's register point** against the log: the verifier's `targetS` operand `r` (Z1's
`m − 13` coordinates) gives the first 24 coordinates of `zrL` (`zLo`, `rbOf`). -/
theorem zrL_append {es : Log} {r : Array F} (hr : ∀ l < 17, r.getD l 0 = coordAt es 2 l)
    (h24 : 24 ≤ (kindOf es).m - 6) :
    ptOf 24 (zrL es) = Fin.append (zLo r) (NodeT.rbOf r) := by
  funext l
  refine Fin.addCases (m := 8) (n := 16) (fun i => ?_) (fun i => ?_) l
  · rw [Fin.append_left]
    simp only [ptOf, Fin.coe_castAdd, zrL_getD es i.val (by omega), zLo]
    split_ifs with h
    · rfl
    · rw [hr 0 (by norm_num)]; congr 1; omega
  · rw [Fin.append_right]
    simp only [ptOf, Fin.coe_natAdd, zrL_getD es (8 + i.val) (by omega), NodeT.rbOf]
    rw [dif_neg (by omega), hr (1 + i.val) (by omega)]; congr 1; omega

theorem m24 (κ : Kind) : 24 ≤ κ.m - 6 := by cases κ <;> decide

/-- **A node's `P^e` is `targetSNodeS`** at Z1's register point. -/
theorem peL_node {es : Log} (hn : kindOf es = .N30) {r : Array F}
    (hr : ∀ l < 17, r.getD l 0 = coordAt es 2 l) :
    NodeT.targetSNodeS r = Array.ofFn (peL zlmFR es) := by
  have h24 : mm 6 (kindOf es) = 24 := by rw [hn]; rfl
  have hpt := zrL_append hr (m24 _)
  unfold NodeT.targetSNodeS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [targetS_range _ _ σ (fun u => NodeT.nodeE (u / 256) (σ + 64 * (u % 256))) fun _ => rfl,
    peL_range, ← hpt]
  simp only [zlmFR, hn, Kind.isNode, if_true, pAt]
  rw [h24]
  rfl

/-- **A leaf's `P^e` is `targetSLeafS 16`** at Z1's register point: the target does not depend
on the block, so an `L32` leaf's two further block coordinates sum out. -/
theorem peL_leaf {es : Log} (hn : (kindOf es).isNode = false) {r : Array F}
    (hr : ∀ l < 17, r.getD l 0 = coordAt es 2 l) :
    targetSLeafS 16 r = Array.ofFn (peL zlmFR es) := by
  have hpt := zrL_append hr (m24 _)
  have hpt' : (Fin.append (zLo r) fun l : Fin 16 => r.getD (1 + l) 0) = ptOf 24 (zrL es) :=
    hpt.symm
  unfold targetSLeafS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [targetS_range _ _ σ (fun u => chainE (σ + 64 * (u % 256))) fun _ => rfl, peL_range, hpt']
  simp only [zlmFR, hn, Bool.false_eq_true, if_false, pAt]
  generalize kindOf es = κ at hn ⊢
  cases κ
  · -- `L32`: sum out the two high block coordinates
    have e : ∀ q y, (y + 2 ^ 24 * q) % 256 = y % 256 := fun q y => by
      rw [show 2 ^ 24 * q = 256 * (2 ^ 16 * q) by ring, Nat.add_mul_mod_self_left]
    conv_rhs => rw [show mm 6 Kind.L32 = 24 + 2 from rfl, sum_eqAtR_split 24 2]
    simp only [e]
    rw [sum_comm]
    refine sum_congr (by norm_num) fun y _ => ?_
    set Q := ptOf 2 ((zrL es).drop 24)
    rw [show (∑ q ∈ range (2 ^ 2), eqAtR (ptOf 24 (zrL es)) y * eqAtR Q q *
        chainE (σ + 64 * (y % 256))) = (eqAtR (ptOf 24 (zrL es)) y * chainE (σ + 64 * (y % 256))) *
        ∑ q ∈ range (2 ^ 2), eqAtR Q q by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring, sum_eqAtR_one, mul_one]
  · rfl
  · simp [Kind.isNode] at hn

/-! ## The leaf's Lc claim as RS0's `PendBad` -/

theorem ptOf_rkL (es : Log) : ptOf 14 (xLL es ++ lcPtL (kindOf es).m es) = ptOf 14 (rkL es) := by
  funext l
  fin_cases l <;> simp [ptOf, xLL, lcPtL, rkL, rchs, List.getD_eq_getElem?_getD,
    List.getElem?_append_left, List.getElem?_append_right]

theorem ptOf_rbLc (es : Log) :
    ptOf (qL (kindOf es)) ((xLL es ++ lcPtL (kindOf es).m es).drop 14) = rbLc es := by
  have hm := kind_m (kindOf es)
  have hd : (xLL es ++ lcPtL (kindOf es).m es).drop 14 =
      (List.range ((kindOf es).m - 14)).map (fun l => rch 15 es (8 + l)) := by
    rw [lcPtL, ← List.append_assoc, List.drop_left' (by simp [xLL])]
  funext l
  have hl := l.isLt
  rw [hd]
  simp only [rbLc, ptOf, rZ, rchs, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show l.val < (kindOf es).m - 14 by unfold qL at hl; omega),
    List.getElem?_range (show 8 + l.val < mm 6 (kindOf es) by unfold mm qL at *; omega),
    Option.map_some, Option.getD_some]

/-- **RS claim 2's true value is the kind-weighted `ẑ(r_k, r_blk)`** at L2's challenges and Z3's
block point (every kind; the weight `kfT` is a node's kind factor `B_β(t)`, a leaf's `1`). -/
theorem trueL_one (L es : Log) : trueL (kindOf es) L es 1 =
    ∑ t ∈ range (2 ^ qL (kindOf es)), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * kfT (kindOf es) es t *
        zW (kindOf es) L es (j + 2 ^ 14 * t) := by
  rw [← ptOf_rkL, ← ptOf_rbLc]
  generalize kindOf es = κ
  have hm := kind_m κ
  have hP0 : nrP 0 κ = qL κ + 7 := by rw [nrP_zero, qL]; omega
  set xL := xLL es
  set lP := lcPtL κ.m es
  have hxL : xL.length = 7 := by simp [xL, xLL]
  have hlP : lP.length = qL κ + 7 := by simp [lP, lcPtL, qL]; omega
  have hcw : ∀ i : Fin 128, cwL κ es (1 : Fin 4) i = eqAtR (ptOf 7 xL) i := by
    intro i
    show (eqTab xL.toArray).getD i 0 = _
    rw [eqTab_getD _ (by simp [hxL]), List.size_toArray, hxL, eqBits, bitSel,
      eqAtR, ← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun l _ => ?_
    simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hg : ∀ u : Fin (2 ^ nrP 0 κ), gL κ es 1 u =
      eqAtR (ptOf (nrP 0 κ) lP) u * kfT κ es (u.val / 2 ^ 7) := by
    intro u
    have hl : (rsPtsL κ es).getD 1 [] = lP := by cases κ <;> rfl
    have h1 : (1 : ℕ) < (rsPtsL κ es).length := by rw [rsPtsL_length]; split_ifs <;> norm_num
    have h1' : ((1 : Fin 4) : ℕ) = 1 := rfl
    rw [gL, h1', if_pos h1, if_pos rfl, hl, eqPts_eq _ _ (hlP.trans hP0.symm) (by simp [bitsL, hlP, hP0]),
      hlP, ← hP0, ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ nrP 0 κ)), algebraMap F F (rsQ κ L es (nrP 0 κ) i u) =
      zW κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [rsQ, zW, Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  set g : ℕ → F := fun b => kfT κ es (b / 2 ^ 14) * zW κ L es b with hgdef
  have step1 : trueL κ L es 1 = ∑ u ∈ range (2 ^ (qL κ + 7)), ∑ i ∈ range (2 ^ 7),
      eqAtR (ptOf 7 xL) i * eqAtR (ptOf (qL κ + 7) lP) u * g (i + 2 ^ 7 * u) := by
    unfold trueL
    simp only [hcw, hg, hq, mul_sum]
    rw [sum_comm, hP0, Finset.sum_range]
    refine sum_congr rfl fun y _ => ?_
    rw [Finset.sum_range]
    refine sum_congr rfl fun x _ => ?_
    have hx := x.isLt
    simp only [hgdef]
    rw [show (x.val + 2 ^ 7 * y.val) / 2 ^ 14 = y.val / 2 ^ 7 by omega]
    ring
  have hP7 : ptOf 7 (xL ++ lP) = ptOf 7 xL := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < xL.length by rw [hxL]; exact l.isLt)]
  have hPd : (xL ++ lP).drop 7 = lP := by rw [List.drop_left' hxL]
  have hR : ∀ P : List F, (∑ t ∈ range (2 ^ qL κ), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 P) j * eqAtR (ptOf (qL κ) (P.drop 14)) t * kfT κ es t *
        zW κ L es (j + 2 ^ 14 * t)) = ∑ t ∈ range (2 ^ qL κ), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 P) j * eqAtR (ptOf (qL κ) (P.drop 14)) t * g (j + 2 ^ 14 * t) := fun P =>
    sum_congr rfl fun t _ => sum_congr rfl fun j hj => by
      rw [mem_range] at hj
      simp only [hgdef]
      rw [show (j + 2 ^ 14 * t) / 2 ^ 14 = t by omega]
      ring
  rw [step1, hR, ← sum_eqAtR_split 14 (qL κ) g, show 14 + qL κ = 7 + (qL κ + 7) by omega,
    sum_eqAtR_split, hP7, hPd]

/-- On a leaf, `z̄_chain(r_k)` is RS claim 2's true value (every block a `chain` block). -/
theorem zfL_leaf {L es : Log} (hn : (kindOf es).isNode = false) :
    zfL zlmFR L es 0 = trueL (kindOf es) L es 1 := by
  rw [trueL_one]
  simp only [kfT, hn, Bool.false_eq_true, if_false, mul_one]
  unfold zfL zfoldK mle IndF
  have hI : ∀ t, zlmFR.Ind (kindOf es) 0 t = 1 := fun t => by simp [zlmFR, hn]
  simp only [hI, mul_one, eq_cube_eqAtR, zN, join, mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ j ∈ range (2 ^ 14), eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t * zW (kindOf es) L es (j + 2 ^ 14 * t)), sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t.val * zW (kindOf es) L es (j + 2 ^ 14 * t.val))]
  exact sum_congr rfl fun j _ => by rw [add_comm (2 ^ 14 * t.val)]; ring

/-- **The leaf's pending Lc claim is RS0's `PendBad` at claim 2** (`v_β`). -/
theorem pendLc_pendBad {oZ oSh : Kind → Log → F → Prop} {L es : Log} (h : PendLc zlmFR L es) :
    PendBad (okRS oZ oSh) L es := by
  obtain ⟨-, hn, hne⟩ := h
  refine ⟨1, by rw [rsPtsL_length]; split_ifs <;> norm_num, fun ho => hne ?_⟩
  have ho' : trueL (kindOf es) L es 1 = vBetaL es := ho
  have ht : ∑ i : Fin 8, fAt es 98 0 ^ i.val * tL zlmFR L es i = zfL zlmFR L es 0 := by
    rw [Fin.sum_univ_succ]
    simp [tL]
  rw [ht, zfL_leaf hn, ho']

/-! ## `RejLc2` is a `RejOK` -/

/-- **`finLc` (ii)'s failure (a leaf) is a `RejOK`** (from L3's absorb at 97 on; it reads L2's
rounds, Zend's message, `α` and L3's message, all before 98). -/
theorem rejLc2_ok (M : ZLM) (hp : fsItems[97]? ≠ some .squeeze) : RejOK (RejLc2 M) := by
  have h := rejOK_at (p := 97) (P := fun L es => (kindOf es).isNode = false ∧
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 ≠
        ∑ j, vM (kindOf es) es j * mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es)))
    (fun L es L' es' _ _ hS => by
      obtain ⟨hk, hl, hr, ha, -, -⟩ := lin_agree (hS.1.mono (by norm_num))
      have hc := clR2_same (b := 69) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
        (c0 := fun _ es => c0L es) (L := L) (L' := L') (c0L_agree (hS.1.mono (by norm_num)))
        (l := 14) (hS.1.mono (by norm_num))
      have hv : vM (kindOf es) es = vM (kindOf es') es' := by
        funext j; simp only [vM, vL, msgAt_congr hS.1 (show 97 < 98 by norm_num), hk]
      have hrk : rkL es = rkL es' := by
        unfold rkL rchs; exact List.map_congr_left fun j hj => by
          simp only [List.mem_range] at hj; exact rch_congr hS.1 (by omega)
      have hrw : rwL es = rwL es' := by unfold rwL rhiL; rw [hl, hr]
      beta_reduce; rw [hc, hv, hrk, hrw, ha, hk]) hp
  exact h

/-! ## Controls -/

/-- Control (positive): block `t`'s own kind has indicator `1`. -/
theorem ind_jOf_self (κ : Kind) (t : ℕ) : zlmFR.Ind κ (jOf κ t) t = 1 := by rw [ind_jOf, if_pos rfl]

/-- Control (negative): every other kind has indicator `0` (the indicators do not overlap). -/
theorem ind_ne {κ : Kind} {t : ℕ} {j : Fin 9} (h : j ≠ jOf κ t) : zlmFR.Ind κ j t = 0 := by
  rw [ind_jOf, if_neg h]

/-- Control (negative): a pinned row of a kind's matrix is zero (`chain` pins `h_in`, row 0). -/
theorem kMat_pinned (C : Block.Pos → Block.Pos → Bool) (k : Fin (2 ^ 14)) :
    kMat C (bkIdx .chain) ⟨0, by norm_num⟩ k = 0 := by
  simp [kMat, bkOf_idx, isZeroRow, zeroRows]

/-- Control (positive): an unpinned row of a non-`free` kind is the circuit's row (`stream`
pins only slot 8; row 0 is `h_in`'s bit 0). -/
theorem kMat_row (C : Block.Pos → Block.Pos → Bool) (k : Fin (2 ^ 14)) :
    kMat C (bkIdx .stream) ⟨0, by norm_num⟩ k = ProductCircuit.ofBool F (C ⟨0, by norm_num⟩ k) := by
  simp [kMat, bkOf_idx, isZeroRow, zeroRows]

/-- Control (positive): the `free` kind's matrix is the identity (`(var k, var k)`). -/
theorem kMat_free_id (C : Block.Pos → Block.Pos → Bool) (z : Fin (2 ^ 14) → F) (p : Fin (2 ^ 14)) :
    ∑ k, kMat C (bkIdx .free) p k * z k = z p := kMat_free C z p

/-- Control (negative): a node's first block is not a `chain` block, a leaf's every block is. -/
theorem jOf_controls : jOf .N30 0 = bkIdx .streamStart ∧ jOf .L32 5 = bkIdx .chain ∧
    jOf .N30 0 ≠ bkIdx .chain := by
  refine ⟨rfl, rfl, by decide⟩

end FR.Snd
