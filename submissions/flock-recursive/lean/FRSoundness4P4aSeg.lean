-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.10 rows Z1 and S1 for a segment; stage P4a).
import FRSoundness4P4aNames
import FRSoundnessExtLeaf
import FRSegment

/-!
# A segment's Z and S truths, and `SegHolds` from them (B-12)

A segment of kind `κ` proves `1 ≤ n ≤ cap κ = 2^nb` steps on its blocks `0 … L` (`L = n − 1`);
the blocks past `L` are free. Two weights see `L` (`FRSegTarget4`):

* **Z2's target** is the chain target on the blocks `t ≤ L` and `0` past (`EtSeg`, the range
  factor). **`zHolds_seg_block`**: Z's statement at `zlm4` gives every used block's chain R1CS.
* **S2's weight** has its successor **masked at `L`** (`shiftSeg_cube`: `[y′ = y + 1 ∧ y ≠ L]`) and
  its end at block `L` (`eq(τ, L)·h̃`): **`wSeg`**, the residuals **`resSeg`**, the truth
  **`ShHoldsSeg`** (the links before `L`, the start, the end at `L`, and what the residual says of
  the free blocks), **`sh_sum_seg`** (the true sum is the target plus the batched residual),
  **`shHoldsSeg_of_res`**, **`res_ne_seg`**.
* **`chainLinks_of_shHoldsSeg`**: the masked truth at `L = n − 1` is `leaf_sound`'s `ChainLinks n`.
* **`segHolds_of_truths`**: Z's statement, the masked S truth with the statement's boundary, `L = n − 1`
  and `1 ≤ n ≤ cap` give **`SegHolds κ ⟨s, h, n⟩`** on the decoded blocks, hence (`seg_sound`)
  `chainEnd s n = h`.
* **`lastL_eq`**: `lastL es = n − 1` when `stmt` holds `n` with `1 ≤ n ≤ 2^18`.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl ProductCircuit

set_option linter.constructorNameAsVariable false

/-! ## The masked S2 weight -/

section Weight
variable {nb : ℕ}

/-- **A segment's In-block weight**: the successor masked at `Lb`, `[1 ≤ y ∧ y − 1 ≠ Lb] eq(τ, y − 1)
+ κ_s [y = 0]`. -/
def shSeg (τ : Fin nb → F) (κ : F) (Lb y : ℕ) : F :=
  (if 1 ≤ y ∧ y - 1 ≠ Lb then eqAtR τ (y - 1) else 0) + κ * if y = 0 then 1 else 0

/-- **A segment's S2 weight**: `h_out` (slot `256 + σ`) out at `eq(τ, y)`, `d` (slot `520 + σ`) in at
`shSeg`. -/
def wSeg (τ : Fin nb → F) (θ : Fin 10 → F) (κ : F) (Lb y q : ℕ) : F :=
  eqAtR τ y * slotT θ 256 q + shSeg τ κ Lb y * slotT θ 520 q

/-- **A segment's residuals** (`J = 2`): `R_0(u)` is `h_out(u) + [u + 1 < 2^nb ∧ u ≠ L] d(u + 1) +
[u = L] h`, `R_1` the start `d(0) + s`, on the slot bits `q < 256`. -/
def resSeg (nb Lb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) (j u q : ℕ) : F :=
  if q < 256 then
    (if j = 0 then z u (256 + q) + (if u + 1 < 2 ^ nb ∧ u ≠ Lb then z (u + 1) (520 + q) else 0) +
        (if u = Lb then hb q else 0)
      else if j = 1 then z 0 (520 + q) + sb q else 0)
  else 0

/-- **A segment's S truth** (the residuals vanish): the links `y → y + 1` for `y ≠ L`, block `0`'s
`d` is the start, block `L`'s `h_out` is the end, and (if `L` is not the top block) the top
block's `h_out` is `0`. The zero blocks past `L` meet the last two parts. -/
def ShHoldsSeg (nb Lb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) : Prop :=
  (∀ y, y + 1 < 2 ^ nb → y ≠ Lb → ∀ σ < 256, z (y + 1) (520 + σ) = z y (256 + σ)) ∧
    (∀ σ < 256, z 0 (520 + σ) = sb σ) ∧ (∀ σ < 256, z Lb (256 + σ) = hb σ) ∧
    (Lb ≠ 2 ^ nb - 1 → ∀ σ < 256, z (2 ^ nb - 1) (256 + σ) = 0)

theorem resSeg_zero (Lb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) (u q : ℕ) :
    resSeg nb Lb z sb hb 0 u q = if q < 256 then z u (256 + q) +
      (if u + 1 < 2 ^ nb ∧ u ≠ Lb then z (u + 1) (520 + q) else 0) +
        (if u = Lb then hb q else 0) else 0 := by
  simp only [resSeg, ↓reduceIte]

theorem resSeg_one (Lb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) (u q : ℕ) :
    resSeg nb Lb z sb hb 1 u q = if q < 256 then z 0 (520 + q) + sb q else 0 := by
  simp only [resSeg, one_ne_zero, ↓reduceIte]

/-- **A segment's true S2 sum** is the target `eq(τ, L) h̃(θ) + κ_s s̃(θ)` plus the residual. -/
theorem sh_sum_seg {Lb : ℕ} (hL : Lb < 2 ^ nb) (τ : Fin nb → F) (θ : Fin 10 → F) (κ : F)
    (z : ℕ → ℕ → F) (sb hb : ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), wSeg τ θ κ Lb y q * z y q =
      eqAtR τ Lb * thS θ hb + κ * thS θ sb + resSum nb 2 (resSeg nb Lb z sb hb) τ θ κ := by
  set O : ℕ → F := fun y => thS θ fun σ => z y (256 + σ)
  set I : ℕ → F := fun y => thS θ fun σ => z y (520 + σ)
  set X : ℕ → F := fun u => if u + 1 < 2 ^ nb ∧ u ≠ Lb then I (u + 1) else 0
  have hL' : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), wSeg τ θ κ Lb y q * z y q =
      ∑ y ∈ range (2 ^ nb), (eqAtR τ y * O y + shSeg τ κ Lb y * I y) := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp only [wSeg, add_mul, sum_add_distrib, mul_assoc]
    rw [← mul_sum, ← mul_sum, sum_slotT θ (by norm_num), sum_slotT θ (by norm_num)]
    rfl
  have hN : 2 ^ nb = (2 ^ nb - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have hS : ∑ y ∈ range (2 ^ nb), shSeg τ κ Lb y * I y =
      ∑ u ∈ range (2 ^ nb), eqAtR τ u * X u + κ * I 0 := by
    have e1 : ∑ y ∈ range (2 ^ nb), shSeg τ κ Lb y * I y =
        ∑ y ∈ range (2 ^ nb), (if 1 ≤ y ∧ y - 1 ≠ Lb then eqAtR τ (y - 1) * I y else 0) +
          κ * I 0 := by
      simp only [shSeg, add_mul, sum_add_distrib, ite_mul, zero_mul, mul_ite, mul_one,
        mul_zero, sum_ite_eq', mem_range, Nat.two_pow_pos, if_true]
    have e2 : ∑ y ∈ range (2 ^ nb), (if 1 ≤ y ∧ y - 1 ≠ Lb then eqAtR τ (y - 1) * I y else 0) =
        ∑ u ∈ range (2 ^ nb), eqAtR τ u * X u := by
      rw [hN, sum_range_succ', sum_range_succ, if_neg (by omega), add_zero]
      simp only [X, mul_ite, mul_zero]
      rw [if_neg (by omega), add_zero]
      refine sum_congr rfl fun u hu => ?_
      have := mem_range.1 hu
      simp only [Nat.add_sub_cancel]
      by_cases h : u = Lb
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_pos ⟨by omega, h⟩, if_pos ⟨by omega, h⟩]
    rw [e1, e2]
  have hR0 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resSeg nb Lb z sb hb 0 u q =
      O u + X u + (if u = Lb then thS θ hb else 0) := by
    intro u
    simp only [resSeg_zero, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    simp only [X, O, I, thS]
    split_ifs <;> simp only [mul_add, sum_add_distrib, add_zero]
  have hR1 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resSeg nb Lb z sb hb 1 u q = I 0 + thS θ sb := by
    intro u
    simp only [resSeg_one, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    simp only [I, thS, mul_add, sum_add_distrib]
  have hres : resSum nb 2 (resSeg nb Lb z sb hb) τ θ κ =
      ∑ u ∈ range (2 ^ nb), eqAtR τ u * (O u + X u + (if u = Lb then thS θ hb else 0)) +
        κ * (I 0 + thS θ sb) := by
    simp only [resSum, sum_range_succ, sum_range_zero, zero_add, pow_zero, one_mul, pow_one]
    rw [sum_comm, sum_comm (s := range (2 ^ 10))]
    simp only [mul_assoc, ← mul_sum, hR0, hR1, ← sum_mul, sum_eqAtR_one, one_mul]
  rw [hL', hres, sum_add_distrib, hS]
  simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_range, hL, if_true]
  linear_combination (-(eqAtR τ Lb * thS θ hb + κ * thS θ sb)) * CharTwo.two_eq_zero (R := F)

theorem shHoldsSeg_of_res {Lb : ℕ} (hL : Lb < 2 ^ nb) {z : ℕ → ℕ → F} {sb hb : ℕ → F}
    (h : ∀ j < 2, ∀ u < 2 ^ nb, ∀ q < 2 ^ 10, resSeg nb Lb z sb hb j u q = 0) :
    ShHoldsSeg nb Lb z sb hb := by
  refine ⟨fun y hy hyL σ hσ => ?_, fun σ hσ => ?_, fun σ hσ => ?_, fun hLt σ hσ => ?_⟩
  · have e := h 0 (by norm_num) y (by omega) σ (by omega)
    rw [resSeg_zero, if_pos hσ, if_pos ⟨hy, hyL⟩, if_neg hyL, add_zero] at e
    exact (CharTwo.add_eq_zero.mp e).symm
  · have e := h 1 (by norm_num) 0 (Nat.two_pow_pos _) σ (by omega)
    rw [resSeg_one, if_pos hσ] at e
    exact CharTwo.add_eq_zero.mp e
  · have e := h 0 (by norm_num) Lb hL σ (by omega)
    rw [resSeg_zero, if_pos hσ, if_neg (fun h => h.2 rfl), if_pos rfl, add_zero] at e
    exact CharTwo.add_eq_zero.mp e
  · have e := h 0 (by norm_num) (2 ^ nb - 1) (Nat.sub_lt (Nat.two_pow_pos _) one_pos) σ (by omega)
    rw [resSeg_zero, if_pos hσ, if_neg (by omega), if_neg (Ne.symm hLt), add_zero, add_zero] at e
    exact e

/-- **Some segment residual table is nonzero** when the masked S truth fails. -/
theorem res_ne_seg {Lb : ℕ} (hL : Lb < 2 ^ nb) {z : ℕ → ℕ → F} {sb hb : ℕ → F}
    (h : ¬ ShHoldsSeg nb Lb z sb hb) :
    ∃ j < 2, ∃ u < 2 ^ nb, ∃ q < 2 ^ 10, resSeg nb Lb z sb hb j u q ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (shHoldsSeg_of_res hL hc)

end Weight

/-! ## The masked truth is `leaf_sound`'s `ChainLinks` -/

/-- Block `blk` of the decoded witness (`Block.Pos`-indexed). -/
def zBlkC (zw : Wit) (κ : CKind) (L es : Log) (blk : ℕ) : Block.Pos → F :=
  fun k => zw κ L es (blk * 2 ^ Blake2sCircuit.m + k.val)

/-- The decoded witness by block and position (`zNode`'s form). -/
def zNodeC (zw : Wit) (κ : CKind) (L es : Log) (blk p : ℕ) : F := zw κ L es (blk * 2 ^ 14 + p)

theorem zBlkC_pos (zw : Wit) (κ : CKind) (L es : Log) (blk x : ℕ) (hx : x < 2 ^ 14) :
    zBlkC zw κ L es blk (pos x) = zNodeC zw κ L es blk x := by
  simp only [zBlkC, zNodeC, pos, Nat.mod_eq_of_lt hx]

theorem sbL_seg {κ : CKind} (hκ : κ.isNode = false) (es : Log) {σ : ℕ} (hσ : σ < 256) :
    sbL κ es σ = ofBool F (Block.digestBit (bytesAt (entAt es 0).1 87 32) σ) := by
  simp only [sbL, bndL, hκ, Bool.false_eq_true, ite_false, List.getD_cons_zero,
    List.getD_cons_succ, ofBool]
  rw [show (103 : ℕ) = 87 + 16 from rfl, digBit_readF _ _ hσ]

theorem hbL_seg {κ : CKind} (hκ : κ.isNode = false) (es : Log) {σ : ℕ} (hσ : σ < 256) :
    hbL κ es σ = ofBool F (Block.digestBit (bytesAt (msgAt es 1) 1 32) σ) := by
  simp only [hbL, bndL, hκ, Bool.false_eq_true, ite_false, List.getD_cons_zero,
    List.getD_cons_succ, ofBool]
  rw [show (17 : ℕ) = 1 + 16 from rfl, digBit_readF _ _ hσ]

/-- **The masked S truth at `L = n − 1` is `ChainLinks n`** over the decoded blocks, with the start
`hdr.pub` (seed bytes 87 …) and the end `stmt` bytes 1–32. -/
theorem chainLinks_of_shHoldsSeg {zw : Wit} {κ : CKind} (hκ : κ.isNode = false) {L es : Log}
    {n : ℕ} (hn : 1 ≤ n) (hcap : n ≤ 2 ^ nbC κ)
    (h : ShHoldsSeg (nbC κ) (n - 1) (zNodeC zw κ L es) (sbL κ es) (hbL κ es)) :
    Leaf.ChainLinks n (zBlkC zw κ L es) (bytesAt (entAt es 0).1 87 32)
      (bytesAt (msgAt es 1) 1 32) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨fun i hi j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [zBlkC_pos _ _ _ _ _ _ (by simp only [Chain.dBase]; omega),
      zBlkC_pos _ _ _ _ _ _ (by omega)]
    exact h1 i (by omega) (by omega) j hj
  · rw [zBlkC_pos _ _ _ _ _ _ (by simp only [Chain.dBase]; omega), ← sbL_seg hκ es hj]
    exact h2 j hj
  · rw [zBlkC_pos _ _ _ _ _ _ (by omega), ← hbL_seg hκ es hj]
    exact h3 j hj

/-! ## Z's statement on a segment's used blocks -/

theorem mC6_q (κ : CKind) : mC 6 κ = 8 + qL κ := by
  unfold mC qL; rcases κ.m_mem with h | h | h <;> omega

/-- **`ZHolds` block by block**: on each of the `2^(m−14)` blocks, at each position, the kinds'
rows `(A z)(B z) = z + E`. -/
theorem zHolds_blocks {M : ZLM4} {zw : Wit} {L es : Log} (h : ZHolds M zw L es) :
    ∀ t < 2 ^ qL (kindOfC es), ∀ p : Fin (2 ^ 14),
      mvZ M zw M.Ak (kindOfC es) L es t p * mvZ M zw M.Bk (kindOfC es) L es t p =
        zBk zw (kindOfC es) L es t p + M.Et (kindOfC es) es t p := by
  have hℓ := mC6_q (kindOfC es)
  simp only [ZHolds, BHolds] at h
  intro t ht p
  have hp := p.isLt
  have hu : p.val / 64 + 256 * t < 2 ^ mC 6 (kindOfC es) := by
    rw [hℓ, pow_add]; norm_num at hp ⊢; omega
  have := h ⟨p.val % 64, Nat.mod_lt _ (by norm_num)⟩ ⟨_, hu⟩
  have h1 : (p.val / 64 + 256 * t) / 256 = t := by omega
  have h2 : pAt ⟨p.val % 64, Nat.mod_lt _ (by norm_num)⟩ (p.val / 64 + 256 * t) = p := by
    ext; simp only [pAt]; norm_num at hp; omega
  simpa only [aZ, bZ, zZ, eZ, h1, h2] using this

section SegZ
variable {indN : Rev4.NodeKind → Fin 9 → ℕ → F} {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F}
  {zw : Wit}

/-- A segment's block rows read kind `0` (`chain`) only. -/
theorem mvZ_seg (κ : Rev4.SegKind) (C : Block.Pos → Block.Pos → Bool) (L es : Log) (t : ℕ)
    (p : Fin (2 ^ 14)) :
    mvZ (zlm4 indN etN) zw (kMat C) (.seg κ) L es t p =
      ∑ k, kMat C (bkIdx .chain) p k * zBk zw (.seg κ) L es t k := by
  unfold mvZ
  rw [sum_eq_single (0 : Fin 9) (fun j _ hj => by
      have h0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp only [zlm4, h0, if_false, zero_mul])
    (fun h => absurd (mem_univ _) h)]
  simp only [zlm4, Fin.val_zero, if_true, one_mul]; rfl

/-- **Z's statement gives a segment's used blocks their chain R1CS** (B-12): on a block `t ≤ L`
the target is the chain block's. -/
theorem zHolds_seg_block {κ : Rev4.SegKind} {L es : Log} (hk : kindOfC es = .seg κ)
    (h : ZHolds (zlm4 indN etN) zw L es) {t : ℕ} (ht : t < 2 ^ qL (.seg κ)) (hL : t ≤ lastL es) :
    Block.HoldsE (Block.blockR1CS Chain.chainTarget) (Block.targetVal F Chain.chainTarget)
      (zBlkC zw (.seg κ) L es t) := by
  have hb := zHolds_blocks h t (by rw [hk]; exact ht)
  rw [hk] at hb
  intro p
  have e := hb p
  have hbk : BlockKind.chain ≠ .free := by decide
  rw [show (zlm4 indN etN).Ak = kMat Block.circuitR1CS.A from rfl,
    show (zlm4 indN etN).Bk = kMat Block.circuitR1CS.B from rfl, mvZ_seg, mvZ_seg,
    kMat_mulVec _ hbk pins_chain, kMat_mulVec _ hbk pins_chain] at e
  have hE : (zlm4 indN etN).Et (.seg κ) es t p = Block.targetVal F Chain.chainTarget p := by
    simp only [zlm4, EtSeg, if_pos hL, chainE_eq]
  have hz : (fun k => zBk zw (.seg κ) L es t k) = zBlkC zw (.seg κ) L es t := by
    funext k; simp only [zBk, zBlkC, mul_comm]
  rw [hE] at e
  rw [← hz]
  exact e

/-- **`L = n − 1`** when `stmt` holds `n` with `1 ≤ n ≤ 2^18` (`lastOps`' value). -/
theorem lastL_eq {es : Log} {n : ℕ} (h : nStmt es = n) (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 18) :
    lastL es = n - 1 := by
  unfold lastL; rw [h]; norm_num at h2 ⊢; omega

/-- **A segment's truths give `SegHolds`** (B-12): Z's statement at `zlm4`, the masked S truth with
the statement's boundary at `L = n − 1`, Boolean witness bits and `1 ≤ n ≤ cap` give the segment
circuit's content on the decoded blocks. -/
theorem segHolds_of_truths {κ : Rev4.SegKind} {L es : Log} (hk : kindOfC es = .seg κ)
    (hbool : ∀ b, BlockR1CS.IsBool (zw (.seg κ) L es b)) {n : ℕ} (hn : 1 ≤ n) (hcap : n ≤ κ.cap)
    (hL : lastL es = n - 1) (hZ : ZHolds (zlm4 indN etN) zw L es)
    (hS : ShHoldsSeg (nbC (.seg κ)) (n - 1) (zNodeC zw (.seg κ) L es) (sbL (.seg κ) es)
      (hbL (.seg κ) es)) :
    Rev4.SegHolds κ ⟨bytesAt (entAt es 0).1 87 32, bytesAt (msgAt es 1) 1 32, n⟩
      (zBlkC zw (.seg κ) L es) := by
  have hcap' : n ≤ 2 ^ nbC (.seg κ) := hcap
  refine ⟨⟨hn, hcap⟩, fun i _ k => hbool _, fun i (hi : i < n) => ?_,
    chainLinks_of_shHoldsSeg rfl hn hcap' hS⟩
  exact zHolds_seg_block hk hZ (lt_of_lt_of_le hi hcap) (by omega)

/-- **A segment's truths prove its chain** (`seg_sound`). -/
theorem chainEnd_of_truths {κ : Rev4.SegKind} {L es : Log} (hk : kindOfC es = .seg κ)
    (hbool : ∀ b, BlockR1CS.IsBool (zw (.seg κ) L es b)) {n : ℕ} (hn : 1 ≤ n) (hcap : n ≤ κ.cap)
    (hL : lastL es = n - 1) (hZ : ZHolds (zlm4 indN etN) zw L es)
    (hS : ShHoldsSeg (nbC (.seg κ)) (n - 1) (zNodeC zw (.seg κ) L es) (sbL (.seg κ) es)
      (hbL (.seg κ) es)) :
    chainEnd (bytesAt (entAt es 0).1 87 32) n = bytesAt (msgAt es 1) 1 32 :=
  Rev4.seg_sound (st := ⟨bytesAt (entAt es 0).1 87 32, bytesAt (msgAt es 1) 1 32, n⟩)
    (segHolds_of_truths hk hbool hn hcap hL hZ hS)

end SegZ

/-! ## S2's tables, its doom and the S truth (the node's parts are parameters, S-G13 F3) -/

section S2
variable (wN : CKind → Log → ℕ → ℕ → F) (truthSN : CKind → Log → Log → Prop) (zw : Wit)

/-- **S2's weight** at S1's challenges: a segment's masked `wSeg` at `L = lastL`, a node's `wN`. -/
def wS (κ : CKind) (es : Log) (y q : ℕ) : F :=
  if κ.isNode then wN κ es y q
  else wSeg (ptOf (nbC κ) (tauL κ es)) (ptOf 10 (thL es)) (ksL es) (lastL es) y q

/-- **S2's tables** `[W, z]` over `2^(nb + 10)` cells, index `y + 2^nb q` (block bits first). -/
noncomputable def TS (L es : Log) : Array (Array F) :=
  #[Array.ofFn (n := 2 ^ (nbC (kindOfC es) + 10)) fun i =>
      wS wN (kindOfC es) es (i.val % 2 ^ nbC (kindOfC es)) (i.val / 2 ^ nbC (kindOfC es)),
    Array.ofFn (n := 2 ^ (nbC (kindOfC es) + 10)) fun i =>
      zNodeC zw (kindOfC es) L es (i.val % 2 ^ nbC (kindOfC es)) (i.val / 2 ^ nbC (kindOfC es))]

/-- **S1's final doom**: S2's initial claim is not the true sum at S1's challenges. -/
def S2Bad (L es : Log) : Prop := c0S es ≠ trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es))

/-- **S2's rounds' doom** (`T4.D2`, F, degree 2, from 114, `nb + 10` real rounds). -/
abbrev D2S : Log → Log → Prop :=
  T4.D2 114 16 readF (fun d => chF d 0) c0SL nrS innerExpr (TS wN zw)

/-- **The S truth** by kind: a segment's masked `ShHoldsSeg` at `L` with the statement's boundary
when `L` is one of the kind's blocks (`L < 2^nb`: `V_A`'s `n ≤ cap`; past them S2's initial claim
has no end term, `c0S_seg_out`), a node's `truthSN`. -/
def truthS (L es : Log) : Prop :=
  if (kindOfC es).isNode then truthSN (kindOfC es) L es
  else lastL es < 2 ^ nbC (kindOfC es) →
    ShHoldsSeg (nbC (kindOfC es)) (lastL es) (zNodeC zw (kindOfC es) L es) (sbL (kindOfC es) es)
      (hbL (kindOfC es) es)

end S2

end FR.Snd.P4a
