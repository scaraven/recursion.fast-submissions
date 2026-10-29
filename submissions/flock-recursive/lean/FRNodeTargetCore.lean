-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 4; stage RET-3): the declarations of
-- the 3.x verifier-shape modules that the revision 4 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRNodeTarget` (58), `FRVerifierImplNode` (64). Content: the
-- node's `targetS`/`linkW` specifications and their computable forms (`targetSNodeI`, `linkWI`,
-- `_meets`). The 3.x modules import this one.
import FRBlockKinds
import FRVIRFinalsCoreSG
import FRVerifierImplOps

/-! ## From `FRNodeTarget` (58 declarations) -/

section

namespace FR

namespace NodeT

open Finset RecursionFast Impl Kinds Stream

/-- A Boolean as an F value. -/
def bF (b : Bool) : F := if b then 1 else 0

/-- A target's bit at position `p` as an F value (`0` where the position is not pinned). -/
def tgtE (tgt : Block.Target) (p : ℕ) : F := bF (tgt (ProductCircuit.pos p) == some true)

/-- **The public target of node block `blk`** (A.6; S-G's `Snd.nodeKind` verbatim): the digest
chains (`streamStart`, then `streamTarget 1,481,344 k`), `hashStmt`'s A/B1/B2 per slot, per slot's
WOTS run chain `⌊o/3⌋`'s step `o mod 3`, the key leaf, the path pairs; `none` for `free` blocks. -/
def nodeTgt (blk : ℕ) : Option Block.Target :=
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

/-- **`E(blk, p)`**: the node's public target bit at block `blk`, position `p` (`0` on `free`). -/
def nodeE (blk p : ℕ) : F :=
  match nodeTgt blk with
  | some tgt => tgtE tgt p
  | none => 0

/-- The 16 block coordinates of `targetS`'s operand (`r[1 … 16]`, as `targetSLeafS`). -/
def rbOf (r : Array F) : Fin 16 → F := fun l => r.getD (1 + l) 0

/-- **The node's `targetS` specification** (`FRPubTarget.targetS` over `8 + 16` variables: the
position's 8 high bits `hi` low, the block high; `E(σ, (hi, blk)) = E(blk, σ + 64 hi)`). -/
def targetSNodeS (r : Array F) : Array F :=
  Array.ofFn (n := 64) fun σ => FR.targetS (ℓ := 8 + 16) (Fin.append (zLo r) (rbOf r))
    (fun σ u => nodeE (u.val / 256) (σ + 64 * (u.val % 256))) σ

/-- **The block sum** `G(p) = Σ_blk eq(r_blk, blk) · E(blk, p)`. -/
def blkW (rb : Fin 16 → F) (p : ℕ) : F := ∑ blk ∈ range (2 ^ 16), eqAtR rb blk * nodeE blk p

/-- **`targetS` through the block sum**: `P^e(σ) = Σ_hi eq(r_lo, hi) · G(σ + 64 hi)`. -/
theorem targetSNode_blk (r : Array F) : targetSNodeS r = Array.ofFn (n := 64) fun σ =>
    ∑ hi ∈ range 256, eqAtR (zLo r) hi * blkW (rbOf r) (σ + 64 * hi) := by
  unfold targetSNodeS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [FR.targetS, ← (joinEquiv 8 16).sum_comp, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun hi => eqAtR (zLo r) hi * blkW (rbOf r) (σ + 64 * hi))]
  refine Finset.sum_congr rfl fun hi _ => ?_
  have h1 : ∀ t : Fin (2 ^ 16), (join hi t).val / 256 = t.val := fun t => by
    show (2 ^ 8 * t.val + hi.val) / 256 = t.val
    have := hi.isLt; omega
  have h2 : ∀ t : Fin (2 ^ 16), (join hi t).val % 256 = hi.val := fun t => by
    show (2 ^ 8 * t.val + hi.val) % 256 = hi.val
    have := hi.isLt; omega
  simp only [show ∀ t, (joinEquiv 8 16) (hi, t) = join hi t from fun _ => rfl, eq_append_join,
    h1, h2, blkW, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun blk => eqAtR (zLo r) hi * (eqAtR (rbOf r) blk *
    nodeE blk (σ + 64 * hi)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eq_cube, eq_cube]
  unfold eqAtR
  ring

section Bits

private theorem pv {p : ℕ} (hp : p < 2 ^ 14) :
    ((ProductCircuit.pos p : Block.Pos) : ℕ) = p := ProductCircuit.pos_val hp

theorem lo32_bit {t i : ℕ} (ht : t < 2 ^ 32) :
    t.toUInt64.toUInt32.toBitVec.getLsbD i = (decide (i < 32) && t.testBit i) := by
  simp only [Nat.toUInt64, UInt64.toUInt32, UInt32.toBitVec_ofNat', BitVec.getLsbD_ofNat]
  simp [Nat.mod_eq_of_lt (lt_trans ht (by norm_num : (2:ℕ) ^ 32 < 18446744073709551616))]

theorem hi32_bit {t i : ℕ} (ht : t < 2 ^ 32) :
    (t.toUInt64 >>> 32).toUInt32.toBitVec.getLsbD i = false := by
  simp only [Nat.toUInt64, UInt64.toUInt32]
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat, UInt32.toBitVec_ofNat',
    BitVec.getLsbD_ofNat]
  have h1 : (UInt64.ofNat t).toNat = t := by
    first
    | exact UInt64.toNat_ofNat_of_lt' (lt_trans ht (by norm_num))
    | (simp only [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (lt_trans ht (by norm_num)))
    | (simp; exact Nat.mod_eq_of_lt (lt_trans ht (by norm_num)))
  rw [h1, show 32 % 2 ^ 64 % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ht]
  simp

theorem u8_bit (i b : ℕ) :
    i.toUInt8.toBitVec.getLsbD b = (decide (b < 8) && i.testBit b) := by
  simp [Nat.toUInt8, UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat]

/-- **The stream counter split off** (`t = 64 v`, `v < 2^26`): `t_lo`'s bit `6 + j` is bit `j` of
`v`, every other bit is the counter-free target's. -/
theorem tgtE_ctr {v p : ℕ} (hv : v < 2 ^ 26) (hp : p < 2 ^ 14) (fin : Bool) :
    tgtE (blockTarget (64 * v) fin) p = tgtE (blockTarget 0 fin) p +
      if 1030 ≤ p ∧ p < 1056 then bF (v.testBit (p - 1030)) else 0 := by
  have h64 : 64 * v < 2 ^ 32 := by norm_num at hv ⊢; omega
  unfold tgtE blockTarget
  rw [pv hp, lo32_bit h64, lo32_bit (show 0 < 2 ^ 32 by norm_num), hi32_bit h64,
    hi32_bit (show 0 < 2 ^ 32 by norm_num), show 64 * v = 2 ^ 6 * v from rfl,
    Nat.testBit_two_pow_mul]
  by_cases a : p < 1024
  · simp [a, show ¬ 1030 ≤ p by omega, bF]
  by_cases b : p < 1056
  · by_cases c : 1030 ≤ p
    · simp [a, b, c, show p - 1024 - 6 = p - 1030 by omega, show 6 ≤ p - 1024 by omega,
        show p - 1024 < 32 by omega, bF]
    · simp [a, b, c, show ¬ (6 ≤ p - 1024) by omega, bF]
  · simp [a, b]

/-- **`w43`'s step fields split off**: byte 9 is `i`, byte 10 is `s`, every other bit is
`w43 0 0`'s. -/
theorem tgtE_w43 (i s : ℕ) {p : ℕ} (hp : p < 2 ^ 14) :
    tgtE (w43 i.toUInt8 s.toUInt8).target p = tgtE (w43 0 0).target p +
      (if 584 ≤ p ∧ p < 592 then bF (i.testBit (p - 584)) else 0) +
      (if 592 ≤ p ∧ p < 600 then bF (s.testBit (p - 592)) else 0) := by
  unfold tgtE Kind.target w43
  rw [pv hp]
  by_cases a : p < 512
  · simp [a, show ¬ 584 ≤ p by omega, show ¬ 592 ≤ p by omega]
  by_cases b : p < 1024
  · have a' : ¬ p < 256 := by omega
    by_cases c9 : (p - 512) / 8 = 9
    · simp only [a, a', b, c9, ite_false, ite_true, show (9 : ℕ) ≠ 0 by omega, Option.map_some,
        u8_bit, show (p - 512) % 8 = p - 584 by omega, show 584 ≤ p by omega,
        show p < 592 by omega, show p - 584 < 8 by omega, show ¬ 592 ≤ p by omega,
        decide_true, Bool.true_and, and_true, false_and, add_zero]
      simp [bF]
    by_cases c10 : (p - 512) / 8 = 10
    · simp only [a, a', b, c10, ite_false, ite_true, show (10 : ℕ) ≠ 0 by omega,
        show (10 : ℕ) ≠ 9 by omega, Option.map_some, u8_bit,
        show (p - 512) % 8 = p - 592 by omega, show 592 ≤ p by omega, show p < 600 by omega,
        show p - 592 < 8 by omega, show ¬ (584 ≤ p ∧ p < 592) by omega, decide_true,
        Bool.true_and, and_true]
      simp [bF]
    · simp [a, a', b, c9, c10, show ¬ (584 ≤ p ∧ p < 592) by omega,
        show ¬ (592 ≤ p ∧ p < 600) by omega]
  · simp [a, b, show ¬ (584 ≤ p ∧ p < 592) by omega, show ¬ (592 ≤ p ∧ p < 600) by omega]

/-- Past position 1,152 no kind pins anything. -/
theorem tgtE_blockTarget_hi {t p : ℕ} (fin : Bool) (h1 : 1153 ≤ p) (hp : p < 2 ^ 14) :
    tgtE (blockTarget t fin) p = 0 := by
  unfold tgtE blockTarget
  rw [pv hp]
  simp [show ¬ p < 1024 by omega, show ¬ p < 1056 by omega, show ¬ p < 1088 by omega,
    show ¬ p < 1120 by omega, show ¬ p < 1152 by omega, show p ≠ 1152 by omega, bF]

theorem tgtE_kind_hi (κ : Kinds.Kind) {p : ℕ} (h1 : 1153 ≤ p) (hp : p < 2 ^ 14) :
    tgtE κ.target p = 0 := by
  have := κ.target_ge (k := ProductCircuit.pos p) (by rw [pv hp]; omega)
  unfold tgtE at *
  rw [this]
  exact tgtE_blockTarget_hi κ.fin h1 hp

end Bits

/-- The ten constant classes' targets: `streamStart`, the stream body with the counter removed, a
digest chain's last block (`t = 1,481,344`, final), `hashA`, `hashB1 tagNode`, `hashB2`, `w43`
with `i = s = 0`, `hashB1 tagWotsLeaf`, `streamEnd41`, `hashB1 tagSigNode`. -/
def cls : ℕ → Block.Target
  | 0 => streamStart.target
  | 1 => blockTarget 0 false
  | 2 => blockTarget 1481344 true
  | 3 => hashA.target
  | 4 => (hashB1 RecursionFast.tagNode).target
  | 5 => hashB2.target
  | 6 => (w43 0 0).target
  | 7 => (hashB1 RecursionFast.tagWotsLeaf).target
  | 8 => streamEnd41.target
  | _ => (hashB1 RecursionFast.tagSigNode).target

/-- Slot `σ`'s first WOTS block. -/
def wb (σ : ℕ) : ℕ := Layout.wotsBase + Layout.wotsSlot * σ

section Closed

variable (rb : Fin 16 → F)

/-- A stream body's counter bits: `Σ_{k<n} eq(r_blk, lo + k) · bit_{p−1030}(k + 2)` on `t_lo`'s
bits `6 … 31` (block `lo + k` has `t = 64 (k + 2)`). -/
def ctrC (lo n p : ℕ) : F :=
  if 1030 ≤ p ∧ p < 1056 then
    ∑ k ∈ range n, eqAtR rb (lo + k) * bF ((k + 2).testBit (p - 1030)) else 0

/-- Digest chain `σ`: `streamStart`, the body (counter `64 (k + 1)`), the last block. -/
def chainC (σ p : ℕ) : F :=
  eqAtR rb (σ * Layout.chainN) * tgtE (cls 0) p +
    (∑ k ∈ range (Layout.chainN - 2), eqAtR rb (σ * Layout.chainN + 1 + k)) * tgtE (cls 1) p +
    ctrC rb (σ * Layout.chainN + 1) (Layout.chainN - 2) p +
    eqAtR rb (σ * Layout.chainN + (Layout.chainN - 1)) * tgtE (cls 2) p

/-- `hashStmt`'s blocks A, B1, B2 of both slots. -/
def stmtC (p : ℕ) : F :=
  ∑ σ ∈ range 2, (eqAtR rb (Layout.stmtBase + 3 * σ) * tgtE (cls 3) p +
    eqAtR rb (Layout.stmtBase + 3 * σ + 1) * tgtE (cls 4) p +
    eqAtR rb (Layout.stmtBase + 3 * σ + 2) * tgtE (cls 5) p)

/-- `w43`'s step fields: `Σ_{o<399} eq(r_blk, wb + o) · bit_b(⌊o/3⌋)` (byte 9) and `bit_b(o mod
3)` (byte 10), the 399-term table sums. -/
def w43C (σ p : ℕ) : F :=
  (if 584 ≤ p ∧ p < 592 then
    ∑ o ∈ range 399, eqAtR rb (wb σ + o) * bF ((o / 3).testBit (p - 584)) else 0) +
  (if 592 ≤ p ∧ p < 600 then
    ∑ o ∈ range 399, eqAtR rb (wb σ + o) * bF ((o % 3).testBit (p - 592)) else 0)

/-- Slot `σ`'s WOTS run: the 399 `w43` steps, the key leaf (`hashB1 tagWotsLeaf`, 65 stream
blocks with counter `64 (k + 2)`, `streamEnd41`), the 16 path pairs. -/
def wotsC (σ p : ℕ) : F :=
  (∑ o ∈ range 399, eqAtR rb (wb σ + o)) * tgtE (cls 6) p + w43C rb σ p +
    eqAtR rb (wb σ + 399) * tgtE (cls 7) p +
    (∑ k ∈ range 65, eqAtR rb (wb σ + 400 + k)) * tgtE (cls 1) p + ctrC rb (wb σ + 400) 65 p +
    eqAtR rb (wb σ + 465) * tgtE (cls 8) p +
    ∑ t ∈ range 16, (eqAtR rb (wb σ + 466 + 2 * t) * tgtE (cls 9) p +
      eqAtR rb (wb σ + 467 + 2 * t) * tgtE (cls 5) p)

/-- **The closed form of `G(p)`** (A.8's node form): both chains, `hashStmt`, both WOTS runs. -/
def Gc (p : ℕ) : F := ∑ σ ∈ range 2, chainC rb σ p + stmtC rb p + ∑ σ ∈ range 2, wotsC rb σ p

end Closed

section Proof

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (a n : ℕ) (f : ℕ → M) :
    ∑ x ∈ range (a * n), f x = ∑ i ∈ range a, ∑ k ∈ range n, f (i * n + k) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem sum_range_pairs {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ x ∈ range (2 * n), f x = ∑ t ∈ range n, (f (2 * t) + f (2 * t + 1)) := by
  rw [mul_comm, sum_range_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Finset.sum_range_succ, mul_comm]

private theorem sum_ite_c {n : ℕ} (c : Prop) [Decidable c] (g h : ℕ → F) :
    ∑ k ∈ range n, g k * (if c then h k else 0) = if c then ∑ k ∈ range n, g k * h k else 0 := by
  split_ifs <;> simp

variable (rb : Fin 16 → F)

theorem nodeE_free {blk : ℕ} (h : Layout.wmBase ≤ blk) (p : ℕ) : nodeE blk p = 0 := by
  have : nodeTgt blk = none := by
    unfold nodeTgt
    have h1 : ¬ blk < 2 * Layout.chainN := by simp only [Layout.wmBase, Layout.wotsBase,
      Layout.stmtBase, Layout.wotsSlot, Layout.chainN] at *; omega
    have h2 : ¬ blk < Layout.wotsBase := by simp only [Layout.wmBase, Layout.wotsBase,
      Layout.stmtBase, Layout.wotsSlot, Layout.chainN] at *; omega
    simp [h1, h2, show ¬ blk < Layout.wmBase by omega]
  simp [nodeE, this]

/-- Chain `σ`'s block `k`. -/
theorem nodeE_chain {σ k : ℕ} (hσ : σ < 2) (hk : k < Layout.chainN) (p : ℕ) :
    nodeE (σ * Layout.chainN + k) p =
      if k = 0 then tgtE (cls 0) p else tgtE (streamTarget 1481344 k) p := by
  have hN : Layout.chainN = 23146 := rfl
  have h1 : σ * Layout.chainN + k < 2 * Layout.chainN := by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> omega
  have h2 : (σ * Layout.chainN + k) % Layout.chainN = k := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  simp only [nodeE, nodeTgt, h1, h2, ite_true]
  split_ifs <;> rfl

theorem chain_part {σ : ℕ} (hσ : σ < 2) {p : ℕ} (hp : p < 2 ^ 14) :
    ∑ k ∈ range Layout.chainN, eqAtR rb (σ * Layout.chainN + k) *
      nodeE (σ * Layout.chainN + k) p = chainC rb σ p := by
  have hN : Layout.chainN = 23146 := rfl
  rw [show Layout.chainN = (Layout.chainN - 2) + 1 + 1 from by omega, Finset.sum_range_succ,
    Finset.sum_range_succ', ← show Layout.chainN = (Layout.chainN - 2) + 1 + 1 from by omega]
  have hbody : ∀ k ∈ range (Layout.chainN - 2),
      eqAtR rb (σ * Layout.chainN + (k + 1)) * nodeE (σ * Layout.chainN + (k + 1)) p =
        eqAtR rb (σ * Layout.chainN + 1 + k) * tgtE (cls 1) p +
          eqAtR rb (σ * Layout.chainN + 1 + k) *
            (if 1030 ≤ p ∧ p < 1056 then bF ((k + 2).testBit (p - 1030)) else 0) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [nodeE_chain hσ (by omega), if_neg (by omega), show σ * Layout.chainN + (k + 1) =
      σ * Layout.chainN + 1 + k by omega, ← mul_add]
    congr 1
    have hct : streamTarget 1481344 (k + 1) = blockTarget (64 * (k + 2)) false := by
      unfold streamTarget ctrAt nBlocks
      rw [if_neg (by omega), show decide (k + 1 + 1 = (1481344 - 1) / 64 + 1) = false by
        simp; omega]
    rw [hct, tgtE_ctr (by omega) hp]
    rfl
  have hlast : streamTarget 1481344 (Layout.chainN - 2 + 1) = blockTarget 1481344 true := by
    unfold streamTarget ctrAt nBlocks
    rw [hN]
    rfl
  rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, ← Finset.sum_mul, sum_ite_c,
    nodeE_chain (k := 0) hσ (by omega), if_pos rfl,
    nodeE_chain (k := Layout.chainN - 2 + 1) hσ (by omega),
    if_neg (show Layout.chainN - 2 + 1 ≠ 0 by omega), hlast,
    show σ * Layout.chainN + (Layout.chainN - 2 + 1) = σ * Layout.chainN + (Layout.chainN - 1)
      by omega, add_zero]
  unfold chainC ctrC
  show _ = _ + _ * tgtE (blockTarget 1481344 true) p
  ring

theorem nodeE_stmt {x : ℕ} (hx : x < 6) (p : ℕ) :
    nodeE (Layout.stmtBase + x) p = tgtE (cls (3 + x % 3)) p := by
  have h1 : ¬ Layout.stmtBase + x < 2 * Layout.chainN := by simp [Layout.stmtBase]
  have h2 : Layout.stmtBase + x < Layout.wotsBase := by simp only [Layout.wotsBase]; omega
  simp only [nodeE, nodeTgt, h1, h2, ite_false, ite_true, Nat.add_sub_cancel_left]
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h <;> simp [h, cls]

theorem stmt_part (p : ℕ) :
    ∑ x ∈ range 6, eqAtR rb (Layout.stmtBase + x) * nodeE (Layout.stmtBase + x) p =
      stmtC rb p := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, sum_range_mul]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ' := Finset.mem_range.1 hσ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [nodeE_stmt (by omega), nodeE_stmt (by omega), nodeE_stmt (by omega)]
  simp only [show σ * 3 = 3 * σ by ring, add_assoc]
  have c0 : cls (3 + (3 * σ + 0) % 3) = cls 3 := by rw [show (3 * σ + 0) % 3 = 0 by omega]
  have c1 : cls (3 + (3 * σ + 1) % 3) = cls 4 := by rw [show (3 * σ + 1) % 3 = 1 by omega]
  have c2 : cls (3 + (3 * σ + 2) % 3) = cls 5 := by rw [show (3 * σ + 2) % 3 = 2 by omega]
  rw [c0, c1, c2, add_zero]

/-- The target of WOTS offset `o` (`o < 498`), as `nodeTgt` reads it. -/
def wotsTgt (o : ℕ) : Block.Target :=
  if o < 399 then (w43 (o / 3).toUInt8 (o % 3).toUInt8).target
  else if o = 399 then (hashB1 RecursionFast.tagWotsLeaf).target
  else if o < 465 then streamTarget 4265 (o - 399)
  else if o = 465 then streamEnd41.target
  else if (o - 466) % 2 = 0 then (hashB1 RecursionFast.tagSigNode).target else hashB2.target

theorem nodeE_wots {σ o : ℕ} (hσ : σ < 2) (ho : o < Layout.wotsSlot) (p : ℕ) :
    nodeE (wb σ + o) p = tgtE (wotsTgt o) p := by
  have hw : Layout.wotsSlot = 498 := rfl
  have hb : Layout.wotsBase = 46298 := rfl
  have hN : Layout.chainN = 23146 := rfl
  have hm : Layout.wmBase = 47294 := rfl
  have e : wb σ + o = Layout.wotsBase + (Layout.wotsSlot * σ + o) := by unfold wb; ring
  have h1 : ¬ wb σ + o < 2 * Layout.chainN := by rw [e]; omega
  have h2 : ¬ wb σ + o < Layout.wotsBase := by rw [e]; omega
  have h3 : wb σ + o < Layout.wmBase := by
    rw [e]; rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> omega
  have h4 : (wb σ + o - Layout.wotsBase) % Layout.wotsSlot = o := by
    rw [e, Nat.add_sub_cancel_left, Nat.mul_add_mod, Nat.mod_eq_of_lt ho]
  simp only [nodeE, nodeTgt, h1, h2, h3, h4, ite_false, ite_true]
  rfl

/-- `Σ_{o<498}` along the WOTS run's pieces. -/
theorem sum_wots (g : ℕ → F) :
    ∑ o ∈ range 498, g o = ∑ o ∈ range 399, g o + g 399 + ∑ k ∈ range 65, g (400 + k) +
      g 465 + ∑ t ∈ range 16, (g (466 + 2 * t) + g (467 + 2 * t)) := by
  have e1 : ∑ x ∈ range 66, g (399 + x) = g 399 + ∑ k ∈ range 65, g (400 + k) := by
    rw [Finset.sum_range_succ' (fun x => g (399 + x)) 65, add_comm]
    simp only [show ∀ k, 399 + (k + 1) = 400 + k from fun k => by omega, add_zero]
  have e2 : ∑ x ∈ range 33, g (399 + (66 + x)) =
      g 465 + ∑ t ∈ range 16, (g (466 + 2 * t) + g (467 + 2 * t)) := by
    rw [Finset.sum_range_succ' (fun x => g (399 + (66 + x))) 32, add_comm,
      show (32 : ℕ) = 2 * 16 from rfl, sum_range_pairs]
    simp only [show ∀ t, 399 + (66 + (2 * t + 1)) = 466 + 2 * t from fun t => by omega,
      show ∀ t, 399 + (66 + (2 * t + 1 + 1)) = 467 + 2 * t from fun t => by omega, add_zero]
  rw [show (498 : ℕ) = 399 + (66 + 33) from rfl, Finset.sum_range_add, Finset.sum_range_add, e1,
    e2]
  ring

theorem wots_part {σ : ℕ} (hσ : σ < 2) {p : ℕ} (hp : p < 2 ^ 14) :
    ∑ o ∈ range Layout.wotsSlot, eqAtR rb (wb σ + o) * nodeE (wb σ + o) p = wotsC rb σ p := by
  rw [show Layout.wotsSlot = 498 from rfl, sum_wots]
  have hw43 : ∀ o ∈ range 399, eqAtR rb (wb σ + o) * nodeE (wb σ + o) p =
      eqAtR rb (wb σ + o) * tgtE (cls 6) p +
        eqAtR rb (wb σ + o) * (if 584 ≤ p ∧ p < 592 then bF ((o / 3).testBit (p - 584)) else 0) +
        eqAtR rb (wb σ + o) * (if 592 ≤ p ∧ p < 600 then bF ((o % 3).testBit (p - 592)) else 0) := by
    intro o ho
    have ho' := Finset.mem_range.1 ho
    rw [nodeE_wots hσ (by simp [Layout.wotsSlot]; omega), wotsTgt, if_pos ho', tgtE_w43 _ _ hp]
    simp only [cls]
    ring
  have hctr : ∀ k ∈ range 65, eqAtR rb (wb σ + (400 + k)) * nodeE (wb σ + (400 + k)) p =
      eqAtR rb (wb σ + 400 + k) * tgtE (cls 1) p +
        eqAtR rb (wb σ + 400 + k) *
          (if 1030 ≤ p ∧ p < 1056 then bF ((k + 2).testBit (p - 1030)) else 0) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [nodeE_wots hσ (by simp [Layout.wotsSlot]; omega), wotsTgt, if_neg (by omega),
      if_neg (by omega), if_pos (by omega), ← add_assoc, ← mul_add]
    have hct : streamTarget 4265 (400 + k - 399) = blockTarget (64 * (k + 2)) false := by
      unfold streamTarget ctrAt nBlocks
      rw [if_neg (by omega), show 400 + k - 399 + 1 = k + 2 by omega,
        show decide (k + 2 = (4265 - 1) / 64 + 1) = false by simp; omega]
    rw [hct, tgtE_ctr (by omega) hp]
    rfl
  have hpath : ∀ t ∈ range 16, eqAtR rb (wb σ + (466 + 2 * t)) * nodeE (wb σ + (466 + 2 * t)) p +
      eqAtR rb (wb σ + (467 + 2 * t)) * nodeE (wb σ + (467 + 2 * t)) p =
      eqAtR rb (wb σ + 466 + 2 * t) * tgtE (cls 9) p +
        eqAtR rb (wb σ + 467 + 2 * t) * tgtE (cls 5) p := by
    intro t ht
    have ht' := Finset.mem_range.1 ht
    rw [nodeE_wots hσ (by simp [Layout.wotsSlot]; omega),
      nodeE_wots hσ (by simp [Layout.wotsSlot]; omega), wotsTgt, wotsTgt]
    simp only [show ¬ 466 + 2 * t < 399 by omega, show 466 + 2 * t ≠ 399 by omega,
      show ¬ 466 + 2 * t < 465 by omega, show 466 + 2 * t ≠ 465 by omega,
      show (466 + 2 * t - 466) % 2 = 0 by omega, show ¬ 467 + 2 * t < 399 by omega,
      show 467 + 2 * t ≠ 399 by omega, show ¬ 467 + 2 * t < 465 by omega,
      show 467 + 2 * t ≠ 465 by omega, show ¬ (467 + 2 * t - 466) % 2 = 0 by omega,
      ite_false, ite_true, add_assoc]
    rfl
  rw [Finset.sum_congr rfl hw43, Finset.sum_congr rfl hctr, Finset.sum_congr rfl hpath,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, sum_ite_c, sum_ite_c, sum_ite_c,
    nodeE_wots hσ (show 399 < Layout.wotsSlot by decide),
    nodeE_wots hσ (show 465 < Layout.wotsSlot by decide)]
  simp only [wotsTgt, show ¬ (399 : ℕ) < 399 by decide, show ¬ (465 : ℕ) < 399 by decide,
    show (465 : ℕ) ≠ 399 by decide, show ¬ (465 : ℕ) < 465 by decide, ite_true, ite_false]
  unfold wotsC w43C ctrC
  simp only [cls, add_assoc]

/-- **`targetS_node_eq`'s core: the block sum is the closed form** at every position. -/
theorem blkW_eq {p : ℕ} (hp : p < 2 ^ 14) : blkW rb p = Gc rb p := by
  have hsplit : 2 ^ 16 = (2 * Layout.chainN + 6 + 2 * Layout.wotsSlot) + 18242 := rfl
  have hm : Layout.wmBase = 2 * Layout.chainN + 6 + 2 * Layout.wotsSlot := rfl
  unfold blkW
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, sum_range_mul,
    sum_range_mul]
  rw [Finset.sum_eq_zero (s := range 18242) fun x _ => by
    rw [nodeE_free (by rw [hm]; omega), mul_zero], add_zero]
  unfold Gc
  rw [Finset.sum_congr rfl fun σ hσ => chain_part rb (Finset.mem_range.1 hσ) hp,
    show 2 * Layout.chainN = Layout.stmtBase from rfl, stmt_part]
  refine congrArg ((∑ σ ∈ range 2, chainC rb σ p + stmtC rb p) + ·) ?_
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [← wots_part rb (Finset.mem_range.1 hσ) hp]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [show Layout.stmtBase + 6 + (σ * Layout.wotsSlot + o) = wb σ + o by
    unfold wb; simp only [Layout.wotsBase]; ring]

end Proof

/-- Past position 1,152 the closed form vanishes (no kind pins anything there). -/
theorem Gc_hi (rb : Fin 16 → F) {p : ℕ} (h1 : 1153 ≤ p) (hp : p < 2 ^ 14) : Gc rb p = 0 := by
  have hcls : ∀ c, tgtE (cls c) p = 0 := by
    intro c
    rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | c <;>
      first | exact tgtE_kind_hi _ h1 hp | exact tgtE_blockTarget_hi _ h1 hp
  simp [Gc, chainC, stmtC, wotsC, w43C, ctrC, hcls, show ¬ 1030 ≤ p ∨ ¬ p < 1056 by omega,
    show ¬ (584 ≤ p ∧ p < 592) by omega, show ¬ (592 ≤ p ∧ p < 600) by omega,
    show ¬ (1030 ≤ p ∧ p < 1056) by omega]

/-- **`targetS_node_eq`** (A.8's node form): `P^e(σ) = Σ_hi eq(r_lo, hi) · Gc(σ + 64 hi)`, the
closed form `Gc` of `Σ_blk eq(r_blk, blk) E(blk, ·)`. -/
theorem targetS_node_eq (r : Array F) : targetSNodeS r = Array.ofFn (n := 64) fun σ =>
    ∑ hi ∈ range 256, eqAtR (zLo r) hi * Gc (rbOf r) (σ + 64 * hi) := by
  rw [targetSNode_blk]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => Finset.sum_congr rfl fun hi hh => ?_)
  rw [blkW_eq _ (by have := σ.isLt; have := Finset.mem_range.1 hh; omega)]

/-- A link family of a slot: `n` sources, source `t` at block `wb_σ + src t`, whose message field
`[off, off + len)` (bytes) equals bits `[mbo, mbo + 8 len)` of mirror source `mir t`. -/
structure Fam where
  /-- Sources per slot. -/
  n : ℕ
  /-- Source `t`'s block, relative to the slot's first WOTS block. -/
  src : ℕ → ℕ
  /-- The field's first message byte. -/
  off : ℕ
  /-- The field's length in bytes. -/
  len : ℕ
  /-- Source `t`'s mirror source in the `WM` map (A.6's `off_f + t`). -/
  mir : ℕ → ℕ
  /-- The field's first bit within its mirror's 256 bits. -/
  mbo : ℕ

/-- **The eight families** (§4.2; `x`, `j`, `end9`, `end41lo`, `end41hi`, `l`, `r0`, `r31`), with
A.6's pinned mirror offsets (revision 3.14) `x` 0, `j` 399, `end9` 400, `end41` 467 (shared by
`end41lo`/`end41hi`), `l` 533, `r0` 549, `r31` 565: sources `0 … 580`. -/
def fam : ℕ → Fam
  | 0 => ⟨399, id, 11, 32, id, 0⟩
  | 1 => ⟨400, id, 1, 8, fun _ => 399, 0⟩
  | 2 => ⟨67, (399 + ·), 9, 32, (400 + ·), 0⟩
  | 3 => ⟨66, (399 + ·), 41, 23, (467 + ·), 0⟩
  | 4 => ⟨66, (400 + ·), 0, 9, (467 + ·), 184⟩
  | 5 => ⟨16, fun t => 466 + 2 * t, 1, 32, (533 + ·), 0⟩
  | 6 => ⟨16, fun t => 466 + 2 * t, 33, 31, (549 + ·), 0⟩
  | 7 => ⟨16, fun t => 467 + 2 * t, 0, 1, (565 + ·), 0⟩
  | _ => ⟨0, id, 0, 0, id, 0⟩

/-- The mirror region's first block of slot `σ` (146 blocks per slot, four sources per block). -/
def wmB (σ : ℕ) : ℕ := Layout.wmBase + 146 * σ

/-- Source `t` of family `f`, slot `σ`: its block. -/
def srcB (σ f t : ℕ) : ℕ := wb σ + (fam f).src t

/-- Its mirror's block (`WM` map: source `g` in block `wmB σ + ⌊g/4⌋`). -/
def mirB (σ f t : ℕ) : ℕ := wmB σ + (fam f).mir t / 4

/-- The position of the field's bit `s` in the source block. -/
def fpos (f s : ℕ) : ℕ := 512 + 8 * (fam f).off + s

/-- The position of the field's bit `s` in the mirror block (elements `2 (g mod 4)`, `+1`). -/
def mpos (f t s : ℕ) : ℕ := 256 * ((fam f).mir t % 4) + (fam f).mbo + s

/-- The field's bits. -/
def fbits (f : ℕ) : ℕ := 8 * (fam f).len

/-- **The slot weight of a bit range**: `Σ_{s<L} eq(θ, s) eq(r_pos, base(s))`. -/
def slotWL (pos : ℕ → ℕ) (L : ℕ) (θ rp : Fin 10 → F) : F :=
  ∑ s ∈ range L, eqAtR θ s * eqAtR rp (pos s)

/-- **`linkW`'s specification** (A.8, revision 3.13): family `f`'s in-table weight at the Sh
point, `Σ_σ Σ_t eq(τ, src)·[eq(r_blk, src)·slotW(field) − eq(r_blk, mirBlk)·slotW(mirPos)]`. -/
def linkWS (f : ℕ) (τ : Fin 16 → F) (θ : Fin 10 → F) (rb : Fin 16 → F) (rp : Fin 10 → F) : F :=
  ∑ σ ∈ range 2, ∑ t ∈ range (fam f).n, eqAtR τ (srcB σ f t) *
    (eqAtR rb (srcB σ f t) * slotWL (fpos f) (fbits f) θ rp -
      eqAtR rb (mirB σ f t) * slotWL (mpos f t) (fbits f) θ rp)

/-- **`linkWAll`'s specification** (A.8, revision 3.14; a node): the 8 families' `linkWS` at the
packed points `tt = τ ‖ θ` (S1's 16 block, then 10 slot coordinates) and `rr = r_blk ‖ r_pos`
(S2's 16, then 10). -/
def linkWAllS (tt rr : Array F) : Array F :=
  Array.ofFn (n := nLinkFam) fun f => linkWS f (ptA 16 tt) (fun l => tt.getD (16 + l) 0)
    (ptA 16 rr) (fun l => rr.getD (16 + l) 0)

/-- **`shiftMask`'s specification** (A.9 `finSh`, a node; revision 3.14, the chain mask): the
block weights over the two chains' link blocks `c·N + k`, `k < N − 1` (`N = chainN`; block `y` is
linked to `y + 1` inside its chain): `Σ eq(τ, y) eq(r, y)`, `Σ eq(τ, y) eq(r, y + 1)`, and the two
starts' weight `eq(r, 0) + eq(r, N)`. -/
def shiftMaskS (τ r : Array F) : F × F × F :=
  (∑ c ∈ range 2, ∑ k ∈ range (Layout.chainN - 1),
      eqAtR (ptA 16 τ) (c * Layout.chainN + k) * eqAtR (ptA 16 r) (c * Layout.chainN + k),
   ∑ c ∈ range 2, ∑ k ∈ range (Layout.chainN - 1),
      eqAtR (ptA 16 τ) (c * Layout.chainN + k) * eqAtR (ptA 16 r) (c * Layout.chainN + k + 1),
   eqAtR (ptA 16 r) 0 + eqAtR (ptA 16 r) Layout.chainN)

section LinkProof

/-- Every source and mirror block is inside the node (`2^16` blocks), every field position inside
the collapse range (`2^10` positions). -/
theorem fam_bounds {f σ t s : ℕ} (hσ : σ < 2) (ht : t < (fam f).n) :
    srcB σ f t < 2 ^ 16 ∧ mirB σ f t < 2 ^ 16 ∧
      (s < fbits f → fpos f s < 2 ^ 10 ∧ mpos f t s < 2 ^ 10) := by
  have hw : wb σ ≤ 46796 := by unfold wb; simp only [Layout.wotsBase, Layout.wotsSlot,
    Layout.stmtBase, Layout.chainN]; omega
  have hm : wmB σ ≤ 47440 := by unfold wmB; simp only [Layout.wmBase, Layout.wotsBase,
    Layout.wotsSlot, Layout.stmtBase, Layout.chainN]; omega
  unfold srcB mirB fpos mpos fbits
  have h4 : ∀ g, g % 4 < 4 := fun g => Nat.mod_lt _ (by norm_num)
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;>
    simp only [fam, id] at ht ⊢ <;> (try have := h4 t) <;> (try have := h4 (400 + t)) <;>
    (try have := h4 (467 + t)) <;> (try have := h4 (533 + t)) <;> (try have := h4 (549 + t)) <;>
    (try have := h4 (565 + t)) <;> omega

theorem fbits_le (f : ℕ) : fbits f ≤ 2 ^ 10 := by
  unfold fbits
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp [fam]

end LinkProof

section Controls

/-- The Boolean point of `b` (`n` coordinates). -/
def cubeN (n b : ℕ) : Fin n → F := fun l => if b.testBit l then 1 else 0

theorem eqAtR_cubeN {n b x : ℕ} (hb : b < 2 ^ n) (hx : x < 2 ^ n) :
    eqAtR (cubeN n b) x = if x = b then 1 else 0 := by
  have h := eq_cube_cube (R := F) (⟨b, hb⟩ : Fin (2 ^ n)) ⟨x, hx⟩
  rw [eq_cube] at h
  refine h.trans ?_
  simp only [Fin.mk.injEq, eq_comm]

/-- The node's target bit as a Boolean (`nodeE = bF ∘ nodeBit`). -/
def nodeBit (blk p : ℕ) : Bool :=
  match nodeTgt blk with
  | some tgt => tgt (ProductCircuit.pos p) == some true
  | none => false

theorem nodeE_bit (blk p : ℕ) : nodeE blk p = bF (nodeBit blk p) := by
  unfold nodeE nodeBit tgtE; split <;> rfl

theorem slotWL_cube {pos : ℕ → ℕ} {L s₀ q : ℕ} (hs : s₀ < L) (hL : L ≤ 2 ^ 10)
    (hpos : ∀ s < L, pos s < 2 ^ 10) (hq : q < 2 ^ 10) :
    slotWL pos L (cubeN 10 s₀) (cubeN 10 q) = if pos s₀ = q then 1 else 0 := by
  unfold slotWL
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_range.2 hs) fun x hx hne => by
    rw [eqAtR_cubeN (by omega) (by have := Finset.mem_range.1 hx; omega), if_neg hne, zero_mul]]
  rw [eqAtR_cubeN (by omega) (by omega), if_pos rfl, one_mul, eqAtR_cubeN hq (hpos s₀ hs)]

end Controls

end NodeT

end FR

end

/-! ## From `FRVerifierImplNode` (64 declarations) -/

section

namespace FR

namespace NodeI

open Finset NodeT Impl

/-- The low `a` coordinates of a point. -/
def loP {a b : ℕ} (r : Fin (a + b) → F) : Fin a → F := fun l => r (Fin.castAdd b l)

/-- The high `b` coordinates of a point. -/
def hiP {a b : ℕ} (r : Fin (a + b) → F) : Fin b → F := fun l => r (Fin.natAdd a l)

theorem eqAtR_split {a b : ℕ} (r : Fin (a + b) → F) (x : ℕ) :
    eqAtR r x = eqAtR (loP r) (x % 2 ^ a) * eqAtR (hiP r) (x / 2 ^ a % 2 ^ b) := by
  unfold eqAtR loP hiP
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun l _ => by simp [Nat.testBit_mod_two_pow, l.isLt]
  · exact Finset.prod_congr rfl fun l _ => by
      simp [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, l.isLt, add_comm]

/-- Prefix sums `0, g 0, g 0 + g 1, …` (`k + 1` entries) and the total. -/
def pfxAux (g : ℕ → F) : ℕ → Array F × F
  | 0 => (#[0], 0)
  | k + 1 => let p := pfxAux g k; (p.1.push (p.2 + g k), p.2 + g k)

/-- The 257 prefix sums of `g` on `0 … 255`. -/
def pfx (g : ℕ → F) : Array F := (pfxAux g 256).1

theorem pfxAux_eq (g : ℕ → F) (k : ℕ) :
    pfxAux g k = (Array.ofFn (n := k + 1) fun i => ∑ l ∈ range i, g l, ∑ l ∈ range k, g l) := by
  induction k with
  | zero =>
    refine Prod.ext ?_ rfl
    rw [Array.ofFn_succ, Array.ofFn_zero]
    rfl
  | succ k ih =>
    rw [pfxAux, ih]
    simp only [Finset.sum_range_succ]
    refine Prod.ext ?_ rfl
    rw [Array.ofFn_succ (n := k + 1)]
    simp [Finset.sum_range_succ]

theorem pfx_getD (g : ℕ → F) {i : ℕ} (hi : i ≤ 256) : (pfx g).getD i 0 = ∑ l ∈ range i, g l := by
  simp [pfx, pfxAux_eq, Array.getD_eq_getD_getElem?, Nat.lt_succ_of_le hi]

/-- `Σ_{x<X} R(⌊x/256⌋) C(x mod 256)` from the prefix arrays `PR`, `PC`. -/
def twoF (PR : Array F) (R : ℕ → F) (PC : Array F) (X : ℕ) : F :=
  PR.getD (X / 256) 0 * PC.getD 256 0 + R (X / 256) * PC.getD (X % 256) 0

theorem twoF_eq (R C : ℕ → F) {X : ℕ} (hX : X ≤ 2 ^ 16) :
    twoF (pfx R) R (pfx C) X = ∑ x ∈ range X, R (x / 256) * C (x % 256) := by
  have hh : X / 256 ≤ 256 := by omega
  have hl : X % 256 ≤ 256 := by omega
  unfold twoF
  rw [pfx_getD _ hh, pfx_getD _ le_rfl, pfx_getD _ hl]
  conv_rhs => rw [← Nat.div_add_mod X 256, Finset.sum_range_add, mul_comm 256, sum_range_mul]
  rw [Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (h * 256 + k) / 256 = h by omega, show (h * 256 + k) % 256 = k by omega]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.1 hk
    rw [show (X / 256 * 256 + k) / 256 = X / 256 by omega,
      show (X / 256 * 256 + k) % 256 = k by omega]

/-- **A separable weight over a block range**: `Σ_{k<n} R(⌊(lo+k)/256⌋) C((lo+k) mod 256)`. -/
def sepSum (PR : Array F) (R : ℕ → F) (PC : Array F) (lo n : ℕ) : F :=
  twoF PR R PC (lo + n) - twoF PR R PC lo

theorem sepSum_eq (R C : ℕ → F) {lo n : ℕ} (h : lo + n ≤ 2 ^ 16) :
    sepSum (pfx R) R (pfx C) lo n = ∑ k ∈ range n, R ((lo + k) / 256) * C ((lo + k) % 256) := by
  rw [sepSum, twoF_eq R C h, twoF_eq R C (by omega), Finset.sum_range_add, add_sub_cancel_left]

/-- The block point's two-level tables `A` (low 8 coordinates), `B` (high 8) and their prefix
arrays. -/
structure Tabs where
  A : Array F
  B : Array F
  PA : Array F
  PB : Array F

/-- `A[l]`. -/
def Tabs.a (T : Tabs) (l : ℕ) : F := T.A.getD l 0

/-- `B[h]`. -/
def Tabs.b (T : Tabs) (h : ℕ) : F := T.B.getD h 0

/-- The low and high 8 block coordinates. -/
def lo8 (rb : Fin 16 → F) : Fin 8 → F := fun l => rb ⟨l, by omega⟩

def hi8 (rb : Fin 16 → F) : Fin 8 → F := fun l => rb ⟨8 + l, by omega⟩

/-- The tables of a 16-coordinate point (510 products). -/
def tabs (rb : Fin 16 → F) : Tabs :=
  let A := eqTable (List.ofFn (lo8 rb))
  let B := eqTable (List.ofFn (hi8 rb))
  ⟨A, B, pfx fun l => A.getD l 0, pfx fun h => B.getD h 0⟩

/-- `eq(r_blk, x)` from the tables (one product). -/
def eqbI (T : Tabs) (x : ℕ) : F := T.a (x % 256) * T.b (x / 256 % 256)

/-- `Σ_{k<n} eq(r_blk, lo + k)` (four products). -/
def rangeI (T : Tabs) (lo n : ℕ) : F := sepSum T.PB T.b T.PA lo n

section TabsLemmas

variable (rb : Fin 16 → F)

theorem tabs_A : (tabs rb).A = eqTable (List.ofFn (lo8 rb)) := by dsimp only [tabs]

theorem tabs_B : (tabs rb).B = eqTable (List.ofFn (hi8 rb)) := by dsimp only [tabs]

theorem tabs_a {l : ℕ} (hl : l < 2 ^ 8) : (tabs rb).a l = eqAtR (lo8 rb) l := by
  rw [Tabs.a, tabs_A]; exact eqTable_ofFn_getD _ hl

theorem tabs_b {h : ℕ} (hh : h < 2 ^ 8) : (tabs rb).b h = eqAtR (hi8 rb) h := by
  rw [Tabs.b, tabs_B]; exact eqTable_ofFn_getD _ hh

theorem eqAtR16 (x : ℕ) : eqAtR rb x = eqAtR (lo8 rb) (x % 256) * eqAtR (hi8 rb) (x / 256 % 256) :=
  eqAtR_split (a := 8) (b := 8) rb x

theorem eqbI_eq (x : ℕ) : eqbI (tabs rb) x = eqAtR rb x := by
  rw [eqbI, tabs_a rb (l := x % 256) (by omega), tabs_b rb (h := x / 256 % 256) (by omega),
    eqAtR16]

theorem ba_eq {x : ℕ} (hx : x < 2 ^ 16) :
    (tabs rb).b (x / 256) * (tabs rb).a (x % 256) = eqAtR rb x := by
  rw [← eqbI_eq, eqbI, Nat.mod_eq_of_lt (show x / 256 < 256 by omega), mul_comm]

theorem tabs_PA : (tabs rb).PA = pfx fun l => (tabs rb).a l := by dsimp only [tabs, Tabs.a]

theorem tabs_PB : (tabs rb).PB = pfx fun h => (tabs rb).b h := by dsimp only [tabs, Tabs.b]

theorem rangeI_eq {lo n : ℕ} (h : lo + n ≤ 2 ^ 16) :
    rangeI (tabs rb) lo n = ∑ k ∈ range n, eqAtR rb (lo + k) := by
  rw [rangeI, tabs_PA, tabs_PB, sepSum_eq _ _ h]
  exact Finset.sum_congr rfl fun k hk => ba_eq rb (by have := Finset.mem_range.1 hk; omega)

end TabsLemmas

/-- **The counter bits of a stream body** `Σ_{k<n} eq(r_blk, lo + k) · bit_j(k + 2)`: with
`k + 2 = (lo + k) + e − 256 Q`, bit `j < 8` depends on the column `(lo + k) mod 256` only, bit
`j ≥ 8` on the row and the column's carry; `0` once `2^j > n + 1`. -/
def ctrI (T : Tabs) (lo n j : ℕ) : F :=
  if n + 1 < 2 ^ j then 0 else
  let Q := (lo + 253) / 256
  let e := 256 * Q + 2 - lo
  let d := e % 256
  if j < 8 then
    let C := fun l => if ((l + d) % 256).testBit j then T.a l else 0
    sepSum T.PB T.b (pfx C) lo n
  else
    let C0 := fun l => if l + d < 256 then T.a l else 0
    let C1 := fun l => if l + d < 256 then 0 else T.a l
    let R0 := fun h => if (h + e / 256 - Q).testBit (j - 8) then T.b h else 0
    let R1 := fun h => if (h + e / 256 + 1 - Q).testBit (j - 8) then T.b h else 0
    sepSum (pfx R0) R0 (pfx C0) lo n + sepSum (pfx R1) R1 (pfx C1) lo n

theorem ctrI_eq (rb : Fin 16 → F) {lo n : ℕ} (h : lo + n ≤ 2 ^ 16) (j : ℕ) :
    ctrI (tabs rb) lo n j = ∑ k ∈ range n, eqAtR rb (lo + k) * bF ((k + 2).testBit j) := by
  unfold ctrI
  split_ifs with hj hj8
  · refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have := Finset.mem_range.1 hk
    rw [Nat.testBit_lt_two_pow (by omega)]
    simp [bF]
  · rw [tabs_PB, sepSum_eq _ _ h]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hb : (k + 2).testBit j = (((lo + k) % 256 + (256 * ((lo + 253) / 256) + 2 - lo) % 256)
        % 256).testBit j := by
      rw [show ((lo + k) % 256 + (256 * ((lo + 253) / 256) + 2 - lo) % 256) % 256 =
        (k + 2) % 2 ^ 8 by omega, Nat.testBit_mod_two_pow]
      simp [hj8]
    rw [hb, ← ba_eq rb (show lo + k < 2 ^ 16 by omega)]
    unfold bF
    split_ifs <;> ring
  · dsimp only
    rw [sepSum_eq _ _ h, sepSum_eq _ _ h, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [← ba_eq rb (show lo + k < 2 ^ 16 by omega)]
    have hb : (k + 2).testBit j = ((k + 2) / 2 ^ 8).testBit (j - 8) := by
      rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
    by_cases hc : (lo + k) % 256 + (256 * ((lo + 253) / 256) + 2 - lo) % 256 < 256
    · rw [hb, show (k + 2) / 2 ^ 8 = (lo + k) / 256 + (256 * ((lo + 253) / 256) + 2 - lo) / 256 -
        (lo + 253) / 256 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, add_zero]
      unfold bF
      split_ifs <;> ring
    · rw [hb, show (k + 2) / 2 ^ 8 = (lo + k) / 256 + (256 * ((lo + 253) / 256) + 2 - lo) / 256 +
        1 - (lo + 253) / 256 by omega]
      simp only [hc, ite_true, ite_false, mul_zero, zero_add]
      unfold bF
      split_ifs <;> ring

/-- The ten classes' pinned bits at the positions `0 … 1152` (computed once). -/
def clsTab : Array (Array Bool) :=
  Array.ofFn (n := 10) fun c => Array.ofFn (n := 1153) fun p =>
    cls c (ProductCircuit.pos p) == some true

/-- Class `c`'s bit at `p`. -/
def clsBit (c p : ℕ) : Bool := (clsTab.getD c #[]).getD p false

theorem clsBit_eq {c p : ℕ} (hc : c < 10) (hp : p < 1153) (w : F) :
    (if clsBit c p then w else 0) = w * tgtE (cls c) p := by
  have : clsBit c p = (cls c (ProductCircuit.pos p) == some true) := by
    simp [clsBit, clsTab, Array.getD_eq_getD_getElem?, hc, hp]
  rw [this, tgtE, bF]
  split_ifs <;> simp

/-- The ten class weights (A.8: range sums and single blocks of `eq(r_blk, ·)`). -/
structure Wts where
  w0 : F
  w1 : F
  w2 : F
  w3 : F
  w4 : F
  w5 : F
  w6 : F
  w7 : F
  w8 : F
  w9 : F

/-- The class weights from the tables: `streamStart`, the stream bodies (both chains, both key
leaves), the chains' last blocks, `hashA`, `hashB1 tagNode`, `hashB2` (statement and path),
`w43`, `hashB1 tagWotsLeaf`, `streamEnd41`, `hashB1 tagSigNode`. -/
def wts (T : Tabs) : Wts :=
  let N := Layout.chainN
  ⟨sumTo 2 fun σ => eqbI T (σ * N),
   (sumTo 2 fun σ => rangeI T (σ * N + 1) (N - 2)) + sumTo 2 fun σ => rangeI T (wb σ + 400) 65,
   sumTo 2 fun σ => eqbI T (σ * N + (N - 1)),
   sumTo 2 fun σ => eqbI T (Layout.stmtBase + 3 * σ),
   sumTo 2 fun σ => eqbI T (Layout.stmtBase + 3 * σ + 1),
   (sumTo 2 fun σ => eqbI T (Layout.stmtBase + 3 * σ + 2)) +
     sumTo 2 fun σ => sumTo 16 fun t => eqbI T (wb σ + 467 + 2 * t),
   sumTo 2 fun σ => rangeI T (wb σ) 399,
   sumTo 2 fun σ => eqbI T (wb σ + 399),
   sumTo 2 fun σ => eqbI T (wb σ + 465),
   sumTo 2 fun σ => sumTo 16 fun t => eqbI T (wb σ + 466 + 2 * t)⟩

/-- `eq(r_blk, wb σ + o)` for the 399 `w43` blocks (399 products). -/
def e43 (T : Tabs) (σ : ℕ) : Array F := Array.ofFn (n := 399) fun o => eqbI T (wb σ + o)

/-- `Σ_{o<399} eq(r_blk, wb σ + o) · bit_b(sel o)` from `e43` (additions only). -/
def w43I (E : Array F) (sel : ℕ → ℕ) (b : ℕ) : F :=
  sumTo 399 fun o => if (sel o).testBit b then E.getD o 0 else 0

/-- `G(p)` from the class weights, the counter bits `CT`, and `w43`'s `i`, `s` bits. -/
def gAt (W : Wts) (CT WI WS : Array F) (p : ℕ) : F :=
  ((if clsBit 0 p then W.w0 else 0) + (if clsBit 1 p then W.w1 else 0) +
    (if clsBit 2 p then W.w2 else 0) + (if clsBit 3 p then W.w3 else 0) +
    (if clsBit 4 p then W.w4 else 0) + (if clsBit 5 p then W.w5 else 0) +
    (if clsBit 6 p then W.w6 else 0) + (if clsBit 7 p then W.w7 else 0) +
    (if clsBit 8 p then W.w8 else 0) + (if clsBit 9 p then W.w9 else 0)) +
  (if 1030 ≤ p ∧ p < 1056 then CT.getD (p - 1030) 0 else 0) +
  (if 584 ≤ p ∧ p < 592 then WI.getD (p - 584) 0 else 0) +
  (if 592 ≤ p ∧ p < 600 then WS.getD (p - 592) 0 else 0)

/-- **`G` at the 1,153 pinned positions** (the rest is `0`). -/
def gArr (T : Tabs) : Array F :=
  let N := Layout.chainN
  let W := wts T
  let CT := Array.ofFn (n := 26) fun j =>
    (sumTo 2 fun σ => ctrI T (σ * N + 1) (N - 2) j) + sumTo 2 fun σ => ctrI T (wb σ + 400) 65 j
  let E0 := e43 T 0
  let E1 := e43 T 1
  let WI := Array.ofFn (n := 8) fun b => w43I E0 (· / 3) b + w43I E1 (· / 3) b
  let WS := Array.ofFn (n := 8) fun b => w43I E0 (· % 3) b + w43I E1 (· % 3) b
  Array.ofFn (n := 1153) fun p => gAt W CT WI WS p

/-- **`targetS` of a node** (A.8, revision 3.13), computed: `Σ_{hi<19} eq(r_lo, hi) G(σ + 64 hi)`. -/
def targetSNodeI (r : Array F) : Array F :=
  let G := gArr (tabs (rbOf r))
  let H := eqTable (List.ofFn (zLo r))
  Array.ofFn (n := 64) fun σ => sumTo 19 fun hi => H.getD hi 0 * G.getD (σ + 64 * hi) 0

section Meets

variable (rb : Fin 16 → F)

theorem w43I_eq (σ : ℕ) (sel : ℕ → ℕ) (b : ℕ) :
    w43I (e43 (tabs rb) σ) sel b = ∑ o ∈ range 399, eqAtR rb (wb σ + o) * bF ((sel o).testBit b) := by
  rw [w43I, sumTo_eq]
  refine Finset.sum_congr rfl fun o ho => ?_
  have := Finset.mem_range.1 ho
  rw [e43, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos this, Option.getD_some,
    eqbI_eq, bF]
  split_ifs <;> simp

private theorem sum_two (g : ℕ → F) : ∑ σ ∈ range 2, g σ = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

theorem gAt_eq {p : ℕ} (hp : p < 1153) :
    (gArr (tabs rb)).getD p 0 = Gc rb p := by
  have hN : Layout.chainN = 23146 := rfl
  have hw : ∀ σ, wb σ = 46298 + 498 * σ := fun _ => rfl
  simp only [gArr]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hp, Option.getD_some]
  unfold gAt
  rw [clsBit_eq (c := 0) (by norm_num) hp, clsBit_eq (c := 1) (by norm_num) hp,
    clsBit_eq (c := 2) (by norm_num) hp, clsBit_eq (c := 3) (by norm_num) hp,
    clsBit_eq (c := 4) (by norm_num) hp, clsBit_eq (c := 5) (by norm_num) hp,
    clsBit_eq (c := 6) (by norm_num) hp, clsBit_eq (c := 7) (by norm_num) hp,
    clsBit_eq (c := 8) (by norm_num) hp, clsBit_eq (c := 9) (by norm_num) hp]
  simp only [wts, sumTo_eq, eqbI_eq, sum_two]
  rw [rangeI_eq rb (lo := 0 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
    rangeI_eq rb (lo := 1 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
    rangeI_eq rb (lo := wb 0 + 400) (n := 65) (by rw [hw]; norm_num),
    rangeI_eq rb (lo := wb 1 + 400) (n := 65) (by rw [hw]; norm_num),
    rangeI_eq rb (lo := wb 0) (n := 399) (by rw [hw]; norm_num),
    rangeI_eq rb (lo := wb 1) (n := 399) (by rw [hw]; norm_num)]
  unfold Gc chainC stmtC wotsC w43C ctrC
  simp only [sum_two]
  by_cases h1 : 1030 ≤ p ∧ p < 1056
  · have h1' : p - 1030 < 26 := by omega
    have h2 : ¬ (584 ≤ p ∧ p < 592) := by omega
    have h3 : ¬ (592 ≤ p ∧ p < 600) := by omega
    simp only [h1, h2, h3, and_self, ite_true, ite_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      dif_pos h1', Option.getD_some, add_zero]
    rw [ctrI_eq rb (lo := 0 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
      ctrI_eq rb (lo := 1 * Layout.chainN + 1) (n := Layout.chainN - 2) (by rw [hN]; norm_num),
      ctrI_eq rb (lo := wb 0 + 400) (n := 65) (by rw [hw]; norm_num),
      ctrI_eq rb (lo := wb 1 + 400) (n := 65) (by rw [hw]; norm_num)]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  by_cases h2 : 584 ≤ p ∧ p < 592
  · have h2' : p - 584 < 8 := by omega
    have h3 : ¬ (592 ≤ p ∧ p < 600) := by omega
    simp only [h1, h2, h3, and_self, ite_true, ite_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      dif_pos h2', Option.getD_some, add_zero, w43I_eq]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  by_cases h3 : 592 ≤ p ∧ p < 600
  · have h3' : p - 592 < 8 := by omega
    simp only [h1, h2, h3, and_self, ite_true, ite_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      dif_pos h3', Option.getD_some, add_zero, w43I_eq]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  simp only [h1, h2, h3, ite_false, add_zero]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- **`targetS` meets the node's specification.** -/
theorem targetSNode_meets (r : Array F) : targetSNodeI r = targetSNodeS r := by
  rw [targetS_node_eq]
  unfold targetSNodeI
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  have hσ := σ.isLt
  rw [sumTo_eq, show (256 : ℕ) = 19 + 237 from rfl, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range 237) fun x hx => by
      rw [Gc_hi _ (by omega) (by have := Finset.mem_range.1 hx; omega), mul_zero], add_zero]
  refine Finset.sum_congr rfl fun hi hh => ?_
  have hh' := Finset.mem_range.1 hh
  rw [eqTable_ofFn_getD _ (show hi < 2 ^ 8 by omega)]
  refine congrArg (eqAtR (zLo r) hi * ·) ?_
  by_cases hq : σ.val + 64 * hi < 1153
  · exact gAt_eq _ hq
  · rw [Gc_hi _ (by omega) (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simp only [gArr, Array.size_ofFn]; omega)]
    rfl

end Meets

/-- The two `eq` tables of a 16-coordinate point without prefix arrays (`eqbI` only). -/
def tabsE (rb : Fin 16 → F) : Tabs :=
  ⟨eqTable (List.ofFn (lo8 rb)), eqTable (List.ofFn (hi8 rb)), #[], #[]⟩

theorem eqbI_eqE (rb : Fin 16 → F) (x : ℕ) : eqbI (tabsE rb) x = eqAtR rb x := by
  rw [eqbI, Tabs.a, Tabs.b, show (tabsE rb).A = eqTable (List.ofFn (lo8 rb)) by dsimp only [tabsE],
    show (tabsE rb).B = eqTable (List.ofFn (hi8 rb)) by dsimp only [tabsE],
    eqTable_ofFn_getD _ (show x % 256 < 2 ^ 8 by omega),
    eqTable_ofFn_getD _ (show x / 256 % 256 < 2 ^ 8 by omega), eqAtR16]

/-- A 10-coordinate point's two tables (low 8 coordinates, high 2). -/
def tab10 (r : Fin 10 → F) : Array F × Array F :=
  (eqTable (List.ofFn (loP (a := 8) (b := 2) r)), eqTable (List.ofFn (hiP (a := 8) (b := 2) r)))

/-- `eq(r, q)` from the tables (one product). -/
def eq10 (P : Array F × Array F) (q : ℕ) : F := P.1.getD (q % 256) 0 * P.2.getD (q / 256 % 4) 0

theorem eq10_eq (r : Fin 10 → F) (q : ℕ) : eq10 (tab10 r) q = eqAtR r q := by
  rw [eq10, show (tab10 r).1 = eqTable (List.ofFn (loP (a := 8) (b := 2) r)) by dsimp only [tab10],
    show (tab10 r).2 = eqTable (List.ofFn (hiP (a := 8) (b := 2) r)) by dsimp only [tab10],
    eqTable_ofFn_getD _ (show q % 256 < 2 ^ 8 by omega),
    eqTable_ofFn_getD _ (show q / 256 % 4 < 2 ^ 2 by omega)]
  exact (eqAtR_split (a := 8) (b := 2) r q).symm

/-- Family `f`'s weight from the tables: per source `eq(τ, src)·(eq(r_blk, src)·SW −
eq(r_blk, mirBlk)·MS[mir mod 4])`, `SW` the field's slot weight, `MS[c]` the mirror's for the
mirror slot `c` (`MS[c] = eq(r_pos,hi, c) · Σ_s eq(θ, s) eq(r_pos,lo, mbo + s)`). -/
def linkWOne (Tτ Tr : Tabs) (Pr : Array F × Array F) (Eθ : Array F) (f : ℕ) : F :=
  let L := fbits f
  let SW := sumTo L fun s => Eθ.getD s 0 * eq10 Pr (fpos f s)
  let MI := sumTo L fun s => Eθ.getD s 0 * Pr.1.getD ((fam f).mbo + s) 0
  let MS := Array.ofFn (n := 4) fun c => Pr.2.getD c 0 * MI
  sumTo 2 fun σ => sumTo (fam f).n fun t =>
    eqbI Tτ (srcB σ f t) * (eqbI Tr (srcB σ f t) * SW -
      eqbI Tr (mirB σ f t) * MS.getD ((fam f).mir t % 4) 0)

/-- The tables of `linkW`'s four points. -/
def linkTabs (τ θ rb rp : Array F) : Tabs × Tabs × (Array F × Array F) × Array F :=
  let Pθ := tab10 (ptA 10 θ)
  (tabsE (ptA 16 τ), tabsE (ptA 16 rb), tab10 (ptA 10 rp),
    Array.ofFn (n := 256) fun s => eq10 Pθ s)

/-- All eight families at once (the tables shared). -/
def linkWAllI (τ θ rb rp : Array F) : Array F :=
  let T := linkTabs τ θ rb rp
  Array.ofFn (n := nLinkFam) fun f => linkWOne T.1 T.2.1 T.2.2.1 T.2.2.2 f

section LinkMeets

theorem mbo_le (f : ℕ) : (fam f).mbo + fbits f ≤ 256 := by
  unfold fbits
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp [fam]

theorem linkWOne_eq (f : ℕ) (τ rb : Fin 16 → F) (θ' rp' : Fin 10 → F) :
    linkWOne (tabsE τ) (tabsE rb) (tab10 rp')
      (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s) f = linkWS f τ θ' rb rp' := by
  have hE : ∀ s < fbits f, (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s).getD s 0 =
      eqAtR θ' s := fun s hs => by
    have : s < 256 := by have := mbo_le f; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos this, Option.getD_some, eq10_eq]
  have hSW : (sumTo (fbits f) fun s => (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s).getD s 0 *
      eq10 (tab10 rp') (fpos f s)) = slotWL (fpos f) (fbits f) θ' rp' := by
    rw [sumTo_eq, slotWL]
    exact Finset.sum_congr rfl fun s hs => by rw [hE s (Finset.mem_range.1 hs), eq10_eq]
  have hMS : ∀ t, ((Array.ofFn (n := 4) fun c => (tab10 rp').2.getD c 0 *
      sumTo (fbits f) fun s => (Array.ofFn (n := 256) fun s => eq10 (tab10 θ') s).getD s 0 *
        (tab10 rp').1.getD ((fam f).mbo + s) 0).getD ((fam f).mir t % 4) 0) =
      slotWL (mpos f t) (fbits f) θ' rp' := fun t => by
    have hc : (fam f).mir t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hc, Option.getD_some, sumTo_eq,
      Finset.mul_sum, slotWL]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    have hb := mbo_le f
    rw [hE s hs', mpos, ← eq10_eq rp', eq10,
      show (256 * ((fam f).mir t % 4) + (fam f).mbo + s) % 256 = (fam f).mbo + s by omega,
      show (256 * ((fam f).mir t % 4) + (fam f).mbo + s) / 256 % 4 = (fam f).mir t % 4 by omega,
      Fin.val_mk]
    ring
  unfold linkWOne linkWS
  dsimp only
  rw [hSW]
  simp only [hMS]
  simp only [sumTo_eq, eqbI_eqE]

theorem ptA_extract (a : Array F) {o s n : ℕ} (hs : s = o + n) :
    ptA n (a.extract o s) = fun l : Fin n => a.getD (o + l.1) 0 := by
  funext l
  subst hs
  simp only [ptA, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : o + l.1 < a.size
  · rw [if_pos (by omega)]
  · rw [Array.getElem?_eq_none (by omega)]
    split_ifs <;> simp

/-- **`linkWAll` meets `linkWAllS`** on the packed points (`implC`'s split of `τ ‖ θ`,
`r_blk ‖ r_pos`; `linkWOne_eq`, as `linkWAll_meets` per family). -/
theorem linkWAll_eqS (tt rr : Array F) :
    linkWAllI (tt.extract 0 16) (tt.extract 16 26) (rr.extract 0 16) (rr.extract 16 26) =
      linkWAllS tt rr := by
  unfold linkWAllI linkTabs linkWAllS
  dsimp only
  rw [ptA_extract tt (o := 0) (n := 16) rfl, ptA_extract tt (o := 16) (n := 10) rfl,
    ptA_extract rr (o := 0) (n := 16) rfl, ptA_extract rr (o := 16) (n := 10) rfl]
  congr 1
  funext f
  rw [linkWOne_eq]
  simp only [zero_add]
  rfl

end LinkMeets

/-- **`shiftMask`, computed**: the product tables of `τ` and `r` (`tabs`), the separable range sums
over the two chains' link blocks (`sepSum`); the shifted weight splits at the low byte's carry
(`l < 255`: `C₁`; `l = 255`: `R₂ C₂`, the high byte stepping). -/
def shiftMaskI (τ r : Array F) : F × F × F :=
  let Tt := tabs (ptA 16 τ); let Tr := tabs (ptA 16 r)
  let R : ℕ → F := fun h => Tt.b h * Tr.b h
  let R2 : ℕ → F := fun h => Tt.b h * Tr.b (h + 1)
  let C : ℕ → F := fun l => Tt.a l * Tr.a l
  let C1 : ℕ → F := fun l => Tt.a l * Tr.a (l + 1)
  let C2 : ℕ → F := fun l => if l = 255 then Tt.a 255 * Tr.a 0 else 0
  let PR := pfx R; let PR2 := pfx R2; let PC := pfx C; let PC1 := pfx C1; let PC2 := pfx C2
  let N := Layout.chainN
  (sepSum PR R PC 0 (N - 1) + sepSum PR R PC N (N - 1),
   sepSum PR R PC1 0 (N - 1) + sepSum PR R PC1 N (N - 1) +
     (sepSum PR2 R2 PC2 0 (N - 1) + sepSum PR2 R2 PC2 N (N - 1)),
   eqbI Tr 0 + eqbI Tr N)

section MaskMeets

theorem tabs_a256 (rb : Fin 16 → F) : (tabs rb).a 256 = 0 := by
  rw [Tabs.a, tabs_A, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
    rw [eqTable_size, List.length_ofFn]; norm_num)]
  rfl

theorem mask_eq (τ r : Fin 16 → F) {y : ℕ} (hy : y < 2 ^ 16) :
    eqAtR τ y * eqAtR r y =
      (tabs τ).b (y / 256) * (tabs r).b (y / 256) * ((tabs τ).a (y % 256) * (tabs r).a (y % 256)) := by
  rw [← ba_eq τ hy, ← ba_eq r hy]; ring

theorem mask_succ_eq (τ r : Fin 16 → F) {y : ℕ} (hy : y + 256 < 2 ^ 16) :
    eqAtR τ y * eqAtR r (y + 1) =
      (tabs τ).b (y / 256) * (tabs r).b (y / 256) * ((tabs τ).a (y % 256) * (tabs r).a (y % 256 + 1)) +
      (tabs τ).b (y / 256) * (tabs r).b (y / 256 + 1) *
        (if y % 256 = 255 then (tabs τ).a 255 * (tabs r).a 0 else 0) := by
  rw [← ba_eq τ (by omega), ← ba_eq r (by omega)]
  by_cases hl : y % 256 = 255
  · rw [if_pos hl, hl, tabs_a256, show (y + 1) / 256 = y / 256 + 1 by omega,
      show (y + 1) % 256 = 0 by omega]
    ring
  · rw [if_neg hl, show (y + 1) / 256 = y / 256 by omega, show (y + 1) % 256 = y % 256 + 1 by omega]
    ring

private theorem sum2 (g : ℕ → F) : ∑ c ∈ range 2, g c = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

/-- **`shiftMask` meets its specification.** -/
theorem shiftMask_meets (τ r : Array F) : shiftMaskI τ r = shiftMaskS τ r := by
  have hN : 2 * Layout.chainN + 256 < 2 ^ 16 := by simp only [Layout.chainN]; norm_num
  unfold shiftMaskI shiftMaskS
  generalize Layout.chainN = N at hN ⊢
  have hs : ∀ (lo : ℕ) (R C : ℕ → F), lo ≤ N →
      sepSum (pfx R) R (pfx C) lo (N - 1) =
        ∑ k ∈ range (N - 1), R ((lo + k) / 256) * C ((lo + k) % 256) :=
    fun lo R C h => sepSum_eq R C (by omega)
  have hb : ∀ k ∈ range (N - 1), N + k + 256 < 2 ^ 16 := fun k hk => by
    have := Finset.mem_range.1 hk; omega
  dsimp only
  rw [hs 0 _ _ (Nat.zero_le _), hs 0 _ _ (Nat.zero_le _), hs 0 _ _ (Nat.zero_le _),
    hs _ _ _ le_rfl, hs _ _ _ le_rfl, hs _ _ _ le_rfl, eqbI_eq, eqbI_eq, sum2, sum2]
  simp only [zero_mul, one_mul, zero_add]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · dsimp only
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k hk => ?_) (Finset.sum_congr rfl fun k hk => ?_)
    · exact (mask_eq (ptA 16 τ) (ptA 16 r) (by have := hb k hk; omega)).symm
    · exact (mask_eq (ptA 16 τ) (ptA 16 r) (by have := hb k hk; omega)).symm
  · dsimp only
    rw [add_add_add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k hk => ?_) (Finset.sum_congr rfl fun k hk => ?_)
    · exact (mask_succ_eq (ptA 16 τ) (ptA 16 r) (by have := hb k hk; omega)).symm
    · exact (mask_succ_eq (ptA 16 τ) (ptA 16 r) (hb k hk)).symm

end MaskMeets

section Controls

theorem ptA_ofFn {n : ℕ} (g : Fin n → F) : ptA n (Array.ofFn g) = g := by
  funext l; simp [ptA, Array.getD_eq_getD_getElem?]

end Controls

end NodeI

end FR

end
