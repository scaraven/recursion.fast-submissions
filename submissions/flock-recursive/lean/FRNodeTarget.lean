-- New for `flock-recursive` (BLUEPRINT revision 3.13: A.8 `targetS` and `linkW` node forms, A.6
-- `WM`, §4.2 link families; stage-review changes 20, gap 3; track S-CN, the S-C part).
import FRVerifierImplOps
import FRNodeLayout
import FRBlockKinds

/-!
# The node's public target on the skip set (`targetSNodeS`) and its link weights (`linkWS`)

**`targetS` of a node** (A.8, revision 3.13). The zerocheck's Z2 rebuilds `P^e(σ) = Σ_{x′} eq(r,
x′) E(x′, σ)` from the public target `E`. A node's `E` is block-dependent: **`nodeTgt blk`** is the
public target of node block `blk` (A.6 per region: the two digest chains, `hashStmt`'s A/B1/B2, the
WOTS runs with the key leaf and the path; `none` for the `free` blocks). It is S-G's
`Snd.nodeKind` (`FRSoundnessPIOP`) verbatim; this module does not import the soundness modules.
**`targetSNodeS`** is `FRPubTarget.targetS` with that `E` on the `8 + 16` variables of the quirky
point (the leaf's convention, `targetSLeafS`).

* **`targetSNode_blk`**: `P^e(σ) = Σ_hi eq(r_lo, hi) · G(σ + 64 hi)` with the block sum
  `G(p) = Σ_blk eq(r_blk, blk) · E(blk, p)` (`blkW`).
* **`targetS_node_eq`**: `G` in closed form (`Gc`): per region, the constant bits of a kind times a
  range sum of `eq(r_blk, ·)` (`streamStart`, the stream body with its counter removed, a chain's
  last block, `hashA`, `hashB1` with its three tags, `hashB2`, `w43` with `i`, `s` removed,
  `streamEnd41`); the stream counter `t_lo = 64 (k + 1)` as the bits of `k + 1` against `eq(r_blk,
  ·)` over the body (`tgtE_ctr`); `w43`'s `i = ⌊o/3⌋`, `s = o mod 3` as a 399-term sum
  (`tgtE_w43`).

**`linkW` of a node** (A.8, §4.2). Per slot, the link families tie an unaligned message field of a
source block to its aligned mirror cell in `WM`. A family (`Fam`) has `n` sources at blocks
`wb_σ + src t`, the field `[off, off + len)` of the message, and the mirror source `mir t` of the
`WM` map. **`linkWS`** is A.8's closed form `Σ_σ Σ_t eq(τ, src)·[eq(r_blk, src)·slotW(field, r_pos)
− eq(r_blk, mirBlk)·slotW(mirPos, r_pos)]` with `slotW(base) = Σ_{s<8 len} eq(θ, s) eq(r_pos, base +
s)`; **`linkW_mle`**: it is the multilinear extension, at `(τ, θ, r_blk, r_pos)`, of the
source-minus-mirror indicator `linkInd`; **`linkInd_apply`**: against a table `z`, the indicator
gives `Σ_σ Σ_t eq(τ, src) Σ_s eq(θ, s) (z(src, field s) − z(mirBlk, mirPos s))`, the family's
residual.

**Deviations from the blueprint's text** (the RESULT's D-1 … D-3; the counterexamples are there):
* **8 families, not 7.** End `2u+1` of the key leaf sits at byte `41` of block `u` and is 32 bytes
  long, so it crosses into block `u + 1` (`41 + 32 = 73 > 64`): A.8's `end41` (offset 41, 32 B) is
  split into `end41lo` (block `u`, bytes 41–63) and `end41hi` (block `u + 1`, bytes 0–8, mirror
  bits 184–255), `u < 66` (end 133 does not exist). `nLinkFam = 8` already.
* **The mirror cells sit in elements 0–7 of their `WM` block.** Sh's claim reads elements 0–7 of a
  block only (`FRVIRFinalsSG.shSrc`: three element coordinates, then four zeros; §2 step 4: 10
  collapse rounds over the positions `< 1024`), so A.6's map `WMbase_σ·128 + 2(off_f + t) + p`
  (elements up to 127 of a block) puts most mirror cells where no link family can read them. Here
  mirror source `g` of slot `σ` is block `wmB σ + ⌊g/4⌋`, elements `2(g mod 4)` and `2(g mod 4)+1`
  (positions `256 (g mod 4) + [0, 256)`), `wmB σ = wmBase + 146 σ` (582 sources, 146 blocks per
  slot; A.6's `WMbase_σ = wotsBase_σ + 498` is slot 1's first WOTS block for `σ = 0`).
* `j`'s 400 sources are the 399 `w43` blocks and key-leaf block 0 (`src t = t`), one mirror.
-/

namespace FR
namespace NodeT
open Finset RecursionFast Impl Kinds Stream

/-! ## The node's public target -/

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

/-! ## The kinds' bits: counter and step fields split off -/

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

/-! ## The closed form of the block sum -/

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

/-! ## The link families (§4.2, A.8 `linkW`) -/

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
A.6's mirror offsets `x` 0, `end9` 399, `end41` 466, `l` 533, `r0` 549, `r31` 565, `j` 581. -/
def fam : ℕ → Fam
  | 0 => ⟨399, id, 11, 32, id, 0⟩
  | 1 => ⟨400, id, 1, 8, fun _ => 581, 0⟩
  | 2 => ⟨67, (399 + ·), 9, 32, (399 + ·), 0⟩
  | 3 => ⟨66, (399 + ·), 41, 23, (466 + ·), 0⟩
  | 4 => ⟨66, (400 + ·), 0, 9, (466 + ·), 184⟩
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

/-- **The source-minus-mirror indicator** of family `f`: at block point `u` (`τ`), field bit `s`
(`θ`), cell `(y, q)` (block, position): `1` at the source's field bit, `−1` at its mirror bit. -/
def linkInd (f u s y q : ℕ) : F :=
  ∑ σ ∈ range 2, ∑ t ∈ range (fam f).n,
    if u = srcB σ f t ∧ s < fbits f then
      (if y = srcB σ f t ∧ q = fpos f s then 1 else 0) -
        (if y = mirB σ f t ∧ q = mpos f t s then 1 else 0)
    else 0

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
    simp only [fam, id] at ht ⊢ <;> (try have := h4 t) <;> (try have := h4 (399 + t)) <;>
    (try have := h4 (466 + t)) <;> (try have := h4 (533 + t)) <;> (try have := h4 (549 + t)) <;>
    (try have := h4 (565 + t)) <;> omega

theorem fbits_le (f : ℕ) : fbits f ≤ 2 ^ 10 := by
  unfold fbits
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp [fam]

private theorem col {n a : ℕ} (h : a < n) (g : ℕ → F) :
    ∑ x ∈ range n, (if x = a then g x else 0) = g a := by
  rw [Finset.sum_ite_eq']; simp [h]

private theorem sum_lt {n L : ℕ} (h : L ≤ n) (g : ℕ → F) :
    ∑ x ∈ range n, (if x < L then g x else 0) = ∑ x ∈ range L, g x := by
  rw [← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_eq_zero (s := Ico L n) fun x hx => by simp [(Finset.mem_Ico.1 hx).1]]
  rw [add_zero]
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.mem_range.1 hx]

/-- Four nested sums and an inner one commute. -/
private theorem sum_pull {α : Type*} (S₁ S₂ S₃ S₄ : Finset ℕ) (T : Finset α)
    (g : ℕ → ℕ → ℕ → ℕ → α → F) :
    ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ q ∈ S₄, ∑ j ∈ T, g u s y q j =
      ∑ j ∈ T, ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ q ∈ S₄, g u s y q j := by
  calc _ = ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ j ∈ T, ∑ q ∈ S₄, g u s y q j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ S₁, ∑ s ∈ S₂, ∑ j ∈ T, ∑ y ∈ S₃, ∑ q ∈ S₄, g u s y q j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ S₁, ∑ j ∈ T, ∑ s ∈ S₂, ∑ y ∈ S₃, ∑ q ∈ S₄, g u s y q j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- One source's term of the indicator, summed against `A(u) B(s) Ψ(y, q)`. -/
private theorem one_source {a m L : ℕ} (fp mp : ℕ → ℕ) (ha : a < 2 ^ 16) (hm : m < 2 ^ 16)
    (hL : L ≤ 2 ^ 10) (hfp : ∀ s < L, fp s < 2 ^ 10) (hmp : ∀ s < L, mp s < 2 ^ 10)
    (A B : ℕ → F) (Ψ : ℕ → ℕ → F) :
    ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), ∑ q ∈ range (2 ^ 10),
      A u * B s * Ψ y q * (if u = a ∧ s < L then
        (if y = a ∧ q = fp s then 1 else 0) - (if y = m ∧ q = mp s then 1 else 0) else 0) =
    A a * ∑ s ∈ range L, B s * (Ψ a (fp s) - Ψ m (mp s)) := by
  have hpt : ∀ u s y q, A u * B s * Ψ y q * (if u = a ∧ s < L then
      (if y = a ∧ q = fp s then (1 : F) else 0) - (if y = m ∧ q = mp s then 1 else 0) else 0) =
      (if u = a then A u else 0) * ((if s < L then B s else 0) *
        ((if y = a then 1 else 0) * (if q = fp s then Ψ y q else 0) -
          (if y = m then 1 else 0) * (if q = mp s then Ψ y q else 0))) := by
    intro u s y q
    rw [ite_and, ite_and, ite_and]
    split_ifs <;> ring
  simp only [hpt, ← Finset.mul_sum]
  rw [← Finset.sum_mul, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 ha)]
  refine congrArg (A a * ·) ?_
  simp only [ite_mul, zero_mul]
  rw [sum_lt hL]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  refine congrArg (B s * ·) ?_
  simp only [Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm (s := range (2 ^ 16)), Finset.sum_comm (s := range (2 ^ 16))]
  simp only [Finset.sum_ite_eq', Finset.mem_range, ha, hm, ite_true, hfp s hs', hmp s hs']

/-- **The indicator against any weights** (the family's residual): with `Ψ = z` the cells' values
this is `Σ_σ Σ_t A(src) Σ_s B(s) (z(src, field s) − z(mirBlk, mirPos s))`, zero when every field
equals its mirror. -/
theorem linkInd_sum (f : ℕ) (A B : ℕ → F) (Ψ : ℕ → ℕ → F) :
    ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), ∑ q ∈ range (2 ^ 10),
      A u * B s * Ψ y q * linkInd f u s y q =
    ∑ σ ∈ range 2, ∑ t ∈ range (fam f).n, A (srcB σ f t) * ∑ s ∈ range (fbits f),
      B s * (Ψ (srcB σ f t) (fpos f s) - Ψ (mirB σ f t) (mpos f t s)) := by
  unfold linkInd
  simp only [Finset.mul_sum (s := range 2), Finset.mul_sum (s := range (fam f).n)]
  rw [sum_pull]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [sum_pull]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hσ' := Finset.mem_range.1 hσ
  have ht' := Finset.mem_range.1 ht
  have hb := fam_bounds (s := 0) hσ' ht'
  exact one_source (fpos f) (mpos f t) hb.1 hb.2.1 (fbits_le f)
    (fun s hs => ((fam_bounds hσ' ht').2.2 hs).1) (fun s hs => ((fam_bounds hσ' ht').2.2 hs).2)
    A B Ψ

/-- **`linkW_mle`** (A.8): `W_f` is the multilinear extension of the source-minus-mirror indicator
at `(τ, θ, r_blk, r_pos)` (`eqAtR r u = eq(r, cube u)`). -/
theorem linkW_mle (f : ℕ) (τ : Fin 16 → F) (θ : Fin 10 → F) (rb : Fin 16 → F) (rp : Fin 10 → F) :
    linkWS f τ θ rb rp =
      ∑ u ∈ range (2 ^ 16), ∑ s ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ 16), ∑ q ∈ range (2 ^ 10),
        eqAtR τ u * eqAtR θ s * (eqAtR rb y * eqAtR rp q) * linkInd f u s y q := by
  rw [linkInd_sum f (eqAtR τ) (eqAtR θ) (fun y q => eqAtR rb y * eqAtR rp q)]
  unfold linkWS slotWL
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun t _ => ?_
  refine congrArg (eqAtR τ (srcB σ f t) * ·) ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

end LinkProof

/-! ## Controls -/

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

/-- At a Boolean block point the block sum reads the target: `G(p) = E(b, p)`. -/
theorem blkW_cube {b : ℕ} (hb : b < 2 ^ 16) (p : ℕ) : blkW (cubeN 16 b) p = nodeE b p := by
  unfold blkW
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.2 hb) fun x hx hne => by
    rw [eqAtR_cubeN hb (Finset.mem_range.1 hx), if_neg hne, zero_mul]]
  rw [eqAtR_cubeN hb hb, if_pos rfl, one_mul]

/-- (+) `one` on a chain block; the counter of chain block 1 is `t = 128` (bit 7 set). -/
theorem nodeBit_pos : nodeBit 0 1152 = true ∧ nodeBit 1 1031 = true ∧
    nodeBit Layout.stmtBase 1152 = true ∧ nodeBit (Layout.stmtBase + 1) 513 = true ∧
    nodeBit (Layout.wotsBase + 5) 584 = true ∧ nodeBit (Layout.wotsBase + 5) 593 = true := by
  decide

/-- (−) Wrong-offset and wrong-constant detection: chain block 1's bit 6 is clear (a counter
`64 k` would set it), `hashA`'s tag `0x4C` has bit 1 clear where `hashB1 tagNode`'s `0x4E` has it
set, `w43` step `(1, 2)` has `s`'s bit 0 clear, and `WM` is not pinned. -/
theorem nodeBit_neg : nodeBit 1 1030 = false ∧ nodeBit Layout.stmtBase 513 = false ∧
    nodeBit (Layout.wotsBase + 5) 592 = false ∧ nodeBit Layout.wmBase 1152 = false ∧
    nodeBit (2 * Layout.chainN - 1) 1088 = true ∧ nodeBit (2 * Layout.chainN - 2) 1088 = false := by
  decide

/-- (+/−) The closed form at a Boolean block point: chain block 1's counter bit 7 is read as `1`,
its bit 6 as `0`. -/
theorem Gc_controls : Gc (cubeN 16 1) 1031 = 1 ∧ Gc (cubeN 16 1) 1030 = 0 := by
  rw [← blkW_eq _ (by norm_num), ← blkW_eq _ (by norm_num), blkW_cube (by norm_num),
    blkW_cube (by norm_num), nodeE_bit, nodeE_bit, nodeBit_pos.2.1, nodeBit_neg.1]
  exact ⟨rfl, rfl⟩

theorem slotWL_cube {pos : ℕ → ℕ} {L s₀ q : ℕ} (hs : s₀ < L) (hL : L ≤ 2 ^ 10)
    (hpos : ∀ s < L, pos s < 2 ^ 10) (hq : q < 2 ^ 10) :
    slotWL pos L (cubeN 10 s₀) (cubeN 10 q) = if pos s₀ = q then 1 else 0 := by
  unfold slotWL
  rw [Finset.sum_eq_single_of_mem s₀ (Finset.mem_range.2 hs) fun x hx hne => by
    rw [eqAtR_cubeN (by omega) (by have := Finset.mem_range.1 hx; omega), if_neg hne, zero_mul]]
  rw [eqAtR_cubeN (by omega) (by omega), if_pos rfl, one_mul, eqAtR_cubeN hq (hpos s₀ hs)]

/-- Family `x` at `τ` = its first source (slot 0, step 0). -/
theorem linkWS_x0 (θ : Fin 10 → F) (rb : Fin 16 → F) (rp : Fin 10 → F) :
    linkWS 0 (cubeN 16 (wb 0)) θ rb rp =
      eqAtR rb (wb 0) * slotWL (fpos 0) (fbits 0) θ rp -
        eqAtR rb (mirB 0 0 0) * slotWL (mpos 0 0) (fbits 0) θ rp := by
  have hw : ∀ σ, wb σ = 46298 + 498 * σ := fun σ => rfl
  have hn : (fam 0).n = 399 := rfl
  have hs : ∀ σ t, srcB σ 0 t = wb σ + t := fun _ _ => rfl
  have h0 : ∀ σ ∈ range 2, ∀ t ∈ range 399, (σ, t) ≠ (0, 0) →
      eqAtR (cubeN 16 (wb 0)) (srcB σ 0 t) = 0 := by
    intro σ hσ t ht hne
    have := Finset.mem_range.1 hσ
    have := Finset.mem_range.1 ht
    rw [eqAtR_cubeN (by rw [hw]; norm_num) (by rw [hs, hw]; omega), if_neg]
    rw [hs, hw, hw]
    intro h
    exact hne (by rw [Prod.mk.injEq]; omega)
  unfold linkWS
  rw [hn, Finset.sum_eq_single_of_mem 0 (by simp) fun σ hσ hne => Finset.sum_eq_zero fun t ht => by
    rw [h0 σ hσ t ht (by simp [hne]), zero_mul]]
  rw [Finset.sum_eq_single_of_mem 0 (by simp) fun t ht hne => by
    rw [h0 0 (by simp) t ht (by simp [hne]), zero_mul]]
  rw [eqAtR_cubeN (by rw [hw]; norm_num) (by rw [hs, hw]; norm_num), if_pos (by rw [hs]; rfl),
    one_mul]
  rfl

theorem bits0 : fbits 0 = 256 := rfl

/-- (+) Family `x`'s indicator: source block, field bit 0 at position 600 (byte 11). -/
theorem linkW_hit : linkWS 0 (cubeN 16 (wb 0)) (cubeN 10 0) (cubeN 16 (wb 0)) (cubeN 10 600) = 1 := by
  rw [linkWS_x0, bits0, slotWL_cube (by norm_num) (by norm_num) (fun s hs => by
      simp only [fpos, fam]; omega) (by norm_num),
    slotWL_cube (by norm_num) (by norm_num) (fun s hs => by simp only [mpos, fam, id]; omega)
      (by norm_num),
    eqAtR_cubeN (by simp [wb, Layout.wotsBase, Layout.stmtBase, Layout.chainN])
      (by simp [wb, Layout.wotsBase, Layout.stmtBase, Layout.chainN]),
    eqAtR_cubeN (by simp [wb, Layout.wotsBase, Layout.stmtBase, Layout.chainN])
      (by simp [mirB, wmB, fam, Layout.wmBase, Layout.wotsBase, Layout.stmtBase, Layout.chainN,
        Layout.wotsSlot])]
  simp [fpos, mpos, mirB, wmB, wb, fam, Layout.wmBase, Layout.wotsBase, Layout.stmtBase,
    Layout.chainN, Layout.wotsSlot]

/-- (−) A wrong offset (position 601 is the field's bit 1, not bit 0) reads `0`. -/
theorem linkW_off : linkWS 0 (cubeN 16 (wb 0)) (cubeN 10 0) (cubeN 16 (wb 0)) (cubeN 10 601) = 0 := by
  rw [linkWS_x0, bits0, slotWL_cube (by norm_num) (by norm_num) (fun s hs => by
      simp only [fpos, fam]; omega) (by norm_num),
    slotWL_cube (by norm_num) (by norm_num) (fun s hs => by simp only [mpos, fam, id]; omega)
      (by norm_num)]
  simp [fpos, mpos, fam]

/-- (+) The mirror side: its cell reads `−1`. -/
theorem linkW_mir : linkWS 0 (cubeN 16 (wb 0)) (cubeN 10 0) (cubeN 16 (mirB 0 0 0))
    (cubeN 10 (mpos 0 0 0)) = -1 := by
  have hm : mirB 0 0 0 = 47294 := rfl
  have hw : wb 0 = 46298 := rfl
  rw [linkWS_x0, bits0, slotWL_cube (by norm_num) (by norm_num) (fun s hs => by
      simp only [fpos, fam]; omega) (by simp [mpos, fam]),
    slotWL_cube (by norm_num) (by norm_num) (fun s hs => by simp only [mpos, fam, id]; omega)
      (by simp [mpos, fam]), hm, hw, eqAtR_cubeN (by norm_num) (by norm_num),
    eqAtR_cubeN (by norm_num) (by norm_num)]
  simp [fpos, mpos, fam]

end Controls

end NodeT
end FR
