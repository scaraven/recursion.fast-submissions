-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8 `targetS` on a node; stage S-CN4b). 3.x
-- template: `FRNodeTarget` (`targetSNode_blk`, `Gc`, `blkW_eq`, `wots_part`, `Gc_hi`).
import FRNodeTarget4

/-!
# The revision 4.1 node's `targetS`: the closed form of the block sum (`N2`/`N4`/`N8`)

`targetSNode4S ν r` (`FRNodeTarget4`) is `P^e(σ) = Σ_{hi<256} eq(r_lo, hi) · G(σ + 64 hi)` with the
block sum `G(p) = Σ_{blk < 2^nb} w(blk) · E(blk, p)`, `w = eq(r_blk, ·)` (`targetSNode4_blk`).
This module gives `G` in closed form for **any** block weight `w` (`blkW4_eq`):

* the sum is split over `nodeLayout4`'s intervals by a generic lemma on a tiling (`sum_contig`,
  from `N4c.layout_contig`), each block's target read off its interval (`N4c.tgt_of_mem`): the
  layout is never evaluated;
* per piece: each main chain (`streamStart`; the body with counter `64 (o + 2)`, `tgtE_ctr`; the
  last block final with `t = chBytes`), `hashStmt` per verifier slot, each WOTS run (3.x's
  `wots_part` at base `wotsB`), the tail's candidate final blocks (`t = aggB k′`, final) and `c_A`'s
  `hashA`; `free` blocks give `0`. A final block's counter is split off by the new bit lemma
  **`tgtE_fin`** (`tgtE (blockTarget t fin)` for any `t < 2^32`);
* **`Gc4 ν w p`**: ten class weights (`clsW`, range sums and single blocks of `w`) against the
  constant classes' bits (`cls4`: 3.x's `cls` with class 2 the counter-free final block), plus the
  counter bits of the stream bodies (`ctrW`), of the final blocks (`finW`) and `w43`'s step
  fields (`stepW`). It vanishes past position 1,152 (`Gc4_hi`).
-/

namespace FR
namespace NT4C
open Finset RecursionFast Rev4 Impl Kinds FR.Stream NodeT NT4

/-! ## The final block's counter -/

/-- **A block target's counter split off** (any `t < 2^32`): `t_lo`'s bit `j` is bit `j` of `t`,
every other bit is the counter-free target's (`t_hi = 0`). -/
theorem tgtE_fin {t p : ℕ} (ht : t < 2 ^ 32) (hp : p < 2 ^ 14) (fin : Bool) :
    tgtE (blockTarget t fin) p = tgtE (blockTarget 0 fin) p +
      if 1024 ≤ p ∧ p < 1056 then bF (t.testBit (p - 1024)) else 0 := by
  unfold tgtE blockTarget
  rw [ProductCircuit.pos_val hp, lo32_bit ht, lo32_bit (show 0 < 2 ^ 32 by norm_num), hi32_bit ht,
    hi32_bit (show 0 < 2 ^ 32 by norm_num)]
  by_cases a : p < 1024
  · simp [a, bF]
  by_cases b : p < 1056
  · simp [a, b, show p - 1024 < 32 by omega, bF]
  · simp [a, b]

/-! ## The block sum over the layout's intervals -/

/-- A target's bit, `0` on `none` (a `free` block). -/
def tF (t : Option Block.Target) (p : ℕ) : F :=
  match t with
  | some t => tgtE t p
  | none => 0

theorem nodeE4_tF (ν : NodeKind) (blk p : ℕ) : nodeE4 ν blk p = tF (N4c.nodeKind4 ν blk) p := by
  unfold nodeE4 tF; cases N4c.nodeKind4 ν blk <;> rfl

/-- **The block sum** `G(p) = Σ_blk w(blk) E(blk, p)` at any block weight `w`. -/
def blkW4 (ν : NodeKind) (w : ℕ → F) (p : ℕ) : F :=
  ∑ blk ∈ range (2 ^ nbN ν), w blk * nodeE4 ν blk p

/-- An interval's part of the block sum. -/
def ivS (w : ℕ → F) (p : ℕ) (iv : N4c.TIv) : F :=
  ∑ o ∈ range (iv.hi - iv.lo), w (iv.lo + o) * tF (iv.tgt o) p

/-- **A sum over a tiled range is the sum over the tiles.** -/
theorem sum_contig (f : ℕ → F) : ∀ {ivs : List N4c.TIv} {a b : ℕ}, N4c.contig ivs a b = true →
    ∑ x ∈ range (b - a), f (a + x) =
      (ivs.map fun iv => ∑ o ∈ range (iv.hi - iv.lo), f (iv.lo + o)).sum
  | [], a, b, h => by simp only [N4c.contig, beq_iff_eq] at h; subst h; simp
  | iv :: ivs, a, b, h => by
    simp only [N4c.contig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hlt⟩, h⟩ := h
    have hb := (N4c.contig_bounds h).1
    rw [List.map_cons, List.sum_cons, ← sum_contig f h,
      show b - iv.lo = (iv.hi - iv.lo) + (b - iv.hi) by omega, Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by rw [show iv.lo + (iv.hi - iv.lo + x) = iv.hi + x by omega]

/-- **`G` over the layout**: the sum of the intervals' parts (no evaluation of the layout). -/
theorem blkW4_layout (ν : NodeKind) (w : ℕ → F) (p : ℕ) :
    blkW4 ν w p = ((N4c.nodeLayout4 ν).map (ivS w p)).sum := by
  have h := sum_contig (fun x => w x * nodeE4 ν x p) (N4c.layout_contig ν)
  simp only [Nat.sub_zero, zero_add] at h
  rw [blkW4, show 2 ^ nbN ν = ν.blocks from rfl, h]
  refine congrArg List.sum (List.map_congr_left fun iv hiv => ?_)
  refine Finset.sum_congr rfl fun o ho => ?_
  have hk : iv.mem (iv.lo + o) = true := by
    have := Finset.mem_range.1 ho
    simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq]; omega
  rw [nodeE4_tF, N4c.tgt_of_mem hiv hk, Nat.add_sub_cancel_left]

/-! ## List sums -/

theorem lsum_flatMap {α : Type*} (l : List ℕ) (g : ℕ → List α) (f : α → F) :
    ((l.flatMap g).map f).sum = (l.map fun i => ((g i).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

theorem lsum_range (n : ℕ) (f : ℕ → F) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem ivS_one (w : ℕ → F) (p : ℕ) (k : BlockKind) (x : ℕ) (g : ℕ → Option Block.Target) :
    ivS w p ⟨k, x, x + 1, g⟩ = w x * tF (g 0) p := by
  simp [ivS]

theorem ivS_free (w : ℕ → F) (p lo hi : ℕ) : ivS w p (N4c.freeIv lo hi) = 0 := by
  simp [ivS, N4c.freeIv, tF]

private theorem sum_ite_c {s : Finset ℕ} (c : Prop) [Decidable c] (g : ℕ → F) :
    ∑ k ∈ s, (if c then g k else 0) = if c then ∑ k ∈ s, g k else 0 := by
  split_ifs <;> simp

private theorem sum_mul_ite {s : Finset ℕ} (c : Prop) [Decidable c] (g h : ℕ → F) :
    ∑ k ∈ s, g k * (if c then h k else 0) = if c then ∑ k ∈ s, g k * h k else 0 := by
  split_ifs <;> simp

/-! ## The pieces -/

/-- `Σ_{k<n} w(lo + k)`. -/
def rngS (w : ℕ → F) (lo n : ℕ) : F := ∑ k ∈ range n, w (lo + k)

/-- The constant classes' targets: 3.x's `cls`, with class 2 the counter-free final block (the
final blocks' counters are split off by `tgtE_fin`). -/
def cls4 (c : ℕ) : Block.Target := if c = 2 then blockTarget 0 true else cls c

theorem cls4_eq : cls4 0 = streamStart.target ∧ cls4 1 = blockTarget 0 false ∧
    cls4 2 = blockTarget 0 true ∧ cls4 3 = hashA.target ∧
    cls4 4 = (hashB1 RecursionFast.tagNode).target ∧ cls4 5 = hashB2.target ∧
    cls4 6 = (w43 0 0).target ∧ cls4 7 = (hashB1 RecursionFast.tagWotsLeaf).target ∧
    cls4 8 = streamEnd41.target ∧ cls4 9 = (hashB1 RecursionFast.tagSigNode).target :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Pieces
variable (w : ℕ → F) {p : ℕ}

/-- **A stream body**: blocks `1 … n` of a stream of `B` bytes (none final), counter `64 (o + 2)`. -/
theorem body_sum {B lo n : ℕ} (hn : n + 1 < nBlocks B) (h26 : n + 2 ≤ 2 ^ 26) (hp : p < 2 ^ 14) :
    ∑ o ∈ range n, w (lo + o) * tgtE (streamTarget B (o + 1)) p =
      rngS w lo n * tgtE (cls4 1) p +
      if 1030 ≤ p ∧ p < 1056 then ∑ k ∈ range n, w (lo + k) * bF ((k + 2).testBit (p - 1030))
      else 0 := by
  have h : ∀ o ∈ range n, w (lo + o) * tgtE (streamTarget B (o + 1)) p =
      w (lo + o) * tgtE (cls4 1) p +
        w (lo + o) * (if 1030 ≤ p ∧ p < 1056 then bF ((o + 2).testBit (p - 1030)) else 0) := by
    intro o ho
    have ho' := Finset.mem_range.1 ho
    have e : streamTarget B (o + 1) = blockTarget (64 * (o + 2)) false := by
      unfold streamTarget ctrAt
      rw [if_neg (show ¬ (o + 1 + 1 = nBlocks B) by omega),
        decide_eq_false (show ¬ (o + 1 + 1 = nBlocks B) by omega)]
    rw [e, tgtE_ctr (by omega) hp, mul_add]
    rfl
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.sum_mul, sum_mul_ite]
  rfl

/-- **A final block** (`t < 2^32`): the counter-free class 2 and `t`'s bits on `t_lo`. -/
theorem fin_one {t : ℕ} (ht : t < 2 ^ 32) (hp : p < 2 ^ 14) (x : ℕ) :
    w x * tgtE (blockTarget t true) p = w x * tgtE (cls4 2) p +
      if 1024 ≤ p ∧ p < 1056 then w x * bF (t.testBit (p - 1024)) else 0 := by
  rw [tgtE_fin ht hp, mul_add, mul_ite, mul_zero]
  rfl

/-- The layout's numbers per signed child: the chain's bytes give its block count, the counters fit. -/
theorem chain_facts (ν : NodeKind) {σ : ℕ} (hσ : σ < 2) :
    nBlocks (N4c.chBytes ν σ) = N4c.chLen ν σ ∧ 2 ≤ N4c.chLen ν σ ∧
      N4c.chLen ν σ ≤ 2 ^ 26 ∧ N4c.chBytes ν σ < 2 ^ 32 := by
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> cases ν <;> decide

/-- Chain `σ`'s last block. -/
def lastB (ν : NodeKind) (σ : ℕ) : ℕ := N4c.chBase ν σ + 1 + (N4c.chLen ν σ - 2)

/-- **Main chain `σ`**: `streamStart`, the body, the final last block. -/
theorem chain_piece (ν : NodeKind) {σ : ℕ} (hσ : σ < 2) (hp : p < 2 ^ 14) :
    ((N4c.chainIvs ν σ).map (ivS w p)).sum =
      w (N4c.chBase ν σ) * tgtE (cls4 0) p +
      (rngS w (N4c.chBase ν σ + 1) (N4c.chLen ν σ - 2) * tgtE (cls4 1) p +
        if 1030 ≤ p ∧ p < 1056 then ∑ k ∈ range (N4c.chLen ν σ - 2),
          w (N4c.chBase ν σ + 1 + k) * bF ((k + 2).testBit (p - 1030)) else 0) +
      (w (lastB ν σ) * tgtE (cls4 2) p +
        if 1024 ≤ p ∧ p < 1056 then w (lastB ν σ) * bF ((N4c.chBytes ν σ).testBit (p - 1024))
        else 0) := by
  obtain ⟨hB, h2, h26, h32⟩ := chain_facts ν hσ
  simp only [N4c.chainIvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    ivS_one]
  rw [ivS, show N4c.chBase ν σ + N4c.chLen ν σ - (N4c.chBase ν σ + 1) = N4c.chLen ν σ - 2 + 1 by
    omega, Finset.sum_range_succ]
  simp only [tF]
  rw [body_sum w (show N4c.chLen ν σ - 2 + 1 < nBlocks (N4c.chBytes ν σ) by omega) (by omega) hp]
  have e : streamTarget (N4c.chBytes ν σ) (N4c.chLen ν σ - 2 + 1) =
      blockTarget (N4c.chBytes ν σ) true := by
    unfold streamTarget ctrAt
    rw [if_pos (show N4c.chLen ν σ - 2 + 1 + 1 = nBlocks (N4c.chBytes ν σ) by omega),
      decide_eq_true (show N4c.chLen ν σ - 2 + 1 + 1 = nBlocks (N4c.chBytes ν σ) by omega)]
  rw [e, fin_one w h32 hp, cls4_eq.1]
  simp only [lastB]
  ring

/-- **`hashStmt`** per verifier slot. -/
theorem stmt_piece (ν : NodeKind) :
    ((N4c.stmtIvs ν).map (ivS w p)).sum = ∑ v ∈ range ν.vslots,
      (w (N4c.stmtB ν + 3 * v) * tgtE (cls4 3) p + w (N4c.stmtB ν + 3 * v + 1) * tgtE (cls4 4) p +
        w (N4c.stmtB ν + 3 * v + 2) * tgtE (cls4 5) p) := by
  rw [N4c.stmtIvs, lsum_flatMap, lsum_range]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ivS_one, tF,
    cls4_eq]
  ring

/-- **A WOTS run's closed form** at its first block `b` (3.x's `wotsC`): the 399 `w43` steps with
their step fields, the key leaf (`hashB1 tagWotsLeaf`, 65 stream blocks, `streamEnd41`), the 16
path pairs. -/
def wotsP (b p : ℕ) : F :=
  rngS w b 399 * tgtE (cls4 6) p + w (b + 399) * tgtE (cls4 7) p +
    rngS w (b + 400) 65 * tgtE (cls4 1) p + w (b + 465) * tgtE (cls4 8) p +
    ∑ t ∈ range 16, (w (b + 466 + 2 * t) * tgtE (cls4 9) p + w (b + 467 + 2 * t) * tgtE (cls4 5) p) +
    (if 1030 ≤ p ∧ p < 1056 then
      ∑ k ∈ range 65, w (b + 400 + k) * bF ((k + 2).testBit (p - 1030)) else 0) +
    (if 584 ≤ p ∧ p < 592 then ∑ o ∈ range 399, w (b + o) * bF ((o / 3).testBit (p - 584)) else 0) +
    (if 592 ≤ p ∧ p < 600 then ∑ o ∈ range 399, w (b + o) * bF ((o % 3).testBit (p - 592)) else 0)

theorem tiv_eq {k : BlockKind} {lo hi lo' hi' : ℕ} {t t' : ℕ → Option Block.Target}
    (h1 : lo = lo') (h2 : hi = hi') (h3 : ∀ o, t o = t' o) :
    (⟨k, lo, hi, t⟩ : N4c.TIv) = ⟨k, lo', hi', t'⟩ := by
  subst h1 h2; rw [funext h3]

/-- **A WOTS run's intervals** at base `b = wotsB ν σ`, for any weight of an interval `g`. -/
theorem wots_map (ν : NodeKind) (σ : ℕ) (g : N4c.TIv → F) :
    ((N4c.wotsIvs ν σ).map g).sum =
      (g ⟨.w43, N4c.wotsB ν σ, N4c.wotsB ν σ + 399, fun o => some (wotsTgt o)⟩ +
      (g ⟨.hashB1, N4c.wotsB ν σ + 399, N4c.wotsB ν σ + 399 + 1, fun o => some (wotsTgt (399 + o))⟩ +
      (g ⟨.stream, N4c.wotsB ν σ + 400, N4c.wotsB ν σ + 465, fun o => some (wotsTgt (400 + o))⟩ +
      g ⟨.streamEnd41, N4c.wotsB ν σ + 465, N4c.wotsB ν σ + 465 + 1,
        fun o => some (wotsTgt (465 + o))⟩))) +
      ∑ t ∈ range 16, (g ⟨.hashB1, N4c.wotsB ν σ + 466 + 2 * t, N4c.wotsB ν σ + 466 + 2 * t + 1,
          fun o => some (wotsTgt (466 + 2 * t + o))⟩ +
        g ⟨.hashB2, N4c.wotsB ν σ + 467 + 2 * t, N4c.wotsB ν σ + 467 + 2 * t + 1,
          fun o => some (wotsTgt (467 + 2 * t + o))⟩) := by
  rw [N4c.wotsIvs, List.map_map]
  simp only [Layout.wotsIvs, mul_zero, add_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_apply]
  rw [lsum_flatMap, lsum_range]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Function.comp_apply]
  have e : ∀ t, Layout.wotsBase + 466 + 2 * t - Layout.wotsBase = 466 + 2 * t ∧
      Layout.wotsBase + 467 + 2 * t - Layout.wotsBase = 467 + 2 * t := fun t => ⟨by omega, by omega⟩
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg g (tiv_eq (by omega) (by omega) fun o => by simp))
    (congrArg₂ (· + ·) (congrArg g (tiv_eq (by omega) (by omega) fun o => by simp))
      (congrArg₂ (· + ·) (congrArg g (tiv_eq (by omega) (by omega) fun o => by simp))
        (congrArg g (tiv_eq (by omega) (by omega) fun o => by simp)))))
    (Finset.sum_congr rfl fun t _ => congrArg₂ (· + ·)
      (congrArg g (tiv_eq (by omega) (by omega) fun o => by rw [(e t).1]))
      (congrArg g (tiv_eq (by omega) (by omega) fun o => by rw [(e t).2])))

/-- **A WOTS run** (3.x's `wots_part` at base `wotsB ν σ`). -/
theorem wots_piece (ν : NodeKind) (σ : ℕ) (hp : p < 2 ^ 14) :
    ((N4c.wotsIvs ν σ).map (ivS w p)).sum = wotsP w (N4c.wotsB ν σ) p := by
  rw [wots_map]
  simp only [ivS, tF, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.reduceSub,
    Finset.sum_range_one, add_zero]
  have hw43 : ∀ o ∈ range 399, w (N4c.wotsB ν σ + o) * tgtE (wotsTgt o) p =
      w (N4c.wotsB ν σ + o) * tgtE (cls4 6) p +
        w (N4c.wotsB ν σ + o) * (if 584 ≤ p ∧ p < 592 then bF ((o / 3).testBit (p - 584)) else 0) +
        w (N4c.wotsB ν σ + o) * (if 592 ≤ p ∧ p < 600 then bF ((o % 3).testBit (p - 592)) else 0) := by
    intro o ho
    rw [wotsTgt, if_pos (Finset.mem_range.1 ho), tgtE_w43 _ _ hp, cls4_eq.2.2.2.2.2.2.1]
    ring
  have hleaf : ∀ o ∈ range 65, w (N4c.wotsB ν σ + 400 + o) * tgtE (wotsTgt (400 + o)) p =
      w (N4c.wotsB ν σ + 400 + o) * tgtE (streamTarget 4265 (o + 1)) p := by
    intro o ho
    have := Finset.mem_range.1 ho
    rw [wotsTgt, if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show 400 + o - 399 = o + 1 by omega]
  have hpath : ∀ t ∈ range 16, w (N4c.wotsB ν σ + 466 + 2 * t) * tgtE (wotsTgt (466 + 2 * t)) p +
      w (N4c.wotsB ν σ + 467 + 2 * t) * tgtE (wotsTgt (467 + 2 * t)) p =
      w (N4c.wotsB ν σ + 466 + 2 * t) * tgtE (cls4 9) p +
        w (N4c.wotsB ν σ + 467 + 2 * t) * tgtE (cls4 5) p := by
    intro t _
    simp only [wotsTgt, show ¬ 466 + 2 * t < 399 by omega, show 466 + 2 * t ≠ 399 by omega,
      show ¬ 466 + 2 * t < 465 by omega, show 466 + 2 * t ≠ 465 by omega,
      show (466 + 2 * t - 466) % 2 = 0 by omega, show ¬ 467 + 2 * t < 399 by omega,
      show 467 + 2 * t ≠ 399 by omega, show ¬ 467 + 2 * t < 465 by omega,
      show 467 + 2 * t ≠ 465 by omega, show ¬ (467 + 2 * t - 466) % 2 = 0 by omega,
      ite_false, ite_true, cls4_eq]
  rw [Finset.sum_congr rfl hw43, Finset.sum_congr rfl hleaf, Finset.sum_congr rfl hpath,
    body_sum w (B := 4265) (by decide) (by norm_num) hp, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, sum_mul_ite, sum_mul_ite]
  simp only [wotsTgt, show ¬ (399 : ℕ) < 399 by decide, show ¬ (465 : ℕ) < 399 by decide,
    show (465 : ℕ) ≠ 399 by decide, show ¬ (465 : ℕ) < 465 by decide, ite_true, ite_false]
  unfold wotsP rngS
  rw [cls4_eq.2.2.2.2.2.2.2.1, cls4_eq.2.2.2.2.2.2.2.2.1]
  ring

theorem lsum_range_map {α : Type*} (n : ℕ) (g : ℕ → α) (f : α → F) :
    (((List.range n).map g).map f).sum = ∑ i ∈ range n, f (g i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem maxK_le (ν : NodeKind) : 1 ≤ ν.maxK ∧ ν.maxK ≤ 8 := by cases ν <;> decide

theorem aggB_lt {k : ℕ} (hk : k ≤ 8) : N4c.aggB k < 2 ^ 32 := by
  simp only [N4c.aggB, N4c.segB, N4c.spacerB]; omega

/-- **A candidate final block** `F_{a,k′}`: the last block of a stream of `aggB k′` bytes. -/
theorem fin_target (k : ℕ) :
    streamTarget (N4c.aggB k) (N4c.aggL k - 1) = blockTarget (N4c.aggB k) true := by
  have h1 : 1 ≤ N4c.aggL k := by simp only [N4c.aggL, N4c.aggB]; omega
  unfold streamTarget
  rw [(N4c.ctr_final k).1, N4c.aggL_nBlocks, Nat.sub_add_cancel h1, decide_eq_true rfl]

/-- **Aggregate `a`'s tail**: the `maxK − 1` candidate final blocks, then `c_A`'s `hashA`. -/
theorem tail_piece (ν : NodeKind) (a : ℕ) (hp : p < 2 ^ 14) :
    ((N4c.tailIvs ν a).map (ivS w p)).sum = ∑ j ∈ range (ν.maxK - 1),
      (w (N4c.finB ν a + j) * tgtE (cls4 2) p +
        if 1024 ≤ p ∧ p < 1056 then w (N4c.finB ν a + j) * bF ((N4c.aggB (j + 1)).testBit (p - 1024))
        else 0) + w (N4c.cAB ν a) * tgtE (cls4 3) p := by
  rw [N4c.tailIvs, List.map_append, List.sum_append, lsum_range_map]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ivS_one, tF,
    cls4_eq.2.2.2.1]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [fin_target, fin_one w (aggB_lt (by have := Finset.mem_range.1 hj; have := maxK_le ν; omega)) hp]

end Pieces

/-! ## The closed form -/

/-- **The ten class weights** from a point weight `pt` and a range sum `rng` (`rng lo n` stands for
`Σ_{k<n} pt(lo + k)`): `streamStart`; the stream bodies (both chains, both key leaves); the final
blocks (both chains' last blocks, the tails' candidates); `hashA` (statements, `c_A`); `hashB1
tagNode`; `hashB2` (statements, paths); `w43`; `hashB1 tagWotsLeaf`; `streamEnd41`; `hashB1
tagSigNode`. -/
def clsW (ν : NodeKind) (pt : ℕ → F) (rng : ℕ → ℕ → F) : ℕ → F
  | 0 => sumTo 2 fun σ => pt (N4c.chBase ν σ)
  | 1 => (sumTo 2 fun σ => rng (N4c.chBase ν σ + 1) (N4c.chLen ν σ - 2)) +
      sumTo 2 fun σ => rng (N4c.wotsB ν σ + 400) 65
  | 2 => (sumTo 2 fun σ => pt (lastB ν σ)) + sumTo (N4c.nAgg ν) fun a => rng (N4c.finB ν a) (ν.maxK - 1)
  | 3 => (sumTo ν.vslots fun v => pt (N4c.stmtB ν + 3 * v)) +
      sumTo (N4c.nAgg ν) fun a => pt (N4c.cAB ν a)
  | 4 => sumTo ν.vslots fun v => pt (N4c.stmtB ν + 3 * v + 1)
  | 5 => (sumTo ν.vslots fun v => pt (N4c.stmtB ν + 3 * v + 2)) +
      sumTo 2 fun σ => sumTo 16 fun t => pt (N4c.wotsB ν σ + 467 + 2 * t)
  | 6 => sumTo 2 fun σ => rng (N4c.wotsB ν σ) 399
  | 7 => sumTo 2 fun σ => pt (N4c.wotsB ν σ + 399)
  | 8 => sumTo 2 fun σ => pt (N4c.wotsB ν σ + 465)
  | _ => sumTo 2 fun σ => sumTo 16 fun t => pt (N4c.wotsB ν σ + 466 + 2 * t)

/-- The stream bodies' counter bit `j` from a per-range counter sum `ct lo n j`. -/
def ctrG (ν : NodeKind) (ct : ℕ → ℕ → ℕ → F) (j : ℕ) : F :=
  (sumTo 2 fun σ => ct (N4c.chBase ν σ + 1) (N4c.chLen ν σ - 2) j) +
    sumTo 2 fun σ => ct (N4c.wotsB ν σ + 400) 65 j

/-- `Σ_{k<n} w(lo + k) · bit_j(k + 2)` (block `lo + k` of a body has counter `64 (k + 2)`). -/
def ctrS (w : ℕ → F) (lo n j : ℕ) : F := ∑ k ∈ range n, w (lo + k) * bF ((k + 2).testBit j)

/-- The final blocks' counter bit `j`: both chains' last blocks (`chBytes`), each tail's
candidates (`aggB k′`). -/
def finG (ν : NodeKind) (pt : ℕ → F) (j : ℕ) : F :=
  (sumTo 2 fun σ => pt (lastB ν σ) * bF ((N4c.chBytes ν σ).testBit j)) +
    sumTo (N4c.nAgg ν) fun a => sumTo (ν.maxK - 1) fun i =>
      pt (N4c.finB ν a + i) * bF ((N4c.aggB (i + 1)).testBit j)

/-- `w43`'s step field bit `b` (`sel` picks `i = ⌊o/3⌋` or `s = o mod 3`). -/
def stepG (ν : NodeKind) (pt : ℕ → F) (sel : ℕ → ℕ) (b : ℕ) : F :=
  sumTo 2 fun σ => sumTo 399 fun o => pt (N4c.wotsB ν σ + o) * bF ((sel o).testBit b)

/-- **The closed form of `G(p)`** at the block weight `w`. -/
def Gc4 (ν : NodeKind) (w : ℕ → F) (p : ℕ) : F :=
  clsW ν w (rngS w) 0 * tgtE (cls4 0) p + clsW ν w (rngS w) 1 * tgtE (cls4 1) p +
    clsW ν w (rngS w) 2 * tgtE (cls4 2) p + clsW ν w (rngS w) 3 * tgtE (cls4 3) p +
    clsW ν w (rngS w) 4 * tgtE (cls4 4) p + clsW ν w (rngS w) 5 * tgtE (cls4 5) p +
    clsW ν w (rngS w) 6 * tgtE (cls4 6) p + clsW ν w (rngS w) 7 * tgtE (cls4 7) p +
    clsW ν w (rngS w) 8 * tgtE (cls4 8) p + clsW ν w (rngS w) 9 * tgtE (cls4 9) p +
    (if 1030 ≤ p ∧ p < 1056 then ctrG ν (ctrS w) (p - 1030) else 0) +
    (if 1024 ≤ p ∧ p < 1056 then finG ν w (p - 1024) else 0) +
    (if 584 ≤ p ∧ p < 592 then stepG ν w (· / 3) (p - 584) else 0) +
    (if 592 ≤ p ∧ p < 600 then stepG ν w (· % 3) (p - 592) else 0)

private theorem sum_two (g : ℕ → F) : ∑ σ ∈ range 2, g σ = g 0 + g 1 := by
  simp [Finset.sum_range_succ]

private theorem ite_add0 (c : Prop) [Decidable c] (a b : F) :
    (if c then a + b else 0) = (if c then a else 0) + (if c then b else 0) := by
  split_ifs <;> simp

/-- **`G` is the closed form** (any block weight, every position). -/
theorem blkW4_eq (ν : NodeKind) (w : ℕ → F) {p : ℕ} (hp : p < 2 ^ 14) : blkW4 ν w p = Gc4 ν w p := by
  rw [blkW4_layout, N4c.nodeLayout4]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, ivS_free, add_zero, lsum_flatMap, lsum_range]
  rw [chain_piece w ν (σ := 0) (by norm_num) hp, chain_piece w ν (σ := 1) (by norm_num) hp,
    stmt_piece, wots_piece w ν 0 hp, wots_piece w ν 1 hp,
    Finset.sum_congr rfl fun a _ => tail_piece w ν a hp]
  unfold Gc4 clsW ctrG finG stepG ctrS wotsP
  simp only [sumTo_eq, sum_two, rngS, ite_add0, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_ite_c]
  ring


/-- Past position 1,152 the closed form vanishes (no class pins anything there). -/
theorem Gc4_hi (ν : NodeKind) (w : ℕ → F) {p : ℕ} (h1 : 1153 ≤ p) (hp : p < 2 ^ 14) :
    Gc4 ν w p = 0 := by
  have hc : ∀ c, tgtE (cls4 c) p = 0 := by
    intro c
    unfold cls4
    split_ifs
    · exact tgtE_blockTarget_hi _ h1 hp
    · rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | c <;>
        first | exact tgtE_kind_hi _ h1 hp | exact tgtE_blockTarget_hi _ h1 hp
  simp only [Gc4, hc, mul_zero, show ¬ (1030 ≤ p ∧ p < 1056) by omega,
    show ¬ (1024 ≤ p ∧ p < 1056) by omega, show ¬ (584 ≤ p ∧ p < 592) by omega,
    show ¬ (592 ≤ p ∧ p < 600) by omega, ite_false, add_zero]

/-- **`targetS` through the block sum** (3.x's `targetSNode_blk` over `8 + nb` variables):
`P^e(σ) = Σ_hi eq(r_lo, hi) · G(σ + 64 hi)`. -/
theorem targetSNode4_blk (ν : NodeKind) (r : Array F) : targetSNode4S ν r =
    Array.ofFn (n := 64) fun σ =>
      ∑ hi ∈ range 256, eqAtR (zLo r) hi * blkW4 ν (eqAtR (rbOf4 ν r)) (σ + 64 * hi) := by
  unfold targetSNode4S
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [FR.targetS, ← (joinEquiv 8 (nbN ν)).sum_comp, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun hi => eqAtR (zLo r) hi *
      blkW4 ν (eqAtR (rbOf4 ν r)) (σ + 64 * hi))]
  refine Finset.sum_congr rfl fun hi _ => ?_
  have h1 : ∀ t : Fin (2 ^ nbN ν), (join hi t).val / 256 = t.val := fun t => by
    show (2 ^ 8 * t.val + hi.val) / 256 = t.val
    have := hi.isLt; omega
  have h2 : ∀ t : Fin (2 ^ nbN ν), (join hi t).val % 256 = hi.val := fun t => by
    show (2 ^ 8 * t.val + hi.val) % 256 = hi.val
    have := hi.isLt; omega
  simp only [show ∀ t, (joinEquiv 8 (nbN ν)) (hi, t) = join hi t from fun _ => rfl, eq_append_join,
    h1, h2, blkW4, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun blk => eqAtR (zLo r) hi * (eqAtR (rbOf4 ν r) blk *
    nodeE4 ν blk (σ + 64 * hi)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eq_cube, eq_cube]
  unfold eqAtR
  ring

/-- **`targetS_node4_eq`** (A.8's node form at revision 4.1): `P^e(σ) = Σ_{hi<19} eq(r_lo, hi) ·
Gc4(σ + 64 hi)`, the closed form of `Σ_blk eq(r_blk, blk) E(blk, ·)`. -/
theorem targetS_node4_eq (ν : NodeKind) (r : Array F) : targetSNode4S ν r =
    Array.ofFn (n := 64) fun σ =>
      ∑ hi ∈ range 19, eqAtR (zLo r) hi * Gc4 ν (eqAtR (rbOf4 ν r)) (σ + 64 * hi) := by
  rw [targetSNode4_blk]
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  have hσ := σ.isLt
  rw [show (256 : ℕ) = 19 + 237 from rfl, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range 237) fun x hx => by
      rw [blkW4_eq _ _ (by have := Finset.mem_range.1 hx; omega),
        Gc4_hi _ _ (by omega) (by have := Finset.mem_range.1 hx; omega), mul_zero], add_zero]
  exact Finset.sum_congr rfl fun hi hh => by
    rw [blkW4_eq _ _ (by have := Finset.mem_range.1 hh; omega)]

/-! ## The blocks the closed form reads lie below `hEnd` -/

/-- **Every block `Gc4` reads is below `hEnd ≤ 2^nb`**: the chains, the statements, the WOTS runs,
the tails. -/
theorem lay_bounds (ν : NodeKind) :
    (∀ σ < 2, N4c.chBase ν σ + N4c.chLen ν σ ≤ N4c.hEnd ν) ∧
    (∀ v < ν.vslots, N4c.stmtB ν + 3 * v + 3 ≤ N4c.hEnd ν) ∧
    (∀ σ < 2, N4c.wotsB ν σ + 498 ≤ N4c.hEnd ν) ∧
    (∀ a < N4c.nAgg ν, N4c.finB ν a + ν.maxK ≤ N4c.hEnd ν) ∧
    N4c.hEnd ν ≤ 2 ^ nbN ν := by
  have hE := (N4c.hEnd_le ν).2
  have hw0 := wotsB_hUsed ν (σ := 0) (by norm_num)
  have hw1 := wotsB_hUsed ν (σ := 1) (by norm_num)
  have hs : N4c.stmtB ν + 3 * ν.vslots = N4c.wotsB ν 0 := by simp [N4c.wotsB]
  refine ⟨fun σ hσ => ?_, fun v hv => by omega, fun σ hσ => ?_, fun a ha => ?_, ?_⟩
  · rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;>
      simp only [N4c.chBase, N4c.stmtB] at hs ⊢ <;> omega
  · rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;> omega
  · have : (a + 1) * ν.maxK ≤ N4c.nAgg ν * ν.maxK := Nat.mul_le_mul_right _ ha
    simp only [N4c.finB]; rw [Nat.add_mul, one_mul] at this; omega
  · cases ν <;> decide

/-- Chain `σ`'s last block lies in the chain. -/
theorem lastB_lt (ν : NodeKind) {σ : ℕ} (hσ : σ < 2) :
    lastB ν σ < N4c.chBase ν σ + N4c.chLen ν σ := by
  have := (chain_facts ν hσ).2.1; unfold lastB; omega

/-- **The class weights depend only on the blocks below `hEnd`** (and the ranges inside it). -/
theorem clsW_congr (ν : NodeKind) {pt pt' : ℕ → F} {rng rng' : ℕ → ℕ → F}
    (h1 : ∀ x < N4c.hEnd ν, pt x = pt' x)
    (h2 : ∀ lo n, lo + n ≤ N4c.hEnd ν → rng lo n = rng' lo n) (c : ℕ) :
    clsW ν pt rng c = clsW ν pt' rng' c := by
  obtain ⟨b1, b2, b3, b4, -⟩ := lay_bounds ν
  have hK := (maxK_le ν).1
  have s2 : ∀ {g g' : ℕ → F}, (∀ σ < 2, g σ = g' σ) → sumTo 2 g = sumTo 2 g' := fun h => by
    simp only [sumTo_eq]; exact Finset.sum_congr rfl fun σ hσ => h σ (Finset.mem_range.1 hσ)
  have sv : ∀ {n : ℕ} {g g' : ℕ → F}, (∀ v < n, g v = g' v) → sumTo n g = sumTo n g' := fun h => by
    simp only [sumTo_eq]; exact Finset.sum_congr rfl fun σ hσ => h σ (Finset.mem_range.1 hσ)
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | c <;> simp only [clsW]
  · exact s2 fun σ hσ => h1 _ (by have := b1 σ hσ; have := (chain_facts ν hσ).2.1; omega)
  · exact congrArg₂ (· + ·) (s2 fun σ hσ => h2 _ _ (by
        have := b1 σ hσ; have := (chain_facts ν hσ).2.1; omega))
      (s2 fun σ hσ => h2 _ _ (by have := b3 σ hσ; omega))
  · exact congrArg₂ (· + ·) (s2 fun σ hσ => h1 _ (by have := b1 σ hσ; have := lastB_lt ν hσ; omega))
      (sv fun a ha => h2 _ _ (by have := b4 a ha; omega))
  · exact congrArg₂ (· + ·) (sv fun v hv => h1 _ (by have := b2 v hv; omega))
      (sv fun a ha => h1 _ (by have := b4 a ha; simp only [N4c.cAB]; omega))
  · exact sv fun v hv => h1 _ (by have := b2 v hv; omega)
  · exact congrArg₂ (· + ·) (sv fun v hv => h1 _ (by have := b2 v hv; omega))
      (s2 fun σ hσ => sv fun t ht => h1 _ (by have := b3 σ hσ; omega))
  · exact s2 fun σ hσ => h2 _ _ (by have := b3 σ hσ; omega)
  · exact s2 fun σ hσ => h1 _ (by have := b3 σ hσ; omega)
  · exact s2 fun σ hσ => h1 _ (by have := b3 σ hσ; omega)
  · exact s2 fun σ hσ => sv fun t ht => h1 _ (by have := b3 σ hσ; omega)

/-- **The final blocks' bits depend only on the blocks below `hEnd`.** -/
theorem finG_congr (ν : NodeKind) {pt pt' : ℕ → F} (h1 : ∀ x < N4c.hEnd ν, pt x = pt' x) (j : ℕ) :
    finG ν pt j = finG ν pt' j := by
  obtain ⟨b1, -, -, b4, -⟩ := lay_bounds ν
  simp only [finG, sumTo_eq]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun σ hσ => ?_)
    (Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun i hi => ?_)
  · have h := Finset.mem_range.1 hσ
    rw [h1 _ (by have := b1 σ h; have := lastB_lt ν h; omega)]
  · rw [h1 _ (by have := b4 a (Finset.mem_range.1 ha); have := Finset.mem_range.1 hi; omega)]

/-- **The step fields depend only on the WOTS runs' blocks.** -/
theorem stepG_congr (ν : NodeKind) {pt pt' : ℕ → F} (h1 : ∀ x < N4c.hEnd ν, pt x = pt' x)
    (sel : ℕ → ℕ) (b : ℕ) : stepG ν pt sel b = stepG ν pt' sel b := by
  obtain ⟨-, -, b3, -, -⟩ := lay_bounds ν
  simp only [stepG, sumTo_eq]
  refine Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun o ho => ?_
  rw [h1 _ (by have := b3 σ (Finset.mem_range.1 hσ); have := Finset.mem_range.1 ho; omega)]

end NT4C
end FR
