import LvmKSpongeDigests
import LvmBits
import RecursionFast.Contract.Signature
import Mathlib.Tactic.IntervalCases
import LvmQSigPre
import LvmQSigHdr
import LvmKSponge

-- ===== merged from `LvmWotsSel` (GOLF module merge: `LvmWotsSel.lean` is now a stub importing `LvmQSigDefs`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRWots.lean@8bff272b (the digest-level
-- selections `wots_chain_sound`, `sigRoot_bits`, `wots_sound`, verbatim; namespace renamed);
-- the digit-from-bits and checksum lemmas are new (WP-12).

/-!
# WOTS at the digest level: chains, path, digits, checksum

* From FR (`FRWots`, hash-agnostic, verbatim): **`wots_chain_sound`** (three steps whose inputs
  are selected by `[d < s − 1]` give the contract's chain from the signed value at position `d`),
  **`sigRoot_bits`** (the path walk with the index's bits is `sigRoot`), **`wots_sound`** (chain
  ends, the leaf of those ends and a walk reaching `vk` give `SigOk vk m σ`).
* New: **`msgDigit_bits`**: digit `i < 128` of a digest is bit `2i` plus twice bit `2i + 1` of the
  digest read as 256 little-endian bits; **`checksum_bits`**: if `x^{Σ (3 − dᵢ)}` equals
  `x^{Σ_k 2^k c_k}` for ten Boolean `c_k` (and powers of `x` are injective below `2^10`), the five
  checksum digits of `wotsDigits` are the bit pairs `c_{2t} + 2 c_{2t+1}`.
-/

set_option autoImplicit false

namespace Lvm.Wots
open RecursionFast

/-- **One chain** (§4.2): steps `s = 1, 2, 3` from position `s − 1`; step `s`'s input is the
previous step's output when `d < s − 1`, else the signed value `ots`; the end is step 3's output
when `d < 3`, else `ots`. The end is the contract's chain from `ots` at position `d` to `3`. -/
theorem wots_chain_sound {j i d : ℕ} (hd : d ≤ 3) {ots e : Digest} {a out : ℕ → Digest}
    (hstep : ∀ s, 1 ≤ s → s ≤ 3 → out s = wotsStep j i (s - 1) (a s))
    (hsel : ∀ s, 1 ≤ s → s ≤ 3 → a s = if d + 1 < s then out (s - 1) else ots)
    (hend : e = if d < 3 then out 3 else ots) :
    e = wotsChain j i d (3 - d) ots := by
  have o1 : out 1 = wotsStep j i 0 (a 1) := hstep 1 (Nat.le_refl 1) (by decide)
  have o2 : out 2 = wotsStep j i 1 (a 2) := hstep 2 (by decide) (by decide)
  have o3 : out 3 = wotsStep j i 2 (a 3) := hstep 3 (by decide) (Nat.le_refl 3)
  have a1 : a 1 = if d + 1 < 1 then out 0 else ots := hsel 1 (Nat.le_refl 1) (by decide)
  have a2 : a 2 = if d + 1 < 2 then out 1 else ots := hsel 2 (by decide) (by decide)
  have a3 : a 3 = if d + 1 < 3 then out 2 else ots := hsel 3 (by decide) (Nat.le_refl 3)
  subst hend
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl
  · rw [if_pos (by decide), o3, a3, if_pos (by decide), o2, a2, if_pos (by decide), o1, a1, if_neg (by decide)]; rfl
  · rw [if_pos (by decide), o3, a3, if_pos (by decide), o2, a2, if_neg (by decide)]; rfl
  · rw [if_pos (by decide), o3, a3, if_neg (by decide)]; rfl
  · rw [if_neg (by decide)]; rfl

/-- **The path walk** (§4.2): `cur (t + 1) = sigNode l r` with `(l, r)` ordered by bit `t` of the
index is the contract's `sigRoot`. -/
theorem sigRoot_bits (cur : ℕ → Digest) : ∀ (path : List Digest) (j t0 : ℕ),
    (∀ t (ht : t < path.length), cur (t0 + t + 1) =
      if j / 2 ^ t % 2 = 0 then sigNode (cur (t0 + t)) path[t] else sigNode path[t] (cur (t0 + t))) →
    sigRoot j (cur t0) path = cur (t0 + path.length)
  | [], _, _, _ => rfl
  | s :: p, j, t0, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero, List.getElem_cons_zero] at h0
    rw [sigRoot, ← h0, sigRoot_bits cur p (j / 2) (t0 + 1) fun t ht => ?_]
    · simp [Nat.add_assoc, Nat.add_comm 1]
    · have := h (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul] at this
      rw [show t0 + 1 + t + 1 = t0 + (t + 1) + 1 by (clear * -; omega), this,
        show t0 + (t + 1) = t0 + 1 + t by (clear * -; omega), Nat.div_div_eq_div_mul, Nat.mul_comm,
        ← Nat.div_div_eq_div_mul]

theorem msgDigits_length (m : Digest) : (msgDigits m).length = 128 := by
  simp [msgDigits, List.length_flatMap]

theorem wotsDigits_length (m : Digest) : (wotsDigits m).length = wotsLen := by
  simp [wotsDigits, msgDigits_length, wotsLen]

/-- **`wots_sound`** (§4.2): chain ends that are the contract's chains from the signed values at
the message's digits, the leaf of those ends, and a walk along the path with the index's bits that
reaches `vk`, give the contract's `SigOk`. -/
theorem wots_sound {vk m : Digest} {σ : Sig} (hidx : σ.idx < 2 ^ sigHeight)
    (hots : σ.ots.length = wotsLen) (hpath : σ.path.length = sigHeight) {ends : List Digest}
    (hlen : ends.length = wotsLen)
    (hends : ∀ i (hi : i < wotsLen), ends[i]'(hlen ▸ hi) =
      wotsChain σ.idx i ((wotsDigits m)[i]'(by rw [wotsDigits_length]; exact hi))
        (3 - (wotsDigits m)[i]'(by rw [wotsDigits_length]; exact hi)) (σ.ots[i]'(hots ▸ hi)))
    {cur : ℕ → Digest} (hleaf : cur 0 = wotsLeaf σ.idx ends)
    (hwalk : ∀ t (ht : t < σ.path.length), cur (t + 1) = if σ.idx / 2 ^ t % 2 = 0
      then sigNode (cur t) σ.path[t] else sigNode σ.path[t] (cur t))
    (hroot : cur sigHeight = vk) : SigOk vk m σ = true := by
  have hE : wotsEnds σ.idx m σ.ots = ends := by
    apply List.ext_getElem (by simp [wotsEnds, wotsDigits_length, hots, hlen])
    intro i h1 h2
    simp only [wotsEnds, List.getElem_mapIdx, List.getElem_zip]
    exact (hends i (hlen ▸ h2)).symm
  have hr := sigRoot_bits cur σ.path σ.idx 0 fun t ht => by simpa using hwalk t ht
  simp only [SigOk, hidx, hots, hpath, decide_true, Bool.true_and, decide_eq_true_eq, hE,
    ← hleaf, hr, Nat.zero_add, hroot]

/-! ## Digits from bits (new) -/

theorem flatMap4_getElem {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length = 4) :
    ∀ (l : List α) (q r : ℕ) (hq : q < l.length) (hr : r < 4) (h : 4 * q + r < (l.flatMap f).length),
      (l.flatMap f)[4 * q + r] = (f l[q])[r]'(by rw [hf]; exact hr)
  | [], _, _, hq, _, _ => absurd hq (by simp)
  | a :: l, q, r, hq, hr, h => by
    simp only [List.flatMap_cons] at h ⊢
    cases q with
    | zero =>
      rw [List.getElem_append_left (by rw [hf]; (clear * - hr; omega))]; simp
    | succ q =>
      rw [List.getElem_append_right (by rw [hf]; (clear * - hr; omega))]
      have := flatMap4_getElem f hf l q r (by simpa using hq) hr
        (by simp only [List.length_append, hf] at h; (clear * - h; omega))
      simp only [hf, show 4 * (q + 1) + r - 4 = 4 * q + r by (clear * - hr; omega), this, List.getElem_cons_succ]

theorem msgDigits_getElem (m : Digest) {i : ℕ} (hi : i < 128) :
    (msgDigits m)[i]'(by rw [msgDigits_length]; exact hi) = m[i / 4].toNat / 4 ^ (i % 4) % 4 := by
  have h := flatMap4_getElem (fun b : UInt8 => (List.range 4).map fun t => b.toNat / 4 ^ t % 4)
    (by simp) m.toList (i / 4) (i % 4) (by simp; omega) (Nat.mod_lt _ (by norm_num))
    (by rw [show 4 * (i / 4) + i % 4 = i by omega]; simpa [msgDigits_length, msgDigits] using hi)
  simp only [show 4 * (i / 4) + i % 4 = i by omega] at h
  simp only [msgDigits, h, List.getElem_map, List.getElem_range, Vector.getElem_toList]

/-- A base-4 digit of a number is two of its bits. -/
theorem div_four_pow_mod (n u : ℕ) :
    n / 4 ^ u % 4 = (n.testBit (2 * u)).toNat + 2 * (n.testBit (2 * u + 1)).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    show 4 ^ u = 2 ^ (2 * u) by rw [pow_mul]; norm_num, pow_succ, ← Nat.div_div_eq_div_mul]
  generalize n / 2 ^ (2 * u) = q
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one (q / 2) with h' | h' <;> simp [h, h'] <;> omega

theorem testBit_byte (b : UInt8) (j : ℕ) : b.toNat.testBit j = Bits.bbit b j := rfl

/-- **Digit `i` of a message from its bits**: with byte `k` of `m` the byte `k % 8` of lane
`k / 8` of `w`, digit `i < 128` is bit `2i` plus twice bit `2i + 1` of the lanes. -/
theorem msgDigit_bits (m : Digest) (w : ℕ → UInt64)
    (hm : ∀ k (hk : k < 32), m[k] = Bits.byteW (w (k / 8)) (k % 8)) {i : ℕ} (hi : i < 128) :
    (msgDigits m)[i]'(by rw [msgDigits_length]; exact hi) =
      (Bits.ubit (w (i / 32)) (2 * i % 64)).toNat + 2 * (Bits.ubit (w (i / 32)) (2 * i % 64 + 1)).toNat := by
  rw [msgDigits_getElem m hi, hm _ (by omega), div_four_pow_mod, testBit_byte, testBit_byte,
    Bits.bbit_byteW _ (by omega) (by omega), Bits.bbit_byteW _ (by omega) (by omega)]
  rw [show i / 4 / 8 = i / 32 by omega, show 8 * (i / 4 % 8) + 2 * (i % 4) = 2 * i % 64 by omega,
    show 8 * (i / 4 % 8) + (2 * (i % 4) + 1) = 2 * i % 64 + 1 by omega]

/-! ## The checksum (new) -/

/-- `Σ_k 2^k c_k` over the first `n` Boolean `c`. -/
def bitsVal (c : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if c n then 2 ^ n else 0) + bitsVal c n

theorem bitsVal_lt (c : ℕ → Bool) : ∀ n, bitsVal c n < 2 ^ n
  | 0 => by simp [bitsVal]
  | n + 1 => by
    have := bitsVal_lt c n
    rw [bitsVal, pow_succ]; split <;> omega

theorem bitsVal_testBit (c : ℕ → Bool) : ∀ n, ∀ k < n, (bitsVal c n).testBit k = c k
  | 0, k, hk => absurd hk (by omega)
  | n + 1, k, hk => by
    have hlt := bitsVal_lt c n
    rw [bitsVal]
    rcases Nat.lt_or_ge k n with h | h
    · rw [← bitsVal_testBit c n k h]
      split
      · exact Nat.testBit_two_pow_add_gt h _
      · rw [Nat.zero_add]
    · obtain rfl : k = n := by (clear * - hk h; omega)
      split
      · rename_i hc; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hc]; rfl
      · rename_i hc; rw [Nat.zero_add, Nat.testBit_lt_two_pow hlt]; simpa using hc

/-- **The checksum digits from bits**: if the checksum `C = Σ (3 − dᵢ)` of the message digits
equals `Σ_k 2^k c_k` over ten bits, the checksum digit `t < 5` is `c_{2t} + 2 c_{2t+1}`. -/
theorem checksum_digit (m : Digest) (c : ℕ → Bool)
    (hC : ((msgDigits m).map (3 - ·)).sum = bitsVal c 10) {t : ℕ} (ht : t < 5) :
    (wotsDigits m)[128 + t]'(by rw [wotsDigits_length]; simp [wotsLen]; omega) =
      (c (2 * t)).toNat + 2 * (c (2 * t + 1)).toNat := by
  simp only [wotsDigits]
  rw [List.getElem_append_right (by rw [msgDigits_length]; omega)]
  simp only [msgDigits_length, List.getElem_map, List.getElem_range,
    show 128 + t - 128 = t by omega, hC, div_four_pow_mod]
  rw [bitsVal_testBit c 10 _ (by omega), bitsVal_testBit c 10 _ (by omega)]

theorem msgDigits_le (m : Digest) : ∀ d ∈ msgDigits m, d ≤ 3 := by
  intro d hd
  simp only [msgDigits, List.mem_flatMap, List.mem_map, List.mem_range] at hd
  obtain ⟨b, -, t, -, rfl⟩ := hd
  omega

theorem checksum_le (m : Digest) : ((msgDigits m).map (3 - ·)).sum ≤ 384 := by
  have : ∀ l : List ℕ, ((l.map (3 - ·)).sum ≤ 3 * l.length) := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [List.sum_cons]; omega
  have := this (msgDigits m)
  rw [msgDigits_length] at this; omega

/-- Powers of `x` with exponents `3 − d` multiply to `x^{Σ (3 − d)}`. -/
theorem prod_pow_sum (l : List ℕ) :
    (l.map fun d => FK.x ^ (3 - d)).prod = FK.x ^ (l.map (3 - ·)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, List.sum_cons, ih, pow_add]

/-- **The checksum equation**: from `x^{Σ (3 − dᵢ)} = x^{Σ 2^k c_k}` with exponents below the
injectivity bound. -/
theorem checksum_of_pow (m : Digest) (c : ℕ → Bool)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    (h : FK.x ^ ((msgDigits m).map (3 - ·)).sum = FK.x ^ bitsVal c 10) :
    ((msgDigits m).map (3 - ·)).sum = bitsVal c 10 :=
  hinj _ _ (by have := checksum_le m; omega) (by have := bitsVal_lt c 10; simpa using this) h

end Lvm.Wots
end
-- ===== end of `LvmWotsSel` =====

-- ===== merged from `LvmQSigCheck` (GOLF module merge: `LvmQSigCheck.lean` is now a stub importing `LvmQSigDefs`) =====
section

/-!
# `Q_sig`: the WOTS checksum, multiplicatively

New for lvm (WP-12; FR `FRNodeRows4Wots`'s `sumRows` idea: the checksum as a product of powers of
a generator, no integer arithmetic). `gCheck_spec`: in every memory where `gCheck`'s rows and its
assertion hold (gate `1`), with Boolean digit bits, `x^{Σ_{i<128} (3 − dᵢ)} = x^{Σ_k 2^k c_k}`.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Wots

/-- A product over a range, pairs folded. -/
theorem prod_pairs (A : Nat → FK) : ∀ n,
    ((List.range (2 * n)).map A).prod = ((List.range n).map fun y => A (2 * y) * A (2 * y + 1)).prod
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, List.range_succ,
      List.map_append, List.map_append, List.map_append, List.prod_append, List.prod_append,
      List.prod_append, prod_pairs A n]
    simp [mul_assoc]

theorem bnat_le (b : FK) : bnat b ≤ 1 := by unfold bnat; split <;> omega

/-- **The checksum factor**: `(Z + (x+1)·b₀ + x)·(Z + (x²+1)·b₁ + x²) = x^{3 − d}`. -/
theorem factor_eq {b0 b1 : FK} (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) :
    (0 + (FK.x + 1) * b0 + FK.x) * (0 + (FK.x ^ 2 + 1) * b1 + FK.x ^ 2) + 0 =
      FK.x ^ (3 - (bnat b0 + 2 * bnat b1)) := by
  have h01 : ¬ ((0 : FK) = 1) := by decide
  have h2 : (2 : FK) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : FK) = 0 := by rw [show (4 : FK) = 2 * 2 by norm_num, h2, zero_mul]
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;>
    simp [bnat, h01] <;> ring_nf <;> simp [h2, h4]

/-- **A product-tree level**: output `y` is `a[2y]·a[2y+1]`. -/
theorem pt_spec {c : Ctx} {M : Mem} {d src st Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d] (ptTpl src st Zn) p).2) (hZ : M.k Zn = 0) {y : Nat}
    (hy : y < 2 ^ d) :
    M.k (p.k + y) = M.k (src + 2 * st * y) * M.k (src + st + 2 * st * y) := by
  have r := loopK_mad h (by simpa using hy) (t := 0) (by simp [ptTpl]) rfl rfl rfl rfl
  rw [cell_lin1 _ 0 _ (by simp [loop_apply, ptTpl])
      (fun r hr => by simp [loop_apply, ptTpl] at hr; subst hr; simp),
    ov_oS _ _ rfl hy, ov_oS _ _ rfl hy, ov_oA, hZ, add_zero] at r
  simpa [loop_apply, ptTpl] using r

/-- The ten checksum bits as Booleans. -/
def cbit (M : Mem) (I : SigIn) (k : Nat) : Bool := decide (M.k (I.bc + k) = 1)

/-- `Σ_{j<n} 2^{k+j} c_{k+j}`. -/
def cexp (c : Nat → Bool) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if c k then 2 ^ k else 0) + cexp c (k + 1) n

theorem bitsVal_cexp (c : Nat → Bool) : ∀ n k, bitsVal c (k + n) = bitsVal c k + cexp c k n
  | 0, k => by simp [cexp]
  | n + 1, k => by
    rw [show k + (n + 1) = (k + 1) + n by omega, bitsVal_cexp c n (k + 1), cexp, bitsVal]
    ring

/-- **The bit factors' product.** -/
theorem cbitsGo_spec {c : Ctx} {M : Mem} {I : SigIn} {Z : Cell} (hZt : Z.ty = .K)
    (hZ : M.k Z.n = 0) (hb : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1) :
    ∀ n k (acc : Cell) (p : Ptr), acc.ty = .K → k + n ≤ 10 →
      SegsHold c M p (cbitsGo I Z k n acc p).2 →
      (cbitsGo I Z k n acc p).1.ty = .K ∧
        M.k (cbitsGo I Z k n acc p).1.n = M.k acc.n * FK.x ^ cexp (cbit M I) k n
  | 0, k, acc, p, ht, _, _ => by simp [cbitsGo, pure_apply, cexp, ht]
  | n + 1, k, acc, p, ht, hkn, h => by
    unfold cbitsGo at h ⊢
    refine seqH (Q := fun r : Cell => r.ty = .K ∧ M.k r.n = M.k acc.n * FK.x ^ cexp (cbit M I) k (n + 1))
      h fun hg p1 h => ?_
    obtain ⟨Zt, Zn⟩ := Z
    simp only at hZt; subst hZt
    have eg := linK_spec hg
    have tg : (lin .K (FK.x ^ 2 ^ k + 1) 1 ⟨.K, Zn⟩ (kc (I.bc + k)) p).1 = kc p.k := rfl
    rw [tg]
    refine seqH (Q := fun r : Cell => r.ty = .K ∧ M.k r.n = M.k acc.n * FK.x ^ cexp (cbit M I) k (n + 1))
      h fun ha p2 h => ?_
    obtain ⟨At, An⟩ := acc
    simp only at ht; subst ht
    have ea := mulAddK_spec ha
    have ta : (mad ⟨.K, An⟩ (kc p.k) ⟨.K, Zn⟩ p1).1 = kc p1.k := rfl
    rw [ta]
    obtain ⟨t1, e1⟩ := cbitsGo_spec rfl hZ hb n (k + 1) (kc p1.k) p2 rfl (by (clear * - hkn; omega)) h
    refine ⟨t1, ?_⟩
    rw [e1, ea, eg, hZ, add_zero]
    simp only [cexp, pow_add, cbit]
    have h2 : (2 : FK) = 0 := CharTwo.two_eq_zero
    rcases hb k (by (clear * - hkn; omega)) with e | e <;> simp [e, show ¬ ((0 : FK) = 1) from by decide] <;> ring_nf <;>
      simp [h2]

theorem cell_eta {c : Cell} (h : c.ty = .K) : c = kc c.n := by
  cases c; simp only at h; subst h; rfl

/-- A product-tree level's product. -/
theorem prod_level (A B : Nat → FK) (n : Nat) (h : ∀ y < n, B y = A (2 * y) * A (2 * y + 1)) :
    ((List.range n).map B).prod = ((List.range (2 * n)).map A).prod := by
  rw [prod_pairs]
  congr 1
  exact List.map_congr_left fun y hy => h y (List.mem_range.mp hy)

/-- The digits of the message chains, from the digit bit cells. -/
def mdig (M : Mem) (I : SigIn) (i : Nat) : Nat := bnat (M.k (I.bd + 2 * i)) + 2 * bnat (M.k (I.bd + 2 * i + 1))

/-- A product-tree level at `p` with stride 1 from `src`. -/
theorem pt_level {c : Ctx} {M : Mem} {d src Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d] (ptTpl src 1 Zn) p).2) (hZ : M.k Zn = 0) {e : Nat} (he : e = d + 1)
    (A : Nat → FK) (hA : ∀ i < 2 ^ e, M.k (src + i) = A i) :
    ((List.range (2 ^ d)).map fun y => M.k (p.k + y)).prod = ((List.range (2 ^ e)).map A).prod := by
  subst he
  rw [pow_succ, mul_comm]
  apply prod_level
  intro y hy
  rw [pt_spec h hZ hy, ← hA _ (by (clear * - hy; omega)), ← hA _ (by (clear * - hy; omega))]
  congr 2 <;> ring

/-- **The checksum gadget**: `x^{Σ_{i<128} (3 − dᵢ)} = x^{Σ_k 2^k c_k}`. -/
theorem gCheck_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Z O : Cell} (hZt : Z.ty = .K)
    (hOt : O.ty = .K) (h : SegsHold c M p (gCheck I Z O p).2) (hA : SegsAssert M p (gCheck I Z O p).2)
    (hg : M.k I.flag = 1) (hZ : M.k Z.n = 0) (hO : M.k O.n = 1)
    (hbd : ∀ q < 256, M.k (I.bd + q) = 0 ∨ M.k (I.bd + q) = 1)
    (hbc : ∀ k < 10, M.k (I.bc + k) = 0 ∨ M.k (I.bc + k) = 1) :
    FK.x ^ ((List.range 128).map fun i => 3 - mdig M I i).sum = FK.x ^ bitsVal (cbit M I) 10 := by
  obtain ⟨Zt, Zn⟩ := Z
  simp only at hZt hZ; subst hZt
  obtain ⟨Ot, On⟩ := O
  simp only at hOt hO; subst hOt
  let T : Prop := FK.x ^ ((List.range 128).map fun i => 3 - mdig M I i).sum = FK.x ^ bitsVal (cbit M I) 10
  unfold gCheck at h hA
  refine seqHA (Q := fun _ => T) h hA fun hcs _ p1 h hA => ?_
  -- the factors
  have hP : ∀ i < 128, M.k ((loop [7] (csfTpl I Zn) p).1.p.k + 2 + 3 * i) =
      FK.x ^ (3 - mdig M I i) := by
    intro i hi
    have hi' : i < 2 ^ [7].sum := by simpa using hi
    have r0 := loopK_lin hcs hi' (t := 0) (by simp [csfTpl]) rfl rfl rfl
    have r1 := loopK_lin hcs hi' (t := 1) (by simp [csfTpl]) rfl rfl rfl
    have r2 := loopK_mad hcs hi' (t := 2) (by simp [csfTpl]) rfl rfl rfl rfl
    have hc : ∀ t < 3, ((loop [7] (csfTpl I Zn) p).1.cell t i).n = p.k + t + 3 * i := fun t ht =>
      cell_lin1 _ t i (by simpa [loop_apply, csfTpl] using ht)
        (fun r hr => by simp [loop_apply, csfTpl] at hr; rcases hr with rfl | rfl | rfl <;> simp)
    rw [ov_oA, ov_oS _ _ rfl (by simpa using hi), hZ] at r0 r1
    rw [ov_cur _ _ hi' 0 rfl, ov_cur _ _ hi' 1 rfl, ov_oA, hZ, r0, r1] at r2
    rw [hc 2 (by (clear * -; omega))] at r2
    show M.k (p.k + 2 + 3 * i) = _
    have hb1 : M.k (I.bd + 2 * i + 1) = 0 ∨ M.k (I.bd + 2 * i + 1) = 1 := by
      rw [Nat.add_assoc]; exact hbd _ (by (clear * - hi; omega))
    rw [r2, show I.bd + 1 + 2 * i = I.bd + 2 * i + 1 by ring,
      factor_eq (hbd _ (by (clear * - hi; omega))) hb1]
    rfl
  generalize loop [7] (csfTpl I Zn) p = rcs at hP h hA ⊢
  -- the tree
  refine seqHA (Q := fun _ => T) h hA fun h6 _ p2 h hA => ?_
  have q6 : ((List.range (2 ^ 6)).map fun y => M.k ((loop [6] (ptTpl (rcs.1.p.k + 2) 3 Zn) p1).1.p.k + y)).prod
      = ((List.range 128).map fun i => FK.x ^ (3 - mdig M I i)).prod := by
    show ((List.range (2 ^ 6)).map fun y => M.k (p1.k + y)).prod = _
    rw [show (128 : Nat) = 2 * 2 ^ 6 by norm_num]
    apply prod_level
    intro y hy
    rw [pt_spec h6 hZ hy, ← hP _ (by (clear * - hy; omega)), ← hP _ (by (clear * - hy; omega))]
    congr 2 <;> ring
  generalize loop [6] (ptTpl (rcs.1.p.k + 2) 3 Zn) p1 = r6 at q6 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h5 _ p3 h hA => ?_
  have q5 := pt_level h5 hZ (e := 6) rfl _ fun i _ => rfl
  rw [q6] at q5
  replace q5 : ((List.range (2 ^ 5)).map fun y =>
      M.k ((loop [5] (ptTpl r6.1.p.k 1 Zn) p2).1.p.k + y)).prod = _ := q5
  generalize loop [5] (ptTpl r6.1.p.k 1 Zn) p2 = r5 at q5 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h4 _ p4 h hA => ?_
  have q4 := pt_level h4 hZ (e := 5) rfl _ fun i _ => rfl
  rw [q5] at q4
  replace q4 : ((List.range (2 ^ 4)).map fun y =>
      M.k ((loop [4] (ptTpl r5.1.p.k 1 Zn) p3).1.p.k + y)).prod = _ := q4
  generalize loop [4] (ptTpl r5.1.p.k 1 Zn) p3 = r4 at q4 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h3 _ p5 h hA => ?_
  have q3 := pt_level h3 hZ (e := 4) rfl _ fun i _ => rfl
  rw [q4] at q3
  replace q3 : ((List.range (2 ^ 3)).map fun y =>
      M.k ((loop [3] (ptTpl r4.1.p.k 1 Zn) p4).1.p.k + y)).prod = _ := q3
  generalize loop [3] (ptTpl r4.1.p.k 1 Zn) p4 = r3 at q3 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h2 _ p6 h hA => ?_
  have q2 := pt_level h2 hZ (e := 3) rfl _ fun i _ => rfl
  rw [q3] at q2
  replace q2 : ((List.range (2 ^ 2)).map fun y =>
      M.k ((loop [2] (ptTpl r3.1.p.k 1 Zn) p5).1.p.k + y)).prod = _ := q2
  generalize loop [2] (ptTpl r3.1.p.k 1 Zn) p5 = r2 at q2 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h1 _ p7 h hA => ?_
  have q1 := pt_level h1 hZ (e := 2) rfl _ fun i _ => rfl
  rw [q2] at q1
  replace q1 : ((List.range (2 ^ 1)).map fun y =>
      M.k ((loop [1] (ptTpl r2.1.p.k 1 Zn) p6).1.p.k + y)).prod = _ := q1
  generalize loop [1] (ptTpl r2.1.p.k 1 Zn) p6 = r1 at q1 h hA ⊢
  refine seqHA (Q := fun _ => T) h hA fun h0 _ p8 h hA => ?_
  have q0 := pt_level h0 hZ (e := 1) rfl _ fun i _ => rfl
  rw [q1] at q0
  have c0 : (loop [0] (ptTpl r1.1.p.k 1 Zn) p7).1.cell 0 0 = kc p7.k := by
    simp [loop_apply, LoopOut.cell, ptTpl, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at]
  rw [c0] at h hA
  generalize loop [0] (ptTpl r1.1.p.k 1 Zn) p7 = r0 at q0 h hA ⊢
  -- the bit side
  refine seqHA (Q := fun _ => T) h hA fun hq _ p9 h hA => ?_
  obtain ⟨tq, eq⟩ := cbitsGo_spec (Z := ⟨.K, Zn⟩) rfl hZ hbc 10 0 ⟨.K, On⟩ p8 rfl (by (clear * -; omega)) hq
  have ecq : (cbits I ⟨.K, Zn⟩ ⟨.K, On⟩ p8).1 = kc (cbits I ⟨.K, Zn⟩ ⟨.K, On⟩ p8).1.n :=
    cell_eta tq
  have eq' : M.k (cbits I ⟨.K, Zn⟩ ⟨.K, On⟩ p8).1.n = FK.x ^ bitsVal (cbit M I) 10 := by
    show M.k (cbitsGo I ⟨.K, Zn⟩ 0 10 ⟨.K, On⟩ p8).1.n = _
    rw [eq, hO, one_mul, show bitsVal (cbit M I) 10 = bitsVal (cbit M I) (0 + 10) from rfl,
      bitsVal_cexp]
    simp [bitsVal]
  beta_reduce at h hA
  rw [ecq] at h hA
  rw [hold_bind] at h
  rw [assert_bind] at hA
  have heq := assertEqKK_spec h.1 hA.1 hg
  rw [eq'] at heq
  simp only [pow_zero, pow_one, List.range_one, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Nat.add_zero] at q0
  show FK.x ^ ((List.range 128).map fun i => 3 - mdig M I i).sum = _
  rw [← heq, q0]
  have := prod_pow_sum ((List.range 128).map (mdig M I))
  simp only [List.map_map] at this
  exact this.symm

end Lvm.QSig
end
-- ===== end of `LvmQSigCheck` =====

-- ===== merged from `LvmQSigMsg` (GOLF module merge: `LvmQSigMsg.lean` is now a stub importing `LvmQSigDefs`) =====
section

/-!
# `Q_sig`: the message lanes as words

New for lvm (WP-12). For each message template of `LvmQSig`, in every memory where its rows hold
(and the zero cell is `0`), the lanes' words (`(M.k _).val`) are the `XOR`s of the operand words
and constants that `LvmWotsMsg`'s layout lemmas take as hypotheses.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The word of a cell. -/
abbrev V (M : Mem) (a : Nat) : UInt64 := (M.k a).val

/-- The word of an operand at an iteration. -/
abbrev OV (M : Mem) (o : LoopOut) (jf : Nat) (x : Opd) : UInt64 := (ov M o jf x).val

section lanes

variable {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr} {jf t : Nat}

theorem lane1 (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {k' : FK} {a b : Opd} (hr : tpl.getD t default = lr 1 k' a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x y z : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) (hy : OV M (loop dims tpl p).1 jf b = y)
    (hz : k'.val = z) : V M ((loop dims tpl p).1.cell t jf).n = x ^^^ y ^^^ z := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, one_mul, ← hx, ← hy, ← hz]; rfl

theorem lane1z (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {a b : Opd} (hr : tpl.getD t default = lr 1 0 a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x y : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) (hy : OV M (loop dims tpl p).1 jf b = y) :
    V M ((loop dims tpl p).1.cell t jf).n = x ^^^ y := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, one_mul, add_zero, ← hx, ← hy]; rfl

theorem lane0 (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {k' : FK} {a b : Opd} (hr : tpl.getD t default = lr 0 k' a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x z : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) (hz : k'.val = z) :
    V M ((loop dims tpl p).1.cell t jf).n = x ^^^ z := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, zero_mul, add_zero, ← hx, ← hz]; rfl

theorem lane00 (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {a b : Opd} (hr : tpl.getD t default = lr 0 0 a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) {x : UInt64}
    (hx : OV M (loop dims tpl p).1 jf a = x) : V M ((loop dims tpl p).1.cell t jf).n = x := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr ha hb, zero_mul, add_zero, add_zero, ← hx]

theorem laneZ {Zn : Nat} (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) (hr : tpl.getD t default = lr 0 0 (oA Zn) (oA Zn)) (hZ : M.k Zn = 0) :
    V M ((loop dims tpl p).1.cell t jf).n = 0 := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr rfl rfl, ov_oA, hZ, zero_mul, add_zero, add_zero]; rfl

theorem lanePad {Zn : Nat} (h : SegsHold c M p (loop dims tpl p).2) (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) (hr : tpl.getD t default = padLane Zn) (hZ : M.k Zn = 0) :
    V M ((loop dims tpl p).1.cell t jf).n = 0x8000000000000000 := by
  show (M.k ((loop dims tpl p).1.cell t jf).n).val = _
  rw [loopK_lin h hjf ht hr rfl rfl, ov_oA, hZ, zero_mul, add_zero, zero_add]

end lanes

theorem ovS_V {M : Mem} {o : LoopOut} {d jf n s n2 : Nat} (hd : o.dims = [d]) (hjf : jf < 2 ^ d)
    (h : n + s * jf = n2) : OV M o jf (oS n s) = V M n2 := by
  subst h; simp only [OV, V, ov_oS M o hd hjf]

/-- **A chain step's lanes** (template `stepsTpl`, step `s < 3`, lanes `17 s + l`). -/
theorem steps_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn} {Zn : Nat} {T : Opd}
    {c1 : Nat → UInt64} {xb st : Nat}
    (h : SegsHold c M p (loop dims (stepsTpl I Zn T c1 xb st) p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) (hT : OpdK (loop dims (stepsTpl I Zn T c1 xb st) p).1 T)
    (hZ : M.k Zn = 0) {s : Nat} (hs : s < 3) :
    let o := (loop dims (stepsTpl I Zn T c1 xb st) p).1
    let L := fun l => V M (o.cell (17 * s + l) jf).n
    let X := fun k => OV M o jf (oS (xb + 8 * s + k) st)
    L 0 = V M I.bi ^^^ 0x57 ∧ L 1 = (OV M o jf T ^^^ X 0) ^^^ c1 s ∧
      (∀ k, 1 ≤ k → k < 4 → L (k + 1) = X (2 * k - 1) ^^^ X (2 * k)) ∧
      L 5 = X 7 ^^^ 0x1000000 ∧ (∀ l, 6 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  have hlen : (stepsTpl I Zn T c1 xb st).length = 51 := by simp [stepsTpl, stepLanes, zeroLanes]
  refine ⟨?_, ?_, fun k hk1 hk2 => ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · interval_cases s <;> apply lane0 h hjf <;>
      first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases s <;> apply lane1 h hjf <;>
      first | (rw [hlen]; (clear * -; omega)) | rfl | assumption
  · interval_cases s <;> interval_cases k <;> apply lane1z h hjf <;>
      first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases s <;> apply lane0 h hjf <;>
      first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases s <;> interval_cases l <;> apply laneZ h hjf (hZ := hZ) <;>
      first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases s <;> apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl

/-- **Two digests after a tag** (template `twoLanes`). -/
theorem two_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {Zn : Nat} {tag : UInt64}
    {aB bB st : Nat} (h : SegsHold c M p (loop dims (twoLanes Zn tag aB bB st) p).2) {jf : Nat}
    (hjf : jf < 2 ^ dims.sum) (hZ : M.k Zn = 0) :
    let o := (loop dims (twoLanes Zn tag aB bB st) p).1
    let L := fun l => V M (o.cell l jf).n
    let A := fun k => OV M o jf (oS (aB + k) st)
    let B := fun k => OV M o jf (oS (bB + k) st)
    L 0 = A 0 ^^^ tag ∧ (∀ k, 1 ≤ k → k < 4 → L k = A (2 * k - 1) ^^^ A (2 * k)) ∧
      L 4 = A 7 ^^^ B 0 ∧ (∀ k, 1 ≤ k → k < 4 → L (4 + k) = B (2 * k - 1) ^^^ B (2 * k)) ∧
      L 8 = B 7 ^^^ 0x100 ∧ (∀ l, 9 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  have hlen : (twoLanes Zn tag aB bB st).length = 17 := by simp [twoLanes, zeroLanes]
  refine ⟨?_, fun k hk1 hk2 => ?_, ?_, fun k hk1 hk2 => ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · apply lane0 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lane1z h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lane0 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases l <;> apply laneZ h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl

/-- **`leafStmt`'s lanes** (template `leafStmtLanes`). -/
theorem leafStmt_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn} {Zn : Nat}
    (h : SegsHold c M p (loop dims (leafStmtLanes I Zn) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hZ : M.k Zn = 0) :
    let o := (loop dims (leafStmtLanes I Zn) p).1
    let L := fun l => V M (o.cell l jf).n
    L 0 = V M I.bh ^^^ 0x4C ∧ (∀ k, 1 ≤ k → k < 4 → L k = V M (I.bh + 2 * k - 1) ^^^ V M (I.bh + 2 * k)) ∧
      L 4 = V M (I.bh + 7) ^^^ V M I.bn ∧ L 5 = V M (I.bn + 1) ^^^ 0x100 ∧
      (∀ l, 6 ≤ l → l < 16 → L l = 0) ∧ L 16 = 0x8000000000000000 := by
  dsimp only
  have hlen : (leafStmtLanes I Zn).length = 17 := by simp [leafStmtLanes, zeroLanes]
  refine ⟨?_, fun k hk1 hk2 => ?_, ?_, ?_, fun l hl1 hl2 => ?_, ?_⟩
  · apply lane0 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lane1z h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lane0 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases l <;> apply laneZ h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl

/-- **The key leaf's lanes 0, 1** (template `leafA`). -/
theorem leafA_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn}
    (h : SegsHold c M p (loop dims (leafA I) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    V M ((loop dims (leafA I) p).1.cell 0 jf).n = V M I.bi ^^^ 0x4B ∧
      V M ((loop dims (leafA I) p).1.cell 1 jf).n = V M I.be := by
  have hlen : (leafA I).length = 2 := rfl
  constructor
  · apply lane0 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lane00 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl

/-- **The key leaf's lanes `2 + m`** (template `leafB`, loop over `m < 512`). -/
theorem leafB_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn}
    (h : SegsHold c M p (loop [9] (leafB I) p).2) {m : Nat} (hm : m < 2 ^ 9) :
    V M ((loop [9] (leafB I) p).1.cell 0 m).n = V M (I.be + 2 * m + 1) ^^^ V M (I.be + 2 * (m + 1)) := by
  have hm' : m < 2 ^ [9].sum := by simpa using hm
  apply lane1z h hm' (by simp [leafB]) rfl
  · rfl
  · rfl
  · exact ovS_V rfl hm (by (clear * -; omega))
  · exact ovS_V rfl hm (by (clear * -; omega))

/-- **The key leaf's lanes 514 … 543** (template `leafC`, row `k` = lane `514 + k`). -/
theorem leafC_spec {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {I : SigIn} {Zn : Nat}
    (h : SegsHold c M p (loop dims (leafC I Zn) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hZ : M.k Zn = 0) :
    let L := fun k => V M ((loop dims (leafC I Zn) p).1.cell k jf).n
    (∀ k < 19, L k = V M (I.be + 2 * (512 + k) + 1) ^^^ V M (I.be + 2 * (513 + k))) ∧
      L 19 = V M (I.be + 2 * 531 + 1) ^^^ 0x100 ∧ (∀ k, 20 ≤ k → k < 29 → L k = 0) ∧
      L 29 = 0x8000000000000000 := by
  dsimp only
  have hlen : (leafC I Zn).length = 30 := by simp [leafC, zeroLanes]
  refine ⟨fun k hk => ?_, ?_, fun k hk1 hk2 => ?_, ?_⟩
  · interval_cases k <;> apply lane1z h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lane0 h hjf <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · interval_cases k <;> apply laneZ h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl
  · apply lanePad h hjf (hZ := hZ) <;> first | (rw [hlen]; (clear * -; omega)) | rfl

end Lvm.QSig
end
-- ===== end of `LvmQSigMsg` =====

-- ===== merged from `LvmQSigParts` (GOLF module merge: `LvmQSigParts.lean` is now a stub importing `LvmQSigDefs`) =====
section

/-!
# `Q_sig`: its parts

New for lvm (WP-12). `qsig_parts`, `gMsg_parts`: where `Q_sig`'s rows and assertions hold, every
part's rows and assertions hold at some pointer, and its output is the field of `Q_sig`'s output
that names it (the frame property of QL's builder: specs are pointer-generic).
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

theorem ok_bind' {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) :
    Ok c M m p ∧ Ok c M (f (m p).1) (p.adv (m p).2) ∧
      ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩, rfl⟩

/-- A default loop output (for `getD`). -/
def dLoop : LoopOut := ⟨⟨0, 0⟩, [], []⟩

theorem ok_seqAll_get {c : Ctx} {M : Mem} :
    ∀ (ms : List (BM LoopOut)) (p : Ptr), Ok c M (seqAll ms) p →
      ∀ u < ms.length, ∃ q, Ok c M (ms.getD u (pure dLoop)) q ∧
        (seqAll ms p).1.getD u dLoop = ((ms.getD u (pure dLoop)) q).1
  | [], _, _, u, hu => absurd hu (by simp)
  | m :: ms, p, h, u, hu => by
    obtain ⟨h1, h2⟩ := h
    rw [seqAll_cons_apply, segsHold_append, segsHold_append] at h1
    rw [seqAll_cons_apply, segsAssert_append, segsAssert_append] at h2
    cases u with
    | zero => exact ⟨p, ⟨h1.1, h2.1⟩, by simp [seqAll_cons_apply]⟩
    | succ u =>
      obtain ⟨q, hq, e⟩ := ok_seqAll_get ms _ ⟨h1.2.1, h2.2.1⟩ u (by simpa using hu)
      refine ⟨q, by simpa using hq, ?_⟩
      simp only [seqAll_cons_apply, List.getD_cons_succ]
      exact e

theorem ok_forN_get {c : Ctx} {M : Mem} {n : Nat} {f : Nat → BM LoopOut} {p : Ptr}
    (h : Ok c M (forN n f) p) : ∀ u < n, ∃ q, Ok c M (f u) q ∧ (forN n f p).1.getD u dLoop = (f u q).1 := by
  intro u hu
  obtain ⟨q, hq, e⟩ := ok_seqAll_get _ p h u (by simpa using hu)
  have hg : ((List.range n).map f).getD u (pure dLoop) = f u := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]; simp
  rw [hg] at hq e
  exact ⟨q, hq, e⟩

set_option maxRecDepth 100000 in
/-- **The parts of `Q_sig`.** -/
theorem qsig_parts {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : Ok c M (qsig I) p) :
    let o := (qsig I p).1
    (∃ q, Ok c M (gPre I) q ∧ (gPre I q).1 = o.pre) ∧
    (∃ q, Ok c M (loop [7] (chainM I o.pre.1.n o.pre.2.1.n)) q ∧
      (loop [7] (chainM I o.pre.1.n o.pre.2.1.n) q).1 = o.cm) ∧
    (∀ u < 5, ∃ q, Ok c M (loop [] (chainC I o.pre.1.n o.pre.2.1.n u)) q ∧
      (loop [] (chainC I o.pre.1.n o.pre.2.1.n u) q).1 = o.cc.getD u dLoop) ∧
    (∃ q, Ok c M (gCheck I o.pre.1 o.pre.2.1) q) ∧
    (∃ q, Ok c M (loop [4] (pathTpl I)) q ∧ (loop [4] (pathTpl I) q).1 = o.pa) ∧
    (∃ q, Ok c M (header I o.pre.1 o.pre.2.1) q) ∧
    (∃ q, Ok c M (assert0 (kc (I.bi + 17)) (kc I.flag)) q) ∧
    (∃ q, Ok c M (gSl I) q) ∧
    (∃ q, Ok c M (gMsg I o.pre.1.n (Tbase o.pre)) q ∧ (gMsg I o.pre.1.n (Tbase o.pre) q).1 = o.msg) := by
  unfold qsig at h ⊢
  intro o
  obtain ⟨o1, h, e1⟩ := ok_bind' h
  obtain ⟨o2, h, e2⟩ := ok_bind' h
  obtain ⟨o3, h, e3⟩ := ok_bind' h
  obtain ⟨o4, h, e4⟩ := ok_bind' h
  obtain ⟨o5, h, e5⟩ := ok_bind' h
  obtain ⟨o6, h, e6⟩ := ok_bind' h
  obtain ⟨o7, h, e7⟩ := ok_bind' h
  obtain ⟨o8, h, e8⟩ := ok_bind' h
  obtain ⟨o9, h, e9⟩ := ok_bind' h
  obtain ⟨o10, h, e10⟩ := ok_bind' h
  refine ⟨⟨_, o1, rfl⟩, ⟨_, o2, rfl⟩, fun u hu => ?_, ⟨_, o4⟩, ⟨_, o5, rfl⟩, ⟨_, o6⟩, ⟨_, o7⟩,
    ⟨_, o8⟩, ⟨_, o10, ?_⟩⟩
  · obtain ⟨q, hq, e⟩ := ok_forN_get o3 u hu
    exact ⟨q, hq, e.symm⟩
  -- `o.msg` through the bind equations (a bare `rfl` makes the kernel unfold the whole builder: 16 s).
  have E := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans e10))))))))
  rw [show o.pre = (gPre I p).1 from congrArg SigOut.pre E]
  exact (congrArg SigOut.msg E).symm

/-- **The parts of the message gadget.** -/
theorem gMsg_parts {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} {Zn Tb : Nat}
    (h : Ok c M (gMsg I Zn Tb) p) :
    let o := (gMsg I Zn Tb p).1
    (∃ q, Ok c M (loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24)) q ∧
      (loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24) q).1 = o.xm) ∧
    (∀ u < 5, ∃ q, Ok c M (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0)) q ∧
      (loop [] (stepsTpl I Zn (oA Zn)
      (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
      (I.bx + 24 * (128 + u)) 0) q).1 = o.xc.getD u dLoop) ∧
    (∃ q, Ok c M (loop [] (leafA I)) q ∧ (loop [] (leafA I) q).1 = o.la) ∧
    (∃ q, Ok c M (loop [9] (leafB I)) q ∧ (loop [9] (leafB I) q).1 = o.lb) ∧
    (∃ q, Ok c M (loop [] (leafC I Zn)) q ∧ (loop [] (leafC I Zn) q).1 = o.lc) ∧
    (∃ q, Ok c M (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16)) q ∧
      (loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16) q).1 = o.xp) ∧
    (∃ q, Ok c M (loop [] (leafStmtLanes I Zn)) q ∧ (loop [] (leafStmtLanes I Zn) q).1 = o.xls) ∧
    (∃ q, Ok c M (loop [] (twoLanes Zn 0x4E I.bcl I.bls 0)) q ∧
      (loop [] (twoLanes Zn 0x4E I.bcl I.bls 0) q).1 = o.xns) := by
  unfold gMsg at h ⊢
  intro o
  obtain ⟨o1, h, e1⟩ := ok_bind' h
  obtain ⟨o2, h, e2⟩ := ok_bind' h
  obtain ⟨o3, h, e3⟩ := ok_bind' h
  obtain ⟨o4, h, e4⟩ := ok_bind' h
  obtain ⟨o5, h, e5⟩ := ok_bind' h
  obtain ⟨o6, h, e6⟩ := ok_bind' h
  obtain ⟨o7, h, e7⟩ := ok_bind' h
  obtain ⟨o8, h, e8⟩ := ok_bind' h
  refine ⟨⟨_, o1, rfl⟩, fun u hu => ?_, ⟨_, o3, rfl⟩, ⟨_, o4, rfl⟩, ⟨_, o5, rfl⟩, ⟨_, o6, rfl⟩,
    ⟨_, o7, rfl⟩, ⟨_, o8, rfl⟩⟩
  obtain ⟨q, hq, e⟩ := ok_forN_get o2 u hu
  exact ⟨q, hq, e.symm⟩

end Lvm.QSig
end
-- ===== end of `LvmQSigParts` =====

-- ===== merged from `LvmWotsMsg` (GOLF module merge: `LvmWotsMsg.lean` is now a stub importing `LvmQSigDefs`) =====
section

/-!
# The message lanes of the signature hashes (byte layouts of the unaligned prefixes)

New for lvm (WP-12). The circuit writes each Keccak message as 17 lanes per block (`K` words); the
sponge reads byte `q` of a message as byte `q mod 8` of lane `q / 8` (`laneByte`). This module
proves, per hash kind, that lanes built from byte-shifted parts (the `BITS` outputs `shl`/`shr`)
and constants carry exactly the contract's bytes, in the form the K2-LS block lemmas
(`LvmKSpongeDigests`: `wotsStep_block`, `two_block`, `leafStmt_block`, `wotsLeaf_bytes`) take.

* `byte_shift`, `lane_shift_byte`: a lane `(A >>> (64 − 8r)) ^^^ (B <<< 8r)` holds the byte stream of
  the words `…, A, B, …` moved up by `r` bytes.
* `wotsStep_lanes` (43 B, `0x57 ‖ enc64 j ‖ i ‖ s ‖ x`: an 11-byte prefix, `x` moved by 3 bytes),
  `two_lanes` (65 B, `tag ‖ a ‖ b`: `sigNode`, `nodeStmt`), `leafStmt_lanes` (41 B,
  `0x4C ‖ h ‖ enc64 n`), `wotsLeaf_lanes` (4,265 B over 32 blocks, `0x4B ‖ enc64 j ‖ ends`).
-/

set_option autoImplicit false

namespace Lvm.Wots

open RecursionFast RecursionFast.Keccak Lvm.Bits Lvm.KSponge

/-- Byte `q` of a lane sequence. -/
def laneByte (lane : ℕ → UInt64) (q : ℕ) : UInt8 := byteW (lane (q / 8)) (q % 8)

/-- The digest whose byte `k` is byte `k mod 8` of word `k / 8`. -/
def digOfW (w : ℕ → UInt64) : Digest := Vector.ofFn fun k : Fin 32 => byteW (w (k / 8)) (k % 8)

theorem digOfW_get (w : ℕ → UInt64) {k : ℕ} (hk : k < 32) :
    (digOfW w)[k] = byteW (w (k / 8)) (k % 8) := by
  simp [digOfW]

/-- Byte `k` of a word is the `k`-th little-endian byte of its number. -/
theorem byteW_toNat (w : UInt64) {k : ℕ} (hk : k < 8) : byteW w k = (w.toNat / 256 ^ k).toUInt8 := by
  apply UInt8.toNat_inj.mp
  have h64 : 8 * k % 64 = 8 * k := Nat.mod_eq_of_lt (by omega)
  have h8 : (8 * k) % 2 ^ 64 = 8 * k := Nat.mod_eq_of_lt (by (clear * - hk; omega))
  simp [byteW, Nat.shiftRight_eq_div_pow, h64, pow_mul]

/-- **A byte-shifted lane** (`0 < r < 8`): byte `t` of `(A >>> (64 − 8r)) ^^^ (B <<< 8r)` is byte
`t + 8 − r` of `A` below `r`, else byte `t − r` of `B`. -/
theorem byte_shift {r : ℕ} (hr0 : 0 < r) (hr : r < 8) (A B : UInt64) {t : ℕ} (ht : t < 8) :
    byteW ((A >>> (64 - 8 * r).toUInt64) ^^^ (B <<< (8 * r).toUInt64)) t =
      if t < r then byteW A (t + 8 - r) else byteW B (t - r) := by
  rw [byteW_xor _ _ ht, show 64 - 8 * r = 8 * (8 - r) by (clear * - hr0 hr; omega), byteW_shr8 _ (by (clear * - hr0 hr; omega)) ht,
    byteW_shl8 _ hr ht]
  split_ifs <;> first | (exfalso; omega) | simp only [UInt8.xor_zero, UInt8.zero_xor]
  congr 1; omega

/-- Byte `t` of lane `l`. -/
theorem laneByte_8 (lane : ℕ → UInt64) (l : ℕ) {t : ℕ} (ht : t < 8) :
    laneByte lane (8 * l + t) = byteW (lane l) t := by
  unfold laneByte; rw [show (8 * l + t) / 8 = l by omega, show (8 * l + t) % 8 = t by omega]

/-- **The stream form**: a lane `l ≥ 1` of the shifted words `X` holds the bytes of `X` at offset
`8l + t − r`. -/
theorem lane_shift_byte {r : ℕ} (hr0 : 0 < r) (hr : r < 8) (X lane : ℕ → UInt64) {l : ℕ} (hl : 1 ≤ l)
    (h : lane l = (X (l - 1) >>> (64 - 8 * r).toUInt64) ^^^ (X l <<< (8 * r).toUInt64)) {t : ℕ}
    (ht : t < 8) : laneByte lane (8 * l + t) = laneByte X (8 * l + t - r) := by
  rw [laneByte_8 _ _ ht, h, byte_shift hr0 hr _ _ ht]
  by_cases h : t < r
  · simp only [h, ↓reduceIte]
    rw [show 8 * l + t - r = 8 * (l - 1) + (t + 8 - r) by omega,
      laneByte_8 _ _ (by (clear * - h; omega))]
  · simp only [h, ↓reduceIte]
    rw [show 8 * l + t - r = 8 * l + (t - r) by (clear * - hl h; omega),
      laneByte_8 _ _ (by (clear * - hr0 hr ht h; omega))]

/-! ## Helpers for the message layouts -/

/-- Dropping the first lane. -/
theorem laneByte_add8 (lane : ℕ → UInt64) (q : ℕ) :
    laneByte lane (8 + q) = laneByte (fun l => lane (l + 1)) q := by
  unfold laneByte; rw [show (8 + q) / 8 = q / 8 + 1 by omega, show (8 + q) % 8 = q % 8 by omega]

theorem byteW_one {t : ℕ} (ht : t < 8) : byteW 1 t = if t = 0 then 1 else 0 := by
  interval_cases t <;> decide

theorem byteW_top {t : ℕ} (ht : t < 8) :
    byteW 0x8000000000000000 t = if t = 7 then 0x80 else 0 := by
  interval_cases t <;> decide

/-- High bytes of a small word vanish. -/
theorem byteW_small (w : UInt64) {n k : ℕ} (hk : k < 8) (hw : w.toNat < 256 ^ n) (hnk : n ≤ k) :
    byteW w k = 0 := by
  rw [byteW_toNat w hk, Nat.div_eq_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hnk))]
  rfl

theorem padAt_self {L : ℕ} (h : L % 136 ≠ 135) : padAt L L = 1 := by
  unfold padAt; simp [Keccak.rate, h]

theorem padAt_mid {L q : ℕ} (h1 : q ≠ L) (h2 : q % 136 ≠ 135) : padAt L q = 0 := by
  unfold padAt; simp [Keccak.rate, h1, h2]

theorem padAt_end {L q : ℕ} (h1 : q ≠ L) (h2 : q % 136 = 135) : padAt L q = 0x80 := by
  unfold padAt; simp [Keccak.rate, h1, h2]

/-- **A byte stream moved up by `r` bytes**: lane 0 is a constant `c` (bytes below `r`) and
`W 0 <<< 8r`, lanes `1 … n` the shifted words. -/
theorem stream_byte {r : ℕ} (hr0 : 0 < r) (hr : r < 8) (W lane : ℕ → UInt64) (c : UInt64) (n : ℕ)
    (h0 : lane 0 = c ^^^ (W 0 <<< (8 * r).toUInt64)) (hc : ∀ t, r ≤ t → t < 8 → byteW c t = 0)
    (hl : ∀ l, 1 ≤ l → l ≤ n →
      lane l = (W (l - 1) >>> (64 - 8 * r).toUInt64) ^^^ (W l <<< (8 * r).toUInt64))
    {k : ℕ} (hk : r + k < 8 * (n + 1)) : laneByte lane (r + k) = laneByte W k := by
  obtain ⟨l, t, ht, hq⟩ : ∃ l t, t < 8 ∧ r + k = 8 * l + t :=
    ⟨_, _, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod _ _).symm⟩
  rw [hq]
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · rw [laneByte_8 _ _ ht, h0, byteW_xor _ _ ht, hc _ (by (clear * - hq; omega)) ht, byteW_shl8 _ hr ht]
    simp only [show r ≤ t by (clear * - hq; omega), ↓reduceIte, UInt8.zero_xor]
    rw [show k = 8 * 0 + k by (clear * -; omega), laneByte_8 _ _ (by (clear * - hr0 hr ht hq; omega))]
    congr 1; (clear * - hr0 hr ht hq; omega)
  · rw [lane_shift_byte hr0 hr W lane hl1 (hl _ hl1 (by (clear * - hk ht hq; omega))) ht]; congr 1; (clear * - hq; omega)

/-- **The padded tail of a block**: the stream's terminator `1` at `L`, zero lanes `l0 … l1 − 1`,
the top bit in lane `l1`, all in the block ending at lane `l1`. -/
theorem pad_all (lane : ℕ → UInt64) {L l0 l1 : ℕ} (hL : L < 8 * l0) (hl01 : l0 ≤ l1)
    (hblk : (8 * l1 + 8) % 136 = 0) (hL0 : 8 * l1 + 8 ≤ L + 136)
    (hfirst : ∀ q, L ≤ q → q < 8 * l0 → laneByte lane q = if q = L then 1 else 0)
    (hz : ∀ l, l0 ≤ l → l < l1 → lane l = 0) (htop : lane l1 = 0x8000000000000000) :
    ∀ q, L ≤ q → q < 8 * l1 + 8 → laneByte lane q = padAt L q := by
  intro q h1 h2
  by_cases hq : q < 8 * l0
  · rw [hfirst q h1 hq]
    split_ifs with he
    · subst he; exact (padAt_self (by (clear * - hl01 hblk h2 hq hL0; omega))).symm
    · exact (padAt_mid he (by (clear * - hL hl01 hblk hL0 h1 hq; omega))).symm
  · unfold laneByte
    by_cases hl : q / 8 < l1
    · rw [hz _ (by (clear * - hq; omega)) hl, byteW_zero, padAt_mid (by (clear * - hL hq; omega)) (by (clear * - hL hl01 hblk hL0 hq hl; omega))]
    · rw [show q / 8 = l1 by (clear * - hL hl01 hblk hL0 h1 h2 hq hl; omega), htop, byteW_top (Nat.mod_lt _ (by norm_num))]
      split_ifs with h7
      · exact (padAt_end (by (clear * - hL hblk h2 hq hl h7; omega)) (by (clear * - hblk h2 hl h7; omega))).symm
      · exact (padAt_mid (by (clear * - hL hq; omega)) (by (clear * - h7; omega))).symm

/-- **`wotsStep`'s lanes** (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x ‖ pad`, 43 bytes): the index `j < 2^16`
moved by one byte, the constants `i`, `s` at bytes 9 and 10, the four lanes of `x` moved by three
bytes, the padding. Conclusions: exactly the hypotheses of `wotsStep_block`. -/
theorem wotsStep_lanes (jw : UInt64) (hj : jw.toNat < 2 ^ 16) (i s : ℕ) (hi : i < 256)
    (hs : s < 256) (x lane : ℕ → UInt64)
    (h0 : lane 0 = (jw <<< (8 : ℕ).toUInt64) ^^^ 0x57)
    (h1 : lane 1 = ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) ^^^
      (x 0 <<< (24 : ℕ).toUInt64))
    (hx : ∀ k, 1 ≤ k → k < 4 → lane (k + 1) = (x (k - 1) >>> (40 : ℕ).toUInt64) ^^^ (x k <<< (24 : ℕ).toUInt64))
    (h5 : lane 5 = (x 3 >>> (40 : ℕ).toUInt64) ^^^ 0x1000000)
    (hz : ∀ l, 6 ≤ l → l < 16 → lane l = 0) (h16 : lane 16 = 0x8000000000000000) :
    laneByte lane 0 = tagWots ∧ (∀ k < 8, laneByte lane (1 + k) = (jw.toNat / 256 ^ k).toUInt8) ∧
      laneByte lane 9 = i.toUInt8 ∧ laneByte lane 10 = s.toUInt8 ∧
      (∀ k (hk : k < 32), laneByte lane (11 + k) = (digOfW x)[k]) ∧
      (∀ q, 43 ≤ q → q < rate → laneByte lane q = padAt 43 q) := by
  have hrate : rate = 136 := rfl
  obtain ⟨W, hWx, hW4⟩ : ∃ W : ℕ → UInt64, (∀ j < 4, W j = x j) ∧ W 4 = 1 :=
    ⟨fun j => if j < 4 then x j else 1, fun j hj => by simp [hj], rfl⟩
  have hiN : i.toUInt64.toNat = i := by simp; (clear * - hi; omega)
  have hsN : s.toUInt64.toNat = s := by simp; (clear * - hs; omega)
  have hi0 : ∀ t, 1 ≤ t → t < 8 → byteW i.toUInt64 t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by (clear * - hi hiN; omega)) h1
  have hs0 : ∀ t, 1 ≤ t → t < 8 → byteW s.toUInt64 t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by (clear * - hs hsN; omega)) h1
  have hc : ∀ t < 8, byteW ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) t
      = (if 1 ≤ t then byteW i.toUInt64 (t - 1) else 0) ^^^
        (if 2 ≤ t then byteW s.toUInt64 (t - 2) else 0) := fun t ht => by
    rw [byteW_xor _ _ ht]
    exact congrArg₂ _ (byteW_shl8 _ (s := 1) (by norm_num) ht) (byteW_shl8 _ (s := 2) (by norm_num) ht)
  have hb0 : ∀ t < 8, byteW (lane 0) t =
      (if 1 ≤ t then byteW jw (t - 1) else 0) ^^^ byteW (0x57 : UInt64) t := fun t ht => by
    rw [h0, byteW_xor _ _ ht]
    exact congrArg (· ^^^ _) (byteW_shl8 _ (s := 1) (by norm_num) ht)
  have hb1 : ∀ t < 8, byteW (lane 1) t =
      ((if 1 ≤ t then byteW i.toUInt64 (t - 1) else 0) ^^^
        (if 2 ≤ t then byteW s.toUInt64 (t - 2) else 0)) ^^^
        (if 3 ≤ t then byteW (x 0) (t - 3) else 0) := fun t ht => by
    rw [h1, byteW_xor _ _ ht, hc t ht]
    exact congrArg (_ ^^^ ·) (byteW_shl8 _ (s := 3) (by norm_num) ht)
  have hS : ∀ k, 3 + k < 40 → laneByte lane (8 + (3 + k)) = laneByte W k := fun k hk => by
    rw [laneByte_add8]
    refine stream_byte (by norm_num) (by norm_num) W (fun l => lane (l + 1))
      ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) 4
      (by show lane 1 = _; rw [h1, hWx 0 (by norm_num)]) (fun t h1 h2 => ?_) (fun l h1 h2 => ?_) hk
    · rw [hc t h2]
      simp only [show 1 ≤ t by (clear * - h1 h2; omega), show 2 ≤ t by (clear * - h1 h2; omega), ↓reduceIte, hi0 (t - 1) (by (clear * - h1 h2; omega)) (by (clear * - h1 h2; omega)),
        hs0 (t - 2) (by (clear * - h1 h2; omega)) (by (clear * - h1 h2; omega)), UInt8.xor_zero]
    · show lane (l + 1) = _
      rcases Nat.lt_or_ge l 4 with h4 | h4
      · rw [hx l h1 h4, hWx _ (by (clear * - h1 h2 h4; omega)), hWx _ h4]
      · obtain rfl : l = 4 := by (clear * - h1 h2 h4; omega)
        rw [show (4 : ℕ) - 1 = 3 from rfl, h5, hWx 3 (by norm_num), hW4]; rfl
  refine ⟨?_, fun k hk => ?_, ?_, ?_, fun k hk => ?_, fun q hq1 hq2 => ?_⟩
  · show byteW (lane 0) 0 = _
    rw [hb0 0 (by norm_num)]; simp [tagWots]; decide
  · rcases Nat.lt_or_ge k 7 with h7 | h7
    · rw [show 1 + k = 8 * 0 + (1 + k) by (clear * -; omega), laneByte_8 _ _ (by (clear * - hk h7; omega)), hb0 _ (by (clear * - hk h7; omega)),
        byteW_small (0x57 : UInt64) (n := 1) (by (clear * - hk h7; omega)) (by decide) (by (clear * - hk h7; omega))]
      simp only [show 1 ≤ 1 + k by (clear * - hk h7; omega), ↓reduceIte, UInt8.xor_zero, Nat.add_sub_cancel_left]
      exact byteW_toNat _ (by omega)
    · obtain rfl : k = 7 := by (clear * - hk h7; omega)
      rw [Nat.div_eq_of_lt (by (clear * - hj; omega))]
      show byteW (lane 1) 0 = _
      rw [hb1 0 (by norm_num)]; simp
  · show byteW (lane 1) 1 = _
    rw [hb1 1 (by norm_num), byteW_toNat i.toUInt64 (k := 1 - 1) (by norm_num), hiN]
    simp
  · show byteW (lane 1) 2 = _
    rw [hb1 2 (by norm_num), hi0 (2 - 1) (by norm_num) (by norm_num),
      byteW_toNat s.toUInt64 (k := 2 - 2) (by norm_num), hsN]
    simp
  · rw [show 11 + k = 8 + (3 + k) by (clear * -; omega), hS k (by (clear * - hk; omega)), digOfW_get x hk]
    unfold laneByte; rw [hWx _ (by (clear * - hk; omega))]
  · refine pad_all lane (l0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q h1 h2 => ?_) hz h16 q hq1 (by (clear * - hrate hq1 hq2; omega))
    rw [show q = 8 + (3 + (q - 11)) by (clear * - h1 h2; omega), hS _ (by (clear * - h1 h2; omega))]
    unfold laneByte
    rw [show (q - 11) / 8 = 4 by (clear * - h1 h2; omega), hW4, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **Two digests after a tag** (65 bytes: `sigNode`, `nodeStmt`): conclusions are the hypotheses
of `two_block`. -/
theorem two_lanes (tag : UInt8) (a b lane : ℕ → UInt64)
    (h0 : lane 0 = (a 0 <<< (8 : ℕ).toUInt64) ^^^ tag.toUInt64)
    (ha : ∀ k, 1 ≤ k → k < 4 → lane k = (a (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (a k <<< (8 : ℕ).toUInt64))
    (h4 : lane 4 = (a 3 >>> (56 : ℕ).toUInt64) ^^^ (b 0 <<< (8 : ℕ).toUInt64))
    (hb : ∀ k, 1 ≤ k → k < 4 →
      lane (4 + k) = (b (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (b k <<< (8 : ℕ).toUInt64))
    (h8 : lane 8 = (b 3 >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 9 ≤ l → l < 16 → lane l = 0) (h16 : lane 16 = 0x8000000000000000) :
    laneByte lane 0 = tag ∧ (∀ k (hk : k < 32), laneByte lane (1 + k) = (digOfW a)[k]) ∧
      (∀ k (hk : k < 32), laneByte lane (33 + k) = (digOfW b)[k]) ∧
      (∀ q, 65 ≤ q → q < rate → laneByte lane q = padAt 65 q) := by
  have hrate : rate = 136 := rfl
  obtain ⟨W, hWa, hWb, hW8⟩ : ∃ W : ℕ → UInt64, (∀ j < 4, W j = a j) ∧
      (∀ j, 4 ≤ j → j < 8 → W j = b (j - 4)) ∧ W 8 = 1 :=
    ⟨fun j => if j < 4 then a j else if j < 8 then b (j - 4) else 1,
      fun j hj => by simp [hj], fun j h1 h2 => by simp [h2, show ¬ j < 4 by (clear * - h1 h2; omega)], rfl⟩
  have hc : ∀ t, 1 ≤ t → t < 8 → byteW tag.toUInt64 t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by have := tag.toNat_lt; simp; omega) h1
  have hS : ∀ k, 1 + k < 72 → laneByte lane (1 + k) = laneByte W k := fun k hk => by
    refine stream_byte (by norm_num) (by norm_num) W lane tag.toUInt64 8
      (by rw [h0, hWa 0 (by norm_num), UInt64.xor_comm]) hc (fun l h1 h2 => ?_) hk
    rcases (show l < 4 ∨ l = 4 ∨ (4 < l ∧ l < 8) ∨ l = 8 by (clear * - h1 h2; omega)) with h | h | h | h
    · rw [ha l h1 h, hWa _ (by (clear * - h1 h2 h; omega)), hWa _ h]
    · subst h
      rw [show (4 : ℕ) - 1 = 3 from rfl, h4, hWa 3 (by norm_num), hWb 4 (by norm_num) (by norm_num)]
    · have := hb (l - 4) (by (clear * - h1 h2 h; omega)) (by (clear * - h1 h2 h; omega))
      rw [show 4 + (l - 4) = l by (clear * - h1 h2 h; omega)] at this
      rw [this, hWb _ (by (clear * - h1 h2 h; omega)) (by (clear * - h1 h2 h; omega)), hWb _ (by (clear * - h1 h2 h; omega)) (by (clear * - h1 h2 h; omega)),
        show l - 1 - 4 = l - 4 - 1 by (clear * - h1 h2 h; omega)]
    · subst h
      rw [show (8 : ℕ) - 1 = 7 from rfl, h8, hWb 7 (by norm_num) (by norm_num), hW8]; rfl
  refine ⟨?_, fun k hk => ?_, fun k hk => ?_, fun q hq1 hq2 => ?_⟩
  · show byteW (lane 0) 0 = _
    rw [h0, byteW_xor _ _ (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
      byteW_shl8 _ (by norm_num) (by norm_num), byteW_toNat tag.toUInt64 (k := 0) (by norm_num)]
    simp
  · rw [hS k (by (clear * - hk; omega)), digOfW_get a hk]
    unfold laneByte; rw [hWa _ (by (clear * - hk; omega))]
  · rw [show 33 + k = 1 + (32 + k) by (clear * -; omega), hS _ (by (clear * - hk; omega)), digOfW_get b hk]
    unfold laneByte
    rw [hWb _ (by (clear * - hk; omega)) (by (clear * - hk; omega)), show (32 + k) / 8 - 4 = k / 8 by (clear * - hk; omega),
      show (32 + k) % 8 = k % 8 by (clear * -; omega)]
  · refine pad_all lane (l0 := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q h1 h2 => ?_) hz h16 q hq1 (by (clear * - hrate hq1 hq2; omega))
    rw [show q = 1 + (q - 1) by (clear * - h1 h2; omega), hS _ (by (clear * - h1 h2; omega))]
    unfold laneByte
    rw [show (q - 1) / 8 = 8 by (clear * - h1 h2; omega), hW8, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **`leafStmt`'s lanes** (`tagLeaf ‖ h ‖ enc64 n ‖ pad`, 41 bytes): conclusions are the
hypotheses of `leafStmt_block`. -/
theorem leafStmt_lanes (h : ℕ → UInt64) (nw : UInt64) (lane : ℕ → UInt64)
    (h0 : lane 0 = (h 0 <<< (8 : ℕ).toUInt64) ^^^ 0x4C)
    (hh : ∀ k, 1 ≤ k → k < 4 → lane k = (h (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (h k <<< (8 : ℕ).toUInt64))
    (h4 : lane 4 = (h 3 >>> (56 : ℕ).toUInt64) ^^^ (nw <<< (8 : ℕ).toUInt64))
    (h5 : lane 5 = (nw >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 6 ≤ l → l < 16 → lane l = 0) (h16 : lane 16 = 0x8000000000000000) :
    laneByte lane 0 = tagLeaf ∧ (∀ k (hk : k < 32), laneByte lane (1 + k) = (digOfW h)[k]) ∧
      (∀ k < 8, laneByte lane (33 + k) = (nw.toNat / 256 ^ k).toUInt8) ∧
      (∀ q, 41 ≤ q → q < rate → laneByte lane q = padAt 41 q) := by
  have hrate : rate = 136 := rfl
  obtain ⟨W, hWh, hW4, hW5⟩ : ∃ W : ℕ → UInt64, (∀ j < 4, W j = h j) ∧ W 4 = nw ∧ W 5 = 1 :=
    ⟨fun j => if j < 4 then h j else if j = 4 then nw else 1, fun j hj => by simp [hj], rfl, rfl⟩
  have hc : ∀ t, 1 ≤ t → t < 8 → byteW (0x4C : UInt64) t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by decide) h1
  have hS : ∀ k, 1 + k < 48 → laneByte lane (1 + k) = laneByte W k := fun k hk => by
    refine stream_byte (by norm_num) (by norm_num) W lane 0x4C 5
      (by rw [h0, hWh 0 (by norm_num), UInt64.xor_comm]) hc (fun l h1 h2 => ?_) hk
    rcases (show l < 4 ∨ l = 4 ∨ l = 5 by (clear * - h1 h2; omega)) with hl | hl | hl
    · rw [hh l h1 hl, hWh _ (by (clear * - h1 h2 hl; omega)), hWh _ hl]
    · subst hl
      rw [show (4 : ℕ) - 1 = 3 from rfl, h4, hWh 3 (by norm_num), hW4]
    · subst hl
      rw [show (5 : ℕ) - 1 = 4 from rfl, h5, hW4, hW5]; rfl
  refine ⟨?_, fun k hk => ?_, fun k hk => ?_, fun q hq1 hq2 => ?_⟩
  · show byteW (lane 0) 0 = _
    rw [h0, byteW_xor _ _ (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
      byteW_shl8 _ (by norm_num) (by norm_num)]
    simp [tagLeaf]; decide
  · rw [hS k (by (clear * - hk; omega)), digOfW_get h hk]
    unfold laneByte; rw [hWh _ (by (clear * - hk; omega))]
  · rw [show 33 + k = 1 + (32 + k) by (clear * -; omega), hS _ (by (clear * - hk; omega))]
    unfold laneByte
    rw [show (32 + k) / 8 = 4 by (clear * - hk; omega), hW4, show (32 + k) % 8 = k by (clear * - hk; omega), byteW_toNat _ hk]
  · refine pad_all lane (l0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q h1 h2 => ?_) hz h16 q hq1 (by (clear * - hrate hq1 hq2; omega))
    rw [show q = 1 + (q - 1) by (clear * - h1 h2; omega), hS _ (by (clear * - h1 h2; omega))]
    unfold laneByte
    rw [show (q - 1) / 8 = 5 by (clear * - h1 h2; omega), hW5, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **The WOTS key leaf's lanes** (`tagWotsLeaf ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂ ‖ pad`, 4,265 bytes,
544 lanes = 32 blocks): the index `j < 2^16` and the 532 end lanes `E` moved by one byte. The
blocked byte map `m u q = laneByte lane (136 u + q)` meets the hypotheses of `wotsLeaf_bytes` and
`PadOk`. -/
theorem wotsLeaf_lanes (jw : UInt64) (hj : jw.toNat < 2 ^ 16) (E lane : ℕ → UInt64)
    (h0 : lane 0 = (jw <<< (8 : ℕ).toUInt64) ^^^ 0x4B) (h1 : lane 1 = E 0 <<< (8 : ℕ).toUInt64)
    (hE : ∀ m, 2 ≤ m → m ≤ 532 →
      lane m = (E (m - 2) >>> (56 : ℕ).toUInt64) ^^^ (E (m - 1) <<< (8 : ℕ).toUInt64))
    (h533 : lane 533 = (E 531 >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 534 ≤ l → l < 543 → lane l = 0) (h543 : lane 543 = 0x8000000000000000) :
    let mb : ℕ → ℕ → UInt8 := fun u q => laneByte lane (rate * u + q)
    mb 0 0 = tagWotsLeaf ∧
      (∀ k < 8, mb ((1 + k) / rate) ((1 + k) % rate) = (jw.toNat / 256 ^ k).toUInt8) ∧
      (∀ i < 133, ∀ k < 32, mb ((9 + 32 * i + k) / rate) ((9 + 32 * i + k) % rate) =
        byteW (E (4 * i + k / 8)) (k % 8)) ∧
      PadOk mb 4265 := by
  have hrate : rate = 136 := rfl
  intro mb
  have hmb : ∀ p, mb (p / rate) (p % rate) = laneByte lane p := fun p => by
    show laneByte lane (rate * (p / rate) + p % rate) = _
    rw [Nat.div_add_mod]
  obtain ⟨W, hW0, hWE, hW533⟩ : ∃ W : ℕ → UInt64, W 0 = jw ∧
      (∀ j, 1 ≤ j → j ≤ 532 → W j = E (j - 1)) ∧ W 533 = 1 :=
    ⟨fun j => if j = 0 then jw else if j ≤ 532 then E (j - 1) else 1, rfl,
      fun j h1 h2 => by simp [h2, show j ≠ 0 by (clear * - h1 h2; omega)], rfl⟩
  have hjs : jw >>> (56 : ℕ).toUInt64 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_zero]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hj (by simp))
  have hc : ∀ t, 1 ≤ t → t < 8 → byteW (0x4B : UInt64) t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by decide) h1
  have hS : ∀ k, 1 + k < 8 * 534 → laneByte lane (1 + k) = laneByte W k := fun k hk => by
    refine stream_byte (by norm_num) (by norm_num) W lane 0x4B 533
      (by rw [h0, hW0, UInt64.xor_comm]) hc (fun l hl1 hl2 => ?_) hk
    rcases (show l = 1 ∨ (2 ≤ l ∧ l ≤ 532) ∨ l = 533 by (clear * - hl1 hl2; omega)) with hl | hl | hl
    · subst hl
      rw [show (1 : ℕ) - 1 = 0 from rfl, h1, hW0, hWE 1 (by norm_num) (by norm_num)]
      show _ = (jw >>> (56 : ℕ).toUInt64) ^^^ _
      rw [hjs, UInt64.zero_xor]
    · rw [hE l hl.1 hl.2, hWE _ (by (clear * - hl1 hl2 hl; omega)) (by (clear * - hl1 hl2 hl; omega)), hWE _ (by omega) (by (clear * - hl1 hl2 hl; omega)),
        show l - 1 - 1 = l - 2 by (clear * - hl1 hl2 hl; omega)]
    · subst hl
      rw [show (533 : ℕ) - 1 = 532 from rfl, h533, hWE 532 (by norm_num) (by norm_num), hW533]; rfl
  refine ⟨?_, fun k hk => ?_, fun i hi k hk => ?_, fun p hp1 hp2 => ?_⟩
  · show laneByte lane (rate * 0 + 0) = _
    show byteW (lane 0) 0 = _
    rw [h0, byteW_xor _ _ (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
      byteW_shl8 _ (by norm_num) (by norm_num)]
    simp [tagWotsLeaf]; decide
  · rw [hmb, hS k (by (clear * - hk; omega))]
    unfold laneByte
    rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, hW0, byteW_toNat _ hk]
  · rw [hmb, show 9 + 32 * i + k = 1 + (8 + 32 * i + k) by (clear * -; omega), hS _ (by (clear * - hi hk; omega))]
    unfold laneByte
    rw [hWE _ (by (clear * - hi hk; omega)) (by (clear * - hi hk; omega)), show (8 + 32 * i + k) / 8 - 1 = 4 * i + k / 8 by (clear * - hi hk; omega),
      show (8 + 32 * i + k) % 8 = k % 8 by (clear * -; omega)]
  · have hn : rate * nBlk 4265 = 4352 := by decide
    rw [hmb]
    refine pad_all lane (l0 := 534) (l1 := 543) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun q h1 h2 => ?_) hz h543 p hp1 (by (clear * - hp2 hn; omega))
    rw [show q = 1 + (q - 1) by (clear * - h1 h2; omega), hS _ (by (clear * - h1 h2; omega))]
    unfold laneByte
    rw [show (q - 1) / 8 = 533 by (clear * - h1 h2; omega), hW533, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

end Lvm.Wots
end
-- ===== end of `LvmWotsMsg` =====

/-!
# `Q_sig`'s soundness: the hypotheses and conclusions (BLUEPRINT §4.6, §11 A2, A3)

New for lvm (WP-12). The theorem WP-14 consumes:

**`qsig_sound`**: in every memory `M` where `Q_sig`'s rows and assertions hold with the node flag
`1`, given
* `SigKS` — the `KS` rows of the signature schedule: each hash's message lanes are `Q_sig`'s cells
  `xcell o r l` (row `r`, lane `l`; the sponge's byte `q` is byte `q mod 8` of lane `q / 8`), its
  block is a `BlockPerm` from the zero state (the key leaf: 32 linked blocks), and its digest
  cells (`ys`, `yc`, `yls`, `yns`) are the output's first 32 bytes. This is the per-row form of
  WP-8's sponge table (`LvmKSponge`, K2-LS); WP-8's `LvmSpongeTable` turns the KS table relation
  into it;
* `SigBits` — the `BITS` outputs: each output cell is its `BOut` word function of the cell the row
  reads (`LvmBits.row_sound` gives this from a `BITS` row's constraints, the bus gives the read);
* powers of `x` injective below `2^10` (from `GInj`, which `loopir_sound` assumes anyway),

the child's signature `σ'` (`sigAt' M.k I.sg`) on the message digest `m` (`digAt M.k I.md`, which is
`traceDigest tr'` by the KS trace rows) passes the contract's `SigOk` under `vk`, and the child's
header (stream lanes from `I.hd`) passes the executable checks of `V_S`'s parse step (`ChildOk`):
`b' ∈ {0,1}`, `vk' = vk`, `1 ≤ n' ≤ 2^20`, `b' = 0 ⇒ c_L' = 0 ∧ σ_leaf' = 0`,
`b' = 1 ⇒ σ_leaf' = σ_leaf` (A2), and `c_L = leafStmt h' n'` (`b' = 0`) or
`nodeStmt c_L' (leafStmt h' n')` (`b' = 1`).
-/

set_option autoImplicit false

namespace Lvm.QSig

open RecursionFast RecursionFast.Keccak Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.KSponge Lvm.Wots

/-! ## Reading digests, signatures and cells -/

/-- The digest whose four lanes are the `K` cells `a … a + 3`. -/
def digAt (v : Nat → FK) (a : Nat) : Digest := digOfW fun l => (v (a + l)).val

/-- The signature whose lanes are the `K` cells from `a`: `idx`, 133 chain values, 16 siblings
(BLUEPRINT §2.1's `σ` layout). -/
def sigAt' (v : Nat → FK) (a : Nat) : Sig :=
  ⟨(v a).val.toNat, (List.range wotsLen).map fun i => digAt v (a + 1 + 4 * i),
    (List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t)⟩

/-- Chain `i`'s template row `t` (message chains `i < 128`, checksum chains `128 … 132`). -/
def chainCell (o : SigOut) (i t : Nat) : Nat :=
  if i < 128 then (o.cm.cell t i).n else ((o.cc.getD (i - 128) dLoop).cell t 0).n

/-- The input of chain `i`'s step `s + 1`, lane `l`: the signed value, then the muxed cells. -/
def xin (I : SigIn) (o : SigOut) (i s l : Nat) : Nat :=
  if s = 0 then I.sg + 1 + 4 * i + l else chainCell o i (8 * s + l)

/-- Chain `i`'s end, lane `l`. -/
def endc (o : SigOut) (i l : Nat) : Nat := chainCell o i (24 + l)

/-- Lane `m < 544` of the key leaf's message. -/
def leafLane (o : SigOut) (m : Nat) : Nat :=
  if m < 2 then (o.msg.la.cell m 0).n
  else if m < 514 then (o.msg.lb.cell 0 (m - 2)).n else (o.msg.lc.cell (m - 514) 0).n

/-- **Lane `l` of `KS` row `r`'s message** (`r < 449`: 399 chain steps, 32 leaf blocks, 16 path
nodes, `leafStmt`, `nodeStmt`). -/
def xcell (o : SigOut) (r l : Nat) : Nat :=
  if r < 384 then (o.msg.xm.cell (17 * (r % 3) + l) (r / 3)).n
  else if r < 399 then ((o.msg.xc.getD ((r - 384) / 3) dLoop).cell (17 * ((r - 384) % 3) + l) 0).n
  else if r < 431 then leafLane o (17 * (r - 399) + l)
  else if r < 447 then (o.msg.xp.cell l (r - 431)).n
  else if r = 447 then (o.msg.xls.cell l 0).n else (o.msg.xns.cell l 0).n

/-- The words of the cells `f l`. -/
def lanesW (v : Nat → FK) (f : Nat → Nat) : Nat → UInt64 := fun l => (v (f l)).val

/-! ## The hypotheses -/

/-- A one-block hash row: its message lanes `x`, its digest cells `y`. -/
def OneHash (v : Nat → FK) (x : Nat → Nat) (y : Nat) : Prop :=
  ∃ s, BlockPerm (xorMsg zeroSt (laneByte (lanesW v x))) s ∧ digAt v y = stDigest s

/-- **The `KS` rows of the signature schedule** (WP-8's sponge table, per row). -/
structure SigKS (I : SigIn) (o : SigOut) (v : Nat → FK) : Prop where
  step : ∀ r < 399, OneHash v (xcell o r) (I.ys + 4 * r)
  leaf : ∃ sIn sOut : Nat → State, sIn 0 = zeroSt ∧
    (∀ u < 32, BlockPerm (xorMsg (sIn u) (laneByte (lanesW v (xcell o (399 + u))))) (sOut u)) ∧
    (∀ u, u + 1 < 32 → sIn (u + 1) = sOut u) ∧ digAt v I.yc = stDigest (sOut 31)
  path : ∀ t < 16, OneHash v (xcell o (431 + t)) (I.yc + 4 * (t + 1))
  ls : OneHash v (xcell o 447) I.yls
  ns : OneHash v (xcell o 448) I.yns

/-- A `BITS` output: cell `c` is the word function `b` of cell `w`. -/
def Out1 (v : Nat → FK) (w : Nat) (b : BOut) (c : Nat) : Prop := v c = w64 (b.word (v w).val)

/-- **The `BITS` outputs `Q_sig` reads** (rows: `σ'.idx`; the message digest's 256 bits; the ten
checksum bits of a free word; every chain step input (`shl 24`/`shr 40`); every chain end, path
node half, `h'`, `c_L'`, `leafStmt` lane (`shl 8`/`shr 56`); `n'`'s parts, bits and range fields). -/
structure SigBits (I : SigIn) (o : SigOut) (v : Nat → FK) : Prop where
  idx_lo : Out1 v I.sg (.shl 8) I.bi
  idx_bit : ∀ z < 16, Out1 v I.sg (.bit z) (I.bi + 1 + z)
  idx_hi : Out1 v I.sg (.shr 16) (I.bi + 17)
  md : ∀ q < 256, Out1 v (I.md + q / 64) (.bit (q % 64)) (I.bd + q)
  cs : ∃ w : UInt64, ∀ k < 10, v (I.bc + k) = w64 ((BOut.bit k).word w)
  x : ∀ i < 133, ∀ s < 3, ∀ l < 4,
    Out1 v (xin I o i s l) (.shl 24) (I.bx + 2 * (4 * (3 * i + s) + l)) ∧
      Out1 v (xin I o i s l) (.shr 40) (I.bx + 2 * (4 * (3 * i + s) + l) + 1)
  e : ∀ i < 133, ∀ l < 4, Out1 v (endc o i l) (.shl 8) (I.be + 2 * (4 * i + l)) ∧
    Out1 v (endc o i l) (.shr 56) (I.be + 2 * (4 * i + l) + 1)
  p : ∀ t < 16, ∀ u < 2, ∀ l < 4,
    Out1 v (o.pa.cell (4 + 4 * u + l) t).n (.shl 8) (I.bp + 2 * (8 * t + 4 * u + l)) ∧
      Out1 v (o.pa.cell (4 + 4 * u + l) t).n (.shr 56) (I.bp + 2 * (8 * t + 4 * u + l) + 1)
  h : ∀ l < 4, Out1 v (I.hd + 14 + l) (.shl 8) (I.bh + 2 * l) ∧
    Out1 v (I.hd + 14 + l) (.shr 56) (I.bh + 2 * l + 1)
  n_lo : Out1 v (I.hd + 13) (.shl 8) I.bn
  n_hi : Out1 v (I.hd + 13) (.shr 56) (I.bn + 1)
  n_bit : ∀ z ≤ I.ln, Out1 v (I.hd + 13) (.bit z) (I.bn + 2 + z)
  n_top : Out1 v (I.hd + 13) (.shr (I.ln + 1)) (I.bn + 2 + I.ln + 1)
  n_low : Out1 v (I.hd + 13) (.shl (64 - I.ln)) (I.bn + 2 + I.ln + 2)
  cl : ∀ l < 4, Out1 v (I.hd + 5 + l) (.shl 8) (I.bcl + 2 * l) ∧
    Out1 v (I.hd + 5 + l) (.shr 56) (I.bcl + 2 * l + 1)
  ls : ∀ l < 4, Out1 v (I.yls + l) (.shl 8) (I.bls + 2 * l) ∧
    Out1 v (I.yls + l) (.shr 56) (I.bls + 2 * l + 1)

/-- The all-zero digest. -/
def zeroDig : Digest := Vector.replicate 32 0

/-- **The child's header passes `V_S`'s executable checks** (BLUEPRINT §11 A2, A3; WP-11a `parseOk`):
the stream lanes from `I.hd` are `b'`, `vk'` (4), `c_L'` (4), `s'` (4), `n'`, `h'` (4), `σ_leaf'`
(597); `I.vk`, `I.cL`, `I.sl` are the current proof's `vk`, `c_L`, `σ_leaf`. -/
def ChildOk (I : SigIn) (v : Nat → FK) : Prop :=
  let b := (v I.hd).val.toNat
  let n := (v (I.hd + 13)).val.toNat
  (b = 0 ∨ b = 1) ∧ digAt v (I.hd + 1) = digAt v I.vk ∧ 1 ≤ n ∧ n ≤ 2 ^ I.ln ∧
    (b = 0 → digAt v (I.hd + 5) = zeroDig ∧ ∀ k < 597, v (I.hd + 18 + k) = 0) ∧
    (b = 1 → ∀ k < 597, v (I.hd + 18 + k) = v (I.sl + k)) ∧
    digAt v I.cL = (if b = 0 then leafStmt (digAt v (I.hd + 14)) n
      else nodeStmt (digAt v (I.hd + 5)) (leafStmt (digAt v (I.hd + 14)) n))

end Lvm.QSig
