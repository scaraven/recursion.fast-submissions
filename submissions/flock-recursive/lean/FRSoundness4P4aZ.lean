-- G6: this module also holds the former modules `FRSoundness4P4aLast`, `FRSoundness4P4aBridge`, `FRSoundness4TailFront`, `FRSoundness4P4aS`, `FRSoundness4P4aFin`, `FRSoundness4P4aS2` (one section each, in import order).
import FRSoundness4P4aNames
import FRVIR4
import FRVIRFinalsCore
import FRSoundness4P4aSeg
import FRSoundness4TailFold
import FRSoundness4TailLig

section G6_FRSoundness4P4aLast

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12; S-F4 §7 Q3; stage P4a).

/-!
# `lastOps` runs to `L = (n − 1) mod 2^18` (the segment's last block, kernel-checked)

A segment's `stmt` phase runs `lastOps so b` (94 ops, `FRVIR4`): the digest at `stmt` byte 33,
its 24-bit index `N = n mod 2^24`, the constants `0`, `1`; per bit `k < 18` the bit `N_k`
(`bitOf`) and its F value (`selectHalf`); then the borrow chain `L_k = N_k + c_k`,
`c_{k+1} = (1 + N_k) c_k` from `c_0 = 1` (characteristic two). S-F4 measured it at nine values of
`n` (`logs/S-F4/dump/last.txt`); this module proves it.

* **`run_lastOps`**: from registers `R` with `|R| = b`, `pureRun` asks nothing, its flag is `true`,
  and the appended values are `lastVals D` (`D` the digest read).
* **`lastVals_zero`**, **`lastVals_bit`**: register `b + 2` holds `0` and register `b + 40 + 3k`
  (`lastOuts`) holds `L_k`, in F (`lbF`).
* **`lastSum`**: `Σ_{k<18} [L_k] 2^k = (N + 2^18 − 1) mod 2^18`, the number the segment's
  `targetS`/`shiftMask` read back (`FRSegTarget4.lastAt`); **`lastSum_eq`**: `n − 1` for
  `1 ≤ N ≤ 2^18`.
-/

namespace FR.Snd.P4a
open RecursionFast Finset

/-! ## The borrow chain -/

theorem bF_add (x y : Bool) : bF x + bF y = bF (x ^^ y) := by
  cases x <;> cases y <;> simp [bF, CharTwo.add_self_eq_zero]

theorem bF_mul (x y : Bool) : (1 + bF x) * bF y = bF (!x && y) := by
  cases x <;> cases y <;> simp [bF, CharTwo.add_self_eq_zero]

theorem decMod {a P : ℕ} (h : a < P) : (a + (P - 1)) % P = if a = 0 then P - 1 else a - 1 := by
  split_ifs with ha
  · subst ha; rw [zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show a + (P - 1) = (a - 1) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **The borrow invariant**: the low `k` bits of `N − 1` and the borrow out of them. -/
theorem borrow_inv (N : ℕ) : ∀ k,
    (∑ j ∈ range k, if lb N j then 2 ^ j else 0) = (N % 2 ^ k + (2 ^ k - 1)) % 2 ^ k ∧
      (borrow N k = true ↔ N % 2 ^ k = 0)
  | 0 => by simp [borrow, Nat.mod_one]
  | k + 1 => by
    obtain ⟨ih, hb⟩ := borrow_inv N k
    have hm : N % 2 ^ (k + 1) = N % 2 ^ k + 2 ^ k * (N / 2 ^ k % 2) := Nat.mod_pow_succ
    have ht : N.testBit k = decide (N / 2 ^ k % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    have hlt := Nat.mod_lt N (Nat.two_pow_pos k)
    have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hd : N / 2 ^ k % 2 = 0 ∨ N / 2 ^ k % 2 = 1 := by omega
    have hlt2 : N % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [sum_range_succ, ih, decMod hlt, decMod hlt2, hm]
    simp only [lb, borrow]
    rw [hp]
    rcases hd with hd | hd <;> simp only [hd] at ht hm ⊢ <;> rw [hm] at hlt2 <;>
      by_cases hz : N % 2 ^ k = 0
    · have hB := hb.mpr hz; simp [ht, hB, hz]; have := Nat.two_pow_pos k; omega
    · have hB : borrow N k = false := by simpa using mt hb.mp hz
      simp [ht, hB, hz]
    · have hB := hb.mpr hz; simp [ht, hB, hz]
    · have hB : borrow N k = false := by simpa using mt hb.mp hz
      simp [ht, hB, hz]; omega

/-- **`L`'s bits sum to `(N − 1) mod 2^18`.** -/
theorem lastSum (N : ℕ) :
    (∑ k ∈ range 18, if lb N k then 2 ^ k else 0) = (N + (2 ^ 18 - 1)) % 2 ^ 18 := by
  rw [(borrow_inv N 18).1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem lastSum_eq {N : ℕ} (h1 : 1 ≤ N) (h2 : N ≤ 2 ^ 18) :
    (∑ k ∈ range 18, if lb N k then 2 ^ k else 0) = N - 1 := by
  rw [lastSum]; norm_num at h2 ⊢; omega

/-! ## Running `lastOps` -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- The bit `k` values: `N_k` and its F value. -/
def bitVals (N k : ℕ) : List Val := [.bit (N.testBit k), .f (bF (N.testBit k))]

/-- The borrow chain's values at `k`: `L_k`, `1 + N_k`, `c_{k+1}`. -/
def chainVals (N k : ℕ) : List Val :=
  [.f (bF (lb N k)), .f (1 + bF (N.testBit k)), .f (bF (borrow N (k + 1)))]

/-- The first four values: the digest, `N`, `0`, `1`. -/
def headVals (D : Digest) (N : ℕ) : List Val := [.d D, .n N, .f 0, .f 1]

/-- **The values `lastOps` appends** from the digest `D` at `stmt` byte 33. -/
def lastVals (D : Digest) : List Val :=
  headVals D (idxOfF 24 D 0) ++ (List.range 18).flatMap (bitVals (idxOfF 24 D 0)) ++
    (List.range 18).flatMap (chainVals (idxOfF 24 D 0))

theorem length_flatMap_const {g : ℕ → List Val} {w : ℕ} (hg : ∀ k, (g k).length = w) :
    ∀ n, ((List.range n).flatMap g).length = w * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_const hg n]
    simp [hg]; ring

theorem getD_flatMap {g : ℕ → List Val} {w : ℕ} (hg : ∀ k, (g k).length = w) :
    ∀ n k j, k < n → j < w → ((List.range n).flatMap g).getD (w * k + j) default = (g k).getD j default
  | 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, j, hk, hj => by
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD]
    by_cases hkn : k < n
    · rw [List.getElem?_append_left (by rw [length_flatMap_const hg]; nlinarith),
        ← List.getD_eq_getElem?_getD, getD_flatMap hg n k j hkn hj, List.getD_eq_getElem?_getD]
    · have : k = n := by omega
      subst this
      rw [List.getElem?_append_right (by rw [length_flatMap_const hg]; omega),
        length_flatMap_const hg]
      simp

/-- Reading the appended values. -/
theorem rd_vals (R : Array Val) (X L : List Val) (i : ℕ) :
    rd (R ++ X.toArray ++ L.toArray) (R.size + i) = (X ++ L).getD i default := by
  have := rd_app R (X ++ L) i
  simpa [Array.append_assoc] using this

/-- Running a `flatMap` over `range n` block by block. -/
theorem pureRun_flatMap (R : Array Val) (P : List Val) (f : ℕ → List Op) (g : ℕ → List Val) :
    ∀ n, (∀ k < n, pureRun impl κ inp (f k) (R ++ (P ++ (List.range k).flatMap g).toArray) [] =
      some (g k, true)) →
    pureRun impl κ inp ((List.range n).flatMap f) (R ++ P.toArray) [] =
      some ((List.range n).flatMap g, true)
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    have hA := pureRun_flatMap R P f g n fun k hk => h k (by omega)
    have hB := h n (by omega)
    have hB' : pureRun impl κ inp (f n) (R ++ P.toArray ++ (List.flatMap g (List.range n)).toArray) [] =
        some (g n, true) := by simpa [Array.append_assoc] using hB
    have := pureRun_seq impl κ inp hA hB'
    simpa using this

theorem bitVals_length (N k : ℕ) : (bitVals N k).length = 2 := rfl
theorem chainVals_length (N k : ℕ) : (chainVals N k).length = 3 := rfl

/-- Bit `k`'s two ops. -/
theorem run_bits (R : Array Val) (D : Digest) (N k : ℕ) :
    pureRun impl κ inp [.bitOf (R.size + 1) k, .selectHalf (R.size + 4 + 2 * k) (R.size + 2) (R.size + 3)]
      (R ++ (headVals D N ++ (List.range k).flatMap (bitVals N)).toArray) [] =
      some (bitVals N k, true) := by
  set X := headVals D N ++ (List.range k).flatMap (bitVals N)
  have hX : X.length = 4 + 2 * k := by
    simp only [X, List.length_append, length_flatMap_const (bitVals_length N), headVals,
      List.length_cons, List.length_nil]
  rw [pureRun_cons_val (v := .bit (N.testBit k)) ?_, pureRun_cons_val (v := .f (bF (N.testBit k))) ?_]
  · rfl
  · simp only [evalOp]
    rw [show R.size + 4 + 2 * k = R.size + X.length by omega, rd_vals, rd_vals, rd_vals,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [X, headVals, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
    cases N.testBit k <;> rfl
  · simp only [evalOp]
    rw [show (#[] : Array Val) = ([] : List Val).toArray from rfl, rd_vals]
    simp only [X, headVals, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]; rfl

/-- The borrow's register holds `c_k`. -/
theorem rd_borrow (R : Array Val) (D : Digest) (N k : ℕ) (L : List Val) :
    rd (R ++ (headVals D N ++ (List.range 18).flatMap (bitVals N) ++
        (List.range k).flatMap (chainVals N)).toArray ++ L.toArray)
      (if k = 0 then R.size + 3 else R.size + 42 + 3 * (k - 1)) =
      .f (bF (borrow N k)) := by
  have h40 : (headVals D N ++ (List.range 18).flatMap (bitVals N)).length = 40 := by
    simp only [List.length_append, length_flatMap_const (bitVals_length N), headVals,
      List.length_cons, List.length_nil]
  split_ifs with hk
  · subst hk
    rw [rd_vals]; simp [headVals, bF, borrow]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show R.size + 42 + 3 * (j + 1 - 1) = R.size + (40 + (3 * j + 2)) by omega, rd_vals,
      List.getD_append _ _ _ _ (by
        rw [List.length_append, h40, length_flatMap_const (chainVals_length N)]; omega),
      List.getD_append_right _ _ _ _ (by omega), h40, Nat.add_sub_cancel_left,
      getD_flatMap (chainVals_length N) _ j 2 (by omega) (by norm_num)]
    rfl

/-- The borrow chain's three ops at `k`. -/
theorem run_chain (R : Array Val) (D : Digest) (N k : ℕ) (hk : k < 18) :
    pureRun impl κ inp
      [.addF (R.size + 5 + 2 * k) (if k = 0 then R.size + 3 else R.size + 42 + 3 * (k - 1)),
       .addF (R.size + 3) (R.size + 5 + 2 * k),
       .mulF (R.size + 41 + 3 * k) (if k = 0 then R.size + 3 else R.size + 42 + 3 * (k - 1))]
      (R ++ (headVals D N ++ (List.range 18).flatMap (bitVals N) ++
        (List.range k).flatMap (chainVals N)).toArray) [] =
      some (chainVals N k, true) := by
  set X := headVals D N ++ (List.range 18).flatMap (bitVals N) ++ (List.range k).flatMap (chainVals N)
  have hX : X.length = 40 + 3 * k := by
    simp only [X, List.length_append, length_flatMap_const (bitVals_length N),
      length_flatMap_const (chainVals_length N), headVals, List.length_cons, List.length_nil]
  have hbit : ∀ L : List Val, rd (R ++ X.toArray ++ L.toArray) (R.size + 5 + 2 * k) =
      .f (bF (N.testBit k)) := fun L => by
    rw [show R.size + 5 + 2 * k = R.size + (4 + (2 * k + 1)) by omega, rd_vals,
      List.getD_append _ _ _ _ (by omega)]
    simp only [X]
    rw [List.getD_append _ _ _ _ (by
        rw [List.length_append, length_flatMap_const (bitVals_length N)]; simp [headVals]; omega),
      List.getD_append_right _ _ _ _ (by simp [headVals]),
      show headVals D N = [.d D, .n N, .f 0, .f 1] from rfl]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
    rw [getD_flatMap (bitVals_length N) 18 k 1 hk (by norm_num)]; rfl
  have hone : ∀ L : List Val, rd (R ++ X.toArray ++ L.toArray) (R.size + 3) = .f 1 := fun L => by
    rw [rd_vals]; simp [X, headVals]
  have hc : ∀ L : List Val, rd (R ++ X.toArray ++ L.toArray)
      (if k = 0 then R.size + 3 else R.size + 42 + 3 * (k - 1)) = .f (bF (borrow N k)) :=
    fun L => rd_borrow R D N k L
  rw [pureRun_cons_val (v := .f (bF (lb N k))) ?_,
    pureRun_cons_val (v := .f (1 + bF (N.testBit k))) ?_,
    pureRun_cons_val (v := .f (bF (borrow N (k + 1)))) ?_]
  · rfl
  · simp only [evalOp]
    rw [hc, show R.size + 41 + 3 * k = R.size + (X.length + 1) by omega, rd_vals,
      List.getD_append_right _ _ _ _ (by omega), show X.length + 1 - X.length = 1 by omega]
    show Res.vals [Val.f ((1 + bF (N.testBit k)) * bF (borrow N k))] true = _
    rw [bF_mul]; rfl
  · simp only [evalOp]
    rw [hone, hbit]; rfl
  · simp only [evalOp]
    rw [show (#[] : Array Val) = ([] : List Val).toArray from rfl, hbit, hc]
    simp only [Val.toF]; rw [bF_add]; rfl

/-- **`lastOps` runs** (from registers `R`, `b = |R|`): it asks nothing, its flag is `true`, and it
appends `lastVals D` with `D` the digest at `stmt` byte 33. -/
theorem run_lastOps (so : ℕ) (R : Array Val) :
    pureRun impl κ inp (Rev4.lastOps so R.size) R [] =
      some (lastVals (digestAt inp.π (absOff 0 (so + 33))), true) := by
  set D := digestAt inp.π (absOff 0 (so + 33))
  set N := idxOfF 24 D 0
  have hA : pureRun impl κ inp [.piDigest 0 (so + 33), .idx (fun _ => R.size) (fun _ => 24) (fun _ => 0),
      .const (fun _ => .f 0), .const (fun _ => .f 1)] R [] = some (headVals D N, true) := by
    rw [pureRun_cons_val (v := .d D) (by simp only [evalOp]; rfl),
      pureRun_cons_val (v := .n N) (by
        simp only [evalOp]
        rw [show R.size = R.size + 0 from rfl, show ([] : List Val) ++ [Val.d D] = [.d D] from rfl,
          show (R ++ [Val.d D].toArray) = R ++ ([] : List Val).toArray ++ [Val.d D].toArray by simp,
          rd_vals]; rfl),
      pureRun_cons_val (v := .f 0) (by simp only [evalOp]),
      pureRun_cons_val (v := .f 1) (by simp only [evalOp])]
    rfl
  have hB := pureRun_flatMap impl κ inp R (headVals D N)
    (fun k => [.bitOf (R.size + 1) k, .selectHalf (R.size + 4 + 2 * k) (R.size + 2) (R.size + 3)])
    (bitVals N) 18 fun k _ => run_bits impl κ inp R D N k
  have hC := pureRun_flatMap impl κ inp R (headVals D N ++ (List.range 18).flatMap (bitVals N))
    (fun k => [.addF (R.size + 5 + 2 * k) (if k = 0 then R.size + 3 else R.size + 42 + 3 * (k - 1)),
       .addF (R.size + 3) (R.size + 5 + 2 * k),
       .mulF (R.size + 41 + 3 * k) (if k = 0 then R.size + 3 else R.size + 42 + 3 * (k - 1))])
    (chainVals N) 18 fun k hk => run_chain impl κ inp R D N k hk
  have hAB := pureRun_seq impl κ inp hA hB
  have := pureRun_seq impl κ inp hAB hC
  simpa [Rev4.lastOps, lastVals] using this

/-- Register `b + 2` (`lastOuts`' first) holds `0`. -/
theorem lastVals_zero (D : Digest) : (lastVals D).getD 2 default = .f 0 := by
  simp [lastVals, headVals]

/-- **Register `b + 40 + 3k` (`lastOuts`' `k + 1`-st) holds `L_k`.** -/
theorem lastVals_bit (D : Digest) {k : ℕ} (hk : k < 18) :
    (lastVals D).getD (40 + 3 * k) default = .f (bF (lb (idxOfF 24 D 0) k)) := by
  have h40 : (headVals D (idxOfF 24 D 0) ++
      (List.range 18).flatMap (bitVals (idxOfF 24 D 0))).length = 40 := by
    simp only [List.length_append, length_flatMap_const (bitVals_length _), headVals,
      List.length_cons, List.length_nil]
  rw [lastVals, List.getD_append_right _ _ _ _ (by omega), h40, Nat.add_sub_cancel_left,
    show 3 * k = 3 * k + 0 from rfl, getD_flatMap (chainVals_length _) 18 k 0 hk (by norm_num)]
  rfl

end Run

/-- **The log's `L` is the bits' number** (`lastOps`' outputs, read back by `lastAt`). -/
theorem lastL_sum (es : RecursionFast.Log) :
    lastL es = ∑ k ∈ range 18, if lb (nStmt es) k then 2 ^ k else 0 := by
  rw [lastSum]; rfl

end FR.Snd.P4a

end G6_FRSoundness4P4aLast

section G6_FRSoundness4P4aBridge

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.9 `finSh` (i), A.10 S1/S2; stage P4a pass 2).

/-!
# A segment's S bridges: `L`'s bits, S2's initial claim, S2's true sum

* **`testBit_lastL`**: bit `k < 18` of `lastL es` is `lastOps`' `L_k` (`lb`); so `lastBits` are the
  cube bits of `lastL` (**`lastBits_getD`**).
* **`eq_pad_last`**: `eq` at an 18-coordinate point zero-padded from `nb` and the bits of `L < 2^nb`
  is `eqAtR τ L`.
* **`c0S_seg`**: a segment's S2 initial claim (`shiftTargetS` on `bnd ‖ L`) is
  `eq(τ, L)·h̃(θ) + κ_s·s̃(θ)` (3.x's `c0S_eq` with the end at `L`).
-/

namespace FR.Snd.P4a
open RecursionFast Finset FR.Impl

/-! ## The bits of `L` -/

theorem sum_bits_lt (b : ℕ → Bool) : ∀ n, (∑ k ∈ range n, if b k then 2 ^ k else 0) < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, pow_succ]; have := sum_bits_lt b n; split_ifs <;> omega

theorem testBit_sum_bits (b : ℕ → Bool) : ∀ n j,
    (∑ k ∈ range n, if b k then 2 ^ k else 0).testBit j = (decide (j < n) && b j)
  | 0, j => by simp
  | n + 1, j => by
    have e : (∑ k ∈ range (n + 1), if b k then 2 ^ k else 0) =
        2 ^ n * (if b n then 1 else 0) + ∑ k ∈ range n, if b k then 2 ^ k else 0 := by
      rw [sum_range_succ]; split_ifs <;> ring
    rw [e, Nat.testBit_two_pow_mul_add _ (sum_bits_lt b n), testBit_sum_bits b n]
    by_cases h : j < n
    · rw [if_pos h]; simp [h, show j < n + 1 by omega]
    · rw [if_neg h]
      obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by omega⟩
      rw [Nat.add_sub_cancel_left]
      rcases d with _ | d
      · cases b n <;> simp
      · cases b n <;> simp [Nat.testBit_succ]

/-- **Bit `k` of `L` is `lastOps`' `L_k`.** -/
theorem testBit_lastL (es : Log) {k : ℕ} (hk : k < 18) : (lastL es).testBit k = lb (nStmt es) k := by
  have h := testBit_sum_bits (fun j => lb (nStmt es) j) 18 k
  rw [decide_eq_true hk, Bool.true_and, ← lastL_sum] at h
  exact h

theorem lastL_lt (es : Log) : lastL es < 2 ^ 18 := Nat.mod_lt _ (by norm_num)

/-- `lastBits` are the cube bits of `lastL`. -/
theorem lastBits_getD (es : Log) {k : ℕ} (hk : k < 18) :
    (lastBits es).getD k 0 = if (lastL es).testBit k then 1 else 0 := by
  rw [testBit_lastL es hk, lastBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rfl

/-! ## `eq` at the padded point and `L` -/

theorem pad_getD {nb : ℕ} (τ : List F) (hτ : τ.length = nb) (l : ℕ) :
    (τ ++ List.replicate (18 - nb) 0).getD l 0 = if l < nb then τ.getD l 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
    split_ifs <;> rfl

/-- **`eq((τ ‖ 0), bits L) = eq(τ, L)`** for `L < 2^nb`. -/
theorem eq_pad_last {nb : ℕ} (hnb : nb ≤ 18) (τ : List F) (hτ : τ.length = nb) {Lb : ℕ}
    (hL : Lb < 2 ^ nb) :
    eq (ptOf 18 (τ ++ List.replicate (18 - nb) 0))
        (fun l : Fin 18 => if Lb.testBit l then 1 else 0) = eqAtR (ptOf nb τ) Lb := by
  set g : ℕ → F := fun l => (τ ++ List.replicate (18 - nb) 0).getD l 0 *
      (if Lb.testBit l then 1 else 0) +
    (1 - (τ ++ List.replicate (18 - nb) 0).getD l 0) * (1 - if Lb.testBit l then 1 else 0)
  set h : ℕ → F := fun l => if Lb.testBit l then τ.getD l 0 else 1 - τ.getD l 0
  calc eq (ptOf 18 (τ ++ List.replicate (18 - nb) 0)) (fun l : Fin 18 => if Lb.testBit l then 1 else 0)
      = ∏ l : Fin 18, g l := rfl
    _ = ∏ l ∈ range 18, g l := Fin.prod_univ_eq_prod_range g 18
    _ = ∏ l ∈ range nb, g l := by
        rw [← prod_range_mul_prod_Ico _ hnb]
        have h1 : ∏ l ∈ Ico nb 18, g l = 1 := by
          refine prod_eq_one fun l hl => ?_
          have hl' := (mem_Ico.1 hl).1
          have ht : Lb.testBit l = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) hl'))
          simp only [g, pad_getD τ hτ, ht, if_neg (show ¬ l < nb by omega)]; simp
        rw [h1, mul_one]
    _ = ∏ l ∈ range nb, h l := by
        refine prod_congr rfl fun l hl => ?_
        have hl' := mem_range.1 hl
        simp only [g, h, pad_getD τ hτ, if_pos hl']
        split_ifs <;> ring
    _ = eqAtR (ptOf nb τ) Lb := (Fin.prod_univ_eq_prod_range h nb).symm

/-! ## S2's initial claim at a segment -/

theorem nbC_le (κ : CKind) : nbC κ ≤ 18 := by
  unfold nbC; rcases κ.m_mem with h | h | h <;> omega

/-- **A segment's S2 initial claim**: `eq(τ, L)·h̃(θ) + κ_s·s̃(θ)` (the end at block `L`). -/
theorem c0S_seg {es : Log} (hn : (kindOfC es).isNode = false)
    (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    c0S es = eqAtR (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (lastL es) *
        thS (ptOf 10 (thL es)) (hbL (kindOfC es) es) +
      ksL es * thS (ptOf 10 (thL es)) (sbL (kindOfC es) es) := by
  rw [c0S, pad18, shiftTargetS, shiftTargetAt, ptA_toArray, ptA_toArray, mle_digTbl, mle_digTbl]
  generalize hκ : kindOfC es = κ at hn hL ⊢
  have hb : (bndL κ es).length = 4 := by unfold bndL; split_ifs <;> rfl
  have hg : ∀ j < 4, (bndL κ es ++ endBits κ es).toArray.getD j 0 = (bndL κ es).getD j 0 :=
    fun j hj => by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show j < (bndL κ es).length by omega)]
  have hlast : lastOf (bndL κ es ++ endBits κ es).toArray =
      fun l : Fin 18 => if (lastL es).testBit l then 1 else 0 := by
    funext l
    rw [lastOf, ← lastBits_getD es l.isLt]
    simp only [endBits, hn, Bool.false_eq_true, if_false, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show (bndL κ es).length ≤ 4 + l.val by omega), hb,
      Nat.add_sub_cancel_left]
  have htau : (tauL κ es).length = nbC κ := by simp [tauL]
  rw [hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num), hlast,
    eq_pad_last (nbC_le κ) _ htau hL]
  rfl

/-! ## T4's witness is the dooms' `zw` -/

/-- **T4's decoded witness is Boolean** (`segHolds_of_truths`' `hbool` at `zw := T4.zW`). -/
theorem zW_bool (κ : CKind) (L es : Log) (b : ℕ) : BlockR1CS.IsBool (T4.zW κ L es b) :=
  unpack_boolean _ _

end FR.Snd.P4a

end G6_FRSoundness4P4aBridge

section G6_FRSoundness4TailFront

-- New for `flock-recursive` (BLUEPRINT A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessFront` Part A (reads and the frame) to revision 4.1's `seq4` (namespace `FR.Snd.T4`,
-- see `FRSoundness4TailStep`). Parts B–D (3.x's node layout, B′ cells) are not copied.

/-!
# Reads and the frame at `seq4` (T4)

`FRSoundnessFront` Part A over T4's `Same`, `G.IsChain`, `fsRnd4`, `fsRanges4`, `phOf4` and
`p1Start` (`= 332`): **`Reads p P`**, its locality and stability (`Reads.append/ext1/ext`,
`Reads.stab`, `Reads.chain`), the single-squeeze and multi-squeeze frames **`card_frame`**,
**`esc_msD_frame`**, and **`frontLocal_of`**. They are the front's tools for its `FrontObl`
(P4a, P4b); this module exports them at revision 4.1.
-/

/-! # Port of `FRSoundnessFront` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: reads and the frame -/

/-- **`P` reads only what lies before position `p`** (entries and the words of earlier caps), on
chains of at least `p` entries. -/
def Reads (p : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L es L' es', p ≤ es.length → p ≤ es'.length → Same L es L' es' p → (P L es ↔ P L' es')

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

theorem ext_eq_append (es : Log) : ∀ as : List Digest, ∃ ys, ext es as = es ++ ys := by
  intro as
  induction as using List.reverseRecOn with
  | nil => exact ⟨[], by simp [ext_nil]⟩
  | append_singleton as a ih =>
    obtain ⟨ys, hy⟩ := ih
    exact ⟨ys ++ [(squeezeQ (lastAns (ext es as)), a)], by rw [ext_append, ext1, hy]; simp⟩

theorem Reads.ext (h : Reads p P) (L es : Log) (as : List Digest) (hp : p ≤ es.length) :
    P L (ext es as) ↔ P L es := by
  obtain ⟨ys, hy⟩ := ext_eq_append es as
  rw [hy]; exact h.append L es ys hp

/-- Stability (`hstab`) on `hloc_of`'s extensions. -/
theorem Reads.stab (h : Reads p P) {L : Log} (hb : ¬ Bad L) {i : ℕ} (hci : G.IsChain L i) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L i)) X) (hp : p ≤ X.length) :
    P (L.take i) X ↔ P L X :=
  h _ X L X hp hp ((same_stabX hb hci hX).mono hp)

/-- Stability on the chain itself (`FrontChainStab`). -/
theorem Reads.chain (h : Reads p P) {L : Log} (hb : ¬ Bad L) {j : ℕ} (hci : G.IsChain L j)
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
theorem esc_msD_frame {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {Bg U U' : Log → Log → Prop} (hBg : Reads (s0 + 1) Bg)
    (hprev : Dk (phOf4 s0) = fun L es => Bg L es ∨ U L es)
    (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) (fun L es => Bg L es ∨ U' L es) s0 r)
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

/-! ## Controls (T4) -/

/-- **Control (negative)**: a predicate of the entry count does not read before position `0`
(`Same … 0` relates any two chains), so `Reads` is not vacuous. -/
theorem not_reads_length : ¬ Reads 0 fun _ es => es.length = 1 := fun h => by
  have := (h [] [(ByteArray.empty, 0)] [] [] (Nat.zero_le _) (Nat.zero_le _)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩).mp rfl
  simp at this

end FR.Snd.T4

end G6_FRSoundness4TailFront

section G6_FRSoundness4P4aS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.10 S1/S2; stage P4a pass 3 (P4c)).

/-!
# S1 at revision 4.1: S2's true sum, the residual, S1's charge

* **`trueSum_TS_seg`**: a segment's S2 true sum (`TS`, the masked weight at `L = lastL`) is its
  initial claim `c0S` plus the batched residual of `resSeg` (`sh_sum_seg`, `c0S_seg`).
* **`SNode`**: what a node kind's S2 law must supply (its residual tables, their count `J`, the sum
  law, the truth's failure leaves a nonzero table, congruence): S-E's, a parameter (S-G13 F3).
* **`resS4`**, **`TR4`**, **`trueSum_TS4`**, **`tr_ne4`**: the residual by kind; a failed S truth
  leaves a nonzero residual table.
* **`ZwSame`**: the witness reads the log before position 3 (level 0's word and the seed);
  **`zwSame_zW`**: T4's `zW` does.
* **`s1_hfin4`**: S1's charge at `seq4`'s `(98, 15)`, `≤ (nb + 10 + J − 1)/2^128`.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The witness reads the log before position 3 -/

/-- **`zw` reads only the seed and the level-0 word** (T4's `Same` at 3). -/
def ZwSame (zw : Wit) : Prop :=
  ∀ κ L es L' es' p, T4.Same L es L' es' p → 3 ≤ p → zw κ L es = zw κ L' es'

theorem capPos_zero4 : T4.capPos 0 = 2 := by
  have h := congrArg (·[0]?) T4.capPos_eq
  simp only [List.getElem?_map, List.getElem?_range (show 0 < 5 by norm_num), Option.map_some,
    List.getElem?_cons_zero, Option.some.injEq] at h
  exact h

/-- **T4's witness `z = unpack f⁽⁰⁾` reads before position 3.** -/
theorem zwSame_zW : ZwSame T4.zW := fun κ L es L' es' p h hp => by
  funext b
  simp only [T4.zW, T4.fF, T4.fTab_same h (i := 0) (by norm_num) κ (by rw [capPos_zero4]; omega)]

/-! ## A segment's S2 true sum -/

section Sum
variable (wN : CKind → Log → ℕ → ℕ → F) (zw : Wit)

/-- **A segment's residual on the log** (`resSeg` at `L = lastL`, the statement's boundary). -/
def resSegL (κ : CKind) (L es : Log) : ℕ → ℕ → ℕ → F :=
  resSeg (nbC κ) (lastL es) (zNodeC zw κ L es) (sbL κ es) (hbL κ es)

theorem sum_TS (L es : Log) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        wS wN (kindOfC es) es y q * zNodeC zw (kindOfC es) L es y q := by
  rw [nrS, TS, prod_trueSum]
  rw [Fin.sum_univ_eq_sum_range (fun i => wS wN (kindOfC es) es (i % 2 ^ nbC (kindOfC es))
      (i / 2 ^ nbC (kindOfC es)) * zNodeC zw (kindOfC es) L es (i % 2 ^ nbC (kindOfC es))
        (i / 2 ^ nbC (kindOfC es))), sum_range_pow_add]
  exact sum_congr rfl fun q _ => sum_congr rfl fun y hy => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hy); rw [h1, h2]

/-- **A segment's S2 true sum is its initial claim plus the residual** (B-12: the end at `L`, the
successor masked there). -/
theorem trueSum_TS_seg {L es : Log} (hn : (kindOfC es).isNode = false)
    (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) 2 (resSegL zw (kindOfC es) L es)
        (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (ptOf 10 (thL es)) (ksL es) := by
  rw [sum_TS, c0S_seg hn hL]
  simp only [wS, hn, Bool.false_eq_true, if_false, resSegL]
  exact sh_sum_seg hL _ _ _ _ _ _

end Sum

/-! ## The node's S2 law (a parameter) and the residual by kind -/

/-- **A node kind's S2 law** (S-E's, S-G13 F3): `J` residual tables `res`, whose batched sum is the
true sum minus the initial claim, one of which is nonzero when the node's S truth fails; they read
the log before S1's first squeeze. -/
structure SNode (wN : CKind → Log → ℕ → ℕ → F) (truthSN : CKind → Log → Log → Prop) (zw : Wit)
    where
  nJ : CKind → ℕ
  res : CKind → Log → Log → ℕ → ℕ → ℕ → F
  nJ_pos : ∀ κ, 1 ≤ nJ κ
  nJ_le : ∀ κ, nbC κ + 10 + (nJ κ - 1) ≤ 239
  sum : ∀ L es, (kindOfC es).isNode = true →
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) (nJ (kindOfC es)) (res (kindOfC es) L es)
        (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (ptOf 10 (thL es)) (ksL es)
  ne : ∀ κ L es, κ.isNode = true → ¬ truthSN κ L es →
    ∃ j < nJ κ, ∃ u < 2 ^ nbC κ, ∃ q < 2 ^ 10, res κ L es j u q ≠ 0
  same : ∀ κ L es L' es' p, T4.Same L es L' es' p → 99 ≤ p → res κ L es = res κ L' es'
  truth_same : ∀ κ L es L' es' p, T4.Same L es L' es' p → 3 ≤ p →
    (truthSN κ L es ↔ truthSN κ L' es')

section Kind
variable {wN : CKind → Log → ℕ → ℕ → F} {truthSN : CKind → Log → Log → Prop} {zw : Wit}
  (hN : SNode wN truthSN zw)

/-- The residual tables' count by kind. -/
def nJ4 (κ : CKind) : ℕ := if κ.isNode then hN.nJ κ else 2

/-- **The S residual by kind**: a node's `hN.res`, a segment's `resSegL`. -/
def resS4 (κ : CKind) (L es : Log) : ℕ → ℕ → ℕ → F :=
  if κ.isNode then hN.res κ L es else resSegL zw κ L es

/-- The residual tables `R_j` as arrays (index `u + 2^nb q`). -/
noncomputable def TR4 (κ : CKind) (L es : Log) (j : ℕ) : Array F :=
  Array.ofFn (n := 2 ^ (nbC κ + 10)) fun i => resS4 hN κ L es j (i.val % 2 ^ nbC κ) (i.val / 2 ^ nbC κ)

theorem TR4_size (κ : CKind) (L es : Log) (j : ℕ) : (TR4 hN κ L es j).size = 2 ^ (nbC κ + 10) := by
  simp [TR4]

theorem TR4_mle (κ : CKind) (L es : Log) (j : ℕ) (l : List F) :
    mle (tbl (nbC κ + 10) (TR4 hN κ L es j)) (ptOf (nbC κ + 10) l) =
      ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbC κ),
        eqAtR (ptOf (nbC κ) l) u * eqAtR (ptOf 10 (l.drop (nbC κ))) q * resS4 hN κ L es j u q := by
  rw [TR4]
  refine (mle_ofFn_split _ 10 (fun i => resS4 hN κ L es j (i % 2 ^ nbC κ) (i / 2 ^ nbC κ)) l).trans ?_
  exact sum_congr rfl fun q _ => sum_congr rfl fun u hu => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hu); rw [h1, h2]

/-- **S2's true sum is its initial claim plus the residual**, by kind (a segment's `L` among its
blocks). -/
theorem trueSum_TS4 {L es : Log}
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) (nJ4 hN (kindOfC es)) (resS4 hN (kindOfC es) L es)
        (ptOf (nbC (kindOfC es)) (tauL (kindOfC es) es)) (ptOf 10 (thL es)) (ksL es) := by
  unfold nJ4 resS4
  cases hn : (kindOfC es).isNode
  · simp only [Bool.false_eq_true, if_false]; exact trueSum_TS_seg wN zw hn (hL hn)
  · simp only [if_true]; exact hN.sum L es hn

/-- **A failed S truth leaves a nonzero residual table.** -/
theorem tr_ne4 {L es : Log} (h : ¬ truthS truthSN zw L es) :
    ∃ j < nJ4 hN (kindOfC es), tbl (nbC (kindOfC es) + 10) (TR4 hN (kindOfC es) L es j) ≠ 0 ∧
      ((kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) := by
  generalize hκ : kindOfC es = κ
  have key : ∀ j u q, u < 2 ^ nbC κ → q < 2 ^ 10 → resS4 hN κ L es j u q ≠ 0 →
      tbl (nbC κ + 10) (TR4 hN κ L es j) ≠ 0 := fun j u q hu hq hne he => by
    have hi : u + 2 ^ nbC κ * q < 2 ^ (nbC κ + 10) := by
      rw [pow_add]; nlinarith
    have := congrFun he ⟨u + 2 ^ nbC κ * q, hi⟩
    obtain ⟨h1, h2⟩ := idx_split (q := q) hu
    simp only [TR4, tbl_ofFn, Pi.zero_apply, h1, h2] at this
    exact hne this
  unfold truthS at h
  rw [hκ] at h
  unfold nJ4
  cases hn : κ.isNode
  · simp only [hn, Bool.false_eq_true, if_false, Classical.not_imp] at h ⊢
    obtain ⟨hL, hS⟩ := h
    obtain ⟨j, hj, u, hu, q, hq, hne⟩ := res_ne_seg hL hS
    have hne' : resS4 hN κ L es j u q ≠ 0 := by simp only [resS4, hn]; exact hne
    exact ⟨j, hj, key j u q hu hq hne', fun _ => hL⟩
  · simp only [hn, if_true] at h ⊢
    obtain ⟨j, hj, u, hu, q, hq, hne⟩ := hN.ne κ L es hn h
    have hne' : resS4 hN κ L es j u q ≠ 0 := by simp only [resS4, hn, if_true]; exact hne
    exact ⟨j, hj, key j u q hu hq hne', fun h => absurd h (by simp)⟩

end Kind

/-! ## Reads -/

section Reads
variable {L es L' es' : Log} {p : ℕ}

theorem nStmt_congr (h : Agree es es' p) (hp : 2 ≤ p) : nStmt es = nStmt es' := by
  simp only [nStmt, msgAt_congr h (show 1 < p by omega)]

theorem lastL_congr (h : Agree es es' p) (hp : 2 ≤ p) : lastL es = lastL es' := by
  simp only [lastL, nStmt_congr h hp]

theorem bndL_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) : bndL κ es = bndL κ es' := by
  simp only [bndL, h 0 (by omega), msgAt_congr h (show 1 < p by omega)]

theorem sbL_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) : sbL κ es = sbL κ es' := by
  funext σ; simp only [sbL, bndL_congr4 h hp κ]

theorem hbL_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) : hbL κ es = hbL κ es' := by
  funext σ; simp only [hbL, bndL_congr4 h hp κ]

theorem s1_congr4 (h : Agree es es' p) (hp : 114 ≤ p) (κ : CKind) :
    tauL κ es = tauL κ es' ∧ thL es = thL es' ∧ ksL es = ksL es' := by
  have hn := nbC_le κ
  refine ⟨List.map_congr_left fun l hl => coS_congr h (by simp at hl; omega),
    List.map_congr_left fun l hl => coS_congr h (by simp at hl; omega), coS_congr h (by omega)⟩

theorem endBits_congr4 (h : Agree es es' p) (hp : 2 ≤ p) (κ : CKind) :
    endBits κ es = endBits κ es' := by
  simp only [endBits, lastBits, nStmt_congr h hp]

theorem c0S_agree4 (h : Agree es es' p) (hp : 114 ≤ p) : c0S es = c0S es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by omega))
  obtain ⟨h1, h2, h3⟩ := s1_congr4 h hp (kindOfC es)
  simp only [c0S, hk, h2, h3, bndL_congr4 h (by omega), endBits_congr4 h (by omega)]
  rw [← hk, h1]

variable {zw : Wit}

theorem zNodeC_same (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    zNodeC zw κ L es = zNodeC zw κ L' es' := by
  funext b q; simp only [zNodeC, hz κ L es L' es' p h hp]

theorem resSegL_same (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    resSegL zw κ L es = resSegL zw κ L' es' := by
  simp only [resSegL, zNodeC_same hz h hp, lastL_congr h.1 (by omega), sbL_congr4 h.1 (by omega),
    hbL_congr4 h.1 (by omega)]

theorem resS4_same {wN : CKind → Log → ℕ → ℕ → F} {truthSN : CKind → Log → Log → Prop}
    (hN : SNode wN truthSN zw) (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 99 ≤ p)
    (κ : CKind) : resS4 hN κ L es = resS4 hN κ L' es' := by
  simp only [resS4, resSegL_same hz h (by omega), hN.same κ L es L' es' p h hp]

/-- **The S truth reads before position 3.** -/
theorem truthS_same4 {truthSN : CKind → Log → Log → Prop}
    (hT : ∀ κ L es L' es' p, T4.Same L es L' es' p → 3 ≤ p → (truthSN κ L es ↔ truthSN κ L' es'))
    (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) :
    truthS truthSN zw L es ↔ truthS truthSN zw L' es' := by
  have hk := h.kind (by omega)
  simp only [truthS, hk, zNodeC_same hz h hp, lastL_congr h.1 (by omega),
    sbL_congr4 h.1 (by omega), hbL_congr4 h.1 (by omega), hT _ L es L' es' p h hp]

end Reads

/-! ## S1's charge -/

/-- **S's positions at `seq4`** (identity below 170): S1 is the range `(98, 15)` (phase 11), S2's
rounds from 114 (phase 12), Lr1 from 170 (phase 13). -/
theorem s_unit_pos4 :
    (98, 15) ∈ fsRanges4 ∧ phOf4 98 = 10 ∧ phOf4 99 = 11 ∧ phOf4 113 = 11 ∧ phOf4 114 = 12 ∧
    phOf4 169 = 12 ∧ phOf4 170 = 13 := by
  refine ⟨by rw [fsRanges4_eq]; simp, ?_⟩
  have hph : ∀ q, phOf4 q = (fsStarts4.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts4_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem selC_coords4 (κ : CKind) (X : Log) :
    ptOf (nbC κ) (selC (nbC κ) (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i)) =
        ptOf (nbC κ) (tauL κ X) ∧
      ptOf 10 ((selC (nbC κ) (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i)).drop (nbC κ)) =
        ptOf 10 (thL X) := by
  have hn := nbC_le κ
  set cl := List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i
  have hd : (selC (nbC κ) cl).drop (nbC κ) = (cl.drop 18).take 10 := by
    rw [selC, List.drop_left' (by simp [cl]; omega)]
  refine ⟨funext fun l => ?_, funext fun l => ?_⟩
  · have hl := l.isLt
    simp only [ptOf, selC, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [cl]; omega), List.getElem?_take, if_pos hl,
      ← List.getD_eq_getElem?_getD, coordS_getD X (by omega)]
    simp [tauL, hl]
  · have hl := l.isLt
    simp only [ptOf, hd, List.getD_eq_getElem?_getD]
    rw [List.getElem?_take, if_pos hl, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
      coordS_getD X (by omega)]
    simp [thL, hl]

open Classical in
/-- **S1's charge at `seq4`** (A.10 S1, `(nb + 10 + J − 1)/2^128`): with the doom of S1's entry
`Bg ∨ ¬ truthS` and its final doom `Bg ∨ S2Bad`. -/
theorem s1_hfin4 {wN : CKind → Log → ℕ → ℕ → F} {truthSN : CKind → Log → Log → Prop} {zw : Wit}
    (hN : SNode wN truthSN zw) (hz : ZwSame zw) {Dk : ℕ → Log → Log → Prop}
    {Bg : Log → Log → Prop} (hBg : T4.Reads 99 Bg)
    (hprev : Dk (phOf4 98) = fun L es => Bg L es ∨ ¬ truthS truthSN zw L es)
    (hfin : Dk (phOf4 99) = msD (Dk (phOf4 98)) (fun L es => Bg L es ∨ S2Bad wN zw L es) 98 15)
    (L es₀ : Log) (hl : es₀.length = 99) :
    condCount (DPos (T4.Dp Dk)) L es₀ 15 [] ≤ deltaR := by
  set κ := kindOfC es₀
  have hn := nbC_le κ
  have hJ : 1 ≤ nJ4 hN κ := by unfold nJ4; split_ifs; exact hN.nJ_pos κ; norm_num
  have hJ' : nbC κ + 10 + (nJ4 hN κ - 1) ≤ 239 := by
    unfold nJ4; split_ifs; exact hN.nJ_le κ; omega
  by_cases hd : ¬ truthS truthSN zw L es₀
  · obtain ⟨j, hj, hne, hL⟩ := tr_ne4 hN hd
    have h0 : DoomS (nbC κ) (nJ4 hN κ) (TR4 hN κ L es₀) [] := by
      unfold DoomS
      rw [if_pos (by simp)]
      refine ⟨j, hj, ?_⟩
      have hs : selC (nbC κ) ([] : List F) = [] := by simp [selC]
      unfold mlDoom
      rw [hs]
      exact hne
    refine (seq_round_le hl (DoomS (nbC κ) (nJ4 hN κ) (TR4 hN κ L es₀)) (bS (nbC κ) (nJ4 hN κ))
      (fun l hdl => doomS_step hn hJ (TR4_size hN κ L es₀) l hdl) h0 fun as has he => ?_).trans
      (coord_le_deltaR ?_)
    · obtain ⟨-, -, hnf⟩ := T4.esc_msD_frame s_unit_pos4.1 hBg hprev hfin hl as has he
      set X := ext es₀ as
      obtain ⟨ys, hy⟩ := T4.ext_eq_append es₀ as
      have hS : T4.Same L X L es₀ 99 := by
        rw [show X = es₀ ++ ys from hy, ← hl]; exact T4.same_append L es₀ ys
      have hk : kindOfC X = κ := hS.kind (by norm_num)
      have hLX : (kindOfC X).isNode = false → lastL X < 2 ^ nbC (kindOfC X) := by
        rw [hk, lastL_congr hS.1 (by norm_num)]; exact hL
      have hres := trueSum_TS4 hN (L := L) hLX
      rw [not_not.mp hnf |>.symm] at hres
      have hr0 := add_eq_left.mp hres.symm
      rw [hk, resS4_same hN hz hS le_rfl] at hr0
      unfold resSum at hr0
      unfold DoomS
      rw [if_neg (by simp), not_not]
      simp only [TR4_mle]
      rw [(selC_coords4 κ X).1, (selC_coords4 κ X).2, coordS_getD X (by norm_num : 28 < 30)]
      exact hr0
    · rw [sum_bS hn]; exact hJ'
  · rw [condCount_eq_zero fun as has he =>
      hd (T4.esc_msD_frame s_unit_pos4.1 hBg hprev hfin hl as has he).2.1]
    exact zero_le

end FR.Snd.P4a

end G6_FRSoundness4P4aS

section G6_FRSoundness4P4aFin

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.8 `targetS`, A.9 `finSh`; stage P4a pass 3 (P4c)).

/-!
# A segment's finals on the specifications: `finSh` (ii) and Z2's `P^e` (B-12)

* **`eqAtR_padN`**: `eq` at a point zero-padded from `a` to `n` coordinates is `eq` at the short
  point on `[0, 2^a)` and `0` past it. Both bridges below sum the padded coordinates out with it.
* **`final_seg`**: a segment's S2 weight (`wSeg`, the successor masked at `L`) has extension
  `E·slotW₀ + (Sh + κ_s·E₀)·slotW₁` at S2's point, with `(E, Sh, E₀)` the segment's `shiftMask`
  specification (`Rev4.shiftSegS`) at the padded points and `L`'s bits (3.x's `final_leaf`).
  **`wSumSeg`** is that value on the log, **`wSumSeg_eq`** the extension of `wS` at `rbL`, `rpL`.
  `claimSL4`, **`oSh4`** (`finSh` (ii)'s binding `c_Sh = (w_out + w_in)·v`; a node's weight value
  `wNS` is a parameter).
* **`peL_seg`**: Z2's `P^e` at a segment is `Rev4.targetSSegS` at the verifier's operand (Z1's
  `m − 13` coordinates zero-padded to 19 entries, then `L`'s bits).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## `eq` at a zero-padded point -/

theorem eqAtR_padN {a n : ℕ} (han : a ≤ n) (xs : List F) (hx : xs.length = a) {i : ℕ}
    (hi : i < 2 ^ n) :
    eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i = if i < 2 ^ a then eqAtR (ptOf a xs) i else 0 := by
  set g : ℕ → F := fun l => if i.testBit l then (xs ++ List.replicate (n - a) 0).getD l 0
    else 1 - (xs ++ List.replicate (n - a) 0).getD l 0
  have hp : ∀ l, (xs ++ List.replicate (n - a) 0).getD l 0 = if l < a then xs.getD l 0 else 0 :=
    fun l => by
      simp only [List.getD_eq_getElem?_getD]
      split_ifs with h
      · rw [List.getElem?_append_left (by omega)]
      · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
        split_ifs <;> rfl
  have e : eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i = ∏ l ∈ range n, g l :=
    Fin.prod_univ_eq_prod_range g n
  rw [e, ← prod_range_mul_prod_Ico _ han]
  split_ifs with hia
  · have h1 : ∏ l ∈ Ico a n, g l = 1 := prod_eq_one fun l hl => by
      have ht : i.testBit l = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hia (Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 hl).1))
      simp only [g, hp, ht, if_neg (show ¬ l < a by have := (mem_Ico.1 hl).1; omega)]; simp
    rw [h1, mul_one]
    refine (prod_congr rfl fun l hl => ?_).trans
      (Fin.prod_univ_eq_prod_range (fun l => if i.testBit l then xs.getD l 0 else 1 - xs.getD l 0) a).symm
    simp only [g, hp, if_pos (mem_range.1 hl)]
  · obtain ⟨l, hl, hb⟩ : ∃ l ∈ Ico a n, i.testBit l = true := by
      by_contra hc
      push Not at hc
      refine hia (Nat.lt_pow_two_of_testBit i fun l hl => ?_)
      by_cases hln : l < n
      · simpa using hc l (mem_Ico.2 ⟨hl, hln⟩)
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [prod_eq_zero hl (by simp only [g, hp, hb, if_true, if_neg (show ¬ l < a by
      have := (mem_Ico.1 hl).1; omega)]), mul_zero]

/-- **Summing over a zero-padded point** is summing over the short point. -/
theorem sum_eqAtR_padN {a n : ℕ} (han : a ≤ n) (xs : List F) (hx : xs.length = a) (g : ℕ → F) :
    ∑ i ∈ range (2 ^ n), eqAtR (ptOf n (xs ++ List.replicate (n - a) 0)) i * g i =
      ∑ i ∈ range (2 ^ a), eqAtR (ptOf a xs) i * g i := by
  rw [sum_congr rfl fun i hi => by rw [eqAtR_padN han xs hx (mem_range.1 hi)]]
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext i; simp only [mem_filter, mem_range]
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) han
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-! ## `finSh` (ii) at a segment -/

/-- The masked successor is the unmasked one plus the link at `L` (characteristic two). -/
theorem shSeg_eq {nb : ℕ} (τ : Fin nb → F) (κ : F) (Lb y : ℕ) :
    shSeg τ κ Lb y = shL τ κ y + if y = Lb + 1 then eqAtR τ Lb else 0 := by
  unfold shSeg shL
  by_cases h : y = Lb + 1
  · subst h
    have h1 : ¬ (1 ≤ Lb + 1 ∧ Lb + 1 - 1 ≠ Lb) := by omega
    have h2 : 1 ≤ Lb + 1 := by omega
    rw [if_neg h1, if_pos h2, if_pos rfl, Nat.add_sub_cancel]
    linear_combination (-(eqAtR τ Lb)) * CharTwo.two_eq_zero (R := F)
  · rw [if_neg h, add_zero]
    by_cases h1 : 1 ≤ y
    · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
    · rw [if_neg (by omega), if_neg h1]

theorem eqPoint_zero18 (rb : List F) (hrb : rb.length = 18) :
    eqPoint (Array.replicate 18 0) rb.toArray = eqAtR (ptOf 18 rb) 0 := by
  have h := eq_zero_pt rb hrb
  rwa [show (List.replicate 18 (0 : F)).toArray = Array.replicate 18 0 from rfl] at h

/-- **A segment's final value** (A.9 `finSh` (ii) with B-12's `shiftMask`): the masked weight's
extension at `(r_blk, r_pos)` is `E·slotW₀ + (Sh + κ_s E₀)·slotW₁` on `shiftSegS` at the padded
points and the operand's last block `L`. -/
theorem final_seg {nb : ℕ} (hnb : nb ≤ 18) (τs rb bits : List F) (hτ : τs.length = nb)
    (hrb : rb.length = nb) {Lb : ℕ} (hL : Lb < 2 ^ nb)
    (hbits : Rev4.lastAt (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray 18 = Lb)
    (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb),
        eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q =
      (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
          (rb ++ List.replicate (18 - nb) 0).toArray).1 * slotWS 0 θ rp +
        ((Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.1 +
          κ * (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.2) * slotWS 1 θ rp := by
  set τP := τs ++ List.replicate (18 - nb) 0
  set rP := rb ++ List.replicate (18 - nb) 0
  have hτP : τP.length = 18 := by simp [τP, hτ]; omega
  have hrP : rP.length = 18 := by simp [rP, hrb]; omega
  have hA : ptA 18 (τP ++ bits).toArray = ptOf 18 τP := funext fun l => by
    simp only [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.val < τP.length by omega)]
  have hB : ptA 18 rP.toArray = ptOf 18 rP := ptA_toArray _ _
  -- the three components
  have h1 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).1 = eqPoint τP.toArray rP.toArray := by
    rw [eqPoint_eq, List.size_toArray, hτP, ptA_toArray, ptA_toArray]
    simp only [Rev4.shiftSegS, hA, hB]
  have hmle : shiftMle 18 (ptOf 18 τP) (ptOf 18 rP) = shiftEqS τP.toArray rP.toArray := by
    rw [← shiftEq_meets _ _ (by simp [hτP, hrP]), shiftEqI, List.toList_toArray, List.toList_toArray,
      shiftPair_eq 18 τP rP hτP hrP]
  have hc : (if Lb + 1 < 2 ^ 18 then eqAtR (ptOf 18 τP) Lb * eqAtR (ptOf 18 rP) (Lb + 1) else 0) =
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    have h18 : 2 ^ nb ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hnb
    rw [eqAtR_padN hnb τs hτ (by omega), if_pos hL]
    by_cases h : Lb + 1 < 2 ^ nb
    · rw [if_pos (by omega), if_pos h, eqAtR_padN hnb rb hrb (by omega), if_pos h]
    · rw [if_neg h]
      split_ifs with h'
      · rw [eqAtR_padN hnb rb hrb h', if_neg h, mul_zero]
      · rfl
  have h2 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.1 = shiftEqS τP.toArray rP.toArray +
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    simp only [Rev4.shiftSegS, hA, hB, hbits, hmle]
    rw [← hc]
  have h3 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.2 =
      eqPoint (Array.replicate 18 0) rP.toArray := by
    rw [eqPoint_zero18 rP hrP]; simp only [Rev4.shiftSegS, hB]
  rw [h1, h2, h3]
  -- the masked weight is the leaf weight plus the link at `L`
  have hw : ∀ y q, wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q = wLeaf (ptOf nb τs) (ptA 10 θ) κ y q +
      (if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) * slotT (ptA 10 θ) 520 q := fun y q => by
    simp only [wSeg, wLeaf, shSeg_eq]; ring
  simp only [hw, mul_add, sum_add_distrib]
  rw [final_leaf hnb τs rb hτ hrb θ rp κ]
  have hlink : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
      eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
        slotT (ptA 10 θ) 520 q) =
      (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
        slotWS 1 θ rp := by
    have e : ∀ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
        eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
          slotT (ptA 10 θ) 520 q) =
        (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
          (eqAtR (ptA 10 rp) q * slotT (ptA 10 θ) 520 q) := fun q _ => by
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_range]
      split_ifs <;> ring
    rw [sum_congr rfl e, ← mul_sum, sum_slot_eqAtR _ _ (by norm_num), slotWS_eq]
    rfl
  rw [hlink]
  ring

/-! ## The segment's weight value on the log -/

/-- The segment's masked-shift operand `τ ‖ 0 ‖ L` (`gFinSh`'s first `packFK`). -/
def tauLL (κ : CKind) (es : Log) : Array F :=
  (tauL κ es ++ List.replicate (18 - nbC κ) 0 ++ lastBits es).toArray

/-- **`w_out + w_in` on the log at a segment** (A.9 `finSh` (ii) with `shiftSegS`). -/
def wSumSeg (κ : CKind) (es : Log) : F :=
  (Rev4.shiftSegS (tauLL κ es) (pad18 κ (rbL κ es))).1 * slotWS 0 (thL es).toArray (rpL κ es).toArray +
    ((Rev4.shiftSegS (tauLL κ es) (pad18 κ (rbL κ es))).2.1 +
      ksL es * (Rev4.shiftSegS (tauLL κ es) (pad18 κ (rbL κ es))).2.2) *
      slotWS 1 (thL es).toArray (rpL κ es).toArray

theorem sum_bits_self (n N : ℕ) (h : N < 2 ^ n) :
    (∑ l ∈ range n, if N.testBit l then 2 ^ l else 0) = N :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_sum_bits (fun l => N.testBit l) n j]
    by_cases hj : j < n
    · simp [hj]
    · simp [hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num)
        (by omega : n ≤ j)))]

/-- **The operand's last block is `lastL`.** -/
theorem lastAt_tauLL (κ : CKind) (es : Log) : Rev4.lastAt (tauLL κ es) 18 = lastL es := by
  have hl : (tauL κ es ++ List.replicate (18 - nbC κ) 0).length = 18 := by
    simp [tauL]; have := nbC_le κ; omega
  unfold Rev4.lastAt tauLL
  have e : ∀ l ∈ range 18, (if (tauL κ es ++ List.replicate (18 - nbC κ) 0 ++ lastBits es).toArray.getD
      (18 + l) 0 = 1 then 2 ^ l else 0) = if (lastL es).testBit l then 2 ^ l else 0 := fun l hl' => by
    have hl'' := mem_range.1 hl'
    have hg : (tauL κ es ++ List.replicate (18 - nbC κ) 0 ++ lastBits es).toArray.getD (18 + l) 0 =
        (lastBits es).getD l 0 := by
      simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show (tauL κ es ++ List.replicate (18 - nbC κ) 0).length ≤ 18 + l
          by omega), hl, Nat.add_sub_cancel_left]
    rw [hg, lastBits_getD es hl'']
    split_ifs <;> simp_all
  rw [sum_congr rfl e, sum_bits_self 18 _ (lastL_lt es)]

section WSum
variable (wN : CKind → Log → ℕ → ℕ → F)

/-- **A segment's weight value is the extension of `wS` at S2's point.** -/
theorem wSumSeg_eq {es : Log} (hn : (kindOfC es).isNode = false)
    (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    wSumSeg (kindOfC es) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
      eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wS wN (kindOfC es) es y q := by
  generalize hκ : kindOfC es = κ at hn hL
  have hθ : ptA 10 (thL es).toArray = ptOf 10 (thL es) := ptA_toArray _ _
  have hr : ptA 10 (rpL κ es).toArray = ptOf 10 (rpL κ es) := ptA_toArray _ _
  have hτ : (tauL κ es).length = nbC κ := by simp [tauL]
  have hrb : (rbL κ es).length = nbC κ := by simp [rbL]
  have e := final_seg (nbC_le κ) (tauL κ es) (rbL κ es) (lastBits es) hτ hrb hL
    (lastAt_tauLL κ es) (thL es).toArray (rpL κ es).toArray (ksL es)
  rw [hθ, hr] at e
  simp only [wS, hn, Bool.false_eq_true, if_false]
  rw [e]
  rfl

end WSum

/-- **The Sh weight value by kind**: a segment's `wSumSeg`, a node's `wNS` (S-E's, a parameter). -/
def wSumL4 (wNS : CKind → Log → F) (κ : CKind) (es : Log) : F :=
  if κ.isNode then wNS κ es else wSumSeg κ es

/-- S2's last claim (after the kind's `nb + 10` rounds). -/
def claimSL4 (κ : CKind) (es : Log) : F :=
  clR2 114 16 readF (fun d => chF d 0) c0SL [] es (nrS κ)

/-- **The Sh claim's binding** (A.9 `finSh` (ii)): `c_Sh = (w_out + w_in)·v` (P4b's `oSh`). -/
def oSh4 (wNS : CKind → Log → F) (κ : CKind) (es : Log) (v : F) : Prop :=
  claimSL4 κ es = wSumL4 wNS κ es * v

/-! ## Z2's `P^e` at a segment -/

theorem peL_range4 (M : ZLM4) (es : Log) (σ : Fin 64) : peL M es σ =
    ∑ u ∈ range (2 ^ mC 6 (kindOfC es)), eqAtR (ptOf (mC 6 (kindOfC es)) (zrL es)) u *
      M.Et (kindOfC es) es (u / 256) (pAt σ u) := by
  unfold peL eZ
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf (mC 6 (kindOfC es)) (zrL es)) u *
    M.Et (kindOfC es) es (u / 256) (pAt σ u))]
  exact sum_congr rfl fun u _ => by rw [eq_cube_eqAtR]

theorem zrL_length (es : Log) : (zrL es).length = mC 6 (kindOfC es) := by
  have := CKind.m_mem (kindOfC es)
  simp only [zrL, List.length_append, List.length_ofFn, List.length_map, List.length_range, mC]
  omega

theorem zrL_getD4 (es : Log) (l : ℕ) (hl : l < mC 6 (kindOfC es)) :
    (zrL es).getD l 0 = if h : l < 7 then pinnedRho ⟨l, h⟩ else coordAt es 2 (l - 7) := by
  have hm := CKind.m_mem (kindOfC es)
  unfold zrL
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
      List.getElem?_ofFn, dif_pos h, Option.getD_some]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_map, List.getElem?_range (show l - 7 < (kindOfC es).m - 13 by
      unfold mC at hl; omega), Option.map_some, Option.getD_some]

/-- **The segment operand's point is Z1's, zero-padded to 26 coordinates.** -/
theorem segPt_eq {es : Log} {r : Array F}
    (hr : ∀ l < (kindOfC es).m - 13, r.getD l 0 = coordAt es 2 l)
    (hz : ∀ l, (kindOfC es).m - 13 ≤ l → l < 19 → r.getD l 0 = 0) :
    Fin.append (zLo r) (Rev4.blkOf r) =
      ptOf (8 + 18) (zrL es ++ List.replicate (8 + 18 - mC 6 (kindOfC es)) 0) := by
  have hm := CKind.m_mem (kindOfC es)
  have hlen := zrL_length es
  have hp : ∀ l, (zrL es ++ List.replicate (8 + 18 - mC 6 (kindOfC es)) 0).getD l 0 =
      if l < mC 6 (kindOfC es) then (zrL es).getD l 0 else 0 := fun l => by
    simp only [List.getD_eq_getElem?_getD]
    split_ifs with h
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
      split_ifs <;> rfl
  funext l
  refine Fin.addCases (m := 8) (n := 18) (fun i => ?_) (fun i => ?_) l
  · rw [Fin.append_left]
    simp only [ptOf, Fin.coe_castAdd, hp, if_pos (show i.val < mC 6 (kindOfC es) by
      unfold mC; omega), zrL_getD4 es i.val (by unfold mC; omega), zLo]
    split_ifs with h
    · rfl
    · rw [hr 0 (by omega)]; congr 1; omega
  · rw [Fin.append_right]
    simp only [ptOf, Fin.coe_natAdd, hp, Rev4.blkOf]
    split_ifs with h
    · rw [zrL_getD4 es _ h, dif_neg (by omega), hr (1 + i.val) (by unfold mC at h; omega)]
      congr 1; omega
    · exact hz (1 + i.val) (by unfold mC at h; omega) (by omega)

/-- **A segment's `P^e` is `targetSSegS`** at the verifier's operand (Z1's coordinates, zeros to
entry 18, `L`'s bits from 19; B-12's range factor). -/
theorem peL_seg {indN : Rev4.NodeKind → Fin 9 → ℕ → F} {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F}
    {es : Log} (hn : (kindOfC es).isNode = false) {r : Array F}
    (hr : ∀ l < (kindOfC es).m - 13, r.getD l 0 = coordAt es 2 l)
    (hz : ∀ l, (kindOfC es).m - 13 ≤ l → l < 19 → r.getD l 0 = 0)
    (hL : Rev4.lastAt r 19 = lastL es) :
    Rev4.targetSSegS r = Array.ofFn (peL (zlm4 indN etN) es) := by
  have hm := CKind.m_mem (kindOfC es)
  unfold Rev4.targetSSegS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [targetS_range _ _ σ (fun u => if u / 256 ≤ Rev4.lastAt r 19 then chainE (σ + 64 * (u % 256))
      else 0) fun _ => rfl, segPt_eq hr hz, peL_range4]
  rw [sum_eqAtR_padN (show mC 6 (kindOfC es) ≤ 8 + 18 by unfold mC; omega) _ (zrL_length es), hL]
  refine sum_congr rfl fun u _ => ?_
  generalize hκ : kindOfC es = κ at hn
  rcases κ with κ | κ
  · simp only [zlm4, EtSeg, pAt]
  · simp [CKind.isNode] at hn

end FR.Snd.P4a

end G6_FRSoundness4P4aFin

section G6_FRSoundness4P4aS2

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 S2; stage P4a pass 3 (P4c)).

/-!
# S2's obligations at `seq4` (positions 114 … 169), against T4's foundation

3.x's `FrS` S2 part over T4's `D2`, `Same`, `RejOK`, `Reads` and P4a's revision 4.1 tables:

* **`p4a_abs`**: Z's, L's and S's absorb positions are not squeezes (one `seq4` certificate).
* `wS_agree`, `TS_same4`, **`TS_local4`**, `TS_size4`: S2's tables read the log before 114 (a
  node's weight `wN` is assumed to, `WNLocal`).
* **`habs_S2_4`** (S1's final doom is S2's doom at its first absorb), **`single_S2_4`**
  (`≤ 2·2^128` per squeeze), `append_S2_4`, **`rejS2_ok4`** (`T4.RejOK RejS2`),
  **`D2S_reads4`** (`T4.Reads 170`).
* **`endS4`**: at S2's end its doom is the Sh binding `oSh4` failing at `ẑ(r_blk, r_pos)` (a
  node's weight value `wNS` is assumed to be its weight's extension).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The front's absorb positions (a `seq4` certificate) -/

/-- Z's end (67), L2's rounds (69 + 2j), L3 (97) and S2's rounds (114 + 2j) are absorbs. -/
def absOKP4a : Bool :=
  ([67, 97] ++ (List.range 14).map (fun j => 69 + 2 * j) ++
    (List.range 28).map (fun j => 114 + 2 * j)).all fun p => fsItems4[p]? != some Item.squeeze

theorem absOKP4a_eq : absOKP4a = true := by
  rw [absOKP4a, fsItems4, Rev4.seq4_eq]; decide +kernel

theorem p4a_abs : fsItems4[67]? ≠ some .squeeze ∧ fsItems4[97]? ≠ some .squeeze ∧
    (∀ j < 14, fsItems4[69 + 2 * j]? ≠ some .squeeze) ∧
    ∀ j < 28, fsItems4[114 + 2 * j]? ≠ some .squeeze := by
  have h := absOKP4a_eq
  simp only [absOKP4a, List.all_eq_true, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range, bne_iff_ne, ne_eq] at h
  exact ⟨h _ (.inl (.inl (.inl rfl))), h _ (.inl (.inl (.inr (.inl rfl)))),
    fun j hj => h _ (.inl (.inr ⟨j, hj, rfl⟩)), fun j hj => h _ (.inr ⟨j, hj, rfl⟩)⟩

/-! ## S2's tables read before 114 -/

/-- **A node's S2 weight reads the log before 114** (S1's challenges; S-E's, a hypothesis). -/
def WNLocal (wN : CKind → Log → ℕ → ℕ → F) : Prop :=
  ∀ κ es es', Agree es es' 114 → wN κ es = wN κ es'

section S2
variable {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit} (hw : WNLocal wN) (hz : ZwSame zw)
variable {L es L' es' : Log} {p : ℕ}

include hw in
theorem wS_agree (h : Agree es es' p) (hp : 114 ≤ p) (κ : CKind) : wS wN κ es = wS wN κ es' := by
  obtain ⟨h1, h2, h3⟩ := s1_congr4 h hp κ
  funext y q
  simp only [wS, h1, h2, h3, lastL_congr h (by omega), hw κ es es' (h.mono hp)]

include hw hz in
theorem TS_same4 (h : T4.Same L es L' es' p) (hp : 114 ≤ p) : TS wN zw L es = TS wN zw L' es' := by
  have hk := h.kind (by omega)
  rw [TS, TS, hk, wS_agree hw h.1 hp, zNodeC_same hz h (by omega)]

include hw hz in
theorem TS_local4 : TruthLocal2 114 c0SL (TS wN zw) := fun L es es' h =>
  ⟨TS_same4 hw hz (T4.same_of_agree L h) le_rfl, c0S_agree4 h le_rfl⟩

theorem TS_size4 (L es : Log) : ∀ t ∈ TS wN zw L es, t.size = 2 ^ nrS (kindOfC es) := by
  simp [TS, nrS]

theorem nrS_le4 (κ : CKind) : nrS κ ≤ 28 := by have := nbC_le κ; unfold nrS; omega

include hw hz in
/-- **Into S2** (`habs` at 114): S1's final doom is S2's doom at its first absorb. -/
theorem habs_S2_4 (x : ByteArray × Digest) (hl : es.length = 114) (hb : S2Bad wN zw L es) :
    D2S wN zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by omega)
  refine ⟨by simp; omega, ?_⟩
  have ha0 : T4.ans3 114 nrS (es ++ [x]) = 0 := by
    simp only [T4.ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [T4.Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [TS_same4 hw hz (hl ▸ hS) le_rfl, hk, c0SL, c0S_agree4 (hl ▸ hS).1 le_rfl]
  exact hb

include hw hz in
open Classical in
/-- **S2's squeezes** (A.10 S2: `2·2^128`). -/
theorem single_S2_4 (L es : Log)
    (hchk : ∀ j, es.length = 114 + 2 * j + 1 → j < nrS (kindOfC es) →
      Chk2 114 16 readF (fun d => chF d 0) c0SL L es j) :
    (univ.filter fun d => D2S wN zw L es ∧ ¬ D2S wN zw L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  T4.D2_single (by omega) (TS_local4 hw hz) innerExpr_deg card_chF_fiber TS_size4 L es hchk

theorem chk_of_not_rejS2_4 (hr : ¬ RejS2 L es) (j : ℕ) (hj : es.length = 114 + 2 * j + 1)
    (hjn : j < nrS (kindOfC es)) : Chk2 114 16 readF (fun d => chF d 0) c0SL L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

include hw hz in
/-- An S2 round's absorb keeps the doom. -/
theorem append_S2_4 (x : ByteArray × Digest) (hlen : 114 < es.length)
    (hc : (es.length - 114) % 2 = 0 ∨ nrS (kindOfC es) ≤ (es.length - 114) / 2) :
    D2S wN zw L (es ++ [x]) ↔ D2S wN zw L es :=
  T4.D2_append_iff (by omega) (TS_local4 hw hz) x hlen hc

end S2

/-! ## S2's round checks -/

section Rej
variable {L es L' es' : Log} {p : ℕ}

theorem chkS_same4 (h : T4.Same L es L' es' p) {j : ℕ} (hj : 114 + 2 * j < p) :
    Chk2 114 16 readF (fun d => chF d 0) c0SL L es j ↔
      Chk2 114 16 readF (fun d => chF d 0) c0SL L' es' j := by
  have hg : g2At 114 16 readF es j = g2At 114 16 readF es' j := by
    simp only [g2At, msgAt, h.1 (114 + 2 * j) hj]
  have hc0 : c0SL L es = c0SL L' es' := c0S_agree4 (h.1.mono (by omega)) (le_refl 114)
  have hc := clR2_same (b := 114) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := c0SL) hc0 (l := j) (h.1.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejS2_mono4 (x : ByteArray × Digest) (h : RejS2 L es) : RejS2 L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  have hS := T4.same_append L es [x]
  refine ⟨j, by rw [hS.kind (by omega)]; exact hj, by simp; omega, fun h' => hc ?_⟩
  exact (chkS_same4 hS (by omega)).mp h'

/-- **`T4.RejOK` for S2's round checks.** -/
theorem rejS2_ok4 : T4.RejOK RejS2 where
  mono L es x := rejS2_mono4 x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejS2_mono4 x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    have hS := T4.same_append L es [x]
    rw [hS.kind (by omega)] at hj
    by_cases he : 114 + 2 * j = es.length
    · exact absurd (he ▸ hit) (p4a_abs.2.2.2 j (lt_of_lt_of_le hj (nrS_le4 _)))
    exact ⟨j, hj, by omega, fun h' => hc ((chkS_same4 hS (by omega)).mpr h')⟩
  stab L i hb hci X hX := by
    have hS := T4.same_stabX hb hci hX
    by_cases h0 : X.length = 0
    · constructor <;> rintro ⟨j, -, hlt, -⟩ <;> omega
    unfold RejS2
    rw [hS.kind (by omega)]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      not_congr (chkS_same4 hS (by omega))

end Rej

section Reads
variable {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit} (hw : WNLocal wN) (hz : ZwSame zw)

include hw hz in
/-- **Once every S2 round is answered, S2's doom reads before 170.** -/
theorem D2S_reads4 : T4.Reads 170 (D2S wN zw) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  have hans : ∀ Y : Log, 170 ≤ Y.length → T4.ans3 114 nrS Y = nrS (kindOfC Y) :=
    fun Y hY => by have := nrS_le4 (kindOfC Y); unfold T4.ans3; simp; omega
  unfold D2S T4.D2 T4.Wrong2
  rw [hans es (by omega), hans es' (by omega), hk, TS_same4 hw hz h (by omega),
    clR2_same (c0 := c0SL) (L' := L') (es' := es') (c0S_agree4 h.1 (by omega))
      (h.1.mono (by have := nrS_le4 (kindOfC es'); omega)),
    rchs2_congr (h.1.mono (by have := nrS_le4 (kindOfC es'); omega))]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

end Reads

/-! ## S2's end: the Sh binding -/

theorem rchsS_pts4 (κ : CKind) (es : Log) :
    ptOf (nbC κ) (rchs2 114 (fun d => chF d 0) es (nbC κ + 10)) = ptOf (nbC κ) (rbL κ es) ∧
      ptOf 10 ((rchs2 114 (fun d => chF d 0) es (nbC κ + 10)).drop (nbC κ)) =
        ptOf 10 (rpL κ es) := by
  refine ⟨funext fun l => ?_, funext fun l => ?_⟩
  · have := l.isLt
    simp [ptOf, rchs2, rbL, List.getD_eq_getElem?_getD, this, show l.val < nbC κ + 10 by omega]
    rfl
  · have := l.isLt
    simp [ptOf, rchs2, rpL, List.getD_eq_getElem?_getD, this]
    rfl

/-- `ẑ` at S2's point `(r_blk, r_pos)` over the block positions `< 2^10` (RS claim 3's true
value; P4b's `trueL4` at claim 3 is this, 3.x's `trueL_two`). -/
def zS2 (zw : Wit) (L es : Log) : F :=
  ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
    eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
      eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * zNodeC zw (kindOfC es) L es y q

/-- **At S2's end its doom is the Sh binding failing at `ẑ`** (a segment's `L` among its blocks; a
node's weight value is its weight's extension). -/
theorem endS4 {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit} {wNS : CKind → Log → F} {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es))
    (h : D2S wN zw L es) (hl : 170 ≤ es.length) : ¬ oSh4 wNS (kindOfC es) es (zS2 zw L es) := by
  obtain ⟨-, hw⟩ := h
  have ha : T4.ans3 114 nrS es = nrS (kindOfC es) := by
    have := nrS_le4 (kindOfC es); unfold T4.ans3; simp; omega
  rw [ha] at hw
  unfold T4.Wrong2 at hw
  rw [Nat.sub_self, trueSum_bindAll' _ _ _ (by simp [rchs2]) (TS_size4 L es), innerExpr_eval2,
    TS, arrGetD_pair0, arrGetD_pair1, nrS, mle_tab, mle_tab,
    (rchsS_pts4 _ es).1, (rchsS_pts4 _ es).2] at hw
  intro hok
  apply hw
  have hW : wSumL4 wNS (kindOfC es) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
      eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wS wN (kindOfC es) es y q := by
    unfold wSumL4
    cases hn : (kindOfC es).isNode
    · simp only [Bool.false_eq_true, if_false]; exact wSumSeg_eq wN hn (hL hn)
    · simp only [if_true]; rw [hNS hn]
      simp only [wS, hn, if_true]
  rw [oSh4, claimSL4, hW, zS2] at hok
  rw [show clR2 114 16 readF (fun d => chF d 0) c0SL L es (nbC (kindOfC es) + 10) =
    claimSL4 (kindOfC es) es from clR2_same rfl (fun _ _ => rfl), claimSL4]
  exact hok

end FR.Snd.P4a

end G6_FRSoundness4P4aS2

section G6_FRSoundness4P4aZ

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Z1 … Zend; stage P4a pass 4 (P4d)):
-- a copy-port of `FRSoundnessFrZ`'s obligations to `seq4` and `CKind`.

/-!
# Z's obligations at `seq4` (positions 2 … 67), against T4's foundation

3.x's `FrZ` part "Positions" … "Z3 and Zend" over T4's `Same`, `Reads`, `D3`, `RejOK`,
`hfin_seq` and P4a's revision 4.1 tables (`ZLM4`, the witness `zw : Wit`). The renaming is
`kindOf → kindOfC`, `mm 6 → mC 6`, `zW_same → ZwSame`, `fsItems/phOf → fsItems4/phOf4`. Two
hypotheses are new:

* **`ZLM4.EtLocal`**: the targets read the log before position 2 (a segment's target reads its
  last block `L` off `stmt`, B-12; 3.x's targets did not read the log). **`zlm4_etLocal`**: P4a's
  `zlm4` meets it for any node maps.
* **`WitBits`**: the witness is bit-valued (3.x's `unpack_boolean` was inline); **`witBits_zW`**:
  T4's `zW` is.

The obligations: **`z_unit_pos4`** (positions), the reads (`zHolds_reads4`, `zEnd_reads4`,
`pendZ_reads4`, `z2Bad_reads4`, `zendBad_reads4`, `rejZ_reads4`, `zDooms_log4`), **`z1_hfin4`**
(`≤ deltaR` at `(2, 10)`), **`z2_habs4`**, **`z2_single4`** (`126·2^128`), **`z3_habs4`**,
**`z3_single4`** (`3·2^128`), **`zend_habs4`**, **`rejZ_ok4`** (`T4.RejOK (RejZ M)`), and
`rejOK_at4` (3.x's `rejOK_at` at `seq4`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The new hypotheses -/

/-- **The targets read the log before position 2** (a segment's `L` from `stmt`). -/
def ZLM4.EtLocal (M : ZLM4) : Prop := ∀ κ es es', Agree es es' 2 → M.Et κ es = M.Et κ es'

theorem zlm4_etLocal (indN : Rev4.NodeKind → Fin 9 → ℕ → F)
    (etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F) : (zlm4 indN etN).EtLocal := fun κ es es' h => by
  funext t p
  cases κ <;> simp only [zlm4, lastL_congr h le_rfl]

/-- **The witness is bit-valued.** -/
def WitBits (zw : Wit) : Prop := ∀ κ L es b, IsBitF (zw κ L es b)

theorem witBits_zW : WitBits T4.zW := fun _ _ _ _ => unpack_boolean _ _

/-! ## Positions and dimensions -/

/-- **Z's and L's positions at `seq4`** (identity below 170): Z1's ten squeezes after 2 (phase 3),
Z2 at 13–14 (4), Z3 from 15 (5), Zend at 67 (6), L1 at 68 (7), L2 from 69 (8), L3 at 97 (9), L3β
at 98 (10), S1 from 99 (11). -/
theorem z_unit_pos4 :
    (2, 10) ∈ fsRanges4 ∧ phOf4 2 = 2 ∧ phOf4 3 = 3 ∧ phOf4 12 = 3 ∧ phOf4 13 = 4 ∧
    phOf4 14 = 4 ∧ phOf4 15 = 5 ∧ phOf4 66 = 5 ∧ phOf4 67 = 6 ∧ phOf4 68 = 7 ∧ phOf4 69 = 8 ∧
    phOf4 96 = 8 ∧ phOf4 97 = 9 ∧ phOf4 98 = 10 ∧ phOf4 99 = 11 := by
  refine ⟨by rw [fsRanges4_eq]; simp, ?_⟩
  have hph : ∀ q, phOf4 q = (fsStarts4.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts4_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mC6_eq4 (κ : CKind) : mC 6 κ = 7 + (κ.m - 13) := by
  unfold mC; rcases κ.m_mem with h | h | h <;> omega

theorem m13_le4 (κ : CKind) : κ.m - 13 ≤ 19 := by rcases κ.m_mem with h | h | h <;> omega

theorem mC6_le (κ : CKind) : mC 6 κ ≤ 26 := by
  unfold mC; rcases κ.m_mem with h | h | h <;> omega

/-- A squeeze's entry is one more `Same` entry (T4's `same_append`). -/
theorem same_ext1_4 (L es : Log) (a : Digest) : T4.Same L (ext1 es a) L es es.length :=
  T4.same_append L es _

/-- A check that holds from position `p + 1` on and reads the entries before it is a `T4.RejOK`
when `p` is not a `seq4` squeeze (3.x's `rejOK_at`). -/
theorem rejOK_at4 {p : ℕ} {P : Log → Log → Prop} (hP : T4.Reads (p + 1) P)
    (hp : fsItems4[p]? ≠ some .squeeze) : T4.RejOK fun L es => p + 1 ≤ es.length ∧ P L es where
  mono L es x h := ⟨by simp; omega, (hP.append L es [x] h.1).mpr h.2⟩
  sq L es x hit := by
    by_cases hle : p + 1 ≤ es.length
    · exact and_congr (by simp; omega) (hP.append L es [x] hle)
    · have hne : es.length ≠ p := fun he => hp (he ▸ hit)
      exact ⟨fun h => absurd h.1 (by simp; omega), fun h => absurd h.1 hle⟩
  stab L i hb hci X hX := by
    by_cases hle : p + 1 ≤ X.length
    · exact and_congr Iff.rfl (hP.stab hb hci hX hle)
    · exact ⟨fun h => absurd h.1 hle, fun h => absurd h.1 hle⟩

/-! ## Reads (Z1) -/

section Reads
variable {M : ZLM4} {zw : Wit} {L es L' es' : Log} {p : ℕ}

theorem zrL_agree4 (h : Agree es es' 13) : zrL es = zrL es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by norm_num))
  have hm := m13_le4 (kindOfC es)
  unfold zrL
  rw [← hk]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  simp only [List.mem_range] at hj
  unfold coordAt
  exact fAt_congr h (by omega) _

theorem zBk_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (κ : CKind) :
    zBk zw κ L es = zBk zw κ L' es' := by
  funext t k; simp only [zBk, hz κ L es L' es' p h hp]

theorem aZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : CKind) :
    aZ M zw ℓ κ L es = aZ M zw ℓ κ L' es' := by
  funext σ u; simp only [aZ, mvZ, zBk_same4 hz h hp κ]

theorem bZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : CKind) :
    bZ M zw ℓ κ L es = bZ M zw ℓ κ L' es' := by
  funext σ u; simp only [bZ, mvZ, zBk_same4 hz h hp κ]

theorem zZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : CKind) :
    zZ zw ℓ κ L es = zZ zw ℓ κ L' es' := by
  funext σ u; simp only [zZ, zBk_same4 hz h hp κ]

theorem eZ_agree4 (hE : M.EtLocal) (h : Agree es es' p) (hp : 2 ≤ p) (ℓ : ℕ) (κ : CKind) :
    eZ M ℓ κ es = eZ M ℓ κ es' := by
  funext σ u; simp only [eZ, hE κ es es' (h.mono hp)]

theorem zHolds_same4 (hz : ZwSame zw) (hE : M.EtLocal) (h : T4.Same L es L' es' p) (hp : 3 ≤ p) :
    ZHolds M zw L es ↔ ZHolds M zw L' es' := by
  have hk := h.kind (by omega)
  unfold ZHolds
  rw [hk, aZ_same4 hz h hp, bZ_same4 hz h hp, zZ_same4 hz h hp, eZ_agree4 hE h.1 (by omega)]

theorem zHolds_reads4 (hz : ZwSame zw) (hE : M.EtLocal) : T4.Reads 3 (ZHolds M zw) :=
  fun _ _ _ _ _ _ h => zHolds_same4 hz hE h le_rfl

/-- `ZEnd` from a nonzero residual at Z1's point read off a longer chain. -/
theorem zEnd_of4 (hz : ZwSame zw) (hE : M.EtLocal) (h : T4.Same L es L' es' 3) {i : Fin 64}
    (hne : mle (zres M zw L' es' i) (ptOf (mC 6 (kindOfC es')) (List.ofFn pinnedRho ++
      (List.range ((kindOfC es').m - 13)).map (coordAt es 2))) ≠ 0) : ZEnd M zw L es := by
  have hk := h.kind (by norm_num)
  refine ⟨i, ?_⟩
  unfold zres zrL
  rw [hk, aZ_same4 hz h le_rfl, bZ_same4 hz h le_rfl, zZ_same4 hz h le_rfl,
    eZ_agree4 hE h.1 (by norm_num)]
  exact hne

theorem zEnd_reads4 (hz : ZwSame zw) (hE : M.EtLocal) : T4.Reads 13 (ZEnd M zw) :=
  fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  unfold ZEnd zres
  rw [hk, zrL_agree4 h.1, aZ_same4 hz h (by norm_num), bZ_same4 hz h (by norm_num),
    zZ_same4 hz h (by norm_num), eZ_agree4 hE h.1 (by norm_num)]

end Reads

/-! ## Bits -/

section Bits
variable {M : ZLM4} {zw : Wit}

theorem mvZ_bit4 (hM : M.Bits) (hb : WitBits zw) {A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F}
    (hA : ∀ j p k, IsBitF (A j p k)) (κ : CKind) (L es : Log) (t : ℕ) (p : Fin (2 ^ 14)) :
    IsBitF (mvZ M zw A κ L es t p) :=
  sum_bitF _ _ fun j _ => isBit_mul (hM.2.2.1 κ j t)
    (sum_bitF _ _ fun k _ => isBit_mul (hA j p k) (hb _ _ _ _))

theorem zres_bit4 (hM : M.Bits) (hb : WitBits zw) (L es : Log) (i : Fin 64)
    (u : Fin (2 ^ mC 6 (kindOfC es))) : IsBitF (zres M zw L es i u) :=
  bzRes_bit (fun _ _ => mvZ_bit4 hM hb hM.1 _ L es _ _) (fun _ _ => mvZ_bit4 hM hb hM.2.1 _ L es _ _)
    (fun _ _ => hb _ _ _ _) (fun _ _ => hM.2.2.2 _ _ _ _) i u

end Bits

/-! ## Z1 (`hfin`, positions 3 … 12) -/

/-- Z1's doom on the coordinate list: the background, or a pinned-fixed residual slice whose
extension is nonzero at the coordinates bound so far (3.x's `Z1Doom`). -/
def Z1Doom4 (M : ZLM4) (zw : Wit) (Bg : Log → Log → Prop) (L es₀ : Log) (l : List F) : Prop :=
  Bg L es₀ ∨ ∃ i : Fin 64, ∃ t : Array F,
    t.size = 2 ^ ((kindOfC es₀).m - 13) ∧ mlDoom ((kindOfC es₀).m - 13) t l ∧
    ∀ cs : List F, cs.length = (kindOfC es₀).m - 13 →
      mle (tbl ((kindOfC es₀).m - 13) t) (ptOf ((kindOfC es₀).m - 13) cs) =
        mle (zres M zw L es₀ i) (ptOf (mC 6 (kindOfC es₀)) (List.ofFn pinnedRho ++ cs))

open Classical in
/-- **Z1's charge at `seq4`** (A.10 Z1, `≤ 19/2^128 ≤ deltaR`): with the entry's doom
`Bg ∨ ¬ ZHolds` and a final doom containing `Bg ∨ ZEnd`, the ten squeezes escape with conditional
probability at most `deltaR`. -/
theorem z1_hfin4 {M : ZLM4} {zw : Wit} (hM : M.Bits) (hb : WitBits zw) (hz : ZwSame zw)
    (hE : M.EtLocal) {Dk : ℕ → Log → Log → Prop} {Bg : Log → Log → Prop}
    (hBg : T4.Reads 3 Bg) (hprev : ∀ L es, Dk (phOf4 2) L es → Bg L es ∨ ¬ ZHolds M zw L es)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 3) = msD (Dk (phOf4 2)) fin 2 10)
    (hfinI : ∀ L es, Bg L es ∨ ZEnd M zw L es → fin L es)
    (L es₀ : Log) (hl : es₀.length = 3) : condCount (DPos (T4.Dp Dk)) L es₀ 10 [] ≤ deltaR := by
  have hsum : ∑ i ∈ range (10 * 2), (if i < 19 then 1 else 0) ≤ 239 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  refine T4.hfin_seq z_unit_pos4.1 hfin (fun i => if i < 19 then 1 else 0) hsum (Z1Doom4 M zw Bg)
    (fun L es₀ l hd => ?_) (fun L es₀ hd => ?_) (fun L es₀ as hl' has hd hnf => ?_) L es₀ hl
  · rcases hd with hb | ⟨i, t, hts, hd, hcs⟩
    · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun c _ h =>
        h (.inl hb))).trans_le (Nat.zero_le _)
    refine le_trans (card_le_card fun c hc => ?_) ((mlDoom_step hts l hd).trans ?_)
    · simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact fun h => hc (.inr ⟨i, t, hts, h, hcs⟩)
    · have := m13_le4 (kindOfC es₀); split_ifs <;> omega
  · rcases hprev L es₀ hd with hb | hzh
    · exact .inl hb
    obtain ⟨i, hi⟩ := bz_start hzh
    obtain ⟨t, hts, ht0, hcs⟩ := pinned_table (mC6_eq4 (kindOfC es₀)) (zres M zw L es₀ i)
      (zres_bit4 hM hb L es₀ i) hi
    exact .inr ⟨i, t, hts, mlDoom_nil ht0, hcs⟩
  · obtain ⟨ys, hy⟩ := T4.ext_eq_append es₀ as
    have hS : T4.Same L (ext es₀ as) L es₀ 3 := by
      rw [hy]; exact (T4.same_append L es₀ ys).mono (by omega)
    rintro (hbg | ⟨i, t, hts, hd, hcs⟩)
    · exact hnf (hfinI _ _ (.inl ((hBg.ext L es₀ as (by omega)).mpr hbg)))
    have hk := m13_le4 (kindOfC es₀)
    have hlen : (kindOfC es₀).m - 13 ≤ (List.ofFn fun j : Fin (10 * 2) =>
        coordAt (ext es₀ as) 2 j).length := by simp; omega
    rw [mlDoom_full t hts _ hlen, hcs _ (by simp; omega),
      take_ofFn_coord (ext es₀ as) (by omega : (kindOfC es₀).m - 13 ≤ 10 * 2)] at hd
    exact hnf (hfinI _ _ (.inr (zEnd_of4 hz hE hS hd)))

/-! ## Reads of Z2 … Zend -/

section Reads2
variable {M : ZLM4} {zw : Wit} {L es L' es' X : Log} {p : ℕ}

theorem z2_agree14_4 (h : Agree es es' 14) :
    kindOfC es = kindOfC es' ∧ zrL es = zrL es' ∧ pzL es = pzL es' ∧ pabL es = pabL es' := by
  refine ⟨kindOfC_congr (h.mono (by norm_num)), zrL_agree4 (h.mono (by norm_num)), ?_, ?_⟩ <;>
  · funext k; simp only [pzL, pabL, msgAt_congr h (show 13 < 14 by norm_num)]

theorem z2_agree4 (h : Agree es es' 15) :
    kindOfC es = kindOfC es' ∧ zrL es = zrL es' ∧ lamL es = lamL es' ∧ pzL es = pzL es' ∧
      pabL es = pabL es' := by
  obtain ⟨h1, h2, h3, h4⟩ := z2_agree14_4 (h.mono (by norm_num))
  exact ⟨h1, h2, fAt_congr h (by norm_num) 0, h3, h4⟩

theorem peL_agree4 (hE : M.EtLocal) (h : Agree es es' 14) : peL M es = peL M es' := by
  obtain ⟨hk, hz, -, -⟩ := z2_agree14_4 h
  unfold peL; rw [hk, hz, eZ_agree4 hE h (by norm_num)]

theorem c0Z_agree4 (hE : M.EtLocal) (h : Agree es es' 15) : c0Z M es = c0Z M es' := by
  obtain ⟨-, -, hl, hp, hq⟩ := z2_agree4 h
  unfold c0Z; rw [hl, hp, hq, peL_agree4 hE (h.mono (by norm_num))]

theorem pzT_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 13 ≤ p) :
    pzT zw L es = pzT zw L' es' := by
  have hk := h.kind (by omega)
  unfold pzT; rw [hk, zrL_agree4 (h.1.mono hp), zZ_same4 hz h (by omega)]

theorem pabT_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 13 ≤ p) :
    pabT M zw L es = pabT M zw L' es' := by
  have hk := h.kind (by omega)
  unfold pabT; rw [hk, zrL_agree4 (h.1.mono hp), aZ_same4 hz h (by omega), bZ_same4 hz h (by omega)]

theorem pendZ_reads4 (hz : ZwSame zw) : T4.Reads 15 (PendZ zw) := fun L es L' es' h1 h2 h => by
  have hl := (z2_agree4 h.1).2.2.1
  rw [PendZ, PendZ, pzStar_agree h.1, pzT_same4 hz h (by norm_num), hl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem z2Bad_reads4 (hz : ZwSame zw) (hE : M.EtLocal) : T4.Reads 15 (Z2Bad M zw) :=
  fun L es L' es' h1 h2 h => by
  have hl := (z2_agree4 h.1).2.2.1
  unfold Z2Bad
  rw [c0Z_agree4 hE h.1, pabT_same4 hz h (by norm_num), hl, pendZ_reads4 hz L es L' es' h1 h2 h]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem TZ_same4 (hz : ZwSame zw) (h : T4.Same L es L' es' p) (hp : 15 ≤ p) :
    TZ M zw L es = TZ M zw L' es' := by
  obtain ⟨hk, hzr, hl, -, -⟩ := z2_agree4 (h.1.mono hp)
  unfold TZ; rw [hk, hzr, hl, aZ_same4 hz h (by omega), bZ_same4 hz h (by omega)]

theorem TZ_local4 (hz : ZwSame zw) (hE : M.EtLocal) :
    TruthLocal 15 (fun _ es => c0Z M es) (TZ M zw) := fun L _ _ h =>
  ⟨TZ_same4 hz (T4.same_of_agree L h) le_rfl, c0Z_agree4 hE h⟩

theorem TZ_size4 (L es : Log) : ∀ t ∈ TZ M zw L es, t.size = 2 ^ mC 6 (kindOfC es) :=
  bz_sizes _ _ _ _

/-- Z's dooms read the log only through the level-0 word: on one chain, two logs whose words
agree give the same dooms (`hstab`). -/
theorem zDooms_log4 (hz : ZwSame zw) (h : T4.Same L X L' X p) (hp : 3 ≤ p) :
    (ZEnd M zw L X ↔ ZEnd M zw L' X) ∧ (Z2D M zw L X ↔ Z2D M zw L' X) ∧
      (D3Z M zw L X ↔ D3Z M zw L' X) ∧ (ZendBad M zw L X ↔ ZendBad M zw L' X) ∧
      (PendZ zw L X ↔ PendZ zw L' X) ∧ (ZHolds M zw L X ↔ ZHolds M zw L' X) := by
  have hzz := zZ_same4 hz h hp; have ha := aZ_same4 (M := M) hz h hp
  have hb := bZ_same4 (M := M) hz h hp
  have h1 : ZEnd M zw L X ↔ ZEnd M zw L' X := by unfold ZEnd zres; rw [ha, hb, hzz]
  have h2 : PendZ zw L X ↔ PendZ zw L' X := by unfold PendZ pzT; rw [hzz]
  have h3 : Z2Bad M zw L X ↔ Z2Bad M zw L' X := by unfold Z2Bad pabT; rw [ha, hb, h2]
  refine ⟨h1, ?_, ?_, ?_, h2, ?_⟩
  · unfold Z2D; split_ifs; exacts [h1, h3]
  · exact (T4.D3_log_congr (b := 15) (c0 := fun _ es => c0Z M es) (nr := mC 6) (e := bzExpr)
      (T := TZ M zw) (by unfold TZ; rw [ha, hb]) rfl).symm
  · unfold ZendBad aStar bStar; rw [ha, hb]
  · unfold ZHolds; rw [ha, hb, hzz]

theorem rZ_agree4 (h : Agree es es' 67) : rZ es = rZ es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by norm_num))
  unfold rZ rchs; rw [hk]
  refine List.map_congr_left fun j hj => ?_
  have := mC6_le (kindOfC es'); simp only [List.mem_range] at hj
  exact rch_congr h (by omega)

theorem zendBad_reads4 (hz : ZwSame zw) : T4.Reads 68 (ZendBad M zw) :=
  fun L es L' es' h1 h2 h => by
  obtain ⟨hk, -, hl, -, -⟩ := z2_agree4 (h.1.mono (by norm_num))
  have hr := rZ_agree4 (h.1.mono (by norm_num))
  have hv : ∀ j, vZ es j = vZ es' j := fun j => by
    simp only [vZ, msgAt_congr h.1 (show 67 < 68 by norm_num)]
  unfold ZendBad aStar bStar
  rw [hk, hl, hr, hv, hv, aZ_same4 hz h (by norm_num), bZ_same4 hz h (by norm_num)]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem rejZ_reads4 (hE : M.EtLocal) : T4.Reads 68 fun L es =>
    clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) ≠
      eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) *
        (vZ es 0 * vZ es 1) :=
  fun L es L' es' h1 h2 h => by
  obtain ⟨hk, hzr, -, -, -⟩ := z2_agree4 (h.1.mono (by norm_num))
  have hr := rZ_agree4 (h.1.mono (by norm_num))
  have hv : ∀ j, vZ es j = vZ es' j := fun j => by
    simp only [vZ, msgAt_congr h.1 (show 67 < 68 by norm_num)]
  have hc : clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) =
      clR 15 (fun _ es => c0Z M es) L' es' (mC 6 (kindOfC es)) := by
    rw [clR_log_congr (L := L) (L' := L') rfl]
    have := mC6_le (kindOfC es)
    exact clR_congr (c0 := fun _ es => c0Z M es) (c0Z_agree4 hE (h.1.mono (by norm_num)))
      (h.1.mono (by omega))
  beta_reduce
  rw [hc, hk, hzr, hr, hv, hv]

end Reads2

/-! ## Z2 (`habs` at 13, `hsingle` at 14) -/

section Z2
variable {M : ZLM4} {zw : Wit}

/-- **Into Z2** (`habs` at 13): Z1's final doom carries over Z2's absorb. -/
theorem z2_habs4 (hz : ZwSame zw) (hE : M.EtLocal) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = 13) (hzE : ZEnd M zw L es) : Z2D M zw L (es ++ [x]) := by
  have : (es ++ [x]).length ≤ 14 := by simp; omega
  rw [Z2D, if_pos this]; exact ((zEnd_reads4 hz hE).append L es [x] (by omega)).mpr hzE

theorem z2_ext1_4 (hz : ZwSame zw) (hE : M.EtLocal) (L es : Log) (a : Digest) (hl : es.length = 14) :
    c0Z M (ext1 es a) = interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (chF a 0) ∧
    pzStar (ext1 es a) = interpolateAt lNode (pzL es) (chF a 0) ∧
    pabT M zw L (ext1 es a) = pabT M zw L es ∧ pzT zw L (ext1 es a) = pzT zw L es ∧
    lamL (ext1 es a) = chF a 0 := by
  have hS := same_ext1_4 L es a
  rw [hl] at hS
  obtain ⟨-, -, hp, hq⟩ := z2_agree14_4 (hS.1 : Agree (ext1 es a) es 14)
  have hlam : lamL (ext1 es a) = chF a 0 := by
    have := entAt_ext1 es a; rw [hl] at this
    simp only [lamL, fAt, ansAt, this]
  refine ⟨?_, ?_, pabT_same4 hz hS (by norm_num), pzT_same4 hz hS (by norm_num), hlam⟩
  · unfold c0Z; rw [hp, hq, hlam, peL_agree4 hE hS.1]
  · unfold pzStar; rw [hp, hlam]

open Classical in
/-- **Z2's squeeze** (A.10 Z2, `126·2^128`; `skip_pair_bad_le`). -/
theorem z2_single4 (hz : ZwSame zw) (hE : M.EtLocal) (L es : Log) (hl : es.length = 14) :
    (univ.filter fun a => Z2D M zw L es ∧ ¬ Z2D M zw L (ext1 es a)).card ≤ 126 * 2 ^ 128 := by
  have hle : es.length ≤ 14 := by omega
  have hgt : ∀ a, ¬ (ext1 es a).length ≤ 14 := fun a => by rw [length_ext1]; omega
  by_cases hzE : ZEnd M zw L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hzE (by rw [Z2D, if_pos hle] at h; exact h.1))).trans_le (Nat.zero_le _)
  obtain ⟨i, hi⟩ := hzE
  have hb : ∃ b : Fin 64, (pabT M zw L es).eval (skipNode (Fin.castLE (by norm_num) b)) ≠
      (pzT zw L es).eval (skipNode (Fin.castLE (by norm_num) b)) + peL M es b := ⟨i, bz_end hi⟩
  have hcnt := skip_pair_bad_le (pzL es) (pabL es) (peL M es) (pabT M zw L es) (pzT zw L es)
    (pabPoly_natDegree _ _ _) (pzPoly_natDegree _ _) (.inl hb)
  refine single_F_le' _ _ hcnt fun a ⟨_, hn⟩ => ?_
  simp only [Z2D, hgt a, if_false] at hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := z2_ext1_4 hz hE L es a hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_contra hc
  refine hn ⟨by rw [length_ext1]; omega, ?_⟩
  rw [h1, h3, h5, PendZ, h2, h4, h5]
  by_cases hab : interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (chF a 0) =
    (pabT M zw L es).eval (chF a 0)
  · exact .inr ⟨by rw [length_ext1]; omega, fun h => hc ⟨hab, h⟩⟩
  · exact .inl hab

end Z2

/-! ## Z3 (`habs` at 15, `hsingle` per round) and Zend (`habs` at 67) -/

section Z3
variable {M : ZLM4} {zw : Wit}

/-- **Into Z3** (`habs` at 15): a false initial claim `P^{ab}*(λ)` is Z3's round doom; otherwise
the c-claim is pending false. -/
theorem z3_habs4 (hz : ZwSame zw) (hE : M.EtLocal) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = 15) (hzb : Z2Bad M zw L es) :
    D3Z M zw L (es ++ [x]) ∨ PendZ zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  rw [hl] at hS
  rcases hzb.2 with hc | hp
  · refine .inl ⟨by simp; omega, ?_⟩
    have ha0 : T4.ans3 15 (mC 6) (es ++ [x]) = 0 := by
      simp only [T4.ans3, List.length_append, List.length_singleton, hl]; simp
    rw [ha0]
    simp only [T4.Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
    rw [TZ_same4 hz hS le_rfl, c0Z_agree4 (M := M) hE hS.1, hS.kind (by norm_num)]
    unfold TZ; rw [bz_trueSum]; exact hc
  · exact .inr (((pendZ_reads4 hz).append L es [x] (by omega)).mpr hp)

open Classical in
/-- **Z3's squeezes** (A.10 Z3, `3·2^128`, T4's `D3_single`). -/
theorem z3_single4 (hz : ZwSame zw) (hE : M.EtLocal) (L es : Log) :
    (univ.filter fun a => D3Z M zw L es ∧ ¬ D3Z M zw L (ext1 es a)).card ≤ 3 * 2 ^ 128 :=
  T4.D3_single (by norm_num) (TZ_local4 hz hE) bzExpr_deg (TZ_size4 (M := M)) L es

/-- **At Zend's absorb** (67): a false final Z3 claim gives `RejZ` or a wrong pair `(â, b̂)`. -/
theorem zend_habs4 (hz : ZwSame zw) (hE : M.EtLocal) {L es : Log} (x : ByteArray × Digest)
    (hl : es.length = 67) (hd : D3Z M zw L es) :
    RejZ M L (es ++ [x]) ∨ ZendBad M zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  rw [hl] at hS
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by norm_num)
  have hm := mC6_le (kindOfC es)
  obtain ⟨-, hw⟩ := hd
  have ha : T4.ans3 15 (mC 6) es = mC 6 (kindOfC es) := by
    simp only [T4.ans3, hl]; omega
  rw [ha] at hw
  unfold T4.Wrong3 at hw
  rw [Nat.sub_self] at hw
  have hfin : trueSum bzExpr (bindAll (TZ M zw L es) (rchs 15 es (mC 6 (kindOfC es)))) 0 =
      eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) *
        (aStar M zw L es * bStar M zw L es) :=
    bz_final _ _ (by simp [rchs]) _ _ _
  rw [hfin] at hw
  have hag : Agree (es ++ [x]) es 67 := hS.1
  obtain ⟨-, hzr, hlam, -, -⟩ := z2_agree4 (hag.mono (by norm_num))
  have hr : rZ (es ++ [x]) = rZ es := rZ_agree4 hag
  have hc : clR 15 (fun _ es => c0Z M es) L (es ++ [x]) (mC 6 (kindOfC es)) =
      clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) :=
    clR_congr (c0Z_agree4 hE (hag.mono (by norm_num))) (hag.mono (by omega))
  have haS : aStar M zw L (es ++ [x]) = aStar M zw L es ∧
      bStar M zw L (es ++ [x]) = bStar M zw L es := by
    unfold aStar bStar
    rw [hk, hlam, hr, aZ_same4 hz hS (by norm_num), bZ_same4 hz hS (by norm_num)]
    exact ⟨rfl, rfl⟩
  by_cases hrej : RejZ M L (es ++ [x])
  · exact .inl hrej
  refine .inr ⟨by simp; omega, ?_⟩
  have hchk : clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) =
      eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) *
        (vZ (es ++ [x]) 0 * vZ (es ++ [x]) 1) := by
    by_contra hne
    exact hrej ⟨by simp; omega, by rw [hk, hzr, hr, hc]; exact hne⟩
  rw [haS.1, haS.2]
  exact bz_triple_wrong hw hchk

/-- **`relZ`'s first conjunct is a `T4.RejOK`** (Zend's absorb, 67, is not a squeeze). -/
theorem rejZ_ok4 (hE : M.EtLocal) : T4.RejOK (RejZ M) :=
  rejOK_at4 (p := 67) (rejZ_reads4 hE) p4a_abs.1

end Z3

end FR.Snd.P4a

end G6_FRSoundness4P4aZ
