-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12; S-F4 §7 Q3; stage P4a).
import FRSoundness4P4aNames
import FRVIR4
import FRVIRFinals

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
