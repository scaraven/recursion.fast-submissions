-- New for lvm2 roll 11 (M′, R11-X): the costs of M′'s decoder programs (`LvmMPXDecIR`), generic in the shape and
-- at M′'s three levels, and the fuel bound against the declared `decBudget`. Adapted from `LvmXDecCost.lean`
-- (`cost_decIR`, `decode_fixed_le`), `LvmXDec1Cost.lean` (`cost_dec1IR`), `LvmXDecIR.lean` (`cost_encC`,
-- `cost_bflyAll`), `LvmXCopy.lean` (`cost_rowsIR`), `LvmXAgree.lean` (`cost_agreeIR`).
import LvmMPXDecIR

/-!
# The cost of M′'s decoders

Exact costs (`cost` of the programs; `k = 2^kL`, `n = 2^nL`):

* scans: `agreeNIR n` `14 + 4293 n`, `agree1NIR n` `14 + 2149 n`;
* `Enc` per coordinate: `34 + 13 k + 9 (n − k) + fwdNIR N nL`;
* interpolation `baryIR k C` (shipped, `cost_baryIR`): `25 + 1106 k + 49 k C + 1118 k² + 44 k² C`;
* the inverse NTTs of `R` rows: `12 + R (13 + bflyNIR N kL)`; reorder `12 + C (37 + 13 k)`; transpose
  `12 + 653 k`.

**At M′'s shapes** (`cost_decMP0IRW`, `cost_decMP1IR`, `cost_decMP2IR`):

| level | program | steps | log₂ |
|---|---|---|---|
| 0 (`2^19` positions, `k = 2^17`, lanes 40–47) | `decMP0IRW` | 25,267,547,498,264 | 44.52 |
| 1 (`2^16`, `2^13`, 48 lanes) | `decMP1IR` | 218,783,633,069 | 37.67 |
| 2 (`2^13`, `2^9`, 48 lanes) | `decMP2IR` | 987,558,522 | 29.88 |

**`decMP_fuel`**: the three decoders, a memory of `2^26` words and any further `R ≤ 2^45` steps (the column reads
of the three words, the transcript replay, the node output; X2-FUEL measured `2^35.6` for the reads) fit
`decBudget t` (`2^46 − 2^26 + (2^13 − 16) t`) for every tape length `t`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-! ## The pieces -/

theorem cost_posNBody (n wB qB eB agB t : ℕ) : cost (posNBody n wB qB eB agB) t = 4290 := by
  simp +decide only [posNBody, foldIR, laneBody, macC, testNIR, appendIR, cost, blkSteps, mulKC, redC,
    List.length_cons, List.length_nil, List.cons_append, List.nil_append]

theorem cost_agreeNIR (n wB qB eB agB t : ℕ) (hn : n < 2 ^ 64) :
    cost (agreeNIR n wB qB eB agB) t = 14 + 4293 * n := by
  simp +decide only [agreeNIR, cost, cost_posNBody, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

theorem cost_pos1NBody (n wB qB eB agB t : ℕ) : cost (pos1NBody n wB qB eB agB) t = 2146 := by
  simp +decide only [pos1NBody, fold1IR, lane1Body, eqtLdE, eqtLd1, test1NIR, appendIR, cost, cost_mulE,
    blkSteps, List.length_cons, List.length_nil]

theorem cost_agree1NIR (n wB qB eB agB t : ℕ) (hn : n < 2 ^ 64) :
    cost (agree1NIR n wB qB eB agB) t = 14 + 2149 * n := by
  simp +decide only [agree1NIR, cost, cost_pos1NBody, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

/-- `2^m` is a word for `m < 64`. -/
theorem pow_lt64 {m : ℕ} (h : m < 64) : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h

theorem cost_encMC (N nL kL dB fB c t : ℕ) (hN : N < 2 ^ 64) (hn : nL < 64) (hk : kL < 64) :
    cost (encMC N nL kL dB fB c) t =
      34 + 13 * 2 ^ kL + 9 * (2 ^ nL - 2 ^ kL) + (14 + nL * ((67 + 20 * N) * 2 ^ (nL - 1) + 27)) := by
  have h1 : 2 ^ nL - 2 ^ kL < 2 ^ 64 := lt_of_le_of_lt (Nat.sub_le _ _) (pow_lt64 hn)
  simp +decide only [encMC, cost, cost_mcpIR _ _ _ _ _ (pow_lt64 hk), cost_zeroIR _ _ _ h1,
    cost_fwdNIR N nL _ _ hN (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le nL 1))
      (pow_lt64 hn)) (by omega), blkSteps, List.length_cons, List.length_nil, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub]
  ring

theorem cost_enc1MC (N nL kL dB fB c t : ℕ) (hN : N < 2 ^ 64) (hn : nL < 64) (hk : kL < 64) :
    cost (enc1MC N nL kL dB fB c) t =
      34 + 13 * 2 ^ kL + 9 * (2 ^ nL - 2 ^ kL) + (14 + nL * ((67 + 20 * N) * 2 ^ (nL - 1) + 27)) := by
  have h1 : 2 ^ nL - 2 ^ kL < 2 ^ 64 := lt_of_le_of_lt (Nat.sub_le _ _) (pow_lt64 hn)
  simp +decide only [enc1MC, cost, cost_mcpIR _ _ _ _ _ (pow_lt64 hk), cost_zeroIR _ _ _ h1,
    cost_fwdNIR N nL _ _ hN (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le nL 1))
      (pow_lt64 hn)) (by omega), blkSteps, List.length_cons, List.length_nil, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub]
  ring

theorem cost_bflyAllM (N kL R tb ob t : ℕ) (hN : N < 2 ^ 64) (hk : kL < 64) (hR : R < 2 ^ 64) :
    cost (bflyAllM N kL R tb ob) t = 12 + R * (27 + kL * ((67 + 20 * N) * 2 ^ (kL - 1) + 23)) := by
  simp +decide only [bflyAllM, bflyRowM, cost, cost_bflyNIR N kL _ _ hN
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le kL 1)) (pow_lt64 hk)) (by omega),
    blkSteps, List.length_cons, List.length_nil, toNat_toWord hR, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceSub]
  ring

theorem cost_okMIR (kL ok t : ℕ) : cost (okMIR kL ok) t = 12 := by
  simp +decide only [okMIR, cost, blkSteps, List.length_cons, List.length_nil, ↓reduceIte, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceSub]

theorem cost_rowsMIR (kL C oB mB t : ℕ) (hk : kL < 64) (hC : C < 2 ^ 64) :
    cost (rowsMIR kL C oB mB) t = 12 + C * (37 + 13 * 2 ^ kL) := by
  simp +decide only [rowsMIR, msgRowM, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (pow_lt64 hk), toNat_toWord hC, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  ring

theorem cost_tr1MIR (kL ob oB t : ℕ) (hk : kL < 64) : cost (tr1MIR kL ob oB) t = 12 + 653 * 2 ^ kL := by
  simp +decide only [tr1MIR, tr1RowM, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (pow_lt64 hk), toNat_toWord (show 48 < 2 ^ 64 by norm_num), ↓reduceIte, Nat.reduceAdd,
    Nat.reduceMul, Nat.reduceSub]
  ring

/-! ## The decoders, generic -/

/-- The level-0 decoder's cost model (`cost_decMP0IR`). -/
def c0Model (N nL kL C : ℕ) : ℕ :=
  (29 + 13 * N + (N - 1) * (1077 + 45 * N)) + 51468 +
    (3 * (34 + 13 * 2 ^ kL + 9 * (2 ^ nL - 2 ^ kL) + (14 + nL * ((67 + 20 * N) * 2 ^ (nL - 1) + 27))) + 2) +
    (14 + 4293 * 2 ^ nL) + 12 +
    ((25 + 1106 * 2 ^ kL + 49 * 2 ^ kL * C + 1118 * (2 ^ kL) ^ 2 + 44 * (2 ^ kL) ^ 2 * C) +
      (12 + C * (27 + kL * ((67 + 20 * N) * 2 ^ (kL - 1) + 23))) + (12 + C * (37 + 13 * 2 ^ kL)) + 2) + 1 + 5

/-- **The level-0 decoder's cost**, generic (`N, C < 2^64`, `nL, kL < 64`). -/
theorem cost_decMP0IR (N nL kL lo C dB wB aB fB t : ℕ) (hN : N < 2 ^ 64) (hn : nL < 64) (hk : kL < 64)
    (hC : C < 2 ^ 64) : cost (decMP0IR N nL kL lo C dB wB aB fB) t = c0Model N nL kL C := by
  simp +decide only [decMP0IR, encMIR, decMP0Tail, cost, cost_wtabNIR N _ t hN, cost_eqtIR_six,
    cost_encMC N nL kL _ _ _ t hN hn hk, cost_agreeNIR _ _ _ _ _ t (pow_lt64 hn), cost_okMIR,
    cost_baryIR _ _ _ _ _ _ _ _ t (pow_lt64 hk) hC, cost_bflyAllM N kL C _ _ t hN hk hC,
    cost_rowsMIR kL C _ _ t hk hC, blkSteps, List.length_cons, List.length_nil, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  rw [max_eq_left (by omega), c0Model]
  ring

/-- The level-≥1 decoder's cost model (`cost_dec1MPIR`). -/
def c1Model (N nL kL : ℕ) : ℕ :=
  (29 + 13 * N + (N - 1) * (1077 + 45 * N)) + (12 + 2 ^ 4 * (54 + 125 * 4)) +
    (3 * (34 + 13 * 2 ^ kL + 9 * (2 ^ nL - 2 ^ kL) + (14 + nL * ((67 + 20 * N) * 2 ^ (nL - 1) + 27))) + 2) +
    (14 + 2149 * 2 ^ nL) + 12 +
    ((25 + 1106 * 2 ^ kL + 49 * 2 ^ kL * 48 + 1118 * (2 ^ kL) ^ 2 + 44 * (2 ^ kL) ^ 2 * 48) +
      (12 + 48 * (27 + kL * ((67 + 20 * N) * 2 ^ (kL - 1) + 23))) + (12 + 653 * 2 ^ kL) + 2) + 1 + 5

/-- **The level-≥1 decoder's cost**, generic (`N < 2^64`, `nL, kL < 64`). -/
theorem cost_dec1MPIR (N nL kL dB wB aB fB oB t : ℕ) (hN : N < 2 ^ 64) (hn : nL < 64) (hk : kL < 64) :
    cost (dec1MPIR N nL kL dB wB aB fB oB) t = c1Model N nL kL := by
  simp +decide only [dec1MPIR, enc1MIR, dec1MTail, cost, cost_wtabNIR N _ t hN, cost_eqtIR 4 _ _ t (by norm_num),
    cost_enc1MC N nL kL _ _ _ t hN hn hk, cost_agree1NIR _ _ _ _ _ t (pow_lt64 hn), cost_okMIR,
    cost_baryIR _ _ _ _ _ _ _ _ t (pow_lt64 hk) (show 48 < 2 ^ 64 by norm_num),
    cost_bflyAllM N kL 48 _ _ t hN hk (by norm_num), cost_tr1MIR kL _ _ t hk, blkSteps, List.length_cons, List.length_nil, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
  rw [max_eq_left (by omega), c1Model]
  ring

/-! ## At M′'s shapes -/

/-- **Level 0** (`2^19` positions, `k = 2^17`, lanes 40–47): `≈ 2^44.52`. -/
theorem cost_decMP0IRW (dB wB aB fB t : ℕ) : cost (decMP0IRW dB wB aB fB) t = 25267547498264 := by
  rw [decMP0IRW, cost_decMP0IR _ _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    c0Model]
  norm_num

/-- **Level 1** (`2^16` positions, `k = 2^13`): `≈ 2^37.67`. -/
theorem cost_decMP1IR (dB wB aB fB oB t : ℕ) : cost (decMP1IR dB wB aB fB oB) t = 218783633069 := by
  rw [decMP1IR, cost_dec1MPIR _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num), c1Model]
  norm_num

/-- **Level 2** (`2^13` positions, `k = 2^9`): `≈ 2^29.88`. -/
theorem cost_decMP2IR (dB wB aB fB oB t : ℕ) : cost (decMP2IR dB wB aB fB oB) t = 987558522 := by
  rw [decMP2IR, cost_dec1MPIR _ _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num), c1Model]
  norm_num

/-- **The fuel bound**: M′'s three decoders, a memory of `2^26` words and any `R ≤ 2^45` further steps fit the
declared `decBudget t` (`fuel_base = 2^46` unchanged). -/
theorem decMP_fuel (d0 w0 a0 f0 d1 w1 a1 f1 o1 d2 w2 a2 f2 o2 R t : ℕ) (hR : R ≤ 2 ^ 45) :
    2 ^ 26 + cost (decMP2IR d2 w2 a2 f2 o2) t + cost (decMP1IR d1 w1 a1 f1 o1) t +
      cost (decMP0IRW d0 w0 a0 f0) t + R ≤ decBudget t := by
  rw [cost_decMP2IR, cost_decMP1IR, cost_decMP0IRW, decBudget, fuelBase, fuelPerWord]
  have : 2 ^ 26 + 987558522 + 218783633069 + 25267547498264 + 2 ^ 45 ≤ 2 ^ 46 - 2 ^ 26 := by norm_num
  have h2 : 0 ≤ (2 ^ 13 - 16) * t := Nat.zero_le _
  omega

/-- **The decoders with the grown memory are below `2^45`** (in fact `2^44.53`). -/
theorem decMP_le (d0 w0 a0 f0 d1 w1 a1 f1 o1 d2 w2 a2 f2 o2 t : ℕ) :
    2 ^ 26 + cost (decMP2IR d2 w2 a2 f2 o2) t + cost (decMP1IR d1 w1 a1 f1 o1) t +
      cost (decMP0IRW d0 w0 a0 f0) t ≤ 2 ^ 45 := by
  rw [cost_decMP2IR, cost_decMP1IR, cost_decMP0IRW]; norm_num

/-- **Cross-check**: the model at the shipped shapes is the shipped decoders' cost (`cost_decIR`,
`cost_dec1IR`; the workspaces differ, the step counts agree). -/
theorem c0Model_shipped : c0Model 15 15 13 64 = 265710864928 := by rw [c0Model]; norm_num
theorem c1Model_shipped : c1Model 15 12 9 = 925440493 := by rw [c1Model]; norm_num

end Lvm.X
