-- New for `flock-recursive` (BLUEPRINT §2.1, A.8, A.9; stage S-G4, `hFin` step 5).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessAccVal
import FRVerifierImpl
import FRSoundness4P4aSeg

/-!
# `hFin`, step 5: the verifier's tables and weights are the tail's

Plain lemmas about the fixed FRVIR functions (no `OpImpl` field is involved):

* **`eqTab_getD`**: `eqTab r` at `q < 2^|r|` is `eqBits r |r| q`: bit `v` of the index against
  coordinate `v` (little-endian, `eqTab`'s fold appends coordinate `v` as the top bit of the
  table so far). Controls: `eqTab_ctl` (the order), `eqTab_rev_ne` (the reversed order disagrees).
* **`dotKF_eq_sum`**: with `w = eqTab s` (`ℓ` coordinates) and a column of at least `2^ℓ` F
  elements, `dotKF w col = Σ_{r < 2^ℓ} eqBits s ℓ r · col[r]`.
* **`fhVal_mle`**: `finPf`'s `final̂(sf)` is `mleN 7 final sf` (`fhVal_eq` and `eqTab_getD`).

The spec-to-spec lemma (`tensorW` at `specC`, `Impl.tensorWS`):

* **`tensorWS_unit`**: `tensorWS p e_v = Ŵ_v(D[p])`;
* **`encVal_eq_encAt`**: with `tensorW = tensorWS` (`implC_meets`), `encVal p` is level 4's
  `encAt κ 4 m p` for any message `m` that agrees with the π elements below `2^mLog` and whose π
  elements above are zero (the final message's absorb flag for a 30-kind);
-/

namespace FR.Snd
open RecursionFast Finset

/-! ## `eqTab` -/

variable {R : Type} [CommRing R]

/-- Control (the order): `eqTab [0, 1]` puts its `1` at index `2` (bit 1 set: coordinate 1), not
at index `1`. -/
theorem eqTab_ctl : (eqTab (#[0, 1] : Array ℤ)).getD 2 0 = 1 ∧ (eqTab (#[0, 1] : Array ℤ)).getD 1 0 = 0 := by
  rw [eqTab_getD _ (by decide), eqTab_getD _ (by decide)]
  simp (config := { decide := true }) [eqBits, bitSel, prod_range_succ, Array.getD_eq_getD_getElem?]

/-- Control (the reversed order disagrees): reading coordinate `v` against bit `1 − v` gives a
different value at index `1`. -/
theorem eqTab_rev_ne :
    (eqTab (#[0, 1] : Array ℤ)).getD 1 0 ≠ eqBits (fun v => (#[1, 0] : Array ℤ).getD v 0) 2 1 := by
  rw [eqTab_ctl.2]
  simp (config := { decide := true }) [eqBits, bitSel, prod_range_succ, Array.getD_eq_getD_getElem?]

/-! ## `dotKF` -/

/-! ## `final̂` -/

/-- **`final̂(sf)` is the final message's extension at `sf`** (`finV`'s elements, `eqTab` of the
seven challenges). -/
theorem fhVal_mle (inp : Input) (sf : Array K) (hs : sf.size = 7) :
    fhVal inp (eqTab sf) (List.range 128) 0 = mleN 7 (finV inp) (fun v => sf.getD v 0) := by
  rw [fhVal_eq, zero_add, mleN, mle, ← List.sum_toFinset _ (List.nodup_range)]
  · rw [List.toFinset_range, show (128 : ℕ) = 2 ^ 7 from rfl, ← Fin.sum_univ_eq_sum_range]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [eqTab_getD sf (by rw [hs]; exact u.2), eq_cube, mul_comm, hs]
    congr 1

/-! ## `tensorW` at the spec -/

/-- **Level 4's encoding as `encOps` computes it**: Horner over `2^7` coefficients with the
weights `tensorW p e_v` (at the spec) is `encAt κ 4 m p`, for a message `m` equal to the
coefficients below `2^mLog` whose coefficients above are zero. -/
theorem encVal_eq_encAt (impl : OpImpl) (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (inp : Input) (κ : Kind) (m : ℕ → K) (p : ℕ)
    (hm : ∀ c < 2 ^ mLog κ 4, finV inp c = m c)
    (hz : ∀ c, 2 ^ mLog κ 4 ≤ c → c < 2 ^ 7 → finV inp c = 0) :
    encVal impl inp p = encAt κ 4 m p := by
  rw [encVal, hornerVal_eq, encAt, encF]
  have hle : mLog κ 4 ≤ 7 := by rw [mLog_four]; split <;> norm_num
  -- the Horner sum over `2^7` is the encoding's sum over `2^mLog` (the rest is zero)
  rw [← Fin.sum_univ_eq_sum_range (fun c => finV inp c * ∏ u ∈ range 7,
    (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ 7)]
  have hsplit : ∑ c : Fin (2 ^ 7), finV inp c * ∏ u ∈ range 7,
      (if (c : ℕ).testBit u then impl.tensorW p (unitK u) else 1) =
      ∑ c ∈ range (2 ^ mLog κ 4), finV inp c * ∏ u ∈ range 7,
        (if c.testBit u then impl.tensorW p (unitK u) else 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun c => finV inp c * ∏ u ∈ range 7,
      (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ 7)]
    symm
    refine sum_subset (range_subset_range.2 (Nat.pow_le_pow_right (by norm_num) hle))
      fun c hc hnc => ?_
    rw [hz c (by simpa using hnc) (by simpa using hc), zero_mul]
  rw [hsplit, ← Fin.sum_univ_eq_sum_range (fun c => finV inp c * ∏ u ∈ range 7,
    (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ mLog κ 4)]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [hm x x.2, bitProd, bitSel]
  congr 1
  -- bits `mLog … 6` of `x < 2^mLog` are clear
  rw [← prod_range_mul_prod_Ico _ hle]
  have hhi : ∏ u ∈ Ico (mLog κ 4) 7,
      (if (x : ℕ).testBit u then impl.tensorW p (unitK u) else 1) = 1 :=
    prod_eq_one fun u hu => by
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.2
        (Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 hu).1))]; rfl
  rw [hhi, mul_one]
  refine prod_congr rfl fun u hu => ?_
  have hu7 : u < 7 := by have := mem_range.1 hu; omega
  split_ifs <;> simp [ht, tensorWS_unit p hu7]

end FR.Snd
