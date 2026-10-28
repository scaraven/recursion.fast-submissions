-- New for `flock-recursive` (BLUEPRINT §2.1, A.8, A.9; stage S-G4, `hFin` step 5).
import FRSoundnessAccVal
import FRVerifierImpl

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

theorem getD_append_lt {R : Type} {a b : Array R} {q : ℕ} {d : R} (h : q < a.size) :
    (a ++ b).getD q d = a.getD q d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem getD_append_ge {R : Type} {a b : Array R} {j : ℕ} {d : R} :
    (a ++ b).getD (a.size + j) d = b.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

theorem getD_map_lt {R : Type} {a : Array R} {q : ℕ} {d : R} (f : R → R) (h : q < a.size) :
    (a.map f).getD q d = f (a.getD q d) := by
  simp [Array.getD_eq_getD_getElem?, h]

variable {R : Type} [CommRing R]

/-- `eqTab`'s fold from a table of `m` coordinates `g 0 … g (m − 1)`. -/
theorem eqTab_foldl : ∀ (l : List R) (t : Array R) (m : ℕ) (g : ℕ → R),
    t.size = 2 ^ m → (∀ q < 2 ^ m, t.getD q 0 = eqBits g m q) →
    (∀ k (hk : k < l.length), g (m + k) = l[k]) →
    (l.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) t).size = 2 ^ (m + l.length) ∧
      ∀ q < 2 ^ (m + l.length),
        (l.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) t).getD q 0 =
          eqBits g (m + l.length) q
  | [], t, m, g, hs, ht, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]; exact ⟨hs, ht⟩
  | x :: l, t, m, g, hs, ht, hg => by
    have hx : g m = x := by have := hg 0 (by simp); rw [Nat.add_zero] at this; exact this
    have hs' : (t.map (· * (1 - x)) ++ t.map (· * x)).size = 2 ^ (m + 1) := by
      simp [hs, pow_succ, mul_two]
    have ht' : ∀ q < 2 ^ (m + 1), (t.map (· * (1 - x)) ++ t.map (· * x)).getD q 0 =
        eqBits g (m + 1) q := by
      intro q hq
      by_cases hlo : q < 2 ^ m
      · rw [getD_append_lt (by simp [hs, hlo]), getD_map_lt _ (by simp [hs, hlo]), ht q hlo,
          eqBits, eqBits, bitSel_succ_lo _ _ hlo, hx]
      · obtain ⟨j, rfl⟩ : ∃ j, q = 2 ^ m + j := ⟨q - 2 ^ m, by omega⟩
        have hj : j < 2 ^ m := by rw [pow_succ] at hq; omega
        rw [show 2 ^ m + j = (t.map (· * (1 - x))).size + j by simp [hs], getD_append_ge,
          getD_map_lt _ (by simp [hs, hj]), ht j hj, show (t.map (· * (1 - x))).size = 2 ^ m by
            simp [hs], eqBits, eqBits, bitSel_succ_hi _ _ hj, hx]
    have := eqTab_foldl l _ (m + 1) g hs' ht' fun k hk => by
      have := hg (k + 1) (by simp; omega)
      rw [show m + (k + 1) = m + 1 + k by omega] at this; exact this
    rw [List.foldl_cons]
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem eqTab_size' (r : Array R) : (eqTab r).size = 2 ^ r.size := by
  have := (eqTab_foldl r.toList #[1] 0 (fun v => r.getD v 0) rfl
    (fun q hq => by simp at hq; subst hq; simp [eqBits, bitSel]) fun k hk => by
      simp at hk; simp [Array.getD_eq_getD_getElem?, hk]).1
  rw [eqTab, ← Array.foldl_toList]; simpa using this

/-- **`eqTab r` at `q` is `eq(r, bits q)`**, bit `v` of `q` against coordinate `v`. -/
theorem eqTab_getD (r : Array R) {q : ℕ} (hq : q < 2 ^ r.size) :
    (eqTab r).getD q 0 = eqBits (fun v => r.getD v 0) r.size q := by
  have := (eqTab_foldl r.toList #[1] 0 (fun v => r.getD v 0) rfl
    (fun q hq => by simp at hq; subst hq; simp [eqBits, bitSel]) fun k hk => by
      simp at hk; simp [Array.getD_eq_getD_getElem?, hk]).2 q (by simpa using hq)
  rw [eqTab, ← Array.foldl_toList]; simpa using this

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

theorem foldl_add_eq {M : Type} [AddCommMonoid M] : ∀ (l : List M) (a : M),
    l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_eq l, List.sum_cons, add_assoc]

/-- **`dotKF` at an `eqTab` weight**: `Σ_{r < 2^ℓ} eq(s, bits r)·col[r]` (the column has at least
`2^ℓ` elements). -/
theorem dotKF_eq_sum (s : Array K) (col : ByteArray) (hc : 2 ^ s.size ≤ col.size / 16) :
    dotKF (eqTab s) col = ∑ r ∈ range (2 ^ s.size),
      eqBits (fun v => s.getD v 0) s.size r * algebraMap F K (readF col (16 * r)) := by
  rw [← dotKFF_eq, dotKFF, dotKFGo_eq, foldl_add_eq, zero_add, eqTab_size',
    min_eq_right hc, ← List.range_eq_range', ← List.sum_toFinset _ (List.nodup_range),
    List.toFinset_range]
  · refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.1 hr
    have hlt : r < (eqTab s).size := by rw [eqTab_size']; exact hr'
    have hg : (eqTab s)[r] = (eqTab s).getD r 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    rw [getElem!_pos _ r hlt, hg, eqTab_getD s hr', K.smulF_eq_mul, ← K.algebraMap_eq_ofF, fAt_eq,
      readF, mul_comm]

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

/-- The unit vector `e_v` of `K^7`: coordinate `u` is `[u = v]`. -/
theorem unitK_getD (v u : ℕ) (hu : u < 7) : (unitK v).getD u 0 = if u = v then 1 else 0 := by
  simp [unitK, Array.getD_eq_getD_getElem?, hu]

/-- **`tensorW p e_v` is `Ŵ_v(D[p])`** (`v < 7`). -/
theorem tensorWS_unit (p : ℕ) {v : ℕ} (hv : v < 7) :
    Impl.tensorWS p (unitK v) = algebraMap F K (wAtD v p) := by
  rw [Impl.tensorWS, tensorTwin, show (unitK v).size = 7 by simp [unitK],
    prod_eq_single_of_mem v (mem_range.2 hv)]
  · rw [unitK_getD v v hv, if_pos rfl]; simp [wAtD]
  · intro u hu huv
    rw [unitK_getD v u (mem_range.1 hu), if_neg huv]; simp

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
