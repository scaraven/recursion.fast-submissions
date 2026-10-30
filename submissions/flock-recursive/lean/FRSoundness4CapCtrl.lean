-- New for `flock-recursive` (PACK-4.4 §11.5, `reviews/PACK-4.4-b2-review.md` PB-m12; track A3′ run 2):
-- a concrete chain in the `ζ` escape set.
import FRSoundness4TailC
import FRSoundness4P4aSeg

/-!
# The `ζ` escape set is not empty (a concrete chain)

`dZeta_ctl` characterises `DZeta` at `CapZeta`'s answer as a common root of (I)'s two polynomials.
**`dZeta_inst`** exhibits one: the chain `capEs` of 483 entries whose `CapD` message commits two
reads to the digest `d₁` (all bytes `1`) and every other read to `0`, under all-zero caps. Then
`D` is false (read `(0, 0)` is `d₁`, its cap entry `0`), (I)'s polynomials are `c·(1 + ζ)` (the same
coefficient at reads `0` and `1`), and `ζ = 1` is a root in characteristic two: the answer
`K.toBytes 1` puts the chain in `DZeta`.
-/

namespace FR.Snd.T4
open RecursionFast Finset

/-- The digest with every byte `1`. -/
def d1 : Digest := Vector.replicate 32 1

/-- `CapD`'s query: 40 header bytes, then `d₁ ‖ d₁` (reads `0` and `1`). -/
def qD : ByteArray := ⟨Array.replicate 40 0 ++ Array.replicate 64 1⟩

/-- The chain: 482 default entries, then `CapD`'s. -/
def capEs : Log := List.replicate 482 default ++ [(qD, default)]

theorem capEs_get482 : capEs.getD 482 default = (qD, default) := by
  rw [capEs, List.getD_append_right _ _ _ _ (by rw [List.length_replicate]), List.length_replicate,
    Nat.sub_self, List.getD_cons_zero]

theorem capEs_length : capEs.length = phStart4 53 := by
  rw [capPh_pos.2.1, capEs, List.length_append, List.length_replicate, List.length_singleton]

theorem bytesAt_beyond (q : ByteArray) {o : ℕ} (n : ℕ) (h : q.size ≤ o) :
    bytesAt q o n = Vector.replicate n 0 := by
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_replicate, bytesAt, Vector.getElem_ofFn, byteAt, dif_neg (by omega)]

theorem qD_size : qD.size = 104 := rfl

theorem qD_byte {k : ℕ} (h1 : 40 ≤ k) (h2 : k < 104) : byteAt qD k = 1 := by
  rw [byteAt, dif_pos (by rw [qD_size]; exact h2)]
  show (Array.replicate 40 (0 : UInt8) ++ Array.replicate 64 1)[k]'(by simp; omega) = 1
  rw [Array.getElem_append_right (by simp; omega), Array.getElem_replicate]

theorem capEs_dAt {i q : ℕ} (hi : i < 5) :
    dAt capEs i q = if rdIx i q < 2 then d1 else Vector.replicate 32 0 := by
  unfold dAt msgAt entAt
  rw [capPh_pos.1, capEs_get482]
  split_ifs with h
  · rw [show qD.size = 40 + 64 from rfl, FR.Snd.bytesAt_extract_of_le qD (by omega)]
    refine Vector.ext fun j hj => ?_
    rw [bytesAt, Vector.getElem_ofFn, qD_byte (by omega) (by omega), d1, Vector.getElem_replicate]
  · refine bytesAt_beyond _ _ ?_
    rw [ByteArray.size_extract, qD_size]; omega

theorem capEs_capDig (i e : ℕ) (hi : i < 5) : capDig capEs i e = Vector.replicate 32 0 := by
  have hp : capPos i < 482 := by
    unfold capPos phStart4; rw [fsStarts4_eq]; interval_cases i <;> decide
  unfold capDig msgAt entAt
  rw [capEs, List.getD_append _ _ _ _ (by rw [List.length_replicate]; exact hp),
    List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hp), List.getElem_replicate]
  refine bytesAt_beyond _ _ ?_
  rw [ByteArray.size_extract]
  show min _ (ByteArray.empty.size) - 40 ≤ _
  simp

/-- **`dZeta_inst` (+)**: the concrete chain `capEs`, answered `K.toBytes 1` at `CapZeta`, is in the
`ζ` escape set: a false `D` whose (I) vanishes at the honest weights. -/
theorem dZeta_inst : DZeta (ext1 capEs (K.toBytes 1)) := by
  rw [dZeta_ctl capEs_length]
  have hd : ∀ (hf : Digest → F) (i q : ℕ), i < 5 →
      hf (dAt capEs i q) - hf (capDig capEs i (kCap capEs i q)) =
        if rdIx i q < 2 then hf d1 - hf (Vector.replicate 32 0) else 0 := by
    intro hf i q hi
    rw [capEs_dAt hi, capEs_capDig _ _ hi]
    split_ifs <;> simp
  have hP : ∀ hf : Digest → F, sigP hf capEs 1 = 0 := by
    intro hf
    unfold sigP sumR
    have h0 : ∀ i ∈ range 5, ∀ q ∈ range (tq i),
        algebraMap F K (hf (dAt capEs i q) - hf (capDig capEs i (kCap capEs i q))) * (1 : K) ^ rdIx i q =
          if i = 0 ∧ q < 2 then algebraMap F K (hf d1 - hf (Vector.replicate 32 0)) else 0 := by
      intro i hi q _
      rw [hd hf i q (mem_range.1 hi), one_pow, mul_one]
      have e : rdIx i q < 2 ↔ i = 0 ∧ q < 2 := by
        have := (ladder_vals (mem_range.1 hi)).2.1
        have r0 : rdIx i q = rdIx i 0 + q := by simp [rdIx]
        have v := tq_eq.2.1
        constructor
        · intro h
          by_contra hc
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · exact hc ⟨rfl, by simp [rdIx, Rev4.capReadsBelow] at h; omega⟩
          · have h1 := this 0 hpos
            have : tq 0 = 290 := by have := congrArg (·[0]?) tq_eq.1; simpa using this
            simp only [rdIx, Nat.add_zero] at h1 ⊢ h
            omega
        · rintro ⟨rfl, hq⟩; simp [rdIx, Rev4.capReadsBelow]; omega
      by_cases h : rdIx i q < 2
      · rw [if_pos h, if_pos (e.1 h)]
      · rw [if_neg h, if_neg (fun h' => h (e.2 h')), map_zero]
    rw [sum_congr rfl fun i hi => sum_congr rfl (h0 i hi)]
    have ht0 : tq 0 = 290 := by have := congrArg (·[0]?) tq_eq.1; simpa using this
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun i _ => by simp), zero_add]
    simp only [true_and, ht0]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    have hc : (Finset.filter (fun q => q < 2) (range 290)).card = 2 := by
      rw [show Finset.filter (fun q => q < 2) (range 290) = range 2 by ext x; simp; omega]; rfl
    rw [hc, two_smul, ← two_mul, CharTwo.two_eq_zero, zero_mul]
  refine ⟨fun ht => ?_, by simp only [chK, K.ofBytes_toBytes]; exact hP _,
    by simp only [chK, K.ofBytes_toBytes]; exact hP _⟩
  have := ht 0 (by norm_num) 0 (by have := congrArg (·[0]?) tq_eq.1; simp at this; simp [this])
  rw [capEs_dAt (by norm_num), capEs_capDig _ _ (by norm_num), if_pos (by simp [rdIx, Rev4.capReadsBelow])] at this
  exact absurd this (by decide)

end FR.Snd.T4
