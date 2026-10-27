-- New for `flock-recursive` (BLUEPRINT A.10, §5.4; stage S-G1c).
import FRSoundnessStepC

/-!
# The per-phase truths (BLUEPRINT A.10): Ligerito's words, and the stability of word reads

* **Part A: the level words and their decoding** (A.10 notation). `wordK κ L es i` is level `i`'s
  word in K (`wordOf`, read under its cap), `codeK κ i = RS[K, D, kᵢ]` the level's code,
  **`farL`** (no agreement set makes the word jointly `eᵢ`-close: `far_i`), and **`decodeL`**:
  the codeword rows of a close word (`decodeL_spec`: in the code, agreeing with the word on at
  least `nᵢ − eᵢ` positions); `0` when far.
* **Part B: no bad event, no Merkle hit** (A.10's `hstab` reads). `frEncW i` is level `i`'s
  encoding with `carried` restricted to the query's windows (`wins`); `colL` does not read
  `carried`, so `colL (frEncW i) = colL (frEnc i)` (`colL_frEncW`). **`not_hit_of_not_bad`**:
  `¬ Bad L → ¬ Hit (frEncW i) L` (a hit is a window hit). **`colL_take`**: on a non-bad log, a
  column read under a digest that an entry of the prefix carries is the same on the prefix and on
  the whole log (`colL_prefix`, `colL_append`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: the level words -/

/-- Level `i`'s word in K. -/
noncomputable def wordK (κ : Kind) (L es : Log) (i : ℕ) :
    Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K :=
  fun r p => algebraMap F K (wordOf κ L es i r p)

/-- Level `i`'s code: `RS[K, D, kᵢ]` on the `nᵢ` points `D j` (`encCode_eq_rsCode`). -/
noncomputable def codeK (κ : Kind) (i : ℕ) : Submodule K (Fin (2 ^ (lvl κ i).logN) → K) :=
  rsCode (Dpts (2 ^ (lvl κ i).logN)) (lvK κ i)

/-- **`far_i`**: no agreement set makes level `i`'s word jointly `eᵢ`-close to the code. -/
def farL (κ : Kind) (L es : Log) (i : ℕ) : Prop :=
  ∀ A, ¬ JointClose (codeK κ i) (lvE κ i) (wordK κ L es i) A

theorem not_farL_iff {κ : Kind} {L es : Log} {i : ℕ} :
    ¬ farL κ L es i ↔ ∃ V : Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K,
      (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (lvl κ i).logN - lvE κ i ≤ (jointAgree (wordK κ L es i) V).card := by
  simp only [farL, JointClose, not_forall, not_not]
  constructor
  · rintro ⟨A, hA, V, hV, rfl⟩; exact ⟨V, hV, hA⟩
  · rintro ⟨V, hV, hA⟩; exact ⟨_, hA, V, hV, rfl⟩

open Classical in
/-- **`decodeL`**: the codeword rows of a close word (A.10's `f⁽ⁱ⁾`, before `interp_F` /
`coeffs_of_values`); `0` when far. -/
noncomputable def decodeL (κ : Kind) (L es : Log) (i : ℕ) :
    Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K :=
  if h : ¬ farL κ L es i then Classical.choose (not_farL_iff.mp h) else 0

theorem decodeL_spec {κ : Kind} {L es : Log} {i : ℕ} (h : ¬ farL κ L es i) :
    (∀ r, decodeL κ L es i r ∈ codeK κ i) ∧
      2 ^ (lvl κ i).logN - lvE κ i ≤ (jointAgree (wordK κ L es i) (decodeL κ L es i)).card := by
  rw [decodeL, dite_eq_left h]
  exact Classical.choose_spec (not_farL_iff.mp h)

/-- The words depend on the entries up to the cap's absorb only. -/
theorem farL_congr {κ : Kind} (L : Log) {es es' : Log} {i : ℕ}
    (h : Agree es es' (capPos i + 1)) : farL κ L es i ↔ farL κ L es' i := by
  have : wordK κ L es i = wordK κ L es' i := by
    funext r p; simp only [wordK, wordOf, colOf_congr κ L i p h]
  simp only [farL, this]

/-- Control (positive): on the empty log the word is `0`, a codeword, so it is not far. -/
theorem not_farL_nil (κ : Kind) (es : Log) (i : ℕ) : ¬ farL κ [] es i := by
  rw [not_farL_iff]
  refine ⟨0, fun _ => Submodule.zero_mem _, ?_⟩
  have : wordK κ [] es i = 0 := by
    funext r p; simp [wordK, wordOf_nil]
  rw [this, show jointAgree (0 : Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K) 0 = univ by
    ext; simp]
  simp

/-! ## Part B: no bad event, no Merkle hit -/

/-- Level `i`'s encoding with `carried` restricted to the query's windows. -/
def frEncW (i : ℕ) : MerkleEnc where
  nodeQ := nodeQ i
  colQ := colQ i
  parseNode := parseNode i
  parseCol := parseCol i
  carried q := (carried q).filter fun d => decide (d ∈ wins q)
  parseNode_nodeQ := parseNode_nodeQ i
  nodeQ_of_parseNode := nodeQ_of_parseNode i
  parseCol_colQ := parseCol_colQ i
  carried_nodeQ l r := by
    have hw : ∀ k, k < 4 → 8 + 16 * k + 32 ≤ 72 →
        bytesAt (nodeQ i l r) (8 + 16 * k) 32 ∈ wins (nodeQ i l r) := fun k hk h32 => by
      rw [wins, ite_eq_left (by rw [nodeQ_size]; unfold queryCap; norm_num)]
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨k, ?_, ?_⟩)
      · rw [List.mem_range, nodeQ_size]; omega
      · rw [nodeQ_size, ite_eq_left h32]
    have hl := hw 0 (by norm_num) (by norm_num)
    have hr := hw 2 (by norm_num) (by norm_num)
    rw [show 8 + 16 * 0 = 8 by rfl, bytesAt_nodeQ_l] at hl
    rw [show 8 + 16 * 2 = 40 by rfl, bytesAt_nodeQ_r] at hr
    obtain ⟨cl, cr⟩ := carried_nodeQ i l r
    exact ⟨List.mem_filter.mpr ⟨cl, by simpa using hl⟩, List.mem_filter.mpr ⟨cr, by simpa using hr⟩⟩

/-- `colL` does not read `carried`. -/
theorem colL_frEncW (i : ℕ) (L : Log) : ∀ (h : ℕ) (d : Digest) (j : ℕ),
    colL (frEncW i) L d h j = colL (frEnc i) L d h j
  | 0, _, _ => rfl
  | h + 1, d, j => by
    simp only [colL]
    congr 1; funext e; congr 1; funext ab
    exact colL_frEncW i L h _ j

/-- **No bad event, no Merkle hit**: a hit under `frEncW` is a window hit. -/
theorem not_hit_of_not_bad {L : Log} (hb : ¬ Bad L) (i : ℕ) : ¬ Hit (frEncW i) L := by
  rintro ⟨a, b, hab, hbL, hm⟩
  have hm' := (List.mem_filter.mp hm).2
  simp only [decide_eq_true_eq] at hm'
  exact hb (Or.inr (Or.inl ⟨a, b, hab.le, hbL, hm'⟩))

/-- **`colL_take`**: on a non-bad log, the column read under a digest carried (within its
windows) by an entry of the prefix `L.take n` is the same on the prefix and on `L`. -/
theorem colL_take {L : Log} (hb : ¬ Bad L) (i n : ℕ) {d : Digest}
    (hd : ∃ e ∈ L.take n, d ∈ (frEncW i).carried e.1) (h j : ℕ) :
    colL (frEnc i) (L.take n) d h j = colL (frEnc i) L d h j := by
  have hnh : ¬ Hit (frEncW i) (L.take n ++ L.drop n) := by
    rw [List.take_append_drop]; exact not_hit_of_not_bad hb i
  rw [← colL_frEncW, ← colL_frEncW]
  cases hc : colL (frEncW i) (L.take n) d h j with
  | some col =>
    have := colL_append (E := frEncW i) (L.drop n) hc
    rw [List.take_append_drop] at this; exact this.symm
  | none =>
    cases hc' : colL (frEncW i) L d h j with
    | none => rfl
    | some col =>
      rw [← List.take_append_drop n L] at hc'
      rw [colL_prefix hnh hd hc'] at hc
      cases hc

/-! ## Part C: the cap entries and the cap's own absorb -/

/-- The bytes of a message read at `o` are the absorb query's bytes at `40 + o`. -/
theorem bytesAt_extract40 (q : ByteArray) (o : ℕ) (h : 40 + o + 32 ≤ q.size) :
    bytesAt (q.extract 40 q.size) o 32 = bytesAt q (40 + o) 32 := by
  ext k hk
  simp only [getElem_bytesAt _ _ _ _ hk, ByteArray.data_extract]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getElem?_toList, Array.getElem?_extract]
  simp only [ByteArray.size] at h
  rw [ite_eq_left (by have : q.size = q.data.size := rfl; omega)]
  congr 3
  omega

/-- **(a) A cap entry is carried (within its windows) by the cap's absorb query**: entry `c` of
an absorb of `len ≥ 32(c + 1)` bytes, at offset `40 + 32c = 8 + 16(2 + 2c)`. -/
theorem cap_carried {q : ByteArray} {len : ℕ} (hq : fsCheck (.absorb len) q = true)
    (hcap : q.size ≤ queryCap) {c : ℕ} (hc : 32 * (c + 1) ≤ len) (j : ℕ) :
    bytesAt (q.extract 40 q.size) (32 * c) 32 ∈ (frEncW j).carried q := by
  simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨ht, hs⟩ := hq
  rw [bytesAt_extract40 q _ (by omega)]
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [carried, ht, ite_true]
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, ?_, rfl⟩)
    rw [List.mem_range, hs, Nat.lt_div_iff_mul_lt (by norm_num)]
    omega
  · rw [decide_eq_true_eq, wins, ite_eq_left hcap]
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨2 + 2 * c, ?_, ?_⟩)
    · rw [List.mem_range]; omega
    · rw [ite_eq_left (by omega)]; congr 2; omega

/-- On a non-bad log, an entry answering a digest carried by entry `i` precedes `i`. -/
theorem ans_lt_of_carried {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) {j : ℕ}
    {d : Digest} (hd : d ∈ (frEncW j).carried (L[i]).1) {k : ℕ} (hk : k < L.length)
    (hkd : L[k].2 = d) : k < i := by
  by_contra hki
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hki) with h | h
  · exact not_hit_of_not_bad hb j ⟨i, k, h, hk, hkd ▸ hd⟩
  · have hw := (List.mem_filter.mp hd).2
    simp only [decide_eq_true_eq] at hw
    exact hb (Or.inr (Or.inl ⟨i, k, h.le, hk, hkd ▸ hw⟩))

/-- Under the same hypotheses, the first preimage of `d` is read off `L.take i`. -/
theorem pre_take_own {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) {j : ℕ}
    {d : Digest} (hd : d ∈ (frEncW j).carried (L[i]).1) : pre (L.take i) d = pre L d := by
  have hnone : (L.drop i).find? (fun e => decide (e.2 = d)) = none := by
    rw [List.find?_eq_none]
    intro e he hed
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem he
    rw [List.getElem_drop] at hed
    simp only [decide_eq_true_eq] at hed
    have := ans_lt_of_carried hb hi hd (by simp at hm; omega) hed
    omega
  conv_rhs => rw [← List.take_append_drop i L]
  simp only [pre, List.find?_append, hnone, Option.or_none]

/-- **(b) The cap's own absorb**: on a non-bad log, a column read under a digest carried by entry
`i` (e.g. the cap absorb as a chain's last entry) is the same on `L.take i` and on `L`. -/
theorem colL_take_own {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) {j : ℕ}
    {d : Digest} (hd : d ∈ (frEncW j).carried (L[i]).1) (h p : ℕ) :
    colL (frEnc j) (L.take i) d h p = colL (frEnc j) L d h p := by
  have hpre := pre_take_own hb hi hd
  cases h with
  | zero => simp only [colL, hpre]
  | succ h =>
    simp only [colL]
    rw [hpre]
    cases he : pre L d with
    | none => rfl
    | some e =>
      simp only [Option.bind_some]
      cases hn : (frEnc j).parseNode e.1 with
      | none => rfl
      | some ab =>
        simp only [Option.bind_some]
        have hmem : e ∈ L.take i := by
          rw [← hpre] at he; exact List.mem_of_find?_eq_some he
        have hc : ab.1 ∈ (frEncW j).carried e.1 ∧ ab.2 ∈ (frEncW j).carried e.1 := by
          rw [(frEncW j).nodeQ_of_parseNode e.1 ab.1 ab.2 hn]
          exact (frEncW j).carried_nodeQ _ _
        exact colL_take hb j i ⟨e, hmem, by split <;> simp [hc]⟩ h p

end FR.Snd
