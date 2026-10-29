-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessStepA` (10), `FRSoundnessStepB` (10),
-- `FRSoundnessStepC` (3), `FRSoundnessTruths` (18). Content: 3.x positions and readers (`phStart`,
-- `capPos`, `wordOf`), the level parameters (`lvN`, `lvK`, `lvE`) and the per-level truths the
-- decoder reads (`wordK`, `foldAt`, `sAt`, `msgOf`, `decodeL`, `farL`, `consSet`, …). The 3.x
-- modules import this one.
import FRRSEval
import FRSoundnessCoreSteps

/-! ## From `FRSoundnessStepA` (10 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

/-- **The kind of a chain**: the header's first byte (byte 71 of the seed query
`"FRSEED0" ‖ vk ‖ c ‖ hdr`); `L32` if it is not a kind byte. -/
def kindOf (es : Log) : Kind := (((entAt es 0).1.data[71]?).bind Kind.ofByte?).getD .L32

theorem kindOf_congr {es es' : Log} (h : Agree es es' 1) : kindOf es = kindOf es' := by
  simp only [kindOf, h 0 one_pos]

/-- The Fiat–Shamir position of each phase's first item, in the order of `phases` (a phase with
no Fiat–Shamir item, `Q`, gets the position of the next one). -/
def fsStarts : List ℕ :=
  (phases.foldl (fun (acc : ℕ × List ℕ) p =>
    (acc.1 + (p.shape.items.filter Item.isFS).length, acc.2 ++ [acc.1])) (0, [])).2

/-- The first Fiat–Shamir position of phase `k` of `phases`. -/
def phStart (k : ℕ) : ℕ := fsStarts.getD k 0

/-- Control: the phase starts (A.4; `piopPhases` are phases `0 … 25` (revision 3.12: E4 at 24), level `i`'s
`P1, C, P2, Q, P3` are `26 + 5i … 30 + 5i`, `Pf` is `51`). -/
theorem fsStarts_eq : fsStarts = [0, 1, 2, 3, 13, 15, 67, 68, 69, 97, 98, 99, 114, 170, 178, 208,
    209, 210, 221, 263, 264, 265, 311, 312, 313, 317, 318, 330, 331, 356, 356, 361, 369, 370, 383,
    383, 388, 396, 397, 407, 407, 412, 420, 421, 429, 429, 434, 442, 443, 449, 449, 454] := by
  decide +kernel

/-- The position of level `i`'s cap absorb: `cap₀` (phase 2), else `C.(i − 1)` (phase `22 + 5i`). -/
def capPos (i : ℕ) : ℕ := if i = 0 then phStart 2 else phStart (22 + 5 * i)

/-- Cap entry `c` of level `i`: the 32 bytes at offset `32c` of the cap's message (A.2). -/
def capDig (es : Log) (i c : ℕ) : Digest := bytesAt (msgAt es (capPos i)) (32 * c) 32

/-- **The column of level `i` at position `p`** for kind `k`, read off `L` top-down from its cap
entry (`p / 2^sib`) along the bits of `p` (`colL (frEnc i)`, height `sib = log₂ n − cap`). -/
def colOf (k : Kind) (L es : Log) (i p : ℕ) : Option ByteArray :=
  colL (frEnc i) L (capDig es i (p / 2 ^ (lvl k i).sib)) (lvl k i).sib p

/-- **The committed word of level `i`**: row `r` at position `p` is the column's F element `r`
(16 bytes each, row 0 first, A.2); `0` where `L` reads no column. -/
def wordOf (k : Kind) (L es : Log) (i : ℕ) : Fin (lvl k i).rows → Fin (2 ^ (lvl k i).logN) → F :=
  fun r p => ((colOf k L es i p).map fun col => readF col (16 * r)).getD 0

/-- The column depends on the entries up to the cap's absorb only. -/
theorem colOf_congr (k : Kind) (L : Log) {es es' : Log} (i p : ℕ)
    (h : Agree es es' (capPos i + 1)) : colOf k L es i p = colOf k L es' i p := by
  simp only [colOf, capDig, msgAt, h (capPos i) (by omega)]

end FR.Snd

end

/-! ## From `FRSoundnessStepB` (10 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

section Rounds3

variable (b : ℕ)

variable (c0 : Log → Log → F)

variable (nr : Kind → ℕ)

/-- The rounds answered by the entries `es`: `min (nr (kindOf es)) ⌊(|es| − b)/2⌋`. -/
def ans3 (es : Log) : ℕ := min (nr (kindOf es)) ((es.length - b) / 2)

variable (e : Expr) (T : Log → Log → Array (Array F))

/-- The claim after `l` rounds is not the true sum of the tables bound at the first `l`
challenges. -/
def Wrong3 (L es : Log) (l : ℕ) : Prop :=
  clR b c0 L es l ≠ trueSum e (bindAll (T L es) (rchs b es l)) (nr (kindOf es) - l)

/-- **The round doom** (§5.2 row Z3): past the phase's first absorb, the running claim after the
answered rounds is false. -/
def D3 (L es : Log) : Prop := b < es.length ∧ Wrong3 b c0 nr e T L es (ans3 b nr es)

variable {b c0 nr e T}

theorem wrong3_congr (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) : Wrong3 b c0 nr e T L es l ↔ Wrong3 b c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong3, clR_congr hc h, rchs_congr h, hT, kindOf_congr (hb.mono hb1)]

theorem kindOf_append {es : Log} (x : ByteArray × Digest) (h : 0 < es.length) :
    kindOf (es ++ [x]) = kindOf es :=
  kindOf_congr (agree_append es [x] h)

/-- When the next position is not a real round's squeeze, appending keeps the answered rounds and
the doom. -/
theorem D3_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2) :
    D3 b c0 nr e T L (es ++ [x]) ↔ D3 b c0 nr e T L es := by
  have hk := kindOf_append x (show 0 < es.length by omega)
  have ha : ans3 b nr (es ++ [x]) = ans3 b nr es := by
    simp only [ans3, hk, List.length_append, List.length_singleton]
    rcases hc with hc | hc
    · rw [show (es.length + 1 - b) / 2 = (es.length - b) / 2 by omega]
    · rw [min_eq_left hc, min_eq_left (le_trans hc (Nat.div_le_div_right (by omega)))]
  have hle : b + 2 * ans3 b nr es ≤ es.length := by
    have : ans3 b nr es ≤ (es.length - b) / 2 := min_le_right _ _
    omega
  simp only [D3, ha, List.length_append, List.length_singleton]
  rw [wrong3_congr hb1 hTc (agree_append es [x] hle)]
  exact ⟨fun h => ⟨hlen, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem not_D3_short {L es : Log} (h : es.length ≤ b) : ¬ D3 b c0 nr e T L es :=
  fun hd => by have := hd.1; omega

/-- At a real round's squeeze, the extension answers one more round, and its claim and truth
are the round polynomial and the bound tables at the answer's first F coordinate. -/
theorem wrong3_ext1 (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (L es : Log) (a : Digest) {j : ℕ}
    (hj : es.length = b + 2 * j + 1) :
    Wrong3 b c0 nr e T L (ext1 es a) (j + 1) ↔
      peval (g3At b es j (clR b c0 L es j)) (chF a 0) ≠
        trueSum e ((bindAll (T L es) (rchs b es j)).map (bind0 · (chF a 0)))
          (nr (kindOf es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
  have hr : rch b (ext1 es a) j = chF a 0 := by
    simp only [rch, fAt, ansAt]
    rw [← hj, entAt_ext1]
  obtain ⟨hT, hc0⟩ := hTc L (ext1 es a) es (hA.mono (by omega))
  have hcl : clR b c0 L (ext1 es a) j = clR b c0 L es j :=
    clR_congr (l := j) hc0 (hA.mono (by omega))
  have hg : g3At b (ext1 es a) j (clR b c0 L es j) = g3At b es j (clR b c0 L es j) := by
    simp only [g3At, msgAt, hA (b + 2 * j) (by omega)]
  have hrs : rchs b (ext1 es a) j = rchs b es j := rchs_congr (l := j) (hA.mono (by omega))
  simp only [Wrong3, clR, hcl, hg, hr, rchs_succ, hrs, hT, hk, bindAll_append]

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **The round row** (§5.2 Z3): from a doomed claim, at most `3·2^128` answers make the next
claim true. -/
theorem D3_single (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (he : e.deg = 3)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOf es)) (L es : Log) :
    (Finset.univ.filter fun a => D3 b c0 nr e T L es ∧ ¬ D3 b c0 nr e T L (ext1 es a)).card ≤
      3 * 2 ^ 128 := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D3_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2 ((D3_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOf es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong3 b c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs b es j), t.size = 2 ^ (nr (kindOf es) - j - 1 + 1) := by
    refine bindAll_size (rchs b es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs b es j)) hts
    (claim := clR b c0 L es j) (by
      rw [show nr (kindOf es) - j - 1 + 1 = nr (kindOf es) - j by omega]; exact hw)
    (g3At b es j (clR b c0 L es j))
  refine le_trans (Finset.card_le_card (t := Finset.univ.filter fun a : Digest => chF a 0 ∈ _)
    fun a ha => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  have hnd : ¬ D3 b c0 nr e T L (ext1 es a) := by
    rw [Finset.mem_filter] at ha; exact ha.2.2
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong3 b c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong3_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨by rw [he]; rfl, g3_check es j _⟩, ?_⟩
  rw [hnw, show nr (kindOf es) - (j + 1) = nr (kindOf es) - j - 1 by omega]

theorem D3_log_congr {L L' X : Log} (hT : T L' X = T L X) (hc : c0 L' X = c0 L X) :
    D3 b c0 nr e T L' X ↔ D3 b c0 nr e T L X := by
  simp only [D3, Wrong3, clR_log_congr hc, hT]

end Rounds3

end FR.Snd

end

/-! ## From `FRSoundnessStepC` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- The proximity parameters of level `i` of kind `κ`: `n = 2^log₂n`, `k = n/2^(i+1)`,
`e = ⌊(n − k)/2⌋` (§2.2). -/
def lvN (κ : Kind) (i : ℕ) : ℕ := 2 ^ (lvl κ i).logN

def lvK (κ : Kind) (i : ℕ) : ℕ := lvN κ i / 2 ^ (i + 1)

def lvE (κ : Kind) (i : ℕ) : ℕ := (lvN κ i - lvK κ i) / 2

end FR.Snd

end

/-! ## From `FRSoundnessTruths` (18 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

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

/-- P1.i's fold challenge `l` (K): the answer of round `l`'s squeeze. -/
def sAt (es : Log) (i l : ℕ) : K := kAt es (phStart (26 + 5 * i) + 2 * l + 1)

/-- **The column fold `y_j`** of level `i` at position `j`: `Σ_r eq(sᵢ, r)·W⁽ⁱ⁾[r][j]`. -/
noncomputable def foldAt (κ : Kind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (lvl κ i).logN)) : K :=
  ∑ r : Fin (lvl κ i).rows, eqBits (sAt es i) (lvl κ i).ell r * wordK κ L es i r j

/-- `log₂ kᵢ`: level `i`'s message length is `kᵢ = nᵢ / 2^(i+1) = 2^mLog`. -/
def mLog (κ : Kind) (i : ℕ) : ℕ := (lvl κ i).logN - (i + 1)

/-- **Row `r`'s message** of level `i`'s decoded word (`f⁽ⁱ⁾`'s row `r`: novel-basis
coefficients by `coeffs_of_values` on `D[0, kᵢ)`); `0` past the rows or the message. -/
noncomputable def msgOf (κ : Kind) (L es : Log) (i r : ℕ) : ℕ → K := fun x =>
  if hr : r < (lvl κ i).rows then
    if hx : x < 2 ^ mLog κ i then
      coeffsOfValuesD (mLog κ i) (fun j => if hj : j < 2 ^ (lvl κ i).logN then
        decodeL κ L es i ⟨r, hr⟩ ⟨j, hj⟩ else 0) ⟨x, hx⟩
    else 0
  else 0

/-- `f⁽ⁱ⁾` as a table over level `i`'s variables (row bits first, as P1.i folds them). -/
noncomputable def fTab (κ : Kind) (L es : Log) (i y : ℕ) : K :=
  msgOf κ L es i (y % (lvl κ i).rows) (y / (lvl κ i).rows)

/-- The final message's element `x` (absorbed at C.4, phase 46). -/
def finalAt (es : Log) (x : ℕ) : K := readK (msgAt es (phStart 47)) (32 * x)

/-- **`f⁽ⁱ⁺¹⁾` as level `i`'s folded message**: K element `x` from level `i + 1`'s rows
`2(x mod 8)` and `2(x mod 8) + 1`, column `x div 8` (`i < 4`); the final message (`i = 4`). -/
noncomputable def nextMsg (κ : Kind) (L es : Log) (i x : ℕ) : K :=
  if i + 1 < nLevels then
    msgOf κ L es (i + 1) (2 * (x % 8)) (x / 8) +
      K.u * msgOf κ L es (i + 1) (2 * (x % 8) + 1) (x / 8)
  else finalAt es x

/-- Level `i`'s encoding of a message at position `j` (`Enc_{kᵢ}` in the novel basis on `D`). -/
noncomputable def encAt (κ : Kind) (i : ℕ) (m : ℕ → K) (j : ℕ) : K :=
  encF (mLog κ i) (fun x => m x) j

/-- **P2.i's consistency set `A_c`** (A.10): the positions where the column fold agrees with the
next level's codeword. -/
noncomputable def consSet (κ : Kind) (L es : Log) (i : ℕ) : Finset (Fin (2 ^ (lvl κ i).logN)) :=
  univ.filter fun j => foldAt κ L es i j = encAt κ i (nextMsg κ L es i) j

/-- The level parameters the uniqueness argument uses (checked per level and kind). -/
theorem lv_params (κ : Kind) {i : ℕ} (hi : i < 5) :
    2 * lvE κ i + lvK κ i ≤ lvN κ i ∧ lvN κ i ≤ nMax ∧ mLog κ i ≤ logNMax ∧
      lvK κ i = 2 ^ mLog κ i ∧ lvN κ i = 2 ^ (lvl κ i).logN := by
  cases κ <;> interval_cases i <;> decide

/-- A codeword of level `i`'s code is `Enc` of a message of `2^mLog` coefficients. -/
theorem exists_msg {κ : Kind} {i : ℕ} (hi : i < 5) {v : Fin (2 ^ (lvl κ i).logN) → K}
    (hv : v ∈ codeK κ i) : ∃ c : Fin (2 ^ mLog κ i) → K, enc D _ _ c = v := by
  obtain ⟨-, hN, -, hk, hn⟩ := lv_params κ hi
  rw [codeK, hk, ← encCode_D (by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN)]
    at hv
  exact LinearMap.mem_range.mp hv

/-- `coeffs_of_values` gives back the message of a codeword. -/
theorem msgOf_eq {κ : Kind} {L es : Log} {i : ℕ} (hi : i < 5) {r : Fin (lvl κ i).rows}
    {c : Fin (2 ^ mLog κ i) → K} (hc : enc D _ _ c = decodeL κ L es i r) (x : Fin (2 ^ mLog κ i)) :
    msgOf κ L es i r x = c x := by
  obtain ⟨-, hN, hm, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (lvl κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  simp only [msgOf, r.2, x.2, dite_true]
  rw [coeffsOfValuesD, coeffs_unique D_xor D_injOn_nMax hm _ c fun j hj => ?_]
  simp only [show j < 2 ^ (lvl κ i).logN from lt_of_lt_of_le hj hkn, dite_true]
  rw [← hc, enc_eq_encN]

end FR.Snd

end
