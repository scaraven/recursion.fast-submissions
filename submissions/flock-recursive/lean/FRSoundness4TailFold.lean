-- G6: this module also holds the former modules `FRSoundness4TailTruths`, `FRSoundness4TailHide` (one section each, in import order).
import FRSoundness4TailStep
import FRSoundnessCoreTruths
import FRBlockKinds

section G6_FRSoundness4TailTruths

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTruths` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The tail truths at `seq4` (T4)

The 3.x declarations of `FRSoundnessTruths` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTruths` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: the level words -/

/-- Level `i`'s word in K. -/
noncomputable def wordK (κ : CKind) (L es : Log) (i : ℕ) :
    Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K :=
  fun r p => algebraMap F K (wordOf κ L es i r p)

/-- Level `i`'s code: `RS[K, D, kᵢ]` on the `nᵢ` points `D j` (`encCode_eq_rsCode`). -/
noncomputable def codeK (κ : CKind) (i : ℕ) : Submodule K (Fin (2 ^ (CKind.lv κ i).logN) → K) :=
  rsCode (Dpts (2 ^ (CKind.lv κ i).logN)) (lvK κ i)

/-- **`far_i`**: no agreement set makes level `i`'s word jointly `eᵢ`-close to the code. -/
def farL (κ : CKind) (L es : Log) (i : ℕ) : Prop :=
  ∀ A, ¬ JointClose (codeK κ i) (lvE κ i) (wordK κ L es i) A

theorem not_farL_iff {κ : CKind} {L es : Log} {i : ℕ} :
    ¬ farL κ L es i ↔ ∃ V : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K,
      (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (jointAgree (wordK κ L es i) V).card := by
  simp only [farL, JointClose, not_forall, not_not]
  constructor
  · rintro ⟨A, hA, V, hV, rfl⟩; exact ⟨V, hV, hA⟩
  · rintro ⟨V, hV, hA⟩; exact ⟨_, hA, V, hV, rfl⟩

open Classical in
/-- **`decodeL`**: the codeword rows of a close word (A.10's `f⁽ⁱ⁾`, before `interp_F` /
`coeffs_of_values`); `0` when far. -/
noncomputable def decodeL (κ : CKind) (L es : Log) (i : ℕ) :
    Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K :=
  if h : ¬ farL κ L es i then Classical.choose (not_farL_iff.mp h) else 0

theorem decodeL_spec {κ : CKind} {L es : Log} {i : ℕ} (h : ¬ farL κ L es i) :
    (∀ r, decodeL κ L es i r ∈ codeK κ i) ∧
      2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (jointAgree (wordK κ L es i) (decodeL κ L es i)).card := by
  rw [decodeL, dite_eq_left h]
  exact Classical.choose_spec (not_farL_iff.mp h)

/-- The words depend on the entries up to the cap's absorb only. -/
theorem farL_congr {κ : CKind} (L : Log) {es es' : Log} {i : ℕ}
    (h : Agree es es' (capPos i + 1)) : farL κ L es i ↔ farL κ L es' i := by
  have : wordK κ L es i = wordK κ L es' i := by
    funext r p; simp only [wordK, wordOf, colOf_congr κ L i p h]
  simp only [farL, this]

/-- Control (positive): on the empty log the word is `0`, a codeword, so it is not far. -/
theorem not_farL_nil (κ : CKind) (es : Log) (i : ℕ) : ¬ farL κ [] es i := by
  rw [not_farL_iff]
  refine ⟨0, fun _ => Submodule.zero_mem _, ?_⟩
  have : wordK κ [] es i = 0 := by
    funext r p; simp [wordK, wordOf_nil]
  rw [this, show jointAgree (0 : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K) 0 = univ by
    ext; simp]
  simp

/-! ## Part B: no bad event, no Merkle hit -/

/-! ## Part C: the cap entries and the cap's own absorb -/

/-! ## Part D: Ligerito's per-level truths (A.10: P1.i, C.i, P2.i, P3.i, Pf)

The layout is the native prover's (`ligerito.rs::prove`, `ntt.rs::encode`): level `i`'s row `r`
encodes the message coefficients `c ↦ f[c·rows + r]` in the novel basis; the next level's F
vector is the folded K message split into coordinates (`split`: F element `2x + b` is coordinate
`b` of K element `x`), so K element `x` of the fold sits in rows `2(x mod 8) + b`, column
`x div 8` of level `i + 1` (16 rows). -/

/-- P1.i's fold challenge `l` (K): the answer of round `l`'s squeeze. -/
def sAt (es : Log) (i l : ℕ) : K := kAt es (phStart4 (26 + 5 * i) + 2 * l + 1)

/-- **The column fold `y_j`** of level `i` at position `j`: `Σ_r eq(sᵢ, r)·W⁽ⁱ⁾[r][j]`. -/
noncomputable def foldAt (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) : K :=
  ∑ r : Fin (CKind.lv κ i).rows, eqBits (sAt es i) (CKind.lv κ i).ell r * wordK κ L es i r j

/-- `log₂ kᵢ`: level `i`'s message length is `kᵢ = nᵢ / 2^(i+1) = 2^mLog`. -/
def mLog (κ : CKind) (i : ℕ) : ℕ := (CKind.lv κ i).logN - (i + 1)

/-- **Row `r`'s message** of level `i`'s decoded word (`f⁽ⁱ⁾`'s row `r`: novel-basis
coefficients by `coeffs_of_values` on `D[0, kᵢ)`); `0` past the rows or the message. -/
noncomputable def msgOf (κ : CKind) (L es : Log) (i r : ℕ) : ℕ → K := fun x =>
  if hr : r < (CKind.lv κ i).rows then
    if hx : x < 2 ^ mLog κ i then
      coeffsOfValuesD (mLog κ i) (fun j => if hj : j < 2 ^ (CKind.lv κ i).logN then
        decodeL κ L es i ⟨r, hr⟩ ⟨j, hj⟩ else 0) ⟨x, hx⟩
    else 0
  else 0

/-- `f⁽ⁱ⁾` as a table over level `i`'s variables (row bits first, as P1.i folds them). -/
noncomputable def fTab (κ : CKind) (L es : Log) (i y : ℕ) : K :=
  msgOf κ L es i (y % (CKind.lv κ i).rows) (y / (CKind.lv κ i).rows)

/-- **`fold_z(f⁽ⁱ⁾)`**: the decoded messages folded by P1.i's challenges. -/
noncomputable def foldMsg (κ : CKind) (L es : Log) (i x : ℕ) : K :=
  ∑ r : Fin (CKind.lv κ i).rows, eqBits (sAt es i) (CKind.lv κ i).ell r * msgOf κ L es i r x

/-- The final message's element `x` (absorbed at C.4, phase 46). -/
def finalAt (es : Log) (x : ℕ) : K := readK (msgAt es (phStart4 47)) (32 * x)

/-- **`f⁽ⁱ⁺¹⁾` as level `i`'s folded message**: K element `x` from level `i + 1`'s rows
`2(x mod 8)` and `2(x mod 8) + 1`, column `x div 8` (`i < 4`); the final message (`i = 4`). -/
noncomputable def nextMsg (κ : CKind) (L es : Log) (i x : ℕ) : K :=
  if i + 1 < nLevels then
    msgOf κ L es (i + 1) (2 * (x % 8)) (x / 8) +
      K.u * msgOf κ L es (i + 1) (2 * (x % 8) + 1) (x / 8)
  else finalAt es x

/-- Level `i`'s encoding of a message at position `j` (`Enc_{kᵢ}` in the novel basis on `D`). -/
noncomputable def encAt (κ : CKind) (i : ℕ) (m : ℕ → K) (j : ℕ) : K :=
  encF (mLog κ i) (fun x => m x) j

/-- **P2.i's consistency set `A_c`** (A.10): the positions where the column fold agrees with the
next level's codeword. -/
noncomputable def consSet (κ : CKind) (L es : Log) (i : ℕ) : Finset (Fin (2 ^ (CKind.lv κ i).logN)) :=
  univ.filter fun j => foldAt κ L es i j = encAt κ i (nextMsg κ L es i) j

/-- **`truthP2 i`**: the next level's codeword is `eᵢ`-close to the fold (`|A_c| ≥ nᵢ − eᵢ`).
P2.i is doomed when this fails and every queried index lands in `A_c`. -/
def truthP2 (κ : CKind) (L es : Log) (i : ℕ) : Prop :=
  lvN κ i - lvE κ i ≤ (consSet κ L es i).card

/-- When `truthP2` fails, `A_c` is small enough for `p2_hround` (`|A_c| + eᵢ < nᵢ`). -/
theorem consSet_card_of_not (κ : CKind) {L es : Log} {i : ℕ} (h : ¬ truthP2 κ L es i) :
    (consSet κ L es i).card + lvE κ i < lvN κ i := by
  have : lvE κ i ≤ lvN κ i := by unfold lvE; omega
  unfold truthP2 at h; omega

/-- **`truthC i`** (A.10, C.i): the next level's message is the fold of level `i`'s decoded
messages. -/
def truthC (κ : CKind) (L es : Log) (i : ℕ) : Prop :=
  ∀ x < 2 ^ mLog κ i, nextMsg κ L es i x = foldMsg κ L es i x

/-- P3.i's consistency coefficient point `κ_c` (the first 9 F coordinates of P3.i). -/
def kcAt (es : Log) (i v : ℕ) : F := coordAt es (phStart4 (30 + 5 * i) - 1) v

/-- P2.i's queried position `q` (A.2: index `q mod per` of answer `q div per`). -/
def qPos (κ : CKind) (es : Log) (i q : ℕ) : ℕ :=
  posAt es (phStart4 (27 + 5 * i)) (CKind.lv κ i).logN (CKind.lv κ i).per q

/-- The column fold at an `ℕ` position (`0` off the code). -/
noncomputable def foldAtN (κ : CKind) (L es : Log) (i j : ℕ) : K :=
  if hj : j < 2 ^ (CKind.lv κ i).logN then foldAt κ L es i ⟨j, hj⟩ else 0

/-- Query `q`'s consistency error `y_q − Enc(f⁽ⁱ⁺¹⁾)[p_q]`. -/
noncomputable def consErr (κ : CKind) (L es : Log) (i q : ℕ) : K :=
  foldAtN κ L es i (qPos κ es i q) - encAt κ i (nextMsg κ L es i) (qPos κ es i q)

/-- **`truthP3 i`** (A.10): every queried fold is the next level's codeword symbol. -/
def truthP3 (κ : CKind) (L es : Log) (i : ℕ) : Prop := ∀ q < (CKind.lv κ i).t, consErr κ L es i q = 0

/-- P3.i's batched consistency `Σ_q eq(κ_c, bits₉(q))·(y_q − Enc[p_q])`: P3.i is doomed when
`truthP3` fails and this vanishes (`9/2^128`, Schwartz–Zippel over `κ_c`). -/
noncomputable def p3Batch (κ : CKind) (L es : Log) (i : ℕ) : K :=
  ∑ q ∈ range (CKind.lv κ i).t, K.smulF (eqBits (kcAt es i) 9 q) (consErr κ L es i q)

/-- **`truthP1 i`** (A.10), in the level's weight table `W` (a parameter: level 0's is
`rsWeight`'s and `evalM`'s, later levels add the tensor weights): on a close word, a claim `c`
is `⟨W, f⁽ⁱ⁾⟩` over level `i`'s variables. -/
noncomputable def truthP1 (κ : CKind) (L es : Log) (i : ℕ) (W : ℕ → K) (c : K) : Prop :=
  ¬ farL κ L es i →
    c = ∑ y ∈ range (2 ^ ((CKind.lv κ i).ell + mLog κ i)), W y * fTab κ L es i y

/-- **`truthPf`** (A.10), in the folded weight `W` over the final message's 7 variables. -/
noncomputable def truthPf (es : Log) (W : ℕ → K) (c : K) : Prop :=
  c = ∑ x ∈ range finalElems, W x * finalAt es x

/-! ### Controls -/

/-- On the empty log the word is `0`, so every column fold is `0`. -/
theorem foldAt_nil (κ : CKind) (es : Log) (i : ℕ) : foldAt κ [] es i = 0 := by
  funext j; simp [foldAt, wordK, wordOf_nil]

/-- `truthP3` is not vacuous: a nonzero error of query `0` refutes it (levels have queries). -/
theorem not_truthP3_of (κ : CKind) {L es : Log} {i : ℕ} (hi : 0 < (CKind.lv κ i).t)
    (h : consErr κ L es i 0 ≠ 0) : ¬ truthP3 κ L es i := fun hT => h (hT 0 hi)

/-- Every level of both ladders has queries (`tᵢ > 0`). -/
theorem lvl_t_pos (κ : CKind) {i : ℕ} (hi : i < 5) : 0 < (CKind.lv κ i).t := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- The message logs: `kᵢ = 2^mLog` is `lvK` (`m = 32`: `19, 16, 13, 10, 7`; T4: `m = 31`:
`18, 15, 12, 9, 6`; `m = 30`: `17, 14, 11, 8, 5`). The six kinds' table. -/
theorem mLog_eq : (List.range 5).map (mLog (.seg .L32)) = [19, 16, 13, 10, 7] ∧
    (List.range 5).map (mLog (.seg .L31)) = [18, 15, 12, 9, 6] ∧
    (List.range 5).map (mLog (.seg .L30)) = [17, 14, 11, 8, 5] ∧
    (List.range 5).map (mLog (.node .N2)) = [18, 15, 12, 9, 6] ∧
    (List.range 5).map (mLog (.node .N4)) = [19, 16, 13, 10, 7] ∧
    (List.range 5).map (mLog (.node .N8)) = [19, 16, 13, 10, 7] ∧
    ∀ κ, ∀ i < 5, 2 ^ mLog κ i = lvK κ i := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, fun κ i hi => ?_⟩
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-! ## Part E: uniqueness (A.10, C.i from P2.i), and the node stream's padding

**`truthC_of`**: a close level-`i` word and `truthP2 i` give `truthC i`. The decoded rows are
`Enc` of messages (`exists_msg`), which `msgOf` recovers (`msgOf_eq`, `coeffs_unique`); their fold
is a codeword agreeing with the column fold on the joint agreement set, the next level's codeword
agrees with it on `A_c`, both sets have at least `nᵢ − eᵢ` positions, so the two codewords agree on
`nᵢ − 2eᵢ ≥ kᵢ` positions (`card_inter_ge`, `lv_params`) and are equal (`rs_eq_of_agree`); `Enc` is
injective (`enc_injective`).

T4: **`stream_padded` is not copied**: it is a fact about 3.x's node stream `FR.streamBytes`;
revision 4.1's padding is a claim of the node relation (R-4-m2). 3.x: the node's hashed stream is `1,481,344 = 64 · 23,146`
bytes (`streamBytes_eq`; revision 3.13 with E4 end's 16 zero bytes, INT-2), so its last block is
full and `Stream.Padded` holds for every assignment: `stream_sound`'s padding hypothesis needs no
point claim. -/

/-- The level parameters the uniqueness argument uses (checked per level and kind). -/
theorem lv_params (κ : CKind) {i : ℕ} (hi : i < 5) :
    2 * lvE κ i + lvK κ i ≤ lvN κ i ∧ lvN κ i ≤ nMax ∧ mLog κ i ≤ logNMax ∧
      lvK κ i = 2 ^ mLog κ i ∧ lvN κ i = 2 ^ (CKind.lv κ i).logN := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- A codeword of level `i`'s code is `Enc` of a message of `2^mLog` coefficients. -/
theorem exists_msg {κ : CKind} {i : ℕ} (hi : i < 5) {v : Fin (2 ^ (CKind.lv κ i).logN) → K}
    (hv : v ∈ codeK κ i) : ∃ c : Fin (2 ^ mLog κ i) → K, enc D _ _ c = v := by
  obtain ⟨-, hN, -, hk, hn⟩ := lv_params κ hi
  rw [codeK, hk, ← encCode_D (by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN)]
    at hv
  exact LinearMap.mem_range.mp hv

/-- `coeffs_of_values` gives back the message of a codeword. -/
theorem msgOf_eq {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) {r : Fin (CKind.lv κ i).rows}
    {c : Fin (2 ^ mLog κ i) → K} (hc : enc D _ _ c = decodeL κ L es i r) (x : Fin (2 ^ mLog κ i)) :
    msgOf κ L es i r x = c x := by
  obtain ⟨-, hN, hm, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (CKind.lv κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  simp only [msgOf, r.2, x.2, dite_true]
  rw [coeffsOfValuesD, coeffs_unique D_xor D_injOn_nMax hm _ c fun j hj => ?_]
  simp only [show j < 2 ^ (CKind.lv κ i).logN from lt_of_lt_of_le hj hkn, dite_true]
  rw [← hc, enc_eq_encN]

/-- **The uniqueness lemma** (A.10, C.i from P2.i): if level `i`'s word is close (`¬ far_i`) and
the next level's codeword agrees with the column fold on at least `nᵢ − eᵢ` positions
(`truthP2`), the next level's message is the fold of level `i`'s decoded messages (`truthC`): two
codewords of `RS[K, D, kᵢ]` agreeing on `nᵢ − 2eᵢ ≥ kᵢ` positions are equal, and `Enc` is
injective. -/
theorem truthC_of {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ farL κ L es i)
    (h2 : truthP2 κ L es i) : truthC κ L es i := by
  classical
  obtain ⟨hek, hN, hm, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (CKind.lv κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  have hnN : 2 ^ (CKind.lv κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := decodeL_spec hfar
  choose c hc using fun r => exists_msg hi (hV r)
  set s : Fin (CKind.lv κ i).rows → K := fun r => eqBits (sAt es i) (CKind.lv κ i).ell r
  set cs : Fin (2 ^ mLog κ i) → K := ∑ r, s r • c r
  set nx : Fin (2 ^ mLog κ i) → K := fun x => nextMsg κ L es i x
  -- the fold of the decoded rows, as a codeword
  have hfold : ∀ j ∈ jointAgree (wordK κ L es i) (decodeL κ L es i),
      foldAt κ L es i j = enc D _ _ cs j := by
    intro j hj
    rw [mem_jointAgree] at hj
    have : enc D (2 ^ (CKind.lv κ i).logN) _ cs = ∑ r, s r • enc D _ _ (c r) := by
      change (encL (M := K) D _ _) cs = ∑ r, s r • (encL (M := K) D _ _) (c r)
      simp only [cs, map_sum, map_smul]
    rw [this, foldAt]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, hj, s]
  have hcons : ∀ j ∈ consSet κ L es i, foldAt κ L es i j = enc D _ _ nx j := by
    intro j hj
    simp only [consSet, mem_filter, mem_univ, true_and] at hj
    rw [hj, encAt, encF_eq hm (lt_of_lt_of_le j.2 hnN), enc_eq_encN]
  have hcode : ∀ c' : Fin (2 ^ mLog κ i) → K, enc D (2 ^ (CKind.lv κ i).logN) _ c' ∈
      rsCode (Dpts (2 ^ (CKind.lv κ i).logN)) (2 ^ mLog κ i) := fun c' => by
    rw [← encCode_D (hkn.trans hnN)]; exact LinearMap.mem_range_self _ c'
  have h2' : 2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (consSet κ L es i).card := h2
  have hk2 : 2 ^ mLog κ i ≤ 2 ^ (CKind.lv κ i).logN - 2 * lvE κ i := by rw [← hk, ← hn]; omega
  have hint := card_inter_ge hJ h2'
  have heq : enc D (2 ^ (CKind.lv κ i).logN) _ cs = enc D _ _ nx :=
    rs_eq_of_agree (Dpts_injective hnN) (hcode cs) (hcode nx)
      (jointAgree (wordK κ L es i) (decodeL κ L es i) ∩ consSet κ L es i)
      (hk2.trans hint) fun j hj => by
        rw [mem_inter] at hj; rw [← hfold j hj.1, hcons j hj.2]
  have hinj := enc_injective (M := K) D_injOn_nMax (hkn.trans hnN) hnN hkn heq
  intro x hx
  have := congrFun hinj ⟨x, hx⟩
  simp only [cs, nx, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [← this, foldMsg]
  refine sum_congr rfl fun r _ => ?_
  rw [msgOf_eq hi (hc r) ⟨x, hx⟩]

/-! ## Part F: the weight tables `W_i` (A.10, P1.i / P3.i / C.i)

The weights move from level to level in two steps:
* **P3.i** (`wNext`, `vNext`, **`vNext_eq`**): the batched claim
  `v_{i+1} = c + Σ_q eq(κ_c, bits₉(q))·y_q` is the inner product of the folded message `f⁽ⁱ⁺¹⁾`
  (`nextMsg`) with `wNext Wf = Wf + Σ_q eq(κ_c, q)·G_{p_q}`, where `G_p(x) = X_x(D[p])` (`gW`,
  whose MLE is `tensorW p`), given `truthC` and `truthP3`.
* **The coordinate split** (`wSplit`, **`wSplit_sum`**): over level `i + 1`'s own variables, the
  table is `wSplit (wNext Wf)`, the split bit weighted `1` or `u` (its MLE: A.9's `û(β)`).

Level `0`'s table (from `rsWeight`, `evalM(r_{E2}, ·)` and the public cells, A.9 `finPf`) stays a
parameter here; `ligerito_final` (S-G2) relates `finPf`'s `lvsV` to it. -/

/-- The codeword weight of position `p` at level `i`: `Enc(m)[p] = Σ_x m_x · G_p(x)`, with
`G_p(x) = X_x(D[p]) = Π_{v : bit v of x} Ŵ_v(D[p])` (`encF`; its MLE is `tensorW p`, A.1). -/
def gW (κ : CKind) (i p x : ℕ) : K := bitProd (fun v => algebraMap F K (wAtD v p)) (mLog κ i) x

theorem encAt_eq_sum (κ : CKind) (i : ℕ) (m : ℕ → K) (p : ℕ) :
    encAt κ i m p = ∑ x ∈ range (2 ^ mLog κ i), m x * gW κ i p x := by
  rw [encAt, encF, ← Fin.sum_univ_eq_sum_range (fun x => m x * gW κ i p x)]
  rfl

/-- **P3.i's weight table** over level `i`'s folded message (A.10, P3.i): the folded weight
`Wf` plus the queried positions' codeword weights `Σ_q eq(κ_c, bits₉(q))·G_{p_q}`. -/
noncomputable def wNext (κ : CKind) (es : Log) (i : ℕ) (Wf : ℕ → K) (x : ℕ) : K :=
  Wf x + ∑ q ∈ range (CKind.lv κ i).t, K.smulF (eqBits (kcAt es i) 9 q) (gW κ i (qPos κ es i q) x)

/-- P3.i's batched claim `v_{i+1} = c_{P1.i} + Σ_q eq(κ_c, bits₉(q))·y_q` (A.9 `finP i`). -/
noncomputable def vNext (κ : CKind) (L es : Log) (i : ℕ) (c : K) : K :=
  c + ∑ q ∈ range (CKind.lv κ i).t, K.smulF (eqBits (kcAt es i) 9 q) (foldAtN κ L es i (qPos κ es i q))

/-- **The batched claim is the next weight's inner product** (A.10, P3.i → P1.(i+1)): if the
folded claim is `⟨Wf, fold_z(f⁽ⁱ⁾)⟩`, the fold is the next message (`truthC`) and every queried
fold is its codeword symbol (`truthP3`), then `v_{i+1} = ⟨wNext Wf, f⁽ⁱ⁺¹⁾⟩` over the folded
message. -/
theorem vNext_eq {κ : CKind} {L es : Log} {i : ℕ} {Wf : ℕ → K} {c : K}
    (hc : c = ∑ x ∈ range (2 ^ mLog κ i), Wf x * foldMsg κ L es i x)
    (hC : truthC κ L es i) (h3 : truthP3 κ L es i) :
    vNext κ L es i c = ∑ x ∈ range (2 ^ mLog κ i), wNext κ es i Wf x * nextMsg κ L es i x := by
  have hq : ∀ q ∈ range (CKind.lv κ i).t, foldAtN κ L es i (qPos κ es i q) =
      ∑ x ∈ range (2 ^ mLog κ i), nextMsg κ L es i x * gW κ i (qPos κ es i q) x := by
    intro q hq
    rw [← encAt_eq_sum, ← sub_eq_zero]
    exact h3 q (mem_range.mp hq)
  rw [vNext, hc, show (∑ q ∈ range (CKind.lv κ i).t,
      K.smulF (eqBits (kcAt es i) 9 q) (foldAtN κ L es i (qPos κ es i q))) =
      ∑ q ∈ range (CKind.lv κ i).t, K.smulF (eqBits (kcAt es i) 9 q)
        (∑ x ∈ range (2 ^ mLog κ i), nextMsg κ L es i x * gW κ i (qPos κ es i q) x) from
      sum_congr rfl fun q hq' => by rw [hq q hq']]
  have h1 : ∑ x ∈ range (2 ^ mLog κ i), Wf x * foldMsg κ L es i x =
      ∑ x ∈ range (2 ^ mLog κ i), Wf x * nextMsg κ L es i x :=
    sum_congr rfl fun x hx => by rw [hC x (mem_range.mp hx)]
  have h2 : ∑ q ∈ range (CKind.lv κ i).t, K.smulF (eqBits (kcAt es i) 9 q)
        (∑ x ∈ range (2 ^ mLog κ i), nextMsg κ L es i x * gW κ i (qPos κ es i q) x) =
      ∑ x ∈ range (2 ^ mLog κ i), (∑ q ∈ range (CKind.lv κ i).t,
        K.smulF (eqBits (kcAt es i) 9 q) (gW κ i (qPos κ es i q) x)) * nextMsg κ L es i x := by
    simp only [K.smulF_eq_mul, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun q _ => by
      rw [mul_comm (nextMsg κ L es i x), mul_assoc]
  rw [h1, h2, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by rw [wNext, add_mul]

/-- Levels `1 … 4` have 16 rows and `k_{i+1} = kᵢ / 8`. -/
theorem lv_next (κ : CKind) {i : ℕ} (hi : i + 1 < 5) :
    (CKind.lv κ (i + 1)).rows = 16 ∧ (CKind.lv κ (i + 1)).ell = 4 ∧ mLog κ (i + 1) + 3 = mLog κ i := by
  have : i < 4 := by omega
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The split table's inner product with `f⁽ⁱ⁺¹⁾`** is the folded message's: level `i + 1`'s
claim `⟨wSplit W, f⁽ⁱ⁺¹⁾⟩` over its `4 + mLog` variables equals `⟨W, nextMsg⟩` over level `i`'s
folded message (`i < 4`). -/
theorem wSplit_sum {κ : CKind} {L es : Log} {i : ℕ} (hi : i + 1 < 5) (W : ℕ → K) :
    ∑ y ∈ range (2 ^ ((CKind.lv κ (i + 1)).ell + mLog κ (i + 1))), wSplit W y * fTab κ L es (i + 1) y =
      ∑ x ∈ range (2 ^ mLog κ i), W x * nextMsg κ L es i x := by
  obtain ⟨hr, he, hm⟩ := lv_next κ hi
  have h2 : 2 ^ ((CKind.lv κ (i + 1)).ell + mLog κ (i + 1)) = 2 * 2 ^ mLog κ i := by
    rw [he, ← hm]; ring
  rw [h2, sum_range_two_mul]
  refine sum_congr rfl fun x _ => ?_
  have hnl : i + 1 < nLevels := hi
  simp only [wSplit, fTab, nextMsg, hnl, ite_true, hr]
  rw [show 2 * x / 2 = x by omega, show (2 * x + 1) / 2 = x by omega,
    show 2 * x % 2 = 0 by omega, show (2 * x + 1) % 2 = 1 by omega,
    show 2 * x % 16 = 2 * (x % 8) by omega, show (2 * x + 1) % 16 = 2 * (x % 8) + 1 by omega,
    show 2 * x / 16 = x / 8 by omega, show (2 * x + 1) / 16 = x / 8 by omega]
  simp only [ite_true, one_ne_zero, ite_false, mul_one, mul_add]
  ring

/-! ## Part G: hidden disagreement (§10 changes 14; A.10 P1.i)

`hideL i` (`Hide_i`): a position outside the joint agreement set whose folded difference vanishes
at P1.i's challenges. **`consSet_eq_jointAgree`**: with `¬ far_i`, `truthC i` and `¬ Hide_i`, the
consistency set `A_c` is `jointAgree`, the set `final` hands the extractor. **`hide_round_le`**:
per round at most `|P|` challenge values make one of `|P| ≤ eᵢ` (`card_not_jointAgree`) nonzero
difference tables vanish (`zerocheck_bad_le` over K); `hide_fits`: the count stays inside P1's
single-squeeze budget. -/

/-- **`Hide_i`** (§10 changes 14, A.10 P1.i): a position where level `i`'s word disagrees with the
decoded codeword rows but whose folded difference `Σ_r eq(sᵢ, r)·(W⁽ⁱ⁾[r][j] − V[r][j])`
vanishes at P1.i's fold challenges. -/
def hideL (κ : CKind) (L es : Log) (i : ℕ) : Prop :=
  ∃ j ∉ jointAgree (wordK κ L es i) (decodeL κ L es i),
    ∑ r : Fin (CKind.lv κ i).rows, eqBits (sAt es i) (CKind.lv κ i).ell r *
      (wordK κ L es i r j - decodeL κ L es i r j) = 0

/-- **The consistency set is the joint agreement set** (§10 changes 14): on a close word whose
next message is the fold (`truthC`) and with no hidden disagreement, `A_c = jointAgree`. This is
what `final` hands the extractor. -/
theorem consSet_eq_jointAgree {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5)
    (hfar : ¬ farL κ L es i) (hC : truthC κ L es i) (hH : ¬ hideL κ L es i) :
    consSet κ L es i = jointAgree (wordK κ L es i) (decodeL κ L es i) := by
  classical
  obtain ⟨-, hN, hm, hk, hn⟩ := lv_params κ hi
  have hnN : 2 ^ (CKind.lv κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, -⟩ := decodeL_spec hfar
  choose c hc using fun r => exists_msg hi (hV r)
  set s : Fin (CKind.lv κ i).rows → K := fun r => eqBits (sAt es i) (CKind.lv κ i).ell r
  -- the next message's codeword is the fold of the decoded rows
  have hnx : ∀ j : Fin (2 ^ (CKind.lv κ i).logN), encAt κ i (nextMsg κ L es i) j =
      ∑ r, s r * decodeL κ L es i r j := by
    intro j
    have hm' : (fun x : Fin (2 ^ mLog κ i) => nextMsg κ L es i x) = ∑ r, s r • c r := by
      funext x
      rw [hC x x.2, foldMsg]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, s]
      exact sum_congr rfl fun r _ => by rw [msgOf_eq hi (hc r) x]
    rw [encAt, encF_eq hm (lt_of_lt_of_le j.2 hnN), ← enc_eq_encN (n := 2 ^ (CKind.lv κ i).logN), hm']
    change (encL (M := K) D _ _) (∑ r, s r • c r) j = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun r _ => by rw [show (encL (M := K) D _ _) (c r) = _ from hc r]
  ext j
  simp only [consSet, mem_filter, mem_univ, true_and, foldAt, hnx]
  constructor
  · intro h
    by_contra hj
    refine hH ⟨j, hj, ?_⟩
    simp only [mul_sub, sum_sub_distrib, sub_eq_zero]
    exact h
  · intro hj
    rw [mem_jointAgree] at hj
    exact sum_congr rfl fun r _ => by rw [hj r]

/-- Outside the joint agreement set of a close word there are at most `eᵢ` positions. -/
theorem card_not_jointAgree {κ : CKind} {L es : Log} {i : ℕ} (hfar : ¬ farL κ L es i) :
    (univ.filter fun j => j ∉ jointAgree (wordK κ L es i) (decodeL κ L es i)).card ≤ lvE κ i := by
  have hJ := (decodeL_spec hfar).2
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 ^ (CKind.lv κ i).logN))))
    fun j => j ∈ jointAgree (wordK κ L es i) (decodeL κ L es i)
  rw [card_univ, Fintype.card_fin, filter_mem_eq_inter, univ_inter] at h
  omega

/-- The hiding count fits P1's single-squeeze budget: `2 + eᵢ ≤ 2^66` at every level (A.10's
`N ≤ 2^66` for P1.i already holds the cancellation term). -/
theorem hide_fits (κ : CKind) {i : ℕ} (hi : i < 5) : 2 + lvE κ i ≤ 2 ^ 20 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- Control: with no disagreeing position there is nothing to hide. -/
theorem not_hideL_of_univ {κ : CKind} {L es : Log} {i : ℕ}
    (h : jointAgree (wordK κ L es i) (decodeL κ L es i) = univ) : ¬ hideL κ L es i := by
  rintro ⟨j, hj, -⟩; rw [h] at hj; exact hj (mem_univ j)

end FR.Snd.T4

end G6_FRSoundness4TailTruths

section G6_FRSoundness4TailHide

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessHide` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The Hide doom and the potential `muT` at `seq4` (T4)

The 3.x declarations of `FRSoundnessHide` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessHide` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the positions -/

/-- P1.i's first Fiat–Shamir position (phase `26 + 5i`). -/
def p1Start (i : ℕ) : ℕ := phStart4 (26 + 5 * i)

theorem lvl_ell (κ : CKind) {i : ℕ} (hi : i < 5) : (CKind.lv κ i).ell = hEll i := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> rfl

/-- Checked: P1's starts and rounds (`[332, 375, 402, 426, 448]`, `[6, 4, 4, 4, 4]`), each level's
cap absorbed before its P1, and the P1 phases disjoint. -/
theorem p1_check : (List.range 5).all (fun i => decide (capPos i < p1Start i) &&
    (List.range 5).all fun i' => i == i' || decide (p1Start i + 2 * hEll i ≤ p1Start i') ||
      decide (p1Start i' + 2 * hEll i' ≤ p1Start i)) = true := by
  unfold capPos p1Start phStart4 hEll; rw [fsStarts4_eq]; decide

theorem capPos_lt {i : ℕ} (hi : i < 5) : capPos i < p1Start i := by
  have := p1_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at this
  exact (this i hi).1

theorem p1_disj {i i' : ℕ} (hi : i < 5) (hi' : i' < 5) (h : i ≠ i') :
    p1Start i + 2 * hEll i ≤ p1Start i' ∨ p1Start i' + 2 * hEll i' ≤ p1Start i := by
  have := p1_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  have := (this i hi).2 i' hi'
  omega

/-- Checked: every level's cap absorb (`len` bytes, `len ≥ 32·2^cap` for every kind, inside
`queryCap`), with `cap ≤ log₂ n`. -/
theorem cap_check : (List.range 5).all (fun i => match fsItems4[capPos i]? with
    | some (.absorb len) => [CKind.seg .L30, .seg .L31, .seg .L32, .node .N2, .node .N4, .node .N8].all (fun κ =>
        decide (32 * 2 ^ (CKind.lv κ i).cap ≤ len) && decide ((CKind.lv κ i).cap ≤ (CKind.lv κ i).logN)) &&
        decide (40 + len ≤ queryCap)
    | _ => false) = true := by
  unfold capPos phStart4; rw [fsStarts4_eq]; decide +kernel

/-- Checked once for all five levels: P1.i's odd offsets are squeezes, and no multi-squeeze
phase meets P1.i. -/
theorem p1_sq_check : (List.range 5).all (fun i => decide (1 ≤ p1Start i) && decide (0 < hEll i) &&
    (List.range (hEll i)).all (fun j => fsItems4[p1Start i + 2 * j + 1]? == some .squeeze) &&
    fsRanges4.all fun x => decide (x.1 + x.2 < p1Start i ∨ p1Start i + 2 * hEll i ≤ x.1 + 1)) =
      true := by
  rw [fsRanges4_eq]; decide +kernel

/-- **P1.i is a rounds phase** of `ℓᵢ` real rounds (checked squeezes, no multi-squeeze phase). -/
theorem p1_phase {i : ℕ} (hi : i < 5) : RoundsPhase (p1Start i) (hEll i) fun _ => hEll i := by
  have h := p1_sq_check
  rw [List.all_eq_true] at h
  have h' := h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact roundsPhase_of h'.1.1.1 h'.1.1.2 (fun _ => le_rfl) h'.1.2 h'.2

/-! ## Part B: the Hide doom -/

/-- The P1.i rounds answered by `es`: `min ℓᵢ ⌊(|es| − p1Start i)/2⌋`. -/
def hRnd (es : Log) (i : ℕ) : ℕ := min (hEll i) ((es.length - p1Start i) / 2)

/-- P1.i's first `l` fold challenges `sᵢ` (`sAt`). -/
def sList (es : Log) (i l : ℕ) : List K := (List.range l).map (sAt es i)

/-- Column `j`'s difference table between level `i`'s word and its decoded rows (over the
`2^ℓᵢ` rows). -/
noncomputable def hDiff (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    Array K :=
  Array.ofFn (n := (CKind.lv κ i).rows) fun r => wordK κ L es i r j - decodeL κ L es i r j

/-- Level `i`'s cap entry passes its absorb item's check (on a chain this is `Matches`; on a formal
extension past the chain it fails, `fsCheck_ext_ge`). -/
def capOK (es : Log) (i : ℕ) : Prop :=
  ∃ len, fsItems4[capPos i]? = some (.absorb len) ∧
    fsCheck (.absorb len) (entAt es (capPos i)).1 = true

/-- **No hidden disagreement so far at level `i`** (§10 changes 14–15): on a close word, every
column outside the joint agreement set keeps a nonzero difference table after binding the P1.i
challenges answered so far (`mlDoom` over K). With all `ℓᵢ` bound this is `¬ Hide_i`
(`noHide_full`); before P1.i it holds for every word (`noHide_zero`). -/
def noHide (κ : CKind) (L es : Log) (i : ℕ) : Prop :=
  ¬ farL κ L es i → ∀ j ∉ jointAgree (wordK κ L es i) (decodeL κ L es i),
    mlDoom (CKind.lv κ i).ell (hDiff κ L es i j) (sList es i (hRnd es i))

/-- **The Hide doom** (§10 changes 15): no level has hidden a disagreement so far. Its potential
`μ_Hide` escapes exactly when some P1.i challenge hides one. -/
def DH (L es : Log) : Prop := ∀ i < 5, noHide (kindOfC es) L es i

theorem hDiff_size (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    (hDiff κ L es i j).size = 2 ^ (CKind.lv κ i).ell := Array.size_ofFn

theorem tbl_hDiff (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    tbl (CKind.lv κ i).ell (hDiff κ L es i j) = fun r => wordK κ L es i r j - decodeL κ L es i r j := by
  funext r
  simp [tbl, hDiff, Array.getD_eq_getD_getElem?, Level.rows]

/-- Before P1.i (no round answered), nothing is hidden: a column outside the joint agreement set
has a nonzero difference table. -/
theorem noHide_zero {κ : CKind} {L es : Log} {i : ℕ} (h : hRnd es i = 0) : noHide κ L es i := by
  intro _ j hj
  have hnil : ∀ n (t : Array K), tbl n t ≠ 0 → mlDoom n t [] := fun n t h => by cases n <;> exact h
  rw [h, sList, List.range_zero, List.map_nil]
  refine hnil _ _ ?_
  rw [tbl_hDiff]
  intro hz
  refine hj (mem_jointAgree.mpr fun r => ?_)
  have := congrFun hz r
  exact sub_eq_zero.mp this

/-- Every chain short of P1.0's first answer satisfies the Hide doom. -/
theorem DH_short {L es : Log} (h : es.length ≤ p1Start 0 + 1) : DH L es := by
  intro i hi
  refine noHide_zero ?_
  have := p1_phase hi
  have hv : ∀ j, j < 5 → p1Start j = [332, 375, 402, 426, 448].getD j 0 := by
    intro j hj; unfold p1Start phStart4; rw [fsStarts4_eq]; interval_cases j <;> rfl
  have h0 := hv 0 (by norm_num)
  have hi' : p1Start 0 ≤ p1Start i := by
    rw [hv i hi, h0]; interval_cases i <;> decide
  simp only [hRnd]
  omega

/-- The rounds answered change only at a P1.i round's squeeze `p1Start i + 2l + 1`, `l < ℓᵢ`. -/
theorem hRnd_append (es : Log) (x : ByteArray × Digest) {i : ℕ}
    (h : ∀ l < hEll i, es.length ≠ p1Start i + 2 * l + 1) : hRnd (es ++ [x]) i = hRnd es i := by
  by_contra hne
  refine h ((es.length - p1Start i) / 2) ?_ ?_ <;>
    simp only [hRnd, List.length_append, List.length_singleton] at hne <;> omega

theorem hRnd_ext1 (es : Log) (a : Digest) {i l : ℕ} (hl : l < hEll i)
    (h : es.length = p1Start i + 2 * l + 1) : hRnd es i = l ∧ hRnd (ext1 es a) i = l + 1 := by
  simp only [hRnd, ext1, List.length_append, List.length_singleton]
  omega

theorem sAt_congr {es es' : Log} {i l : ℕ} (h : Agree es es' (p1Start i + 2 * l + 2)) :
    sAt es i l = sAt es' i l := by
  simp only [sAt, kAt, ansAt]
  rw [h _ (by unfold p1Start; omega)]

theorem sList_congr {es es' : Log} {i l : ℕ} (h : Agree es es' (p1Start i + 2 * l)) :
    sList es i l = sList es' i l := by
  refine List.map_congr_left fun l' hl' => sAt_congr (h.mono ?_)
  simp only [List.mem_range] at hl'
  omega

theorem sList_ext1 (es : Log) (a : Digest) {i l : ℕ} (h : es.length = p1Start i + 2 * l + 1) :
    sList (ext1 es a) i (l + 1) = sList es i l ++ [chK a] := by
  rw [sList, List.range_succ, List.map_append, List.map_singleton, ← sList,
    sList_congr (l := l) (show Agree (ext1 es a) es _ from agree_append es _ (by omega))]
  have : sAt (ext1 es a) i l = chK a := by
    simp only [sAt, kAt, ansAt]
    rw [show phStart4 (26 + 5 * i) + 2 * l + 1 = es.length by unfold p1Start at h; omega,
      entAt_ext1]
  rw [this]

/-- `decodeL` reads the word only. -/
theorem decodeL_congr {κ : CKind} {L L' es es' : Log} {i : ℕ}
    (h : wordK κ L es i = wordK κ L' es' i) : decodeL κ L es i = decodeL κ L' es' i := by
  have key : ∀ (U U' : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K) (hU : U = U')
      (p : ∃ V : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K, (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (jointAgree U V).card)
      (p' : ∃ V : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K, (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (jointAgree U' V).card),
      Classical.choose p = Classical.choose p' := by
    intro U U' hU p p'; subst hU; rfl
  have hf : farL κ L es i ↔ farL κ L' es' i := by simp only [farL, h]
  unfold decodeL
  by_cases hn : farL κ L es i
  · simp only [hn, hf.mp hn, not_true_eq_false, dite_false]
  · simp only [hn, (not_congr hf).mp hn, not_false_eq_true, dite_true]
    exact key _ _ h _ _

/-- Appending where the rounds answered do not change keeps level `i`'s Hide state. -/
theorem noHide_append {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) (x : ByteArray × Digest)
    (hr : hRnd (es ++ [x]) i = hRnd es i) : noHide κ L (es ++ [x]) i ↔ noHide κ L es i := by
  by_cases h0 : hRnd es i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero (hr.trans h0)⟩
  have hlen : p1Start i + 2 * hRnd es i ≤ es.length := by unfold hRnd at h0 ⊢; omega
  have hcap := capPos_lt hi
  have hA : Agree (es ++ [x]) es es.length := agree_append es _ le_rfl
  have hw : wordK κ L (es ++ [x]) i = wordK κ L es i := by
    funext r p; simp only [wordK, wordOf, colOf_congr κ L i p (hA.mono (by omega))]
  have hd := decodeL_congr hw
  have hs : sList (es ++ [x]) i (hRnd es i) = sList es i (hRnd es i) := sList_congr (hA.mono hlen)
  unfold noHide hDiff farL
  rw [hr, hs, hw, hd]

theorem kindOf_ext1 (es : Log) (a : Digest) (h : 0 < es.length) : kindOfC (ext1 es a) = kindOfC es :=
  kindOf_append _ h

/-- **Off P1's round squeezes, appending keeps the Hide doom.** -/
theorem DH_append_iff {L es : Log} (x : ByteArray × Digest)
    (h : ∀ i < 5, ∀ l < hEll i, es.length ≠ p1Start i + 2 * l + 1) :
    DH L (es ++ [x]) ↔ DH L es := by
  rcases Nat.eq_zero_or_pos es.length with h0 | h0
  · exact ⟨fun _ => DH_short (by omega),
      fun _ => DH_short (by rw [List.length_append, List.length_singleton]; omega)⟩
  rw [DH, DH, kindOf_append x h0]
  exact forall₂_congr fun i hi => noHide_append hi x (hRnd_append es x (h i hi))

/-! ## Part C: the word read off the charging log (`hstab`) -/

/-- **The level words of a chain's formal extensions read the same off the charging log**
(§10 changes 10; A.10's `hstab` reads): on a non-bad log, when the cap entry of an extension of a
prefix of chain `n` passes its absorb check, it is a real chain entry (`fsCheck_ext_ge`), an
entry of `L.take n` or the chain's last entry `L[n]`; its cap digests are carried within the
windows (`cap_carried`), so every column under them reads the same (`colL_take`,
`colL_take_own`). -/
theorem colOf_stab {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) (k : ℕ)
    (as : List Digest) {i : ℕ} (hi : i < 5) (κ : CKind)
    (hc : capOK (ext ((entriesOf L (pathOf L n)).take k) as) i) (p : Fin (2 ^ (CKind.lv κ i).logN)) :
    colOf κ (L.take n) (ext ((entriesOf L (pathOf L n)).take k) as) i p =
      colOf κ L (ext ((entriesOf L (pathOf L n)).take k) as) i p := by
  obtain ⟨len, hit, hchk⟩ := hc
  set es₀ := (entriesOf L (pathOf L n)).take k with hes₀
  have hlt : capPos i < es₀.length := by
    by_contra h
    rw [fsCheck_ext_ge _ _ (not_lt.mp h)] at hchk
    cases hchk
  have hlk : capPos i < k := by rw [hes₀, List.length_take] at hlt; omega
  have hlc : capPos i < (entriesOf L (pathOf L n)).length := by
    rw [hes₀, List.length_take] at hlt; omega
  have hpl : capPos i < (pathOf L n).length := by rwa [length_entriesOf] at hlc
  set idx := (pathOf L n)[capPos i] with hidx
  have hidxn : idx ≤ n := mem_pathOf_le (List.getElem_mem hpl)
  have hidxL : idx < L.length := lt_of_le_of_lt hidxn hci.1
  have hent : entAt (ext es₀ as) (capPos i) = L[idx] := by
    rw [entAt_ext_lt _ _ hlt, hes₀, entAt_take hlk, entAt, List.getD_eq_getElem _ _ hlc,
      entriesOf_getElem, getElem!_pos L _ hidxL]
  -- the cap's sizes (checked)
  have hcc := cap_check
  simp only [List.all_eq_true, List.mem_range] at hcc
  have hci' := hcc i hi
  rw [hit] at hci'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hci'
  have hk32 := hci'.1 κ (by rcases κ with (_|_|_) | (_|_|_) <;> simp)
  have hq := hci'.2
  rw [hent] at hchk
  have hsz : (L[idx]).1.size = 40 + len := by
    simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at hchk; exact hchk.2
  have hcp : p.val / 2 ^ (CKind.lv κ i).sib < 2 ^ (CKind.lv κ i).cap := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Level.sib,
      Nat.add_sub_cancel' hk32.2]
    exact p.isLt
  have hd : capDig (ext es₀ as) i (p.val / 2 ^ (CKind.lv κ i).sib) ∈ (frEncW i).carried (L[idx]).1 := by
    rw [capDig, msgAt, hent]
    refine cap_carried hchk (by omega) ?_ i
    calc 32 * (p.val / 2 ^ (CKind.lv κ i).sib + 1) ≤ 32 * 2 ^ (CKind.lv κ i).cap := by omega
      _ ≤ len := hk32.1
  unfold colOf
  rcases Nat.lt_or_eq_of_le hidxn with h | h
  · refine colL_take hb i n ⟨L[idx], ?_, hd⟩ _ _
    rw [List.mem_iff_getElem]
    exact ⟨idx, by simp; omega, by simp⟩
  · have hd' : capDig (ext es₀ as) i (p.val / 2 ^ (CKind.lv κ i).sib) ∈
        (frEncW i).carried (L[n]'hci.1).1 := by simpa [h] using hd
    exact colL_take_own hb hci.1 hd' _ _

theorem wordK_stab {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) (k : ℕ)
    (as : List Digest) {i : ℕ} (hi : i < 5) (κ : CKind)
    (hc : capOK (ext ((entriesOf L (pathOf L n)).take k) as) i) :
    wordK κ (L.take n) (ext ((entriesOf L (pathOf L n)).take k) as) i =
      wordK κ L (ext ((entriesOf L (pathOf L n)).take k) as) i := by
  funext r p
  simp only [wordK, wordOf, colOf_stab hb hci k as hi κ hc p]

/-- On a chain past level `i`'s cap absorb, the cap entry is real. -/
theorem capOK_of_matches {es : Log} (hm : G.Matches es) {i : ℕ} (hi : i < 5)
    (hl : capPos i < es.length) : capOK es i := by
  have hcc := cap_check
  simp only [List.all_eq_true, List.mem_range] at hcc
  have h := hcc i hi
  have h1 : 1 ≤ capPos i := by
    unfold capPos phStart4; rw [fsStarts4_eq]; interval_cases i <;> decide
  obtain ⟨_, hl', H⟩ := hm
  dsimp only [fs_eq4] at hl' H  -- T4: `G.Matches` reads `FsSeq.fs`, which is `fsItems4`
  obtain ⟨-, hf⟩ := H (capPos i - 1) (by omega)
  cases hh : fsItems4[capPos i]? with
  | none => rw [hh] at h; simp at h
  | some it =>
    cases it with
    | absorb len =>
      refine ⟨len, hh, ?_⟩
      have hlt : capPos i < fsItems4.length := by omega
      have he : fsItems4[capPos i] = .absorb len :=
        Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hh)
      have hidx : capPos i - 1 + 1 = capPos i := by omega
      simp only [hidx, he] at hf
      rw [entAt, List.getD_eq_getElem _ _ hl]
      exact hf
    | _ => rw [hh] at h; simp at h

/-- **On `hloc_of`'s extensions a cap entry inside the extension is real** (the ruling on S-G1g
§8 Q1: `hstab`'s scope is `StabExt`): the formal entries sit on squeeze positions
(`fsRnd4_ok`), and the cap position is an absorb (`cap_check`), so it lies in the chain's prefix,
where `Matches` gives the check (`capOK_of_matches`). -/
theorem capOK_of_stabExt {es X : Log} (hm : G.Matches es) (hX : StabExt fsRnd4 es X) {i : ℕ}
    (hi : i < 5) (hl : capPos i < X.length) : capOK X i := by
  obtain ⟨s0, r, as, hr, hs, has, rfl⟩ := hX
  have htk : (es.take (s0 + 1)).length = s0 + 1 := by simp; omega
  have hlt : capPos i < s0 + 1 := by
    by_contra hge
    obtain ⟨-, hpr, hspec⟩ := fsRnd4_ok _ _ _ hr
    rw [length_ext, htk] at hl
    have hsq := (hspec (capPos i) (by omega) (by omega)).1
    dsimp only [fs_eq4] at hsq  -- T4
    have hcc := cap_check
    simp only [List.all_eq_true, List.mem_range] at hcc
    have h := hcc i hi
    rw [hsq] at h
    simp at h
  obtain ⟨len, hit, hchk⟩ := capOK_of_matches hm hi (by omega)
  refine ⟨len, hit, ?_⟩
  rw [entAt_ext_lt _ _ (by rw [htk]; exact hlt), entAt_take hlt]
  exact hchk

/-- **The level words read the same off the charging log on `hloc_of`'s extensions**, once the
extension reaches the cap (the reusable form for every word-reading doom). -/
theorem wordK_stabX {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L n)) X) {i : ℕ} (hi : i < 5) (κ : CKind)
    (hl : capPos i < X.length) : wordK κ (L.take n) X i = wordK κ L X i := by
  have hc := capOK_of_stabExt hci.2 hX hi hl
  obtain ⟨s0, r, as, -, -, -, rfl⟩ := hX
  exact wordK_stab hb hci (s0 + 1) as hi κ hc

/-- **Level `i`'s Hide state reads the same off the charging log** on `hloc_of`'s extensions:
before P1.i it holds on both sides (`noHide_zero`); after, the cap is real (`wordK_stabX`). -/
theorem noHide_stab {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L n)) X) {i : ℕ} (hi : i < 5) (κ : CKind) :
    noHide κ (L.take n) X i ↔ noHide κ L X i := by
  by_cases h0 : hRnd X i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero h0⟩
  have hl : capPos i < X.length := by
    have := capPos_lt hi; unfold hRnd at h0; omega
  have hw := wordK_stabX hb hci hX hi κ hl
  have hd := decodeL_congr hw
  unfold noHide hDiff farL
  rw [hw, hd]

/-! ## Part D: the Hide potential's step law at `ε_H` -/

/-- Every level's decoding radius fits `2^18` (level 0 of `L32`: `e₀ = 2^18`). -/
theorem lvE_le (κ : CKind) {i : ℕ} (hi : i < 5) : lvE κ i ≤ 2 ^ 18 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

theorem not_p1Sq_of_absorb {es : Log} {len : ℕ} (hit : fsItems4[es.length]? = some (.absorb len)) :
    ∀ i < 5, ∀ l < hEll i, es.length ≠ p1Start i + 2 * l + 1 := by
  intro i hi l hl he
  have := (p1_phase hi).hsq l hl
  rw [← he, hit] at this
  cases this

theorem not_p1Sq_of_rnd {p s0 r : ℕ} (h : fsRnd4 p = some (s0, r)) :
    ∀ i < 5, ∀ l < hEll i, p ≠ p1Start i + 2 * l + 1 := by
  intro i hi l hl he
  rcases (p1_phase hi).hph p s0 r h with h' | h' <;> omega

open Classical in
/-- **The Hide row** (A.10 P1.i, §10 changes 14): at P1.i's round-`l` squeeze, the other levels
keep their state (`p1_disj`), and an answer hides a disagreement only if its challenge `chK a`
makes one of the `≤ eᵢ` nonzero bound difference tables vanish (`mlDoom_step` over K,
`card_not_jointAgree`): at most `eᵢ ≤ 2^18` answers (`card_chK_fiber`). -/
theorem hide_single (L es : Log) {i₀ l : ℕ} (hi₀ : i₀ < 5) (hl : l < hEll i₀)
    (hp : es.length = p1Start i₀ + 2 * l + 1) :
    (univ.filter fun a => DH L es ∧ ¬ DH L (ext1 es a)).card ≤ 2 ^ 18 := by
  have h0 : 0 < es.length := by omega
  set κ := kindOfC es with hκ
  have hsub : (univ.filter fun a => DH L es ∧ ¬ DH L (ext1 es a)) ⊆
      univ.filter fun a => noHide κ L es i₀ ∧ ¬ noHide κ L (ext1 es a) i₀ := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    obtain ⟨hd, hnd⟩ := ha
    refine ⟨hd i₀ hi₀, fun hn => hnd fun i hi => ?_⟩
    rw [kindOf_ext1 es a h0]
    by_cases hii : i = i₀
    · subst hii; exact hn
    · have hr : hRnd (ext1 es a) i = hRnd es i := hRnd_append es _ fun l' hl' he => by
        rcases p1_disj hi hi₀ hii with h | h <;> omega
      exact (noHide_append hi _ hr).mpr (hd i hi)
  refine (card_le_card hsub).trans ?_
  have hcap := capPos_lt hi₀
  have hA : ∀ a, Agree (ext1 es a) es es.length := fun a => agree_append es _ le_rfl
  have hw : ∀ a, wordK κ L (ext1 es a) i₀ = wordK κ L es i₀ := fun a => by
    funext r p; simp only [wordK, wordOf, colOf_congr κ L i₀ p ((hA a).mono (by omega))]
  have hkey : ∀ a, noHide κ L (ext1 es a) i₀ ↔ (¬ farL κ L es i₀ →
      ∀ j ∉ jointAgree (wordK κ L es i₀) (decodeL κ L es i₀),
        mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [chK a])) := fun a => by
    unfold noHide hDiff farL
    rw [(hRnd_ext1 es a hl hp).2, sList_ext1 es a hp, hw a, decodeL_congr (hw a)]
  have hR : hRnd es i₀ = l := (hRnd_ext1 es default hl hp).1
  by_cases hf1 : farL κ L es i₀
  · rw [Finset.filter_false_of_mem fun a _ ha => ha.2 ((hkey a).mpr fun h2 => absurd hf1 h2)]
    simp
  by_cases hn : noHide κ L es i₀
  swap
  · rw [Finset.filter_false_of_mem fun a _ ha => hn ha.1]; simp
  set P := univ.filter fun j => j ∉ jointAgree (wordK κ L es i₀) (decodeL κ L es i₀)
  set S := univ.filter fun c : K => ∃ j ∈ P,
    ¬ mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [c])
  have h1 : (univ.filter fun a => noHide κ L es i₀ ∧ ¬ noHide κ L (ext1 es a) i₀) ⊆
      univ.filter fun a : Digest => chK a ∈ S := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [hkey a] at ha
    by_contra hS
    refine ha.2 fun _ j hj => ?_
    by_contra hd
    exact hS (by simp only [S, P, mem_filter, mem_univ, true_and]; exact ⟨j, hj, hd⟩)
  have h2 : S.card ≤ P.card := by
    calc S.card ≤ (P.biUnion fun j => univ.filter fun c : K =>
          ¬ mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [c])).card :=
          card_le_card fun c hc => by
            simp only [S, mem_filter, mem_univ, true_and] at hc
            obtain ⟨j, hj, h⟩ := hc
            exact mem_biUnion.mpr ⟨j, hj, by simp [h]⟩
      _ ≤ ∑ j ∈ P, (univ.filter fun c : K =>
          ¬ mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [c])).card :=
          card_biUnion_le
      _ ≤ ∑ _j ∈ P, 1 := sum_le_sum fun j hj => by
          have hd := hn hf1 j (by simpa [P] using hj)
          rw [hR] at hd
          exact (mlDoom_step (hDiff_size κ L es i₀ j) _ hd).trans (by split <;> omega)
      _ = P.card := by simp
  calc _ ≤ (univ.filter fun a : Digest => chK a ∈ S).card := card_le_card h1
    _ = S.card := card_chK_fiber S
    _ ≤ P.card := h2
    _ ≤ lvE κ i₀ := card_not_jointAgree hf1
    _ ≤ 2 ^ 18 := lvE_le κ hi₀

open Classical in
/-- **The Hide doom's five obligations** at `δ = 2^-238`, `N = 2^18`: off P1's round squeezes the
doom does not move (`DH_append_iff`), so absorbs, middle squeezes and the multi-squeeze phases
cost nothing; P1's squeezes are `hide_single`; the reads are stable (`noHide_stab`). -/
theorem hide_obl : StepObl DH fsRnd4 ((2 : ℝ≥0)⁻¹ ^ 238) (2 ^ 18) where
  habs L es x len _ hit hd := (DH_append_iff x (not_p1Sq_of_absorb hit)).mpr hd
  hmid L es x s0 r _ hr _ := DH_append_iff x (not_p1Sq_of_rnd hr)
  hsingle L es _ _ _ := by
    by_cases h : ∃ i < 5, ∃ l < hEll i, es.length = p1Start i + 2 * l + 1
    · obtain ⟨i, hi, l, hl, hp⟩ := h
      exact hide_single L es hi hl hp
    · push Not at h
      rw [Finset.filter_false_of_mem fun a _ ha => ha.2 ((DH_append_iff _ h).mpr ha.1)]
      simp
  hround L es₀ s0 r _ hl hr := by
    rw [condCount_eq_zero]
    · exact zero_le
    intro as has ⟨_, hd, hnd⟩
    obtain ⟨-, hpr, hspec⟩ := fsRnd4_ok _ _ _ hr
    have hlen := length_ext as es₀
    have hne : ext es₀ as ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have hdl : (ext es₀ as).dropLast.length = s0 + r := by
      rw [List.length_dropLast, hlen]; omega
    have hq := not_p1Sq_of_rnd (hspec (s0 + r) (by omega) le_rfl).2
    rw [← hdl] at hq
    have := (DH_append_iff ((ext es₀ as).getLast hne) hq).mpr hd
    rw [List.dropLast_append_getLast hne] at this
    exact hnd this
  hstab L n hb hci X hX := forall₂_congr fun i hi => noHide_stab hb hci hX hi _

open Classical in
/-- **`μ_Hide`'s step law** (§10 changes 15): the library's `KState.step` law with error
`ε_H = 2^-142 + 2^-238` for `muG DH (pRoundG DH fsRnd4)`. -/
theorem hide_step (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : G.muG DH (pRoundG DH fsRnd4) L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, G.muG DH (pRoundG DH fsRnd4) (L ++ [(q, a)]) ≤
      (G.muG DH (pRoundG DH fsRnd4) L + epsH) * 2 ^ 256 :=
  (G.muG_step_of fsRnd4_ok fsRnd4_zero _ _ hide_N_le hide_obl.habs hide_obl.hmid hide_obl.hsingle
    hide_obl.hround hide_obl.hstab hl hμ hq).trans (by gcongr; exact err_le_epsH)

/-! ## Part E: at P1.i's end, `noHide` is `¬ Hide_i` -/

theorem sList_length (es : Log) (i l : ℕ) : (sList es i l).length = l := by simp [sList]

/-- With all `ℓ` challenges bound, the table's value is the `eq(sᵢ, ·)`-weighted row sum. -/
theorem bindL_sList {ℓ : ℕ} {t : Array K} (ht : t.size = 2 ^ ℓ) (es : Log) (i : ℕ) :
    tbl 0 (bindL t (sList es i ℓ)) 0 = ∑ u : Fin (2 ^ ℓ), eqBits (sAt es i) ℓ u * tbl ℓ t u := by
  rw [bindL_mle _ _ (by rw [ht, sList_length]), ← mleEval_eq,
    mleEval_eq' t _ (sList_length es i ℓ), mle]
  refine sum_congr rfl fun u _ => ?_
  have : (fun v : Fin ℓ => sAt es i (v : ℕ)) = ptOf ℓ (sList es i ℓ) := by
    funext v
    simp only [ptOf, sList, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range v.isLt, Option.map_some, Option.getD_some]
  rw [eqBits_eq_eq, this]

/-- **`noHide` at P1.i's end is `¬ Hide_i`** (A.10 P1.i): with every round answered and a close
word, no disagreeing column's fold vanishes. -/
theorem noHide_full {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hR : hRnd es i = hEll i)
    (hfar : ¬ farL κ L es i) (hn : noHide κ L es i) : ¬ hideL κ L es i := by
  rintro ⟨j, hj, hz⟩
  have hd := hn hfar j hj
  rw [hR, ← lvl_ell κ hi, mlDoom, List.take_of_length_le (by rw [sList_length]),
    sList_length, Nat.sub_self] at hd
  refine hd (funext fun u => ?_)
  obtain ⟨u, hu⟩ := u
  obtain rfl : u = 0 := by simp at hu; omega
  rw [Pi.zero_apply, show (⟨0, hu⟩ : Fin (2 ^ 0)) = 0 from rfl,
    bindL_sList (hDiff_size κ L es i j), tbl_hDiff]
  exact hz

/-- **What `final` gets from `μ_Hide`** (§10 changes 14–15, S-H2 Part 11 Q2): on a chain past
P1.i whose Hide doom holds (no escape of `μ_Hide`), a close level whose next message is the fold
has `A_c = jointAgree` (`consSet_eq_jointAgree`). -/
theorem consSet_eq_of_DH {L es : Log} {i : ℕ} (hi : i < 5)
    (hlen : p1Start i + 2 * hEll i ≤ es.length) (hD : DH L es)
    (hfar : ¬ farL (kindOfC es) L es i) (hC : truthC (kindOfC es) L es i) :
    consSet (kindOfC es) L es i =
      jointAgree (wordK (kindOfC es) L es i) (decodeL (kindOfC es) L es i) :=
  consSet_eq_jointAgree hi hfar hC (noHide_full hi (by unfold hRnd; omega) hfar (hD i hi))

/-! ## Part F: the entry's potential `μ = μ_doom + μ_Hide` and its step law at `εR` -/

/-- **The entry's potential** (§10 changes 15): the doom potential of `DC Rej (Dp Dk)` plus the
Hide potential. -/
noncomputable def muT (Rej : Log → Log → Prop) (Dk : ℕ → Log → Log → Prop) (L : Log) : ℝ≥0 :=
  G.muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd4) L + G.muG DH (pRoundG DH fsRnd4) L

theorem muT_empty (Rej : Log → Log → Prop) (Dk : ℕ → Log → Log → Prop) : muT Rej Dk [] = 0 := by
  simp only [muT, G.muG_empty, add_zero]

open Classical in
/-- **`KState.step` at `εR` for the entry's potential** (BLUEPRINT §5.1, §10 changes 15):
`kstate_step` (`εD`) and `hide_step` (`ε_H`) through `step_add`, with `εD + ε_H = εR`. -/
theorem muT_step {Rej : Log → Log → Prop} {Dk : ℕ → Log → Log → Prop} {N : ℕ}
    (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR) (ob : PhaseObl Rej Dk N) (L : Log) (q : ByteArray)
    (hl : L.length < logCap) (hμ : muT Rej Dk L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muT Rej Dk (L ++ [(q, a)]) ≤ (muT Rej Dk L + epsR) * 2 ^ 256 := by
  have h := step_add (fun L q hl hμ hq => kstate_step hN ob L q hl hμ hq)
    (fun L q hl hμ hq => hide_step L q hl hμ hq) L q hl hμ hq
  rwa [epsD_add_epsH] at h

/-- Below `1`, neither potential has escaped and the log is not bad. -/
theorem muT_lt_one {Rej : Log → Log → Prop} {Dk : ℕ → Log → Log → Prop} {L : Log}
    (h : muT Rej Dk L < 1) :
    ¬ Bad L ∧ ¬ G.EscG (DC Rej (Dp Dk)) L ∧ ¬ G.EscG DH L := by
  have h1 := G.muG_lt_one _ _ (lt_of_le_of_lt le_self_add h)
  have h2 := G.muG_lt_one _ _ (lt_of_le_of_lt le_add_self h)
  exact ⟨h1.1, h1.2, h2.2⟩

/-! ## Controls -/

/-- Control (positive): before P1.0's first answer every chain satisfies the Hide doom. -/
theorem DH_seed (L : Log) (e : ByteArray × Digest) : DH L [e] :=
  DH_short (by
    have := (p1_phase (i := 0) (by norm_num)).hb1; simp only [List.length_singleton]; omega)

/-- Control (negative): a hidden disagreement at P1.i's end refutes `noHide`, so the Hide doom is
not vacuous. -/
theorem not_noHide_of_hideL {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5)
    (hR : hRnd es i = hEll i) (hfar : ¬ farL κ L es i)
    (hH : hideL κ L es i) : ¬ noHide κ L es i :=
  fun hn => noHide_full hi hR hfar hn hH

/-- Control (negative): a formal extension past the chain has no real cap entry. -/
theorem not_capOK_ext (es₀ : Log) (as : List Digest) {i : ℕ} (h : es₀.length ≤ capPos i) :
    ¬ capOK (ext es₀ as) i := by
  rintro ⟨len, -, hc⟩
  rw [fsCheck_ext_ge es₀ as h] at hc
  cases hc

end FR.Snd.T4

end G6_FRSoundness4TailHide

section G6_FRSoundness4TailFold

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessWalk`, `FRSoundnessWeights` and `FRSoundnessFold` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The walk, the weights and the folds at `seq4` (T4)

The 3.x declarations of `FRSoundnessWalk`, `FRSoundnessWeights` and `FRSoundnessFold` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessWalk` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle

/-! ## Part A: logs and their prefixes -/

theorem isChain_take {L : Log} {j : ℕ} (h : G.IsChain L j) {t : ℕ} (ht : j < t) :
    G.IsChain (L.take t) j :=
  ⟨by simp; exact ⟨ht, h.1⟩, by rw [entriesOf_pathOf_take L ht]; exact h.2⟩

/-! ## Part B: the walk -/

/-- **Stability of a doom on chains**: on a non-bad log, `D` reads the same off the log before a
chain's last entry and off the log, on the chain itself (the reads of A.10's `hstab` column, on
the real chain). -/
def ChainStab (D : Log → Log → Prop) : Prop :=
  ∀ L j, ¬ Bad L → G.IsChain L j →
    (D (L.take j) (entriesOf L (pathOf L j)) ↔ D L (entriesOf L (pathOf L j)))

/-- A nonempty prefix of a matching chain matches. -/
theorem matches_take {es : Log} (h : G.Matches es) : ∀ d k, es.length = k + d → 1 ≤ k →
    G.Matches (es.take k) := by
  intro d
  induction d with
  | zero => intro k hk _; rw [List.take_of_length_le (by omega)]; exact h
  | succ d ih =>
    intro k hk h1
    have h' := ih (k + 1) (by omega) (by omega)
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some] at h'
    exact G.matches_of_append (fun he => by
      have := congrArg List.length he; rw [List.length_take, List.length_nil] at this; omega) h'

theorem isChain_prefix {L : Log} {i : ℕ} (hci : G.IsChain L i) {m : ℕ}
    (hm : m < (pathOf L i).length) : G.IsChain L (pathOf L i)[m] := by
  refine ⟨lt_of_le_of_lt (mem_pathOf_le (List.getElem_mem _)) hci.1, ?_⟩
  rw [entriesOf_prefix L i hm]
  exact matches_take hci.2 ((pathOf L i).length - (m + 1)) (m + 1)
    (by rw [length_entriesOf]; omega) (by omega)

/-- **One step of the walk**: with no escape, `D` on the chain's first `m + 1` entries (charged at
the `(m+1)`-th) gives `D` on its first `m + 2` (charged at the `(m+2)`-th). -/
theorem walk_step {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ G.EscG D L) {i : ℕ} (hci : G.IsChain L i) {m : ℕ} (hm : m + 1 < (pathOf L i).length)
    (hD : D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1))) :
    D (L.take (pathOf L i)[m + 1]) ((entriesOf L (pathOf L i)).take (m + 2)) := by
  set p := pathOf L i
  set es := entriesOf L p
  have hlt : p[m] < p[m + 1] := pathOf_lt hm
  -- transport `D` on the `(m+1)`-prefix from `L.take p[m]` to `L.take p[m+1]`
  have hb' := not_bad_take hb p[m + 1]
  have hc' : G.IsChain (L.take p[m + 1]) p[m] := isChain_take (isChain_prefix hci (by omega)) hlt
  have key := hS _ _ hb' hc'
  rw [List.take_take, min_eq_left hlt.le, entriesOf_pathOf_take L hlt,
    entriesOf_prefix L i (by omega)] at key
  have hD' := key.mp hD
  -- no escape at the chain of `p[m+1]`
  by_contra hnd
  refine hE ⟨p[m + 1], G.mem_chains.mpr (isChain_prefix hci hm), ?_⟩
  rw [entriesOf_prefix L i hm]
  refine ⟨by rw [List.length_take, length_entriesOf]; omega, ?_, hnd⟩
  rw [List.dropLast_eq_take, List.length_take, length_entriesOf, List.take_take,
    show min (m + 2) p.length - 1 = m + 1 by omega, min_eq_left (by omega)]
  exact hD'

/-- **The walk forwards**: with no escape, `D` on a prefix carries to the whole chain (charged at
its last entry). -/
theorem walk_fwd {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ G.EscG D L) {i : ℕ} (hci : G.IsChain L i) {m : ℕ} (hm : m < (pathOf L i).length)
    (hD : D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1))) :
    D (L.take i) (entriesOf L (pathOf L i)) := by
  have hn : ∀ d, ∀ m (hm : m < (pathOf L i).length), (pathOf L i).length - (m + 1) = d →
      D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1)) →
      D (L.take i) (entriesOf L (pathOf L i)) := by
    intro d
    induction d with
    | zero =>
      intro m hm hd hD
      have hlast : (pathOf L i)[m] = i := by
        have := pathOf_getLast? L i
        rw [List.getLast?_eq_getElem?] at this
        have h2 : (pathOf L i)[m]? = some i := by
          rw [show m = (pathOf L i).length - 1 by omega]; exact this
        rw [List.getElem?_eq_getElem hm] at h2
        exact Option.some.inj h2
      rw [hlast, List.take_of_length_le (l := entriesOf L (pathOf L i))
        (by rw [length_entriesOf]; omega)] at hD
      exact hD
    | succ d ih =>
      intro m hm hd hD
      exact ih (m + 1) (by omega) (by omega) (walk_step hS hb hE hci (by omega) hD)
  exact hn _ m hm rfl hD

/-- **The walk backwards** (A.10: "by induction from Pf upwards"): with no escape, `¬ D` at the
chain's end gives `¬ D` on every prefix. -/
theorem walk_back {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ G.EscG D L) {i : ℕ} (hci : G.IsChain L i) (hend : ¬ D (L.take i) (entriesOf L (pathOf L i)))
    {m : ℕ} (hm : m < (pathOf L i).length) :
    ¬ D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1)) :=
  fun hD => hend (walk_fwd hS hb hE hci hm hD)

/-! ## Part C: the Hide potential's walk -/

/-- **The Hide doom is stable on chains**: before P1.i a level holds on both logs; after, the
chain's cap is a real entry (`capOK_of_matches`), so the word reads the same (`wordK_stab`). -/
theorem DH_chainStab : ChainStab DH := by
  intro L j hb hci
  refine forall₂_congr fun i hi => ?_
  set es := entriesOf L (pathOf L j)
  by_cases h0 : hRnd es i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero h0⟩
  have hl : capPos i < es.length := by
    have := capPos_lt hi; unfold hRnd at h0; omega
  have hc := capOK_of_matches hci.2 hi hl
  have hes : ext (es.take es.length) [] = es := by rw [ext_nil, List.take_length]
  have hw := wordK_stab hb hci es.length [] hi (kindOfC es) (by rw [hes]; exact hc)
  rw [hes] at hw
  have hd := decodeL_congr hw
  unfold noHide hDiff farL
  rw [hw, hd]

/-- **No Hide escape keeps `DH` on every chain** (it holds at the seed, `DH_short`). -/
theorem DH_of_noEsc {L : Log} (hb : ¬ Bad L) (hE : ¬ G.EscG DH L) {i : ℕ} (hci : G.IsChain L i) :
    DH L (entriesOf L (pathOf L i)) := by
  have hne : 0 < (pathOf L i).length := List.length_pos_iff.mpr (pathOf_ne_nil L i)
  have h0 : DH (L.take (pathOf L i)[0]) ((entriesOf L (pathOf L i)).take (0 + 1)) :=
    DH_short (by
      have := (p1_phase (i := 0) (by norm_num)).hb1
      simp only [List.length_take]; omega)
  exact (DH_chainStab L i hb hci).mp (walk_fwd DH_chainStab hb hE hci hne h0)

/-- **What `final` gets from `μ_Hide`** (§10 changes 14–15): on a non-bad log with no Hide escape,
a chain past P1.i whose level `i` is close and whose next message is the fold has
`A_c = jointAgree`. -/
theorem consSet_eq_of_noEsc {L : Log} (hb : ¬ Bad L) (hE : ¬ G.EscG DH L) {j : ℕ}
    (hci : G.IsChain L j) {i : ℕ} (hi : i < 5)
    (hlen : p1Start i + 2 * hEll i ≤ (entriesOf L (pathOf L j)).length)
    (hfar : ¬ farL (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i)
    (hC : truthC (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i) :
    consSet (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i =
      jointAgree (wordK (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i)
        (decodeL (kindOfC (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i) :=
  consSet_eq_of_DH hi hlen (DH_of_noEsc hb hE hci) hfar hC

/-- Control (positive): a doom that reads only the chain is stable. -/
theorem chainStab_const (P : Log → Prop) : ChainStab fun _ es => P es :=
  fun _ _ _ _ => Iff.rfl

end FR.Snd.T4

/-! # Port of `FRSoundnessWeights` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

/-! ## Part A: extensions of ℕ-indexed tables -/

/-- **The codeword weight's extension is the tensor weight** (A.1; `tensorTwin`, the spec of
`tensorW`): `G̃_p(ρ) = Π_v (1 − ρ_v + ρ_v Ŵ_v(D[p]))`. -/
theorem mleN_gW (κ : CKind) (i p : ℕ) (ρ : Fin (mLog κ i) → K) :
    mleN (mLog κ i) (gW κ i p) ρ =
      tensorTwin D logNMax (mLog κ i) (fun v => if h : v < mLog κ i then ρ ⟨v, h⟩ else 0) p := by
  simp only [mleN, gW]
  rw [mle_bitProd, tensorTwin, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun v _ => ?_
  simp [wAtD]

/-- **P3.i's table's extension** (A.9 `finP i`): the folded weight's plus the queried positions'
tensor weights. -/
theorem mleN_wNext (κ : CKind) (es : Log) (i : ℕ) (Wf : ℕ → K) (ρ : Fin (mLog κ i) → K) :
    mleN (mLog κ i) (wNext κ es i Wf) ρ = mleN (mLog κ i) Wf ρ +
      ∑ q ∈ range (CKind.lv κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
        mleN (mLog κ i) (gW κ i (qPos κ es i q)) ρ := by
  have h : (fun u : Fin (2 ^ mLog κ i) => wNext κ es i Wf u) =
      (fun u : Fin (2 ^ mLog κ i) => Wf u) + fun u : Fin (2 ^ mLog κ i) =>
      ∑ q ∈ range (CKind.lv κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
        gW κ i (qPos κ es i q) u := by
    funext u; simp only [wNext, Pi.add_apply, K.smulF_eq_mul]; rfl
  rw [mleN, h, mle_add, mle_sum]
  rfl

/-! ## Part B: the next level's table -/

/-- **Level `i + 1`'s table** (A.10 P3.i → P1.(i+1)): level `i`'s table bound at `sᵢ`, plus
the queried codeword weights, split. -/
noncomputable def nextW (κ : CKind) (es : Log) (i : ℕ) (W : ℕ → K) : ℕ → K :=
  wSplit (wNext κ es i (foldW (CKind.lv κ i).ell (sAt es i) W))

/-- **The claim moves to the next level** (A.10 P1.i, C.i, P2.i, P3.i): if P1.i's folded claim
is `⟨foldW W, fold_z(f⁽ⁱ⁾)⟩`, the next message is the fold (`truthC`) and every query is
consistent (`truthP3`), the batched claim is `⟨nextW W, f⁽ⁱ⁺¹⁾⟩`. -/
theorem truthP1_next {κ : CKind} {L es : Log} {i : ℕ} (hi : i + 1 < 5) {W : ℕ → K} {c : K}
    (hc : c = ∑ x ∈ range (2 ^ mLog κ i), foldW (CKind.lv κ i).ell (sAt es i) W x * foldMsg κ L es i x)
    (hC : truthC κ L es i) (h3 : truthP3 κ L es i) :
    truthP1 κ L es (i + 1) (nextW κ es i W) (vNext κ L es i c) := fun _ => by
  rw [nextW, wSplit_sum hi, vNext_eq hc hC h3]

/-- **`finPf`'s level step at the spec** (`lvStepV`): the next table's extension at
`(β, ρ)` is `û(β)·(W̃(sᵢ, ρ) + Σ_q eq(κ_c, bits₉(q))·tensorW(p_q, ρ))`. -/
theorem mleN_nextW (κ : CKind) (es : Log) (i : ℕ) (W : ℕ → K) (ρ : Fin (mLog κ i + 1) → K) :
    mleN (mLog κ i + 1) (nextW κ es i W) ρ = uHat (ρ 0) *
      (mleN ((CKind.lv κ i).ell + mLog κ i) W (Fin.append (fun v : Fin (CKind.lv κ i).ell => sAt es i v)
          (Fin.tail ρ)) +
        ∑ q ∈ range (CKind.lv κ i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
          tensorTwin D logNMax (mLog κ i)
            (fun v => if h : v < mLog κ i then Fin.tail ρ ⟨v, h⟩ else 0) (qPos κ es i q)) := by
  rw [nextW, mleN_wSplit, mleN_wNext, mleN_foldW]
  simp only [mleN_gW]

/-! ## T4: the level-0 message in F (from `FRSoundnessPIOP` Part A; `LigeritoOut.claim0` reads it) -/

/-- **A.10's `f⁽⁰⁾` in F**: element `e` is the constant coefficient of the decoded level-0
message's element `e` (`fTab`, row bits first). -/
noncomputable def fF (κ : CKind) (L es : Log) (e : ℕ) : F := (fTab κ L es 0 e).f₀

/-- **A close level-0 word decodes to F-messages** (`interp_F_D`): every decoded row's message is
F-valued. -/
theorem msgOf_F {κ : CKind} {L es : Log} (hfar : ¬ farL κ L es 0) (r x : ℕ) :
    msgOf κ L es 0 r x = algebraMap F K (msgOf κ L es 0 r x).f₀ := by
  by_cases hr : r < (CKind.lv κ 0).rows
  swap
  · simp only [msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ mLog κ 0
  swap
  · simp only [msgOf, hr, hx, dite_true, dite_false]; rfl
  obtain ⟨hek, hN, -, hk, hn⟩ := lv_params κ (i := 0) (by norm_num)
  have hkN : 2 ^ mLog κ 0 ≤ nMax := by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN
  have hnN : 2 ^ (CKind.lv κ 0).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := decodeL_spec hfar
  set rr : Fin (CKind.lv κ 0).rows := ⟨r, hr⟩
  have hv := hV rr
  rw [codeK, hk, ← encCode_D hkN] at hv
  have hA : 2 ^ mLog κ 0 ≤ (jointAgree (wordK κ L es 0) (decodeL κ L es 0)).card := by
    have : lvK κ 0 ≤ 2 ^ (CKind.lv κ 0).logN - lvE κ 0 := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  obtain ⟨c, hc⟩ := interp_F_D hnN hkN hv (fun j => wordOf κ L es 0 rr j) _ hA fun j hj => by
    rw [mem_jointAgree] at hj; rw [← hj rr]; rfl
  have := msgOf_eq (i := 0) (by norm_num) (r := rr) hc.symm ⟨x, hx⟩
  rw [this, algebraMap_f₀]

/-- **`f⁽⁰⁾` is F-valued**: on a close level-0 word, `fTab … 0 = ι ∘ fF`. -/
theorem fTab_F {κ : CKind} {L es : Log} (hfar : ¬ farL κ L es 0) (e : ℕ) :
    fTab κ L es 0 e = algebraMap F K (fF κ L es e) := msgOf_F hfar _ _

/-! T4: the witness bits `z = unpack f⁽⁰⁾` (from `FRSoundnessPIOP` Part B; P4a's dooms read `zW`) -/

/-- **A.10's `z := unpack f⁽⁰⁾`** (A.7's pack map): bit `b` of `z` is bit `b mod 128` of
`f[b / 128]`. -/
noncomputable def zW (κ : CKind) (L es : Log) (b : ℕ) : F :=
  unpack (fF κ L es (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

/-- Block `blk`'s positions (A.7: block element `k` is `f[blk·128 + k]`, `2^14` bits). -/
noncomputable def zBlk (κ : CKind) (L es : Log) (blk : ℕ) : Block.Pos → F :=
  fun k => zW κ L es (blk * 2 ^ Blake2sCircuit.m + k.val)

/-- Block `blk`'s element `k` is `f[blk·128 + k]`: its bits are positions `128k … 128k + 127`. -/
theorem zBlk_elem (κ : CKind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    zBlk κ L es blk k = unpack (fF κ L es (blk * 128 + k.val / 128))
      ⟨k.val % 128, Nat.mod_lt _ (by norm_num)⟩ := by
  have hm : (2 : ℕ) ^ Blake2sCircuit.m = 128 * 128 := by decide
  have h1 : (blk * (128 * 128) + k.val) / 128 = blk * 128 + k.val / 128 := by omega
  have h2 : (blk * (128 * 128) + k.val) % 128 = k.val % 128 := by omega
  simp only [zBlk, zW, hm, h1, h2]

/-- **The unpacked witness is Boolean** (`leaf_sound`'s `hbool`). -/
theorem zBlk_bool (κ : CKind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    BlockR1CS.IsBool (zBlk κ L es blk k) :=
  unpack_boolean _ _


/-! ## Part C: level 0 (T4: `truthP1_zero` is B′'s handoff, unused downstream; not copied) -/

section Level0
open Circ

end Level0

end FR.Snd.T4

/-! # Port of `FRSoundnessFold` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: intermediate folds -/

section Generic

variable {K' : Type*} [Field K'] [DecidableEq K'] {n : ℕ}

end Generic

/-- Level `i`'s word with ℕ-indexed rows (`0` past the rows). -/
noncomputable def wN (κ : CKind) (L es : Log) (i r : ℕ) : Fin (2 ^ (CKind.lv κ i).logN) → K :=
  fun j => if h : r < (CKind.lv κ i).rows then wordK κ L es i ⟨r, h⟩ j else 0

/-- **Level `i`'s word after `l` fold rounds**: row `r` is `Σ_{u<2^l} eq(sᵢ, u)·W[u + 2^l r]`
(the rounds bind the row bits low first). -/
noncomputable def pf (κ : CKind) (L es : Log) (i l r : ℕ) : Fin (2 ^ (CKind.lv κ i).logN) → K :=
  fun j => ∑ u ∈ range (2 ^ l), eqBits (sAt es i) l u * wN κ L es i (u + 2 ^ l * r) j

/-- **The intermediate fold is close**: its `2^(ℓᵢ−l)` rows are jointly `eᵢ`-close to `C_K`. P1.i's
far doom is `¬ closeP` at the rounds answered. -/
def closeP (κ : CKind) (L es : Log) (i l : ℕ) : Prop :=
  CloseN (codeK κ i) (lvE κ i) (2 ^ ((CKind.lv κ i).ell - l)) (pf κ L es i l)

/-- One more round folds rows `2r`, `2r + 1` at `s_l`. -/
theorem pf_succ (κ : CKind) (L es : Log) (i l : ℕ) :
    pf κ L es i (l + 1) = foldN (sAt es i l) (pf κ L es i l) := by
  funext r j
  set s := sAt es i
  have e1 : ∀ u ∈ range (2 ^ l), eqBits s (l + 1) u = eqBits s l u * (1 - s l) :=
    fun u hu => bitSel_succ_lo _ _ (mem_range.1 hu)
  have e2 : ∀ u ∈ range (2 ^ l), eqBits s (l + 1) (2 ^ l + u) = eqBits s l u * s l :=
    fun u hu => bitSel_succ_hi _ _ (mem_range.1 hu)
  have hA : ∀ u, u + 2 ^ (l + 1) * r = u + 2 ^ l * (2 * r) := fun u => by ring
  have hB : ∀ u, 2 ^ l + u + 2 ^ (l + 1) * r = u + 2 ^ l * (2 * r + 1) := fun u => by ring
  simp only [pf, foldN, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hr : range (2 ^ (l + 1)) = range (2 ^ l + 2 ^ l) := by congr 1; ring
  have s1 : ∑ u ∈ range (2 ^ l), eqBits s (l + 1) u * wN κ L es i (u + 2 ^ (l + 1) * r) j =
      ∑ u ∈ range (2 ^ l), eqBits s l u * (1 - s l) * wN κ L es i (u + 2 ^ l * (2 * r)) j :=
    sum_congr rfl fun u hu => by rw [e1 u hu, hA]
  have s2 : ∑ u ∈ range (2 ^ l),
      eqBits s (l + 1) (2 ^ l + u) * wN κ L es i (2 ^ l + u + 2 ^ (l + 1) * r) j =
      ∑ u ∈ range (2 ^ l), eqBits s l u * s l * wN κ L es i (u + 2 ^ l * (2 * r + 1)) j :=
    sum_congr rfl fun u hu => by rw [e2 u hu, hB]
  rw [hr, sum_range_add, s1, s2, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun u _ => by ring

theorem pf_zero (κ : CKind) (L es : Log) (i r : ℕ) : pf κ L es i 0 r = wN κ L es i r := by
  funext j; simp [pf, eqBits, bitSel]

/-- **`closeP 0` is `¬ far_i`.** -/
theorem closeP_zero {κ : CKind} {L es : Log} {i : ℕ} : closeP κ L es i 0 ↔ ¬ farL κ L es i := by
  have hrow : (CKind.lv κ i).rows = 2 ^ ((CKind.lv κ i).ell - 0) := by rw [Nat.sub_zero]; rfl
  have heq : (fun r : Fin (2 ^ ((CKind.lv κ i).ell - 0)) => pf κ L es i 0 r) =
      wordK κ L es i ∘ finCongr hrow.symm := by
    funext r j
    simp only [pf_zero, wN, Function.comp_apply, finCongr_apply, Fin.cast]
    have hr : (r : ℕ) < (CKind.lv κ i).rows := by rw [hrow]; exact r.2
    simp only [hr, ↓reduceDIte]
  simp only [closeP, CloseN, heq, jointClose_equiv, farL, not_forall, not_not]

/-- Closeness survives the rounds. -/
theorem closeP_succ {κ : CKind} {L es : Log} {i l : ℕ} (hl : l < (CKind.lv κ i).ell)
    (h : closeP κ L es i l) : closeP κ L es i (l + 1) := by
  unfold closeP at h ⊢
  rw [two_pow_sub hl] at h
  rw [pf_succ]
  exact closeN_fold _ h

theorem closeP_of_not_far {κ : CKind} {L es : Log} {i : ℕ} (hf : ¬ farL κ L es i) :
    ∀ l ≤ (CKind.lv κ i).ell, closeP κ L es i l
  | 0, _ => closeP_zero.mpr hf
  | l + 1, hl => closeP_succ (by omega) (closeP_of_not_far hf l (by omega))

/-- The bad set of round `l` (`round_bad_cover`): at most `2^(ℓᵢ−l−1)·C_mca(nᵢ, kᵢ, eᵢ)` values. -/
theorem closeP_cover {κ : CKind} {i : ℕ} (hi : i < 5) (L es : Log) {l : ℕ}
    (hl : l < (CKind.lv κ i).ell) :
    ∃ B : Finset K, B.card ≤ 2 ^ ((CKind.lv κ i).ell - (l + 1)) * cMca (lvN κ i) (lvK κ i) (lvE κ i) ∧
      ∀ z ∉ B, closeP κ L es i l ∨ ¬ CloseN (codeK κ i) (lvE κ i) (2 ^ ((CKind.lv κ i).ell - (l + 1)))
        (foldN z (pf κ L es i l)) := by
  obtain ⟨hek, hN, -, -, hn⟩ := lv_params κ hi
  have hnN : 2 ^ (CKind.lv κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨B, hB, hsub⟩ := round_bad_cover (Dpts_injective hnN) (by rw [← hn]; exact hek)
    (fun c : Fin (2 ^ ((CKind.lv κ i).ell - (l + 1))) => pf κ L es i l (2 * c))
    (fun c => pf κ L es i l (2 * c + 1))
  refine ⟨B, by simpa [lvN, Fintype.card_fin] using hB, fun z hz => ?_⟩
  by_cases hc : CloseN (codeK κ i) (lvE κ i) (2 ^ ((CKind.lv κ i).ell - (l + 1)))
    (foldN z (pf κ L es i l))
  · left
    unfold closeP
    rw [two_pow_sub hl]
    exact closeN_unfold (Dpts_injective hnN) (by rw [← hn]; exact hek)
      (fun c hzc => hz (hsub c hzc)) hc
  · exact Or.inr hc

/-- Level `i`'s encoding is a codeword of `C_K`. -/
theorem encAt_eq_enc {κ : CKind} {i : ℕ} (hi : i < 5) (m : ℕ → K)
    (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    encAt κ i m j = enc D (2 ^ (CKind.lv κ i).logN) _ (fun x : Fin (2 ^ mLog κ i) => m x) j := by
  obtain ⟨-, hN, hm, -, hn⟩ := lv_params κ hi
  rw [encAt, encF_eq hm (lt_of_lt_of_le j.2 (hn ▸ hN)), enc_eq_encN]

theorem enc_mem_codeK {κ : CKind} {i : ℕ} (hi : i < 5) (c : Fin (2 ^ mLog κ i) → K) :
    enc D (2 ^ (CKind.lv κ i).logN) _ c ∈ codeK κ i := by
  obtain ⟨-, hN, -, hk, hn⟩ := lv_params κ hi
  have hkn : 2 ^ mLog κ i ≤ 2 ^ (CKind.lv κ i).logN := by
    rw [← hk, ← hn]; unfold lvK; exact Nat.div_le_self _ _
  rw [codeK, hk, ← encCode_D (hkn.trans (hn ▸ hN))]
  exact LinearMap.mem_range_self _ c

/-- After all rounds the single row is the column fold `foldAt`. -/
theorem pf_full (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    pf κ L es i (CKind.lv κ i).ell 0 j = foldAt κ L es i j := by
  simp only [pf, mul_zero, add_zero, foldAt]
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqBits (sAt es i) (CKind.lv κ i).ell u * wN κ L es i u j)]
  refine sum_congr rfl fun u _ => ?_
  simp only [wN, Level.rows, u.2, ↓reduceDIte]

/-- **A close next codeword makes the full fold close** (`truthP2`): a far fold refutes it. -/
theorem closeP_of_truthP2 {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5)
    (h : truthP2 κ L es i) : closeP κ L es i (CKind.lv κ i).ell := by
  classical
  refine ⟨consSet κ L es i, h, fun _ => enc D _ _ fun x : Fin (2 ^ mLog κ i) =>
    nextMsg κ L es i x, fun _ => enc_mem_codeK hi _, ?_⟩
  ext j
  simp only [mem_jointAgree, consSet, mem_filter, mem_univ, true_and]
  rw [encAt_eq_enc hi]
  constructor
  · intro hj; have := hj 0; rwa [Fin.val_zero, pf_full] at this
  · intro hj r
    have hr0 : (r : ℕ) = 0 := by have := r.2; simp only [Nat.sub_self, pow_zero] at this; omega
    rw [hr0, pf_full]; exact hj

/-! ## Part B: P3.i's batched table -/

/-- **P3.i's table** (512 entries over `κ_c`'s 9 coordinates): query `q`'s consistency error
(`0` past `tᵢ`), plus the folded claim's offset `d`. -/
noncomputable def p3T (κ : CKind) (L es : Log) (i : ℕ) (d : K) : Array K :=
  Array.ofFn (n := 2 ^ 9) fun q => (if (q : ℕ) < (CKind.lv κ i).t then consErr κ L es i q else 0) + d

theorem p3T_size (κ : CKind) (L es : Log) (i : ℕ) (d : K) : (p3T κ L es i d).size = 2 ^ 9 :=
  Array.size_ofFn

theorem tbl_p3T (κ : CKind) (L es : Log) (i : ℕ) (d : K) (q : Fin (2 ^ 9)) :
    tbl 9 (p3T κ L es i d) q = (if (q : ℕ) < (CKind.lv κ i).t then consErr κ L es i q else 0) + d := by
  simp [tbl, p3T, Array.getD_eq_getD_getElem?]

theorem lvl_t_lt (κ : CKind) {i : ℕ} (hi : i < 5) : (CKind.lv κ i).t < 2 ^ 9 - 1 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The table's extension at `κ_c`** is `d + p3Batch`. -/
theorem p3T_mle (κ : CKind) (L es : Log) {i : ℕ} (hi : i < 5) (d : K) :
    ∑ q : Fin (2 ^ 9), eqBits (fun v => algebraMap F K (kcAt es i v)) 9 q *
      tbl 9 (p3T κ L es i d) q = d + p3Batch κ L es i := by
  set e : ℕ → K := fun q => eqBits (fun v => algebraMap F K (kcAt es i v)) 9 q
  set g : ℕ → K := fun q => if q < (CKind.lv κ i).t then consErr κ L es i q else 0
  have h1 : ∀ q : Fin (2 ^ 9), e q * tbl 9 (p3T κ L es i d) q = e q * g q + e q * d :=
    fun q => by rw [tbl_p3T, mul_add]
  rw [sum_congr rfl fun q _ => h1 q, sum_add_distrib, ← sum_mul,
    Fin.sum_univ_eq_sum_range e, Fin.sum_univ_eq_sum_range (fun q => e q * g q)]
  suffices hs : ∑ q ∈ range (2 ^ 9), e q * g q = p3Batch κ L es i by
    rw [hs, show ∑ q ∈ range (2 ^ 9), e q = 1 from sum_eqBits_one _ _, one_mul, add_comm]
  have ht : (CKind.lv κ i).t ≤ 2 ^ 9 := by have := lvl_t_lt κ hi; omega
  rw [← Finset.sum_range_add_sum_Ico _ ht, Finset.sum_eq_zero (s := Ico _ _) fun q hq => by
    have : ¬ q < (CKind.lv κ i).t := by simp only [mem_Ico] at hq; omega
    simp only [g, this, ↓reduceIte, mul_zero],
    add_zero, p3Batch]
  refine sum_congr rfl fun q hq => ?_
  simp only [g, e, mem_range.1 hq, ↓reduceIte, K.smulF_eq_mul, ← K.algebraMap_eq_ofF,
    algebraMap_eqBits]

/-- **The next claim's error** (A.10 P3.i): `v_{i+1} − ⟨wNext Wf, f⁽ⁱ⁺¹⁾⟩ = d + p3Batch`, with
`d = c − ⟨Wf, f⁽ⁱ⁺¹⁾⟩` over level `i`'s folded message. -/
theorem vNext_sub (κ : CKind) (L es : Log) (i : ℕ) (Wf : ℕ → K) (c : K) :
    vNext κ L es i c - ∑ x ∈ range (2 ^ mLog κ i), wNext κ es i Wf x * nextMsg κ L es i x =
      (c - ∑ x ∈ range (2 ^ mLog κ i), Wf x * nextMsg κ L es i x) + p3Batch κ L es i := by
  have hq : ∀ q, foldAtN κ L es i (qPos κ es i q) = consErr κ L es i q +
      ∑ x ∈ range (2 ^ mLog κ i), nextMsg κ L es i x * gW κ i (qPos κ es i q) x := by
    intro q; rw [consErr, ← encAt_eq_sum]; ring
  simp only [vNext, p3Batch, wNext, hq, K.smulF_eq_mul, mul_add, sum_add_distrib, add_mul,
    mul_sum, sum_mul]
  rw [sum_comm (s := range (CKind.lv κ i).t)]
  have hc : ∑ y ∈ range (2 ^ mLog κ i), ∑ q ∈ range (CKind.lv κ i).t,
      K.ofF (eqBits (kcAt es i) 9 q) * (nextMsg κ L es i y * gW κ i (qPos κ es i q) y) =
      ∑ y ∈ range (2 ^ mLog κ i), ∑ q ∈ range (CKind.lv κ i).t,
        K.ofF (eqBits (kcAt es i) 9 q) * gW κ i (qPos κ es i q) y * nextMsg κ L es i y :=
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  rw [hc]
  ring

/-- **The table is nonzero** when a query is inconsistent or the offset is nonzero (`tᵢ < 511`,
so the last entry is `d`). -/
theorem p3T_ne_zero {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) {d : K}
    (h : ¬ truthP3 κ L es i ∨ d ≠ 0) : tbl 9 (p3T κ L es i d) ≠ 0 := by
  intro hz
  have ht := lvl_t_lt κ hi
  have hd : d = 0 := by
    have := congrFun hz ⟨2 ^ 9 - 1, by omega⟩
    rwa [tbl_p3T, ite_eq_right_iff.mpr fun h => absurd h (by simp; omega), zero_add] at this
  rcases h with h | h
  · refine h fun q hq => ?_
    have := congrFun hz ⟨q, by omega⟩
    rwa [tbl_p3T, ite_eq_left_iff.mpr fun h => absurd hq h, hd, add_zero] at this
  · exact h hd

end FR.Snd.T4

end G6_FRSoundness4TailFold
