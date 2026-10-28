-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTruths` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.
import FRSoundness4TailStep
import FRRSEval
import FRBlockStream

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

