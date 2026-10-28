-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, §6.5 `fold_spec`/`enc_spec`/`agree_spec`;
-- §10 changes 14; stage S-H2, track L-ext).
import FRXEncB
import FRSoundnessTruths
import FRXRead

/-!
# One level's decoding, pure: what the machine computes is S-G's `msgOf`

The extractor decodes level `i` (BLUEPRINT §6.2 step 4) from three inputs:
- the word `W⁽ⁱ⁾` (`wordOf`, which the read stores);
- P1.i's challenges (`sAt`, from the chain answers);
- the next level's message (`nextMsg`): the final message at `i = 4`, else level `i + 1`'s
  decoded rows.

Every quantity has two `F` coordinates (`K = F + F u`), and the machine computes in `F`. This
module proves, in pure form, that the machine's steps give S-G's objects.

* `kAt_words`: a K challenge is the four words of its answer digest (`rdK` order).
* `foldAt_f₀`/`_f₁`: the column fold's coordinates are `F` dot products of the column with the
  coordinates of the `eq` table.
* `encF_f₀`/`_f₁`: `Enc` over `K` is `Enc` over `F` on each coordinate.
* `nextMsg_coords`: below level 4 the next message's coordinates are two decoded rows.
* `mem_consSet_iff`: the agreement flag is the four `F` equalities.
* **`level_decode`**: take a close word (`¬ farL`) with `A_c = jointAgree` (what `final` hands
  over, §10 changes 14). Interpolating each row of the word on the first `kᵢ` positions of `A_c`
  and running the butterflies gives `msgOf`, as an `F` element. So the decoded messages are
  `F`-valued (`msgOf_embed`).
-/

namespace FR.X

open RecursionFast FR Finset FR.Snd

/-! ## K coordinates -/

/-- `f₀` as an additive map. -/
def f₀Hom : K →+ F := ⟨⟨K.f₀, rfl⟩, fun _ _ => rfl⟩

/-- `f₁` as an additive map. -/
def f₁Hom : K →+ F := ⟨⟨K.f₁, rfl⟩, fun _ _ => rfl⟩

theorem K_sum_f₀ {ι : Type*} (s : Finset ι) (f : ι → K) : (∑ i ∈ s, f i).f₀ = ∑ i ∈ s, (f i).f₀ :=
  map_sum f₀Hom f s

theorem K_sum_f₁ {ι : Type*} (s : Finset ι) (f : ι → K) : (∑ i ∈ s, f i).f₁ = ∑ i ∈ s, (f i).f₁ :=
  map_sum f₁Hom f s

/-- An `F` scalar acts coordinatewise. -/
theorem algebraMap_mul_K (c : F) (a : K) : algebraMap F K c * a = ⟨c * a.f₀, c * a.f₁⟩ := by
  rw [K.algebraMap_eq_ofF, ← K.smulF_eq_mul]; rfl

theorem K_ext' {a b : K} (h0 : a.f₀ = b.f₀) (h1 : a.f₁ = b.f₁) : a = b := by
  cases a; cases b; simp only at h0 h1; rw [h0, h1]

/-- `a + u b` for `F` elements `a`, `b` is the pair `(a, b)`. -/
theorem ofF_add_u_mul (a b : F) : algebraMap F K a + K.u * algebraMap F K b = ⟨a, b⟩ := by
  rw [mul_comm, algebraMap_mul_K]
  refine K_ext' ?_ ?_
  · show a + b * 0 = a; rw [mul_zero, add_zero]
  · show 0 + b * 1 = b; rw [mul_one, zero_add]

/-- **A K challenge from its answer's four words**: `chK a` is `rdK`'s reading of `a`'s packed
words (`f₀ = (w₀, w₁)`, `f₁ = (w₂, w₃)`). -/
theorem chK_words (a : RecursionFast.Digest) :
    chK a = ⟨⟨wB ((packBytes a.toList).getD 0 0), wB ((packBytes a.toList).getD 1 0)⟩,
      ⟨wB ((packBytes a.toList).getD 2 0), wB ((packBytes a.toList).getD 3 0)⟩⟩ := by
  have key : ∀ m, ∀ (_ : m < 4), (Vector.ofFn fun i : Fin 8 => a[8 * m + i.1]'(by omega)) =
      Vector.ofFn fun i : Fin 8 => (((packBytes a.toList).getD m 0).toNat / 256 ^ i.1).toUInt8 := by
    intro m hm
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have hw := wordByte_packBytes a.toList (8 * m + i)
    rw [wordByte, show (8 * m + i) / 8 = m by omega, show (8 * m + i) % 8 = i by omega] at hw
    rw [hw, List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem (by omega),
      Option.getD_some]
  simp only [chK, K.ofBytes, F.ofBytes, Vector.getElem_ofFn]
  rw [← b64_ofBytes_word, ← b64_ofBytes_word, ← b64_ofBytes_word, ← b64_ofBytes_word,
    ← key 0 (by norm_num), ← key 1 (by norm_num), ← key 2 (by norm_num), ← key 3 (by norm_num)]
  rfl

/-- **A challenge read off the machine**: four heap words holding `a`'s packed words are `chK a`
under `rdK`. -/
theorem rdK_of_words {M : Mem} {b : ℕ} {a : RecursionFast.Digest}
    (h : ∀ m < 4, rd M (b + m) = (packBytes a.toList).getD m 0) : rdK M b = chK a := by
  rw [chK_words, rdK, rdF, rdF, rdB, rdB, rdB, rdB, ← h 0 (by norm_num), ← h 1 (by norm_num),
    ← h 2 (by norm_num), ← h 3 (by norm_num)]
  rfl

/-! ## The fold, `Enc` and the next message in coordinates -/

/-- **The column fold's `f₀`**: `Σ_r W[r][j] · eq(s, r).f₀`. -/
theorem foldAt_f₀ (κ : Kind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (lvl κ i).logN)) :
    (foldAt κ L es i j).f₀ = ∑ r : Fin (lvl κ i).rows,
      wordOf κ L es i r j * (eqBits (sAt es i) (lvl κ i).ell r).f₀ := by
  rw [foldAt, K_sum_f₀]
  refine sum_congr rfl fun r _ => ?_
  rw [wordK, mul_comm, algebraMap_mul_K]

/-- The column fold's `f₁`. -/
theorem foldAt_f₁ (κ : Kind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (lvl κ i).logN)) :
    (foldAt κ L es i j).f₁ = ∑ r : Fin (lvl κ i).rows,
      wordOf κ L es i r j * (eqBits (sAt es i) (lvl κ i).ell r).f₁ := by
  rw [foldAt, K_sum_f₁]
  refine sum_congr rfl fun r _ => ?_
  rw [wordK, mul_comm, algebraMap_mul_K]

theorem bitProd_algebraMap (ℓ x j : ℕ) :
    bitProd (fun v => algebraMap F K (wAtD v j)) ℓ x = algebraMap F K (bitProd (fun v => wAtD v j) ℓ x) :=
  (bitProd_map (algebraMap F K : F →* K) (fun v => wAtD v j) ℓ x).symm

/-- **`Enc` over K, coordinate `f₀`**: `Enc` over `F` of the messages' `f₀`. -/
theorem encF_f₀ (ℓ : ℕ) (c : Fin (2 ^ ℓ) → K) (j : ℕ) :
    (encF ℓ c j).f₀ = encF ℓ (fun x => (c x).f₀) j := by
  rw [encF, K_sum_f₀, encF]
  refine sum_congr rfl fun x _ => ?_
  rw [bitProd_algebraMap, mul_comm, algebraMap_mul_K]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  exact mul_comm _ _

/-- `Enc` over K, coordinate `f₁`. -/
theorem encF_f₁ (ℓ : ℕ) (c : Fin (2 ^ ℓ) → K) (j : ℕ) :
    (encF ℓ c j).f₁ = encF ℓ (fun x => (c x).f₁) j := by
  rw [encF, K_sum_f₁, encF]
  refine sum_congr rfl fun x _ => ?_
  rw [bitProd_algebraMap, mul_comm, algebraMap_mul_K]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  exact mul_comm _ _

/-- **The agreement flag in coordinates**: `j ∈ A_c` iff the fold's two coordinates are those of
`Enc(f⁽ⁱ⁺¹⁾)`. -/
theorem mem_consSet_iff (κ : Kind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (lvl κ i).logN)) :
    j ∈ consSet κ L es i ↔
      (∑ r : Fin (lvl κ i).rows, wordOf κ L es i r j * (eqBits (sAt es i) (lvl κ i).ell r).f₀ =
        encF (mLog κ i) (fun x => (nextMsg κ L es i x).f₀) j) ∧
      (∑ r : Fin (lvl κ i).rows, wordOf κ L es i r j * (eqBits (sAt es i) (lvl κ i).ell r).f₁ =
        encF (mLog κ i) (fun x => (nextMsg κ L es i x).f₁) j) := by
  rw [consSet, Finset.mem_filter]
  simp only [mem_univ, true_and, encAt]
  rw [← foldAt_f₀, ← foldAt_f₁, ← encF_f₀, ← encF_f₁]
  exact ⟨fun h => ⟨by rw [h], by rw [h]⟩, fun h => K_ext' h.1 h.2⟩

/-- **The next message from level `i + 1`'s rows** (`i < 4`): if level `i + 1`'s messages are
`F`-valued, K element `x` is the pair of rows `2(x mod 8)`, `2(x mod 8) + 1` at column `x div 8`. -/
theorem nextMsg_coords {κ : Kind} {L es : Log} {i : ℕ} (hi : i + 1 < nLevels)
    (hF : ∀ r x, msgOf κ L es (i + 1) r x = algebraMap F K (msgOf κ L es (i + 1) r x).f₀) (x : ℕ) :
    nextMsg κ L es i x = ⟨(msgOf κ L es (i + 1) (2 * (x % 8)) (x / 8)).f₀,
      (msgOf κ L es (i + 1) (2 * (x % 8) + 1) (x / 8)).f₀⟩ := by
  rw [nextMsg, if_pos hi, hF (2 * (x % 8)), hF (2 * (x % 8) + 1), ofF_add_u_mul]
  rfl

/-! ## The butterflies and the interpolation commute with `F → K` -/

theorem bflyRun_map (N s0 : ℕ) : ∀ (ℓ : ℕ) (Y : ℕ → F) (i : ℕ),
    algebraMap F K (bflyRun (M := F) D N s0 ℓ Y i) =
      bflyRun (M := K) D N s0 ℓ (fun j => algebraMap F K (Y j)) i
  | 0, _, _ => rfl
  | ℓ + 1, Y, i => by
    simp only [bflyRun, bflyLevel]
    rw [← bflyRun_map N s0 ℓ Y, ← bflyRun_map N s0 ℓ Y]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs <;> simp only [map_sub, map_mul]

theorem interpF_map (J : Finset ℕ) (y : ℕ → F) (j : ℕ) :
    algebraMap F K (interpF (M := F) D J y j) = interpF (M := K) D J (fun i => algebraMap F K (y i)) j := by
  simp only [interpF, map_sum, map_mul, map_prod, map_div₀, map_sub, Algebra.algebraMap_self,
    RingHom.id_apply]

/-! ## One level's decoding -/

/-- Level `i`'s agreement set as positions in `ℕ`. -/
noncomputable def consN (κ : Kind) (L es : Log) (i : ℕ) : Finset ℕ :=
  (consSet κ L es i).map Fin.valEmbedding

/-- Level `i`'s row `r` as an `ℕ`-indexed word (`0` past the positions). -/
def wordN (κ : Kind) (L es : Log) (i : ℕ) (r : Fin (lvl κ i).rows) (j : ℕ) : F :=
  if hj : j < 2 ^ (lvl κ i).logN then wordOf κ L es i r ⟨j, hj⟩ else 0

theorem mem_consN {κ : Kind} {L es : Log} {i j : ℕ} :
    j ∈ consN κ L es i ↔ ∃ h : j < 2 ^ (lvl κ i).logN, (⟨j, h⟩ : Fin _) ∈ consSet κ L es i := by
  simp only [consN, mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, hm⟩; exact ⟨_, hm, rfl⟩

/-- **One level's decoding** (BLUEPRINT §6.2 step 4 with §10 changes 14). Assume the word of
level `i` is close and `final`'s `A_c = jointAgree`. Interpolate row `r` on the first `kᵢ`
positions of `A_c` and run the `mLog` butterflies. The result, mapped into `K`, is S-G's
`msgOf κ L es i r`. -/
theorem level_decode {κ : Kind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ farL κ L es i)
    (hA : consSet κ L es i = jointAgree (wordK κ L es i) (decodeL κ L es i))
    (r : Fin (lvl κ i).rows) (x : Fin (2 ^ mLog κ i)) :
    algebraMap F K (bflyRun (M := F) D logNMax 0 (mLog κ i)
        (interpF D (firstK (2 ^ (lvl κ i).logN) (consN κ L es i) (2 ^ mLog κ i)) (wordN κ L es i r))
        x) = msgOf κ L es i r x := by
  classical
  obtain ⟨hek, hN, hm, hk, hn⟩ := lv_params κ hi
  have hnN : 2 ^ (lvl κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := decodeL_spec hfar
  obtain ⟨c, hc⟩ := exists_msg hi (hV r)
  rw [msgOf_eq hi hc x, bflyRun_map]
  simp only [interpF_map]
  refine decode_agree hm hnN (fun j hj => (mem_consN.1 hj).1) ?_ c _ (fun j hj => ?_) x
  · rw [consN, card_map, hA]
    have : lvK κ i ≤ 2 ^ (lvl κ i).logN - lvE κ i := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  · obtain ⟨hj', hmem⟩ := mem_consN.1 hj
    rw [hA, mem_jointAgree] at hmem
    have h1 := hmem r
    rw [wordK] at h1
    simp only [wordN, hj', dite_true]
    rw [h1, ← hc, enc_eq_encN]

/-- **The decoded messages are `F`-valued** on a close word with `A_c = jointAgree`. -/
theorem msgOf_embed {κ : Kind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ farL κ L es i)
    (hA : consSet κ L es i = jointAgree (wordK κ L es i) (decodeL κ L es i)) (r x : ℕ) :
    msgOf κ L es i r x = algebraMap F K (msgOf κ L es i r x).f₀ := by
  by_cases hr : r < (lvl κ i).rows
  swap
  · simp only [msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ mLog κ i
  swap
  · simp only [msgOf, hr, hx, dite_true, dite_false]; rfl
  rw [← level_decode hi hfar hA ⟨r, hr⟩ ⟨x, hx⟩]
  rfl

end FR.X
