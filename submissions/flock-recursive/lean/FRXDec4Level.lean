-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2).
import FRXLevel
import FRSoundness4TailTruths

/-!
# One level's decoding at revision 4.1's kinds, pure (`level_decode4`)

`FRXLevel` proves, at 3.x's `Kind`, that interpolating a close word's rows on the first `kᵢ`
agreement positions and running the butterflies gives S-G's `msgOf`. This module restates it
over T4's `CKind` copies (`FR.Snd.T4`: `wordOf`, `consSet`, `decodeL`, `farL`, `msgOf`, `mLog`, the
ladder `CKind.lv κ i = lvOf κ.m i`). The proofs are 3.x's: only the level parameters
(`lv_params`) are per kind.

* `foldAt4_f₀`/`_f₁`, `mem_consSet4_iff`: the agreement flag in `F` coordinates;
* `nextMsg4_coords`: below level 4 the next message is two decoded rows;
* **`level_decode4`** and `msgOf4_embed`.
-/

namespace FR.X

open RecursionFast FR Finset FR.Snd.T4

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **The column fold's `f₀`** at a 4.1 kind. -/
theorem foldAt4_f₀ (κ : Snd.CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (Snd.CKind.lv κ i).logN)) :
    (Snd.T4.foldAt κ L es i j).f₀ = ∑ r : Fin (Snd.CKind.lv κ i).rows,
      Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₀ := by
  rw [Snd.T4.foldAt, K_sum_f₀]
  refine sum_congr rfl fun r _ => ?_
  rw [Snd.T4.wordK, mul_comm, algebraMap_mul_K]

/-- The column fold's `f₁` at a 4.1 kind. -/
theorem foldAt4_f₁ (κ : Snd.CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (Snd.CKind.lv κ i).logN)) :
    (Snd.T4.foldAt κ L es i j).f₁ = ∑ r : Fin (Snd.CKind.lv κ i).rows,
      Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₁ := by
  rw [Snd.T4.foldAt, K_sum_f₁]
  refine sum_congr rfl fun r _ => ?_
  rw [Snd.T4.wordK, mul_comm, algebraMap_mul_K]

/-- **The agreement flag in coordinates** at a 4.1 kind. -/
theorem mem_consSet4_iff (κ : Snd.CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (Snd.CKind.lv κ i).logN)) :
    j ∈ Snd.T4.consSet κ L es i ↔
      (∑ r : Fin (Snd.CKind.lv κ i).rows, Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₀ =
        encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₀) j) ∧
      (∑ r : Fin (Snd.CKind.lv κ i).rows, Snd.T4.wordOf κ L es i r j * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₁ =
        encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₁) j) := by
  rw [Snd.T4.consSet, Finset.mem_filter]
  simp only [mem_univ, true_and, Snd.T4.encAt]
  rw [← foldAt4_f₀, ← foldAt4_f₁, ← encF_f₀, ← encF_f₁]
  exact ⟨fun h => ⟨by rw [h], by rw [h]⟩, fun h => K_ext' h.1 h.2⟩

/-- **The next message from level `i + 1`'s rows** (`i < 4`) at a 4.1 kind. -/
theorem nextMsg4_coords {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i + 1 < nLevels)
    (hF : ∀ r x, Snd.T4.msgOf κ L es (i + 1) r x = algebraMap F K (Snd.T4.msgOf κ L es (i + 1) r x).f₀)
    (x : ℕ) :
    Snd.T4.nextMsg κ L es i x = ⟨(Snd.T4.msgOf κ L es (i + 1) (2 * (x % 8)) (x / 8)).f₀,
      (Snd.T4.msgOf κ L es (i + 1) (2 * (x % 8) + 1) (x / 8)).f₀⟩ := by
  rw [Snd.T4.nextMsg, if_pos hi, hF (2 * (x % 8)), hF (2 * (x % 8) + 1), ofF_add_u_mul]
  rfl

/-- Level `i`'s agreement set as positions in `ℕ` (a 4.1 kind). -/
noncomputable def consN4 (κ : Snd.CKind) (L es : Log) (i : ℕ) : Finset ℕ :=
  (Snd.T4.consSet κ L es i).map Fin.valEmbedding

/-- Level `i`'s row `r` as an `ℕ`-indexed word (`0` past the positions). -/
def wordN4 (κ : Snd.CKind) (L es : Log) (i : ℕ) (r : Fin (Snd.CKind.lv κ i).rows) (j : ℕ) : F :=
  if hj : j < 2 ^ (Snd.CKind.lv κ i).logN then Snd.T4.wordOf κ L es i r ⟨j, hj⟩ else 0

theorem mem_consN4 {κ : Snd.CKind} {L es : Log} {i j : ℕ} :
    j ∈ consN4 κ L es i ↔ ∃ h : j < 2 ^ (Snd.CKind.lv κ i).logN, (⟨j, h⟩ : Fin _) ∈ Snd.T4.consSet κ L es i := by
  simp only [consN4, mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, hm⟩; exact ⟨_, hm, rfl⟩

/-- **One level's decoding at a 4.1 kind**: on a close word with `A_c = jointAgree`, interpolating
row `r` on the first `kᵢ` positions of `A_c` and running the `mLog` butterflies gives
`T4.msgOf κ L es i r` (in `K`). -/
theorem level_decode4 {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i))
    (r : Fin (Snd.CKind.lv κ i).rows) (x : Fin (2 ^ Snd.T4.mLog κ i)) :
    algebraMap F K (bflyRun (M := F) D logNMax 0 (Snd.T4.mLog κ i)
        (interpF D (firstK (2 ^ (Snd.CKind.lv κ i).logN) (consN4 κ L es i) (2 ^ Snd.T4.mLog κ i))
          (wordN4 κ L es i r)) x) = Snd.T4.msgOf κ L es i r x := by
  classical
  obtain ⟨hek, hN, hm, hk, hn⟩ := Snd.T4.lv_params κ hi
  have hnN : 2 ^ (Snd.CKind.lv κ i).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := Snd.T4.decodeL_spec hfar
  obtain ⟨c, hc⟩ := Snd.T4.exists_msg hi (hV r)
  rw [Snd.T4.msgOf_eq hi hc x, bflyRun_map]
  simp only [interpF_map]
  refine decode_agree hm hnN (fun j hj => (mem_consN4.1 hj).1) ?_ c _ (fun j hj => ?_) x
  · rw [consN4, card_map, hA]
    have : Snd.T4.lvK κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN - Snd.T4.lvE κ i := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  · obtain ⟨hj', hmem⟩ := mem_consN4.1 hj
    rw [hA, mem_jointAgree] at hmem
    have h1 := hmem r
    rw [Snd.T4.wordK] at h1
    simp only [wordN4, hj', dite_true]
    rw [h1, ← hc, enc_eq_encN]

/-- **The decoded messages are `F`-valued** (a 4.1 kind, close word, `A_c = jointAgree`). -/
theorem msgOf4_embed {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i)) (r x : ℕ) :
    Snd.T4.msgOf κ L es i r x = algebraMap F K (Snd.T4.msgOf κ L es i r x).f₀ := by
  by_cases hr : r < (Snd.CKind.lv κ i).rows
  swap
  · simp only [Snd.T4.msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ Snd.T4.mLog κ i
  swap
  · simp only [Snd.T4.msgOf, hr, hx, dite_true, dite_false]; rfl
  rw [← level_decode4 hi hfar hA ⟨r, hr⟩ ⟨x, hx⟩]
  rfl

end FR.X
