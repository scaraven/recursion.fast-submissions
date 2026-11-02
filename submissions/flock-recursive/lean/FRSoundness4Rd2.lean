-- New for `flock-recursive` (`flock-128`, design D128 §2.1, §5.4, §8 item 7; stage I5): the doom of
-- the degree-2 F rounds (L2, S2, E4) over the derived readers `g2dAt`/`clR2d` (I3), with the proof
-- of work at each round's squeeze.
import FRSoundness4TailStep
import FRSoundness128Rd

/-!
# The degree-2 F rounds' doom with `c₂` derived (`flock-128`)

A degree-2 F round sends `c₀ ‖ c₁ ‖ nonce`; the verifier derives `c₂ := claim + c₁` (I3,
`FRSoundness128Rd.g2dAt`), so the round check `g(0) + g(1) = claim` holds by construction
(`chk2d`) and no asserted check is left to put in `Rej`: the doom is the running claim alone, as for
the degree-3 rounds (`T4.D3`).

* **`D2d b c0 nr e T`**: past the phase's first absorb, the running claim `clR2d` after the answered
  rounds (`ans3`) is not the true sum of the tables bound at the round challenges (`rch`).
* **`D2d_append_iff`**, **`not_D2d_short`**, **`wrong2d_ext1`**, **`D2d_log_congr`**: the doom's
  reads (`T4.D3`'s, verbatim over `clR2d`).
* **`D2d_single_pow`**: at a round's squeeze, counting only answers that pass the proof of work there,
  at most `2·2^120` escape (`round_escape_le`, `card_chF_pow_fiber`); no check hypothesis
  (3.x's `D2_single` needed `Chk2` from `¬ Rej`).
* Controls: `D2d_first_absorb` (+), `not_D2d_before` (−).
-/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

section Rounds2d

variable (b : ℕ) (c0 : Log → Log → F) (nr : CKind → ℕ) (e : Expr)
  (T : Log → Log → Array (Array F))

/-- The claim after `l` rounds (derived `c₂`) is not the true sum of the bound tables. -/
def Wrong2d (L es : Log) (l : ℕ) : Prop :=
  clR2d b c0 L es l ≠ trueSum e (bindAll (T L es) (rchs b es l)) (nr (kindOfC es) - l)

/-- **The degree-2 rounds' doom** (`flock-128`): past the phase's first absorb, the running claim
after the answered rounds is false. -/
def D2d (L es : Log) : Prop := b < es.length ∧ Wrong2d b c0 nr e T L es (ans3 b nr es)

variable {b c0 nr e T}

/-- The claims read the log `L` only through `c0`, and the entries before round `l`. -/
theorem clR2d_same {L L' es es' : Log} (hc : c0 L es = c0 L' es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) → clR2d b c0 L es l = clR2d b c0 L' es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR2d]
    rw [clR2d_same hc (h.mono (by omega))]
    simp only [g2dAt, rch, fAt, ansAt, msgAt, h (b + 2 * l) (by omega), h (b + 2 * l + 1) (by omega)]

theorem wrong2d_congr (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) : Wrong2d b c0 nr e T L es l ↔ Wrong2d b c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong2d, clR2d_congr hc h, rchs_congr h, hT, kindOfC_congr (hb.mono hb1)]

/-- When the next position is not a real round's squeeze, appending keeps the doom. -/
theorem D2d_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOfC es) ≤ (es.length - b) / 2) :
    D2d b c0 nr e T L (es ++ [x]) ↔ D2d b c0 nr e T L es := by
  have hk := kindOf_append x (show 0 < es.length by omega)
  have ha : ans3 b nr (es ++ [x]) = ans3 b nr es := by
    simp only [ans3, hk, List.length_append, List.length_singleton]
    rcases hc with hc | hc
    · rw [show (es.length + 1 - b) / 2 = (es.length - b) / 2 by omega]
    · rw [min_eq_left hc, min_eq_left (le_trans hc (Nat.div_le_div_right (by omega)))]
  have hle : b + 2 * ans3 b nr es ≤ es.length := by
    have : ans3 b nr es ≤ (es.length - b) / 2 := min_le_right _ _
    omega
  simp only [D2d, ha, List.length_append, List.length_singleton]
  rw [wrong2d_congr hb1 hTc (agree_append es [x] hle)]
  exact ⟨fun h => ⟨hlen, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem not_D2d_short {L es : Log} (h : es.length ≤ b) : ¬ D2d b c0 nr e T L es :=
  fun hd => by have := hd.1; omega

/-- At a real round's squeeze, the extension answers one more round, its claim the derived round
polynomial at the answer's first F coordinate. -/
theorem wrong2d_ext1 (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (L es : Log) (a : Digest) {j : ℕ}
    (hj : es.length = b + 2 * j + 1) :
    Wrong2d b c0 nr e T L (ext1 es a) (j + 1) ↔
      peval (g2dAt b es j (clR2d b c0 L es j)) (chF a 0) ≠
        trueSum e ((bindAll (T L es) (rchs b es j)).map (bind0 · (chF a 0)))
          (nr (kindOfC es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOfC (ext1 es a) = kindOfC es := kindOf_append _ (by omega)
  have hr : rch b (ext1 es a) j = chF a 0 := by
    simp only [rch, fAt, ansAt]
    rw [← hj, entAt_ext1]
  obtain ⟨hT, hc0⟩ := hTc L (ext1 es a) es (hA.mono (by omega))
  have hcl : clR2d b c0 L (ext1 es a) j = clR2d b c0 L es j :=
    clR2d_congr (l := j) hc0 (hA.mono (by omega))
  have hg : g2dAt b (ext1 es a) j (clR2d b c0 L es j) = g2dAt b es j (clR2d b c0 L es j) := by
    simp only [g2dAt, msgAt, hA (b + 2 * j) (by omega)]
  have hrs : rchs b (ext1 es a) j = rchs b es j := rchs_congr (l := j) (hA.mono (by omega))
  simp only [Wrong2d, clR2d, hcl, hg, hr, rchs_succ, hrs, hT, hk, bindAll_append]

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **The degree-2 round row with the proof of work** (`flock-128`, D128 §5.4: L2, S2, E4):
counting only the answers with `Q`, where `Q` forces the proof of work at a real round's squeeze
(`hQ`), at most `2·2^120` answers make the next claim true. The round check is `chk2d`. -/
theorem D2d_single_pow (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (he : e.deg = 2)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOfC es)) (L es : Log) (Q : Digest → Prop)
    (hQ : ∀ j, es.length = b + 2 * j + 1 → j < nr (kindOfC es) → ∀ a, Q a → pow a) :
    (univ.filter fun a => D2d b c0 nr e T L es ∧ ¬ D2d b c0 nr e T L (ext1 es a) ∧ Q a).card ≤
      2 * 2 ^ 120 := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D2d_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOfC es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2.1 ((D2d_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOfC es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong2d b c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs b es j), t.size = 2 ^ (nr (kindOfC es) - j - 1 + 1) := by
    refine bindAll_size (rchs b es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs b es j)) hts
    (claim := clR2d b c0 L es j) (by
      rw [show nr (kindOfC es) - j - 1 + 1 = nr (kindOfC es) - j by omega]; exact hw)
    (g2dAt b es j (clR2d b c0 L es j))
  refine le_trans (Finset.card_le_card (t := univ.filter fun a : Digest => chF a 0 ∈ _ ∧ pow a)
    fun a ha => ?_) (by rw [card_chF_pow_fiber]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  rw [Finset.mem_filter] at ha
  have hnd : ¬ D2d b c0 nr e T L (ext1 es a) := ha.2.2.1
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOfC (ext1 es a) = kindOfC es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong2d b c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong2d_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨⟨by rw [he]; rfl, chk2d b es j _⟩, ?_⟩, hQ j hlj hj a ha.2.2.2⟩
  rw [hnw, show nr (kindOfC es) - (j + 1) = nr (kindOfC es) - j - 1 by omega]

theorem D2d_log_congr {L L' X : Log} (hT : T L' X = T L X) (hc : c0 L' X = c0 L X) :
    D2d b c0 nr e T L' X ↔ D2d b c0 nr e T L X := by
  have : ∀ l, clR2d b c0 L' X l = clR2d b c0 L X l := by
    intro l
    induction l with
    | zero => exact hc
    | succ l ih => simp only [clR2d, ih]
  simp only [D2d, Wrong2d, this, hT]

end Rounds2d

/-! ## Controls -/

/-- Control (positive): a false initial claim dooms the rounds at their first absorb. -/
theorem D2d_first_absorb (nr : CKind → ℕ) (L : Log) :
    D2d 15 (fun _ _ => 1) nr (.var 0) (fun _ _ => #[]) L (List.replicate 16 default) := by
  refine ⟨by simp, ?_⟩
  simp [Wrong2d, ans3, clR2d, trueSum, tbl, rchs, bindAll, Expr.eval]

/-- Control (negative): before the phase's first absorb nothing is doomed. -/
theorem not_D2d_before (nr : CKind → ℕ) (L : Log) (c0 : Log → Log → F)
    (T : Log → Log → Array (Array F)) (e : Expr) :
    ¬ D2d 15 c0 nr e T L (List.replicate 15 default) :=
  not_D2d_short (by simp)

end FR.Snd.T4

namespace FR.Snd
open RecursionFast Finset

set_option linter.constructorNameAsVariable false

/-! ## Single F squeezes with the proof of work (`flock-128`) -/

/-- **A batch of `k + 1` terms with the proof of work** (`batch_count` with `pow`): if some term is
false, at most `k·2^120` answers passing the proof of work make the batch true. -/
theorem batch_count_pow {k : ℕ} (P : Digest → Prop) [DecidablePred P] (v t : Fin (k + 1) → F)
    (hvt : v ≠ t)
    (h : ∀ a, P a → (∑ i, chF a 0 ^ i.val * v i = ∑ i, chF a 0 ^ i.val * t i) ∧ pow a) :
    (univ.filter P).card ≤ k * 2 ^ 120 := by
  classical
  refine le_trans (card_le_card (t := univ.filter fun a : Digest => chF a 0 ∈
    univ.filter (fun c : F => ∑ i, c ^ i.val * v i = ∑ i, c ^ i.val * t i) ∧ pow a)
    fun a ha => ?_) ?_
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact h a ha
  · rw [card_chF_pow_fiber]; exact Nat.mul_le_mul_right _ (batch_pow_bad_le hvt)

/-- **A single F squeeze with the proof of work**, the filter's instance from the context: at most
`s·2^120`. -/
theorem single_F_pow_le_dec (P : Digest → Prop) [DecidablePred P] (S : Finset F) {s : ℕ}
    (hS : S.card ≤ s) (h : ∀ a, P a → chF a 0 ∈ S ∧ pow a) : (univ.filter P).card ≤ s * 2 ^ 120 := by
  classical
  refine le_trans (card_le_card (t := univ.filter fun a : Digest => chF a 0 ∈ S ∧ pow a)
    fun a ha => ?_) ?_
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact h a ha
  · rw [card_chF_pow_fiber]; exact Nat.mul_le_mul_right _ hS

end FR.Snd
