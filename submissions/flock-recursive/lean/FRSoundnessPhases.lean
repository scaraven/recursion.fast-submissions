-- New for `flock-recursive` (BLUEPRINT A.10 L1, L3, Lr3, E3, B′; stage S-G1h, item 3 begun).
import FRSoundnessWalk

/-!
# Per-phase obligations, part 1: the single-squeeze batching rows (A.10)

Five phases start with one squeeze that batches claims already on the chain by powers of a fresh
F challenge: L1 (`α`, 2 claims), L3 (`β`, 8 `v_kind`), Lr3 (`κ_L`, 3), E3 (`κ_E`, 3), B′ (`κ′`,
`J_f` terms). Their doom after the squeeze is "the batched claim is false"; before it, "some
claim is false". **`batch_single`**: at such a squeeze at most `k·2^128` answers escape
(`batch_pow_bad_le`, `single_F_le`); **`batch_N_le`**: every such count (`k ≤ 239`) fits
`PhaseObl`'s single-squeeze budget `N ≤ 2^256·deltaR`. This discharges `PhaseObl.hsingle` at these
five positions once the phases' claims and truths are fixed (the rest of item 3, S-G1h RESULT).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

open Classical in
/-- **A single-squeeze batching row** (A.10 L1, L3, Lr3, E3, B′): if the doom before the squeeze
means some of the `k + 1` claims `v` differs from its truth `t`, and the doom after it fails only
when the batch `Σ_i κ^i v_i` at the answer's first F coordinate `κ` equals the true batch, then at
most `k·2^128` answers escape. -/
theorem batch_single {k : ℕ} (D : Log → Log → Prop) (v t : Fin (k + 1) → F) (L es : Log)
    (hpre : D L es → v ≠ t)
    (hpost : ∀ a, D L es → ¬ D L (ext1 es a) →
      ∑ i, chF a 0 ^ i.val * v i = ∑ i, chF a 0 ^ i.val * t i) :
    (univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ k * 2 ^ 128 := by
  by_cases hD : D L es
  · have hS := batch_pow_bad_le (R := F) (hpre hD)
    convert single_F_le (fun a => D L es ∧ ¬ D L (ext1 es a)) _ hS fun a ha =>
      mem_filter.mpr ⟨mem_univ _, hpost a ha.1 ha.2⟩ using 2
    ext a; simp
  · rw [filter_false_of_mem fun a _ ha => hD ha.1]; simp

/-- Every batching count fits the single-squeeze budget (`k ≤ 239`; A.10's largest is B′'s
`J_f − 1 ≤ 20`). -/
theorem batch_N_le {k : ℕ} (hk : k ≤ 239) : ((k * 2 ^ 128 : ℕ) : ℝ≥0) ≤ 2 ^ 256 * deltaR := by
  have h := coord_le_deltaR hk
  rw [div_le_iff₀ (by positivity)] at h
  calc ((k * 2 ^ 128 : ℕ) : ℝ≥0) = (k : ℝ≥0) * 2 ^ 128 := by push_cast; ring
    _ ≤ deltaR * 2 ^ 128 * 2 ^ 128 := by gcongr
    _ = 2 ^ 256 * deltaR := by ring

/-- Control (positive): with all claims true nothing is doomed, so nothing escapes. -/
theorem batch_single_true {k : ℕ} (v : Fin (k + 1) → F) (L es : Log) :
    (univ.filter fun a => (fun (_ _ : Log) => v ≠ v) L es ∧
      ¬ (fun (_ _ : Log) => v ≠ v) L (ext1 es a)).card = 0 := by
  simp

end FR.Snd
