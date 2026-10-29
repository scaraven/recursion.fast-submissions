-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4; stage S-G1g, the frame of S-G2's `kstate`).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessHide
import RecursionFast.Contract.Certificate
import RecursionFast.Library.PaperTheorem
import FRSoundnessCoreRows

/-!
# The knowledge state `kstate vk` (frame; `final` is S-G2's)

The library's `KState (Rel (S.acc vk)) (S.V vk) S.E ε` (`RecursionFast.Library.Security`; core
PR #19 moved it out of the contract) for the entry's potential
`muT Rej Dk = μ_doom + μ_Hide` (`FRSoundnessHide`) at `ε = εR = 15/2^124`:

* `empty`: `muT_empty`;
* `step`: `muT_step`, from `PhaseObl Rej Dk N` and `N ≤ 2^256·deltaR` (the per-phase obligations
  of the concrete doom, A.10);
* `final`: a hypothesis, **`FinalLaw S vk Rej Dk`**, exactly the contract's `final` law for
  `muT Rej Dk`. Below `1`, `muT_lt_one` gives it `¬ Bad L`, no escape of the doom potential and no
  escape of the Hide potential; S-G2 proves it from `ligerito_final` and `leaf_sound` /
  `node_sound` for the concrete `Rej`, `Dk`.

**`kstate_of`** builds the knowledge state from these; **`ks_of`** adds the verifier's query bound
and turns it into the contract's textbook `KS` at the same `ε` through the library bridge
`KState.ks` (`RecursionFast.Library.PaperTheorem`, BLUEPRINT B-14).
-/

namespace FR.Snd
open RecursionFast
open scoped NNReal

/-- **What `final` must prove** (the library's `KState.final` for `muT Rej Dk`): on a log within
`logCap` whose potential is below `1`, every proof the verifier accepts on the log's answers is
extracted to a witness of `Rel (S.acc vk)`. -/
def FinalLaw (S : Submission) (vk : Digest) (Rej : Log → Log → Prop)
    (Dk : ℕ → Log → Log → Prop) : Prop :=
  ∀ L c π, L.length ≤ logCap → muT Rej Dk L < 1 → (S.V vk c π).runLog L = some true →
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w

/-- **The knowledge state at `εR`** from the per-phase obligations and the `final` law. -/
noncomputable def kstate_of (S : Submission) (vk : Digest) {Rej : Log → Log → Prop}
    {Dk : ℕ → Log → Log → Prop} {N : ℕ} (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR)
    (ob : PhaseObl Rej Dk N) (hfin : FinalLaw S vk Rej Dk) :
    KState (Rel (S.acc vk)) (S.V vk) S.E epsR where
  μ := muT Rej Dk
  empty := muT_empty Rej Dk
  step L q hl hμ hq := muT_step hN ob L q hl hμ hq
  final := hfin

/-- **Knowledge soundness at `εR`** under one key, given the verifier's query bound: the knowledge
state through `KState.ks` (B-14). -/
theorem ks_of (S : Submission) (vk : Digest) {Rej : Log → Log → Prop}
    {Dk : ℕ → Log → Log → Prop} {N : ℕ} (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR)
    (ob : PhaseObl Rej Dk N) (hfin : FinalLaw S vk Rej Dk)
    (hq : ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV) :
    KS (Rel (S.acc vk)) (S.V vk) S.E epsR S.qV :=
  (kstate_of S vk hN ob hfin).ks hq

end FR.Snd
