-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
import SpartanSromSoundnessChain
import SpartanSromChainEval
import SpartanSromNode

/-!
# The `final` law of the knowledge state (BLUEPRINT §5; v3 BLUEPRINT-R1 §9.3 `final`, L-K5)

`mu_final` is the `final` law of the library's potential `KState` (`Library/Security.lean`) for the
entry under a public key `vk`. The pieces are:

* the verifier `V LV vk` (`SpartanSromNode`), with `LV := Leaf.leafVerifier chainEvals`;
* the library's extractor `WitnessSending.E` (`decode π`);
* the relation `Rel (accV LV vk)` (the contract's `Rel (submission.acc vk)`, `accV_eq_acc`);
* the potential `KS.μ chainEvals` (v3's, unchanged: it is defined on logs, not on the verifier).

It holds for every key, every log with `μ L < 1` and every proof the verifier accepts reading its
answers from the log.

* **`snark_final`**: a SNARK verifier run that accepts on a log with `μ L < 1` proves its chain,
  `chainEnd s n = h` (v3's L-K4 `runLog_chain`, then L-K3 `accept_not_doomed` and
  `doom_of_not_esc` under `¬ Bad`, `¬ Esc`: `SoundnessFinal.chainEnd_of_runChain`). This is v3's
  leaf argument for one SNARK, now applied to the leaf branch `L` and to **every SNARK of a
  bundle**: the potential already covers every chain in the log, so a bundle of `k` SNARKs costs
  no more error than one.
* **`mu_final`**: `V_final` (`SpartanSromNode`) per branch: `L` as v3; `C` and `N` by their
  definitions; `B` by `snark_final` for each bundled leaf, then by induction on the clear tree
  (`clear_acc`).

The log-length guard of `KState.final` is not needed.
-/

namespace SpartanSrom.SoundnessKSFinal

open RecursionFast SoundnessChain

/-- The entry's leaf verifier: the SNARK with the chain R1CS's evaluators. -/
abbrev LV : LeafVerifier := Leaf.leafVerifier chainEvals

/-- **A SNARK verifier run accepting on a log with `μ L < 1` proves its chain.** -/
theorem snark_final {L : Log} (hμ : KS.μ chainEvals L < 1) (s : Digest) (n : ℕ) (h : Digest)
    (πS : ByteArray) (h1 : 1 ≤ n) (hcap : n ≤ chainCap) (hsz : πS.size = LV.size n - 80)
    (hrun : (LV.prog s n h πS).runLog L = some true) : chainEnd s n = h := by
  obtain ⟨hb, he⟩ := SoundnessFinal.not_bad_esc_of_mu chainEvals hμ
  have hsz' : Leaf.off₃ (Leaf.kap n) ≤ πS.size := by
    rw [hsz]
    simp only [LV, Leaf.leafVerifier, Leaf.leafSize, show n ≠ 0 by omega, ↓reduceIte]
    unfold Leaf.snarkSize Leaf.off₃ Leaf.off₂ Leaf.off₁ Ligero.size2
    omega
  exact SoundnessFinal.chainEnd_of_runChain chainEvals hb he
    (runLog_chain chainEvals hb h1 hcap hsz' hrun)

/-- **`mu_final`** (the library's `KState.final` for the entry under `vk`): on a log with
`μ L < 1`, every proof the verifier accepts reading its answers from the log is extracted by the
library's extractor to a witness of `Rel (accV LV vk)`. -/
theorem mu_final (vk : Digest) (L : Log) (c : Digest) (π : Proof) (_hl : L.length ≤ logCap)
    (hμ : KS.μ chainEvals L < 1) (hacc : (V LV vk c π).runLog L = some true) :
    ∃ w, WitnessSending.E c π L = some w ∧ Rel (accV LV vk) c w :=
  V_final (snark_final hμ) hacc

/-- `mu_final` with the binders in the order of `KState.final`. -/
theorem final_law (vk : Digest) : ∀ L c π, L.length ≤ logCap → KS.μ chainEvals L < 1 →
    (V LV vk c π).runLog L = some true →
    ∃ w, WitnessSending.E c π L = some w ∧ Rel (accV LV vk) c w :=
  mu_final vk

end SpartanSrom.SoundnessKSFinal
