-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
import SpartanSromSoundnessKS
import SpartanSromSoundnessKSFinal
import SpartanSromSnarkQueries

/-!
# The knowledge state and knowledge soundness of the entry (BLUEPRINT §5; v3 L-K5, L-K6)

For **every public key** `vk` (V4-1):

* **L-K5 `kstate vk`**: `KState (Rel (accV LV vk)) (V LV vk) WitnessSending.E 2^-129` with v3's
  potential `KS.μ chainEvals` (independent of `vk`), the laws `empty` (`KS.mu_empty`), `step`
  (`KS.mu_step_chain`, from `SpartanSromSoundnessKS`, unchanged) and `final`
  (`SoundnessKSFinal.final_law vk`).
* **L-K6 `ks vk`**: `KS (Rel (accV LV vk)) (V LV vk) WitnessSending.E 2^-129 2^16`: the knowledge
  state, and the query bound (`atMost_V` with `atMost_snarkProg` and v3's `qBound_le`).

`LV = Leaf.leafVerifier chainEvals`, `ε = 2^-129` (`KS.εKS`).
-/

namespace SpartanSrom.KS

open RecursionFast SoundnessKSFinal

/-- **L-K5 `kstate`**: the knowledge state of the entry under `vk`, with error `2^-129`. -/
noncomputable def kstate (vk : Digest) :
    KState (Rel (accV LV vk)) (V LV vk) WitnessSending.E εKS where
  μ := μ chainEvals
  empty := mu_empty chainEvals
  step := fun _ _ hl hμ hq => mu_step_chain hl hμ hq
  final := final_law vk

/-- The entry's SNARK asks at most `qBound (kap n)` queries along every path. -/
theorem atMost_leaf (s : Digest) (n : ℕ) (h : Digest) (π : ByteArray) (_ : n ≤ chainCap) :
    OProg.AtMost (LV.qb n) (LV.prog s n h π) :=
  atMost_snarkProg chainEvals s n h π

/-- `qBound (kap n) ≤ 2^14 ≤ 2^16` on every chain of at most `chainCap` steps (v3's L-Q1). -/
theorem qb_le (n : ℕ) (hn : n ≤ chainCap) : LV.qb n ≤ 2 ^ 16 :=
  (Leaf.qBound_le _ (Leaf.kap_le hn)).trans (by norm_num)

/-- **The query bound at the top level**: `V LV vk` asks at most `2^16` queries on every input
and oracle. -/
theorem V_queries_le (vk : Digest) (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((V LV vk c π).queries H).length ≤ 2 ^ 16 :=
  (atMost_V atMost_leaf qb_le vk c π).queries_length H

/-- **L-K6 `ks`**: knowledge soundness of the entry under every key,
`KS (Rel (accV LV vk)) (V LV vk) E 2^-129 2^16`. -/
theorem ks (vk : Digest) :
    RecursionFast.KS (Rel (accV LV vk)) (V LV vk) WitnessSending.E εKS (2 ^ 16) :=
  ⟨⟨kstate vk⟩, V_queries_le vk⟩

end SpartanSrom.KS
