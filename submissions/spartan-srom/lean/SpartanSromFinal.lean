-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
import SpartanSromSubmission
import SpartanSromSoundnessKState
import SpartanSromChainHonest

/-!
# The final instantiation of the entry, and its certificate (BLUEPRINT §4, §5)

The parameters of `SpartanSromSubmission`:

* `leafVerifier := Leaf.leafVerifier chainEvals`: the leaf SNARK verifier with the chain R1CS's
  evaluators and the query bound `qBound (kap n)` (`SpartanSromVerifier`, `SpartanSromChainEval`);
* `proveLeafR1 s n _ := Leaf.proveSnark chainWf s n`: the SNARK prover with the chain's tables
  (`SpartanSromProver`, `SpartanSromChainHonest`);
* `facts : Facts leafVerifier proveLeafR1`:
  * `size_zero`: `leafSize 0 = 80`;
  * `leaf_complete`: `snark_size` and `snark_complete` with `chainHonest : HonestOps chainEvals
    chainWf`;
  * `ks`: L-K5 `KS.kstate vk` (`ε = 2^-129`, v3's `εKS`, equal to `εR1`), for every key;
  * `atMost`, `qb_le`: `atMost_snarkProg` and L-Q1 `Leaf.qBound_le`.

**`SpartanSrom.certificate : Certificate SpartanSrom.submission`** is the entry's closed
certificate (no hypothesis); `Solution.lean` binds it to the rendered claim.
-/

namespace SpartanSrom

open RecursionFast

/-- The entry's leaf verifier. -/
abbrev leafVerifier : LeafVerifier := Leaf.leafVerifier chainEvals

/-- The entry's SNARK prover (`h = chainEnd s n` is recomputed by `proveSnark`). -/
def proveLeafR1 (s : Digest) (n : ℕ) (_h : Digest) : OProg ByteArray := Leaf.proveSnark chainWf s n

/-- **The facts** the certificate needs. -/
theorem facts : Facts leafVerifier proveLeafR1 where
  size_zero := rfl
  leaf_complete H s n h1 h2 := by
    refine ⟨?_, ?_⟩
    · show 80 + ((Leaf.proveSnark chainWf s n).run H).size = Leaf.leafSize n
      rw [Leaf.snark_size, Leaf.leafSize, ite_eq_right (by omega)]
    · exact Leaf.snark_complete chainEv chainWf chainHonest H s h1 h2
  ks vk := ⟨(KS.kstate vk).mono (le_of_eq εR1_eq.symm)⟩
  atMost := KS.atMost_leaf
  qb_le := KS.qb_le

/-- **The entry's submission**: `V` with branches `L`, `C`, `N`, `B` over the Spartan–Ligero
leaf SNARK, the Lean honest prover, the library's copy extractor; `ε = 2^-129`, `δ = 0`,
`qV = 2^16`, fuel `8 t`. -/
def submission : Submission := submissionOf leafVerifier proveLeafR1

/-- **The entry's certificate** (closed): knowledge soundness and completeness for every public
key, the extractor program, and the caps. -/
theorem certificate : Certificate submission := certificateOf facts

end SpartanSrom
