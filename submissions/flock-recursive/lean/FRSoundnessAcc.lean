-- New for `flock-recursive` (BLUEPRINT §5.4, A.10 "What `final` then gets"; stage S-G3).
import FRSoundnessAccFin
import FRXSpec

/-!
# `hAcc`: an accepted run is a `W` witness or an `AcceptTail`

`finalLaw_of`'s hypothesis `hAcc`, for a submission whose verifier is `Vwith impl fin`:

* the `W` branch is `acc_W_all` (`E` copies the proof below the word; `WBeyond` above it, a
  residual since core PR #20; `Rel` is what `V` decided);
* a `bad` proof is never accepted (`not_acc_bad`);
* a SNARK proof's accepted run on a log without bad events has a chain `j` whose entries are the
  run's Fiat–Shamir entries (`runLog_chain`); on it, the verifier's checks in log terms
  (`FinLog`) and the front's asserts (`¬ RejF`) give `AcceptTail` (`acceptTail_of_finLog`).

**`hAcc_of`** proves `hAcc` from two named obligations on the accepted trace, both about the run
semantics of the verifier's program:

* `hFin` (the tail side): the trace's registers, read on the log, satisfy `FinLog` for some
  column folds `y`;
* `hFront` (the front side): `¬ RejF` on the chain (`RejF` is the front's, not yet concrete).

**`finalLaw_of_run`** composes it with `finalLaw_of`: `FinalLaw` from `FrontLocal`,
`FrontChainStab`, `hFin`, `hFront` and `hExt`.
-/

namespace FR.Snd
open RecursionFast

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem size_of_snark {π : Proof} {k : Kind} (h : FR.kindOf π = .snark k) : π.size = piSize := by
  unfold FR.kindOf at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- **`hAcc` from the run obligations** (`finalLaw_of`'s hypothesis, for `V = Vwith impl fin`).
`hFin` and `hFront` are asked on every accepted SNARK trace whose entries are in a log without
bad events, on the chain of the run's Fiat–Shamir entries. -/
theorem hAcc_of (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    {RejF : Log → Log → Prop} (hV : S.V = Vwith impl fin) (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    (hWB : WBeyond S vk)
    (hFin : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ∃ y, FinLog W₀ c₀ L (entriesOf L (pathOf L j)) y)
    (hFront : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ¬ RejF L (entriesOf L (pathOf L j))) :
    ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨ ∃ j, AcceptTail RejF W₀ c₀ L j := by
  intro L c π _ hb hrun
  rcases hk : FR.kindOf π with _ | _ | k
  · exact .inl (acc_W_all impl fin S hV hq hE hWB hk hrun)
  · exact absurd (hV ▸ hrun) (not_acc_bad impl fin hk)
  · have hπ := size_of_snark hk
    rw [hV, V_snark impl fin vk c π hk] at hrun
    obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ := runLog_chain impl fin hb hπ hrun
    obtain ⟨y, hy⟩ := hFin k c π L tr j hb hπ hsem hin hci hes
    exact .inr ⟨j, acceptTail_of_finLog hb hci hlen
      (hFront k c π L tr j hb hπ hsem hin hci hes) hy⟩

/-- `hAcc_of` with the entry's extractor `E` (`FRXSpec.ext_W`). -/
theorem hAcc_of_E (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    {RejF : Log → Log → Prop} (hV : S.V = Vwith impl fin) (hq : S.qV = qV) {A : Digest → Digest → Signed → Bool}
    (hE : S.E = X.E A)
    (hWB : WBeyond S vk)
    (hFin : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ∃ y, FinLog W₀ c₀ L (entriesOf L (pathOf L j)) y)
    (hFront : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ¬ RejF L (entriesOf L (pathOf L j))) :
    ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨ ∃ j, AcceptTail RejF W₀ c₀ L j :=
  hAcc_of impl fin S vk hV hq (fun c π L hW _ => hE ▸ X.ext_W A c π L hW) hWB hFin hFront

/-- **`FinalLaw` from the run obligations**: `finalLaw_of` with `hAcc := hAcc_of`. What is left
for `kstate` (with `kstate_of_front`): `FrontObl`, `FrontChainStab`, `hFin`, `hFront`, `hExt`. -/
theorem finalLaw_of_run (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop}
    (hV : S.V = Vwith impl fin) (hq : S.qV = qV) {A : Digest → Digest → Signed → Bool}
    (hE : S.E = X.E A) (hWB : WBeyond S vk)
    (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF)
    (hFin : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ∃ y, FinLog W₀ c₀ L (entriesOf L (pathOf L j)) y)
    (hFront : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ¬ RejF L (entriesOf L (pathOf L j)))
    (hExt : ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) :
    FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀) :=
  finalLaw_of S vk hF hFS (hAcc_of_E impl fin S vk hV hq hE hWB hFin hFront) hExt

end FR.Snd
