-- New for `flock-recursive` (BLUEPRINT A.10, §5.1, B-14, B-15; revision 3.16; stage S-G12′, from
-- S-G11's draft `logs/S-G11/FRSoundnessFrKS.lean.draft`).
import FRSoundnessFrLc
import FRSoundnessExtE

/-!
# The 3.x knowledge state with `hStart`, `hW0` and the node's L discharged

`kstate_front_ofE'` (B-15, no `hOut`/`hWB`) with the front's run facts that are proved:

* `hStart` := `start_run`, `hW0` := `w0V_run` (`implC_meets`);
* the node's L: `nodeLF` (L3, L3β, claim 2's binding `oLcV`) with its accepted-run part, the
  node's `finLc` (ii) `RejLcN`, now proved (`accFrontK_rejLcN_C`, through the walk bridge).

`AccFront` quantifies over every program kind `k` without the proof's kind byte; the log's kind
`kindOf es` is the program's `k` only under `FR.kindOf π = .snark k` (`kindOf_fsQ`), which is how
`hAcc_of_finR` calls it. So the run facts are taken in the `AccFrontK` form, and
**`hAcc_of_finRK`** is `hAcc_of_finR` with that form (same proof, `hk` passed on).

**`kstate_front_K`**'s hypotheses are exactly: the verifier's form `hV`, `hq`; the B-15 extractor
`hE : S.E = X.E S.acc`; the node circuit's residual `hRes` (S-E's, S-N1 O1/O2); the M rows' fit
`hfit` (S-E's row counts); and the front's other checks on accepted runs, **`hFrontV`**
(`RejF … oLcV (fun _ _ => False)`: Z, L2, the leaf's Lc (ii) — proved here as
`accFrontK_rejLc2_C` —, S2, the ends, E4's rounds, `finE` (iv), RS0's bindings).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- **`hAcc_of_finR` with the kind byte** in the front's run facts (`AccFrontK`'s form). -/
theorem hAcc_of_finRK (impl : OpImpl) (S : Submission) (vk : Digest)
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {RejF : Log → Log → Prop}
    (hV : S.V = Vwith impl (sfFinals finP finPf)) (hq : S.qV = qV)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    (hWB : WBeyond S vk)
    (hStart : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀ L (fsOf tr items)))
    (hW0 : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      ∀ (fi : FinIn) (r' : Array Val), fi.outs = skeleton.2.outs → ExtA (#[] ++ y.1.toArray) r' →
        w0V impl k fi r' = wHatL W₀ L (fsOf tr items) 0)
    (hFront : AccFrontK impl vk RejF) :
    ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨
        ∃ j, AcceptTail RejF W₀ c₀ L j ∧ RunLink impl (sfFinals finP finPf) vk c π L j := by
  intro L c π _ hb hrun
  rcases hk : FR.kindOf π with _ | _ | k
  · exact .inl (acc_W_all impl _ S hV hq hE hWB hk hrun)
  · exact absurd (hV ▸ hrun) (not_acc_bad impl _ hk)
  · have hπ := size_of_snark hk
    rw [hV, V_snark impl _ vk c π hk] at hrun
    obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ := runLog_chain impl _ hb hπ hrun
    obtain ⟨y, hy⟩ := finLog_of_run ht hb hπ hk hsem hin
      (fun y hy' => hStart k c π L tr y hb hπ hk hsem hin hy')
      (fun y hy' => hW0 k c π L tr y hb hπ hk hsem hin hy')
    rw [← hes] at hy
    exact .inr ⟨j, acceptTail_of_finLog hb hci hlen (hFront k c π L tr j hb hπ hk hsem hin hci hes) hy,
      k, tr, hk, hsem, hin, hes⟩

/-- **The knowledge state for the 3.x verifier** (`VC finPf Layout.lRows κs₀`) and the B-15
extractor, with `hStart`, `hW0` and the node's L proved. Left: `hRes`, `hfit`, `hFrontV`. -/
noncomputable def kstate_front_K (S : Submission) (vk : Digest) (κs₀ : F)
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV) (hE : S.E = X.E S.acc)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) (vkL es)
        (fF .N30 L es))
    (hfit : RowsFit (Layout.nodeRows (finC finPf)) 21 23)
    (hFrontV : AccFrontK (implC (finC finPf) Layout.lRows κs₀) vk
      (RejF (finC finPf) oLcV fun _ _ => False)) :
    KState (Rel (S.acc vk)) (S.V vk) S.E epsR :=
  have hN := nodeLF (nsq nsq_mem.2.1)
  kstate_of_front S vk (frontObl hN hfit)
    (finalLaw_ofE (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) S vk frontLocal_W0
      (frontChainStab hN)
      (hAcc_of_finRK (implC (finC finPf) Layout.lRows κs₀) S vk hV hq
        (tensorW_implC _ _ _) (fun c π L hW _ => hE ▸ X.ext_W _ c π L hW)
        (wBeyond_E _ _ S hV hq hE vk)
        (fun k c π L tr y _ _ hk hsem _ hy =>
          start_run (fun r a hr => (implC_meets _ _ _).2.2.2.2.2.1 r a hr) vk k c π L tr y hk hsem hy)
        (w0V_run (fun r ps k β p hr hp => (implC_meets _ _ _).2.2.2.2.1 r ps k β p hr hp) vk)
        (fun k c π L tr j hb hπ hk hsem hin hci heq h =>
          (rejF_split h).elim (hFrontV k c π L tr j hb hπ hk hsem hin hci heq)
            (accFrontK_rejLcN_C κs₀ vk k c π L tr j hb hπ hk hsem hin hci heq)))
      (hExt_of_ifaceE (extIfaceE_of hV hq hE (implCWith_implT _ _) hRes)
        (stmt_reads _ sLeaf_reads) rfl))

/-- **Knowledge soundness at `εR`** (B-14: through `KState.ks`, the same `ε`), given the
verifier's query bound. -/
theorem ks_front_K (S : Submission) (vk : Digest) (κs₀ : F)
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV) (hE : S.E = X.E S.acc)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) (vkL es)
        (fF .N30 L es))
    (hfit : RowsFit (Layout.nodeRows (finC finPf)) 21 23)
    (hFrontV : AccFrontK (implC (finC finPf) Layout.lRows κs₀) vk
      (RejF (finC finPf) oLcV fun _ _ => False))
    (hQ : ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV) :
    KS (Rel (S.acc vk)) (S.V vk) S.E epsR S.qV :=
  (kstate_front_K S vk κs₀ hV hq hE hRes hfit hFrontV).ks hQ

end FR.Snd
