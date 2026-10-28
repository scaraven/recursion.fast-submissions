-- New for `flock-recursive` (BLUEPRINT A.10 cap₀, §5.1 `hExt`, §5.4; stage S-N1).
import FRSoundnessFrK

/-!
# The extractor's interface with the run's link (`ExtIfaceR`), and the knowledge state from it

`ExtIface` (`FRSoundnessFrExt`) quantifies over **every** chain `j` of the log: nothing ties `j`
to the proof `π` the verifier accepted (S-N1 RESULT, finding O0). `hAcc_of_fin` does build
`AcceptTail L j` from the run's own chain (`runLog_chain`), with the run's trace `tr`, but
`finalLaw_of`'s `hAcc` keeps only `∃ j, AcceptTail …`. This module keeps the link:

* **`RunLink impl fin vk c π L j`**: `π` is a SNARK of kind `k`, the run on a trace `tr` of `L`'s
  entries accepts, and the chain of `j` is `tr`'s Fiat–Shamir entries.
* **`InDom c π L`**: the extractor's domain (contract `Computes`): every query below `2^64` bytes,
  the tape at most `2^64` words (finding O3).
* **`ExtIfaceR`**: `ExtIface` with `RunLink` and `InDom` as hypotheses.
* **`hAcc_of_finR`**, **`finalLaw_ofR`**, **`hExt_of_ifaceR`**, **`kstate_front_ofR`**: the same
  route as `hAcc_of_fin`, `finalLaw_of`, `hExt_of_iface`, `kstate_front_of`, keeping the link. The
  out-of-domain logs are a separate hypothesis `hOut`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

variable {oLc : Kind → Log → F → Prop} {RejN : Log → Log → Prop}

/-! ## The link and the domain -/

/-- **The run's link**: `π` is a SNARK of kind `k`, the verifier's program accepts it on a trace
`tr` whose entries are in `L`, and the chain of entry `j` is `tr`'s Fiat–Shamir entries. -/
def RunLink (impl : OpImpl) (fin : Finals) (vk c : Digest) (π : Proof) (L : Log) (j : ℕ) : Prop :=
  ∃ (k : Kind) (tr : Log), FR.kindOf π = .snark k ∧
    semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true ∧ (∀ e ∈ tr, e ∈ L) ∧
    entriesOf L (pathOf L j) = fsOf tr items

/-- **The extractor's domain** (contract `Computes`): queries below `2^64` bytes, the tape at most
`2^64` words. -/
def InDom (c : Digest) (π : Proof) (L : Log) : Prop :=
  (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64

/-- **The extractor's interface, linked** (`ExtIface` with the run's link and the domain). -/
def ExtIfaceR (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (St : Log → Log → Prop) : Prop :=
  ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
    RunLink impl fin vk c π L j → InDom c π L →
    IsChain L j → pfStart + 14 ≤ (entriesOf L (pathOf L j)).length →
    ¬ farL (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) 0 →
    St L (entriesOf L (pathOf L j)) → LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w

/-- `ExtIface` gives `ExtIfaceR` (the linked interface asks less). -/
theorem extIfaceR_of_iface {impl : OpImpl} {fin : Finals} {S : Submission} {vk : Digest}
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {St : Log → Log → Prop}
    (h : ExtIface S vk W₀ c₀ St) : ExtIfaceR impl fin S vk W₀ c₀ St :=
  fun L c π j hl hb hrun _ _ => h L c π j hl hb hrun

/-! ## The route, keeping the link -/

/-- **`hAcc_of_fin`, linked**: the `AcceptTail` comes with the run's link. -/
theorem hAcc_of_finR (impl : OpImpl) (S : Submission) (vk : Digest)
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
    (hFront : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ¬ RejF L (entriesOf L (pathOf L j))) :
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
    exact .inr ⟨j, acceptTail_of_finLog hb hci hlen (hFront k c π L tr j hb hπ hsem hin hci hes) hy,
      k, tr, hk, hsem, hin, hes⟩

/-- **`finalLaw_of`, linked**: `hAcc` keeps the run's link, `hExt` uses it on the extractor's
domain, and `hOut` covers the logs outside it. -/
theorem finalLaw_ofR (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {RejF : Log → Log → Prop}
    {DF : ℕ → Log → Log → Prop} (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF)
    (hAcc : ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨
        ∃ j, AcceptTail RejF W₀ c₀ L j ∧ RunLink impl fin vk c π L j)
    (hExt : ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      RunLink impl fin vk c π L j → InDom c π L → AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w)
    (hOut : ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      ¬ InDom c π L → ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) :
    FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀) := by
  intro L c π hl hμ hrun
  obtain ⟨hb, hE, hEH⟩ := muT_lt_one hμ
  by_cases hD : InDom c π L
  swap
  · exact hOut L c π hl hb hrun hD
  rcases hAcc L c π hl hb hrun with hw | ⟨j, hT, hR⟩
  · exact hw
  have hS := chainStab_of hF hFS
  have hend := not_DC_end (DF := DF) hT
  have hp := pfStart_eq
  have hlen := hT.len
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  exact hExt L c π j hl hb hrun hR hD hT (fun p hp' => not_D_prefix hS hb hE hT.chain hend hp')
    (ligerito_final_of_walk hF hS hb hE hEH hT.chain (by omega) hend)

/-- **`hExt` from the linked interface** (`hExt_of_iface` with the link and the domain). -/
theorem hExt_of_ifaceR {impl : OpImpl} {fin : Finals} {S : Submission} {vk : Digest}
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {St : Log → Log → Prop}
    {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} (hI : ExtIfaceR impl fin S vk W₀ c₀ St)
    (hSt : Reads 3 St) (hD2 : DF 2 = fun L es => farL (kindOf es) L es 0 ∨ ¬ St L es) :
    ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      RunLink impl fin vk c π L j → InDom c π L → AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w := by
  intro L c π j hl hb hrun hR hD hT hnd hLig
  have hlen := hT.len
  have hpf : 3 ≤ pfStart := by rw [pfStart_eq]; norm_num
  generalize hes : entriesOf L (pathOf L j) = es at hlen hnd hLig ⊢
  have h3 : (es.take 3).length = 3 := by simp; omega
  have hn := hnd 2 (by omega)
  simp only [DC, DPos, Dp, not_or, h3, show 3 - 1 = 2 from rfl, phOf_two,
    DkC_lt (show 2 < 26 by norm_num), hD2, not_not] at hn
  have hS : Same L es L (es.take 3) 3 := by
    have := same_append L (es.take 3) (es.drop 3)
    rwa [List.take_append_drop, h3] at this
  have hst : St L es := (hSt L es L (es.take 3) (by omega) (by omega) hS).mpr hn.2.2
  subst hes
  exact hI L c π j hl hb hrun hR hD hT.chain hlen (hLig.close 0 (by norm_num)) hst hLig

/-- **The knowledge state from the front, linked** (`kstate_front_of` with `ExtIfaceR` for
`ExtIface`, and `hOut` for the logs outside the extractor's domain). -/
noncomputable def kstate_front_ofR (S : Submission) (vk : Digest) (κs₀ : F)
    {L3N PendN : Log → Log → Prop}
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    (hWB : WBeyond S vk)
    (hI : ExtIfaceR (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) S vk W₀L c₀L
      (Stmt (finC finPf) SLeaf))
    (hOut : ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      ¬ InDom c π L → ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w)
    (hN : NodeL (implC (finC finPf) Layout.lRows κs₀) vk oLc RejN L3N PendN)
    (hfit : RowsFit (Layout.nodeRows (finC finPf)) 21 23)
    (hStart : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR (implC (finC finPf) Layout.lRows κs₀) (gen (sfFinals finP finPf) (.fixed k))
        ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) →
      refPhases (implC (finC finPf) Layout.lRows κs₀) k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀L L (fsOf tr items)))
    (hW0 : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR (implC (finC finPf) Layout.lRows κs₀) (gen (sfFinals finP finPf) (.fixed k))
        ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) →
      refPhases (implC (finC finPf) Layout.lRows κs₀) k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      ∀ (fi : FinIn) (r' : Array Val), fi.outs = skeleton.2.outs → ExtA (#[] ++ y.1.toArray) r' →
        w0V (implC (finC finPf) Layout.lRows κs₀) k fi r' = wHatL W₀L L (fsOf tr items) 0)
    (hFrontV : AccFront (implC (finC finPf) Layout.lRows κs₀) vk
      (RejF (finC finPf) oLc fun _ _ => False)) :
    KState (Rel (S.acc vk)) (S.V vk) S.E epsR :=
  kstate_of_front S vk (frontObl hN.toNodeLF hfit)
    (finalLaw_ofR (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) S vk frontLocal_W0
      (frontChainStab hN.toNodeLF)
      (hAcc_of_finR (implC (finC finPf) Layout.lRows κs₀) S vk hV hq
        (tensorW_implC _ _ _) hE hWB hStart hW0
        (fun k c π L tr j hb hπ hsem hin hci heq h =>
          (rejF_split h).elim (hFrontV k c π L tr j hb hπ hsem hin hci heq)
            (hN.front k c π L tr j hb hπ hsem hin hci heq)))
      (hExt_of_ifaceR hI (stmt_reads _ sLeaf_reads) rfl) hOut)

/-! ## Controls -/

/-- Control (positive): the linked interface with a false statement holds (it asks for a witness
only where `St` holds). -/
theorem extIfaceR_false (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) :
    ExtIfaceR impl fin S vk W₀ c₀ fun _ _ => False :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h _ => h.elim

/-- Control (negative, non-vacuous): a `W` proof has no run link (`RunLink` needs a SNARK). -/
theorem not_runLink_W {impl : OpImpl} {fin : Finals} {vk c : Digest} {π : Proof} {L : Log} {j : ℕ}
    (hW : FR.kindOf π = .W) : ¬ RunLink impl fin vk c π L j := by
  rintro ⟨k, tr, hk, -⟩; rw [hW] at hk; cases hk

/-- Control (positive): the empty log is in the domain of a small statement and proof. -/
theorem inDom_nil (c : Digest) : InDom c ByteArray.empty [] := by
  refine ⟨fun e he => absurd he List.not_mem_nil, ?_⟩
  simp [extractorInput, logWords, packBytes_length, bytesWords]

/-- Control (negative): a log with a query of `2^64` bytes or more is outside the domain. -/
theorem not_inDom_of_big {c : Digest} {π : Proof} {L : Log} {e : ByteArray × Digest} (he : e ∈ L)
    (hs : 2 ^ 64 ≤ e.1.size) : ¬ InDom c π L := fun h => absurd (h.1 e he) (by omega)

end FR.Snd
