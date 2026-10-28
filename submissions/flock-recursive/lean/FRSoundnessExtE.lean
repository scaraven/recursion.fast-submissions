-- New for `flock-recursive` (BLUEPRINT §0.1 B-15, §10 changes 25 (2); stage S-H2n).
import FRSoundnessExtAll

/-!
# The knowledge state with the B-15 extractor: no `hOut`, no `hWB`

With `E := if InDomE then Ed else Eout` (B-15, `FRXExt`) and the search's acceptance the
submission's own (`S.E = X.E S.acc`), the two out-of-domain hypotheses of `kstate_front_ofE`
are theorems:

* **`wBeyond_E`**: `WBeyond S vk` (INT-6): `E` decodes every `W` proof, of any size
  (`FRXSpec.ext_W`), so `wBeyond_of_decode` applies.
* **`extIfaceE_of`**: the linked interface **without the domain** (`ExtIfaceE`, `ExtIfaceR`
  minus `InDom`). On the domain it is `extIfaceR_of`. Outside it, a leaf's `E` is still its
  denotation (`E_leaf`, domain-free); a node's `E` searches (`E_node_out`), and a witness
  exists by the same decode argument as on the domain, which uses no domain bound: `readWit` of
  the decoded `f⁽⁰⁾` is a witness (`rel_readWit`), and the proof carries the verifier's key
  (`vkOf_of_run`). This replaces `hOut` (S-N1 O3, S-H2m O3′): the 64-bit machine cannot read past
  tape word `2^64`, but `E` outside the domain is not the machine.
* **`hExt_of_ifaceE`**, **`finalLaw_ofE`**: `hExt_of_ifaceR`, `finalLaw_ofR` without the domain
  split (same proofs, the `InDom` argument and `hOut` dropped).
* **`kstate_front_ofE'`**: `kstate_front_ofE` without `hWB` and `hOut`; its hypotheses are
  `hRes` (the node circuit's residual, S-N1 O1/O2) and `kstate_front_of`'s front obligations.

Controls: `extIfaceE_false` (positive: a false statement asks nothing), `extIfaceE_W` (negative:
a `W` proof has no run link, so its `final` is `wBeyond_E`'s). `extIfaceR_of_E`: `ExtIfaceE`
implies S-N1's `ExtIfaceR`. `hE_of_accV`: `hE` holds for an extractor built from `accV`.
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

set_option linter.constructorNameAsVariable false

variable {oLc : Kind → Log → F → Prop} {RejN : Log → Log → Prop}

/-! ## `WBeyond` -/

/-- **`WBeyond` for the B-15 extractor**: `E` decodes every `W` proof, so every accepted `W`
proof of `2^64` bytes or more is extracted. -/
theorem wBeyond_E (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV) {A : Digest → Digest → Signed → Bool} (hE : S.E = X.E A) (vk : Digest) :
    WBeyond S vk :=
  wBeyond_of_decode impl fin S hV hq (fun c π L hW => hE ▸ X.ext_W A c π L hW) vk

/-! ## The interface without the domain -/

/-- **The extractor's interface, linked, on every log** (`ExtIfaceR` without `InDom`). -/
def ExtIfaceE (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (St : Log → Log → Prop) : Prop :=
  ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
    RunLink impl fin vk c π L j →
    IsChain L j → pfStart + 14 ≤ (entriesOf L (pathOf L j)).length →
    ¬ farL (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) 0 →
    St L (entriesOf L (pathOf L j)) → LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w

/-- `ExtIfaceE` gives `ExtIfaceR` (the domain is one more hypothesis). -/
theorem extIfaceR_of_E {impl : OpImpl} {fin : Finals} {S : Submission} {vk : Digest}
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {St : Log → Log → Prop}
    (h : ExtIfaceE impl fin S vk W₀ c₀ St) : ExtIfaceR impl fin S vk W₀ c₀ St :=
  fun L c π j hl hb hrun hR _ => h L c π j hl hb hrun hR

/-- **`ExtIfaceE` for the entry's statement and the B-15 extractor**, from the node circuit's
residual: on the domain `extIfaceR_of`; outside it a leaf by `E_leaf`, a node by `E_node_out`
with the decoded witness `readWit` (`rel_readWit`, no domain bound). -/
theorem extIfaceE_of {impl : OpImpl} {S : Submission} {vk : Digest}
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (hV : S.V = Vwith impl (sfFinals finP finPf)) (hq : S.qV = qV) (hE : S.E = X.E S.acc)
    (hT : Circ.ImplT impl)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid impl (sfFinals finP finPf) (vkL es) (fF .N30 L es)) :
    ExtIfaceE impl (sfFinals finP finPf) S vk W₀ c₀ (Stmt (finC finPf) SLeaf) := by
  intro L c π j hl hb hrun hR hc hlen hfar hSt hLig
  by_cases hD : InDom c π L
  · exact extIfaceR_of hV hq hE hT hRes L c π j hl hb hrun hR hD hc hlen hfar hSt hLig
  obtain ⟨k, tr, hk, hsem, hin, hes⟩ := hR
  obtain ⟨y, hsk⟩ := skRun_of_accept (sfFinals finP finPf) noAsk_sf hsem
  rw [hes] at hSt
  have hkc := kindOf_chain hsk.hq hk
  rw [hE]
  unfold Stmt at hSt
  rw [hkc] at hSt
  cases hkn : k.isNode
  · -- a leaf kind: `E` is the denotation on every log
    rw [if_neg (by simp [hkn])] at hSt
    have hkN : k ≠ .N30 := by rintro rfl; cases hkn
    rw [acc_eq impl _ S hV hq]
    exact ⟨_, X.E_leaf _ c π L hk hkN, rel_leaf_of_run hkn hk hsk _ hSt⟩
  · -- a node outside the domain: `E` searches, and the decoded witness exists
    obtain rfl : k = .N30 := by cases k <;> simp_all [Kind.isNode]
    rw [if_pos (show Kind.N30.isNode = true from rfl)] at hSt
    obtain ⟨hZ, hS1, hLr, hEt, hPub⟩ := hSt
    have hp := pubCells_of_pubOK hPub
    rw [vkL_of_chain hsk.hq] at hp
    have hRs := hRes L _ ⟨hZ, hS1, hLr, hEt, hPub⟩
    rw [vkL_of_chain hsk.hq] at hRs
    have hvk := vkOf_of_run hsk
    obtain ⟨w, hw, hRw⟩ := X.E_node_out S.acc c π L hk rfl (fun h => hD h.2)
      (fun _ _ h => X.sFits_of_acc (by rw [hq]; decide) h)
      ⟨_, by rw [hvk, acc_eq impl _ S hV hq]; exact rel_readWit hT hp (c_node_of_run hsk) hLr hRs⟩
    rw [hvk] at hRw
    exact ⟨w, hw, hRw⟩

/-! ## The route without the domain split -/

/-- **`hExt` from `ExtIfaceE`** (`hExt_of_ifaceR` without the domain). -/
theorem hExt_of_ifaceE {impl : OpImpl} {fin : Finals} {S : Submission} {vk : Digest}
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {St : Log → Log → Prop}
    {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} (hI : ExtIfaceE impl fin S vk W₀ c₀ St)
    (hSt : Reads 3 St) (hD2 : DF 2 = fun L es => farL (kindOf es) L es 0 ∨ ¬ St L es) :
    ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      RunLink impl fin vk c π L j → AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w := by
  intro L c π j hl hb hrun hR hT hnd hLig
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
  exact hI L c π j hl hb hrun hR hT.chain hlen (hLig.close 0 (by norm_num)) hst hLig

/-- **`finalLaw_ofR` without the domain split**: `hExt` covers every accepted run's chain. -/
theorem finalLaw_ofE (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {RejF : Log → Log → Prop}
    {DF : ℕ → Log → Log → Prop} (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF)
    (hAcc : ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨
        ∃ j, AcceptTail RejF W₀ c₀ L j ∧ RunLink impl fin vk c π L j)
    (hExt : ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      RunLink impl fin vk c π L j → AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) :
    FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀) := by
  intro L c π hl hμ hrun
  obtain ⟨hb, hE, hEH⟩ := muT_lt_one hμ
  rcases hAcc L c π hl hb hrun with hw | ⟨j, hT, hR⟩
  · exact hw
  have hS := chainStab_of hF hFS
  have hend := not_DC_end (DF := DF) hT
  have hp := pfStart_eq
  have hlen := hT.len
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  exact hExt L c π j hl hb hrun hR hT (fun p hp' => not_D_prefix hS hb hE hT.chain hend hp')
    (ligerito_final_of_walk hF hS hb hE hEH hT.chain (by omega) hend)

/-! ## The knowledge state -/

/-- **The knowledge state for the entry's verifier and the B-15 extractor** (`S.E = X.E S.acc`):
`kstate_front_ofE` without `hWB` (`wBeyond_E`) and `hOut` (`extIfaceE_of`). -/
noncomputable def kstate_front_ofE' (S : Submission) (vk : Digest) (κs₀ : F)
    {L3N PendN : Log → Log → Prop}
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV) (hE : S.E = X.E S.acc)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) (vkL es)
        (fF .N30 L es))
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
    (finalLaw_ofE (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) S vk frontLocal_W0
      (frontChainStab hN.toNodeLF)
      (hAcc_of_finR (implC (finC finPf) Layout.lRows κs₀) S vk hV hq
        (tensorW_implC _ _ _) (fun c π L hW _ => hE ▸ X.ext_W _ c π L hW)
        (wBeyond_E _ _ S hV hq hE vk) hStart hW0
        (fun k c π L tr j hb hπ hsem hin hci heq h =>
          (rejF_split h).elim (hFrontV k c π L tr j hb hπ hsem hin hci heq)
            (hN.front k c π L tr j hb hπ hsem hin hci heq)))
      (hExt_of_ifaceE (extIfaceE_of hV hq hE (implCWith_implT _ _) hRes)
        (stmt_reads _ sLeaf_reads) rfl))

/-! ## Controls -/

/-- Control (positive): the interface with a false statement holds (it asks for a witness only
where `St` holds). -/
theorem extIfaceE_false (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) :
    ExtIfaceE impl fin S vk W₀ c₀ fun _ _ => False :=
  fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.elim

/-- Control (negative, non-vacuous): a `W` proof has no run link, so `ExtIfaceE` asks nothing of
it; the `W` case of `final` is `wBeyond_E`'s and `ext_W`'s. -/
theorem extIfaceE_W {impl : OpImpl} {fin : Finals} {vk c : Digest} {π : Proof} {L : Log} {j : ℕ}
    (hW : FR.kindOf π = .W) : ¬ RunLink impl fin vk c π L j := not_runLink_W hW

/-- Control (positive, `hE` is satisfiable without self-reference): a submission whose extractor
searches with `accV impl fin` (no mention of `S`) meets `S.E = X.E S.acc` (`acc_eq`). -/
theorem hE_of_accV {impl : OpImpl} {fin : Finals} {S : Submission} (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV) (h : S.E = X.E (accV impl fin)) : S.E = X.E S.acc := by
  rw [acc_eq impl fin S hV hq]; exact h

end FR.Snd
