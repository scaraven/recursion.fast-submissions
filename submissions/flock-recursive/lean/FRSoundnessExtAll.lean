-- New for `flock-recursive` (BLUEPRINT A.10 cap₀, §5.1 `hExt`, §5.4, §6; stage S-N1).
import FRNodeSoundA
import FRSoundnessExtLeaf

/-!
# `ExtIfaceR` for the entry's statement

**`extIfaceR_of`**: the linked interface `ExtIfaceR` (`FRSoundnessExtR`) holds for
`St := Stmt (finC finPf) SLeaf`, the entry's extractor `X.E` and a verifier `Vwith impl
(sfFinals finP finPf)` with `ImplT impl`, given one hypothesis, the node circuit's residual:

* `hRes`: on a node chain, the statement `StmtN` gives `NodeResid` of `f⁽⁰⁾` (the parts of
  `SlotHolds` beyond the selector bits, and the two signatures; S-N1 findings O1, O2).

Everything else is discharged:
* the run's link gives `SkRun` (`skRun_of_accept`), the chain's kind is π's (`kindOf_chain`);
* a leaf kind: `E_leaf` and `rel_leaf_of_run` (`SLeaf`, the run's statement check);
* `N30`: `E_node_of_run` (every chain link from the run and `LigeritoOut`), then
  `rel_readWit` with `PubOK → PubCells`, `c_node_of_run`, `vkL_of_chain` and `truthLr`.

**`kstate_front_ofE`**: `kstate_front_ofR` with `extIfaceR_of` for the entry's verifier
(`VC finPf Layout.lRows κs₀`); its hypotheses are `kstate_front_of`'s without `ExtIface`, plus
`hRes` and the out-of-domain case `hOut` (finding O3).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

set_option linter.constructorNameAsVariable false

variable {oLc : Kind → Log → F → Prop} {RejN : Log → Log → Prop}

/-- **The seed's `vk` on the run's chain is the input's.** -/
theorem vkL_of_chain {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2) :
    vkL es = vk := by
  unfold vkL
  rw [seed_query hq]
  refine Vector.ext fun k hk => ?_
  rw [getElem_bytesAt _ _ _ _ hk, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]),
    show 7 + k - tagSeed.length = k by simp [tagSeed],
    List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
    Vector.getElem_toList]

/-- **`ExtIfaceR` for the entry's statement**, from the node circuit's residual. -/
theorem extIfaceR_of {impl : OpImpl} {S : Submission} {vk : Digest}
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (hV : S.V = Vwith impl (sfFinals finP finPf)) (hq : S.qV = qV) (hE : S.E = X.E)
    (hT : Circ.ImplT impl)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid impl (sfFinals finP finPf) (vkL es) (fF .N30 L es)) :
    ExtIfaceR impl (sfFinals finP finPf) S vk W₀ c₀ (Stmt (finC finPf) SLeaf) := by
  intro L c π j _ hb _ hR hD _ _ _ hSt hLig
  obtain ⟨k, tr, hk, hsem, hin, hes⟩ := hR
  obtain ⟨y, hsk⟩ := skRun_of_accept (sfFinals finP finPf) noAsk_sf hsem
  rw [hes] at hSt hLig
  have hkc := kindOf_chain hsk.hq hk
  rw [acc_eq impl _ S hV hq, hE]
  unfold Stmt at hSt
  rw [hkc] at hSt
  cases hkn : k.isNode
  · -- a leaf kind
    rw [if_neg (by simp [hkn])] at hSt
    have hkN : k ≠ .N30 := by rintro rfl; cases hkn
    exact ⟨_, X.E_leaf c π L hk hkN, rel_leaf_of_run hkn hk hsk _ hSt⟩
  · -- a node
    obtain rfl : k = .N30 := by cases k <;> simp_all [Kind.isNode]
    rw [if_pos (show Kind.N30.isNode = true from rfl)] at hSt
    obtain ⟨hZ, hS1, hLr, hEt, hPub⟩ := hSt
    have hp := pubCells_of_pubOK hPub
    rw [vkL_of_chain hsk.hq] at hp
    have hR := hRes L _ ⟨hZ, hS1, hLr, hEt, hPub⟩
    rw [vkL_of_chain hsk.hq] at hR
    exact ⟨_, E_node_of_run hsk hb hin hk hD hLig,
      rel_readWit hT hp (c_node_of_run hsk) hLr hR⟩

/-- **The knowledge state for the entry's verifier**, with `ExtIfaceR` discharged up to the node
circuit's residual `hRes` (and the out-of-domain case `hOut`, and the `W` proofs beyond the word
`hWB`, core PR #20). -/
noncomputable def kstate_front_ofE (S : Submission) (vk : Digest) (κs₀ : F)
    {L3N PendN : Log → Log → Prop}
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV) (hE : S.E = X.E)
    (hWB : WBeyond S vk)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) (vkL es)
        (fF .N30 L es))
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
  kstate_front_ofR S vk κs₀ hV hq (fun c π L hW hπ => hE ▸ X.ext_W c π L hW hπ) hWB
    (extIfaceR_of hV hq hE (implCWith_implT _ _) hRes) hOut hN hfit hStart hW0 hFrontV

/-! ## Controls -/

/-- Control (positive): the residual is only asked on node chains whose statement holds; on a
chain whose `PubOK` fails it is vacuous (`StmtN`'s last conjunct). -/
theorem hRes_vacuous {impl : OpImpl} {L es : Log} (h : ¬ PubOK .N30 L es) :
    StmtN (finC finPf) .N30 L es →
      NodeResid impl (sfFinals finP finPf) (vkL es) (fF .N30 L es) :=
  fun hS => absurd hS.2.2.2.2 h

end FR.Snd
