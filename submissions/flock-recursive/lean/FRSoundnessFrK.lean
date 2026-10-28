-- New for `flock-recursive` (BLUEPRINT A.10, §5.1; stage S-G9).
import FRSoundnessFrObl
import FRSoundnessAccLog

/-!
# The knowledge state from the front

* **`AccFront impl vk R`**: on every accepted run of the verifier, the check `R` holds on the
  run's chain (`hAcc_of_fin`'s `hFront` form).
* **`NodeL`**: the node's L as one hypothesis (`NodeLF` and the accepted run's part `front`).
* **`kstate_front_of`**: the knowledge state at `εR` for a submission whose verifier is
  `VC finPf Layout.lRows κs₀`, from `ExtIface` (with `Stmt … SLeaf`), `NodeL`, the M rows' fit,
  and the run facts `hStart`, `hW0`, `hFrontV` (S-G5 §5 items 8–10; not yet discharged, see the
  RESULT's handover).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- **A check holds on every accepted run's chain** (`hAcc_of_fin`'s `hFront` form). -/
def AccFront (impl : OpImpl) (vk : Digest) (R : Log → Log → Prop) : Prop :=
  ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
    π.size = piSize → semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
    (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
    ¬ R L (entriesOf L (pathOf L j))

/-- **The node's L** (one hypothesis; blueprint 3.16, INT-5): `NodeLF` and, on every accepted
run, its checks `RejN` hold. -/
structure NodeL (impl : OpImpl) (vk : Digest) (oLc : Kind → Log → F → Prop)
    (RejN L3N PendN : Log → Log → Prop) : Prop extends NodeLF oLc RejN L3N PendN where
  front : AccFront impl vk RejN

variable {fin : Finals} {oLc : Kind → Log → F → Prop} {RejN : Log → Log → Prop} {L es : Log}

theorem rejF_split (h : RejF fin oLc RejN L es) :
    RejF fin oLc (fun _ _ => False) L es ∨ RejN L es := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inr h

/-- **The knowledge state at `εR` from the front.** The verifier is `VC finPf Layout.lRows κs₀`
(`Vwith implC finC`). What is left: the extractor's interface `ExtIface` with the statement
`Stmt (finC finPf) SLeaf`, the node's L (`NodeL`), the M rows' fit (S-E's row counts), the
extractor's `W` branch (`hE`), and the front's run facts `hStart`, `hW0`, `hFrontV`. -/
noncomputable def kstate_front_of (S : Submission) (vk : Digest) (κs₀ : F)
    {L3N PendN : Log → Log → Prop}
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    (hI : ExtIface S vk W₀L c₀L (Stmt (finC finPf) SLeaf))
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
    (finalLaw_of S vk frontLocal_W0 (frontChainStab hN.toNodeLF)
      (hAcc_of_fin (implC (finC finPf) Layout.lRows κs₀) S vk hV hq
        (tensorW_implC _ _ _) hE hStart hW0
        (fun k c π L tr j hb hπ hsem hin hci heq h =>
          (rejF_split h).elim (hFrontV k c π L tr j hb hπ hsem hin hci heq)
            (hN.front k c π L tr j hb hπ hsem hin hci heq)))
      (hExt_of_iface hI (stmt_reads _ sLeaf_reads) rfl))

/-! ## Controls -/

/-- Control (positive): the empty check holds on every accepted run. -/
theorem accFront_false (impl : OpImpl) (vk : Digest) : AccFront impl vk fun _ _ => False :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => h

/-- Control (positive, satisfiability): `NodeL` is met (`nodeLF_ex` with no checks). -/
theorem nodeL_ex (impl : OpImpl) (vk : Digest) :
    NodeL impl vk (fun κ es v => κ.isNode = false ∧ v = vBetaL es) (fun _ _ => False)
      (fun _ es => (kindOf es).isNode = true ∧ 97 < es.length)
      (fun _ es => (kindOf es).isNode = true ∧ 98 < es.length) :=
  { nodeLF_ex with front := accFront_false impl vk }

/-- Control (negative): a binding that accepts everything is no `NodeL`. -/
theorem not_nodeL_true (impl : OpImpl) (vk : Digest) {L3N PendN : Log → Log → Prop} :
    ¬ NodeL impl vk (fun _ _ _ => True) RejN L3N PendN := fun h => not_nodeLF_true h.toNodeLF

end FR.Snd
