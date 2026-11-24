-- New for lvm6 (WP N4-tail). The CC tail of `dec_of_runs`'s `htail`: the `J₀` bound on the stacked claims
-- and the ring phase (CC-5′ `ringPhaseHar`) as an `afterV` return on V1's values.
import Lvm6NodeChildOk
import Lvm6QCRing6

/-!
# The CC tail of `dec_of_runs` (WP N4-tail): `J₀` and the ring phase

* **`afterV_of_runsO`**: CC's `RunsO` (CB's `Runs` over the opening slots) on values without openings
  whose events match the slots gives an `afterV` return (`afterV_of_runs` for `OEv`).
* **The `J₀` bound**: the stacked claims of the tree (`toS`, 13), the sponge (`spS`, 30) and the typed
  phases (`claimsOnStack ∘ typedClaimsE`, 4 + the mini-bus's 3) with claim 0 are 51, and with the two
  slice sets 53 ≤ `J₀ = 1024` (`J0_P18`, `stacked_len`, `typed_len`). No value enters.
* **The ring phase**: `ringPhase_runs` is CC-5′ at `P18` at a memory, for every `sl`, `st` at once
  (inside one `HsA`); `ring_afterV` turns it into `afterV (ringPhase6 P18 sl st) vr = ret cl` with
  `RingPhRep` (the claim is `claimOf6` at the cells' maps and `λ₀`, the value cell holds its value);
  **`tail_ring`** does both at the represented outputs of tree, sponge and typed: the slice points'
  lengths (the outputs' shapes) give `ringOK`, the cells `svT`, `svS`, `vs` holding the slice values
  and the stacked values give `RingPhRep`.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open Lvm6.QK
open LeanVM.Parameters

/-! ## `RunsO → afterV` -/

/-- **A phase that `RunsO` on its slots returns on matching values** (no openings among them). -/
theorem afterV_of_runsO {β : Type} {M : Mem} {lay : List QC.OEv} {p : VerifierProgram β} {P : β → Prop}
    (h : QC.RunsO M lay p P) (hp : QC.PowLayO M lay) {vs : List V.Val} (hn : NoRows vs)
    (he : QC.OEvMatch M lay (vs.map toEv)) : ∃ out, afterV p vs = some (.ret out) ∧ P out := by
  obtain ⟨out, h1, h2⟩ := h hp _ he
  exact ⟨out, afterV_of_after p vs hn h1, h2⟩

/-! ## The `J₀` bound -/

theorem treeCols_length (κ : ℕ) (h : Digest) (out : K.TreeOut) : (K.treeCols κ h out).length = 13 := by
  simp [K.treeCols]

/-- The sponge phase's stacked claims: claims 16–45. -/
theorem spS_claims_length (os : K.SpOut) (lk : SP.LinkOut) : (SP.spS os lk).claims.length = 30 := by
  simp [SP.spS]

/-- The typed phases' stacked claims: the two `C_rec` claims, the two region claims and the mini-bus's
claims (three for `mbClaimsG`). -/
theorem typed_len (Ti : Lvm6.Ty.TInst6) (ry rv rr : List E2) (vR : E2) (cl : List Lvm6.Mb.ClaimE) :
    (Lvm6.Ty.claimsOnStack (Lvm6.Ty.typedClaimsE Ti ry rv rr vR cl)).length = 4 + cl.length := by
  simp [Lvm6.Ty.claimsOnStack, Lvm6.Ty.typedClaimsE]
  omega

theorem mbClaims_len (nu : ℕ) (tabs : List Lvm.M3.Tab) (b : Lvm6.Mb.LBusG) :
    ((Lvm6.Mb.mbClaimsG nu tabs b).map (·.onStack)).length = 3 := by
  simp [Lvm6.Mb.mbClaimsG]

theorem stacked_len (c0 : StackClaim6) (h : Digest) (ot : K.TreeOut) (os : K.SpOut) (lk : SP.LinkOut)
    (ty : List StackClaim6) : (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty).length = 44 + ty.length := by
  have e1 : (K.toS 19 h ot).claims.length = 13 := by
    simp only [K.toS, List.length_map]
    exact treeCols_length 19 h ot
  simp only [stackedOf, List.length_cons, List.length_append, e1, spS_claims_length]
  omega

theorem J0_eq : P18.J₀ = 1024 := rfl

/-- **The `J₀` bound at `P18`** for the represented outputs (any typed list of at most 7 claims). -/
theorem J0_P18 (c0 : StackClaim6) (h : Digest) (ot : K.TreeOut) (os : K.SpOut) (lk : SP.LinkOut)
    (ty : List StackClaim6) (hty : ty.length ≤ 7) :
    [(K.toS 19 h ot).slices, (SP.spS os lk).slices].length +
      (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty).length ≤ P18.J₀ := by
  rw [stacked_len, J0_eq, List.length_cons, List.length_cons, List.length_nil]
  omega

/-! ## The ring phase -/

/-- §6.5's static conditions at `P18` from the slice points' lengths. -/
theorem ringOK_P18 {sl : List SliceClaim} (h2 : sl.length = 2) (hpt : ∀ c ∈ sl, c.pt.length = 25) :
    ringOK P18 sl :=
  ⟨by decide, by decide, hpt, h2⟩

/-- **CC-5′ at `P18` at a memory**: where the ring gadget's rows and assertions hold, it re-executes
`ringPhase6 P18 sl st` for every `sl`, `st` meeting `ringOK` and the claim bound. -/
theorem ringPhase_runs {c : Ctx} {M : Mem} (svT svS vs : List C2) (a : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (QC.ringPhaseGen 17 svT svS vs a gate) fun o ↦ ∀ (sl : List SliceClaim) (st : List StackClaim6),
      ringOK P18 sl → st.length + 2 ≤ P18.J₀ →
      QC.RunsO M (QC.layRing6 17 a) (ringPhase6 P18 sl st) fun out ↦
        sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
          st.map (·.2) = vs.map (ev2 M) → QC.RingPhRep sl st M o out := by
  intro p hh ha sl st hok hJ
  exact QC.ringPhaseHar P18 sl st hok hJ svT svS vs a gate c M hg p hh ha

/-- **The ring phase returns on V1's values** (`RunsO → afterV` for CC-5′). -/
theorem ring_afterV {M : Mem} {o : QC.RingPhC} {svT svS vs : List C2} {a : ℕ} {sl : List SliceClaim}
    {st : List StackClaim6}
    (hR : QC.RunsO M (QC.layRing6 17 a) (ringPhase6 P18 sl st) fun out ↦
        sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
          st.map (·.2) = vs.map (ev2 M) → QC.RingPhRep sl st M o out)
    (hp : QC.PowLayO M (QC.layRing6 17 a)) {vr : List V.Val} (hn : NoRows vr)
    (he : QC.OEvMatch M (QC.layRing6 17 a) (vr.map toEv))
    (h1 : sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)])
    (h2 : st.map (·.2) = vs.map (ev2 M)) :
    ∃ cl, afterV (ringPhase6 P18 sl st) vr = some (.ret cl) ∧ QC.RingPhRep sl st M o cl := by
  obtain ⟨cl, hcl, hP⟩ := afterV_of_runsO hR hp hn he
  exact ⟨cl, hcl, hP h1 h2⟩

/-- **`htail`'s `J₀` bound and ring phase** at the represented outputs of tree (`ot`), sponge (`os`, `lk`)
and typed (`ty`, at most 7 claims): the gadget's run at the node's memory (`ringPhase_runs`), the slots'
grinds and events, the outputs' slice points of 25 coordinates, and the cells holding the slice values and
the stacked claims' values. -/
theorem tail_ring {M : Mem} {o : QC.RingPhC} {svT svS vs : List C2} {a : ℕ}
    (hR : ∀ (sl : List SliceClaim) (st : List StackClaim6), ringOK P18 sl → st.length + 2 ≤ P18.J₀ →
      QC.RunsO M (QC.layRing6 17 a) (ringPhase6 P18 sl st) fun out ↦
        sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
          st.map (·.2) = vs.map (ev2 M) → QC.RingPhRep sl st M o out)
    (hp : QC.PowLayO M (QC.layRing6 17 a)) {vr : List V.Val} (hn : NoRows vr)
    (he : QC.OEvMatch M (QC.layRing6 17 a) (vr.map toEv))
    (c0 : StackClaim6) (h : Digest) (ot : K.TreeOut) (os : K.SpOut) (lk : SP.LinkOut) (ty : List StackClaim6)
    (hty : ty.length ≤ 7) (hpt : ot.en.pt.length = 19 + 6) (hps : os.2.2.2.pt.length = 13 + 6)
    (h1 : [List.ofFn (K.toS 19 h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
      [svT.map (ev2 M), svS.map (ev2 M)])
    (h2 : (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty).map (·.2) = vs.map (ev2 M)) :
    [(K.toS 19 h ot).slices, (SP.spS os lk).slices].length +
        (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty).length ≤ P18.J₀ ∧
      ∃ cl, afterV (ringPhase6 P18 [(K.toS 19 h ot).slices, (SP.spS os lk).slices]
          (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty)) vr = some (.ret cl) ∧
        QC.RingPhRep [(K.toS 19 h ot).slices, (SP.spS os lk).slices]
          (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty) M o cl := by
  have hJ := J0_P18 c0 h ot os lk ty hty
  have hok : ringOK P18 [(K.toS 19 h ot).slices, (SP.spS os lk).slices] := by
    refine ringOK_P18 rfl fun c hc ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hpt
    · simp only [SP.spS, List.length_append, bitsF_length, hps]
  have hJ2 : (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) ty).length + 2 ≤ P18.J₀ := by
    rw [List.length_cons, List.length_cons, List.length_nil] at hJ
    omega
  exact ⟨hJ, ring_afterV (hR _ _ hok hJ2) hp hn he h1 h2⟩

end Lvm6.Node
