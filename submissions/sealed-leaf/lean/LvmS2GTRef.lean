-- New for lvm2 S2GT (GT-L3): S2GT-STMT 7 (`refinesG20`, moved here from `LvmS2GTStmtV` with its text unchanged, lead
-- approved): `VSGX N` refines the compiled verifier of S2GT's pinned middle phases at `fmtG20` (`refinesF20`'s proof
-- at `P20T`: `refines_seqOfG` with `ref_decideG` at `k = 4`).
import LvmS2GTClaims
import LvmS2GTStmtV
import LvmS2GTFol
import LvmE2VDecRef
import LvmE2VTopF

/-!
# S2GT-STMT 7: `refinesG20`

* `fe16At_congr`, `pubG_eq`: V_S's S2GT public values (16-B `acc_in` scalars) are the statement's (`pubOfW_eq`).
* `decideFGX_ok`: `decideFGX` holds ⇒ the run's checks held and `Φ_Q` at `E2` holds on the folded accumulator.
* `dTypedT_m3G`: the typed phases on the S2GT mini-bus instance (`m3G`, `PUB` on the 2-lane header) are those on the
  record's (`dMiniT` reads only the bus's forms and tables).
* `ref_decideGT`: V_S's S2GT decision refines the pinned middle phases (`ref_decideG` at `k = 4`, `P20T`, with
  `ref_dTypedT` and `claimsT_rel`).
* **`refinesG20`**.
-/

set_option autoImplicit false

namespace Lvm.E2T

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.CT Lvm.E2F Lvm.E2V Lvm.VEq LeanVM.Protocol.Compile
open Lvm.Typed (Lay PhiQFT phiVarsT)

/-! ## The public values and the decision -/

/-- **V_S's S2GT public values are the statement's** (16-B `acc_in` scalars; the stream holds the header bytes). -/
theorem pubG_eq {vk c : Digest} {π : ByteArray} (h : parseOk P20T vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytesP P20T - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubG vk c sig = pubXT (xOfH (headerBytesP P20T) π) :=
  pubOfW_eq h fe16At 16 accVT (fun _ _ _ h ↦ fe16At_congr h) (hdrFix_le_P _)
    (by rw [headerBytesP_P20T.1]; decide) hsig

/-- `StateT.run` restated with a non-`rfl` proof (proof help: a `rw` step, not a kernel defeq through the program). -/
private theorem stRunG {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

/-- `decideFGX` holds: the run's checks held and its folded claim passes `Φ_Q` at `E2`. -/
theorem decideFGX_ok {N : TNatT} {vk c : Digest} {sig : ByteArray} (h : decideFGX N vk c sig = true) :
    (runD (decideProgG N vk c) sig (RS.startH (headerBytesP P20T))).2.ok = true ∧
      N.phiT ((runD (decideProgG N vk c) sig (RS.startH (headerBytesP P20T))).1.pt.map Lvm.e2OfFE) =
        Lvm.e2OfFE (runD (decideProgG N vk c) sig (RS.startH (headerBytesP P20T))).1.y := by
  -- `delta` on the bare constant and a non-`rfl` `StateT.run` step: `unfold … at h` and a closing `rfl` left the
  -- kernel a check that ran `decideProgG` symbolically (8.4 M hb)
  have eD : @decideFGX = @decideFGX := rfl
  conv at eD => rhs; delta decideFGX
  rw [eD] at h
  beta_reduce at h
  have e : DM.runOnH (headerBytesP P20T) (decideProgG N vk c) sig =
      runD (decideProgG N vk c) sig (RS.startH (headerBytesP P20T)) := by rw [DM.runOnH, stRunG]
  rw [e] at h
  rcases hr : runD (decideProgG N vk c) sig (RS.startH (headerBytesP P20T)) with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, fe2_beq h.2⟩

/-- **The typed phases on S2GT's mini-bus instance are those on the record's** (`m3G` differs from `N.toN.m3` only
in `PUB`'s check, which `dMiniT` does not read). -/
theorem dTypedT_m3G (N : TNatT) (pub : Pub) :
    dTypedT P20 N (m3G N P20T) pub = dTypedT P20 N (N.toN.m3 P20) pub := by
  unfold dTypedT dTypedTG
  rw [dMiniT_congr P20 P20 (m3G N P20T) (N.toN.m3 P20) N.mbT pub rfl rfl rfl rfl rfl]

/-! ## The decision refines the pinned middle phases -/

/-- **V_S's S2GT decision refines the pinned middle phases on the stream with S2GT's read widths** under the promise
that its value passes `Φ_Q` at `E2` (`ref_decideG` at `k = 4`, `P20T`). -/
theorem ref_decideGT (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay)
    (hσ : Lvm.TypedV.SigInS N.toN) (sig : ByteArray) (vk c : Digest) (x : List UInt8)
    (hpub : pubG vk c sig = pubXT x) :
    RefAtPW capS occS shpS rwG20 sig 0 (decideProgG N vk c)
      (PSWithM (midP (midMk 4 reloc20 (midGT (N.inst Q lay)))) x) (fun _ b ↦ b = true)
      (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y)
      (wDecF (atomsOf P20T (typedIT P20T)) (atomsOf P20 (openMainI P20))).length := by
  have hw : WAt rwG20 0 (wDecF (atomsOf P20T (typedIT P20T)) (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwG20
    rw [widthsA_scheduleT] at h
    exact h
  have hw' := hw
  rw [wDecF, WAt.append, WAt.append, WAt.append, widthsA_typedIT] at hw'
  obtain ⟨⟨⟨-, hwT⟩, -⟩, -⟩ := hw'
  have hacc : (pubXT x).accIn.pt.length = phiVarsT := length_pubOfW _ _ _ _ _ _
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.toT.sc_eq
  have hs : sBitsD (pubXT x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXT x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  rw [decideProgG_eq]
  exact ref_decideG 4 P20T pubG contRowsT (fun m pub ↦ dTypedT P20 N m pub) (m3G N)
    (fun x ↦ typedProgT (N.inst Q lay) (pubXT x)) (TRelTT N Q lay) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y)
    vk c x (pubXT x) hpub _ _
    (by rw [widthsA_typedIT, dTypedT_m3G]; exact ref_dTypedT N Q lay H (pubXT x) hacc hwT)
    (fun _ _ ↦ monoD_dTypedT _ _ _ _) (fun cl pp ↦ fol_openMain cl pp)
    (fun w hw' ↦ mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')) hw Shape.nuMain_P20 rfl rfl
    (by rw [show dSel P20T = dSel P20 from rfl, dSel, layout0_P20]; rfl) rfl ksXLog_P20F skip_P20F
    (smallT_P20F x) hs rfl (fun _ _ _ ↦ rfl)
    (fun t a' hT tp co lo kg hk hsh hall ↦ by
      rw [m3G_tableClaims, hsc] at hall ⊢
      exact claimsT_rel N Q lay H hσ x t a' hT tp co lo kg hk hsh hall)

/-- **S2GT-STMT 7** (owner V, then L): **`refinesG20`**: `VSGX N` refines the compiled verifier of S2GT's pinned
middle phases (`midGT`, E2F-T) at S2GT's format `fmtG20`, for every native record meeting `TRefHypT` with `σ′` in
`S` (`refinesF20`'s shape). -/
theorem refinesG20 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay)
    (hσ : Lvm.TypedV.SigInS N.toN) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSGX N vk c π).runLog L = some true →
      ((schemeSW fmtG20 vk (PSWithM (midP (midMk 4 reloc20 (midGT (N.inst Q lay)))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.toT.fits
  exact fun vk L c π _ h ↦ runLog_of_seq (fun tr ht ↦ refines_seqOfG
    (PSWithM (midP (midMk 4 reloc20 (midGT (N.inst Q lay)))))
    (wDecF (atomsOf P20T (typedIT P20T)) (atomsOf P20 (openMainI P20))).length P20T fmtG20 (VSGX N) (decideFGX N)
    (decideProgG N) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (fun sig vk c x ↦ pubG vk c sig = pubXT x)
    (fun _ _ _ ↦ rfl) (fun _ _ _ hF ↦ decideFGX_ok hF) (fun _ _ _ _ hp hs ↦ pubG_eq hp hs)
    (fun sig vk c x hpub ↦ ref_decideGT N Q lay H hσ sig vk c x hpub) rfl rfl rfl
    (by rw [headerBytesP_P20T.1]; decide) (fun _ _ _ hp ↦ okS_of_parseOkH hp (hdrFix_le_P _))
    (fol_PSOfT reloc20 (N.inst Q lay) hl busDepth_P20 hr he) stA_P20T wAt_rwG20 vk c π tr ht) L h

end Lvm.E2T
