-- New for lvm2 E2-FT (E2F-V2-REF): pieces (b) and (c) of `refinesF20` — V_S's opening at S2GF (`dOpenF`, the
-- pin's claim first) against `verifyStackedJ (cfgMain23Jq 1)`, and V_S's whole decision `decideProgF` at `P20F`
-- against `PSWithM (midP (midM Lvm.CT.reloc20 (midF₂ Ti)))` on the stream with S2GF's read widths `rwF20`.
import LvmE2VDecClaims
import LvmE2VRefW
import LvmE2VRefines

/-!
# V_S's decision at S2GF refines the pinned middle phases

* `dTypedX_P20F`: the typed phases read only `P20`'s fields (`P20F` is `P20` at stage `1`, `accV = 44`).
* **`ref_dOpenF`**: the opening, the pin's claim first, given the pin's claim relation (`screl_pinW`).
* `psF_eq`: `PSWithM (midP (midM Lvm.CT.reloc20 (midF₂ Ti))) x` as one chain (commit, pin, typed, tape, `KS`, link,
  opening).
* **`ref_decideFX`**: `RefAtPW … rwF20 sig 0 (decideProgF P20F …) (PSWithM …) (fun _ b ↦ b = true) (Φ_Q)` from the
  sibling's facts (the typed program and the opening follow 24-byte atoms; the widths of the S2GF schedule).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-! ## `P20F` reads `P20`'s fields -/

theorem m3_busFinal (N : TNat) (p : Params) :
    (N.m3 p).busFinal = fun i ↦ M3.busFinalR (M3.sumcheckTabs N.mbT) i := rfl

theorem m3_tables (N : TNat) (p : Params) :
    (N.m3 p).tables = fun _ ↦ (M3.sumcheckTabs N.mbT).map M3.nativeTable := rfl

theorem m3_tableClaims (N : TNat) (p : Params) (pub : Pub) (evs : List (List FE × List FE)) :
    (N.m3 p).tableClaims pub evs = M3.tableClaimsR (M3.sumcheckTabs N.mbT) evs := rfl

theorem dMiniT_congr (p p' : Params) (m m' : M3) (tabs : List M3.Tab) (pub : Pub) (h1 : p.busDepth = p'.busDepth)
    (h2 : p.leafdecReads = p'.leafdecReads) (h3 : p.tableRounds = p'.tableRounds) (hb : m.busFinal = m'.busFinal)
    (ht : m.tables = m'.tables) : dMiniT p m tabs pub = dMiniT p' m' tabs pub := by
  unfold dMiniT
  rw [h1, h2, h3, hb, ht]

theorem typedClaimsN_P20F (N : TNat) : typedClaimsN N P20F = typedClaimsN N P20 := rfl

/-- **The typed phases at `P20F` are `P20`'s** (they read `busDepth`, `leafdecReads`, `tableRounds`, the layout). -/
theorem dTypedX_P20F (N : TNat) (pub : Pub) : dTypedX P20F N (N.m3 P20F) pub = dTypedX P20 N (N.m3 P20) pub := by
  unfold dTypedX
  rw [dMiniT_congr P20F P20 (N.m3 P20F) (N.m3 P20) N.mbT pub rfl rfl rfl
    ((m3_busFinal N P20F).trans (m3_busFinal N P20).symm) ((m3_tables N P20F).trans (m3_tables N P20).symm),
    typedClaimsN_P20F]

/-! ## The opening -/

theorem monoD_dOpenF (p : Params) (s : Bool) (pin : BlockClaim) (claims : List (Com × BlockClaim × FE)) :
    MonoD (dOpenF p s pin claims) :=
  (MonoD.require _).bind fun _ ↦ monoD_verifyStacked _ _ _ _ _ _

/-- **The opening at S2GF** (`dOpenF`, the pin's claim first, then `C_main`'s claims on the statement's shape's
stack) refines `verifyStackedJ (cfgMain23Jq 1)` on the list `pc :: cl`, where its `require` held, given the pin's
claim relation `SCRel (pin.weight, pin.value) pc` (`screl_pinW`) and the rest's (`claimsF_rel`). -/
theorem ref_dOpenF {sig : ByteArray} (pin : BlockClaim) (pc : VStackClaim) (hpc : SCRel (pin.weight, pin.value) pc)
    (s : Bool)
    (claims : List (Com × BlockClaim × FE)) (cl : List VStackClaim)
    (h : claims.all (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2))) cl) :
    RefAtP capS occS shpS sig (dOpenF P20F s pin claims)
      (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (pc :: cl)) (fun _ _ ↦ True) (fun _ ↦ True) := by
  unfold dOpenF
  refine RefAtP.require_left (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _) fun hall ↦ ?_
  have h' := h hall
  have e : (if s then ((claims.filter (·.1 == .main)).map (·.2)).map fun e ↦ onStackZBN P20F.nuMain e.1 e.2
      else ((claims.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2)) := by
    unfold Shape.onStackZsF; rfl
  dsimp only
  rw [e]
  exact (ref_verifyStackedJ P20.mainLevels (cfgMain23Jq 1) 23 _ _ _ _ (.cons hpc h') mainOod_P20 rfl rfl rfl rfl rfl
    corrMain24).toP _

/-- **The pin's claim** (`dOpenF`'s head: weight `eq(z, ·)`, value `a`) relates to the lead's `pinClaim` at every
point. (The block claim's `onStack` would not: it carries the factor `eq(x_{≥23}, 0)`, so at `z = 0^23`, `a = 0`,
`x = 0^23 ‖ 1` the spec's weight is `1` and its `0`; `SCRel` quantifies over lists of every length.) -/
theorem screl_pinW (z : List FE) (a : FE) :
    SCRel ((BlockClaim.point ⟨CMain.nu20, 0⟩ z a).weight, (BlockClaim.point ⟨CMain.nu20, 0⟩ z a).value)
      (Lvm.E2F.pinClaim (z.map FE.toExt3, FE.toExt3 a)) :=
  ⟨rfl, fun xs ↦ (toExt3_eqEval z xs).symm⟩

/-! ## The decision -/

theorem monoD_callerD (h : ℕ) : MonoD (callerD h) :=
  (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_verifyKeccakD _ _ _).bind fun _ ↦
    (monoD_rowSwitchD _ _).bind fun _ ↦ MonoD.pure _

/-- `C_main`'s cap (no read). -/
theorem refW_skip {sig : ByteArray} {rw : ℕ → ℕ} {i ht w n : ℕ} (h : n = 32 * 2 ^ capS ht w) :
    RefAtW capS occS shpS rw sig i (DM.skip n) (VerifierProgram.readCommitment ht w) (fun _ _ ↦ True) i := by
  intro s _
  subst h
  exact ⟨(), rfl, rfl, rfl, rfl, trivial⟩

/-- **The pinned middle phases as one chain**, for the typed program `T` and the `KS` link's rows `rows`: the root,
the pin, the typed phases, the tape caller, `KS`, the link, `C_main`'s opening on the pin's claim and `ordM` of
`assembleF₂`'s relocated pair. -/
theorem psG_eq (k : ℕ) (T : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims) (rows : List ℕ) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk k Lvm.CT.reloc20 (E2V.midFWithR T rows))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        T x >>= fun a ↦ E2V.tapeProgE2 20 1 0 (hdX x).s (pubX x).n >>= fun tp ↦
          E2V.callerProgE2 13 >>= fun co ↦ E2V.ksLinkProgE2 13 9 rows >>= fun lo ↦
            LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
              Lvm.ASM.ordMk k ((E2V.assembleF₂ x a (tp, (co, lo))).1.map (Lvm.CT.reloc20 x))
                (E2V.assembleF₂ x a (tp, (co, lo))).2) >>= fun _ ↦ pure true := by
  unfold Lvm.ASM.PSWithM Lvm.E2F.midP Lvm.ASM.midMk E2V.midFWithR E2V.kgProgFR
  rw [commitRootUd_mainT]
  simp only [bind_assoc, ret_bindM, pure_bind]

/-- **The pinned middle phases at S2GF as one chain** (`psG_eq` at `typedProgX`, `contRowsF`). -/
theorem psF_eq (Ti : TInst) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midM Lvm.CT.reloc20 (E2V.midF₂ Ti))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        Lvm.Typed.typedProgX Ti (pubXF x) >>= fun a ↦ E2V.tapeProgE2 20 1 0 (hdX x).s (pubX x).n >>= fun tp ↦
          E2V.callerProgE2 13 >>= fun co ↦ E2V.ksLinkProgE2 13 9 E2V.contRowsF >>= fun lo ↦
            LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
              Lvm.ASM.ordM ((E2V.assembleF₂ x a (tp, (co, lo))).1.map (Lvm.CT.reloc20 x))
                (E2V.assembleF₂ x a (tp, (co, lo))).2) >>= fun _ ↦ pure true :=
  psG_eq 2 (fun x ↦ Lvm.Typed.typedProgX Ti (pubXF x)) E2V.contRowsF x

/-- `Φ_Q`'s promise on a step's value from the value it always returns. -/
theorem promise_of_retDG (Φ : Acc → Prop) {d : DM Acc} {c : Acc} (hr : RetD (fun r ↦ r = c) d)
    {sig : ByteArray} {s : RS} (h : Φ (runD d sig s).1) : Φ c :=
  hr sig s ▸ h

theorem promise_of_retD (φ : List FE → FE) {d : DM Acc} {c : Acc} (hr : RetD (fun r ↦ r = c) d)
    {sig : ByteArray} {s : RS} (h : φ (runD d sig s).1.pt = (runD d sig s).1.y) : φ c.pt = c.y :=
  promise_of_retDG (fun a ↦ φ a.pt = a.y) hr h

theorem skip_P20F : nodeBytes * 2 ^ (P20F.level ⟨.main, 0⟩).cap = 32 * 2 ^ capS 19 64 := by decide

theorem smallT_P20F (x : List UInt8) : TypedV.smallT P20F (pubXF x) = Shape.small x := smallP_P20 x

/-- The front's widths at S2GF: the tape caller, `KS`, the link. -/
def wFrontF : List ℕ := wTape 20 ++ wCaller 13 ++ wKsLink 13

/-- **V_S's read widths at S2GF** in the decision's order: the pin's read, the typed phases' (`asT`), the front's, the
opening's (`asO`). -/
def wDecF (asT asO : List Atom) : List ℕ := [24] ++ widthsA asT ++ wFrontF ++ widthsA asO

/-- **V_S's decision of an `E2`-front stage refines the pinned middle phases** (`ref_decideFX`'s proof, generic in
the record `p`, the public values' reader `pubR`, the `KS` rows, the typed phases `typed` against `T x` (`hTyp`, with
relation `RT` and promise `Φ`), the mini-bus's instance `m3` and the claims' relation `hcl`), with read widths
`[24] ++ widthsA asT ++ wFrontF ++ widthsA asO` from read `0`. -/
theorem ref_decideG (k : ℕ) (p : Params) (pubR : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Pub)
    (rows : List ℕ) (typed : M3 → Pub → DM (Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)))
    (m3 : Params → M3) (T : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims)
    (RT : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE) → Lvm.ASM.OpenClaims → Prop)
    (Φ : Acc → Prop) (vk c : RecursionFast.Digest) (x : List UInt8) {sig : ByteArray} (pubS : Pub)
    (hpub : pubR vk c sig = pubS) (asT asO : List Atom) {rw : ℕ → ℕ}
    (hTyp : RefAtPW capS occS shpS rw sig (0 + [24].length) (typed (m3 p) pubS) (T x) RT (fun t ↦ Φ t.1)
      (0 + [24].length + (widthsA asT).length))
    (hmT : ∀ m pub, MonoD (typed m pub))
    (hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl) asO pp fun _ _ ↦ True)
    (h24O : ∀ w ∈ widthsA asO, w = 24) (hw : WAt rw 0 (wDecF asT asO))
    (hnu : p.nuMain = CMain.nu20) (hlog : p.logN = 20) (hdsb : dSelBits p = 1) (hds : dSel p = 0)
    (hks : p.ksLog = 13) (hxl : ksXLog p = 9) (hskip : nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = 32 * 2 ^ capS 19 64)
    (hsmall : TypedV.smallT p pubS = Shape.small x) (hs : sBitsD pubS.s = KG.digestBits (hdX x).s)
    (hn : pubS.n = (pubX x).n) (hOpen : ∀ s pin cl, dOpenF p s pin cl = dOpenF P20F s pin cl)
    (hcl : ∀ t a', RT t a' → ∀ tp co lo (kg : E2V.KgOutF), FrontRel tp co lo kg → TapeShape 20 1 0 tp →
      (t.2.1 ++ Shape.zeroTails ((m3 p).tableClaims pubS t.2.2) ++ frontClaimsD p pubS tp co lo).all
        (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
          (((t.2.1 ++ Shape.zeroTails ((m3 p).tableClaims pubS t.2.2) ++ frontClaimsD p pubS tp co lo).filter
            (·.1 == .main)).map (·.2)))
        (Lvm.ASM.ordMk k ((E2V.assembleF₂ x a' kg).1.map (Lvm.CT.reloc20 x)) (E2V.assembleF₂ x a' kg).2)) :
    RefAtPW capS occS shpS rw sig 0 (decideProgFG pubR rows p typed m3 vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk k Lvm.CT.reloc20 (E2V.midFWithR T rows))) x)
      (fun _ b ↦ b = true) Φ (wDecF asT asO).length := by
  rw [wDecF, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw0, hwT⟩, hwF⟩, hwO⟩ := hw
  rw [wFrontF, WAt.append, WAt.append] at hwF
  obtain ⟨⟨hwTp, hwC⟩, hwL⟩ := hwF
  rw [psG_eq k]
  unfold decideProgFG
  refine RefAtPW.read_left ?_
  dsimp only
  rw [hpub, hnu]
  -- the cap
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    ((refW_skip (n := nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap) (ht := 19) (w := 64) hskip).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro - - - -
  -- the pin
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ ((refW_pinD (WAt.cons.mp hw0).1).toPW _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro pin za ⟨z, a, rfl, rfl⟩ -
  -- the typed phases
  refine RefAtPW.bind (Q := fun t ↦ Φ t.1) ?_ hTyp ?_ ?_
  rotate_left
  · intro b s hs
    refine promise_of_retDG Φ ?_ hs
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      RetD.pure rfl
  rintro ⟨acc, tcl, evals⟩ a' hT -
  dsimp only
  -- the tape caller
  rw [hlog, hdsb, hds, hn]
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    (((refW_tapeD 20 1 0 _ _ hs _ (WAt.idx_eq hwTp (by simp; omega))).retD (retD_tapeD 20 1 0 _ _)).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro tp tp' ⟨htp, hsh⟩ -
  -- `KS`
  rw [hks, hxl]
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_ ((refW_callerD 13 (WAt.idx_eq hwC (by simp; omega))).toPW _)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro co co' hco -
  -- the `KS` link
  refine RefAtPW.bind (Q := fun _ ↦ True) ?_
    ((refW_ksLinkD 13 9 rows (WAt.idx_eq hwL (by simp; omega))).toPW _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro lo lo' hlo -
  -- the opening
  rw [hsmall, hOpen]
  have hO := RefAtP.toPW (ref_dOpenF (sig := sig) _ _ (screl_pinW z a) (Shape.small x) _ _
    (hcl (acc, tcl, evals) a' hT tp co lo (tp', (co', lo')) ⟨htp, hco, hlo⟩ hsh))
    (cap' := capS) (shp' := shpS) (idx := idxS)
    (i := 0 + [24].length + (widthsA asT).length + (wTape 20).length + (wCaller 13).length + (wKsLink 13).length)
    (hFO _) (WAt.idx_eq hwO (by simp [wFrontF]; omega)) h24O
  refine RefAtPW.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) hO (fun _ _ _ ↦ trivial) ?_
  rintro - - - -
  exact ((RefAtW.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) rfl).idx
    (by simp [wDecF, wFrontF]; omega)).toPW _
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_pinD _) | (with_reducible exact hmT _ _)
    | (with_reducible exact monoD_tapeD _ _ _ _ _) | (with_reducible exact monoD_callerD _)
    | (with_reducible exact monoD_ksLinkD _ _ _) | (with_reducible exact monoD_dOpenF _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-- **V_S's decision at S2GF refines the pinned middle phases on the stream with S2GF's read widths** under the
promise that its value (the folded accumulator) passes `Φ_Q`: from read `0` to read `|wDecF asT asO|`, given that the
typed program follows `asT` and the opening `asO` (24-byte reads), and that `rwF20` reads `wDecF asT asO` from
`0` (`ref_decideG` at S2GF). -/
theorem ref_decideFX (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypX N Q lay) (hσ : SigInS N)
    (vk c : RecursionFast.Digest) (x : List UInt8) {sig : ByteArray} (hpub : pubOfA accVF vk c sig = pubXF x)
    (asT asO : List Atom) (RT : Lvm.ASM.OpenClaims → Prop)
    (hFT : FolP capS shpS idxS (typedProgX (N.inst Q lay) (pubXF x)) asT RT)
    (hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl) asO pp fun _ _ ↦ True)
    (h24T : ∀ w ∈ widthsA asT, w = 24) (h24O : ∀ w ∈ widthsA asO, w = 24)
    (hw : WAt rwF20 0 (wDecF asT asO)) :
    RefAtPW capS occS shpS rwF20 sig 0 (decideProgF P20F (fun m pub ↦ TypedV.dTypedX P20F N m pub) N.m3 vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midM Lvm.CT.reloc20 (E2V.midF₂ (N.inst Q lay)))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y) (wDecF asT asO).length := by
  have hw' := hw
  rw [wDecF, WAt.append, WAt.append, WAt.append] at hw'
  obtain ⟨⟨⟨-, hwT⟩, -⟩, -⟩ := hw'
  have hacc : (pubXF x).accIn.pt.length = phiVarsX := length_pubXF x
  have hTyp := RefAtP.toPW (ref_dTypedX (cap := capS) (occ := occS) (shp := shpS) (sig := sig) N Q lay H (pubXF x)
    hacc) (cap' := capS) (shp' := shpS) (idx := idxS) (fun pp ↦ (hFT.run pp).mono fun _ _ h ↦ h.2) hwT h24T
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.toT.sc_eq
  have hs : sBitsD (pubXF x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXF x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  exact ref_decideG 2 P20F (pubOfA P20F.accV) E2V.contRowsF (fun m pub ↦ TypedV.dTypedX P20F N m pub) N.m3
    (fun x ↦ typedProgX (N.inst Q lay) (pubXF x)) (TRelT N Q lay) (fun a ↦ N.phi a.pt = a.y) vk c x (pubXF x) hpub
    asT asO (by rw [dTypedX_P20F]; exact hTyp) (fun _ _ ↦ monoD_dTypedX _ _ _ _) hFO h24O hw rfl rfl
    dSelBits_P20F dSel_P20F ksLog_P20F ksXLog_P20F skip_P20F (smallT_P20F x) hs rfl (fun _ _ _ ↦ rfl)
    (fun t a' hT tp co lo k hk hsh hall ↦ by
      rw [m3_tableClaims, hsc] at hall ⊢
      exact claimsF_rel N Q lay H hσ x t a' hT tp co lo k hk hsh hall)

end Lvm.VEq
