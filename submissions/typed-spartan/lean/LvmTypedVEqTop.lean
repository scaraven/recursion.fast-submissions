-- New for lvm2 (roll 8 = B1, wave L, L-C): O5b for the typed backend. `VST P20 N` (parse, drive the typed
-- schedule, `decideFT`) accepting implies the compiled verifier of `P_S = PSWith (midT₂ (N.inst Q lay))`
-- accepting, on every log: the value refinement `ref_decideT` (the typed phases, roll 7's tape/wire/`KS`/`KS` link,
-- the openings at ν = 23 in both shapes), the schedule's shape (`fol_PST`), roll 7's simulation (`sim`).
import LvmTypedVEqPhases
import LvmTypedVEqFol
import LvmVEqMain
import LvmCertTInst

/-!
# V_S ⇒ S.V, typed

* `dMidT`, `dTopT`, **`decideProgT_dTopT`**: `decideProgT` grouped as `P_S` (the caps, the typed phases and
  phases 4–7 as `midT₂`, the openings).
* **`typedClaims_rel`**: V_S's claim list (the typed claims, then the mini-bus's, the tape's, `KS`'s and the
  `KS` link's) against `assembleT₂`'s, both commitments (`C_main`'s on the statement's shape: the typed region
  claims have no tail, `tail_affW`).
* `ref_dMidT`, **`ref_decideT`**: phases 2–7, then the whole decision, under the promise that the folded claim
  holds (`decideFT` checks it after the run).
* `refines_seqOfT`, **`refines_VST`**: O5b on every trace and every log (roll 7's `refines_seqOf`, read for
  `VST`/`decideFT`).
* **`refinesT20L`**, **`midFollowsT20L`**: `LvmCertT20`'s stubs `refinesT20`, `midFollowsT20` (statements
  verbatim), from the guard's facts `S : SF20` and `THyp Ti20`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgRec20G cfgMain24G cfgMain23Jq cfgRec20Jp)

/-! ## `decideProgT` grouped as `P_S` -/

/-- A bus result with no claim (the typed path has no bus; the mini-bus's claims are its table phase's). -/
def busNil : BusOut := ⟨true, [], [], []⟩

/-- **Phases 2–7 of the typed decision** (the typed phases, then roll 7's `dKg`), grouped as `midT₂`: the claims
and the folded accumulator. -/
def dMidT (p : Params) (N : TNat) (pub : Pub) : DM (List (Com × BlockClaim × FE) × Acc) :=
  dTypedT p N (N.m3 p) pub >>= fun t ↦ dKg p (N.m3 p) pub >>= fun kg ↦
    pure (t.2.1 ++ dClaimsT (N.m3 p) p pub busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2, t.1)

/-- **`decideProgT` grouped as `P_S`** (its value: the folded accumulator). -/
def dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) : DM Acc :=
  MonadReader.read >>= fun sig ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap) >>= fun _ ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap) >>= fun _ ↦
    dMidT p N (pubOf vk c sig) >>= fun r ↦ dOpenT p (smallT p (pubOf vk c sig)) r.1 >>= fun _ ↦ pure r.2

theorem decideProgT_dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) :
    decideProgT p N vk c = dTopT p N vk c := by
  simp only [decideProgT, dTopT, dMidT, dKg, dKec, dKsLink, dClaimsT, busNil, bind_assoc, pure_bind]

theorem monoD_dMidT (p : Params) (N : TNat) (pub : Pub) : MonoD (dMidT p N pub) :=
  (monoD_dTypedT _ _ _ _).bind fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _

theorem nuMain_P20 : P20.nuMain = 23 := by decide +kernel

theorem nuRec_P20 : P20.nuRec = 19 := by decide +kernel

/-- The typed shape bit is roll 7's (`nuT = CMain.nu20 = 23`, `2^18`). -/
theorem smallT_eq (p : Params) (pub : Pub) : smallT p pub = Shape.smallP p pub := rfl

/-- The typed openings are roll 7's two-shape openings at `P20` (`onStackZBN 23 = onStackZB`). -/
theorem dOpenT_P20 (s : Bool) (claims : List (Com × BlockClaim × FE)) :
    dOpenT P20 s claims = Shape.dOpenZ P20 s claims := by
  unfold dOpenT Shape.dOpenZ Shape.onStackZsF
  rw [nuMain_P20]
  rfl

/-! ## The claims -/

/-- `okB`'s facts on a region's target. -/
theorem okB_dst {N : TNat} {nuMain nuRec : ℕ} (h : N.okB nuMain nuRec = true) {g : NReg} (hg : g ∈ N.regs) :
    ((g.src = .com ∨ g.src = .ks) → g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ nuMain) ∧
    (g.src = .sigma → g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ nuRec) := by
  unfold TNat.okB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hs := (h.1.1.1.1.1 g hg).2
  constructor
  · rintro (he | he) <;> rw [he] at hs <;> simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs <;>
      exact ⟨hs.1.1, le_trans hs.2 (min_le_left _ _)⟩
  · intro he
    rw [he] at hs
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    exact hs

theorem regsOf_dst {N : TNat} {nuMain nuRec : ℕ} (h : N.okB nuMain nuRec = true) (s : YSrc) (ν : ℕ)
    (hs : (s = .com ∨ s = .ks) ∧ ν = nuMain ∨ s = .sigma ∧ ν = nuRec) :
    ∀ g ∈ N.regsOf s, g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ ν := by
  intro g hg
  simp only [TNat.regsOf, List.mem_filter, beq_iff_eq] at hg
  obtain ⟨hg, hgs⟩ := hg
  rcases hs with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · exact (okB_dst h hg).1 (hgs ▸ hs)
  · exact (okB_dst h hg).2 (hgs ▸ hs)

theorem onStackZsF_append (s : Bool) (a b : List (BlockClaim × FE)) :
    Shape.onStackZsF s (a ++ b) = Shape.onStackZsF s a ++ Shape.onStackZsF s b := by
  unfold Shape.onStackZsF; split <;> simp

theorem onStackZs_append (x : List UInt8) (a b : List VStackClaim) :
    Shape.onStackZs x (a ++ b) = Shape.onStackZs x a ++ Shape.onStackZs x b := by
  unfold Shape.onStackZs; split <;> simp

theorem m3_eq (N : TNat) (p : Params) : N.m3 p = M3.real p fun _ ↦ N.mbT := rfl

/-- **V_S's claim list against `assembleT₂`'s**, both commitments (`C_main`'s on the statement's shape). -/
theorem typedClaims_rel (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (x : List UInt8)
    (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims)
    (hT : TRelT N Q lay t a)
    (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') (hi : ∃ i, kg.2.2 = ((N.m3 P20).ksLink i).2) :
    List.Forall₂ SCRel (((t.2.1 ++ dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1
        kg.2.2).filter (·.1 == .crec)).map (·.2.1.onStack)) (assembleT₂ x a kg').1 ∧
      List.Forall₂ SCRel (Shape.onStackZsF (Shape.smallP P20 (pubX x))
        (((t.2.1 ++ dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2).filter
          (·.1 == .main)).map (·.2))) (assembleT₂ x a kg').2 := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, hrr, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.fits
  have hR := dClaims_rel (fun _ ↦ N.mbT) (pubX x) ((([] : List FE), busNil), t.2.2) (claimsOfEvs N.mbT t.2.2)
    rfl (by rw [H.sc_eq]; exact hcl) kg kg' hk
  rw [H.sc_eq, ← Shape.dClaimsT_fst] at hR
  rw [m3_eq]
  have hok := H.ok
  rw [nuMain_P20] at hok
  -- the typed region claims
  have hcom := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .com 23
    (regsOf_dst hok .com 23 (.inl ⟨.inl rfl, rfl⟩)) ry hry (rv.getD 0 0)
  have hks := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .ks 23
    (regsOf_dst hok .ks 23 (.inl ⟨.inr rfl, rfl⟩)) ry hry (rv.getD 3 0)
  have hsg := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .sigma P20.nuRec
    (regsOf_dst hok .sigma P20.nuRec (.inr ⟨rfl, rfl⟩)) ry hry (rv.getD 2 0)
  have hrel : SCRel (BlockClaim.point ⟨P20.nuRec, 0⟩ rr vR).onStack
      (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack :=
    onStack_rel (Lk.point_rel _ _ _ (by rw [nuRec_P20]; rfl) rfl rfl)
  rw [ht1]
  set D := dClaimsT (M3.real P20 fun _ ↦ N.mbT) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2
  set cl := claimsOfEvs N.mbT t.2.2
  have eR : ∀ com : Com, ((tableClaimsE N.mbT cl ++
      (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (fun c : BClaim ↦ (Com.main, c)) ++
      ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1 ++ ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2).filter
        (fun e : Com × BClaim ↦ e.1 == com)).map (fun e : Com × BClaim ↦ e.2.onStack) =
      miniClaims (N.inst Q lay) com cl ++ ((tableClaimsE [] [] ++
        (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (fun c : BClaim ↦ (Com.main, c)) ++
        ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1 ++ ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2).filter
          (fun e : Com × BClaim ↦ e.1 == com)).map (fun e : Com × BClaim ↦ e.2.onStack) := by
    intro com
    simp only [miniClaims, List.filter_append, List.map_append, List.append_assoc, TNat.inst]
    rfl
  constructor
  · have hc := on_rel hR .crec
    rw [← Shape.filter_fst, List.map_map, eR] at hc
    rw [List.filter_append, List.map_append]
    rw [← getD_map_toExt3] at hsg
    exact List.Forall₂.cons hrel (List.Forall₂.cons hsg hc)
  · have hm := Shape.onStackZsF_rel hR x (s := Shape.smallP P20 (pubX x)) (smallP_P20 x) fun hsm ↦ by
      obtain ⟨⟨-, -, -, hwr, hr, hring⟩, -⟩ := hk
      rw [smallP_P20] at hsm
      exact Shape.tails_main (fun _ ↦ N.mbT) (pubX x) hfc hfh busNil rfl t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2
        hr hwr.2.2.2.2.2.2.1 hwr.2.2.2.2.2.2.2.2.1 hring hi (of_decide_eq_true hsm) (by simp [pubX, pubOf])
    rw [eR] at hm
    have hT2 : List.Forall₂ SCRel
        (Shape.onStackZsF (Shape.smallP P20 (pubX x))
          [(⟨⟨P20.nuMain, 0⟩, affW N .com ry, rv.getD 0 0⟩, 0), (⟨⟨P20.nuMain, 0⟩, affW N .ks ry, rv.getD 3 0⟩, 0)])
        (Shape.onStackZs x [regClaim (N.inst Q lay) .com N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 0 0)),
          regClaim (N.inst Q lay) .ks N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 3 0))]) := by
      rw [nuMain_P20]
      unfold Shape.onStackZsF Shape.onStackZs
      rw [smallP_P20]
      cases Shape.small x
      · exact List.Forall₂.cons hcom (List.Forall₂.cons hks List.Forall₂.nil)
      · have hin : Shape.InStack ⟨23, 0⟩ := ⟨le_rfl, rfl, by norm_num⟩
        exact List.Forall₂.cons (Shape.onStackZB_rel hcom hin (tail_affW N P20.nuRec hok .com (.inl rfl) _ _).symm)
          (List.Forall₂.cons (Shape.onStackZB_rel hks hin (tail_affW N P20.nuRec hok .ks (.inr rfl) _ _).symm)
            List.Forall₂.nil)
    rw [List.filter_append, List.map_append, onStackZsF_append]
    have e2 : (assembleT₂ x (typedClaims (N.inst Q lay) (ry.map FE.toExt3) (rv.map FE.toExt3) (rr.map FE.toExt3)
        (FE.toExt3 vR) cl) kg').2 = Shape.onStackZs x [regClaim (N.inst Q lay) .com N.off (ry.map FE.toExt3)
          (FE.toExt3 (rv.getD 0 0)), regClaim (N.inst Q lay) .ks N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 3 0))] ++
        Shape.onStackZs x (miniClaims (N.inst Q lay) .main cl ++ (assembleS [] (pubX x) [] kg').2) := by
      rw [← onStackZs_append]
      unfold assembleT₂ typedClaims
      simp only [getD_map_toExt3, List.cons_append, List.nil_append]
      rfl
    rw [e2]
    exact Lk.forall₂_append hT2 hm

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

/-- **Phases 2–7 refine `midT₂`** under the promise that the folded claim holds: `C_rec`'s stack claims agree,
and `C_main`'s, put on the statement's shape's stack by V_S, agree with `onStackZs`'s. -/
theorem ref_dMidT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (x : List UInt8)
    (hacc : (pubX x).accIn.pt.length = phiVars) :
    RefAtP capS occS shpS sig (dMidT P20 N (pubX x)) (midT₂ (N.inst Q lay) x)
      (fun r cl ↦
        List.Forall₂ SCRel ((r.1.filter (·.1 == .crec)).map (·.2.1.onStack)) cl.1 ∧
          List.Forall₂ SCRel
            (Shape.onStackZsF (Shape.smallP P20 (pubX x)) ((r.1.filter (·.1 == .main)).map (·.2))) cl.2)
      (fun r ↦ N.phi r.2.pt = r.2.y) := by
  unfold dMidT midT₂
  apply RefAtP.bind (Q := fun t ↦ N.phi t.1.pt = t.1.y)
  · exact fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_dTypedT N Q lay H (pubX x) hacc
  · intro t s h; rw [runD_bind_pure_snd] at h; exact h
  · rintro t a hT -
    refine (RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKg (fun _ ↦ N.mbT) (pubX x) (hdX x).s (pubX_s x)) ?_).toP _
    rintro kg kg' ⟨hk, hi⟩
    exact RefAt.pure (typedClaims_rel N Q lay H x t a hT kg kg' hk hi)

theorem commitRootUd_mainT : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

theorem commitRootUd_recT : Verifier.commitRootUd cfgRec20G = VerifierProgram.readCommitment 15 64 := rfl

/-- **V_S's typed decision refines `P_S = PSWith (midT₂ Ti)`** under the promise that its value (the folded
accumulator) passes `Φ_Q` (`decideFT`'s check after the run). -/
theorem ref_decideT (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay)
    (vk c : RecursionFast.Digest) (x : List UInt8) (hacc : (pubX x).accIn.pt.length = phiVars)
    (hpub : pubOf vk c sig = pubX x) :
    RefAtP capS occS shpS sig (decideProgT P20 N vk c) (Lvm.ASM.PSWith (midT₂ (N.inst Q lay)) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y) := by
  rw [decideProgT_dTopT]
  unfold dTopT Lvm.ASM.PSWith
  rw [commitRootUd_mainT, commitRootUd_recT]
  refine RefAtP.read_left ?_
  simp only [hpub, smallT_eq, dOpenT_P20]
  -- the caps
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ (monoD_skip _).bind fun _ ↦ (monoD_dMidT _ _ _).bind fun _ ↦
      (Shape.monoD_dOpenZ _ _ _).bind fun _ ↦ MonoD.pure _
  · exact (ref_skip (n := nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap) rfl).toP _
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ (monoD_dMidT _ _ _).bind fun _ ↦ (Shape.monoD_dOpenZ _ _ _).bind fun _ ↦ MonoD.pure _
  · exact (ref_skip (n := nodeBytes * 2 ^ (P20.level ⟨.crec, 0⟩).cap) rfl).toP _
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  -- phases 2–7
  apply RefAtP.bind (Q := fun r ↦ N.phi r.2.pt = r.2.y)
  · exact fun _ ↦ (Shape.monoD_dOpenZ _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_dMidT N Q lay H x hacc
  · intro r s h; rw [runD_bind_pure] at h; exact h
  rintro r cl ⟨h1, h2⟩ -
  -- the openings
  have h := RefAt.bind (fun _ ↦ MonoD.pure _) (Shape.ref_dOpenZ (sig := sig) _ r.1 cl h1 h2)
    fun _ _ _ ↦ RefAt.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) (b := r.2) (a := true) rfl
  have e : ((Verifier.verifyStackedJ cfgRec20Jp cl.1 >>= fun _ ↦
      Verifier.verifyStackedJ (cfgMain23Jq 3) cl.2).bind fun _ ↦ VerifierProgram.ret true) =
      (Verifier.verifyStackedJ cfgRec20Jp cl.1 >>= fun _ ↦ Verifier.verifyStackedJ (cfgMain23Jq 3) cl.2 >>=
        fun _ ↦ pure true) := VerifierProgram.bind_assoc _ _ _
  rw [e] at h
  exact h.toP _

end Ref

/-! ## V_S ⇒ S.V -/

/-- `decideFT` holds: the run's checks held and its folded claim passes `Φ_Q`. -/
theorem decideFT_ok {p : Params} {N : TNat} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFT p N vk c sig = true) :
    (runD (decideProgT p N vk c) sig RS.start).2.ok = true ∧
      N.phi (runD (decideProgT p N vk c) sig RS.start).1.pt = (runD (decideProgT p N vk c) sig RS.start).1.y := by
  unfold decideFT DM.runOn at h
  rw [decideProgTS_eq] at h
  have e : (decideProgT p N vk c sig).run RS.start = runD (decideProgT p N vk c) sig RS.start := rfl
  rw [e] at h
  rcases hr : runD (decideProgT p N vk c) sig RS.start with ⟨a, s⟩
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, Lvm.M3.FE_eq_of_beq h.2⟩

section Main

variable (N : TNat) (mid : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram
  (List VStackClaim × List VStackClaim))

/-- **V_S's typed decision refines `PSWith mid`** on every stream whose header is the statement's. -/
def RefDT : Prop :=
  ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), pubOf vk c sig = pubX x →
    RefAtP capS occS shpS sig (decideProgT P20 N vk c) (Lvm.ASM.PSWith mid x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y)

/-- **V_S ⇒ S.V on a trace, typed** (roll 7's `refines_seqOf` for `VST`/`decideFT`). -/
theorem refines_seqOfT (href : RefDT N mid)
    (hfol : ∀ x, Fol capS shpS idxS (Lvm.ASM.PSWith mid x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VST P20 N vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)).V c π).runSeq tr = some true := by
  -- the header check
  unfold VST at h
  by_cases hp : parseOk P20 vk c π = true
  swap
  · rw [if_neg hp] at h; exact absurd (runSeq_ret_true h).2 (by simp)
  rw [if_pos hp] at h
  have hp' := hp
  simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hp'
  have hsize : π.size = piSize P20 := hp'.1.1.1
  have hHle : headerBytes ≤ π.size := by rw [hsize, sizes_P20.1]; decide
  -- the driver: q₀, the seed, the schedule
  unfold drive at h
  obtain ⟨a₀, tr1, rfl, h1⟩ := runSeq_query_cons h
  obtain ⟨st₀, rest, rfl, h2⟩ := runSeq_query_cons h1
  rw [driveItems_eq] at h2
  obtain ⟨sf, n, hf1, hf2, -, -⟩ := drive_run P20 π _ _ _ rest h2
  obtain ⟨hnil, hb⟩ := runSeq_ret_true hf1
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨-, hF⟩ := hb
  have hn : rest.take n = rest := List.take_of_length_le (List.drop_eq_nil_iff.mp hnil)
  have hlog : streamOf sf.log =
      traceBytesB ((q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest) := by
    rw [streamOf, hf2, hn]; simp
  rw [hlog] at hF
  set tr := (q0Query, a₀) :: (seedQuery π a₀, st₀) :: rest with htr
  set x := xOf π with hx
  -- the value refinement: the program read off the stream returns `true`
  have hpub := pubOf_eq_pubX hp (sig := traceBytesB tr) (seed_bytes π a₀ st₀ rest hHle)
  obtain ⟨hok0, hacc⟩ := decideFT_ok hF
  obtain ⟨b, hb1, -, -, rfl⟩ := href (traceBytesB tr) vk c x hpub RS.start hok0 hacc
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS occS shpS (Lvm.ASM.PSWith mid x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    sim (S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid)) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq occOfS_eq (atomsOf P20 (schedule P20)) (Lvm.ASM.PSWith mid x) [] _ _ st₀ [] []
      _ RS.start 2 [] [] _ true rs' (hfol x) (by simpa using stA_P20) hJ0 rfl
      (fun _ h ↦ by simp at h)
      (fun s'' m hm ↦ by
        obtain ⟨-, hb⟩ := runSeq_ret_true hm
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        rw [hb.1])
      h2 hivp
  obtain ⟨hnil', hb'⟩ := runSeq_ret_true hk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hb'
  have hbody' : body' = [] := by
    rw [hJ'.body, hb'.1, List.drop_eq_nil_iff, length_blb]
  -- the compiled verifier
  have hx5976 : x.length = Lvm.ASM.hdrLen := by
    rw [hx, xOf, List.length_take, List.length_drop, length_blb]
    simp only [Lvm.ASM.hdrLen]; omega
  have hseed : toQ (a₀.toList ++ x) = seedQuery π a₀ := by
    apply toQ_eq
    rw [seedQuery, blb_append, blb_digestBytes, blb_extract, hx, xOf]
    rfl
  have hqc : 32 + x.length ≤ queryCap := by rw [hx5976]; decide
  set S := Lvm.ASM.schemeS vk (Lvm.ASM.PSWith mid) with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hdrS_of_parseOk hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [okS_of_parseOk hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = Lvm.ASM.PSWith mid x from rfl, run_eq_runK,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

end Main

/-- **O5b for the typed backend** (`OpenS.refines`' form): whenever `VST P20 N` accepts a proof on a log, so does
the compiled verifier of `PSWith (midT₂ (N.inst Q lay))`. -/
theorem refines_VST (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay)
    (hacc : ∀ x, (pubX x).accIn.pt.length = phiVars) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VST P20 N vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midT₂ (N.inst Q lay)))).V c π).runLog L = some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.fits
  intro vk L c π _ h
  exact runLog_of_seq (fun tr ht ↦ refines_seqOfT N (midT₂ (N.inst Q lay))
    (fun sig vk c x hpub ↦ ref_decideT N Q lay H vk c x (hacc x) hpub)
    (fol_PST (N.inst Q lay) hl busDepth_P20 hr he) vk c π tr ht) L h

/-- **The typed middle phases follow the schedule** (`MidFollows`), the mini-bus's numbers from `TRefHyp`. -/
theorem midFollows_T (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) :
    Lvm.ASM.MidFollows (midT₂ (N.inst Q lay)) := by
  obtain ⟨hl, hr, he, -, -⟩ := H.fits
  exact midFollows_midT₂ (N.inst Q lay) hl busDepth_P20 hr he

/-! ## At `P20`: `LvmCertT20`'s stubs -/

open Lvm.CT Lvm.QTyped in
/-- **`TRefHyp` at `P20`** from the guard's facts and `THyp`: `PhiQC cacheT20` is `PhiQF` (`cacheT20_eq`, then
`PhiQC_eq`, rewriting only). -/
theorem trefHyp20 (S : SF20) (H : THyp Ti20) : TRefHyp NT20 QB20 layT20 where
  ok := S.regs
  hlay := S.hlayOk
  mini := S.mini
  sc := H.sc
  phi pt hpt := by
    have e : NT20.phi = PhiQC cacheT20 := rfl
    have hc : (cacheW QB20 layT20).okB QB20 layT20 = true := by rw [← cacheT20_eq]; exact S.cache
    rw [e, cacheT20_eq]
    exact PhiQC_eq QB20 layT20 S.hlay hc pt hpt

open Lvm.CT Lvm.QTyped Lvm.T Lvm.ASM in
/-- **`LvmCertT20.refinesT20`** (statement verbatim): `VST P20 NT20` refines the compiled verifier of
`midT₂ Ti20`. -/
theorem refinesT20L (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWith (midT₂ Ti20))).V c π).runLog L = some true :=
  refines_VST NT20 QB20 layT20 (trefHyp20 S H) H.acc

open Lvm.CT Lvm.QTyped Lvm.ASM in
/-- **`LvmCertT20.midFollowsT20`** (statement verbatim). -/
theorem midFollowsT20L (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  midFollows_T NT20 QB20 layT20 (trefHyp20 S H)

end Lvm.VEq
