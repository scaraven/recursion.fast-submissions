-- New for lvm2 (roll 8 = B1, wave L, L-C): O5b for the typed backend. `VST P20 N` (parse, drive the typed
-- schedule, `decideFT`) accepting implies the compiled verifier of an IOP verifier `PS` accepting, on every log,
-- given the value refinement and the schedule's shape (roll 7's simulation, `sim`). lvm2 roll 11 (M′, R11-IR): the
-- grouping and the opening at `S2GM` (one cap, `C_main`'s opening only); the M′ instance is `LvmMPVEq`.
import LvmTypedVEqPhases
import LvmTypedVEqFol
import LvmVEqMain
import LvmCertTInst

/-!
# V_S ⇒ S.V, typed

* `dMidT`, `dTopT`, **`decideProgT_dTopT`**: `decideProgT` grouped as `P_S` (the cap, the typed phases and
  phases 4–7 as `midT₂`, the opening).
* `okB_dst`, `regsOf_dst`: `okB`'s facts on the region targets (M′: `σ′`'s on `C_main`).
* **`ref_dOpenT`**: the M′ opening (`C_main`'s claims, both shapes) refines `verifyStackedJ (cfgMain23Jq 1)`.
* `refines_seqOfT`: O5b on every trace, for any `PS` V_S's decision refines (`RefDT`) and that follows the
  schedule (roll 7's `refines_seqOf`, read for `VST`/`decideFT`).
* `trefHyp20`; **`midFollowsT20L`**: `LvmCertT20.midFollowsT20` (statement verbatim).
* (lvm2 roll 11, M′ `S2GM`: B1's `typedClaims_rel`, `ref_dMidT`, `ref_decideT`, `refines_VST`, `refinesT20L`
  targeted the two-root `PSWith` and are gone; their M′ forms are `LvmMPVEq`'s.)
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs)
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)

/-! ## `decideProgT` grouped as `P_S` -/

/-- A bus result with no claim (the typed path has no bus; the mini-bus's claims are its table phase's). -/
def busNil : BusOut := ⟨true, [], [], []⟩

/-- **Phases 2–7 of the typed decision** (the typed phases, then roll 7's `dKg`), grouped as `midT₂`: the claims
and the folded accumulator. -/
def dMidT (p : Params) (N : TNat) (pub : Pub) : DM (List (Com × BlockClaim × FE) × Acc) :=
  dTypedT p N (N.m3 p) pub >>= fun t ↦ dKg p (N.m3 p) pub >>= fun kg ↦
    pure (t.2.1 ++ dClaimsT (N.m3 p) p pub busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2, t.1)

/-- **`decideProgT` grouped as `P_S`** (its value: the folded accumulator; M′ `S2GM`: one cap). -/
def dTopT (p : Params) (N : TNat) (vk c : Vector UInt8 32) : DM Acc :=
  MonadReader.read >>= fun sig ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap) >>= fun _ ↦
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

/-! ## The claims -/

/-- `okB`'s facts on a region's target (M′ `S2GM`: `σ′`'s regions are in `C_main`, as the committed block's and
`KS`'s; B1 had them in `C_rec`). -/
theorem okB_dst {N : TNat} {nuMain nuRec : ℕ} (h : N.okB nuMain nuRec = true) {g : NReg} (hg : g ∈ N.regs) :
    (g.src = .com ∨ g.src = .ks ∨ g.src = .sigma) → g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ nuMain := by
  unfold TNat.okB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hs := (h.1.1.1.1.1 g hg).2
  rintro (he | he | he) <;> rw [he] at hs <;> simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs <;>
    exact ⟨hs.1.1, le_trans hs.2 (min_le_left _ _)⟩

theorem regsOf_dst {N : TNat} {nuMain nuRec : ℕ} (h : N.okB nuMain nuRec = true) (s : YSrc)
    (hs : s = .com ∨ s = .ks ∨ s = .sigma) :
    ∀ g ∈ N.regsOf s, g.dst % 2 ^ g.log = 0 ∧ g.dst + 2 ^ g.log ≤ 2 ^ nuMain := by
  intro g hg
  simp only [TNat.regsOf, List.mem_filter, beq_iff_eq] at hg
  obtain ⟨hg, hgs⟩ := hg
  exact okB_dst h hg (hgs ▸ hs)

theorem onStackZsF_append (s : Bool) (a b : List (BlockClaim × FE)) :
    Shape.onStackZsF s (a ++ b) = Shape.onStackZsF s a ++ Shape.onStackZsF s b := by
  unfold Shape.onStackZsF; split <;> simp

theorem onStackZs_append (x : List UInt8) (a b : List VStackClaim) :
    Shape.onStackZs x (a ++ b) = Shape.onStackZs x a ++ Shape.onStackZs x b := by
  unfold Shape.onStackZs; split <;> simp

theorem m3_eq (N : TNat) (p : Params) : N.m3 p = M3.real p fun _ ↦ N.mbT := rfl

/-! ## The opening -/

section Ref

variable {sig : ByteArray}

theorem commitRootUd_mainT : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

theorem monoD_dOpenT (p : Params) (s : Bool) (claims : List (Com × BlockClaim × FE)) : MonoD (dOpenT p s claims) :=
  (MonoD.require _).bind fun _ ↦ monoD_verifyStacked _ _ _ _ _ _

/-- **The M′ opening at `P20`** (`S2GM`: `C_main`'s claims only, on the statement's shape's stack): V_S's
`dOpenT` refines `verifyStackedJ (cfgMain23Jq 1)` on a list `SCRel`-related to `onStackZsF`'s, where its
`require` (every claim on `C_main`) held. -/
theorem ref_dOpenT (s : Bool) (claims : List (Com × BlockClaim × FE)) (cl : List VStackClaim)
    (h : claims.all (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2))) cl) :
    RefAtP capS occS shpS sig (dOpenT P20 s claims) (Verifier.verifyStackedJ (cfgMain23Jq 1) cl)
      (fun _ _ ↦ True) (fun _ ↦ True) := by
  unfold dOpenT
  refine RefAtP.require_left (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _) fun hall ↦ ?_
  have h' := h hall
  have e : (if s then ((claims.filter (·.1 == .main)).map (·.2)).map fun e ↦ onStackZBN P20.nuMain e.1 e.2
      else ((claims.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2)) := by
    unfold Shape.onStackZsF; rw [nuMain_P20]; rfl
  dsimp only
  rw [e, nuMain_P20]
  exact (ref_verifyStackedJ _ (cfgMain23Jq 1) _ _ _ _ _ h' mainOod_P20 rfl rfl rfl rfl rfl corrMain24).toP _

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

variable (N : TNat) (PS : List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool)

/-- **V_S's typed decision refines the IOP verifier `PS`** on every stream whose header is the statement's (lvm2
roll 11: generic in `PS`; M′'s is `PSWithM`, B1's was `PSWith mid`). -/
def RefDT : Prop :=
  ∀ (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8), pubOf vk c sig = pubX x →
    RefAtP capS occS shpS sig (decideProgT P20 N vk c) (PS x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y)

/-- **V_S ⇒ S.V on a trace, typed** (roll 7's `refines_seqOf` for `VST`/`decideFT`). -/
theorem refines_seqOfT (href : RefDT N PS)
    (hfol : ∀ x, Fol capS shpS idxS (PS x) (atomsOf P20 (schedule P20)) []
      fun _ _ ↦ True)
    (vk c : RecursionFast.Digest) (π : ByteArray) (tr : Trace)
    (h : (VST P20 N vk c π).runSeq tr = some true) :
    ((Lvm.ASM.schemeS vk PS).V c π).runSeq tr = some true := by
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
  obtain ⟨⟨b0, rs'⟩, hivp⟩ : ∃ r, ivp capS occS shpS (PS x) (traceBytesB tr) RS.start = r :=
    ⟨_, rfl⟩
  rw [hivp] at hb1
  simp only at hb1
  subst hb1
  -- the simulation
  have hJ0 : J (Lvm.ASM.schemeS vk PS) π tr
      ⟨headerBytes, headerBytes, st₀, [(seedQuery π a₀, st₀), (q0Query, a₀)], [], []⟩ st₀ [] []
      ((π.data.toList).drop headerBytes) RS.start 2 [] :=
    ⟨rfl, le_rfl, hHle, by rw [Nat.sub_self, List.take_zero], rfl, (entOff_two π a₀ st₀ rest hHle).symm,
      by show 0 = headerBytes - headerBytes; rw [Nat.sub_self],
      ⟨[], rfl, rfl, rfl, fun j hj ↦ absurd hj (by simp), List.nodup_nil⟩⟩
  obtain ⟨s', st', buf', caps', body', i', cr', hJ', hk', -, hrun⟩ :=
    sim (S := Lvm.ASM.schemeS vk PS) (π := π) (tr := tr) (p := P20)
      rfl rfl rfl capOfS_eq occOfS_eq (atomsOf P20 (schedule P20)) (PS x) [] _ _ st₀ [] []
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
  set S := Lvm.ASM.schemeS vk PS with hSdef
  have hS_hdr : S.hdr π = some (x, (π.data.toList).drop headerBytes) := hdrS_of_parseOk hp
  have hS_pre : S.preOk c x = true := by
    show (Lvm.ASM.okS vk c x && decide (32 + x.length ≤ queryCap)) = true
    rw [okS_of_parseOk hp]; simp [hqc]
  unfold Scheme.V
  rw [hS_hdr]
  simp only [hS_pre, ↓reduceIte]
  rw [show toQ S.q0 = q0Query from rfl, htr, runSeq_query_eq,
    show S.seedQ a₀ x = seedQuery π a₀ from hseed, runSeq_query_eq,
    show S.P x = PS x from rfl, run_eq_runK,
    show rest = tr.drop 2 from rfl, hrun, hnil', hbody']
  rfl

end Main

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

open Lvm.CT Lvm.QTyped Lvm.ASM in
/-- **`LvmCertT20.midFollowsT20`** (statement verbatim). -/
theorem midFollowsT20L (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  midFollows_T NT20 QB20 layT20 (trefHyp20 S H)

end Lvm.VEq
