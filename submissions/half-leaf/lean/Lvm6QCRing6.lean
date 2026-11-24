-- New for lvm6 (WP CC). Generator and HAR of the ring phase of `prog6` (ASM's `ringPhase6`,
-- FORMAT6 v2.4 §6.5): the bind, the two ring maps and `λ₀` from the stream, both ring targets and
-- the batch in §6.5's claim order (CC-5′ of `Lvm6QCStmt`).
import Lvm6QCWhir
import Lvm6QCRing

/-!
# The ring phase (generator and HAR)

`ringPhaseGen g svT svS vs a`: the 33 answers of the group whose nonce is at `a + 9` (`ansAt`):
tree `f` 0–7, `g` 8–15, sponge `f` 16–23, `g` 24–31, `λ₀` 32; the two `ring_target`s (`tgtG`);
Horner at `λ₀` over `placeC tT tS vs` (ASM's `placeRing` on cells: claim 0, the tree ring claim, 13
claims, the sponge ring claim, the rest). **`ringPhaseHar : RingPhaseHarStmt ringPhaseGen`**.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6.Ring (ringTarget)

/-- ASM's `placeRing` on any list. -/
def placeC {α : Type} (rt rs : α) (st : List α) : List α :=
  st.take 1 ++ rt :: (st.drop 1).take 13 ++ rs :: st.drop 14

theorem map_placeRing {β : Type} (f : StackClaim6 → β) (rt rs : StackClaim6) (st : List StackClaim6) :
    (placeRing rt rs st).map f = placeC (f rt) (f rs) (st.map f) := by
  simp [placeRing, placeC, List.map_append, List.map_take, List.map_drop]

theorem map_placeC {α β : Type} (f : α → β) (rt rs : α) (st : List α) :
    (placeC rt rs st).map f = placeC (f rt) (f rs) (st.map f) := by
  simp [placeC, List.map_append, List.map_take, List.map_drop]

/-- The cells of the group whose nonce is at `a`. -/
def ring6Cells (a : ℕ) (val : C2) : RingPhC :=
  ⟨(List.range 8).map (ansAt a), (List.range 8).map fun j ↦ ansAt a (8 + j),
    (List.range 8).map fun j ↦ ansAt a (16 + j), (List.range 8).map fun j ↦ ansAt a (24 + j),
    ansAt a 32, val⟩

/-- **The ring phase's generator**. -/
def ringPhaseGen (_g : ℕ) (svT svS vs : List C2) (a : ℕ) (_gate : Cell) : BM RingPhC :=
  let c := ring6Cells (a + 9) default
  g2Zero c.lam >>= fun z ↦ g2Const (FE2.ofK FK.x) c.lam >>= fun x ↦ tgtG z x svT c.ft c.gt >>= fun tT ↦
    tgtG z x svS c.fs c.gs >>= fun tS ↦ hornerG z c.lam (placeC tT tS vs) >>= fun v ↦
      pure (ring6Cells (a + 9) v)

theorem tgt_ev2 {c : Ctx} {M : Mem} {z x : C2} (hz : z.val M = 0) (hx : x.val M = FE2.ofK FK.x)
    (sv fs gs : List C2) :
    Hs c M (tgtG z x sv fs gs) fun r ↦
      ev2 M r = ringTarget Ring.genE2 (sv.map (ev2 M)) (fs.map (ev2 M)) (gs.map (ev2 M)) :=
  hs_mono (hs_tgtG hz hx sv fs gs) fun r hr ↦ by
    rw [ev2, hr, Ring.toE2_ringTarget, map_ev2, map_ev2, map_ev2]

/-- **The ring phase runs**, for any value cell meeting the batch's value. -/
theorem runsO_ringPhase6 (M : Mem) (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6)
    (hok : ringOK sh sl) (svT svS vs : List C2) (a : ℕ) (v : C2)
    (hv : sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
      st.map (·.2) = vs.map (ev2 M) → ev2 M v = (claimOf6 sl st
        ((((ring6Cells (a + 9) v).ft.map (ev2 M), (ring6Cells (a + 9) v).gt.map (ev2 M)),
          ((ring6Cells (a + 9) v).fs.map (ev2 M), (ring6Cells (a + 9) v).gs.map (ev2 M))),
          ev2 M (ring6Cells (a + 9) v).lam)).2) :
    RunsO M (layRing6 sh.gRing a) (ringPhase6 sh sl st)
      (fun out ↦ sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
        st.map (·.2) = vs.map (ev2 M) → RingPhRep sl st M (ring6Cells (a + 9) v) out) := by
  intro hpw
  have hg : sh.gRing ≤ 64 := hok.2.1
  have e : layRing6 sh.gRing a = [] ++ ([.b (.d a 0)] ++ ([.b (.k (a + 9))] ++
      (([.b (.d (a + 9 + 1) sh.gRing)] ++
        (bl ((List.range 32).map fun i ↦ LEv.d (a + 9 + 10 + 9 * i) 0) ++ [])) ++ ([] ++ [])))) := by
    simp [layRing6, layItems, bl]
  have hpow : kToNat (lk M (a + 9 + 1 + 2)) < 2 ^ (64 - sh.gRing) :=
    hpw (a + 9 + 1) sh.gRing (by rw [e]; simp)
  rw [e] at hpw ⊢
  have hS : RunsO M ([.b (.d (a + 9 + 1) sh.gRing)] ++
      (bl ((List.range 32).map fun i ↦ LEv.d (a + 9 + 10 + 9 * i) 0) ++ []))
      (VerifierProgram.sampleChallenges 33) (fun cs ↦ cs.map e2OfE =
        ev2 M (ld2 (a + 9 + 1)) :: draws M (a + 9 + 10) 32 ∧ powOK sh.gRing (cs.headD 0)) := by
    show RunsO M _ (VerifierProgram.sampleChallenge >>= fun x ↦
      VerifierProgram.sampleChallenges 32 >>= fun xs ↦ pure (x :: xs)) _
    refine runsO_bind (runsO_sample M (a + 9 + 1) sh.gRing) fun x hx ↦
      runsO_bind (runsO_samples M 32 (a + 9 + 10)) fun xs hxs ↦ runsO_pure ⟨by rw [List.map_cons, hx.1, hxs], ?_⟩
    rw [List.headD_cons, powOK_iff_lane2 hg, hx.2]
    exact hpow
  unfold ringPhase6 ringBody
  refine runsO_bind (runsO_require hok) (fun _ _ ↦ runsO_bind (runsO_sep M a) fun _ _ ↦
    runsO_bind (p := VerifierProgram.readScalar) (runsO_readScalar M (a + 9)) fun _ _ ↦
    runsO_bind (p := VerifierProgram.sampleChallenges 33) hS fun cs hcs ↦
      runsO_bind (runsO_require hcs.2) fun _ _ ↦ runsO_pure ?_) hpw
  intro h1 h2
  have hO : ringOut6 cs = ((((ring6Cells (a + 9) v).ft.map (ev2 M), (ring6Cells (a + 9) v).gt.map (ev2 M)),
      ((ring6Cells (a + 9) v).fs.map (ev2 M), (ring6Cells (a + 9) v).gs.map (ev2 M))),
      ev2 M (ring6Cells (a + 9) v).lam) := by
    have b0 := ans_slice hcs.1 0 8 (by omega)
    have b1 := ans_slice hcs.1 8 8 (by omega)
    have b2 := ans_slice hcs.1 16 8 (by omega)
    have b3 := ans_slice hcs.1 24 8 (by omega)
    simp only [List.drop_zero, Nat.zero_add] at b0
    simp only [ringOut6, ring6Cells, List.map_map, Function.comp_def, b0, b1, b2, b3,
      List.drop_drop]
    rw [ground_ansE hcs.1 (j := 32) (by omega)]
  rw [hO]
  exact ⟨rfl, hv h1 h2⟩

/-- **CC-5′ proved**: the generator re-executes ASM's ring phase. -/
theorem ringPhaseHar : RingPhaseHarStmt ringPhaseGen := by
  intro sh sl st hok hJ svT svS vs a gate c M _
  dsimp only [ringPhaseGen]
  have hlz : ∀ v : C2, (ring6Cells (a + 9) v).lam = ansAt (a + 9) 32 := fun _ ↦ rfl
  refine hsA_of_hs (hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const (FE2.ofK FK.x) _)
    fun x hx ↦ hs_bind (tgt_ev2 hz hx svT _ _) fun tT hT ↦ hs_bind (tgt_ev2 hz hx svS _ _)
    fun tS hS' ↦ hs_bind (hs_hornerG hz _ (placeC tT tS vs)) fun v hvv ↦ hs_pure ?_)
  refine runsO_ringPhase6 M sh sl st hok svT svS vs a v fun h1 h2 ↦ ?_
  obtain ⟨cT, cS, rfl⟩ : ∃ cT cS, sl = [cT, cS] := by
    rcases sl with _ | ⟨cT, _ | ⟨cS, _ | ⟨c3, rest⟩⟩⟩ <;> simp at h1
    exact ⟨cT, cS, rfl⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
  simp only [claimOf6, Ring.batch, List.getD_cons_zero, List.getD_cons_succ]
  rw [map_placeRing, ← List.length_map (f := fun c : StackClaim6 ↦ c.2), map_placeRing, dotF_powersF, h2]
  simp only [ringOf, Ring.ringClaim, h1.1, h1.2]
  dsimp only [ring6Cells] at hT hS' ⊢
  rw [← hT, ← hS', ← map_placeC]
  show FE2.toE2 (v.val M) = _
  rw [hvv, toE2_polyEvalF, ← map_ev2]
  rfl

end Lvm6.QC
