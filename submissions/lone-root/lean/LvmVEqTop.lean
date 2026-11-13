-- New for lvm (WP-14a, H3): the per-phase value refinements of V_S's phases 4–7 (`dKg`) against `kgProgS`, and the
-- claim lists they return. lvm2 roll 11 (M′, R11-IR): the bus path's top (`dTop`, `ref_dMid`, `ref_decide`) is gone;
-- the typed top is `LvmTypedVEqTop`.
import LvmVEqLink
import LvmVEqTape
import LvmVEqWire
import LvmVEqParse
import LvmVEqKec
import LvmVEqBus
import LvmVEqWhir
import LvmCertS
import LvmAccNodeFold
import LvmShapeVR

/-!
# V_S's phases 4–7 refine `kgProgS`

`dBusTab` (the bus path's phases 2–3b, dead at B1), `dKg` (phases 4–7, grouped as `kgProgS`); against `kgProgS`:
phases 4–5 by `ref_dTapeW` (`ref_dTape`, `ref_dWire`), phase 6 by H2's `ref_dKec`, phase 7 by `ref_dKsLink`
(**`ref_dKg`**, relation `KgRel`); `dClaims_rel`: the claims of the tape, `KS` and its output lanes, claim for claim
(`CRel`); the `KS` link's by `CRelM` (M′: `M` on `S`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Lk
open LeanVM.Protocol.Whir.Sound (cfgMain24G)

/-! ## `decideProg` grouped as `P_S` -/

/-- The native result of a Keccak phase (`dKec`). -/
abbrev KecN : Type := List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE))

/-- Phases 2–3b (A23: the table phase's evaluations, then phase 3b's folded accumulator). -/
def dBusTab (p : Params) (m : M3) (pub : Pub) :
    DM (((List FE × BusOut) × List (List FE × List FE)) × Acc) :=
  (dBus p m pub >>= fun pb ↦ dTab p m pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun bt ↦
    accFold p m pub bt.2 >>= fun acc ↦ pure (bt, acc)

/-- Phases 4–7, grouped as `kgProgS` (lvm2 S2: the tape and the wire, then `KS` and its link). -/
def dKg (p : Params) (m : M3) (pub : Pub) :
    DM ((TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) :=
  (dTape p.logN >>= fun tp ↦ dRange p pub >>= fun _ ↦ Shape.dWireC p pub tp.claim >>= fun wo ↦
      pure (tp, wo)) >>= fun tw ↦
    (dKec p.ksLog >>= fun ks ↦ dKsLink p m ks.1 pub >>= fun klc ↦ pure (ks, klc)) >>= fun ksN ↦
      pure (tw, ksN)

/-! ## `MonoD` -/

theorem monoD_dKg (p : Params) (m : M3) (pub : Pub) : MonoD (dKg p m pub) :=
  ((monoD_dTape _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (Shape.monoD_dWireC _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦
    ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
      MonoD.pure _

/-! ## The claims -/

/-- The native tape and wire against the tape caller's output (lvm2 S2; roll 7: `r`'s length and the
ring claim's weight at the returned coefficients). -/
def TapeWRel (tw : TapeRes × (WireOut × List FE)) (o : Lvm.KG.TapeOutE) : Prop :=
  o.1 = tw.1.r.map FE.toExt3 ∧ o.2.1 = tw.1.v.map FE.toExt3 ∧ o.2.2.1 = kcE tw.1.claim ∧
    WireRel 20 tw.2.1 o.2.2.2 ∧ tw.1.r.length = 20 ∧ Shape.WireRing P20 tw.2

/-- The native and the language's outputs of phases 4–7 (`KS` at `9 + 4`: KS13, lvm2 roll 8, B1; roll 7: `10 + 4`; lvm2
roll 11, M′: the `KS` link's claims by `CRelM`, `M` on `S` against the spec's relocated `C_rec` claim). -/
def KgRel (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut) : Prop :=
  TapeWRel kg.1 kg'.1 ∧
    (KecRel (9 + 4) kg.2.1 kg'.2.1 ∧
      List.Forall₂ CRelM kg.2.2 (ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2))

theorem forall₂_main {l : List BlockClaim} {l' : List BClaim} (h : List.Forall₂ BCRel l l') :
    List.Forall₂ CRel (l.map (.main, ·)) (l'.map (.main, ·)) :=
  forall₂_map_both (h.imp fun _ _ h ↦ ⟨rfl, h⟩)

/-- **The claim list of phases 2–6** (all but the `KS` link's, which `KgRel` relates by `CRelM`): V_S's against
`assembleS`'s, claim for claim (lvm2 roll 11, M′: B1's `dClaims_rel` over the whole list, now split at the link). -/
theorem dClaims_rel (tabs : Pub → List M3.Tab) (pub : Pub)
    (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') :
    List.Forall₂ CRel ((tapeClaims P20 kg.1.1 kg.1.2.1 pub ++ keccakClaims (M3.real P20 tabs).ksBlock kg.2.1.2.2.1
        kg.2.1.2.2.2).map (.main, ·) ++ (M3.real P20 tabs).ksOutputClaims kg.2.1.1 kg.2.1.2.1)
      ((tapeClaimsE kg'.1 pub ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
        ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1) := by
  obtain ⟨⟨hr, hv, -, hw, -, -⟩, ⟨hks, -⟩⟩ := hk
  have hk1 := hks.1
  have hk2 := hks.2.1
  refine forall₂_append (forall₂_main
    (forall₂_append (tapeClaims_rel _ _ _ pub hr hv hw.2.2.2.2.1 hw.2.2.2.2.2.1)
      (keccakClaims_rel hks _))) ?_
  rw [hk1, hk2]
  exact ksOutputClaims_rel _ _

/-! ## `s` from the statement -/

theorem get!_hdX_x (x : List UInt8) (t : ℕ) :
    (⟨(List.replicate 8 0 ++ x).toArray⟩ : ByteArray).get! (8 + t) = x.getD t 0 := by
  rw [get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem get!_sigOfX_x' (x : List UInt8) (t : ℕ) : (sigOfX x).get! (headerAt 8 + t) = x.getD t 0 := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

/-- **The statement's chain start**: V_S's `s` lanes are the header digest `s`'s (lvm2 S2: the wire
phase's `Pad43(s)`). -/
theorem pubX_s (x : List UInt8) : (pubX x).s = digestLanes (hdX x).s := by
  have e : ∀ i < 4, ∀ j < 8, ((hdX x).s.toArray.getD (8 * i + j) 0) =
      (sigOfX x).get! (headerAt 80 + 8 * i + j) := by
    intro i hi j hj
    rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_eq_getElem (by omega)]
    simp only [hdX, Header.ofProof, digestAt, Vector.getElem_ofFn, Option.getD_some, offS]
    rw [show 80 + (8 * i + j) = 8 + (72 + 8 * i + j) by omega, get!_hdX_x,
      show headerAt 80 + 8 * i + j = headerAt 8 + (72 + 8 * i + j) by simp only [headerAt]; omega,
      get!_sigOfX_x']
  unfold pubX pubOf digestLanes
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have e0 := e i hi' 0 (by omega)
  simp only [Nat.add_zero] at e0
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e i hi' 1 (by omega), e i hi' 2 (by omega), e i hi' 3 (by omega),
    e i hi' 4 (by omega), e i hi' 5 (by omega), e i hi' 6 (by omega), e i hi' 7 (by omega), kAt, laneAt,
    UInt64.zero_or, Nat.add_zero, Nat.add_assoc]

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

theorem dSel_P20 : dSel P20 = 0 := by decide +kernel

/-- `D`'s selector bits at P20: `ν − 22 = 1` (B1, ν = 23; roll 7: `2`). -/
theorem dSelBits_P20 : dSelBits P20 = 1 := by decide +kernel

/-- The tape caller as the tape phase, then the wire phase. -/
theorem tapeProg_eq (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    Lvm.KG.tapeProg w sb dsel s n =
      (VerifierProgram.sampleChallenges w >>= fun r ↦ VerifierProgram.readScalars 25 >>= fun v ↦
        KeccakGkr.tapeGkr w r v >>= fun claim ↦ VerifierProgram.ret (r, v, claim)) >>= fun t ↦
      VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ w) >>= fun _ ↦
      Lvm.KG.wireChProg w sb dsel s n t.2.2 >>= fun wo ↦ VerifierProgram.ret (t.1, t.2.1, t.2.2, wo) := by
  simp only [Lvm.KG.tapeProg, bind_assoc]
  rfl

/-- **Phases 4–5 refine the tape caller** (lvm2 S2; B1: `D`'s selector bits `dSelBits P20 = 1`, roll 7: `2`). -/
theorem ref_dTapeW (pub : Pub) (d : RecursionFast.Digest) (hs : pub.s = digestLanes d) :
    Ref20 sig (dTape P20.logN >>= fun tp ↦ dRange P20 pub >>= fun _ ↦ Shape.dWireC P20 pub tp.claim >>=
      fun wo ↦ pure (tp, wo))
      (Lvm.KG.tapeProg 20 1 0 d pub.n) TapeWRel := by
  rw [tapeProg_eq]
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (Shape.monoD_dWireC _ _ _).bind fun _ ↦
    MonoD.pure _) (ref_dTape _) ?_
  rintro tp t ⟨h1, h2, h3, -, h5, -, -⟩
  refine RefAt.bind (fun _ ↦ (Shape.monoD_dWireC _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ of_decide_eq_true hc) ?_
  rintro _ _ _
  have hw := Shape.ref_dWireC (cap := capS) (occ := occS) (shp := shpS) (sig := sig) P20 pub tp.claim d hs
  rw [dSel_P20, dSelBits_P20] at hw
  rw [h5]
  refine RefAt.bind (fun _ ↦ MonoD.pure _) hw ?_
  rintro wo out ⟨hwo, hring⟩
  exact RefAt.pure ⟨h1, h2, rfl, hwo, h3, hring⟩

/-- The `KS` link's claims are `m.ksLink`'s (`dKsLink` returns them unchanged). -/
theorem retD_dKsLink (p : Params) (m : M3) (rk : List FE) (pub : Pub) :
    RetD (fun kl ↦ ∃ i, kl = (m.ksLink i).2) (dKsLink p m rk pub) := by
  unfold dKsLink
  refine RetD.bind_true fun kchal ↦ RetD.bind_true fun kshift ↦ RetD.bind_true fun kvals ↦ ?_
  intro sig s
  rcases h : m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩ with ⟨ok, kl⟩
  exact ⟨⟨kchal, kshift, kvals, rk, pub⟩, by rw [h]; rfl⟩

/-- **Phases 4–7 refine `kgProgS`** (roll 7: the native `KS` link claims are `ksLink`'s; roll 8, B1: KS13, `tapeProg 20 1 0`). -/
theorem ref_dKg (tabs : Pub → List M3.Tab) (pub : Pub) (d : RecursionFast.Digest)
    (hs : pub.s = digestLanes d) :
    Ref20 sig (dKg P20 (M3.real P20 tabs) pub) (kgProgS d pub.n)
      (fun kg kg' ↦ KgRel kg kg' ∧ ∃ i, kg.2.2 = ((M3.real P20 tabs).ksLink i).2) := by
  unfold dKg kgProgS
  refine RefAt.bind (fun _ ↦ ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦ MonoD.pure _) (ref_dTapeW pub d hs) ?_
  intro tw tp htw
  refine RefAt.bind (fun _ ↦ MonoD.pure _)
    (R := fun ksN ks ↦ (KecRel (9 + 4) ksN.1 ks.1 ∧
      List.Forall₂ CRelM ksN.2 (ksLinkClaimsE ks.2.1 ks.2.2.1 ks.2.2.2)) ∧
        ∃ i, ksN.2 = ((M3.real P20 tabs).ksLink i).2) ?_ ?_
  · refine RefAt.bind (fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _) (ref_dKec _) ?_
    intro ks co hco
    refine RefAt.bind (fun _ ↦ MonoD.pure _)
      ((ref_dKsLink tabs ks.1 pub).retD (retD_dKsLink _ _ _ _)) ?_
    rintro klc lo ⟨hlo, hi⟩
    exact RefAt.pure ⟨⟨hco, hlo⟩, hi⟩
  rintro ksN ks ⟨hks, hi⟩
  exact RefAt.pure ⟨⟨htw, hks⟩, hi⟩

theorem smallP_P20 (x : List UInt8) : Shape.smallP P20 (pubX x) = Shape.small x := by
  unfold Shape.smallP Shape.small
  rw [show (P20.logN == 20 && P20.nuMain == CMain.nu20) = true by decide +kernel, Bool.true_and]

theorem commitRootUd_main : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

end Ref

end Lvm.VEq
