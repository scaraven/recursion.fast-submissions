-- New for lvm6 (WP CD). The typed family composed: the node circuit's re-execution of the child's
-- whole `typedProgE` (zerocheck, wiring, relayout, A23 with the tie, the mini-bus) from the five
-- HARs, with the returned claims in terms of the gadgets' cells.
import Lvm6QDWire
import Lvm6QDMb

/-!
# The typed phases composed (`ty6`, `ty6_har`)

`ty6 Ti pubC ain yIn own ownY a gate` runs `zero6`, `wire6`, `relay6`, `qacc6`, `mb6` on the lanes
`layItems (tyItems ++ mbItems) a` (each phase from the previous one's `layEnd`). **`ty6_har`**:
with the gate on, where the rows and gated assertions hold, (i) the child's `accOut` is the
node's `accIn` cells (the tie), and (ii) under the promise `Φ_Q(own) = ownY`, Y1's `typedProgE Ti L
pw (ain, yIn)` returns on every matching event list with grinds passing, and its claims are
`typedClaimsE` of the gadgets' cells and the mini-bus's claims (`mbClaimsG`) of the walk's cells.
-/

set_option autoImplicit false

namespace Lvm6.QD

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm.Typed
open Lvm6 (Item rep rnd)
open Lvm6.QK
open Lvm6.Ty (TInst6 typedProgE typedClaimsE zeroProgE wireProgE relayProgE accProgE phiVarsE PhiQE)
open Lvm6.Mb (LBusG lvmBusProgG miniBusLProg6 mbClaimsG miniDepth)

variable {c : Ctx} {M : Mem}

/-! ## Shapes of the gadgets' outputs -/

theorem hs_bind_t {α β : Type} {m : BM α} {f : α → BM β} {P : β → Prop} (hf : ∀ a, Hs c M (f a) P) :
    Hs c M (m >>= f) P := hs_bind (hs_true m) fun a _ ↦ hf a

theorem hs_eqRounds6_len : ∀ (q : ℕ) (value : C2) (rs : List C2),
    Hs c M (eqRounds6 q value rs) (fun o ↦ o.2.length = rs.length)
  | _, _, [] => hs_pure rfl
  | q, value, r :: rs => hs_bind_t fun rc ↦ hs_bind (hs_eqRounds6_len (q + 14) rc.2 rs) fun res hres ↦
      hs_pure (by simp [hres])

/-- The zerocheck's `A, B, C` cells. -/
def abcC (a : ℕ) : List C2 := [ld2 (zAbc a), ld2 (zAbc a + 2), ld2 (zAbc a + 4)]

theorem hs_zero6_shape (a : ℕ) (gate : Cell) :
    Hs c M (zero6 a gate) (fun o ↦ o.abc = abcC a ∧ o.rx.length = xVars) := by
  unfold zero6
  refine hs_bind_t fun z ↦ hs_bind (hs_eqRounds6_len _ z (tauC a)) fun rf hrf ↦ ?_
  refine hs_bind_t fun _ ↦ hs_bind_t fun _ ↦ hs_bind_t fun _ ↦ hs_pure ⟨rfl, ?_⟩
  simpa [tauC] using hrf

/-- The wiring's matrix-value and region-value cells. -/
def vsC (a : ℕ) : List C2 := (List.range 4).map fun i ↦ ld2 (a + 304 + 2 * i)

def rvC (a : ℕ) : List C2 := (List.range 4).map fun i ↦ ld2 (a + 312 + 2 * i)

theorem hs_wire6_shape (Ti : TInst6) (pubC : ℕ → Cell) (v : List C2) (a : ℕ) (gate : Cell) :
    Hs c M (wire6 Ti pubC v a gate) (fun o ↦ o.vs = vsC a ∧ o.rv = rvC a ∧ o.ry.length = yVars) := by
  unfold wire6
  refine hs_bind_t fun _ ↦ hs_bind_t fun _ ↦ hs_bind_t fun _ ↦ hs_bind_t fun _ ↦ hs_bind_t fun _ ↦ ?_
  refine hs_bind (hs_sc2 yVars (a + 10) _) fun rf hrf ↦ ?_
  have hl : rf.1.length = yVars := by rw [hrf.1]; simp [sc2Ans]
  repeat refine hs_bind_t fun _ ↦ ?_
  exact hs_pure ⟨rfl, rfl, hl⟩

theorem hsA_and {α : Type} {m : BM α} {P Q : α → Prop} (h1 : HsA c M m P) (h2 : HsA c M m Q) :
    HsA c M m fun o ↦ P o ∧ Q o := fun p hh ha ↦ ⟨h1 p hh ha, h2 p hh ha⟩

/-! ## The composed gadget -/

/-- The phases' first lanes. -/
def aW (a : ℕ) : ℕ := layEnd zeroItems a
def aR (a : ℕ) : ℕ := layEnd wireItems (aW a)
def aA (a : ℕ) : ℕ := layEnd relayItems (aR a)
def aM (a : ℕ) : ℕ := layEnd accItems (aA a)

/-- What the composed gadget hands on. -/
structure TyOutC where
  zero : ZeroOutC
  wire : WireOutC
  relay : RelayOutC
  mb : MbOutC

/-- **The typed phases in the node circuit.** -/
def ty6 (Ti : TInst6) (pubC : ℕ → Cell) (ain : List C2) (yIn : C2) (own : List C2) (ownY : C2) (a : ℕ)
    (gate : Cell) : BM TyOutC :=
  zero6 a gate >>= fun zo ↦ wire6 Ti pubC zo.abc (aW a) gate >>= fun wo ↦
    relay6 Ti wo.ry (wo.rv.getD 1 (ld2 0)) (aR a) gate >>= fun ro ↦
      qacc6 Ti.Q Ti.lay ain yIn (zo.rx ++ wo.ry) wo.vs own ownY (aA a) gate >>= fun _ ↦
        mb6 (aM a) gate >>= fun mo ↦ pure ⟨zo, wo, ro, mo⟩

/-- The mini-bus walk's result as the program's record. -/
def busOf (M : Mem) (o : MbOutC) : LBusG :=
  ⟨o.alphas.map (ev2 M), ev2 M o.beta, o.point.map (ev2 M), o.values.map (ev2 M)⟩

/-- **The typed phases composed** (CD-1 … CD-5 along `typedProgE`). -/
theorem ty6_har (Ti : TInst6) (hok : Ti.Ok) (hlay : TyLayOk Ti) (L : Lvm.M3.Lay) (pubC : ℕ → Cell)
    (ain : List C2) (yIn : C2) (own : List C2) (ownY : C2) (hain : ain.length = phiVarsE)
    (hown : own.length = phiVarsE) (a : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (ty6 Ti pubC ain yIn own ownY a gate) fun o ↦
      accOut6 (ain.map (ev2 M), ev2 M yIn) (gdraws M (aA a) 2) ((o.zero.rx ++ o.wire.ry).map (ev2 M))
          (scal M (aA a + 20) (phiVarsE + 1)) (ev2 M (ld2 (aA a + 20 + 2 * (phiVarsE + 1) + 1))) =
        (own.map (ev2 M), ev2 M ownY) ∧
      (PhiQE Ti.Q Ti.lay (own.map (ev2 M)) = ev2 M ownY →
        Runs M (layItems (tyItems ++ mbItems) a)
          (typedProgE Ti L (fun y ↦ ((pubC y).val M).c₀) (ain.map (ev2 M), ev2 M yIn))
          (fun out ↦ out = typedClaimsE Ti (o.wire.ry.map (ev2 M)) (o.wire.rv.map (ev2 M))
            (o.relay.rr.map (ev2 M)) (ev2 M o.relay.vR)
              ((mbClaimsG L.nuMain Ti.mbT (busOf M o.mb)).map (·.onStack)))) := by
  unfold ty6
  refine hsA_bind (hsA_and (zero6_har a gate c M hg) (hsA_of_hs (hs_zero6_shape a gate))) fun zo hzo ↦ ?_
  obtain ⟨hZ, habc, hrx⟩ := hzo
  refine hsA_bind (hsA_and (wire6_har Ti hok hlay pubC zo.abc (by rw [habc]; rfl) (aW a) gate c M hg)
    (hsA_of_hs (hs_wire6_shape Ti pubC zo.abc (aW a) gate))) fun wo hwo ↦ ?_
  obtain ⟨hW, hvs, hrv, hry⟩ := hwo
  refine hsA_bind (relay6_har Ti hok hlay wo.ry hry _ (aR a) gate c M hg) fun ro hR ↦ ?_
  refine hsA_bind (qacc6_har Ti.Q Ti.lay ain yIn (zo.rx ++ wo.ry) wo.vs own ownY hain
    (by simp [hrx, hry]) (by rw [hvs]; rfl) hown (aA a) gate c M hg) fun _ hA ↦ ?_
  refine hsA_bind (mb6_har (aM a) gate c M hg) fun mo hMb ↦ hsA_pure ⟨hA.1, fun hP ↦ ?_⟩
  have hl : layItems (tyItems ++ mbItems) a = layItems zeroItems a ++ (layItems wireItems (aW a) ++
      (layItems relayItems (aR a) ++ (layItems accItems (aA a) ++ layItems mbItems (aM a)))) := by
    simp only [tyItems, layItems_append, layEnd_append, List.append_assoc, aW, aR, aA, aM]
  rw [hl]
  unfold typedProgE
  refine runs_bind' rfl hZ fun z hz ↦ ?_
  rw [hz.2]
  refine runs_bind' rfl hW fun w hw ↦ ?_
  have hvS : w.2.2.getD 1 0 = ev2 M (wo.rv.getD 1 (ld2 0)) := by rw [hw.2.2, hrv]; rfl
  rw [hw.1, hvS]
  refine runs_bind' rfl hR fun r hr ↦ ?_
  have hA' : Runs M (layItems accItems (aA a)) (accProgE Ti.Q Ti.lay (ev2 M yIn) (ain.map (ev2 M))
      ((zo.rx ++ wo.ry).map (ev2 M)) (wo.vs.map (ev2 M))) (fun _ ↦ True) := fun hpw evs he ↦
    ⟨(), hA.2 hP hpw evs he, trivial⟩
  rw [hz.1, hw.2.1, ← List.map_append]
  refine runs_bind' rfl hA' fun _ _ ↦ ?_
  unfold miniBusLProg6
  rw [bind_assoc]
  refine runs_bind' (l₂ := []) (List.append_nil _).symm hMb fun b hb ↦ ?_
  simp only [pure_bind]
  refine runs_pure ?_
  obtain ⟨ba, bb, bp, bv⟩ := b
  obtain ⟨h1, h2, h3, h4⟩ := hb
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rw [hr.1, hr.2, hw.2.2]
  rfl

end Lvm6.QD
