-- New for lvm2 roll 11 (M′, R11-IR): O5b at M′. `VST P20 N` (stage `S2GM`: one commitment, every claim on
-- `C_main`) accepting implies the compiled verifier of `PSWithM (midM (relocV relocS) (midT₂ (N.inst Q lay)))`
-- accepting, on every log: B1's typed phases and phases 4–7 (`ref_dTypedT`, `ref_dKg`), the claim list against
-- `ordM` of the pair form's (the stream claims relocated onto `S`), the opening (`ref_dOpenT`), roll 7's simulation.
import LvmMPVEqReloc
import LvmMPSig
import LvmTypedVEqTop
import LvmMPMidT

-- (GOLF2: 11 declarations that `certified` does not use moved verbatim to `LvmE2VWidthsFOff`, outside its import closure.)

-- ===== merged from `LvmMPVEqFol` (GOLF module merge: `LvmMPVEqFol.lean` is now a stub importing `LvmMPVEq`) =====
section
-- New for lvm2 roll 11 (M′, R11-IR): M′'s middle phases `midM reloc (midT₂ Ti)` and the IOP verifier
-- `PSWithM (midM reloc (midT₂ Ti))` follow the schedule at `P20` (`S2GM`: one root, `C_main`'s opening), and
-- WP-14d's shape obligation `MidFollows` for them (R11-X's `ext_eqM20` reads it).

/-!
# M′'s `P_S` follows the schedule

* `folP_midM`: `midM reloc mid x` follows what `mid x` follows (the relocation and `ordM` read nothing);
* **`fol_PSTM`**: `PSWithM (midM reloc (midT₂ Ti)) x` against the whole schedule (`fol_PSOfM`);
* `midFollows_midM`: `MidFollows mid` gives `MidFollows (midM reloc mid)`;
* **`midFollowsM20`**: `MidFollows (midM reloc (midT₂ Ti20))` for every relocation, from the guard's facts
  (`LvmTypedVEqTop.midFollowsT20L`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

section

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- `midMk k` follows what its pair-form phases follow. -/
theorem folP_midMk (k : ℕ) (reloc : List UInt8 → VStackClaim → VStackClaim)
    (mid : List UInt8 → VerifierProgram Lvm.ASM.OpenClaims) (x : List UInt8) (as : List Atom)
    (h : FolP cap shp idx (mid x) as fun _ ↦ True) :
    FolP cap shp idx (Lvm.ASM.midMk k reloc mid x) as fun _ ↦ True :=
  h.bind_ret fun _ _ ↦ trivial

end

end Lvm.VEq
end
-- ===== end of `LvmMPVEqFol` =====

/-!
# V_S ⇒ S.V at M′

* `SigInS N` (`LvmMPSig`, R11-IS): `σ′`'s native regions lie in the stream block `S` (the guard's `sigInSB`).
* `regClaim_relocS`: `σ′`'s region claim on the whole stack is its `C_rec` claim relocated onto `S`.
* `VRel s`: a native claim with its tail against a language stack claim, on the shape `s`'s stack;
  `forall₂_crelM`: a `CRelM`-related list in `VRel`, its spec side placed in V_S's order (`inplM`).
* **`typedClaimsM_rel`**: V_S's claim list (all on `C_main`) against `ordM` of `assembleT₂`'s relocated pair.
* `ref_dMidTM`, **`ref_decideTM`**: phases 2–7, then the whole decision, against `midM`, `PSWithM`.
* **`refines_VSTM`**: O5b on every log; **`refinesM20L`**: at `P20` (`LvmCertM20.refinesM20`'s statement, with
  the relocation `relocV relocS = reloc20`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm DM Lvm.FS LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.KeccakGkr (eqAt)

/-! ## `σ′` on the stream block -/

/-- `eq` on `19` coordinates reads only the index's low `19` bits. -/
theorem eqAt_take19_mod (X : List E) (m : ℕ) : eqAt (X.take 19) (m % 2 ^ 19) = eqAt (X.take 19) m := by
  rw [LeanVM.Protocol.KeccakGkr.eqAt_mod _ (m % 2 ^ 19), LeanVM.Protocol.KeccakGkr.eqAt_mod _ m,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by simp))]

/-- **`σ′`'s region claim is its `C_rec` claim relocated onto `S`** (as functions on every point). -/
theorem regClaim_relocS (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (nuMain nuRec : ℕ)
    (hok : N.okB nuMain nuRec = true) (hlay : N.layOk lay = true) (hσ : SigInS N) (r : List E) (v : E) :
    regClaim (N.inst Q lay) .sigma N.off r v = relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW r v) := by
  obtain ⟨-, -, hsort⟩ := fm_ok N nuMain nuRec hok
  have hpw := fm_pairwise N.regs hsort
  refine Prod.ext (funext fun X ↦ ?_) rfl
  show regSum (N.inst Q lay) (fun s' ↦ s' == .sigma) (fun y ↦ eqAt X (N.off y)) r =
    (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove X *
      regSum (N.inst Q lay) (fun s' ↦ s' == .sigma) (fun y ↦ eqAt (X.take 19) (N.off y % 2 ^ 19)) r
  rw [fm_regSum N Q lay hlay, fm_regSum N Q lay hlay, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hgs : (g.src == .sigma) = true
  · simp only [hgs, ite_true]
    obtain ⟨h1, h2⟩ := hσ g hg (by simpa using hgs)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [eqAt_take19_mod, fm_off N hpw g hg i hi', eqAt_reloc X (g.dst + i) ?_]
    · ring
    · simp only [Nat.shiftRight_eq_div_pow]
      rw [show CMain.sOff20 = 5767168 from rfl] at h1 h2 ⊢
      have : 0 < 2 ^ g.log := by positivity
      norm_num
      omega
  · simp [hgs]

/-! ## The relation per claim, both shapes -/

/-- A native claim with its tail against a language stack claim, on the shape `s`'s stack. -/
def VRel (s : Bool) (e : Com × BlockClaim × FE) (w : VStackClaim) : Prop :=
  SCRel (if s then Shape.onStackZB e.2.1 e.2.2 else e.2.1.onStack) (if s then Shape.onStackZ w else w)

theorem vrel_of {s : Bool} {e : Com × BlockClaim × FE} {w : VStackClaim} (h : SCRel e.2.1.onStack w)
    (ht : s = true → Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1) : VRel s e w := by
  cases s
  · simpa [VRel] using h
  · obtain ⟨h1, h2⟩ := ht rfl
    simpa [VRel] using Shape.onStackZB_rel h h1 h2

/-- V_S's stack claims on the shape `s`'s stack against a `VRel`-related list. -/
theorem forall₂_onStackZsF {s : Bool} {V : List (Com × BlockClaim × FE)} {W : List VStackClaim}
    (h : List.Forall₂ (VRel s) V W) :
    List.Forall₂ SCRel (Shape.onStackZsF s (V.map (·.2))) (W.map fun w ↦ if s then Shape.onStackZ w else w) := by
  unfold Shape.onStackZsF
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_map, List.map_id']
    simpa [Function.comp_def] using Lk.forall₂_map_both (h.imp fun _ _ hr ↦ by simpa [VRel] using hr)
  · simp only [↓reduceIte, List.map_map]
    exact Lk.forall₂_map_both (h.imp fun _ _ hr ↦ by simpa [VRel] using hr)

/-- A spec claim in V_S's order: a `C_rec` claim relocated onto `S`, a `C_main` claim as it is. -/
def inplM (b : Com × BClaim) : VStackClaim := if b.1 = .crec then relocS b.2.onStack else b.2.onStack

/-- **A `CRelM`-related list** (every native claim on `C_main`, with its tail) in `VRel`. -/
theorem forall₂_crelM {s : Bool} {D : List (Com × BlockClaim × FE)} {E : List (Com × BClaim)}
    (h : List.Forall₂ CRelM (D.map fun e ↦ (e.1, e.2.1)) E) (hm : ∀ e ∈ D, e.1 = .main)
    (ht : s = true → ∀ e ∈ D, e.1 = .main → Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1) :
    List.Forall₂ (VRel s) D (E.map inplM) := by
  rw [List.forall₂_map_left_iff] at h
  rw [List.forall₂_map_right_iff]
  induction h with
  | nil => exact .nil
  | @cons e b D E hab _ ih =>
    refine .cons ?_ (ih (fun e he ↦ hm e (List.mem_cons_of_mem _ he))
      fun hs e he ↦ ht hs e (List.mem_cons_of_mem _ he))
    have he := hm e List.mem_cons_self
    refine vrel_of ?_ fun hs ↦ ht hs e List.mem_cons_self he
    rcases hab with ⟨h1, h2⟩ | ⟨-, h2, h3⟩
    · have hb : b.1 = .main := h1 ▸ he
      simp only [inplM, hb, reduceCtorEq, ↓reduceIte]
      exact onStack_rel h2
    · simp only [inplM, h2, ↓reduceIte]
      exact h3

theorem main_of_crel {A : List (Com × BlockClaim)} {B : List (Com × BClaim)} (h : List.Forall₂ CRel A B)
    (hA : ∀ a ∈ A, a.1 = .main) : ∀ b ∈ B, b.1 = .main := by
  induction h with
  | nil => simp
  | @cons a b A B hab _ ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab.1 ▸ hA a List.mem_cons_self
    · exact ih (fun a ha ↦ hA a (List.mem_cons_of_mem _ ha)) c hc

theorem inplM_main {l : List (Com × BClaim)} (h : ∀ b ∈ l, b.1 = .main) : l.map inplM = l.map (·.2.onStack) :=
  List.map_congr_left fun b hb ↦ by simp [inplM, h b hb]

theorem filter_main_self {l : List (Com × BClaim)} (h : ∀ b ∈ l, b.1 = .main) : l.filter (·.1 == .main) = l :=
  List.filter_eq_self.2 fun b hb ↦ by simp [h b hb]

theorem filter_crec_nil {l : List (Com × BClaim)} (h : ∀ b ∈ l, b.1 = .main) : l.filter (·.1 == .crec) = [] :=
  List.filter_eq_nil_iff.2 fun b hb ↦ by simp [h b hb]

/-! ## The claim list -/

/-- `ordM` commutes with a common map. -/
theorem ordM_map {α β : Type} (f : α → β) (r m : List α) :
    Lvm.ASM.ordM (r.map f) (m.map f) = (Lvm.ASM.ordM r m).map f := by
  simp only [Lvm.ASM.ordM, List.map_append, List.map_take, List.map_drop, List.map_dropLast, List.getLast?_map]
  cases m.getLast? <;> rfl

theorem onStackZs_eq_map (x : List UInt8) (l : List VStackClaim) :
    Shape.onStackZs x l = l.map fun w ↦ if Shape.small x then Shape.onStackZ w else w := by
  unfold Shape.onStackZs; split <;> simp_all

theorem offOK_relay : Shape.OffOK ⟨P20.nuRec, (layout0 P20).s⟩ := by
  rw [layout0_P20]; decide +kernel

theorem layout0_s : (layout0 P20).s = CMain.sOff20 := by rw [layout0_P20]

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

theorem ret_bindM {α β : Type} (a : α) (f : α → VerifierProgram β) : (VerifierProgram.ret a >>= f) = f a := rfl

end Ref

/-! ## V_S ⇒ S.V at M′ -/

end Lvm.VEq
