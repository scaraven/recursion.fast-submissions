-- New for lvm2 roll 11 (M′, R11-IR): O5b at M′. `VST P20 N` (stage `S2GM`: one commitment, every claim on
-- `C_main`) accepting implies the compiled verifier of `PSWithM (midM (relocV relocS) (midT₂ (N.inst Q lay)))`
-- accepting, on every log: B1's typed phases and phases 4–7 (`ref_dTypedT`, `ref_dKg`), the claim list against
-- `ordM` of the pair form's (the stream claims relocated onto `S`), the opening (`ref_dOpenT`), roll 7's simulation.
import LvmMPVEqFol
import LvmMPVEqReloc
import LvmMPSig

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

theorem relocV_eq (x : List UInt8) (c : VStackClaim) :
    relocV relocS x c = (fun w ↦ if Shape.small x then Shape.onStackZ w else w) (relocS c) := rfl

theorem offOK_relay : Shape.OffOK ⟨P20.nuRec, (layout0 P20).s⟩ := by
  rw [layout0_P20]; decide +kernel

theorem layout0_s : (layout0 P20).s = CMain.sOff20 := by rw [layout0_P20]

/-- **V_S's claim list against `ordM` of `assembleT₂`'s relocated pair** (M′, both shapes): where V_S's
`require` held (every claim on `C_main`), its claims, on the statement's shape's stack, are the spec's in
V_S's phase order, the stream claims (the relayout's point claim, `σ′`'s, the `KS` link's `M`) relocated onto
`S`. -/
theorem typedClaimsM_rel (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (x : List UInt8) (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims)
    (hT : TRelT N Q lay t a)
    (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') (hi : ∃ i, kg.2.2 = ((N.m3 P20).ksLink i).2)
    (hall : (t.2.1 ++ dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2).all
      (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.smallP P20 (pubX x))
        (((t.2.1 ++ dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2).filter
          (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordM ((assembleT₂ x a kg').1.map (relocV relocS x)) (assembleT₂ x a kg').2) := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, hrr, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.fits
  set D := dClaimsT (N.m3 P20) P20 (pubX x) busNil t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2 with hD
  set cl := M3.claimsOfEvs N.mbT t.2.2
  have hsx : Shape.smallP P20 (pubX x) = Shape.small x := smallP_P20 x
  have hall' : ∀ e ∈ t.2.1 ++ D, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he], hsx]
  have hok := H.ok
  rw [nuMain_P20] at hok
  -- phases 3–7's claims (`D`), claim for claim
  have hDfst : D.map (fun e ↦ (e.1, e.2.1)) = M3.tableClaimsR N.mbT t.2.2 ++
      ((tapeClaims P20 kg.1.1 kg.1.2.1 (pubX x) ++ keccakClaims (M3.real P20 fun _ ↦ N.mbT).ksBlock
        kg.2.1.2.2.1 kg.2.1.2.2.2).map (.main, ·) ++
        (M3.real P20 fun _ ↦ N.mbT).ksOutputClaims kg.2.1.1 kg.2.1.2.1) ++ kg.2.2 := by
    have htc : (M3.real P20 fun _ ↦ N.mbT).tableClaims (pubX x) t.2.2 = M3.tableClaimsR N.mbT t.2.2 := by
      conv_rhs => rw [← H.sc_eq]
      rfl
    rw [hD, Shape.dClaimsT_fst, m3_eq]
    unfold dClaims
    rw [show busNil.claims = [] from rfl, List.nil_append, htc]
    simp only [List.append_assoc]
  have hpre := dClaims_rel (fun _ ↦ N.mbT) (pubX x) kg kg' hk
  have hDrel : List.Forall₂ CRelM (D.map fun e ↦ (e.1, e.2.1)) (tableClaimsE N.mbT cl ++
      ((tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
        ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1) ++ ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2) := by
    rw [hDfst]
    exact Lk.forall₂_append (Lk.forall₂_append (hcl.imp fun _ _ h ↦ CRel.crelM h) (hpre.imp fun _ _ h ↦ CRel.crelM h))
      hk.2.2
  have hDtail : Shape.small x = true → ∀ e ∈ D, e.1 = .main →
      Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1 := fun hsm ↦ by
    obtain ⟨⟨-, -, -, hwr, hr, hring⟩, -⟩ := hk
    rw [hD, m3_eq]
    exact Shape.tails_main (fun _ ↦ N.mbT) (pubX x) hfc hfh busNil rfl t.2.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2
      hr hwr.2.2.2.2.2.2.1 hwr.2.2.2.2.2.2.2.2.1 hring (by rw [← m3_eq]; exact hi) (of_decide_eq_true hsm)
      (by simp [pubX, pubOf])
  have hDV := forall₂_crelM (s := Shape.small x) hDrel (fun e he ↦ hall' e (List.mem_append_right _ he)) hDtail
  -- the mini-bus's claims are on `C_main`
  have hmbV : ∀ e ∈ M3.tableClaimsR N.mbT t.2.2, e.1 = .main := fun e he ↦ by
    have h1 : e ∈ D.map (fun e ↦ (e.1, e.2.1)) := by
      rw [hDfst]; exact List.mem_append_left _ (List.mem_append_left _ he)
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 h1
    exact hall' e' (List.mem_append_right _ he')
  have hmbE := main_of_crel hcl hmbV
  -- the typed claims
  have hin : Shape.InStack ⟨23, 0⟩ := ⟨le_rfl, rfl, by norm_num⟩
  have hrelay : SCRel (BlockClaim.point ⟨P20.nuRec, (layout0 P20).s⟩ rr vR).onStack
      (relocS (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack) := by
    rw [← relocS_point]
    exact onStack_rel (Lk.point_rel _ _ _ (by rw [nuRec_P20, layout0_s]; rfl) rfl rfl)
  have hsg : SCRel (⟨⟨23, 0⟩, affW N .sigma ry, rv.getD 2 0⟩ : BlockClaim).onStack
      (relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map FE.toExt3)
        ((rv.map FE.toExt3).getD 2 0))) := by
    rw [← regClaim_relocS N Q lay 23 P20.nuRec hok H.hlay hσ, getD_map_toExt3]
    exact regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .sigma 23 (regsOf_dst hok .sigma (.inr (.inr rfl))) ry hry _
  have hcom := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .com 23
    (regsOf_dst hok .com (.inl rfl)) ry hry (rv.getD 0 0)
  have hks := regClaim_rel N Q lay 23 P20.nuRec hok H.hlay .ks 23
    (regsOf_dst hok .ks (.inr (.inl rfl))) ry hry (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      [relocS (BClaim.point ⟨relayRounds, 0⟩ (rr.map FE.toExt3) (FE.toExt3 vR)).onStack,
        relocS (regClaim (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map FE.toExt3)
          ((rv.map FE.toExt3).getD 2 0)),
        regClaim (N.inst Q lay) .com N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 0 0)),
        regClaim (N.inst Q lay) .ks N.off (ry.map FE.toExt3) (FE.toExt3 (rv.getD 3 0))] := by
    rw [ht1]
    unfold typedClaimsN
    rw [nuMain_P20]
    refine .cons (vrel_of hrelay fun _ ↦ ⟨offOK_relay.inStack, (Shape.OffOK.tail offOK_relay).symm⟩)
      (.cons (vrel_of hsg fun _ ↦ ⟨hin, (tail_affW N P20.nuRec hok .sigma (.inr (.inr rfl)) _ _).symm⟩)
        (.cons (vrel_of hcom fun _ ↦ ⟨hin, (tail_affW N P20.nuRec hok .com (.inl rfl) _ _).symm⟩)
          (.cons (vrel_of hks fun _ ↦ ⟨hin, (tail_affW N P20.nuRec hok .ks (.inr (.inl rfl)) _ _).symm⟩) .nil)))
  have hV := forall₂_onStackZsF (Lk.forall₂_append hTV hDV)
  -- the spec's list in V_S's order
  obtain ⟨yE, inE, mE, xE, hK⟩ : ∃ a b c d, ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2 =
      [(.main, a), (.main, b), (.crec, c), (.main, d)] := ⟨_, _, _, _, rfl⟩
  have hpreE : ∀ b ∈ (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
      ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1, b.1 = .main := by
    intro b hb
    simp only [List.mem_append, List.mem_map, ksOutputClaimsE] at hb
    rcases hb with ⟨c, -, rfl⟩ | ⟨l, -, rfl⟩ <;> rfl
  convert hV using 1
  set P := (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map (fun c : BClaim ↦ (Com.main, c)) ++
    ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1 with hP
  have hP1 : ∀ b ∈ (tapeClaimsE kg'.1 (pubX x) ++ keccakClaimsE ksBlk kg'.2.1).map
      (fun c : BClaim ↦ (Com.main, c)), b.1 = .main := fun b hb ↦ hpreE b (List.mem_append_left _ hb)
  have hP2 : ∀ b ∈ ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1, b.1 = .main :=
    fun b hb ↦ hpreE b (List.mem_append_right _ hb)
  have hS : assembleS [] (pubX x) [] kg' =
      ([mE.onStack], P.map (·.2.onStack) ++ [yE.onStack, inE.onStack, xE.onStack]) := by
    unfold assembleS
    dsimp only
    rw [hK, show tableClaimsE [] [] = [] from rfl, List.nil_append, hP]
    have hmc : (Com.main == Com.crec) = false := rfl
    have hcc : (Com.crec == Com.main) = false := rfl
    simp [List.filter_append, List.filter_map, Function.comp_def, ksOutputClaimsE, hmc, hcc]
  have hmb : (N.inst Q lay).mbT = N.mbT := rfl
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (relocV relocS x) = (l.map relocS).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold assembleT₂ typedClaims miniClaims
  rw [hmb, filter_main_self hmbE, filter_crec_nil hmbE, hS, onStackZs_eq_map, hρ, ordM_map]
  congr 1
  rw [hK]
  simp only [List.map_append, inplM_main hmbE, inplM_main hpreE, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.append_assoc]
  have hm : ∀ (a b : VStackClaim) (A B : List VStackClaim) (c d e : VStackClaim),
      a :: b :: (A ++ (B ++ [c, d, e])) = (a :: b :: (A ++ (B ++ [c, d]))) ++ [e] := by intros; simp
  rw [hm, Lvm.ASM.ordM, List.dropLast_concat, List.getLast?_concat]
  simp only [getD_map_toExt3]
  simp [inplM]
  exact ⟨rfl, rfl⟩

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

theorem ret_bindM {α β : Type} (a : α) (f : α → VerifierProgram β) : (VerifierProgram.ret a >>= f) = f a := rfl

/-- `midM` on the typed phases, as one program. -/
theorem midM_midT₂ (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : TInst) (x : List UInt8) :
    Lvm.ASM.midM reloc (midT₂ Ti) x = typedProg Ti (pubX x) >>= fun a ↦ kgProgS (hdX x).s (pubX x).n >>= fun k ↦
      VerifierProgram.ret (Lvm.ASM.ordM ((assembleT₂ x a k).1.map (reloc x)) (assembleT₂ x a k).2) := by
  unfold Lvm.ASM.midM midT₂
  simp only [bind_assoc, ret_bindM]

/-- **Phases 2–7 refine `midM (relocV relocS) (midT₂ Ti)`** under the promise that the folded claim holds: where
every claim is on `C_main` (V_S's `require`), V_S's claims, on the statement's shape's stack, are `midM`'s. -/
theorem ref_dMidTM (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (x : List UInt8) (hacc : (pubX x).accIn.pt.length = phiVars) :
    RefAtP capS occS shpS sig (dMidT P20 N (pubX x)) (Lvm.ASM.midM (relocV relocS) (midT₂ (N.inst Q lay)) x)
      (fun r cl ↦ r.1.all (·.1 == .main) = true →
        List.Forall₂ SCRel (Shape.onStackZsF (Shape.smallP P20 (pubX x)) ((r.1.filter (·.1 == .main)).map (·.2))) cl)
      (fun r ↦ N.phi r.2.pt = r.2.y) := by
  rw [midM_midT₂]
  unfold dMidT
  apply RefAtP.bind (Q := fun t ↦ N.phi t.1.pt = t.1.y)
  · exact fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_dTypedT N Q lay H (pubX x) hacc
  · intro t s h; rw [runD_bind_pure_snd] at h; exact h
  · rintro t a hT -
    refine (RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKg (fun _ ↦ N.mbT) (pubX x) (hdX x).s (pubX_s x)) ?_).toP _
    rintro kg kg' ⟨hk, hi⟩
    exact RefAt.pure fun hall ↦ typedClaimsM_rel N Q lay H hσ x t a hT kg kg' hk hi hall

/-- **V_S's typed decision refines `P_S = PSWithM (midM (relocV relocS) (midT₂ Ti))`** under the promise that its
value (the folded accumulator) passes `Φ_Q` (`decideFT`'s check after the run). -/
theorem ref_decideTM (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (vk c : RecursionFast.Digest) (x : List UInt8) (hacc : (pubX x).accIn.pt.length = phiVars)
    (hpub : pubOf vk c sig = pubX x) :
    RefAtP capS occS shpS sig (decideProgT P20 N vk c)
      (Lvm.ASM.PSWithM (Lvm.ASM.midM (relocV relocS) (midT₂ (N.inst Q lay))) x)
      (fun _ b ↦ b = true) (fun a ↦ N.phi a.pt = a.y) := by
  rw [decideProgT_dTopT]
  unfold dTopT Lvm.ASM.PSWithM
  rw [commitRootUd_mainT]
  refine RefAtP.read_left ?_
  simp only [hpub, smallT_eq]
  -- the cap
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ (monoD_dMidT _ _ _).bind fun _ ↦ (monoD_dOpenT _ _ _).bind fun _ ↦ MonoD.pure _
  · exact (ref_skip (n := nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap) rfl).toP _
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  -- phases 2–7
  apply RefAtP.bind (Q := fun r ↦ N.phi r.2.pt = r.2.y)
  · exact fun _ ↦ (monoD_dOpenT _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_dMidTM N Q lay H hσ x hacc
  · intro r s h; rw [runD_bind_pure] at h; exact h
  rintro r cl h -
  -- the opening
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ MonoD.pure _
  · exact ref_dOpenT _ r.1 cl h
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  exact (RefAt.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) (b := r.2) (a := true) rfl).toP _

end Ref

/-! ## V_S ⇒ S.V at M′ -/

/-- **O5b at M′** (`OpenSM.refines`' form): whenever `VST P20 N` accepts a proof on a log, so does the compiled
verifier of `PSWithM (midM (relocV relocS) (midT₂ (N.inst Q lay)))`. -/
theorem refines_VSTM (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHyp N Q lay) (hσ : SigInS N)
    (hacc : ∀ x, (pubX x).accIn.pt.length = phiVars) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VST P20 N vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWithM (Lvm.ASM.midM (relocV relocS) (midT₂ (N.inst Q lay))))).V c π).runLog L =
        some true := by
  obtain ⟨hl, hr, he, -, -⟩ := H.fits
  intro vk L c π _ h
  exact runLog_of_seq (fun tr ht ↦ refines_seqOfT N _
    (fun sig vk c x hpub ↦ ref_decideTM N Q lay H hσ vk c x (hacc x) hpub)
    (fol_PSTM (relocV relocS) (N.inst Q lay) hl busDepth_P20 hr he) vk c π tr ht) L h

open Lvm.CT Lvm.QTyped Lvm.T Lvm.ASM in
/-- **`LvmCertM20.refinesM20`** (its statement, with `reloc20 = relocV relocS`): `VST P20 NT20` refines the compiled
verifier of `PSWithM (midM (relocV relocS) (midT₂ Ti20))`, from the guard's facts (`σ′` in `S`: `S.sig`, the
guard's `sigInSB`) and `THyp Ti20`. -/
theorem refinesM20L (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWithM (midM (relocV relocS) (midT₂ Ti20)))).V c π).runLog L = some true :=
  refines_VSTM NT20 QB20 layT20 (trefHyp20 S H) S.sig H.acc

end Lvm.VEq
