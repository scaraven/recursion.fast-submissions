-- New for lvm2 (roll 8 = B1, L-H): roll 7's HAR helpers the typed HAR reuses (generic: they name no bus-program constant), split out of
-- `LvmQAsmHarMain` (unchanged text) so that the typed HAR (`LvmQTypedHar*`) reads them without the bus phases'
-- proofs: `PhaseAt` from `Replays`, the `E` constants, `M3.real` as `ofParts`, `n'`'s bits, the tape's claims and
-- their tails as cells, the claims with tails (`noDR`, `list_eq_of_proj`, `claimsT_proj`), the bus gadget's output
-- cells (`busV`, `busR_eq`, `busG_fst`, which the mini-bus reuses).
import LvmQAsmHarP47
import LvmQAsmHarShape
import LvmQAsmHarIn
import LvmQShapeH

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- A `Replays` fact and the gadget's `Ok` give a `PhaseAt` fact, the value read off `R`. -/
theorem phaseAt_of {α β : Type} {c : Ctx} {M : Mem} {sig : ByteArray} {F : DM α} {g : BM β} {ptr : Ptr}
    {P P' : Nat} {R : α → β → Prop} {v : α} (h : Replays c M sig F g ptr P P' R)
    (hok : Lvm.QSig.Ok c M g ptr) (hv : ∀ a, R a (g ptr).1 → a = v) : PhaseAt F sig P P' v :=
  fun s hs hsok => by
    obtain ⟨h1, h2, h3⟩ := h hok s hs hsok
    exact ⟨hv _ h3, h1, h2⟩

/-- The `E` constant `k'` from any cell `x` (`x + 1·x + k'`). -/
theorem constE_val {c : Ctx} {M : Mem} {k' : FK} {x : Cell} {p : Ptr}
    (h : SegsHold c M p (const .E k' x p).2) : (const .E k' x p).1.val M = FE.ofK k' := by
  have e := lin_spec (c := c) (M := M) (p := p) (τ := .E) (k := 1) (k' := k') (a := x) (b := x) h
  show (lin .E 1 k' x x p).1.val M = _
  rw [e, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

theorem real_eq (p : Params) (ts : Pub → List M3.Tab) :
    M3.real p ts = M3.ofParts p (fun i => M3.busFinalR (M3.sumcheckTabs (ts i.pub)) i)
      (fun pub => (M3.sumcheckTabs (ts pub)).map M3.nativeTable)
      (fun pub => M3.tableClaimsR (M3.sumcheckTabs (ts pub)))
      (fun pub => M3.fixValsR (M3.sumcheckTabs (ts pub)) p.pubTab)
      (fun pub => M3.fixSentR (M3.sumcheckTabs (ts pub)) p.pubTab)
      (fun pub => M3.pubCheckR p.pubTab pub) := rfl

theorem bitE_out1 {v : Nat → FK} {w nb j : Nat} (hj : j < 64) (h : Lvm.QSig.Out1 v w (.bit j) (nb + j)) :
    FE.ofK (v (nb + j)) = bitE (v w).val.toNat j := by
  rw [h, Lvm.QSig.w64, bit_word _ hj, bitE]
  split_ifs <;> rfl

/-- **The tape's claims as cells are T-V's `tapeClaims`** on the phases' values (`TW`), the header lanes
`h'` the stream's (`pub_h`). -/
theorem tapeClaimsC_val (C : QCfg) {M : Mem} {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) {oP : P47Out}
    {tp : TapeRes} {wo : WireOut} {pub : Pub} (htw : TW C M oP pub tp wo) (hvl : oP.v.length = 25)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) :
    (tapeClaimsC C.p z o oP).map (CClaim.val M) = (tapeClaims C.p tp wo pub).map (.main, ·) := by
  obtain ⟨hr, hv, -, hsc, hsl, hring, hmb⟩ := htw
  have e4 : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [tapeClaimsC, tapeClaims, dLanes, e4, hh, List.map_cons, List.map_nil, List.zipIdx_cons,
    List.zipIdx_nil, List.cons_append, List.nil_append, CClaim.val, vs_append, selC_vs hz ho, hr, hv, hmb,
    hring, hsc, hsl, vs_getD M oP.v (show 0 < oP.v.length by omega), vs_getD M oP.v (show 1 < oP.v.length by omega),
    vs_getD M oP.v (show 2 < oP.v.length by omega), vs_getD M oP.v (show 3 < oP.v.length by omega)]
  rfl

/-- A claim whose tail is `0` by its form (no `D` point claim, no ring claim on `⟨CMain.nu20, 0⟩`). -/
def noDR (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk _ => blk != ⟨22, 0⟩
  | .ring blk _ _ => blk != ⟨CMain.nu20, 0⟩
  | .sum _ _ => true

theorem tailC_noDR {M : Mem} (cc : CClaim) (h : noDR cc = true) : Lvm.QShape.tailC M cc = 0 := by
  rcases cc with ⟨com, cw, v⟩
  cases cw <;> simp_all [noDR, Lvm.QShape.tailC]

theorem list_eq_of_proj (l₁ l₂ : List (Com × BlockClaim × FE))
    (h1 : l₁.map (fun e => (e.1, e.2.1)) = l₂.map (fun e => (e.1, e.2.1))) (h2 : l₁.map (·.2.2) = l₂.map (·.2.2)) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h1
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h1 h2
      obtain ⟨a1, a2, a3⟩ := a
      obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at h1 h2
      rw [h1.1.1, h1.1.2, h2.1, ih l' h1.2 h2.2]

theorem claimsT_proj {M : Mem} (cs : List CClaim) : (claimsT M cs).map (fun e => (e.1, e.2.1)) = cs.map (CClaim.val M) := by
  rw [claimsT, List.map_map]; rfl

theorem zeroTails_tails (l : List (Com × BlockClaim)) :
    (Lvm.Shape.zeroTails l).map (·.2.2) = List.replicate l.length 0 := by
  rw [List.eq_replicate_iff]
  simp only [Lvm.Shape.zeroTails, List.map_map, List.length_map, true_and]
  intro b hb
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hb
  rfl

theorem map_tailC_zero {M : Mem} (l : List CClaim) (h : l.all noDR = true) :
    l.map (Lvm.QShape.tailC M) = List.replicate l.length 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun t ht => ?_⟩
  obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp ht
  exact tailC_noDR cc (List.all_eq_true.mp h cc hcc)

/-- **The tape's tails as cells are `V_S`'s** (`tapeTails`) when the child is small. -/
theorem tapeTails_eq (C : QCfg) {M : Mem} {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) {oP : P47Out}
    {tp : TapeRes} {wo : WireOut} {pub : Pub} (htw : TW C M oP pub tp wo) (hrl : oP.r.length = 20)
    (hστ : (oP.wire.sigma ++ oP.wire.tau).length = 22) (hh : pub.h.length = 4)
    (hsm : Lvm.Shape.smallP C.p pub = true) (hD : Lvm.dBlock C.p = ⟨22, 0⟩) (hds : dSel C.p = 0)
    (hn1 : 1 ≤ pub.n) :
    (tapeClaimsC C.p z o oP).map (Lvm.QShape.tailC M) =
      Lvm.Shape.tapeTails C.p tp wo (vs M oP.wire.ring.cs) pub := by
  obtain ⟨hr, -, -, hsc, hsl, -, hmb⟩ := htw
  simp only [Lvm.Shape.smallP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsm
  obtain ⟨⟨hlog, hnu⟩, hsmall⟩ := hsm
  have hdb : dSelBits C.p = 1 := by simp [dSelBits, hlog, hnu]; rfl
  have e4 : List.range 4 = [0, 1, 2, 3] := rfl
  have hvr : (vs M oP.r).length = 20 := by simp [vs, hrl]
  have hph : pub.h.map (fun _ => (0 : FE)) = [0, 0, 0, 0] := by
    rw [List.map_const', hh]; rfl
  have tD : ∀ l < 4, Lvm.QShape.tailC M ⟨.main, .point (Lvm.dBlock C.p) (oP.r ++ selC z o l 2), oP.v.getD l default⟩ =
      Lvm.Shape.tailDF tp.r l := fun l hl => by
    simp only [Lvm.QShape.tailC, hD, if_true, vs_append, selC_vs hz ho, hr]
    exact Lvm.QShape.tailD_pt _ hvr l hl
  have tB : ∀ l < 4, Lvm.QShape.tailC M ⟨.main, .point (Lvm.dBlock C.p) (oP.mb ++ selC z o l 2), kc (hLane l)⟩ = 0 :=
    fun l _ => by
      simp only [Lvm.QShape.tailC, hD, if_true, vs_append, selC_vs hz ho, hmb, hlog]
      exact Lvm.QShape.tailD_bnd _ (by simp [CMain.smallLogN20] at hsmall; omega) l
  have tR : Lvm.QShape.tailC M ⟨.main, .ring ⟨C.p.nuMain, 0⟩ (oP.wire.sigma ++ oP.wire.tau ++
      selC z o (dSel C.p) (dSelBits C.p)) oP.wire.ring.cs, oP.wire.ring.target⟩ =
      Lvm.Shape.ringTailN (Lvm.Shape.wirePt C.p wo) (vs M oP.wire.ring.cs) := by
    simp only [Lvm.QShape.tailC, hnu, if_true, vs_append, selC_vs hz ho, Lvm.Shape.wirePt, hsc, hsl]
    have hl : (vs M oP.wire.sigma ++ vs M oP.wire.tau).length = 22 := by
      simpa [vs] using hστ
    rw [hds, hdb]
    refine Lvm.QShape.tailR_eq _ _ (by
      show _ = 23; simp only [List.length_append, Lvm.QShape.selectorPoint_length'] at hl ⊢; omega) ?_
    rw [List.drop_left' hl]
    show selectorPoint 0 1 = List.replicate 1 0
    simp [selectorPoint, eOfNat_zero]
  simp only [tapeClaimsC, Lvm.Shape.tapeTails, dLanes, e4, hph, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.singleton_append]
  rw [tD 0 (by norm_num), tD 1 (by norm_num), tD 2 (by norm_num), tD 3 (by norm_num), tR, tB 0 (by norm_num),
    tB 1 (by norm_num), tB 2 (by norm_num), tB 3 (by norm_num)]

theorem ldEs_fst (st : Nat) : ∀ (n a : Nat) (p : Ptr),
    (Lvm.Har.ldEs a st n p).1 = (List.range n).map fun i => ec (p.e + i)
  | 0, _, _ => rfl
  | n + 1, a, p => by
    simp only [Lvm.Har.ldEs, bind_apply, pure_apply]
    rw [ldE_adv, ldEs_fst st n (a + st) ⟨p.k, p.e + 1⟩, ldE_apply, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    exact List.map_congr_left fun i _ => by simp only [Function.comp_apply]; congr 1; omega

/-- The bus phase's value: the output cells' values, one zero leaf-decomposition scalar. -/
def busV (M : Mem) (b : BusC) : List FE × FE × FE × List FE × List FE × List FE :=
  (vs M b.al, b.be.val M, b.cnt.val M, vs M b.pt, vs M b.vals, [0])

theorem busR_eq {M : Mem} {res : List FE × FE × FE × List FE × List FE × List FE} {b : BusC}
    (h : BusR M res b) : res = busV M b ∧ (vs M b.vals).length = 3 := by
  obtain ⟨a, b', c', d, e, f⟩ := res
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6
  exact ⟨rfl, h7⟩

theorem busG_fst (p : Params) (z o g : Cell) (P : Nat) (ptr : Ptr) :
    (busG p z o g P ptr).1.al = (List.range busBits).map (fun i => ec (ptr.e + i)) ∧
      ∃ d : PD, (busG p z o g P ptr).1.pt = d.cells := by
  simp only [busG, bind_apply, pure_apply]
  exact ⟨ldEs_fst _ _ _ _, _, rfl⟩

end Lvm.Har
