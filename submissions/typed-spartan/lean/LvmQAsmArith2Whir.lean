-- New for lvm (HAR-WH): Q_arith phases 8–9: one stacked WHIR opening (`stackGW`, `stack_run`) and
-- `openPh`'s two (`openG`, `openPh_replays`: `C_rec`, then `C_main`). Lvm2 roll 8 (wave L): the gadgets' definitions
-- (`stackGW`, `stackGZ`, `openG`, …) are in `LvmQAsmArith2WhirD`, off the B program's build path; the proofs stay here.
import LvmQAsmArith2WhirD
import LvmQAsmArith2WhirLS
import LvmQAsmArith2WhirBasis
import LvmQShapeB

/-!
# Phases 8–9: the stacked WHIR openings

**`stackGW C cl zc oc g`** is `F`'s `verifyStackedOpening C.levels C.nu (cl.map onStack) false` for
the claims `cl` of one commitment (cells `CClaim`): every fold and tail challenge loaded from the
stream (`preloadG`, `chLanes`' order), the batching challenge `s` and its powers, the target
`Σ s^i v_i` (`targetG`), the basis point (the challenges rotated by the first fold, `copiesG`), the
batched weight `Σ s^i onStack_i(x)` (`basisG`), `verifyWhir`'s first polynomial, the levels
(`levelsG`). **`stack_run`**: wherever it holds and asserts (gate on), `F` from any state at
position `8 U` keeps `ok`, ends at `8 · stackEndL`, `msg = 0`.

**`openPh_replays`**: `openG Cr Cm cs` (`stackGW` on `cs`' `C_rec` claims, then on its `C_main`
claims) replays `openPh p (cs.map (CClaim.val M))` (`Replays`, LvmQAsmHarBase), `C_main` starting
where `C_rec` ends. Hypotheses: the stream (`Streamed`), the static checks (`StackOk`, decidable),
the zero/one/gate cells, the positions (`PosOk`: position `j` of level `i` is the `K` cell
`pb i + j` holding `eOfNat` of `F`'s `j`-th position, `qsAt`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {c : Ctx} {M : Mem}

theorem xs_eq {pc ν lf xb : Nat} (hlf : lf ≤ ν)
    (h : ∀ i < (((List.range ν).map fun k => ec (pc + k)).drop lf ++
      ((List.range ν).map fun k => ec (pc + k)).take lf).length,
      M.e (xb + i) = ((((List.range ν).map fun k => ec (pc + k)).drop lf ++
        ((List.range ν).map fun k => ec (pc + k)).take lf).getD i default).val M) :
    (List.range ν).map (fun i => M.e (xb + i)) = (ptv M pc ν).drop lf ++ (ptv M pc ν).take lf := by
  have hc : ((((List.range ν).map fun k => ec (pc + k)).drop lf ++
      ((List.range ν).map fun k => ec (pc + k)).take lf)).map (Cell.val M) =
      (ptv M pc ν).drop lf ++ (ptv M pc ν).take lf := by
    rw [List.map_append, List.map_drop, List.map_take, List.map_map]; rfl
  rw [← hc]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_map, h i (by simp; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- **One generic stacked opening replays `F`'s `verifyStackedOpening`** on any claim list `scs` whose batched
values the target and the basis gadgets give. -/
theorem stackG_run {β : Type} (C : SCfg) (n : Nat) (pre : BM β) (tg : β → Nat → BM Cell)
    (bg : β → Nat → Nat → BM Cell) (W : β → Prop) (scs : List StackClaim) (hn : scs.length = n)
    (hpre : Hs c M pre W)
    (htg : ∀ w, W w → ∀ (sp : Nat) (s : FE), (∀ i < n, M.e (sp + i) = s ^ i) →
      Hs c M (tg w sp) (fun t => t.val M = Lvm.dot (powers s n) (scs.map (·.2))))
    (hbg : ∀ w, W w → ∀ (sp xb : Nat) (s : FE), (∀ i < n, M.e (sp + i) = s ^ i) →
      Hs c M (bg w sp xb) (fun b => b.val M =
        Lvm.dot (powers s n) (scs.map fun sc => sc.1 ((List.range C.nu).map fun i => M.e (xb + i)))))
    (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk C T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGWG C n pre tg bg zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.msg = 0 := by
  simp only [LayOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨hlv, hch⟩, hU⟩, hlf⟩ := hok
  replace hU := of_decide_eq_true hU
  replace hlf := of_decide_eq_true hlf
  simp only [stackGWG] at h
  -- the shape and the muxed claims
  obtain ⟨h0, h⟩ := okb h
  have hw := hpre p h0.1
  have hp0 := le_trans hp (adv_e_le p (pre p).2)
  generalize (pre p).1 = w at h hw
  generalize p.adv (pre p).2 = p at h hp0
  clear hp
  -- the challenges
  obtain ⟨h1, h⟩ := okb h
  obtain ⟨epc, ech⟩ := preloadG_spec hS (fun v hv => of_decide_eq_true (hch v hv)) h1.1
  rw [epc] at h
  have hp1 := le_trans hp0 (adv_e_le p (preloadG (chLanes C.g C.ood C.levels (C.U + 15)) p).2)
  generalize p.adv (preloadG (chLanes C.g C.ood C.levels (C.U + 15)) p).2 = p1 at h hp1
  -- the batching challenge and its powers
  obtain ⟨h2, h⟩ := okb h
  have esb := ldE_spec hS (by omega) h2.1
  rw [ldE_out] at esb h
  rw [ldEW_adv] at h
  have esb' : M.e p1.e = feAt sig (8 * C.U + 40) := by
    rw [show 8 * C.U + 40 = 8 * (C.U + 5) by ring]; exact esb
  obtain ⟨h3, h⟩ := okb h
  have e3 := pows_spec h3.1 hz ho hoE
  have hsp : ∀ i < n,
      M.e ((pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + i) =
        feAt sig (8 * C.U + 40) ^ i := fun i hi => by
    rw [e3 i (le_trans hi.le (Nat.le_pow_clog (by norm_num) _)), Cell.val_E, esb']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by show 1 ≤ p1.e + 1; omega) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = sp at h hsp
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3
  -- the target
  obtain ⟨h4, h⟩ := okb h
  have et := htg w hw sp _ hsp p3 h4.1
  have hp4 := le_trans hp3 (adv_e_le p3 (tg w sp p3).2)
  generalize (tg w sp p3).1 = tgt at h et
  generalize p3.adv (tg w sp p3).2 = p4 at h hp4
  -- the basis point and the basis
  obtain ⟨h5, h⟩ := okb h
  obtain ⟨exb, ecp⟩ := copiesG_spec (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hx); rfl
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx); rfl) h5.1
  have hxs := xs_eq (M := M) hlf ecp
  rw [exb] at h
  have hp5 : 1 ≤ (p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2).e :=
    le_trans hp4 (adv_e_le _ _)
  generalize p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2 = p5 at h hp5
  obtain ⟨h6, h⟩ := okb h
  have eb := hbg w hw sp p4.e _ hsp p5 h6.1
  rw [hxs] at eb
  have hp6 := le_trans hp5 (adv_e_le p5 (bg w sp p4.e p5).2)
  generalize (bg w sp p4.e p5).1 = bas at h eb
  generalize p5.adv (bg w sp p4.e p5).2 = p6 at h hp6
  -- the `K` zero cell
  obtain ⟨h7, h⟩ := okb h
  have ez := lin_spec (τ := .K) (k := 1) (k' := 0) (a := g) (b := g) h7.1
  have hzk : M.k p6.k = 0 := by
    rw [show (lin .K 1 0 g g p6).1 = kc p6.k from rfl, Cell.val_K, hg, ofK_one, ofK_zero, one_mul,
      add_zero, CharTwo.add_self_eq_zero] at ez
    exact ofK_inj (ez.trans ofK_zero.symm)
  have hp7 := le_trans hp6 (adv_e_le p6 (const .K 0 g p6).2)
  rw [show (const .K 0 g p6).1 = kc p6.k from rfl] at h
  generalize p6.adv (const .K 0 g p6).2 = p7 at h hp7
  -- `verifyWhir`'s first polynomial
  obtain ⟨h8, h⟩ := okb h
  have eq0 := rdQ_spec hS (by omega) h8.1
  have hp8 := le_trans hp7 (adv_e_le p7 (rdQ (C.U + 9) tgt p7).2)
  generalize (rdQ (C.U + 9) tgt p7).1 = q at h eq0
  generalize p7.adv (rdQ (C.U + 9) tgt p7).2 = p8 at h hp8
  -- `F`
  simp only [verifyStackedOpening, verifyWhir]
  rw [dm_bind, sampleE_run]
  dsimp only
  rw [dm_bind, srp3_run]
  dsimp only
  refine levels_run C hS p.e zc oc g p6.k bas hz ho hzE hoE hg hgK hzk C.lf _ ?_ C.levels 0 0 (C.U + 15)
    q [] _ p8 hlv hp8 ?_ (by simp) (fun j hj => by rw [Nat.add_zero]; exact ech j hj) hpos hpw
    ⟨by simp, by simp⟩ h _ ?_
  · rw [eb, hs, hn]
  · rw [eq0, et, pos_mk0, hs, hn, show 8 * (C.U + 9) = 8 * C.U + 72 by ring]
  · simp only [pos] at hs ⊢; omega

set_option maxHeartbeats 1000000 in
/-- **One stacked opening replays `F`'s `verifyStackedOpening`.** -/
theorem stack_run (C : SCfg) (cl : List CClaim) (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : StackOk C cl T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGW C cl zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2.msg = 0 := by
  simp only [StackOk, Bool.and_eq_true] at hok
  unfold stackGW at h
  have e1 : (cl.map fun cc => (cc.val M).2.onStack).map (·.2) = cl.map fun cc => (cc.val M).2.value := by
    rw [List.map_map]; rfl
  have hn : (cl.map fun cc => (cc.val M).2.onStack).length = cl.length := List.length_map _
  have htg : ∀ (w : Unit), True → ∀ (sp : Nat) (σ : FE), (∀ i < cl.length, M.e (sp + i) = σ ^ i) →
      Hs c M (targetG cl sp zc) (fun t => t.val M =
        Lvm.dot (powers σ cl.length) ((cl.map fun cc => (cc.val M).2.onStack).map (·.2))) :=
    fun _ _ sp σ hsp p' h' => by rw [e1]; exact targetG_spec h' hz σ hsp
  have hbg : ∀ (w : Unit), True → ∀ (sp xb : Nat) (σ : FE), (∀ i < cl.length, M.e (sp + i) = σ ^ i) →
      Hs c M (basisG C.nu cl sp xb zc oc g) (fun b => b.val M = Lvm.dot (powers σ cl.length)
        ((cl.map fun cc => (cc.val M).2.onStack).map fun sc => sc.1 ((List.range C.nu).map fun i => M.e (xb + i)))) :=
    fun _ _ sp xb σ hsp p' h' => by rw [List.map_map]; exact basisG_spec h' hok.2 hz ho hzE hoE hgK σ hsp
  have k1 := stackG_run (β := Unit) (c := c) (M := M) C cl.length (pure ()) (fun _ sp => targetG cl sp zc)
    (fun _ sp xb => basisG C.nu cl sp xb zc oc g) (fun _ => True) (cl.map fun cc => (cc.val M).2.onStack) hn
    (fun _ _ => trivial) htg hbg zc oc g hS
  have k2 := k1 hok.1 hz ho hzE hoE hg hgK hpos hpw hp h s hs
  exact k2

/-! ## `C_main`'s opening in both shapes (roll 7, SH2-Z; CR-Q) -/

section Z

open Lvm.QShape Lvm.Shape

theorem fa2_mem {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | [], [], _, _, h => absurd h (by simp)
  | a :: l₁, b' :: l₂, .cons hab hr, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', hr'⟩ := fa2_mem hr b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

theorem rotZ_getD (X : List FE) (hX : X.length = CMain.nu20) {i : Nat} (hi : i < CMain.nu20) :
    (rotZ X).getD i 0 = X.getD ((i + 1) % CMain.nu20) 0 := by
  have hnu : CMain.nu20 = 23 := rfl
  cases X with
  | nil => simp at hX
  | cons x0 xt =>
    have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hX; omega
    simp only [rotZ, List.tail_cons, List.headD_cons]
    by_cases h : i < CMain.nu20 - 1
    · rw [getD_append_lo (by omega), Nat.mod_eq_of_lt (by omega : i + 1 < CMain.nu20)]; rfl
    · have e : i = xt.length + 0 := by omega
      rw [e, getD_append_hi, show xt.length + 0 + 1 = CMain.nu20 by omega, Nat.mod_self]; rfl

/-- The muxed values of the claims are the stack claims' values on the shape's stack. -/
theorem tgt_list (b : Bool) {s : Cell} (hsv : s.val M = if b then 1 else 0) :
    ∀ (cl : List CClaim) (zs : List (CClaim × Bool)), List.Forall₂ (ZRel M s) cl zs →
      (zs.map (·.1)).map (fun cc => (cc.val M).2.value) =
        (onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))).map (·.2)
  | [], [], _ => by cases b <;> simp [onStackZsF]
  | cc :: cl, r :: zs, .cons hr hrs => by
    have ih := tgt_list b hsv cl zs hrs
    cases b
    · simp only [onStackZsF, Bool.false_eq_true, if_false] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      rw [cval_value, hr.value, hsv]
      simp only [Bool.false_eq_true, if_false, zero_mul, add_zero, Function.comp_apply]
      show _ = (cc.val M).2.value
      rw [cval_value]
    · simp only [onStackZsF, if_true] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      rw [cval_value, hr.value, hsv]
      simp only [if_true, one_mul, Function.comp_apply, onStackZB]
      rw [cval_value, CharTwo.sub_eq_add]

theorem bas_list (b : Bool) {s : Cell} (hsv : s.val M = if b then 1 else 0) (X : List FE)
    (hX : X.length = CMain.nu20) :
    ∀ (cl : List CClaim) (zs : List (CClaim × Bool)), List.Forall₂ (ZRel M s) cl zs →
      zs.map (if b then wSml M (rotZ X) else wBig M X) =
        (onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))).map fun sc => sc.1 X
  | [], [], _ => by cases b <;> simp [onStackZsF]
  | cc :: cl, r :: zs, .cons hr hrs => by
    have ih := bas_list b hsv X hX cl zs hrs
    cases b
    · simp only [onStackZsF, Bool.false_eq_true, if_false] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      simp only [Function.comp_apply, wBig]
      by_cases h2 : r.2 = true
      · rw [hr.reg h2]
      · exact hr.big (by simpa using h2) (by rw [hsv]; rfl) X hX
    · simp only [onStackZsF, if_true] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      simp only [Function.comp_apply, wSml]
      have hsm := hr.small (by rw [hsv]; rfl) X hX
      by_cases h2 : r.2 = true
      · rw [if_pos h2] at hsm ⊢; rw [hr.reg h2]; exact hsm
      · rw [if_neg h2] at hsm ⊢; exact hsm

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening in both shapes replays `F`'s** on `V_S`'s stack claims `onStackZsF b` of the claims
with their tails (`b`: the child is small; `σ'` holds `1` iff `b`). -/
theorem stackZ_run (C : SCfg) (cl : List CClaim) (mb : List Cell) (zc oc g : Cell) (b : Bool)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (hν : C.nu = CMain.nu20) (hwf : ClaimsWF CMain.nu20 cl = true) (hzw : ∀ cc ∈ cl, ZWF zc cc = true)
    {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk C T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGZ C cl mb zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    let scs := onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.msg = 0 := by
  intro scs
  have hlen : scs.length = cl.length := by cases b <;> simp [scs, onStackZsF]
  have hwf1 : ∀ cc ∈ cl, WF1 CMain.nu20 cc = true := by simpa [ClaimsWF, List.all_eq_true] using hwf
  refine stackG_run C cl.length _ _ _
    (fun w => (w.1.val M = if b then 1 else 0) ∧ List.Forall₂ (ZRel M w.1) cl w.2) scs hlen ?_ ?_ ?_
    zc oc g hS hok hz ho hzE hoE hg hgK hpos hpw hp h s hs
  · exact hs_bind (sigmaG_spec hz) fun σ hσv =>
      hs_bind (zClaimsG_spec hz ho cl hzw) fun zs hzs => hs_pure ⟨by rw [hσv, hσ], hzs⟩
  · intro w ⟨hsv, hrel⟩ sp σ hsp p' h'
    have hl : (w.2.map (·.1)).length = cl.length := by simp [hrel.length_eq.symm]
    rw [targetG_spec h' hz σ (fun i hi => hsp i (by rw [← hl]; exact hi)), hl, tgt_list b hsv cl w.2 hrel]
  · intro w ⟨hsv, hrel⟩ sp xb σ hsp
    have hl : w.2.length = cl.length := hrel.length_eq.symm
    have hX : ((List.range C.nu).map fun i => M.e (xb + i)).length = CMain.nu20 := by simp [hν]
    refine hs_bind (muxPtG_spec w.1 xb (List.range CMain.nu20)) fun ms ⟨hml, hmE, hmv⟩ => ?_
    have hcp : Hs c M (copiesG ms) (fun xs => ∀ i < CMain.nu20, M.e (xs + i) = (ms.getD i default).val M) :=
      fun p' h' => by
        obtain ⟨e1, e2⟩ := copiesG_spec hmE h'
        rw [e1]; exact fun i hi => e2 i (by rw [hml]; simpa using hi)
    have hw : ∀ e ∈ w.2, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1) := by
      intro e he
      obtain ⟨cc, hcc, hr⟩ := fa2_mem hrel e he
      refine ⟨hr.wf (hwf1 cc hcc), fun h2 => ?_⟩
      rw [hr.reg h2]; exact hr.regC h2
    refine hs_bind hcp fun xs hxs =>
      hs_mono (basisZ_spec hz ho hzE hw σ (fun j hj => hsp j (by rw [← hl]; exact hj))) fun bv hbv => ?_
    rw [hbv]
    set X := (List.range C.nu).map fun i => M.e (xb + i) with hXd
    have hXl : X.length = CMain.nu20 := hX
    have hXg : ∀ i < CMain.nu20, X.getD i 0 = M.e (xb + i) := fun i hi => by
      simp [hXd, List.getD_eq_getElem?_getD, List.getElem?_map, hν, hi]
    have hxs' : xsOf M CMain.nu20 xs = if b then rotZ X else X := by
      refine list_ext_getD _ _ (by cases b <;> simp [xs_length, hXl, rotZ_length X hXl]) fun i hi => ?_
      rw [xs_length] at hi
      have hm := hmv i (by simpa using hi)
      have hrN : (List.range CMain.nu20).getD i 0 = i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
      rw [hrN] at hm
      rw [xs_getD hi, hxs i hi, hm, hsv]
      cases b
      · simp only [Bool.false_eq_true, if_false, mux_zero]; rw [hXg i hi]
      · simp only [if_true, mux_one]; rw [rotZ_getD X hXl hi, hXg _ (Nat.mod_lt _ (by decide))]
    have hsl : (scs.map fun sc => sc.1 X).length = cl.length := by rw [List.length_map, hlen]
    rw [← hsl, dot_powers_bsum, hsv, hxs']
    cases b
    · simp only [Bool.false_eq_true, if_false, mux_zero]
      rw [← bas_list false (by rw [hsv]) X hXl cl w.2 hrel]
      rfl
    · simp only [if_true, mux_one]
      rw [← bas_list true (by rw [hsv]) X hXl cl w.2 hrel]
      rfl

end Z

/-! ## Phases 8–9 -/

theorem on_eq (cs : List CClaim) (com : Com) :
    ((cs.map (CClaim.val M)).filter (·.1 == com)).map (·.2.onStack) =
      (onCom cs com).map fun cc => (cc.val M).2.onStack := by
  rw [List.filter_map, List.map_map]; rfl

theorem claimsT_rec (cs : List CClaim) :
    ((claimsT M cs).filter (·.1 == .crec)).map (·.2.1.onStack) = (onCom cs .crec).map fun cc => (cc.val M).2.onStack := by
  rw [claimsT, onCom, List.filter_map, List.map_map]; rfl

theorem claimsT_main (cs : List CClaim) :
    ((claimsT M cs).filter (·.1 == .main)).map (·.2) =
      (onCom cs .main).map fun cc => ((cc.val M).2, Lvm.QShape.tailC M cc) := by
  rw [claimsT, onCom, List.filter_map, List.map_map]; rfl

/-- The child's shape cell: `σ' = 1` iff `n' ≤ 2^18` (its bits `m = n' − 1`, `1 ≤ n' ≤ 2^20`). -/
theorem sigma_val (mb : List Cell) (n : Nat) (hmb : vs M mb = selectorPoint (n - 1) 20) (hn1 : 1 ≤ n)
    (hnN : n ≤ 2 ^ 20) :
    (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (n ≤ 2 ^ 18) then 1 else 0 := by
  have hl : mb.length = 20 := by simpa [vs, selectorPoint] using congrArg List.length hmb
  have g : ∀ i < 20, (mb.getD i default).val M = eOfNat (((n - 1) >>> i) % 2) := fun i hi => by
    rw [Lvm.QShape.vs_getD' mb i (by omega), hmb, Lvm.QShape.selectorPoint_getD' hi]
  rw [g 18 (by norm_num), g 19 (by norm_num), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h18 : (n - 1) / 2 ^ 18 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h19 : (n - 1) / 2 ^ 19 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases hs : n ≤ 2 ^ 18
  · rw [show (n - 1) / 2 ^ 18 % 2 = 0 by omega, show (n - 1) / 2 ^ 19 % 2 = 0 by omega]
    have hs' : n ≤ 262144 := hs
    simp [hs', eOfNat_zero]
  · rw [if_neg (by simpa using hs)]
    rcases Nat.lt_or_ge ((n - 1) / 2 ^ 18 % 2) 1 with h | h
    · rw [show (n - 1) / 2 ^ 18 % 2 = 0 by omega, show (n - 1) / 2 ^ 19 % 2 = 1 by omega]
      simp [eOfNat_zero, eOfNat_one, CharTwo.add_self_eq_zero]
    · rw [show (n - 1) / 2 ^ 18 % 2 = 1 by omega]
      simp [eOfNat_one, CharTwo.add_self_eq_zero]

/-- **Phases 8–9 run** (roll 7): `F`'s `openPhZ` (`V_S`'s `dOpenZ` at the child's `smallP`) on the cells' claims
with their tails, from any state at position `8 Cr.U`, keeps `ok`, ends at `8 · stackEndL` of `C_main`, `msg = 0`. -/
theorem openPhZ_run (p : Params) (pub : Pub) (Cr Cm : SCfg) (zon : Bool) (cs : List CClaim) (mb : List Cell)
    (zc oc g : Cell) {sig : ByteArray}
    {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hr : Cr.levels = p.recLevels) (hrν : Cr.nu = p.nuRec)
    (hm : Cm.levels = p.mainLevels) (hmν : Cm.nu = p.nuMain) (hrg : Cr.g = p.grind) (hro : Cr.ood = p.recOod)
    (hmg : Cm.g = p.grind) (hmo : Cm.ood = p.mainOod)
    (hzon : zon = (p.logN == 20 && p.nuMain == CMain.nu20))
    (hσ : zon = true → (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : zon = true → ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF zc cc = true)
    (hU : Cm.U = stackEndL Cr.g Cr.ood Cr.levels (Cr.U + 15)) (hlr : LayOk Cr T = true) (hlm : LayOk Cm T = true)
    (hwr : ClaimsWF Cr.nu (onCom cs .crec) = true)
    (hwm : ClaimsWF Cm.nu (onCom cs .main) = true) (hz : zc.val M = 0) (ho : oc.val M = 1)
    (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hposr : PosOk Cr M sig 0 Cr.levels (Cr.U + 15)) (hposm : PosOk Cm M sig 0 Cm.levels (Cm.U + 15))
    (hpwr : PwOk Cr M 0 Cr.levels) (hpwm : PwOk Cm M 0 Cm.levels) {ptr : Ptr} (hp : 1 ≤ ptr.e)
    (h : Lvm.QSig.Ok c M (openG Cr Cm zon cs mb zc oc g) ptr) (s : RS) (hs : pos s = 8 * Cr.U) :
    (openPhZ p pub (claimsT M cs) sig s).2.ok = s.ok ∧
    pos (openPhZ p pub (claimsT M cs) sig s).2 = 8 * stackEndL p.grind p.mainOod Cm.levels (Cm.U + 15) ∧
    (openPhZ p pub (claimsT M cs) sig s).2.msg = 0 := by
  simp only [openG] at h
  obtain ⟨h1, h2⟩ := okb h
  simp only [openPhZ, Lvm.Shape.dOpenZ]
  rw [dm_bind, claimsT_rec, claimsT_main, ← hr, ← hrν, ← hm, ← hmν]
  obtain ⟨o1, p1, -⟩ := stack_run Cr _ zc oc g hS (by simp [StackOk, hlr, hwr]) hz ho hzE hoE hg hgK
    hposr hpwr hp h1 s hs
  rw [hrg, hro] at o1 p1
  rw [hrg, hro] at hU
  have hp2 := le_trans hp (adv_e_le ptr (stackGW Cr (onCom cs .crec) zc oc g ptr).2)
  have hzp : zon = true → p.logN = 20 ∧ p.nuMain = CMain.nu20 := fun hz' => by
    rw [hz'] at hzon; simpa using hzon.symm
  by_cases hz' : zon = true
  · rw [if_pos hz'] at h2
    have hsm : Lvm.Shape.smallP p pub = decide (pub.n ≤ 2 ^ CMain.smallLogN20) := by
      obtain ⟨e1, e2⟩ := hzp hz'
      simp [Lvm.Shape.smallP, e1, e2]
    rw [hsm]
    have hσ' := hσ hz'
    rw [← hsm] at hσ' ⊢
    have hνZ : Cm.nu = CMain.nu20 := by rw [hmν, (hzp hz').2]
    have hwm' : ClaimsWF CMain.nu20 (onCom cs .main) = true := by rw [← hνZ]; exact hwm
    obtain ⟨o2, p2, m2⟩ := stackZ_run Cm _ mb zc oc g _ hσ' hνZ hwm' (hzw hz') hS hlm hz ho hzE hoE hg hgK hposm
      hpwm hp2 h2 _ (by rw [p1, hU])
    rw [hmg, hmo] at o2 p2 m2
    exact ⟨o2.trans o1, p2, m2⟩
  · rw [if_neg hz'] at h2
    have hsm : Lvm.Shape.smallP p pub = false := by
      have : zon = false := by simpa using hz'
      rw [this] at hzon
      simp only [Lvm.Shape.smallP]
      rw [← hzon, Bool.false_and]
    rw [hsm]
    simp only [Lvm.Shape.onStackZsF, Bool.false_eq_true, if_false, List.map_map]
    obtain ⟨o2, p2, m2⟩ := stack_run Cm _ zc oc g hS (by simp [StackOk, hlm, hwm]) hz ho hzE hoE hg hgK
      hposm hpwm hp2 h2 _ (by rw [p1, hU])
    rw [hmg, hmo] at o2 p2 m2
    exact ⟨o2.trans o1, p2, m2⟩

/-! ## `F`'s positions as bit fields of the answers -/

theorem paF_getD (sig : ByteArray) (h : Nat) : ∀ (n P rem j : Nat), j < min (positionsPerAnswer * n) rem →
    (paF sig h P n rem).getD j 0 = (eToNat (feAt sig (P + 72 * (j / 8) + 40)) >>> ((j % 8) * h)) % 2 ^ h
  | 0, _, _, j, hj => by simp [positionsPerAnswer] at hj
  | n + 1, P, rem, j, hj => by
    rw [paF]
    simp only [positionsPerAnswer] at hj ⊢
    by_cases hj8 : j < min 8 rem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj8),
        List.getElem?_map, List.getElem?_range hj8]
      simp only [Option.map_some, Option.getD_some]
      have e1 : j / 8 = 0 := by omega
      have e2 : j % 8 = j := by omega
      rw [e1, e2, Nat.mul_zero, Nat.add_zero]
    · have h8 : min 8 rem = 8 := by omega
      have e := paF_getD sig h n (P + 72) (rem - 8) (j - 8) (by simp only [positionsPerAnswer]; omega)
      have hl : ((List.range (min 8 rem)).map
          (fun j => (eToNat (feAt sig (P + 40)) >>> (j * h)) % 2 ^ h)).length = 8 := by simp [h8]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; omega), hl,
        ← List.getD_eq_getElem?_getD, h8, e]
      have e1 : (j - 8) / 8 = j / 8 - 1 := by omega
      have e2 : (j - 8) % 8 = j % 8 := by omega
      have e3 : P + 72 + 72 * (j / 8 - 1) = P + 72 * (j / 8) := by
        have : 1 ≤ j / 8 := by omega
        rw [Nat.mul_sub, Nat.mul_one]; omega
      rw [e1, e2, e3]

/-- **`F`'s `j`-th position** of level `L` at position `P`: bits `(j mod 8)·height …` of the
`⌊j/8⌋`-th positions answer (lanes `0–2` as one number, `eToNat`). -/
theorem qsAt_getD (sig : ByteArray) (P : Nat) (L : Level) (j : Nat) (hj : j < L.t) :
    (qsAt sig P L).getD j 0 =
      (eToNat (feAt sig (P + 72 * (j / 8) + 40)) >>> ((j % 8) * L.height)) % 2 ^ L.height := by
  have e := (positionsAux_run L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t sig
    ⟨P, 0, true⟩).1
  show (positionsAux L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t sig
    ⟨P, 0, true⟩).1.getD j 0 = _
  rw [e, pos_mk0]
  exact paF_getD sig L.height _ P L.t j (by simp only [positionsPerAnswer]; omega)

end Lvm.Har
