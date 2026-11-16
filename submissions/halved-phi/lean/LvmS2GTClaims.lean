-- New for lvm2 S2GT (GT-L3): piece (a) of `refinesG20` (STMT 7): V_S's claim list at S2GT (after the pin) against
-- the specification's `ordMk 4` of `assembleF₂`'s relocated pair (`claimsF_rel`'s S2GT port, re-freeze A4).
import LvmE2VDecClaims
import LvmE2TVClaim
import LvmE2TVEq
import LvmE2VDecG

/-!
# V_S's claim list at S2GT

* `tail_affWD`: a committed, `KS` or `σ′` split region claim has no tail (`tail_affW` at `E2`, through `kc_affWD`).
* `vrel_regND`: both split claims of such a region claim, with their tails, against `regClaimT`'s (`regClaimD_rel`).
* `regClaimT_relocS`: `σ′`'s split claims on `S` are its `C_rec` claims relocated (`regClaim_relocS` at `E2`).
* `frontClaimsD_T`: the front's claims at `P20T` on `pubXT` are S2GF's (the front reads neither the stage nor
  `acc_in`).
* `ordMk4_front`: `ordMk 4` on S2GT's lists (the relayout's and `σ′`'s halves first; `M`'s halves before `X_im`).
* **`claimsT_rel`**: the whole list (typed claims, the mini-bus's, the front's) against `ordMk 4` of `assembleF₂`'s
  relocated pair.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.TypedV Lvm.Typed
open Lvm.E2T (TNatT TRefHypT TRelTT affWD regClaimsND typedClaimsND regClaimT typedClaimsT coordH coordE)
open LeanVM.Protocol.KeccakGkr (eqAt)

/-! ## The split region claims -/

/-- **A committed, `KS` or `σ′` split region claim has no tail** (`okB`: their targets lie in `[2^22, 2^ν)`). -/
theorem tail_affWD (N : TNatT) (nuRec : ℕ) (hok : N.toN.okB CMain.nu20 nuRec = true) (s : YSrc)
    (hs : s = .com ∨ s = .ks ∨ s = .sigma) (ry : List FE2) (h : Bool) (v : FE) :
    Shape.tailValueF (⟨⟨CMain.nu20, 0⟩, affWD N s ry h, v⟩ : BlockClaim).onStack.1 = 0 := by
  obtain ⟨hreg, -, -⟩ := fm_ok N.toN CMain.nu20 nuRec hok
  unfold Shape.tailValueF
  refine Finset.sum_eq_zero fun a ha ↦ ?_
  have ha' : a < 2 ^ 22 := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  have hx : (Shape.boolPointF CMain.nu20 a).take CMain.nu20 = Shape.boolPointF CMain.nu20 a :=
    List.take_of_length_le (by simp [Shape.boolPointF])
  have h0 : affWD N s ry h (Shape.boolPointF CMain.nu20 a) = 0 := by
    refine FE.toExt3_injective ?_
    rw [E2T.kc_affWD, FE.toExt3_zero, List.sum_eq_zero, E2T.coordH_zero]
    intro t ht
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ht
    obtain ⟨hgr, hgs⟩ := List.mem_filter.1 hg
    have hsrc : g.src = .com ∨ g.src = .ks ∨ g.src = .sigma := by
      rcases hs with rfl | rfl | rfl <;> simp_all
    obtain ⟨-, -, hc, -, -⟩ := hreg g hgr
    obtain ⟨-, hd2, hd3⟩ := hc hsrc
    have hd4 : g.dst + 2 ^ g.log ≤ 2 ^ 23 := le_trans hd3 (min_le_left _ _)
    have hl : g.log ≤ 22 := by
      have : 2 ^ g.log ≤ 2 ^ 22 := by (clear * - hd2 hd4; omega)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have hpos : 0 < 2 ^ g.log := by positivity
    have hd5 : g.dst / 2 ^ 22 = 1 := Nat.div_eq_of_lt_le (by omega) (by (clear * - hd4 hpos; omega))
    have hz : eqAt (((Shape.boolPointF CMain.nu20 a).map FE.toExt3).drop g.log) (g.dst >>> g.log) = 0 := by
      rw [← List.map_drop, ← fm_toExt3_eqAtF, fm_eqAtF_zero _ _ (22 - g.log), FE.toExt3_zero]
      · simp only [Shape.boolPointF, List.length_drop, List.length_map, List.length_range, CMain.nu20]
        (clear * - hl; omega)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' hl]
        simp [Shape.boolPointF, Nat.testBit_lt_two_pow ha']
      · rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' hl, Nat.testBit_eq_decide_div_mod_eq, hd5]
        rfl
    rw [hz, map_zero, mul_zero]
  simp only [BlockClaim.onStack]
  rw [hx, h0, mul_zero, zero_mul]

/-- **Both split claims of a committed, `KS` or `σ′` region claim, with their tails**, against `regClaimT`'s. -/
theorem vrel_regND {s : Bool} (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (nuRec : ℕ)
    (hok : N.toN.okB 23 nuRec = true) (hlay : N.toN.layOk lay = true) (src : YSrc)
    (hsrc : src = .com ∨ src = .ks ∨ src = .sigma) (ry : List FE2) (hry : ry.length = yVars) (v : FE2) :
    List.Forall₂ (VRel s) (regClaimsND N P20 src ry v)
      (regClaimT (N.inst Q lay) src N.toN.off (ry.map toE2) (toE2 v)) := by
  have hν := regsOf_dst hok src hsrc
  unfold regClaimsND regClaimT
  rw [nuMain_P20]
  simp only [List.map_cons, List.map_nil]
  exact .cons (vrel_of (E2T.regClaimD_rel N Q lay 23 nuRec hok hlay src 23 hν ry hry v false)
      fun _ ↦ ⟨inStack_full, (tail_affWD N nuRec hok src hsrc ry false _).symm⟩)
    (.cons (vrel_of (E2T.regClaimD_rel N Q lay 23 nuRec hok hlay src 23 hν ry hry v true)
      fun _ ↦ ⟨inStack_full, (tail_affWD N nuRec hok src hsrc ry true _).symm⟩) .nil)

/-- **`σ′`'s split claims on `S` are its `C_rec` claims relocated** (`regClaim_relocS` at `E2`). -/
theorem regClaimT_relocS (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (nuMain nuRec : ℕ)
    (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true) (hσ : SigInS N.toN) (r : List E2)
    (v : E2) :
    regClaimT (N.inst Q lay) .sigma N.toN.off r v =
      (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW r v).map relocS := by
  obtain ⟨-, -, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  unfold regClaimT
  rw [List.map_map]
  refine List.map_congr_left fun h _ ↦ Prod.ext (funext fun X ↦ ?_) rfl
  show E2T.regSumW (N.inst Q lay) (fun s' ↦ s' == .sigma)
      (fun y ↦ coordE h (E2V.eqAtF r y) * eqAt X (N.toN.off y)) =
    (⟨19, CMain.sOff20⟩ : VPlacement).eqAbove X * E2T.regSumW (N.inst Q lay) (fun s' ↦ s' == .sigma)
      (fun y ↦ coordE h (E2V.eqAtF r y) * eqAt (X.take 19) (N.toN.off y % 2 ^ 19))
  rw [E2T.kf_regSumWT N Q lay hlay, E2T.kf_regSumWT N Q lay hlay, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hgs : (g.src == .sigma) = true
  · simp only [hgs, ite_true]
    obtain ⟨h1, h2⟩ := hσ g hg (by simpa using hgs)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [eqAt_take19_mod, fm_off N.toN hpw g hg i hi', eqAt_reloc X (g.dst + i) ?_]
    · ring
    · simp only [Nat.shiftRight_eq_div_pow]
      rw [show CMain.sOff20 = 5767168 from rfl] at h1 h2 ⊢
      have : 0 < 2 ^ g.log := by positivity
      norm_num
      omega
  · simp [hgs]

/-- The relayout's point claim's block (`C_rec`'s whole cube) moves onto `S` (`relocS_sum`'s conditions). -/
theorem relocOK_relay (z : List E2) : RelocOK (1, ⟨relayRounds, 0⟩, z) := by
  unfold RelocOK
  dsimp only
  decide

/-! ## The front and the order -/

/-- **The front's claims at `P20T` on S2GT's public values are S2GF's** (they read `P20`'s fields and `pub.h`,
`pub.n`). -/
theorem frontClaimsD_T (x : List UInt8) (tp : TapeV)
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) :
    frontClaimsD P20T (pubXT x) tp co lo = frontClaimsD P20F (pubXF x) tp co lo := rfl

/-- `ordMk` commutes with a common map. -/
theorem ordMk_map {α β : Type} (k : ℕ) (f : α → β) (r m : List α) :
    Lvm.ASM.ordMk k (r.map f) (m.map f) = (Lvm.ASM.ordMk k r m).map f := by
  simp only [Lvm.ASM.ordMk, List.map_append, List.map_take, List.map_drop, List.map_dropLast, List.getLast?_map]
  cases m.getLast? <;> rfl

/-- `ordMk 4` at S2GT: the relayout's and `σ′`'s halves, `C_main`'s up to `X_re`, `M`'s halves, `X_im`. -/
theorem ordMk4_front {α : Type} (a b c d r1 r2 e f g h y1 y2 i1 i2 x1 x2 : α) (A B : List α) :
    Lvm.ASM.ordMk 4 [a, b, c, d, r1, r2] (e :: f :: g :: h :: (A ++ (B ++ [y1, y2, i1, i2, x1, x2]))) =
      a :: b :: c :: d :: e :: f :: g :: h :: (A ++ (B ++ [y1, y2, i1, i2, x1, r1, r2, x2])) := by
  have hm : e :: f :: g :: h :: (A ++ (B ++ [y1, y2, i1, i2, x1, x2])) =
      (e :: f :: g :: h :: (A ++ (B ++ [y1, y2, i1, i2, x1]))) ++ [x2] := by simp
  rw [hm, Lvm.ASM.ordMk, List.dropLast_concat, List.getLast?_concat]
  simp

/-- `(m3G N p).tableClaims` is the record's (`M3.realW`'s table claims do not read the lanes). -/
theorem m3G_tableClaims (N : TNatT) (p : Params) (pub : Pub) (evs : List (List FE × List FE)) :
    (E2T.m3G N p).tableClaims pub evs = M3.tableClaimsR (M3.sumcheckTabs N.mbT) evs := rfl

/-! ## The whole list -/

/-- **V_S's claim list at S2GT (after the pin) against `ordMk 4` of `assembleF₂`'s relocated pair** (both shapes):
where V_S's `require` held (every claim on `C_main`), the typed claims (`TRelTT`: the relayout's and `σ′`'s halves
relocated onto `S`, the committed block's and `KS`'s halves), the mini-bus's and the front's (`front_rel`), on the
statement's shape's stack, are the spec's in V_S's order. -/
theorem claimsT_rel (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay) (hσ : SigInS N.toN)
    (x : List UInt8) (t : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE))
    (a : Lvm.ASM.OpenClaims) (hT : TRelTT N Q lay t a) (tp : TapeV)
    (co : List FE2 × List FE2 × (List (List FE2 × FE2) × List FE2 × List FE2) × ((FE × (List FE → FE)) × List FE))
    (lo : List FE2 × (List FE2 × FE2) × List FE2) (k : E2V.KgOutF) (hk : FrontRel tp co lo k)
    (hsh : TapeShape 20 1 0 tp)
    (hall : (t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsD P20T (pubXT x) tp co lo).all
      (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
        (((t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++ frontClaimsD P20T (pubXT x) tp co lo).filter
          (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordMk 4 ((E2V.assembleF₂ x a k).1.map (Lvm.CT.reloc20 x)) (E2V.assembleF₂ x a k).2) := by
  obtain ⟨ry, rv, rr, vR, ht1, hry, -, -, rfl, -, hcl⟩ := hT
  obtain ⟨-, -, -, hfc, hfh⟩ := H.toT.fits
  have hall' : ∀ e ∈ t.2.1 ++ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2) ++
      frontClaimsD P20T (pubXT x) tp co lo, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he]]
  have hok := H.ok
  rw [nuMain_P20] at hok
  -- the typed claims
  have hrelay := vrel_splitM (s := Shape.small x) [(1, ⟨P20.nuRec, (layout0 P20).s⟩, rr)]
    (by simpa using offOK_relay) vR [(1, ⟨relayRounds, 0⟩, rr.map toE2)]
    (by simp [E2V.partE, shiftS2, nuRec_P20, layout0_s, Lvm.FE2.toE2_one]; rfl)
    (by simp only [List.mem_singleton, forall_eq]; exact relocOK_relay _) (toE2 vR) rfl
  have hsg := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .sigma (.inr (.inr rfl)) ry hry
    (rv.getD 2 0)
  rw [regClaimT_relocS N Q lay 23 P20.nuRec hok H.hlay hσ] at hsg
  have hcom := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .com (.inl rfl) ry hry (rv.getD 0 0)
  have hks := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .ks (.inr (.inl rfl)) ry hry
    (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      ((E2V.splitE2 19 ⟨[(1, ⟨relayRounds, 0⟩, rr.map toE2)], toE2 vR⟩).map (fun c ↦ relocS c.onStack) ++
        (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map toE2) (toE2 (rv.getD 2 0))).map relocS ++
        regClaimT (N.inst Q lay) .com N.toN.off (ry.map toE2) (toE2 (rv.getD 0 0)) ++
        regClaimT (N.inst Q lay) .ks N.toN.off (ry.map toE2) (toE2 (rv.getD 3 0))) := by
    rw [ht1]
    unfold typedClaimsND
    rw [nuMain_P20]
    exact Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append hrelay hsg) hcom) hks
  -- the mini-bus's claims
  have hZrel : List.Forall₂ CRelM ((Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2)).map fun e ↦ (e.1, e.2.1))
      (tableClaimsE N.mbT (M3.claimsOfEvs N.mbT t.2.2)) := by
    rw [Shape.zeroTails, List.map_map]
    simpa [Function.comp_def] using hcl.imp fun _ _ h ↦ CRel.crelM h
  have hZm : ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main := fun e he ↦
    hall' e (List.mem_append_left _ (List.mem_append_right _ he))
  have hZt : Shape.small x = true → ∀ e ∈ Shape.zeroTails (M3.tableClaimsR N.mbT t.2.2), e.1 = .main →
      Shape.InStack e.2.1.block ∧ e.2.2 = Shape.tailValueF e.2.1.onStack.1 := by
    intro _ e he hm
    rw [Shape.zeroTails] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have h := Shape.table_tails N.mbT N.mbT (fun _ h ↦ h) t.2.2 hfc hfh e' he' hm
    exact ⟨h.inStack, h.tail.symm⟩
  have hZV := forall₂_crelM (s := Shape.small x) hZrel hZm hZt
  -- the front
  have hFV := front_rel (s := Shape.small x) x tp co lo k hk hsh (fun hs ↦ of_decide_eq_true hs)
    (by simp [pubX, pubOf])
  rw [← frontClaimsD_T] at hFV
  have hV := forall₂_onStackZsF (Lk.forall₂_append (Lk.forall₂_append hTV hZV) hFV)
  -- the spec's list in V_S's order
  have hmbE := main_of_crel hcl fun e he ↦ by
    have := hZm (e.1, e.2, 0) (List.mem_map.2 ⟨e, he, rfl⟩)
    exact this
  convert hV using 1
  have hmb : (N.inst Q lay).mbT = N.mbT := rfl
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (Lvm.CT.reloc20 x) = (l.map relocS).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold E2V.assembleF₂ typedClaimsT miniClaims
  rw [hmb, filter_main_self hmbE, filter_crec_nil hmbE, assembleSF_eq]
  dsimp only
  rw [onStackZs_eq_map, hρ, ordMk_map]
  congr 1
  rw [inplM_main hmbE]
  simp only [frontW, linkW, E2V.splitE2, E2V.pointE2, regClaimT, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.append_assoc, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero]
  rw [ordMk4_front]
  simp only [E2T.kv_toE2_getD]
  rfl

end Lvm.VEq
