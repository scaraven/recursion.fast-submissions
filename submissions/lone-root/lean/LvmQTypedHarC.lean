-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's claims and openings: the circuit's typed claims
-- (`typedClaimsC`: `regClaimG`'s sum claims, the relayout's point claim, the mini-bus's table claims) are V_S's
-- (`typedClaimsN` and `tableClaimsR`), and the openings at ν = 23 in both shapes (`dOpenT`) read only the claims and
-- `C_main`'s tails. lvm2 roll 11 (M′ `S2GM`, R11-N): every claim is on `C_main`, which `dOpenT` opens alone.
import LvmQTypedHarB
import LvmQAsmHarTails

/-!
# The typed claims and the openings

* **`regClaimG_val`**: `regClaimG`'s sum claim, on regions that are V_S's, is V_S's region claim
  `⟨⟨ν, 0⟩, affW N s r_y, v⟩` (the selector `eq(r_y^{≥ log}, base ≫ log)` is `hiW`, a block's `eqAbove` is
  `eqAtF` of its target, `eqConstG`'s value is `eqAtF`).
* **`typedClaimsC_val`**: the circuit's typed claims are V_S's: first the relayout point claim on `S`, `σ′`'s region
  claim (and the mini-bus's `C_rec` table claims, none at S2GM); then the committed regions' and `KS`'s claims and the
  mini-bus's `C_main` table claims (M′: all on `C_main`).
* **`dOpenT_congr`**: `dOpenT` reads only the claims (commitment and claim) and `C_main`'s tails in the small shape.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped DM
open Lvm.TypedV (TNat NReg)

section
variable {c : Ctx} {M : Mem}

/-- `eqAtF` is `eqW` (characteristic 2). -/
theorem eqAtF_eqW : ∀ (r : List FE) (w : Nat), eqAtF r w = Loop.eqW r w
  | [], _ => rfl
  | a :: r, w => by
    rw [eqAtF, Loop.eqW, eqAtF_eqW r (w / 2), sub_eq_add_neg, CharTwo.neg_eq]

/-- **`eqConstG`'s value** is `eqAtF` of its cells at the constant. -/
theorem eqConstG_valC {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (r : List Cell) (b : Nat) (p : Ptr), SegsHold c M p (eqConstG z o r b p).2 →
      (eqConstG z o r b p).1.val M = eqAtF (vs M r) b
  | [], _, _, _ => by simp [eqConstG, pure, vs, eqAtF, ho]
  | x :: r, b, p, h => by
    simp only [eqConstG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    have ih := eqConstG_valC hz ho r (b / 2) p h.1
    simp only [vs, List.map_cons, eqAtF] at ih ⊢
    by_cases hb : b % 2 = 1
    · simp only [hb, if_true] at h ⊢
      rw [mulAdd_spec h.2, ih, hz, add_zero, mul_comm]
    · simp only [hb, if_false, neg1, addK, bind_apply] at h ⊢
      rw [segsHold_append] at h
      rw [mulAdd_spec h.2.2, lin_spec h.2.1, ih, hz, add_zero, ofK_zero, zero_mul, add_zero, ofK_one,
        mul_comm, add_comm]

/-- A block's `eqAbove` is `eqAtF` of the point above it at its target's high bits. -/
theorem eqAbove_eqAtF (log off : Nat) (X : List FE) :
    (⟨log, off⟩ : Placement).eqAbove X = eqAtF (X.drop log) (off >>> log) := by
  rw [Placement.eqAbove, eqAtF_eqW, ← eqEval_selector, List.length_drop]

/-- `regClaimG`'s parts (selector cell, block, point cells) by value. -/
theorem regParts_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (ry : List Cell) :
    ∀ (rs : List TReg) (p : Ptr),
      SegsHold c M p (seqAll (rs.map fun R => do
        let s ← regSelG z o ry R
        pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) p).2 →
      (seqAll (rs.map fun R => do
        let s ← regSelG z o ry R
        pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) p).1.map
          (fun x => (x.1.val M, x.2.1, vs M x.2.2)) =
        rs.map fun R => (TypedV.hiW (vs M ry) R.log R.base, (⟨R.log, R.off⟩ : Placement), (vs M ry).take R.log)
  | [], _, _ => rfl
  | R :: rs, p, h => by
    simp only [List.map_cons, seqAll, bind_apply, pure_apply, List.append_nil] at h ⊢
    rw [segsHold_append] at h
    rw [regParts_val hz ho ry rs _ h.2]
    rw [List.cons.injEq]
    refine ⟨?_, rfl⟩
    rw [regSelG, eqConstG_valC hz ho _ _ _ h.1, TypedV.hiW]
    simp [vs, List.map_drop, List.map_take]

/-- The region claim's weight, term by term. -/
theorem affW_eq (N : TNat) (s : Lvm.Typed.YSrc) (ry : List FE) (X : List FE) :
    TypedV.affW N s ry X = sumE ((N.regsOf s).map fun g =>
      TypedV.hiW ry g.log g.base * (⟨g.log, g.dst⟩ : Placement).eqAbove X * eqEval (ry.take g.log) (X.take g.log)) := by
  simp only [TypedV.affW, sumE, List.foldl_map]
  congr 1
  funext acc g
  rw [eqAbove_eqAtF]
  ring

/-- **`regClaimG`'s claim is V_S's region claim**, on regions that are V_S's. -/
theorem regClaimG_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (com : Com) (nu : Nat) (N : TNat)
    (s : Lvm.Typed.YSrc) (rs : List TReg) (hrs : (N.regsOf s).map nTrip = rs.map tTrip) (ry : List Cell) (v : Cell)
    (p : Ptr) (h : SegsHold c M p (regClaimG z o com nu rs ry v p).2) :
    (regClaimG z o com nu rs ry v p).1.val M = (com, ⟨⟨nu, 0⟩, TypedV.affW N s (vs M ry), v.val M⟩) := by
  simp only [regClaimG, bind_apply, pure_apply, List.append_nil] at h ⊢
  have hp := regParts_val hz ho ry rs p h
  simp only [CClaim.val, sumClaim]
  refine congrArg (Prod.mk com) ?_
  congr 1
  funext X
  rw [affW_eq, List.map_map]
  generalize (seqAll (rs.map fun R => do
    let s ← regSelG z o ry R
    pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) p).1 = parts at hp
  have e1 : parts.map ((fun cbz : FE × Placement × List FE => cbz.1 * cbz.2.1.eqAbove X *
      eqEval cbz.2.2 (X.take cbz.2.1.variableCount)) ∘ fun x => (x.1.val M, x.2.1, vs M x.2.2)) =
      (parts.map fun x => (x.1.val M, x.2.1, vs M x.2.2)).map (fun cbz => cbz.1 * cbz.2.1.eqAbove X *
        eqEval cbz.2.2 (X.take cbz.2.1.variableCount)) := by rw [List.map_map]
  rw [e1, hp, List.map_map]
  congr 1
  clear hp e1 parts h
  generalize N.regsOf s = gs at hrs ⊢
  induction gs generalizing rs with
  | nil => cases rs with
    | nil => rfl
    | cons _ _ => simp at hrs
  | cons g gs ih =>
    cases rs with
    | nil => simp at hrs
    | cons R rs =>
      simp only [List.map_cons, List.cons.injEq, nTrip, tTrip, Prod.mk.injEq] at hrs ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hrs
      refine ⟨?_, ih rs h4⟩
      simp only [Function.comp_apply, h1, h2, h3]
/-- The claims of one commitment, by value (`CClaim.val` keeps the commitment). -/
theorem filter_val (l : List CClaim) (com : Com) :
    (l.filter (·.com == com)).map (CClaim.val M) = (l.map (CClaim.val M)).filter (·.1 == com) := by
  rw [List.filter_map]; rfl

/-- **The circuit's typed claims are V_S's** (M′ `S2GM`: all on `C_main`): first the relayout's point claim on the
stream block (`⟨19, sOff⟩`), `σ′`'s region claim and the mini-bus's `C_rec` table claims (none at `S2GM`, by the
guard's `claimsOkB`); then the committed regions', `KS`'s and the mini-bus's `C_main` table claims. -/
theorem typedClaimsC_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {Td : TData} {N : TNat}
    (htd : TdOk Td N) (nu sOff : Nat) (t : TypedC) (st : List Lvm.M3.Tab) (hst : Td.mbS = st.map Lvm.M3.Tab.shape)
    (p : Ptr) (h : SegsHold c M p (typedClaimsC z o Td nu sOff t p).2) :
    (typedClaimsC z o Td nu sOff t p).1.1.map (CClaim.val M) =
      (.main, BlockClaim.point ⟨19, sOff⟩ (vs M t.rr) (t.vR.val M)) ::
        (.main, ⟨⟨nu, 0⟩, TypedV.affW N .sigma (vs M t.ry), (t.rv.getD 2 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))).filter (·.1 == .crec) ∧
    (typedClaimsC z o Td nu sOff t p).1.2.map (CClaim.val M) =
      (.main, ⟨⟨nu, 0⟩, TypedV.affW N .com (vs M t.ry), (t.rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨nu, 0⟩, TypedV.affW N .ks (vs M t.ry), (t.rv.getD 3 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))).filter (·.1 == .main) ∧
    (∀ cc ∈ (typedClaimsC z o Td nu sOff t p).1.2, cc.com = .main) := by
  simp only [typedClaimsC, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  have e1 := regClaimG_val hz ho .main nu N .sigma Td.sig htd.sig t.ry (t.rv.getD 2 z) p h.1
  have e2 := regClaimG_val hz ho .main nu N .com Td.com htd.com t.ry (t.rv.getD 0 z) _ h.2.1
  have e3 := regClaimG_val hz ho .main nu N .ks Td.ks htd.ks t.ry (t.rv.getD 3 z) _ h.2.2
  have hv := tabClaims_val hz st t.tab
  rw [← hst] at hv
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_cons, List.map_cons, e1, filter_val, hv]; rfl
  · rw [List.map_cons, List.map_cons, e2, e3, filter_val, hv]
  · intro cc hcc
    simp only [List.mem_cons, List.mem_filter, beq_iff_eq] at hcc
    rcases hcc with rfl | rfl | ⟨-, h⟩
    · simp [regClaimG, bind_apply, pure_apply]
    · simp [regClaimG, bind_apply, pure_apply]
    · exact h

end

/-! ## The openings read each commitment's claims -/

theorem map_pair_eq {α β γ : Type} : ∀ (l₁ l₂ : List (α × β × γ)), l₁.map (·.2.1) = l₂.map (·.2.1) →
    l₁.map (·.2.2) = l₂.map (·.2.2) → l₁.map (·.2) = l₂.map (·.2)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l₁, b :: l₂, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
    exact ⟨Prod.ext h1.1 h2.1, map_pair_eq l₁ l₂ h1.2 h2.2⟩

/-- **`dOpenT` reads only the claims' commitments and claims, and `C_main`'s tails in the small shape** (M′ `S2GM`:
it requires every claim on `C_main` and opens `C_main` alone). -/
theorem dOpenT_congr (p : Params) (s : Bool) (l₁ l₂ : List (Com × BlockClaim × FE))
    (hp : l₁.map (fun e => (e.1, e.2.1)) = l₂.map (fun e => (e.1, e.2.1)))
    (ht : s = true → (l₁.filter (·.1 == .main)).map (·.2.2) = (l₂.filter (·.1 == .main)).map (·.2.2)) :
    TypedV.dOpenT p s l₁ = TypedV.dOpenT p s l₂ := by
  have ha : l₁.all (·.1 == .main) = l₂.all (·.1 == .main) := by
    have e := congrArg (fun l : List (Com × BlockClaim) => l.all (·.1 == Com.main)) hp
    simpa only [List.all_map, Function.comp_def] using e
  have ef : ∀ l : List (Com × BlockClaim × FE), (l.filter (·.1 == .main)).map (·.2.1) =
      ((l.map fun e => (e.1, e.2.1)).filter (·.1 == .main)).map (·.2) := fun l => by
    rw [List.filter_map, List.map_map]; rfl
  have hm : (l₁.filter (·.1 == .main)).map (·.2.1) = (l₂.filter (·.1 == .main)).map (·.2.1) := by
    rw [ef, ef, hp]
  unfold TypedV.dOpenT
  rw [ha]
  cases s with
  | false =>
    simp only [Bool.false_eq_true, if_false, List.map_map]
    have em : ∀ l : List (Com × BlockClaim × FE), (l.filter (·.1 == .main)).map ((·.1.onStack) ∘ (·.2)) =
        ((l.filter (·.1 == .main)).map (·.2.1)).map (·.onStack) := fun l => by rw [List.map_map]; rfl
    rw [em l₁, em l₂, hm]
  | true =>
    simp only [if_true]
    rw [map_pair_eq _ _ hm (ht rfl)]

/-- The shape bit at `P20` is roll 7's `smallP`. -/
theorem smallT_P20 (pub : Pub) : TypedV.smallT P20 pub = Shape.smallP P20 pub := rfl

-- (M′ `S2GM`, R11-N: B1's `dOpenT_P20` (`dOpenT P20 = Shape.dOpenZ P20`) is removed: `dOpenZ` still opens `C_rec`.)

/-! ## V_S's claim list against the circuit's -/

section
variable {M : Mem}

/-- `noDRB` is roll 7's `noDR`. -/
theorem noDRB_eq (cc : CClaim) : noDRB cc = noDR cc := rfl

theorem filter_all {α : Type} {l : List α} {f : α → Bool} (h : ∀ x ∈ l, f x = true) : l.filter f = l :=
  List.filter_eq_self.mpr h

/-- **V_S's openings on its claim list are its openings on the circuit's claims** (with their tails; M′ `S2GM`: all
on `C_main`): the typed claims (`[A, B, C, D]`, tail `0`) and the mini-bus's table claims `tabs` (tail `0`) on V_S's
side; the circuit's first claims `tc₁` (`A`, `B` and the `C_rec` table claims, of which there are none since `tc₁`
is on `C_main`) and `tc₂` (`C`, `D`, the `C_main` table claims); the rest equal on both sides (in the small shape
with their tails). -/
theorem openClaims_eq (p : Params) (s : Bool) (A B Cc D : BlockClaim) (tabs : List (Com × BlockClaim))
    (tc₁ tc₂ rest : List CClaim) (restV : List (Com × BlockClaim × FE))
    (h1 : tc₁.map (CClaim.val M) = (.main, A) :: (.main, B) :: tabs.filter (·.1 == .crec))
    (h2 : tc₂.map (CClaim.val M) = (.main, Cc) :: (.main, D) :: tabs.filter (·.1 == .main))
    (hc1 : ∀ cc ∈ tc₁, cc.com = .main) (hnd1 : tc₁.all noDRB = true) (hnd2 : tc₂.all noDRB = true)
    (hr : rest.map (CClaim.val M) = restV.map fun e => (e.1, e.2.1))
    (ht : s = true → claimsT M rest = restV) :
    TypedV.dOpenT p s ([(.main, A, 0), (.main, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
        (Shape.zeroTails ([] ++ tabs) ++ restV)) =
      TypedV.dOpenT p s (claimsT M (tc₁ ++ tc₂ ++ rest)) := by
  -- no table claim is on `C_rec`: `tc₁`'s are on `C_main`
  have hT1 : tabs.filter (·.1 == .crec) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro e he
    have he' : e ∈ tc₁.map (CClaim.val M) := by
      rw [h1]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)
    obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he'
    have h := (List.mem_filter.mp he).2
    have h' : (CClaim.val M cc).1 = .main := hc1 cc hcc
    rw [h'] at h
    exact absurd h (by decide)
  have hT2 : tabs.filter (·.1 == .main) = tabs := by
    refine filter_all fun e he => ?_
    have hn := List.filter_eq_nil_iff.mp hT1 e he
    revert hn
    rcases e with ⟨c', b'⟩
    cases c' <;> simp
  rw [hT1] at h1
  rw [hT2] at h2
  have hl1 := congrArg List.length h1
  have hl2 := congrArg List.length h2
  simp only [List.length_map, List.length_cons, List.length_nil] at hl1 hl2
  have hP : (claimsT M (tc₁ ++ tc₂ ++ rest)).map (fun e => (e.1, e.2.1)) =
      [(.main, A), (.main, B), (.main, Cc), (.main, D)] ++ (tabs ++ restV.map fun e => (e.1, e.2.1)) := by
    rw [claimsT_proj, List.map_append, List.map_append, h1, h2, hr]
    simp
  have hV : ([(.main, A, 0), (.main, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
      (Shape.zeroTails ([] ++ tabs) ++ restV) : List (Com × BlockClaim × FE)).map (fun e => (e.1, e.2.1)) =
      [(.main, A), (.main, B), (.main, Cc), (.main, D)] ++ (tabs ++ restV.map fun e => (e.1, e.2.1)) := by
    rw [List.map_append, List.map_append, Shape.map_zeroTails, List.nil_append]; rfl
  refine dOpenT_congr p s _ _ (hV.trans hP.symm) fun hs => ?_
  have hR := ht hs
  have ec : ∀ l : List CClaim, (∀ cc ∈ l, cc.com = .main) → (claimsT M l).filter (·.1 == .main) = claimsT M l :=
    fun l hl => filter_all fun e he => by
      obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he
      simp [hl cc hcc]
  have hall : ∀ e ∈ tabs, e.1 = .main := fun e he => by
    have := List.filter_eq_self.mp hT2 e he
    simpa using this
  have hc2 : ∀ cc ∈ tc₂, cc.com = .main := fun cc hcc => by
    have he : CClaim.val M cc ∈ tc₂.map (CClaim.val M) := List.mem_map_of_mem hcc
    rw [h2] at he
    show (CClaim.val M cc).1 = .main
    simp only [List.mem_cons] at he
    rcases he with he | he | he
    · rw [he]
    · rw [he]
    · exact hall _ he
  have hl1' : tc₁.length = 2 := by simpa using hl1
  have hl2' : tc₂.length = 2 + tabs.length := by omega
  have et1 : (claimsT M tc₁).map (·.2.2) = List.replicate 2 0 := by
    rw [claimsT, List.map_map, show (2 : Nat) = tc₁.length from hl1'.symm]
    exact map_tailC_zero tc₁ (by simpa [noDRB_eq] using hnd1)
  have et2 : (claimsT M tc₂).map (·.2.2) = List.replicate (2 + tabs.length) 0 := by
    rw [claimsT, List.map_map, ← hl2']
    exact map_tailC_zero tc₂ (by simpa [noDRB_eq] using hnd2)
  have ez : ((Shape.zeroTails ([] ++ tabs)).filter (·.1 == .main)).map (·.2.2) =
      List.replicate (tabs.filter (·.1 == .main)).length 0 := by
    rw [List.nil_append, Shape.zeroTails, List.filter_map, List.map_map, List.eq_replicate_iff]
    refine ⟨by simp [Function.comp_def], fun b hb => ?_⟩
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hb
    rfl
  rw [hT2] at ez
  have eR : ((claimsT M (tc₁ ++ tc₂ ++ rest)).filter (·.1 == .main)).map (·.2.2) =
      List.replicate (4 + tabs.length) 0 ++ (restV.filter (·.1 == .main)).map (·.2.2) := by
    rw [show claimsT M (tc₁ ++ tc₂ ++ rest) = claimsT M tc₁ ++ claimsT M tc₂ ++ claimsT M rest by
      simp [claimsT], hR, List.filter_append, List.filter_append, ec tc₁ hc1, ec tc₂ hc2, List.map_append,
      List.map_append, et1, et2, ← List.replicate_add]
    congr 2; omega
  have eL : (([(.main, A, 0), (.main, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
      (Shape.zeroTails ([] ++ tabs) ++ restV) : List (Com × BlockClaim × FE)).filter (·.1 == .main)).map (·.2.2) =
      [0, 0, 0, 0] ++ (List.replicate tabs.length 0 ++ (restV.filter (·.1 == .main)).map (·.2.2)) := by
    rw [List.filter_append, List.map_append, List.filter_append, List.map_append, ez]
    rfl
  rw [eL, eR, List.replicate_add, List.append_assoc]
  rfl

theorem zipProj (L : List BlockClaim) (T : List FE) (h : T.length = L.length) :
    ((L.zip T).map fun e => (Com.main, e.1, e.2)).map (fun e => (e.1, e.2.1)) = L.map (Com.main, ·) := by
  induction L generalizing T with
  | nil => rfl
  | cons a L ih => cases T with
    | nil => simp at h
    | cons b T => simp only [List.zip_cons_cons, List.map_cons]; rw [ih T (by simpa using h)]

theorem Shape.zeroTails_tails' (l : List (Com × BlockClaim)) :
    (Shape.zeroTails l).map (·.2.2) = List.replicate l.length 0 := zeroTails_tails l

/-- **V_S's openings on its whole claim list are the circuit's** (`openClaims_eq` with V_S's list written out: the typed
claims `typedClaimsN`, then `dClaimsZ` with no bus claims; the circuit's list `qarithB`'s `cs`). -/
theorem openClaimsT_eq (p : Params) (s : Bool) (N : TNat) (m : M3) (pub : Pub) (z : Cell) (hz : z.val M = 0)
    (ry rv rr : List Cell) (vR : Cell) (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut)
    (wcs rk vks : List FE) (ksC : List BlockClaim) (kL : List (Com × BlockClaim))
    (tc₁ tc₂ tapeC kC ksOut clK : List CClaim) (hrec : p.nuRec = 19)
    (h1 : tc₁.map (CClaim.val M) =
      (.main, BlockClaim.point ⟨19, (layout0 p).s⟩ (vs M rr) (vR.val M)) ::
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .sigma (vs M ry), (rv.getD 2 z).val M⟩) ::
          (m.tableClaims pub evals).filter (·.1 == .crec))
    (h2 : tc₂.map (CClaim.val M) =
      (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .com (vs M ry), (rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .ks (vs M ry), (rv.getD 3 z).val M⟩) ::
          (m.tableClaims pub evals).filter (·.1 == .main))
    (hc1 : ∀ cc ∈ tc₁, cc.com = .main) (hnd1 : tc₁.all noDRB = true) (hnd2 : tc₂.all noDRB = true)
    (htape : tapeC.map (CClaim.val M) = (tapeClaims p tp wo pub).map (.main, ·))
    (hks : kC.map (CClaim.val M) = ksC.map (.main, ·)) (hko : ksOut.map (CClaim.val M) = m.ksOutputClaims rk vks)
    (hkl : clK.map (CClaim.val M) = kL)
    (htt : s = true → tapeC.map (Lvm.QShape.tailC M) = Shape.tapeTails p tp wo wcs pub)
    (hnd : (kC ++ ksOut ++ clK).all noDRB = true) :
    TypedV.dOpenT p s (TypedV.typedClaimsN N p (vs M ry) (vs M rv) (vs M rr) (vR.val M) ++
        Shape.dClaimsZ m p pub [] evals tp wo wcs rk vks ksC kL) =
      TypedV.dOpenT p s (claimsT M (tc₁ ++ tc₂ ++ (tapeC ++ kC) ++ ksOut ++ clK)) := by
  have gv : ∀ i, (vs M rv).getD i 0 = (rv.getD i z).val M := fun i => Lvm.QAcc.getD_vals rv z hz i
  have eN : TypedV.typedClaimsN N p (vs M ry) (vs M rv) (vs M rr) (vR.val M) =
      [(.main, BlockClaim.point ⟨19, (layout0 p).s⟩ (vs M rr) (vR.val M), 0),
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .sigma (vs M ry), (rv.getD 2 z).val M⟩, 0),
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .com (vs M ry), (rv.getD 0 z).val M⟩, 0),
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .ks (vs M ry), (rv.getD 3 z).val M⟩, 0)] := by
    simp only [TypedV.typedClaimsN, hrec, gv]
  have eZ : Shape.dClaimsZ m p pub [] evals tp wo wcs rk vks ksC kL = Shape.zeroTails ([] ++ m.tableClaims pub evals) ++
      ((((tapeClaims p tp wo pub).zip (Shape.tapeTails p tp wo wcs pub)).map fun e => (Com.main, e.1, e.2)) ++
        Shape.zeroTails (ksC.map (.main, ·)) ++ Shape.zeroTails (m.ksOutputClaims rk vks ++ kL)) := by
    simp only [Shape.dClaimsZ, List.append_assoc]
  rw [eN, eZ, show tc₁ ++ tc₂ ++ (tapeC ++ kC) ++ ksOut ++ clK = tc₁ ++ tc₂ ++ ((tapeC ++ kC) ++ ksOut ++ clK) by
    simp only [List.append_assoc]]
  have hlt := Shape.length_tapeTails p tp wo wcs pub
  have hP : ((((tapeClaims p tp wo pub).zip (Shape.tapeTails p tp wo wcs pub)).map fun e => (Com.main, e.1, e.2)) ++
      Shape.zeroTails (ksC.map (.main, ·)) ++ Shape.zeroTails (m.ksOutputClaims rk vks ++ kL)).map
        (fun e => (e.1, e.2.1)) = ((tapeC ++ kC) ++ ksOut ++ clK).map (CClaim.val M) := by
    simp only [List.map_append, Shape.map_zeroTails, zipProj _ _ hlt, htape, hks, hko, hkl, List.append_assoc]
  refine openClaims_eq p s _ _ _ _ _ tc₁ tc₂ _ _ h1 h2 hc1 hnd1 hnd2 hP.symm fun hs => ?_
  refine list_eq_of_proj _ _ (by rw [claimsT_proj, hP]) ?_
  have hnd' : (kC ++ ksOut ++ clK).map (Lvm.QShape.tailC M) = List.replicate (kC ++ ksOut ++ clK).length 0 :=
    map_tailC_zero _ (by simpa [noDRB_eq] using hnd)
  have hl1 := congrArg List.length hks
  have hl2 := congrArg List.length hko
  have hl3 := congrArg List.length hkl
  simp only [List.length_map] at hl1 hl2 hl3
  simp only [claimsT, List.map_map, List.map_append, List.append_assoc, Shape.zeroTails_tails',
    ← htt hs]
  simp only [List.map_append, List.length_append, ← List.append_assoc] at hnd'
  have e1 : ∀ l : List CClaim, l.map ((fun x : Com × BlockClaim × FE => x.2.2) ∘
      fun cc => (cc.com, (CClaim.val M cc).2, Lvm.QShape.tailC M cc)) = l.map (Lvm.QShape.tailC M) := fun l => rfl
  have hl0 := congrArg List.length htape
  simp only [List.length_map] at hl0
  rw [e1, e1, e1, e1, show ((fun x : Com × BlockClaim × FE => x.2.2) ∘ fun e : BlockClaim × FE => (Com.main, e.1, e.2)) =
    Prod.snd from rfl, List.map_snd_zip (by rw [List.length_map]; omega)]
  congr 1
  rw [← List.append_assoc, hnd']
  simp only [List.length_map, List.length_append, List.replicate_add, List.append_assoc, hl1, hl2, hl3]

end

end Lvm.Har
