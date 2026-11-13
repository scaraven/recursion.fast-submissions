-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's claims and openings: the circuit's typed claims
-- (`typedClaimsC`: `regClaimG`'s sum claims, the relayout's point claim, the mini-bus's table claims) are V_S's
-- (`typedClaimsN` and `tableClaimsR`) on each commitment, and the openings at ν = 23 in both shapes (`dOpenT`) read
-- only each commitment's claims: `dOpenT` is roll 7's `Shape.dOpenZ` at `P20`, so `openPhZ_run` runs it.
import LvmQTypedHarB
import LvmQAsmHarTails

/-!
# The typed claims and the openings

* **`regClaimG_val`**: `regClaimG`'s sum claim, on regions that are V_S's, is V_S's region claim
  `⟨⟨ν, 0⟩, affW N s r_y, v⟩` (the selector `eq(r_y^{≥ log}, base ≫ log)` is `hiW`, a block's `eqAbove` is
  `eqAtF` of its target, `eqConstG`'s value is `eqAtF`).
* **`typedClaimsC_val`**: the circuit's typed claims on `C_rec` are V_S's relayout point claim, `σ′`'s region claim
  and the mini-bus's `C_rec` table claims; on `C_main` the committed regions' and `KS`'s claims and the mini-bus's
  `C_main` table claims.
* **`dOpenT_congr`**: `dOpenT` reads only each commitment's claims (`C_rec`'s on the stack, `C_main`'s with their
  tails in the small shape); **`dOpenT_P20`**: at `P20` it is `Shape.dOpenZ` at `smallP`.
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

/-- **The circuit's typed claims are V_S's** on each commitment: on `C_rec` the relayout's point claim, `σ′`'s region
claim and the mini-bus's `C_rec` table claims; on `C_main` the committed regions', `KS`'s and the mini-bus's
`C_main` table claims. -/
theorem typedClaimsC_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {Td : TData} {N : TNat}
    (htd : TdOk Td N) (nu : Nat) (t : TypedC) (st : List Lvm.M3.Tab) (hst : Td.mbS = st.map Lvm.M3.Tab.shape)
    (p : Ptr) (h : SegsHold c M p (typedClaimsC z o Td nu t p).2) :
    (typedClaimsC z o Td nu t p).1.1.map (CClaim.val M) =
      (.crec, BlockClaim.point ⟨19, 0⟩ (vs M t.rr) (t.vR.val M)) ::
        (.crec, ⟨⟨19, 0⟩, TypedV.affW N .sigma (vs M t.ry), (t.rv.getD 2 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))).filter (·.1 == .crec) ∧
    (typedClaimsC z o Td nu t p).1.2.map (CClaim.val M) =
      (.main, ⟨⟨nu, 0⟩, TypedV.affW N .com (vs M t.ry), (t.rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨nu, 0⟩, TypedV.affW N .ks (vs M t.ry), (t.rv.getD 3 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st (t.tab.map fun e => (vs M e.1, vs M e.2))).filter (·.1 == .main) ∧
    (∀ cc ∈ (typedClaimsC z o Td nu t p).1.1, cc.com = .crec) ∧
    (∀ cc ∈ (typedClaimsC z o Td nu t p).1.2, cc.com = .main) := by
  simp only [typedClaimsC, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  have e1 := regClaimG_val hz ho .crec tR N .sigma Td.sig htd.sig t.ry (t.rv.getD 2 z) p h.1
  have e2 := regClaimG_val hz ho .main nu N .com Td.com htd.com t.ry (t.rv.getD 0 z) _ h.2.1
  have e3 := regClaimG_val hz ho .main nu N .ks Td.ks htd.ks t.ry (t.rv.getD 3 z) _ h.2.2
  have hv := tabClaims_val hz st t.tab
  rw [← hst] at hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.map_cons, List.map_cons, e1, filter_val, hv]; rfl
  · rw [List.map_cons, List.map_cons, e2, e3, filter_val, hv]
  · intro cc hcc
    simp only [List.mem_cons, List.mem_filter, beq_iff_eq] at hcc
    rcases hcc with rfl | rfl | ⟨-, h⟩
    · rfl
    · simp [regClaimG, bind_apply, pure_apply]
    · exact h
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

/-- **`dOpenT` reads only each commitment's claims** (`C_rec`'s, `C_main`'s, and `C_main`'s tails in the small
shape). -/
theorem dOpenT_congr (p : Params) (s : Bool) (l₁ l₂ : List (Com × BlockClaim × FE))
    (hr : (l₁.filter (·.1 == .crec)).map (·.2.1) = (l₂.filter (·.1 == .crec)).map (·.2.1))
    (hm : (l₁.filter (·.1 == .main)).map (·.2.1) = (l₂.filter (·.1 == .main)).map (·.2.1))
    (ht : s = true → (l₁.filter (·.1 == .main)).map (·.2.2) = (l₂.filter (·.1 == .main)).map (·.2.2)) :
    TypedV.dOpenT p s l₁ = TypedV.dOpenT p s l₂ := by
  unfold TypedV.dOpenT
  have er : ∀ l : List (Com × BlockClaim × FE), (l.filter (·.1 == .crec)).map (·.2.1.onStack) =
      ((l.filter (·.1 == .crec)).map (·.2.1)).map (·.onStack) := fun l => by rw [List.map_map]; rfl
  rw [er l₁, er l₂, hr]
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

/-- **At `P20`, `dOpenT` is roll 7's `Shape.dOpenZ`** (ν = 23: `onStackZBN 23 = onStackZB`). -/
theorem dOpenT_P20 (s : Bool) (l : List (Com × BlockClaim × FE)) :
    TypedV.dOpenT P20 s l = Shape.dOpenZ P20 s l := by
  unfold TypedV.dOpenT Shape.dOpenZ Shape.onStackZsF
  rw [show P20.nuMain = 23 from rfl, TypedV.onStackZBN_23]

/-! ## V_S's claim list against the circuit's -/

section
variable {M : Mem}

/-- `noDRB` is roll 7's `noDR`. -/
theorem noDRB_eq (cc : CClaim) : noDRB cc = noDR cc := rfl

/-- The claims of one commitment through the projection on (commitment, claim). -/
theorem filter_proj (l : List (Com × BlockClaim × FE)) (com : Com) :
    (l.filter (·.1 == com)).map (·.2.1) = ((l.map fun e => (e.1, e.2.1)).filter (·.1 == com)).map (·.2) := by
  rw [List.filter_map, List.map_map]; rfl

theorem filter_all {α : Type} {l : List α} {f : α → Bool} (h : ∀ x ∈ l, f x = true) : l.filter f = l :=
  List.filter_eq_self.mpr h

theorem filter_none {α : Type} {l : List α} {f : α → Bool} (h : ∀ x ∈ l, f x = false) : l.filter f = [] :=
  List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]

theorem filter_filter_com (l : List (Com × BlockClaim)) (a b : Com) :
    (l.filter (·.1 == a)).filter (·.1 == b) = if a = b then l.filter (·.1 == a) else [] := by
  rw [List.filter_filter]
  split_ifs with h
  · subst h; congr 1; funext x; cases x.1 == a <;> rfl
  · refine filter_none fun x _ => ?_
    by_cases hx : x.1 = a
    · simp [hx, h]
    · simp [hx]

/-- **V_S's openings on its claim list are its openings on the circuit's claims** (with their tails): the typed
claims (`[A, B]` on `C_rec`, `[C, D]` on `C_main`, tail `0`) and the mini-bus's table claims `tabs` (tail `0`) on
V_S's side, the circuit's `C_rec` claims `tc₁` and `C_main` claims `tc₂` (the table claims split by commitment), and
the rest equal on both sides (in the small shape with their tails). -/
theorem openClaims_eq (p : Params) (s : Bool) (A B Cc D : BlockClaim) (tabs : List (Com × BlockClaim))
    (tc₁ tc₂ rest : List CClaim) (restV : List (Com × BlockClaim × FE))
    (h1 : tc₁.map (CClaim.val M) = (.crec, A) :: (.crec, B) :: tabs.filter (·.1 == .crec))
    (h2 : tc₂.map (CClaim.val M) = (.main, Cc) :: (.main, D) :: tabs.filter (·.1 == .main))
    (hc1 : ∀ cc ∈ tc₁, cc.com = .crec) (hc2 : ∀ cc ∈ tc₂, cc.com = .main) (hnd : tc₂.all noDRB = true)
    (hr : rest.map (CClaim.val M) = restV.map fun e => (e.1, e.2.1))
    (ht : s = true → claimsT M rest = restV) :
    TypedV.dOpenT p s ([(.crec, A, 0), (.crec, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
        (Shape.zeroTails ([] ++ tabs) ++ restV)) =
      TypedV.dOpenT p s (claimsT M (tc₁ ++ tc₂ ++ rest)) := by
  have hP : (claimsT M (tc₁ ++ tc₂ ++ rest)).map (fun e => (e.1, e.2.1)) =
      ((.crec, A) :: (.crec, B) :: tabs.filter (·.1 == .crec)) ++
        ((.main, Cc) :: (.main, D) :: tabs.filter (·.1 == .main)) ++ restV.map fun e => (e.1, e.2.1) := by
    rw [claimsT_proj, List.map_append, List.map_append, h1, h2, hr]
  have hV : ([(.crec, A, 0), (.crec, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
      (Shape.zeroTails ([] ++ tabs) ++ restV) : List (Com × BlockClaim × FE)).map (fun e => (e.1, e.2.1)) =
      [(.crec, A), (.crec, B), (.main, Cc), (.main, D)] ++ (tabs ++ restV.map fun e => (e.1, e.2.1)) := by
    rw [List.map_append, List.map_append, Shape.map_zeroTails, List.nil_append]; rfl
  have hcom : ∀ c' : Com, c' = .crec ∨ c' = .main := fun c' => by cases c' <;> simp
  apply dOpenT_congr
  · rw [filter_proj, filter_proj, hP, hV]
    simp only [List.filter_append, List.filter_cons, filter_filter_com]
    simp
  · rw [filter_proj, filter_proj, hP, hV]
    simp only [List.filter_append, List.filter_cons, filter_filter_com]
    simp
  · intro hs
    have hR := ht hs
    -- the tails: `0` on the typed and table claims, the rest's on both sides
    have ec1 : (claimsT M tc₁).filter (·.1 == .main) = [] := by
      refine filter_none fun e he => ?_
      obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he
      simp [hc1 cc hcc]
    have ec2 : (claimsT M tc₂).filter (·.1 == .main) = claimsT M tc₂ := by
      refine filter_all fun e he => ?_
      obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp he
      simp [hc2 cc hcc]
    have et2 : (claimsT M tc₂).map (·.2.2) = List.replicate tc₂.length 0 := by
      rw [claimsT, List.map_map]
      exact map_tailC_zero tc₂ (by simpa [noDRB_eq] using hnd)
    have hl2 := congrArg List.length h2
    simp only [List.length_map, List.length_cons] at hl2
    have ez : ((Shape.zeroTails ([] ++ tabs)).filter (·.1 == .main)).map (·.2.2) =
        List.replicate (tabs.filter (·.1 == .main)).length 0 := by
      rw [List.nil_append, Shape.zeroTails, List.filter_map, List.map_map, List.eq_replicate_iff]
      refine ⟨by simp [Function.comp_def], fun b hb => ?_⟩
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp hb
      rfl
    have eR : ((claimsT M (tc₁ ++ tc₂ ++ rest)).filter (·.1 == .main)).map (·.2.2) =
        List.replicate (2 + (tabs.filter (·.1 == .main)).length) 0 ++ (restV.filter (·.1 == .main)).map (·.2.2) := by
      rw [show claimsT M (tc₁ ++ tc₂ ++ rest) = claimsT M tc₁ ++ claimsT M tc₂ ++ claimsT M rest by
        simp [claimsT], hR, List.filter_append, List.filter_append, ec1, ec2, List.nil_append, List.map_append, et2,
        hl2]
      congr 2; omega
    have eL : (([(.crec, A, 0), (.crec, B, 0), (.main, Cc, 0), (.main, D, 0)] ++
        (Shape.zeroTails ([] ++ tabs) ++ restV) : List (Com × BlockClaim × FE)).filter (·.1 == .main)).map (·.2.2) =
        [0, 0] ++ (List.replicate (tabs.filter (·.1 == .main)).length 0 ++
          (restV.filter (·.1 == .main)).map (·.2.2)) := by
      rw [List.filter_append, List.map_append, List.filter_append, List.map_append, ez]
      rfl
    rw [eL, eR, ← List.append_assoc, List.replicate_add]
    rfl

theorem zipProj (L : List BlockClaim) (T : List FE) (h : T.length = L.length) :
    ((L.zip T).map fun e => (Com.main, e.1, e.2)).map (fun e => (e.1, e.2.1)) = L.map (Com.main, ·) := by
  induction L generalizing T with
  | nil => rfl
  | cons a L ih => cases T with
    | nil => simp at h
    | cons b T => simp only [List.zip_cons_cons, List.map_cons]; rw [ih T (by simpa using h)]

theorem zipTails (L : List BlockClaim) (T : List FE) (h : T.length = L.length) :
    ((L.zip T).map fun e => (Com.main, e.1, e.2)).map (·.2.2) = T := by
  induction L generalizing T with
  | nil => cases T with
    | nil => rfl
    | cons _ _ => simp at h
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
      (.crec, BlockClaim.point ⟨19, 0⟩ (vs M rr) (vR.val M)) ::
        (.crec, ⟨⟨19, 0⟩, TypedV.affW N .sigma (vs M ry), (rv.getD 2 z).val M⟩) ::
          (m.tableClaims pub evals).filter (·.1 == .crec))
    (h2 : tc₂.map (CClaim.val M) =
      (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .com (vs M ry), (rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨p.nuMain, 0⟩, TypedV.affW N .ks (vs M ry), (rv.getD 3 z).val M⟩) ::
          (m.tableClaims pub evals).filter (·.1 == .main))
    (hc1 : ∀ cc ∈ tc₁, cc.com = .crec) (hc2 : ∀ cc ∈ tc₂, cc.com = .main) (hnd2 : tc₂.all noDRB = true)
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
      [(.crec, BlockClaim.point ⟨19, 0⟩ (vs M rr) (vR.val M), 0),
        (.crec, ⟨⟨19, 0⟩, TypedV.affW N .sigma (vs M ry), (rv.getD 2 z).val M⟩, 0),
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
  refine openClaims_eq p s _ _ _ _ _ tc₁ tc₂ _ _ h1 h2 hc1 hc2 hnd2 hP.symm fun hs => ?_
  refine list_eq_of_proj _ _ (by rw [claimsT_proj, hP]) ?_
  have hnd' : (kC ++ ksOut ++ clK).map (Lvm.QShape.tailC M) = List.replicate (kC ++ ksOut ++ clK).length 0 :=
    map_tailC_zero _ (by simpa [noDRB_eq] using hnd)
  have hl1 := congrArg List.length hks
  have hl2 := congrArg List.length hko
  have hl3 := congrArg List.length hkl
  simp only [List.length_map] at hl1 hl2 hl3
  simp only [claimsT, List.map_map, List.map_append, List.append_assoc, zipTails _ _ hlt, Shape.zeroTails_tails',
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
