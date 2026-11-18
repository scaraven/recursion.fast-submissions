-- New for lvm2 S2GT (GT-W, STMT 6): `PhiQGC_eq` — the fast `Φ_Q` at `E2` on the coordinate-split cache is `Φ_Q`.
import LvmE2VPhiTEq
import LvmWiringX

/-!
# STMT 6: `PhiQGC = PhiQFT`

* The terms of coordinate `s` are its entries (`PhiCache.okBX`): a sum over the terms' iterations of any
  function of the entry is the sum over `S1`'s entries of coordinate `s` (`w_terms_ents`).
* Both paths of `PhiQGCK` are `Σ_{s, j} X^s·sel_j·PhiPieceFT s j p'`: the slow path term by term
  (`termsSum2_eq`), the fast path by the simulation (`evalC2_cache`) with `ρ_j = sel_j / sel₀`.
* `PhiQCT_eq` closes.
-/

set_option autoImplicit false

namespace Lvm.Typed.KT

open Lvm Lvm.Typed Lvm.Typed.K Lvm.Loop

/-! ## Terms and entries (any summand) -/

section Rows

variable {M : Type} [AddCommMonoid M]

theorem w_sum_comm (m n : ℕ) (f : ℕ → ℕ → M) :
    ((List.range m).map fun a ↦ ((List.range n).map fun b ↦ f a b).sum).sum =
      ((List.range n).map fun b ↦ ((List.range m).map fun a ↦ f a b).sum).sum := by
  induction m with
  | zero => simp
  | succ m ih => simp only [List.sum_range_succ, ih, List.sum_map_add]

theorem w_sum_getD {α : Type} [Inhabited α] (l : List α) (h : α → M) :
    ((List.range l.length).map fun i ↦ h (l.getD i default)).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons, ← ih]
    rfl

theorem w_sum_keys (Q : Program) (lay : Lay) (s : Bool) (ts : List CTerm) (F : TSrc → ℕ → M)
    (hkeys : ts.map (fun t ↦ (t.src, t.idx)) = termKeysX Q lay s) :
    (ts.map fun t ↦ F t.src t.idx).sum =
      ((rowsOf Q lay).map fun src ↦ ((List.range (srcEntsX Q lay s src 0).length).map (F src)).sum).sum := by
  have : (ts.map fun t ↦ F t.src t.idx) = (ts.map fun t ↦ (t.src, t.idx)).map fun p ↦ F p.1 p.2 := by
    rw [List.map_map]; rfl
  rw [this, hkeys, termKeysX, tw_sum_flatMap]
  simp only [List.map_map, Function.comp_def]

theorem w_row_swap (Q : Program) (lay : Lay) (s : Bool) (G : Ent → M) (src : TSrc) :
    ((List.range (srcEntsX Q lay s src 0).length).map fun i ↦ ((List.range (2 ^ srcL Q lay src)).map fun jf ↦
      G ((srcEntsX Q lay s src jf).getD i default)).sum).sum =
    ((List.range (2 ^ srcL Q lay src)).map fun jf ↦ ((srcEntsX Q lay s src jf).map G).sum).sum := by
  rw [w_sum_comm (srcEntsX Q lay s src 0).length (2 ^ srcL Q lay src) fun i jf ↦
      G ((srcEntsX Q lay s src jf).getD i default)]
  apply congrArg
  apply List.map_congr_left
  intro jf _
  rw [← lhx_len Q lay s src jf]
  exact w_sum_getD (srcEntsX Q lay s src jf) G

/-- **The terms of a checked coordinate are its rows' entries**, for any summand of the entries. -/
theorem w_terms_rows (Q : Program) (lay : Lay) (s : Bool)
    (hc : PhiCache.okBX Q lay s ⟨(deriveTermsX Q lay s).toList, K.compileT (deriveTermsX Q lay s)⟩ = true)
    (G : Ent → M) :
    ((deriveTermsX Q lay s).toList.map fun t ↦ ((List.range (2 ^ t.l)).map fun jf ↦ G (t.at jf)).sum).sum =
      ((rowsOf Q lay).map fun src ↦ ((List.range (2 ^ srcL Q lay src)).map fun jf ↦
        ((srcEntsX Q lay s src jf).map G).sum).sum).sum := by
  set ts := deriveTermsX Q lay s
  unfold PhiCache.okBX at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Array.toArray_toList] at hc
  obtain ⟨⟨hkeys, hall⟩, hchk⟩ := hc
  have hl : ∀ t ∈ ts.toList, t.l = srcL Q lay t.src := fun t ht ↦ (hall t ht).1
  have hg := phi_checkTermsG (srcEntsX Q lay s) ts
    (fun k k' hk hk' hs ↦ by rw [hl _ (phi_getD_mem _ k hk), hl _ (phi_getD_mem _ k' hk'), hs]) hchk
  rw [List.map_congr_left fun t ht ↦ show ((List.range (2 ^ t.l)).map fun jf ↦ G (t.at jf)).sum =
      ((List.range (2 ^ srcL Q lay t.src)).map fun jf ↦ G ((srcEntsX Q lay s t.src jf).getD t.idx default)).sum by
    rw [← hl t ht]
    refine congrArg List.sum (List.map_congr_left fun jf hjf ↦ ?_)
    obtain ⟨k, hk, rfl⟩ := phi_mem_getD _ t ht
    rw [← hg k hk jf (List.mem_range.1 hjf), Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD]]
  rw [w_sum_keys Q lay s _ (fun src i ↦ ((List.range (2 ^ srcL Q lay src)).map fun jf ↦
      G ((srcEntsX Q lay s src jf).getD i default)).sum) hkeys]
  simp only [w_row_swap]

theorem w_foldr_eq_sum {α : Type} (f : α → M) (l : List α) :
    l.foldr (fun x acc ↦ f x + acc) 0 = (l.map f).sum := tw_foldr_sum l f

/-- `entsX` row by row (as `phiX_rows`, any summand). -/
theorem w_ents_rows (Q : Program) (lay : Lay) (H : Ent → M) :
    ((entsX Q lay).map H).sum = ((rowsOf Q lay).map fun src ↦ ((List.range (2 ^ srcL Q lay src)).map fun jf ↦
      ((rawX Q lay src jf).map H).sum).sum).sum := by
  unfold entsX rowsOf auxEnts
  simp only [List.map_append, List.sum_append, tw_sum_flatMap, phi_insts, List.map_map, Function.comp_def, srcL,
    rawX]
  congr 1
  · apply congrArg
    apply List.map_congr_left
    intro b _
    exact w_sum_comm _ _ _
  · apply congrArg
    apply List.map_congr_left
    intro k _
    exact w_sum_comm _ _ _

/-- A row's raw entries, coordinate `s` (entries below matrix `8`). -/
theorem w_raw_split (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : Bool) (G : Ent → M) (src : TSrc) (jf : ℕ) :
    ((rawX Q lay src jf).map fun e ↦ if (e.o / 4 == 1) == s then G { e with o := e.o % 4 } else 0).sum =
      ((srcEntsX Q lay s src jf).map G).sum := by
  cases src with
  | row b t =>
    simp only [rawX, srcEntsX, List.map_map]
    rw [← tw_sum_filter_map]
    rfl
  | aux k r =>
    have ho := auxRowEnts_o' hlay k r jf
    simp only [rawX, srcEntsX]
    cases s with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
      have h4 := ho e he
      rw [if_pos (by simp [show e.o / 4 = 0 by omega]), Nat.mod_eq_of_lt h4]
    | true =>
      simp only [↓reduceIte, List.map_nil, List.sum_nil]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      have h4 := ho e he
      rw [if_neg (by simp [show e.o / 4 = 0 by omega])]

/-- **Coordinate `s`'s rows are `S1`'s entries of coordinate `s`** (matrix `o mod 4`). -/
theorem w_rows_ents (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : Bool) (G : Ent → M) :
    ((rowsOf Q lay).map fun src ↦ ((List.range (2 ^ srcL Q lay src)).map fun jf ↦
        ((srcEntsX Q lay s src jf).map G).sum).sum).sum =
      ((entsX Q lay).map fun e ↦ if (e.o / 4 == 1) == s then G { e with o := e.o % 4 } else 0).sum := by
  rw [w_ents_rows]
  simp only [w_raw_split Q lay hlay s G]

end Rows

/-- A `K`-linear coefficient map `c ↦ Σ_j σ_j·c_j` (both `lamS` and `lamE` are). -/
def coefMap (σ0 σ1 σ2 : FE2) (c : FE) : FE2 := σ0 * FE2.ofK c.c₀ + σ1 * FE2.ofK c.c₁ + σ2 * FE2.ofK c.c₂

/-! ## The slow path -/

theorem w_foldl_add {α : Type} (l : List α) (f : α → FE2) (a : FE2) :
    l.foldl (fun acc x ↦ a2 acc (f x)) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp only [List.map_cons, List.sum_cons, a2_fun]; ring

theorem lamS_eq (s0 s1 s2 : FE2) (c : FE) : lamS s0 s1 s2 c = coefMap s0 s1 s2 c := by
  simp only [lamS, coefMap, a2_fun, mK_eq]

/-- **The slow path** is the terms' sums under `lamS`. -/
theorem termsSum2_eq (s0 s1 s2 : FE2) (ts : List CTerm) (p' : List FE2) :
    termsSum2 s0 s1 s2 ts p' = (ts.map fun t ↦ ((List.range (2 ^ t.l)).map fun jf ↦
      coefMap s0 s1 s2 (t.at jf).c * eqWT p' (t.at jf).idx).sum).sum := by
  unfold termsSum2
  suffices h : ∀ a : FE2, ts.foldl (fun acc t ↦ (List.range (2 ^ t.l)).foldl (fun acc jf ↦
      a2 acc (m2 (lamS s0 s1 s2 (t.at jf).c) (eqWT p' (t.at jf).idx))) acc) a = a + (ts.map fun t ↦
        ((List.range (2 ^ t.l)).map fun jf ↦ coefMap s0 s1 s2 (t.at jf).c * eqWT p' (t.at jf).idx).sum).sum by
    rw [h 0, zero_add]
  intro a
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, w_foldl_add]
    simp only [m2_fun, lamS_eq]
    ring

/-! ## The fast path -/

theorem eqWG_eqWT (l : List FE2) (x : ℕ) : eqWG l x = eqWT l x := by
  induction l generalizing x with
  | nil => rfl
  | cons r rs ih => simp only [eqWG, eqWT, ih, kt_sub2]

theorem nat_eqWG {R S : Type} [CommRing R] [CharP R 2] [CommRing S] [CharP S 2] (f : R →+* S) (l : List R)
    (x : ℕ) : eqWG (l.map f) x = f (eqWG l x) := by
  induction l generalizing x with
  | nil => simp [eqWG]
  | cons r rs ih => simp only [List.map_cons, eqWG, ih, map_mul, apply_ite f, map_sub, map_one]

theorem lamE_coef (L : Lam) (c : FE) : lamE L c = coefMap 1 L.r1 L.r2 c := by
  simp only [lamE, coefMap]
  ring

/-- **The fast path on a checked, linear coordinate** is the terms' sums under `λ/sel₀`. -/
theorem evalC2_cache (L : Lam) (Q : Program) (lay : Lay) (s : Bool)
    (hcs : PhiCache.okBX Q lay s ⟨(deriveTermsX Q lay s).toList, K.compileT (deriveTermsX Q lay s)⟩ = true)
    (hl : linOk (K.compileT (deriveTermsX Q lay s)) = true) (p' : List FE2) (hp' : p'.length = 2 + xVars + yVars) :
    evalC2 L (K.compileT (deriveTermsX Q lay s)) p' = some ((deriveTermsX Q lay s).toList.map fun t ↦
      ((List.range (2 ^ t.l)).map fun jf ↦ coefMap 1 L.r1 L.r2 (t.at jf).c * eqWT p' (t.at jf).idx).sum).sum := by
  have hwf : ∀ t ∈ deriveTermsX Q lay s, K.TermWF t := by
    unfold PhiCache.okBX at hcs
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcs
    exact fun t ht ↦ phi_termWF t (hcs.1.2 t (Array.mem_toList_iff.2 ht)).2
  rw [evalC2_sim L _ hl p', compileT_eqG _ hwf (ptA p') (by simp [ptA, hp'])]
  congr 1
  rw [show lam L = lamAdd L from rfl, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ ↦ ?_)
  rw [Function.comp_apply, termSumG, tw_foldr_sum, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun jf _ ↦ ?_)
  simp only [Function.comp_apply, termAtG, ptA, nat_eqWG emb, show lamAdd L = (lam L : FEA → FE2) from rfl]
  rw [lam_ofE_mul_emb, eqWG_eqWT, lamE_coef, mul_comm]
  rfl

/-! ## The two paths -/

/-- **A coordinate's entry sum under a coefficient map is the pieces' combination.** -/
theorem w_piece (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : Bool) (σ0 σ1 σ2 : FE2) (p' : List FE2) :
    ((entsX Q lay).map fun e ↦ if (e.o / 4 == 1) == s then
        coefMap σ0 σ1 σ2 e.c * eqWT p' ({ e with o := e.o % 4 } : Ent).idx else 0).sum =
      σ0 * PhiPieceFT Q lay (if s then 1 else 0) 0 p' + σ1 * PhiPieceFT Q lay (if s then 1 else 0) 1 p' +
        σ2 * PhiPieceFT Q lay (if s then 1 else 0) 2 p' := by
  have hp : ∀ e ∈ entsX Q lay, ((e.o / 4 == 1) == s) = (e.o / 4 == if s then 1 else 0) := by
    intro e he
    have := tw_entsX_o Q lay hlay e he
    have h8 : e.o / 4 = 0 ∨ e.o / 4 = 1 := by omega
    rcases h8 with h | h <;> cases s <;> simp [h]
  unfold PhiPieceFT
  simp only [tw_foldr_filter, ← List.sum_map_mul_left, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  rw [hp e he]
  split_ifs <;> first | (simp only [coefMap, feCoord, Ent.idx]; ring) | simp

/-- **STMT 6** (S2GT-W): the fast `Φ_Q` at `E2` on a checked, linear cache is `Φ_Q`. -/
theorem PhiQGC_eqW (Q : Lvm.Loop.Program) (lay : Lay) (hlay : lay.Ok Q)
    (hc : (Lvm.Typed.cacheWX Q lay).okB Q lay = true) (hlin : linOkX (Lvm.Typed.cacheWX Q lay) = true)
    (pt : List FE2) (hpt : pt.length = phiVarsT) :
    PhiQGCK (Lvm.Typed.cacheWX Q lay) pt = PhiQFT Q lay pt := by
  -- the pieces' form (`PhiQCT_eq`)
  rw [← PhiQCT_eq Q lay hlay (fun s j p ↦ PhiPieceFT Q lay s j p) (fun _ _ _ _ _ _ ↦ rfl) pt hpt]
  obtain ⟨p0, p1, p2, p3, rest, rfl⟩ : ∃ p0 p1 p2 p3 rest, pt = p0 :: p1 :: p2 :: p3 :: rest := by
    match pt, hpt with
    | p0 :: p1 :: p2 :: p3 :: rest, _ => exact ⟨p0, p1, p2, p3, rest, rfl⟩
  have hrest : (p0 :: p1 :: rest).length = 2 + xVars + yVars := by
    simp only [List.length_cons, phiVarsT, selBitsT] at hpt ⊢; omega
  have hc0 := (Bool.and_eq_true _ _).mp hc
  have hl0 := (Bool.and_eq_true _ _).mp hlin
  -- each coordinate under a coefficient map
  have hcoord : ∀ (s : Bool) (σ0 σ1 σ2 : FE2),
      ((deriveTermsX Q lay s).toList.map fun t ↦ ((List.range (2 ^ t.l)).map fun jf ↦
        coefMap σ0 σ1 σ2 (t.at jf).c * eqWT (p0 :: p1 :: rest) (t.at jf).idx).sum).sum =
      σ0 * PhiPieceFT Q lay (if s then 1 else 0) 0 (p0 :: p1 :: rest) +
        σ1 * PhiPieceFT Q lay (if s then 1 else 0) 1 (p0 :: p1 :: rest) +
        σ2 * PhiPieceFT Q lay (if s then 1 else 0) 2 (p0 :: p1 :: rest) := by
    intro s σ0 σ1 σ2
    have hcs : PhiCache.okBX Q lay s ⟨(deriveTermsX Q lay s).toList, K.compileT (deriveTermsX Q lay s)⟩ = true := by
      cases s
      · exact hc0.1
      · exact hc0.2
    exact (w_terms_rows Q lay s hcs (fun e ↦ coefMap σ0 σ1 σ2 e.c * eqWT (p0 :: p1 :: rest) e.idx)).trans
      ((w_rows_ents Q lay hlay s _).trans (w_piece Q lay hlay s σ0 σ1 σ2 _))
  -- the target, `Σ_s X^s Σ_j sel_j·piece(s, j)`
  have hX : ∀ v : FE2, mX v = ⟨0, 1⟩ * v := mX_eq
  set P := fun (s j : ℕ) ↦ PhiPieceFT Q lay s j (p0 :: p1 :: rest) with hP
  have htarget : PhiQCT (fun s j p ↦ PhiPieceFT Q lay s j p) (p0 :: p1 :: p2 :: p3 :: rest) =
      (selJT 0 p2 p3 * P 0 0 + selJT 1 p2 p3 * P 0 1 + selJT 2 p2 p3 * P 0 2) +
        ⟨0, 1⟩ * (selJT 0 p2 p3 * P 1 0 + selJT 1 p2 p3 * P 1 1 + selJT 2 p2 p3 * P 1 2) := by
    simp only [PhiQCT, List.getD_cons_succ, List.getD_cons_zero, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append, hP]
    rw [show List.range 2 = [0, 1] from rfl, show List.range 3 = [0, 1, 2] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, xPowT]
    simp only [Nat.one_ne_zero, ↓reduceIte, one_mul]
    ring
  rw [htarget]
  have hsel : m2 (a2 1 p2) (a2 1 p3) = selJT 0 p2 p3 ∧ m2 p2 (a2 1 p3) = selJT 1 p2 p3 ∧
      m2 (a2 1 p2) p3 = selJT 2 p2 p3 := ⟨by simp [m2_fun, a2_fun, selJT], by simp [m2_fun, a2_fun, selJT],
        by simp [m2_fun, a2_fun, selJT]⟩
  -- the slow path
  have hslow : a2 (termsSum2 (selJT 0 p2 p3) (selJT 1 p2 p3) (selJT 2 p2 p3) (deriveTermsX Q lay false).toList
      (p0 :: p1 :: rest)) (mX (termsSum2 (selJT 0 p2 p3) (selJT 1 p2 p3) (selJT 2 p2 p3)
        (deriveTermsX Q lay true).toList (p0 :: p1 :: rest))) =
      (selJT 0 p2 p3 * P 0 0 + selJT 1 p2 p3 * P 0 1 + selJT 2 p2 p3 * P 0 2) +
        ⟨0, 1⟩ * (selJT 0 p2 p3 * P 1 0 + selJT 1 p2 p3 * P 1 1 + selJT 2 p2 p3 * P 1 2) := by
    rw [termsSum2_eq, termsSum2_eq, hX, a2_fun, hcoord, hcoord]
    simp only [Bool.false_eq_true, ↓reduceIte, hP]
  have hC : Lvm.Typed.cacheWX Q lay = ⟨⟨(deriveTermsX Q lay false).toList, K.compileT (deriveTermsX Q lay false)⟩,
      ⟨(deriveTermsX Q lay true).toList, K.compileT (deriveTermsX Q lay true)⟩⟩ := rfl
  unfold PhiQGCK
  rw [hC]
  dsimp only
  simp only [List.getD_cons_succ, List.getD_cons_zero, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append, hsel.1, hsel.2.1, hsel.2.2]
  split_ifs with h0
  · exact hslow
  · have hne : selJT 0 p2 p3 ≠ 0 := by simpa using h0
    rw [evalC2_cache _ Q lay false hc0.1 hl0.1 _ hrest, evalC2_cache _ Q lay true hc0.2 hl0.2 _ hrest]
    simp only [hcoord, Bool.false_eq_true, ↓reduceIte, hX, m2_fun, a2_fun, hP]
    field_simp

end Lvm.Typed.KT
