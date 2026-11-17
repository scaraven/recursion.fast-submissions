-- New for lvm2 VQ2 (VQ2-T): the fast twin `PhiQGCKT` of `PhiQGCK` (repeated products read once, tables shared
-- between the coordinates) is `PhiQGCK` (`PhiQGCKT_eq`; `NTB20` runs the twin).
import LvmE2VPhiTEq

/-!
# `PhiQGCKT = PhiQGCK`

* **Repeated products**: a checked rewrite (`cseOkL`) runs on `F' = F ++ E` as the code on `F`, instruction by
  instruction (`cse_step`): an unchanged instruction reads `F'` outside `E`'s range, where it is `F`; a rewritten
  one reads `E[k] = F[a]·F[b]`, its op-`7` product.
* **Shared tables**: `tabsAt2` is `tabsFin2` over `tab02` (`tabsAt2_split`); a shared table is `tab02` of an equal
  recipe (`tab0Sh_eq`).
-/

set_option autoImplicit false

namespace Lvm.Typed.KT

open Lvm Lvm.Typed.K

/-! ## Repeated products -/

theorem cse_getD_out (F : Array FE2) (ps : Array ℕ) (x : ℕ) (h : x < F.size ∨ F.size + ps.size ≤ x) :
    (F ++ ps.map (pairV F)).getD x 0 = F.getD x 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  rcases h with h | h
  · rw [if_pos h]
  · rw [if_neg (by omega), Array.getElem?_eq_none (by simp only [Array.size_map]; omega),
      Array.getElem?_eq_none (by omega)]

theorem cse_getD_in (F : Array FE2) (ps : Array ℕ) (c : ℕ) (h1 : F.size ≤ c) (h2 : c < F.size + ps.size) :
    (F ++ ps.map (pairV F)).getD c 0 = pairV F (ps.getD (c - F.size) 0) := by
  have hc : c - F.size < ps.size := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append, if_neg (by omega), Array.getElem?_map,
    Array.getElem?_eq_getElem hc, Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hc, Option.getD_some]

/-- `fstep2` reads `F` only at the operands its op reads. -/
theorem fstep2_congr (L : Lam) (F F' : Array FE2) (W : Array FE) (s : FE2 × Array FE2 × Array (ℕ × FE2)) (n : ℕ)
    (ha : rdA (n &&& 15) = true → F'.getD ((n >>> 6) &&& 0xFFFFF) 0 = F.getD ((n >>> 6) &&& 0xFFFFF) 0)
    (hb : rdB (n &&& 15) = true → F'.getD ((n >>> 26) &&& 0xFFFFF) 0 = F.getD ((n >>> 26) &&& 0xFFFFF) 0) :
    fstep2 L F' W s n = fstep2 L F W s n := by
  unfold fstep2
  dsimp only
  by_cases h7 : (n &&& 15 == 7) = true
  · rw [if_pos h7, if_pos h7, ha (by simp [rdA, h7]), hb (by simp [rdB, h7])]
  rw [if_neg h7, if_neg h7]
  by_cases h5 : (n &&& 15 == 5) = true
  · rw [if_pos h5, if_pos h5, ha (by simp [rdA, h5])]
  rw [if_neg h5, if_neg h5]
  by_cases h6 : (n &&& 15 == 6) = true
  · rw [if_pos h6, if_pos h6, ha (by simp [rdA, h6])]
  rw [if_neg h6, if_neg h6]
  by_cases h3 : (n &&& 15 == 3) = true
  · rw [if_pos h3, if_pos h3, ha (by simp [rdA, h3])]
  rw [if_neg h3, if_neg h3]
  by_cases h1 : (n &&& 15 == 1) = true
  · rw [if_pos h1, if_pos h1, ha (by simp [rdA, h1])]
  rw [if_neg h1, if_neg h1]
  by_cases h0 : (n &&& 15 == 0) = true
  · rw [if_pos h0, if_pos h0]
  rw [if_neg h0, if_neg h0]
  by_cases h8 : (n &&& 15 == 8) = true
  · rw [if_pos h8, if_pos h8, ha (by simp [rdA, h8]), hb (by simp [rdB, h8])]
  rw [if_neg h8, if_neg h8]
  by_cases h4 : (n &&& 15 == 4) = true
  · rw [if_pos h4, if_pos h4]
  rw [if_neg h4, if_neg h4]
  by_cases h2 : (n &&& 15 == 2) = true
  · rw [if_pos h2, if_pos h2, ha (by simp [rdA, h2])]
  rw [if_neg h2, if_neg h2]

/-- **One checked instruction** on `F ++ E` is the original on `F`. -/
theorem cse_step (L : Lam) (F : Array FE2) (W : Array FE) (ps : Array ℕ) (n' n : ℕ)
    (h : cseIns F.size ps n' n = true) (s : FE2 × Array FE2 × Array (ℕ × FE2)) :
    fstep2 L (F ++ ps.map (pairV F)) W s n' = fstep2 L F W s n := by
  unfold cseIns at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨rfl, ha⟩, hb⟩ | ⟨⟨h7, h5⟩, ⟨h1, h2⟩, hq⟩
  · refine fstep2_congr L F _ W s n' (fun hr ↦ cse_getD_out F ps _ ?_) (fun hr ↦ cse_getD_out F ps _ ?_)
    · rcases ha with (ha | ha) | ha
      · rw [hr] at ha; exact absurd ha Bool.false_ne_true
      · exact Or.inl ha
      · exact Or.inr ha
    · rcases hb with (hb | hb) | hb
      · rw [hr] at hb; exact absurd hb Bool.false_ne_true
      · exact Or.inl hb
      · exact Or.inr hb
  · have e7 : (n' &&& 15 == 7) = false := by rw [h5]; rfl
    have e5 : (n' &&& 15 == 5) = true := by rw [h5]; rfl
    have f7 : (n &&& 15 == 7) = true := by rw [h7]; rfl
    unfold fstep2
    simp only [e7, e5, f7, if_true, Bool.false_eq_true, if_false]
    rw [cse_getD_in F ps _ h1 h2, pairV]
    rcases hq with ⟨hqa, hqb⟩ | ⟨hqa, hqb⟩
    · rw [hqa, hqb]
    · rw [hqa, hqb, m2_eq, m2_eq, mul_comm]

/-- Folds over lists related entrywise by `P`, of steps equal on related entries, are equal. -/
theorem foldl_allZ {β : Type} (P : ℕ → ℕ → Bool) (f g : β → ℕ → β) (hP : ∀ x y, P x y = true → ∀ s, f s x = g s y) :
    ∀ (l' l : List ℕ), allZ P l' l = true → ∀ s, l'.foldl f s = l.foldl g s := by
  intro l'
  induction l' with
  | nil =>
    intro l h s
    cases l with
    | nil => rfl
    | cons y l => exact absurd h Bool.false_ne_true
  | cons x l' ih =>
    intro l h s
    cases l with
    | nil => exact absurd h Bool.false_ne_true
    | cons y l =>
      simp only [allZ, Bool.and_eq_true] at h
      rw [List.foldl_cons, List.foldl_cons, hP x y h.1 s]
      exact ih l h.2 _

/-- **A checked rewrite** folds as the original. -/
theorem cse_fold (L : Lam) (F : Array FE2) (W : Array FE) (ps : Array ℕ) (l' l : List ℕ)
    (h : cseOkL F.size ps l' l = true) (s : FE2 × Array FE2 × Array (ℕ × FE2)) :
    l'.foldl (fstep2 L (F ++ ps.map (pairV F)) W) s = l.foldl (fstep2 L F W) s :=
  foldl_allZ (cseIns F.size ps) _ _ (fun x y hxy s ↦ cse_step L F W ps x y hxy s) l' l h s

theorem cse_runF2 (L : Lam) (F : Array FE2) (ps : Array ℕ) (fc fc' : FCode) (hw : fc'.ws = fc.ws)
    (h : cseOkL F.size ps fc'.ins.toList fc.ins.toList = true) :
    runF2 L (F ++ ps.map (pairV F)) fc' = runF2 L F fc := by
  rw [runF2_fold, runF2_fold, hw, cse_fold L F fc.ws ps _ _ h]

theorem opt_bind_congr {α β : Type} (o : Option α) (f g : α → Option β) (h : ∀ x, o = some x → f x = g x) :
    (o >>= f) = (o >>= g) := by
  cases o with
  | none => rfl
  | some x => exact h x rfl

theorem foldlM_congr_mem {α β : Type} (l : List α) (f g : β → α → Option β)
    (h : ∀ x ∈ l, ∀ b, f b x = g b x) : ∀ b, l.foldlM f b = l.foldlM g b := by
  induction l with
  | nil => intro b; rfl
  | cons x l ih =>
    intro b
    rw [List.foldlM_cons, List.foldlM_cons, h x List.mem_cons_self b]
    exact congrArg (Bind.bind _) (funext fun b ↦ ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) b)

theorem runPassF2_cse (L : Lam) (P : Pt2) (T : Array (Array FE2)) (F : Array FE2) (ps : Array ℕ) (p : Pass)
    (pf : FCode) (h : cseOkL F.size ps pf.ins.toList pf.ins.toList = true) :
    runPassF2 L P T (F ++ ps.map (pairV F)) p pf = runPassF2 L P T F p pf := by
  unfold runPassF2
  rw [cse_runF2 L F ps pf pf rfl h]

/-- **The passes on `F ++ E`** (their codes checked as unchanged) are the passes on `F`. -/
theorem passes_cse (L : Lam) (c : Comp) (P : Pt2) (T : Array (Array FE2)) (F : Array FE2) (ps : Array ℕ)
    (h : cseOkP c F.size ps = true) (a : FE2) :
    passesF2 L c P T (F ++ ps.map (pairV F)) a = passesF2 L c P T F a := by
  unfold passesF2
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  unfold cseOkP at h
  rw [Array.all_eq_true'] at h
  refine foldlM_congr_mem _ _ _ (fun p hp acc ↦ opt_bind_congr _ _ _ fun pf hpf ↦ ?_) a
  have := h p (by simpa using hp)
  rw [hpf] at this
  exact congrArg (fun x ↦ pure (a2 acc x)) (runPassF2_cse L P T F ps p pf this)

/-- `evalC2X` with a checked rewrite is `evalC2X` without. -/
theorem evalC2X_some (L : Lam) (c : Comp) (P : Pt2) (T : Array (Array FE2)) (fc : FCode) (hfc : c.fcode = some fc)
    (k : CseC) (hw : k.fc.ws = fc.ws) (h1 : cseOkL k.n0 k.ps k.fc.ins.toList fc.ins.toList = true)
    (h2 : cseOkP c k.n0 k.ps = true) :
    evalC2X L c (some k) P T = evalC2X L c none P T := by
  simp only [evalC2X, hfc, Option.bind_eq_bind, Option.bind_some, beq_iff_eq]
  split
  · rename_i hs
    rw [← hs] at h1 h2
    rw [passes_cse L c P T _ _ h2, cse_runF2 L _ _ fc _ hw h1]
  · rfl

theorem evalC2X_cse (L : Lam) (c : Comp) (P : Pt2) (T : Array (Array FE2)) :
    evalC2X L c (cseOf c) P T = evalC2X L c none P T := by
  cases hfc : c.fcode with
  | none =>
    have : cseOf c = none := by unfold cseOf; rw [hfc]
    rw [this]
  | some fc =>
    have e : cseOf c = cseFor c fc ((tabOffs c.tabs).getD c.tabs.size 0) cseTh := by unfold cseOf; rw [hfc]
    rw [e]
    unfold cseFor
    dsimp only
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact evalC2X_some L c P T fc hfc _ rfl h.1 h.2
    · rfl

theorem evalC2_X (L : Lam) (c : Comp) (pt : List FE2) :
    evalC2 L c pt = evalC2X L c none (Pt2.ofList pt) (tabsAt2 L (Pt2.ofList pt) c.tabs) := rfl

/-! ## Shared tables -/

theorem tabsAt2_split (L : Lam) (P : Pt2) (rs : Array TRec) :
    tabsAt2 L P rs = tabsFin2 rs (rs.map (tab02 L P (lv2Of P))) := rfl

theorem recEqS_eq (a b : TRec) (h : recEqS a b = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h Bool.false_ne_true
    | (simp only [recEqS, beq_iff_eq] at h; rw [h])

theorem tab0Sh_eq (L : Lam) (P : Pt2) (V : Lv2) (rs0 : Array TRec) (src : Array ℕ) (rs1 : Array TRec) :
    tab0Sh L P V rs0 (rs0.map (tab02 L P V)) src rs1 = rs1.map (tab02 L P V) := by
  unfold tab0Sh
  refine Array.mapIdx_eq_iff.2 fun i ↦ ?_
  rw [Array.getElem?_map]
  cases rs1[i]? with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.some.injEq]
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := h
      generalize src.getD i rs0.size = j at h1 h2 ⊢
      have hr := recEqS_eq _ _ h2
      subst hr
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h1, Option.map_some,
        Option.getD_some]
    · rfl

/-! ## The twin -/

/-- **The fast twin is `PhiQGCK`.** -/
theorem PhiQGCKT_eq (c : PhiCacheX) (pt : List FE2) : PhiQGCKT c (phiPre c) pt = PhiQGCK c pt := by
  unfold PhiQGCKT PhiQGCK phiPre
  dsimp only
  rw [tab0Sh_eq, evalC2X_cse, evalC2X_cse, ← tabsAt2_split, ← tabsAt2_split, ← evalC2_X, ← evalC2_X]

end Lvm.Typed.KT
