-- New for lvm2 S2GT (GT-W, STMT 6 `PhiQGC_eq`): the fast evaluator at `E2` under the leaf map is the leaf map of
-- the generic evaluator over `E3 ⊗ E2` (a simulation under `linOk`).
import LvmE2VRingA
import LvmWiringKC

/-!
# The fast `Φ_Q` at `E2` simulates the evaluator over `E3 ⊗ E2`

* **Twins**: GT-V's `E2` kernels without the leaf map (`eqTabB2`, `eqLevels2`, `margTab2`, `subTab2`, `succVal2`,
  `kapTab2`, `autoStepP2`, `runAuto2`, `finVal2`, `finSum2`, `flatTabs2`, `prodKeys2`) are `LvmWiringK`'s generic
  twins at `𝔽 = FE2` (`m2_eq`).
* **Naturality**: the value-only kernels commute with a ring map (`emb : FE2 →+* FEA`).
* **The simulation** (`evalC2_sim`): on a linear compiled evaluator (`linOk`), `evalC2 L c pt = lam L (evalCG c
  (pt.map emb))`. Every value of the `E2` run is the leaf map of the `FEA` run's, and equal to it (under `emb`)
  where `linCode`'s flag says it carries no `E3` content.
-/

set_option autoImplicit false

namespace Lvm.Typed.KT

open Lvm Lvm.Typed.K

/-! ## Twins -/

theorem m2_fun : m2 = fun a b : FE2 ↦ a * b := funext fun a ↦ funext fun b ↦ m2_eq a b

theorem a2_fun : a2 = fun a b : FE2 ↦ a + b := rfl

theorem kt_sub2 (a b : FE2) : a - b = a + b := rfl

theorem eqTabB2_eqG (r : Array FE2) (bits : List ℕ) : eqTabB2 r bits = eqTabBG r bits := by
  unfold eqTabB2 eqTabBG; simp only [m2_fun, a2_fun, kt_sub2]

theorem eqLevels2_eqG (r : Array FE2) (lo n : ℕ) : eqLevels2 r lo n = eqLevelsG r lo n := by
  unfold eqLevels2 eqLevelsG; simp only [m2_fun, a2_fun, kt_sub2]

theorem margTab2_eqG (lv : Array (Array FE2)) (lo n : ℕ) (bits : List ℕ) :
    margTab2 lv lo n bits = margTabG lv lo n bits := by
  unfold margTab2 margTabG; simp only [a2_fun]; rfl

theorem subTab2_eqG (r : Array FE2) (lv : Array (Array FE2)) (lo n : ℕ) (bits : List ℕ) :
    subTab2 r lv lo n bits = subTabG r lv lo n bits := by
  unfold subTab2 subTabG; simp only [eqTabB2_eqG, margTab2_eqG]; rfl

theorem succVal2_eqG (xs ys : List FE2) : succVal2 xs ys = succValG xs ys := by
  simp only [succVal2, succValG, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, m2_fun, a2_fun, kt_sub2]
  refine congrArg Prod.snd (congrArg (fun F ↦ List.foldl F _ _) ?_)
  funext p i
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem flatTabs2_eqG (rs : Array TRec) (T : Array (Array FE2)) : flatTabs2 rs T = flatTabsG rs T := by
  unfold flatTabs2 flatTabsG; rfl

theorem keyVal2_eqG (T : Array (Array FE2)) (k : ℕ × ℕ) : keyVal2 T k = keyValG T k := rfl

theorem prodKeys2_eqG (T : Array (Array FE2)) (ks : List (ℕ × ℕ)) : prodKeys2 T ks = prodKeysG T ks := by
  cases ks <;> simp only [prodKeys2, prodKeysG, m2_fun, keyVal2_eqG]

theorem autoStepP2_eqG (R : ℕ) (rxk ryk : FE2) (cs : Array ℕ) (vs : Array FE2) :
    autoStepP2 R rxk ryk cs vs = autoStepPG R rxk ryk cs vs := by
  unfold autoStepP2 autoStepPG; simp only [m2_fun, a2_fun, kt_sub2]

theorem runAuto2_eqG (P : Pt2) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × FE2)) :
    runAuto2 P xs R st = runAutoG (⟨P.kap, P.rx, P.ry⟩ : PtG FE2) xs R st := by
  unfold runAuto2 runAutoG; simp only [autoStepP2_eqG]

theorem finVal2_eqG (T : Array (Array FE2)) (p : Pass) (c : ℕ) : finVal2 T p c = finValG T p c := by
  unfold finVal2 finValG; simp only [m2_fun]

theorem finSum2_eqG (T : Array (Array FE2)) (p : Pass) (fs : Array (ℕ × FE2)) : finSum2 T p fs = finSumG T p fs := by
  unfold finSum2 finSumG; simp only [m2_fun, a2_fun, finVal2_eqG]

theorem kap_eqTab {R : Type} [CommRing R] [CharP R 2] (κ : Array R) : eqTabBG κ [0, 1] = eqTabG κ 0 2 := by
  rw [tab_eqTabB_eq, tab_eqTab_eq]
  rfl

theorem kapTab2_eqG (κ : Array FE2) : kapTab2 κ = kapTabG κ := by
  unfold kapTab2 kapTabG
  rw [eqTabB2_eqG, kap_eqTab]
  simp only [a2_fun]

/-! ## Naturality of the value-only kernels -/

section Nat

variable {R S : Type} [CommRing R] [CharP R 2] [CommRing S] [CharP S 2] (f : R →+* S)

theorem nat_getD (r : Array R) (i : ℕ) : (r.map f).getD i 0 = f (r.getD i 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases r[i]? <;> simp only [Option.map_none, Option.getD_none, map_zero, Option.map_some, Option.getD_some]

theorem nat_dbl (t : Array R) (a : R) : (tab_dbl t a).map f = tab_dbl (t.map f) (f a) := by
  unfold tab_dbl
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map, List.foldl_map]
  suffices h : ∀ (l : List R) (b : Array R), (l.foldl (fun b v ↦ (b.push (v - v * a)).push (v * a)) b).map f =
      l.foldl (fun b v ↦ (b.push (f v - f v * f a)).push (f v * f a)) (b.map f) by
    rw [h]
    congr 1
    simp only [Array.mkEmpty, List.map_toArray, List.map_nil]
  intro l
  induction l with
  | nil => intro b; rfl
  | cons v l ih => intro b; simp only [List.foldl_cons, ih, Array.map_push, map_sub, map_mul]

theorem nat_dbls (g : ℕ → R) (l : List ℕ) (t : Array R) :
    (l.foldl (fun t i ↦ tab_dbl t (g i)) t).map f = l.foldl (fun t i ↦ tab_dbl t (f (g i))) (t.map f) := by
  induction l generalizing t with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih, nat_dbl]

theorem nat_eqTabB (r : Array R) (bits : List ℕ) : (eqTabBG r bits).map f = eqTabBG (r.map f) bits := by
  have h1 : (#[1] : Array R).map f = #[1] := by simp only [List.map_toArray, List.map_cons, map_one, List.map_nil]
  rw [tab_eqTabB_eq, tab_eqTabB_eq, nat_dbls, h1]
  simp only [nat_getD]

theorem nat_eqTab (r : Array R) (lo n : ℕ) : (eqTabG r lo n).map f = eqTabG (r.map f) lo n := by
  have h1 : (#[1] : Array R).map f = #[1] := by simp only [List.map_toArray, List.map_cons, map_one, List.map_nil]
  rw [tab_eqTab_eq, tab_eqTab_eq, nat_dbls, h1]
  simp only [nat_getD]

theorem nat_succVal (xs ys : List R) : succValG (xs.map f) (ys.map f) = f (succValG xs ys) := by
  simp only [succValG, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, List.length_map, ← List.map_toArray]
  have e : ((1 : S), (0 : S)) = Prod.map f f ((1 : R), (0 : R)) := by simp only [Prod.map_apply, map_one, map_zero]
  rw [e, List.foldl_hom (Prod.map f f)]
  · rfl
  · intro st i
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.map_fst, Prod.map_snd, nat_getD, map_mul, map_add, map_sub, map_one]

theorem nat_eqLevels (r : Array R) (lo n : ℕ) :
    (eqLevelsG r lo n).map (·.map f) = eqLevelsG (r.map f) lo n := by
  rw [tab_eqLevels_eq, tab_eqLevels_eq]
  suffices h : ∀ (l : List ℕ) (s : Array R × Array (Array R)),
      ((l.foldl (fun s i ↦ (tab_dbl s.1 (r.getD (lo + n - 1 - i) 0), s.2.push (tab_dbl s.1 (r.getD (lo + n - 1 - i) 0))))
          s).1.map f,
        (l.foldl (fun s i ↦ (tab_dbl s.1 (r.getD (lo + n - 1 - i) 0), s.2.push (tab_dbl s.1 (r.getD (lo + n - 1 - i) 0))))
          s).2.map (·.map f)) =
      l.foldl (fun s i ↦ (tab_dbl s.1 ((r.map f).getD (lo + n - 1 - i) 0),
        s.2.push (tab_dbl s.1 ((r.map f).getD (lo + n - 1 - i) 0)))) (s.1.map f, s.2.map (·.map f)) by
    have := congrArg Prod.snd (h (List.range' 0 n) (#[1], #[#[1]]))
    simp only at this
    have e1 : (#[1] : Array R).map f = #[1] := by simp only [List.map_toArray, List.map_cons, map_one, List.map_nil]
    have e2 : (#[#[1]] : Array (Array R)).map (·.map f) = #[#[1]] := by simp only [List.map_toArray, List.map_cons, map_one, List.map_nil]
    rw [e1, e2] at this
    rw [Array.map_reverse, this]
  intro l
  induction l with
  | nil => intro s; rfl
  | cons i l ih =>
    intro s
    simp only [List.foldl_cons]
    rw [ih]
    simp only [nat_dbl, nat_getD, Array.map_push]

theorem nat_margTab (lv : Array (Array R)) (lo n : ℕ) (bits : List ℕ) :
    (margTabG lv lo n bits).map f = margTabG (lv.map (·.map f)) lo n bits := by
  unfold margTabG
  cases bits.head? with
  | none => simp only [Id.run_pure, List.map_toArray, List.map_cons, map_one, List.map_nil]
  | some b0 =>
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind]
    have ht : (lv.map (·.map f)).getD (b0 - lo) #[] = (lv.getD (b0 - lo) #[]).map f := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]; cases lv[b0 - lo]? <;> simp only [Option.map_none, Option.getD_none, List.map_toArray, List.map_nil, Option.map_some, Option.getD_some]
    rw [ht]
    have e0 : ((Array.mkEmpty (2 ^ bits.length) : Array S), (0 : ℕ)) =
        Prod.map (Array.map f) id ((Array.mkEmpty (2 ^ bits.length) : Array R), (0 : ℕ)) := by
      simp only [Array.mkEmpty, Prod.map_apply, List.map_toArray, List.map_nil, id_eq]
    rw [e0, List.foldl_hom (Prod.map (Array.map f) id)]
    · rfl
    · intro st i
      have e1 : ((0 : S), (0 : ℕ)) = Prod.map f id ((0 : R), (0 : ℕ)) := by simp only [Prod.map_apply, map_zero, id_eq]
      refine Prod.ext ?_ rfl
      simp only [Prod.map_fst, Array.map_push]
      rw [e1, List.foldl_hom (Prod.map f id)]
      · rfl
      · intro st' j
        refine Prod.ext ?_ rfl
        simp only [Prod.map_fst, Prod.map_snd, id, nat_getD, map_add]

theorem nat_subTab (r : Array R) (lv : Array (Array R)) (lo n : ℕ) (bits : List ℕ) :
    (subTabG r lv lo n bits).map f = subTabG (r.map f) (lv.map (·.map f)) lo n bits := by
  unfold subTabG
  cases bits with
  | nil => simp only [List.head?_nil, List.map_toArray, List.map_cons, map_one, List.map_nil]
  | cons b0 bs =>
    simp only [List.head?_cons]
    split_ifs
    · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases lv[b0 - lo]? <;> simp only [Option.getD_none, List.map_toArray, List.map_nil, Option.map_none, Option.getD_some, Option.map_some]
    · exact nat_eqTabB f r _
    · exact nat_margTab f lv lo n _

theorem nat_kapfold (m : ℕ) (e : Array R) (l : List ℕ) (a : R) :
    f (l.foldl (fun acc o ↦ if m.testBit o then acc + e.getD o 0 else acc) a) =
      l.foldl (fun acc o ↦ if m.testBit o then acc + (e.map f).getD o 0 else acc) (f a) := by
  induction l generalizing a with
  | nil => rfl
  | cons o l ih =>
    have hs : f (if m.testBit o = true then a + e.getD o 0 else a) =
        (if m.testBit o = true then f a + (e.map f).getD o 0 else f a) := by
      split_ifs
      · rw [map_add, nat_getD]
      · rfl
    simp only [List.foldl_cons]
    rw [ih, hs]

theorem nat_kapTab (κ : Array R) : (kapTabG κ).map f = kapTabG (κ.map f) := by
  unfold kapTabG
  rw [← nat_eqTab, Array.map_map]
  apply Array.map_congr_left
  intro m _
  simp only [Function.comp_apply]
  rw [nat_kapfold, map_zero]

end Nat

/-! ## The value relation -/

/-- `x ∈ FEA` simulates `y ∈ E2` under flag `f`: `lam x = y`, and `x = emb y` when the flag is clear. -/
def SimV (L : Lam) (f : Bool) (x : FEA) (y : FE2) : Prop := lam L x = y ∧ (f = false → x = emb y)

theorem SimV.zero (L : Lam) (f : Bool) : SimV L f 0 0 := ⟨lam_zero L, fun _ ↦ (map_zero emb).symm⟩

theorem SimV.of_emb (L : Lam) (f : Bool) (y : FE2) : SimV L f (emb y) y := ⟨lam_emb L y, fun _ ↦ rfl⟩

theorem SimV.mono {L : Lam} {x : FEA} {y : FE2} (f : Bool) (h : SimV L false x y) : SimV L f x y :=
  ⟨h.1, fun _ ↦ h.2 rfl⟩

theorem SimV.flag {L : Lam} {f g : Bool} {x : FEA} {y : FE2} (h : SimV L f x y) (hfg : f = true → g = true) :
    SimV L g x y := ⟨h.1, fun hg ↦ h.2 (by cases f <;> simp_all only [Bool.false_eq_true, implies_true, Bool.true_eq_false])⟩

theorem SimV.add {L : Lam} {f g : Bool} {x x' : FEA} {y y' : FE2} (h : SimV L f x y) (h' : SimV L g x' y') :
    SimV L (f || g) (x + x') (y + y') := by
  refine ⟨by rw [lam_add, h.1, h'.1], fun hf ↦ ?_⟩
  simp only [Bool.or_eq_false_iff] at hf
  rw [h.2 hf.1, h'.2 hf.2, map_add]

theorem SimV.mul {L : Lam} {f g : Bool} {x x' : FEA} {y y' : FE2} (h : SimV L f x y) (h' : SimV L g x' y')
    (hfg : (f && g) = false) : SimV L (f || g) (x * x') (y * y') := by
  cases f with
  | false =>
    rw [h.2 rfl]
    refine ⟨by rw [lam_emb_mul, h'.1], fun hf ↦ ?_⟩
    simp only [Bool.false_or] at hf
    rw [h'.2 hf, map_mul]
  | true =>
    cases g with
    | false =>
      rw [h'.2 rfl, mul_comm, mul_comm y]
      exact ⟨by rw [lam_emb_mul, h.1], fun hf ↦ by simp only [Bool.or_false, Bool.true_eq_false] at hf⟩
    | true => simp only [Bool.and_self, Bool.true_eq_false] at hfg


theorem SimV.add' {L : Lam} {f : Bool} {x x' : FEA} {y y' : FE2} (h : SimV L f x y) (h' : SimV L f x' y') :
    SimV L f (x + x') (y + y') := (h.add h').flag (by simp only [Bool.or_self, imp_self])

theorem SimV.emb_mul {L : Lam} {f : Bool} {x : FEA} {y : FE2} (a : FE2) (h : SimV L f x y) :
    SimV L f (emb a * x) (a * y) := ((SimV.of_emb L false a).mul h (by simp only [Bool.false_and])).flag (by simp only [Bool.false_or, imp_self])

theorem SimV.mul_emb {L : Lam} {f : Bool} {x : FEA} {y : FE2} (a : FE2) (h : SimV L f x y) :
    SimV L f (x * emb a) (y * a) := (h.mul (SimV.of_emb L false a) (by simp only [Bool.and_false])).flag (by simp only [Bool.or_false, imp_self])

theorem SimV.ite {L : Lam} {f : Bool} {x x' : FEA} {y y' : FE2} (c : Prop) [Decidable c] (h : SimV L f x y)
    (h' : SimV L f x' y') : SimV L f (if c then x else x') (if c then y else y') := by
  split
  · exact h
  · exact h'

theorem SimV.mul_iteE {L : Lam} {f : Bool} {x : FEA} {y : FE2} (h : SimV L f x y) (c : Prop) [Decidable c]
    (p q : FE2) : SimV L f (x * (if c then emb p else emb q)) (y * (if c then p else q)) := by
  split
  · exact h.mul_emb p
  · exact h.mul_emb q

theorem SimV.sub' {L : Lam} {f : Bool} {x x' : FEA} {y y' : FE2} (h : SimV L f x y) (h' : SimV L f x' y') :
    SimV L f (x - x') (y - y') := by
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]; exact h.add' h'

/-! ## Weights under the leaf map -/

/-- `mK v c = v·c` (`c ∈ K`). -/
theorem mK_eq (v : FE2) (c : FK) : mK v c = v * FE2.ofK c := by
  rw [FE2.mul_def]
  show (⟨v.re * c, v.im * c⟩ : FE2) = ⟨v.re * c + v.im * 0, v.re * 0 + v.im * c + FK.x * (v.im * 0)⟩
  congr 1 <;> ring

/-- `lamW L w = λ(w)`. -/
theorem lamW_eq (L : Lam) (w : FE) : lamW L w = lamE L w := by
  simp only [lamW, lamE, a2_fun, mK_eq, FE2.ofK]
  ring

/-- `ofE (c·y^m)` for `m < 3` as an `E2` scalar under `lam`. -/
theorem lam_ofE_mul_emb (L : Lam) (c : FE) (y : FE2) : lam L (KRing.ofE c * emb y) = y * lamE L c := by
  rw [mul_comm, lam_emb_mul, lam_ofE]

theorem ofE_ofK (c : FK) : (KRing.ofE (FE.ofK c) : FEA) = emb (FE2.ofK c) := by
  ext
  · rfl
  · show (0 : FE) = FE.ofK 0; rfl

/-- **A weighted value under the leaf map** (`linCode`: a weight with `E3` content meets only `E2` values). -/
theorem SimV.wmul {L : Lam} {f : Bool} {x : FEA} {y : FE2} (h : SimV L f x y) (m : ℕ) (w : FE)
    (hfm : (f && (m != 0)) = false) : SimV L (f || (m != 0)) (wmulG m x w) (wmul2 L m y w) := by
  unfold wmulG wmul2
  by_cases h0 : m = 0
  · subst h0
    simp only [beq_self_eq_true, ite_true, bne_self_eq_false, Bool.or_false]
    rw [ofE_ofK, mK_eq, mul_comm y]
    exact (SimV.of_emb L false (FE2.ofK w.c₀)).mul h (by simp only [Bool.false_and])
  · have hf : f = false := by simpa only [Bool.and_eq_false_imp, bne_eq_false_iff_eq, h0, imp_false, Bool.not_eq_true] using hfm
    subst hf
    rw [h.2 rfl]
    have hm : (m != 0) = true := by simpa only [bne_iff_ne, ne_eq] using h0
    rw [hm]
    refine ⟨?_, fun h' ↦ by simp only [Bool.or_true, Bool.true_eq_false] at h'⟩
    simp only [show (m == 0) = false by simpa only [beq_eq_false_iff_ne, ne_eq] using h0, Bool.false_eq_true, ite_false, m2_fun, mK_eq]
    split_ifs with h1 h2
    · rw [← mul_assoc, ← map_mul, mul_comm FE.y, ← fuse_fe_y1, lam_ofE_mul_emb]
      simp only [lamE, show FE2.ofK 0 = 0 from rfl]; ring
    · rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (FE.y * FE.y), ← fuse_fe_y2, lam_ofE_mul_emb]
      simp only [lamE, show FE2.ofK 0 = 0 from rfl]; ring
    · rw [lam_emb_mul, lam_ofE, lamW_eq]

/-! ## The fused code: one step at a time -/

/-- One instruction of `runF2` (flat tables `F`, weights `W`). -/
def fstep2 (L : Lam) (F : Array FE2) (W : Array FE) (s : FE2 × Array FE2 × Array (ℕ × FE2)) (n : ℕ) :
    FE2 × Array FE2 × Array (ℕ × FE2) :=
  let a := F.getD ((n >>> 6) &&& 0xFFFFF) 0
  if n &&& 15 == 7 then (a2 s.1 (m2 a (F.getD ((n >>> 26) &&& 0xFFFFF) 0)), s.2.1, s.2.2)
  else if n &&& 15 == 5 then (a2 s.1 a, s.2.1, s.2.2)
  else if n &&& 15 == 6 then (a2 s.1 (wmul2 L ((n >>> 4) &&& 3) a (W.getD (n >>> 46) 1)), s.2.1, s.2.2)
  else if n &&& 15 == 3 then (a2 (s.2.1.getD (s.2.1.size - 1) 0) (m2 a s.1), s.2.1.pop, s.2.2)
  else if n &&& 15 == 1 then (a, s.2.1.push s.1, s.2.2)
  else if n &&& 15 == 0 then (0, s.2.1.push s.1, s.2.2)
  else if n &&& 15 == 8 then
    (a2 s.1 (m2 a (wmul2 L ((n >>> 4) &&& 3) (F.getD ((n >>> 26) &&& 0xFFFFF) 0) (W.getD (n >>> 46) 1))),
      s.2.1, s.2.2)
  else if n &&& 15 == 4 then (s.2.1.getD (s.2.1.size - 1) 0, s.2.1.pop, s.2.2.push (n >>> 26, s.1))
  else if n &&& 15 == 2 then (wmul2 L ((n >>> 4) &&& 3) a (W.getD (n >>> 46) 1), s.2.1.push s.1, s.2.2)
  else (a2 (s.2.1.getD (s.2.1.size - 1) 0) s.1, s.2.1.pop, s.2.2)

/-- One step of `runF2Go` is `fstep2` on the state `(top, st, em)`. -/
theorem runF2Go_succ (L : Lam) (F : Array FE2) (ins : Array ℕ) (W : Array FE) (fuel k : ℕ) (tr ti : UInt64)
    (st : Array FE2) (em : Array (ℕ × FE2)) (s : FE2 × Array FE2 × Array (ℕ × FE2))
    (hs : fstep2 L F W (⟨⟨tr⟩, ⟨ti⟩⟩, st, em) (ins.getD k 0) = s) :
    runF2Go L F ins W (fuel + 1) k tr ti st em = runF2Go L F ins W fuel (k + 1) s.1.re.val s.1.im.val s.2.1 s.2.2 := by
  rw [runF2Go]
  generalize ins.getD k 0 = n at hs ⊢
  dsimp only [fstep2] at hs
  dsimp only
  by_cases h7 : (n &&& 15 == 7) = true
  · rw [if_pos h7] at hs ⊢; subst hs; rfl
  rw [if_neg h7] at hs ⊢
  by_cases h5 : (n &&& 15 == 5) = true
  · rw [if_pos h5] at hs ⊢; subst hs; rfl
  rw [if_neg h5] at hs ⊢
  by_cases h6 : (n &&& 15 == 6) = true
  · rw [if_pos h6] at hs ⊢; subst hs; rfl
  rw [if_neg h6] at hs ⊢
  by_cases h3 : (n &&& 15 == 3) = true
  · rw [if_pos h3] at hs ⊢; subst hs; rfl
  rw [if_neg h3] at hs ⊢
  by_cases h1 : (n &&& 15 == 1) = true
  · rw [if_pos h1] at hs ⊢; subst hs; rfl
  rw [if_neg h1] at hs ⊢
  by_cases h0 : (n &&& 15 == 0) = true
  · rw [if_pos h0] at hs ⊢; subst hs; rfl
  rw [if_neg h0] at hs ⊢
  by_cases h8 : (n &&& 15 == 8) = true
  · rw [if_pos h8] at hs ⊢; subst hs; rfl
  rw [if_neg h8] at hs ⊢
  by_cases h4 : (n &&& 15 == 4) = true
  · rw [if_pos h4] at hs ⊢; subst hs; rfl
  rw [if_neg h4] at hs ⊢
  by_cases h2 : (n &&& 15 == 2) = true
  · rw [if_pos h2] at hs ⊢; subst hs; rfl
  rw [if_neg h2] at hs ⊢
  subst hs; rfl

/-- `runF2Go` from instruction `k` is the fold of `fstep2` over the remaining instructions. -/
theorem runF2Go_eq (L : Lam) (F : Array FE2) (ins : Array ℕ) (W : Array FE) :
    ∀ fuel k tr ti st em, ins.size = k + fuel →
      runF2Go L F ins W fuel k tr ti st em =
        (((ins.toList.drop k).foldl (fstep2 L F W) (⟨⟨tr⟩, ⟨ti⟩⟩, st, em)).1,
          ((ins.toList.drop k).foldl (fstep2 L F W) (⟨⟨tr⟩, ⟨ti⟩⟩, st, em)).2.2)
  | 0, k, tr, ti, st, em, h => by
    rw [List.drop_eq_nil_of_le (by simp only [Array.length_toList]; omega), runF2Go]
    rfl
  | fuel + 1, k, tr, ti, st, em, h => by
    have hk : k < ins.toList.length := by simp only [Array.length_toList]; omega
    have hg : ins.getD k 0 = ins.toList[k] := by
      rw [Array.getD, dif_pos (by omega)]
      rfl
    rw [runF2Go_succ L F ins W fuel k tr ti st em _ rfl, List.drop_eq_getElem_cons hk, List.foldl_cons, hg]
    exact runF2Go_eq L F ins W fuel (k + 1) _ _ _ _ (by omega)

theorem runF2_fold (L : Lam) (F : Array FE2) (c : FCode) :
    runF2 L F c = ((c.ins.toList.foldl (fstep2 L F c.ws) (0, #[], #[])).1,
      (c.ins.toList.foldl (fstep2 L F c.ws) (0, #[], #[])).2.2) := by
  unfold runF2
  rw [runF2Go_eq L F c.ins c.ws c.ins.size 0 0 0 _ _ (by omega), List.drop_zero]
  rfl

/-- One instruction of `linCode` (`lim` the flat indices with `E3` content): the result's flag, the stack's flags,
whether every product so far met at most one `E3`-carrying factor, whether an emitted state carried `E3`. -/
def lstep (lim : ℕ → Bool) (s : Bool × Array Bool × Bool × Bool) (n : ℕ) : Bool × Array Bool × Bool × Bool :=
  if n &&& 15 == 7 then
    if lim ((n >>> 6) &&& 0xFFFFF) && lim ((n >>> 26) &&& 0xFFFFF) then
      (s.1 || lim ((n >>> 6) &&& 0xFFFFF) || lim ((n >>> 26) &&& 0xFFFFF), s.2.1, false, s.2.2.2)
    else (s.1 || lim ((n >>> 6) &&& 0xFFFFF) || lim ((n >>> 26) &&& 0xFFFFF), s.2.1, s.2.2.1, s.2.2.2)
  else if n &&& 15 == 5 then (s.1 || lim ((n >>> 6) &&& 0xFFFFF), s.2.1, s.2.2.1, s.2.2.2)
  else if n &&& 15 == 6 then
    if lim ((n >>> 6) &&& 0xFFFFF) && (n >>> 4) &&& 3 != 0 then
      (s.1 || lim ((n >>> 6) &&& 0xFFFFF) || (n >>> 4) &&& 3 != 0, s.2.1, false, s.2.2.2)
    else (s.1 || lim ((n >>> 6) &&& 0xFFFFF) || (n >>> 4) &&& 3 != 0, s.2.1, s.2.2.1, s.2.2.2)
  else if n &&& 15 == 3 then
    if lim ((n >>> 6) &&& 0xFFFFF) && s.1 then
      (s.2.1.getD (s.2.1.size - 1) false || lim ((n >>> 6) &&& 0xFFFFF) || s.1, s.2.1.pop, false, s.2.2.2)
    else (s.2.1.getD (s.2.1.size - 1) false || lim ((n >>> 6) &&& 0xFFFFF) || s.1, s.2.1.pop, s.2.2.1, s.2.2.2)
  else if n &&& 15 == 1 then (lim ((n >>> 6) &&& 0xFFFFF), s.2.1.push s.1, s.2.2.1, s.2.2.2)
  else if n &&& 15 == 0 then (false, s.2.1.push s.1, s.2.2.1, s.2.2.2)
  else if n &&& 15 == 8 then
    if (lim ((n >>> 6) &&& 0xFFFFF) && lim ((n >>> 26) &&& 0xFFFFF)) ||
        (lim ((n >>> 6) &&& 0xFFFFF) && (n >>> 4) &&& 3 != 0) || (lim ((n >>> 26) &&& 0xFFFFF) && (n >>> 4) &&& 3 != 0)
    then (s.1 || lim ((n >>> 6) &&& 0xFFFFF) || lim ((n >>> 26) &&& 0xFFFFF) || (n >>> 4) &&& 3 != 0, s.2.1, false,
      s.2.2.2)
    else (s.1 || lim ((n >>> 6) &&& 0xFFFFF) || lim ((n >>> 26) &&& 0xFFFFF) || (n >>> 4) &&& 3 != 0, s.2.1,
      s.2.2.1, s.2.2.2)
  else if n &&& 15 == 4 then (s.2.1.getD (s.2.1.size - 1) false, s.2.1.pop, s.2.2.1, s.2.2.2 || s.1)
  else if n &&& 15 == 2 then
    if lim ((n >>> 6) &&& 0xFFFFF) && (n >>> 4) &&& 3 != 0 then
      (lim ((n >>> 6) &&& 0xFFFFF) || (n >>> 4) &&& 3 != 0, s.2.1.push s.1, false, s.2.2.2)
    else (lim ((n >>> 6) &&& 0xFFFFF) || (n >>> 4) &&& 3 != 0, s.2.1.push s.1, s.2.2.1, s.2.2.2)
  else (s.2.1.getD (s.2.1.size - 1) false || s.1, s.2.1.pop, s.2.2.1, s.2.2.2)

theorem linCode_fold (lim : ℕ → Bool) (c : FCode) :
    linCode lim c = ((c.ins.toList.foldl (lstep lim) (false, #[], true, false)).2.2.1,
      !((c.ins.toList.foldl (lstep lim) (false, #[], true, false)).1 ||
        (c.ins.toList.foldl (lstep lim) (false, #[], true, false)).2.2.2)) := by
  unfold linCode
  simp only [Id.run]
  rw [← Array.forIn_toList, code_forIn_list _ _ _ (fun s n ↦ lstep lim s n)
    (by intro n s; simp only [lstep, fuse_ite_pure])]
  rfl

/-! ## The simulation of the fused code -/

/-- Stacks: the same size, entrywise simulated under their flags. -/
def SimS (L : Lam) (fs : Array Bool) (xs : Array FEA) (ys : Array FE2) : Prop :=
  xs.size = ys.size ∧ fs.size = xs.size ∧ ∀ i, SimV L (fs.getD i false) (xs.getD i 0) (ys.getD i 0)

/-- Emitted states: the same keys, values simulated under one flag. -/
def SimE (L : Lam) (f : Bool) (xs : Array (ℕ × FEA)) (ys : Array (ℕ × FE2)) : Prop :=
  xs.size = ys.size ∧ ∀ i, (xs.getD i (0, 0)).1 = (ys.getD i (0, 0)).1 ∧
    SimV L f (xs.getD i (0, 0)).2 (ys.getD i (0, 0)).2

/-- Flat tables: entrywise simulated, the flag `lim` (`E3` content). -/
def SimF (L : Lam) (lim : ℕ → Bool) (FA : Array FEA) (F2 : Array FE2) : Prop :=
  ∀ i, SimV L (lim i) (FA.getD i 0) (F2.getD i 0)

theorem SimS.empty (L : Lam) : SimS L #[] #[] #[] := ⟨rfl, rfl, fun i ↦ by simpa only [Array.getD_eq_getD_getElem?, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none] using SimV.zero L false⟩

theorem SimE.empty (L : Lam) (f : Bool) : SimE L f #[] #[] := ⟨rfl, fun i ↦ by simpa only [Array.getD_eq_getD_getElem?, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, true_and] using SimV.zero L f⟩

theorem SimS.push {L : Lam} {fs : Array Bool} {xs : Array FEA} {ys : Array FE2} (h : SimS L fs xs ys)
    {f : Bool} {x : FEA} {y : FE2} (hv : SimV L f x y) : SimS L (fs.push f) (xs.push x) (ys.push y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp only [Array.size_push, h1, Nat.add_left_cancel_iff], by simp only [Array.size_push, h2, Nat.add_left_cancel_iff], fun i ↦ ?_⟩
  have := h3 i
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at this ⊢
  rw [h2, h1]
  split_ifs with hi
  · simpa only [Option.getD_some] using hv
  · exact this

theorem SimS.pop {L : Lam} {fs : Array Bool} {xs : Array FEA} {ys : Array FE2} (h : SimS L fs xs ys) :
    SimS L fs.pop xs.pop ys.pop := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp only [Array.size_pop, h1], by simp only [Array.size_pop, h2], fun i ↦ ?_⟩
  have := h3 i
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_pop] at this ⊢
  rw [h2, h1]
  split_ifs with hi
  · exact this
  · simpa only [Option.getD_none] using SimV.zero L false

theorem SimS.top {L : Lam} {fs : Array Bool} {xs : Array FEA} {ys : Array FE2} (h : SimS L fs xs ys) :
    SimV L (fs.getD (fs.size - 1) false) (xs.getD (xs.size - 1) 0) (ys.getD (ys.size - 1) 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [h2, h1]; exact h3 _

theorem SimE.push {L : Lam} {f : Bool} {xs : Array (ℕ × FEA)} {ys : Array (ℕ × FE2)} (h : SimE L f xs ys)
    (k : ℕ) {g : Bool} {x : FEA} {y : FE2} (hv : SimV L g x y) :
    SimE L (f || g) (xs.push (k, x)) (ys.push (k, y)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp only [Array.size_push, h1, Nat.add_left_cancel_iff], fun i ↦ ?_⟩
  have := h2 i
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at this ⊢
  rw [h1]
  split_ifs with hi
  · exact ⟨rfl, hv.flag (by simp_all only [Array.getD_eq_getD_getElem?, lt_self_iff_false, not_false_eq_true, getElem?_neg, Option.getD_none, true_and, Bool.or_true, implies_true])⟩
  · exact ⟨this.1, this.2.flag (by simp_all only [Array.getD_eq_getD_getElem?, and_self, Bool.true_or, implies_true])⟩

theorem SimE.mono {L : Lam} {xs : Array (ℕ × FEA)} {ys : Array (ℕ × FE2)} (h : SimE L false xs ys) (f : Bool) :
    SimE L f xs ys := ⟨h.1, fun i ↦ ⟨(h.2 i).1, (h.2 i).2.mono f⟩⟩

/-- The invariant of the three runs (fused code over `FEA`, over `E2`, `linCode`'s flags). -/
def SimR (L : Lam) (sa : FEA × Array FEA × Array (ℕ × FEA)) (s2 : FE2 × Array FE2 × Array (ℕ × FE2))
    (sf : Bool × Array Bool × Bool × Bool) : Prop :=
  sf.2.2.1 = true → SimV L sf.1 sa.1 s2.1 ∧ SimS L sf.2.1 sa.2.1 s2.2.1 ∧ SimE L sf.2.2.2 sa.2.2 s2.2.2

theorem ok_ite {α : Type} {c : Prop} [Decidable c] {a b : α} {P : α → Prop} (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

theorem lstep_ok (lim : ℕ → Bool) (s : Bool × Array Bool × Bool × Bool) (n : ℕ)
    (h : (lstep lim s n).2.2.1 = true) : s.2.2.1 = true := by
  revert h
  show (fun x : Bool × Array Bool × Bool × Bool ↦ x.2.2.1 = true → s.2.2.1 = true) (lstep lim s n)
  unfold lstep
  repeat' (first | exact id | exact fun h ↦ absurd h Bool.false_ne_true |
    refine ok_ite (P := fun x : Bool × Array Bool × Bool × Bool ↦ x.2.2.1 = true → s.2.2.1 = true) ?_ ?_)

theorem sim_step (L : Lam) (lim : ℕ → Bool) (FA : Array FEA) (F2 : Array FE2) (W : Array FE)
    (hF : SimF L lim FA F2) (sa : FEA × Array FEA × Array (ℕ × FEA)) (s2 : FE2 × Array FE2 × Array (ℕ × FE2))
    (sf : Bool × Array Bool × Bool × Bool) (h : SimR L sa s2 sf) (n : ℕ) :
    SimR L (fuse_fstep FA W sa n) (fstep2 L F2 W s2 n) (lstep lim sf n) := by
  obtain ⟨topA, stA, emA⟩ := sa
  obtain ⟨top2, st2, em2⟩ := s2
  obtain ⟨tf, sfl, ok, emc⟩ := sf
  intro hok'
  have hok : ok = true := lstep_ok lim (tf, sfl, ok, emc) n hok'
  obtain ⟨ht, hs, he⟩ := h hok
  have hFa := hF ((n >>> 6) &&& 0xFFFFF)
  have hFb := hF ((n >>> 26) &&& 0xFFFFF)
  revert hok'
  unfold fuse_fstep fstep2 lstep
  simp only [m2_fun, a2_fun]
  generalize lim ((n >>> 6) &&& 0xFFFFF) = la at hFa ⊢
  generalize lim ((n >>> 26) &&& 0xFFFFF) = lb at hFb ⊢
  generalize FA.getD ((n >>> 6) &&& 0xFFFFF) 0 = xa at hFa ⊢
  generalize FA.getD ((n >>> 26) &&& 0xFFFFF) 0 = xb at hFb ⊢
  generalize F2.getD ((n >>> 6) &&& 0xFFFFF) 0 = ya at hFa ⊢
  generalize F2.getD ((n >>> 26) &&& 0xFFFFF) 0 = yb at hFb ⊢
  generalize (n >>> 4) &&& 3 = m
  generalize W.getD (n >>> 46) 1 = w
  obtain ⟨op, hop⟩ : ∃ op, n &&& 15 = op := ⟨_, rfl⟩
  rw [hop]
  by_cases h7 : op = 7
  · subst h7
    simp only [show ((7 : ℕ) == 7) = true from rfl, ite_true]
    by_cases hc : (la && lb) = true
    · simp only [hc, ite_true]; intro h0; cases h0
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro _
      exact ⟨(ht.add (hFa.mul hFb (Bool.eq_false_iff.2 hc))).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), hs, he⟩
  by_cases h5 : op = 5
  · subst h5
    simp only [show ((5 : ℕ) == 7) = false from rfl, show ((5 : ℕ) == 5) = true from rfl, Bool.false_eq_true,
      ite_false, ite_true]
    intro _
    exact ⟨(ht.add hFa).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), hs, he⟩
  by_cases h6 : op = 6
  · subst h6
    simp only [show ((6 : ℕ) == 7) = false from rfl, show ((6 : ℕ) == 5) = false from rfl,
      show ((6 : ℕ) == 6) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
    by_cases hc : (la && m != 0) = true
    · simp only [hc, ite_true]; intro h0; cases h0
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro _
      exact ⟨(ht.add (hFa.wmul _ _ (Bool.eq_false_iff.2 hc))).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), hs, he⟩
  by_cases h3 : op = 3
  · subst h3
    simp only [show ((3 : ℕ) == 7) = false from rfl, show ((3 : ℕ) == 5) = false from rfl,
      show ((3 : ℕ) == 6) = false from rfl, show ((3 : ℕ) == 3) = true from rfl, Bool.false_eq_true, ite_false,
      ite_true]
    by_cases hc : (la && tf) = true
    · simp only [hc, ite_true]; intro h0; cases h0
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro _
      exact ⟨((SimS.top hs).add (hFa.mul ht (Bool.eq_false_iff.2 hc))).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), SimS.pop hs, he⟩
  by_cases h1 : op = 1
  · subst h1
    simp only [show ((1 : ℕ) == 7) = false from rfl, show ((1 : ℕ) == 5) = false from rfl,
      show ((1 : ℕ) == 6) = false from rfl, show ((1 : ℕ) == 3) = false from rfl, show ((1 : ℕ) == 1) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true]
    intro _
    exact ⟨hFa, SimS.push hs ht, he⟩
  by_cases h0' : op = 0
  · subst h0'
    simp only [show ((0 : ℕ) == 7) = false from rfl, show ((0 : ℕ) == 5) = false from rfl,
      show ((0 : ℕ) == 6) = false from rfl, show ((0 : ℕ) == 3) = false from rfl, show ((0 : ℕ) == 1) = false from rfl,
      show ((0 : ℕ) == 0) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
    intro _
    exact ⟨SimV.zero L false, SimS.push hs ht, he⟩
  have hne : ∀ k ∈ [7, 5, 6, 3, 1, 0], (op == k) = false := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa only [beq_eq_false_iff_ne, ne_eq]
  simp only [hne 7 (by decide), hne 5 (by decide), hne 6 (by decide), hne 3 (by decide), hne 1 (by decide), hne 0 (by decide),
    Bool.false_eq_true, ite_false]
  by_cases h8 : op = 8
  · subst h8
    simp only [show ((8 : ℕ) == 8) = true from rfl, ite_true]
    by_cases hc : ((la && lb) || (la && m != 0) || (lb && m != 0)) = true
    · simp only [hc, ite_true]; intro h0; cases h0
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro _
      have hc' : (lb && (m != 0)) = false ∧ (la && (lb || (m != 0))) = false := by
        revert hc; generalize (m != 0) = mb; cases la <;> cases lb <;> cases mb <;> decide
      exact ⟨(ht.add (hFa.mul (hFb.wmul _ _ hc'.1) hc'.2)).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), hs, he⟩
  by_cases h4 : op = 4
  · subst h4
    simp only [show ((4 : ℕ) == 8) = false from rfl, show ((4 : ℕ) == 4) = true from rfl, Bool.false_eq_true,
      ite_false, ite_true]
    intro _
    exact ⟨SimS.top hs, SimS.pop hs, SimE.push he _ ht⟩
  by_cases h2 : op = 2
  · subst h2
    simp only [show ((2 : ℕ) == 8) = false from rfl, show ((2 : ℕ) == 4) = false from rfl,
      show ((2 : ℕ) == 2) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
    by_cases hc : (la && m != 0) = true
    · simp only [hc, ite_true]; intro h0; cases h0
    · simp only [hc, Bool.false_eq_true, ite_false]
      intro _
      exact ⟨(hFa.wmul _ _ (Bool.eq_false_iff.2 hc)).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), SimS.push hs ht, he⟩
  have h8' : (op == 8) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using h8
  have h4' : (op == 4) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using h4
  have h2' : (op == 2) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using h2
  simp only [h8', h4', h2', Bool.false_eq_true, ite_false]
  intro _
  exact ⟨((SimS.top hs).add ht).flag (fun hh ↦ by simpa only [Bool.or_assoc] using hh), SimS.pop hs, he⟩

theorem sim_fold (L : Lam) (lim : ℕ → Bool) (FA : Array FEA) (F2 : Array FE2) (W : Array FE)
    (hF : SimF L lim FA F2) (l : List ℕ) : ∀ sa s2 sf, SimR L sa s2 sf →
      SimR L (l.foldl (fuse_fstep FA W) sa) (l.foldl (fstep2 L F2 W) s2) (l.foldl (lstep lim) sf) := by
  induction l with
  | nil => intro sa s2 sf h; exact h
  | cons n l ih => intro sa s2 sf h; exact ih _ _ _ (sim_step L lim FA F2 W hF sa s2 sf h n)

/-- **The fused code at `E2` under the leaf map simulates the fused code over `FEA`** (`linCode`'s check). -/
theorem runF_sim (L : Lam) (lim : ℕ → Bool) (FA : Array FEA) (F2 : Array FE2) (c : FCode)
    (hF : SimF L lim FA F2) (hok : (linCode lim c).1 = true) :
    SimV L (c.ins.toList.foldl (lstep lim) (false, #[], true, false)).1 (runFG FA c).1 (runF2 L F2 c).1 ∧
      SimE L (c.ins.toList.foldl (lstep lim) (false, #[], true, false)).2.2.2 (runFG FA c).2 (runF2 L F2 c).2 := by
  rw [linCode_fold] at hok
  have h := sim_fold L lim FA F2 c.ws hF c.ins.toList (0, #[], #[]) (0, #[], #[]) (false, #[], true, false)
    (fun _ ↦ ⟨SimV.zero L false, SimS.empty L, SimE.empty L false⟩)
  obtain ⟨h1, -, h3⟩ := h hok
  rw [fuse_runF, runF2_fold]
  exact ⟨h1, h3⟩

/-! ## Kernel factors under the leaf map -/

theorem kt_yy : FE.y * FE.y = (⟨0, 0, 1⟩ : FE) := by
  rw [fuse_fe_y2 1, show FE.ofK 1 = 1 from rfl, one_mul]

theorem lam_ofE_y (L : Lam) : lamE L FE.y = L.r1 := by
  simp only [lamE, FE.y, show FE2.ofK 0 = 0 from rfl, show FE2.ofK 1 = 1 from rfl]; ring

theorem lam_ofE_yy (L : Lam) : lamE L (FE.y * FE.y) = L.r2 := by
  rw [kt_yy]
  simp only [lamE, show FE2.ofK 0 = 0 from rfl, show FE2.ofK 1 = 1 from rfl]; ring

/-- **The limb factor under the leaf map**: `Σ_m eq_m·y^m ↦ Σ_m eq_m·ρ_m`. -/
theorem limbVal_sim (L : Lam) (a b : FE2) : SimV L true (limbValG (emb a) (emb b)) (limbVal2 L a b) := by
  refine ⟨?_, fun h ↦ by simp only [Bool.true_eq_false] at h⟩
  unfold limbValG limbVal2
  simp only [a2_fun, m2_fun, ← map_mul, ← map_sub, ← map_one emb, ← map_add]
  rw [lam_add, lam_add, lam_emb, lam_emb_mul, lam_emb_mul, lam_ofE, lam_ofE, lam_ofE_y, lam_ofE_yy]
  simp only [kt_sub2]

theorem emb_getD (r : Array FE2) (i : ℕ) : (r.map emb).getD i 0 = emb (r.getD i 0) := nat_getD emb r i

/-- `KF.limb`'s flag. -/
def isLimb : KF → Bool
  | .limb _ => true
  | _ => false

/-- **A kernel factor under the leaf map.** -/
theorem kfVal_sim (L : Lam) (P : Pt2) (f : KF) :
    SimV L (isLimb f) (kfValG (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) f) (kfVal2 L P f) := by
  cases f with
  | pair i j =>
    have e : kfValG (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) (.pair i j) =
        emb (kfVal2 L P (.pair i j)) := by
      simp only [kfValG, kfVal2, emb_getD, a2_fun, ← kt_sub2, map_sub, map_one]
    rw [e]; exact SimV.of_emb L _ _
  | fixX i b =>
    have e : kfValG (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) (.fixX i b) =
        emb (kfVal2 L P (.fixX i b)) := by
      simp only [kfValG, kfVal2, emb_getD, eq1G]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, a2_fun, ← kt_sub2, map_sub, map_one]
    rw [e]; exact SimV.of_emb L _ _
  | succ xs ys =>
    have e : kfValG (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) (.succ xs ys) =
        emb (kfVal2 L P (.succ xs ys)) := by
      simp only [kfValG, kfVal2, emb_getD, succVal2_eqG]
      rw [← nat_succVal]
      simp only [List.map_map, Function.comp_def]
    rw [e]; exact SimV.of_emb L _ _
  | limb e =>
    simp only [kfValG, kfVal2, emb_getD, isLimb]
    exact limbVal_sim L _ _
  | ypow j c =>
    have e : kfValG (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) (.ypow j c) =
        emb (kfVal2 L P (.ypow j c)) := by
      simp only [kfValG, kfVal2, emb_getD, a2_fun, mK_eq, ofE_ofK, ← kt_sub2, map_sub, map_one, map_add,
        map_mul]
      have h2 : (2 : FEA) = 0 := CharTwo.two_eq_zero
      linear_combination (emb (P.ry.getD j 0) * emb (FE2.ofK c)) * h2
    rw [e]; exact SimV.of_emb L _ _

/-! ## The tables -/


/-- The limb count `limbTabs` computes. -/
def limbCntL (fs : List KF) : ℕ := (fs.filter fun f ↦ match f with | KF.limb _ => true | _ => false).length

/-- **What `limbTabs` guarantees**: kernel entries have at most one limb factor, a kernel table with one is listed,
no product table reads a listed table. -/
structure LimbOk (rs : Array TRec) (lt : Array ℕ) : Prop where
  ker1 : ∀ t ks, rs.getD t .one = .ker ks → ∀ fs ∈ ks, limbCntL fs ≤ 1
  kerL : ∀ t ks, rs.getD t .one = .ker ks → (∃ fs ∈ ks, 0 < limbCntL fs) → lt.contains t = true
  prod : ∀ t rows, rs.getD t .one = .prod rows → ∀ r ∈ rows, ∀ k ∈ r, lt.contains k.1 = false

/-- `limbTabs`'s first loop body. -/
def ltBody1 (rs : Array TRec) (t : ℕ) (s : Option (Option (Array ℕ)) × Array ℕ) :
    Id (ForInStep (Option (Option (Array ℕ)) × Array ℕ)) :=
  match rs.getD t TRec.one with
  | TRec.ker ks =>
    if ((ks.map limbCntL).any fun x ↦ decide (x > 1)) = true then pure (ForInStep.done (some none, s.2))
    else if ((ks.map limbCntL).any fun x ↦ decide (x > 0)) = true then pure (ForInStep.yield (none, s.2.push t))
    else pure (ForInStep.yield (none, s.2))
  | _ => pure (ForInStep.yield (none, s.2))

/-- `limbTabs`'s second loop body. -/
def ltBody2 (rs : Array TRec) (out : Array ℕ) (t : ℕ) (_ : Option (Option (Array ℕ)) × Unit) :
    Id (ForInStep (Option (Option (Array ℕ)) × Unit)) :=
  match rs.getD t TRec.one with
  | TRec.prod rows =>
    if (rows.any fun r ↦ r.any fun k ↦ out.contains k.1) = true then pure (ForInStep.done (some none, ()))
    else pure (ForInStep.yield (none, ()))
  | _ => pure (ForInStep.yield (none, ()))

theorem lt_mem_any {α : Type} (ks : Array α) (g : α → ℕ) (c : ℕ) (h : ¬((ks.map g).any fun x ↦ decide (x > c)) = true) :
    ∀ fs ∈ ks, g fs ≤ c := by
  intro fs hfs
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hfs
  by_contra hc
  exact h (Array.any_eq_true.2 ⟨i, by simpa only [Array.size_map] using hi, by simp only [Array.getElem_map]; simp only [gt_iff_lt, decide_eq_true_eq]; omega⟩)

theorem lt_loop1 (rs : Array TRec) (l : List ℕ) : ∀ out : Array ℕ,
    ((forIn l (none, out) (ltBody1 rs)).run.1 = none ∨ (forIn l (none, out) (ltBody1 rs)).run.1 = some none) ∧
    ((forIn l (none, out) (ltBody1 rs)).run.1 = none →
      (∀ t ∈ l, ∀ ks, rs.getD t .one = .ker ks → ∀ fs ∈ ks, limbCntL fs ≤ 1) ∧
      (∀ t ∈ l, ∀ ks, rs.getD t .one = .ker ks → (∃ fs ∈ ks, 0 < limbCntL fs) →
        t ∈ (forIn l (none, out) (ltBody1 rs)).run.2) ∧
      (∀ x ∈ out, x ∈ (forIn l (none, out) (ltBody1 rs)).run.2)) := by
  induction l with
  | nil => intro out; simp only [List.forIn_nil, Id.run_pure, reduceCtorEq, or_false, List.not_mem_nil, Array.getD_eq_getD_getElem?,
    IsEmpty.forall_iff, implies_true, forall_exists_index, and_imp, imp_self, and_self]
  | cons t l ih =>
    intro out
    rw [List.forIn_cons]
    have hstep : ∀ out' : Array ℕ, (∀ x ∈ out, x ∈ out') → (t ∈ out' ∨ ∀ ks, rs.getD t .one = .ker ks →
          ∀ fs ∈ ks, limbCntL fs = 0) → (∀ ks, rs.getD t .one = .ker ks → ∀ fs ∈ ks, limbCntL fs ≤ 1) →
        ((forIn l (none, out') (ltBody1 rs)).run.1 = none ∨ (forIn l (none, out') (ltBody1 rs)).run.1 = some none) ∧
        ((forIn l (none, out') (ltBody1 rs)).run.1 = none →
          (∀ t' ∈ t :: l, ∀ ks, rs.getD t' .one = .ker ks → ∀ fs ∈ ks, limbCntL fs ≤ 1) ∧
          (∀ t' ∈ t :: l, ∀ ks, rs.getD t' .one = .ker ks → (∃ fs ∈ ks, 0 < limbCntL fs) →
            t' ∈ (forIn l (none, out') (ltBody1 rs)).run.2) ∧
          (∀ x ∈ out, x ∈ (forIn l (none, out') (ltBody1 rs)).run.2)) := by
      intro out' hsub ht hk1
      obtain ⟨i1, i2⟩ := ih out'
      refine ⟨i1, fun hn ↦ ?_⟩
      obtain ⟨a1, a2, a3⟩ := i2 hn
      refine ⟨fun t' ht' ↦ ?_, fun t' ht' ks hks hex ↦ ?_, fun x hx ↦ a3 x (hsub x hx)⟩
      · rcases List.mem_cons.1 ht' with rfl | ht'
        · exact hk1
        · exact a1 t' ht'
      · rcases List.mem_cons.1 ht' with rfl | ht'
        · rcases ht with ht | ht
          · exact a3 _ ht
          · obtain ⟨fs, hfs, hp⟩ := hex; have := ht ks hks fs hfs; omega
        · exact a2 t' ht' ks hks hex
    cases hrt : rs.getD t TRec.one
    case ker ks =>
      simp only [ltBody1, hrt]
      by_cases h1 : ((ks.map limbCntL).any fun x ↦ decide (x > 1)) = true
      · rw [if_pos h1]; simp only [pure_bind, Id.run_pure, reduceCtorEq, or_true, List.mem_cons, Array.getD_eq_getD_getElem?,
          forall_eq_or_imp, forall_exists_index, and_imp, imp_self, implies_true, and_true, IsEmpty.forall_iff, and_self]
      · rw [if_neg h1]
        have hk1 := lt_mem_any ks limbCntL 1 h1
        by_cases h2 : ((ks.map limbCntL).any fun x ↦ decide (x > 0)) = true
        · rw [if_pos h2]
          exact hstep (out.push t) (fun x hx ↦ Array.mem_push_of_mem _ hx) (Or.inl Array.mem_push_self)
            (fun ks' hks' ↦ by rw [hrt] at hks'; cases hks'; exact hk1)
        · rw [if_neg h2]
          have hk0 := lt_mem_any ks limbCntL 0 h2
          exact hstep out (fun x hx ↦ hx)
            (Or.inr fun ks' hks' fs hfs ↦ by rw [hrt] at hks'; cases hks'; have := hk0 fs hfs; omega)
            (fun ks' hks' ↦ by rw [hrt] at hks'; cases hks'; exact hk1)
    all_goals
      simp only [ltBody1, hrt]
      exact hstep out (fun x hx ↦ hx) (Or.inr fun ks' hks' ↦ by rw [hrt] at hks'; cases hks')
        (fun ks' hks' ↦ by rw [hrt] at hks'; cases hks')

theorem lt_loop2 (rs : Array TRec) (out : Array ℕ) (l : List ℕ) :
    ((forIn l (none, ()) (ltBody2 rs out)).run.1 = none ∨ (forIn l (none, ()) (ltBody2 rs out)).run.1 = some none) ∧
    ((forIn l (none, ()) (ltBody2 rs out)).run.1 = none →
      ∀ t ∈ l, ∀ rows, rs.getD t .one = .prod rows → ∀ r ∈ rows, ∀ k ∈ r, out.contains k.1 = false) := by
  induction l with
  | nil => simp only [List.forIn_nil, Id.run_pure, reduceCtorEq, or_false, List.not_mem_nil, Array.getD_eq_getD_getElem?, Array.contains_eq_mem, decide_eq_false_iff_not, Prod.forall, IsEmpty.forall_iff, implies_true, imp_self, and_self]
  | cons t l ih =>
    rw [List.forIn_cons]
    cases hrt : rs.getD t TRec.one
    case prod rows =>
      simp only [ltBody2, hrt]
      by_cases h1 : (rows.any fun r ↦ r.any fun k ↦ out.contains k.1) = true
      · rw [if_pos h1]; simp only [pure_bind, Id.run_pure, reduceCtorEq, or_true, List.mem_cons, Array.getD_eq_getD_getElem?,
          Array.contains_eq_mem, decide_eq_false_iff_not, Prod.forall, forall_eq_or_imp, IsEmpty.forall_iff, and_self]
      · rw [if_neg h1]
        refine ⟨ih.1, fun hn t' ht' rows' hr' r hr k hk ↦ ?_⟩
        rcases List.mem_cons.1 ht' with rfl | ht'
        · rw [hrt] at hr'; cases hr'
          by_contra hc
          simp only [Bool.not_eq_false] at hc
          obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hr
          exact h1 (Array.any_eq_true.2 ⟨i, hi, List.any_eq_true.2 ⟨k, hk, hc⟩⟩)
        · exact ih.2 hn t' ht' rows' hr' r hr k hk
    all_goals
      simp only [ltBody2, hrt]
      refine ⟨ih.1, fun hn t' ht' rows' hr' r hr k hk ↦ ?_⟩
      rcases List.mem_cons.1 ht' with rfl | ht'
      · rw [hrt] at hr'; cases hr'
      · exact ih.2 hn t' ht' rows' hr' r hr k hk

theorem lt_getD_out (rs : Array TRec) (t : ℕ) (ht : rs.size ≤ t) : rs.getD t .one = .one := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ht]; rfl

theorem limbTabs_ok (rs : Array TRec) (lt : Array ℕ) (h : limbTabs rs = some lt) : LimbOk rs lt := by
  unfold limbTabs at h
  simp only [Id.run_bind, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  generalize hB1 : (fun t __s ↦ _ : ℕ → Option (Option (Array ℕ)) × Array ℕ →
    Id (ForInStep (Option (Option (Array ℕ)) × Array ℕ))) = B1 at h
  have e1 : B1 = ltBody1 rs := by
    rw [← hB1]
    funext t s
    unfold ltBody1 limbCntL
    cases rs.getD t TRec.one <;> rfl
  subst e1
  generalize hB2 : (fun t __s ↦ _ : ℕ → Option (Option (Array ℕ)) × Unit →
    Id (ForInStep (Option (Option (Array ℕ)) × Unit))) = B2 at h
  have e2 : B2 = ltBody2 rs (forIn (List.range' 0 [:rs.size].size) (none, #[]) (ltBody1 rs)).run.2 := by
    rw [← hB2]
    funext t s
    unfold ltBody2
    cases rs.getD t TRec.one <;> rfl
  subst e2
  obtain ⟨c1, c2⟩ := lt_loop1 rs (List.range' 0 [:rs.size].size) #[]
  generalize forIn (List.range' 0 [:rs.size].size) (none, #[]) (ltBody1 rs) = r1 at h c1 c2
  obtain ⟨d1, d2⟩ := lt_loop2 rs r1.run.2 (List.range' 0 [:rs.size].size)
  generalize forIn (List.range' 0 [:rs.size].size) (none, ()) (ltBody2 rs r1.run.2) = r2 at h d1 d2
  have hmem : ∀ t, t < rs.size → t ∈ List.range' 0 [:rs.size].size := fun t ht ↦ by
    simp only [Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one, List.mem_range', one_mul, zero_add, exists_eq_right']; omega
  rcases c1 with h1 | h1
  · rcases d1 with g1 | g1
    · have hl : lt = r1.run.2 := by
        simp only [h1, Id.run_bind, g1] at h
        exact (Option.some.inj h).symm
      subst hl
      obtain ⟨a1, a2, -⟩ := c2 h1
      refine ⟨fun t ks hks ↦ ?_, fun t ks hks hex ↦ ?_, fun t rows hrows ↦ ?_⟩
      · by_cases ht : t < rs.size
        · exact a1 t (hmem t ht) ks hks
        · rw [lt_getD_out rs t (by omega)] at hks; cases hks
      · by_cases ht : t < rs.size
        · exact Array.contains_iff.2 (a2 t (hmem t ht) ks hks hex)
        · rw [lt_getD_out rs t (by omega)] at hks; cases hks
      · by_cases ht : t < rs.size
        · exact d2 g1 t (hmem t ht) rows hrows
        · rw [lt_getD_out rs t (by omega)] at hrows; cases hrows
    · simp only [h1, Id.run_bind, g1, Id.run_pure, reduceCtorEq] at h
  · simp only [h1, Id.run_pure, reduceCtorEq] at h

/-- The `E2` point and the `FEA` point. -/
def ptA (pt : List FE2) : List FEA := pt.map emb

theorem ptA_ofList (pt : List FE2) :
    PtG.ofList (ptA pt) = ⟨(Pt2.ofList pt).kap.map emb, (Pt2.ofList pt).rx.map emb, (Pt2.ofList pt).ry.map emb⟩ := by
  simp only [PtG.ofList, ptA, Pt2.ofList, List.map_toArray, List.map_take, List.map_drop]

/-- **A kernel entry under the leaf map**: pure without a limb factor, the leaf map's value with one. -/
theorem kerVal_sim (L : Lam) (P : Pt2) (fs : List KF) (h1 : limbCntL fs ≤ 1) :
    SimV L (decide (0 < limbCntL fs)) (kerValG (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) fs)
      (kerVal2 L P fs) := by
  unfold kerValG kerVal2
  suffices H : ∀ (fs : List KF) (xa : FEA) (x2 : FE2) (g : Bool), SimV L g xa x2 →
      (g = true → limbCntL fs = 0) → limbCntL fs ≤ 1 →
      SimV L (g || decide (0 < limbCntL fs)) (fs.foldl (fun acc f ↦ acc * kfValG
        (⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩ : PtG FEA) f) xa)
        (fs.foldl (fun acc f ↦ m2 acc (kfVal2 L P f)) x2) by
    have := H fs 1 1 false ⟨by rw [← map_one emb, lam_emb], fun _ ↦ (map_one emb).symm⟩ (by simp only [Bool.false_eq_true, IsEmpty.forall_iff]) h1
    simpa only [Bool.false_or] using this
  intro fs
  induction fs with
  | nil => intro xa x2 g h _ _; simpa only [limbCntL, List.filter_nil, List.length_nil, lt_self_iff_false, decide_false, Bool.or_false, List.foldl_nil] using h
  | cons f fs ih =>
    intro xa x2 g h hg hc
    simp only [List.foldl_cons]
    have hcnt : limbCntL (f :: fs) = (if isLimb f then 1 else 0) + limbCntL fs := by
      cases f <;> simp only [limbCntL, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, isLimb, ↓reduceIte, zero_add, List.filter_cons_of_pos, List.length_cons] <;> omega
    have hk := kfVal_sim L P f
    have hm := h.mul hk (by
      cases g
      · rfl
      · have h0 := hg rfl
        rw [hcnt] at h0
        cases hf : isLimb f
        · rfl
        · simp only [hf, ↓reduceIte] at h0; omega)
    rw [m2_fun] at *
    have := ih _ _ _ hm (by
      intro hgl
      cases hf : isLimb f <;> simp only [hf, ↓reduceIte, Bool.or_false, Bool.or_true] at hcnt hgl
      · have := hg hgl; omega
      · omega) (by omega)
    refine this.flag ?_
    intro hx
    cases g
    · cases hf : isLimb f <;>
        simp only [hf, ↓reduceIte, Bool.false_or, Bool.true_or, Bool.or_false, decide_eq_true_eq] at hx hcnt ⊢ <;>
        omega
    · rfl


theorem emb_getElem? (arr : Array FE2) (i : ℕ) : (arr.map emb)[i]?.getD 0 = emb (arr[i]?.getD 0) := by
  rw [Array.getElem?_map]; cases arr[i]? <;> simp only [Option.map_none, Option.getD_none, map_zero, Option.map_some, Option.getD_some]

/-- A product of pure keys is pure. -/
theorem prodKeys_pure (TA : Array (Array FEA)) (T2 : Array (Array FE2)) (ks : List (ℕ × ℕ))
    (h : ∀ k ∈ ks, keyValG TA k = emb (keyValG T2 k)) : prodKeysG TA ks = emb (prodKeysG T2 ks) := by
  cases ks with
  | nil => simp only [prodKeysG, map_one]
  | cons k ks =>
    simp only [prodKeysG]
    suffices H : ∀ (l : List (ℕ × ℕ)), (∀ k ∈ l, keyValG TA k = emb (keyValG T2 k)) → ∀ a : FE2,
        l.foldl (fun acc k' ↦ acc * keyValG TA k') (emb a) = emb (l.foldl (fun acc k' ↦ acc * keyValG T2 k') a) by
      rw [h k List.mem_cons_self]
      exact H ks (fun k' hk' ↦ h k' (List.mem_cons_of_mem _ hk')) _
    intro l
    induction l with
    | nil => intro _ a; rfl
    | cons k' l ih =>
      intro hl a
      simp only [List.foldl_cons]
      rw [hl k' List.mem_cons_self, ← map_mul]
      exact ih (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) _

/-- **The tables under the leaf map** (`linOk`'s `limbTabs`): every entry simulated, flagged by its table. -/
theorem tabs_sim (L : Lam) (pt : List FE2) (rs : Array TRec) (lt : Array ℕ) (hlt : LimbOk rs lt) (t i : ℕ) :
    SimV L (lt.contains t) (((tabsAtG (PtG.ofList (ptA pt)) rs).getD t #[]).getD i 0)
      (((tabsAt2 L (Pt2.ofList pt) rs).getD t #[]).getD i 0) := by
  rw [ptA_ofList]
  generalize Pt2.ofList pt = P
  unfold tabsAtG tabsAt2
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx]
  -- the pre-product tables, as data
  generalize hA : Array.map (fun r ↦ _ : TRec → Array FEA) rs = T0A
  generalize h2 : Array.map (fun r ↦ _ : TRec → Array FE2) rs = T02
  -- every pre-product entry simulated, flagged by its table
  have hT0 : ∀ t' i' : ℕ, SimV L (lt.contains t') ((T0A[t']?.getD #[])[i']?.getD 0) ((T02[t']?.getD #[])[i']?.getD 0) := by
    intro t' i'
    rw [← hA, ← h2, Array.getElem?_map, Array.getElem?_map]
    cases hrt : rs[t']? with
    | none => simpa only [Array.contains_eq_mem, beq_iff_eq, Option.map_none, Option.getD_none, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg] using SimV.zero L _
    | some r =>
      have hget : rs.getD t' .one = r := by rw [Array.getD_eq_getD_getElem?, hrt]; rfl
      simp only [Option.map_some, Option.getD_some]
      cases r with
      | one =>
        simp only [TRec.evalG, TRec.eval2]
        rcases i' with _ | i'
        · simpa only [Array.contains_eq_mem, List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, getElem?_pos, List.getElem_toArray, List.getElem_cons_zero, Option.getD_some, map_one] using SimV.of_emb L (lt.contains t') (1 : FE2)
        · simpa only [Array.contains_eq_mem, List.size_toArray, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, getElem?_neg, Option.getD_none] using SimV.zero L _
      | eqx bits =>
        simp only [subTab2_eqG, eqLevels2_eqG]
        have e : subTabG (P.rx.map emb) (if (groupOf xVars 10 bits).1 == 0 then eqLevelsG (P.rx.map emb) 0 10
            else eqLevelsG (P.rx.map emb) 10 (xVars - 10)) (groupOf xVars 10 bits).1 (groupOf xVars 10 bits).2 bits =
            (subTabG P.rx (if (groupOf xVars 10 bits).1 == 0 then eqLevelsG P.rx 0 10
              else eqLevelsG P.rx 10 (xVars - 10)) (groupOf xVars 10 bits).1 (groupOf xVars 10 bits).2 bits).map emb := by
          rw [nat_subTab]
          split_ifs <;> rw [nat_eqLevels]
        rw [e, emb_getElem?]
        exact SimV.of_emb L _ _
      | eqy bits =>
        simp only [subTab2_eqG, eqLevels2_eqG]
        have e : subTabG (P.ry.map emb) (if (groupOf yVars 11 bits).1 == 0 then eqLevelsG (P.ry.map emb) 0 11
            else eqLevelsG (P.ry.map emb) 11 (yVars - 11)) (groupOf yVars 11 bits).1 (groupOf yVars 11 bits).2 bits =
            (subTabG P.ry (if (groupOf yVars 11 bits).1 == 0 then eqLevelsG P.ry 0 11
              else eqLevelsG P.ry 11 (yVars - 11)) (groupOf yVars 11 bits).1 (groupOf yVars 11 bits).2 bits).map emb := by
          rw [nat_subTab]
          split_ifs <;> rw [nat_eqLevels]
        rw [e, emb_getElem?]
        exact SimV.of_emb L _ _
      | kap =>
        simp only [TRec.evalG, TRec.eval2, kapTab2_eqG]
        rw [← nat_kapTab, emb_getElem?]
        exact SimV.of_emb L _ _
      | ker ks =>
        simp only [TRec.evalG, TRec.eval2, Array.getElem?_map]
        cases hks : ks[i']? with
        | none => simpa only [Array.contains_eq_mem, Option.map_none, Option.getD_none] using SimV.zero L _
        | some fs =>
          have hmem : fs ∈ ks := Array.mem_of_getElem? hks
          simp only [Option.map_some, Option.getD_some]
          exact (kerVal_sim L P fs (hlt.ker1 t' ks hget fs hmem)).flag
            (fun hc ↦ hlt.kerL t' ks hget ⟨fs, hmem, by simpa only [decide_eq_true_eq] using hc⟩)
      | prod rows => simpa only [Array.contains_eq_mem, TRec.evalG, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, TRec.eval2] using SimV.zero L _
  -- the product tables read pure entries
  cases hrt : rs[t]? with
  | none => simpa only [Array.contains_eq_mem, Option.map_none, Option.getD_none, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg] using SimV.zero L _
  | some r =>
    have hget : rs.getD t .one = r := by rw [Array.getD_eq_getD_getElem?, hrt]; rfl
    simp only [Option.map_some, Option.getD_some]
    cases r
    case prod rows =>
      simp only [Array.getElem?_map, prodKeys2_eqG]
      cases hks : rows[i]? with
      | none => simpa only [Array.contains_eq_mem, Option.map_none, Option.getD_none] using SimV.zero L _
      | some ks =>
        have hmem : ks ∈ rows := Array.mem_of_getElem? hks
        simp only [Option.map_some, Option.getD_some]
        rw [prodKeys_pure T0A T02 ks (fun k hk ↦ by
          have := hT0 k.1 k.2
          rw [hlt.prod t rows hget ks hmem k hk] at this
          simp only [keyValG, Array.getD_eq_getD_getElem?]
          exact this.2 rfl), prodKeys2_eqG]
        exact SimV.of_emb L _ _
    all_goals exact hT0 t i

/-! ## The automaton under the leaf map -/

/-- **Two `while` loops in lockstep** keep a relation of their states, and end in `Q`. -/
theorem loop_rel {β γ : Type} (f : Unit → β → Id (ForInStep β)) (g : Unit → γ → Id (ForInStep γ)) (μ : β → ℕ)
    (R Q : β → γ → Prop)
    (h : ∀ b c, R b c → match (f () b).run, (g () c).run with
      | .done b', .done c' => Q b' c'
      | .yield b', .yield c' => R b' c' ∧ μ b' < μ b
      | _, _ => False)
    (b : β) (c : γ) (hbc : R b c) : Q (forIn Lean.Loop.mk b f).run (forIn Lean.Loop.mk c g).run := by
  induction hm : μ b using Nat.strong_induction_on generalizing b c with
  | _ n ih =>
    have := h b c hbc
    rw [show forIn Lean.Loop.mk b f = Lean.Loop.forIn Lean.Loop.mk b f from rfl, Lean.Loop.forIn_eq_of_monadTail,
      show forIn Lean.Loop.mk c g = Lean.Loop.forIn Lean.Loop.mk c g from rfl, Lean.Loop.forIn_eq_of_monadTail]
    revert this
    rcases hf : (f () b).run with b' | b' <;> rcases hg : (g () c).run with c' | c' <;> intro this
    · simp only [Id.run] at hf hg ⊢; rw [hf, hg]; exact this
    · exact absurd this id
    · exact absurd this id
    · simp only [Id.run] at hf hg ⊢; rw [hf, hg]; exact ih _ (hm ▸ this.2) b' c' this.1 rfl

/-- Arrays simulated entrywise under one flag. -/
def SimL (L : Lam) (f : Bool) (xs : Array FEA) (ys : Array FE2) : Prop :=
  xs.size = ys.size ∧ ∀ i, SimV L f (xs.getD i 0) (ys.getD i 0)

theorem SimL.push {L : Lam} {f : Bool} {xs : Array FEA} {ys : Array FE2} (h : SimL L f xs ys) {x : FEA} {y : FE2}
    (hv : SimV L f x y) : SimL L f (xs.push x) (ys.push y) := by
  refine ⟨by simp only [Array.size_push, h.1, Nat.add_left_cancel_iff], fun i ↦ ?_⟩
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.1]
  have := h.2 i
  simp only [Array.getD_eq_getD_getElem?, h.1] at this
  split_ifs
  · simp_all only [lt_self_iff_false, not_false_eq_true, getElem?_neg, Option.getD_none, Option.getD_some]
  · simp_all only

theorem auto_half_sim (L : Lam) (f : Bool) (cs : Array ℕ) (vA : Array FEA) (v2 : Array FE2) (b : FE2) (sh : ℕ)
    (h : SimL L f vA v2) :
    (auto_half cs vA (emb b) sh).1 = (auto_half cs v2 b sh).1 ∧
      SimL L f (auto_half cs vA (emb b) sh).2.1 (auto_half cs v2 b sh).2.1 ∧
      (auto_half cs vA (emb b) sh).2.2 = (auto_half cs v2 b sh).2.2 := by
  unfold auto_half
  simp only [Id.run_bind, Id.run_pure]
  refine loop_rel (β := Array ℕ × Array FEA × Array ℕ × ℕ) (γ := Array ℕ × Array FE2 × Array ℕ × ℕ) _ _
    (fun s ↦ cs.size - s.2.2.2)
    (fun sA s2 ↦ sA.1 = s2.1 ∧ SimL L f sA.2.1 s2.2.1 ∧ sA.2.2.1 = s2.2.2.1 ∧ sA.2.2.2 = s2.2.2.2)
    (fun sA s2 ↦ sA.1 = s2.1 ∧ SimL L f sA.2.1 s2.2.1 ∧ sA.2.2.1 = s2.2.2.1) ?_ _ _
    ⟨rfl, ⟨rfl, fun i ↦ by simpa only [Array.mkEmpty_eq, Array.getD_eq_getD_getElem?, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none] using SimV.zero L f⟩, rfl, rfl⟩
  rintro ⟨tsA, xsA, ksA, i⟩ ⟨ts2, xs2, ks2, i'⟩ ⟨h1, hx, h3, h4⟩
  dsimp only at h1 h3 h4 ⊢
  subst h1 h3 h4
  have hv : ∀ j, SimV L f (vA.getD j 0) (v2.getD j 0) := h.2
  by_cases hi : i < cs.size
  · rw [if_pos hi, if_pos hi]
    by_cases hd : ((cs.getD i 0 + sh) % 2 == 0) = true
    · rw [if_pos hd, if_pos hd]
      by_cases hn : (decide (i + 1 < cs.size) && cs.getD (i + 1) 0 == cs.getD i 0 + 1) = true
      · rw [if_pos hn, if_pos hn]
        exact ⟨⟨rfl, hx.push ((hv i).add' ((hv i).add' (hv (i + 1)) |>.emb_mul b)), rfl, rfl⟩, by dsimp only; omega⟩
      · rw [if_neg hn, if_neg hn]
        exact ⟨⟨rfl, hx.push (hv i), rfl, rfl⟩, by dsimp only; omega⟩
    · rw [if_neg hd, if_neg hd]
      exact ⟨⟨rfl, hx.push (hv i), rfl, rfl⟩, by dsimp only; omega⟩
  · rw [if_neg hi, if_neg hi]
    exact ⟨rfl, hx, rfl⟩

theorem auto_merge_sim (L : Lam) (f : Bool) (a b : FE2) (ta : Array ℕ) (vaA : Array FEA) (va2 : Array FE2)
    (ka : Array ℕ) (tb : Array ℕ) (vbA : Array FEA) (vb2 : Array FE2) (kb : Array ℕ)
    (ha : SimL L f vaA va2) (hb : SimL L f vbA vb2) :
    (auto_merge (emb a) (emb b) (ta, vaA, ka) (tb, vbA, kb)).1 = (auto_merge a b (ta, va2, ka) (tb, vb2, kb)).1 ∧
      SimL L f (auto_merge (emb a) (emb b) (ta, vaA, ka) (tb, vbA, kb)).2
        (auto_merge a b (ta, va2, ka) (tb, vb2, kb)).2 := by
  have e00 : (1 - emb a - emb b + emb a * emb b : FEA) = emb (1 - a - b + a * b) := by
    simp only [map_add, map_sub, map_mul, map_one]
  have e01 : (emb b - emb a * emb b : FEA) = emb (b - a * b) := by simp only [map_sub, map_mul]
  have e10 : (emb a - emb a * emb b : FEA) = emb (a - a * b) := by simp only [map_sub, map_mul]
  have e11 : (emb a * emb b : FEA) = emb (a * b) := by simp only [map_mul]
  have hva : ∀ j, SimV L f (vaA.getD j 0) (va2.getD j 0) := ha.2
  have hvb : ∀ j, SimV L f (vbA.getD j 0) (vb2.getD j 0) := hb.2
  unfold auto_merge
  simp only [Id.run_bind, Id.run_pure]
  simp only [← map_mul emb, ← map_sub emb, ← map_add emb, ← map_one emb]
  refine loop_rel (β := Array ℕ × Array FEA × ℕ × ℕ) (γ := Array ℕ × Array FE2 × ℕ × ℕ) _ _
    (fun s ↦ (ta.size - s.2.2.1) + (tb.size - s.2.2.2))
    (fun sA s2 ↦ sA.1 = s2.1 ∧ SimL L f sA.2.1 s2.2.1 ∧ sA.2.2.1 = s2.2.2.1 ∧ sA.2.2.2 = s2.2.2.2)
    (fun sA s2 ↦ sA.1 = s2.1 ∧ SimL L f sA.2.1 s2.2.1) ?_ _ _
    ⟨rfl, ⟨rfl, fun i ↦ by simpa only [Array.mkEmpty_eq, Array.getD_eq_getD_getElem?, List.size_toArray, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none] using SimV.zero L f⟩, rfl, rfl⟩
  rintro ⟨ocA, ovA, i, j⟩ ⟨oc2, ov2, i', j'⟩ ⟨h1, hx, h3, h4⟩
  dsimp only at h1 h3 h4 ⊢
  subst h1 h3 h4
  have hwA : ∀ (k : ℕ) (xA : FEA) (x2 : FE2), SimV L f xA x2 →
      SimV L f (if (k == 2) = true then xA else if (k == 0) = true then xA - emb b * xA else emb b * xA)
        (if (k == 2) = true then x2 else if (k == 0) = true then x2 - b * x2 else b * x2) := by
    intro k xA x2 hxx
    exact SimV.ite _ hxx (SimV.ite _ (hxx.sub' (hxx.emb_mul b)) (hxx.emb_mul b))
  by_cases hc : (decide (i < ta.size) || decide (j < tb.size)) = true
  · rw [if_pos hc, if_pos hc]
    have hc' : i < ta.size ∨ j < tb.size := by simpa only [Bool.or_eq_true, decide_eq_true_eq] using hc
    by_cases h1 : (decide (j ≥ tb.size) || decide (i < ta.size) && decide (ta.getD i 0 < tb.getD j 0)) = true
    · rw [if_pos h1, if_pos h1]
      have h1' : j ≥ tb.size ∨ (i < ta.size ∧ ta.getD i 0 < tb.getD j 0) := by
        simpa only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h1
      exact ⟨⟨rfl, hx.push (SimV.ite _ ((hva i).sub' ((hva i).emb_mul a)) ((hva i).mul_iteE _ _ _)), rfl, rfl⟩,
        by dsimp only; omega⟩
    · rw [if_neg h1, if_neg h1]
      have h1' : j < tb.size ∧ (i < ta.size → tb.getD j 0 ≤ ta.getD i 0) := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_or, not_and, not_lt] at h1
        omega
      by_cases h2 : (decide (i ≥ ta.size) || decide (tb.getD j 0 < ta.getD i 0)) = true
      · rw [if_pos h2, if_pos h2]
        exact ⟨⟨rfl, hx.push (SimV.ite _ ((hvb j).emb_mul a) ((hvb j).mul_iteE _ _ _)), rfl, rfl⟩,
          by dsimp only; omega⟩
      · rw [if_neg h2, if_neg h2]
        have h2' : i < ta.size := by
          simp only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] at h2; omega
        by_cases h3 : (ka.getD i 0 != 2 && kb.getD j 0 != 2) = true
        · rw [if_pos h3, if_pos h3]
          exact ⟨⟨rfl, hx.push (((hva i).mul_iteE _ _ _).add' ((hvb j).mul_iteE _ _ _)), rfl, rfl⟩,
            by dsimp only; omega⟩
        · rw [if_neg h3, if_neg h3]
          exact ⟨⟨rfl, hx.push ((hwA _ _ _ (hva i)).add' (((hwA _ _ _ (hva i)).add' (hwA _ _ _ (hvb j))).emb_mul a)),
            rfl, rfl⟩, by dsimp only; omega⟩
  · rw [if_neg hc, if_neg hc]
    exact ⟨rfl, hx⟩

theorem autoStepP_sim (L : Lam) (f : Bool) (R : ℕ) (a b : FE2) (cs : Array ℕ) (vA : Array FEA) (v2 : Array FE2)
    (h : SimL L f vA v2) :
    (autoStepPG R (emb a) (emb b) cs vA).1 = (autoStepPG R a b cs v2).1 ∧
      SimL L f (autoStepPG R (emb a) (emb b) cs vA).2 (autoStepPG R a b cs v2).2 := by
  rw [auto_autoStepP_eq, auto_autoStepP_eq]
  obtain ⟨e1, s1, k1⟩ := auto_half_sim L f cs vA v2 b 0 h
  obtain ⟨e2, s2, k2⟩ := auto_half_sim L f cs vA v2 b R h
  rw [show auto_half cs vA (emb b) 0 = ((auto_half cs vA (emb b) 0).1, (auto_half cs vA (emb b) 0).2.1,
      (auto_half cs vA (emb b) 0).2.2) from rfl,
    show auto_half cs vA (emb b) R = ((auto_half cs vA (emb b) R).1, (auto_half cs vA (emb b) R).2.1,
      (auto_half cs vA (emb b) R).2.2) from rfl, e1, e2, k1, k2]
  exact auto_merge_sim L f a b _ _ _ _ _ _ _ _ s1 s2

/-! ## The flat tables -/

/-- A flat index below the total lies in one table. -/
theorem flat_split (rs : Array TRec) (fi : ℕ) (h : fi < fuse_off rs rs.size) :
    ∃ t < rs.size, ∃ i < (rs.getD t .one).size, fi = fuse_off rs t + i := by
  suffices H : ∀ n, fi < fuse_off rs n → ∃ t < n, ∃ i < (rs.getD t .one).size, fi = fuse_off rs t + i from H _ h
  intro n
  induction n with
  | zero => intro h0; simp only [fuse_off, Array.getD_eq_getD_getElem?, List.range_zero, List.map_nil, List.sum_nil, not_lt_zero] at h0
  | succ n ih =>
    intro hn
    rw [fuse_off_succ] at hn
    by_cases h1 : fi < fuse_off rs n
    · obtain ⟨t, ht, i, hi, rfl⟩ := ih h1
      exact ⟨t, by omega, i, hi, rfl⟩
    · exact ⟨n, by omega, fi - fuse_off rs n, by omega, by omega⟩

theorem flatTabsG_size (rs : Array TRec) {R : Type} [CommRing R] [CharP R 2] (T : Array (Array R)) :
    (flatTabsG rs T).size = fuse_off rs rs.size := by
  rw [← Array.length_toList, fuse_flatTabs, List.length_flatMap]
  simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range, fuse_off]

/-- **The flat tables under the leaf map**, flagged by `linOk`'s `lim`. -/
theorem flat_sim (L : Lam) (rs : Array TRec) (lt : Array ℕ) (TA : Array (Array FEA)) (T2 : Array (Array FE2))
    (hT : ∀ t i, SimV L (lt.contains t) ((TA.getD t #[]).getD i 0) ((T2.getD t #[]).getD i 0)) :
    SimF L (fun fi ↦ lt.any fun t ↦ (tabOffs rs).getD t 0 ≤ fi && fi < (tabOffs rs).getD (t + 1) 0)
      (flatTabsG rs TA) (flatTabsG rs T2) := by
  intro fi
  by_cases h : fi < fuse_off rs rs.size
  · obtain ⟨t, ht, i, hi, rfl⟩ := flat_split rs fi h
    rw [fuse_flat_get rs TA t i ht hi, fuse_flat_get rs T2 t i ht hi]
    refine (hT t i).flag fun hc ↦ ?_
    obtain ⟨j, hj, hjt⟩ := Array.getElem_of_mem (Array.contains_iff.1 hc)
    rw [Array.any_eq_true]
    refine ⟨j, hj, ?_⟩
    rw [hjt, fuse_tabOffs rs t (by omega), fuse_tabOffs rs (t + 1) (by omega), fuse_off_succ]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · have e1 : (flatTabsG rs TA).getD fi 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [flatTabsG_size]; omega)]; rfl
    have e2 : (flatTabsG rs T2).getD fi 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [flatTabsG_size]; omega)]; rfl
    rw [e1, e2]; exact SimV.zero L _

/-! ## Passes and the evaluator -/

/-- The leaf map as an additive map. -/
def lamAdd (L : Lam) : FEA →+ FE2 := ⟨⟨lam L, lam_zero L⟩, lam_add L⟩

/-- The `E2` point as the twin's. -/
def Pt2.toG (P : Pt2) : PtG FE2 := ⟨P.kap, P.rx, P.ry⟩

/-- The `FEA` point of an `E2` point. -/
def Pt2.toA (P : Pt2) : PtG FEA := ⟨P.kap.map emb, P.rx.map emb, P.ry.map emb⟩

/-- One step of `runAutoG`'s loop. -/
def raStep {R : Type} [CommRing R] [CharP R 2] (P : PtG R) (xs : Array ℕ) (Rs : ℕ) (s : Array ℕ × Array R)
    (k : ℕ) : Array ℕ × Array R :=
  autoStepPG Rs (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) s.1 s.2

/-- `runAutoG`'s result from its final state. -/
def raFin {R : Type} [CommRing R] (r : Array ℕ × Array R) : Array (ℕ × R) :=
  (Array.range r.1.size).map fun i ↦ (r.1.getD i 0, r.2.getD i 0)

theorem runAutoG_fold {R : Type} [CommRing R] [CharP R 2] (P : PtG R) (xs : Array ℕ) (Rs : ℕ)
    (st : Array (ℕ × R)) :
    runAutoG P xs Rs st = raFin ((List.range' 0 xs.size).foldl (raStep P xs Rs) (st.map (·.1), st.map (·.2))) := by
  unfold runAutoG
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem runAuto_sim (L : Lam) (f : Bool) (P : Pt2) (xs : Array ℕ) (R : ℕ) (stA : Array (ℕ × FEA))
    (st2 : Array (ℕ × FE2)) (h : SimE L f stA st2) :
    SimE L f (runAutoG P.toA xs R stA) (runAuto2 P xs R st2) := by
  obtain ⟨h1, h2⟩ := h
  have hc : stA.map (·.1) = st2.map (·.1) := by
    apply Array.ext (by simp only [Array.size_map, h1])
    intro i hiA hi2
    have := (h2 i).1
    simp only [Array.getD_eq_getD_getElem?] at this
    simp only [Array.size_map] at hiA hi2
    simp only [Array.getElem_map]
    rw [Array.getElem?_eq_getElem hiA, Array.getElem?_eq_getElem (h1 ▸ hiA)] at this
    exact this
  have hv : SimL L f (stA.map (·.2)) (st2.map (·.2)) := by
    refine ⟨by simp only [Array.size_map, h1], fun i ↦ ?_⟩
    have := (h2 i).2
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map] at this ⊢
    cases hA : stA[i]? <;> cases hB : st2[i]?
    · simp_all only [Array.getD_eq_getD_getElem?, Option.getD_none, getElem?_eq_none_iff, not_lt, getElem?_neg,
        Option.map_none]
    · simp_all only [Array.getD_eq_getD_getElem?, Option.getD_none, Option.getD_some, getElem?_eq_none_iff, not_lt,
        getElem?_neg, reduceCtorEq]
    · simp_all only [Array.getD_eq_getD_getElem?, Option.getD_some, Option.getD_none, getElem?_eq_none_iff, not_lt,
        Option.map_some, Option.map_none]
    · simp_all only [Array.getD_eq_getD_getElem?, Option.getD_some, Option.map_some]
  rw [runAuto2_eqG, runAutoG_fold, runAutoG_fold, hc]
  have key : ∀ (l : List ℕ) (cs : Array ℕ) (vA : Array FEA) (v2 : Array FE2), SimL L f vA v2 →
      (l.foldl (raStep P.toA xs R) (cs, vA)).1 = (l.foldl (raStep ⟨P.kap, P.rx, P.ry⟩ xs R) (cs, v2)).1 ∧
        SimL L f (l.foldl (raStep P.toA xs R) (cs, vA)).2 (l.foldl (raStep ⟨P.kap, P.rx, P.ry⟩ xs R) (cs, v2)).2 := by
    intro l
    induction l with
    | nil => intro cs vA v2 hv; exact ⟨rfl, hv⟩
    | cons k l ih =>
      intro cs vA v2 hv
      simp only [List.foldl_cons]
      have hs := autoStepP_sim L f R (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) cs vA v2 hv
      have e : raStep P.toA xs R (cs, vA) k = autoStepPG R (emb (P.rx.getD (xs.getD k 0) 0)) (emb (P.ry.getD k 0)) cs vA := by
        simp only [raStep, Pt2.toA, emb_getD]
      have e2 : raStep ⟨P.kap, P.rx, P.ry⟩ xs R (cs, v2) k = autoStepPG R (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) cs v2 :=
        rfl
      rw [e, e2, show autoStepPG R (emb (P.rx.getD (xs.getD k 0) 0)) (emb (P.ry.getD k 0)) cs vA =
          ((autoStepPG R (emb (P.rx.getD (xs.getD k 0) 0)) (emb (P.ry.getD k 0)) cs vA).1,
            (autoStepPG R (emb (P.rx.getD (xs.getD k 0) 0)) (emb (P.ry.getD k 0)) cs vA).2) from rfl, hs.1]
      exact ih _ _ _ hs.2
  obtain ⟨k1, k2⟩ := key (List.range' 0 xs.size) (st2.map (·.1)) (stA.map (·.2)) (st2.map (·.2)) hv
  unfold raFin
  rw [k1]
  refine ⟨by simp only [Array.getD_eq_getD_getElem?, Array.size_map, Array.size_range], fun i ↦ ?_⟩
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs
  · simp only [Option.map_some, Option.getD_some]
    exact ⟨by trivial, by simpa only [Array.getD_eq_getD_getElem?] using k2.2 i⟩
  · simpa only [Option.map_none, Option.getD_none, true_and] using SimV.zero L f

theorem sum_map_range {α M : Type} [AddCommMonoid M] (zs : Array α) (d : α) (F : α → M) :
    (zs.toList.map F).sum = ((List.range zs.size).map fun i ↦ F (zs.getD i d)).sum := by
  congr 1
  apply List.ext_getElem (by simp only [List.length_map, Array.length_toList, Array.getD_eq_getD_getElem?, List.length_range])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem (by simpa only [List.length_map, Array.length_toList] using h1)]
  rfl

/-- A weighted sum of simulated states with pure weights. -/
theorem SimE.wsum {L : Lam} {f : Bool} {xs : Array (ℕ × FEA)} {ys : Array (ℕ × FE2)} (h : SimE L f xs ys)
    (gA : ℕ → FEA) (g2 : ℕ → FE2) (hg : ∀ c, gA c = emb (g2 c)) :
    SimV L f ((xs.toList.map fun cv ↦ cv.2 * gA cv.1).sum) ((ys.toList.map fun cv ↦ cv.2 * g2 cv.1).sum) := by
  obtain ⟨h1, h2⟩ := h
  rw [sum_map_range xs (0, 0), sum_map_range ys (0, 0), h1]
  generalize ys.size = N
  induction N with
  | zero => simpa only [Array.getD_eq_getD_getElem?, List.range_zero, List.map_nil, List.sum_nil] using SimV.zero L f
  | succ n ih =>
    simp only [List.sum_range_succ]
    have hi := h2 n
    rw [hi.1, hg]
    have := ih.add (hi.2.mul (SimV.of_emb L false (g2 (ys.getD n (0, 0)).1)) (by simp only [Bool.and_false]))
    simpa only [Array.getD_eq_getD_getElem?, Bool.or_false, Bool.or_self] using this

/-- **The finish under the leaf map** (its tables pure). -/
theorem finSum_sim (L : Lam) (f : Bool) (T2 : Array (Array FE2)) (TA : Array (Array FEA)) (p : Pass)
    (hfin : ∀ tb ∈ p.fin.toList, ∀ i, (TA.getD tb.1 #[]).getD i 0 = emb ((T2.getD tb.1 #[]).getD i 0))
    (fsA : Array (ℕ × FEA)) (fs2 : Array (ℕ × FE2)) (h : SimE L f fsA fs2) :
    SimV L f (finSumG TA p fsA) (finSum2 T2 p fs2) := by
  rw [finSum2_eqG, c3_finSum, c3_finSum]
  refine h.wsum _ _ fun c ↦ ?_
  unfold finValG
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  suffices H : ∀ (l : List (ℕ × List ℕ)), (∀ tb ∈ l, tb ∈ p.fin.toList) → ∀ a : FE2,
      l.foldl (fun acc (tb : ℕ × List ℕ) ↦ acc * (TA.getD tb.1 #[]).getD (pext c tb.2) 0) (emb a) =
        emb (l.foldl (fun acc (tb : ℕ × List ℕ) ↦ acc * (T2.getD tb.1 #[]).getD (pext c tb.2) 0) a) by
    simpa only [Array.getD_eq_getD_getElem?, Array.foldl_toList, map_one] using H p.fin.toList (fun _ h ↦ h) 1
  intro l
  induction l with
  | nil => intro _ a; rfl
  | cons tb l ih =>
    intro hl a
    simp only [List.foldl_cons]
    rw [hfin tb (hl tb List.mem_cons_self), ← map_mul]
    exact ih (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) _

/-- **A pass under the leaf map.** -/
theorem pass_sim (L : Lam) (P : Pt2) (lim : ℕ → Bool) (TA : Array (Array FEA)) (T2 : Array (Array FE2))
    (FA : Array FEA) (F2 : Array FE2) (hF : SimF L lim FA F2) (p : Pass)
    (hfin : ∀ tb ∈ p.fin.toList, ∀ i, (TA.getD tb.1 #[]).getD i 0 = emb ((T2.getD tb.1 #[]).getD i 0))
    (fc : FCode) (hfc : p.fcode = some fc) (hok : (linCode lim fc).1 = true)
    (hlimb : (p.limbE.isNone || (linCode lim fc).2) = true) :
    SimV L true (runPassFG P.toA TA FA p) (runPassF2 L P T2 F2 p fc) := by
  have hr := runF_sim L lim FA F2 fc hF hok
  rw [linCode_fold] at hlimb
  unfold runPassFG runPassF2
  simp only [hfc]
  have hs := finSum_sim L _ T2 TA p hfin _ _ (runAuto_sim L _ P p.xs p.R _ _ hr.2)
  cases he : p.limbE with
  | none => exact hs.flag fun _ ↦ rfl
  | some e =>
    simp only [he, Option.isNone_some, Bool.false_or, Bool.not_eq_true', Bool.or_eq_false_iff] at hlimb
    rw [hlimb.2] at hs
    simp only [m2_fun, Pt2.toA, emb_getD]
    exact (hs.mul (limbVal_sim L _ _) (by simp only [Bool.and_true])).flag fun _ ↦ rfl

/-- The passes' fold under the leaf map. -/
theorem passes_sim (L : Lam) (P : Pt2) (PA : PtG FEA) (hPA : PA = P.toA) (lim : ℕ → Bool) (lt : Array ℕ)
    (TA : Array (Array FEA)) (T2 : Array (Array FE2)) (FA : Array FEA) (F2 : Array FE2) (hF : SimF L lim FA F2)
    (hT : ∀ t i, SimV L (lt.contains t) ((TA.getD t #[]).getD i 0) ((T2.getD t #[]).getD i 0)) (l : List Pass)
    (hl : ∀ p ∈ l, ∃ fc, p.fcode = some fc ∧ (linCode lim fc).1 = true ∧
      (p.limbE.isNone || (linCode lim fc).2) = true ∧ ∀ tb ∈ p.fin.toList, lt.contains tb.1 = false)
    (aA : FEA) (b : FE2) (ha : lam L aA = b) :
    l.foldlM (fun acc p ↦ do let pf ← p.fcode; pure (a2 acc (runPassF2 L P T2 F2 p pf))) b =
      some (lam L (l.foldl (fun acc p ↦ acc + runPassFG PA TA FA p) aA)) := by
  subst hPA
  induction l generalizing aA b with
  | nil => simp only [Option.pure_def, Option.bind_eq_bind, List.foldlM_nil, List.foldl_nil, ha]
  | cons p l ih =>
    obtain ⟨fc, hpf, hok, hlimb, hfin⟩ := hl p List.mem_cons_self
    have hs := pass_sim L P lim TA T2 FA F2 hF p (fun tb htb i ↦ (hT tb.1 i).2 (hfin tb htb)) fc hpf hok hlimb
    simp only [List.foldlM_cons, List.foldl_cons, hpf, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    exact ih (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)) _ _ (by rw [lam_add, ha, hs.1]; rfl)

/-- **The fast evaluator at `E2` is the leaf map of the evaluator over `FEA`** on a linear compiled evaluator. -/
theorem evalC2_sim (L : Lam) (c : Comp) (hlin : linOk c = true) (pt : List FE2) :
    evalC2 L c pt = some (lam L (evalCG c (ptA pt))) := by
  unfold linOk at hlin
  cases hlt : limbTabs c.tabs with
  | none => rw [hlt] at hlin; cases hlin
  | some lt =>
  cases hfc : c.fcode with
  | none => rw [hlt, hfc] at hlin; simp only [Array.getD_eq_getD_getElem?, Array.contains_eq_mem, Bool.false_and, Bool.false_eq_true] at hlin
  | some fc =>
  rw [hlt, hfc] at hlin
  simp only [Bool.and_eq_true, Array.all_eq_true'] at hlin
  obtain ⟨h0, hps⟩ := hlin
  have hT := tabs_sim L pt c.tabs lt (limbTabs_ok c.tabs lt hlt)
  have hF := flat_sim L c.tabs lt _ _ hT
  have hr := runF_sim L _ _ _ fc hF h0
  unfold evalC2 evalCG
  simp only [hfc, Option.bind_eq_bind, Option.bind_some, flatTabs2_eqG]
  rw [← Array.foldlM_toList, ← Array.foldl_toList]
  refine passes_sim L (Pt2.ofList pt) _ (ptA_ofList pt) _ lt _ _ _ _ hF hT c.passes.toList ?_ _ _ hr.1.1
  intro p hp
  have hp' := hps p (by simpa only [Array.mem_toList_iff] using hp)
  cases hpf : p.fcode with
  | none => rw [hpf] at hp'; simp only [Bool.false_eq_true, Array.contains_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Prod.forall, false_and] at hp'
  | some pf =>
    rw [hpf] at hp'
    simp only [Bool.and_eq_true, Array.all_eq_true'] at hp'
    obtain ⟨⟨hok, hlimb⟩, hfin⟩ := hp'
    refine ⟨pf, rfl, hok, hlimb, fun tb htb ↦ ?_⟩
    obtain ⟨t, bs⟩ := tb
    have := hfin (t, bs) (by simpa only [Array.mem_toList_iff] using htb)
    simpa only [Array.contains_eq_mem, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true] using this

end Lvm.Typed.KT
