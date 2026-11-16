-- New for lvm2 E2F (slice S1, E2F-QH2): the opening's `Quad Ext3` word leaf (`LvmE2QPinOpen.w6Leaf`) computes V's
-- word weight (`LvmDecideE2.wordWD`) times the part's coefficient.
import LvmE2QPinOpen
import LvmDecideE2

/-!
# The word leaf (`w6Leaf_spec`)

* `qmul_spec`: `(A, B)·(α, β)` in `E3[X]/(X² + tX + 1)`;
* `wordFactor_eq`: V's factor `z r + (1 + z)(1 + r)` is `(1 + z_re + r) + z_im X`;
* **`wordGo_spec`**, **`w6Leaf_spec`**: on a memo whose entries are correct (`Memo6Ok`), the leaf's two cells are the
  coordinates of `c · wordWD z X` (`X` the `E` cells `xb + l`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har

variable {c : Ctx} {M : Mem}

/-- A pair of cells as a `Quad Ext3` value. -/
def f6 (M : Mem) (p : Cell × Cell) : FE6 := ⟨p.1.val M, p.2.val M⟩

/-- An optional pair (`none` = `1`). -/
def f6o (M : Mem) : Option (Cell × Cell) → FE6
  | none => ⟨1, 0⟩
  | some p => f6 M p

theorem fe_two : (2 : FE) = 0 := CharTwo.two_eq_zero

theorem qmul_spec (t : FK) {z : Cell} (hz : z.val M = 0) (A B α β : Cell) :
    Hs c M (qmul t z A B α β) (fun r => r.1.val M = A.val M * α.val M + B.val M * β.val M ∧
      r.2.val M = A.val M * β.val M + B.val M * α.val M + FE.ofK t * (B.val M * β.val M)) := by
  unfold qmul
  refine hs_bind (hs_mulAdd _ _ _ _) fun q hq => hs_bind (hs_mulAdd _ _ _ _) fun re hre =>
    hs_bind (hs_lin _ _ _ _ _) fun tq htq => hs_bind (hs_mulAdd _ _ _ _) fun i1 hi1 =>
    hs_bind (hs_mulAdd _ _ _ _) fun im him => hs_pure ⟨?_, ?_⟩
  · rw [hre, hq, hz, add_zero]
  · rw [him, hi1, htq, hq, hz, add_zero]
    have : FE.ofK (t + 1) = FE.ofK t + 1 := by
      show FE.ofKRingHom (t + 1) = FE.ofKRingHom t + 1; rw [map_add, map_one]
    rw [this, show FE.ofK 0 = 0 from rfl, add_zero]
    linear_combination (B.val M * β.val M) * fe_two

/-- `FE6.mul` on coordinates. -/
theorem fe6_mul (a b : FE6) : FE6.mul a b =
    ⟨a.re * b.re + a.im * b.im, a.re * b.im + a.im * b.re + FE6.xE * (a.im * b.im)⟩ := by
  unfold FE6.mul
  simp only [FE6.mk.injEq, true_and]
  linear_combination (a.re * b.re + a.im * b.im) * fe_two

/-- V's factor `z·r + (1 + z)(1 + r)` in `Quad Ext3`. -/
def factorV (z : FE2) (r : FE) : FE6 :=
  let a := FE6.ofE2 z
  let f := FE6.mul a (FE6.ofE r)
  let g := FE6.mul ⟨1 + a.re, a.im⟩ ⟨1 + r, 0⟩
  ⟨f.re + g.re, f.im + g.im⟩

theorem wordFactor_eq (z : FE2) (r : FE) : factorV z r = ⟨r + FE.ofK z.re + 1, FE.ofK z.im⟩ := by
  simp only [factorV, fe6_mul, FE6.ofE2, FE6.ofE, FE6.mk.injEq]
  refine ⟨?_, ?_⟩
  · linear_combination (FE.ofK z.re * r) * fe_two
  · linear_combination (FE.ofK z.im * r) * fe_two

/-- The word product from coordinate `l` over the point `zs` at the basis values `X`. -/
def wordF (X : ℕ → FE) : ℕ → FE6 → List FE2 → FE6
  | _, acc, [] => acc
  | l, acc, z :: zs => wordF X (l + 1) (FE6.mul acc (factorV z (X l))) zs

theorem fe6_one_mul (b : FE6) : FE6.mul ⟨1, 0⟩ b = b := by
  rw [fe6_mul]; rcases b with ⟨b1, b2⟩; simp only [FE6.mk.injEq]; constructor <;> ring

/-- A `K` cell's value is the embedding of its word. -/
theorem kcell_val {x : Cell} (hx : x.ty = .K) : FE.ofK (x.val M).c₀ = x.val M := by
  rcases x with ⟨ty, n⟩; cases hx; rfl

/-- **The factor chain** computes `wordF` (the point's cells are `K` cells). -/
theorem wordGo_spec {F : FCtx} (hz : F.z.val M = 0) (xb : ℕ) (cs : List C2)
    (hK : ∀ x ∈ cs, x.re.ty = .K ∧ x.im.ty = .K) : ∀ (l : ℕ) (a : Option (Cell × Cell)),
    Hs c M (wordGo F xb l a cs) (fun r => f6o M r =
      wordF (fun i => M.e (xb + i)) l (f6o M a) (cs.map (C2.val M))) := by
  induction cs with
  | nil => intro l a; exact hs_pure rfl
  | cons x cs ih =>
    intro l a
    obtain ⟨hre, him⟩ := hK x (List.mem_cons_self ..)
    have ih' := ih fun y hy => hK y (List.mem_cons_of_mem _ hy)
    unfold wordGo
    refine hs_bind (hs_lin _ 1 1 _ x.re) fun α hα => ?_
    rw [Cell.val_E, show FE.ofK 1 = 1 from rfl, one_mul] at hα
    have hfac : factorV (x.val M) (M.e (xb + l)) = ⟨α.val M, x.im.val M⟩ := by
      rw [wordFactor_eq, hα]
      show (⟨_ + FE.ofK (x.re.val M).c₀ + 1, FE.ofK (x.im.val M).c₀⟩ : FE6) = _
      rw [kcell_val hre, kcell_val him]
    cases a with
    | none =>
      refine hs_bind (hs_pure (P := fun a' => a' = some (α, x.im)) rfl) fun a' ha' => ?_
      subst ha'
      refine hs_mono (ih' (l + 1) _) fun r hr => ?_
      rw [hr, List.map_cons, wordF, f6o, fe6_one_mul, hfac]; rfl
    | some p =>
      obtain ⟨A, B⟩ := p
      refine hs_bind (hs_bind (qmul_spec FK.x hz A B α x.im) fun q hq =>
        hs_pure (P := fun a' => ∃ q', a' = some q' ∧ q'.1.val M = A.val M * α.val M + B.val M * x.im.val M ∧
          q'.2.val M = A.val M * x.im.val M + B.val M * α.val M + FE.ofK FK.x * (B.val M * x.im.val M))
          ⟨q, rfl, hq⟩) fun a' ⟨q, hqa, hq1, hq2⟩ => ?_
      subst hqa
      refine hs_mono (ih' (l + 1) _) fun r hr => ?_
      rw [hr, List.map_cons, wordF, f6o, f6o, hfac, fe6_mul]
      simp only [f6, hq1, hq2, FE6.xE]

/-- The memo's entries hold their word products. -/
def Memo6Ok (M : Mem) (xb : ℕ) (m : Memo6) : Prop :=
  ∀ e ∈ m, f6 M e.2 = wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (e.1.map (C2.val M))

/-- `wordF` of a point extended by one coordinate: one more factor. -/
theorem wordF_concat (X : ℕ → FE) : ∀ (l : ℕ) (acc : FE6) (zs : List FE2) (z : FE2),
    wordF X l acc (zs ++ [z]) = FE6.mul (wordF X l acc zs) (factorV z (X (l + zs.length)))
  | l, acc, [], z => by rw [List.nil_append, wordF, wordF, wordF, List.length_nil, Nat.add_zero]
  | l, acc, y :: ys, z => by
    rw [List.cons_append, wordF, wordF, wordF_concat X (l + 1) _ ys z, List.length_cons,
      show l + 1 + ys.length = l + (ys.length + 1) by omega]

/-- **The prefix-memoised word product** (blob GT, `wordPre`): the first `n` coordinates' product, every prefix
memoised. -/
theorem wordPre_spec {F : FCtx} (hz : F.z.val M = 0) (xb : ℕ) (zl : List C2)
    (hK : ∀ x ∈ zl, x.re.ty = .K ∧ x.im.ty = .K) : ∀ (n : ℕ) (m : Memo6), n ≤ zl.length → Memo6Ok M xb m →
    Hs c M (wordPre F xb zl n m) (fun r => Memo6Ok M xb r.1 ∧
      f6o M r.2 = wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ ((zl.take n).map (C2.val M)))
  | 0, m, _, hm => hs_pure ⟨hm, by rw [List.take_zero, List.map_nil, wordF]; rfl⟩
  | n + 1, m, hn, hm => by
    rw [wordPre]
    split
    · rename_i e he
      have hmem := List.mem_of_find?_eq_some he
      have heq : e.1 = zl.take (n + 1) := by simpa using List.find?_some he
      exact hs_pure ⟨hm, by rw [f6o, hm e hmem, heq]⟩
    · have hnl : n < zl.length := by omega
      have hxm : zl.getD n default ∈ zl := by rw [List.getD_eq_getElem _ _ hnl]; exact List.getElem_mem hnl
      obtain ⟨hre, him⟩ := hK _ hxm
      refine hs_bind (wordPre_spec hz xb zl hK n m (by omega) hm) fun r hr0 => ?_
      obtain ⟨hm', hr⟩ := hr0
      refine hs_bind (hs_lin _ 1 1 _ _) fun α hα => ?_
      rw [Cell.val_E, show FE.ofK 1 = 1 from rfl, one_mul] at hα
      have hfac : factorV ((zl.getD n default).val M) (M.e (xb + n)) =
          ⟨α.val M, (zl.getD n default).im.val M⟩ := by
        rw [wordFactor_eq, hα]
        show (⟨_ + FE.ofK ((zl.getD n default).re.val M).c₀ + 1, FE.ofK ((zl.getD n default).im.val M).c₀⟩ : FE6) = _
        rw [kcell_val hre, kcell_val him]
      have htake : (zl.take (n + 1)).map (C2.val M) = (zl.take n).map (C2.val M) ++ [(zl.getD n default).val M] := by
        rw [List.take_succ, List.map_append, List.getElem?_eq_getElem hnl, Option.toList_some, List.map_singleton,
          List.getD_eq_getElem _ _ hnl]
      have hval : wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ ((zl.take (n + 1)).map (C2.val M)) =
          FE6.mul (f6o M r.2) ⟨α.val M, (zl.getD n default).im.val M⟩ := by
        rw [htake, wordF_concat, ← hr, List.length_map, List.length_take_of_le (by omega), Nat.zero_add, hfac]
      obtain ⟨m', o⟩ := r
      cases o with
      | none =>
        refine hs_bind (hs_pure (P := fun w => w = (α, (zl.getD n default).im)) rfl) fun w hw => ?_
        subst hw
        refine hs_pure ⟨fun e he => ?_, ?_⟩
        · rcases List.mem_cons.mp he with rfl | he'
          · rw [hval]; exact (fe6_one_mul _).symm
          · exact hm' e he'
        · rw [hval]; exact (fe6_one_mul _).symm
      | some p =>
        obtain ⟨A, B⟩ := p
        refine hs_bind (qmul_spec FK.x hz A B α (zl.getD n default).im) fun q hq0 => ?_
        obtain ⟨hq1, hq2⟩ := hq0
        have hq : f6 M q = FE6.mul (f6o M (some (A, B))) ⟨α.val M, (zl.getD n default).im.val M⟩ := by
          rw [f6o, fe6_mul]
          simp only [f6, hq1, hq2, FE6.xE]
        refine hs_pure ⟨fun e he => ?_, ?_⟩
        · rcases List.mem_cons.mp he with rfl | he'
          · rw [hval]; exact hq
          · exact hm' e he'
        · rw [f6o, hval]; exact hq

/-- **The memoised word product.** -/
theorem wordWG_spec {F : FCtx} (hz : F.z.val M = 0) (ho : F.o.val M = 1) (xb : ℕ) (zl : List C2)
    (hK : ∀ x ∈ zl, x.re.ty = .K ∧ x.im.ty = .K) (m : Memo6) (hm : Memo6Ok M xb m) :
    Hs c M (wordWG F xb zl m) (fun r => Memo6Ok M xb r.1 ∧
      f6 M r.2 = wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M))) := by
  unfold wordWG
  split
  · refine hs_bind (wordPre_spec hz xb zl hK zl.length m le_rfl hm) fun r hr0 => ?_
    obtain ⟨hm', hr⟩ := hr0
    obtain ⟨m', o⟩ := r
    refine hs_pure ⟨hm', ?_⟩
    rw [List.take_length] at hr
    rw [← hr]
    cases o with
    | none => show (⟨F.o.val M, F.z.val M⟩ : FE6) = ⟨1, 0⟩; rw [ho, hz]
    | some p => rfl
  · split
    · rename_i e he
      have hmem := List.mem_of_find?_eq_some he
      have heq : e.1 = zl := by simpa using List.find?_some he
      exact hs_pure ⟨hm, by rw [hm e hmem, heq]⟩
    · refine hs_bind (wordGo_spec hz xb zl hK 0 none) fun r hr => ?_
      rw [show f6o M none = ⟨1, 0⟩ from rfl] at hr
      have hw : f6 M (r.getD (F.o, F.z)) = wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M)) := by
        cases r with
        | none => rw [← hr]; show (⟨F.o.val M, F.z.val M⟩ : FE6) = _; rw [ho, hz]; rfl
        | some p => rw [← hr]; rfl
      refine hs_pure ⟨fun e he => ?_, hw⟩
      rcases List.mem_cons.mp he with rfl | he'
      · exact hw
      · exact hm e he'

/-- **The word leaf**: `c · wordW(z, X)` in `Quad Ext3` (`c`'s cells `K` cells). -/
theorem w6Leaf_spec {F : FCtx} (hz : F.z.val M = 0) (ho : F.o.val M = 1) (xb : ℕ) (cc : C2) (zl : List C2)
    (hc : cc.re.ty = .K ∧ cc.im.ty = .K) (hK : ∀ x ∈ zl, x.re.ty = .K ∧ x.im.ty = .K) (m : Memo6)
    (hm : Memo6Ok M xb m) :
    Hs c M (w6Leaf F xb cc zl m) (fun r => Memo6Ok M xb r.1 ∧
      f6 M r.2 = FE6.mul (wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M))) (FE6.ofE2 (cc.val M))) := by
  unfold w6Leaf
  refine hs_bind (wordWG_spec hz ho xb zl hK m hm) fun r ⟨hm', hr⟩ => ?_
  refine hs_bind (qmul_spec FK.x hz _ _ cc.re cc.im) fun q ⟨hq1, hq2⟩ => hs_pure ⟨hm', ?_⟩
  rw [← hr, fe6_mul]
  have h1 : FE.ofK (C2.val M cc).re = cc.re.val M := kcell_val hc.1
  have h2 : FE.ofK (C2.val M cc).im = cc.im.val M := kcell_val hc.2
  simp only [f6, FE6.ofE2, FE6.xE, hq1, hq2, h1, h2]

/-- `wordF` is V's fold. -/
theorem wordF_fold (X : ℕ → FE) : ∀ (zs : List FE2) (l : ℕ) (acc : FE6),
    wordF X l acc zs = (List.zip zs ((List.range zs.length).map fun i => X (l + i))).foldl
      (fun acc p => FE6.mul acc (factorV p.1 p.2)) acc
  | [], _, _ => rfl
  | z :: zs, l, acc => by
    rw [wordF, wordF_fold X zs (l + 1), List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.zip_cons_cons, List.foldl_cons, Nat.add_zero]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]; congr 1; omega

/-- **The word product is V's `wordWD`** at the basis point's values. -/
theorem wordF_eq_wordWD (X : ℕ → FE) (zs : List FE2) :
    wordF X 0 ⟨1, 0⟩ zs = wordWD zs ((List.range zs.length).map X) := by
  rw [wordF_fold, wordWD]
  simp only [Nat.zero_add]
  rfl

end Lvm.Q2
