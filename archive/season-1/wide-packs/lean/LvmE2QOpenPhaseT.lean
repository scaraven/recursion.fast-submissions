-- New for lvm2 E2-FT (E2F-C5): the small shape's tails at S2GF, circuit side: the tape's row claim's tail
-- (`LvmE2QPinOpen.rowTailG`) is V's `rowTailE2` (the switched target of the tail slices), and a `D` word half's tail
-- (`prepZ`'s `mass·zF`) is V's `tailDE2`.
import LvmQRingRowSem
import LvmE2QWSem
import LvmE2QPinOpen
import LvmDecideE2
import LvmQRingCrtL
import LvmQRingCrtSem
import LvmQAsmArith2Whir
import LvmE2QPinOpenG

-- ===== merged from `LvmE2QPinOpenSem` (VQ module merge: `LvmE2QPinOpenSem.lean` removed) =====
section
-- New for lvm2 E2F (slice S1, E2F-QH2): the opening's `Quad Ext3` word leaf (`LvmE2QPinOpen.w6Leaf`) computes V's
-- word weight (`LvmDecideE2.wordWD`) times the part's coefficient.

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
end
-- ===== end of `LvmE2QPinOpenSem` =====

-- ===== merged from `LvmQRingCrtLSem` (VQ module merge: `LvmQRingCrtLSem.lean` removed) =====
section
-- New for lvm2 S2GT (GT-C, GT-C2): the looped row-switch leaf's value (blob v4/GT, lever L1: `rowLeafGL`), on GT-L's
-- squaring-loop and `ν` lemmas (`LvmQRingCrtL`: `hs_frobLoop`, `fk_pow_two_pow_64`, `rowNuGL_ok`).

/-!
# The looped row leaf (`rowLeafGL`)

* **`frob_comp`**: the squaring loop's iteration `j < 64` is component `(j + 1) mod 64`: on a `K` cell,
  `a^(2^(j+1)) = a^(2^((j+1) mod 64))` (`fk_pow_two_pow_64`).
* **`comp_iter`**: iteration `j` of the component loop (`compIns`) holds `ν₀(j)·A + ν₁(j)·B`, `(A, B)` the
  `qm`-product of the factors' values read from the squaring loop (`cInit`, `cStep`, `cBody`: `compIns`'s rows).
* **`hs_accLoop`**, **`hs_accLoop2`**: the accumulation loops sum a row of an earlier loop (or `lRhoGL`'s `ν`-pairing)
  over its 64 iterations.
* **`hs_rowLeafGL`**: the leaf is `Σ_k ν₀·A_k + ν₁·B_k` over the components `k` (`crtL`), `ν` read through `nuAt` at
  iteration `(k + 63) mod 64`; **`rowLeafGL_weightN`**: with `RowNuOk` it is V's row weight `rowW`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Finset
open Lvm.Q1 (Ins Src tplOf)

variable {c : Ctx} {M : Mem}

/-- The squaring loop's iteration `j < 64` is component `(j + 1) mod 64`. -/
theorem frob_comp {a : Cell} (ha : a.ty = .K) {j : ℕ} (hj : j < 64) :
    a.val M ^ 2 ^ (j + 1) = a.val M ^ 2 ^ ((j + 1) % 64) := by
  rcases Nat.lt_or_ge (j + 1) 64 with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have h63 : j + 1 = 64 := by (clear * - j hj h; omega)
    rw [h63, Nat.mod_self, pow_zero, pow_one]
    rcases a with ⟨ty, n⟩
    cases ha
    show (FE.ofKRingHom (M.k n)) ^ 2 ^ 64 = FE.ofKRingHom (M.k n)
    rw [← map_pow, fk_pow_two_pow_64]

/-- The `K` version of `frob_comp`. -/
theorem fk_comp (a : FK) {j : ℕ} (hj : j < 64) : a ^ 2 ^ (j + 1) = a ^ 2 ^ ((j + 1) % 64) := by
  rcases Nat.lt_or_ge (j + 1) 64 with h | h
  · rw [Nat.mod_eq_of_lt h]
  · rw [show j + 1 = 64 by (clear * - j hj h; omega), Nat.mod_self, pow_zero, pow_one, fk_pow_two_pow_64]

/-- Summing over the iterations is summing over the components (`c(j) = (j + 1) mod 64` is a rotation). -/
theorem sum_rot64 (f : ℕ → FE) : ∑ j ∈ range 64, f ((j + 1) % 64) = ∑ k ∈ range 64, f k := by
  have h : ∑ j ∈ range 63, f ((j + 1) % 64) = ∑ j ∈ range 63, f (j + 1) :=
    Finset.sum_congr rfl fun j hj => by rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hj; (clear * - j this; omega))]
  rw [Finset.sum_range_succ, Finset.sum_range_succ' f, h]

/-! ## Loop rows -/

theorem hs_loop_rows (dims : List ℕ) (tpl : List LRow) :
    Hs c M (loop dims tpl) (fun o => o.dims = dims ∧ o.tpl = tpl ∧
      ∀ jf < 2 ^ dims.sum, ∀ t < tpl.length, LRel c M o jf t) :=
  fun _ h => ⟨rfl, rfl, fun _ hjf _ ht => loop_rel h hjf ht⟩

theorem row_muladd {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {j t : ℕ} (h : LRel c M o j t)
    (ht : t < ins.length) {τ : Ty} {a b d : Src} (hi : ins.getD t default = ⟨.muladd, τ, [a, b, d]⟩) :
    (o.cell t j).val M = a.toOpd.val M o j * b.toOpd.val M o j + d.toOpd.val M o j := by
  have hr : o.tpl.getD t default = ⟨.muladd, τ, [a.toOpd, b.toOpd, d.toOpd]⟩ := by
    rw [ho, Lvm.Q1.tplOf_getD ins ht, hi]; rfl
  simpa using lrel_muladd hr h

theorem row_lin {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {j t : ℕ} (h : LRel c M o j t)
    (ht : t < ins.length) {k k' : FK} {τ : Ty} {a b : Src} (hi : ins.getD t default = ⟨.lin k k', τ, [a, b]⟩) :
    (o.cell t j).val M = a.toOpd.val M o j + FE.ofK k * b.toOpd.val M o j + FE.ofK k' := by
  have hr : o.tpl.getD t default = ⟨.lin k k', τ, [a.toOpd, b.toOpd]⟩ := by
    rw [ho, Lvm.Q1.tplOf_getD ins ht, hi]; rfl
  simpa using lrel_lin hr h

theorem sv_loc (o : LoopOut) {j : ℕ} (hj : j < 2 ^ o.dims.sum) (k : ℕ) :
    (Src.loc k).toOpd.val M o j = (o.cell k j).val M := Opd.val_cur M o hj k

theorem sv_cell (o : LoopOut) (j : ℕ) (x : Cell) : (Src.ext x.addr).toOpd.val M o j = x.val M :=
  Cell.val_opd M o j x

/-- A loop of 64 iterations reads `nuAddr l` at iteration `j` as `nuAt l j`. -/
theorem val_nuAddr (o : LoopOut) (ho : o.dims = [6]) {j : ℕ} (hj : j < 64) (l : List Cell) :
    (Opd.abs (nuAddr l)).val M o j = (nuAt l j).val M :=
  Lvm.Q1.iterXv_ext1 M o ho (by simpa using hj) .E _ _

theorem sv_nu (o : LoopOut) (ho : o.dims = [6]) {j : ℕ} (hj : j < 64) (l : List Cell) :
    (Src.ext (nuAddr l)).toOpd.val M o j = (nuAt l j).val M := val_nuAddr o ho hj l

/-- A loop over an earlier loop's dimensions reads `F.addr i` at iteration `j` as `F`'s cell. -/
theorem sv_addr (P F : LoopOut) (hPd : P.dims = F.dims) {j : ℕ} (hj : j < 2 ^ F.dims.sum) (i : ℕ) :
    (Src.ext (F.addr i)).toOpd.val M P j = (F.cell i j).val M := Opd.val_abs_addr P F hPd hj i

theorem getD_pre {L R ins : List Ins} (h : ins = L ++ R) (i : ℕ) :
    ins.getD (L.length + i) default = R.getD i default := by
  subst h; rw [List.getD_append_right _ _ _ _ (by (clear * - L i; omega)), Nat.add_sub_cancel_left]

/-- **`qmIns`'s rows compute `qm`**: `re` at `t0 + 1`, `im` at `t0 + 4`. -/
theorem qm_rows {o : LoopOut} {ins : List Ins} (ho : o.tpl = tplOf ins) {j : ℕ} (hj : j < 2 ^ o.dims.sum)
    (hrel : ∀ t < ins.length, LRel c M o j t) {z : Cell} (hz : z.val M = 0) {tw A B α β : Src} {t0 : ℕ}
    (hseg : ∀ i < 5, ins.getD (t0 + i) default = (qmIns z tw t0 A B α β).getD i default)
    (hlen : t0 + 5 ≤ ins.length) :
    ((o.cell (t0 + 1) j).val M, (o.cell (t0 + 4) j).val M) =
      qm (tw.toOpd.val M o j) (A.toOpd.val M o j, B.toOpd.val M o j) (α.toOpd.val M o j, β.toOpd.val M o j) := by
  have r0 := row_muladd ho (hrel t0 (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 0 (by norm_num))
  have r1 := row_muladd ho (hrel (t0 + 1) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 1 (by norm_num))
  have r2 := row_muladd ho (hrel (t0 + 2) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 2 (by norm_num))
  have r3 := row_muladd ho (hrel (t0 + 3) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 3 (by norm_num))
  have r4 := row_muladd ho (hrel (t0 + 4) (by (clear * - t0 ins o j hlen; omega))) (by (clear * - t0 ins o j hlen; omega)) (hseg 4 (by norm_num))
  rw [sv_cell, hz, add_zero] at r0 r2
  rw [sv_loc o hj] at r1 r2 r3 r4
  simp only [qm]
  refine Prod.ext ?_ ?_
  · show (o.cell (t0 + 1) j).val M = _
    rw [r1, r0]
  · show (o.cell (t0 + 4) j).val M = _
    rw [r4, r3, r2, r0]
    ring

/-! ## `compIns`'s rows -/

/-- `compIns`'s first rows: factor `0`'s `α` (row `0`) and `β`. -/
def cInit (F : LoopOut) (xb : ℕ) : List Ins × Src × Src :=
  ([⟨.lin 1 1, .E, [.ext (ec xb).addr, .ext (F.addr (2 * 0))]⟩], .loc 0, .ext (F.addr (2 * 0 + 1)))

/-- `compIns`'s step for factor `l`: its `α` row, then `qmIns` (`re` at `ta + 2`, `im` at `ta + 5`). -/
def cStep (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (acc : List Ins × Src × Src) (l : ℕ) :
    List Ins × Src × Src :=
  (acc.1 ++ ⟨.lin 1 1, .E, [.ext (ec (xb + l)).addr, .ext (F.addr (2 * l))]⟩ ::
      qmIns z (.ext (F.addr (2 * n + if κ then 2 else 0))) (acc.1.length + 1) acc.2.1 acc.2.2 (.loc acc.1.length)
        (.ext (F.addr (2 * l + 1))),
    .loc (acc.1.length + 2), .loc (acc.1.length + 5))

/-- `compIns`'s factor rows after `m` steps. -/
def cFold (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (m : ℕ) : List Ins × Src × Src :=
  (List.range m).foldl (fun acc l => cStep F n κ xb z acc (l + 1)) (cInit F xb)

/-- `compIns`'s rows before the last two (the `κ` factor last). -/
def cBody (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) : List Ins × Src × Src :=
  if κ then
    ((cFold F n κ xb z (n - 1)).1 ++ qmIns z (.ext (F.addr (2 * n + if κ then 2 else 0)))
        (cFold F n κ xb z (n - 1)).1.length (cFold F n κ xb z (n - 1)).2.1 (cFold F n κ xb z (n - 1)).2.2
        (.ext (F.addr (2 * n))) (.ext (F.addr (2 * n + 1))),
      .loc ((cFold F n κ xb z (n - 1)).1.length + 1), .loc ((cFold F n κ xb z (n - 1)).1.length + 4))
  else cFold F n κ xb z (n - 1)

theorem compIns_eq (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (a0 a1 : Addr) :
    compIns F n κ xb z a0 a1 = (cBody F n κ xb z).1 ++
      [⟨.muladd, .E, [.ext a0, (cBody F n κ xb z).2.1, .ext z.addr]⟩,
        ⟨.muladd, .E, [.ext a1, (cBody F n κ xb z).2.2, .loc (cBody F n κ xb z).1.length]⟩] := by
  unfold compIns cBody cFold cStep cInit
  cases κ <;> rfl

theorem cFold_succ (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) (m : ℕ) :
    cFold F n κ xb z (m + 1) = cStep F n κ xb z (cFold F n κ xb z m) (m + 1) := by
  rw [cFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl

theorem cBody_pre (F : LoopOut) (n : ℕ) (κ : Bool) (xb : ℕ) (z : Cell) :
    ∃ R, (cBody F n κ xb z).1 = (cFold F n κ xb z (n - 1)).1 ++ R := by
  unfold cBody; cases κ
  · exact ⟨[], (List.append_nil _).symm⟩
  · exact ⟨_, rfl⟩

/-- Factor `l`'s value at iteration `j` of the squaring loop `F`: `(1 + a_l^(2^c) + x_l, b_l^(2^c))`. -/
def facF (M : Mem) (F : LoopOut) (xb j l : ℕ) : FE × FE :=
  (1 + (F.cell (2 * l) j).val M + M.e (xb + l), (F.cell (2 * l + 1) j).val M)

/-- **The factor rows**: after `m` steps, the chain holds the `qm`-product of factors `0 … m`. -/
theorem cFold_val {F P : LoopOut} {n : ℕ} {κ : Bool} {xb : ℕ} {z : Cell} {ins : List Ins} (hPt : P.tpl = tplOf ins)
    (hPd : P.dims = F.dims) {j : ℕ} (hj : j < 2 ^ F.dims.sum) (hrel : ∀ t < ins.length, LRel c M P j t)
    (hz : z.val M = 0) : ∀ m, (∃ R, ins = (cFold F n κ xb z m).1 ++ R) →
      (cFold F n κ xb z m).1.length = 1 + 6 * m ∧
      ((cFold F n κ xb z m).2.1.toOpd.val M P j, (cFold F n κ xb z m).2.2.toOpd.val M P j) =
        ((List.range m).map fun l => facF M F xb j (l + 1)).foldl
          (qm ((Src.ext (F.addr (2 * n + if κ then 2 else 0))).toOpd.val M P j)) (facF M F xb j 0)
  | 0, ⟨R, hR⟩ => by
    have hjP : j < 2 ^ P.dims.sum := by rw [hPd]; exact hj
    have hl0 : 0 < ins.length := by rw [hR]; simp [cFold, cInit]
    have r0 := row_lin hPt (hrel 0 hl0) hl0 (by rw [hR]; rfl)
    refine ⟨rfl, ?_⟩
    simp only [cFold, cInit, List.range_zero, List.map_nil, List.foldl_nil]
    rw [sv_loc P hjP, r0, sv_cell, sv_addr P F hPd hj, sv_addr P F hPd hj]
    simp only [facF, Cell.val_E, show FE.ofK 1 = 1 from rfl, one_mul, Nat.add_zero]
    exact Prod.ext (by dsimp only; ring) rfl
  | m + 1, ⟨R, hR⟩ => by
    have hjP : j < 2 ^ P.dims.sum := by rw [hPd]; exact hj
    rw [cFold_succ] at hR ⊢
    have hR' : ins = (cFold F n κ xb z m).1 ++ ((⟨.lin 1 1, .E, [.ext (ec (xb + (m + 1))).addr,
        .ext (F.addr (2 * (m + 1)))]⟩ :: qmIns z (.ext (F.addr (2 * n + if κ then 2 else 0)))
          ((cFold F n κ xb z m).1.length + 1) (cFold F n κ xb z m).2.1 (cFold F n κ xb z m).2.2
          (.loc (cFold F n κ xb z m).1.length) (.ext (F.addr (2 * (m + 1) + 1)))) ++ R) := by
      rw [hR]; simp only [cStep, List.append_assoc]
    obtain ⟨hl, hv⟩ := cFold_val hPt hPd hj hrel hz m ⟨_, hR'⟩
    have hlen : (cFold F n κ xb z m).1.length + 6 ≤ ins.length := by
      rw [hR', List.length_append, List.length_append]; simp [qmIns]
    have rα := row_lin hPt (hrel (cFold F n κ xb z m).1.length (by (clear * - F n κ xb z m ins P j hl hlen; omega))) (by (clear * - F n κ xb z m ins P j hl hlen; omega))
      (by rw [show (cFold F n κ xb z m).1.length = (cFold F n κ xb z m).1.length + 0 from rfl, getD_pre hR' 0]; rfl)
    have hq := qm_rows (z := z) (t0 := (cFold F n κ xb z m).1.length + 1) hPt hjP hrel hz (fun i hi => by
      rw [show (cFold F n κ xb z m).1.length + 1 + i = (cFold F n κ xb z m).1.length + (1 + i) by (clear * - F n κ xb z m i P ins j; omega),
        getD_pre hR' (1 + i), List.getD_append _ _ _ _ (by simp [qmIns]; (clear * - i F P n κ xb z ins j m hi; omega)), show 1 + i = i + 1 by (clear * - i F P n κ xb z ins j m; omega),
        List.getD_cons_succ]) (by (clear * - hlen; omega))
    refine ⟨by simp only [cStep, List.length_append, List.length_cons, qmIns, List.length_nil]; (clear * - F n κ xb z m P ins j hl; omega), ?_⟩
    simp only [cStep]
    rw [sv_loc P hjP, sv_loc P hjP, show (cFold F n κ xb z m).1.length + 2 = (cFold F n κ xb z m).1.length + 1 + 1 by
      (clear * - F n κ xb z m P ins j; omega), show (cFold F n κ xb z m).1.length + 5 = (cFold F n κ xb z m).1.length + 1 + 4 by (clear * - F n κ xb z m P ins j; omega), hq,
      List.range_succ, List.map_append, List.foldl_append, ← hv]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    congr 2
    · rw [sv_loc P hjP, rα, sv_cell]
      simp only [sv_addr P F hPd hj, Cell.val_E, show FE.ofK 1 = 1 from rfl, one_mul]
      ring
    · exact sv_addr P F hPd hj _

/-- **Iteration `j` of the component loop**: its last row is `ν₀(j)·A + ν₁(j)·B`, `(A, B)` the `qm`-product (twist
`F(2n + 2κ)`) of the factors `facF` and, with `κ`, `(F(2n), F(2n + 1))`. -/
theorem comp_iter {F P : LoopOut} {n : ℕ} {κ : Bool} {xb : ℕ} {z : Cell} {a0 a1 : Addr}
    (hPt : P.tpl = tplOf (compIns F n κ xb z a0 a1)) (hPd : P.dims = F.dims) {j : ℕ} (hj : j < 2 ^ F.dims.sum)
    (hrel : ∀ t < (compIns F n κ xb z a0 a1).length, LRel c M P j t) (hz : z.val M = 0) (hn : 1 ≤ n) :
    (P.cell ((compIns F n κ xb z a0 a1).length - 1) j).val M =
      (Src.ext a0).toOpd.val M P j * ((((List.range n).map (facF M F xb j)) ++
        (if κ then [((F.cell (2 * n) j).val M, (F.cell (2 * n + 1) j).val M)] else [])).foldl
          (qm ((F.cell (2 * n + if κ then 2 else 0) j).val M)) (1, 0)).1 +
      (Src.ext a1).toOpd.val M P j * ((((List.range n).map (facF M F xb j)) ++
        (if κ then [((F.cell (2 * n) j).val M, (F.cell (2 * n + 1) j).val M)] else [])).foldl
          (qm ((F.cell (2 * n + if κ then 2 else 0) j).val M)) (1, 0)).2 := by
  have hjP : j < 2 ^ P.dims.sum := by rw [hPd]; exact hj
  have he := compIns_eq F n κ xb z a0 a1
  have hlast : (compIns F n κ xb z a0 a1).length - 1 = (cBody F n κ xb z).1.length + 1 := by rw [he]; simp
  have hlen : (cBody F n κ xb z).1.length + 2 = (compIns F n κ xb z a0 a1).length := by rw [he]; simp
  have rA := row_muladd hPt (hrel (cBody F n κ xb z).1.length (by (clear * - F n κ xb z a0 a1 P j hlen; omega))) (by (clear * - F n κ xb z a0 a1 P j hlen; omega))
    (by rw [show (cBody F n κ xb z).1.length = (cBody F n κ xb z).1.length + 0 from rfl, getD_pre he 0]; rfl)
  have rB := row_muladd hPt (hrel ((cBody F n κ xb z).1.length + 1) (by (clear * - F n κ xb z a0 a1 P j hlen; omega))) (by (clear * - F n κ xb z a0 a1 P j hlen; omega))
    (by rw [getD_pre he 1]; rfl)
  rw [sv_cell, hz, add_zero] at rA
  rw [sv_loc P hjP, rA] at rB
  rw [hlast, rB]
  -- the chain's value before the last two rows
  have htw : (Src.ext (F.addr (2 * n + if κ then 2 else 0))).toOpd.val M P j =
      (F.cell (2 * n + if κ then 2 else 0) j).val M := sv_addr P F hPd hj _
  obtain ⟨R0, hR0⟩ := cBody_pre F n κ xb z
  have hpre : ∃ R, compIns F n κ xb z a0 a1 = (cFold F n κ xb z (n - 1)).1 ++ R :=
    ⟨R0 ++ _, by rw [he, hR0, List.append_assoc]⟩
  obtain ⟨-, hv⟩ := cFold_val (κ := κ) hPt hPd hj hrel hz (n - 1) hpre
  rw [htw] at hv
  have hr : List.range n = 0 :: (List.range (n - 1)).map (· + 1) := by
    rw [← List.range_succ_eq_map, Nat.sub_add_cancel hn]
  have hval : (((cBody F n κ xb z).2.1.toOpd.val M P j, (cBody F n κ xb z).2.2.toOpd.val M P j) : FE × FE) =
      (((List.range n).map (facF M F xb j)) ++
        (if κ then [((F.cell (2 * n) j).val M, (F.cell (2 * n + 1) j).val M)] else [])).foldl
          (qm ((F.cell (2 * n + if κ then 2 else 0) j).val M)) (1, 0) := by
    rw [hr, List.map_cons, List.cons_append, List.foldl_cons, qm_one, List.foldl_append, List.map_map]
    rw [show ((facF M F xb j) ∘ (· + 1)) = fun l => facF M F xb j (l + 1) from rfl, ← hv]
    cases κ
    · rfl
    · obtain ⟨R1, hR1⟩ : ∃ R1, compIns F n true xb z a0 a1 = (cFold F n true xb z (n - 1)).1 ++
          (qmIns z (.ext (F.addr (2 * n + if true then 2 else 0))) (cFold F n true xb z (n - 1)).1.length
            (cFold F n true xb z (n - 1)).2.1 (cFold F n true xb z (n - 1)).2.2 (.ext (F.addr (2 * n)))
            (.ext (F.addr (2 * n + 1))) ++ R1) :=
        ⟨_, by rw [he]; unfold cBody; simp only [ite_true, List.append_assoc]; exact rfl⟩
      have hq := qm_rows (z := z) (t0 := (cFold F n true xb z (n - 1)).1.length) hPt hjP hrel hz (fun i hi => by
        rw [getD_pre hR1 i, List.getD_append _ _ _ _ (by simp [qmIns]; (clear * - hi; omega))]) (by
          rw [hR1, List.length_append, List.length_append]; simp [qmIns])
      simp only [cBody, ite_true, List.foldl_cons, List.foldl_nil]
      rw [sv_loc P hjP, sv_loc P hjP, hq, sv_addr P F hPd hj, sv_addr P F hPd hj, sv_addr P F hPd hj]
      rfl
  rw [← hval]
  dsimp only
  ring

/-! ## The accumulation loop -/

/-- **The one-row accumulation loop** sums row `t` of a loop `P` over its 64 iterations. -/
theorem hs_accLoop (P : LoopOut) (hPd : P.dims = [6]) (t : ℕ) {z : Cell} (hz : z.val M = 0) :
    Hs c M (loopP [6] (tplOf [⟨.lin 1 0, .E, [.prev 0, .ext (P.addr t)]⟩]) (fun _ => z))
      (fun S => (S.cell 0 63).val M = ∑ j ∈ range 64, (P.cell t j).val M) := by
  intro p h
  have hrow : (tplOf [(⟨.lin 1 0, .E, [.prev 0, .ext (P.addr t)]⟩ : Ins)]).getD 0 default =
      ⟨.lin 1 0, .E, [.prev 0, .abs (P.addr t)]⟩ := rfl
  have key : ∀ j < 64, ((loopP [6] (tplOf [⟨.lin 1 0, .E, [.prev 0, .ext (P.addr t)]⟩]) (fun _ => z) p).1.cell 0 j).val M
      = ∑ i ∈ range (j + 1), (P.cell t i).val M := by
    intro j hj
    induction j with
    | zero =>
      have hr := lrel_lin hrow (loopP_rel h (show 0 < 2 ^ [6].sum by decide) (by simp [tplOf]))
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hr
      rw [hr, Opd.val_abs_addr _ P (by rw [hPd]; rfl) (by rw [hPd]; decide), show FE.ofK 1 = 1 from rfl,
        show FE.ofK 0 = 0 from rfl, one_mul, add_zero,
        loopP_prev_zero h (by simp [tplOf]) (fun e => by rw [hrow] at e; cases e), hz, zero_add, Finset.sum_range_one]
    | succ j ih =>
      have hj' : j + 1 < 2 ^ [6].sum := by simpa using hj
      have hr := lrel_lin hrow (loopP_rel h hj' (by simp [tplOf]))
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hr
      rw [hr, Opd.val_abs_addr _ P (by rw [hPd]; rfl) (by rw [hPd]; exact hj'), show FE.ofK 1 = 1 from rfl,
        show FE.ofK 0 = 0 from rfl, one_mul, add_zero, loopP_prev_succ M [6] _ _ p hj', ih (by (clear * - j hj; omega)),
        Finset.sum_range_succ _ (j + 1)]
  exact key 63 (by norm_num)

/-- **The two-row accumulation loop** (`lRhoGL`'s): `Σ_j ν₀(j)·D(0, j) + ν₁(j)·D(1, j)` over the 64 iterations, `ν`
read through `nuAt`. -/
theorem hs_accLoop2 (D : LoopOut) (hDd : D.dims = [6]) (l0 l1 : List Cell) {z : Cell} (hz : z.val M = 0) :
    Hs c M (loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z))
      (fun S => (S.cell 1 63).val M = ∑ j ∈ range 64, ((nuAt l0 j).val M * (D.cell 0 j).val M +
        (nuAt l1 j).val M * (D.cell 1 j).val M)) := by
  intro p h
  have h0 : (tplOf [(⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩ : Ins),
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]).getD 0 default =
      ⟨.muladd, .E, [.abs (nuAddr l0), .abs (D.addr 0), .prev 1]⟩ := rfl
  have h1 : (tplOf [(⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩ : Ins),
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]).getD 1 default =
      ⟨.muladd, .E, [.abs (nuAddr l1), .abs (D.addr 1), .cur 0]⟩ := rfl
  have hSd : (loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1.dims = [6] := rfl
  have step : ∀ j < 64, ((loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1.cell 1 j).val M =
      (nuAt l1 j).val M * (D.cell 1 j).val M + ((nuAt l0 j).val M * (D.cell 0 j).val M +
        (Opd.prev 1).val M (loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
          ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1 j) := by
    intro j hj
    have hj' : j < 2 ^ [6].sum := by simpa using hj
    have r0 := lrel_muladd h0 (loopP_rel h hj' (by simp [tplOf]))
    have r1 := lrel_muladd h1 (loopP_rel h hj' (by simp [tplOf]))
    simp only [List.getD_cons_zero, List.getD_cons_succ] at r0 r1
    rw [r1, Opd.val_cur M _ (by rw [hSd]; exact hj'), r0, val_nuAddr _ hSd hj, val_nuAddr _ hSd hj,
      Opd.val_abs_addr _ D (by rw [hSd, hDd]) (by rw [hDd]; exact hj'),
      Opd.val_abs_addr _ D (by rw [hSd, hDd]) (by rw [hDd]; exact hj')]
  have key : ∀ j < 64, ((loopP [6] (tplOf [⟨.muladd, .E, [.ext (nuAddr l0), .ext (D.addr 0), .prev 1]⟩,
      ⟨.muladd, .E, [.ext (nuAddr l1), .ext (D.addr 1), .loc 0]⟩]) (fun _ => z) p).1.cell 1 j).val M =
      ∑ i ∈ range (j + 1), ((nuAt l0 i).val M * (D.cell 0 i).val M + (nuAt l1 i).val M * (D.cell 1 i).val M) := by
    intro j hj
    induction j with
    | zero =>
      rw [step 0 hj, loopP_prev_zero h (by simp [tplOf]) (fun e => by rw [h1] at e; cases e), hz, add_zero,
        Finset.sum_range_one]
      ring
    | succ j ih =>
      rw [step (j + 1) hj, loopP_prev_succ M [6] _ _ p (by simpa using hj), ih (by (clear * - j hj; omega)),
        Finset.sum_range_succ _ (j + 1)]
      ring
  exact key 63 (by norm_num)

/-! ## The leaf -/

/-- Component `k` of a row leaf's factors: `(1 + z_re^(2^k) + x_l, z_im^(2^k))`, then `κ`'s `(κ_re^(2^k), κ_im^(2^k))`. -/
def crtF (M : Mem) (zs : List C2) (κ : Option C2) (xb k : ℕ) : List (FE × FE) :=
  (List.range zs.length).map (fun l => (1 + (zs.getD l default).re.val M ^ 2 ^ k + M.e (xb + l),
    (zs.getD l default).im.val M ^ 2 ^ k)) ++
  (match κ with
    | some cκ => [(cκ.re.val M ^ 2 ^ k, cκ.im.val M ^ 2 ^ k)]
    | none => [])

/-- Component `k` of a row leaf's product. -/
def crtL (M : Mem) (zs : List C2) (κ : Option C2) (xb k : ℕ) : FE × FE :=
  (crtF M zs κ xb k).foldl (qm (twK k)) (1, 0)

theorem flat2_getD (m : List Cell) (x : Cell) : ∀ (zs : List C2) {l : ℕ}, l < zs.length →
    (zs.flatMap (fun c => [c.re, c.im]) ++ m ++ [x]).getD (2 * l) default = (zs.getD l default).re ∧
      (zs.flatMap (fun c => [c.re, c.im]) ++ m ++ [x]).getD (2 * l + 1) default = (zs.getD l default).im
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => ⟨rfl, rfl⟩
  | _ :: zs, l + 1, h => by
    have := flat2_getD m x zs (l := l) (by simpa using h)
    rw [show 2 * (l + 1) = 2 * l + 1 + 1 by omega]
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ] using this

theorem flat2_getD_rest (m : List Cell) (x : Cell) (zs : List C2) (i : ℕ) :
    (zs.flatMap (fun c => [c.re, c.im]) ++ m ++ [x]).getD (2 * zs.length + i) default = (m ++ [x]).getD i default := by
  have hl : (zs.flatMap (fun c => [c.re, c.im])).length = 2 * zs.length := by
    induction zs with
    | nil => rfl
    | cons y zs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]; (clear * - zs; omega)
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by (clear * - zs i hl; omega)), hl, Nat.add_sub_cancel_left]

theorem getD_twist (m : List Cell) (x : Cell) {k : ℕ} (hm : m.length = k) : (m ++ [x]).getD k default = x := by
  rw [List.getD_append_right _ _ _ _ (by (clear * - m k hm; omega)), hm, Nat.sub_self]; rfl

/-- **The looped row leaf** (`rowLeafGL`): `Σ_k ν₀·A_k + ν₁·B_k`, `(A_k, B_k)` component `k`'s product (`crtL`), the
`ν` cells read through `nuAt` at iteration `(k + 63) mod 64`. -/
theorem hs_rowLeafGL (nu : RowNu) (zs : List C2) (κ : Option C2) (xb : ℕ) {z zk : Cell} (hz : z.val M = 0)
    (hzk : zk.val M = 0) (hne : zs ≠ []) (hK : ∀ x ∈ zs, x.re.ty = .K ∧ x.im.ty = .K)
    (hκ : ∀ cκ, κ = some cκ → cκ.re.ty = .K ∧ cκ.im.ty = .K) :
    Hs c M (rowLeafGL nu zs κ xb z zk) (fun r => r.val M = ∑ k ∈ range 64,
      ((nuAt nu.nu0 ((k + 63) % 64)).val M * (crtL M zs κ xb k).1 +
        (nuAt nu.nu1 ((k + 63) % 64)).val M * (crtL M zs κ xb k).2)) := by
  have hn : 1 ≤ zs.length := by
    rcases zs with _ | ⟨_, _⟩
    · exact absurd rfl hne
    · simp
  unfold rowLeafGL
  refine hs_bind (hs_const .K FK.x zk) fun x hx => ?_
  refine hs_bind (hs_frobLoop hzk _) fun F ⟨hFd, hFv⟩ => ?_
  refine hs_bind (hs_loop_rows _ _) fun P ⟨hPd, hPt, hPrel⟩ => ?_
  refine hs_bind (hs_accLoop P hPd _ hz) fun S hS => hs_pure ?_
  rw [hS]
  -- the factor cells of the squaring loop at iteration `j`, component `(j + 1) mod 64`
  have hfz : ∀ j < 64, ∀ l < zs.length,
      (F.cell (2 * l) j).val M = (zs.getD l default).re.val M ^ 2 ^ ((j + 1) % 64) ∧
      (F.cell (2 * l + 1) j).val M = (zs.getD l default).im.val M ^ 2 ^ ((j + 1) % 64) := by
    intro j hj l hl
    have hKl := hK (zs.getD l default) (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl)
    rw [hFv (2 * l) (by simp; (clear * - l zs κ j hl; omega)) j hj, hFv (2 * l + 1) (by simp; (clear * - l zs κ j hl; omega)) j hj, (flat2_getD _ _ zs hl).1,
      (flat2_getD _ _ zs hl).2, frob_comp hKl.1 hj, frob_comp hKl.2 hj]
    exact ⟨rfl, rfl⟩
  have htw : ∀ j < 64, (F.cell (2 * zs.length + if κ.isSome then 2 else 0) j).val M = twK ((j + 1) % 64) := by
    intro j hj
    rw [hFv _ (by cases κ <;> simp <;> (clear * - zs j; omega)) j hj, flat2_getD_rest, getD_twist]
    · rw [hx, twK, show FE.ofK FK.x ^ 2 ^ (j + 1) = FE.ofK (FK.x ^ 2 ^ (j + 1)) from
        (map_pow FE.ofKRingHom _ _).symm, fk_comp _ hj]
    · cases κ <;> rfl
  have hkap : ∀ j < 64, ∀ cκ, κ = some cκ →
      (F.cell (2 * zs.length) j).val M = cκ.re.val M ^ 2 ^ ((j + 1) % 64) ∧
      (F.cell (2 * zs.length + 1) j).val M = cκ.im.val M ^ 2 ^ ((j + 1) % 64) := by
    intro j hj cκ e
    subst e
    have h0 := flat2_getD_rest [cκ.re, cκ.im] x zs 0
    have h1 := flat2_getD_rest [cκ.re, cκ.im] x zs 1
    rw [Nat.add_zero] at h0
    rw [hFv _ (by simp; (clear * - zs j; omega)) j hj, hFv _ (by simp; (clear * - zs j; omega)) j hj]
    refine ⟨?_, ?_⟩
    · show (List.getD (zs.flatMap (fun c => [c.re, c.im]) ++ [cκ.re, cκ.im] ++ [x]) (2 * zs.length) default).val M ^ _ = _
      rw [h0]
      exact frob_comp (hκ cκ rfl).1 hj
    · show (List.getD (zs.flatMap (fun c => [c.re, c.im]) ++ [cκ.re, cκ.im] ++ [x]) (2 * zs.length + 1) default).val M ^
        _ = _
      rw [h1]
      exact frob_comp (hκ cκ rfl).2 hj
  -- iteration `j` is component `(j + 1) mod 64`
  have hit : ∀ j < 64,
      (P.cell ((compIns F zs.length κ.isSome xb z (nuAddr nu.nu0) (nuAddr nu.nu1)).length - 1) j).val M =
        (nuAt nu.nu0 j).val M * (crtL M zs κ xb ((j + 1) % 64)).1 +
          (nuAt nu.nu1 j).val M * (crtL M zs κ xb ((j + 1) % 64)).2 := by
    intro j hj
    have hj' : j < 2 ^ F.dims.sum := by rw [hFd]; simpa using hj
    have hPF : P.dims = F.dims := by rw [hPd, hFd]
    rw [comp_iter hPt hPF hj' (fun t ht => hPrel j (by simpa using hj) t (by simpa [tplOf] using ht)) hz hn,
      sv_nu P hPd hj, sv_nu P hPd hj, htw j hj]
    have hl : (List.range zs.length).map (facF M F xb j) ++
        (if κ.isSome then [((F.cell (2 * zs.length) j).val M, (F.cell (2 * zs.length + 1) j).val M)] else []) =
        crtF M zs κ xb ((j + 1) % 64) := by
      unfold crtF
      congr 1
      · refine List.map_congr_left fun l hl => ?_
        have h := hfz j hj l (List.mem_range.mp hl)
        simp only [facF, h.1, h.2]
      · cases κ with
        | none => rfl
        | some cκ =>
          have h := hkap j hj cκ rfl
          simp only [Option.isSome_some, ite_true, h.1, h.2]
    rw [hl]
    rfl
  rw [Finset.sum_congr rfl fun j hj => hit j (Finset.mem_range.mp hj)]
  rw [← sum_rot64 (fun k => (nuAt nu.nu0 ((k + 63) % 64)).val M * (crtL M zs κ xb k).1 +
    (nuAt nu.nu1 ((k + 63) % 64)).val M * (crtL M zs κ xb k).2)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e : ((j + 1) % 64 + 63) % 64 = j := by (clear * - j zs hj'; omega)
  simp only [e]

/-- **The looped row leaf is V's row weight** (big shape; `rowLeaf_weightN` for blob v4's `rowLeafGL`): with `ν`'s
cells standing for `eqR` as the loop reads them (`RowNuOk`), the claim point's `E2` coordinates `zs` (`K` cells) and
the basis point's first `|zs|` coordinates in the `E` cells `xb + l`. -/
theorem rowLeafGL_weightN (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) (zs : List C2) (hne : zs ≠ [])
    (hK : ∀ x ∈ zs, x.re.ty = .K ∧ x.im.ty = .K) (xb : ℕ) (xs : List FE) (hxl : xs.length = zs.length)
    (hx : ∀ l < zs.length, M.e (xb + l) = xs.getD l 0) {z zk : Cell} (hz : z.val M = 0) (hzk : zk.val M = 0) :
    Hs c M (rowLeafGL nu zs none xb z zk) (fun r => r.val M = rowW eqR (zs.map (C2.val M)) xs) := by
  refine hs_mono (hs_rowLeafGL nu zs none xb hz hzk hne hK (fun _ h => by cases h)) fun r hv => ?_
  rw [hv, rowW, sumE_eq, lsum_range,
    show ∑ j ∈ range 128, eqR.getD j 0 * (tensorWD (zs.map (C2.val M)) xs).getD j 0 =
      ∑ j ∈ range 128, (fun j => eqR.getD j 0) j * (tensorWD (zs.map (C2.val M)) xs).getD j 0 from rfl, weight_crt]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hf : ∀ L : List (FE2 × FE), L.foldl (fun P zr => qm (twK k) P (fct k zr)) (1, 0) =
      (L.map (fct k)).foldl (qm (twK k)) (1, 0) := fun L => (List.foldl_map ..).symm
  rw [(hnu.2 k hk').1, (hnu.2 k hk').2, phiA_tensorWD, hf]
  simp only [crtL, crtF, List.append_nil]
  have hzz : (List.zip (zs.map (C2.val M)) xs).map (fct k) = (List.range zs.length).map fun l =>
      (1 + (zs.getD l default).re.val M ^ 2 ^ k + M.e (xb + l), (zs.getD l default).im.val M ^ 2 ^ k) := by
    apply List.ext_getElem
    · simp [hxl]
    · intro l h1 _
      have hl : l < zs.length := by simpa [hxl] using h1
      have hKl := hK _ (List.getElem_mem hl)
      simp only [List.getElem_map, List.getElem_zip, List.getElem_range, fct]
      rw [hx l hl, List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by (clear * - l xs M zs xb hxl k hl; omega))]
      have hre : (zs[l]).re.val M = FE.ofK ((zs[l]).re.val M).c₀ := by
        rcases h : zs[l].re with ⟨ty, n⟩; rw [h] at hKl; obtain ⟨rfl, -⟩ := hKl; rfl
      have him : (zs[l]).im.val M = FE.ofK ((zs[l]).im.val M).c₀ := by
        rcases h : zs[l].im with ⟨ty, n⟩; rw [h] at hKl; obtain ⟨-, rfl⟩ := hKl; rfl
      have hp : ∀ a : FK, FE.ofK a ^ 2 ^ k = FE.ofK (a ^ 2 ^ k) := fun a => (map_pow FE.ofKRingHom a _).symm
      rw [hre, him, hp, hp]
      rfl
  rw [hzz]

end Lvm.Q2
end
-- ===== end of `LvmQRingCrtLSem` =====

-- ===== merged from `LvmE2QPinOpenF` (VQ module merge: `LvmE2QPinOpenF.lean` removed) =====
section
-- New for lvm2 E2-FT (E2F-QH5): `C_main`'s opening at S2GF (`LvmE2QPinOpen.openGF`) replays V's opening
-- (`LvmDecideE2.dOpenF`), big shape: what each circuit claim stands for (`FRel`), the batched basis with the `E2`
-- claim forms (`basisGF_spec`: word halves by `w6Leaf_spec`, row claims by `rowLeafGL_weightN`, `E3` claims by
-- `oneClaim_spec`), and the stacked opening's run (`openGF_big_run`, by the generic `stackG_run`).

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmE2QPinOpenFOff`, outside its import closure.)

/-!
# The opening at S2GF, big shape

* **`FRel M ν fc bc`**: the circuit claim `fc` (`FClaim`) stands for V's block claim `bc` on the stack of `ν`
  variables: an `E3` claim its `CClaim.val`; a half `h` of an `E2` sum claim `halfB ν h parts v` (`splitD`'s,
  `splitD_halfB`); a `D` half the half of the one-part sum on `⟨22, 0⟩`; a row claim the block claim with V's row
  weight `rowW eqR z` (`rowValD_weight`), its `ν` cells standing for `eqR` (`RowNuOk`).
* **`pfTermsB_spec`**, **`basisGF_spec`**: the terms of the big-shape preparations sum to `sc·onStack(x)`; the
  basis is `Σ_i s^i·onStack_i(x)`.
* **`openGF_big_run`**: on the claim list `(pinW, pin.value) :: bcs.map onStack` (the pin first, `pinW` its
  weight on the stack), V's `verifyStackedOpening` keeps `ok`, ends where the circuit's opening does, and leaves no
  message pending.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset

variable {c : Ctx} {M : Mem}

/-! ## V's claims of the circuit's forms -/

/-- Coordinate `h` of a `Quad Ext3` value. -/
def c6 (h : Bool) (a : FE6) : FE := if h then a.im else a.re

/-- An `E2` sum claim's parts as values. -/
def partsV (M : Mem) (parts : List (C2 × Placement × List C2)) : List (FE2 × Placement × List FE2) :=
  parts.map fun e => (e.1.val M, e.2.1, e.2.2.map (C2.val M))

/-- **Half `h` of an `E2` sum claim** on the stack of `ν` variables (`splitD`'s claims). -/
def halfB (ν : ℕ) (h : Bool) (parts : List (FE2 × Placement × List FE2)) (v : FE) : BlockClaim :=
  ⟨⟨ν, 0⟩, fun x => c6 h (sumW6D parts x), v⟩

theorem splitD_halfB (ν : ℕ) (parts : List (FE2 × Placement × List FE2)) (v : FE2) :
    splitD ν parts v = [halfB ν false parts (FE.ofK v.re), halfB ν true parts (FE.ofK v.im)] := rfl

/-- Both cells of an `E2` value are `K` cells. -/
def KC2 (x : C2) : Prop := x.re.ty = .K ∧ x.im.ty = .K

/-- **What a circuit claim stands for** (big shape) on the stack of `ν` variables. -/
def FRel (M : Mem) (ν : ℕ) : FClaim → BlockClaim → Prop
  | .e3 cc, bc => WF1 ν cc = true ∧ bc = (cc.val M).2
  | .half h parts v, bc => (∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
      e.2.1.variableCount ≤ ν) ∧ bc = halfB ν h (partsV M parts) (v.val M)
  | .dhalf h z v, bc => (∀ x ∈ z, KC2 x) ∧ z.length = 22 ∧ 22 ≤ ν ∧
      bc = halfB ν h [(1, ⟨22, 0⟩, z.map (C2.val M))] (v.val M)
  | .row blk z nu v, bc => ∃ eqR, RowNuOk M nu eqR ∧ z ≠ [] ∧ (∀ x ∈ z, KC2 x) ∧
      z.length = blk.variableCount ∧ blk.variableCount ≤ ν ∧ bc = ⟨blk, rowW eqR (z.map (C2.val M)), v.val M⟩
  | .drow z nu v, bc => ∃ eqR, RowNuOk M nu eqR ∧ z ≠ [] ∧ (∀ x ∈ z, KC2 x) ∧
      z.length = CMain.nu20 ∧ CMain.nu20 ≤ ν ∧ bc = ⟨⟨CMain.nu20, 0⟩, rowW eqR (z.map (C2.val M)), v.val M⟩

/-- The opening's shared cells hold their constants. -/
structure FCtxOk (M : Mem) (F : FCtx) : Prop where
  z : F.z.val M = 0
  o : F.o.val M = 1
  zk : F.zk.val M = 0
  zE : F.z.ty = .E
  oE : F.o.ty = .E
  o2 : F.o2.val M = 1
  o2K : KC2 F.o2
  z2 : F.z2.val M = 0

/-! ## Algebra of the word halves -/

/-- A coordinate of `sumW6D` is the sum of the parts' coordinates. -/
theorem c6_sumW6D (h : Bool) (parts : List (FE2 × Placement × List FE2)) (x : List FE) :
    c6 h (sumW6D parts x) = (parts.map fun e => c6 h (FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove x)))
      (wordWD e.2.2 (x.take e.2.1.variableCount)))).sum := by
  have hgen : ∀ (ps : List (FE2 × Placement × List FE2)) (acc : FE6),
      c6 h (ps.foldl (fun acc (e : FE2 × Placement × List FE2) =>
        let w := FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove x))) (wordWD e.2.2 (x.take e.2.1.variableCount))
        (⟨acc.re + w.re, acc.im + w.im⟩ : FE6)) acc) =
      c6 h acc + (ps.map fun e => c6 h (FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove x)))
        (wordWD e.2.2 (x.take e.2.1.variableCount)))).sum := by
    intro ps
    induction ps with
    | nil => intro acc; simp
    | cons e ps ih =>
      intro acc
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      cases h <;> simp only [c6, Bool.false_eq_true, if_false, if_true] <;> ring
  rw [sumW6D, hgen]
  cases h <;> simp [c6]

/-- A part's coordinate: the selector times the coordinate of `wordW·c`. -/
theorem c6_part (h : Bool) (cv : FE2) (e : FE) (W : FE6) :
    c6 h (FE6.mul (FE6.mul (FE6.ofE2 cv) (FE6.ofE e)) W) = e * c6 h (FE6.mul W (FE6.ofE2 cv)) := by
  simp only [fe6_mul, FE6.ofE2, FE6.ofE, c6]
  cases h <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem eqAbove_top (ν : ℕ) (y : List FE) (hy : y.length = ν) : (⟨ν, 0⟩ : Placement).eqAbove y = 1 := by
  simp [Placement.eqAbove, hy, selectorPoint, eqEval]

theorem xs_take (ν xb k : ℕ) (hk : k ≤ ν) : (xsOf M ν xb).take k = (List.range k).map fun i => M.e (xb + i) := by
  rw [xsOf, ← List.map_take, List.take_range, min_eq_left hk]

/-! ## The big-shape terms -/

/-- **The big-shape terms of a half's parts**: no pairs; they sum to `sc · Σ_parts eqAbove·coord(wordW·c)`. -/
theorem halfTermsB_spec {F : FCtx} (hF : FCtxOk M F) {ν xb : ℕ} (sc : Cell) (h : Bool) :
    ∀ (parts : List (C2 × Placement × List C2)) (m6 : Memo6),
      (∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
        e.2.1.variableCount ≤ ν) → Memo6Ok M xb m6 →
      Hs c M (halfTerms F ν xb sc h false parts m6) (fun r => Memo6Ok M xb r.1 ∧ r.2.1 = [] ∧
        (r.2.2.map (tval M (fun i => M.e (xb + i)) ν)).sum =
          sc.val M * (partsV M parts |>.map fun e => c6 h (FE6.mul (FE6.mul (FE6.ofE2 e.1)
            (FE6.ofE (e.2.1.eqAbove (xsOf M ν xb)))) (wordWD e.2.2 ((xsOf M ν xb).take e.2.1.variableCount)))).sum)
  | [], m6, _, hm => hs_pure ⟨hm, rfl, by simp [partsV]⟩
  | (cv, blk, zl) :: ps, m6, hp, hm => by
    obtain ⟨hcK, hzK, hzl, hvc⟩ := hp _ (List.mem_cons_self ..)
    unfold halfTerms
    refine hs_bind (w6Leaf_spec hF.z hF.o xb cv zl hcK hzK m6 hm) fun r ⟨hm', hr⟩ => ?_
    refine hs_bind (halfTermsB_spec hF sc h ps r.1 (fun e he => hp e (List.mem_cons_of_mem _ he)) hm')
      fun rs ⟨hm'', hn, hs⟩ => ?_
    simp only [Bool.false_eq_true, if_false]
    refine hs_pure ⟨hm'', hn, ?_⟩
    rw [List.map_cons, List.sum_cons, hs]
    simp only [partsV, List.map_cons, List.sum_cons]
    have hlf : (if h then r.2.2 else r.2.1).val M =
        c6 h (FE6.mul (wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M))) (FE6.ofE2 (cv.val M))) := by
      rw [← hr]; cases h <;> rfl
    have hW : wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M)) =
        wordWD (zl.map (C2.val M)) ((xsOf M ν xb).take blk.variableCount) := by
      rw [wordF_eq_wordWD, xs_take ν xb _ hvc, List.length_map, hzl]
    have hE : kprod (fun i => M.e (xb + i)) ν (keyOf (selbit blk) ν blk.variableCount) = blk.eqAbove (xsOf M ν xb) := by
      rw [kprod_keyOf, eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [xs_length]; exact hvc)
        (fun i hi => xs_getD (by rwa [xs_length] at hi)), xs_length]
    simp only [tval]
    rw [hE, hlf, hW, c6_part]
    ring

/-! ## The opening, big shape -/

/-! ## V's `dOpenF`, big shape -/

/-- **What a circuit claim stands for in V's list** (`dOpenF`'s `(com, claim, tail)`): on `C_main`, `FRel`. -/
def FRelT (M : Mem) (ν : ℕ) (fc : FClaim) (cl : Com × BlockClaim × FE) : Prop := cl.1 = .main ∧ FRel M ν fc cl.2.1

theorem relT_main {ν : ℕ} : ∀ {cs : List FClaim} {cls : List (Com × BlockClaim × FE)},
    List.Forall₂ (FRelT M ν) cs cls → cls.all (·.1 == .main) = true ∧
      List.Forall₂ (FRel M ν) cs ((cls.filter (·.1 == .main)).map (·.2.1))
  | [], [], _ => ⟨rfl, .nil⟩
  | _ :: _, cl :: _, .cons ⟨hm, hr⟩ hrs => by
    obtain ⟨h1, h2⟩ := relT_main hrs
    refine ⟨by simp only [List.all_cons, hm, h1]; rfl, ?_⟩
    rw [List.filter_cons_of_pos (by simp [hm]), List.map_cons]
    exact .cons hr h2

end Lvm.Q2
end
-- ===== end of `LvmE2QPinOpenF` =====

-- ===== merged from `LvmE2QPinOpenZ` (VQ module merge: `LvmE2QPinOpenZ.lean` removed) =====
section
-- New for lvm2 E2-FT (E2F-QH5): the small shape's `E2` claims at S2GF: V_S's small claim (`onStackZB` =
-- `onStackZBN 23`) of a word half on regular blocks (`halfB_small`: the parts moved down), of a `D` word half
-- (`halfD_small`: `κ` times the half at `D`'s small point, through `LvmE2QPinOpenG.zWR_D` over `Quad Ext3`), of a
-- regular row claim (`onStackZB_reg`), at the rotated point.

/-!
# The small shape's `E2` claims

* `R6 = Quad Ext3` as a ring (`Quad FE x`), `q6 : FE6 → R6` multiplicative (`q6_mul`), `e2q : E2 → R6`,
  `q6_wordWD`: V's word weight is `pR` over `R6`; `L6 h`: coordinate `h` as an `E3`-linear map;
* **`halfB_small`**: on regular parts, the small claim is the sum of the parts' claims moved down, at `x^σ`;
* **`halfD_small`**: on `D` (one part, coefficient `1`), the small claim is `eqAbove_D(x^σ)` times coordinate `h` of
  `wordW(dzE z, x^σ)·κ(z)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape

/-! ## `Quad Ext3` as a ring -/

/-- `Quad Ext3 = E3[X]/(X² + xX + 1)` as a commutative ring. -/
abbrev R6 := Quad FE FE6.xE

/-- A `FE6` value in the ring. -/
def q6 (a : FE6) : R6 := ⟨a.re, a.im⟩

theorem q6_mul (a b : FE6) : q6 (FE6.mul a b) = q6 a * q6 b := by
  rw [fe6_mul]
  apply QuadraticAlgebra.ext
  · rw [Quad.re_mul]; rfl
  · rw [Quad.im_mul]
    show a.re * b.im + a.im * b.re + FE6.xE * (a.im * b.im) = a.re * b.im + a.im * b.re + FE6.xE * a.im * b.im
    ring

/-- `E2 → Quad Ext3`. -/
def e2q (z : FE2) : R6 := q6 (FE6.ofE2 z)

theorem e2q_mul (a b : FE2) : e2q (a * b) = e2q a * e2q b := by
  apply QuadraticAlgebra.ext
  · rw [Quad.re_mul]
    show FE.ofK (a * b).re = FE.ofK a.re * FE.ofK b.re + FE.ofK a.im * FE.ofK b.im
    rw [FE2.mul_def]
    show FE.ofKRingHom _ = FE.ofKRingHom _ * FE.ofKRingHom _ + FE.ofKRingHom _ * FE.ofKRingHom _
    rw [map_add, map_mul, map_mul]
  · rw [Quad.im_mul]
    show FE.ofK (a * b).im = FE.ofK a.re * FE.ofK b.im + FE.ofK a.im * FE.ofK b.re + FE6.xE * FE.ofK a.im * FE.ofK b.im
    rw [FE2.mul_def]
    show FE.ofKRingHom _ = FE.ofKRingHom _ * FE.ofKRingHom _ + FE.ofKRingHom _ * FE.ofKRingHom _ +
      FE.ofKRingHom FK.x * FE.ofKRingHom _ * FE.ofKRingHom _
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul]
    ring

theorem e2q_one : e2q 1 = 1 := by apply QuadraticAlgebra.ext <;> rfl

theorem e2q_zero : e2q 0 = 0 := by apply QuadraticAlgebra.ext <;> rfl

theorem e2q_add (a b : FE2) : e2q (a + b) = e2q a + e2q b := by
  apply QuadraticAlgebra.ext
  · show FE.ofKRingHom (a.re + b.re) = _; rw [map_add]; rfl
  · show FE.ofKRingHom (a.im + b.im) = _; rw [map_add]; rfl

theorem q6_ofE (e : FE) : q6 (FE6.ofE e) = algebraMap FE R6 e := rfl

theorem q6_factorV (z : FE2) (r : FE) : q6 (factorV z r) = fR (e2q z) r := by
  rw [wordFactor_eq]
  apply QuadraticAlgebra.ext
  · show r + FE.ofK z.re + 1 = (1 + e2q z + algebraMap FE R6 r).re
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_one, QuadraticAlgebra.algebraMap_eq]
    show _ = 1 + FE.ofK z.re + r
    ring
  · show FE.ofK z.im = (1 + e2q z + algebraMap FE R6 r).im
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_one, QuadraticAlgebra.algebraMap_eq]
    show _ = 0 + FE.ofK z.im + 0
    ring

/-- **V's word weight is `pR` over `Quad Ext3`.** -/
theorem q6_wordWD : ∀ (z : List FE2) (y : List FE), q6 (wordWD z y) = pR (z.map e2q) y := by
  have hgen : ∀ (z : List FE2) (y : List FE) (acc : FE6),
      q6 ((List.zip z y).foldl (fun acc (p : FE2 × FE) => FE6.mul acc (factorV p.1 p.2)) acc) =
        q6 acc * pR (z.map e2q) y := by
    intro z
    induction z with
    | nil => intro y acc; simp [pR]
    | cons a z ih =>
      intro y acc
      cases y with
      | nil => simp [pR]
      | cons b y => rw [List.zip_cons_cons, List.foldl_cons, ih, q6_mul, q6_factorV, List.map_cons, pR_cons]; ring
  intro z y
  have e : wordWD z y = (List.zip z y).foldl (fun acc (p : FE2 × FE) => FE6.mul acc (factorV p.1 p.2)) ⟨1, 0⟩ := rfl
  rw [e, hgen, show q6 ⟨1, 0⟩ = 1 from rfl, one_mul]

/-- Coordinate `h` as an `E3`-linear map. -/
def L6 (h : Bool) : R6 →ₗ[FE] FE where
  toFun q := if h then q.im else q.re
  map_add' a b := by cases h <;> simp
  map_smul' c a := by cases h <;> simp [smul_eq_mul]

theorem c6_eq (h : Bool) (a : FE6) : c6 h a = L6 h (q6 a) := by cases h <;> rfl

/-! ## Word halves on regular parts -/

/-- A part of a half as a block claim: `coord_h(wordW(z, ·)·c)` on its block. -/
def partH (h : Bool) (e : FE2 × Placement × List FE2) : BlockClaim :=
  ⟨e.2.1, fun y => c6 h (FE6.mul (wordWD e.2.2 y) (FE6.ofE2 e.1)), 0⟩

theorem halfB_parts (h : Bool) (P : List (FE2 × Placement × List FE2)) (v : FE) (y : List FE)
    (hy : y.length = CMain.nu20) :
    (halfB CMain.nu20 h P v).onStack.1 y = (P.map fun e => 1 * (partH h e).onStack.1 y).sum := by
  simp only [BlockClaim.onStack, halfB]
  rw [eqAbove_top _ y hy, one_mul, List.take_of_length_le (by omega), c6_sumW6D]
  exact congrArg List.sum (List.map_congr_left fun e _ => by rw [c6_part, one_mul]; rfl)

/-- **The small claim of a half on regular parts**: its parts moved down, at `x^σ`. -/
theorem halfB_small (h : Bool) (P : List (FE2 × Placement × List FE2)) (hP : ∀ e ∈ P, RegP e.2.1) (v t : FE)
    (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB (halfB CMain.nu20 h P v) t).1 x = (P.map fun e => (shiftB (partH h e)).onStack.1 (rotZ x)).sum := by
  have e1 : (onStackZB (halfB CMain.nu20 h P v) t).1 x = zW x (halfB CMain.nu20 h P v).onStack.1 := by
    unfold zW onStackZB
    rw [show (halfB CMain.nu20 h P v).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  rw [e1, zW_congr x hx (halfB_parts h P v), zW_sum]
  exact congrArg List.sum (List.map_congr_left fun e he => by
    rw [one_mul, zW_eq_zb (partH h e) 0 (hP e he) x hx, onStackZB_reg _ 0 (hP e he) x hx])

/-! ## `D` word halves -/

/-- `D`'s small point over `E2`: `z₀…z₁₇ ‖ z₂₀ z₂₁ ‖ 0 0`. -/
def dzE (z : List FE2) : List FE2 := z.take 18 ++ [z.getD 20 0, z.getD 21 0, 0, 0]

/-- `D`'s scale over `E2`: `(1 + z₁₈)(1 + z₁₉)`. -/
def kapE (z : List FE2) : FE2 := (1 + z.getD 18 0) * (1 + z.getD 19 0)

theorem getD_map_e2q (z : List FE2) (i : ℕ) : (z.map e2q).getD i 0 = e2q (z.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases z[i]? with
  | none => exact e2q_zero.symm
  | some a => rfl

theorem kapR_map (z : List FE2) : kapR (z.map e2q) = e2q (kapE z) := by
  rw [kapR, kapE, e2q_mul, e2q_add, e2q_add, e2q_one, getD_map_e2q, getD_map_e2q]

theorem dzR_map (z : List FE2) : dzR (z.map e2q) = (dzE z).map e2q := by
  rw [dzR, dzE, List.map_append, List.map_take, getD_map_e2q, getD_map_e2q]
  simp [e2q_zero]

/-- **The small claim of a `D` half** (one part on `⟨22, 0⟩`, coefficient `1`): `eqAbove_D(x^σ)` times coordinate
`h` of `wordW(dzE z, x^σ)·κ(z)`. -/
theorem halfD_small (h : Bool) (z : List FE2) (hz : z.length = 22) (v t : FE) (x : List FE)
    (hx : x.length = CMain.nu20) :
    (onStackZB (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v) t).1 x =
      (⟨22, 0⟩ : Placement).eqAbove (rotZ x) *
        c6 h (FE6.mul (wordWD (dzE z) ((rotZ x).take 22)) (FE6.ofE2 (kapE z))) := by
  have e1 : (onStackZB (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v) t).1 x =
      zW x (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v).onStack.1 := by
    unfold zW onStackZB
    rw [show (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  have hw : ∀ y : List FE, y.length = CMain.nu20 → (halfB CMain.nu20 h [(1, ⟨22, 0⟩, z)] v).onStack.1 y =
      L6 h (algebraMap FE R6 ((⟨22, 0⟩ : Placement).eqAbove y) * pR (z.map e2q) (y.take 22)) := by
    intro y hy
    rw [halfB_parts h _ v y hy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    simp only [partH, BlockClaim.onStack]
    have hs : ∀ (e : FE) (q : R6), e * L6 h q = L6 h (algebraMap FE R6 e * q) := fun e q => by
      rw [← Algebra.smul_def, (L6 h).map_smul, smul_eq_mul]
    rw [c6_eq, q6_mul, show q6 (FE6.ofE2 1) = 1 from e2q_one, mul_one, q6_wordWD, hs]
  rw [e1, zW_congr x hx hw, zW_lin, zWR_D _ (by simp [hz]) x hx, kapR_map, dzR_map, ← q6_wordWD]
  rw [show algebraMap FE R6 ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) * (e2q (kapE z) *
      q6 (wordWD (dzE z) ((rotZ x).take 22))) = ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) •
        q6 (FE6.mul (wordWD (dzE z) ((rotZ x).take 22)) (FE6.ofE2 (kapE z))) by
    rw [Algebra.smul_def, q6_mul]; unfold e2q; ring, (L6 h).map_smul, smul_eq_mul, ← c6_eq]

/-! ## The row claim by components -/

/-- Component `k`'s ring: `E3[X]/(X² + x^(2^k) X + 1)`. -/
abbrev Rk (k : ℕ) := Quad FE (twK k)

/-- A pair in component `k`'s ring. -/
def qk (k : ℕ) (p : FE × FE) : Rk k := ⟨p.1, p.2⟩

/-- `E2 → ` component `k`: `a ↦ σ^k(a_re) + σ^k(a_im) X`. -/
def zk (k : ℕ) (a : FE2) : Rk k := ⟨FE.ofK (a.re ^ 2 ^ k), FE.ofK (a.im ^ 2 ^ k)⟩

theorem qk_qm (k : ℕ) (a b : FE × FE) : qk k (qm (twK k) a b) = qk k a * qk k b := by
  apply QuadraticAlgebra.ext
  · rw [Quad.re_mul]; rfl
  · rw [Quad.im_mul]
    show (qm (twK k) a b).2 = a.1 * b.2 + a.2 * b.1 + twK k * a.2 * b.2
    simp only [qm]
    ring

theorem qk_fct (k : ℕ) (zr : FE2 × FE) : qk k (fct k zr) = fR (zk k zr.1) zr.2 := by
  apply QuadraticAlgebra.ext
  · show 1 + FE.ofK (zr.1.re ^ 2 ^ k) + zr.2 = (1 + zk k zr.1 + algebraMap FE (Rk k) zr.2).re
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_one, QuadraticAlgebra.algebraMap_eq]; rfl
  · show FE.ofK (zr.1.im ^ 2 ^ k) = (1 + zk k zr.1 + algebraMap FE (Rk k) zr.2).im
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_one, QuadraticAlgebra.algebraMap_eq]
    show _ = 0 + FE.ofK (zr.1.im ^ 2 ^ k) + 0
    ring

theorem zk_mul (k : ℕ) (a b : FE2) : zk k (a * b) = zk k a * zk k b := by
  have h := crd_mul_frob k a b
  simp only [crd, Bool.false_eq_true, if_false, if_true] at h
  rw [show zk k (a * b) = qk k (FE.ofK ((a * b).re ^ 2 ^ k), FE.ofK ((a * b).im ^ 2 ^ k)) from rfl, h, qk_qm]
  rfl

theorem zk_add (k : ℕ) (a b : FE2) : zk k (a + b) = zk k a + zk k b := by
  apply QuadraticAlgebra.ext
  · show FE.ofK ((a.re + b.re) ^ 2 ^ k) = FE.ofK (a.re ^ 2 ^ k) + FE.ofK (b.re ^ 2 ^ k)
    rw [← frobK_apply, map_add, frobK_apply, frobK_apply]
    exact map_add FE.ofKRingHom _ _
  · show FE.ofK ((a.im + b.im) ^ 2 ^ k) = FE.ofK (a.im ^ 2 ^ k) + FE.ofK (b.im ^ 2 ^ k)
    rw [← frobK_apply, map_add, frobK_apply, frobK_apply]
    exact map_add FE.ofKRingHom _ _

theorem zk_one (k : ℕ) : zk k 1 = 1 := by
  apply QuadraticAlgebra.ext
  · show FE.ofK ((1 : FK) ^ 2 ^ k) = 1; rw [one_pow]; rfl
  · show FE.ofK ((0 : FK) ^ 2 ^ k) = 0; rw [zero_pow (pow_ne_zero k two_ne_zero)]; rfl

theorem zk_zero (k : ℕ) : zk k 0 = 0 := by
  apply QuadraticAlgebra.ext <;>
  · show FE.ofK ((0 : FK) ^ 2 ^ k) = 0; rw [zero_pow (pow_ne_zero k two_ne_zero)]; rfl

/-- **Component `k` of V's tensor coordinates is `pR` over component `k`'s ring.** -/
theorem qk_phiA (k : ℕ) (z : List FE2) (y : List FE) : qk k (phiA k (tensorWD z y)) = pR (z.map (zk k)) y := by
  rw [phiA_tensorWD]
  have hgen : ∀ (z : List FE2) (y : List FE) (P : FE × FE),
      qk k ((List.zip z y).foldl (fun P zr => qm (twK k) P (fct k zr)) P) = qk k P * pR (z.map (zk k)) y := by
    intro z
    induction z with
    | nil => intro y P; simp [pR]
    | cons a z ih =>
      intro y P
      cases y with
      | nil => simp [pR]
      | cons b y => rw [List.zip_cons_cons, List.foldl_cons, ih, qk_qm, qk_fct, List.map_cons, pR_cons]; ring
  rw [hgen, show qk k (1, 0) = 1 from rfl, one_mul]

/-- The `ν`-pairing of component `k` as an `E3`-linear map. -/
def Lk (ρ : ℕ → FE) (k : ℕ) : Rk k →ₗ[FE] FE where
  toFun q := nuH ρ false k * q.re + nuH ρ true k * q.im
  map_add' a b := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
  map_smul' c a := by simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul, RingHom.id_apply]; ring

/-- **V's row weight by components**: `rowW eqR z y = Σ_k L_k(pR (σ^k z) y)`. -/
theorem rowW_comp (eqR : List FE) (z : List FE2) (y : List FE) :
    rowW eqR z y = ∑ k ∈ Finset.range 64, Lk (fun j => eqR.getD j 0) k (pR (z.map (zk k)) y) := by
  rw [rowW, sumE_eq, lsum_range, show ∑ j ∈ Finset.range 128, eqR.getD j 0 * (tensorWD z y).getD j 0 =
    ∑ j ∈ Finset.range 128, (fun j => eqR.getD j 0) j * (tensorWD z y).getD j 0 from rfl, weight_crt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← qk_phiA]
  rfl

theorem zW_fsum1 (x : List FE) (n : ℕ) (g : ℕ → List FE → FE) :
    zW x (fun y ↦ ∑ i ∈ Finset.range n, g i y) = ∑ i ∈ Finset.range n, zW x (g i) := by
  have := zW_fsum x n (fun _ => 1) g
  simp only [one_mul] at this
  exact this

theorem pR_last {R : Type} [CommRing R] [Algebra FE R] (z : List R) (hz : z.length = 23) (hz22 : z.getD 22 0 = 0)
    (y : List FE) (hy : y.length = 23) :
    pR z y = algebraMap FE R ((⟨22, 0⟩ : Placement).eqAbove y) * pR (z.take 22) (y.take 22) := by
  conv_lhs => rw [← List.take_append_drop 22 z, ← List.take_append_drop 22 y]
  have hz' : z.drop 22 = [0] := by
    apply List.ext_getElem (by simp [hz])
    intro i h1 _
    have : i = 0 := by simp [hz] at h1; omega
    subst this
    rw [List.getElem_drop]
    simpa [List.getD_eq_getElem?_getD, hz] using hz22
  obtain ⟨y22, hy'⟩ : ∃ y22, y.drop 22 = [y22] := by
    rcases hd : y.drop 22 with _ | ⟨a, _ | ⟨b, l⟩⟩
    · have := congrArg List.length hd; simp [hy] at this
    · exact ⟨a, rfl⟩
    · have := congrArg List.length hd; simp [hy] at this
  have hyl : y = y.take 22 ++ [y22] := by rw [← hy', List.take_append_drop]
  rw [pR_append (by simp [hz, hy]), hz', hy', pR_cons, pR_nil, mul_one, mul_comm]
  congr 1
  conv_rhs => rw [hyl]
  rw [eqAbove_app 22 0 _ _ (by simp [hy])]
  simp [selectorPoint, eqEval, Shape.eOfNat_zero, fR]

theorem getD_map_zk (k : ℕ) (z : List FE2) (i : ℕ) : (z.map (zk k)).getD i 0 = zk k (z.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases z[i]? with
  | none => exact (zk_zero k).symm
  | some a => rfl

theorem kapR_zk (k : ℕ) (z : List FE2) : kapR ((z.take 22).map (zk k)) = zk k (kapE (z.take 22)) := by
  rw [kapR, kapE, zk_mul, zk_add, zk_add, zk_one, getD_map_zk, getD_map_zk]

theorem dzR_mapZ (k : ℕ) (w : List FE2) : dzR (w.map (zk k)) = (dzE w).map (zk k) := by
  rw [dzR, dzE, List.map_append, List.map_take, getD_map_zk, getD_map_zk]
  simp [zk_zero]

theorem dzR_zk (k : ℕ) (z : List FE2) : dzR ((z.take 22).map (zk k)) = (dzE (z.take 22)).map (zk k) :=
  dzR_mapZ k (z.take 22)

/-- **The small claim of the tape's row claim** (on `⟨23, 0⟩`, its point `0` above `D`): by components,
`eqAbove_D(x^σ)·σ^k(κ(z))·pR(σ^k(dzE z), x^σ)` paired with `ν`. -/
theorem rowZ_small (eqR : List FE) (z : List FE2) (hz : z.length = 23) (hz22 : z.getD 22 0 = 0) (v t : FE)
    (x : List FE) (hx : x.length = CMain.nu20) :
    (onStackZB ⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ t).1 x =
      ∑ k ∈ Finset.range 64, Lk (fun j => eqR.getD j 0) k
        (algebraMap FE (Rk k) ((⟨22, 0⟩ : Placement).eqAbove (rotZ x)) *
          (zk k (kapE (z.take 22)) * pR ((dzE (z.take 22)).map (zk k)) ((rotZ x).take 22))) := by
  have e1 : (onStackZB ⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ t).1 x =
      zW x (⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ : BlockClaim).onStack.1 := by
    unfold zW onStackZB
    rw [show (⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ : BlockClaim).block = ⟨CMain.nu20, 0⟩ from rfl, filter_nu]
  have hw : ∀ y : List FE, y.length = CMain.nu20 → (⟨⟨CMain.nu20, 0⟩, rowW eqR z, v⟩ : BlockClaim).onStack.1 y =
      ∑ k ∈ Finset.range 64, Lk (fun j => eqR.getD j 0) k
        (algebraMap FE (Rk k) ((⟨22, 0⟩ : Placement).eqAbove y) * pR ((z.take 22).map (zk k)) (y.take 22)) := by
    intro y hy
    simp only [BlockClaim.onStack]
    rw [eqAbove_top _ y hy, one_mul, List.take_of_length_le (by omega), rowW_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pR_last _ (by simp [hz]) (by rw [getD_map_zk, hz22, zk_zero]) y hy, List.map_take]
  rw [e1, zW_congr x hx hw, zW_fsum1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zW_lin, zWR_D _ (by simp [hz]) x hx, kapR_zk, dzR_zk]

end Lvm.Q2
end
-- ===== end of `LvmE2QPinOpenZ` =====

-- ===== merged from `LvmE2QPinOpenS` (VQ module merge: `LvmE2QPinOpenS.lean` removed) =====
section
-- New for lvm2 E2-FT (E2F-QH5): `C_main`'s opening at S2GF in the small shape, circuit side: the term pairs of the
-- regular `E2` claims (`halfTermsZ_spec`, `rowPairZ_spec`: big keys on the block, moved keys on the block moved down,
-- one leaf), on the pattern of `LvmQShapeB.rgPair_spec`.

/-!
# The small shape's term pairs

* `pairT_spec`: a pair on a regular block with any leaf: the big term is `sc·eqAbove_blk(x)·leaf`, the moved one
  `sc·eqAbove_{blk − 3·2^20}(x)·leaf`;
* **`halfTermsZ_spec`**: a regular half's pairs sum to `sc·(halfB …).onStack(x)` (big) and `sc·Σ (shiftB part)` (moved);
* **`rowPairZ_spec`**: a regular row claim's pair: `sc·bc.onStack(x)` and `sc·(shiftB bc).onStack(x)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Lvm.Shape

variable {c : Ctx} {M : Mem}

/-- The pair of a leaf on a regular block. -/
def pairOf (sc lf : Cell) (blk : Placement) : ZT :=
  ⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩

theorem pairT_spec (xb : ℕ) {blk : Placement} (hr : RegP blk) (sc lf : Cell) :
    tval M (fun i ↦ M.e (xb + i)) CMain.nu20 (pairOf sc lf blk).big =
        sc.val M * (blk.eqAbove (xsOf M CMain.nu20 xb) * lf.val M) ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 (pairOf sc lf blk).sml =
        sc.val M * ((shiftP blk).eqAbove (xsOf M CMain.nu20 xb) * lf.val M) ∧
      (pairOf sc lf blk).pb.length = CMain.nu20 - 20 ∧ (pairOf sc lf blk).ps.length = CMain.nu20 - 20 := by
  have hnu : CMain.nu20 = 23 := rfl
  have hv := hr.1
  refine ⟨?_, ?_, topK_length _, topK_length _⟩
  · simp only [pairOf, ZT.big]
    rw [← keyOf_top _ hv, tval, kprod_keyOf, eqAbove_prod blk _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length]; omega) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length]
    ring
  · simp only [pairOf, ZT.sml]
    rw [keyOf_congr (selbit blk) (selbit (shiftP blk)) _ 20 (fun i h1 h2 ↦ (selbit_shift_lo blk hr h1 h2).symm),
      ← keyOf_top _ hv, tval, kprod_keyOf, eqAbove_prod (shiftP blk) _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length, shiftP_vc]; omega) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length, shiftP_vc]
    ring

/-- **The pairs of a regular half's parts** (`halfTerms … true`): big `sc·Σ eqAbove_blk·coord(wordW·c)`, moved
`sc·Σ eqAbove_{shifted blk}·coord(wordW·c)`, no plain terms. -/
theorem halfTermsZ_spec {F : FCtx} (hF : FCtxOk M F) {xb : ℕ} (sc : Cell) (h : Bool) :
    ∀ (parts : List (C2 × Placement × List C2)) (m6 : Memo6),
      (∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧ RegP e.2.1) →
      Memo6Ok M xb m6 →
      Hs c M (halfTerms F CMain.nu20 xb sc h true parts m6) (fun r => Memo6Ok M xb r.1 ∧ r.2.2 = [] ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum =
          sc.val M * (partsV M parts |>.map fun e => (partH h e).onStack.1 (xsOf M CMain.nu20 xb)).sum ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum =
          sc.val M * (partsV M parts |>.map fun e => (shiftB (partH h e)).onStack.1 (xsOf M CMain.nu20 xb)).sum ∧
        ∀ t ∈ r.2.1, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], m6, _, hm => hs_pure ⟨hm, rfl, by simp [partsV], by simp [partsV], by simp⟩
  | (cv, blk, zl) :: ps, m6, hp, hm => by
    obtain ⟨hcK, hzK, hzl, hreg⟩ : KC2 cv ∧ (∀ x ∈ zl, KC2 x) ∧ zl.length = blk.variableCount ∧ RegP blk :=
      hp _ (List.mem_cons_self ..)
    have hnu : CMain.nu20 = 23 := rfl
    have hvc : blk.variableCount ≤ CMain.nu20 := by have := hreg.1; omega
    unfold halfTerms
    refine hs_bind (w6Leaf_spec hF.z hF.o xb cv zl hcK hzK m6 hm) fun r ⟨hm', hr⟩ => ?_
    refine hs_bind (halfTermsZ_spec hF sc h ps r.1 (fun e he => hp e (List.mem_cons_of_mem _ he)) hm')
      fun rs ⟨hm'', hn, hb, hs, hl⟩ => ?_
    simp only [ite_true]
    have hlf : (if h then r.2.2 else r.2.1).val M =
        c6 h (FE6.mul (wordWD (zl.map (C2.val M)) ((xsOf M CMain.nu20 xb).take blk.variableCount))
          (FE6.ofE2 (cv.val M))) := by
      have hW : wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M)) =
          wordWD (zl.map (C2.val M)) ((xsOf M CMain.nu20 xb).take blk.variableCount) := by
        rw [wordF_eq_wordWD, xs_take CMain.nu20 xb _ hvc, List.length_map, hzl]
      rw [← hW, ← hr]
      cases h <;> rfl
    obtain ⟨pb, ps', l1, l2⟩ := pairT_spec (M := M) xb hreg sc (if h then r.2.2 else r.2.1)
    refine hs_pure ⟨hm'', hn, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, show (⟨sc, if h then r.2.2 else r.2.1, topK (selbit blk),
        topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ : ZT).big =
        (pairOf sc (if h then r.2.2 else r.2.1) blk).big from rfl, pb, hb]
      simp only [partsV, List.map_cons, List.sum_cons]
      rw [hlf]
      simp only [partH, BlockClaim.onStack]
      ring
    · rw [List.map_cons, List.sum_cons, show (⟨sc, if h then r.2.2 else r.2.1, topK (selbit blk),
        topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩ : ZT).sml =
        (pairOf sc (if h then r.2.2 else r.2.1) blk).sml from rfl, ps', hs]
      simp only [partsV, List.map_cons, List.sum_cons]
      rw [hlf]
      simp only [partH, shiftB, BlockClaim.onStack, shiftP_vc]
      ring
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨l1, l2⟩
      · exact hl t ht

end Lvm.Q2
end
-- ===== end of `LvmE2QPinOpenS` =====

/-!
# The small shape's tails

* `trace_bit`: `Σ_k (δ_i a)^(2^k)` is bit `i` of `a` (the trace-dual basis, `dual_trace`, `fk_eq_sum_bits`);
  **`lrho_bits`**: the `ν`-pairing of the Frobenius powers of `u`'s coordinates is `Σ_j ρ_j·bit_j(u)`.
* `rowWordD_eq`: row `j` of the slices is `Σ_i bit_j(s_i)·x^i`; **`rowTailE2_eq`**: V's row tail is
  `Σ_l z*_l·L_ρ(w_l)`, `w_l = mass(z)·(1 + z₂₂)·eq((z₂₀, z₂₁), l)`.
* **`rowTailG_spec`**: the circuit's `rowTailG` is `rowTailE2`; **`tailD_val`**: `mass·zF(sel(l))` is `tailDE2`'s.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset

/-! ## Bits through the trace -/

/-- A bit as a `K` element. -/
def bitK (b : Bool) : FK := if b then 1 else 0

theorem bitK_pow (b : Bool) (k : ℕ) : bitK b ^ 2 ^ k = bitK b := by
  cases b
  · show (0 : FK) ^ 2 ^ k = 0; exact zero_pow (pow_ne_zero k two_ne_zero)
  · show (1 : FK) ^ 2 ^ k = 1; exact one_pow _

/-- **The trace against the dual basis is a bit**: `Σ_k (δ_i a)^(2^k) = bit_i(a)`. -/
theorem trace_bit {i : ℕ} (hi : i < 64) (a : FK) :
    ∑ k ∈ range 64, (dualK i * a) ^ 2 ^ k = bitK (a.val.toNat.testBit i) := by
  have ea : a = ∑ i' ∈ range 64, bitK (a.val.toNat.testBit i') * FK.x ^ i' := by
    conv_lhs => rw [fk_eq_sum_bits a]
    refine sum_congr rfl fun i' _ => ?_
    by_cases h : a.val.toNat.testBit i' <;> simp [h, bitK]
  have e1 : ∀ k, (dualK i * a) ^ 2 ^ k = ∑ i' ∈ range 64, bitK (a.val.toNat.testBit i') * (dualK i * FK.x ^ i') ^ 2 ^ k :=
    fun k => by
      conv_lhs => rw [ea, mul_sum, ← frobK_apply, map_sum]
      refine sum_congr rfl fun i' _ => ?_
      rw [frobK_apply, show dualK i * (bitK (a.val.toNat.testBit i') * FK.x ^ i') =
        bitK (a.val.toNat.testBit i') * (dualK i * FK.x ^ i') by ring, mul_pow, bitK_pow]
  rw [sum_congr rfl fun k _ => e1 k, sum_comm]
  rw [sum_congr rfl fun i' hi' => by rw [← mul_sum, dual_trace hi (mem_range.mp hi')]]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range, hi, ite_true]

/-- A bit of an `E2` value as an `E3` scalar. -/
def bE (u : FE2) (j : ℕ) : FE := FE.ofK (bitK (bitFE2 u j))

/-- **The `ν`-pairing of the Frobenius powers is the bit pairing**: `Σ_k ν₀_k a^(2^k) + ν₁_k b^(2^k) =
Σ_{j<128} ρ_j·bit_j(a + bX)`. -/
theorem lrho_bits (ρ : ℕ → FE) (u : FE2) :
    ∑ k ∈ range 64, (nuH ρ false k * FE.ofK (u.re ^ 2 ^ k) + nuH ρ true k * FE.ofK (u.im ^ 2 ^ k)) =
      ∑ j ∈ range 128, ρ j * bE u j := by
  have h1 : ∀ (h : Bool) (a : FK), ∑ k ∈ range 64, nuH ρ h k * FE.ofK (a ^ 2 ^ k) =
      ∑ i ∈ range 64, ρ (i + if h then 64 else 0) * FE.ofK (bitK (a.val.toNat.testBit i)) := by
    intro h a
    simp only [nuH, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    rw [← trace_bit (mem_range.mp hi), show FE.ofK (∑ k ∈ range 64, (dualK i * a) ^ 2 ^ k) =
      ∑ k ∈ range 64, FE.ofK ((dualK i * a) ^ 2 ^ k) from map_sum FE.ofKRingHom _ _, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [dK, mul_pow, show FE.ofK (dualK i ^ 2 ^ k * a ^ 2 ^ k) = FE.ofK (dualK i ^ 2 ^ k) * FE.ofK (a ^ 2 ^ k) from
      map_mul FE.ofKRingHom _ _]
    ring
  have a1 : ∑ i ∈ range 64, ρ (i + if false = true then 64 else 0) * FE.ofK (bitK (u.re.val.toNat.testBit i)) =
      ∑ i ∈ range 64, ρ i * bE u i :=
    sum_congr rfl fun i hi => by simp [bE, bitFE2, mem_range.mp hi]
  have a2 : ∑ i ∈ range 64, ρ (i + if true = true then 64 else 0) * FE.ofK (bitK (u.im.val.toNat.testBit i)) =
      ∑ i ∈ range 64, ρ (64 + i) * bE u (64 + i) :=
    sum_congr rfl fun i _ => by simp [bE, bitFE2, Nat.add_comm i 64]
  rw [sum_add_distrib, h1, h1, a1, a2]
  exact (sum_range_add (fun j => ρ j * bE u j) 64 64).symm

/-! ## The row words -/

/-- Bit `j` of an `E2` value as a `K` element, additive. -/
def bitHom (j : ℕ) : FE2 →+ FK where
  toFun u := bitK (bitFE2 u j)
  map_zero' := by
    unfold bitFE2
    split_ifs
    · show bitK ((0 : UInt64).toNat.testBit j) = 0; simp [bitK]
    · show bitK ((0 : UInt64).toNat.testBit (j - 64)) = 0; simp [bitK]
  map_add' a b := by
    have hx : ∀ (p q : Bool), bitK (xor p q) = bitK p + bitK q := by decide
    rw [← hx]
    congr 1
    unfold bitFE2
    split_ifs
    · show (a.re.val ^^^ b.re.val).toNat.testBit j = _
      rw [UInt64.toNat_xor, Nat.testBit_xor]
    · show (a.im.val ^^^ b.im.val).toNat.testBit (j - 64) = _
      rw [UInt64.toNat_xor, Nat.testBit_xor]

theorem bitHom_apply (j : ℕ) (u : FE2) : bitHom j u = bitK (bitFE2 u j) := rfl

/-- **Row `j` of the slices** packs bit `j` of each slice. -/
theorem rowWordD_eq (sv : List FE2) (j : ℕ) :
    rowWordD sv j = ∑ i ∈ range 64, bitK (bitFE2 (sv.getD i 0) j) * FK.x ^ i := by
  have hv : (rowWordD sv j).val.toNat = natsum (fun i => bitFE2 (sv.getD i 0) j) 64 := by
    show ((natsum (fun i => bitFE2 (sv.getD i 0) j) 64).toUInt64).toNat = _
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (natsum_lt _ 64)]
  conv_lhs => rw [fk_eq_sum_bits (rowWordD sv j)]
  refine sum_congr rfl fun i hi => ?_
  rw [hv, testBit_natsum]
  simp only [mem_range.mp hi, decide_true, Bool.true_and]
  by_cases h : bitFE2 (sv.getD i 0) j <;> simp [h, bitK]

/-- The tail rows' lane weights: `w_l = mass(z)·eq(z₂₂, 0)·eq((z₂₀, z₂₁), l)`. -/
def wT (z : List FE2) (l : ℕ) : FE2 :=
  tailMassE2 z * E2V.eqEvalF (z.drop 22) (E2V.selPtF 0 (CMain.nu20 - 22)) *
    (E2V.eqKernelF ((z.drop 20).take 2)).getD l 0

theorem zStarF_c0 (l : ℕ) : (Shape.zStarF l).c₀ = zK l := by rw [← ofK_zK]; rfl

/-- **A row word of the tail slices**: `Σ_l z*_l·bit_j(w_l)`. -/
theorem rowWordD_tail (z : List FE2) (j : ℕ) :
    FE.ofK (rowWordD (tailSlicesE2 z) j) = ∑ l ∈ range 4, FE.ofK (zK l) * bE (wT z l) j := by
  have hs : ∀ i < 64, bitK (bitFE2 ((tailSlicesE2 z).getD i 0) j) =
      ∑ l ∈ range 4, if (zK l).val.toNat.testBit i then bitK (bitFE2 (wT z l) j) else 0 := by
    intro i hi
    have e : (tailSlicesE2 z).getD i 0 = ∑ l ∈ range 4,
        if (zK l).val.toNat.testBit i then wT z l else 0 := by
      unfold tailSlicesE2
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.getD_some]
      rw [E2V.sumF_eq_sum, lsum_range, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [zStarF_c0]
      unfold wT
      split_ifs <;> simp [List.getD_eq_getElem?_getD]
    rw [← bitHom_apply, e, map_sum]
    refine sum_congr rfl fun l _ => ?_
    split_ifs
    · rfl
    · exact map_zero _
  have hw : rowWordD (tailSlicesE2 z) j = ∑ l ∈ range 4, bitK (bitFE2 (wT z l) j) * zK l := by
    rw [rowWordD_eq, sum_congr rfl fun i hi => by rw [hs i (mem_range.mp hi), sum_mul], sum_comm]
    refine sum_congr rfl fun l _ => ?_
    conv_rhs => rw [fk_eq_sum_bits (zK l), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hw, show FE.ofK (∑ l ∈ range 4, bitK (bitFE2 (wT z l) j) * zK l) =
    ∑ l ∈ range 4, FE.ofK (bitK (bitFE2 (wT z l) j) * zK l) from map_sum FE.ofKRingHom _ _]
  refine sum_congr rfl fun l _ => ?_
  rw [show FE.ofK (bitK (bitFE2 (wT z l) j) * zK l) = FE.ofK (bitK (bitFE2 (wT z l) j)) * FE.ofK (zK l) from
    map_mul FE.ofKRingHom _ _, bE, mul_comm]

/-- **V's row tail** is `Σ_l z*_l·L_ρ(w_l)` (`L_ρ(w) = Σ_j ρ_j bit_j(w)`). -/
theorem rowTailE2_eq (eqR : List FE) (z : List FE2) :
    rowTailE2 eqR z = ∑ l ∈ range 4, FE.ofK (zK l) * ∑ j ∈ range 128, eqR.getD j 0 * bE (wT z l) j := by
  unfold rowTailE2
  dsimp only
  rw [sumE_eq, lsum_range, sum_congr rfl fun j _ => by rw [rowWordD_tail, mul_sum], sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-! ## The circuit's row tail -/

section Circ

variable {c : Ctx} {M : Mem}

theorem g2Mul_K (a b d : C2) : Hs c M (g2Mul a b d) KC2 := fun _ _ => ⟨rfl, rfl⟩
theorem g2Lin_K (k : FK) (k' : FE2) (a b : C2) : Hs c M (g2Lin k k' a b) KC2 := fun _ _ => ⟨rfl, rfl⟩
theorem g2One_K (a : C2) : Hs c M (g2One a) KC2 := fun _ _ => ⟨rfl, rfl⟩
theorem g2Add_K (a b : C2) : Hs c M (g2Add a b) KC2 := fun _ _ => ⟨rfl, rfl⟩

theorem hs_mapB_all {α β : Type} (f : α → BM β) (P : β → Prop) (hf : ∀ a, Hs c M (f a) P) :
    ∀ l : List α, Hs c M (mapB f l) (fun rs => ∀ x ∈ rs, P x)
  | [] => hs_pure (by simp)
  | a :: l => hs_bind (hf a) fun r hr => hs_bind (hs_mapB_all f P hf l) fun rs hrs =>
    hs_pure fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hrs x hx

theorem hs_g2Eq0_K (z : C2) : ∀ (acc : C2) (rs : List C2), KC2 acc → Hs c M (g2Eq0 z acc rs) KC2
  | acc, [], h => hs_pure h
  | acc, r :: rs, _ => hs_bind (hs_g2One r) fun r1 _ => hs_bind (g2Mul_K acc r1 z) fun a ha =>
    hs_g2Eq0_K z a rs ha

theorem hs_g2EqStep_K (z : C2) (tab : List C2) (r : C2) : Hs c M (g2EqStep z tab r) (fun t => ∀ x ∈ t, KC2 x) := by
  unfold g2EqStep
  exact hs_bind (hs_g2One r) fun r1 _ => hs_bind (hs_mapB_all _ KC2 (fun e => g2Mul_K e r1 z) tab) fun lo hlo =>
    hs_bind (hs_mapB_all _ KC2 (fun e => g2Mul_K e r z) tab) fun hi hhi => hs_pure fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hlo x hx
      · exact hhi x hx

theorem hs_g2EqTab_K (z : C2) : ∀ (tab pt : List C2), (∀ x ∈ tab, KC2 x) →
    Hs c M (g2EqTab z tab pt) (fun t => ∀ x ∈ t, KC2 x)
  | tab, [], h => hs_pure h
  | tab, r :: rs, _ => hs_bind (hs_g2EqStep_K z tab r) fun t ht => hs_g2EqTab_K z t rs ht

theorem eqStep2_mul (a : FE2) (tab : List FE2) (r : FE2) :
    eqStep2 (tab.map (a * ·)) r = (eqStep2 tab r).map (a * ·) := by
  simp only [eqStep2, List.map_append, List.map_map, Function.comp_def, mul_assoc]

theorem foldl_eqStep2_mul (a : FE2) : ∀ (pt tab : List FE2),
    pt.foldl eqStep2 (tab.map (a * ·)) = (pt.foldl eqStep2 tab).map (a * ·)
  | [], _ => rfl
  | r :: pt, tab => by
    rw [List.foldl_cons, List.foldl_cons, eqStep2_mul, foldl_eqStep2_mul a pt]

/-- **`L_ρ` in the circuit** (`lRhoG`): `Σ_k ν₀_k·u_re^(2^k) + ν₁_k·u_im^(2^k)`. -/
theorem lRhoG_spec {F : FCtx} (hF : FCtxOk M F) (nu : RowNu) (u : C2) :
    Hs c M (lRhoG F nu u) (fun r => r.val M = ∑ k ∈ range 64, ((nu.nu0.getD k default).val M * u.re.val M ^ 2 ^ k +
      (nu.nu1.getD k default).val M * u.im.val M ^ 2 ^ k)) := by
  unfold lRhoG
  refine hs_bind (hs_frobsK hF.zk u.re) fun fr hfr => hs_bind (hs_frobsK hF.zk u.im) fun fi hfi => ?_
  have hgen : ∀ n, Hs c M ((List.range n).foldl (fun (m : BM Cell) k => m >>= fun acc =>
      mulAdd .E (nu.nu0.getD k default) (fr.getD k default) acc >>= fun a1 =>
      mulAdd .E (nu.nu1.getD k default) (fi.getD k default) a1) (pure F.z))
      (fun r => r.val M = ∑ k ∈ range n, ((nu.nu0.getD k default).val M * (fr.getD k default).val M +
        (nu.nu1.getD k default).val M * (fi.getD k default).val M)) := by
    intro n
    induction n with
    | zero => exact hs_pure (by rw [hF.z, sum_range_zero])
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine hs_bind ih fun acc hacc => hs_bind (hs_mulAdd _ _ _ _) fun a1 ha1 =>
        hs_mono (hs_mulAdd _ _ _ _) fun r hr => ?_
      rw [hr, ha1, hacc, sum_range_succ]
      ring
  refine hs_mono (hgen 64) fun r hr => ?_
  rw [hr]
  refine sum_congr rfl fun k hk => ?_
  rw [hfr k (mem_range.mp hk), hfi k (mem_range.mp hk)]

/-- **`L_ρ` in loops** (`lRhoGL`, blob GT's lever L1c): `Σ_k ν₀·u_re^(2^k) + ν₁·u_im^(2^k)`, the `ν` cells read
through `nuAt` at iteration `(k + 63) mod 64` (component `k`). -/
theorem lRhoGL_spec {F : FCtx} (hF : FCtxOk M F) (nu : RowNu) (u : C2) (hu : KC2 u) :
    Hs c M (lRhoGL F nu u) (fun r => r.val M = ∑ k ∈ range 64,
      ((nuAt nu.nu0 ((k + 63) % 64)).val M * u.re.val M ^ 2 ^ k +
        (nuAt nu.nu1 ((k + 63) % 64)).val M * u.im.val M ^ 2 ^ k)) := by
  unfold lRhoGL
  refine hs_bind (hs_frobLoop hF.zk _) fun Fr ⟨hFd, hFv⟩ => ?_
  refine hs_bind (hs_accLoop2 Fr hFd nu.nu0 nu.nu1 hF.z) fun S hS => hs_pure ?_
  rw [hS]
  have hit : ∀ j ∈ range 64, (nuAt nu.nu0 j).val M * (Fr.cell 0 j).val M + (nuAt nu.nu1 j).val M * (Fr.cell 1 j).val M =
      (fun k => (nuAt nu.nu0 ((k + 63) % 64)).val M * u.re.val M ^ 2 ^ k +
        (nuAt nu.nu1 ((k + 63) % 64)).val M * u.im.val M ^ 2 ^ k) ((j + 1) % 64) := by
    intro j hj
    have hj' := mem_range.mp hj
    have e : ((j + 1) % 64 + 63) % 64 = j := by omega
    simp only [e]
    rw [hFv 0 (by simp) j hj', hFv 1 (by simp) j hj']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [frob_comp hu.1 hj', frob_comp hu.2 hj']
  rw [sum_congr rfl hit]
  exact sum_rot64 (fun k => (nuAt nu.nu0 ((k + 63) % 64)).val M * u.re.val M ^ 2 ^ k +
    (nuAt nu.nu1 ((k + 63) % 64)).val M * u.im.val M ^ 2 ^ k)

/-- **`L_ρ` of a `K`-celled value** is the bit pairing. -/
theorem lRho_val (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR) {u : C2} (hu : KC2 u) :
    ∑ k ∈ range 64, ((nuAt nu.nu0 ((k + 63) % 64)).val M * u.re.val M ^ 2 ^ k +
      (nuAt nu.nu1 ((k + 63) % 64)).val M * u.im.val M ^ 2 ^ k) =
      ∑ j ∈ range 128, eqR.getD j 0 * bE (u.val M) j := by
  rw [← lrho_bits]
  refine sum_congr rfl fun k hk => ?_
  rw [(hnu.2 k (mem_range.mp hk)).1, (hnu.2 k (mem_range.mp hk)).2, ← kcell_val hu.1, ← kcell_val hu.2,
    show FE.ofK ((u.re.val M).c₀) ^ 2 ^ k = FE.ofK ((u.re.val M).c₀ ^ 2 ^ k) from (map_pow FE.ofKRingHom _ _).symm,
    show FE.ofK ((u.im.val M).c₀) ^ 2 ^ k = FE.ofK ((u.im.val M).c₀ ^ 2 ^ k) from (map_pow FE.ofKRingHom _ _).symm]
  rfl

/-- **`L_ρ` of a `K`-celled value** is the bit pairing (blob v4's `lRhoG`, reading the `ν` cells by index). -/
theorem lRho_valV (nu : RowNu) (eqR : List FE) (hnu : RowNuV M nu eqR) {u : C2} (hu : KC2 u) :
    ∑ k ∈ range 64, ((nu.nu0.getD k default).val M * u.re.val M ^ 2 ^ k +
      (nu.nu1.getD k default).val M * u.im.val M ^ 2 ^ k) =
      ∑ j ∈ range 128, eqR.getD j 0 * bE (u.val M) j := by
  rw [← lrho_bits]
  refine sum_congr rfl fun k hk => ?_
  rw [(hnu k (mem_range.mp hk)).1, (hnu k (mem_range.mp hk)).2, ← kcell_val hu.1, ← kcell_val hu.2,
    show FE.ofK ((u.re.val M).c₀) ^ 2 ^ k = FE.ofK ((u.re.val M).c₀ ^ 2 ^ k) from (map_pow FE.ofKRingHom _ _).symm,
    show FE.ofK ((u.im.val M).c₀) ^ 2 ^ k = FE.ofK ((u.im.val M).c₀ ^ 2 ^ k) from (map_pow FE.ofKRingHom _ _).symm]
  rfl

theorem fe2_sub (a b : FE2) : a - b = a + b := rfl

theorem getD_of_map_eq {α β γ : Type} (f : α → γ) (g : β → γ) {as : List α} {bs : List β}
    (h : as.map f = bs.map g) {i : ℕ} (hi : i < bs.length) (da : α) (db : β) :
    f (as.getD i da) = g (bs.getD i db) := by
  have hl : as.length = bs.length := by simpa using congrArg List.length h
  have e := List.getElem_of_eq h (by simpa [hl] using hi)
  simp only [List.getElem_map] at e
  rw [List.getD_eq_getElem _ _ (hl ▸ hi), List.getD_eq_getElem _ _ hi, e]

theorem eqKernelF_eq (pt : List FE2) : E2V.eqKernelF pt = pt.foldl eqStep2 [1] := rfl

theorem c2_getD (z : List C2) {i : ℕ} (hi : i < z.length) : (z.getD i default).val M = (z.map (C2.val M)).getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem drop22 (zv : List FE2) (hz : zv.length = 23) : zv.drop 22 = [zv.getD 22 0] := by
  apply List.ext_getElem (by simp [hz])
  intro i h1 _
  have : i = 0 := by simp [hz] at h1; omega
  subst this
  simp [List.getD_eq_getElem?_getD, hz]

theorem take2drop20 (zv : List FE2) (hz : zv.length = 23) : (zv.drop 20).take 2 = [zv.getD 20 0, zv.getD 21 0] := by
  apply List.ext_getElem (by simp [hz])
  intro i h1 _
  have : i < 2 := by simp [hz] at h1; omega
  interval_cases i <;> simp [List.getD_eq_getElem?_getD, hz]

/-- **The circuit's row tail is V's** (`rowTailG` = `rowTailE2` at the claim's point; `κ = (1 + z₁₈)(1 + z₁₉)`). -/
theorem rowTailG_spec {F : FCtx} (hF : FCtxOk M F) (nu : RowNu) (eqR : List FE) (hnu : RowNuOk M nu eqR)
    (z : List C2) (hz : z.length = 23) (κ : C2) (hκ : κ.val M = kapE (z.map (C2.val M))) :
    Hs c M (rowTailG F nu z κ) (fun r => r.val M = rowTailE2 eqR (z.map (C2.val M))) := by
  unfold rowTailG
  refine hs_bind (hs_and (hs_g2One κ) (g2One_K κ)) fun mass ⟨hm, hmK⟩ => ?_
  refine hs_bind (hs_and (hs_g2Eq0 hF.z2 mass (z.drop 22)) (hs_g2Eq0_K F.z2 mass (z.drop 22) hmK))
    fun mb ⟨hmb, hmbK⟩ => ?_
  refine hs_bind (hs_and (hs_g2EqTab hF.z2 [mb] [z.getD 20 default, z.getD 21 default])
    (hs_g2EqTab_K F.z2 [mb] _ (by simpa using hmbK))) fun us ⟨hus, husK⟩ => ?_
  refine hs_bind (hs_mapBC (if F.gt then lRhoGL F nu else lRhoG F nu)
    (fun u => ∑ j ∈ range 128, eqR.getD j 0 * bE (u.val M) j) us fun u hu => ?_) fun Ls hLs => ?_
  · cases F.gt
    · exact hs_mono (lRhoG_spec hF nu u) fun r hr => by rw [hr, lRho_valV nu eqR hnu.1 (husK u hu)]
    · exact hs_mono (lRhoGL_spec hF nu u (husK u hu)) fun r hr => by rw [hr, lRho_val nu eqR hnu (husK u hu)]
  refine hs_mono (hs_linSumE F.z _) fun r hr => ?_
  have hzl : (z.map (C2.val M)).length = 23 := by simp [hz]
  have hus' : us.map (C2.val M) =
      (E2V.eqKernelF [(z.map (C2.val M)).getD 20 0, (z.map (C2.val M)).getD 21 0]).map (mb.val M * ·) := by
    rw [hus, List.map_cons, List.map_nil, List.map_cons, List.map_cons, List.map_nil, c2_getD z (by omega),
      c2_getD z (by omega), show [mb.val M] = [1].map (mb.val M * ·) by simp, foldl_eqStep2_mul, eqKernelF_eq]
  have hkl : ∀ a b : FE2, (E2V.eqKernelF [a, b]).length = 4 := fun a b => by simp [E2V.eqKernelF]
  have hul : us.length = 4 := by have := congrArg List.length hus'; rw [List.length_map, List.length_map, hkl] at this; exact this
  have ewG : ∀ l, mb.val M * (E2V.eqKernelF [(z.map (C2.val M)).getD 20 0, (z.map (C2.val M)).getD 21 0]).getD l 0 =
      wT (z.map (C2.val M)) l := by
    intro l
    rw [hmb, hm, hκ, List.map_drop, drop22 _ hzl, wT, drop22 _ hzl, take2drop20 _ hzl]
    have ea : E2V.eqAtF [(z.map (C2.val M)).getD 22 0] 0 = 1 + (z.map (C2.val M)).getD 22 0 := by
      simp [E2V.eqAtF]
    have eb : E2V.eqEvalF [(z.map (C2.val M)).getD 22 0] (E2V.selPtF 0 (CMain.nu20 - 22)) =
        1 + (z.map (C2.val M)).getD 22 0 := by
      rw [show CMain.nu20 - 22 = 1 from rfl, show (E2V.selPtF 0 1 : List FE2) = [0] from rfl]
      simp [E2V.eqEvalF]
    rw [ea, eb, tailMassE2, kapE, fe2_sub, fe2_sub, fe2_sub]
  rw [hr, hF.z, zero_add, rowTailE2_eq, List.map_map, lsum_range]
  refine sum_congr rfl fun l hl => ?_
  have hl4 := mem_range.mp hl
  have e1 := getD_of_map_eq (Cell.val M) _ hLs (by omega : l < us.length) default default
  have e2 := getD_of_map_eq (C2.val M) _ hus' (by rw [hkl]; exact hl4) default 0
  simp only [Function.comp_apply]
  rw [e1, e2, ewG]

end Circ

end Lvm.Q2
