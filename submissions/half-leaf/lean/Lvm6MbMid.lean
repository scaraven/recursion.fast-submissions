-- New for lvm6 Y1 (2026-11-22): merged module (build cost: one import load), parts:
--   Lvm6MbBus: the mini-bus's leaves at `E2 = GF(2^128)` (MB-decision §6, `Lvm6MbBus`): the three
--   Lvm6MbLin: the mini-bus's tableless ending at `E2` (MB-decision §4, `Lvm6MbLin`): on tables with
--   Lvm6MbMid: the mini-bus at `E2` from doom to doom (MB-decision §6, `Lvm6MbFid` and `Lvm6MbMid`
import Lvm6MbProg
import Lvm6MbSample
import Lvm6MbGkr

/-! ### Part `Lvm6MbBus` (was its own module) -/
section

/-!
# The mini-bus's leaves at `E2`

Season 1's `Bus.sideLeaves` (`W/LvmBus.lean`) stacks the leaves of an `M3Instance`'s sources over `E`. Here the
leaves are those of the program's own blocks (`sideBlocksG`, `stackBlocksG` of `Lvm6MbProg`), over `E2`, on the lvm
instance of a list of tables (no boundary block, no padding row):

* **`leafG`**: side `k`'s leaf at index `w`: `1 + Σ_b [w ∈ b]·(leaf_b(w − off_b) + 1)` (characteristic two: the
  block's leaf inside the block, `1` outside every block), `leaf_b` the block's form on the row (`evalFG`).
* **`prod_leafG`**: the product of a side's leaves is the product, block by block, of its blocks' leaves
  (consecutive blocks inside `2^μ`); **`prod_leafG_side`** (push, pull): `Π_{t ∈ tuples} (β − t̃(α))`, the grand
  product polynomial at `(α, β)`; **`prod_leafG_count`**: the count cells' product.
* **`mle_leafG`**: the leaves' extension at `ζ` is `1 + Σ_b w_b·(ℓ̃_b(ζ_low) + 1)`, `w_b = eqAboveG` (aligned blocks:
  stacked largest first).

The `K`-level facts (`Bus.sideTuples_perm`, `Bus.Conditions.fits`, `Lvm.M3.sideBlocksV_eq`'s source order) are
season 1's, reused.
-/

set_option autoImplicit false

namespace Lvm6.Mb

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm.M3 CompPoly CMlPolynomialEval
open Finset

/-! ## Characteristic two -/

section Char2

variable {F : Type} [Field F] [CharP F 2]

theorem one_add_add_one (a : F) : 1 + (a + 1) = a := by
  rw [add_comm a 1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

omit [CharP F 2] in
theorem eqEvalF_comm : ∀ (a b : List F), eqEvalF a b = eqEvalF b a := by
  intro a b
  unfold eqEvalF
  rw [List.zipWith_comm]
  congr 2
  funext x y
  ring

omit [CharP F 2] in
theorem eqEvalF_cons2 (a b : F) (x y : List F) :
    eqEvalF (a :: x) (b :: y) = (1 + a + b) * eqEvalF x y := by
  unfold eqEvalF
  rw [List.zipWith_cons_cons, List.foldl_cons, one_mul]
  have h : ∀ (l : List F) (c : F), l.foldl (· * ·) c = c * l.foldl (· * ·) 1 := by
    intro l
    induction l with
    | nil => simp
    | cons d l ih => intro c; rw [List.foldl_cons, List.foldl_cons, ih, ih (1 * d)]; ring
  exact h _ _

/-- **`eq` at a cube point**: `eqEvalF u (bits y)` is `eqAtF u y`. -/
theorem eqEvalF_bitsF : ∀ (u : List F) (y : ℕ), eqEvalF u (bitsF y u.length) = eqAtF u y
  | [], _ => rfl
  | r :: rs, y => by
    rw [List.length_cons, bitsF, eqEvalF_cons2, eqEvalF_bitsF rs, eqAtF_succ]
    congr 1
    split_ifs
    · rw [add_assoc, one_add_add_one]
    · rw [add_zero]

end Char2

/-! ## Stacking -/

section Stack

variable {X : Type} (κ : X → ℕ)

/-- Blocks stacked consecutively from offset `o`. -/
def stk : List X → ℕ → List (X × ℕ)
  | [], _ => []
  | b :: bs, o => (b, o) :: stk bs (o + 2 ^ κ b)

/-- The blocks' total size. -/
def tot (bs : List X) : ℕ := (bs.map fun b ↦ 2 ^ κ b).sum

theorem tot_cons (b : X) (bs : List X) : tot κ (b :: bs) = 2 ^ κ b + tot κ bs := by
  simp [tot]

theorem tot_perm {bs bs' : List X} (h : bs.Perm bs') : tot κ bs = tot κ bs' :=
  (h.map _).sum_eq

theorem mem_stk {bo : X × ℕ} : ∀ {bs : List X} {o : ℕ}, bo ∈ stk κ bs o →
    bo.1 ∈ bs ∧ o ≤ bo.2 ∧ bo.2 + 2 ^ κ bo.1 ≤ o + tot κ bs
  | [], _, h => by simp [stk] at h
  | b :: bs, o, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨List.mem_cons_self, le_rfl, by simp [tot_cons]⟩
    · obtain ⟨h1, h2, h3⟩ := mem_stk h
      have := Nat.two_pow_pos (κ b)
      exact ⟨List.mem_cons_of_mem _ h1, by omega, by rw [tot_cons]; omega⟩

/-- In a list stacked largest first, every block is aligned on its size. -/
theorem dvd_stk {bo : X × ℕ} : ∀ {bs : List X} {o : ℕ}, bs.Pairwise (fun a b ↦ κ b ≤ κ a) →
    (∀ b ∈ bs, 2 ^ κ b ∣ o) → bo ∈ stk κ bs o → 2 ^ κ bo.1 ∣ bo.2
  | [], _, _, _, h => by simp [stk] at h
  | b :: bs, o, hp, hd, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hd _ List.mem_cons_self
    · refine dvd_stk (List.pairwise_cons.mp hp).2 (fun b' hb' ↦ ?_) h
      exact Nat.dvd_add (hd b' (List.mem_cons_of_mem _ hb'))
        (Nat.pow_dvd_pow 2 ((List.pairwise_cons.mp hp).1 b' hb'))

/-- `stackBlocksG`'s fold. -/
theorem stack_foldG (l : List VBlockG) (acc : List (VBlockG × ℕ)) (o : ℕ) :
    l.foldl (fun (acc : List (VBlockG × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ)) (acc, o) =
      (acc ++ stk VBlockG.κ l o, o + tot VBlockG.κ l) := by
  induction l generalizing acc o with
  | nil => simp [stk, tot]
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    simp [stk, tot_cons, add_assoc]

/-- The program's blocks sorted largest first (stable). -/
def sortG (bs : List VBlockG) : List VBlockG := bs.mergeSort fun a b ↦ decide (b.κ ≤ a.κ)

theorem stackBlocksG_eq (bs : List VBlockG) : stackBlocksG bs = stk VBlockG.κ (sortG bs) 0 := by
  rw [stackBlocksG, stack_foldG]
  simp [sortG]

theorem sortG_perm (bs : List VBlockG) : (sortG bs).Perm bs := List.mergeSort_perm _ _

theorem sortG_pairwise (bs : List VBlockG) : (sortG bs).Pairwise (fun a b ↦ b.κ ≤ a.κ) := by
  have hp := List.pairwise_mergeSort (le := fun a b : VBlockG ↦ decide (b.κ ≤ a.κ))
    (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) bs
  exact hp.imp fun h ↦ of_decide_eq_true h

/-- A stacked block of the program: inside the stack, aligned. -/
theorem mem_stackBlocksG {bs : List VBlockG} {bo : VBlockG × ℕ} (h : bo ∈ stackBlocksG bs) :
    bo.1 ∈ bs ∧ bo.2 + 2 ^ bo.1.κ ≤ tot VBlockG.κ bs ∧ 2 ^ bo.1.κ ∣ bo.2 := by
  rw [stackBlocksG_eq] at h
  obtain ⟨h1, -, h3⟩ := mem_stk VBlockG.κ h
  refine ⟨(sortG_perm bs).subset h1, by rw [← tot_perm VBlockG.κ (sortG_perm bs)]; omega, ?_⟩
  exact dvd_stk VBlockG.κ (sortG_pairwise bs) (fun _ _ ↦ dvd_zero _) h

variable {F : Type} [Field F] (f : X → ℕ → F)

/-- The leaves of stacked blocks, less the pad `1` (characteristic two). -/
def bump (l : List (X × ℕ)) (w : ℕ) : F :=
  (l.map fun bo ↦ if bo.2 ≤ w ∧ w < bo.2 + 2 ^ κ bo.1 then f bo.1 (w - bo.2) + 1 else 0).sum

theorem bump_below : ∀ (bs : List X) (o w : ℕ), w < o → bump κ f (stk κ bs o) w = 0
  | [], _, _, _ => by simp [bump, stk]
  | b :: bs, o, w, h => by
    have := Nat.two_pow_pos (κ b)
    have ih := bump_below bs (o + 2 ^ κ b) w (by omega)
    simp only [bump, stk, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, if_neg (by omega), add_zero]

variable [CharP F 2]

/-- **The product of stacked leaves** is the product of the blocks' leaves: the pad is `1`. -/
theorem prod_bump : ∀ (bs : List X) (o N : ℕ), o + tot κ bs ≤ N →
    ∏ w ∈ Ico o N, (1 + bump κ f (stk κ bs o) w) = (bs.map fun b ↦ ∏ n ∈ range (2 ^ κ b), f b n).prod
  | [], o, N, _ => by simp [bump, stk]
  | b :: bs, o, N, h => by
    have := Nat.two_pow_pos (κ b)
    rw [tot_cons] at h
    rw [← Finset.prod_Ico_consecutive _ (show o ≤ o + 2 ^ κ b by omega) (show o + 2 ^ κ b ≤ N by omega),
      List.map_cons, List.prod_cons, ← prod_bump bs (o + 2 ^ κ b) N (by omega)]
    congr 1
    · rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
      refine Finset.prod_congr rfl fun n hn ↦ ?_
      have hn' := Finset.mem_range.mp hn
      simp only [bump, stk, List.map_cons, List.sum_cons]
      have h0 := bump_below κ f bs (o + 2 ^ κ b) (o + n) (by omega)
      simp only [bump] at h0
      rw [h0, if_pos (by omega), add_zero, Nat.add_sub_cancel_left, one_add_add_one]
    · refine Finset.prod_congr rfl fun w hw ↦ ?_
      have hw' := Finset.mem_Ico.mp hw
      simp only [bump, stk, List.map_cons, List.sum_cons]
      rw [if_neg (by omega), zero_add]

omit [CharP F 2] in
/-- **The extension of stacked leaves**: the pad's, plus each block's leaves less one at its indices. -/
theorem sum_bump (e : ℕ → F) (l : List (X × ℕ)) (N : ℕ) (hl : ∀ bo ∈ l, bo.2 + 2 ^ κ bo.1 ≤ N) :
    ∑ w ∈ range N, e w * (1 + bump κ f l w) =
      ∑ w ∈ range N, e w + (l.map fun bo ↦ ∑ n ∈ range (2 ^ κ bo.1), e (bo.2 + n) * (f bo.1 n + 1)).sum := by
  simp only [mul_add, mul_one, Finset.sum_add_distrib]
  congr 1
  induction l with
  | nil => simp [bump]
  | cons bo l ih =>
    simp only [bump, List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib] at ih ⊢
    rw [ih fun b hb ↦ hl b (List.mem_cons_of_mem _ hb)]
    congr 1
    have hb := hl bo List.mem_cons_self
    rw [show (∑ w ∈ range N, e w * if bo.2 ≤ w ∧ w < bo.2 + 2 ^ κ bo.1 then f bo.1 (w - bo.2) + 1 else 0) =
        ∑ w ∈ Ico bo.2 (bo.2 + 2 ^ κ bo.1), e w * (f bo.1 (w - bo.2) + 1) by
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun w _ ↦ rfl
      ext w
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    simp only [Nat.add_sub_cancel_left, mul_add, mul_one, Finset.sum_add_distrib]

end Stack

/-! ## Equality weights of a block -/

section Weights

/-- **A block's weight** (`eqAboveG`) is the equality weight of the high coordinates at its index. -/
theorem eqAboveG_eq (κ off : ℕ) (ζ : List E2) :
    eqAboveG ⟨κ, off⟩ ζ = eqAtF (ζ.drop κ) (off / 2 ^ κ) := by
  unfold eqAboveG
  simp only
  rw [selPtF_eq_bitsF, Nat.shiftRight_eq_div_pow, eqEvalF_comm, ← List.length_drop, eqEvalF_bitsF]

/-- The equality weight of an index inside an aligned block splits into the block's weight and the low
coordinates' weight. -/
theorem eqAtF_block {κ off n : ℕ} {ζ : List E2} (hκ : κ ≤ ζ.length) (hd : 2 ^ κ ∣ off) (hn : n < 2 ^ κ) :
    eqAtF ζ (off + n) = eqAtF (ζ.take κ) n * eqAboveG ⟨κ, off⟩ ζ := by
  have ht : (ζ.take κ).length = κ := by simp [hκ]
  obtain ⟨m, rfl⟩ := hd
  conv_lhs => rw [← List.take_append_drop κ ζ]
  rw [eqAtF_append, eqAtF_mod (ζ.take κ), ht, eqAboveG_eq, Nat.mul_div_cancel_left _ (Nat.two_pow_pos κ)]
  congr 2
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos κ), Nat.div_eq_of_lt hn, zero_add]

end Weights

/-! ## Forms on a row -/

/-- **A form's value on a row** of `E2` values: `Σ_m coef·Π_{c ∈ m} v(c)`. -/
def evalFG (f : FormG) (v : ℕ → E2) : E2 := (f.terms.map fun m ↦ m.2 * (m.1.map v).prod).sum

theorem sum_map_flatMapG {M α β : Type} [AddCommMonoid M] (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).sum = (l.map fun a ↦ ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem prod_map_flatMapG {M α β : Type} [CommMonoid M] (l : List α) (g : α → List β) (f : β → M) :
    ((l.flatMap g).map f).prod = (l.map fun a ↦ ((g a).map f).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem evalFG_formSumG (fs : List FormG) (v : ℕ → E2) :
    evalFG (formSumG fs) v = (fs.map fun f ↦ evalFG f v).sum := by
  simp only [evalFG, formSumG, sum_map_flatMapG]

theorem evalFG_cpolyFormG (w : E2) (P : CPoly) (v : ℕ → E2) :
    evalFG (cpolyFormG w P) v = w * (P.map fun m ↦ kG m.1 * (m.2.map v).prod).sum := by
  simp only [evalFG, cpolyFormG, List.map_map, Function.comp_def, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun m _ ↦ by ring)

theorem kG_eq (a : Lvm.FK) : kG a = algebraMap K E2 (Lvm.FK.toBF64 a) := by
  simp [kG]
  rfl

/-- A coordinate polynomial on a row of `K` values, lifted to `E2`. -/
theorem cpoly_lift {w : ℕ} (r : Fin w → K) (P : CPoly) :
    (P.map fun m ↦ kG m.1 * (m.2.map fun c ↦ algebraMap K E2 (CPoly.ext r c)).prod).sum =
      algebraMap K E2 (MvPolynomial.eval r (P.toMv w)) := by
  rw [CPoly.eval_toMv, CPoly.evalB, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun m _ ↦ ?_)
  simp only [Function.comp_apply, map_mul, kG_eq, map_list_prod, List.map_map]
  rfl

/-- A sum over a list with its indices is a sum over the indices. -/
theorem sum_zipIdxG {M α : Type} [AddCommMonoid M] (g : ℕ → α → M) (d : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map fun x ↦ g x.2 x.1).sum =
      ∑ k ∈ Finset.range l.length, g (n + k) (l.getD k d)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdxG g d l (n + 1),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ ↦ by rw [add_assoc, add_comm 1 k]) rfl

/-- **A message's leaf on a row** (`leafFormG`): `β + eqα_0·sep + eqα_1·addr + eqα_2·cnt + Σ_l eqα_{3+l}·val_l`. -/
theorem evalFG_leafFormG (eqα : List E2) (β : E2) (k : Key) (cnt : CPoly) {w : ℕ} (r : Fin w → K) :
    evalFG (leafFormG eqα β k cnt) (fun c ↦ algebraMap K E2 (CPoly.ext r c)) =
      β + eqα.getD 0 0 * kG k.sep + eqα.getD 1 0 * algebraMap K E2 (MvPolynomial.eval r (k.addr.toMv w)) +
        eqα.getD 2 0 * algebraMap K E2 (MvPolynomial.eval r (cnt.toMv w)) +
        ∑ l ∈ range k.val.length, eqα.getD (3 + l) 0 *
          algebraMap K E2 (MvPolynomial.eval r ((k.val.getD l []).toMv w)) := by
  simp only [leafFormG, evalFG_formSumG, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, evalFG_cpolyFormG, cpoly_lift, List.map_map, Function.comp_def]
  rw [sum_zipIdxG (fun l P ↦ eqα.getD (3 + l) 0 * algebraMap K E2 (MvPolynomial.eval r (CPoly.toMv w P))) [] k.val 0]
  simp [evalFG]
  ring

/-- **The sixteen weighted coordinates** of a message with at most thirteen value limbs. -/
theorem sum_vecG (eqα : List E2) (k : Key) (cnt : CPoly) {w : ℕ} (r : Fin w → K) (hk : k.val.length ≤ 13) :
    ∑ i : Fin 16, eqα.getD i 0 * algebraMap K E2 (MvPolynomial.eval r (k.vec w cnt)[i]) =
      eqα.getD 0 0 * kG k.sep + eqα.getD 1 0 * algebraMap K E2 (MvPolynomial.eval r (k.addr.toMv w)) +
        eqα.getD 2 0 * algebraMap K E2 (MvPolynomial.eval r (cnt.toMv w)) +
        ∑ l ∈ range k.val.length, eqα.getD (3 + l) 0 *
          algebraMap K E2 (MvPolynomial.eval r ((k.val.getD l []).toMv w)) := by
  have hv : ∀ i : ℕ, (hi : i < 16) → MvPolynomial.eval r (k.vec w cnt)[i] =
      if i = 0 then Lvm.FK.toBF64 k.sep else if i = 1 then MvPolynomial.eval r (k.addr.toMv w)
      else if i = 2 then MvPolynomial.eval r (cnt.toMv w)
      else MvPolynomial.eval r ((k.val.getD (i - 3) []).toMv w) := by
    intro i hi
    simp only [Key.vec, Vector.getElem_ofFn]
    split_ifs <;> simp
  have e : ∑ i : Fin 16, eqα.getD i 0 * algebraMap K E2 (MvPolynomial.eval r (k.vec w cnt)[i]) =
      ∑ i ∈ range 16, eqα.getD i 0 * algebraMap K E2 (MvPolynomial.eval r
        (if h : i < 16 then (k.vec w cnt)[i] else 0)) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [dif_pos i.isLt]
    rfl
  rw [e, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have h13 : ∑ i ∈ range 13, eqα.getD (i + 1 + 1 + 1) 0 * algebraMap K E2 (MvPolynomial.eval r
      (if h : i + 1 + 1 + 1 < 16 then (k.vec w cnt)[i + 1 + 1 + 1] else 0)) =
      ∑ l ∈ range k.val.length, eqα.getD (3 + l) 0 *
        algebraMap K E2 (MvPolynomial.eval r ((k.val.getD l []).toMv w)) := by
    rw [← Finset.sum_range_add_sum_Ico _ hk, Finset.sum_eq_zero (s := Ico k.val.length 13), add_zero]
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.mp hi
      rw [dif_pos (by omega), hv _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show i + 1 + 1 + 1 - 3 = i by omega, show i + 1 + 1 + 1 = 3 + i by omega]
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      rw [dif_pos (by omega), hv _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show i + 1 + 1 + 1 - 3 = i by omega, List.getD_eq_default _ _ hi'.1]
      simp [CPoly.toMv]
  rw [h13, dif_pos (by norm_num), dif_pos (by norm_num), dif_pos (by norm_num), hv _ (by norm_num),
    hv _ (by norm_num), hv _ (by norm_num)]
  simp only [kG_eq]
  norm_num
  ring

/-! ## The lvm instance's leaves -/

section Inst

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **Row `n` of table `j` of the stack**, lifted to `E2` (`0` outside the tables and their rows). -/
noncomputable def cellsAt (st : Column L.μ) (j n c : ℕ) : E2 :=
  if h : j < tabs.length then
    if h' : n < 2 ^ (tabs.get ⟨j, h⟩).τ then
      algebraMap K E2 (CPoly.ext ((inst L tabs hτ).row st ⟨j, h⟩ ⟨n, h'⟩) c)
    else 0
  else 0

theorem cellsAt_eq (st : Column L.μ) (j : Fin tabs.length) (x : Fin (2 ^ (tabs.get j).τ)) :
    cellsAt L tabs hτ st j x = fun c ↦ algebraMap K E2 (CPoly.ext ((inst L tabs hτ).row st j x) c) := by
  funext c
  simp [cellsAt, j.isLt]

/-- **The program's block of a source** of the lvm instance at `E2` (`Lvm.M3.vsrc`'s twin). -/
def vsrcG (eqα : List E2) (β : E2) : Bus.Source (inst L tabs hτ) → VBlockG
  | .boundary b => ⟨0, b.κ, {}⟩
  | .flush j f => ⟨j.val, (tabs.get j).τ,
      leafFormG eqα β ((tabs.get j).kcs.getD f.val kc0).2.1 ((tabs.get j).kcs.getD f.val kc0).2.2⟩
  | .count j c => ⟨j.val, (tabs.get j).τ, ⟨[([c.val], 1)]⟩⟩

theorem vsrcG_κ (eqα : List E2) (β : E2) (s : Bus.Source (inst L tabs hτ)) : (vsrcG L tabs hτ eqα β s).κ = s.κ := by
  cases s <;> rfl

/-- Table `j`'s flushes of side `s`, as the program's blocks. -/
theorem side_map_vsrcG (eqα : List E2) (β : E2) (s : Side) (j : Fin tabs.length) :
    (((List.finRange ((inst L tabs hτ).flushes j).length).filter fun f ↦
        decide (((inst L tabs hτ).flushes j)[f].1 = s)).map (Bus.Source.flush j)).map
      (vsrcG L tabs hτ eqα β) =
    ((tabs.get j).kcs.filter fun x ↦ decide (x.1 = s)).map fun x ↦
      (⟨j.val, (tabs.get j).τ, leafFormG eqα β x.2.1 x.2.2⟩ : VBlockG) := by
  rw [List.map_map]
  have hlen : ((inst L tabs hτ).flushes j).length = (tabs.get j).kcs.length :=
    (length_kcs _).symm
  have key := filter_finRange_getD (fun x : Side × Key × CPoly ↦ decide (x.1 = s))
    (fun x ↦ (⟨j.val, (tabs.get j).τ, leafFormG eqα β x.2.1 x.2.2⟩ : VBlockG)) kc0 (tabs.get j).kcs
  rw [← key]
  have : ∀ (n m : ℕ) (h : n = m) (P : Fin n → Bool) (Q : Fin m → Bool) (F : Fin n → VBlockG)
      (G : Fin m → VBlockG), (∀ i, P i = Q (Fin.cast h i)) → (∀ i, F i = G (Fin.cast h i)) →
      ((List.finRange n).filter P).map F = ((List.finRange m).filter Q).map G := by
    intro n m h P Q F G hP hF
    subst h
    have hP' : P = Q := funext fun i ↦ hP i
    have hF' : F = G := funext fun i ↦ hF i
    rw [hP', hF']
  refine this _ _ hlen _ _ _ _ (fun f ↦ ?_) (fun f ↦ rfl)
  show decide ((((tabs.get j).flushes)[f.val]'f.isLt).1 = s) = _
  rw [flushes_getElem]
  rfl

/-- **The program's blocks of a side are the protocol's sources**, in order (`sideBlocksV_eq`'s twin). -/
theorem sideBlocksG_eq (eqα : List E2) (β : E2) :
    sideBlocksG tabs eqα β = [(Bus.sources (inst L tabs hτ) 0).map (vsrcG L tabs hτ eqα β),
      (Bus.sources (inst L tabs hτ) 1).map (vsrcG L tabs hτ eqα β),
      (Bus.sources (inst L tabs hτ) 2).map (vsrcG L tabs hτ eqα β)] := by
  simp only [sideBlocksG, Bus.sources, Bus.sideSources, Bus.countSources, List.filter_nil,
    List.map_nil, List.nil_append, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, List.map_flatMap, zipIdx_eq_finRange, List.flatMap_map]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [side_map_vsrcG, kcs_push]
    simp [Function.comp_def]
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [side_map_vsrcG, kcs_pull]
    simp [Function.comp_def]
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [List.map_map]
    rfl

/-- Side `k`'s blocks. -/
def sideG (alphas : List E2) (β : E2) (k : ℕ) : List VBlockG := (sideBlocksG tabs (eqKernelF alphas) β).getD k []

theorem sideG_eq (alphas : List E2) (β : E2) (k : Fin 3) :
    sideG tabs alphas β k = (Bus.sources (inst L tabs hτ) k).map (vsrcG L tabs hτ (eqKernelF alphas) β) := by
  rw [sideG, sideBlocksG_eq L tabs hτ]
  fin_cases k <;> rfl

/-- **The sides fit in the leaf stacks' depth** (`Bus.Conditions.fits`). -/
theorem tot_sideG (hsc : AllSc tabs) (alphas : List E2) (β : E2) (k : Fin 3) :
    tot VBlockG.κ (sideG tabs alphas β k) ≤ 2 ^ (inst L tabs hτ).μBus := by
  have h := (condOf L tabs hτ hsc).fits k
  rw [Bus.blocks_total, Bus.leafCount] at h
  rw [sideG_eq L tabs hτ, tot, List.map_map]
  refine le_of_eq_of_le (congrArg List.sum (List.map_congr_left fun s _ ↦ ?_)) h
  simp [vsrcG_κ]

/-- A block's leaf at row `n`: its form on the row of its table. -/
noncomputable def leafAt (st : Column L.μ) (b : VBlockG) (n : ℕ) : E2 :=
  evalFG b.form (cellsAt L tabs hτ st b.tab n)

/-- **Side `k`'s leaf at index `w`**: the block's leaf inside a stacked block, `1` outside. -/
noncomputable def leafG (alphas : List E2) (β : E2) (st : Column L.μ) (k w : ℕ) : E2 :=
  1 + bump VBlockG.κ (leafAt L tabs hτ st) (stackBlocksG (sideG tabs alphas β k)) w

/-- **The product of a side's leaves** is the product of its blocks' leaves. -/
theorem prod_leafG (alphas : List E2) (β : E2) (st : Column L.μ) (k : ℕ) {N : ℕ}
    (hN : tot VBlockG.κ (sideG tabs alphas β k) ≤ N) :
    ∏ w ∈ range N, leafG L tabs hτ alphas β st k w =
      ((sideG tabs alphas β k).map fun b ↦ ∏ n ∈ range (2 ^ b.κ), leafAt L tabs hτ st b n).prod := by
  rw [Finset.range_eq_Ico]
  unfold leafG
  rw [stackBlocksG_eq, prod_bump _ _ _ _ _ (by rw [tot_perm _ (sortG_perm _)]; omega)]
  exact ((sortG_perm _).map _).prod_eq

/-- **The extension of a side's leaves** at `ζ`: `1 + Σ_b w_b·(ℓ̃_b(ζ_low) + 1)`. -/
theorem mle_leafG (alphas : List E2) (β : E2) (st : Column L.μ) (k : ℕ) (ζ : List E2)
    (hN : tot VBlockG.κ (sideG tabs alphas β k) ≤ 2 ^ ζ.length) :
    ∑ w ∈ range (2 ^ ζ.length), eqAtF ζ w * leafG L tabs hτ alphas β st k w =
      1 + ((stackBlocksG (sideG tabs alphas β k)).map fun bo ↦ eqAboveG ⟨bo.1.κ, bo.2⟩ ζ *
        ((∑ n ∈ range (2 ^ bo.1.κ), eqAtF (ζ.take bo.1.κ) n * leafAt L tabs hτ st bo.1 n) + 1)).sum := by
  unfold leafG
  rw [sum_bump _ _ _ _ _ fun bo hbo ↦ (mem_stackBlocksG hbo).2.1.trans hN, sum_eqAtF]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun bo hbo ↦ ?_)
  obtain ⟨-, hfit, hd⟩ := mem_stackBlocksG hbo
  have hκ : bo.1.κ ≤ ζ.length := by
    have h1 : 2 ^ bo.1.κ ≤ 2 ^ ζ.length := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hs : ∑ n ∈ range (2 ^ bo.1.κ), eqAtF (ζ.take bo.1.κ) n = 1 := by
    have := sum_eqAtF (ζ.take bo.1.κ)
    rwa [List.length_take, min_eq_left hκ] at this
  rw [Finset.sum_congr rfl fun n hn ↦ by rw [eqAtF_block hκ hd (Finset.mem_range.mp hn)]]
  have e : (∑ n ∈ range (2 ^ bo.1.κ), eqAtF (ζ.take bo.1.κ) n * leafAt L tabs hτ st bo.1 n) + 1 =
      ∑ n ∈ range (2 ^ bo.1.κ), eqAtF (ζ.take bo.1.κ) n * (leafAt L tabs hτ st bo.1 n + 1) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hs]
  rw [e, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ ↦ by ring

end Inst

/-! ## The fingerprint at `E2` -/

section Fingerprint

/-- The equality weight as a product over the coordinates. -/
theorem eqAtF_prod : ∀ (pt : List E2) (w : ℕ),
    eqAtF pt w = ∏ b ∈ range pt.length, if w.testBit b then pt.getD b 0 else 1 - pt.getD b 0
  | [], _ => by simp
  | r :: rs, w => by
    rw [eqAtF_succ, eqAtF_prod rs, List.length_cons, Finset.prod_range_succ', mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun b _ ↦ ?_
      simp only [Nat.testBit_succ, List.getD_cons_succ]
    · simp only [Nat.testBit_zero, List.getD_cons_zero]
      rcases Nat.mod_two_eq_zero_or_one w with h | h <;> simp [h, CharTwo.sub_eq_add]

/-- The four `α` as a vector. -/
def a4 (alphas : List E2) : Vector E2 4 := Vector.ofFn fun i ↦ alphas.getD i 0

/-- **The fingerprint** `Σ_{i < 16} eq(α, i)·t_i` is the tuple's extension at `α` (`fingerprint_eq_eval₂Mle`'s
twin). -/
theorem fp_eq_eval₂Mle {alphas : List E2} (ha : alphas.length = 4) (t : Vector K 16) :
    ∑ i : Fin 16, (eqKernelF alphas).getD i 0 * algebraMap K E2 t[i] =
      eval₂Mle (n := 4) t (algebraMap K E2) (a4 alphas) := by
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : i.val < 2 ^ alphas.length := by rw [ha]; exact i.isLt
  rw [eqKernelF_getD, if_pos hi, mul_comm, eqAtF_prod, ha]
  refine congrArg₂ (· * ·) ?_ ?_
  · show _ = (Vector.map (fun a ↦ algebraMap K E2 a) t)[i.val]
    rw [Vector.getElem_map]
    rfl
  · rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (show i.val < 2 ^ 4 from i.isLt),
      ← Fin.prod_univ_eq_prod_range (fun b ↦ if i.val.testBit b then alphas.getD b 0 else 1 - alphas.getD b 0) 4]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    simp only [a4, Fin.getElem_fin, Vector.getElem_ofFn]

end Fingerprint

/-! ## The sides' products -/

section Products

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- A table's rows are all executed (no padding row). -/
theorem executed_lvm (j : Fin tabs.length) :
    (inst L tabs hτ).executed j = List.finRange (2 ^ (tabs.get j).τ) :=
  List.filter_eq_self.mpr fun x _ ↦ by simp

/-- **A flush block's leaves** multiply `β − t̃(α)` over its tuples. -/
theorem prod_leafAt_flush (hkey : KeysOk tabs) {alphas : List E2} (ha : alphas.length = 4) (β : E2)
    (st : Column L.μ) (j : Fin tabs.length) (f : Fin ((inst L tabs hτ).flushes j).length) :
    ∏ n ∈ range (2 ^ (vsrcG L tabs hτ (eqKernelF alphas) β (.flush j f)).κ),
        leafAt L tabs hτ st (vsrcG L tabs hτ (eqKernelF alphas) β (.flush j f)) n =
      ((Bus.Source.busTuples (I := inst L tabs hτ) st (.flush j f)).map fun t ↦
        β - eval₂Mle (n := 4) t (algebraMap K E2) (a4 alphas)).prod := by
  have hkv := kcs_getD_val _ (hkey _ (List.get_mem _ j)) f.val
  show ∏ n ∈ range (2 ^ (tabs.get j).τ), evalFG (leafFormG (eqKernelF alphas) β
      ((tabs.get j).kcs.getD f.val kc0).2.1 ((tabs.get j).kcs.getD f.val kc0).2.2) (cellsAt L tabs hτ st j n) = _
  simp only [Bus.Source.busTuples, executed_lvm, List.map_map]
  rw [← Fin.prod_univ_def, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  rw [cellsAt_eq L tabs hτ st j x, evalFG_leafFormG, Function.comp_apply, CharTwo.sub_eq_add,
    ← fp_eq_eval₂Mle ha]
  have hft : ∀ i : Fin 16, (Bus.flushTuple (I := inst L tabs hτ) st j f x)[i] = MvPolynomial.eval ((inst L tabs hτ).row st j x)
      ((((tabs.get j).kcs.getD f.val kc0).2.1.vec (tabs.get j).w ((tabs.get j).kcs.getD f.val kc0).2.2)[i]) := by
    intro i
    simp only [Bus.flushTuple, Bus.flushPolys, Fin.getElem_fin, Vector.getElem_map]
    have hfl := flushes_getElem (tabs.get j) f.val f.isLt
    simp only [hfl]
  simp only [hft]
  rw [sum_vecG (w := (tabs.get j).w) (r := (inst L tabs hτ).row st j x) _ _ _ hkv]
  ring

/-- **The product of a push or pull side's leaves** is the grand product polynomial of its tuples at `(α, β)`. -/
theorem prod_leafG_side (hsc : AllSc tabs) (hkey : KeysOk tabs) {alphas : List E2} (ha : alphas.length = 4)
    (β : E2) (st : Column L.μ) (k : Fin 3) (s : Side) (hk : Bus.sources (inst L tabs hτ) k = Bus.sideSources _ s) :
    ∏ w ∈ range (2 ^ (inst L tabs hτ).μBus), leafG L tabs hτ alphas β st k w =
      ((((inst L tabs hτ).tuples st s : Multiset (Vector K 16))).map fun t ↦
        β - eval₂Mle (n := 4) t (algebraMap K E2) (a4 alphas)).prod := by
  rw [prod_leafG L tabs hτ alphas β st k (tot_sideG L tabs hτ hsc alphas β k), sideG_eq L tabs hτ, hk,
    Multiset.map_coe, Multiset.prod_coe, ← ((Bus.sideTuples_perm (I := inst L tabs hτ) st s).map _).prod_eq, Bus.sideTuples,
    prod_map_flatMapG, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun src hs ↦ ?_)
  cases src with
  | boundary b => simp [Bus.sideSources] at hs
  | flush j f => exact prod_leafAt_flush L tabs hτ hkey ha β st j f
  | count j c => simp [Bus.sideSources] at hs

/-- The product as the grand product polynomial (`eval₂_grandProductPoly`). -/
theorem prod_tuples_eq_eval₂ (M : Multiset (Vector K 16)) (alphas : List E2) (β : E2) :
    (M.map fun t ↦ β - eval₂Mle (n := 4) t (algebraMap K E2) (a4 alphas)).prod =
      MvPolynomial.eval₂ (algebraMap K E2) (fun i ↦ i.elim β fun j ↦ (a4 alphas)[j])
        (grandProductPoly (n := 4) M) :=
  (eval₂_grandProductPoly (n := 4) M (algebraMap K E2) (a4 alphas) β).symm

/-- **A nonzero count product**: every count cell is nonzero (`Bus.countsNonzero_of_prod`'s twin). -/
theorem countsNonzero_of_leafG (hsc : AllSc tabs) (alphas : List E2) (β : E2) (st : Column L.μ)
    (hnz : ∏ w ∈ range (2 ^ (inst L tabs hτ).μBus), leafG L tabs hτ alphas β st 2 w ≠ 0) :
    (inst L tabs hτ).CountsNonzero st := by
  have h2 : sideG tabs alphas β 2 = _ := sideG_eq L tabs hτ alphas β 2
  rw [prod_leafG L tabs hτ alphas β st 2 (tot_sideG L tabs hτ hsc alphas β 2), h2, List.map_map] at hnz
  intro j c hc x hx h0
  refine hnz (List.prod_eq_zero (List.mem_map.mpr ⟨.count j c, ?_,
    Finset.prod_eq_zero (i := x.val) (Finset.mem_range.mpr x.isLt) ?_⟩))
  · change _ ∈ Bus.countSources _
    simp only [Bus.countSources, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨j, c, hc, rfl⟩
  · simp only [vsrcG, leafAt]
    rw [cellsAt_eq L tabs hτ st j x]
    simp only [evalFG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
      List.sum_nil, one_mul, mul_one, add_zero, CPoly.ext, dif_pos c.isLt]
    simp only [M3Instance.row]
    rw [h0, map_zero]

end Products

end Lvm6.Mb
end -- part Lvm6MbBus

/-! ### Part `Lvm6MbLin` (was its own module) -/
section

/-!
# The three claims at `E2` are the leaves' extensions

On tableless tables (`mbLinB6`: no constraint, every key and count coordinate a constant or one column, every committed
column on `C_main`) a block's leaf is affine in its table's row. So a side's leaf extension at the GKR point `ζ`
(`mle_leafG`: `1 + Σ_b w_b·(ℓ̃_b + 1)`) is, table by table, the side's form at the columns' extensions at `ζ.take τ`:
the committed columns' blocks of `C_main` (`blkValG`) with their coefficients and a constant (constant terms and fixed
columns at `mleFixG`). The claim `sumClaimG ν parts value` holds on `C_main` iff the parts' blocks sum to the value
(`holds_sumClaimG_iff`), so:

* **`mle_of_claims`**: when the three claims `mbClaimsG` of what the bus phase read hold on `qm`, every side's leaves
  on the stack `stackOf qm qr` have extension `values[s]` at the point (the GKR's output relation).

The column reading (`column_stackOfG`) is season 1's `column_stackOf` (`P/LvmM3MidCert.lean`) on `Lvm6MbProg`'s
`stackOf`.
-/

set_option autoImplicit false

namespace Lvm6.Mb

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm.M3 CompPoly CMlPolynomialEval
open Finset

/-! ## The stack of the two commitments -/

section Stack

variable (L : Lay)

/-- Cell `n` of commitment `rec` (`C_rec` if `rec`, else `C_main`; `0` past it). -/
def comCellG (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (n : ℕ) : K :=
  if rec then (if h : n < 2 ^ L.nuRec then qr.values[n] else 0)
  else (if h : n < 2 ^ L.nuMain then qm.values[n] else 0)

/-- The block of `2^τ` cells of commitment `rec` from `off`. -/
def comBlockG (qm : Column L.nuMain) (qr : Column L.nuRec) (rec : Bool) (τ off : ℕ) : Column τ :=
  ⟨Vector.ofFn fun x ↦ comCellG L qm qr rec (off + x.val)⟩

theorem stackOf_getElem (qm : Column L.nuMain) (qr : Column L.nuRec) (n : ℕ) (hn : n < 2 ^ L.μ) :
    (stackOf L qm qr).values[n] = if n < 2 ^ L.nuMain then comCellG L qm qr false n
      else comCellG L qm qr true (n - 2 ^ L.nuMain) := by
  simp only [stackOf, Vector.getElem_ofFn, comCellG]
  by_cases h : n < 2 ^ L.nuMain
  · simp [h]
  · simp [h]

variable (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A committed column read off the stack of the commitments is its block** (under `LayOk`; season 1's
`column_stackOf`). -/
theorem column_stackOfG (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (j : Fin tabs.length) (i : Fin (tabs.get j).w) {rec : Bool} {off : ℕ}
    (hcol : (tabs.get j).cols[i.val]? = some (.com rec off)) :
    (inst L tabs hτ).column (stackOf L qm qr) ⟨j, i⟩ = comBlockG L qm qr rec (tabs.get j).τ off := by
  have hal := hlay (tabs.get j) (List.get_mem _ _) i.val i.isLt
  unfold Aligned at hal
  rw [hcol] at hal
  obtain ⟨hdvd, hfit, hnu⟩ := hal
  have hder : (inst L tabs hτ).derived ⟨j, i⟩ = none := by
    simp only [inst, Tab.fixedOf, hcol, Option.map_none]
  have hτμ : (tabs.get j).τ ≤ L.μ := hτ _ (List.get_mem _ _)
  have hso : stackOff L (tabs.get j) i.val = off + if rec then 2 ^ L.nuMain else 0 := by
    simp only [stackOff, hcol]
  have hτm : (tabs.get j).τ ≤ L.nuMain := by
    have h1 : 2 ^ (tabs.get j).τ ≤ 2 ^ (if rec then L.nuRec else L.nuMain) := by (clear * - hfit hso; omega)
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    cases rec
    · simpa using h2
    · exact le_trans (by simpa using h2) hnu
  have hdvd' : 2 ^ (tabs.get j).τ ∣ stackOff L (tabs.get j) i.val := by
    rw [hso]
    refine Nat.dvd_add hdvd ?_
    split
    · exact Nat.pow_dvd_pow 2 hτm
    · exact Nat.dvd_zero _
  have hfit' : stackOff L (tabs.get j) i.val + 2 ^ (tabs.get j).τ ≤ 2 ^ L.μ := by
    rw [hso, Lay.μ, pow_succ]
    have : 2 ^ L.nuRec ≤ 2 ^ L.nuMain := Nat.pow_le_pow_right (by norm_num) hnu
    cases rec <;> simp at hfit ⊢ <;> (clear * - hfit this; omega)
  have hsel : (selOf L (tabs.get j) hτμ i.val).val = stackOff L (tabs.get j) i.val / 2 ^ (tabs.get j).τ := by
    simp only [selOf, dif_pos (And.intro hdvd' hfit')]
  have hread := readWith_liftAt (fun c : (inst L tabs hτ).ColumnId ↦ hτ _ (List.get_mem _ c.1))
    (fun c ↦ selOf L (tabs.get c.1) (hτ _ (List.get_mem _ c.1)) c.2) (stackOf L qm qr) ⟨j, i⟩
  have hcolv : (inst L tabs hτ).column (stackOf L qm qr) ⟨j, i⟩ =
      (inst L tabs hτ).layout.read (stackOf L qm qr) ⟨j, i⟩ := by
    unfold M3Instance.column; rw [hder]; rfl
  rw [hcolv]
  show (⟨((inst L tabs hτ).layout.read (stackOf L qm qr) ⟨j, i⟩).values⟩ : Column _) =
    ⟨(comBlockG L qm qr rec (tabs.get j).τ off).values⟩
  congr 1
  change (Layout.readWith (fun c : (inst L tabs hτ).ColumnId ↦ liftAt (hτ _ (List.get_mem _ c.1))
    (selOf L (tabs.get c.1) (hτ _ (List.get_mem _ c.1)) c.2)) (stackOf L qm qr) ⟨j, i⟩).values = _
  rw [hread]
  apply Vector.ext
  intro x hx
  have hxl : x < 2 ^ (tabs.get j).τ := hx
  rw [slice_getElem_nat _ _ hxl, Vector.getElem_cast, stackOf_getElem]
  simp only [comBlockG, Vector.getElem_ofFn]
  have key : ∀ n, n = off + x + (if rec then 2 ^ L.nuMain else 0) →
      (if n < 2 ^ L.nuMain then comCellG L qm qr false n else comCellG L qm qr true (n - 2 ^ L.nuMain)) =
        comCellG L qm qr rec (off + x) := by
    intro n hn
    subst hn
    cases rec
    · have h1 : off + x < 2 ^ L.nuMain := by
        simp only [Bool.false_eq_true, ite_false] at hfit; (clear * - hτ hτμ hxl hfit; omega)
      simp [h1]
    · have h2 : ¬ off + x + 2 ^ L.nuMain < 2 ^ L.nuMain := by (clear * - hτ hτμ; omega)
      simp [h2]
  refine key _ ?_
  show x + 2 ^ (tabs.get j).τ * (selOf L (tabs.get j) hτμ i.val).val = _
  rw [hsel, Nat.mul_div_cancel' hdvd', hso]; (clear * - hτ hτμ; omega)

/-- **A committed `C_main` cell of a row** (`mbLinB6`: no `C_rec` column). -/
theorem cellsAt_com (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec) (j : Fin tabs.length)
    {c off : ℕ} (hcol : (tabs.get j).cols[c]? = some (.com false off)) {n : ℕ} (hn : n < 2 ^ (tabs.get j).τ) :
    cellsAt L tabs hτ (stackOf L qm qr) j n c = algebraMap K E2 (qm.values.getD (off + n) 0) := by
  have hcw : c < (tabs.get j).w := (List.getElem?_eq_some_iff.mp hcol).1
  have hfit := hlay (tabs.get j) (List.get_mem _ _) c hcw
  unfold Aligned at hfit
  rw [hcol] at hfit
  obtain ⟨-, hf2, -⟩ := hfit
  simp only [Bool.false_eq_true, ite_false] at hf2
  have h1 : off + n < 2 ^ L.nuMain := by omega
  have := cellsAt_eq L tabs hτ (stackOf L qm qr) j ⟨n, hn⟩
  rw [this]
  simp only [CPoly.ext, dif_pos hcw, M3Instance.row]
  rw [column_stackOfG L tabs hτ hlay qm qr j ⟨c, hcw⟩ hcol]
  simp [comBlockG, comCellG, h1, Vector.getD, Vector.get_eq_getElem]

/-- **A fixed cell of a row**. -/
theorem cellsAt_fix (st : Column L.μ) (j : Fin tabs.length) {c : ℕ} {f : ℕ → Lvm.FK} {ev : List Lvm.FE → Lvm.FE}
    (hcol : (tabs.get j).cols[c]? = some (.fix f ev)) {n : ℕ} (hn : n < 2 ^ (tabs.get j).τ) :
    cellsAt L tabs hτ st j n c = kG (f n) := by
  have hcw : c < (tabs.get j).w := (List.getElem?_eq_some_iff.mp hcol).1
  have := cellsAt_eq L tabs hτ st j ⟨n, hn⟩
  rw [this]
  have hfo : (tabs.get j).fixedOf c = some f := by
    show (match (tabs.get j).cols[c]? with | some (.fix f _) => some f | _ => none) = _
    rw [hcol]
  simp only [CPoly.ext, dif_pos hcw, M3Instance.row, M3Instance.column]
  simp only [inst, hfo, Option.map_some, Option.elim_some, fixedColumn, kG_eq]
  simp [Vector.get_eq_getElem]

/-- A cell past the width is `0`. -/
theorem cellsAt_none (st : Column L.μ) (j n : ℕ) {c : ℕ} (hc : ∀ h : j < tabs.length, (tabs.get ⟨j, h⟩).w ≤ c) :
    cellsAt L tabs hτ st j n c = 0 := by
  unfold cellsAt
  split_ifs with h1 h2
  · show algebraMap K E2 (CPoly.ext _ c) = 0
    unfold CPoly.ext
    rw [dif_neg (not_lt.mpr (hc h1)), map_zero]
  · rfl
  · rfl

end Stack

/-! ## Claims on `C_main` -/

section Claims

/-- A block's extension at `z` on `C_main`: `Σ_n eq(z, n)·q[index + n]`. -/
noncomputable def blkValG {ν : ℕ} (q : Column ν) (blk : LeanVM.Protocol.Verifier.Placement) (z : List E2) : E2 :=
  ∑ n ∈ range (2 ^ blk.variableCount), eqAtF z n * algebraMap K E2 (q.values.getD (blk.index + n) 0)

theorem bitsF_take : ∀ (x m v : ℕ), v ≤ m → (bitsF x m : List E2).take v = bitsF x v
  | _, _, 0, _ => by simp [bitsF]
  | x, m + 1, v + 1, h => by
    rw [bitsF, bitsF, List.take_succ_cons, bitsF_take (x / 2) m v (by omega)]
  | _, 0, _ + 1, h => by omega

theorem bitsF_drop : ∀ (x m v : ℕ), v ≤ m → (bitsF x m : List E2).drop v = bitsF (x / 2 ^ v) (m - v)
  | x, _, 0, _ => by simp
  | x, m + 1, v + 1, h => by
    rw [bitsF, List.drop_succ_cons, bitsF_drop (x / 2) m v (by omega), Nat.div_div_eq_div_mul, pow_succ',
      Nat.add_sub_add_right]
  | _, 0, _ + 1, h => by omega

/-- **A part's weight at a cube point**: `eq_above·eq(z, ·)` is the equality weight of the block's stack point. -/
theorem part_weight {ν v off x : ℕ} {z : List E2} (hz : z.length = v) (hv : v ≤ ν) (hoff : off / 2 ^ v < 2 ^ (ν - v))
    (hx : x < 2 ^ ν) :
    eqAboveG ⟨v, off⟩ (bitsF x ν) * eqEvalF z ((bitsF x ν).take v) =
      eqAtF (z ++ bitsF (off / 2 ^ v) (ν - v)) x := by
  rw [eqAboveG_eq, bitsF_drop _ _ _ hv, bitsF_take _ _ _ hv, ← hz, eqEvalF_bitsF, eqAtF_append, hz,
    eqAtF_bitsF_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' hv]; exact hx)) hoff,
    eqAtF_bitsF_lt hoff (Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.add_sub_cancel' hv]; exact hx))]
  by_cases h : off / 2 ^ v = x / 2 ^ v
  · simp [h, mul_comm]
  · simp [h, Ne.symm h]

theorem sum_listSumG {ι α : Type} (s : Finset ι) (l : List α) (f : ι → α → E2) :
    ∑ x ∈ s, (l.map (f x)).sum = (l.map fun a ↦ ∑ x ∈ s, f x a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/-- **A `sumClaimG` claim on `C_main`** holds iff its parts' block extensions sum to its value. -/
theorem holds_sumClaimG_iff (ν : ℕ) (parts : List (E2 × LeanVM.Protocol.Verifier.Placement × List E2)) (val : E2)
    (q : Column ν) (hP : ∀ p ∈ parts, p.2.2.length = p.2.1.variableCount ∧
      2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ ν) :
    ClaimE.Holds ν (sumClaimG ν parts val).onStack q ↔ (parts.map fun p ↦ p.1 * blkValG q p.2.1 p.2.2).sum = val := by
  unfold ClaimE.Holds
  refine Eq.congr_left ?_
  have key : ∀ x : Fin (2 ^ ν), (sumClaimG ν parts val).onStack.1 (bitsF x ν) * algebraMap K E2 (q.values.getD x 0) =
      (parts.map fun p ↦ p.1 * (eqAboveG p.2.1 (bitsF x ν) * eqEvalF p.2.2 ((bitsF x ν).take p.2.1.variableCount)) *
        algebraMap K E2 (q.values.getD x 0)).sum := by
    intro x
    have h1 : eqAboveG ⟨ν, 0⟩ (bitsF x ν) = 1 := by
      rw [eqAboveG_eq, List.drop_eq_nil_of_le (by simp)]
      rfl
    have h2 : (bitsF x ν : List E2).take ν = bitsF x ν := List.take_of_length_le (by simp)
    show eqAboveG ⟨ν, 0⟩ (bitsF x ν) * sumF (parts.map fun p ↦
        p.1 * eqAboveG p.2.1 ((bitsF x ν).take ν) * eqEvalF p.2.2 (((bitsF x ν).take ν).take p.2.1.variableCount)) *
        algebraMap K E2 (q.values.getD x 0) = _
    rw [h1, h2, one_mul, sumF_eq_sum, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun p _ ↦ by ring)
  rw [Finset.sum_congr rfl fun x _ ↦ key x, sum_listSumG]
  refine congrArg List.sum (List.map_congr_left fun p hp ↦ ?_)
  obtain ⟨hz, hal, hfit⟩ := hP p hp
  obtain ⟨co, ⟨v, off⟩, z⟩ := p
  simp only at hz hal hfit ⊢
  have hv : v ≤ ν := by
    have : 2 ^ v ≤ 2 ^ ν := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hoff : off / 2 ^ v < 2 ^ (ν - v) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos v), ← pow_add, Nat.sub_add_cancel hv]
    have := Nat.two_pow_pos v
    omega
  rw [blkValG, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ co * (eqAboveG ⟨v, off⟩ (bitsF x ν) * eqEvalF z ((bitsF x ν).take v)) *
    algebraMap K E2 (q.values.getD x 0)) (2 ^ ν)]
  rw [Finset.sum_congr rfl fun x hx ↦ by
    rw [part_weight hz hv hoff (Finset.mem_range.mp hx)]]
  have hl : (bitsF (off / 2 ^ v) (ν - v) : List E2).length = ν - v := bitsF_length _ _
  have e := col_splitF (F := E2) (a := z) (s := bitsF (off / 2 ^ v) (ν - v)) hz
    (fun x ↦ algebraMap K E2 (q.values.getD x 0))
  rw [hl, sum_eqAtF_bitsF hoff, Nat.add_sub_cancel' hv] at e
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [e]
  refine congrArg (co * ·) (Finset.sum_congr rfl fun n _ ↦ ?_)
  obtain ⟨m, rfl⟩ := hal
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos v), Nat.add_comm n]

end Claims

/-! ## Affine forms -/

section Affine

/-- A monomial of at most one column, named in `N`. -/
def TermIn (N : List ℕ) (m : List ℕ) : Prop := m = [] ∨ ∃ c ∈ N, m = [c]

/-- A form of monomials of at most one column is affine in the column values. -/
theorem evalFG_affine (T : List (List ℕ × E2)) (hT : ∀ m ∈ T, m.1.length ≤ 1) (s : Finset ℕ) (w : ℕ → E2)
    (hw : ∑ x ∈ s, w x = 1) (col : ℕ → ℕ → E2) :
    evalFG ⟨T⟩ (fun i ↦ ∑ x ∈ s, w x * col x i) = ∑ x ∈ s, w x * evalFG ⟨T⟩ (col x) := by
  simp only [evalFG]
  induction T with
  | nil => simp
  | cons m T ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [ih fun m' hm' ↦ hT m' (List.mem_cons_of_mem _ hm')]
    congr 1
    have h1 := hT m List.mem_cons_self
    rcases hc : m.1 with _ | ⟨i, _ | ⟨i', l⟩⟩
    · simp only [List.map_nil, List.prod_nil, mul_one]
      rw [← Finset.sum_mul, hw, one_mul]
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    · rw [hc] at h1; simp at h1

/-- The key columns of a table. -/
def keyColsG (t : Tab) : List ℕ :=
  (t.reads.map (·.1) ++ t.seeds.map (·.1)).flatMap fun k ↦ (k.addr :: k.val).flatMap fun P ↦ P.flatMap (·.2)

/-- The columns side `s` of table `t` names (`sideColsG`'s list before the range filter). -/
def namedG (t : Tab) (s : ℕ) : List ℕ :=
  if s = 0 then keyColsG t ++ t.reads.map (·.2)
  else if s = 1 then keyColsG t ++ t.reads.map (·.2) ++ t.seeds.map (·.2)
  else t.counts.map (·.val)

theorem sideColsG_eq (t : Tab) (s : ℕ) :
    sideColsG t s = (List.range t.w).filter fun c ↦ (namedG t s).contains c := rfl

theorem termIn_cpoly {N : List ℕ} {P : CPoly} (hP : cpolyLinB P = true)
    (hN : ∀ m ∈ P, ∀ c ∈ m.2, c ∈ N) : ∀ m ∈ P, TermIn N m.2 := by
  intro m hm
  have h1 : m.2.length ≤ 1 := by simpa using List.all_eq_true.mp hP m hm
  rcases hc : m.2 with _ | ⟨c, _ | ⟨d, l⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨c, hN m hm c (by simp [hc]), rfl⟩
  · rw [hc] at h1; simp at h1

theorem termIn_cpolyForm {N : List ℕ} (w : E2) (P : CPoly) (hP : ∀ m ∈ P, TermIn N m.2) :
    ∀ m ∈ (cpolyFormG w P).terms, TermIn N m.1 := by
  intro m hm
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
  exact hP m' hm'

theorem termIn_leaf {N : List ℕ} (eqα : List E2) (β : E2) (k : Key) (cnt : CPoly)
    (hA : ∀ m ∈ k.addr, TermIn N m.2) (hC : ∀ m ∈ cnt, TermIn N m.2)
    (hV : ∀ P ∈ k.val, ∀ m ∈ P, TermIn N m.2) :
    ∀ m ∈ (leafFormG eqα β k cnt).terms, TermIn N m.1 := by
  intro m hm
  obtain ⟨f, hf, hmf⟩ := List.mem_flatMap.mp hm
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hf
  rcases hf with (rfl | rfl | rfl) | ⟨⟨P, l⟩, hPl, rfl⟩
  · obtain rfl := List.mem_singleton.mp hmf
    exact Or.inl rfl
  · exact termIn_cpolyForm _ _ hA m hmf
  · exact termIn_cpolyForm _ _ hC m hmf
  · exact termIn_cpolyForm _ _ (hV P (List.fst_mem_of_mem_zipIdx hPl)) m hmf

theorem termIn_keyLeaf {t : Tab} {N : List ℕ} (hN : ∀ c ∈ keyColsG t, c ∈ N)
    (hk : ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), cpolyLinB k.addr = true ∧ ∀ P ∈ k.val, cpolyLinB P = true)
    (eqα : List E2) (β : E2) {k : Key} (hkm : k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1)) {cnt : CPoly}
    (hC : ∀ m ∈ cnt, TermIn N m.2) :
    ∀ m ∈ (leafFormG eqα β k cnt).terms, TermIn N m.1 := by
  have hl := hk k hkm
  refine termIn_leaf eqα β k cnt (termIn_cpoly hl.1 fun m hm c hc ↦ hN c ?_) hC
    fun P hP ↦ termIn_cpoly (hl.2 P hP) fun m hm c hc ↦ hN c ?_
  · exact List.mem_flatMap.mpr ⟨k, hkm, List.mem_flatMap.mpr ⟨_, List.mem_cons_self,
      List.mem_flatMap.mpr ⟨m, hm, hc⟩⟩⟩
  · exact List.mem_flatMap.mpr ⟨k, hkm, List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem _ hP,
      List.mem_flatMap.mpr ⟨m, hm, hc⟩⟩⟩

theorem termIn_one {N : List ℕ} (c : Lvm.FK) (i : ℕ) (hi : i ∈ N) :
    ∀ m ∈ ([(c, [i])] : CPoly), TermIn N m.2 := by
  intro m hm
  obtain rfl := List.mem_singleton.mp hm
  exact Or.inr ⟨i, hi, rfl⟩

/-- **A block of a side on tableless tables**: of a table `j`, its height, every monomial a constant or one column
the side names. -/
theorem block_facts {tabs : List Tab} (hlin : mbLinB6 tabs = true) (eqα : List E2) (β : E2) (s : ℕ) {b : VBlockG}
    (hb : b ∈ (sideBlocksG tabs eqα β).getD s []) :
    ∃ j : Fin tabs.length, b.tab = j ∧ b.κ = (tabs.get j).τ ∧
      ∀ m ∈ b.form.terms, TermIn (namedG (tabs.get j) s) m.1 := by
  have hz : ∀ {tt : Tab} {j' : ℕ}, (tt, j') ∈ tabs.zipIdx → ∃ h : j' < tabs.length, tt = tabs.get ⟨j', h⟩ := by
    intro tt j' hz
    obtain ⟨h1, h2⟩ := List.mem_zipIdx' hz
    exact ⟨h1, h2⟩
  have hk : ∀ t ∈ tabs, ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1),
      cpolyLinB k.addr = true ∧ ∀ P ∈ k.val, cpolyLinB P = true := by
    intro t ht k hkm
    have h := List.all_eq_true.mp hlin t ht
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact h.1.2 k hkm
  rcases s with _ | _ | _ | s
  · simp only [sideBlocksG, List.getD_cons_zero, List.mem_flatMap, List.mem_append, List.mem_map] at hb
    obtain ⟨⟨tt, j'⟩, hzm, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)⟩ := hb <;> obtain ⟨hj, rfl⟩ := hz hzm
    · refine ⟨⟨j', hj⟩, rfl, rfl, termIn_keyLeaf (fun c hc ↦ ?_) (hk _ (List.get_mem _ _)) _ _
        (List.mem_append_left _ (List.mem_map_of_mem hr)) (termIn_one _ _ ?_)⟩
      · exact List.mem_append_left _ hc
      · exact List.mem_append_right _ (List.mem_map_of_mem hr)
    · refine ⟨⟨j', hj⟩, rfl, rfl, termIn_keyLeaf (fun c hc ↦ ?_) (hk _ (List.get_mem _ _)) _ _
        (List.mem_append_right _ (List.mem_map_of_mem hr)) (fun m hm ↦ ?_)⟩
      · exact List.mem_append_left _ hc
      · simp only [CPoly.const, List.mem_singleton] at hm; subst hm; exact Or.inl rfl
  · simp only [sideBlocksG, List.getD_cons_succ, List.getD_cons_zero, List.mem_flatMap, List.mem_append,
      List.mem_map] at hb
    obtain ⟨⟨tt, j'⟩, hzm, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)⟩ := hb <;> obtain ⟨hj, rfl⟩ := hz hzm
    · refine ⟨⟨j', hj⟩, rfl, rfl, termIn_keyLeaf (fun c hc ↦ ?_) (hk _ (List.get_mem _ _)) _ _
        (List.mem_append_left _ (List.mem_map_of_mem hr)) (termIn_one _ _ ?_)⟩
      · exact List.mem_append_left _ (List.mem_append_left _ hc)
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hr))
    · refine ⟨⟨j', hj⟩, rfl, rfl, termIn_keyLeaf (fun c hc ↦ ?_) (hk _ (List.get_mem _ _)) _ _
        (List.mem_append_right _ (List.mem_map_of_mem hr)) (termIn_one _ _ ?_)⟩
      · exact List.mem_append_left _ (List.mem_append_left _ hc)
      · exact List.mem_append_right _ (List.mem_map_of_mem hr)
  · simp only [sideBlocksG, List.getD_cons_succ, List.getD_cons_zero, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨⟨tt, j'⟩, hzm, ⟨c, hc, rfl⟩⟩ := hb
    obtain ⟨hj, rfl⟩ := hz hzm
    refine ⟨⟨j', hj⟩, rfl, rfl, fun m hm ↦ ?_⟩
    obtain rfl := List.mem_singleton.mp hm
    exact Or.inr ⟨c.val, List.mem_map_of_mem hc, rfl⟩
  · simp [sideBlocksG] at hb

end Affine

/-! ## A table's form splits into its constant and its committed blocks -/

section Split

/-- Column `c`'s committed block value (`0` if `c` is not committed). -/
def comValG (t : Tab) (B : LeanVM.Protocol.Verifier.Placement → List E2 → E2) (z : List E2) (c : ℕ) : E2 :=
  match t.cols[c]? with
  | some (ColSrc.com _ off) => B ⟨t.τ, off⟩ z
  | _ => 0

theorem coefG_cons (m : List ℕ × E2) (T : List (List ℕ × E2)) (c : ℕ) :
    coefG ⟨m :: T⟩ c = (if m.1 = [c] then m.2 else 0) + coefG ⟨T⟩ c := by
  simp only [coefG, sumF_eq_sum, List.filter_cons, beq_iff_eq]
  split <;> simp

theorem constG_cons (t : Tab) (m : List ℕ × E2) (T : List (List ℕ × E2)) (pt : List E2) :
    constG t ⟨m :: T⟩ pt = (match m.1 with
      | [] => m.2
      | [c] => match t.cols[c]? with
        | some (ColSrc.fix fc _) => m.2 * mleFixG t.τ fc pt
        | _ => 0
      | _ => 0) + constG t ⟨T⟩ pt := by
  simp only [constG, sumF_eq_sum, List.map_cons, List.sum_cons]
  rfl

theorem sum_parts_tableG (t : Tab) (T : List (List ℕ × E2)) (SC : List ℕ)
    (B : LeanVM.Protocol.Verifier.Placement → List E2 → E2) (z : List E2) :
    ((SC.filterMap fun c ↦ match t.cols[c]? with
        | some (ColSrc.com _ off) => some (coefG ⟨T⟩ c, (⟨t.τ, off⟩ : LeanVM.Protocol.Verifier.Placement), z)
        | _ => none).map fun p ↦ p.1 * B p.2.1 p.2.2).sum =
      (SC.map fun c ↦ coefG ⟨T⟩ c * comValG t B z c).sum := by
  induction SC with
  | nil => simp
  | cons c SC ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    unfold comValG
    rcases hcol : t.cols[c]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩) <;> simp [hcol]

/-- **A table's form on a tableless side splits** into its constant (constant terms, fixed columns at their
extensions) and its committed columns' blocks with their coefficients. -/
theorem evalFG_split (t : Tab) (T : List (List ℕ × E2)) (N SC : List ℕ) (e : ℕ → E2) (pt z : List E2)
    (B : LeanVM.Protocol.Verifier.Placement → List E2 → E2) (hT : ∀ m ∈ T, TermIn N m.1)
    (hN : ∀ c ∈ N, c < t.w → c ∈ SC) (hSC : SC.Nodup) (hnone : ∀ c, t.w ≤ c → e c = 0)
    (hfix : ∀ c f ev, t.cols[c]? = some (.fix f ev) → e c = mleFixG t.τ f pt)
    (hcom : ∀ c rec off, t.cols[c]? = some (.com rec off) → e c = B ⟨t.τ, off⟩ z) :
    evalFG ⟨T⟩ e = constG t ⟨T⟩ pt +
      ((SC.filterMap fun c ↦ match t.cols[c]? with
        | some (ColSrc.com _ off) => some (coefG ⟨T⟩ c, (⟨t.τ, off⟩ : LeanVM.Protocol.Verifier.Placement), z)
        | _ => none).map fun p ↦ p.1 * B p.2.1 p.2.2).sum := by
  rw [sum_parts_tableG, ← List.sum_toFinset _ hSC]
  induction T with
  | nil => simp [evalFG, constG, coefG, sumF_eq_sum]
  | cons m T ih =>
    have ih' := ih fun m' hm' ↦ hT m' (List.mem_cons_of_mem _ hm')
    simp only [evalFG, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', constG_cons]
    simp only [coefG_cons, add_mul, Finset.sum_add_distrib]
    suffices h : m.2 * (m.1.map e).prod = (match m.1 with
        | [] => m.2
        | [c] => match t.cols[c]? with
          | some (ColSrc.fix fc _) => m.2 * mleFixG t.τ fc pt
          | _ => 0
        | _ => 0) + ∑ c ∈ SC.toFinset, (if m.1 = [c] then m.2 else 0) * comValG t B z c by
      rw [h]; ring
    rcases hT m List.mem_cons_self with hm | ⟨c0, hc0, hm⟩
    · simp [hm]
    · rw [hm, Finset.sum_eq_single c0 (fun c _ hc ↦ by simp [Ne.symm hc]) (fun h ↦ ?_)]
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ite_true]
        unfold comValG
        rcases hcol : t.cols[c0]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩)
        · simp [hnone c0 (List.getElem?_eq_none_iff.mp hcol)]
        · simp [hcom c0 rec off hcol]
        · simp [hfix c0 f ev hcol]
      · rcases hcol : t.cols[c0]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩)
        · simp [comValG, hcol]
        · exact absurd (List.mem_toFinset.mpr (hN c0 hc0 (List.getElem?_eq_some_iff.mp hcol).1)) h
        · simp [comValG, hcol]

end Split

/-! ## The claims give the leaves' extensions -/

section Main

theorem evalFG_bucketG (side : List (VBlockG × E2)) (j : ℕ) (v : ℕ → E2) :
    evalFG ⟨bucketG side j⟩ v = ((side.filter fun bw ↦ bw.1.tab == j).map fun bw ↦ bw.2 * evalFG bw.1.form v).sum := by
  simp only [evalFG, bucketG, sum_map_flatMapG, List.map_map, Function.comp_def]
  rw [List.map_reverse, List.sum_reverse]
  refine congrArg List.sum (List.map_congr_left fun bw _ ↦ ?_)
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun t _ ↦ by ring)

/-- Grouping a sum by table. -/
theorem sum_group {α : Type} (N : ℕ) (key : α → ℕ) (g : α → E2) :
    ∀ (l : List α), (∀ a ∈ l, key a < N) →
      ∑ j : Fin N, ((l.filter fun a ↦ key a == j.val).map g).sum = (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_group N key g l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    rw [Finset.sum_congr rfl (g := fun j : Fin N ↦ (if key a = j.val then g a else 0) +
        ((l.filter fun a ↦ key a == j.val).map g).sum) fun j _ ↦ by
      by_cases hk : key a = j.val <;> simp [hk],
      Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons,
      Finset.sum_eq_single (⟨key a, ha⟩ : Fin N) (fun j _ hj ↦ by
        rw [if_neg]; intro hk; exact hj (Fin.ext hk.symm)) (by simp)]
    simp

/-- A sum over `zipIdx` is a sum over the positions. -/
theorem sum_zipIdxFinG {α : Type} (G : α × ℕ → E2) : ∀ (l : List α) (k : ℕ),
    ((l.zipIdx k).map G).sum = ∑ j : Fin l.length, G (l[j], k + j)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdxFinG G l (k + 1)]
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := l.length) fun j ↦ G ((a :: l)[j], k + j)).symm
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, add_zero, Fin.val_succ,
      List.getElem_cons_succ]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Nat.add_assoc, Nat.add_comm 1]

theorem add_eq_iff_char2 (a b c : E2) : a + b = c ↔ b = c + a := by
  constructor
  · rintro rfl; rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rintro rfl; rw [add_comm c a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- The height of table `j` (`0` past the tables). -/
def τof (j : ℕ) : ℕ := (tabs[j]?.map (·.τ)).getD 0

theorem τof_eq (j : Fin tabs.length) : τof tabs j = (tabs.get j).τ := by
  simp [τof]

/-- **Table `j`'s columns' extensions at `ζ.take τ_j`**. -/
noncomputable def colMle (ζ : List E2) (st : Column L.μ) (j c : ℕ) : E2 :=
  ∑ n ∈ range (2 ^ τof tabs j), eqAtF (ζ.take (τof tabs j)) n * cellsAt L tabs hτ st j n c

/-- **A block's leaf extension** is its form at its table's columns' extensions. -/
theorem leafMle_eq (hlin : mbLinB6 tabs = true) (alphas : List E2) (β : E2) (s : ℕ) (ζ : List E2) (st : Column L.μ)
    {b : VBlockG} (hb : b ∈ sideG tabs alphas β s) (hκ : b.κ ≤ ζ.length) :
    ∑ n ∈ range (2 ^ b.κ), eqAtF (ζ.take b.κ) n * leafAt L tabs hτ st b n =
      evalFG b.form (colMle L tabs hτ ζ st b.tab) := by
  obtain ⟨j, hj, hκj, hT⟩ := block_facts hlin (eqKernelF alphas) β s hb
  have hs1 : ∑ n ∈ range (2 ^ b.κ), eqAtF (ζ.take b.κ) n = 1 := by
    have := sum_eqAtF (ζ.take b.κ)
    rwa [List.length_take, min_eq_left hκ] at this
  unfold colMle leafAt
  rw [hj, τof_eq, ← hκj]
  exact (evalFG_affine b.form.terms (fun m hm ↦ by rcases hT m hm with h | ⟨c, -, h⟩ <;> simp [h]) _ _ hs1 _).symm

/-- Side `s`'s weighted blocks. -/
theorem sidesG_getD (alphas β : _) (ζ : List E2) {s : ℕ} (_hs : s < 3) :
    (sidesG tabs alphas β ζ).getD s [] =
      (stackBlocksG (sideG tabs alphas β s)).map fun bo ↦ (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ ζ) := by
  rw [sidesG, sideG]
  rw [show ([] : List (VBlockG × E2)) = (stackBlocksG ([] : List VBlockG)).map
    (fun bo ↦ (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ ζ)) by simp [stackBlocksG], List.getD_map]

theorem formG_busResG (b : LBusG) {j : ℕ} (hj : j < tabs.length) (s : ℕ) :
    formG (busResG tabs b) j s = ⟨bucketG ((sidesG tabs b.alphas b.beta b.point).getD s []) j⟩ := by
  have hr : (busResG tabs b).forms.getD j [] =
      (sidesG tabs b.alphas b.beta b.point).map fun sd ↦ (⟨bucketG sd j⟩ : FormG) := by
    simp only [busResG, busFinalG]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rw [formG, hr, show (default : FormG) = ⟨bucketG [] j⟩ from rfl, List.getD_map]

theorem rec_falseG {tabs : List Tab} (hlin : mbLinB6 tabs = true) {t : Tab} (ht : t ∈ tabs) {c : ℕ} {rec : Bool}
    {off : ℕ} (hcol : t.cols[c]? = some (.com rec off)) : rec = false := by
  have h := List.all_eq_true.mp hlin t ht
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 _ (List.mem_of_getElem? hcol)
  simpa using this

/-- Table `j`'s parts on side `s` (`mbPartsG`'s block of table `j`). -/
def partsG (r : BusResG) (t : Tab) (j s : ℕ) : List (E2 × LeanVM.Protocol.Verifier.Placement × List E2) :=
  (sideColsG t s).filterMap fun c ↦ match t.cols[c]? with
    | some (ColSrc.com _ off) => some (coefG (formG r j s) c, ⟨t.τ, off⟩, r.point.take t.τ)
    | _ => none

/-- The tables are no taller than the leaf stacks. -/
theorem τ_le_μBus (hsc : AllSc tabs) (j : Fin tabs.length) : (tabs.get j).τ ≤ (inst L tabs hτ).μBus :=
  ((inst L tabs hτ).τ_le_τmax ⟨j, sumcheckTable_of L tabs hτ hsc j⟩).trans (condOf L tabs hτ hsc).τmax_le

/-- **The leaves' extensions from the three claims**: on tableless tables, when the three claims of what the bus phase
read hold on `qm`, each side's leaves on `stackOf qm qr` have the extension `values[s]` at the point. -/
theorem mle_of_claims (hsc : AllSc tabs) (hlay : LayOk L tabs) (hlin : mbLinB6 tabs = true) (b : LBusG)
    (hp : b.point.length = (inst L tabs hτ).μBus) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (hcl : ∀ c ∈ mbClaimsG L.nuMain tabs b, ClaimE.Holds L.nuMain c.onStack qm) (s : Fin 3) :
    ∑ w ∈ range (2 ^ b.point.length), eqAtF b.point w * leafG L tabs hτ b.alphas b.beta (stackOf L qm qr) s w =
      b.values.getD s 0 := by
  set ζ := b.point
  set st := stackOf L qm qr
  set r := busResG tabs b
  have hside := sidesG_getD tabs b.alphas b.beta ζ s.isLt
  set side := (sidesG tabs b.alphas b.beta ζ).getD s [] with hsd
  have hfit : tot VBlockG.κ (sideG tabs b.alphas b.beta s) ≤ 2 ^ ζ.length := by
    rw [hp]; exact tot_sideG L tabs hτ hsc b.alphas b.beta s
  rw [mle_leafG L tabs hτ b.alphas b.beta st s ζ hfit]
  -- each block's leaf extension is its form at the columns' extensions
  have hblk : ∀ bo ∈ stackBlocksG (sideG tabs b.alphas b.beta s),
      (∑ n ∈ range (2 ^ bo.1.κ), eqAtF (ζ.take bo.1.κ) n * leafAt L tabs hτ st bo.1 n) =
        evalFG bo.1.form (colMle L tabs hτ ζ st bo.1.tab) := by
    intro bo hbo
    obtain ⟨hm, hf, -⟩ := mem_stackBlocksG hbo
    refine leafMle_eq L tabs hτ hlin _ _ s ζ st hm ?_
    have h1 : 2 ^ bo.1.κ ≤ 2 ^ ζ.length := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  rw [List.map_congr_left fun bo hbo ↦ by rw [hblk bo hbo]]
  -- grouped by table
  have hgroup : ((stackBlocksG (sideG tabs b.alphas b.beta s)).map fun bo ↦
      eqAboveG ⟨bo.1.κ, bo.2⟩ ζ * evalFG bo.1.form (colMle L tabs hτ ζ st bo.1.tab)).sum =
      ∑ j : Fin tabs.length, evalFG ⟨bucketG side j⟩ (colMle L tabs hτ ζ st j) := by
    simp only [evalFG_bucketG]
    rw [hside]
    have hk : ∀ bw ∈ (stackBlocksG (sideG tabs b.alphas b.beta s)).map
        (fun bo ↦ (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ ζ)), bw.1.tab < tabs.length := by
      intro bw hbw
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp hbw
      obtain ⟨j, hj, -⟩ := block_facts hlin _ _ s (mem_stackBlocksG hbo).1
      exact hj ▸ j.isLt
    have e : ∀ j : Fin tabs.length, ((((stackBlocksG (sideG tabs b.alphas b.beta s)).map
        (fun bo ↦ (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ ζ))).filter fun bw ↦ bw.1.tab == j.val).map
          fun bw ↦ bw.2 * evalFG bw.1.form (colMle L tabs hτ ζ st j)).sum =
        ((((stackBlocksG (sideG tabs b.alphas b.beta s)).map
        (fun bo ↦ (bo.1, eqAboveG ⟨bo.1.κ, bo.2⟩ ζ))).filter fun bw ↦ bw.1.tab == j.val).map
          fun bw ↦ bw.2 * evalFG bw.1.form (colMle L tabs hτ ζ st bw.1.tab)).sum := by
      intro j
      refine congrArg List.sum (List.map_congr_left fun bw hbw ↦ ?_)
      rw [beq_iff_eq.mp (List.mem_filter.mp hbw).2]
    rw [Finset.sum_congr rfl fun j _ ↦ e j, sum_group tabs.length (fun bw : VBlockG × E2 ↦ bw.1.tab)
      (fun bw ↦ bw.2 * evalFG bw.1.form (colMle L tabs hτ ζ st bw.1.tab)) _ hk, List.map_map]
    rfl
  -- each table's form splits
  have hsplit : ∀ j : Fin tabs.length, evalFG ⟨bucketG side j⟩ (colMle L tabs hτ ζ st j) =
      constG tabs[j] (formG r j s) (ζ.take tabs[j].τ) +
        ((partsG r tabs[j] j s).map fun p ↦ p.1 * blkValG qm p.2.1 p.2.2).sum := by
    intro j
    rw [partsG, formG_busResG tabs b j.isLt]
    refine evalFG_split tabs[j] _ (namedG tabs[j] s) (sideColsG tabs[j] s) _ (ζ.take tabs[j].τ)
      (r.point.take tabs[j].τ) (blkValG qm) (fun m hm ↦ ?_) (fun c hc hcw ↦ ?_) ((List.nodup_range).filter _)
      (fun c hc ↦ ?_) (fun c f ev hcol ↦ ?_) (fun c rec off hcol ↦ ?_)
    · obtain ⟨bw, hbw, t, ht, rfl⟩ : ∃ bw ∈ (side.filter fun bw ↦ bw.1.tab == j.val).reverse,
          ∃ t ∈ bw.1.form.terms, (t.1, bw.2 * t.2) = m := by
        simpa [bucketG, List.mem_flatMap] using hm
      have hbw' := List.mem_filter.mp (List.mem_reverse.mp hbw)
      rw [hside] at hbw'
      obtain ⟨bo, hbo, rfl⟩ := List.mem_map.mp hbw'.1
      obtain ⟨j', hj', -, hT⟩ := block_facts hlin _ _ s (mem_stackBlocksG hbo).1
      have : j' = j := Fin.ext (hj' ▸ beq_iff_eq.mp hbw'.2)
      subst this
      exact hT t ht
    · rw [sideColsG_eq, List.mem_filter, List.mem_range]
      exact ⟨hcw, List.elem_iff.mpr hc⟩
    · refine Finset.sum_eq_zero fun n _ ↦ ?_
      rw [cellsAt_none L tabs hτ st j n (fun h ↦ hc), mul_zero]
    · unfold colMle
      rw [τof_eq]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [cellsAt_fix L tabs hτ st j hcol (Finset.mem_range.mp hn)]
      rfl
    · obtain rfl := rec_falseG hlin (List.getElem_mem j.isLt) hcol
      unfold colMle blkValG
      rw [τof_eq]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [cellsAt_com L tabs hτ hlay qm qr j hcol (Finset.mem_range.mp hn)]
      rfl
  -- the claim of side `s`
  have hclaim := hcl _ (List.mem_map.mpr ⟨s.val, List.mem_range.mpr s.isLt, rfl⟩)
  have hP : ∀ p ∈ mbPartsG tabs r s, p.2.2.length = p.2.1.variableCount ∧
      2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ L.nuMain := by
    intro p hpm
    obtain ⟨⟨t, j'⟩, hz, hpt⟩ := List.mem_flatMap.mp hpm
    obtain ⟨hj', ht⟩ := List.mem_zipIdx' hz
    have ht2 : t = tabs[j']'hj' := ht
    subst ht2
    obtain ⟨c, -, hsome⟩ := List.mem_filterMap.mp hpt
    rcases hcol : tabs[j'].cols[c]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩) <;> simp only [hcol] at hsome
    · cases hsome
    · cases hsome
      obtain rfl := rec_falseG hlin (List.getElem_mem hj') hcol
      have hτj : tabs[j'].τ ≤ ζ.length := by rw [hp]; exact τ_le_μBus L tabs hτ hsc ⟨j', hj'⟩
      have hcw : c < tabs[j'].w := (List.getElem?_eq_some_iff.mp hcol).1
      have hal := hlay _ (List.getElem_mem hj') c hcw
      unfold Aligned at hal
      rw [hcol] at hal
      obtain ⟨hd, hf, -⟩ := hal
      refine ⟨?_, hd, by simpa using hf⟩
      show (List.take tabs[j'].τ ζ).length = tabs[j'].τ
      simp [hτj]
    · cases hsome
  have hPeq : mbPartsG tabs r s = tabs.zipIdx.flatMap fun tj ↦ partsG r tj.1 tj.2 s := rfl
  rw [holds_sumClaimG_iff _ _ _ _ hP, hPeq, sum_map_flatMapG, sum_zipIdxFinG, mbValueG, sumF_eq_sum,
    sum_zipIdxFinG] at hclaim
  simp only [Nat.zero_add] at hclaim
  have hsum : ∑ j : Fin tabs.length, evalFG ⟨bucketG side j⟩ (colMle L tabs hτ ζ st j) = r.totals.getD s 0 := by
    rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_add_distrib]
    exact (add_eq_iff_char2 _ _ _).mpr hclaim
  have htot : r.totals.getD s 0 = b.values.getD s 0 + 1 + (side.map (·.2)).sum := by
    simp only [r, busResG, busFinalG, side]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, sumF_eq_sum]
  -- assemble
  have hw : ((stackBlocksG (sideG tabs b.alphas b.beta s)).map fun bo ↦
      eqAboveG ⟨bo.1.κ, bo.2⟩ ζ * (evalFG bo.1.form (colMle L tabs hτ ζ st bo.1.tab) + 1)).sum =
      r.totals.getD s 0 + (side.map (·.2)).sum := by
    rw [← hsum, ← hgroup, hside, List.map_map]
    simp only [mul_add, mul_one, List.sum_map_add]
    rfl
  rw [hw, htot]
  have h2 : ∀ a : E2, a + a = 0 := fun a ↦ CharTwo.add_self_eq_zero a
  calc 1 + (b.values.getD s 0 + 1 + (side.map (·.2)).sum + (side.map (·.2)).sum)
      = b.values.getD s 0 + (1 + 1) + ((side.map (·.2)).sum + (side.map (·.2)).sum) := by ring
    _ = b.values.getD s 0 := by rw [h2, h2, add_zero, add_zero]

end Main

end Lvm6.Mb
end -- part Lvm6MbLin

/-! ### Part `Lvm6MbMid` (was its own module) -/
section

/-!
# The mini-bus at `E2`: `miniSpecL6`

The candidates are the stacks `stackOf qm qr` of the pairs of `S` meeting `aRm` (`Lvm.M3.candSet`, season 1's
`miniSpecL`), the one oracle of the lvm instance. Doom is carried on relations over that oracle (`HDoom`):

* **`Seam.commit`** (`M3Holds`) → **`afterAB`** at the drawn `(α, β)`: the push and pull leaf products agree and the
  count product is nonzero. On tableless tables `M3Holds` is `Balanced ∧ CountsNonzero`; a stack breaking
  `CountsNonzero` has a zero count product, one breaking `Balanced` has push and pull tuple multisets that differ, so
  their grand product polynomials differ (`grandProduct_difference_ne_zero`), of total degree `≤ 4·2^12` in the five
  draws: `szN_escape_grind` prices the group at `errG gAB (4·2^12)` (**`ab_escape`**).
* `afterAB` → `Gkr.relIn` at the roots (a nonzero count root), the walk (`gkrSpecG`), the count root checked nonzero:
  doom on `Gkr.relOut` at the point and the three values (**`lvmBusSpecG`**).
* `Gkr.relOut` → the three claims: claims that hold make the leaves' extensions the values (`mle_of_claims`).
-/

set_option autoImplicit false

namespace Lvm6.Mb

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm.M3 CompPoly CMlPolynomialEval
open Finset
open scoped ENNReal

/-! ## Multilinear extensions as equality-weighted sums -/

theorem evalMle_eq_eqAtF {n : ℕ} (t : CMlPolynomialEval E2 n) (x : Vector E2 n) :
    evalMle t x = ∑ w ∈ range (2 ^ n), eqAtF x.toList w * (if h : w < 2 ^ n then t[w] else 0) := by
  rw [evalMle_eq_sum, ← Fin.sum_univ_eq_sum_range (fun w ↦ eqAtF x.toList w * (if h : w < 2 ^ n then t[w] else 0))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dif_pos i.isLt, mul_comm, eqAtF_prod, Vector.length_toList, Fin.getElem_fin, lagrangeBasis_getElem_nat _ i.isLt,
    ← Fin.prod_univ_eq_prod_range (fun b ↦ if i.val.testBit b then x.toList.getD b 0 else 1 - x.toList.getD b 0) n]
  congr 1
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  simp

/-! ## The relations -/

section Rel

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **After the fingerprint group**: the push and pull leaf products agree, the count product is nonzero. -/
def AfterAB (x : List E2 × E2) (st : Column L.μ) : Prop :=
  (∏ w ∈ range (2 ^ miniDepth), leafG L tabs hτ x.1 x.2 st 0 w) =
      ∏ w ∈ range (2 ^ miniDepth), leafG L tabs hτ x.1 x.2 st 1 w ∧
    ∏ w ∈ range (2 ^ miniDepth), leafG L tabs hτ x.1 x.2 st 2 w ≠ 0

/-- `AfterAB` as a relation over the instance's one oracle. -/
def relAB : Set (((List E2 × E2) × ∀ i, TheOracle (inst L tabs hτ) i) × Unit) :=
  {p | AfterAB L tabs hτ p.1.1 (p.1.2 0)}

/-- **The leaves of the GKR walk at `E2`**: side `k`'s leaf stack at `(α, β)` on the oracle's stack. -/
noncomputable def leavesG (x : List E2 × E2) (o : ∀ i, TheOracle (inst L tabs hτ) i) (k : Fin 3) :
    CMlPolynomialEval E2 miniDepth :=
  Vector.ofFn fun w : Fin (2 ^ miniDepth) ↦ leafG L tabs hτ x.1 x.2 (o 0) k w

/-- No rider: the tables have no constraint. -/
def ridersG (_x : List E2 × E2) (_o : ∀ i, TheOracle (inst L tabs hτ) i) :
    List (Σ τ : Fin (miniDepth + 1), CMlPolynomialEval E2 τ) := []

/-- The draws of the fingerprint group as `(α, β)`. -/
def abOf (ys : List E2) : List E2 × E2 := (ys.take 4, ys.getD 4 0)

theorem prod_leavesG (x : List E2 × E2) (o : ∀ i, TheOracle (inst L tabs hτ) i) (k : Fin 3) :
    ∏ i : Fin (2 ^ miniDepth), (leavesG L tabs hτ x o k)[i] =
      ∏ w ∈ range (2 ^ miniDepth), leafG L tabs hτ x.1 x.2 (o 0) k w := by
  rw [← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ ↦ by simp [leavesG]

/-- **A nonzero count root in the grand product's input relation reflects into `AfterAB`.** -/
theorem roots_reflectG (x : List E2 × E2) (o : ∀ i, TheOracle (inst L tabs hτ) i) (shared count : E2)
    (hc : count ≠ 0)
    (hin : (((x, ![shared, shared, count]), o), ()) ∈ Gkr.relIn 3 miniDepth (leavesG L tabs hτ) (ridersG L tabs hτ)) :
    (((x, o), ()) : ((List E2 × E2) × ∀ i, TheOracle (inst L tabs hτ) i) × Unit) ∈ relAB L tabs hτ := by
  obtain ⟨-, hr⟩ := hin
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, prod_leavesG] at h0 h1 h2
  exact ⟨h0.symm.trans h1, h2 ▸ hc⟩

end Rel

/-! ## The fingerprint group's escape (Theorem 5.1 at `E2`, with grinding) -/

section Escape

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- The five draws' variables: `β` is the fifth. -/
def eAB : Option (Fin 4) → Fin 5 := fun i ↦ i.elim 4 Fin.castSucc

theorem eAB_injective : Function.Injective eAB := by
  intro a b h
  cases a <;> cases b <;> simp [eAB, Fin.ext_iff] at h ⊢ <;> omega

/-- On tableless tables `M3Holds` is `Balanced ∧ CountsNonzero`. -/
theorem m3Holds_of (hlin : mbLinB6 tabs = true) (st : Column L.μ) (hb : (inst L tabs hτ).Balanced st)
    (hc : (inst L tabs hτ).CountsNonzero st) : M3Holds (inst L tabs hτ) () st := by
  refine ⟨fun j C hC ↦ ?_, hb, hc, publicLines_lvm L tabs hτ st, fun r hr ↦ by simp [inst] at hr⟩
  have h := List.all_eq_true.mp hlin _ (List.get_mem tabs j)
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  have hC' : C ∈ (tabs.get j).cons.map (CPoly.toMv _) := hC
  rw [h.1.1] at hC'
  exact absurd hC' List.not_mem_nil

/-- A side's tuples are at most the leaf stacks' size. -/
theorem card_tuples_le (hsc : AllSc tabs) (hμ : (inst L tabs hτ).μBus = miniDepth) (st : Column L.μ) (k : Fin 3)
    (s : Side) (hk : Bus.sources (inst L tabs hτ) k = Bus.sideSources _ s) :
    ((inst L tabs hτ).tuples st s).length ≤ 2 ^ miniDepth := by
  have h1 := Bus.length_side hk st
  have h2 := (condOf L tabs hτ hsc).fits k
  rw [Bus.blocks_total, hμ] at h2
  omega

/-- **The fingerprint group's escape**: a stack outside `M3Holds` meets `AfterAB` at an accepted tuple of the five
draws with probability `≤ errG gAB (4·2^12)`. -/
theorem ab_escape (hsc : AllSc tabs) (hkey : KeysOk tabs) (hlin : mbLinB6 tabs = true)
    (hμ : (inst L tabs hτ).μBus = miniDepth) (st : Column L.μ) (hno : ¬ M3Holds (inst L tabs hτ) () st) :
    avgEN 5 (fun c ↦ indE (powOK gAB (c 0) ∧ AfterAB L tabs hτ (abOf ((List.ofFn c).map e2OfE)) st)) ≤
      errG gAB (4 * 2 ^ miniDepth) := by
  classical
  by_cases hcnt : (inst L tabs hτ).CountsNonzero st
  swap
  · refine le_of_eq_of_le ?_ zero_le
    have : ∀ c : Fin 5 → E, ¬ (powOK gAB (c 0) ∧ AfterAB L tabs hτ (abOf ((List.ofFn c).map e2OfE)) st) := by
      rintro c ⟨-, -, hnz⟩
      refine hcnt (countsNonzero_of_leafG L tabs hτ hsc (abOf ((List.ofFn c).map e2OfE)).1
        (abOf ((List.ofFn c).map e2OfE)).2 st ?_)
      rwa [hμ]
    rw [show (fun c ↦ indE (powOK gAB (c 0) ∧ AfterAB L tabs hτ (abOf ((List.ofFn c).map e2OfE)) st)) =
      fun _ ↦ 0 from funext fun c ↦ indE_of_not (this c)]
    simp [avgEN]
  have hbal : ¬ (inst L tabs hτ).Balanced st := fun hb ↦ hno (m3Holds_of L tabs hτ hlin st hb hcnt)
  set φ := algebraMap K E2
  set M : Multiset (CMlPolynomialEval E2 4) :=
    ((((inst L tabs hτ).tuples st .push : List (Vector K 16)) : Multiset _).map (CMlPolynomialEval.map (n := 4) φ))
  set N : Multiset (CMlPolynomialEval E2 4) :=
    ((((inst L tabs hτ).tuples st .pull : List (Vector K 16)) : Multiset _).map (CMlPolynomialEval.map (n := 4) φ))
  have hne : M ≠ N := fun h ↦ hbal (Multiset.coe_eq_coe.mp (map_tupleMultiset_injective φ φ.injective h))
  have hM : M.card ≤ 2 ^ miniDepth := by
    simp only [M, Multiset.card_map, Multiset.coe_card]; exact card_tuples_le L tabs hτ hsc hμ st 0 .push rfl
  have hN : N.card ≤ 2 ^ miniDepth := by
    simp only [N, Multiset.card_map, Multiset.coe_card]; exact card_tuples_le L tabs hτ hsc hμ st 1 .pull rfl
  set P := MvPolynomial.rename eAB (grandProductPoly M - grandProductPoly N)
  have hP : P ≠ 0 := fun h ↦ grandProduct_difference_ne_zero hne
    (MvPolynomial.rename_injective _ eAB_injective (h.trans (map_zero _).symm))
  have hd : P.totalDegree ≤ 4 * 2 ^ miniDepth :=
    (MvPolynomial.totalDegree_rename_le _ _).trans (totalDegree_grandProduct_difference_le M N hM hN)
  refine (avgEN_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans (szN_escape_grind (by norm_num) hP hd)
  obtain ⟨-, hprod, -⟩ := hc
  have hlen : (abOf ((List.ofFn c).map e2OfE)).1.length = 4 := by simp [abOf]
  set x := abOf ((List.ofFn c).map e2OfE) with hx
  have e0 : (∏ w ∈ range (2 ^ miniDepth), leafG L tabs hτ x.1 x.2 st 0 w) =
      ((((inst L tabs hτ).tuples st .push : List (Vector K 16)) : Multiset (Vector K 16)).map fun t ↦
        x.2 - eval₂Mle (n := 4) t (algebraMap K E2) (a4 x.1)).prod := by
    rw [← hμ]; exact prod_leafG_side L tabs hτ hsc hkey hlen x.2 st 0 .push rfl
  have e1 : (∏ w ∈ range (2 ^ miniDepth), leafG L tabs hτ x.1 x.2 st 1 w) =
      ((((inst L tabs hτ).tuples st .pull : List (Vector K 16)) : Multiset (Vector K 16)).map fun t ↦
        x.2 - eval₂Mle (n := 4) t (algebraMap K E2) (a4 x.1)).prod := by
    rw [← hμ]; exact prod_leafG_side L tabs hτ hsc hkey hlen x.2 st 1 .pull rfl
  rw [e0, e1, prod_tuples_eq_eval₂, prod_tuples_eq_eval₂,
    ← MvPolynomial.eval_map, ← MvPolynomial.eval_map, map_grandProductPoly, map_grandProductPoly] at hprod
  have hpt : (fun i ↦ e2OfE (c i)) ∘ eAB = fun i ↦ i.elim x.2 fun j ↦ (a4 x.1)[j] := by
    funext i
    cases i with
    | none => simp [x, eAB, abOf]
    | some j => fin_cases j <;> rfl
  rw [MvPolynomial.eval_rename, map_sub, sub_eq_zero, hpt]
  exact hprod

end Escape

/-! ## The bus phase -/

section Bus

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)
  (cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i)) {εmax T : ℝ≥0∞}

/-- The bus phase's output relation: the point and values have their lengths, and doom on the GKR's output relation. -/
def BusPostG (b : LBusG) (h : List Ev) : Prop :=
  b.point.length = miniDepth ∧ b.values.length = 3 ∧
    HDoom cands (Gkr.relOut 3 miniDepth (leavesG L tabs hτ) (ridersG L tabs hτ))
      (layerStmtOfG (b.alphas, b.beta) miniDepth ⟨b.values, b.point⟩) h

/-- **The bus phase at `E2`** (`lvmBusSpec4`'s twin): from doom on `M3Holds` to doom on the GKR's output relation at
what was read. Lead `0`; every group's error plus the follower's lead `T` within `εmax < 1`. -/
noncomputable def lvmBusSpecG (hsc : AllSc tabs) (hkey : KeysOk tabs) (hlin : mbLinB6 tabs = true)
    (hμ : (inst L tabs hτ).μBus = miniDepth) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hε : εmax < 1)
    (hab : (L₀ : ℝ≥0∞) * errG gAB (4 * 2 ^ miniDepth) + T ≤ εmax) (hlam : (L₀ : ℝ≥0∞) * errG gLam 2 + T ≤ εmax)
    (hrd : (L₀ : ℝ≥0∞) * errG gRd 5 + T ≤ εmax) (hY : (L₀ : ℝ≥0∞) * errG gY 2 + T ≤ εmax)
    (hYl : (L₀ : ℝ≥0∞) * errG gYl 4 + T ≤ εmax) :
    Spec (lvmBusProgG miniDepth) (HDoom cands (Seam.commit (inst L tabs hτ)) ())
      (BusPostG L tabs hτ cands) εmax 0 T :=
  (e2SampleNSpecH hfin hcard (Seam.commit (inst L tabs hτ)) () (relAB L tabs hτ) abOf (n := 4) (g := gAB)
    (errG gAB (4 * 2 ^ miniDepth))
    (fun o ho ↦ ab_escape L tabs hτ hsc hkey hlin hμ (o 0) ho)
    (le_trans (add_le_add le_rfl zero_le) hab) hε).bind' fun ab ↦
  ((gkrSpecG (leavesG L tabs hτ) (ridersG L tabs hτ) cands (abOf ab) (relAB L tabs hτ) (abOf ab)
      (fun o shared count hc hin ↦ roots_reflectG L tabs hτ _ o shared count hc hin) hfin hcard (by decide)
      hlam hrd hY hYl hε).mono (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
  (Spec.require (Post := fun _ h ↦ r.2.1.length = miniDepth ∧ r.2.2.length = 3 ∧
      HDoom cands (Gkr.relOut 3 miniDepth (leavesG L tabs hτ) (ridersG L tabs hτ))
        (layerStmtOfG (abOf ab) miniDepth ⟨r.2.2, r.2.1⟩) h)
    fun _ hp hc ↦ hp.resolve_left hc).bind' fun _ ↦
  Spec.ret (Post := BusPostG L tabs hτ cands) _

end Bus

/-! ## `miniSpecL6` -/

section Mid

/-- **`miniSpecL6`** (the frozen `MiniSpecL6Stmt`): the mini-bus at `E2`, from doom of the mini-bus relation to doom
of the three claims on `C_main`, on a fixed candidate set, every group's error as the hypotheses state. -/
theorem miniSpecL6 : MiniSpecL6Stmt := by
  intro L tabs hτ S aRm L₀ εmax T hfin hS hsc hlay hkey _hfix hlin hμ hε hab hlam hrd hY hYl
  let cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i) := fun _ ↦
    candSet L tabs hτ (fun _ ↦ S) (fun p ↦ stackOf L p.1 p.2) aRm []
  have hcf : ∀ W, (cands W).Finite := fun _ ↦ candSet_finite L tabs hτ _ _ _ hfin
  have hcc : ∀ W, (cands W).ncard ≤ L₀ := fun _ ↦ (candSet_ncard L tabs hτ _ _ _ hfin).trans hS
  refine ⟨Spec.congr (p := lvmBusProgG miniDepth >>= fun b ↦ pure ((mbClaimsG L.nuMain tabs b).map (·.onStack)))
    rfl ?_⟩
  refine ((lvmBusSpecG L tabs hτ cands hsc hkey hlin hμ hcf hcc hε hab hlam hrd hY hYl).bind' fun b ↦
    (Spec.ret (Post := fun cl h ↦ cl.length = 3 ∧ Doomed (fun _ ↦ S) (fun q ↦
      (∀ c ∈ cl, ClaimE.Holds L.nuMain c q.1) ∧ aRm q) h) _).mono ?_ (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    ?_ (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  · intro h hp
    obtain ⟨hpl, hvl, W, hW, hR⟩ := hp
    refine ⟨by simp [mbClaimsG], fun q hqS ⟨hcl, hq⟩ ↦ hR _ ⟨q, ⟨hqS, hq⟩, rfl⟩ ⟨fun s ↦ ?_, fun r hr ↦ by
      simp [ridersG] at hr⟩⟩
    have hp' : b.point.length = (inst L tabs hτ).μBus := hpl.trans hμ.symm
    have hm := mle_of_claims L tabs hτ hsc hlay hlin b hp' q.1 q.2
      (fun c hc ↦ hcl _ (List.mem_map_of_mem hc)) s
    rw [hpl] at hm
    simp only [layerStmtOfG, leavesG, evalMle_eq_eqAtF, toList_vecOfG _ hpl, valuesFnG]
    rw [← hm]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [dif_pos (Finset.mem_range.mp hw)]
    simp [oraOf]
  · intro h hp
    obtain ⟨⟨W, hW⟩, hD⟩ := hp
    exact ⟨W, hW, fun o ho hR ↦ by
      obtain ⟨p, ⟨hpS, hpR⟩, rfl⟩ := ho
      exact hD p hpS ⟨hR, hpR⟩⟩

end Mid

end Lvm6.Mb
end -- part Lvm6MbMid
