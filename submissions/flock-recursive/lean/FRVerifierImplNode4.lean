-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8/A.9 on a node; stage S-CN4). 3.x templates:
-- `FRVerifierImplNode` (`shiftMaskI`, `linkWOne`/`linkWAllI`).
import FRNodeTarget4
import FRVerifierImplNode
import FRVerifierImplOps4

/-!
# The node's verifier ops at the revision 4.1 layout: computed forms

* **`shiftMask4I`**: the chain mask is the prefix `[0, chLen₀ + chLen₁ − 1)` less chain 0's last
  block (`chainLk4_iff`), so each weight is one dyadic prefix sum less one term: `prefixP` for
  `Σ eq(τ,y) eq(r,y)` and **`shP`** (new: the successor's prefix sum by the low bit, `shP_eq`) for
  `Σ eq(τ,y) eq(r,y+1)`. **`shiftMask4_meets`**.
* **`linkWAll4I`**: 3.x's `linkWOne` over two-level `eq` tables of the `nb`-coordinate block points
  (**`bt`**: the low 9 coordinates, the high `nb − 9`; `bt_eq`), the eight families sharing the
  tables. **`linkWAll4_meets`**.
-/

namespace FR
namespace NI4
open Finset RecursionFast Rev4 Impl NT4

/-! ## The successor's prefix sum -/

/-- **`Σ_{x < c, x + 1 < 2^n} Π_l m_l(x_l, (x + 1)_l)`** by the low bit: `x = 2u` steps to `2u + 1`
(bit 0: `0 → 1`), `x = 2u + 1` to `2(u + 1)` (bit 0: `1 → 0`, the carry into `u`). -/
def shP : (n : ℕ) → (Fin n → Bool → Bool → F) → ℕ → F
  | 0, _, _ => 0
  | n + 1, m, c => m 0 false true * prefixP n (fun l b => m l.succ b b) ((c + 1) / 2) +
      m 0 true false * shP n (fun l => m l.succ) (c / 2)

theorem tb_two_succ (u : ℕ) (b : Bool) (l : ℕ) : (2 * u + b.toNat).testBit (l + 1) = u.testBit l := by
  rw [Nat.testBit_succ]; congr 1; cases b <;> simp <;> omega

theorem tb_two_zero (u : ℕ) (b : Bool) : (2 * u + b.toNat).testBit 0 = b := by
  cases b <;> simp [Nat.testBit_zero]

theorem shP_eq (n : ℕ) (m : Fin n → Bool → Bool → F) (c : ℕ) :
    shP n m c = ∑ x : Fin (2 ^ n), if x.val < c ∧ x.val + 1 < 2 ^ n then
      ∏ l : Fin n, m l (x.val.testBit l) ((x.val + 1).testBit l) else 0 := by
  induction n generalizing c with
  | zero =>
    rw [sum_cube_zero]
    simp [shP]
  | succ n ih =>
    rw [shP, ih, prefixP_eq, sum_cube_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have e0 : (dbl u false).val = 2 * u.val + (false).toNat := by simp [dbl]
    have e1 : (dbl u true).val = 2 * u.val + (true).toNat := by simp [dbl]
    have e2 : 2 * u.val + (true).toNat + 1 = 2 * (u.val + 1) + (false).toNat := by simp; ring
    have e3 : 2 * u.val + (false).toNat + 1 = 2 * u.val + (true).toNat := by simp
    have k : ∀ (v w : ℕ) (b b' : Bool), ∏ l : Fin (n + 1), m l ((2 * v + b.toNat).testBit l)
        ((2 * w + b'.toNat).testBit l) =
        m 0 b b' * ∏ l : Fin n, m l.succ (v.testBit l) (w.testBit l) := fun v w b b' => by
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, tb_two_succ, tb_two_zero]
    rw [e0, e1, e2, e3, k, k]
    have hu := u.isLt
    rw [pow_succ]
    simp only [Bool.toNat_false, Bool.toNat_true]
    split_ifs <;> first | ring1 | (exfalso; omega)

/-! ## The prefix sums on index-shifted factors (the computed forms) -/

/-- `Π_{l<n} g l` as a loop. -/
def prodTo (n : ℕ) (g : ℕ → F) : F := Nat.fold n (fun i _ acc => acc * g i) 1

theorem prodTo_eq (n : ℕ) (g : ℕ → F) : prodTo n g = ∏ i ∈ range n, g i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prodTo, Nat.fold_succ, ← prodTo, ih, Finset.prod_range_succ]

/-- `prodAt` on the coordinates `s, s + 1, …` of `e` (a loop, no `Fin` enumeration). -/
def prodQ (e : ℕ → Bool → F) (n s d : ℕ) : F :=
  if d < 2 ^ n then prodTo n fun l => e (s + l) (d.testBit l) else 0

/-- `prefixP` on the coordinates `s, s + 1, …` of `e`. -/
def prefixQ (e : ℕ → Bool → F) : ℕ → ℕ → ℕ → F
  | 0, _, c => if 0 < c then 1 else 0
  | n + 1, s, c => (e s false + e s true) * prefixQ e n (s + 1) (c / 2) +
      if c % 2 = 1 then e s false * prodQ e n (s + 1) (c / 2) else 0

/-- `shP` on the coordinates `s, s + 1, …` of `m`. -/
def shQ (m : ℕ → Bool → Bool → F) : ℕ → ℕ → ℕ → F
  | 0, _, _ => 0
  | n + 1, s, c => m s false true * prefixQ (fun l b => m l b b) n (s + 1) ((c + 1) / 2) +
      m s true false * shQ m n (s + 1) (c / 2)

theorem prodQ_eq (e : ℕ → Bool → F) (n s d : ℕ) :
    prodQ e n s d = prodAt (fun (l : Fin n) b => e (s + l.val) b) d := by
  unfold prodQ prodAt
  split_ifs
  · rw [prodTo_eq, ← Fin.prod_univ_eq_prod_range (fun l => e (s + l) (d.testBit l))]
  · rfl

theorem prefixQ_eq (e : ℕ → Bool → F) (n s c : ℕ) :
    prefixQ e n s c = prefixP n (fun (l : Fin n) b => e (s + l.val) b) c := by
  induction n generalizing s c with
  | zero => rfl
  | succ n ih =>
    have hf : (fun (l : Fin n) b => e (s + (Fin.succ l).val) b) = fun (l : Fin n) b => e (s + 1 + l.val) b :=
      funext fun l => funext fun b => by rw [Fin.val_succ, show s + (l.val + 1) = s + 1 + l.val by omega]
    rw [prefixQ, prefixP, ih, prodQ_eq, hf]
    simp only [Fin.val_zero, add_zero]

theorem shQ_eq (m : ℕ → Bool → Bool → F) (n s c : ℕ) :
    shQ m n s c = shP n (fun (l : Fin n) b b' => m (s + l.val) b b') c := by
  induction n generalizing s c with
  | zero => rfl
  | succ n ih =>
    have hf : (fun (l : Fin n) b b' => m (s + (Fin.succ l).val) b b') =
        fun (l : Fin n) b b' => m (s + 1 + l.val) b b' :=
      funext fun l => funext fun b => funext fun b' => by
        rw [Fin.val_succ, show s + (l.val + 1) = s + 1 + l.val by omega]
    have hd : (fun (l : Fin n) b => m (s + (Fin.succ l).val) b b) =
        fun (l : Fin n) b => m (s + 1 + l.val) b b :=
      funext fun l => funext fun b => by rw [Fin.val_succ, show s + (l.val + 1) = s + 1 + l.val by omega]
    rw [shQ, shP, ih, prefixQ_eq, hf, hd]
    simp only [Fin.val_zero, add_zero]

/-! ## `shiftMask` -/

section Mask
variable (ν : NodeKind)

/-- The per-coordinate factors `m_l(b, b′) = eq(τ_l, b) eq(r_l, b′)`. -/
def mF {n : ℕ} (τ r : Fin n → F) (l : Fin n) (b b' : Bool) : F :=
  (if b then τ l else 1 - τ l) * (if b' then r l else 1 - r l)

/-- The four factors `m_l(b, b′)` of every coordinate, computed once. -/
def mArr {n : ℕ} (τ r : Fin n → F) : Array (F × F × F × F) :=
  Array.ofFn fun l => (mF τ r l false false, mF τ r l false true, mF τ r l true false, mF τ r l true true)

/-- `m_l(b, b′)` read from `mArr`. -/
def mQ (M : Array (F × F × F × F)) (l : ℕ) (b b' : Bool) : F :=
  let q := M.getD l (0, 0, 0, 0)
  if b then (if b' then q.2.2.2 else q.2.2.1) else (if b' then q.2.1 else q.1)

theorem mQ_eq {n : ℕ} (τ r : Fin n → F) (l : Fin n) (b b' : Bool) :
    mQ (mArr τ r) l.val b b' = mF τ r l b b' := by
  unfold mQ mArr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos l.isLt, Option.getD_some]
  cases b <;> cases b' <;> rfl

/-- **`shiftMask`, computed** (`c = chLen₀ + chLen₁ − 1`, `a = chLen₀ − 1`): the prefix sums
`Σ_{y<c}` less chain 0's last block `a`, and the starts' two `eq`s; the factors read from
`mArr` (`prefixQ`, `shQ`: index-shifted, loops). -/
def shiftMask4I (τ r : Array F) : F × F × F :=
  let n := nbN ν
  let τ' := ptA n τ; let r' := ptA n r
  let M := mArr τ' r'
  let L0 := N4c.chLen ν 0
  let c := L0 + N4c.chLen ν 1 - 1
  let ea := eqAtR τ' (L0 - 1)
  (prefixQ (fun l b => mQ M l b b) n 0 c - ea * eqAtR r' (L0 - 1),
   shQ (mQ M) n 0 c - ea * eqAtR r' L0,
   eqAtR r' 0 + eqAtR r' L0)

theorem prod_mF {n : ℕ} (τ r : Fin n → F) (x y : ℕ) :
    ∏ l : Fin n, mF τ r l (x.testBit l) (y.testBit l) = eqAtR τ x * eqAtR r y := by
  unfold eqAtR mF; rw [← Finset.prod_mul_distrib]

/-- A sum over the masked blocks is the prefix sum less chain 0's last block. -/
theorem sum_lk (g : ℕ → F) :
    ∑ y ∈ range (2 ^ nbN ν), (if N4c.chainLk4 ν y then g y else 0) =
      ∑ x : Fin (2 ^ nbN ν), (if x.val < N4c.chLen ν 0 + N4c.chLen ν 1 - 1 then g x else 0) -
        g (N4c.chLen ν 0 - 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := chLen_facts ν
  have hw := wotsB_hUsed ν (σ := 0) (by norm_num)
  have key : ∀ y, (if y < N4c.chLen ν 0 + N4c.chLen ν 1 - 1 then g y else 0) =
      (if N4c.chainLk4 ν y then g y else 0) + (if y = N4c.chLen ν 0 - 1 then g y else 0) := by
    intro y
    by_cases ha : y = N4c.chLen ν 0 - 1
    · rw [if_pos (by omega), if_pos ha, if_neg (fun e => ((chainLk4_iff ν y).1 e).2 ha), zero_add]
    · rw [if_neg ha, add_zero]
      by_cases hc : y < N4c.chLen ν 0 + N4c.chLen ν 1 - 1
      · rw [if_pos hc, if_pos ((chainLk4_iff ν y).2 ⟨hc, ha⟩)]
      · rw [if_neg hc, if_neg (fun e => hc ((chainLk4_iff ν y).1 e).1)]
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < N4c.chLen ν 0 + N4c.chLen ν 1 - 1 then g x else 0),
    eq_sub_iff_add_eq, Finset.sum_congr rfl fun y _ => key y, Finset.sum_add_distrib,
    Finset.sum_ite_eq', if_pos (mem_range.2 (by omega))]

/-- **`shiftMask4I` meets `shiftMask4S`** (every operand). -/
theorem shiftMask4_meets (τ r : Array F) : shiftMask4I ν τ r = shiftMask4S ν τ r := by
  obtain ⟨h1, h2, h3, h4⟩ := chLen_facts ν
  have hw : N4c.wotsB ν 0 < N4c.hUsedN ν := by
    have := wotsB_hUsed ν (σ := 0) (by norm_num); omega
  have hM : ∀ {n : ℕ} (τ' r' : Fin n → F), (fun (l : Fin n) b b' => mQ (mArr τ' r') (0 + l.val) b b') =
      mF τ' r' := fun τ' r' => funext fun l => funext fun b => funext fun b' => by
    rw [zero_add, mQ_eq]
  have hD : ∀ {n : ℕ} (τ' r' : Fin n → F), (fun (l : Fin n) b => mQ (mArr τ' r') (0 + l.val) b b) =
      fun l b => mF τ' r' l b b := fun τ' r' => funext fun l => funext fun b => by
    rw [zero_add, mQ_eq]
  simp only [shiftMask4I, shiftMask4S, lkE, lkSh, lkE0, prefixQ_eq, shQ_eq, hM, hD]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only
  · rw [sum_lk, prefixP_eq]
    simp only [prod_mF]
  · rw [sum_lk, shP_eq, show N4c.chLen ν 0 - 1 + 1 = N4c.chLen ν 0 by omega]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prod_mF]
    by_cases hx : x.val < N4c.chLen ν 0 + N4c.chLen ν 1 - 1
    · rw [if_pos ⟨hx, by omega⟩, if_pos hx]
    · rw [if_neg (fun h => hx h.1), if_neg hx]

end Mask

/-! ## Two-level tables of a block point -/

/-- The low 9 and the high `n − 9` coordinates of an array point. -/
def lo9 (a : Array F) : Fin 9 → F := fun l => a.getD l 0
def hiN (n : ℕ) (a : Array F) : Fin (n - 9) → F := fun l => a.getD (9 + l) 0

/-- `eq` tables of the low and the high coordinates. -/
structure BT where
  A : Array F
  B : Array F

/-- The tables of an `n`-coordinate block point (`2^9 + 2^(n−9)` entries). -/
def bt (n : ℕ) (a : Array F) : BT := ⟨eqTable (List.ofFn (lo9 a)), eqTable (List.ofFn (hiN n a))⟩

/-- `eq(point, x)` from the tables (one product). -/
def BT.eq (T : BT) (x : ℕ) : F := T.A.getD (x % 512) 0 * T.B.getD (x / 512) 0

theorem eqAtR_split9 {n : ℕ} (hn : 9 ≤ n) (a : Array F) (x : ℕ) :
    eqAtR (ptA n a) x = eqAtR (lo9 a) (x % 512) * eqAtR (hiN n a) (x / 512) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 9 + k := ⟨n - 9, by omega⟩
  unfold eqAtR ptA lo9 hiN
  rw [Fin.prod_univ_eq_prod_range (fun l => if x.testBit l then a.getD l 0 else 1 - a.getD l 0),
    Fin.prod_univ_eq_prod_range (fun l => if (x % 512).testBit l then a.getD l 0 else 1 - a.getD l 0),
    Fin.prod_univ_eq_prod_range
      (fun l => if (x / 512).testBit l then a.getD (9 + l) 0 else 1 - a.getD (9 + l) 0),
    Finset.prod_range_add, Nat.add_sub_cancel_left]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow]
    simp [mem_range.1 hl]
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_div_two_pow, add_comm l 9]

theorem bt_eq {n : ℕ} (hn : 9 ≤ n) (a : Array F) {x : ℕ} (hx : x < 2 ^ n) :
    (bt n a).eq x = eqAtR (ptA n a) x := by
  have h2 : x / 512 < 2 ^ (n - 9) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), show (512 : ℕ) = 2 ^ 9 from rfl, ← pow_add,
      Nat.sub_add_cancel hn]; exact hx
  rw [BT.eq, bt, eqTable_ofFn_getD _ (show x % 512 < 2 ^ 9 by omega), eqTable_ofFn_getD _ h2,
    eqAtR_split9 hn]

/-! ## `linkWAll` -/

/-- Family `f`'s weight from the tables (3.x's `linkWOne` at `srcB4`/`mirB4`). -/
def linkWOne4 (ν : NodeKind) (Tτ Tr : BT) (Pr : Array F × Array F) (Eθ : Array F) (f : ℕ) : F :=
  let L := NodeT.fbits f
  let SW := sumTo L fun s => Eθ.getD s 0 * NodeI.eq10 Pr (NodeT.fpos f s)
  let MI := sumTo L fun s => Eθ.getD s 0 * Pr.1.getD ((NodeT.fam f).mbo + s) 0
  let MS := Array.ofFn (n := 4) fun c => Pr.2.getD c 0 * MI
  sumTo 2 fun σ => sumTo (NodeT.fam f).n fun t =>
    Tτ.eq (N4c.srcB4 ν σ f t) * (Tr.eq (N4c.srcB4 ν σ f t) * SW -
      Tr.eq (N4c.mirB4 ν σ f t) * MS.getD ((NodeT.fam f).mir t % 4) 0)

/-- Family `f`'s weight from the per-block arrays of both slots (`EP σ`: `eq(τ, ·) eq(r_blk, ·)` on
the WOTS blocks, `Eτ σ`: `eq(τ, ·)` on them, `EM σ`: `eq(r_blk, ·)` on the `WM` blocks): the field
weight `SW` factored out of the source sum, two products per source. -/
def linkWOneF (EP Eτ EM : ℕ → Array F) (Pr : Array F × Array F) (Eθ : Array F) (f : ℕ) : F :=
  let L := NodeT.fbits f
  let SW := sumTo L fun s => Eθ.getD s 0 * NodeI.eq10 Pr (NodeT.fpos f s)
  let MI := sumTo L fun s => Eθ.getD s 0 * Pr.1.getD ((NodeT.fam f).mbo + s) 0
  let MS := Array.ofFn (n := 4) fun c => Pr.2.getD c 0 * MI
  sumTo 2 fun σ => SW * (sumTo (NodeT.fam f).n fun t => (EP σ).getD ((NodeT.fam f).src t) 0) -
    sumTo (NodeT.fam f).n fun t => (Eτ σ).getD ((NodeT.fam f).src t) 0 *
      (EM σ).getD ((NodeT.fam f).mir t / 4) 0 * MS.getD ((NodeT.fam f).mir t % 4) 0

/-- **`linkWAll`, computed** on the packed points `tt = τ ‖ θ`, `rr = r_blk ‖ r_pos` (`nb + 10`
entries each): per slot the 498 WOTS blocks' `eq(τ, ·)` and `eq(τ, ·) eq(r_blk, ·)`, the 146 `WM`
blocks' `eq(r_blk, ·)`, shared by the eight families. -/
def linkWAll4I (ν : NodeKind) (tt rr : Array F) : Array F :=
  let n := nbN ν
  let Tτ := bt n tt; let Tr := bt n rr
  let Pθ := NodeI.tab10 (fun l => tt.getD (n + l) 0)
  let Pr := NodeI.tab10 (fun l => rr.getD (n + l) 0)
  let Eθ := Array.ofFn (n := 256) fun s => NodeI.eq10 Pθ s
  let Eτ0 := Array.ofFn (n := 498) fun o => Tτ.eq (N4c.wotsB ν 0 + o)
  let Eτ1 := Array.ofFn (n := 498) fun o => Tτ.eq (N4c.wotsB ν 1 + o)
  let EP0 := Array.ofFn (n := 498) fun o => Eτ0.getD o 0 * Tr.eq (N4c.wotsB ν 0 + o)
  let EP1 := Array.ofFn (n := 498) fun o => Eτ1.getD o 0 * Tr.eq (N4c.wotsB ν 1 + o)
  let EM0 := Array.ofFn (n := 146) fun o => Tr.eq (N4c.wmB ν 0 + o)
  let EM1 := Array.ofFn (n := 146) fun o => Tr.eq (N4c.wmB ν 1 + o)
  Array.ofFn (n := nLinkFam) fun f => linkWOneF (fun σ => if σ = 0 then EP0 else EP1)
    (fun σ => if σ = 0 then Eτ0 else Eτ1) (fun σ => if σ = 0 then EM0 else EM1) Pr Eθ f

/-- **The shared form is the per-source form** (`linkWOne4`). -/
theorem linkWOneF_eq (ν : NodeKind) (Tτ Tr : BT) (Pr : Array F × Array F) (Eθ : Array F) (f : ℕ) :
    linkWOneF (fun σ => if σ = 0 then Array.ofFn (n := 498) fun o =>
          (Array.ofFn (n := 498) fun o => Tτ.eq (N4c.wotsB ν 0 + o)).getD o 0 * Tr.eq (N4c.wotsB ν 0 + o)
        else Array.ofFn (n := 498) fun o =>
          (Array.ofFn (n := 498) fun o => Tτ.eq (N4c.wotsB ν 1 + o)).getD o 0 * Tr.eq (N4c.wotsB ν 1 + o))
      (fun σ => if σ = 0 then Array.ofFn (n := 498) fun o => Tτ.eq (N4c.wotsB ν 0 + o)
        else Array.ofFn (n := 498) fun o => Tτ.eq (N4c.wotsB ν 1 + o))
      (fun σ => if σ = 0 then Array.ofFn (n := 146) fun o => Tr.eq (N4c.wmB ν 0 + o)
        else Array.ofFn (n := 146) fun o => Tr.eq (N4c.wmB ν 1 + o)) Pr Eθ f =
      linkWOne4 ν Tτ Tr Pr Eθ f := by
  unfold linkWOneF linkWOne4
  dsimp only
  simp only [sumTo_eq]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ' := Finset.mem_range.1 hσ
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have hs := fam_src_lt4 ht'
  have hm : (NodeT.fam f).mir t / 4 < 146 := by have := fam_mir_lt4 ht'; omega
  unfold N4c.srcB4 N4c.mirB4
  rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;>
    simp only [if_true, one_ne_zero, if_false, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hs, hm,
      dite_true, Option.getD_some] <;> ring

theorem linkWOne4_eq (ν : NodeKind) (f : ℕ) (τ rb : Array F) (θ' rp' : Fin 10 → F) :
    linkWOne4 ν (bt (nbN ν) τ) (bt (nbN ν) rb) (NodeI.tab10 rp')
      (Array.ofFn (n := 256) fun s => NodeI.eq10 (NodeI.tab10 θ') s) f =
      linkW4S ν f (ptA (nbN ν) τ) θ' (ptA (nbN ν) rb) rp' := by
  have hE : ∀ s < NodeT.fbits f, (Array.ofFn (n := 256) fun s => NodeI.eq10 (NodeI.tab10 θ') s).getD s 0 =
      eqAtR θ' s := fun s hs => by
    have : s < 256 := by have := NodeI.mbo_le f; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos this, Option.getD_some, NodeI.eq10_eq]
  have hSW : (sumTo (NodeT.fbits f) fun s =>
      (Array.ofFn (n := 256) fun s => NodeI.eq10 (NodeI.tab10 θ') s).getD s 0 *
        NodeI.eq10 (NodeI.tab10 rp') (NodeT.fpos f s)) = NodeT.slotWL (NodeT.fpos f) (NodeT.fbits f) θ' rp' := by
    rw [sumTo_eq, NodeT.slotWL]
    exact Finset.sum_congr rfl fun s hs => by rw [hE s (Finset.mem_range.1 hs), NodeI.eq10_eq]
  have hMS : ∀ t, ((Array.ofFn (n := 4) fun c => (NodeI.tab10 rp').2.getD c 0 *
      sumTo (NodeT.fbits f) fun s =>
        (Array.ofFn (n := 256) fun s => NodeI.eq10 (NodeI.tab10 θ') s).getD s 0 *
        (NodeI.tab10 rp').1.getD ((NodeT.fam f).mbo + s) 0).getD ((NodeT.fam f).mir t % 4) 0) =
      NodeT.slotWL (NodeT.mpos f t) (NodeT.fbits f) θ' rp' := fun t => by
    have hc : (NodeT.fam f).mir t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hc, Option.getD_some, sumTo_eq,
      Finset.mul_sum, NodeT.slotWL]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    have hb := NodeI.mbo_le f
    rw [hE s hs', NodeT.mpos, ← NodeI.eq10_eq rp', NodeI.eq10,
      show (256 * ((NodeT.fam f).mir t % 4) + (NodeT.fam f).mbo + s) % 256 = (NodeT.fam f).mbo + s by omega,
      show (256 * ((NodeT.fam f).mir t % 4) + (NodeT.fam f).mbo + s) / 256 % 4 =
        (NodeT.fam f).mir t % 4 by omega]
    ring
  unfold linkWOne4 linkW4S
  dsimp only
  rw [hSW]
  simp only [hMS]
  simp only [sumTo_eq]
  have hn := (nbN_bounds ν).1
  refine Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun t ht => ?_
  have hσ' := mem_range.1 hσ
  have ht' := mem_range.1 ht
  rw [bt_eq hn _ (srcB4_lt' ν hσ' ht'), bt_eq hn _ (srcB4_lt' ν hσ' ht'),
    bt_eq hn _ (mirB4_lt' ν hσ' ht')]

/-- **`linkWAll4I` meets `linkWAll4S`** (every operand). -/
theorem linkWAll4_meets (ν : NodeKind) (tt rr : Array F) : linkWAll4I ν tt rr = linkWAll4S ν tt rr := by
  unfold linkWAll4I linkWAll4S
  dsimp only
  congr 1
  funext f
  exact (linkWOneF_eq ν _ _ _ _ f).trans (linkWOne4_eq ν f tt rr _ _)

/-! ## The node's op implementation -/

/-- **`implN4 base tS ν`**: the node kind `ν`'s ops for `VnodeC` (`implSeg`'s analogue): `base ν`
(the node plan's other ops) with the 4.1 node's `rsWeight` (S-T2's `rsWeightF4 ν`, by
`Impl.withRS4`), `shiftMask`, `linkWAll`, 3.x's `slotW` (kind-free, the node's slot maps 0 and 2),
and `targetS` from `tS`. A node program's kind index is `N30`
(`KindP.ofNode`), so the node branch is the one taken. -/
def implN4 (base : NodeKind → OpImpl) (tS : NodeKind → Array F → Array F) (ν : NodeKind) : OpImpl :=
  { Impl.withRS4 (base ν) ν with
    targetS := fun κ r => if κ.isNode then tS ν r else (base ν).targetS κ r
    slotW := fun _ => slotWI
    linkWAll := fun κ tt rr => if κ.isNode then linkWAll4I ν tt rr else (base ν).linkWAll κ tt rr
    shiftMask := shiftMask4I ν }

/-- Its specification (`rsWeightS4 ν`, and `targetSNode4S`, `slotWS`, `linkWAll4S`, `shiftMask4S` on a
  node). -/
def specN4 (base : NodeKind → OpSpec) (ν : NodeKind) : OpSpec :=
  { Impl.withRS4S (base ν) ν with
    targetS := fun κ r => if κ.isNode then targetSNode4S ν r else (base ν).targetS κ r
    slotW := fun _ => slotWS
    linkWAll := fun κ tt rr => if κ.isNode then linkWAll4S ν tt rr else (base ν).linkWAll κ tt rr
    shiftMask := shiftMask4S ν }

/-- **`implN4 ⊨ specN4`**, given the base's ops and a `targetS` meeting `targetSNode4S`. -/
theorem implN4_meets {base : NodeKind → OpImpl} {spec : NodeKind → OpSpec}
    {tS : NodeKind → Array F → Array F} (ν : NodeKind) (h : (base ν).Meets (spec ν))
    (htS : ∀ r, tS ν r = targetSNode4S ν r) : (implN4 base tS ν).Meets (specN4 spec ν) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h13, h14, -, h16, h17⟩ :=
    Impl.withRS4_meets ν h
  refine ⟨h1, fun κ r => ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun _ s a b => slotW_meets s a b,
    h13, fun κ tt rr => ?_, shiftMask4_meets ν, h16, h17⟩
  · simp only [implN4, specN4]
    split_ifs
    exacts [htS r, h2 κ r]
  · simp only [implN4, specN4]
    split_ifs
    exacts [linkWAll4_meets ν tt rr, h14 κ tt rr]

/-! ## Controls -/

section Controls
open NodeT

/-- The masked weights at Boolean block points: `lkE` reads `[lk y₀ ∧ y₁ = y₀]`, `lkSh` reads
`[lk y₀ ∧ y₁ = y₀ + 1]`. -/
theorem lk_cube (ν : NodeKind) {y₀ y₁ : ℕ} (h0 : y₀ < 2 ^ nbN ν) (h1 : y₁ < 2 ^ nbN ν) :
    lkE ν (cubeN (nbN ν) y₀) (cubeN (nbN ν) y₁) = (if N4c.chainLk4 ν y₀ ∧ y₁ = y₀ then 1 else 0) ∧
      lkSh ν (cubeN (nbN ν) y₀) (cubeN (nbN ν) y₁) = if N4c.chainLk4 ν y₀ ∧ y₁ = y₀ + 1 then 1 else 0 := by
  have hz : ∀ y ∈ range (2 ^ nbN ν), y ≠ y₀ → eqAtR (cubeN (nbN ν) y₀) y = 0 := fun y hy hne => by
    rw [eqAtR_cubeN h0 (mem_range.1 hy), if_neg hne]
  have hlk : N4c.chainLk4 ν y₀ = true → y₀ + 1 < 2 ^ nbN ν := fun e => by
    have := (chainLk4_iff ν y₀).1 e; have := chLen_facts ν; have := wotsB_hUsed ν (σ := 0) (by norm_num)
    omega
  unfold lkE lkSh
  rw [Finset.sum_eq_single_of_mem y₀ (mem_range.2 h0) fun y hy hne => by rw [hz y hy hne]; simp,
    Finset.sum_eq_single_of_mem y₀ (mem_range.2 h0) fun y hy hne => by rw [hz y hy hne]; simp,
    eqAtR_cubeN h0 h0, if_pos rfl, one_mul, one_mul]
  constructor
  · by_cases e : N4c.chainLk4 ν y₀ = true
    · rw [if_pos e, eqAtR_cubeN h1 h0]; simp [e, eq_comm]
    · simp [e]
  · by_cases e : N4c.chainLk4 ν y₀ = true
    · rw [if_pos e, eqAtR_cubeN h1 (hlk e)]; simp [e, eq_comm]
    · simp [e]

/-- (+) `shiftMask4I`'s `Sh` links block 0 to block 1; (−) it does not link chain 0's last block to
chain 1's start (the unmasked shift would), and `E` is `0` there. -/
theorem shiftMask4_ctrl :
    (shiftMask4I .N4 (Array.ofFn (cubeN (nbN .N4) 0)) (Array.ofFn (cubeN (nbN .N4) 1))).2.1 = 1 ∧
    (shiftMask4I .N4 (Array.ofFn (cubeN (nbN .N4) (N4c.chLen .N4 0 - 1)))
      (Array.ofFn (cubeN (nbN .N4) (N4c.chLen .N4 0)))).2.1 = 0 ∧
    (shiftMask4I .N4 (Array.ofFn (cubeN (nbN .N4) (N4c.chLen .N4 0 - 1)))
      (Array.ofFn (cubeN (nbN .N4) (N4c.chLen .N4 0 - 1)))).1 = 0 := by
  have hL : N4c.chLen .N4 0 < 2 ^ nbN .N4 := by decide
  have h1 : 1 < 2 ^ nbN .N4 := by decide
  have e0 : N4c.chainLk4 .N4 0 = true := by decide
  have e1 : N4c.chainLk4 .N4 (N4c.chLen .N4 0 - 1) = false := by decide
  simp only [shiftMask4_meets, shiftMask4S, NodeI.ptA_ofFn]
  refine ⟨?_, ?_, ?_⟩
  · rw [(lk_cube .N4 (by omega) h1).2, if_pos ⟨e0, rfl⟩]
  · rw [(lk_cube .N4 (by omega) hL).2, if_neg (by simp [e1])]
  · rw [(lk_cube .N4 (by omega) (by omega)).1, if_neg (by simp [e1])]

/-- Family `x` at `τ` = its first source (slot 0, step 0). -/
theorem linkW4S_x0 (ν : NodeKind) (θ : Fin 10 → F) (rb : Fin (nbN ν) → F) (rp' : Fin 10 → F) :
    linkW4S ν 0 (cubeN (nbN ν) (N4c.srcB4 ν 0 0 0)) θ rb rp' =
      eqAtR rb (N4c.srcB4 ν 0 0 0) * slotWL (fpos 0) (fbits 0) θ rp' -
        eqAtR rb (N4c.mirB4 ν 0 0 0) * slotWL (mpos 0 0) (fbits 0) θ rp' := by
  have hn : (fam 0).n = 399 := rfl
  have hs : ∀ σ t, N4c.srcB4 ν σ 0 t = N4c.wotsB ν σ + t := fun _ _ => rfl
  have hw : N4c.wotsB ν 1 = N4c.wotsB ν 0 + 498 := by simp [N4c.wotsB, wotsSlot4]
  have hb := srcB4_lt' ν (σ := 0) (f := 0) (t := 0) (by norm_num) (by rw [hn]; norm_num)
  have h0 : ∀ σ ∈ range 2, ∀ t ∈ range 399, (σ, t) ≠ (0, 0) →
      eqAtR (cubeN (nbN ν) (N4c.srcB4 ν 0 0 0)) (N4c.srcB4 ν σ 0 t) = 0 := by
    intro σ hσ t ht hne
    have h1 := mem_range.1 hσ
    have h2 := mem_range.1 ht
    rw [eqAtR_cubeN hb (srcB4_lt' ν h1 (by rw [hn]; exact h2)), if_neg]
    rw [hs, hs]
    intro h
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl
    · exact hne (by rw [Prod.mk.injEq]; omega)
    · omega
  unfold linkW4S
  rw [hn, Finset.sum_eq_single_of_mem 0 (by simp) fun σ hσ hne => Finset.sum_eq_zero fun t ht => by
    rw [h0 σ hσ t ht (by simp [hne]), zero_mul]]
  rw [Finset.sum_eq_single_of_mem 0 (by simp) fun t ht hne => by
    rw [h0 0 (by simp) t ht (by simp [hne]), zero_mul]]
  rw [eqAtR_cubeN hb hb, if_pos rfl, one_mul]

/-- (+) Family `x`'s indicator on `N4`: source block, field bit 0 at position 600 (byte 11) reads
`1`; (−) position 601 (bit 1, a wrong offset) reads `0`. -/
theorem linkW4_ctrl :
    linkW4S .N4 0 (cubeN 18 (N4c.srcB4 .N4 0 0 0)) (cubeN 10 0) (cubeN 18 (N4c.srcB4 .N4 0 0 0))
      (cubeN 10 600) = 1 ∧
    linkW4S .N4 0 (cubeN 18 (N4c.srcB4 .N4 0 0 0)) (cubeN 10 0) (cubeN 18 (N4c.srcB4 .N4 0 0 0))
      (cubeN 10 601) = 0 := by
  have hb : fbits 0 = 256 := rfl
  have hs := srcB4_lt' .N4 (σ := 0) (f := 0) (t := 0) (by norm_num) (by decide)
  have hm := mirB4_lt' .N4 (σ := 0) (f := 0) (t := 0) (by norm_num) (by decide)
  have hf : ∀ s < 256, fpos 0 s < 2 ^ 10 := fun s hs => by simp only [fpos, fam]; omega
  have hp : ∀ s < 256, mpos 0 0 s < 2 ^ 10 := fun s hs => by simp only [mpos, fam, id]; omega
  refine ⟨?_, ?_⟩ <;>
    rw [show (18 : ℕ) = nbN .N4 from rfl, linkW4S_x0, hb,
      slotWL_cube (by norm_num) (by norm_num) hf (by norm_num),
      slotWL_cube (by norm_num) (by norm_num) hp (by norm_num), eqAtR_cubeN hs hs]
  · simp [fpos, mpos, fam]
  · simp [fpos, mpos, fam]

end Controls

end NI4
end FR
