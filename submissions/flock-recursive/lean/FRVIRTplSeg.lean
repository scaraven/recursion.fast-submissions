-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.11; stage S-E12e, track L-circ).
import FRVIRTplMask

/-!
# The replay template of a segment's `shiftMask` (revision 4.1, B-12)

A segment's `shiftMask` is `Rev4.shiftSegI τL r` (`FRSegTarget4`): on the operand `τL = τ ‖ L`
(entries `0 … 17` the point, `18 … 35` the bits of the last block `L`) and the 18 block coordinates
`r`, the triple `(eq(τ, r), shift(τ, r) + [L + 1 < 2^18]·eq(τ, L)·eq(r, L + 1), eq(r, 0))`.
`FRSegTarget4` is downstream of this module, so the value is a copy, **`segMaskV`**
(`FRVIRTpl4Bridge.segMaskV_eq`: it is `shiftSegI`).

**`tplShiftSeg`** mirrors it gate for gate (≈ 300 rows):

* the bits `b_l = [τL₁₈₊ₗ = 1]` (`isOneG`: an inverse of `x − 1` and one product);
* `eq(τ, r)` (`facsG` and a product, as `tplEqPt`) and `shift(τ, r)` (`shiftG`, as `tplShiftEq`);
* `eq(τ, L)`: per coordinate `b τ + (1 − b)(1 − τ)` (`facsG`);
* the carries `c₀ = 1`, `c_{l+1} = c_l b_l` (`scanG`), the bits of `L + 1`,
  `d_l = b_l + c_l − 2c_{l+1}` (linear; `testBit_succ_carry`), and `eq(r, L + 1)` from them;
* the guard `[L + 1 < 2^18] = 1 − c₁₈` (`lt_two_pow_iff_carry`), and `eq(r, 0)`.

**`tplShiftSeg_ok`**: the gate equations give `segMaskV`.
-/

namespace FR
namespace Tpl
open Circ Finset

variable {e : Env}

/-! ## The value (a copy of `Rev4.shiftSegI`) -/

/-- The number whose bit `l < 18` is set iff entry `o + l` of `a` is `1` (`Rev4.lastAt`). -/
def lastAtV (a : Array F) (o : ℕ) : ℕ := ∑ l ∈ range 18, if a.getD (o + l) 0 = 1 then 2 ^ l else 0

/-- **A segment's `shiftMask`** (`Rev4.shiftSegI`, a copy). -/
def segMaskV (τL r : Array F) : F × F × F :=
  let τ := Array.ofFn (Impl.ptA 18 τL); let ρ := Array.ofFn (Impl.ptA 18 r)
  let L := lastAtV τL 18
  (eqPoint τ ρ,
   Impl.shiftEqI τ ρ + (if L + 1 < 2 ^ 18 then Impl.eqAtR (Impl.ptA 18 τL) L * Impl.eqAtR (Impl.ptA 18 r) (L + 1)
     else 0),
   Impl.eqAtR (Impl.ptA 18 r) 0)

/-! ## Bits -/

theorem sum_bitsP_lt (p : ℕ → Prop) [DecidablePred p] : ∀ n, (∑ k ∈ range n, if p k then 2 ^ k else 0) < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, pow_succ]; have := sum_bitsP_lt p n; split_ifs <;> omega

theorem testBit_sum_bitsP (p : ℕ → Prop) [DecidablePred p] : ∀ n j,
    (∑ k ∈ range n, if p k then 2 ^ k else 0).testBit j = decide (j < n ∧ p j)
  | 0, j => by simp
  | n + 1, j => by
    have e : (∑ k ∈ range (n + 1), if p k then 2 ^ k else 0) =
        2 ^ n * (if p n then 1 else 0) + ∑ k ∈ range n, if p k then 2 ^ k else 0 := by
      rw [sum_range_succ]; split_ifs <;> ring
    rw [e, Nat.testBit_two_pow_mul_add _ (sum_bitsP_lt p n), testBit_sum_bitsP p n]
    by_cases h : j < n
    · rw [if_pos h]; simp [h, show j < n + 1 by omega]
    · rw [if_neg h]
      obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by omega⟩
      rw [Nat.add_sub_cancel_left]
      rcases d with _ | d
      · by_cases hp : p n <;> simp [hp]
      · by_cases hp : p n <;> simp [hp, Nat.testBit_succ] <;> omega

theorem lastAtV_lt (a : Array F) (o : ℕ) : lastAtV a o < 2 ^ 18 := sum_bitsP_lt _ 18

theorem testBit_lastAtV (a : Array F) (o : ℕ) {l : ℕ} (hl : l < 18) :
    (lastAtV a o).testBit l = decide (a.getD (o + l) 0 = 1) := by
  rw [lastAtV, testBit_sum_bitsP]; simp [hl]

/-- The low bits `0 … l − 1` all set. -/
def allLow (L l : ℕ) : Bool := (List.range l).all L.testBit

/-- **The bits of `L + 1` by the carry**: bit `l` of `L + 1` is bit `l` of `L` flipped iff the bits
below `l` are all set. -/
theorem testBit_succ_carry : ∀ (l L : ℕ), (L + 1).testBit l = (L.testBit l ^^ allLow L l)
  | 0, L => by
    simp only [allLow, List.range_zero, List.all_nil, Bool.xor_true, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one L with h | h <;> simp [h, Nat.add_mod]
  | l + 1, L => by
    have hr : allLow L (l + 1) = (L.testBit 0 && allLow (L / 2) l) := by
      simp only [allLow, List.range_succ_eq_map, List.all_cons, List.all_map]
      simp [Function.comp_def, Nat.testBit_succ]
    rw [Nat.testBit_succ, Nat.testBit_succ, hr, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one L with h | h
    · rw [show (L + 1) / 2 = L / 2 by omega]; simp [h]
    · rw [show (L + 1) / 2 = L / 2 + 1 by omega, testBit_succ_carry l (L / 2)]; simp [h]

/-- **`L + 1 < 2^n` iff not every bit of `L < 2^n` is set.** -/
theorem lt_two_pow_iff_carry {L n : ℕ} (hL : L < 2 ^ n) : L + 1 < 2 ^ n ↔ allLow L n = false := by
  constructor
  · intro h
    cases hc : allLow L n
    · rfl
    exfalso
    have : L + 1 = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.zero_testBit]
      by_cases hi : i < n
      · rw [testBit_succ_carry]
        have h1 : L.testBit i = true := by
          simp only [allLow, List.all_eq_true, List.mem_range] at hc; exact hc i hi
        have h2 : allLow L i = true := by
          simp only [allLow, List.all_eq_true, List.mem_range] at hc ⊢
          exact fun j hj => hc j (by omega)
        rw [h1, h2]; rfl
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))
    omega
  · intro hc
    by_contra h
    have : L = 2 ^ n - 1 := by omega
    subst this
    simp only [allLow, List.all_eq_false, List.mem_range, Nat.testBit_two_pow_sub_one] at hc
    obtain ⟨j, hj, h'⟩ := hc; simp [hj] at h'

/-! ## Pieces -/

/-- `[x = 1]`: `a = x − 1`, `i = a⁻¹` (an inverse, two locals), `s = a·i` (one product); the bit
is `1 − s`. -/
def isOneG (x : LinT) (k : ℕ) : List Gate × LinT :=
  ([.inv (x ++ C (-1)), .mul (x ++ C (-1)) (L k)], C 1 ++ sc (-1) (L (k + 2)))

theorem isOneG_ev (h1 : e.one = 1) (x : LinT) (k : ℕ) (h : Eqns e (isOneG x k).1 k) :
    (isOneG x k).2.ev e = if x.ev e = 1 then 1 else 0 := by
  simp only [isOneG, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
  obtain ⟨hi, hm⟩ := h
  simp only [isOneG, ev_append, ev_C, ev_sc, ev_L, h1, hm, hi]
  split_ifs with hx
  · simp [hx]
  · rw [mul_inv_cancel₀ (by intro h0; apply hx; linear_combination h0)]; ring

/-- `isOneG` over a list, three locals each. -/
def isOnesG : List LinT → ℕ → List Gate × List LinT
  | [], _ => ([], [])
  | x :: xs, k => let r := isOnesG xs (k + 3); ((isOneG x k).1 ++ r.1, (isOneG x k).2 :: r.2)

theorem isOnesG_ev (h1 : e.one = 1) : ∀ (xs : List LinT) (k : ℕ), Eqns e (isOnesG xs k).1 k →
    (isOnesG xs k).2.map (LinT.ev e) = xs.map fun x => if x.ev e = 1 then 1 else 0
  | [], _, _ => rfl
  | x :: xs, k, h => by
    simp only [isOnesG, Eqns.append] at h
    have hn : nlocs (isOneG x k).1 = 3 := rfl
    rw [hn] at h
    simp only [isOnesG, List.map_cons, isOneG_ev h1 x k h.1, isOnesG_ev h1 xs (k + 3) h.2]

/-- Per pair `(x, y)`: the product `t = x·y` (one row), the factor `x y + (1 − x)(1 − y)`. -/
def facsG : List (LinT × LinT) → ℕ → List Gate × List LinT
  | [], _ => ([], [])
  | p :: ps, k => let r := facsG ps (k + 1); (.mul p.1 p.2 :: r.1, eqFac p.1 p.2 (L k) :: r.2)

theorem facsG_ev (h1 : e.one = 1) : ∀ (ps : List (LinT × LinT)) (k : ℕ), Eqns e (facsG ps k).1 k →
    (facsG ps k).2.map (LinT.ev e) =
      ps.map fun p => p.1.ev e * p.2.ev e + (1 - p.1.ev e) * (1 - p.2.ev e)
  | [], _, _ => rfl
  | p :: ps, k, h => by
    simp only [facsG, Eqns.cons, Gate.nloc, Gate.Eqn] at h
    simp only [facsG, List.map_cons, facsG_ev h1 ps (k + 1) h.2,
      eqFac_ev h1 p.1 p.2 (L k) (by rw [ev_L]; exact h.1)]

theorem prod_range_list {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).prod = ∏ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_range_list f n,
      prod_range_succ]; simp

/-- **`eq(x, c)` at a constant index** over `n` coordinate forms: one product per coordinate. -/
def eqAtG (n : ℕ) (x : ℕ → LinT) (c k : ℕ) : List Gate × LinT :=
  prodG (C 1) ((List.range n).map fun l => if c.testBit l then x l else C 1 ++ sc (-1) (x l)) k

theorem eqAtG_ev (h1 : e.one = 1) (n : ℕ) (x : ℕ → LinT) (c k : ℕ) (h : Eqns e (eqAtG n x c k).1 k) :
    (eqAtG n x c k).2.ev e = Impl.eqAtR (fun l : Fin n => (x l).ev e) c := by
  rw [eqAtG, prodG_ev _ _ _ h, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F), Impl.eqAtR,
    Fin.prod_univ_eq_prod_range (fun l => if c.testBit l then (x l).ev e else 1 - (x l).ev e)]
  apply Finset.prod_congr rfl
  intro l _
  simp only [Function.comp_apply]
  split_ifs <;> simp [h1, sub_eq_add_neg]

/-! ## The template -/

/-- The point's coordinates `τL₀ … τL₁₇`, the bit entries `τL₁₈ … τL₃₅`, `r₀ … r₁₇`. -/
def sτ (n : ℕ) : List LinT := (List.range 18).map (cT n)
def sB (n : ℕ) : List LinT := (List.range 18).map fun l => cT n (18 + l)
def sr (n m : ℕ) : List LinT := (List.range 18).map (cR n m)

/-- **The segment's `shiftMask`** for `τL : AF n`, `r : AF m`, its locals from `k`: the gates and
the three outputs. -/
def segG (n m k : ℕ) : List Gate × List LinT :=
  let B := isOnesG (sB n) k
  let k1 := k + nlocs B.1
  let E := facsG ((List.range 18).map fun l => (cT n l, cR n m l)) k1
  let k2 := k1 + nlocs E.1
  let Ep := prodG (C 1) E.2 k2
  let k3 := k2 + nlocs Ep.1
  let S := shiftG (sτ n) (sr n m) k3
  let k4 := k3 + nlocs S.1
  let T := facsG ((List.range 18).map fun l => (B.2.getD l [], cT n l)) k4
  let k5 := k4 + nlocs T.1
  let Tp := prodG (C 1) T.2 k5
  let k6 := k5 + nlocs Tp.1
  let Cc := scanG (C 1) B.2 k6
  let k7 := k6 + nlocs Cc.1
  let D := facsG ((List.range 18).map fun l =>
    (B.2.getD l [] ++ Cc.2.getD l [] ++ sc (-2) (Cc.2.getD (l + 1) []), cR n m l)) k7
  let k8 := k7 + nlocs D.1
  let Dp := prodG (C 1) D.2 k8
  let k9 := k8 + nlocs Dp.1
  let Z := eqAtG 18 (cR n m) 0 k9
  let k10 := k9 + nlocs Z.1
  let gs := B.1 ++ (E.1 ++ (Ep.1 ++ (S.1 ++ (T.1 ++ (Tp.1 ++ (Cc.1 ++ (D.1 ++ (Dp.1 ++ (Z.1 ++
      [.mul (C 1 ++ sc (-1) (Cc.2.getD 18 [])) Tp.2, .mul (L k10) Dp.2])))))))))
  (gs, [Ep.2, S.2.2 ++ L (k10 + 1), Z.2])

/-- **The template** (locals from `0`). -/
def tplShiftSeg (n m : ℕ) : Tpl := ⟨(segG n m 0).1, (segG n m 0).2⟩

/-! ## Correctness -/

/-- `0/1` of a Boolean. -/
def bv (b : Bool) : F := if b then 1 else 0

theorem getD_ofFn18 (a : Array F) {v : ℕ} (hv : v < 18) :
    (Array.ofFn (Impl.ptA 18 a)).getD v 0 = a.getD v 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hv]; rfl

theorem toList_ofFn18 (a : Array F) :
    (Array.ofFn (Impl.ptA 18 a)).toList = (List.range 18).map fun l => a.getD l 0 :=
  List.ext_getElem (by simp) fun i _ _ => by
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range, Impl.ptA]

/-- The running products' entries: `(scanl (·*·) a xs)[l] = a · Π_{j<l} xs_j`. -/
theorem scanl_getD : ∀ (xs : List F) (a : F) (l : ℕ), l ≤ xs.length →
    (List.scanl (· * ·) a xs).getD l 0 = a * ((xs.take l).prod)
  | [], a, l, h => by simp at h; subst h; simp
  | x :: xs, a, 0, _ => by simp
  | x :: xs, a, l + 1, h => by
    simp only [List.scanl_cons, List.getD_cons_succ, List.take_succ_cons, List.prod_cons]
    rw [scanl_getD xs (a * x) l (by simpa using h)]; ring

theorem prod_bv_take (β : ℕ → Bool) {l : ℕ} (hl : l ≤ 18) :
    (((List.range 18).map fun j => bv (β j)).take l).prod = bv ((List.range l).all β) := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hl]
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.all_append]
    cases (List.range l).all β <;> cases β l <;> simp [bv]

section Proof
variable {τL r : Array F} (hi : InpIs e (τL.toList ++ r.toList))
include hi

set_option maxHeartbeats 1000000 in
/-- **The segment template computes `segMaskV`.** -/
theorem tplShiftSeg_ok (h1 : e.one = 1) (h : Eqns e (tplShiftSeg τL.size r.size).gates 0) :
    (tplShiftSeg τL.size r.size).outs.map (LinT.ev e) =
      encV (.f (segMaskV τL r).1) ++ encV (.f (segMaskV τL r).2.1) ++ encV (.f (segMaskV τL r).2.2) := by
  have vτ : ∀ l, (cT τL.size l).ev e = τL.getD l 0 := cT_ev hi
  have vr : ∀ l, (cR τL.size r.size l).ev e = r.getD l 0 := cR_ev hi
  have hLlt : lastAtV τL 18 < 2 ^ 18 := lastAtV_lt τL 18
  have hbit : ∀ l < 18, bv ((lastAtV τL 18).testBit l) = if τL.getD (18 + l) 0 = 1 then 1 else 0 :=
    fun l hl => by rw [testBit_lastAtV τL 18 hl]; by_cases hx : τL.getD (18 + l) 0 = 1 <;> simp [hx, bv]
  simp only [tplShiftSeg, segG, Eqns.append] at h ⊢
  obtain ⟨hB, hE, hEp, hS, hT, hTp, hC, hD, hDp, hZ, hL⟩ := h
  simp only [Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at hL
  obtain ⟨hL1, hL2⟩ := hL
  simp only [segMaskV, List.map_cons, List.map_nil, encV, List.cons_append, List.nil_append, ev_append, ev_L,
    hL2, hL1, ev_sc, ev_C, h1]
  generalize lastAtV τL 18 = Lv at hLlt hbit ⊢
  have hbig : ∀ l, 18 ≤ l → Lv.testBit l = false := fun l hl =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by norm_num) hl))
  -- the bits
  have vB := isOnesG_ev h1 _ _ hB
  have bBmap : (isOnesG (sB τL.size) 0).2.map (LinT.ev e) =
      (List.range 18).map fun l => bv (Lv.testBit l) := by
    rw [vB, sB, List.map_map]
    exact List.map_congr_left fun l hl => by
      rw [Function.comp_apply, vτ, hbit l (List.mem_range.1 hl)]
  have bB : ∀ l, ((isOnesG (sB τL.size) 0).2.getD l []).ev e = bv (Lv.testBit l) := fun l => by
    rw [getD_map_ev, bBmap]
    by_cases hl : l < 18
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]; rfl
    · rw [List.getD_eq_default _ _ (by simp; omega), hbig l (by omega)]; rfl
  -- the carries
  have cv : ∀ K, Eqns e (scanG (C 1) (isOnesG (sB τL.size) 0).2 K).1 K → ∀ l,
      ((scanG (C 1) (isOnesG (sB τL.size) 0).2 K).2.getD l []).ev e = bv (allLow Lv l) := by
    intro K hK l
    have oC := scanG_ev _ _ _ hK
    rw [bBmap, ev_C, h1, mul_one] at oC
    rw [getD_map_ev, oC]
    by_cases hl : l ≤ 18
    · rw [scanl_getD _ _ _ (by simpa using hl), one_mul, prod_bv_take _ hl]; rfl
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have : allLow Lv l = false := by
        simp only [allLow, List.all_eq_false, List.mem_range]
        exact ⟨18, by omega, by rw [hbig 18 le_rfl]; decide⟩
      rw [this]; rfl
  have cv' := cv _ hC
  -- the pieces' values
  have oE := prodG_ev _ _ _ hEp
  rw [facsG_ev h1 _ _ hE, ev_C, h1, one_mul, one_mul, List.map_map] at oE
  simp only [Function.comp_def, vτ, vr] at oE
  have oS := shiftG_ev h1 _ _ _ hS
  have mτ : (sτ τL.size).map (LinT.ev e) = (List.range 18).map fun x => τL.getD x 0 := by
    simp only [sτ, List.map_map, Function.comp_def, vτ]
  have mr : (sr τL.size r.size).map (LinT.ev e) = (List.range 18).map fun x => r.getD x 0 := by
    simp only [sr, List.map_map, Function.comp_def, vr]
  rw [mτ, mr] at oS
  have oT := prodG_ev _ _ _ hTp
  rw [facsG_ev h1 _ _ hT, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F)] at oT
  simp only [Function.comp_def, bB, vτ] at oT
  have oD := prodG_ev _ _ _ hDp
  rw [facsG_ev h1 _ _ hD, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F)] at oD
  simp only [Function.comp_def, ev_append, ev_sc, bB, cv', vr] at oD
  have oZ := eqAtG_ev h1 _ _ _ _ hZ
  simp only [vr] at oZ
  have oS2 := congrArg Prod.snd oS
  simp only at oS2
  rw [oE, oT, oD, oZ, cv', oS2]
  simp only [mul_one]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩
  · -- `eq(τ, r)`
    simp only [eqPoint, Array.size_ofFn]
    rw [← foldl_mul_range]
    refine List.foldl_ext _ _ _ fun acc v hv => ?_
    have hv := List.mem_range.1 hv
    simp only [getD_ofFn18 _ hv]
  · -- the masked successor
    rw [Impl.shiftEqI, toList_ofFn18, toList_ofFn18]
    congr 1
    have gT : ∏ i ∈ range 18, (bv (Lv.testBit i) * τL.getD i 0 + (1 - bv (Lv.testBit i)) * (1 - τL.getD i 0)) =
        Impl.eqAtR (Impl.ptA 18 τL) Lv := by
      rw [← Fin.prod_univ_eq_prod_range, Impl.eqAtR]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Impl.ptA]
      cases Lv.testBit l <;> simp [bv]
    have gD : ∏ i ∈ range 18, ((bv (Lv.testBit i) + bv (allLow Lv i) + -2 * bv (allLow Lv (i + 1))) * r.getD i 0 +
        (1 - (bv (Lv.testBit i) + bv (allLow Lv i) + -2 * bv (allLow Lv (i + 1)))) * (1 - r.getD i 0)) =
        Impl.eqAtR (Impl.ptA 18 r) (Lv + 1) := by
      rw [← Fin.prod_univ_eq_prod_range, Impl.eqAtR]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Impl.ptA, testBit_succ_carry]
      have ha : allLow Lv (l + 1) = (allLow Lv l && Lv.testBit l) := by
        simp [allLow, List.range_succ, List.all_append]
      rw [ha]
      cases Lv.testBit l <;> cases allLow Lv l <;> simp [bv] <;> ring
    rw [gT, gD]
    have hg := lt_two_pow_iff_carry hLlt
    by_cases hc : Lv + 1 < 2 ^ 18
    · rw [if_pos hc, hg.1 hc]; simp [bv]
    · rw [if_neg hc]
      have : allLow Lv 18 = true := by
        cases h' : allLow Lv 18
        · exact absurd (hg.2 h') hc
        · rfl
      rw [this]; simp [bv, h1]
  · -- `eq(r, 0)`
    rfl

end Proof

/-! ## Controls -/

/-- (+) Three outputs; the instance reads `τL` (36) then `r` (18). -/
theorem tplShiftSeg_outs (n m : ℕ) : (tplShiftSeg n m).outs.length = 3 := rfl

/-- (+) The carry rule on `L = 5` (`101 → 110`); (−) it is not the plain bit (bit 1 flips). -/
theorem carry_ctl : (allLow 5 1, (5 + 1).testBit 1) = (true, true) ∧ (5 : ℕ).testBit 1 = false := by
  decide

/-- (+) `L + 1 < 2^n` fails exactly at `L = 2^n − 1` (all bits set): at `n = 3`, `L = 7` and `L = 6`. -/
theorem guard_ctl : allLow 7 3 = true ∧ allLow 6 3 = false := by decide

end Tpl
end FR
