-- New for lvm6 K1: the tree batch's front (`FORMAT6.md` §6.2 rows 1–5): `δ`, the wiring point `ρ`
-- (`G(5) D(17)`), `D^b`, the fold challenge `u` (`G(1)`): the zero-test tables of (W) and (G), the alive
-- predicates and their escapes.
import Lvm6KHead

/-!
# The front of the tree batch

With `κ = N + 1` row bits (`ρ ∈ E^N`), for a stack `Q`:

* `wTabs κ Q δ`: 58 tables on the `2^N` parent rows `k` — (W) left with `δ` on row 0 (4), (W) right (4),
  and (G) on the child rows `b + 2k` (25 lanes × 2). `AliveR`: they all vanish part-way at `acc`, (R)
  holds and `R`. `treeOkG_of_aliveR`: at `acc = []` this is `TreeOkG ∧ R`. `aliveR_escape`: one
  coordinate of `ρ` escapes at `errG 0 1` (the per-draw form of `gPointSpec`).
* `AliveU`: after `u`, the eight wiring claims at `(ρ, 0)`, (R), the first four output claims and the
  segments' agreement at `(u, ρ)`, and `R`. `aliveU_escape`: from `¬ AliveR ρ`, the draw `u` escapes at
  `errG g 1` (an affine polynomial in `u`).
* Column-claim algebra: `stepMle_rowpt` (a claim at `(ρ, 0, slot o)`), `stepMle_boolpt` (a Boolean
  point), `stepMle_cons` (splitting off the low row bit `u`).
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (Shape statesOfS laneWord segStateS roundsFrom)
open Lvm.E2V
open RecursionFast
open Finset Polynomial
open scoped ENNReal

/-! ## Column claims at structured points -/

theorem stepMle_rowpt {N : ℕ} (Q : Stack) {ρ : List E2} (hρ : ρ.length = N) {o : ℕ} (ho : o < 64) :
    stepMleK (N + 1 + 6) (ρ ++ [0] ++ bitsF o 6) Q =
      ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (k + 2 ^ (N + 1) * o)) := by
  have ha : (ρ ++ [(0 : E2)]).length = N + 1 := by simp [hρ]
  rw [stepMleK, show N + 1 + 6 = N + 1 + (bitsF o 6 : List E2).length by simp,
    col_splitF ha, bitsF_length, sum_eqAtF_bitsF (by omega)]
  generalize 2 ^ (N + 1) * o = c
  have e := col_splitF (h := N) (a := ρ) (s := [(0 : E2)]) hρ (fun x ↦ kF (Q (x + c)))
  simp only [List.length_singleton] at e
  rw [e, pow_one, Finset.sum_range_succ, Finset.sum_range_one]
  simp [eqAtF]

theorem stepMle_boolpt {κ : ℕ} (Q : Stack) {x o : ℕ} (hx : x < 2 ^ κ) (ho : o < 64) :
    stepMleK (κ + 6) (bitsF x κ ++ bitsF o 6 : List E2) Q = kF (Q (x + 2 ^ κ * o)) := by
  rw [stepMleK, show κ + 6 = κ + (bitsF o 6 : List E2).length by simp,
    col_splitF (bitsF_length (F := E2) x κ), bitsF_length, sum_eqAtF_bitsF (F := E2) (by omega),
    sum_eqAtF_bitsF (F := E2) hx]

theorem stepMle_cons {N : ℕ} (u : E2) {ρ : List E2} (_hρ : ρ.length = N) (f : ℕ → K) :
    stepMleK (N + 1) (u :: ρ) f =
      (1 + u) * ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (f (2 * k)) +
        u * ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (f (2 * k + 1)) := by
  rw [stepMleK, sum_cube_succW, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ ↦ ?_) (Finset.sum_congr rfl fun k _ ↦ ?_)
  · rw [eqAtF_succ, if_neg (by omega), show 2 * k / 2 = k by omega]; ring
  · rw [eqAtF_succ, if_pos (by omega), show (2 * k + 1) / 2 = k by omega]; ring

/-! ## The tables of the front -/

/-- (R): row 0's slots `4 … 7` are the words of `h`. -/
def RootOk (κ : ℕ) (Q : Stack) (h : Digest) : Prop := ∀ m < 4, Q (2 ^ κ * (4 + m)) = K.ofLane (dLane h m)

/-- (W) left at slot `m`, with `δ_m` on row 0. -/
def tabL (κ : ℕ) (Q : Stack) (δ : List K) (m k : ℕ) : E2 :=
  kF (Q (k + 2 ^ κ * m)) + kF (outW κ Q (2 * k) m) + (if k = 0 then kF (δ.getD m 0) else 0)

/-- (W) right at slot `4 + m`. -/
def tabR (κ : ℕ) (Q : Stack) (m k : ℕ) : E2 := kF (Q (k + 2 ^ κ * (4 + m))) + kF (outW κ Q (2 * k + 1) m)

/-- (G) at lane `l` on the child rows `b + 2k`. -/
def tabG (κ : ℕ) (Q : Stack) (l b k : ℕ) : E2 :=
  kF (laneWord (roundsFrom 0 12 (inTree κ Q (b + 2 * k))) l) + kF (Q (b + 2 * k + 2 ^ κ * (8 + l)))

/-- The 58 tables. -/
def wTabs (κ : ℕ) (Q : Stack) (δ : List K) : List (ℕ → E2) :=
  (List.range 4).map (tabL κ Q δ) ++ (List.range 4).map (tabR κ Q) ++
    (List.range 25).flatMap fun l ↦ (List.range 2).map (tabG κ Q l)

variable {β : Type}

/-- Alive after part of `ρ`. -/
def AliveR (κ : ℕ) (stk : β → Stack) (h : Digest) (R : β → Prop) (δ : List K) (pre : List E2)
    (q : β) : Prop :=
  pre.length ≤ κ - 1 ∧ (∀ t ∈ wTabs κ (stk q) δ, ZeroOnF t pre (κ - 1)) ∧ RootOk κ (stk q) h ∧ R q


/-- The wiring claims at `(ρ, 0)` (rows 2–3). -/
def WireOk (κ : ℕ) (Q : Stack) (δ : List K) (ρ dd : List E2) : Prop :=
  (∀ m < 4, stepMleK (κ + 6) (ρ ++ [0] ++ bitsF m 6) Q = dd.getD m 0 + eqAtF ρ 0 * kF (δ.getD m 0)) ∧
    ∀ m < 4, stepMleK (κ + 6) (ρ ++ [0] ++ bitsF (4 + m) 6) Q = dd.getD (4 + m) 0

/-- Alive after `u`. -/
def AliveU (κ : ℕ) (stk : β → Stack) (h : Digest) (R : β → Prop) (δ : List K) (ρ dd : List E2)
    (u : E2) (q : β) : Prop :=
  WireOk κ (stk q) δ ρ dd ∧ RootOk κ (stk q) h ∧
    (∀ m < 4, stepMleK κ (u :: ρ) (fun x ↦ outW κ (stk q) x m) = (oLow u dd).getD m 0) ∧
    midAgreeV κ (Itree κ (stk q)) (u :: ρ) ∧ R q

/-! ## Membership in the tables -/

theorem tabL_mem (κ : ℕ) (Q : Stack) (δ : List K) {m : ℕ} (hm : m < 4) : tabL κ Q δ m ∈ wTabs κ Q δ :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.2 hm)))

theorem tabR_mem (κ : ℕ) (Q : Stack) (δ : List K) {m : ℕ} (hm : m < 4) : tabR κ Q m ∈ wTabs κ Q δ :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hm)))

theorem tabG_mem (κ : ℕ) (Q : Stack) (δ : List K) {l b : ℕ} (hl : l < 25) (hb : b < 2) :
    tabG κ Q l b ∈ wTabs κ Q δ :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl,
    List.mem_map_of_mem (List.mem_range.2 hb)⟩)

theorem mem_wTabs {κ : ℕ} {Q : Stack} {δ : List K} {t : ℕ → E2} (ht : t ∈ wTabs κ Q δ) :
    (∃ m < 4, t = tabL κ Q δ m) ∨ (∃ m < 4, t = tabR κ Q m) ∨
      ∃ l < 25, ∃ b < 2, t = tabG κ Q l b := by
  simp only [wTabs, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at ht
  rcases ht with (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩) | ⟨l, hl, b, hb, rfl⟩
  · exact Or.inl ⟨m, hm, rfl⟩
  · exact Or.inr (Or.inl ⟨m, hm, rfl⟩)
  · exact Or.inr (Or.inr ⟨l, hl, b, hb, rfl⟩)

theorem kF_inj {a b : K} (h : (kF a : E2) = kF b) : a = b := (algebraMap K E2).injective h

theorem eq_of_add_zero {a b : E2} (h : a + b = 0) : a = b := addF_eq_zero_iff.1 h

/-! ## The start: `TreeOkG` -/

/-- **Alive at the start is the tree relation.** -/
theorem treeOkG_of_aliveR {N : ℕ} {stk : β → Stack} {h : Digest} {R : β → Prop} {δ : List K} {q : β}
    (ha : AliveR (N + 1) stk h R δ [] q) : TreeOkG (N + 1) (stk q) h ∧ R q := by
  obtain ⟨-, hz, hroot, hR⟩ := ha
  have hz' : ∀ t ∈ wTabs (N + 1) (stk q) δ, ∀ v < 2 ^ N, t v = 0 := fun t ht ↦ by
    have := hz t ht
    rwa [Nat.add_sub_cancel, zeroOnF_nil] at this
  refine ⟨⟨fun k h1 hk m hm ↦ ?_, fun k hk m hm ↦ ?_, hroot, fun x hx ↦ ?_⟩, hR⟩
  · rw [Nat.add_sub_cancel] at hk
    have := hz' _ (tabL_mem _ _ δ hm) k hk
    rw [tabL, if_neg (by omega), add_zero] at this
    exact kF_inj (eq_of_add_zero this)
  · rw [Nat.add_sub_cancel] at hk
    have := hz' _ (tabR_mem _ _ δ hm) k hk
    exact kF_inj (eq_of_add_zero this)
  · have hx2 : x / 2 < 2 ^ N := by rw [pow_succ] at hx; omega
    have hxe : x % 2 + 2 * (x / 2) = x := by omega
    refine Vector.ext fun l hl ↦ ?_
    have := hz' _ (tabG_mem _ _ δ hl (Nat.mod_lt x (by norm_num))) (x / 2) hx2
    rw [tabG, hxe] at this
    have e := (kF_inj (eq_of_add_zero this)).symm
    rw [midTree, Vector.getElem_ofFn, ← LeanVM.Protocol.KeccakGkr.lane_eq _ hl]
    show K.lane (stk q (x + 2 ^ (N + 1) * (8 + l))) = LeanVM.Semantics.Keccak.lane _ l
    simp only [e, laneWord, Lvm.KG.lane_ofLane']

/-! ## Escapes -/

/-- **One coordinate of `ρ`** escapes at `errG 0 1`. -/
theorem aliveR_escape {N : ℕ} (stk : β → Stack) (h : Digest) (R : β → Prop) (δ : List K)
    (acc : List E2) (q : β) (hq : ¬ AliveR (N + 1) stk h R δ acc q) :
    avgE (fun c ↦ indE (powOK 0 c ∧ AliveR (N + 1) stk h R δ (acc ++ [e2OfE c]) q)) ≤ errG 0 1 := by
  have zero_bound : ∀ (P : E → Prop), (∀ c, ¬ P c) → avgE (fun c ↦ indE (P c)) ≤ errG 0 1 :=
    fun P hP ↦ (avgE_le_of_le fun c ↦ (indE_of_not (hP c)).le).trans zero_le
  have hN : N + 1 - 1 = N := by omega
  simp only [AliveR, hN] at hq ⊢
  by_cases hl : acc.length < N
  · by_cases hRR : RootOk (N + 1) (stk q) h ∧ R q
    · have : ¬ ∀ t ∈ wTabs (N + 1) (stk q) δ, ZeroOnF t acc N :=
        fun hz ↦ hq ⟨hl.le, hz, hRR.1, hRR.2⟩
      push_neg at this
      obtain ⟨t, ht, hnz⟩ := this
      exact (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, hc.2.2.1 t ht⟩).trans
        (zeroOnG_escape (g := 0) (by norm_num) t hl hnz)
    · exact zero_bound _ fun c hc ↦ hRR ⟨hc.2.2.2.1, hc.2.2.2.2⟩
  · exact zero_bound _ fun c hc ↦ by
      have := hc.2.1
      rw [List.length_append, List.length_singleton] at this
      omega

/-- A nonzero affine polynomial `(1 + u)·a + u·b` vanishes at an accepted draw with probability at
most `errG g 1`. -/
theorem affine_escape {g : ℕ} (hg : g ≤ 64) {a b : E2} (hab : ¬ (a = 0 ∧ b = 0)) (P : E2 → Prop)
    (hP : ∀ u, P u → (1 + u) * a + u * b = 0) :
    avgE (fun c ↦ indE (powOK g c ∧ P (e2OfE c))) ≤ errG g 1 := by
  have hne : (C a + C (a + b) * X : E2[X]) ≠ 0 := by
    intro he
    have h0 : a = 0 := by have := congrArg (coeff · 0) he; simpa using this
    refine hab ⟨h0, ?_⟩
    have := congrArg (coeff · 1) he
    simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, one_ne_zero, if_false,
      coeff_zero] at this
    rw [h0, zero_add, mul_one] at this
    simpa using this
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
    (sampleG_escape hg hne (q := 0) (natDegree_add_le_of_degree_le
      ((natDegree_C _).trans_le (by norm_num)) ((natDegree_C_mul_le _ _).trans (by simp)))
      (by simp))
  simp only [eval_add, eval_C, eval_mul, eval_X, eval_zero]
  have := hP _ hc.2
  linear_combination this

theorem sum_eq_mul_ite (ρ : List E2) {N : ℕ} (x : E2) :
    ∑ k ∈ range (2 ^ N), eqAtF ρ k * (if k = 0 then x else 0) = eqAtF ρ 0 * x := by
  rw [Finset.sum_eq_single 0 (fun k _ hk ↦ by rw [if_neg hk, mul_zero])
    (fun h0 ↦ absurd (Finset.mem_range.2 (Nat.two_pow_pos N)) h0), if_pos rfl]

theorem midAgree_cons {N : ℕ} {Q : Stack} {u : E2} {ρ : List E2} (hρ : ρ.length = N) {l : ℕ}
    (hl : l < 25) (hm : midAgreeV (N + 1) (Itree (N + 1) Q) (u :: ρ)) :
    (1 + u) * ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabG (N + 1) Q l 0 k +
      u * ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabG (N + 1) Q l 1 k = 0 := by
  have := hm l hl
  have hA : ∀ x, laneWord (segStateS Shape.v1 (Itree (N + 1) Q) 0 12 x) l =
      laneWord (roundsFrom 0 12 (inTree (N + 1) Q x)) l := fun x ↦ by simp [segStateS, Itree]
  rw [stepMle_cons u hρ, stepMle_cons u hρ] at this
  simp only [hA, laneWord_Itree_one _ _ _ hl] at this
  have hG0 : ∀ k, tabG (N + 1) Q l 0 k = kF (laneWord (roundsFrom 0 12 (inTree (N + 1) Q (2 * k))) l) +
      kF (Q (2 * k + 2 ^ (N + 1) * (8 + l))) := fun k ↦ by rw [tabG, Nat.zero_add]
  have hG1 : ∀ k, tabG (N + 1) Q l 1 k =
      kF (laneWord (roundsFrom 0 12 (inTree (N + 1) Q (2 * k + 1))) l) +
      kF (Q (2 * k + 1 + 2 ^ (N + 1) * (8 + l))) := fun k ↦ by rw [tabG, Nat.add_comm 1 (2 * k)]
  have s0 : ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabG (N + 1) Q l 0 k =
      ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (laneWord (roundsFrom 0 12 (inTree (N + 1) Q (2 * k))) l) +
      ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (2 * k + 2 ^ (N + 1) * (8 + l))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hG0, mul_add]
  have s1 : ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabG (N + 1) Q l 1 k =
      ∑ k ∈ range (2 ^ N), eqAtF ρ k *
        kF (laneWord (roundsFrom 0 12 (inTree (N + 1) Q (2 * k + 1))) l) +
      ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (2 * k + 1 + 2 ^ (N + 1) * (8 + l))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hG1, mul_add]
  rw [s0, s1]
  set B0 := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (2 * k + 2 ^ (N + 1) * (8 + l)))
  set B1 := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (2 * k + 1 + 2 ^ (N + 1) * (8 + l)))
  have h2 : (2 : E2) = 0 := CharTwo.two_eq_zero
  linear_combination this + (u * B0 + u * B1 + B0) * h2


theorem oLow_getD (u : E2) (dd : List E2) {m : ℕ} (hm : m < 4) :
    (oLow u dd).getD m 0 = (1 + u) * dd.getD m 0 + u * dd.getD (4 + m) 0 := by
  simp [oLow, List.getD_eq_getElem?_getD, hm]

/-- **The draw `u`** escapes at `errG g 1` from a candidate not alive after `ρ`. -/
theorem aliveU_escape {N g : ℕ} (hg : g ≤ 64) (stk : β → Stack) (h : Digest) (R : β → Prop)
    (δ : List K) {ρ : List E2} (hρ : ρ.length = N) (dd : List E2) (q : β)
    (hq : ¬ AliveR (N + 1) stk h R δ ρ q) :
    avgE (fun c ↦ indE (powOK g c ∧ AliveU (N + 1) stk h R δ ρ dd (e2OfE c) q)) ≤ errG g 1 := by
  have zero_bound : ∀ (P : E → Prop), (∀ c, ¬ P c) → avgE (fun c ↦ indE (P c)) ≤ errG g 1 :=
    fun P hP ↦ (avgE_le_of_le fun c ↦ (indE_of_not (hP c)).le).trans zero_le
  have h2 : (2 : E2) = 0 := CharTwo.two_eq_zero
  by_cases hW : WireOk (N + 1) (stk q) δ ρ dd ∧ RootOk (N + 1) (stk q) h ∧ R q
  swap
  · exact zero_bound _ fun c hc ↦ hW ⟨hc.2.1, hc.2.2.1, hc.2.2.2.2.2⟩
  obtain ⟨⟨hWL, hWR⟩, hroot, hR⟩ := hW
  have hN : N + 1 - 1 = N := by omega
  have : ¬ ∀ t ∈ wTabs (N + 1) (stk q) δ, ZeroOnF t ρ N := fun hz ↦
    hq ⟨by rw [hρ]; omega, by rwa [hN], hroot, hR⟩
  push_neg at this
  obtain ⟨t, ht, hnz⟩ := this
  rw [zeroOnF_full _ hρ] at hnz
  set Q := stk q
  rcases mem_wTabs ht with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨l, hl, b, hb, rfl⟩
  · -- (W) left
    set S := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (k + 2 ^ (N + 1) * m))
    set D0 := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (outW (N + 1) Q (2 * k) m)
    set D1 := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (outW (N + 1) Q (2 * k + 1) m)
    have hsum : ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabL (N + 1) Q δ m k =
        S + D0 + eqAtF ρ 0 * kF (δ.getD m 0) := by
      simp only [tabL, mul_add, Finset.sum_add_distrib, sum_eq_mul_ite, S, D0]
    have hS : S = dd.getD m 0 + eqAtF ρ 0 * kF (δ.getD m 0) := by
      rw [← hWL m hm, stepMle_rowpt Q hρ (by omega)]
    refine affine_escape hg (a := dd.getD m 0 + D0) (b := dd.getD (4 + m) 0 + D1)
      (fun hab ↦ hnz (by rw [hsum, hS]; linear_combination hab.1 + eqAtF ρ 0 * kF (δ.getD m 0) * h2))
      (fun u ↦ AliveU (N + 1) stk h R δ ρ dd u q) fun u hu ↦ ?_
    have := hu.2.2.1 m hm
    rw [stepMle_cons u hρ, oLow_getD u dd hm] at this
    linear_combination this + ((1 + u) * dd.getD m 0 + u * dd.getD (4 + m) 0) * h2
  · -- (W) right
    set S := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (Q (k + 2 ^ (N + 1) * (4 + m)))
    set D0 := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (outW (N + 1) Q (2 * k) m)
    set D1 := ∑ k ∈ range (2 ^ N), eqAtF ρ k * kF (outW (N + 1) Q (2 * k + 1) m)
    have hsum : ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabR (N + 1) Q m k = S + D1 := by
      simp only [tabR, mul_add, Finset.sum_add_distrib, S, D1]
    have hS : S = dd.getD (4 + m) 0 := by
      rw [← hWR m hm, stepMle_rowpt Q hρ (by omega)]
    refine affine_escape hg (a := dd.getD m 0 + D0) (b := dd.getD (4 + m) 0 + D1)
      (fun hab ↦ hnz (by rw [hsum, hS]; exact hab.2))
      (fun u ↦ AliveU (N + 1) stk h R δ ρ dd u q) fun u hu ↦ ?_
    have := hu.2.2.1 m hm
    rw [stepMle_cons u hρ, oLow_getD u dd hm] at this
    linear_combination this + ((1 + u) * dd.getD m 0 + u * dd.getD (4 + m) 0) * h2
  · -- (G)
    refine affine_escape hg (a := ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabG (N + 1) Q l 0 k)
      (b := ∑ k ∈ range (2 ^ N), eqAtF ρ k * tabG (N + 1) Q l 1 k)
      (fun hab ↦ hnz (by interval_cases b; exacts [hab.1, hab.2]))
      (fun u ↦ AliveU (N + 1) stk h R δ ρ dd u q)
      fun u hu ↦ midAgree_cons hρ hl hu.2.2.2.1

end Lvm6.K
