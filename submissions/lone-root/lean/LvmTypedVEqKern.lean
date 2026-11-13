-- New for lvm2 (roll 8 = B1, wave L, L-C): the two automata of V_S's relayout kernel (`LvmTypedV.divKern`,
-- `geKern`) are their brute-force sums (B-DES §1.4).
import LvmTypedV

/-!
# The relayout's automata

* **`divKern_eq`**: the long-division automaton over the 19 position bits (high to low, the remainder by 17 as
  state, one quotient bit per step) is `Σ_{i < 17·2^14} eq(ρ, i)·eq(r_lo, i / 17)·eq(r_hi, i mod 17)`, at
  `S_flat`'s one region (`dst = 0`, `log = 19`, `TNat.okB`).
* **`geKern_eq`**: the two-state comparator is `Σ_{c ≤ i < 2^l} eq(ρ, i)·eq(r, i)`.

Both are native (`FE`, `eqAtF`); `LvmTypedVEqForms` transfers them to the specification's `relayKern`.
-/

set_option autoImplicit false

namespace Lvm.TypedV

open Lvm

theorem kern_toArray_getD (ρ : List FE) (k : Nat) : ρ.toArray.getD k 0 = ρ.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem kern_foldl_range (n : Nat) (h : Nat → FE) (a : FE) :
    (List.range n).foldl (fun acc x => acc + h x) a = a + ∑ i ∈ Finset.range n, h i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [Finset.sum_range_succ, add_assoc]

theorem kern_foldl_filter (L : List Nat) (p : Nat → Bool) (h : Nat → FE) (a : FE) :
    (L.filter p).foldl (fun acc x => acc + h x) a = L.foldl (fun acc x => acc + if p x then h x else 0) a := by
  induction L generalizing a with
  | nil => rfl
  | cons x L ih => by_cases hx : p x <;> simp [hx, ih]

theorem kern_sumE_filter (n : Nat) (p : Nat → Bool) (f : Nat → FE) :
    sumE (((List.range n).filter p).map f) = ∑ i ∈ Finset.range n, if p i then f i else 0 := by
  rw [sumE, List.foldl_map, kern_foldl_filter, kern_foldl_range, zero_add]

theorem kern_sumE_range (n : Nat) (f : Nat → FE) :
    sumE ((List.range n).map f) = ∑ i ∈ Finset.range n, f i := by
  rw [sumE, List.foldl_map, kern_foldl_range, zero_add]

/-- `Σ_{s < 2m} F s` by pairs `2t, 2t + 1`. -/
theorem kern_sum_pairs (m : Nat) (F : Nat → FE) :
    ∑ s ∈ Finset.range (2 * m), F s = ∑ t ∈ Finset.range m, (F (2 * t) + F (2 * t + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem kern_eqAtF_cons (a : FE) (ρ : List FE) (w : Nat) :
    eqAtF (a :: ρ) w = (if w % 2 = 1 then a else 1 + a) * eqAtF ρ (w / 2) := rfl

theorem kern_eq1_t (a : FE) : eq1 a true = a := rfl
theorem kern_eq1_f (a : FE) : eq1 a false = 1 + a := rfl

/-! ## The comparator -/

/-- `geKern`'s step. -/
def kern_gt (c : Nat) (ρ r : List FE) (st : FE × FE) (k : Nat) : FE × FE :=
  let ρa := ρ.toArray
  let ra := r.toArray
  let t (k : Nat) (b : Bool) : FE := eq1 (ρa.getD k 0) b * eq1 (ra.getD k 0) b
  let full := t k false + t k true
  if c.testBit k then (st.1 * t k true, st.2 * full) else (st.1 * t k false, st.2 * full + st.1 * t k true)

theorem kern_geKern_unfold (c l : Nat) (ρ r : List FE) :
    geKern c l ρ r = ((List.range l).reverse.foldl (kern_gt c ρ r) (1, 0)).1 +
      ((List.range l).reverse.foldl (kern_gt c ρ r) (1, 0)).2 := rfl

theorem kern_gt_succ (c : Nat) (a b : FE) (ρ r : List FE) :
    (fun k st => kern_gt c (a :: ρ) (b :: r) st (k + 1)) = fun k st => kern_gt (c / 2) ρ r st k := by
  funext k st
  simp only [kern_gt, kern_toArray_getD, List.getD_cons_succ, Nat.testBit_succ]

/-- The comparator's states after the bits of `[0, n)` (high to low): equal so far, above. -/
theorem kern_ge_inv (n : Nat) : ∀ (c : Nat) (ρ r : List FE), ρ.length = n → r.length = n → c < 2 ^ n →
    (List.range n).foldr (fun k st => kern_gt c ρ r st k) (1, 0) =
      (eqAtF ρ c * eqAtF r c, ∑ i ∈ Finset.range (2 ^ n), if c < i then eqAtF ρ i * eqAtF r i else 0) := by
  induction n with
  | zero =>
    intro c ρ r hρ hr hc
    rw [List.length_eq_zero_iff] at hρ hr
    subst hρ hr
    obtain rfl : c = 0 := by omega
    rw [pow_zero, Finset.sum_range_one]
    simp [eqAtF]
  | succ n ih =>
    intro c ρ r hρ hr hc
    obtain ⟨a, ρ, rfl⟩ := List.exists_cons_of_length_eq_add_one hρ
    obtain ⟨b, r, rfl⟩ := List.exists_cons_of_length_eq_add_one hr
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hρ hr
    have hc2 : c / 2 < 2 ^ n := by rw [pow_succ] at hc; omega
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [Nat.succ_eq_add_one]
    rw [kern_gt_succ, ih (c / 2) ρ r hρ hr hc2, pow_succ, mul_comm _ 2, kern_sum_pairs]
    simp only [kern_gt, kern_toArray_getD, List.getD_cons_zero, Nat.testBit_zero, kern_eqAtF_cons]
    have e1 : ∀ t : Nat, (2 * t) % 2 = 0 := fun t => by omega
    have e2 : ∀ t : Nat, (2 * t) / 2 = t := fun t => by omega
    have e3 : ∀ t : Nat, (2 * t + 1) % 2 = 1 := fun t => by omega
    have e4 : ∀ t : Nat, (2 * t + 1) / 2 = t := fun t => by omega
    simp only [e1, e2, e3, e4, kern_eq1_t, kern_eq1_f, ite_true, Nat.zero_ne_one, ite_false]
    rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
    · simp only [hc0, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
      refine Prod.ext (by simp only; ring) ?_
      simp only
      symm
      rw [Finset.sum_congr rfl (g := fun t => (if c / 2 < t then eqAtF ρ t * eqAtF r t else 0) *
          ((1 + a) * (1 + b) + a * b) + if c / 2 = t then eqAtF ρ t * eqAtF r t * (a * b) else 0)]
      · rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq]
        simp only [Finset.mem_range.2 hc2, ite_true]
      · intro t _
        rcases lt_trichotomy (c / 2) t with h | h | h
        · have h1 : c < 2 * t := by omega
          have h2 : c < 2 * t + 1 := by omega
          have h3 : c / 2 ≠ t := by omega
          simp only [h, h1, h2, h3, ite_true, ite_false]; ring
        · have h1 : ¬ c < 2 * t := by omega
          have h2 : c < 2 * t + 1 := by omega
          simp only [h, h1, h2, lt_self_iff_false, ite_true, ite_false]; ring
        · have h1 : ¬ c < 2 * t := by omega
          have h2 : ¬ c < 2 * t + 1 := by omega
          have h3 : ¬ c / 2 < t := by omega
          have h4 : c / 2 ≠ t := by omega
          simp only [h1, h2, h3, h4, ite_false]; ring
    · simp only [hc1, decide_true, ite_true]
      refine Prod.ext (by simp only; ring) ?_
      simp only
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : c / 2 < t
      · have h1 : c < 2 * t := by omega
        have h2 : c < 2 * t + 1 := by omega
        simp only [h, h1, h2, ite_true]; ring
      · have h1 : ¬ c < 2 * t := by omega
        have h2 : ¬ c < 2 * t + 1 := by omega
        simp only [h, h1, h2, ite_false]; ring

/-! ## The long-division automaton -/

/-- `2·rem + b`. -/
def kern_t (rem : Nat) (b : Bool) : Nat := 2 * rem + (if b then 1 else 0)

/-- The new remainder. -/
def kern_idx (rem : Nat) (b : Bool) : Nat :=
  if decide (sLanes ≤ kern_t rem b) then kern_t rem b - sLanes else kern_t rem b

/-- The step's factor at `(rem, b)`. -/
def kern_f (F : Bool → Bool → FE) (rem : Nat) (b : Bool) : FE :=
  let q := decide (sLanes ≤ kern_t rem b)
  if b then (if q then F true true else F true false) else (if q then F false true else F false false)

/-- `divKern`'s step at a free bit, with the bit factors `F b q`. -/
def kern_dstep (F : Bool → Bool → FE) (V : Array FE) : Array FE :=
  (List.range sLanes).foldl (fun W rem =>
    [false, true].foldl (fun W b => W.modify (kern_idx rem b) (· + V.getD rem 0 * kern_f F rem b)) W)
    (Array.replicate sLanes 0)

/-- The factors at bit `k`. -/
def kern_fac (ρ rlo : List FE) (k : Nat) (b q : Bool) : FE :=
  eq1 (ρ.toArray.getD k 0) b * (if k < recRowBits then eq1 (rlo.toArray.getD k 0) q else if q then 0 else 1)

/-- The initial state. -/
def kern_init : Array FE := (Array.replicate sLanes (0 : FE)).set! 0 1

theorem kern_divKern_unfold (ρ rlo rhi : List FE) :
    divKern 0 posBits ρ rlo rhi = (List.range sLanes).foldl (fun acc rem => acc +
      ((List.range posBits).reverse.foldl (fun V k => kern_dstep (kern_fac ρ rlo k) V) kern_init).getD rem 0 *
        eqAtF rhi rem) 0 := by
  unfold divKern
  dsimp only
  refine List.foldl_ext _ _ _ fun acc rem _ => ?_
  refine congrArg (acc + ·) (congrArg (· * eqAtF rhi rem) (congrArg (Array.getD · rem 0) ?_))
  apply List.foldl_ext
  intro V k hk
  have hk' : k < posBits := by simpa using hk
  simp only [hk', decide_true, ite_true]
  rfl

theorem kern_getD_modify (W : Array FE) (j i : Nat) (v : FE) (hj : j < W.size) :
    (W.modify j (· + v)).getD i 0 = W.getD i 0 + if j = i then v else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split_ifs with h
  · subst h; simp [Array.getElem?_eq_getElem hj]
  · simp

/-- An array fold that adds `c x i` at each `i`. -/
theorem kern_fold_add {α : Type} (L : List α) (G : Array FE → α → Array FE) (c : α → Nat → FE)
    (hG : ∀ W x, x ∈ L → W.size = 17 → (G W x).size = 17 ∧ ∀ i, (G W x).getD i 0 = W.getD i 0 + c x i) :
    ∀ W : Array FE, W.size = 17 →
      (L.foldl G W).size = 17 ∧ ∀ i, (L.foldl G W).getD i 0 = W.getD i 0 + (L.map (c · i)).sum := by
  induction L with
  | nil => intro W hW; simp [hW]
  | cons x L ih =>
    intro W hW
    obtain ⟨h1, h2⟩ := hG W x List.mem_cons_self hW
    obtain ⟨h3, h4⟩ := ih (fun W y hy => hG W y (List.mem_cons_of_mem _ hy)) (G W x) h1
    refine ⟨h3, fun i => ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons, add_assoc]

theorem kern_idx_lt {rem : Nat} (h : rem < 17) (b : Bool) : kern_idx rem b < 17 := by
  unfold kern_idx kern_t
  rw [show sLanes = 17 from rfl]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero, decide_eq_true_eq] <;>
    split_ifs <;> omega

theorem kern_list_sum_range (n : Nat) (f : Nat → FE) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **The step** on the remainders. -/
theorem kern_dstep_getD (F : Bool → Bool → FE) (V : Array FE) (i : Nat) :
    (kern_dstep F V).getD i 0 = ∑ rem ∈ Finset.range 17,
      ((if kern_idx rem false = i then V.getD rem 0 * kern_f F rem false else 0) +
        (if kern_idx rem true = i then V.getD rem 0 * kern_f F rem true else 0)) := by
  have hin := fun (rem : Nat) (hrem : rem < 17) => kern_fold_add [false, true]
    (fun W b => W.modify (kern_idx rem b) (· + V.getD rem 0 * kern_f F rem b))
    (fun b i => if kern_idx rem b = i then V.getD rem 0 * kern_f F rem b else 0)
    (fun W b _ hW => ⟨by simp [hW], fun i => kern_getD_modify W _ i _ (hW ▸ kern_idx_lt hrem b)⟩)
  obtain ⟨_, h⟩ := kern_fold_add (List.range sLanes) _ _
    (fun W rem hrem hW => hin rem (List.mem_range.1 hrem) W hW) (Array.replicate sLanes 0)
    (by rw [Array.size_replicate]; rfl)
  rw [kern_dstep, h i, kern_list_sum_range]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  split_ifs <;> simp [sLanes, recStreamCols]

theorem kern_init_getD (i : Nat) : kern_init.getD i 0 = if 0 = i then 1 else 0 := by
  unfold kern_init
  rw [show sLanes = 17 from rfl]
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_replicate,
    Array.size_replicate]
  split_ifs <;> first | rfl | omega

/-- `Π_{m < n} fac m (bit_m t) (bit_m Q)`. -/
def kern_P (fac : Nat → Bool → Bool → FE) : Nat → Nat → Nat → FE
  | 0, _, _ => 1
  | n + 1, t, Q => fac 0 (decide (t % 2 = 1)) (decide (Q % 2 = 1)) * kern_P (fun m => fac (m + 1)) n (t / 2) (Q / 2)

theorem kern_P_succ (fac : Nat → Bool → Bool → FE) (n t Q : Nat) :
    kern_P fac (n + 1) t Q =
      fac 0 (decide (t % 2 = 1)) (decide (Q % 2 = 1)) * kern_P (fun m => fac (m + 1)) n (t / 2) (Q / 2) := rfl

/-- The automaton's state after `n` bits: `V[R] = Σ_{t < 2^n, t mod 17 = R} Π_m fac m (bit_m t) (bit_m (t / 17))`. -/
def kern_C (fac : Nat → Bool → Bool → FE) (n R : Nat) : FE :=
  ∑ t ∈ Finset.range (2 ^ n), if t % 17 = R then kern_P fac n t (t / 17) else 0

theorem kern_idx_false (t : Nat) : kern_idx (t % 17) false = (2 * t) % 17 := by
  unfold kern_idx kern_t
  rw [show sLanes = 17 from rfl]
  simp only [Bool.false_eq_true, ite_false, add_zero, decide_eq_true_eq]
  split_ifs <;> omega

theorem kern_idx_true (t : Nat) : kern_idx (t % 17) true = (2 * t + 1) % 17 := by
  unfold kern_idx kern_t
  rw [show sLanes = 17 from rfl]
  simp only [ite_true, decide_eq_true_eq]
  split_ifs <;> omega

theorem kern_f_false (F : Bool → Bool → FE) (t : Nat) :
    kern_f F (t % 17) false = F false (decide ((2 * t) / 17 % 2 = 1)) := by
  unfold kern_f kern_t
  rw [show sLanes = 17 from rfl]
  simp only [Bool.false_eq_true, ite_false, add_zero]
  by_cases h : 17 ≤ 2 * (t % 17)
  · have h' : (2 * t) / 17 % 2 = 1 := by omega
    simp only [h, h', decide_true, ite_true]
  · have h' : ¬ (2 * t) / 17 % 2 = 1 := by omega
    simp only [h, h', decide_false, Bool.false_eq_true, ite_false]

theorem kern_f_true (F : Bool → Bool → FE) (t : Nat) :
    kern_f F (t % 17) true = F true (decide ((2 * t + 1) / 17 % 2 = 1)) := by
  unfold kern_f kern_t
  rw [show sLanes = 17 from rfl]
  simp only [ite_true]
  by_cases h : 17 ≤ 2 * (t % 17) + 1
  · have h' : (2 * t + 1) / 17 % 2 = 1 := by omega
    simp only [h, h', decide_true, ite_true]
  · have h' : ¬ (2 * t + 1) / 17 % 2 = 1 := by omega
    simp only [h, h', decide_false, Bool.false_eq_true, ite_false]

/-- **One step of the invariant**: the step maps the state after the bits above to the state after this one. -/
theorem kern_step_closed (fac : Nat → Bool → Bool → FE) (n i : Nat) :
    ∑ rem ∈ Finset.range 17,
      ((if kern_idx rem false = i then kern_C (fun m => fac (m + 1)) n rem * kern_f (fac 0) rem false else 0) +
        (if kern_idx rem true = i then kern_C (fun m => fac (m + 1)) n rem * kern_f (fac 0) rem true else 0)) =
      kern_C fac (n + 1) i := by
  have e : ∀ (rem : Nat) (p : Prop) [Decidable p] (x : FE),
      (if p then kern_C (fun m => fac (m + 1)) n rem * x else 0) = ∑ t ∈ Finset.range (2 ^ n),
        if t % 17 = rem then (if p then kern_P (fun m => fac (m + 1)) n t (t / 17) * x else 0) else 0 := by
    intro rem p _ x
    unfold kern_C
    split_ifs with hp
    · rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun t _ => ?_; split_ifs <;> simp
    · simp
  have h17 : ∀ t : Nat, t % 17 < 17 := fun t => Nat.mod_lt t (by norm_num)
  simp only [e, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have e2 : ∀ t rem : Nat, ((if t % 17 = rem then (if kern_idx rem false = i then
      kern_P (fun m => fac (m + 1)) n t (t / 17) * kern_f (fac 0) rem false else 0) else 0) +
      (if t % 17 = rem then (if kern_idx rem true = i then
      kern_P (fun m => fac (m + 1)) n t (t / 17) * kern_f (fac 0) rem true else 0) else 0)) =
      if t % 17 = rem then ((if kern_idx (t % 17) false = i then
      kern_P (fun m => fac (m + 1)) n t (t / 17) * kern_f (fac 0) (t % 17) false else 0) +
      (if kern_idx (t % 17) true = i then
      kern_P (fun m => fac (m + 1)) n t (t / 17) * kern_f (fac 0) (t % 17) true else 0)) else 0 := by
    intro t rem
    by_cases ht : t % 17 = rem
    · subst ht; simp only [ite_true]
    · simp only [ht, ite_false, add_zero]
  simp only [e2, Finset.sum_ite_eq, Finset.mem_range, h17, ite_true]
  unfold kern_C
  rw [pow_succ, mul_comm _ 2, kern_sum_pairs]
  refine Finset.sum_congr rfl fun t _ => ?_
  have a1 : (2 * t) % 2 = 0 := by omega
  have a2 : (2 * t) / 2 = t := by omega
  have a3 : (2 * t + 1) % 2 = 1 := by omega
  have a4 : (2 * t + 1) / 2 = t := by omega
  have a5 : (2 * t) / 17 / 2 = t / 17 := by omega
  have a6 : (2 * t + 1) / 17 / 2 = t / 17 := by omega
  rw [kern_idx_false, kern_idx_true, kern_f_false, kern_f_true, kern_P_succ, kern_P_succ]
  simp only [a1, a2, a3, a4, a5, a6, Nat.zero_ne_one, decide_false, decide_true]
  split_ifs <;> ring

/-- **The invariant**: the automaton after the bits `n − 1, …, 0` (high to low) is `kern_C`. -/
theorem kern_fold_closed (n : Nat) : ∀ (fac : Nat → Bool → Bool → FE) (i : Nat),
    ((List.range n).foldr (fun k V => kern_dstep (fac k) V) kern_init).getD i 0 = kern_C fac n i := by
  induction n with
  | zero =>
    intro fac i
    rw [List.range_zero, List.foldr_nil, kern_init_getD]
    unfold kern_C
    rw [pow_zero, Finset.sum_range_one]
    simp [kern_P]
  | succ n ih =>
    intro fac i
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, kern_dstep_getD]
    simp only [ih]
    exact kern_step_closed fac n i

theorem kern_divKern_closed (ρ rlo rhi : List FE) :
    divKern 0 posBits ρ rlo rhi = ∑ rem ∈ Finset.range 17, kern_C (kern_fac ρ rlo) 19 rem * eqAtF rhi rem := by
  rw [kern_divKern_unfold, List.foldl_reverse, kern_foldl_range, zero_add]
  simp only [kern_fold_closed]
  rfl

/-! ## The factors: `eq(ρ, i)`, `eq(r_lo, i / 17)` and `i / 17 < 2^14` -/

/-- `Π_{m < n} u m (bit_m t)`. -/
def kern_U (u : Nat → Bool → FE) : Nat → Nat → FE
  | 0, _ => 1
  | n + 1, t => u 0 (decide (t % 2 = 1)) * kern_U (fun m => u (m + 1)) n (t / 2)

theorem kern_P_mul (n : Nat) : ∀ (u w : Nat → Bool → FE) (t Q : Nat),
    kern_P (fun m b q => u m b * w m q) n t Q = kern_U u n t * kern_U w n Q := by
  induction n with
  | zero => intros; simp [kern_P, kern_U]
  | succ n ih => intro u w t Q; simp only [kern_P_succ, kern_U, ih]; ring

theorem kern_U_eqAtF (ρ : List FE) : ∀ t : Nat, kern_U (fun m b => eq1 (ρ.getD m 0) b) ρ.length t = eqAtF ρ t := by
  induction ρ with
  | nil => intro t; rfl
  | cons a ρ ih =>
    intro t
    simp only [List.length_cons, kern_U, List.getD_cons_succ, List.getD_cons_zero, ih, kern_eqAtF_cons]
    simp only [eq1, decide_eq_true_eq]

theorem kern_U_congr (n : Nat) : ∀ (u u' : Nat → Bool → FE) (t : Nat), (∀ m < n, u m = u' m) →
    kern_U u n t = kern_U u' n t := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro u u' t h
    simp only [kern_U, h 0 (by omega), ih (fun m => u (m + 1)) (fun m => u' (m + 1)) (t / 2)
      (fun m hm => h (m + 1) (by omega))]

theorem kern_U_split (a : Nat) : ∀ (u : Nat → Bool → FE) (b Q : Nat),
    kern_U u (a + b) Q = kern_U u a Q * kern_U (fun m => u (m + a)) b (Q / 2 ^ a) := by
  induction a with
  | zero => intros; simp [kern_U]
  | succ a ih =>
    intro u b Q
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [kern_U, ih, Nat.div_div_eq_div_mul, ← pow_succ']
    have hl : (fun m => u (m + a + 1)) = fun m => u (m + (a + 1)) := funext fun m => by rw [Nat.add_assoc]
    rw [hl, mul_assoc]

theorem kern_U_zero (n : Nat) : kern_U (fun _ q => if q then 0 else 1) n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [kern_U]; simpa using ih

theorem kern_U_lo (rlo : List FE) (hlo : rlo.length = recRowBits) (Q : Nat) (hQ : Q < 2 ^ 15) :
    kern_U (fun m q => if m < recRowBits then eq1 (rlo.toArray.getD m 0) q else if q then 0 else 1) 19 Q =
      eqAtF rlo Q * (if Q < 2 ^ 14 then 1 else 0) := by
  rw [show 19 = 14 + 5 from rfl, kern_U_split,
    kern_U_congr 14 _ (fun m b => eq1 (rlo.getD m 0) b) Q (fun m hm => funext fun q => by
      simp only [show m < recRowBits from hm, ite_true, kern_toArray_getD]),
    kern_U_congr 5 _ (fun _ q => if q then 0 else 1) _ (fun m _ => funext fun q => by
      simp only [show ¬ (m + 14 < recRowBits) by simp [recRowBits], ite_false])]
  have h := kern_U_eqAtF rlo Q
  rw [hlo] at h
  rw [h]
  rcases (show Q / 2 ^ 14 = 0 ∨ Q / 2 ^ 14 = 1 by omega) with h1 | h1
  · rw [h1, kern_U_zero]
    simp only [show Q < 2 ^ 14 by omega, ite_true]
  · have h2 : ¬ Q < 2 ^ 14 := by omega
    rw [h1]
    simp only [h2, ite_false]
    simp [kern_U]

/-! ## The two lemmas -/

/-- **The long-division automaton is its sum** (at `S_flat`'s region: positions from `0`, all `19` bits
free). -/
theorem divKern_eq (ρ rlo rhi : List FE) (hρ : ρ.length = posBits) (hlo : rlo.length = recRowBits) :
    divKern 0 posBits ρ rlo rhi =
      sumE ((List.range sPos).map fun i => eqAtF ρ i * eqAtF rlo (i / sLanes) * eqAtF rhi (i % sLanes)) := by
  have h17 : ∀ t : Nat, t % 17 < 17 := fun t => Nat.mod_lt t (by norm_num)
  have hP : ∀ t, t < 2 ^ 19 →
      kern_P (kern_fac ρ rlo) 19 t (t / 17) = eqAtF ρ t * (eqAtF rlo (t / 17) * if t < sPos then 1 else 0) := by
    intro t ht
    have hu := kern_U_eqAtF ρ t
    rw [hρ] at hu
    rw [show kern_fac ρ rlo = fun m b q => (fun m b => eq1 (ρ.toArray.getD m 0) b) m b *
        (fun m q => if m < recRowBits then eq1 (rlo.toArray.getD m 0) q else if q then 0 else 1) m q from rfl,
      kern_P_mul, kern_U_lo rlo hlo _ (by omega)]
    simp only [kern_toArray_getD]
    rw [hu]
    simp only [show (t / 17 < 2 ^ 14 ↔ t < sPos) by rw [show sPos = 17 * 2 ^ 14 from rfl]; omega]
  rw [kern_divKern_closed, kern_sumE_range]
  unfold kern_C
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range, h17, ite_true]
  rw [show (2 : Nat) ^ 19 = sPos + 245760 from rfl, Finset.sum_range_add]
  have hs : sPos = 17 * 2 ^ 14 := rfl
  have h2 : ∀ x ∈ Finset.range 245760,
      kern_P (kern_fac ρ rlo) 19 (sPos + x) ((sPos + x) / 17) * eqAtF rhi ((sPos + x) % 17) = 0 := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [hP _ (by omega)]
    simp
  rw [Finset.sum_eq_zero h2, add_zero]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [hP t (ht.trans (by rw [hs]; norm_num))]
  simp only [ht, ite_true, mul_one, show sLanes = 17 from rfl]

/-- **The comparator is its sum**: `Σ_{i < 2^l, c ≤ i} eq(ρ, i)·eq(r, i)`. -/
theorem geKern_eq (c l : Nat) (ρ r : List FE) (hρ : ρ.length = l) (hr : r.length = l) (hc : c < 2 ^ l) :
    geKern c l ρ r =
      sumE (((List.range (2 ^ l)).filter fun i => decide (c ≤ i)).map fun i => eqAtF ρ i * eqAtF r i) := by
  rw [kern_geKern_unfold, List.foldl_reverse, kern_ge_inv l c ρ r hρ hr hc, kern_sumE_filter]
  simp only
  symm
  rw [Finset.sum_congr rfl (g := fun i => (if c < i then eqAtF ρ i * eqAtF r i else 0) +
      if c = i then eqAtF ρ i * eqAtF r i else 0), Finset.sum_add_distrib, Finset.sum_ite_eq]
  · simp only [Finset.mem_range.2 hc, ite_true]; ring
  · intro i _
    rcases lt_trichotomy c i with h | h | h
    · simp only [h, h.le, h.ne, decide_true, ite_true, ite_false]; ring
    · subst h; simp
    · have h1 : ¬ c ≤ i := by omega
      have h2 : c ≠ i := by omega
      have h3 : ¬ c < i := by omega
      simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ite_false]; ring

end Lvm.TypedV
