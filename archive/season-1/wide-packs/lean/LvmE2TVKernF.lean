-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): V_S's typed kernels at `E2` (`LvmE2TV`: `virtD`, `relayKernD`) are the
-- specification's region sums (`LvmE2TProg`: `virtT`, `relayKernT`) on `N.inst Q lay`, through `FE2.toE2`
-- (roll 11's `LvmTypedVEqForms.virtEF_rel`, `relayKernF_rel` at S2GT).
import LvmE2TV
import LvmTypedVEqForms
import LvmE2VGkrBase
import LvmE2VWireAlg
import LvmE2VTwins
import LvmE2TVKern

-- ===== merged from `LvmE2TVKernP` (VQ module merge: `LvmE2TVKernP.lean` removed) =====
section
-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): the relayout's automata over any field (roll 11's
-- `LvmTypedVEqKern`, generic): `divKernG`, `geKernG` are their brute-force sums.

/-!
# The relayout's automata over a field

Roll 11's `LvmTypedVEqKern` over a field `F` (`LvmE2TVKern`'s `divKernG`, `geKernG`, `E2V.eqAtF`):

* **`divKernG_eq`**: the long-division automaton over the 19 position bits is
  `Σ_{i < 17·2^14} eq(ρ, i)·eq(r_lo, i / 17)·eq(r_hi, i mod 17)` (`S_flat`'s one region: `dst = 0`, `log = 19`);
* **`geKernG_eq`**: the two-state comparator is `Σ_{c ≤ i < 2^l} eq(ρ, i)·eq(r, i)`.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm Lvm.TypedV

variable {F : Type} [Field F]

theorem kg_toArray_getD (ρ : List F) (k : Nat) : ρ.toArray.getD k 0 = ρ.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem kg_foldl_range (n : Nat) (h : Nat → F) (a : F) :
    (List.range n).foldl (fun acc x => acc + h x) a = a + ∑ i ∈ Finset.range n, h i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [Finset.sum_range_succ, add_assoc]

theorem kg_foldl_filter (L : List Nat) (p : Nat → Bool) (h : Nat → F) (a : F) :
    (L.filter p).foldl (fun acc x => acc + h x) a = L.foldl (fun acc x => acc + if p x then h x else 0) a := by
  induction L generalizing a with
  | nil => rfl
  | cons x L ih => by_cases hx : p x <;> simp [hx, ih]

theorem kg_sumE_filter (n : Nat) (p : Nat → Bool) (f : Nat → F) :
    E2V.sumF (((List.range n).filter p).map f) = ∑ i ∈ Finset.range n, if p i then f i else 0 := by
  rw [E2V.sumF, List.foldl_map, kg_foldl_filter, kg_foldl_range, zero_add]

theorem kg_sumE_range (n : Nat) (f : Nat → F) :
    E2V.sumF ((List.range n).map f) = ∑ i ∈ Finset.range n, f i := by
  rw [E2V.sumF, List.foldl_map, kg_foldl_range, zero_add]

/-- `Σ_{s < 2m} Fb s` by pairs `2t, 2t + 1`. -/
theorem kg_sum_pairs (m : Nat) (Fb : Nat → F) :
    ∑ s ∈ Finset.range (2 * m), Fb s = ∑ t ∈ Finset.range m, (Fb (2 * t) + Fb (2 * t + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem kg_eqAtF_cons (a : F) (ρ : List F) (w : Nat) :
    E2V.eqAtF (a :: ρ) w = (if w % 2 = 1 then a else 1 + a) * E2V.eqAtF ρ (w / 2) := rfl

theorem kg_eq1_t (a : F) : eq1G a true = a := rfl
theorem kg_eq1_f (a : F) : eq1G a false = 1 + a := rfl

/-! ## The comparator -/

/-- `geKernG`'s step. -/
def kg_gt (c : Nat) (ρ r : List F) (st : F × F) (k : Nat) : F × F :=
  let ρa := ρ.toArray
  let ra := r.toArray
  let t (k : Nat) (b : Bool) : F := eq1G (ρa.getD k 0) b * eq1G (ra.getD k 0) b
  let full := t k false + t k true
  if c.testBit k then (st.1 * t k true, st.2 * full) else (st.1 * t k false, st.2 * full + st.1 * t k true)

theorem kg_geKern_unfold (c l : Nat) (ρ r : List F) :
    geKernG c l ρ r = ((List.range l).reverse.foldl (kg_gt c ρ r) (1, 0)).1 +
      ((List.range l).reverse.foldl (kg_gt c ρ r) (1, 0)).2 := rfl

theorem kg_gt_succ (c : Nat) (a b : F) (ρ r : List F) :
    (fun k st => kg_gt c (a :: ρ) (b :: r) st (k + 1)) = fun k st => kg_gt (c / 2) ρ r st k := by
  funext k st
  simp only [kg_gt, kg_toArray_getD, List.getD_cons_succ, Nat.testBit_succ]

/-- The comparator's states after the bits of `[0, n)` (high to low): equal so far, above. -/
theorem kg_ge_inv (n : Nat) : ∀ (c : Nat) (ρ r : List F), ρ.length = n → r.length = n → c < 2 ^ n →
    (List.range n).foldr (fun k st => kg_gt c ρ r st k) (1, 0) =
      (E2V.eqAtF ρ c * E2V.eqAtF r c, ∑ i ∈ Finset.range (2 ^ n), if c < i then E2V.eqAtF ρ i * E2V.eqAtF r i else 0) := by
  induction n with
  | zero =>
    intro c ρ r hρ hr hc
    rw [List.length_eq_zero_iff] at hρ hr
    subst hρ hr
    obtain rfl : c = 0 := by (clear * - c hc; omega)
    rw [pow_zero, Finset.sum_range_one]
    simp [E2V.eqAtF]
  | succ n ih =>
    intro c ρ r hρ hr hc
    obtain ⟨a, ρ, rfl⟩ := List.exists_cons_of_length_eq_add_one hρ
    obtain ⟨b, r, rfl⟩ := List.exists_cons_of_length_eq_add_one hr
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hρ hr
    have hc2 : c / 2 < 2 ^ n := by rw [pow_succ] at hc; (clear * - c n F hc ρ r; omega)
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    simp only [Nat.succ_eq_add_one]
    rw [kg_gt_succ, ih (c / 2) ρ r hρ hr hc2, pow_succ, mul_comm _ 2, kg_sum_pairs]
    simp only [kg_gt, kg_toArray_getD, List.getD_cons_zero, Nat.testBit_zero, kg_eqAtF_cons]
    have e1 : ∀ t : Nat, (2 * t) % 2 = 0 := fun t => by (clear * - t F n c ρ r; omega)
    have e2 : ∀ t : Nat, (2 * t) / 2 = t := fun t => by (clear * - t F n c ρ r; omega)
    have e3 : ∀ t : Nat, (2 * t + 1) % 2 = 1 := fun t => by (clear * - t F n c ρ r; omega)
    have e4 : ∀ t : Nat, (2 * t + 1) / 2 = t := fun t => by (clear * - t F n c ρ r; omega)
    simp only [e1, e2, e3, e4, kg_eq1_t, kg_eq1_f, ite_true, Nat.zero_ne_one, ite_false]
    rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
    · simp only [hc0, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
      refine Prod.ext (by simp only; ring) ?_
      simp only
      symm
      rw [Finset.sum_congr rfl (g := fun t => (if c / 2 < t then E2V.eqAtF ρ t * E2V.eqAtF r t else 0) *
          ((1 + a) * (1 + b) + a * b) + if c / 2 = t then E2V.eqAtF ρ t * E2V.eqAtF r t * (a * b) else 0)]
      · rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq]
        simp only [Finset.mem_range.2 hc2, ite_true]
      · intro t _
        rcases lt_trichotomy (c / 2) t with h | h | h
        · have h1 : c < 2 * t := by (clear * - c t F n ρ r hc0 h; omega)
          have h2 : c < 2 * t + 1 := by (clear * - c t F n ρ r hc0 h; omega)
          have h3 : c / 2 ≠ t := by (clear * - c t F n ρ r h; omega)
          simp only [h, h1, h2, h3, ite_true, ite_false]; ring
        · have h1 : ¬ c < 2 * t := by (clear * - c t F n ρ r hc0 h; omega)
          have h2 : c < 2 * t + 1 := by (clear * - c t F n ρ r hc0 h; omega)
          simp only [h, h1, h2, lt_self_iff_false, ite_true, ite_false]; ring
        · have h1 : ¬ c < 2 * t := by (clear * - c t F n ρ r hc0 h; omega)
          have h2 : ¬ c < 2 * t + 1 := by (clear * - c t F n ρ r hc0 h; omega)
          have h3 : ¬ c / 2 < t := by (clear * - c t F n ρ r h; omega)
          have h4 : c / 2 ≠ t := by (clear * - c t F n ρ r h; omega)
          simp only [h1, h2, h3, h4, ite_false]; ring
    · simp only [hc1, decide_true, ite_true]
      refine Prod.ext (by simp only; ring) ?_
      simp only
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : c / 2 < t
      · have h1 : c < 2 * t := by (clear * - c t F n ρ r hc1 h; omega)
        have h2 : c < 2 * t + 1 := by (clear * - c t F n ρ r hc1 h; omega)
        simp only [h, h1, h2, ite_true]; ring
      · have h1 : ¬ c < 2 * t := by (clear * - c t F n ρ r hc1 h; omega)
        have h2 : ¬ c < 2 * t + 1 := by (clear * - c t F n ρ r hc1 h; omega)
        simp only [h, h1, h2, ite_false]; ring

/-! ## The long-division automaton -/

/-- `2·rem + b`. -/
def kg_t (rem : Nat) (b : Bool) : Nat := 2 * rem + (if b then 1 else 0)

/-- The new remainder. -/
def kg_idx (rem : Nat) (b : Bool) : Nat :=
  if decide (sLanes ≤ kg_t rem b) then kg_t rem b - sLanes else kg_t rem b

/-- The step's factor at `(rem, b)`. -/
def kg_f (Fb : Bool → Bool → F) (rem : Nat) (b : Bool) : F :=
  let q := decide (sLanes ≤ kg_t rem b)
  if b then (if q then Fb true true else Fb true false) else (if q then Fb false true else Fb false false)

/-- `divKernG`'s step at a free bit, with the bit factors `Fb b q`. -/
def kg_dstep (Fb : Bool → Bool → F) (V : Array F) : Array F :=
  (List.range sLanes).foldl (fun W rem =>
    [false, true].foldl (fun W b => W.modify (kg_idx rem b) (· + V.getD rem 0 * kg_f Fb rem b)) W)
    (Array.replicate sLanes 0)

/-- The factors at bit `k`. -/
def kg_fac (ρ rlo : List F) (k : Nat) (b q : Bool) : F :=
  eq1G (ρ.toArray.getD k 0) b * (if k < recRowBits then eq1G (rlo.toArray.getD k 0) q else if q then 0 else 1)

/-- The initial state. -/
def kg_init : Array F := (Array.replicate sLanes (0 : F)).set! 0 1

theorem kg_divKern_unfold (ρ rlo rhi : List F) :
    divKernG 0 posBits ρ rlo rhi = (List.range sLanes).foldl (fun acc rem => acc +
      ((List.range posBits).reverse.foldl (fun V k => kg_dstep (kg_fac ρ rlo k) V) kg_init).getD rem 0 *
        E2V.eqAtF rhi rem) 0 := by
  unfold divKernG
  dsimp only
  refine List.foldl_ext _ _ _ fun acc rem _ => ?_
  refine congrArg (acc + ·) (congrArg (· * E2V.eqAtF rhi rem) (congrArg (Array.getD · rem 0) ?_))
  apply List.foldl_ext
  intro V k hk
  have hk' : k < posBits := by simpa using hk
  simp only [hk', decide_true, ite_true]
  rfl

theorem kg_getD_modify (W : Array F) (j i : Nat) (v : F) (hj : j < W.size) :
    (W.modify j (· + v)).getD i 0 = W.getD i 0 + if j = i then v else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split_ifs with h
  · subst h; simp [Array.getElem?_eq_getElem hj]
  · simp

/-- An array fold that adds `c x i` at each `i`. -/
theorem kg_fold_add {α : Type} (L : List α) (G : Array F → α → Array F) (c : α → Nat → F)
    (hG : ∀ W x, x ∈ L → W.size = 17 → (G W x).size = 17 ∧ ∀ i, (G W x).getD i 0 = W.getD i 0 + c x i) :
    ∀ W : Array F, W.size = 17 →
      (L.foldl G W).size = 17 ∧ ∀ i, (L.foldl G W).getD i 0 = W.getD i 0 + (L.map (c · i)).sum := by
  induction L with
  | nil => intro W hW; simp [hW]
  | cons x L ih =>
    intro W hW
    obtain ⟨h1, h2⟩ := hG W x List.mem_cons_self hW
    obtain ⟨h3, h4⟩ := ih (fun W y hy => hG W y (List.mem_cons_of_mem _ hy)) (G W x) h1
    refine ⟨h3, fun i => ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons, add_assoc]

theorem kg_idx_lt {rem : Nat} (h : rem < 17) (b : Bool) : kg_idx rem b < 17 := by
  unfold kg_idx kg_t
  rw [show sLanes = 17 from rfl]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero, decide_eq_true_eq] <;>
    split_ifs <;> omega

theorem kg_list_sum_range (n : Nat) (f : Nat → F) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **The step** on the remainders. -/
theorem kg_dstep_getD (Fb : Bool → Bool → F) (V : Array F) (i : Nat) :
    (kg_dstep Fb V).getD i 0 = ∑ rem ∈ Finset.range 17,
      ((if kg_idx rem false = i then V.getD rem 0 * kg_f Fb rem false else 0) +
        (if kg_idx rem true = i then V.getD rem 0 * kg_f Fb rem true else 0)) := by
  have hin := fun (rem : Nat) (hrem : rem < 17) => kg_fold_add [false, true]
    (fun W b => W.modify (kg_idx rem b) (· + V.getD rem 0 * kg_f Fb rem b))
    (fun b i => if kg_idx rem b = i then V.getD rem 0 * kg_f Fb rem b else 0)
    (fun W b _ hW => ⟨by simp [hW], fun i => kg_getD_modify W _ i _ (hW ▸ kg_idx_lt hrem b)⟩)
  obtain ⟨_, h⟩ := kg_fold_add (List.range sLanes) _ _
    (fun W rem hrem hW => hin rem (List.mem_range.1 hrem) W hW) (Array.replicate sLanes 0)
    (by rw [Array.size_replicate]; rfl)
  rw [kg_dstep, h i, kg_list_sum_range]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  split_ifs <;> simp [sLanes, recStreamCols]

theorem kg_init_getD (i : Nat) : (kg_init (F := F)).getD i 0 = if 0 = i then (1 : F) else 0 := by
  unfold kg_init
  rw [show sLanes = 17 from rfl]
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Array.getElem?_replicate,
    Array.size_replicate]
  split_ifs <;> first | rfl | omega

/-- `Π_{m < n} fac m (bit_m t) (bit_m Q)`. -/
def kg_P (fac : Nat → Bool → Bool → F) : Nat → Nat → Nat → F
  | 0, _, _ => 1
  | n + 1, t, Q => fac 0 (decide (t % 2 = 1)) (decide (Q % 2 = 1)) * kg_P (fun m => fac (m + 1)) n (t / 2) (Q / 2)

theorem kg_P_succ (fac : Nat → Bool → Bool → F) (n t Q : Nat) :
    kg_P fac (n + 1) t Q =
      fac 0 (decide (t % 2 = 1)) (decide (Q % 2 = 1)) * kg_P (fun m => fac (m + 1)) n (t / 2) (Q / 2) := rfl

/-- The automaton's state after `n` bits: `V[R] = Σ_{t < 2^n, t mod 17 = R} Π_m fac m (bit_m t) (bit_m (t / 17))`. -/
def kg_C (fac : Nat → Bool → Bool → F) (n R : Nat) : F :=
  ∑ t ∈ Finset.range (2 ^ n), if t % 17 = R then kg_P fac n t (t / 17) else 0

theorem kg_idx_false (t : Nat) : kg_idx (t % 17) false = (2 * t) % 17 := by
  unfold kg_idx kg_t
  rw [show sLanes = 17 from rfl]
  simp only [Bool.false_eq_true, ite_false, add_zero, decide_eq_true_eq]
  split_ifs <;> omega

theorem kg_idx_true (t : Nat) : kg_idx (t % 17) true = (2 * t + 1) % 17 := by
  unfold kg_idx kg_t
  rw [show sLanes = 17 from rfl]
  simp only [ite_true, decide_eq_true_eq]
  split_ifs <;> omega

omit [Field F] in
theorem kg_f_false (Fb : Bool → Bool → F) (t : Nat) :
    kg_f Fb (t % 17) false = Fb false (decide ((2 * t) / 17 % 2 = 1)) := by
  unfold kg_f kg_t
  rw [show sLanes = 17 from rfl]
  simp only [Bool.false_eq_true, ite_false, add_zero]
  by_cases h : 17 ≤ 2 * (t % 17)
  · have h' : (2 * t) / 17 % 2 = 1 := by (clear * - t h; omega)
    simp only [h, h', decide_true, ite_true]
  · have h' : ¬ (2 * t) / 17 % 2 = 1 := by (clear * - t h; omega)
    simp only [h, h', decide_false, Bool.false_eq_true, ite_false]

omit [Field F] in
theorem kg_f_true (Fb : Bool → Bool → F) (t : Nat) :
    kg_f Fb (t % 17) true = Fb true (decide ((2 * t + 1) / 17 % 2 = 1)) := by
  unfold kg_f kg_t
  rw [show sLanes = 17 from rfl]
  simp only [ite_true]
  by_cases h : 17 ≤ 2 * (t % 17) + 1
  · have h' : (2 * t + 1) / 17 % 2 = 1 := by (clear * - t h; omega)
    simp only [h, h', decide_true, ite_true]
  · have h' : ¬ (2 * t + 1) / 17 % 2 = 1 := by (clear * - t h; omega)
    simp only [h, h', decide_false, Bool.false_eq_true, ite_false]

/-- **One step of the invariant**: the step maps the state after the bits above to the state after this one. -/
theorem kg_step_closed (fac : Nat → Bool → Bool → F) (n i : Nat) :
    ∑ rem ∈ Finset.range 17,
      ((if kg_idx rem false = i then kg_C (fun m => fac (m + 1)) n rem * kg_f (fac 0) rem false else 0) +
        (if kg_idx rem true = i then kg_C (fun m => fac (m + 1)) n rem * kg_f (fac 0) rem true else 0)) =
      kg_C fac (n + 1) i := by
  have e : ∀ (rem : Nat) (p : Prop) [Decidable p] (x : F),
      (if p then kg_C (fun m => fac (m + 1)) n rem * x else 0) = ∑ t ∈ Finset.range (2 ^ n),
        if t % 17 = rem then (if p then kg_P (fun m => fac (m + 1)) n t (t / 17) * x else 0) else 0 := by
    intro rem p _ x
    unfold kg_C
    split_ifs with hp
    · rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun t _ => ?_; split_ifs <;> simp
    · simp
  have h17 : ∀ t : Nat, t % 17 < 17 := fun t => Nat.mod_lt t (by norm_num)
  simp only [e, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have e2 : ∀ t rem : Nat, ((if t % 17 = rem then (if kg_idx rem false = i then
      kg_P (fun m => fac (m + 1)) n t (t / 17) * kg_f (fac 0) rem false else 0) else 0) +
      (if t % 17 = rem then (if kg_idx rem true = i then
      kg_P (fun m => fac (m + 1)) n t (t / 17) * kg_f (fac 0) rem true else 0) else 0)) =
      if t % 17 = rem then ((if kg_idx (t % 17) false = i then
      kg_P (fun m => fac (m + 1)) n t (t / 17) * kg_f (fac 0) (t % 17) false else 0) +
      (if kg_idx (t % 17) true = i then
      kg_P (fun m => fac (m + 1)) n t (t / 17) * kg_f (fac 0) (t % 17) true else 0)) else 0 := by
    intro t rem
    by_cases ht : t % 17 = rem
    · subst ht; simp only [ite_true]
    · simp only [ht, ite_false, add_zero]
  simp only [e2, Finset.sum_ite_eq, Finset.mem_range, h17, ite_true]
  unfold kg_C
  rw [pow_succ, mul_comm _ 2, kg_sum_pairs]
  refine Finset.sum_congr rfl fun t _ => ?_
  have a1 : (2 * t) % 2 = 0 := by (clear * - t; omega)
  have a2 : (2 * t) / 2 = t := by (clear * - t a1; omega)
  have a3 : (2 * t + 1) % 2 = 1 := by (clear * - t a1; omega)
  have a4 : (2 * t + 1) / 2 = t := by (clear * - t a1 a3; omega)
  have a5 : (2 * t) / 17 / 2 = t / 17 := by (clear * - t a1 a3; omega)
  have a6 : (2 * t + 1) / 17 / 2 = t / 17 := by (clear * - t a1 a3; omega)
  rw [kg_idx_false, kg_idx_true, kg_f_false, kg_f_true, kg_P_succ, kg_P_succ]
  simp only [a1, a2, a3, a4, a5, a6, Nat.zero_ne_one, decide_false, decide_true]
  split_ifs <;> ring

/-- **The invariant**: the automaton after the bits `n − 1, …, 0` (high to low) is `kg_C`. -/
theorem kg_fold_closed (n : Nat) : ∀ (fac : Nat → Bool → Bool → F) (i : Nat),
    ((List.range n).foldr (fun k V => kg_dstep (fac k) V) kg_init).getD i 0 = kg_C fac n i := by
  induction n with
  | zero =>
    intro fac i
    rw [List.range_zero, List.foldr_nil, kg_init_getD]
    unfold kg_C
    rw [pow_zero, Finset.sum_range_one]
    simp [kg_P]
  | succ n ih =>
    intro fac i
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, kg_dstep_getD]
    simp only [ih]
    exact kg_step_closed fac n i

theorem kg_divKern_closed (ρ rlo rhi : List F) :
    divKernG 0 posBits ρ rlo rhi = ∑ rem ∈ Finset.range 17, kg_C (kg_fac ρ rlo) 19 rem * E2V.eqAtF rhi rem := by
  rw [kg_divKern_unfold, List.foldl_reverse, kg_foldl_range, zero_add]
  simp only [kg_fold_closed]
  rfl

/-! ## The factors: `eq(ρ, i)`, `eq(r_lo, i / 17)` and `i / 17 < 2^14` -/

/-- `Π_{m < n} u m (bit_m t)`. -/
def kg_U (u : Nat → Bool → F) : Nat → Nat → F
  | 0, _ => 1
  | n + 1, t => u 0 (decide (t % 2 = 1)) * kg_U (fun m => u (m + 1)) n (t / 2)

theorem kg_P_mul (n : Nat) : ∀ (u w : Nat → Bool → F) (t Q : Nat),
    kg_P (fun m b q => u m b * w m q) n t Q = kg_U u n t * kg_U w n Q := by
  induction n with
  | zero => intros; simp [kg_P, kg_U]
  | succ n ih => intro u w t Q; simp only [kg_P_succ, kg_U, ih]; ring

theorem kg_U_eqAtF (ρ : List F) : ∀ t : Nat, kg_U (fun m b => eq1G (ρ.getD m 0) b) ρ.length t = E2V.eqAtF ρ t := by
  induction ρ with
  | nil => intro t; rfl
  | cons a ρ ih =>
    intro t
    simp only [List.length_cons, kg_U, List.getD_cons_succ, List.getD_cons_zero, ih, kg_eqAtF_cons]
    simp only [eq1G, decide_eq_true_eq]

theorem kg_U_congr (n : Nat) : ∀ (u u' : Nat → Bool → F) (t : Nat), (∀ m < n, u m = u' m) →
    kg_U u n t = kg_U u' n t := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro u u' t h
    simp only [kg_U, h 0 (by (clear * - n; omega)), ih (fun m => u (m + 1)) (fun m => u' (m + 1)) (t / 2)
      (fun m hm => h (m + 1) (by (clear * - m n hm; omega)))]

theorem kg_U_split (a : Nat) : ∀ (u : Nat → Bool → F) (b Q : Nat),
    kg_U u (a + b) Q = kg_U u a Q * kg_U (fun m => u (m + a)) b (Q / 2 ^ a) := by
  induction a with
  | zero => intros; simp [kg_U]
  | succ a ih =>
    intro u b Q
    rw [show a + 1 + b = (a + b) + 1 by (clear * - a b; omega)]
    simp only [kg_U, ih, Nat.div_div_eq_div_mul, ← pow_succ']
    have hl : (fun m => u (m + a + 1)) = fun m => u (m + (a + 1)) := funext fun m => by rw [Nat.add_assoc]
    rw [hl, mul_assoc]

theorem kg_U_zero (n : Nat) : kg_U (F := F) (fun _ q => if q then 0 else 1) n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [kg_U]; simpa using ih

theorem kg_U_lo (rlo : List F) (hlo : rlo.length = recRowBits) (Q : Nat) (hQ : Q < 2 ^ 15) :
    kg_U (fun m q => if m < recRowBits then eq1G (rlo.toArray.getD m 0) q else if q then 0 else 1) 19 Q =
      E2V.eqAtF rlo Q * (if Q < 2 ^ 14 then 1 else 0) := by
  rw [show 19 = 14 + 5 from rfl, kg_U_split,
    kg_U_congr 14 _ (fun m b => eq1G (rlo.getD m 0) b) Q (fun m hm => funext fun q => by
      simp only [show m < recRowBits from hm, ite_true, kg_toArray_getD]),
    kg_U_congr 5 _ (fun _ q => if q then 0 else 1) _ (fun m _ => funext fun q => by
      simp only [show ¬ (m + 14 < recRowBits) by simp [recRowBits], ite_false])]
  have h := kg_U_eqAtF rlo Q
  rw [hlo] at h
  rw [h]
  rcases (show Q / 2 ^ 14 = 0 ∨ Q / 2 ^ 14 = 1 by (clear * - Q F rlo hQ; omega)) with h1 | h1
  · rw [h1, kg_U_zero]
    simp only [show Q < 2 ^ 14 by (clear * - Q F rlo hQ h1; omega), ite_true]
  · have h2 : ¬ Q < 2 ^ 14 := by (clear * - Q F rlo hQ h1; omega)
    rw [h1]
    simp only [h2, ite_false]
    simp [kg_U]

/-! ## The two lemmas -/

/-- **The long-division automaton is its sum** (at `S_flat`'s region: positions from `0`, all `19` bits
free). -/
theorem divKernG_eq (ρ rlo rhi : List F) (hρ : ρ.length = posBits) (hlo : rlo.length = recRowBits) :
    divKernG 0 posBits ρ rlo rhi =
      E2V.sumF ((List.range sPos).map fun i => E2V.eqAtF ρ i * E2V.eqAtF rlo (i / sLanes) * E2V.eqAtF rhi (i % sLanes)) := by
  have h17 : ∀ t : Nat, t % 17 < 17 := fun t => Nat.mod_lt t (by norm_num)
  have hP : ∀ t, t < 2 ^ 19 →
      kg_P (kg_fac ρ rlo) 19 t (t / 17) = E2V.eqAtF ρ t * (E2V.eqAtF rlo (t / 17) * if t < sPos then 1 else 0) := by
    intro t ht
    have hu := kg_U_eqAtF ρ t
    rw [hρ] at hu
    rw [show kg_fac ρ rlo = fun m b q => (fun m b => eq1G (ρ.toArray.getD m 0) b) m b *
        (fun m q => if m < recRowBits then eq1G (rlo.toArray.getD m 0) q else if q then 0 else 1) m q from rfl,
      kg_P_mul, kg_U_lo rlo hlo _ (by (clear * - t F ρ rlo ht; omega))]
    simp only [kg_toArray_getD]
    rw [hu]
    simp only [show (t / 17 < 2 ^ 14 ↔ t < sPos) by rw [show sPos = 17 * 2 ^ 14 from rfl]; (clear * - t F ρ rlo ht; omega)]
  rw [kg_divKern_closed, kg_sumE_range]
  unfold kg_C
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range, h17, ite_true]
  rw [show (2 : Nat) ^ 19 = sPos + 245760 from rfl, Finset.sum_range_add]
  have hs : sPos = 17 * 2 ^ 14 := rfl
  have h2 : ∀ x ∈ Finset.range 245760,
      kg_P (kg_fac ρ rlo) 19 (sPos + x) ((sPos + x) / 17) * E2V.eqAtF rhi ((sPos + x) % 17) = 0 := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [hP _ (by (clear * - x F ρ rlo hs hx; omega))]
    simp
  rw [Finset.sum_eq_zero h2, add_zero]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [hP t (ht.trans (by rw [hs]; norm_num))]
  simp only [ht, ite_true, mul_one, show sLanes = 17 from rfl]

/-- **The comparator is its sum**: `Σ_{i < 2^l, c ≤ i} eq(ρ, i)·eq(r, i)`. -/
theorem geKernG_eq (c l : Nat) (ρ r : List F) (hρ : ρ.length = l) (hr : r.length = l) (hc : c < 2 ^ l) :
    geKernG c l ρ r =
      E2V.sumF (((List.range (2 ^ l)).filter fun i => decide (c ≤ i)).map fun i => E2V.eqAtF ρ i * E2V.eqAtF r i) := by
  rw [kg_geKern_unfold, List.foldl_reverse, kg_ge_inv l c ρ r hρ hr hc, kg_sumE_filter]
  simp only
  symm
  rw [Finset.sum_congr rfl (g := fun i => (if c < i then E2V.eqAtF ρ i * E2V.eqAtF r i else 0) +
      if c = i then E2V.eqAtF ρ i * E2V.eqAtF r i else 0), Finset.sum_add_distrib, Finset.sum_ite_eq]
  · simp only [Finset.mem_range.2 hc, ite_true]; ring
  · intro i _
    rcases lt_trichotomy c i with h | h | h
    · simp only [h, h.le, h.ne, decide_true, ite_true, ite_false]; ring
    · subst h; simp
    · have h1 : ¬ c ≤ i := by (clear * - c i F l ρ r h; omega)
      have h2 : c ≠ i := by (clear * - c i F l ρ r h; omega)
      have h3 : ¬ c < i := by (clear * - c i F l ρ r h; omega)
      simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ite_false]; ring

end Lvm.E2T
end
-- ===== end of `LvmE2TVKernP` =====

/-!
# The typed kernels' closed forms at `E2`

On a native instance whose shape check holds (`TNat.okB`) and whose regions are the layout's (`TNat.layOk`):

* over any field: `kf_eqAtF_split` (an aligned index splits), `kf_sflat` (a stream position's `C_rec` word),
  `kf_mleKG` (`mleKG` is its sum), `kf_virtG` (`virtG` is the sum of its regions' terms), `kf_regSumW`
  (`regSumW` on `N.inst` is a sum over the native regions);
* **`virtD_rel`**: `virtD` is `virtT`; **`relayKernD_rel`**: `relayKernD` is `relayKernT` (the automata,
  `LvmE2TVKernP`).
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm Lvm.TypedV
open Lvm.Typed (YSrc xVars yVars relayRounds Lay)
open Finset (range)

section Gen

variable {F : Type} [Field F]

/-- A list sum over a range is the `Finset` sum. -/
theorem kf_list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, kf_list_sum_range f n, Finset.sum_range_succ]
    simp

/-- A left fold adding terms is the sum. -/
theorem kf_foldl {α M : Type} [AddCommMonoid M] (L : List α) (G : M → α → M) (T : α → M)
    (h : ∀ acc g, G acc g = acc + T g) (a : M) : L.foldl G a = a + (L.map T).sum := by
  induction L generalizing a with
  | nil => simp
  | cons g L ih => rw [List.foldl_cons, ih, h, List.map_cons, List.sum_cons, add_assoc]

/-- **An aligned index splits**: the low `l` bits are `i`, the high ones `b >>> l` (any length of `X`). -/
theorem kf_eqAtF_split (X : List F) (b l i : ℕ) (hb : b % 2 ^ l = 0) (hi : i < 2 ^ l) :
    E2V.eqAtF X (b + i) = E2V.eqAtF (X.take l) i * E2V.eqAtF (X.drop l) (b >>> l) := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  conv_lhs => rw [← List.take_append_drop l X]
  rw [E2V.eqAtF_append]
  congr 1
  · rw [E2V.eqAtF_mod, E2V.eqAtF_mod _ i]
    have hd : 2 ^ (X.take l).length ∣ 2 ^ l := Nat.pow_dvd_pow 2 (by simp)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_trans hd (dvd_mul_right _ _)), zero_add, Nat.mod_mod]
  · rcases le_or_gt l X.length with hl | hl
    · rw [List.length_take_of_le hl, Nat.shiftRight_eq_div_pow, Nat.mul_add_div (by positivity),
        Nat.div_eq_of_lt hi, add_zero, Nat.mul_div_cancel_left _ (by positivity)]
    · rw [List.drop_of_length_le hl.le, E2V.eqAtF_nil, E2V.eqAtF_nil]

/-- **A stream position's `C_rec` word** splits into its row (`i / 17`) and its lane (`i mod 17`). -/
theorem kf_sflat (R : List F) (i : ℕ) (hi : i < sPos) :
    E2V.eqAtF R (sflatWord i) =
      E2V.eqAtF (R.take recRowBits) (i / sLanes) * E2V.eqAtF (R.drop recRowBits) (i % sLanes) := by
  rw [sflatWord, ite_eq_left hi, kf_eqAtF_split R _ recRowBits _ (Nat.mul_mod_left _ _)]
  · rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by positivity)]
  · exact (Nat.div_lt_iff_lt_mul (by norm_num [sLanes, recStreamCols])).2 (by rw [mul_comm]; exact hi)

/-- **`mleKG` is its sum.** -/
theorem kf_mleKG [Algebra FK F] (log : ℕ) (v : ℕ → FK) (pt : List F) (hpt : log ≤ pt.length) :
    mleKG log v pt = ∑ i ∈ range (2 ^ log), algebraMap FK F (v i) * E2V.eqAtF (pt.take log) i := by
  unfold mleKG
  dsimp only
  rw [kg_foldl_range, zero_add]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [kg_toArray_getD, E2V.eqKernelF_getD, List.length_take_of_le hpt, ite_eq_left (Finset.mem_range.1 hi)]

/-- **`virtG` is the sum of its regions' terms.** -/
theorem kf_virtG [Algebra FK F] (regs : List NReg) (hdr : Array FK) (ry : List F)
    (hl : ∀ g ∈ regs, g.src = .pub → g.log ≤ ry.length) :
    virtG regs hdr ry = (regs.map fun g ↦
      (if g.src = .pub then hiWG ry g.log g.base *
        ∑ i ∈ range (2 ^ g.log), algebraMap FK F (hdr.getD (g.dst + i) 0) * E2V.eqAtF (ry.take g.log) i
        else 0) + (if g.src = .one then hiWG ry g.log g.base else 0)).sum := by
  unfold virtG
  rw [kf_foldl _ _ (fun g ↦ (if g.src = .pub then hiWG ry g.log g.base *
      mleKG g.log (fun i ↦ hdr.getD (g.dst + i) 0) ry else 0) + (if g.src = .one then hiWG ry g.log g.base else 0))
    (fun acc g ↦ by rcases g with ⟨b, l, src, d⟩; cases src <;> simp), zero_add]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hp : g.src = .pub
  · simp only [hp, ↓reduceIte]
    rw [kf_mleKG _ _ _ (hl g hg hp)]
  · simp only [hp, ↓reduceIte]

end Gen

/-- **`regSumW` on `N.inst`** is a sum over the native regions. -/
theorem kf_regSumW (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (hlay : N.layOk lay = true) {M : Type}
    [AddCommMonoid M] (S : YSrc → Bool) (f : ℕ → M) :
    regSumW (N.inst Q lay) S f =
      (N.regs.map fun g ↦ if S g.src then ∑ i ∈ range (2 ^ g.log), f (g.base + i) else 0).sum := by
  have hy : lay.yregs = N.regs.map fun r ↦ (⟨r.base, r.log, r.src⟩ : Lvm.Typed.YReg) := by
    simpa [TNat.layOk] using hlay
  unfold regSumW
  simp only [TNat.inst, hy, List.map_map, Function.comp_def, kf_list_sum_range]

/-- **`regSumW` on the S2GT instance** (`TNatT.inst`: only `pubV` differs from `N.toN.inst`, and `regSumW` reads the
regions). -/
theorem kf_regSumWT (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (hlay : N.toN.layOk lay = true) {M : Type}
    [AddCommMonoid M] (S : YSrc → Bool) (f : ℕ → M) :
    regSumW (N.inst Q lay) S f =
      (N.toN.regs.map fun g ↦ if S g.src then ∑ i ∈ range (2 ^ g.log), f (g.base + i) else 0).sum :=
  kf_regSumW N.toN Q lay hlay S f

/-- `toE2` of a list sum. -/
theorem kf_toE2_sum {α : Type} (L : List α) (f : α → FE2) :
    FE2.toE2 (L.map f).sum = (L.map fun g ↦ FE2.toE2 (f g)).sum := by
  rw [← FE2.ringEquivE2_apply, map_list_sum, List.map_map]; rfl

/-- `toE2` of a `Finset` sum. -/
theorem kf_toE2_fsum {ι : Type} (s : Finset ι) (f : ι → FE2) :
    FE2.toE2 (∑ i ∈ s, f i) = ∑ i ∈ s, FE2.toE2 (f i) := by
  rw [← FE2.ringEquivE2_apply, map_sum]; rfl

theorem kf_toE2_mul (a b : FE2) : FE2.toE2 (a * b) = FE2.toE2 a * FE2.toE2 b := by
  rw [← FE2.ringEquivE2_apply, map_mul]; rfl

theorem kf_toE2_algebraMap (a : FK) : FE2.toE2 (algebraMap FK FE2 a) = kE2 a := rfl

variable (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)

/-- **`virtD` is `virtT`** (the `PUB` region by its multilinear extension, the `1` region by its weight; the `QLT`
part is `0`: `TNat.inst`'s `qltV` is `0`). -/
theorem virtD_rel (nuMain nuRec : ℕ) (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true)
    (pub : Pub) (ry : List FE2) (hry : ry.length = yVars) :
    FE2.toE2 (virtD N pub ry) = virtT (N.inst Q lay) pub (ry.map FE2.toE2) := by
  obtain ⟨hreg, -, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  have hpub : ∀ g ∈ N.regs, g.src = .pub → g.log ≤ ry.length := fun g hg hs ↦ by
    rw [(hreg g hg).2.2.2.1 hs |>.1, hry]; norm_num
  unfold virtD
  rw [kf_virtG _ _ _ hpub, kf_toE2_sum]
  unfold virtT regSumT
  rw [kf_regSumWT N Q lay hlay, kf_regSumWT N Q lay hlay, kf_regSumWT N Q lay hlay,
    ← List.sum_map_add, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  obtain ⟨hb1, -, -, hp, hone⟩ := hreg g hg
  have hoff := fm_off N.toN hpw g hg
  rcases g with ⟨b, l, src, d⟩
  cases src
  · simp
  · simp
  · obtain ⟨-, rfl⟩ := hp rfl
    simp only [ite_true, beq_iff_eq, reduceCtorEq, ite_false, add_zero, beq_self_eq_true, kf_toE2_mul, hiWG,
      E2V.toE2_eqAtF, kf_toE2_fsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 2 ^ l := Finset.mem_range.1 hi
    simp only at hb1 hoff
    rw [kf_toE2_algebraMap, kf_eqAtF_split _ b l i hb1 hi', List.map_take, List.map_drop, zero_add]
    simp only [TNatT.inst, TNat.instL, TNat.inst]
    rw [hoff i hi', zero_add, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    ring
  · simp
  · simp
  · have hk0 : kE2 0 = 0 := by rw [kE2, show FE2.ofK 0 = 0 from rfl, FE2.toE2_zero]
    simp [TNatT.inst, TNat.instL, TNat.inst, hk0]
  · obtain rfl := hone rfl
    simp [hiWG, E2V.toE2_eqAtF]

/-- **`relayKernD` is `relayKernT`** (the long-division automaton and the comparator, `LvmE2TVKernP`). -/
theorem relayKernD_rel (nuMain nuRec : ℕ) (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true)
    (ry r : List FE2) (hry : ry.length = yVars) (hr : r.length = relayRounds) :
    FE2.toE2 (relayKernD N ry r) = relayKernT (N.inst Q lay) (ry.map FE2.toE2) (r.map FE2.toE2) := by
  obtain ⟨hreg, ⟨g, hg1, hlog, hdst⟩, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  have hgm : g ∈ N.toN.regs :=
    (List.mem_filter.1 (hg1 ▸ List.mem_singleton_self g : g ∈ N.toN.regsOf .sflat)).1
  obtain ⟨hb1, -⟩ := hreg g hgm
  have hoff := fm_off N.toN hpw g hgm
  have hsingle : regSumW (N.inst Q lay) (fun s ↦ s == .sflat)
      (fun y ↦ E2V.eqAtF (ry.map FE2.toE2) y *
        E2V.eqAtF (r.map FE2.toE2) ((N.inst Q lay).sflatW y)) =
      ∑ i ∈ range (2 ^ g.log), E2V.eqAtF (ry.map FE2.toE2) (g.base + i) *
        E2V.eqAtF (r.map FE2.toE2) ((N.inst Q lay).sflatW (g.base + i)) := by
    rw [kf_regSumWT N Q lay hlay]
    have := fm_sum_filter N.toN.regs (fun g ↦ g.src == .sflat)
      (fun g ↦ ∑ i ∈ range (2 ^ g.log), E2V.eqAtF (ry.map FE2.toE2) (g.base + i) *
        E2V.eqAtF (r.map FE2.toE2) ((N.inst Q lay).sflatW (g.base + i)))
    rw [show N.toN.regs.filter (fun g ↦ g.src == .sflat) = [g] from hg1] at this
    simpa using this.symm
  unfold relayKernD relayKernT regSumT
  rw [hg1, hsingle]
  rcases g with ⟨b, l, src, d⟩
  simp only at hlog hdst hb1 hoff
  subst hlog hdst
  have hidp : ¬ (0 + 2 ^ posBits ≤ sPos) := by norm_num [sPos, sLanes, recStreamCols, recRowBits]
  have hρ : (ry.take posBits).length = posBits := List.length_take_of_le (by rw [hry]; norm_num)
  have hlo : (r.take recRowBits).length = recRowBits := List.length_take_of_le (by rw [hr]; norm_num)
  have hr' : r.length = posBits := hr
  have hc : sPos < 2 ^ posBits := by norm_num [sPos, sLanes, recStreamCols, recRowBits]
  simp only [relayKernG, List.foldl_cons, List.foldl_nil, zero_add, Nat.zero_shiftRight, Nat.min_zero,
    Nat.sub_zero, List.drop_of_length_le (le_of_eq hr'), List.take_of_length_le (le_of_eq hr')]
  rw [divKernG_eq _ _ _ hρ hlo, geKernG_eq _ _ _ _ hρ hr' hc, ite_eq_right (by simpa using hidp), E2V.eqAtF_nil,
    one_mul, kf_toE2_mul, FE2.toE2_add, hiWG, E2V.toE2_eqAtF, E2V.toE2_sumF, E2V.toE2_sumF, List.map_map,
    List.map_map, E2V.sumF_map_range, E2V.sumF_eq_sum, fm_sum_filter, kf_list_sum_range]
  simp only [TNatT.inst, TNat.instL, TNat.inst]
  have e : ∀ i ∈ range (2 ^ posBits), E2V.eqAtF (ry.map FE2.toE2) (b + i) *
      E2V.eqAtF (r.map FE2.toE2) (sflatWord (N.toN.off (b + i))) =
        E2V.eqAtF ((ry.map FE2.toE2).drop posBits) (b >>> posBits) *
          (E2V.eqAtF ((ry.map FE2.toE2).take posBits) i * E2V.eqAtF (r.map FE2.toE2) (sflatWord i)) := by
    intro i hi
    rw [hoff i (Finset.mem_range.1 hi), zero_add, kf_eqAtF_split _ b posBits i hb1 (Finset.mem_range.1 hi)]
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, List.map_drop]
  conv_rhs => rw [← Finset.sum_range_add_sum_Ico _ hc.le]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· + ·) ?_ ?_)
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [Function.comp_apply]
    rw [kf_sflat _ i (Finset.mem_range.1 hi), kf_toE2_mul, kf_toE2_mul, E2V.toE2_eqAtF, E2V.toE2_eqAtF,
      E2V.toE2_eqAtF, List.map_take, List.map_drop, List.map_take]
    ring
  · rw [← Finset.sum_filter]
    have hset : (range (2 ^ posBits)).filter (fun k ↦ decide (sPos ≤ k) = true) = Finset.Ico sPos (2 ^ posBits) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, decide_eq_true_eq]
      omega
    rw [hset]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : sPos ≤ i := (Finset.mem_Ico.1 hi).1
    simp only [Function.comp_apply]
    rw [sflatWord, ite_eq_right (by omega), kf_toE2_mul, E2V.toE2_eqAtF, E2V.toE2_eqAtF, List.map_take]

end Lvm.E2T
