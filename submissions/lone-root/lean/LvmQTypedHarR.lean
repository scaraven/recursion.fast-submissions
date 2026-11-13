-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's relayout phase: `relayKernG`'s value is V_S's closed form
-- `relayKernF` (the stride-17 division automaton and the identity tail), and `relayG` replays `dRelayT`.
import LvmQTypedHarB

/-!
# The `S_flat` relayout in the circuit

* **`relayKernG_spec`**: on regions that are V_S's (`TdOk`: one `S_flat` region of `2^19` words from position 0),
  `relayKernG`'s value at `(r_y, r)` is `relayKernF N r_y r` (the circuit's division by 17, MSB first, with the
  remainders' weights, against V_S's array automaton `divKern`; the circuit's `tailG` against `geKern`).
* **`relayG_replays`**: `relayG` replays `dRelayT` from `rRP P` to `aP P`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)

open Lvm.TypedV (eq1)

/-! ## Helpers (the division automaton, `geKern`'s tail, `tailG`) -/
/-- `divKern`'s step (its local `step`). -/
def r_dStep (p0 log : Nat) (ρa ra : Array FE) (V : Array FE) (k : Nat) : Array FE :=
  let free := decide (k < log)
  let bits : List Bool := if free then [false, true] else [p0.testBit k]
  let fac (b q : Bool) : FE :=
    (if free then eq1 (ρa.getD k 0) b else 1) *
      (if k < TypedV.recRowBits then eq1 (ra.getD k 0) q else if q then 0 else 1)
  let f00 := fac false false
  let f01 := fac false true
  let f10 := fac true false
  let f11 := fac true true
  (List.range TypedV.sLanes).foldl (fun W rem =>
    let v := V.getD rem 0
    bits.foldl (fun W b =>
      let t := 2 * rem + (if b then 1 else 0)
      let q := decide (TypedV.sLanes ≤ t)
      let f := if b then (if q then f11 else f10) else (if q then f01 else f00)
      W.modify (if q then t - TypedV.sLanes else t) (· + v * f)) W) (Array.replicate TypedV.sLanes 0)

theorem r_divKern_eq (p0 log : Nat) (ρ rlo rhi : List FE) :
    TypedV.divKern p0 log ρ rlo rhi = (List.range 17).foldl (fun acc rem => acc +
      ((List.range 19).reverse.foldl (r_dStep p0 log ρ.toArray rlo.toArray)
        ((Array.replicate 17 (0 : FE)).set! 0 1)).getD rem 0 * eqAtF rhi rem) 0 := rfl

/-- `geKern`'s step. -/
def r_geStep (c : Nat) (t : Nat → Bool → FE) (st : FE × FE) (k : Nat) : FE × FE :=
  let full := t k false + t k true
  if c.testBit k then (st.1 * t k true, st.2 * full) else (st.1 * t k false, st.2 * full + st.1 * t k true)

theorem r_geKern_eq (c log : Nat) (ρ r : List FE) :
    TypedV.geKern c log ρ r = ((List.range log).reverse.foldl
      (r_geStep c fun k b => eq1 (ρ.toArray.getD k 0) b * eq1 (r.toArray.getD k 0) b) (1, 0)).1 +
      ((List.range log).reverse.foldl
      (r_geStep c fun k b => eq1 (ρ.toArray.getD k 0) b * eq1 (r.toArray.getD k 0) b) (1, 0)).2 := rfl

theorem r_sLanes_eq : TypedV.sLanes = 17 := rfl
theorem r_recRowBits_eq : TypedV.recRowBits = 14 := rfl

theorem r_getD_modify_add (A : Array FE) (i j : Nat) (d : FE) (hj : j < A.size) :
    (A.modify i (· + d)).getD j 0 = A.getD j 0 + if i = j then d else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getElem?_eq_getElem hj]
  split_ifs <;> simp

theorem r_foldl_getD {α : Type} (F : Array FE → α → Array FE) (D : α → Nat → FE)
    (hF : ∀ A x, (F A x).size = A.size ∧ ∀ j < A.size, (F A x).getD j 0 = A.getD j 0 + D x j) :
    ∀ (l : List α) (A : Array FE), (l.foldl F A).size = A.size ∧
      ∀ j < A.size, (l.foldl F A).getD j 0 = A.getD j 0 + (l.map fun x => D x j).sum
  | [], A => ⟨rfl, fun j _ => by simp⟩
  | x :: l, A => by
    obtain ⟨h1, h2⟩ := hF A x
    obtain ⟨ih1, ih2⟩ := r_foldl_getD F D hF l (F A x)
    refine ⟨by rw [List.foldl_cons, ih1, h1], fun j hj => ?_⟩
    rw [List.foldl_cons, ih2 j (by rw [h1]; exact hj), h2 j hj, List.map_cons, List.sum_cons, add_assoc]

/-- The quotient bit of `2 rem + b`. -/
def r_qN (rem : Nat) (b : Bool) : Bool := decide (17 ≤ 2 * rem + (if b then 1 else 0))

/-- The new remainder. -/
def r_idxN (rem : Nat) (b : Bool) : Nat :=
  if r_qN rem b then 2 * rem + (if b then 1 else 0) - 17 else 2 * rem + (if b then 1 else 0)

/-- The transition's factor. -/
def r_facN (ρa ra : Array FE) (k : Nat) (b q : Bool) : FE :=
  eq1 (ρa.getD k 0) b * (if k < 14 then eq1 (ra.getD k 0) q else if q then 0 else 1)

theorem r_dStep_getD (ρa ra V : Array FE) {k : Nat} (hk : k < 19) {j : Nat} (hj : j < 17) :
    (r_dStep 0 19 ρa ra V k).getD j 0 = ((List.range 17).map fun rem =>
      (if r_idxN rem false = j then V.getD rem 0 * r_facN ρa ra k false (r_qN rem false) else 0) +
      (if r_idxN rem true = j then V.getD rem 0 * r_facN ρa ra k true (r_qN rem true) else 0)).sum := by
  unfold r_dStep
  have hk' : decide (k < 19) = true := decide_eq_true hk
  simp only [hk', ite_true, r_sLanes_eq, r_recRowBits_eq]
  rw [(r_foldl_getD _ (fun rem j =>
      (if r_idxN rem false = j then V.getD rem 0 * r_facN ρa ra k false (r_qN rem false) else 0) +
      (if r_idxN rem true = j then V.getD rem 0 * r_facN ρa ra k true (r_qN rem true) else 0)) ?_ _ _).2 j
      (by simp [hj])]
  · simp [Array.getD]
  · intro A rem
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by simp, fun j hj => ?_⟩
    rw [r_getD_modify_add _ _ _ _ (by simpa using hj), r_getD_modify_add _ _ _ _ hj, add_assoc]
    simp only [r_idxN, r_qN, r_facN]
    by_cases h17 : 17 ≤ 2 * rem <;> by_cases h16 : 17 ≤ 2 * rem + 1 <;>
      simp [h17, h16]

def r_divCG (z ρi nρ : Cell) : Option Cell → BM (List (Nat × Nat × Cell))
  | none => pure [(0, 0, nρ), (1, 0, ρi)]
  | some r => do
    let nr ← neg1 r
    let c00 ← mulAdd .E nρ nr z
    let c10 ← mulAdd .E ρi nr z
    let c01 ← mulAdd .E nρ r z
    let c11 ← mulAdd .E ρi r z
    pure [(0, 0, c00), (1, 0, c10), (0, 1, c01), (1, 1, c11)]

/-- The incoming transitions of the new remainder `r'`. -/
def r_divIns (c : List (Nat × Nat × Cell)) (W : List (Option Cell)) (r' : Nat) : List (Cell × Cell) :=
  (List.range 17).flatMap fun rem => match W.getD rem none with
    | none => []
    | some w => c.filterMap fun x =>
      let v := 2 * rem + x.1
      let qb := if 17 ≤ v then 1 else 0
      if qb = x.2.1 ∧ v - 17 * qb = r' then some (w, x.2.2) else none

/-- A weight cell, `none` for no incoming transition. -/
def r_optMac (z : Cell) : List (Cell × Cell) → BM (Option Cell)
  | [] => pure none
  | l => do
    let s ← Lvm.QAcc.macChain l z
    pure (some s)

theorem r_divStep_eq (z ρi : Cell) (ri : Option Cell) (W : List (Option Cell)) :
    divStep z ρi ri W = (do
      let nρ ← neg1 ρi
      let c ← r_divCG z ρi nρ ri
      seqAll ((List.range 17).map fun r' => r_optMac z (r_divIns c W r'))) := by
  cases ri <;> rfl
section
variable {c : Ctx} {M : Mem}

theorem r_neg1_val {x : Cell} {p : Ptr} (h : SegsHold c M p (neg1 x p).2) :
    (neg1 x p).1.val M = x.val M + 1 := by
  simp only [neg1, addK] at h ⊢
  rw [lin_spec h, ofK_zero, ofK_one, zero_mul, add_zero]

theorem r_eqConstG_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (rs : List Cell) (b : Nat) (p : Ptr), SegsHold c M p (eqConstG z o rs b p).2 →
      (eqConstG z o rs b p).1.val M = eqAtF (vs M rs) b
  | [], b, p, _ => by simp only [eqConstG, pure_apply, vs, List.map_nil, eqAtF, ho]
  | r :: rs, b, p, h => by
    simp only [eqConstG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    have ih := r_eqConstG_val hz ho rs (b / 2) p h.1
    simp only [vs, List.map_cons, eqAtF] at ih ⊢
    by_cases hb : b % 2 = 1
    · rw [ite_eq_left hb] at h ⊢
      rw [ite_eq_left hb, mulAdd_spec h.2, ih, hz, add_zero, mul_comm]
    · rw [ite_eq_right hb] at h ⊢
      simp only [bind_apply] at h ⊢
      rw [segsHold_append] at h
      rw [ite_eq_right hb, mulAdd_spec h.2.2, r_neg1_val h.2.1, ih, hz, add_zero, mul_comm, add_comm (r.val M)]

end

/-- A weight cell's value (`none`: `0`). -/
def r_oval (M : Mem) : Option Cell → FE
  | none => 0
  | some x => x.val M

/-- The automaton's state against the circuit's weights. -/
def r_DRel (M : Mem) (V : Array FE) (W : List (Option Cell)) : Prop :=
  W.length = 17 ∧ ∀ j < 17, V.getD j 0 = r_oval M (W.getD j none)

theorem r_seqAll_length {α : Type} : ∀ (ms : List (BM α)) (p : Ptr), (seqAll ms p).1.length = ms.length
  | [], _ => rfl
  | m :: ms, p => by rw [Lvm.QSig.seqAll_cons_apply, List.length_cons, List.length_cons, r_seqAll_length ms]

section
variable {c : Ctx} {M : Mem}

theorem r_optMac_val {z : Cell} (hz : z.val M = 0) : ∀ (l : List (Cell × Cell)) (q : Ptr),
    SegsHold c M q (r_optMac z l q).2 → r_oval M (r_optMac z l q).1 = (l.map fun ab => ab.1.val M * ab.2.val M).sum
  | [], _, _ => by simp [r_optMac, pure_apply, r_oval]
  | ab :: l, q, h => by
    simp only [r_optMac, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [pure_apply]
    simp only [r_oval]
    rw [Lvm.QAcc.macChain_spec _ _ _ h.1, hz, zero_add]

theorem r_divCG_spec {z : Cell} (hz : z.val M = 0) {ρi nρ : Cell} (hnρ : nρ.val M = ρi.val M + 1) {k : Nat}
    {ρa ra : Array FE} (hρ : ρa.getD k 0 = ρi.val M) :
    ∀ (ri : Option Cell), (∀ r, ri = some r → k < 14 ∧ ra.getD k 0 = r.val M) → (ri = none → 14 ≤ k) →
    ∀ (p : Ptr), SegsHold c M p (r_divCG z ρi nρ ri p).2 → ∀ g : Nat → Nat → FE,
      ((r_divCG z ρi nρ ri p).1.map fun x => g x.1 x.2.1 * x.2.2.val M).sum =
        g 0 0 * r_facN ρa ra k false false + g 1 0 * r_facN ρa ra k true false +
          g 0 1 * r_facN ρa ra k false true + g 1 1 * r_facN ρa ra k true true
  | none, _, hn, p, _, g => by
    have hk : ¬ k < 14 := by have := hn rfl; omega
    simp only [r_divCG, pure_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r_facN, eq1,
      hk, ite_false, ite_true, hρ, hnρ, Bool.false_eq_true]
    ring
  | some r, hr, _, p, h, g => by
    obtain ⟨hk, hra⟩ := hr r rfl
    simp only [r_divCG, bind_apply, pure_apply, List.append_nil] at h ⊢
    rw [segsHold_append, segsHold_append, segsHold_append, segsHold_append] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r_facN, eq1, hk, ite_false,
      ite_true, hρ, hra, Bool.false_eq_true]
    rw [mulAdd_spec h2, mulAdd_spec h3, mulAdd_spec h4, mulAdd_spec h5, r_neg1_val h1, hnρ, hz]
    ring

theorem r_sum_filterMap_ite {α : Type} (P : α → Prop) [DecidablePred P] (h : α → Cell × Cell)
    (G : Cell × Cell → FE) : ∀ l : List α,
    ((l.filterMap fun x => if P x then some (h x) else none).map G).sum =
      (l.map fun x => if P x then G (h x) else 0).sum
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons]
    by_cases hx : P x
    · simp only [hx, ite_true, List.map_cons, List.sum_cons, r_sum_filterMap_ite P h G l]
    · simp only [hx, ite_false, List.map_cons, List.sum_cons, r_sum_filterMap_ite P h G l, zero_add]

theorem r_sum_flatMap {α β : Type} (f : α → List β) (G : β → FE) : ∀ l : List α,
    ((l.flatMap f).map G).sum = (l.map fun a => ((f a).map G).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, r_sum_flatMap f G l, List.map_cons, List.sum_cons]

theorem r_divIns_sum (c' : List (Nat × Nat × Cell)) (W : List (Option Cell)) (r' : Nat) :
    ((r_divIns c' W r').map fun ab => ab.1.val M * ab.2.val M).sum =
      ((List.range 17).map fun rem => r_oval M (W.getD rem none) *
        (c'.map fun x => (if (if 17 ≤ 2 * rem + x.1 then 1 else 0) = x.2.1 ∧
          2 * rem + x.1 - 17 * (if 17 ≤ 2 * rem + x.1 then 1 else 0) = r' then 1 else 0) * x.2.2.val M).sum).sum := by
  rw [r_divIns, r_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun rem _ => ?_)
  cases hw : W.getD rem none with
  | none => simp [r_oval]
  | some w =>
    simp only [r_oval]
    refine (r_sum_filterMap_ite _ _ _ c').trans ?_
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    split_ifs <;> simp

theorem r_divStep_rel {z : Cell} (hz : z.val M = 0) {ρi : Cell} {ri : Option Cell} {k : Nat} (hk : k < 19)
    {ρa ra : Array FE} (hρ : ρa.getD k 0 = ρi.val M)
    (hri : ∀ r, ri = some r → k < 14 ∧ ra.getD k 0 = r.val M) (hn : ri = none → 14 ≤ k)
    {V : Array FE} {W : List (Option Cell)} (hVW : r_DRel M V W) {p : Ptr}
    (h : SegsHold c M p (divStep z ρi ri W p).2) : r_DRel M (r_dStep 0 19 ρa ra V k) (divStep z ρi ri W p).1 := by
  rw [r_divStep_eq] at h ⊢
  simp only [bind_apply] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hc := r_divCG_spec hz (r_neg1_val h1) hρ ri hri hn _ h2
  generalize (r_divCG z ρi (neg1 ρi p).1 ri (p.adv (neg1 ρi p).2)).1 = cc at hc h3 ⊢
  refine ⟨by rw [r_seqAll_length, List.length_map, List.length_range], fun j hj => ?_⟩
  have hv := Lvm.QAcc.seqAll_vals (fun r' => r_optMac z (r_divIns cc W r')) (r_oval M)
    (fun r' => ((r_divIns cc W r').map fun ab => ab.1.val M * ab.2.val M).sum)
    (fun k q hq => r_optMac_val hz _ q hq) (List.range 17) _ h3 j (by simpa using hj)
  rw [List.getD_eq_getElem (List.range 17) 0 (by simpa using hj), List.getElem_range] at hv
  rw [show (none : Option Cell) = default from rfl, hv, r_dStep_getD ρa ra V hk hj, r_divIns_sum]
  refine congrArg List.sum (List.map_congr_left fun rem hrem => ?_)
  have hrem' : rem < 17 := List.mem_range.mp hrem
  have hc' := hc fun b q => if (if 17 ≤ 2 * rem + b then 1 else 0) = q ∧
    2 * rem + b - 17 * (if 17 ≤ 2 * rem + b then 1 else 0) = j then 1 else 0
  rw [hc', ← hVW.2 rem hrem']
  by_cases h17 : 17 ≤ 2 * rem <;> by_cases h16 : 17 ≤ 2 * rem + 1 <;>
    simp [r_idxN, r_qN, h17, h16] <;> split_ifs <;> ring

theorem r_divRun_rel {z o : Cell} (hz : z.val M = 0) (ρ r : List Cell) {ρa ra : Array FE}
    (hρa : ∀ k < 19, ρa.getD k 0 = (ρ.getD k z).val M) (hra : ∀ k < 14, ra.getD k 0 = (r.getD k z).val M) :
    ∀ n, n ≤ 19 → ∀ (V : Array FE) (W : List (Option Cell)) (p : Ptr), r_DRel M V W →
      SegsHold c M p (divRun z o ρ r n W p).2 →
        r_DRel M ((List.range n).reverse.foldl (r_dStep 0 19 ρa ra) V) (divRun z o ρ r n W p).1
  | 0, _, V, W, p, hVW, _ => by simpa [divRun, pure_apply] using hVW
  | n + 1, hn, V, W, p, hVW, h => by
    simp only [divRun, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]
    refine r_divRun_rel hz ρ r hρa hra n (by omega) _ _ _ (r_divStep_rel hz (by omega) (hρa n (by omega))
      (fun r' hr' => ?_) (fun hn' => ?_) hVW h.1) h.2
    · by_cases h14 : n < 14
      · rw [ite_eq_left h14, Option.some.injEq] at hr'
        exact ⟨h14, hr' ▸ hra n h14⟩
      · rw [ite_eq_right h14] at hr'; exact absurd hr' (by simp)
    · by_cases h14 : n < 14
      · rw [ite_eq_left h14] at hn'; exact absurd hn' (by simp)
      · omega

end
/-- A run of `0` bits of `c`. -/
theorem r_geRun_zero (c : Nat) (t : Nat → Bool → FE) : ∀ (ks : List Nat) (a b : FE),
    (∀ k ∈ ks, c.testBit k = false) → ks.foldl (r_geStep c t) (a, b) =
      (a * (ks.map fun k => t k false).prod,
        (a + b) * (ks.map fun k => t k false + t k true).prod - a * (ks.map fun k => t k false).prod)
  | [], a, b, _ => by simp
  | k :: ks, a, b, h => by
    have hk : c.testBit k = false := h k List.mem_cons_self
    rw [List.foldl_cons]
    simp only [r_geStep, hk, Bool.false_eq_true, ite_false]
    rw [r_geRun_zero c t ks _ _ fun k' hk' => h k' (List.mem_cons_of_mem _ hk')]
    simp only [List.map_cons, List.prod_cons, Prod.mk.injEq]
    constructor <;> ring

/-- **`geKern` at the stream's end** (`c = 17·2^14 = 2^18 + 2^14`): `Π_{k<14} t_k · t₁₈(1) ·
(Π_{14≤k<18} t_k + Π_{14≤k<18} t_k(0))`, `t_k = t_k(0) + t_k(1)` (characteristic 2). -/
theorem r_geKern_tail (t : Nat → Bool → FE) :
    ((List.range 19).reverse.foldl (r_geStep 278528 t) (1, 0)).1 +
      ((List.range 19).reverse.foldl (r_geStep 278528 t) (1, 0)).2 =
    ((List.range 14).map fun k => t k false + t k true).prod * t 18 true *
      ((t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
        (t 17 false + t 17 true) + t 14 false * t 15 false * t 16 false * t 17 false) := by
  have e : (List.range 19).reverse = [18, 17, 16, 15, 14] ++ (List.range 14).reverse := by decide
  have hz : ∀ k ∈ (List.range 14).reverse, Nat.testBit 278528 k = false := by decide
  rw [e, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, r_geStep,
    show Nat.testBit 278528 18 = true by decide, show Nat.testBit 278528 17 = false by decide,
    show Nat.testBit 278528 16 = false by decide, show Nat.testBit 278528 15 = false by decide,
    show Nat.testBit 278528 14 = true by decide, ite_true, ite_false, Bool.false_eq_true]
  rw [r_geRun_zero _ _ _ _ _ hz, List.map_reverse, List.prod_reverse, List.map_reverse, List.prod_reverse]
  generalize ((List.range 14).map fun k => t k false).prod = P0
  generalize ((List.range 14).map fun k => t k false + t k true).prod = PF
  have h2 : (2 : FE) = 0 := CharTwo.two_eq_zero
  linear_combination (-(t 18 true) * PF * (t 14 false * t 15 false * t 16 false * t 17 false)) * h2

section
variable {c : Ctx} {M : Mem}

theorem r_add_val {a b : Cell} {p : Ptr} (h : SegsHold c M p (add a b p).2) :
    (add a b p).1.val M = a.val M + b.val M := by
  have := lin_spec h
  rw [ofK_one, one_mul, ofK_zero, add_zero] at this
  exact this

theorem r_prodG_val {z : Cell} (hz : z.val M = 0) : ∀ (l : List Cell) (acc : Cell) (p : Ptr),
    SegsHold c M p ((l.foldlM (fun acc x => mulAdd .E acc x z) acc : BM Cell) p).2 →
      ((l.foldlM (fun acc x => mulAdd .E acc x z) acc : BM Cell) p).1.val M =
        acc.val M * (l.map (Cell.val M)).prod
  | [], acc, p, _ => by simp [pure_apply]
  | x :: l, acc, p, h => by
    rw [List.foldlM_cons, hold_bind] at h
    rw [List.foldlM_cons, bind_apply, r_prodG_val hz l _ _ h.2, mulAdd_spec h.1, hz, add_zero,
      List.map_cons, List.prod_cons, mul_assoc]

theorem r_getD_vs {z : Cell} (hz : z.val M = 0) (l : List Cell) (k : Nat) :
    (vs M l).toArray.getD k 0 = (l.getD k z).val M := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, vs, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[k]? <;> simp [hz]

theorem r_map_dt {α : Type} [Inhabited α] (ts : List α) (f : α → FE) (g : Nat → FE) (n m : Nat)
    (hl : n + m ≤ ts.length) (hv : ∀ i, n ≤ i → i < n + m → f (ts.getD i default) = g i) :
    ((ts.drop n).take m).map f = (List.range m).map fun i => g (n + i) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [← hv (n + i) (by omega) (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem r_forN_length {α : Type} (n : Nat) (f : Nat → BM α) (p : Ptr) : (forN n f p).1.length = n := by
  rw [forN, r_seqAll_length, List.length_map, List.length_range]

theorem r_tail_facts {z : Cell} {t : Nat → Bool → FE} (ts : List (Cell × Cell × Cell))
    (hlen : ts.length = 19)
    (v0 : ∀ i < 19, (ts.getD i default).1.val M = t i false)
    (v1 : ∀ i < 19, (ts.getD i default).2.1.val M = t i true)
    (v2 : ∀ i < 19, (ts.getD i default).2.2.val M = t i false + t i true) :
    (((ts.take 14).map (fun x => x.2.2)).map (Cell.val M)).prod =
        ((List.range 14).map fun k => t k false + t k true).prod ∧
      ((((ts.drop 14).take 4).map (fun x => x.2.2)).map (Cell.val M)).prod =
        (t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
          (t 17 false + t 17 true) ∧
      ((((ts.drop 14).take 4).map (fun x => x.1)).map (Cell.val M)).prod =
        t 14 false * t 15 false * t 16 false * t 17 false ∧
      (ts.getD 18 (z, z, z)).2.1.val M = t 18 true := by
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := r_map_dt ts (fun x => x.2.2.val M) (fun i => t i false + t i true) 0 14 (by omega)
      (fun i _ hi => v2 i (by omega))
    rw [List.drop_zero] at this
    rw [List.map_map, show (Cell.val M ∘ fun x : Cell × Cell × Cell => x.2.2) = (fun x => x.2.2.val M) from rfl,
      this]
    simp only [Nat.zero_add]
  · rw [List.map_map, show (Cell.val M ∘ fun x : Cell × Cell × Cell => x.2.2) = (fun x => x.2.2.val M) from rfl,
      r_map_dt ts (fun x => x.2.2.val M) (fun i => t i false + t i true) 14 4 (by omega)
        (fun i _ hi => v2 i (by omega)), h4]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  · rw [List.map_map, show (Cell.val M ∘ fun x : Cell × Cell × Cell => x.1) = (fun x => x.1.val M) from rfl,
      r_map_dt ts (fun x => x.1.val M) (fun i => t i false) 14 4 (by omega)
        (fun i _ hi => v0 i (by omega)), h4]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  · have := v1 18 (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at this ⊢
    exact this

/-- `tailG`'s per-coordinate step. -/
def r_tStep (z : Cell) (ρ r : List Cell) (i : Nat) : BM (Cell × Cell × Cell) := do
  let a := ρ.getD i z
  let b := r.getD i z
  let na ← neg1 a
  let nb ← neg1 b
  let d0 ← mulAdd .E na nb z
  let d1 ← mulAdd .E a b z
  let t ← add d0 d1
  pure (d0, d1, t)

/-- `tailG` after its steps. -/
def r_tRest (z o : Cell) (ts : List (Cell × Cell × Cell)) : BM Cell := do
  let lo ← Lvm.QAcc.macChain [] o
  let prodG (l : List Cell) : BM Cell := l.foldlM (fun acc x => mulAdd .E acc x z) lo
  let pT ← prodG ((ts.take 14).map (·.2.2))
  let pM ← prodG (((ts.drop 14).take 4).map (·.2.2))
  let pZ ← prodG (((ts.drop 14).take 4).map (·.1))
  let df ← add pM pZ
  let h ← mulAdd .E pT (ts.getD 18 (z, z, z)).2.1 z
  mulAdd .E h df z

theorem r_bind_fst {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

theorem r_tailG_eq (z o : Cell) (ρ r : List Cell) :
    Lvm.QTyped.tailG z o ρ r = forN 19 (r_tStep z ρ r) >>= r_tRest z o := rfl

theorem r_tStep_val {z : Cell} (hz : z.val M = 0) (ρ r : List Cell) (t : Nat → Bool → FE)
    (ht : ∀ k b, t k b = eq1 ((ρ.getD k z).val M) b * eq1 ((r.getD k z).val M) b) (k : Nat) (q : Ptr)
    (hq : SegsHold c M q (r_tStep z ρ r k q).2) :
    (r_tStep z ρ r k q).1.1.val M = t k false ∧ (r_tStep z ρ r k q).1.2.1.val M = t k true ∧
      (r_tStep z ρ r k q).1.2.2.val M = t k false + t k true := by
  simp only [r_tStep, bind_apply, pure_apply, segsHold_append] at hq ⊢
  have e0 : (mulAdd .E (neg1 (ρ.getD k z) q).1 (neg1 (r.getD k z) (q.adv (neg1 (ρ.getD k z) q).2)).1 z
      ((q.adv (neg1 (ρ.getD k z) q).2).adv (neg1 (r.getD k z) (q.adv (neg1 (ρ.getD k z) q).2)).2)).1.val M =
      t k false := by
    rw [mulAdd_spec hq.2.2.1, r_neg1_val hq.1, r_neg1_val hq.2.1, hz, add_zero, ht]
    simp only [eq1, Bool.false_eq_true, ite_false]; ring
  have e1 : ∀ q', SegsHold c M q' (mulAdd .E (ρ.getD k z) (r.getD k z) z q').2 →
      (mulAdd .E (ρ.getD k z) (r.getD k z) z q').1.val M = t k true := by
    intro q' h'
    rw [mulAdd_spec h', hz, add_zero, ht]
    simp only [eq1, ite_true]
  refine ⟨e0, e1 _ hq.2.2.2.1, ?_⟩
  rw [r_add_val hq.2.2.2.2.1, e0, e1 _ hq.2.2.2.1]

theorem r_tRest_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {t : Nat → Bool → FE}
    (ts : List (Cell × Cell × Cell)) (hlen : ts.length = 19)
    (v0 : ∀ i < 19, (ts.getD i default).1.val M = t i false)
    (v1 : ∀ i < 19, (ts.getD i default).2.1.val M = t i true)
    (v2 : ∀ i < 19, (ts.getD i default).2.2.val M = t i false + t i true)
    (p : Ptr) (h : SegsHold c M p (r_tRest z o ts p).2) :
    (r_tRest z o ts p).1.val M =
      ((List.range 14).map fun k => t k false + t k true).prod * t 18 true *
        ((t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
          (t 17 false + t 17 true) + t 14 false * t 15 false * t 16 false * t 17 false) := by
  simp only [r_tRest, bind_apply] at h ⊢
  simp only [segsHold_append] at h
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := r_tail_facts ts hlen v0 v1 v2
  rw [mulAdd_spec h8, mulAdd_spec h7, r_add_val h6, r_prodG_val hz _ _ _ h3, r_prodG_val hz _ _ _ h4,
    r_prodG_val hz _ _ _ h5, Lvm.QAcc.macChain_spec _ _ _ h2, e1, e2, e3, e4, hz, ho]
  simp only [List.map_nil, List.sum_nil, add_zero, one_mul]

theorem r_tailG_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (ρ r : List Cell)
    (t : Nat → Bool → FE) (ht : ∀ k b, t k b = eq1 ((ρ.getD k z).val M) b * eq1 ((r.getD k z).val M) b)
    (p : Ptr) (h : SegsHold c M p (Lvm.QTyped.tailG z o ρ r p).2) :
    (Lvm.QTyped.tailG z o ρ r p).1.val M =
      ((List.range 14).map fun k => t k false + t k true).prod * t 18 true *
        ((t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
          (t 17 false + t 17 true) + t 14 false * t 15 false * t 16 false * t 17 false) := by
  rw [r_tailG_eq, hold_bind] at h
  rw [r_tailG_eq, r_bind_fst]
  have hf := r_tStep_val (c := c) hz ρ r t ht
  have v0 := Lvm.QAcc.forN_vals (c := c) (M := M) (n := 19) (f := r_tStep z ρ r) (p := p)
    (fun x : Cell × Cell × Cell => x.1.val M) (fun i => t i false) (fun k q hq => (hf k q hq).1) h.1
  have v1 := Lvm.QAcc.forN_vals (c := c) (M := M) (n := 19) (f := r_tStep z ρ r) (p := p)
    (fun x : Cell × Cell × Cell => x.2.1.val M) (fun i => t i true) (fun k q hq => (hf k q hq).2.1) h.1
  have v2 := Lvm.QAcc.forN_vals (c := c) (M := M) (n := 19) (f := r_tStep z ρ r) (p := p)
    (fun x : Cell × Cell × Cell => x.2.2.val M) (fun i => t i false + t i true)
    (fun k q hq => (hf k q hq).2.2) h.1
  have hl := r_forN_length 19 (r_tStep z ρ r) p
  obtain ⟨-, h⟩ := h
  generalize p.adv (forN 19 (r_tStep z ρ r) p).2 = p' at h ⊢
  generalize (forN 19 (r_tStep z ρ r) p).1 = ts at h hl v0 v1 v2 ⊢
  exact r_tRest_val hz ho ts hl v0 v1 v2 p' h

end

section
variable {c : Ctx} {M : Mem}

theorem r_eqAtF_eqW : ∀ (r : List FE) (w : Nat), eqAtF r w = Loop.eqW r w
  | [], _ => rfl
  | a :: r, w => by
    rw [eqAtF, Loop.eqW, r_eqAtF_eqW r (w / 2), sub_eq_add_neg, CharTwo.neg_eq]

theorem r_foldl_add (f : Nat → FE) : ∀ (l : List Nat) (a : FE),
    l.foldl (fun acc x => acc + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, r_foldl_add f l, List.map_cons, List.sum_cons, add_assoc]

theorem r_oval_getD {z : Cell} (hz : z.val M = 0) (w : Option Cell) : (w.getD z).val M = r_oval M w := by
  cases w <;> simp [r_oval, hz]

theorem r_drel_init {o : Cell} (ho : o.val M = 1) :
    r_DRel M ((Array.replicate 17 (0 : FE)).set! 0 1) ((List.range 17).map fun i => if i = 0 then some o else none) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rcases j with _ | j
  · simp [r_oval, ho]
  · simp [r_oval, hj]

end

theorem r_scSpec_len (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (eqs : List (Option FE)),
    (Q1.scSpec v count p claim eqs).1.length = eqs.length
  | _, _, [] => rfl
  | p, claim, e :: es => by simp only [Q1.scSpec, List.length_cons, r_scSpec_len v count _ _ es]

theorem r_getPtr_apply (p : Ptr) : getPtr p = (p, []) := rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The relayout's kernel in the circuit is V_S's** (`relayKernF`), on regions that are V_S's. -/
theorem relayKernG_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E)
    {Td : TData} {N : TNat} (htd : TdOk Td N) (ry r : List Cell) (hry : ry.length = 21) (hr : r.length = 19)
    (hryE : ∀ x ∈ ry, x.ty = .E) (hrE : ∀ x ∈ r, x.ty = .E) (q : Ptr)
    (h : SegsHold c M q (relayKernG z o Td ry r q).2) :
    (relayKernG z o Td ry r q).1.val M = TypedV.relayKernF N (vs M ry) (vs M r) := by
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp at hoE; subst hoE; rfl
  have hal : ∀ i, (r.getD (14 + i) z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases hx : r[14 + i]? with
    | none => exact hzE
    | some y => exact hrE y (List.mem_of_getElem? hx)
  have hvt : ∀ (l : List Cell) (n : Nat), (vs M l).take n = vs M (l.take n) := fun l n => by
    simp [vs, List.map_take]
  have hρa : ∀ k < 19, ((vs M ry).take 19).toArray.getD k 0 = ((ry.take 19).getD k z).val M := fun k _ => by
    rw [hvt, r_getD_vs hz]
  have hra : ∀ k < 14, ((vs M r).take 14).toArray.getD k 0 = (r.getD k z).val M := fun k hk => by
    rw [hvt, r_getD_vs hz, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hk]
  simp only [relayKernG, regSelG, hold_bind] at h
  simp only [relayKernG, regSelG, r_bind_fst]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hW := r_divRun_rel hz (ry.take 19) r hρa hra 19 le_rfl _ _ _ (r_drel_init ho) h2
  generalize (divRun z o (ry.take 19) r 19 _ _).1 = W at hW h3 h4 h5 h6 ⊢
  have hWl : W.length = 17 := hW.1
  have htt : ∀ k b, (fun k b => eq1 (((vs M ry).take 19).toArray.getD k 0) b * eq1 ((vs M r).toArray.getD k 0) b) k b =
      eq1 (((ry.take 19).getD k z).val M) b * eq1 ((r.getD k z).val M) b := fun k b => by
    simp only; rw [hvt, r_getD_vs hz, r_getD_vs hz]
  rw [mulAdd_spec h6, r_add_val h5, r_eqConstG_val hz ho _ _ _ h1,
    Lvm.QAcc.eqDot_spec hal (by norm_num) (by rw [List.length_map, hWl]; norm_num) hz hone h3,
    r_tailG_val hz ho _ _ _ htt _ h4, hz, add_zero]
  simp only [TypedV.relayKernF, htd.sflat, List.foldl_cons, List.foldl_nil, zero_add]
  have hrd : List.drop 19 (vs M r) = [] := List.drop_eq_nil_of_le (by simp [vs, hr])
  have hrt : List.take 19 (vs M r) = vs M r := List.take_of_length_le (by simp [vs, hr])
  have hd5 : (List.range 5).map (fun i => (r.getD (14 + i) z).val M) = (vs M r).drop 14 := by
    apply List.ext_getElem
    · simp [vs, hr]
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_drop, vs]
      rw [List.getD_eq_getElem _ _ (by omega)]
  rw [ite_eq_right (by decide), hrd, hrt, show TypedV.sPos - min TypedV.sPos 0 = 278528 from rfl, r_geKern_eq,
    r_geKern_tail, r_recRowBits_eq, show eqAtF [] (0 >>> 19) = 1 from rfl, one_mul]
  congr 1
  · simp [TypedV.hiW, vs, List.map_drop]
  · congr 1
    rw [r_divKern_eq, r_foldl_add, zero_add, Lvm.QAcc.sum_map_range, List.length_map, hWl]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hd5, ← r_eqAtF_eqW, List.getD_eq_getElem _ _ (by simp [hWl]; omega), List.getElem_map, r_oval_getD hz,
      ← List.getD_eq_getElem _ none (by omega), ← hW.2 k hk, mul_comm]

/-- **The relayout replayed**: wherever `relayG`'s rows hold and assert (gate on), `dRelayT` at `r_y` from `v_S`
from any state at `rRP P` with `ok` keeps `ok`, ends at `aP P`; `r` and `v_R` are the output's cells' values. -/
theorem relayG_replays (hS : Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {P : Nat} (hP : P % 8 = 0) (hT : aP P + 40 ≤ 8 * T) (ry : List Cell) (hry : ry.length = 21)
    (hryE : ∀ x ∈ ry, x.ty = .E) (vS : Cell) (ptr : Ptr) (hp : 1 ≤ ptr.e) :
    Replays c M sig (TypedV.dRelayT N (vs M ry) (vS.val M)) (relayG z o g Td P ry vS) ptr (rRP P) (aP P)
      fun v t => v.1 = vs M t.1 ∧ v.2 = t.2.val M ∧ t.1.length = 19 ∧ (∀ x ∈ t.1, x.ty = .E) := by
  intro hok s hs hsok
  have hR8 : rRP P % 8 = 0 := by simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, tX, tY]; omega
  have hA : aP P = rRP P + 2304 := by simp only [aP, rVP, tR]
  have hV : rVP P = rRP P + 2280 := by simp only [rVP, tR]
  have hs' : s.ent + s.msg = rRP P := hs
  unfold relayG at hok ⊢
  obtain ⟨-, hok⟩ := okb hok
  simp only [r_getPtr_apply, Ptr.adv_nil] at hok
  obtain ⟨hF, hok⟩ := okb hok
  obtain ⟨hVl, hok⟩ := okb hok
  obtain ⟨hK, hok⟩ := okb hok
  obtain ⟨hM, hok⟩ := okb hok
  obtain ⟨hAs, -⟩ := okb hok
  simp only [r_bind_fst, r_getPtr_apply, Ptr.adv_nil, pure_apply]
  have hsc := QB.scRunP3_eq (binParts tR) (rRP P / 8) vS ptr hF.1 sig ⟨8 * (rRP P / 8), 0, true⟩ rfl rfl
    (fun j _ h2 => by rw [nRounds_binParts] at h2; exact hS j (by simp only [tR] at h2; omega))
  rw [nRounds_binParts, Q1.sumcheck_run sig 3 (by decide)] at hsc
  simp only [show 8 * (rRP P / 8) + 0 = rRP P by omega] at hsc
  have hvR := Lvm.QAcc.ldE_feAt hS (q := (rVP P + 40) / 8) (by omega) hVl.1
  have hrr : ∀ x ∈ (List.range tR).map (fun i => ec (ptr.e + 3 + 6 * i)), x.ty = .E := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; rfl
  have hk := relayKernG_spec hz ho hzE hoE htd ry _ hry (by simp) hryE hrr _ hK.1
  have hpr := mulAdd_spec hM.1
  have heq := Lvm.QAcc.assertEqE_spec hAs hg
  rw [hpr, hk, hvR, hz, add_zero, hsc.1] at heq
  rw [show feAt sig (8 * ((rVP P + 40) / 8)) = feAt sig (rRP P + 2280 + 40 + 0) from congrArg _ (by omega)]
    at heq hvR
  unfold TypedV.dRelayT
  simp only [Q1.bind_run, Q1.sumcheck_run sig 3 (by decide : 2 ≤ 3), Q1.readE_run, require_run', Q1.pure_run]
  have hst : Q1.scState 3 s (List.replicate TypedV.relayRoundsN none) = ⟨rRP P + 2280, 0, s.ok⟩ := by
    rw [← hs']; rfl
  rw [hst, hs']
  have hl := r_scSpec_len (feAt sig) 3 (rRP P) (vS.val M) (List.replicate tR none)
  rw [List.length_replicate] at hl
  have hch := hsc.2
  generalize Q1.scSpec (feAt sig) 3 (rRP P) (vS.val M) (List.replicate tR none) = SC at heq hl hch ⊢
  have hrv : SC.1 = vs M ((List.range tR).map fun i => ec (ptr.e + 3 + 6 * i)) := by
    apply List.ext_getElem
    · simp [vs, hl]
    · intro i h1 h2
      rw [← List.getD_eq_getElem _ 0 h1, ← hch i (by omega)]
      simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
      congr 1; omega
  dsimp only
  refine ⟨?_, ?_, hrv, hvR.symm, by simp, hrr⟩
  · rw [hsok, heq, hrv]; simp
  · simp only [pos]; omega

end

end Lvm.Har
