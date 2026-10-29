-- New for `flock-recursive` (BLUEPRINT A.11, stage S-E3; track L-circ).
import FRVIRTemplates

/-!
# Replay templates over `eq` tables: `targetS`, `slotW`, `maskRows`

BLUEPRINT A.11. `eqTblG` builds `FRMLE.eqTable` over forms, one product per table entry of the
coordinate below (`eqTblG_ev`); the templates mirror `implC`'s `targetSLeafI` (the leaf kinds'
`targetS`), `slotWI` and `FRVIR.maskRows`.
-/

namespace FR
namespace Tpl
open Circ

variable {e : Env}

/-! ## `eq` tables over forms (`FRMLE.eqTable`'s order: the first coordinate is the low bit) -/

theorem getElem_flatMap_pair {α β : Type*} (f g : α → β) :
    ∀ (l : List α) (u : ℕ) (h : u < (l.flatMap fun x => [f x, g x]).length),
    (l.flatMap fun x => [f x, g x])[u] =
      if u % 2 = 0 then f (l[u / 2]'(by simp at h; omega)) else g (l[u / 2]'(by simp at h; omega))
  | [], u, h => by simp at h
  | x :: l, u, h => by
    rcases u with _ | _ | u
    · simp
    · simp
    · have := getElem_flatMap_pair f g l u (by simp at h ⊢; omega)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ] at this ⊢
      rw [this]
      simp only [show (u + 2) % 2 = u % 2 by omega, show (u + 2) / 2 = u / 2 + 1 by omega,
        List.getElem_cons_succ]

theorem length_flatMap_two {α β : Type*} (f g : α → β) (l : List α) :
    (l.flatMap fun x => [f x, g x]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]; ring

theorem eqTable_toList_cons {R : Type*} [CommRing R] (c : R) (r : List R) :
    (eqTable (c :: r)).toList = (eqTable r).toList.flatMap fun x => [x * (1 - c), x * c] := by
  apply List.ext_getElem (by rw [length_flatMap_two]; simp [eqTable])
  intro u h₁ h₂
  rw [getElem_flatMap_pair (fun x => x * (1 - c)) (fun x => x * c)]
  simp only [eqTable, Array.getElem_toList, Array.getElem_ofFn]
  rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h]

theorem flatMap_range_getD {β : Type*} (l : List F) (f : F → List β) :
    l.flatMap f = (List.range l.length).flatMap fun i => f (l.getD i 0) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, ih,
      Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]

theorem getD_map_ev (l : List LinT) (i : ℕ) :
    (l.getD i []).ev e = (l.map (LinT.ev e)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- **`eqTable` over forms**: per coordinate (the last first), one product per entry (the previous
table's entries read from an array: `List.getD` per entry was quadratic in the table, INIT). -/
def eqTblG : List LinT → ℕ → List Gate × List LinT
  | [], _ => ([], [C 1])
  | c :: cs, k =>
    let r := eqTblG cs k
    let k' := k + nlocs r.1
    let a := r.2.toArray
    (r.1 ++ mulsG r.2.length (fun i => a.getD i []) (fun _ => c),
     (List.range r.2.length).flatMap fun i => [a.getD i [] ++ sc (-1) (L (k' + i)), L (k' + i)])

theorem toArray_getD {α : Type*} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem eqTblG_nlocs : ∀ (cs : List LinT) (k : ℕ), nlocs (eqTblG cs k).1 + 1 = 2 ^ cs.length ∧
    (eqTblG cs k).2.length = 2 ^ cs.length
  | [], _ => ⟨rfl, rfl⟩
  | c :: cs, k => by
    obtain ⟨h1, h2⟩ := eqTblG_nlocs cs k
    have hm := mulsG_nlocs (eqTblG cs k).2.length (fun i => (eqTblG cs k).2.getD i []) (fun _ => c)
    refine ⟨?_, ?_⟩
    · simp only [eqTblG, toArray_getD, nlocs, List.map_append, List.sum_append] at h1 hm ⊢
      rw [hm, h2, List.length_cons, pow_succ]; omega
    · simp only [eqTblG, toArray_getD]
      rw [length_flatMap_two, List.length_range, h2, List.length_cons, pow_succ]; ring

theorem eqTblG_ev (h1 : e.one = 1) : ∀ (cs : List LinT) (k : ℕ), Eqns e (eqTblG cs k).1 k →
    (eqTblG cs k).2.map (LinT.ev e) = (eqTable (cs.map (LinT.ev e))).toList
  | [], _, _ => by simp [eqTblG, eqTable, h1]
  | c :: cs, k, h => by
    simp only [eqTblG, toArray_getD, Eqns.append] at h
    have ih := eqTblG_ev h1 cs k h.1
    have hm := mulsG_eqns h.2
    rw [List.map_cons, eqTable_toList_cons, ← ih, flatMap_range_getD, List.length_map]
    simp only [eqTblG, toArray_getD, List.map_flatMap]
    refine List.flatMap_congr fun i hi => ?_
    have hi := List.mem_range.1 hi
    rw [← getD_map_ev]
    simp only [List.map_cons, List.map_nil, ev_append, ev_sc, ev_L, hm i hi]
    simp only [List.cons.injEq, and_true]
    ring

theorem nlocs_append (a b : List Gate) : nlocs (a ++ b) = nlocs a + nlocs b := by
  simp [nlocs]

/-! ## `targetS` of the leaf kinds (`Impl.targetSLeafI`) -/

/-- The 8 coordinates `zLo r` as forms: the pinned `pr₀ … pr₆` (constants), then `r₀`. -/
def zLoT (pr : Fin 7 → F) (n : ℕ) : List LinT :=
  List.ofFn fun l : Fin 8 => if h : l.val < 7 then C (pr ⟨l, h⟩) else if 0 < n then I 0 else []

/-- The template over constant pins `pr` and coefficients `cf` (generic, so that no proof sees the
constants). -/
def tgtT (pr : Fin 7 → F) (cf : ℕ → F) (n : ℕ) : Tpl :=
  let g := eqTblG (zLoT pr n) 0
  ⟨g.1, (List.range 64).map fun σ => (List.range 256).flatMap fun hi => sc (cf (σ + 64 * hi)) (g.2.getD hi [])⟩

/-- **`targetS`** for `r : AF n`: the table over `zLo r` (255 products), each output a constant
combination of its entries. -/
def tplTargetS (n : ℕ) : Tpl := tgtT pinnedRho (fun p => Impl.chainTab.getD p 0) n

theorem ev_flatMap {α : Type*} (l : List α) (f : α → LinT) :
    LinT.ev e (l.flatMap f) = (l.map fun x => (f x).ev e).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem sumTo_list {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    sumTo n g = ((List.range n).map g).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo, Nat.fold_succ, ← sumTo, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem tgtT_ok (h1 : e.one = 1) (pr : Fin 7 → F) (cf : ℕ → F) {r : Array F} (hi : InpIs e r.toList)
    (h : Eqns e (tgtT pr cf r.size).gates 0) :
    (tgtT pr cf r.size).outs.map (LinT.ev e) = encV (.af (Array.ofFn (n := 64) fun σ =>
      sumTo 256 fun hi => cf (σ + 64 * hi) *
        (eqTable (List.ofFn fun l : Fin 8 => if h : l.val < 7 then pr ⟨l, h⟩ else r.getD 0 0)).getD hi 0)) := by
  have hz : (zLoT pr r.size).map (LinT.ev e) =
      List.ofFn fun l : Fin 8 => if h : l.val < 7 then pr ⟨l, h⟩ else r.getD 0 0 := by
    refine List.ext_getElem (by simp [zLoT]) fun l h₁ h₂ => ?_
    simp only [zLoT, List.getElem_map, List.getElem_ofFn]
    by_cases hl : l < 7
    · simp only [hl, dite_true, ev_C, h1, mul_one]
    · by_cases hn : 0 < r.size
      · simp only [hl, dite_false, hn, if_true, ev_I]; rw [hi, arr_getD]
      · simp only [hl, dite_false, hn, if_false, ev_nil]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
  have ht := eqTblG_ev h1 _ 0 h
  rw [hz] at ht
  simp only [tgtT, encV, Array.toList_ofFn, List.map_map]
  refine List.ext_getElem (by simp) fun σ h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_ofFn,
    ev_flatMap, ev_sc, sumTo_list]
  refine congrArg List.sum (List.map_congr_left fun hi _ => ?_)
  rw [getD_map_ev, ht, arr_getD]

theorem tplTargetS_ok (h1 : e.one = 1) {r : Array F} (hi : InpIs e r.toList)
    (h : Eqns e (tplTargetS r.size).gates 0) :
    (tplTargetS r.size).outs.map (LinT.ev e) = encV (.af (Impl.targetSLeafI r)) :=
  tgtT_ok h1 pinnedRho (fun p => Impl.chainTab.getD p 0) hi h

/-! ## `slotW` (`Impl.slotWI`) -/

/-- Ten coordinates of an `AF n` input at offset `o` (missing ones `0`). -/
def ptT (o n : ℕ) : List LinT := List.ofFn fun l : Fin 10 => if l.val < n then I (o + l) else []

/-- **`slotW`** of slot map `s` for `θ : AF n`, `r : AF m`: two tables (1023 products each), then
the 256 products and their sum. -/
def tplSlotW (s n m : ℕ) : Tpl :=
  let g₁ := eqTblG (ptT 0 n) 0
  let g₂ := eqTblG (ptT n m) (nlocs g₁.1)
  let k := nlocs g₁.1 + nlocs g₂.1
  ⟨g₁.1 ++ g₂.1 ++ mulsG 256 (fun σ => g₁.2.getD σ []) (fun σ => g₂.2.getD (Impl.slotBase s + σ) []),
   [(List.range 256).flatMap fun σ => L (k + σ)]⟩

theorem ptT_ev {xs ys : List F} (hi : InpIs e (xs ++ ys)) :
    (ptT 0 xs.length).map (LinT.ev e) = List.ofFn (fun l : Fin 10 => xs.getD l 0) ∧
    (ptT xs.length ys.length).map (LinT.ev e) = List.ofFn (fun l : Fin 10 => ys.getD l 0) := by
  constructor <;> refine List.ext_getElem (by simp [ptT]) fun l h₁ h₂ => ?_ <;>
    simp only [ptT, List.getElem_map, List.getElem_ofFn]
  · by_cases hl : l < xs.length
    · simp only [hl, if_true, ev_I, zero_add]; rw [hi, getD_append_left hl]
    · simp only [hl, if_false, ev_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · by_cases hl : l < ys.length
    · simp only [hl, if_true, ev_I]; rw [hi, getD_append_right]
    · simp only [hl, if_false, ev_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem tbl_getD {cs : List LinT} {k : ℕ} {xs : List F}
    (h : (eqTblG cs k).2.map (LinT.ev e) = (eqTable xs).toList) (i : ℕ) :
    ((eqTblG cs k).2.getD i []).ev e = (eqTable xs).getD i 0 := by
  rw [getD_map_ev, h, arr_getD]

theorem ofFn_ptA (a : Array F) : List.ofFn (Impl.ptA 10 a) = List.ofFn fun l : Fin 10 => a.getD l 0 :=
  rfl

theorem tplSlotW_ok (h1 : e.one = 1) (s : ℕ) {θ r : Array F} (hi : InpIs e (θ.toList ++ r.toList))
    (h : Eqns e (tplSlotW s θ.size r.size).gates 0) :
    (tplSlotW s θ.size r.size).outs.map (LinT.ev e) = encV (.f (Impl.slotWI s θ r)) := by
  simp only [tplSlotW, Eqns.append, zero_add, nlocs_append] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  have hp := ptT_ev hi
  simp only [Array.length_toList] at hp
  have t₁ := eqTblG_ev h1 _ _ h₁; have t₂ := eqTblG_ev h1 _ _ h₂
  rw [hp.1] at t₁; rw [hp.2] at t₂
  have hm := mulsG_eqns h₃
  simp only [tplSlotW, List.map_cons, List.map_nil, encV, Impl.slotWI, List.cons.injEq, and_true,
    ev_flatMap, ev_L, sumTo_list]
  refine congrArg List.sum (List.map_congr_left fun σ hσ => ?_)
  rw [hm σ (List.mem_range.1 hσ), tbl_getD t₁, tbl_getD t₂, ofFn_ptA, ofFn_ptA]
  simp only [arr_getD]

/-! ## `maskRows` (`FRVIR.maskRows`) -/

theorem ev_flatten (l : List LinT) : LinT.ev e l.flatten = (l.map (LinT.ev e)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- The mask of row `k` as a form over the `n` kind weights. -/
def maskT (n k : ℕ) : LinT :=
  ((blockKinds.zipIdx.filter fun p => !isZeroRow p.1 k).map fun p => if p.2 < n then I p.2 else []).flatten

/-- **`maskRows`** for `kindW : AF n`, `rowW : AF m` (inputs in that order): one product per row. -/
def tplMaskRows (n m : ℕ) : Tpl :=
  ⟨mulsG m (fun k => I (n + k)) (maskT n), (List.range m).map L⟩

theorem tplMaskRows_ok {kw rw : Array F} (hi : InpIs e (kw.toList ++ rw.toList))
    (h : Eqns e (tplMaskRows kw.size rw.size).gates 0) :
    (tplMaskRows kw.size rw.size).outs.map (LinT.ev e) = encV (.af (maskRows kw rw)) := by
  have hm := mulsG_eqns h
  simp only [tplMaskRows, encV, List.map_map]
  refine List.ext_getElem (by simp [maskRows]) fun k h₁ h₂ => ?_
  have hk : k < rw.size := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, ev_L, maskRows_eq, maskOf,
    Array.getElem_toList, Array.getElem_mapIdx]
  have hk' := hm k hk
  rw [zero_add] at hk'
  rw [hk']
  congr 1
  · rw [ev_I, hi, ← Array.length_toList, getD_append_right, arr_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hk]; rfl
  · rw [maskT, ev_flatten, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    by_cases hp : p.2 < kw.size
    · simp only [hp, if_true, ev_I]; rw [hi, getD_append_left (by simpa using hp), arr_getD]
    · simp only [hp, if_false, ev_nil]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

end Tpl
end FR
