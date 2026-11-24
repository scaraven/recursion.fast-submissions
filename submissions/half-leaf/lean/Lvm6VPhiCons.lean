-- New for lvm6 (ST-4, construct, don't check): the class table from rows and any hints, correct for every hint.
import Lvm6VPhiRows

/-!
# The class table constructed from the rows (ST-4)

No start-up check: the table is right for **every** hint list, bad hints cost speed only.

* A class hint is accepted at run time when its row range is in order and inside `[0, N)` and its class (template
  of instance `0`, kinds from instances `0` and `1`, `tplOf`) fits (`clsAccB`: `CTpl.okB`, the slot bound, the
  template in bounds); otherwise its rows stay with the rest (`accH`).
* Every hinted instance's row is the template at its instance **plus its difference** (`diffZ`): positionwise, a
  free position or a mismatch gives the row's entry and the template's with coefficient `-c`. **`diffZ_sum`**: any
  row is its template part plus its difference (any ring, any lengths).
* The class covers are singles (`sglCov`, entries exact); the rest (rows under no accepted hint, the differences)
  is one row kind (`rkOf`, entries kept in order), entries brought in bounds by their index (`nrmB`, same `Φ_Q` term).
* **`ptOfRowsG_eval`**: the table's evaluator is the rows' sum at every point, for every `ρ`, `N`, `H`.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Specification -/

/-- An entry with its coefficient negated. -/
def negQ (q : Q4) : Q4 := (-q.1, q.2)

/-- **A row's difference to the template at instance `j`**: free positions and mismatches give the row's entry
and the template's negated; leftovers of either list are kept (the template's negated). -/
def diffZ (k : CTpl) (j : ℕ) : List EntT → List (ℕ × Q4) → List Q4
  | e :: es, p :: ps =>
    (if freeAt j p.1 then [toQ e] else if toQ e == ctAt k p.1 j p.2 then [] else [toQ e, negQ (ctAt k p.1 j p.2)]) ++
      diffZ k j es ps
  | es, [] => es.map toQ
  | [], ps => (tAt k j ps).map negQ

/-- The class of a template (its covers singles, exact). -/
def mkC (h : HCls) (tp : Array (List (ℕ × Q4))) : CTpl :=
  ⟨h.xb, h.a, h.yb, h.bb, h.n, (if h.n ≤ 1 then 0 else Nat.log2 (h.n - 1) + 1), sglCov (tPart tp 0),
    sglCov (tPart tp 1), sglCov (tPart tp 2)⟩

/-- A class is accepted: it fits, its slots stay below `2^20`, its template parts are in bounds. -/
def clsAccB (k : CTpl) : Bool :=
  k.okB && decide (k.xb + 2 ^ (k.a + k.L) ≤ 2 ^ 20) && k.t0.ents.all bndQ && k.t1.ents.all bndQ && k.t2.ents.all bndQ

/-- The accepted hints from cursor `c`, with their classes and templates. -/
def accH (ρ : ℕ → List EntT) (N : ℕ) : ℕ → List HCls → List (HCls × CTpl × Array (List (ℕ × Q4)))
  | _, [] => []
  | c, h :: hs =>
    if c ≤ h.g0 ∧ h.g0 + h.n * h.len ≤ N then
      let tp := tplOf ρ h
      let k := mkC h tp
      if clsAccB k then (h, k, tp) :: accH ρ N (h.g0 + h.n * h.len) hs else accH ρ N c hs
    else accH ρ N c hs

/-- An accepted hint's differences (every instance, every row). -/
def clsDiff (ρ : ℕ → List EntT) (c : HCls × CTpl × Array (List (ℕ × Q4))) : List Q4 :=
  (List.range c.1.n).flatMap fun j => (List.range c.1.len).flatMap fun t =>
    diffZ c.2.1 j (ρ (c.1.g0 + j * c.1.len + t)) (c.2.2.getD t [])

/-- An entry in bounds with the same index (`gIdx`'s decoding). -/
def nrmB (q : Q4) : Q4 :=
  if bndQ q then q else
    let i := idxOf q.2.1 q.2.2.1 q.2.2.2
    (q.1, i % 4, i / 4 % 2 ^ 20, i / 4 / 2 ^ 20)

/-- The rest: rows under no accepted hint, then the accepted hints' differences. -/
def restQ (ρ : ℕ → List EntT) (N : ℕ) (A : List (HCls × CTpl × Array (List (ℕ × Q4)))) : List Q4 :=
  (gaps 0 (A.map (·.1)) N).flatMap (fun p => (List.range' p.1 p.2).flatMap fun g => (ρ g).map toQ) ++
    A.flatMap (clsDiff ρ)

/-- **The class table of rows `ρ g`, `g < N`, from any hints.** -/
def ptOfRowsG (ρ : ℕ → List EntT) (N : ℕ) (H : Array HCls) : PT :=
  let A := accH ρ N 0 H.toList
  ⟨(A.map (·.2.1)).toArray, sglCov [], #[], #[], #[], #[], rkOf ((restQ ρ N A).map nrmB)⟩

/-! ## Proof helpers -/

theorem qval_neg (g : ℕ → ℕ → ℕ → FE2) (q : Q4) : qval g (negQ q) = -qval g q := by
  simp [qval, negQ, neg_mul]

private theorem sum_neg_map {β : Type} (l : List β) (f : β → FE2) : (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Any row is its template part plus its difference.** -/
theorem diffZ_sum (k : CTpl) (j : ℕ) (g : ℕ → ℕ → ℕ → FE2) :
    ∀ (es : List EntT) (ps : List (ℕ × Q4)),
      (es.map (qval g ∘ toQ)).sum = ((tAt k j ps).map (qval g)).sum + ((diffZ k j es ps).map (qval g)).sum
  | [], [] => by simp [tAt, diffZ]
  | e :: es, [] => by simp [tAt, diffZ, Function.comp_def]
  | [], p :: ps => by
    simp only [diffZ, List.map_map, List.map_nil, List.sum_nil, Function.comp_def, qval_neg, sum_neg_map]
    ring
  | e :: es, p :: ps => by
    have ih := diffZ_sum k j g es ps
    by_cases hf : freeAt j p.1 = true
    · have e2 : tAt k j (p :: ps) = tAt k j ps := by simp [tAt, hf]
      simp only [diffZ, hf, if_true, List.map_append, List.sum_append, e2, List.map_cons, List.sum_cons,
        List.map_nil, List.sum_nil, Function.comp_apply] at ih ⊢
      rw [ih]; ring
    · have e2 : tAt k j (p :: ps) = ctAt k p.1 j p.2 :: tAt k j ps := by simp [tAt, hf]
      rw [e2]
      by_cases hm : toQ e = ctAt k p.1 j p.2
      · simp only [diffZ, hf, Bool.false_eq_true, if_false, hm, beq_self_eq_true, if_true, List.nil_append,
          List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
        rw [ih]; ring
      · have hb : (toQ e == ctAt k p.1 j p.2) = false := by simpa using hm
        simp only [diffZ, hf, Bool.false_eq_true, if_false, hb, List.cons_append, List.nil_append, List.map_cons,
          List.sum_cons, Function.comp_apply, qval_neg] at ih ⊢
        rw [ih]; ring

private theorem accH_segs (ρ : ℕ → List EntT) (N : ℕ) :
    ∀ (c : ℕ) (hs : List HCls), c ≤ N → segsOkB c ((accH ρ N c hs).map (·.1)) N = true
  | c, [], hc => by simp [accH, segsOkB, hc]
  | c, h :: hs, hc => by
    unfold accH
    split
    · rename_i hh
      simp only
      split
      · simp only [List.map_cons, segsOkB, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hh.1, accH_segs ρ N _ hs hh.2⟩
      · exact accH_segs ρ N c hs hc
    · exact accH_segs ρ N c hs hc

private theorem accH_mem (ρ : ℕ → List EntT) (N : ℕ) :
    ∀ (c : ℕ) (hs : List HCls), ∀ x ∈ accH ρ N c hs,
      x.2.2 = tplOf ρ x.1 ∧ x.2.1 = mkC x.1 x.2.2 ∧ clsAccB x.2.1 = true
  | c, [], x, hx => by simp [accH] at hx
  | c, h :: hs, x, hx => by
    unfold accH at hx
    split at hx
    · simp only at hx
      split at hx
      · rename_i ha
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨rfl, rfl, ha⟩
        · exact accH_mem ρ N _ hs x hx
      · exact accH_mem ρ N c hs x hx
    · exact accH_mem ρ N c hs x hx

theorem tplOf_size (ρ : ℕ → List EntT) (h : HCls) : (tplOf ρ h).size = h.len := by simp [tplOf]

/-- **One accepted hint**: its rows sum as its class plus its differences. -/
theorem acc_sum (ρ : ℕ → List EntT) (x : HCls × CTpl × Array (List (ℕ × Q4))) (hx1 : x.2.2.size = x.1.len)
    (hx2 : x.2.1 = mkC x.1 x.2.2) (g : ℕ → ℕ → ℕ → FE2) :
    ((List.range' x.1.g0 (x.1.n * x.1.len)).map fun r => ((ρ r).map (qval g ∘ toQ)).sum).sum =
      (x.2.1.ents.map (qval g)).sum + ((clsDiff ρ x).map (qval g)).sum := by
  obtain ⟨h, k, tp⟩ := x
  simp only at hx1 hx2 ⊢
  subst hx2
  rw [sum_seg]
  have e1 : ((List.range h.n).map fun j => ((List.range h.len).map fun t =>
      ((ρ (h.g0 + j * h.len + t)).map (qval g ∘ toQ)).sum).sum).sum =
      ((List.range h.n).map fun j => ((List.range h.len).map fun t =>
        ((tAt (mkC h tp) j (tp.getD t [])).map (qval g)).sum).sum).sum +
        ((clsDiff ρ (h, mkC h tp, tp)).map (qval g)).sum := by
    simp only [clsDiff]
    rw [sum_map_flatMap, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [sum_map_flatMap, ← List.sum_map_add]
    exact congrArg List.sum (List.map_congr_left fun t _ => diffZ_sum _ j g _ _)
  rw [e1]
  congr 1
  simp only [tAt_sum, List.sum_map_add, ite_sum, ← hx1]
  simp only [sum_tPart]
  rw [range_ite, ents_sum]
  simp only [mkC, sglCov_ents]

theorem nrmB_val (pt : List FE2) (q : Q4) : qval (phW pt) (nrmB q) = qval (phW pt) q := by
  unfold nrmB
  split
  · rfl
  · simp only [qval, phW]
    congr 2
    unfold idxOf
    have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
    rw [h20]
    omega

theorem nrmB_bnd (q : Q4) : bndQ (nrmB q) = true := by
  unfold nrmB
  split
  · assumption
  · simp only [bndQ, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by positivity)⟩

/-! ## The table's evaluator is the rows' sum -/

private theorem ptG_ents (ρ : ℕ → List EntT) (N : ℕ) (H : Array HCls) :
    (ptOfRowsG ρ N H).ents = ((accH ρ N 0 H.toList).map (·.2.1)).flatMap CTpl.ents ++
      (restQ ρ N (accH ρ N 0 H.toList)).map nrmB := by
  simp [ptOfRowsG, PT.ents, PT.kents, sglCov_ents, rkOf_ents]

/-- **The constructed table computes the rows' sum** at every point, for every rows and hints. -/
theorem ptOfRowsG_eval (ρ : ℕ → List EntT) (N : ℕ) (H : Array HCls) (pt : List FE2) :
    (ptOfRowsG ρ N H).eval pt = (((List.range N).flatMap ρ).map (qval (phW pt) ∘ toQ)).sum := by
  set A := accH ρ N 0 H.toList with hA
  have hmem := accH_mem ρ N 0 H.toList
  rw [← hA] at hmem
  have hok : (ptOfRowsG ρ N H).okB = true := by
    simp only [PT.okB, ptOfRowsG, Bool.and_eq_true, List.all_eq_true, List.toList_toArray, List.mem_map]
    refine ⟨fun k ⟨x, hx, hk⟩ => ?_, by simp [PT.kok]⟩
    rw [← hA] at hx
    have := (hmem x hx).2.2
    simp only [clsAccB, Bool.and_eq_true] at this
    exact hk ▸ this.1.1.1.1
  have hb : (ptOfRowsG ρ N H).ents.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) = true := by
    rw [ptG_ents, ← hA, List.all_append, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · simp only [List.mem_flatMap, List.mem_map] at hq
      obtain ⟨k, ⟨x, hx, rfl⟩, hq⟩ := hq
      have hc := (hmem x hx).2.2
      simp only [clsAccB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      exact ctpl_bnd _ hc.1.1.1.1 hc.1.1.1.2 hc.1.1.2 hc.1.2 hc.2 q hq
    · obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq
      exact nrmB_bnd q'
  rw [eval_ents _ hok hb, List.map_map]
  show ((ptOfRowsG ρ N H).ents.map (qval (phW pt))).sum = _
  rw [ptG_ents, ← hA, List.map_append, List.sum_append, List.map_map]
  have hn : ((restQ ρ N A).map (qval (phW pt) ∘ nrmB)).sum = ((restQ ρ N A).map (qval (phW pt))).sum :=
    congrArg List.sum (List.map_congr_left fun q _ => nrmB_val pt q)
  rw [hn]
  have hseg := sum_segs (fun r => ((ρ r).map (qval (phW pt) ∘ toQ)).sum) 0 (A.map (·.1)) N
    (accH_segs ρ N 0 H.toList (Nat.zero_le N))
  rw [Nat.sub_zero, ← List.range_eq_range'] at hseg
  have hc : ∀ x ∈ A, ((List.range' x.1.g0 (x.1.n * x.1.len)).map fun r => ((ρ r).map (qval (phW pt) ∘ toQ)).sum).sum =
      (x.2.1.ents.map (qval (phW pt))).sum + ((clsDiff ρ x).map (qval (phW pt))).sum := by
    intro x hx
    obtain ⟨h1, h2, _⟩ := hmem x hx
    exact acc_sum ρ x (by rw [h1, tplOf_size]) (h2) _
  rw [sum_map_flatMap (List.range N) ρ, hseg, List.map_map]
  rw [show (List.map ((fun h => ((List.range' h.g0 (h.n * h.len)).map fun r =>
      ((ρ r).map (qval (phW pt) ∘ toQ)).sum).sum) ∘ fun x => x.1) A) =
      A.map fun x => (x.2.1.ents.map (qval (phW pt))).sum + ((clsDiff ρ x).map (qval (phW pt))).sum from
    List.map_congr_left hc]
  rw [List.sum_map_add, restQ, List.map_append, List.sum_append]
  simp only [sum_map_flatMap, List.map_map, Function.comp_def]
  ring

end Lvm6.V
