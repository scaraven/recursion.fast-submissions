-- New for lvm6 (ST-4): the class table built from rows and checked per row (generic in the rows).
import Lvm6VPhiPT

/-!
# The class table from the rows (ST-4)

`ptCheck P (entsE Q lay)` expands every class and sorts 1.6–2.8 M entries. Here the table is built from the rows,
and the start-up check compares rows, not sorted expansions.

* **Rows** `ρ g`, `g < N`: a row instance's entries (`Lvm6VPhiRowsQ`: a template row at an iteration, `entsE`'s
  entries of it).
* **Class hints** (`HCls`, LAY's `HCLS g0 len n xb a yb b`): instance `j < n` is the rows `g0 + j·len + t`,
  `t < len`. The template (`clsOf`, a hint: the check decides) gives every entry position a kind `d`: `0` own word
  (`yb + j·2^bb + dy`), `1` the previous instance's word (`j ≥ 1`), `2` a fixed word, `≥ 3` free (to the rest). Every
  instance's row must be the template at `j` (`rowOkB`, `Row.shift` of the slot and word); instance `0`'s
  previous-word entries and every free entry go to the rest.
* **No sort.** The class's covers and the rest's kinds come from untrusted builders. They are compared with their
  inputs by `normB`: one bucket pass by slot (`bkF`, a permutation: **`bkF_perm`**), then each bucket's
  few entries normalised (`normL`). **`normB_sum`**: equal `normB` give equal sums.
* `rowsResG ρ N H`: the table and the check on rows `ρ g`, `g < N`; **`rowsOkG_sum`**: on a passed check the
  table's entries sum as the rows. `RowsOk` names the facts.
* `rowsChk`, `ptOfRows`, **`ptOfRows_ok`** on `(Q, lay)`: `Lvm6VPhiRowsQ`.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Specification -/

/-- **An entry moved by `dx` slots and `dy` words.** -/
def Row.shift (dx dy : ℕ) (e : EntT) : EntT := ⟨e.o, e.x + dx, e.y + dy, e.c⟩

/-- An entry as `(c, o, x, y)`. -/
def toQ (e : EntT) : Q4 := (e.c, e.o, e.x, e.y)

/-- An entry's value at the weights `g` (`c · g o x y`). -/
def qval (g : ℕ → ℕ → ℕ → FE2) (q : Q4) : FE2 := q.1 * g q.2.1 q.2.2.1 q.2.2.2

/-- `Φ_Q`'s weight at a point: `eq(pt, idx)`. -/
def phW (pt : List FE2) (o x y : ℕ) : FE2 := eqAtF pt (idxOf o x y)

/-- A class hint: instance `j < n` is the rows `g0 + j·len + t` (`t < len`); the class's slot and word blocks. -/
structure HCls where
  g0 : ℕ
  len : ℕ
  n : ℕ
  xb : ℕ
  a : ℕ
  yb : ℕ
  bb : ℕ
  deriving Inhabited, Repr

/-- The hints: the classes, sorted by `g0` with disjoint row ranges, and the rest's kinds (`cls` unused). -/
structure Hints where
  cls : Array HCls
  rk : PT

/-- The relative entry `q = (c, o, dx, dy)` of kind `d` at instance `j` of class `k` (`CTpl.ents`' three forms). -/
def ctAt (k : CTpl) (d j : ℕ) (q : Q4) : Q4 :=
  (q.1, q.2.1, k.xb + j * 2 ^ k.a + q.2.2.1,
    if d = 0 then k.yb + j * 2 ^ k.bb + q.2.2.2 else if d = 1 then k.yb + (j - 1) * 2 ^ k.bb + q.2.2.2
    else q.2.2.2)

/-- Whether position kind `d` goes to the rest at instance `j`: free, or the previous instance's word at `0`. -/
def freeAt (j d : ℕ) : Bool := decide (3 ≤ d) || (j == 0 && d == 1)

/-- **A row is the template at instance `j`**: same length, every position not free is the template's entry. -/
def rowOkB (k : CTpl) (j : ℕ) : List EntT → List (ℕ × Q4) → Bool
  | [], [] => true
  | e :: es, p :: ps => (freeAt j p.1 || toQ e == ctAt k p.1 j p.2) && rowOkB k j es ps
  | _, _ => false

/-- The row's entries that go to the rest. -/
def rowFree (j : ℕ) : List EntT → List (ℕ × Q4) → List EntT
  | e :: es, p :: ps => if freeAt j p.1 then e :: rowFree j es ps else rowFree j es ps
  | _, _ => []

/-- The template's part of kind `d` (relative entries). -/
def tPart (tp : Array (List (ℕ × Q4))) (d : ℕ) : List Q4 :=
  tp.toList.flatMap fun r => r.filterMap fun p => if p.1 = d then some p.2 else none

/-! ## No sort: buckets by slot -/

/-- One bucket pass: `a` into bucket `key a % K` (`Array.modify`, in place). -/
def bkF {α : Type} (K : ℕ) (key : α → ℕ) (l : List α) : Array (List α) :=
  l.foldl (fun A a => A.modify (key a % K) (a :: ·)) (Array.replicate K [])

/-- **The normal form by buckets**: entries by slot (`2^20` buckets), each bucket `normL`'d. -/
def normB (l : List (FE2 × ℕ)) : Array (List (FE2 × ℕ)) :=
  (bkF (2 ^ 20) (fun p => p.2 / 4) l).map normL

/-- In-bounds: matrix `< 4`, slot `< 2^20`. -/
def bndQ (q : Q4) : Bool := decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)

/-! ## The table from the rows (generic in the rows `ρ g`, `g < N`) -/

/-- The template of a class hint (a hint: the check decides): kinds from instances `0` and `1`. -/
def tplOf (ρ : ℕ → List EntT) (h : HCls) : Array (List (ℕ × Q4)) :=
  ((List.range h.len).map fun t =>
    let es1 := if 2 ≤ h.n then (ρ (h.g0 + h.len + t)).toArray else #[]
    (ρ (h.g0 + t)).zipIdx.map fun (e, i) =>
      let inb (y : ℕ) : Bool := decide (h.yb ≤ y ∧ y < h.yb + 2 ^ h.bb)
      let e1 := es1.getD i e
      if inb e.y && (h.n < 2 || e1.y == e.y + 2 ^ h.bb) then (0, (e.c, e.o, e.x - h.xb, e.y - h.yb))
      else if 2 ≤ h.n && inb e1.y && e1.x == e.x + 2 ^ h.a then (1, (e.c, e.o, e.x - h.xb, e1.y - h.yb))
      else if e1.y == e.y then (2, (e.c, e.o, e.x - h.xb, e.y))
      else (3, toQ e)).toArray

/-- A template part as entries (`x`, `y` relative). -/
def partE (tp : Array (List (ℕ × Q4))) (d : ℕ) : List EntT := (tPart tp d).map fun q => ⟨q.2.1, q.2.2.1, q.2.2.2, q.1⟩

/-- The class of a hint (covers from `mkRCov`: a hint). -/
def clsOf (ρ : ℕ → List EntT) (h : HCls) : CTpl × Array (List (ℕ × Q4)) :=
  let tp := tplOf ρ h
  (⟨h.xb, h.a, h.yb, h.bb, h.n, (if h.n ≤ 1 then 0 else Nat.log2 (h.n - 1) + 1), mkRCov (partE tp 0) true,
    mkRCov (partE tp 1) false, mkRCov (partE tp 2) false⟩, tp)

/-- A class's cover part `d`. -/
def CTpl.part (k : CTpl) (d : ℕ) : RCov := if d = 0 then k.t0 else if d = 1 then k.t1 else k.t2

/-- **A class hint's instance rows** (class `k`, template `tp`): every instance's rows are the template at its
instance. This check reads every hinted row; a row-level twin (the layout's affinity per chunk and region)
would discharge the same fact without reading entries. -/
def clsRowsC (ρ : ℕ → List EntT) (h : HCls) (k : CTpl) (tp : Array (List (ℕ × Q4))) : Bool :=
  (List.range h.n).all fun j => (List.range h.len).all fun t => rowOkB k j (ρ (h.g0 + j * h.len + t)) (tp.getD t [])

/-- A class hint's instance rows, on its class. -/
def clsRowsB (ρ : ℕ → List EntT) (h : HCls) : Bool := clsRowsC ρ h (clsOf ρ h).1 (clsOf ρ h).2

/-- **A class's template check**: the class fits, each cover part is its template part (`normB`, both in
bounds). Template rows only. -/
def clsTplC (k : CTpl) (tp : Array (List (ℕ × Q4))) : Bool :=
  k.okB && decide (k.xb + 2 ^ (k.a + k.L) ≤ 2 ^ 20) &&
    ([0, 1, 2].all fun d => (k.part d).ents.all bndQ && (tPart tp d).all bndQ &&
      normB ((k.part d).ents.map toIdx) == normB ((tPart tp d).map toIdx))

/-- A class hint's template check, on its class. -/
def clsTplB (ρ : ℕ → List EntT) (h : HCls) : Bool := clsTplC (clsOf ρ h).1 (clsOf ρ h).2

/-- The class hints' row ranges are sorted and disjoint, from row `c`, inside `[0, N)`. -/
def segsOkB : ℕ → List HCls → ℕ → Bool
  | c, [], N => decide (c ≤ N)
  | c, h :: hs, N => decide (c ≤ h.g0) && segsOkB (h.g0 + h.n * h.len) hs N

/-- The rows under no hint, as ranges `(start, count)`. -/
def gaps : ℕ → List HCls → ℕ → List (ℕ × ℕ)
  | c, [], N => [(c, N - c)]
  | c, h :: hs, N => (c, h.g0 - c) :: gaps (h.g0 + h.n * h.len) hs N

/-- The free entries of a class hint (all instances). -/
def clsFreeC (ρ : ℕ → List EntT) (h : HCls) (tp : Array (List (ℕ × Q4))) : List EntT :=
  (List.range h.n).flatMap fun j => (List.range h.len).flatMap fun t =>
    rowFree j (ρ (h.g0 + j * h.len + t)) (tp.getD t [])

/-- The free entries of a class hint, on its template. -/
def clsFree (ρ : ℕ → List EntT) (h : HCls) : List EntT := clsFreeC ρ h (clsOf ρ h).2

/-- The rest's entries: rows under no hint, then each class's free entries (instance `0` and free positions). -/
def restE (ρ : ℕ → List EntT) (N : ℕ) (H : List HCls) : List EntT :=
  (gaps 0 H N).flatMap (fun p => (List.range' p.1 p.2).flatMap ρ) ++ H.flatMap (clsFree ρ)

/-- `restE` on the hints' classes computed once. -/
def restEC (ρ : ℕ → List EntT) (N : ℕ) (H : List HCls) (cs : List (HCls × CTpl × Array (List (ℕ × Q4)))) :
    List EntT :=
  (gaps 0 H N).flatMap (fun p => (List.range' p.1 p.2).flatMap ρ) ++ cs.flatMap fun c => clsFreeC ρ c.1 c.2.2

theorem restEC_eq (ρ : ℕ → List EntT) (N : ℕ) (H : List HCls) :
    restEC ρ N H (H.map fun h => (h, clsOf ρ h)) = restE ρ N H := by
  unfold restEC restE
  rw [List.flatMap_map]
  rfl

/-- **The table and its check on rows `ρ g`, `g < N`**: the hinted classes, then the rest's table `H.rk` (any
kinds, classes included: untrusted, compared with the rest's entries by `normB`). -/
def rowsResG (ρ : ℕ → List EntT) (N : ℕ) (H : Hints) : PT × Bool :=
  let R := H.rk
  let cs := H.cls.toList.map fun h => (h, clsOf ρ h)
  (⟨(cs.map fun c => c.2.1).toArray ++ R.cls, R.rest, R.ak, R.str, R.gk, R.bk, R.rk⟩,
    segsOkB 0 H.cls.toList N && cs.all (fun c => clsTplC c.2.1 c.2.2) &&
      cs.all (fun c => clsRowsC ρ c.1 c.2.1 c.2.2) && R.okB && R.ents.all bndQ &&
      normB (R.ents.map toIdx) == normB ((restEC ρ N H.cls.toList cs).map keyE))

/-- **The facts of a passed check**, by name. -/
structure RowsOk (ρ : ℕ → List EntT) (N : ℕ) (H : Hints) : Prop where
  segs : segsOkB 0 H.cls.toList N = true
  tpl : ∀ h ∈ H.cls.toList, clsTplB ρ h = true
  rows : ∀ h ∈ H.cls.toList, clsRowsB ρ h = true
  kinds : H.rk.okB = true
  bnd : H.rk.ents.all bndQ = true
  rest : normB (H.rk.ents.map toIdx) = normB ((restE ρ N H.cls.toList).map keyE)

/-! ## Load-bearing lemmas -/

theorem rowsResG_sound {ρ : ℕ → List EntT} {N : ℕ} {H : Hints} (h : (rowsResG ρ N H).2 = true) :
    RowsOk ρ N H := by
  simp only [rowsResG, Bool.and_eq_true, beq_iff_eq, List.all_map, Function.comp_def, restEC_eq] at h
  obtain ⟨⟨⟨⟨⟨hs, ht⟩, hw⟩, hk⟩, hb⟩, hr⟩ := h
  simp only [List.all_eq_true] at ht hw
  exact ⟨hs, ht, hw, hk, hb, hr⟩

/-! ## Proof helpers: buckets -/

private theorem modify_cons_perm {α : Type} (a : α) :
    ∀ (l : List (List α)) (i : ℕ), i < l.length → (l.modify i (a :: ·)).flatten.Perm (a :: l.flatten)
  | [], _, h => absurd h (by simp)
  | b :: l, 0, _ => by simp [List.modify]
  | b :: l, i + 1, h => by
    have ih := modify_cons_perm a l i (by simpa using h)
    simp only [List.modify, List.modifyTailIdx_succ_cons, List.flatten_cons] at ih ⊢
    exact ((List.Perm.refl b).append ih).trans List.perm_middle

private theorem bucket_go_perm {α : Type} (K : ℕ) (key : α → ℕ) (hK : 0 < K) :
    ∀ (l : List α) (A : Array (List α)), A.size = K →
      (l.foldl (fun A a => A.modify (key a % K) (a :: ·)) A).toList.flatten.Perm (l ++ A.toList.flatten)
  | [], A, _ => by simp
  | a :: l, A, hA => by
    rw [List.foldl_cons]
    have hs : (A.modify (key a % K) (a :: ·)).size = K := by rw [Array.size_modify, hA]
    refine (bucket_go_perm K key hK l _ hs).trans ?_
    rw [Array.toList_modify]
    refine ((List.Perm.refl l).append (modify_cons_perm a A.toList _ ?_)).trans List.perm_middle
    rw [Array.length_toList, hA]; exact Nat.mod_lt _ hK

/-- **One bucket pass is a permutation** of its input. -/
theorem bkF_perm {α : Type} (K : ℕ) (key : α → ℕ) (hK : 0 < K) (l : List α) :
    (bkF K key l).toList.flatten.Perm l := by
  unfold bkF
  have h := bucket_go_perm K key hK l (Array.replicate K []) (by simp)
  simpa using h

private theorem sum_flatten_map {β : Type} (L : List (List β)) (f : β → FE2) :
    ((L.flatten).map f).sum = (L.map fun b => (b.map f).sum).sum := by
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.flatten_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- The sum of a list is the sum of its `normB` buckets. -/
theorem normB_val (l : List (FE2 × ℕ)) (f : ℕ → FE2) :
    (l.map fun p => p.1 * f p.2).sum = ((normB l).toList.map fun b => (b.map fun p => p.1 * f p.2).sum).sum := by
  rw [← ((bkF_perm (2 ^ 20) (fun p : FE2 × ℕ => p.2 / 4) (by positivity) l).map
    (fun p : FE2 × ℕ => p.1 * f p.2)).sum_eq, sum_flatten_map]
  unfold normB
  rw [Array.toList_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun b _ => (normL_sum f b).symm)

/-- **Equal bucket normal forms give equal sums**, at any weights of the index. -/
theorem normB_sum {l₁ l₂ : List (FE2 × ℕ)} (h : normB l₁ = normB l₂) (f : ℕ → FE2) :
    (l₁.map fun p => p.1 * f p.2).sum = (l₂.map fun p => p.1 * f p.2).sum := by
  rw [normB_val, normB_val, h]

/-! ## Proof helpers: indices, templates, rows -/

/-- The weights of an index (matrix, slot, word decoded). -/
def gIdx (g : ℕ → ℕ → ℕ → FE2) (i : ℕ) : FE2 := g (i % 4) (i / 4 % 2 ^ 20) (i / 4 / 2 ^ 20)

theorem idx_dec (o x y : ℕ) (ho : o < 4) (hx : x < 2 ^ 20) :
    idxOf o x y % 4 = o ∧ idxOf o x y / 4 % 2 ^ 20 = x ∧ idxOf o x y / 4 / 2 ^ 20 = y := by
  have h20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  rw [h20] at hx ⊢
  unfold idxOf
  rw [h20]
  omega

theorem sum_idx (g : ℕ → ℕ → ℕ → FE2) (L : List Q4) (hL : ∀ q ∈ L, bndQ q = true) :
    (L.map (qval g)).sum = ((L.map toIdx).map fun p => p.1 * gIdx g p.2).sum := by
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  have hb := hL q hq
  simp only [bndQ, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨h1, h2, h3⟩ := idx_dec q.2.1 q.2.2.1 q.2.2.2 hb.1 hb.2
  simp only [Function.comp_apply, toIdx, qval, gIdx, h1, h2, h3]

/-- In-bounds lists with equal `normB` forms have equal sums at any weights. -/
theorem sum_tr {L₁ L₂ : List Q4} (h₁ : ∀ q ∈ L₁, bndQ q = true) (h₂ : ∀ q ∈ L₂, bndQ q = true)
    (h : normB (L₁.map toIdx) = normB (L₂.map toIdx)) (g : ℕ → ℕ → ℕ → FE2) :
    (L₁.map (qval g)).sum = (L₂.map (qval g)).sum := by
  rw [sum_idx g L₁ h₁, sum_idx g L₂ h₂]
  exact normB_sum h _

/-- A template row at instance `j`: its positions not free. -/
def tAt (k : CTpl) (j : ℕ) (ps : List (ℕ × Q4)) : List Q4 :=
  ps.filterMap fun p => if freeAt j p.1 then none else some (ctAt k p.1 j p.2)

/-- A row's part of kind `d`. -/
def rPart (ps : List (ℕ × Q4)) (d : ℕ) : List Q4 := ps.filterMap fun p => if p.1 = d then some p.2 else none

theorem row_sum (k : CTpl) (j : ℕ) (g : ℕ → ℕ → ℕ → FE2) :
    ∀ (es : List EntT) (ps : List (ℕ × Q4)), rowOkB k j es ps = true →
      (es.map (qval g ∘ toQ)).sum = ((tAt k j ps).map (qval g)).sum + ((rowFree j es ps).map (qval g ∘ toQ)).sum
  | [], [], _ => by simp [tAt, rowFree]
  | [], _ :: _, h => by simp [rowOkB] at h
  | _ :: _, [], h => by simp [rowOkB] at h
  | e :: es, p :: ps, h => by
    simp only [rowOkB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨hp, hr⟩ := h
    have ih := row_sum k j g es ps hr
    by_cases hf : freeAt j p.1 = true
    · have e1 : rowFree j (e :: es) (p :: ps) = e :: rowFree j es ps := by simp [rowFree, hf]
      have e2 : tAt k j (p :: ps) = tAt k j ps := by simp [tAt, hf]
      rw [e1, e2, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
      ring
    · have he : toQ e = ctAt k p.1 j p.2 := by
        rcases hp with hp | hp
        · exact absurd hp hf
        · exact hp
      have e1 : rowFree j (e :: es) (p :: ps) = rowFree j es ps := by simp [rowFree, hf]
      have e2 : tAt k j (p :: ps) = ctAt k p.1 j p.2 :: tAt k j ps := by simp [tAt, hf]
      rw [e1, e2, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, Function.comp_apply, he]
      ring

theorem tAt_sum (k : CTpl) (j : ℕ) (g : ℕ → ℕ → ℕ → FE2) : ∀ ps : List (ℕ × Q4),
    ((tAt k j ps).map (qval g)).sum = ((rPart ps 0).map fun q => qval g (ctAt k 0 j q)).sum +
      (if j = 0 then 0 else ((rPart ps 1).map fun q => qval g (ctAt k 1 j q)).sum) +
      ((rPart ps 2).map fun q => qval g (ctAt k 2 j q)).sum
  | [] => by simp [tAt, rPart]
  | (d, q) :: ps => by
    have ih := tAt_sum k j g ps
    have hc : tAt k j ((d, q) :: ps) = (if freeAt j d then [] else [ctAt k d j q]) ++ tAt k j ps := by
      by_cases h : freeAt j d = true <;> simp [tAt, h]
    have hr : ∀ d', rPart ((d, q) :: ps) d' = (if d = d' then [q] else []) ++ rPart ps d' := by
      intro d'; by_cases h : d = d' <;> simp [rPart, h]
    rw [hc, hr 0, hr 1, hr 2, List.map_append, List.sum_append, ih]
    rcases Nat.lt_or_ge d 3 with hd | hd
    · interval_cases d <;> by_cases hj : j = 0 <;> simp [freeAt, hj] <;> ring
    · have hf : freeAt j d = true := by simp [freeAt, hd]
      simp [hf, show d ≠ 0 by omega, show d ≠ 1 by omega, show d ≠ 2 by omega]

/-- **A class's entries by kind and instance** (`CTpl.ents`' three parts at `ctAt`). -/
theorem ents_sum (k : CTpl) (g : ℕ → ℕ → ℕ → FE2) :
    (k.ents.map (qval g)).sum =
      ((List.range k.n).map fun j => (k.t0.ents.map fun q => qval g (ctAt k 0 j q)).sum).sum +
      ((List.range' 1 (k.n - 1)).map fun j => (k.t1.ents.map fun q => qval g (ctAt k 1 j q)).sum).sum +
      ((List.range k.n).map fun j => (k.t2.ents.map fun q => qval g (ctAt k 2 j q)).sum).sum := by
  unfold CTpl.ents
  simp only [List.map_append, List.sum_append, sum_map_flatMap, List.map_map]
  rfl

theorem ite_sum {β : Type} (l : List β) (c : Prop) [Decidable c] (f : β → FE2) :
    (l.map fun t => if c then 0 else f t).sum = if c then 0 else (l.map f).sum := by
  split <;> simp

theorem range_ite (n : ℕ) (f : ℕ → FE2) :
    ((List.range n).map fun j => if j = 0 then 0 else f j).sum = ((List.range' 1 (n - 1)).map f).sum := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [List.range_eq_range', List.range'_succ, List.map_cons, List.sum_cons, if_pos rfl, zero_add,
      Nat.add_sub_cancel]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have : 1 ≤ j := (List.mem_range'_1.1 hj).1
    rw [if_neg (by omega)]

/-! ## Proof helpers: segments, one class -/

private theorem segs_le : ∀ (c : ℕ) (hs : List HCls) (N : ℕ), segsOkB c hs N = true → c ≤ N
  | c, [], N, h => by simpa [segsOkB] using h
  | c, h :: hs, N, hh => by
    simp only [segsOkB, Bool.and_eq_true, decide_eq_true_eq] at hh
    have := segs_le _ hs N hh.2
    omega

/-- The rows from `c` split into the hints' ranges and the gaps. -/
theorem sum_segs (f : ℕ → FE2) : ∀ (c : ℕ) (hs : List HCls) (N : ℕ), segsOkB c hs N = true →
    ((List.range' c (N - c)).map f).sum =
      (hs.map fun h => ((List.range' h.g0 (h.n * h.len)).map f).sum).sum +
      ((gaps c hs N).map fun p => ((List.range' p.1 p.2).map f).sum).sum
  | c, [], N, _ => by simp [gaps]
  | c, h :: hs, N, hh => by
    simp only [segsOkB, Bool.and_eq_true, decide_eq_true_eq] at hh
    have hle := segs_le _ hs N hh.2
    have ih := sum_segs f _ hs N hh.2
    have e : N - c = (h.g0 - c) + (h.n * h.len + (N - (h.g0 + h.n * h.len))) := by omega
    rw [e, ← List.range'_append_1, ← List.range'_append_1, show c + (h.g0 - c) = h.g0 by omega]
    simp only [List.map_append, List.sum_append, ih, gaps, List.map_cons, List.sum_cons]
    ring

/-- A hint's range, instance by instance. -/
theorem sum_seg (f : ℕ → FE2) (g0 len : ℕ) : ∀ n : ℕ,
    ((List.range' g0 (n * len)).map f).sum =
      ((List.range n).map fun j => ((List.range len).map fun t => f (g0 + j * len + t)).sum).sum
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, ← List.range'_append_1, List.map_append, List.sum_append, sum_seg f g0 len n,
      List.range_succ, List.map_append, List.sum_append, List.range'_eq_map_range (s := g0 + n * len)]
    simp [List.map_map, Function.comp_def]

theorem sum_getD {α : Type} [Inhabited α] (l : List α) (h : α → FE2) :
    ((List.range l.length).map fun i ↦ h (l.getD i default)).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons, ← ih]
    rfl

theorem getD_toList {α : Type} (A : Array α) (i : ℕ) (d : α) : A.getD i d = A.toList.getD i d := by
  simp [List.getD_eq_getElem?_getD]

/-- The weights of an entry of kind `d` at instance `j`, as weights of its relative entry. -/
def gS (k : CTpl) (d j : ℕ) (g : ℕ → ℕ → ℕ → FE2) (o x y : ℕ) : FE2 :=
  g o (k.xb + j * 2 ^ k.a + x)
    (if d = 0 then k.yb + j * 2 ^ k.bb + y else if d = 1 then k.yb + (j - 1) * 2 ^ k.bb + y else y)

theorem qval_ctAt (k : CTpl) (d j : ℕ) (g : ℕ → ℕ → ℕ → FE2) (q : Q4) :
    qval g (ctAt k d j q) = qval (gS k d j g) q := rfl

theorem sum_tPart (tp : Array (List (ℕ × Q4))) (d : ℕ) (φ : Q4 → FE2) :
    ((List.range tp.size).map fun t => ((rPart (tp.getD t []) d).map φ).sum).sum = ((tPart tp d).map φ).sum := by
  have h := sum_getD tp.toList fun r => ((rPart r d).map φ).sum
  simp only [Array.length_toList] at h
  simp only [getD_toList]
  rw [show ([] : List (ℕ × Q4)) = default from rfl, h, tPart, sum_map_flatMap]
  rfl

private theorem part_tr (k : CTpl) (tp : Array (List (ℕ × Q4))) (d : ℕ) (hd : d ≤ 2)
    (h1 : ∀ q ∈ (k.part d).ents, bndQ q = true) (h2 : ∀ q ∈ tPart tp d, bndQ q = true)
    (h3 : (normB ((k.part d).ents.map toIdx) == normB ((tPart tp d).map toIdx)) = true)
    (g : ℕ → ℕ → ℕ → FE2) (j : ℕ) :
    ((tPart tp d).map fun q => qval g (ctAt k d j q)).sum = ((k.part d).ents.map fun q => qval g (ctAt k d j q)).sum := by
  simp only [qval_ctAt]
  exact (sum_tr h1 h2 (beq_iff_eq.1 h3) _).symm

/-- **One class hint**: its rows sum as its class plus its free entries. -/
theorem cls_sum (ρ : ℕ → List EntT) (h : HCls) (ht : clsTplB ρ h = true) (hw : clsRowsB ρ h = true)
    (g : ℕ → ℕ → ℕ → FE2) :
    ((List.range' h.g0 (h.n * h.len)).map fun r => ((ρ r).map (qval g ∘ toQ)).sum).sum =
      ((clsOf ρ h).1.ents.map (qval g)).sum + ((clsFree ρ h).map (qval g ∘ toQ)).sum := by
  set k := (clsOf ρ h).1 with hk
  set tp := (clsOf ρ h).2 with htp
  have hsz : tp.size = h.len := by simp [htp, clsOf, tplOf]
  have hn : k.n = h.n := rfl
  simp only [clsTplB, clsTplC, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨_, _⟩, hparts⟩ := ht
  simp only [clsRowsB, clsRowsC, List.all_eq_true, List.mem_range] at hw
  have hrows := hw
  rw [sum_seg]
  have hrow : ∀ j, j < h.n → ∀ t, t < h.len →
      ((ρ (h.g0 + j * h.len + t)).map (qval g ∘ toQ)).sum =
        ((tAt k j (tp.getD t [])).map (qval g)).sum +
          ((rowFree j (ρ (h.g0 + j * h.len + t)) (tp.getD t [])).map (qval g ∘ toQ)).sum :=
    fun j hj t ht => row_sum k j g _ _ (hrows j hj t ht)
  have e1 : ((List.range h.n).map fun j => ((List.range h.len).map fun t =>
      ((ρ (h.g0 + j * h.len + t)).map (qval g ∘ toQ)).sum).sum).sum =
      ((List.range h.n).map fun j => ((List.range h.len).map fun t =>
        ((tAt k j (tp.getD t [])).map (qval g)).sum).sum).sum + ((clsFree ρ h).map (qval g ∘ toQ)).sum := by
    simp only [clsFree, clsFreeC]
    rw [sum_map_flatMap, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [sum_map_flatMap, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    exact hrow j (List.mem_range.1 hj) t (List.mem_range.1 ht)
  rw [e1]
  congr 1
  simp only [tAt_sum, List.sum_map_add, ite_sum, ← hsz]
  simp only [sum_tPart]
  rw [range_ite, ents_sum, hn]
  have p0 := hparts 0 (by simp)
  have p1 := hparts 1 (by simp)
  have p2 := hparts 2 (by simp)
  have q0 := part_tr k tp 0 (by omega) p0.1.1 p0.1.2 p0.2 g
  have q1 := part_tr k tp 1 (by omega) p1.1.1 p1.1.2 p1.2 g
  have q2 := part_tr k tp 2 (by omega) p2.1.1 p2.1.2 p2.2 g
  simp only [q0, q1, q2]
  rfl

/-! ## Proof helpers: bounds -/

theorem ctpl_bnd (k : CTpl) (hk : k.okB = true) (hx : k.xb + 2 ^ (k.a + k.L) ≤ 2 ^ 20)
    (h0 : ∀ q ∈ k.t0.ents, bndQ q = true) (h1 : ∀ q ∈ k.t1.ents, bndQ q = true)
    (h2 : ∀ q ∈ k.t2.ents, bndQ q = true) : ∀ q ∈ k.ents, bndQ q = true := by
  simp only [CTpl.okB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hn⟩, _⟩, _⟩, a0⟩, a1⟩, a2⟩, _⟩ := hk
  have key : ∀ j ex, j < k.n → ex < 2 ^ k.a → k.xb + j * 2 ^ k.a + ex < 2 ^ 20 := by
    intro j ex hj he
    have h3 : j * 2 ^ k.a + ex < 2 ^ (k.a + k.L) := by
      calc j * 2 ^ k.a + ex < (j + 1) * 2 ^ k.a := by rw [Nat.succ_mul]; omega
        _ ≤ 2 ^ k.L * 2 ^ k.a := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ (k.a + k.L) := by rw [pow_add, mul_comm]
    omega
  intro q hq
  simp only [CTpl.ents, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'_1] at hq
  rcases hq with (⟨j, hj, e, he, rfl⟩ | ⟨j, hj, e, he, rfl⟩) | ⟨j, hj, e, he, rfl⟩
  · have hb := h0 e he
    simp only [bndQ, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, key j _ hj (a0 e he).1⟩
  · have hb := h1 e he
    simp only [bndQ, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, key j _ (by omega) (a1 e he).1⟩
  · have hb := h2 e he
    simp only [bndQ, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, key j _ hj (a2 e he)⟩

/-! ## The table's entries sum as the rows -/

private theorem resG_ents (ρ : ℕ → List EntT) (N : ℕ) (H : Hints) :
    (rowsResG ρ N H).1.ents = (H.cls.toList.map fun h => (clsOf ρ h).1).flatMap CTpl.ents ++ H.rk.ents := by
  simp [rowsResG, PT.ents, PT.kents, List.flatMap_append, List.map_map, Function.comp_def]

private theorem key_val (pt : List FE2) (e : EntT) :
    (keyE e).1 * eqAtF pt (keyE e).2 = qval (phW pt) (toQ e) := rfl

/-- **On a passed check the table's entries sum as the rows**, at every point. -/
theorem rowsOkG_sum {ρ : ℕ → List EntT} {N : ℕ} {H : Hints} (hR : RowsOk ρ N H) (pt : List FE2) :
    ((rowsResG ρ N H).1.ents.map (qval (phW pt))).sum = (((List.range N).flatMap ρ).map (qval (phW pt) ∘ toQ)).sum := by
  have hrest : (H.rk.ents.map (qval (phW pt))).sum =
      ((restE ρ N H.cls.toList).map (qval (phW pt) ∘ toQ)).sum := by
    have h := normB_sum hR.rest (eqAtF pt)
    simp only [List.map_map] at h
    exact h
  have hP := resG_ents ρ N H
  have hc : ∀ h ∈ H.cls.toList, ((List.range' h.g0 (h.n * h.len)).map fun r => ((ρ r).map (qval (phW pt) ∘ toQ)).sum).sum =
      ((clsOf ρ h).1.ents.map (qval (phW pt))).sum + ((clsFree ρ h).map (qval (phW pt) ∘ toQ)).sum :=
    fun h hh => cls_sum ρ h (hR.tpl h hh) (hR.rows h hh) _
  have hseg := sum_segs (fun r => ((ρ r).map (qval (phW pt) ∘ toQ)).sum) 0 H.cls.toList N hR.segs
  rw [Nat.sub_zero, ← List.range_eq_range'] at hseg
  rw [hP, List.map_append, List.sum_append, hrest, sum_map_flatMap _ CTpl.ents, List.map_map,
    sum_map_flatMap (List.range N) ρ, hseg, List.map_congr_left hc, List.sum_map_add, restE, List.map_append,
    List.sum_append, sum_map_flatMap _ (clsFree ρ), sum_map_flatMap (gaps 0 H.cls.toList N)]
  simp only [sum_map_flatMap, Function.comp_def]
  ring

/-- **The generic theorem**: on a passed check, the table's evaluator is the rows' sum at every point. -/
theorem rowsResG_eval {ρ : ℕ → List EntT} {N : ℕ} {H : Hints} (h : (rowsResG ρ N H).2 = true) (pt : List FE2) :
    (rowsResG ρ N H).1.eval pt = (((List.range N).flatMap ρ).map (qval (phW pt) ∘ toQ)).sum := by
  have hR := rowsResG_sound h
  have hcls : ∀ c ∈ H.cls.toList, (clsOf ρ c).1.okB = true ∧ (clsOf ρ c).1.xb + 2 ^ ((clsOf ρ c).1.a + (clsOf ρ c).1.L) ≤ 2 ^ 20 ∧
      ∀ d ∈ [0, 1, 2], (∀ q ∈ ((clsOf ρ c).1.part d).ents, bndQ q = true) := by
    intro c hc
    have := hR.tpl c hc
    simp only [clsTplB, clsTplC, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, fun d hd q hq => (this.2 d hd).1.1 q hq⟩
  have hok : (rowsResG ρ N H).1.okB = true := by
    have hk := hR.kinds
    simp only [PT.okB, Bool.and_eq_true, List.all_eq_true] at hk
    simp only [PT.okB, rowsResG, Bool.and_eq_true, List.all_eq_true, Array.toList_append, List.toList_toArray,
      List.mem_append, List.map_map, List.mem_map]
    refine ⟨fun k hk' => ?_, hk.2⟩
    rcases hk' with ⟨c, hc, rfl⟩ | hk'
    · exact (hcls c hc).1
    · exact hk.1 k hk'
  have hb : (rowsResG ρ N H).1.ents.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) = true := by
    rw [resG_ents, List.all_append, Bool.and_eq_true]
    refine ⟨?_, hR.bnd⟩
    rw [List.all_eq_true]
    intro q hq
    simp only [List.mem_flatMap, List.mem_map] at hq
    obtain ⟨k, ⟨c, hc, rfl⟩, hq⟩ := hq
    obtain ⟨h1, h2, h3⟩ := hcls c hc
    exact ctpl_bnd _ h1 h2 (h3 0 (by simp)) (h3 1 (by simp)) (h3 2 (by simp)) q hq
  rw [eval_ents _ hok hb, ← rowsOkG_sum hR pt, List.map_map]
  rfl

end Lvm6.V
