-- New for lvm6 (WP-TWT, PHI-decision R1): the cover-form `Φ_Q`. The entries come as twin pairs (word `y` with
-- coefficient `1`, word `y + 1` with `X`); per matrix the pairs are grouped by their slot or by their cell, one
-- product per group, with dense `eq` tables over the used slots and cells. The grouping is a hint: the evaluator
-- equals the sum over its own expansion for every table (`phiCov_eq`), and a start-up check (`covCheck`, a sort and
-- a comparison) makes the expansion a permutation of `entsE` (`phiCov_ents`).
import Lvm6VTwTPhi

/-!
# The cover-form `Φ_Q`

At a point `pt` of 43 coordinates write `a = pt[0,2)`, `m = pt[2,22)`, `b = pt[22,43) = b₀ :: b'`. For `o < 4` and
`x < 2^20`, `eq(pt, o + 4(x + 2^20 y)) = eq(a, o)·eq(m, x)·eq(b, y)` (`eq3`), and
* an aligned pair (`y = 2c`): `eq(b, 2c) + X·eq(b, 2c+1) = T·eq(b', c)`, `T = (1 + b₀) + X·b₀` (`alPair`);
* an odd pair (`y = 2c+1`): `eq(b, 2c+1) + X·eq(b, 2c+2)`, tabulated per odd cell (`odPair`).

* `Cov`: the used slots, aligned cells and odd cells (tables), per bucket `β < 8` (matrix `β/2`, aligned iff `β`
  odd) the row groups (a slot and its cells) and the cell groups (a cell and its slots), and the other entries.
* `Cov.expand`: the table's entries `(c, idx)`; **`phiCov`**, **`phiCov_eq`**: the sum over `expand`.
* `covCheck`, **`phiCov_ents`**: with the check, `phiCov tab pt = Σ_{e ∈ es} c_e·eq(pt, idx_e)`.
* `mkCov` (a hint, not proved): pairs found on the sorted entries, each bucket grouped by its smaller side.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## The table -/

/-- A member of a group: its index in the other side's table and its key (slot or cell). -/
structure CMem where
  k : ℕ
  v : ℕ

/-- A group: its key (table index and value) and its members. -/
structure CGrp where
  k : ℕ
  v : ℕ
  mem : Array CMem

/-- An entry outside every pair. -/
structure CSgl where
  o : ℕ
  x : ℕ
  c : FE2
  y : ℕ

/-- **The cover table.** -/
structure Cov where
  slots : Array ℕ
  als : Array ℕ
  ods : Array ℕ
  rowsB : Array (Array CGrp)
  colsB : Array (Array CGrp)
  sgl : Array CSgl

/-- `X` in `FE2`. -/
def xF : FE2 := ⟨0, 1⟩

/-- An entry's index on `Φ_Q`'s cube. -/
def idxOf (o x y : ℕ) : ℕ := o + 4 * (x + 2 ^ 20 * y)

/-- The two entries of a pair at slot `x`, cell `c` (aligned: words `2c, 2c+1`; odd: `2c+1, 2c+2`). -/
def pairEnts (o : ℕ) (al : Bool) (x c : ℕ) : List (FE2 × ℕ) :=
  if al then [(1, idxOf o x (2 * c)), (xF, idxOf o x (2 * c + 1))]
  else [(1, idxOf o x (2 * c + 1)), (xF, idxOf o x (2 * c + 2))]

/-- **The table's entries.** -/
def Cov.expand (tab : Cov) : List (FE2 × ℕ) :=
  (List.range 8).flatMap (fun β =>
    (tab.rowsB.getD β #[]).toList.flatMap (fun g => g.mem.toList.flatMap fun m => pairEnts (β / 2) (β % 2 == 1) g.v m.v) ++
    (tab.colsB.getD β #[]).toList.flatMap (fun g => g.mem.toList.flatMap fun m => pairEnts (β / 2) (β % 2 == 1) m.v g.v)) ++
  tab.sgl.toList.map fun s => (s.c, idxOf s.o s.x s.y)

/-- The bounds the factorization needs: every slot below `2^20`, every single's matrix below 4. -/
def Cov.okB (tab : Cov) : Bool :=
  (List.range 8).all (fun β => (tab.rowsB.getD β #[]).toList.all (fun g => decide (g.v < 2 ^ 20)) &&
    (tab.colsB.getD β #[]).toList.all (fun g => g.mem.toList.all fun m => decide (m.v < 2 ^ 20))) &&
  tab.sgl.toList.all fun s => decide (s.o < 4) && decide (s.x < 2 ^ 20)

/-! ## The evaluation -/

/-- A table value by index, checked against its key (`f v` otherwise). -/
@[inline] def lk (keys : Array ℕ) (vals : Array FE2) (f : ℕ → FE2) (k v : ℕ) : FE2 :=
  if h : k < keys.size ∧ k < vals.size then (if keys[k] = v then vals[k] else f v) else f v

theorem lk_eq (keys : Array ℕ) (f : ℕ → FE2) : lk keys (keys.map f) f = fun _ v => f v := by
  funext k v
  unfold lk
  split
  · rename_i h
    split
    · rename_i hv
      rw [Array.getElem_map, hv]
    · rfl
  · rfl

theorem arr_foldl_sum {α : Type} (arr : Array α) (g : α → FE2) :
    arr.foldl (fun s x => s + g x) 0 = (arr.toList.map g).sum := by
  rw [← Array.foldl_toList, foldl_add_eq, zero_add]

/-- `Σ_m vals(m)` over a group's members, read off a checked table, the sum kept in two words. -/
def memT (keys : Array ℕ) (vals : Array FE2) (f : ℕ → FE2) (mem : Array CMem) : FE2 := go 0 0 0
where
  go (i : ℕ) (re im : UInt64) : FE2 :=
    if h : i < mem.size then
      let z := lk keys vals f mem[i].k mem[i].v
      go (i + 1) (re ^^^ z.re.val) (im ^^^ z.im.val)
    else ⟨⟨re⟩, ⟨im⟩⟩
  termination_by mem.size - i

theorem memT_go (keys : Array ℕ) (vals : Array FE2) (f : ℕ → FE2) (mem : Array CMem) :
    ∀ (n i : ℕ) (re im : UInt64), mem.size - i = n →
      memT.go keys vals f mem i re im = ⟨⟨re⟩, ⟨im⟩⟩ + ((mem.toList.drop i).map fun m => lk keys vals f m.k m.v).sum
  | 0, i, re, im, hn => by
    rw [memT.go, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega), List.map_nil, List.sum_nil,
      add_zero]
  | n + 1, i, re, im, hn => by
    have hi : i < mem.size := by omega
    rw [memT.go, dif_pos hi, memT_go keys vals f mem n (i + 1) _ _ (by omega),
      List.drop_eq_getElem_cons (i := i) (l := mem.toList) (by simpa using hi), List.map_cons, List.sum_cons,
      ← add_assoc]
    simp only [Array.getElem_toList]
    rfl

theorem memT_eq (keys : Array ℕ) (vals : Array FE2) (f : ℕ → FE2) (mem : Array CMem) :
    memT keys vals f mem = (mem.toList.map fun m => lk keys vals f m.k m.v).sum := by
  rw [memT, memT_go keys vals f mem _ 0 0 0 rfl, List.drop_zero]
  exact zero_add _

/-- A bucket's groups: rows (slot key, word members) and columns (word key, slot members). -/
def grpSum (sk : Array ℕ) (sv : Array FE2) (fs : ℕ → FE2) (wk : Array ℕ) (wv : Array FE2) (fw : ℕ → FE2)
    (rows cols : Array CGrp) : FE2 :=
  rows.foldl (fun s g => s + lk sk sv fs g.k g.v * memT wk wv fw g.mem) 0 +
    cols.foldl (fun s g => s + lk wk wv fw g.k g.v * memT sk sv fs g.mem) 0

/-- The sum over the buckets and the singles, the tables given (computed once by the caller). -/
def covSum (tab : Cov) (a : List FE2) (T : FE2) (fsv fcv fov fy : ℕ → FE2) (SV CV OV : Array FE2) : FE2 :=
  (List.range 8).foldl (fun s β =>
    let al := β % 2 == 1
    let rows := tab.rowsB.getD β #[]
    let cols := tab.colsB.getD β #[]
    let S := if al then grpSum tab.slots SV fsv tab.als CV fcv rows cols
      else grpSum tab.slots SV fsv tab.ods OV fov rows cols
    s + eqAtF a (β / 2) * ((if al then T else 1) * S)) 0 +
    tab.sgl.foldl (fun s e => s + e.c * (eqAtF a e.o * (fsv e.x * fy e.y))) 0

/-- **The cover-form evaluation** at `a`, `m`, `b = b₀ :: b'` (and `b` itself for the odd cells and the singles). -/
def covEval (tab : Cov) (a mid : List FE2) (b0 : FE2) (bt b : List FE2) : FE2 :=
  let sm := mkSEq mid
  let st := mkSEq bt
  let sb := mkSEq b
  let fsv : ℕ → FE2 := fun x => sm.at mid x
  let fcv : ℕ → FE2 := fun c => st.at bt c
  let fov : ℕ → FE2 := fun c => sb.at b (2 * c + 1) + xF * sb.at b (2 * c + 2)
  covSum tab a ((1 + b0) + xF * b0) fsv fcv fov (fun y => sb.at b y) (tab.slots.map fsv) (tab.als.map fcv)
    (tab.ods.map fov)

/-- **The cover-form `Φ_Q`** (by the expansion at a point not of 43 coordinates). -/
def phiCov (tab : Cov) (pt : List FE2) : FE2 :=
  if pt.length = 43 then
    covEval tab (pt.take 2) ((pt.drop 2).take 20) ((pt.drop 22).headD 0) (pt.drop 22).tail (pt.drop 22)
  else (tab.expand.map fun e => e.1 * eqAtF pt e.2).sum

/-! ## Correctness -/

section Proof

theorem sum_map_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → FE2) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem eq3 (pt : List FE2) (hl : pt.length = 43) (o x y : ℕ) (ho : o < 4) (hx : x < 2 ^ 20) :
    eqAtF pt (idxOf o x y) = eqAtF (pt.take 2) o * (eqAtF ((pt.drop 2).take 20) x * eqAtF (pt.drop 22) y) := by
  have h1 : pt = pt.take 2 ++ ((pt.drop 2).take 20 ++ pt.drop 22) := by
    rw [show pt.drop 22 = (pt.drop 2).drop 20 by rw [List.drop_drop], List.take_append_drop,
      List.take_append_drop]
  have l2 : (pt.take 2).length = 2 := by simp [hl]
  have l20 : ((pt.drop 2).take 20).length = 20 := by simp [hl]
  conv_lhs => rw [h1]
  rw [eqAtF_append, eqAtF_append, l2, l20, eqAtF_mod (pt.take 2), l2, eqAtF_mod ((pt.drop 2).take 20), l20]
  unfold idxOf
  have e1 : (o + 4 * (x + 2 ^ 20 * y)) % 2 ^ 2 = o := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]; omega
  have e2 : (o + 4 * (x + 2 ^ 20 * y)) / 2 ^ 2 = x + 2 ^ 20 * y := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]; omega
  have e3 : (x + 2 ^ 20 * y) % 2 ^ 20 = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have e4 : (x + 2 ^ 20 * y) / 2 ^ 20 = y := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
  rw [e1, e2, e3, e4]

variable (pt : List FE2) (hl : pt.length = 43)

include hl in
theorem pair_val (b0 : FE2) (bt : List FE2) (hb : pt.drop 22 = b0 :: bt) (o : ℕ) (ho : o < 4) (al : Bool) (x c : ℕ)
    (hx : x < 2 ^ 20) :
    ((pairEnts o al x c).map fun e => e.1 * eqAtF pt e.2).sum =
      eqAtF (pt.take 2) o * ((if al then (1 + b0) + xF * b0 else 1) *
        (eqAtF ((pt.drop 2).take 20) x * (if al then eqAtF bt c else
          eqAtF (pt.drop 22) (2 * c + 1) + xF * eqAtF (pt.drop 22) (2 * c + 2)))) := by
  unfold pairEnts
  cases al
  · simp only [Bool.false_eq_true, if_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [eq3 pt hl _ _ _ ho hx, eq3 pt hl _ _ _ ho hx]
    ring
  · simp only [if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [eq3 pt hl _ _ _ ho hx, eq3 pt hl _ _ _ ho hx, hb, eqAtF_succ, eqAtF_succ, if_neg (by omega),
      if_pos (by omega), show 2 * c / 2 = c by omega, show (2 * c + 1) / 2 = c by omega]
    ring

end Proof

section Assembly

variable (pt : List FE2) (hl : pt.length = 43) (b0 : FE2) (bt : List FE2) (hb : pt.drop 22 = b0 :: bt)

/-- The word side of a pair (aligned: `eq(b', c)`; odd: the odd cell's value). -/
def wOf (al : Bool) (c : ℕ) : FE2 :=
  if al then eqAtF bt c else eqAtF (pt.drop 22) (2 * c + 1) + xF * eqAtF (pt.drop 22) (2 * c + 2)

include hl hb in
theorem row_val (o : ℕ) (ho : o < 4) (al : Bool) (g : CGrp) (hx : g.v < 2 ^ 20) :
    (g.mem.toList.map fun m => ((pairEnts o al g.v m.v).map fun e => e.1 * eqAtF pt e.2).sum).sum =
      eqAtF (pt.take 2) o * ((if al then (1 + b0) + xF * b0 else 1) *
        (eqAtF ((pt.drop 2).take 20) g.v * (g.mem.toList.map fun m => wOf pt bt al m.v).sum)) := by
  simp only [pair_val pt hl b0 bt hb o ho al _ _ hx, List.sum_map_mul_left]
  rfl

include hl hb in
theorem col_val (o : ℕ) (ho : o < 4) (al : Bool) (g : CGrp) (hx : ∀ m ∈ g.mem.toList, m.v < 2 ^ 20) :
    (g.mem.toList.map fun m => ((pairEnts o al m.v g.v).map fun e => e.1 * eqAtF pt e.2).sum).sum =
      eqAtF (pt.take 2) o * ((if al then (1 + b0) + xF * b0 else 1) *
        (wOf pt bt al g.v * (g.mem.toList.map fun m => eqAtF ((pt.drop 2).take 20) m.v).sum)) := by
  rw [List.map_congr_left fun m hm => pair_val pt hl b0 bt hb o ho al _ _ (hx m hm)]
  simp only [List.sum_map_mul_left, List.sum_map_mul_right]
  unfold wOf
  ring

end Assembly

theorem phiCov_eq (tab : Cov) (hok : tab.okB = true) (pt : List FE2) :
    phiCov tab pt = (tab.expand.map fun e => e.1 * eqAtF pt e.2).sum := by
  unfold phiCov
  split
  · rename_i hl
    obtain ⟨b0, bt, hb⟩ : ∃ b0 bt, pt.drop 22 = b0 :: bt := by
      cases h : pt.drop 22 with
      | nil => have := congrArg List.length h; simp [hl] at this
      | cons b0 bt => exact ⟨b0, bt, rfl⟩
    simp only [Cov.okB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hok
    obtain ⟨hB, hS⟩ := hok
    have h0 : (pt.drop 22).headD 0 = b0 := by rw [hb]; rfl
    have ht : (pt.drop 22).tail = bt := by rw [hb]; rfl
    unfold covEval covSum
    simp only [grpSum, memT_eq, lk_eq, mkSEq_at, h0, ht, arr_foldl_sum, foldl_add_eq, zero_add]
    unfold Cov.expand
    rw [List.map_append, List.sum_append, sum_map_flatMap, List.map_map]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine congrArg List.sum (List.map_congr_left fun β hβ => ?_)
      have hβ8 : β < 8 := List.mem_range.mp hβ
      have ho : β / 2 < 4 := by omega
      obtain ⟨hr, hc⟩ := hB β hβ8
      simp only [Function.comp_apply, List.map_append, List.sum_append, sum_map_flatMap]
      rw [List.map_congr_left fun g hg => row_val pt hl b0 bt hb _ ho _ g (hr g hg),
        List.map_congr_left fun g hg => col_val pt hl b0 bt hb _ ho _ g (hc g hg)]
      rcases Bool.eq_false_or_eq_true (β % 2 == 1) with h | h <;>
        simp only [h, if_true, if_false, Bool.false_eq_true, List.sum_map_mul_left, wOf] <;> ring
    · refine congrArg List.sum (List.map_congr_left fun e he => ?_)
      obtain ⟨ho, hx⟩ := hS e he
      simp only [Function.comp_apply, eq3 pt hl _ _ _ ho hx]
  · rfl

/-! ## The start-up check -/

/-- An entry as `(c, idx)`. -/
def keyE (e : EntT) : FE2 × ℕ := (e.c, Lvm6.Ty.EntT.idxE e)

/-- A comparison of keys (any comparison makes the check sound; a total order makes it complete). -/
def keyLe (p q : FE2 × ℕ) : Bool :=
  p.2 < q.2 || (p.2 == q.2 && (p.1.re.val < q.1.re.val || (p.1.re.val == q.1.re.val && p.1.im.val ≤ q.1.im.val)))

/-- **The check**: the bounds, and the expansion sorted is the entries sorted. -/
def covCheck (tab : Cov) (es : List EntT) : Bool :=
  tab.okB && decide (tab.expand.mergeSort keyLe = (es.map keyE).mergeSort keyLe)

/-- **The cover-form `Φ_Q` is the entries' sum** once the check passed. -/
theorem phiCov_ents (tab : Cov) (es : List EntT) (h : covCheck tab es = true) (pt : List FE2) :
    phiCov tab pt = es.foldr (fun e acc => e.c * eqWT pt (Lvm6.Ty.EntT.idxE e) + acc) 0 := by
  simp only [covCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, heq⟩ := h
  have hp : tab.expand.Perm (es.map keyE) :=
    (List.mergeSort_perm tab.expand keyLe).symm.trans (heq ▸ List.mergeSort_perm (es.map keyE) keyLe)
  rw [phiCov_eq tab hok, (hp.map _).sum_eq, foldr_add_eq, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  simp only [Function.comp_apply, keyE, eqWT_eq]

/-! ## The cover (a hint) -/

/-- The index of a key in a growing table. -/
def idxIn (m : Std.HashMap ℕ ℕ) (keys : Array ℕ) (v : ℕ) : Std.HashMap ℕ ℕ × Array ℕ × ℕ :=
  match m.get? v with
  | some k => (m, keys, k)
  | none => (m.insert v keys.size, keys.push v, keys.size)

/-- **The cover of a list of entries**: pairs on the entries sorted by `(o, x, y)`; per bucket the smaller side as
the groups' keys. Not proved: `covCheck` decides whether it is right. -/
def mkCov (es : List EntT) : Cov := Id.run do
  let arr := (es.map fun e => (e.o, e.x, e.y, e.c)).toArray.qsort fun p q =>
    p.1 < q.1 || (p.1 == q.1 && (p.2.1 < q.2.1 || (p.2.1 == q.2.1 && p.2.2.1 < q.2.2.1)))
  let mut edges : Array (Array (ℕ × ℕ)) := Array.replicate 8 #[]
  let mut sgl : Array CSgl := #[]
  let mut skip := false
  for i in [0:arr.size] do
    if skip then
      skip := false
    else
      let (o, x, y, c) := arr[i]!
      let nxt := arr[i + 1]?
      if c = 1 ∧ o < 4 ∧ nxt = some (o, x, y + 1, xF) then
        let al := y % 2 == 0
        let β := 2 * o + (if al then 1 else 0)
        edges := edges.modify β (·.push (x, if al then y / 2 else (y - 1) / 2))
        skip := true
      else
        sgl := sgl.push ⟨o, x, c, y⟩
  let mut sm : Std.HashMap ℕ ℕ := {}
  let mut slots : Array ℕ := #[]
  let mut am : Std.HashMap ℕ ℕ := {}
  let mut als : Array ℕ := #[]
  let mut om : Std.HashMap ℕ ℕ := {}
  let mut ods : Array ℕ := #[]
  let mut rowsB : Array (Array CGrp) := #[]
  let mut colsB : Array (Array CGrp) := #[]
  for β in [0:8] do
    let ed := edges[β]!
    let al := β % 2 == 1
    let nr := (ed.foldl (fun (h : Std.HashSet ℕ) e => h.insert e.1) {}).size
    let nc := (ed.foldl (fun (h : Std.HashSet ℕ) e => h.insert e.2) {}).size
    let mut grp : Std.HashMap ℕ (Array CMem) := {}
    for (x, cl) in ed do
      let r := idxIn sm slots x
      sm := r.1; slots := r.2.1
      let ki ← if al then
          let r' := idxIn am als cl
          am := r'.1; als := r'.2.1
          pure r'.2.2
        else
          let r' := idxIn om ods cl
          om := r'.1; ods := r'.2.1
          pure r'.2.2
      if nr ≤ nc then grp := grp.insert x ((grp.getD x #[]).push ⟨ki, cl⟩)
      else grp := grp.insert cl ((grp.getD cl #[]).push ⟨r.2.2, x⟩)
    let gs : Array CGrp := grp.fold (fun acc key mem =>
      let k := if nr ≤ nc then (sm.getD key 0) else if al then am.getD key 0 else om.getD key 0
      acc.push ⟨k, key, mem⟩) #[]
    if nr ≤ nc then
      rowsB := rowsB.push gs; colsB := colsB.push #[]
    else
      rowsB := rowsB.push #[]; colsB := colsB.push gs
  return ⟨slots, als, ods, rowsB, colsB, sgl⟩

end Lvm6.V
