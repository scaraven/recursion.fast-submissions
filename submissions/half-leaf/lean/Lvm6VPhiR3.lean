-- New for lvm6 (WP-PHIV, PHI-decision R2/R3): the class evaluator of `Φ_Q` on LAY's layout. A class's instances
-- repeat one template, so the class costs its template once (in cover form, on the low `eq` tables) times
-- `Σ_j eq(x_mid, j)·eq(y_mid, j)`; R2's `W` twins (word `2x` at slot `x`) are summed in closed form over runs.
-- The table is a hint: the start-up check (`ptCheck`) compares its expansion with `entsE` after merging equal
-- indices (characteristic 2 corrections cancel), and then the evaluator is `Φ_Q` (`phiOk_pt`).
import Lvm6VPhiV
import Lvm6PhiCls

/-!
# The class evaluator of `Φ_Q`

* `Q4`: an entry `(c, o, x, y)`; `qv fa fs fw q = c·fa(o)·fs(x)·fw(y)`.
* `FCov.ents`, `flatSumG`, **`gflat_eq`**: the flat cover's sum for any weights `fa`, `fs`, `fw` (no decoding).
* `wPre`, **`wPre_eq`**: `Σ_{x<e} eq(m, x)·eq(b', x)` in closed form; `RCov` (a cover and `W` runs), `rsum_eq`.
* `CTpl` (a class: geometry, templates `t0` same instance, `t1` previous instance, `t2` fixed words), `CTpl.ents`,
  `CTpl.val`, **`class_eq`**.
* `AK` (affine kinds: loop classes, aligned externals), `AK.ents`, `AK.okB`, `AK.valW`, **`AK.valW_eq`**.
* PHIV7: `flushSum`, **`flushSum_eq`** (a sum grouped by runs of equal keys, any order); its uses `sglSumK`
  (singles per `(o, key y)`), `flatSumK`, `rsumK` (empty buckets and run factors skipped), `AK.rowW2`, `AK.valW2`
  (affine lines per `(fx, ek, o, high word part)`), each with an `_eq` lemma to the PHIV5 form.
* The table `PT`, its evaluator and start-up check: `Lvm6VPhiPT`.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Generic cover sums -/

/-- An entry `(c, o, x, y)`. -/
abbrev Q4 := FE2 × ℕ × ℕ × ℕ

/-- An entry's value under the weights. -/
def qv (fa fs fw : ℕ → FE2) (e : Q4) : FE2 := e.1 * (fa e.2.1 * (fs e.2.2.1 * fw e.2.2.2))

/-- The entries of a pair of bucket `β` at slot `x`, cell `c`. -/
def pairQ (β x c : ℕ) : List Q4 :=
  if β % 2 == 1 then [(1, β / 2, x, 2 * c), (xF, β / 2, x, 2 * c + 1)]
  else [(1, β / 2, x, 2 * c + 1), (xF, β / 2, x, 2 * c + 2)]

/-- A flat bucket's entries. -/
def FBk.ents (b : FBk) (β : ℕ) (sl ce : Array ℕ) : List Q4 :=
  (List.range b.gk.size).flatMap fun g => (b.mem g).flatMap fun j =>
    if b.byRow then pairQ β (sl.getD (b.gk.getD g 0) 0) (ce.getD (b.mm.getD j 0) 0)
    else pairQ β (sl.getD (b.mm.getD j 0) 0) (ce.getD (b.gk.getD g 0) 0)

/-- **A flat cover's entries.** -/
def FCov.ents (ft : FCov) : List Q4 :=
  (List.range 8).flatMap (fun β => (ft.bk.getD β default).ents β ft.slots (ft.cells β)) ++
    ft.sgl.toList.map fun s => (s.c, s.o, s.x, s.y)

/-- A table valid for the keys `K` and the weights `f`: every read is `f` of the key (`K.map f` or `#[]`). -/
abbrev TV (V : Array FE2) (K : Array ℕ) (f : ℕ → FE2) : Prop := ∀ k, rd V K f k = f (K.getD k 0)

theorem tv_ite (c : Bool) (K : Array ℕ) (f : ℕ → FE2) : TV (if c = true then K.map f else #[]) K f := by
  intro k
  split
  · exact rd_map K f k
  · simp [rd]

/-- The singles of matrix `o` from `i` on: `Σ c·fs(x)·fw(y)` (products inlined, coefficient `1` skipped). -/
@[specialize] def sglGo (sg : Array CSgl) (fs fw : ℕ → FE2) (o i : ℕ) (acc : FE2) : FE2 :=
  if h : i < sg.size then
    if sg[i].o = o then
      let v := mulE (fs sg[i].x) (fw sg[i].y)
      sglGo sg fs fw o (i + 1) (acc + if sg[i].c = 1 then v else mulE sg[i].c v)
    else sglGo sg fs fw o (i + 1) acc
  else acc
termination_by sg.size - i

/-- **The singles' sum**: per matrix `o < 4` one pass and `fa o` once; matrices from `4` on entry by entry. -/
@[specialize] def sglSum (sg : Array CSgl) (fa fs fw : ℕ → FE2) : FE2 :=
  mulE (fa 0) (sglGo sg fs fw 0 0 0) + mulE (fa 1) (sglGo sg fs fw 1 0 0) + mulE (fa 2) (sglGo sg fs fw 2 0 0) +
    mulE (fa 3) (sglGo sg fs fw 3 0 0) +
    sg.foldl (fun s e => if 4 ≤ e.o then s + e.c * (fa e.o * (fs e.x * fw e.y)) else s) 0

theorem sglGo_eq (sg : Array CSgl) (fs fw : ℕ → FE2) (o : ℕ) : ∀ (d i : ℕ) (acc : FE2), sg.size - i = d →
    sglGo sg fs fw o i acc = acc + (((sg.toList.drop i).filter fun e => e.o = o).map fun e =>
      e.c * (fs e.x * fw e.y)).sum
  | 0, i, acc, hd => by
    rw [sglGo, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]; simp
  | d + 1, i, acc, hd => by
    have hi : i < sg.size := by omega
    rw [sglGo, dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [Array.getElem_toList, List.filter_cons, mulE_eq]
    by_cases ho : sg[i].o = o
    · rw [if_pos ho, sglGo_eq sg fs fw o d (i + 1) _ (by omega)]
      simp only [ho, decide_true, if_true, List.map_cons, List.sum_cons]
      by_cases hc : sg[i].c = 1
      · rw [if_pos hc, hc, one_mul, add_assoc]
      · rw [if_neg hc, add_assoc]
    · rw [if_neg ho, sglGo_eq sg fs fw o d (i + 1) _ (by omega)]
      simp [ho]

theorem sgl_split (fa fs fw : ℕ → FE2) : ∀ l : List CSgl,
    (l.map fun e => e.c * (fa e.o * (fs e.x * fw e.y))).sum =
      fa 0 * ((l.filter fun e => e.o = 0).map fun e => e.c * (fs e.x * fw e.y)).sum +
      fa 1 * ((l.filter fun e => e.o = 1).map fun e => e.c * (fs e.x * fw e.y)).sum +
      fa 2 * ((l.filter fun e => e.o = 2).map fun e => e.c * (fs e.x * fw e.y)).sum +
      fa 3 * ((l.filter fun e => e.o = 3).map fun e => e.c * (fs e.x * fw e.y)).sum +
      ((l.filter fun e => 4 ≤ e.o).map fun e => e.c * (fa e.o * (fs e.x * fw e.y))).sum
  | [] => by simp
  | e :: l => by
    rw [List.map_cons, List.sum_cons, sgl_split fa fs fw l]
    simp only [List.filter_cons]
    rcases (show e.o = 0 ∨ e.o = 1 ∨ e.o = 2 ∨ e.o = 3 ∨ 4 ≤ e.o by omega) with h | h | h | h | h
    · simp [h]; ring
    · simp [h]; ring
    · simp [h]; ring
    · simp [h]; ring
    · simp [h, show e.o ≠ 0 by omega, show e.o ≠ 1 by omega, show e.o ≠ 2 by omega, show e.o ≠ 3 by omega]
      ring

theorem sglSum_eq (sg : Array CSgl) (fa fs fw : ℕ → FE2) :
    sglSum sg fa fs fw = (sg.toList.map fun e => e.c * (fa e.o * (fs e.x * fw e.y))).sum := by
  have hf : sg.foldl (fun s e => if 4 ≤ e.o then s + e.c * (fa e.o * (fs e.x * fw e.y)) else s) 0 =
      ((sg.toList.filter fun e => 4 ≤ e.o).map fun e => e.c * (fa e.o * (fs e.x * fw e.y))).sum := by
    rw [← Array.foldl_toList]
    generalize sg.toList = l
    suffices ∀ acc, l.foldl (fun s e => if 4 ≤ e.o then s + e.c * (fa e.o * (fs e.x * fw e.y)) else s) acc =
        acc + ((l.filter fun e => 4 ≤ e.o).map fun e => e.c * (fa e.o * (fs e.x * fw e.y))).sum by
      simpa using this 0
    induction l with
    | nil => intro acc; simp
    | cons e l ih =>
      intro acc
      rw [List.foldl_cons, ih, List.filter_cons]
      by_cases h : 4 ≤ e.o
      · simp [h, add_assoc]
      · simp [h]
  conv_rhs => rw [sgl_split fa fs fw sg.toList]
  unfold sglSum
  rw [hf, sglGo_eq _ _ _ _ _ 0 0 rfl, sglGo_eq _ _ _ _ _ 0 0 rfl, sglGo_eq _ _ _ _ _ 0 0 rfl,
    sglGo_eq _ _ _ _ _ 0 0 rfl]
  simp only [mulE_eq, List.drop_zero, zero_add]

/-- The flat cover's sum under any weights (`flatSum` with `fa` for `eq(a, ·)`). -/
@[specialize] def flatSumG (ft : FCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (SV CV OV : Array FE2) : FE2 :=
  (List.range 8).foldl (fun s β =>
    s + fa (β / 2) * ((if β % 2 == 1 then T else 1) *
      (if β % 2 == 1 then bkSum (ft.bk.getD β default) ft.slots ft.als SV CV fs fcv
        else bkSum (ft.bk.getD β default) ft.slots ft.ods SV OV fs fov))) 0 +
    sglSum ft.sgl fa fs fw

section Generic

variable (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2)
  (hal : ∀ c, fw (2 * c) + xF * fw (2 * c + 1) = T * fcv c)
  (hod : ∀ c, fov c = fw (2 * c + 1) + xF * fw (2 * c + 2))

include hal hod in
theorem pairQ_sum (β x c : ℕ) :
    ((pairQ β x c).map (qv fa fs fw)).sum =
      fa (β / 2) * ((if β % 2 == 1 then T else 1) * (fs x * (if β % 2 == 1 then fcv c else fov c))) := by
  unfold pairQ
  rcases Bool.eq_false_or_eq_true (β % 2 == 1) with h | h
  · simp only [h, if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qv]
    rw [show T * (fs x * fcv c) = fs x * (T * fcv c) by ring, ← hal]
    ring
  · simp only [h, Bool.false_eq_true, if_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qv]
    rw [hod]
    ring

theorem bk_ents_sum (b : FBk) (β : ℕ) (sl ce : Array ℕ) (q : Q4 → FE2) (C : FE2) (gs gc : ℕ → FE2)
    (SV CV : Array FE2) (hS : TV SV sl gs) (hC : TV CV ce gc)
    (hp : ∀ x c, ((pairQ β x c).map q).sum = C * (gs x * gc c)) :
    ((b.ents β sl ce).map q).sum = C * bkSum b sl ce SV CV gs gc := by
  unfold FBk.ents bkSum
  have hc : ∀ u v, gs u * gc v = gc v * gs u := fun _ _ => mul_comm _ _
  by_cases hb : b.byRow
  · simp only [hb, if_true, sum_map_flatMap, hp, bkGo_zero, hS, hC, List.sum_map_mul_left]
  · simp only [hb, Bool.false_eq_true, if_false, sum_map_flatMap, hp, hc, bkGo_zero, hS, hC, List.sum_map_mul_left]

include hal hod in
/-- **The flat cover's sum** under any weights. -/
theorem gflat_eq (ft : FCov) (SV CV OV : Array FE2) (hS : TV SV ft.slots fs) (hC : TV CV ft.als fcv)
    (hO : TV OV ft.ods fov) :
    flatSumG ft fa T fs fcv fov fw SV CV OV = (ft.ents.map (qv fa fs fw)).sum := by
  unfold flatSumG FCov.ents
  simp only [List.map_append, List.sum_append, sum_map_flatMap, foldl_add_eq, zero_add, List.map_map]
  refine congrArg₂ (· + ·) (congrArg List.sum (List.map_congr_left fun β _ => ?_)) ?_
  · rcases Bool.eq_false_or_eq_true (β % 2 == 1) with h | h
    · have hp : ∀ x c, ((pairQ β x c).map (qv fa fs fw)).sum = (fa (β / 2) * T) * (fs x * fcv c) := by
        intro x c; rw [pairQ_sum fa T fs fcv fov fw hal hod]; simp only [h, if_true]; ring
      simp only [FCov.cells, h, if_true]
      rw [bk_ents_sum _ β _ _ _ _ fs fcv SV CV hS hC hp]
      ring
    · have hp : ∀ x c, ((pairQ β x c).map (qv fa fs fw)).sum = fa (β / 2) * (fs x * fov c) := by
        intro x c; rw [pairQ_sum fa T fs fcv fov fw hal hod]; simp only [h, Bool.false_eq_true, if_false]; ring
      simp only [FCov.cells, h, Bool.false_eq_true, if_false]
      rw [bk_ents_sum _ β _ _ _ _ fs fov SV OV hS hO hp]
      ring
  · rw [sglSum_eq]; rfl

end Generic

/-! ## `W` runs in closed form -/

/-- `(Σ_{x<e} eq(ms, x)·eq(bs, x), eq(ms, e)·eq(bs, e))`, the lists of equal length, `e ≤ 2^|ms|`. -/
def wPre : List FE2 → List FE2 → ℕ → FE2 × FE2
  | m0 :: ms, b0 :: bs, e =>
    let r := wPre ms bs (e / 2)
    let h0 := (1 + m0) * (1 + b0)
    let h1 := m0 * b0
    ((h0 + h1) * r.1 + (if e % 2 = 1 then h0 * r.2 else 0), (if e % 2 = 1 then h1 else h0) * r.2)
  | _, _, e => (if e = 0 then 0 else 1, 1)

theorem range_add1 (n : ℕ) : List.range (n + 1) = List.range n ++ [n] := List.range_succ

theorem sum_range_pair (ms bs : List FE2) (h0 h1 : FE2) : ∀ q : ℕ,
    ((List.range (2 * q)).map fun x =>
      (if x % 2 = 1 then h1 else h0) * (eqAtF ms (x / 2) * eqAtF bs (x / 2))).sum =
      (h0 + h1) * ((List.range q).map fun x => eqAtF ms x * eqAtF bs x).sum
  | 0 => by simp
  | q + 1 => by
    have e1 : (2 * q) % 2 = 0 := by omega
    have e2 : (2 * q) / 2 = q := by omega
    have e3 : (2 * q + 1) % 2 = 1 := by omega
    have e4 : (2 * q + 1) / 2 = q := by omega
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, range_add1 (2 * q + 1), range_add1 (2 * q), range_add1 q,
      List.map_append, List.map_append, List.sum_append, List.sum_append, sum_range_pair ms bs h0 h1 q,
      List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e1, e2, e3, e4, if_true,
      show (0 : ℕ) ≠ 1 from by decide, if_false]
    ring

theorem wPre_eq : ∀ (ms bs : List FE2) (e : ℕ), ms.length = bs.length → e ≤ 2 ^ ms.length →
    wPre ms bs e = (((List.range e).map fun x => eqAtF ms x * eqAtF bs x).sum, eqAtF ms e * eqAtF bs e)
  | [], [], e, _, he => by
    have : e = 0 ∨ e = 1 := by simp at he; omega
    rcases this with rfl | rfl <;> simp [wPre]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | m0 :: ms, b0 :: bs, e, h, he => by
    have hl : ms.length = bs.length := by simpa using h
    have hq : e / 2 ≤ 2 ^ ms.length := by
      simp only [List.length_cons, pow_succ] at he; omega
    rw [wPre, wPre_eq ms bs (e / 2) hl hq]
    have hP : ∀ x, eqAtF (m0 :: ms) x * eqAtF (b0 :: bs) x =
        (if x % 2 = 1 then m0 * b0 else (1 + m0) * (1 + b0)) * (eqAtF ms (x / 2) * eqAtF bs (x / 2)) := by
      intro x; rw [eqAtF_succ, eqAtF_succ]; split_ifs <;> ring
    simp only [hP]
    obtain ⟨q, rfl | rfl⟩ : ∃ q, e = 2 * q ∨ e = 2 * q + 1 := ⟨e / 2, by omega⟩
    · have e1 : (2 * q) % 2 = 0 := by omega
      have e2 : (2 * q) / 2 = q := by omega
      rw [sum_range_pair ms bs]
      simp only [e1, e2, show (0 : ℕ) ≠ 1 from by decide, if_false, add_zero, Prod.mk.injEq, and_self]
    · have e3 : (2 * q + 1) % 2 = 1 := by omega
      have e4 : (2 * q + 1) / 2 = q := by omega
      rw [range_add1 (2 * q), List.map_append, List.sum_append, sum_range_pair ms bs]
      have e1 : (2 * q) % 2 = 0 := by omega
      have e2 : (2 * q) / 2 = q := by omega
      simp only [e1, e2, e3, e4, if_true, show (0 : ℕ) ≠ 1 from by decide, if_false, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Prod.mk.injEq, and_self]

/-- The per-coordinate factors `((1 + m)(1 + b), m·b)` of `wPre`, computed once. -/
def hzip : List FE2 → List FE2 → List (FE2 × FE2)
  | m0 :: ms, b0 :: bs => (mulE (1 + m0) (1 + b0), mulE m0 b0) :: hzip ms bs
  | _, _ => []

/-- `wPre` off precomputed factors. -/
def wPreH : List (FE2 × FE2) → ℕ → FE2 × FE2
  | h :: hs, e =>
    let r := wPreH hs (e / 2)
    (mulE (h.1 + h.2) r.1 + (if e % 2 = 1 then mulE h.1 r.2 else 0), mulE (if e % 2 = 1 then h.2 else h.1) r.2)
  | [], e => (if e = 0 then 0 else 1, 1)

theorem wPreH_eq : ∀ (ms bs : List FE2) (e : ℕ), wPreH (hzip ms bs) e = wPre ms bs e
  | m0 :: ms, b0 :: bs, e => by
    simp only [hzip, wPreH, wPre, wPreH_eq ms bs, mulE_eq]
  | [], _, e => by simp [hzip, wPreH, wPre]
  | _ :: _, [], e => by simp [hzip, wPreH, wPre]

/-- The entries of a `W` run `[s, e)`: `(1, 3, x, 2x)`, `(X, 3, x, 2x + 1)`. -/
def runEnts (r : ℕ × ℕ) : List Q4 :=
  (List.range' r.1 (r.2 - r.1)).flatMap fun x => [(1, 3, x, 2 * x), (xF, 3, x, 2 * x + 1)]

/-- **A cover with `W` runs.** -/
structure RCov where
  fc : FCov
  wr : Array (ℕ × ℕ)

/-- Its entries. -/
def RCov.ents (rc : RCov) : List Q4 := rc.fc.ents ++ rc.wr.toList.flatMap runEnts

/-- A run's sum: closed form when the lists fit, else entry by entry. -/
def runSum (fa : ℕ → FE2) (T : FE2) (fs fw : ℕ → FE2) (ms bs : List FE2) (r : ℕ × ℕ) : FE2 :=
  if ms.length = bs.length ∧ r.1 ≤ r.2 ∧ r.2 ≤ 2 ^ ms.length then
    fa 3 * (T * ((wPre ms bs r.2).1 - (wPre ms bs r.1).1))
  else ((runEnts r).map (qv fa fs fw)).sum

/-- `Σ_{x∈[s,e)} fs(x)·fcv(x)` entry by entry (short runs). -/
@[specialize] def dirRun (fs fcv : ℕ → FE2) (r : ℕ × ℕ) : FE2 :=
  (List.range' r.1 (r.2 - r.1)).foldl (fun acc x => acc + mulE (fs x) (fcv x)) 0

/-- `runSum` with the factors of `wPre` precomputed; runs of at most 16 slots entry by entry. -/
@[specialize] def runSumH (hz : List (FE2 × FE2)) (fa : ℕ → FE2) (T : FE2) (fs fcv fw : ℕ → FE2) (ms bs : List FE2)
    (r : ℕ × ℕ) : FE2 :=
  if r.2 - r.1 ≤ 16 then mulE (fa 3) (mulE T (dirRun fs fcv r))
  else if ms.length = bs.length ∧ r.1 ≤ r.2 ∧ r.2 ≤ 2 ^ ms.length then
    mulE (fa 3) (mulE T ((wPreH hz r.2).1 - (wPreH hz r.1).1))
  else ((runEnts r).map (qv fa fs fw)).sum

/-- **A run's entries' sum** is `fa 3 · T · Σ_x fs(x)·fcv(x)`. -/
theorem runEnts_sum (fa : ℕ → FE2) (T : FE2) (fs fcv fw : ℕ → FE2)
    (hal : ∀ c, fw (2 * c) + xF * fw (2 * c + 1) = T * fcv c) (r : ℕ × ℕ) :
    ((runEnts r).map (qv fa fs fw)).sum =
      fa 3 * (T * ((List.range' r.1 (r.2 - r.1)).map fun x => fs x * fcv x).sum) := by
  unfold runEnts
  rw [sum_map_flatMap, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qv]
  rw [show fa 3 * (T * (fs x * fcv x)) = fa 3 * (fs x * (T * fcv x)) by ring, ← hal]
  ring

/-- **The sum of a cover with runs** (`ms`, `bs`: the runs' slot and twin-cell coordinates). Only the tables read
as members are built (the keys are computed in the group loop). -/
@[specialize] def rsum (rc : RCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (ms bs : List FE2) : FE2 :=
  let needS := rc.fc.bk.any fun b => !b.byRow && decide (0 < b.gk.size)
  let needC := rc.fc.bk.any fun b => b.byRow
  let hz := hzip ms bs
  flatSumG rc.fc fa T fs fcv fov fw (if needS = true then rc.fc.slots.map fs else #[])
      (if needC = true then rc.fc.als.map fcv else #[]) (if needC = true then rc.fc.ods.map fov else #[]) +
    rc.wr.foldl (fun s r => s + runSumH hz fa T fs fcv fw ms bs r) 0

section Runs

variable (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2)
  (hal : ∀ c, fw (2 * c) + xF * fw (2 * c + 1) = T * fcv c)
  (hod : ∀ c, fov c = fw (2 * c + 1) + xF * fw (2 * c + 2))
  (ms bs : List FE2) (hs : ∀ x, fs x = eqAtF ms x) (hc : ∀ c, fcv c = eqAtF bs c)

include hal hs hc in
theorem runSum_eq (r : ℕ × ℕ) : runSum fa T fs fw ms bs r = ((runEnts r).map (qv fa fs fw)).sum := by
  unfold runSum
  split
  · rename_i h
    obtain ⟨hl, h1, h2⟩ := h
    rw [wPre_eq ms bs _ hl h2, wPre_eq ms bs _ hl (le_trans h1 h2)]
    simp only
    have hsplit : List.range r.2 = List.range r.1 ++ List.range' r.1 (r.2 - r.1) := by
      rw [List.range_eq_range', List.range_eq_range']
      have := List.range'_append_1 (s := 0) (m := r.1) (n := r.2 - r.1)
      rw [Nat.zero_add, show r.1 + (r.2 - r.1) = r.2 by omega] at this
      exact this.symm
    rw [hsplit, List.map_append, List.sum_append, add_sub_cancel_left]
    unfold runEnts
    rw [sum_map_flatMap, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, qv, ← hs, ← hc]
    rw [show T * (fs x * fcv x) = fs x * (T * fcv x) by ring, ← hal]
    ring
  · rfl

include hal hs hc in
theorem runSumH_eq (r : ℕ × ℕ) :
    runSumH (hzip ms bs) fa T fs fcv fw ms bs r = ((runEnts r).map (qv fa fs fw)).sum := by
  unfold runSumH
  split
  · rw [runEnts_sum fa T fs fcv fw hal r, dirRun, foldl_add_eq, zero_add, mulE_eq, mulE_eq]
    simp only [mulE_eq]
  · split
    · rename_i hcond
      have h := runSum_eq fa T fs fcv fw hal ms bs hs hc r
      unfold runSum at h
      rw [if_pos hcond] at h
      rw [← h, wPreH_eq, wPreH_eq, mulE_eq, mulE_eq]
    · rfl

include hal hod hs hc in
theorem rsum_eq (rc : RCov) : rsum rc fa T fs fcv fov fw ms bs = (rc.ents.map (qv fa fs fw)).sum := by
  unfold rsum RCov.ents
  simp only
  rw [gflat_eq fa T fs fcv fov fw hal hod _ _ _ _ (tv_ite _ _ _) (tv_ite _ _ _) (tv_ite _ _ _), List.map_append,
    List.sum_append, sum_map_flatMap, ← Array.foldl_toList, foldl_add_eq, zero_add]
  refine congrArg₂ (· + ·) rfl (congrArg List.sum (List.map_congr_left fun r _ => ?_))
  exact runSumH_eq fa T fs fcv fw hal ms bs hs hc r

end Runs

/-! ## Splitting `eq` at aligned blocks -/

theorem eq_split (p : List FE2) (k u v : ℕ) (hk : k ≤ p.length) (hu : u < 2 ^ k) :
    eqAtF p (u + 2 ^ k * v) = eqAtF (p.take k) u * eqAtF (p.drop k) v := by
  have hl : (p.take k).length = k := by simp [hk]
  conv_lhs => rw [← List.take_append_drop k p]
  rw [eqAtF_append, hl, eqAtF_mod (p.take k), hl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hu, zero_add]

theorem eq_split3 (p : List FE2) (base k L j u : ℕ) (hb : base % 2 ^ (k + L) = 0) (hu : u < 2 ^ k)
    (hj : j < 2 ^ L) (hl : k + L ≤ p.length) :
    eqAtF p (base + j * 2 ^ k + u) =
      eqAtF (p.take k) u * (eqAtF ((p.drop k).take L) j * eqAtF ((p.drop k).drop L) (base / 2 ^ (k + L))) := by
  obtain ⟨q, hq⟩ : 2 ^ (k + L) ∣ base := Nat.dvd_of_mod_eq_zero hb
  have hd : base / 2 ^ (k + L) = q := by rw [hq, Nat.mul_div_cancel_left q (by positivity)]
  have he : base + j * 2 ^ k + u = u + 2 ^ k * (j + 2 ^ L * q) := by rw [hq, pow_add]; ring
  rw [he, eq_split p k u _ (by omega) hu, eq_split (p.drop k) L j q (by simp; omega) hj, hd]

/-! ## Classes -/

/-- **A class**: instance `j < n` at slots `xb + j·2^a + i`, words `yb + j·2^bb + w`; `L` instance bits;
templates `t0` (words of the same instance), `t1` (the previous instance), `t2` (fixed words). -/
structure CTpl where
  xb : ℕ
  a : ℕ
  yb : ℕ
  bb : ℕ
  n : ℕ
  L : ℕ
  t0 : RCov
  t1 : RCov
  t2 : RCov

/-- **A class's entries.** -/
def CTpl.ents (k : CTpl) : List Q4 :=
  (List.range k.n).flatMap (fun j => k.t0.ents.map fun e =>
      (e.1, e.2.1, k.xb + j * 2 ^ k.a + e.2.2.1, k.yb + j * 2 ^ k.bb + e.2.2.2)) ++
    (List.range' 1 (k.n - 1)).flatMap (fun j => k.t1.ents.map fun e =>
      (e.1, e.2.1, k.xb + j * 2 ^ k.a + e.2.2.1, k.yb + (j - 1) * 2 ^ k.bb + e.2.2.2)) ++
    (List.range k.n).flatMap (fun j => k.t2.ents.map fun e => (e.1, e.2.1, k.xb + j * 2 ^ k.a + e.2.2.1, e.2.2.2))

/-- The class check: aligned, fitting, the templates inside their blocks, word blocks of at least two words. -/
def CTpl.okB (k : CTpl) : Bool :=
  decide (k.a + k.L ≤ 20) && decide (k.bb + k.L ≤ 21) && decide (k.n ≤ 2 ^ k.L) &&
    k.xb % 2 ^ (k.a + k.L) == 0 && k.yb % 2 ^ (k.bb + k.L) == 0 &&
    k.t0.ents.all (fun e => decide (e.2.2.1 < 2 ^ k.a) && decide (e.2.2.2 < 2 ^ k.bb)) &&
    k.t1.ents.all (fun e => decide (e.2.2.1 < 2 ^ k.a) && decide (e.2.2.2 < 2 ^ k.bb)) &&
    k.t2.ents.all (fun e => decide (e.2.2.1 < 2 ^ k.a)) && decide (1 ≤ k.bb)

/-- The instance weights `eq(x_mid, j)`. -/
def CTpl.XM (k : CTpl) (m : List FE2) : ℕ → FE2 := eqAtF ((m.drop k.a).take k.L)
/-- The instance weights `eq(y_mid, j)`. -/
def CTpl.YM (k : CTpl) (b : List FE2) : ℕ → FE2 := eqAtF ((b.drop k.bb).take k.L)
/-- The slot block's high weight. -/
def CTpl.XH (k : CTpl) (m : List FE2) : FE2 := eqAtF ((m.drop k.a).drop k.L) (k.xb / 2 ^ (k.a + k.L))
/-- The word block's high weight. -/
def CTpl.YH (k : CTpl) (b : List FE2) : FE2 := eqAtF ((b.drop k.bb).drop k.L) (k.yb / 2 ^ (k.bb + k.L))

/-- `Σ_{j<n} f(j)·g(j)`. -/
def dotN (f g : ℕ → FE2) (n : ℕ) : FE2 := ((List.range n).map fun j => f j * g j).sum

/-- **A class's value** from its parts: the instance weights `XM`, `YM`, the high parts `XH`, `YH`, the template
sums `V0`, `V1`, `V2`. -/
def clsComb (n : ℕ) (XM YM : ℕ → FE2) (XH YH V0 V1 V2 : FE2) : FE2 :=
  XH * (YH * (dotN XM YM n * V0 + ((List.range' 1 (n - 1)).map fun j => XM j * YM (j - 1)).sum * V1) +
    ((List.range n).map XM).sum * V2)

section Class

variable (A : ℕ → FE2) (m b : List FE2) (k : CTpl)

/-- **A class's sum** is its templates' sums on the low `eq` tables times the instance sums. -/
theorem class_eq (hm : k.a + k.L ≤ m.length) (hb : k.bb + k.L ≤ b.length) (hk : k.okB = true) :
    (k.ents.map (qv A (eqAtF m) (eqAtF b))).sum =
      clsComb k.n (k.XM m) (k.YM b) (k.XH m) (k.YH b)
        ((k.t0.ents.map (qv A (eqAtF (m.take k.a)) (eqAtF (b.take k.bb)))).sum)
        ((k.t1.ents.map (qv A (eqAtF (m.take k.a)) (eqAtF (b.take k.bb)))).sum)
        ((k.t2.ents.map (qv A (eqAtF (m.take k.a)) (eqAtF b))).sum) := by
  simp only [CTpl.okB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hn⟩, hxb⟩, hyb⟩, h0⟩, h1⟩, h2⟩, _⟩ := hk
  have hj : ∀ j, j < k.n → j < 2 ^ k.L := fun j hj => lt_of_lt_of_le hj hn
  have e0 : (((List.range k.n).flatMap (fun j => k.t0.ents.map fun e =>
      (e.1, e.2.1, k.xb + j * 2 ^ k.a + e.2.2.1, k.yb + j * 2 ^ k.bb + e.2.2.2))).map
        (qv A (eqAtF m) (eqAtF b))).sum =
      ((List.range k.n).map fun j => (k.t0.ents.map (qv A (eqAtF (m.take k.a)) (eqAtF (b.take k.bb)))).sum *
        (k.XM m j * k.YM b j * (k.XH m * k.YH b))).sum := by
    rw [sum_map_flatMap]
    refine congrArg List.sum (List.map_congr_left fun j hjm => ?_)
    have hjL := hj j (List.mem_range.mp hjm)
    rw [List.map_map, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    obtain ⟨hx, hy⟩ := h0 e he
    simp only [Function.comp_apply, qv, CTpl.XM, CTpl.YM, CTpl.XH, CTpl.YH]
    rw [eq_split3 m k.xb k.a k.L j _ hxb hx hjL hm, eq_split3 b k.yb k.bb k.L j _ hyb hy hjL hb]
    ring
  have e1 : (((List.range' 1 (k.n - 1)).flatMap (fun j => k.t1.ents.map fun e =>
      (e.1, e.2.1, k.xb + j * 2 ^ k.a + e.2.2.1, k.yb + (j - 1) * 2 ^ k.bb + e.2.2.2))).map
        (qv A (eqAtF m) (eqAtF b))).sum =
      ((List.range' 1 (k.n - 1)).map fun j => (k.t1.ents.map (qv A (eqAtF (m.take k.a)) (eqAtF (b.take k.bb)))).sum *
        (k.XM m j * k.YM b (j - 1) * (k.XH m * k.YH b))).sum := by
    rw [sum_map_flatMap]
    refine congrArg List.sum (List.map_congr_left fun j hjm => ?_)
    have hjn : j < k.n := by rw [List.mem_range'_1] at hjm; omega
    have hjL := hj j hjn
    have hjL' : j - 1 < 2 ^ k.L := by omega
    rw [List.map_map, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    obtain ⟨hx, hy⟩ := h1 e he
    simp only [Function.comp_apply, qv, CTpl.XM, CTpl.YM, CTpl.XH, CTpl.YH]
    rw [eq_split3 m k.xb k.a k.L j _ hxb hx hjL hm, eq_split3 b k.yb k.bb k.L (j - 1) _ hyb hy hjL' hb]
    ring
  have e2 : (((List.range k.n).flatMap (fun j => k.t2.ents.map fun e =>
      (e.1, e.2.1, k.xb + j * 2 ^ k.a + e.2.2.1, e.2.2.2))).map (qv A (eqAtF m) (eqAtF b))).sum =
      ((List.range k.n).map fun j => (k.t2.ents.map (qv A (eqAtF (m.take k.a)) (eqAtF b))).sum *
        (k.XM m j * k.XH m)).sum := by
    rw [sum_map_flatMap]
    refine congrArg List.sum (List.map_congr_left fun j hjm => ?_)
    have hjL := hj j (List.mem_range.mp hjm)
    rw [List.map_map, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    have hx := h2 e he
    simp only [Function.comp_apply, qv, CTpl.XM, CTpl.XH]
    rw [eq_split3 m k.xb k.a k.L j _ hxb hx hjL hm]
    ring
  unfold CTpl.ents
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, e0, e1, e2]
  unfold clsComb dotN
  simp only [List.sum_map_mul_left, List.sum_map_mul_right]
  ring

end Class

/-! ## Kernel lookups -/

/-- One coordinate of the kernel, one product per entry (`v·(1 + r) = v + v·r`). -/
def kerStep (out : Array FE2) (r : FE2) : Array FE2 :=
  let t := out.map fun v => mulE v r
  Array.zipWith (· + ·) out t ++ t

/-- **The `eq` kernel** with one product per entry. -/
def kerF (p : List FE2) : Array FE2 := p.foldl kerStep #[1]

theorem zw_aux (r : FE2) : ∀ l : List FE2,
    List.zipWith (· + ·) l (l.map fun v => v * r) = l.map fun v => v * (1 + r)
  | [] => rfl
  | v :: l => by simp only [List.map_cons, List.zipWith_cons_cons, zw_aux r l, mul_add, mul_one]

theorem kerStep_eq (out : Array FE2) (r : FE2) : kerStep out r = out.map (· * (1 + r)) ++ out.map (· * r) := by
  apply Array.ext'
  rw [kerStep, Array.toList_append, Array.toList_zipWith, Array.toList_map, Array.toList_append, Array.toList_map,
    Array.toList_map]
  simp only [mulE_eq]
  rw [zw_aux]

theorem kerF_eq (p : List FE2) : kerF p = eqKernelAF p := by
  have h : kerStep = fun out r => out.map (· * (1 + r)) ++ out.map (· * r) := funext fun out => funext fun r =>
    kerStep_eq out r
  unfold kerF eqKernelAF
  rw [h]

/-- `mkSEq` with the fast kernel. -/
def mkSEqF (ρ : List FE2) : SEq FE2 :=
  ⟨decide (11 ≤ ρ.length), 2 ^ ρ.length, kerF (ρ.take 11), kerF (ρ.drop 11)⟩

theorem mkSEqF_eq (ρ : List FE2) : mkSEqF ρ = mkSEq ρ := by
  unfold mkSEqF mkSEq
  rw [kerF_eq, kerF_eq]

/-- `eq(ρ, i)` off a kernel `K` below `bnd` (`eqAtF` past it). -/
@[inline] def klF (K : Array FE2) (bnd : ℕ) (ρ : List FE2) (i : ℕ) : FE2 :=
  if i < bnd then K.getD i 0 else eqAtF ρ i

theorem klF_eq (K : Array FE2) (bnd : ℕ) (ρ : List FE2) (h : (K = eqKernelAF ρ ∧ bnd = 2 ^ ρ.length) ∨ bnd = 0)
    (i : ℕ) : klF K bnd ρ i = eqAtF ρ i := by
  unfold klF
  split
  · rename_i hi
    rcases h with ⟨rfl, rfl⟩ | h
    · rw [eqKernelAF_getD, if_pos hi]
    · omega
  · rfl

/-- The kernels of the prefixes `ρ.take k` for the `k` in `ks` (others empty), with their bounds. -/
def kerTab (ρ : List FE2) (ks : List ℕ) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k => if k ∈ ks then (kerF (ρ.take k), 2 ^ (ρ.take k).length) else (#[], 0)).toArray

theorem kerTab_ok (ρ : List FE2) (ks : List ℕ) (k : ℕ) :
    ((kerTab ρ ks).getD k (#[], 0)).1 = eqKernelAF (ρ.take k) ∧
        ((kerTab ρ ks).getD k (#[], 0)).2 = 2 ^ (ρ.take k).length ∨ ((kerTab ρ ks).getD k (#[], 0)).2 = 0 := by
  unfold kerTab
  by_cases hk : k < 22
  · rw [getD_mapRange 22 _ _ k hk]
    split
    · exact Or.inl ⟨kerF_eq _, rfl⟩
    · exact Or.inr rfl
  · right
    simp [Array.getD, hk]

/-- `eq(ρ.take k, i)` off a kernel table. -/
@[inline] def ktF (kt : Array (Array FE2 × ℕ)) (ρ : List FE2) (k i : ℕ) : FE2 :=
  let t := kt.getD k (#[], 0)
  klF t.1 t.2 (ρ.take k) i

theorem ktF_eq (ρ : List FE2) (ks : List ℕ) (k i : ℕ) : ktF (kerTab ρ ks) ρ k i = eqAtF (ρ.take k) i :=
  klF_eq _ _ _ (kerTab_ok ρ ks k) i

/-- `kerTab` with the prefix-`11` kernel given (`mkSEqF`'s low table: not built twice). -/
def kerTabS (ρ : List FE2) (ks : List ℕ) (K11 : Array FE2) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k =>
    if k ∈ ks then (if k = 11 then K11 else kerF (ρ.take k), 2 ^ (ρ.take k).length) else (#[], 0)).toArray

theorem ktFS_eq (ρ : List FE2) (ks : List ℕ) (K11 : Array FE2) (hK : K11 = kerF (ρ.take 11)) (k i : ℕ) :
    ktF (kerTabS ρ ks K11) ρ k i = eqAtF (ρ.take k) i := by
  apply klF_eq
  unfold kerTabS
  by_cases hk : k < 22
  · rw [getD_mapRange 22 _ _ k hk]
    split
    · left
      refine ⟨?_, rfl⟩
      split
      · rename_i h11; subst h11; rw [hK, kerF_eq]
      · exact kerF_eq _
    · exact Or.inr rfl
  · right
    simp [Array.getD, hk]

/-- `Σ_{j<n} f(j)` over the instances. -/
def sumN (f : ℕ → FE2) (n : ℕ) : FE2 := ((List.range n).map f).sum

/-- **`clsComb`, fast**: `Σ_j XM·YM` in closed form (`wPre`); the previous-instance and fixed-word sums on the
instance kernels only when their template sums are not zero. -/
def clsCombF (n : ℕ) (XL YL : List FE2) (XH YH V0 V1 V2 : FE2) : FE2 :=
  let D0 := if XL.length = YL.length ∧ n ≤ 2 ^ XL.length then (wPreH (hzip XL YL) n).1
    else dotN (eqAtF XL) (eqAtF YL) n
  let D1 := if V1 = 0 then 0 else
    let XK := kerF XL
    let YK := kerF YL
    ((List.range' 1 (n - 1)).map fun j =>
      mulE (klF XK (2 ^ XL.length) XL j) (klF YK (2 ^ YL.length) YL (j - 1))).sum
  let D2 := if V2 = 0 then 0 else
    let XK := kerF XL
    sumN (fun j => klF XK (2 ^ XL.length) XL j) n
  mulE XH (mulE YH (mulE D0 V0 + mulE D1 V1) + mulE D2 V2)

theorem clsCombF_eq (n : ℕ) (XL YL : List FE2) (XH YH V0 V1 V2 : FE2) :
    clsCombF n XL YL XH YH V0 V1 V2 = clsComb n (eqAtF XL) (eqAtF YL) XH YH V0 V1 V2 := by
  have hX : ∀ j, klF (kerF XL) (2 ^ XL.length) XL j = eqAtF XL j :=
    fun j => klF_eq _ _ _ (Or.inl ⟨kerF_eq _, rfl⟩) j
  have hY : ∀ j, klF (kerF YL) (2 ^ YL.length) YL j = eqAtF YL j :=
    fun j => klF_eq _ _ _ (Or.inl ⟨kerF_eq _, rfl⟩) j
  have h0 : (if XL.length = YL.length ∧ n ≤ 2 ^ XL.length then (wPreH (hzip XL YL) n).1
      else dotN (eqAtF XL) (eqAtF YL) n) = dotN (eqAtF XL) (eqAtF YL) n := by
    split
    · rename_i h
      rw [wPreH_eq, wPre_eq XL YL n h.1 h.2]
      rfl
    · rfl
  have h1 : (if V1 = 0 then 0 else ((List.range' 1 (n - 1)).map fun j =>
      klF (kerF XL) (2 ^ XL.length) XL j * klF (kerF YL) (2 ^ YL.length) YL (j - 1)).sum) * V1 =
      ((List.range' 1 (n - 1)).map fun j => eqAtF XL j * eqAtF YL (j - 1)).sum * V1 := by
    split
    · rename_i h; rw [h, mul_zero, mul_zero]
    · simp only [hX, hY]
  have h2 : (if V2 = 0 then 0 else sumN (fun j => klF (kerF XL) (2 ^ XL.length) XL j) n) * V2 =
      ((List.range n).map (eqAtF XL)).sum * V2 := by
    split
    · rename_i h; rw [h, mul_zero, mul_zero]
    · simp only [sumN, hX]
  unfold clsCombF clsComb
  simp only [mulE_eq]
  rw [h0, h1, h2]

/-! ## Affine kinds: loop classes and aligned externals (PHIV2) -/

/-- `Σ_{x<2q}` of a function of `x / 2` weighted by the parity of `x`. -/
theorem sum_range_pairG (g : ℕ → FE2) (h0 h1 : FE2) : ∀ q : ℕ,
    ((List.range (2 * q)).map fun x => (if x % 2 = 1 then h1 else h0) * g (x / 2)).sum =
      (h0 + h1) * ((List.range q).map g).sum
  | 0 => by simp
  | q + 1 => by
    have e1 : (2 * q) % 2 = 0 := by omega
    have e2 : (2 * q) / 2 = q := by omega
    have e3 : (2 * q + 1) % 2 = 1 := by omega
    have e4 : (2 * q + 1) / 2 = q := by omega
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, range_add1 (2 * q + 1), range_add1 (2 * q), range_add1 q,
      List.map_append, List.map_append, List.sum_append, List.sum_append, sum_range_pairG g h0 h1 q,
      List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e1, e2, e3, e4, if_true,
      show (0 : ℕ) ≠ 1 from by decide, if_false]
    ring

/-- **`eq` sums to `1` over the cube.** -/
theorem eqSum_one : ∀ p : List FE2, ((List.range (2 ^ p.length)).map (eqAtF p)).sum = 1
  | [] => by simp
  | r :: rs => by
    have h := sum_range_pairG (eqAtF rs) (1 + r) r (2 ^ rs.length)
    rw [List.length_cons, pow_succ, mul_comm]
    have hP : ∀ x, eqAtF (r :: rs) x = (if x % 2 = 1 then r else 1 + r) * eqAtF rs (x / 2) := fun x => by
      rw [eqAtF_succ]
    rw [show eqAtF (r :: rs) = (fun x => (if x % 2 = 1 then r else 1 + r) * eqAtF rs (x / 2)) from funext hP, h,
      eqSum_one rs, mul_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- `eq` at `x + j·2^a` when the bits `[a, a + L)` of `x` are zero. -/
theorem eq_split3x (p : List FE2) (x a L j : ℕ) (hx : x / 2 ^ a % 2 ^ L = 0) (hj : j < 2 ^ L)
    (hl : a + L ≤ p.length) :
    eqAtF p (x + j * 2 ^ a) =
      eqAtF (p.take a) (x % 2 ^ a) * (eqAtF ((p.drop a).take L) j * eqAtF ((p.drop a).drop L) (x / 2 ^ (a + L))) := by
  obtain ⟨r, hr⟩ : 2 ^ L ∣ x / 2 ^ a := Nat.dvd_of_mod_eq_zero hx
  have hu : x % 2 ^ a < 2 ^ a := Nat.mod_lt _ (by positivity)
  have hxe : x = 2 ^ (a + L) * r + x % 2 ^ a := by
    have := Nat.div_add_mod x (2 ^ a)
    rw [hr, pow_add] at *
    linarith [this]
  have hb : (2 ^ (a + L) * r) % 2 ^ (a + L) = 0 := Nat.mul_mod_right _ _
  have hd : x / 2 ^ (a + L) = r := by
    rw [hxe, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (lt_of_lt_of_le hu (Nat.pow_le_pow_right
      (by norm_num) (by omega))), add_zero]
  have h3 := eq_split3 p (2 ^ (a + L) * r) a L j (x % 2 ^ a) hb hu hj hl
  rw [Nat.mul_div_cancel_left r (by positivity)] at h3
  rw [hd, ← h3]
  congr 1
  omega

/-- `Σ_j Σ_t = Σ_t Σ_j`. -/
theorem sum_swap {α : Type} (f : ℕ → α → FE2) (n : ℕ) : ∀ l : List α,
    ((List.range n).map fun j => (l.map (f j)).sum).sum = (l.map fun t => ((List.range n).map fun j => f j t).sum).sum
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [← sum_swap f n l, ← List.sum_map_add]

/-- **An affine entry**: coefficient `c`, matrix `o`, word `y`; at instance `j` the word `y` (`fx`: a fixed word)
or `y + j·2^e` (`e = ds[ek]`). -/
structure AE where
  c : FE2
  o : ℕ
  y : ℕ
  fx : Bool
  ek : ℕ
  deriving Inhabited

/-- **An affine kind** (LAY3's loop classes: `n = 2^l` at `a = 0`, words `w + jf` (`e = 0`), `w` (fixed) or
`w + jf·2^e`; a class's aligned externals `d = 3`): `n` instances on the slot bits `[a, a + L)`; per base slot `x`
(a row) its entries, at instance `j` on the slot `x + j·2^a`; word strides `2^e` for `e ∈ ds`. -/
structure AK where
  a : ℕ
  L : ℕ
  n : ℕ
  ds : Array ℕ
  rows : Array (ℕ × Array AE)
  deriving Inhabited

/-- An entry's word stride `log₂`. -/
def AK.e (k : AK) (t : AE) : ℕ := k.ds.getD t.ek 0

/-- An entry's word at instance `j`. -/
def AK.wd (k : AK) (t : AE) (j : ℕ) : ℕ := if t.fx then t.y else t.y + j * 2 ^ k.e t

/-- The entries of a row at instance `j`. -/
def AK.rowEnts (k : AK) (j : ℕ) (r : ℕ × Array AE) : List Q4 :=
  r.2.toList.map fun t => (t.c, t.o, r.1 + j * 2 ^ k.a, k.wd t j)

/-- **The kind's entries.** -/
def AK.ents (k : AK) : List Q4 := (List.range k.n).flatMap fun j => k.rows.toList.flatMap (k.rowEnts j)

/-- **The kind's start-up check**: the instance bits inside the slot point, free in every base slot and every
strided word. -/
def AK.okB (k : AK) : Bool :=
  decide (k.a + k.L ≤ 20) && decide (k.n ≤ 2 ^ k.L) &&
    k.rows.toList.all fun r => r.1 / 2 ^ k.a % 2 ^ k.L == 0 &&
      r.2.toList.all fun t => t.fx || (decide (k.e t + k.L ≤ 21) && t.y / 2 ^ k.e t % 2 ^ k.L == 0)

/-- The instance bits of the slot point. -/
def AK.XL (k : AK) (m : List FE2) : List FE2 := (m.drop k.a).take k.L

/-- A base slot's weight off the instance bits. -/
def AK.MX (k : AK) (m : List FE2) (x : ℕ) : FE2 :=
  eqAtF (m.take k.a) (x % 2 ^ k.a) * eqAtF ((m.drop k.a).drop k.L) (x / 2 ^ (k.a + k.L))

/-- A word's weight off the bits `[e, e + L)`. -/
def AK.WY (k : AK) (b : List FE2) (e y : ℕ) : FE2 :=
  eqAtF (b.take e) (y % 2 ^ e) * eqAtF ((b.drop e).drop k.L) (y / 2 ^ (e + k.L))

/-- `Σ_{j<n} eq(x_mid, j)·eq(y_[e, e+L), j)` in closed form. -/
def AK.D (k : AK) (m b : List FE2) (e : ℕ) : FE2 := (wPreH (hzip (k.XL m) ((b.drop e).take k.L)) k.n).1

/-- `Σ_{j<n} eq(x_mid, j)` (`1` on the full cube). -/
def AK.S (k : AK) (m : List FE2) : FE2 :=
  if k.n = 2 ^ (k.XL m).length then 1 else sumN (eqAtF (k.XL m)) k.n

/-- `c·v`, the product skipped at `c = 1`. -/
@[inline] def cmulE (c v : FE2) : FE2 := if c = 1 then v else mulE c v

theorem cmulE_eq (c v : FE2) : cmulE c v = c * v := by
  unfold cmulE
  split
  · rename_i h; rw [h, one_mul]
  · exact mulE_eq c v

/-- PHIV7: `c = 1` by the words (no `DecidableEq` call). -/
@[inline] def isOne (c : FE2) : Bool := c.re.val == 1 && c.im.val == 0

theorem isOne_eq (c : FE2) (h : isOne c = true) : c = 1 := by
  obtain ⟨⟨r⟩, ⟨i⟩⟩ := c
  simp only [isOne, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- PHIV7: `a·b`, the product skipped when a factor is `1`. -/
@[inline] def mul1 (a b : FE2) : FE2 := if isOne a then b else if isOne b then a else mulE a b

theorem mul1_eq (a b : FE2) : mul1 a b = a * b := by
  unfold mul1
  split
  · rename_i h; rw [isOne_eq a h, one_mul]
  · split
    · rename_i h; rw [isOne_eq b h, mul_one]
    · exact mulE_eq a b

/-- PHIV7: `c·v` for a single's coefficient: skipped at `c = 1`, else the out-of-line product `FE2.mul` (keeps the
singles' loop body small; measured no slower than inlining `mulE` there). -/
@[inline] def cmulO (c v : FE2) : FE2 := if isOne c then v else c * v

theorem cmulO_eq (c v : FE2) : cmulO c v = c * v := by
  unfold cmulO
  split
  · rename_i h; rw [isOne_eq c h, one_mul]
  · rfl

/-! ## PHIV7: grouped sums (flush on a change of group) -/

/-- **The grouped fold** of `es` from `i` on: `inner` sums `g t` over the current run of items `same` as the
representative `r`; at a change `F r inner` goes to `outer` and the item becomes the representative. -/
@[specialize] def flushGo {α : Type} (es : Array α) (same : α → α → Bool) (g : α → FE2) (F : α → FE2 → FE2)
    (i : ℕ) (r : α) (inner outer : FE2) : FE2 :=
  if h : i < es.size then
    if same r es[i] then flushGo es same g F (i + 1) r (inner + g es[i]) outer
    else flushGo es same g F (i + 1) es[i] (g es[i]) (outer + F r inner)
  else outer + F r inner
termination_by es.size - i

/-- **`Σ_t F t (g t)`, grouped**: `F` once per run of `same` items (any order; sorted inputs make few runs). -/
@[specialize] def flushSum {α : Type} (es : Array α) (same : α → α → Bool) (g : α → FE2) (F : α → FE2 → FE2) :
    FE2 :=
  if h : 0 < es.size then flushGo es same g F 1 es[0] (g es[0]) 0 else 0

section Grouped

variable {α : Type} (es : Array α) (same : α → α → Bool) (g : α → FE2) (F : α → FE2 → FE2)
  (hadd : ∀ r x y, F r (x + y) = F r x + F r y) (hsame : ∀ r t, same r t = true → ∀ v, F r v = F t v)

include hadd hsame in
theorem flushGo_eq : ∀ (d i : ℕ) (r : α) (inner outer : FE2), es.size - i = d →
    flushGo es same g F i r inner outer = outer + F r inner + ((es.toList.drop i).map fun t => F t (g t)).sum
  | 0, i, r, inner, outer, hd => by
    rw [flushGo, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | d + 1, i, r, inner, outer, hd => by
    have hi : i < es.size := by omega
    rw [flushGo, dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [Array.getElem_toList, List.map_cons, List.sum_cons]
    split
    · rename_i hs
      rw [flushGo_eq d (i + 1) _ _ _ (by omega), hadd, hsame r es[i] hs (g es[i])]
      abel
    · rw [flushGo_eq d (i + 1) _ _ _ (by omega)]
      abel

include hadd hsame in
/-- **The grouped fold is the plain sum**, whatever the order of `es`. -/
theorem flushSum_eq : flushSum es same g F = (es.toList.map fun t => F t (g t)).sum := by
  unfold flushSum
  split
  · rename_i h
    have hc := List.drop_eq_getElem_cons (l := es.toList) (i := 0) (by simpa using h)
    rw [List.drop_zero] at hc
    rw [flushGo_eq es same g F hadd hsame _ 1 _ _ _ rfl, zero_add]
    conv_rhs => rw [hc]
    simp [Array.getElem_toList]
  · rename_i h
    have h0 : es.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
    simp [h0]

end Grouped

/-- PHIV7: **the singles grouped** by matrix `o` and word key `key y`, with `fw y = hw (key y) · lw y`: per single
`c·fs(x)·lw(y)` (one product at `c = 1`), per group `fa(o)·hw(key)` once. -/
@[specialize] def sglSumK (sg : Array CSgl) (fa fs : ℕ → FE2) (key : ℕ → ℕ) (hw lw : ℕ → FE2) : FE2 :=
  flushSum sg (fun r t => r.o == t.o && key r.y == key t.y) (fun t => cmulO t.c (mulE (fs t.x) (lw t.y)))
    (fun r v => mulE (fa r.o) (mulE (hw (key r.y)) v))

theorem sglSumK_eq (sg : Array CSgl) (fa fs fw : ℕ → FE2) (key : ℕ → ℕ) (hw lw : ℕ → FE2)
    (h : ∀ y, fw y = hw (key y) * lw y) : sglSumK sg fa fs key hw lw = sglSum sg fa fs fw := by
  unfold sglSumK
  rw [flushSum_eq, sglSum_eq]
  · refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
    simp only [mulE_eq, cmulO_eq, h]
    ring
  · intro r x y
    simp only [mulE_eq]
    ring
  · intro r t hs v
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1, hs.2]

theorem bkSum_nil (b : FBk) (SK WK : Array ℕ) (SV WV : Array FE2) (fs fw : ℕ → FE2) (h : b.gk.size = 0) :
    bkSum b SK WK SV WV fs fw = 0 := by
  unfold bkSum
  split <;> rw [bkGo_zero, h] <;> simp

/-- PHIV7: `flatSumG` with the singles grouped (`sglSumK`) and empty buckets skipped. -/
@[specialize] def flatSumK (ft : FCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov : ℕ → FE2) (SV CV OV : Array FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) : FE2 :=
  (List.range 8).foldl (fun s β =>
    if (ft.bk.getD β default).gk.size = 0 then s else
    s + fa (β / 2) * ((if β % 2 == 1 then T else 1) *
      (if β % 2 == 1 then bkSum (ft.bk.getD β default) ft.slots ft.als SV CV fs fcv
        else bkSum (ft.bk.getD β default) ft.slots ft.ods SV OV fs fov))) 0 +
    sglSumK ft.sgl fa fs key hw lw

theorem flatSumK_eq (ft : FCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (SV CV OV : Array FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) (h : ∀ y, fw y = hw (key y) * lw y) :
    flatSumK ft fa T fs fcv fov SV CV OV key hw lw = flatSumG ft fa T fs fcv fov fw SV CV OV := by
  unfold flatSumK flatSumG
  rw [sglSumK_eq _ _ _ fw _ _ _ h]
  congr 1
  refine congrArg (fun f => List.foldl f 0 (List.range 8)) (funext fun s => funext fun β => ?_)
  split
  · rename_i h0
    rw [bkSum_nil _ _ _ _ _ _ _ h0, bkSum_nil _ _ _ _ _ _ _ h0]
    simp
  · rfl

/-- PHIV7: `rsum` with `flatSumK`, and the factors of `wPre` built only when there are `W` runs. -/
@[specialize] def rsumK (rc : RCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (ms bs : List FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) : FE2 :=
  let needS := rc.fc.bk.any fun b => !b.byRow && decide (0 < b.gk.size)
  let needC := rc.fc.bk.any fun b => b.byRow
  let fl := flatSumK rc.fc fa T fs fcv fov (if needS = true then rc.fc.slots.map fs else #[])
    (if needC = true then rc.fc.als.map fcv else #[]) (if needC = true then rc.fc.ods.map fov else #[]) key hw lw
  if rc.wr.size = 0 then fl
  else
    let hz := hzip ms bs
    fl + rc.wr.foldl (fun s r => s + runSumH hz fa T fs fcv fw ms bs r) 0

theorem rsumK_eq (rc : RCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (ms bs : List FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) (h : ∀ y, fw y = hw (key y) * lw y) :
    rsumK rc fa T fs fcv fov fw ms bs key hw lw = rsum rc fa T fs fcv fov fw ms bs := by
  unfold rsumK rsum
  simp only [flatSumK_eq _ _ _ _ _ _ fw _ _ _ _ _ _ h]
  split
  · rename_i h0
    have : rc.wr = #[] := Array.eq_empty_of_size_eq_zero h0
    simp [this]
  · rfl

/-- A row's sum off its slot weight. -/
@[specialize] def AK.rowW (k : AK) (fa fw : ℕ → FE2) (wy : ℕ → ℕ → FE2) (S : FE2) (Dv : Array FE2) (D : ℕ → FE2)
    (es : Array AE) : FE2 :=
  es.foldl (fun s t => s + mulE (cmulE t.c (fa t.o))
    (if t.fx then mulE S (fw t.y) else mulE (rd Dv k.ds D t.ek) (wy t.ek t.y))) 0

/-- **The kind's value** with its weights (`fa` matrices, `fw` fixed words, `mx` base slots, `wy i` the words of
stride `ds[i]`, `S`,
the stride sums `Dv` of `ds`, `D` past it). -/
@[specialize] def AK.valW (k : AK) (fa fw mx : ℕ → FE2) (wy : ℕ → ℕ → FE2) (S : FE2) (Dv : Array FE2)
    (D : ℕ → FE2) : FE2 :=
  k.rows.foldl (fun s r => s + mulE (mx r.1) (k.rowW fa fw wy S Dv D r.2)) 0

/-- PHIV7: **`AK.rowW` grouped**. A strided word's weight splits as `wy i y = wlo i y · whi i (hk i y)` (low bits
and high part). Fixed lines of equal `o`, and strided lines of equal `(o, ek)` and high part `hk`, form a group.
Per line `c·wlo` (fixed words `c·fw`), at most one product; per group `faw(o, ek)·(whi·Σ)` (`faw o i = fa(o)·W_i`,
`W_i` the stride sum) or `fa(o)·(S·Σ)` for fixed words. -/
@[specialize] def AK.rowW2 (fa fw : ℕ → FE2) (faw : ℕ → ℕ → FE2) (wlo : ℕ → ℕ → FE2) (hk : ℕ → ℕ → ℕ)
    (whi : ℕ → ℕ → FE2) (S : FE2) (es : Array AE) : FE2 :=
  flushSum es (fun r t => r.fx == t.fx && r.o == t.o && (t.fx || (r.ek == t.ek && hk r.ek r.y == hk t.ek t.y)))
    (fun t => mul1 t.c (if t.fx then fw t.y else wlo t.ek t.y))
    (fun r v => if r.fx then mulE (fa r.o) (mul1 S v) else mulE (faw r.o r.ek) (mulE (whi r.ek (hk r.ek r.y)) v))

theorem AK.rowW2_eq (k : AK) (fa fw : ℕ → FE2) (faw : ℕ → ℕ → FE2) (wy wlo : ℕ → ℕ → FE2) (hk : ℕ → ℕ → ℕ)
    (whi : ℕ → ℕ → FE2) (S : FE2) (Dv : Array FE2) (D : ℕ → FE2) (hw : ∀ i y, wy i y = wlo i y * whi i (hk i y))
    (hfaw : ∀ o i, faw o i = fa o * rd Dv k.ds D i) (es : Array AE) :
    AK.rowW2 fa fw faw wlo hk whi S es = k.rowW fa fw wy S Dv D es := by
  unfold AK.rowW2 AK.rowW
  rw [flushSum_eq, ← Array.foldl_toList, foldl_add_eq, zero_add]
  · refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    by_cases hf : t.fx <;> simp only [hf, if_true, Bool.false_eq_true, if_false, mulE_eq, cmulE_eq, mul1_eq, hw,
      hfaw] <;> ring
  · intro r x y
    split <;> simp only [mulE_eq, mul1_eq] <;> ring
  · intro r t hs v
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hs
    obtain ⟨⟨hfx, ho⟩, hh⟩ := hs
    by_cases hf : t.fx
    · simp only [hfx, hf, ho, if_true]
    · rcases hh with hh | ⟨hek, hh⟩
      · exact absurd hh hf
      · simp only [hfx, hf, ho, Bool.false_eq_true, if_false]
        rw [hh, hek]

/-- PHIV7: `AK.valW` with `rowW2`. -/
@[specialize] def AK.valW2 (k : AK) (fa fw mx : ℕ → FE2) (faw : ℕ → ℕ → FE2) (wlo : ℕ → ℕ → FE2) (hk : ℕ → ℕ → ℕ)
    (whi : ℕ → ℕ → FE2) (S : FE2) : FE2 :=
  k.rows.foldl (fun s r => s + mulE (mx r.1) (AK.rowW2 fa fw faw wlo hk whi S r.2)) 0

theorem AK.valW2_eq (k : AK) (fa fw mx : ℕ → FE2) (faw : ℕ → ℕ → FE2) (wy wlo : ℕ → ℕ → FE2) (hk : ℕ → ℕ → ℕ)
    (whi : ℕ → ℕ → FE2) (S : FE2) (Dv : Array FE2) (D : ℕ → FE2) (hw : ∀ i y, wy i y = wlo i y * whi i (hk i y))
    (hfaw : ∀ o i, faw o i = fa o * rd Dv k.ds D i) :
    k.valW2 fa fw mx faw wlo hk whi S = k.valW fa fw mx wy S Dv D := by
  unfold AK.valW2 AK.valW
  simp only [AK.rowW2_eq k fa fw faw wy wlo hk whi S Dv D hw hfaw]

/-- **The kind's value at a point** (`eq` of the slot and word parts directly). -/
def AK.val (k : AK) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2) : FE2 :=
  k.valW fa fw (k.MX m) (fun i y => k.WY b (k.ds.getD i 0) y) (k.S m) (k.ds.map (k.D m b)) (k.D m b)

section AKind

variable (k : AK) (fa : ℕ → FE2) (m b : List FE2)

theorem AK.S_eq : k.S m = sumN (eqAtF (k.XL m)) k.n := by
  unfold AK.S
  split
  · rename_i h
    rw [h, sumN, eqSum_one]
  · rfl

theorem AK.D_eq (hm : k.a + k.L ≤ m.length) (e : ℕ) (he : e + k.L ≤ b.length) (hn : k.n ≤ 2 ^ k.L) :
    k.D m b e = dotN (eqAtF (k.XL m)) (eqAtF ((b.drop e).take k.L)) k.n := by
  have h1 : (k.XL m).length = k.L := by simp [AK.XL]; omega
  have h2 : ((b.drop e).take k.L).length = k.L := by simp; omega
  unfold AK.D
  rw [wPreH_eq, wPre_eq _ _ _ (by rw [h1, h2]) (by rw [h1]; exact hn)]
  rfl

/-- **An affine kind is the sum of its entries.** -/
theorem AK.valW_eq (hok : k.okB = true) (hm : m.length = 20) (hb : b.length = 21) (fw mx : ℕ → FE2)
    (wy : ℕ → ℕ → FE2) (S : FE2) (Dv : Array FE2) (D : ℕ → FE2) (hfw : ∀ y, fw y = eqAtF b y)
    (hmx : ∀ x, mx x = k.MX m x) (hwy : ∀ i y, wy i y = k.WY b (k.ds.getD i 0) y) (hS : S = k.S m)
    (hDv : Dv = k.ds.map (k.D m b)) (hD : D = k.D m b) :
    k.valW fa fw mx wy S Dv D = (k.ents.map (qv fa (eqAtF m) (eqAtF b))).sum := by
  simp only [AK.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨haL, hn⟩, hrows⟩ := hok
  subst hDv hD hS
  unfold AK.valW AK.ents
  rw [← Array.foldl_toList, foldl_add_eq, zero_add, sum_map_flatMap]
  simp only [sum_map_flatMap]
  rw [sum_swap (fun j r => ((k.rowEnts j r).map (qv fa (eqAtF m) (eqAtF b))).sum)]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  obtain ⟨hx, hes⟩ := hrows r hr
  have hXM : ∀ j, j ∈ List.range k.n → eqAtF m (r.1 + j * 2 ^ k.a) = k.MX m r.1 * eqAtF (k.XL m) j := by
    intro j hj
    rw [eq_split3x m r.1 k.a k.L j hx (lt_of_lt_of_le (List.mem_range.mp hj) hn) (by omega)]
    unfold AK.MX AK.XL
    ring
  unfold AK.rowW AK.rowEnts
  rw [← Array.foldl_toList, foldl_add_eq, zero_add, mulE_eq, hmx, ← List.sum_map_mul_left]
  simp only [List.map_map, Function.comp_def]
  rw [sum_swap (fun j t => qv fa (eqAtF m) (eqAtF b) (t.c, t.o, r.1 + j * 2 ^ k.a, k.wd t j))]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have hy := hes t ht
  simp only [Function.comp_apply, mulE_eq, cmulE_eq, rd_map]
  by_cases hf : t.fx
  · simp only [hf, if_true, AK.wd, qv, hfw]
    rw [AK.S_eq k m, sumN, ← List.sum_map_mul_right, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [hXM j hj]
    ring
  · simp only [hf, Bool.false_eq_true, if_false, AK.wd, qv, hwy, false_or] at hy ⊢
    obtain ⟨he, hy0⟩ := hy
    rw [show (k.ds.getD t.ek 0) = k.e t from rfl, AK.D_eq k m b (by omega) _ (by omega) hn, dotN,
      ← List.sum_map_mul_right, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have hj' : j < 2 ^ k.L := lt_of_lt_of_le (List.mem_range.mp hj) hn
    rw [hXM j hj, eq_split3x b t.y (k.e t) k.L j hy0 hj' (by omega)]
    unfold AK.WY AK.XL
    ring

theorem AK.val_eq (hok : k.okB = true) (hm : m.length = 20) (hb : b.length = 21) :
    k.val fa m b (eqAtF b) = (k.ents.map (qv fa (eqAtF m) (eqAtF b))).sum :=
  k.valW_eq fa m b hok hm hb _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rfl rfl rfl

end AKind

/-- (a hint) The affine kind of entries `(o, x, d, w, c, e)` on `n` instances of the slot bits `[a, a + L)`:
`d = 2` the fixed word `w`, else the word `w + j·2^e`; rows by base slot `x`. -/
def AK.ofEnts (a L n : ℕ) (es : List (ℕ × ℕ × ℕ × ℕ × FE2 × ℕ)) : AK := Id.run do
  let ds := (es.filterMap fun e => if e.2.2.1 = 2 then none else some e.2.2.2.2.2).eraseDups.toArray
  let xs := ((es.map (·.2.1)).eraseDups.toArray.qsort (· < ·))
  let mut rows : Array (ℕ × Array AE) := #[]
  for x in xs do
    let r := (es.filter (·.2.1 = x)).map fun e =>
      (⟨e.2.2.2.2.1, e.1, e.2.2.2.1, e.2.2.1 = 2, ds.idxOf e.2.2.2.2.2⟩ : AE)
    rows := rows.push (x, r.toArray)
  return ⟨a, L, n, ds, rows⟩

end Lvm6.V
