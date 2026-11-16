import LvmQLinkArith
import LvmQLinkArithRead

-- ===== merged from `LvmQLinkArithRows` (GOLF module merge: `LvmQLinkArithRows.lean` is now a stub importing `LvmQLinkArithKS`) =====
section

/-!
# QA1 links: row combinators for the link circuits

Template combinators (`Ins` lists at an absolute position, QA1's `Fix` semantics, `LvmQSumcheckCore`) and
their values on any fixed point:

* `eqTabGo`: `eqKernel` itself, one level per coordinate (a `lin` for `1 + r`, then `2^k` rows
  `old·(1 + r)` and `2^k` rows `old·r`); **`eqTab_val`**: the last level's values are
  `rs.foldl eqStep olds` (so `eqKernel` of the point when `olds = [1]`);
* `mulChainIns` (`s·c₀·c₁…`), `dotIns` (`s + Σ aᵢbᵢ`), with `mulChain_val`, `dot_val`;
* `shiftRecIns`: `(eqEval, shiftEval)` from the last coordinate down (`shiftEval_cons`), 8 rows
  per coordinate; **`shiftRec_val`**;
* `preRecIns`: `preCF` for a static bound, 12 rows per coordinate; **`preRec_val`**.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## Generic helpers -/

theorem fix_seg {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat}
    {seg : List Ins} (hseg : Seg ins n seg) (hlen : n + seg.length ≤ ins.length) {i : Nat}
    (hi : i < seg.length) (hw : (seg.getD i default).op ≠ .assert0) :
    V.getD (n + i) 0 = (seg.getD i default).eval xv V :=
  fix_at hF (by (clear * - hlen hi; omega)) (hseg i hi) hw

theorem seg_cons_tail {ins : List Ins} {n : Nat} {a : Ins} {seg : List Ins} (h : Seg ins n (a :: seg)) :
    Seg ins (n + 1) seg := seg_sub h [a] seg rfl

theorem seg_append_left {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) : Seg ins n A := by
  intro i hi
  rw [h i (by simp; (clear * - hi; omega)), List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    ← List.getD_eq_getElem?_getD]

theorem seg_append_right {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) :
    Seg ins (n + A.length) B := seg_sub h A B rfl

theorem getD_range_map {α : Type} [Inhabited α] (f : Nat → α) {k i : Nat} (hi : i < k) :
    ((List.range k).map f).getD i default = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem list_ext_getD (l l' : List FE) (h : l.length = l'.length)
    (h' : ∀ i < l.length, l.getD i 0 = l'.getD i 0) : l = l' := by
  apply List.ext_getElem h
  intro i h1 h2
  have := h' i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem getD_map_lt (f : Src → FE) (l : List Src) {i : Nat} (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i default) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

@[simp] theorem val_loc (xv : Src → FE) (V : List FE) (k : Nat) : (Src.loc k).val xv V = V.getD k 0 := rfl

theorem eval_linI' (xv : Src → FE) (V : List FE) (k k' : FK) (a b : Src) :
    (linI k k' a b).eval xv V = a.val xv V + FE.ofK k * b.val xv V + FE.ofK k' := rfl

/-! ## `eqKernel` -/

/-- One level's rows at `n`: `1 + r`, then `old_i·(1 + r)`, then `old_i·r`. -/
def eqLevelIns (zero : Src) (n : Nat) (olds : List Src) (r : Src) : List Ins :=
  linI 0 1 r r :: (List.range (2 * olds.length)).map fun i =>
    if i < olds.length then mulI (olds.getD i default) (.loc n) zero
    else mulI (olds.getD (i - olds.length) default) r zero

/-- The level's results. -/
def eqLevelOut (n m : Nat) : List Src := (List.range (2 * m)).map fun i => .loc (n + 1 + i)

/-- **The `eq` table of a point**, from the table `olds` (`[1]` for `eqKernel`). -/
def eqTabGo (zero : Src) : Nat → List Src → List Src → List Ins
  | _, _, [] => []
  | n, olds, r :: rs => eqLevelIns zero n olds r ++ eqTabGo zero (n + 1 + 2 * olds.length) (eqLevelOut n olds.length) rs

/-- Where the table's values are. -/
def eqTabOut : Nat → List Src → List Src → List Src
  | _, olds, [] => olds
  | n, olds, _ :: rs => eqTabOut (n + 1 + 2 * olds.length) (eqLevelOut n olds.length) rs

theorem eqLevelIns_length (zero : Src) (n : Nat) (olds : List Src) (r : Src) :
    (eqLevelIns zero n olds r).length = 1 + 2 * olds.length := by
  simp [eqLevelIns]; omega

theorem eqLevel_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) {n : Nat} {olds : List Src} {r : Src} (hseg : Seg ins n (eqLevelIns zero n olds r))
    (hlen : n + 1 + 2 * olds.length ≤ ins.length) :
    (eqLevelOut n olds.length).map (Src.val xv V) = eqStep (olds.map (Src.val xv V)) (r.val xv V) := by
  have hL := eqLevelIns_length zero n olds r
  have h0 : V.getD n 0 = 1 + r.val xv V := by
    have := fix_seg hF hseg (by (clear * - hlen hL; omega)) (i := 0) (by (clear * - hL; omega)) (by simp [eqLevelIns, linI])
    rw [Nat.add_zero] at this
    rw [this]
    simp only [eqLevelIns, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]; ring
  apply list_ext_getD
  · simp [eqLevelOut, eqStep_length]
  · intro i hi
    have hi' : i < 2 * olds.length := by simpa [eqLevelOut] using hi
    have hrow : (eqLevelIns zero n olds r).getD (i + 1) default =
        if i < olds.length then mulI (olds.getD i default) (.loc n) zero
        else mulI (olds.getD (i - olds.length) default) r zero := by
      simp only [eqLevelIns, List.getD_cons_succ]
      exact getD_range_map _ hi'
    have hv := fix_seg hF hseg (by (clear * - hlen hL; omega)) (i := i + 1) (by (clear * - hL hi'; omega)) (by rw [hrow]; split <;> simp [mulI])
    rw [eqStep_getD _ _ (by simpa using hi'), List.length_map,
      getD_map_lt _ _ (by simpa [eqLevelOut] using hi)]
    simp only [eqLevelOut]
    rw [getD_range_map _ hi']
    show V.getD (n + 1 + i) 0 = _
    rw [show n + 1 + i = n + (i + 1) by (clear * -; omega), hv, hrow]
    split
    · rename_i hlt
      rw [eval_mulI, hz, add_zero, getD_map_lt _ _ hlt]
      show _ * V.getD n 0 = _
      rw [h0]
    · rename_i hlt
      rw [eval_mulI, hz, add_zero, getD_map_lt _ _ (by (clear * - hi' hlt; omega))]

theorem eqTab_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) : ∀ (rs : List Src) (n : Nat) (olds : List Src),
    Seg ins n (eqTabGo zero n olds rs) → n + (eqTabGo zero n olds rs).length ≤ ins.length →
    (eqTabOut n olds rs).map (Src.val xv V) = (rs.map (Src.val xv V)).foldl eqStep (olds.map (Src.val xv V))
  | [], n, olds, _, _ => rfl
  | r :: rs, n, olds, hseg, hlen => by
    have hL := eqLevelIns_length zero n olds r
    simp only [eqTabGo, List.length_append] at hseg hlen
    have h1 := eqLevel_val hF hz (seg_append_left hseg) (by (clear * - hL hlen; omega))
    have h2 := seg_append_right hseg
    rw [hL, show n + (1 + 2 * olds.length) = n + 1 + 2 * olds.length by (clear * -; omega)] at h2
    have ih := eqTab_val hF hz rs (n + 1 + 2 * olds.length) (eqLevelOut n olds.length) h2 (by (clear * - hL hlen; omega))
    simp only [eqTabOut, List.map_cons, List.foldl_cons]
    rw [ih, h1]

/-! ## Chains -/

/-- `s·c₀·c₁·…`, one `muladd` per factor (`zero` the addend). -/
def mulChainIns (zero : Src) : Nat → Src → List Src → List Ins
  | _, _, [] => []
  | n, s, c :: cs => mulI s c zero :: mulChainIns zero (n + 1) (.loc n) cs

theorem mulChainIns_length (zero : Src) : ∀ (n : Nat) (s : Src) (cs : List Src),
    (mulChainIns zero n s cs).length = cs.length
  | _, _, [] => rfl
  | n, s, c :: cs => by simp [mulChainIns, mulChainIns_length zero (n + 1) (.loc n) cs]

theorem mulChain_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) : ∀ (cs : List Src) (n : Nat) (s : Src), Seg ins n (mulChainIns zero n s cs) →
    n + cs.length ≤ ins.length → (sumSrc n s cs).val xv V = s.val xv V * (cs.map (Src.val xv V)).prod
  | [], n, s, _, _ => by simp [sumSrc]
  | c :: cs, n, s, hseg, hlen => by
    have h0 : V.getD n 0 = s.val xv V * c.val xv V := by
      have := fix_seg hF hseg (by rw [mulChainIns_length]; simpa using hlen) (i := 0) (by simp [mulChainIns])
        (by simp [mulChainIns, mulI])
      rw [Nat.add_zero] at this
      rw [this]
      simp [mulChainIns, eval_mulI, hz]
    have ih := mulChain_val hF hz cs (n + 1) (.loc n) (seg_cons_tail hseg) (by simp at hlen; (clear * - hlen; omega))
    have hs : sumSrc n s (c :: cs) = sumSrc (n + 1) (.loc n) cs := by
      cases cs with
      | nil => simp [sumSrc]
      | cons _ _ => simp [sumSrc]; (clear * -; omega)
    rw [hs, ih]
    show V.getD n 0 * _ = _
    rw [h0, List.map_cons, List.prod_cons, mul_assoc]

/-- `s + a₀b₀ + a₁b₁ + …`, one `muladd` per pair. -/
def dotIns : Nat → Src → List (Src × Src) → List Ins
  | _, _, [] => []
  | n, s, (a, b) :: ps => mulI a b s :: dotIns (n + 1) (.loc n) ps

/-- Where the dot product is. -/
def dotSrc (n : Nat) (s : Src) (ps : List (Src × Src)) : Src := if ps = [] then s else .loc (n + ps.length - 1)

theorem dotIns_length : ∀ (n : Nat) (s : Src) (ps : List (Src × Src)), (dotIns n s ps).length = ps.length
  | _, _, [] => rfl
  | n, s, (a, b) :: ps => by simp [dotIns, dotIns_length (n + 1) (.loc n) ps]

theorem dot_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) :
    ∀ (ps : List (Src × Src)) (n : Nat) (s : Src), Seg ins n (dotIns n s ps) → n + ps.length ≤ ins.length →
    (dotSrc n s ps).val xv V = s.val xv V + (ps.map fun ab => ab.1.val xv V * ab.2.val xv V).sum
  | [], n, s, _, _ => by simp [dotSrc]
  | (a, b) :: ps, n, s, hseg, hlen => by
    have h0 : V.getD n 0 = a.val xv V * b.val xv V + s.val xv V := by
      have := fix_seg hF hseg (by rw [dotIns_length]; simpa using hlen) (i := 0) (by simp [dotIns])
        (by simp [dotIns, mulI])
      rw [Nat.add_zero] at this
      rw [this]
      simp [dotIns, eval_mulI]
    have ih := dot_val hF ps (n + 1) (.loc n) (seg_cons_tail hseg) (by simp at hlen; (clear * - hlen; omega))
    have hs : dotSrc n s ((a, b) :: ps) = dotSrc (n + 1) (.loc n) ps := by
      cases ps with
      | nil => simp [dotSrc]
      | cons _ _ => simp [dotSrc]; (clear * -; omega)
    rw [hs, ih]
    show V.getD n 0 + _ = _
    rw [h0, List.map_cons, List.sum_cons]
    ring

/-! ## The shift kernel, from the last coordinate down -/

/-- The 8 rows of one coordinate at `m`, from the tail's `eqEval` (`Et`) and `shiftEval` (`St`). -/
def shiftLevel (zero : Src) (m : Nat) (x0 y0 Et St : Src) : List Ins :=
  [linI 1 1 x0 y0, mulI (.loc m) Et zero, linI 0 1 x0 x0, mulI (.loc (m + 2)) y0 zero,
    linI 0 1 y0 y0, mulI x0 (.loc (m + 4)) zero, mulI (.loc (m + 5)) St zero,
    mulI (.loc (m + 3)) Et (.loc (m + 6))]

/-- `eqEval`'s source after the coordinates `xs`, `ys` (`E0` before any). -/
def shiftRecE (n : Nat) : List Src → List Src → Src → Src
  | _ :: x, _ :: _, _ => .loc (n + 8 * x.length + 1)
  | _, _, E0 => E0

/-- `shiftEval`'s source. -/
def shiftRecS (n : Nat) : List Src → List Src → Src → Src
  | _ :: x, _ :: _, _ => .loc (n + 8 * x.length + 7)
  | _, _, S0 => S0

/-- **`(eqEval, shiftEval)` of two points**, the last coordinate first, 8 rows per coordinate. -/
def shiftRecIns (zero : Src) (n : Nat) : List Src → List Src → Src → Src → List Ins
  | x0 :: x, y0 :: y, E0, S0 => shiftRecIns zero n x y E0 S0 ++
      shiftLevel zero (n + 8 * x.length) x0 y0 (shiftRecE n x y E0) (shiftRecS n x y S0)
  | _, _, _, _ => []

theorem shiftRecIns_length (zero : Src) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src),
    xs.length = ys.length → (shiftRecIns zero n xs ys E0 S0).length = 8 * xs.length
  | [], [], _, _, _ => rfl
  | x0 :: x, y0 :: y, E0, S0, h => by
    simp only [shiftRecIns, List.length_append, shiftLevel, List.length_cons, List.length_nil]
    rw [shiftRecIns_length zero n x y E0 S0 (by simpa using h)]; ring
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem shiftRec_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src), xs.length = ys.length →
    E0.val xv V = 1 → S0.val xv V = 0 →
    Seg ins n (shiftRecIns zero n xs ys E0 S0) → n + 8 * xs.length ≤ ins.length →
    (shiftRecE n xs ys E0).val xv V = eqEval (xs.map (Src.val xv V)) (ys.map (Src.val xv V)) ∧
    (shiftRecS n xs ys S0).val xv V = shiftEval (xs.map (Src.val xv V)) (ys.map (Src.val xv V))
  | [], [], E0, S0, _, hE, hS, _, _ => by simp [shiftRecE, shiftRecS, hE, hS, eqEval_nil, shiftEval_nil]
  | x0 :: x, y0 :: y, E0, S0, h, hE, hS, hseg, hlen => by
    have hl : x.length = y.length := by simpa using h
    have hT := shiftRecIns_length zero n x y E0 S0 hl
    simp only [shiftRecIns] at hseg
    have ih := shiftRec_val hF hz n x y E0 S0 hl hE hS (seg_append_left hseg) (by simp at hlen; (clear * - hlen hl; omega))
    have hs := seg_append_right hseg
    rw [hT] at hs
    set m := n + 8 * x.length with hm
    have hlen' : m + (shiftLevel zero m x0 y0 (shiftRecE n x y E0) (shiftRecS n x y S0)).length ≤ ins.length := by
      simp [shiftLevel]; simp at hlen; omega
    have v : ∀ i, i < 8 → V.getD (m + i) 0 =
        ((shiftLevel zero m x0 y0 (shiftRecE n x y E0) (shiftRecS n x y S0)).getD i default).eval xv V := by
      intro i hi
      exact fix_seg hF hs hlen' (by simp [shiftLevel]; omega) (by
        interval_cases i <;> simp [shiftLevel, linI, mulI])
    have v0 := v 0 (by (clear * -; omega)); have v1 := v 1 (by (clear * -; omega)); have v2 := v 2 (by (clear * -; omega))
    have v3 := v 3 (by (clear * -; omega)); have v4 := v 4 (by (clear * -; omega)); have v5 := v 5 (by (clear * -; omega))
    have v6 := v 6 (by (clear * -; omega)); have v7 := v 7 (by (clear * -; omega))
    simp only [shiftLevel, List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_linI', Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7
    simp only [val_loc] at v1 v3 v5 v6 v7
    simp only [ih.1, ih.2, hz, add_zero] at v1 v3 v5 v6 v7
    simp only [shiftRecE, shiftRecS, List.map_cons, val_loc]
    rw [show n + 8 * x.length + 1 = m + 1 by (clear * -; omega), show n + 8 * x.length + 7 = m + 7 by (clear * -; omega),
      eqEval_cons, shiftEval_cons _ _ _ _ (by simpa using hl), v1, v7, v6, v5, v3, v0, v2, v4]
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]
    constructor <;> ring
  | [], _ :: _, _, _, h, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _ => by simp at h

/-! ## The interval shift sum `pre(H)`, from the last coordinate down -/

/-- The 12 rows of one coordinate at `m` (bound bit `h`), from the tail's `P`, `E`, `Pt`. -/
def preLevel (zero : Src) (m : Nat) (h : Bool) (x0 y0 P E Pt : Src) : List Ins :=
  [linI 0 1 y0 y0, linI 0 1 x0 x0,
    mulI (.loc m) x0 zero, mulI y0 (.loc (m + 1)) zero, mulI (.loc m) (.loc (m + 1)) zero, mulI y0 x0 zero,
    addI E (if h then Pt else zero),
    mulI (.loc (m + 3)) P zero, mulI (.loc (m + 2)) (.loc (m + 6)) (.loc (m + 7)),
    mulI (.loc (m + 5)) E zero, mulI (.loc (m + 4)) (.loc (m + 6)) (.loc (m + 9)),
    mulI (if h then .loc (m + 5) else .loc (m + 4)) Pt zero]

/-- The sources of `(pre, E, Pt)` after the coordinates `xs`, `ys` (`base` before any). -/
def preRecOut (n : Nat) : List Src → List Src → Src × Src × Src → Src × Src × Src
  | _ :: x, _ :: _, _ => (.loc (n + 12 * x.length + 8), .loc (n + 12 * x.length + 10), .loc (n + 12 * x.length + 11))
  | _, _, base => base

/-- **`preCF xs ys H`**, the last coordinate first, 12 rows per coordinate. -/
def preRecIns (zero : Src) (n : Nat) : List Src → List Src → Nat → Src × Src × Src → List Ins
  | x0 :: x, y0 :: y, H, base => preRecIns zero n x y (H / 2) base ++
      preLevel zero (n + 12 * x.length) (H % 2 = 1) x0 y0 (preRecOut n x y base).1 (preRecOut n x y base).2.1
        (preRecOut n x y base).2.2
  | _, _, _, _ => []

theorem preRecIns_length (zero : Src) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    xs.length = ys.length → (preRecIns zero n xs ys H base).length = 12 * xs.length
  | [], [], _, _, _ => rfl
  | x0 :: x, y0 :: y, H, base, h => by
    simp only [preRecIns, List.length_append, preLevel, List.length_cons, List.length_nil]
    rw [preRecIns_length zero n x y (H / 2) base (by simpa using h)]; ring
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem preRec_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    xs.length = ys.length → H < 2 ^ xs.length →
    base.1.val xv V = 0 → base.2.1.val xv V = 0 → base.2.2.val xv V = 1 →
    Seg ins n (preRecIns zero n xs ys H base) → n + 12 * xs.length ≤ ins.length →
    ((preRecOut n xs ys base).1.val xv V, (preRecOut n xs ys base).2.1.val xv V,
      (preRecOut n xs ys base).2.2.val xv V) = preCF (xs.map (Src.val xv V)) (ys.map (Src.val xv V)) H
  | [], [], H, base, _, hH, h1, h2, h3, _, _ => by
    simp only [List.length_nil, pow_zero] at hH
    have : H = 0 := by (clear * - hH; omega)
    subst this
    simp [preRecOut, preCF, h1, h2, h3]
  | x0 :: x, y0 :: y, H, base, h, hH, h1, h2, h3, hseg, hlen => by
    have hl : x.length = y.length := by simpa using h
    have hT := preRecIns_length zero n x y (H / 2) base hl
    simp only [preRecIns] at hseg
    have ih := preRec_val hF hz n x y (H / 2) base hl
      (by simp only [List.length_cons, pow_succ] at hH; (clear * - hH; omega)) h1 h2 h3 (seg_append_left hseg)
      (by simp at hlen; (clear * - hlen hl; omega))
    have hs := seg_append_right hseg
    rw [hT] at hs
    set m := n + 12 * x.length with hm
    set L := preLevel zero m (H % 2 = 1) x0 y0 (preRecOut n x y base).1 (preRecOut n x y base).2.1
        (preRecOut n x y base).2.2 with hL
    have hlen' : m + L.length ≤ ins.length := by
      simp [hL, preLevel]; simp at hlen; omega
    have v : ∀ i, i < 12 → V.getD (m + i) 0 = (L.getD i default).eval xv V := by
      intro i hi
      exact fix_seg hF hs hlen' (by simp [hL, preLevel]; omega) (by
        interval_cases i <;> simp [hL, preLevel, linI, mulI, addI] <;> split <;> simp [mulI])
    have v0 := v 0 (by (clear * -; omega)); have v1 := v 1 (by (clear * -; omega)); have v2 := v 2 (by (clear * -; omega))
    have v3 := v 3 (by (clear * -; omega)); have v4 := v 4 (by (clear * -; omega)); have v5 := v 5 (by (clear * -; omega))
    have v6 := v 6 (by (clear * -; omega)); have v7 := v 7 (by (clear * -; omega)); have v8 := v 8 (by (clear * -; omega))
    have v9 := v 9 (by (clear * -; omega)); have v10 := v 10 (by (clear * -; omega)); have v11 := v 11 (by (clear * -; omega))
    simp only [hL, preLevel, List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_linI', eval_addI,
      Nat.add_zero, val_loc, hz, add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl] at v0 v1
    have hpre : preCF ((x0 :: x).map (Src.val xv V)) ((y0 :: y).map (Src.val xv V)) H =
        preStep (x0.val xv V) (y0.val xv V) (H % 2 = 1) (preCF (x.map (Src.val xv V)) (y.map (Src.val xv V)) (H / 2)) := rfl
    rw [hpre, ← ih]
    rw [show preRecOut n (x0 :: x) (y0 :: y) base = (Src.loc (m + 8), Src.loc (m + 10), Src.loc (m + 11))
      from rfl]
    simp only [val_loc]
    unfold preStep
    by_cases hb : H % 2 = 1
    · have hd : decide (H % 2 = 1) = true := by simp [hb]
      simp only [hd, eq_self_iff_true, if_true, ite_true] at v6 v11 ⊢
      simp only [val_loc] at v11
      rw [v8, v10, v11, v7, v9, v6, v2, v3, v4, v5, v0, v1]
      simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by first | trivial | ring⟩
    · have hd : decide (H % 2 = 1) = false := by simp [hb]
      simp only [hd, Bool.false_eq_true, ite_false, hz, add_zero] at v6 v11 ⊢
      simp only [val_loc] at v11
      rw [v8, v10, v11, v7, v9, v6, v2, v3, v4, v5, v0, v1]
      simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by first | trivial | ring⟩
  | [], _ :: _, _, _, h, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _, _, _ => by simp at h

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithRows` =====

-- ===== merged from `LvmQLinkArithCH` (GOLF module merge: `LvmQLinkArithCH.lean` is now a stub importing `LvmQLinkArithKS`) =====
section

/-!
# QA1 links: the `CH` link circuit (phase 5)

Three straight-line blocks around two sumcheck gadgets (`scGadget`):

* **A** (`chGlueA`, `2n + 166` rows, `n = logN`): load the `n + 9` challenges `ρ, λ, ζ`; `eq(λ, ·)` (8) and
  `eq(ζ, ·)` (64) as `eqKernel`; `Pad43`'s constant bits; `Πρ`; the shift sumcheck's claim
  `C·(1 + Πρ)` (= `chShiftTarget0`, `chGlueA_target`).
* the shift sumcheck (`n` rounds, degree 2);
* **B** (`chGlueB`): the 64 `in` slices, `Σ_p eq(ζ,p)·inS_p`, `(eqEval, shiftEval)(ρ, ρ')`, the second
  sumcheck's claim (= `chSc2Target0`);
* the two-round sumcheck;
* **C** (`chGlueC`): the 64 `Y` slices, `eq(μ, ·)`, `α`, `β`, the two halves of `Σ_q W̃(μ,q)·yS_q`,
  `eqMasked`, and the gated assertion `gate·(f₂ − eqMasked·Σ) = 0` (`chLink0`'s check).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Helpers -/

/-- A cell as an operand of a template. -/
def cellSrc (c : Cell) : Src := .ext c.addr

theorem iterXv_cell (M : Mem) (o : LoopOut) (jf : Nat) (c : Cell) : iterXv M o jf (cellSrc c) = c.val M := by
  simp only [iterXv, cellSrc, Src.toOpd, Opd.val_abs, Cell.addr, Addr.at, dot_nil, Nat.add_zero]
  rfl

theorem iterXv_fixed (M : Mem) (o : LoopOut) (jf : Nat) (τ : Ty) (b : Nat) :
    iterXv M o jf (.ext ⟨τ, b, []⟩) = M.rd τ b := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, Addr.at]
  rfl

theorem seg_whole (ins : List Ins) : Seg ins 0 ins := by intro i _; simp

/-- A load of the fixed lanes `q, q + 1, q + 2` is the stream's scalar at byte `8q`. -/
theorem load_fixed {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) (jf : Nat)
    (V : List FE) {q : Nat} (hq : q + 2 < T) :
    (loadI q []).eval (iterXv M o jf) V = feAt sig (8 * q) := by
  show iterXv M o jf (.ext ⟨.K, q, []⟩) + FE.y * iterXv M o jf (.ext ⟨.K, q + 1, []⟩) +
    FE.y * FE.y * iterXv M o jf (.ext ⟨.K, q + 2, []⟩) = _
  rw [iterXv_fixed, iterXv_fixed, iterXv_fixed]
  exact load_feAt hS hq

/-- The loads of `N` scalars at lanes `q + s·i`. -/
def loadsAt (q s N : Nat) : List Ins := (List.range N).map fun i => loadI (q + s * i) []

theorem loadsAt_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {ins : List Ins} {V : List FE} (hF : Fix (iterXv M o jf) ins V) {n q s N : Nat}
    (hseg : Seg ins n (loadsAt q s N)) (hlen : n + N ≤ ins.length) (hT : q + s * N + 2 < T + s) {i : Nat}
    (hi : i < N) : V.getD (n + i) 0 = feAt sig (8 * (q + s * i)) := by
  have hrow : (loadsAt q s N).getD i default = loadI (q + s * i) [] := by
    simp [loadsAt, List.getD_eq_getElem?_getD, hi]
  rw [fix_seg hF hseg (by simpa [loadsAt] using hlen) (by simpa [loadsAt] using hi)
    (by rw [hrow]; simp [loadI]), hrow]
  apply load_fixed hS
  have : s * i + s ≤ s * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

/-! ## Block A: the shift sumcheck's claim -/

/-- `λ`'s sources (challenges `n … n + 2`). -/
def lamS (n : Nat) : List Src := [.loc n, .loc (n + 1), .loc (n + 2)]
/-- `ζ`'s sources (challenges `n + 3 … n + 8`). -/
def zetaS (n : Nat) : List Src := (List.range 6).map fun i => .loc (n + 3 + i)
/-- `ρ`'s sources (challenges `0 … n − 1`). -/
def rhoS (n : Nat) : List Src := (List.range n).map Src.loc

/-- `eq(λ, k)`'s source. -/
def eLs (n k : Nat) : Src := (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).getD k default
/-- `eq(ζ, k)`'s source. -/
def eZs (n k : Nat) : Src := (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).getD k default

/-- `Pad43`'s constant bits `eq(λ,0)(eq(ζ,0) + eq(ζ,1) + eq(ζ,6)) + eq(λ,4)eq(ζ,8)` at `n + 160 … n + 163`. -/
def padRows (n : Nat) : List Ins :=
  [addI (eZs n 0) (eZs n 1), addI (.loc (n + 160)) (eZs n 6), mulI (eLs n 0) (.loc (n + 161)) (.loc (n + 9)),
    mulI (eLs n 4) (eZs n 8) (.loc (n + 162))]

/-- **Block A**: loads (`0 … n + 8`, lanes `Q + 9i`), zero (`n + 9`), one (`n + 10`), `eq(λ,·)`
(`n + 11`, 17 rows), `eq(ζ,·)` (`n + 28`, 132 rows), `Pad43`'s bits (`n + 160`), `Πρ` (`n + 164`,
`n` rows), `1 + Πρ` (`2n + 164`), the claim (`2n + 165`). -/
def chGlueA (n Q : Nat) : List Ins :=
  loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n) ++
    [linI 0 1 (.loc (2 * n + 163)) (.loc (2 * n + 163)), mulI (.loc (n + 163)) (.loc (2 * n + 164)) (.loc (n + 9))])))))

theorem eqTab3_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 3) :
    (eqTabGo z m [o] l).length = 17 := by
  match l, hl with
  | [a, b, c], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem eqTab6_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 6) :
    (eqTabGo z m [o] l).length = 132 := by
  match l, hl with
  | [a, b, c, d, e, f], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem chGlueA_length (n Q : Nat) : (chGlueA n Q).length = 2 * n + 166 := by
  simp only [chGlueA, List.length_append, loadsAt, List.length_map, List.length_range,
    eqTab3_length _ _ _ _ (rfl : (lamS n).length = 3),
    eqTab6_length _ _ _ _ (by simp [zetaS] : (zetaS n).length = 6), padRows, mulChainIns_length, rhoS,
    List.length_cons, List.length_nil]
  omega

theorem seg_split {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) :
    Seg ins n A ∧ Seg ins (n + A.length) B := ⟨seg_append_left h, seg_append_right h⟩

theorem seg_at {ins : List Ins} {n m : Nat} {seg : List Ins} (h : Seg ins n seg) (e : n = m) : Seg ins m seg :=
  e ▸ h

theorem eqKernel_map_getD (l : List FE) {k : Nat} (hk : k < 2 ^ l.length) :
    (eqKernel l).getD k 0 = eqW l k := eqKernel_getD l hk

/-- Block A's values, on any fixed point of its rows over a streamed memory. -/
theorem chGlueA_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n Q : Nat} {V : List FE} (hF : Fix (iterXv M o jf) (chGlueA n Q) V) (hn : 1 ≤ n)
    (hT : Q + 9 * (n + 9) + 2 < T + 9) :
    (∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i))) ∧
    V.getD (n + 9) 0 = 0 ∧ V.getD (n + 10) 0 = 1 ∧
    (∀ k < 8, (eLs n k).val (iterXv M o jf) V =
      eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k) ∧
    (∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k) ∧
    V.getD (2 * n + 163) 0 = ((List.range n).map fun i => V.getD i 0).prod ∧
    V.getD (2 * n + 165) 0 =
      (eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 0 *
        (eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 0 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 1 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 6) +
        eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 4 *
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 8) *
      (1 + ((List.range n).map fun i => V.getD i 0).prod) := by
  have hlen := chGlueA_length n Q
  have hs : Seg (chGlueA n Q) 0 (loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n) ++
    [linI 0 1 (.loc (2 * n + 163)) (.loc (2 * n + 163)), mulI (.loc (n + 163)) (.loc (2 * n + 164)) (.loc (n + 9))])))))) :=
    seg_whole _
  have lL : (loadsAt Q 9 (n + 9)).length = n + 9 := by simp [loadsAt]
  have lEL : (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n)).length = 17 := eqTab3_length _ _ _ _ rfl
  have lEZ : (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n)).length = 132 :=
    eqTab6_length _ _ _ _ (by simp [zetaS])
  have lM : (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n)).length = n := by
    rw [mulChainIns_length]; simp [rhoS]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEL, s3⟩ := seg_split s2
  obtain ⟨sEZ, s4⟩ := seg_split s3
  obtain ⟨sP, s5⟩ := seg_split s4
  obtain ⟨sM, sF⟩ := seg_split s5
  replace sZ := seg_at (m := n + 9) sZ (by simp [lL])
  replace sEL := seg_at (m := n + 11) sEL (by simp [lL] <;> omega)
  replace sEZ := seg_at (m := n + 28) sEZ (by simp [lL, lEL] <;> omega)
  replace sP := seg_at (m := n + 160) sP (by simp [lL, lEL, lEZ] <;> omega)
  replace sM := seg_at (m := n + 164) sM (by simp [lL, lEL, lEZ, padRows] <;> omega)
  replace sF := seg_at (m := 2 * n + 164) sF (by simp [lL, lEL, lEZ, lM, padRows] <;> omega)
  -- loads
  have hL : ∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hi
    rwa [Nat.zero_add] at this
  -- zero and one
  have hz : V.getD (n + 9) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 10) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [linI])
    rw [show n + 9 + 1 = n + 10 by omega] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 9)).val (iterXv M o jf) V = 0 := hz
  -- eq tables
  have hEL := eqTab_val hF hzs (lamS n) (n + 11) [.loc (n + 10)] sEL
    (by rw [eqTab3_length _ _ _ _ rfl, hlen]; omega)
  have hEZ := eqTab_val hF hzs (zetaS n) (n + 28) [.loc (n + 10)] sEZ
    (by rw [eqTab6_length _ _ _ _ (by simp [zetaS]), hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1] at hEL hEZ
  have hlam : (lamS n).map (Src.val (iterXv M o jf) V) = [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] := by
    simp [lamS]
  have hzeta : (zetaS n).map (Src.val (iterXv M o jf) V) = (List.range 6).map fun i => V.getD (n + 3 + i) 0 := by
    simp [zetaS]
  rw [hlam] at hEL
  rw [hzeta] at hEZ
  have eL : ∀ k < 8, (eLs n k).val (iterXv M o jf) V = eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).length := by
      have := congrArg List.length hEL
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eLs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEL, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  have eZ : ∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).length := by
      have := congrArg List.length hEZ
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eZs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEZ, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  -- Pad43's bits
  have p0 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 0) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p1 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 1) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p2 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 2) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p3 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 3) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  simp only [padRows, List.getD_cons_zero, List.getD_cons_succ, eval_addI, eval_mulI, val_loc, hz, add_zero,
    Nat.add_zero] at p0 p1 p2 p3
  rw [show n + 160 + 1 = n + 161 by omega] at p1
  rw [show n + 160 + 2 = n + 162 by omega, p1, p0] at p2
  rw [show n + 160 + 3 = n + 163 by omega, p2] at p3
  rw [eL 0 (by omega), eL 4 (by omega), eZ 0 (by omega), eZ 1 (by omega), eZ 6 (by omega),
    eZ 8 (by omega)] at p3
  -- Πρ
  have hM := mulChain_val hF hzs (rhoS n) (n + 164) (.loc (n + 10))
    sM (by rw [hlen]; simp [rhoS]; omega)
  have hsrc : sumSrc (n + 164) (.loc (n + 10)) (rhoS n) = .loc (2 * n + 163) := by
    simp only [sumSrc, rhoS, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by omega), show n + 164 + n - 1 = 2 * n + 163 by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul] at hM
  have hrho : (rhoS n).map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => V.getD i 0 := by
    simp [rhoS]
  rw [hrho] at hM
  -- the claim
  have f0 := fix_seg hF sF (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
  have f1 := fix_seg hF sF (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_linI', eval_mulI, val_loc, Nat.add_zero] at f0 f1
  rw [show 2 * n + 164 + 1 = 2 * n + 165 by omega, f0, hz, p3, hM] at f1
  refine ⟨hL, hz, h1, eL, eZ, hM, ?_⟩
  rw [f1, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]
  ring

/-! ## Block B: the second sumcheck's claim -/

/-- **Block B**: the 64 `in` slices (lanes `QB + 3k`), zero (64), one (65), `Σ_k eq(ζ,k)·inS_k` (66, 64 rows,
at 129), `(eqEval, shiftEval)(ρ, ρ')` (130, `8n` rows), the claim `S·dot + f₁` (`8n + 130`). -/
def chGlueB (QB : Nat) (rho rho' eZ : List Cell) (f1 : Cell) : List Ins :=
  loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (shiftRecIns (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64) ++
    [mulI (.loc (8 * rho.length + 129)) (.loc 129) (cellSrc f1)])))

theorem chGlueB_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QB : Nat} {rho rho' eZ : List Cell} {f1 : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueB QB rho rho' eZ f1) V) (hn : 1 ≤ rho.length) (hl : rho.length = rho'.length)
    (hT : QB + 3 * 64 + 2 < T + 3) :
    (∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k))) ∧
    V.getD (8 * rho.length + 123) 0 = eqEval (rho.map (Cell.val M)) (rho'.map (Cell.val M)) ∧
    V.getD (8 * rho.length + 130) 0 = shiftEval (rho.map (Cell.val M)) (rho'.map (Cell.val M)) *
      (∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k))) + f1.val M := by
  have hs : Seg (chGlueB QB rho rho' eZ f1) 0 (loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (shiftRecIns (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64) ++
    [mulI (.loc (8 * rho.length + 129)) (.loc 129) (cellSrc f1)])))) := seg_whole _
  have lS := shiftRecIns_length (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64)
    (by simpa using hl)
  have hlen : (chGlueB QB rho rho' eZ f1).length = 8 * rho.length + 131 := by
    simp only [chGlueB, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length, lS,
      List.length_cons, List.length_nil]; omega
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sD, s3⟩ := seg_split s2
  obtain ⟨sR, sF⟩ := seg_split s3
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sD := seg_at (m := 66) sD (by simp [loadsAt])
  replace sR := seg_at (m := 130) sR (by simp [loadsAt, dotIns_length])
  replace sF := seg_at (m := 8 * rho.length + 130) sF (by simp [loadsAt, dotIns_length, lS]; omega)
  have hL : ∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k)) := by
    intro k hk
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hk
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hD := dot_val hF ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) 66 (.loc 64) sD
    (by rw [hlen]; simp <;> omega)
  have hDs : dotSrc 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) = .loc 129 := by
    simp [dotSrc]
  rw [hDs, val_loc, val_loc, hz, zero_add] at hD
  have hR := shiftRec_val hF (zero := .loc 64) hz 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64)
    (by simpa using hl) h1 hz sR (by rw [hlen]; simp <;> omega)
  have hE : shiftRecE 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) = .loc (8 * rho.length + 123) := by
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, rho = c :: cs := ⟨rho.head (by intro h; simp [h] at hn), rho.tail, by simp⟩
    obtain ⟨c', cs', rfl⟩ : ∃ c cs, rho' = c :: cs := ⟨rho'.head (by intro h; simp [h] at hl <;> omega), rho'.tail, by simp⟩
    simp [shiftRecE] <;> omega
  have hSs : shiftRecS 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 64) = .loc (8 * rho.length + 129) := by
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, rho = c :: cs := ⟨rho.head (by intro h; simp [h] at hn), rho.tail, by simp⟩
    obtain ⟨c', cs', rfl⟩ : ∃ c cs, rho' = c :: cs := ⟨rho'.head (by intro h; simp [h] at hl <;> omega), rho'.tail, by simp⟩
    simp [shiftRecS] <;> omega
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  rw [hE, hSs, val_loc, val_loc, hmap, hmap] at hR
  have f0 := fix_seg hF sF (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, eval_mulI, val_loc, Nat.add_zero] at f0
  have hsum : (List.map (fun ab => ab.1.val (iterXv M o jf) V * ab.2.val (iterXv M o jf) V)
      (List.map (fun k => (cellSrc (eZ.getD k default), Src.loc k)) (List.range 64))).sum =
      ∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k)) := by
    rw [List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    show iterXv M o jf (cellSrc (eZ.getD k default)) * V.getD k 0 = _
    rw [iterXv_cell, hL k hk']
  refine ⟨hL, hR.1, ?_⟩
  rw [f0, hR.2, hD, hsum]
  show _ + iterXv M o jf (cellSrc f1) = _
  rw [iterXv_cell]

/-! ## Block C: the `CH` link's check -/

/-- `eq(μ, m)`'s source in block C. -/
def eMus (mu : List Cell) (m : Nat) : Src := (eqTabOut 66 [.loc 65] (mu.map cellSrc)).getD m default

/-- **Block C**: the 64 `Y` slices (lanes `QC + 3q`), zero (64), one (65), `eq(μ,·)` (66, 8 rows),
`α` (74, at 77), `β` (78, at 81), `S₁ = Σ_{q<56} eq(ζ,q+8)·yS_q` (82, at 137), `S₂` (138, at 145),
`β S₂` (146), `α S₁ + β S₂` (147), `Πρ'` (148, `n` rows), `eqMasked = Πρ·Πρ' + eqEval` (`148 + n`),
the target (`149 + n`), `f₂ + target` (`150 + n`), the gated assertion (`151 + n`). -/
def chGlueC (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) : List Ins :=
  loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc) ++
    [mulI (cellSrc prodRho) (.loc (147 + rho'.length)) (cellSrc eqE),
      mulI (.loc (148 + rho'.length)) (.loc 147) (.loc 64),
      addI (cellSrc f2) (.loc (149 + rho'.length)),
      ⟨.assert0, .K, [.loc (150 + rho'.length), cellSrc gate]⟩]))))))))

theorem eqTab2_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 2) :
    (eqTabGo z m [o] l).length = 8 := by
  match l, hl with
  | [a, b], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem chGlueC_length (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).length = 152 + rho'.length := by
  simp only [chGlueC, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
    mulChainIns_length, eqTab2_length _ _ _ _ (by simpa using hm : (mu.map cellSrc).length = 2),
    List.length_cons, List.length_nil]
  omega

/-- **Block C's assertion**: with gate `1`, `f₂ = (Πρ·Πρ' + eqEval)·(α S₁ + β S₂)`. -/
theorem chGlueC_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QC : Nat} {mu eL eZ rho' : List Cell} {prodRho eqE f2 gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate) V) (hm : mu.length = 2)
    (hT : QC + 3 * 64 + 2 < T + 3)
    (hn : 1 ≤ rho'.length)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD (150 + rho'.length) 0 = 0) (hg : gate.val M = 1) :
    f2.val M = (prodRho.val M * (rho'.map (Cell.val M)).prod + eqE.val M) *
      ((∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M) *
          (∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q))) +
        (∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M) *
          (∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))))) := by
  set n := rho'.length with hndef
  have hlen := chGlueC_length QC mu eL eZ rho' prodRho eqE f2 gate hm
  have hs : Seg (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate) 0
    (loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc) ++
    [mulI (cellSrc prodRho) (.loc (147 + n)) (cellSrc eqE),
      mulI (.loc (148 + n)) (.loc 147) (.loc 64),
      addI (cellSrc f2) (.loc (149 + n)),
      ⟨.assert0, .K, [.loc (150 + n), cellSrc gate]⟩]))))))))) := seg_whole _
  have lEM : (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc)).length = 8 := eqTab2_length _ _ _ _ (by simpa using hm)
  have lMC : (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc)).length = n := by
    rw [mulChainIns_length]; simp [hndef]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEM, s3⟩ := seg_split s2
  obtain ⟨sDA, s4⟩ := seg_split s3
  obtain ⟨sDB, s5⟩ := seg_split s4
  obtain ⟨sD1, s6⟩ := seg_split s5
  obtain ⟨sD2, s7⟩ := seg_split s6
  obtain ⟨sMM, s8⟩ := seg_split s7
  obtain ⟨sMC, sF⟩ := seg_split s8
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sEM := seg_at (m := 66) sEM (by simp [loadsAt])
  replace sDA := seg_at (m := 74) sDA (by simp [loadsAt, lEM])
  replace sDB := seg_at (m := 78) sDB (by simp [loadsAt, lEM, dotIns_length])
  replace sD1 := seg_at (m := 82) sD1 (by simp [loadsAt, lEM, dotIns_length])
  replace sD2 := seg_at (m := 138) sD2 (by simp [loadsAt, lEM, dotIns_length])
  replace sMM := seg_at (m := 146) sMM (by simp [loadsAt, lEM, dotIns_length])
  replace sMC := seg_at (m := 148) sMC (by simp [loadsAt, lEM, dotIns_length])
  replace sF := seg_at (m := 148 + n) sF (by simp [loadsAt, lEM, dotIns_length, lMC] <;> omega)
  have hL : ∀ q < 64, V.getD q 0 = feAt sig (8 * (QC + 3 * q)) := by
    intro q hq
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hq
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc 64).val (iterXv M o jf) V = 0 := hz
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  -- eq(μ, ·)
  have hEM := eqTab_val hF hzs (mu.map cellSrc) 66 [.loc 65] sEM (by rw [lEM, hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1, hmap] at hEM
  have eMu : ∀ m < 4, (eMus mu m).val (iterXv M o jf) V = eqW (mu.map (Cell.val M)) m := by
    intro m hm4
    have hlo : m < (eqTabOut 66 [.loc 65] (mu.map cellSrc)).length := by
      have := congrArg List.length hEM
      rw [List.length_map, foldl_eqStep_length] at this; simp [hm] at this; omega
    rw [eMus, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlo, hEM, ← eqKernel_foldl,
      eqKernel_getD _ (by simp [hm]; omega)]
  -- the dot products
  have hDA := dot_val hF _ 74 (.loc 64) sDA (by rw [hlen]; simp <;> omega)
  have hDB := dot_val hF _ 78 (.loc 64) sDB (by rw [hlen]; simp <;> omega)
  have hD1 := dot_val hF _ 82 (.loc 64) sD1 (by rw [hlen]; simp <;> omega)
  have hD2 := dot_val hF _ 138 (.loc 64) sD2 (by rw [hlen]; simp <;> omega)
  simp only [dotSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range,
    OfNat.ofNat_ne_zero, if_false, val_loc, hz, zero_add, List.map_map] at hDA hDB hD1 hD2
  rw [list_sum_range] at hDA hDB hD1 hD2
  simp only [Function.comp_def, hcell, val_loc] at hDA hDB hD1 hD2
  have hA4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD x default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have hB4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD (x + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have h56 : ∑ x ∈ Finset.range 56, (eZ.getD (x + 8) default).val M * V.getD x 0 =
      ∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q)) :=
    Finset.sum_congr rfl fun q hq => by rw [hL q (by have := Finset.mem_range.mp hq; omega)]
  have h8 : ∑ x ∈ Finset.range 8, (eZ.getD x default).val M * V.getD (x + 56) 0 =
      ∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))) :=
    Finset.sum_congr rfl fun q hq => by rw [hL (q + 56) (by have := Finset.mem_range.mp hq; omega)]
  rw [hA4] at hDA
  rw [hB4] at hDB
  rw [h56] at hD1
  rw [h8] at hD2
  -- the products and the check
  have m0 := fix_seg hF sMM (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [mulI])
  have m1 := fix_seg hF sMM (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, val_loc, hz, add_zero, Nat.add_zero] at m0 m1
  have hMC := mulChain_val hF hzs (rho'.map cellSrc) 148 (.loc 65) sMC (by rw [hlen]; simp <;> omega)
  have hsrc : sumSrc 148 (.loc 65) (rho'.map cellSrc) = .loc (147 + n) := by
    simp only [sumSrc, List.map_eq_nil_iff, List.length_map]
    rw [if_neg (by intro h; rw [h] at hndef; simp at hndef; omega), show 148 + rho'.length - 1 = 147 + n by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul, hmap] at hMC
  have f0 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [mulI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  have f2' := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 2) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_addI, val_loc, hz, add_zero,
    Nat.add_zero, hcell] at f0 f1 f2'
  rw [show 148 + n + 1 = 149 + n by omega] at f1
  rw [show 148 + n + 2 = 150 + n by omega] at f2'
  rw [hcell, hg, one_mul, f2', f1, f0, hMC, m1, m0, hDA, hDB, hD1, hD2] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination hA

/-! ## Where the tables are -/

theorem getD_range_loc (b k N : Nat) (hk : k < N) :
    ((List.range N).map fun i => Src.loc (b + i)).getD k default = .loc (b + k) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem eLs_eq (n k : Nat) (hk : k < 8) : eLs n k = .loc (n + 20 + k) := by
  simp only [eLs, lamS, eqTabOut, eqLevelOut, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [show n + 11 + 1 + 2 * (0 + 1) + 1 + 2 * (2 * (0 + 1)) + 1 = n + 20 by omega, getD_range_loc _ _ _ (by omega)]

theorem eZs_eq (n k : Nat) (hk : k < 64) : eZs n k = .loc (n + 96 + k) := by
  have hz : zetaS n = [.loc (n + 3 + 0), .loc (n + 3 + 1), .loc (n + 3 + 2), .loc (n + 3 + 3), .loc (n + 3 + 4),
      .loc (n + 3 + 5)] := rfl
  simp only [eZs, hz, eqTabOut, eqLevelOut, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  rw [show n + 28 + 1 + 2 * (0 + 1) + 1 + 2 * (2 * (0 + 1)) + 1 + 2 * (2 * (2 * (0 + 1))) + 1 +
      2 * (2 * (2 * (2 * (0 + 1)))) + 1 + 2 * (2 * (2 * (2 * (2 * (0 + 1))))) + 1 = n + 96 by omega,
    getD_range_loc _ _ _ (by omega)]

theorem eMus_eq (c₀ c₁ : Cell) (m : Nat) (hm : m < 4) : eMus [c₀, c₁] m = .loc (70 + m) := by
  simp only [eMus, List.map_cons, List.map_nil, eqTabOut, eqLevelOut, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  rw [show 66 + 1 + 2 * (0 + 1) + 1 = 70 by omega, getD_range_loc _ _ _ (by omega)]

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithCH` =====

-- ===== merged from `LvmQLinkArithCHSound` (GOLF module merge: `LvmQLinkArithCHSound.lean` is now a stub importing `LvmQLinkArithKS`) =====
section

/-!
# QA1 links: the `CH` link gadget and its soundness against `F`

`chLinkGadget n D Q gate`: block A, the shift sumcheck (`2^D ≥ n` iterations), block B, the two-round
sumcheck, block C. **`chLink_sound`**: in every memory where the gadget's rows hold, whose input lanes
are the stream's (`Streamed`), with the phase starting at position `P` (`P + 40 = 8Q`) and gate `1`:
if the gadget's assertion holds, then `chLink0`'s check on what `F` reads in phase 5
(`chLinkView`, `LvmQLinkArithRead`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Small facts -/

theorem lnk_fe_beq (x y : FE) : (x == y) = true ↔ x = y := by
  cases x; cases y
  show ((_ == _ && _ == _) && _ == _) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem lnk_scSpec_length (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (es : List (Option FE)),
    (scSpec v count p claim es).1.length = es.length
  | _, _, [] => rfl
  | p, claim, e :: es => by simp [scSpec, lnk_scSpec_length v count _ _ es]

theorem take_range_map (f : Nat → FE) {n N : Nat} (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_range_map (f : Nat → FE) (n N : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun i => f (n + i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_drop, List.getElem_map, List.getElem_range]

/-! ## The gadget -/

/-- The shift sumcheck's first message lane. -/
def chQ1 (n Q : Nat) : Nat := Q + 9 * (n + 9)
/-- The `in` slices' first lane. -/
def chQB (n Q : Nat) : Nat := chQ1 n Q + 15 * n
/-- The two-round sumcheck's first message lane. -/
def chQ2 (n Q : Nat) : Nat := chQB n Q + 246
/-- The `Y` slices' first lane. -/
def chQC (n Q : Nat) : Nat := chQ2 n Q + 30

/-- `ρ`'s cells (block A's loads `0 … n − 1`). -/
def rhoC (oA : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => oA.cell i 0
/-- `ρ'`'s cells (the shift sumcheck's challenges). -/
def rho'C (sh : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => sh.cell 2 i
/-- `eq(ζ, ·)`'s cells. -/
def eZC (oA : LoopOut) (n : Nat) : List Cell := (List.range 64).map fun k => oA.cell (n + 96 + k) 0
/-- `eq(λ, ·)`'s cells. -/
def eLC (oA : LoopOut) (n : Nat) : List Cell := (List.range 8).map fun k => oA.cell (n + 20 + k) 0

/-- **The `CH` link gadget** (phase 5's arithmetic). -/
def chLinkGadget (n D Q : Nat) (gate : Cell) : BM Unit := do
  let oA ← loop [] (tplOf (chGlueA n Q))
  let sh ← scGadget D 2 (chQ1 n Q) .plain (oA.cell (2 * n + 165) 0)
  let oB ← loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))))
  let sc2 ← scGadget 1 2 (chQ2 n Q) .plain (oB.cell (8 * n + 130) 0)
  let _ ← loop [] (tplOf (chGlueC (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate))
  pure ()

/-! ## Soundness -/

theorem chGlueC_last (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).getD (151 + rho'.length) default =
      ⟨.assert0, .K, [.loc (150 + rho'.length), cellSrc gate]⟩ := by
  have hlen := chGlueC_length QC mu eL eZ rho' prodRho eqE f2 gate hm
  rw [show 151 + rho'.length = (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).length - 1 by omega,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
  simp [chGlueC, List.getLast?_append, List.getLast?_cons]

theorem cell_iterV {M : Mem} (o : LoopOut) {t len : Nat} (ht : t < len) :
    (o.cell t 0).val M = (iterV M o len 0).getD t 0 := (iterV_getD M o ht).symm

/-- **The `CH` link circuit is sound for `F`'s phase-5 check.** -/
theorem chLink_sound (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    (blk : Placement) (ySlot D : Nat) {c : Ctx} {M : Mem} {ptr : Ptr}
    {sig : ByteArray} {T P Q : Nat} (r w : List FE) (pub : Pub) (gate : Cell)
    (hn : 1 ≤ p.logN) (hD : p.logN ≤ 2 ^ D) (hPQ : P + 40 = 8 * Q)
    (hokA : SLok (chGlueA p.logN Q) = true)
    (hokB : ∀ oA sh : LoopOut, SLok (chGlueB (chQB p.logN Q) (rhoC oA p.logN) (rho'C sh p.logN) (eZC oA p.logN)
      (sh.cell 5 (p.logN - 1))) = true)
    (hokC : ∀ oA sh sc2 oB : LoopOut, SLok (chGlueC (chQC p.logN Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA p.logN)
      (eZC oA p.logN) (rho'C sh p.logN) (oA.cell (2 * p.logN + 163) 0) (oB.cell (8 * p.logN + 123) 0)
      (sc2.cell 5 1) gate) = true)
    (hS : Streamed M sig T) (hT : chQC p.logN Q + 3 * 64 + 3 ≤ T) (hg : gate.val M = 1)
    (h : SegsHold c M ptr (chLinkGadget p.logN D Q gate ptr).2)
    (hA : SegsAssert M ptr (chLinkGadget p.logN D Q gate ptr).2) :
    (chLink0 p blk ySlot (chLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P r w pub)).1 = true := by
  set n := p.logN with hndef
  -- decomposition
  simp only [chLinkGadget] at h hA
  rw [hold_bind] at h; obtain ⟨hhA, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhS, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhB, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hh2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhC, -⟩ := h
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨haC, -⟩ := hA
  -- names
  generalize hoA : (loop [] (tplOf (chGlueA n Q)) ptr).1 = oA at hhS hhB hh2 hhC haC
  have hFA : Fix (iterXv M oA 0) (chGlueA n Q) (iterV M oA (chGlueA n Q).length 0) := by
    rw [← hoA]; exact fix_of_loop hokA hhA (by simp)
  generalize hVA : iterV M oA (chGlueA n Q).length 0 = VA at hFA
  have hlA := chGlueA_length n Q
  have hcA : ∀ t < 2 * n + 166, (oA.cell t 0).val M = VA.getD t 0 := by
    intro t ht; rw [← hVA, cell_iterV (len := (chGlueA n Q).length) oA (by rw [hlA]; exact ht)]
  obtain ⟨A1, -, -, AL, AZ, AP, AT⟩ := chGlueA_val hS hFA hn (by simp [chQC, chQ2, chQB, chQ1] at hT; omega)
  -- F's challenges
  set f : Nat → FE := fun i => feAt sig (P + 40 + 72 * i) with hf
  have hchal : samplesAt (feAt sig) P (n + 3 + 6) = (List.range (n + 9)).map f := rfl
  have hVf : ∀ i < n + 9, VA.getD i 0 = f i := by
    intro i hi; rw [A1 i hi, hf]; congr 1; omega
  have hrhoF : (samplesAt (feAt sig) P (n + 3 + 6)).take n = (List.range n).map f := by
    rw [hchal, take_range_map _ (by omega)]
  have hlamF : ((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3 = [f n, f (n + 1), f (n + 2)] := by
    rw [hchal, drop_range_map, show n + 9 - n = 9 by omega, take_range_map _ (by omega)]
    simp [List.range_succ]
  have hzetaF : (samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3) = (List.range 6).map fun i => f (n + 3 + i) := by
    rw [hchal, drop_range_map, show n + 9 - (n + 3) = 6 by omega]
  have hlamV : [VA.getD n 0, VA.getD (n + 1) 0, VA.getD (n + 2) 0] = [f n, f (n + 1), f (n + 2)] := by
    rw [hVf n (by omega), hVf (n + 1) (by omega), hVf (n + 2) (by omega)]
  have hzetaV : ((List.range 6).map fun i => VA.getD (n + 3 + i) 0) = (List.range 6).map fun i => f (n + 3 + i) := by
    apply List.map_congr_left; intro i hi; rw [hVf _ (by simp at hi; omega)]
  have hrhoV : ((List.range n).map fun i => VA.getD i 0) = (List.range n).map f := by
    apply List.map_congr_left; intro i hi; rw [hVf _ (by simp at hi; omega)]
  rw [hlamV, hzetaV, hrhoV] at AT
  rw [hrhoV] at AP
  -- the shift sumcheck's claim is F's
  have hclaimA : (oA.cell (2 * n + 165) 0).val M =
      chShiftTarget0 p (samplesAt (feAt sig) P (n + 3 + 6)) := by
    rw [hcA _ (by omega), AT, chShiftTarget0_eq p _ (by simp [samplesAt, hndef]), hrhoF, hlamF, hzetaF]
  -- the shift sumcheck
  have hq1 : 8 * chQ1 n Q - 40 = chP1 p P := by simp only [chQ1, chP1, ← hndef]; omega
  have hSC := sc_spec_plain (R := n) (by omega) (scTpl_ok_2 _) hD (by simp [chQ1]; omega) hS
    (by simp [chQC, chQ2, chQB, chQ1, roundLanes] at hT ⊢; omega) hhS
  set pS := ptr.adv (loop [] (tplOf (chGlueA n Q)) ptr).2 with hpS
  generalize hsh : (scGadget D 2 (chQ1 n Q) .plain (oA.cell (2 * n + 165) 0) pS).1 = sh at hSC hhB hh2 hhC haC
  rw [hq1, hclaimA] at hSC
  set shiftF := scSpec (feAt sig) 3 (chP1 p P) (chShiftTarget0 p (samplesAt (feAt sig) P (n + 3 + 6)))
    (List.replicate n none) with hshiftF
  have hSlen : shiftF.1.length = n := by rw [hshiftF, lnk_scSpec_length]; simp
  have S1 : (rho'C sh n).map (Cell.val M) = shiftF.1 := by
    apply List.ext_getElem
    · simp [rho'C, hSlen]
    · intro i h1 h2
      have hi : i < n := by simpa [rho'C] using h1
      simp only [rho'C, List.getElem_map, List.getElem_range]
      rw [(hSC i hi).1, List.getD_eq_getElem _ _ h2]
  have S2 : (sh.cell 5 (n - 1)).val M = shiftF.2 := by
    rw [(hSC (n - 1) (by omega)).2, show n - 1 + 1 = n by omega, List.take_of_length_le (by simp)]
  -- block B
  have hrhoC : (rhoC oA n).map (Cell.val M) = (samplesAt (feAt sig) P (n + 3 + 6)).take n := by
    rw [hrhoF, rhoC, List.map_map]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.mp hi
    show (oA.cell i 0).val M = f i
    rw [hcA i (by omega), hVf i (by omega)]
  have heZ : ∀ k < 64, ((eZC oA n).getD k default).val M =
      eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) k := by
    intro k hk
    have : (eZC oA n).getD k default = oA.cell (n + 96 + k) 0 := by
      simp [eZC, List.getD_eq_getElem?_getD, hk]
    rw [this, hcA _ (by omega), hzetaF, ← hzetaV, ← AZ k hk, eZs_eq n k hk, val_loc]
  have heL : ∀ k < 8, ((eLC oA n).getD k default).val M =
      eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) k := by
    intro k hk
    have : (eLC oA n).getD k default = oA.cell (n + 20 + k) 0 := by
      simp [eLC, List.getD_eq_getElem?_getD, hk]
    rw [this, hcA _ (by omega), hlamF, ← hlamV, ← AL k hk, eLs_eq n k hk, val_loc]
  have hFB := fix_of_loop (hokB oA sh) hhB (jf := 0) (by simp)
  obtain ⟨-, B2, B3⟩ := chGlueB_val hS hFB (by simp [rhoC]; omega) (by simp [rhoC, rho'C])
    (by simp only [chQC, chQ2] at hT; omega)
  set pB := pS.adv (scGadget D 2 (chQ1 n Q) Mode.plain (oA.cell (2 * n + 165) 0) pS).2 with hpB
  generalize hoB : (loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1)))) pB).1 = oB
    at hFB B2 B3 hh2 hhC haC
  have hlenB : (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))).length = 8 * n + 131 := by
    simp only [chGlueB, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
      List.length_cons, List.length_nil, rhoC]
    rw [shiftRecIns_length _ _ _ _ _ _ (by simp [rho'C])]; simp; omega
  simp only [rhoC, List.length_map, List.length_range] at B2 B3
  rw [show ((List.range n).map fun i => oA.cell i 0) = rhoC oA n from rfl, hrhoC, S1] at B2 B3
  rw [S2] at B3
  set inSF := scalarsAt (feAt sig) (chP2 p P + 40) kBits with hinSF
  have hinS : ∀ k < 64, feAt sig (8 * (chQB n Q + 3 * k)) = inSF.getD k 0 := by
    intro k hk
    rw [hinSF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [kBits, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
    refine congrArg (feAt sig) ?_
    simp only [chQB, chQ1, chP2, chP1, roundLen, ← hndef]; omega
  have hclaimB : (oB.cell (8 * n + 130) 0).val M = chSc2Target0 p (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF := by
    have hsum : ∑ k ∈ Finset.range 64, ((eZC oA n).getD k default).val M * feAt sig (8 * (chQB n Q + 3 * k)) =
        ∑ q ∈ Finset.range 64, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) q * inSF.getD q 0 :=
      Finset.sum_congr rfl fun k hk => by
        have hk' := Finset.mem_range.mp hk
        rw [heZ k hk', hinS k hk']
    rw [cell_iterV (len := (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))).length) oB
      (by rw [hlenB]; omega), B3, chSc2Target0_eq p _ _ _ (by simp [samplesAt, hndef])
      (by simp [hinSF, kBits, scalarsAt]), hsum]
    ring
  -- the two-round sumcheck
  have hq2 : 8 * chQ2 n Q - 40 = chP3 p P := by
    simp only [chQ2, chQB, chQ1, chP3, chP2, chP1, roundLen, kBits, ringStages, ← hndef]; omega
  have hSC2 := sc_spec_plain (R := 2) (D := 1) (by omega) (scTpl_ok_2 _) (by norm_num) (by simp [chQ2, chQB, chQ1] <;> omega) hS
    (by simp [chQC, roundLanes] at hT ⊢ <;> omega) hh2
  set p2 := pB.adv (loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1)))) pB).2
    with hp2
  generalize hsc2 : (scGadget 1 2 (chQ2 n Q) .plain (oB.cell (8 * n + 130) 0) p2).1 = sc2 at hSC2 hhC haC
  rw [hq2, hclaimB] at hSC2
  set sc2F := scSpec (feAt sig) 3 (chP3 p P) (chSc2Target0 p (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF)
    [none, none] with hsc2F
  change ∀ i < 2, Cell.val M (sc2.cell 2 i) = sc2F.1.getD i 0 ∧ Cell.val M (sc2.cell 5 i) =
    (scSpec (feAt sig) 3 (chP3 p P) (chSc2Target0 p (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF)
      (([none, none] : List (Option FE)).take (i + 1))).2 at hSC2
  have hmu : [sc2.cell 2 0, sc2.cell 2 1].map (Cell.val M) = sc2F.1 := by
    have hl : sc2F.1.length = 2 := by rw [hsc2F, lnk_scSpec_length]; rfl
    have h2 : sc2F.1 = [sc2F.1.getD 0 0, sc2F.1.getD 1 0] := by
      match hm : sc2F.1, hl with
      | [a, b], _ => rfl
    rw [h2, ← (hSC2 0 (by omega)).1, ← (hSC2 1 (by omega)).1]
    rfl
  have hf2 : (sc2.cell 5 1).val M = sc2F.2 := by
    rw [(hSC2 1 (by omega)).2]; rfl
  -- block C
  have hokC' := hokC oA sh sc2 oB
  have hFC := fix_of_loop hokC' hhC (jf := 0) (by simp)
  have hlenC := chGlueC_length (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate rfl
  have hrl : (rho'C sh n).length = n := by simp [rho'C]
  have hlast := chGlueC_last (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate rfl
  have hAs := assert_of_loop hokC' haC (jf := 0) (by simp) (t := 151 + (rho'C sh n).length)
    (by rw [hlenC]; omega) (by rw [hlast])
  rw [hlast] at hAs
  simp only [List.getD_cons_zero, List.getD_cons_succ, val_loc] at hAs
  have C := chGlueC_sound hS hFC rfl (by omega) (by rw [hrl]; omega) hAs hg
  rw [hf2, hmu, S1] at C
  have hprodRho : (oA.cell (2 * n + 163) 0).val M = ((samplesAt (feAt sig) P (n + 3 + 6)).take n).prod := by
    rw [hcA _ (by omega), AP, hrhoF]
  have heqE : (oB.cell (8 * n + 123) 0).val M = eqEval ((samplesAt (feAt sig) P (n + 3 + 6)).take n) shiftF.1 := by
    rw [cell_iterV (len := (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))).length) oB
      (by rw [hlenB]; omega), B2]
  rw [hprodRho, heqE] at C
  set ySF := scalarsAt (feAt sig) (chP4 p P + 40) kBits with hySF
  have hyS : ∀ q < 64, feAt sig (8 * (chQC n Q + 3 * q)) = ySF.getD q 0 := by
    intro q hq
    rw [hySF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [kBits, List.getElem?_map, List.getElem?_range hq, Option.map_some, Option.getD_some]
    refine congrArg (feAt sig) ?_
    simp only [chQC, chQ2, chQB, chQ1, chP4, chP3, chP2, chP1, roundLen, kBits, ringStages, ← hndef]; omega
  have hα : ∑ m ∈ Finset.range 4, eqW sc2F.1 m * ((eLC oA n).getD m default).val M =
      ∑ m ∈ Finset.range 4, eqW sc2F.1 m * eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) m :=
    Finset.sum_congr rfl fun m hm => by rw [heL m (by have := Finset.mem_range.mp hm; omega)]
  have hβ : ∑ m ∈ Finset.range 4, eqW sc2F.1 m * ((eLC oA n).getD (m + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW sc2F.1 m * eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) (m + 1) :=
    Finset.sum_congr rfl fun m hm => by rw [heL (m + 1) (by have := Finset.mem_range.mp hm; omega)]
  have hS1 : ∑ q ∈ Finset.range 56, ((eZC oA n).getD (q + 8) default).val M * feAt sig (8 * (chQC n Q + 3 * q)) =
      ∑ q ∈ Finset.range 56, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) (q + 8) * ySF.getD q 0 :=
    Finset.sum_congr rfl fun q hq => by
      have := Finset.mem_range.mp hq
      rw [heZ (q + 8) (by omega), hyS q (by omega)]
  have hS2 : ∑ q ∈ Finset.range 8, ((eZC oA n).getD q default).val M * feAt sig (8 * (chQC n Q + 3 * (q + 56))) =
      ∑ q ∈ Finset.range 8, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) q * ySF.getD (q + 56) 0 :=
    Finset.sum_congr rfl fun q hq => by
      have := Finset.mem_range.mp hq
      rw [heZ q (by omega), hyS (q + 56) (by omega)]
  rw [hα, hβ, hS1, hS2] at C
  -- F's check
  have hok : (chLink0 p blk ySlot (chLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P r w pub)).1 =
      (sc2F.2 == eqMasked ((samplesAt (feAt sig) P (n + 3 + 6)).take n) shiftF.1 *
        sumE ((List.range 64).map fun q => sumE ((List.range 4).map fun m =>
          (eqKernel sc2F.1).getD m 0 * padWeight (omegaCH (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3)
            ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3))) m q) * ySF.getD q 0)) := by
    rfl
  rw [hok, lnk_fe_beq, chLink_sum_eq _ _ _ _ (by simp [samplesAt] <;> omega) (by simp [samplesAt] <;> omega)
    (by rw [hsc2F, lnk_scSpec_length]; rfl), C]
  unfold eqMasked eqOnes
  rw [prodE_eq_prod, prodE_eq_prod]
  ring

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithCHSound` =====

/-!
# QA1 links: the `KS` link circuit (phase 7) and its soundness against `F`

The shift sumcheck from a zero claim (`ksShiftTarget = 0` in `M3.ofParts` (ex `M3.v0`)), then block E (`ksBlockE`,
v1's `ksGlueE`, `39n + 15` rows, `n = ksLog`, or KS14's `ksGlueE14`, `39n + |sel| + 14` rows, lvm2 CR-K): the `n`
challenges `ρ`, the four scalars `Y_ω, in_ω, M_ω, X_ω`, `contShift` as `pre(B − 1) + pre(K + 31) + pre(K)` (three
`preRecIns`, `K = ksSplit p + 399`, `contShift_eq`), `eqEval(ρ, ρ')` (`n` `lin` + `n` products), and the gated
assertion `gate·(f − contShift·Y − eqEval·(in + (1 + x_r)M + x_r X)) = 0` (v1) or
`gate·(f − contShift·Y − eqEval·(in + M + sel·X)) = 0` (KS14, `sel = Π_{j ≥ ksXLog} ρ'_j`, a product chain over the
four cells) (`ksLink0`'s check). **`ksLink_sound`**: if the assertion holds (gate `1`), `ksLink0`'s check on what
`F` reads in phase 7 (`ksLinkView`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- `pre(H)`'s source after a `preRecIns` at `a` over `n ≥ 1` coordinates. -/
def preP (a n : Nat) : Src := .loc (a + 12 * (n - 1) + 8)

/-- **Block E** (positions in the doc above). -/
def ksGlueE (n QR QV H1 H2 H3 : Nat) (rho' : List Cell) (xr f gate : Cell) : List Ins :=
  let z : Src := .loc (n + 4)
  let base : Src × Src × Src := (z, z, .loc (n + 5))
  let rS : List Src := (List.range n).map Src.loc
  let r'S : List Src := rho'.map cellSrc
  let g := 39 * n + 8
  loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns z (n + 6) rS r'S H1 base ++ (preRecIns z (13 * n + 6) rS r'S H2 base ++
    (preRecIns z (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns z (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    [linI 0 1 (cellSrc xr) (cellSrc xr), mulI (.loc g) (.loc (n + 2)) (.loc (n + 1)),
      mulI (cellSrc xr) (.loc (n + 3)) (.loc (g + 1)), mulI (.loc (39 * n + 7)) (.loc (g + 2)) z,
      mulI (.loc (37 * n + 7)) (.loc n) (.loc (g + 3)), addI (cellSrc f) (.loc (g + 4)),
      ⟨.assert0, .K, [.loc (g + 5), cellSrc gate]⟩]))))))))

theorem ksGlueE_length (n QR QV H1 H2 H3 : Nat) (rho' : List Cell) (xr f gate : Cell) (hl : rho'.length = n) :
    (ksGlueE n QR QV H1 H2 H3 rho' xr f gate).length = 39 * n + 15 := by
  simp only [ksGlueE, List.length_append, loadsAt, List.length_map, List.length_range, mulChainIns_length,
    List.length_cons, List.length_nil]
  rw [preRecIns_length _ _ _ _ _ _ (by simp [hl]), preRecIns_length _ _ _ _ _ _ (by simp [hl]),
    preRecIns_length _ _ _ _ _ _ (by simp [hl])]
  simp; (clear * -; omega)

theorem preRecOut_fst (a : Nat) (xs ys : List Src) (base : Src × Src × Src) (hn : 1 ≤ xs.length)
    (hl : xs.length = ys.length) : (preRecOut a xs ys base).1 = preP a xs.length := by
  match xs, ys, hn, hl with
  | x0 :: x, y0 :: y, _, _ => simp [preRecOut, preP]

theorem getD_rangeMap0 (g : Nat → FE) {n i : Nat} (hi : i < n) : ((List.range n).map g).getD i 0 = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_mapCell (M : Mem) (l : List Cell) {i : Nat} (hi : i < l.length) :
    (l.map (Cell.val M)).getD i 0 = (l.getD i default).val M := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- **Block E's assertion**: with gate `1`, `f = (Σ pre)·Y + eqEval·(in + (1 + x_r)M + x_r X)`. -/
theorem ksGlueE_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n QR QV H1 H2 H3 : Nat} {rho' : List Cell} {xr f gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (ksGlueE n QR QV H1 H2 H3 rho' xr f gate) V) (hn : 1 ≤ n) (hl : rho'.length = n)
    (hH : H1 < 2 ^ n ∧ H2 < 2 ^ n ∧ H3 < 2 ^ n)
    (hTR : QR + 9 * n + 2 < T + 9) (hTV : QV + 3 * 4 + 2 < T + 3)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD (39 * n + 13) 0 = 0) (hg : gate.val M = 1) :
    f.val M = (preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H1 +
        preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H2 +
        preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H3) *
        feAt sig (8 * QV) +
      eqEval ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) *
        (feAt sig (8 * (QV + 3)) + (1 + xr.val M) * feAt sig (8 * (QV + 6)) + xr.val M * feAt sig (8 * (QV + 9))) := by
  have hlen := ksGlueE_length n QR QV H1 H2 H3 rho' xr f gate hl
  set rS : List Src := (List.range n).map Src.loc with hrS
  set r'S : List Src := rho'.map cellSrc with hr'S
  set base : Src × Src × Src := (.loc (n + 4), .loc (n + 4), .loc (n + 5)) with hbase
  have hs : Seg (ksGlueE n QR QV H1 H2 H3 rho' xr f gate) 0
    (loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns (.loc (n + 4)) (n + 6) rS r'S H1 base ++ (preRecIns (.loc (n + 4)) (13 * n + 6) rS r'S H2 base ++
    (preRecIns (.loc (n + 4)) (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns (.loc (n + 4)) (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    [linI 0 1 (cellSrc xr) (cellSrc xr), mulI (.loc (39 * n + 8)) (.loc (n + 2)) (.loc (n + 1)),
      mulI (cellSrc xr) (.loc (n + 3)) (.loc (39 * n + 8 + 1)), mulI (.loc (39 * n + 7)) (.loc (39 * n + 8 + 2)) (.loc (n + 4)),
      mulI (.loc (37 * n + 7)) (.loc n) (.loc (39 * n + 8 + 3)), addI (cellSrc f) (.loc (39 * n + 8 + 4)),
      ⟨.assert0, .K, [.loc (39 * n + 8 + 5), cellSrc gate]⟩]))))))))) := seg_whole _
  have lP : ∀ a H, (preRecIns (.loc (n + 4)) a rS r'S H base).length = 12 * n := by
    intro a H; rw [preRecIns_length _ _ _ _ _ _ (by simp [hrS, hr'S, hl])]; simp [hrS]
  have lM : (mulChainIns (.loc (n + 4)) (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i))).length = n := by
    rw [mulChainIns_length]; simp
  obtain ⟨sL1, s1⟩ := seg_split hs
  obtain ⟨sL2, s2⟩ := seg_split s1
  obtain ⟨sZ, s3⟩ := seg_split s2
  obtain ⟨sP1, s4⟩ := seg_split s3
  obtain ⟨sP2, s5⟩ := seg_split s4
  obtain ⟨sP3, s6⟩ := seg_split s5
  obtain ⟨sAD, s7⟩ := seg_split s6
  obtain ⟨sAR, s8⟩ := seg_split s7
  obtain ⟨sMC, sF⟩ := seg_split s8
  replace sL2 := seg_at (m := n) sL2 (by simp [loadsAt])
  replace sZ := seg_at (m := n + 4) sZ (by simp [loadsAt])
  replace sP1 := seg_at (m := n + 6) sP1 (by simp [loadsAt])
  replace sP2 := seg_at (m := 13 * n + 6) sP2 (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sP3 := seg_at (m := 25 * n + 6) sP3 (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sAD := seg_at (m := 37 * n + 6) sAD (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sAR := seg_at (m := 37 * n + 8) sAR (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sMC := seg_at (m := 38 * n + 8) sMC (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sF := seg_at (m := 39 * n + 8) sF (by simp [loadsAt, lP, lM] <;> (clear * -; omega))
  have hR : ∀ i < n, V.getD i 0 = feAt sig (8 * (QR + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL1 (by rw [hlen]; (clear * - hn hl lM; omega)) (by omega) hi
    rwa [Nat.zero_add] at this
  have hK : ∀ k < 4, V.getD (n + k) 0 = feAt sig (8 * (QV + 3 * k)) := fun k hk =>
    loadsAt_val hS hF sL2 (by rw [hlen]; (clear * - hn hl lM; omega)) (by omega) hk
  have hz : V.getD (n + 4) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> (clear * - hn hl lM; omega)) (i := 0) (by simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 5) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> (clear * - hn hl lM; omega)) (i := 1) (by simp) (by simp [linI])
    rw [show n + 4 + 1 = n + 5 by (clear * -; omega)] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 4)).val (iterXv M o jf) V = 0 := hz
  have hrv : rS.map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => feAt sig (8 * (QR + 9 * i)) := by
    rw [hrS, List.map_map]; apply List.map_congr_left; intro i hi
    exact hR i (List.mem_range.mp hi)
  have hr'v : r'S.map (Src.val (iterXv M o jf) V) = rho'.map (Cell.val M) := by
    rw [hr'S, List.map_map]; apply List.map_congr_left; intro c _
    exact iterXv_cell M o jf c
  have hlS : rS.length = r'S.length := by simp [hrS, hr'S, hl]
  have hnS : rS.length = n := by simp [hrS]
  have pre : ∀ a H, H < 2 ^ n → Seg (ksGlueE n QR QV H1 H2 H3 rho' xr f gate) a (preRecIns (.loc (n + 4)) a rS r'S H base) →
      a + 12 * n ≤ 39 * n + 15 →
      (preP a n).val (iterXv M o jf) V = preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i)))
        (rho'.map (Cell.val M)) H := by
    intro a H hH sP hle
    have := preRec_val hF hzs a rS r'S H base hlS (by rw [hnS]; exact hH) hz hz h1 sP (by rw [hlen, hnS]; omega)
    rw [preCF_eq _ _ _ (by simp [hrv, hr'v, hl]), hrv, hr'v] at this
    have e := congrArg Prod.fst this
    simp only at e
    rw [show preP a n = (preRecOut a rS r'S base).1 by rw [preRecOut_fst _ _ _ _ (by (clear * - hn hl lM hlS hnS; omega)) hlS, hnS], e]
  have p1 := pre (n + 6) H1 hH.1 sP1 (by (clear * - hn hl lM hlS hnS; omega))
  have p2 := pre (13 * n + 6) H2 hH.2.1 sP2 (by (clear * - hn hl lM hlS hnS; omega))
  have p3 := pre (25 * n + 6) H3 hH.2.2 sP3 (by (clear * - hn hl lM hlS hnS; omega))
  have a0 := fix_seg hF sAD (by rw [hlen]; simp <;> (clear * - hn hl lM hlS hnS; omega)) (i := 0) (by simp) (by simp [addI, linI])
  have a1 := fix_seg hF sAD (by rw [hlen]; simp <;> (clear * - hn hl lM hlS hnS; omega)) (i := 1) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_addI, val_loc, Nat.add_zero] at a0 a1
  rw [p1, p2] at a0
  rw [show 37 * n + 6 + 1 = 37 * n + 7 by (clear * -; omega), a0, p3] at a1
  -- eqEval
  have hAR : ∀ i < n, V.getD (37 * n + 8 + i) 0 = 1 + feAt sig (8 * (QR + 9 * i)) + (rho'.getD i default).val M := by
    intro i hi
    have hrow : ((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)).getD i default =
        linI 1 1 (.loc i) (r'S.getD i default) := by simp [List.getD_eq_getElem?_getD, hi]
    rw [fix_seg hF sAR (by rw [hlen]; simp <;> (clear * - hn hl lM hlS hnS; omega)) (by simpa using hi) (by rw [hrow]; simp [linI]), hrow,
      eval_linI', val_loc, hR i hi]
    have : (r'S.getD i default).val (iterXv M o jf) V = (rho'.getD i default).val M := by
      rw [hr'S, List.getD_eq_getElem _ _ (by simp [hl, hi]), List.getElem_map, List.getD_eq_getElem _ _ (by simp [hl, hi])]
      exact iterXv_cell M o jf _
    rw [this, show FE.ofK 1 = 1 from rfl, one_mul]; ring
  have hMC := mulChain_val hF hzs ((List.range n).map fun i => Src.loc (37 * n + 8 + i)) (38 * n + 8) (.loc (n + 5)) sMC
    (by rw [hlen]; simp <;> (clear * -; omega))
  have hsrc : sumSrc (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => Src.loc (37 * n + 8 + i)) = .loc (39 * n + 7) := by
    simp only [sumSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by (clear * - hn hl lM hlS hnS; omega)), show 38 * n + 8 + n - 1 = 39 * n + 7 by (clear * - hn hl lM hlS hnS; omega)]
  rw [hsrc, val_loc, val_loc, h1, one_mul, List.map_map] at hMC
  have hE : V.getD (39 * n + 7) 0 = eqEval ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) := by
    rw [hMC, eqEval_range _ _ (by simp [hl]), list_prod_range]
    simp only [List.length_map, List.length_range]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [Function.comp_def, val_loc]
    rw [hAR i hi', getD_rangeMap0 _ hi', getD_mapCell _ _ (by rw [hl]; exact hi')]
  -- the final rows
  have f0 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  have f2 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 2) (by simp) (by simp [mulI])
  have f3 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 3) (by simp) (by simp [mulI])
  have f4 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 4) (by simp) (by simp [mulI])
  have f5 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 5) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_linI', eval_mulI, eval_addI, val_loc, Nat.add_zero,
    iterXv_cell] at f0 f1 f2 f3 f4 f5
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  simp only [hcell] at f0 f1 f2 f3 f4 f5 hA
  rw [show 39 * n + 13 = 39 * n + 8 + 5 by (clear * -; omega)] at hA
  have k0 : V.getD n 0 = feAt sig (8 * QV) := by have := hK 0 (by (clear * -; omega)); simpa using this
  have k1 : V.getD (n + 1) 0 = feAt sig (8 * (QV + 3)) := by have := hK 1 (by (clear * -; omega)); simpa using this
  have k2 : V.getD (n + 2) 0 = feAt sig (8 * (QV + 6)) := by have := hK 2 (by (clear * -; omega)); simpa using this
  have k3 : V.getD (n + 3) 0 = feAt sig (8 * (QV + 9)) := by have := hK 3 (by (clear * -; omega)); simpa using this
  rw [hg, one_mul, f5, f4, f3, f2, f1, f0, a1, hE, hz, k0, k1, k2, k3] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl] at hA
  linear_combination hA

/-! ## Block E under KS14 (lvm2 CR-K)

`ksGlueE14`: block E with the check `f = (Σ pre)·Y + eqEval·(in + M + sel·X)`, `sel` the product of the cells
`sel` (the coordinates `xl … n − 1` of `ρ'`, a `mulChainIns` from `1`): `39n + |sel| + 14` rows. -/

/-- **Block E under KS14** (positions: block E's up to `39n + 7`, then the selector's product chain, then the
check). -/
def ksGlueE14 (n QR QV H1 H2 H3 : Nat) (rho' sel : List Cell) (f gate : Cell) : List Ins :=
  let z : Src := .loc (n + 4)
  let base : Src × Src × Src := (z, z, .loc (n + 5))
  let rS : List Src := (List.range n).map Src.loc
  let r'S : List Src := rho'.map cellSrc
  let sS : List Src := sel.map cellSrc
  let g := 39 * n + 8 + sel.length
  loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns z (n + 6) rS r'S H1 base ++ (preRecIns z (13 * n + 6) rS r'S H2 base ++
    (preRecIns z (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns z (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    (mulChainIns z (39 * n + 8) (.loc (n + 5)) sS ++
    [addI (.loc (n + 1)) (.loc (n + 2)), mulI (sumSrc (39 * n + 8) (.loc (n + 5)) sS) (.loc (n + 3)) (.loc g),
      mulI (.loc (39 * n + 7)) (.loc (g + 1)) z, mulI (.loc (37 * n + 7)) (.loc n) (.loc (g + 2)),
      addI (cellSrc f) (.loc (g + 3)), ⟨.assert0, .K, [.loc (g + 4), cellSrc gate]⟩])))))))))

theorem ksGlueE14_length (n QR QV H1 H2 H3 : Nat) (rho' sel : List Cell) (f gate : Cell) (hl : rho'.length = n) :
    (ksGlueE14 n QR QV H1 H2 H3 rho' sel f gate).length = 39 * n + sel.length + 14 := by
  simp only [ksGlueE14, List.length_append, loadsAt, List.length_map, List.length_range, mulChainIns_length,
    List.length_cons, List.length_nil]
  rw [preRecIns_length _ _ _ _ _ _ (by simp [hl]), preRecIns_length _ _ _ _ _ _ (by simp [hl]),
    preRecIns_length _ _ _ _ _ _ (by simp [hl])]
  simp; (clear * -; omega)

/-- **Block E's assertion under KS14**: with gate `1`, `f = (Σ pre)·Y + eqEval·(in + M + (Π sel)·X)`. -/
theorem ksGlueE14_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n QR QV H1 H2 H3 : Nat} {rho' sel : List Cell} {f gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (ksGlueE14 n QR QV H1 H2 H3 rho' sel f gate) V) (hn : 1 ≤ n)
    (hl : rho'.length = n) (hH : H1 < 2 ^ n ∧ H2 < 2 ^ n ∧ H3 < 2 ^ n)
    (hTR : QR + 9 * n + 2 < T + 9) (hTV : QV + 3 * 4 + 2 < T + 3)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD (39 * n + sel.length + 12) 0 = 0)
    (hg : gate.val M = 1) :
    f.val M = (preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H1 +
        preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H2 +
        preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H3) *
        feAt sig (8 * QV) +
      eqEval ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) *
        (feAt sig (8 * (QV + 3)) + feAt sig (8 * (QV + 6)) + (sel.map (Cell.val M)).prod * feAt sig (8 * (QV + 9))) := by
  have hlen := ksGlueE14_length n QR QV H1 H2 H3 rho' sel f gate hl
  set w := sel.length with hw
  set rS : List Src := (List.range n).map Src.loc with hrS
  set r'S : List Src := rho'.map cellSrc with hr'S
  set sS : List Src := sel.map cellSrc with hsS
  set base : Src × Src × Src := (.loc (n + 4), .loc (n + 4), .loc (n + 5)) with hbase
  have hs : Seg (ksGlueE14 n QR QV H1 H2 H3 rho' sel f gate) 0
    (loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns (.loc (n + 4)) (n + 6) rS r'S H1 base ++ (preRecIns (.loc (n + 4)) (13 * n + 6) rS r'S H2 base ++
    (preRecIns (.loc (n + 4)) (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns (.loc (n + 4)) (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    (mulChainIns (.loc (n + 4)) (39 * n + 8) (.loc (n + 5)) sS ++
    [addI (.loc (n + 1)) (.loc (n + 2)), mulI (sumSrc (39 * n + 8) (.loc (n + 5)) sS) (.loc (n + 3))
        (.loc (39 * n + 8 + w)),
      mulI (.loc (39 * n + 7)) (.loc (39 * n + 8 + w + 1)) (.loc (n + 4)),
      mulI (.loc (37 * n + 7)) (.loc n) (.loc (39 * n + 8 + w + 2)), addI (cellSrc f) (.loc (39 * n + 8 + w + 3)),
      ⟨.assert0, .K, [.loc (39 * n + 8 + w + 4), cellSrc gate]⟩])))))))))) := seg_whole _
  have lP : ∀ a H, (preRecIns (.loc (n + 4)) a rS r'S H base).length = 12 * n := by
    intro a H; rw [preRecIns_length _ _ _ _ _ _ (by simp [hrS, hr'S, hl])]; simp [hrS]
  have lM : (mulChainIns (.loc (n + 4)) (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i))).length = n := by
    rw [mulChainIns_length]; simp
  have lS : (mulChainIns (.loc (n + 4)) (39 * n + 8) (.loc (n + 5)) sS).length = w := by
    rw [mulChainIns_length]; simp [hsS, hw]
  obtain ⟨sL1, s1⟩ := seg_split hs
  obtain ⟨sL2, s2⟩ := seg_split s1
  obtain ⟨sZ, s3⟩ := seg_split s2
  obtain ⟨sP1, s4⟩ := seg_split s3
  obtain ⟨sP2, s5⟩ := seg_split s4
  obtain ⟨sP3, s6⟩ := seg_split s5
  obtain ⟨sAD, s7⟩ := seg_split s6
  obtain ⟨sAR, s8⟩ := seg_split s7
  obtain ⟨sMC, s9⟩ := seg_split s8
  obtain ⟨sSel, sF⟩ := seg_split s9
  replace sL2 := seg_at (m := n) sL2 (by simp [loadsAt])
  replace sZ := seg_at (m := n + 4) sZ (by simp [loadsAt])
  replace sP1 := seg_at (m := n + 6) sP1 (by simp [loadsAt])
  replace sP2 := seg_at (m := 13 * n + 6) sP2 (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sP3 := seg_at (m := 25 * n + 6) sP3 (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sAD := seg_at (m := 37 * n + 6) sAD (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sAR := seg_at (m := 37 * n + 8) sAR (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sMC := seg_at (m := 38 * n + 8) sMC (by simp [loadsAt, lP] <;> (clear * -; omega))
  replace sSel := seg_at (m := 39 * n + 8) sSel (by simp [loadsAt, lP, lM] <;> (clear * -; omega))
  replace sF := seg_at (m := 39 * n + 8 + w) sF (by simp [loadsAt, lP, lM, lS] <;> (clear * -; omega))
  have hR : ∀ i < n, V.getD i 0 = feAt sig (8 * (QR + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL1 (by rw [hlen]; (clear * - hl hlen lM lS; omega)) (by omega) hi
    rwa [Nat.zero_add] at this
  have hK : ∀ k < 4, V.getD (n + k) 0 = feAt sig (8 * (QV + 3 * k)) := fun k hk =>
    loadsAt_val hS hF sL2 (by rw [hlen]; (clear * - hn hl hlen lM lS; omega)) (by omega) hk
  have hz : V.getD (n + 4) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> (clear * - hn hl hlen lM lS; omega)) (i := 0) (by simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 5) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> (clear * - hn hl hlen lM lS; omega)) (i := 1) (by simp) (by simp [linI])
    rw [show n + 4 + 1 = n + 5 by (clear * -; omega)] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 4)).val (iterXv M o jf) V = 0 := hz
  have hrv : rS.map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => feAt sig (8 * (QR + 9 * i)) := by
    rw [hrS, List.map_map]; apply List.map_congr_left; intro i hi
    exact hR i (List.mem_range.mp hi)
  have hr'v : r'S.map (Src.val (iterXv M o jf) V) = rho'.map (Cell.val M) := by
    rw [hr'S, List.map_map]; apply List.map_congr_left; intro c _
    exact iterXv_cell M o jf c
  have hsv : sS.map (Src.val (iterXv M o jf) V) = sel.map (Cell.val M) := by
    rw [hsS, List.map_map]; apply List.map_congr_left; intro c _
    exact iterXv_cell M o jf c
  have hlS : rS.length = r'S.length := by simp [hrS, hr'S, hl]
  have hnS : rS.length = n := by simp [hrS]
  have pre : ∀ a H, H < 2 ^ n → Seg (ksGlueE14 n QR QV H1 H2 H3 rho' sel f gate) a
      (preRecIns (.loc (n + 4)) a rS r'S H base) → a + 12 * n ≤ 39 * n + w + 14 →
      (preP a n).val (iterXv M o jf) V = preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i)))
        (rho'.map (Cell.val M)) H := by
    intro a H hH sP hle
    have := preRec_val hF hzs a rS r'S H base hlS (by rw [hnS]; exact hH) hz hz h1 sP (by rw [hlen, hnS]; omega)
    rw [preCF_eq _ _ _ (by simp [hrv, hr'v, hl]), hrv, hr'v] at this
    have e := congrArg Prod.fst this
    simp only at e
    rw [show preP a n = (preRecOut a rS r'S base).1 by rw [preRecOut_fst _ _ _ _ (by (clear * - hn hl lM hlS hnS; omega)) hlS, hnS], e]
  have p1 := pre (n + 6) H1 hH.1 sP1 (by (clear * - hn hl lM lS hlS hnS; omega))
  have p2 := pre (13 * n + 6) H2 hH.2.1 sP2 (by (clear * - hn hl lM lS hlS hnS; omega))
  have p3 := pre (25 * n + 6) H3 hH.2.2 sP3 (by (clear * - hn hl lM lS hlS hnS; omega))
  have a0 := fix_seg hF sAD (by rw [hlen]; simp <;> (clear * - hn hl lM lS hlS hnS; omega)) (i := 0) (by simp) (by simp [addI, linI])
  have a1 := fix_seg hF sAD (by rw [hlen]; simp <;> (clear * - hn hl lM lS hlS hnS; omega)) (i := 1) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_addI, val_loc, Nat.add_zero] at a0 a1
  rw [p1, p2] at a0
  rw [show 37 * n + 6 + 1 = 37 * n + 7 by (clear * -; omega), a0, p3] at a1
  -- eqEval
  have hAR : ∀ i < n, V.getD (37 * n + 8 + i) 0 = 1 + feAt sig (8 * (QR + 9 * i)) + (rho'.getD i default).val M := by
    intro i hi
    have hrow : ((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)).getD i default =
        linI 1 1 (.loc i) (r'S.getD i default) := by simp [List.getD_eq_getElem?_getD, hi]
    rw [fix_seg hF sAR (by rw [hlen]; simp <;> (clear * - hn hl lM lS hlS hnS; omega)) (by simpa using hi) (by rw [hrow]; simp [linI]), hrow,
      eval_linI', val_loc, hR i hi]
    have : (r'S.getD i default).val (iterXv M o jf) V = (rho'.getD i default).val M := by
      rw [hr'S, List.getD_eq_getElem _ _ (by simp [hl, hi]), List.getElem_map, List.getD_eq_getElem _ _ (by simp [hl, hi])]
      exact iterXv_cell M o jf _
    rw [this, show FE.ofK 1 = 1 from rfl, one_mul]; ring
  have hMC := mulChain_val hF hzs ((List.range n).map fun i => Src.loc (37 * n + 8 + i)) (38 * n + 8) (.loc (n + 5)) sMC
    (by rw [hlen]; simp <;> (clear * - lS; omega))
  have hsrc : sumSrc (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => Src.loc (37 * n + 8 + i)) = .loc (39 * n + 7) := by
    simp only [sumSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by (clear * - hn hl lM hlS hnS; omega)), show 38 * n + 8 + n - 1 = 39 * n + 7 by (clear * - hn hl lM hlS hnS; omega)]
  rw [hsrc, val_loc, val_loc, h1, one_mul, List.map_map] at hMC
  have hE : V.getD (39 * n + 7) 0 = eqEval ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) := by
    rw [hMC, eqEval_range _ _ (by simp [hl]), list_prod_range]
    simp only [List.length_map, List.length_range]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [Function.comp_def, val_loc]
    rw [hAR i hi', getD_rangeMap0 _ hi', getD_mapCell _ _ (by rw [hl]; exact hi')]
  -- the selector
  have hSel := mulChain_val hF hzs sS (39 * n + 8) (.loc (n + 5)) sSel (by rw [hlen, hsS, List.length_map]; (clear * -; omega))
  rw [val_loc, h1, one_mul, hsv] at hSel
  -- the final rows
  have f0 := fix_seg hF sF (by rw [hlen]; simp <;> (clear * -; omega)) (i := 0) (by simp) (by simp [addI, linI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp <;> (clear * -; omega)) (i := 1) (by simp) (by simp [mulI])
  have f2 := fix_seg hF sF (by rw [hlen]; simp <;> (clear * -; omega)) (i := 2) (by simp) (by simp [mulI])
  have f3 := fix_seg hF sF (by rw [hlen]; simp <;> (clear * -; omega)) (i := 3) (by simp) (by simp [mulI])
  have f4 := fix_seg hF sF (by rw [hlen]; simp <;> (clear * -; omega)) (i := 4) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_addI, val_loc, Nat.add_zero,
    iterXv_cell] at f0 f1 f2 f3 f4
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  simp only [hcell] at f0 f1 f2 f3 f4 hA
  rw [hSel] at f1
  rw [show 39 * n + w + 12 = 39 * n + 8 + w + 4 by (clear * -; omega)] at hA
  have k0 : V.getD n 0 = feAt sig (8 * QV) := by have := hK 0 (by (clear * -; omega)); simpa using this
  have k1 : V.getD (n + 1) 0 = feAt sig (8 * (QV + 3)) := by have := hK 1 (by (clear * -; omega)); simpa using this
  have k2 : V.getD (n + 2) 0 = feAt sig (8 * (QV + 6)) := by have := hK 2 (by (clear * -; omega)); simpa using this
  have k3 : V.getD (n + 3) 0 = feAt sig (8 * (QV + 9)) := by have := hK 3 (by (clear * -; omega)); simpa using this
  rw [hg, one_mul, f4, f3, f2, f1, f0, a1, hE, hz, k0, k1, k2, k3] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination hA

/-! ## The gadget and its soundness -/

/-- The `KS` shift sumcheck's first message lane (`n = ksLog`). -/
def ksQ1 (n Q : Nat) : Nat := Q + 9 * (n + laneBits)
/-- The four scalars' first lane. -/
def ksQV (n Q : Nat) : Nat := ksQ1 n Q + 15 * n

/-- The selector's cells: the shift sumcheck's challenges `xl … n − 1` (`xl = ksXLog p`, KS14). -/
def ksSelC (p : Params) (sh : LoopOut) : List Cell := (rho'C sh p.ksLog).drop (ksXLog p)

/-- `P20`'s selector cells (KS13): `ρ'_9 … ρ'_12`. -/
theorem ksSelC_P20 (sh : LoopOut) : ksSelC P20 sh = [sh.cell 2 9, sh.cell 2 10, sh.cell 2 11, sh.cell 2 12] := rfl

/-- **Block E of a parameter set** (lvm2 CR-K): KS14's (`ksLog ≤ recRowsLog`) or v1's; the WOTS leaf's
continuation rows from the split (`ksSplit p + 399`). -/
def ksBlockE (p : Params) (Q : Nat) (sh : LoopOut) (gate : Cell) : List Ins :=
  if p.ksLog ≤ p.recRowsLog then
    ksGlueE14 p.ksLog Q (ksQV p.ksLog Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31) (ksSplit p + 399)
      (rho'C sh p.ksLog) (ksSelC p sh) (sh.cell 5 (p.ksLog - 1)) gate
  else
    ksGlueE p.ksLog Q (ksQV p.ksLog Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31) (ksSplit p + 399)
      (rho'C sh p.ksLog) (sh.cell 2 p.recRowsLog) (sh.cell 5 (p.ksLog - 1)) gate

/-- **The `KS` link gadget** (phase 7's arithmetic): a zero claim, the shift sumcheck, block E. -/
def ksLinkGadget (p : Params) (D Q : Nat) (gate : Cell) : BM Unit := do
  let oD ← loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)])
  let sh ← scGadget D 2 (ksQ1 p.ksLog Q) .plain (oD.cell 0 0)
  let _ ← loop [] (tplOf (ksBlockE p Q sh gate))
  pure ()

theorem prodE_eq_prodF (l : List FE) : prodE l = l.prod := by
  suffices h : ∀ a : FE, l.foldl (· * ·) a = a * l.prod by rw [prodE, h, one_mul]
  induction l with
  | nil => intro a; simp
  | cons b l ih => intro a; rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/-- **The `KS` link circuit is sound for `F`'s phase-7 check** (both layouts). -/
theorem ksLink_sound (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    (D : Nat) {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T P Q : Nat}
    (rk : List FE) (pub : Pub) (gate : Cell)
    (hn : 1 ≤ p.ksLog) (h4 : 4 ≤ p.ksLog) (hD : p.ksLog ≤ 2 ^ D) (hPQ : P + 40 = 8 * Q)
    (hB : 1 ≤ spongeBlocks p) (hB2 : spongeBlocks p ≤ 2 ^ p.ksLog) (hK : ksSplit p + 431 ≤ 2 ^ p.ksLog)
    (hokE : ∀ sh : LoopOut, SLok (ksBlockE p Q sh gate) = true)
    (hS : Streamed M sig T) (hT : ksQV p.ksLog Q + 3 * 4 + 3 ≤ T) (hg : gate.val M = 1)
    (h : SegsHold c M ptr (ksLinkGadget p D Q gate ptr).2)
    (hA : SegsAssert M ptr (ksLinkGadget p D Q gate ptr).2) :
    (ksLink0 p (ksLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 = true := by
  set n := p.ksLog with hndef
  simp only [ksLinkGadget] at h hA
  rw [hold_bind] at h; obtain ⟨hhD, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhS, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhE, -⟩ := h
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨haE, -⟩ := hA
  -- the zero claim
  generalize hoD : (loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)]) ptr).1 = oD at hhS hhE haE
  have hFD : Fix (iterXv M oD 0) [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)]
      (iterV M oD 1 0) := by
    rw [← hoD]; exact fix_of_loop rfl hhD (by simp)
  have hz : (oD.cell 0 0).val M = 0 := by
    rw [cell_iterV (len := 1) oD (by (clear * -; omega)),
      fix_at hFD (n := 0) (i := linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)) (by simp) rfl (by simp [linI]),
      eval_linI']
    show iterXv M oD 0 (.ext ⟨.K, Q, []⟩) + FE.ofK 1 * iterXv M oD 0 (.ext ⟨.K, Q, []⟩) + FE.ofK 0 = 0
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero, CharTwo.add_self_eq_zero]
  -- the shift sumcheck
  have hq1 : 8 * ksQ1 n Q - 40 = ksP1 p P := by simp only [ksQ1, ksP1, laneBits, ← hndef]; (clear * - hPQ h4; omega)
  have hSC := sc_spec_plain (R := n) (by (clear * -; omega)) (scTpl_ok_2 _) hD (by simp [ksQ1]; (clear * - hPQ; omega)) hS
    (by simp [ksQV, ksQ1, roundLanes, laneBits] at hT ⊢; (clear * - hT; omega)) hhS
  set pS := ptr.adv (loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)]) ptr).2 with hpS
  generalize hsh : (scGadget D 2 (ksQ1 n Q) .plain (oD.cell 0 0) pS).1 = sh at hSC hhE haE
  rw [hq1, hz] at hSC
  set shiftF := scSpec (feAt sig) 3 (ksP1 p P) 0 (List.replicate n none) with hshiftF
  have hSlen : shiftF.1.length = n := by rw [hshiftF, lnk_scSpec_length]; simp
  have S1 : (rho'C sh n).map (Cell.val M) = shiftF.1 := by
    apply List.ext_getElem
    · simp [rho'C, hSlen]
    · intro i h1 h2
      have hi : i < n := by simpa [rho'C] using h1
      simp only [rho'C, List.getElem_map, List.getElem_range]
      rw [(hSC i hi).1, List.getD_eq_getElem _ _ h2]
  have S2 : (sh.cell 5 (n - 1)).val M = shiftF.2 := by
    rw [(hSC (n - 1) (by (clear * - h4 hSlen; omega))).2, show n - 1 + 1 = n by (clear * - h4 hSlen; omega), List.take_of_length_le (by simp)]
  -- F's view
  have hrhoF : (samplesAt (feAt sig) P (n + laneBits)).take n = (List.range n).map fun i => feAt sig (8 * (Q + 9 * i)) := by
    rw [samplesAt, take_range_map _ (by (clear * -; omega))]
    apply List.map_congr_left; intro i _; congr 1; (clear * - hPQ; omega)
  set valsF := scalarsAt (feAt sig) (ksP2 p P + 40) 4 with hvalsF
  have hv : ∀ k < 4, feAt sig (8 * (ksQV n Q + 3 * k)) = valsF.getD k 0 := by
    intro k hk
    rw [hvalsF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
    congr 1
    simp only [ksQV, ksQ1, ksP2, ksP1, roundLen, laneBits, ← hndef]; (clear * - hPQ; omega)
  have v0 := hv 0 (by (clear * -; omega)); have v1 := hv 1 (by (clear * -; omega)); have v2 := hv 2 (by (clear * -; omega)); have v3 := hv 3 (by (clear * -; omega))
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at v0 v1 v2 v3
  rw [show ksQV n Q + 3 * 2 = ksQV n Q + 6 by (clear * -; omega)] at v2
  rw [show ksQV n Q + 3 * 3 = ksQV n Q + 9 by (clear * -; omega)] at v3
  -- block E
  have hokE' := hokE sh
  by_cases h14 : n ≤ p.recRowsLog
  · -- KS14
    have hxl : ksXLog p = n - 4 := by simp only [ksXLog, ← hndef, if_pos h14]
    have hn4 : 4 ≤ n := h4
    simp only [ksBlockE, ← hndef, if_pos h14] at hokE' hhE haE
    have hFE := fix_of_loop hokE' hhE (jf := 0) (by simp)
    have hsl : (ksSelC p sh).length = 4 := by simp [ksSelC, rho'C, hxl, ← hndef]; (clear * - h4 hSlen; omega)
    have hlenE := ksGlueE14_length n Q (ksQV n Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31)
      (ksSplit p + 399) (rho'C sh n) (ksSelC p sh) (sh.cell 5 (n - 1)) gate (by simp [rho'C])
    have hlast : (ksGlueE14 n Q (ksQV n Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31) (ksSplit p + 399)
        (rho'C sh n) (ksSelC p sh) (sh.cell 5 (n - 1)) gate).getD (39 * n + (ksSelC p sh).length + 13) default =
        ⟨.assert0, .K, [.loc (39 * n + 8 + (ksSelC p sh).length + 4), cellSrc gate]⟩ := by
      rw [show 39 * n + (ksSelC p sh).length + 13 = (ksGlueE14 n Q (ksQV n Q) (spongeBlocks p - 1)
        (ksSplit p + 399 + 31) (ksSplit p + 399) (rho'C sh n) (ksSelC p sh) (sh.cell 5 (n - 1)) gate).length - 1
        by (clear * - hSlen hsl hlenE; omega), List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
      simp [ksGlueE14, List.getLast?_append, List.getLast?_cons]
    have hAs := assert_of_loop hokE' haE (jf := 0) (by simp) (t := 39 * n + (ksSelC p sh).length + 13)
      (by rw [hlenE]; (clear * -; omega)) (by rw [hlast])
    rw [hlast] at hAs
    simp only [List.getD_cons_zero, List.getD_cons_succ, val_loc] at hAs
    rw [show 39 * n + 8 + (ksSelC p sh).length + 4 = 39 * n + (ksSelC p sh).length + 12 by (clear * -; omega)] at hAs
    have E := ksGlueE14_sound hS hFE hn (by simp [rho'C])
      ⟨by (clear * - hB hB2; omega), by (clear * - hK; omega), by (clear * - hK; omega)⟩ (by simp only [ksQV, ksQ1] at hT; (clear * - h4 hT hSlen; omega)) (by (clear * - hT; omega)) hAs hg
    rw [S1, S2, v0, v1, v2, v3] at E
    have hsel : ((ksSelC p sh).map (Cell.val M)).prod = prodE (shiftF.1.drop (ksXLog p)) := by
      rw [prodE_eq_prodF, ksSelC, List.map_drop, ← hndef, S1]
    rw [hsel] at E
    have hok : (ksLink0 p (ksLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 =
        (shiftF.2 == contShift p ((samplesAt (feAt sig) P (n + laneBits)).take n) shiftF.1 * valsF.getD 0 0 +
          eqEval ((samplesAt (feAt sig) P (n + laneBits)).take n) shiftF.1 *
            (valsF.getD 1 0 + valsF.getD 2 0 + prodE (shiftF.1.drop (ksXLog p)) * valsF.getD 3 0)) := by
      simp only [ksLink0, ← hndef, if_pos h14]; rfl
    rw [hok, lnk_fe_beq, contShift_eq p _ _ (by simp [samplesAt]; omega) hSlen hB hB2 hK, hrhoF, ← E]
  · -- v1's layout
    have hr' : p.recRowsLog < n := by (clear * - hSlen h14; omega)
    simp only [ksBlockE, ← hndef, if_neg h14] at hokE' hhE haE
    have hFE := fix_of_loop hokE' hhE (jf := 0) (by simp)
    have Sx : (sh.cell 2 p.recRowsLog).val M = shiftF.1.getD p.recRowsLog 0 := (hSC _ hr').1
    have hlenE := ksGlueE_length n Q (ksQV n Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31)
      (ksSplit p + 399) (rho'C sh n) (sh.cell 2 p.recRowsLog) (sh.cell 5 (n - 1)) gate (by simp [rho'C])
    have hlast : (ksGlueE n Q (ksQV n Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31) (ksSplit p + 399)
        (rho'C sh n) (sh.cell 2 p.recRowsLog) (sh.cell 5 (n - 1)) gate).getD (39 * n + 14) default =
        ⟨.assert0, .K, [.loc (39 * n + 8 + 5), cellSrc gate]⟩ := by
      rw [show 39 * n + 14 = (ksGlueE n Q (ksQV n Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31)
        (ksSplit p + 399) (rho'C sh n) (sh.cell 2 p.recRowsLog) (sh.cell 5 (n - 1)) gate).length - 1 by (clear * - hSlen hlenE; omega),
        List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
      simp [ksGlueE, List.getLast?_append, List.getLast?_cons]
    have hAs := assert_of_loop hokE' haE (jf := 0) (by simp) (t := 39 * n + 14) (by rw [hlenE]; (clear * -; omega))
      (by rw [hlast])
    rw [hlast] at hAs
    simp only [List.getD_cons_zero, List.getD_cons_succ, val_loc] at hAs
    rw [show 39 * n + 8 + 5 = 39 * n + 13 by (clear * -; omega)] at hAs
    have E := ksGlueE_sound hS hFE hn (by simp [rho'C])
      ⟨by (clear * - hB hB2; omega), by (clear * - hK; omega), by (clear * - hK; omega)⟩ (by simp only [ksQV, ksQ1] at hT; (clear * - h4 hT hSlen; omega)) (by (clear * - hT; omega)) hAs hg
    rw [S1, S2, Sx, v0, v1, v2, v3] at E
    have hok : (ksLink0 p (ksLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 =
        (shiftF.2 == contShift p ((samplesAt (feAt sig) P (n + laneBits)).take n) shiftF.1 * valsF.getD 0 0 +
          eqEval ((samplesAt (feAt sig) P (n + laneBits)).take n) shiftF.1 *
            (valsF.getD 1 0 + (1 + shiftF.1.getD p.recRowsLog 0) * valsF.getD 2 0 +
              shiftF.1.getD p.recRowsLog 0 * valsF.getD 3 0)) := by
      simp only [ksLink0, ← hndef, if_neg h14]; rfl
    rw [hok, lnk_fe_beq, contShift_eq p _ _ (by simp [samplesAt]; omega) hSlen hB hB2 hK, hrhoF, ← E]

end Lvm.Q1
