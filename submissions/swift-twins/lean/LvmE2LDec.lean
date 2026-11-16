-- New for lvm2 MB-LIN (MBL-V, stage S2GL): V_S without the mini-bus's table phase. The bus phase is S2GU's (`α`, `β`,
-- the grand products, the leaf-decomposition scalar, the bus check); its three final GKR claims become three K-linear
-- claims on `C_main` (push, pull, count) that join the opening batch where the table columns' claims stood.
import LvmE2UDec
import LvmS2GLLin

/-!
# V_S at S2GL

* **`dMiniL p m pub`**: S2GU's mini-bus (`TypedV.dMiniT`) up to the bus check; no `ξ`, no table sumcheck. It returns
  the grand products' point `ζ` and the leaf decomposition (`BusOut`: each table's form per side, the sides' totals).
* **The three claims** (MBL-L's `LvmS2GLLin.mbClaimsN`, the native twin of `mbClaimsL`): side `s` (push, pull, count) is `sumClaim ν (mbPartsN tabs bus ζ s) (mbValueN ..)`,
  one part `(coef, ⟨τ_t, off_c⟩, ζ.take τ_t)` per committed column the side's flushes name (`sideColsL`; push 259,
  pull 446, count 24 at blob U'), in table and column order; value = total + the tables' constants (char 2).
* **`linWS`** (V_S's run weights; `mbColsN` = the parts without the point): `eq(ζ.take τ, y.take τ)` once per `τ`,
  folded into the low table of the coordinates `[τ, 12)`; the coordinates `[12, 18)` and `[18, k)` one table each,
  shared by every column and side; a column is three lookups. In the small shape only the regions holding a column are
  visited, each with its own coordinates.
* **`decideProgLG p pT B N vk c`**: S2GU's decision program with the bus phase `dMiniL`, the three claims in the
  opening, the tape's sponge intervals from `B` sponge blocks (`contIvOf B`; S2GU's `contIvU = contIvOf 3961`).
-/

set_option autoImplicit false

namespace Lvm.E2L

open Lvm DM Lvm.E2V Lvm.E2T Lvm.E2U

/-! ## The bus phase without the table phase -/

/-- **The mini-bus at S2GL**: `dMiniT`'s bus phase and bus check; the point `ζ` and the leaf decomposition. -/
def dMiniL (p : Params) (m : M3) (pub : Pub) : DM (List FE × BusOut) := do
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  pure (point, bus)

end Lvm.E2L

/-! ## The three claims' columns (`LvmS2GLLin.mbPartsN` without the point) -/

namespace Lvm.M3

/-- One table's columns on side `s` under its form `f`. -/
def tabColsN (t : Tab) (f : Lvm.Form) (s : ℕ) : List (FE × Nat × Nat) :=
  (sideColsL t s).filterMap fun c ↦ match t.cols[c]? with
    | some (ColSrc.com _ off) => some (coefN f c, t.τ, off)
    | _ => none

/-- The tables walked with their forms (no index lookups). -/
def colsGo (s : ℕ) : List Tab → List (List Lvm.Form) → List (FE × Nat × Nat)
  | [], _ => []
  | t :: ts, fs => tabColsN t ((fs.headD []).getD s default) s ++ colsGo s ts fs.tail

/-- **Side `s`'s columns** without the point (`mbPartsN` = these with `pt.take τ`, `mbPartsN_cols`): coefficient,
log-height, word. -/
def mbColsN (tabs : List Tab) (o : Lvm.BusOut) (s : ℕ) : List (FE × Nat × Nat) :=
  colsGo s tabs o.forms

theorem headD_drop' {α : Type} (d : α) : ∀ (l : List α) (n : ℕ), (l.drop n).headD d = l.getD n d
  | [], _ => by simp
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => by rw [List.drop_succ_cons, headD_drop' d l n]; rfl

theorem colsGo_eq (o : Lvm.BusOut) (s : ℕ) : ∀ (tabs : List Tab) (n : ℕ),
    colsGo s tabs (o.forms.drop n) = (tabs.zipIdx n).flatMap fun tj ↦ tabColsN tj.1 (formN o tj.2 s) s
  | [], _ => rfl
  | t :: ts, n => by
    rw [colsGo, List.zipIdx_cons, List.flatMap_cons, ← colsGo_eq o s ts (n + 1), List.tail_drop]
    congr 2
    unfold formN
    rw [headD_drop']

theorem mbPartsN_cols (tabs : List Tab) (o : Lvm.BusOut) (pt : List FE) (s : ℕ) :
    mbPartsN tabs o pt s = (mbColsN tabs o s).map fun q => (q.1, (⟨q.2.1, q.2.2⟩ : Lvm.Placement), pt.take q.2.1) := by
  unfold mbPartsN mbColsN
  rw [show o.forms = o.forms.drop 0 from rfl, colsGo_eq, List.map_flatMap]
  refine List.flatMap_congr fun tj _ => ?_
  unfold tabColsN
  rw [List.map_filterMap]
  refine List.filterMap_congr fun c _ => ?_
  rcases tj.1.cols[c]? with _ | (_ | _) <;> rfl

/-! ## The three claims' values with each fixed column evaluated once (`mbValsF_eq`) -/

/-- Table `t`'s fixed columns' closed forms at `pt` (`0` at a committed column). -/
def fixEvs (t : Tab) (pt : List FE) : List FE :=
  t.cols.map fun c => match c with
    | ColSrc.fix _ ev => ev pt
    | _ => 0

/-- `constN` with the fixed columns' values `evs` given. -/
def constE (t : Tab) (evs : List FE) (f : Lvm.Form) : FE :=
  Lvm.sumE (f.terms.map fun m ↦ match m.1 with
    | [] => m.2
    | [c] => match t.cols[c]? with
      | some (ColSrc.fix _ _) => m.2 * evs.getD c 0
      | _ => 0
    | _ => 0)

theorem constE_eq (t : Tab) (f : Lvm.Form) (pt : List FE) : constE t (fixEvs t pt) f = constN t f pt := by
  unfold constE constN
  congr 1
  refine List.map_congr_left fun m _ => ?_
  rcases m with ⟨_ | ⟨c, _ | _⟩, a⟩
  · rfl
  · dsimp only
    rcases h : t.cols[c]? with _ | (_ | ⟨g, ev⟩)
    · rfl
    · rfl
    · dsimp only
      unfold fixEvs
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
      rfl
  · rfl

/-- The tables (with their fixed columns' values) walked with their forms. -/
def constsGo (s : ℕ) : List (Tab × List FE) → List (List Lvm.Form) → List FE
  | [], _ => []
  | te :: ts, fs => constE te.1 te.2 ((fs.headD []).getD s default) :: constsGo s ts fs.tail

/-- **The three sides' values** (`mbValueN`'s), each fixed column's closed form evaluated once for the sides. -/
def mbValsF (tabs : List Tab) (o : Lvm.BusOut) (pt : List FE) : List FE :=
  let E := tabs.map fun t => (t, fixEvs t (pt.take t.τ))
  (List.range 3).map fun s => o.totals.getD s 0 + Lvm.sumE (constsGo s E o.forms)

theorem constsGo_eq (o : Lvm.BusOut) (s : ℕ) (pt : List FE) : ∀ (tabs : List Tab) (n : ℕ),
    constsGo s (tabs.map fun t => (t, fixEvs t (pt.take t.τ))) (o.forms.drop n) =
      (tabs.zipIdx n).map fun tj => constN tj.1 (formN o tj.2 s) (pt.take tj.1.τ)
  | [], _ => rfl
  | t :: ts, n => by
    rw [List.map_cons, constsGo, List.zipIdx_cons, List.map_cons, ← constsGo_eq o s pt ts (n + 1),
      List.tail_drop, headD_drop', constE_eq]
    rfl

theorem mbValsF_eq (tabs : List Tab) (o : Lvm.BusOut) (pt : List FE) :
    mbValsF tabs o pt = (List.range 3).map (mbValueN tabs o pt) := by
  unfold mbValsF
  refine List.map_congr_left fun s _ => ?_
  unfold mbValueN
  rw [show o.forms = o.forms.drop 0 from rfl, constsGo_eq]

end Lvm.M3

namespace Lvm.E2L

open Lvm DM Lvm.E2V Lvm.E2T Lvm.E2U

/-! ## The weights -/

/-- Columns `(coef, τ, off)` as `sumClaim` parts at `ζ`. -/
def partsOf (ζ : List FE) (cs : List (FE × Nat × Nat)) : List (FE × Placement × List FE) :=
  cs.map fun q => (q.1, ⟨q.2.1, q.2.2⟩, ζ.take q.2.1)

/-- **The claims of the sides' columns `css`** (values `vs`) on `C_main` (block `⟨nu, 0⟩`, tails `0`). -/
def linClaims (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (vs : List FE) :
    List (Com × BlockClaim × FE) :=
  css.zipIdx.map fun ck => (.main, sumClaim nu (partsOf ζ ck.1) (vs.getD ck.2 0), 0)

/-- The split coordinates of the fast weights: `[τ, 12)` per `τ`, `[12, 18)`, `[18, k)`. -/
abbrev linK1 : Nat := 12

/-- See `linK1`. -/
abbrev linK2 : Nat := 18

/-- The distinct `τ ≤ 12` of the columns. -/
def lowTs (css : List (List (FE × Nat × Nat))) : List Nat :=
  css.foldl (fun ts cs => cs.foldl (fun ts q =>
    if q.2.1 ≤ linK1 && !ts.contains q.2.1 then ts ++ [q.2.1] else ts) ts) []

/-- `eqKernelA` with one product per entry (char 2: `a·(1 + r) = a + a·r`; `eqKA_eq`). -/
def eqKA (point : List FE) : Array FE :=
  point.foldl (fun out r => let m := out.map (· * r); Array.zipWith (· + ·) out m ++ m) #[1]

/-- The fast weights' tables at `y` over the coordinates `[0, k)`: per `τ ∈ ts` the pair `eq(ζ.take τ, y.take τ)`
and the kernel of `y[τ, 12)`, then the kernels of `y[12, min k 18)` and `y[18, k)`. -/
structure WTabs where
  /-- Per `τ`: `τ`, `eq(ζ.take τ, y.take τ)`, the kernel of `y[τ, 12)`. -/
  Ls : List (Nat × FE × Array FE)
  /-- `[12, min k 18)`. -/
  M : Array FE
  /-- `[18, k)`. -/
  T : Array FE

/-- See `WTabs`. -/
def wTabs (ζ y : List FE) (k : Nat) (ts : List Nat) : WTabs :=
  ⟨ts.map fun τ => (τ, eqEval (ζ.take τ) (y.take τ), eqKA ((y.drop τ).take (linK1 - τ))),
    eqKA ((y.drop linK1).take (min k linK2 - linK1)), eqKA ((y.drop linK2).take (k - linK2))⟩

/-- **A column's low term and key**: `(coef·L_τ[bits τ..12 of off], (τ + 1, off >>> 12))` when `τ`'s low table is
there and `τ ≤ 12 ≤ k`; otherwise its whole term `coef·wd τ off` under the key `(0, 0)` (factor `1`). -/
def partAK (W : WTabs) (k : Nat) (wd : Nat → Nat → FE) (q : FE × Nat × Nat) : FE × Nat × Nat :=
  match W.Ls.find? (·.1 == q.2.1) with
  | some L =>
    if q.2.1 ≤ linK1 ∧ linK1 ≤ k then
      (q.1 * L.2.2.getD ((q.2.2 >>> q.2.1) % 2 ^ (linK1 - q.2.1)) 0, q.2.1 + 1, q.2.2 >>> linK1)
    else (q.1 * wd q.2.1 q.2.2, 0, 0)
  | none => (q.1 * wd q.2.1 q.2.2, 0, 0)

/-- **A key's factor**: `eq(ζ.take τ, y.take τ)·M[mid]·T[top]·G hi` (`1` for the key `(0, 0)`). -/
def keyF (W : WTabs) (k : Nat) (G : Nat → FE) (key : Nat × Nat) : FE :=
  if key.1 = 0 then 1 else
    match W.Ls.find? (·.1 == key.1 - 1) with
    | some L => L.2.1 * W.M.getD (key.2 % 2 ^ (min k linK2 - linK1)) 0 *
        W.T.getD ((key.2 >>> (linK2 - linK1)) % 2 ^ (k - linK2)) 0 * G key.2
    | none => 0

/-- Runs of equal keys summed, each run's sum times its key's factor once. -/
def grpGo (F : Nat × Nat → FE) : FE → Nat × Nat → FE → List (FE × Nat × Nat) → FE
  | t, k, s, [] => t + F k * s
  | t, k, s, p :: l =>
    if p.2.1 == k.1 && p.2.2 == k.2 then grpGo F t k (s + p.1) l else grpGo F (t + F k * s) p.2 p.1 l

/-- See `grpGo`. -/
def grpSum (F : Nat × Nat → FE) : List (FE × Nat × Nat) → FE
  | [] => 0
  | p :: l => grpGo F 0 p.2 p.1 l

/-- The columns' order for `sideF`: by `off >>> 12`, then `τ` (equal keys adjacent). -/
def colLe (a b : FE × Nat × Nat) : Bool :=
  a.2.2 >>> linK1 < b.2.2 >>> linK1 || (a.2.2 >>> linK1 == b.2.2 >>> linK1 && a.2.1 ≤ b.2.1)

/-- **One side's weight**: `Σ coef·L[lo]` per key, times the key's factor (one product per column). -/
def sideF (W : WTabs) (k : Nat) (wd : Nat → Nat → FE) (G : Nat → FE) (cs : List (FE × Nat × Nat)) : FE :=
  grpSum (keyF W k G) ((cs.mergeSort colLe).map (partAK W k wd))

/-- A column with `off >>> 12 = hi` (and `τ ≤ 12`) lies in region `r` of the small shape. -/
def inRegionHi (nu : Nat) (r : Nat × Nat × Nat) (hi : Nat) : Bool :=
  (hi >>> (r.1 - linK1)) % 2 ^ (nu - r.1) == (r.2.1 >>> r.1) % 2 ^ (nu - r.1)

/-- The small shape's top factor of `hi`: `Σ_r [in r]·e_r·eq(bits 18.. of off, z[18, r.1))`. -/
def regG (nu : Nat) (z : List FE) (RE : List ((Nat × Nat × Nat) × FE)) (hi : Nat) : FE :=
  (RE.map fun d => if inRegionHi nu d.1 hi then
    d.2 * eqEval (selectorPoint (hi >>> (linK2 - linK1)) (d.1.1 - linK2)) ((z.drop linK2).take (d.1.1 - linK2))
    else 0).sum

/-- A column's term in region `r`'s weight (the specification's). -/
def gR (nu : Nat) (ζ x : List FE) (r : Nat × Nat × Nat) (τ off : Nat) : FE :=
  (⟨τ, off⟩ : Placement).eqAbove (TypedV.relocN nu x r) * eqEval (ζ.take τ) ((TypedV.relocN nu x r).take τ)

/-- The small shape's regions with their weights `eq_above(⟨r.1, r.2.2⟩, x.tail)·eq_above(⟨ν, 0⟩, y_r)`. -/
def regE (nu : Nat) (x : List FE) : List ((Nat × Nat × Nat) × FE) :=
  ((TypedV.regionsN nu).filter (Shape.meets ⟨nu, 0⟩)).map fun r =>
    (r, (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu, 0⟩ : Placement).eqAbove (TypedV.relocN nu x r))

/-- **The claims' stack weights at `x`, together** (`toStk` of `linClaims`; V_S's run weights). Big shape: the tables
once at `x` (`k = ν`). Small shape (`ν ≥ 21`): the tables once at `z = x.tail ++ 0…` (`k = 18`; every region's
point agrees with `z` below 18), the regions in each key's factor. Each side: its columns sorted by key, one product
per column, one factor per key. Otherwise (no such point is opened) the specification's form. -/
def linWS (s : Bool) (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (x : List FE) : List FE :=
  if s ∧ 21 ≤ nu then
    let h := 1 - x.headD 0
    let z := x.tail ++ List.replicate (nu - 1) 0
    let RE := regE nu x
    let W := wTabs ζ z linK2 (lowTs css)
    css.map fun cs => h * sideF W linK2 (fun τ off => (RE.map fun d => d.2 * gR nu ζ x d.1 τ off).sum)
      (regG nu z RE) cs
  else if s = false ∧ x.length = nu then
    let W := wTabs ζ x nu (lowTs css)
    css.map (sideF W nu (fun τ off => eqEval (selectorPoint (off >>> τ) (nu - τ)) ((x.drop τ).take (nu - τ)) *
      eqEval (ζ.take τ) (x.take τ)) fun _ => 1)
  else css.map fun cs => (toStk s nu (sumClaim nu (partsOf ζ cs) 0, 0)).1 x

/-! ## `mbWF_eq`: the run weights are the claims' stack weights -/

section WF

open Lvm.Shape (eqEval_append eqEval_nil_left eqEval_nil_right length_selectorPointF eqEval_cons)

theorem foldl_add_sum (l : List FE) (a : FE) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem sumE_eq_sum (l : List FE) : Lvm.sumE l = l.sum := by
  unfold Lvm.sumE
  rw [foldl_add_sum, zero_add]

theorem selectorPoint_congr {a b n : Nat} (h : ∀ i < n, a.testBit i = b.testBit i) :
    selectorPoint a n = selectorPoint b n := by
  unfold selectorPoint
  refine List.map_congr_left fun i hi => ?_
  have hi' := h i (List.mem_range.mp hi)
  rw [Nat.testBit, Nat.testBit] at hi'
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at hi' ⊢
  congr 1
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with hb | hb <;>
    simp_all [Nat.and_one_is_mod]

theorem selectorPoint_mod (a n : Nat) : selectorPoint (a % 2 ^ n) n = selectorPoint a n :=
  selectorPoint_congr fun i hi => by rw [Nat.testBit_mod_two_pow]; simp [hi]

/-- A table lookup is the `eq` of the point at the index's low bits. -/
theorem tabLook (z : List FE) (i : Nat) :
    (eqKernelA z).getD (i % 2 ^ z.length) 0 = eqEval (selectorPoint i z.length) z := by
  rw [Lvm.VEq.getD_eqKernelA, Lvm.Q1.eqKernel_getD z (Nat.mod_lt _ (Nat.two_pow_pos _)),
    ← Lvm.Har.eqEval_selector, selectorPoint_mod]

theorem tabLook' (z : List FE) (i n : Nat) (h : z.length = n) :
    (eqKernelA z).getD (i % 2 ^ n) 0 = eqEval (selectorPoint i n) z := by
  subst h; exact tabLook z i

/-- `eqKA` is `eqKernelA`. -/
theorem eqKA_eq (p : List FE) : eqKA p = eqKernelA p := by
  unfold eqKA eqKernelA
  suffices h : ∀ a : Array FE,
      p.foldl (fun out r => let m := out.map (· * r); Array.zipWith (· + ·) out m ++ m) a =
        p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) a from h _
  induction p with
  | nil => intro a; rfl
  | cons r p ih =>
    intro a
    have hs : Array.zipWith (· + ·) a (a.map (· * r)) = a.map (· * (1 + r)) := by
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_zipWith, Array.getElem_map]
      ring
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp only [hs]

/-- `eq` of a selector against a concatenation. -/
theorem eqEval_sel_append (a m n : Nat) (z₁ z₂ : List FE) (h : z₁.length = m) :
    eqEval (selectorPoint a (m + n)) (z₁ ++ z₂) = eqEval (selectorPoint a m) z₁ * eqEval (selectorPoint (a >>> m) n) z₂ := by
  rw [Lvm.E2U.selectorPoint_add, eqEval_append (by rw [length_selectorPointF, h])]

/-- **The direct weight in three lookups** (`τ ≤ 12 ≤ k ≤ |y|`). -/
theorem split3 (y : List FE) (k τ off : Nat) (hτ : τ ≤ linK1) (hk1 : linK1 ≤ k) (hk : k ≤ y.length) :
    (eqKA ((y.drop τ).take (linK1 - τ))).getD ((off >>> τ) % 2 ^ (linK1 - τ)) 0 *
      (eqKA ((y.drop linK1).take (min k linK2 - linK1))).getD ((off >>> linK1) % 2 ^ (min k linK2 - linK1)) 0 *
      (eqKA ((y.drop linK2).take (k - linK2))).getD ((off >>> linK1 >>> (linK2 - linK1)) % 2 ^ (k - linK2)) 0 =
    eqEval (selectorPoint (off >>> τ) (k - τ)) ((y.drop τ).take (k - τ)) := by
  have e1 : linK1 = 12 := rfl
  have e2 : linK2 = 18 := rfl
  rw [eqKA_eq, eqKA_eq, eqKA_eq, ← Nat.shiftRight_add, show linK1 + (linK2 - linK1) = linK2 by omega]
  have h1 : ((y.drop τ).take (linK1 - τ)).length = linK1 - τ := by simp; omega
  have h2 : ((y.drop linK1).take (min k linK2 - linK1)).length = min k linK2 - linK1 := by simp; omega
  have h3 : ((y.drop linK2).take (k - linK2)).length = k - linK2 := by simp; omega
  rw [tabLook' _ _ _ h1, tabLook' _ _ _ h2, tabLook' _ _ _ h3]
  have hsplit : (y.drop τ).take (k - τ) = ((y.drop τ).take (linK1 - τ) ++
      (y.drop linK1).take (min k linK2 - linK1)) ++ (y.drop linK2).take (k - linK2) := by
    rw [show k - τ = (linK1 - τ) + ((min k linK2 - linK1) + (k - linK2)) by omega, List.take_add,
      List.take_add, List.append_assoc]
    simp only [List.drop_drop]
    rw [show τ + (linK1 - τ) = linK1 by omega]
    by_cases hk18 : linK2 ≤ k
    · rw [show linK1 + (min k linK2 - linK1) = linK2 by omega]
    · rw [show k - linK2 = 0 by omega]; simp
  have hlen : k - τ = ((linK1 - τ) + (min k linK2 - linK1)) + (k - linK2) := by omega
  rw [hsplit, hlen, eqEval_sel_append _ _ _ _ _ (by rw [List.length_append, h1, h2]),
    eqEval_sel_append _ _ _ _ _ h1]
  simp only [← Nat.shiftRight_add]
  have h18 : selectorPoint (off >>> (τ + (linK1 - τ + (min k linK2 - linK1)))) (k - linK2) =
      selectorPoint (off >>> linK2) (k - linK2) := by
    by_cases hk18 : linK2 ≤ k
    · rw [show τ + (linK1 - τ + (min k linK2 - linK1)) = linK2 by omega]
    · rw [show k - linK2 = 0 by omega]; rfl
  rw [h18, show τ + (linK1 - τ) = linK1 by omega]

/-- **A column's fast term times its key's factor is its term** (given that the shape's direct weight `wd` is the
fast form wherever the fast path applies). -/
theorem partAK_mul (ζ y : List FE) (k : Nat) (ts : List Nat) (wd : Nat → Nat → FE) (G : Nat → FE)
    (hk : k ≤ y.length)
    (hwd : ∀ τ off, τ ≤ linK1 → linK1 ≤ k → eqEval (selectorPoint (off >>> τ) (k - τ)) ((y.drop τ).take (k - τ)) *
      eqEval (ζ.take τ) (y.take τ) * G (off >>> linK1) = wd τ off) (q : FE × Nat × Nat) :
    (partAK (wTabs ζ y k ts) k wd q).1 * keyF (wTabs ζ y k ts) k G (partAK (wTabs ζ y k ts) k wd q).2 =
      q.1 * wd q.2.1 q.2.2 := by
  unfold partAK
  split
  · rename_i L hL
    split
    · rename_i hc
      obtain ⟨hτ, hk1⟩ := hc
      have hL1 : L.1 = q.2.1 := by simpa using List.find?_some hL
      have hmem := List.mem_of_find?_eq_some hL
      simp only [wTabs, List.mem_map] at hmem
      obtain ⟨τ', -, rfl⟩ := hmem
      simp only at hL1
      subst hL1
      have hk2 : q.2.1 + 1 - 1 = q.2.1 := by omega
      simp only [keyF, Nat.add_one_ne_zero, ↓reduceIte, hk2, hL]
      rw [← hwd _ _ hτ hk1, ← split3 y k _ q.2.2 hτ hk1 hk]
      simp only [wTabs]
      ring
    · simp [keyF]
  · simp [keyF]

theorem grpGo_eq (F : Nat × Nat → FE) : ∀ (l : List (FE × Nat × Nat)) (t : FE) (k : Nat × Nat) (s : FE),
    grpGo F t k s l = t + F k * s + (l.map fun p => p.1 * F p.2).sum
  | [], t, k, s => by simp [grpGo]
  | p :: l, t, k, s => by
    unfold grpGo
    split
    · rename_i h
      have hk : p.2 = k := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact Prod.ext h.1 h.2
      rw [grpGo_eq F l, List.map_cons, List.sum_cons, hk]
      ring
    · rw [grpGo_eq F l, List.map_cons, List.sum_cons]
      ring

theorem grpSum_eq (F : Nat × Nat → FE) (l : List (FE × Nat × Nat)) :
    grpSum F l = (l.map fun p => p.1 * F p.2).sum := by
  cases l with
  | nil => rfl
  | cons p l =>
    simp only [grpSum, grpGo_eq, List.map_cons, List.sum_cons]
    ring

theorem sideF_eq (W : WTabs) (k : Nat) (wd : Nat → Nat → FE) (G : Nat → FE) (cs : List (FE × Nat × Nat)) :
    sideF W k wd G cs = (cs.map fun q => (partAK W k wd q).1 * keyF W k G (partAK W k wd q).2).sum := by
  unfold sideF
  rw [grpSum_eq, List.map_map]
  exact ((List.mergeSort_perm cs colLe).map _).sum_eq

/-- **A side's fast weight is the sum of its columns' direct terms.** -/
theorem sideF_wd (ζ y : List FE) (k : Nat) (ts : List Nat) (wd : Nat → Nat → FE) (G : Nat → FE)
    (hk : k ≤ y.length)
    (hwd : ∀ τ off, τ ≤ linK1 → linK1 ≤ k → eqEval (selectorPoint (off >>> τ) (k - τ)) ((y.drop τ).take (k - τ)) *
      eqEval (ζ.take τ) (y.take τ) * G (off >>> linK1) = wd τ off) (cs : List (FE × Nat × Nat)) :
    sideF (wTabs ζ y k ts) k wd G cs = (cs.map fun q => q.1 * wd q.2.1 q.2.2).sum := by
  rw [sideF_eq]
  exact congrArg List.sum (List.map_congr_left fun q _ => partAK_mul ζ y k ts wd G hk hwd q)

/-- A column's term in a claim's weight at `y` (`sumClaim`'s). -/
theorem sumClaim_weight (nu : Nat) (ζ : List FE) (cs : List (FE × Nat × Nat)) (v : FE) (y : List FE) :
    (sumClaim nu (partsOf ζ cs) v).weight y = (cs.map fun q =>
      q.1 * ((⟨q.2.1, q.2.2⟩ : Placement).eqAbove y * eqEval (ζ.take q.2.1) (y.take q.2.1))).sum := by
  simp only [sumClaim, partsOf, List.map_map]
  rw [sumE_eq_sum]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  simp only [Function.comp_apply]
  ring

theorem eqAbove_full (τ off : Nat) (y : List FE) :
    (⟨τ, off⟩ : Placement).eqAbove y =
      eqEval (selectorPoint (off >>> τ) (y.length - τ)) ((y.drop τ).take (y.length - τ)) := by
  unfold Placement.eqAbove
  rw [List.take_of_length_le (by simp)]

theorem eqAbove_nu (nu : Nat) (y : List FE) (h : y.length = nu) : (⟨nu, 0⟩ : Placement).eqAbove y = 1 := by
  unfold Placement.eqAbove
  rw [h, Nat.sub_self]
  rfl

/-- **Big shape**: the shared tables give each claim's weight. -/
theorem linWS_big (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (x : List FE) (hx : x.length = nu) :
    css.map (sideF (wTabs ζ x nu (lowTs css)) nu (fun τ off => eqEval (selectorPoint (off >>> τ) (nu - τ))
      ((x.drop τ).take (nu - τ)) * eqEval (ζ.take τ) (x.take τ)) fun _ => 1) =
      css.map fun cs => (toStk false nu (sumClaim nu (partsOf ζ cs) 0, 0)).1 x := by
  refine List.map_congr_left fun cs _ => ?_
  rw [sideF_wd ζ x nu _ _ _ hx.ge (fun τ off _ _ => by simp only [mul_one])]
  show _ = (⟨nu, 0⟩ : Placement).eqAbove x * (sumClaim nu (partsOf ζ cs) (0 : FE)).weight (x.take nu)
  rw [eqAbove_nu nu x hx, one_mul, List.take_of_length_le hx.le, sumClaim_weight]
  refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
  rw [eqAbove_full, hx]

end WF

section WFS

open Lvm.Shape (eqEval_append eqEval_nil_left eqEval_nil_right length_selectorPointF eqEval_cons)

theorem mod_eq_iff_testBit (a b n : Nat) : a % 2 ^ n = b % 2 ^ n ↔ ∀ i < n, a.testBit i = b.testBit i := by
  constructor
  · intro h i hi
    have := congrArg (fun m => m.testBit i) h
    simpa [Nat.testBit_mod_two_pow, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · simp [hi, h i hi]
    · simp [hi]

theorem eOfNat_bit (a i : Nat) : eOfNat ((a >>> i) % 2) = if a.testBit i then 1 else 0 := by
  have ht : a.testBit i = decide ((a >>> i) % 2 = 1) := by
    rw [Nat.testBit, Nat.one_and_eq_mod_two]
    rcases Nat.mod_two_eq_zero_or_one (a >>> i) with h | h <;> simp [h]
  rw [ht]
  rcases Nat.mod_two_eq_zero_or_one (a >>> i) with h | h <;> simp [h] <;> rfl

/-- **`eq` of two Boolean points**: `1` iff their bits agree. -/
theorem eqEval_sel_sel (a b : Nat) : ∀ n : Nat,
    eqEval (selectorPoint a n) (selectorPoint b n) = if ∀ i < n, a.testBit i = b.testBit i then 1 else 0
  | 0 => by simp [selectorPoint]
  | n + 1 => by
    rw [Lvm.E2U.selectorPoint_add a n 1, Lvm.E2U.selectorPoint_add b n 1,
      eqEval_append (by rw [length_selectorPointF, length_selectorPointF]), eqEval_sel_sel a b n]
    have h1 : ∀ c : Nat, selectorPoint (c >>> n) 1 = [if c.testBit n then (1 : FE) else 0] := fun c => by
      simp only [selectorPoint, List.range_one, List.map_cons, List.map_nil, Nat.shiftRight_zero, eOfNat_bit,
        Nat.testBit_shiftRight, Nat.add_zero]
    rw [h1, h1, eqEval_cons, eqEval_nil_left, mul_one]
    have hiff : (∀ i < n + 1, a.testBit i = b.testBit i) ↔ (∀ i < n, a.testBit i = b.testBit i) ∧
        a.testBit n = b.testBit n := ⟨fun h => ⟨fun i hi => h i (by omega), h n (by omega)⟩,
          fun h i hi => by rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl; exacts [h.1 i hi, h.2]⟩
    rw [if_congr hiff rfl rfl]
    by_cases hA : ∀ i < n, a.testBit i = b.testBit i <;>
      cases ha : a.testBit n <;> cases hb : b.testBit n <;>
        simp [hA, ha, hb, CharTwo.add_self_eq_zero, add_assoc]

/-- **The block weight at a relocated point** splits at the region's size `k`. -/
theorem eqAbove_reloc (τ off k nu b : Nat) (y₁ : List FE) (hy : y₁.length = k) (hτ : τ ≤ k) :
    (⟨τ, off⟩ : Placement).eqAbove (y₁ ++ selectorPoint b (nu - k)) =
      eqEval (selectorPoint (off >>> τ) (k - τ)) (((y₁ ++ selectorPoint b (nu - k)).drop τ).take (k - τ)) *
        (if ∀ i < nu - k, (off >>> k).testBit i = (b).testBit i then 1 else 0) := by
  unfold Placement.eqAbove
  have hl : (y₁ ++ selectorPoint b (nu - k)).length - τ = (k - τ) + (nu - k) := by
    rw [List.length_append, hy, length_selectorPointF]; omega
  have hd : (y₁ ++ selectorPoint b (nu - k)).drop τ = y₁.drop τ ++ selectorPoint b (nu - k) := by
    rw [List.drop_append_of_le_length (by omega)]
  rw [hl, hd, eqEval_sel_append _ _ _ _ _ (by rw [List.length_drop, hy]), ← Nat.shiftRight_add,
    show τ + (k - τ) = k by omega, eqEval_sel_sel, List.take_append_of_le_length (by rw [List.length_drop, hy]),
    List.take_of_length_le (by rw [List.length_drop, hy])]

theorem regionsN_fst {nu : Nat} {r : Nat × Nat × Nat} (h : r ∈ TypedV.regionsN nu) : r.1 = 18 ∨ r.1 = 20 := by
  unfold TypedV.regionsN at h
  simp only [List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨l, -, rfl⟩ | ⟨j, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem relocN_eq (nu : Nat) (x : List FE) (r : Nat × Nat × Nat) :
    TypedV.relocN nu x r = (x.tail ++ List.replicate (nu - 1) 0).take r.1 ++ selectorPoint (r.2.1 >>> r.1) (nu - r.1) :=
  rfl

theorem length_reloc_take (nu : Nat) (x : List FE) (r : Nat × Nat × Nat) (h : r.1 + 1 ≤ nu) :
    ((x.tail ++ List.replicate (nu - 1) 0).take r.1).length = r.1 := by
  simp; omega

/-- **A column's term in a region at its fast form** (`τ ≤ 12`, the region of size `18` or `20`). -/
theorem gR_fast (nu : Nat) (ζ x : List FE) (r : Nat × Nat × Nat) (hr : r.1 + 1 ≤ nu) (h18 : linK2 ≤ r.1)
    (τ off : Nat) (hτ : τ ≤ linK1) :
    gR nu ζ x r τ off =
      eqEval (selectorPoint (off >>> τ) (linK2 - τ)) (((x.tail ++ List.replicate (nu - 1) 0).drop τ).take (linK2 - τ)) *
      eqEval (ζ.take τ) ((x.tail ++ List.replicate (nu - 1) 0).take τ) *
      (if inRegionHi nu r (off >>> linK1) then eqEval (selectorPoint (off >>> linK1 >>> (linK2 - linK1)) (r.1 - linK2))
        (((x.tail ++ List.replicate (nu - 1) 0).drop linK2).take (r.1 - linK2)) else 0) := by
  have e1 : linK1 = 12 := rfl
  have e2 : linK2 = 18 := rfl
  set z := x.tail ++ List.replicate (nu - 1) 0 with hz
  have hzl : r.1 ≤ z.length := by rw [hz]; simp; omega
  have hl := length_reloc_take nu x r hr
  unfold gR
  rw [relocN_eq, eqAbove_reloc _ _ _ _ _ _ hl (by omega)]
  have hd : ((z.take r.1 ++ selectorPoint (r.2.1 >>> r.1) (nu - r.1)).drop τ).take (r.1 - τ) =
      (z.drop τ).take (r.1 - τ) := by
    rw [List.drop_append_of_le_length (by rw [hl]; omega), List.take_append_of_le_length (by simp; omega),
      List.drop_take, List.take_take]
    congr 1
    omega
  have ht : (z.take r.1 ++ selectorPoint (r.2.1 >>> r.1) (nu - r.1)).take τ = z.take τ := by
    rw [List.take_append_of_le_length (by rw [hl]; omega), List.take_take]
    congr 1
    omega
  rw [hd, ht]
  have hsplit : (z.drop τ).take (r.1 - τ) = (z.drop τ).take (linK2 - τ) ++ (z.drop linK2).take (r.1 - linK2) := by
    rw [show r.1 - τ = (linK2 - τ) + (r.1 - linK2) by omega, List.take_add, List.drop_drop,
      show τ + (linK2 - τ) = linK2 by omega]
  rw [hsplit, show r.1 - τ = (linK2 - τ) + (r.1 - linK2) by omega,
    eqEval_sel_append _ _ _ _ _ (by simp; omega), ← Nat.shiftRight_add, ← Nat.shiftRight_add,
    show τ + (linK2 - τ) = linK2 by omega, show linK1 + (linK2 - linK1) = linK2 by omega]
  have hin : (∀ i < nu - r.1, (off >>> r.1).testBit i = (r.2.1 >>> r.1).testBit i) ↔
      inRegionHi nu r (off >>> linK1) = true := by
    unfold inRegionHi
    rw [← Nat.shiftRight_add, show linK1 + (r.1 - linK1) = r.1 by omega, beq_iff_eq, mod_eq_iff_testBit]
  by_cases hI : inRegionHi nu r (off >>> linK1) = true
  · rw [if_pos (hin.mpr hI), if_pos hI]
    ring
  · rw [if_neg (fun h => hI (hin.mp h)), if_neg hI]
    ring

/-- **Small shape, per column**: the fast form with the regions' factor is the regions' sum. -/
theorem small_hwd (nu : Nat) (ζ x : List FE) (RE : List ((Nat × Nat × Nat) × FE))
    (hRE : ∀ d ∈ RE, d.1 ∈ TypedV.regionsN nu) (hnu : 21 ≤ nu) (τ off : Nat) (hτ : τ ≤ linK1) :
    eqEval (selectorPoint (off >>> τ) (linK2 - τ)) (((x.tail ++ List.replicate (nu - 1) 0).drop τ).take (linK2 - τ)) *
      eqEval (ζ.take τ) ((x.tail ++ List.replicate (nu - 1) 0).take τ) *
      regG nu (x.tail ++ List.replicate (nu - 1) 0) RE (off >>> linK1) =
    (RE.map fun d => d.2 * gR nu ζ x d.1 τ off).sum := by
  induction RE with
  | nil => simp [regG]
  | cons d RE ih =>
    have hr := hRE d List.mem_cons_self
    have ih' := ih fun d' h' => hRE d' (List.mem_cons_of_mem _ h')
    simp only [regG, List.map_cons, List.sum_cons] at ih' ⊢
    rw [← ih', gR_fast nu ζ x d.1 (by rcases regionsN_fst hr with h | h <;> rw [h] <;> omega)
      (by rcases regionsN_fst hr with h | h <;> rw [h] <;> decide) τ off hτ]
    split <;> ring

/-- Two list sums commute. -/
theorem sum_comm' {α β : Type} (rs : List α) (qs : List β) (f : α → β → FE) :
    (rs.map fun r => (qs.map (f r)).sum).sum = (qs.map fun q => (rs.map fun r => f r q).sum).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

/-- Two sums swapped. -/
theorem sum_swap {α β : Type} (rs : List α) (qs : List β) (e : α → FE) (c : β → FE) (g : α → β → FE) :
    (rs.map fun r => e r * (qs.map fun q => c q * g r q).sum).sum =
      (qs.map fun q => c q * (rs.map fun r => e r * g r q).sum).sum := by
  have h1 : ∀ r, e r * (qs.map fun q => c q * g r q).sum = (qs.map fun q => c q * (e r * g r q)).sum := fun r => by
    rw [← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left fun q _ => by ring)
  rw [List.map_congr_left fun r _ => h1 r, sum_comm']
  exact congrArg List.sum (List.map_congr_left fun q _ => by rw [List.sum_map_mul_left])

end WFS

section WFM

open Lvm.Shape (length_selectorPointF)

theorem toStk_weight (s : Bool) (nu : Nat) (ζ : List FE) (cs : List (FE × Nat × Nat)) (v : FE) :
    (toStk s nu (sumClaim nu (partsOf ζ cs) v, 0)).1 = (toStk s nu (sumClaim nu (partsOf ζ cs) 0, 0)).1 := by
  cases s <;> rfl

theorem linClaims_weights (s : Bool) (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (vs x : List FE) :
    (linClaims nu ζ css vs).map (fun e => (toStk s nu e.2).1 x) =
      css.map fun cs => (toStk s nu (sumClaim nu (partsOf ζ cs) 0, 0)).1 x := by
  unfold linClaims
  rw [List.map_map]
  have hz : ∀ (l : List (List (FE × Nat × Nat))) (n : Nat), (l.zipIdx n).map Prod.fst = l := by
    intro l
    induction l with
    | nil => intro n; rfl
    | cons a l ih => intro n; simp [List.zipIdx_cons, ih]
  conv_rhs => rw [← hz css 0, List.map_map]
  refine List.map_congr_left fun ck _ => ?_
  simp only [Function.comp_apply]
  rw [toStk_weight]

/-- **MBL `mbWF_eq`, the region case**: one side's small-shape weight. -/
theorem linWS_small (nu : Nat) (hnu : 21 ≤ nu) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (x : List FE)
    (cs : List (FE × Nat × Nat)) :
    (1 - x.headD 0) * sideF (wTabs ζ (x.tail ++ List.replicate (nu - 1) 0) linK2 (lowTs css)) linK2
      (fun τ off => ((regE nu x).map fun d => d.2 * gR nu ζ x d.1 τ off).sum)
      (regG nu (x.tail ++ List.replicate (nu - 1) 0) (regE nu x)) cs =
      (toStk true nu (sumClaim nu (partsOf ζ cs) 0, 0)).1 x := by
  have e2 : linK2 = 18 := rfl
  have hRS : ∀ r ∈ (TypedV.regionsN nu).filter (Shape.meets ⟨nu, 0⟩), r ∈ TypedV.regionsN nu :=
    fun r h => (List.mem_filter.mp h).1
  have hRE : ∀ d ∈ regE nu x, d.1 ∈ TypedV.regionsN nu := fun d hd => by
    unfold regE at hd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
    exact (List.mem_filter.mp hr).1
  rw [sideF_wd _ _ _ _ _ _ (by simp; omega) (fun τ off hτ _ => small_hwd nu ζ x _ hRE hnu τ off hτ)]
  simp only [toStk, ↓reduceIte, TypedV.onStackZBN, BlockClaim.onStack]
  congr 1
  rw [show (sumClaim nu (partsOf ζ cs) (0 : FE)).block = ⟨nu, 0⟩ from rfl]
  have hw : ∀ r ∈ (TypedV.regionsN nu).filter (Shape.meets ⟨nu, 0⟩),
      (⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * ((⟨nu, 0⟩ : Placement).eqAbove (TypedV.relocN nu x r) *
        (sumClaim nu (partsOf ζ cs) 0).weight ((TypedV.relocN nu x r).take nu)) =
      ((⟨r.1, r.2.2⟩ : Placement).eqAbove x.tail * (⟨nu, 0⟩ : Placement).eqAbove (TypedV.relocN nu x r)) *
        (cs.map fun q => q.1 * gR nu ζ x r q.2.1 q.2.2).sum := fun r hrm => by
    have hr : r.1 + 1 ≤ nu := by
      rcases regionsN_fst (hRS r hrm) with h | h <;> rw [h] <;> omega
    have hlen : (TypedV.relocN nu x r).length = nu := by
      rw [relocN_eq, List.length_append, length_reloc_take nu x r hr, length_selectorPointF]; omega
    rw [List.take_of_length_le hlen.le, sumClaim_weight, mul_assoc]
    rfl
  rw [List.map_congr_left hw, sum_swap]
  unfold regE
  simp only [List.map_map]
  rfl

end WFM


/-- **MBL day-0 item 6 `mbWF_eq`** (owner V): V_S's run weights are the claims' stack weights, both shapes. -/
theorem linWS_eq (s : Bool) (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (vs : List FE)
    (x : List FE) : linWS s nu ζ css x = (linClaims nu ζ css vs).map fun e => (toStk s nu e.2).1 x := by
  rw [linClaims_weights]
  unfold linWS
  split
  · rename_i h
    obtain ⟨hs, hnu⟩ := h
    subst hs
    exact List.map_congr_left fun cs _ => linWS_small nu hnu ζ css x cs
  · split
    · rename_i h
      obtain ⟨hs, hx⟩ := h
      subst hs
      exact linWS_big nu ζ css x hx
    · rfl

/-- The claims as one opening group. -/
def linGroup (s : Bool) (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (vs : List FE) : SGroup :=
  ⟨(linClaims nu ζ css vs).map fun e => toStk s nu e.2, linWS s nu ζ css, fun x => by
    rw [linWS_eq s nu ζ css vs x, List.map_map]; rfl⟩

/-! ## The opening and the decision -/

/-- **`dOpenFFI` with the three claims** between the typed items and the front's. -/
def dOpenFFL (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × Nat × Nat))) (vs : List FE) (items : List FItem) : DM Unit := do
  require (((ti ++ items).flatMap FItem.flat).all (·.1 == .main))
  verifyStackedOpeningG p.mainLevels p.nuMain
    (SGroup.one (pin.weight, pin.value) :: (ti.flatMap (FItem.groups s p.nuMain) ++ linGroup s p.nuMain ζ css vs ::
      items.flatMap (FItem.groups s p.nuMain)))
    false p.grind p.mainOod

/-- **The typed phases at S2GL** (`dTypedTG` with `dMiniL`): the accumulator, the typed items, `ζ`, the bus. -/
def dTypedLG {α : Type} (p : Params) (N : TNatT) (m : M3) (pub : Pub)
    (mk : List FE2 → List FE2 → List FE2 → FE2 → α) : DM (Acc × α × List FE × BusOut) := do
  let z ← dZeroT
  let w ← dWiringT N pub z.2
  let r ← dRelayT2 N w.1 (w.2.2.getD 1 0)
  let acc ← dAccT pub (z.1 ++ w.1) w.2.1
  let mb ← dMiniL p m pub
  pure (acc, mk w.1 w.2.2 r.1 r.2, mb.1, mb.2)

/-- The tape's sponge intervals with `B` sponge blocks (R1's `contIvB (B - 1)`; `contIvU = contIvOf 3961`). -/
def contIvOf (B : Nat) : List (Nat × Nat) := contIvB (B - 1)

/-- S2GL's intervals are R1's `contIvB 3842` (`midGL`'s `tapeProgB bL`). -/
theorem contIvOf_L : contIvOf 3843 = contIvB 3842 := rfl

/-- **`wireUDG` with the sponge intervals `iv`.** -/
def wireUDGc {ρ : Type} (iv : List (Nat × Nat)) (rs : List FE2 → List FE2 → DM ρ) (p : Params) (s : List FK) (n : Nat)
    (claim : E2V.KClaim FE2) : DM (WireU ρ) := do
  let sc ← sumcheckD gC2 (wireTargetDF (sBitsD s) n claim) 3 (List.replicate p.logN none)
  let g ← readE2s 3
  let L := layout0 p
  let σ' := sc.1.take p.ksLog
  let base := 2 ^ p.logN
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF p.ksLog p.logN sc.1 * (kksF iv claim.point claim.mu σ' base * g.getD 1 0 +
      ikEvalP claim.point claim.mu σ' base * g.getD 2 0))
  let d ← slotDFG rs 2 (dSelBits p) (dSel p) (dWA claim.weights.toArray) sc.1 (g.getD 0 0)
  let y ← slotDFW rs slotBitsU (p.nuMain - (p.ksLog + slotBitsU)) (L.ks / 2 ^ (p.ksLog + slotBitsU))
    (lanesW slotBitsU 25 claim.weights.toArray) σ' (g.getD 1 0)
  let m ← slotDFW rs slotBitsU (p.nuMain - p.nuRec) (L.s / 2 ^ p.nuRec) (lanesW slotBitsU 17 claim.weights.toArray)
    (σ' ++ [0]) (g.getD 2 0)
  pure ⟨sc, g, d, y, m⟩

/-- **`tapeUDG` with the sponge intervals `iv`.** -/
def tapeUDGc {ρ : Type} (iv : List (Nat × Nat)) (rs : List FE2 → List FE2 → DM ρ) (p : Params) (s : List FK)
    (n : Nat) : DM (TapeU ρ) := do
  sepE2
  let r ← samplesG gC1 p.logN
  let ab ← readE2s (2 * 25)
  let rw ← sampleG gC1
  let claim ← tapeGkrDF (p.logN + 1) (r ++ [rw]) (t1ValsF p.logN p.ksLog (r ++ [rw]) ab)
  require (decide (1 ≤ n ∧ n ≤ 2 ^ p.logN))
  let wo ← wireUDGc iv rs p s n claim
  pure ⟨r, rw, ab, claim, wo⟩

theorem wireUDGc_U {ρ : Type} : @wireUDGc ρ contIvU = wireUDG := rfl

theorem tapeUDGc_U {ρ : Type} : @tapeUDGc ρ contIvU = tapeUDG := rfl

/-- **The decision program at S2GL** (`decideProgUG` with the bus phase `dMiniL` and the three claims; the tape's
sponge intervals `contIvOf B`). -/
def decideProgLG (p pT : Params) (B : Nat) (N : TNatT) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubG vk c sig
  let m := m3G N p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, ti, ζ, bus) ← dTypedLG pT N m pub (typedItemsND N p)
  let tabs := M3.sumcheckTabs N.mbT
  let tp ← tapeUDGc (contIvOf B) rowSwitchDR p pub.s pub.n
  dOpenFFL p (TypedV.smallT p pub) pin ti ζ ((List.range 3).map (M3.mbColsN tabs bus))
    (M3.mbValsF tabs bus ζ) (frontItemsU rowAccR p pub tp)
  pure acc

/-- **V_S's decision at S2GL** at `p` (`decideFUG`'s form). -/
def decideFLG (p pT : Params) (B : Nat) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := DM.runOnH (headerBytesP p) (decideProgLG p pT B N vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phiT (a.pt.map Lvm.e2OfFE) == Lvm.e2OfFE a.y

end Lvm.E2L
