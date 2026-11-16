-- new for lvm (AC-S, BLUEPRINT §12.6 `accSpec`): phase 3b of the lvm instance from the table seam
-- (WP-2's `TablePost`, with `AccOk acc_in` carried in the candidates) to WP-9b's `TablePostC`; then
-- with the bus and table phases (WP-9b's `lbusTableSpec`), as WP-9b's `lbusTableCheckSpec` composes
-- them with `tableCheckSpec` (`LvmM3Mid`). The good-branch lemma follows WP-9b's `derived_holds`.
import LvmM3Mid
import LvmAccSpec
import LvmDecide
import LvmDecideM3Real
import LvmM3FidFix
import LvmQLinkArith
import LvmM3FidFixC
import LvmM3FidNative

-- ===== merged from `LvmAccSpecPhi` (GOLF module merge: `LvmAccSpecPhi.lean` is now a stub importing `LvmAccSpecT`) =====
section
-- new for lvm (AC-S, BLUEPRINT §12.2): `Φ` as a multilinear extension. Built on WP-10's `Loop.mle`
-- rules (`mle_split`, `mle_congr`, `mle_const`, `mle_eq_sum`), WP-9b's `toExt3_mle_fixed` and
-- `FixOk`, QL's `eqKernel_getD` (`LvmQLinkArith`) and AC-V's `fixColsR`/`PhiC` (`LvmDecide*`).

/-!
# `Φ` is a multilinear polynomial in `D = τ* + dk` variables

BLUEPRINT §12.2: `Φ(x, k) = F_k(x mod 2^{τ_k})` for `k < nFix`, `0` otherwise, on `{0,1}^D`
(`x` the low `τ*` bits). Its extension is `Φ̃(p, κ) = Σ_k eq(κ, k)·F̃_k(p.take τ_k)`, which is how
AC-V's native `PhiC` computes it (one sweep of the closed forms, then a dot product with
`eqKernel κ`).

* `PhiF cs τs pt`: that evaluator over any column list (`PhiC P (M3.real P tabs) pub = PhiF
  (fixColsR …) P.tableRounds`, `phiC_real`); `phiCells`: `Φ`'s cells;
* **`phiF_eq_mle`**: when every closed form is its cells' extension and `nFix ≤ 2^dk`, `PhiF` is
  `Loop.mle` of `Φ`'s cells; **`phiE_eq_eval₂Mle`**: over `E` it is `eval₂Mle` of `Φ`'s fixed
  column (CompPoly);
* **`phiC_eq_eval₂Mle`** (BLUEPRINT §12.6 "`PhiC = eval₂Mle Φ`"): the native `PhiC` of the real
  instance, from WP-9b's `FixOk` of the sumcheck tables;
* **`lineDeg_phiE`**: `Φ̃ ∘ line` has degree at most `D` (`lineDeg_mle`).
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval Finset
open Lvm.Loop (mle eqW)
open Lvm.M3 (FixCol fixColsR fixValsR sumcheckTabs Tab ColSrc FixOk fixedColumn)
open LeanVM.Protocol.EndToEnd.Front (vecOf)
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons eqKernel_length eqKernel_getD)

/-! ## Sums of lists -/

theorem foldl_add_sum (l : List FE) (a : FE) : l.foldl (· + ·) a = a + l.sum := Lvm.M3.foldl_add_acc l a

/-- `dot` of a long list with a short one: the sum over the short one. -/
theorem dot_eq_sum_fe : ∀ (l r : List FE), r.length ≤ l.length →
    Lvm.dot l r = ∑ j ∈ range r.length, l.getD j 0 * r.getD j 0
  | _, [], _ => by simp [Lvm.dot]
  | [], _ :: _, h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_eq_sum_fe l r (by simpa using h)
    simp only [Lvm.dot, List.zipWith_cons_cons, List.foldl_cons, zero_add, foldl_add_sum] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- **`dot (eqKernel κ) v`** is the `eq(κ, ·)`-weighted sum of `v`. -/
theorem dot_eqKernel_fe (κ v : List FE) (hv : v.length ≤ 2 ^ κ.length) :
    Lvm.dot (Lvm.eqKernel κ) v = ∑ j ∈ range v.length, eqW κ j * v.getD j 0 := by
  rw [dot_eq_sum_fe _ _ (by rw [Lvm.Q1.eqKernel_length_lk]; exact hv)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Lvm.Q1.eqKernel_getD κ (lt_of_lt_of_le (mem_range.mp hj) hv)]

/-! ## `Φ` over a column list -/

/-- **`Φ̃` over a column list** (AC-V's `PhiC`): the closed forms at `p.take τ_k`, `p` the first
`τs` coordinates, dotted with `eq(κ, ·)`, `κ` the rest. -/
def PhiF (cs : List FixCol) (τs : ℕ) (pt : List FE) : FE :=
  Lvm.dot (Lvm.eqKernel (pt.drop τs)) (cs.map fun c ↦ c.ev ((pt.take τs).take c.τ))

/-- **`Φ`'s cells**: cell `x + 2^τs·k` is column `k`'s cell `x mod 2^{τ_k}`, `0` past the columns. -/
def phiCells (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs : ℕ) (n : ℕ) : FK :=
  match cs[n / 2 ^ τs]? with
  | some c => cell c ((n % 2 ^ τs) % 2 ^ c.τ)
  | none => 0

/-- A column read modulo `2^τ` has the extension of its first `2^τ` cells at the first `τ`
coordinates. -/
theorem mle_mod (r : List FE) {τ : ℕ} (hτ : τ ≤ r.length) (u : ℕ → FE) :
    mle r (fun x ↦ u (x % 2 ^ τ)) = mle (r.take τ) u := by
  have ht : (r.take τ).length = τ := by simp; omega
  conv_lhs => rw [← List.take_append_drop τ r]
  rw [Lvm.Loop.mle_split, ht]
  rw [Lvm.Loop.mle_congr (r.drop τ) (w := fun _ ↦ mle (r.take τ) u) fun y _ ↦
    Lvm.Loop.mle_congr _ fun x hx ↦ by
      rw [ht] at hx
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]]
  exact Lvm.Loop.mle_const _ _

/-- **`Φ̃` is the multilinear extension of `Φ`'s cells**, when every closed form is its cells'
extension at its height (`hev`, WP-9b's `FixOk`), every height is at most `τs`, and the columns
fit `2^dk`. -/
theorem phiF_eq_mle (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (pt : List FE) (hpt : pt.length = τs + dk) :
    PhiF cs τs pt = mle pt fun n ↦ FE.ofK (phiCells cs cell τs n) := by
  have hp : (pt.take τs).length = τs := by simp; omega
  have hk : (pt.drop τs).length = dk := by simp; omega
  conv_rhs => rw [← List.take_append_drop τs pt]
  rw [Lvm.Loop.mle_split, hp, PhiF, dot_eqKernel_fe _ _ (by simpa [hk] using hn)]
  rw [Lvm.Loop.mle_congr (pt.drop τs) (w := fun y ↦ if h : y < cs.length then
      (cs[y]'h).ev ((pt.take τs).take (cs[y]'h).τ) else 0) fun y hy ↦ ?_,
    Lvm.Loop.mle_eq_sum, hk]
  · rw [← Finset.sum_range_add_sum_Ico _ (show cs.length ≤ 2 ^ dk from hn)]
    rw [Finset.sum_eq_zero (s := Ico cs.length (2 ^ dk)) fun y hy ↦ by
      rw [dif_neg (by have := (mem_Ico.mp hy).1; omega), mul_zero], add_zero, List.length_map]
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    have hy' := mem_range.mp hy
    rw [dif_pos hy', List.getD_eq_getElem _ _ (by simpa using hy'), List.getElem_map]
  · have hdiv : ∀ x < 2 ^ τs, (x + 2 ^ τs * y) / 2 ^ τs = y := fun x hx ↦ by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
    have hmod : ∀ x < 2 ^ τs, (x + 2 ^ τs * y) % 2 ^ τs = x := fun x hx ↦ by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    split_ifs with hyc
    · have hc := List.getElem_mem hyc
      rw [Lvm.Loop.mle_congr (pt.take τs) (w := fun x ↦ FE.ofK (cell cs[y] (x % 2 ^ cs[y].τ)))
        fun x hx ↦ by
          rw [hp] at hx
          simp only [phiCells, hdiv x hx, hmod x hx, List.getElem?_eq_getElem hyc]]
      have hm := mle_mod (pt.take τs) (τ := cs[y].τ) (by rw [hp]; exact hτ _ hc)
        (fun x ↦ FE.ofK (cell cs[y] x))
      rw [hm, hev _ hc _ (by simp; have := hτ _ hc; omega)]
    · rw [Lvm.Loop.mle_congr (pt.take τs) (w := fun _ ↦ 0) fun x hx ↦ by
          rw [hp] at hx
          simp only [phiCells, hdiv x hx, List.getElem?_eq_none (show cs.length ≤ y by omega),
            Lvm.M3.ofK_zero']]
      exact Lvm.Loop.mle_const _ _

/-- `Φ`'s fixed column on `D = τs + dk` variables. -/
def phiCol (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ) : Column (τs + dk) :=
  fixedColumn (τs + dk) (phiCells cs cell τs)

/-- `Φ̃` read over `E` (the DSL's evaluator: the native one through `FE.toExt3`). -/
def phiE (cs : List FixCol) (τs : ℕ) (pt : List E) : E :=
  FE.toExt3 (PhiF cs τs (pt.map FE.ofExt3))

/-- **`Φ̃` over `E` is `eval₂Mle` of `Φ`'s column** (CompPoly's multilinear extension). -/
theorem phiE_eq_eval₂Mle (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (pt : List E) (hpt : pt.length = τs + dk) :
    phiE cs τs pt = eval₂Mle (phiCol cs cell τs dk).values (algebraMap K E) (vecOf (τs + dk) pt) := by
  rw [phiE, phiF_eq_mle cs cell τs dk hτ hev hn _ (by simpa using hpt), phiCol,
    ← Lvm.M3.toExt3_mle_fixed, LeanVM.Protocol.EndToEnd.Front.toList_vecOf _ hpt]

/-- **`Φ̃ ∘ line` has degree at most `D`** (BLUEPRINT §12.6, the `t` step's `D/|E|`). -/
theorem lineDeg_phiE (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (a b : List E) (ha : a.length = τs + dk) (hb : b.length = τs + dk) :
    ∃ g : Polynomial E, g.natDegree ≤ τs + dk ∧ ∀ t, g.eval t = phiE cs τs (line a b t) := by
  obtain ⟨g, hg, hgv⟩ := lineDeg_mle (phiCol cs cell τs dk) a b ha hb
  refine ⟨g, hg, fun t ↦ ?_⟩
  rw [hgv, phiE_eq_eval₂Mle cs cell τs dk hτ hev hn _ (by rw [length_line, ha, hb, min_self])]

/-! ## The real instance: `PhiC = eval₂Mle Φ` -/

/-- A fixed column's cells, read off the tables (`0` if the column is not fixed). -/
def cellOf (T : List Tab) (c : FixCol) : ℕ → FK :=
  match T[c.tab]?.bind fun t ↦ t.cols[c.col]? with
  | some (.fix f _) => f
  | _ => fun _ ↦ 0

/-- Every column of `fixCols` is a fixed column of its table, with the table's height and the
column's closed form. -/
theorem mem_fixColsR {T : List Tab} {pubTab : ℕ} {c : FixCol} (hc : c ∈ fixColsR T pubTab) :
    ∃ t ∈ T, t.τ = c.τ ∧ ColSrc.fix (cellOf T c) c.ev ∈ t.cols := by
  unfold fixColsR at hc
  obtain ⟨⟨t, j⟩, htj, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨src, i⟩, hsi, hc⟩ := List.mem_filterMap.mp hc
  have ht : T[j]? = some t := List.mem_zipIdx_iff_getElem?.mp htj
  have hs : t.cols[i]? = some src := List.mem_zipIdx_iff_getElem?.mp hsi
  cases src with
  | com _ _ => simp at hc
  | fix f e =>
    simp only at hc
    split_ifs at hc
    obtain rfl := Option.some.inj hc
    refine ⟨t, List.mem_of_getElem? ht, rfl, ?_⟩
    have hcell : cellOf T ⟨j, t.τ, i, e⟩ = f := by simp [cellOf, ht, hs]
    rw [hcell]
    exact List.mem_of_getElem? hs

/-- `FixOk` of the tables gives every column of `fixCols` its cells' extension. -/
theorem fixCols_ev {T : List Tab} (pubTab : ℕ) (hfix : FixOk T) :
    ∀ c ∈ fixColsR T pubTab, ∀ r : List FE, r.length = c.τ →
      c.ev r = mle r fun x ↦ FE.ofK (cellOf T c x) := by
  intro c hc r hr
  obtain ⟨t, ht, hτ, hm⟩ := mem_fixColsR hc
  exact hfix t ht _ _ hm r (hτ ▸ hr)

theorem fixCols_τ {T : List Tab} (pubTab τs : ℕ) (hτ : ∀ t ∈ T, t.τ ≤ τs) :
    ∀ c ∈ fixColsR T pubTab, c.τ ≤ τs := by
  intro c hc
  obtain ⟨t, ht, he, -⟩ := mem_fixColsR hc
  exact he ▸ hτ t ht

/-- The native `PhiC` of the real instance is `PhiF` of its `fixCols`. -/
theorem phiC_real (P : Params) (tabs : Pub → List Tab) (pub : Pub) (pt : List FE) :
    PhiC P (M3.real P tabs) pub pt = PhiF (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) P.tableRounds pt :=
  rfl

/-- **`PhiC = eval₂Mle Φ`** (BLUEPRINT §12.6) for the real instance: from WP-9b's `FixOk` of the
sumcheck tables, their heights at most `tableRounds`, and `nFix ≤ 2^accLog`, at a point of
`tableRounds + accLog` coordinates (`= accVars` under `fitsR`). -/
theorem phiC_eq_eval₂Mle (P : Params) (tabs : Pub → List Tab) (pub : Pub)
    (hfix : FixOk (sumcheckTabs (tabs pub)))
    (hτ : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ P.tableRounds)
    (hn : (fixColsR (sumcheckTabs (tabs pub)) P.pubTab).length ≤ 2 ^ P.accLog)
    (pt : List E) (hpt : pt.length = P.tableRounds + P.accLog) :
    FE.toExt3 (PhiC P (M3.real P tabs) pub (pt.map FE.ofExt3)) =
      eval₂Mle (phiCol (fixColsR (sumcheckTabs (tabs pub)) P.pubTab)
        (cellOf (sumcheckTabs (tabs pub))) P.tableRounds P.accLog).values (algebraMap K E)
        (vecOf _ pt) :=
  phiE_eq_eval₂Mle _ _ _ _ (fixCols_τ _ _ hτ) (fixCols_ev _ hfix) hn pt hpt

/-! ## The instance's `AccHyp`: the fold identity -/

/-- `dot` of a long list with a short one over `E`. -/
theorem dot_eq_sum_e : ∀ (l r : List E), r.length ≤ l.length →
    Verifier.dot l r = ∑ j ∈ range r.length, l.getD j 0 * r.getD j 0
  | _, [], _ => by simp [Verifier.dot]
  | [], _ :: _, h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_eq_sum_e l r (by simpa using h)
    have hf : ∀ (m : List E) (a : E), m.foldl (· + ·) a = a + m.sum := fun m ↦ by
      induction m with
      | nil => intro a; simp
      | cons z m ihm => intro a; rw [List.foldl_cons, ihm, List.sum_cons]; ring
    simp only [Verifier.dot, List.zipWith_cons_cons, zero_add, hf, List.sum_cons] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- **`dot (eqKernel κ) v` over `E`** is the `eq(κ, ·)`-weighted sum of `v`. -/
theorem dot_eqKernel_e (κ v : List E) (hv : v.length ≤ 2 ^ κ.length) :
    Verifier.dot (Verifier.eqKernel κ) v = ∑ j ∈ range v.length, eqAt κ j * v.getD j 0 := by
  rw [dot_eq_sum_e _ _ (by rw [eqKernel_length]; exact hv)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eqKernel_getD, if_pos (lt_of_lt_of_le (mem_range.mp hj) hv)]

theorem toExt3_sum (s : Finset ℕ) (f : ℕ → FE) :
    FE.toExt3 (∑ k ∈ s, f k) = ∑ k ∈ s, FE.toExt3 (f k) :=
  map_sum FE.ringEquivExt3 f s

/-- The native equality weight read over `E`. -/
theorem toExt3_eqW : ∀ (l : List E) (w : ℕ), FE.toExt3 (eqW (l.map FE.ofExt3) w) = eqAt l w
  | [], _ => by simp [eqW]
  | r :: l, w => by
    simp only [List.map_cons, eqW, eqAt_cons, FE.toExt3_mul, toExt3_eqW l]
    split_ifs
    · simp
    · rw [FE.toExt3_sub, FE.toExt3_one, FE.toExt3_ofExt3, CharTwo.sub_eq_add]

/-- The fixed claims' errors: claim value minus closed form at the table point, `0` past the
columns. -/
def deltaOf (cs : List FixCol) (vs r : List E) (w : ℕ) : E :=
  if h : w < cs.length then
    vs.getD w 0 - FE.toExt3 ((cs[w]'h).ev ((r.map FE.ofExt3).take (cs[w]'h).τ))
  else 0

/-- **The instance's `AccHyp`**: `Φ = phiE cs τs` (the native `PhiC`), `y_own = dot (eqKernel κ) vs`
(the sent evaluations of `fixCols`), `b(κ) = r ++ κ` with `|r| = τs`, `|a| = D = τs + dk`. -/
theorem accHyp_phi (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (a r vs : List E) (ha : a.length = τs + dk) (hr : r.length = τs)
    (hvs : vs.length = cs.length) :
    AccHyp dk (τs + dk) a (fun κ ↦ Verifier.dot (Verifier.eqKernel κ) vs) (fun κ ↦ r ++ κ)
      (phiE cs τs) (deltaOf cs vs r) where
  line_deg κ hκ := lineDeg_phiE cs cell τs dk hτ hev hn a _ ha (by simp [hr, hκ])
  at0 κ hκ := line_zero _ _ (by simp [ha, hr, hκ])
  at1 κ hκ := line_one _ _ (by simp [ha, hr, hκ])
  fold κ hκ := by
    have hl : ((r ++ κ).map FE.ofExt3).take τs = r.map FE.ofExt3 := by
      rw [List.map_append, List.take_append_of_le_length (by simp [hr]), List.take_of_length_le
        (by simp [hr])]
    have hd : ((r ++ κ).map FE.ofExt3).drop τs = κ.map FE.ofExt3 := by
      rw [List.map_append, List.drop_append_of_le_length (by simp [hr]), List.drop_of_length_le
        (by simp [hr]), List.nil_append]
    rw [phiE, PhiF, hl, hd, dot_eqKernel_fe _ _ (by simpa [hκ] using hn), toExt3_sum,
      dot_eqKernel_e _ _ (by rw [hvs, hκ]; exact hn), List.length_map, hvs, ← Finset.sum_sub_distrib,
      ← Finset.sum_range_add_sum_Ico _ hn,
      Finset.sum_eq_zero (s := Ico cs.length (2 ^ dk)) fun w hw ↦ by
        rw [deltaOf, dif_neg (by have := (mem_Ico.mp hw).1; omega), mul_zero], add_zero]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := mem_range.mp hw
    rw [FE.toExt3_mul, toExt3_eqW, deltaOf, dif_pos hw', mul_sub,
      List.getD_eq_getElem (cs.map _) _ (by simpa using hw'), List.getElem_map]

end Lvm.Acc
end
-- ===== end of `LvmAccSpecPhi` =====

-- ===== merged from `LvmAccSpecRet` (GOLF module merge: `LvmAccSpecRet.lean` is now a stub importing `LvmAccSpecT`) =====
section
-- new for lvm (AC-S): what the table phase returns, for phase 3b's claim lookups. Adapted from
-- WP-16b's `retOK_tableTermsClaims`/`retOK_tableSumcheckClaims` (lvm/CERT `LvmCertSMid3Tab`), with
-- the sumcheck point kept and the columns' order tracked; WP-9b's `base_eq` (`LvmM3FidFixC`).

/-!
# The table phase's claims: one per column, in column order, at prefixes of one point

Phase 3b (AC-N's DSL instance in `midS`) reads a fixed column's sent evaluation as the first claim
on its global column (`find?`) and the table point as the longest claim point. Both read the
claims the table sumcheck returned; **`retOK_lvmBusTableProg`**: every return `cl` of WP-9b's
`lvmBusTableProg` on tables `T` has

* strictly increasing columns (`Pairwise (· < ·)`), so a column has at most one claim;
* every claim on global column `base_j + i` (`i < w_j`) at `pt.take τ_j`, for one point `pt` of
  `max τ` coordinates;
* a claim at `pt` itself when some table of maximal height has a column.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open Lvm.M3 (Tab vTable vTables vLayout busResV lvmBusTableProg)

/-- Table `k`'s first global column, continued past the last table. -/
def bnd (T : List Tab) (k : ℕ) : ℕ := globalColumnCount + ((T.map (·.w)).take k).sum

theorem bnd_succ (T : List Tab) {k : ℕ} (hk : k < T.length) :
    bnd T (k + 1) = bnd T k + T[k].w := by
  rw [bnd, bnd, List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]; ring

theorem base_bnd (T : List Tab) {k : ℕ} (hk : k < T.length) :
    (globalColumnBases (vTables T)).getD k 0 = bnd T k := Lvm.M3.base_eq T hk

/-- A claim of table `j`'s column `i` at `pt.take τ_j`. -/
def ClaimOf (T : List Tab) (pt : List E) (c : ColumnClaim) : Prop :=
  ∃ j i, ∃ hj : j < T.length, i < T[j].w ∧ c.column = bnd T j + i ∧ c.point = pt.take T[j].τ

/-- **The shape of the table phase's claims.** -/
def ClaimShape (T : List Tab) (cl : List ColumnClaim) : Prop :=
  (cl.map (·.column)).Pairwise (· < ·) ∧
    ∃ pt : List E, pt.length = (T.map (·.τ)).foldl max 0 ∧ (∀ c ∈ cl, ClaimOf T pt c) ∧
      ((∃ t ∈ T, t.τ = (T.map (·.τ)).foldl max 0 ∧ 0 < t.w) → ∃ c ∈ cl, c.point = pt)

/-- The rows of the table loop from table `k` on. -/
def RowsFrom (T : List Tab) (k : ℕ) (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) : Prop :=
  ∀ m (hm : m < rows.length), ∃ hk : k + m < T.length,
    rows[m].1 = vTable (k + m) T[k + m] ∧ rows[m].2.1 = T[k + m].τ

theorem rowsFrom_tail {T : List Tab} {k : ℕ} {r : Verifier.Table × ℕ × List Verifier.Form × E}
    {rows : List (Verifier.Table × ℕ × List Verifier.Form × E)} (h : RowsFrom T k (r :: rows)) :
    RowsFrom T (k + 1) rows := fun m hm ↦ by
  obtain ⟨hk, h1, h2⟩ := h (m + 1) (by simp; omega)
  exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 m] using h1,
    by simpa [Nat.add_assoc, Nat.add_comm 1 m] using h2⟩

/-- New claims of one row: columns `base + i`, increasing. -/
theorem pairwise_newCols (base : ℕ) (evs : List E) (pt : List E) (h : ℕ) :
    ((evs.zipIdx.map fun (x : E × ℕ) ↦ (⟨base + x.2, pt.take h, x.1⟩ : ColumnClaim)).map
      (·.column)).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map, List.length_zipIdx] at hi hj
  simp [List.getElem_map, List.getElem_zipIdx]
  omega

open LeanVM.Protocol.Compile in
/-- **The table loop's returns** (adapted from WP-16b's `retOK_tableTermsClaims`). -/
theorem retOK_terms (T : List Tab) (cp fp pt : List E) (F : Prop) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (k cursor : ℕ) (final : E)
      (claims : List ColumnClaim), RowsFrom T k rows →
      (claims.map (·.column)).Pairwise (· < ·) → (∀ c ∈ claims, c.column < bnd T k ∧ ClaimOf T pt c) →
      (F → (∃ c ∈ claims, c.point = pt) ∨ ∃ m, ∃ hm : m < rows.length, pt.length ≤ rows[m].2.1 ∧
        0 < rows[m].1.width) →
      RetOK (fun x : E × List ColumnClaim ↦ (x.2.map (·.column)).Pairwise (· < ·) ∧
          (∀ c ∈ x.2, ClaimOf T pt c) ∧ (F → ∃ c ∈ x.2, c.point = pt))
        (tableTermsClaims (vTables T) cp fp pt rows cursor final claims)
  | [], _, _, _, claims, _, hp, hc, hf => RetOK.ret ⟨hp, fun c h ↦ (hc c h).2, fun hF ↦ by
      rcases hf hF with hf | ⟨m, hm, -⟩
      · exact hf
      · simp at hm⟩
  | r :: rows, k, cursor, final, claims, hr, hp, hc, hf => by
    obtain ⟨hk, hr1, hr2⟩ := hr 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hk hr1 hr2
    unfold tableTermsClaims
    refine (RetOK.readN r.1.width).bind fun evs hevs ↦ ?_
    have hw : r.1.width = T[k].w := by rw [hr1]; simp [vTable, Table.width]
    have hop : r.1.opcode = k := by rw [hr1]; rfl
    refine retOK_terms T cp fp pt F rows (k + 1) _ _ _ (rowsFrom_tail hr) ?_ ?_ fun hF ↦ ?_
    · rw [List.map_append, List.pairwise_append]
      refine ⟨hp, ?_, ?_⟩
      · rw [hop, base_bnd T hk]; exact pairwise_newCols _ _ _ _
      · intro a ha b hb
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp ha
        obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hb
        obtain ⟨⟨v, col⟩, -, rfl⟩ := List.mem_map.mp hdm
        have := (hc c hcm).1
        simp only [hop, base_bnd T hk]
        omega
    · intro c hc'
      rcases List.mem_append.mp hc' with h | h
      · exact ⟨by have := (hc c h).1; rw [bnd_succ T hk]; omega, (hc c h).2⟩
      · obtain ⟨⟨v, col⟩, hvc, rfl⟩ := List.mem_map.mp h
        have hcol := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hvc)).1
        simp only at hcol
        simp only [hop, base_bnd T hk, hr2]
        refine ⟨by rw [bnd_succ T hk]; omega, k, col, hk, by omega, rfl, rfl⟩
    · rcases hf hF with ⟨c, hcm, hcp⟩ | ⟨m, hm, hle, hwp⟩
      · exact .inl ⟨c, List.mem_append_left _ hcm, hcp⟩
      · rcases m with _ | m
        · simp only [List.getElem_cons_zero] at hwp hle
          refine .inl ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨(evs.getD 0 0, 0), ?_, rfl⟩), ?_⟩
          · rw [List.mem_zipIdx_iff_getElem?]
            have h0 : 0 < evs.length := by omega
            simp [List.getElem?_eq_getElem h0, List.getD_eq_getElem _ _ h0]
          · exact List.take_of_length_le hle
        · exact .inr ⟨m, by simpa using hm, by simpa using hle, by simpa using hwp⟩

theorem length_tableWeights (hs : List ℕ) (e p : List E) :
    (Verifier.tableWeights hs e p).length = hs.length := by
  unfold Verifier.tableWeights
  suffices h : ∀ (l : List (E × ℕ)) (w : List E), w.length = hs.length →
      (l.foldl (fun weights (x : E × ℕ) ↦ List.zipWith (fun weight height ↦ weight *
        if x.2 < height then 1 + e.getD x.2 0 + x.1 else x.1) weights hs) w).length = hs.length from
    h _ _ (by simp)
  intro l
  induction l with
  | nil => intro w hw; exact hw
  | cons x l ih => intro w hw; exact ih _ (by simp [hw])

theorem getElem_vTables' (T : List Tab) (m : ℕ) (hm : m < (vTables T).length) :
    (vTables T)[m] = vTable m (T[m]'(by simpa using hm)) := by
  simp [vTables, List.getElem_zipIdx]

open LeanVM.Protocol.Compile in
/-- The table sumcheck's returns (adapted from WP-16b's `retOK_tableSumcheckClaims`). -/
theorem retOK_tsc (T : List Tab) (forms : List (List Verifier.Form)) (cp fp eqp : List E)
    (target : E) (hforms : forms.length = T.length) :
    RetOK (fun cl : List ColumnClaim ↦ (cl.map (·.column)).Pairwise (· < ·) ∧
        ∃ pt : List E, pt.length = (T.map (·.τ)).foldl max 0 ∧ (∀ c ∈ cl, ClaimOf T pt c) ∧
          ((∃ t ∈ T, t.τ = (T.map (·.τ)).foldl max 0 ∧ 0 < t.w) → ∃ c ∈ cl, c.point = pt))
      (tableSumcheckClaims (vTables T) (T.map (·.τ)) forms cp fp eqp target) := by
  unfold tableSumcheckClaims
  refine (LeanVM.Protocol.EndToEnd.Front.retOK_sumcheck 4 _ _).bind fun x hx ↦ ?_
  obtain ⟨ch, claim⟩ := x
  simp only [List.length_replicate] at hx
  let F : Prop := ∃ t ∈ T, t.τ = (T.map (·.τ)).foldl max 0 ∧ 0 < t.w
  refine (retOK_terms T cp fp ch.reverse F _ 0 0 0 [] (fun m hm ↦ ?_) (by simp) (by simp)
    (fun hF ↦ .inr ?_)).bind fun y hy ↦ ?_
  · simp only [List.length_zip, Lvm.M3.length_vTables, List.length_map] at hm
    have hmT : m < T.length := by omega
    refine ⟨by omega, ?_, ?_⟩
    · simp only [List.getElem_zip, zero_add, getElem_vTables' T m (by simpa using hmT)]
    · simp only [List.getElem_zip, zero_add, List.getElem_map]
  · obtain ⟨t, ht, htτ, htw⟩ := hF
    obtain ⟨m, hmT, rfl⟩ := List.getElem_of_mem ht
    have hlen : m < (List.zip (vTables T) (List.zip (T.map (·.τ))
        (List.zip forms (Verifier.tableWeights (T.map (·.τ)) eqp ch.reverse)))).length := by
      simp [length_tableWeights, hforms, hmT]
    refine ⟨m, hlen, ?_, ?_⟩
    · simp only [List.getElem_zip, List.getElem_map, List.length_reverse, hx, ← htτ]; rfl
    · simp only [List.getElem_zip, getElem_vTables' T m (by simpa using hmT)]
      simpa [vTable, Table.width] using htw
  · obtain ⟨final, cl⟩ := y
    refine RetOK.bind_true fun _ ↦ RetOK.ret ⟨hy.1, ch.reverse, by simp [hx], hy.2.1, hy.2.2⟩

open LeanVM.Protocol.Compile in
/-- **Every return of WP-9b's bus and table phases has `ClaimShape`.** -/
theorem retOK_lvmBusTableProg (T : List Tab) (μ : ℕ) :
    RetOK (ClaimShape T) (lvmBusTableProg (vTables T) (vLayout T) μ (busResV T)) := by
  unfold lvmBusTableProg
  refine RetOK.bind_true fun b ↦ ?_
  unfold tablePhaseClaims
  refine RetOK.bind_true fun xi ↦ ?_
  refine (retOK_tsc T _ _ _ _ _ (by simp [Lvm.M3.busResV, Lvm.M3.busFinalV])).bind
    fun cl hcl ↦ RetOK.ret ?_
  simpa [Lvm.M3.busResV, Lvm.M3.busFinalV, ClaimShape] using hcl

end Lvm.Acc
end
-- ===== end of `LvmAccSpecRet` =====

-- ===== merged from `LvmAccSpecL` (GOLF module merge: `LvmAccSpecL.lean` is now a stub importing `LvmAccSpecT`) =====
section
-- new for lvm (AC-S): phase 3b of the lvm instance on the wire (AC-N's proposed DSL instance, its
-- bodies), and why its pass means the table seam's fixed claims hold. The proof pattern of the
-- last step is WP-9b's `derived_holds` (`LvmM3FidFixC`).

/-!
# Phase 3b of the lvm instance

Over `E` (native forms through `FE.toExt3`/`FE.ofExt3`, as WP-9b's `fixedEvalV`), on the claims `cl`
the table phase returned, for the sumcheck tables `T`:

* `claimAt cl n`: the first claim on global column `n`; `gcol T c`: a `fixCols` column's number;
* `pubOkV`: `PUB`'s value column (table `pubTab`, column 0) has `pubEval` of the header lanes;
* `yOwnV`: `dot (eqKernel κ) (v_fix)`; `tablePointV`: the longest claim point (AC-V's `tablePoint`);
* `PhiV P tabs pub = toExt3 ∘ PhiC ∘ ofExt3` (`= phiE (fixColsR T pubTab) tableRounds`, rfl);
* **`accProgV P tabs pub cl`**: `accProg` with these (what AC-N's `midS` runs after the table phase);
* `claimAt_eq` (one claim per column), `tablePointV_eq` (the longest point is the sumcheck point);
* **`holds_of_good`**: if the phase's checks can all pass (`AccGood`: the `PUB` check, and every
  fixed claim's error `δ_k` zero), every fixed column's claim of the table seam holds of every stack.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
open Lvm.M3 (Tab ColSrc FixCol fixColsR sumcheckTabs vTables Lay inst colOfL FixOk pubEval)
open LeanVM.Protocol.Compile (VerifierProgram)

/-! ## The definitions (AC-N's proposal, relayed 2026-11-10) -/

/-- The first claim on global column `n` (the default claim if none). -/
def claimAt (cl : List ColumnClaim) (n : ℕ) : ColumnClaim := (cl.find? (·.column == n)).getD default

/-- A `fixCols` column's global number. -/
def gcol (T : List Tab) (c : FixCol) : ℕ := (globalColumnBases (vTables T)).getD c.tab 0 + c.col

/-- **`PUB`'s check**: the claim on table `pubTab`'s column 0 has the header lanes' extension at
its point (AC-V's `pubCheckR` over `E`). -/
def pubOkV (T : List Tab) (pubTab : ℕ) (pub : Pub) (cl : List ColumnClaim) : Bool :=
  let c := claimAt cl ((globalColumnBases (vTables T)).getD pubTab 0 + 0)
  decide (c.value = FE.toExt3 (pubEval pub.hdrLanes (c.point.map FE.ofExt3)))

/-- **`y_own(κ)`**: `dot (eqKernel κ)` of the claims on the `fixCols` columns. -/
def yOwnV (T : List Tab) (pubTab : ℕ) (cl : List ColumnClaim) (κ : List E) : E :=
  Verifier.dot (Verifier.eqKernel κ) ((fixColsR T pubTab).map fun c ↦ (claimAt cl (gcol T c)).value)

/-- **The table point**: the longest claim point (AC-V's `tablePoint`). -/
def tablePointV (cl : List ColumnClaim) : List E :=
  cl.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) []

/-- **`Φ̃` over `E`**: the native `PhiC` of the real instance through `toExt3`. -/
def PhiV (P : Params) (tabs : Pub → List Tab) (pub : Pub) (p : List E) : E :=
  FE.toExt3 (PhiC P (M3.real P tabs) pub (p.map FE.ofExt3))

/-- **Phase 3b of the lvm instance** on the claims `cl` of the table phase. -/
def accProgV (P : Params) (tabs : Pub → List Tab) (pub : Pub) (cl : List ColumnClaim) :
    VerifierProgram Unit :=
  let T := sumcheckTabs (tabs pub)
  accProg P.accLog accVars (pubOkV T P.pubTab pub cl) (FE.toExt3 pub.accIn.y)
    (pub.accIn.pt.map FE.toExt3) (yOwnV T P.pubTab cl) (fun κ ↦ tablePointV cl ++ κ) (PhiV P tabs pub)

theorem phiV_eq (P : Params) (tabs : Pub → List Tab) (pub : Pub) :
    PhiV P tabs pub = phiE (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) P.tableRounds := rfl

/-- **`AccOk acc_in` over `E`** is the native one. -/
theorem accOk_iff (P : Params) (tabs : Pub → List Tab) (pub : Pub) :
    AccOk P (M3.real P tabs) pub pub.accIn = true ↔
      PhiV P tabs pub (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y := by
  have hb : ∀ x y : FE, (x == y) = true ↔ x = y := fun x y ↦ ⟨Lvm.M3.FE_eq_of_beq, fun h ↦ by
    subst h; change (x.c₀ == x.c₀ && x.c₁ == x.c₁ && x.c₂ == x.c₂) = true; simp⟩
  rw [AccOk, hb, PhiV, List.map_map]
  simp only [Function.comp_def, FE.ofExt3_toExt3, List.map_id']
  exact FE.toExt3_inj.symm

/-! ## Reading the claims -/

/-- **One claim per column**: in a list with strictly increasing columns, the first claim on a
member's column is the member. -/
theorem claimAt_eq : ∀ {cl : List ColumnClaim}, (cl.map (·.column)).Pairwise (· < ·) →
    ∀ {c : ColumnClaim}, c ∈ cl → claimAt cl c.column = c
  | [], _, _, h => by simp at h
  | d :: cl, hp, c, hc => by
    rw [List.map_cons, List.pairwise_cons] at hp
    unfold claimAt
    rw [List.find?_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have hlt := hp.1 c.column (List.mem_map_of_mem hc)
      rw [show (d.column == c.column) = false by simp; omega]
      exact claimAt_eq hp.2 hc

/-- The longest point of claims that are prefixes of `pt`, one of them `pt` itself, is `pt`. -/
theorem tablePointV_eq {cl : List ColumnClaim} {pt : List E}
    (hpre : ∀ c ∈ cl, ∃ m, c.point = pt.take m) (hfull : ∃ c ∈ cl, c.point = pt) :
    tablePointV cl = pt := by
  suffices h : ∀ (l : List ColumnClaim) (r : List E), (∀ c ∈ l, ∃ m, c.point = pt.take m) →
      (∃ m, r = pt.take m) →
      (∃ m, l.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) r = pt.take m) ∧
        (∀ c ∈ l, c.point.length ≤
          (l.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) r).length) ∧
        r.length ≤ (l.foldl (fun r c ↦ if r.length < c.point.length then c.point else r) r).length by
    obtain ⟨⟨m, hm⟩, hle, -⟩ := h cl [] hpre ⟨0, by simp⟩
    obtain ⟨c, hc, hcp⟩ := hfull
    have := hle c hc
    rw [hcp, hm] at this
    rw [tablePointV, hm]
    exact List.take_of_length_le (by simpa using this)
  intro l
  induction l with
  | nil => intro r _ hr; exact ⟨hr, by simp, le_rfl⟩
  | cons c l ih =>
    intro r hl hr
    have hc := hl c List.mem_cons_self
    have hl' := fun d hd ↦ hl d (List.mem_cons_of_mem _ hd)
    simp only [List.foldl_cons]
    split_ifs with hlt
    · obtain ⟨h1, h2, h3⟩ := ih c.point hl' hc
      exact ⟨h1, fun d hd ↦ (List.mem_cons.mp hd).elim (fun h ↦ h ▸ h3) (h2 d), by omega⟩
    · obtain ⟨h1, h2, h3⟩ := ih r hl' hr
      exact ⟨h1, fun d hd ↦ (List.mem_cons.mp hd).elim (fun h ↦ by subst h; omega) (h2 d), h3⟩

/-- A fixed column outside `PUB`'s value column is listed in `fixCols`. -/
theorem mem_fixColsR_of {T : List Tab} {pubTab j i : ℕ} {t : Tab} {f : ℕ → FK} {ev : List FE → FE}
    (ht : T[j]? = some t) (hc : t.cols[i]? = some (.fix f ev)) (hn : ¬ (j = pubTab ∧ i = 0)) :
    (⟨j, t.τ, i, ev⟩ : FixCol) ∈ fixColsR T pubTab := by
  unfold fixColsR
  refine List.mem_flatMap.mpr ⟨(t, j), List.mem_zipIdx_iff_getElem?.mpr ht, ?_⟩
  refine List.mem_filterMap.mpr ⟨(.fix f ev, i), List.mem_zipIdx_iff_getElem?.mpr hc, ?_⟩
  simp only
  rw [ite_eq_right_iff.mpr (by simp at hn ⊢; omega)]

end Lvm.Acc
end
-- ===== end of `LvmAccSpecL` =====

/-!
# `accSpec`: phase 3b replaces the fixed-column check

* `AccInst P T pub`: the facts of the tables and the header the phase needs (`FixOk`, heights,
  `nFix ≤ 2^accLog`, `tableRounds + accLog = accVars`, `|acc_in.pt| = accVars`, `PUB`'s closed form);
* **`holds_of_good`**: if the phase's checks can all pass (`pubOkV` and every `δ_k = 0`), every
  derived (fixed) column's claim of the table seam holds of every stack;
* `candsA cands A`: the candidates, when `A` (here `AccOk acc_in`, a property of the statement);
* **`accSpecT`**: `Spec (accProgV …) (TablePost (candsA cands AccOk) ∧ ClaimShape) TablePostC`,
  escape `1/|E|` per `κ_j`, `D/|E|` at `t`, lead `max (accLog/|E|) T` (BLUEPRINT §12.6);
* **`lbusTableAccProg`/`lbusTableAccSpec`**: V_S phases 2–3b (bus, table sumcheck, phase 3b, the
  claims returned), from the commitment's doom of the `AccOk`-candidates to `TablePostC`.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab ColSrc FixCol fixColsR sumcheckTabs vTables vLayout busResV Lay inst colOfL FixOk
  pubEval TablePostC lvmBusTableProg)
open scoped ENNReal

/-- **What phase 3b needs of the tables `T` (the sumcheck tables of `tabs pub`) and the header.**
All but `pubEv` follow from `fitsR` and `MidHyp`; `pubEv` is the real `PUB` array's closed form. -/
structure AccInst (P : Params) (T : List Tab) (pub : Pub) : Prop where
  fix : FixOk T
  rounds : (T.map (·.τ)).foldl max 0 = P.tableRounds
  τle : ∀ t ∈ T, t.τ ≤ P.tableRounds
  full : ∃ t ∈ T, t.τ = P.tableRounds ∧ 0 < t.w
  nfix : (fixColsR T P.pubTab).length ≤ 2 ^ P.accLog
  vars : P.tableRounds + P.accLog = accVars
  acc : pub.accIn.pt.length = accVars
  pubEv : ∀ t f e, T[P.pubTab]? = some t → t.cols[0]? = some (.fix f e) →
    ∀ r : List FE, r.length = t.τ → e r = pubEval pub.hdrLanes r

/-- The sent evaluations of `fixCols` as the phase reads them. -/
def vsOf (T : List Tab) (pubTab : ℕ) (cl : List Verifier.ColumnClaim) : List E :=
  (fixColsR T pubTab).map fun c ↦ (claimAt cl (gcol T c)).value

/-! ## The good branch: every fixed claim holds -/

theorem colOfL_eq (L : Lay) (T : List Tab) (hτL : ∀ t ∈ T, t.τ ≤ L.μ) (c : (inst L T hτL).ColumnId) :
    colOfL L T hτL c = (Verifier.globalColumnBases (vTables T)).getD c.1.val 0 + c.2.val := rfl

/-- **If phase 3b's checks can all pass, every fixed column's claim of the table seam holds.** -/
theorem holds_of_good {L : Lay} {T : List Tab} {hτL : ∀ t ∈ T, t.τ ≤ L.μ} {P : Params} {pub : Pub}
    {cl : List Verifier.ColumnClaim} (H : AccInst P T pub) (hsh : ClaimShape T cl)
    (hok : pubOkV T P.pubTab pub cl = true)
    (hδ : ∀ w < 2 ^ P.accLog, deltaOf (fixColsR T P.pubTab) (vsOf T P.pubTab cl) (tablePointV cl) w = 0)
    (c : LeanVM.Protocol.ColumnClaim (inst L T hτL)) (hd : (inst L T hτL).derived c.col ≠ none)
    (hc : (⟨colOfL L T hτL c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ cl)
    (q : Column (inst L T hτL).μ) : c.Holds q := by
  obtain ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩, pt, v⟩ := c
  have hj' : j < T.length := hj
  have htj : T.get ⟨j, hj⟩ = T[j] := rfl
  have hfo : T[j].fixedOf i ≠ none := by
    intro h; apply hd
    show Option.map _ ((T.get ⟨j, hj⟩).fixedOf i) = none
    rw [htj, h]; rfl
  obtain ⟨f, ev, hcol⟩ : ∃ f ev, T[j].cols[i]? = some (.fix f ev) := by
    unfold Tab.fixedOf at hfo
    split at hfo
    · exact ⟨_, _, by assumption⟩
    · exact absurd rfl hfo
  have hcolq : (inst L T hτL).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ = Lvm.M3.fixedColumn T[j].τ f := by
    simp [M3Instance.column, inst, Tab.fixedOf, htj, hcol]
  -- the claim the phase reads is the seam's
  set n := colOfL L T hτL ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ with hn
  have hca : claimAt cl n = ⟨n, pt.toList, v⟩ := claimAt_eq hsh.1 hc
  obtain ⟨ptS, hptS, hof, hfull⟩ := hsh.2
  -- its point is the sumcheck point's prefix, and the phase's table point is the sumcheck point
  obtain ⟨j', i', hj'', hi', hcn, hpt⟩ := hof _ hc
  have hji : j = j' ∧ i = i' := by
    have h1 := Lvm.M3.colLoc_colOfL L T hτL ⟨⟨j, hj⟩, ⟨i, hi⟩⟩
    have h2 := Lvm.M3.colLoc_colOfL L T hτL ⟨⟨j', hj''⟩, ⟨i', hi'⟩⟩
    rw [colOfL_eq, base_bnd T hj''] at h2
    simp only at hcn
    rw [← hcn] at h2
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩
  obtain ⟨hj1, hi1⟩ := hji
  subst hj1
  subst hi1
  simp only at hpt
  have hr : tablePointV cl = ptS := tablePointV_eq (fun d hd ↦ by
      obtain ⟨_, _, hk, -, -, hp⟩ := hof d hd; exact ⟨_, hp⟩)
    (hfull (by obtain ⟨t, ht, h1, h2⟩ := H.full; exact ⟨t, ht, by rw [h1, H.rounds], h2⟩))
  have hlen : pt.toList.length = T[j].τ := by simp; rfl
  -- the value is the closed form at the point
  have hv : v = FE.toExt3 (ev (pt.toList.map FE.ofExt3)) := by
    by_cases hp : j = P.pubTab ∧ i = 0
    · obtain ⟨hp1, hp2⟩ := hp
      have hn0 : (Verifier.globalColumnBases (vTables T)).getD P.pubTab 0 + 0 = n := by
        rw [hn, colOfL_eq]; simp only [hp1, hp2]
      unfold pubOkV at hok
      simp only [decide_eq_true_eq] at hok
      rw [hn0, hca] at hok
      simp only at hok
      rw [hok, H.pubEv T[j] f ev (by rw [← hp1]; exact List.getElem?_eq_getElem hj')
        (by rw [← hp2]; exact hcol) _ (by simpa using hlen)]
    · obtain ⟨k, hk, hk'⟩ := List.mem_iff_getElem.mp
        (mem_fixColsR_of (List.getElem?_eq_getElem hj') hcol hp)
      have h0 := hδ k (lt_of_lt_of_le hk H.nfix)
      rw [deltaOf, dif_pos hk, sub_eq_zero, hk'] at h0
      rw [vsOf, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, hk',
        show gcol T ⟨j, T[j].τ, i, ev⟩ = n from rfl, hca, hr, ← List.map_take, ← hpt] at h0
      exact h0
  have hmem : ColSrc.fix f ev ∈ T[j].cols := List.mem_of_getElem? hcol
  have hfx := H.fix _ (List.getElem_mem hj') f ev hmem (pt.toList.map FE.ofExt3) (by simpa using hlen)
  show eval₂Mle ((inst L T hτL).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩).values (algebraMap K E) pt = v
  rw [hcolq, hv, hfx, Lvm.M3.toExt3_mle_fixed]
  rfl

/-! ## The phase's specification on the table seam -/

/-- The candidates, when `A` holds (`A` a property of the statement: `AccOk acc_in`). -/
def candsA {α : Type} (cands : Word → Set α) (A : Prop) : Word → Set α := fun W ↦ {o | o ∈ cands W ∧ A}

theorem candsA_finite {α : Type} {cands : Word → Set α} (hf : ∀ W, (cands W).Finite) (A : Prop) :
    ∀ W, (candsA cands A W).Finite := fun W ↦ (hf W).subset fun _ h ↦ h.1

theorem candsA_ncard {α : Type} {cands : Word → Set α} {L₀ : ℕ} (hf : ∀ W, (cands W).Finite)
    (hc : ∀ W, (cands W).ncard ≤ L₀) (A : Prop) : ∀ W, (candsA cands A W).ncard ≤ L₀ :=
  fun W ↦ (Set.ncard_le_ncard (fun _ h ↦ h.1) (hf W)).trans (hc W)

/-- **`AccOk acc_in` over `E`** (`accOk_iff`: the native one). -/
def AccOkE (P : Params) (tabs : Pub → List Tab) (pub : Pub) : Prop :=
  PhiV P tabs pub (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y

section Inst

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ)

/-- The phase's table point has `tableRounds` coordinates. -/
theorem length_tablePointV {T : List Tab} {cl : List Verifier.ColumnClaim} (H : AccInst P T pub)
    (hs : ClaimShape T cl) : (tablePointV cl).length = P.tableRounds := by
  obtain ⟨ptS, hptS, hof, hfull⟩ := hs.2
  rw [tablePointV_eq (fun d hd ↦ by obtain ⟨_, _, hk, -, -, hp⟩ := hof d hd; exact ⟨_, hp⟩)
    (hfull (by obtain ⟨t, ht, h1, h2⟩ := H.full; exact ⟨t, ht, by rw [h1, H.rounds], h2⟩)),
    hptS, H.rounds]

/-- **The instance's `AccHyp`** (`accHyp_phi` at the claims' values and table point). -/
theorem accHypV {cl : List Verifier.ColumnClaim} (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hs : ClaimShape (sumcheckTabs (tabs pub)) cl) :
    AccHyp P.accLog accVars (pub.accIn.pt.map FE.toExt3) (yOwnV (sumcheckTabs (tabs pub)) P.pubTab cl)
      (fun κ ↦ tablePointV cl ++ κ) (PhiV P tabs pub)
      (deltaOf (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) (vsOf (sumcheckTabs (tabs pub)) P.pubTab cl)
        (tablePointV cl)) := by
  have h := accHyp_phi (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) (cellOf (sumcheckTabs (tabs pub)))
    P.tableRounds P.accLog (fixCols_τ _ _ H.τle) (fixCols_ev _ H.fix) H.nfix
    (pub.accIn.pt.map FE.toExt3) (tablePointV cl) (vsOf (sumcheckTabs (tabs pub)) P.pubTab cl)
    (by rw [List.length_map, H.acc, H.vars]) (length_tablePointV P pub H hs) (by simp [vsOf])
  rw [H.vars] at h
  exact h

/-- **`accSpec`** (BLUEPRINT §12.6, replaces WP-9b's `tableCheckSpec`): phase 3b of the lvm
instance, from the table seam of the candidates meeting `AccOk acc_in` (with the claims' shape,
a return fact of the table phase) to the doom of the committed claims of all candidates
(`TablePostC`). Escape `1/|E|` per `κ_j`, `accVars/|E|` at `t`. -/
noncomputable def accSpecT (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (cands : Word → Set (∀ i, TheOracle (inst L (sumcheckTabs (tabs pub)) hτL) i))
    (cl : List Verifier.ColumnClaim) {εmax Tf : ℝ≥0∞} (hD : errE accVars ≤ εmax) (hTf : Tf ≤ εmax) :
    Spec (accProgV P tabs pub cl)
      (fun h ↦ TablePost (inst L (sumcheckTabs (tabs pub)) hτL) (candsA cands (AccOkE P tabs pub)) ()
          (colOfL L (sumcheckTabs (tabs pub)) hτL) cl h ∧ ClaimShape (sumcheckTabs (tabs pub)) cl)
      (fun _ h ↦ TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands ()
        (colOfL L (sumcheckTabs (tabs pub)) hτL) cl h)
      εmax (max (P.accLog * errE 1) Tf) Tf := by
  classical
  exact if hs : ClaimShape (sumcheckTabs (tabs pub)) cl then
    (accSpecG (accHypV P tabs pub H hs)
        (TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands () (colOfL L (sumcheckTabs (tabs pub)) hτL) cl)
        (fun _ l _ ⟨W, tout, hW, rest⟩ ↦ ⟨W, tout, firstWord_append hW l, rest⟩) hD hTf).mono
      (fun h ⟨hp, _⟩ ↦ by
        by_cases hg : AccGood P.accLog (pubOkV (sumcheckTabs (tabs pub)) P.pubTab pub cl)
            (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (PhiV P tabs pub)
            (deltaOf (fixColsR (sumcheckTabs (tabs pub)) P.pubTab)
              (vsOf (sumcheckTabs (tabs pub)) P.pubTab cl) (tablePointV cl))
        · refine .inr ?_
          obtain ⟨W, tout, hW, hDm, h1, hcl, hout⟩ := hp
          refine ⟨W, tout, hW, fun o ho ⟨hc, hpub, haux⟩ ↦ hDm o ⟨ho, hg.2.1⟩
            ⟨fun c hcm ↦ ?_, hpub, haux⟩, h1, hcl, hout⟩
          by_cases hd : (inst L (sumcheckTabs (tabs pub)) hτL).derived c.col = none
          · exact hc c hcm hd
          · exact holds_of_good H hs hg.1 hg.2.2 c hd (hcl c hcm) _
        · exact .inl hg)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hs hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Inst

/-! ## V_S phases 2–3b -/

/-- **V_S phases 2–3b** on the program objects (BLUEPRINT §12.4): the bus phase, the table sumcheck,
phase 3b (in place of WP-9b's `require (tableCheckVB)`), the claims. -/
def lbusTableAccProg (P : Params) (tabs : Pub → List Tab) (pub : Pub) (μ : ℕ) :
    VerifierProgram (List Verifier.ColumnClaim) :=
  (lvmBusTableProg (vTables (sumcheckTabs (tabs pub))) (vLayout (sumcheckTabs (tabs pub))) μ
      (busResV (sumcheckTabs (tabs pub)))).bind fun cl ↦
    (accProgV P tabs pub cl).bind fun _ ↦ VerifierProgram.ret cl

section Phase

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  (cands : Word → Set (∀ i, TheOracle (inst L (sumcheckTabs (tabs pub)) hτL) i)) {εmax : ℝ≥0∞}

/-- **V_S phases 2–3b of the lvm instance** (WP-9b's `lbusTableCheckSpec` with `accSpec` in place of
`tableCheckSpec`): from the commitment's doom of the candidates meeting `AccOk acc_in` to the
committed claims' doom of all candidates (`TablePostC`). `Ta` is phase 3b's lead
`max (accLog/|E|) T`; `T` is the follower's. -/
noncomputable def lbusTableAccSpec (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (HDoom (candsA cands (AccOkE P tabs pub)) (Seam.commit (inst L (sumcheckTabs (tabs pub)) hτL)) ())
      (TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands () (colOfL L (sumcheckTabs (tabs pub)) hτL))
      εmax (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  (Lvm.KG.specWithRet (Lvm.M3.lbusTableSpec L (sumcheckTabs (tabs pub)) hτL hsc
      (candsA cands (AccOkE P tabs pub)) hkey hw (candsA_finite hfin _) (candsA_ncard hfin hcard _) hμ hab
      he4 hT hlam he3 hTa hxi) (retOK_lvmBusTableProg (sumcheckTabs (tabs pub)) _)).bind fun cl ↦
    ((accSpecT L P tabs pub hτL H cands cl hD hTf).mono (fun _ ⟨hs, hp⟩ ↦ ⟨hp, hs⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind fun _ ↦
      Spec.ret (Post := TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands ()
        (colOfL L (sumcheckTabs (tabs pub)) hτL)) cl

end Phase

end Lvm.Acc
