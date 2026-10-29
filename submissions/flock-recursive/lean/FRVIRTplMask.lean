-- New for `flock-recursive` (BLUEPRINT A.9 `finSh`, A.11; stage S-E9, track L-circ).
import FRVIRTplTab
import FRNodeTargetCore

/-!
# The replay template of `shiftMask` (revision 3.14, the chain-masked Sh weights)

`implC.shiftMask` is `NodeI.shiftMaskI τ r` (INT-3): the two 16-coordinate block points' two-level
`eq` tables (`NodeI.tabs`: 8 + 8 coordinates), the products `R = B_τ·B_r`, `R2 = B_τ·B_r(·+1)`,
`C = A_τ·A_r`, `C1 = A_τ·A_r(·+1)`, `C2` (the wrap at 255), their prefix sums (linear), and the
separable range sums `sepSum` over the two chains' link blocks. The template **mirrors it gate for
gate**: four `eqTblG` tables (255 products each), 1,025 products, 26 for the range sums and the
starts' weight: 2,071 rows. **`tplShiftMask_ok`**: the gate equations give `shiftMaskI`.
-/

namespace FR
namespace Tpl
open Circ NodeI

variable {e : Env}

/-! ## The template -/

/-- Coordinate `l` of `τ : AF n` (`0` past `n`). -/
def cT (n l : ℕ) : LinT := if l < n then I l else []

/-- Coordinate `l` of `r : AF m`, after `τ`'s `n` inputs. -/
def cR (n m l : ℕ) : LinT := if l < m then I (n + l) else []

/-- The four tables: `τ`'s low and high 8 coordinates, then `r`'s. -/
def mTabs (n m : ℕ) : List (List Gate × List LinT) :=
  [eqTblG ((List.range 8).map (cT n)) 0, eqTblG ((List.range 8).map fun l => cT n (8 + l)) 255,
   eqTblG ((List.range 8).map (cR n m)) 510, eqTblG ((List.range 8).map fun l => cR n m (8 + l)) 765]

/-- Entry `i` of table `t` (`[]` past the end). -/
def mEnt (n m t i : ℕ) : LinT := ((mTabs n m).getD t ([], [])).2.getD i []

/-- The 1,025 products: `R`, `R2`, `C`, `C1` (256 each), then `C2`'s single entry. -/
def mProds (n m : ℕ) : List Gate :=
  mulsG 256 (fun h => mEnt n m 1 h) (fun h => mEnt n m 3 h) ++
  mulsG 256 (fun h => mEnt n m 1 h) (fun h => mEnt n m 3 (h + 1)) ++
  mulsG 256 (fun l => mEnt n m 0 l) (fun l => mEnt n m 2 l) ++
  mulsG 256 (fun l => mEnt n m 0 l) (fun l => mEnt n m 2 (l + 1)) ++
  [.mul (mEnt n m 0 255) (mEnt n m 2 0)]

/-- A product's form (`[]` past 256): `R` at locals `1020 + h`, `R2` at `1276`, `C` at `1532`, `C1`
at `1788`; `C2` at `2044` (only `l = 255`). -/
def fR (h : ℕ) : LinT := if h < 256 then L (1020 + h) else []
def fR2 (h : ℕ) : LinT := if h < 256 then L (1276 + h) else []
def fC (l : ℕ) : LinT := if l < 256 then L (1532 + l) else []
def fC1 (l : ℕ) : LinT := if l < 256 then L (1788 + l) else []
def fC2 (l : ℕ) : LinT := if l = 255 then L 2044 else []

/-- The prefix sum `Σ_{l<i} f l` (linear). -/
def pfxT (f : ℕ → LinT) (i : ℕ) : LinT := (List.range i).flatMap f

/-- `twoF` at `X`: two products. -/
def twoP (f g : ℕ → LinT) (X : ℕ) : List (LinT × LinT) :=
  [(pfxT f (X / 256), pfxT g 256), (f (X / 256), pfxT g (X % 256))]

/-- The range sums' points (`N = chainN`): `lo + n` and `lo` for the two chains. -/
def mPts : List ℕ := [0 + (Layout.chainN - 1), 0, Layout.chainN + (Layout.chainN - 1), Layout.chainN]

/-- The 26 last products: per output pair (`R·C`, `R·C1`, `R2·C2`) `twoF` at the four points,
then `eq(r, 0)` and `eq(r, N)`. -/
def mSP (n m : ℕ) : List (LinT × LinT) :=
  mPts.flatMap (twoP fR fC) ++ mPts.flatMap (twoP fR fC1) ++ mPts.flatMap (twoP fR2 fC2) ++
    [(mEnt n m 2 0, mEnt n m 3 0),
     (mEnt n m 2 (Layout.chainN % 256), mEnt n m 3 (Layout.chainN / 256 % 256))]

/-- `sepSum` from the four locals of `twoF` at `lo + n` and `lo` (from local `k`). -/
def sepT (k : ℕ) : LinT := L k ++ L (k + 1) ++ sc (-1) (L (k + 2)) ++ sc (-1) (L (k + 3))

/-- **`shiftMask`** for `τ : AF n`, `r : AF m` (inputs `τ`, then `r`). -/
def tplShiftMask (n m : ℕ) : Tpl :=
  ⟨(mTabs n m).flatMap Prod.fst ++ mProds n m ++
      mulsG 26 (fun i => ((mSP n m).getD i ([], [])).1) (fun i => ((mSP n m).getD i ([], [])).2),
    [sepT 2045 ++ sepT 2049, sepT 2053 ++ sepT 2057 ++ (sepT 2061 ++ sepT 2065),
     L 2069 ++ L 2070]⟩

/-! ## The template, computed with its tables once (S-E13: plan time) -/

/-- `mEnt` over given tables. -/
def mEntT (T : List (List Gate × List LinT)) (t i : ℕ) : LinT := (T.getD t ([], [])).2.getD i []

/-- `mProds` over given tables. -/
def mProdsT (T : List (List Gate × List LinT)) : List Gate :=
  mulsG 256 (fun h => mEntT T 1 h) (fun h => mEntT T 3 h) ++
  mulsG 256 (fun h => mEntT T 1 h) (fun h => mEntT T 3 (h + 1)) ++
  mulsG 256 (fun l => mEntT T 0 l) (fun l => mEntT T 2 l) ++
  mulsG 256 (fun l => mEntT T 0 l) (fun l => mEntT T 2 (l + 1)) ++
  [.mul (mEntT T 0 255) (mEntT T 2 0)]

/-- `mSP` over given tables. -/
def mSPT (T : List (List Gate × List LinT)) : List (LinT × LinT) :=
  mPts.flatMap (twoP fR fC) ++ mPts.flatMap (twoP fR fC1) ++ mPts.flatMap (twoP fR2 fC2) ++
    [(mEntT T 2 0, mEntT T 3 0),
     (mEntT T 2 (Layout.chainN % 256), mEntT T 3 (Layout.chainN / 256 % 256))]

/-- **`tplShiftMask`, its four tables built once** (`mEnt` rebuilds them per entry: 1.5 s per
template). -/
def tplShiftMaskF (n m : ℕ) : Tpl :=
  let T := mTabs n m
  let sp := mSPT T
  ⟨T.flatMap Prod.fst ++ mProdsT T ++ mulsG 26 (fun i => (sp.getD i ([], [])).1)
      (fun i => (sp.getD i ([], [])).2),
    [sepT 2045 ++ sepT 2049, sepT 2053 ++ sepT 2057 ++ (sepT 2061 ++ sepT 2065), L 2069 ++ L 2070]⟩

theorem tplShiftMaskF_eq (n m : ℕ) : tplShiftMaskF n m = tplShiftMask n m := rfl

/-! ## Correctness -/

theorem ofFn_lo8 (τ : Array F) : List.ofFn (lo8 (Impl.ptA 16 τ)) = (List.range 8).map fun l => τ.getD l 0 :=
  List.ext_getElem (by simp) fun i _ _ => by
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, lo8, Impl.ptA]

theorem ofFn_hi8 (τ : Array F) :
    List.ofFn (hi8 (Impl.ptA 16 τ)) = (List.range 8).map fun l => τ.getD (8 + l) 0 :=
  List.ext_getElem (by simp) fun i _ _ => by
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, hi8, Impl.ptA]

/-- An `eqTblG` table's entry `i` is the `eqTable` entry. -/
theorem tblG_ent (h1 : e.one = 1) {cs : List LinT} {k : ℕ} (hk : Eqns e (eqTblG cs k).1 k) (i : ℕ) :
    ((eqTblG cs k).2.getD i []).ev e = (eqTable (cs.map (LinT.ev e))).getD i 0 := by
  rw [getD_map_ev, eqTblG_ev h1 cs k hk, arr_getD]

theorem nl_app (a b : List Gate) : nlocs (a ++ b) = nlocs a + nlocs b := by
  simp [nlocs, List.map_append, List.sum_append]

theorem tblG_nl (cs : List LinT) (k : ℕ) (h8 : cs.length = 8) : nlocs (eqTblG cs k).1 = 255 := by
  have := (eqTblG_nlocs cs k).1; rw [h8] at this; omega

theorem getD_big {l : List F} {i : ℕ} (h : 2 ^ l.length ≤ i) : (eqTable l).getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [eqTable_size]; omega)]; rfl

theorem tabs_a_big (rb : Fin 16 → F) {i : ℕ} (h : 256 ≤ i) : (tabs rb).a i = 0 := by
  rw [Tabs.a, tabs_A]; exact getD_big (by simp; omega)

theorem tabs_b_big (rb : Fin 16 → F) {i : ℕ} (h : 256 ≤ i) : (tabs rb).b i = 0 := by
  rw [Tabs.b, tabs_B]; exact getD_big (by simp; omega)

theorem sum_range_ev (f : ℕ → LinT) (i : ℕ) :
    (pfxT f i).ev e = ∑ l ∈ Finset.range i, (f l).ev e := by
  rw [pfxT, ev_flatMap, ← sumTo_list, sumTo_eq]

section Proof
variable {τ r : Array F} (hi : InpIs e (τ.toList ++ r.toList))
include hi

theorem cT_ev (l : ℕ) : (cT τ.size l).ev e = τ.getD l 0 := by
  by_cases h : l < τ.size
  · simp only [cT, h, ite_true]; rw [ev_I, hi, getD_append_left (by simpa using h), arr_getD]
  · simp only [cT, h, ite_false, ev_nil]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

theorem cR_ev (l : ℕ) : (cR τ.size r.size l).ev e = r.getD l 0 := by
  by_cases h : l < r.size
  · simp only [cR, h, ite_true]; rw [ev_I, hi, ← Array.length_toList, getD_append_right, arr_getD]
  · simp only [cR, h, ite_false, ev_nil]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

set_option maxRecDepth 4096 in
/-- **`shiftMask`'s template computes `shiftMaskI`.** -/
theorem tplShiftMask_ok (h1 : e.one = 1) (h : Eqns e (tplShiftMask τ.size r.size).gates 0) :
    (tplShiftMask τ.size r.size).outs.map (LinT.ev e) =
      encV (.f (shiftMaskI τ r).1) ++ encV (.f (shiftMaskI τ r).2.1) ++
        encV (.f (shiftMaskI τ r).2.2) := by
  -- the tables
  simp only [tplShiftMask, mTabs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Eqns.append] at h
  obtain ⟨⟨⟨g1, g2, g3, g4⟩, hp⟩, hs⟩ := h
  have l8 : ∀ f : ℕ → LinT, ((List.range 8).map f).length = 8 := fun f => by simp
  simp only [tblG_nl _ _ (l8 _), zero_add, nl_app] at g2 g3 g4 hp hs
  norm_num at g3 g4 hp hs
  have hA : ∀ i, (mEnt τ.size r.size 0 i).ev e = (tabs (Impl.ptA 16 τ)).a i := fun i => by
    simp only [mEnt, mTabs, List.getD_cons_zero]
    rw [tblG_ent h1 g1, List.map_map, Tabs.a, tabs_A, ofFn_lo8]
    congr 2; exact List.map_congr_left fun l _ => cT_ev hi l
  have hB : ∀ i, (mEnt τ.size r.size 1 i).ev e = (tabs (Impl.ptA 16 τ)).b i := fun i => by
    simp only [mEnt, mTabs, List.getD_cons_succ, List.getD_cons_zero]
    rw [tblG_ent h1 g2, List.map_map, Tabs.b, tabs_B, ofFn_hi8]
    congr 2; exact List.map_congr_left fun l _ => cT_ev hi (8 + l)
  have hA' : ∀ i, (mEnt τ.size r.size 2 i).ev e = (tabs (Impl.ptA 16 r)).a i := fun i => by
    simp only [mEnt, mTabs, List.getD_cons_succ, List.getD_cons_zero]
    rw [tblG_ent h1 g3, List.map_map, Tabs.a, tabs_A, ofFn_lo8]
    congr 2; exact List.map_congr_left fun l _ => cR_ev hi l
  have hB' : ∀ i, (mEnt τ.size r.size 3 i).ev e = (tabs (Impl.ptA 16 r)).b i := fun i => by
    simp only [mEnt, mTabs, List.getD_cons_succ, List.getD_cons_zero]
    rw [tblG_ent h1 g4, List.map_map, Tabs.b, tabs_B, ofFn_hi8]
    congr 2; exact List.map_congr_left fun l _ => cR_ev hi (8 + l)
  -- the products
  simp only [mProds, Eqns.append, mulsG_nlocs, nl_app] at hp hs
  norm_num at hp hs
  obtain ⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩ := hp
  have e1 := mulsG_eqns p1; have e2 := mulsG_eqns p2; have e3 := mulsG_eqns p3
  have e4 := mulsG_eqns p4
  have e5 := (Eqns.cons.1 p5).1
  simp only [Gate.Eqn] at e5
  have vR : ∀ h, (fR h).ev e = (tabs (Impl.ptA 16 τ)).b h * (tabs (Impl.ptA 16 r)).b h := fun h => by
    unfold fR; split_ifs with hh
    · rw [ev_L, show 1020 + h = 1020 + h from rfl, e1 h hh, hB, hB']
    · rw [ev_nil, tabs_b_big _ (by omega), zero_mul]
  have vR2 : ∀ h, (fR2 h).ev e = (tabs (Impl.ptA 16 τ)).b h * (tabs (Impl.ptA 16 r)).b (h + 1) := fun h => by
    unfold fR2; split_ifs with hh
    · rw [ev_L, show 1276 + h = 1020 + 256 + h by omega, e2 h hh, hB, hB']
    · rw [ev_nil, tabs_b_big _ (by omega), zero_mul]
  have vC : ∀ l, (fC l).ev e = (tabs (Impl.ptA 16 τ)).a l * (tabs (Impl.ptA 16 r)).a l := fun l => by
    unfold fC; split_ifs with hh
    · rw [ev_L, show 1532 + l = 1020 + 256 + 256 + l by omega, e3 l hh, hA, hA']
    · rw [ev_nil, tabs_a_big _ (by omega), zero_mul]
  have vC1 : ∀ l, (fC1 l).ev e = (tabs (Impl.ptA 16 τ)).a l * (tabs (Impl.ptA 16 r)).a (l + 1) := fun l => by
    unfold fC1; split_ifs with hh
    · rw [ev_L, show 1788 + l = 1020 + 256 + 256 + 256 + l by omega, e4 l hh, hA, hA']
    · rw [ev_nil, tabs_a_big _ (by omega), zero_mul]
  have vC2 : ∀ l, (fC2 l).ev e = if l = 255 then (tabs (Impl.ptA 16 τ)).a 255 * (tabs (Impl.ptA 16 r)).a 0 else 0 := fun l => by
    unfold fC2; split_ifs with hh
    · rw [ev_L, show (2044 : ℕ) = 1020 + 256 + 256 + 256 + 256 from rfl, e5, hA, hA']
    · rfl
  -- the range sums
  have es := mulsG_eqns hs
  have hv : ∀ i < 26, e.loc (2045 + i) =
      ((mSP τ.size r.size).getD i ([], [])).1.ev e * ((mSP τ.size r.size).getD i ([], [])).2.ev e := fun i hi' => by
    have := es i hi'
    rw [show 1020 + (1024 + nlocs [Gate.mul (mEnt τ.size r.size 0 255) (mEnt τ.size r.size 2 0)]) + i =
      2045 + i from rfl] at this
    simpa only [List.getD_eq_getElem?_getD] using this
  have pf : ∀ (f : ℕ → LinT) (g : ℕ → F), (∀ x, (f x).ev e = g x) → ∀ i ≤ 256,
      (pfxT f i).ev e = (pfx g).getD i 0 := fun f g hfg i hi' => by
    rw [sum_range_ev, pfx_getD _ hi']; exact Finset.sum_congr rfl fun x _ => hfg x
  have tw : ∀ (f g : ℕ → LinT) (F' G' : ℕ → F), (∀ x, (f x).ev e = F' x) → (∀ x, (g x).ev e = G' x) →
      ∀ X ≤ 2 ^ 16, ∀ k, e.loc k = (pfxT f (X / 256)).ev e * (pfxT g 256).ev e →
        e.loc (k + 1) = (f (X / 256)).ev e * (pfxT g (X % 256)).ev e →
        e.loc k + e.loc (k + 1) = twoF (pfx F') F' (pfx G') X := by
    intro f g F' G' hf hg X hX k hk hk1
    rw [hk, hk1, twoF, pf f F' hf _ (by omega), pf g G' hg _ le_rfl, pf g G' hg _ (by omega), hf]
  have sep : ∀ (f g : ℕ → LinT) (F' G' : ℕ → F), (∀ x, (f x).ev e = F' x) →
      (∀ x, (g x).ev e = G' x) → ∀ j k lo nn, lo + nn ≤ 2 ^ 16 →
      (∀ i < 4, e.loc (k + i) = ((twoP f g (lo + nn) ++ twoP f g lo).getD i ([], [])).1.ev e *
        ((twoP f g (lo + nn) ++ twoP f g lo).getD i ([], [])).2.ev e) → j = k →
      (sepT j).ev e = sepSum (pfx F') F' (pfx G') lo nn := by
    intro f g F' G' hf hg j k lo nn hl hk hj; subst hj
    have a := tw f g F' G' hf hg (lo + nn) hl j (by simpa [twoP] using hk 0 (by norm_num))
      (by simpa [twoP] using hk 1 (by norm_num))
    have b := tw f g F' G' hf hg lo (by omega) (j + 2) (by simpa [twoP] using hk 2 (by norm_num))
      (by simpa [twoP, add_assoc] using hk 3 (by norm_num))
    rw [sepT, ev_append, ev_append, ev_append, ev_sc, ev_sc, ev_L, ev_L, ev_L, ev_L, sepSum, ← a, ← b]
    rw [show j + 2 + 1 = j + 3 by omega]; ring
  have grp : ∀ (f g : ℕ → LinT) (o lo nn : ℕ), (∀ i < 4, (mSP τ.size r.size).getD (o + i) ([], []) =
      (twoP f g (lo + nn) ++ twoP f g lo).getD i ([], [])) → o + 4 ≤ 26 →
      ∀ i < 4, e.loc (2045 + o + i) = ((twoP f g (lo + nn) ++ twoP f g lo).getD i ([], [])).1.ev e *
        ((twoP f g (lo + nn) ++ twoP f g lo).getD i ([], [])).2.ev e := by
    intro f g o lo nn hg ho i hi'
    rw [add_assoc, hv (o + i) (by omega), hg i hi']
  have hN : Layout.chainN = 23146 := rfl
  have b1 : Layout.chainN + (Layout.chainN - 1) ≤ 2 ^ 16 := by rw [hN]; norm_num
  have b0 : 0 + (Layout.chainN - 1) ≤ 2 ^ 16 := by rw [hN]; norm_num
  simp only [tplShiftMask, List.map_cons, List.map_nil, encV, List.cons_append, List.nil_append]
  unfold shiftMaskI
  dsimp only
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩
  · rw [ev_append, sep fR fC _ _ vR vC 2045 2045 0 _ b0
        (grp fR fC 0 0 _ (fun i hi' => by interval_cases i <;> rfl) (by norm_num)) rfl,
      sep fR fC _ _ vR vC 2049 2049 Layout.chainN _ b1
        (grp fR fC 4 _ _ (fun i hi' => by interval_cases i <;> rfl) (by norm_num)) rfl]
  · rw [ev_append, ev_append, ev_append,
      sep fR fC1 _ _ vR vC1 2053 2053 0 _ b0
        (grp fR fC1 8 0 _ (fun i hi' => by interval_cases i <;> rfl) (by norm_num)) rfl,
      sep fR fC1 _ _ vR vC1 2057 2057 Layout.chainN _ b1
        (grp fR fC1 12 _ _ (fun i hi' => by interval_cases i <;> rfl) (by norm_num)) rfl,
      sep fR2 fC2 _ _ vR2 vC2 2061 2061 0 _ b0
        (grp fR2 fC2 16 0 _ (fun i hi' => by interval_cases i <;> rfl) (by norm_num)) rfl,
      sep fR2 fC2 _ _ vR2 vC2 2065 2065 Layout.chainN _ b1
        (grp fR2 fC2 20 _ _ (fun i hi' => by interval_cases i <;> rfl) (by norm_num)) rfl]
  · rw [ev_append, ev_L, ev_L, show (2069 : ℕ) = 2045 + 24 from rfl, show (2070 : ℕ) = 2045 + 25 from rfl,
      hv 24 (by norm_num), hv 25 (by norm_num)]
    simp only [mSP, mPts, twoP, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, List.getD_cons_succ, List.getD_cons_zero, hA', hB', eqbI]

end Proof

/-! ## Controls -/

/-- (+) Three outputs; the range sums run over the link blocks `c·N + k`, `k < N − 1`. -/
theorem tplShiftMask_outs (n m : ℕ) : (tplShiftMask n m).outs.length = 3 := rfl

theorem mPts_link : mPts = [23145, 0, 46291, 23146] := by decide

/-- (−) Not the unmasked ranges of `N` blocks per chain (which would link chain 1's last block to
chain 2's first). -/
theorem mPts_neg : mPts ≠ [23146, 0, 46292, 23146] := by decide

end Tpl
end FR
