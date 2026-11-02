-- G6: this module also holds the former modules `FRVIRTplMask` (one section each, in import order).
import FRVIRTplTab
import FRNodeTargetCore

section G6_FRVIRTplMask

-- New for `flock-recursive` (BLUEPRINT A.9 `finSh`, A.11; stage S-E9, track L-circ).

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

end G6_FRVIRTplMask

section G6_FRVIRTplSeg

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, A.11; stage S-E12e, track L-circ).

/-!
# The replay template of a segment's `shiftMask` (revision 4.1, B-12)

A segment's `shiftMask` is `Rev4.shiftSegI τL r` (`FRSegTarget4`): on the operand `τL = τ ‖ L`
(entries `0 … 17` the point, `18 … 35` the bits of the last block `L`) and the 18 block coordinates
`r`, the triple `(eq(τ, r), shift(τ, r) + [L + 1 < 2^18]·eq(τ, L)·eq(r, L + 1), eq(r, 0))`.
`FRSegTarget4` is downstream of this module, so the value is a copy, **`segMaskV`**
(`FRVIRTpl4Bridge.segMaskV_eq`: it is `shiftSegI`).

**`tplShiftSeg`** mirrors it gate for gate (≈ 300 rows):

* the bits `b_l = [τL₁₈₊ₗ = 1]` (`isOneG`: an inverse of `x − 1` and one product);
* `eq(τ, r)` (`facsG` and a product, as `tplEqPt`) and `shift(τ, r)` (`shiftG`, as `tplShiftEq`);
* `eq(τ, L)`: per coordinate `b τ + (1 − b)(1 − τ)` (`facsG`);
* the carries `c₀ = 1`, `c_{l+1} = c_l b_l` (`scanG`), the bits of `L + 1`,
  `d_l = b_l + c_l − 2c_{l+1}` (linear; `testBit_succ_carry`), and `eq(r, L + 1)` from them;
* the guard `[L + 1 < 2^18] = 1 − c₁₈` (`lt_two_pow_iff_carry`), and `eq(r, 0)`.

**`tplShiftSeg_ok`**: the gate equations give `segMaskV`.
-/

namespace FR
namespace Tpl
open Circ Finset

variable {e : Env}

/-! ## The value (a copy of `Rev4.shiftSegI`) -/

/-- The number whose bit `l < 18` is set iff entry `o + l` of `a` is `1` (`Rev4.lastAt`). -/
def lastAtV (a : Array F) (o : ℕ) : ℕ := ∑ l ∈ range 18, if a.getD (o + l) 0 = 1 then 2 ^ l else 0

/-- **A segment's `shiftMask`** (`Rev4.shiftSegI`, a copy). -/
def segMaskV (τL r : Array F) : F × F × F :=
  let τ := Array.ofFn (Impl.ptA 18 τL); let ρ := Array.ofFn (Impl.ptA 18 r)
  let L := lastAtV τL 18
  (eqPoint τ ρ,
   Impl.shiftEqI τ ρ + (if L + 1 < 2 ^ 18 then Impl.eqAtR (Impl.ptA 18 τL) L * Impl.eqAtR (Impl.ptA 18 r) (L + 1)
     else 0),
   Impl.eqAtR (Impl.ptA 18 r) 0)

/-! ## Bits -/

theorem sum_bitsP_lt (p : ℕ → Prop) [DecidablePred p] : ∀ n, (∑ k ∈ range n, if p k then 2 ^ k else 0) < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, pow_succ]; have := sum_bitsP_lt p n; split_ifs <;> omega

theorem testBit_sum_bitsP (p : ℕ → Prop) [DecidablePred p] : ∀ n j,
    (∑ k ∈ range n, if p k then 2 ^ k else 0).testBit j = decide (j < n ∧ p j)
  | 0, j => by simp
  | n + 1, j => by
    have e : (∑ k ∈ range (n + 1), if p k then 2 ^ k else 0) =
        2 ^ n * (if p n then 1 else 0) + ∑ k ∈ range n, if p k then 2 ^ k else 0 := by
      rw [sum_range_succ]; split_ifs <;> ring
    rw [e, Nat.testBit_two_pow_mul_add _ (sum_bitsP_lt p n), testBit_sum_bitsP p n]
    by_cases h : j < n
    · rw [if_pos h]; simp [h, show j < n + 1 by omega]
    · rw [if_neg h]
      obtain ⟨d, rfl⟩ : ∃ d, j = n + d := ⟨j - n, by omega⟩
      rw [Nat.add_sub_cancel_left]
      rcases d with _ | d
      · by_cases hp : p n <;> simp [hp]
      · by_cases hp : p n <;> simp [hp, Nat.testBit_succ] <;> omega

theorem lastAtV_lt (a : Array F) (o : ℕ) : lastAtV a o < 2 ^ 18 := sum_bitsP_lt _ 18

theorem testBit_lastAtV (a : Array F) (o : ℕ) {l : ℕ} (hl : l < 18) :
    (lastAtV a o).testBit l = decide (a.getD (o + l) 0 = 1) := by
  rw [lastAtV, testBit_sum_bitsP]; simp [hl]

/-- The low bits `0 … l − 1` all set. -/
def allLow (L l : ℕ) : Bool := (List.range l).all L.testBit

/-- **The bits of `L + 1` by the carry**: bit `l` of `L + 1` is bit `l` of `L` flipped iff the bits
below `l` are all set. -/
theorem testBit_succ_carry : ∀ (l L : ℕ), (L + 1).testBit l = (L.testBit l ^^ allLow L l)
  | 0, L => by
    simp only [allLow, List.range_zero, List.all_nil, Bool.xor_true, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one L with h | h <;> simp [h, Nat.add_mod]
  | l + 1, L => by
    have hr : allLow L (l + 1) = (L.testBit 0 && allLow (L / 2) l) := by
      simp only [allLow, List.range_succ_eq_map, List.all_cons, List.all_map]
      simp [Function.comp_def, Nat.testBit_succ]
    rw [Nat.testBit_succ, Nat.testBit_succ, hr, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one L with h | h
    · rw [show (L + 1) / 2 = L / 2 by omega]; simp [h]
    · rw [show (L + 1) / 2 = L / 2 + 1 by omega, testBit_succ_carry l (L / 2)]; simp [h]

/-- **`L + 1 < 2^n` iff not every bit of `L < 2^n` is set.** -/
theorem lt_two_pow_iff_carry {L n : ℕ} (hL : L < 2 ^ n) : L + 1 < 2 ^ n ↔ allLow L n = false := by
  constructor
  · intro h
    cases hc : allLow L n
    · rfl
    exfalso
    have : L + 1 = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.zero_testBit]
      by_cases hi : i < n
      · rw [testBit_succ_carry]
        have h1 : L.testBit i = true := by
          simp only [allLow, List.all_eq_true, List.mem_range] at hc; exact hc i hi
        have h2 : allLow L i = true := by
          simp only [allLow, List.all_eq_true, List.mem_range] at hc ⊢
          exact fun j hj => hc j (by omega)
        rw [h1, h2]; rfl
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))
    omega
  · intro hc
    by_contra h
    have : L = 2 ^ n - 1 := by omega
    subst this
    simp only [allLow, List.all_eq_false, List.mem_range, Nat.testBit_two_pow_sub_one] at hc
    obtain ⟨j, hj, h'⟩ := hc; simp [hj] at h'

/-! ## Pieces -/

/-- `[x = 1]`: `a = x − 1`, `i = a⁻¹` (an inverse, two locals), `s = a·i` (one product); the bit
is `1 − s`. -/
def isOneG (x : LinT) (k : ℕ) : List Gate × LinT :=
  ([.inv (x ++ C (-1)), .mul (x ++ C (-1)) (L k)], C 1 ++ sc (-1) (L (k + 2)))

theorem isOneG_ev (h1 : e.one = 1) (x : LinT) (k : ℕ) (h : Eqns e (isOneG x k).1 k) :
    (isOneG x k).2.ev e = if x.ev e = 1 then 1 else 0 := by
  simp only [isOneG, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
  obtain ⟨hi, hm⟩ := h
  simp only [isOneG, ev_append, ev_C, ev_sc, ev_L, h1, hm, hi]
  split_ifs with hx
  · simp [hx]
  · rw [mul_inv_cancel₀ (by intro h0; apply hx; linear_combination h0)]; ring

/-- `isOneG` over a list, three locals each. -/
def isOnesG : List LinT → ℕ → List Gate × List LinT
  | [], _ => ([], [])
  | x :: xs, k => let r := isOnesG xs (k + 3); ((isOneG x k).1 ++ r.1, (isOneG x k).2 :: r.2)

theorem isOnesG_ev (h1 : e.one = 1) : ∀ (xs : List LinT) (k : ℕ), Eqns e (isOnesG xs k).1 k →
    (isOnesG xs k).2.map (LinT.ev e) = xs.map fun x => if x.ev e = 1 then 1 else 0
  | [], _, _ => rfl
  | x :: xs, k, h => by
    simp only [isOnesG, Eqns.append] at h
    have hn : nlocs (isOneG x k).1 = 3 := rfl
    rw [hn] at h
    simp only [isOnesG, List.map_cons, isOneG_ev h1 x k h.1, isOnesG_ev h1 xs (k + 3) h.2]

/-- Per pair `(x, y)`: the product `t = x·y` (one row), the factor `x y + (1 − x)(1 − y)`. -/
def facsG : List (LinT × LinT) → ℕ → List Gate × List LinT
  | [], _ => ([], [])
  | p :: ps, k => let r := facsG ps (k + 1); (.mul p.1 p.2 :: r.1, eqFac p.1 p.2 (L k) :: r.2)

theorem facsG_ev (h1 : e.one = 1) : ∀ (ps : List (LinT × LinT)) (k : ℕ), Eqns e (facsG ps k).1 k →
    (facsG ps k).2.map (LinT.ev e) =
      ps.map fun p => p.1.ev e * p.2.ev e + (1 - p.1.ev e) * (1 - p.2.ev e)
  | [], _, _ => rfl
  | p :: ps, k, h => by
    simp only [facsG, Eqns.cons, Gate.nloc, Gate.Eqn] at h
    simp only [facsG, List.map_cons, facsG_ev h1 ps (k + 1) h.2,
      eqFac_ev h1 p.1 p.2 (L k) (by rw [ev_L]; exact h.1)]

theorem prod_range_list {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).prod = ∏ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_range_list f n,
      prod_range_succ]; simp

/-- **`eq(x, c)` at a constant index** over `n` coordinate forms: one product per coordinate. -/
def eqAtG (n : ℕ) (x : ℕ → LinT) (c k : ℕ) : List Gate × LinT :=
  prodG (C 1) ((List.range n).map fun l => if c.testBit l then x l else C 1 ++ sc (-1) (x l)) k

theorem eqAtG_ev (h1 : e.one = 1) (n : ℕ) (x : ℕ → LinT) (c k : ℕ) (h : Eqns e (eqAtG n x c k).1 k) :
    (eqAtG n x c k).2.ev e = Impl.eqAtR (fun l : Fin n => (x l).ev e) c := by
  rw [eqAtG, prodG_ev _ _ _ h, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F), Impl.eqAtR,
    Fin.prod_univ_eq_prod_range (fun l => if c.testBit l then (x l).ev e else 1 - (x l).ev e)]
  apply Finset.prod_congr rfl
  intro l _
  simp only [Function.comp_apply]
  split_ifs <;> simp [h1, sub_eq_add_neg]

/-! ## The template -/

/-- The point's coordinates `τL₀ … τL₁₇`, the bit entries `τL₁₈ … τL₃₅`, `r₀ … r₁₇`. -/
def sτ (n : ℕ) : List LinT := (List.range 18).map (cT n)
def sB (n : ℕ) : List LinT := (List.range 18).map fun l => cT n (18 + l)
def sr (n m : ℕ) : List LinT := (List.range 18).map (cR n m)

/-- **The segment's `shiftMask`** for `τL : AF n`, `r : AF m`, its locals from `k`: the gates and
the three outputs. -/
def segG (n m k : ℕ) : List Gate × List LinT :=
  let B := isOnesG (sB n) k
  let k1 := k + nlocs B.1
  let E := facsG ((List.range 18).map fun l => (cT n l, cR n m l)) k1
  let k2 := k1 + nlocs E.1
  let Ep := prodG (C 1) E.2 k2
  let k3 := k2 + nlocs Ep.1
  let S := shiftG (sτ n) (sr n m) k3
  let k4 := k3 + nlocs S.1
  let T := facsG ((List.range 18).map fun l => (B.2.getD l [], cT n l)) k4
  let k5 := k4 + nlocs T.1
  let Tp := prodG (C 1) T.2 k5
  let k6 := k5 + nlocs Tp.1
  let Cc := scanG (C 1) B.2 k6
  let k7 := k6 + nlocs Cc.1
  let D := facsG ((List.range 18).map fun l =>
    (B.2.getD l [] ++ Cc.2.getD l [] ++ sc (-2) (Cc.2.getD (l + 1) []), cR n m l)) k7
  let k8 := k7 + nlocs D.1
  let Dp := prodG (C 1) D.2 k8
  let k9 := k8 + nlocs Dp.1
  let Z := eqAtG 18 (cR n m) 0 k9
  let k10 := k9 + nlocs Z.1
  let gs := B.1 ++ (E.1 ++ (Ep.1 ++ (S.1 ++ (T.1 ++ (Tp.1 ++ (Cc.1 ++ (D.1 ++ (Dp.1 ++ (Z.1 ++
      [.mul (C 1 ++ sc (-1) (Cc.2.getD 18 [])) Tp.2, .mul (L k10) Dp.2])))))))))
  (gs, [Ep.2, S.2.2 ++ L (k10 + 1), Z.2])

/-- **The template** (locals from `0`). -/
def tplShiftSeg (n m : ℕ) : Tpl := ⟨(segG n m 0).1, (segG n m 0).2⟩

/-! ## Correctness -/

/-- `0/1` of a Boolean. -/
def bv (b : Bool) : F := if b then 1 else 0

theorem getD_ofFn18 (a : Array F) {v : ℕ} (hv : v < 18) :
    (Array.ofFn (Impl.ptA 18 a)).getD v 0 = a.getD v 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hv]; rfl

theorem toList_ofFn18 (a : Array F) :
    (Array.ofFn (Impl.ptA 18 a)).toList = (List.range 18).map fun l => a.getD l 0 :=
  List.ext_getElem (by simp) fun i _ _ => by
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range, Impl.ptA]

/-- The running products' entries: `(scanl (·*·) a xs)[l] = a · Π_{j<l} xs_j`. -/
theorem scanl_getD : ∀ (xs : List F) (a : F) (l : ℕ), l ≤ xs.length →
    (List.scanl (· * ·) a xs).getD l 0 = a * ((xs.take l).prod)
  | [], a, l, h => by simp at h; subst h; simp
  | x :: xs, a, 0, _ => by simp
  | x :: xs, a, l + 1, h => by
    simp only [List.scanl_cons, List.getD_cons_succ, List.take_succ_cons, List.prod_cons]
    rw [scanl_getD xs (a * x) l (by simpa using h)]; ring

theorem prod_bv_take (β : ℕ → Bool) {l : ℕ} (hl : l ≤ 18) :
    (((List.range 18).map fun j => bv (β j)).take l).prod = bv ((List.range l).all β) := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left hl]
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.all_append]
    cases (List.range l).all β <;> cases β l <;> simp [bv]

section Proof
variable {τL r : Array F} (hi : InpIs e (τL.toList ++ r.toList))
include hi

set_option maxHeartbeats 1000000 in
/-- **The segment template computes `segMaskV`.** -/
theorem tplShiftSeg_ok (h1 : e.one = 1) (h : Eqns e (tplShiftSeg τL.size r.size).gates 0) :
    (tplShiftSeg τL.size r.size).outs.map (LinT.ev e) =
      encV (.f (segMaskV τL r).1) ++ encV (.f (segMaskV τL r).2.1) ++ encV (.f (segMaskV τL r).2.2) := by
  have vτ : ∀ l, (cT τL.size l).ev e = τL.getD l 0 := cT_ev hi
  have vr : ∀ l, (cR τL.size r.size l).ev e = r.getD l 0 := cR_ev hi
  have hLlt : lastAtV τL 18 < 2 ^ 18 := lastAtV_lt τL 18
  have hbit : ∀ l < 18, bv ((lastAtV τL 18).testBit l) = if τL.getD (18 + l) 0 = 1 then 1 else 0 :=
    fun l hl => by rw [testBit_lastAtV τL 18 hl]; by_cases hx : τL.getD (18 + l) 0 = 1 <;> simp [hx, bv]
  simp only [tplShiftSeg, segG, Eqns.append] at h ⊢
  obtain ⟨hB, hE, hEp, hS, hT, hTp, hC, hD, hDp, hZ, hL⟩ := h
  simp only [Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at hL
  obtain ⟨hL1, hL2⟩ := hL
  simp only [segMaskV, List.map_cons, List.map_nil, encV, List.cons_append, List.nil_append, ev_append, ev_L,
    hL2, hL1, ev_sc, ev_C, h1]
  generalize lastAtV τL 18 = Lv at hLlt hbit ⊢
  have hbig : ∀ l, 18 ≤ l → Lv.testBit l = false := fun l hl =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hLlt (Nat.pow_le_pow_right (by norm_num) hl))
  -- the bits
  have vB := isOnesG_ev h1 _ _ hB
  have bBmap : (isOnesG (sB τL.size) 0).2.map (LinT.ev e) =
      (List.range 18).map fun l => bv (Lv.testBit l) := by
    rw [vB, sB, List.map_map]
    exact List.map_congr_left fun l hl => by
      rw [Function.comp_apply, vτ, hbit l (List.mem_range.1 hl)]
  have bB : ∀ l, ((isOnesG (sB τL.size) 0).2.getD l []).ev e = bv (Lv.testBit l) := fun l => by
    rw [getD_map_ev, bBmap]
    by_cases hl : l < 18
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]; rfl
    · rw [List.getD_eq_default _ _ (by simp; omega), hbig l (by omega)]; rfl
  -- the carries
  have cv : ∀ K, Eqns e (scanG (C 1) (isOnesG (sB τL.size) 0).2 K).1 K → ∀ l,
      ((scanG (C 1) (isOnesG (sB τL.size) 0).2 K).2.getD l []).ev e = bv (allLow Lv l) := by
    intro K hK l
    have oC := scanG_ev _ _ _ hK
    rw [bBmap, ev_C, h1, mul_one] at oC
    rw [getD_map_ev, oC]
    by_cases hl : l ≤ 18
    · rw [scanl_getD _ _ _ (by simpa using hl), one_mul, prod_bv_take _ hl]; rfl
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have : allLow Lv l = false := by
        simp only [allLow, List.all_eq_false, List.mem_range]
        exact ⟨18, by omega, by rw [hbig 18 le_rfl]; decide⟩
      rw [this]; rfl
  have cv' := cv _ hC
  -- the pieces' values
  have oE := prodG_ev _ _ _ hEp
  rw [facsG_ev h1 _ _ hE, ev_C, h1, one_mul, one_mul, List.map_map] at oE
  simp only [Function.comp_def, vτ, vr] at oE
  have oS := shiftG_ev h1 _ _ _ hS
  have mτ : (sτ τL.size).map (LinT.ev e) = (List.range 18).map fun x => τL.getD x 0 := by
    simp only [sτ, List.map_map, Function.comp_def, vτ]
  have mr : (sr τL.size r.size).map (LinT.ev e) = (List.range 18).map fun x => r.getD x 0 := by
    simp only [sr, List.map_map, Function.comp_def, vr]
  rw [mτ, mr] at oS
  have oT := prodG_ev _ _ _ hTp
  rw [facsG_ev h1 _ _ hT, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F)] at oT
  simp only [Function.comp_def, bB, vτ] at oT
  have oD := prodG_ev _ _ _ hDp
  rw [facsG_ev h1 _ _ hD, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F)] at oD
  simp only [Function.comp_def, ev_append, ev_sc, bB, cv', vr] at oD
  have oZ := eqAtG_ev h1 _ _ _ _ hZ
  simp only [vr] at oZ
  have oS2 := congrArg Prod.snd oS
  simp only at oS2
  rw [oE, oT, oD, oZ, cv', oS2]
  simp only [mul_one]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩
  · -- `eq(τ, r)`
    simp only [eqPoint, Array.size_ofFn]
    rw [← foldl_mul_range]
    refine List.foldl_ext _ _ _ fun acc v hv => ?_
    have hv := List.mem_range.1 hv
    simp only [getD_ofFn18 _ hv]
  · -- the masked successor
    rw [Impl.shiftEqI, toList_ofFn18, toList_ofFn18]
    congr 1
    have gT : ∏ i ∈ range 18, (bv (Lv.testBit i) * τL.getD i 0 + (1 - bv (Lv.testBit i)) * (1 - τL.getD i 0)) =
        Impl.eqAtR (Impl.ptA 18 τL) Lv := by
      rw [← Fin.prod_univ_eq_prod_range, Impl.eqAtR]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Impl.ptA]
      cases Lv.testBit l <;> simp [bv]
    have gD : ∏ i ∈ range 18, ((bv (Lv.testBit i) + bv (allLow Lv i) + -2 * bv (allLow Lv (i + 1))) * r.getD i 0 +
        (1 - (bv (Lv.testBit i) + bv (allLow Lv i) + -2 * bv (allLow Lv (i + 1)))) * (1 - r.getD i 0)) =
        Impl.eqAtR (Impl.ptA 18 r) (Lv + 1) := by
      rw [← Fin.prod_univ_eq_prod_range, Impl.eqAtR]
      refine Finset.prod_congr rfl fun l _ => ?_
      simp only [Impl.ptA, testBit_succ_carry]
      have ha : allLow Lv (l + 1) = (allLow Lv l && Lv.testBit l) := by
        simp [allLow, List.range_succ, List.all_append]
      rw [ha]
      cases Lv.testBit l <;> cases allLow Lv l <;> simp [bv] <;> ring
    rw [gT, gD]
    have hg := lt_two_pow_iff_carry hLlt
    by_cases hc : Lv + 1 < 2 ^ 18
    · rw [if_pos hc, hg.1 hc]; simp [bv]
    · rw [if_neg hc]
      have : allLow Lv 18 = true := by
        cases h' : allLow Lv 18
        · exact absurd (hg.2 h') hc
        · rfl
      rw [this]; simp [bv, h1]
  · -- `eq(r, 0)`
    rfl

end Proof

/-! ## Controls -/

/-- (+) Three outputs; the instance reads `τL` (36) then `r` (18). -/
theorem tplShiftSeg_outs (n m : ℕ) : (tplShiftSeg n m).outs.length = 3 := rfl

/-- (+) The carry rule on `L = 5` (`101 → 110`); (−) it is not the plain bit (bit 1 flips). -/
theorem carry_ctl : (allLow 5 1, (5 + 1).testBit 1) = (true, true) ∧ (5 : ℕ).testBit 1 = false := by
  decide

/-- (+) `L + 1 < 2^n` fails exactly at `L = 2^n − 1` (all bits set): at `n = 3`, `L = 7` and `L = 6`. -/
theorem guard_ctl : allLow 7 3 = true ∧ allLow 6 3 = false := by decide

end Tpl
end FR

end G6_FRVIRTplSeg
