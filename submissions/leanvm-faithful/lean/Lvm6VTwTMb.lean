-- New for lvm6 (WP-TWT): the fast twin of Y1's mini-bus at `E2` (`miniBusLProg6`): the multi-draw group
-- (`e2SampleN`), the GKR walk, the bus phase, and the three claims with the bus result, the forms and the fixed
-- columns' extensions in the word field (`mleFixF`: one `eq` table).
import Lvm6VTwX
import Lvm6VTwTTy

/-!
# Fast twins: the mini-bus

* `fE2SampleN`, `tw_e2SampleN`; `fGkrStep`, `fGkrLayers`, `fVerifyGkr`, **`fLvmBus`**, **`tw_lvmBus`**.
* The bus result in the word field: `FormF`, `leafFormF`, `sideBlocksF`, `stackBlocksF` (`map_mergeSort`),
  `sidesF`, `busFinalF`, `coefF`, **`mleFixF`** (`Σ_{x<2^τ} eq(pt, x)·f(x)` off `eqKernelAF pt`), `constF`,
  `mbPartsF`, `mbValueF`; each with its decoding lemma.
* `mbClaimF` (a sum claim on the stack as an `FClaim`), `mbClaimsF`; **`fMiniBus6`**, **`tw_miniBus6`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V Lvm.M3
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.Mb
open Finset

/-- A block's placement on the stack. -/
abbrev Plc : Type := LeanVM.Protocol.Verifier.Placement

/-! ## The multi-draw group -/

/-- **Fast `e2SampleN g n`**: the nonce, the first draw with its proof of work, `n − 1` more draws. -/
def fE2SampleN (g : ℕ) : ℕ → VF (List FE2)
  | 0 => VF.pure []
  | n + 1 => VF.bind fRead fun _ => VF.bind fSample fun a => VF.guard (pw g (answerBits a))
      (VF.bind (fSamples n) fun as => VF.pure ((a :: as).map fe2OfAns))

theorem tw_e2SampleN (g : ℕ) : ∀ n, TwinF (List.map FE2.toE2) (e2SampleN g n) (fE2SampleN g n)
  | 0 => tw_pure rfl
  | n + 1 => by
    unfold e2SampleN fE2SampleN
    refine tw_skipRead (tw_sample fun a => tw_guard _ _ (powOK_iff g a) ?_)
    refine tw_bindR (twin_samples n) fun π as cs h tr => ?_
    subst h
    refine tw_pure ?_ π tr
    simp only [List.map_cons, List.map_map, Function.comp_def, e2OfE_chal]

/-! ## The GKR walk -/

/-- The walk's state in the word field: values, point. -/
abbrev GkrF : Type := List FE2 × List FE2

/-- Its decoding. -/
def gD (s : GkrF) : GkrStateG := ⟨s.1.map FE2.toE2, s.2.map FE2.toE2⟩

/-- **Fast `gkrStepG gy step`.** -/
def fGkrStep (gy step : ℕ) (s : GkrF) : VF GkrF :=
  VF.bind (fE2Sample gLam) fun lam =>
  VF.bind (fSumcheck gRd (polyEvalF s.1 lam) (2 ^ step + 1) (s.2.map some)) fun rf =>
  VF.bind (fE2Reads (2 ^ step)) fun c0 => VF.bind (fE2Reads (2 ^ step)) fun c1 =>
  VF.bind (fE2Reads (2 ^ step)) fun c2 =>
  VF.guard (decide (rf.2 = polyEvalF ([c0, c1, c2].map prodF) lam))
    (VF.bind (fE2SampleN gy step) fun y => VF.pure ([c0, c1, c2].map (multilinearEvalF · y), y ++ rf.1))

theorem map_some_toE2 (l : List FE2) : (l.map FE2.toE2).map some = (l.map some).map (Option.map FE2.toE2) := by
  simp [List.map_map, Function.comp_def]

theorem tw_gkrStep (gy step : ℕ) (s : GkrF) : TwinF gD (gkrStepG gy step (gD s)) (fGkrStep gy step s) := by
  unfold gkrStepG fGkrStep
  refine tw_bind (tw_e2Sample _) fun lam => ?_
  beta_reduce
  rw [show (gD s).values = s.1.map FE2.toE2 from rfl, show (gD s).point = s.2.map FE2.toE2 from rfl,
    ← toE2_polyEvalF, map_some_toE2]
  refine tw_bind (tw_sumcheck _ _ _ _) fun rf => tw_bind (tw_e2Reads _) fun c0 => tw_bind (tw_e2Reads _) fun c1 =>
    tw_bind (tw_e2Reads _) fun c2 => tw_guard _ _ ?_ (tw_bind (tw_e2SampleN _ _) fun y => tw_pure ?_)
  · rw [show [c0.map FE2.toE2, c1.map FE2.toE2, c2.map FE2.toE2].map prodF =
        ([c0, c1, c2].map prodF).map FE2.toE2 by simp only [List.map_cons, List.map_nil, ← coe_tE, map_prodF],
      ← toE2_polyEvalF]
    exact toE2_eq_iff _ _
  · simp only [gD, scD, List.map_cons, List.map_nil, List.map_append, toE2_multilinearEvalF]

/-- **Fast `gkrLayersG`.** -/
def fGkrLayers : ℕ → GkrF → VF GkrF
  | 0, s => VF.pure s
  | 1, s => fGkrStep gYl 1 s
  | n + 2, s =>
    if n % 2 = 1 then VF.bind (fGkrStep gY 1 s) fun s' => fGkrLayers (n + 1) s'
    else VF.bind (fGkrStep (if n = 0 then gYl else gY) 2 s) fun s' => fGkrLayers n s'

theorem tw_gkrLayers : ∀ (n : ℕ) (s : GkrF), TwinF gD (gkrLayersG n (gD s)) (fGkrLayers n s)
  | 0, _ => tw_pure rfl
  | 1, s => tw_gkrStep _ _ s
  | n + 2, s => by
    unfold gkrLayersG fGkrLayers
    by_cases h : n % 2 = 1
    · simp only [h, if_true]
      exact tw_bind (tw_gkrStep _ _ s) fun s' => tw_gkrLayers (n + 1) s'
    · simp only [h, if_false]
      exact tw_bind (tw_gkrStep _ _ s) fun s' => tw_gkrLayers n s'

/-- **Fast `verifyGkrGrandProductsG μ`.** -/
def fVerifyGkr (μ : ℕ) : VF (FE2 × List FE2 × List FE2) :=
  VF.bind fReadF fun sh => VF.bind fReadF fun cnt =>
  VF.bind (fGkrLayers μ ([sh, sh, cnt], [])) fun s => VF.pure (cnt, s.2, s.1)

/-- The decoding of the walk's result. -/
def vD (r : FE2 × List FE2 × List FE2) : E2 × List E2 × List E2 :=
  (FE2.toE2 r.1, r.2.1.map FE2.toE2, r.2.2.map FE2.toE2)

theorem tw_verifyGkr (μ : ℕ) : TwinF vD (verifyGkrGrandProductsG μ) (fVerifyGkr μ) := by
  unfold verifyGkrGrandProductsG fVerifyGkr
  exact tw_bind tw_e2Read fun sh => tw_bind tw_e2Read fun cnt =>
    tw_bind (tw_gkrLayers μ ([sh, sh, cnt], [])) fun s => tw_pure rfl

/-- What the bus phase read, in the word field. -/
structure LBusF where
  alphas : List FE2
  beta : FE2
  point : List FE2
  values : List FE2

/-- Its decoding. -/
def lbD (b : LBusF) : LBusG := ⟨b.alphas.map FE2.toE2, FE2.toE2 b.beta, b.point.map FE2.toE2, b.values.map FE2.toE2⟩

/-- **Fast `lvmBusProgG μ`.** -/
def fLvmBus (μ : ℕ) : VF LBusF :=
  VF.bind (fE2SampleN gAB 5) fun ab => VF.bind (fVerifyGkr μ) fun r =>
  VF.guard (decide (r.1 ≠ 0)) (VF.pure ⟨ab.take 4, ab.getD 4 0, r.2.1, r.2.2⟩)

theorem tw_lvmBus (μ : ℕ) : TwinF lbD (lvmBusProgG μ) (fLvmBus μ) := by
  unfold lvmBusProgG fLvmBus
  refine tw_bind (tw_e2SampleN _ _) fun ab => tw_bind (tw_verifyGkr μ) fun r => tw_guard _ _ ?_ (tw_pure ?_)
  · simp only [vD, decide_eq_true_eq, ne_eq]
    rw [← toE2_zero', FE2.toE2_injective.eq_iff]
  · simp only [lbD, vD, List.map_take, toE2_getD]

/-! ## Forms in the word field -/

/-- A form in the word field: its terms. -/
abbrev FormF : Type := List (List ℕ × FE2)

/-- Its decoding. -/
def formD (f : FormF) : FormG := ⟨f.map fun t => (t.1, FE2.toE2 t.2)⟩

theorem toE2_mulK_kG (w : FE2) (k : FK) : FE2.toE2 (FE2.mulK w k) = FE2.toE2 w * kG k := by
  rw [FE2.toE2_mulK, ← FE2.toE2_ofK]; rfl

/-- `cpolyFormG`. -/
def cpolyFormF (w : FE2) (P : CPoly) : FormF := P.map fun m => (m.2, FE2.mulK w m.1)

theorem formD_cpolyFormF (w : FE2) (P : CPoly) : formD (cpolyFormF w P) = cpolyFormG (FE2.toE2 w) P := by
  simp only [formD, cpolyFormF, cpolyFormG, List.map_map, Function.comp_def, toE2_mulK_kG]

/-- `formSumG`. -/
def formSumF (fs : List FormF) : FormF := fs.flatMap id

theorem formD_formSumF (fs : List FormF) : formD (formSumF fs) = formSumG (fs.map formD) := by
  simp only [formD, formSumF, formSumG, List.map_flatMap, List.flatMap_map, id]

/-- `leafFormG`. -/
def leafFormF (eqα : List FE2) (β : FE2) (k : Key) (cnt : CPoly) : FormF :=
  formSumF ([[([], β + eqα.getD 0 0 * FE2.ofK k.sep)], cpolyFormF (eqα.getD 1 0) k.addr,
    cpolyFormF (eqα.getD 2 0) cnt] ++ k.val.zipIdx.map fun (P, l) => cpolyFormF (eqα.getD (3 + l) 0) P)

theorem formD_leafFormF (eqα : List FE2) (β : FE2) (k : Key) (cnt : CPoly) :
    formD (leafFormF eqα β k cnt) = leafFormG (eqα.map FE2.toE2) (FE2.toE2 β) k cnt := by
  simp only [leafFormF, leafFormG, formD_formSumF, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, formD_cpolyFormF, ← toE2_getD]
  congr 2
  simp only [formD, List.map_cons, List.map_nil, toE2_add', toE2_mul']
  rfl

/-- A block of a bus side in the word field. -/
structure VBlockF where
  tab : ℕ
  κ : ℕ
  form : FormF

/-- Its decoding. -/
def blkD (b : VBlockF) : VBlockG := ⟨b.tab, b.κ, formD b.form⟩

/-- `sideBlocksG`. -/
def sideBlocksF (tabs : List Tab) (eqα : List FE2) (β : FE2) : List (List VBlockF) :=
  let ts := tabs.zipIdx
  [ts.flatMap fun (t, j) =>
      t.reads.map (fun r => ⟨j, t.τ, leafFormF eqα β r.1 [(Lvm.FK.x, [r.2])]⟩) ++
        t.seeds.map (fun s => ⟨j, t.τ, leafFormF eqα β s.1 (CPoly.const 1)⟩),
   ts.flatMap fun (t, j) =>
      t.reads.map (fun r => ⟨j, t.τ, leafFormF eqα β r.1 (CPoly.var r.2)⟩) ++
        t.seeds.map (fun s => ⟨j, t.τ, leafFormF eqα β s.1 (CPoly.var s.2)⟩),
   ts.flatMap fun (t, j) => t.counts.map fun c => ⟨j, t.τ, [([c.val], 1)]⟩]

theorem sideBlocksF_dec (tabs : List Tab) (eqα : List FE2) (β : FE2) :
    (sideBlocksF tabs eqα β).map (·.map blkD) = sideBlocksG tabs (eqα.map FE2.toE2) (FE2.toE2 β) := by
  simp only [sideBlocksF, sideBlocksG, List.map_cons, List.map_nil, List.map_flatMap, List.map_append,
    List.map_map, Function.comp_def, blkD, formD_leafFormF]
  simp only [formD, List.map_cons, List.map_nil, toE2_one']

/-- `stackBlocksG`'s step. -/
def stackStepF (acc : List (VBlockF × ℕ) × ℕ) (b : VBlockF) : List (VBlockF × ℕ) × ℕ :=
  (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ)

/-- `stackBlocksG`. -/
def stackBlocksF (bs : List VBlockF) : List (VBlockF × ℕ) :=
  ((bs.mergeSort fun a b => decide (b.κ ≤ a.κ)).foldl stackStepF ([], 0)).1

theorem stack_foldl (l : List VBlockF) : ∀ (a : List (VBlockF × ℕ)) (n : ℕ),
    ((l.foldl stackStepF (a, n)).1).map (fun p => (blkD p.1, p.2)) =
      ((l.map blkD).foldl (fun (acc : List (VBlockG × ℕ) × ℕ) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
        (a.map (fun p => (blkD p.1, p.2)), n)).1 := by
  induction l with
  | nil => intro a n; rfl
  | cons b l ih =>
    intro a n
    simp only [List.foldl_cons, List.map_cons]
    rw [show stackStepF (a, n) b = (a ++ [(b, n)], n + 2 ^ b.κ) from rfl, ih]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rfl

theorem stackBlocksF_dec (bs : List VBlockF) :
    (stackBlocksF bs).map (fun p => (blkD p.1, p.2)) = stackBlocksG (bs.map blkD) := by
  unfold stackBlocksF stackBlocksG
  rw [stack_foldl, List.map_mergeSort (r := fun (a b : VBlockF) => decide (b.κ ≤ a.κ))
    (s := fun (a b : VBlockG) => decide (b.κ ≤ a.κ))
    (fun _ _ _ _ => rfl)]
  rfl

/-- `eqAboveG` in the word field. -/
def eqAboveF (p : Plc) (pt : List FE2) : FE2 :=
  eqEvalF (selPtF (p.index >>> p.variableCount) (pt.length - p.variableCount)) (pt.drop p.variableCount)

theorem map_selPtF {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (s n : ℕ) :
    (selPtF s n : List F).map φ = selPtF s n := by
  simp only [selPtF, List.map_map, Function.comp_def, apply_ite (⇑φ), map_one, map_zero]

theorem toE2_eqEvalF (a b : List FE2) : FE2.toE2 (eqEvalF a b) = eqEvalF (a.map FE2.toE2) (b.map FE2.toE2) :=
  map_eqEvalF tE a b

theorem toE2_eqAboveF (p : Plc) (pt : List FE2) :
    FE2.toE2 (eqAboveF p pt) = eqAboveG p (pt.map FE2.toE2) := by
  simp only [eqAboveF, eqAboveG, ← coe_tE, map_eqEvalF, map_selPtF, List.length_map, List.map_drop]

/-- `sidesG`. -/
def sidesF (tabs : List Tab) (alphas : List FE2) (β : FE2) (ζ : List FE2) : List (List (VBlockF × FE2)) :=
  (sideBlocksF tabs (eqKernelF alphas) β).map fun bs =>
    (stackBlocksF bs).map fun (b, off) => (b, eqAboveF ⟨b.κ, off⟩ ζ)

/-- A weighted block's decoding. -/
def bwD (bw : VBlockF × FE2) : VBlockG × E2 := (blkD bw.1, FE2.toE2 bw.2)

theorem sidesF_dec (tabs : List Tab) (alphas : List FE2) (β : FE2) (ζ : List FE2) :
    (sidesF tabs alphas β ζ).map (·.map bwD) =
      sidesG tabs (alphas.map FE2.toE2) (FE2.toE2 β) (ζ.map FE2.toE2) := by
  unfold sidesF sidesG
  rw [show eqKernelF (alphas.map FE2.toE2) = (eqKernelF alphas).map FE2.toE2 by rw [← coe_tE, map_eqKernelF],
    ← sideBlocksF_dec]
  simp only [List.map_map]
  refine List.map_congr_left fun bs _ => ?_
  simp only [Function.comp_apply, List.map_map]
  rw [← stackBlocksF_dec, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, bwD, toE2_eqAboveF]
  rfl

/-- `bucketG`. -/
def bucketF (s : List (VBlockF × FE2)) (j : ℕ) : FormF :=
  ((s.filter fun bw => bw.1.tab == j).reverse).flatMap fun bw => bw.1.form.map fun t => (t.1, bw.2 * t.2)

theorem bucketF_dec (s : List (VBlockF × FE2)) (j : ℕ) : formD (bucketF s j) = ⟨bucketG (s.map bwD) j⟩ := by
  simp only [formD, bucketF, bucketG, List.filter_map, List.map_flatMap, List.map_map, Function.comp_def, bwD, blkD,
    toE2_mul']
  rw [← List.map_reverse, List.flatMap_map]
  congr 1
  refine congrArg (fun g => List.flatMap g _) (funext fun a => ?_)
  simp only [bwD, blkD, formD, List.map_map, Function.comp_def]

/-- The bus result in the word field. -/
structure BusResF where
  point : List FE2
  forms : List (List FormF)
  totals : List FE2

/-- Its decoding. -/
def resD (r : BusResF) : BusResG := ⟨r.point.map FE2.toE2, r.forms.map (·.map formD), r.totals.map FE2.toE2⟩

/-- **`busFinalG` in the word field.** -/
def busFinalF (tabs : List Tab) (alphas : List FE2) (β : FE2) (ζ values : List FE2) : BusResF :=
  let sides := sidesF tabs alphas β ζ
  ⟨ζ, (List.range tabs.length).map (fun j => sides.map fun s => bucketF s j),
    (List.range 3).map fun k => values.getD k 0 + 1 + sumF ((sides.getD k []).map (·.2))⟩

theorem getD_map_nil {α β : Type} (L : List (List α)) (f : α → β) (k : ℕ) :
    (L.map (·.map f)).getD k [] = (L.getD k []).map f := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[k]? <;> rfl

theorem resD_busFinalF (tabs : List Tab) (alphas : List FE2) (β : FE2) (ζ values : List FE2) :
    resD (busFinalF tabs alphas β ζ values) =
      busFinalG tabs (alphas.map FE2.toE2) (FE2.toE2 β) (ζ.map FE2.toE2) (values.map FE2.toE2) := by
  unfold busFinalF busFinalG resD
  rw [← sidesF_dec]
  simp only [List.map_map, Function.comp_def, BusResG.mk.injEq, true_and]
  constructor
  · refine List.map_congr_left fun j _ => ?_
    simp only [List.map_map, Function.comp_def, bucketF_dec]
  · refine List.map_congr_left fun k _ => ?_
    rw [getD_map_nil, List.map_map]
    simp only [toE2_add', toE2_getD, toE2_one', toE2_sumF, List.map_map, Function.comp_def, bwD]

/-! ## The claims' parts and values -/

/-- `coefG`. -/
def coefF (f : FormF) (c : ℕ) : FE2 := sumF ((f.filter fun m => m.1 == [c]).map (·.2))

theorem toE2_coefF (f : FormF) (c : ℕ) : FE2.toE2 (coefF f c) = coefG (formD f) c := by
  simp only [coefF, coefG, formD, toE2_sumF, List.filter_map, List.map_map, Function.comp_def]
  try rfl

/-- **A fixed column's extension in the word field**: `Σ_{x<2^τ} eq(pt, x)·f(x)`, `eq(pt, ·)` off one table. -/
def mleFixF (τ : ℕ) (f : ℕ → FK) (pt : List FE2) : FE2 :=
  let t := eqKernelAF pt
  let n := 2 ^ pt.length
  sumF ((List.range (2 ^ τ)).map fun x => FE2.mulK (if x < n then t.getD x 0 else eqAtF pt x) (f x))

theorem toE2_mleFixF (τ : ℕ) (f : ℕ → FK) (pt : List FE2) :
    FE2.toE2 (mleFixF τ f pt) = mleFixG τ f (pt.map FE2.toE2) := by
  unfold mleFixF mleFixG
  rw [toE2_sumF, sumF_eq_sum, List.map_map, lsumR]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, toE2_mulK_kG]
  congr 1
  split_ifs with h
  · rw [eqKernelAF_getD, if_pos h, toE2_eqAtF]
  · rw [toE2_eqAtF]

/-- `constG`. -/
def constF (t : Tab) (f : FormF) (pt : List FE2) : FE2 :=
  sumF (f.map fun m => match m.1 with
    | [] => m.2
    | [c] => match t.cols[c]? with
      | some (ColSrc.fix fc _) => m.2 * mleFixF t.τ fc pt
      | _ => 0
    | _ => 0)

theorem toE2_constF (t : Tab) (f : FormF) (pt : List FE2) :
    FE2.toE2 (constF t f pt) = constG t (formD f) (pt.map FE2.toE2) := by
  unfold constF constG formD
  rw [toE2_sumF, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp_apply]
  rcases m with ⟨l, v⟩
  match l with
  | [] => rfl
  | [c] =>
    simp only
    split
    · rename_i fc ev h
      rw [h, toE2_mul', toE2_mleFixF]
    · rename_i h
      split
      · rename_i fc ev h'; exact absurd h' (h fc ev)
      · rfl
  | _ :: _ :: _ => rfl

/-- `formG`. -/
def formF (r : BusResF) (j s : ℕ) : FormF := (r.forms.getD j []).getD s []

theorem formD_formF (r : BusResF) (j s : ℕ) : formD (formF r j s) = formG (resD r) j s := by
  unfold formF formG resD
  simp only [getD_map_nil]
  generalize r.forms.getD j [] = L
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[s]? <;> rfl

/-- A part's decoding. -/
def partD (p : FE2 × Plc × List FE2) : E2 × Plc × List E2 := (FE2.toE2 p.1, p.2.1, p.2.2.map FE2.toE2)

/-- `mbPartsG`. -/
def mbPartsF (tabs : List Tab) (r : BusResF) (s : ℕ) : List (FE2 × Plc × List FE2) :=
  tabs.zipIdx.flatMap fun (tj : Tab × ℕ) => (sideColsG tj.1 s).filterMap fun c => match tj.1.cols[c]? with
    | some (ColSrc.com _ off) => some (coefF (formF r tj.2 s) c, ⟨tj.1.τ, off⟩, r.point.take tj.1.τ)
    | _ => none

theorem mbPartsF_dec (tabs : List Tab) (r : BusResF) (s : ℕ) :
    (mbPartsF tabs r s).map partD = mbPartsG tabs (resD r) s := by
  unfold mbPartsF mbPartsG
  rw [List.map_flatMap]
  congr 1
  funext tj
  rw [List.map_filterMap]
  congr 1
  funext c
  split
  · rename_i rec off h
    rw [h]
    simp only [Option.map_some, partD, toE2_coefF, formD_formF, List.map_take]
    rfl
  · rename_i h
    split
    · rename_i rec off h'; exact absurd h' (h rec off)
    · rfl

/-- `mbValueG`. -/
def mbValueF (tabs : List Tab) (r : BusResF) (s : ℕ) : FE2 :=
  r.totals.getD s 0 + sumF (tabs.zipIdx.map fun (t, j) => constF t (formF r j s) (r.point.take t.τ))

theorem toE2_mbValueF (tabs : List Tab) (r : BusResF) (s : ℕ) :
    FE2.toE2 (mbValueF tabs r s) = mbValueG tabs (resD r) s := by
  unfold mbValueF mbValueG
  rw [toE2_add', toE2_getD, toE2_sumF, List.map_map]
  congr 2
  refine List.map_congr_left fun tj _ => ?_
  simp only [Function.comp_apply, toE2_constF, formD_formF, resD, List.map_take]

/-! ## The claims -/

/-- **A sum claim on the stack** (`(sumClaimG nu parts v).onStack`) as a fast claim. -/
def mbClaimF (nu : ℕ) (parts : List (FE2 × Plc × List FE2)) (v : FE2) : FClaim :=
  ⟨fun x => eqAboveF ⟨nu, 0⟩ x * sumF (parts.map fun p =>
    p.1 * eqAboveF p.2.1 (x.take nu) * eqEvalF p.2.2 ((x.take nu).take p.2.1.variableCount)), v⟩

theorem mbClaimF_dec (nu : ℕ) (parts : List (FE2 × Plc × List FE2)) (v : FE2) :
    (mbClaimF nu parts v).dec = (sumClaimG nu (parts.map partD) (FE2.toE2 v)).onStack := by
  simp only [FClaim.dec, mbClaimF, sumClaimG, BClaimG.onStack, Prod.mk.injEq, and_true]
  funext x
  simp only [toE2_mul', toE2_eqAboveF, map_toE2_ofE2, toE2_sumF, List.map_map, Function.comp_def, partD,
    List.map_take, toE2_eqEvalF, FE2.toE2_ofE2, List.map_id']

/-- **The three claims in the word field.** -/
def mbClaimsF (nu : ℕ) (tabs : List Tab) (b : LBusF) : List FClaim :=
  let r := busFinalF tabs b.alphas b.beta b.point b.values
  (List.range 3).map fun s => mbClaimF nu (mbPartsF tabs r s) (mbValueF tabs r s)

theorem mbClaimsF_dec (nu : ℕ) (tabs : List Tab) (b : LBusF) :
    (mbClaimsF nu tabs b).map FClaim.dec = (mbClaimsG nu tabs (lbD b)).map (·.onStack) := by
  unfold mbClaimsF mbClaimsG busResG
  simp only [List.map_map, Function.comp_def]
  refine List.map_congr_left fun s _ => ?_
  rw [mbClaimF_dec, mbPartsF_dec, toE2_mbValueF, resD_busFinalF]
  rfl

/-! ## The mini-bus phase -/

/-- **Fast `miniBusLProg6 L tabs μ`.** -/
def fMiniBus6 (L : Lay) (tabs : List Tab) (μ : ℕ) : VF (List FClaim) :=
  VF.bind (fLvmBus μ) fun b => VF.pure (mbClaimsF L.nuMain tabs b)

theorem tw_miniBus6 (L : Lay) (tabs : List Tab) (μ : ℕ) :
    TwinF (List.map FClaim.dec) (miniBusLProg6 L tabs μ) (fMiniBus6 L tabs μ) := by
  unfold miniBusLProg6 fMiniBus6
  exact tw_bind (tw_lvmBus μ) fun b => tw_pure (mbClaimsF_dec _ _ _)

end Lvm6.V
