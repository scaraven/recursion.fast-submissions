-- New for lvm6 (WP-TWT): fast twins of Y1's typed parts at `E2` (`zeroProgE`, `wireProgE`, `relayProgE`,
-- `accProgE`), under CD's layout (`TyLayOk`: `virt` and the relayout kernel as products of `eq`s, `virt_eq` and
-- `relayKern_eq`) and with `Φ_Q` off its table (`Lvm6VTwTPhi`).
import Lvm6VTwR
import Lvm6VTwTPhi
import Lvm6QDWire

/-!
# Fast twins: zerocheck, wiring, relayout, A23

* `tw_require` (a final `require`).
* **`tw_zero`**: `zeroProgE` (20 ground coordinates, 20 equality-mode rounds, `A, B, C`, the check).
* `virtF`, `toE2_virtF` (`virt_eq` in the word field: one `eq` table over 10 coordinates, the `PUB` words by `mulK`);
  **`tw_wire`** (with `|r_y| = 21` on the fast value).
* `kernF`, **`tw_relay`** (`relayKern_eq`: `eq(r_y^{≥19}, bs/2^19)·eqEval(r_y^{<19}, r)`, with `|r| = 19`).
* `lineF`, `hEvalF`, `yOwnF` and their maps; **`tw_acc`**: A23 with `Φ_Q` from any evaluator `ev` with
  `PhiOk ev Q lay` (`phiFast (mkPhiTab (entsE Q lay))` is one, `phiOk_mk`; `phiCov` with its check another).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V Lvm.Typed Lvm.Loop
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.Ty (TInst6 zeroProgE wireProgE relayProgE accProgE virtE relayKernE wBatchE wGE lineE hEvalE yOwnE
  PhiQE PhiQFE entsE gTau gZero gGamma gWire gKappa gT selBitsE phiVarsE relayRounds)
open Lvm6.QD (TyLayOk StreamRegs6 pubBase onesOf sflatBase)
open Finset

/-! ## A final check -/

theorem tw_require (c : Prop) [Decidable c] (fc : Bool) (hc : c ↔ fc = true) :
    TwinF (fun _ : Unit => ()) (VerifierProgram.require c) (VF.guard fc (VF.pure ())) := by
  intro π tr
  by_cases h : fc = true
  · have e : VerifierProgram.require c = pure () := by
      rw [VerifierProgram.require, if_pos (hc.mpr h)]; rfl
    rw [e]
    show Option.Rel _ (if fc then VF.pure () π tr else none) _
    rw [if_pos h]
    exact tw_pure (d := fun _ : Unit => ()) rfl π tr
  · have e : VerifierProgram.require c = VerifierProgram.fail := by
      rw [VerifierProgram.require, if_neg (fun h' => h (hc.mp h'))]
    rw [e, replayP_fail]
    show Option.Rel _ (if fc then VF.pure () π tr else none) none
    rw [if_neg h]
    exact Option.Rel.none

/-- `tw_guard` for any relation. -/
theorem tw_guardG {α β : Type} {R : ByteArray → β → α → Prop} (c : Prop) [Decidable c] (fc : Bool)
    (hc : c ↔ fc = true) {k : VerifierProgram α} {fk : VF β} (hk : Twin R k fk) :
    Twin R (VerifierProgram.require c >>= fun _ => k) (VF.guard fc fk) := by
  intro π tr
  by_cases h : fc = true
  · have e : (VerifierProgram.require c >>= fun _ => k) = k := by
      show (VerifierProgram.require c).bind _ = _
      rw [VerifierProgram.require, if_pos (hc.mpr h)]
      rfl
    rw [e]
    show Option.Rel _ (if fc then fk π tr else none) _
    rw [if_pos h]
    exact hk π tr
  · have e : (VerifierProgram.require c >>= fun _ => k) = VerifierProgram.fail := by
      show (VerifierProgram.require c).bind _ = _
      rw [VerifierProgram.require, if_neg (fun h' => h (hc.mp h'))]
      rfl
    rw [e, replayP_fail]
    show Option.Rel _ (if fc then fk π tr else none) none
    rw [if_neg h]
    exact Option.Rel.none

theorem lsumR {M : Type} [AddCommMonoid M] (f : ℕ → M) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, lsumR f n, sum_range_succ]; simp

theorem map_ofE2_toE2 (x : List FE2) : (x.map FE2.toE2).map FE2.ofE2 = x := by
  rw [List.map_map]; exact List.map_id'' (fun y => FE2.ofE2_toE2 y) x

theorem map_tofE2_toE2 (x : List FE2) : (x.map FE2.toE2).map Lvm.Typed.ofE2 = x := by
  rw [List.map_map]; exact List.map_id'' (fun _ => rfl) x

/-! ## Zerocheck -/

/-- **Fast `zeroProgE`.** -/
def fZero : VF (List FE2 × List FE2) :=
  VF.bind (fE2Samples gTau xVars) fun τ => VF.bind (fSumcheck gZero 0 3 (τ.map some)) fun rf =>
  VF.bind (fE2Reads 3) fun v =>
  VF.guard (decide (rf.2 = v.getD 0 0 * v.getD 1 0 + v.getD 2 0)) (VF.pure (rf.1, v))

/-- The decoding of a pair of lists. -/
def l2D (r : List FE2 × List FE2) : List E2 × List E2 := (r.1.map FE2.toE2, r.2.map FE2.toE2)

theorem tw_zero : TwinF l2D zeroProgE fZero := by
  unfold zeroProgE fZero
  refine tw_bind (tw_e2Samples _ _) fun τ => ?_
  have h := tw_sumcheck gZero 3 (τ.map some) 0
  rw [toE2_zero', List.map_map, show (Option.map FE2.toE2 ∘ some) = (some ∘ FE2.toE2) from rfl,
    ← List.map_map] at h
  refine tw_bind h fun rf => tw_bind (tw_e2Reads 3) fun v => tw_guard _ _ ?_ (tw_pure rfl)
  simp only [scD, ← toE2_getD, ← toE2_mul', ← toE2_add']
  exact toE2_eq_iff _ _

/-! ## Wiring -/

/-- `wBatchE` in the word field. -/
def wBatchF (γ : FE2) (v : List FE2) : FE2 := v.getD 0 0 + γ * v.getD 1 0 + γ ^ 2 * v.getD 2 0

/-- `wGE` in the word field. -/
def wGF (γ : FE2) (vs : List FE2) : FE2 := vs.getD 0 0 + γ * vs.getD 1 0 + γ ^ 2 * (vs.getD 2 0 + vs.getD 3 0)

theorem toE2_wBatchF (γ : FE2) (v : List FE2) : FE2.toE2 (wBatchF γ v) = wBatchE (FE2.toE2 γ) (v.map FE2.toE2) := by
  simp only [wBatchF, wBatchE, ← coe_tE, map_add, map_mul, map_pow, map_getD]

theorem toE2_wGF (γ : FE2) (v : List FE2) : FE2.toE2 (wGF γ v) = wGE (FE2.toE2 γ) (v.map FE2.toE2) := by
  simp only [wGF, wGE, ← coe_tE, map_add, map_mul, map_pow, map_getD]

/-- **`virt(r_y)` in the word field** (CD's layout): `eq(r_y^{≥10}, pb/2^10)·Σ_j eq(r_y^{<10}, j)·pw(pb + j)` plus
the `1` regions' selectors. -/
def virtF (Ti : TInst6) (pw : ℕ → FK) (ry : List FE2) : FE2 :=
  let pb := pubBase Ti
  let t := eqKernelAF (ry.take 10)
  eqAtF (ry.drop 10) (pb / 2 ^ 10) * sumF ((List.range (2 ^ 10)).map fun j => FE2.mulK (t.getD j 0) (pw (pb + j))) +
    sumF ((onesOf Ti).map fun R => eqAtF (ry.drop R.log) (R.base / 2 ^ R.log))

theorem toE2_virtF {Ti : TInst6} (hok : Ti.Ok) (hlay : TyLayOk Ti) (pw : ℕ → FK) (ry : List FE2)
    (hry : ry.length = yVars) : FE2.toE2 (virtF Ti pw ry) = virtE Ti pw (ry.map FE2.toE2) := by
  rw [Lvm6.QD.virt_eq hok hlay pw _ (by simp [hry])]
  have ht : (ry.take 10).length = 10 := by simp [hry, yVars]
  have key : ∀ j < 2 ^ 10, FE2.toE2 (FE2.mulK ((eqKernelAF (ry.take 10)).getD j 0) (pw (pubBase Ti + j))) =
      eqAtF ((ry.map FE2.toE2).take 10) j * Lvm6.Mb.kG (pw (pubBase Ti + j)) := by
    intro j hj
    rw [FE2.toE2_mulK, ← FE2.toE2_ofK, eqKernelAF_getD, if_pos (by rw [ht]; exact hj), toE2_eqAtF, List.map_take]
    rfl
  simp only [virtF]
  rw [toE2_add', toE2_mul', toE2_eqAtF, toE2_sumF, toE2_sumF, sumF_eq_sum, sumF_eq_sum, List.map_map, List.map_map,
    lsumR, List.map_drop]
  refine congrArg₂ (· + ·) (congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun j hj => ?_)) ?_
  · exact key j (Finset.mem_range.mp hj)
  · refine congrArg List.sum (List.map_congr_left fun R _ => ?_)
    simp only [Function.comp_apply, toE2_eqAtF, List.map_drop]

/-- **Fast `wireProgE`.** -/
def fWire (Ti : TInst6) (pw : ℕ → FK) (v : List FE2) : VF (List FE2 × List FE2 × List FE2) :=
  VF.bind (fE2Sample gGamma) fun γ =>
  VF.bind (fSumcheck gWire (wBatchF γ v) 3 (List.replicate yVars none)) fun rf =>
  VF.bind (fE2Reads 4) fun vs => VF.bind (fE2Reads 4) fun rv =>
  VF.guard (decide (rf.2 = wGF γ vs * (sumF rv + virtF Ti pw rf.1))) (VF.pure (rf.1, vs, rv))

/-- The decoding of three lists. -/
def l3D (r : List FE2 × List FE2 × List FE2) : List E2 × List E2 × List E2 :=
  (r.1.map FE2.toE2, r.2.1.map FE2.toE2, r.2.2.map FE2.toE2)

theorem tw_wire {Ti : TInst6} (hok : Ti.Ok) (hlay : TyLayOk Ti) (pw : ℕ → FK) (v : List FE2) :
    TwinP (fun r => r.1.length = yVars) l3D (wireProgE Ti pw (v.map FE2.toE2)) (fWire Ti pw v) := by
  unfold wireProgE fWire
  refine tw_bindG (tw_e2Sample _) fun γ => ?_
  beta_reduce
  rw [← toE2_wBatchF]
  refine twP_bind (tw_sumcheckPlainL _ _ _ _) fun rf hrf => tw_bindG (tw_e2Reads 4) fun vs =>
    tw_bindG (tw_e2Reads 4) fun rv => ?_
  refine tw_guardG _ _ ?_ (twP_pure (P := fun r : List FE2 × List FE2 × List FE2 => r.1.length = yVars) rfl hrf)
  simp only [scD]
  rw [← toE2_virtF hok hlay pw _ hrf, ← toE2_wGF, ← toE2_sumF, ← toE2_add', ← toE2_mul']
  exact toE2_eq_iff _ _

/-! ## Relayout -/

/-- The relayout kernel (CD's layout). -/
def kernF (Ti : TInst6) (ry r : List FE2) : FE2 :=
  eqAtF (ry.drop relayRounds) (sflatBase Ti / 2 ^ relayRounds) * eqEvalF (ry.take relayRounds) r

/-- **Fast `relayProgE`.** -/
def fRelay (Ti : TInst6) (ry : List FE2) (vS : FE2) : VF (List FE2 × FE2) :=
  VF.bind (fSumcheck gWire vS 3 (List.replicate relayRounds none)) fun rf => VF.bind fReadF fun vR =>
  VF.guard (decide (rf.2 = kernF Ti ry rf.1 * vR)) (VF.pure (rf.1, vR))

/-- The decoding of a list and a value. -/
def lvD (r : List FE2 × FE2) : List E2 × E2 := (r.1.map FE2.toE2, FE2.toE2 r.2)

theorem tw_relay {Ti : TInst6} (hok : Ti.Ok) (hS : StreamRegs6 Ti) (ry : List FE2) (hry : ry.length = yVars)
    (vS : FE2) : TwinF lvD (relayProgE Ti (ry.map FE2.toE2) (FE2.toE2 vS)) (fRelay Ti ry vS) := by
  unfold relayProgE fRelay
  refine twP_bind (tw_sumcheckPlainL _ _ _ _) fun rf hrf => tw_bind tw_e2Read fun vR => ?_
  refine tw_guard _ _ ?_ (tw_pure rfl)
  simp only [scD]
  rw [Lvm6.QD.relayKern_eq hok hS _ _ (by simp [hry]) (by simp [hrf])]
  rw [show eqAtF ((ry.map FE2.toE2).drop relayRounds) (sflatBase Ti / 2 ^ relayRounds) *
      eqEvalF ((ry.map FE2.toE2).take relayRounds) (rf.1.map FE2.toE2) = FE2.toE2 (kernF Ti ry rf.1) by
    simp only [kernF, ← coe_tE, map_mul, map_eqAtF, map_eqEvalF, List.map_drop, List.map_take]]
  rw [← toE2_mul']
  exact toE2_eq_iff _ _

/-! ## A23 -/

/-- `lineE` in the word field. -/
def lineF (a b : List FE2) (t : FE2) : List FE2 := List.zipWith (fun x y => x + t * (x + y)) a b

/-- `hEvalE` in the word field. -/
def hEvalF (hs : List FE2) (t : FE2) : FE2 := hs.foldr (fun c acc => c + t * acc) 0

/-- `yOwnE` in the word field. -/
def yOwnF (vs κ : List FE2) : FE2 := dotF (eqKernelF κ) vs

theorem map_lineF (a b : List FE2) (t : FE2) :
    (lineF a b t).map FE2.toE2 = lineE (a.map FE2.toE2) (b.map FE2.toE2) (FE2.toE2 t) := by
  simp only [lineF, lineE, List.map_zipWith, List.zipWith_map, ← coe_tE, map_add, map_mul]

theorem toE2_hEvalF (hs : List FE2) (t : FE2) : FE2.toE2 (hEvalF hs t) = hEvalE (hs.map FE2.toE2) (FE2.toE2 t) := by
  unfold hEvalF hEvalE
  induction hs with
  | nil => rfl
  | cons c hs ih => simp only [List.foldr_cons, List.map_cons, toE2_add', toE2_mul', ih]

theorem toE2_yOwnF (vs κ : List FE2) : FE2.toE2 (yOwnF vs κ) = yOwnE (vs.map FE2.toE2) (κ.map FE2.toE2) := by
  simp only [yOwnF, yOwnE, ← coe_tE, map_dotF, map_eqKernelF]

/-- **`ev` computes `Φ_Q`** (an evaluator: `phiFast tab`, `phiCov tab`). -/
def PhiOk (ev : List FE2 → FE2) (Q : Program) (lay : Lay) : Prop := ∀ pt, ev pt = PhiQFE Q lay pt

theorem phiOk_mk (Q : Program) (lay : Lay) : PhiOk (phiFast (mkPhiTab (entsE Q lay))) Q lay := phiFast_eq Q lay

/-- The flag of A23's three checks. -/
def accFlag (ev : List FE2 → FE2) (yIn : FE2) (a rxy vs κ hs : List FE2) (t : FE2) : Bool :=
  decide (hEvalF hs 0 = yIn) && decide (hEvalF hs 1 = yOwnF vs κ) &&
    decide (ev (lineF a (κ ++ rxy) t) = hEvalF hs t)

/-- **Fast `accProgE`.** -/
def fAcc (ev : List FE2 → FE2) (yIn : FE2) (a rxy vs : List FE2) : VF Unit :=
  VF.bind (fE2Samples gKappa selBitsE) fun κ => VF.bind (fE2Reads (phiVarsE + 1)) fun hs =>
  VF.bind (fE2Sample gT) fun t => VF.guard (accFlag ev yIn a rxy vs κ hs t) (VF.pure ())

theorem tw_acc {Q : Program} {lay : Lay} {ev : List FE2 → FE2} (htab : PhiOk ev Q lay) (yIn : FE2) (a rxy vs : List FE2) :
    TwinF (fun _ : Unit => ()) (accProgE Q lay (FE2.toE2 yIn) (a.map FE2.toE2) (rxy.map FE2.toE2) (vs.map FE2.toE2))
      (fAcc ev yIn a rxy vs) := by
  unfold accProgE fAcc
  refine tw_bind (tw_e2Samples _ _) fun κ => tw_bind (tw_e2Reads _) fun hs => tw_bind (tw_e2Sample _) fun t => ?_
  refine tw_require _ _ ?_
  rw [← List.map_append, ← map_lineF, Lvm6.Ty.PhiQE, map_tofE2_toE2, ← htab, ← toE2_zero', ← toE2_one',
    ← toE2_hEvalF, ← toE2_hEvalF, ← toE2_hEvalF, ← toE2_yOwnF]
  simp only [accFlag, Bool.and_eq_true, decide_eq_true_eq, FE2.toE2_injective.eq_iff, and_assoc]

end Lvm6.V
