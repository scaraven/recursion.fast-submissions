-- New for lvm6 (WP-V1b): fast claims as closures in the word field (`FClaim`, decoded through `ofE2`), and the
-- fast twin of ASM's ring phase (`ringPhase6`, FORMAT6 v2.4 §6.5: the bind, a nonce, 33 draws with the proof of work on
-- the first, the two ring claims placed at indices 1 and 15, the batch by `λ₀`).
import Lvm6VTwS
import Lvm6AsmRing

/-!
# Fast twins: stack claims and the ring phase

* `FClaim` (`f : List FE2 → FE2`, `v`), `FClaim.dec` (`x ↦ toE2 (f (x.map ofE2))`); point claims `pcF`
  (`pcF_dec`), the batch `batchF` (`batchF_dec`), `placeRingF` (`placeRingF_dec`).
* `SliceF`, `ringOfF` (`ringOfF_dec`: RS's `toE2_ringTarget`, `toE2_ringWeight`, `toE2_ringCoefficients`).
* **`fRingPhase6`**, **`tw_ringPhase6`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.Ring

/-! ## Fast stack claims -/

/-- A stack claim in the word field: its weight as a function, its value. -/
structure FClaim where
  f : List FE2 → FE2
  v : FE2

/-- Its value in `E2`. -/
def FClaim.dec (c : FClaim) : StackClaim6 := (fun x => FE2.toE2 (c.f (x.map FE2.ofE2)), FE2.toE2 c.v)

theorem map_toE2_ofE2 (x : List E2) : (x.map FE2.ofE2).map FE2.toE2 = x := by
  rw [List.map_map]; exact List.map_id'' (fun y => FE2.toE2_ofE2 y) x

/-- `eqPt` in the word field. -/
def eqPtF (a b : List FE2) : FE2 := (List.zipWith (fun r t => r * t + (1 + r) * (1 + t)) a b).prod

theorem toE2_eqPtF (a b : List FE2) : FE2.toE2 (eqPtF a b) = eqPt (a.map FE2.toE2) (b.map FE2.toE2) := by
  unfold eqPtF eqPt
  rw [← coe_tE, map_list_prod, List.map_zipWith, List.zipWith_map]
  simp only [map_add, map_mul, map_one]

/-- A point claim `(eq(p, ·), v)`. -/
def pcF (c : List FE2 × FE2) : FClaim := ⟨fun x => eqPtF c.1 x, c.2⟩

theorem pcF_dec (c : List FE2 × FE2) : (pcF c).dec = pcDec c := by
  simp only [FClaim.dec, pcF, pcDec, toE2_eqPtF, map_toE2_ofE2]

/-- The batch by `λ` (RS's `batch`). -/
def batchF (lam : FE2) (cs : List FClaim) : FClaim :=
  ⟨fun x => dotF (powersF lam cs.length) (cs.map fun c => c.f x), dotF (powersF lam cs.length) (cs.map (·.v))⟩

theorem batchF_dec (lam : FE2) (cs : List FClaim) : (batchF lam cs).dec = batch (FE2.toE2 lam) (cs.map FClaim.dec) := by
  simp only [FClaim.dec, batchF, batch, List.length_map, ← coe_tE, map_dotF, map_powersF, List.map_map,
    Function.comp_def]

/-- `placeRing` on fast claims. -/
def placeRingF (rt rs : FClaim) (st : List FClaim) : List FClaim :=
  st.take 1 ++ rt :: (st.drop 1).take 13 ++ rs :: st.drop 14

theorem placeRingF_dec (rt rs : FClaim) (st : List FClaim) :
    (placeRingF rt rs st).map FClaim.dec = placeRing rt.dec rs.dec (st.map FClaim.dec) := by
  simp only [placeRingF, placeRing, List.map_append, List.map_cons, List.map_take, List.map_drop]

/-! ## Ring claims -/

/-- A slice claim in the word field. -/
structure SliceF where
  pt : List FE2
  s : List FE2

/-- Its value in `E2`. -/
def SliceF.dec (c : SliceF) : SliceClaim := ⟨c.pt.map FE2.toE2, fun z => (c.s.map FE2.toE2).getD z 0⟩

theorem map_foldl_mul {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (l : List F) (acc : F) :
    φ (l.foldl (· * ·) acc) = (l.map φ).foldl (· * ·) (φ acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, map_mul]

theorem map_eqEvalF {F F' : Type} [Field F] [Field F'] (φ : F →+* F') (a b : List F) :
    φ (eqEvalF a b) = eqEvalF (a.map φ) (b.map φ) := by
  unfold eqEvalF
  rw [map_foldl_mul, map_one, List.map_zipWith, List.zipWith_map]
  simp only [map_add, map_one]

/-- RS's ring claim of a slice claim (`μ = |pt|`, no selector), in the word field. -/
def ringOfF (c : SliceF) (f g : List FE2) : FClaim :=
  ⟨fun x => eqEvalF [] (x.drop c.pt.length) * ringWeight c.pt (x.take c.pt.length) (ringCoefficients f g),
    ringTarget (FE2.ofK FK.x) (List.ofFn fun z : Fin 64 => c.s.getD z 0) f g⟩

theorem ringOfF_dec (c : SliceF) (f g : List FE2) :
    (ringOfF c f g).dec = ringOf c.dec (f.map FE2.toE2) (g.map FE2.toE2) := by
  simp only [FClaim.dec, ringOfF, ringOf, ringClaim, SliceF.dec, List.length_map]
  congr 1
  · funext x
    rw [toE2_mul', toE2_ringWeight, ← toE2_ringCoefficients]
    simp only [eqEvalF, List.zipWith_nil_left, List.foldl_nil, toE2_one', List.map_take, map_toE2_ofE2]
  · rw [toE2_ringTarget, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun z => ?_)
    simp only [Function.comp_apply, toE2_getD]

/-! ## The ring phase -/

/-- The `i`-th answer's challenge in `FE2` (`0` past the end). -/
@[inline] def ansAt (as : List Digest) (i : ℕ) : FE2 :=
  match as[i]? with
  | some a => fe2OfAns a
  | none => 0

theorem decAns (as : List Digest) (i : ℕ) : FE2.toE2 (ansAt as i) = e2OfE ((as.map chalOf).getD i 0) := by
  unfold ansAt
  cases hi : as[i]? with
  | none =>
    have : (as.map chalOf)[i]? = none := by simp [hi]
    rw [List.getD_eq_getElem?_getD, this, Option.getD_none]
    show FE2.toE2 0 = e2OfE 0
    rw [toE2_zero']
    simp [e2OfE]
    rfl
  | some a =>
    have : (as.map chalOf)[i]? = some (chalOf a) := by simp [hi]
    rw [List.getD_eq_getElem?_getD, this, Option.getD_some, e2OfE_chal]

/-- `ringOut6` on the answers. -/
def ringOut6F (as : List Digest) : ((List FE2 × List FE2) × (List FE2 × List FE2)) × FE2 :=
  ((((as.take 8).map fe2OfAns, ((as.drop 8).take 8).map fe2OfAns),
    (((as.drop 16).take 8).map fe2OfAns, ((as.drop 24).take 8).map fe2OfAns)), ansAt as 32)

/-- The batched claim of the challenges. -/
def claimOf6F (sl : List SliceF) (st : List FClaim)
    (o : ((List FE2 × List FE2) × (List FE2 × List FE2)) × FE2) : FClaim :=
  batchF o.2 (placeRingF (ringOfF (sl.getD 0 ⟨[], []⟩) o.1.1.1 o.1.1.2)
    (ringOfF (sl.getD 1 ⟨[], []⟩) o.1.2.1 o.1.2.2) st)

theorem sliceDec_default : SliceF.dec ⟨[], []⟩ = (⟨[], 0⟩ : SliceClaim) := by
  simp only [SliceF.dec, List.map_nil, List.getD_nil]
  rfl

theorem sl_getD (sl : List SliceF) (i : ℕ) : (sl.map SliceF.dec).getD i ⟨[], 0⟩ = (sl.getD i ⟨[], []⟩).dec := by
  rw [← sliceDec_default, List.getD_map]

theorem map_fe2OfAns (as : List Digest) : (as.map fe2OfAns).map FE2.toE2 = (as.map chalOf).map e2OfE := by
  simp only [List.map_map, Function.comp_def, e2OfE_chal]

theorem claimOf6F_dec (sl : List SliceF) (st : List FClaim) (as : List Digest) :
    (claimOf6F sl st (ringOut6F as)).dec = claimOf6 (sl.map SliceF.dec) (st.map FClaim.dec) (ringOut6 (as.map chalOf)) := by
  simp only [claimOf6F, claimOf6, batchF_dec, placeRingF_dec, ringOfF_dec, sl_getD, ringOut6F, ringOut6, decAns,
    map_fe2OfAns, List.map_take, List.map_drop]

/-- The proof of work of the first draw. -/
def powHead (g : ℕ) : List Digest → Bool
  | a :: _ => pw g (answerBits a)
  | [] => decide (LeanVM.Protocol.Verifier.powOK g 0)

theorem powHead_iff (g : ℕ) (as : List Digest) :
    LeanVM.Protocol.Verifier.powOK g ((as.map chalOf).headD 0) ↔ powHead g as = true := by
  cases as with
  | nil => simp [powHead]
  | cons a as => exact powOK_iff g a

/-- **Fast `ringPhase6 sh`.** -/
def fRingPhase6 (sh : Lvm6.Shape) (sl : List SliceF) (st : List FClaim) : VF FClaim :=
  VF.guard (decide (Lvm6.Params.admits ((sh.J₀ + 3) * sh.L₀) sh.gRing = true ∧ sh.gRing ≤ 64 ∧
      (∀ c ∈ sl, c.pt.length = sh.M) ∧ sl.length = 2)) <|
  VF.bind (VF.bind fSample fun _ => VF.pure ()) fun _ =>
  VF.bind fRead fun _ =>
  VF.bind (fSamples 33) fun as =>
  VF.guard (powHead sh.gRing as) (VF.pure (claimOf6F sl st (ringOut6F as)))

theorem tw_ringPhase6 (sh : Lvm6.Shape) (sl : List SliceF) (st : List FClaim) :
    TwinF FClaim.dec (ringPhase6 sh (sl.map SliceF.dec) (st.map FClaim.dec)) (fRingPhase6 sh sl st) := by
  unfold ringPhase6
  refine tw_guard _ _ ?_ ?_
  · simp only [ringOK, decide_eq_true_iff, List.forall_mem_map, SliceF.dec, List.length_map]
  refine tw_bind (d := fun _ => ()) (tw_sample fun _ => tw_pure rfl) fun _ => ?_
  refine tw_skipRead ?_
  unfold ringBody
  refine tw_bindR (twin_samples 33) fun π as cs hcs tr => ?_
  subst hcs
  exact tw_guard _ _ (powHead_iff _ as) (tw_pure (claimOf6F_dec sl st as)) π tr

end Lvm6.V
