-- New for `flock-recursive` (BLUEPRINT revision 4.3, stage-review changes 28 (a): the per-revision
-- template set; stage S-E12d, track L-circ).
import FRVIRTplExt

/-!
# A template set per revision: `tplExtF`, `ImplTF`, `compileTF_sound`

`tplExt` templates every op of A.11's table, and `ImplT` fixes the matching `OpImpl` fields to
3.x's (`implC`'s). Revision 4.1 runs other functions on some of these ops (S-E12c obstruction 4:
the node's `shiftMask` is over `chainLk4`, the segment's is `shiftSegI`), so a 4.1 program must not
use 3.x's template there. A revision therefore names **the set of keys it templates** (`TFilt`):

* **`tplExtF F`**: `tplExt` keeping only instances whose key is in `F`; any other op falls back to
  the plain compile (`opOut`: an import for `shiftMask`).
* **`KeyImpl impl k`**: what key `k`'s template needs of `impl` (one `ImplT` field, or nothing);
  **`ImplTF F impl`**: it holds for every key of `F`. `ImplT impl ↔ ImplTF allK impl`
  (`implTF_all`): 3.x's set is every key.
* **`tplExtF_ok`**, **`compileTF_sound`**: `compileT_sound` over a set. The proof reuses
  `tplExt_ok` at `fixT impl` (`impl` with the ten templated fields set to 3.x's): an op kept by
  `F` reads only its own key's field, on which `impl` and `fixT impl` agree (`evalOp_fixT`).

3.x's definitions (`tplExt`, `ImplT`, `compileT`, `compileT_sound`) are unchanged;
`tplExtF allK = tplExt` (`tplExtF_all`).
-/

namespace FR
namespace Circ
open Tpl RecursionFast

/-! ## The set -/

/-- **A template set**: the keys a revision templates. -/
abbrev TFilt := TKey → Bool

/-- 3.x's set: every key. -/
def allK : TFilt := fun _ => true

/-- **`tplExt` restricted to a set** (an op whose key is outside `F` is compiled by `opOut`). -/
def tplExtF (F : TFilt) (tc : TCtx) : Ext := fun P cs op =>
  (tplExt tc P cs op).filter fun o => o.tin.all fun t => F t.1

/-- **3.x's instance**: every key kept. -/
theorem tplExtF_all (tc : TCtx) : tplExtF allK tc = tplExt tc := by
  funext P cs op
  simp only [tplExtF, allK, Option.all_true]
  cases tplExt tc P cs op <;> rfl

/-- **`compileT` over a set.** -/
def compileTF (F : TFilt) (L : TLay) (P : Params) (base : ℕ) (ops : List Op) : CS :=
  compileX (tplExtF F L.ctx) P base ops

theorem compileTF_all (L : TLay) (P : Params) (base : ℕ) (ops : List Op) :
    compileTF allK L P base ops = compileT L P base ops := by
  rw [compileTF, tplExtF_all]; rfl

/-! ## What a key's template needs of `impl` -/

/-- **Key `k`'s requirement on `impl`** (`ImplT`'s field for `k`'s op; none for the keys whose op
reads no `OpImpl` field). -/
def KeyImpl (impl : OpImpl) : TKey → Prop
  | .shiftEq .. => impl.shiftEq = Impl.shiftEqI
  | .phiRS _ => impl.phiRS = Impl.phiRSI
  | .zero => ∀ a b c, impl.kindFoldWeight a b c = 0
  | .eqZ => impl.eqZ = Impl.eqZI
  | .lagrangeS .. => impl.lagrangeS = Impl.lagrangeSI
  | .slotW .. => ∀ κ, impl.slotW κ = Impl.slotWI
  | .tensorW _ => impl.tensorW = Impl.tensorWI
  | .rowW _ => impl.rowW = Impl.rowWI
  | .shiftMask .. => impl.shiftMask = NodeI.shiftMaskI
  | .walkAB .. => impl.walkAB = Eval.walkImpl
  | _ => True

/-- **`ImplT` over a set**: `impl` meets every kept key's template. -/
def ImplTF (F : TFilt) (impl : OpImpl) : Prop := ∀ k, F k = true → KeyImpl impl k

/-- `ImplT` gives `ImplTF` at every set. -/
theorem ImplT.toF {impl : OpImpl} (hT : ImplT impl) (F : TFilt) : ImplTF F impl := fun k _ => by
  cases k
  all_goals first
    | exact trivial
    | exact hT.shiftEq
    | exact hT.phiRS
    | exact hT.kfw
    | exact hT.eqZ
    | exact hT.lagrangeS
    | exact hT.slotW
    | exact hT.tensorW
    | exact hT.rowW
    | exact hT.shiftMask
    | exact hT.walkAB

/-- **3.x's set asks exactly `ImplT`.** -/
theorem implTF_all (impl : OpImpl) : ImplTF allK impl ↔ ImplT impl := by
  refine ⟨fun h => ?_, fun h => h.toF allK⟩
  exact ⟨h (.shiftEq 0 0) rfl, h (.phiRS 0) rfl, h .zero rfl, h .eqZ rfl, h (.lagrangeS 0 0) rfl,
    h (.slotW 0 0 0) rfl, h (.tensorW 0) rfl, h (.rowW 0) rfl, h (.shiftMask 0 0) rfl,
    h (.walkAB 0 0) rfl⟩

/-! ## Soundness -/

/-- `impl` with the ten templated fields set to 3.x's (`ImplT` holds). -/
def fixT (impl : OpImpl) : OpImpl :=
  { impl with
    shiftEq := Impl.shiftEqI
    phiRS := Impl.phiRSI
    kindFoldWeight := fun _ _ _ => 0
    eqZ := Impl.eqZI
    lagrangeS := Impl.lagrangeSI
    slotW := fun _ => Impl.slotWI
    tensorW := Impl.tensorWI
    rowW := Impl.rowWI
    shiftMask := NodeI.shiftMaskI
    walkAB := Eval.walkImpl }

theorem fixT_implT (impl : OpImpl) : ImplT (fixT impl) := by
  constructor <;> intros <;> simp only [fixT]

/-- **A templated op reads only its key's field**: where `impl` meets the instance's key, it runs
the op as `fixT impl` does. -/
theorem evalOp_fixT {impl : OpImpl} {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out}
    (hX : tplExt tc P cs op = some o) (hK : ∀ t ∈ o.tin, KeyImpl impl t.1)
    (κ : Kind) (inp : Input) (regs : Array Val) :
    evalOp impl κ inp regs op = evalOp (fixT impl) κ inp regs op := by
  cases op <;> simp only [tplExt] at hX
  all_goals first
    | (simp at hX; done)
    | (repeat' split at hX
       all_goals first
         | (simp at hX; done)
         | (simp only [Option.some.injEq] at hX; subst hX
            have h := hK _ rfl
            simp only [KeyImpl] at h
            simp only [evalOp, fixT, h]))

/-- **`tplExtF` is sound** under `ImplTF`. -/
theorem tplExtF_ok {impl : OpImpl} {F : TFilt} (hT : ImplTF F impl) (L : TLay) :
    ExtOk impl L.ctx (tplExtF F L.ctx) := by
  intro P cs op o hX
  obtain ⟨hX, hF⟩ := Option.filter_eq_some_iff.1 hX
  have he := evalOp_fixT (impl := impl) hX fun t ht => hT t.1 (by
    rw [Option.all_eq_true] at hF; exact hF t ht)
  obtain ⟨hl, h⟩ := tplExt_ok (fixT_implT impl) L P cs op o hX
  refine ⟨hl, fun κ inp w regs hP hI => ?_⟩
  simp only [he κ inp regs]
  exact h κ inp w regs hP hI

/-- **`compileT_sound` over a set** (`compileT_sound` at `F`, with `ImplTF F` for `ImplT`). -/
theorem compileTF_sound {impl : OpImpl} {F : TFilt} {κ : Kind} {inp : Input} {ops : List Op}
    {tr tr' : Trace} {s : St} {w : Asg} {P : Params} (hT : ImplTF F impl) (L : TLay) (base : ℕ)
    (hP : SelOk w P κ) (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileTF F L P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileTF F L P base ops).tplRows L.ctx P.one, r.Holds w)
    (hx : ∀ a ∈ (compileTF F L P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (compileTF F L P base ops).imp,
      RepS w ((compileTF F L P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileTF F L P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileTF F L P base ops).slot i) (rd s.regs i) :=
  compileX_sound (tplExtF_ok hT L) base hP he hr ht hx hi hf

/-- **The two-pass layout over a set** (`layOf` at `F`; a layout is a hint, `compileTF_sound` holds
at every layout). -/
def layOfF (F : TFilt) (P : Params) (base : ℕ) (ops : List Op) : TLay :=
  let cs := compileTF F [] P base ops
  mkLay cs.nrows cs.next (keyCounts cs.tins)

/-! ## Revision 4.1's set -/

/-- **Revision 4.1's set** (S-E12c obstruction 4): every key but 3.x's `shiftMask` (the node's
`chainLk4` mask and the segment's `shiftSegI` are imports until their templates). -/
def keys41 : TFilt
  | .shiftMask .. => false
  | _ => true

/-- `ImplTF keys41` leaves `shiftMask` free: the segment's `implSeg` (with `shiftSegI`) meets it
whenever its base meets `ImplT`. -/
theorem implTF_keys41 {impl : OpImpl} (hT : ImplT impl) (sm : Array F → Array F → F × F × F) :
    ImplTF keys41 { impl with shiftMask := sm } := fun k hk => by
  cases k
  all_goals first
    | exact trivial
    | exact hT.shiftEq
    | exact hT.phiRS
    | exact hT.kfw
    | exact hT.eqZ
    | exact hT.lagrangeS
    | exact hT.slotW
    | exact hT.tensorW
    | exact hT.rowW
    | exact hT.walkAB
    | exact absurd hk Bool.false_ne_true

/-! ## Controls -/

/-- Two `af` registers (the controls' compile state). -/
def ctlCS : CS :=
  ((CS.init 0).add (.const fun _ => .af #[0]) { slots := [some (.af 1, [[]])] }).add
    (.const fun _ => .af #[0]) { slots := [some (.af 1, [[]])] }

/-- (+) A kept key's op is templated; (−) an op whose key is outside the set is not: `shiftMask`
on two `af` registers under `allK` and `keys41`, and `shiftEq` kept by `keys41`. -/
theorem tplExtF_ctl :
    (tplExtF allK ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCS (.shiftMask 0 1)).isSome
        = true ∧
      (tplExtF keys41 ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCS
        (.shiftMask 0 1)).isSome = false ∧
      (tplExtF keys41 ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCS
        (.shiftEq 0 1)).isSome = true := by
  decide

/-- (−) 3.x's set pins `shiftMask` to 3.x's (so a 4.1 `impl` does not meet it), where `keys41`
leaves it free (`implTF_keys41`). -/
theorem implTF_all_shiftMask {impl : OpImpl} (h : ImplTF allK impl) :
    impl.shiftMask = NodeI.shiftMaskI := h (.shiftMask 0 0) rfl

/-- (+) `keys41` keeps `eqZ`; (−) it drops `shiftMask`. -/
theorem keys41_ctl : keys41 .eqZ = true ∧ keys41 (.shiftMask 18 18) = false := ⟨rfl, rfl⟩

end Circ
end FR
