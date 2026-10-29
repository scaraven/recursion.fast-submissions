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

/-! ## Revision 4.1's `shiftMask` route (S-E12e) -/

/-- **Which 4.1 template a `shiftMask` takes** (per prototype): none (an import, S-E12d's), the
segment's (`shiftSegI`, key `.shiftSeg`), or the node's over the group's kinds (`chainLk4`, key
`.maskN … ks` with per selector index the kind's `(nb, chLen₀, chLen₁)`). -/
inductive ShR where
  | imp
  | seg
  | node (ks : List (ℕ × ℕ × ℕ))

/-- A selector index's position in `kinds`. -/
def kIx : Kind → ℕ
  | .L32 => 0
  | .P30 => 1
  | .N30 => 2

/-- **`tplExtF` with the 4.1 `shiftMask` templates**: a `shiftMask` on `af n, af m` goes to the
route's key when `F` keeps it (the node's instance reads the selector forms after `τ`, `r`); every
other op as `tplExtF F`. -/
def tplExt4 (F : TFilt) (R : ShR) (tc : TCtx) : Ext := fun P cs op =>
  match op, R with
  | .shiftMask t r, .seg =>
    match cs.slot t, cs.slot r with
    | some (.af n, lt), some (.af m, lr) =>
      if F (.shiftSeg n m) then some (tplOut tc P cs (.shiftSeg n m) (lt ++ lr) [.f, .f, .f]) else none
    | _, _ => none
  | .shiftMask t r, .node ks =>
    match cs.slot t, cs.slot r with
    | some (.af n, lt), some (.af m, lr) =>
      if F (.maskN n m ks) then
        some (tplOut tc P cs (.maskN n m ks) (lt ++ lr ++ kinds.map P.sel) [.f, .f, .f])
      else none
    | _, _ => none
  | _, _ => tplExtF F tc P cs op

/-- Without a route it is `tplExtF`. -/
theorem tplExt4_imp (F : TFilt) (tc : TCtx) : tplExt4 F .imp tc = tplExtF F tc := by
  funext P cs op; cases op <;> rfl

/-- **What the route needs of `impl` at kind `κ`**: the segment's `shiftMask`, or the node kind's
of index `κ`. -/
def RouteOk (R : ShR) (impl : OpImpl) (κ : Kind) : Prop :=
  match R with
  | .imp => True
  | .seg => impl.shiftMask = segMaskV
  | .node ks => kIx κ < ks.length ∧ impl.shiftMask = maskNV (ks.getD (kIx κ) (0, 0, 0))

theorem sel_onehot {w : Asg} {P : Params} {κ : Kind} (hP : SelOk w P κ) :
    (kinds.map P.sel).map (Lin.ev w) = kinds.map fun ι => if ι = κ then 1 else 0 := by
  simp only [List.map_map]; exact List.map_congr_left fun ι _ => hP.2 ι

theorem kinds_getD (κ : Kind) (j : ℕ) :
    (kinds.map fun ι => if ι = κ then (1 : F) else 0).getD j 0 = if j = kIx κ then 1 else 0 := by
  cases κ <;> rcases j with _ | _ | _ | j <;> simp [kinds, kIx]

/-- **`tplExt4` is sound at kind `κ`** under `ImplTF F` and the route's requirement at `κ`. -/
theorem tplExt4_okAt {impl : OpImpl} {F : TFilt} {R : ShR} {κ : Kind} (hT : ImplTF F impl)
    (hR : RouteOk R impl κ) (L : TLay) : ExtOkAt impl L.ctx (tplExt4 F R L.ctx) κ := by
  intro P cs op o hX
  rcases R with _ | _ | ks
  · rw [tplExt4_imp] at hX; exact (tplExtF_ok hT L).at κ P cs op o hX
  · unfold tplExt4 at hX
    split at hX
    · split at hX
      · rename_i n lt m lr ht' hr'
        split_ifs at hX with hF
        simp only [Option.some.injEq] at hX; subst hX
        refine ⟨rfl, fun inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
        simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ht')
        obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr')
        have hsm : impl.shiftMask = segMaskV := hR
        rw [hx, hy, hsm]
        exact outSlots_three rfl rfl rfl
          (tplShiftSeg_ok (inpIs_of (by simp [hxl, hyl])) hP.1 (tin_eqns hP.1 ht))
      · simp at hX
    · rename_i heq; cases heq
    · exact (tplExtF_ok hT L).at κ P cs _ o hX
  · unfold tplExt4 at hX
    split at hX
    · rename_i heq; cases heq
    · rename_i ks' heq; cases heq
      split at hX
      · rename_i n lt m lr ht' hr'
        split_ifs at hX with hF
        simp only [Option.some.injEq] at hX; subst hX
        refine ⟨rfl, fun inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
        simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ht')
        obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr')
        obtain ⟨hk, hsm⟩ : kIx κ < ks.length ∧ impl.shiftMask = maskNV (ks.getD (kIx κ) (0, 0, 0)) := hR
        rw [hx, hy, hsm]
        have hE := tin_eqns hP.1 ht
        have hI' : InpIs (envOf w P.one (lt ++ lr ++ kinds.map P.sel)
            (L.ctx.cb (.maskN x.size y.size ks) (cs.tcount (.maskN x.size y.size ks))))
            (x.toList ++ y.toList ++ kinds.map fun ι => if ι = κ then (1 : FR.F) else 0) :=
          inpIs_of (by rw [List.map_append, List.map_append, hxl, hyl, sel_onehot hP])
        have ho := tplMaskN_ok (τ := x) (r := y) (ks := ks) (j0 := kIx κ) hI' hP.1 hk (kinds_getD κ) hE
        exact outSlots_three rfl rfl rfl ho
      · simp at hX
    · exact (tplExtF_ok hT L).at κ P cs _ o hX

/-- **`compileTF` with the 4.1 route.** -/
def compileTF4 (F : TFilt) (R : ShR) (L : TLay) (P : Params) (base : ℕ) (ops : List Op) : CS :=
  compileX (tplExt4 F R L.ctx) P base ops

theorem compileTF4_imp (F : TFilt) (L : TLay) (P : Params) (base : ℕ) (ops : List Op) :
    compileTF4 F .imp L P base ops = compileTF F L P base ops := by
  rw [compileTF4, tplExt4_imp]; rfl

/-- **`compileTF_sound` with the 4.1 route, at the run's kind** (`ImplTF F` and the route's
requirement at `κ`; `compileX_soundAt`). -/
theorem compileTF4_soundAt {impl : OpImpl} {F : TFilt} {R : ShR} {κ : Kind} {inp : Input}
    {ops : List Op} {tr tr' : Trace} {s : St} {w : Asg} {P : Params} (hT : ImplTF F impl)
    (hR : RouteOk R impl κ) (L : TLay) (base : ℕ)
    (hP : SelOk w P κ) (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileTF4 F R L P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileTF4 F R L P base ops).tplRows L.ctx P.one, r.Holds w)
    (hx : ∀ a ∈ (compileTF4 F R L P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (compileTF4 F R L P base ops).imp,
      RepS w ((compileTF4 F R L P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileTF4 F R L P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileTF4 F R L P base ops).slot i) (rd s.regs i) :=
  compileX_soundAt (tplExt4_okAt hT hR L) base hP he hr ht hx hi hf

/-- **The two-pass layout with the 4.1 route.** -/
def layOfF4 (F : TFilt) (R : ShR) (P : Params) (base : ℕ) (ops : List Op) : TLay :=
  let cs := compileTF4 F R [] P base ops
  mkLay cs.nrows cs.next (keyCounts cs.tins)

/-! ## Controls -/

/-- Two `af` registers of sizes 36 and 18 (the 4.1 controls' compile state). -/
def ctlCS4 : CS :=
  ((CS.init 0).add (.const fun _ => .af #[0]) { slots := [some (.af 36, [[]])] }).add
    (.const fun _ => .af #[0]) { slots := [some (.af 18, [[]])] }

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

/-- (+) The segment route templates `shiftMask` on `af 36, af 18` at `.shiftSeg 36 18`; the node
route at `.maskN 18 18 ks`; (−) no route leaves it an import (S-E12d's `keys41`). -/
theorem tplExt4_ctl :
    ((tplExt4 keys41 .seg ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCS4 (.shiftMask 0 1)).bind
        (·.tin.map Prod.fst)) = some (.shiftSeg 36 18) ∧
      ((tplExt4 keys41 (.node [(1, 2, 3)]) ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCS4
        (.shiftMask 0 1)).bind (·.tin.map Prod.fst)) = some (.maskN 36 18 [(1, 2, 3)]) ∧
      (tplExt4 keys41 .imp ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCS4
        (.shiftMask 0 1)).isSome = false := by
  decide

/-- (+) The node route asks the kind's own entry; (−) at another kind's entry it fails (the three
kinds' `shiftMask`s differ, so a single `impl` cannot serve every kind: hence `ExtOkAt`). -/
theorem routeOk_ctl (impl : OpImpl) (sm : Array F → Array F → F × F × F) :
    RouteOk (.node [(1, 1, 1), (2, 2, 2), (3, 3, 3)]) { impl with shiftMask := sm } .P30 ↔
      sm = maskNV (2, 2, 2) := by
  simp [RouteOk, kIx]

end Circ
end FR
