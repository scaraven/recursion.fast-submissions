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
  | .tensorWK _ => impl.tensorW = Impl.tensorWI
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

/-- **`tplExtF` with the 4.1 `shiftMask` templates** (S-E12e's `tplExt4`): a `shiftMask` on
`af n, af m` goes to the route's key when `F` keeps it (the node's instance reads the selector
forms after `τ`, `r`); every other op as `tplExtF F`. -/
def tplExt4S (F : TFilt) (R : ShR) (tc : TCtx) : Ext := fun P cs op =>
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
theorem tplExt4S_imp (F : TFilt) (tc : TCtx) : tplExt4S F .imp tc = tplExtF F tc := by
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

/-- **`tplExt4S` is sound at kind `κ`** under `ImplTF F` and the route's requirement at `κ`. -/
theorem tplExt4S_okAt {impl : OpImpl} {F : TFilt} {R : ShR} {κ : Kind} (hT : ImplTF F impl)
    (hR : RouteOk R impl κ) (L : TLay) : ExtOkAt impl L.ctx (tplExt4S F R L.ctx) κ := by
  intro P cs op o hX
  rcases R with _ | _ | ks
  · rw [tplExt4S_imp] at hX; exact (tplExtF_ok hT L).at κ P cs op o hX
  · unfold tplExt4S at hX
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
  · unfold tplExt4S at hX
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

/-! ## Kind-muxed operands (S-E12f, INT-9 F1) -/

/-- `tplExt`'s results set no per-kind slot. -/
theorem tplExt_kin {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out} (h : tplExt tc P cs op = some o) :
    o.kin = none := by
  cases op <;> simp only [tplExt] at h
  all_goals first
    | (simp at h; done)
    | (repeat' split at h
       all_goals first
         | (simp at h; done)
         | (simp only [Option.some.injEq] at h; subst h; rfl))

theorem tplExt4S_kin {F : TFilt} {R : ShR} {tc : TCtx} {P : Params} {cs : CS} {op : Op} {o : Out}
    (h : tplExt4S F R tc P cs op = some o) : o.kin = none := by
  have hF : ∀ {o}, tplExtF F tc P cs op = some o → o.kin = none := fun h' =>
    tplExt_kin (Option.filter_eq_some_iff.1 h').1
  unfold tplExt4S at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | exact hF h

/-- An `ak` slot's length and forms. -/
def akS : Slot → Option (ℕ × List Lin)
  | some (.ak n, ls) => some (n, ls)
  | _ => none

/-- An `af` slot's length and forms. -/
def afS : Slot → Option (ℕ × List Lin)
  | some (.af n, ls) => some (n, ls)
  | _ => none

theorem akS_eq {s : Slot} {b : ℕ × List Lin} (h : akS s = some b) : s = some (.ak b.1, b.2) := by
  unfold akS at h; split at h
  · cases h; rfl
  · cases h

theorem afS_eq {s : Slot} {b : ℕ × List Lin} (h : afS s = some b) : s = some (.af b.1, b.2) := by
  unfold afS at h; split at h
  · cases h; rfl
  · cases h

/-- Whether `opOut` tracks a `keep`'s result (its operands' types agree). -/
def keepTracked (cs : CS) (n o : ℕ) : Bool :=
  match (cs.slot n).ty?, (cs.slot o).ty? with
  | some t, some t' => decide (t = t')
  | _, _ => false

/-- **A `keep`'s result at kind `κ`**: the kind's operand at `κ`. -/
def keepK (cs : CS) (act : KC Bool) (n o : ℕ) (κ : Kind) : Slot :=
  if act κ then cs.slotK n κ else cs.slotK o κ

/-- **A `packFK`'s result at kind `κ`**: the kind's list as an `af` (when its elements are tracked). -/
def packFKK (cs : CS) (xs : Kind → List ℕ) (κ : Kind) : Slot :=
  if (xs κ).all fun x => (cs.slot x).isSome then
    some (.af (xs κ).length, (xs κ).map fun x => asF (cs.slot x))
  else none

/-- **The kind-mux extension**: a `keep` that `opOut` leaves untracked and a `packFK` of lists of
unequal lengths get per-kind slots (`keepK`, `packFKK`); a `tensorW` on a point and an `eqPt` on
points that are typed at every kind (`slotK`) go to `.tensorWK`/`.eqPtK` with the kinds' lengths,
reading each kind's forms (checked to be of their type's length) and the selector forms. -/
def tplExtKM (F : TFilt) (tc : TCtx) : Ext := fun P cs op =>
  match op with
  | .keep act n o =>
    if keepTracked cs n o then none
    else if kinds.any fun κ => (keepK cs act n o κ).isSome then
      some { slots := [none], kin := some (keepK cs act n o) }
    else none
  | .packFK xs =>
    if (xs .L32).length = (xs .P30).length ∧ (xs .P30).length = (xs .N30).length then none
    else some { slots := [none], kin := some (packFKK cs xs) }
  | .tensorW j r =>
    match akS (cs.slotK r .L32), akS (cs.slotK r .P30), akS (cs.slotK r .N30) with
    | some a, some b, some c =>
      let ns := [a.1, b.1, c.1]
      if ([a, b, c].all fun x => x.2.length == 2 * x.1) && ns.all (· ≤ logNMax) && F (.tensorWK ns) then
        -- `j`'s 20 bits: auxiliary import cells after the template's locals (as `tensorW`'s)
        let cb := tc.cb (.tensorWK ns) (cs.tcount (.tensorWK ns))
        let cells := (List.range logNMax).map fun i => Lin.cell (cb + twkLocs ns + i)
        some { tplOut tc P cs (.tensorWK ns) (a.2 ++ b.2 ++ c.2 ++ cells ++ kinds.map P.sel) [.k] with
          aux := [(cells, j, .bits logNMax)] }
      else none
    | _, _, _ => none
  | .eqPt x y =>
    match afS (cs.slotK x .L32), afS (cs.slotK y .L32), afS (cs.slotK x .P30), afS (cs.slotK y .P30),
        afS (cs.slotK x .N30), afS (cs.slotK y .N30) with
    | some a0, some b0, some a1, some b1, some a2, some b2 =>
      let ps := [(a0.1, b0.1), (a1.1, b1.1), (a2.1, b2.1)]
      if ([(a0, b0), (a1, b1), (a2, b2)].all fun p => p.1.2.length == p.1.1 && p.2.2.length == p.2.1) &&
          F (.eqPtK ps) then
        some (tplOut tc P cs (.eqPtK ps) (a0.2 ++ b0.2 ++ (a1.2 ++ b1.2) ++ (a2.2 ++ b2.2) ++ kinds.map P.sel) [.f])
      else none
    | _, _, _, _, _, _ => none
  | _ => none

theorem kinds_oneHot (κ : Kind) :
    (kinds.map fun ι => if ι = κ then (1 : F) else 0) = oneHot 3 (kIx κ) := by
  cases κ <;> simp [kinds, oneHot, kIx, List.range_succ]

theorem kIx_lt (κ : Kind) : kIx κ < 3 := by cases κ <;> decide

/-- The three kinds' entries, read at `κ`. -/
theorem get3 {α : Type} {f : Kind → Option α} {a b c : α} (ha : f .L32 = some a) (hb : f .P30 = some b)
    (hc : f .N30 = some c) (κ : Kind) : f κ = some ([a, b, c][kIx κ]'(by simpa using kIx_lt κ)) := by
  cases κ <;> simpa [kIx]

theorem get3_pair {α β : Type} (a0 a1 a2 : α) (b0 b1 b2 : β) (κ : Kind) :
    [(a0, b0), (a1, b1), (a2, b2)][kIx κ]'(by simpa using kIx_lt κ) =
      ([a0, a1, a2][kIx κ]'(by simpa using kIx_lt κ), [b0, b1, b2][kIx κ]'(by simpa using kIx_lt κ)) := by
  cases κ <;> rfl

theorem get3_fst {α β : Type} (a0 a1 a2 : ℕ × α) (b0 b1 b2 : ℕ × β) (κ : Kind) :
    [(a0.1, b0.1), (a1.1, b1.1), (a2.1, b2.1)][kIx κ]'(by simpa using kIx_lt κ) =
      (([a0, a1, a2][kIx κ]'(by simpa using kIx_lt κ)).1, ([b0, b1, b2][kIx κ]'(by simpa using kIx_lt κ)).1) := by
  cases κ <;> rfl

/-- **The kind-mux extension is sound at kind `κ`** (with per-kind slots). -/
theorem tplExtKM_okK {impl : OpImpl} {F : TFilt} {κ : Kind} (hT : ImplTF F impl) (L : TLay) :
    ExtOkK impl L.ctx (tplExtKM F L.ctx) κ := by
  intro P cs op o hX
  cases op <;> simp only [tplExtKM] at hX
  all_goals first | (simp at hX; done) | skip
  case keep act n m =>
    split_ifs at hX with h1 h2
    simp only [Option.some.injEq] at hX; subst hX
    refine ⟨rfl, fun _ => by simp, fun inp w regs hP hI hK => ⟨fun q => by simp [evalOp], fun _ _ _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => List.Forall₂.cons trivial List.Forall₂.nil, fun _ => rfl, fun f v hf hv => ?_⟩
    simp only [Option.some.injEq] at hf; subst hf
    simp only [List.head?_cons, Option.some.injEq] at hv; subst hv
    simp only [keepK]; split_ifs <;> exact hK _
  case packFK xs =>
    split_ifs at hX with h1
    simp only [Option.some.injEq] at hX; subst hX
    refine ⟨rfl, fun _ => by simp, fun inp w regs hP hI hK => ⟨fun q => by simp [evalOp], fun _ _ _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => List.Forall₂.cons trivial List.Forall₂.nil, fun _ => rfl, fun f v hf hv => ?_⟩
    simp only [Option.some.injEq] at hf; subst hf
    simp only [List.head?_cons, Option.some.injEq] at hv; subst hv
    simp only [packFKK]
    split_ifs with ht
    · refine ⟨by simp [tyOf], ?_⟩
      simp only [encV, List.map_map]
      exact List.map_congr_left fun x hx => asF_slot hI (List.all_eq_true.1 ht x hx)
    · trivial
  case tensorW j r =>
    split at hX
    · rename_i a b c ha hb hc
      split_ifs at hX with hcond
      simp only [Option.some.injEq] at hX; subst hX
      simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq,
        decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨la, lb, lc⟩, na, nb, nc⟩, hF⟩ := hcond
      refine ⟨rfl, fun h => by simp [tplOut] at h, fun inp w regs hP hI hK =>
        ⟨fun q => by simp [evalOp], fun _ ht hx vs ok he => ?_⟩⟩
      simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      refine ⟨fun _ => ?_, fun _ => rfl, fun f v hf => by simp [tplOut] at hf⟩
      -- the run's kind's point
      have hg := get3 (f := fun ι => akS (cs.slotK r ι)) ha hb hc κ
      have hj0 : kIx κ < 3 := kIx_lt κ
      have hs := akS_eq hg
      obtain ⟨x, hx', hxs, hxl⟩ := rep_ak (hs ▸ hK r)
      have hcells := hx _ (List.mem_singleton_self _)
      simp only [Tpl.AuxK.val] at hcells
      have hTw : impl.tensorW = Impl.tensorWI := hT _ hF
      rw [hx', hTw]
      refine outSlots_one rfl (tplTensorWK_ok (vb := [a, b, c].map fun y => y.2.map (Lin.ev w)) (j0 := kIx κ)
        hP.1 (by simp [la, lb, lc]) (by simpa using hj0) ?_ ?_ ?_
        (tin_eqns (tc := L.ctx) (k := .tensorWK [a.1, b.1, c.1]) (tys := [.k]) hP.1 ht))
      · rw [List.getElem?_map, List.getElem?_eq_getElem (l := [a, b, c]) (by simpa using hj0)]
        exact congrArg some hxl
      · have : ∀ ι, ([a, b, c][kIx ι]'(by simpa using kIx_lt ι)).1 ≤ logNMax := fun ι => by
          cases ι <;> assumption
        show x.size ≤ logNMax
        rw [hxs]; exact this κ
      · refine inpIs_of ?_
        simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc, hcells, sel_onehot hP, kinds_oneHot]
        rfl
    · simp at hX
  case eqPt x y =>
    split at hX
    · rename_i a0 b0 a1 b1 a2 b2 ha0 hb0 ha1 hb1 ha2 hb2
      split_ifs at hX with hcond
      simp only [Option.some.injEq] at hX; subst hX
      simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨la0, lb0⟩, ⟨la1, lb1⟩, ⟨la2, lb2⟩⟩, hF⟩ := hcond
      refine ⟨rfl, fun h => by simp [tplOut] at h, fun inp w regs hP hI hK =>
        ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
      simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      refine ⟨fun _ => ?_, fun _ => rfl, fun f v hf => by simp [tplOut] at hf⟩
      have hga := get3 (f := fun ι => afS (cs.slotK x ι)) ha0 ha1 ha2 κ
      have hgb := get3 (f := fun ι => afS (cs.slotK y ι)) hb0 hb1 hb2 κ
      have hj0 : kIx κ < 3 := kIx_lt κ
      obtain ⟨u, hu', hus, hul⟩ := rep_af (afS_eq hga ▸ hK x)
      obtain ⟨v, hv', hvs, hvl⟩ := rep_af (afS_eq hgb ▸ hK y)
      rw [hu', hv']
      refine outSlots_one rfl (tplEqPtK_ok (j0 := kIx κ)
        (vb := [(a0, b0), (a1, b1), (a2, b2)].map fun p => (p.1.2 ++ p.2.2).map (Lin.ev w))
        hP.1 (by simp [epW, la0, lb0, la1, lb1, la2, lb2]) (by simpa using hj0) ?_ ?_ ?_
        (tin_eqns (tc := L.ctx) (k := .eqPtK _) (tys := [.f]) hP.1 ht))
      · rw [List.getElem?_eq_getElem (by simpa using hj0), get3_fst]
        show some (_, _) = some (u.size, v.size)
        rw [hus, hvs]
      · rw [List.getElem?_map, List.getElem?_eq_getElem (l := [(a0, b0), (a1, b1), (a2, b2)])
          (by simpa using hj0), get3_pair]
        show some (List.map (Lin.ev w) ((_ : List Lin) ++ _)) = _
        rw [List.map_append, hul, hvl]; rfl
      · refine inpIs_of ?_
        simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc, sel_onehot hP, kinds_oneHot]
        rfl
    · simp at hX

/-- Whether a route templates the kind-muxed operands (every 4.1 prototype's does). -/
def ShR.kmux : ShR → Bool
  | .imp => false
  | _ => true

/-- **Revision 4.1's extension**: `tplExt4S` (S-E12e), then, under a route, the kind mux
(`tplExtKM`, S-E12f). -/
def tplExt4 (F : TFilt) (R : ShR) (tc : TCtx) : Ext :=
  (tplExt4S F R tc).orElse fun P cs op => if R.kmux then tplExtKM F tc P cs op else none

/-- Without a route it is `tplExtF`. -/
theorem tplExt4_imp (F : TFilt) (tc : TCtx) : tplExt4 F .imp tc = tplExtF F tc := by
  funext P cs op
  simp only [tplExt4, Ext.orElse, ShR.kmux, tplExt4S_imp]
  cases tplExtF F tc P cs op <;> rfl

/-- **`tplExt4` is sound at kind `κ`** (with per-kind slots) under `ImplTF F` and the route's
requirement at `κ`. -/
theorem tplExt4_okK {impl : OpImpl} {F : TFilt} {R : ShR} {κ : Kind} (hT : ImplTF F impl)
    (hR : RouteOk R impl κ) (L : TLay) : ExtOkK impl L.ctx (tplExt4 F R L.ctx) κ :=
  ((tplExt4S_okAt hT hR L).toK fun _ _ _ _ h => tplExt4S_kin h).orElse fun P cs op o h => by
    by_cases hk : R.kmux = true
    · simp only [hk, if_true] at h; exact tplExtKM_okK hT L P cs op o h
    · simp only [hk, if_false, Bool.false_eq_true, reduceCtorEq] at h

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
  compileX_soundK (tplExt4_okK hT hR L) base hP he hr ht hx hi hf

/-- The start of the first interval of `occ` that `[a, a + n)` meets. -/
def meetsAt (a n : ℕ) (occ : List (ℕ × ℕ)) : Option ℕ :=
  (occ.find? fun p => decide (a < p.2) && decide (p.1 < a + n)).map (·.1)

/-- The highest `2^b`-aligned base whose `n` cells end at or below `c` and meet no interval of `occ`
(each step passes one interval: fuel `|occ| + 1`). -/
def fitDown (b n : ℕ) (occ : List (ℕ × ℕ)) : ℕ → ℕ → ℕ
  | 0, c => (c - n) / 2 ^ b * 2 ^ b
  | fuel + 1, c =>
    let x := (c - n) / 2 ^ b * 2 ^ b
    match meetsAt x n occ with
    | some s => fitDown b n occ fuel s
    | none => x

/-- **Top-down cells** (B2′; it makes a hint only, which nothing trusts): a layout's groups re-based
in cells, in decreasing cell bits, each at the highest base below `top` (the slot region's end, an
aligned bound), aligned to its bits, whose cells meet no group placed before; the rows stay
`mkLay`'s. A group takes `n·2^b` cells, the walk up to its last local. From an aligned top, groups of
decreasing alignment pack without gaps; `mkLay`'s order leaves one before every group aligned more
than the one before it (4.4.1's prototype 0: 27,392 cells before `rowW 8`), and a slot region's cells
are nearly full (B2′'s RESULT). -/
def fitCells (top : ℕ) (L : TLay) (ks : List (TKey × ℕ)) : TLay :=
  let sz := fun (e : TKey × ℕ × ℕ × ℕ) =>
    let n := ((ks.find? (·.1 == e.1)).map (·.2)).getD 1
    if isWalk e.1 then (n - 1) * 2 ^ e.2.2.2 + tNlocs e.1 else n * 2 ^ e.2.2.2
  let ord := (List.range (L.foldl (fun m e => max m e.2.2.2) 0 + 1)).reverse.flatMap fun b =>
    L.filter (·.2.2.2 == b)
  let placed := ord.foldl (fun (acc : List (TKey × ℕ) × List (ℕ × ℕ)) e =>
    let c := fitDown e.2.2.2 (sz e) acc.2 (acc.2.length + 1) top
    ((e.1, c) :: acc.1, (c, c + sz e) :: acc.2)) ([], [])
  L.map fun e => (e.1, e.2.1, ((placed.1.find? (·.1 == e.1)).map (·.2)).getD e.2.2.1, e.2.2.2)

/-- (+) Below 64, a 16-cell group goes to 48 and a 4-cell group right below it, at 44; (−) a group
that would meet one placed before moves below it (8 cells at 56, then 4 at 52, not 60). -/
theorem fitCells_ctl :
    (fitCells 64 [(.zero, 0, 0, 2), (.eqZ, 0, 0, 4)] [(.zero, 1), (.eqZ, 1)]).map (·.2.2.1) = [44, 48] ∧
    (fitCells 64 [(.zero, 0, 0, 2), (.eqZ, 0, 0, 2)] [(.zero, 2), (.eqZ, 1)]).map (·.2.2.1) = [56, 52] := by
  decide

/-- **The two-pass layout with the 4.1 route** (B2′: cells top-down from the `2^20`-cell region's end,
`fitCells`). -/
def layOfF4 (F : TFilt) (R : ShR) (P : Params) (base : ℕ) (ops : List Op) : TLay :=
  let cs := compileTF4 F R [] P base ops
  fitCells (alignUp (base + 1) 20) (mkLay cs.nrows cs.next (keyCounts cs.tins)) (keyCounts cs.tins)

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

/-- Two `ak` registers of lengths 2 and 1, two `f` registers (the kind-mux controls' state). -/
def ctlCSK : CS :=
  (((CS.init 0).add (.const fun _ => .af #[0]) { slots := [some (.ak 2, [[], [], [], []])] }).add
    (.const fun _ => .af #[0]) { slots := [some (.ak 1, [[], []])] }).add
    (.const fun _ => .af #[0]) { slots := [some (.f, [[]]), some (.f, [[]])] }

/-- The controls' program: `r4 = keep {L32} r0 r1` (2 `K`s at `L32`, 1 otherwise), `tensorW r0 r4`,
`r6 = packFK {L32: [r2, r3], P30: [r2], N30: [r2]}`, `eqPt r6 r6`. -/
def ctlOpsK : List Op :=
  [.keep (fun κ => κ == .L32) 0 1, .tensorW 0 4, .packFK fun κ => if κ = .L32 then [2, 3] else [2], .eqPt 6 6]

/-- (+) The kind mux: the `keep` and the `packFK` get per-kind slots, `tensorW` and `eqPt` the
kind-muxed keys with the kinds' lengths; (−) without a route both stay untracked (no per-kind
slot) and the two ops are imports; a `keep` on one type is left to `opOut`. -/
theorem tplExtKM_ctl :
    ((compileFromX (tplExt4 keys41 .seg ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).slotK 4 .L32).map (·.1) = some (.ak 2) ∧
      ((compileFromX (tplExt4 keys41 .seg ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).slotK 4 .N30).map (·.1) = some (.ak 1) ∧
      ((compileFromX (tplExt4 keys41 .seg ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).slotK 6 .P30).map (·.1) = some (.af 1) ∧
      (compileFromX (tplExt4 keys41 .seg ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).tins.map (·.1) = [.eqPtK [(2, 2), (1, 1), (1, 1)], .tensorWK [2, 1, 1]] ∧
      (compileFromX (tplExt4 keys41 .imp ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).tins.isEmpty = true ∧
      (compileFromX (tplExt4 keys41 .imp ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).kslots.isEmpty = true ∧
      (compileFromX (tplExt4 keys41 .imp ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) ⟨[], fun _ => []⟩ ctlCSK
        ctlOpsK).imp.length = 2 ∧
      (tplExtKM keys41 ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩ ⟨[], fun _ => []⟩ ctlCSK
        (.keep (fun κ => κ == .L32) 0 0)).isNone = true := by
  decide +kernel

/-- (−) A kind-muxed register has no kind-free slot: `keepK` differs between kinds (so `RepS` of
one slot cannot hold at every kind; hence `slotK` and `ExtOkK`). -/
theorem keepK_ctl :
    (keepK ctlCSK (fun κ => κ == .L32) 0 1 .L32).map (·.1) = some (.ak 2) ∧
      (keepK ctlCSK (fun κ => κ == .L32) 0 1 .P30).map (·.1) = some (.ak 1) := by
  decide +kernel

end Circ
end FR
