-- New for `flock-recursive` (BLUEPRINT A.11, §4.3, stage S-E3; track L-circ).
import FRVIRTemplates
import FRVIRTplTab
import FRVIRTplLag
import FRVIRTplRep
import FRVIRCompileSound
import FRVIRTplMask
import FRVIRTplWalk

/-!
# `compileT`: the compiler with the replay templates, and `compileT_sound`

BLUEPRINT A.11. `tplExt` routes each structured op whose operands have the template's types to its
template (`tplOf`): the op's result slots are the template's output forms at the instance's cells
(`outSlots`), and the instance (key, input forms) is recorded; its rows are `Tpl.instRows`.
**`tplExt_ok`**: the extension is sound for every `impl` whose fields are `implC`'s on the
templated ops (`ImplT`): an instance's rows give the gate equations (`inst_eqns`), which give the
op's value (`tplX_ok`). So **`compileT_sound`** (`compileX_sound` at `tplExt`) has as import
hypotheses only the ops left without a template, plus the auxiliary imports (trace cells, L bits).

**The layout** (A.11's alignment): a first pass (`cb = 0`) counts each key's instances; the groups
are then laid out after the skeleton's cells and rows, each instance region `2^b` cells and `2^a`
rows (`Tpl.cbits`, `Tpl.rbits`), aligned (`mkLay`). Soundness does not depend on the layout
(overlapping regions only constrain more); the counts and the evaluator use it.
-/

namespace FR
namespace Circ
open Tpl RecursionFast

/-! ## The template table -/

/-- The node's walk template (`rowW′`, `colW` of `2^14` entries), computed once. -/
def tplWalk14 : Tpl := tplWalkG (2 ^ 14) (2 ^ 14)

/-- `walkAB`'s template at operand sizes `n`, `m` (the node's from the closed term). -/
def tplWalkOf (n m : ℕ) : Tpl := if n = 2 ^ 14 ∧ m = 2 ^ 14 then tplWalk14 else tplWalkG n m

theorem tplWalkOf_eq (n m : ℕ) : tplWalkOf n m = tplWalkG n m := by
  unfold tplWalkOf; split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

/-- **The templates** by key (A.11's table; keys without a template yet have none). -/
def tplOf : TKey → Tpl
  | .eqPt n m => tplEqPt n m
  | .shiftEq n m => tplShiftEq n m
  | .phiRS n => tplPhiRS n
  | .zero => tplZero
  | .targetS n => tplTargetS n
  | .slotW s n m => tplSlotW s n m
  | .maskRows n m => tplMaskRows n m
  | .eqZ => tplEqZ
  | .lagrangeS n m => tplLagrangeS n m
  | .eqTableK v => tplEqTableK v
  | .dotKF n => tplDotKF n
  | .tensorW n => tplTensorW n
  | .rowW _ => tplRowW
  | .shiftMask n m => tplShiftMask n m
  | .walkAB n m => tplWalkOf n m
  | _ => ⟨[], []⟩

/-! ## The walk template's rows and sizes, computed once (S-E11: plan time) -/

def tplWalk14Rows : List RowT := tplWalk14.rows
def tplWalk14RB : ℕ := tplWalk14.rbits
def tplWalk14CB : ℕ := tplWalk14.cbits
def tplWalk14NL : ℕ := nlocs tplWalk14.gates

/-- The node's walk key. -/
def isWalk14 : TKey → Bool
  | .walkAB n m => n == 2 ^ 14 && m == 2 ^ 14
  | _ => false

/-- A key's template rows (the walk's from the closed term). -/
def tRows (k : TKey) : List RowT := if isWalk14 k then tplWalk14Rows else (tplOf k).rows
/-- A key's row bits. -/
def tRbits (k : TKey) : ℕ := if isWalk14 k then tplWalk14RB else (tplOf k).rbits
/-- A key's cell bits. -/
def tCbits (k : TKey) : ℕ := if isWalk14 k then tplWalk14CB else (tplOf k).cbits
/-- A key's locals. -/
def tNlocs (k : TKey) : ℕ := if isWalk14 k then tplWalk14NL else nlocs (tplOf k).gates

theorem tplOf_walk14 {k : TKey} (h : isWalk14 k = true) : tplOf k = tplWalk14 := by
  cases k <;> simp [isWalk14] at h
  obtain ⟨rfl, rfl⟩ := h
  show tplWalkOf _ _ = _
  unfold tplWalkOf
  rw [if_pos ⟨rfl, rfl⟩]

theorem tRows_eq (k : TKey) : tRows k = (tplOf k).rows := by
  unfold tRows; split_ifs with h
  · rw [tplOf_walk14 h]; rfl
  · rfl

theorem tRbits_eq (k : TKey) : tRbits k = (tplOf k).rbits := by
  unfold tRbits; split_ifs with h
  · rw [tplOf_walk14 h]; rfl
  · rfl

/-- **A layout**: per key, the group's row base (relative to the slot), cell base and cell bits. -/
abbrev TLay := List (TKey × ℕ × ℕ × ℕ)

/-- The cell base of instance `i` of key `k`. -/
def TLay.cb (L : TLay) (k : TKey) (i : ℕ) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, _, c, b) => c + i * 2 ^ b
  | none => 0

/-- The context of a layout. -/
def TLay.ctx (L : TLay) : TCtx := ⟨tplOf, L.cb⟩

/-! ## The extension -/

/-- A slot's components. -/
def comps : Slot → List Lin
  | some (_, ls) => ls
  | none => []

/-- The output slots of an instance: the types `tys`, the template's outputs split by length. -/
def outSlots (one : Lin) (ins : List Lin) (cb : ℕ) : List Ty → List LinT → List Slot
  | [], _ => []
  | t :: ts, os =>
    some (t, (os.take t.len).map (instLin one ins cb)) :: outSlots one ins cb ts (os.drop t.len)

/-- A template instance's contribution: no rows of its own (they are the instance's). -/
def tplOut (tc : TCtx) (P : Params) (cs : CS) (k : TKey) (ins : List Lin) (tys : List Ty) : Out :=
  { slots := outSlots P.one ins (tc.cb k (cs.tcount k)) tys (tc.tpl k).outs, tin := some (k, ins) }

/-- **`tplExt`**: the templated ops, at their operands' types. -/
def tplExt (tc : TCtx) : Ext := fun P cs op =>
  match op with
  | .eqPt a b =>
    match cs.slot a, cs.slot b with
    | some (.af n, la), some (.af m, lb) => some (tplOut tc P cs (.eqPt n m) (la ++ lb) [.f])
    | _, _ => none
  | .shiftEq a b =>
    match cs.slot a, cs.slot b with
    | some (.af n, la), some (.af m, lb) => some (tplOut tc P cs (.shiftEq n m) (la ++ lb) [.f])
    | _, _ => none
  | .phiRS r a =>
    match cs.slot r, cs.slot a with
    | some (.af n, lr), some (.f, la) => some (tplOut tc P cs (.phiRS n) (lr ++ la) [.f])
    | _, _ => none
  | .kindFoldWeight .. => some (tplOut tc P cs .zero [] [.f])
  -- `linkWAll` (revision 3.14): an import until `tplLinkWAll` (S-E)
  | .shiftMask t r =>
    match cs.slot t, cs.slot r with
    | some (.af n, lt), some (.af m, lr) =>
      some (tplOut tc P cs (.shiftMask n m) (lt ++ lr) [.f, .f, .f])
    | _, _ => none
  -- `targetS` is the node's at a node kind (S-CN's `targetSNodeI`) and the leaf's otherwise, so
  -- the leaf template no longer serves every kind: an import until `tplTargetSNode` (S-E6)
  -- the walk as the node's own XOR DAG (revision 3.15)
  | .walkAB r c =>
    match cs.slot r, cs.slot c with
    | some (.af n, lr), some (.af m, lc) => some (tplOut tc P cs (.walkAB n m) (lr ++ lc) [.f, .f])
    | _, _ => none
  | .slotW sm t r =>
    match cs.slot t, cs.slot r with
    | some (.af n, lt), some (.af m, lr) => some (tplOut tc P cs (.slotW sm n m) (lt ++ lr) [.f])
    | _, _ => none
  | .maskRows kw rw =>
    match cs.slot kw, cs.slot rw with
    | some (.af n, lk), some (.af m, lr) => some (tplOut tc P cs (.maskRows n m) (lk ++ lr) [.af m])
    | _, _ => none
  | .eqZ l r =>
    match cs.slot l, cs.slot r with
    | some (.f, ll), some (.f, lr) => some (tplOut tc P cs .eqZ (ll ++ lr) [.af 128])
    | _, _ => none
  | .lagrangeS v l pe =>
    match cs.slot v, cs.slot l, cs.slot pe with
    | some (.af n, lv), some (.f, ll), some (.af m, lp) =>
      some (tplOut tc P cs (.lagrangeS n m) (lv ++ ll ++ lp) [.f, .f])
    | _, _, _ => none
  | .eqTableK r =>
    match cs.slot r with
    | some (.ak n, lr) => some (tplOut tc P cs (.eqTableK n) lr [.ak (2 ^ n)])
    | _ => none
  | .dotKF w col =>
    match cs.slot w with
    | some (.ak n, lw) =>
      -- the column's `n` F elements: auxiliary import cells (trace cells), in the instance's own
      -- cell region after the template's `2n` locals (S-E5: local to the instance)
      let cb := tc.cb (.dotKF n) (cs.tcount (.dotKF n))
      let cells := (List.range n).map fun b => Lin.cell (cb + 2 * n + b)
      some { tplOut tc P cs (.dotKF n) (lw ++ cells) [.k] with aux := [(cells, col, .felems n)] }
    | _ => none
  | .rowW lam rhi =>
    match cs.slot lam, cs.slot rhi with
    | some (.f, ll), some (.af n, lr) => some (tplOut tc P cs (.rowW n) (ll ++ lr) [.af (2 ^ 14)])
    | _, _ => none
  | .tensorW j r =>
    match cs.slot r with
    | some (.ak n, lr) =>
      if n ≤ logNMax then
        -- `j`'s 20 bits: auxiliary import cells (L bits) after the template's `5n` locals (S-E6)
        let cb := tc.cb (.tensorW n) (cs.tcount (.tensorW n))
        let cells := (List.range logNMax).map fun i => Lin.cell (cb + 5 * n + i)
        some { tplOut tc P cs (.tensorW n) (lr ++ cells) [.k] with aux := [(cells, j, .bits logNMax)] }
      else none
    | _ => none
  | _ => none

/-! ## Soundness -/

/-- **The implementation the templates mirror** (`implC`'s fields on the templated ops). -/
structure ImplT (impl : OpImpl) : Prop where
  shiftEq : impl.shiftEq = Impl.shiftEqI
  phiRS : impl.phiRS = Impl.phiRSI
  kfw : ∀ a b c, impl.kindFoldWeight a b c = 0
  eqZ : impl.eqZ = Impl.eqZI
  lagrangeS : impl.lagrangeS = Impl.lagrangeSI
  slotW : ∀ κ, impl.slotW κ = Impl.slotWI
  tensorW : impl.tensorW = Impl.tensorWI
  rowW : impl.rowW = Impl.rowWI
  shiftMask : impl.shiftMask = NodeI.shiftMaskI
  walkAB : impl.walkAB = Eval.walkImpl

theorem outSlots_length (one : Lin) (ins : List Lin) (cb : ℕ) :
    ∀ (tys : List Ty) (os : List LinT), (outSlots one ins cb tys os).length = tys.length
  | [], _ => rfl
  | _ :: ts, os => by simp [outSlots, outSlots_length one ins cb ts]

theorem inpIs_of {w : Asg} {one : Lin} {cb : ℕ} {ins : List Lin} {xs : List F}
    (h : ins.map (Lin.ev w) = xs) : InpIs (envOf w one ins cb) xs := fun i => getD_ev h i

/-- One output: the template's outputs are the value's encoding. -/
theorem outSlots_one {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {t : Ty} {os : List LinT}
    {v : Val} (hv : tyOf v = some t) (ho : os.map (LinT.ev (envOf w one ins cb)) = encV v) :
    List.Forall₂ (RepS w) (outSlots one ins cb [t] os) [v] := by
  have hl : os.length = t.len := by rw [← encV_length hv, ← ho, List.length_map]
  simp only [outSlots, List.forall₂_cons, List.Forall₂.nil, and_true, RepS, hv, true_and,
    List.take_of_length_le hl.le, List.map_map]
  rw [← ho]; exact List.map_congr_left fun l _ => by simp only [Function.comp_apply, instLin_ev]

/-- Two outputs. -/
theorem outSlots_two {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {t₁ t₂ : Ty} {os : List LinT}
    {v₁ v₂ : Val} (hv₁ : tyOf v₁ = some t₁) (hv₂ : tyOf v₂ = some t₂)
    (ho : os.map (LinT.ev (envOf w one ins cb)) = encV v₁ ++ encV v₂) :
    List.Forall₂ (RepS w) (outSlots one ins cb [t₁, t₂] os) [v₁, v₂] := by
  have hl := congrArg List.length ho
  rw [List.length_map, List.length_append, encV_length hv₁, encV_length hv₂] at hl
  have h1 : (os.take t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₁ := by
    rw [List.map_take, ho, List.take_left' (encV_length hv₁)]
  have h2 : (os.drop t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₂ := by
    rw [List.map_drop, ho, List.drop_left' (encV_length hv₁)]
  have := outSlots_one (one := one) (ins := ins) (cb := cb) hv₂ h2
  simp only [outSlots] at this ⊢
  refine List.Forall₂.cons ⟨hv₁, ?_⟩ this
  rw [← h1, List.map_map]; exact List.map_congr_left fun l _ => by simp only [Function.comp_apply, instLin_ev]

/-- Three outputs. -/
theorem outSlots_three {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {t₁ t₂ t₃ : Ty}
    {os : List LinT} {v₁ v₂ v₃ : Val} (hv₁ : tyOf v₁ = some t₁) (hv₂ : tyOf v₂ = some t₂)
    (hv₃ : tyOf v₃ = some t₃)
    (ho : os.map (LinT.ev (envOf w one ins cb)) = encV v₁ ++ encV v₂ ++ encV v₃) :
    List.Forall₂ (RepS w) (outSlots one ins cb [t₁, t₂, t₃] os) [v₁, v₂, v₃] := by
  have h1 : (os.take t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₁ := by
    rw [List.map_take, ho, List.append_assoc, List.take_left' (encV_length hv₁)]
  have h2 : (os.drop t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₂ ++ encV v₃ := by
    rw [List.map_drop, ho, List.append_assoc, List.drop_left' (encV_length hv₁)]
  have := outSlots_two (one := one) (ins := ins) (cb := cb) hv₂ hv₃ h2
  simp only [outSlots] at this ⊢
  refine List.Forall₂.cons ⟨hv₁, ?_⟩ this
  rw [← h1, List.map_map]; exact List.map_congr_left fun l _ => by simp only [Function.comp_apply, instLin_ev]

theorem eqStepL_length (l : List K) : ∀ t : List K, (l.foldl eqStepL t).length = t.length * 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih => intro t; simp [ih, eqStepL, pow_succ]; ring

theorem eqTab_size (r : Array K) : (eqTab r).size = 2 ^ r.size := by
  rw [← Array.length_toList, eqTab_toList, eqStepL_length]; simp

/-- An `AK` operand. -/
theorem rep_ak {w : Asg} {n : ℕ} {ls : List Lin} {v : Val} (h : RepS w (some (.ak n, ls)) v) :
    ∃ x : Array K, v = .ak x ∧ x.size = n ∧ ls.map (Lin.ev w) = x.toList.flatMap encK := by
  obtain ⟨h1, h2⟩ := h
  rcases v with _ | _ | _ | _ | _ | _ | _ | x | _ <;> simp [tyOf] at h1
  exact ⟨x, rfl, h1, h2⟩

/-- An `AF` operand: its value is an array of that size, its forms evaluate to the elements. -/
theorem rep_af {w : Asg} {n : ℕ} {ls : List Lin} {v : Val} (h : RepS w (some (.af n, ls)) v) :
    ∃ x : Array F, v = .af x ∧ x.size = n ∧ ls.map (Lin.ev w) = x.toList := by
  obtain ⟨h1, h2⟩ := h
  rcases v with _ | _ | _ | _ | _ | _ | x | _ | _ <;> simp [tyOf] at h1
  exact ⟨x, rfl, h1, h2⟩

theorem rep_f {w : Asg} {ls : List Lin} {v : Val} (h : RepS w (some (.f, ls)) v) :
    ∃ x : F, v = .f x ∧ ls.map (Lin.ev w) = [x] := by
  obtain ⟨h1, h2⟩ := h
  rcases v with x | _ | _ | _ | _ | _ | _ | _ | _ <;> simp [tyOf] at h1
  exact ⟨x, rfl, h2⟩

/-- The slot of a register (from the invariant). -/
theorem rep_slot {w : Asg} {cs : CS} {regs : Array Val} (hI : ∀ i, RepS w (cs.slot i) (rd regs i))
    {a : ℕ} {s : Slot} (h : cs.slot a = s) : RepS w s (rd regs a) := h ▸ hI a

/-- The instance's gate equations from its rows. -/
theorem tin_eqns {tc : TCtx} {P : Params} {cs : CS} {w : Asg} (hone : P.one.ev w = 1) {k : TKey}
    {ins : List Lin} {tys : List Ty}
    (h : ∀ t ∈ (tplOut tc P cs k ins tys).tin, ∀ r ∈ instRows tc P.one (t.1, cs.tcount t.1, t.2),
      r.Holds w) :
    Eqns (envOf w P.one ins (tc.cb k (cs.tcount k))) (tc.tpl k).gates 0 :=
  inst_eqns hone ins _ (tc.tpl k) fun r hr =>
    h (k, ins) rfl _ (List.mem_map.2 ⟨r, hr, rfl⟩)

/-- **`tplExt` is sound** (A.11's `tplX_sound` for every templated op). -/
theorem tplExt_ok {impl : OpImpl} (hT : ImplT impl) (L : TLay) : ExtOk impl L.ctx (tplExt L.ctx) := by
  intro P cs op o hX
  cases op <;> simp only [tplExt] at hX
  case eqPt a b =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n la m lb ha hb
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ha)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hb)
    rw [hx, hy]
    exact outSlots_one rfl (tplEqPt_ok hP.1 (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case shiftEq a b =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n la m lb ha hb
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ha)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hb)
    rw [hx, hy, hT.shiftEq]
    exact outSlots_one rfl (tplShiftEq_ok hP.1 (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case phiRS r a =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lr la hr ha
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hr)
    obtain ⟨y, hy, hyl⟩ := rep_f (rep_slot hI ha)
    rw [hx, hy, hT.phiRS]
    exact outSlots_one rfl (tplPhiRS_ok (inpIs_of (by simp [hxl, hyl, Val.toF])) (tin_eqns hP.1 ht))
  case slotW sm t r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lt m lr ht' hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ht')
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy, hT.slotW]
    exact outSlots_one rfl (tplSlotW_ok hP.1 sm (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case maskRows kw rw =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lk m lr hk hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hk)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy]
    exact outSlots_one (by simp [tyOf, maskRows, Val.toAF])
      (tplMaskRows_ok (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case eqZ l r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i ll lr hl hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, hxl⟩ := rep_f (rep_slot hI hl)
    obtain ⟨y, hy, hyl⟩ := rep_f (rep_slot hI hr)
    rw [hx, hy, hT.eqZ]
    exact outSlots_one (by simp [tyOf, eqZI_size])
      (tplEqZ_ok hP.1 (inpIs_of (by simp [hxl, hyl, Val.toF])) (tin_eqns hP.1 ht))
  case lagrangeS v l pe =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lv ll m lp hv hl hp
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hv)
    obtain ⟨y, hy, hyl⟩ := rep_f (rep_slot hI hl)
    obtain ⟨z, hz, rfl, hzl⟩ := rep_af (rep_slot hI hp)
    rw [hx, hy, hz, hT.lagrangeS]
    exact outSlots_two rfl rfl (tplLagrangeS_ok hP.1
      (inpIs_of (by simp [hxl, hyl, hzl, Val.toF, Val.toAF])) (tin_eqns hP.1 ht))
  case eqTableK r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lr hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_ak (rep_slot hI hr)
    rw [hx]
    exact outSlots_one (by simp [tyOf, Val.toAK, eqTab_size])
      (tplEqTableK_ok hP.1 (inpIs_of hxl) (tin_eqns hP.1 ht))
  case dotKF w col =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lw hw
    refine ⟨rfl, fun κ inp ww regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht hx vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx', rfl, hxl⟩ := rep_ak (rep_slot hI hw)
    have hc := hx _ (List.mem_singleton_self _)
    simp only [Tpl.AuxK.val] at hc
    rw [hx', dotKFF_eq]
    exact outSlots_one rfl (tplDotKF_ok rfl (inpIs_of (by rw [List.map_append, hxl, hc]; rfl))
      (tin_eqns (tc := L.ctx) (k := .dotKF x.size) (tys := [.k]) hP.1 ht))
  case rowW lam rhi =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i ll n lr hl hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, hxl⟩ := rep_f (rep_slot hI hl)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy, hT.rowW]
    exact outSlots_one (by simp [tyOf, rowWI_size])
      (tplRowW_ok hP.1 (inpIs_of (by simp [hxl, hyl, Val.toF, Val.toAF])) (tin_eqns hP.1 ht))
  case shiftMask t r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lt m lr ht' hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ht')
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy, hT.shiftMask]
    exact outSlots_three rfl rfl rfl
      (tplShiftMask_ok (inpIs_of (by simp [hxl, hyl])) hP.1 (tin_eqns hP.1 ht))
  case walkAB r c =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lr m lc hr hc
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hr)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hc)
    rw [hx, hy, hT.walkAB]
    have he := tin_eqns hP.1 ht
    have hg : (L.ctx.tpl (.walkAB x.size y.size)) = tplWalkG x.size y.size := by
      simp only [TLay.ctx, tplOf, tplWalkOf_eq]
    rw [hg] at he
    have ho := tplWalkAB_ok (inpIs_of (by simp [hxl, hyl])) he
    rw [← hg] at ho
    exact outSlots_two rfl rfl ho
  case tensorW j r =>
    split at hX
    · rename_i n lr hr
      split_ifs at hX with hn
      · simp only [Option.some.injEq] at hX; subst hX
        refine ⟨rfl, fun κ inp ww regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht hx vs ok he => ?_⟩⟩
        simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        obtain ⟨x, hx', rfl, hxl⟩ := rep_ak (rep_slot hI hr)
        have hc := hx _ (List.mem_singleton_self _)
        simp only [Tpl.AuxK.val] at hc
        rw [hx', hT.tensorW]
        exact outSlots_one rfl (tplTensorW_ok hP.1 hn
          (inpIs_of (by rw [List.map_append, hxl, hc]))
          (tin_eqns (tc := L.ctx) (k := .tensorW x.size) (tys := [.k]) hP.1 ht))
    · simp at hX
  all_goals first
    | (simp at hX; done)
    | skip
  case kindFoldWeight r b ρ =>
    obtain rfl := Option.some.inj hX
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ _ _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rw [hT.kfw]
    exact ⟨fun _ => outSlots_one rfl tplZero_ok, fun _ => rfl⟩

/-! ## `compileT` and `compileT_sound` -/

/-- **`compileT`**: `compile` with the templates at layout `L`. -/
def compileT (L : TLay) (P : Params) (base : ℕ) (ops : List Op) : CS :=
  compileX (tplExt L.ctx) P base ops

/-- **`compileT_sound`** (A.11): with `ImplT`, the template instances' rows and the auxiliary
imports, the import hypotheses left are those of the ops without a template (and the trace / L /
public imports of the skeleton): the run accepts and every tracked register is represented. -/
theorem compileT_sound {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} (hT : ImplT impl) (L : TLay) (base : ℕ) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileT L P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileT L P base ops).tplRows L.ctx P.one, r.Holds w)
    (hx : ∀ a ∈ (compileT L P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (compileT L P base ops).imp,
      RepS w ((compileT L P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileT L P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileT L P base ops).slot i) (rd s.regs i) :=
  compileX_sound (tplExt_ok hT L) base hP he hr ht hx hi hf

/-! ## The layout -/

/-- The keys in order of first appearance, with their instance counts. -/
def keyCounts (tins : List (TKey × ℕ × List Lin)) : List (TKey × ℕ) :=
  tins.reverse.foldl (fun acc t => if acc.any (·.1 == t.1) then
    acc.map fun p => if p.1 == t.1 then (p.1, p.2 + 1) else p else acc ++ [(t.1, 1)]) []

/-- A key's cell region bits: its template's locals and, for `dotKF`, the column cells after them. -/
def cregion (k : TKey) : ℕ :=
  match k with
  | .dotKF n => max (tplOf k).cbits (Nat.size (3 * n + 1))
  | .tensorW n => max (tplOf k).cbits (Nat.size (5 * n + logNMax))
  | _ => tCbits k

/-- The walk's blocks (`G` gadgets at a `2^gBits` stride): its rows and cells are aligned to the
block, and the next group's cells start after its last local (S-E10). -/
def isWalk : TKey → Bool
  | .walkAB .. => true
  | _ => false

/-- **A split template** (S-E11, changes 22 (b)): its first `2^a` rows (the head) and the rest (the
tail, at most `2^b` rows) are laid out in two aligned blocks, so that an instance takes
`2^a + 2^b` rows instead of `2^(a+1)`: `phiRS 7` (134 rows) takes `128 + 8`. -/
def splitOf : TKey → Option (ℕ × ℕ)
  | .phiRS n => if 4 ≤ n then some (n, Nat.size (n - 2)) else none
  | _ => none

/-- **The row of a split instance**: groups of `g = 2^(a−b)` instances, each group `g` heads then
`g` tails (`(g + 1)·2^a` rows); instance `i`'s row `j`. -/
def splitRow (a b i j : ℕ) : ℕ :=
  let g := 2 ^ (a - b)
  i / g * ((g + 1) * 2 ^ a) + if j < 2 ^ a then i % g * 2 ^ a + j else g * 2 ^ a + i % g * 2 ^ b + (j - 2 ^ a)

/-- (+) `phiRS 7` is split as 128 + 8 rows; instance 0's tail follows the group's 16 heads, instance
16 starts the next group of `17 · 128` rows. -/
theorem splitRow_phi : splitOf (.phiRS 7) = some (7, 3) ∧ splitRow 7 3 0 128 = 2048 ∧
    splitRow 7 3 15 133 = 2173 ∧ splitRow 7 3 16 0 = 2176 := by
  refine ⟨by simp only [splitOf]; decide, ?_, ?_, ?_⟩ <;> norm_num [splitRow]

/-- (−) Other keys keep the `2^rbits` stride. -/
theorem splitOf_walk (n m : ℕ) : splitOf (.walkAB n m) = none := rfl

/-- **The layout** from the counts: groups after the skeleton's rows `r0` and cells `c0`, each
aligned to its instance size. -/
def mkLay (r0 c0 : ℕ) : List (TKey × ℕ) → TLay
  | [] => []
  | (k, n) :: ks =>
    -- the template's rows once (S-E11: plan time); `Nat.size (nr − 1)` is `Tpl.rbits`
    let nr := (tRows k).length; let rbk := Nat.size (nr - 1); let cr := cregion k
    -- a template of more than `2^12` rows is evaluated in 64-row chunks (`FRVIRTplPlan.tinPP`),
    -- so its rows need only 64-row alignment (S-E6); the walk's in `2^gBits` blocks (S-E10)
    let rb := alignUp r0 (match splitOf k with
      | some (a, _) => a
      | none => if isWalk k then gBits else if 12 < rbk then 6 else rbk)
    let cb := alignUp c0 (if isWalk k then gBits else cr)
    -- the next group starts after the last instance's rows, not its whole aligned region (S-E6);
    -- a split template's instances take `(g + 1)·2^a` rows per group of `g` (S-E11)
    let re := match splitOf k with
      | some (a, b) => rb + (n + 2 ^ (a - b) - 1) / 2 ^ (a - b) * ((2 ^ (a - b) + 1) * 2 ^ a)
      | none => rb + (n - 1) * 2 ^ rbk + nr
    (k, rb, cb, cr) :: mkLay re
      (if isWalk k then cb + (n - 1) * 2 ^ cr + tNlocs k else cb + n * 2 ^ cr) ks

/-- **The two-pass compile**: count with the zero layout, lay the groups out, compile again. -/
def layOf (P : Params) (base : ℕ) (ops : List Op) : TLay :=
  let cs := compileT [] P base ops
  mkLay cs.nrows cs.next (keyCounts cs.tins)

end Circ
end FR
