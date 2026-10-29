-- New for `flock-recursive` (track B3): controls for `FRNodeRun4`/`FRNodeRun4S`.
import FRNodeRun4S

/-!
# Controls for the run's existence

* `execA` against `exec`: on a trace whose query is wrong the answer-driven run exists and `exec`
  fails (`execA_ne_exec`), so `ATOk` carries the content; `execA_of_exec` (in `FRNodeRun4`) is the
  converse.
* `ATOk`: with no rows it holds on the empty trace (`atOk_nil`) and fails on an entry the program
  does not ask (`atOk_none_neg`).
* **A sound ask template** (`pinSq`, one squeeze of the `input` before it) and **`compileX_run` on a
  program with an ask** (`run_ctl`): every hypothesis is met at a concrete assignment and the run
  exists (+); the same template on a wrong trace is not sound (`pinSq_neg`, −).
-/

namespace FR
namespace Circ
open RecursionFast

/-- The selector forms of kind `L32` with `one` at cell `0`. -/
def pCtl : Params := fixedP (Lin.cell 0) .L32

/-- The control's assignment: cell `0` is `1`, every other `0`. -/
def wCtl : Asg := fun i => if i = 0 then 1 else 0

theorem selOk_ctl : SelOk wCtl pCtl .L32 :=
  ⟨by simp [pCtl, fixedP, wCtl], fun κ' => by cases κ' <;> simp [pCtl, fixedP, wCtl]⟩

theorem invK_init (w : Asg) (κ : Kind) (b : ℕ) : InvK w (CS.init b) #[] κ :=
  ⟨⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩, fun p hp => by simp [CS.init] at hp,
    fun i => by simp [CS.slotK, CS.slot, CS.init, RepS]⟩

theorem squeezeQ_ne_empty (d : Digest) : squeezeQ d ≠ ByteArray.empty := fun h => by
  have h1 := congrArg (fun b : ByteArray => b.data.toList.length) h
  simp [squeezeQ, bytesOf] at h1

/-- The control's input (`vk = c = 0^32`, an empty proof). -/
def inpCtl : Input := ⟨zeroD, zeroD, ByteArray.empty⟩

/-! ## `execA` is not `exec` -/

/-- (−) **The answer-driven run ignores the query**: on an entry with the wrong query it runs,
`exec` does not. -/
theorem execA_ne_exec (impl : OpImpl) :
    (execA impl .L32 inpCtl [.askSqueeze 0] St.init [(ByteArray.empty, zeroD)]).isSome = true ∧
      exec impl .L32 inpCtl [.askSqueeze 0] St.init [(ByteArray.empty, zeroD)] = none := by
  refine ⟨rfl, ?_⟩
  simp only [exec, evalOp]
  rw [if_neg (fun h => squeezeQ_ne_empty _ h.symm)]

/-! ## `ATOk` without rows -/

/-- (+) With no entries, no ask is constrained. -/
theorem atOk_nil (impl : OpImpl) (X : Ext) (κ : Kind) (inp : Input) (w : Asg) :
    ATOk impl X AT.none κ inp w [] :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ he => by simp at he, fun _ _ _ _ _ _ _ _ hc => by simp [AT.none] at hc⟩

/-- (−) **Rows are needed**: with none, an entry the program does not ask breaks `ATOk`. -/
theorem atOk_none_neg (impl : OpImpl) (X : Ext) :
    ¬ ATOk impl X AT.none .L32 inpCtl wCtl [(ByteArray.empty, zeroD)] := fun h => by
  have := (h.1 pCtl (CS.init 0) none (.askSqueeze 0) 0 #[] _ _
    ⟨selOk_ctl, invK_init wCtl .L32 0, trivial, fun r hr => by simp [AT.none] at hr⟩ rfl rfl).1
  exact squeezeQ_ne_empty _ this.symm

/-! ## A sound ask template, and the run of a program with an ask -/

/-- The squeeze's state register, if `op` is a squeeze. -/
def sqSt? : Op → Option ℕ
  | .askSqueeze st => some st
  | _ => none

/-- Whether the previous op is `input 0`. -/
def isVk : Option Op → Bool
  | some (.input 0) => true
  | _ => false

theorem sqSt?_eq {op : Op} {st : ℕ} (h : sqSt? op = some st) : op = .askSqueeze st := by
  cases op <;> simp [sqSt?] at h; rw [h]

theorem isVk_eq {pre : Option Op} (h : isVk pre = true) : pre = some (.input 0) := by
  rcases pre with _ | ⟨_ | _⟩ <;> simp_all [isVk]
  all_goals (rename_i n; cases n <;> simp_all [isVk])

/-- The row `0 · 0 = one` (it fails where `one = 1`). -/
def rejRow (P : Params) : Row := ⟨[], [], P.one⟩

/-- **A template for one squeeze of `vk`** (entry `0`): the squeeze must read the `input 0` just
before it; its answer cells are pinned to `a`. Anything else gets a failing row. -/
def pinSq (a : Digest) : AT where
  cov _ := false
  rows P cs pre op k :=
    match sqSt? op with
    | some st =>
      if isVk pre ∧ k = 0 ∧ st + 1 = cs.slots.size then
        [⟨P.one, cs.cell 0, P.one.smul (dlo a)⟩, ⟨P.one, cs.cell 1, P.one.smul (dhi a)⟩]
      else [rejRow P]
    | none => [rejRow P]

theorem rej_false {w : Asg} {P : Params} {κ : Kind} (hP : SelOk w P κ) : ¬ (rejRow P).Holds w := by
  simp [rejRow, Row.Holds, hP.1]

theorem stepOut_sq (P : Params) (cs : CS) (st : ℕ) :
    (stepOut noExt P cs (.askSqueeze st)).slots = [some (.d, [cs.cell 0, cs.cell 1])] := by
  simp [stepOut, noExt, opOut, imports, impSlots, Ty.len, List.range_succ]

/-- (+) **`pinSq` is sound** for the trace `[(squeezeQ vk, a)]`. -/
theorem pinSq_ok (impl : OpImpl) (κ : Kind) (inp : Input) (w : Asg) (a : Digest) :
    ATOk impl noExt (pinSq a) κ inp w [(squeezeQ inp.vk, a)] := by
  refine ⟨?_, fun _ _ _ _ _ _ _ _ hc => by simp [pinSq] at hc⟩
  intro P cs pre op k regs q e ⟨hP, hI, hpv, hrows⟩ hq he
  rcases hs : sqSt? op with _ | st
  · exact absurd (hrows _ (by simp [pinSq, hs])) (rej_false hP)
  obtain rfl := sqSt?_eq hs
  by_cases hc : isVk pre = true ∧ k = 0 ∧ st + 1 = cs.slots.size
  swap
  · exact absurd (hrows _ (by simp [pinSq, sqSt?, hc])) (rej_false hP)
  obtain ⟨hv, rfl, hsz⟩ := hc
  obtain rfl := isVk_eq hv
  simp only [List.getElem?_cons_zero, Option.some.injEq] at he
  subst he
  have hr : ∀ r ∈ [(⟨P.one, cs.cell 0, P.one.smul (dlo a)⟩ : Row), ⟨P.one, cs.cell 1, P.one.smul (dhi a)⟩],
      r.Holds w := fun r h => hrows r (by simp only [pinSq, sqSt?, hv, hsz, and_self, if_true]; exact h)
  have h0 := hr _ (List.mem_cons_self ..)
  have h1 := hr _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [Row.Holds, Lin.ev_smul, hP.1, one_mul, mul_one] at h0 h1
  refine ⟨?_, ans_of_cells (stepOut_sq P cs st) h0 h1⟩
  simp only [evalOp, Res.ask.injEq] at hq
  subst hq
  obtain ⟨r₀, ⟨vs, ok, hev, rfl⟩ | ⟨q', a', hev, -⟩⟩ := hpv
  · simp only [evalOp, if_true, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    have hst : st = r₀.size := by
      have := hI.1.1; simp at this; omega
    subst hst
    simp [rd, Val.toD]
  · simp [evalOp] at hev

/-- The control's program: `vk`, then one squeeze of it. -/
def progCtl : List Op := [.input 0, .askSqueeze 0]

/-- (+) **`compileX_run` on a program with an ask**: with `pinSq`, at `wCtl` (`vk`'s cells and
the answer's cells `0`), every hypothesis holds and the run on `[(squeezeQ 0^32, 0^32)]` exists. -/
theorem run_ctl (impl : OpImpl) (tc : Tpl.TCtx) :
    exec impl .L32 inpCtl progCtl St.init [(squeezeQ zeroD, zeroD)] =
      some (⟨#[.d zeroD, .d zeroD], true⟩, []) := by
  have hX : ExtOkK impl tc noExt .L32 :=
    ((noExt_ok impl _).at .L32).toK fun _ _ _ _ h => by simp [noExt] at h
  have hrows : (compileX noExt pCtl 1 progCtl).rows = [] := rfl
  have htins : (compileX noExt pCtl 1 progCtl).tins = [] := rfl
  have haux : (compileX noExt pCtl 1 progCtl).aux = [] := rfl
  have hfors : (compileX noExt pCtl 1 progCtl).fors = [] := rfl
  have himp : impAX noExt pCtl RT.none (pinSq zeroD) (CS.init 1) progCtl = [0] := rfl
  have hslot : (compileX noExt pCtl 1 progCtl).slot 0 = some (.d, [Lin.cell 1, Lin.cell 2]) := rfl
  have hrep : repRowsX noExt pCtl RT.none (CS.init 1) progCtl = [] := rfl
  have hask : askRowsX noExt pCtl (pinSq zeroD) (CS.init 1) none 0 progCtl =
      [⟨Lin.cell 0, Lin.cell 3, (Lin.cell 0).smul (dlo zeroD)⟩,
        ⟨Lin.cell 0, Lin.cell 4, (Lin.cell 0).smul (dhi zeroD)⟩] := rfl
  have := compileX_run (ops := progCtl) (inp := inpCtl) (tr := [(squeezeQ zeroD, zeroD)]) (rt := RT.none) (A := pinSq zeroD) (P := pCtl) (tc := tc)
    (s := ⟨#[.d zeroD, .d zeroD], true⟩) (tr' := []) hX (RT.none_ok _ _ _)
    (pinSq_ok impl .L32 inpCtl wCtl zeroD) 1 selOk_ctl rfl (by simp [hrows])
    (by simp [CS.tplRows, htins]) (by simp [haux])
    (fun i hi => by
      rw [himp, List.mem_singleton] at hi
      subst hi; rw [hslot]
      exact ⟨rfl, by simp [encV, wCtl, rd, dlo_zero, dhi_zero]⟩)
    (by simp [hrep])
    (by rw [hask]; simp [Row.Holds, wCtl, dlo_zero, dhi_zero]) (by simp [hfors])
  exact this.1

/-- (−) **`pinSq` on a trace whose query is not the squeeze's** is not sound. -/
theorem pinSq_neg (impl : OpImpl) : ¬ ATOk impl noExt (pinSq zeroD) .L32 inpCtl wCtl [(ByteArray.empty, zeroD)] :=
  fun h => by
    let cs := (CS.init 1).add (.input 0) (stepOut noExt pCtl (CS.init 1) (.input 0))
    have hI : InvK wCtl cs #[.d zeroD] .L32 := by
      refine ⟨⟨by simp [cs, CS.add, CS.init, stepOut, noExt, opOut, imports, impSlots], fun i => ?_⟩,
        fun p hp => by simp [cs, CS.add, CS.init, stepOut, noExt, opOut, imports] at hp, fun i => ?_⟩ <;>
      rcases i with _ | i <;>
        simp [cs, CS.slotK, CS.slot, CS.add, CS.init, stepOut, noExt, opOut, imports, impSlots, Ty.len,
          RepS, rd, tyOf, encV, CS.cell, wCtl, dlo_zero, dhi_zero, List.range_succ]
    have := (h.1 pCtl cs (some (.input 0)) (.askSqueeze 0) 0 #[.d zeroD] _ _
      ⟨selOk_ctl, hI, ⟨#[], .inl ⟨[.d zeroD], true, by simp [evalOp, inpCtl], rfl⟩⟩, fun r hr => by
        simp only [pinSq, sqSt?, isVk, cs, CS.add, stepOut, noExt, opOut, imports, impSlots, CS.init] at hr
        simp at hr
        rcases hr with rfl | rfl <;>
          simp [Row.Holds, CS.cell, wCtl, pCtl, fixedP, dlo_zero, dhi_zero, Ty.len]⟩ rfl rfl).1
    exact squeezeQ_ne_empty _ this.symm

/-- A template covering `input` with no rows. -/
def covIn : AT := ⟨fun op => match op with | .input _ => true | _ => false, fun _ _ _ _ _ => []⟩

/-- An input with `vk = 1^32`. -/
def inpOne : Input := ⟨Vector.replicate 32 1, zeroD, ByteArray.empty⟩

/-- (−) **A covered import needs rows**: covering `input` without any, its fresh cells (`0` at
`wCtl`) need not carry `vk`. -/
theorem atImp_neg (impl : OpImpl) : ¬ ATImp impl noExt covIn .L32 inpOne wCtl := fun h => by
  have := h pCtl (CS.init 5) none (.input 0) 0 #[] _ _ rfl
    ⟨selOk_ctl, invK_init wCtl .L32 5, trivial, fun r hr => by simp [covIn] at hr⟩ rfl rfl
  simp [stepOut, noExt, opOut, imports, impSlots, Ty.len, List.range_succ, RepS, tyOf, encV, CS.cell,
    CS.init, wCtl] at this
  obtain ⟨h0, h1⟩ := this
  have hz : (inpOne.vk : Digest) = zeroD :=
    digest_ext (by rw [dlo_zero]; exact h0.symm) (by rw [dhi_zero]; exact h1.symm)
  exact absurd hz (by decide)

end Circ
end FR
