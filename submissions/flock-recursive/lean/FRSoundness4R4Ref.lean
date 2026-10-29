-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8, A.10; stage R4).
-- RET-2: import re-pointed at Core: `FRSoundnessAccSem` → `FRSoundnessCoreAcc`.
import FRSoundness4Qry
import FRVIRChain
import FRSoundnessCoreAcc

/-!
# The reference semantics of `gen4`'s skeleton (`refPhase4`, `exec_skeleton4`)

3.x's `exec_skeleton` (`FRVIRSpec`) is stated over 3.x's phase table and `genPhase`; revision 4.1's
programs are `gen4 S p fin` (`FRVIR4`), with their own generator `genPhase4`. This module gives
`genPhase4` its reference semantics, phase by phase, and composes them.

* **Generic run facts** (any op list): the flag factors out (`exec_ok_and`), and a run appends
  exactly `opsOut` registers and consumes one trace entry per ask (`exec_ext`).
* **`refPhase4`**: a phase's registers, flag and the rest of the trace.
  - Squeezes, the univariate round and sumcheck rounds: 3.x's references (`sqzT`, `uniVals`,
    `roundsT`) at field `0` and absolute offsets (`gen4` addresses π absolutely, `absOff 0 o = o`).
    A segment's univariate round first packs its `targetS` operand (`segPtOp`).
  - The seed and absorbs: the query (`ans1`), then the phase's ask-free tail (`seedTail4`, `absTail4`:
    `stmtOps4`, a segment's `lastOps`, `finalOps4`, the end-zero check) as a `pureRun`.
  - **A query phase is its own `exec`**: the front never reads a query phase's values; its chain
    facts need only that it consumes non-Fiat–Shamir entries and keeps `st` (`exec_ext`).
* **`exec_genPhase4`**, **`genPhase4_ctx`**, **`refPhases4`**, **`exec_skeleton4`**: 3.x's
  statements for `genPhase4`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-! ## Generic run facts -/

section Generic
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **The flag factors out of a run.** -/
theorem exec_ok_and : ∀ (ops : List Op) (r : Array Val) (ok : Bool) (tr : Trace),
    exec impl κ inp ops ⟨r, ok⟩ tr =
      (exec impl κ inp ops ⟨r, true⟩ tr).map fun x => (⟨x.1.regs, ok && x.1.ok⟩, x.2)
  | [], r, ok, tr => by simp [exec]
  | op :: ops, r, ok, tr => by
    simp only [exec]
    split
    · next vs f _ =>
      rw [exec_ok_and ops _ (ok && f), exec_ok_and ops _ (true && f), Option.map_map]
      simp [Function.comp_def, Bool.and_assoc]
    · rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · rfl
      · simp only
        split_ifs
        · rw [exec_ok_and ops _ ok, exec_ok_and ops _ true, Option.map_map]
        · rfl

theorem ask_outs {regs : Array Val} {op : Op} {q : ByteArray} (h : evalOp impl κ inp regs op = .ask q) :
    op.outs = 1 ∧ op.item?.isSome = true := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> exact ⟨rfl, rfl⟩

theorem vals_item {regs : Array Val} {op : Op} {vs : List Val} {ok : Bool}
    (h : evalOp impl κ inp regs op = .vals vs ok) : op.item? = none := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

/-- **A run appends `opsOut` registers and consumes one entry per ask.** -/
theorem exec_ext : ∀ (ops : List Op) (r : Array Val) (ok : Bool) (tr : Trace) (s : St) (tr' : Trace),
    exec impl κ inp ops ⟨r, ok⟩ tr = some (s, tr') →
    ∃ L : List Val, s.regs = r ++ L.toArray ∧ L.length = opsOut ops ∧
      ∃ seg, tr = seg ++ tr' ∧ seg.length = (ops.filterMap Op.item?).length
  | [], r, ok, tr, s, tr', h => by
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, [], rfl, rfl⟩
  | op :: ops, r, ok, tr, s, tr', h => by
    simp only [exec] at h
    split at h
    · next vs f hv =>
      obtain ⟨L, hL, hl, seg, hs, hsl⟩ := exec_ext ops _ _ tr s tr' h
      refine ⟨vs ++ L, by rw [hL]; simp [Array.append_assoc], ?_, seg, hs, ?_⟩
      · rw [List.length_append, hl, evalOp_outs_len impl κ inp _ op hv]; simp [opsOut]
      · rw [List.filterMap_cons, vals_item impl κ inp hv]; exact hsl
    · next q hq =>
      rcases tr with _ | ⟨⟨q', a⟩, tr₀⟩
      · cases h
      simp only at h
      split_ifs at h
      obtain ⟨L, hL, hl, seg, hs, hsl⟩ := exec_ext ops _ _ tr₀ s tr' h
      obtain ⟨h1, h2⟩ := ask_outs impl κ inp hq
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 h2
      refine ⟨.d a :: L, by rw [hL]; simp [Array.append_assoc], ?_, (q', a) :: seg, by rw [hs]; rfl, ?_⟩
      · simp [opsOut, h1, hl]; omega
      · rw [List.filterMap_cons, hit]; simp [hsl]

end Generic

/-! ## The reference of a phase -/

section Ref
variable (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP)

/-- The seed's ops after its query (`seedOps4` from its third op). -/
def seedTail4 (b : ℕ) : List Op := (seedOps4 p b).drop 2

/-- **An absorb phase's ops after its query**: the statement's checks (a segment's with
`lastOps`), the final message's zero padding, the ends' zero check, or nothing. -/
def absTail4 (n f b : ℕ) : List Op :=
  let o := fieldOffOf S f + phaseOffOf S n f
  if f = fStmt then
    if p.d.node then stmtOps4 p o b (b + 2)
    else stmtOps4 p o b (b + 2) ++ lastOps o (b + 2 + opsOut (stmtOps4 p o b (b + 2)))
  else if f = fFinal then finalOps4 S p o (b + 2)
  else if f = fLrEnd ∨ f = fEEnd then [.assertZero b (fun _ => !p.d.node)]
  else []

/-- The registers of a segment's `targetS` operand (`segPtOp`). -/
def segPtRegs (outs : Array (List Reg)) : List Reg :=
  ((outs.getD 3 []).drop 1).take (p.d.m - 13) ++ List.replicate (S.mStar - p.d.m) ((outs.getD 1 []).getD 1 0) ++
    (outs.getD 1 []).drop 2

theorem segPtOp_eq (outs : Array (List Reg)) : segPtOp S p outs = .packF (segPtRegs S p outs) := rfl

/-- **Reference semantics of a phase of `genPhase4`** (number `n`, context `c`, registers `r`). -/
def refPhase4 (n : ℕ) (ph : String × Sh) (c : GCtx) (r : Array Val) (tr : Trace) :
    Option (List Val × Bool × Trace) :=
  let d := (rd r c.st).toD
  let o := fun f => fieldOffOf S f + phaseOffOf S n f
  match ph.2 with
  | .seed =>
    match tr with
    | (q, a) :: tr =>
      let hdr := FR.msgAt inp 0 0 48
      if q = seedQ inp.vk inp.c hdr then
        (pureRun impl κ inp (seedTail4 p r.size) r [.b hdr, .d a]).map fun y => (y.1, y.2, tr)
      else none
    | [] => none
  | .absorb f len =>
    (ans1 (absorbQ d (FR.msgAt inp 0 (o f) len)) tr).bind fun x =>
      (pureRun impl κ inp (absTail4 S p n f r.size) r [.b (FR.msgAt inp 0 (o f) len), .d x.1]).map
        fun y => (y.1, y.2, x.2)
  | .squeezes k ch =>
    (sqzT k d tr).map fun x =>
      match ch with
      | .coords => (x.1.flatMap coordVals ++ [.af (FR.coordsOf x.1).toArray], true, x.2)
      | .one => (x.1.map .d ++ [.f (chF (x.1.headD zeroD) 0)], true, x.2)
      | .pos _ => (x.1.map .d, true, x.2)
  | .uni f =>
    match tr with
    | (q₁, a₁) :: (q₂, a₂) :: tr =>
      if q₁ = absorbQ d (FR.msgAt inp 0 (o f) uniBytes) ∧ q₂ = squeezeQ a₁ then
        if p.d.node then
          some (uniVals impl inp 0 (o f) (impl.targetS κ (rd r c.pt).toAF) a₁ a₂,
            (Val.b (FR.msgAt inp 0 (o f + 2032) 16)).isZero, tr)
        else
          let P := ((segPtRegs S p c.outs).map fun x => (rd r x).toF).toArray
          some (.af P :: uniVals impl inp 0 (o f) (impl.targetS κ P) a₁ a₂,
            (Val.b (FR.msgAt inp 0 (o f + 2032) 16)).isZero, tr)
      else none
    | _ => none
  | .rounds f k deg inK =>
    let init := initClaim ph.1
    let iv := initVals inp init 0 (o f) inK
    let cl := match init with | .uni => rd r c.uni | _ => iv.getLastD default
    (roundsT inp 0 (o f) deg inK (realRounds p ph.1 k) k 0 d cl tr).map fun x =>
      (iv ++ x.1, x.2.1, x.2.2)
  | .queries _ =>
    (exec impl κ inp (genPhase4 S p n ph c).1 ⟨r, true⟩ tr).map fun x =>
      (x.1.regs.toList.drop r.size, x.1.ok, x.2)

/-- An absorb (field `0`, absolute offset), with the state register's digest. -/
theorem exec_abs4 (o len st : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (hst : st < r.size)
    (q : ByteArray) (a : Digest) (tr : Trace) :
    exec impl κ inp (absorbOps 0 o len st r.size ++ ops) ⟨r, ok⟩ ((q, a) :: tr) =
      if q = absorbQ (rd r st).toD (FR.msgAt inp 0 o len) then
        exec impl κ inp ops ⟨r ++ [Val.b (FR.msgAt inp 0 o len), .d a].toArray, ok⟩ tr else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [absorbOps, List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ hst,
    Val.toB, rd_app0, List.getD_cons_zero, Bool.and_true]
  by_cases h : q = absorbQ (rd r st).toD (FR.msgAt inp 0 o len) <;> simp_all [FR.msgAt]

/-- The ask-free tails ask nothing. -/
theorem opsOut_seedTail4 (b : ℕ) : opsOut (seedTail4 p b) = 2 := rfl

theorem noAsk_seedTail4 (b : ℕ) : (seedTail4 p b).filterMap Op.item? = [] := rfl

theorem noAsk_absTail4 (n f b : ℕ) : (absTail4 S p n f b).filterMap Op.item? = [] := by
  unfold absTail4
  split_ifs <;> simp [List.filterMap_append, noAsk_stmtOps4, noAsk_lastOps, finalOps4, Op.item?]

/-- A pure tail after `base` on the registers `r`. -/
theorem exec_tail (o₁ ops : List Op) (r : Array Val) (base : List Val) (ok : Bool) (tr : Trace)
    (h : o₁.filterMap Op.item? = []) :
    exec impl κ inp (o₁ ++ ops) ⟨r ++ base.toArray, ok⟩ tr =
      (pureRun impl κ inp o₁ r base).bind fun y => exec impl κ inp ops ⟨r ++ y.1.toArray, ok && y.2⟩ tr := by
  obtain ⟨L, f, hp⟩ := pureRun_noAsk impl κ inp r o₁ base h
  rw [hp, Option.bind_some, exec_pureRun impl κ inp o₁ ops r base L f ok tr hp]

/-- The registers a context points to are below a file's size (3.x's `CtxOk`). -/
theorem genPhase4_absorb (n : ℕ) (name : String) (f len : ℕ) (c : GCtx) :
    (genPhase4 S p n (name, .absorb f len) c).1 =
      absorbOps 0 (fieldOffOf S f + phaseOffOf S n f) len c.st c.next ++ absTail4 S p n f c.next := by
  simp only [genPhase4, absTail4]
  split_ifs <;> simp [List.append_assoc]

/-- **Every phase's semantics** (`genPhase4`'s 3.x `exec_genPhase`): a phase's ops on a trace are
its reference `refPhase4`. -/
theorem exec_genPhase4 (n : ℕ) (ph : String × Sh) (c : GCtx) (r : Array Val) (ok : Bool) (ops : List Op)
    (hb : c.next = r.size) (hwf : ph.2 = .seed ∨ CtxOk c r) (tr : Trace) :
    exec impl κ inp ((genPhase4 S p n ph c).1 ++ ops) ⟨r, ok⟩ tr =
      (refPhase4 impl κ inp S p n ph c r tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  obtain ⟨name, sh⟩ := ph
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hwf; subst hb
  have e0 : ∀ ok', (⟨r, ok'⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok'⟩ := fun _ => by simp
  cases sh with
  | seed =>
    simp only [genPhase4, refPhase4]
    rw [show seedOps4 p r.size = [.piField 0 0 48, .askSeed r.size] ++ seedTail4 p r.size from rfl,
      List.append_assoc, e0]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp only [List.cons_append, List.nil_append, exec_app, evalOp]
      rfl
    · simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app0, List.getD_cons_zero,
        Val.toB, Bool.and_true]
      by_cases h : q = seedQ inp.vk inp.c (FR.msgAt inp 0 0 48)
      · simp only [FR.msgAt] at h
        simp only [h, ite_true, FR.msgAt, Array.append_empty]
        erw [exec_tail impl κ inp _ _ r [_, _] _ _ (noAsk_seedTail4 p _), Option.bind_map]
        rfl
      · simp only [FR.msgAt] at h
        simp [h, FR.msgAt]
  | absorb f len =>
    have hst : st < r.size := (hwf.resolve_left (by simp)).1
    rw [genPhase4_absorb, List.append_assoc]
    simp only [refPhase4]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · rw [e0]; simp only [absorbOps, List.cons_append, exec_app, evalOp, List.nil_append]; rfl
    · rw [exec_abs4 impl κ inp _ _ _ r ok _ hst]
      simp only [ans1]
      split_ifs with h
      · simp only [Option.bind_some]
        rw [exec_tail impl κ inp _ _ _ _ _ _ (noAsk_absTail4 S p _ _ _), Option.bind_map]
        rfl
      · rfl
  | squeezes k ch =>
    have hst : st < r.size := (hwf.resolve_left (by simp)).1
    cases ch with
    | coords =>
      simp only [genPhase4, refPhase4, List.append_assoc]
      rw [exec_sqzC impl κ inp k st r ok _ hst, Option.bind_map]
      refine Option.bind_congr fun x hx => ?_
      rw [show 2 * k = 2 * x.1.length by rw [sqzT_spec hx]]
      simp only [Function.comp_apply, List.singleton_append, exec_app, evalOp, pack_coords,
        Bool.and_true, List.nil_append]
    | one =>
      simp only [genPhase4, refPhase4, List.append_assoc]
      rw [exec_sqzOps impl κ inp k st r ok _ hst, Option.bind_map]
      refine Option.bind_congr fun x _ => ?_
      have h0 : ((x.1.map Val.d).getD 0 default).toD = x.1.headD zeroD := by
        cases x.1 <;> rfl
      simp only [Function.comp_apply, List.singleton_append, exec_app, evalOp, rd_app0, h0,
        Bool.and_true]
    | pos _ =>
      simp only [genPhase4, refPhase4]
      rw [exec_sqzOps impl κ inp k st r ok _ hst, Option.bind_map]
      simp
  | uni f =>
    obtain ⟨hst, -, -, -, hpt⟩ := hwf.resolve_left (by simp)
    replace hst : st < r.size := hst
    replace hpt : pt < r.size := hpt
    by_cases hnd : p.d.node = true
    · simp only [genPhase4, refPhase4, hnd, ite_true]
      rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
      · rw [e0]; simp only [uniOps, uniHead, List.append_assoc, List.cons_append, exec_app, evalOp,
          List.nil_append, Option.bind_none]
      · rw [e0]; simp only [uniOps, uniHead, List.append_assoc, List.cons_append, exec_app, evalOp,
          List.nil_append, Option.bind_none]; split <;> simp
      · rw [exec_uni impl κ inp 0 _ st pt r ok ops _ hst hpt rfl]
        by_cases h : q₁ = absorbQ (rd r st).toD (FR.msgAt inp 0 (fieldOffOf S f + phaseOffOf S n f) uniBytes) ∧
          q₂ = squeezeQ a₁ <;> simp [h]
    · simp only [genPhase4, refPhase4, hnd, Bool.false_eq_true, ite_false, segPtOp_eq,
        List.cons_append]
      rw [e0, exec_app]
      simp only [evalOp, List.nil_append, Bool.and_true]
      generalize hP : ((segPtRegs S p outs).map fun x => (rd (r ++ ([] : List Val).toArray) x).toF).toArray = P
      have hP' : ((segPtRegs S p outs).map fun x => (rd r x).toF).toArray = P := by
        rw [← hP]; simp
      have hs1 : (r ++ [Val.af P].toArray).size = r.size + 1 := by simp
      rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
      · simp only [uniOps, uniHead, List.append_assoc, List.cons_append, exec_app, evalOp,
          List.nil_append]; rfl
      · simp only [uniOps, uniHead, List.append_assoc, List.cons_append, exec_app, evalOp,
          List.nil_append]; split <;> simp
      · rw [← hs1, exec_uni impl κ inp 0 _ st r.size (r ++ [Val.af P].toArray) ok ops _
          (by rw [hs1]; exact Nat.lt_succ_of_lt hst) (by rw [hs1]; exact Nat.lt_succ_self _)
          rfl, rd_app_left _ _ hst, rd_app0, hP']
        by_cases h : q₁ = absorbQ (rd r st).toD (FR.msgAt inp 0 (fieldOffOf S f + phaseOffOf S n f) uniBytes) ∧
          q₂ = squeezeQ a₁
        · simp [h]; rfl
        · simp [h]
  | rounds f k deg inK =>
    obtain ⟨hst, hu, -, -, -⟩ := hwf.resolve_left (by simp)
    replace hst : st < r.size := hst
    replace hu : u < r.size := hu
    simp only [genPhase4, refPhase4]
    rcases hi : initClaim name with _ | _ | _ <;>
      simp only [initOps, initVals, Init.width, List.nil_append, Nat.add_zero]
    · rw [exec_roundsT impl κ inp 0 _ deg inK _ k 0 st u r ok ops _ _ hst hu rfl rfl, Option.bind_map]
      simp
    · rw [e0]
      simp only [List.singleton_append, List.cons_append, exec_app, evalOp, List.nil_append]
      rw [exec_roundsT' impl κ inp 0 _ deg inK _ k 0 st r.size _ (r ++ [Val.f 0].toArray) _ ops _
        (.f 0) (by simp) (by simp; exact Nat.le_of_lt hst) (by simp) (by rw [rd_app_left _ _ hst])
        (by simpa using rd_app0 r [Val.f 0]), Option.bind_map]
      simp [Array.append_assoc]
    · rw [e0]
      cases inK <;>
      simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append, exec_app,
        evalOp, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, toF_f, toK_k] <;>
      rw [exec_roundsT' impl κ inp 0 _ deg _ _ k 0 st (r.size + 2) _ _ _ ops (rd r st).toD _ ?_ ?_ ?_ ?_
          rfl,
        Option.bind_map] <;>
      first
        | (simp [Array.append_assoc, rd_app, List.getD_cons_succ, List.getD_cons_zero, elemAt,
            elemKAt]; done)
        | exact Nat.lt_of_lt_of_le hst (by simp)
        | (simp; done)
        | rw [rd_app_left _ _ hst]
  | queries i =>
    simp only [refPhase4]
    rw [exec_append, exec_ok_and impl κ inp _ r ok tr]
    rcases hx : exec impl κ inp (genPhase4 S p n (name, .queries i) ⟨r.size, st, u, pa, fr, pt, outs⟩).1
      ⟨r, true⟩ tr with _ | ⟨s, tr'⟩
    · rfl
    · obtain ⟨L, hL, -, -⟩ := exec_ext impl κ inp _ r true tr s tr' hx
      simp [hL]

/-- The next free register is past the phase's ops, and one output list is pushed. -/
theorem genPhase4_next (n : ℕ) (ph : String × Sh) (c : GCtx) :
    (genPhase4 S p n ph c).2.next = c.next + opsOut (genPhase4 S p n ph c).1 ∧
      (genPhase4 S p n ph c).2.outs.size = c.outs.size + 1 := by
  obtain ⟨name, sh⟩ := ph
  cases sh with
  | squeezes k ch => cases ch <;> simp [genPhase4]
  | absorb f len => simp only [genPhase4]; split_ifs <;> simp
  | uni f => simp only [genPhase4]; split_ifs <;> simp
  | rounds f k deg inK => cases inK <;> simp [genPhase4]
  | _ => simp [genPhase4]

/-- **The context a phase hands on** (3.x's `genPhase_ctx`): the next free register is past the
phase's registers, the next context's registers point into them, one output list is pushed. -/
theorem genPhase4_ctx (n : ℕ) (ph : String × Sh) (c : GCtx) (r : Array Val) (tr : Trace)
    (x : List Val × Bool × Trace) (hb : c.next = r.size)
    (hwf : (ph.2 = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r)
    (hx : refPhase4 impl κ inp S p n ph c r tr = some x) :
    (genPhase4 S p n ph c).2.next = (r ++ x.1.toArray).size ∧
      CtxOk (genPhase4 S p n ph c).2 (r ++ x.1.toArray) ∧
      (genPhase4 S p n ph c).2.outs.size = c.outs.size + 1 := by
  have hex := exec_genPhase4 impl κ inp S p n ph c r true [] hb
    (hwf.imp (fun h => h.1) id) tr
  rw [hx, Option.bind_some, List.append_nil] at hex
  obtain ⟨L, hL, hl, -⟩ := exec_ext impl κ inp _ r true tr _ _ (hex.trans rfl)
  have hxL : x.1 = L := by simpa using congrArg Array.toList hL
  obtain ⟨hn, ho⟩ := genPhase4_next S p n ph c
  refine ⟨by rw [hn, hb, ← hl, ← hxL]; simp, ?_, ho⟩
  clear hex hL hxL hl hn ho
  obtain ⟨name, sh⟩ := ph
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hwf hx ⊢; subst hb
  have hm : ∀ m, r.size ≤ m → 1 ≤ m →
      st < m ∧ u < m ∧ (∀ x ∈ pa, x < m) ∧ (∀ x ∈ fr, x < m) ∧ pt < m := fun m h1 h2 => by
    rcases hwf with ⟨-, h⟩ | h
    · exact h.mono (by simpa using h2)
    · exact h.mono h1
  have hm4 : ∀ m, r.size ≤ m → 1 ≤ m →
      u < m ∧ (∀ x ∈ pa, x < m) ∧ (∀ x ∈ fr, x < m) ∧ pt < m := fun m h1 h2 => (hm m h1 h2).2
  have hpos : sh ≠ .seed → 0 < r.size := fun h => by
    rcases hwf with ⟨h', -⟩ | h
    · exact absurd h' h
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) h.1
  cases sh with
  | seed =>
    simp only [refPhase4] at hx
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · cases hx
    simp only at hx
    split_ifs at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hl := pureRun_len impl κ inp r _ _ _ _ hy
    rw [opsOut_seedTail4] at hl
    obtain ⟨-, h2, h3, h4, h5⟩ := hm (r.size + 2) (by omega) (by omega)
    simp only [genPhase4, CtxOk, Array.size_append, List.size_toArray, hl]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.length_cons, List.length_nil] at * <;>
      (try dsimp only [Reg] at *) <;> first | omega | (intro a ha; have := h3 a ha; omega) | (intro a ha; have := h4 a ha; omega)
  | absorb f len =>
    simp only [refPhase4] at hx
    obtain ⟨⟨a, tr'⟩, -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hl := pureRun_len impl κ inp r _ _ _ _ hy
    have hp := hpos (by simp)
    simp only [List.length_cons, List.length_nil] at hl
    obtain ⟨-, h2, h3, h4, h5⟩ := hm (r.size + 2) (by omega) (by omega)
    simp only [genPhase4]
    split_ifs <;> simp only [CtxOk, Array.size_append, List.size_toArray, hl] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try dsimp only [Reg] at *) <;>
      first | omega | (intro a ha; have := h3 a ha; omega) | (intro a ha; have := h4 a ha; omega)
  | squeezes k ch =>
    simp only [refPhase4] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hk := sqzT_spec hy
    have hc := coordVals_length y.1
    simp only [List.length_flatMap] at hc
    have hp := hpos (by simp)
    cases ch <;> simp [genPhase4, CtxOk, hc, hk]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | uni f =>
    simp only [refPhase4] at hx
    have hp := hpos (by simp)
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only at hx
    split_ifs at hx with h1 h2 <;> cases hx <;> simp [genPhase4, CtxOk, uniVals_length, h2]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | rounds f k deg inK =>
    simp only [refPhase4] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hk := roundsT_length inp hy
    have hp := hpos (by simp)
    have hw : 13 ≤ roundW deg := by unfold roundW; split <;> omega
    have hwk : 0 < k → roundW deg ≤ roundW deg * k := Nat.le_mul_of_pos_right _
    have hst : st < r.size := (hm r.size le_rfl hp).1
    simp only [genPhase4]
    rcases initClaim name with _ | _ | _ <;> cases inK <;>
      simp [initOps, initVals_length, hk, CtxOk, Init.width]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | (split_ifs with hk0 <;> first | omega | (have := hwk (by omega); omega))
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | queries i =>
    have hp := hpos (by simp)
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm (r.size + x.1.length) (by omega) (by omega)
    simp only [genPhase4, CtxOk, Array.size_append, List.size_toArray]
    exact ⟨h1, h2, h3, h4, h5⟩

/-- **Reference semantics of a run of phases** (3.x's `refPhases`). -/
def refPhases4 : List (String × Sh) → ℕ → GCtx → Array Val → Trace →
    Option (List Val × List Bool × Trace)
  | [], _, _, _, tr => some ([], [], tr)
  | ph :: ps, n, c, r, tr =>
    (refPhase4 impl κ inp S p n ph c r tr).bind fun x =>
      (refPhases4 ps (n + 1) (genPhase4 S p n ph c).2 (r ++ x.1.toArray) x.2.2).map fun y =>
        (x.1 ++ y.1, x.2.1 :: y.2.1, y.2.2)

/-- A run of phases may start: the first is the seed, or the context is well formed. -/
def StartOk4 (ps : List (String × Sh)) (c : GCtx) (r : Array Val) : Prop :=
  CtxOk c r ∨ ∃ ph ps', ps = ph :: ps' ∧ ph.2 = .seed ∧ CtxOk c #[default]

theorem exec_genPhases4 (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (r : Array Val) (ok : Bool)
    (ops : List Op) (hb : c.next = r.size) (hs : StartOk4 ps c r) (tr : Trace) :
    exec impl κ inp ((genPhases4 S p ps n c).1 ++ ops) ⟨r, ok⟩ tr =
      (refPhases4 impl κ inp S p ps n c r tr).bind fun y =>
        exec impl κ inp ops ⟨r ++ y.1.toArray, ok && y.2.1.all id⟩ y.2.2 := by
  induction ps generalizing n c r ok tr with
  | nil => simp [genPhases4, refPhases4]
  | cons ph ps ih =>
    have hwf : (ph.2 = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [genPhases4, List.append_assoc]
    rw [exec_genPhase4 impl κ inp S p n ph c r ok _ hb (hwf.imp (fun h => h.1) id), refPhases4,
      Option.bind_assoc]
    refine Option.bind_congr fun x hx => ?_
    obtain ⟨h1, h2, -⟩ := genPhase4_ctx impl κ inp S p n ph c r tr x hb hwf hx
    rw [ih (n + 1) _ _ _ h1 (.inl h2), Option.bind_map]
    refine Option.bind_congr fun y _ => ?_
    simp [Array.append_assoc, Bool.and_assoc, List.all_cons]

/-- The skeleton's next free register is the size of the register file it leaves. -/
theorem genPhases4_next : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace), refPhases4 impl κ inp S p ps n c r tr = some y →
    c.next = r.size → StartOk4 ps c r → (genPhases4 S p ps n c).2.next = (r ++ y.1.toArray).size
  | [], _, c, r, tr, y, h, hb, _ => by
    simp only [refPhases4, Option.some.injEq] at h; subst h; simp [genPhases4, hb]
  | ph :: ps, n, c, r, tr, y, h, hb, hs => by
    have hwf : (ph.2 = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [refPhases4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    obtain ⟨h1, h2, -⟩ := genPhase4_ctx impl κ inp S p n ph c r tr x hb hwf hx
    have := genPhases4_next ps (n + 1) _ _ _ y' hy' h1 (.inl h2)
    simp only [genPhases4]
    rw [this]
    simp [Array.size_append]

/-- The initial context. -/
theorem startOk4 : StartOk4 (phasesOf S) ⟨0, 0, 0, [], [], 0, #[]⟩ #[] :=
  .inr ⟨_, _, rfl, rfl, by simp [CtxOk]⟩

/-- **`exec_skeleton4`**: the whole skeleton of `gen4 S p` on a trace is `refPhases4`. -/
theorem exec_skeleton4 (ok : Bool) (ops : List Op) (tr : Trace) :
    exec impl κ inp ((skeleton4 S p).1 ++ ops) ⟨#[], ok⟩ tr =
      (refPhases4 impl κ inp S p (phasesOf S) 0 ⟨0, 0, 0, [], [], 0, #[]⟩ #[] tr).bind fun y =>
        exec impl κ inp ops ⟨#[] ++ y.1.toArray, ok && y.2.1.all id⟩ y.2.2 :=
  exec_genPhases4 impl κ inp S p (phasesOf S) 0 _ #[] ok ops rfl (startOk4 S) tr

/-- The skeleton's next free register is the size of its register file. -/
theorem skeleton4_next {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp S p (phasesOf S) 0 ⟨0, 0, 0, [], [], 0, #[]⟩ #[] tr = some y) :
    (skeleton4 S p).2.next = (#[] ++ y.1.toArray).size :=
  genPhases4_next impl κ inp S p _ 0 _ #[] tr y h rfl (startOk4 S)

end Ref

end FR.Snd.R4
