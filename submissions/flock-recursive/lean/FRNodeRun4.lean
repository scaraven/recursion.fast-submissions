-- New for `flock-recursive` (PACK-4.4 §4, B4's theorem; track B3). The trace-building twin of
-- S-E14's `compileFromX_soundR` (`FRNodeRows4Rep`).
import FRNodeRows4Rep

/-!
# The run's existence on a read trace (`compileFromX_run`)

S-N2's `SlotRun` asks for `exec impl ι inp ops St.init tr = some (s, [])` on the trace `tr` the
reader takes off H. `exec` stops only at an ask whose computed query differs from the trace entry's
(or when the trace runs out). So the run exists iff every ask's query, computed from the registers,
is the trace's. This module proves it along the compile's trail, never by evaluating a program:

* **`execA`**, the **answer-driven run**: `exec` without the query comparison (each ask binds the
  trace entry's answer). It exists as soon as the trace has an entry per ask (`execA_some`), and
  its final state is a function of the trace alone, so the run facts `SlotRun` needs (auxiliary,
  import, foreign) are stated on it.
* **`AT`** (an ask template: rows per compile state, previous op, op and ask index; `cov` the
  non-ask ops whose imports it binds) and **`ATOk = ATAsk ∧ ATImp`**: at an ask whose rows hold,
  with the invariant `InvK` at the op and the previous op's results last in the registers
  (`PrevOk`), the trace entry's query is the computed one and the answer slots represent its answer
  (`ATAsk`); at a covered op, its import slots represent its results at the fixed input (`ATImp`:
  the proof fields, challenge halves, bits and inputs of PACK-4.4 §1.3, which S-E14's `RTOk`, being
  quantified over every input, cannot bind). **`AskBound`** is `ATAsk` split per ask constructor
  (`seed`, `absorb`, `squeeze`, `node`, `col`, and the answer `ans`; `atAsk_of_askBound`). Its
  fields are the interface the row side (FS links, Merkle mux rows, pins and the H bridge) meets;
  `rd_of_cells`, `rd_of_piField`, `absorbQ_of_links`, `squeezeQ_of_links`, `nodeQ_of_mux`,
  `seedQ_of_pre`, `colQ_of_pre`, `ans_of_cells` reduce each field to a per-item fact on cells.
* **`askRowsX`**, **`impAX`**: the template's rows along the trail, and the import registers that
  are neither asks nor covered by `A` or by a replay template `RT`.
* **`compileFromX_run`** (the induction) and **`compileX_run`**: with the rows, the templates, the
  replay rows, the ask rows and the residual facts on `execA`'s final state, `exec` runs to that
  state and every register is represented.

The previous op is passed because an ask's byte operand (`hdr`, an absorb's message, a column) is an
untracked register (a `Val.b`): in every generator it is the `piField` just before the ask
(`prev_piField` reads it).
-/

namespace FR
namespace Circ
open RecursionFast

/-! ## The answer-driven run -/

/-- **The answer-driven run**: `exec`, except that an ask binds the trace entry's answer without
comparing its query. -/
def execA (impl : OpImpl) (κ : Kind) (inp : Input) : List Op → St → Trace → Option (St × Trace)
  | [], s, tr => some (s, tr)
  | op :: ops, s, tr =>
    match evalOp impl κ inp s.regs op with
    | .vals vs ok => execA impl κ inp ops ⟨s.regs ++ vs.toArray, s.ok && ok⟩ tr
    | .ask _ =>
      match tr with
      | [] => none
      | (_, a) :: tr' => execA impl κ inp ops ⟨s.regs.push (.d a), s.ok⟩ tr'

section Run
variable {impl : OpImpl} {κ : Kind} {inp : Input}

theorem ask_item {regs : Array Val} {op : Op} {q : ByteArray} (h : evalOp impl κ inp regs op = .ask q) :
    op.item?.isSome = true := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

theorem vals_item' {regs : Array Val} {op : Op} {vs : List Val} {ok : Bool}
    (h : evalOp impl κ inp regs op = .vals vs ok) : op.item?.isSome = false := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

/-- (+) **A run is the answer-driven run**: `execA` assumes nothing `exec` does not. -/
theorem execA_of_exec : ∀ (ops : List Op) (s : St) (tr : Trace) {r : St × Trace},
    exec impl κ inp ops s tr = some r → execA impl κ inp ops s tr = some r
  | [], s, tr, r, h => h
  | op :: ops, s, tr, r, h => by
    simp only [exec] at h
    simp only [execA]
    split at h
    · next vs ok hv => rw [hv]; exact execA_of_exec ops _ tr h
    · next q hq =>
      rw [hq]
      rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · cases h
      · simp only at h ⊢
        split_ifs at h
        exact execA_of_exec ops _ tr' h

/-- **The answer-driven run exists** when the trace has an entry per ask; it leaves the rest. -/
theorem execA_some : ∀ (ops : List Op) (s : St) (tr : Trace),
    (ops.filterMap Op.item?).length ≤ tr.length →
    ∃ s', execA impl κ inp ops s tr = some (s', tr.drop (ops.filterMap Op.item?).length)
  | [], s, tr, _ => ⟨s, rfl⟩
  | op :: ops, s, tr, hl => by
    simp only [execA]
    split
    · next vs ok hv =>
      have hi : op.item? = none := by simpa using vals_item' hv
      simp only [List.filterMap_cons, hi] at hl ⊢
      exact execA_some ops _ tr hl
    · next q hq =>
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 (ask_item hq)
      simp only [List.filterMap_cons, hit, List.length_cons] at hl ⊢
      rcases tr with _ | ⟨⟨q', a⟩, tr'⟩
      · simp at hl
      · simp only [List.length_cons, add_le_add_iff_right] at hl
        simpa using execA_some ops _ tr' hl

theorem execA_prefix : ∀ (ops : List Op) (s : St) (tr : Trace) {s' : St} {tr' : Trace},
    execA impl κ inp ops s tr = some (s', tr') → ∃ more : Array Val, s'.regs = s.regs ++ more
  | [], s, tr, s', tr', h => by simp [execA] at h; exact ⟨#[], by simp [← h.1]⟩
  | op :: ops, s, tr, s', tr', h => by
    simp only [execA] at h
    split at h
    · next vs _ _ =>
      obtain ⟨m, hm⟩ := execA_prefix ops _ _ h
      exact ⟨vs.toArray ++ m, by rw [hm, Array.append_assoc]⟩
    · rcases tr with _ | ⟨⟨q', a⟩, tr0⟩
      · cases h
      · obtain ⟨m, hm⟩ := execA_prefix ops _ _ h
        exact ⟨#[.d a] ++ m, by rw [hm, Array.push_eq_append, Array.append_assoc]⟩

end Run

/-! ## Ask templates and their obligation -/

/-- **The previous op's results are the last registers** (`none`: no previous op). -/
def PrevOk (impl : OpImpl) (κ : Kind) (inp : Input) : Option Op → Array Val → Prop
  | none, _ => True
  | some p, regs => ∃ r₀ : Array Val,
      (∃ vs ok, evalOp impl κ inp r₀ p = .vals vs ok ∧ regs = r₀ ++ vs.toArray) ∨
      (∃ q a, evalOp impl κ inp r₀ p = .ask q ∧ regs = r₀.push (.d a))

/-- **An ask template**: for a compile state, the previous op, an op and the asks before it (an
ask's entry in the trace), rows. At an ask they bind the query to the entry and the answer slots to
its answer; at a covered op (`cov`, not an ask) they bind its import slots to its results. -/
structure AT where
  cov : Op → Bool
  rows : Params → CS → Option Op → Op → ℕ → List Row

/-- The template with no rows, covering nothing. -/
def AT.none : AT := ⟨fun _ => false, fun _ _ _ _ _ => []⟩

/-- **The context of a templated op**: the selector, the invariant at the op, the previous op's
results last, the template's rows. -/
def AskCtx (impl : OpImpl) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (P : Params) (cs : CS)
    (pre : Option Op) (op : Op) (k : ℕ) (regs : Array Val) : Prop :=
  SelOk w P κ ∧ InvK w cs regs κ ∧ PrevOk impl κ inp pre regs ∧ ∀ r ∈ A.rows P cs pre op k, r.Holds w

/-- **The asks are sound for the trace `tr`**: at every ask in its context, entry `k` of `tr` has
the computed query, and the answer slots represent its answer. -/
def ATAsk (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (tr : Trace) : Prop :=
  ∀ P cs pre op k regs q e, AskCtx impl A κ inp w P cs pre op k regs →
    evalOp impl κ inp regs op = .ask q → tr[k]? = some e →
    e.1 = q ∧ List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d e.2]

/-- **The covered imports are sound at the input `inp`**: a covered op's import slots represent
its results in its context. -/
def ATImp (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) : Prop :=
  ∀ P cs pre op k regs vs ok, A.cov op = true → AskCtx impl A κ inp w P cs pre op k regs →
    evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
    List.Forall₂ (RepS w) (stepOut X P cs op).slots vs

/-- **An ask template is sound for `inp` and the trace `tr`.** -/
def ATOk (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (tr : Trace) : Prop :=
  ATAsk impl X A κ inp w tr ∧ ATImp impl X A κ inp w

/-- **`ATAsk` per ask constructor**: what the rows of each ask (with the H bridge) must give. The
query facts are `evalOp`'s queries at the registers; `ans` is the answer's representation. -/
structure AskBound (impl : OpImpl) (X : Ext) (A : AT) (κ : Kind) (inp : Input) (w : Asg) (tr : Trace) :
    Prop where
  /-- The seed: `"FRSEED0" ‖ vk ‖ c ‖ hdr`. -/
  seed : ∀ P cs pre h k regs e, AskCtx impl A κ inp w P cs pre (.askSeed h) k regs → tr[k]? = some e →
    e.1 = seedQ inp.vk inp.c (rd regs h).toB
  /-- An absorb: its state register's digest and its message. -/
  absorb : ∀ P cs pre st m len k regs e, AskCtx impl A κ inp w P cs pre (.askAbsorb st m len) k regs →
    tr[k]? = some e → e.1 = absorbQ (rd regs st).toD (rd regs m).toB
  /-- A squeeze: its state register's digest. -/
  squeeze : ∀ P cs pre st k regs e, AskCtx impl A κ inp w P cs pre (.askSqueeze st) k regs →
    tr[k]? = some e → e.1 = squeezeQ (rd regs st).toD
  /-- A Merkle node: its halves (`0^64` where the depth is inactive). -/
  node : ∀ P cs pre i h l r act k regs e, AskCtx impl A κ inp w P cs pre (.askNode i h l r act) k regs →
    tr[k]? = some e →
    e.1 = if act κ then nodeQF i (rd regs l).toD (rd regs r).toD else nodeQF i zeroD zeroD
  /-- A column: its bytes. -/
  col : ∀ P cs pre i c k regs e, AskCtx impl A κ inp w P cs pre (.askCol i c) k regs →
    tr[k]? = some e → e.1 = colQ i (rd regs c).toB
  /-- Every ask's answer slots represent the entry's answer. -/
  ans : ∀ P cs pre op k regs e, op.item?.isSome = true → AskCtx impl A κ inp w P cs pre op k regs →
    tr[k]? = some e → List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d e.2]

/-- **The per-constructor obligations give `ATAsk`.** -/
theorem atAsk_of_askBound {impl : OpImpl} {X : Ext} {A : AT} {κ : Kind} {inp : Input} {w : Asg}
    {tr : Trace} (h : AskBound impl X A κ inp w tr) : ATAsk impl X A κ inp w tr := by
  intro P cs pre op k regs q e hc hq he
  refine ⟨?_, h.ans P cs pre op k regs e (ask_item hq) hc he⟩
  cases op <;> simp only [evalOp, reduceCtorEq, Res.ask.injEq] at hq <;> subst hq
  · exact h.seed _ _ _ _ _ _ _ hc he
  · exact h.absorb _ _ _ _ _ _ _ _ _ hc he
  · exact h.squeeze _ _ _ _ _ _ _ hc he
  · exact h.node _ _ _ _ _ _ _ _ _ _ _ hc he
  · exact h.col _ _ _ _ _ _ _ _ hc he

/-- (+) The converse: `ATAsk` gives every field, so `AskBound` asks nothing more. -/
theorem askBound_of_atAsk {impl : OpImpl} {X : Ext} {A : AT} {κ : Kind} {inp : Input} {w : Asg}
    {tr : Trace} (h : ATAsk impl X A κ inp w tr) : AskBound impl X A κ inp w tr where
  seed _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  absorb _ _ _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  squeeze _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  node _ _ _ _ _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  col _ _ _ _ _ _ _ _ hc he := (h _ _ _ _ _ _ _ _ hc rfl he).1
  ans P cs pre op k regs e hi hc he := by
    obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 hi
    cases op <;> simp only [Op.item?, reduceCtorEq] at hit <;>
      exact (h _ _ _ _ _ _ _ _ hc rfl he).2

/-! ## Facts a template uses -/

/-- **A byte operand read off the previous `piField`**: the last register holds its bytes. -/
theorem prev_piField {impl : OpImpl} {κ : Kind} {inp : Input} {f o len : ℕ} {regs : Array Val}
    (h : PrevOk impl κ inp (some (.piField f o len)) regs) :
    rd regs (regs.size - 1) = .b (inp.π.extract (absOff f o) (absOff f o + len)) := by
  obtain ⟨r₀, ⟨vs, ok, hv, rfl⟩ | ⟨q, a, hq, -⟩⟩ := h
  · simp only [evalOp, Res.vals.injEq] at hv
    obtain ⟨rfl, -⟩ := hv
    simp [rd]
  · simp [evalOp] at hq

/-- **A register's slot at `κ` represents it** (the invariant, read at one register). -/
theorem rep_of_invK {w : Asg} {cs : CS} {regs : Array Val} {κ : Kind} (h : InvK w cs regs κ) (i : ℕ) :
    RepS w (cs.slotK i κ) (rd regs i) :=
  h.2.2 i

/-- **A digest slot's two cells determine the digest.** -/
theorem digest_of_rep {w : Asg} {l₀ l₁ : Lin} {v : Val} {x : Digest}
    (h : RepS w (some (.d, [l₀, l₁])) v) (h₀ : l₀.ev w = dlo x) (h₁ : l₁.ev w = dhi x) : v = .d x := by
  obtain ⟨ht, he⟩ := h
  cases v <;> simp only [tyOf, Option.some.injEq, reduceCtorEq] at ht
  rename_i y
  simp only [List.map_cons, List.map_nil, encV, List.cons.injEq, and_true] at he
  rw [digest_ext (he.1.symm.trans h₀) (he.2.symm.trans h₁)]

/-! ## The per-item facts that meet `AskBound`

Each field of `AskBound` reduces to a fact about the trace entry and the cells (the row side's
FS links, Merkle mux rows and pins, with the H bridge): a digest operand is read off its slot's two
cells (`rd_of_cells`), a byte operand off the `piField` before the ask (`prev_piField`), and the
answer slot's cells carry the entry's answer (`ans_of_cells`). -/

section Items
variable {impl : OpImpl} {A : AT} {κ : Kind} {inp : Input} {w : Asg} {P : Params} {cs : CS}
  {pre : Option Op} {op : Op} {k : ℕ} {regs : Array Val}

/-- **A digest operand is the digest its cells carry.** -/
theorem rd_of_cells (hc : AskCtx impl A κ inp w P cs pre op k regs) {i : ℕ} {l₀ l₁ : Lin} {x : Digest}
    (hs : cs.slotK i κ = some (.d, [l₀, l₁])) (h₀ : l₀.ev w = dlo x) (h₁ : l₁.ev w = dhi x) :
    rd regs i = .d x :=
  digest_of_rep (hs ▸ rep_of_invK hc.2.1 i) h₀ h₁

/-- **The byte operand just appended by the previous `piField`.** -/
theorem rd_of_piField {f o len : ℕ} (hc : AskCtx impl A κ inp w P cs (some (.piField f o len)) op k regs) {m : ℕ}
    (hm : m + 1 = cs.slots.size) : rd regs m = .b (inp.π.extract (absOff f o) (absOff f o + len)) := by
  have := prev_piField hc.2.2.1
  rwa [show regs.size - 1 = m by rw [← hc.2.1.1.1]; omega] at this

/-- **The FS link at an absorb**: its state cells carry `x` and its message is the previous
`piField`'s, so its query is `absorbQ x (π's bytes)`. -/
theorem absorbQ_of_links {f o len' st m len : ℕ}
    (hc : AskCtx impl A κ inp w P cs (some (.piField f o len')) (.askAbsorb st m len) k regs)
    (hm : m + 1 = cs.slots.size) {l₀ l₁ : Lin} {x : Digest} (hs : cs.slotK st κ = some (.d, [l₀, l₁]))
    (h₀ : l₀.ev w = dlo x) (h₁ : l₁.ev w = dhi x) :
    absorbQ (rd regs st).toD (rd regs m).toB = absorbQ x (inp.π.extract (absOff f o) (absOff f o + len')) := by
  rw [rd_of_cells hc hs h₀ h₁, rd_of_piField hc hm]; rfl

/-- **The FS link at a squeeze.** -/
theorem squeezeQ_of_links {st : ℕ} (hc : AskCtx impl A κ inp w P cs pre (.askSqueeze st) k regs)
    {l₀ l₁ : Lin} {x : Digest} (hs : cs.slotK st κ = some (.d, [l₀, l₁])) (h₀ : l₀.ev w = dlo x)
    (h₁ : l₁.ev w = dhi x) : squeezeQ (rd regs st).toD = squeezeQ x := by
  rw [rd_of_cells hc hs h₀ h₁]; rfl

/-- **The Merkle mux at a node**: its halves' cells carry `x`, `y` (the half at the index bit is
the previous answer, the other the sibling), so its query is `nodeQF i x y`. -/
theorem nodeQ_of_mux {i h l r : ℕ} {act : KC Bool}
    (hc : AskCtx impl A κ inp w P cs pre (.askNode i h l r act) k regs) {l₀ l₁ r₀ r₁ : Lin} {x y : Digest}
    (hl : cs.slotK l κ = some (.d, [l₀, l₁])) (hl₀ : l₀.ev w = dlo x) (hl₁ : l₁.ev w = dhi x)
    (hr : cs.slotK r κ = some (.d, [r₀, r₁])) (hr₀ : r₀.ev w = dlo y) (hr₁ : r₁.ev w = dhi y) :
    nodeQF i (rd regs l).toD (rd regs r).toD = nodeQF i x y := by
  rw [rd_of_cells hc hl hl₀ hl₁, rd_of_cells hc hr hr₀ hr₁]; rfl

/-- **The seed's header is the previous `piField`'s bytes.** -/
theorem seedQ_of_pre {f o len hd : ℕ} (hc : AskCtx impl A κ inp w P cs (some (.piField f o len)) (.askSeed hd) k regs)
    (hm : hd + 1 = cs.slots.size) :
    seedQ inp.vk inp.c (rd regs hd).toB = seedQ inp.vk inp.c (inp.π.extract (absOff f o) (absOff f o + len)) := by
  rw [rd_of_piField hc hm]; rfl

/-- **A column is the previous `piField`'s bytes.** -/
theorem colQ_of_pre {f o len i c : ℕ} (hc : AskCtx impl A κ inp w P cs (some (.piField f o len)) (.askCol i c) k regs)
    (hm : c + 1 = cs.slots.size) :
    colQ i (rd regs c).toB = colQ i (inp.π.extract (absOff f o) (absOff f o + len)) := by
  rw [rd_of_piField hc hm]; rfl

/-- **The answer's cells carry the entry's answer.** -/
theorem ans_of_cells {X : Ext} {l₀ l₁ : Lin} {a : Digest}
    (hs : (stepOut X P cs op).slots = [some (.d, [l₀, l₁])]) (h₀ : l₀.ev w = dlo a) (h₁ : l₁.ev w = dhi a) :
    List.Forall₂ (RepS w) (stepOut X P cs op).slots [.d a] := by
  rw [hs]; exact .cons ⟨rfl, by simp [encV, h₀, h₁]⟩ .nil

end Items

/-! ## Along the trail -/

/-- **The ask rows along the compile's trail** (the alignment and the step exactly as
`compileFromX`; `pre` the previous op, `k` the asks so far). -/
def askRowsX (X : Ext) (P : Params) (A : AT) : CS → Option Op → ℕ → List Op → List Row
  | _, _, _, [] => []
  | cs, pre, k, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if op.item?.isSome || A.cov op then A.rows P c pre op k else []) ++
      askRowsX X P A (c.add op (stepOut X P c op)) (some op) (if op.item?.isSome then k + 1 else k) ops

/-- **The import registers neither an ask nor covered by `rt` or `A`**, along the trail. -/
def impAX (X : Ext) (P : Params) (rt : RT) (A : AT) : CS → List Op → List ℕ
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if (stepOut X P c op).imp && !rt.cov op && !A.cov op && !op.item?.isSome then
        List.range' c.slots.size (stepOut X P c op).slots.length else []) ++
      impAX X P rt A (c.add op (stepOut X P c op)) ops

theorem askRowsX_cons (X : Ext) (P : Params) (A : AT) (cs : CS) (pre : Option Op) (k : ℕ) (op : Op)
    (ops : List Op) :
    askRowsX X P A cs pre k (op :: ops) =
      (if op.item?.isSome || A.cov op then A.rows P (cs.align (alignOf op ops)) pre op k else []) ++
        askRowsX X P A ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op))
          (some op) (if op.item?.isSome then k + 1 else k) ops :=
  rfl

theorem impAX_cons (X : Ext) (P : Params) (rt : RT) (A : AT) (cs : CS) (op : Op) (ops : List Op) :
    impAX X P rt A cs (op :: ops) =
      (if (stepOut X P (cs.align (alignOf op ops)) op).imp && !rt.cov op && !A.cov op && !op.item?.isSome then
          List.range' (cs.align (alignOf op ops)).slots.size
            (stepOut X P (cs.align (alignOf op ops)) op).slots.length else []) ++
        impAX X P rt A ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op)) ops :=
  rfl

/-- **The residual imports are uncovered imports** (`impAX ⊆ impRX`), so they ask nothing new. -/
theorem impAX_sub (X : Ext) (P : Params) (rt : RT) (A : AT) :
    ∀ (ops : List Op) (cs : CS), ∀ i ∈ impAX X P rt A cs ops, i ∈ impRX X P rt cs ops
  | [], _, i, h => by simp [impAX] at h
  | op :: ops, cs, i, h => by
    rw [impAX_cons, List.mem_append] at h
    rw [impRX_cons, List.mem_append]
    rcases h with h | h
    · refine .inl ?_
      split_ifs at h with hc
      · simp only [Bool.and_eq_true] at hc
        rw [if_pos (by simp only [Bool.and_eq_true]; exact hc.1.1)]; exact h
      · simp at h
    · exact .inr (impAX_sub X P rt A ops _ i h)

theorem drop_cons_get {tr : Trace} {k : ℕ} {e : ByteArray × Digest} {t : Trace}
    (h : tr.drop k = e :: t) : tr[k]? = some e ∧ t = tr.drop (k + 1) := by
  constructor
  · rw [← List.head?_drop, h]; rfl
  · rw [← List.drop_drop, h]; rfl

/-! ## The run -/

/-- **The run along the compile's trail** (`compileFromX_soundR` with the trace threaded): the
answer-driven run from entry `k` is `exec`'s, and the invariant holds at its end. -/
theorem compileFromX_run {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} {rt : RT} {A : AT} {tr : Trace} (hX : ExtOkK impl tc X κ)
    (hP : SelOk w P κ) (hR : RTOk impl X rt κ) (hA : ATOk impl X A κ inp w tr) :
    ∀ (ops : List Op) (cs : CS) (pre : Option Op) (k : ℕ) (s s' : St) (tr' : Trace),
    InvK w cs s.regs κ → PrevOk impl κ inp pre s.regs →
    execA impl κ inp ops s (tr.drop k) = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ impAX X P rt A cs ops, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ r ∈ repRowsX X P rt cs ops, r.Holds w) →
    (∀ r ∈ askRowsX X P A cs pre k ops, r.Holds w) →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    exec impl κ inp ops s (tr.drop k) = some (s', tr') ∧ s'.ok = s.ok ∧
      InvK w (compileFromX X P cs ops) s'.regs κ
  | [], cs, pre, k, s, s', tr', hI, _, he, _, _, _, _, _, _, _ => by
    simp [execA] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, rfl, hI⟩
  | op :: ops, cs, pre, k, s, s', tr', hI, hpv, he, hr, ht, hx, hi, hrr, hra, hf => by
    rw [impAX_cons] at hi
    rw [repRowsX_cons] at hrr
    rw [askRowsX_cons] at hra
    rw [compileFromX_cons] at hr ht hx hi hf ⊢
    have hI' : InvK w (cs.align (alignOf op ops)) s.regs κ :=
      ⟨⟨by simp [hI.1.1], fun i => by rw [CS.align_slot]; exact hI.1.2 i⟩,
        fun p hp => by rw [CS.align_kslots] at hp; rw [CS.align_slots]; exact hI.2.1 p hp,
        fun i => by rw [CS.align_slotK]; exact hI.2.2 i⟩
    generalize cs.align (alignOf op ops) = cs at hI' hr ht hx hi hrr hra hf ⊢
    clear hI
    rename' hI' => hI
    set o := stepOut X P cs op with ho
    obtain ⟨ss, rs, hsl, hrw, -, hfor, htin, haux⟩ := compileFromX_mono X P ops (cs.add op o)
    have hro : ∀ r ∈ o.rows, r.Holds w := fun r h =>
      hr r (by
        rw [hrw]; simp only [CS.add, List.reverseAux_eq]
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 h)))
    have hto : ∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w :=
      fun t htm r hr' => ht _ (htin (by simp only [CS.add, Option.mem_def.1 htm]; simp)) r hr'
    have hpre : ∀ (m : Array Val), (s.regs ++ m).extract 0 cs.slots.size = s.regs := fun m => by
      rw [hI.1.1, Array.extract_append_left, Array.extract_size]
    have flag : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.foreign = true →
        flagOf impl κ inp s.regs op = true := by
      intro vs s1 hs1 ⟨m, hm⟩ hfo
      have := hf (op, cs.slots.size) (hfor (by simp [CS.add, hfo]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hauxo : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) →
        ∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd s.regs a.2.1) := by
      intro vs s1 hs1 ⟨m, hm⟩ a ha
      have := hx (a, cs.slots.size) (haux (by simp [CS.add, ha]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hstep : (∀ q, evalOp impl κ inp s.regs op ≠ .ask q) ∨ X P cs op = none := by
      rcases hXo : X P cs op with _ | o'
      · exact .inr rfl
      · exact .inl ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).1
    have hpos : o.kin.isSome → 0 < o.slots.length := by
      rcases hXo : X P cs op with _ | o'
      · simp [ho, stepOut, hXo, opOut_kin]
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).2.1
    have hlen : o.slots.length = op.nOut := by
      rcases hXo : X P cs op with _ | o'
      · simp only [ho, stepOut, hXo, Option.getD_none]; exact opOut_len P cs op
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).1
    have hrr' : ∀ r ∈ repRowsX X P rt (cs.add op o) ops, r.Holds w :=
      fun r h => hrr r (List.mem_append_right _ h)
    have hi' : ∀ i ∈ impAX X P rt A (cs.add op o) ops,
        RepS w ((compileFromX X P (cs.add op o) ops).slot i) (rd s'.regs i) :=
      fun i h => hi i (List.mem_append_right _ h)
    simp only [execA] at he
    split at he
    · rename_i vs ok hev
      have hit := vals_item' hev
      rw [hit, Bool.false_or] at hra
      have hra' : ∀ r ∈ askRowsX X P A (cs.add op o) (some op) k ops, r.Holds w :=
        fun r h => hra r (List.mem_append_right _ h)
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := execA_prefix ops _ _ he
      -- an uncovered non-ask import's registers: from `hi`
      have fin : o.imp = true → rt.cov op = false → A.cov op = false →
          ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        intro hio hc hac j hj
        obtain ⟨m, hm'⟩ := hm
        have := hi (cs.slots.size + j) (List.mem_append_left _ (by
          simp only [hio, hc, hac, hit, Bool.not_false, Bool.and_self, if_true, List.mem_range'_1]; omega))
        have hs := slot_append_right cs.slots o.slots ss hj
        have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
        rw [CS.slot, hsl] at this; simp only [CS.add] at this
        rw [hs, hm', hI.1.1, hv] at this; exact this
      have hsnd : (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true) ∧
          (∀ f v, o.kin = some f → vs.head? = some v → RepS w (f κ) v) := by
        rcases hXo : X P cs op with _ | o'
        · simp only [ho, stepOut, hXo, Option.getD_none] at hro ⊢
          exact ⟨(opOut_sound hP hI.1.2 op hro hev).1, (opOut_sound hP hI.1.2 op hro hev).2,
            fun f v hf => by rw [opOut_kin] at hf; cases hf⟩
        · have eo : o = o' := by simp [ho, stepOut, hXo]
          rw [eo] at hro hto ⊢
          exact ((hX P cs op o' hXo).2.2 inp w s.regs hP hI.1.2 hI.2.2).2 hro hto
            (eo ▸ hauxo vs _ rfl hm) vs ok hev
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        cases hio : o.imp
        · exact fun j hj => (List.forall₂_iff_get.1 (hsnd.1 hio)).2 j hj _
        · cases hc : rt.cov op
          · cases hac : A.cov op
            · exact fin hio hc hac
            · have hctx : AskCtx impl A κ inp w P cs pre op k s.regs :=
                ⟨hP, hI, hpv, fun r h => hra r (List.mem_append_left _ (by rw [if_pos hac]; exact h))⟩
              exact fun j hj => (List.forall₂_iff_get.1
                (hA.2 P cs pre op k s.regs vs ok hac hctx hev hio)).2 j hj _
          · have hrows : ∀ r ∈ rt.rows P cs op o.slots, r.Holds w :=
              fun r h => hrr r (List.mem_append_left _ (by rw [if_pos hc]; exact h))
            exact fun j hj => (List.forall₂_iff_get.1
              ((hR P cs op hc).2 inp w s.regs vs ok hP hI hrows hev hio)).2 j hj _
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2.1 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_run hX hP hR hA ops _ (some op) k _ s' tr'
        (invK_add hI o op hl hnew hsnd.2.2 hpos) ⟨s.regs, .inl ⟨vs, ok, hev, rfl⟩⟩ he hr ht hx hi' hrr'
        hra' hf
      refine ⟨?_, by rw [ih.2.1, hok, Bool.and_true], ih.2.2⟩
      simp only [exec, hev]; exact ih.1
    · rename_i q hev
      have hit := ask_item hev
      rw [hit, Bool.true_or] at hra
      simp only [if_true] at hra
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      rcases hd : tr.drop k with _ | ⟨⟨q', a⟩, tr0⟩
      · rw [hd] at he; cases he
      rw [hd] at he
      obtain ⟨hk, rfl⟩ := drop_cons_get hd
      have hc : AskCtx impl A κ inp w P cs pre op k s.regs :=
        ⟨hP, hI, hpv, fun r h => hra r (List.mem_append_left _ h)⟩
      obtain ⟨hq, hans⟩ := hA.1 P cs pre op k s.regs q (q', a) hc hev hk
      have hl : o.slots.length = [Val.d a].length := by rw [hlen, ask_nOut hev]; rfl
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] ([Val.d a][j]'(hl ▸ hj)) :=
        fun j hj => (List.forall₂_iff_get.1 hans).2 j hj _
      have ih := compileFromX_run hX hP hR hA ops _ (some op) (k + 1) ⟨s.regs.push (.d a), s.ok⟩ s' tr'
        (invK_add hI o op hl hnew (fun f v hf => by rw [ho', opOut_kin] at hf; cases hf) hpos)
        ⟨s.regs, .inr ⟨q, a, hev, rfl⟩⟩ he hr ht hx hi' hrr' (fun r h => hra r (List.mem_append_right _ h)) hf
      refine ⟨?_, ih.2.1, ih.2.2⟩
      simp only [exec, hev]
      simp only at hq
      rw [if_pos hq]; exact ih.1

/-- **The run of a compiled program exists** (`compileX_soundR`'s twin): the answer-driven run on
`tr`, with the rows, templates, replay and ask rows and the residual facts at its final state, is
`exec`'s run; its flag is set and every register is represented. -/
theorem compileX_run {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} {tc : Tpl.TCtx} {X : Ext} {rt : RT} {A : AT}
    (hX : ExtOkK impl tc X κ) (hR : RTOk impl X rt κ) (hA : ATOk impl X A κ inp w tr) (base : ℕ)
    (hP : SelOk w P κ) (he : execA impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ impAX X P rt A (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w)
    (hra : ∀ r ∈ askRowsX X P A (CS.init base) none 0 ops, r.Holds w)
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    exec impl κ inp ops St.init tr = some (s, tr') ∧ s.ok = true ∧
      ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_run hX hP hR hA ops (CS.init base) none 0 St.init s tr'
    ⟨⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩, fun p hp => by simp [CS.init] at hp,
      fun i => by simp [CS.slotK, CS.slot, CS.init, RepS]⟩ trivial (by simpa using he) hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hrr hra hf
  exact ⟨by simpa using h.1, h.2.1, h.2.2.1.2⟩

end Circ
end FR
