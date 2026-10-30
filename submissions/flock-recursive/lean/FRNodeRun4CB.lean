-- New for `flock-recursive` (track SIB): the closure generator's soundness. `ATAsk`/`ATImp` of `AT.close` and
-- `AT.addE`; `SlotRunB` from the closed residual `SlotRunC` (the replay ops' imports and the `felems` cells).
import FRNodeRun4BF
import FRNodeRows4

/-!
# The closed residual

`FRNodeRows4AskC.TG.close` covers every op that can be an import or a foreign flag (`closeCov`: less the
asks, the `bitOf`s and the replay ops) and fails at such an op the rest does not handle. So:

* **`atImp_close`**: covering those ops costs no `ATImp` obligation (a failing row at an import `A` does
  not cover); **`atAsk_close`**: the asks are `A`'s;
* **`impB_sub`**: the residual imports (`impBX` over the closed template) are the replay ops' (`impQX`), given
  that every `bitOf` is followed by its `selectHalf` (`bitNxAll`, checked at the first ask);
* **`fors_close`**: no foreign flag is left beside the zero pins and the statement's flags;
* **`SlotRunC`**: `SlotRunB` less those: the `felems` auxiliary cells and the imports of the replay ops
  neither the replay template `rt` nor the ask template covers (**`slotRunB_of_close`**). A class handled
  later (a template covering a replay op, `colTG`) shrinks it by definition.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## The ask-template forms -/

/-- **`TG.close` as an ask template.** -/
def _root_.FR.Circ.AT.close (A : AT) (X : Ext) (pv : List (ℕ × ℕ × ℕ × ℕ)) (T : BTab) (nx : Bool) : AT :=
  ⟨fun op => closeCov op || A.cov op, fun P cs pre op k =>
    if closeCov op then
      if opImp op then (if A.cov op then A.rows P cs pre op k else impRows X P cs op)
      else (if A.cov op then A.rows P cs pre op k else []) ++ forRows X pv T P cs op
    else A.rows P cs pre op k ++
      (if k = 0 && op.item?.isSome && !nx then [failRT P] else [])⟩

/-- **`TG.addE` as an ask template.** -/
def _root_.FR.Circ.AT.addE (A B : AT) : AT :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k =>
    if B.cov op then B.rows P cs pre op k ++ (if op.item?.isSome then A.rows P cs pre op k else [])
    else A.rows P cs pre op k ++ (if op.item?.isSome then B.rows P cs pre op k else [])⟩

/-- **`TG.repF` as an ask template** (SEG-R2). -/
def _root_.FR.Circ.AT.repF (A : AT) (rc : Op → Bool) : AT :=
  ⟨fun op => A.cov op || (isRep op && !rc op), fun P cs pre op k =>
    if !A.cov op && isRep op && !rc op then [failRT P] else A.rows P cs pre op k⟩

theorem toAT_repF (A : TG) (rc : Op → Bool) : (A.repF rc).toAT = A.toAT.repF rc := rfl

theorem toAT_close (A : TG) (X : Ext) (pv : List (ℕ × ℕ × ℕ × ℕ)) (T : BTab) (nx : Bool) :
    (A.close X pv T nx).toAT = A.toAT.close X pv T nx := rfl

theorem toAT_addE (A B : TG) : (A.addE B).toAT = A.toAT.addE B.toAT := rfl

theorem closeCov_item {op : Op} (h : op.item?.isSome = true) : closeCov op = false := by
  simp [closeCov, h]

section Close
variable {impl : OpImpl} {X : Ext} {A B : AT} {κ : Kind} {inp : Input} {w : Asg} {tr : Trace}
  {P : Params} {cs : CS} {pre : Option Op} {op : Op} {k : ℕ} {regs : Array Val}
  {Xc : Ext} {pv : List (ℕ × ℕ × ℕ × ℕ)} {T : BTab} {nx : Bool}

/-- At an op the closure leaves to `A` (not one of its own, or one `A` covers), `A`'s context. -/
theorem askCtx_close (h : AskCtx impl (A.close Xc pv T nx) κ inp w P cs pre op k regs)
    (hc : closeCov op = false ∨ A.cov op = true) : AskCtx impl A κ inp w P cs pre op k regs := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r ?_⟩
  simp only [AT.close]
  split
  · rcases hc with hc | hc
    · simp_all
    · simp only [hc, ite_true]
      split <;> simp [hr]
  · exact List.mem_append_left _ hr

theorem atAsk_close (h : ATAsk impl X A κ inp w tr) : ATAsk impl X (A.close Xc pv T nx) κ inp w tr :=
  fun P cs pre op k regs q e hc hev =>
    h P cs pre op k regs q e (askCtx_close hc (.inl (closeCov_item (ask_item hev)))) hev

/-- **Covering the possible imports costs nothing**: at an import `A` does not cover, the closure's rows
fail, provided whether a template takes an op is the same for `X` (the compile's) and `Xc`. -/
theorem atImp_close (hX : ExtFl X)
    (hXc : ∀ P cs op, (Xc P cs op).isNone = (X P cs op).isNone) (h : ATImp impl X A κ inp w) :
    ATImp impl X (A.close Xc pv T nx) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  by_cases hA : A.cov op = true
  · exact h P cs pre op k regs vs ok hA (askCtx_close hc (.inr hA)) hev himp
  · have hcc : closeCov op = true := by simpa [AT.close, hA] using hcov
    obtain ⟨hi, hn⟩ := stepOut_imp_of hX himp
    have hr := hc.2.2.2
    simp only [AT.close, hcc, if_true, hi, Bool.not_eq_true] at hr
    simp only [Bool.not_eq_true] at hA
    rw [if_neg (by simp [hA]), impRows, if_pos (by simp [hXc, hn])] at hr
    exact absurd (hr _ List.mem_cons_self) (failRT_not hc.1.1)

theorem atOk_close (hX : ExtFl X)
    (hXc : ∀ P cs op, (Xc P cs op).isNone = (X P cs op).isNone) (h : ATOk impl X A κ inp w tr) :
    ATOk impl X (A.close Xc pv T nx) κ inp w tr :=
  ⟨atAsk_close h.1, atImp_close hX hXc h.2⟩

theorem askCtx_addE_left (h : AskCtx impl (A.addE B) κ inp w P cs pre op k regs)
    (hc : B.cov op = false ∨ op.item?.isSome = true) : AskCtx impl A κ inp w P cs pre op k regs := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r ?_⟩
  simp only [AT.addE]
  split
  · rename_i hb
    rcases hc with hc | hc
    · rw [hc] at hb; cases hb
    · rw [if_pos hc]; exact List.mem_append_right _ hr
  · exact List.mem_append_left _ hr

theorem askCtx_addE_right (h : AskCtx impl (A.addE B) κ inp w P cs pre op k regs)
    (hc : B.cov op = true) : AskCtx impl B κ inp w P cs pre op k regs := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r ?_⟩
  simp only [AT.addE, hc, if_true]
  exact List.mem_append_left _ hr

theorem atAsk_addE (h : ATAsk impl X A κ inp w tr) : ATAsk impl X (A.addE B) κ inp w tr :=
  fun P cs pre op k regs q e hc hev =>
    h P cs pre op k regs q e (askCtx_addE_left hc (.inr (ask_item hev))) hev

theorem atImp_addE (hA : ATImp impl X A κ inp w) (hB : ATImp impl X B κ inp w) :
    ATImp impl X (A.addE B) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  by_cases hb : B.cov op = true
  · exact hB P cs pre op k regs vs ok hb (askCtx_addE_right hc hb) hev himp
  · have ha : A.cov op = true := by simpa [AT.addE, hb] using hcov
    exact hA P cs pre op k regs vs ok ha (askCtx_addE_left hc (.inl (by simpa using hb))) hev himp

theorem atOk_addE (hA : ATOk impl X A κ inp w tr) (hB : ATImp impl X B κ inp w) :
    ATOk impl X (A.addE B) κ inp w tr :=
  ⟨atAsk_addE hA.1, atImp_addE hA.2 hB⟩

end Close

/-! ## Failing at the uncovered replay ops (SEG-R2) -/

section RepF
variable {impl : OpImpl} {X : Ext} {A : AT} {rc : Op → Bool} {κ : Kind} {inp : Input} {w : Asg} {tr : Trace}
  {P : Params} {cs : CS} {pre : Option Op} {op : Op} {k : ℕ}

theorem repF_rows (h : (!A.cov op && isRep op && !rc op) = false) :
    (A.repF rc).rows P cs pre op k = A.rows P cs pre op k := by
  simp only [AT.repF, h, Bool.false_eq_true, ite_false]

theorem isRep_item {op : Op} (h : isRep op = true) : op.item?.isSome = false := by
  cases op <;> first | rfl | (simp [isRep] at h)

theorem askCtx_repF {regs : Array Val} (h : AskCtx impl (A.repF rc) κ inp w P cs pre op k regs)
    (hc : (!A.cov op && isRep op && !rc op) = false) : AskCtx impl A κ inp w P cs pre op k regs :=
  ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r (by rw [repF_rows hc]; exact hr)⟩

theorem atAsk_repF (h : ATAsk impl X A κ inp w tr) : ATAsk impl X (A.repF rc) κ inp w tr :=
  fun P cs pre op k regs q e hc hev => h P cs pre op k regs q e (askCtx_repF hc (by
    cases hr : isRep op
    · simp
    · exact absurd (ask_item hev) (by rw [isRep_item hr]; decide))) hev

/-- **Failing at the uncovered replay ops costs no `ATImp`**: there the rows do not hold. -/
theorem atImp_repF (h : ATImp impl X A κ inp w) : ATImp impl X (A.repF rc) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  by_cases hf : (!A.cov op && isRep op && !rc op) = true
  · have hr := hc.2.2.2
    simp only [AT.repF, hf, ite_true] at hr
    exact absurd (hr _ List.mem_cons_self) (failRT_not hc.1.1)
  · have hf' : (!A.cov op && isRep op && !rc op) = false := by simpa using hf
    have ha : A.cov op = true := by
      simp only [AT.repF, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hcov
      simp only [Bool.and_eq_false_iff, Bool.not_eq_false'] at hf'
      rcases hcov with h1 | ⟨h1, h2⟩
      · exact h1
      · rcases hf' with (h3 | h3) | h3
        · exact h3
        · rw [h1] at h3; cases h3
        · rw [h2] at h3; cases h3
    exact h P cs pre op k regs vs ok ha (askCtx_repF hc hf') hev himp

theorem atOk_repF (h : ATOk impl X A κ inp w tr) : ATOk impl X (A.repF rc) κ inp w tr :=
  ⟨atAsk_repF h.1, atImp_repF h.2⟩

end RepF

/-! ## The residual imports -/

/-- **The replay ops' residual imports** (along the compile's trail): imports of an `isRep` op neither the
replay template `rt` nor the ask template `A` covers. -/
def impQX (X : Ext) (P : Params) (rt : RT) (A : AT) : CS → List Op → List ℕ
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if (stepOut X P c op).imp && !rt.cov op && !A.cov op && isRep op then
        List.range' c.slots.size (stepOut X P c op).slots.length else []) ++
      impQX X P rt A (c.add op (stepOut X P c op)) ops

/-- Prototype `π`'s replay-op residual imports. -/
def impQP (rt : RT) (A : AT) (π : ℕ) : List ℕ := impQX (Xof π) (protoP π) rt A (CS.init (baseR π)) (protoProg π).ops

/-- **No replay op's import is left** once the template fails at the replay ops `rt` does not cover
(SEG-R2: structural, the compile is not evaluated). -/
theorem impQX_repF (X : Ext) (P : Params) (rt : RT) (A : AT) :
    ∀ (cs : CS) (ops : List Op), impQX X P rt (A.repF rt.cov) cs ops = []
  | _, [] => rfl
  | cs, op :: ops => by
    simp only [impQX, impQX_repF X P rt A _ ops, List.append_nil]
    rw [if_neg]
    simp only [AT.repF]
    cases isRep op <;> cases rt.cov op <;> simp

theorem impQP_repF (rt : RT) (A : AT) (π : ℕ) : impQP rt (A.repF rt.cov) π = [] :=
  impQX_repF _ _ _ _ _ _

theorem bitNx_eq (op : Op) (ops : List Op) (n : ℕ) : bitNx op ops n = bitNxT op ops n := by
  cases op <;> rfl

/-- **The closed residual imports are the replay ops'**: a residual import of the closed template is an
`isRep` op's (`opImp` and the template-free context make every other one covered; a `bitOf` is followed by
its `selectHalf`). -/
theorem impB_sub {X : Ext} (hfl : ExtFl X) {P : Params} {rt : RT} {A : AT} {Xc : Ext}
    {pv : List (ℕ × ℕ × ℕ × ℕ)} {T : BTab} {nx : Bool}
    (hlen : ∀ c op, (stepOut X P c op).slots.length = op.nOut) :
    ∀ (ops : List Op) (cs : CS), bitNxAll cs.slots.size ops = true →
      ∀ i ∈ impBX X P rt (A.close Xc pv T nx) cs ops, i ∈ impQX X P rt A cs ops
  | [], _, _, i, hi => by simp [impBX] at hi
  | op :: ops, cs, hb, i, hi => by
    simp only [impBX, List.mem_append] at hi
    simp only [impQX, List.mem_append]
    simp only [bitNxAll, Bool.and_eq_true] at hb
    rcases hi with hi | hi
    · left
      split_ifs at hi with hc
      swap; · cases hi
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨himp, hrt⟩, hcov⟩, hit⟩, hnx⟩ := hc
      have hcc : closeCov op = false := by
        simp only [AT.close, Bool.or_eq_false_iff] at hcov; exact hcov.1
      have hAc : A.cov op = false := by
        simp only [AT.close, Bool.or_eq_false_iff] at hcov; exact hcov.2
      have hi' := (stepOut_imp_of hfl himp).1
      have hrep : isRep op = true := by
        simp only [closeCov, hit, hi', Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true,
          Bool.and_eq_false_iff, Bool.not_eq_false'] at hcc
        rcases hcc with h | h
        · exact h
        · exfalso
          have := hb.1
          rw [h, Bool.not_true, Bool.false_or, ← bitNx_eq] at this
          rw [CS.align_slots, this] at hnx; cases hnx
      rw [if_pos (by simp [himp, hrt, hrep, hAc])]
      exact hi
    · right
      refine impB_sub hfl hlen ops _ ?_ i hi
      rw [add_slots_size, hlen, CS.align_slots]; exact hb.2

/-! ## The foreign flags -/

/-- **A foreign flag of the compile is at a trail point** where the compile marked it foreign. -/
theorem trail_forsF (X : Ext) (P : Params) (A : AT) : ∀ (ops : List Op) (cs : CS) (pre : Option Op) (k : ℕ)
    {p : Op × ℕ}, p ∈ (compileFromX X P cs ops).fors → p ∈ cs.fors ∨ ∃ (c : CS) (pre' : Option Op) (k' : ℕ),
      c.slots.size = p.2 ∧ (stepOut X P c p.1).foreign = true ∧
      (A.cov p.1 = true → ∀ r ∈ A.rows P c pre' p.1 k', r ∈ askRowsX X P A cs pre k ops)
  | [], _, _, _, _, h => Or.inl h
  | op :: ops, cs, pre, k, p, h => by
    simp only [compileFromX] at h
    rcases trail_forsF X P A ops _ (some op) (if op.item?.isSome then k + 1 else k) h with
      h1 | ⟨c, pre', k', hc, hf, hr⟩
    · simp only [CS.add, align_fors] at h1
      split_ifs at h1 with hfo
      · rcases List.mem_cons.1 h1 with rfl | h1
        · right
          refine ⟨cs.align (alignOf op ops), pre, k, rfl, hfo, fun hcov r hr => ?_⟩
          rw [askRowsX_cons]
          exact List.mem_append_left _ (by rw [if_pos (by simp [hcov])]; exact hr)
        · exact Or.inl h1
      · exact Or.inl h1
    · exact Or.inr ⟨c, pre', k', hc, hf, fun hcov r hr0 => by
        rw [askRowsX_cons]; exact List.mem_append_right _ (hr hcov r hr0)⟩

theorem zPinT_eq : zPinT = zPin := rfl
theorem stFlagT_eq : stFlagT = stFlag := rfl

theorem forCap_opImp {op : Op} (h : forCap op = true) : opImp op = false := by
  cases op <;> first | rfl | (simp [forCap] at h)

theorem closeCov_of_forCap {op : Op} (h : forCap op = true) : closeCov op = true := by
  cases op <;> first | rfl | (simp [forCap] at h)

/-! ## The closed residual -/

/-- **The closed residual run facts** (`SlotRunB` less what the closure gives): the `felems` auxiliary
cells (`colTG`'s, not folded) and the imports of the replay ops neither `rt` nor `A` covers. -/
def SlotRunC (rt : RT) (A : AT) (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∀ s : St, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
    (∀ a ∈ (protoCS π).aux, isBitsA a = false →
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    ∀ i ∈ impQP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)

/-- **The run facts left** (SEG-R2): `SlotRunC` without the replay imports (`impQP_repF`): the `felems`
auxiliary cells (`isBitsA` false) only. -/
def SlotRunF (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∀ s : St, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
    ∀ a ∈ (protoCS π).aux, isBitsA a = false →
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)

/-- **`SlotRunC` from `SlotRunF`** at a template failing at the replay ops `rt` does not cover. -/
theorem slotRunC_of_F {rt : RT} {A : AT} {impl : OpImpl} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace} {w : Asg}
    (h : SlotRunF impl π ι inp tr w) : SlotRunC rt (A.repF rt.cov) impl π ι inp tr w := fun s he =>
  ⟨h s he, fun i hi => by rw [impQP_repF] at hi; cases hi⟩

/-- The closed template of prototype `π` over `A` (its context the template-free one, its tables the
prototype's). -/
def closeP (A : AT) (π : ℕ) : AT := A.close (XofA π) (pvP π) (bitTabP π) (bitNxAll 0 (protoProg π).ops)

theorem xofA_isNone (π : ℕ) (P : Params) (cs : CS) (op : Op) :
    (XofA π P cs op).isNone = (Xof π P cs op).isNone :=
  tplExt4A_isNone _ _ _ _ _ _ P cs op

/-- `Xof`'s outputs are neither imports nor foreign (FEL). -/
theorem extFl_xof (π : ℕ) : ExtFl (Xof π) := extFl_tplExt4A

/-- **`SlotRunB` from the closed residual**: with the closed template's rows holding along the trail. -/
theorem slotRunB_of_close {rt : RT} {A : AT} {impl : OpImpl} {π : ℕ} {ι : Kind} {inp : Input} {tr : Trace}
    {w : Asg} (hlen : ∀ c op, (stepOut (Xof π) (protoP π) c op).slots.length = op.nOut)
    (hone : (protoP π).one.ev w = 1) (hask : ∀ r ∈ askRowsP (closeP A π) π, r.Holds w)
    (h : SlotRunC rt A impl π ι inp tr w) : SlotRunB rt (closeP A π) impl π ι inp tr w := by
  intro s he
  obtain ⟨hx, hi⟩ := h s he
  -- every `bitOf` is followed by its `selectHalf` (the first ask's rows)
  have hnx : bitNxAll 0 (protoProg π).ops = true := by
    obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
    obtain ⟨c, pre', op, ho, hm⟩ := first_ask (Xof π) (protoP π) (closeP A π) (protoProg π).ops
      (CS.init (baseR π)) none (it := .seed) (by rw [protoProg_items, hr]; rfl)
    have hio : op.item?.isSome = true := by rw [ho]; rfl
    by_contra hb
    simp only [Bool.not_eq_true] at hb
    have hrow := hask (failRT (protoP π)) (hm (failRT (protoP π)) (by
      simp only [closeP, AT.close, closeCov_item hio, Bool.false_eq_true, if_false]
      exact List.mem_append_right _ (by simp [hb, hio])))
    exact failRT_not hone hrow
  refine ⟨hx, fun i hi0 => hi i ?_, fun p hp hz hst => ?_⟩
  · exact impB_sub (extFl_xof π) hlen _ _ (by rw [show (CS.init (baseR π)).slots.size = 0 from rfl]; exact hnx) i hi0
  · exfalso
    rcases trail_forsF (Xof π) (protoP π) (closeP A π) _ _ none 0 hp with h0 | ⟨c, pre', k', hcs, hf, hr⟩
    · cases h0
    obtain ⟨op, m⟩ := p
    obtain ⟨hfo, hn⟩ := stepOut_foreign_of (extFl_xof π) hf
    have hfc := opOut_foreign hfo
    have hcc := closeCov_of_forCap hfc
    have hrows := fun x hx0 => hask x (hr (by simp [closeP, AT.close, hcc]) x hx0)
    simp only [closeP, AT.close, hcc, if_true, forCap_opImp hfc, Bool.false_eq_true, if_false] at hrows
    rw [opForeign_eq] at hfo
    have hf : forRows (XofA π) (pvP π) (bitTabP π) (protoP π) c op = [failRT (protoP π)] := by
      rw [forRows, if_pos]
      simp only [hfo, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
      refine ⟨⟨Or.inr (by rw [xofA_isNone, hn]; rfl), ?_⟩, ?_⟩
      · rw [zPinT_eq, hcs]; exact hz
      · rw [stFlagT_eq, hcs]; exact hst
    exact failRT_not hone (hrows _ (List.mem_append_right _ (by rw [hf]; exact List.mem_cons_self)))

end N4s
end FR
