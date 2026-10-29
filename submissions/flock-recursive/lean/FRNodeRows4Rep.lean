-- New for `flock-recursive` (BLUEPRINT revision 4.1, §4.4 "the replay fixed point", A.11's replay
-- templates; stage S-E14, track L-circ).
import FRNodeSound4R

/-!
# The replay `R`: imports discharged by rows, inside the compile's induction

The compiled slot programs leave the six replayed ops (`targetS`, `shiftTarget`, `linkWAll`,
`rsWeight`, `evalM`, `evalL`) as **imports** (`FRVIRCompile.opOut`): fresh cells that no row
constrains, assumed by `compileX_soundK` at the final run (`hi`). A replay row can only say
`cell(out) = f(cells(args))`; it gives `RepS` of the output only if the operands' cells already
represent their registers **at the op**. So the discharge is a staged soundness:

* **`RT`** (a replay template): which ops it covers, and per compile state, op and output slots its
  rows. **`RTOk impl X rt κ`**: a covered op never asks, and its rows, the invariant `InvK` at the
  op and the selector give `RepS` of its outputs at the op's value.
* **`repRowsX`**, **`impRX`**: the rows of every covered op along the compile's trail, and the import
  registers of the ops it does not cover (defined by the same fold as `compileFromX`, so nothing
  evaluates a program).
* **`compileFromX_soundR`**: `compileFromX_soundK`'s induction with `hi` restricted to `impRX` and
  the rows `repRowsX`; **`compileX_soundR`**.

At the node (namespace `N4s`): `repRowsP rt π` (prototype `π`'s replay rows, its frame),
**`SlotRunR`**/**`SlotImpR`** (S-N2's `SlotRun`/`SlotImp` with the covered imports removed),
**`slotImp_of_rep`** (the rows and `SlotImpR` give `SlotImp`), the node's indexed rows `repIRows4`
in each slot region's replay rows (`repBase`, JOURNAL §0) and **`gap4Imp_of_rep`** (`Gap4.imp` from
`StmtN4`, the fold `hfold` and `SlotImpR`).
-/

namespace FR
namespace Circ
open RecursionFast

/-! ## Replay templates -/

/-- **A replay template**: the ops it covers, and for a compile state, an op and the op's output
slots, the rows that compute the outputs from the operands' slots. -/
structure RT where
  cov : Op → Bool
  rows : Params → CS → Op → List Slot → List Row

/-- **A replay template is sound at kind `κ`**: a covered op never asks, and where it is an import,
its rows with the invariant at the op give its outputs' representation. -/
def RTOk (impl : OpImpl) (X : Ext) (rt : RT) (κ : Kind) : Prop :=
  ∀ P cs op, rt.cov op = true →
    (∀ inp regs q, evalOp impl κ inp regs op ≠ .ask q) ∧
    ∀ inp w regs vs ok, SelOk w P κ → InvK w cs regs κ →
      (∀ r ∈ rt.rows P cs op (stepOut X P cs op).slots, r.Holds w) →
      evalOp impl κ inp regs op = .vals vs ok → (stepOut X P cs op).imp = true →
      List.Forall₂ (RepS w) (stepOut X P cs op).slots vs

/-- The template that covers nothing. -/
def RT.none : RT := ⟨fun _ => false, fun _ _ _ _ => []⟩

theorem RT.none_ok (impl : OpImpl) (X : Ext) (κ : Kind) : RTOk impl X RT.none κ :=
  fun _ _ _ h => absurd h Bool.false_ne_true

/-- **The replay rows along the compile's trail** (the alignment and the step exactly as
`compileFromX`). -/
def repRowsX (X : Ext) (P : Params) (rt : RT) : CS → List Op → List Row
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if rt.cov op then rt.rows P c op (stepOut X P c op).slots else []) ++
      repRowsX X P rt (c.add op (stepOut X P c op)) ops

/-- **The import registers the template does not cover**, along the trail. -/
def impRX (X : Ext) (P : Params) (rt : RT) : CS → List Op → List ℕ
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if (stepOut X P c op).imp && !rt.cov op then List.range' c.slots.size (stepOut X P c op).slots.length
      else []) ++ impRX X P rt (c.add op (stepOut X P c op)) ops

theorem repRowsX_cons (X : Ext) (P : Params) (rt : RT) (cs : CS) (op : Op) (ops : List Op) :
    repRowsX X P rt cs (op :: ops) =
      (if rt.cov op then rt.rows P (cs.align (alignOf op ops)) op
          (stepOut X P (cs.align (alignOf op ops)) op).slots else []) ++
        repRowsX X P rt ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op)) ops :=
  rfl

theorem impRX_cons (X : Ext) (P : Params) (rt : RT) (cs : CS) (op : Op) (ops : List Op) :
    impRX X P rt cs (op :: ops) =
      (if (stepOut X P (cs.align (alignOf op ops)) op).imp && !rt.cov op then
          List.range' (cs.align (alignOf op ops)).slots.size
            (stepOut X P (cs.align (alignOf op ops)) op).slots.length else []) ++
        impRX X P rt ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op)) ops :=
  rfl

/-- **Every uncovered import is an import of the compile** (so `impRX` asks nothing new). -/
theorem impRX_sub (X : Ext) (P : Params) (rt : RT) :
    ∀ (ops : List Op) (cs : CS), ∀ i ∈ impRX X P rt cs ops, i ∈ (compileFromX X P cs ops).imp
  | [], _, i, h => by simp [impRX] at h
  | op :: ops, cs, i, h => by
    rw [impRX_cons, List.mem_append] at h
    rw [compileFromX_cons]
    rcases h with h | h
    · obtain ⟨_, _, -, -, hm, -⟩ := compileFromX_mono X P ops
        ((cs.align (alignOf op ops)).add op (stepOut X P (cs.align (alignOf op ops)) op))
      refine hm ?_
      split_ifs at h with hc
      · simp only [Bool.and_eq_true] at hc
        simp only [CS.add, hc.1, if_true]
        exact List.mem_append_left _ h
      · simp at h
    · exact impRX_sub X P rt ops _ i h

/-- The template that covers nothing leaves every import. -/
theorem impRX_none (X : Ext) (P : Params) :
    ∀ (ops : List Op) (cs : CS), ∀ i ∈ (compileFromX X P cs ops).imp, i ∈ cs.imp ∨ i ∈ impRX X P RT.none cs ops
  | [], cs, i, h => .inl (by simpa [compileFromX] using h)
  | op :: ops, cs, i, h => by
    rw [compileFromX_cons] at h
    rcases impRX_none X P ops _ i h with h' | h'
    · simp only [CS.add, CS.align_imp] at h'
      split_ifs at h' with hc
      · rcases List.mem_append.1 h' with h'' | h''
        · refine .inr ?_
          rw [impRX_cons]
          refine List.mem_append_left _ ?_
          simp only [RT.none, hc, Bool.not_false, Bool.and_self, if_true]
          exact h''
        · exact .inl h''
      · exact .inl h'
    · exact .inr (by rw [impRX_cons]; exact List.mem_append_right _ h')

/-! ## The staged soundness -/

/-- **`compileFromX_soundK` with replay rows**: the imports of covered ops are discharged by their
rows at the op (`RTOk`), the others are assumed (`impRX`). -/
theorem compileFromX_soundR {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} {rt : RT} (hX : ExtOkK impl tc X κ) (hP : SelOk w P κ)
    (hR : RTOk impl X rt κ) :
    ∀ (ops : List Op) (cs : CS) (s s' : St) (tr tr' : Trace),
    InvK w cs s.regs κ → exec impl κ inp ops s tr = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ impRX X P rt cs ops, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ r ∈ repRowsX X P rt cs ops, r.Holds w) →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    s'.ok = s.ok ∧ InvK w (compileFromX X P cs ops) s'.regs κ
  | [], cs, s, s', tr, tr', hI, he, _, _, _, _, _, _ => by
    simp [exec] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, hI⟩
  | op :: ops, cs, s, s', tr, tr', hI, he, hr, ht, hx, hi, hrr, hf => by
    rw [impRX_cons] at hi
    rw [repRowsX_cons] at hrr
    rw [compileFromX_cons] at hr ht hx hi hf ⊢
    have hI' : InvK w (cs.align (alignOf op ops)) s.regs κ :=
      ⟨⟨by simp [hI.1.1], fun i => by rw [CS.align_slot]; exact hI.1.2 i⟩,
        fun p hp => by rw [CS.align_kslots] at hp; rw [CS.align_slots]; exact hI.2.1 p hp,
        fun i => by rw [CS.align_slotK]; exact hI.2.2 i⟩
    generalize cs.align (alignOf op ops) = cs at hI' hr ht hx hi hrr hf ⊢
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
    -- an uncovered import's registers: from `hi`
    have fin : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.imp = true → rt.cov op = false →
        (hl : o.slots.length = vs.length) →
        ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
      intro vs s1 hs1 ⟨m, hm⟩ hio hc hl j hj
      have := hi (cs.slots.size + j) (List.mem_append_left _ (by
        simp only [← ho, hio, hc, Bool.not_false, Bool.and_self, if_true, List.mem_range'_1]; omega))
      have hs := slot_append_right cs.slots o.slots ss hj
      have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
      rw [CS.slot, hsl] at this; simp only [CS.add] at this
      rw [hs, hm, hs1, hI.1.1, hv] at this; exact this
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
    have hi' : ∀ i ∈ impRX X P rt (cs.add op o) ops,
        RepS w ((compileFromX X P (cs.add op o) ops).slot i) (rd s'.regs i) :=
      fun i h => hi i (List.mem_append_right _ h)
    simp only [exec] at he
    split at he
    · rename_i vs ok hev
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := exec_prefix ops _ _ he
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
          · exact fin vs _ rfl hm hio hc hl
          · have hrows : ∀ r ∈ rt.rows P cs op o.slots, r.Holds w :=
              fun r h => hrr r (List.mem_append_left _ (by rw [if_pos hc]; exact h))
            exact fun j hj => (List.forall₂_iff_get.1
              ((hR P cs op hc).2 inp w s.regs vs ok hP hI hrows hev hio)).2 j hj _
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2.1 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_soundR hX hP hR ops _ _ s' tr tr'
        (invK_add hI o op hl hnew hsnd.2.2 hpos) he hr ht hx hi' hrr' hf
      exact ⟨by rw [ih.1, hok, Bool.and_true], ih.2⟩
    · rename_i q hev
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      have hc : rt.cov op = false := by
        cases hc : rt.cov op
        · rfl
        · exact absurd hev ((hR P cs op hc).1 inp s.regs q)
      split at he
      · simp at he
      · rename_i q' a tr0
        split at he
        · have hio : o.imp = true := ho' ▸ ask_imp P cs hev
          have hl : o.slots.length = [Val.d a].length := by
            rw [hlen, ask_nOut hev]; rfl
          have hm := exec_prefix ops _ _ he
          have hnew := fin [.d a] ⟨s.regs.push (.d a), s.ok⟩ rfl hm hio hc hl
          exact compileFromX_soundR hX hP hR ops _ ⟨s.regs.push (.d a), s.ok⟩ s' tr0 tr'
            (invK_add hI o op hl hnew (fun f v hf => by rw [ho', opOut_kin] at hf; cases hf) hpos)
            he hr ht hx hi' hrr' hf
        · simp at he

/-- **`compileX_soundK` with replay rows.** -/
theorem compileX_soundR {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} {tc : Tpl.TCtx} {X : Ext} {rt : RT} (hX : ExtOkK impl tc X κ)
    (hR : RTOk impl X rt κ) (base : ℕ) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ impRX X P rt (CS.init base) ops, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hrr : ∀ r ∈ repRowsX X P rt (CS.init base) ops, r.Holds w)
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_soundR hX hP hR ops (CS.init base) St.init s tr tr'
    ⟨⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩, fun p hp => by simp [CS.init] at hp,
      fun i => by simp [CS.slotK, CS.slot, CS.init, RepS]⟩ he hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hrr hf
  exact ⟨h.1, h.2.1.2⟩

end Circ

/-! ## At the node's slots -/

namespace N4s
open RecursionFast Rev4 Circ

/-- Prototype `π`'s compiler extension (`protoCS π = compileX (Xof π) …`). -/
def Xof (π : ℕ) : Ext := tplExt4 (protoF π) (protoR π) (protoLay π).ctx

theorem protoCS_X (π : ℕ) : protoCS π = compileX (Xof π) (protoP π) (baseR π) (protoProg π).ops := rfl

/-- **Prototype `π`'s replay rows** (its frame: M-relative cells of region `π`). -/
def repRowsP (rt : RT) (π : ℕ) : List Row := repRowsX (Xof π) (protoP π) rt (CS.init (baseR π)) (protoProg π).ops

/-- Prototype `π`'s import registers `rt` does not cover. -/
def impRP (rt : RT) (π : ℕ) : List ℕ := impRX (Xof π) (protoP π) rt (CS.init (baseR π)) (protoProg π).ops

/-- **`SlotRun` with the covered imports removed**: only the registers of `impRP` are assumed. -/
def SlotRunR (rt : RT) (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∃ s : St, exec impl ι inp (protoProg π).ops St.init tr = some (s, []) ∧
    (∀ a ∈ (protoCS π).aux, a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ impRP rt π, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

/-- **`SlotImp` with the covered imports removed** (`rt π` per prototype). -/
def SlotImpR (rt : ℕ → RT) (impl₀ : OpImpl) (base : NodeKind → OpImpl) (κ : NodeKind) (v : ℕ) (w : Asg)
    (inp : Input) (tr : Trace) : Prop :=
  ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
    SlotRunR (rt (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w) ∧
      stmtOk4 seq4 (kindP (protoOf κ v) ι) inp = true

/-- **The replay rows hold** at slot `v` (in its prototype's frame, at the slot's assignment). -/
def RepHolds (rt : ℕ → RT) (κ : NodeKind) (v : ℕ) (w : Asg) : Prop :=
  ∀ r ∈ repRowsP (rt (protoOf κ v)) (protoOf κ v), r.Holds (slotAsg κ v w)

/-- **The templates are sound** for every prototype and index (under `implP`). -/
def RepOk (rt : ℕ → RT) (impl₀ : OpImpl) (base : NodeKind → OpImpl) : Prop :=
  ∀ π ≤ 1, ∀ ι, RTOk (implP impl₀ base π ι) (Xof π) (rt π) ι

/-- **The discharge at a slot**: its rows, its replay rows and `SlotImpR` give `SlotImp`. -/
theorem slotImp_of_rep {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind} {v : ℕ} {w : Asg}
    {inp : Input} {tr : Trace} (hrows : SlotRows κ v w) (hrep : RepHolds rt κ v w)
    (h : SlotImpR rt impl₀ base κ v w inp tr) : SlotImp impl₀ base κ v w inp tr := by
  intro ι hS
  obtain ⟨⟨s, he, hx, hi, hf⟩, hst⟩ := h ι hS
  have hπ := protoOf_le' κ v
  have hX := tplExt4_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base hπ ι)
    (protoLay (protoOf κ v))
  have key := compileX_soundR hX (hok _ hπ ι) (baseR (protoOf κ v)) hS he hrows.1 hrows.2 hx hi hrep hf
  exact ⟨⟨s, he, hx, fun i _ => key.2 i, hf⟩, hst⟩

/-- (+) The converse: `SlotImp` gives `SlotImpR` (an uncovered import is an import), so
`SlotImpR` asks nothing `SlotImp` does not. -/
theorem slotImpR_of_imp (rt : ℕ → RT) {impl₀ : OpImpl} {base : NodeKind → OpImpl} {κ : NodeKind}
    {v : ℕ} {w : Asg} {inp : Input} {tr : Trace} (h : SlotImp impl₀ base κ v w inp tr) :
    SlotImpR rt impl₀ base κ v w inp tr := by
  intro ι hS
  obtain ⟨⟨s, he, hx, hi, hf⟩, hst⟩ := h ι hS
  exact ⟨⟨s, he, hx, fun i hm => hi i (impRX_sub _ _ _ _ _ i hm), hf⟩, hst⟩

/-! ## The node's indexed replay rows (JOURNAL §0) -/

/-- **The replay rows' first row in a slot region** (`23·2^15`: after the prototypes' 730,493 rows
and a 3 % gap, `2^18` rows before the link region). -/
def repBase : ℕ := 23 * 2 ^ 15

/-- **Slot `v`'s replay rows** (absolute cells, the prototype's rows moved), at `v·2^20 + repBase + k`. -/
def repIRows4 (rt : ℕ → RT) (κ : NodeKind) (v : ℕ) : List (ℕ × Row) :=
  (repRowsP (rt (protoOf κ v)) (protoOf κ v)).zipIdx.map fun p =>
    (v * slotM4 + repBase + p.2, rowMapC (fun c => mvC (protoOf κ v) v c + κ.oneCell) p.1)

/-- Every element of `l` has its image in `l.zipIdx.map g` (generic, so that no list is evaluated). -/
theorem mem_zipIdx_map {α β : Type*} {l : List α} {r : α} (hr : r ∈ l) (g : α × ℕ → β) :
    ∃ k, g (r, k) ∈ l.zipIdx.map g := by
  obtain ⟨k, hkl, hrk⟩ := List.mem_iff_getElem.1 hr
  refine ⟨k, List.mem_map_of_mem (List.mem_iff_getElem.2 ⟨k, by rw [List.length_zipIdx]; exact hkl, ?_⟩)⟩
  rw [List.getElem_zipIdx, hrk]; simp

/-- **The node's rows give the replay rows** once they are folded in (`hfold`). -/
theorem repHolds_of {rt : ℕ → RT} {κ : NodeKind} {v : ℕ} {w : Asg}
    (hfold : ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    RepHolds rt κ v w := by
  unfold RepHolds
  unfold repIRows4 at hfold
  generalize repRowsP (rt (protoOf κ v)) (protoOf κ v) = l at hfold ⊢
  generalize hF : (fun c => mvC (protoOf κ v) v c + κ.oneCell) = F at hfold
  intro r hr
  obtain ⟨k, hm⟩ := mem_zipIdx_map hr fun p : Row × ℕ => (v * slotM4 + repBase + p.2, rowMapC F p.1)
  have hm' : (v * slotM4 + repBase + k, rowMapC F r) ∈ nodeIRows4 κ := hfold _ hm
  have h3 := hE _ hm'
  dsimp only at h3
  rw [holds_rowMapC, ← hF] at h3
  exact h3

/-- **`Gap4.imp` from the replay rows**: with the fold, `StmtN4`'s rows and `SlotImpR` at every
active slot give `SlotImp` there. -/
theorem gap4Imp_of_rep {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) (pf : Trace → Proof) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg}
    (hfold : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImpR rt impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) := by
  intro v hv
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hlt := active_lt pf hv
  exact slotImp_of_rep hT₀ hT hok (slotRows_of (one_of_pubCells hP) hlt hE)
    (repHolds_of (hfold v hlt) hE) (h v hv)

end N4s
end FR
