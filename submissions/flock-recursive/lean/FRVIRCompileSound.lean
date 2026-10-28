-- New for `flock-recursive` (BLUEPRINT §4.3, §7; split from `FRVIRCompile` in stage S-E6 to keep
-- each module under FR-R3′'s 1,000 code lines).
import FRVIRCompile

/-!
# `compile_sound`: the program

The induction over an op list (`compileFromX_sound`, with the alignment steps and a sound extension
`ExtOk`) and its two corollaries **`compile_sound`** and **`compileX_sound`** (BLUEPRINT §4.3,
FR-R3′). One op's soundness (`opOut_sound`) is in `FRVIRCompile`.
-/

namespace FR
namespace Circ
open RecursionFast

/-! ## The program -/

/-- **The compiler's invariant**: one slot per register, each representing its register. -/
def Inv (w : Asg) (cs : CS) (regs : Array Val) : Prop :=
  cs.slots.size = regs.size ∧ ∀ i, RepS w (cs.slot i) (rd regs i)

theorem rd_append_left {a b : Array Val} {i : ℕ} (h : i < a.size) : rd (a ++ b) i = rd a i := by
  simp [rd, Array.getElem?_append_left h]

theorem rd_append_right (a : Array Val) (b : List Val) (c : Array Val) {j : ℕ} (h : j < b.length) :
    rd (a ++ b.toArray ++ c) (a.size + j) = b[j] := by
  rw [rd, Array.getElem?_append_left (by simp [h]), Array.getElem?_append_right (by omega)]
  simp [h]

theorem slot_append_right (a : Array Slot) (b : List Slot) (c : Array Slot) {j : ℕ}
    (h : j < b.length) : (a ++ b.toArray ++ c).getD (a.size + j) none = b[j] := by
  simp only [Array.getD_eq_getD_getElem?, Array.append_assoc]
  rw [Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    Array.getElem?_append_left (by simpa using h)]
  simp [h]

theorem inv_append {w : Asg} {cs : CS} {regs : Array Val} (h : Inv w cs regs) {ss : List Slot}
    {vs : List Val} (hl : ss.length = vs.length)
    (hr : ∀ j (hj : j < ss.length), RepS w ss[j] (vs[j]'(hl ▸ hj))) (o : Out) (op : Op)
    (hs : o.slots = ss) : Inv w (cs.add op o) (regs ++ vs.toArray) := by
  subst hs
  refine ⟨by simp [CS.add, h.1, hl], fun i => ?_⟩
  simp only [CS.slot, CS.add]
  by_cases h1 : i < cs.slots.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h1, rd_append_left (h.1 ▸ h1)]
    simpa [CS.slot] using h.2 i
  by_cases h2 : i < cs.slots.size + o.slots.length
  · obtain ⟨j, rfl⟩ : ∃ j, i = cs.slots.size + j := ⟨i - cs.slots.size, by omega⟩
    have := slot_append_right cs.slots o.slots #[] (by omega : j < o.slots.length)
    have h' := rd_append_right regs vs #[] (by omega : j < vs.length)
    simp only [Array.append_empty] at this h'
    rw [this, h.1, h']; exact hr j (by omega)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]; trivial

theorem exec_prefix {impl : OpImpl} {κ : Kind} {inp : Input} :
    ∀ (ops : List Op) (s : St) (tr : Trace) {s' : St} {tr' : Trace},
    exec impl κ inp ops s tr = some (s', tr') → ∃ more : Array Val, s'.regs = s.regs ++ more
  | [], s, tr, s', tr', h => by simp [exec] at h; exact ⟨#[], by simp [← h.1]⟩
  | op :: ops, s, tr, s', tr', h => by
    simp only [exec] at h
    split at h
    · obtain ⟨m, hm⟩ := exec_prefix ops _ _ h; exact ⟨_, by rw [hm, Array.append_assoc]⟩
    · split at h
      · simp at h
      · split at h
        · obtain ⟨m, hm⟩ := exec_prefix ops _ _ h
          exact ⟨_, by rw [hm, Array.push_eq_append, Array.append_assoc]⟩
        · simp at h

/-- **A sound extension** (S-E3): for every op it handles, the contribution has `op.nOut` results,
the op asks nothing, and the contribution's rows, its template instance's rows and its auxiliary
imports give its results (unless imported) and its flag (unless foreign). -/
def ExtOk (impl : OpImpl) (tc : Tpl.TCtx) (X : Ext) : Prop :=
  ∀ (P : Params) (cs : CS) (op : Op) (o : Out), X P cs op = some o →
    o.slots.length = op.nOut ∧
    ∀ (κ : Kind) (inp : Input) (w : Asg) (regs : Array Val), SelOk w P κ →
      (∀ i, RepS w (cs.slot i) (rd regs i)) →
      (∀ q, evalOp impl κ inp regs op ≠ .ask q) ∧
      ((∀ r ∈ o.rows, r.Holds w) →
       (∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w) →
       (∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd regs a.2.1)) →
       ∀ vs ok, evalOp impl κ inp regs op = .vals vs ok →
         (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true))

/-! ## Alignment changes only the rows (by empty rows) and the next cell -/

@[simp] theorem CS.align_slots (cs : CS) (a : Option (ℕ × ℕ)) : (cs.align a).slots = cs.slots := by
  rcases a with _ | ⟨_, _⟩ <;> rfl
@[simp] theorem CS.align_imp (cs : CS) (a : Option (ℕ × ℕ)) : (cs.align a).imp = cs.imp := by
  rcases a with _ | ⟨_, _⟩ <;> rfl
@[simp] theorem CS.align_fors (cs : CS) (a : Option (ℕ × ℕ)) : (cs.align a).fors = cs.fors := by
  rcases a with _ | ⟨_, _⟩ <;> rfl
@[simp] theorem CS.align_tins (cs : CS) (a : Option (ℕ × ℕ)) : (cs.align a).tins = cs.tins := by
  rcases a with _ | ⟨_, _⟩ <;> rfl
@[simp] theorem CS.align_aux (cs : CS) (a : Option (ℕ × ℕ)) : (cs.align a).aux = cs.aux := by
  rcases a with _ | ⟨_, _⟩ <;> rfl

theorem CS.align_rows (cs : CS) (a : Option (ℕ × ℕ)) :
    ∃ pad : List Row, (cs.align a).rows = pad ++ cs.rows ∧ ∀ r ∈ pad, r = ⟨[], [], []⟩ := by
  rcases a with _ | ⟨_, _⟩
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨_, rfl, fun r h => List.eq_of_mem_replicate h⟩

theorem CS.align_slot (cs : CS) (a : Option (ℕ × ℕ)) (i : ℕ) : (cs.align a).slot i = cs.slot i := by
  simp [CS.slot]

theorem compileFromX_cons (X : Ext) (P : Params) (cs : CS) (op : Op) (ops : List Op) :
    compileFromX X P cs (op :: ops) =
      compileFromX X P ((cs.align (alignOf op ops)).add op
        (stepOut X P (cs.align (alignOf op ops)) op)) ops := rfl

theorem noExt_ok (impl : OpImpl) (tc : Tpl.TCtx) : ExtOk impl tc noExt := by
  intro _ _ _ _ h; simp [noExt] at h

theorem compileFromX_mono (X : Ext) (P : Params) : ∀ (ops : List Op) (cs : CS), ∃ ss rs,
    (compileFromX X P cs ops).slots = cs.slots ++ ss ∧ (compileFromX X P cs ops).rows = rs ++ cs.rows ∧
    cs.imp ⊆ (compileFromX X P cs ops).imp ∧ cs.fors ⊆ (compileFromX X P cs ops).fors ∧
    cs.tins ⊆ (compileFromX X P cs ops).tins ∧ cs.aux ⊆ (compileFromX X P cs ops).aux
  | [], cs => ⟨#[], [], by simp [compileFromX]⟩
  | op :: ops, cs => by
    rw [compileFromX_cons]
    obtain ⟨pad, hpad, -⟩ := CS.align_rows cs (alignOf op ops)
    generalize hc : cs.align (alignOf op ops) = cs' at hpad ⊢
    have hs : cs'.slots = cs.slots := by rw [← hc]; simp
    have hi : cs'.imp = cs.imp := by rw [← hc]; simp
    have hf : cs'.fors = cs.fors := by rw [← hc]; simp
    have ht : cs'.tins = cs.tins := by rw [← hc]; simp
    have ha : cs'.aux = cs.aux := by rw [← hc]; simp
    obtain ⟨ss, rs, h1, h2, h3, h4, h5, h6⟩ :=
      compileFromX_mono X P ops (cs'.add op (stepOut X P cs' op))
    refine ⟨(stepOut X P cs' op).slots.toArray ++ ss, rs ++ (stepOut X P cs' op).rows.reverse ++ pad,
      h1.trans (by simp [CS.add, Array.append_assoc, hs]),
      h2.trans (by simp [CS.add, List.reverseAux_eq, List.append_assoc, hpad]),
      fun x hx => h3 ?_, fun x hx => h4 ?_, fun x hx => h5 ?_, fun x hx => h6 ?_⟩ <;>
      simp only [CS.add, hi, hf, ht, ha] <;> (try split) <;> simp [hx]

/-- The induction behind `compile_sound` (with an extension). -/
theorem compileFromX_sound {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} (hX : ExtOk impl tc X) (hP : SelOk w P κ) :
    ∀ (ops : List Op) (cs : CS) (s s' : St) (tr tr' : Trace),
    Inv w cs s.regs → exec impl κ inp ops s tr = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ (compileFromX X P cs ops).imp, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    s'.ok = s.ok ∧ Inv w (compileFromX X P cs ops) s'.regs
  | [], cs, s, s', tr, tr', hI, he, _, _, _, _, _ => by
    simp [exec] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, hI⟩
  | op :: ops, cs, s, s', tr, tr', hI, he, hr, ht, hx, hi, hf => by
    rw [compileFromX_cons] at hr ht hx hi hf ⊢
    have hI' : Inv w (cs.align (alignOf op ops)) s.regs :=
      ⟨by simp [hI.1], fun i => by rw [CS.align_slot]; exact hI.2 i⟩
    generalize cs.align (alignOf op ops) = cs at hI' hr ht hx hi hf ⊢
    clear hI
    rename' hI' => hI
    set o := stepOut X P cs op with ho
    obtain ⟨ss, rs, hsl, hrw, himp, hfor, htin, haux⟩ := compileFromX_mono X P ops (cs.add op o)
    have hro : ∀ r ∈ o.rows, r.Holds w := fun r h =>
      hr r (by
        rw [hrw]; simp only [CS.add, List.reverseAux_eq]
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 h)))
    have hto : ∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w :=
      fun t htm r hr' => ht _ (htin (by simp only [CS.add, Option.mem_def.1 htm]; simp)) r hr'
    have hpre : ∀ (m : Array Val), (s.regs ++ m).extract 0 cs.slots.size = s.regs := fun m => by
      rw [hI.1, Array.extract_append_left, Array.extract_size]
    -- the new registers' values, read off the final state
    have fin : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.imp = true →
        (hl : o.slots.length = vs.length) →
        ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
      intro vs s1 hs1 ⟨m, hm⟩ hio hl j hj
      have := hi (cs.slots.size + j) (himp (by simp [CS.add, hio, List.mem_range'_1, hj]))
      have hs := slot_append_right cs.slots o.slots ss hj
      have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
      rw [CS.slot, hsl] at this; simp only [CS.add] at this
      rw [hs, hm, hs1, hI.1, hv] at this; exact this
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
    -- the step's soundness: the extension's or `opOut`'s
    have hstep : (∀ q, evalOp impl κ inp s.regs op ≠ .ask q) ∨ X P cs op = none := by
      rcases hXo : X P cs op with _ | o'
      · exact .inr rfl
      · exact .inl ((hX P cs op o' hXo).2 κ inp w s.regs hP hI.2).1
    have hlen : o.slots.length = op.nOut := by
      rcases hXo : X P cs op with _ | o'
      · simp only [ho, stepOut, hXo, Option.getD_none]; exact opOut_len P cs op
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).1
    simp only [exec] at he
    split at he
    · rename_i vs ok hev
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := exec_prefix ops _ _ he
      have hsnd : (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true) := by
        rcases hXo : X P cs op with _ | o'
        · simp only [ho, stepOut, hXo, Option.getD_none] at hro ⊢
          exact opOut_sound hP hI.2 op hro hev
        · have eo : o = o' := by simp [ho, stepOut, hXo]
          rw [eo] at hro hto ⊢
          exact ((hX P cs op o' hXo).2 κ inp w s.regs hP hI.2).2 hro hto
            (eo ▸ hauxo vs _ rfl hm) vs ok hev
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        cases hio : o.imp
        · exact fun j hj => (List.forall₂_iff_get.1 (hsnd.1 hio)).2 j hj _
        · exact fin vs _ rfl hm hio hl
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_sound hX hP ops _ _ s' tr tr'
        (inv_append hI hl hnew _ op rfl) he hr ht hx hi hf
      exact ⟨by rw [ih.1, hok, Bool.and_true], ih.2⟩
    · rename_i q hev
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      split at he
      · simp at he
      · rename_i q' a tr0
        split at he
        · have hio : o.imp = true := ho' ▸ ask_imp P cs hev
          have hl : o.slots.length = [Val.d a].length := by
            rw [hlen, ask_nOut hev]; rfl
          have hm := exec_prefix ops _ _ he
          have hnew := fin [.d a] ⟨s.regs.push (.d a), s.ok⟩ rfl hm hio hl
          exact compileFromX_sound hX hP ops _ ⟨s.regs.push (.d a), s.ok⟩ s' tr0 tr'
            (inv_append hI hl hnew _ op rfl) he hr ht hx hi hf
        · simp at he

/-! ## `compile_sound` -/

/-- **`compile_sound`** (BLUEPRINT §4.3, FR-R3′): if the op list runs to state `s` on the trace
(kind `κ`), the selector forms are one-hot at `κ`, every compiled row holds, every import's cells
hold its value and every foreign assertion's flag is set, then the run accepts (`s.ok`) and every
tracked register's cells hold its value. -/
theorem compile_sound {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} (base : ℕ) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compile P base ops).rows, r.Holds w)
    (hi : ∀ i ∈ (compile P base ops).imp, RepS w ((compile P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compile P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compile P base ops).slot i) (rd s.regs i) := by
  have hn : ∀ (ops : List Op) (cs : CS), cs.tins = [] → cs.aux = [] →
      (compileFrom P cs ops).tins = [] ∧ (compileFrom P cs ops).aux = [] := by
    intro ops; induction ops with
    | nil => intro cs h1 h2; exact ⟨h1, h2⟩
    | cons op ops ih =>
      intro cs h1 h2
      exact ih _ (by simp [CS.add, stepOut, noExt, opOut_tin, h1])
        (by simp [CS.add, stepOut, noExt, opOut_aux, h2])
  have h0 := hn ops (CS.init base) rfl rfl
  have h := compileFromX_sound (noExt_ok impl ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) hP ops (CS.init base)
    St.init s tr tr' ⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩ he hr
    (by simp [compile] at h0 ⊢; simp [h0.1]) (by simp [compile] at h0 ⊢; simp [h0.2]) hi hf
  exact ⟨h.1, h.2.2⟩

/-- **`compileX_sound`** (S-E3's `compileT_sound` shape): `compile_sound` with a sound extension;
the template instances' rows and the auxiliary imports join the hypotheses. -/
theorem compileX_sound {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} {tc : Tpl.TCtx} {X : Ext} (hX : ExtOk impl tc X) (base : ℕ)
    (hP : SelOk w P κ) (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (compileX X P base ops).imp, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_sound hX hP ops (CS.init base) St.init s tr tr'
    ⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩ he hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hf
  exact ⟨h.1, h.2.2⟩

end Circ
end FR
