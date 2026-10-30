-- G6: this module also holds the former modules `FRNodeRows4RepK`, `FRNodeRows4RepN`, `FRNodeRows4RepW`, `FRNodeRows4RepRsK`, `FRVIRTplRepL`, `FRNodeRows4RepLT`, `FRNodeRun4S` (one section each, in import order).
import FRNodeRun4
import FRVIRTplEval
import FRInitFuse
import FRVIRTplRepT
import FRNodeRows4RepCFRs
import FRNodeRows4
import FRVerifierImplNode4F
import FRSoundness4Qry

section G6_FRNodeRows4RepK

-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).

/-!
# Kind-muxed replay templates for the previous node's ops

Prototype 0 (the previous node's program) runs at index `ι` the ops of the node kind `nodeAt ι`
(`implP impl₀ base 0 ι = (implN4F base (nodeAt ι)).fixK .N30`), so a replay of one of its ops
computes every kind's value and selects one by the selectors:

* **`KOp`**: a covered op's operand registers at each index, its sub-template per node kind and
  operand types, its output types. **`rtK K cb`**: the replay template that instantiates
  `kmuxT` (`FRVIRTplKMux`) over the three indices' operand blocks (the operands' forms at each
  index, `CS.slotK`) and the selectors, with its locals from cell `cb`, and one row
  `one · out_c = T.out_c` per output component on the import's own cells. Anything else (an operand
  without forms, an output slot of another type) gets the rejecting row `one · one = 0`.
* **`KOk impl ι K`**: the per-op obligation, a statement about pure functions: the sub-template of
  `nodeAt ι` at the operands' types computes the op's values. **`rtK_okW`**: `KOk` gives `RTOkW`
  (`FRNodeRows4Rep`: the replay rows at an assignment agreeing with the slot's below the frame bound
  `B`; every form the template reads is checked below `B`).
* **`RT.orElse`** (`RT.orElse_ok`, `RT.orElse_okW`): two templates, the first where it covers.
* **`rtST0`** (`rtST0_ok`): prototype 0's `shiftTarget` is `0` (its `bnd` operand is the constant
  `0⁴ ‖ last`: both digest terms of `shiftTargetI` vanish), one row behind a compile-time check of
  `bnd`'s forms.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## Combining replay templates -/

theorem _root_.FR.Circ.RT.orElse_ok {impl : OpImpl} {X : Ext} {κ : Kind} {rt₁ rt₂ : RT} (h₁ : RTOk impl X rt₁ κ)
    (h₂ : RTOk impl X rt₂ κ) : RTOk impl X (rt₁.orElse rt₂) κ := by
  intro P cs op hc
  by_cases h : rt₁.cov op = true
  · obtain ⟨ha, hb⟩ := h₁ P cs op h
    exact ⟨ha, fun inp w regs vs ok hP hI hr => hb inp w regs vs ok hP hI (by simpa [RT.orElse, h] using hr)⟩
  · have h' : rt₂.cov op = true := by simpa [RT.orElse, h] using hc
    obtain ⟨ha, hb⟩ := h₂ P cs op h'
    exact ⟨ha, fun inp w regs vs ok hP hI hr => hb inp w regs vs ok hP hI (by simpa [RT.orElse, h] using hr)⟩

theorem rej_false {P : Params} {w : Asg} (hone : P.one.ev w = 1) {l : List Row} (hm : rejRow P ∈ l)
    (h : ∀ r ∈ l, r.Holds w) : False :=
  rej_not hone (h _ hm)

theorem _root_.FR.Circ.RT.orElse_okW {impl : OpImpl} {X : Ext} {κ : Kind} {B : ℕ} {rt₁ rt₂ : RT}
    (h₁ : RTOkW impl X rt₁ κ B) (h₂ : RTOkW impl X rt₂ κ B) : RTOkW impl X (rt₁.orElse rt₂) κ B := by
  intro P cs op hc
  by_cases h : rt₁.cov op = true
  · obtain ⟨ha, hb⟩ := h₁ P cs op h
    exact ⟨ha, fun inp w w' regs vs ok hP hP' hI hA hr =>
      hb inp w w' regs vs ok hP hP' hI hA (by simpa [RT.orElse, h] using hr)⟩
  · have h' : rt₂.cov op = true := by simpa [RT.orElse, h] using hc
    obtain ⟨ha, hb⟩ := h₂ P cs op h'
    exact ⟨ha, fun inp w w' regs vs ok hP hP' hI hA hr =>
      hb inp w w' regs vs ok hP hP' hI hA (by simpa [RT.orElse, h] using hr)⟩

/-! ## The output side: copy rows on the import's cells -/

theorem outF_cons (t : Ty) (ls : List Lin) (os : List Slot) : outF (some (t, ls) :: os) = ls ++ outF os :=
  rfl

theorem outsOk_len : ∀ {tys : List Ty} {outs : List Slot}, outsOk tys outs = true →
    (outF outs).length = (tys.map Ty.len).sum
  | [], [], _ => rfl
  | t :: ts, some (t', ls) :: os, h => by
    simp only [outsOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hl⟩, h⟩ := h
    rw [outF_cons, List.length_append, hl, outsOk_len h, List.map_cons, List.sum_cons]

/-- **The output slots represent the values** once their forms evaluate to the values' encodings. -/
theorem outsOk_rep {w : Asg} : ∀ {tys : List Ty} {outs : List Slot} {vs : List Val},
    outsOk tys outs = true → vs.map tyOf = tys.map some →
    (outF outs).map (Lin.ev w) = vs.flatMap encV → List.Forall₂ (RepS w) outs vs
  | [], [], [], _, _, _ => .nil
  | t :: ts, some (t', ls) :: os, v :: vs, h, ht, he => by
    simp only [outsOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hl⟩, h⟩ := h
    simp only [List.map_cons, List.cons.injEq] at ht
    have hl' : ls.length = (encV v).length := by rw [encV_length ht.1, hl]
    rw [outF_cons, List.map_append, List.flatMap_cons] at he
    have h1 := congrArg (List.take ls.length) he
    have h2 := congrArg (List.drop ls.length) he
    rw [List.take_left' (by simp), hl', List.take_left' rfl] at h1
    rw [List.drop_left' (by simp), hl', List.drop_left' rfl] at h2
    exact .cons ⟨ht.1, h1⟩ (outsOk_rep h ht.2 h2)
  | [], _ :: _, _, h, _, _ => by simp [outsOk] at h
  | _ :: _, [], _, h, _, _ => by simp [outsOk] at h
  | _ :: _, none :: _, _, h, _, _ => by simp [outsOk] at h
  | [], [], _ :: _, _, ht, _ => by simp at ht
  | _ :: _, some _ :: _, [], _, ht, _ => by simp at ht

theorem copyRows_ev {P : Params} {w : Asg} (hone : P.one.ev w = 1) {outs : List Slot} {o : List Lin}
    (hl : (outF outs).length = o.length) (h : ∀ r ∈ copyRows P outs o, r.Holds w) :
    (outF outs).map (Lin.ev w) = o.map (Lin.ev w) := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have hi : i < (outF outs).length := by simpa using h1
  have := h _ (List.mem_map.2 ⟨((outF outs)[i], i), List.mem_iff_getElem.2
    ⟨i, by simpa using hi, by simp [List.getElem_zipIdx]⟩, rfl⟩)
  simp only [Row.Holds, hone, one_mul] at this
  rw [List.getElem_map, List.getElem_map, this, List.getD_eq_getElem _ _ (hl ▸ hi)]

/-! ## The input side: the operands' forms at each index -/

/-- **Where the forms represent the operands** (`InvK`), they evaluate to the operands' encodings,
and the types are the operands' types. -/
theorem kOps_rep {w : Asg} {cs : CS} {regs : Array Val} {ι : Kind}
    (hI : ∀ i, RepS w (cs.slotK i ι) (rd regs i)) : ∀ {as : List ℕ} {ts : List Ty} {fs : List Lin},
    kOps cs ι as = some (ts, fs) →
    as.map (fun a => tyOf (rd regs a)) = ts.map some ∧
      fs.map (Lin.ev w) = as.flatMap fun a => encV (rd regs a)
  | [], ts, fs, h => by simp only [kOps, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | a :: as, ts, fs, h => by
    simp only [kOps] at h
    split at h
    · rename_i t ls ts' fs' hs hk
      split_ifs at h with hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ha := hI a; rw [hs] at ha
      obtain ⟨h1, h2⟩ := kOps_rep hI hk
      exact ⟨by simp [ha.1, h1], by simp [ha.2, h2]⟩
    · simp at h

/-- A form list's values at `w`, past its end `0`. -/
theorem inpIs_envOf (w : Asg) (one : Lin) (ins : List Lin) (cb : ℕ) :
    InpIs (envOf w one ins cb) (ins.map (Lin.ev w)) := fun i => by
  simp only [envOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ins[i]? <;> rfl

/-! ## The kind-muxed op template -/

/-- **The per-op obligation** (pure functions): at index `ι`, the op never asks, its sub-templates
have one output per component, and the sub-template of `nodeAt ι` at the operands' types computes
the op's values from the operands' encodings. -/
def KOk (impl : OpImpl) (ι : Kind) (K : KOp) : Prop :=
  ∀ op, K.cov op = true → (∀ inp regs q, evalOp impl ι inp regs op ≠ .ask q) ∧
    (∀ ν ts, (K.T op ν ts).outs.length = (K.tys.map Ty.len).sum) ∧
    ∀ inp regs vs ok ts, evalOp impl ι inp regs op = .vals vs ok → K.inOk ts = true →
      (K.args op ι).map (fun a => tyOf (rd regs a)) = ts.map some →
      vs.map tyOf = K.tys.map some ∧
      ∀ e : Env, e.one = 1 → InpIs e ((K.args op ι).flatMap fun a => encV (rd regs a)) →
        Eqns e (K.T op (nodeAt ι) ts).gates 0 → (K.T op (nodeAt ι) ts).outs.map (LinT.ev e) = vs.flatMap encV

theorem kBlocks_some {K : KOp} {cs : CS} {op : Op} {bs : List (List Ty × List Lin)}
    (h : kBlocks K cs op = some bs) (ι : Kind) :
    ∃ b, bs.length = 3 ∧ bs[kIx ι]? = some b ∧ kOps cs ι (K.args op ι) = some b := by
  unfold kBlocks at h
  split at h
  · rename_i a b c ha hb hc
    simp only [Option.some.injEq] at h; subst h
    cases ι
    · exact ⟨a, rfl, rfl, ha⟩
    · exact ⟨b, rfl, rfl, hb⟩
    · exact ⟨c, rfl, rfl, hc⟩
  · simp at h

theorem nodeAt_kIx (ι : Kind) (bs : List (List Ty × List Lin)) (K : KOp) (op : Op) (hl : bs.length = 3) :
    ([K.T op .N4 (bs.getD 0 ([], [])).1, K.T op .N2 (bs.getD 1 ([], [])).1,
      K.T op .N8 (bs.getD 2 ([], [])).1] : List Tpl)[kIx ι]'(by cases ι <;> simp [kIx]) =
      K.T op (nodeAt ι) (bs.getD (kIx ι) ([], [])).1 := by
  cases ι <;> rfl

/-- The selectors' values under `SelOk`: one-hot at `kIx ι`. -/
theorem sels_ev {w : Asg} {P : Params} {ι : Kind} (hP : SelOk w P ι) :
    (kinds.map P.sel).map (Lin.ev w) = (List.range 3).map fun j => if j = kIx ι then 1 else 0 := by
  simp only [kinds, List.map_cons, List.map_nil, hP.2]
  cases ι <;> simp [kIx, List.range_succ]

/-- **The kind-muxed template computes the selected kind's sub-template** (pure template
reasoning: the blocks' values `vb`, the selectors one-hot at `kIx ι`). -/
theorem kTpl_ok {e : Env} (h1 : e.one = 1) {K : KOp} {op : Op} {bs : List (List Ty × List Lin)}
    (hl3 : bs.length = 3) {ι : Kind} {vb : List (List F)}
    (hvb : vb.map List.length = bs.map fun b => b.2.length)
    (hin : InpIs e (vb.flatten ++ (List.range 3).map fun j => if j = kIx ι then 1 else 0))
    (hlen : ∀ ν ts, (K.T op ν ts).outs.length = (K.tys.map Ty.len).sum) {out : List F}
    (hT : ∀ e' : Env, e'.one = 1 → InpIs e' (vb.getD (kIx ι) []) →
      Eqns e' (K.T op (nodeAt ι) (bs.getD (kIx ι) ([], [])).1).gates 0 →
      (K.T op (nodeAt ι) (bs.getD (kIx ι) ([], [])).1).outs.map (LinT.ev e') = out)
    (h : Eqns e (kTpl K op bs).gates 0) : (kTpl K op bs).outs.map (LinT.ev e) = out := by
  unfold kTpl at h ⊢
  dsimp only at h ⊢
  have hjl : kIx ι < 3 := by cases ι <;> simp [kIx]
  have hvl : vb.length = 3 := by simpa [hl3] using congrArg List.length hvb
  have hwl : (bs.map fun b => b.2.length).sum = vb.flatten.length := by
    rw [List.length_flatten, hvb]
  obtain ⟨k', hE', hO⟩ := kmuxT_ok (σ := kSig (bs.map fun b => b.2.length))
    (so := (bs.map fun b => b.2.length).sum) (nout := (K.tys.map Ty.len).sum)
    (ts := [K.T op .N4 (bs.getD 0 ([], [])).1, K.T op .N2 (bs.getD 1 ([], [])).1,
      K.T op .N8 (bs.getD 2 ([], [])).1]) (j0 := kIx ι) (e := e) (by cases ι <;> simp [kIx])
    (by rw [nodeAt_kIx ι bs K op hl3]; exact hlen _ _)
    (fun j hj => by
      rw [hin, hwl, getD_append_right]
      simp only [List.length_cons, List.length_nil] at hj
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp) (by exact h)
  rw [nodeAt_kIx ι bs K op hl3] at hE' hO
  rw [hO]
  refine hT _ (by simp [pullE, h1]) (fun i => ?_) hE'
  have hvj : (vb.getD (kIx ι) []).length = (bs.map fun b => b.2.length).getD (kIx ι) 0 := by
    rw [← hvb, List.getD_eq_getElem _ _ (by simpa [hvl] using hjl),
      List.getD_eq_getElem _ _ (by simpa [hvl] using hjl), List.getElem_map]
  simp only [pullE, kSig]
  split_ifs with hi
  · have hoff : ((bs.map fun b => b.2.length).take (kIx ι)).sum = ((vb.take (kIx ι)).map List.length).sum := by
      rw [List.map_take, hvb]
    have hle := flatten_le (vb := vb) (j0 := kIx ι) (hvl ▸ hjl)
    rw [← List.getD_eq_getElem _ [] (hvl ▸ hjl)] at hle
    rw [ev_I, hin, hoff, getD_append_left (by omega),
      flatten_getD (hvl ▸ hjl) (by rw [← List.getD_eq_getElem _ [] (hvl ▸ hjl), hvj]; exact hi),
      List.getD_eq_getElem _ [] (hvl ▸ hjl)]
  · rw [ev_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

-- `gatesAtGo_eq`, `rowsTR_eq`: moved to `FRNodeRows4RepCFP` (CF2; the plan imports it).

theorem rtK_rows {K : KOp} {B cb : ℕ} {P : Params} {cs : CS} {op : Op} {outs : List Slot}
    (hc : K.cov op = true) : (rtK K B cb).rows P cs op outs = kRows K B cb P cs op outs := by
  unfold rtK; dsimp only; rw [ite_cond_eq_true _ _ (eq_true hc)]

/-- **`KOk` gives `RTOkW`** (the replay rows at `w'`, agreeing with `w` below `B`; the template's
locals from `cb`). -/
theorem rtK_okW {impl : OpImpl} {X : Ext} {ι : Kind} {K : KOp} (B cb : ℕ) (hK : KOk impl ι K) :
    RTOkW impl X (rtK K B cb) ι B := by
  intro P cs op hc
  obtain ⟨hask, hlen, hval⟩ := hK op hc
  refine ⟨hask, fun inp w w' regs vs ok hP hP' hI hA hrows hev _ => ?_⟩
  generalize (stepOut X P cs op).slots = outs at hrows ⊢
  rw [rtK_rows hc] at hrows
  unfold kRows at hrows
  simp only [rowsTR_eq] at hrows
  split at hrows
  · rename_i bs hbs
    split_ifs at hrows with hoi
    · simp only [Bool.and_eq_true] at hoi
      obtain ⟨⟨ho, hok⟩, hlt⟩ := hoi
      rw [List.all_append, Bool.and_eq_true] at hlt
      obtain ⟨b, hl3, hb, hk⟩ := kBlocks_some hbs ι
      obtain ⟨hty, hfe⟩ := kOps_rep hI.2.2 hk
      obtain ⟨htv, hT⟩ := hval inp regs vs ok b.1 hev
        (List.all_eq_true.1 hok b (List.mem_of_getElem? hb)) hty
      have hE := inst_eqns hP'.1 (kIns P bs) cb (kTpl K op bs)
        fun r hr => hrows _ (List.mem_append_left _ (List.mem_map_of_mem hr))
      have hbj : bs.getD (kIx ι) ([], []) = b := by
        rw [List.getD_eq_getElem?_getD, hb]; rfl
      have hins : (kIns P bs).map (Lin.ev w') =
          (bs.map fun b => b.2.map (Lin.ev w')).flatten ++ (List.range 3).map fun j => if j = kIx ι then 1 else 0 := by
        rw [kIns, List.map_append, sels_ev hP', List.map_flatten, List.map_map]; rfl
      have hin := inpIs_envOf w' P.one (kIns P bs) cb
      rw [hins] at hin
      -- block `kIx ι`'s forms read the same at `w'` and `w`
      have hbw : b.2.map (Lin.ev w') = b.2.map (Lin.ev w) := by
        refine map_ev_agree hA (List.all_eq_true.2 fun l hl => List.all_eq_true.1 hlt.1 l ?_)
        rw [kIns]; refine List.mem_append_left _ (List.mem_flatten.2 ⟨b.2, ?_, hl⟩)
        exact List.mem_map.2 ⟨b, List.mem_of_getElem? hb, rfl⟩
      have hO := kTpl_ok (e := envOf w' P.one (kIns P bs) cb) hP'.1 hl3 (vb := bs.map fun b => b.2.map (Lin.ev w'))
        (by simp [Function.comp_def]) hin hlen (out := vs.flatMap encV) (fun e' h1' hi' hE' => by
          rw [hbj] at hE' ⊢
          refine hT e' h1' (fun i => ?_) hE'
          have hvbj : (bs.map fun b => b.2.map (Lin.ev w')).getD (kIx ι) [] = b.2.map (Lin.ev w) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map, hb]; exact hbw
          rw [hi', hvbj, ← hfe]) hE
      have hcl : (outF outs).length = ((kTpl K op bs).outs.map (instLin P.one (kIns P bs) cb)).length := by
        rw [outsOk_len ho, List.length_map]
        simp [kTpl, kmuxT]
      have hc' := copyRows_ev hP'.1 hcl fun r hr => hrows r (List.mem_append_right _ hr)
      refine outsOk_rep ho htv ?_
      rw [← map_ev_agree hA hlt.2, hc', List.map_map, ← hO]
      exact List.map_congr_left fun l _ => instLin_ev _ _ _ _ l
    · exact (rej_false hP'.1 (List.mem_singleton_self _) hrows).elim
  · exact (rej_false hP'.1 (List.mem_singleton_self _) hrows).elim

/-! ## Prototype 0's `shiftTarget`: zero -/

theorem zeroLin_ev {l : Lin} (h : zeroLin l = true) (w : Asg) : l.ev w = 0 := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [zeroLin, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [Lin.ev_cons, h.1, zero_mul, zero_add, ih h.2]

theorem stOut_ok {B : ℕ} {P : Params} {cs : CS} {bd : ℕ} {outs : List Slot} {w w' : Asg}
    (hA : Agree B w w') (hone : P.one.ev w' = 1)
    (hr : ∀ r ∈ stOut B P cs bd outs, r.Holds w') : bndZ cs bd = true ∧ List.Forall₂ (RepS w) outs [.f 0] := by
  unfold stOut at hr
  split at hr
  · rename_i o
    by_cases hb : (bndZ cs bd && linLt B o) = true
    · rw [ite_cond_eq_true _ _ (eq_true hb)] at hr
      rw [Bool.and_eq_true] at hb
      have := hr _ (List.mem_singleton_self _)
      simp only [Row.Holds, hone, one_mul, Lin.ev_nil, ev_agree hA hb.2] at this
      exact ⟨hb.1, .cons ⟨rfl, by simp only [List.map_cons, List.map_nil, encV, this]⟩ .nil⟩
    · rw [ite_cond_eq_false _ _ (eq_false hb)] at hr; exact (rej_false hone (List.mem_singleton_self _) hr).elim
  · exact (rej_false hone (List.mem_singleton_self _) hr).elim

theorem digBit_zero (σ : ℕ) : Impl.digBit 0 0 σ = false := by
  unfold Impl.digBit; split_ifs <;> exact bitF_zero _

/-- The digest weight of the zero digest is `0`. -/
theorem digestMle_zero (Eθ : Array F) : Impl.digestMle Eθ 0 0 = 0 := by
  unfold Impl.digestMle
  rw [sumTo_eq]
  exact Finset.sum_eq_zero fun σ _ => by rw [digBit_zero]; rfl

/-- **`shiftTargetI` with zero digests is `0`.** -/
theorem shiftTargetI_zero (κs : F) (τ θ bnd : Array F) (h : ∀ j < 4, bnd.getD j 0 = 0) :
    Impl.shiftTargetI κs τ θ bnd = 0 := by
  unfold Impl.shiftTargetI
  simp only [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), digestMle_zero,
    mul_zero, add_zero]

/-- **The bases' `shiftTarget` is `shiftTargetI`** (at the certificate's `base = fun _ => implC …`:
`rfl`). -/
def STBase (base : NodeKind → OpImpl) : Prop := ∀ ν, (base ν).shiftTarget = Impl.shiftTargetI

/-- **Prototype 0's `shiftTarget` replay is sound** at every index, under `STBase`. -/
theorem rtST0_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hB : STBase base) (B : ℕ) (ι : Kind) :
    RTOkW (implP impl₀ base 0 ι) (Xof 0) (rtST0 B) ι B := by
  intro P cs op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t h bd ks
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp w w' regs vs ok hP hP' hI hA hrows hev _ => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  generalize (stepOut (Xof 0) P cs (.shiftTarget t h bd ks)).slots = outs at hrows ⊢
  have hr : ∀ r ∈ stOut B P cs bd outs, r.Holds w' := fun r hm =>
    hrows r (by simp only [rtST0, isST, ite_true]; exact hm)
  obtain ⟨hb, hrep⟩ := stOut_ok hA hP'.1 hr
  -- the value is `0`
  have hz : ∀ j < 4, (rd regs bd).toAF.getD j 0 = 0 := by
    intro j hj
    have hbι := List.all_eq_true.1 hb ι (by cases ι <;> simp [kinds])
    have hrep' := hI.2.2 bd
    revert hbι hrep'
    rcases cs.slotK bd ι with _ | ⟨t', ls⟩
    · intro hbι; simp at hbι
    · cases t' <;> intro hbι hrep' <;> try (simp at hbι; done)
      dsimp only at hbι
      obtain ⟨x, hx, -, hls⟩ := rep_af hrep'
      rw [hx]
      have hzj : zeroLin (ls.getD j []) = true := List.all_eq_true.1 hbι j (List.mem_range.2 hj)
      simp only [Val.toAF]
      by_cases hjl : j < ls.length
      · have : (ls.map (Lin.ev w)).getD j 0 = x.toList.getD j 0 := by rw [hls]
        rw [← arr_getD, ← this, List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map,
          ← List.getD_eq_getElem _ [] hjl]
        exact zeroLin_ev hzj w
      · have hs : x.size ≤ j := by
          have := congrArg List.length hls; simp at this; omega
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hs]; rfl
  have hv : (implP impl₀ base 0 ι).shiftTarget (rd regs ks).toF (rd regs t).toAF (rd regs h).toAF
      (rd regs bd).toAF = 0 := by
    simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4, Impl.withRS4]
    rw [hB (nodeAt ι)]
    exact shiftTargetI_zero _ _ _ _ hz
  rw [hv]; exact hrep

end N4s
end FR

end G6_FRNodeRows4RepK

section G6_FRNodeRows4RepN

-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).

/-!
# The previous node's replay templates (prototype 0)

* **`kLW`**: `linkWAll`'s kind-muxed replay (sub-template `Tpl.tplLW ν a b` on operands
  `[af a, af b]`); **`kLW_ok`**: `KOk` at every index (`Tpl.tplLW_ok`; the value is
  `linkWAll4I (nodeAt ι)`).
* **`rtLinkSegW`** (`rtLinkSegW_ok`): S-E14's segment `linkWAll` replay (`0^8`) with its output cells
  checked below the frame bound.
* **`rtN0`**: prototype 0's templates: `shiftTarget` (`rtST0`, the value `0`) and `linkWAll` (`kLW`,
  locals from `cbLW = repB`); **`rtC1 π`**: `rtN0` at prototype 0, `rtLinkSegW` at prototype 1.
* **`rtC1_ok`**: `RTOkW` at `repB` for both prototypes and every index, under `LinkZero impl₀` (S-E14)
  and `STBase base` (both `rfl` at the certificate's `implC`).

**The replay frame**: the templates read the compile's forms (cells below `repB = 2^40`, checked at
compile time) and put their locals from `repB` up; `FRNodeRows4RepW.repMapC` sends those to slot 0's
spare region.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## `linkWAll` -/

theorem implP0_linkWAll {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) (tt rr : Array F) :
    (implP impl₀ base 0 ι).linkWAll ι tt rr = NI4.linkWAll4I (nodeAt ι) tt rr := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4]
  rfl

theorem linkWAll4I_size (ν : Rev4.NodeKind) (tt rr : Array F) : (NI4.linkWAll4I ν tt rr).size = nLinkFam := by
  unfold NI4.linkWAll4I; simp

/-- **`linkWAll`'s replay obligation holds at every index.** -/
theorem kLW_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kLW := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t p
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => ?_, fun inp regs vs ok ts hev hin hty => ?_⟩
  · simp only [kLW, lwT]
    split
    · rw [tplLW_outs]; rfl
    · simp [nLinkFam, Ty.len]
  · simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [implP0_linkWAll]
    simp only [kLW, lwArgs] at hty ⊢
    refine ⟨by simp [tyOf, linkWAll4I_size], fun e h1 hi hE => ?_⟩
    match ts, hin, hty with
    | [.af a, .af b], _, hty =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hty
      obtain ⟨h1t, h1p, -⟩ := hty
      obtain ⟨tt, htt⟩ : ∃ tt, rd regs t = .af tt := by
        rcases hv : rd regs t <;> simp [hv, tyOf] at h1t; exact ⟨_, rfl⟩
      obtain ⟨rr, hrr⟩ : ∃ rr, rd regs p = .af rr := by
        rcases hv : rd regs p <;> simp [hv, tyOf] at h1p; exact ⟨_, rfl⟩
      rw [htt, tyOf] at h1t; rw [hrr, tyOf] at h1p
      simp only [Option.some.injEq, Ty.af.injEq] at h1t h1p
      subst h1t h1p
      simp only [lwT] at hE ⊢
      simp only [htt, hrr, Val.toAF, List.flatMap_cons, List.flatMap_nil, List.append_nil, encV] at hi ⊢
      rw [tplLW_ok hi h1 hE]
      simp [encV]

/-! ## The segment's `linkWAll` at the second assignment -/

theorem rep_agree {B : ℕ} {w w' : Asg} (hA : Agree B w w') {t : Ty} {ls : List Lin} {v : Val}
    (h : RepS w' (some (t, ls)) v) (hl : ls.all (linLt B) = true) : RepS w (some (t, ls)) v :=
  ⟨h.1, by rw [← map_ev_agree hA hl]; exact h.2⟩

theorem forall2_agree {B : ℕ} {w w' : Asg} (hA : Agree B w w') :
    ∀ {outs : List Slot} {vs : List Val}, List.Forall₂ (RepS w') outs vs → (outF outs).all (linLt B) = true →
      List.Forall₂ (RepS w) outs vs
  | [], [], .nil, _ => .nil
  | some (t, ls) :: os, v :: vs, .cons h hs, hl => by
    rw [outF_cons, List.all_append, Bool.and_eq_true] at hl
    exact .cons (rep_agree hA h hl.1) (forall2_agree hA hs hl.2)
  | none :: os, v :: vs, .cons _ hs, hl => .cons trivial (forall2_agree hA hs hl)

theorem rtLinkSegW_ok {impl₀ : OpImpl} (base : Rev4.NodeKind → OpImpl) (hZ : LinkZero impl₀) (B : ℕ)
    (ι : Kind) : RTOkW (implP impl₀ base 1 ι) (Xof 1) (rtLinkSegW B) ι B := by
  intro P cs op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t p
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp w w' regs vs ok hP hP' _ hA hrows hev _ => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  have hv : (implP impl₀ base 1 ι).linkWAll ι (rd regs t).toAF (rd regs p).toAF =
      Array.replicate nLinkFam 0 := by
    simp only [implP, one_ne_zero, ite_false, OpImpl.fixK, implSeg]; exact hZ _ _
  rw [hv]
  generalize (stepOut (Xof 1) P cs (.linkWAll t p)).slots = outs at hrows ⊢
  simp only [rtLinkSegW, isLinkW, ite_true] at hrows
  split_ifs at hrows with hl
  · exact forall2_agree hA (zeroRows_sound hP'.1 hrows) hl
  · exact (rej_false hP'.1 (List.mem_singleton_self _) hrows).elim

/-! ## Prototype 0's templates, and both prototypes' -/

/-- **The replay templates per prototype**: `rtN0` at prototype 0, the segment's `linkWAll` at
prototype 1. -/
def rtC1 (π : ℕ) : RT := if π = 0 then rtN0 else if π = 1 then rtLinkSegW repB else RT.none

/-- **Every template of `rtC1` is sound** (`RTOkW` at `repB`), under `LinkZero impl₀` (S-E14) and
`STBase base`. -/
theorem rtC1_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtC1 π) ι repB := by
  by_cases h : π = 0
  · subst h
    simp only [rtC1, ite_true, rtN0]
    exact RT.orElse_okW (rtST0_ok hB repB ι) (rtK_okW repB cbLW (kLW_ok ι))
  · obtain rfl : π = 1 := by omega
    simp only [rtC1, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

/-- (+) At the certificate's `implC`, `STBase` holds by `rfl`. -/
theorem stBase_implC (fin : Finals) (lRows : List Row) (κs₀ : F) :
    STBase (fun _ => Impl.implC fin lRows κs₀) := fun _ => rfl

end N4s
end FR

end G6_FRNodeRows4RepN

section G6_FRNodeRows4RepW

-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).

/-!
# The replay rows at the spare region's assignment

S-E14's `compileFromX_soundR` evaluates the replay rows at the slot's own assignment, so a replay
template's locals would have to be cells of the slot's region (prototype 0's region is full,
PACK-4.4 §6.1). Here the replay rows hold at **`repAsg κ v w`**: the slot's assignment on the
compile's frame (cells below `repB`), the spare region's cells above it (`repMapC`).

* **`compileFromX_soundRW`**, **`compileX_soundRW`**: S-E14's induction with the replay rows at `w'`
  (`Agree B w w'`, `SelOk w' P`, `RTOkW`).
* At the node: **`repAsg`**, **`RepHoldsW`**, **`RepOkW`**, **`slotImp_of_repW`** (the slot's rows, the
  replay rows at `repAsg` and `SlotImpR` give `SlotImp`), the indexed rows **`repIRowsW`** (slot 0's
  in the spare region from row `κ.vslots·2^20`, a segment slot's at `v·2^20 + repBase`, S-E14's place),
  **`repHoldsW_of`** and **`gap4Imp_of_repW`**.
* **`repOkW_rtC1`**: `RepOkW rtC1 impl₀ base` (`FRNodeRows4RepN`'s templates).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-! ## At the node's slots -/

/-- **The replay rows' assignment** at slot `v`. -/
def repAsg (κ : Rev4.NodeKind) (v : ℕ) (w : Asg) : Asg := w ∘ repMapC κ v

theorem agree_repAsg (κ : Rev4.NodeKind) (v : ℕ) (w : Asg) : Agree repB (slotAsg κ v w) (repAsg κ v w) :=
  fun c hc => by simp only [repAsg, Function.comp_apply, repMapC, hc, ite_true, slotAsg]

/-- **The replay rows hold** at slot `v` (at `repAsg`; REPF: S-E14's `RepHolds`, now this form). -/
def RepHoldsW (rt : ℕ → RT) (κ : Rev4.NodeKind) (v : ℕ) (w : Asg) : Prop :=
  ∀ r ∈ repRowsP (rt (protoOf κ v)) (protoOf κ v), r.Holds (repAsg κ v w)

/-- **The templates are sound** for every prototype and index (`RTOkW` at `repB`; REPF: S-E14's
`RepOk`, now this form). -/
def RepOkW (rt : ℕ → RT) (impl₀ : OpImpl) (base : Rev4.NodeKind → OpImpl) : Prop :=
  ∀ π ≤ 1, ∀ ι, RTOkW (implP impl₀ base π ι) (Xof π) (rt π) ι repB

/-- The prototypes' selector forms are frame cells (below `repB`). -/
theorem selOk_repAsg {κ : Rev4.NodeKind} {v : ℕ} {w : Asg} {ι : Kind}
    (h : SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι) : SelOk (repAsg κ v w) (protoP (protoOf κ v)) ι := by
  have hA := agree_repAsg κ v w
  have hπ := protoOf_le' κ v
  have hlt : ∀ c ∈ ((protoP (protoOf κ v)).one :: Circ.kinds.map (protoP (protoOf κ v)).sel),
      linLt repB c = true := by
    intro c hc
    rcases (by omega : protoOf κ v = 0 ∨ protoOf κ v = 1) with h0 | h0 <;> rw [h0] at hc <;>
      revert c <;> decide
  refine ⟨by rw [ev_agree hA (hlt _ (List.mem_cons_self ..))]; exact h.1, fun κ' => ?_⟩
  rw [ev_agree hA (hlt _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨κ', by cases κ' <;> simp [Circ.kinds], rfl⟩)))]
  exact h.2 κ'

/-- **The discharge at a slot** (replay rows at `repAsg`): the slot's rows, the replay rows and
`SlotImpR` give `SlotImp`. -/
theorem slotImp_of_repW {rt : ℕ → RT} {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (hok : RepOkW rt impl₀ base) {κ : Rev4.NodeKind} {v : ℕ} {w : Asg}
    {inp : Input} {tr : Trace} (hrows : SlotRows κ v w) (hrep : RepHoldsW rt κ v w)
    (h : SlotImpR rt impl₀ base κ v w inp tr) : SlotImp impl₀ base κ v w inp tr := by
  intro ι hS
  obtain ⟨⟨s, he, hx, hi, hf⟩, hst⟩ := h ι hS
  have hπ := protoOf_le' κ v
  have hX := tplExt4A_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base hπ ι)
    (protoLay (protoOf κ v)) (colA (protoOf κ v))
  have key := compileX_soundRW hX (hok _ hπ ι) (baseR (protoOf κ v)) hS (selOk_repAsg hS)
    (agree_repAsg κ v w) he hrows.1 hrows.2 hx hi hrep hf
  exact ⟨⟨s, he, hx, fun i _ => key.2 i, hf⟩, hst⟩

/-- **`RepOkW` for `rtC1`.** -/
theorem repOkW_rtC1 {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base) :
    RepOkW rtC1 impl₀ base := fun _ hπ ι => rtC1_ok hZ hB hπ ι

/-! ## The node's indexed replay rows -/

/-- **The node's rows give the replay rows** once they are folded in (`hfold`). -/
theorem repHoldsW_of {rt : ℕ → RT} {κ : Rev4.NodeKind} {v : ℕ} {w : Asg}
    (hfold : ∀ p ∈ repIRowsW rt κ v, p ∈ nodeIRows4 κ) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    RepHoldsW rt κ v w := by
  unfold RepHoldsW
  unfold repIRowsW at hfold
  generalize repRowsP (rt (protoOf κ v)) (protoOf κ v) = l at hfold ⊢
  intro r hr
  obtain ⟨k, hm⟩ := mem_zipIdx_map hr fun p : Row × ℕ => (repRowI κ v p.2, rowMapC (repMapC κ v) p.1)
  have h3 := hE _ (hfold _ hm)
  dsimp only at h3
  rw [holds_rowMapC] at h3
  exact h3

/-- **`Gap4.imp` from the replay rows** (at `repAsg`): with the fold, `StmtN4`'s rows and `SlotImpR`
at every active slot give `SlotImp` there. -/
theorem gap4Imp_of_repW {rt : ℕ → RT} {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (hok : RepOkW rt impl₀ base) (pf : Trace → Proof) {κ : Rev4.NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg}
    (hfold : ∀ v < κ.vslots, ∀ p ∈ repIRowsW rt κ v, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImpR rt impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) := by
  intro v hv
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hlt := active_lt pf hv
  exact slotImp_of_repW hT₀ hT hok (slotRows_of (one_of_pubCells hP) hlt hE)
    (repHoldsW_of (hfold v hlt) hE) (h v hv)

/-! ## S-E14's names in the `RTOkW` form (REPF)

`RepOk`, `RepHolds` and `repIRows4` (`FRNodeRows4Rep`) are now `RepOkW`, `RepHoldsW` and `repIRowsW`
by definition, so B3's run (`FRNodeRun4S`) and every theorem stated over them take the replay rows at
the spare region's assignment. S-E14's three theorems, at the same statements: -/

theorem repOk_iff {rt : ℕ → RT} {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} :
    RepOk rt impl₀ base ↔ RepOkW rt impl₀ base := Iff.rfl

theorem repIRows4_eq (rt : ℕ → RT) (κ : Rev4.NodeKind) (v : ℕ) : repIRows4 rt κ v = repIRowsW rt κ v := rfl

/-- **The discharge at a slot** (S-E14's statement): its rows, its replay rows and `SlotImpR` give `SlotImp`. -/
theorem slotImp_of_rep {rt : ℕ → RT} {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : Rev4.NodeKind} {v : ℕ} {w : Asg}
    {inp : Input} {tr : Trace} (hrows : SlotRows κ v w) (hrep : RepHolds rt κ v w)
    (h : SlotImpR rt impl₀ base κ v w inp tr) : SlotImp impl₀ base κ v w inp tr :=
  slotImp_of_repW hT₀ hT hok hrows hrep h

/-- **The node's rows give the replay rows** once they are folded in (`hfold`; S-E14's statement). -/
theorem repHolds_of {rt : ℕ → RT} {κ : Rev4.NodeKind} {v : ℕ} {w : Asg}
    (hfold : ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    RepHolds rt κ v w :=
  repHoldsW_of hfold hE

/-- **`Gap4.imp` from the replay rows** (S-E14's statement). -/
theorem gap4Imp_of_rep {rt : ℕ → RT} {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hT₀ : ImplT impl₀)
    (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) (pf : Trace → Proof) {κ : Rev4.NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg}
    (hfold : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImpR rt impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) :=
  gap4Imp_of_repW hT₀ hT hok pf hfold hS h

end N4s
end FR

end G6_FRNodeRows4RepW

section G6_FRNodeRows4RepRsK

-- New for `flock-recursive` (R-OPS §5.2, stage R3: `rsWeight`'s replay at the previous-node slot).

/-!
# `rsWeight`'s kind-muxed replay (prototype 0)

* **`rsT ν ts`**: the node kind `ν`'s sub-template at the operand types
  `ts = [af 7, f, f, ak m] ++ ns.map ak` (`r″`, `κ`, `β`, `ρ`, then the claims), `Tpl.rsG` over the
  inputs' forms; two empty outputs at any other types (which `rsIn` rejects).
* **`kRS`**: the `KOp` (C1's mechanism, `FRNodeRows4RepK`): covers an `rsWeight` op whose `act` holds
  at every index; operands `[r, κ, β, ρ] ++ pts ι`.
* **`kRS_ok`**: `KOk (implP impl₀ base 0 ι) ι kRS` at every index: the sub-template of `nodeAt ι`
  computes `rsWeightF4 (nodeAt ι)` (`Tpl.ok_rsGS`, `RsR.rsWeightF4_ref`).
* **`rtRs`** (`rtRs_okW`): the replay template, its locals from `cbRS = repB + 2^16` (after
  `linkWAll`'s 42,601).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## Operand shapes and input forms -/

theorem akS_eq : ∀ {r : List Ty} {ns : List ℕ}, akS r = some ns → r = ns.map .ak
  | [], ns, h => by simp only [akS, Option.some.injEq] at h; subst h; rfl
  | .ak n :: r, ns, h => by
    simp only [akS, Option.map_eq_some_iff] at h
    obtain ⟨ns', h', rfl⟩ := h
    rw [akS_eq h']; rfl
  | .f :: _, _, h | .k :: _, _, h | .bit :: _, _, h | .d :: _, _, h | .af _ :: _, _, h => by simp [akS] at h

theorem rsShape_eq {ts : List Ty} {m : ℕ} {ns : List ℕ} (h : rsShape ts = some (m, ns)) :
    ts = .af 7 :: .f :: .f :: .ak m :: ns.map .ak := by
  unfold rsShape at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨ns', h', rfl, rfl⟩ := h
    rw [akS_eq h']
  · simp at h

theorem rsT_outs (ν : NodeKind) (ts : List Ty) : (rsT ν ts).outs.length = 2 := by
  unfold rsT; split <;> rfl

/-! ## Input values -/

variable {e : Env}

theorem getD_mid (pre m post : List F) {i : ℕ} (hi : i < m.length) :
    (pre ++ m ++ post).getD (pre.length + i) 0 = m.getD i 0 := by
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

theorem kIn_ev {xs pre post : List F} {x : List K} (h : InpIs e xs) (hx : xs = pre ++ x.flatMap encK ++ post) :
    (kIn pre.length x.length).map (evK e) = x := by
  refine List.ext_getElem (by simp [kIn]) fun l h1 h2 => ?_
  simp only [kIn, List.length_map, List.length_range] at h1
  have hl : 2 * l + 1 < (x.flatMap encK).length := by rw [length_flatMap_encK]; omega
  have e0 := encK_getD x l
  simp only [kIn, List.getElem_map, List.getElem_range, evK, ev_I]
  rw [h, h, hx, Nat.add_assoc, getD_mid _ _ _ (by omega), getD_mid _ _ _ hl, e0.1, e0.2,
    List.getD_eq_getElem _ _ h2]

theorem cIn_ev {xs : List F} (h : InpIs e xs) : ∀ (pss : List (List K)) (pre post : List F),
    xs = pre ++ (pss.map (·.flatMap encK)).flatten ++ post →
    (cIn pre.length (pss.map List.length)).map (List.map (evK e)) = pss
  | [], _, _, _ => rfl
  | x :: pss, pre, post, hx => by
    simp only [List.map_cons, cIn, List.cons.injEq]
    refine ⟨kIn_ev h (pre := pre) (post := (pss.map (·.flatMap encK)).flatten ++ post) (by
      rw [hx]; simp), ?_⟩
    have := cIn_ev h pss (pre ++ x.flatMap encK) post (by rw [hx]; simp)
    rwa [List.length_append, length_flatMap_encK] at this

theorem fIn_ev {xs pre post : List F} {x : List F} (h : InpIs e xs) (hx : xs = pre ++ x ++ post) :
    ((List.range x.length).map fun l => I (pre.length + l)).map (LinT.ev e) = x := by
  refine List.ext_getElem (by simp) fun l h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, ev_I]
  rw [h, hx, getD_mid _ _ _ h1, List.getD_eq_getElem _ _ h1]

/-! ## The `KOp` -/

theorem implP0_rsWeight {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    (implP impl₀ base 0 ι).rsWeight = Impl.rsWeightF4 (nodeAt ι) := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4]
  rfl

theorem val_af {v : Val} {n : ℕ} (h : tyOf v = some (.af n)) : ∃ x : Array F, v = .af x ∧ x.size = n := by
  cases v <;> simp [tyOf] at h; exact ⟨_, rfl, h⟩

theorem val_ak {v : Val} {n : ℕ} (h : tyOf v = some (.ak n)) : ∃ x : Array K, v = .ak x ∧ x.size = n := by
  cases v <;> simp [tyOf] at h; exact ⟨_, rfl, h⟩

theorem val_f {v : Val} (h : tyOf v = some .f) : ∃ x : F, v = .f x := by
  cases v <;> simp [tyOf] at h; exact ⟨_, rfl⟩

/-- The claims' registers are `AK`s of the given sizes. -/
theorem claims_ak {regs : Array Val} : ∀ {as : List ℕ} {ns : List ℕ},
    as.map (fun a => tyOf (rd regs a)) = (ns.map Ty.ak).map some →
    as.flatMap (fun a => encV (rd regs a)) = ((as.map fun a => (rd regs a).toAK.toList).map (·.flatMap encK)).flatten ∧
      (as.map fun a => (rd regs a).toAK.toList).map List.length = ns
  | [], [], _ => ⟨rfl, rfl⟩
  | a :: as, n :: ns, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨x, hx, hs⟩ := val_ak h.1
    obtain ⟨ih1, ih2⟩ := claims_ak h.2
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons, ih1, List.map_cons, List.map_cons, List.flatten_cons, hx]; rfl
    · rw [List.map_cons, List.map_cons, ih2, hx]; simp [Val.toAK, hs]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **`rsWeight`'s replay obligation holds at every index.** -/
theorem kRS_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kRS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i r ps κ' β act ρ
  have hact : act ι = true := by
    simp only [kRS, isRS, Bool.and_eq_true] at hc
    cases ι <;> simp [hc]
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => rsT_outs ν ts,
    fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq, hact, ite_true] at hev
  obtain ⟨rfl, -⟩ := hev
  refine ⟨rfl, fun e h1 hi hE => ?_⟩
  obtain ⟨⟨m, ns⟩, hsh⟩ := Option.isSome_iff_exists.1 hin
  have hts := rsShape_eq hsh
  simp only [kRS, rsArgs, hts, List.map_cons, List.map_append, List.cons_append, List.cons.injEq,
    List.map_map] at hty
  obtain ⟨hr, hκ, hβ, hρ, hps⟩ := hty
  obtain ⟨ra, hra, hrs⟩ := val_af hr
  obtain ⟨κv, hκv⟩ := val_f hκ
  obtain ⟨βv, hβv⟩ := val_f hβ
  obtain ⟨ρa, hρa, hρs⟩ := val_ak hρ
  obtain ⟨hpe, hpl⟩ := claims_ak (regs := regs) (as := ps ι) (ns := ns)
    (by simpa [List.map_map] using hps)
  have hx : (kRS.args (.rsWeight r ps κ' β act ρ) ι).flatMap (fun a => encV (rd regs a)) =
      ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
        (((ps ι).map fun a => (rd regs a).toAK.toList).map (·.flatMap encK)).flatten := by
    show encV (rd regs r) ++ (encV (rd regs κ') ++ (encV (rd regs β) ++ (encV (rd regs ρ) ++
      (ps ι).flatMap fun a => encV (rd regs a)))) = _
    rw [hra, hκv, hβv, hρa, hpe]
    simp [encV]
  rw [hx] at hi
  simp only [kRS, rsT, hsh] at hE ⊢
  set cl := (((ps ι).map fun a => (rd regs a).toAK.toList).map (·.flatMap encK)).flatten with hcl
  have hO := ok_rsGS (e := e) h1 (nodeAt ι)
    (r := ra.toList) (ps := (ps ι).map fun a => (rd regs a).toAK.toList) (κ := κv) (β := βv)
    (ρ := ρa.toList)
    (by
      have := fIn_ev (pre := []) (post := [κv, βv] ++ ρa.toList.flatMap encK ++ cl) hi (x := ra.toList)
        (by simp only [List.nil_append, List.append_assoc])
      simpa only [List.length_nil, zero_add, Array.length_toList, hrs] using this)
    (by
      have := cIn_ev hi _ (ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK) [] (by rw [List.append_nil])
      simp only [hpl, List.length_append, List.length_cons, List.length_nil, Array.length_toList, hrs,
        length_flatMap_encK, hρs] at this
      rwa [show 7 + (0 + 1 + 1) + 2 * m = 9 + 2 * m by ring] at this)
    (by
      rw [ev_I, hi, List.append_assoc (ra.toList ++ [κv, βv]),
        show 7 = ra.toList.length + 0 by simp [hrs], getD_mid _ _ _ (by simp)]; rfl)
    (by
      rw [ev_I, hi, List.append_assoc (ra.toList ++ [κv, βv]),
        show 8 = ra.toList.length + 1 by simp [hrs], getD_mid _ _ _ (by simp)]; rfl)
    (by
      have := kIn_ev hi (pre := ra.toList ++ [κv, βv]) (x := ρa.toList) (post := cl) rfl
      simpa only [List.length_append, List.length_cons, List.length_nil, Array.length_toList, hrs, hρs]
        using this)
    0 hE
  rw [implP0_rsWeight, show (rd regs r).toAF = ra by rw [hra]; rfl, hκv, hβv, hρa,
    show (Val.f κv).toF = κv from rfl, show (Val.f βv).toF = βv from rfl,
    show (Val.ak ρa).toAK = ρa from rfl, RsR.rsWeightF4_ref _ _ _ _ _ _ hrs, List.map_map]
  simp only [encV, encK, List.flatMap_cons, List.flatMap_nil, List.append_nil, Function.comp_def]
  rw [← hO]
  rfl

/-! ## The replay templates -/

theorem rtRs_okW {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    RTOkW (implP impl₀ base 0 ι) (Xof 0) rtRs ι repB :=
  rtK_okW repB cbRS (kRS_ok ι)

/-- **The replay templates per prototype** (`rtC1` with `rsWeight` at prototype 0). -/
def rtR3 (π : ℕ) : RT := if π = 0 then rtN0R else if π = 1 then rtLinkSegW repB else RT.none

/-- **Every template of `rtR3` is sound** (`rtC1_ok`'s hypotheses). -/
theorem rtR3_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtR3 π) ι repB := by
  by_cases h : π = 0
  · subst h
    simp only [rtR3, ite_true, rtN0R]
    exact RT.orElse_okW (by simpa [rtC1] using rtC1_ok hZ hB (le_refl _ |>.trans (Nat.zero_le 1)) ι) (rtRs_okW ι)
  · obtain rfl : π = 1 := by omega
    simp only [rtR3, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

end N4s
end FR

end G6_FRNodeRows4RepRsK

section G6_FRVIRTplRepL

-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).

/-!
# The replay template of a node's `evalL`: correctness

**`tplEvL_ok`**: with `e.one = 1`, the inputs `rL ++ r4` and the gate equations, the outputs of
`tplEvL ν rL.size r4.size` (`FRVIRTplRepLD`) are `evalL4I ν rL r4`'s three values (CF2: by the carry
automata's `GS` values, `ok_autoG`, `GS_eq`).
-/

namespace FR
namespace Tpl
open Circ Finset NI4 NI4F Impl

variable {e : Env}

/-- An `eq` table over `n` coordinates `g 0 … g (n−1)` at an index below `2^n`. -/
theorem eqTable_getD_map (n : ℕ) (g : ℕ → F) {x : ℕ} (hx : x < 2 ^ n) :
    (eqTable ((List.range n).map g)).getD x 0 = eqAtR (fun l : Fin n => g l) x := by
  rw [eqTable_getD _ (by simpa using hx)]
  unfold eqAtR ptOf
  rw [Fin.prod_univ_eq_prod_range
      (fun l => if x.testBit l then ((List.range n).map g).getD l 0 else 1 - ((List.range n).map g).getD l 0),
    Fin.prod_univ_eq_prod_range (fun l => if x.testBit l then g l else 1 - g l)]
  simp only [List.length_map, List.length_range]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range]

theorem nJL_eq : nJL = nJ := rfl

/-- `evalL4I`'s three values as sums over the slots and their bits. -/
theorem evalL4I_sums (ν : Rev4.NodeKind) (rL r4 : Array F) :
    evalL4I ν rL r4 =
      (∑ σ ∈ range ν.vslots, eqAtR (hiK 14 (ν.m - 7) r4) (ν.lBase * 128 / 2 ^ 14 + σ) *
          ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
            (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0,
       (∑ σ ∈ range ν.vslots, ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j)) *
          eqAtR (ptA (ν.m - 7) r4) ν.oneCell -
        ∑ σ ∈ range ν.vslots, eqAtR (hiK 14 (ν.m - 7) r4) (ν.lBase * 128 / 2 ^ 14 + σ) *
          ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
            (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0,
       0) := by
  simp only [evalL4I, slotL, sumTo_eq, Prod.fst_sum, Prod.snd_sum]

/-! ## The bit factors' values -/

/-- The bit factors of a block's values `v` (`n` coordinates, padded). -/
def fE (v : ℕ → F) (n l : ℕ) (bit : Bool) : F := if l < n then (if bit then v l else 1 - v l) else (if bit then 0 else 1)

def fO (_ : ℕ) (_ : Bool) : F := 1

theorem qE_ev (h1 : e.one = 1) {c : ℕ → LinT} {v : ℕ → F} (hc : ∀ l, (c l).ev e = v l) (n l : ℕ) (bit : Bool) :
    (qE c n l bit).ev e = fE v n l bit := by
  unfold qE fE
  split_ifs <;> simp [ev_append, ev_sc, ev_C, h1, hc] <;> ring

theorem qO_ev (h1 : e.one = 1) (l : ℕ) (bit : Bool) : (qO l bit).ev e = fO l bit := by
  simp [qO, fO, ev_C, h1]

theorem PF_fO (L x : ℕ) : PF fO L x = if x < 2 ^ L then 1 else 0 := by
  unfold PF fO; simp

/-- **Padded factors are `gN`** of the block. -/
theorem PF_fE (v : ℕ → F) {n L : ℕ} (h : n ≤ L) (x : ℕ) : PF (fE v n) L x = TEval.gN n v x := by
  obtain ⟨d, rfl⟩ : ∃ d, L = n + d := ⟨L - n, by omega⟩
  unfold PF TEval.gN TEval.eqN
  by_cases hx : x < 2 ^ n
  · have hx' : x < 2 ^ (n + d) := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [if_pos hx', if_pos hx, prod_range_add]
    have h2 : ∏ l ∈ range d, fE v n (n + l) (x.testBit (n + l)) = 1 := prod_eq_one fun l _ => by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp [fE]
    rw [h2, mul_one]
    exact prod_congr rfl fun l hl => by simp [fE, mem_range.1 hl]
  · rw [if_neg hx]
    split_ifs with hx'
    · have hne : x / 2 ^ n ≠ 0 := by
        rw [Ne, Nat.div_eq_zero_iff_lt (by positivity)]; exact hx
      obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
      have hlt : x / 2 ^ n < 2 ^ d := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hx'
      have hid : i < d := by
        by_contra hc
        exact absurd hi (by rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]; simp)
      rw [prod_range_add]
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_range.2 hid) ?_)
      rw [show n + i = i + n by ring, ← Nat.testBit_div_two_pow, hi]
      simp [fE]
    · rfl

theorem eqAtR_gN {n : ℕ} (g : ℕ → F) {x : ℕ} (hx : x < 2 ^ n) : eqAtR (fun l : Fin n => g l) x = TEval.gN n g x := by
  unfold eqAtR TEval.gN TEval.eqN
  rw [if_pos hx, Fin.prod_univ_eq_prod_range (fun l => if x.testBit l then g l else 1 - g l)]

theorem lsumR (n : ℕ) (f : ℕ → F) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem flatten_ev (l : List LinT) : LinT.ev e l.flatten = (l.map (LinT.ev e)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatten_cons, ev_append, ih]; simp

theorem getD_ev {α : Type} {l : List LinT} {m : List α} {g : α → F} (h : l.map (LinT.ev e) = m.map g) {i : ℕ}
    (hi : i < m.length) : (l.getD i []).ev e = g m[i] := by
  have hl : l.length = m.length := by simpa using congrArg List.length h
  have := congrArg (fun x => x.getD i 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (hl ▸ hi),
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hi), Option.getD_some]
  exact this

section Proof
variable {ν : Rev4.NodeKind} {rL r4 : Array F} (hi : InpIs e (rL.toList ++ r4.toList))
include hi

set_option maxHeartbeats 1000000 in
/-- **The node kind `ν`'s `evalL` template computes `evalL4I ν`.** -/
theorem tplEvL_ok (h1 : e.one = 1) (h : Eqns e (tplEvL ν rL.size r4.size).gates 0) :
    (tplEvL ν rL.size r4.size).outs.map (LinT.ev e) =
      [(evalL4I ν rL r4).1, (evalL4I ν rL r4).2.1, (evalL4I ν rL r4).2.2] := by
  obtain ⟨hfit, hlo, h3, hVJ, h9, hhi⟩ := lCells_fit ν
  have hNJ : nJL = nJ := rfl
  have hnJ : nJ = 8220 := rfl
  have hq1 := qE_ev h1 (cT_ev hi) ν.dims.logL
  have hq2 := qE_ev h1 (cR_ev hi) 14
  have hq3 := qE_ev h1 (c := fun l => cR rL.size r4.size (14 + l)) (v := fun l => r4.getD (14 + l) 0)
    (fun l => cR_ev hi (14 + l)) (ν.m - 7 - 14)
  have hL14 : 14 ≤ ν.dims.logL := by
    have : nJ ≤ 2 ^ ν.dims.logL := le_trans (Nat.le_mul_of_pos_left _ (by cases ν <;> decide)) hVJ
    by_contra hc
    have : 2 ^ ν.dims.logL ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hnJ] at *; omega
  have hpow : 2 ^ (ν.m - 7) = 2 ^ (ν.m - 7 - 14) * 2 ^ 14 := by rw [← pow_add, Nat.sub_add_cancel hhi]
  -- the four automata's values
  have hok : GM.Ok e (evGM ν rL.size r4.size) fun outs => outs.map (LinT.ev e) =
      [(evalL4I ν rL r4).1, (evalL4I ν rL r4).2.1, (evalL4I ν rL r4).2.2] := by
    unfold evGM
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq1 hq2) fun S hS => ?_
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq1 (qO_ev h1)) fun E hE => ?_
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq2 (qO_ev h1)) fun O1 hO1 => ?_
    refine GM.ok_bind (ok_autoG h1 _ _ _ _ _ _ hq3 (qO_ev h1)) fun H hH => ?_
    refine GM.ok_bind (GM.ok_mapL (E := LinT.ev e) (v := fun σ => (H.getD σ []).ev e * (S.getD σ []).ev e) _
      fun σ _ => ok_mulF _ _) fun Q hQ => ?_
    refine GM.ok_bind (ok_mulF _ _) fun O hO => GM.ok_map (ok_mulF _ _) fun EO hEO => ?_
    -- slot values
    have hSg : ∀ σ < ν.vslots, GS (fE (fun l => rL.getD l 0) ν.dims.logL) (fE (fun l => r4.getD l 0) 14) ν.dims.logL
        nJL (σ * nJL) 299 = ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
          (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := fun σ hσ => by
      rw [GS_eq, hNJ]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      have hx : σ * nJ + j < 2 ^ ν.dims.logL := lt_of_lt_of_le (by nlinarith) hVJ
      have hy : 299 + j < 2 ^ 14 := by rw [hnJ] at hj'; norm_num; omega
      have e1 : TEval.gN ν.dims.logL (fun l => rL.getD l 0) (σ * nJ + j) = (bt ν.dims.logL rL).eq (σ * nJ + j) := by
        rw [bt_eq h9 _ hx, ← eqAtR_gN (fun l => rL.getD l 0) hx]; rfl
      have e2 : TEval.gN 14 (fun l => r4.getD l 0) (299 + j) = (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := by
        rw [ofFn_eq_range (ptA 14 r4) (fun l => r4.getD l 0) fun l => rfl, eqTable_getD_map 14 _ hy,
          eqAtR_gN (fun l => r4.getD l 0) hy]
      rw [PF_fE _ le_rfl, PF_fE _ hL14, e1, e2]
    have hEg : ∀ σ < ν.vslots, GS (fE (fun l => rL.getD l 0) ν.dims.logL) fO ν.dims.logL nJL (σ * nJL) 0 =
        ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) := fun σ hσ => by
      rw [GS_eq, hNJ]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      have hx : σ * nJ + j < 2 ^ ν.dims.logL := lt_of_lt_of_le (by nlinarith) hVJ
      have hy : 0 + j < 2 ^ ν.dims.logL := lt_of_lt_of_le (by nlinarith) hVJ
      have e1 : TEval.gN ν.dims.logL (fun l => rL.getD l 0) (σ * nJ + j) = (bt ν.dims.logL rL).eq (σ * nJ + j) := by
        rw [bt_eq h9 _ hx, ← eqAtR_gN (fun l => rL.getD l 0) hx]; rfl
      rw [PF_fE _ le_rfl, PF_fO, if_pos hy, mul_one, e1]
    have hSv : ∀ σ < ν.vslots, (S.getD σ []).ev e = ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) *
        (eqTable (List.ofFn (ptA 14 r4))).getD (299 + j) 0 := fun σ hσ => by
      rw [getD_ev hS (by simpa using hσ)]
      simp only [List.getElem_map, List.getElem_range]
      exact hSg σ hσ
    have hb : ∀ σ < ν.vslots, evHb ν + σ < 2 ^ (ν.m - 7 - 14) := fun σ hσ => by
      have h2 := hpow ▸ hlo
      unfold evHb
      generalize 2 ^ (ν.m - 7 - 14) = X at h2 ⊢
      rw [show (2 : ℕ) ^ 14 = 16384 from rfl] at h3 hfit h2 ⊢
      omega
    have hq : ν.oneCell / 2 ^ 14 < 2 ^ (ν.m - 7 - 14) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← hpow]; exact hlo
    have hHv : ∀ σ < ν.vslots, (H.getD σ []).ev e = eqAtR (hiK 14 (ν.m - 7) r4) (evHb ν + σ) := fun σ hσ => by
      rw [getD_ev hH (by simpa using Nat.lt_succ_of_lt hσ)]
      rw [List.getElem_append_left (by simpa using hσ)]
      simp only [List.getElem_map, List.getElem_range, GS_eq, sum_range_one, add_zero, PF_fE _ le_rfl, PF_fO]
      rw [if_pos (by positivity), mul_one, ← eqAtR_gN (fun l => r4.getD (14 + l) 0) (hb σ hσ)]; rfl
    have hHo : (H.getD ν.vslots []).ev e = eqAtR (hiK 14 (ν.m - 7) r4) (ν.oneCell / 2 ^ 14) := by
      rw [getD_ev hH (by simp)]
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_cons_zero, GS_eq, sum_range_one,
        add_zero, PF_fE _ le_rfl, PF_fO]
      rw [if_pos (by positivity), mul_one, ← eqAtR_gN (fun l => r4.getD (14 + l) 0) hq]; rfl
    have hO1v : (O1.getD 0 []).ev e = eqAtR (ptA 14 r4) (ν.oneCell % 2 ^ 14) := by
      rw [getD_ev hO1 (by simp)]
      simp only [List.getElem_cons_zero, GS_eq, sum_range_one, add_zero, PF_fE _ le_rfl, PF_fO]
      rw [if_pos (by positivity), mul_one, ← eqAtR_gN (fun l => r4.getD l 0) (Nat.mod_lt _ (by positivity))]; rfl
    have hQs : LinT.ev e Q.flatten = (evalL4I ν rL r4).1 := by
      rw [flatten_ev, hQ, evalL4I_sums, lsumR]
      exact sum_congr rfl fun σ hσ => by rw [hHv σ (mem_range.1 hσ), hSv σ (mem_range.1 hσ), evHb]
    have hEs : LinT.ev e E.flatten = ∑ σ ∈ range ν.vslots, ∑ j ∈ range nJ, (bt ν.dims.logL rL).eq (σ * nJ + j) := by
      rw [flatten_ev, hE, List.map_map, lsumR]
      exact sum_congr rfl fun σ hσ => hEg σ (mem_range.1 hσ)
    have hOv : O.ev e = eqAtR (ptA (ν.m - 7) r4) ν.oneCell := by
      rw [hO, hO1v, hHo, eqAtR_splitK hhi]
    simp only [List.map_cons, List.map_nil, ev_append, ev_sc, ev_nil, hEO, hEs, hOv, hQs]
    rw [evalL4I_sums]
    simp only [List.cons.injEq, and_true, true_and]
    ring
  have hg : (tplEvL ν rL.size r4.size).gates = (evGM ν rL.size r4.size 0).1 := rfl
  have ho : (tplEvL ν rL.size r4.size).outs = (evGM ν rL.size r4.size 0).2 := by simp only [tplEvL]
  rw [hg] at h
  rw [ho]
  exact hok 0 h

end Proof

end Tpl
end FR

end G6_FRVIRTplRepL

section G6_FRNodeRows4RepLT

-- New for `flock-recursive` (PACK-4.4 §6.2, R1's route (a); track C1b).

/-!
# The previous node's `targetS` and `evalL` replays (prototype 0)

* **`kTS`**: `targetS`'s kind-muxed replay (sub-template `Tpl.tplTS ν a` on the operand `[af a]`);
  **`kTS_ok`**: `KOk` at every index (`Tpl.tplTS_ok`; the value is `targetSNode4I (nodeAt ι)`).
* **`kEvL`**: `evalL`'s kind-muxed replay (sub-template `Tpl.tplEvL ν a b` on `[af a, af b]`);
  **`kEvL_ok`** (`Tpl.tplEvL_ok`; the value is `evalL4I (nodeAt ι)`).
* **`rtN0b`**: C1's `rtN0` (`shiftTarget`, `linkWAll`) and these two, each template's locals in its
  own block of the replay frame (`cbTS`, `cbEvL`); **`rtC1b π`**: `rtN0b` at prototype 0, S-E14's
  segment `linkWAll` at prototype 1; **`rtC1b_ok`**, **`repOkW_rtC1b`**.

Both `KOp`s are keyed by the op's constructor and read the operand registers from the op itself
(no register number of a particular program).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## `targetS` -/

theorem implP0_targetS {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) (rr : Array F) :
    (implP impl₀ base 0 ι).targetS ι rr = NI4T.targetSNode4I (nodeAt ι) rr := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F, NI4T.implN4T, NI4.implN4]
  rfl

theorem kTS_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kTS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => ?_, fun inp regs vs ok ts hev hin hty => ?_⟩
  · simp only [kTS, tsTpl]
    split
    · rw [tplTS_outs]; rfl
    · simp [Ty.len]
  · simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [implP0_targetS]
    simp only [kTS, tsArgs] at hty ⊢
    refine ⟨by simp [tyOf, NI4T.targetSNode4I], fun e h1 hi hE => ?_⟩
    match ts, hin, hty with
    | [.af a], _, hty =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hty
      obtain ⟨h1t, -⟩ := hty
      obtain ⟨rr, hrr⟩ : ∃ rr, rd regs t = .af rr := by
        rcases hv : rd regs t <;> simp [hv, tyOf] at h1t; exact ⟨_, rfl⟩
      rw [hrr, tyOf] at h1t
      simp only [Option.some.injEq, Ty.af.injEq] at h1t
      subst h1t
      simp only [tsTpl] at hE ⊢
      simp only [hrr, Val.toAF, List.flatMap_cons, List.flatMap_nil, List.append_nil, encV] at hi ⊢
      exact tplTS_ok (by simpa using hi) h1 hE

/-! ## `evalL` -/

theorem implP0_evalL {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) (rL r4 : Array F) :
    (implP impl₀ base 0 ι).evalL rL r4 = NI4F.evalL4I (nodeAt ι) rL r4 := by
  simp only [implP, ite_true, OpImpl.fixK, NI4F.implN4F]

theorem kEvL_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (ι : Kind) :
    KOk (implP impl₀ base 0 ι) ι kEvL := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t s
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun ν ts => ?_, fun inp regs vs ok ts hev hin hty => ?_⟩
  · simp only [kEvL, evTpl]
    split
    · rw [tplEvL_outs]; rfl
    · simp [Ty.len]
  · simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [implP0_evalL]
    simp only [kEvL, evArgs] at hty ⊢
    refine ⟨by simp [tyOf], fun e h1 hi hE => ?_⟩
    match ts, hin, hty with
    | [.af a, .af b], _, hty =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hty
      obtain ⟨h1t, h1s, -⟩ := hty
      obtain ⟨rL, hrL⟩ : ∃ rL, rd regs t = .af rL := by
        rcases hv : rd regs t <;> simp [hv, tyOf] at h1t; exact ⟨_, rfl⟩
      obtain ⟨r4, hr4⟩ : ∃ r4, rd regs s = .af r4 := by
        rcases hv : rd regs s <;> simp [hv, tyOf] at h1s; exact ⟨_, rfl⟩
      rw [hrL, tyOf] at h1t; rw [hr4, tyOf] at h1s
      simp only [Option.some.injEq, Ty.af.injEq] at h1t h1s
      subst h1t h1s
      simp only [evTpl] at hE ⊢
      simp only [hrL, hr4, Val.toAF, List.flatMap_cons, List.flatMap_nil, List.append_nil, encV] at hi ⊢
      rw [tplEvL_ok hi h1 hE]
      simp

/-! ## Prototype 0's templates, and both prototypes' -/

/-- **Prototype 0's replay templates**: `shiftTarget`, `linkWAll` (C1), `targetS`, `evalL`. -/
def rtN0b : RT := rtN0.orElse ((rtK kTS repB cbTS).orElse (rtK kEvL repB cbEvL))

/-- **The replay templates per prototype.** -/
def rtC1b (π : ℕ) : RT := if π = 0 then rtN0b else if π = 1 then rtLinkSegW repB else RT.none

theorem rtC1b_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtC1b π) ι repB := by
  by_cases h : π = 0
  · subst h
    have h0 := rtC1_ok hZ hB (π := 0) (by norm_num) ι
    simp only [rtC1, ite_true] at h0
    simp only [rtC1b, ite_true, rtN0b]
    exact RT.orElse_okW h0 (RT.orElse_okW (rtK_okW repB cbTS (kTS_ok ι)) (rtK_okW repB cbEvL (kEvL_ok ι)))
  · obtain rfl : π = 1 := by omega
    simp only [rtC1b, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

/-- **`RepOkW` for `rtC1b`.** -/
theorem repOkW_rtC1b {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base) :
    RepOkW rtC1b impl₀ base := fun _ hπ ι => rtC1b_ok hZ hB hπ ι

theorem rtC1c_ok {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    {π : ℕ} (hπ : π ≤ 1) (ι : Kind) : RTOkW (implP impl₀ base π ι) (Xof π) (rtC1c π) ι repB := by
  by_cases h : π = 0
  · subst h
    have h0 := rtR3_ok hZ hB (π := 0) (by norm_num) ι
    simp only [rtR3, ite_true] at h0
    simp only [rtC1c, ite_true, rtN0c]
    exact RT.orElse_okW h0 (RT.orElse_okW (rtK_okW repB cbTS (kTS_ok ι)) (rtK_okW repB cbEvL (kEvL_ok ι)))
  · obtain rfl : π = 1 := by omega
    simp only [rtC1c, one_ne_zero, ite_false, ite_true]
    exact rtLinkSegW_ok base hZ repB ι

/-- **`RepOkW` for `rtC1c`.** -/
theorem repOkW_rtC1c {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base) :
    RepOkW rtC1c impl₀ base := fun _ hπ ι => rtC1c_ok hZ hB hπ ι

end N4s
end FR

end G6_FRNodeRows4RepLT

section G6_FRNodeRun4S

-- New for `flock-recursive` (PACK-4.4 §4.3; track B3). `compileX_run` at the node's slot prototypes;
-- the twin of S-E14's `slotImp_of_rep`/`gap4Imp_of_rep` (`FRNodeRows4Rep`).

/-!
# The slot's run on the reader's trace

`compileX_run` at prototype `π` (`protoCS π = compileX (Xof π) …`):

* **`protoProg_items`**: both prototypes ask `itemsOf seq4` (8,783 items), read off the group
  programs' relation to the kind programs (`progNodeGK_rel`, `progSegG_rel`) and `items_gen4`. So the
  answer-driven run on a trace of 8,783 entries exists and uses it up.
* **`askRowsP`**, **`impAP`**: prototype `π`'s ask rows (its frame) and its residual imports.
* **`SlotRunA`**: the run facts left to the row side, stated on the answer-driven run (auxiliary
  cells, the residual imports, the foreign flags). **`SlotImpA`**: per selectable index, the ask
  obligation `ATOk`, `SlotRunA` and the statement fact.
* **`slotImp_of_runA`**: the slot's rows, replay rows and ask rows with `SlotImpA` give S-N2's
  `SlotImp` (the run's existence included). **`gap4Imp_of_run`**: `Gap4.imp` from `StmtN4`, the folds
  of the replay and ask rows into `nodeIRows4`, and `SlotImpA` at every active slot.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ

/-! ## The prototypes ask `seq4`'s items -/

theorem item_at {h : Reg → Op} (hh : ∀ s, (h s).item? = none) (pf : Bool) (ι : Kind) (op : Op) :
    (Op.at h pf ι op).item? = op.item? := by
  cases op <;> first | rfl | exact hh _ | (simp only [Op.at]; split <;> rfl)

theorem items_uni {ι : Kind} : ∀ {ops ops' : List Op}, List.Forall₂ (UniRel ι) ops ops' →
    ops.filterMap Op.item? = ops'.filterMap Op.item?
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨-, e | e⟩ := h <;> subst e <;>
      rw [List.filterMap_cons, List.filterMap_cons, item_at (fun _ => rfl), items_uni hs]

/-- **Prototype `π` asks `seq4`'s items.** -/
theorem protoProg_items (π : ℕ) : (protoProg π).ops.filterMap Op.item? = itemsOf seq4 := by
  unfold protoProg; split_ifs
  · rw [items_uni (progNodeGK_rel N4c.cells4 cells4_len .L32), progNode, genNode,
      items_gen4 _ _ _ (noAsk_finOps4 _)]
  · rw [items_uni (progSegG_rel .L32), progSeg, genSeg, items_gen4 _ _ _ (noAsk_finOps4 _)]

/-- **The answer-driven run of prototype `π` on a trace of 8,783 entries exists and uses it up.** -/
theorem execA_proto (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) {tr : Trace} (hl : tr.length = 8783) :
    ∃ s, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) := by
  obtain ⟨s, he⟩ := execA_some (impl := impl) (κ := ι) (inp := inp) (protoProg π).ops St.init tr
    (by rw [protoProg_items, itemsOf_seq4_len, hl])
  rw [protoProg_items, itemsOf_seq4_len, ← hl, List.drop_length] at he
  exact ⟨s, he⟩

/-! ## At a slot -/

/-- **Prototype `π`'s ask rows** (its frame: M-relative cells of region `π`). -/
def askRowsP (A : AT) (π : ℕ) : List Row :=
  askRowsX (Xof π) (protoP π) A (CS.init (baseR π)) none 0 (protoProg π).ops

/-- Prototype `π`'s import registers that are neither asks nor covered by `rt` or `A`. -/
def impAP (rt : RT) (A : AT) (π : ℕ) : List ℕ :=
  impAX (Xof π) (protoP π) rt A (CS.init (baseR π)) (protoProg π).ops

/-- **The run facts left to the row side**, on prototype `π`'s answer-driven run on `tr`: the
auxiliary cells, the residual imports and the foreign flags. -/
def SlotRunA (rt : RT) (A : AT) (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) (tr : Trace) (w : Asg) : Prop :=
  ∀ s : St, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
    (∀ a ∈ (protoCS π).aux, a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)) ∧
    (∀ i ∈ impAP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧
    (∀ p ∈ (protoCS π).fors, flagOf impl ι inp (s.regs.extract 0 p.2) p.1 = true)

/-- **The ask rows hold** at slot `v` (in its prototype's frame, at the slot's assignment). -/
def AskHolds (A : ℕ → AT) (κ : NodeKind) (v : ℕ) (w : Asg) : Prop :=
  ∀ r ∈ askRowsP (A (protoOf κ v)) (protoOf κ v), r.Holds (slotAsg κ v w)

/-- **What slot `v` leaves to the row side**: at every index its selectors may pick, the ask
obligation on the trace, the residual run facts and the statement fact. -/
def SlotImpA (rt : ℕ → RT) (A : ℕ → AT) (impl₀ : OpImpl) (base : NodeKind → OpImpl) (κ : NodeKind) (v : ℕ) (w : Asg)
    (inp : Input) (tr : Trace) : Prop :=
  ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
    ATOk (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (A (protoOf κ v)) ι inp (slotAsg κ v w) tr ∧
    SlotRunA (rt (protoOf κ v)) (A (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp tr (slotAsg κ v w) ∧
    stmtOk4 seq4 (kindP (protoOf κ v) ι) inp = true

/-- **The run at a slot**: its rows, replay rows and ask rows with `SlotImpA` give `SlotImp`, the
run on `tr` (8,783 entries) included. -/
theorem slotImp_of_runA {rt : ℕ → RT} {A : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind} {v : ℕ}
    {w : Asg} {inp : Input} {tr : Trace} (hl : tr.length = 8783) (hrows : SlotRows κ v w)
    (hrep : RepHolds rt κ v w) (hask : AskHolds A κ v w) (h : SlotImpA rt A impl₀ base κ v w inp tr) :
    SlotImp impl₀ base κ v w inp tr := by
  intro ι hS
  obtain ⟨hA, hR, hst⟩ := h ι hS
  have hπ := protoOf_le' κ v
  have hX := tplExt4A_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base hπ ι)
    (protoLay (protoOf κ v)) (colA (protoOf κ v))
  obtain ⟨s, he⟩ := execA_proto (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp hl
  obtain ⟨hx, hi, hf⟩ := hR s he
  have key := compileX_run hX (hok _ hπ ι) hA (baseR (protoOf κ v)) hS (selOk_repAsg hS) (agree_repAsg κ v w) he
    hrows.1 hrows.2 hx hi hrep hask hf
  exact ⟨⟨s, key.1, hx, fun i _ => key.2.2 i, hf⟩, hst⟩

/-! ## The node's indexed ask rows -/

/-- **Slot `v`'s ask rows** (absolute cells, the prototype's rows moved), at `v·2^20 + b + k`. -/
def askIRows4 (A : ℕ → AT) (κ : NodeKind) (v b : ℕ) : List (ℕ × Row) :=
  (askRowsP (A (protoOf κ v)) (protoOf κ v)).zipIdx.map fun p =>
    (v * slotM4 + b + p.2, rowMapC (fun c => mvC (protoOf κ v) v c + κ.oneCell) p.1)

/-- **The node's rows give the ask rows** once they are folded in (`hfold`). -/
theorem askHolds_of {A : ℕ → AT} {κ : NodeKind} {v b : ℕ} {w : Asg}
    (hfold : ∀ p ∈ askIRows4 A κ v b, p ∈ nodeIRows4 κ) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    AskHolds A κ v w := by
  unfold AskHolds
  unfold askIRows4 at hfold
  generalize askRowsP (A (protoOf κ v)) (protoOf κ v) = l at hfold ⊢
  generalize hF : (fun c => mvC (protoOf κ v) v c + κ.oneCell) = F at hfold
  intro r hr
  obtain ⟨k, hm⟩ := mem_zipIdx_map hr fun p : Row × ℕ => (v * slotM4 + b + p.2, rowMapC F p.1)
  have h3 := hE _ (hfold _ hm)
  dsimp only at h3
  rw [holds_rowMapC, ← hF] at h3
  exact h3

/-- **`Gap4.imp` from the run**: with the folds of the replay and ask rows, `StmtN4`'s rows and
`SlotImpA` at every active slot give `SlotImp` there. -/
theorem gap4Imp_of_run {rt : ℕ → RT} {A : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) (pf : Trace → Proof)
    {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {b : ℕ}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 A κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImpA rt A impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) := by
  intro v hv
  obtain ⟨-, -, -, hE, hP⟩ := hS
  have hlt := active_lt pf hv
  exact slotImp_of_runA hT₀ hT hok (slotTr4_length κ v w) (slotRows_of (one_of_pubCells hP) hlt hE)
    (repHolds_of (hfoldR v hlt) hE) (askHolds_of (hfoldA v hlt) hE) (h v hv)

end N4s
end FR

end G6_FRNodeRun4S

section G6_FRNodeRun4Ctrl

-- New for `flock-recursive` (track B3): controls for `FRNodeRun4`/`FRNodeRun4S`.

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
    (s := ⟨#[.d zeroD, .d zeroD], true⟩) (tr' := []) hX (RT.none_okW _ _ _ 0)
    (pinSq_ok impl .L32 inpCtl wCtl zeroD) 1 selOk_ctl selOk_ctl (fun _ _ => rfl) rfl (by simp [hrows])
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

end G6_FRNodeRun4Ctrl
