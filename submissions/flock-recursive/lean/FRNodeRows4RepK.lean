-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).
import FRNodeRows4RepS
import FRVIRTplKMux

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

theorem gatesAtGo_eq : ∀ (gs : List Gate) (k : ℕ) (acc : List (ℕ × Gate)),
    gatesAtGo gs k acc = (gatesAt gs k).reverse ++ acc
  | [], _, _ => rfl
  | g :: gs, k, acc => by
    rw [gatesAtGo, gatesAtGo_eq gs, gatesAt, List.reverse_cons, List.append_assoc]; rfl

theorem rowsTR_eq (T : Tpl) : rowsTR T = T.rows := by
  rw [rowsTR, gatesAtGo_eq, List.append_nil, List.reverse_reverse]; rfl

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
