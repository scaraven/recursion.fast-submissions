-- New for `flock-recursive` (SEG-R §4.5, stage SEG-R1): the segment program's replay wrapper.
import FRNodeRows4RepK
import FRVIRTplChain

/-!
# Replay templates on muxed inputs (`rtKD`), and the dead ops' zero rows (`rtEvZ`)

Prototype 1 (the segment program) runs the same ops at its three selector indices; a kind only
selects which registers a `packFK`/`keep` reads. So one template serves the three kinds, over
**canonical inputs** that the wrapper muxes from the three operand blocks (SEG-R §4.5; C1's `kTpl`
instantiates three sub-templates instead):

* **`KOpD`**: C1's `KOp` with one template `T` over `W` canonical inputs. `lay ts p` is the position
  in the operand encoding (at types `ts`) that canonical input `p` reads (`none`: the input is `0`);
  `zf ts` the encoding positions the wrapper **forces to `0`** (rows `one · f = 0`, e.g. the `f₁` of
  an `F`-point claim coordinate); `T cst` is the template given, per canonical input, a constant it may
  fold (`some c`: the input is `c`), with its own **forcing rows** (`RowT`s over its inputs and locals,
  e.g. bit decompositions in `pad` locals).
* **`kdPos`/`kdAll`** (the mux): a canonical input whose three forms are equal is that form (a
  constant hint if it is zero or `c · Σ_κ sel_κ`); otherwise it is `Σ_ι m_ι` over three mux locals
  with rows `sel_ι · f_ι = m_ι`.
* **`kdRows`/`rtKD`**: the mux rows, the zero-forcing rows, the template's gate rows and forcing rows
  (locals after the mux's), and the copy rows on the import's cells; the rejecting row on any other
  shape (as `kRows`).
* **`KOkD impl ι K`**: the per-op obligation (pure functions): at the inputs the selected index's
  operands give, with the forced positions zero and the constants as hinted, wherever the template's
  gate equations and forcing rows hold its outputs are the op's values. **`rtKD_okW`**: `KOkD` gives
  `RTOkW`.
* **`rtEvZ`** (`rtEvZ_okW`): prototype 1's `evalM`/`evalL`, pinned to zero in `implSeg` (SEG-R1),
  replayed by `one · out = 0` on their three `F` cells; no hypothesis.

SEG-R2: the definitions (`KOpD` … `rtKD`, `rtEvZ`) moved verbatim to `FRNodeRows4SegD` (below `FRNodeRows4`, so that the
fold names them); the theorems stay here.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## The wrapper -/

/-- **The per-op obligation** (pure functions): at index `ι` the op never asks, and at operand
types `ts` it serves, its values have `tys`, and wherever the forced positions are zero, the
canonical inputs are the selected operands' (the hinted constants included) and the template's gate
equations and forcing rows hold, the outputs are the values' encodings. -/
def KOkD (impl : OpImpl) (ι : Kind) (K : KOpD) : Prop :=
  ∀ op, K.cov op = true → (∀ inp regs q, evalOp impl ι inp regs op ≠ .ask q) ∧
    ∀ inp regs vs ok ts, evalOp impl ι inp regs op = .vals vs ok → K.inOk ts = true →
      (K.args op ι).map (fun a => tyOf (rd regs a)) = ts.map some →
      vs.map tyOf = K.tys.map some ∧
      ∀ cst : List (Option F),
        (∀ q ∈ K.zf ts, ((K.args op ι).flatMap fun a => encV (rd regs a)).getD q 0 = 0) →
        ∀ e : Env, e.one = 1 →
          (∀ p < K.W, e.inp p = ((K.lay ts p).map fun q => ((K.args op ι).flatMap fun a => encV (rd regs a)).getD q 0).getD 0) →
          (∀ p c, cst.getD p none = some c → e.inp p = c) →
          GM.Ok e (K.T cst) fun o => (∀ r ∈ o.2, r.Holds e) → o.1.map (LinT.ev e) = vs.flatMap encV

/-! ## The mux's values -/

theorem kdMux_ev {P : Params} {g : Kind → Lin} {w : Asg} :
    ∀ (ks : List Kind) (c : ℕ), (∀ r ∈ (kdMux P g ks c).2, r.Holds w) →
      (kdMux P g ks c).1.ev w = (ks.map fun ι => (P.sel ι).ev w * (g ι).ev w).sum
  | [], _, _ => rfl
  | ι :: ks, c, h => by
    simp only [kdMux, List.mem_cons, forall_eq_or_imp] at h
    have h0 := h.1
    simp only [Row.Holds, Lin.ev_cell] at h0
    simp only [kdMux, Lin.ev_cons, one_mul, List.map_cons, List.sum_cons, kdMux_ev ks (c + 1) h.2, h0]

theorem cstOf_eq {P : Params} {l : Lin} {c : F} (h : cstOf P l = some c) : l = P.kc fun _ => c := by
  unfold cstOf at h
  split at h
  · split_ifs at h with h'
    · simp only [Option.some.injEq] at h; subst h; exact h'
  · simp at h

/-- **One canonical input's value** at the selected kind `ι` (its rows holding), and its hint. -/
theorem kdPos_ev {P : Params} {g : Kind → Lin} {c : ℕ} {w : Asg} {ι : Kind} (hP : SelOk w P ι)
    (h : ∀ r ∈ (kdPos P g c).2.2.1, r.Holds w) :
    (kdPos P g c).1.ev w = (g ι).ev w ∧ ∀ v, (kdPos P g c).2.1 = some v → (kdPos P g c).1.ev w = v := by
  unfold kdPos at h ⊢
  split_ifs at h ⊢ with he hz
  · refine ⟨by obtain ⟨h1, h2⟩ := he; cases ι <;> simp [h1, h2], fun v hv => ?_⟩
    simp only [Option.some.injEq] at hv; subst hv; exact zeroLin_ev hz w
  · refine ⟨by obtain ⟨h1, h2⟩ := he; cases ι <;> simp [h1, h2], fun v hv => ?_⟩
    rw [cstOf_eq hv, kc_ev hP]
  · refine ⟨?_, fun v hv => by simp at hv⟩
    rw [kdMux_ev _ _ h]
    have hs : ∀ ι', (P.sel ι').ev w = if ι' = ι then 1 else 0 := hP.2
    cases ι <;> simp [kinds, hs]

theorem kdAll_ev {P : Params} {g : ℕ → Kind → Lin} {w : Asg} {ι : Kind} (hP : SelOk w P ι) :
    ∀ (n p c : ℕ), (∀ r ∈ (kdAll P g n p c).2.2.1, r.Holds w) →
      (kdAll P g n p c).1.length = n ∧
      (∀ i < n, ((kdAll P g n p c).1.getD i []).ev w = (g (p + i) ι).ev w) ∧
      ∀ i v, (kdAll P g n p c).2.1.getD i none = some v → ((kdAll P g n p c).1.getD i []).ev w = v
  | 0, _, _, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun i v h => by simp [kdAll] at h⟩
  | n + 1, p, c, h => by
    simp only [kdAll, List.mem_append] at h
    obtain ⟨h0, h1⟩ := kdPos_ev hP fun r hr => h r (.inl hr)
    obtain ⟨l, ih1, ih2⟩ := kdAll_ev hP n (p + 1) _ fun r hr => h r (.inr hr)
    refine ⟨by simp [kdAll, l], fun i hi => ?_, fun i v hv => ?_⟩
    · rcases i with _ | i
      · simpa [kdAll] using h0
      · simp only [kdAll, List.getD_cons_succ]
        rw [ih1 i (by omega), show p + 1 + i = p + (i + 1) by omega]
    · rcases i with _ | i
      · simp only [kdAll, List.getD_cons_zero] at hv ⊢; exact h1 v hv
      · simp only [kdAll, List.getD_cons_succ] at hv ⊢; exact ih2 i v hv

/-! ## `KOkD` gives `RTOkW` -/

theorem rtKD_rows {K : KOpD} {B cb : ℕ} {P : Params} {cs : CS} {op : Op} {outs : List Slot}
    (hc : K.cov op = true) : (rtKD K B cb).rows P cs op outs = kdRows K B cb P cs op outs := by
  unfold rtKD; dsimp only; rw [ite_cond_eq_true _ _ (eq_true hc)]

/-- A block's form at `p` reads the encoding's entry (`kOps_rep`'s values; `0` past it). -/
theorem kdG_ev {w : Asg} {K : KOpD} {b : List Ty × List Lin} {xs : List F} (hb : b.2.map (Lin.ev w) = xs)
    (p : ℕ) : (kdG K b p).ev w = ((K.lay b.1 p).map fun q => xs.getD q 0).getD 0 := by
  unfold kdG
  cases h : K.lay b.1 p with
  | none => simp
  | some q =>
    simp only [Option.map_some, Option.getD_some]
    rw [← hb, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases b.2[q]? <;> rfl

/-- **`KOkD` gives `RTOkW`** (the replay rows at `w'`, agreeing with `w` below `B`; the mux's locals
from `cb`). -/
theorem rtKD_okW {impl : OpImpl} {X : Ext} {ι : Kind} {K : KOpD} (B cb : ℕ) (hK : KOkD impl ι K) :
    RTOkW impl X (rtKD K B cb) ι B := by
  intro P cs op hc
  obtain ⟨hask, hval⟩ := hK op hc
  refine ⟨hask, fun inp w w' regs vs ok hP hP' hI hA hrows hev _ => ?_⟩
  generalize (stepOut X P cs op).slots = outs at hrows ⊢
  rw [rtKD_rows hc] at hrows
  unfold kdRows at hrows
  split at hrows
  · rename_i bs hbs
    split_ifs at hrows with hoi
    · simp only [Bool.and_eq_true, beq_iff_eq] at hoi
      obtain ⟨⟨⟨ho, hok⟩, hlt⟩, hlen⟩ := hoi
      rw [List.all_append, Bool.and_eq_true] at hlt
      obtain ⟨b, hl3, hb, hk⟩ := kBlocks_some hbs ι
      obtain ⟨hty, hfe⟩ := kOps_rep hI.2.2 hk
      set xs := (K.args op ι).flatMap fun a => encV (rd regs a) with hxs
      obtain ⟨htv, hT⟩ := hval inp regs vs ok b.1 hev
        (List.all_eq_true.1 hok b (List.mem_of_getElem? hb)) hty
      have hbj : bs.getD (kIx ι) ([], []) = b := by rw [List.getD_eq_getElem?_getD, hb]; rfl
      have hbm : b ∈ bs := List.mem_of_getElem? hb
      -- the block's forms read the same at `w'` and `w`
      have hfe' : b.2.map (Lin.ev w) = xs := hfe
      have hbw : b.2.map (Lin.ev w') = xs := by
        rw [← hfe']
        refine map_ev_agree hA (List.all_eq_true.2 fun l hl => List.all_eq_true.1 hlt.1 l ?_)
        exact List.mem_flatMap.2 ⟨b, hbm, hl⟩
      set m := kdIn K P cb bs with hm
      set t := K.T m.2.1 0 with ht
      have hr : ∀ r ∈ m.2.2.1, r.Holds w' := fun r hr => hrows r (by simp [hr])
      obtain ⟨-, hmv, hmc⟩ := kdAll_ev hP' K.W 0 cb hr
      have hmv' : ∀ p < K.W, (m.1.getD p []).ev w' = (kdG K (bs.getD (kIx ι) ([], [])) (0 + p)).ev w' := hmv
      have hmc' : ∀ i v, m.2.1.getD i none = some v → (m.1.getD i []).ev w' = v := hmc
      set e := envOf w' P.one m.1 m.2.2.2 with he
      have he1 : e.one = 1 := hP'.1
      have hinp : ∀ p < K.W, e.inp p = ((K.lay b.1 p).map fun q => xs.getD q 0).getD 0 := fun p hp => by
        show (m.1.getD p []).ev w' = _
        rw [hmv' p hp, zero_add, hbj, kdG_ev hbw p]
      have hcst : ∀ p c, m.2.1.getD p none = some c → e.inp p = c := fun p c hpc => hmc' p c hpc
      have hz : ∀ q ∈ K.zf b.1, xs.getD q 0 = 0 := fun q hq => by
        have hrow := hrows ⟨P.one, b.2.getD q [], []⟩ (by
          simp only [List.mem_append]
          exact .inl (.inl (.inl (.inr (List.mem_flatMap.2 ⟨b, hbm, List.mem_map.2 ⟨q, hq, rfl⟩⟩)))))
        simp only [Row.Holds, hP'.1, one_mul, Lin.ev_nil] at hrow
        rw [← hbw, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getD_eq_getElem?_getD] at hrow
        cases h' : b.2[q]? <;> simp_all
      have hE : Eqns e t.1 0 := inst_eqns hP'.1 m.1 m.2.2.2 ⟨t.1, []⟩ fun r hr =>
        hrows _ (by rw [← rowsTR_eq] at hr; simp [List.mem_map_of_mem hr])
      have hfr : ∀ r ∈ t.2.2, r.Holds e := fun r hr =>
        instRow_holds.1 (hrows _ (by simp [List.mem_map_of_mem hr]))
      have hO := hT m.2.1 hz e he1 hinp hcst 0 hE hfr
      have hcl : (outF outs).length = (t.2.1.map (instLin P.one m.1 m.2.2.2)).length := by
        rw [outsOk_len ho, List.length_map, hlen]
      have hc' := copyRows_ev hP'.1 hcl fun r hr => hrows r (List.mem_append_right _ hr)
      refine outsOk_rep ho htv ?_
      rw [← map_ev_agree hA hlt.2, hc', List.map_map, ← hO]
      exact List.map_congr_left fun l _ => instLin_ev _ _ _ _ l
    · exact (rej_false hP'.1 (List.mem_singleton_self _) hrows).elim
  · exact (rej_false hP'.1 (List.mem_singleton_self _) hrows).elim

/-! ## `evalM`, `evalL` at prototype 1: zero -/


theorem zeroF3_ok {B : ℕ} {P : Params} {outs : List Slot} {w w' : Asg} (hA : Agree B w w')
    (hone : P.one.ev w' = 1) (h : ∀ r ∈ zeroF3 B P outs, r.Holds w') :
    List.Forall₂ (RepS w) outs [.f 0, .f 0, .f 0] := by
  unfold zeroF3 at h
  split_ifs at h with hc
  · rw [Bool.and_eq_true] at hc
    refine outsOk_rep hc.1 rfl ?_
    rw [← map_ev_agree hA hc.2]
    have hl := outsOk_len hc.1
    have hz : ∀ l ∈ outF outs, l.ev w' = 0 := fun l hm => by
      have := h _ (List.mem_map_of_mem (f := fun l => (⟨P.one, l, []⟩ : Row)) hm)
      simpa [Row.Holds, hone] using this
    rw [List.map_congr_left hz, List.map_const', hl]; rfl
  · exact (rej_false hone (List.mem_singleton_self _) h).elim

/-- **Prototype 1's `evalM`/`evalL` replay is sound** at every index (no hypothesis: `implSeg`'s
pinned values are the values). -/
theorem rtEvZ_okW (impl₀ : OpImpl) (base : NodeKind → OpImpl) (B : ℕ) (ι : Kind) :
    RTOkW (implP impl₀ base 1 ι) (Xof 1) (rtEvZ B) ι B := by
  intro P cs op hc
  have hr : ∀ outs, (rtEvZ B).rows P cs op outs = zeroF3 B P outs := fun outs => by
    show (if isEvML op then zeroF3 B P outs else []) = _
    rw [if_pos (show isEvML op = true from hc)]
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  all_goals
    refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp w w' regs vs ok hP hP' hI hA hrows hev _ => ?_⟩
    rw [hr] at hrows
    simp only [evalOp, Res.vals.injEq,
      show ∀ a b, (implP impl₀ base 1 ι).evalM a b = (0, 0, 0) from fun _ _ => rfl,
      show ∀ a b, (implP impl₀ base 1 ι).evalL a b = (0, 0, 0) from fun _ _ => rfl] at hev
    obtain ⟨rfl, -⟩ := hev
    exact zeroF3_ok hA hP'.1 hrows

end N4s
end FR
