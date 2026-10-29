-- New for `flock-recursive` (PACK-4.4 §1.3 `input`, §4.2; B3's `AT`; track IMP): the `input` ask
-- template, the composition of ask templates, and `imp` without `stmtOk4`.
import FRNodeRows4AskStmtS
import FRNodeRun4Ctrl
import FRNodeRows4ArenaPlace

/-!
# The `input` alias as an ask template, and what `imp` still needs

* **`AT.add`**: two ask templates side by side (covers either's ops, emits both rows). The context
  of the sum gives each part's (`askCtx_add`), so `ATAsk`/`ATImp` compose (`atOk_add`): the ask
  templates of PACK §1.3's classes can be built and proved one class at a time.
* **`AT.inp X π`**: the `input` class (`vk`, `c`; PACK §1.3). At an `input j` op it ties the
  compiled slot's two cells to the region's `input` cells `inC π j h` (`W4.inOff`, between arena₁
  and the bits), or emits a failing row if the compile did not give a digest slot.
  **`atImp_inp`**: given `InpCells` (the `input` cells hold `vk`'s and `c`'s halves), it meets `ATImp`.
* **`inpCells_of_rows`**: the node's `input` rows (`W4.inpRows`, in `xRowsA`), `PubCells4` and the
  statement rows give `InpCells` at every active slot and selectable index (with `stmtC_sub`,
  `stmtC_prev`, `stmtVk`).
* **`gap4Imp_of_runS`**: B3's `gap4Imp_of_run` with `stmtOk4` discharged (`stmtOk4_of_rows`): `imp`
  from the folds, `ATOk` and `SlotRunA` at every active slot.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4

/-! ## Composing ask templates -/

/-- **Two ask templates side by side.** -/
def _root_.FR.Circ.AT.add (A B : AT) : AT := ⟨fun op => A.cov op || B.cov op, fun P cs pre op k => A.rows P cs pre op k ++ B.rows P cs pre op k⟩

section Add
variable {impl : OpImpl} {X : Ext} {A B : AT} {κ : Kind} {inp : Input} {w : Asg} {tr : Trace}

theorem askCtx_add {P : Params} {cs : CS} {pre : Option Op} {op : Op} {k : ℕ} {regs : Array Val}
    (h : AskCtx impl (A.add B) κ inp w P cs pre op k regs) :
    AskCtx impl A κ inp w P cs pre op k regs ∧ AskCtx impl B κ inp w P cs pre op k regs :=
  ⟨⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r (List.mem_append_left _ hr)⟩,
    ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r (List.mem_append_right _ hr)⟩⟩

/-- **The sum's asks are sound if the first part's are.** -/
theorem atAsk_add (h : ATAsk impl X A κ inp w tr) : ATAsk impl X (A.add B) κ inp w tr :=
  fun P cs pre op k regs q e hc => h P cs pre op k regs q e (askCtx_add hc).1

/-- **The sum's covered imports are sound if each part's are.** -/
theorem atImp_add (hA : ATImp impl X A κ inp w) (hB : ATImp impl X B κ inp w) :
    ATImp impl X (A.add B) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  rcases (by simpa [AT.add] using hcov : A.cov op = true ∨ B.cov op = true) with h | h
  · exact hA P cs pre op k regs vs ok h (askCtx_add hc).1 hev himp
  · exact hB P cs pre op k regs vs ok h (askCtx_add hc).2 hev himp

theorem atOk_add (hA : ATOk impl X A κ inp w tr) (hB : ATImp impl X B κ inp w) :
    ATOk impl X (A.add B) κ inp w tr :=
  ⟨atAsk_add hA.1, atImp_add hA.2 hB⟩

end Add

/-! ## A digest's halves -/

/-- The halves of a digest given by its bytes. -/
theorem halves_of_toList (d : Digest) (x y : Vector UInt8 16) (hD : d.toList = x.toList ++ y.toList) :
    dlo d = F.ofBytes x ∧ dhi d = F.ofBytes y := by
  constructor
  · rw [dlo]; refine congrArg F.ofBytes (Vector.ext fun i hi => ?_)
    rw [Vector.getElem_ofFn, ← Vector.getElem_toList, ← Vector.getElem_toList]
    simp only [hD]
    rw [List.getElem_append_left (by simpa using hi)]
    all_goals simp
    all_goals omega
  · rw [dhi]; refine congrArg F.ofBytes (Vector.ext fun i hi => ?_)
    rw [Vector.getElem_ofFn, ← Vector.getElem_toList, ← Vector.getElem_toList]
    simp only [hD]
    rw [List.getElem_append_right (by simp)]
    simp only [Vector.length_toList]
    congr 1
    all_goals simp
    all_goals omega

/-- **`digestOf`'s halves are its two cells.** -/
theorem dlo_digestOf (w : ℕ → F) (a b : ℕ) : dlo (Read.digestOf w a b) = w a ∧ dhi (Read.digestOf w a b) = w b := by
  have hA : wordsBytes (Read.elemWords (w a)) = (F.toBytes (w a)).toList := by
    conv_lhs => rw [← F.ofBytes_toBytes (w a)]
    exact Snd.wordsBytes_elemWords _
  have hB : wordsBytes (Read.elemWords (w b)) = (F.toBytes (w b)).toList := by
    conv_lhs => rw [← F.ofBytes_toBytes (w b)]
    exact Snd.wordsBytes_elemWords _
  have hD : (Read.digestOf w a b).toList = (F.toBytes (w a)).toList ++ (F.toBytes (w b)).toList := by
    rw [Read.digestOf, Read.digestW_toList (by simp [Read.elemWords]), wordsBytes, List.flatMap_append,
      ← wordsBytes, ← wordsBytes, hA, hB]
  have := halves_of_toList _ _ _ hD
  rw [F.ofBytes_toBytes, F.ofBytes_toBytes] at this
  exact this

/-! ## The `input` template -/

/-- Region `π`'s `input` cell for half `h` of `vk` (`j = 0`) or `c` (`j = 1`) (prototype frame). -/
def inC (π j h : ℕ) : ℕ := π * slotM4 + inOff + 2 * j + h

/-- **The `input` cells sit between arena₁ and the bits** (clear of the compile's cells, the
arenas and the templates: `arena_cells`, `logs/B2pp/arenafit.log`). -/
theorem inp_cells : arA1 + arN ≤ inOff ∧ inOff + 4 ≤ arBt := by
  rw [arN_eq]; exact ⟨by decide, by decide⟩

/-- A row no assignment with `one = 1` meets (`1·1 = 0`). -/
def failR (P : Params) : Row := ⟨P.one, P.one, []⟩

/-- **The `input j` op's rows**: its digest slot's two cells are the `input` cells, else `failR`. -/
def inpRowsT (X : Ext) (π : ℕ) (P : Params) (cs : CS) (j : ℕ) : List Row :=
  match (stepOut X P cs (.input j)).slots with
  | [some (.d, [l₀, l₁])] =>
    [⟨P.one, l₀.sub (Lin.cell (inC π (if j = 0 then 0 else 1) 0)), []⟩,
     ⟨P.one, l₁.sub (Lin.cell (inC π (if j = 0 then 0 else 1) 1)), []⟩]
  | _ => [failR P]

/-- **The `input` template** of prototype `π` (extension `X`): covers the `input` ops. -/
def AT.inp (X : Ext) (π : ℕ) : AT where
  cov op := match op with | .input _ => true | _ => false
  rows P cs _ op _ := match op with | .input j => inpRowsT X π P cs j | _ => []

/-- **The region's `input` cells hold `vk`'s and `c`'s halves.** -/
def InpCells (w : Asg) (π : ℕ) (inp : Input) : Prop :=
  w (inC π 0 0) = dlo inp.vk ∧ w (inC π 0 1) = dhi inp.vk ∧ w (inC π 1 0) = dlo inp.c ∧ w (inC π 1 1) = dhi inp.c

/-- **The `input` template is sound** where the `input` cells hold the input. -/
theorem atImp_inp {impl : OpImpl} {X : Ext} {π : ℕ} {κ : Kind} {inp : Input} {w : Asg}
    (h : InpCells w π inp) : ATImp impl X (AT.inp X π) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev _
  cases op with
  | input j =>
    obtain ⟨hsel, -, -, hrows⟩ := hc
    simp only [evalOp, Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    have hr : ∀ r ∈ inpRowsT X π P cs j, r.Holds w := hrows
    unfold inpRowsT at hr
    split at hr
    · rename_i l₀ l₁ hsl
      rw [hsl]
      have r0 := hr _ List.mem_cons_self
      have r1 := hr _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [Row.Holds, Lin.ev_sub, Lin.ev_cell, hsel.1, one_mul, Lin.ev_nil] at r0 r1
      refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      simp only [List.map_cons, List.map_nil, encV, sub_eq_zero.1 r0, sub_eq_zero.1 r1]
      obtain ⟨h0, h1, h2, h3⟩ := h
      split_ifs <;> simp_all
    · exfalso
      have := hr _ List.mem_cons_self
      simp [failR, Row.Holds, hsel.1] at this
  | _ => simp [AT.inp] at hcov

section Rows
variable {pf : Trace → Proof} {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg}

theorem slotAsg_inC (κ : NodeKind) (v : ℕ) (w : Asg) (j h : ℕ) :
    slotAsg κ v w (inC (protoOf κ v) j h) = w (κ.oneCell + v * slotM4 + inOff + 2 * j + h) := by
  simp only [slotAsg, mvC, inC, Nat.add_assoc, Nat.add_sub_cancel_left]
  congr 1; omega

/-- **The node's `input` rows, `PubCells4` and the statement rows give `InpCells`** at every
active slot and selectable index. -/
theorem inpCells_of_rows (hpv : PfView pf) (hpf : PfHdr pf)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      InpCells (slotAsg κ v w) (protoOf κ v) (N4c.slotIn (rd4 pf) κ vk c₁ w v) := by
  have hR : ∀ r ∈ inpRows κ, r.Holds w := fun r hr => stmtRows_hold hS r (List.mem_append_right _ hr)
  have hP := hS.2.2.2.2
  have hone := one_of_pubCells hP
  have hvk : ∀ σ < 2, w (N4c.seedC κ σ 0) = dlo vk ∧ w (N4c.seedC κ σ 1) = dhi vk := fun σ hσ => by
    rw [← stmtVk hP hσ]; exact ⟨(dlo_digestOf _ _ _).1.symm, (dlo_digestOf _ _ _).2.symm⟩
  rintro v (⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩) ι hι
  · have hc : w (N4c.seedC κ 0 2) = dlo c₁ ∧ w (N4c.seedC κ 0 3) = dhi c₁ := by
      rw [← stmtC_prev hP hp]; exact ⟨(dlo_digestOf _ _ _).1.symm, (dlo_digestOf _ _ _).2.symm⟩
    have hr : ∀ h < 2, w (κ.oneCell + inOff + h) = w (N4c.seedC κ 0 h) ∧
        w (κ.oneCell + inOff + 2 + h) = w (N4c.seedC κ 0 (2 + h)) := fun h hh => by
      have hm : ∀ r ∈ [eqRow κ.oneCell (κ.oneCell + inOff + h) (N4c.seedC κ 0 h),
          eqRow κ.oneCell (κ.oneCell + inOff + 2 + h) (N4c.seedC κ 0 (2 + h))], r.Holds w := fun r hr' =>
        hR r (List.mem_append_right _ (by rw [if_pos hp]; exact List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, hr'⟩))
      exact ⟨eqRow_holds hone (hm _ List.mem_cons_self),
        eqRow_holds hone (hm _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    have e0 := hr 0 (by norm_num); have e1 := hr 1 (by norm_num)
    simp only [Nat.add_zero] at e0 e1
    rw [N4c.slotIn, if_pos ⟨hp, rfl⟩]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [slotAsg_inC] <;> simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add]
    · rw [e0.1, (hvk 0 (by norm_num)).1]
    · rw [e1.1, (hvk 0 (by norm_num)).2]
    · rw [e0.2, hc.1]
    · rw [show κ.oneCell + inOff + 2 + 1 = κ.oneCell + inOff + 2 + 1 from rfl, e1.2, hc.2]
  · rw [kA_rd4 pf κ ha] at hi
    have hi' : i < κ.maxK := lt_of_lt_of_le hi (kAct_le κ a w)
    obtain ⟨-, -, hpv', -⟩ := sub_facts κ ha hi'
    rw [protoOf_seg hpv'] at hι ⊢
    have hnp : ¬ (κ.hasPrev = true ∧ N4c.sub κ a i = 0) := fun ⟨h1, h2⟩ => by
      simp [isPrevSlot, h1, h2] at hpv'
    have hcS := stmtC_sub hpf hpv hS ha hi hι
    set B := N4c.stmtB κ + 3 * N4c.sub κ a i
    have hr : ∀ h < 2, w (κ.oneCell + N4c.sub κ a i * slotM4 + inOff + h) = w (N4c.seedC κ (N4c.aggChild κ a) h) ∧
        w (κ.oneCell + N4c.sub κ a i * slotM4 + inOff + 2 + h) = w (hc B (2 + h)) := fun h hh => by
      have hm : ∀ r ∈ [eqRow κ.oneCell (κ.oneCell + N4c.sub κ a i * slotM4 + inOff + h) (N4c.seedC κ (N4c.aggChild κ a) h),
          eqRow κ.oneCell (κ.oneCell + N4c.sub κ a i * slotM4 + inOff + 2 + h) (hc B (2 + h))], r.Holds w :=
        fun r hr' => hR r (List.mem_append_left _ (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha,
          List.mem_flatMap.2 ⟨i, List.mem_range.2 hi', List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, hr'⟩⟩⟩))
      exact ⟨eqRow_holds hone (hm _ List.mem_cons_self),
        eqRow_holds hone (hm _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    have e0 := hr 0 (by norm_num); have e1 := hr 1 (by norm_num)
    simp only [Nat.add_zero] at e0 e1
    have hv := hvk (N4c.aggChild κ a) (N4c.aggChild_lt κ ha)
    have hcc : w (hc B 2) = dlo (N4c.slotIn (rd4 pf) κ vk c₁ w (N4c.sub κ a i)).c ∧
        w (hc B 3) = dhi (N4c.slotIn (rd4 pf) κ vk c₁ w (N4c.sub κ a i)).c := by
      rw [hcS]; exact ⟨(dlo_digestOf _ _ _).1.symm, (dlo_digestOf _ _ _).2.symm⟩
    have hvk' : (N4c.slotIn (rd4 pf) κ vk c₁ w (N4c.sub κ a i)).vk = vk := by rw [N4c.slotIn, if_neg hnp]
    have h1 : inC 1 = inC (protoOf κ (N4c.sub κ a i)) := by rw [protoOf_seg hpv']
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h1, slotAsg_inC] <;> simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    · rw [e0.1, hvk', hv.1]
    · rw [e1.1, hvk', hv.2]
    · rw [e0.2, hcc.1]
    · rw [e1.2, hcc.2]

end Rows

/-! ## `imp` without `stmtOk4`, and with the `input` template -/

/-- **`gap4Imp_of_run` with `stmtOk4` discharged** (`stmtOk4_of_rows`): `Gap4.imp` from the folds,
`StmtN4`, `PfHdr`, `PfView`, and at every active slot and selectable index the ask obligation and
the residual run facts. -/
theorem gap4Imp_of_runS {rt : ℕ → RT} {A : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {pf : Trace → Proof}
    (hpf : PfHdr pf) (hpv : PfView pf) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {b : ℕ}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 A κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      ATOk (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (A (protoOf κ v)) ι
          (N4c.slotIn (rd4 pf) κ vk c₁ w v) (slotAsg κ v w) ((rd4 pf).slotTr κ v w) ∧
        SlotRunA (rt (protoOf κ v)) (A (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι
          (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) :=
  gap4Imp_of_run hT₀ hT hok pf hfoldR hfoldA hS fun v hv ι hι =>
    ⟨(h v hv ι hι).1, (h v hv ι hι).2, stmtOk4_of_rows hpf hpv hS v hv ι hι⟩

/-- Prototype `π`'s ask template `Aq π` with the `input` template beside it. -/
def withInp (Aq : ℕ → AT) (π : ℕ) : AT := (Aq π).add (AT.inp (Xof π) π)

/-- **`imp` with the `input` class discharged**: the `input` registers' representation comes from
the `input` template and rows (`atImp_inp`, `inpCells_of_rows`); what remains per slot is the other
templates' `ATOk` (`Aq`) and the residual run facts (`SlotRunA`, whose imports exclude `input`). -/
theorem gap4Imp_of_runI {rt : ℕ → RT} {Aq : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {pf : Trace → Proof}
    (hpf : PfHdr pf) (hpv : PfView pf) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {b : ℕ}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withInp Aq) κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      ATOk (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (Aq (protoOf κ v)) ι
          (N4c.slotIn (rd4 pf) κ vk c₁ w v) (slotAsg κ v w) ((rd4 pf).slotTr κ v w) ∧
        SlotRunA (rt (protoOf κ v)) (withInp Aq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι
          (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) :=
  gap4Imp_of_runS hT₀ hT hok hpf hpv hfoldR hfoldA hS fun v hv ι hι =>
    ⟨atOk_add (h v hv ι hι).1 (atImp_inp (inpCells_of_rows hpv hpf hS v hv ι hι)), (h v hv ι hι).2⟩

/-- (+) **`input` ops only**: the template covers `input 0` and not a proof field. -/
theorem atInp_cov (X : Ext) (π : ℕ) : (AT.inp X π).cov (.input 0) = true ∧ (AT.inp X π).cov (.piField 0 0 1) = false :=
  ⟨rfl, rfl⟩

/-- (−) **The template needs `InpCells`**: at `wCtl` (every cell but `0` is `0`) the `input 0` op's
rows hold (its cells and the `input` cells are all `0`), yet its slot does not represent
`vk = 1^32`. -/
theorem atImp_inp_neg (impl : OpImpl) : ¬ ATImp impl noExt (AT.inp noExt 0) .L32 inpOne wCtl := fun h => by
  have hr : ∀ r ∈ (AT.inp noExt 0).rows pCtl (CS.init 5) none (.input 0) 0, r.Holds wCtl := by
    simp [AT.inp, inpRowsT, stepOut, noExt, opOut, imports, impSlots, Ty.len, List.range_succ, CS.cell,
      CS.init, Row.Holds, wCtl, pCtl, fixedP, inC, inOff]
  have := h pCtl (CS.init 5) none (.input 0) 0 #[] _ _ rfl ⟨selOk_ctl, invK_init wCtl .L32 5, trivial, hr⟩ rfl rfl
  simp [stepOut, noExt, opOut, imports, impSlots, Ty.len, List.range_succ, RepS, tyOf, encV, CS.cell,
    CS.init, wCtl] at this
  obtain ⟨h0, h1⟩ := this
  have hz : (inpOne.vk : Digest) = zeroD :=
    digest_ext (by rw [dlo_zero]; exact h0.symm) (by rw [dhi_zero]; exact h1.symm)
  exact absurd hz (by decide)

end N4s
end FR
