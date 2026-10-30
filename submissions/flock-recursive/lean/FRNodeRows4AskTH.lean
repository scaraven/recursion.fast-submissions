-- G6: this module also holds the former modules `FRNodeRows4AskInp`, `FRNodeRsvLink`, `FRNodeRows4AskPosF`, `FRNodeRows4AskPos`, `FRNodeRows4AskPosR`, `FRNodeRows4AskTB` (one section each, in import order).
import FRNodeRows4AskStmtS
import FRNodeRun4Ctrl
import FRNodeRows4ArenaPlace
import FRNodeStmtR4
import FRXPf4
import FRNodeRows4AskB

section G6_FRNodeRows4AskInp

-- New for `flock-recursive` (PACK-4.4 §1.3 `input`, §4.2; B3's `AT`; track IMP): the `input` ask
-- template, the composition of ask templates, and `imp` without `stmtOk4`.

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

end G6_FRNodeRows4AskInp

section G6_FRNodeRsvLink

-- New for `flock-recursive` (revision 4.4.2, the reserve; RSV-S2b §5 item 4, RSV-S3 §5.4; track SRA):
-- slot 0's stacked `evalM` bound by the reserve's cells, as one more ask-template summand.

/-!
# The reserve's binding of slot 0's `evalM` (`gap4Imp_of_rsv`)

A node with a previous node replays `V(C)` in slot 0 (prototype 0). `V(C)`'s one stacked `evalM`
call (RSV2 §2.4, `rsvEOps`) has three output registers, imports of the circuit: nothing in the
slot's own rows binds them. `StmtN4R` does: its reserve cells (`PubCellsR4`) hold the node's child
claim `ch`, and the claim is true (`truthChildV`). The binding is a template beside IMP's (`AT.add`):

* **`AT.rsv X π`** (prototype 0 only) covers the `evalM` ops. At such an op its rows check, on the
  compile state, that the row point's 32 entries are the cells `tauC`, the column point's 25 entries
  the cells `sigC` and the three outputs the cells `rsvC 57 … 59` (`FRVerifierC4.rsvRel`, prototype
  frame). A component already *is* its cell (the compile's layout, `rsvcells.py`) costs no row
  (`eqRowIf`); another is tied to it by one row; a slot of the wrong shape emits `failR`.
* **`atImp_rsv`**: where those cells hold `ch` (`RsvCells`) and `ch` is true, the template meets
  `ATImp`: `ATImp` sees the invariant `InvK` at the op (the run's prefix), so the operands are `ch`'s
  `p_x ‖ s` and `p_y`, and `evalM_childV` gives the outputs `X₃`. **No prefix form of
  `compileX_run` is needed**: the induction already hands every covered op its prefix invariant.
* **`rsvCells_slot0`**: `PubCellsR4` is `RsvCells` at slot 0's assignment.
* **`gap4Imp_of_rsv`**: IMP's `gap4Imp_of_runI` over `StmtN4R`, with the reserve template beside the
  `input` one (`withRsv`): `SlotRunA`'s residual imports exclude slot 0's `evalM` outputs.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4

/-! ## The reserve's cells, prototype frame -/

/-- Reserve cell `j` (`rsvRel`: `x̂` 0 … 22, `ŷ` 23 … 47, `s` 48 … 56, `X₃` 57 … 59). -/
def rsvC (j : ℕ) : ℕ := rsvRel.getD j 0

/-- The row point's entry `j` (`x̂ ‖ s`, 32 entries). -/
def tauC (j : ℕ) : ℕ := if j < 23 then rsvC j else rsvC (25 + j)

/-- The column point's entry `j` (`ŷ`, 25 entries). -/
def sigC (j : ℕ) : ℕ := rsvC (23 + j)

/-- **The reserve's cells hold `ch`** (at an assignment in the prototype frame). -/
def RsvCells (w : Asg) (ch : List F) : Prop := ∀ j < 60, w (rsvC j) = ch.getD j 0

/-! ## The template -/

/-- **`l` is the cell `c`**: no row if it is syntactically, else the row `1·(l − c) = 0`. -/
def eqRowIf (P : Params) (l : Lin) (c : ℕ) : List Row :=
  if l = Lin.cell c then [] else [⟨P.one, l.sub (Lin.cell c), []⟩]

/-- **An `F`-array operand on the cells `f 0 … f (n−1)`**, else `failR`. -/
def argRows (P : Params) (s : Slot) (n : ℕ) (f : ℕ → ℕ) : List Row :=
  match s with
  | some (.af m, ls) =>
    if m = n ∧ ls.length = n then (ls.zipIdx).flatMap (fun p => eqRowIf P p.1 (f p.2)) else [failR P]
  | _ => [failR P]

/-- **Three `F` outputs on the cells `rsvC 57 … 59`**, else `failR`. -/
def outRows (P : Params) : List Slot → List Row
  | [some (.f, [l₀]), some (.f, [l₁]), some (.f, [l₂])] =>
    eqRowIf P l₀ (rsvC 57) ++ eqRowIf P l₁ (rsvC 58) ++ eqRowIf P l₂ (rsvC 59)
  | _ => [failR P]

/-- **The rows at an `evalM` op**: at every kind, the operands' slots on the reserve cells, and the
outputs' slots. -/
def rsvRowsT (X : Ext) (P : Params) (cs : CS) : Op → List Row
  | .evalM t s => kinds.flatMap (fun κ => argRows P (cs.slotK t κ) 32 tauC ++ argRows P (cs.slotK s κ) 25 sigC) ++
      outRows P (stepOut X P cs (.evalM t s)).slots
  | _ => []

/-- Whether an op is an `evalM`. -/
def isEvalM : Op → Bool
  | .evalM .. => true
  | _ => false

/-- **The reserve template** of prototype `π` (extension `X`): at prototype 0, the `evalM` ops. -/
def AT.rsv (X : Ext) (π : ℕ) : AT where
  cov op := π == 0 && isEvalM op
  rows P cs _ op _ := if π = 0 then rsvRowsT X P cs op else []

/-! ## Reading the rows -/

section Read
variable {P : Params} {w : Asg}

theorem eqRowIf_ev (h1 : P.one.ev w = 1) {l : Lin} {c : ℕ} (h : ∀ r ∈ eqRowIf P l c, r.Holds w) :
    l.ev w = w c := by
  unfold eqRowIf at h
  split_ifs at h with he
  · rw [he, Lin.ev_cell]
  · have := h _ List.mem_cons_self
    simp only [Row.Holds, Lin.ev_sub, Lin.ev_cell, h1, one_mul, Lin.ev_nil] at this
    exact sub_eq_zero.1 this

theorem failR_not (h1 : P.one.ev w = 1) : ¬ (failR P).Holds w := by
  simp [failR, Row.Holds, h1]

theorem zipIdx_ev (h1 : P.one.ev w = 1) (f : ℕ → ℕ) : ∀ (ls : List Lin) (k : ℕ),
    (∀ r ∈ (ls.zipIdx k).flatMap (fun p => eqRowIf P p.1 (f p.2)), r.Holds w) →
    ls.map (Lin.ev w) = (List.range' k ls.length).map (w ∘ f)
  | [], _, _ => rfl
  | l :: ls, k, h => by
    simp only [List.zipIdx_cons, List.flatMap_cons, List.mem_append] at h
    rw [List.map_cons, List.length_cons, List.range'_succ, List.map_cons,
      eqRowIf_ev h1 fun r hr => h r (.inl hr), zipIdx_ev h1 f ls (k + 1) fun r hr => h r (.inr hr)]
    rfl

/-- **An operand's rows give its slot**: an `F` array on the cells `f 0 … f (n−1)`. -/
theorem argRows_ev (h1 : P.one.ev w = 1) {s : Slot} {n : ℕ} {f : ℕ → ℕ}
    (h : ∀ r ∈ argRows P s n f, r.Holds w) :
    ∃ ls, s = some (.af n, ls) ∧ ls.map (Lin.ev w) = (List.range n).map (w ∘ f) := by
  unfold argRows at h
  split at h
  · rename_i m ls
    split_ifs at h with hm
    · obtain ⟨rfl, hl⟩ := hm
      refine ⟨ls, rfl, ?_⟩
      have := zipIdx_ev h1 f ls 0 h
      rwa [hl, ← List.range_eq_range'] at this
    · exact absurd (h _ List.mem_cons_self) (failR_not h1)
  · exact absurd (h _ List.mem_cons_self) (failR_not h1)

/-- **The outputs' rows give their slots.** -/
theorem outRows_ev (h1 : P.one.ev w = 1) {ss : List Slot} (h : ∀ r ∈ outRows P ss, r.Holds w) :
    ∃ l₀ l₁ l₂ : Lin, ss = [some (.f, [l₀]), some (.f, [l₁]), some (.f, [l₂])] ∧
      l₀.ev w = w (rsvC 57) ∧ l₁.ev w = w (rsvC 58) ∧ l₂.ev w = w (rsvC 59) := by
  unfold outRows at h
  split at h
  · rename_i l₀ l₁ l₂
    simp only [List.mem_append] at h
    exact ⟨l₀, l₁, l₂, rfl, eqRowIf_ev h1 fun r hr => h r (.inl (.inl hr)),
      eqRowIf_ev h1 fun r hr => h r (.inl (.inr hr)), eqRowIf_ev h1 fun r hr => h r (.inr hr)⟩
  · exact absurd (h _ List.mem_cons_self) (failR_not h1)

/-- `getD` of an array whose list is a mapped range. -/
theorem getD_of_toList {x : Array F} {n : ℕ} {g : ℕ → F} (hx : x.toList = (List.range n).map g) {j : ℕ}
    (hj : j < n) : x.getD j 0 = g j := by
  have hs : x.size = n := by rw [← Array.length_toList, hx, List.length_map, List.length_range]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
    ← Array.getElem_toList]
  simp only [hx, List.getElem_map, List.getElem_range]

/-- **A representing `F`-array register on the cells**: its value is the array of their values. -/
theorem af_of_rep {v : Val} {n : ℕ} {ls : List Lin} {g : ℕ → F} (hr : RepS w (some (.af n, ls)) v)
    (he : ls.map (Lin.ev w) = (List.range n).map g) :
    v.toAF.size = n ∧ ∀ j < n, v.toAF.getD j 0 = g j := by
  obtain ⟨ht, hv⟩ := hr
  cases v <;> simp only [tyOf, Option.some.injEq, reduceCtorEq, Ty.af.injEq] at ht
  rename_i x
  simp only [encV] at hv
  rw [he] at hv
  exact ⟨ht, fun j hj => getD_of_toList hv.symm hj⟩

end Read

/-! ## The template is sound -/

/-- `fixK` leaves `evalM`. -/
theorem fixK_evalM (impl : OpImpl) (ι : Kind) : (impl.fixK ι).evalM = impl.evalM := rfl

/-- **The reserve template is sound** where its cells hold a true child claim: at prototype 0 (whose
ops are `implN4F base ν`'s), every covered `evalM`'s three imports represent its outputs. -/
theorem atImp_rsv {impl : OpImpl} {X : Ext} {π : ℕ} {κ : Kind} {inp : Input} {w : Asg} {ch : List F}
    (hI : π = 0 → ∃ base ν, impl.evalM = (NI4F.implN4F base ν).evalM)
    (hC : π = 0 → RsvCells w ch ∧ N4c.truthChildV NI4F.srcE4 ch) :
    ATImp impl X (AT.rsv X π) κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev _
  have hπ : π = 0 := by
    simp only [AT.rsv, Bool.and_eq_true, beq_iff_eq] at hcov; exact hcov.1
  obtain ⟨base, ν, hM⟩ := hI hπ
  obtain ⟨hcl, hT⟩ := hC hπ
  cases op with
  | evalM t s =>
    obtain ⟨hsel, hinv, -, hrows⟩ := hc
    have h1 := hsel.1
    have hr : ∀ r ∈ rsvRowsT X P cs (.evalM t s), r.Holds w := fun r h => hrows r (by
      simp only [AT.rsv, if_pos hπ]; exact h)
    simp only [rsvRowsT, List.mem_append, List.mem_flatMap] at hr
    have hk : κ ∈ kinds := by cases κ <;> simp [kinds]
    obtain ⟨lt, hst, het⟩ := argRows_ev h1 fun r h => hr r (.inl ⟨κ, hk, .inl h⟩)
    obtain ⟨ls, hss, hes⟩ := argRows_ev h1 fun r h => hr r (.inl ⟨κ, hk, .inr h⟩)
    obtain ⟨l₀, l₁, l₂, ho, e₀, e₁, e₂⟩ := outRows_ev h1 fun r h => hr r (.inr h)
    have rt := hinv.2.2 t; rw [hst] at rt
    have rs := hinv.2.2 s; rw [hss] at rs
    obtain ⟨hτ, hτj⟩ := af_of_rep rt het
    obtain ⟨-, hσj⟩ := af_of_rep rs hes
    have hev' := N4c.evalM_childV (τ := (rd regs t).toAF) (σ := (rd regs s).toAF) base ν hT hτ
      (fun j hj => by rw [hτj j (by omega), Function.comp_apply, tauC, if_pos hj, hcl j (by omega)])
      (fun i hi => by
        rw [hτj (23 + i) (by omega), Function.comp_apply, tauC, if_neg (by omega),
          show 25 + (23 + i) = 48 + i by omega, hcl _ (by omega)])
      (fun j hj => by rw [hσj j hj, Function.comp_apply, sigC, hcl _ (by omega)])
    simp only [evalOp, hM, hev', Res.vals.injEq] at hev
    obtain ⟨rfl, -⟩ := hev
    rw [ho]
    refine .cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ .nil)) <;>
      simp only [List.map_cons, List.map_nil, encV]
    · rw [e₀, hcl 57 (by norm_num)]
    · rw [e₁, hcl 58 (by norm_num)]
    · rw [e₂, hcl 59 (by norm_num)]
  | _ => simp [AT.rsv, isEvalM] at hcov

/-! ## At a node -/

/-- M's `one` cell is `3·2^logM` where the node has a previous node (the reserve's base). -/
theorem oneCell_rsv (κ : NodeKind) (h : κ.hasPrev = true) : κ.oneCell = 3 * 2 ^ κ.dims.logM := by
  cases κ <;> first | exact absurd h (by decide) | decide

/-- `rsvRel` has the reserve's 60 cells. -/
theorem rsvRel_length : rsvRel.length = 60 := rfl

/-- **`PubCellsR4` is `RsvCells` at slot 0's assignment** (a node with a previous node). -/
theorem rsvCells_slot0 {κ : NodeKind} {w : Asg} {ch : List F} (hp : κ.hasPrev = true)
    (h : N4c.PubCellsR4 κ w ch) : RsvCells (slotAsg κ 0 w) ch := by
  intro j hj
  have hπ : protoOf κ 0 = 0 := by simp [protoOf, isPrevSlot, hp]
  unfold N4c.PubCellsR4 at h
  rw [rsvCells, if_pos hp, List.map_map] at h
  subst h
  rw [List.getD_eq_getElem _ _ (by simp [rsvRel_length, hj]), List.getElem_map, slotAsg, hπ, mvC,
    Function.comp_apply, rsvC, List.getD_eq_getElem _ _ (by rw [rsvRel_length]; exact hj),
    oneCell_rsv κ hp]
  congr 1; omega

/-- Prototype `π`'s ask templates with the `input` and the reserve templates beside them. -/
def withRsv (Aq : ℕ → AT) (π : ℕ) : AT := (withInp Aq π).add (AT.rsv (Xof π) π)

/-- **The reserve template at a slot** of a node meeting `StmtN4R`: at slot 0 of a node with a
previous node, the reserve's cells; elsewhere the template covers nothing. -/
theorem atImp_rsv_slot {impl₀ : OpImpl} {base : NodeKind → OpImpl} {κ : NodeKind} {w : Asg}
    {ch : List F} (hR : N4c.PubCellsR4 κ w ch) (hT : N4c.truthChildV NI4F.srcE4 ch) (v : ℕ) (ι : Kind)
    (inp : Input) :
    ATImp (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (AT.rsv (Xof (protoOf κ v)) (protoOf κ v))
      ι inp (slotAsg κ v w) := by
  refine atImp_rsv (ch := ch) (fun h => ⟨base, nodeAt ι, by rw [implP, if_pos h]; rfl⟩) fun h => ⟨?_, hT⟩
  have hp : isPrevSlot κ v = true := by
    by_contra hn; rw [protoOf_seg (by simpa using hn)] at h; exact absurd h one_ne_zero
  simp only [isPrevSlot, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hp, rfl⟩ := hp
  exact rsvCells_slot0 hp hR

/-- **`imp` over `StmtN4R`, with slot 0's `evalM` bound by the reserve**: IMP's `gap4Imp_of_runI`
with the reserve template beside the `input` one. What remains per active slot and selectable
index is the other templates' `ATOk` (`Aq`) and `SlotRunA` over `withRsv Aq`, whose residual
imports exclude the `input` registers and slot 0's `evalM` outputs. -/
theorem gap4Imp_of_rsv {rt : ℕ → RT} {Aq : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {pf : Trace → Proof}
    (hpf : PfHdr pf) (hpv : PfView pf) {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {ch : List F} {b : ℕ}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withRsv Aq) κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 pf) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      ATOk (implP impl₀ base (protoOf κ v) ι) (Xof (protoOf κ v)) (Aq (protoOf κ v)) ι
          (N4c.slotIn (rd4 pf) κ vk c₁ w v) (slotAsg κ v w) ((rd4 pf).slotTr κ v w) ∧
        SlotRunA (rt (protoOf κ v)) (withRsv Aq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 pf) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 pf) κ vk c₁ w v) ((rd4 pf).slotTr κ v w) :=
  gap4Imp_of_runS hT₀ hT hok hpf hpv hfoldR hfoldA hS.1 fun v hv ι hι =>
    ⟨atOk_add (atOk_add (h v hv ι hι).1 (atImp_inp (inpCells_of_rows hpv hpf hS.1 v hv ι hι)))
      (atImp_rsv_slot hS.2.1 hS.2.2 v ι _), (h v hv ι hι).2⟩

/-! ## Controls -/

/-- (+) **The template covers prototype 0's `evalM` only**: not prototype 1's, nor an `evalL`. -/
theorem atRsv_cov (X : Ext) : (AT.rsv X 0).cov (.evalM 1 2) = true ∧ (AT.rsv X 1).cov (.evalM 1 2) = false ∧
    (AT.rsv X 0).cov (.evalL 1 2) = false := ⟨rfl, rfl, rfl⟩

/-- (+) **A component on its own cell costs no row**; (−) another costs one. -/
theorem eqRowIf_ctl (P : Params) : eqRowIf P (Lin.cell 5) 5 = [] ∧ (eqRowIf P (Lin.cell 6) 5).length = 1 := by
  simp [eqRowIf, Lin.cell]

/-- (+) **An operand on its own cells costs no row.** -/
theorem argRows_cells (P : Params) (n : ℕ) (f : ℕ → ℕ) :
    argRows P (some (.af n, (List.range n).map (Lin.cell ∘ f))) n f = [] := by
  rw [argRows, if_pos ⟨rfl, by simp⟩, List.flatMap_eq_nil_iff]
  intro p hp
  rw [List.mem_zipIdx_iff_getElem?] at hp
  rw [List.getElem?_map] at hp
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.1 ha
  rw [List.getElem_range] at hg
  rw [← he, ← hg]; simp [eqRowIf]

/-- The control's compile state: register 0 the row point on `tauC`, register 1 the column point on
`sigC`, the next fresh cell the first output's reserve cell. -/
def csR : CS :=
  ⟨rsvC 57, #[some (.af 32, (List.range 32).map (Lin.cell ∘ tauC)),
    some (.af 25, (List.range 25).map (Lin.cell ∘ sigC))], [], [], [], [], [], 0, [], []⟩

/-- The control's registers: two zero points. -/
def regsR : Array Val := #[.af (Array.replicate 32 0), .af (Array.replicate 25 0)]

/-- An `evalM` returning a false claim's outputs (`X₃[1] = 1`). -/
def implR : OpImpl := { Impl.implC0 with evalM := fun _ _ => (0, 1, 0) }

theorem tauC_ne : ∀ j < 32, tauC j ≠ 0 := by decide
theorem sigC_ne : ∀ j < 25, sigC j ≠ 0 := by decide

theorem map_zero {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j ≠ 0) :
    ((List.range n).map (Lin.cell ∘ f)).map (Lin.ev wCtl) = (Array.replicate n (0 : F)).toList := by
  rw [Array.toList_replicate, List.map_map, List.eq_replicate_iff]
  refine ⟨by simp, fun x hx => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  simp [wCtl, h j (List.mem_range.1 hj)]

/-- (−) **The reserve template needs its cells**: at the layout's own cells its rows are empty, so on
the zero assignment with `one = 1` (`wCtl`) an `evalM` returning `X₃[1] = 1` meets its context, yet
its second output's cell (`0`) does not represent it. `atImp_rsv`'s `RsvCells`/`truthChildV` are
what binds the outputs. -/
theorem atImp_rsv_neg : ¬ ATImp implR noExt (AT.rsv noExt 0) .L32 inpCtl wCtl := by
  intro h
  have hinv : InvK wCtl csR regsR .L32 := by
    have hs : ∀ i, RepS wCtl (csR.slot i) (rd regsR i) := fun i => by
      rcases i with _ | _ | i
      · exact ⟨rfl, by simpa [csR, CS.slot, regsR, rd, encV] using map_zero tauC_ne⟩
      · exact ⟨rfl, by simpa [csR, CS.slot, regsR, rd, encV] using map_zero sigC_ne⟩
      · simp [csR, CS.slot, RepS]
    exact ⟨⟨rfl, hs⟩, fun p hp => by simp [csR] at hp, fun i => by simpa [CS.slotK, csR] using hs i⟩
  have hrows : ∀ r ∈ (AT.rsv noExt 0).rows pCtl csR none (.evalM 0 1) 0, r.Holds wCtl := by
    have e1 : ∀ κ, csR.slotK 0 κ = some (.af 32, (List.range 32).map (Lin.cell ∘ tauC)) := fun κ => rfl
    have e2 : ∀ κ, csR.slotK 1 κ = some (.af 25, (List.range 25).map (Lin.cell ∘ sigC)) := fun κ => rfl
    have e3 : outRows pCtl (stepOut noExt pCtl csR (.evalM 0 1)).slots = [] := by
      simp [stepOut, noExt, opOut, imports, impSlots, Ty.len, CS.cell, csR, outRows, eqRowIf, rsvC, rsvRel]
    simp [AT.rsv, rsvRowsT, e1, e2, e3, argRows_cells]
  have := h pCtl csR none (.evalM 0 1) 0 regsR _ _ rfl ⟨selOk_ctl, hinv, trivial, hrows⟩ rfl rfl
  simp only [implR, stepOut, noExt, Option.getD_none, opOut, imports, impSlots, Ty.len] at this
  simp [List.range_succ, RepS, tyOf, encV, CS.cell, csR, wCtl, rsvC, rsvRel] at this

end N4s
end FR

end G6_FRNodeRsvLink

section G6_FRNodeRows4AskPosF

-- New for `flock-recursive` (PACK-4.4.1 §4.2, §5.2; IMP-RESULT §5.5; SRA-RESULT §6.1; track ASK-P): the
-- folds of the ask templates' rows, arena₁ and the bits into `nodeIRows4`, as theorems.

/-!
# The folds: the node's M rows hold the ask templates' rows, arena₁ and the bits

`FRNodeRows4.arIRows4` puts, in every slot region, arena₁ (`a1Rows4`), the slot prototype's
template rows (`askRowsT`, at `v·2^20 + arR2 + k`: B3's `askIRows4 A κ v arR2` for any template `A`
whose fields are `askTG`'s) and the bits (`bitRows4`), once they fit (`ArFit`). Here:

* **`arFit_of`**: on `one = 1`, the statement's M rows give `ArFit` (else a slot's rejecting row fails).
* **`askRowsX_trail`**: B3's `askRowsX` is `trailRows` at the template's fields; **`askRowsP_eq`**.
* **`askFold`**: `askIRows4 A κ v arR2 ⊆ nodeIRows4 κ` for every template `A` with `askTG`'s fields
  (the hypothesis `hfoldA` of B3's `gap4Imp_of_run`, IMP's `gap4Imp_of_runI`, SRA's `gap4Imp_of_rsv`);
  today's template and its fold are `FRNodeRun4AskT.withImpc_askT`, `askFold_askT` (ASK-T's asks,
  `input`, the reserve, IMPC's import classes).
* **`a1_slot`** (the arena₁ bridge, prototype frame): at slot `v`'s assignment, arena₁'s cell
  `π·2^20 + arA1 + e` is the H cell of the slot's stream element `e`; **`bit_slot`**: the bits' cells
  are bits.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4

/-! ## Templates and generators -/

/-- **B3's ask template of a generator.** -/
def _root_.FR.Rev4.TG.toAT (G : TG) : AT := ⟨G.cov, G.rows⟩

/-- **B3's `askRowsX` is `trailRows`** at the template's fields. -/
theorem askRowsX_trail (X : Ext) (P : Params) (A : AT) : ∀ (cs : CS) (pre : Option Op) (k : ℕ) (ops : List Op),
    askRowsX X P A cs pre k ops = trailRows X P ⟨A.cov, A.rows⟩ cs pre k ops
  | _, _, _, [] => rfl
  | cs, pre, k, op :: ops => by
    rw [askRowsX_cons, trailRows, askRowsX_trail X P A _ _ _ ops]

/-- **A template with `askTG`'s fields has the node's template rows.** -/
theorem askRowsP_eq {A : AT} {π : ℕ} (hc : A.cov = (askTG π).cov) (hr : A.rows = (askTG π).rows) :
    askRowsP A π = askRowsT π := by
  rw [askRowsP, askRowsX_trail, askRowsT, hc, hr]; rfl

/-- **The node's ask template** (ASK-T): the ask generator `askTGT` as B3's template. -/
def askAq (π : ℕ) : AT := (askTGT (Xof π) π).toAT

/-! ## The fit from the statement's rows -/

/-- **On `one = 1`, the M rows give `ArFit`** (else slot 0's arena rows are one rejecting row). -/
theorem arFit_of {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ArFit := by
  by_contra hA
  have hF := protoFit_of hone hE
  have hv : 0 < κ.vslots := by cases κ <;> decide
  have hm : (arRej 0, rejR κ) ∈ nodeIRows4 κ := mem_node_ar hF hv (by
    unfold arIRows4; rw [if_neg hA]; exact List.mem_singleton_self _)
  have := hE _ hm
  simp [rejR, Row.Holds, Lin.ev, Lin.cell, hone] at this

/-! ## The folds -/

theorem mapC_comp (f g : ℕ → ℕ) (l : Lin) : mapC f (mapC g l) = mapC (f ∘ g) l := by
  simp [mapC, List.map_map, Function.comp_def]

theorem rowMapC_comp (f g : ℕ → ℕ) (r : Row) : rowMapC f (rowMapC g r) = rowMapC (f ∘ g) r := by
  simp only [rowMapC, mapC_comp]

/-- **The ask templates' rows are folded** (`hfoldA` at `b = arR2`), for every template with the
node generator's fields. -/
theorem askFold {A : ℕ → AT} (hA : ∀ π ≤ 1, (A π).cov = (askTG π).cov ∧ (A π).rows = (askTG π).rows)
    {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ askIRows4 A κ v arR2, p ∈ nodeIRows4 κ := by
  intro v hv p hp
  have hF := protoFit_of hone hE
  have hAr := arFit_of hone hE
  refine mem_node_ar hF hv ?_
  have hπ := protoOf_le' κ v
  obtain ⟨hc, hr⟩ := hA _ hπ
  unfold askIRows4 at hp
  rw [askRowsP_eq hc hr] at hp
  unfold arIRows4
  rw [if_pos hAr]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  obtain ⟨⟨r, k⟩, hk, rfl⟩ := List.mem_map.1 hp
  simp only [absRows4, mvRows, askPI, List.map_map, List.mem_map, Function.comp_def]
  refine ⟨(r, k), hk, ?_⟩
  simp only [rowMapC_comp, Prod.mk.injEq]
  refine ⟨by simp only [mvC]; omega, rfl⟩

/-! ## Arena₁ and the bits at a slot's assignment (the prototype frame) -/

/-- **Arena₁'s rows hold** at slot `v` (absolute cells). -/
theorem a1_hold {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w)
    {v : ℕ} (hv : v < κ.vslots) : ∀ p ∈ a1Rows4 κ v (slotB0 κ v), p.2.Holds w := by
  intro p hp
  refine hE p (mem_node_ar (protoFit_of hone hE) hv ?_)
  unfold arIRows4; rw [if_pos (arFit_of hone hE)]
  exact List.mem_append_left _ (List.mem_append_left _ hp)

/-- **The bits' rows hold** at slot `v`. -/
theorem bit_hold {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w)
    {v : ℕ} (hv : v < κ.vslots) : ∀ p ∈ bitRows4 κ v, p.2.Holds w := by
  intro p hp
  refine hE p (mem_node_ar (protoFit_of hone hE) hv ?_)
  unfold arIRows4; rw [if_pos (arFit_of hone hE)]
  exact List.mem_append_right _ hp

/-- A prototype-frame cell of region `π = protoOf κ v` at slot `v`'s assignment. -/
theorem slotAsg_frame (κ : NodeKind) (v : ℕ) (w : Asg) (c : ℕ) :
    slotAsg κ v w (protoOf κ v * slotM4 + c) = w (κ.oneCell + v * slotM4 + c) := by
  simp only [slotAsg, mvC]
  congr 1; omega

/-- **The arena₁ bridge in the prototype frame**: at slot `v`'s assignment, arena₁'s cell
`π·2^20 + arA1 + e` (`π` the slot's prototype, `e < arN`) is the H cell of the slot's stream element `e`
(`sCell (slotB0 κ v) e`). -/
theorem a1_slot {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w)
    {v : ℕ} (hv : v < κ.vslots) {e : ℕ} (he : e < arN) :
    slotAsg κ v w (protoOf κ v * slotM4 + arA1 + e) = w (sCell (slotB0 κ v) e) := by
  rw [Nat.add_assoc, slotAsg_frame, ← Nat.add_assoc]
  exact a1_cells4 hone (a1_hold hone hE hv) he

/-- **The bits' cells are bits** at slot `v`'s assignment (prototype frame `π·2^20 + arBt + j`). -/
theorem bit_slot {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w)
    {v : ℕ} (hv : v < κ.vslots) {j : ℕ} (hj : j < arNb) :
    slotAsg κ v w (protoOf κ v * slotM4 + arBt + j) = 0 ∨ slotAsg κ v w (protoOf κ v * slotM4 + arBt + j) = 1 := by
  rw [Nat.add_assoc, slotAsg_frame, ← Nat.add_assoc]
  exact bit_cells4 (bit_hold hone hE hv) hj

/-! ## Controls -/

/-- (−) **`ArFit` is load-bearing**: without it slot `σ`'s arena rows are the rejecting row, which no
assignment with `one = 1` meets; (+) with it they are arena₁'s, the template rows and the bits. -/
theorem arIRows4_ctl (κ : NodeKind) (σ : ℕ) (w : Asg) (hone : w κ.oneCell = 1) :
    (¬ ArFit → ¬ ∀ p ∈ arIRows4 κ σ, p.2.Holds w) ∧
      (ArFit → arIRows4 κ σ = a1Rows4 κ σ (slotB0 κ σ) ++
        absRows4 κ (mvRows (protoOf κ σ) σ (askPI (protoOf κ σ))) ++ bitRows4 κ σ) := by
  refine ⟨fun hA h => ?_, fun hA => by unfold arIRows4; rw [if_pos hA]⟩
  unfold arIRows4 at h; rw [if_neg hA] at h
  have := h _ (List.mem_singleton_self _)
  simp [rejR, Row.Holds, Lin.ev, Lin.cell, hone] at this

end N4s
end FR

end G6_FRNodeRows4AskPosF

section G6_FRNodeRows4AskPos

-- New for `flock-recursive` (PACK-4.4.1 §4.2–§5.2; IMP-RESULT §5.2; track ASK-P): the reader's
-- positional spec and the element alignment of every item, at revision 4.4.1's format.

/-!
# Where each trace entry sits: the reader's positional spec and the element alignment

A slot's trace (`slotTr4`, the reader `rd4`) is `seq4`'s items read off its signed child's stream
(`chainBytes4`) from the slot's segment start `1 + i·strideB` (`segIx`, R-A′'s spacers). Here:

* **`slotTr4_getElem?`** (the reader's positional spec): entry `k` is item `k` read at the stream
  offset `1 + i·strideB + itOff k`, `itOff k` the prefix sum of the items' stream lengths
  (`readItems_getElem?` for any item list).
* **`entryAt_qbyte`**, **`entryAt_abyte`**: an entry's query byte `j` and answer byte `j` are stream
  bytes `o + 8 + j` and `o + 8 + qlen + j`.
* **`slot_byte`** (the H bridge at an active slot): stream byte `i·strideB + x` of the slot's segment
  is byte `x mod 16` of the H cell `sCell (slotB0 κ v) (x / 16)` (outside the segment's last block).
* **The alignment** (`itOff_al`, `ans_al`, `itOff_le`): item `k ≥ 1` starts on an element boundary
  (`1 + itOff k ≡ 0 mod 16`), every answer is two whole elements (`1 + itOff k + 8 + qlen ≡ 0`), and
  items end inside the segment. **`itE k`**/**`ansE k`**: item `k`'s first element and its answer's.
* **`slot_ans`** / **`slot_ansA`**: entry `k`'s answer halves are the H cells (and the arena₁ cells in
  the prototype frame) of elements `ansE k`, `ansE k + 1`; **`slot_qbyte`** / **`slot_qelem`**: its query
  bytes are those cells' bytes, a whole 16-byte query window an element (`F.ofBytes`).

Only the last item's answer lies in the segment's last block (`last_item`), which may be an
aggregate's candidate final block: the statements exclude it by `1 + itOff k + slen + 64 ≤ segB`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The reader's positional spec -/

/-- **Entry `k` of `readItems`** is item `k` read at the prefix sum of the items' stream lengths. -/
theorem readItems_getElem? (B : List UInt8) : ∀ (its : List Item) (o k : ℕ),
    (Read.readItems B o its)[k]? = (its[k]?).map (Read.entryAt B (o + ((its.take k).map Item.slen).sum))
  | [], _, _ => rfl
  | it :: its, o, 0 => by simp [Read.readItems]
  | it :: its, o, k + 1 => by
    rw [Read.readItems, List.getElem?_cons_succ, readItems_getElem? B its, List.getElem?_cons_succ,
      List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **Item `k`'s offset in a segment's trace** (bytes after the trace's first byte): the prefix sum of
`seq4`'s items' stream lengths. -/
def itOff (k : ℕ) : ℕ := (((itemsOf seq4).take k).map Item.slen).sum

/-- Item `k` of `seq4` (the seed past the end). -/
def itAt (k : ℕ) : Item := (itemsOf seq4).getD k .seed

/-- Slot `v`'s signed child (whose stream it reads). -/
def slotSg (κ : NodeKind) (v : ℕ) : ℕ := if isPrevSlot κ v then 0 else N4c.aggChild κ (slotA κ v)

/-- Slot `v`'s stream's segment count (the reader's). -/
noncomputable def slotK (κ : NodeKind) (v : ℕ) (w : Asg) : ℕ := if isPrevSlot κ v then 0 else kAct κ (slotA κ v) w

/-- **Slot `v`'s stream** (`chainBytes4` of its signed child). -/
noncomputable def slotStr (κ : NodeKind) (v : ℕ) (w : Asg) : List UInt8 :=
  N4c.chainBytes4 κ (slotSg κ v) (slotK κ v w) w

theorem slotTr4_seg (κ : NodeKind) (v : ℕ) (w : Asg) :
    slotTr4 κ v w = segTr κ (slotSg κ v) (slotK κ v w) (segIx κ v) w := by
  unfold slotTr4 slotSg slotK segIx; split_ifs <;> rfl

/-- **The reader's positional spec**: slot `v`'s entry `k` is item `k` read off the slot's stream at
`1 + i·strideB + itOff k` (`i = segIx κ v`). -/
theorem slotTr4_getElem? (κ : NodeKind) (v : ℕ) (w : Asg) (k : ℕ) :
    (slotTr4 κ v w)[k]? =
      ((itemsOf seq4)[k]?).map (Read.entryAt (slotStr κ v w) (1 + segIx κ v * N4c.strideB + itOff k)) := by
  rw [slotTr4_seg, segTr, readItems_getElem?]; rfl

/-! ## An entry's bytes -/

/-- **An entry's query byte `j`** is stream byte `o + 8 + j` (inside the stream). -/
theorem entryAt_qbyte (B : List UInt8) (o : ℕ) (it : Item) {j : ℕ} (hj : j < it.qlen)
    (hB : o + 8 + it.qlen ≤ B.length) : byteAt (Read.entryAt B o it).1 j = B.getD (o + 8 + j) 0 := by
  have hs : ((B.drop (o + 8)).take it.qlen).length = it.qlen := by simp; omega
  rw [Read.entryAt]
  dsimp only
  rw [byteAt_mk, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

/-- **An entry's answer byte `j`** is stream byte `o + 8 + qlen + j`. -/
theorem entryAt_abyte (B : List UInt8) (o : ℕ) (it : Item) (j : ℕ) (hj : j < 32) :
    (Read.entryAt B o it).2[j] = B.getD (o + 8 + it.qlen + j) 0 := by
  simp [Read.entryAt]

/-! ## The stream's bytes are H cells (an active slot) -/

/-- **An active slot is the previous node's or an active sub-slot** (the reader's `k`). -/
theorem active_cases {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) :
    (κ.hasPrev = true ∧ v = 0) ∨ ∃ a < N4c.nAgg κ, ∃ i < kAct κ a w, v = N4c.sub κ a i := by
  rcases hv with h | ⟨a, ha, i, hi, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ha, i, by rwa [kA_rd4 pf κ ha] at hi, rfl⟩

theorem isAgg_aggChild (κ : NodeKind) (a : ℕ) : N4c.isAgg κ (N4c.aggChild κ a) = true := by
  cases κ <;> simp [N4c.isAgg, N4c.aggChild, NodeKind.hasPrev]

/-- **Stream byte `i·strideB + x` of an active slot's segment** (outside the segment's last block,
`16·⌊x/16⌋ + 80 ≤ segB`) is byte `x mod 16` of the H cell of element `⌊x/16⌋` (`sCell (slotB0 κ v) ·`). -/
theorem slot_byte {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {x : ℕ} (hx : 16 * (x / 16) + 80 ≤ N4c.segB) :
    (slotStr κ v w).getD (segIx κ v * N4c.strideB + x) 0 =
      (F.toBytes (w (sCell (slotB0 κ v) (x / 16))))[x % 16]'(Nat.mod_lt _ (by norm_num)) := by
  have hx' : x = 16 * (x / 16) + x % 16 := (Nat.div_add_mod x 16).symm
  rcases active_cases hv with ⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · have h0 : isPrevSlot κ 0 = true := by simp [isPrevSlot, hp]
    simp only [slotStr, slotSg, slotK, segIx, slotB0, h0, if_true, Nat.zero_mul, Nat.zero_add]
    conv_lhs => rw [hx']
    exact seg0_elem w (fun h => by simp [N4c.isAgg, hp] at h) (Nat.mod_lt _ (by norm_num)) hx
  · have hk := kAct_le κ a w
    obtain ⟨-, hsi, hps, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi hk)
    have hsa := slotA_sub κ ha (lt_of_lt_of_le hi hk)
    have hag : aggSlot κ (N4c.sub κ a i) = slotA κ (N4c.sub κ a i) := by
      unfold aggSlot slotA; rfl
    simp only [slotStr, slotSg, slotK, segIx, slotB0, hps, if_false, Bool.false_eq_true, hsi, hsa, hag]
    rw [show i * N4c.strideB + x = i * N4c.strideB + 16 * (x / 16) + x % 16 by omega]
    exact segi_elem w (isAgg_aggChild κ a) hi (Nat.mod_lt _ (by norm_num)) hx

/-! ## The alignment -/

theorem sum_mod16 : ∀ l : List ℕ, (∀ x ∈ l, x % 16 = 0) → l.sum % 16 = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [List.sum_cons, Nat.add_mod, h x List.mem_cons_self,
      sum_mod16 l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **Every item after the seed starts on an element boundary** (`1 + itOff k ≡ 0 mod 16`). -/
theorem itOff_al {k : ℕ} (hk : 1 ≤ k) : (1 + itOff k) % 16 = 0 := by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hs := sum_mod16 ((rest.take j).map Item.slen) fun x hx => by
    obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hx
    exact (hal it (List.mem_of_mem_take hit)).1
  rw [itOff, hr, List.take_succ_cons, List.map_cons, List.sum_cons]
  have : Item.slen .seed = 159 := rfl
  omega

/-- **Every answer is two whole elements**: `1 + itOff k + 8 + qlen ≡ 0 (mod 16)`. -/
theorem ans_al {k : ℕ} (hk : k < (itemsOf seq4).length) : (1 + itOff k + 8 + (itAt k).qlen) % 16 = 0 := by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [itOff, itAt, hr, List.take_zero, List.map_nil, List.sum_nil, List.getD_cons_zero]; rfl
  · have h1 := itOff_al hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j < rest.length := by rw [hr] at hk; simpa using hk
    have hit : itAt (j + 1) = rest[j] := by simp [itAt, hr, List.getD_eq_getElem?_getD, hj]
    have := (hal rest[j] (List.getElem_mem hj)).1
    rw [hit]; unfold Item.slen at this; omega

/-- **Every item ends inside the segment**: `1 + itOff k + slen ≤ segB`. -/
theorem itOff_le {k : ℕ} (hk : k < (itemsOf seq4).length) : 1 + itOff k + (itAt k).slen ≤ N4c.segB := by
  have h := slenL_seq4
  have hk' : itAt k = (itemsOf seq4)[k] := by simp [itAt, List.getD_eq_getElem?_getD, hk]
  have e : itOff k + (itAt k).slen = (((itemsOf seq4).take (k + 1)).map Item.slen).sum := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.sum_append,
      hk']; simp [itOff]
  have le : (((itemsOf seq4).take (k + 1)).map Item.slen).sum ≤ slenL (itemsOf seq4) := by
    rw [slenL]
    conv_rhs => rw [← List.take_append_drop (k + 1) (itemsOf seq4)]
    rw [List.map_append, List.sum_append]; omega
  omega

/-- **Item `k`'s first element** in its segment (for `k ≥ 1` exactly: `itOff_al`). -/
def itE (k : ℕ) : ℕ := (1 + itOff k) / 16

/-- **Item `k`'s answer's first element** (the answer is elements `ansE k`, `ansE k + 1`: `ans_al`). -/
def ansE (k : ℕ) : ℕ := (1 + itOff k + 8 + (itAt k).qlen) / 16

/-! ## The composites: an entry's answer and query at an active slot -/

theorem itAt_eq {k : ℕ} (hk : k < (itemsOf seq4).length) : (itemsOf seq4)[k]? = some (itAt k) := by
  simp [itAt, List.getD_eq_getElem?_getD, hk]

theorem slotStr_len {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) :
    segIx κ v * N4c.strideB + N4c.segB ≤ (slotStr κ v w).length := by
  have hL : ∀ σ k, (N4c.chainBytes4 κ σ k w).length = N4c.streamB κ σ k := fun σ k => by
    simp [N4c.chainBytes4, Stream.streamBytes]
  obtain ⟨h1, h2, h3⟩ := N4c.strideB_eq
  rcases active_cases hv with ⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · have h0 : isPrevSlot κ 0 = true := by simp [isPrevSlot, hp]
    simp only [slotStr, slotSg, slotK, segIx, h0, if_true, Nat.zero_mul, Nat.zero_add, hL]
    exact (stream_ge (fun h => by simp [N4c.isAgg, hp] at h)).1
  · have hk := kAct_le κ a w
    obtain ⟨-, hsi, hps, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi hk)
    have hsa := slotA_sub κ ha (lt_of_lt_of_le hi hk)
    simp only [slotStr, slotSg, slotK, segIx, hps, if_false, Bool.false_eq_true, hsi, hsa, hL, N4c.streamB,
      isAgg_aggChild, if_true]
    obtain ⟨-, -, h6⟩ := N4c.aggB_blocks (k := kAct κ a w) (by omega)
    have : i * N4c.strideB + N4c.strideB ≤ kAct κ a w * N4c.strideB := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    omega

/-- **Entry `k`'s answer at an active slot** (not the last block's item): its halves are the H cells of
elements `ansE k`, `ansE k + 1` of the slot's segment. -/
theorem slot_ans {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) :
    dlo e.2 = w (sCell (slotB0 κ v) (ansE k)) ∧ dhi e.2 = w (sCell (slotB0 κ v) (ansE k + 1)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hal := ans_al hk
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  have key : ∀ (h : ℕ) (r : Fin 16) (_hh : h < 2),
      (Read.entryAt (slotStr κ v w) (1 + segIx κ v * N4c.strideB + itOff k) (itAt k)).2[16 * h + r.1]'(by omega) =
        (F.toBytes (w (sCell (slotB0 κ v) (ansE k + h))))[r.1] := fun h r hh => by
    rw [entryAt_abyte _ _ _ (16 * h + r.1) (by omega)]
    rw [show 1 + segIx κ v * N4c.strideB + itOff k + 8 + (itAt k).qlen + (16 * h + r.1) =
        segIx κ v * N4c.strideB + (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) by omega,
      slot_byte hv (by have := r.2; unfold ansE at *; omega)]
    have e1 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) / 16 = ansE k + h := by unfold ansE; omega
    have e2 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) % 16 = r.1 := by omega
    simp only [e1, e2]
  constructor
  · rw [dlo, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    have := key 0 ⟨r, hr⟩ (by norm_num)
    simpa using this
  · rw [dhi, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k + 1)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    exact key 1 ⟨r, hr⟩ (by norm_num)

/-- **Entry `k`'s query byte `j`** at an active slot (not the last block's item): byte `(o + j) mod 16`
of the H cell of element `⌊(o + j)/16⌋`, `o = 1 + itOff k + 8`. -/
theorem slot_qbyte {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) {j : ℕ} (hj : j < (itAt k).qlen) :
    byteAt e.1 j = (F.toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16))))[(1 + itOff k + 8 + j) % 16]'(
      Nat.mod_lt _ (by norm_num)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  have hL := slotStr_len hv
  rw [entryAt_qbyte _ _ _ hj (by omega),
    show 1 + segIx κ v * N4c.strideB + itOff k + 8 + j = segIx κ v * N4c.strideB + (1 + itOff k + 8 + j) by omega,
    slot_byte hv (by omega)]

/-- **A whole 16-byte query window is an element**: if `1 + itOff k + 8 + j ≡ 0 (mod 16)` and the window
lies in the query, the window's `F` value is the H cell. -/
theorem slot_qelem {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) {j : ℕ} (hj : j + 16 ≤ (itAt k).qlen)
    (hal : (1 + itOff k + 8 + j) % 16 = 0) :
    F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (j + r)) = w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16)) := by
  rw [← F.ofBytes_toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16)))]
  refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
  rw [Vector.getElem_ofFn, slot_qbyte hv hk he hb (by omega)]
  have e1 : (1 + itOff k + 8 + (j + r)) / 16 = (1 + itOff k + 8 + j) / 16 := by omega
  have e2 : (1 + itOff k + 8 + (j + r)) % 16 = r := by omega
  simp only [e1, e2]

/-! ## In the prototype frame: the arena₁ cells -/

/-- An item's elements lie in arena₁ (`arN = 4·cLen` elements: the segment's). -/
theorem elem_arN {x : ℕ} (hx : 16 * x + 16 ≤ N4c.segB) : x < arN := by
  have := (arConsts).2.2.2.2.2
  have h3 := N4c.strideB_eq.2.2
  omega

/-- **Entry `k`'s answer in the prototype frame**: its halves are arena₁'s cells
`π·2^20 + arA1 + ansE k (+ 1)` at the slot's assignment (`π = protoOf κ v`). -/
theorem slot_ansA {pf : Trace → Proof} {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) (hvs : v < κ.vslots)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) :
    dlo e.2 = slotAsg κ v w (protoOf κ v * slotM4 + arA1 + ansE k) ∧
      dhi e.2 = slotAsg κ v w (protoOf κ v * slotM4 + arA1 + (ansE k + 1)) := by
  obtain ⟨h1, h2⟩ := slot_ans hv hk he hb
  have hal := ans_al hk
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  rw [a1_slot hone hE hvs (elem_arN (x := ansE k) (by unfold ansE; omega)),
    a1_slot hone hE hvs (elem_arN (x := ansE k + 1) (by unfold ansE; omega))]
  exact ⟨h1, h2⟩

/-- **A query element in the prototype frame**: arena₁'s cell `π·2^20 + arA1 + ⌊(o + j)/16⌋`. -/
theorem slot_qelemA {pf : Trace → Proof} {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1)
    (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v) (hvs : v < κ.vslots)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    (hb : 1 + itOff k + (itAt k).slen + 64 ≤ N4c.segB) {j : ℕ} (hj : j + 16 ≤ (itAt k).qlen)
    (hal : (1 + itOff k + 8 + j) % 16 = 0) :
    F.ofBytes (Vector.ofFn fun r : Fin 16 => byteAt e.1 (j + r)) =
      slotAsg κ v w (protoOf κ v * slotM4 + arA1 + (1 + itOff k + 8 + j) / 16) := by
  have hsl : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl
  rw [slot_qelem hv hk he hb hj hal, a1_slot hone hE hvs (elem_arN (by omega))]

/-! ## Controls -/

/-- (+) The reader's spec on a toy stream: entry `1` of two `squeeze` items read from offset `1` is read
at `1 + 80` (one `squeeze` is 80 bytes), (−) not at `1`. -/
theorem readItems_ctl :
    ((Read.readItems (List.replicate 200 7) 1 [.squeeze, .squeeze])[1]?).isSome ∧
      ([Item.squeeze, .squeeze].take 1).map Item.slen = [80] ∧ ([Item.squeeze].map Item.slen).sum ≠ 0 := by
  decide

/-- (+) The seed's answer is element-aligned (`1 + 8 + 119 = 128`); (−) its query is not (`1 + 8 ≢ 0`). -/
theorem seed_al_ctl : (1 + 0 + 8 + Item.qlen .seed) % 16 = 0 ∧ (1 + 0 + 8) % 16 ≠ 0 := by decide

end N4s
end FR

end G6_FRNodeRows4AskPos

section G6_FRNodeRows4AskPosR

-- New for `flock-recursive` (PACK-4.4.1 §4.3, A.5; IMP-RESULT §5.2; SRA-RESULT §6.3; track ASK-P):
-- `reassemble4`'s positional spec, field by field and phase by phase.

/-!
# Which trace bytes a proof field's bytes are (`reassemble4`'s positional spec)

The generators read phase `n`'s bytes of field `f` at the absolute offset
`fieldOffOf S f + phaseOffOf S n f` (`FRVIR4.genPhase4`'s `o f`). `reassemble4 S tr` lays the fields
out in order, each field phase by phase (`ctbs4`), so:

* **`reassemble4_byte`**: byte `fieldOffOf S f + phaseOffOf S n f + j` of the proof is byte `j` of
  phase `n`'s contribution `ctb4 … (phIx S n) (phAns …) sh f`, `phIx S n` the phase's first item.
* **Per shape** (`ctb4_seed`, `ctb4_absorb`, `ctb4_uni`, `ctb4_rounds`, `ctb4_cols`, `ctb4_sibs`): the
  contribution's byte is a query byte of an item of the phase (`hdr` from the seed's byte 71, a
  message from byte 40 of its absorb, a column from byte 8 of its column query), or a sibling half.
* **`itemsOf_phIx`**: item `phIx S n + q` of `itemsOf S` is the phase's item `q`.
* **The slot's proof** (`slotπ_byte`): at slot `v`, `rd4 pf4`'s proof is `pf4` of the slot's trace.
  **`slot_pfAbsorb`**: at an active slot, an absorb phase's message byte `j` is byte
  `(o + 48 + j) mod 16` of the H cell of element `⌊(o + 48 + j)/16⌋` of the slot's segment
  (`o = 1 + itOff (phIx seq4 n)`), outside the last block.
-/

namespace FR
namespace X
open RecursionFast FR.Snd FR.Rev4

/-! ## Lists of blocks -/

theorem getD_flatMap_const {α : Type} (g : α → List UInt8) (c : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, (g x).length = c) → ∀ {p t : ℕ} (hp : p < l.length), t < c →
      (l.flatMap g).getD (p * c + t) 0 = (g l[p]).getD t 0
  | [], _, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | x :: l, h, p, t, hp, ht => by
    rw [List.flatMap_cons]
    rcases p with _ | p
    · rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by rw [h x List.mem_cons_self]; exact ht)]; rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [h x List.mem_cons_self]; nlinarith), h x List.mem_cons_self,
        show (p + 1) * c + t - c = p * c + t by rw [Nat.add_one_mul]; omega,
        getD_flatMap_const g c l (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by simpa using hp) ht]
      rfl

theorem getD_flatMap_range (g : ℕ → List UInt8) : ∀ (N f o : ℕ), f < N → o < (g f).length →
    ((List.range N).flatMap g).getD (((List.range f).map fun i => (g i).length).sum + o) 0 = (g f).getD o 0
  | 0, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | N + 1, f, o, hf, ho => by
    rw [List.range_succ, List.flatMap_append]
    have hl : ((List.range N).flatMap g).length = ((List.range N).map fun i => (g i).length).sum := by
      simp [List.length_flatMap]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | rfl
    · have hle : ((List.range f).map fun i => (g i).length).sum + o < ((List.range N).flatMap g).length := by
        rw [hl]
        obtain ⟨d, rfl⟩ : ∃ d, N = f + 1 + d := ⟨N - f - 1, by omega⟩
        rw [List.range_add, List.map_append, List.sum_append, List.range_succ, List.map_append, List.sum_append]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
      rw [List.getD_append _ _ _ _ hle, getD_flatMap_range g N f o hf ho]
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
      simp

/-! ## The phases -/

/-- The position answers after `n` phases (`ctbs4`'s threading of `ansOf4`). -/
def ansN (S : Seq) (a : Array (ByteArray × Digest)) : ℕ → List Digest → List Sh → ℕ → List Digest
  | _, ans, _, 0 => ans
  | _, ans, [], _ + 1 => ans
  | ix, ans, sh :: shs, n + 1 => ansN S a (ix + (sh.itemsL S.lv).length) (ansOf4 a ix ans sh) shs n

/-- **Phase `n`'s contribution in `ctbs4`**: byte `Σ_{q<n} |sh_q|_f + j` is its byte `j`. -/
theorem ctbs4_getD (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (f : ℕ) :
    ∀ (shs : List Sh) (ix : ℕ) (ans : List Digest) (n j : ℕ) (hn : n < shs.length),
      j < shs[n].bytesToL S.lv f →
      (ctbs4 S m a ix ans shs f).getD (((shs.take n).map fun sh => sh.bytesToL S.lv f).sum + j) 0 =
        (ctb4 S m a (ix + ((shs.take n).map fun sh => (sh.itemsL S.lv).length).sum) (ansN S a ix ans shs n)
          shs[n] f).getD j 0
  | [], _, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | sh :: shs, ix, ans, 0, j, _, hj => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero, ansN, ctbs4,
      List.getElem_cons_zero]
    rw [List.getD_append _ _ _ _ (by rw [ctb4_length]; exact hj)]
  | sh :: shs, ix, ans, n + 1, j, hn, hj => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, ansN, ctbs4, List.getElem_cons_succ] at hj ⊢
    rw [List.getD_append_right _ _ _ _ (by rw [ctb4_length]; omega), ctb4_length,
      show sh.bytesToL S.lv f + ((shs.take n).map fun sh => sh.bytesToL S.lv f).sum + j -
        sh.bytesToL S.lv f = ((shs.take n).map fun sh => sh.bytesToL S.lv f).sum + j by omega,
      ctbs4_getD S m a f shs _ _ n j (by simpa using hn) hj, Nat.add_assoc]

/-- **Phase `n`'s first item** (index in `itemsOf S`). -/
def phIx (S : Seq) (n : ℕ) : ℕ := (((phasesOf S).take n).map fun p => (p.2.itemsL S.lv).length).sum

/-- The position answers phase `n` reads (the trace `a`'s). -/
def phAns (S : Seq) (a : Array (ByteArray × Digest)) (n : ℕ) : List Digest :=
  ansN S a 0 [] ((phasesOf S).map Prod.snd) n

theorem fieldSize_ctbs4 (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (f : ℕ) :
    (ctbs4 S m a 0 [] ((phasesOf S).map Prod.snd) f).length = fieldSizeOf S f := by
  rw [ctbs4_length, List.map_map]; rfl

theorem take_sum_le {α : Type} (F : α → ℕ) : ∀ (l : List α) (n : ℕ) (hn : n < l.length),
    ((l.take n).map F).sum + F l[n] ≤ (l.map F).sum
  | [], _, hn => absurd hn (Nat.not_lt_zero _)
  | x :: l, 0, _ => by simp
  | x :: l, n + 1, hn => by
    have := take_sum_le F l n (by simpa using hn)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-- **`reassemble4`'s positional spec**: byte `j` of phase `n`'s part of field `f` (the generators'
absolute offset `fieldOffOf S f + phaseOffOf S n f + j`) is byte `j` of the phase's contribution. -/
theorem reassemble4_byte (S : Seq) (tr : Trace) {f n j : ℕ} (hf : f < nFields4) (hn : n < (phasesOf S).length)
    (hj : j < ((phasesOf S)[n]).2.bytesToL S.lv f) :
    byteAt (reassemble4 S tr) (fieldOffOf S f + phaseOffOf S n f + j) =
      (ctb4 S (trM4 tr.toArray) tr.toArray (phIx S n) (phAns S tr.toArray n) ((phasesOf S)[n]).2 f).getD j 0 := by
  have hn' : n < ((phasesOf S).map Prod.snd).length := by simpa using hn
  have hm : ((phasesOf S).map Prod.snd)[n] = ((phasesOf S)[n]).2 := by simp
  have hpo : phaseOffOf S n f = ((((phasesOf S).map Prod.snd).take n).map fun sh => sh.bytesToL S.lv f).sum := by
    rw [phaseOffOf, ← List.map_take, List.map_map]; rfl
  have hpi : phIx S n = 0 + ((((phasesOf S).map Prod.snd).take n).map fun sh => (sh.itemsL S.lv).length).sum := by
    rw [phIx, ← List.map_take, List.map_map, Nat.zero_add]; rfl
  have hfo : fieldOffOf S f = ((List.range f).map fun i =>
      (ctbs4 S (trM4 tr.toArray) tr.toArray 0 [] ((phasesOf S).map Prod.snd) i).length).sum := by
    rw [fieldOffOf]
    exact congrArg List.sum (List.map_congr_left fun i _ => (fieldSize_ctbs4 S _ _ i).symm)
  have hlt : phaseOffOf S n f + j <
      (ctbs4 S (trM4 tr.toArray) tr.toArray 0 [] ((phasesOf S).map Prod.snd) f).length := by
    rw [ctbs4_length, hpo]
    have := take_sum_le (fun sh : Sh => sh.bytesToL S.lv f) _ n hn'
    rw [hm] at this; omega
  rw [reassemble4, N4s.byteAt_mk, hfo, Nat.add_assoc,
    getD_flatMap_range (fun i => ctbs4 S (trM4 tr.toArray) tr.toArray 0 [] ((phasesOf S).map Prod.snd) i)
      nFields4 f _ hf hlt,
    hpo, ctbs4_getD S _ _ f _ 0 [] n j hn' (by rw [hm]; exact hj), hm, ← hpi]
  rfl

/-! ## Each shape's contribution -/

section Shapes
variable (S : Seq) (m : ℕ) (a : Array (ByteArray × Digest)) (ix : ℕ) (ans : List Digest)

theorem qB4_getD {j o n t : ℕ} (ht : t < n) : (qB4 a j o n).getD t 0 = byteAt (a.getD j (ByteArray.empty, 0)).1 (o + t) := by
  rw [qB4, qBytes]; exact fitL_extract_getDj _ _ _ ht

/-- `hdr`: the seed query's bytes from 71. -/
theorem ctb4_seed {j : ℕ} (hj : j < 48) :
    (ctb4 S m a ix ans .seed fHdr).getD j 0 = byteAt (a.getD ix (ByteArray.empty, 0)).1 (71 + j) := by
  rw [ctb4, if_pos rfl, qB4_getD _ hj]

/-- An absorb phase: its message, the query's bytes from 40 (`tag ‖ st ‖ msg`). -/
theorem ctb4_absorb {g len j : ℕ} (hj : j < len) :
    (ctb4 S m a ix ans (.absorb g len) g).getD j 0 = byteAt (a.getD ix (ByteArray.empty, 0)).1 (40 + j) := by
  rw [ctb4, if_pos rfl, qB4_getD _ hj]

/-- A univariate phase: its absorb's message. -/
theorem ctb4_uni {g j : ℕ} (hj : j < uniBytes) :
    (ctb4 S m a ix ans (.uni g) g).getD j 0 = byteAt (a.getD ix (ByteArray.empty, 0)).1 (40 + j) := by
  rw [ctb4, if_pos rfl, qB4_getD _ hj]

/-- A rounds phase: round `p`'s message, its absorb (item `2p`) from byte 40. -/
theorem ctb4_rounds {g n d : ℕ} {inK : Bool} {p t : ℕ} (hp : p < n) (ht : t < roundBytes inK) :
    (ctb4 S m a ix ans (.rounds g n d inK) g).getD (p * roundBytes inK + t) 0 =
      byteAt (a.getD (ix + 2 * p) (ByteArray.empty, 0)).1 (40 + t) := by
  rw [ctb4, if_pos rfl, getD_flatMap_const (fun j => qB4 a (ix + 2 * j) 40 (roundBytes inK)) _ _
    (fun _ _ => N4s.fitL_length _ _) (by simpa using hp) ht, List.getElem_range, qB4_getD _ ht]

/-- A queries phase, field `fCols`: position `p`'s column, its column query (item `(1 + sib)·p`) from
byte 8. -/
theorem ctb4_cols {i p t : ℕ} (hp : p < (S.lv i).t) (ht : t < colBytes i) :
    (ctb4 S m a ix ans (.queries i) fCols).getD (p * colBytes i + t) 0 =
      byteAt (a.getD (ix + (1 + (S.lv i).sib) * p) (ByteArray.empty, 0)).1 (8 + t) := by
  rw [ctb4, if_pos rfl, getD_flatMap_const (fun p => qB4 a (ix + (1 + (S.lv i).sib) * p) 8 (colBytes i)) _ _
    (fun _ _ => N4s.fitL_length _ _) (by simpa using hp) ht, List.getElem_range, qB4_getD _ ht]

/-- A queries phase, field `fSibs`: position `p`'s sibling `h`, the half of its node query (item
`(1 + sib)·p + 1 + h`) not at the position's bit `h` (`sib4`). -/
theorem ctb4_sibs {i p h t : ℕ} (hp : p < (S.lv i).t) (hh : h < (S.lv i).sib) (ht : t < 32) :
    (ctb4 S m a ix ans (.queries i) fSibs).getD ((p * (S.lv i).sib + h) * 32 + t) 0 =
      (sib4 S m i h (posOf4 S m i ans p) (a.getD (ix + (1 + (S.lv i).sib) * p + 1 + h) (ByteArray.empty, 0)).1).getD t 0 := by
  have hne : fSibs ≠ fCols := by decide
  rw [ctb4, if_neg hne, if_pos rfl, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
    getD_flatMap_const _ _ _ (fun _ _ => by
      rw [flatMap_const_length _ _ 32 fun _ _ => sib4_length .., List.length_range]) (by simpa using hp)
      (by nlinarith),
    List.getElem_range, getD_flatMap_const _ _ _ (fun _ _ => sib4_length ..) (by simpa using hh) ht,
    List.getElem_range]

end Shapes

/-! ## The items of a phase -/

theorem getElem?_flatMap_take {β γ : Type} (g : β → List γ) : ∀ (l : List β) (n q : ℕ) (hn : n < l.length),
    q < (g l[n]).length → (l.flatMap g)[((l.take n).map fun x => (g x).length).sum + q]? = (g l[n])[q]?
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | x :: l, 0, q, _, hq => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons,
      List.getElem_cons_zero] at hq ⊢
    rw [List.getElem?_append_left hq]
  | x :: l, n + 1, q, h, hq => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.getElem_cons_succ] at hq ⊢
    rw [List.getElem?_append_right (by omega), show (g x).length + ((l.take n).map fun x => (g x).length).sum + q -
      (g x).length = ((l.take n).map fun x => (g x).length).sum + q by omega,
      getElem?_flatMap_take g l n q (by simpa using h) hq]

/-- **Item `phIx S n + q` of `itemsOf S` is phase `n`'s item `q`.** -/
theorem itemsOf_phIx (S : Seq) {n q : ℕ} (hn : n < (phasesOf S).length)
    (hq : q < (((phasesOf S)[n]).2.itemsL S.lv).length) :
    (itemsOf S)[phIx S n + q]? = (((phasesOf S)[n]).2.itemsL S.lv)[q]? := by
  rw [itemsOf, phIx]
  exact getElem?_flatMap_take (fun p : String × Sh => p.2.itemsL S.lv) _ n q hn hq

/-! ## At a slot: the proof the reader reads -/

/-- **The slot's proof is `pf4` of its trace** (`fitL` keeps `reassemble4`'s exact size). -/
theorem slotπ_byte (κ : NodeKind) (v : ℕ) (w : Circ.Asg) (i : ℕ) :
    byteAt ((N4s.rd4 pf4).slotπ κ v w) i = byteAt (pf4 (N4s.slotTr4 κ v w)) i := by
  have hp : pf4 = reassemble4 seq4 := rfl
  have hl : (pf4 (N4s.slotTr4 κ v w)).data.toList.length = piSizeOf seq4 := by
    rw [Array.length_toList, hp]; exact reassemble4_size seq4 (N4s.slotTr4 κ v w)
  have hf : N4s.fitL (piSizeOf seq4) (pf4 (N4s.slotTr4 κ v w)).data.toList = (pf4 (N4s.slotTr4 κ v w)).data.toList := by
    generalize piSizeOf seq4 = P at hl ⊢
    rw [N4s.fitL, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hr : (N4s.rd4 pf4).slotπ κ v w = ⟨(N4s.slotPf pf4 κ v w).toArray⟩ := rfl
  rw [hr, N4s.slotPf, hf, Array.toArray_toList]

/-- The trace as an array: entry `k` (`k < 8,783`) is item `k` read off the slot's stream. -/
theorem slotTr_getD (κ : NodeKind) (v : ℕ) (w : Circ.Asg) {k : ℕ} (hk : k < (itemsOf seq4).length) :
    (N4s.slotTr4 κ v w).toArray.getD k (ByteArray.empty, 0) =
      Read.entryAt (N4s.slotStr κ v w) (1 + segIx κ v * N4c.strideB + N4s.itOff k) (N4s.itAt k) := by
  have h := N4s.slotTr4_getElem? κ v w k
  rw [N4s.itAt_eq hk, Option.map_some] at h
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, h, Option.getD_some]

/-- **An absorb phase's message at an active slot** (not the last block's item): proof byte
`fieldOffOf seq4 g + phaseOffOf seq4 n g + j` is byte `(o + 48 + j) mod 16` of the H cell of element
`⌊(o + 48 + j)/16⌋`, `o = 1 + itOff (phIx seq4 n)` (the absorb's query: `tag ‖ st ‖ msg`). -/
theorem slot_pfAbsorb {pf : Trace → Proof} {κ : NodeKind} {w : Circ.Asg} {v : ℕ}
    (hv : N4c.Active4 (N4s.rd4 pf) κ w v) {n g len j : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : ((phasesOf seq4)[n]).2 = .absorb g len) (hg : g < nFields4) (hj : j < len)
    (hb : 1 + N4s.itOff (phIx seq4 n) + (N4s.itAt (phIx seq4 n)).slen + 64 ≤ N4c.segB) :
    byteAt ((N4s.rd4 pf4).slotπ κ v w) (fieldOffOf seq4 g + phaseOffOf seq4 n g + j) =
      (F.toBytes (w (sCell (slotB0 κ v) ((1 + N4s.itOff (phIx seq4 n) + 8 + (40 + j)) / 16))))[
        (1 + N4s.itOff (phIx seq4 n) + 8 + (40 + j)) % 16]'(Nat.mod_lt _ (by norm_num)) := by
  have hq0 : 0 < (((phasesOf seq4)[n]).2.itemsL seq4.lv).length := by rw [hsh]; simp [Sh.itemsL]
  have hit := itemsOf_phIx seq4 hn hq0
  rw [hsh, Nat.add_zero] at hit
  simp only [Sh.itemsL, List.getElem?_cons_zero] at hit
  have hk : phIx seq4 n < (itemsOf seq4).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hit; exact absurd hit (by simp)
  have hia : N4s.itAt (phIx seq4 n) = .absorb len := by
    rw [N4s.itAt, List.getD_eq_getElem?_getD, hit]; rfl
  rw [slotπ_byte, pf4, reassemble4_byte seq4 _ hg hn (by rw [hsh]; simpa [Sh.bytesToL] using hj), hsh,
    ctb4_absorb _ _ _ _ _ hj, slotTr_getD κ v w hk]
  have he : (N4s.slotTr4 κ v w)[phIx seq4 n]? = some (Read.entryAt (N4s.slotStr κ v w)
      (1 + segIx κ v * N4c.strideB + N4s.itOff (phIx seq4 n)) (N4s.itAt (phIx seq4 n))) := by
    rw [N4s.slotTr4_getElem?, N4s.itAt_eq hk]; rfl
  exact N4s.slot_qbyte hv hk he hb (by rw [hia]; simp [Item.qlen]; omega)

/-! ## Controls -/

/-- (+) Blocks of constant length: byte `1·3 + 2` of `[a, b]` in blocks of 3 is block `b`'s byte 2;
(−) not block `a`'s. -/
theorem getD_flatMap_ctl :
    ([[1, 2, 3], [4, 5, 6]].flatMap id : List UInt8).getD (1 * 3 + 2) 0 = 6 ∧
      ([[1, 2, 3], [4, 5, 6]].flatMap id : List UInt8).getD (1 * 3 + 2) 0 ≠ 3 := by decide

end X
end FR

end G6_FRNodeRows4AskPosR

section G6_FRNodeRows4AskTB

-- New for `flock-recursive` (PACK-4.4.1 §4.2–§4.3; track ASK-T): what the ask generator's soundness
-- reads: its tables, the byte sources against `reassemble4`, every stream byte an H cell, the pinned tags.

/-!
# The ask generator's facts

* **The tables** (`itemsT_get`, `offT_get`, `srcT_get`): the closed constants are `itemsOf seq4`,
  `itOff` and `srcOf seq4`, read positionally.
* **The byte sources** (`src_spec`): where `srcOf seq4` names `(A, len)` for item `k`, bytes
  `A … A + len` of `reassemble4 seq4 tr` are item `k`'s query bytes from `qoffOf` (the seed's `hdr`
  from 71, a message from 40, a column from 8), which end the query; `A + len ≤ piSizeOf seq4`.
* **Every byte of an active slot's segment is an H cell** (`slot_byte'`): `slot_byte` without its
  last-block exclusion. The last block is the main chain's, or, for an aggregate with `k < maxK`, its
  candidate final block, whose message `aggPad` (`AggPad4`, a theorem of the statement's rows) makes
  the main chain's. So the last item (the cap check's last squeeze) is read like any other.
* **The tags** (`tag_byte`): an entry's query tag is its item's (`itemTag`), from the pack rows' pins
  (`wfSeg`; the seed's from `HeadOk`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The tables -/

theorem itemsT_get (k : ℕ) : itemsT[k]? = (itemsOf seq4)[k]? := by simp [itemsT]

theorem srcT_get (k : ℕ) : srcT[k]? = (srcOf seq4)[k]? := by simp [srcT]

theorem scanl_get (f : Item → ℕ) : ∀ (l : List Item) (o k : ℕ), k ≤ l.length →
    (l.scanl (fun a it => a + f it) o)[k]? = some (o + ((l.take k).map f).sum)
  | [], o, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | it :: l, o, 0, _ => by simp
  | it :: l, o, k + 1, h => by
    rw [List.scanl_cons, List.getElem?_cons_succ, scanl_get f l _ k (by simpa using h)]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, Option.some.injEq]
    omega

theorem offT_get {k : ℕ} (hk : k ≤ (itemsOf seq4).length) : offT.getD k 0 = itOff k := by
  unfold offT itOff
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, scanl_get _ _ 0 k hk, Option.getD_some,
    Nat.zero_add]

/-! ## Lists of blocks -/

theorem flatMap_inv {α β : Type} (g : α → List β) : ∀ (l : List α) (k : ℕ) (x : β), (l.flatMap g)[k]? = some x →
    ∃ n, ∃ hn : n < l.length, ∃ q, k = ((l.take n).map fun a => (g a).length).sum + q ∧ (g l[n])[q]? = some x
  | [], k, x, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.flatMap_cons] at h
    by_cases hk : k < (g a).length
    · rw [List.getElem?_append_left hk] at h
      exact ⟨0, by simp, k, by simp, by simpa using h⟩
    · rw [List.getElem?_append_right (by omega)] at h
      obtain ⟨n, hn, q, hq, hx⟩ := flatMap_inv g l _ x h
      refine ⟨n + 1, by simpa using hn, q, ?_, by simpa using hx⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega

theorem flatMap_range_len {β : Type} (g : ℕ → List β) (c : ℕ) (hc : ∀ p, (g p).length = c) :
    ∀ N, ((List.range N).flatMap g).length = N * c
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_len g c hc N]
    simp [hc, Nat.succ_mul]

theorem flatMap_range_get {β : Type} (g : ℕ → List β) (c : ℕ) (hc : ∀ p, (g p).length = c) :
    ∀ (N p r : ℕ), p < N → r < c → ((List.range N).flatMap g)[c * p + r]? = (g p)[r]?
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | N + 1, p, r, hp, hr => by
    rw [List.range_succ, List.flatMap_append]
    have hl := flatMap_range_len g c hc N
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · have : c * p + r < N * c := by nlinarith
      rw [List.getElem?_append_left (by omega), flatMap_range_get g c hc N p r hp hr]
    · rw [List.getElem?_append_right (by rw [hl, Nat.mul_comm]; omega), hl,
        show c * p + r - p * c = r by rw [Nat.mul_comm]; omega]
      simp

theorem flatMap_range_inv {β : Type} (g : ℕ → List β) {c : ℕ} (hc : ∀ p, (g p).length = c) (hc0 : 0 < c)
    {N k : ℕ} {x : β} (h : ((List.range N).flatMap g)[k]? = some x) : k / c < N ∧ (g (k / c))[k % c]? = some x := by
  have hk : k < N * c := by
    rw [← flatMap_range_len g c hc N]
    exact (List.getElem?_eq_some_iff.1 h).1
  have hN : k / c < N := (Nat.div_lt_iff_lt_mul hc0).2 hk
  refine ⟨hN, ?_⟩
  rw [← flatMap_range_get g c hc N _ _ hN (Nat.mod_lt _ hc0), Nat.div_add_mod]; exact h

theorem replicate_flatten_get {β : Type} (l : List β) : ∀ (N p r : ℕ), p < N → r < l.length →
    ((List.replicate N l).flatten)[l.length * p + r]? = l[r]?
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | N + 1, 0, r, _, hr => by
    rw [List.replicate_succ, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_append_left hr]
  | N + 1, p + 1, r, hp, hr => by
    rw [List.replicate_succ, List.flatten_cons, List.getElem?_append_right (by nlinarith),
      show l.length * (p + 1) + r - l.length = l.length * p + r by rw [Nat.mul_succ]; omega]
    exact replicate_flatten_get l N p r (by omega) hr

/-! ## The byte sources against `reassemble4` -/

/-- Where the proof bytes an item gives start in its query. -/
def qoffOf : Item → ℕ
  | .seed => 71
  | .absorb _ => 40
  | .col _ => 8
  | _ => 0

theorem srcL_length (S : Seq) (n : ℕ) (sh : Sh) : (sh.srcL S n).length = (sh.itemsL S.lv).length := by
  cases sh with
  | rounds g k d inK =>
    simp only [Sh.srcL, Sh.itemsL]
    rw [flatMap_range_len _ 2 (fun _ => rfl)]
    simp [List.length_flatten, List.sum_replicate, Nat.mul_comm]
  | queries i =>
    simp only [Sh.srcL, Sh.itemsL]
    rw [flatMap_range_len _ (1 + (S.lv i).sib) (fun _ => by simp; omega)]
    simp [List.length_flatten, List.sum_replicate, posItemsL, Nat.mul_comm, Nat.add_comm]
  | _ => simp [Sh.srcL, Sh.itemsL]

theorem srcOf_sum (S : Seq) (n : ℕ) :
    (((phasesOf S).zipIdx.take n).map fun p => (p.1.2.srcL S p.2).length).sum = X.phIx S n := by
  have hf : (fun p : (String × Sh) × ℕ => (p.1.2.srcL S p.2).length) =
      (fun a : String × Sh => (a.2.itemsL S.lv).length) ∘ Prod.fst := by
    funext p; simp [srcL_length]
  rw [hf, ← List.map_map, List.map_take, List.zipIdx_map_fst, X.phIx]

theorem fieldOff_succ (S : Seq) (b : ℕ) : fieldOffOf S (b + 1) = fieldOffOf S b + fieldSizeOf S b := by
  simp [fieldOffOf, List.range_succ]

theorem fieldOff_mono (S : Seq) (a : ℕ) : ∀ d, fieldOffOf S a ≤ fieldOffOf S (a + d)
  | 0 => le_rfl
  | d + 1 => by rw [← Nat.add_assoc, fieldOff_succ]; have := fieldOff_mono S a d; omega

/-- **A field's phase part ends inside the proof.** -/
theorem src_le (S : Seq) {f n j : ℕ} (hf : f < nFields4) (hn : n < (phasesOf S).length)
    (hj : j ≤ ((phasesOf S)[n]).2.bytesToL S.lv f) : fieldOffOf S f + phaseOffOf S n f + j ≤ piSizeOf S := by
  have h1 := X.take_sum_le (fun p : String × Sh => p.2.bytesToL S.lv f) (phasesOf S) n hn
  have h2 : phaseOffOf S n f + ((phasesOf S)[n]).2.bytesToL S.lv f ≤ fieldSizeOf S f := h1
  have e := fieldOff_succ S f
  have h3 := fieldOff_mono S (f + 1) (nFields4 - (f + 1))
  rw [Nat.add_sub_cancel' hf] at h3
  have h4 : fieldOffOf S nFields4 = piSizeOf S := rfl
  omega

theorem itAt_of {k : ℕ} {it : Item} (h : (itemsOf seq4)[k]? = some it) : k < (itemsOf seq4).length ∧ itAt k = it := by
  have hk : k < (itemsOf seq4).length := (List.getElem?_eq_some_iff.1 h).1
  exact ⟨hk, by rw [itAt, List.getD_eq_getElem?_getD, h, Option.getD_some]⟩

/-- **The byte sources are `reassemble4`'s**: where `srcOf seq4` names `(A, len)` for item `k`, proof
bytes `A + j` are item `k`'s query bytes `qoffOf + j`, the query's last `len` bytes. -/
theorem src_spec {k A len : ℕ} (h : (srcOf seq4)[k]? = some (some (A, len))) :
    k < (itemsOf seq4).length ∧ qoffOf (itAt k) + len = (itAt k).qlen ∧ A + len ≤ piSizeOf seq4 ∧
      ∀ (tr : Trace) (j : ℕ), j < len → byteAt (X.reassemble4 seq4 tr) (A + j) =
        byteAt (tr.toArray.getD k (ByteArray.empty, 0)).1 (qoffOf (itAt k) + j) := by
  obtain ⟨n, hn, q, rfl, hq⟩ := flatMap_inv _ _ k _ h
  rw [srcOf_sum] at *
  simp only [List.length_zipIdx] at hn
  rw [List.getElem_zipIdx, Nat.zero_add] at hq
  have hqi : q < (((phasesOf seq4)[n]).2.itemsL seq4.lv).length := by
    rw [← srcL_length seq4 n]; exact (List.getElem?_eq_some_iff.1 hq).1
  have hit := X.itemsOf_phIx seq4 hn hqi
  have hrb := fun (tr : Trace) {f j : ℕ} (hf : f < nFields4)
    (hj : j < ((phasesOf seq4)[n]).2.bytesToL seq4.lv f) => X.reassemble4_byte seq4 tr hf hn hj
  have hle := fun {f j : ℕ} (hf : f < nFields4) (hj : j ≤ ((phasesOf seq4)[n]).2.bytesToL seq4.lv f) =>
    src_le seq4 hf hn hj
  generalize hsh : ((phasesOf seq4)[n]).2 = sh at hq hit hrb hle
  cases sh with
  | seed =>
    simp only [Sh.srcL] at hq
    obtain rfl : q = 0 := by rcases q with _ | q; rfl; simp at hq
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨hk, hia⟩ := itAt_of (by rw [hit]; rfl)
    refine ⟨hk, by rw [hia]; rfl, hle (by decide) (by simp [Sh.bytesToL, fHdr]), fun tr j hj => ?_⟩
    rw [hrb tr (f := fHdr) (by decide) (by simpa [Sh.bytesToL, fHdr] using hj), X.ctb4_seed _ _ _ _ _ hj, hia, Nat.add_zero]
    rfl
  | absorb g len' =>
    simp only [Sh.srcL] at hq
    obtain rfl : q = 0 := by rcases q with _ | q; rfl; simp at hq
    split_ifs at hq with hg
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      obtain ⟨hk, hia⟩ := itAt_of (by rw [hit]; rfl)
      refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega, hle hg (by simp [Sh.bytesToL]), fun tr j hj => ?_⟩
      rw [hrb tr hg (by simpa [Sh.bytesToL] using hj), X.ctb4_absorb _ _ _ _ _ hj, hia, Nat.add_zero]
      rfl
    · simp at hq
  | squeezes k' ch =>
    rw [Sh.srcL, List.getElem?_replicate] at hq
    split_ifs at hq <;> simp at hq
  | uni g =>
    simp only [Sh.srcL] at hq
    rcases q with _ | _ | q
    · split_ifs at hq with hg
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨hk, hia⟩ := itAt_of (by rw [hit]; rfl)
        refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega, hle hg (by simp [Sh.bytesToL]),
          fun tr j hj => ?_⟩
        rw [hrb tr hg (by simpa [Sh.bytesToL] using hj), X.ctb4_uni _ _ _ _ _ hj, hia, Nat.add_zero]
        rfl
      · simp at hq
    · simp at hq
    · simp at hq
  | rounds g k' d inK =>
    simp only [Sh.srcL] at hq
    obtain ⟨hp, hq'⟩ := flatMap_range_inv _ (c := 2) (fun _ => rfl) (by norm_num) hq
    have hr : q % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
      · exact h0
      · rw [h1] at hq'; simp at hq'
    rw [hr] at hq'
    split_ifs at hq' with hg
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨rfl, rfl⟩ := hq'
      have e2 := replicate_flatten_get [Item.absorb (roundBytes inK), .squeeze] k' (q / 2) 0 hp (by simp)
      have hq2 : [Item.absorb (roundBytes inK), Item.squeeze].length * (q / 2) + 0 = q := by simp; omega
      rw [hq2] at e2
      obtain ⟨hk, hia⟩ := itAt_of (by rw [hit, Sh.itemsL, e2]; rfl)
      have hb : (q / 2) * roundBytes inK + roundBytes inK ≤ k' * roundBytes inK := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
      refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega,
        by have := hle (j := q / 2 * roundBytes inK + roundBytes inK) hg (by simp [Sh.bytesToL]; omega); omega,
        fun tr j hj => ?_⟩
      have e := hrb tr (j := q / 2 * roundBytes inK + j) hg (by simp [Sh.bytesToL]; omega)
      rw [X.ctb4_rounds _ _ _ _ _ hp hj, show 2 * (q / 2) = q by omega] at e
      rw [Nat.add_assoc, e, hia]; rfl
    · simp at hq'
  | queries i =>
    simp only [Sh.srcL] at hq
    have hc : ∀ p, ((fun p => some (fieldOffOf seq4 fCols + phaseOffOf seq4 n fCols + p * colBytes i, colBytes i) ::
        List.replicate (seq4.lv i).sib (none : Option (ℕ × ℕ))) p).length = 1 + (seq4.lv i).sib := fun p => by
      simp only [List.length_cons, List.length_replicate]; omega
    obtain ⟨hp, hq'⟩ := flatMap_range_inv _ hc (by omega) hq
    have hr : q % (1 + (seq4.lv i).sib) = 0 := by
      by_contra h0
      obtain ⟨r, hr⟩ : ∃ r, q % (1 + (seq4.lv i).sib) = r + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
      rw [hr] at hq'; simp only [List.getElem?_cons_succ, List.getElem?_replicate] at hq'
      split_ifs at hq' <;> simp at hq'
    rw [hr] at hq'
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    have hpl : (posItemsL seq4.lv i).length = 1 + (seq4.lv i).sib := by simp [posItemsL]; omega
    have hq2 : (1 + (seq4.lv i).sib) * (q / (1 + (seq4.lv i).sib)) = q := by
      have := Nat.div_add_mod q (1 + (seq4.lv i).sib); omega
    have e2 := replicate_flatten_get (posItemsL seq4.lv i) _ _ 0 hp (by simp [posItemsL])
    rw [hpl, Nat.add_zero, hq2] at e2
    obtain ⟨hk, hia⟩ := itAt_of (by rw [hit, Sh.itemsL, e2]; rfl)
    set p := q / (1 + (seq4.lv i).sib)
    have hb : p * colBytes i + colBytes i ≤ (seq4.lv i).t * colBytes i := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
    have hfc : fCols < nFields4 := by decide
    refine ⟨hk, by rw [hia]; simp [qoffOf, Item.qlen] <;> omega,
      by have := hle (j := p * colBytes i + colBytes i) hfc (by simp [Sh.bytesToL]; omega); omega,
      fun tr j hj => ?_⟩
    have e := hrb tr (j := p * colBytes i + j) hfc (by simp [Sh.bytesToL]; omega)
    rw [X.ctb4_cols _ _ _ _ _ hp hj, hq2] at e
    rw [Nat.add_assoc, e, hia]; rfl

end N4s
end FR

end G6_FRNodeRows4AskTB

section G6_FRNodeRows4AskTH

-- New for `flock-recursive` (PACK-4.4.1 §4.3; ASK-P-RESULT §6 item 1; track ASK-T): every byte of an
-- active slot's segment is an H cell (the last block by `aggPad`), and the pinned tags.

/-!
# The whole segment off H, and the tags

ASK-P's bridge (`slot_byte`) stops before the segment's last block: for an aggregate with `k < maxK`
its stream's last block is the candidate final block `finB + (k − 1)`, not the main chain's. Here:

* **`readByte_eqz`**, **`chainBytes4_elem'`**: a stream byte is the main chain's H cell wherever the
  final block's message equals the main chain's block (`AggPad4`, R-4-m2: whole blocks, `aggB k =
  64·aggL k`, so its `r` is 64 and the whole message is tied);
* **`slot_byte'`**: every byte `x < segB` of an active slot's segment (given `AggPad4` at every
  aggregate, a theorem of the statement's rows: `wots_aggPad_of_rows`); **`slot_qbyte'`**,
  **`slot_ans'`**: entry `k`'s query bytes and answer for every item, the last one included;
* **`tag_byte`**: an entry's query tag is its item's (`itemTag`), from the pack rows (`wfSeg`'s pins;
  the seed's from `HeadOk`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval

/-! ## The last block -/

/-- A block's message byte depends only on its message bits. -/
theorem readByte_eqz (w : Asg) {b₁ b₂ p : ℕ} (hp : 512 ≤ p) (hp' : p + 8 ≤ 1024)
    (h : ∀ x < 512, N4c.zN4 w b₁ (512 + x) = N4c.zN4 w b₂ (512 + x)) :
    Block.readByte (N4c.bitsB4 w b₁) p = Block.readByte (N4c.bitsB4 w b₂) p := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => ?_)
  rw [Block.readByte_getLsbD _ _ hi, Block.readByte_getLsbD _ _ hi, N4c.bitsB4_pos w _ (by omega),
    N4c.bitsB4_pos w _ (by omega), show p + i = 512 + (p + i - 512) by omega, h _ (by omega)]

/-- **A stream byte is its main-chain cell's**, the last block included where its block is the main
chain's or carries the main chain's message. -/
theorem chainBytes4_elem' {κ : NodeKind} {σ k : ℕ} (w : Asg) {e r : ℕ} (hr : r < 16)
    (hp : 16 * e + r < N4c.streamB κ σ k)
    (hfin : e / 4 + 1 = N4c.streamL κ σ k → N4c.finBlk κ σ k = N4c.chBase κ σ + e / 4 ∨
      ∀ x < 512, N4c.zN4 w (N4c.finBlk κ σ k) (512 + x) = N4c.zN4 w (N4c.chBase κ σ + e / 4) (512 + x)) :
    (N4c.chainBytes4 κ σ k w).getD (16 * e + r) 0 = (F.toBytes (w (sCell (N4c.chBase κ σ) e)))[r] := by
  obtain ⟨h1, h2⟩ := Stream.elem_slot e r hr
  rw [N4c.chainBytes4, Stream.streamBytes, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hp, Option.map_some, Option.getD_some, h1, h2]
  simp only [N4c.chainW4, N4c.blkOf]
  rw [show 128 * (4 + e % 4) + 8 * r = 512 + 128 * (e % 4) + 8 * r by ring]
  have hm : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  split_ifs with hb
  · rcases hfin hb with h | h
    · rw [h, readByte_cell w _ hm hr]; rfl
    · rw [readByte_eqz w (by omega) (by omega) h, readByte_cell w _ hm hr]; rfl
  · rw [readByte_cell w _ hm hr]; rfl

/-- **The last block reads the main chain**: for an aggregate with `k < maxK`, `AggPad4`'s message
tie (its `r` is 64: whole blocks); otherwise the final block is the main chain's last. -/
theorem fin_main {κ : NodeKind} {a k : ℕ} {w : Asg} (hk : 1 ≤ k) (hkm : k ≤ κ.maxK)
    (hpad : N4c.AggPad4 κ a k w) {e : ℕ} (he : e / 4 + 1 = N4c.streamL κ (N4c.aggChild κ a) k) :
    N4c.finBlk κ (N4c.aggChild κ a) k = N4c.chBase κ (N4c.aggChild κ a) + e / 4 ∨
      ∀ x < 512, N4c.zN4 w (N4c.finBlk κ (N4c.aggChild κ a) k) (512 + x) =
        N4c.zN4 w (N4c.chBase κ (N4c.aggChild κ a) + e / 4) (512 + x) := by
  have hA := isAgg_aggChild κ a
  simp only [N4c.streamL, hA, if_true] at he
  obtain ⟨hb, -, -⟩ := N4c.aggB_blocks hk
  rcases Nat.lt_or_ge k κ.maxK with hlt | hge
  · refine .inr fun x hx => ?_
    have h2 := (hpad.1 hlt).2 x (by omega)
    rwa [show N4c.chBase κ (N4c.aggChild κ a) + N4c.aggL k - 1 = N4c.chBase κ (N4c.aggChild κ a) + e / 4 by
      omega] at h2
  · refine .inl ?_
    have hk' : k = κ.maxK := by omega
    simp only [N4c.finBlk, N4c.chLen, hA, true_and, if_true, show ¬ k < κ.maxK by omega, if_false]
    rw [← hk']; omega

/-- **Every byte of an active slot's segment** (`x < segB`) is byte `x mod 16` of the H cell of its
element `⌊x/16⌋`, given `AggPad4` at every aggregate. -/
theorem slot_byte' {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w) {x : ℕ} (hx : x < N4c.segB) :
    (slotStr κ v w).getD (segIx κ v * N4c.strideB + x) 0 =
      (F.toBytes (w (sCell (slotB0 κ v) (x / 16))))[x % 16]'(Nat.mod_lt _ (by norm_num)) := by
  obtain ⟨h1, -, h3⟩ := N4c.strideB_eq
  rcases active_cases hv with ⟨hp, rfl⟩ | ⟨a, ha, i, hi, rfl⟩
  · have h0 : isPrevSlot κ 0 = true := by simp [isPrevSlot, hp]
    have hA : N4c.isAgg κ 0 = false := by
      cases h : N4c.isAgg κ 0
      · rfl
      · simp [N4c.isAgg, hp] at h
    simp only [slotStr, slotSg, slotK, segIx, slotB0, h0, if_true, Nat.zero_mul, Nat.zero_add]
    conv_lhs => rw [show x = 16 * (x / 16) + x % 16 by omega]
    refine chainBytes4_elem' w (Nat.mod_lt _ (by norm_num)) (by simp [N4c.streamB, hA]; omega) fun hb => .inl ?_
    simp only [N4c.streamL, hA, Bool.false_eq_true, if_false] at hb
    simp only [N4c.finBlk, N4c.chLen, hA, Bool.false_eq_true, false_and, if_false]
    omega
  · have hk := kAct_le κ a w
    obtain ⟨-, hsi, hps, -⟩ := sub_facts κ ha (lt_of_lt_of_le hi hk)
    have hsa := slotA_sub κ ha (lt_of_lt_of_le hi hk)
    have hag : aggSlot κ (N4c.sub κ a i) = slotA κ (N4c.sub κ a i) := by unfold aggSlot slotA; rfl
    simp only [slotStr, slotSg, slotK, segIx, slotB0, hps, if_false, Bool.false_eq_true, hsi, hsa, hag]
    have hA := isAgg_aggChild κ a
    have hk1 : 1 ≤ kAct κ a w := by omega
    obtain ⟨-, -, hB⟩ := N4c.aggB_blocks hk1
    have hik : i * N4c.strideB + N4c.strideB ≤ kAct κ a w * N4c.strideB := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    have hm : i * N4c.strideB = 64 * (i * N4c.sBlk) := by rw [h1]; ring
    have hs : N4c.strideB = N4c.segB + 128 := by decide
    rw [show i * N4c.strideB + x = 16 * (4 * (i * N4c.sBlk) + x / 16) + x % 16 by omega,
      chainBytes4_elem' w (Nat.mod_lt _ (by norm_num))
        (by simp only [N4c.streamB, hA, if_true]; omega)
        (fin_main hk1 hk (by rw [← kA_rd4 pf κ ha w]; exact hpad a ha)), sCell_add]

/-! ## Entries -/

theorem itOff_slen {k : ℕ} (hk : k < (itemsOf seq4).length) : 1 + itOff k + 8 + (itAt k).qlen + 32 ≤ N4c.segB := by
  have := itOff_le hk; have : (itAt k).slen = 8 + (itAt k).qlen + 32 := rfl; omega

/-- **Entry `k`'s query byte `j`** at an active slot, every item. -/
theorem slot_qbyte' {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    {j : ℕ} (hj : j < (itAt k).qlen) :
    byteAt e.1 j = (F.toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16))))[(1 + itOff k + 8 + j) % 16]'(
      Nat.mod_lt _ (by norm_num)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hs := itOff_slen hk
  have hL := slotStr_len hv
  rw [entryAt_qbyte _ _ _ hj (by omega),
    show 1 + segIx κ v * N4c.strideB + itOff k + 8 + j = segIx κ v * N4c.strideB + (1 + itOff k + 8 + j) by omega,
    slot_byte' hv hpad (by omega)]

/-- **Entry `k`'s answer** at an active slot, every item: its halves are the H cells of elements
`ansE k`, `ansE k + 1`. -/
theorem slot_ans' {pf : Trace → Proof} {κ : NodeKind} {w : Asg} {v : ℕ} (hv : N4c.Active4 (rd4 pf) κ w v)
    (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e) :
    dlo e.2 = w (sCell (slotB0 κ v) (ansE k)) ∧ dhi e.2 = w (sCell (slotB0 κ v) (ansE k + 1)) := by
  rw [slotTr4_getElem?, itAt_eq hk, Option.map_some, Option.some.injEq] at he
  subst he
  have hal := ans_al hk
  have hs := itOff_slen hk
  have key : ∀ (h : ℕ) (r : Fin 16) (_hh : h < 2),
      (Read.entryAt (slotStr κ v w) (1 + segIx κ v * N4c.strideB + itOff k) (itAt k)).2[16 * h + r.1]'(by omega) =
        (F.toBytes (w (sCell (slotB0 κ v) (ansE k + h))))[r.1] := fun h r hh => by
    rw [entryAt_abyte _ _ _ (16 * h + r.1) (by omega)]
    rw [show 1 + segIx κ v * N4c.strideB + itOff k + 8 + (itAt k).qlen + (16 * h + r.1) =
        segIx κ v * N4c.strideB + (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) by omega,
      slot_byte' hv hpad (by have := r.2; omega)]
    have e1 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) / 16 = ansE k + h := by unfold ansE; omega
    have e2 : (1 + itOff k + 8 + (itAt k).qlen + 16 * h + r.1) % 16 = r.1 := by omega
    simp only [e1, e2]
  constructor
  · rw [dlo, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    simpa using key 0 ⟨r, hr⟩ (by norm_num)
  · rw [dhi, ← F.ofBytes_toBytes (w (sCell (slotB0 κ v) (ansE k + 1)))]
    refine congrArg F.ofBytes (Vector.ext fun r hr => ?_)
    rw [Vector.getElem_ofFn]
    exact key 1 ⟨r, hr⟩ (by norm_num)

/-! ## The tags -/

theorem wfData_get : ∀ (its : List Item) (o k : ℕ), (wfData o its)[k]? =
    its[k]?.map fun it => ((o + ((its.take k).map Item.slen).sum) / 16, winF (o + ((its.take k).map Item.slen).sum) it)
  | [], _, _ => rfl
  | it :: its, o, 0 => by simp [wfData]
  | it :: its, o, k + 1 => by
    rw [wfData, List.getElem?_cons_succ, wfData_get its, List.getElem?_cons_succ, List.take_succ_cons,
      List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **Item `k ≥ 1`'s first element is pinned** (`wfSeg`). -/
theorem wfSeg_mem {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (itemsOf seq4).length) :
    (itE k, winF (1 + itOff k) (itAt k)) ∈ wfSeg := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine List.mem_of_getElem? (i := j) ?_
  rw [wfSeg, List.getElem?_tail, wfData_get, itAt_eq hk]; rfl

theorem itAt_seed : itAt 0 = .seed := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al; simp [itAt, hr]

theorem itAt_ne_seed {k : ℕ} (hk1 : 1 ≤ k) (hk : k < (itemsOf seq4).length) : itAt k ≠ .seed := by
  obtain ⟨rest, hr, hal⟩ := itemsOf_seq4_al
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : j < rest.length := by rw [hr] at hk; simpa using hk
  have hit : itAt (j + 1) = rest[j] := by simp [itAt, hr, List.getD_eq_getElem?_getD, hj]
  intro h
  have := (hal rest[j] (List.getElem_mem hj)).1
  rw [← hit, h] at this; exact absurd this (by decide)

theorem toBytes_idx {a b : F} (h : a = b) {r s : ℕ} (hrs : r = s) (hr : r < 16) :
    (F.toBytes a)[r]'hr = (F.toBytes b)[s]'(hrs ▸ hr) := by subst h hrs; rfl

theorem itemTag_len (it : Item) : (itemTag it).length = if it = .seed then 7 else 8 := by
  cases it <;> rfl

/-- **The first query element's alignment**: past the length word and the tag, item `k`'s query is on
an element boundary (the seed's `vk` at element 1, every other query's first digest). -/
theorem qAl {k : ℕ} (hk : k < (itemsOf seq4).length) : (1 + itOff k + 8 + (itemTag (itAt k)).length) % 16 = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [itAt_seed]; rfl
  · rw [itemTag_len, if_neg (itAt_ne_seed hk1 hk)]; have := itOff_al hk1; omega

/-- **An entry's tag is its item's**, at an active slot whose rows hold. -/
theorem tag_byte {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {v : ℕ}
    (hS : N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) (hv : N4c.Active4 (rd4 pf4) κ w v)
    (hvs : v < κ.vslots) (hpad : ∀ a < N4c.nAgg κ, N4c.AggPad4 κ a (N4c.kA (rd4 pf4) κ w a) w)
    {k : ℕ} (hk : k < (itemsOf seq4).length) {e : ByteArray × Digest} (he : (slotTr4 κ v w)[k]? = some e)
    {j : ℕ} (hj : j < (itemTag (itAt k)).length) : byteAt e.1 j = (itemTag (itAt k)).getD j 0 := by
  have hjq : j < (itAt k).qlen := by
    have := itemTag_len (itAt k); cases h : itAt k <;> simp [h, Item.qlen] at this hj ⊢ <;> omega
  rw [slot_qbyte' hv hpad hk he hjq]
  obtain ⟨G, hG⟩ : ∃ G, packB κ v = some (slotB0 κ v, G) := by
    have := packB_b0 κ v
    rcases h : packB κ v with _ | ⟨b, G⟩
    · rw [h] at this; cases this
    · rw [h] at this; simp at this; exact ⟨G, by rw [this]⟩
  obtain ⟨hpin, -, hhd⟩ := pins_of hS hvs hG
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [itAt_seed] at hj ⊢
    have hj7 : j < 7 := by simpa [itemTag, tagSeed] using hj
    have e1 : (1 + itOff 0 + 8 + j) / 16 = 0 := by simp [itOff]; omega
    have e2 : (1 + itOff 0 + 8 + j) % 16 = 9 + j := by simp [itOff]; omega
    simp only [e1, e2]
    rw [hhd.e0 _ (by omega) (by omega), seedW, winF, winFB, F.toBytes_ofBytes, Vector.getElem_ofFn]
    interval_cases j <;> rfl
  · have hal := itOff_al hk1
    have hne := itAt_ne_seed hk1 hk
    have hj8 : j < 8 := by rw [itemTag_len, if_neg hne] at hj; exact hj
    have e1 : (1 + itOff k + 8 + j) / 16 = itE k := by unfold itE; omega
    have e2 : (1 + itOff k + 8 + j) % 16 = 8 + j := by omega
    have hm := wfSeg_mem hk1 hk
    have hp := hpin _ hm
    dsimp only at hp
    have hp' : w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j) / 16)) = winF (1 + itOff k) (itAt k) := by
      rw [e1]; exact hp
    rw [toBytes_idx hp' e2, winF, winFB, F.toBytes_ofBytes,
      Vector.getElem_ofFn]
    simp only [winB, show (1 + itOff k) % 16 ≠ 1 by omega, if_false, List.nil_append]
    rw [List.getD_append_right _ _ _ _ (by simp [enc64])]
    simp [enc64]

end N4s
end FR

end G6_FRNodeRows4AskTH
