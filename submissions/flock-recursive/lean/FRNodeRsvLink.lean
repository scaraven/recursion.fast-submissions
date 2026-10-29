-- New for `flock-recursive` (revision 4.4.2, the reserve; RSV-S2b §5 item 4, RSV-S3 §5.4; track SRA):
-- slot 0's stacked `evalM` bound by the reserve's cells, as one more ask-template summand.
import FRNodeRows4AskInp
import FRNodeStmtR4

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
def implR : OpImpl := { Impl.implCN with evalM := fun _ _ => (0, 1, 0) }

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
