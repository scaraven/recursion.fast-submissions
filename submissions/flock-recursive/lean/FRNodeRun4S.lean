-- New for `flock-recursive` (PACK-4.4 §4.3; track B3). `compileX_run` at the node's slot prototypes;
-- the twin of S-E14's `slotImp_of_rep`/`gap4Imp_of_rep` (`FRNodeRows4Rep`).
import FRNodeRun4
import FRSoundness4Qry

/-!
# The slot's run on the reader's trace

`compileX_run` at prototype `π` (`protoCS π = compileX (Xof π) …`):

* **`protoProg_items`**: both prototypes ask `itemsOf seq4` (8,905 items), read off the group
  programs' relation to the kind programs (`progNodeGK_rel`, `progSegG_rel`) and `items_gen4`. So the
  answer-driven run on a trace of 8,905 entries exists and uses it up.
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

/-- **The answer-driven run of prototype `π` on a trace of 8,905 entries exists and uses it up.** -/
theorem execA_proto (impl : OpImpl) (π : ℕ) (ι : Kind) (inp : Input) {tr : Trace} (hl : tr.length = 8905) :
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
run on `tr` (8,905 entries) included. -/
theorem slotImp_of_runA {rt : ℕ → RT} {A : ℕ → AT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind} {v : ℕ}
    {w : Asg} {inp : Input} {tr : Trace} (hl : tr.length = 8905) (hrows : SlotRows κ v w)
    (hrep : RepHolds rt κ v w) (hask : AskHolds A κ v w) (h : SlotImpA rt A impl₀ base κ v w inp tr) :
    SlotImp impl₀ base κ v w inp tr := by
  intro ι hS
  obtain ⟨hA, hR, hst⟩ := h ι hS
  have hπ := protoOf_le' κ v
  have hX := tplExt4_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base hπ ι)
    (protoLay (protoOf κ v))
  obtain ⟨s, he⟩ := execA_proto (implP impl₀ base (protoOf κ v) ι) (protoOf κ v) ι inp hl
  obtain ⟨hx, hi, hf⟩ := hR s he
  have key := compileX_run hX (hok _ hπ ι) hA (baseR (protoOf κ v)) hS he hrows.1 hrows.2 hx hi hrep hask hf
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
