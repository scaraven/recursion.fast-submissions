-- New for `flock-recursive` (PACK-4.4 §6.2, the stage table's C1; track C1).
import FRNodeRows4RepN

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

/-- **Where a replay cell lives** (slot `v` of a node of kind `κ`): a frame cell where the slot's
assignment reads it; a local (`c ≥ repB`) in the spare region, from cell `κ.vslots·2^20`. -/
def repMapC (κ : Rev4.NodeKind) (v c : ℕ) : ℕ :=
  if c < repB then mvC (protoOf κ v) v c + κ.oneCell else κ.vslots * slotM4 + (c - repB) + κ.oneCell

/-- **The replay rows' assignment** at slot `v`. -/
def repAsg (κ : Rev4.NodeKind) (v : ℕ) (w : Asg) : Asg := w ∘ repMapC κ v

theorem agree_repAsg (κ : Rev4.NodeKind) (v : ℕ) (w : Asg) : Agree repB (slotAsg κ v w) (repAsg κ v w) :=
  fun c hc => by simp only [repAsg, Function.comp_apply, repMapC, hc, ite_true, slotAsg]

/-- **The replay rows hold** at slot `v` (at `repAsg`). -/
def RepHoldsW (rt : ℕ → RT) (κ : Rev4.NodeKind) (v : ℕ) (w : Asg) : Prop :=
  ∀ r ∈ repRowsP (rt (protoOf κ v)) (protoOf κ v), r.Holds (repAsg κ v w)

/-- **The templates are sound** for every prototype and index (`RTOkW` at `repB`). -/
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
  have hX := tplExt4_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base hπ ι)
    (protoLay (protoOf κ v))
  have key := compileX_soundRW hX (hok _ hπ ι) (baseR (protoOf κ v)) hS (selOk_repAsg hS)
    (agree_repAsg κ v w) he hrows.1 hrows.2 hx hi hrep hf
  exact ⟨⟨s, he, hx, fun i _ => key.2 i, hf⟩, hst⟩

/-- **`RepOkW` for `rtC1`.** -/
theorem repOkW_rtC1 {impl₀ : OpImpl} {base : Rev4.NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base) :
    RepOkW rtC1 impl₀ base := fun _ hπ ι => rtC1_ok hZ hB hπ ι

/-! ## The node's indexed replay rows -/

/-- **Slot `v`'s replay rows' first row**: slot 0 of a node with a previous node (prototype 0) in
the spare region (`κ.vslots·2^20`); a segment slot at S-E14's `v·2^20 + repBase`. -/
def repRow0 (κ : Rev4.NodeKind) (v : ℕ) : ℕ := if protoOf κ v = 0 then κ.vslots * slotM4 else v * slotM4 + repBase

/-- **Slot `v`'s replay rows** (absolute cells: `repMapC`). -/
def repIRowsW (rt : ℕ → RT) (κ : Rev4.NodeKind) (v : ℕ) : List (ℕ × Row) :=
  (repRowsP (rt (protoOf κ v)) (protoOf κ v)).zipIdx.map fun p =>
    (repRow0 κ v + p.2, rowMapC (repMapC κ v) p.1)

/-- **The node's rows give the replay rows** once they are folded in (`hfold`). -/
theorem repHoldsW_of {rt : ℕ → RT} {κ : Rev4.NodeKind} {v : ℕ} {w : Asg}
    (hfold : ∀ p ∈ repIRowsW rt κ v, p ∈ nodeIRows4 κ) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    RepHoldsW rt κ v w := by
  unfold RepHoldsW
  unfold repIRowsW at hfold
  generalize repRowsP (rt (protoOf κ v)) (protoOf κ v) = l at hfold ⊢
  intro r hr
  obtain ⟨k, hm⟩ := mem_zipIdx_map hr fun p : Row × ℕ => (repRow0 κ v + p.2, rowMapC (repMapC κ v) p.1)
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

end N4s
end FR
