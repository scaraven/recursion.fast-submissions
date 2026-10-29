-- New for `flock-recursive` (PACK-4.4.1 §4.2, §5.2; IMP-RESULT §5.5; SRA-RESULT §6.1; track ASK-P): the
-- folds of the ask templates' rows, arena₁ and the bits into `nodeIRows4`, as theorems.
import FRNodeRsvLink

/-!
# The folds: the node's M rows hold the ask templates' rows, arena₁ and the bits

`FRNodeRows4.arIRows4` puts, in every slot region, arena₁ (`a1Rows4`), the slot prototype's
template rows (`askRowsT`, at `v·2^20 + arR2 + k`: B3's `askIRows4 A κ v arR2` for any template `A`
whose fields are `askTG`'s) and the bits (`bitRows4`), once they fit (`ArFit`). Here:

* **`arFit_of`**: on `one = 1`, the statement's M rows give `ArFit` (else a slot's rejecting row fails).
* **`askRowsX_trail`**: B3's `askRowsX` is `trailRows` at the template's fields; **`askRowsP_eq`**.
* **`askFold`**: `askIRows4 A κ v arR2 ⊆ nodeIRows4 κ` for every template `A` with `askTG`'s fields
  (the hypothesis `hfoldA` of B3's `gap4Imp_of_run`, IMP's `gap4Imp_of_runI`, SRA's `gap4Imp_of_rsv`);
  **`askFold_rsv`**: at `withRsv (fun _ => AT.none)`, today's template (`input` + reserve).
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

/-- **Today's template** (SRA's `withRsv` at the empty ask template: IMP's `input`, SRA's reserve)
has `askTG`'s fields. -/
theorem withRsv_none (π : ℕ) :
    (withRsv (fun _ => AT.none) π).cov = (askTG π).cov ∧ (withRsv (fun _ => AT.none) π).rows = (askTG π).rows :=
  ⟨rfl, rfl⟩

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

/-- **Today's fold** (`input` + reserve: SRA-RESULT §6.1's request): `askIRows4 (withRsv (fun _ =>
AT.none)) κ v arR2 ⊆ nodeIRows4 κ`. -/
theorem askFold_rsv {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withRsv fun _ => AT.none) κ v arR2, p ∈ nodeIRows4 κ :=
  askFold (fun π _ => withRsv_none π) hone hE

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
