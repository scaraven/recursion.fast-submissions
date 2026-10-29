-- New for `flock-recursive` (revision 4.4.1, track CK: SRA's finding §4.2).
import FRVIRCompileSound

/-!
# `getK` of a kind-muxed array: `extGetK`, `extGetK_okK`

The group-uniform prototype 0 selects `finPf`'s points by the kind (`FRVIRFinals4.gFinPf`: five
`keep selA` over the `m*` family's and the other family's `packK`, of lengths `n` and `n − 1`). The
plain compile tracks a `keep` only over one type (`opOut`), so the kind mux (`tplExtKM`, S-E12f)
gives the result **per-kind slots** (`CS.kslots`: at kind `κ`, the kind's operand) and no kind-free
slot. `tensorW` on such a point is templated per kind (`.tensorWK`), but `getK` fell back to
`opOut`, which leaves it untracked: `P₀`'s coordinates `ρ_v`, and the 852 registers of `finPf`'s
cell and level sums after them, were not in the rows, so its final `assertEq` (op#109053) was a
foreign flag (SRA §4.2).

**`extGetK`**: a `getK a i` whose register `a` has no kind-free slot (`opOut` would skip it) but a
slot at every kind gets, per `F` component, the kind mux of the kinds' forms (`mux3`): the common
form if the three agree, else three fresh cells `c_κ` with the rows `sel_κ · x_κ = c_κ` and the form
`c_L + c_P + c_N`. Beyond a kind's length the form is `[]` (`0`), which is `getK`'s value there
(`Array.getD … 0`). **`extGetK_okK`**: it is sound at every kind with per-kind slots (`ExtOkK`).
`FRVIRTplSet.tplExt4` runs it after `tplExtKM`.
-/

namespace FR
namespace Circ
open RecursionFast

/-- **A kind mux of three forms** (fresh cells `o … o + 2`): their common form if the three kinds'
agree, else `c_L + c_P + c_N` with the rows `sel_κ · x_κ = c_κ`. -/
def mux3 (P : Params) (cs : CS) (x : Kind → Lin) (o : ℕ) : Lin × List Row :=
  if x .L32 = x .P30 ∧ x .P30 = x .N30 then (x .L32, [])
  else (cs.cell o ++ cs.cell (o + 1) ++ cs.cell (o + 2),
    [⟨P.sel .L32, x .L32, cs.cell o⟩, ⟨P.sel .P30, x .P30, cs.cell (o + 1)⟩,
     ⟨P.sel .N30, x .N30, cs.cell (o + 2)⟩])

/-- **The mux is the kind's form** when the selectors are one-hot at `κ` and its rows hold. -/
theorem mux3_ev {w : Asg} {P : Params} {cs : CS} {x : Kind → Lin} {o : ℕ} {κ : Kind}
    (hP : SelOk w P κ) (hr : ∀ r ∈ (mux3 P cs x o).2, r.Holds w) :
    (mux3 P cs x o).1.ev w = (x κ).ev w := by
  unfold mux3 at hr ⊢
  split_ifs at hr ⊢ with h
  · obtain ⟨e1, e2⟩ := h; cases κ <;> simp [e1, e2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Row.Holds,
      hP.2] at hr
    obtain ⟨q1, q2, q3⟩ := hr
    simp only [Lin.ev_append, ← q1, ← q2, ← q3]
    cases κ <;> simp

/-- Component `j` of element `i` of register `a` at kind `κ` (its per-kind slot's form; `[]` beyond
the kind's length). -/
def gkForm (cs : CS) (a i j : ℕ) (κ : Kind) : Lin := (asAK (cs.slotK a κ)).getD (2 * i + j) []

/-- Whether `a` has no kind-free slot (`opOut` skips its `getK`) but a slot at every kind. -/
def kindTyped (cs : CS) (a : ℕ) : Bool :=
  (cs.slot a).isNone && kinds.all fun κ => (cs.slotK a κ).isSome

/-- **`getK a i` of a kind-muxed register**: per `F` component, the kinds' forms muxed (`mux3`;
six fresh cells, six rows unless the kinds' forms agree). -/
def getKK (P : Params) (cs : CS) (a i : ℕ) : Out :=
  let m0 := mux3 P cs (gkForm cs a i 0) 0
  let m1 := mux3 P cs (gkForm cs a i 1) 3
  { slots := [some (.k, [m0.1, m1.1])], rows := m0.2 ++ m1.2, fresh := 6 }

/-- **The extension**: `getK` of a kind-muxed register (`kindTyped`); every other op is left. -/
def extGetK : Ext := fun P cs op =>
  match op with
  | .getK a i => if kindTyped cs a then some (getKK P cs a i) else none
  | _ => none

/-- **`extGetK` is sound at every kind, with per-kind slots.** -/
theorem extGetK_okK {impl : OpImpl} {tc : Tpl.TCtx} {κ : Kind} : ExtOkK impl tc extGetK κ := by
  intro P cs op o hX
  cases op <;> simp only [extGetK, reduceCtorEq] at hX
  rename_i a i
  split_ifs at hX with ha
  simp only [Option.some.injEq] at hX; subst hX
  refine ⟨rfl, fun h => by simp [getKK] at h, fun inp w regs hP _ hK =>
    ⟨fun q => by simp [evalOp], fun hr _ _ vs ok he => ?_⟩⟩
  simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun _ => List.Forall₂.cons ?_ List.Forall₂.nil, fun _ => rfl, fun f v hf => by
    simp [getKK] at hf⟩
  have hs : (cs.slotK a κ).isSome := by
    simp only [kindTyped, kinds, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at ha
    cases κ <;> simp_all
  obtain ⟨⟨t, ls⟩, e⟩ := Option.isSome_iff_exists.1 hs
  have r := hK a; rw [e] at r
  have hx := flatMap_encK_getD (rd regs a).toAK.toList i
  have h0 := (getD_ev (asAK_ev r) (2 * i)).trans hx.1
  have h1 := (getD_ev (asAK_ev r) (2 * i + 1)).trans hx.2
  have m0 := mux3_ev (cs := cs) (x := gkForm cs a i 0) (o := 0) hP
    (fun r h => hr r (List.mem_append_left _ h))
  have m1 := mux3_ev (cs := cs) (x := gkForm cs a i 1) (o := 3) hP
    (fun r h => hr r (List.mem_append_right _ h))
  simp only [gkForm, e, Nat.add_zero] at m0 m1
  rw [h0] at m0; rw [h1] at m1
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList] at m0 m1
  simp only [RepS, tyOf, encV, encK, List.map_cons, List.map_nil, true_and]
  simp [m0, m1]

/-! ## Controls -/

/-- The controls' state: register `0` an `ak 2` on cells `0 … 3`, register `1` an `ak 1` on cells
`4, 5`, register `2` kind-muxed (`L32`: register `0`; else register `1`; no kind-free slot),
register `3` kind-muxed with register `0` at every kind. -/
def ctlCSG : CS :=
  { next := 8
    slots := #[some (.ak 2, [Lin.cell 0, Lin.cell 1, Lin.cell 2, Lin.cell 3]),
      some (.ak 1, [Lin.cell 4, Lin.cell 5]), none, none]
    rows := [], imp := [], fors := []
    kslots := [(2, fun κ => if κ = .L32 then some (.ak 2, [Lin.cell 0, Lin.cell 1, Lin.cell 2, Lin.cell 3])
        else some (.ak 1, [Lin.cell 4, Lin.cell 5])),
      (3, fun _ => some (.ak 2, [Lin.cell 0, Lin.cell 1, Lin.cell 2, Lin.cell 3]))] }

/-- (+) `getK` of the kind-muxed register is tracked (`K`), with six mux rows for element `0`
(`L32`'s cells `0, 1`, the others' `4, 5`) and for element `1` (beyond the shorter kinds' length:
`L32`'s cells `2, 3`, else `0`); (+) when the kinds' forms agree, no row (register `3`); (−) a
register with a kind-free slot is left to `opOut` (register `0`), and so is one with no slot at some
kind (`CS.init`). -/
theorem extGetK_ctl :
    ((extGetK ⟨[], fun _ => []⟩ ctlCSG (.getK 2 0)).map fun o => (o.slots.map (·.map (·.1)), o.rows.length))
        = some ([some .k], 6) ∧
      ((extGetK ⟨[], fun _ => []⟩ ctlCSG (.getK 2 1)).map (·.rows.length)) = some 6 ∧
      ((extGetK ⟨[], fun _ => []⟩ ctlCSG (.getK 3 1)).map (·.rows.length)) = some 0 ∧
      (extGetK ⟨[], fun _ => []⟩ ctlCSG (.getK 0 0)).isNone = true ∧
      (extGetK ⟨[], fun _ => []⟩ (CS.init 0) (.getK 0 0)).isNone = true := by
  decide +kernel

/-- (−) **The mux is needed**: register `2`'s element `1` has a different form at `L32` (cell `2`)
than at `P30` (none: `0`), so no kind-free form represents it at every kind. -/
theorem gkForm_ctl : gkForm ctlCSG 2 1 0 .L32 = Lin.cell 2 ∧ gkForm ctlCSG 2 1 0 .P30 = [] := by
  decide +kernel

end Circ
end FR
