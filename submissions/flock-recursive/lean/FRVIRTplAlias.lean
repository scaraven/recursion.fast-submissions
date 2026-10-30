-- New for `flock-recursive` (stage FEL, design `FEL.md` with review S3): the `dotKF` arm with aliased
-- column cells, as an override of `tplExt4` at `dotKF` only, and its soundness.
import FRVIRTplSet

/-!
# `tplExt4A`: `tplExt4` with the `dotKF` column cells aliased

`tplExt`'s `dotKF w col` arm gives the template instance fresh auxiliary cells for the column's `n` `F`
elements (`aux := [(cells, col, .felems n)]`), which no row binds. **`tplExt4A F R tc al`** is `tplExt4 F R
tc` at every op but `dotKF`; at `dotKF w col` (with `w`'s slot `.ak n`, the key kept by `F`, `col` an
existing register) it takes the cells `al col n` instead, and **refuses** the op (no template: the compile
makes it an import) where `al col n = none`. The instance's rows, inputs `lw ++ cells` and auxiliary entry
are the arm's, so its soundness is `tplExt_ok`'s `dotKF` case, which uses the cells only through the
auxiliary fact (`dkX_ok`; the `ImplTF` step is void: `dotKF` reads no `OpImpl` field).

* **`tplExt4A_ne`**: at any other op it is `tplExt4`;
* **`tplExt4A_okK`**: sound at the run's kind, as `tplExt4_okK`.
-/

namespace FR
namespace Circ
open Tpl RecursionFast

/-- **The aliased `dotKF` arm**: `w`'s slot `.ak n`, the key `dotKF n` kept, `col` an existing register,
the cells `al col n` (none: refused). -/
def dkA (F : TFilt) (tc : TCtx) (al : ℕ → ℕ → Option (List Lin)) (P : Params) (cs : CS) (w col : ℕ) :
    Option Out :=
  match cs.slot w with
  | some (.ak n, lw) =>
    if F (.dotKF n) = true ∧ col < cs.slots.size then
      (al col n).map fun cells =>
        { tplOut tc P cs (.dotKF n) (lw ++ cells) [.k] with aux := [(cells, col, .felems n)] }
    else none
  | _ => none

/-- **`tplExt4` with the `dotKF` arm aliased** (`al`: a column register and a length to the cells). -/
def tplExt4A (F : TFilt) (R : ShR) (tc : TCtx) (al : ℕ → ℕ → Option (List Lin)) : Ext := fun P cs op =>
  match op with
  | .dotKF w col => dkA F tc al P cs w col
  | _ => tplExt4 F R tc P cs op

/-- The arm alone, as an extension. -/
def dkX (F : TFilt) (tc : TCtx) (al : ℕ → ℕ → Option (List Lin)) : Ext := fun P cs op =>
  match op with
  | .dotKF w col => dkA F tc al P cs w col
  | _ => none

/-- At an op other than `dotKF`, `tplExt4A` is `tplExt4`. -/
theorem tplExt4A_ne {F : TFilt} {R : ShR} {tc : TCtx} {al : ℕ → ℕ → Option (List Lin)} {P : Params}
    {cs : CS} {op : Op} (h : ∀ w col, op ≠ .dotKF w col) : tplExt4A F R tc al P cs op = tplExt4 F R tc P cs op := by
  cases op <;> first | rfl | exact absurd rfl (h _ _)

/-- **What the aliased arm gives**: the cells `al col n`, `col` an existing register, its one auxiliary
entry, no import, not foreign. -/
theorem dkA_some {F : TFilt} {tc : TCtx} {al : ℕ → ℕ → Option (List Lin)} {P : Params} {cs : CS}
    {w col : ℕ} {o : Out} (h : dkA F tc al P cs w col = some o) :
    ∃ n cells, al col n = some cells ∧ col < cs.slots.size ∧ o.aux = [(cells, col, .felems n)] ∧
      o.imp = false ∧ o.foreign = false := by
  unfold dkA at h
  split at h
  · rename_i n lw _
    split_ifs at h with hF
    obtain ⟨cells, hc, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨n, cells, hc, hF.2, rfl, rfl, rfl⟩
  · cases h

/-- **Whether the aliased arm takes an op does not depend on the template bodies.** -/
theorem dkA_isNone (F : TFilt) (tp tp' : TKey → Tpl) (cb : TKey → ℕ → ℕ) (al : ℕ → ℕ → Option (List Lin))
    (P : Params) (cs : CS) (w col : ℕ) :
    (dkA F ⟨tp, cb⟩ al P cs w col).isNone = (dkA F ⟨tp', cb⟩ al P cs w col).isNone := by
  unfold dkA
  split
  · split_ifs <;> simp
  · rfl

/-- **The aliased arm is sound** (`tplExt_ok`'s `dotKF` case, with the cells `al col n`). -/
theorem dkX_ok {impl : OpImpl} (F : TFilt) (L : TLay) (al : ℕ → ℕ → Option (List Lin)) :
    ExtOk impl L.ctx (dkX F L.ctx al) := by
  intro P cs op o hX
  cases op <;> simp only [dkX, reduceCtorEq] at hX
  rename_i w col
  simp only [dkA] at hX
  split at hX
  · rename_i n lw hw
    split_ifs at hX with hF
    obtain ⟨cells, -, rfl⟩ := Option.map_eq_some_iff.1 hX
    refine ⟨rfl, fun κ inp ww regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht hx vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx', rfl, hxl⟩ := rep_ak (rep_slot hI hw)
    have hc := hx _ (List.mem_singleton_self _)
    simp only [Tpl.AuxK.val] at hc
    rw [hx', dotKFF_eq]
    exact outSlots_one rfl (tplDotKF_ok rfl (inpIs_of (by rw [List.map_append, hxl, hc]; rfl))
      (tin_eqns (tc := L.ctx) (k := .dotKF x.size) (tys := [.k]) hP.1 ht))
  · cases hX

/-- The arm sets no per-kind slot. -/
theorem dkX_kin {F : TFilt} {tc : TCtx} {al : ℕ → ℕ → Option (List Lin)} {P : Params} {cs : CS} {op : Op}
    {o : Out} (h : dkX F tc al P cs op = some o) : o.kin = none := by
  cases op <;> simp only [dkX, reduceCtorEq] at h
  simp only [dkA] at h
  split at h
  · split_ifs at h
    obtain ⟨cells, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

/-- **`tplExt4A` is sound at kind `κ`** (with per-kind slots), under `tplExt4_okK`'s hypotheses. -/
theorem tplExt4A_okK {impl : OpImpl} {F : TFilt} {R : ShR} {κ : Kind} (hT : ImplTF F impl)
    (hR : RouteOk R impl κ) (L : TLay) (al : ℕ → ℕ → Option (List Lin)) :
    ExtOkK impl L.ctx (tplExt4A F R L.ctx al) κ := by
  intro P cs op o h
  by_cases hd : ∃ w col, op = .dotKF w col
  · obtain ⟨w, col, rfl⟩ := hd
    exact ((dkX_ok F L al).at κ).toK (fun _ _ _ _ h => dkX_kin h) P cs _ o h
  · rw [tplExt4A_ne fun w col he => hd ⟨w, col, he⟩] at h
    exact tplExt4_okK hT hR L P cs op o h

/-! ## Controls -/

/-- A context with one empty template per key and cell base `0`. -/
def ctlTC : TCtx := ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩

/-- A compile with register `0` of type `ak 2` (forms `[c₀, c₁, c₂, c₃]`) and register `1`. -/
def ctlCSA : CS := { CS.init 10 with slots := #[some (.ak 2, [Lin.cell 0, Lin.cell 1, Lin.cell 2, Lin.cell 3]), none] }

/-- (+) **The alias arm** takes `dotKF 0 1` with the given cells: they are its auxiliary entry and the
instance's inputs follow `w`'s forms; (−) with `al = none` it refuses (no template); (−) a column that is not
yet a register (`5 ≥ 2`) is refused; (−) an op other than `dotKF` is `tplExt4`'s. -/
theorem dkA_ctl :
    ((tplExt4A allK .imp ctlTC (fun _ _ => some [Lin.cell 7, []]) (⟨Lin.cell 0, fun _ => []⟩ : Params) ctlCSA
        (.dotKF 0 1)).map fun o => (o.aux, o.tin)) =
      some ([([Lin.cell 7, []], 1, .felems 2)],
        some (.dotKF 2, [Lin.cell 0, Lin.cell 1, Lin.cell 2, Lin.cell 3, Lin.cell 7, []])) ∧
    (tplExt4A allK .imp ctlTC (fun _ _ => none) (⟨Lin.cell 0, fun _ => []⟩ : Params) ctlCSA (.dotKF 0 1)).isNone ∧
    (tplExt4A allK .imp ctlTC (fun _ _ => some []) (⟨Lin.cell 0, fun _ => []⟩ : Params) ctlCSA (.dotKF 0 5)).isNone ∧
    tplExt4A allK .imp ctlTC (fun _ _ => none) (⟨Lin.cell 0, fun _ => []⟩ : Params) ctlCSA (.eqZ 0 1) =
      tplExt4 allK .imp ctlTC (⟨Lin.cell 0, fun _ => []⟩ : Params) ctlCSA (.eqZ 0 1) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Circ
end FR
