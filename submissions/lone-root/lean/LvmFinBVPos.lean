-- New for lvm (WP-16a2, FIN-BV): `harith_core`'s position facts `PosOk` at the `P20` node program.
-- Route (HAR §3): Q_link's position cells (QL's `qlink_pos`: the sum of the position's two `BITS`
-- fields, A20), the position classes' `fld` outputs (WP-12b's `out1_at`), the fields' sum is
-- Q_link's `posL` (new: `fields_posL`), and `F` reads the same number (HAR-POS's `qsAt_posL`).
import LvmFinBV
import LvmFinPos

/-!
# The position cells hold `F`'s positions

* (`fields_posL`, `PosLanes`, `posOk_of`: moved to `LvmFinPos`, lvm2 roll 8, wave L.)
* **`posVal_of`** (any configuration): in the interpreter's memory, a position's two field cells add
  up to `kOf (posL …)`.
* **`posOkR20`**: `harith_core`'s `hposr` at `cfg20` (B1; `posOkM20` removed at M′).
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Bits Lvm.NS Lvm.QAsm Lvm.Har LeanVM.Protocol

-- The field and position lemmas (`ubit_fld` … `hi_mem`): `LvmFinPos`.

/-- An output of a position class's row, in `Out1` form: the output `e` of opening `k`'s lane-`l` row
(`laneOuts`), written by a row of lane class `l` (`posSpecs_hit`). -/
theorem out1_entry {Q : Program} {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr}
    {aux : List Tab} {L : Lay} {hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ} {q : Column L.μ}
    (H : AuxHyps Q pl groups arrs aux L hτ q) (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) {k l x : ℕ} {o : OpenInfo}
    (hk : k < (opens C.p).length) (ho : (opens C.p).getD k default = o) (hl : l < QAsm.nLanes o.L.height)
    (hx : x < nRows o) {e : BOut × ℕ × ℕ} (he : e ∈ laneOuts o.L.height l) (hv : e.1.Valid) :
    Out1 (memK Q pl groups arrs aux L hτ q) (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e) := by
  subst ho
  obtain ⟨S, hS, hτS, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ := posSpecs_hit C bpl hk hl hx he
  exact out1_at Q pl groups arrs aux L hτ q H S (haux _ hS) hτS hrd y jo hy hjo
    (posCellsLt_spec hpc bpl hS hy) hwc hoc hout hv

/-- **A position's two field cells add up to `kOf (posL …)`** in the interpreter's memory (the position
classes' `fld` outputs on the answer lanes, the stream cells `hs`). -/
theorem posVal_of {Q : Program} {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr}
    {aux : List Tab} {L : Lay} {hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ} {q : Column L.μ}
    (H : AuxHyps Q pl groups arrs aux L hτ q) (C : QCfg) (bpl : ℕ → ℕ → Bool × ℕ)
    (haux : ∀ S ∈ posSpecs C bpl, S.tab ∈ aux) (hpc : PosCellsLt Q C) (hS : StreamOk C.p)
    (hQ : QOk C.p (lay C)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, memK Q pl groups arrs aux L hτ q ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    memK Q pl groups arrs aux L hτ q ((lay C).fl + posIdx C.p k j) +
        memK Q pl groups arrs aux L hτ q ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8) (j % 8 * ((opens C.p).getD k default).L.height)
        ((opens C.p).getD k default).L.height) := by
  generalize hoD : (opens C.p).getD k default = o at hH hj ⊢
  have ho : o ∈ opens C.p := by
    rw [← hoD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hj
  obtain ⟨hp1, hp2, -, -, -⟩ := hQ.opens _ ho
  have hin := lanes_in hS h1 hlt
  have hT := hQ.hT
  have hx : j / 8 < nRows o := by
    have := lt_padT hj; unfold nRows; omega
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hji : 8 * (j / 8) + j % 8 = j := by omega
  have hsH : j % 8 * o.L.height ≤ 7 * o.L.height := Nat.mul_le_mul_right _ (by omega)
  -- the two field entries, their lanes and validity
  have hl1 : (fields o.L.height (j % 8)).1.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; omega
  have hl2 : (fields o.L.height (j % 8)).2.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; split_ifs <;> omega
  have hv1 : (BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have hv2 : (BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have o1 := out1_entry H C bpl haux hpc hk hoD hl1 hx (lo_mem o.L.height hj8) hv1
  have o2 := out1_entry H C bpl haux hpc hk hoD hl2 hx (hi_mem o.L.height hj8) hv2
  have c1 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2), 1, j % 8) = (lay C).fl + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte, Nat.add_zero]; rfl
  have c2 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2), 2, j % 8) = (lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte]; rfl
  have hlane : ∀ l ≤ 2, ansLane C.p (o.pe + j / 8) + l < 2 ^ (lay C).m := by
    intro l hl
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by omega)]; omega
  have hl1' : (fields o.L.height (j % 8)).1.1 ≤ 2 := by
    simp only [fields]; omega
  have hl2' : (fields o.L.height (j % 8)).2.1 ≤ 2 := by
    simp only [fields]; split_ifs <;> omega
  have hs' : ∀ l < 2 ^ (lay C).m, memK Q pl groups arrs aux L hτ q l = laneK ws l := fun l hl => by
    have := hs l hl; rwa [show (lay C).sb = 0 from rfl, Nat.zero_add] at this
  unfold Out1 at o1 o2
  rw [← c1, ← c2, o1, o2, hs' _ (hlane _ hl1'), hs' _ (hlane _ hl2')]
  exact fields_posL C.p ws (o.pe + j / 8) (by omega) hH h192

-- `PosLanes`, `posOk_of`: `LvmFinPos`.

section P20

theorem cfg20_p : cfg20.p = P20 := by unfold cfg20; rfl

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}
  {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}

/-- **The position cells of the `P20` node program** (Q_link's `posLoop`, `qlink_pos`) hold
`kOf (posL …)` of the child's stream, on a good pair with the input map. -/
theorem posCells20
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D)
      (arrsX x))
    (hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 (lay cfg20))
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodN T hτ x qm qr)
    (mp : InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm
      qr) :
    ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t,
      (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr).k
          (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height) ((opens P20).getD k default).L.height) := by
  intro k hk hH j hj
  have H := auxH20 hT hst hinb hok hb hG
  obtain ⟨hl, -, -⟩ := parts_of_aux H
  have hk' : k < (opens cfg20.p).length := by rw [cfg20_p]; exact hk
  have hH' : ((opens cfg20.p).getD k default).L.height ≤ 64 := by rw [cfg20_p]; exact hH
  have hj' : j < ((opens cfg20.p).getD k default).L.t := by rw [cfg20_p]; exact hj
  have hv := posVal_of H cfg20 (fun c => bplOf D (6 + c)) (fun _ h => posSpecs_aux cfg20 D h) hpc
    (by rw [cfg20_p]; exact hS) (by rw [cfg20_p]; exact hQ) mp.stream hk' hH' hj'
  rw [cfg20_p] at hv
  have hq := qlink_pos (pt := p0 (nK cfg20) 0) hQ hl.1 hk hj
  exact hq.trans hv

/-- **`harith_core`'s `hposr`**: `C_rec`'s position cells hold `F`'s positions. -/
theorem posOkR20
    (hT : ∀ x, T x = lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
      (aux cfg20 D))
    (hst : ∀ x, AuxStatic (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups (aux cfg20 D)
      (arrsX x))
    (hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0).interp
        (inKOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))
        (inEOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x) (aux cfg20 D)
          lay26 (hτ' x) (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 (lay cfg20))
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hPL : PosLanes P20 P20.grind P20.recOod P20.recLevels (openU P20 + 15) 0) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
      PosOk (cfgRec P20 (posBase cfg20) (pwBase cfg20))
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' x qm qr)
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) 0 P20.recLevels (openU P20 + 15) := by
  intro vk c x qm qr hok hb hG mp hL
  exact posOk_of _ 0 (fun i => by rw [Nat.zero_add]; rfl) hPL hS hL hQ
    (posCells20 hT hst hinb hS hQ hpc hok hb hG mp)

-- (R11-IS, M′: `posOkM20` is removed: the bus path's `C_main` positions after B1's `C_rec` opening; no consumer.)

end P20

end Lvm.Fin
