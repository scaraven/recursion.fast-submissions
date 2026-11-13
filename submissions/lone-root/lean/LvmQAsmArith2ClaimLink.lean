-- New for lvm (HAR-RC): the claims of the link phases (5: `CH` link, `chLink0`'s two ring claims and
-- 17 constant-lane claims; 7: `KS` link, `ksLink0`'s four `sumClaim`s) as cells, every challenge and
-- scalar loaded from its stream lanes. Reused: QA1's reading (`chLinkView`, `ksLinkView`, lane
-- functions `chQ1 … chQC`, `take_range_map`, `drop_range_map`, `scSpec_fst_getD`), HAR's
-- `chLinkPh_run`/`ksLinkPh_run`, QA2's `eqTab_eq` (the `KS` link's `eq(λ, ·)`), this family's `ringG`.
import LvmQAsmArith2Claim
import LvmQWhirBatch

/-!
# Q_arith: the claims of the link phases

* **`chLinkG n Q z o blk ySlot`** (phase 5 from the reader at `P`, `P + 40 = 8 Q`): loads `ρ'` (the
  shift sumcheck's `n` challenges), `λ` (3), `μ` (the two-round sumcheck's 2 challenges), the two
  ring switches (`ringG` on the `in`/`Y` slices and their challenges), one constant cell; returns
  `chLinkC`: the two ring claims at `(ρ', λ, 0, 0, 0)` and `(ρ', μ, slot bits)`, the 17 constant
  lanes at `(ρ', slot l)`. **`chLinkG_val`**: the cells are `(chLink0 p blk ySlot (chLinkView …)).2`;
  `chLinkPh_claims`: `F`'s phase-5 claims (`chLinkPh`) for `m = M3.ofParts p …` (any bus/table parts).
* **`ksLinkG p Q z o`** (phase 7): loads `λ` (5), `ρ'` (`ksLog`), the four scalars; `eq(λ, ·)` by
  QA2's `eqTab`; returns `ksLinkC`: the four `sumClaim`s. **`ksLinkG_val`**, `ksLinkPh_claims`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig DM

variable {c : Ctx} {M : Mem}

/-! ## `F`'s side -/

theorem scSpec_fst (v : Nat → FE) (count : Nat) (es : List (Option FE)) (p : Nat) (claim : FE) :
    (scSpec v count p claim es).1 =
      (List.range es.length).map fun i => v (p + i * roundLen count + 40 + 24 * (count - 1)) := by
  refine List.ext_getElem (by rw [lnk_scSpec_length]; simp) fun i h1 h2 => ?_
  have e := scSpec_fst_getD v count i es p claim (by rw [lnk_scSpec_length] at h1; exact h1)
  rw [List.getD_eq_getElem _ _ h1] at e
  rw [e]
  simp

/-! ## The `KS` link -/

/-- `λ`'s lanes (samples `ksLog … ksLog + 4`), `ρ'`'s (the shift sumcheck's answers), the four
scalars'. -/
def ksLamL (p : Params) (Q : Nat) : List Nat := (List.range laneBits).map fun j => Q + 9 * (p.ksLog + j)
def ksRhoL (p : Params) (Q : Nat) : List Nat :=
  (List.range p.ksLog).map fun i => Q + 9 * (p.ksLog + laneBits) + 6 + 15 * i
def ksValL (p : Params) (Q : Nat) : List Nat :=
  (List.range 4).map fun k => Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 3 * k

/-- The `KS` link's claims as cells (`om`: `eq(λ, ·)`, `rho'`, `vals`: the four scalars). -/
def ksLinkC (p : Params) (z o : Nat) (om rho' vals : List Cell) : List CClaim :=
  let L := layout0 p
  let lo := rho'.take p.recRowsLog
  [⟨.main, .sum p.nuMain ((List.range 25).map fun l =>
      (om.getD l default, (ksYPartC p l rho' z o).1, (ksYPartC p l rho' z o).2)), vals.getD 0 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 25).map fun l =>
      (om.getD l default, ⟨p.ksLog + slotLog, L.ks⟩, rho' ++ selC z o l slotLog)), vals.getD 1 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 17).map fun l =>
      (om.getD l default, ⟨p.recRowsLog, L.s + l * 2 ^ p.recRowsLog⟩, lo)), vals.getD 2 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 17).map fun l =>
      (om.getD l default, ⟨p.recRowsLog, L.x + l * 2 ^ p.recRowsLog⟩, lo)), vals.getD 3 default⟩]

/-- **The `KS` link's claims in v1's layout** (phase 7; `P + 40 = 8 Q`). -/
def ksLinkGV1 (p : Params) (Q z o : Nat) : BM (List CClaim) := do
  let pl ← getPtr
  let _ ← loadAt (ksLamL p Q)
  let rho' ← loadAt (ksRhoL p Q)
  let vals ← loadAt (ksValL p Q)
  let eb ← eqTab (fun i => ec (pl.e + i)) (ec z) (ec o) false laneBits
  pure (ksLinkC p z o ((List.range 32).map fun l => ec (eb + l)) rho' vals)

theorem vs_take (M : Mem) (l : List Cell) (n : Nat) : vs M (l.take n) = (vs M l).take n := by
  simp [vs, List.map_take]

theorem ksLinkC_val (p : Params) {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1)
    (om rho' vals : List Cell) (i : KsLinkIn) (hom : vs M om = eqKernel (i.chal.drop p.ksLog))
    (homl : om.length = 32) (hrho : vs M rho' = i.shift.1) (hvals : vs M vals = i.vals)
    (hvl : vals.length = 4) :
    (ksLinkC p z o om rho' vals).map (CClaim.val M) = (ksLinkV1 p i).2 := by
  have hc : ∀ l < 32, (om.getD l default).val M = (eqKernel (i.chal.drop p.ksLog)).getD l 0 := by
    intro l hl; rw [vs_getD M om (by omega), hom]
  have hv : ∀ k < 4, (vals.getD k default).val M = i.vals.getD k 0 := by
    intro k hk; rw [vs_getD M vals (by omega), hvals]
  simp only [ksLinkC, ksLinkV1, List.map_cons, List.map_nil, CClaim.val, List.map_map, vs_take, hrho,
    hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega)]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_,
    List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩⟩
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    have e := ksYPartC_val (M := M) p l rho' hz ho
    rw [hrho] at e
    simp only [Function.comp_apply, hc l (by omega)]
    rw [← e]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_append, hrho, selC_vs hz ho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_take, hrho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_take, hrho]

theorem eqKernel_getD_A (pt : List FE) (x : Nat) : (eqKernel pt).getD x 0 = (eqKernelA pt).getD x 0 := by
  rw [← eqKernelA_toList, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **Q_arith_eq, the `KS` link's claims in v1's layout**: with the reader at `P` (`P + 40 = 8 Q`) the cells are
`ksLinkV1`'s claims on what `F` reads in phase 7 (any `M3` `m`). -/
theorem ksLinkGV1_val (p : Params) (m : M3) {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr}
    (rk : List FE) (pub : Pub) (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T)
    (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (ksLinkGV1 p Q z o ptr).2) :
    (ksLinkGV1 p Q z o ptr).1.map (CClaim.val M) = (ksLinkV1 p (ksLinkView p m (feAt sig) P rk pub)).2 := by
  simp only [ksLinkGV1] at h ⊢
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h; obtain ⟨-, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h3, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h4, -⟩ := h
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _)]
  simp only [bind_apply, pure_apply]
  set lamF : List FE := (List.range laneBits).map fun j => feAt sig (P + 40 + 72 * (p.ksLog + j))
    with hlamF
  have hlam : (ksLinkView p m (feAt sig) P rk pub).chal.drop p.ksLog = lamF := by
    simp only [ksLinkView, samplesAt]
    rw [drop_range_map, show p.ksLog + laneBits - p.ksLog = laneBits by omega]
  have hll : lamF.length = laneBits := by simp [hlamF]
  have hL := loadAt_e hS (ksLamL p Q) ptr (fun q hq => by
    simp only [ksLamL, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only [laneBits] at hj hT ⊢; omega) h1
  have hE := eqTab_eq (fun i => ec (ptr.e + i)) (ec z) (ec o) false lamF (by rw [hll]; exact h4) hz
    (fun _ => rfl) ho (fun i hi => by
      rw [hll] at hi
      rw [Cell.val_E, hL i (by simp [ksLamL, hi])]
      simp only [ksLamL, hlamF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some]
      congr 1; omega)
  rw [hll] at hE
  refine ksLinkC_val p hz ho _ _ _ _ ?_ (by simp) ?_ ?_ (by rw [loadAt_out]; simp [ksValL])
  · rw [hlam]
    refine List.ext_getElem (by simp [vs, Build.eqKernel_length, hll, laneBits]) fun x h1 h2 => ?_
    simp only [vs, List.length_map, List.length_range] at h1
    simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
    have e := hE x (by simpa [laneBits] using h1)
    simp only [if_false, Bool.false_eq_true] at e
    rw [e, ← eqKernel_getD_A, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksRhoL, List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      simp only [laneBits] at hT ⊢; omega) h2]
    simp only [ksLinkView, scSpec_fst, List.length_replicate, ksRhoL, List.map_map]
    refine List.map_congr_left fun i _ => congrArg (feAt sig) ?_
    simp only [ksP1, roundLen, laneBits]; omega
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksValL, List.mem_map, List.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      omega) h3]
    simp only [ksLinkView, scalarsAt, ksValL, List.map_map]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [ksP2, ksP1, roundLen, laneBits]; omega

/-! ### KS14 (lvm2 CR-K)

`M`'s claim has 17 more parts on the rows from the split, with coefficients `eq(λ, l)·sel(ρ')`: entries
`l + 32·(2^w − 1)` of a second `eq` table over `λ ‖ ρ'_{xl…}` (`w = ksLog − xl` coordinates of `ρ'`, all one). -/

/-- The second table's width: `λ`'s 5 coordinates and `ρ'`'s `ksLog − xl`. -/
def ksSelW (p : Params) : Nat := laneBits + (p.ksLog - ksXLog p)

/-- The index of `eq(λ, l)·sel` in the second table. -/
def ksTop (p : Params) : Nat := 32 * (2 ^ (p.ksLog - ksXLog p) - 1)

/-- The second table's coordinate cells: `λ`'s (`pl.e + i`), then `ρ'`'s from `xl`. -/
def ksSelAl (p : Params) (pe : Nat) (rho' : List Cell) (i : Nat) : Cell :=
  if i < laneBits then ec (pe + i) else ec ((rho'.getD (ksXLog p + (i - laneBits)) (ec 0)).n)

/-- The `KS` link's claims as cells under KS14 (`om`: `eq(λ, ·)`; `oms`: `eq(λ ‖ ρ'_{xl…}, ·)`). -/
def ksLinkC14 (p : Params) (z o : Nat) (om oms rho' vals : List Cell) : List CClaim :=
  let L := layout0 p
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let xlo := rho'.take xl
  [⟨.main, .sum p.nuMain ((List.range 25).map fun l =>
      (om.getD l default, (ksYPartC p l rho' z o).1, (ksYPartC p l rho' z o).2)), vals.getD 0 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 25).map fun l =>
      (om.getD l default, ⟨p.ksLog + slotLog, L.ks⟩, rho' ++ selC z o l slotLog)), vals.getD 1 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 17).map (fun l =>
      (om.getD l default, ⟨p.ksLog, L.s + l * R⟩, rho')) ++ (List.range 17).map fun l =>
      (oms.getD (ksTop p + l) default, ⟨xl, L.s + l * R + ksSplit p⟩, xlo)), vals.getD 2 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 17).map fun l =>
      (om.getD l default, ⟨xl, L.x + l * R⟩, xlo)), vals.getD 3 default⟩]

/-- **The `KS` link's claims under KS14** (phase 7; `P + 40 = 8 Q`). -/
def ksLinkG14 (p : Params) (Q z o : Nat) : BM (List CClaim) := do
  let pl ← getPtr
  let _ ← loadAt (ksLamL p Q)
  let rho' ← loadAt (ksRhoL p Q)
  let vals ← loadAt (ksValL p Q)
  let eb ← eqTab (fun i => ec (pl.e + i)) (ec z) (ec o) false laneBits
  let es ← eqTab (ksSelAl p pl.e rho') (ec z) (ec o) false (ksSelW p)
  pure (ksLinkC14 p z o ((List.range 32).map fun l => ec (eb + l))
    ((List.range (2 ^ ksSelW p)).map fun l => ec (es + l)) rho' vals)

/-- **The `KS` link's claims** (phase 7): KS14's or v1's. -/
def ksLinkG (p : Params) (Q z o : Nat) : BM (List CClaim) :=
  if p.ksLog ≤ p.recRowsLog then ksLinkG14 p Q z o else ksLinkGV1 p Q z o

theorem eqW_ones : ∀ b : List FE, eqW b (2 ^ b.length - 1) = b.prod
  | [] => by simp [eqW]
  | r :: b => by
    have h1 : 1 ≤ 2 ^ b.length := Nat.one_le_two_pow
    have hm : (2 ^ b.length * 2 - 1) % 2 = 1 := by omega
    have hd : (2 ^ b.length * 2 - 1) / 2 = 2 ^ b.length - 1 := by omega
    simp only [eqW, List.length_cons, pow_succ, hm, hd, if_true, eqW_ones b, List.prod_cons]

theorem ksLinkC14_val (p : Params) {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1)
    (om oms rho' vals : List Cell) (i : KsLinkIn) (hom : vs M om = eqKernel (i.chal.drop p.ksLog))
    (homl : om.length = 32)
    (homs : ∀ l < 17, (oms.getD (ksTop p + l) default).val M =
      (eqKernel (i.chal.drop p.ksLog)).getD l 0 * prodE (i.shift.1.drop (ksXLog p)))
    (hrho : vs M rho' = i.shift.1) (hvals : vs M vals = i.vals) (hvl : vals.length = 4) :
    (ksLinkC14 p z o om oms rho' vals).map (CClaim.val M) = (ksLink14 p i).2 := by
  have hc : ∀ l < 32, (om.getD l default).val M = (eqKernel (i.chal.drop p.ksLog)).getD l 0 := by
    intro l hl; rw [vs_getD M om (by omega), hom]
  have hv : ∀ k < 4, (vals.getD k default).val M = i.vals.getD k 0 := by
    intro k hk; rw [vs_getD M vals (by omega), hvals]
  simp only [ksLinkC14, ksLink14, List.map_cons, List.map_nil, CClaim.val, List.map_map, List.map_append,
    vs_take, hrho, hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega)]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_,
    List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩⟩
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    have e := ksYPartC_val (M := M) p l rho' hz ho
    rw [hrho] at e
    simp only [Function.comp_apply, hc l (by omega)]
    rw [← e]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_append, hrho, selC_vs hz ho]
  · congr 2
    congr 1
    · refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      simp only [Function.comp_apply, hc l (by omega), hrho]
    · refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      simp only [Function.comp_apply, homs l hl', vs_take, hrho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_take, hrho]

/-- **Q_arith_eq, the `KS` link's claims under KS14** (`ksLog ≤ recRowsLog`, `4 ≤ ksLog`): the cells are
`ksLink14`'s claims on what `F` reads in phase 7. -/
theorem ksLinkG14_val (p : Params) (m : M3) {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr}
    (rk : List FE) (pub : Pub) (h14 : p.ksLog ≤ p.recRowsLog) (h4 : 4 ≤ p.ksLog) (hPQ : P + 40 = 8 * Q)
    (hS : Streamed M sig T)
    (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (ksLinkG14 p Q z o ptr).2) :
    (ksLinkG14 p Q z o ptr).1.map (CClaim.val M) = (ksLink14 p (ksLinkView p m (feAt sig) P rk pub)).2 := by
  have hxl : ksXLog p = p.ksLog - 4 := by simp only [ksXLog, if_pos h14]
  simp only [ksLinkG14] at h ⊢
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h; obtain ⟨-, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h3, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h4', h⟩ := h
  rw [hold_bind] at h; obtain ⟨h6, -⟩ := h
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _)]
  simp only [bind_apply, pure_apply]
  set lamF : List FE := (List.range laneBits).map fun j => feAt sig (P + 40 + 72 * (p.ksLog + j))
    with hlamF
  set rhoF : List FE := (ksLinkView p m (feAt sig) P rk pub).shift.1 with hrhoF
  have hlam : (ksLinkView p m (feAt sig) P rk pub).chal.drop p.ksLog = lamF := by
    simp only [ksLinkView, samplesAt]
    rw [drop_range_map, show p.ksLog + laneBits - p.ksLog = laneBits by omega]
  have hll : lamF.length = laneBits := by simp [hlamF]
  have hrhoL : rhoF = (ksRhoL p Q).map fun q => feAt sig (8 * q) := by
    simp only [hrhoF, ksLinkView, scSpec_fst, List.length_replicate, ksRhoL, List.map_map]
    refine List.map_congr_left fun i _ => congrArg (feAt sig) ?_
    simp only [ksP1, roundLen, laneBits]; omega
  have hrl : rhoF.length = p.ksLog := by rw [hrhoL]; simp [ksRhoL]
  have hL := loadAt_e hS (ksLamL p Q) ptr (fun q hq => by
    simp only [ksLamL, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only [laneBits] at hj hT ⊢; omega) h1
  have hlamv : ∀ i < laneBits, M.e (ptr.e + i) = lamF.getD i 0 := fun i hi => by
    rw [hL i (by simp [ksLamL, hi])]
    simp only [ksLamL, hlamF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    congr 1; omega
  have hE := eqTab_eq (fun i => ec (ptr.e + i)) (ec z) (ec o) false lamF (by rw [hll]; exact h4') hz
    (fun _ => rfl) ho (fun i hi => by rw [hll] at hi; rw [Cell.val_E, hlamv i hi])
  rw [hll] at hE
  -- the second table: `λ ‖ ρ'_{xl…}`
  have hRv := loadAt_e hS (ksRhoL p Q) _ (fun q hq => by
    simp only [ksRhoL, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    simp only [laneBits] at hT ⊢; omega) h2
  set sF : List FE := lamF ++ rhoF.drop (ksXLog p) with hsF
  have hw : (rhoF.drop (ksXLog p)).length = p.ksLog - ksXLog p := by simp [hrl]
  have hsl : ksSelW p = sF.length := by simp [ksSelW, hsF, hll, hw]
  rw [hsl] at h6
  have hE2 := eqTab_eq _ (ec z) (ec o) false sF h6 hz
    (fun i => by unfold ksSelAl; split <;> rfl) ho (fun i hi => by
      unfold ksSelAl
      by_cases h5 : i < laneBits
      · rw [if_pos h5, Cell.val_E, hlamv i h5, hsF, List.getD_append _ _ _ _ (by rw [hll]; exact h5)]
      · have hk : ksXLog p + (i - laneBits) < (ksRhoL p Q).length := by
          rw [hsF, List.length_append, hll, hw] at hi; simp [ksRhoL]; omega
        rw [if_neg h5, Cell.val_E, loadAt_out, List.getD_eq_getElem _ _ (by simpa using hk),
          List.getElem_map, List.getElem_range, hRv _ hk, hsF,
          List.getD_append_right _ _ _ _ (by rw [hll]; omega), hll, List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_drop, hrhoL, List.getElem?_map,
          List.getElem?_eq_getElem hk]
        rfl)
  rw [← hsl] at hE2
  refine ksLinkC14_val p hz ho _ _ _ _ _ ?_ (by simp) ?_ ?_ ?_ (by rw [loadAt_out]; simp [ksValL])
  · rw [hlam]
    refine List.ext_getElem (by simp [vs, Build.eqKernel_length, hll, laneBits]) fun x h1 h2 => ?_
    simp only [vs, List.length_map, List.length_range] at h1
    simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
    have e := hE x (by simpa [laneBits] using h1)
    simp only [if_false, Bool.false_eq_true] at e
    rw [e, ← eqKernel_getD_A, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  · intro l hl
    have h1w : 1 ≤ 2 ^ (p.ksLog - ksXLog p) := Nat.one_le_two_pow
    have htop : ksTop p + l < 2 ^ ksSelW p := by
      rw [ksSelW, pow_add, ksTop, laneBits, Nat.mul_sub_one]
      have : 32 ≤ 2 ^ 5 * 2 ^ (p.ksLog - ksXLog p) := by
        calc 32 = 2 ^ 5 * 1 := rfl
          _ ≤ _ := Nat.mul_le_mul_left _ h1w
      omega
    have hidx : ksTop p + l = l + 2 ^ lamF.length * (2 ^ (rhoF.drop (ksXLog p)).length - 1) := by
      rw [hll, hw, ksTop, laneBits]; ring
    rw [List.getD_eq_getElem _ _ (by simpa using htop), List.getElem_map, List.getElem_range, Cell.val_E,
      hE2 _ htop, if_neg (by simp), eqKernelA_getD _ _ (by rw [← hsl]; exact htop), hsF, eqW_append, hidx,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [hll]; simp only [laneBits]; omega),
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by rw [hll]; simp only [laneBits]; omega),
      zero_add, eqW_ones, hlam, ← Lvm.Q1.prodE_eq_prodF, eqKernel_getD_A,
      eqKernelA_getD _ _ (by rw [hll]; simp only [laneBits]; omega)]
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksRhoL, List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      simp only [laneBits] at hT ⊢; omega) h2, ← hrhoL]
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksValL, List.mem_map, List.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      omega) h3]
    simp only [ksLinkView, scalarsAt, ksValL, List.map_map]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [ksP2, ksP1, roundLen, laneBits]; omega

/-- **Q_arith_eq, the `KS` link's claims**: with the reader at `P` (`P + 40 = 8 Q`) the cells are
`ksLink0`'s claims on what `F` reads in phase 7 (any `M3` `m`; KS14 needs `4 ≤ ksLog`). -/
theorem ksLinkG_val (p : Params) (m : M3) {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr}
    (rk : List FE) (pub : Pub) (h4 : 4 ≤ p.ksLog) (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T)
    (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (ksLinkG p Q z o ptr).2) :
    (ksLinkG p Q z o ptr).1.map (CClaim.val M) = (ksLink0 p (ksLinkView p m (feAt sig) P rk pub)).2 := by
  by_cases h14 : p.ksLog ≤ p.recRowsLog
  · simp only [ksLinkG, ksLink0, if_pos h14] at h ⊢
    exact ksLinkG14_val p m rk pub h14 h4 hPQ hS hT hz ho h
  · simp only [ksLinkG, ksLink0, if_neg h14] at h ⊢
    exact ksLinkGV1_val p m rk pub hPQ hS hT hz ho h

/-- **`F`'s phase-7 claims** (`ksLinkPh`, any `m`) from the reader at `P`. -/
theorem ksLinkPh_claims (p : Params) (m : M3) {z o Q T : Nat} {sig : ByteArray} {ptr : Ptr}
    (rk : List FE) (pub : Pub) (s : RS) (hn : 1 ≤ p.ksLog) (h4 : 4 ≤ p.ksLog) (hPQ : pos s + 40 = 8 * Q)
    (hS : Streamed M sig T) (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T)
    (hz : M.e z = 0) (ho : M.e o = 1) (hm : m.ksLink = ksLink0 p)
    (h : SegsHold c M ptr (ksLinkG p Q z o ptr).2) :
    (ksLinkPh p m rk pub sig s).1.2 = (ksLinkG p Q z o ptr).1.map (CClaim.val M) := by
  rw [ksLinkPh_run p m rk pub sig s hn, hm]
  exact (ksLinkG_val p m rk pub h4 hPQ hS hT hz ho h).symm

/-! ## Instances: `P20`, `P8` (reader positions from `phaseFirst`, WP-16a's `aLane`) -/

open Lvm.QAsm in
/-- The lanes this family reads at a parameter set lie in the stream (`streamLanes`), the links'
lanes are their phases' first positions, and `KS`'s ring switch ends where `KS`'s link begins. -/
def RCLanes (p : Params) : Prop :=
  5 ≤ aLane p 2 ∧ 5 ≤ aLane p 6 ∧
  Lvm.Q1.wireEnd (p.logN - 5) (aLane p 3) + 2 ≤ streamLanes p ∧
  gkrEnd (p.ksLog - 4) (aLane p 6) + 48 ≤ streamLanes p ∧
  Lvm.Q1.tapeEnd (p.logN - 5) (aLane p 2) = aLane p 3 ∧
  aLane p 7 + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ streamLanes p ∧
  phaseByte p .wire + 40 = 8 * aLane p 3 ∧ phaseByte p .ksLink + 40 = 8 * aLane p 7 ∧
  8 * gkrEnd (p.ksLog - 4) (aLane p 6) - 40 + 72 * ringStages = phaseByte p .ksLink ∧
  8 * Lvm.Q1.wireEnd (p.logN - 5) (aLane p 3) - 40 = phaseByte p .ks

theorem rcLanes20 : RCLanes P20 := by
  unfold RCLanes; decide +kernel

theorem rcLanes8 : RCLanes P8 := by
  unfold RCLanes; decide +kernel

/-- **`P20`'s phase-5 claims** from the reader at the phase's first position. -/
theorem ksLinkPh_claims20 {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o : Nat} {sig : ByteArray} {ptr : Ptr} (rk : List FE) (pub : Pub) (s : RS)
    (hs : pos s = phaseByte P20 .ksLink) (hS : Streamed M sig (streamLanes P20)) (hz : M.e z = 0)
    (ho : M.e o = 1) (h : SegsHold c M ptr (ksLinkG P20 (aLane P20 7) z o ptr).2) :
    (ksLinkPh P20 (M3.ofParts P20 bf tb tcl fv fs pck) rk pub sig s).1.2 =
      (ksLinkG P20 (aLane P20 7) z o ptr).1.map (CClaim.val M) :=
  ksLinkPh_claims P20 _ rk pub s (by decide) (by decide) (by rw [hs]; exact rcLanes20.2.2.2.2.2.2.2.1) hS
    rcLanes20.2.2.2.2.2.1 hz ho rfl h

/-- **`P20`'s `KS` ring switch** (after `KS`'s GKR at WP-16a's lane `aLane P20 6`): `F`'s `ringAt` at the
GKR's end is the gadget's claim, and the switch ends at the `KS` link's first position. -/
theorem ksRing20 {sig : ByteArray} {z : Nat} {p : Ptr} (instV outV : List FE)
    (hinst : instV.length = P20.ksLog) (ok : Bool) (hS : Streamed M sig (streamLanes P20))
    (hz : M.e z = 0) (h : SegsHold c M p (ringGkr (P20.ksLog - 4) (aLane P20 6) z p).2) :
    RingRel M (vkSpec (feAt sig) P20.ksLog instV outV (8 * aLane P20 6 - 40) ok).1.slicePoint
      (ringAt (feAt sig) (8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40)
        (vkSpec (feAt sig) P20.ksLog instV outV (8 * aLane P20 6 - 40) ok).1.slicePoint
        (vkSpec (feAt sig) P20.ksLog instV outV (8 * aLane P20 6 - 40) ok).1.slices)
      (ringGkr (P20.ksLog - 4) (aLane P20 6) z p).1 ∧
    8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40 + 72 * ringStages = phaseByte P20 .ksLink :=
  ⟨ringGkr_ringAt (by decide) rcLanes20.2.1 instV outV hinst ok hS rcLanes20.2.2.2.1 hz h,
    rcLanes20.2.2.2.2.2.2.2.2.1⟩

/-- `ksLinkG_val` in `F`'s form `m.ksLink (ksLinkView …)` (`m = M3.ofParts p …`). -/
theorem ksLinkG_val' (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr} (rk : List FE) (pub : Pub) (h4 : 4 ≤ p.ksLog)
    (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T)
    (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (ksLinkG p Q z o ptr).2) :
    (ksLinkG p Q z o ptr).1.map (CClaim.val M) =
      ((M3.ofParts p bf tb tcl fv fs pck).ksLink
        (ksLinkView p (M3.ofParts p bf tb tcl fv fs pck) (feAt sig) P rk pub)).2 :=
  ksLinkG_val p _ rk pub h4 hPQ hS hT hz ho h

end Lvm.Har
