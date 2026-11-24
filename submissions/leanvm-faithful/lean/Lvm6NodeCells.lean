-- New for lvm6 (WP N4-cells). `NodeFacts6`'s input cells, sponge rows and readers on the deployed layout: what
-- follows from the memory read off a candidate pair (stream words, QLT constants, `PUB` lanes = header bytes,
-- `KS` aliases), and the reader definitions. What does not follow is named (module doc, `N4-cells.md`).
import Lvm6NodeCellsAux
import Lvm6NodeV

/-!
# Input cells, CB-4 sponge rows and readers of `node6V_Q` (WP N4-cells, targets 2–4)

Every fact here is about `memTi Ti L pw p` = `memOf Ti.lay (Ti.zOf …)`, whose `K` cell `n` is the constant
`Ti.lay.cst? n` if any, else the word `Ti.lay.wordK n` read through its source (`zOf`).

* **Stream** (`wsOf`): the stream words are *defined* as the cells `sbC + j`, `j < 2^19`; `QIn6.stream` and
  `ws.length = 2^19` hold by definition (`laneK_wsOf`, `wsOf_length`).
* **QLT** (`QltCst`, layout fact): the deployed `lay.cst` is the exporter's `[(zC, [0]), (qtC, qltData6 P6 lay6)]`;
  `qlt_of_cst` gives `QIn6.table`.
* **`PUB`** (`PubCells`, layout fact): cell `pbC + l` is `PUB` word `pubBase + l`. With CD's `pw = pwOf Ti (hdrBytes x)`
  (`TyRest6`), cell `pbC + l` is header lane `l` (`pub_lane`): **the flag** (lane 1 = `b`) is `1` in node mode
  (`flag_cell`), the key is at `pbC + 11` (`key_cells`), `c'` at `pbC + 7` (`cp_cells`). (NODE3 F1 moved the
  deployed `sigI.vk`, `sigI.cL` to these lanes; RV4 m3: the old `sigI_vk_cells`, `sigI_cL_cells` are removed.)
* **`KS` aliases** (`KSAlias`, layout fact on `ksW`): the alias cells hold the node's sponge rows `X`, `Yl`;
  with K1's `OutRel`/`SpongeLink` (relation facts of the node's own sponge table, `rest`), CB-4 gives `SigKSin`,
  `SigKSinC` (`sigKS_of_alias`) and `hmd` (`md_of_alias`); `B = 4002` (`blocks_P18`).
* **Readers** (`wsOf`, `trOfM`, `σOfM`, `σlOfM` of a memory map `mOf : Stack → Mem`): equal to the cells' values
  wherever `mOf q` agrees with the pair's memory on the stream and signature cells (`readers_of_agree`); `PUB`
  words do not matter there when those cells are not `PUB` (`memTi_pw`).
* **`nodeFacts6_of_cells`**: `NodeFacts6` from the guard, `TGoodE`, the layout facts, the `BITS` cells (not
  constrained by the deployed layout), the node's sponge relations, `hdec` and the readers.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm.Har Lvm.E2V LeanVM.Protocol
open Lvm6.QK Lvm6.QD Lvm6.Node Lvm.QSig Lvm.QLink Lvm.Wots Lvm.Bits
open Lvm6.Ty (TInst6 TGoodE NoE3)
open LeanVM.Parameters

/-! ## Stream words -/

/-- **The stream words of a memory**: its `K` cells `sbC + j`, `j < 2^19`. -/
def wsOf (M : Mem) : List Word := (List.range (2 ^ 19)).map fun j ↦ (M.k (sbC + j)).val.toBitVec

theorem wsOf_length (M : Mem) : (wsOf M).length = 2 ^ 19 := by simp [wsOf]

theorem laneK_wsOf (M : Mem) {j : ℕ} (hj : j < 2 ^ 19) : laneK (wsOf M) j = M.k (sbC + j) := by
  simp only [laneK, wsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

/-! ## The QLT constants -/

/-- **The deployed layout's constant cells** (the exporter's `specOf`): the zero cell, the QLT table. -/
def QltCst (lay : Lay) : Prop := lay.cst = [(zC, [0]), (qtC, qltData6 P6 lay6)]

/-- `qlt_of_cst` at any table `D` (KDN: the kernel checks it with `D` a variable, so it never evaluates
`qltData6 P6 lay6`). -/
theorem qlt_of_cst_aux {lay : Lay} {D : List FK} (h : lay.cst = [(zC, [0]), (qtC, D)]) (z : ℕ → FK) {x : ℕ}
    (hx : x < D.length) : (memOf lay z).k (qtC + x) = D.getD x 0 := by
  have h1 : ¬ (zC ≤ qtC + x ∧ qtC + x < zC + [(0 : FK)].length) := by
    simp only [zC, qtC, X0, List.length_singleton]; omega
  have h2 : qtC ≤ qtC + x ∧ qtC + x < qtC + D.length := ⟨by omega, by omega⟩
  show (lay.cst? (qtC + x)).getD _ = _
  rw [Lay.cst?, h, List.find?_cons_of_neg (by simpa only [decide_eq_true_eq] using h1),
    List.find?_cons_of_pos (by simpa only [decide_eq_true_eq] using h2)]
  simp

theorem qlt_of_cst {lay : Lay} (h : QltCst lay) (z : ℕ → FK) {x : ℕ} (hx : x < (qltData6 P6 lay6).length) :
    (memOf lay z).k (lay6.qt + x) = (qltData6 P6 lay6).getD x 0 := by
  have e : lay6.qt = qtC := rfl
  rw [e]
  exact qlt_of_cst_aux h z hx

/-! ## `PUB` cells and the header -/

/-- **The deployed layout's `PUB` cells**: `K` cell `pbC + l` (`l < 2^10`) is no constant and holds `PUB` word
`pubBase + l`. -/
def PubCells (Ti : TInst6) : Prop :=
  ∀ l < 2 ^ 10, Ti.lay.cst? (pbC + l) = none ∧ Ti.lay.wordK (pbC + l) = pubBase Ti + l ∧
    Ti.src? (pubBase Ti + l) = some .pub

theorem pub_cell {Ti : TInst6} (hP : PubCells Ti) (L : Lvm.M3.Lay) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) {l : ℕ} (hl : l < 2 ^ 10) :
    (memTi Ti L pw p).k (pbC + l) = pw (pubBase Ti + l) := by
  obtain ⟨h1, h2, h3⟩ := hP l hl
  show (Ti.lay.cst? (pbC + l)).getD (Ti.zOf L pw p.1 p.2 (Ti.lay.wordK (pbC + l))) = _
  rw [h1, Option.getD_none, h2]
  unfold TInst6.zOf
  rw [h3]

/-- `PUB` lane `l` of a header's bytes. -/
theorem pwOf_lane (Ti : TInst6) (H : List UInt8) (l : ℕ) :
    pwOf Ti H (pubBase Ti + l) = w64 (le8 H (8 * l)).toUInt64 := by
  simp [pwOf]

/-- **`PUB` cell `pbC + l` is header lane `l`** (CD's public words). -/
theorem pub_lane {Ti : TInst6} (hP : PubCells Ti) (L : Lvm.M3.Lay) (H : List UInt8)
    (p : Column L.nuMain × Column L.nuRec) {l : ℕ} (hl : l < 2 ^ 10) :
    (memTi Ti L (pwOf Ti H) p).k (pbC + l) = w64 (le8 H (8 * l)).toUInt64 := by
  rw [pub_cell hP L _ p hl, pwOf_lane]

theorem le8_expand (H : List UInt8) (o : ℕ) : le8 H o =
    (H.getD (o + 0) 0).toNat + (H.getD (o + 1) 0).toNat * 2 ^ 8 + (H.getD (o + 2) 0).toNat * 2 ^ 16 +
      (H.getD (o + 3) 0).toNat * 2 ^ 24 + (H.getD (o + 4) 0).toNat * 2 ^ 32 + (H.getD (o + 5) 0).toNat * 2 ^ 40 +
      (H.getD (o + 6) 0).toNat * 2 ^ 48 + (H.getD (o + 7) 0).toNat * 2 ^ 56 := by
  unfold le8
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.map_append,
    List.sum_cons, List.sum_nil, List.sum_append]
  ring

theorem le8_lt (H : List UInt8) (o : ℕ) : le8 H o < 2 ^ 64 := by
  have hb : ∀ t, (H.getD (o + t) 0).toNat < 256 := fun t ↦ (H.getD (o + t) 0).toNat_lt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  clear hb
  rw [le8_expand]
  generalize (H.getD (o + 0) 0).toNat = b0 at h0 ⊢
  generalize (H.getD (o + 1) 0).toNat = b1 at h1 ⊢
  generalize (H.getD (o + 2) 0).toNat = b2 at h2 ⊢
  generalize (H.getD (o + 3) 0).toNat = b3 at h3 ⊢
  generalize (H.getD (o + 4) 0).toNat = b4 at h4 ⊢
  generalize (H.getD (o + 5) 0).toNat = b5 at h5 ⊢
  generalize (H.getD (o + 6) 0).toNat = b6 at h6 ⊢
  generalize (H.getD (o + 7) 0).toNat = b7 at h7 ⊢
  norm_num
  omega

/-- **Byte `t` of a little-endian word is byte `o + t` of the list.** -/
theorem byteW_le8 (H : List UInt8) (o : ℕ) {t : ℕ} (ht : t < 8) :
    byteW (le8 H o).toUInt64 t = H.getD (o + t) 0 := by
  rw [byteW_toNat _ ht, show (le8 H o).toUInt64.toNat = le8 H o from by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (le8_lt H o)]
  apply UInt8.toNat_inj.mp
  have e : ∀ y : ℕ, y.toUInt8.toNat = y % 256 := fun y ↦ by simp [Nat.toUInt8]
  rw [e, le8_expand]
  have hb : ∀ t, (H.getD (o + t) 0).toNat < 256 := fun t ↦ (H.getD (o + t) 0).toNat_lt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  clear hb
  interval_cases t <;>
  · generalize (H.getD (o + 0) 0).toNat = b0 at h0 ⊢
    generalize (H.getD (o + 1) 0).toNat = b1 at h1 ⊢
    generalize (H.getD (o + 2) 0).toNat = b2 at h2 ⊢
    generalize (H.getD (o + 3) 0).toNat = b3 at h3 ⊢
    generalize (H.getD (o + 4) 0).toNat = b4 at h4 ⊢
    generalize (H.getD (o + 5) 0).toNat = b5 at h5 ⊢
    generalize (H.getD (o + 6) 0).toNat = b6 at h6 ⊢
    generalize (H.getD (o + 7) 0).toNat = b7 at h7 ⊢
    norm_num
    omega

/-- **Four cells holding header lanes `k … k + 3` are the digest at bytes `8k`.** -/
theorem digAt_lanes {v : ℕ → FK} {a k : ℕ} {H : List UInt8}
    (hv : ∀ l < 4, v (a + l) = w64 (le8 H (8 * (k + l))).toUInt64) : digAt v a = dig32 H (8 * k) := by
  apply Vector.ext
  intro i hi
  simp only [digAt, dig32, Vector.getElem_ofFn]
  rw [digOfW_get _ hi, hv _ (by omega)]
  show byteW (le8 H (8 * (k + i / 8))).toUInt64 (i % 8) = _
  rw [byteW_le8 _ _ (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

/-- The header's byte layout: the 88 bytes before `vk` (magic, `b`, `n`, `h`, `c'`). -/
theorem hdrBytes_split (x : Hdr) :
    hdrBytes x = (V.magic6 ++ le64 x.b ++ le64 x.n ++ x.h.toList) ++ (x.c'.toList ++ (x.vk.toList ++
      (x.accIn.1.flatMap eBytes ++ eBytes x.accIn.2))) := by
  simp [hdrBytes, List.append_assoc]

theorem len56 (x : Hdr) : (V.magic6 ++ le64 x.b ++ le64 x.n ++ x.h.toList).length = 56 := by
  simp [V.magic6, le64]

theorem dig32_vk (x : Hdr) : dig32 (hdrBytes x) (8 * 11) = x.vk := by
  apply Vector.ext
  intro i hi
  simp only [dig32, Vector.getElem_ofFn]
  rw [hdrBytes_split, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [len56]; omega), len56,
    List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [Vector.length_toList, Vector.getElem?_toList]
  rw [show 8 * 11 + i - 56 - 32 = i by omega, Vector.getElem?_eq_getElem hi, Option.getD_some]

theorem dig32_cp (x : Hdr) : dig32 (hdrBytes x) (8 * 7) = x.c' := by
  apply Vector.ext
  intro i hi
  simp only [dig32, Vector.getElem_ofFn]
  rw [hdrBytes_split, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [len56]; omega), len56,
    List.getElem?_append_left (by simp; omega)]
  simp only [Vector.getElem?_toList]
  rw [show 8 * 7 + i - 56 = i by omega, Vector.getElem?_eq_getElem hi, Option.getD_some]

section Pub

variable {Ti : TInst6} (hP : PubCells Ti) (L : Lvm.M3.Lay) (x : Hdr) (p : Column L.nuMain × Column L.nuRec)
include hP

/-- The digest at `PUB` cell `pbC + k` is the header's bytes `8k … 8k + 31`. -/
theorem pub_dig {k : ℕ} (hk : k + 4 ≤ 2 ^ 10) :
    digAt (memTi Ti L (pwOf Ti (hdrBytes x)) p).k (pbC + k) = dig32 (hdrBytes x) (8 * k) :=
  digAt_lanes fun l hl ↦ by rw [Nat.add_assoc, pub_lane hP L _ p (by omega)]

/-- **The key's cells**: header lanes 11–14 (FORMAT6 §2: `vk` at byte 88). -/
theorem key_cells : digAt (memTi Ti L (pwOf Ti (hdrBytes x)) p).k (pbC + 11) = x.vk := by
  rw [pub_dig hP L x p (by norm_num), dig32_vk]

/-- **`c'`'s cells**: header lanes 7–10 (FORMAT6 §2: `c'` at byte 56). -/
theorem cp_cells : digAt (memTi Ti L (pwOf Ti (hdrBytes x)) p).k (pbC + 7) = x.c' := by
  rw [pub_dig hP L x p (by norm_num), dig32_cp]

/-- **The flag** (header lane 1 = `b`) is `1` in node mode; `sigIl.flag = sigI.flag = lay6.fg`. -/
theorem flag_cell (hb : x.b = 1) : (memTi Ti L (pwOf Ti (hdrBytes x)) p).k (pbC + 1) = 1 := by
  rw [pub_lane hP L _ p (by norm_num)]
  have e : le8 (hdrBytes x) (8 * 1) = 1 := by
    unfold le8
    have h : ∀ t ∈ List.range 8, ((hdrBytes x).getD (8 * 1 + t) 0).toNat * 2 ^ (8 * t) =
        ((le64 x.b).getD t 0).toNat * 2 ^ (8 * t) := by
      intro t ht
      have ht8 := List.mem_range.mp ht
      rw [hdrBytes_split, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [len56]; omega),
        List.getElem?_append_left (by simp [V.magic6, le64]; omega),
        List.getElem?_append_left (by simp [V.magic6, le64]; omega),
        List.getElem?_append_right (by simp [V.magic6]), List.getD_eq_getElem?_getD,
        show 8 * 1 + t - V.magic6.length = t by simp [V.magic6]]
    rw [List.map_congr_left h, hb]
    decide
  rw [e]
  rfl

omit hP in
/-- Cells whose word is not `PUB` do not depend on the public words. -/
theorem memTi_pw (pw pw' : ℕ → FK) {n : ℕ} (h : Ti.src? (Ti.lay.wordK n) ≠ some .pub) :
    (memTi Ti L pw p).k n = (memTi Ti L pw' p).k n := by
  show (Ti.lay.cst? n).getD (Ti.zOf L pw p.1 p.2 _) = (Ti.lay.cst? n).getD (Ti.zOf L pw' p.1 p.2 _)
  congr 1
  unfold TInst6.zOf
  rcases hs : Ti.src? (Ti.lay.wordK n) with _ | s
  · rfl
  · cases s <;> first | rfl | exact absurd hs h

end Pub

/-! ## CB-4: the `KS` alias cells -/

/-- **The `KS` alias cells** of the deployed layout hold the node's sponge rows: input lanes `X r l` (`r < 912`) at
`xsC + 17 r + l`; output lanes of rows `7168 + r` (`r < 449`) at `ysC + 4 r + l`, of rows `7680 + r` (`r < 400`) at
`ysC + 4·2^10 + 4 r + l`, of row `4001 = B − 1` at `mdC + l`. A layout fact on `Ti.ksW` once `X`, `Yl` are read
off the stack's sponge columns. -/
structure KSAlias (v : ℕ → FK) (X Yl : ℕ → ℕ → K) : Prop where
  xs : ∀ r < 912, ∀ l < 17, v (xsC + 17 * r + l) = FK.ofBF64 (X r l)
  ys : ∀ r < 449, ∀ l < 4, v (ysC + 4 * r + l) = FK.ofBF64 (Yl l (7168 + r))
  ysl : ∀ r < 400, ∀ l < 4, v (ysC + 4 * 2 ^ 10 + 4 * r + l) = FK.ofBF64 (Yl l (7680 + r))
  md : ∀ l < 4, v (mdC + l) = FK.ofBF64 (Yl l 4001)

section KS

variable {v : ℕ → FK} {ks : ℕ → K} {X Yl Mx : ℕ → ℕ → K}

/-- **`Q_sig`'s `KS` hypotheses** (both walks) from the node's sponge relations and the alias cells. -/
theorem sigKS_of_alias (hout : Lvm.KG.OutRel 13 25 ks Yl)
    (hlink : Lvm.KG.SpongeLink 13 (rowsBK2 4002 7567 8032) ks (fun i l ↦ Yl l i) (Lvm.KG.ksMsg 7168 Mx X))
    (hA : KSAlias v X Yl) : SigKSin sigI v ∧ SigKSinC sigIl v := by
  have hn := W.nStepRowsC_eq
  refine ⟨W.sigKSin6 (by norm_num) hout hlink (fun r hr l hl ↦ hA.xs r (by omega) l hl)
    (fun r hr l hl ↦ hA.ys r (by omega) l hl) (fun t ht l hl ↦ ?_) (fun l hl ↦ hA.ys 447 (by norm_num) l hl)
    (fun l hl ↦ hA.ys 448 (by norm_num) l hl),
    W.sigKSinC6 (by norm_num) hout hlink (fun r hr l hl ↦ ?_) (fun r hr l hl ↦ hA.ysl r (by omega) l hl)
      (fun t ht l hl ↦ ?_)⟩
  · have := hA.ys (430 + t) (by omega) l hl
    rw [show ysC + 4 * (430 + t) + l = sigI.yc + 4 * t + l by simp only [sigI]; omega,
      show 7168 + (430 + t) = 7168 + 430 + t by omega] at this
    exact this
  · have := hA.xs (512 + r) (by omega) l hl
    rw [show xsC + 17 * (512 + r) + l = sigIl.xs + 17 * r + l by simp only [sigIl, sigI]; omega] at this
    exact this
  · have := hA.ysl (383 + t) (by omega) l hl
    rw [show ysC + 4 * 2 ^ 10 + 4 * (383 + t) + l = sigIl.yc + 4 * t + l by simp only [sigIl, sigI, hn]; omega,
      show 7680 + (383 + t) = 7680 + 383 + t by omega] at this
    exact this

/-- **CB-4's digest cells** (`hmd`) from the alias cells, at `B = 4002`. -/
theorem md_of_alias (hA : KSAlias v X Yl) : ∀ l < 4, v (sigI.md + l) = FK.ofBF64 (Yl l (4002 - 1)) :=
  fun l hl ↦ hA.md l hl

/-- `B = nBlk (hashedLen6 P6) = 4002` (CB-4's `blocks_P18`). -/
theorem nBlk_P6 : (4002 : ℕ) = Lvm.KSponge.nBlk (hashedLen6 P6) := W.blocks_P18.2.symm

end KS

/-! ## Readers -/

/-- **The child's trace read off a memory map** (the stream words, decoded). -/
def trOfM (mOf : Stack → Mem) (q : Stack) : Trace := decode6 P6 (wsOf (mOf q))

/-- **`σ'` read off a memory map** (cells from `sigI.sg = sgC`). -/
def σOfM (mOf : Stack → Mem) (q : Stack) : Sig := sigAt' (mOf q).k sigI.sg

/-- **`σ_leaf` read off a memory map** (cells from `sigIl.sg = dstC`, chains in `permC` order). -/
def σlOfM (mOf : Stack → Mem) (q : Stack) : Sig := sigAtP (mOf q).k sigIl.sg

theorem digAt_congr {v v' : ℕ → FK} {a : ℕ} (h : ∀ l < 4, v (a + l) = v' (a + l)) : digAt v a = digAt v' a :=
  SigH.digOfW_congr fun l hl ↦ by show (v (a + l)).val = (v' (a + l)).val; rw [h l hl]

theorem sigAt'_congr {v v' : ℕ → FK} {a : ℕ} (h : ∀ i < 597, v (a + i) = v' (a + i)) :
    sigAt' v a = sigAt' v' a := by
  have e1 : v a = v' a := by simpa using h 0 (by norm_num)
  have e2 : (List.range wotsLen).map (fun i => digAt v (a + 1 + 4 * i)) =
      (List.range wotsLen).map (fun i => digAt v' (a + 1 + 4 * i)) :=
    List.map_congr_left fun i hi ↦ digAt_congr fun l hl ↦ by
      have hi' : i < 133 := List.mem_range.mp hi
      rw [show a + 1 + 4 * i + l = a + (1 + 4 * i + l) by omega, h _ (by omega)]
  have e3 : (List.range sigHeight).map (fun t => digAt v (a + 533 + 4 * t)) =
      (List.range sigHeight).map (fun t => digAt v' (a + 533 + 4 * t)) :=
    List.map_congr_left fun t ht ↦ digAt_congr fun l hl ↦ by
      have ht' : t < 16 := List.mem_range.mp ht
      rw [show a + 533 + 4 * t + l = a + (533 + 4 * t + l) by omega, h _ (by omega)]
  rw [sigAt', sigAt', e1, e2, e3]

theorem sigAtP_congr {v v' : ℕ → FK} {a : ℕ} (h : ∀ i < 597, v (a + i) = v' (a + i)) :
    sigAtP v a = sigAtP v' a := by
  have e1 : v a = v' a := by simpa using h 0 (by norm_num)
  have e2 : (List.range wotsLen).map (fun i => digAt v (a + 1 + 4 * posC i)) =
      (List.range wotsLen).map (fun i => digAt v' (a + 1 + 4 * posC i)) :=
    List.map_congr_left fun i hi ↦ digAt_congr fun l hl ↦ by
      have hi' : i < 133 := List.mem_range.mp hi
      have hp : posC i < 133 := by
        obtain ⟨hd, -, hlt, -⟩ := posC_spec hi'
        have hb : ∀ d ≤ 3, gOffC d + (grpC d).length ≤ 133 := by decide +kernel
        exact lt_of_lt_of_le hlt (hb _ hd)
      rw [show a + 1 + 4 * posC i + l = a + (1 + 4 * posC i + l) by omega, h _ (by omega)]
  have e3 : (List.range sigHeight).map (fun t => digAt v (a + 533 + 4 * t)) =
      (List.range sigHeight).map (fun t => digAt v' (a + 533 + 4 * t)) :=
    List.map_congr_left fun t ht ↦ digAt_congr fun l hl ↦ by
      have ht' : t < 16 := List.mem_range.mp ht
      rw [show a + 533 + 4 * t + l = a + (533 + 4 * t + l) by omega, h _ (by omega)]
  rw [sigAtP, sigAtP, e1, e2, e3]

/-- **The readers are the cells' values** wherever the memory map agrees with the pair's memory on the stream
cells and the two signatures' cells. -/
theorem readers_of_agree {M : Mem} {mOf : Stack → Mem} {q : Stack}
    (hs : ∀ j < 2 ^ 19, (mOf q).k (sbC + j) = M.k (sbC + j))
    (hσ : ∀ i < 597, (mOf q).k (sgC + i) = M.k (sgC + i))
    (hσl : ∀ i < 597, (mOf q).k (dstC + i) = M.k (dstC + i)) :
    trOfM mOf q = decode6 P6 (wsOf M) ∧ σOfM mOf q = sigAt' M.k sigI.sg ∧ σlOfM mOf q = sigAtP M.k sigIl.sg := by
  refine ⟨?_, sigAt'_congr hσ, sigAtP_congr hσl⟩
  have e : (List.range (2 ^ 19)).map (fun j ↦ ((mOf q).k (sbC + j)).val.toBitVec) =
      (List.range (2 ^ 19)).map (fun j ↦ (M.k (sbC + j)).val.toBitVec) :=
    List.map_congr_left fun j hj ↦ by rw [hs j (List.mem_range.mp hj)]
  unfold trOfM wsOf
  rw [e]

/-! ## `NodeFacts6` from the cells -/

/-- **`Q_link`'s position bits** (`QIn6.bits` at the deployed layout): free committed cells of the deployed
layout (`bbC`, `.com`; no `BITS` row constrains them). -/
def PosBits6 (ws : List Word) (M : Mem) : Prop :=
  ∀ k < opensP18.length, ∀ j < (opensP18.getD k default).t, ∀ z < (opensP18.getD k default).h,
    M.k (bitBase6 opensP18 lay6 k + (opensP18.getD k default).h * j + z) =
      if ansBit6 P6 ws ((opensP18.getD k default).pd0 + j / (opensP18.getD k default).per)
        (j % (opensP18.getD k default).per * (opensP18.getD k default).h + z) then 1 else 0

/-- **`NodeFacts6` from the cells.** The guard and the relation as in `node6V_Q`; the layout facts `PowAuxIn`,
`QltCst`, `PubCells`, `KSAlias`; the `BITS` cells (`PosBits6`, `SigBits`, `SigBitsC`); the node's own sponge
relations (`OutRel`, `SpongeLink`) and its message rows on the stream (`hM`); the decision; the readers. The
stream words are `wsOf` of the memory, `B = 4002`, the public words CD's `pwOf Ti (hdrBytes x)`. -/
theorem nodeFacts6_of_cells (Φ : Phases) (trOf : Stack → Trace) (σOf σlOf : Stack → Sig) (x : Hdr) (q : Stack)
    (hb : x.b = 1) (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (p : Column L.nuMain × Column L.nuRec) (N : ℕ) (ks : ℕ → K) (Yl Mx X : ℕ → ℕ → K)
    -- the guard and the relation
    (hQ : Ti.Q = progQ6 Ti.lay) (hwf : Ti.Q.wf = true) (htw : Ti.Q.twinsOk = true) (hE3 : NoE3 Ti.Q Ti.lay)
    (hok : Ti.Ok) (hrd : ReaddOk Ti.Q (memTi Ti L (pwOf Ti (hdrBytes x)) p))
    (hg : TGoodE Ti L hτ (pwOf Ti (hdrBytes x)) p)
    (hinj : GInj N) (hN : (ctxOf Ti.Q).cells .K ≤ N) (hNs : sbC + 2 ^ 19 ≤ N)
    (hinj' : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    -- the layout facts
    (hpow : PowAuxIn Ti.lay) (hcst : QltCst Ti.lay) (hpub : PubCells Ti)
    (hA : KSAlias (memTi Ti L (pwOf Ti (hdrBytes x)) p).k X Yl)
    -- the `BITS` cells
    (hpb : PosBits6 (wsOf (memTi Ti L (pwOf Ti (hdrBytes x)) p)) (memTi Ti L (pwOf Ti (hdrBytes x)) p))
    (hbits : SigBits sigI (qsig6 sigI sigIl sbC (pS Ti.lay ⟨nK, 0⟩)).1.1 (memTi Ti L (pwOf Ti (hdrBytes x)) p).k)
    (hbitsL : SigBitsC sigIl (qsig6 sigI sigIl sbC (pS Ti.lay ⟨nK, 0⟩)).1.2.pa
      (memTi Ti L (pwOf Ti (hdrBytes x)) p).k)
    -- the node's sponge table
    (hout : Lvm.KG.OutRel 13 25 ks Yl)
    (hlink : Lvm.KG.SpongeLink 13 (rowsBK2 4002 7567 8032) ks (fun i l ↦ Yl l i) (Lvm.KG.ksMsg 7168 Mx X))
    (hM : ∀ i < 7168, ∀ l < 17,
      (Mx i l).toBitVec.toNat = lw (wsOf (memTi Ti L (pwOf Ti (hdrBytes x)) p)) (17 * i + l))
    -- the decision
    (hdec : F6 Φ P18 (digAt (memTi Ti L (pwOf Ti (hdrBytes x)) p).k sigI.vk)
      (reassemble6 P6 (decode6 P6 (wsOf (memTi Ti L (pwOf Ti (hdrBytes x)) p))))
      (accOf P18 (reassemble6 P6 (decode6 P6 (wsOf (memTi Ti L (pwOf Ti (hdrBytes x)) p))))
        (decode6 P6 (wsOf (memTi Ti L (pwOf Ti (hdrBytes x)) p)))) = true)
    -- the readers
    (hvk : digAt (memTi Ti L (pwOf Ti (hdrBytes x)) p).k sigI.vk = x.vk)
    (hcL : digAt (memTi Ti L (pwOf Ti (hdrBytes x)) p).k sigI.cL = x.c')
    (htr : trOf q = decode6 P6 (wsOf (memTi Ti L (pwOf Ti (hdrBytes x)) p)))
    (hσ : σOf q = sigAt' (memTi Ti L (pwOf Ti (hdrBytes x)) p).k sigI.sg)
    (hσl : σlOf q = sigAtP (memTi Ti L (pwOf Ti (hdrBytes x)) p).k sigIl.sg) :
    NodeFacts6 Φ trOf σOf σlOf x q := by
  set M := memTi Ti L (pwOf Ti (hdrBytes x)) p with hMdef
  have hfl : M.k (pbC + 1) = 1 := flag_cell hpub L x p hb
  have hks := sigKS_of_alias hout hlink hA
  have hin : QIn6 P6 opensP18 lay6 (wsOf M) M :=
    ⟨hfl, fun j hj ↦ (laneK_wsOf M hj).symm, fun _ hx ↦ qlt_of_cst hcst _ hx, hpb⟩
  exact ⟨Ti, L, hτ, pwOf Ti (hdrBytes x), p, wsOf M, N, 4002, ks, Yl, Mx, X, hQ, hwf, htw, hE3, hok, hrd, hg,
    hin, wsOf_length M, hinj, hN, hNs, hinj', hfl, hks.1, hbits, hfl, hks.2, hbitsL,
    powRowsHold_of_tgoodE Ti L hτ _ p hok hE3 hg hpow, by norm_num, hout, hlink, nBlk_P6, hM,
    md_of_alias hA, hdec, hvk, hcL, htr, hσ, hσl⟩

end Lvm6.Node.Dep
