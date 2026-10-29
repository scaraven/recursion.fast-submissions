-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`'s `Ŵ₀(P₀)`; track R4i). The 3.x
-- template is `FRSoundnessFrW0V` (`zSrc_val` … `eSrc_val`, `p0_vals`, `w0V_run`).
import FRSoundness4R4Wt

/-!
# `finPf`'s `Ŵ₀(P₀)` on the run is T4's `wHatL … 0`

* **The claim points** (`rsSrc4_val`): the kind's claim sources (`rsSrc4`: Z, Lc, Sh at the kind's
  `m`, a node's E4 `r′`) read the log's `rsPtsL4` (`zSrc_val4`, `lcSrc_val4`, `shSrc_val4`,
  `eSrc_val4`); the tables pick them (`ptIx_seg4`, `ptIx_node4`).
* **`P₀`** (`p0_vals4`): `gP0Regs` holds `T4.ptL es 0`.
* **The cells** (`cellsVal4_sum`, `eqCellK4_eq`): `gCellsOpsK`'s accumulator over `nc = 25`
  coordinates is `Σ_k κ′^(k+2)·eq(P₀, cell_k)` over the kind's `m − 7`: a coordinate past `m − 7`
  has bit `0` and `ρ_v = 0`, factor `1`.
* **`w0V4_eq4`**: with `rsWeight` at the kind's spec (`rsSpec4`), `w0V4 = T4.wHatL W₀ L es 0` at
  `W₀ := P4b.W₀L4 N4c.kf4 cells` (`wHat0_spec4`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## Windows of a rounds phase's challenges -/

theorem rchs_drop (b : ℕ) (es : Log) (n d : ℕ) :
    (rchs b es n).drop d = (List.range (n - d)).map (fun l => rch b es (d + l)) := by
  apply List.ext_getElem (by simp [rchs])
  intro j h1 h2; simp [rchs]

theorem rchs_take (b : ℕ) (es : Log) {n t : ℕ} (h : t ≤ n) : (rchs b es n).take t = rchs b es t := by
  apply List.ext_getElem (by simp [rchs]; omega)
  intro j h1 h2; simp [rchs]

theorem srcF_map (R : Array Val) (l : List Reg) :
    (l.map PtSrc.f).map (srcVal R) = (l.map (fv R)).map (algebraMap F K) := by
  simp [srcVal, K.smulF_one]

/-! ## The claim sources -/

/-- **The kind's claim sources** (`gPfPts`' claims at the kind's `m`; `rsPtsL4`'s order). -/
def rsSrc4 (κ : CKind) (fi : FinIn) : List (List PtSrc) :=
  [zSrc fi κ.m, gLcSrc seq4 fi κ.m, gShSrc seq4 fi κ.m] ++
    match κ with
    | .node ν => [(chals fi "E4" (P4b.ncR ν)).map .f]
    | .seg _ => []

theorem seq4_mStar : seq4.mStar = 32 := by rw [seq4_eq]

/-- **A segment's tables pick its claim sources.** -/
theorem ptIx_seg4 (σ : SegKind) (κ : Kind) (fi : FinIn) :
    ((segFinP σ).kv.ptIx κ).map (fun j => (gPfPts (segFinP σ) fi).getD j []) = rsSrc4 (.seg σ) fi := by
  cases σ <;> simp (config := { decide := true }) [segFinP, kvOf, segFams, gPfPts, rsSrc4, seq4_mStar,
    SegKind.m, CKind.m]

/-- **A node's tables pick its claim sources** (E4's point of length `m − 7`). -/
theorem ptIx_node4 (ν : NodeKind) (cells : List ℕ) (κ : Kind) (fi : FinIn) :
    ((nodeFinP ν cells).kv.ptIx κ).map (fun j => (gPfPts (nodeFinP ν cells) fi).getD j []) =
      rsSrc4 (.node ν) fi := by
  cases ν <;> simp (config := { decide := true }) [nodeFinP, kvOf, nodeFams, nodeE4s, gPfPts, rsSrc4,
    seq4_mStar, NodeKind.m, CKind.m, P4b.ncR]

section Run
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

theorem chalsK_view4 {name : String} {n f k : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 2 false) (hix : phaseIx name = n) :
    (chals fi name k).map (fv R) = rchs (phStart4 n) (fsOf tr (itemsOf seq4)) k :=
  chals_view4 h hfi hR hn hsh hix le_rfl

theorem zSrc_val4 {m : ℕ} (hm : m ≤ 32) :
    (zSrc fi m).map (srcVal R) = (zPtL m (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 h hfi hR hn3 (by rw [e3]) (by norm_num) phaseIx_vals.1 (a := m - 13) (by omega)
  rw [show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  rw [zSrc, zPtL, List.map_append, List.map_append, srcF_map, hco, List.map_map, List.map_map, List.map_map]
  rfl

theorem lcSrc_val4 {m : ℕ} (hm1 : 14 ≤ m) (hm : m ≤ 32) :
    (gLcSrc seq4 fi m).map (srcVal R) = (lcPtL m (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) (by rw [seq4_eq]; rfl)
  obtain ⟨hn5, e5⟩ := ph4 (n := 5) (x := ("Z3", Sh.rounds fZ3 26 3 false)) (by rw [seq4_eq]; rfl)
  have hL := chalsK_view4 h hfi hR hn8 (by rw [e8]) phaseIx_vals.2.2.2.2.1
  have hZ := chals_view4 h hfi hR hn5 (by rw [e5]) phaseIx_vals.2.2.1 (a := 26) le_rfl
  rw [show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hL
  rw [show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hZ
  have e1 : ((chals fi "L2" 14).drop 7).map (fv R) =
      (List.range 7).map (fun l => rch 69 (fsOf tr (itemsOf seq4)) (7 + l)) := by
    rw [List.map_drop, hL, rchs_drop]
  have e2 : (((chals fi "Z3" 26).take (m - 6)).drop 8).map (fv R) =
      (List.range (m - 14)).map (fun l => rch 15 (fsOf tr (itemsOf seq4)) (8 + l)) := by
    rw [List.map_drop, List.map_take, hZ, rchs_take _ _ (by omega), rchs_drop, show m - 6 - 8 = m - 14 by omega]
  rw [gLcSrc, lcPtL, show seq4.z3 = 26 by rw [seq4_eq], List.map_append, List.map_append, srcF_map,
    srcF_map, e1, e2]

theorem shSrc_val4 {m : ℕ} (hm1 : 14 ≤ m) (hm : m ≤ 32) :
    (gShSrc seq4 fi m).map (srcVal R) = (shPtL m (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn12, e12⟩ := ph4 (n := 12) (x := ("S2", Sh.rounds fS2 28 2 false)) (by rw [seq4_eq]; rfl)
  have hS := chalsK_view4 h hfi hR hn12 (by rw [e12]) phaseIx_vals.2.2.2.2.2.2.2.1
  rw [show phStart4 12 = 114 by rw [phStart4, fsStarts4_eq]; rfl] at hS
  have e1 : (((chals fi "S2" 28).drop (m - 7)).take 3).map (fv R) =
      (List.range 3).map fun l => rch 114 (fsOf tr (itemsOf seq4)) (m - 7 + l) := by
    rw [List.map_take, List.map_drop, hS, rchs_drop, ← List.map_take, List.take_range,
      show min 3 (28 - (m - 7)) = 3 by omega]
  have e2 : ((chals fi "S2" 28).take (m - 14)).map (fv R) =
      (List.range (m - 14)).map (rch 114 (fsOf tr (itemsOf seq4))) := by
    rw [List.map_take, hS, rchs_take _ _ (by omega)]; rfl
  rw [gShSrc, shPtL, show seq4.s2 = 28 by rw [seq4_eq], List.map_append, List.map_append,
    List.map_append, List.map_append, srcF_map, srcF_map, e1, e2]
  simp [srcVal]

theorem eSrc_val4 (ν : NodeKind) :
    ((chals fi "E4" (P4b.ncR ν)).map PtSrc.f).map (srcVal R) =
      (P4b.ePtL4 (P4b.ncR ν) (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn21, e21⟩ := ph4 (n := 21) (x := ("E4", Sh.rounds fE 25 2 false)) (by rw [seq4_eq]; rfl)
  have hE := chals_view4 h hfi hR hn21 (by rw [e21]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (a := P4b.ncR ν) (by cases ν <;> decide)
  rw [show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at hE
  rw [srcF_map, hE]
  rfl

/-- **The claim sources read the log's claim points** (every chain kind). -/
theorem rsSrc4_val (κ : CKind) :
    (rsSrc4 κ fi).map (fun s => (s.map (srcVal R)).toArray) =
      (P4b.rsPtsL4 κ (fsOf tr (itemsOf seq4))).map fun l => (l.map (algebraMap F K)).toArray := by
  have hm := CKind.m_mem κ
  have hz := zSrc_val4 h hfi hR (m := κ.m) (by omega)
  have hl := lcSrc_val4 h hfi hR (m := κ.m) (by omega) (by omega)
  have hs := shSrc_val4 h hfi hR (m := κ.m) (by omega) (by omega)
  cases κ with
  | seg σ => simp only [rsSrc4, P4b.rsPtsL4, List.map_append, List.map_cons, List.map_nil, hz, hl, hs]
  | node ν =>
    simp only [rsSrc4, P4b.rsPtsL4, List.map_append, List.map_cons, List.map_nil, hz, hl, hs,
      eSrc_val4 h hfi hR ν]

/-- **`P₀`'s registers hold `T4.ptL es 0`** (3.x's `p0_vals`). -/
theorem p0_vals4 (κ : CKind) :
    ((gP0Regs seq4 fi κ.m).map fun x => (rd R x).toK).length = κ.m - 7 ∧
      ∀ v < κ.m - 7, ((gP0Regs seq4 fi κ.m).map fun x => (rd R x).toK).getD v 0 =
        T4.ptL (fsOf tr (itemsOf seq4)) 0 v := by
  obtain ⟨b, hs, -, hv, -⟩ := gSRegs_view4 h hfi hR (i := 0) (by norm_num)
  have ht := (tail_vals4 h hfi hR κ (k := 1) le_rfl (by norm_num)).1
  have hA : (gSRegs seq4 fi 0).map (fun x => (rd R x).toK) =
      (List.range (hEll 0)).map (T4.sAt (fsOf tr (itemsOf seq4)) 0) := by
    rw [hs, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, hv j (List.mem_range.mp hj)]
    rfl
  have hn : κ.m - 7 = hEll 0 + T4.mLog κ 0 := by
    rw [← nrP_zero4, T4.nrP, T4.lvl_ell κ (by norm_num)]
  rw [gP0Regs, List.map_append, hA, ht]
  refine ⟨by simp [hn], fun v hv' => ?_⟩
  rw [T4.ptL_lt (k := 0) (by norm_num)]
  dsimp only
  by_cases h0 : v < hEll 0
  · rw [List.getD_append _ _ _ _ (by simpa using h0), if_pos h0,
      List.getD_eq_getElem _ _ (by simpa using h0)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simpa using h0), if_neg h0]
    simp only [List.length_map, List.length_range]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, zero_add]

end Run

/-! ## The cells -/

theorem cellsVal4_sum (nc : ℕ) (ρ : Array K) (kp : F) (cell : ℕ → ℕ) :
    ∀ (n j : ℕ) (pw : F) (A : K), cellsVal4 nc ρ kp cell n j pw A =
      A + ∑ k ∈ range n, algebraMap F K (pw * kp ^ k) * eqCellK4 nc ρ (cell (j + k))
  | 0, _, _, A => by simp [cellsVal4]
  | n + 1, j, pw, A => by
    rw [cellsVal4, cellsVal4_sum nc ρ kp cell n (j + 1), sum_range_succ', K.smulF_eq_mul,
      ← K.algebraMap_eq_ofF, pow_zero, mul_one, add_zero]
    have e : ∀ k ∈ range n, algebraMap F K (pw * kp * kp ^ k) * eqCellK4 nc ρ (cell (j + 1 + k)) =
        algebraMap F K (pw * kp ^ (k + 1)) * eqCellK4 nc ρ (cell (j + (k + 1))) := fun k _ => by
      rw [pow_succ, mul_assoc pw, mul_comm (kp ^ k) kp, show j + 1 + k = j + (k + 1) by ring]
    rw [sum_congr rfl e]
    ring

/-- **`finPf`'s two cell chains** (the public cells from `κ′²`, then, gated, the reserve's from
`κ′^{2+n₁}`) sum `Σ_k κ′^{k+2}·eq(cell_k, ρ)` over the cells `cs ++ rs` (revision 4.4.2; with the gate
off the reserve's list is empty). -/
theorem cells2_sum (nc : ℕ) (ρ : Array K) (kp : F) (cs rs : List ℕ) (g : Bool) (n1 n2 : ℕ)
    (h1 : n1 = cs.length) (h2 : rs.length = if g = true then n2 else 0) :
    (if g = true then cellsVal4 nc ρ kp (fun j => rs.getD j 0) n2 0 (kp * kp * kp ^ n1)
        (cellsVal4 nc ρ kp (fun j => cs.getD j 0) n1 0 (kp * kp) 0)
      else cellsVal4 nc ρ kp (fun j => cs.getD j 0) n1 0 (kp * kp) 0) =
      ∑ k ∈ range (cs ++ rs).length, algebraMap F K (kp ^ (k + 2)) * eqCellK4 nc ρ ((cs ++ rs).getD k 0) := by
  have hA : cellsVal4 nc ρ kp (fun j => cs.getD j 0) n1 0 (kp * kp) 0 =
      ∑ k ∈ range cs.length, algebraMap F K (kp ^ (k + 2)) * eqCellK4 nc ρ ((cs ++ rs).getD k 0) := by
    rw [cellsVal4_sum, zero_add, h1]
    refine sum_congr rfl fun k hk => ?_
    rw [zero_add, List.getD_append _ _ _ _ (mem_range.1 hk), show kp * kp * kp ^ k = kp ^ (k + 2) by ring]
  rw [List.length_append, sum_range_add, ← hA]
  split_ifs at h2 ⊢ with hg
  · rw [cellsVal4_sum, h2]
    refine congrArg₂ (· + ·) rfl (sum_congr rfl fun k _ => ?_)
    rw [zero_add, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, h1]
    congr 2; ring
  · rw [h2, range_zero, sum_empty, add_zero]

/-- **`eqCellK4` over `nc` coordinates is `eq(cell, ρ)` over `ρ`'s `n ≤ nc`** for a cell below `2^n`
(characteristic 2; the zero-padded coordinates give `1`). -/
theorem eqCellK4_eq {nc n : ℕ} (ρ : List K) (hρ : ρ.length = n) (hn : n ≤ nc) {c : ℕ} (hc : c < 2 ^ n) :
    eqCellK4 nc ρ.toArray c = eqCell (FR.ptOf n ρ) c := by
  have h1 : ∀ x : K, 1 + x = 1 - x := fun x => by rw [sub_eq_add_neg, CharTwo.neg_eq]
  have hl : ∀ (l : List K), l.foldl (· * ·) 1 = l.prod := fun l => by
    rw [← List.prod_eq_foldl]
  rw [eqCellK4, hl, list_prod_range, ← prod_range_mul_prod_Ico _ hn]
  have hhi : ∏ v ∈ Ico n nc, (if c.testBit v then ρ.toArray.getD v 0 else 1 + ρ.toArray.getD v 0) = 1 := by
    refine prod_eq_one fun v hv => ?_
    have hv' := (mem_Ico.1 hv).1
    have hb : c.testBit v = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hv'))
    have hz : ρ.toArray.getD v 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_none (by omega)]; rfl
    simp [hb, hz]
  rw [hhi, mul_one, eqCell, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun v _ => ?_
  have hg : ρ.toArray.getD v 0 = FR.ptOf n ρ v := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, FR.ptOf, List.getD_eq_getElem?_getD]
  rw [hg, h1]

/-! ## `Ŵ₀(P₀)` -/

/-- **The kind's `rsWeight` specification** (a node's `rsWeightS4 ν`, a segment's `rsWeightS`). -/
noncomputable def rsSpec4 : CKind → Array F → List (Array K) → F → F → Array K → K
  | .node ν => Impl.rsWeightS4 ν
  | .seg _ => Impl.rsWeightS

/-- **`finPf`'s `Ŵ₀(P₀)` on an accepted run is T4's `wHatL … 0`** (3.x's `w0V_run`), for tables `P`
whose claim indices pick the kind's sources (`ptIx_seg4`, `ptIx_node4`), whose cells are the kind's
(`nc = 25` coordinates), with `rsWeight` at the kind's spec. -/
theorem w0V4_eq4 {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {κc : CKind} (hk : kindOfC (fsOf tr (itemsOf seq4)) = κc)
    {P : FinP} (hT : FinTabs4 P p.tix κc)
    (hpts : (P.kv.ptIx p.tix).map (fun j => (gPfPts P fi).getD j []) = rsSrc4 κc fi)
    {cells : NodeKind → List ℕ} (hc : ∀ ν, ∀ c ∈ cells ν, c < 2 ^ P4b.ncR ν)
    (hcl : P.cells ++ P.rcells = P4b.cellsC cells κc) (hncell : P.ncell = P.cells.length)
    (hrc : P.rcells.length = if (P.rsvOps && P.rsv) = true then P.nrcell else 0) (hnc : P.nc = 25)
    (hrs : ∀ r ps k β ρ, r.size = 7 → 23 ≤ ρ.size → impl.rsWeight r ps k β ρ = rsSpec4 κc r ps k β ρ)
    (L : Log) :
    w0V4 impl p.tix fi R P = T4.wHatL (P4b.W₀L4 N4c.kf4 cells) L (fsOf tr (itemsOf seq4)) 0 := by
  obtain ⟨hρl, hρv⟩ := p0_vals4 h hfi hR κc
  rw [wHat0_spec4 cells hc L _ _ (by rw [hk]; exact hρl) (by rw [hk]; exact hρv), hk]
  have hrho : rho4 p.tix fi R P = ((gP0Regs seq4 fi κc.m).map fun x => (rd R x).toK).toArray := by
    rw [rho4, ptPf, slot_p04 P fi _ hT.nf, pfFamM_eq hT, hT.S]
    simp [ptV, srcVal]
  have hpts' : (P.kv.ptIx p.tix).map (ptPf fi R P) =
      (P4b.rsPtsL4 κc (fsOf tr (itemsOf seq4))).map fun l => (l.map (algebraMap F K)).toArray := by
    rw [← rsSrc4_val h hfi hR, ← hpts, List.map_map]; rfl
  have hr7 : ptF R ((List.range 7).map fun q => (coordsR fi "RS1").getD q 0) =
      (P4b.rsRL4 (fsOf tr (itemsOf seq4))).toArray := by
    simp only [ptF, P4b.rsRL4, List.map_map]
    exact congrArg List.toArray (List.map_congr_left fun q hq =>
      rs1_val4 h hfi hR (by simp at hq; omega))
  have hκ7 : fv R ((coordsR fi "RS1").getD 7 0) = P4b.rsKL4 (fsOf tr (itemsOf seq4)) :=
    rs1_val4 h hfi hR (by norm_num)
  have h23 : 23 ≤ (((gP0Regs seq4 fi κc.m).map fun x => (rd R x).toK).toArray).size := by
    rw [List.size_toArray, hρl]; have := CKind.m_mem κc; omega
  unfold w0V4 cv4
  rw [hrho, hpts', hr7, hκ7, hrs _ _ _ _ _ (by simp [P4b.rsRL4]) h23, hT.node]
  cases κc with
  | seg σ =>
    simp only [CKind.isNode, Bool.false_eq_true, if_false, add_zero, P4b.cellsC, List.length_nil,
      range_zero, sum_empty]
    simp only [rsSpec4, rsWS4]
  | node ν =>
    simp only [CKind.isNode, if_true]
    obtain ⟨hn10, e10⟩ := ph4 (n := 10) (x := ("L3β", Sh.squeezes 1 .one)) rfl
    obtain ⟨-, hβ⟩ := one_name_view4 h hfi hR hn10 (by rw [e10]) phaseIx_vals.2.2.2.2.2.1
    rw [show phStart4 10 = 98 by rw [phStart4, fsStarts4_eq]; rfl] at hβ
    obtain ⟨hn25, e25⟩ := ph4 (n := 25) (x := ("B'", Sh.squeezes 1 .one)) (by rw [seq4_eq]; rfl)
    obtain ⟨-, hkp⟩ := one_name_view4 h hfi hR hn25 (by rw [e25]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [show phStart4 25 = 331 by rw [phStart4, fsStarts4_eq]; rfl] at hkp
    have hkp' : kp4 fi R = P4b.kpL4 (fsOf tr (itemsOf seq4)) := hkp
    rw [hβ, hkp', hnc, cells2_sum _ _ _ _ _ _ _ _ hncell hrc, hcl]
    refine congrArg₂ (· + ·) (by simp only [rsSpec4, rsWS4]) (sum_congr rfl fun k hk' => ?_)
    have hkl := mem_range.1 hk'
    simp only [P4b.cellsC] at hkl ⊢
    have hmem : (cells ν).getD k 0 ∈ cells ν := by
      rw [List.getD_eq_getElem _ _ hkl]; exact List.getElem_mem _
    rw [eqCellK4_eq _ hρl (by simp only [CKind.m]; cases ν <;> decide) (hc ν _ hmem)]

/-! ## `hW` on an accepted run's fields -/

/-- **`finPf`'s `Ŵ₄(P₄)` on an accepted run's fields is `T4.wHatL W₀ L es 4`** (`hW` of
`finRest4_full`), at `W₀ := P4b.W₀L4 N4c.kf4 cells`: the level steps (`wV_eq4`) from `Ŵ₀(P₀)`
(`w0V4_eq4`). -/
theorem wV4_of_fields {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace} {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val}
    {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) {κc : CKind}
    (hk : kindOfC (fsOf tr (itemsOf seq4)) = κc) (hT : FinTabs4 P p.tix κc)
    (hpts : (P.kv.ptIx p.tix).map (fun j => (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).getD j []) =
      rsSrc4 κc ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩)
    {cells : NodeKind → List ℕ} (hc : ∀ ν, ∀ c ∈ cells ν, c < 2 ^ P4b.ncR ν)
    (hcl : P.cells ++ P.rcells = P4b.cellsC cells κc) (hncell : P.ncell = P.cells.length)
    (hrc : P.rcells.length = if (P.rsvOps && P.rsv) = true then P.nrcell else 0) (hnc : P.nc = 25)
    (hrs : ∀ r ps k β ρ, r.size = 7 → 23 ≤ ρ.size → impl.rsWeight r ps k β ρ = rsSpec4 κc r ps k β ρ)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) :
    wV4 impl p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P =
      T4.wHatL (P4b.W₀L4 N4c.kf4 cells) L (fsOf tr (itemsOf seq4)) 4 := by
  have hL : (L.map Prod.fst).Nodup := by by_contra hr; exact hb (.inr (.inr (.inr hr)))
  have hE := hF.ext 11 (by omega)
  have hw0 := w0V4_eq4 hF.sk (fi := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩) rfl hE hk hT hpts hc hcl hncell
    hrc hnc hrs L
  have htl : ∀ k < 4, tl4 p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P (k + 1) =
      ((gTailRegs seq4 ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (kindOfC (fsOf tr (itemsOf seq4))).m (k + 1)).map
        fun x => (rd (Rs 11) x).toK).toArray := fun k hk4 => by
    rw [tl4, Nat.add_sub_cancel, ptPf, slot_tl4 P _ _ hT.nf hk4, pfFamM_eq hT, hT.S, hk]
    simp [ptV, srcVal]
  unfold wV4
  exact wV_eq4 hF.sk (fi := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩) rfl hE hL hin hm ht htl _ hw0

end FR.Snd.R4
