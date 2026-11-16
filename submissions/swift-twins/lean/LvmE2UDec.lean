-- New for lvm2 U-TAPE (UT-V): V_S's `E2` front at stage S2GU on the reader `DM` (the merged tape: T1 in R-BP2's B1
-- order with the 50 scalars, the depth-24 GKR over `logN + 1` row bits, the wire with the sponge terms, three slot
-- reductions), its claims as opening items, and the decision program at a parameter set `p` (generic in `p`; the
-- layout is `layout0 p`: at stage 3 the `Y` block in the field `ks`, the stream block in `s`).
import LvmE2VDecG
import LvmE2UProg
import LvmS2GUFront

/-!
# V_S's front at S2GU

Phases `tape` and `wire` of `phasesS2GU` (`ref/utape.py`'s `CHtape`, `CHwire`), on the S2GT fast twins (`slotDFG`,
`tapeGkrDF`, `wireTargetDF`, the row switch's data `rowSwitchDR`):
* **`tapeUDG rs p s n`**: the separator, `r_0 … r_{w−1}` (ground, `c = 1`), 50 `E2` scalars, `r_w` (`c = 1`), the GKR
  of `Shape {w + 1, 24}` on T1's output lanes (`tapeOutF`), `n`'s range, the wire;
* **`wireUDG rs p s n claim`**: the wire sumcheck (`w` rounds of degree 2), `g_D, g_Y, g_M`, the final check
  `K̃_ch(σ)·g_D + e'·(K̃_ks(σ')·g_Y + Ĩ_ks(σ')·g_M)`, then the slot reductions of `D` (2 rounds, as S2GT), `Y` (5
  rounds at `σ'`) and `M` (5 rounds at `(σ', 0)`), each with its row switch;
* **`frontItemsU A p pub tp`**: the claims, in the order `a_0 … a_3` (`D`, tails as S2GT), `b_0 … b_24` (`Y`), the
  rows of `D` (tail as S2GT), `Y` and `M`, the boundary words `h`;
* **`decideProgUG p pR N vk c`**: S2GT's decision program (`decideProgFFGM`'s body) with the merged front.
-/

set_option autoImplicit false

namespace Lvm.E2U

open Lvm DM Lvm.E2V Lvm.E2T

/-! ## Layout constants -/

/-- The slot bits of the `Y` block and of the stream block (32 slots, 32 columns). -/
abbrev slotBitsU : Nat := 5

/-! ## Outputs -/

/-- A slot reduction's output: the slot point and last claim, the 64 slices, the row switch. -/
abbrev SlotU (ρ : Type) : Type := (List FE2 × FE2) × List FE2 × ρ

/-- The wire's output at S2GU. -/
structure WireU (ρ : Type) where
  /-- The wire point `σ` and the final claim. -/
  sc : List FE2 × FE2
  /-- `g_D, g_Y, g_M`. -/
  g : List FE2
  /-- `D`'s slot reduction. -/
  d : SlotU ρ
  /-- The `Y` block's slot reduction. -/
  y : SlotU ρ
  /-- The stream block's slot reduction. -/
  m : SlotU ρ

/-- The merged tape's output at S2GU. -/
structure TapeU (ρ : Type) where
  /-- `r_0 … r_{w−1}`. -/
  r : List FE2
  /-- `r_w`. -/
  rw : FE2
  /-- The 50 scalars `a_0 … a_24, b_0 … b_24`. -/
  ab : List FE2
  /-- The GKR's input claim. -/
  claim : E2V.KClaim FE2
  /-- The wire. -/
  wo : WireU ρ

/-! ## The programs -/

/-- **A slot reduction with its weights given at the slot point** (`slotDFG` with `W̃_z(τ)` read from `wz τ`, an
array of the 64 bits' weights, formed once per `τ`): `b` rounds, 64 slices, the check, the row switch. -/
def slotDFW {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (b sb blk : Nat) (wz : List FE2 → Array FE2) (pt : List FE2)
    (v : FE2) : DM (SlotU ρ) := do
  let sl ← sumcheckD gC2 v 3 (List.replicate b none)
  let sv ← readE2s 64
  let a := wz sl.1
  require (sl.2 == sumF ((List.range 64).map fun z => a.getD z 0 * sv.getD z 0))
  let row ← rs (pt ++ sl.1 ++ selPtF blk sb) sv
  pure (sl, sv, row)

/-- **The slot weights of `nl` lanes in slots `0 … nl − 1`** (`W(l, z) = ω_{64l + z}`) at the slot point `τ`: the
`2^b` values `eq(τ, o)` once, then `Σ_{l<nl} eq(τ, l)·ω_{64l + z}` for each bit `z`. -/
def lanesW (b nl : Nat) (ω : Array FE2) (τ : List FE2) : Array FE2 :=
  let e := ((List.range (2 ^ b)).map (E2V.eqAtF τ)).toArray
  (List.range 64).toArray.map fun z => sumF ((List.range nl).map fun l => e.getD l 0 * ω.getD (64 * l + z) 0)

theorem lanesW_getD {b nl : Nat} (hnl : nl ≤ 2 ^ b) (ω τ : List FE2) {z : Nat} (hz : z < 64) :
    (lanesW b nl ω.toArray τ).getD z 0 =
      E2V.slotWF b (fun o z => if o < nl then ω.getD (64 * o + z) 0 else 0) τ z := by
  rw [lanesW, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hz,
    Option.map_some, Option.getD_some, E2V.slotWF_eq, sumF_map_range,
    ← Finset.sum_range_add_sum_Ico _ hnl, Finset.sum_eq_zero (s := Finset.Ico nl (2 ^ b)) fun o ho => by
      rw [ite_eq_right (by (clear * - ho; simp only [Finset.mem_Ico] at ho; omega)), mul_zero], add_zero]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [ite_eq_left hl', list_toArray_getD, list_toArray_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by (clear * - hl' hnl; omega)), Option.map_some, Option.getD_some]

/-- **`slotDFW` on `lanesW` is `slotDFG`** on the lane weights (`nl ≤ 2^b`). -/
theorem slotDFW_lanesW {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) {b nl : Nat} (hnl : nl ≤ 2 ^ b)
    (sb blk : Nat) (ω : List FE2) (W : Nat → Nat → FE2)
    (hW : ∀ o z, W o z = if o < nl then ω.getD (64 * o + z) 0 else 0) (pt : List FE2) (v : FE2) :
    slotDFW rs b sb blk (lanesW b nl ω.toArray) pt v = slotDFG rs b sb blk W pt v := by
  have hW' : W = fun o z => if o < nl then ω.getD (64 * o + z) 0 else 0 := funext fun o => funext fun z => hW o z
  subst hW'
  unfold slotDFW slotDFG
  refine congrArg (sumcheckD gC2 v 3 (List.replicate b none) >>= ·) (funext fun sl => ?_)
  refine congrArg (readE2s 64 >>= ·) (funext fun sv => ?_)
  have hm : (List.range 64).map (fun z => (lanesW b nl ω.toArray sl.1).getD z 0 * sv.getD z 0) =
      (List.range 64).map (fun z => E2V.slotWF b (fun o z => if o < nl then ω.getD (64 * o + z) 0 else 0) sl.1 z *
        sv.getD z 0) :=
    List.map_congr_left fun z hz => by rw [lanesW_getD hnl ω sl.1 (List.mem_range.mp hz)]
  simp only [hm]

/-- The `Y` block's slot reduction on `lanesW` (25 lanes) is `slotDFG` on `yWG`. -/
theorem slotDFW_yWG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (sb blk : Nat) (ω pt : List FE2) (v : FE2) :
    slotDFW rs slotBitsU sb blk (lanesW slotBitsU 25 ω.toArray) pt v = slotDFG rs slotBitsU sb blk (yWG ω) pt v :=
  slotDFW_lanesW rs (by (clear * -; simp only [slotBitsU]; omega)) sb blk ω (yWG ω) (fun _ _ => rfl) pt v

/-- The stream block's slot reduction on `lanesW` (17 lanes) is `slotDFG` on `mWG`. -/
theorem slotDFW_mWG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (sb blk : Nat) (ω pt : List FE2) (v : FE2) :
    slotDFW rs slotBitsU sb blk (lanesW slotBitsU 17 ω.toArray) pt v = slotDFG rs slotBitsU sb blk (mWG ω) pt v :=
  slotDFW_lanesW rs (by (clear * -; simp only [slotBitsU]; omega)) sb blk ω (mWG ω) (fun _ _ => rfl) pt v


/-- **The wire at S2GU** (`wireU`'s items), generic in the row switch `rs`: the wire sumcheck from S2GT's target,
`g_D, g_Y, g_M`, the final check with the sponge terms, the three slot reductions. -/
def wireUDG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (p : Params) (s : List FK) (n : Nat)
    (claim : E2V.KClaim FE2) : DM (WireU ρ) := do
  let sc ← sumcheckD gC2 (wireTargetDF (sBitsD s) n claim) 3 (List.replicate p.logN none)
  let g ← readE2s 3
  let L := layout0 p
  let σ' := sc.1.take p.ksLog
  let base := 2 ^ p.logN
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF p.ksLog p.logN sc.1 * (kksF contIvU claim.point claim.mu σ' base * g.getD 1 0 +
      ikEvalP claim.point claim.mu σ' base * g.getD 2 0))
  let d ← slotDFG rs 2 (dSelBits p) (dSel p) (dWA claim.weights.toArray) sc.1 (g.getD 0 0)
  let y ← slotDFW rs slotBitsU (p.nuMain - (p.ksLog + slotBitsU)) (L.ks / 2 ^ (p.ksLog + slotBitsU))
    (lanesW slotBitsU 25 claim.weights.toArray) σ' (g.getD 1 0)
  let m ← slotDFW rs slotBitsU (p.nuMain - p.nuRec) (L.s / 2 ^ p.nuRec) (lanesW slotBitsU 17 claim.weights.toArray)
    (σ' ++ [0]) (g.getD 2 0)
  pure ⟨sc, g, d, y, m⟩

/-- **The merged tape at S2GU** (`tapeU`'s items), generic in the row switch: the separator, `r_{<w}`, the 50
scalars, `r_w`, the GKR on T1's output lanes over `w + 1` row bits, `n`'s range, the wire. -/
def tapeUDG {ρ : Type} (rs : List FE2 → List FE2 → DM ρ) (p : Params) (s : List FK) (n : Nat) :
    DM (TapeU ρ) := do
  sepE2
  let r ← samplesG gC1 p.logN
  let ab ← readE2s (2 * 25)
  let rw ← sampleG gC1
  let claim ← tapeGkrDF (p.logN + 1) (r ++ [rw]) (t1ValsF p.logN p.ksLog (r ++ [rw]) ab)
  require (decide (1 ≤ n ∧ n ≤ 2 ^ p.logN))
  let wo ← wireUDG rs p s n claim
  pure ⟨r, rw, ab, claim, wo⟩

/-! ## Row claims on their blocks -/

section RowBlock

open Lvm.Shape (eqEval_append eqEval_cons eqEval_nil_left eqEval_nil_right length_selectorPointF)

/-- The bits of `s` below `m`, lowest first. -/
def selBits (s m : Nat) : List Bool := (List.range m).map fun i => decide ((s >>> i) % 2 = 1)

theorem selPtF_bits (s m : Nat) :
    (E2V.selPtF s m : List FE2) = (selBits s m).map fun c => if c then 1 else 0 := by
  unfold E2V.selPtF selBits
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  by_cases h : (s >>> i) % 2 = 1 <;>
    simp only [Function.comp_apply, h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem selectorPoint_bits (s m : Nat) :
    selectorPoint s m = (selBits s m).map fun c => if c then (1 : FE) else 0 := by
  unfold selectorPoint selBits
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (s >>> i) with h | h <;> simp only [Function.comp_apply, h] <;> rfl

theorem selectorPoint_add (s m n : Nat) :
    selectorPoint s (m + n) = selectorPoint s m ++ selectorPoint (s >>> m) n := by
  unfold selectorPoint
  rw [List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  rw [Function.comp_apply, Nat.shiftRight_add]

/-- Coordinate `j` of the basis element `β_k` (`j, k < 128`). -/
theorem bitFE2F_basis {k j : Nat} (hk : k < 128) (hj : j < 128) : bitFE2F (basisFE2 k) j = decide (j = k) := by
  rw [bitFE2F_eq _ _ hj]
  unfold bitFE2 basisFE2
  by_cases hj6 : j < 64 <;> by_cases hk6 : k < 64
  · rw [ite_eq_left hj6, ite_eq_left hk6]
    have h2 : (2 ^ k : Nat).toUInt64.toNat = 2 ^ k :=
      by rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk6)]
    simp only [h2, Nat.testBit_two_pow, eq_comm]
  · rw [ite_eq_left hj6, ite_eq_right hk6]
    rw [show (0 : FK).val.toNat = 0 from rfl, Nat.zero_testBit]
    exact (decide_eq_false (by (clear * - hj6 hk6; omega))).symm
  · rw [ite_eq_right hj6, ite_eq_left hk6]
    rw [show (0 : FK).val.toNat = 0 from rfl, Nat.zero_testBit]
    exact (decide_eq_false (by (clear * - hj6 hk6; omega))).symm
  · rw [ite_eq_right hj6, ite_eq_right hk6]
    have h2 : (2 ^ (k - 64) : Nat).toUInt64.toNat = 2 ^ (k - 64) :=
      by rw [Nat.toUInt64_eq, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by (clear * - hk; omega)))]
    simp only [h2, Nat.testBit_two_pow]
    exact decide_eq_decide.mpr (by (clear * - hj6 hk6; omega))

/-- **A step on a Boolean coordinate is a scalar**: `tColsW 0` gives `(1 + r)·u`, `tColsW 1` gives `r·u`. -/
theorem tStepN_sel (c : Bool) (r : FE) (u : Array FE) {k : Nat} (hk : k < 128) :
    (tStepN (tColsW (if c then 1 else 0), r) u).getD k 0 = (1 + (if c then 1 else 0) + r) * u.getD k 0 := by
  rw [tStepN_eq, tStepT_getD u _ r hk]
  cases c
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, mul_zero,
      Finset.sum_eq_zero fun j hj => by
        rw [bitFE2F_eq _ _ (Finset.mem_range.mp hj), ite_eq_right (by simp [bitFE2, show (0 : FK).val.toNat = 0
          from rfl, show ((0 : FE2).re : FK) = 0 from rfl, show ((0 : FE2).im : FK) = 0 from rfl])], add_zero]
    ring
  · rw [ite_eq_left rfl, ite_eq_left rfl, mul_one, Finset.sum_eq_single k (fun j hj hjk => by
        rw [bitFE2F_basis hk (Finset.mem_range.mp hj), ite_eq_right (by simpa using hjk)])
        (fun h => absurd (Finset.mem_range.mpr hk) h), bitFE2F_basis hk hk, ite_eq_left (by simp)]
    ring

theorem rowSuf_nil (cols : List (Array FE2)) (eqA : Array FE) : rowSuf cols eqA [] = eqA := by
  unfold rowSuf
  rw [List.zip_nil_right, List.foldr_nil]

/-- **The transposed product over Boolean coordinates** is `eq(b, sel)` times `eq(r'', ·)`. -/
theorem rowSuf_sel (eqA : Array FE) : ∀ (bs : List Bool) (b : List FE) {k : Nat}, k < 128 →
    (rowSuf (bs.map fun c => tColsW (if c then 1 else 0)) eqA b).getD k 0 =
      eqEval (bs.map fun c => if c then (1 : FE) else 0) b * eqA.getD k 0
  | [], b, k, _ => by
    unfold rowSuf
    rw [List.map_nil, List.map_nil, List.zip_nil_left, List.foldr_nil, eqEval_nil_left, one_mul]
  | c :: bs, [], k, _ => by rw [rowSuf_nil, eqEval_nil_right, one_mul]
  | c :: bs, r :: b, k, hk => by
    have e : rowSuf ((c :: bs).map fun c => tColsW (if c then 1 else 0)) eqA (r :: b) =
        tStepN (tColsW (if c then 1 else 0), r) (rowSuf (bs.map fun c => tColsW (if c then 1 else 0)) eqA b) := by
      unfold rowSuf
      rw [List.map_cons, List.zip_cons_cons, List.foldr_cons]
    rw [e, tStepN_sel c r _ hk, rowSuf_sel eqA bs b hk, List.map_cons, eqEval_cons]
    ring

theorem dot128_scale (u v w : Array FE) (c : FE) (h : ∀ k < 128, w.getD k 0 = c * v.getD k 0) :
    dot128 u w = c * dot128 u v := by
  rw [dot128_eq, dot128_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]; ring

/-- **A row claim on the whole stack whose point ends in a block's selector is the row claim on the block**: for
`|z| = k = blk.variableCount ≤ ν` and `blk.index < 2^ν`, the claim on `⟨ν, 0⟩` with the row weight over
`z ++ sel(blk.index >>> k, ν − k)` (`tensorDotT`, the switched weight) and the claim on `blk` with the row weight over
`z` have the same stack weight and value (in every length of the stack point). -/
theorem onStack_rowSel (nu : Nat) (blk : Placement) (z : List FE2) (eqA : Array FE) (v : FE)
    (hz : z.length = blk.variableCount) (hk : blk.variableCount ≤ nu) (hi : blk.index < 2 ^ nu) :
    BlockClaim.onStack ⟨⟨nu, 0⟩, tensorDotT ((z ++ E2V.selPtF (blk.index >>> blk.variableCount)
        (nu - blk.variableCount)).map tColsW) eqA, v⟩ =
      BlockClaim.onStack ⟨blk, tensorDotT (z.map tColsW) eqA, v⟩ := by
  obtain ⟨k, idx⟩ := blk
  simp only at hz hk hi ⊢
  unfold BlockClaim.onStack
  refine Prod.ext (funext fun x => ?_) rfl
  simp only [Placement.eqAbove, Nat.zero_shiftRight]
  have hzs : (z.map tColsW).length = k := by rw [List.length_map, hz]
  have hsmall : ∀ a : List FE, a.length ≤ k → tensorDotT (z.map tColsW) eqA a =
      dot128 (rowPre ((z.map tColsW).take a.length) a) eqA := fun a ha => by
    rw [← List.append_nil a, tensorDotT_split z eqA a [] (by omega), rowSuf_nil, List.append_nil]
  by_cases hx : x.length ≤ k
  · have h1 : x.take nu = x ++ [] := by rw [List.take_of_length_le (by omega), List.append_nil]
    rw [h1, tensorDotT_split _ eqA x [] (by rw [List.length_append]; omega), rowSuf_nil,
      List.take_of_length_le hx, hsmall x hx, List.map_append, List.take_append_of_le_length (by omega),
      show x.length - nu = 0 by omega, show x.length - k = 0 by omega]
    simp only [selectorPoint, List.range_zero, List.map_nil, eqEval_nil_left]
  · have hxk : k ≤ x.length := by omega
    have ha : (x.take k).length = k := by rw [List.length_take]; omega
    have hsplit : x.take nu = x.take k ++ (x.take nu).drop k := by
      conv_lhs => rw [← List.take_append_drop k (x.take nu)]
      rw [List.take_take, Nat.min_eq_left hk]
    have hb : ∀ j < 128, (rowSuf (((z ++ E2V.selPtF (idx >>> k) (nu - k)).map tColsW).drop k) eqA
        ((x.take nu).drop k)).getD j 0 = eqEval (selectorPoint (idx >>> k) (nu - k)) ((x.take nu).drop k) *
          eqA.getD j 0 := fun j hj => by
      rw [List.map_append, List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append, selPtF_bits, List.map_map, selectorPoint_bits]
      exact rowSuf_sel eqA _ _ hj
    rw [hsplit, tensorDotT_split _ eqA _ _ (by rw [List.length_append, ha]; omega), ha,
      dot128_scale _ eqA _ _ hb, hsmall _ (by omega), ha, List.map_append, List.take_append_of_le_length (by omega)]
    have hE : eqEval (selectorPoint 0 (x.length - nu)) (x.drop nu) *
        eqEval (selectorPoint (idx >>> k) (nu - k)) ((x.take nu).drop k) =
        eqEval (selectorPoint (idx >>> k) (x.length - k)) (x.drop k) := by
      by_cases hn : x.length ≤ nu
      · rw [List.drop_of_length_le hn, eqEval_nil_right, one_mul, List.take_of_length_le hn,
          show nu - k = (x.length - k) + (nu - x.length) by omega, selectorPoint_add, ← List.append_nil (x.drop k),
          eqEval_append (by rw [length_selectorPointF, List.length_drop]), eqEval_nil_right, mul_one,
          List.append_nil]
      · have hd : x.drop k = (x.take nu).drop k ++ x.drop nu := by
          conv_lhs => rw [← List.take_append_drop nu x]
          rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]
        have h0 : idx >>> k >>> (nu - k) = 0 := by
          rw [← Nat.shiftRight_add, show k + (nu - k) = nu by omega, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hi]
        rw [hd, show x.length - k = (nu - k) + (x.length - nu) by omega, selectorPoint_add, h0,
          eqEval_append (by rw [length_selectorPointF, List.length_drop, List.length_take]; omega), mul_comm]
    rw [← hE]
    ring

theorem sum_map_filter_zero {α : Type} (p : α → Bool) (f : α → FE) :
    ∀ l : List α, (∀ a ∈ l, p a = false → f a = 0) → ((l.filter p).map f).sum = (l.map f).sum
  | [], _ => rfl
  | a :: l, h => by
    have ih := sum_map_filter_zero p f l fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
    · rw [List.filter_cons_of_neg ha, List.map_cons, List.sum_cons, h a List.mem_cons_self (by simpa using ha),
        zero_add, ih]

/-- **The same in the opening's stack form, both shapes** (`toStk`; the small shape at `ν = 23` with `blk` inside
the stack): the regions `blk` does not meet weigh `0` (`Shape.eqAbove_relocF_eq_zero`). -/
theorem toStk_rowSel (s : Bool) (nu : Nat) (blk : Placement) (z : List FE2) (eqA : Array FE) (v t : FE)
    (hz : z.length = blk.variableCount) (hk : blk.variableCount ≤ nu) (hi : blk.index < 2 ^ nu)
    (hs : s = true → nu = 23 ∧ inStackB blk = true) :
    toStk s nu (⟨⟨nu, 0⟩, tensorDotT ((z ++ E2V.selPtF (blk.index >>> blk.variableCount)
        (nu - blk.variableCount)).map tColsW) eqA, v⟩, t) =
      toStk s nu (⟨blk, tensorDotT (z.map tColsW) eqA, v⟩, t) := by
  cases s
  · simp only [toStk, Bool.false_eq_true, ite_false]
    exact onStack_rowSel nu blk z eqA v hz hk hi
  · obtain ⟨rfl, hst⟩ := hs rfl
    simp only [toStk, ite_true]
    unfold TypedV.onStackZBN
    rw [onStack_rowSel 23 blk z eqA v hz hk hi]
    refine Prod.ext (funext fun x => ?_) rfl
    simp only
    congr 1
    rw [sum_map_filter_zero _ _ _ fun r hr hm => ?_, sum_map_filter_zero _ _ _ fun r hr hm => ?_]
    · have hr' : r ∈ Shape.regions := TypedV.regionsN_23 ▸ hr
      simp only [BlockClaim.onStack, TypedV.relocN_23,
        Shape.eqAbove_relocF_eq_zero blk (inStack_of_B hst) x hr' hm, zero_mul, mul_zero]
    · have hr' : r ∈ Shape.regions := TypedV.regionsN_23 ▸ hr
      obtain ⟨_, _, hoe⟩ := Shape.regions_facts r hr'
      have : Shape.meets ⟨23, 0⟩ r = true := by
        simp only [Shape.meets, decide_eq_true_eq]
        have := Nat.two_pow_pos r.1
        constructor <;> (clear * - hoe this; omega)
      rw [this] at hm
      exact Bool.noConfusion hm

/-- **How the front makes a row claim on a block** of the stack `⟨ν, 0⟩` whose row point ends in the block's
selector: on the data (`RowZ`), the row claim on the block with the first `blk.variableCount` coordinates
(`rowStackW` then meets only the block's regions); on the closures, the claim on the whole stack. -/
class RowK (ρ : Type) where
  /-- The item of the row `ρ` on `blk` (stack `⟨ν, 0⟩`) with tail `t`. -/
  rowItemK : Nat → Placement → ρ → FE → FItem

/-- A row's data on its first `k` coordinates. -/
def _root_.Lvm.RowR.takeC (k : Nat) (R : RowR) : RowR := ⟨R.tgt, R.cols.take k, R.eqA, R.eqR⟩

theorem _root_.Lvm.RowR.takeC_ofZ (k : Nat) {R : RowR} (h : R.OfZ) : (R.takeC k).OfZ := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z.take k, by rw [RowR.takeC, hz, List.map_take]⟩

instance : RowK RowZ := ⟨fun _ blk R t => .rowS blk (R.1.takeC blk.variableCount) (RowR.takeC_ofZ _ R.2) t⟩

instance : RowK ((FE × (List FE → FE)) × List FE) := ⟨fun nu _ row t => rowAccC.rowItem ⟨nu, 0⟩ row t⟩

/-- **V_S's block row is its stack row** (both shapes): for a row switch run at `z ++ sel(blk)` (`|z| = k`), the
item `RowK.rowItemK ν blk R t` stands for the block claim, whose stack form is the stack claim's
(`⟨⟨ν, 0⟩, R.w, R.tgt⟩`, tail `t`). -/
theorem rowItemK_toStk (s : Bool) (nu : Nat) (blk : Placement) (R : RowZ) (z : List FE2) (t : FE)
    (hR : R.1.cols = (z ++ E2V.selPtF (blk.index >>> blk.variableCount) (nu - blk.variableCount)).map tColsW)
    (hz : z.length = blk.variableCount) (hk : blk.variableCount ≤ nu) (hi : blk.index < 2 ^ nu)
    (hs : s = true → nu = 23 ∧ inStackB blk = true) :
    (RowK.rowItemK nu blk R t).flat.map (fun e => toStk s nu e.2) =
      [toStk s nu (⟨⟨nu, 0⟩, R.1.w, R.1.tgt⟩, t)] := by
  have hw : (R.1.takeC blk.variableCount).w = tensorDotT (z.map tColsW) R.1.eqA := by
    unfold RowR.w RowR.takeC
    rw [hR, List.map_append, List.take_append_of_le_length (by rw [List.length_map]; omega),
      List.take_of_length_le (by rw [List.length_map]; omega)]
  have hW : R.1.w = tensorDotT ((z ++ E2V.selPtF (blk.index >>> blk.variableCount)
      (nu - blk.variableCount)).map tColsW) R.1.eqA := by
    unfold RowR.w
    rw [hR]
  simp only [RowK.rowItemK, FItem.flat, List.map_cons, List.map_nil]
  rw [hw, hW, toStk_rowSel s nu blk z R.1.eqA R.1.tgt t hz hk hi hs]
  rfl

/-- **The opening sees its claims only through their stack forms**: two claim lists with the same commitments and
the same `toStk` images give the same `dOpenF`. -/
theorem dOpenF_congr (p : Params) (s : Bool) (pin : BlockClaim) {c₁ c₂ : List (Com × BlockClaim × FE)}
    (h : c₁.map (fun e => (e.1, toStk s p.nuMain e.2)) = c₂.map (fun e => (e.1, toStk s p.nuMain e.2))) :
    dOpenF p s pin c₁ = dOpenF p s pin c₂ := by
  have hm : c₁.map (·.1) = c₂.map (·.1) := by
    have := congrArg (List.map Prod.fst) h
    simpa only [List.map_map, Function.comp_def] using this
  have hall : ∀ c : List (Com × BlockClaim × FE), c.all (·.1 == .main) = (c.map (·.1)).all (· == .main) :=
    fun c => by rw [List.all_map]; rfl
  have hst : ∀ c : List (Com × BlockClaim × FE),
      (if s then ((c.filter (·.1 == .main)).map (·.2)).map fun e => TypedV.onStackZBN p.nuMain e.1 e.2
        else ((c.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      ((c.map fun e => (e.1, toStk s p.nuMain e.2)).filter (·.1 == .main)).map (·.2) := fun c => by
    rw [List.filter_map, List.map_map, List.map_map]
    cases s <;> simp only [toStk, Function.comp_def, Bool.false_eq_true, ↓reduceIte, List.map_map]
  unfold dOpenF
  dsimp only
  rw [hall, hall, hm, hst, hst, h]

end RowBlock

/-! ## The claims -/

/-- **The front's claims at S2GU as items**: `D`'s four word claims at `r_{<w}` (tails `tailDE2`, as S2GT), the
`Y` block's 25 word claims at `r_{<hs}` (lane `l` at `Y + l·2^hs`), `D`'s row claim on `C_main` (tail `rowTailE2`,
as S2GT), the `Y` and stream blocks' row claims on their blocks, the boundary words `h` (as S2GT). -/
def frontItemsU {ρ : Type} [RowK ρ] (A : RowAcc ρ) (p : Params) (pub : Pub) (tp : TapeU ρ) : List FItem :=
  let L := layout0 p
  let blkD := dBlock p
  let r := tp.r
  let ab := tp.ab
  let wo := tp.wo
  let rowPt := wo.sc.1 ++ wo.d.1.1 ++ selPtF (dSel p) (dSelBits p)
  ((List.range dLanes).map fun l =>
    FItem.split p.nuMain [(1, blkD, r ++ selPtF l 2)] (ab.getD l 0) ((tailDE2 r l).getD 0 0)
      ((tailDE2 r l).getD 1 0)) ++
  ((List.range 25).map fun l =>
    FItem.split p.nuMain [(1, ⟨p.ksLog, L.ks + l * 2 ^ p.ksLog⟩, r.take p.ksLog)] (ab.getD (25 + l) 0) 0 0) ++
  [A.rowItem ⟨p.nuMain, 0⟩ wo.d.2.2 (rowTailE2 (A.eqR wo.d.2.2) rowPt),
   RowK.rowItemK p.nuMain ⟨p.ksLog + slotBitsU, L.ks⟩ wo.y.2.2 0, RowK.rowItemK p.nuMain ⟨p.nuRec, L.s⟩ wo.m.2.2 0] ++
  (pub.h.zipIdx.map fun (w, l) =>
    .one (.main, BlockClaim.point blkD (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w), 0))

/-! ## The decision program -/

/-- **The decision program at S2GU** (S2GT's `decideProgFFGM` with the merged front): the public values, the cap,
the pin, the typed phases at `E2` (`pT`: the mini-bus's record, as S2GT `P20`; the relayout's split claim on
`layout0 p`'s stream block), the mini-bus's claims per table, the merged tape and wire, the opening at `p`. -/
def decideProgUG (p pT : Params) (N : TNatT) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubG vk c sig
  let m := m3G N p
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let pin ← pinD p.nuMain
  let (acc, ti, evals) ← dTypedTG pT N m pub (typedItemsND N p)
  let tp ← tapeUDG rowSwitchDR p pub.s pub.n
  dOpenFFI p (TypedV.smallT p pub) pin (ti ++ tabItemsR (M3.sumcheckTabs N.mbT) evals) (frontItemsU rowAccR p pub tp)
  pure acc

/-- **V_S's decision at S2GU** at `p` on the stream `sig` (`decideFGX`'s form): every check held, `Σ` read to its
end, `Φ_Q` at `E2` at the folded accumulator. -/
def decideFUG (p pT : Params) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := DM.runOnH (headerBytesP p) (decideProgUG p pT N vk c) sig
  (s.ok && s.ent == sig.size && s.msg == 0) && N.phiT (a.pt.map Lvm.e2OfFE) == Lvm.e2OfFE a.y

end Lvm.E2U
