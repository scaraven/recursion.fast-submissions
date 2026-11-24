-- New for lvm6 (WP CB-L). The layer gadget's parts as season-1 `BM` programs on `C2` cells
-- (`LvmE2QWKit`), with their values in `E2` (`Hs` form): the projection, the iota sums, the
-- instance weights, Horner, the lane forms, the lane weights, the rotated-sum tables and the two
-- final-check weights.
import Lvm6QKLayAlg

/-!
# The layer gadget's parts (CB-L)

Every table is read with the zero cell `z` as its default (`getD k z`), so a read past the end
is `0` (`ev2_getDz`). Values are stated in `E2` (`ev2`): `hs2_*` restate the kit's `Hs` lemmas.

* `projG`: `Σ_c (Σ_{i: mask_i ∋ c} μ_i)·product_c` (`projectedF`); `iotaG`: `ι(rc, W)` from the
  seven weights `W(2^i − 1)`; `instG`: `instWeightsF s`; `hornerG`: `polyEvalF`.
* `laneFormG`: `laneFormF`; `laneWG`: the next claim's lane weights (`laneWB`); `firstIotaG`,
  `ltIotaG`: the seven weights `W(2^i − 1)` of the two kinds of claim.
* `firstDotG`, `ltDotG`: the final check's weight `dot(eq(lp)[:1600], W)` (`dot_prod`,
  `dot_lt`); `ltDotG` builds the rotated sum through `shiftLHG`'s tables (`lowG`, `highG`,
  `shiftG`).
* `failG`: an assertion that fails under the gate (an ill-shaped claim).
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters (E2)
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open Lvm.Q1 (eqAtG prodWG rotSumG laneFormF flipFormG rcBitG iotaFG lowTabG highTabG shiftLHG iotaPos
  rho lt_flipG shift_LHG iotaF_reduceG)

variable {c : Ctx} {M : Mem}

/-! ## Values in `E2` -/

theorem ev2_zero {z : C2} (hz : z.val M = 0) : ev2 M z = 0 := by simp [ev2, hz]

theorem ev2_one' {one : C2} (h : one.val M = 1) : ev2 M one = 1 := by simp [ev2, h]

/-- A table read with the zero cell as default. -/
theorem ev2_getDz {l : List C2} {L : List E2} (h : l.map (ev2 M) = L) {z : C2} (hz : ev2 M z = 0)
    (k : ℕ) : ev2 M (l.getD k z) = L.getD k 0 := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> simp [hz]

theorem getD_map_range (f : ℕ → E2) {n k : ℕ} (hk : k < n) : ((List.range n).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem hs2_mul (a b d : C2) : Hs c M (g2Mul a b d) (fun r ↦ ev2 M r = ev2 M a * ev2 M b + ev2 M d) :=
  hs_mono (hs_g2Mul a b d) fun _ hr ↦ ev2_mul hr

theorem hs2_add (a b : C2) : Hs c M (g2Add a b) (fun r ↦ ev2 M r = ev2 M a + ev2 M b) :=
  hs_mono (hs_g2Add a b) fun _ hr ↦ ev2_add hr

theorem hs2_one (a : C2) : Hs c M (g2One a) (fun r ↦ ev2 M r = 1 + ev2 M a) :=
  hs_mono (hs_g2One a) fun _ hr ↦ by simp [ev2, hr]

theorem hs2_const (k : E2) (a : C2) :
    Hs c M (g2Const (FE2.ringEquivE2.symm k) a) (fun r ↦ ev2 M r = k) :=
  hs_mono (hs_g2Const _ a) fun _ hr ↦ by
    rw [ev2, hr, ← FE2.ringEquivE2_apply, RingEquiv.apply_symm_apply]

theorem hs2_sum : ∀ (s : C2) (cs : List C2),
    Hs c M (g2Sum s cs) (fun r ↦ ev2 M r = ev2 M s + (cs.map (ev2 M)).sum)
  | s, [] => hs_pure (by simp)
  | s, x :: cs => hs_bind (hs2_add s x) fun s' hs' ↦ hs_mono (hs2_sum s' cs) fun r hr ↦ by
    rw [hr, hs', List.map_cons, List.sum_cons, add_assoc]

theorem hs2_dot : ∀ (acc : C2) (l : List (C2 × C2)),
    Hs c M (g2Dot acc l) (fun r ↦ ev2 M r = ev2 M acc + (l.map fun e ↦ ev2 M e.1 * ev2 M e.2).sum)
  | acc, [] => hs_pure (by simp)
  | acc, (a, b) :: l => hs_bind (hs2_mul a b acc) fun s hs ↦ hs_mono (hs2_dot s l) fun r hr ↦ by
    rw [hr, hs, List.map_cons, List.sum_cons]; ring

theorem hs2_mapB {α : Type} (f : α → BM C2) (g : α → E2) : ∀ l : List α,
    (∀ a ∈ l, Hs c M (f a) (fun r ↦ ev2 M r = g a)) →
      Hs c M (mapB f l) (fun rs ↦ rs.map (ev2 M) = l.map g)
  | [], _ => hs_pure rfl
  | a :: l, hf => hs_bind (hf a (by simp)) fun r hr ↦
    hs_bind (hs2_mapB f g l fun b hb ↦ hf b (List.mem_cons_of_mem _ hb)) fun rs hrs ↦
      hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

/-- **The `eq` table** of a point, in `E2`. -/
theorem hs_tab {z one : C2} (hz : z.val M = 0) (hone : one.val M = 1) (pt : List C2) :
    Hs c M (g2EqTab z [one] pt) (fun t ↦ t.map (ev2 M) = eqKernelF (pt.map (ev2 M))) :=
  hs_mono (hs_g2EqTab hz [one] pt) fun _ ht ↦ eqTab_ev2 hone pt ht

/-! ## The projection -/

/-- **The projection** `Σ_c (Σ_{i: mask_i ∋ c} μ_i)·product_c`. -/
def projG (z : C2) (mu prodC : List C2) : BM C2 :=
  mapB (fun c' ↦ g2Sum z ((mu.zip Lvm.rmfeProject).filterMap fun p ↦
    if p.2.testBit c' then some p.1 else none)) (List.range 47) >>= fun P ↦
  g2Dot z ((List.range 47).map fun c' ↦ (P.getD c' z, prodC.getD c' z))

theorem filt_ev2 (c' : ℕ) : ∀ (mu : List C2) (masks : List ℕ),
    ((mu.zip masks).filterMap fun p ↦ if p.2.testBit c' then some p.1 else none).map (ev2 M) =
      ((mu.map (ev2 M)).zip masks).filterMap fun p ↦ if p.2.testBit c' then some p.1 else none
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: mu, k :: ks => by
    by_cases h : k.testBit c' <;> simp [List.filterMap_cons, h, filt_ev2 c' mu ks]

theorem projectedF_eq (cl : KClaim E2) (product : List E2) :
    projectedF cl product = sumF ((List.range 47).map fun c' ↦
      sumF ((cl.mu.zip Lvm.rmfeProject).filterMap fun p ↦
        if p.2.testBit c' then some p.1 else none) * product.getD c' 0) := rfl

theorem hs_projG {z : C2} (hz : z.val M = 0) (mu prodC : List C2) (cl : KClaim E2)
    (hmu : mu.map (ev2 M) = cl.mu) (product : List E2) (hp : prodC.map (ev2 M) = product) :
    Hs c M (projG z mu prodC) (fun r ↦ ev2 M r = projectedF cl product) := by
  have hz' := ev2_zero hz
  refine hs_bind (hs2_mapB _ (fun c' ↦ sumF ((cl.mu.zip Lvm.rmfeProject).filterMap
    fun p ↦ if p.2.testBit c' then some p.1 else none)) _ fun c' _ ↦ hs_mono (hs2_sum z _) fun r hr ↦ by
      rw [hr, hz', zero_add, filt_ev2, hmu, sumF_eq_sum]) fun P hP ↦ hs_mono (hs2_dot z _) fun r hr ↦ ?_
  rw [hr, hz', zero_add, List.map_map, projectedF_eq, sumF_eq_sum]
  refine congrArg List.sum (List.map_congr_left fun c' hc ↦ ?_)
  simp only [Function.comp_apply]
  rw [ev2_getDz hP hz', ev2_getDz hp hz', getD_map_range _ (List.mem_range.mp hc)]

/-! ## The iota sums -/

/-- `ι(rc, W) = Σ_i rcBit_i·W(2^i − 1)` from the seven weights `fs`. -/
def iotaG (z : C2) (step seg : ℕ) (fs : List C2) : BM C2 :=
  mapB (fun i ↦ g2Const (FE2.ringEquivE2.symm (rcBitG (rcAt step seg) i)) z) (List.range 7) >>= fun rcs ↦
  g2Dot z ((List.range 7).map fun i ↦ (rcs.getD i z, fs.getD i z))

theorem hs_iotaG {z : C2} (hz : z.val M = 0) (step seg : ℕ) (hs : step < 12) (hg : seg < 2)
    (fs : List C2) (W : List E2) (hfs : fs.map (ev2 M) = (List.range 7).map fun i ↦ W.getD (iotaPos i) 0) :
    Hs c M (iotaG z step seg fs) (fun r ↦ ev2 M r = iotaFG (rcAt step seg) W) := by
  have hz' := ev2_zero hz
  refine hs_bind (hs2_mapB _ (fun i ↦ (rcBitG (rcAt step seg) i : E2)) _ fun i _ ↦ hs2_const _ z)
    fun rcs hrcs ↦ hs_mono (hs2_dot z _) fun r hr ↦ ?_
  rw [hr, hz', zero_add, iotaF_reduceG (rcAt_mem hs hg), sumF_eq_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
  simp only [Function.comp_apply]
  rw [ev2_getDz hrcs hz', ev2_getDz hfs hz', getD_map_range _ (List.mem_range.mp hi),
    getD_map_range _ (List.mem_range.mp hi)]

/-! ## Instance weights and Horner -/

/-- `acc, acc·s, …` (`n` terms). -/
def powG (z s : C2) : C2 → ℕ → BM (List C2)
  | _, 0 => pure []
  | acc, n + 1 => g2Mul acc s z >>= fun nx ↦ powG z s nx n >>= fun rest ↦ pure (acc :: rest)

theorem hs_powG {z : C2} (hz : z.val M = 0) (s : C2) : ∀ (acc : C2) (n : ℕ),
    Hs c M (powG z s acc n) (fun rs ↦ rs.map (ev2 M) = powersFromF (ev2 M acc) (ev2 M s) n)
  | _, 0 => hs_pure rfl
  | acc, n + 1 => hs_bind (hs2_mul acc s z) fun nx hnx ↦ hs_bind (hs_powG hz s nx n) fun rs hrs ↦
      hs_pure (by simp only [List.map_cons, hrs, hnx, ev2_zero hz, add_zero, powersFromF])

/-- **The instance weights** `μ_e = Σ_{b ∈ e} s^b` (`instWeightsF`). -/
def instG (z one s : C2) : BM (List C2) :=
  powG z s one 24 >>= fun pw ↦
  mapB (fun e ↦ g2Sum z ((List.range 24).filterMap fun b ↦ if e.testBit b then some (pw.getD b z) else none))
    Lvm.rmfeEmbed

theorem filtB_ev2 (P : ℕ → Bool) (g : ℕ → C2) (l : List ℕ) :
    (l.filterMap fun b ↦ if P b then some (g b) else none).map (ev2 M) =
      l.filterMap fun b ↦ if P b then some (ev2 M (g b)) else none := by
  rw [List.map_filterMap]
  congr 1
  funext b
  cases P b <;> rfl

theorem hs_instG {z one : C2} (hz : z.val M = 0) (hone : one.val M = 1) (s : C2) :
    Hs c M (instG z one s) (fun mu ↦ mu.map (ev2 M) = instWeightsF (ev2 M s)) := by
  have hz' := ev2_zero hz
  refine hs_bind (hs_powG hz s one 24) fun pw hpw ↦ ?_
  rw [ev2_one' hone] at hpw
  refine hs_mono (hs2_mapB _ (fun e ↦ sumF ((List.range 24).filterMap fun b ↦
    if e.testBit b then some ((powersF (ev2 M s) 24).getD b 0) else none)) _ fun e _ ↦
      hs_mono (hs2_sum z _) fun r hr ↦ ?_) fun mu hmu ↦ ?_
  · rw [hr, hz', zero_add, filtB_ev2, sumF_eq_sum]
    simp only [ev2_getDz hpw hz', powersF]
  · exact hmu.trans rfl

/-- Horner: `polyEvalF cs x`. -/
def hornerG (z x : C2) : List C2 → BM C2
  | [] => pure z
  | a :: cs => hornerG z x cs >>= fun acc ↦ g2Mul acc x a

theorem hs_hornerG {z : C2} (hz : z.val M = 0) (x : C2) : ∀ cs : List C2,
    Hs c M (hornerG z x cs) (fun r ↦ ev2 M r = polyEvalF (cs.map (ev2 M)) (ev2 M x))
  | [] => hs_pure (by simp [polyEvalF, ev2_zero hz])
  | a :: cs => hs_bind (hs_hornerG hz x cs) fun acc hacc ↦ hs_mono (hs2_mul acc x a) fun r hr ↦ by
      rw [hr, hacc]
      simp [polyEvalF]

/-! ## Lane forms and lane weights -/

/-- **Lane `ℓ`'s form** from the lane weights `B` and a rotated-sum table `R` (`laneFormF`). -/
def laneFormG (z : C2) (B : List C2) (R : ℕ → C2) (l : ℕ) : BM C2 :=
  g2Mul (B.getD (Lvm.keccakPi l) z) (R (rho l)) z >>= fun t1 ↦
  g2Dot t1 ((List.range 5).map fun y ↦ (B.getD (Lvm.keccakPi ((l % 5 + 1) % 5 + 5 * y)) z,
    R (rho ((l % 5 + 1) % 5 + 5 * y)))) >>= fun t2 ↦
  g2Dot t2 ((List.range 5).map fun y ↦ (B.getD (Lvm.keccakPi ((l % 5 + 4) % 5 + 5 * y)) z,
    R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

theorem hs_laneFormG {z : C2} (hz : z.val M = 0) (B : List C2) (Bv : List E2)
    (hB : B.map (ev2 M) = Bv) (R : ℕ → C2) (l : ℕ) :
    Hs c M (laneFormG z B R l) (fun r ↦ ev2 M r = laneFormF Bv (fun s ↦ ev2 M (R s)) l) := by
  have hz' := ev2_zero hz
  refine hs_bind (hs2_mul _ _ _) fun t1 ht1 ↦ hs_bind (hs2_dot _ _) fun t2 ht2 ↦
    hs_mono (hs2_dot _ _) fun r hr ↦ ?_
  rw [hr, ht2, ht1, hz', add_zero]
  simp only [laneFormF, sumF_eq_sum, List.map_map, Function.comp_def, ev2_getDz hB hz']

/-- **The next claim's lane weights** `eq_L(ℓ) + β·(eq_L(x+4) + β·eq_L(x+3))` from `eq_L`'s table. -/
def laneWG (z β : C2) (eL : List C2) : BM (List C2) :=
  mapB (fun l ↦ g2Mul β (eL.getD (keccakAlong (64 * l) 3 / 64) z) (eL.getD (keccakAlong (64 * l) 4 / 64) z) >>=
    fun u ↦ g2Mul β u (eL.getD l z)) (List.range 25)

theorem hs_laneWG {z : C2} (hz : z.val M = 0) (β : C2) (pos eL : List C2)
    (heL : eL.map (ev2 M) = eqKernelF ((pos.drop 6).map (ev2 M))) :
    Hs c M (laneWG z β eL) (fun B ↦ B.map (ev2 M) = laneWB (pos.map (ev2 M)) (ev2 M β)) := by
  have hz' := ev2_zero hz
  unfold laneWB
  refine hs2_mapB _ _ _ fun l _ ↦ hs_bind (hs2_mul _ _ _) fun u hu ↦ hs_mono (hs2_mul _ _ _) fun r hr ↦ ?_
  rw [hr, hu, ev2_getDz heL hz', ev2_getDz heL hz', ev2_getDz heL hz', List.map_drop]
  ring

/-! ## The seven iota weights -/

/-- The first claim's weights at `2^i − 1`: `x^(2^i−1)·B(0)`. -/
def firstIotaG (z : C2) (B : List C2) : BM (List C2) :=
  mapB (fun i ↦ g2Const (FE2.ringEquivE2.symm (nF (2 ^ iotaPos i))) z >>= fun k ↦ g2Mul k (B.getD 0 z) z)
    (List.range 7)

theorem hs_firstIotaG {z : C2} (hz : z.val M = 0) (B : List C2) (Bv : List E2) (hB : B.map (ev2 M) = Bv) :
    Hs c M (firstIotaG z B) (fun fs ↦ fs.map (ev2 M) = (List.range 7).map fun i ↦
      (prodWG (fun zz ↦ (nF (2 ^ zz) : E2)) Bv).getD (iotaPos i) 0) :=
  hs2_mapB _ _ _ fun i hi ↦ hs_bind (hs2_const _ z) fun k hk ↦ hs_mono (hs2_mul _ _ _) fun r hr ↦ by
    rw [hr, hk, ev2_getDz hB (ev2_zero hz), ev2_zero hz, add_zero, prodWG_iota _ _ (List.mem_range.mp hi)]

/-- A transposed product claim's weights at `2^i − 1`: the flip forms. -/
def ltIotaG (z : C2) (B A : List C2) : BM (List C2) :=
  mapB (fun i ↦ laneFormG z B (fun s ↦ A.getD ((iotaPos i + s) % 64) z) 0) (List.range 7)

theorem hs_ltIotaG {z : C2} (hz : z.val M = 0) (B : List C2) (Bv : List E2) (hB : B.map (ev2 M) = Bv)
    (A : List C2) (a : List E2) (hA : A.map (ev2 M) = eqKernelF a) :
    Hs c M (ltIotaG z B A) (fun fs ↦ fs.map (ev2 M) = (List.range 7).map fun i ↦
      (linearTransposeF (prodWG (eqAtG a) Bv)).getD (iotaPos i) 0) :=
  hs2_mapB _ _ _ fun i hi ↦ hs_mono (hs_laneFormG hz B Bv hB _ 0) fun r hr ↦ by
    rw [hr, lt_flipG _ _ (List.mem_range.mp hi), flipFormG]
    simp only [ev2_getDz hA (ev2_zero hz), eqAtG]

/-! ## The final check's weights -/

/-- The first claim's: `(Σ_ℓ eq_L(ℓ)·B(ℓ))·(Σ_z eq_Z(z)·x^z)`. -/
def firstDotG (z one : C2) (B lp : List C2) : BM C2 :=
  g2EqTab z [one] (lp.drop 6) >>= fun f ↦
  g2Dot z ((List.range 25).map fun l ↦ (f.getD l z, B.getD l z)) >>= fun s1 ↦
  g2EqTab z [one] (lp.take 6) >>= fun e ↦
  mapB (fun zz ↦ g2Const (FE2.ringEquivE2.symm (nF (2 ^ zz))) z) (List.range 64) >>= fun C ↦
  g2Dot z ((List.range 64).map fun zz ↦ (e.getD zz z, C.getD zz z)) >>= fun s2 ↦
  g2Mul s1 s2 z

theorem hs_firstDotG {z one : C2} (hz : z.val M = 0) (hone : one.val M = 1) (B : List C2)
    (Bv : List E2) (hB : B.map (ev2 M) = Bv) (lp : List C2) (hlp : lp.length = 11) :
    Hs c M (firstDotG z one B lp) (fun r ↦ ev2 M r =
      dotF ((eqKernelF (lp.map (ev2 M))).take LeanVM.Protocol.Verifier.keccakBits)
        (prodWG (fun zz ↦ (nF (2 ^ zz) : E2)) Bv)) := by
  have hz' := ev2_zero hz
  refine hs_bind (hs_tab hz hone _) fun f hf ↦ hs_bind (hs2_dot _ _) fun s1 hs1 ↦
    hs_bind (hs_tab hz hone _) fun e he ↦
    hs_bind (hs2_mapB _ (fun zz ↦ (nF (2 ^ zz) : E2)) _ fun zz _ ↦ hs2_const _ z) fun C hC ↦
    hs_bind (hs2_dot _ _) fun s2 hs2 ↦ hs_mono (hs2_mul _ _ _) fun r hr ↦ ?_
  rw [hr, hs1, hs2, hz', add_zero, zero_add, zero_add, dot_prod (lp := lp.map (ev2 M)) (by simp [hlp]), sumF_eq_sum,
    sumF_eq_sum, List.map_map, List.map_map]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg List.sum (List.map_congr_left fun l _ ↦ ?_)
    simp only [Function.comp_apply]
    rw [ev2_getDz hf hz', ev2_getDz hB hz', List.map_drop]
  · refine congrArg List.sum (List.map_congr_left fun zz hzz ↦ ?_)
    simp only [Function.comp_apply]
    rw [ev2_getDz he hz', ev2_getDz hC hz', getD_map_range _ (List.mem_range.mp hzz), List.map_take]

/-- `L_c(r_l)` (`lowTabG`): the terms off the carry `c` read as `0`. -/
def lowG (z : C2) (ta tb : List C2) (cc rl : ℕ) : BM C2 :=
  g2Dot z ((List.range 8).map fun zz ↦
    (tb.getD zz z, if (zz + rl) / 8 = cc then ta.getD ((zz + rl) % 8) z else z))

/-- `H(k)` (`highTabG`). -/
def highG (z : C2) (ta tb : List C2) (k : ℕ) : BM C2 :=
  g2Dot z ((List.range 8).map fun zz ↦ (tb.getD zz z, ta.getD ((zz + k) % 8) z))

/-- `shift(r) = L₀·H + L₁·H'` (`shiftLHG`). -/
def shiftG (z : C2) (L0 L1 H : List C2) (r : ℕ) : BM C2 :=
  g2Mul (L1.getD (r % 8) z) (H.getD ((r / 8 + 1) % 8) z) z >>= fun t ↦
    g2Mul (L0.getD (r % 8) z) (H.getD (r / 8) z) t

/-- A transposed product claim's: `Σ_ℓ eq_L(ℓ)·laneForm(B, rotSum(eq(lp₀…₅), eq(a)))(ℓ)`. -/
def ltDotG (z one : C2) (B a lp : List C2) : BM C2 :=
  g2EqTab z [one] ((lp.take 6).take 3) >>= fun tbLo ↦ g2EqTab z [one] ((lp.take 6).drop 3) >>= fun tbHi ↦
  g2EqTab z [one] (a.take 3) >>= fun taLo ↦ g2EqTab z [one] (a.drop 3) >>= fun taHi ↦
  mapB (lowG z taLo tbLo 0) (List.range 8) >>= fun L0 ↦ mapB (lowG z taLo tbLo 1) (List.range 8) >>= fun L1 ↦
  mapB (highG z taHi tbHi) (List.range 8) >>= fun H ↦
  mapB (shiftG z L0 L1 H) (List.range 64) >>= fun sh ↦
  g2EqTab z [one] (lp.drop 6) >>= fun f ↦
  mapB (laneFormG z B fun s ↦ sh.getD (s % 64) z) (List.range 25) >>= fun lf ↦
  g2Dot z ((List.range 25).map fun l ↦ (f.getD l z, lf.getD l z))

theorem hs_ltDotG {z one : C2} (hz : z.val M = 0) (hone : one.val M = 1) (B : List C2) (Bv : List E2)
    (hB : B.map (ev2 M) = Bv) (a : List C2) (ha : a.length = 6) (lp : List C2) (hlp : lp.length = 11) :
    Hs c M (ltDotG z one B a lp) (fun r ↦ ev2 M r =
      dotF ((eqKernelF (lp.map (ev2 M))).take LeanVM.Protocol.Verifier.keccakBits)
        (linearTransposeF (prodWG (eqAtG (a.map (ev2 M))) Bv))) := by
  have hz' := ev2_zero hz
  have hav : (a.map (ev2 M)).length = 6 := by simp [ha]
  have hbv : ((lp.map (ev2 M)).take 6).length = 6 := by simp [hlp]
  refine hs_bind (hs_tab hz hone _) fun tbLo htbLo ↦ hs_bind (hs_tab hz hone _) fun tbHi htbHi ↦
    hs_bind (hs_tab hz hone _) fun taLo htaLo ↦ hs_bind (hs_tab hz hone _) fun taHi htaHi ↦ ?_
  rw [List.map_take, List.map_take] at htbLo
  rw [List.map_drop, List.map_take] at htbHi
  rw [List.map_take] at htaLo
  rw [List.map_drop] at htaHi
  have hlow : ∀ cc, ∀ rl ∈ List.range 8, Hs c M (lowG z taLo tbLo cc rl)
      (fun r ↦ ev2 M r = lowTabG (a.map (ev2 M)) ((lp.map (ev2 M)).take 6) cc rl) := fun cc rl _ ↦
    hs_mono (hs2_dot z _) fun r hr ↦ by
      rw [hr, hz', zero_add, lowTabG, sumF_eq_sum, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun zz _ ↦ ?_)
      simp only [Function.comp_apply, apply_ite (ev2 M), ev2_getDz htbLo hz', ev2_getDz htaLo hz', hz',
        mul_ite, mul_zero, eqAtG]
  refine hs_bind (hs2_mapB _ _ _ (hlow 0)) fun L0 hL0 ↦ hs_bind (hs2_mapB _ _ _ (hlow 1)) fun L1 hL1 ↦
    hs_bind (hs2_mapB _ (fun k ↦ highTabG (a.map (ev2 M)) ((lp.map (ev2 M)).take 6) k) _ fun k _ ↦
      hs_mono (hs2_dot z _) fun r hr ↦ by
        rw [hr, hz', zero_add, highTabG, sumF_eq_sum, List.map_map]
        refine congrArg List.sum (List.map_congr_left fun zz _ ↦ ?_)
        simp only [Function.comp_apply, ev2_getDz htbHi hz', ev2_getDz htaHi hz', eqAtG]) fun H hH ↦ ?_
  have hL0' : ∀ rl < 8, ev2 M (L0.getD rl z) = lowTabG (a.map (ev2 M)) ((lp.map (ev2 M)).take 6) 0 rl :=
    fun rl h ↦ by rw [ev2_getDz hL0 hz', getD_map_range _ h]
  have hL1' : ∀ rl < 8, ev2 M (L1.getD rl z) = lowTabG (a.map (ev2 M)) ((lp.map (ev2 M)).take 6) 1 rl :=
    fun rl h ↦ by rw [ev2_getDz hL1 hz', getD_map_range _ h]
  have hH' : ∀ k < 8, ev2 M (H.getD k z) = highTabG (a.map (ev2 M)) ((lp.map (ev2 M)).take 6) k :=
    fun k h ↦ by rw [ev2_getDz hH hz', getD_map_range _ h]
  refine hs_bind (hs2_mapB _ (fun r ↦ shiftLHG (a.map (ev2 M)) ((lp.map (ev2 M)).take 6) r) _
    fun r hr ↦ hs_bind (hs2_mul _ _ _) fun t ht ↦ hs_mono (hs2_mul _ _ _) fun u hu ↦ by
      have hr64 : r < 64 := List.mem_range.mp hr
      rw [hu, ht, hz', add_zero, hL0' _ (Nat.mod_lt _ (by norm_num)), hL1' _ (Nat.mod_lt _ (by norm_num)),
        hH' (r / 8) (by omega), hH' _ (Nat.mod_lt _ (by norm_num)), shiftLHG]) fun sh hsh ↦ ?_
  have hsh' : ∀ s, ev2 M (sh.getD (s % 64) z) =
      rotSumG (eqAtG ((lp.map (ev2 M)).take 6)) (eqAtG (a.map (ev2 M))) s := fun s ↦ by
    rw [ev2_getDz hsh hz', getD_map_range _ (Nat.mod_lt s (by norm_num : (64 : ℕ) > 0)),
      ← shift_LHG hav hbv (Nat.mod_lt _ (by norm_num)), rotSum_mod]
  refine hs_bind (hs_tab hz hone _) fun f hf ↦ hs_bind (hs2_mapB _ (fun l ↦ laneFormF Bv
    (rotSumG (eqAtG ((lp.map (ev2 M)).take 6)) (eqAtG (a.map (ev2 M)))) l) _ fun l _ ↦
      hs_mono (hs_laneFormG hz B Bv hB _ l) fun r hr ↦ by
        rw [hr]
        exact congrArg (fun R ↦ laneFormF Bv R l) (funext hsh')) fun lf hlf ↦
    hs_mono (hs2_dot z _) fun r hr ↦ ?_
  rw [hr, hz', zero_add, dot_lt (lp := lp.map (ev2 M)) (by simp [hlp]) (a.map (ev2 M)) Bv, sumF_eq_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun l hl ↦ ?_)
  simp only [Function.comp_apply]
  rw [ev2_getDz hf hz', ev2_getDz hlf hz', getD_map_range _ (List.mem_range.mp hl), List.map_drop]

/-! ## An ill-shaped claim -/

/-- An assertion that fails under the gate (`1 ≠ 0`). -/
def failG (claim : ClaimC) (one : C2) (gate : Cell) : BM ClaimC :=
  g2Assert one gate >>= fun _ ↦ pure claim

theorem hsA_failG {claim : ClaimC} {one : C2} {gate : Cell} (hone : one.val M = 1)
    (hg : gate.val M = 1) {P : ClaimC → Prop} : HsA c M (failG claim one gate) P :=
  hsA_bind (hsA_g2Assert one gate hg) fun _ h ↦ absurd (hone.symm.trans h) one_ne_zero

end Lvm6.QK
