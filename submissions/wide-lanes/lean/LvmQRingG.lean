-- New for lvm2 (T-Q): v1's ring-switch gadget (`ringG`, HAR-RC's, from `LvmQAsmArith2Ring`) and
-- its cell spec, moved below the assembly modules so that the S2 wire gadget (`LvmQWire`) can use
-- it without the v1 phase cut. Unchanged text; `vs` moved here from `LvmQAsmHarBase`.
import LvmQSumcheckCore
import LvmQRing
import LvmQWhirBase

-- ===== merged from `LvmQRingTarget` (GOLF module merge: `LvmQRingTarget.lean` is now a stub importing `LvmQRingG`) =====
section
-- New for lvm (WP-11b-QA2, helper H1); `polyEval_sum` adapted from our `LvmPolyLE.polyEval_eq_sum`
-- (leanVM formal `EndToEnd/Complete/Sumcheck.lean` rev 40f877dc), restated on `Lvm.FE`.

/-!
# QA2 ring switching, part 2: the target `Σ_i g^i Φ(s_i)`

`F`'s target (`LvmDecideKeccak.ringSwitch`): `polyEval (s.map (phiMap · ch)) gen` over the 64
slices `s_i` (stream scalars) and the six challenges. Gadget `ringTargetG lb ch z`:

* `loadL [6]`: the slices from the `K` lanes `lb + 3i + (0, 1, 2)` (64 `loadE` rows);
* `phiStages`: `Φ` stage by stage over all 64 slices at once (`phiStage b f`, shift `2^b`, challenge
  cell `f`): squarings dims `[6, b]` (slice fastest; the step-`j` row reads step `j − 1`, 64 cells
  back, and step 0 the 64 stage inputs just before the block), then `v' = v + f·v^(2^(2^b))`
  (dims `[6]`); `64·2^b + 64` rows per stage, 4416 in all;
* Horner in natural order: `acc_x = Φ_x + g⁻¹·acc_{x−1}` (`lin`, `acc_{−1}` a copy of the zero
  cell), and `target = g^63·acc_63` (one `lin`). 66 rows.

`ringTarget_eq`: **the target cell is `F`'s `polyEval (s.map (phiMap · ch)) gen`**.
-/

set_option autoImplicit false

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

/-! ## `F`'s side -/

-- adapted from LvmPolyLE.polyEval_eq_sum (leanVM formal Complete/Sumcheck.lean), on Lvm.FE
theorem polyEval_sum : ∀ (l : List FE) (x : FE),
    polyEval l x = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i
  | [], x => by simp [polyEval]
  | a :: l, x => by
    have h : polyEval (a :: l) x = polyEval l x * x + a := rfl
    rw [h, polyEval_sum l x, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun i _ => by
        rw [List.getD_cons_succ, pow_succ]; ring
    · rw [List.getD_cons_zero, pow_zero, mul_one]

theorem x_ne_zero : FK.x ≠ 0 := by decide

theorem ofK_xinv_mul : FE.ofK (FK.x)⁻¹ * FE.ofK FK.x = 1 := by
  rw [← ofK_mul, inv_mul_cancel₀ x_ne_zero, ofK_one]

/-! ## One stage of `Φ` -/

/-- Stage with shift `2^b` and challenge cell `f`: the stage inputs `V_x` are the 64 cells before
the pointer; squarings `(x, j) ↦ V_x^(2^(j+1))` (dims `[6, b]`), then `V_x + f·V_x^(2^(2^b))`. -/
def phiStage (b f z : Nat) : BM Unit := do
  let p ← getPtr
  let _ ← madL [6, b] (eA (p.e - 64) [1, 64]) (eA (p.e - 64) [1, 64]) (eA z [])
  let _ ← madL [6] (eA f []) (eA (p.e + 64 * (2 ^ b - 1)) [1]) (eA (p.e - 64) [1])
  pure ()

theorem phiStage_adv (b f z : Nat) (p : Ptr) :
    p.adv (phiStage b f z p).2 = ⟨p.k, p.e + 64 * 2 ^ b + 64⟩ := by
  simp only [phiStage]
  rw [bind_adv_eq (getPtr_out _) (getPtr_adv _), bind_adv_eq rfl (madL_adv _ _ _ _ _),
    bind_adv_eq rfl (madL_adv _ _ _ _ _), pure_apply, Ptr.adv_nil]
  simp [pow_add]

theorem phiStage_spec {b f z : Nat} {p : Ptr} (hz : M.e z = 0) (h64 : 64 ≤ p.e)
    (h : SegsHold c M p (phiStage b f z p).2) :
    ∀ x < 64, M.e (p.e + 64 * 2 ^ b + x) =
      M.e (p.e - 64 + x) + M.e f * M.e (p.e - 64 + x) ^ 2 ^ 2 ^ b := by
  simp only [phiStage] at h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq rfl (madL_adv _ _ _ _ _)] at h
  obtain ⟨hs, h⟩ := h
  rw [hold_bind_eq rfl (madL_adv _ _ _ _ _)] at h
  obtain ⟨hc, -⟩ := h
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hc
  have hsq : ∀ x < 2 ^ 6, ∀ j < 2 ^ b,
      M.e (p.e + (x + 2 ^ 6 * j)) = M.e (p.e - 64 + x) ^ 2 ^ (j + 1) := by
    intro x hx j
    induction j with
    | zero =>
      intro hj
      have e := madL_spec hs (jf := x + 2 ^ 6 * 0) (by simpa using lt_size_la hx hj)
      rw [unflat_two hx hj] at e
      simp only [Mem.rd, Addr.at, dot, hz, add_zero, Nat.one_mul, Nat.mul_zero] at e
      rw [show p.e + (x + 2 ^ 6 * 0) = p.e + x by simp, e]; ring
    | succ j ih =>
      intro hj
      have e := madL_spec hs (jf := x + 2 ^ 6 * (j + 1)) (by simpa using lt_size_la hx hj)
      rw [unflat_two hx hj] at e
      simp only [Mem.rd, Addr.at, dot, hz, add_zero, Nat.one_mul] at e
      rw [e, show p.e - 64 + (x + 64 * (j + 1)) = p.e + (x + 2 ^ 6 * j) by (clear * - h64; omega),
        ih (by (clear * - hj; omega)), ← pow_two, ← pow_mul, pow_succ 2 (j + 1)]
  intro x hx
  have e := madL_spec hc (jf := x) (by simpa using hx)
  simp only [Mem.rd, Addr.at, unflat_one (show x < 2 ^ 6 by simpa using hx), dot, Nat.one_mul,
    Nat.add_zero, Nat.zero_mul] at e
  have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hl := hsq x (by simpa using hx) (2 ^ b - 1) (by (clear * - hb1; omega))
  rw [Nat.sub_add_cancel hb1, show p.e + (x + 2 ^ 6 * (2 ^ b - 1)) = p.e + 64 * (2 ^ b - 1) + x by
    (clear * -; omega)] at hl
  rw [show p.e + 64 * 2 ^ b + x = p.e + 2 ^ (6 + b) + x by simp [pow_add], e, hl, add_comm]

/-! ## All stages -/

/-- The stages `(b, f)` in order. -/
def phiStages (z : Nat) : List (Nat × Nat) → BM Unit
  | [] => pure ()
  | (b, f) :: rest => do
    phiStage b f z
    phiStages z rest

/-- One stage on a value: `v + f·v^(2^(2^b))`. -/
def stageF (M : Mem) (v : FE) (bf : Nat × Nat) : FE := v + M.e bf.2 * v ^ 2 ^ 2 ^ bf.1

theorem phiStages_adv (z : Nat) : ∀ (L : List (Nat × Nat)) (p : Ptr),
    p.adv (phiStages z L p).2 = ⟨p.k, p.e + (L.map fun bf => 64 * 2 ^ bf.1 + 64).sum⟩
  | [], p => by simp [phiStages, pure_apply]
  | (b, f) :: rest, p => by
    simp only [phiStages]
    rw [bind_adv_eq rfl (phiStage_adv _ _ _ _), phiStages_adv z rest]
    simp only [List.map_cons, List.sum_cons, Ptr.mk.injEq, true_and]
    omega

theorem phiStages_spec {z : Nat} (hz : M.e z = 0) : ∀ (L : List (Nat × Nat)) (p : Ptr)
    (V : Nat → FE), 64 ≤ p.e → (∀ x < 64, M.e (p.e - 64 + x) = V x) →
    SegsHold c M p (phiStages z L p).2 →
    ∀ x < 64, M.e (p.e + (L.map fun bf => 64 * 2 ^ bf.1 + 64).sum - 64 + x) =
      L.foldl (stageF M) (V x)
  | [], p, V, _, hV, _ => by simpa using hV
  | (b, f) :: rest, p, V, h64, hV, h => by
    simp only [phiStages] at h
    rw [hold_bind_eq rfl (phiStage_adv _ _ _ _)] at h
    obtain ⟨h1, h2⟩ := h
    have hs := phiStage_spec hz h64 h1
    have ih := phiStages_spec hz rest _ (fun x => stageF M (V x) (b, f))
      (by show 64 ≤ p.e + 64 * 2 ^ b + 64; omega)
      (fun x hx => by
        simp only [stageF]
        rw [show p.e + 64 * 2 ^ b + 64 - 64 + x = p.e + 64 * 2 ^ b + x by omega, hs x hx, hV x hx])
      h2
    simp only at ih
    intro x hx
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    rw [← ih x hx]
    congr 1
    omega

/-- The stages of `F`'s `Φ`: shift `32` with challenge cell `ch`, …, shift `1` with `ch + 5`. -/
def phiList (ch : Nat) : List (Nat × Nat) :=
  [(5, ch), (4, ch + 1), (3, ch + 2), (2, ch + 3), (1, ch + 4), (0, ch + 5)]

theorem phiList_sum (ch : Nat) : ((phiList ch).map fun bf => 64 * 2 ^ bf.1 + 64).sum = 4416 := by
  simp [phiList]

theorem phiList_eq {ch : Nat} {chs : List FE} (hl : chs.length = 6)
    (hch : ∀ i < 6, M.e (ch + i) = chs.getD i 0) (v : FE) :
    (phiList ch).foldl (stageF M) v = phiMap v chs := by
  match chs, hl with
  | [f0, f1, f2, f3, f4, f5], _ =>
    have e0 : M.e ch = f0 := by simpa using hch 0 (by norm_num)
    have e1 : M.e (ch + 1) = f1 := by simpa using hch 1 (by norm_num)
    have e2 : M.e (ch + 2) = f2 := by simpa using hch 2 (by norm_num)
    have e3 : M.e (ch + 3) = f3 := by simpa using hch 3 (by norm_num)
    have e4 : M.e (ch + 4) = f4 := by simpa using hch 4 (by norm_num)
    have e5 : M.e (ch + 5) = f5 := by simpa using hch 5 (by norm_num)
    simp only [phiList, phiMap, ringMapShifts, List.zip_cons_cons, List.zip_nil_right,
      List.foldl_cons, List.foldl_nil, stageF, FE.frob_eq_pow, e0, e1, e2, e3, e4, e5]
    norm_num

/-! ## The target -/

/-- **The ring-switching target** from the slices in the `K` lanes `lb + 3i + (0, 1, 2)`
(`i < 64`), the challenges in the `E` cells `ch + i` and a zero `E` cell `z`; its cell is returned. -/
def ringTargetG (lb ch z : Nat) : BM Nat := do
  let _ ← loadL [6] ⟨.K, lb, [3]⟩ ⟨.K, lb + 1, [3]⟩ ⟨.K, lb + 2, [3]⟩
  phiStages z (phiList ch)
  let p ← getPtr
  let q ← copy (ec z)
  let _ ← linL [6] (FK.x)⁻¹ 0 (eA (p.e - 64) [1]) (eA q.n [1])
  let t ← lin .E (Build.gpow 63) 0 (ec z) (ec (q.n + 64))
  pure t.n

theorem ringTargetG_out (lb ch z : Nat) (p : Ptr) : (ringTargetG lb ch z p).1 = p.e + 4545 := by
  simp only [ringTargetG]
  rw [bind_fst_eq rfl (loadL_adv _ _ _ _ _), bind_fst_eq rfl (phiStages_adv _ _ _),
    bind_fst_eq (getPtr_out _) (getPtr_adv _), bind_fst_eq (copy_out _ _) (copyE_adv _ _),
    bind_fst_eq rfl (linL_adv _ _ _ _ _ _), bind_apply, phiList_sum]
  -- the cell by `show` and `Nat.add_assoc`: `simp`'s folding of the offsets left the kernel a unary `Nat.add`
  -- check through `p.e + 4545` (0.55 s)
  show p.e + 2 ^ [6].sum + 4416 + 1 + 2 ^ [6].sum = p.e + 4545
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
  rfl

private theorem lin_advE (k k' : FK) (a b : Cell) (P : Ptr) : P.adv (lin .E k k' a b P).2 = ⟨P.k, P.e + 1⟩ := by
  simp [lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem ringTargetG_adv (lb ch z : Nat) (p : Ptr) :
    p.adv (ringTargetG lb ch z p).2 = ⟨p.k, p.e + 4546⟩ := by
  simp only [ringTargetG]
  rw [bind_adv_eq rfl (loadL_adv _ _ _ _ _), bind_adv_eq rfl (phiStages_adv _ _ _), phiList_sum,
    bind_adv_eq (getPtr_out _) (getPtr_adv _), bind_adv_eq (copy_out _ _) (copyE_adv _ _),
    bind_adv_eq rfl (linL_adv _ _ _ _ _ _), bind_apply, Ptr.adv_append, lin_advE]
  -- as `ringTargetG_out` (the closing `simp` cost the kernel 0.3 s)
  show (⟨p.k + 0, p.e + 2 ^ [6].sum + 4416 + 1 + 2 ^ [6].sum + 1 + 0⟩ : Ptr) = _
  rw [Nat.add_zero, Nat.add_zero, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
  rfl

/-- **Q_arith_eq, ring-switching target.** If the lanes `lb + 3i + (0, 1, 2)` hold slice `s_i`
(`i < 64`), the `E` cells `ch + i` the challenges `ch_i` (`i < 6`) and `z` zero, the gadget's
cell (`p.e + 4545`) is `F`'s target `polyEval (s.map (phiMap · ch)) gen`. -/
theorem ringTarget_eq {lb ch z : Nat} {chs s : List FE} (hl : chs.length = 6)
    (hch : ∀ i < 6, M.e (ch + i) = chs.getD i 0) (hz : M.e z = 0) (hsl : s.length = 64)
    (hs : ∀ i < 64, (⟨M.k (lb + 3 * i), M.k (lb + 1 + 3 * i), M.k (lb + 2 + 3 * i)⟩ : FE) =
      s.getD i 0) {p : Ptr} (h : SegsHold c M p (ringTargetG lb ch z p).2) :
    M.e ((ringTargetG lb ch z p).1) = polyEval (s.map (phiMap · chs)) gen := by
  rw [ringTargetG_out]
  simp only [ringTargetG] at h
  rw [hold_bind_eq rfl (loadL_adv' [6] 64 rfl _ _ _ _)] at h
  obtain ⟨hL, h⟩ := h
  rw [hold_bind_eq rfl (phiStages_adv _ _ _), phiList_sum] at h
  obtain ⟨hP, h⟩ := h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq (copy_out _ _) (copyE_adv _ _)] at h
  obtain ⟨hq, h⟩ := h
  rw [hold_bind_eq rfl (linL_adv' [6] 64 rfl _ _ _ _ _)] at h
  obtain ⟨hH, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨hT, -⟩ := h
  -- `hH`, `hT`: `Ptr.at` by `rw`, the projections by `dsimp` (`simp only [Ptr.at]` there left the kernel a check
  -- of `Ptr.at … = p.e + 64 + 4416` that unfolded `Nat.add` in unary, 0.3 s)
  simp only [Ptr.at] at hq
  rw [show (ec z).ty = Ty.E from rfl, Ptr.at] at hH hT
  dsimp only at hH hT
  -- the loaded slices
  have hV : ∀ x < 64, M.e (p.e + 64 - 64 + x) = s.getD x 0 := by
    intro x hx
    have e := loadL_spec hL (jf := x) (by simpa using hx)
    simp only [Mem.rd, Addr.at, unflat_one (show x < 2 ^ 6 by simpa using hx), dot,
      Nat.add_zero] at e
    rw [show p.e + 64 - 64 + x = p.e + x by (clear * -; omega), e, loadE_eq, ← hs x hx]
  -- the stages: `Φ(s_x)` at `p.e + 4416 + x`
  have hΦ := phiStages_spec hz (phiList ch) ⟨p.k, p.e + 64⟩ (fun x => s.getD x 0)
    (by show 64 ≤ p.e + 64; (clear * -; omega)) hV hP
  rw [phiList_sum] at hΦ
  have hΦ' : ∀ x < 64, M.e (p.e + 4416 + x) = phiMap (s.getD x 0) chs := by
    intro x hx
    have e := hΦ x hx
    rw [show ({ k := p.k, e := p.e + 64 } : Ptr).e + 4416 - 64 + x = p.e + 4416 + x by
      show p.e + 64 + 4416 - 64 + x = p.e + 4416 + x; (clear * -; omega)] at e
    rw [e, phiList_eq hl hch]
  -- Horner
  have h0 := (copyE_spec hq).2
  simp only [Ptr.at] at h0
  have hacc : ∀ x < 64, FE.ofK (Build.gpow x) * M.e (p.e + 64 + 4416 + 1 + x) =
      ∑ y ∈ Finset.range (x + 1), FE.ofK (Build.gpow y) * phiMap (s.getD y 0) chs := by
    intro x hx
    induction x with
    | zero =>
      have e := linL_spec hH (jf := 0) (by simp)
      -- the right side only: simp's folding of the cell `p.e + 64 + 4416 + 1 + 0` to `p.e + 4481` cost the
      -- kernel a unary `Nat.add` check (0.4 s)
      conv at e => rhs; simp only [Mem.rd, Addr.at, unflat_one (show 0 < 2 ^ 6 by norm_num), dot, Nat.add_zero,
        Nat.mul_zero, h0, hz, mul_zero, ofK_zero]
      rw [e, show p.e + 64 + 4416 - 64 = p.e + 4416 by (clear * -; omega), hΦ' 0 hx]
      simp [gpow]
    | succ x ih =>
      have e := linL_spec hH (jf := x + 1) (by simpa using hx)
      simp only [Mem.rd, Addr.at, unflat_one (show x + 1 < 2 ^ 6 by simpa using hx), dot,
        Nat.add_zero, ofK_zero, Nat.one_mul, add_zero] at e
      rw [e,
        show p.e + 64 + 4416 - 64 + (x + 1) = p.e + 4416 + (x + 1) by (clear * -; omega), hΦ' _ hx,
        show p.e + 64 + 4416 + (x + 1) = p.e + 64 + 4416 + 1 + x by (clear * -; omega),
        Finset.sum_range_succ, ← ih (by (clear * - hx; omega))]
      have hg : FE.ofK (Build.gpow (x + 1)) * FE.ofK (FK.x)⁻¹ = FE.ofK (Build.gpow x) := by
        rw [← ofK_mul, Build.gpow, Build.gpow, pow_succ, mul_assoc, mul_inv_cancel₀ x_ne_zero,
          mul_one]
      linear_combination (M.e (p.e + 64 + 4416 + 1 + x)) * hg
  -- the final row
  have eT := lin_spec hT
  simp only [lin, rowRes, Cell.val, Mem.rd, Ptr.at, ec, hz, ofK_zero, zero_add, add_zero] at eT
  rw [show p.e + 4545 = p.e + 64 + 4416 + 1 + 64 by (clear * -; omega), eT,
    show p.e + 64 + 4416 + 64 = p.e + 64 + 4416 + 1 + 63 by (clear * -; omega), hacc 63 (by norm_num),
    polyEval_sum, List.length_map, hsl]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 64 := Finset.mem_range.1 hi
  have hm : (s.map (phiMap · chs)).getD i 0 = phiMap (s.getD i 0) chs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by (clear * - hsl hi'; omega))]
    rfl
  have hp : FE.ofK (FK.x ^ i) = FE.ofK FK.x ^ i := map_pow FE.ofKRingHom FK.x i
  rw [hm, gen, Build.gpow, hp, mul_comm]

end Lvm.Loop.QRing
end
-- ===== end of `LvmQRingTarget` =====

/-!
# The ring-switch gadget (`ringG`)

* `loadAt qs`: one `loadE` row per stream lane `q`; `loadAt_e`, `loadAt_vs`: the cells are
  `feAt Σ (8 q)`.
* **`ringG q lb z`**: the six challenges from lanes `q + 9 i`, QA2's `coeffs` and `ringTargetG`
  over the slices at lanes `lb + 3 k`; outputs `RingOut` = the 64 coefficient cells and the target.
* **`ringG_spec`**: the coefficients are `ringCoefficients (chsAt Σ q)`, the target is
  `polyEval ((slAt Σ lb).map (phiMap · chs)) gen`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM

/-- The values of a list of cells. -/
def vs (M : Mem) (l : List Cell) : List FE := l.map (Cell.val M)

/-! ## Loading stream scalars -/

/-- One `loadE` row per lane `q`: the stream's `E` scalar at lanes `q, q + 1, q + 2`. -/
def loadAt : List Nat → BM (List Cell)
  | [] => pure []
  | q :: qs => do
    let c ← loadE (kc q) (kc (q + 1)) (kc (q + 2))
    let cs ← loadAt qs
    pure (c :: cs)

variable {c : Ctx} {M : Mem}

theorem loadE_out (a₀ a₁ a₂ : Cell) (p : Ptr) : (loadE a₀ a₁ a₂ p).1 = ec p.e := rfl

theorem loadE_adv (a₀ a₁ a₂ : Cell) (p : Ptr) : p.adv (loadE a₀ a₁ a₂ p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem loadAt_adv : ∀ (qs : List Nat) (p : Ptr), p.adv (loadAt qs p).2 = ⟨p.k, p.e + qs.length⟩
  | [], p => by simp [loadAt, pure_apply]
  | q :: qs, p => by
    simp only [loadAt]
    rw [bind_adv_eq (loadE_out _ _ _ _) (loadE_adv _ _ _ _), bind_apply, Ptr.adv_append,
      loadAt_adv qs]
    simp only [pure_apply, Ptr.adv_nil, List.length_cons, Ptr.mk.injEq, true_and]
    omega

theorem loadAt_out : ∀ (qs : List Nat) (p : Ptr),
    (loadAt qs p).1 = (List.range qs.length).map fun i => ec (p.e + i)
  | [], p => rfl
  | q :: qs, p => by
    simp only [loadAt]
    rw [bind_fst_eq (loadE_out _ _ _ _) (loadE_adv _ _ _ _), bind_apply, loadAt_out qs]
    simp only [pure_apply, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    omega

theorem loadAt_e {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) :
    ∀ (qs : List Nat) (p : Ptr), (∀ q ∈ qs, q + 2 < T) → SegsHold c M p (loadAt qs p).2 →
      ∀ i < qs.length, M.e (p.e + i) = feAt sig (8 * qs.getD i 0)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | q :: qs, p, hq, h, i, hi => by
    simp only [loadAt] at h
    rw [hold_bind_eq (loadE_out _ _ _ _) (loadE_adv _ _ _ _), hold_bind] at h
    obtain ⟨h1, h2, -⟩ := h
    cases i with
    | zero =>
      have e := loadE_spec h1
      simp only [loadE_out, Cell.val_E, Cell.val_K] at e
      rw [Nat.add_zero, e, load_feAt hS (hq q (by simp))]
      rfl
    | succ i =>
      have e := loadAt_e hS qs _ (fun q' hq' => hq q' (by simp [hq'])) h2 i
        (by simpa using hi)
      rw [show p.e + (i + 1) = p.e + 1 + i by (clear * -; omega), e]
      rfl

/-- The values of `loadAt`'s cells. -/
theorem loadAt_vs {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (qs : List Nat) (p : Ptr)
    (hq : ∀ q ∈ qs, q + 2 < T) (h : SegsHold c M p (loadAt qs p).2) :
    vs M (loadAt qs p).1 = qs.map fun q => feAt sig (8 * q) := by
  rw [loadAt_out]
  refine List.ext_getElem (by simp [vs]) fun i h1 h2 => ?_
  simp only [vs, List.length_map, List.length_range] at h1
  simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
  rw [loadAt_e hS qs p hq h i h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rfl

/-! ## The ring-switch gadget -/

/-- The lanes of a ring switch's six challenges (`sampleE` answers from the reader at `8 q − 40`). -/
def ringLanes (q : Nat) : List Nat := (List.range ringStages).map fun i => q + 9 * i

/-- The six challenges at lanes `q + 9 i`. -/
def chsAt (sig : ByteArray) (q : Nat) : List FE :=
  (List.range ringStages).map fun i => feAt sig (8 * (q + 9 * i))

/-- The 64 slices at lanes `lb + 3 k`. -/
def slAt (sig : ByteArray) (lb : Nat) : List FE :=
  (List.range kBits).map fun k => feAt sig (8 * (lb + 3 * k))

/-- A ring switch's output cells. -/
structure RingOut where
  /-- The 64 Frobenius coefficients `c_k` (`ringCoefficients`). -/
  cs : List Cell
  /-- The target `Σ_i g^i Φ(s_i)`. -/
  target : Cell

/-- **A ring switch**: the challenges from lanes `q + 9 i`, the slices from lanes `lb + 3 k`, `z` an
`E` zero cell. -/
def ringG (q lb z : Nat) : BM RingOut := do
  let p ← getPtr
  let _ ← loadAt (ringLanes q)
  let cb ← coeffs p.e z
  let t ← ringTargetG lb p.e z
  pure ⟨(List.range kBits).map fun k => ec (cb + k), ec t⟩

theorem ringG_out (q lb z : Nat) (p : Ptr) :
    (ringG q lb z p).1 = ⟨(List.range kBits).map fun k => ec (p.e + 6 + 67 + k), ec (p.e + 6 + 131 + 4545)⟩ := by
  simp only [ringG]
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _), bind_fst_eq rfl (loadAt_adv _ _),
    bind_fst_eq (coeffs_out _ _ _) (coeffs_adv _ _ _), bind_fst_eq (ringTargetG_out _ _ _ _)
      (ringTargetG_adv _ _ _ _)]
  simp [pure_apply, ringLanes, ringStages]

/-- **The ring-switch gadget's cells.** -/
theorem ringG_spec {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (hS : Streamed M sig T)
    (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0) (h : SegsHold c M p (ringG q lb z p).2) :
    vs M (ringG q lb z p).1.cs = ringCoefficients (chsAt sig q) ∧
      (ringG q lb z p).1.target.val M = polyEval ((slAt sig lb).map (phiMap · (chsAt sig q))) gen := by
  simp only [ringG] at h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq rfl (loadAt_adv _ _)] at h
  obtain ⟨hL, h⟩ := h
  rw [hold_bind_eq (coeffs_out _ _ _) (coeffs_adv _ _ _)] at h
  obtain ⟨hC, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨hT, -⟩ := h
  have hlen : (ringLanes q).length = 6 := by simp [ringLanes, ringStages]
  simp only [hlen] at hC hT
  have hcl : (chsAt sig q).length = 6 := by simp [chsAt, ringStages]
  have hch : ∀ i < 6, M.e (p.e + i) = (chsAt sig q).getD i 0 := by
    intro i hi
    rw [loadAt_e hS (ringLanes q) p (fun q' hq' => by
      simp only [ringLanes, ringStages, List.mem_map, List.mem_range] at hq'
      obtain ⟨j, hj, rfl⟩ := hq'; (clear * - hq hj; omega)) hL i (by rw [hlen]; exact hi)]
    simp [ringLanes, chsAt, ringStages, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hco := coeffs_eq hcl hch hz hC
  have hsl : (slAt sig lb).length = 64 := by simp [slAt, kBits]
  have hs : ∀ i < 64, (⟨M.k (lb + 3 * i), M.k (lb + 1 + 3 * i), M.k (lb + 2 + 3 * i)⟩ : FE) =
      (slAt sig lb).getD i 0 := by
    intro i hi
    rw [hS _ (by (clear * - hlb hi; omega)), hS _ (by (clear * - hlb hi; omega)), hS _ (by (clear * - hlb hi; omega))]
    simp only [slAt, kBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some, feAt]
    congr 2 <;> (clear * -; omega)
  have hta := ringTarget_eq hcl hch hz hsl hs hT
  rw [ringG_out]
  refine ⟨?_, ?_⟩
  · refine List.ext_getElem (by simp [vs, kBits, ringCoefficients]) fun k h1 h2 => ?_
    simp only [vs, List.length_map, List.length_range, kBits] at h1
    simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
    rw [hco k h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  · rw [← hta, ringTargetG_out]
    rfl

end Lvm.Har
