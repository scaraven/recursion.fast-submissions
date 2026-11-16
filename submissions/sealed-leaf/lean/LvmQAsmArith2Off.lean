/- `LvmQAsmArith2Off` (GOLF2 off-path move, group 33 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQRingG, LvmQAsmBorrow, LvmQAsmArith2,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQRingG
import LvmQAsmBorrow
import LvmQAsmArith2
import LvmE2QHarPosOff
import LvmFinPosOff
import LvmQAsmHar47Off
import LvmQEqKeccakTapeOff
import LvmQTypedHarZOff
import LvmMlListLemmas
import LvmQAsmHar47

-- ===== from `LvmQRingG` =====

section
section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

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

end Lvm.Loop.QRing
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

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

end Lvm.Loop.QRing
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

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

end Lvm.Loop.QRing
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

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

end Lvm.Loop.QRing
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

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
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM
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

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM
variable {c : Ctx} {M : Mem}

/-- The six challenges at lanes `q + 9 i`. -/
def chsAt (sig : ByteArray) (q : Nat) : List FE :=
  (List.range ringStages).map fun i => feAt sig (8 * (q + 9 * i))

/-- The 64 slices at lanes `lb + 3 k`. -/
def slAt (sig : ByteArray) (lb : Nat) : List FE :=
  (List.range kBits).map fun k => feAt sig (8 * (lb + 3 * k))

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM
variable {c : Ctx} {M : Mem}

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
end

-- ===== from `LvmQAsmBorrow` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

theorem add_out (a b : Cell) (p : Ptr) : (add a b p).1 = ⟨jn a.ty b.ty, p.at (jn a.ty b.ty)⟩ := rfl

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

theorem borrowGo_vs (N nb : Nat) : ∀ (k j : Nat) (cy : Cell) (p : Ptr), cy.ty = .E →
    cy.val M = carryE N j → (∀ i < k, (kc (nb + j + i)).val M = bitE N (j + i)) → 1 ≤ N →
    SegsHold c M p (borrowGo nb j k cy p).2 →
    vs M (borrowGo nb j k cy p).1 = (List.range k).map fun i => bitE (N - 1) (j + i)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | k + 1, j, cy, p, hty, hcy, hb, hN, h => by
    simp only [borrowGo] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h2, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h3, -⟩ := h
    have e1 := add_val h1
    have e2 := mad_val h2
    have hb0 := hb 0 (by (clear * -; omega))
    simp only [Nat.add_zero] at hb0
    have ih := borrowGo_vs N nb k (j + 1) _ _ (by rw [mad_out, hty]; rfl)
      (by rw [e2, hcy, hb0, carry_succ]) (fun i hi => by
        rw [show nb + (j + 1) + i = nb + j + (i + 1) by (clear * -; omega), hb (i + 1) (by (clear * - hi; omega))]
        congr 1; (clear * -; omega)) hN h3
    rw [bind_apply, bind_apply, bind_apply, pure_apply]
    simp only [vs, List.map_cons] at ih ⊢
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map, e1, hb0, hcy, ← pred_bit N j hN,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1; (clear * -; omega)

theorem borrow_vs {N nb o n : Nat} {p : Ptr} (ho : M.e o = 1) (hb : ∀ j < n, (kc (nb + j)).val M = bitE N j) (hN : 1 ≤ N)
    (h : SegsHold c M p (borrow nb o n p).2) :
    vs M (borrow nb o n p).1 = (List.range n).map (bitE (N - 1)) := by
  match n, hb, h with
  | 0, _, _ => rfl
  | k + 1, hb, h =>
    simp only [borrow] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h2, -⟩ := h
    have e1 := add_val h1
    have hb0 := hb 0 (by (clear * -; omega))
    simp only [Nat.add_zero] at hb0
    have hc1 : (add (kc nb) (ec o) p).1.val M = carryE N 1 := by
      rw [e1, Cell.val_E, ho, hb0]
      have := carry_succ N 0
      simp only [carryE, pow_zero, Nat.mod_one, if_true, one_mul, Nat.zero_add] at this ⊢
      rw [this, add_comm]
    have ih := borrowGo_vs N nb k 1 _ _ rfl hc1 (fun i hi => by
      rw [show nb + 1 + i = nb + (1 + i) by (clear * -; omega)]; exact hb (1 + i) (by (clear * - hi; omega))) hN h2
    rw [bind_apply, bind_apply, pure_apply]
    simp only [vs, List.map_cons] at ih ⊢
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map, e1, Cell.val_E, ho, hb0, pred_bit N 0 hN]
    simp only [carryE, pow_zero, Nat.mod_one, if_true]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1; (clear * -; omega)

end Lvm.Har
end

-- ===== from `LvmQAsmArith2` =====

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM
variable {c : Ctx} {M : Mem}

theorem samplesAt_ring (sig : ByteArray) {q : Nat} (hq : 5 ≤ q) :
    samplesAt (feAt sig) (8 * q - 40) ringStages = chsAt sig q := by
  simp only [samplesAt, chsAt]
  refine List.map_congr_left fun i _ => ?_
  congr 1; omega

/-- **HAR's `ringAt` is the gadget's claim**: target and weight closure. -/
theorem ringG_ringAt {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (pt : List FE) (hq5 : 5 ≤ q)
    (hS : Streamed M sig T) (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0)
    (h : SegsHold c M p (ringG q lb z p).2) :
    (ringAt (feAt sig) (8 * q - 40) pt (slAt sig lb)).1 = (ringG q lb z p).1.target.val M ∧
      (ringAt (feAt sig) (8 * q - 40) pt (slAt sig lb)).2 =
        fun x => ringWeight pt x (vs M (ringG q lb z p).1.cs) := by
  obtain ⟨h1, h2⟩ := ringG_spec hS hq hlb hz h
  simp only [ringAt, samplesAt_ring sig hq5, h1, h2]
  exact ⟨trivial, trivial⟩

/-- The relation of a ring switch's result to the gadget's cells. -/
def RingRel (M : Mem) (pt : List FE) (res : FE × (List FE → FE)) (o : RingOut) : Prop :=
  res.1 = o.target.val M ∧ res.2 = fun x => ringWeight pt x (vs M o.cs)

/-- **`F`'s `ringSwitch` (after a Keccak GKR) replayed by `ringG`.** -/
theorem ringSwitch_replays {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (pt : List FE) (hq5 : 5 ≤ q)
    (hS : Streamed M sig T) (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0) :
    Replays c M sig (ringSwitch pt (slAt sig lb)) (ringG q lb z) p (8 * q - 40) (8 * q + 392)
      (RingRel M pt) := by
  intro hOk s hs hok
  rw [ringSwitch_run, hs]
  exact ⟨hok, by simp [pos, ringStages]; (clear * - hq5; omega), ringG_ringAt pt hq5 hS hq hlb hz hOk.1⟩

/-- **`F`'s `ringRaw` (the `CH` link's switches) replayed by `ringG`.** -/
theorem ringRaw_replays {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (hq5 : 5 ≤ q)
    (hS : Streamed M sig T) (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0) :
    Replays c M sig (ringRaw (slAt sig lb)) (ringG q lb z) p (8 * q - 40) (8 * q + 392)
      (fun res o => res.1 = o.target.val M ∧ res.2 = vs M o.cs) := by
  intro hOk s hs hok
  obtain ⟨h1, h2⟩ := ringG_spec hS hq hlb hz hOk.1
  rw [ringRaw_run]
  simp only [pos] at hs
  rw [hs, samplesAt_ring sig hq5]
  exact ⟨hok, by simp [pos, ringStages]; (clear * - hq5; omega), h2.symm, h1.symm⟩

/-- **The slices of `F`'s Keccak GKR** (first FS answer at lane `qs`) are the stream scalars at
lanes `gkrEnd P qs − 192 + 3 k`. -/
theorem vkSpec_slices (v : Nat → FE) {ls qs : Nat} (hls : 4 ≤ ls) (hq : 5 ≤ qs) (instV outV : List FE)
    (hinst : instV.length = ls) (ok : Bool) :
    (vkSpec v ls instV outV (8 * qs - 40) ok).1.slices =
      (List.range kBits).map fun k => v (8 * (gkrEnd (ls - 4) qs - 192 + 3 * k)) := by
  obtain ⟨h1, -, -⟩ := vk_facts v (ls - 4) qs instV outV ok hq (by (clear * - hls hinst; omega))
  rw [show ls - 4 + 4 = ls by (clear * - hls hinst; omega)] at h1
  rw [h1]
  simp only [vkSl, kBits]
  refine List.map_congr_left fun k _ => congrArg v ?_
  simp only [gkrEnd]
  (clear * -; omega)

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM
variable {c : Ctx} {M : Mem}

/-- **The ring switch after a Keccak GKR** (HAR's `chPh_run`/`ksPh_run` form): with `F`'s GKR read
from `8 qs − 40` (`K = vkSpec …`, ending at `8 · gkrEnd − 40`), `ringAt` at the GKR's end on its
slices is the gadget's claim. -/
theorem ringGkr_ringAt {sig : ByteArray} {T ls qs z : Nat} {p : Ptr} (hls : 4 ≤ ls) (hq : 5 ≤ qs)
    (instV outV : List FE) (hinst : instV.length = ls) (ok : Bool) (hS : Streamed M sig T)
    (hT : gkrEnd (ls - 4) qs + 48 ≤ T) (hz : M.e z = 0) (h : SegsHold c M p (ringGkr (ls - 4) qs z p).2) :
    RingRel M (vkSpec (feAt sig) ls instV outV (8 * qs - 40) ok).1.slicePoint
      (ringAt (feAt sig) (8 * gkrEnd (ls - 4) qs - 40) (vkSpec (feAt sig) ls instV outV (8 * qs - 40) ok).1.slicePoint
        (vkSpec (feAt sig) ls instV outV (8 * qs - 40) ok).1.slices) (ringGkr (ls - 4) qs z p).1 := by
  have hE : 192 ≤ gkrEnd (ls - 4) qs := by simp only [gkrEnd, gkrQO]; (clear * - hq; omega)
  rw [vkSpec_slices (feAt sig) hls hq instV outV hinst ok]
  exact ringG_ringAt _ (by simp only [gkrEnd, gkrQO]; (clear * - hq; omega)) hS hT (by (clear * - hT hE; omega)) hz h

/-- **The slices of QA1's GKR gadget** are the stream scalars at lanes `gkrEnd P qs − 192 + 3 k` (from
`gkr_spec`: the gadget's outputs are `F`'s `KeccakOut`). -/
theorem gkrGadget_slices {sig : ByteArray} {T P qs : Nat} {inst out : Nat → Cell} {b : Cell} {p : Ptr}
    (hP : Lvm.Q1.layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T) (hT : gkrEnd P qs ≤ T)
    (h : SegsHold c M p (gkrGadget P qs inst out b p).2) :
    ((gkrGadget P qs inst out b p).1.vals M).slices = slAt sig (gkrEnd P qs - 192) := by
  have g1 := (gkr_spec hP hq hS hT h ⟨8 * qs - 40, 0, true⟩ (by simp)).1
  rw [← g1, verifyKeccak_run sig _ _ _ _ (8 * qs - 40) (by simp),
    vkSpec_slices (feAt sig) (by (clear * -; omega)) hq _ _ (by simp) true, Nat.add_sub_cancel]
  rfl

/-- **The ring switch after a Keccak GKR**, for any `KeccakOut` `K` whose slices are the stream's
(`gkrGadget_slices`, `vkSpec_slices`): HAR's `ringAt` at the GKR's end is the gadget's claim. -/
theorem ringGkr_rel {sig : ByteArray} {T P qs z : Nat} {p : Ptr} (K : KeccakOut) (hq : 5 ≤ qs)
    (hK : K.slices = slAt sig (gkrEnd P qs - 192)) (hS : Streamed M sig T) (hT : gkrEnd P qs + 48 ≤ T)
    (hz : M.e z = 0) (h : SegsHold c M p (ringGkr P qs z p).2) :
    RingRel M K.slicePoint (ringAt (feAt sig) (8 * gkrEnd P qs - 40) K.slicePoint K.slices)
      (ringGkr P qs z p).1 := by
  have hE : 192 ≤ gkrEnd P qs := by simp only [gkrEnd, gkrQO]; (clear * - hq; omega)
  rw [hK]
  exact ringG_ringAt _ (by simp only [gkrEnd, gkrQO]; (clear * - hq; omega)) hS hT (by (clear * - hT hE; omega)) hz h

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

theorem vs_append (M : Mem) (a b : List Cell) : vs M (a ++ b) = vs M a ++ vs M b := List.map_append

theorem vs_getD (M : Mem) (l : List Cell) {i : Nat} (hi : i < l.length) :
    (l.getD i default).val M = (vs M l).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa [vs] using hi)]
  simp [vs]

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

theorem kClaimsC_val (blk : Placement) (ko : GkrOut) (rg : RingOut) (ring : FE × (List FE → FE))
    (hr : RingRel M (ko.vals M).slicePoint ring rg) :
    (kClaimsC blk ko rg).map (CClaim.val M) = (keccakClaims blk (ko.vals M) ring).map (.main, ·) := by
  obtain ⟨h1, h2⟩ := hr
  simp only [kClaimsC, keccakClaims, List.map_cons, List.map_nil, CClaim.val, GkrOut.vals, h1, h2, vs]

theorem or_eq_xor_of {x y : UInt64} (h : ∀ i, x.toNat.testBit i = true → y.toNat.testBit i = false) :
    x ||| y = x ^^^ y := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or, UInt64.toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor]
  have := h i
  cases hx : x.toNat.testBit i <;> cases hy : y.toNat.testBit i <;> simp_all

theorem testBit_shl8 (w : UInt64) (i : Nat) (hi : (w <<< (8 : UInt64)).toNat.testBit i = true) :
    8 ≤ i := by
  rw [UInt64.toNat_shiftLeft, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft] at hi
  simp at hi; omega

theorem testBit_shr56 (w : UInt64) (i : Nat) (hi : (w >>> (56 : UInt64)).toNat.testBit i = true) :
    i < 8 := by
  rw [UInt64.toNat_shiftRight, show (56 : UInt64).toNat % 64 = 56 from rfl, Nat.testBit_shiftRight] at hi
  by_contra hc
  have hlt := w.toNat_lt
  have : w.toNat.testBit (56 + i) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by (clear * - hc; omega))))
  simp_all

theorem pad_or0 (w : UInt64) : (0x43 : UInt64) ||| (w <<< 8) = (w <<< 8) ^^^ 0x43 := by
  rw [UInt64.or_comm]
  refine or_eq_xor_of fun i hi => ?_
  have h8 := testBit_shl8 w i hi
  rw [show (0x43 : UInt64).toNat = 0x43 from rfl]
  exact Nat.testBit_lt_two_pow
    (lt_of_lt_of_le (by norm_num : 0x43 < 2 ^ 8) (Nat.pow_le_pow_right (by norm_num) h8))

theorem pad_or1 (a b : UInt64) : (a >>> 56) ||| (b <<< 8) = (a >>> 56) ^^^ (b <<< 8) := by
  refine or_eq_xor_of fun i hi => ?_
  have := testBit_shr56 a i hi
  cases h : (b <<< (8 : UInt64)).toNat.testBit i
  · rfl
  · have := testBit_shl8 b i h; (clear h hi; omega)

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

theorem headerAt_lane (k : Nat) : headerAt (8 + 8 * k) = 8 * hdrLane (8 + 8 * k) := by
  simp only [hdrLane, headerAt]; omega

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

theorem ksYPartC_val (p : Params) (l : Nat) (ptc : List Cell) {z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) :
    ((ksYPartC p l ptc z o).1, vs M (ksYPartC p l ptc z o).2) = ksYPart p (layout0 p) l (vs M ptc) := by
  unfold ksYPartC ksYPart
  split_ifs <;> simp [vs_append, selC_vs hz ho]

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits
variable {c : Ctx} {M : Mem}

/-- **Q_arith_eq, `KS`'s output-lane claims (phase 6)**. -/
theorem ksOutC_val (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool} (rk vk : List Cell) {z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hvk : vk.length = 25) :
    (ksOutC p rk vk z o).map (CClaim.val M) =
      (M3.ofParts p bf tb tcl fv fs pck).ksOutputClaims (vs M rk) (vs M vk) := by
  show _ = ksOutputClaims0 p (vs M rk) (vs M vk)
  simp only [ksOutC, ksOutputClaims0, List.map_map]
  refine List.map_congr_left fun l hl => ?_
  have hl' := List.mem_range.mp hl
  have e := ksYPartC_val (M := M) p l rk hz ho
  simp only [Function.comp_apply, CClaim.val, vs_getD M vk (by (clear * - hvk hl'; omega) : l < vk.length)]
  rw [← e]

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig DM
variable {c : Ctx} {M : Mem}

theorem scSpec_fst (v : Nat → FE) (count : Nat) (es : List (Option FE)) (p : Nat) (claim : FE) :
    (scSpec v count p claim es).1 =
      (List.range es.length).map fun i => v (p + i * roundLen count + 40 + 24 * (count - 1)) := by
  refine List.ext_getElem (by rw [lnk_scSpec_length]; simp) fun i h1 h2 => ?_
  have e := scSpec_fst_getD v count i es p claim (by rw [lnk_scSpec_length] at h1; exact h1)
  rw [List.getD_eq_getElem _ _ h1] at e
  rw [e]
  simp

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig DM
variable {c : Ctx} {M : Mem}

theorem vs_take (M : Mem) (l : List Cell) (n : Nat) : vs M (l.take n) = (vs M l).take n := by
  simp [vs, List.map_take]

theorem ksLinkC_val (p : Params) {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1)
    (om rho' vals : List Cell) (i : KsLinkIn) (hom : vs M om = eqKernel (i.chal.drop p.ksLog))
    (homl : om.length = 32) (hrho : vs M rho' = i.shift.1) (hvals : vs M vals = i.vals)
    (hvl : vals.length = 4) :
    (ksLinkC p z o om rho' vals).map (CClaim.val M) = (ksLinkV1 p i).2 := by
  have hc : ∀ l < 32, (om.getD l default).val M = (eqKernel (i.chal.drop p.ksLog)).getD l 0 := by
    intro l hl; rw [vs_getD M om (by (clear * - homl hl; omega)), hom]
  have hv : ∀ k < 4, (vals.getD k default).val M = i.vals.getD k 0 := by
    intro k hk; rw [vs_getD M vals (by (clear * - hvl hk; omega)), hvals]
  simp only [ksLinkC, ksLinkV1, List.map_cons, List.map_nil, CClaim.val, List.map_map, vs_take, hrho,
    hv 0 (by (clear * -; omega)), hv 1 (by (clear * -; omega)), hv 2 (by (clear * -; omega)), hv 3 (by (clear * -; omega))]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_,
    List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩⟩
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    have e := ksYPartC_val (M := M) p l rho' hz ho
    rw [hrho] at e
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega))]
    rw [← e]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega)), vs_append, hrho, selC_vs hz ho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega)), vs_take, hrho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega)), vs_take, hrho]

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
    rw [drop_range_map, show p.ksLog + laneBits - p.ksLog = laneBits by (clear * -; omega)]
  have hll : lamF.length = laneBits := by simp [hlamF]
  have hL := loadAt_e hS (ksLamL p Q) ptr (fun q hq => by
    simp only [ksLamL, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only [laneBits] at hj hT ⊢; (clear * - hT hj; omega)) h1
  have hE := eqTab_eq (fun i => ec (ptr.e + i)) (ec z) (ec o) false lamF (by rw [hll]; exact h4) hz
    (fun _ => rfl) ho (fun i hi => by
      rw [hll] at hi
      rw [Cell.val_E, hL i (by simp [ksLamL, hi])]
      simp only [ksLamL, hlamF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some]
      congr 1; (clear * - hPQ; omega))
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
      simp only [laneBits] at hT ⊢; (clear * - hT hi; omega)) h2]
    simp only [ksLinkView, scSpec_fst, List.length_replicate, ksRhoL, List.map_map]
    refine List.map_congr_left fun i _ => congrArg (feAt sig) ?_
    simp only [ksP1, roundLen, laneBits]; (clear * - hPQ; omega)
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksValL, List.mem_map, List.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      (clear * - hT hll hk; omega)) h3]
    simp only [ksLinkView, scalarsAt, ksValL, List.map_map]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [ksP2, ksP1, roundLen, laneBits]; (clear * - hPQ; omega)

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig DM
variable {c : Ctx} {M : Mem}

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
    intro l hl; rw [vs_getD M om (by (clear * - homl hl; omega)), hom]
  have hv : ∀ k < 4, (vals.getD k default).val M = i.vals.getD k 0 := by
    intro k hk; rw [vs_getD M vals (by (clear * - hvl hk; omega)), hvals]
  simp only [ksLinkC14, ksLink14, List.map_cons, List.map_nil, CClaim.val, List.map_map, List.map_append,
    vs_take, hrho, hv 0 (by (clear * -; omega)), hv 1 (by (clear * -; omega)), hv 2 (by (clear * -; omega)), hv 3 (by (clear * -; omega))]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_,
    List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩⟩
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    have e := ksYPartC_val (M := M) p l rho' hz ho
    rw [hrho] at e
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega))]
    rw [← e]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega)), vs_append, hrho, selC_vs hz ho]
  · congr 2
    congr 1
    · refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      simp only [Function.comp_apply, hc l (by (clear * - hl'; omega)), hrho]
    · refine List.map_congr_left fun l hl => ?_
      have hl' := List.mem_range.mp hl
      simp only [Function.comp_apply, homs l hl', vs_take, hrho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by (clear * - hl'; omega)), vs_take, hrho]

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
    rw [drop_range_map, show p.ksLog + laneBits - p.ksLog = laneBits by (clear * -; omega)]
  have hll : lamF.length = laneBits := by simp [hlamF]
  have hrhoL : rhoF = (ksRhoL p Q).map fun q => feAt sig (8 * q) := by
    simp only [hrhoF, ksLinkView, scSpec_fst, List.length_replicate, ksRhoL, List.map_map]
    refine List.map_congr_left fun i _ => congrArg (feAt sig) ?_
    simp only [ksP1, roundLen, laneBits]; (clear * - hPQ; omega)
  have hrl : rhoF.length = p.ksLog := by rw [hrhoL]; simp [ksRhoL]
  have hL := loadAt_e hS (ksLamL p Q) ptr (fun q hq => by
    simp only [ksLamL, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only [laneBits] at hj hT ⊢; (clear * - h4 hT hrl hj; omega)) h1
  have hlamv : ∀ i < laneBits, M.e (ptr.e + i) = lamF.getD i 0 := fun i hi => by
    rw [hL i (by simp [ksLamL, hi])]
    simp only [ksLamL, hlamF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    congr 1; (clear * - hPQ; omega)
  have hE := eqTab_eq (fun i => ec (ptr.e + i)) (ec z) (ec o) false lamF (by rw [hll]; exact h4') hz
    (fun _ => rfl) ho (fun i hi => by rw [hll] at hi; rw [Cell.val_E, hlamv i hi])
  rw [hll] at hE
  -- the second table: `λ ‖ ρ'_{xl…}`
  have hRv := loadAt_e hS (ksRhoL p Q) _ (fun q hq => by
    simp only [ksRhoL, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    simp only [laneBits] at hT ⊢; (clear * - hT hrl hi; omega)) h2
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
          rw [hsF, List.length_append, hll, hw] at hi; simp [ksRhoL]; (clear * - hxl hll hrl hi h5; omega)
        rw [if_neg h5, Cell.val_E, loadAt_out, List.getD_eq_getElem _ _ (by simpa using hk),
          List.getElem_map, List.getElem_range, hRv _ hk, hsF,
          List.getD_append_right _ _ _ _ (by rw [hll]; (clear * - hll h5; omega)), hll, List.getD_eq_getElem?_getD,
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
      (clear * - hl h1w; omega)
    have hidx : ksTop p + l = l + 2 ^ lamF.length * (2 ^ (rhoF.drop (ksXLog p)).length - 1) := by
      rw [hll, hw, ksTop, laneBits]; ring
    rw [List.getD_eq_getElem _ _ (by simpa using htop), List.getElem_map, List.getElem_range, Cell.val_E,
      hE2 _ htop, if_neg (by simp), eqKernelA_getD _ _ (by rw [← hsl]; exact htop), hsF, eqW_append, hidx,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [hll]; simp only [laneBits]; (clear * - hl; omega)),
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by rw [hll]; simp only [laneBits]; (clear * - hl; omega)),
      zero_add, eqW_ones, hlam, ← Lvm.Q1.prodE_eq_prodF, eqKernel_getD_A,
      eqKernelA_getD _ _ (by rw [hll]; simp only [laneBits]; (clear * - hl; omega))]
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksRhoL, List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      simp only [laneBits] at hT ⊢; (clear * - hT hrl hi; omega)) h2, ← hrhoL]
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksValL, List.mem_map, List.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      (clear * - hT hll hrl hk; omega)) h3]
    simp only [ksLinkView, scalarsAt, ksValL, List.map_map]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [ksP2, ksP1, roundLen, laneBits]; (clear * - hPQ; omega)

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
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop

/-- **The cells' claims are `F`'s** given each part's equation. -/
theorem claimsC_val (M : Mem) (p : Params) (m : M3) (pub : Pub) (bus : BusOut)
    (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut) (rk vks : List FE) (kko : KeccakOut)
    (kring : FE × (List FE → FE)) (kLinkClaims : List (Com × BlockClaim)) {tabCs tapeCs ksCs ksOut clK : List CClaim}
    (hbus : bus.claims = []) (htab : tabCs.map (CClaim.val M) = m.tableClaims pub evals)
    (htape : tapeCs.map (CClaim.val M) = (tapeClaims p tp wo pub).map (.main, ·))
    (hks : ksCs.map (CClaim.val M) = (keccakClaims m.ksBlock kko kring).map (.main, ·))
    (hko : ksOut.map (CClaim.val M) = m.ksOutputClaims rk vks)
    (hkl : clK.map (CClaim.val M) = kLinkClaims) :
    (claimsC tabCs tapeCs ksCs ksOut clK).map (CClaim.val M) =
      claimsOf p m pub bus evals tp wo rk vks kko kring kLinkClaims := by
  simp only [claimsC, claimsOf, List.map_append, htab, htape, hks, hko, hkl, hbus, List.nil_append]

end Lvm.Har
end
end
