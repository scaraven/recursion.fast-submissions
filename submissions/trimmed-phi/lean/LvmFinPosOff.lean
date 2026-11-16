/- `LvmFinPosOff` (GOLF2 off-path move, group 28 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQRing, LvmQRingWeight, LvmQAsmArith2Whir, LvmFinPos,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQRing
import LvmQRingWeight
import LvmQAsmArith2Whir
import LvmFinPos
import LvmNodeSoundTOff
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmSpecRulesCert

-- ===== from `LvmQRing` =====

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem loadL_adv (dims : List Nat) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (loadL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + 2 ^ dims.sum⟩ := by
  simp [loadL, loop, Ptr.adv, segsW, Seg.w, mkLoop, Block.tw, Block.size, Block.lsize, Row.w,
    Row.writes]

theorem madL_adv' (dims : List Nat) (n : Nat) (hn : 2 ^ dims.sum = n) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (madL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + n⟩ := by rw [madL_adv, hn]

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem loadL_adv' (dims : List Nat) (n : Nat) (hn : 2 ^ dims.sum = n) (a₀ a₁ a₂ : Addr) (p : Ptr) :
    p.adv (loadL dims a₀ a₁ a₂ p).2 = ⟨p.k, p.e + n⟩ := by rw [loadL_adv, hn]

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem loadL_spec {dims : List Nat} {a₀ a₁ a₂ : Addr} {p : Ptr}
    (h : SegsHold c M p (loadL dims a₀ a₁ a₂ p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    M.e (p.e + jf) = M.rd a₀.ty (a₀.at (unflat dims jf)) +
      FE.y * M.rd a₁.ty (a₁.at (unflat dims jf)) + FE.y * FE.y * M.rd a₂.ty (a₂.at (unflat dims jf)) := by
  have := loop_rel (t := 0) h hjf (by simp)
  rw [loop_apply] at this
  simpa [LRel, LoopOut.cell, LoopOut.arg, lrank, ltw, LRow.w, Row.w, Row.writes, Opd.val_abs,
    Cell.val, Mem.rd, Ptr.at] using this

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

/-- The `E` constant `k'` (`x + 1·x + k'`): result at `p.e`. -/
theorem constE_spec {k' : FK} {x : Nat} {p : Ptr} (h : SegsHold c M p (const .E k' (ec x) p).2) :
    M.e p.e = FE.ofK k' := by
  have := lin_spec h
  simp only [const, lin, rowRes, Cell.val, Mem.rd, Ptr.at, ec, ofK_one, one_mul] at this
  rw [this, CharTwo.add_self_eq_zero, zero_add]

theorem const_out (τ : Ty) (k' : FK) (x : Cell) (p : Ptr) : (const τ k' x p).1 = ⟨τ, p.at τ⟩ := rfl

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem frobTab_apply (b f z : Nat) (p : Ptr) : frobTab b f z p =
    (p.e, (copy (ec f) p).2 ++ ((madL [b] (eA p.e [1]) (eA p.e [1]) (eA z []) ⟨p.k, p.e + 1⟩).2 ++ [])) :=
  rfl

theorem frobTab_out (b f z : Nat) (p : Ptr) : (frobTab b f z p).1 = p.e := rfl

theorem frobTab_adv (b f z : Nat) (p : Ptr) :
    p.adv (frobTab b f z p).2 = ⟨p.k, p.e + 1 + 2 ^ b⟩ := by
  rw [frobTab_apply, Ptr.adv_append, copyE_adv, Ptr.adv_append, madL_adv]
  simp [Ptr.adv, segsW]

theorem frobTab_spec {b f z : Nat} {p : Ptr} (h : SegsHold c M p (frobTab b f z p).2)
    (hz : M.e z = 0) :
    (frobTab b f z p).1 = p.e ∧ p.adv (frobTab b f z p).2 = ⟨p.k, p.e + 1 + 2 ^ b⟩ ∧
      ∀ m ≤ 2 ^ b, M.e (p.e + m) = M.e f ^ 2 ^ m := by
  rw [frobTab_apply] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  obtain ⟨h1, h2, -⟩ := h
  obtain ⟨-, hv⟩ := copyE_spec h1
  rw [copyE_adv] at h2
  refine ⟨rfl, ?_, ?_⟩
  · rw [Ptr.adv_append, copyE_adv, Ptr.adv_append, madL_adv]
    simp [Ptr.adv, segsW]
  · intro m hm
    induction m with
    | zero => simpa using hv
    | succ m ih =>
      have hs := madL_spec h2 (jf := m) (by simp; (clear * - hm; omega))
      simp only [Mem.rd, Addr.at, unflat_one (show m < 2 ^ b by (clear * - hm; omega)), dot, hz, add_zero,
        Nat.one_mul, Nat.add_zero] at hs
      rw [show p.e + (m + 1) = p.e + 1 + m by (clear * -; omega), hs, ih (by (clear * - hm; omega)), ← pow_two, ← pow_mul,
        pow_succ]

/-- The coefficient `c_k` of `F`'s map in closed form: the product over the set bits `b` of `k`
of `f_{5-b}^(2^(k mod 2^b))` (`fc i` the challenge of shift `2^(5-i)`). -/
def coefV (fc : Nat → FE) (k : Nat) : FE :=
  ∏ b ∈ Finset.range 6, if k &&& 2 ^ b ≠ 0 then fc (5 - b) ^ 2 ^ (k % 2 ^ b) else 1

theorem coefV_zero (fc : Nat → FE) : coefV fc 0 = 1 := by simp [coefV]

/-- The bits of `2^b + m`, `m < 2^b` (a finite check, on the `m < 2^b` only: 378 cases instead of
the 2304 of `level_bits_list`). -/
theorem level_bits_list' : ∀ b ∈ List.range 6, ∀ m ∈ List.range (2 ^ b), ∀ b' ∈ List.range 6,
    (b' ≠ b → (((2 ^ b + m) &&& 2 ^ b' ≠ 0 ↔ m &&& 2 ^ b' ≠ 0) ∧
      (m &&& 2 ^ b' ≠ 0 → (2 ^ b + m) % 2 ^ b' = m % 2 ^ b'))) ∧
    (b' = b → ((2 ^ b + m) &&& 2 ^ b ≠ 0 ∧ (2 ^ b + m) % 2 ^ b = m ∧ m &&& 2 ^ b = 0)) := by
  decide

/-- The bits of `2^b + m`, `m < 2^b` (from `level_bits_list'`). -/
theorem level_bits_list : ∀ b ∈ List.range 6, ∀ m ∈ List.range 64, ∀ b' ∈ List.range 6, m < 2 ^ b →
    (b' ≠ b → (((2 ^ b + m) &&& 2 ^ b' ≠ 0 ↔ m &&& 2 ^ b' ≠ 0) ∧
      (m &&& 2 ^ b' ≠ 0 → (2 ^ b + m) % 2 ^ b' = m % 2 ^ b'))) ∧
    (b' = b → ((2 ^ b + m) &&& 2 ^ b ≠ 0 ∧ (2 ^ b + m) % 2 ^ b = m ∧ m &&& 2 ^ b = 0)) :=
  fun b hb m _ b' hb' hm => level_bits_list' b hb m (List.mem_range.2 hm) b' hb'

theorem level_bits {b m b' : Nat} (hb : b < 6) (hm : m < 2 ^ b) (hb' : b' < 6) :
    (b' ≠ b → (((2 ^ b + m) &&& 2 ^ b' ≠ 0 ↔ m &&& 2 ^ b' ≠ 0) ∧
      (m &&& 2 ^ b' ≠ 0 → (2 ^ b + m) % 2 ^ b' = m % 2 ^ b'))) ∧
    (b' = b → ((2 ^ b + m) &&& 2 ^ b ≠ 0 ∧ (2 ^ b + m) % 2 ^ b = m ∧ m &&& 2 ^ b = 0)) := by
  have h64 : m < 64 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by (clear * - hb; omega) : b ≤ 6))
  exact level_bits_list b (List.mem_range.2 hb) m (List.mem_range.2 h64) b' (List.mem_range.2 hb') hm

/-- **The level recursion**: `c_{2^b + m} = c_m · f_{5-b}^(2^m)`. -/
theorem coefV_level (fc : Nat → FE) {b m : Nat} (hb : b < 6) (hm : m < 2 ^ b) :
    coefV fc (2 ^ b + m) = coefV fc m * fc (5 - b) ^ 2 ^ m := by
  have hbr := Finset.mem_range.2 hb
  unfold coefV
  rw [← Finset.mul_prod_erase _ _ hbr, ← Finset.mul_prod_erase _ _ hbr]
  obtain ⟨-, hself⟩ := level_bits hb hm hb
  obtain ⟨h1, h2, h3⟩ := hself rfl
  rw [if_pos h1, h2, if_neg (by simpa using h3), one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun b' hb' => ?_
  obtain ⟨hne, hb'r⟩ := Finset.mem_erase.1 hb'
  obtain ⟨hlow, -⟩ := level_bits hb hm (Finset.mem_range.1 hb'r)
  obtain ⟨hiff, hmod⟩ := hlow hne
  by_cases hc : m &&& 2 ^ b' ≠ 0
  · rw [if_pos (hiff.2 hc), if_pos hc, hmod hc]
  · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]

theorem foldl_filter_mul {α : Type} (P : α → Bool) (g : α → FE) : ∀ (l : List α) (a : FE),
    (l.filter P).foldl (fun acc x => acc * g x) a =
      a * (l.map fun x => if P x then g x else 1).prod
  | [], a => by simp
  | x :: l, a => by
    by_cases hx : P x
    · simp [List.filter_cons, hx, foldl_filter_mul P g l, mul_assoc]
    · simp [List.filter_cons, hx, foldl_filter_mul P g l]

/-- **`F`'s coefficients are `coefV`.** -/
theorem ringCoefficients_getD {chs : List FE} (hl : chs.length = 6) {k : Nat} (hk : k < 64) :
    (ringCoefficients chs).getD k 0 = coefV (fun i => chs.getD i 0) k := by
  match chs, hl with
  | [f0, f1, f2, f3, f4, f5], _ =>
    have e1 : (fun (acc : FE) (x : FE × Nat) => match x with | (f, s) => acc * FE.frob (k % s) f) =
        fun acc x => acc * FE.frob (k % x.2) x.1 := by
      funext acc x; rcases x with ⟨f, s⟩; rfl
    have e2 : (fun (x : FE × Nat) => match x with | (_, s) => decide (k &&& s ≠ 0)) =
        fun x => decide (k &&& x.2 ≠ 0) := by
      funext x; rcases x with ⟨f, s⟩; rfl
    simp only [ringCoefficients, kBits, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some]
    rw [e2, e1, foldl_filter_mul]
    simp only [ringMapShifts, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, coefV, Finset.prod_range_succ, Finset.prod_range_zero,
      FE.frob_eq_pow, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      decide_eq_true_eq, one_mul, mul_one, Nat.reducePow, Nat.reduceSub]
    ring

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem cLevels_adv (cb z : Nat) : ∀ (fbs : List Nat) (b : Nat) (p : Ptr),
    p.adv (cLevels cb z b fbs p).2 = ⟨p.k, p.e + (2 ^ (b + fbs.length) - 2 ^ b)⟩
  | [], b, p => by simp [cLevels, pure_apply]
  | fb :: fbs, b, p => by
    simp only [cLevels]
    rw [bind_apply, Ptr.adv_append, madL_adv, cLevels_adv cb z fbs (b + 1)]
    simp only [List.length_cons, List.sum_cons, List.sum_nil, Nat.add_zero, Ptr.mk.injEq, true_and]
    rw [show b + (fbs.length + 1) = b + 1 + fbs.length by omega]
    have h1 : 2 ^ (b + 1) ≤ 2 ^ (b + 1 + fbs.length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := pow_succ 2 b
    (clear * - h1 h2; omega)

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem cLevels_spec (fc : Nat → FE) {cb z : Nat} (hz : M.e z = 0) : ∀ (fbs : List Nat) (b : Nat)
    (p : Ptr), p.e = cb + 2 ^ b → b + fbs.length ≤ 6 → TabsOk M fc b fbs →
    (∀ k < 2 ^ b, M.e (cb + k) = coefV fc k) → SegsHold c M p (cLevels cb z b fbs p).2 →
    p.adv (cLevels cb z b fbs p).2 = ⟨p.k, cb + 2 ^ (b + fbs.length)⟩ ∧
      ∀ k < 2 ^ (b + fbs.length), M.e (cb + k) = coefV fc k
  | [], b, p, hp, _, _, hc, _ => by
    refine ⟨?_, by simpa using hc⟩
    simp only [cLevels, pure_apply, Ptr.adv_nil, List.length_nil, Nat.add_zero]
    rw [← hp]
  | fb :: fbs, b, p, hp, hb, ht, hc, h => by
    simp only [cLevels] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h2⟩ := h
    rw [madL_adv] at h2
    obtain ⟨ht1, ht2⟩ := ht
    have hb6 : b < 6 := by simp at hb; (clear * - hb; omega)
    have hc' : ∀ k < 2 ^ (b + 1), M.e (cb + k) = coefV fc k := by
      intro k hk
      by_cases hk' : k < 2 ^ b
      · exact hc k hk'
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 ^ b + m := ⟨k - 2 ^ b, by (clear * - hk'; omega)⟩
        have hm : m < 2 ^ b := by rw [pow_succ] at hk; (clear * - hk; omega)
        have hs := madL_spec h1 (jf := m) (by simpa using hm)
        simp only [Mem.rd, Addr.at, unflat_one hm, dot, hz,
          add_zero, Nat.one_mul, Nat.add_zero, Nat.zero_mul] at hs
        rw [← Nat.add_assoc, ← hp, hs, hc m hm, ht1 m hm, coefV_level fc hb6 hm]
    have ih := cLevels_spec fc hz fbs (b + 1) _ (by simp [hp, pow_succ]; (clear * -; omega))
      (by simp at hb; (clear * - hb; omega)) ht2 hc' h2
    rw [bind_apply, Ptr.adv_append, madL_adv]
    simpa [Nat.add_assoc, Nat.add_comm 1] using ih

end Lvm.Loop.QRing
end

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem coeffs_out (ch z : Nat) (p : Ptr) : (coeffs ch z p).1 = p.e + 67 := by
  simp only [coeffs]
  rw [bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_fst_eq (const_out _ _ _ _) (constE_adv _ _ _), bind_apply]
  simp only [pure_apply, Ptr.at]
  omega

theorem coeffs_adv (ch z : Nat) (p : Ptr) : p.adv (coeffs ch z p).2 = ⟨p.k, p.e + 131⟩ := by
  simp only [coeffs]
  rw [bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _),
    bind_adv_eq (const_out _ _ _ _) (constE_adv _ _ _), bind_apply, Ptr.adv_append,
    cLevels_adv]
  simp only [pure_apply, Ptr.adv_nil, List.length_cons, List.length_nil]
  simp only [Ptr.mk.injEq, true_and]
  omega

/-- **Q_arith_eq, ring coefficients.** With the challenges in the `E` cells `ch + i` and a zero
cell `z`, the 64 cells from `(coeffs ch z p).1 = p.e + 67` hold `F`'s `ringCoefficients ch`. -/
theorem coeffs_eq {ch z : Nat} {chs : List FE} (hl : chs.length = 6)
    (hch : ∀ i < 6, M.e (ch + i) = chs.getD i 0) (hz : M.e z = 0) {p : Ptr}
    (h : SegsHold c M p (coeffs ch z p).2) :
    ∀ k < 64, M.e (p.e + 67 + k) = (ringCoefficients chs).getD k 0 := by
  simp only [coeffs] at h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h5, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h4, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h3, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h2, h⟩ := h
  rw [hold_bind_eq (frobTab_out _ _ _ _) (frobTab_adv _ _ _ _)] at h
  obtain ⟨h1, h⟩ := h
  rw [hold_bind_eq (const_out _ _ _ _) (constE_adv _ _ _)] at h
  obtain ⟨h0, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨hL, -⟩ := h
  have v5 := (frobTab_spec h5 hz).2.2
  have v4 := (frobTab_spec h4 hz).2.2
  have v3 := (frobTab_spec h3 hz).2.2
  have v2 := (frobTab_spec h2 hz).2.2
  have v1 := (frobTab_spec h1 hz).2.2
  have v0 := constE_spec h0
  simp only [Ptr.at, Nat.reducePow] at v5 v4 v3 v2 v1 v0 hL
  have hL' := cLevels_spec (fun i => chs.getD i 0) hz _ 0 _ (by simp) (by simp) ?_ ?_ hL
  · intro k hk
    rw [ringCoefficients_getD hl hk, ← hL'.2 k (by simpa using hk)]
  · simp only [TabsOk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · intro m hm
      obtain rfl : m = 0 := by simpa using hm
      simpa using hch 5 (by norm_num)
    · intro m hm; rw [v1 m (by simpa using hm.le), hch 4 (by norm_num)]
    · intro m hm; rw [v2 m (by simpa using hm.le), hch 3 (by norm_num)]
    · intro m hm; rw [v3 m (by simpa using hm.le), hch 2 (by norm_num)]
    · intro m hm; rw [v4 m (by simpa using hm.le), hch 1 (by norm_num)]
    · intro m hm
      have h0' := hch 0 (by norm_num)
      rw [Nat.add_zero] at h0'
      rw [v5 m (by simpa using hm.le), h0']
  · intro k hk
    obtain rfl : k = 0 := by simpa using hk
    rw [coefV_zero, Nat.add_zero, v0, ofK_one]

end Lvm.Loop.QRing
end

-- ===== from `LvmQRingWeight` =====

section
set_option autoImplicit false
namespace Lvm.Loop.QRing
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

/-- **The ring-switching weight** at the point `r` (cells `r0 + n`) and `r'` (cells `rp0 + n`),
`n < sz bs`, with the challenges in the `E` cells `ch + i` and a zero `E` cell `z`. -/
def ringWeightG (bs : List Nat) (ch r0 rp0 z : Nat) : BM Nat := do
  let Fs ← fChunks r0 rp0 0 bs
  let _ ← coeffs ch z
  pChunks z bs Fs
  let p ← getPtr
  let q ← copy (ec z)
  let _ ← linL [6] 1 0 (eA (p.e - 64) [1]) (eA q.n [1])
  pure (q.n + 64)

theorem ringWeightG_out (bs : List Nat) (ch r0 rp0 z : Nat) (p : Ptr) :
    (ringWeightG bs ch r0 rp0 z p).1 = p.e + 130 * sz bs + 195 := by
  simp only [ringWeightG]
  rw [bind_fst_eq rfl (fChunks_adv _ _ _ _ _), bind_fst_eq rfl (coeffs_adv _ _ _),
    bind_fst_eq rfl (pChunks_adv _ _ _ _), bind_fst_eq (getPtr_out _) (getPtr_adv _),
    bind_fst_eq (copy_out _ _) (copyE_adv _ _), bind_fst_eq rfl (linL_adv _ _ _ _ _ _), pure_apply]
  simp only [ec, Ptr.at]
  ring

theorem ringWeightG_adv (bs : List Nat) (ch r0 rp0 z : Nat) (p : Ptr) :
    p.adv (ringWeightG bs ch r0 rp0 z p).2 = ⟨p.k, p.e + 130 * sz bs + 196⟩ := by
  simp only [ringWeightG]
  rw [bind_adv_eq rfl (fChunks_adv _ _ _ _ _), bind_adv_eq rfl (coeffs_adv _ _ _),
    bind_adv_eq rfl (pChunks_adv _ _ _ _), bind_adv_eq (getPtr_out _) (getPtr_adv _),
    bind_adv_eq (copy_out _ _) (copyE_adv _ _), bind_adv_eq rfl (linL_adv _ _ _ _ _ _), pure_apply,
    Ptr.adv_nil]
  simp only [List.sum_cons, List.sum_nil, Ptr.mk.injEq, true_and]
  ring

/-- **Q_arith_eq, ring-switching weight.** If the `E` cells `r0 + n`, `rp0 + n` hold the point `r`
and the sumcheck point `r'` (`n < sz bs`, both of length `sz bs`), the cells `ch + i` the six
challenges and `z` zero, the gadget's cell (`p.e + 130·sz bs + 195`) is `F`'s
`ringWeight r r' (ringCoefficients ch)`. -/
theorem ringWeight_eq {bs : List Nat} {ch r0 rp0 z : Nat} {chs r rp : List FE}
    (hl : chs.length = 6) (hch : ∀ i < 6, M.e (ch + i) = chs.getD i 0) (hz : M.e z = 0)
    (hr : r.length = sz bs) (hrp : rp.length = sz bs)
    (hrv : ∀ n < sz bs, M.e (r0 + n) = r.getD n 0) (hrpv : ∀ n < sz bs, M.e (rp0 + n) = rp.getD n 0)
    {p : Ptr} (h : SegsHold c M p (ringWeightG bs ch r0 rp0 z p).2) :
    M.e (ringWeightG bs ch r0 rp0 z p).1 = ringWeight r rp (ringCoefficients chs) := by
  rw [ringWeightG_out]
  simp only [ringWeightG] at h
  rw [hold_bind_eq rfl (fChunks_adv _ _ _ _ _)] at h
  obtain ⟨hf, h⟩ := h
  rw [hold_bind_eq rfl (coeffs_adv _ _ _)] at h
  obtain ⟨hc, h⟩ := h
  rw [hold_bind_eq rfl (pChunks_adv _ _ _ _)] at h
  obtain ⟨hp, h⟩ := h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq (copy_out _ _) (copyE_adv _ _)] at h
  obtain ⟨hq, h⟩ := h
  rw [hold_bind_eq rfl (linL_adv' [6] 64 rfl _ _ _ _ _)] at h
  obtain ⟨hH, -⟩ := h
  have hF := fChunks_spec (R := fun n => r.getD n 0) (R' := fun n => rp.getD n 0) bs 0 p
    (by simpa using hrv) (by simpa using hrpv) hf
  have hC := coeffs_eq hl hch hz hc
  have hP := pChunks_spec hz bs _ 0 ⟨p.k, p.e + 66 * sz bs + 131⟩
    (fun k => (ringCoefficients chs).getD k 0) (by show 64 ≤ p.e + 66 * sz bs + 131; (clear * - hr hrp; omega))
    (fun k hk => by
      rw [← hC k hk]
      show M.e (p.e + 66 * sz bs + 131 - 64 + k) = M.e (p.e + 66 * sz bs + 67 + k)
      rw [show p.e + 66 * sz bs + 131 - 64 + k = p.e + 66 * sz bs + 67 + k by (clear * - hr hrp; omega)]) hF hp
  simp only [Nat.zero_add] at hP
  have h0 := (copyE_spec hq).2
  simp only [ec, Ptr.at] at h0 hH
  -- the running sum of the 64 products
  have hacc : ∀ k < 64, M.e (p.e + 66 * sz bs + 131 + 64 * sz bs + 1 + k) =
      ∑ j ∈ Finset.range (k + 1), (ringCoefficients chs).getD j 0 *
        ∏ n ∈ Finset.range (sz bs), wf (r.getD n 0) (rp.getD n 0) j := by
    intro k hk
    induction k with
    | zero =>
      have e := linL_spec hH (jf := 0) (by simp)
      simp only [Mem.rd, Addr.at, unflat_one (show 0 < 2 ^ 6 by norm_num), dot, Nat.add_zero,
        Nat.mul_zero, h0, hz, mul_zero, ofK_zero, ofK_one, one_mul, add_zero] at e
      rw [e, zero_add, Finset.sum_range_one]
      exact hP 0 hk
    | succ k ih =>
      have e := linL_spec hH (jf := k + 1) (by simpa using hk)
      simp only [Mem.rd, Addr.at, unflat_one (show k + 1 < 2 ^ 6 by simpa using hk), dot,
        Nat.add_zero, ofK_zero, ofK_one, one_mul, Nat.one_mul, add_zero] at e
      rw [e, Finset.sum_range_succ, ← ih (by (clear * - hk; omega)), ← hP (k + 1) hk, add_comm]
      congr 2
      (clear * -; omega)
  rw [show p.e + 130 * sz bs + 195 = p.e + 66 * sz bs + 131 + 64 * sz bs + 1 + 63 by ring,
    hacc 63 (by norm_num), ringWeight_sum r rp _ (by rw [hr, hrp]), hr]
  have hlen : (ringCoefficients chs).length = 64 := by simp [ringCoefficients, kBits]
  rw [hlen]

end Lvm.Loop.QRing
end

-- ===== from `LvmQAsmArith2Whir` =====

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem adv_k_le (p : Ptr) (δ : List Seg) : p.k ≤ (p.adv δ).k := Nat.le_add_right _ _

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem iwConsts_adv (m : Nat) {g : Cell} (hg : g.ty = .K) (p : Ptr) :
    p.adv (iwConsts m g p).2 = ⟨p.k + 2 * m, p.e⟩ := by
  simp only [iwConsts, bind_apply, Ptr.adv_append, kconsts_adv g hg, List.length_map, List.length_range]
  congr 1; (clear * -; omega)

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem seqCopy_adv : ∀ (cells : List Cell), (∀ x ∈ cells, x.ty = .E) → ∀ p : Ptr,
    p.adv (seqAll (cells.map copy) p).2 = ⟨p.k, p.e + cells.length⟩
  | [], _, p => by simp [seqAll, pure_apply]
  | x :: cells, hE, p => by
    obtain ⟨xt, xn⟩ := x
    have hx : xt = .E := hE ⟨xt, xn⟩ (by simp)
    subst hx
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, Ptr.adv_append, QRing.copyE_adv,
      seqCopy_adv cells (fun y hy => hE y (List.mem_cons_of_mem _ hy))]
    simp only [List.length_cons, Ptr.mk.injEq, true_and]; omega

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem copiesG_adv (cells : List Cell) (hE : ∀ x ∈ cells, x.ty = .E) (p : Ptr) :
    p.adv (copiesG cells p).2 = ⟨p.k, p.e + cells.length⟩ := by
  simp only [copiesG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil]
  exact seqCopy_adv cells hE p

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem pev_adv (q : Cell × Cell × Cell) (cc : Cell) (p : Ptr) : p.adv (pev q cc p).2 = ⟨p.k, p.e + 2⟩ := by
  simp [pev, bind_apply, mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build
variable {c : Ctx} {M : Mem}

theorem glueG_adv (lam : Cell) (q i : Cell × Cell × Cell) (p : Ptr) : p.adv (glueG lam q i p).2 = ⟨p.k, p.e + 3⟩ := by
  simp [glueG, bind_apply, pure_apply, mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem wsumG_adv : ∀ (gl : List (Cell × Cell)) (w : Cell) (p : Ptr), p.adv (wsumG w gl p).2 = ⟨p.k, p.e + gl.length⟩
  | [], w, p => by simp [wsumG, pure_apply]
  | (lam, W) :: gl, w, p => by
    simp only [wsumG, bind_apply, Ptr.adv_append]
    rw [wsumG_adv gl]
    simp [mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]; omega

theorem roundsG_adv (pc : Nat) : ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr),
    p.adv (roundsG pc f V n q p).2 = ⟨p.k, p.e + 5 * n⟩
  | 0, f, V, q, p => by simp [roundsG, pure_apply]
  | n + 1, f, V, q, p => by
    simp only [roundsG, bind_apply, Ptr.adv_append, pev_adv, rdQ_adv, roundsG_adv pc n]
    simp only [Ptr.mk.injEq, true_and]; omega

theorem tailG_adv (pc : Nat) : ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), 1 ≤ n →
    p.adv (tailG pc f V n q p).2 = ⟨p.k, p.e + 5 * n - 3⟩
  | 0, _, _, _, _, h => absurd h (by omega)
  | 1, f, V, q, p, _ => by simp only [tailG, pev_adv, Ptr.mk.injEq, true_and]; omega
  | n + 2, f, V, q, p, _ => by
    simp only [tailG, bind_apply, Ptr.adv_append, pev_adv, rdQ_adv]
    rw [tailG_adv pc (n + 1) _ _ _ _ (by omega)]
    simp only [Ptr.mk.injEq, true_and]; omega

end Lvm.Har
end
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {c : Ctx} {M : Mem}

set_option maxHeartbeats 1000000 in
/-- **One stacked opening replays `F`'s `verifyStackedOpening`.** -/
theorem stack_run (C : SCfg) (cl : List CClaim) (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : StackOk C cl T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGW C cl zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2.msg = 0 := by
  simp only [StackOk, Bool.and_eq_true] at hok
  unfold stackGW at h
  have e1 : (cl.map fun cc => (cc.val M).2.onStack).map (·.2) = cl.map fun cc => (cc.val M).2.value := by
    rw [List.map_map]; rfl
  have hn : (cl.map fun cc => (cc.val M).2.onStack).length = cl.length := List.length_map _
  have htg : ∀ (w : Unit), True → ∀ (sp : Nat) (σ : FE), (∀ i < cl.length, M.e (sp + i) = σ ^ i) →
      Hs c M (targetG cl sp zc) (fun t => t.val M =
        Lvm.dot (powers σ cl.length) ((cl.map fun cc => (cc.val M).2.onStack).map (·.2))) :=
    fun _ _ sp σ hsp p' h' => by rw [e1]; exact targetG_spec h' hz σ hsp
  have hbg : ∀ (w : Unit), True → ∀ (sp xb : Nat) (σ : FE), (∀ i < cl.length, M.e (sp + i) = σ ^ i) →
      Hs c M (basisG C.nu cl sp xb zc oc g) (fun b => b.val M = Lvm.dot (powers σ cl.length)
        ((cl.map fun cc => (cc.val M).2.onStack).map fun sc => sc.1 ((List.range C.nu).map fun i => M.e (xb + i)))) :=
    fun _ _ sp xb σ hsp p' h' => by rw [List.map_map]; exact basisG_spec h' hok.2 hz ho hzE hoE hgK σ hsp
  have k1 := stackG_run (β := Unit) (c := c) (M := M) C cl.length (pure ()) (fun _ sp => targetG cl sp zc)
    (fun _ sp xb => basisG C.nu cl sp xb zc oc g) (fun _ => True) (cl.map fun cc => (cc.val M).2.onStack) hn
    (fun _ _ => trivial) htg hbg zc oc g hS
  have k2 := k1 hok.1 hz ho hzE hoE hg hgK hpos hpw hp h s hs
  exact k2

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {c : Ctx} {M : Mem}
section Z
open Lvm.QShape Lvm.Shape

theorem fa2_mem {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | [], [], _, _, h => absurd h (by simp)
  | a :: l₁, b' :: l₂, .cons hab hr, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', hr'⟩ := fa2_mem hr b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

end Z
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {c : Ctx} {M : Mem}
section Z
open Lvm.QShape Lvm.Shape

/-- The muxed values of the claims are the stack claims' values on the shape's stack. -/
theorem tgt_list (b : Bool) {s : Cell} (hsv : s.val M = if b then 1 else 0) :
    ∀ (cl : List CClaim) (zs : List (CClaim × Bool)), List.Forall₂ (ZRel M s) cl zs →
      (zs.map (·.1)).map (fun cc => (cc.val M).2.value) =
        (onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))).map (·.2)
  | [], [], _ => by cases b <;> simp [onStackZsF]
  | cc :: cl, r :: zs, .cons hr hrs => by
    have ih := tgt_list b hsv cl zs hrs
    cases b
    · simp only [onStackZsF, Bool.false_eq_true, if_false] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      rw [cval_value, hr.value, hsv]
      simp only [Bool.false_eq_true, if_false, zero_mul, add_zero, Function.comp_apply]
      show _ = (cc.val M).2.value
      rw [cval_value]
    · simp only [onStackZsF, if_true] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      rw [cval_value, hr.value, hsv]
      simp only [if_true, one_mul, Function.comp_apply, onStackZB]
      rw [cval_value, CharTwo.sub_eq_add]

theorem bas_list (b : Bool) {s : Cell} (hsv : s.val M = if b then 1 else 0) (X : List FE)
    (hX : X.length = CMain.nu20) :
    ∀ (cl : List CClaim) (zs : List (CClaim × Bool)), List.Forall₂ (ZRel M s) cl zs →
      zs.map (if b then wSml M (rotZ X) else wBig M X) =
        (onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))).map fun sc => sc.1 X
  | [], [], _ => by cases b <;> simp [onStackZsF]
  | cc :: cl, r :: zs, .cons hr hrs => by
    have ih := bas_list b hsv X hX cl zs hrs
    cases b
    · simp only [onStackZsF, Bool.false_eq_true, if_false] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      simp only [Function.comp_apply, wBig]
      by_cases h2 : r.2 = true
      · rw [hr.reg h2]
      · exact hr.big (by simpa using h2) (by rw [hsv]; rfl) X hX
    · simp only [onStackZsF, if_true] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      simp only [Function.comp_apply, wSml]
      have hsm := hr.small (by rw [hsv]; rfl) X hX
      by_cases h2 : r.2 = true
      · rw [if_pos h2] at hsm ⊢; rw [hr.reg h2]; exact hsm
      · rw [if_neg h2] at hsm ⊢; exact hsm

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening in both shapes replays `F`'s** on `V_S`'s stack claims `onStackZsF b` of the claims
with their tails (`b`: the child is small; `σ'` holds `1` iff `b`). -/
theorem stackZ_run (C : SCfg) (cl : List CClaim) (mb : List Cell) (zc oc g : Cell) (b : Bool)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (hν : C.nu = CMain.nu20) (hwf : ClaimsWF CMain.nu20 cl = true) (hzw : ∀ cc ∈ cl, ZWF zc cc = true)
    {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk C T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGZ C cl mb zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    let scs := onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.msg = 0 := by
  intro scs
  have hlen : scs.length = cl.length := by cases b <;> simp [scs, onStackZsF]
  have hwf1 : ∀ cc ∈ cl, WF1 CMain.nu20 cc = true := by simpa [ClaimsWF, List.all_eq_true] using hwf
  refine stackG_run C cl.length _ _ _
    (fun w => (w.1.val M = if b then 1 else 0) ∧ List.Forall₂ (ZRel M w.1) cl w.2) scs hlen ?_ ?_ ?_
    zc oc g hS hok hz ho hzE hoE hg hgK hpos hpw hp h s hs
  · exact hs_bind (sigmaG_spec hz) fun σ hσv =>
      hs_bind (zClaimsG_spec hz ho cl hzw) fun zs hzs => hs_pure ⟨by rw [hσv, hσ], hzs⟩
  · intro w ⟨hsv, hrel⟩ sp σ hsp p' h'
    have hl : (w.2.map (·.1)).length = cl.length := by simp [hrel.length_eq.symm]
    rw [targetG_spec h' hz σ (fun i hi => hsp i (by rw [← hl]; exact hi)), hl, tgt_list b hsv cl w.2 hrel]
  · intro w ⟨hsv, hrel⟩ sp xb σ hsp
    have hl : w.2.length = cl.length := hrel.length_eq.symm
    have hX : ((List.range C.nu).map fun i => M.e (xb + i)).length = CMain.nu20 := by simp [hν]
    refine hs_bind (muxPtG_spec w.1 xb (List.range CMain.nu20)) fun ms ⟨hml, hmE, hmv⟩ => ?_
    have hcp : Hs c M (copiesG ms) (fun xs => ∀ i < CMain.nu20, M.e (xs + i) = (ms.getD i default).val M) :=
      fun p' h' => by
        obtain ⟨e1, e2⟩ := copiesG_spec hmE h'
        rw [e1]; exact fun i hi => e2 i (by rw [hml]; simpa using hi)
    have hw : ∀ e ∈ w.2, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1) := by
      intro e he
      obtain ⟨cc, hcc, hr⟩ := fa2_mem hrel e he
      refine ⟨hr.wf (hwf1 cc hcc), fun h2 => ?_⟩
      rw [hr.reg h2]; exact hr.regC h2
    refine hs_bind hcp fun xs hxs =>
      hs_mono (basisZ_spec hz ho hzE hw σ (fun j hj => hsp j (by rw [← hl]; exact hj))) fun bv hbv => ?_
    rw [hbv]
    set X := (List.range C.nu).map fun i => M.e (xb + i) with hXd
    have hXl : X.length = CMain.nu20 := hX
    have hXg : ∀ i < CMain.nu20, X.getD i 0 = M.e (xb + i) := fun i hi => by
      simp [hXd, List.getD_eq_getElem?_getD, List.getElem?_map, hν, hi]
    have hxs' : xsOf M CMain.nu20 xs = if b then rotZ X else X := by
      refine list_ext_getD _ _ (by cases b <;> simp [xs_length, hXl, rotZ_length X hXl]) fun i hi => ?_
      rw [xs_length] at hi
      have hm := hmv i (by simpa using hi)
      have hrN : (List.range CMain.nu20).getD i 0 = i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
      rw [hrN] at hm
      rw [xs_getD hi, hxs i hi, hm, hsv]
      cases b
      · simp only [Bool.false_eq_true, if_false, mux_zero]; rw [hXg i hi]
      · simp only [if_true, mux_one]; rw [rotZ_getD X hXl hi, hXg _ (Nat.mod_lt _ (by decide))]
    have hsl : (scs.map fun sc => sc.1 X).length = cl.length := by rw [List.length_map, hlen]
    rw [← hsl, dot_powers_bsum, hsv, hxs']
    cases b
    · simp only [Bool.false_eq_true, if_false, mux_zero]
      rw [← bas_list false (by rw [hsv]) X hXl cl w.2 hrel]
      rfl
    · simp only [if_true, mux_one]
      rw [← bas_list true (by rw [hsv]) X hXl cl w.2 hrel]
      rfl

end Z
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {c : Ctx} {M : Mem}

theorem on_eq (cs : List CClaim) (com : Com) :
    ((cs.map (CClaim.val M)).filter (·.1 == com)).map (·.2.onStack) =
      (onCom cs com).map fun cc => (cc.val M).2.onStack := by
  rw [List.filter_map, List.map_map]; rfl

theorem claimsT_rec (cs : List CClaim) :
    ((claimsT M cs).filter (·.1 == .crec)).map (·.2.1.onStack) = (onCom cs .crec).map fun cc => (cc.val M).2.onStack := by
  rw [claimsT, onCom, List.filter_map, List.map_map]; rfl

theorem claimsT_main (cs : List CClaim) :
    ((claimsT M cs).filter (·.1 == .main)).map (·.2) =
      (onCom cs .main).map fun cc => ((cc.val M).2, Lvm.QShape.tailC M cc) := by
  rw [claimsT, onCom, List.filter_map, List.map_map]; rfl

end Lvm.Har
end

-- ===== from `LvmFinPos` =====

section
section
set_option autoImplicit false
namespace Lvm.Har
open RecursionFast Lvm Lvm.QLink

theorem kToNat_laneK (ws : List Word) (i : Nat) : kToNat (laneK ws i) = lw ws i := rfl

end Lvm.Har
end
end

section
set_option autoImplicit false
namespace Lvm.Fin
section BVPos
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Bits Lvm.NS Lvm.QAsm Lvm.Har LeanVM.Protocol

/-- **`PosOk` from the position cells' values** (`F`'s positions are `posL`, `qsAt_posL`). -/
theorem posOk_of (C : SCfg) (k0 : ℕ) (hpb : ∀ i, C.pb i = posBase cfg20 (k0 + i)) {Ls : List Level} {V : ℕ}
    (hPL : PosLanes P20 C.g C.ood Ls V k0) {M : Mem} {ws : List Word} (hS : StreamOk P20) (hL : LaneLink P20 ws)
    (hQ : QOk P20 (lay cfg20))
    (hcell : ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t, M.k (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 ws (((opens P20).getD k default).pe + j / 8) (j % 8 * ((opens P20).getD k default).L.height)
          ((opens P20).getD k default).L.height)) :
    PosOk C M (traceBytesB (decode P20 ws)) 0 Ls V := by
  intro i hi j hj
  obtain ⟨hk, hLeq, hH, hP⟩ := hPL i hi
  rw [traceBytesB_decode hS hL, hpb, Nat.zero_add]
  have hjt : j < ((opens P20).getD (k0 + i) default).L.t := by rw [hLeq]; exact hj
  have ho : (opens P20).getD (k0 + i) default ∈ opens P20 := by
    -- `Option.getD_some` by `rw`: left to defeq, the kernel evaluates `opens P20` (1.5 s)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hjt
  have hin := lanes_in hS h1 hlt
  have hab := ansLane_bound hS hL.size hlt
  have e1 : posBase cfg20 (k0 + i) + j = nK cfg20 + posIdx P20 (k0 + i) j := by
    have hp : cfg20.p = P20 := rfl
    simp only [posBase, posIdx, hp]; (clear * -; omega)
  rw [e1, hcell _ hk (by rw [hLeq]; exact hH) j hjt]
  have hx : j / 8 < nAns ((opens P20).getD (k0 + i) default) := by unfold nAns; (clear * - hjt e1; omega)
  have hb : j % 8 * (Ls.getD i default).height + (Ls.getD i default).height ≤ 192 := by rw [← hLeq]; exact h192
  have hlen : 8 * ansLane P20 (((opens P20).getD (k0 + i) default).pe + j / 8) + 24 ≤ hashedLen P20 := by
    simp only [ansLane, if_neg (show ((opens P20).getD (k0 + i) default).pe + j / 8 ≠ 0 by (clear * - h1; omega))]; (clear * - hin; omega)
  rw [qsAt_posL P20 ws _ _ _ j hj (hP _ hx) hb hlen (by (clear * - hab; omega)), hLeq]
  rfl

end BVPos
end Lvm.Fin
end

section
set_option autoImplicit false
namespace Lvm.Fin
section Dec
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.Har Lvm.Replay Lvm.QLink
open Lvm.QAsm (QCfg cfg20 nK bsB pwB clog2 nAns pbB)
open Lvm.X (Blk blocks lensB lanesOf lanes_eq lensB_opn)

/-- A run of 32-byte queries in the plan (entries `e … e + n − 1`). -/
theorem lens_run {p : Params} {e n : ℕ} (hr : ((lens p).drop e).take n = List.replicate n 32) {y : ℕ}
    (hy : y < n) : e + y < (plan p).length ∧ ((plan p).getD (e + y) default).len = 32 := by
  have hl : (((lens p).drop e).take n).length = n := by rw [hr, List.length_replicate]
  simp only [List.length_take, List.length_drop, lens_length] at hl
  refine ⟨by (clear * - hy hl; omega), ?_⟩
  rw [← lens_getD]
  have h1 : (((lens p).drop e).take n).getD y 0 = 32 := by
    rw [hr, List.getD_eq_getElem _ _ (by simpa using hy), List.getElem_replicate]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hy, List.getElem?_drop] at h1
  rw [List.getD_eq_getElem?_getD]
  exact h1

/-- **Consecutive positions answers lie 9 lanes apart** when the entries after the first carry 32-byte
queries (`ansLane (i + 1) = ansLane i + 5 + len (i + 1) / 8`, QL's `eLane_succ`). -/
theorem ansLane_run {p : Params} (hS : streamOkL (plan p) = true) {e n : ℕ} (he : 1 ≤ e)
    (hr : ((lens p).drop (e + 1)).take n = List.replicate n 32) :
    ∀ x ≤ n, ansLane p (e + x) = ansLane p e + 9 * x
  | 0, _ => rfl
  | x + 1, hx => by
    have ih := ansLane_run hS he hr x (by omega)
    obtain ⟨h0, l1⟩ := lens_run hr (y := x) (by omega)
    have hs := eLane_succ hS (i := e + x) (by omega) (by omega)
    have a0 : ansLane p (e + x) = eLane p (e + x) + 1 + ((plan p).getD (e + x) default).len / 8 := by
      simp only [ansLane, ite_eq_right (show e + x ≠ 0 by omega)]
    have a1 : ansLane p (e + (x + 1)) = eLane p (e + x + 1) + 1 + 32 / 8 := by
      rw [← Nat.add_assoc, ← l1, show e + 1 + x = e + x + 1 by omega]
      simp only [ansLane, ite_eq_right (show e + x + 1 ≠ 0 by omega)]
    omega

/-- **`PosLanes` with one answer per opening**: level `i` is opening `k0 + i` (height at most 64), the
opening's entries after its first positions entry carry 32-byte queries, and its first answer is at the
level's positions lane. -/
def PosLanesR (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens p).length ∧ ((opens p).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧ 1 ≤ ((opens p).getD (k0 + i) default).pe ∧
    ((lens p).drop (((opens p).getD (k0 + i) default).pe + 1)).take
        (nAns ((opens p).getD (k0 + i) default) - 1) =
      List.replicate (nAns ((opens p).getD (k0 + i) default) - 1) 32 ∧
    8 * (posLanes g ood Ls V).getD i 0 + 40 = 8 * ansLane p ((opens p).getD (k0 + i) default).pe

theorem posLanes_of {p : Params} {g : ℕ} {ood : Bool} (hS : streamOkL (plan p) = true) {Ls : List Level} {V k0 : ℕ}
    (h : PosLanesR p g ood Ls V k0) : PosLanes p g ood Ls V k0 := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h i hi
  refine ⟨h1, h2, h3, fun x hx => ?_⟩
  rw [ansLane_run hS h4 h5 x (by (clear * - hx; omega))]
  (clear * - h6; omega)

/-- A block's entries. -/
def bCnt : Blk → ℕ
  | .one _ _ => 1
  | .opn t _ path => t * (path + 1)

theorem length_lensB (b : Blk) : (lensB b).length = bCnt b := by
  cases b with
  | one c len => rfl
  | opn t row path =>
    rw [lensB_opn]; simp [bCnt, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem length_flatMap_lensB (bs : List Blk) : (bs.flatMap lensB).length = (bs.map bCnt).sum := by
  rw [List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun b _ => length_lensB b)

theorem lanesOf_flatMap : ∀ bs : List Blk, lanesOf (bs.flatMap lensB) = (bs.map Blk.lanes).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← lanesOf_flatMap bs, lanes_eq]
    simp only [lanesOf, List.map_append, List.sum_append]

theorem slenS_lanesOf : ∀ {l : List ℕ}, (∀ x ∈ l, x % 8 = 0) → slenS l = 8 * lanesOf l
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := slenS_lanesOf (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [slenS, lanesOf, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem lens_blocks : lens P20 = 7 :: (blocks P20).flatMap lensB := Lvm.NS.lens_P20

theorem mod8_blocks {x : ℕ} (hx : x ∈ (blocks P20).flatMap lensB) : x % 8 = 0 := by
  have h := List.all_eq_true.mp Lvm.X.lensL_facts.2 x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- The answer lane of the entry that starts block `j` (a single query), from the blocks before it. -/
def blkAns (bs : List Blk) (j : ℕ) : Option ℕ :=
  match bs[j]? with
  | some (.one _ len) => some (6 + ((bs.take j).map Blk.lanes).sum + 1 + len / 8)
  | _ => none

theorem blkAns_some {bs : List Blk} {j A : ℕ} (h : blkAns bs j = some A) :
    ∃ c len, bs[j]? = some (.one c len) ∧ A = 6 + ((bs.take j).map Blk.lanes).sum + 1 + len / 8 := by
  unfold blkAns at h
  split at h
  · rename_i c len hj
    exact ⟨c, len, hj, (Option.some.inj h).symm⟩
  · cases h

/-- The plan's lengths around block `j` (a single query of `len` bytes). -/
theorem lens_split {j : ℕ} {c : QClass} {len : ℕ} (hj : (blocks P20)[j]? = some (.one c len)) :
    lens P20 =
      7 :: (((blocks P20).take j).flatMap lensB ++ len :: ((blocks P20).drop (j + 1)).flatMap lensB) := by
  have hl : j < (blocks P20).length := by
    by_contra h; rw [List.getElem?_eq_none (by (clear * - h; omega))] at hj; cases hj
  have hd : (blocks P20).drop j = .one c len :: (blocks P20).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hl]
    rw [List.getElem?_eq_getElem hl, Option.some.injEq] at hj
    rw [hj]
  have e : (blocks P20).flatMap lensB =
      ((blocks P20).take j).flatMap lensB ++ ((blocks P20).drop j).flatMap lensB := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [lens_blocks, e, hd, List.flatMap_cons]
  rfl

theorem drop_mid {α : Type} (a : α) (pre : List α) (x : α) (R : List α) :
    (a :: (pre ++ x :: R)).drop (1 + pre.length + 1) = R := by
  have e : a :: (pre ++ x :: R) = (a :: pre ++ [x]) ++ R := by simp
  rw [e, show 1 + pre.length + 1 = (a :: pre ++ [x]).length by simp; (clear * -; omega), List.drop_left]

/-- **The answer lane of a block's first entry** from the blocks before it. -/
theorem ansLane_blk {j A : ℕ} (h : blkAns (blocks P20) j = some A) :
    ansLane P20 (1 + (((blocks P20).take j).map bCnt).sum) = A := by
  obtain ⟨c, len, hj, rfl⟩ := blkAns_some h
  have hs := lens_split hj
  set pre := ((blocks P20).take j).flatMap lensB with hpre
  have hpl : pre.length = (((blocks P20).take j).map bCnt).sum := length_flatMap_lensB _
  have h8 : ∀ x ∈ pre, x % 8 = 0 := fun x hx => mod8_blocks (by
    rw [hpre] at hx
    obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨b, List.mem_of_mem_take hb, hx⟩)
  have hL : ((plan P20).getD (1 + pre.length) default).len = len := by
    rw [← lens_getD, hs, Nat.add_comm 1, List.getD_cons_succ, List.getD_append_right _ _ _ _ le_rfl,
      Nat.sub_self, List.getD_cons_zero]
  have hT : (lens P20).take (1 + pre.length) = 7 :: pre := by
    rw [hs, Nat.add_comm 1, List.take_succ_cons, List.take_left' rfl]
  rw [← hpl]
  simp only [ansLane, ite_eq_right (show 1 + pre.length ≠ 0 by (clear * - hpl; omega)), eLane, bOff, hT, hL]
  rw [show slenS (7 :: pre) = 47 + slenS pre from rfl, slenS_lanesOf h8, hpre, lanesOf_flatMap]
  (clear * -; omega)

theorem flatMap_rep32 :
    ∀ n : ℕ, (List.replicate n (Blk.one .fs 32)).flatMap lensB = List.replicate n 32
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatMap_cons, flatMap_rep32 n]; rfl

/-- **The run after a block's first entry**: `n` single 32-byte queries. -/
theorem lens_run_blk {j n : ℕ} {c : QClass} {len : ℕ} (hj : (blocks P20)[j]? = some (.one c len))
    (hr : ((blocks P20).drop (j + 1)).take n = List.replicate n (.one .fs 32)) :
    ((lens P20).drop (1 + (((blocks P20).take j).map bCnt).sum + 1)).take n = List.replicate n 32 := by
  rw [lens_split hj, ← length_flatMap_lensB, drop_mid, ← List.take_append_drop n ((blocks P20).drop (j + 1)),
    hr, List.flatMap_append, flatMap_rep32, List.take_left' (by simp)]

/-- **`PosLanesR` at `P20` through the extractor's blocks** (`js`: the block of each opening's first
positions entry). -/
def PosLanesK (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) (js : List ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens P20).length ∧ ((opens P20).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧
    1 + (((blocks P20).take (js.getD i 0)).map bCnt).sum = ((opens P20).getD (k0 + i) default).pe ∧
    ((blocks P20).drop (js.getD i 0 + 1)).take (nAns ((opens P20).getD (k0 + i) default) - 1) =
      List.replicate (nAns ((opens P20).getD (k0 + i) default) - 1) (.one .fs 32) ∧
    blkAns (blocks P20) (js.getD i 0) = some ((posLanes g ood Ls V).getD i 0 + 5)

theorem posLanesR_of_K {g : ℕ} {ood : Bool} {Ls : List Level} {V k0 : ℕ} {js : List ℕ} (h : PosLanesK g ood Ls V k0 js) :
    PosLanesR P20 g ood Ls V k0 := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h i hi
  obtain ⟨c, len, hj, -⟩ := blkAns_some h6
  refine ⟨h1, h2, h3, by (clear * - h4; omega), ?_, ?_⟩
  · rw [← h4]; exact lens_run_blk hj h5
  · rw [← h4, ansLane_blk h6]; (clear * -; omega)

/-- Walk `j` blocks: the entries and the lanes before block `j`, and the blocks from `j`. -/
def blkWalk : List Blk → ℕ → ℕ → ℕ → ℕ × ℕ × List Blk
  | bs, 0, c, l => (c, l, bs)
  | [], _ + 1, c, l => (c, l, [])
  | b :: bs, j + 1, c, l => blkWalk bs j (c + bCnt b) (l + b.lanes)

theorem blkWalk_eq : ∀ (bs : List Blk) (j c l : ℕ),
    blkWalk bs j c l = (c + ((bs.take j).map bCnt).sum, l + ((bs.take j).map Blk.lanes).sum, bs.drop j)
  | bs, 0, c, l => by simp [blkWalk]
  | [], _ + 1, c, l => by simp [blkWalk]
  | b :: bs, j + 1, c, l => by
    rw [blkWalk, blkWalk_eq bs j]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_succ_cons, Prod.mk.injEq,
      and_true]
    exact ⟨by omega, by omega⟩

/-- `blkAns` from the walk: the block at `j` is a single query, its answer lane is `A`. -/
def blkAnsW (pre : ℕ) (rest : List Blk) (A : ℕ) : Bool :=
  match rest with
  | .one _ len :: _ => 6 + pre + 1 + len / 8 == A
  | _ => false

theorem blkAns_of_W {bs : List Blk} {j A : ℕ}
    (h : blkAnsW ((bs.take j).map Blk.lanes).sum (bs.drop j) A = true) : blkAns bs j = some A := by
  unfold blkAns
  rw [← List.head?_drop]
  unfold blkAnsW at h
  split at h
  · rename_i c len r heq
    rw [heq]
    simp only [List.head?_cons, beq_iff_eq] at h ⊢
    rw [h]
  · cases h

/-- **`PosLanesK` as one Boolean**: each level's first positions block walked to once (`blkWalk`). -/
def posLanesKB (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) (js : List ℕ) : Bool :=
  (List.range Ls.length).all fun i =>
    let o := (opens P20).getD (k0 + i) default
    let w := blkWalk (blocks P20) (js.getD i 0) 0 0
    decide (k0 + i < (opens P20).length) && decide (o.L = Ls.getD i default) &&
    decide ((Ls.getD i default).height ≤ 64) && decide (1 + w.1 = o.pe) &&
    decide ((w.2.2.drop 1).take (nAns o - 1) = List.replicate (nAns o - 1) (.one .fs 32)) &&
    blkAnsW w.2.1 w.2.2 ((posLanes g ood Ls V).getD i 0 + 5)

theorem posLanesK_of_B {g : ℕ} {ood : Bool} {Ls : List Level} {V k0 : ℕ} {js : List ℕ} (h : posLanesKB g ood Ls V k0 js = true) :
    PosLanesK g ood Ls V k0 js := by
  intro i hi
  unfold posLanesKB at h
  have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, blkWalk_eq, Nat.zero_add, List.drop_drop] at hi'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hi'
  exact ⟨h1, h2, h3, h4, h5, blkAns_of_W h6⟩

end Dec
end Lvm.Fin
end
