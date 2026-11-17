-- lvm2 X-REC2 (helper XA). The byte-level and O12 bridges of O5c that need no certificate module,
-- moved out of WP-14d's `LvmCertSExqCodec` (unchanged: `kOfBytes_eq`, `eOfBytes_eq`, `chalOf_eq_alphaE`,
-- `alphaE_zero`, `xDescend_eq`, `readRow_eq_wordOf`), and their level-1 analogues for `C_rec`'s second
-- WHIR level (lvm2 S4): `f2E_eq`, `readRow1_eq_wordOf`, `readWd1_eq_wdOf`, `capRec1_eq`.
import LvmCompileCodec
import LvmXSpec
import LvmXDecUd

-- (GOLF2: 6 declarations that `certified` does not use moved verbatim to `LvmXSChildOff`, outside its import closure.)

/-!
# The certificate-free bridges of O5c

* `kOfBytes_eq`: `kOfBytes b = decLE (b.take 8)`; `eOfBytes_eq`, **`chalOf_eq_alphaE`**,
  **`f2E_eq`** (π's `f₂` coefficient `v` is `eOfBytes` of its 24 bytes at `f2Off + 24 v`);
* **`readRow_eq_wordOf`** (O12): XD's `readRow L cap p` is WP-5's `S.wordOf L ⟨15, 64, 7, cap⟩ p`
  for every scheme with `decK = kOfBytes` whose `C_rec` leaves carry the reader's `crOcc` words (`occ`);
  **`readRow1_eq_wordOf`**: DEC's level-1 `readRow1 L cap p`
  is `S.wordOf L ⟨12, 48, 7, cap⟩ p`, and `readWd1_eq_wdOf`: the decoder's word is `wdOf` of it;
* **`capRec1_eq`**: the 128 digests of π's 4096 bytes at `capRec1Off` are `capRec1 π`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes

/-! ## Bytes -/

theorem get!_eq_getD (π : ByteArray) (k : ℕ) : π.get! k = π.data.toList.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  first
    | rfl
    | (simp only [ByteArray.get!]; rfl)
    | (cases π; simp only [ByteArray.get!, getElem!_def]; split <;> simp_all <;> rfl)

theorem sum_fin_ofLE : ∀ (n : ℕ) (b : List UInt8),
    ∑ i : Fin n, (b.getD i 0).toNat * 256 ^ (i : ℕ) = ofLE (b.take n)
  | 0, b => by simp [ofLE]
  | n + 1, [] => by simp [ofLE]
  | n + 1, d :: ds => by
    rw [Fin.sum_univ_succ, List.take_succ_cons, ofLE_cons, ← sum_fin_ofLE n ds, Finset.mul_sum]
    simp only [Fin.val_zero, List.getD_cons_zero, pow_zero, mul_one, Fin.val_succ,
      List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem ofLE_take8_lt (b : List UInt8) : ofLE (b.take 8) < 2 ^ 64 :=
  (ofLE_lt _).trans_le (by
    rw [show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by simp))

/-- **WP-5's word decoder is XD's** on the first eight bytes. -/
theorem kOfBytes_eq (b : List UInt8) : kOfBytes b = Lvm.X.decLE (b.take 8) := by
  unfold kOfBytes Lvm.X.decLE
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofFin, Fin.coe_cast, finFunctionFinEquiv_apply, toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (ofLE_take8_lt b), ← sum_fin_ofLE 8 b]
  rfl

theorem mkE_ofFn (f : Fin BF64.ext3Params.d → BF64) :
    (CompPoly.Extension.Ext.equivFn BF64.ext3Params).symm f =
      Lvm.X.mkE (f ⟨0, by decide⟩) (f ⟨1, by decide⟩) (f ⟨2, by decide⟩) := by
  apply CompPoly.Extension.Ext.coeffs_injective
  apply Vector.ext
  intro i hi
  have hi3 : i < 3 := hi
  interval_cases i <;> rfl

/-- **WP-5's scalar decoder** in XD's limbs. -/
theorem eOfBytes_eq (b : List UInt8) : eOfBytes b = Lvm.X.mkE (Lvm.X.decLE (b.take 8))
    (Lvm.X.decLE ((b.drop 8).take 8)) (Lvm.X.decLE ((b.drop 16).take 8)) := by
  unfold eOfBytes
  rw [mkE_ofFn]
  simp only [kOfBytes_eq, mul_zero, mul_one, List.drop_zero]

/-- `wK` of a packed word of a byte string is XD's decoder of its eight bytes. -/
theorem wK_packBytes (l : List UInt8) {j : ℕ} (hj : 8 * j < l.length) :
    Lvm.X.wK ((packBytes l).getD j 0) = Lvm.X.decLE ((l.drop (8 * j)).take 8) := by
  rw [Lvm.X.packBytes_getDX, if_pos hj]
  rfl

/-- **The codec of a fold challenge** (bridge (a)): WP-5's `chalOf` is WP-13a's `alphaE`. -/
theorem chalOf_eq_alphaE (a : Digest) : chalOf a = Lvm.X.alphaE a := by
  have hl : a.toList.length = 32 := by simp
  rw [chalOf, eOfBytes_eq, Lvm.X.alphaE, Lvm.X.dw, Lvm.X.dw, Lvm.X.dw,
    wK_packBytes _ (by omega), wK_packBytes _ (by omega), wK_packBytes _ (by omega)]
  simp

/-! ## O12: the column reading is WP-5's first-preimage word -/

theorem xDescend_eq (L : Log) : ∀ (n : ℕ) (v : Digest) (q : ℕ),
    Lvm.X.xDescend L n v q = Scheme.descend L n v q
  | 0, _, _ => rfl
  | n + 1, v, q => by
    simp only [Lvm.X.xDescend, Scheme.descend, xDescend_eq L n]
    rfl

end Lvm.ASM
