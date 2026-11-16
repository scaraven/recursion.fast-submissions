/- `LvmXDecUdOff` (GOLF2 off-path move, group 18 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXDec, LvmXDecUd,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXDec
import LvmXDecUd
import LvmXDec1UdOff
import LvmMlListLemmas

-- ===== from `LvmXDec` =====

section
section
namespace Lvm.Nb
open Polynomial Finset
section Generic
variable {K : Type*} [Field K] {n : ℕ}

/-- The word of the evaluations of `p` at the points `x`. -/
def evalWord (x : Fin n → K) (p : K[X]) : Fin n → K := fun j => p.eval (x j)

end Generic
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Generic
variable {K : Type*} [Field K] {n : ℕ}

theorem evalWordL_apply (x : Fin n → K) (p : K[X]) : evalWordL x p = evalWord x p := rfl

end Generic
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Generic
variable {K : Type*} [Field K] {n : ℕ}

theorem mem_rsCode {x : Fin n → K} {k : ℕ} {w : Fin n → K} :
    w ∈ rsCode x k ↔ ∃ p : K[X], p.degree < k ∧ evalWord x p = w := by
  simp [rsCode, mem_degreeLT, evalWordL_apply]

theorem evalWord_mem_rsCode {x : Fin n → K} {k : ℕ} {p : K[X]} (hp : p.degree < k) :
    evalWord x p ∈ rsCode x k := mem_rsCode.2 ⟨p, hp, rfl⟩

end Generic
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Tensor
variable {R : Type*} [CommRing R]

/-- **The tensor identity** (BLUEPRINT §2.1, BP-C-M4), over any commutative ring:
`Σ_{x<2^ℓ} eq(r, x) ∏_{v ∈ bits x} w_v = ∏_{v<ℓ} (1 − r_v + r_v w_v)`. -/
theorem tensor_identity (r w : ℕ → R) (ℓ : ℕ) :
    ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * bitProd w ℓ x = ∏ v ∈ range ℓ, (1 - r v + r v * w v) := by
  induction ℓ with
  | zero => simp [eqBits, bitSel, bitProd]
  | succ ℓ ih =>
    rw [pow_succ, mul_two, sum_range_add, prod_range_succ, ← ih, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    simp only [eqBits, bitSel_succ_lo _ _ hx', bitSel_succ_hi _ _ hx', bitProd_succ_lo _ hx',
      bitProd_succ_hi _ hx']
    ring

end Tensor
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section NovelBasis
variable {L : Type*} [Field L]
variable {pt : ℕ → L} {N : ℕ}

/-- **Block-triangularity** (BLUEPRINT §2.1): `X_x(pt j) = 0` when bit `v` of `x` is set and
`j < 2^v`. -/
theorem novelX_eval_zero (pt : ℕ → L) {x v j : ℕ} (hb : x.testBit v = true) (hj : j < 2 ^ v) :
    (novelX pt x).eval (pt j) = 0 := by
  have hv : v < x := Nat.lt_two_pow_self.trans_le (Nat.ge_two_pow_of_testBit hb)
  rw [novelX, bitProd, bitSel, eval_prod]
  exact prod_eq_zero (mem_range.2 hv) (by simp only [hb, ite_true]; exact normW_eval_lt pt hj)

/-- Block-triangularity at the top bit: `X_x(pt j) = 0` for `j < 2^msb(x)`. -/
theorem novelX_eval_lt_msb (pt : ℕ → L) {x j : ℕ} (hx : x ≠ 0) (hj : j < 2 ^ x.log2) :
    (novelX pt x).eval (pt j) = 0 :=
  novelX_eval_zero pt (Nat.testBit_log2 hx) hj

/-- The tensor identity for the novel basis: `Σ_{x<2^ℓ} eq(r, x) X_x(y) =
∏_{v<ℓ} (1 − r_v + r_v Ŵ_v(y))`. -/
theorem novelX_tensor (pt : ℕ → L) (r : ℕ → L) (ℓ : ℕ) (y : L) :
    ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * (novelX pt x).eval y =
      ∏ v ∈ range ℓ, (1 - r v + r v * (normW pt v).eval y) := by
  rw [← tensor_identity]
  refine sum_congr rfl fun x hx => ?_
  rw [novelX_eq_bitProd pt (mem_range.1 hx), bitProd, bitSel, bitProd, bitSel, eval_prod]
  congr 1
  exact prod_congr rfl fun v _ => by split_ifs <;> simp

end NovelBasis
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Enc
variable {L M : Type*} [Field L] [Field M] [Algebra L M]

/-- `Enc_k` as an `M`-linear map. -/
noncomputable def encL (pt : ℕ → L) (n k : ℕ) : (Fin k → M) →ₗ[M] (Fin n → M) where
  toFun := enc pt n k
  map_add' c c' := by funext j; simp [enc, add_mul, sum_add_distrib]
  map_smul' a c := by funext j; simp [enc, mul_sum, mul_assoc]

/-- The code `C_M = Enc_k(M^k)` (`C_K` over `K`, `C_F` over `F`). -/
noncomputable def encCode (pt : ℕ → L) (n k : ℕ) : Submodule M (Fin n → M) :=
  LinearMap.range (encL (M := M) pt n k)

end Enc
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Enc
variable {L M : Type*} [Field L] [Field M] [Algebra L M]
variable {pt : ℕ → L} {N : ℕ}

theorem encPoly_add (pt : ℕ → L) {k : ℕ} (c c' : Fin k → M) :
    encPoly pt (c + c') = encPoly pt c + encPoly pt c' := by
  simp [encPoly, add_mul, sum_add_distrib]

theorem encPoly_single (pt : ℕ → L) {k : ℕ} (t : Fin k) (a : M) :
    encPoly pt (Pi.single t a) = C a * (novelX pt t).map (algebraMap L M) := by
  classical
  rw [encPoly, sum_eq_single t (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- Every polynomial of degree `< k ≤ 2^N` is `Σ_x c_x X_x`. -/
theorem exists_encPoly (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N) :
    ∀ d, d < k → ∀ p : M[X], p.natDegree ≤ d → ∃ c : Fin k → M, encPoly pt c = p := by
  intro d
  induction d with
  | zero =>
    intro h0 p hp
    refine ⟨Pi.single ⟨0, h0⟩ (p.coeff 0), ?_⟩
    rw [encPoly_single, eq_C_of_natDegree_le_zero hp]
    simp [novelX, bitProd, bitSel]
  | succ d ih =>
    intro hd p hp
    set t : Fin k := ⟨d + 1, hd⟩
    obtain ⟨hdeg, hlc⟩ := novelX_map (M := M) hpt (show d + 1 < 2 ^ N by omega)
    set Y := (novelX pt (d + 1)).map (algebraMap L M)
    set q := p - C (p.coeff (d + 1) / Y.leadingCoeff) * Y
    have hq : q.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      simp only [q, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (d + 1) i with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h),
          coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt h), mul_zero, sub_zero]
      · obtain rfl : i = d + 1 := by omega
        rw [show Y.coeff (d + 1) = Y.leadingCoeff by rw [leadingCoeff, hdeg],
          div_mul_cancel₀ _ hlc, sub_self]
    obtain ⟨c, hc⟩ := ih (by omega) q hq
    refine ⟨c + Pi.single t (p.coeff (d + 1) / Y.leadingCoeff), ?_⟩
    rw [encPoly_add, hc, encPoly_single]
    simp [q, Y, t]

/-- **`C_M = RS[M, pt, k]`**: the novel-basis code is the Reed–Solomon code on the points `pt j`
(for `k ≤ 2^N`). Distance, interpolation and the proximity lemmas therefore apply to it. -/
theorem encCode_eq_rsCode (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {n k : ℕ} (hk : k ≤ 2 ^ N) :
    encCode (M := M) pt n k = rsCode (fun j : Fin n => algebraMap L M (pt j)) k := by
  ext w
  rw [mem_rsCode]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨encPoly pt c, mem_degreeLT.1 (encPoly_mem hpt hk c),
      funext fun j => encPoly_eval pt n k c j⟩
  · rintro ⟨p, hp, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · obtain rfl : p = 0 := by simpa using hp
      exact ⟨0, funext fun j => by simp [evalWord, encL, enc]⟩
    obtain ⟨c, rfl⟩ := exists_encPoly hpt hk (k - 1) (by (clear * - hk0; omega)) p
      (natDegree_le_pred (natDegree_le_of_degree_le hp.le) (coeff_eq_zero_of_degree_lt hp))
    exact ⟨c, funext fun j => (encPoly_eval pt n k c j).symm⟩

end Enc
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Twin
variable {L : Type*} [Field L]
variable [CharP L 2] {pt : ℕ → L} {N : ℕ}
variable {M : Type*} [Field M] [Algebra L M]

/-- **The computable `Enc_{2^ℓ}`**: `Σ_x c_x ∏_{v ∈ bits x} Ŵ_v(pt j)` from the table. -/
def encTwin (pt : ℕ → L) (N ℓ : ℕ) {n : ℕ} (c : Fin (2 ^ ℓ) → M) (j : Fin n) : M :=
  ∑ x : Fin (2 ^ ℓ), c x * bitProd (fun v => algebraMap L M (wAt pt N v j)) ℓ x

/-- **The verifier's tensor weight** `∏_{v<ℓ} (1 − r_v + r_v Ŵ_v(pt j))` (`tensorW`, A.5). -/
def tensorTwin (pt : ℕ → L) (N ℓ : ℕ) (r : ℕ → M) (j : ℕ) : M :=
  ∏ v ∈ range ℓ, (1 - r v + r v * algebraMap L M (wAt pt N v j))

theorem bitProd_map {R S : Type*} [CommMonoid R] [CommMonoid S] (φ : R →* S) (f : ℕ → R)
    (ℓ x : ℕ) : φ (bitProd f ℓ x) = bitProd (fun v => φ (f v)) ℓ x := by
  simp only [bitProd, bitSel, map_prod]
  exact prod_congr rfl fun v _ => by split_ifs <;> simp

/-- `X_x(pt j)` from the table. -/
theorem novelX_eval_twin (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ x j : ℕ} (hℓ : ℓ ≤ N) (hx : x < 2 ^ ℓ)
    (hj : j < 2 ^ N) :
    algebraMap L M ((novelX pt x).eval (pt j)) =
      bitProd (fun v => algebraMap L M (wAt pt N v j)) ℓ x := by
  rw [novelX_eq_bitProd pt hx, bitProd, bitSel, eval_prod, map_prod, bitProd, bitSel]
  refine prod_congr rfl fun v hv => ?_
  split_ifs
  · rw [wAt_eq hadd hpt (by have := mem_range.1 hv; (clear * - hℓ this; omega)) hj]
  · simp

/-- **`encTwin_eq`**: the computable encoding is `Enc_{2^ℓ}` (`ℓ ≤ N`, `n ≤ 2^N`). -/
theorem encTwin_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ n : ℕ} (hℓ : ℓ ≤ N) (hn : n ≤ 2 ^ N)
    (c : Fin (2 ^ ℓ) → M) (j : Fin n) : encTwin pt N ℓ c j = enc pt n (2 ^ ℓ) c j := by
  refine sum_congr rfl fun x _ => ?_
  rw [novelX_eval_twin hadd hpt hℓ x.2 (j.2.trans_le hn)]

/-- **`tensorTwin_eq`** (the tensor identity, computed): `tensorTwin = Σ_x eq(r, x) X_x(pt j)`. -/
theorem tensorTwin_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ j : ℕ} (hℓ : ℓ ≤ N) (hj : j < 2 ^ N) (r : ℕ → M) :
    tensorTwin pt N ℓ r j =
      ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * algebraMap L M ((novelX pt x).eval (pt j)) := by
  rw [tensorTwin, ← tensor_identity]
  exact sum_congr rfl fun x hx => by rw [novelX_eval_twin hadd hpt hℓ (mem_range.1 hx) hj]

end Twin
end Lvm.Nb
end
end

section
section
namespace Lvm.Nb
open Polynomial Finset
section Bfly
variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- From offset `0`, the iteration is `coeffsOfValues`. -/
theorem bflyRun_coeffs (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) (i : Fin (2 ^ ℓ)) :
    bflyRun pt N 0 ℓ y i = coeffsOfValues pt N ℓ y i :=
  bflyRun_eq pt N 0 ℓ y i.2

end Bfly
end Lvm.Nb
end
end

section
namespace Lvm.X
open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

/-- **Correctness in the unique-decoding regime**: the closeness hypothesis at WP-6's
threshold `udThr 13 2 = 20480` (`δ₀ = 3/8` of the `2^15` positions may disagree). -/
theorem decodeRec_correct_ud (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (msg : ℕ → BF64)
    (hclose : LeanVM.Protocol.Whir.udThr 13 2 ≤ (closeSet wd msg).card)
    (hf : ∀ v < 2 ^ 13, f₁ v = ∑ l ∈ range 64, eqA α l * ofK (msg (l * 2 ^ 13 + v)))
    (hluck : ∀ q < 2 ^ 15, foldAt α wd q = enc0 f₁ q → ∀ l < 64, rowW wd l q = cwRec msg l q) :
    decodeRec wd α f₁ = some ((List.range (2 ^ 19)).map msg) :=
  decodeRec_correct wd α f₁ msg
    (le_trans (by norm_num [LeanVM.Protocol.Whir.udThr]) hclose) hf hluck

end Lvm.X
end

-- ===== from `LvmXDecUd` =====

section
section
namespace Lvm.X
open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

theorem ptK_eq_ofBits (n : ℕ) : ptK n = LeanVM.Parameters.K.ofBits n := rfl

end Lvm.X
end
end

section
section
namespace Lvm.X
open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

/-- **`Enc₀` is leanVM's `enc 13 2`** on the message `u ↦ f₁ ⟨u⟩`. -/
theorem enc0_eq_enc (f₁ : ℕ → Ext3) (q : Fin (2 ^ (13 + 2))) :
    enc0 f₁ q = LeanVM.Protocol.Whir.enc 13 2 (fun u => f₁ (LeanVM.Protocol.Whir.bitsToNat u)) q := by
  rw [LeanVM.Protocol.Whir.enc_apply, enc0,
    ← sum_cube 13 (fun v => f₁ v * ofK (nbAt v q))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((LeanVM.Protocol.Whir.bitsToNat_lt u).trans (by norm_num)), ofK_eq]

/-- **`Enc₀` is the IOP program's `encRes`** (WP-7's direct final check) on the residual list. -/
theorem enc0_eq_encRes (residual : List Ext3) {q : ℕ} (hq : q < 2 ^ 15) :
    enc0 (fun v => residual.getD v 0) q =
      LeanVM.Protocol.Verifier.encRes 13 2 residual q := by
  rw [LeanVM.Protocol.Verifier.encRes, dif_pos hq]
  exact enc0_eq_enc (fun v => residual.getD v 0) ⟨q, hq⟩

/-- **Row `l` of `cwRec msg` is leanVM's `encK 13 2`** of the row's message. -/
theorem cwRec_eq_encK (msg : ℕ → BF64) (l : ℕ) (q : Fin (2 ^ (13 + 2))) :
    cwRec msg l q =
      LeanVM.Protocol.Whir.encK 13 2 (fun u => msg (l * 2 ^ 13 + LeanVM.Protocol.Whir.bitsToNat u)) q := by
  rw [LeanVM.Protocol.Whir.encK, cwRec,
    ← sum_cube 13 (fun v => msg (l * 2 ^ 13 + v) * nbAt v q)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((LeanVM.Protocol.Whir.bitsToNat_lt u).trans (by norm_num))]

end Lvm.X
end
end

section
namespace Lvm.X
open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-- **The decoder returns the unique candidate's message** (BLUEPRINT §6.2, from WP-7's
`ud_extract_rec20_l0`): not doomed after the commitment and after the residual, and not lucky. -/
theorem decodeRec_of_ud (Good : Column 19 → Prop) (W : Compile.Word) (α : Fin laneBits → E)
    (f : (Fin (19 - laneBits) → Bool) → E) (hW : ∀ v < 2 ^ 15, (W v).length = 64)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W)
    (hF : ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W, q' = q) ∧
      (¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q) →
        decodeRec (wdOf W) (alphaN α) (fNr f) = some ((List.range (2 ^ 19)).map (msgOf q))) := by
  obtain ⟨q, hq, hG, huniq, hf, hcard, hluck⟩ := ud_extract_rec20_l0 Good W α f hC hF
  refine ⟨q, hq, hG, huniq, fun hL => ?_⟩
  have hfx : ∀ x : Fin (2 ^ (19 - laneBits + 2)),
      x ∈ agreeSet (laneRows 19 2 W) (encRows 19 2 q) ↔
        ∀ l < 64, rowW (wdOf W) l x = cwRec (msgOf q) l x := by
    intro x
    rw [mem_agreeSet]
    constructor
    · intro h l hl
      have := h ((bitsEquiv laneBits).symm ⟨l, hl⟩)
      rw [laneRows_eq W hW, encRows_eq] at this
      have hb : bitsToNat ((bitsEquiv laneBits).symm ⟨l, hl⟩) = l := by
        rw [← bitsEquiv_val, Equiv.apply_symm_apply]
      rw [hb] at this
      exact (algebraMap BF64 Ext3).injective this
    · intro h u
      rw [laneRows_eq W hW, encRows_eq, h _ (bitsToNat_lt u)]
  refine decodeRec_correct_ud (wdOf W) (alphaN α) (fNr f) (msgOf q) ?_ ?_ ?_
  · -- closeness: the agreement set maps into `closeSet`
    refine hcard.trans (le_of_le_of_eq (Finset.card_le_card_of_injOn (fun x => (x : ℕ)) ?_
      (fun a _ b _ h => Fin.ext h)) rfl)
    intro x hx
    have hx' := (hfx x).1 hx
    simp only [Finset.coe_filter, closeSet, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨lt15 x rfl, hx'⟩
  · intro v hv
    rw [hf]; exact fN_foldMsg α q hv
  · intro x hx hfold l hl
    have hmem : (⟨x, hx.trans_le (by norm_num)⟩ : Fin (2 ^ (19 - laneBits + 2))) ∈
        agreeSet (foldAll α (laneRows 19 2 W)) (fun _ ↦ enc (19 - laneBits) 2 f) := by
      rw [mem_agreeSet]
      intro r
      rw [foldAll_laneRows_eq W hW, enc_fN]
      exact hfold
    rw [hluck hL] at hmem
    exact (hfx _).1 hmem l hl

/-- `decodeRec_of_ud` for a well-shaped word (`wordOf`'s rows have `64` words, `wellShaped_wordOf`). -/
theorem decodeRec_of_ud_ws (Good : Column 19 → Prop) (W : Compile.Word) (α : Fin laneBits → E)
    (f : (Fin (19 - laneBits) → Bool) → E) (hW : WellShaped 64 W)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W)
    (hF : ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W, q' = q) ∧
      (¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q) →
        decodeRec (wdOf W) (alphaN α) (fNr f) = some ((List.range (2 ^ 19)).map (msgOf q))) :=
  decodeRec_of_ud Good W α f (fun v _ => hW v) hC hF

end Lvm.X
end
