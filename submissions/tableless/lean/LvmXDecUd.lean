-- WP-13b: the decoder's correctness from WP-7's extraction facts (`LvmWhirDoom.ud_extract_rec20_l0`); new.
import LvmWhirDoom
import LvmXDec
import LvmNovelBasis
import LvmWhirProg

-- (GOLF2: 6 declarations that `certified` does not use moved verbatim to `LvmXDecUdOff`, outside its import closure.)

-- ===== merged from `LvmXDecLv` (GOLF module merge: `LvmXDecLv.lean` is now a stub importing `LvmXDecUd`) =====
section
-- WP-13b: the decoder's encoder is leanVM's, as WP-7 ports it (`LvmNovelBasis`: `novelAt`, `enc`,
-- `encK`, `bitsToNat`, `bitsEquiv`; `LvmWhirProg`: `encRes`), which are canonical; the equalities are new.

/-!
# `Enc₀` and `cwRec` are leanVM's `enc` and `encK` at `κ = 13`, `R = 2`

* `ptK_eq_ofBits`, `ofK_eq`: lvm's `ptK`, `ofK` are leanVM's `K.ofBits`, `ofK`.
* `nbAt_eq_novelAt`: `X_v(x_q)` (FR's `novelX` at `ptK`) is leanVM's `novelAt v (K.ofBits q)`
  (`v < 2^64`): the same product of normalised subspace polynomials.
* **`enc0_eq_enc`**: `enc0 f₁ q = enc 13 2 g q` for `g u = f₁ ⟨u⟩` (`⟨u⟩ = bitsToNat u`, bit 0 first);
  **`enc0_eq_encRes`**: the IOP program's `encRes 13 2 residual q` (WP-7, the direct final check).
* **`cwRec_eq_encK`**: row `l` of `cwRec msg` is `encK 13 2` of the row's message.
-/

namespace Lvm.X

open Polynomial Finset Lvm.Nb CompPoly.Extension BF64

theorem ofK_eq (a : BF64) : ofK a = LeanVM.Parameters.ofK a := by
  rw [ofK, Ext.algebraMap_eq_ofBase]

theorem sub_eq_add_K (a b : BF64) : a - b = a + b := by
  rw [sub_eq_add_neg, CharTwo.neg_eq]

/-- `Ŵ_i(a)` here is leanVM's. -/
theorem normW_eval_eq (i : ℕ) (a : BF64) :
    (normW ptK i).eval a = LeanVM.Protocol.Whir.normVanishingAt i a := by
  rw [normW, eval_mul, eval_C, eval_subW, eval_subW, LeanVM.Protocol.Whir.normVanishingAt,
    LeanVM.Protocol.Whir.vanishingAt, LeanVM.Protocol.Whir.vanishingAt,
    LeanVM.Protocol.Whir.basisVec, mul_comm]
  simp only [sub_eq_add_K]
  rfl

/-- **`X_v(x_q)` is leanVM's `novelAt v (K.ofBits q)`** (`v < 2^64`). -/
theorem nbAt_eq_novelAt {v : ℕ} (hv : v < 2 ^ 64) (q : ℕ) :
    nbAt v q = LeanVM.Protocol.Whir.novelAt v (LeanVM.Parameters.K.ofBits q) := by
  rw [nbAt, novelX_eq_bitProd ptK hv, bitProd, bitSel, eval_prod, LeanVM.Protocol.Whir.novelAt]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact normW_eval_eq i _
  · simp

/-- A sum over cube points is a sum over `range (2^κ)`. -/
theorem sum_cube {M : Type*} [AddCommMonoid M] (κ : ℕ) (F : ℕ → M) :
    ∑ u : Fin κ → Bool, F (LeanVM.Protocol.Whir.bitsToNat u) = ∑ j ∈ range (2 ^ κ), F j := by
  rw [← Fin.sum_univ_eq_sum_range, ← (LeanVM.Protocol.Whir.bitsEquiv κ).sum_comp]
  exact Finset.sum_congr rfl fun u _ => by rw [LeanVM.Protocol.Whir.bitsEquiv_val]

end Lvm.X
end
-- ===== end of `LvmXDecLv` =====

/-!
# The decoder returns the unique candidate's message

WP-7's `ud_extract_rec20_l0`: for a committed word `W` of `C_rec` (`μ = 19`, `R = 2`, threshold
`udThr 13 2`), the fold challenges `α ∈ E^6` and the final residual `f`, if neither the commitment
nor the residual is doomed, there is exactly one candidate `q` (a `K`-valued stack whose lane-wise
encoding agrees with `W` on `≥ thr` columns), it is good, `f = foldMsg α q`, and off the luck
event the agreement set of the folded word with `Enc(f)` is the word's agreement set with `q`.

**`decodeRec_of_ud`**: then, off the luck event for that `q`, the pure decoder on the word's leaf
words (`wdOf W`), the challenges (`alphaN α`) and the residual's coefficients (`fNr f`) returns
`q`'s `2^19` words. The leaves are assumed to have 64 words (`wordOf`'s rows are well shaped).

The bridges: `eqW_eq_eqA` (the fold weights), `laneRows_eq` (lane `u` is leaf word `63 − ⟨u⟩`),
`encRows_eq` (`q`'s lane encoding is `cwRec` of its words), `foldAll_laneRows_eq` (the fold is
`foldAt`), `enc_fN` (`Enc(f)` is `enc0 (fNr f)`), `fN_foldMsg` (the residual is the fold of `q`'s
words).
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-! ## The decoder's inputs from WP-7's objects -/

/-- The decoder's word: leaf word `t` at position `q` of the committed word (`0` past the leaf). -/
def wdOf (W : Compile.Word) (q t : ℕ) : BF64 := (W q).getD t 0

/-- The fold challenges, `ℕ`-indexed. -/
def alphaN (α : Fin laneBits → E) (i : ℕ) : Ext3 := if h : i < 6 then α ⟨i, h⟩ else 0

/-- The residual's coefficients, `ℕ`-indexed (`v ↦ f(bits v)`). -/
def fNr (f : (Fin (19 - laneBits) → Bool) → E) (v : ℕ) : Ext3 :=
  if h : v < 2 ^ 13 then f ((bitsEquiv 13).symm ⟨v, h⟩) else 0

/-- A stack's `2^19` words. -/
def msgOf (q : Column 19) (i : ℕ) : BF64 := q.values.getD i 0

/-! ## The bridges -/

theorem bitsEquiv_symm_bitsToNat {κ : ℕ} (u : Fin κ → Bool) :
    (bitsEquiv κ).symm ⟨bitsToNat u, bitsToNat_lt u⟩ = u := by
  apply (bitsEquiv κ).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (bitsEquiv_val u).symm

theorem cube_sum64 {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ u : Fin laneBits → Bool, F (bitsToNat u) = ∑ l ∈ range 64, F l := sum_cube 6 F

theorem lt15 {n : ℕ} (x : Fin (2 ^ (19 - laneBits + 2))) (h : n = x) : n < 2 ^ 15 :=
  h ▸ x.isLt.trans_le (by norm_num)

/-- **The fold weights**: `eqW α u = eq(α, ⟨u⟩)`. -/
theorem eqW_eq_eqA (α : Fin laneBits → E) (u : Fin laneBits → Bool) :
    eqW α u = eqA (alphaN α) (bitsToNat u) := by
  rw [eqW, eqA, eqBits, bitSel, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [testBit_bitsToNat u i]
  simp [alphaN, i.isLt]

theorem getD_reverse64 {L : List BF64} (hL : L.length = 64) {l : ℕ} (hl : l < 64) :
    L.reverse.getD l 0 = L.getD (63 - l) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [hL]; omega), List.getD_eq_getElem _ _ (by omega),
    List.getElem_reverse]
  congr 1; omega

/-- **Lane `u` is leaf word `63 − ⟨u⟩`.** -/
theorem laneRows_eq (W : Compile.Word) (hW : ∀ v < 2 ^ 15, (W v).length = 64)
    (u : Fin laneBits → Bool) (x : Fin (2 ^ (19 - laneBits + 2))) :
    laneRows 19 2 W u x = ofK (rowW (wdOf W) (bitsToNat u) x) := by
  rw [laneRows, laneWord, laneOf, bitsEquiv_val, rowW, wdOf, ofK_eq,
    getD_reverse64 (hW x (lt15 x rfl)) (bitsToNat_lt u)]

/-- **`q`'s lane encoding is `cwRec` of its words.** -/
theorem encRows_eq (q : Column 19) (u : Fin laneBits → Bool) (x : Fin (2 ^ (19 - laneBits + 2))) :
    encRows 19 2 q u x = ofK (cwRec (msgOf q) (bitsToNat u) x) := by
  have hx : (x : ℕ) < 2 ^ 15 := lt15 x rfl
  rw [encRows, enc_apply, cwRec, Lvm.X.ofK, map_sum,
    ← sum_cube 13 (fun v => algebraMap BF64 Ext3 (msgOf q (bitsToNat u * 2 ^ 13 + v) * nbAt v x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [blockOf, bitsEquiv_val, map_mul, nbAt_eq_novelAt ((bitsToNat_lt y).trans (by norm_num)),
    ← Lvm.X.ofK, ← Lvm.X.ofK, ofK_eq, ofK_eq, msgOf]
  have e : bitsToNat y + 2 ^ (19 - laneBits) * bitsToNat u = bitsToNat u * 2 ^ 13 + bitsToNat y := by
    rw [show (2 : ℕ) ^ (19 - laneBits) = 2 ^ 13 from rfl]; ring
  rw [e]

/-- **The fold of the lanes is `foldAt`.** -/
theorem foldAll_laneRows_eq (W : Compile.Word) (hW : ∀ v < 2 ^ 15, (W v).length = 64)
    (α : Fin laneBits → E) (r : Fin 0 → Bool) (x : Fin (2 ^ (19 - laneBits + 2))) :
    foldAll α (laneRows 19 2 W) r x = foldAt (alphaN α) (wdOf W) x := by
  rw [foldAll_eq_sum, foldAt, ← cube_sum64 (fun l => eqA (alphaN α) l * ofK (rowW (wdOf W) l x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [laneRows_eq W hW, eqW_eq_eqA]

/-- **`Enc(f)` is `Enc₀` of the coefficients.** -/
theorem enc_fN (f : (Fin (19 - laneBits) → Bool) → E) (x : Fin (2 ^ (19 - laneBits + 2))) :
    enc (19 - laneBits) 2 f x = enc0 (fNr f) x := by
  rw [enc_apply, enc0, ← sum_cube 13 (fun v => fNr f v * ofK (nbAt v x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((bitsToNat_lt u).trans (by norm_num)), ofK_eq]
  unfold fNr
  split
  · rename_i h
    congr 1
    exact congrArg f (bitsEquiv_symm_bitsToNat u).symm
  · rename_i h
    exact absurd (bitsToNat_lt u) h

/-- **The residual is the fold of `q`'s words.** -/
theorem fN_foldMsg (α : Fin laneBits → E) (q : Column 19) {v : ℕ} (hv : v < 2 ^ 13) :
    fNr (foldMsg α q) v = ∑ l ∈ range 64, eqA (alphaN α) l * ofK (msgOf q (l * 2 ^ 13 + v)) := by
  rw [fNr, dif_pos hv, foldMsg, Finset.sum_apply]
  rw [← cube_sum64 (fun l => eqA (alphaN α) l * ofK (msgOf q (l * 2 ^ 13 + v)))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, eqW_eq_eqA, blockOf, bitsEquiv_val, msgOf, ofK_eq]
  have h : bitsToNat ((bitsEquiv 13).symm ⟨v, hv⟩) = v := by
    rw [← bitsEquiv_val, Equiv.apply_symm_apply]
  have e : bitsToNat ((bitsEquiv 13).symm ⟨v, hv⟩) + 2 ^ (19 - laneBits) * bitsToNat u =
      bitsToNat u * 2 ^ 13 + v := by
    rw [h, show (2 : ℕ) ^ (19 - laneBits) = 2 ^ 13 from rfl]; ring
  rw [e]

/-! ## The theorem -/

/-- A candidate at threshold `A` agrees with the word's lanes on at least `A` columns (`ud_extract`'s
argument, without uniqueness; generic in `μ`, `R`: at the concrete code the unifier recurses too deep). -/
theorem card_agreeSet_of_candidate {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64) {W : Compile.Word}
    {q : Column μ} (hq : q ∈ Candidates μ R A W) :
    A ≤ (agreeSet (laneRows μ R W) (encRows μ R q)).card := by
  classical
  have hmem : encRows μ R q ∈ iList (Whir.rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
      (laneRows μ R W) := by
    rw [LeanVM.Protocol.Whir.Sound.encRows_eq]
    exact comp_mem_iList _ (bitsEquiv laneBits) (mem_iList_of_candidate h64 hq)
  exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2

/-- **The level-0 decoder returns any list member's message** (lvm2 J2′, J2C-DES T8a): for a candidate `q` of
the root word `W` at a threshold `A ≥ 2^13`, not lucky in the six level-0 fold rounds, the decoder on `W`,
`α` and `q`'s fold returns `q`'s message. -/
theorem decodeRec_of_mem (W : Compile.Word) (α : Fin laneBits → E) (q : Column 19) {A : ℕ}
    (hW : ∀ v < 2 ^ 15, (W v).length = 64) (hq : q ∈ Candidates 19 2 A W) (hA : 2 ^ 13 ≤ A)
    (hL : ¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q)) :
    decodeRec (wdOf W) (alphaN α) (fNr (foldMsg α q)) = some ((List.range (2 ^ 19)).map (msgOf q)) := by
  classical
  have h64 : 19 - laneBits + 2 ≤ 64 := by norm_num
  have hcard := card_agreeSet_of_candidate h64 hq
  have hluck : agreeSet (foldAll α (laneRows 19 2 W)) (fun _ ↦ enc (19 - laneBits) 2 (foldMsg α q)) =
      agreeSet (laneRows 19 2 W) (encRows 19 2 q) := by
    rw [← foldAll_encRows]; exact agreeSet_foldAll_eq (not_not.mp hL)
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
  refine decodeRec_correct (wdOf W) (alphaN α) (fNr (foldMsg α q)) (msgOf q) ?_ ?_ ?_
  · -- closeness: the agreement set maps into `closeSet`
    refine hA.trans (hcard.trans (le_of_le_of_eq (Finset.card_le_card_of_injOn (fun x => (x : ℕ)) ?_
      (fun a _ b _ h => Fin.ext h)) rfl))
    intro x hx
    have hx' := (hfx x).1 hx
    simp only [Finset.coe_filter, closeSet, Set.mem_setOf_eq, Finset.mem_range]
    exact ⟨lt15 x rfl, hx'⟩
  · intro v hv
    exact fN_foldMsg α q hv
  · intro x hx hfold l hl
    have hmem' : (⟨x, hx.trans_le (by norm_num)⟩ : Fin (2 ^ (19 - laneBits + 2))) ∈
        agreeSet (foldAll α (laneRows 19 2 W)) (fun _ ↦ enc (19 - laneBits) 2 (foldMsg α q)) := by
      rw [mem_agreeSet]
      intro r
      rw [foldAll_laneRows_eq W hW, enc_fN]
      exact hfold
    rw [hluck] at hmem'
    exact (hfx _).1 hmem' l hl

end Lvm.X
