-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 Z3 → RS0, L3β → RS0, E4 end; stage P4a
-- pass 5 (P4e)): 3.x's `trueL_zero`/`pendZ_pendBad` (`FRSoundnessFrBind`), `trueL_one`/`zfL_leaf`/
-- `pendLc_pendBad` (`FRSoundnessFrZM`) and `trueL_node` (`FRSoundnessFrLN`) at P4b's `trueL4`.
import FRSoundness4P4aDF
import FRSoundness4P4aT

/-!
# The pending Z and Lc claims into RS0 at revision 4.1

With the witness the unpacked `f⁽⁰⁾` of P4b's source (`WitOf`):

* **`trueL4_zero`**: RS claim 1's true value is `P^z(λ)` at Z1's point (the c-claim's true value),
  so **`pendZ4_pendBad4`**: Z's pending doom `PendZ` is RS0's `PendBad4` at claim 1 (binding `oZ`).
* **`trueL4_one`**: RS claim 2's true value is the kind-weighted `ẑ(r_k, r_blk)` (P4b's kind factor
  `kfT4`); **`zfL_eq4`**: a kind's true value `z̄̃_k(r_k)` on the cube.
* **`oLc4`**: claim 2's binding `v = v_β` (`finLc` (iii), every kind; 3.x's `oLcV`).
* A segment (`SegInd`: its indicator is `chain` everywhere): **`pendLc4_pendBad4`**.
* A node (**`KfInd`**: the kind factor is `Σ_i β^i Ind_{i+1}`, `finLc`'s `v_i` order): **`trueL4_node`**
  (claim 2's true value is the true batch), **`pendLcN4_pendBad4`**.
* **`pendF4a_pendBad4`**: phase 12's pending dooms (Z, Lc on both kinds, S2) are `PendBad4` from
  170 on; **`dF4a12_pendBad4`**: phase 12's doom is `BgA` or `PendBad4` (E4 end's `DPend4`, with
  P4b's `pendE4_pendBad4`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## RS claim 1 -/

theorem zZ_eq4 (zw : Wit) (ℓ : ℕ) (κ : CKind) (L es : Log) (σ : Fin 64) (u : Fin (2 ^ ℓ)) :
    zZ zw ℓ κ L es σ u = zw κ L es (σ.val + 64 * u.val) := by
  simp only [zZ, zBk, pAt]
  congr 1
  have := Nat.div_add_mod u.val 256
  norm_num
  omega

/-- (`rw`, not `rfl`: the kernel's `rfl` unfolds `eqZS` first, 1.1 s.) -/
theorem cwF_zero (lam : F) (xL xS : List F) (i : ℕ) :
    cwF lam xL xS 0 i = (eqZS lam (pinnedRho 0)).getD i 0 := by
  rw [cwF]

theorem cwF_one (lam : F) (xL xS : List F) (i : ℕ) :
    cwF lam xL xS 1 i = (eqTab xL.toArray).getD i 0 := by
  rw [cwF]

/-- RS claim 1's inner weight: the Lagrange weight of the low 6 bits times `eq(ρ₁, ·)` at bit 6. -/
theorem cwL4_zero (κ : CKind) (es : Log) {σ y : ℕ} (hσ : σ < 64) (hy : y < 2) :
    P4b.cwL4 κ es 0 (σ + 64 * y) = lagrangeWeight sNodeF (lamL es) ⟨σ, hσ⟩ *
      eqAtR (ptOf 1 [pinnedRho 0]) y := by
  rw [P4b.cwL4, cwF_zero, ← cwF_zero (fAt es 14 0) (xLL es) (xSL .N30 es)]
  exact cwL_zero .N30 es hσ hy

theorem zPtL_length4 (κ : CKind) (es : Log) : (zPtL κ.m es).length = κ.m - 7 := by
  have := κ.m_mem; simp only [zPtL, List.length_append, List.length_drop, List.length_ofFn,
    List.length_map, List.length_range]; omega

theorem zrL_drop4 (es : Log) : (zrL es).drop 1 = zPtL (kindOfC es).m es := by
  simp only [zrL, zPtL]
  rw [List.drop_append_of_le_length (by simp)]

/-- **RS claim 1's true value is `P^z(λ)` at Z1's point** (3.x's `trueL_zero`). -/
theorem trueL4_zero (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {zw : Wit} (hzw : WitOf R zw)
    (L es : Log) : P4b.trueL4 R kf (kindOfC es) L es 0 = (pzT zw L es).eval (lamL es) := by
  have hzd := zrL_drop4 es
  have hzw' := fun b => hzw L es b
  simp only [pzT, pzPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    skipExt_eval]
  revert hzw'
  generalize kindOfC es = κ at hzd ⊢
  intro hzw'
  have hm := κ.m_mem
  have hℓ : mC 6 κ = 1 + (κ.m - 7) := by unfold mC; omega
  set zr := zrL es
  set zP := zPtL κ.m es
  have hzP : zP.length = κ.m - 7 := zPtL_length4 κ es
  have hg : ∀ u : Fin (2 ^ (κ.m - 7)), P4b.gL4 kf κ es 0 u = eqAtR (ptOf (κ.m - 7) zP) u := by
    intro u
    have hl : (P4b.rsPtsL4 κ es).getD 0 [] = zP := by cases κ <;> rfl
    have h0 : (0 : ℕ) < (P4b.rsPtsL4 κ es).length := by
      rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num
    rw [P4b.gL4, Fin.val_zero, if_pos h0, if_neg (show (0 : ℕ) ≠ 1 by norm_num), mul_one, hl,
      eqPts_eq _ _ hzP (by simp [bitsL, hzP]), hzP, ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (κ.m - 7))),
      algebraMap F F (P4b.rsQ4 R L es (κ.m - 7) i u) = zw κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [P4b.rsQ4, hzw', Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  set lw : ℕ → F := fun σ => lagrangeWeight sNodeF (lamL es) ⟨σ % 64, Nat.mod_lt _ (by norm_num)⟩
  have hL : P4b.trueL4 R kf κ L es 0 = ∑ q ∈ range (2 ^ (κ.m - 7)), ∑ y ∈ range 2, ∑ σ ∈ range 64,
      lw σ * eqAtR (ptOf 1 [pinnedRho 0]) y * eqAtR (ptOf (κ.m - 7) zP) q *
        zw κ L es (σ + 64 * y + 2 ^ 7 * q) := by
    unfold P4b.trueL4
    simp only [hg, hq, mul_sum, Fin.val_zero]
    rw [sum_comm]
    rw [Fin.sum_univ_eq_sum_range (fun q => ∑ i : Fin 128, P4b.cwL4 κ es 0 i *
      (eqAtR (ptOf (κ.m - 7) zP) q * zw κ L es (i + 2 ^ 7 * q)))]
    refine sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => P4b.cwL4 κ es 0 i *
      (eqAtR (ptOf (κ.m - 7) zP) q * zw κ L es (i + 2 ^ 7 * q))), show (128 : ℕ) = 64 * 2 from rfl,
      sum_range_mul_split]
    refine sum_congr rfl fun y hy => sum_congr rfl fun σ hσ => ?_
    rw [mem_range] at hy hσ
    rw [cwL4_zero κ es hσ hy]
    simp only [lw, Nat.mod_eq_of_lt hσ]
    ring
  have hR : ∑ u : Fin (2 ^ mC 6 κ), eq (ptOf (mC 6 κ) zr) (cube u) *
      ∑ σ : Fin 64, lagrangeWeight (fun b : Fin 64 => skipNode (Fin.castLE (by norm_num) b))
        (lamL es) σ * zZ zw (mC 6 κ) κ L es σ u =
      ∑ u ∈ range (2 ^ (1 + (κ.m - 7))), eqAtR (ptOf (1 + (κ.m - 7)) zr) u *
        ∑ σ ∈ range 64, lw σ * zw κ L es (σ + 64 * u) := by
    rw [← hℓ, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf (mC 6 κ) zr) u *
      ∑ σ ∈ range 64, lw σ * zw κ L es (σ + 64 * u))]
    refine sum_congr rfl fun u _ => ?_
    rw [eq_cube_eqAtR, ← Fin.sum_univ_eq_sum_range (fun σ => lw σ * zw κ L es (σ + 64 * u))]
    refine congrArg _ (sum_congr rfl fun σ _ => ?_)
    rw [zZ_eq4]
    simp only [lw, Nat.mod_eq_of_lt σ.isLt]
    rfl
  rw [hR, sum_eqAtR_split, hL, hzd]
  refine sum_congr rfl fun q _ => ?_
  rw [pow_one]
  refine sum_congr rfl fun y _ => ?_
  have h1 : ptOf 1 zr = ptOf 1 [pinnedRho 0] := by
    funext l; fin_cases l; simp [ptOf, zr, zrL, List.getD_eq_getElem?_getD]
  rw [h1, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [show σ + 64 * y + 2 ^ 7 * q = σ + 64 * (y + 2 ^ 1 * q) by ring]
  ring_nf

/-- **Z's pending doom is RS0's `PendBad4` at claim 1** (binding `oZ`: the value is `P^z*(λ)`). -/
theorem pendZ4_pendBad4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F)
    {oLc oSh : CKind → Log → F → Prop} {zw : Wit} (hzw : WitOf R zw) {L es : Log}
    (h : PendZ zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ oLc oSh) L es :=
  ⟨0, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => h.2 (by
    have ho' : P4b.trueL4 R kf (kindOfC es) L es 0 = pzStar es := ho
    rw [← trueL4_zero R kf hzw, ho'])⟩

/-! ## RS claim 2 -/

theorem ptOf_rkL4 (es : Log) :
    ptOf 14 (xLL es ++ lcPtL (kindOfC es).m es) = ptOf 14 (rkL es) := by
  funext l
  fin_cases l <;> simp [ptOf, xLL, lcPtL, rkL, rchs, List.getD_eq_getElem?_getD,
    List.getElem?_append_left, List.getElem?_append_right]

theorem ptOf_rbLc4 (es : Log) :
    ptOf (qL (kindOfC es)) ((xLL es ++ lcPtL (kindOfC es).m es).drop 14) = rbLc es := by
  have hm := (kindOfC es).m_mem
  have hd : (xLL es ++ lcPtL (kindOfC es).m es).drop 14 =
      (List.range ((kindOfC es).m - 14)).map (fun l => rch 15 es (8 + l)) := by
    rw [lcPtL, ← List.append_assoc, List.drop_left' (by simp [xLL])]
  funext l
  have hl := l.isLt
  rw [hd]
  simp only [rbLc, ptOf, rZ, rchs, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show l.val < (kindOfC es).m - 14 by unfold qL at hl; omega),
    List.getElem?_range (show 8 + l.val < mC 6 (kindOfC es) by unfold mC qL at *; omega),
    Option.map_some, Option.getD_some]

/-- **RS claim 2's true value is the kind-weighted `ẑ(r_k, r_blk)`** (3.x's `trueL_one`; the weight
`kfT4` is a node's kind factor `kf ν β t`, a segment's `1`). -/
theorem trueL4_one (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {zw : Wit} (hzw : WitOf R zw)
    (L es : Log) : P4b.trueL4 R kf (kindOfC es) L es 1 =
    ∑ t ∈ range (2 ^ qL (kindOfC es)), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * P4b.kfT4 kf (kindOfC es) es t *
        zw (kindOfC es) L es (j + 2 ^ 14 * t) := by
  rw [← ptOf_rkL4, ← ptOf_rbLc4]
  have hzw' := fun b => hzw L es b
  revert hzw'
  generalize kindOfC es = κ
  intro hzw'
  have hm := κ.m_mem
  have hP0 : κ.m - 7 = qL κ + 7 := by unfold qL; omega
  set xL := xLL es
  set lP := lcPtL κ.m es
  have hxL : xL.length = 7 := by simp [xL, xLL]
  have hlP : lP.length = qL κ + 7 := by simp [lP, lcPtL, qL]; omega
  have hcw : ∀ i : Fin 128, P4b.cwL4 κ es ((1 : Fin 4) : ℕ) i = eqAtR (ptOf 7 xL) i := by
    intro i
    rw [P4b.cwL4, show ((1 : Fin 4) : ℕ) = 1 from rfl, cwF_one, show xLL es = xL from rfl]
    rw [eqTab_getD _ (by simp [hxL]), List.size_toArray, hxL, eqBits, bitSel,
      eqAtR, ← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun l _ => ?_
    simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hg : ∀ u : Fin (2 ^ (κ.m - 7)), P4b.gL4 kf κ es 1 u =
      eqAtR (ptOf (κ.m - 7) lP) u * P4b.kfT4 kf κ es (u.val / 2 ^ 7) := by
    intro u
    have hl : (P4b.rsPtsL4 κ es).getD 1 [] = lP := by cases κ <;> rfl
    have h1 : (1 : ℕ) < (P4b.rsPtsL4 κ es).length := by
      rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num
    have h1' : ((1 : Fin 4) : ℕ) = 1 := rfl
    rw [P4b.gL4, h1', if_pos h1, if_pos rfl, hl,
      eqPts_eq _ _ (hlP.trans hP0.symm) (by simp [bitsL, hlP, hP0]),
      hlP, ← hP0, ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (κ.m - 7))),
      algebraMap F F (P4b.rsQ4 R L es (κ.m - 7) i u) = zw κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [P4b.rsQ4, hzw', Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  set g : ℕ → F := fun b => P4b.kfT4 kf κ es (b / 2 ^ 14) * zw κ L es b with hgdef
  have step1 : P4b.trueL4 R kf κ L es 1 = ∑ u ∈ range (2 ^ (qL κ + 7)), ∑ i ∈ range (2 ^ 7),
      eqAtR (ptOf 7 xL) i * eqAtR (ptOf (qL κ + 7) lP) u * g (i + 2 ^ 7 * u) := by
    unfold P4b.trueL4
    simp only [hcw, hg, hq, mul_sum]
    rw [sum_comm, hP0, Finset.sum_range]
    refine sum_congr rfl fun y _ => ?_
    rw [Finset.sum_range]
    refine sum_congr rfl fun x _ => ?_
    have hx := x.isLt
    simp only [hgdef]
    rw [show (x.val + 2 ^ 7 * y.val) / 2 ^ 14 = y.val / 2 ^ 7 by omega]
    ring
  have hP7 : ptOf 7 (xL ++ lP) = ptOf 7 xL := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < xL.length by rw [hxL]; exact l.isLt)]
  have hPd : (xL ++ lP).drop 7 = lP := by rw [List.drop_left' hxL]
  have hR : ∀ P : List F, (∑ t ∈ range (2 ^ qL κ), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 P) j * eqAtR (ptOf (qL κ) (P.drop 14)) t * P4b.kfT4 kf κ es t *
        zw κ L es (j + 2 ^ 14 * t)) = ∑ t ∈ range (2 ^ qL κ), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 P) j * eqAtR (ptOf (qL κ) (P.drop 14)) t * g (j + 2 ^ 14 * t) := fun P =>
    sum_congr rfl fun t _ => sum_congr rfl fun j hj => by
      rw [mem_range] at hj
      simp only [hgdef]
      rw [show (j + 2 ^ 14 * t) / 2 ^ 14 = t by omega]
      ring
  rw [step1, hR, ← sum_eqAtR_split 14 (qL κ) g, show 14 + qL κ = 7 + (qL κ + 7) by omega,
    sum_eqAtR_split, hP7, hPd]

/-- Kind `k`'s true value `z̄̃_k(r_k)` as a sum on the cube (3.x's `zfL_eq`). -/
theorem zfL_eq4 (M : ZLM4) (zw : Wit) (L es : Log) (k : Fin 9) : zfL M zw L es k =
    ∑ t ∈ range (2 ^ qL (kindOfC es)), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * M.Ind (kindOfC es) k t *
        zw (kindOfC es) L es (j + 2 ^ 14 * t) := by
  unfold zfL zfoldK mle IndF
  simp only [eq_cube_eqAtR, zN, join, mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ j ∈ range (2 ^ 14), eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t * M.Ind (kindOfC es) k t * zw (kindOfC es) L es (j + 2 ^ 14 * t)),
    sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t.val * M.Ind (kindOfC es) k t.val *
        zw (kindOfC es) L es (j + 2 ^ 14 * t.val))]
  exact sum_congr rfl fun j _ => by rw [add_comm (2 ^ 14 * t.val)]; ring

/-- **Claim 2's binding** (every kind; 3.x's `oLcV`, `finLc` (iii)): `v = v_β`. -/
def oLc4 (_κ : CKind) (es : Log) (v : F) : Prop := v = vBetaL es

/-- **A segment's indicators are `chain` everywhere** (`zlm4`'s, `segInd_zlm4`). -/
def SegInd (M : ZLM4) : Prop := ∀ σ t, M.Ind (.seg σ) 0 t = 1

/-- **The kind factor is the node's indicators batched by `β`** (`finLc`'s `v_i` order: kind
`i + 1`). -/
def KfInd (M : ZLM4) (kf : Rev4.NodeKind → F → ℕ → F) : Prop :=
  ∀ ν β t, kf ν β t = ∑ i : Fin 8, β ^ i.val * M.Ind (.node ν) i.succ t

theorem segInd_zlm4 (indN : Rev4.NodeKind → Fin 9 → ℕ → F)
    (etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F) : SegInd (zlm4 indN etN) := fun _ _ => rfl

/-- On a segment, `z̄̃_chain(r_k)` is RS claim 2's true value. -/
theorem zfL_seg4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {M : ZLM4} (hS : SegInd M)
    {zw : Wit} (hzw : WitOf R zw) {L es : Log} (hn : (kindOfC es).isNode = false) :
    zfL M zw L es 0 = P4b.trueL4 R kf (kindOfC es) L es 1 := by
  rw [trueL4_one R kf hzw, zfL_eq4]
  obtain ⟨σ, hσ⟩ : ∃ σ, kindOfC es = .seg σ := by
    cases h : kindOfC es with
    | seg σ => exact ⟨σ, rfl⟩
    | node ν => rw [h] at hn; cases hn
  simp only [hσ, hS σ, P4b.kfT4]

/-- **A segment's pending Lc claim is RS0's `PendBad4` at claim 2** (`v_β`; 3.x's
`pendLc_pendBad`). -/
theorem pendLc4_pendBad4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F)
    {oZ' oSh : CKind → Log → F → Prop} {M : ZLM4} (hS : SegInd M) {zw : Wit} (hzw : WitOf R zw)
    {L es : Log} (h : PendLc M zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ' oLc4 oSh) L es := by
  obtain ⟨-, hn, hne⟩ := h
  refine ⟨1, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => hne ?_⟩
  have ho' : P4b.trueL4 R kf (kindOfC es) L es 1 = vBetaL es := ho
  have ht : ∑ i : Fin 8, fAt es 98 0 ^ i.val * tL M zw L es i = zfL M zw L es 0 := by
    rw [Fin.sum_univ_succ]; simp [tL]
  rw [ht, zfL_seg4 R kf hS hzw hn, ho']

/-- **RS claim 2's true value on a node is the true batch** `Σ_i β^i z̄̃_{i+1}(r_k)` (3.x's
`trueL_node`). -/
theorem trueL4_node (R : P4b.FSrc) {kf : Rev4.NodeKind → F → ℕ → F} {M : ZLM4} (hkf : KfInd M kf)
    {zw : Wit} (hzw : WitOf R zw) {L es : Log} (hn : (kindOfC es).isNode = true) :
    P4b.trueL4 R kf (kindOfC es) L es 1 = ∑ i : Fin 8, fAt es 98 0 ^ i.val * tNL M zw L es i := by
  obtain ⟨ν, hν⟩ : ∃ ν, kindOfC es = .node ν := by
    cases h : kindOfC es with
    | seg σ => rw [h] at hn; cases hn
    | node ν => exact ⟨ν, rfl⟩
  rw [trueL4_one R kf hzw]
  simp only [tNL, zfL_eq4, mul_sum]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have hk : P4b.kfT4 kf (kindOfC es) es t =
      ∑ i : Fin 8, fAt es 98 0 ^ i.val * M.Ind (kindOfC es) i.succ t := by
    rw [hν]; exact hkf ν _ t
  rw [hk, mul_sum, sum_mul]
  exact sum_congr rfl fun i _ => by ring

/-- **A node's pending Lc claim is RS0's `PendBad4` at claim 2** (through the kind factor). -/
theorem pendLcN4_pendBad4 (R : P4b.FSrc) {kf : Rev4.NodeKind → F → ℕ → F}
    {oZ' oSh : CKind → Log → F → Prop} {M : ZLM4} (hkf : KfInd M kf) {zw : Wit}
    (hzw : WitOf R zw) {L es : Log} (h : PendLcN M zw L es) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ' oLc4 oSh) L es := by
  obtain ⟨-, hn, hne⟩ := h
  refine ⟨1, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => hne ?_⟩
  have ho' : P4b.trueL4 R kf (kindOfC es) L es 1 = vBetaL es := ho
  rw [← ho', trueL4_node R hkf hzw hn]

/-! ## Phase 12's pending dooms are RS0's `PendBad4` -/

section Pend
variable (R : P4b.FSrc) {kf : Rev4.NodeKind → F → ℕ → F} {P : Front4a} {wNS : CKind → Log → F}

/-- **Phase 12's pending claims are false at RS0** (from 170): Z's, a segment's or a node's Lc,
S2's (3.x's four `okF_pend*` bridges without E's). -/
theorem pendF4a_pendBad4 (hS : SegInd P.M) (hkf : KfInd P.M kf) (hzw : WitOf R P.zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * P.wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) (hl : 170 ≤ es.length)
    (h : PendZ P.zw L es ∨ PendLc P.M P.zw L es ∨ PendLcN P.M P.zw L es ∨ D2S P.wN P.zw L es) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ oLc4 (oSh4 wNS)) L es := by
  rcases h with h | h | h | h
  · exact pendZ4_pendBad4 R kf hzw h
  · exact pendLc4_pendBad4 R kf hS hzw h
  · exact pendLcN4_pendBad4 R hkf hzw h
  · exact pendS4_pendBad4 R kf hzw hNS hL h hl

/-- **Phase 12's doom at E4 end** is the background or a false pending claim (E4 end's `DPend4`
with P4b's `pendE4_pendBad4` and the background's far and public parts). -/
theorem dF4a12_pendBad4 (hS : SegInd P.M) (hkf : KfInd P.M kf) (hzw : WitOf R P.zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * P.wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) (hl : 170 ≤ es.length)
    (h : DF4a P 12 L es) : P.BgA L es ∨ P4b.PendBad4 R kf (P4b.okRS4 oZ oLc4 (oSh4 wNS)) L es := by
  rcases h with (h | h | h | h) | h
  · exact .inl h
  all_goals refine .inr (pendF4a_pendBad4 R hS hkf hzw hNS hL hl ?_)
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end Pend

end FR.Snd.P4a
