-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8/A.9 on a node, A.10 S2; stage S-CN4): the node
-- ops' specifications against P4e's weights (`FRSoundness4P4aNS`: `wNode4`, `wNS4`; P4c's `peL`).
import FRSoundness4P4aNS
import FRSoundness4P4aFin
import FRNodeTarget4

/-!
# The node ops' specifications are P4e's weights (closes P4e's D11)

* **`final_node4`** (the MLE lemma of `finSh` (ii)): the node's S2 weight `wNode4` (P4e) has
  extension at `(r_blk, r_pos)`
  `E·slotW₀ + (Sh + κ_s E₀)·slotW₂ + Σ_f κ_s^(f+2) W_f`, with `(E, Sh, E₀)` the components of
  `shiftMask4S` (`lkE`, `lkSh`, `lkE0`), `slotW` 3.x's `slotWS` at the node's slot maps 0 and 2, and
  `W_f = linkW4S` (`sum_lkW4`, `sum_shN4`, `sum_famW4'`).
* **`wSumNode4 ν es`**: that value on the log, as `finSh` (ii) computes it under the
  specifications (`relSh4`'s `w_out + w_in` with `shiftMask4S` on the 18-entry padded `τ`, `r_blk`,
  `linkWAll4S` on `τ ‖ θ`, `r_blk ‖ r_pos`, `linkSum`). **`wNS4_node4`**: `wNS4 (.node ν) es =
  wSumNode4 ν es`, so `hNS4` is a theorem about the specifications, not a definition.
* **`peL_node4`**: Z2's `P^e` on a node is `targetSNode4S` at the verifier's operand (Z1's point).
-/

namespace FR.Snd.CN4
open RecursionFast FR.Merkle Finset FR.Impl FR.Snd.P4a FR.NT4

set_option linter.constructorNameAsVariable false

theorem nbC_node (ν : Rev4.NodeKind) : nbC (.node ν) = nbN ν := rfl

section Weights
variable (ν : Rev4.NodeKind)

/-- The `Out` part: `Σ_y eq(r, y)·[lk y] eq(τ, y) = lkE`. -/
theorem sum_lkW4 {n : ℕ} (τ rb : Fin n → F) :
    ∑ y ∈ range (2 ^ n), eqAtR rb y * lkW4 ν τ y = lkE ν τ rb := by
  unfold lkW4 lkE
  refine sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- The `In` part: `Σ_y eq(r, y)·shN4(y) = lkSh + κ_s·lkE0` (the successor reindexed; the top
block is not linked). -/
theorem sum_shN4 (τ rb : Fin (nbN ν) → F) (κ : F) :
    ∑ y ∈ range (2 ^ nbN ν), eqAtR rb y * shN4 ν τ κ y = lkSh ν τ rb + κ * lkE0 ν rb := by
  obtain ⟨h1, h2, h3, h4⟩ := chLen_facts ν
  have hw := wotsB_hUsed ν (σ := 0) (by norm_num)
  have hpos : 0 < 2 ^ nbN ν := Nat.two_pow_pos _
  have hN : 2 ^ nbN ν = (2 ^ nbN ν - 1) + 1 := by omega
  have hA : ∑ y ∈ range (2 ^ nbN ν), eqAtR rb y *
      (if 1 ≤ y ∧ N4c.chainLk4 ν (y - 1) then eqAtR τ (y - 1) else 0) = lkSh ν τ rb := by
    unfold lkSh
    rw [hN, sum_range_succ', sum_range_succ]
    have htop : N4c.chainLk4 ν (2 ^ nbN ν - 1) = false := by
      rw [Bool.eq_false_iff]; intro e; have := ((chainLk4_iff ν _).1 e).1; omega
    rw [htop, if_neg (by omega)]
    simp only [Bool.false_eq_true, if_false, add_zero, mul_zero]
    refine sum_congr rfl fun y _ => ?_
    rw [Nat.add_sub_cancel]
    simp only [show 1 ≤ y + 1 by omega, true_and]
    split_ifs <;> ring
  have hB : ∑ y ∈ range (2 ^ nbN ν), eqAtR rb y *
      (κ * ((if y = 0 then 1 else 0) + if y = N4c.chLen ν 0 then 1 else 0)) = κ * lkE0 ν rb := by
    unfold lkE0
    simp only [mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib, sum_ite_eq', mem_range,
      if_pos hpos, if_pos (show N4c.chLen ν 0 < 2 ^ nbN ν by omega)]
    ring
  rw [← hA, ← hB, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [shN4, mul_add]

/-- Family `f`'s part: its extension is `linkW4S`. -/
theorem sum_famW4' (f : ℕ) (τ rb : Fin (nbN ν) → F) (θ rp : Fin 10 → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν), eqAtR rb y * eqAtR rp q * famW4 ν f τ θ y q =
      linkW4S ν f τ θ rb rp := by
  have e : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν), famW4 ν f τ θ y q *
      (eqAtR rb y * eqAtR rp q) = ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n,
        ∑ s ∈ range (NodeT.fbits f), eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
          (eqAtR rb (N4c.srcB4 ν σ f t) * eqAtR rp (NodeT.fpos f s) -
            eqAtR rb (N4c.mirB4 ν σ f t) * eqAtR rp (NodeT.mpos f t s)) :=
    sum_famW4 (ν := ν) (f := f) τ θ (fun y q => eqAtR rb y * eqAtR rp q)
  calc _ = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν), famW4 ν f τ θ y q *
        (eqAtR rb y * eqAtR rp q) := sum_congr rfl fun q _ => sum_congr rfl fun y _ => mul_comm _ _
    _ = _ := e
    _ = _ := by
      unfold linkW4S NodeT.slotWL
      refine sum_congr rfl fun σ _ => sum_congr rfl fun t _ => ?_
      rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun s _ => by ring

/-- **`finSh` (ii)'s MLE lemma on a node**: the extension of `wNode4` at `(r_blk, r_pos)` is
`E·slotW₀ + (Sh + κ_s E₀)·slotW₂ + Σ_f κ_s^(f+2) W_f` on the specifications. -/
theorem final_node4 (τ rb : Fin (nbN ν) → F) (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν),
        eqAtR rb y * eqAtR (ptA 10 rp) q * wNode4 ν τ (ptA 10 θ) κ y q =
      lkE ν τ rb * slotWS 0 θ rp + ((lkSh ν τ rb + κ * lkE0 ν rb) * slotWS 2 θ rp +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * linkW4S ν f τ (ptA 10 θ) rb (ptA 10 rp)) := by
  have hO := sum_prod_split (eqAtR rb) (lkW4 ν τ) (eqAtR (ptA 10 rp)) (slotT (ptA 10 θ) 256)
    (2 ^ 10) (2 ^ nbN ν)
  have hI := sum_prod_split (eqAtR rb) (shN4 ν τ κ) (eqAtR (ptA 10 rp)) (slotT (ptA 10 θ) 0)
    (2 ^ 10) (2 ^ nbN ν)
  rw [sum_lkW4, sum_slot_eqAtR _ _ (by norm_num)] at hO
  rw [sum_shN4, sum_slot_eqAtR _ _ (by norm_num)] at hI
  have hF : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν), eqAtR rb y * eqAtR (ptA 10 rp) q *
      ∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW4 ν f τ (ptA 10 θ) y q =
      ∑ f ∈ range nLinkFam, κ ^ (f + 2) * linkW4S ν f τ (ptA 10 θ) rb (ptA 10 rp) := by
    calc _ = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν), ∑ f ∈ range nLinkFam,
          κ ^ (f + 2) * (eqAtR rb y * eqAtR (ptA 10 rp) q * famW4 ν f τ (ptA 10 θ) y q) :=
          sum_congr rfl fun q _ => sum_congr rfl fun y _ => by
            rw [mul_sum]; exact sum_congr rfl fun f _ => by ring
      _ = ∑ q ∈ range (2 ^ 10), ∑ f ∈ range nLinkFam, ∑ y ∈ range (2 ^ nbN ν),
          κ ^ (f + 2) * (eqAtR rb y * eqAtR (ptA 10 rp) q * famW4 ν f τ (ptA 10 θ) y q) :=
          sum_congr rfl fun q _ => sum_comm
      _ = _ := sum_comm
      _ = _ := sum_congr rfl fun f _ => by
          rw [← sum_famW4', mul_sum]; exact sum_congr rfl fun q _ => by rw [mul_sum]
  rw [← hF, slotWS_eq, slotWS_eq, show slotBase 0 = 256 from rfl, show slotBase 2 = 0 from rfl]
  simp only [zero_add] at hI ⊢
  rw [← hO, ← hI, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [wNode4]
  ring

end Weights

/-! ## On the log -/

/-- `linkSum` over the eight families: `acc + Σ_f κ_s^(f+2) W_f`. -/
theorem linkSum_eq8 (W : Array F) (ks acc : F) :
    linkSum W ks nLinkFam acc (ks * ks) = acc + ∑ f ∈ range nLinkFam, ks ^ (f + 2) * W.getD f 0 := by
  simp only [nLinkFam, linkSum, sum_range_succ, sum_range_zero]
  ring

/-- **`finSh` (ii)'s weight on a node, on the specifications** (`relSh4`'s `w_out + w_in` with
`implN ν`'s ops at `specN4`): `shiftMask4S` at the padded `τ`, `r_blk`; `slotWS` 0 and 2;
`linkWAll4S` at `τ ‖ θ`, `r_blk ‖ r_pos`; `linkSum` from `(Sh + κ_s E₀)·slotW₂` at `κ_s²`. -/
def wSumNode4 (ν : Rev4.NodeKind) (es : Log) : F :=
  (shiftMask4S ν (P4a.pad18 (.node ν) (P4a.tauL (.node ν) es)) (P4a.pad18 (.node ν) (P4a.rbL (.node ν) es))).1 *
      slotWS 0 (thL es).toArray (P4a.rpL (.node ν) es).toArray +
    linkSum (linkWAll4S ν (P4a.tauL (.node ν) es ++ thL es).toArray (P4a.rbL (.node ν) es ++ P4a.rpL (.node ν) es).toArray)
      (ksL es) nLinkFam
      (((shiftMask4S ν (P4a.pad18 (.node ν) (P4a.tauL (.node ν) es)) (P4a.pad18 (.node ν) (P4a.rbL (.node ν) es))).2.1 +
          ksL es *
            (shiftMask4S ν (P4a.pad18 (.node ν) (P4a.tauL (.node ν) es)) (P4a.pad18 (.node ν) (P4a.rbL (.node ν) es))).2.2) *
        slotWS 2 (thL es).toArray (P4a.rpL (.node ν) es).toArray)
      (ksL es * ksL es)

theorem ptA_pad (ν : Rev4.NodeKind) (xs : List F) (h : xs.length = nbN ν) :
    ptA (nbN ν) (P4a.pad18 (.node ν) xs) = ptOf (nbN ν) xs := funext fun l => by
  simp only [ptA, ptOf, P4a.pad18, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.val < xs.length by omega)]

theorem ptA_app (n : ℕ) (xs ys : List F) (h : xs.length = n) :
    ptA n (xs ++ ys).toArray = ptOf n xs ∧
      (fun l : Fin 10 => (xs ++ ys).toArray.getD (n + l) 0) = ptOf 10 ys := by
  constructor <;> funext l <;>
    simp only [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  · rw [List.getElem?_append_left (show l.val < xs.length by omega)]
  · rw [List.getElem?_append_right (show xs.length ≤ n + l.val by omega),
      show n + l.val - xs.length = l.val by omega]

/-- **`hNS4` on the specifications**: P4e's `wNS4` (the extension of the node's S2 weight at S2's
point) is the value `finSh` (ii) computes from `shiftMask4S`, `slotWS` and `linkWAll4S`. -/
theorem wNS4_node4 (ν : Rev4.NodeKind) (es : Log) : wNS4 (.node ν) es = wSumNode4 ν es := by
  have hτ : (P4a.tauL (.node ν) es).length = nbN ν := by simp [P4a.tauL, nbC_node]
  have hr : (P4a.rbL (.node ν) es).length = nbN ν := by simp [P4a.rbL, nbC_node]
  have hθ : ptA 10 (thL es).toArray = ptOf 10 (thL es) := ptA_toArray _ _
  have hp : ptA 10 (P4a.rpL (.node ν) es).toArray = ptOf 10 (P4a.rpL (.node ν) es) := ptA_toArray _ _
  have e := final_node4 ν (ptOf (nbN ν) (P4a.tauL (.node ν) es)) (ptOf (nbN ν) (P4a.rbL (.node ν) es))
    (thL es).toArray (P4a.rpL (.node ν) es).toArray (ksL es)
  rw [hθ, hp] at e
  have hw : wNS4 (.node ν) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbN ν),
      eqAtR (ptOf (nbN ν) (P4a.rbL (.node ν) es)) y * eqAtR (ptOf 10 (P4a.rpL (.node ν) es)) q *
        wNode4 ν (ptOf (nbN ν) (P4a.tauL (.node ν) es)) (ptOf 10 (thL es)) (ksL es) y q := rfl
  rw [hw, e, wSumNode4, linkSum_eq8]
  obtain ⟨a1, a2⟩ := ptA_app (nbN ν) _ (thL es) hτ
  obtain ⟨b1, b2⟩ := ptA_app (nbN ν) _ (P4a.rpL (.node ν) es) hr
  simp only [shiftMask4S, ptA_pad ν _ hτ, ptA_pad ν _ hr]
  have hs : ∀ f ∈ range nLinkFam, (linkWAll4S ν (P4a.tauL (.node ν) es ++ thL es).toArray
      (P4a.rbL (.node ν) es ++ P4a.rpL (.node ν) es).toArray).getD f 0 =
      linkW4S ν f (ptOf (nbN ν) (P4a.tauL (.node ν) es)) (ptOf 10 (thL es))
        (ptOf (nbN ν) (P4a.rbL (.node ν) es)) (ptOf 10 (P4a.rpL (.node ν) es)) := fun f hf => by
    rw [linkWAll4S, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (mem_range.1 hf),
      Option.getD_some, a1, a2, b1, b2]
  rw [Finset.sum_congr rfl (fun f hf => congrArg (ksL es ^ (f + 2) * ·) (hs f hf))]

/-! ## Z2's `P^e` on a node -/

/-- **A node's `P^e` is `targetSNode4S`** at the verifier's operand (Z1's point: entry `l` is Z1's
coordinate `l`, for `l ≤ nb`). -/
theorem peL_node4 {es : Log} {ν : Rev4.NodeKind} (hν : kindOfC es = .node ν) {r : Array F}
    (hr : ∀ l < nbN ν + 1, r.getD l 0 = coordAt es 2 l) :
    targetSNode4S ν r = Array.ofFn (P4a.peL (zlm4 N4c.indN4 N4c.etN4) es) := by
  have hm : 14 ≤ ν.m := by cases ν <;> decide
  have h6 : P4a.mC 6 (kindOfC es) = 8 + nbN ν := by rw [hν]; show ν.m - 6 = 8 + (ν.m - 14); omega
  have hlen := P4a.zrL_length es
  unfold targetSNode4S
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [targetS_range _ _ σ (fun u => nodeE4 ν (u / 256) (σ + 64 * (u % 256))) fun _ => rfl,
    peL_range4]
  have hpt : Fin.append (zLo r) (rbOf4 ν r) = ptOf (8 + nbN ν) (P4a.zrL es) := by
    funext l
    refine Fin.addCases (m := 8) (n := nbN ν) (fun i => ?_) (fun i => ?_) l
    · rw [Fin.append_left]
      simp only [ptOf, Fin.coe_castAdd, zrL_getD4 es i.val (by rw [h6]; omega), zLo]
      split_ifs with h
      · rfl
      · rw [hr 0 (by omega)]; congr 1; omega
    · rw [Fin.append_right]
      have hi := i.isLt
      rw [ptOf, Fin.coe_natAdd, zrL_getD4 es (8 + i.val) (by rw [h6]; omega),
        dif_neg (show ¬ 8 + i.val < 7 by omega), rbOf4, hr (1 + i.val) (by omega)]
      congr 1; omega
  rw [hpt]
  have hk : ∀ u, (zlm4 N4c.indN4 N4c.etN4).Et (kindOfC es) es (u / 256) (pAt σ u) =
      nodeE4 ν (u / 256) (σ + 64 * (u % 256)) := fun u => by
    rw [hν]; exact (nodeE4_etN4 ν _ _).symm
  simp only [hk]
  rw [h6]

/-! ## Controls -/

/-- **The start term is present** (ruling D10): at `r = 0` the starts' weight
`eq(r, 0) + eq(r, chLen₀)` is `1` (chain 0's start reads `1`, chain 1's `0`), so `E₀` is not the
zero function and dropping it (`J = 9`) changes `finSh` (ii)'s weight. -/
theorem lkE0_ctrl (ν : Rev4.NodeKind) : lkE0 ν (fun _ : Fin (nbN ν) => (0 : F)) = 1 := by
  have h : 0 < N4c.chLen ν 0 := (chLen_facts ν).1
  have hb : (N4c.chLen ν 0).testBit (Nat.log2 (N4c.chLen ν 0)) = true :=
    Nat.testBit_log2 (by omega)
  have hl : Nat.log2 (N4c.chLen ν 0) < nbN ν := by
    have := (chLen_facts ν).2.2.2; have := wotsB_hUsed ν (σ := 0) (by norm_num)
    have h3 := (chLen_facts ν).2.2.1
    rw [Nat.log2_lt (by omega)]; omega
  have h0 : eqAtR (fun _ : Fin (nbN ν) => (0 : F)) 0 = 1 := by simp [eqAtR]
  have h1 : eqAtR (fun _ : Fin (nbN ν) => (0 : F)) (N4c.chLen ν 0) = 0 := by
    unfold eqAtR; exact Finset.prod_eq_zero (i := ⟨_, hl⟩) (mem_univ _) (by simp [hb])
  unfold lkE0; rw [h0, h1, add_zero]

end FR.Snd.CN4
