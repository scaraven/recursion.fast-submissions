-- G6: this module also holds the former modules `FRNodeTarget4W`, `FRSoundness4R4Ctrl`, `FRSoundness4R4FrS`, `FRSoundness4R4FrZ`, `FRSoundness4R4FrLc` (one section each, in import order).
import FRSoundness4P4aNS
import FRSoundness4P4aZ
import FRNodeTarget4C
import FRSoundness4R4FrE
import FRSoundness4R4Stmt
import FRSoundness4R4FinSh
import FRVerifierImplNode4
import FRVerifierC4
import FRSoundnessCoreWalk

section G6_FRNodeTarget4W

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8/A.9 on a node, A.10 S2; stage S-CN4): the node
-- ops' specifications against P4e's weights (`FRSoundness4P4aNS`: `wNode4`, `wNS4`; P4c's `peL`).

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

end G6_FRNodeTarget4W

section G6_FRSoundness4R4Ctrl

-- New for `flock-recursive` (stage R4): controls for the program layer on `gen4`.

/-!
# Controls for R4's definitions

| Definition | Positive | Negative |
|---|---|---|
| `refPhase4` | `refPhase4_sqz0` (an empty squeeze run passes, consuming nothing) | `refPhase4_seed_nil` (a seed with no entry fails), `refPhase4_abs_wrong` (an absorb answered for another query fails) |
| `fsMsgs4` | `fsMsgs4_len`, `fsMsgs4_items`, `fsMsgs4_ctl` (message 1 is `stmt` at 48, 128 bytes) | `fsMsgs4_ctl` (message 3 is a squeeze, not a message) |
| `relocFin` | `relocFin_ops`, `finOps4_eq` | `relocF_moves` (relocation to `seq4` changes `E`'s offset: `reloc_seq4_moves`) |
| `SkRun4` | `skRun4_of_accept` | `not_skRun4_nil` (an empty trace has no 482 entries) |
| `exec_ext` | the lemma | `exec_ask_nil` (an ask on an empty trace fails) |
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP)

theorem refPhase4_sqz0 (n i : ℕ) (c : GCtx) (r : Array Val) (tr : Trace) :
    refPhase4 impl κ inp S p n ("P2", .squeezes 0 (.pos i)) c r tr = some ([], true, tr) := rfl

theorem refPhase4_seed_nil (n : ℕ) (c : GCtx) (r : Array Val) :
    refPhase4 impl κ inp S p n ("seed", .seed) c r [] = none := rfl

theorem refPhase4_abs_wrong (n f len : ℕ) (c : GCtx) (r : Array Val) (q : ByteArray) (a : Digest)
    (tr : Trace) (hq : q ≠ absorbQ (rd r c.st).toD (FR.msgAt inp 0 (fieldOffOf S f + phaseOffOf S n f) len)) :
    refPhase4 impl κ inp S p n ("x", .absorb f len) c r ((q, a) :: tr) = none := by
  simp [refPhase4, ans1, hq]

theorem fsMsgs4_ctl : (fsMsgs4 seq4).getD 1 none = some (48, 128) ∧ (fsMsgs4 seq4).getD 3 none = none := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

theorem relocF_moves : fieldOffOf seq4 fE ≠ fieldOff fE := reloc_seq4_moves

theorem not_skRun4_nil {y : List Val × List Bool × Trace} : ¬ SkRun4 impl p inp [] y := fun h => by
  have := h.len; simp [fsOf] at this

theorem exec_ask_nil (st : ℕ) (s : St) : exec impl κ inp [.askSqueeze st] s [] = none := rfl

end FR.Snd.R4

end G6_FRSoundness4R4Ctrl

section G6_FRSoundness4R4FrS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finSh` (i), A.10 S2, B-12; stage R4e).

/-!
# S2's round checks on an accepted run (P4a's `RejS2`)

* **The log's public reads**: the seed query is `seedQ vk c (π[0, 48))` (**`seedQ4`**), so its bytes
  `71 + o` are π's `o` (**`seed_bytesAt4`**); the `stmt` message is `π[48, 176)` (**`stmt_msg4`**),
  so the log's `n` is π's (**`nStmt_eq4`**). `bndL`'s four values are the program's `pe4` reads
  (**`bnd_seg4`**).
* **A segment's last block on the registers** (**`last_view4`**): the `stmt` phase's outputs after
  its state register are `lastOuts b₂`, and `lastOps` (P4a's `run_lastOps`) left `0` at `b₂ + 2` and
  `L`'s bits `bF (lb n k)` at `b₂ + 40 + 3k`.
* **`relSh4_of_accept`**: `finSh`'s relation holds on an accepted run (field 2 of the rest).
* **`s2_chk_seg4`**, **`s2_chk_node4`**: `relSh4` (i) through the views is `c0S` (for `shiftTarget`
  at its specification `shiftTargetS`, the parameter `hST`), so every real S2 round check holds;
  **`not_rejS2_seg4`**, **`not_rejS2_node4`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-! ## The seed and the statement on the log -/

theorem fieldOff_hdr_stmt4 : fieldOffOf seq4 fHdr = 0 ∧ fieldOffOf seq4 fStmt = 48 := by
  rw [seq4_eq]; decide +kernel


section Log
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
include h

/-- **The seed entry's query** is `seedQ vk c hdr`, `hdr` π's first 48 bytes. -/
theorem seedQ4 : (entAt (fsOf tr (itemsOf seq4)) 0).1 = seedQ inp.vk inp.c (inp.π.extract 0 48) := by
  have h0 := h.hq 0 (by decide)
  obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
  rw [hms] at h0
  simp only [List.getD_cons_zero, qOf, ite_true] at h0
  rw [entAt, h0]

theorem seed_byte4' {k : ℕ} (hk : k < 48) :
    (entAt (fsOf tr (itemsOf seq4)) 0).1.data.toList.getD (71 + k) 0 = inp.π.data.toList.getD k 0 := by
  rw [seedQ4 h, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega),
    List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega),
    List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega), toList_extract]
  simp only [tagSeed, List.length_cons, List.length_nil, Vector.length_toList, Nat.sub_zero,
    List.drop_zero]
  rw [show 71 + k - 7 - 32 - 32 = k by omega, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hk]

/-- **The seed query's bytes `71 + o`** are π's bytes `o` (`o + n ≤ 48`). -/
theorem seed_bytesAt4 {o n : ℕ} (hon : o + n ≤ 48) :
    bytesAt (entAt (fsOf tr (itemsOf seq4)) 0).1 (71 + o) n = bytesAt inp.π o n := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, Nat.add_assoc, seed_byte4' h (by omega)]

/-- **The `stmt` message on the log** is π's bytes `48 … 175`. -/
theorem stmt_msg4 : Snd.msgAt (fsOf tr (itemsOf seq4)) 1 = inp.π.extract 48 (48 + 128) := by
  have e := h.hq 1 (by decide)
  rw [fsMsgs4_ctl.1] at e
  simp only [qOf, one_ne_zero, if_false] at e
  exact msgAt_of_q e

/-- **The log's `n` is the program's** (the 24-bit index at π's byte 81). -/
theorem nStmt_eq4 : P4a.nStmt (fsOf tr (itemsOf seq4)) = idxOfF 24 (digestAt inp.π 81) 0 := by
  rw [P4a.nStmt, stmt_msg4 h, digestAt_eq, digestAt_eq, bytesAt_extract_of_le _ (by norm_num)]

/-- **A segment's boundary reads** (`bndL`'s four values) are the program's `pe4` reads. -/
theorem bnd_seg4 :
    [readF (entAt (fsOf tr (itemsOf seq4)) 0).1 87, readF (entAt (fsOf tr (itemsOf seq4)) 0).1 103,
      readF (Snd.msgAt (fsOf tr (itemsOf seq4)) 1) 1, readF (Snd.msgAt (fsOf tr (itemsOf seq4)) 1) 17] =
    [pe4 seq4 inp fHdr 16, pe4 seq4 inp fHdr 32, pe4 seq4 inp fStmt 1, pe4 seq4 inp fStmt 17] := by
  obtain ⟨h0, h1⟩ := fieldOff_hdr_stmt4
  simp only [readF, pe4, h0, h1, stmt_msg4 h, bytesAt_extract_of_le16 _ (show 1 + 16 ≤ 128 by norm_num),
    bytesAt_extract_of_le16 _ (show 17 + 16 ≤ 128 by norm_num),
    show (87 : ℕ) = 71 + 16 from rfl, show (103 : ℕ) = 71 + 32 from rfl,
    seed_bytesAt4 h (show 16 + 16 ≤ 48 by norm_num), seed_bytesAt4 h (show 32 + 16 ≤ 48 by norm_num)]

end Log

/-! ## A segment's last block on the registers -/

theorem phaseIx_stmt : phaseIx "stmt" = 1 := by decide

/-- **The `stmt` phase of an accepted segment run**: its outputs after the state register are
`lastOuts b₂`; `lastOps` left `0` at `b₂ + 2` and bit `k` of `L = n − 1` at `b₂ + 40 + 3k`
(`n` the index at π's byte 81). -/
theorem last_view4 {σ : SegKind} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl (.ofSeg σ) inp tr y) :
    ∃ b₂, ((skeleton4 seq4 (.ofSeg σ)).2.outs.getD 1 []).drop 1 = lastOuts b₂ ∧
      b₂ + 94 ≤ (#[] ++ y.1.toArray).size ∧ rd (#[] ++ y.1.toArray) (b₂ + 2) = .f 0 ∧
      ∀ k < 18, rd (#[] ++ y.1.toArray) (b₂ + 40 + 3 * k) =
        .f (P4a.bF (P4a.lb (idxOfF 24 (digestAt inp.π 81) 0) k)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, -, -⟩ := phase_at4 impl _ inp _ h.ref (k := 1) (by decide)
  have hph : (phasesOf seq4)[1] = ("stmt", .absorb fStmt 128) := rfl
  have hnode : (KindP.ofSeg σ).d.node = false := by cases σ <;> rfl
  have hout := skeleton4_outs seq4 (KindP.ofSeg σ) (k := 1) (by decide)
  rw [hph] at hx hout
  simp only [refPhase4] at hx
  obtain ⟨⟨a, trk'⟩, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [absTail4, ite_true, hnode, Bool.false_eq_true, ite_false] at hz
  generalize ho : fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt = o at hz hout
  have ho' : o = 48 := by rw [← ho, stmtOff4]
  rw [pureRun_append] at hz
  obtain ⟨⟨L1, f1⟩, h1, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨⟨L2, f2⟩, h2, rfl⟩ := Option.map_eq_some_iff.1 hz
  have hl1 := pureRun_len impl _ inp _ _ _ _ _ h1
  simp only [List.length_cons, List.length_nil] at hl1
  set b₂ := (#[] ++ M.toArray).size + 2 + opsOut (stmtOps4 (.ofSeg σ) o (#[] ++ M.toArray).size
    ((#[] ++ M.toArray).size + 2)) with hb₂
  have hs : (#[] ++ M.toArray ++ L1.toArray).size = b₂ := by simp [hl1, hb₂]; omega
  have hrun := P4a.run_lastOps impl (KindP.ofSeg σ).tix inp o (#[] ++ M.toArray ++ L1.toArray)
  rw [hs] at hrun
  have hreb := pureRun_rebase impl (KindP.ofSeg σ).tix inp (lastOps o b₂) (#[] ++ M.toArray) L1 []
  rw [List.append_nil, hrun, h2] at hreb
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hreb)
  have hl := pureRun_len impl _ inp _ _ _ _ _ hrun
  rw [opsOut_lastOps, List.length_nil, Nat.zero_add] at hl
  have hML : (M ++ L1).length = b₂ := by simpa using hs
  dsimp only at hext
  rw [← List.append_assoc] at hext
  have hD : digestAt inp.π (absOff 0 (o + 33)) = digestAt inp.π 81 := by rw [absOff_zero, ho']
  refine ⟨b₂, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [hout]; simp [genPhase4, hb, hnode, hb₂, ho]
  · have := hext.1; simp only [Array.size_append, List.size_toArray, List.length_append] at this ⊢
    simp only [List.length_append] at hML; omega
  · rw [← hML, rd_phase4 hext (by omega), P4a.lastVals_zero]
  · rw [← hML, Nat.add_assoc, rd_phase4 hext (by omega), P4a.lastVals_bit _ hk, hD]

/-! ## `finSh`'s relation on an accepted run -/

theorem rest_gFinSh (P : FinP) :
    (finalsOf P).rest[2]'(by rw [rest_finalsOf_length]; decide) = gFinSh P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

/-- `finSh`'s registers are named or `zhat` registers (abstract `fi`). -/
theorem hin_Sh {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) :
    ∀ x ∈ coordsR fi "S1" ++ chals fi "S2" P.S.s2 ++ lastRegs fi ++
      [claim0 fi "S2", claimN fi "S2", fi.zhat.getD 2 0, zeroReg fi,
       (coordsR fi "S1").getD (P.S.mStar - 14 + 10) 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((hx | hx) | hx) | rfl | rfl | rfl | rfl | rfl
  · exact hsk "S1" x (List.mem_of_mem_drop hx)
  · exact hsk "S2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "stmt" x (List.mem_of_mem_drop hx)
  · exact headD_lt (hsk "S2") hn
  · exact getLastD_lt (hsk "S2") hn
  · exact getD_lt hn hz 2
  · exact getD_lt hn (hsk "stmt") 1
  · exact getD_lt hn (fun x hx => hsk "S1" x (List.mem_of_mem_drop hx)) _

/-- **`finSh`'s relation on the fields of an accepted run** (field 2, file `Rs 2`). -/
theorem relSh4_of_fields {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relSh4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 2⟩ (Rs 2) P = true := by
  obtain ⟨-, L2, hL2, -, -⟩ := hF.fld 2 (by decide)
  rw [rest_gFinSh] at hL2
  obtain ⟨L', hL'⟩ := flag_gFinSh impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 2⟩ (Rs 2) P
    (hin_Sh (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide)))
  exact pureRun_det hL2 hL'

/-- **`finSh`'s relation on an accepted run.** -/
theorem relSh4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R ∧ (∀ x ∈ fi.zhat, x < R.size) ∧
      relSh4 impl p.tix inp fi R P = true := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept P h
  exact ⟨y, hF.sk, ⟨(skeleton4 seq4 p).2.outs, zh, Ex 2⟩, Rs 2, rfl, hF.ext 2 (by decide), hF.zlt' (by decide),
    relSh4_of_fields hF⟩

/-! ## S1's coordinates and S2's challenges by name -/

/-- A list mapped to `g` on `range N`: its length is `N`, its entries `g j`. -/
theorem map_getElem_of {α β : Type} {co : List α} {f : α → β} {g : ℕ → β} {N : ℕ}
    (hco : co.map f = (List.range N).map g) :
    co.length = N ∧ ∀ j (hj : j < co.length), f co[j] = g j := by
  have hl := congrArg List.length hco
  simp only [List.length_map, List.length_range] at hl
  refine ⟨hl, fun j hj => ?_⟩
  have := congrArg (fun l => l[j]?) hco
  simp only [List.getElem?_map, List.getElem?_range, show j < N by omega,
    List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at this
  exact this

/-- The first `N` entries mapped to `g`: `N ≤` the length, entries `j < N` are `g j`. -/
theorem take_map_getElem {α β : Type} {co : List α} {f : α → β} {g : ℕ → β} {N : ℕ}
    (hco : (co.take N).map f = (List.range N).map g) :
    N ≤ co.length ∧ ∀ j (hj : j < co.length), j < N → f co[j] = g j := by
  obtain ⟨hl, hg⟩ := map_getElem_of hco
  simp only [List.length_take] at hl
  refine ⟨by omega, fun j hj hjN => ?_⟩
  have := hg j (by simp; omega)
  rwa [List.getElem_take] at this

section S1
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
  {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **S1's coordinates by name** (`coS`): `κ_s` at 28, `τ`'s first `n ≤ 18`, `θ` at 18 … 27. -/
theorem s1_view4 :
    fv R ((coordsR fi "S1").getD 28 0) = ksL (fsOf tr (itemsOf seq4)) ∧
      (∀ n ≤ 18, ((coordsR fi "S1").take n).map (fv R) = (List.range n).map (coS (fsOf tr (itemsOf seq4)))) ∧
      (((coordsR fi "S1").drop 18).take 10).map (fv R) = thL (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hn11, e11⟩ := ph4 (n := 11) (x := ("S1", Sh.squeezes 15 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 h hfi hR hn11 (by rw [e11]) (by norm_num) phaseIx_vals.2.2.2.2.2.2.1
    (a := 29) (by norm_num)
  rw [show phStart4 11 = 99 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  obtain ⟨hlen, hget⟩ := take_map_getElem hco
  refine ⟨?_, fun n hn => ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega), hget 28 (by omega) (by norm_num)]; rfl
  · apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [hget j (by omega) (by omega)]; rfl
  · apply List.ext_getElem (by simp [thL]; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range, thL]
    simp only [thL, List.length_map, List.length_range] at h2
    rw [hget _ (by omega) (by omega)]; rfl

/-- **S2's challenges by name**: the block part (`n ≤ 18`) and the 10 position coordinates after
it are the log's `rch 114`. -/
theorem s2r_view4 {n : ℕ} (hn : n ≤ 18) :
    ((chals fi "S2" seq4.s2).take n).map (fv R) = (List.range n).map (rch 114 (fsOf tr (itemsOf seq4))) ∧
      (((chals fi "S2" seq4.s2).drop n).take 10).map (fv R) =
        (List.range 10).map (fun l => rch 114 (fsOf tr (itemsOf seq4)) (n + l)) := by
  obtain ⟨hn12, e12⟩ := ph4 (n := 12) (x := ("S2", Sh.rounds fS2 seq4.s2 2 false)) rfl
  have hch := chals_view4 h hfi hR hn12 (by rw [e12]) phaseIx4_rounds.2.2.2.1 le_rfl
  rw [show phStart4 12 = 114 by rw [phStart4, fsStarts4_eq]; rfl, rchs] at hch
  obtain ⟨hlen, hget⟩ := map_getElem_of hch
  have h28 : seq4.s2 = 28 := by rw [seq4_eq]
  replace hlen := hlen.trans h28
  constructor
  · apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [hget j (by omega)]
  · apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [hget _ (by omega)]

/-- **S2 from its head claim**: the real rounds' checks hold from `c`, and S2's last claim register
holds the claim after them. -/
theorem s2_from_head4 (hle : p.d.seq.s2 ≤ seq4.s2) {c : F} (hc : rd R (claim0 fi "S2") = .f c) (L : Log) :
    (∀ l < p.d.seq.s2, Chk2 114 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4)) l) ∧
      rd R (claimN fi "S2") =
        .f (clR2 114 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4)) p.d.seq.s2) := by
  obtain ⟨hn12, e12⟩ := ph4 (n := 12) (x := ("S2", Sh.rounds fS2 seq4.s2 2 false)) rfl
  obtain ⟨hcl, -, -, hlt, hlast⟩ := roundsF2_view4 h hn12 (by rw [e12]) L
  rw [(outsOf_skel hfi "S2").2.1, phaseIx4_rounds.2.2.2.1] at hc
  rw [← hR.rd hcl, hc] at hlast
  obtain ⟨hN, hchk⟩ := hlast _ rfl
  rw [e12, (realRounds_vals _ _).2.1, Nat.min_eq_left hle,
    show phStart4 12 = 114 by rw [phStart4, fsStarts4_eq]; rfl] at hchk hN
  refine ⟨hchk, ?_⟩
  rw [(outsOf_skel hfi "S2").2.2, phaseIx4_rounds.2.2.2.1, hR.rd hlt, hN]

end S1

/-! ## S2's head and last claims on the fields -/

section Head
variable {tr : Trace} {y : List Val × List Bool × Trace} {zh : List Reg} {Rs : ℕ → Array Val}
  {Ex : ℕ → Array (List Reg)}

/-- **A segment's `stmt` registers in a field's input**: `lastRegs` hold `lastBits`, `zeroReg`
holds `0`. -/
theorem lastRegs_view4 {σ : SegKind} (h : SkRun4 impl (.ofSeg σ) inp tr y) {fi : FinIn}
    (hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) :
    (lastRegs fi).map (fv R) = P4a.lastBits (fsOf tr (itemsOf seq4)) ∧ fv R (zeroReg fi) = 0 := by
  obtain ⟨b₂, hout, hsz, hz, hbits⟩ := last_view4 h
  have e : outsOf fi "stmt" = (outsOf fi "stmt").take 1 ++ lastOuts b₂ := by
    rw [← hout, (outsOf_skel hfi "stmt").1, phaseIx_stmt, List.take_append_drop]
  constructor
  · rw [lastRegs, e, List.drop_append, List.length_take]
    rw [(outsOf_skel hfi "stmt").1, phaseIx_stmt] at e ⊢
    have h1 : ((skeleton4 seq4 (.ofSeg σ)).2.outs.getD 1 []).length = 20 := by
      have := congrArg List.length e
      simp only [List.length_append, List.length_take, lastOuts, List.length_cons, List.length_map,
        List.length_range] at this
      omega
    rw [h1, show min 1 20 = 1 from rfl, show 2 - 1 = 1 from rfl, List.drop_of_length_le (by simp),
      List.nil_append]
    simp only [lastOuts, List.drop_succ_cons, List.drop_zero, List.map_map, P4a.lastBits, nStmt_eq4 h]
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    show (rd R (b₂ + 40 + 3 * k)).toF = _
    rw [hR.rd (by omega), hbits k hk]; rfl
  · rw [zeroReg, e]
    have h1 : ((outsOf fi "stmt").take 1).length = 1 := by
      rw [(outsOf_skel hfi "stmt").1, phaseIx_stmt]
      have := congrArg List.length (show (skeleton4 seq4 (.ofSeg σ)).2.outs.getD 1 [] = _ from
        (List.take_append_drop 1 _).symm)
      rw [hout] at this
      simp only [List.length_append, lastOuts, List.length_cons, List.length_map, List.length_range] at this
      simp only [List.length_take]; omega
    rw [List.getD_append_right _ _ _ _ (by omega), h1]
    show (rd R (b₂ + 2)).toF = _
    rw [hR.rd (by omega), hz]; rfl

/-- **A segment's S2 head claim is `c0S`** (`relSh4` (i) through the views; `shiftTarget` at
`shiftTargetS`). -/
theorem sh_head_seg4 {σ : SegKind}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hF : Fields4 impl (.ofSeg σ) inp tr (segFinP σ) y zh Rs Ex) :
    rd (Rs 2) (claim0 ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩ "S2") =
      .f (P4a.c0S (fsOf tr (itemsOf seq4))) := by
  have hrel := relSh4_of_fields hF
  have hm : (segFinP σ).kv.m (KindP.ofSeg σ).tix = σ.m := rfl
  have hnode : (segFinP σ).kv.node (KindP.ofSeg σ).tix = false := rfl
  have hvn : (segFinP σ).vn = true := rfl
  have hS4 : (segFinP σ).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd] at hrel
  rw [val_eqv_f4 hrel.1]
  congr 1
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs := rfl
  have hE := hF.ext 2 (by decide)
  have hk := kindOfC_seg4 hF.sk
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi hE
  obtain ⟨hL, -⟩ := lastRegs_view4 hF.sk hfi hE
  simp only [P4a.c0S, hk, P4a.bndL, P4a.endBits, CKind.isNode, Bool.false_eq_true,
    ite_false, bnd_seg4 hF.sk, P4a.pad18, P4a.tauL, P4a.nbC, CKind.m]
  have hle18 : σ.m - 14 ≤ 18 := by cases σ <;> decide
  rw [hL, hST _ _ _ _ (by simp [P4a.lastBits]), hks, hτ _ hle18, hθ,
    show 32 - σ.m = 18 - (σ.m - 14) by cases σ <;> rfl]

/-- **A node's S2 head claim is `c0S`** (boundary `0⁴ ‖ lastPad`). -/
theorem sh_head_node4 {ν : NodeKind} {cells : List ℕ}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hF : Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex) :
    rd (Rs 2) (claim0 ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩ "S2") =
      .f (P4a.c0S (fsOf tr (itemsOf seq4))) := by
  have hrel := relSh4_of_fields hF
  have hm : (nodeFinP ν cells).kv.m (KindP.ofNode ν).tix = ν.m := rfl
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hvn : (nodeFinP ν cells).vn = false := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd] at hrel
  rw [val_eqv_f4 hrel.1]
  congr 1
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofNode ν)).2.outs := rfl
  have hk := kindOfC_node4 hF.sk
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi (hF.ext 2 (by decide))
  simp only [P4a.c0S, hk, P4a.bndL, P4a.endBits, CKind.isNode, ite_true, P4a.pad18,
    P4a.tauL, P4a.nbC, CKind.m, Impl.lastPad]
  have hle18 : ν.m - 14 ≤ 18 := by cases ν <;> decide
  rw [hST _ _ _ _ (by simp; cases ν <;> rfl), hks, hτ _ hle18, hθ,
    show 32 - ν.m = 18 - (ν.m - 14) by cases ν <;> rfl]

end Head

/-! ## `RejS2` -/

theorem s2_chk_seg4 {σ : SegKind} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ∀ l < P4a.nrS (kindOfC (fsOf tr (itemsOf seq4))),
      Chk2 114 16 readF (fun d => chF d 0) P4a.c0SL L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have hle : (KindP.ofSeg σ).d.seq.s2 ≤ seq4.s2 := by cases σ <;> decide
  obtain ⟨hchk, -⟩ := s2_from_head4 hF.sk (fi := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩) rfl
    (hF.ext 2 (by decide)) hle (sh_head_seg4 hST hF) L
  rw [(dims_seg4 σ).2.1] at hchk
  intro l hl
  rw [kindOfC_seg4 hF.sk] at hl
  exact (chk2F_c0 (c0 := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) (c0' := P4a.c0SL) rfl 114 l).1
    (hchk l hl)

theorem s2_chk_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ∀ l < P4a.nrS (kindOfC (fsOf tr (itemsOf seq4))),
      Chk2 114 16 readF (fun d => chF d 0) P4a.c0SL L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have hle : (KindP.ofNode ν).d.seq.s2 ≤ seq4.s2 := by cases ν <;> decide
  obtain ⟨hchk, -⟩ := s2_from_head4 hF.sk (fi := ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩) rfl
    (hF.ext 2 (by decide)) hle (sh_head_node4 hST hF) L
  rw [(dims_node4 ν).2.1] at hchk
  intro l hl
  rw [kindOfC_node4 hF.sk] at hl
  exact (chk2F_c0 (c0 := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) (c0' := P4a.c0SL) rfl 114 l).1
    (hchk l hl)

/-- **`RejS2` never holds on an accepted segment run** (`shiftTarget` at its specification). -/
theorem not_rejS2_seg4 {σ : SegKind} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejS2 L (fsOf tr (itemsOf seq4)) :=
  fun ⟨l, hl, _, hne⟩ => hne (s2_chk_seg4 hST h L l hl)

/-- **… nor on an accepted node run.** -/
theorem not_rejS2_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejS2 L (fsOf tr (itemsOf seq4)) :=
  fun ⟨l, hl, _, hne⟩ => hne (s2_chk_node4 hST h L l hl)

/-- **`hST` from an op specification** whose `shiftTarget` is `shiftTargetS` (`specC`, `specSeg`,
`specN4` over `specC`). -/
theorem shiftTarget_of_meets {spec : OpSpec} (hm : impl.Meets spec)
    (hs : spec.shiftTarget = FR.Impl.shiftTargetS) :
    ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c :=
  fun k a b c hc => (hm.2.2.2.2.2.2.2.2.2.2.1 k a b c hc).trans (by rw [hs])

/-! ## `finSh` (ii): S2's last claim binds RS claim 2 (`oSh4`) -/

theorem clR2_c0_eq {c0 c0' : Log → Log → F} {L es : Log} (hc : c0 L es = c0' L es) (b n : ℕ) :
    clR2 b 16 readF (fun d => chF d 0) c0 L es n = clR2 b 16 readF (fun d => chF d 0) c0' L es n := by
  cases n <;> simp only [clR2, hc]

section Bind
variable {tr : Trace} {y : List Val × List Bool × Trace} {zh : List Reg} {Rs : ℕ → Array Val}
  {Ex : ℕ → Array (List Reg)}

/-- **A segment's S2 binding** (`relSh4` (ii) through the views): S2's last claim is
`wSumSeg · v`, `v` the `zhat` register of RS claim 2 (for `shiftMask`, `slotW`, `linkWAll` at the
segment's specifications). -/
theorem sh_bind_seg4 {σ : SegKind}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = shiftSegS a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0)
    (hF : Fields4 impl (.ofSeg σ) inp tr (segFinP σ) y zh Rs Ex) (wNS : CKind → Log → F) :
    P4a.oSh4 wNS (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 2) (zh.getD 2 0)) := by
  have hrel := relSh4_of_fields hF
  have hm : (segFinP σ).kv.m (KindP.ofSeg σ).tix = σ.m := rfl
  have hnode : (segFinP σ).kv.node (KindP.ofSeg σ).tix = false := rfl
  have hvn : (segFinP σ).vn = true := rfl
  have hS4 : (segFinP σ).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd, Bool.true_or, hSM, hSW, hLW, linkSum_zero] at hrel
  have h2 := val_eqv_f4 hrel.2
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs := rfl
  have hE := hF.ext 2 (by decide)
  have hle : (KindP.ofSeg σ).d.seq.s2 ≤ seq4.s2 := by cases σ <;> decide
  obtain ⟨-, hN⟩ := s2_from_head4 hF.sk hfi hE hle (sh_head_seg4 hST hF) []
  have e := Val.f.inj (h2.symm.trans hN)
  have hk := kindOfC_seg4 hF.sk
  simp only [P4a.oSh4, P4a.claimSL4, P4a.wSumL4, hk, CKind.isNode, Bool.false_eq_true, ite_false]
  rw [show P4a.nrS (.seg σ) = (KindP.ofSeg σ).d.seq.s2 by rw [(dims_seg4 σ).2.1]; rfl,
    clR2_c0_eq (c0' := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) rfl, ← e]
  refine congrArg (· * fv (Rs 2) (zh.getD 2 0)) ?_
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi hE
  obtain ⟨hL, hz⟩ := lastRegs_view4 hF.sk hfi hE
  have hle18 : σ.m - 14 ≤ 18 := by cases σ <;> decide
  obtain ⟨hrb, hrp⟩ := s2r_view4 hF.sk hfi hE hle18
  have h32 : 32 - σ.m = 18 - (σ.m - 14) := by cases σ <;> rfl
  rw [hks, hτ _ hle18, hθ, hz, hL, hrb, hrp, h32]
  simp only [P4a.wSumSeg, P4a.tauLL, P4a.pad18, P4a.tauL, P4a.rbL, P4a.rpL, P4a.nbC, CKind.m]

/-- **A node's S2 binding** (`relSh4` (ii) with the node ops at `specN4`): S2's last claim is
`wNS4 · v` (`wSumNode4`, S-CN4's `wNS4_node4`). -/
theorem sh_bind_node4 {ν : NodeKind} {cells : List ℕ}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr)
    (hF : Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex) :
    P4a.oSh4 P4a.wNS4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 2) (zh.getD 2 0)) := by
  have hrel := relSh4_of_fields hF
  have hm : (nodeFinP ν cells).kv.m (KindP.ofNode ν).tix = ν.m := rfl
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hvn : (nodeFinP ν cells).vn = false := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd, Bool.or_true, hSM, hSW, hLW] at hrel
  have h2 := val_eqv_f4 hrel.2
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofNode ν)).2.outs := rfl
  have hE := hF.ext 2 (by decide)
  have hle : (KindP.ofNode ν).d.seq.s2 ≤ seq4.s2 := by cases ν <;> decide
  obtain ⟨-, hN⟩ := s2_from_head4 hF.sk hfi hE hle (sh_head_node4 hST hF) []
  have e := Val.f.inj (h2.symm.trans hN)
  have hk := kindOfC_node4 hF.sk
  simp only [P4a.oSh4, P4a.claimSL4, P4a.wSumL4, hk, CKind.isNode, ite_true]
  rw [show P4a.nrS (.node ν) = (KindP.ofNode ν).d.seq.s2 by rw [(dims_node4 ν).2.1]; rfl,
    clR2_c0_eq (c0' := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) rfl, ← e, CN4.wNS4_node4]
  refine congrArg (· * fv (Rs 2) (zh.getD 2 0)) ?_
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi hE
  have hle18 : ν.m - 14 ≤ 18 := by cases ν <;> decide
  obtain ⟨hrb, hrp⟩ := s2r_view4 hF.sk hfi hE hle18
  have h32 : 32 - ν.m = 18 - (ν.m - 14) := by cases ν <;> rfl
  simp only [List.map_append]
  rw [hks, hτ _ hle18, hθ, hrb, hrp, h32]
  simp only [CN4.wSumNode4, P4a.pad18, P4a.tauL, P4a.rbL, P4a.rpL, P4a.nbC, CKind.m]

end Bind

/-- **The segment ops' facts from `implSegC_meets`'s form** (`specSeg` over `specC`). -/
theorem segOps_of_meets {fin : Finals} {lRows : List Circ.Row} {κs₀ : F}
    (hm : impl.Meets (specSeg (Impl.specC fin lRows κs₀))) (σ : SegKind) :
    (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = shiftSegS a b) ∧ (∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b) ∧
      ∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0 :=
  ⟨hm.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1,
    linkWAll_seg_of_meets hm σ⟩

/-- **The node ops' facts from `implN4_meets`'s form** (`specN4` over a base whose `shiftTarget`
is `shiftTargetS`). -/
theorem nodeOps_of_meets {spec : NodeKind → OpSpec} {ν : NodeKind} (hm : impl.Meets (NI4.specN4 spec ν))
    (hs : (spec ν).shiftTarget = FR.Impl.shiftTargetS) :
    (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b) ∧
      (∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b) ∧
      ∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr :=
  ⟨shiftTarget_of_meets hm hs, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1,
    fun tt rr => (hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ tt rr).trans (by simp only [NI4.specN4, show (KindP.ofNode ν).tix.isNode = true from rfl, if_true])⟩

end FR.Snd.R4

end G6_FRSoundness4R4FrS

section G6_FRSoundness4R4FrZ

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finZ`, A.10 Z1–Zend, B-12; stage R4e).

/-!
# Z3's last claim on an accepted run (P4a's `RejZ`)

* **`coords_pt_view4`**: a coordinates phase's packed register holds the log's coordinates; Z1's
  is the context's `pt` at Z2 (**`pt_cAt4`**), Z2's second output the context's `uni` at Z3
  (**`uni_cAt5`**).
* **`z3_head_seg4`**, **`z3_head_node4`**: Z3's first claim (Z2's `lagrangeS` at the target
  `targetS pe`) is P4a's `c0Z M` — `lagrangeS` at `lagrangeSS` (parameter `hLS`), the target at
  the kind's specification (segment `targetSSegS`, through P4c's `peL_seg` with `lastOps`' bits;
  node `targetSNode4S`, through S-CN4's `peL_node4`; parameter `hTS`).
* **`z_end4`**: `relZ4` (i) through the views is `RejZ`'s equation; **`not_rejZ_seg4`**,
  **`not_rejZ_node4`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-! ## Z1's packed point and Z2's claim register in the contexts -/

/-- **A coordinates phase's packed register** (`outs[n]`'s head) holds the log's coordinates. -/
theorem coords_pt_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) :
    ((skeleton4 seq4 p).2.outs.getD n []).headD 0 < (#[] ++ y.1.toArray).size ∧
      ∀ l < 2 * k, ((rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0)).toAF).getD l 0 =
        fAt (fsOf tr (itemsOf seq4)) (phStart4 n + l / 2) (l % 2) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hout := skeleton4_outs seq4 p hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh hout
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) hk hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, coordVals_length, hl,
    List.length_singleton, List.size_toArray] at hsz
  have hpt : ((skeleton4 seq4 p).2.outs.getD n []).headD 0 = M.length + 3 * k := by
    rw [hout]; simp [genPhase4, hb]
  rw [hpt]
  refine ⟨lt_reg (by simp only [List.length_nil, Nat.zero_add] at hsz; simp; omega), fun l hl2 => ?_⟩
  have hfl : (xs.1.flatMap coordVals).length = 3 * k := by rw [coordVals_length, hl]
  rw [rd_phase4 hext (by simp only [List.length_append, List.length_singleton]; omega),
    List.getD_append_right _ _ _ _ (by omega), hfl, Nat.sub_self, List.getD_cons_zero]
  simp only [Val.toAF, FR.coordsOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range, show l < 2 * xs.1.length by omega, Option.map_some,
    Option.getD_some]
  rw [fAt, ← hans _ (by omega)]

/-- **The context at Z2 points at Z1's packed register.** -/
theorem pt_cAt4 : (cAt4 seq4 p 4).pt = ((skeleton4 seq4 p).2.outs.getD 3 []).headD 0 := by
  rw [cAt4_succ seq4 p (k := 3) (by decide), skeleton4_outs seq4 p (k := 3) (by decide)]
  have e : (phasesOf seq4)[3] = ("Z1", .squeezes (half seq4.z1) .coords) := rfl
  rw [e]
  simp [genPhase4]

/-- **The context at Z3 points at Z2's second output** (`P^{ab}*(λ)`). -/
theorem uni_cAt5 : (cAt4 seq4 p 5).uni = ((skeleton4 seq4 p).2.outs.getD 4 []).getD 1 0 := by
  rw [cAt4_succ seq4 p (k := 4) (by decide), skeleton4_outs seq4 p (k := 4) (by decide)]
  have e : (phasesOf seq4)[4] = ("Z2", .uni fZ2) := rfl
  rw [e]
  cases hn : p.d.node <;> simp [genPhase4, hn]

/-! ## Z3's first claim is `c0Z` -/

theorem extA_refl (R : Array Val) : ExtA R R := ⟨le_rfl, fun _ _ => rfl⟩

/-- `lastAt` of a point whose entries from 19 are `lastBits` is `lastL`. -/
theorem lastAt_pad19 (es : Log) (xs : List F) (hxs : xs.length = 19) :
    Rev4.lastAt (xs ++ P4a.lastBits es).toArray 19 = P4a.lastL es := by
  unfold Rev4.lastAt
  have e : ∀ l ∈ Finset.range 18, (if (xs ++ P4a.lastBits es).toArray.getD (19 + l) 0 = 1 then 2 ^ l else 0) =
      if (P4a.lastL es).testBit l then 2 ^ l else 0 := fun l hl => by
    have hl' := Finset.mem_range.1 hl
    have hg : (xs ++ P4a.lastBits es).toArray.getD (19 + l) 0 = (P4a.lastBits es).getD l 0 := by
      simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show xs.length ≤ 19 + l by omega), hxs, Nat.add_sub_cancel_left]
    rw [hg, P4a.lastBits_getD es hl']
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl e, P4a.sum_bits_self 18 _ (P4a.lastL_lt es)]

/-- Z2's `lagrangeS` value at a target `P^e` table is `c0Z`'s interpolant. -/
theorem lag_c0Z {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (M : P4a.ZLM4) {pe : Array F}
    (hpe : impl.targetS p.tix pe = Array.ofFn (P4a.peL M (fsOf tr (itemsOf seq4)))) :
    (impl.lagrangeS (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray
      (fAt (fsOf tr (itemsOf seq4)) (phStart4 4 + 1) 0) (impl.targetS p.tix pe)).1 =
      P4a.c0Z M (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨-, -, -, -, -, -, -, hmsg, -, -⟩ := uni_view4 h hn4 (by rw [e4])
  have h13 : phStart4 4 = 13 := by rw [phStart4, fsStarts4_eq]; rfl
  rw [h13] at hmsg
  rw [hpe, hLS _ _ _ (by simp [uniEs]), Impl.lagrangeSS, P4a.c0Z, h13]
  have hv : ∀ i < 127, (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD i 0 =
      readF (msgAt (fsOf tr (itemsOf seq4)) 13) (16 * i) := fun i hi => by
    rw [hmsg i hi]
    simp [uniEs, Array.getD_eq_getD_getElem?, hi]
  have e1 : (fun k : Fin 64 => (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD k 0) =
      pzL (fsOf tr (itemsOf seq4)) := funext fun k => hv k (by omega)
  have e2 : (fun k : Fin 63 =>
      (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD (64 + k.val) 0) =
      pabL (fsOf tr (itemsOf seq4)) := funext fun k => hv (64 + k) (by omega)
  have e3 : (fun σ : Fin 64 => (Array.ofFn (P4a.peL M (fsOf tr (itemsOf seq4)))).getD σ 0) =
      P4a.peL M (fsOf tr (itemsOf seq4)) := funext fun σ => by simp [Array.getD_eq_getD_getElem?]
  rw [e1, e2, e3]
  rfl

/-- **A segment's Z3 first claim is `c0Z`** (`targetS` at `targetSSegS`: the point is Z1's
coordinates, zeros, then `lastOps`' bits, so P4c's `peL_seg` applies). -/
theorem z3_head_seg4 {σ : SegKind} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl (.ofSeg σ) inp tr y)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofSeg σ).tix r = Rev4.targetSSegS r)
    (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F) :
    rd (#[] ++ y.1.toArray) (cAt4 seq4 (.ofSeg σ) 5).uni =
      .f (P4a.c0Z (P4a.zlm4 indN etN) (fsOf tr (itemsOf seq4))) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, -, h133, -, -, -, hseg⟩ := uni_view4 h hn4 (by rw [e4])
  have hnode : (KindP.ofSeg σ).d.node = false := by cases σ <;> rfl
  obtain ⟨-, hpe⟩ := hseg hnode
  have hpe' := hpe (segPt_lt _ h.ref (by norm_num) (by decide))
  rw [uni_cAt5, hout]
  simp only [hnode, Bool.false_eq_true, ite_false, List.getD_cons_succ, List.getD_cons_zero] at h133 ⊢
  rw [h133]
  refine congrArg Val.f (lag_c0Z h hLS _ ?_)
  -- the point
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, [], #[]⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs := rfl
  have hR := extA_refl (#[] ++ y.1.toArray)
  have hsp : segPtRegs seq4 (.ofSeg σ) (cAt4 seq4 (.ofSeg σ) 4).outs =
      (coordsR fi "Z1").take ((KindP.ofSeg σ).d.m - 13) ++
        List.replicate (seq4.mStar - (KindP.ofSeg σ).d.m) (zeroReg fi) ++ lastRegs fi := by
    rw [segPtRegs, cAt4_outs seq4 _ (by norm_num) (by decide), cAt4_outs seq4 _ (by norm_num) (by decide)]
    rfl
  have hk := kindOfC_seg4 h
  have hm : (KindP.ofSeg σ).d.m = σ.m := (dims_seg4 σ).2.2
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  have hle : σ.m - 13 ≤ 2 * 10 := by cases σ <;> decide
  have hco := coordsR_view4 h hfi hR hn3 (by rw [e3]) (by norm_num) phaseIx_vals.1 hle
  rw [show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  obtain ⟨hL, hz⟩ := lastRegs_view4 h hfi hR
  have hpe2 : pe = ((List.range (σ.m - 13)).map (coordAt (fsOf tr (itemsOf seq4)) 2) ++
      List.replicate (32 - σ.m) 0 ++ P4a.lastBits (fsOf tr (itemsOf seq4))).toArray := by
    rw [hpe', hsp, hm, hmS]
    simp only [List.map_append, List.map_replicate]
    rw [show (fun x => (rd (#[] ++ y.1.toArray) x).toF) = fv (#[] ++ y.1.toArray) from rfl, hco, show (rd (#[] ++ y.1.toArray) (zeroReg fi)).toF = 0 from hz, hL]
    rfl
  rw [hTS, hpe2]
  have hlen : ((List.range (σ.m - 13)).map (coordAt (fsOf tr (itemsOf seq4)) 2) ++
      List.replicate (32 - σ.m) 0).length = 19 := by simp; cases σ <;> rfl
  refine P4a.peL_seg (by rw [hk]; rfl) (fun l hl => ?_) (fun l h1 h2 => ?_) ?_
  · rw [hk] at hl; change l < σ.m - 13 at hl
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.append_assoc,
      List.getElem?_append_left (by simpa using hl), List.getElem?_map, List.getElem?_range hl]
    rfl
  · rw [hk] at h1; change σ.m - 13 ≤ l at h1
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_append_left (by rw [hlen]; exact h2),
      List.getElem?_append_right (by simpa using h1), List.getElem?_replicate]
    split_ifs <;> rfl
  · exact lastAt_pad19 _ _ hlen

/-- **A node's Z3 first claim is `c0Z`** (`targetS` at `targetSNode4S`, S-CN4's `peL_node4`; the
point is Z1's packed register). -/
theorem z3_head_node4 {ν : NodeKind} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl (.ofNode ν) inp tr y)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r) :
    rd (#[] ++ y.1.toArray) (cAt4 seq4 (.ofNode ν) 5).uni =
      .f (P4a.c0Z (P4a.zlm4 N4c.indN4 N4c.etN4) (fsOf tr (itemsOf seq4))) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, -, h133, -, -, hnd, -⟩ := uni_view4 h hn4 (by rw [e4])
  have hnode : (KindP.ofNode ν).d.node = true := by cases ν <;> rfl
  have hpe := hnd hnode
  rw [uni_cAt5, hout]
  simp only [hnode, ite_true, List.getD_cons_succ, List.getD_cons_zero] at h133 ⊢
  rw [h133]
  refine congrArg Val.f (lag_c0Z h hLS _ ?_)
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  obtain ⟨-, hco⟩ := coords_pt_view4 h hn3 (by rw [e3]) (by norm_num)
  rw [hTS, hpe, pt_cAt4]
  refine CN4.peL_node4 (kindOfC_node4 h) fun l hl => ?_
  have hl' : l < 2 * 10 := by have : NT4.nbN ν ≤ 18 := by cases ν <;> decide
                              omega
  rw [hco l hl', show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl]
  rfl

/-! ## `finZ` on the fields; Z3's last claim (`RejZ`) -/

theorem rest_gFinZ (P : FinP) :
    (finalsOf P).rest[0]'(by rw [rest_finalsOf_length]; decide) = gFinZ P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_zero]

/-- `finZ`'s registers are named or `zhat` registers (abstract `fi`). -/
theorem hin_Z {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) :
    ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" P.S.z3 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | rfl | rfl | rfl
  · exact hsk "Z1" x (List.mem_of_mem_drop hx)
  · exact hsk "Z3" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact getLastD_lt (hsk "Z3") hn
  · exact getD_lt hn (hsk "Z2") 2
  · exact getD_lt hn hz 0

/-- **`finZ`'s relation on the fields of an accepted run** (field 0, file `Rs 0`). -/
theorem relZ4_of_fields {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relZ4 p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩ (Rs 0) P = true := by
  obtain ⟨-, L0, hL0, -, -⟩ := hF.fld 0 (by decide)
  rw [rest_gFinZ] at hL0
  obtain ⟨L', hL'⟩ := flag_gFinZ impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩ (Rs 0) P
    (hin_Z (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide)))
  exact pureRun_det hL0 hL'

theorem clR_c0_eq {c0 c0' : Log → Log → F} {L es : Log} (hc : c0 L es = c0' L es) (b : ℕ) :
    ∀ n, clR b c0 L es n = clR b c0' L es n
  | 0 => hc
  | n + 1 => by simp only [clR, clR_c0_eq hc b n]

/-- **Z3's last claim on the fields** (`relZ4` (i) through the views), for any kind whose `m` the
finals and the chain agree on, from Z3's first claim `c0Z M`. -/
theorem z_chk4 {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
    (hPS : P.S = seq4) (hm : P.kv.m p.tix = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (hz3 : p.d.seq.z3 = (kindOfC (fsOf tr (itemsOf seq4))).m - 6)
    (M : P4a.ZLM4) (hc : rd (#[] ++ y.1.toArray) (cAt4 seq4 p 5).uni = .f (P4a.c0Z M (fsOf tr (itemsOf seq4))))
    (L : Log) :
    clR 15 (fun _ es => P4a.c0Z M es) L (fsOf tr (itemsOf seq4)) (P4a.mC 6 (kindOfC (fsOf tr (itemsOf seq4)))) =
      eq (ptOf (P4a.mC 6 (kindOfC (fsOf tr (itemsOf seq4)))) (P4a.zrL (fsOf tr (itemsOf seq4))))
          (ptOf (P4a.mC 6 (kindOfC (fsOf tr (itemsOf seq4)))) (P4a.rZ (fsOf tr (itemsOf seq4)))) *
        (vZ (fsOf tr (itemsOf seq4)) 0 * vZ (fsOf tr (itemsOf seq4)) 1) := by
  have hrel := relZ4_of_fields hF
  simp only [relZ4, hm, hPS, Bool.and_eq_true] at hrel
  have h1 := val_eqv_f4 hrel.1
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 0 (by decide)
  have hκ := CKind.m_mem κ
  obtain ⟨hn5, e5⟩ := ph4 (n := 5) (x := ("Z3", Sh.rounds fZ3 seq4.z3 3 false)) rfl
  obtain ⟨hcl, hcv, -, hlt, hlast⟩ := roundsF3_view4 hF.sk hn5 (by rw [e5]) L
  rw [e5, (initClaim_vals).1] at hcv
  rw [hcv] at hlast
  have hN := hlast _ hc
  have hle : p.d.seq.z3 ≤ seq4.z3 := by rw [hz3, seq4_eq]; show κ.m - 6 ≤ 26; omega
  rw [e5, (realRounds_vals _ _).1, Nat.min_eq_left hle, hz3,
    show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hN
  rw [(outsOf_skel hfi "Z3").2.2, phaseIx4_rounds.2.1, hE.rd hlt, hN] at h1
  rw [P4a.mC, clR_c0_eq (c0' := fun _ _ => P4a.c0Z M es) rfl, Val.f.inj h1]
  -- the right-hand side
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 hF.sk hfi hE hn3 (by rw [e3]) (by norm_num) phaseIx_vals.1
    (a := κ.m - 13) (by omega)
  rw [show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  have hch := chals_view4 hF.sk hfi hE hn5 (by rw [e5]) phaseIx4_rounds.2.1 (a := κ.m - 6)
    (by rw [seq4_eq]; show κ.m - 6 ≤ 26; omega)
  rw [show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hch
  have htk : (chals fi "Z3" seq4.z3).take (κ.m - 6) = chals fi "Z3" (κ.m - 6) := by
    rw [chals, chals, List.take_take, Nat.min_eq_left (by rw [seq4_eq]; show κ.m - 6 ≤ 26; omega)]
  have hm1 := fsMsgs4_front.1
  have hv : ∀ j < 2, vZ es j = pe4 seq4 inp fZend (16 * j) := fun j hj => by
    rw [vZ, msg_abs4 hF.sk (by norm_num) (by norm_num) hm1 (by omega)]; rfl
  rw [htk, hco, hch, FR.Impl.eqPoint_eq, hv 0 (by norm_num), hv 1 (by norm_num)]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hl, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray, List.length_append, List.length_ofFn,
    List.length_map, List.length_range, show 7 + (κ.m - 13) = κ.m - 6 by omega, mul_assoc]
  rfl

/-- **`RejZ` never holds on an accepted segment run** (`lagrangeS`, `targetS` at their
specifications; `M` the segment's `zlm4`). -/
theorem not_rejZ_seg4 {σ : SegKind} {tr : Trace}
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofSeg σ).tix r = Rev4.targetSSegS r)
    (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejZ (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have hk := kindOfC_seg4 hF.sk
  exact fun ⟨_, hne⟩ => hne (z_chk4 hF rfl (by rw [hk]; rfl) (by rw [hk, (dims_seg4 σ).1]) _
    (z3_head_seg4 hF.sk hLS hTS indN etN) L)

/-- **… nor on an accepted node run** (`targetS` at `targetSNode4S`: the node's `tS`, a parameter
until `targetSNode4I`). -/
theorem not_rejZ_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejZ (P4a.zlm4 N4c.indN4 N4c.etN4) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have hk := kindOfC_node4 hF.sk
  exact fun ⟨_, hne⟩ => hne (z_chk4 hF rfl (by rw [hk]; rfl) (by rw [hk, (dims_node4 ν).1]) _
    (z3_head_node4 hF.sk hLS hTS) L)

end FR.Snd.R4

end G6_FRSoundness4R4FrZ

section G6_FRSoundness4R4FrLc

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finLc` (ii), A.10 L3; stage R4e).
-- RET-2: import re-pointed at Core: `FRSoundnessFrLc` → `FRSoundnessCoreWalk`.

/-!
# L2's last claim on an accepted run (P4a's `RejLc2`, `RejLcN`)

3.x's `lc_ii_run` at `gen4`: `relLc4` (ii) on the fields (**`relLc4_of_fields`**) through the views
(L2's last claim from its head `c0L`, `λ`, `α`, `r′_hi`, `r_k`, L3's values `vL`), and 3.x's walk
bridge `lc_bridge` with `walkAB`, `rowW`, `eqZ` at their specifications (parameters `hW hR hZ`, as
3.x's): **`lc_ii4`**, L2's last claim is `Σ_j v′_j M̃_j(r_k)`, `v′` the kind-masked values
(P4a's `vM`). **`not_rejLc_seg4`**, **`not_rejLc_node4`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **`finLc`'s relation on the fields of an accepted run** (field 1, file `Rs 1`). -/
theorem relLc4_of_fields {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relLc4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ (Rs 1) P = true := by
  obtain ⟨-, L1, hL1, -, -⟩ := hF.fld 1 (by decide)
  rw [rest_gFinLc] at hL1
  obtain ⟨L', hL'⟩ := flag_gFinLc impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ (Rs 1) P
    (hin_Lc (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide)))
  exact pureRun_det hL1 hL'

/-- L3's values on the log are the program's reads. -/
theorem lcV4_eq {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {P : FinP} (hP : P.S = seq4) :
    lcV4 inp P = (List.range 8).map (vL (fsOf tr (itemsOf seq4))) := by
  unfold lcV4
  rw [phaseIx_L3, hP]
  refine List.map_congr_left fun i hi => ?_
  have hi8 := List.mem_range.1 hi
  rw [vL, msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_front.2 (by omega), pe4, Nat.add_assoc]

/-- **L2's last claim on the fields of an accepted run** (3.x's `lc_ii_run` at `gen4`): for
`walkAB`, `rowW`, `eqZ` at their specifications and a kind flag the finals and the chain agree on,
it is the per-kind lincheck sum. -/
theorem lc_ii4 (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
    (hPS : P.S = seq4) (hnode : P.kv.node p.tix = p.tix.isNode)
    (hκ : (kindOfC (fsOf tr (itemsOf seq4))).isNode = p.tix.isNode)
    (M : P4a.ZLM4) (hA : M.Ak = zlmFR.Ak) (hB : M.Bk = zlmFR.Bk) (L : Log) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr (itemsOf seq4)) 14 =
      ∑ j, P4a.vM (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) j *
        mle (linM (M.Ak j) (M.Bk j) (P4a.rwL (fsOf tr (itemsOf seq4))) (alL (fsOf tr (itemsOf seq4))))
          (ptOf 14 (rkL (fsOf tr (itemsOf seq4)))) := by
  have hrel := relLc4_of_fields hF
  simp only [relLc4, Bool.and_eq_true, hPS] at hrel
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 1 (by decide)
  have hS := hF.sk
  -- L2's head and last claims
  have hc0 := val_eqv_f4 hrel.1.1
  have h3 := val_eqv_f4 hrel.2
  obtain ⟨hn8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) rfl
  obtain ⟨hn7, e7⟩ := ph4 (n := 7) (x := ("L1", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hα⟩ := one_name_view4 hS hfi hE hn7 (by rw [e7]) phaseIx_vals.2.2.2.1
  rw [show phStart4 7 = 68 by rw [phStart4, fsStarts4_eq]; rfl] at hα
  obtain ⟨hcl, -, -, hlt, hlast⟩ := roundsF2_view4 hS hn8 (by rw [e8]) L
  rw [(outsOf_skel hfi "L2").2.1, phaseIx4_rounds.2.2.1] at hc0
  rw [← hE.rd hcl, hc0] at hlast
  obtain ⟨hN, -⟩ := hlast _ rfl
  rw [e8, (realRounds_vals _ _).2.2.2.2.2, Nat.min_self,
    show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hN
  rw [(outsOf_skel hfi "L2").2.2, phaseIx4_rounds.2.2.1, hE.rd hlt, hN, Val.f.injEq] at h3
  have hc0L : pe4 seq4 inp fZend 0 + fv (Rs 1) ((outsOf fi "L1").headD 0) * pe4 seq4 inp fZend 16 =
      c0L es := by
    have hm := fsMsgs4_front.1
    rw [hα, c0L, alL, vZ, vZ, msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num),
      msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num)]
    rfl
  rw [clR2_c0_eq (c0' := fun _ _ => pe4 seq4 inp fZend 0 +
    fv (Rs 1) ((outsOf fi "L1").headD 0) * pe4 seq4 inp fZend 16) hc0L.symm, h3]
  -- the views
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, hlam, -⟩ := uni_view4 hS hn4 (by rw [e4])
  have hlm : fv (Rs 1) ((outsOf fi "Z2").headD 0) = lamL es := by
    rw [(outsOf_skel hfi "Z2").1, phaseIx4_rounds.1, hout, List.headD_cons]
    have hlt' := (hF.sk_lt (k := 1) (by decide) (Ex 1) "Z2")
    show (rd (Rs 1) _).toF = _
    rw [hE.rd (by
      have := skeleton4_out_lt p hS.ref 4 (b + (if p.d.node = true then 0 else 1) + 3)
        (by rw [hout]; simp)
      exact this), hlam, show phStart4 4 + 1 = 14 by rw [phStart4, fsStarts4_eq]; rfl]
    rfl
  obtain ⟨hn5, e5⟩ := ph4 (n := 5) (x := ("Z3", Sh.rounds fZ3 seq4.z3 3 false)) rfl
  have hz8 := chals_view4 hS hfi hE hn5 (by rw [e5]) phaseIx4_rounds.2.1 (a := 8) (by rw [seq4_eq]; decide)
  rw [show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hz8
  have htk : (chals fi "Z3" P.S.z3).take 8 = chals fi "Z3" 8 := by
    rw [hPS]
    rw [chals, chals, List.take_take, Nat.min_eq_left (by rw [seq4_eq]; decide)]
  have hrhi : lcRhi4 fi (Rs 1) P = (rchs 15 es 8).toArray := by
    rw [lcRhi4, htk, hz8]
  have hrhi8 : (lcRhi4 fi (Rs 1) P).size = 8 := by rw [hrhi]; simp [rchs]
  have hκm := CKind.m_mem (kindOfC es)
  have hrhiL : ptA 8 (lcRhi4 fi (Rs 1) P) = P4a.rhiL es := by
    rw [hrhi, ptA_toArray]
    funext i
    simp only [P4a.rhiL, P4a.rZ, ptOf, rchs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range i.isLt, List.getElem?_range (show i.val < P4a.mC 6 (kindOfC es) by
        unfold P4a.mC; omega)]
  have hch := chals_view4 hS hfi hE hn8 (by rw [e8]) phaseIx4_rounds.2.2.1 (a := 14) le_rfl
  rw [show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hch
  have hrk : lcRk fi (Rs 1) = rkL es := by rw [lcRk, hch]; rfl
  have hv := lcV4_eq hS hPS
  have hv8 : (lcV4 inp P).length = 8 := by simp [lcV4]
  have hrkl : (lcRk fi (Rs 1)).length = 14 := by rw [hrk]; simp [rkL, rchs]
  have hb := lc_bridge hW hR hZ p.tix (v := lcV4 inp P) hv8 (lcVf4 p.tix inp P)
    (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (fv (Rs 1) ((outsOf fi "L1").headD 0)) (lcRhi4 fi (Rs 1) P)
    hrhi8 (lcRk fi (Rs 1)) hrkl
  simp only at hb
  have hlhs : lcWalk4 impl p.tix inp fi (Rs 1) P + (lcFree4 impl p.tix inp fi (Rs 1) P +
      fv (Rs 1) ((outsOf fi "L1").headD 0) * lcFree4 impl p.tix inp fi (Rs 1) P) =
      (impl.walkAB (maskRows (lcWts p.tix (lcV4 inp P)).toArray
          (impl.rowW (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (lcRhi4 fi (Rs 1) P)))
          (eqTab (lcRk fi (Rs 1)).toArray)).1 +
        fv (Rs 1) ((outsOf fi "L1").headD 0) * (impl.walkAB (maskRows (lcWts p.tix (lcV4 inp P)).toArray
          (impl.rowW (fv (Rs 1) ((outsOf fi "Z2").headD 0)) (lcRhi4 fi (Rs 1) P)))
          (eqTab (lcRk fi (Rs 1)).toArray)).2 +
        (lcVf4 p.tix inp P * (dotAcc 0 (impl.eqZ (fv (Rs 1) ((outsOf fi "Z2").headD 0)) 0)
            (eqTab ((lcRk fi (Rs 1)).take 6).toArray) 64 *
          eqPoint (lcRhi4 fi (Rs 1) P) ((lcRk fi (Rs 1)).drop 6).toArray) +
         fv (Rs 1) ((outsOf fi "L1").headD 0) * (lcVf4 p.tix inp P *
          (dotAcc 0 (impl.eqZ (fv (Rs 1) ((outsOf fi "Z2").headD 0)) 0)
            (eqTab ((lcRk fi (Rs 1)).take 6).toArray) 64 *
          eqPoint (lcRhi4 fi (Rs 1) P) ((lcRk fi (Rs 1)).drop 6).toArray))) := by
    simp only [lcWalk4, lcFree4, lcRk, lcWts, List.map_take, List.map_drop, hnode]
  rw [hlhs, hb, hlm, hα, hrhiL, hrk, hA, hB]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lcWts_vM p.tix hv8 _ (by simp only [lcVf4, hnode]; split <;> simp [lcV4]), hv]
  simp only [P4a.vM, hκ]
  split
  · split
    · rfl
    · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp only [List.getElem_map, List.getElem_range]; rfl
  · split
    · rw [List.getD_eq_getElem _ _ (by simp)]; simp only [List.getElem_map, List.getElem_range]; rfl
    · rfl

/-- **`RejLc2`, `RejLcN` never hold on an accepted segment run** (`walkAB`, `rowW`, `eqZ` at their
specifications; `M` a `zlm4`). -/
theorem not_rejLc_seg4 (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {σ : SegKind} {tr : Trace} (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejLc2 (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) ∧
      ¬ P4a.RejLcN (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have e := lc_ii4 hW hR hZ hF rfl rfl (by rw [kindOfC_seg4 hF.sk]; rfl) (P4a.zlm4 indN etN) rfl rfl L
  exact ⟨fun ⟨_, _, hne⟩ => hne e, fun ⟨_, _, hne⟩ => hne e⟩

/-- **… nor on an accepted node run.** -/
theorem not_rejLc_node4 (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = rowWS l a) (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    {ν : NodeKind} {cells : List ℕ} {tr : Trace} (indN : NodeKind → Fin 9 → ℕ → F)
    (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejLc2 (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) ∧
      ¬ P4a.RejLcN (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have e := lc_ii4 hW hR hZ hF rfl rfl (by rw [kindOfC_node4 hF.sk]; rfl) (P4a.zlm4 indN etN) rfl rfl L
  exact ⟨fun ⟨_, _, hne⟩ => hne e, fun ⟨_, _, hne⟩ => hne e⟩

end FR.Snd.R4

end G6_FRSoundness4R4FrLc

section G6_FRSoundness4R4FrRS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS` and the claims' bindings; stage R4e).

/-!
# RS0's claim values and their bindings on an accepted run (P4b's `RejRS4`)

* **`rs_alpha4`**: `finRS`'s exported value `α_j` (the `zhat` register `j`) is P4b's `alphaL4 κ es j`:
  RS0's slices are the log's message at 326 (`msg_abs4`), the inner weights `rsW4` are `cwL4`
  (`eqZ` at `eqZS`, parameter `hZ`; L2's and S2's challenges by the views).
* **The bindings on the same registers**: Z's `α_Z = P^z*(λ)` (`relZ4` (ii), `lagrangeS`'s second
  value, **`z_bind4`**), Lc's `α_Lc = v_β` (`relLc4` (iii), **`lc_bind4`**), Sh's (`sh_bind_*`),
  E's `α_E` = E4 end's value (`relE4`, **`e_bind4`**).
* **`not_rejRS4_seg`**, **`not_rejRS4_node`**: `¬ RejRS4 (okRS4 oZ oLc4 (oSh4 wNS))`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

section F
variable {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
  {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- A `zhat` register reads the same in every file. -/
theorem Fields4.fv_zh (hF : Fields4 impl p inp tr P y zh Rs Ex) {k : ℕ} (hk : k ≤ 12) (j : ℕ) :
    fv (Rs k) (zh.getD j 0) = fv (Rs 0) (zh.getD j 0) := by
  show (rd (Rs k) _).toF = (rd (Rs 0) _).toF
  rw [(hF.chain (Nat.zero_le k) hk).rd (getD_lt (lt_of_lt_of_le (hF.pos (by decide)) le_rfl) hF.zlt j)]

/-- `finRS`'s registers are named registers (abstract `fi`). -/
theorem hin_RS {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (κ : Kind) (P : FinP) : ∀ x ∈ rsRefs4 κ fi P, x < n := by
  intro x hx
  simp only [rsRefs4, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ((⟨q, -, rfl⟩ | rfl) | hx) | hx
  · exact getD_lt hn (fun x hx => hsk "RS1" x (List.mem_of_mem_drop hx)) _
  · exact headD_lt (hsk "Z2") hn
  · exact hsk "L2" x (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take hx)))
  · exact hsk "S2" x (List.mem_of_mem_drop (List.mem_of_mem_take
      (List.mem_of_mem_drop (List.mem_of_mem_take hx))))

/-- **`finRS`'s exports hold `rsAlpha4`** on the skeleton's file. -/
theorem rs_vals4 (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    ∀ j < 4, fv (Rs 0) (zh.getD j 0) =
      rsAlpha4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray) P j := by
  obtain ⟨L₀, hL₀, h0⟩ := hF.rs
  obtain ⟨L, hL, hv, -⟩ := exec_gFinRS impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
    (#[] ++ y.1.toArray) P (hin_RS (fun name x hx => outsOf_lt4 hF.sk [] #[] name x hx)
      (skel_pos4 hF.sk) _ P)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hL₀.symm.trans hL))
  intro j hj
  rw [h0, hF.zh_eq]
  exact hv j hj

end F

/-! ## The claim values are `alphaL4` -/

section V
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
  {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **Z2's `λ` by name** is `lamL`. -/
theorem lam_view4 : fv R ((outsOf fi "Z2").headD 0) = lamL (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, hlam, -⟩ := uni_view4 h hn4 (by rw [e4])
  rw [(outsOf_skel hfi "Z2").1, phaseIx4_rounds.1, hout, List.headD_cons]
  show (rd R _).toF = _
  rw [hR.rd (skeleton4_out_lt p h.ref 4 (b + (if p.d.node = true then 0 else 1) + 3) (by rw [hout]; simp)),
    hlam, show phStart4 4 + 1 = 14 by rw [phStart4, fsStarts4_eq]; rfl]
  rfl

end V

/-- **Claim `j`'s value is `alphaL4`** (for `eqZ` at `eqZS` and a kind whose `m` the finals and
the chain agree on). -/
theorem rs_alpha4 (hZ : ∀ a b, impl.eqZ a b = eqZS a b) {tr : Trace} {P : FinP}
    {y : List Val × List Bool × Trace} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4)
    (hm : P.kv.m p.tix = (kindOfC (fsOf tr (itemsOf seq4))).m) (j : Fin 4)
    (hj : j.val < (P4b.rsPtsL4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4))).length) :
    P4b.alphaL4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) j = fv (Rs 0) (zh.getD j 0) := by
  rw [rs_vals4 hF j j.isLt, rsAlpha4, P4b.alphaL4, ← Fin.sum_univ_eq_sum_range]
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hR := extA_refl (#[] ++ y.1.toArray)
  have hS := hF.sk
  have hκ := CKind.m_mem (kindOfC es)
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : P4b.sL4 (kindOfC es) es j i = sv4 P.S inp j i := by
    rw [P4b.sL4, if_pos hj, P4b.sliceL4, hPS,
      msg_abs4 hS (by norm_num) (by norm_num) fsMsgs4_ends.2.2.2 (by
        have := i.isLt; have := j.isLt; simp only [rsOff]; omega)]
    rfl
  rw [hs]
  refine congrArg (· * _) ?_
  -- the inner weights
  obtain ⟨n8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) rfl
  have hch := chals_view4 hS hfi hR n8 (by rw [e8]) phaseIx4_rounds.2.2.1 (a := 14) le_rfl
  rw [show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hch
  have hle : P.kv.m p.tix - 14 ≤ 18 := by rw [hm]; omega
  obtain ⟨-, hrp⟩ := s2r_view4 hS hfi hR hle
  rcases j with ⟨_ | _ | _ | _ | j, hj4⟩
  · simp only [rsW4, P4b.cwL4, cwF]
    rw [hZ, lam_view4 hS hfi hR]; rfl
  · simp only [rsW4, P4b.cwL4, cwF]
    rw [ptF, List.map_take, hch]
    rfl
  · simp only [rsW4, P4b.cwL4, cwF]
    have e7 : ((chals fi "S2" P.S.s2).drop (P.kv.m p.tix - 14)).take 7 =
        (((chals fi "S2" seq4.s2).drop (P.kv.m p.tix - 14)).take 10).take 7 := by
      rw [hPS, List.take_take]; rfl
    rw [ptF, e7, List.map_take, hrp]
    simp only [P4b.xSL4, ← hm, ← List.map_take, List.take_range]
    rfl
  · simp only [rsW4, P4b.cwL4, cwF]
  · omega

/-! ## The bindings on the fields -/

section B
variable {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
  {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **Z's binding** (`relZ4` (ii)): `α_Z = P^z*(λ)` (`lagrangeS`'s second value at its
specification). -/
theorem z_bind4 (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    P4a.oZ (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 0) (zh.getD 0 0)) := by
  have hrel := relZ4_of_fields hF
  simp only [relZ4, Bool.and_eq_true] at hrel
  have h2 := hrel.2
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 0 (by decide)
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, -, -, h134, hmsg, -, -⟩ := uni_view4 hF.sk hn4 (by rw [e4])
  have h13 : phStart4 4 = 13 := by rw [phStart4, fsStarts4_eq]; rfl
  rw [h13] at hmsg h134
  have hreg : (outsOf fi "Z2").getD 2 0 = b + (if p.d.node = true then 0 else 1) + 134 := by
    rw [(outsOf_skel hfi "Z2").1, phaseIx4_rounds.1, hout]; rfl
  rw [hreg, hE.rd (skeleton4_out_lt p hF.sk.ref 4 _ (by rw [hout]; simp)), h134,
    hLS _ _ _ (by simp [uniEs]), Impl.lagrangeSS] at h2
  have e1 : (fun k : Fin 64 => (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD k 0) =
      pzL (fsOf tr (itemsOf seq4)) := funext fun k => by
    simp only [pzL]; rw [hmsg k (by omega)]
    simp [uniEs, Array.getD_eq_getD_getElem?, List.getElem?_range (show k.val < 127 by omega)]
  rw [P4a.oZ, fv, val_eqv_f4 h2, pzStar]
  simp only [Val.toF, e1]
  rfl

/-- **Lc's binding** (`relLc4` (iii)): `α_Lc = v_β` (L3's values batched by `β`). -/
theorem lc_bind4 (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) :
    P4a.oLc4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 1) (zh.getD 1 0)) := by
  have hrel := relLc4_of_fields hF
  simp only [relLc4, Bool.and_eq_true] at hrel
  have h2 := val_eqv_f4 hrel.1.2
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 1 (by decide)
  obtain ⟨hn10, e10⟩ := ph4 (n := 10) (x := ("L3β", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hβ⟩ := one_name_view4 hF.sk hfi hE hn10 (by rw [e10]) phaseIx_vals.2.2.2.2.2.1
  rw [show phStart4 10 = 98 by rw [phStart4, fsStarts4_eq]; rfl] at hβ
  rw [P4a.oLc4, fv]
  show (rd (Rs 1) (zh.getD 1 0)).toF = _
  rw [h2, lcV4_eq hF.sk hPS, hβ, vBetaL]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil, List.drop_succ_cons,
    List.drop_zero, List.foldl_cons, List.foldl_nil, List.getD_cons_succ, List.getD_cons_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, vL, Val.toF, List.singleton_append]
  ring

/-- **`finE`'s relation on the fields of an accepted run** (field 4, file `Rs 4`; `lrEx` are
`finLr`'s exports). -/
theorem relE4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relE4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩ (Rs 4) P = true := by
  obtain ⟨hs3, L3, hL3, he3, hx3⟩ := hF.fld 3 (by decide)
  obtain ⟨-, L4, hL4, -, -⟩ := hF.fld 4 (by decide)
  rw [rest_gFinLr] at hL3 hx3
  rw [rest_gFinE] at hL4
  have hl3 := pureRun_len impl p.tix inp _ _ [] _ _ hL3
  rw [opsOut_gFinLr, List.length_nil, Nat.zero_add] at hl3
  have hsz4 : (Rs 4).size = (Rs 3).size + 14 := by rw [he3]; simp [hl3]
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩
  have hlr : ∀ j, lrEx fi j = (gFinLr P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3).size).2.getD j 0 :=
    lrEx_eq4 hs3 _ fi hx3
  obtain ⟨LE, hLE, -⟩ := flag_gFinE impl p.tix inp fi (Rs 4) P
    (hin_E (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide))
      (by rw [hlr]; show (Rs 3).size + 13 < _; omega) (by rw [hlr]; show (Rs 3).size + 4 < _; omega))
  exact pureRun_det hL4 hLE

/-- **`finE`'s exports after `r′` on the fields** (the reserve, RSV2 §2.2): the 60 registers
`finB′` reads hold the child claim's values, Lrend's reads at `48 + 16 i`. -/
theorem rsvEx_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    ∀ i < rsvN, P.rsvOps = true →
      fv (Rs 5) ((((Ex 5).getD exE []).drop 1).getD i 0) = pe4 P.S inp fLrEnd (48 + 16 * i) := by
  obtain ⟨hs3, L3, hL3, he3, hx3⟩ := hF.fld 3 (by decide)
  obtain ⟨hs4, L4, hL4, he4, hx4⟩ := hF.fld 4 (by decide)
  rw [rest_gFinLr] at hL3 hx3
  rw [rest_gFinE] at hL4 hx4
  have hl3 := pureRun_len impl p.tix inp _ _ [] _ _ hL3
  rw [opsOut_gFinLr, List.length_nil, Nat.zero_add] at hl3
  have hsz4 : (Rs 4).size = (Rs 3).size + 14 := by rw [he3]; simp [hl3]
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩
  have hlr : ∀ j, lrEx fi j = (gFinLr P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3).size).2.getD j 0 :=
    lrEx_eq4 hs3 _ fi hx3
  obtain ⟨LE, hLE, -, hv⟩ := flag_gFinE impl p.tix inp fi (Rs 4) P
    (hin_E (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide))
      (by rw [hlr]; show (Rs 3).size + 13 < _; omega) (by rw [hlr]; show (Rs 3).size + 4 < _; omega))
  have hLL : L4 = LE := by
    have e := hL4.symm.trans hLE
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    exact e.1
  intro i hi hr
  have hfx : (Ex 5).getD exE [] = (gFinE P fi (Rs 4).size).2 := by
    rw [hx4, exE, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs4, if_pos rfl, Option.getD_some]
  rw [hfx, he4, hLL]
  have e := hv i hi hr
  show (rd _ _).toF = _
  rw [e]; rfl

/-- **E's binding** (`relE4`'s `e4`): `α_E` is E4 end's value. -/
theorem e_bind4 (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) :
    P4b.okE4 (fsOf tr (itemsOf seq4)) (fv (Rs 4) (zh.getD 3 0)) := by
  have hrel := relE4_of_fields hF
  have he4 : ((Val.f (pe4 P.S inp fE (gOE4end P.S))).eqv (rd (Rs 4) (zh.getD 3 0)) &&
      (inp.π.extract (fieldOffOf P.S fE + (gOE4end P.S + 16))
        (fieldOffOf P.S fE + (gOE4end P.S + 16) + 16)).data.all (· == 0)) = true := by
    revert hrel; simp only [relE4, relE4o]; split <;> (try split) <;> simp_all
  simp only [Bool.and_eq_true] at he4
  rw [P4b.okE4, fv, val_eqv_f4 he4.1, hPS,
    msg_abs4 hF.sk (by norm_num) (by norm_num) fsMsgs4_ends.2.2.1 (by norm_num), Nat.add_zero]
  rfl

end B

/-! ## `RejRS4` -/

/-- **`RejRS4` never holds on an accepted segment run** (`eqZ`, `lagrangeS`, `shiftTarget`,
`shiftMask`, `slotW`, `linkWAll` at the segment's specifications): every claim's value from RS0's
slices meets its binding (Z's `oZ`, Lc's `oLc4`, Sh's `oSh4 wNS` at `wSumSeg`). -/
theorem not_rejRS4_seg {σ : SegKind} {tr : Trace}
    (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = shiftSegS a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0)
    (wNS : CKind → Log → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4b.RejRS4 (P4b.okRS4 P4a.oZ P4a.oLc4 (P4a.oSh4 wNS)) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have hk := kindOfC_seg4 hF.sk
  rintro ⟨-, j, hj, hne⟩
  apply hne
  rw [rs_alpha4 hZ hF rfl (by rw [hk]; rfl) j hj]
  rw [P4b.rsPtsL4_length, hk] at hj
  rcases j with ⟨_ | _ | _ | j, hj4⟩
  · exact z_bind4 hLS hF
  · rw [← hF.fv_zh (k := 1) (by decide)]; exact lc_bind4 hF rfl
  · rw [← hF.fv_zh (k := 2) (by decide)]; exact sh_bind_seg4 hST hSM hSW hLW hF wNS
  · simp only [CKind.isNode, Bool.false_eq_true, ite_false] at hj; omega

/-- **… nor on an accepted node run** (the node ops at `specN4`; Sh's binding at `wNS4`, E's
`okE4`). -/
theorem not_rejRS4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hZ : ∀ a b, impl.eqZ a b = eqZS a b)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejRS4 (P4b.okRS4 P4a.oZ P4a.oLc4 (P4a.oSh4 P4a.wNS4)) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have hk := kindOfC_node4 hF.sk
  rintro ⟨-, j, hj, hne⟩
  apply hne
  rw [rs_alpha4 hZ hF rfl (by rw [hk]; rfl) j hj]
  rcases j with ⟨_ | _ | _ | _ | j, hj4⟩
  · exact z_bind4 hLS hF
  · rw [← hF.fv_zh (k := 1) (by decide)]; exact lc_bind4 hF rfl
  · rw [← hF.fv_zh (k := 2) (by decide)]; exact sh_bind_node4 hST hSM hSW hLW hF
  · rw [← hF.fv_zh (k := 4) (by decide)]; exact e_bind4 hF rfl
  · omega

end FR.Snd.R4

end G6_FRSoundness4R4FrRS
