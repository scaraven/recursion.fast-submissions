-- lvm6 X9 (X8a F-X8a-3): the builder `sbIR` meets `SbOkW` with `S = sbSpec`. X8a's one-piece proof timed out;
-- here it is four lemmas: the head (prologue, table, flag clear), the lane loop, the output, the assembly. New.
import Lvm6XDescSb

/-!
# The builder meets `SbOkW`

* **`sbHead_sem`**: after the prologue, `wtabNIR` and the flag clear: `q = 0`, the word's base and row stride in
  `bBase`/`bOcc`, the sources kept (`SrcEq`), the basis table (`TabOk`), every flag zero.
* **`sbLanes_sem`**: the lane loop (`loopK_runLe` over `laneB_sem`) runs `occ ≤ K` lanes: `FlagInv … occ`.
* **`sbIR_okW`**: with the listing (`scanIR_sem`) and `sbSpec_eq`, the builder meets
  `SbOkW I (sbIR …) B ℓ (sbSpec M₀ …) (PreB M₀ B ℓ r)`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

attribute [local irreducible] entryK storeM

/-- The builder's head: prologue, basis table, flag clear. -/
def sbHead (N ℓ B tS : ℕ) : XIR := .seq (sIR (sbPro tS)) (.seq (wtabNIR N (tbA' B ℓ)) (zeroIR (2 ^ ℓ) (flA B ℓ)))

theorem semXIR_sbIR (I : Array Word) (N ℓ B colB str d tS K : ℕ) (s : St) :
    semXIR I (sbIR N ℓ B colB str d tS K) s = semXIR I (scanIR ℓ B d)
      (semXIR I (.loopK bC1 bOcc (toWord K) (laneB N ℓ B colB str d)) (semXIR I (sbHead N ℓ B tS) s)) := by
  simp only [sbIR, sbHead, semXIR_seq]

theorem hasOut_sbIR (N ℓ B colB str d tS K : ℕ) : hasOut (sbIR N ℓ B colB str d tS K) = false := by
  simp [sbIR, laneB, scanIR, scanBody, cmpBody, sbPro, hasOut, hasOut_sIR, mcpLoop, mcpBody, zeroIR, zeroBody,
    hasOut_wtabNIR', hasOut_fwdNIR']

/-- **The head**: `q = 0`, base and row stride loaded, sources kept, the table written, the flags zero. -/
theorem sbHead_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B tS r : ℕ} (M₀ : Mem) (hN : N ≤ 64)
    (hN1 : 1 ≤ N) (hB : regs ≤ B) (hE : fdEnd B ℓ < 2 ^ 64) (hsz : fdEnd B ℓ ≤ s.M.size)
    (hNN : N * N ≤ 8 * 2 ^ ℓ) (hR : rd s.M xR = toWord r) (hS : SrcEq M₀ B ℓ s.M)
    (hT1 : OutB B ℓ (tS + 2 * r)) (hT2 : OutB B ℓ (tS + 2 * r + 1)) (hT3 : tS + 2 * r + 1 < 2 ^ 64) :
    let t := semXIR I (sbHead N ℓ B tS) s
    Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M bQ = toWord 0 ∧ rd t.M bBase = toWord (tbBase M₀ tS r) ∧
      rd t.M bOcc = toWord (tbOcc M₀ tS r) ∧ SrcEq M₀ B ℓ t.M ∧ TabOk N B ℓ t.M ∧
      ∀ j < 2 ^ ℓ, rd t.M (flA B ℓ + j) = 0 := by
  intro t
  have hs := hM.1
  have eS : sA B = B + 4096 := rfl
  have eF : flA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eT : tbA' B ℓ = B + 4096 + 2 ^ ℓ + 2 * 2 ^ ℓ := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have hL : 2 ^ ℓ < 2 ^ 64 := by omega
  simp only [regs] at hB hs
  have hT1' := hT1
  simp only [OutB, regs] at hT1'
  obtain ⟨p0, p1, p2, p3⟩ := sbPro_run (tS := tS) (rd s.M) (rd s.M) hR (hM.2 0 (by decide)) (by omega)
    (by simp only [regs]; omega)
  obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd s.M) (sbPro tS) s (rd s.M) hM (ok_sbPro tS) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) p0
  have eB : rd s.M (r + r + tS) = toWord (tbBase M₀ tS r) := by
    rw [show r + r + tS = tS + 2 * r by ring, hS _ hT1.1 hT1.2, tbBase, toWord_toNat]
  have eO : rd s.M (r + r + tS + 1) = toWord (tbOcc M₀ tS r) := by
    rw [show r + r + tS + 1 = tS + 2 * r + 1 by ring, hS _ hT2.1 hT2.2, tbOcc, toWord_toNat]
  have hBa1 := (a1 bBase (trkB (by decide) (by decide))).trans (p1.trans eB)
  have hO1 := (a1 bOcc (trkB (by decide) (by decide))).trans (p2.trans eO)
  have hQ1 := (a1 bQ (trkB (by decide) (by decide))).trans p3
  have z1 := size_sIR I (sbPro tS) s
  simp only [t, sbHead, semXIR_seq]
  generalize semXIR I (sIR (sbPro tS)) s = s1 at a1 a2 a3 hBa1 hO1 hQ1 z1
  obtain ⟨w1, w2, w3, w4⟩ := wtabNIR_sem I s1 a3 hN hN1 (tb := tbA' B ℓ) (by simp only [regs]; omega)
    (by omega) (by omega)
  have k2 : ∀ x, 187 ≤ x → x < 256 → rd (semXIR I (wtabNIR N (tbA' B ℓ)) s1).M x = rd s1.M x := fun x h1 h2 ↦
    keepHi I (wf_wtabNIR ..) (allBelow_wtabNIR ..) s1 a3 h1 h2
  generalize semXIR I (wtabNIR N (tbA' B ℓ)) s1 = s2 at w1 w2 w3 w4 k2
  obtain ⟨c1, c2, c3⟩ := zeroIR_sem I s2 w3 (n := 2 ^ ℓ) (dst := flA B ℓ) hL (by simp only [regs]; omega)
    (by omega) (by omega)
  have k3 : ∀ x, 187 ≤ x → x < 256 → rd (semXIR I (zeroIR (2 ^ ℓ) (flA B ℓ)) s2).M x = rd s2.M x :=
    fun x h1 h2 ↦ keepHi I (wf_zeroIR ..) (allBelow_mono (by decide) (allBelow_zeroIR ..)) s2 w3 h1 h2
  have z3 := size_sem I (zeroIR (2 ^ ℓ) (flA B ℓ)) s2
  generalize semXIR I (zeroIR (2 ^ ℓ) (flA B ℓ)) s2 = s3 at c1 c2 c3 k3 z3
  have g3 : ∀ x, 190 ≤ x → x < 256 → rd s3.M x = rd s1.M x := fun x h1 h2 ↦ by
    rw [k3 x (by omega) h2, k2 x (by omega) h2]
  refine ⟨c3, by rw [z3, w4, z1], ?_, ?_, ?_, fun x hx hx' ↦ ?_, fun v hv i hi ↦ ?_, fun j hj ↦ c1 j hj⟩
  · rw [g3 _ (by decide) (by decide), hQ1]
  · rw [g3 _ (by decide) (by decide), hBa1]
  · rw [g3 _ (by decide) (by decide), hO1]
  · simp only [regs] at hx
    rw [c2 x (by simp only [regs]; omega) (by omega), w2 x (by simp only [regs]; omega) (by omega),
      a2 x (by simp only [regs]; omega), hS x (by simp only [regs]; omega) hx']
  · have := w1 v hv i hi
    simp only [rdK] at this ⊢
    rw [c2 _ (by simp only [regs]; omega) (by omega), this]

/-- **The lane loop**: from the head's state, `occ ≤ K` lanes; afterwards flag `j` is zero iff every lane agrees. -/
theorem sbLanes_sem (I : Array Word) (t : St) (hM : Inv t.M) {N ℓ B colB str d tS r K : ℕ} (M₀ : Mem)
    (hN : N ≤ 64) (hℓN : ℓ ≤ N) (hB : regs ≤ B) (hE : fdEnd B ℓ < 2 ^ 64) (hsz : fdEnd B ℓ ≤ t.M.size)
    (hNN : N * N ≤ 8 * 2 ^ ℓ) (hd : d + 1 ≤ 2 ^ ℓ) (hK : K < 2 ^ 64) (hoK : tbOcc M₀ tS r ≤ K)
    (hW : ∀ q < tbOcc M₀ tS r, ∀ j < 2 ^ ℓ, OutB B ℓ (tbBase M₀ tS r + q + tbOcc M₀ tS r * j) ∧
      tbBase M₀ tS r + q + tbOcc M₀ tS r * j < 2 ^ 64)
    (hC : ∀ q < tbOcc M₀ tS r, (∀ x < d + 1, OutB B ℓ (colB + str * q + x)) ∧ colB + str * q + (d + 1) < 2 ^ 64)
    (hQ : rd t.M bQ = toWord 0) (hBa : rd t.M bBase = toWord (tbBase M₀ tS r))
    (hO : rd t.M bOcc = toWord (tbOcc M₀ tS r)) (hS : SrcEq M₀ B ℓ t.M) (hT : TabOk N B ℓ t.M)
    (hF : ∀ j < 2 ^ ℓ, rd t.M (flA B ℓ + j) = 0) :
    let t' := semXIR I (.loopK bC1 bOcc (toWord K) (laneB N ℓ B colB str d)) t
    Inv t'.M ∧ t'.M.size = t.M.size ∧ SrcEq M₀ B ℓ t'.M ∧
      FlagInv M₀ N ℓ B colB str d tS r (tbOcc M₀ tS r) t'.M := by
  intro t'
  have hs := hM.1
  simp only [regs] at hB hs
  let Q : ℕ → St → Prop := fun q u ↦ Inv u.M ∧ u.M.size = t.M.size ∧ rd u.M bQ = toWord q ∧
    rd u.M bBase = toWord (tbBase M₀ tS r) ∧ rd u.M bOcc = toWord (tbOcc M₀ tS r) ∧ SrcEq M₀ B ℓ u.M ∧
    TabOk N B ℓ u.M ∧ FlagInv M₀ N ℓ B colB str d tS r q u.M
  have hE0 : ∀ i, i ≠ bC1 → i ≠ cTmp → rd (entryK bC1 bOcc (toWord K) t.M) i = rd t.M i :=
    fun i h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hH0 : ∀ x, regs ≤ x → rd (entryK bC1 bOcc (toWord K) t.M) x = rd t.M x := fun x hx ↦
    hE0 x (by simp only [regs, bC1] at hx ⊢; omega) (by simp only [regs, cTmp] at hx ⊢; omega)
  have h0 : Q 0 ⟨entryK bC1 bOcc (toWord K) t.M, t.o⟩ := by
    refine ⟨inv_entryK hM (by decide), by simp only [size_entryK], ?_, ?_, ?_, hS.of_heap hH0,
      hT.of_heap (by simp only [regs]; omega) hH0, fun j hj ↦ ?_⟩ <;> dsimp only
    · rw [hE0 _ (by decide) (by decide), hQ]
    · rw [hE0 _ (by decide) (by decide), hBa]
    · rw [hE0 _ (by decide) (by decide), hO]
    · refine ⟨fun _ q' hq' ↦ absurd hq' (Nat.not_lt_zero _), fun _ ↦ ?_⟩
      rw [hH0 _ (by simp only [regs, flA, yA]; omega), hF j hj]
  have hstep : ∀ q u, q < tbOcc M₀ tS r → Q q u →
      Q (q + 1) (decS bC1 (semXIR I (laneB N ℓ B colB str d) u)) := by
    rintro q u hq ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
    obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := laneB_sem I u i1 M₀ hN hℓN (by simp only [regs]; omega) hE
      (by omega) hNN hd (hW q hq) (hC q hq).1 (hC q hq).2 i3 i4 i5 i6 i7 i8
    have hh : ∀ x, regs ≤ x → rd (decS bC1 (semXIR I (laneB N ℓ B colB str d) u)).M x =
        rd (semXIR I (laneB N ℓ B colB str d) u).M x := fun x hx ↦
      rd_decS (by simp only [regs, bC1] at hx ⊢; omega) _
    refine ⟨inv_decS l1 (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_, l5.of_heap hh,
      l6.of_heap (by simp only [regs]; omega) hh, l7.of_heap (by simp only [regs]; omega) hh⟩
    · rw [rd_decS (by decide), l2]
    · rw [rd_decS (by decide), l3, i4]
    · rw [rd_decS (by decide), l4, i5]
  obtain ⟨g1, g2, -, -, -, g6, -, g8⟩ := loopK_runLe I (laneB N ℓ B colB str d) Q t hM (c := bC1) (n := bOcc)
    (m := tbOcc M₀ tS r) (K := K) (by decide) (by decide) (by decide) (by decide) hO hoK hK h0 hstep
  exact ⟨g1, g2, g6, g8⟩

open Classical in
/-- **The agreement-set builder meets `SbOkW`** with `S = sbSpec M₀ …` (the first `d + 3` positions where every
lane `q < occ` encodes to the round's folded word), from `PreB M₀ B ℓ r`: the round's table entry, the folded word
and the columns lie outside the scratch, `occ ≤ K`, `d + 3 ≤ 2^ℓ`, the basis table fits the scratch. -/
theorem sbIR_okW (I : Array Word) {N ℓ B colB str d tS K r : ℕ} (M₀ : Mem) (hN : N ≤ 64) (hN1 : 1 ≤ N)
    (hℓN : ℓ ≤ N) (hB : regs ≤ B) (hE : fdEnd B ℓ < 2 ^ 64) (hNN : N * N ≤ 8 * 2 ^ ℓ) (hd : d + 3 ≤ 2 ^ ℓ)
    (hK : K < 2 ^ 64) (hoK : tbOcc M₀ tS r ≤ K)
    (hT1 : OutB B ℓ (tS + 2 * r)) (hT2 : OutB B ℓ (tS + 2 * r + 1)) (hT3 : tS + 2 * r + 1 < 2 ^ 64)
    (hW : ∀ q < tbOcc M₀ tS r, ∀ j < 2 ^ ℓ, OutB B ℓ (tbBase M₀ tS r + q + tbOcc M₀ tS r * j) ∧
      tbBase M₀ tS r + q + tbOcc M₀ tS r * j < 2 ^ 64)
    (hC : ∀ q < tbOcc M₀ tS r, (∀ x < d + 1, OutB B ℓ (colB + str * q + x)) ∧ colB + str * q + (d + 1) < 2 ^ 64) :
    SbOkW I (sbIR N ℓ B colB str d tS K) B ℓ (sbSpec M₀ N ℓ colB str d tS r) (PreB M₀ B ℓ r) := by
  rintro s ⟨hR, hS⟩ hM hsz
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := sbHead_sem I s hM M₀ hN hN1 hB hE hsz hNN hR hS hT1 hT2 hT3
    (N := N) (ℓ := ℓ) (tS := tS)
  have hsz1 : fdEnd B ℓ ≤ (semXIR I (sbHead N ℓ B tS) s).M.size := by rw [a2]; exact hsz
  obtain ⟨g1, g2, g6, g8⟩ := sbLanes_sem I _ a1 M₀ hN hℓN hB hE hsz1 hNN (by omega) hK hoK hW hC a3 a4 a5 a6 a7
    a8 (colB := colB) (str := str) (d := d)
  have hsz2 : fdEnd B ℓ ≤ (semXIR I (.loopK bC1 bOcc (toWord K) (laneB N ℓ B colB str d))
      (semXIR I (sbHead N ℓ B tS) s)).M.size := by rw [g2]; exact hsz1
  have hG : ∀ j < 2 ^ ℓ, rd (semXIR I (.loopK bC1 bOcc (toWord K) (laneB N ℓ B colB str d))
      (semXIR I (sbHead N ℓ B tS) s)).M (flA B ℓ + j) = 0 ↔
      (fun j ↦ @decide (GoodB M₀ N ℓ colB str d tS r j) (Classical.propDecidable _)) j = true := fun j hj ↦
    (g8 j hj).trans (@decide_eq_true_iff (GoodB M₀ N ℓ colB str d tS r j) (Classical.propDecidable _)).symm
  obtain ⟨d1, d2, d3⟩ := scanIR_sem I _ g1 _ hB hE hsz2 hd hG
  rw [sbSpec_eq, semXIR_sbIR]
  refine ⟨d2, d1, ?_, fun x hx hx' ↦ ?_⟩
  · rw [← semXIR_sbIR]; exact sem_o I _ s (hasOut_sbIR ..)
  · have hdE : sA B + (d + 3) ≤ fdEnd B ℓ := by simp only [sA, fdEnd]; omega
    rw [d3 x hx (by omega), g6 x hx hx', hS x hx hx']

/-- A lane of the builder within `2^(ℓ + 13)` (`ℓ ≤ 21`, `N = ℓ + 1`). -/
theorem laneBCost_le {ℓ d : ℕ} (hℓ : ℓ ≤ 21) (hd : d + 1 ≤ 2 ^ ℓ) : laneBCost (ℓ + 1) ℓ d + 3 ≤ 2 ^ (ℓ + 13) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · unfold laneBCost
    norm_num at hd ⊢
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    have hP : 2 ^ (k + 1 + 13) = 16384 * 2 ^ k := by rw [pow_add, pow_succ]; ring
    have hP1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hH : k + 1 - 1 = k := by omega
    unfold laneBCost
    rw [hH, hP, hP1]
    rw [hP1] at hd
    generalize 2 ^ k = H at hd ⊢
    have h1 : (67 + 20 * (k + 1 + 1)) * H ≤ 507 * H := Nat.mul_le_mul_right H (by omega)
    have h2 : (k + 1) * ((67 + 20 * (k + 1 + 1)) * H + 27) ≤ 21 * (507 * H + 27) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

/-- **The builder within X9's affine cap** (`ℓ ≤ 21`, `N = ℓ + 1`, `d + 1 ≤ 2^ℓ`): `sbCost ≤ 2^27 + K·2^(ℓ + 13)`, so
`cost (sbIR …) ≤ sbCap i n` at level `i` (`ℓ = ht6 i`) whenever its lane bound `K ≤ n`. -/
theorem sbCost_le {ℓ d K : ℕ} (hℓ : ℓ ≤ 21) (hd : d + 1 ≤ 2 ^ ℓ) :
    sbCost (ℓ + 1) ℓ d K ≤ 2 ^ 27 + K * 2 ^ (ℓ + 13) := by
  have hL := laneBCost_le hℓ hd
  have hP : 2 ^ ℓ ≤ 2097152 := (Nat.pow_le_pow_right (by norm_num) hℓ).trans (by norm_num)
  have hF : (ℓ + 1 - 1) * (1077 + 45 * (ℓ + 1)) ≤ 21 * 2067 := Nat.mul_le_mul (by omega) (by omega)
  have := Nat.mul_le_mul_left K hL
  have e : (2 : ℕ) ^ 27 = 134217728 := by norm_num
  unfold sbCost
  rw [e]
  omega

end Lvm6.X
