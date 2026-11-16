-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iii)): what M′'s extractor `EXM` returns on an `S` proof.
-- Adapted from `LvmXSpec.lean` (`den_S`, `EX_leaf`, `EX_node_out`, `okXIR_sem`, and the `C_rec` node theorem
-- `EX_node` removed in roll 11) at M′'s program `decXM` (`LvmMPXTop`): the chain through `C_main`'s folds
-- (`chainLM_spec`), the three column reads (`readGIR_sem`), the copies, the three decoders (`decMP2IR_sem`,
-- `decMP1IR_sem`, `decMP0IRW_sem`), the stream block and the node output (`outIR_sem`).
import LvmMPXComputes
import LvmMPXLayout
import LvmMPXDec1Sem
import LvmXRead1
import LvmMPXRead

-- ===== merged from `LvmMPXChain` (GOLF module merge: `LvmMPXChain.lean` is now a stub importing `LvmMPXNodeSem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (i)): the chain scan's specification through `C_main`'s fold
-- challenges. Adapted from `LvmXChainL.lean` (`msgL_ok`, `msgL_last`, `chTabL_getD`, `tabW_chTabL`, `chainL_spec`) at
-- the table `chTabM` (`nChainM pX = 1319` targets, `LvmMPXLayout`).

/-!
# `chainLM_spec`

On a domain tape of an `S` proof whose log has no state hit, for every position `p < nChainM pX` that the first-match
chain answers with `a`, the machine's answer at `ansB + 4p` is `a`'s four words; the heap outside the chain's region
is kept.
-/

namespace Lvm.X

open RecursionFast Lvm

theorem msgsM_ok : ((fsMsgs pX).take (nChainM pX - 1)).all msgOkL = true :=
  layoutM_P20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem nChainM_le : nChainM pX - 1 ≤ (fsMsgs pX).length := by
  rw [nChainM_eq, layoutM_P20.2.2.2.2.2.2.2.2.2.1]; decide

theorem msgLM_ok {p : ℕ} (hp0 : 0 < p) (hp : p < nChainM pX) :
    (msgL p).1 % 8 = 0 ∧ (msgL p).2 % 8 = 0 ∧ (msgL p).1 + (msgL p).2 ≤ piSize pX ∧
      32 + (msgL p).2 ≤ queryCap := by
  have hl := nChainM_le
  have hm : (fsMsgs pX)[p - 1]'(by omega) ∈ (fsMsgs pX).take (nChainM pX - 1) :=
    List.mem_iff_getElem.mpr ⟨p - 1, by simp; omega, by simp⟩
  have h := List.all_eq_true.mp msgsM_ok _ hm
  unfold msgL
  rw [List.getD_eq_getElem _ _ (by (clear * - hp0 hp hl; omega))]
  simp only [msgOkL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem msgLM_last : (msgL (nChainM pX)).1 = 286136 := by
  -- from `layoutM_P20`'s `resOffM` (no second kernel evaluation of `fsMsgs pX`)
  have h : resOffM pX = 286184 := layoutM_P20.2.2.2.2.2.2.2.2.1
  rw [resOffM, eBytes] at h
  rw [msgL]
  omega

theorem chTabM_getD {p k : ℕ} (hp : p ≤ nChainM pX) (hk : k < 4) :
    chTabM.getD (4 * p + k) 0 = (tabEntL p).getD k 0 :=
  getD_flatMap4 tabEntL tabEntL_length _ p k (by (clear * - hp; omega)) hk

/-- **The table realises `V_S`'s chain** through `C_main`'s folds. -/
theorem tabW_chTabM (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) :
    TabW (extractorInput c π L).toArray (fsQL π) (nChainM pX) chTabM := by
  have hp1 : π.size = 332336 := hs.trans piSize_eq
  refine ⟨chTabM_length, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTabM_getD hpN (by norm_num), tabEntL, if_neg (by (clear * - hp0; omega))]
    show (toWord (5 + (msgL p).1 / 8)).toNat < 2 ^ 62
    have : (msgL p).1 ≤ 332336 := by
      rcases Nat.lt_or_ge p (nChainM pX) with h | h
      · have := (msgLM_ok hp0 h).2.2.1; rw [piSize_eq] at this; (clear * - this; omega)
      · have hpe : p = nChainM pX := by (clear * - hpN h; omega)
        rw [hpe, msgLM_last]; (clear * -; omega)
    generalize msgL p = m at this
    rw [toNat_toWord (by (clear * - this; omega))]; (clear * - this; omega)
  · obtain ⟨ho, hl, hol, hq⟩ := msgLM_ok hp0 hpN'
    have e0 := chTabM_getD hpN (k := 0) (by norm_num)
    have e1 := chTabM_getD hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntL, if_neg (by (clear * - hp0; omega))]
    have hz : (fsQL π p st).size = 32 + (msgL p).2 := by
      rw [fsQL, if_neg (by (clear * - hp0; omega)), ByteArray.size_append, extract_size π (by (clear * - hs hp1 ho hl hol; omega)), digestBytes_size]
    refine ⟨by rw [hz]; rfl, by rw [hz]; (clear * - hs hp1 ho hl hol; omega), fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQL_data p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msgL p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · rw [piSize_eq] at hol
      generalize msgL p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by (clear * - ho; omega)⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by (clear * - hl; omega)⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by (clear * - h4 hj hol; omega)), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by (clear * -; omega),
        tape_getD_proof c π L (by rw [hp1]; (clear * - h4 hj hol; omega)), ← List.getD_eq_getElem _ 0,
        extract_words π (by rw [hp1]; omega) (by (clear * - h4 hj; omega))]

/-- **`chainLM_spec`**: the machine's chain answers are the first-match chain's. -/
theorem chainLM_spec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nChainM pX, ∀ a, fmAns (fsQL π) zeroDL L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray chainLM s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray chainLM s).M y = rd s.M y) := by
  have hT : ∀ p st, 0 < p → stateIn (fsQL π p st) = some st := fun p st hp => stateIn_fsQL π hp st
  obtain ⟨-, hans, hheap⟩ := chainIR_sem c π L (hs_posL hs) hq ht (N := nChainM pX)
    (by rw [nChainM_eq]; norm_num) (tabW_chTabM c π L hs) (seedOK_sdL _) (st₀ := zeroDL)
    (by simp [fsQL, q0Query, ByteArray.size, q0Bytes]) s hM hsz
  refine ⟨fun p hp a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nChainM pX) (st₀ := zeroDL) hT hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nChainM pX) (st₀ := zeroDL) (L := L) (T := fsQL π) hT hS).1
  have hpl : p < (scanC (fsQL π) (nChainM pX) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQL π) (nChainM pX) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [show chainLM = chainIR (posL (piSize pX)) (nChainM pX) chTabM sdL from rfl, hans p hpl m hm, hg]

end Lvm.X
end
-- ===== end of `LvmMPXChain` =====

-- ===== merged from `LvmMPXDec0Sem` (GOLF module merge: `LvmMPXDec0Sem.lean` is now a stub importing `LvmMPXNodeSem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X): the level-0 decoder program `decMP0IR N nL kL lo C` computes
-- `decodeG0 N nL kL lo C`. Adapted from `LvmXDecIR2.lean` (`DecLay`), `LvmXCopy.lean` (`msgRow_sem`, `rowsIR_sem`),
-- `LvmXDecIR3.lean` (`decTail_sem`), `LvmXDecIR4.lean` (`decIR_sem`) and this slice's `LvmMPXDec1Sem` (`enc1MC_sem`,
-- `enc1MIR_sem`): `2^15` positions → `2^nL`, `2^13` coefficients → `2^kL`, 64 decoded rows → the window `[lo, lo + C)`.

/-!
# The level-0 decoder on the machine, generic in the shape

**`decMP0IR_sem`**: on a memory holding the word `wd` at `wB + 64 q + t` (`q < 2^nL`), `α_i` at `aB + 3i` (`i < 6`)
and `f(v)` at `fB + 3v` (`rdE`), with the layout `DecM0Lay`:

* the cell `okM dB` holds `[2^kL ≤ |agreeG nL kL wd α f|]`, i.e. `decodeG0 N nL kL lo C wd α f ≠ none`;
* if `decodeG0 N nL kL lo C wd α f = some out`, the `C·2^kL` cells at `mM` hold `out`;
* the heap outside the workspace is kept.

`decMP0IRW_sem`: M′'s level 0 (`decodeMP0`, lanes 40–47); `decMP0Lay_example`: a layout below `2^26`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-0 decoder's memory layout** at `(N, nL, kL, lo, C)`: the workspace `[dB, dB + wsM nL kL C)`; the
word (`wB`, `64·2^nL` words, plus the interpolation's overreach of `64` words), `α` (`aB`, 18 words) and `f` (`fB`,
`3·2^kL`) outside it; addresses below `2^60`. -/
structure DecM0Lay (N nL kL lo C dB wB aB fB sz : ℕ) : Prop where
  hN : N ≤ 64
  hN1 : 1 ≤ N
  hkn : kL ≤ nL
  hnN : nL ≤ N
  hlo : lo + C ≤ 64
  r : regs ≤ dB
  t : dB + wsM nL kL C < 2 ^ 60
  z : dB + wsM nL kL C ≤ sz
  rW : regs ≤ wB
  tW : wB + 64 * 2 ^ nL + 64 < 2 ^ 60
  dW : wB + 64 * 2 ^ nL + 64 ≤ dB ∨ dB + wsM nL kL C ≤ wB
  rA : regs ≤ aB
  tA : aB + 18 < 2 ^ 60
  dA : aB + 18 ≤ dB ∨ dB + wsM nL kL C ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ kL < 2 ^ 60
  dF : fB + 3 * 2 ^ kL ≤ dB ∨ dB + wsM nL kL C ≤ fB

/-- The arithmetic facts of the layout, as linear facts on the atoms `2^kL`, `2^nL`, `C·2^kL`. -/
theorem DecM0Lay.facts {N nL kL lo C dB wB aB fB sz : ℕ} (hL : DecM0Lay N nL kL lo C dB wB aB fB sz) :
    0 < 2 ^ kL ∧ 2 ^ kL ≤ 2 ^ nL ∧ 2 ^ (kL + 1) = 2 * 2 ^ kL ∧ C * 2 ^ kL ≤ 64 * 2 ^ kL ∧
      N * N ≤ 2 ^ 12 ∧ kL < 61 ∧ nL < 61 ∧ wsM nL kL C = 2 ^ 13 + 2 * 2 ^ kL + 5 * 2 ^ nL + 2 * (C * 2 ^ kL) := by
  have h1 := hL.hN
  have hkn := hL.hkn
  have hk := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hL.hkn
  have hNN : N * N ≤ 64 * 64 := Nat.mul_le_mul h1 h1
  have hn : nL < 61 := by
    have := hL.tW
    by_contra h
    have : 2 ^ 61 ≤ 2 ^ nL := Nat.pow_le_pow_right (by norm_num) (by (clear * - h; omega))
    omega
  refine ⟨by positivity, hk, by ring, Nat.mul_le_mul_right _ (by have := hL.hlo; (clear * - this; omega)), by omega, by (clear * - hkn hn; omega),
    hn, ?_⟩
  rw [wsM, pow_succ]; ring

/-! ## `Enc(f)` (the programs are `LvmMPXDec1Sem`'s with the level-0 layout) -/

/-- **One coordinate of `Enc(f)`** at `encM + c·2^nL`. -/
theorem encMC_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB c : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (hc : c < 3) (hT : TabOkN N s.M dB) :
    (∀ j < 2 ^ nL, rdK (semXIR I (encMC N nL kL dB fB c) s).M (encM nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encM nL kL dB + c * 2 ^ nL ∨ encM nL kL dB + c * 2 ^ nL + 2 ^ nL ≤ x) →
      rd (semXIR I (encMC N nL kL dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (encMC N nL kL dB fB c) s).M := by
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  have hc2 : c * 2 ^ nL + 2 ^ nL ≤ 3 * 2 ^ nL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by (clear * - hc; omega))
  set A := encM nL kL dB + c * 2 ^ nL with hA
  have hAd : dB + 2 ^ 12 ≤ A ∧ A + 2 ^ nL ≤ dB + wsM nL kL C := by
    simp only [hA, encM, agM]; constructor <;> (clear * - hCK hws hc2; omega)
  rw [encMC, tbM, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ kL) (src := fB + c) (str := 3) (dst := A)
    (pow_lt64 (by (clear * - hk61; omega))) (by (clear * - hc tF; omega)) (by norm_num) (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - hkn' hCK hws r t rF tF hAd; omega)) (by (clear * - hkn' hws z hAd; omega))
    (fun i hi => by (clear * - hc hkn' hws dF hAd hi; omega)) (fun i hi => by simp only [regs]; (clear * - hc rF; omega))
  have z1 := size_sem I (mcpIR (2 ^ kL) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ kL) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ nL - 2 ^ kL) (dst := A + 2 ^ kL)
    (by (clear * - k0 hkn' hCK hws r t rF tF hAd; omega)) (by simp only [regs]; (clear * - hCK hws r t rW tW hAd; omega)) (by (clear * - hkn' hws t hAd; omega)) (by (clear * - hkn' hws z hAd z1; omega))
  have z2 := size_sem I (zeroIR (2 ^ nL - 2 ^ kL) (A + 2 ^ kL)) s1
  generalize semXIR I (zeroIR (2 ^ nL - 2 ^ kL) (A + 2 ^ kL)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; (clear * - hs z1 z2; omega))]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; (clear * - hx; omega))
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ nL ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by (clear * - k0 hkn' rF tF hx2; omega)), m2 x hx (by (clear * - hkn' hx2; omega))]
  have hT3 : TabOkN N s3.M dB := tabOkN_congr hT fun x h1 h2 => h3 x (by simp only [regs] at *; (clear * - hNN r h1 h2; omega))
    (by (clear * - hNN hAd h1 h2; omega))
  have hY : ∀ i < 2 ^ nL, rdK s3.M (A + i) =
      if h : i < 2 ^ kL then (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; (clear * - r hAd; omega))]
    by_cases h : i < 2 ^ kL
    · rw [dif_pos h, n2 _ (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - h; omega)), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ kL + (i - 2 ^ kL) by (clear * - h; omega), n1 _ (by (clear * - hkn' hi h; omega))]; rfl
  have hfe := fwdNIR_enc I s3 hM3 hN (A := A) (tb := dB) (ℓ := nL) (m := kL) hnN hkn
    (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - hws t hAd; omega)) (by (clear * - hws z hAd z1 z2 z3; omega)) (by simp only [regs]; omega)
    (by (clear * - hNN hws t; omega)) (by (clear * - hNN hAd; omega)) a3 hT3 (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdNIR_sem I s3 hM3 hN (A := A) (tb := dB) (ℓ := nL)
    (Y := fun i => rdK s3.M (A + i)) hnN (by simp only [regs]; (clear * - r hAd; omega)) (by (clear * - hws t hAd; omega)) (by (clear * - hws z hAd z1 z2 z3; omega))
    (by simp only [regs]; omega) (by (clear * - hNN hws t; omega)) (by (clear * - hNN hAd; omega)) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc(f)`'s three coordinates** at `encM + c·2^nL + j`. -/
theorem encMIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (hT : TabOkN N s.M dB) :
    (∀ c < 3, ∀ j < 2 ^ nL, rdK (semXIR I (encMIR N nL kL dB fB) s).M (encM nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encM nL kL dB ∨ encM nL kL dB + 3 * 2 ^ nL ≤ x) →
      rd (semXIR I (encMIR N nL kL dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (encMIR N nL kL dB fB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rF
  rw [encMIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := encMC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (encMC N nL kL dB fB 0) s
  generalize semXIR I (encMC N nL kL dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : DecM0Lay N nL kL lo C dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < encM nL kL dB ∨ encM nL kL dB + 2 ^ nL ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs] at *; (clear * - hNN r h1 h2; omega)) (by simp only [encM, agM] at *; (clear * - hCK hNN hws t rW tW h1 h2; omega))
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := encMC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (encMC N nL kL dB fB 1) s1
  generalize semXIR I (encMC N nL kL dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : DecM0Lay N nL kL lo C dB wB aB fB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs] at *; (clear * - hNN r h1 h2; omega)) (by simp only [encM, agM] at *; (clear * - hCK hNN hws t h1 h2; omega))
  obtain ⟨c1, c2, hM3⟩ := encMC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ kL → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < encM nL kL dB ∨ encM nL kL dB + 3 * 2 ^ nL ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, encM, agM] at *; (clear * - hCK hws r t rF dF hx hc; omega)
  have ee1 : ∀ x : Fin (2 ^ kL), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by (clear * - h2; omega))]
  have ee2 : ∀ x : Fin (2 ^ kL), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by (clear * - h2; omega))]; exact ee1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encM, agM] at *; (clear * - hCK hws r; omega)) (by simp only [encM, agM] at *; (clear * - hj; omega)),
        b2 _ (by simp only [regs, encM, agM] at *; (clear * - hCK hws r; omega)) (by simp only [encM, agM] at *; (clear * - hj; omega))]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encM, agM] at *; (clear * - hCK hws r; omega)) (by simp only [encM, agM] at *; (clear * - hj; omega))]
      rw [show wK (rd s2.M (encM nL kL dB + 1 * 2 ^ nL + j)) = rdK s2.M (encM nL kL dB + 1 * 2 ^ nL + j)
        from rfl, b1 j hj]
      congr 1; funext x; exact ee1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact ee2 x 2 (by norm_num)
  · rw [c2 x hx (by (clear * - hx2; omega)), b2 x hx (by (clear * - hx2; omega)), a2 x hx (by (clear * - hx2; omega))]

/-! ## The reorder -/

/-- **One message row** `l < C`: `mB + l·2^kL + v := oB + (C − 1 − l)·2^kL + v`, `yL := l + 1`. -/
theorem msgRowM_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL C oB mB l : ℕ} (hk : kL < 64) (hC : C < 2 ^ 64) (hl : l < C)
    (hoB : regs ≤ oB) (hoB2 : oB + C * 2 ^ kL < 2 ^ 64) (hmB : regs ≤ mB) (hmB2 : mB + C * 2 ^ kL < 2 ^ 64)
    (hms : mB + C * 2 ^ kL ≤ s.M.size) (hdisj : oB + C * 2 ^ kL ≤ mB ∨ mB + C * 2 ^ kL ≤ oB)
    (hL : rd s.M yL = toWord l) :
    (∀ v < 2 ^ kL, rd (semXIR I (msgRowM kL C oB mB) s).M (mB + l * 2 ^ kL + v) =
      rd s.M (oB + (C - 1 - l) * 2 ^ kL + v)) ∧
    rd (semXIR I (msgRowM kL C oB mB) s).M yL = toWord (l + 1) ∧
    (∀ r, regs ≤ r → (r < mB + l * 2 ^ kL ∨ mB + l * 2 ^ kL + 2 ^ kL ≤ r) →
      rd (semXIR I (msgRowM kL C oB mB) s).M r = rd s.M r) ∧
    Inv (semXIR I (msgRowM kL C oB mB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hoB hmB
  have hK0 : 0 < 2 ^ kL := by positivity
  have hl2 : l * 2 ^ kL + 2 ^ kL ≤ C * 2 ^ kL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
  have hl3 : (C - 1 - l) * 2 ^ kL + 2 ^ kL ≤ C * 2 ^ kL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by (clear * - hl; omega))
  rw [msgRowM, semXIR_seq]
  set ps : List Prim := [.const yK (toWord (C - 1)), .op .sub ySr yK yL, .const yK (toWord (2 ^ kL)),
    .op .mul ySr ySr yK, .const yK (toWord oB), .op .add ySr ySr yK, .const yK (toWord (2 ^ kL)),
    .op .mul yDs yL yK, .const yK (toWord mB), .op .add yDs yDs yK, .const yStr 1] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (oB + (C - 1 - l) * 2 ^ kL) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (mB + l * 2 ^ kL) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord 1 ∧ rd (semXIR I (.blk ps) s).M yL = toWord l := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yK, ySr, yDs, yStr, yL]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hL, sub_toWord (by (clear * - hC hl; omega)) (by (clear * - hC hl; omega)),
        mul_toWord, add_toWord, Nat.add_comm]
    · rw [hL, mul_toWord, add_toWord, Nat.add_comm]
    · rfl
    · exact hL
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk ps) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, yK, ySr, yDs, yStr] <;> (clear * - hr; omega)
  generalize semXIR I (.blk ps) s = s0 at hM0 z0 r0 k0
  obtain ⟨p1, p2, p3, p4⟩ := r0
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpLoop_sem I s0 hM0 (n := 2 ^ kL) (src := oB + (C - 1 - l) * 2 ^ kL)
    (str := 1) (dst := mB + l * 2 ^ kL) (pow_lt64 hk) (by (clear * - hoB2 hl3; omega)) (by simp only [regs]; (clear * - hmB; omega))
    (by (clear * - hmB2 hl2; omega)) (by (clear * - hms hl2 z0; omega)) (fun i hi => by (clear * - hdisj hl2 hl3 hi; omega)) (fun i hi => by simp only [regs]; (clear * - hoB; omega)) p1 p2 p3
  have z1 := size_sem I (mcpLoop (2 ^ kL)) s0
  have l1 : rd (semXIR I (mcpLoop (2 ^ kL)) s0).M yL = toWord l := by
    rw [frame I _ s0 (by simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yV, yN,
      yC, cTmp, regs]) hM0 yL (by decide) (by simp +decide [mcpLoop, mcpBody, Writes, Prim.dst,
        ySr, yDs, yV, yN, yC, yL, cTmp]), p4]
  generalize semXIR I (mcpLoop (2 ^ kL)) s0 = s1 at m1 m2 hM1 z1 l1
  have b2 : ∀ r, r ≠ yL → rd (semXIR I (.blk [.op .add yL yL cOne]) s1).M r = rd s1.M r :=
    fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
  have hx : ∀ x, regs ≤ x → x ≠ yL := fun x hx => by simp only [regs, yL] at *; (clear * - hx; omega)
  refine ⟨fun v hv => ?_, ?_, fun r hr hr2 => ?_, inv_sem I (P := .blk [.op .add yL yL cOne])
    (by simp +decide [WF, Prim.dst, yL]) hM1⟩
  · rw [b2 _ (hx _ (by simp only [regs]; (clear * - hmB; omega))), m1 v hv, Nat.one_mul,
      k0 _ (by simp only [regs]; (clear * - hoB; omega))]
  · have hs1 := hM1.1
    simp only [regs] at hs1
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yL]; (clear * - hs z0 z1; omega)), l1, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · rw [b2 _ (hx r hr), m2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The message reorder**: row `l < C` of the message at `mB + l·2^kL` is row `C − 1 − l` at
`oB`; the heap outside `[mB, mB + 2^19)` is kept. -/
theorem rowsMIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL C oB mB : ℕ} (hk : kL < 64) (hC : C < 2 ^ 64)
    (hoB : regs ≤ oB) (hoB2 : oB + C * 2 ^ kL < 2 ^ 64) (hmB : regs ≤ mB) (hmB2 : mB + C * 2 ^ kL < 2 ^ 64)
    (hms : mB + C * 2 ^ kL ≤ s.M.size) (hdisj : oB + C * 2 ^ kL ≤ mB ∨ mB + C * 2 ^ kL ≤ oB) :
    (∀ l < C, ∀ v < 2 ^ kL, rd (semXIR I (rowsMIR kL C oB mB) s).M (mB + l * 2 ^ kL + v) =
      rd s.M (oB + (C - 1 - l) * 2 ^ kL + v)) ∧
    (∀ r, regs ≤ r → (r < mB ∨ mB + C * 2 ^ kL ≤ r) → rd (semXIR I (rowsMIR kL C oB mB) s).M r = rd s.M r) ∧
    Inv (semXIR I (rowsMIR kL C oB mB) s).M := by
  have hs := hM.1
  have hK0 : 0 < 2 ^ kL := by positivity
  simp only [regs] at hs hoB hmB
  rw [rowsMIR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 (toWord C)]) := by simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 (toWord C)]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s).M yN2 = toWord C := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ l < j, ∀ v < 2 ^ kL, rd s'.M (mB + l * 2 ^ kL + v) = rd s.M (oB + (C - 1 - l) * 2 ^ kL + v)) ∧
    (∀ r, regs ≤ r → (r < mB ∨ mB + j * 2 ^ kL ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord C) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord C) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun l hl => absurd hl (by (clear * - hl; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; (clear * - hr; omega)) (by simp only [cTmp]; (clear * - hr; omega)), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < C → P j s' → P (j + 1) (decS yC2 (semXIR I (msgRowM kL C oB mB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := msgRowM_sem I s' i1 (oB := oB) (mB := mB) hk hC hj
      (by simp only [regs]; omega) hoB2 (by simp only [regs]; omega) hmB2 (by (clear * - hms z0 h0 i2; omega)) hdisj i3
    have hd : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (msgRowM kL C oB mB) s')).M x =
        rd (semXIR I (msgRowM kL C oB mB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; (clear * - hx; omega)
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd _ (by decide), b2],
      fun l hl v hv => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (hx _ (by simp only [regs]; (clear * - hoB hoB2 hmB hmB2; omega)))]
      by_cases hlj : l = j
      · subst hlj
        have h1 := Nat.mul_le_mul_right (2 ^ kL) (show C - 1 - l + 1 ≤ C by (clear * - hj; omega))
        have h2 := Nat.mul_le_mul_right (2 ^ kL) (show l ≤ C by (clear * - hj; omega))
        rw [Nat.succ_mul] at h1
        rw [b1 v hv, i5 _ (by simp only [regs]; (clear * - hoB; omega)) (by (clear * - hdisj hv h1 h2; omega))]
      · rw [b3 _ (by simp only [regs]; (clear * - hoB hoB2 hmB hmB2; omega)) (by
          rcases Nat.lt_or_gt_of_ne hlj with h | h
          · left
            have := Nat.mul_le_mul_right (2 ^ kL) (show l + 1 ≤ j by (clear * - h; omega))
            rw [Nat.succ_mul] at this; (clear * - hv this; omega)
          · right
            have := Nat.mul_le_mul_right (2 ^ kL) (show j + 1 ≤ l by (clear * - hl h; omega))
            rw [Nat.succ_mul] at this; (clear * - hl h; omega)), i4 l (by (clear * - hl hlj; omega)) v hv]
    · have e : (j + 1) * 2 ^ kL = j * 2 ^ kL + 2 ^ kL := Nat.succ_mul _ _
      rw [e] at hr2
      rw [hd _ (hx r hr), b3 r hr (by (clear * - hr2 e; omega)), i5 r hr (by (clear * - hK0 hr2 e; omega))]
  have hfin := loopK_run I (msgRowM kL C oB mB) P s0 hM0 (c := yC2) (n := yN2) (K := C) (by decide)
    (by decide) (by decide) n0 hC h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩

/-! ## The decoding proper -/

/-- **The decoding proper**: on a list of `≥ 2^kL` agreeing positions at `agM`, the window's words at `mM`
(`decWordG` of the window's stack words `lo·2^kL + i`). -/
theorem decMP0Tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (hT : TabOkN N s.M dB) (wd : ℕ → ℕ → BF64)
    (α f : ℕ → Ext3) (hW : ∀ q < 2 ^ nL, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hlen : 2 ^ kL ≤ (agreeG nL kL wd α f).length)
    (hJ : ∀ t < 2 ^ kL, rd s.M (agM kL dB + t) = toWord ((agreeG nL kL wd α f).getD t 0)) :
    (∀ i < C * 2 ^ kL, rdK (semXIR I (decMP0Tail N nL kL lo C dB wB) s).M (mM nL kL C dB + i) =
      decWordG N nL kL wd α f (lo * 2 ^ kL + i)) ∧
    (∀ x, regs ≤ x → (x < wbM dB ∨ dB + wsM nL kL C ≤ x) →
      rd (semXIR I (decMP0Tail N nL kL lo C dB wB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP0Tail N nL kL lo C dB wB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rW
  have hkC : 2 ^ kL * C = C * 2 ^ kL := Nat.mul_comm _ _
  set Jl := (agreeG nL kL wd α f).take (2 ^ kL) with hJl
  have hJlen : Jl.length = 2 ^ kL := by
    rw [hJl, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_filter_range _ _).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ nL := fun j hj => by
    have := List.mem_of_mem_take hj
    rw [agreeG, List.mem_filter, List.mem_range] at this
    exact this.1
  have hBL : BaryLayP (2 ^ nL) (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64
      (oM nL kL dB) s.M.size := by
    refine ⟨by (clear * - k0 hws r t hkC hJlen; omega), by (clear * - hlo; omega), hkn', by (clear * - hlo; omega), ?_, ?_, ?_, ?_, by simp only [regs]; (clear * - rW; omega), ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [regs, agM, wbM, ebM, oM, encM]) <;> (clear * - k0 r hJlen n0 hws t hkC hlo tW z hkn' hCK dW rW; omega)
  have hget : ∀ t < 2 ^ kL, Jl.getD t 0 < 2 ^ nL := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by (clear * - hJlen ht; omega))]
    exact hJlt _ (List.getElem_mem (l := Jl) (n := t) (by (clear * - hJlen ht; omega)))
  rw [decMP0Tail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_semP I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64
    (oM nL kL dB)) s
  generalize semXIR I (baryIR (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64
    (oM nL kL dB)) s = s1 at b1 b2 hM1 z1
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 => by
    exact b2 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [wbM]; (clear * - hNN h2; omega))
      (by simp only [ebM]; (clear * - hNN hJlen h1 h2; omega)) (by simp only [oM, encM, agM]; (clear * - hCK hNN hws n0 r t rW tW hkC hJlen h1 h2; omega))
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAllM_sem I s1 hM1 hN (kL := kL) (R := C) (tb := tbM dB) (ob := oM nL kL dB)
    (by (clear * - hkn hnN; omega)) (by (clear * - hlo; omega)) (by simp only [regs, oM, encM, agM]; (clear * - k0 n0 r hJlen; omega))
    (by simp only [oM, encM, agM]; (clear * - hws t hkC hJlen; omega)) (by rw [z1]; simp only [oM, encM, agM]; (clear * - hws z hkC hJlen z1; omega))
    (by simp only [regs, tbM]; omega) (by simp only [tbM]; (clear * - hNN hws t hkC hJlen; omega)) (by simp only [tbM, oM, encM, agM]; (clear * - hkn' hCK hNN hws r t hkC hJlen; omega)) hT1
    (fun t i => rdK s1.M (oM nL kL dB + t * 2 ^ kL + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAllM N kL C (tbM dB) (oM nL kL dB)) s1
  generalize semXIR I (bflyAllM N kL C (tbM dB) (oM nL kL dB)) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := rowsMIR_sem I s2 hM2 (kL := kL) (C := C) (oB := oM nL kL dB) (mB := mM nL kL C dB)
    (by (clear * - hk61; omega)) (by (clear * - hlo; omega)) (by simp only [regs, oM, encM, agM]; (clear * - k0 n0 r hJlen; omega)) (by simp only [oM, encM, agM]; (clear * - hws t hkC hJlen; omega))
    (by simp only [regs, mM, oM, encM, agM]; (clear * - k0 hws n0 r t hkC hJlen; omega)) (by simp only [mM, oM, encM, agM]; (clear * - hws t hkC hJlen; omega))
    (by rw [z2, z1]; simp only [mM, oM, encM, agM]; (clear * - hws z hkC hJlen z1 z2; omega)) (by simp only [mM]; (clear * -; omega))
  generalize semXIR I (rowsMIR kL C (oM nL kL dB) (mM nL kL C dB)) s2 = s3 at d1 d2 hM3
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, hM3⟩
  · -- the window word `i = r·2^kL + v`: row `lo + r`, interpolated as output row `C − 1 − r`
    have hr : i / 2 ^ kL < C := by rw [Nat.div_lt_iff_lt_mul k0]; exact hi
    have hv : i % 2 ^ kL < 2 ^ kL := Nat.mod_lt _ k0
    have hdm := Nat.div_add_mod' i (2 ^ kL)
    have e1' : (lo * 2 ^ kL + i) / 2 ^ kL = lo + i / 2 ^ kL := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ k0, Nat.add_comm]
    have e2' : (lo * 2 ^ kL + i) % 2 ^ kL = i % 2 ^ kL := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    have hi' : mM nL kL C dB + i = mM nL kL C dB + i / 2 ^ kL * 2 ^ kL + i % 2 ^ kL := by (clear * - hdm; omega)
    rw [decWordG, e1', e2']
    generalize i / 2 ^ kL = rr at *
    generalize i % 2 ^ kL = v at *
    simp only [rdK]
    rw [hi', d1 rr hr v hv,
      show wK (rd s2.M (oM nL kL dB + (C - 1 - rr) * 2 ^ kL + v)) =
        rdK s2.M (oM nL kL dB + (C - 1 - rr) * 2 ^ kL + v) from rfl,
      c1 (C - 1 - rr) (by (clear * - hr; omega)) v hv, ← hJl]
    refine coeffsAt_congr ptK N kL 0 _ _ (fun j hj => ?_) v hv
    rw [show oM nL kL dB + (C - 1 - rr) * 2 ^ kL + j = oM nL kL dB + 2 ^ kL * (C - 1 - rr) + j by ring,
      b1 j hj _ (by (clear * - hr; omega)), show (2 : ℕ) ^ kL = Jl.length from hJlen.symm,
      baryValK_eqP (P := 2 ^ nL) (by (clear * - rW tW; omega)) hJnd hJlt (by (clear * - hkn' hJlen hj; omega))]
    refine interpF_congr ptK _ (fun q hq => ?_) j
    have hq' := hJlt q (List.mem_toFinset.1 hq)
    rw [show wB + (64 - lo - C) + 64 * q + (C - 1 - rr) = wB + 64 * q + (63 - (lo + rr)) by (clear * - hlo hr e1'; omega),
      hW q hq' _ (by (clear * - hlo e1'; omega))]
    rfl
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by simp only [mM, oM, encM, agM, wbM] at *; (clear * - hkn' hCK hws t hkC hJlen hx hx2; omega)),
      c2 x (by simp only [regs]; omega) (by simp only [oM, encM, agM, wbM] at *; (clear * - hCK hws n0 t hkC hJlen hx hx2; omega)),
      b2 x (by simp only [regs]; omega) (by simp only [wbM] at *; (clear * - hws n0 hkC hJlen hx2; omega))
        (by simp only [ebM, wbM] at *; (clear * - hws n0 hkC hJlen hx2; omega)) (by simp only [oM, encM, agM, wbM] at *; (clear * - hCK hws n0 t hkC hJlen hx hx2; omega))]

/-! ## The whole program -/

/-- **The level-0 decoder program computes `decodeG0 N nL kL lo C`.** -/
theorem decMP0IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ nL, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ kL, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M (okM dB) =
      bW (decide (2 ^ kL ≤ (agreeG nL kL wd α f).length)) ∧
    (∀ out, decodeG0 N nL kL lo C wd α f = some out →
      ∀ i < C * 2 ^ kL, rdK (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M (mM nL kL C dB + i) =
        out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + wsM nL kL C ≤ x) →
      rd (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  -- 1. the basis table
  rw [decMP0IR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabNIR_sem I s hM hN hN1 (tb := tbM dB) (by simp only [regs, tbM]; omega)
    (by simp only [tbM]; (clear * - hNN hws t; omega)) (by simp only [tbM]; (clear * - hCK hNN hws n0 z; omega))
  generalize semXIR I (wtabNIR N (tbM dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOkN N s1.M dB := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_eqA I s1 hM1 (aB := aB) (qB := qM dB) (by simp only [regs]; omega)
    (by (clear * - rA tA; omega)) (by simp only [regs, qM]; (clear * - r; omega)) (by simp only [qM]; (clear * - hws t; omega))
    (by rw [z1]; simp only [qM]; (clear * - hCK hws n0 z z1; omega)) (by simp only [qM]; (clear * - hCK hws n0 dA dF; omega))
  have z2 := size_sem I (eqtIR 6 aB (qM dB)) s1
  generalize semXIR I (eqtIR 6 aB (qM dB)) s1 = s2 at q1 q2 hM2 z2
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 => by
    exact q2 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [qM]; (clear * - hNN h2; omega))
  have hQ2 : ∀ l < 64, rdE s2.M (qM dB + 3 * l) = eqA α l := fun l hl => by
    rw [q1 l hl]
    refine eqA_congr (fun i hi => ?_) l
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; (clear * - rA tA hi hk; omega)) (by simp only [tbM]; (clear * - hCK hNN hws n0 dA dF hi hk; omega))
  have hL2 : DecM0Lay N nL kL lo C dB wB aB fB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc(f)`
  rw [semXIR_seq]
  obtain ⟨ee1, ee2, hM3⟩ := encMIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (encMIR N nL kL dB fB) s2
  generalize semXIR I (encMIR N nL kL dB fB) s2 = s3 at ee1 ee2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + wsM nL kL C ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2 x hx (by simp only [qM]; (clear * - hCK hws n0 hx2; omega)), w2 x hx (by simp only [tbM]; (clear * - hCK hNN hws n0 hx2; omega))]
  have hfB : ∀ v < 2 ^ kL, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; (clear * - rF hc; omega)) (by (clear * - hws dF hv hc; omega))]
  have hW3 : ∀ q < 2 ^ nL, ∀ t < 64, rdK s3.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
    have : 64 * q + t < 64 * 2 ^ nL := by (clear * - hq ht; omega)
    rw [← hW q hq t ht]; simp only [rdK]
    rw [ee2 _ (by simp only [regs]; (clear * - rW ht; omega)) (by simp only [encM, agM]; omega),
      hout _ (by simp only [regs]; (clear * - rW ht; omega)) (by (clear * - hws dW dA dF ht this; omega))]
  have hQ3 : ∀ l < 64, rdE s3.M (qM dB + 3 * l) = eqA α l := fun l hl => by
    rw [← hQ2 l hl]
    exact rdE_congr fun k hk => ee2 _ (by simp only [regs, qM]; (clear * - r hl hk; omega))
      (by simp only [qM, encM, agM]; (clear * - hCK hws n0 hl hk; omega))
  have hE3 : ∀ q < 2 ^ nL, encG kL f q = mkE (rdK s3.M (encM nL kL dB + q))
      (rdK s3.M (encM nL kL dB + 2 ^ nL + q)) (rdK s3.M (encM nL kL dB + 2 * 2 ^ nL + q)) := by
    intro q hq
    rw [encG_coords kL f (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (encM nL kL dB + c * 2 ^ nL + q) := fun c hc => by
      rw [ee1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agreeNM s3.M (2 ^ nL) wB (qM dB) (encM nL kL dB) (2 ^ nL) = agreeG nL kL wd α f :=
    agreeNM_eq_agreeG wd α f hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agreeNIR_sem I s3 hM3 (st := 2 ^ nL) (wB := wB) (qB := qM dB)
    (eB := encM nL kL dB) (agB := agM kL dB) (by simp only [regs]; omega) (by (clear * - tW; omega))
    (by simp only [regs, qM]; (clear * - r; omega)) (by simp only [qM]; (clear * - hws t; omega))
    (by simp only [regs, encM, agM]; (clear * - hCK hws n0 r; omega)) (by simp only [encM, agM]; (clear * - hkn' hws t; omega))
    (by simp only [regs, agM]; (clear * - hCK hws r t; omega)) (by simp only [agM]; (clear * - hws n0 t; omega))
    (by rw [z3, z2, z1]; simp only [agM]; (clear * - hws n0 z z1 z2 z3; omega))
    ⟨by simp only [agM]; (clear * - hCK hws t rW tW dW dA dF; omega), by simp only [agM, qM]; (clear * - hCK hws r t; omega), by simp only [agM, encM]; (clear * -; omega)⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agreeNIR (2 ^ nL) wB (qM dB) (encM nL kL dB) (agM kL dB)) s3
  generalize semXIR I (agreeNIR (2 ^ nL) wB (qM dB) (encM nL kL dB) (agM kL dB)) s3 = s4
    at g1 g2 g3 hM4 z4
  have hlenL : (agreeG nL kL wd α f).length ≤ 2 ^ nL := by
    rw [agreeG]; exact (List.length_filter_le _ _).trans (by simp)
  have hlen64 : (agreeG nL kL wd α f).length < 2 ^ 64 := by (clear * - rW tW hlenL; omega)
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okMIR_sem I s4 hM4 (kL := kL) (ok := okM dB)
    (n := (agreeG nL kL wd α f).length) (by (clear * - hk61; omega)) (by simp only [regs, okM]; (clear * - r; omega))
    (by simp only [okM]; (clear * - hws t; omega)) (by rw [z4, z3, z2, z1]; simp only [okM]; (clear * - hCK hws n0 z z1 z2 z3 z4; omega)) hlen64 g1
  have z5 := size_sem I (okMIR kL (okM dB)) s4
  generalize semXIR I (okMIR kL (okM dB)) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOkN N s5.M dB := tabOkN_congr hT2 fun x h1 h2 => by
    rw [o3 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [okM]; (clear * - hNN h2; omega)),
      g3 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [agM]; (clear * - hCK hNN hws t h1 h2; omega)),
      ee2 x (by simp only [regs]; (clear * - hNN r h1 h2; omega)) (by simp only [encM, agM]; (clear * - hCK hNN hws t h1 h2; omega))]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + wsM nL kL C ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [okM]; (clear * - hCK hws n0 hx2; omega)), g3 x hx (by simp only [agM]; (clear * - hCK hws t hx2; omega)),
      ee2 x hx (by simp only [encM, agM]; (clear * - hCK hws r t hx2; omega)), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ kL ≤ (agreeG nL kL wd α f).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : DecM0Lay N nL kL lo C dB wB aB fB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ nL, ∀ t < 64, rdK s5.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
      have : 64 * q + t < 64 * 2 ^ nL := by (clear * - hq ht; omega)
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; (clear * - rW ht; omega)) (by (clear * - hws dW dA dF ht this; omega))]
    have hJ5 : ∀ t < 2 ^ kL, rd s5.M (agM kL dB + t) = toWord ((agreeG nL kL wd α f).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, agM]; (clear * - r ht; omega)) (by simp only [agM, okM]; (clear * - ht; omega)), g2 t (by (clear * - hk ht; omega))]
    obtain ⟨d1, d2, hM6⟩ := decMP0Tail_sem I s5 hM5 hL5 hT5 wd α f hW5 hk hJ5
    refine ⟨?_, fun out hout' i hi => ?_, fun x hx hx2 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, okM]; (clear * - r; omega)) (by simp only [okM, wbM]; (clear * -; omega)), o2, decide_eq_true hk]
    · rw [decodeG0, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 i hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getElem_range]
    · rw [d2 x hx (by simp only [wbM]; (clear * - hws hx2; omega)), h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun out hout' => ?_, h5, hM5⟩
    rw [decodeG0, if_neg hk] at hout'
    exact absurd hout' (by simp)

/-! ## M′'s level 0 -/

/-- **M′'s level-0 decoder program computes `decodeMP0`** (`2^19` positions, `k = 2^17`, lanes 40–47): the
window's `8·2^17` words at `mM`. -/
theorem decMP0IRW_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecM0Lay 19 19 17 40 8 dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 19, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 17, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP0IRW dB wB aB fB) s).M (okM dB) =
      bW (decide (2 ^ 17 ≤ (agreeG 19 17 wd α f).length)) ∧
    (∀ out, decodeMP0 wd α f = some out →
      ∀ i < 8 * 2 ^ 17, rdK (semXIR I (decMP0IRW dB wB aB fB) s).M (mM 19 17 8 dB + i) = out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + wsM 19 17 8 ≤ x) →
      rd (semXIR I (decMP0IRW dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP0IRW dB wB aB fB) s).M :=
  decMP0IR_sem I s hM hL wd α f hW hA hF

/-- **A level-0 layout exists** below `2^26` (non-vacuity): workspace at `2^23`, word at `2^24`, `α` at `2^20`, `f`
at `2^20 + 64`. -/
theorem decMP0Lay_example (sz : ℕ) (hsz : 2 ^ 26 ≤ sz) :
    DecM0Lay 19 19 17 40 8 (2 ^ 23) (2 ^ 24) (2 ^ 20) (2 ^ 20 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, wsM]) <;> norm_num <;> omega

end Lvm.X
end
-- ===== end of `LvmMPXDec0Sem` =====

-- ===== merged from `LvmMPXReadSem` (GOLF module merge: `LvmMPXReadSem.lean` is now a stub importing `LvmMPXNodeSem`) =====
section
-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (ii)): the semantics of the generic column reads `readGIR`.
-- Adapted from `LvmXRead.lean` (`cr_zero_sem`, `cr_copy_sem`) and `LvmXRead1.lean` (`cr1_capLd_sem`, `cr1_pos_sem`,
-- `cr1_posLoop`, `read1IR_sem4`, `read1IR_sem`) at a generic tree: `nPos` positions, `D` steps below the cap, rows of
-- `z` zero words and `occ` leaf words.

/-!
# `readGIR_sem`: the generic column reads compute `readRowG`

After the index (`idxIR4`), `readGIR bX pL capW wB (2^ht) (ht − lv) z occ` stores `readRowG ht lv z occ L cap p` at
`wB + (z + occ) p + t` (`p < 2^ht`, `t < z + occ`); the index and the heap outside `[wB, wB + (z + occ) 2^ht)` are
kept. `readRowG` is the first-preimage reading of WP-5's `leafBytes` under `⟨ht, z + occ, lv, cap⟩`: `z` zero words,
then the leaf's first `occ` words.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The pure reading -/

/-- The leaf bytes the log holds under the cap `cap` of a tree of height `ht` with a cap at level `lv`
(`none`: an erasure); WP-5's `leafBytes L ⟨ht, _, lv, cap⟩ p`. -/
def xLeafBytesG (ht lv : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p % 2 ^ ht / 2 ^ (ht - lv)]?).bind fun v =>
    (xDescend L (ht - lv) v (p % 2 ^ ht)).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- **The row the log holds** at position `p`: `z` zero words, then the leaf's first `occ` words; an erasure reads
as the row of the empty byte string. -/
def readRowG (ht lv z occ : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : List BF64 :=
  List.replicate z 0 ++ xRowOf decLE occ ((xLeafBytesG ht lv L cap p).getD [])

@[simp] theorem readRowG_length (ht lv z occ : ℕ) (L : Log) (cap : List Digest) (p : ℕ) :
    (readRowG ht lv z occ L cap p).length = z + occ := by
  simp [readRowG, xRowOf]

theorem readRowG_getD (ht lv z occ : ℕ) (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht' : t < z + occ) :
    (readRowG ht lv z occ L cap p).getD t 0 = if t < z then 0 else
      decLE ((((xLeafBytesG ht lv L cap p).getD []).drop (8 * (t - z))).take 8) := by
  rw [List.getD_eq_getElem _ _ (by rw [readRowG_length]; exact ht')]
  simp only [readRowG, xRowOf]
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp only [List.length_replicate] at h1; (clear * - h2 h1; omega)
  · simp only [List.length_replicate] at h1; omega
  · simp

/-- The reading at position `p` under the cap node `p / 2^D`, `D` steps down (`none` past the cap). -/
def crRdG (D : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p / 2 ^ D]?).bind fun v => crRdN D L v p

theorem crRdG_eq {D : ℕ} {L : Log} {cap : List Digest} {p : ℕ} (hpc : p / 2 ^ D < cap.length) :
    crRdG D L cap p = crRdN D L (cap[p / 2 ^ D]'hpc) p := by
  unfold crRdG
  rw [List.getElem?_eq_getElem hpc]
  rfl

/-- On a position of the tree, the leaf bytes are the machine's reading. -/
theorem xLeafBytesG_eq {ht lv : ℕ} {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ ht) :
    xLeafBytesG ht lv L cap p = crRdG (ht - lv) L cap p := by
  unfold xLeafBytesG crRdG crRdN
  rw [Nat.mod_eq_of_lt hp]

/-- **Row word `t` of a reading** as the machine stores it: `z` zero words, then the leaf words. -/
def crGRowW (z : ℕ) (o : Option (List UInt8)) (t : ℕ) : Word :=
  if t < z then 0 else crLeafW o (t - z)

/-- **The stored word as a `K` element is the row's word.** -/
theorem crGRowW_readRowG {ht lv z occ : ℕ} (L : Log) (cap : List Digest) {p : ℕ} (hp : p < 2 ^ ht)
    {t : ℕ} (ht' : t < z + occ) :
    wK (crGRowW z (crRdG (ht - lv) L cap p) t) = (readRowG ht lv z occ L cap p).getD t 0 := by
  rw [readRowG_getD ht lv z occ L cap p ht', crGRowW, xLeafBytesG_eq hp]
  split_ifs
  · rfl
  · rw [wK_crLeafW]

/-! ## The cap node -/

/-- **The cap node's words**: after `crCapGPs capW D ; crLd4`, `rQ0 … rQ3` hold `cap[p / 2^D]`. -/
theorem crG_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW D : ℕ} {cap : List Digest}
    (hD : D < 64) (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 2 ^ D < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ3] =
      packBytes (cap[p / 2 ^ D]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (crCapGPs capW D)) := by simp +decide only [crCapGPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hle : p / 2 ^ D ≤ p := Nat.div_le_self _ _
  have hA : rd (semXIR I (.blk (crCapGPs capW D)) s).M crTA = toWord (capW + 4 * (p / 2 ^ D)) := by
    simp only [crCapGPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, shr_toWord (by (clear * - hp; omega)) hD, show (2 : Word) = toWord 2 from rfl]
    generalize p / 2 ^ D = e at hle ⊢
    rw [shl_toWord (by norm_num) (by (clear * - hp hle; omega)), add_toWord]
    congr 1
    (clear * -; omega)
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by (clear * - hcw he; omega)) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

/-! ## The row: zero prefix and copy -/

theorem crG_wf_zero (z : ℕ) : WF (crZeroG z) := by
  simp +decide only [crZeroG, crZeroBody, WF, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem crG_wf_copy (z occ : ℕ) : WF (crCopyG z occ) := by
  simp +decide only [crCopyG, crZeroG, crZeroBody, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK,
    crWA, crTA, cr8, crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true]

/-- The registers the zero prefix keeps. -/
theorem crG_zero_nw (z : ℕ) {r : ℕ} (hr : r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) :
    ¬ Writes (crZeroG z) r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [crZeroG, crZeroBody, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, crX, crQe,
    crP, crTA, cr8, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false,
    not_or, exists_false, not_false_eq_true, and_self]

/-- **The row's zero prefix**: from `crWA = a`, cells `a … a + z − 1` get `0`; every other heap cell is kept;
`crWA` ends at `a + z`. -/
theorem crZeroG_sem (I : Array Word) (s : St) (hM : Inv s.M) {z a : ℕ} (ha : regs ≤ a)
    (ha2 : a + z < 2 ^ 64) (hsz : a + z ≤ s.M.size) (hA : rd s.M crWA = toWord a) :
    (∀ i < z, rd (semXIR I (crZeroG z) s).M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (z) ≤ y) → rd (semXIR I (crZeroG z) s).M y = rd s.M y) ∧
    Inv (semXIR I (crZeroG z) s).M ∧ rd (semXIR I (crZeroG z) s).M crWA = toWord (a + (z)) := by
  have hs := hM.1
  simp only [regs] at hs ha
  rw [crZeroG, semXIR_seq]
  have w0 : WF (.blk [.const crV 0, .const crNw (toWord (z))]) := by
    simp +decide only [WF, Prim.dst, crV, crNw, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
      forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const crV 0, .const crNw (toWord (z))]) s
  have r0 : rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M crV = 0 ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M crNw =
        toWord (z) ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M crWA =
        toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crV, crNw, crWA]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hA
  have k0 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, crV, crNw, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  generalize semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨v0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M crV = 0 ∧ rd s'.M crWA = toWord (a + j) ∧ (∀ i < j, rd s'.M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + j ≤ y) → rd s'.M y = rd s.M y)
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp →
      rd (entryK crCw crNw (toWord (z)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK crCw crNw (toWord (z)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun i hi => absurd hi (by (clear * - hi; omega)), fun y hy _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), v0]
    · rw [hE _ (by decide) (by decide), a0, Nat.add_zero]
    · simp only [regs] at hy
      rw [hE _ (by simp only [crCw]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega)),
        k0 y (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < z → P j s' →
      P (j + 1) (decS crCw (semXIR I crZeroBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    rw [crZeroBody, semXIR_seq]
    obtain ⟨c1, c2, hM1⟩ := store_sem I s' i1 (p := crWA) (v := crV) (x := a + j) (by decide)
      (by decide) i4 (by simp only [regs]; (clear * - ha; omega)) (by (clear * - ha2 hj; omega)) (by (clear * - hsz z0 h0 hj i2; omega))
    have z1 := size_sem I (.store crWA crV) s'
    generalize semXIR I (.store crWA crV) s' = s1 at c1 c2 hM1 z1
    have hs1 := hM1.1
    simp only [regs] at hs1
    have hdr : ∀ r, r < regs → r ≠ a + j := fun r hr => by simp only [regs] at hr; (clear * - ha ha2 hr; omega)
    have b2 : ∀ r, r ≠ crWA → rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M r = rd s1.M r :=
      fun r hr => by
        simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
    have hM2 := inv_sem I (P := .blk [.op .add crWA crWA cOne])
      (by simp +decide only [WF, Prim.dst, crWA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
        forall_eq, or_false, and_true]) hM1
    have hd : ∀ y, y ≠ crCw → rd (decS crCw (semXIR I (.blk [.op .add crWA crWA cOne]) s1)).M y =
        rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M y := fun y hy => rd_decS (Ne.symm hy) _
    have hx : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ crWA ∧ y ≠ cTmp := fun y hy => by
      simp only [regs, crCw, crWA, cTmp] at *; (clear * - hy; omega)
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, z1, i2], ?_, ?_,
      fun i hi => ?_, fun y hy hy2 => ?_⟩
    · rw [hd _ (by decide), b2 _ (by decide), c2 _ (hdr _ (by decide)) (by decide), i3]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [crWA]; (clear * - hs z0 h0 i2 z1; omega)), c2 _ (hdr _ (by decide)) (by decide), i4,
        c2 _ (hdr _ (by decide)) (by decide), show rd s'.M cOne = 1 from i1.2 0 (by decide),
        add_one_toWord, Nat.add_assoc]
    · obtain ⟨x1, x2, x3⟩ := hx (a + i) (by simp only [regs]; (clear * - ha; omega))
      rw [hd _ x1, b2 _ x2]
      by_cases hij : i = j
      · subst hij; rw [c1, i3]
      · rw [c2 _ (by (clear * - hij; omega)) x3, i5 i (by (clear * - hi hij; omega))]
    · obtain ⟨x1, x2, x3⟩ := hx y hy
      rw [hd _ x1, b2 _ x2, c2 _ (by (clear * - hy2 x1 x2 x3; omega)) x3, i6 y hy (by (clear * - hy2 x1 x2 x3; omega))]
  have hfin := loopK_run I crZeroBody P s0 hM0 (c := crCw) (n := crNw) (K := z)
    (by decide) (by decide) (by decide) n0 (by (clear * - ha ha2; omega)) h0 hstep
  exact ⟨hfin.2.2.2.2.1, hfin.2.2.2.2.2, hfin.1, hfin.2.2.2.1⟩


/-- What the copy stores at row cell `i`: `0` in the first `z` cells, then copy word `i − z`. -/
def crCpRowG (I : Array Word) (x : Word) (ql z i : ℕ) : Word :=
  if i < z then 0 else crCpW I x ql (i - z)

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + z + occ − 1` get `crCpRowG I x ql z ·`
(`z` zero words, then copy words `0 … occ − 1`); every other heap cell is kept; `crWA` ends at `a + z + occ`. -/
theorem crCopyG_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql z occ a : ℕ}
    (hql : ql < 2 ^ 64) (ho : occ < 2 ^ 60) (ha : regs ≤ a) (ha2 : a + (z + occ) + 2 < 2 ^ 64)
    (hsz : a + (z + occ) ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < z + occ, rd (semXIR I (crCopyG z occ) s).M (a + i) = crCpRowG I x ql z i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (z + occ) ≤ y) → rd (semXIR I (crCopyG z occ) s).M y = rd s.M y) ∧
    Inv (semXIR I (crCopyG z occ) s).M ∧ rd (semXIR I (crCopyG z occ) s).M crWA = toWord (a + (z + occ)) ∧
    rd (semXIR I (crCopyG z occ) s).M crP = rd s.M crP := by
  -- the zero prefix
  obtain ⟨z1, z2, hMz, az⟩ := crZeroG_sem I s hM (z := z) ha (by (clear * - ho ha2; omega)) (by (clear * - ho hsz; omega)) hA
  have fz : ∀ r, (r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) →
      rd (semXIR I (crZeroG z) s).M r = rd s.M r := fun r hr =>
    frame I _ s (crG_wf_zero z) hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (crG_zero_nw z hr)
  have hszz := size_sem I (crZeroG z) s
  rw [crCopyG, semXIR_seq]
  generalize semXIR I (crZeroG z) s = s1 at z1 z2 hMz az fz hszz
  have hX1 : rd s1.M crX = x := (fz _ (.inl rfl)).trans hX
  have hQ1 : rd s1.M crQe = toWord ql := (fz _ (.inr (.inl rfl))).trans hQ
  have hP1 : rd s1.M crP = rd s.M crP := fz _ (.inr (.inr (.inl rfl)))
  -- the copy of `occ` words to `a + z`
  have hs := hMz.1
  have h1 : rd s1.M cOne = 1 := hMz.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hMz
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)]) s1
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
    s1
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crNw = toWord occ ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crWA = toWord (a + z + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crP = rd s1.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ1 | exact az | (rw [hX1, h1]; all_goals rfl)
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
    s1 = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord occ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord occ) s0.M) crCw = toWord occ :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord occ) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord occ) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw occ ⟨entryK crCw crNw (toWord occ) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show occ < 2 ^ 64 by (clear * - ho; omega))]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; (clear * - hy; omega)
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I (a := a + z) (nw := occ) hql
    (by simp only [regs] at ha ⊢; (clear * - ha; omega)) (by (clear * - ha2; omega)) ho occ 0 ⟨entryK crCw crNw (toWord occ) s0.M, s0.o⟩
    (by (clear * -; omega)) hME (by simp only [size_entryK]; (clear * - hsz hszz hsz0; omega)) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  have back : ∀ y, regs ≤ y → (y < a + z ∨ a + (z + occ) ≤ y) →
      rd (iterL (semXIR I crCopyBody) crCw occ ⟨entryK crCw crNw (toWord occ) s0.M, s0.o⟩).M y =
        rd s1.M y := fun y hy1 hy2 => by
    rw [d2 y hy1 (by (clear * - hy2; omega))]
    show rd (entryK crCw crNw (toWord occ) s0.M) y = rd s1.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  refine ⟨fun i hi => ?_, fun y hy1 hy2 => ?_, d3, ?_, ?_⟩
  · rw [crCpRowG]
    split_ifs with h
    · rw [back _ (by simp only [regs] at ha ⊢; (clear * - ha; omega)) (.inl (by (clear * - h; omega))), z1 i h]
    · rw [show a + i = a + z + (i - z) by (clear * - h; omega)]
      exact d1 _ (by (clear * -; omega)) (by (clear * - hi h; omega))
  · rw [back y hy1 (by (clear * - ho hy2; omega)), z2 y hy1 (by (clear * - ho hy2; omega))]
  · rw [d4, show a + z + (0 + occ) = a + (z + occ) by (clear * -; omega)]
  · rw [d5]
    show rd (entryK crCw crNw (toWord occ) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0, hP1]

section PosG

variable {nPos D z occ : ℕ}
variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the row of position `p` at `a … a + z + occ − 1`; `crP := p + 1`,
`crWA := a + (z + occ)`; every other heap cell kept. -/
theorem crPosG_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : ∀ q < nPos, q / 2 ^ D < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : nPos < 2 ^ 62) (hD64 : D < 64) (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < nPos) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + (z + occ) + 2 < 2 ^ 64) (hsz : a + (z + occ) ≤ s.M.size) :
    (∀ t < (z + occ), rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M (a + t) =
      crGRowW z (crRdG D L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (z + occ) ≤ y) →
      rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M ∧
    rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M crWA = toWord (a + (z + occ)) ∧
    rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 2 ^ D < cap.length := hcl p hp
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (crCapGPs capW D)) crLd4) := ⟨by simp +decide only [crCapGPs, WF,
    Prim.dst, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (crCapGPs capW D)) crLd4) := ⟨by simp +decide only [crCapGPs, Lo,
    Prim.dst, regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_lo_ld4⟩
  have q1 := crG_capLd_sem I s hM hD64 hcw hcap (by (clear * - hn hp; omega)) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [crCapGPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3,
        crP, crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (crCapGPs capW D)) crLd4) s
  rw [crPosG, semXIR_seq]
  generalize semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord D)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1).M crNH = toWord D := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord D)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalkN D L (cap[p / 2 ^ D]'hpc) p D s2.M := by
    refine .inl ⟨o2.1, cap[p / 2 ^ D]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; (clear * - hy; omega)) (by simp only [crNH, regs] at *; (clear * - hy; omega)),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord D) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord D) s2.M) crHc = toWord D :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord D) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord D) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc D ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show D < 2 ^ 64 by (clear * - hD64; omega))]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; (clear * - hy; omega)
  have hWE : crWalkN D L (cap[p / 2 ^ D]'hpc) p D (entryK crHc crNH (toWord D) s2.M) := by
    unfold crWalkN at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord D) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord D) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoopN hbX hbX2 hpL hD hX (by (clear * - hn hp; omega)) D
    ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩ hD64 hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc D ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord D) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc D
      ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord D) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc D
      ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord D) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc D
      ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord D) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc D ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_semN hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := crCopyG_sem I s4 hM4 hql ho ha ha2 (by (clear * - hsz hsz1 hsz2 hsz3 hsz4; omega)) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I (crCopyG z occ) s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; (clear * - ha; omega)), k1 t ht, crCpRowG, crGRowW]
    split_ifs
    · rfl
    · rw [c2, crRdG_eq hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; (clear * - hy1; omega)), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; (clear * - hs5; omega)), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their rows (`z` zero words, then the leaf words) at
`wB + (z + occ) q`. -/
theorem crPosG_loop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : ∀ q < nPos, q / 2 ^ D < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : nPos < 2 ^ 62) (hD64 : D < 64) (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + (z + occ) * nPos ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ nPos → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + (z + occ) * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < (z + occ),
        rd (iterL (semXIR (crTape c π L) (crPosG bX pL capW D z occ)) crCp m s).M (wB + (z + occ) * q + t) =
          crGRowW z (crRdG D L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + (z + occ) * j ∨ wB + (z + occ) * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (crPosG bX pL capW D z occ)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (crPosG bX pL capW D z occ)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : (z + occ) * (j + 1) = (z + occ) * j + (z + occ) := Nat.mul_succ (z + occ) j
    have hmj : (z + occ) * (j + 1) ≤ (z + occ) * nPos := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := crPosG_sem (z := z) (occ := occ) hbX hbX2 hpL hD hX s hM hXs hcl hcw hn hD64 ho hcap (p := j)
      (a := wB + (z + occ) * j) (by omega) hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS crCp (semXIR I (crPosG bX pL capW D z occ) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (crPosG bX pL capW D z occ) s)).M r =
        rd (semXIR I (crPosG bX pL capW D z occ) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; omega
    have hsz' : bX ≤ (decS crCp (semXIR I (crPosG bX pL capW D z occ) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := crPosG_loop hD hX hcl hcw hn hD64 ho hcap hwB hwB2 m (j + 1) _ (by omega) hM'
      hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)),
          b2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : (z + occ) * (j + 1 + m) = (z + occ) * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by omega]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by simp only [regs] at hwB ⊢; omega) (.inl (by omega)), dk _ (hy _ (by simp only [regs] at hwB ⊢; omega)), b1 t ht]
      · exact d1 q (by omega) (by omega) t ht
    · have h2 : y < wB + (z + occ) * (j + 1) ∨ wB + (z + occ) * (j + (m + 1)) ≤ y := by
        rcases hy2 with h | h
        · exact .inl (by rw [e1]; omega)
        · exact .inr h
      have h3 : y < wB + (z + occ) * j ∨ wB + (z + occ) * j + (z + occ) ≤ y := by
        rcases hy2 with h | h
        · exact .inl h
        · refine .inr (le_trans ?_ h)
          rw [Nat.add_assoc, ← e1]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      rw [d2 _ hy1 h2, dk _ (hy _ hy1), b2 _ hy1 h3]

/-- **The column reads on a sorted index**: `readGIR bX pL capW wB nPos D z occ` stores at `wB + (z + occ) p + t`
row word `t` of the reading at position `p < nPos` and keeps every heap cell outside `[wB, wB + (z + occ) nPos)`. -/
theorem readGIR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : ∀ q < nPos, q / 2 ^ D < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : nPos < 2 ^ 62) (hD64 : D < 64) (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + (z + occ) * nPos ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < nPos, ∀ t < (z + occ),
      rd (semXIR (crTape c π L) (readGIR bX pL capW wB nPos D z occ) s).M (wB + (z + occ) * p + t) =
        crGRowW z (crRdG D L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + (z + occ) * nPos ≤ y) →
      rd (semXIR (crTape c π L) (readGIR bX pL capW wB nPos D z occ) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (readGIR bX pL capW wB nPos D z occ) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (nPos))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (nPos))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (nPos))]) s).M crWA = toWord (wB + (z + occ) * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (nPos))]) s).M crNp = toWord (nPos) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals rfl
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (nPos))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (nPos))]) s
  rw [readGIR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (nPos))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp →
      rd (entryK crCp crNp (toWord (nPos)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (nPos)) s0.M) crCp = toWord (nPos) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (nPos)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (nPos)) (crPosG bX pL capW D z occ)) s0 =
      iterL (semXIR I (crPosG bX pL capW D z occ)) crCp (nPos)
        ⟨entryK crCp crNp (toWord (nPos)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show nPos < 2 ^ 64 by (clear * - hn; omega))]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; (clear * - hy; omega)
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (nPos)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : (z + occ) * (0 + nPos) = (z + occ) * nPos := by rw [Nat.zero_add]
  obtain ⟨d1, d2, d3⟩ := crPosG_loop hbX hbX2 hpL hD hX hcl hcw hn hD64 ho hcap hwB hwB2 (nPos) 0
    ⟨entryK crCp crNp (toWord (nPos)) s0.M, s0.o⟩
    (by (clear * -; omega)) hME (by simp only [size_entryK]; (clear * - hsz hsz0; omega))
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (nPos)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (nPos)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (nPos)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by (clear * -; omega)) (by (clear * - hq; omega)) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (nPos)) s0.M) y = _
  rw [hHE y hy1]

end PosG

/-- **The column reads** of a tree of height `ht` with its cap at level `lv` (`2^ht` positions, `ht − lv` steps):
row word `t` of position `p` is `readRowG ht lv z occ L cap p`'s word `t`; the index and the heap outside the rows
are kept. -/
theorem readGIR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {ht' lv z occ capW wB : ℕ} {cap : List Digest} (hcl : ∀ q < 2 ^ ht', q / 2 ^ (ht' - lv) < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : 2 ^ ht' < 2 ^ 62) (hD64 : ht' - lv < 64)
    (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + (z + occ) * 2 ^ ht' ≤ bX) :
    (∀ p < 2 ^ ht', ∀ t < z + occ,
      rdK (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M
        (wB + (z + occ) * p + t) = (readRowG ht' lv z occ L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + (z + occ) * 2 ^ ht' ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M y =
        rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M
        (bX + a) = rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := readGIR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hn hD64 ho hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht'' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega))
    (.inr (by (clear * - hwB2; omega))), w3⟩
  rw [rdK, w1 p hp t ht'', crGRowW_readRowG L cap hp ht'']

end Lvm.X
end
-- ===== end of `LvmMPXReadSem` =====

/-!
# What `EXM` returns (BLUEPRINT §6.2, M′)

On an `S` proof (`π[0] = 'S'`, `|π| = piSize`):

* **`EXM_leaf`** (`b = 0`, every log): `leafW π`;
* **`EXM_node_out`** (`b ≠ 0`, outside the domain): the search under π's `vk`;
* **`EXM_node`** (`b ≠ 0`, in the domain): if the log has no state hit, the first-match chain answers the 14 fold
  challenges `αk k` (chain positions `foldPosK pX k`), and the three decoders succeed on the readings of
  `C_main`'s three words under π's caps (`readRowG`, caps `capM π i`), on `alphaE` of the answers and on π's
  residual (`resEM π`), then `EXM = some (Xwit π (wStreamM π out))`: the node with the child read off the
  decoded window `out` at the statement's shape (`wStreamM`: words `2i` when `n ≤ 2^18`, else `2^19 + i`).
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## The inputs of the decoders, as pure functions of π and the log -/

/-- The number of cap digests of `C_main`'s level `i`: `2^8` at level 0, `2^7` at levels 1, 2. -/
def capNM (i : ℕ) : ℕ := if i = 0 then 2 ^ 8 else 2 ^ 7

/-- **`C_main`'s level-`i` cap from π**: `capNM i` digests at π word `capOffM pX i / 8`. -/
def capM (π : Proof) (i : ℕ) : List Digest :=
  (List.range (capNM i)).map fun e => hdD π (capOffM pX i / 8 + 4 * e)

/-- **The residual's coefficient `v`** from π (`E` scalars of 3 words at π word `resOffM / 8`). -/
def resEM (π : Proof) (v : ℕ) : BF64.Ext3 :=
  mkE (wK (pw π (resOffM pX / 8 + 3 * v))) (wK (pw π (resOffM pX / 8 + 3 * v + 1)))
    (wK (pw π (resOffM pX / 8 + 3 * v + 2)))

/-- **The stream block's word `i`** from the decoded window `out` at the statement's shape (`n` is π word 14):
small (`n < 2^18 + 1`) window word `2i`, big window word `2^19 + i`. -/
def wStreamM (π : Proof) (out : List BF64) (i : ℕ) : Word :=
  BF64.toBitVec (out.getD (if pw π 14 < toWord (2 ^ 18 + 1) then 2 * i else 2 ^ 19 + i) 0)

/-! ## The parse, the leaf, outside the domain -/

theorem den_SM (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (h0 : π.data[0]? = some 0x53) :
    ∃ s1 : St, Inv s1.M ∧ s1.M.size = memM + mpwX * (extractorInput c π L).length ∧ s1.o = #[] ∧
      den memM mpwX (extIRWith (piSize pX) decXM) (extractorInput c π L) =
        (semXIR (extractorInput c π L).toArray decXM s1).o.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0' : Inv (initSt (memM + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  refine ⟨semXIR I (parseIR (piSize pX)) (initSt (memM + mpwX * (extractorInput c π L).length)),
    inv_sem I (wf_extIRWith (pz := piSize pX) wf_decXM).1 h0', by rw [size_sem, initSt_M, size_runPrims,
      Array.size_replicate], by rw [parse_o, initSt_o], ?_⟩
  have hk : rd (semXIR I (parseIR (piSize pX)) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsK ≠ 0 := by
    rw [parse_isK _ I _ h0']
    have hb := tape_byte0 c π L h0
    have e : I.getD 5 0 &&& 0xFF = kindS := by
      apply BitVec.eq_of_toNat_eq
      rw [lowByte, hI, getD_toArray, hb]; rfl
    rw [if_pos e]; decide
  have hz : rd (semXIR I (parseIR (piSize pX)) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsSz ≠ 0 := by
    rw [parse_regs _ I _ h0', hI, getD_toArray, tape_getD4, hs]
    rw [if_pos (by rfl)]; decide
  rw [den, extIRWith, semXIR_seq, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]

/-- **`EXM` on an `S` proof with `b = 0`**, on every log: the leaf witness of its header. -/
theorem EXM_leaf (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 = 0) :
    EXM A c π L = some (leafW π) := by
  by_cases hD : InDomE c π L
  · rw [EXM, if_pos hD, EdXM, Eden]
    obtain ⟨s1, hM1, -, ho1, hden⟩ := den_SM c π L hs h0
    rw [hden]
    set I := (extractorInput c π L).toArray with hI
    obtain ⟨b1, -, hM2, -, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
      (by decide) (by norm_num)
    rw [decXM, semXIR_seq]
    generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 bo
    have h6 : I.getD 6 0 = 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num), hb]
    rw [semXIR_ite, if_pos (by rw [b1, h6]), leafIR, semXIR_seq]
    obtain ⟨e1, -⟩ := emitIR_sem I s2 hM2 (toWord 0)
    have hM3 := inv_sem I (wf_emitIR (toWord 0)) hM2
    generalize semXIR I (emitIR (toWord 0)) s2 = s3 at e1 hM3
    obtain ⟨t1, -⟩ := tcpIR_sem I s3 hM3 (a := 15) (n := 5) (by norm_num)
    rw [t1, e1, bo, ho1]
    have t2 := wsAt_tape c π L hs (a := 10) (n := 5) (by norm_num)
    simp only [show (5 + 10 : ℕ) = 15 from rfl] at t2
    rw [t2]
    have hw : witWords (leafW π) = toWord 0 :: wsAt (pw π) 10 5 := by
      simp only [leafW, witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat',
        show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
      simp [wsAt]
    rw [Array.toList_empty, List.nil_append, List.singleton_append, ← hw]
    exact decodeWit_witWords _ (pw π 14).isLt
  · rw [EXM, if_neg hD, EoutX, if_pos h0, if_pos hs, if_pos hb]

/-- **`EXM` on an `S` node proof outside the domain**: the search under the key the proof carries. -/
theorem EXM_node_out (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : ¬ InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0) :
    EXM A c π L = search A (hdD π 2) c := by
  rw [EXM, if_neg hD, EoutX, if_pos h0, if_pos hs, if_neg hb]

/-! ## The pieces of the node branch -/

/-- **A flag test** `eA := a; eW := M[eA]; if eW then P`: on a set flag, `P` from a state that differs only in the
registers `eA`, `eW`. -/
theorem flagIte_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : regs ≤ a) (ha64 : a < 2 ^ 64)
    (hf : rd s.M a = 1) (P : XIR) :
    ∃ s' : St, Inv s'.M ∧ s'.M.size = s.M.size ∧ s'.o = s.o ∧ (∀ y, regs ≤ y → rd s'.M y = rd s.M y) ∧
      semXIR I (.seq (.blk [.const eA (toWord a)]) (.seq (.load eW eA) (.ite eW P (.blk [])))) s =
        semXIR I P s' := by
  have hs := hM.1
  simp only [regs] at hs ha
  rw [semXIR_seq]
  have e1 := blk_const_val I s hM (d := eA) (by decide) (toWord a)
  have g1 : ∀ y, y ≠ eA → rd (semXIR I (.blk [.const eA (toWord a)]) s).M y = rd s.M y :=
    fun y hy => blk_const_ne _ s _ hy
  have hM9 := inv_sem I (P := .blk [.const eA (toWord a)]) (by simp +decide [WF, Prim.dst, eA]) hM
  have z9 := size_sem I (.blk [.const eA (toWord a)]) s
  have o9 : (semXIR I (.blk [.const eA (toWord a)]) s).o = s.o := rfl
  generalize semXIR I (.blk [.const eA (toWord a)]) s = s9 at e1 g1 hM9 z9 o9
  have hs9 := hM9.1
  simp only [regs] at hs9
  have eL : semXIR I (.load eW eA) s9 = ⟨s9.M.setIfInBounds eW (rd s9.M (rd s9.M eA).toNat), s9.o⟩ := rfl
  have l1 : rd (semXIR I (.load eW eA) s9).M eW = rd s9.M a := by
    rw [eL]; show rd (s9.M.setIfInBounds eW _) eW = _
    rw [rd_set_self (by simp only [eW]; (clear * - hs z9; omega)), e1, toNat_toWord ha64]
  have l2 : ∀ i, i ≠ eW → rd (semXIR I (.load eW eA) s9).M i = rd s9.M i :=
    fun i hi => by rw [eL]; exact rd_set_ne (Ne.symm hi)
  have hM10 := inv_sem I (P := .load eW eA) (show 4 ≤ eW by decide) hM9
  have z10 := size_sem I (.load eW eA) s9
  have o10 : (semXIR I (.load eW eA) s9).o = s9.o := rfl
  rw [semXIR_seq]
  generalize semXIR I (.load eW eA) s9 = s10 at l1 l2 hM10 z10 o10
  have hflag : rd s10.M eW ≠ 0 := by rw [l1, g1 _ (by simp only [eA]; (clear * - ha ha64; omega)), hf]; decide
  rw [semXIR_ite, if_neg hflag]
  refine ⟨s10, hM10, by rw [z10, z9], by rw [o10, o9], fun y hy => ?_, rfl⟩
  simp only [regs] at hy
  rw [l2 _ (by simp only [eW]; (clear * - hy; omega)), g1 _ (by simp only [eA]; (clear * - hy; omega))]

theorem winM_eq : winM = 12328960 := by simp only [winM, mM, oM, encM, agM, dB0M]; norm_num

/-- **The stream block**: from the decoded window at `winM`, the statement's stream words at `mBM`. -/
theorem streamM_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s : St) (hM : Inv s.M)
    (hsz : memM ≤ s.M.size) (out : List BF64)
    (hW : ∀ j < 2 ^ 20, rd s.M (winM + j) = BF64.toBitVec (out.getD j 0)) :
    (∀ i < 2 ^ 19, rd (semXIR (extractorInput c π L).toArray streamM s).M (mBM + i) = wStreamM π out i) ∧
    (∀ y, regs ≤ y → (y < mBM ∨ mBM + 2 ^ 19 ≤ y) →
      rd (semXIR (extractorInput c π L).toArray streamM s).M y = rd s.M y) ∧
    Inv (semXIR (extractorInput c π L).toArray streamM s).M ∧
    (semXIR (extractorInput c π L).toArray streamM s).M.size = s.M.size ∧
    (semXIR (extractorInput c π L).toArray streamM s).o = s.o := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  simp only [regs] at hs0
  have hwin := winM_eq
  simp only [memM] at hsz
  suffices H : (∀ i < 2 ^ 19, rd (semXIR I streamM s).M (mBM + i) = wStreamM π out i) ∧
      (∀ y, regs ≤ y → (y < mBM ∨ mBM + 2 ^ 19 ≤ y) → rd (semXIR I streamM s).M y = rd s.M y) ∧
      Inv (semXIR I streamM s).M from ⟨H.1, H.2.1, H.2.2, size_sem I _ s, sem_o I _ s rfl⟩
  obtain ⟨b1, b2, hM1, z1, -⟩ := readAt_val I s hM (d := eW) (pos := 19) (by decide) (by decide)
    (by decide) (by norm_num)
  rw [streamM, semXIR_seq]
  generalize semXIR I (readAt eW 19) s = s1 at b1 b2 hM1 z1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have w2 : WF (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) := by
    simp +decide [WF, Prim.dst, eA, eW]
  have hM2 := inv_sem I w2 hM1
  have z2 := size_sem I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1
  have r2 : rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M eW =
      if I.getD 19 0 < toWord (2 ^ 18 + 1) then 1 else 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, eW]; (clear * - hsz z1 z2; omega)), rd_set_ne (by decide),
      rd_set_self (by simp only [eA]; (clear * - hsz z1 z2; omega)), b1]
    rfl
  have k2 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M y = rd s.M y :=
    fun y hy => by
      simp only [regs] at hy
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by simp only [eW]; (clear * - hy; omega)), rd_set_ne (by simp only [eA]; (clear * - hy; omega)),
        b2 _ (by simp only [eW]; (clear * - hy; omega)) (by simp only [rA]; (clear * - hy; omega))]
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1 = s2 at hM2 z2 r2 k2
  have hn : I.getD 19 0 = pw π 14 := by rw [show (19 : ℕ) = 5 + 14 from rfl, tape_pw c π L hs (by norm_num)]
  rw [hn] at r2
  have hsz2 : memM ≤ s2.M.size := by rw [z2, z1]; simp only [memM]; omega
  simp only [memM] at hsz2
  rw [semXIR_ite]
  by_cases hsm : pw π 14 < toWord (2 ^ 18 + 1)
  · rw [if_pos hsm] at r2
    rw [if_neg (by rw [r2]; decide)]
    obtain ⟨m1, m2, m3⟩ := mcpIR_sem I s2 hM2 (n := 2 ^ 19) (src := winM) (str := 2) (dst := mBM) (by norm_num)
      (by rw [hwin]; norm_num) (by norm_num) (by simp only [regs, mBM]; norm_num) (by simp only [mBM]; norm_num)
      (by simp only [mBM]; (clear * - hsz z1 z2; omega)) (fun i hi => .inr (by rw [hwin]; simp only [mBM]; (clear * - hi; omega)))
      (fun i hi => by rw [hwin]; simp only [regs]; (clear * - hi; omega))
    refine ⟨fun i hi => ?_, fun y hy h => ?_, m3⟩
    · rw [m1 i hi, k2 _ (by rw [hwin]; simp only [regs]; (clear * - hi; omega)), hW _ (by (clear * - hi; omega)), wStreamM, if_pos hsm]
    · rw [m2 y hy h, k2 y hy]
  · rw [if_neg hsm] at r2
    rw [if_pos r2]
    obtain ⟨m1, m2, m3⟩ := mcpIR_sem I s2 hM2 (n := 2 ^ 19) (src := winM + 2 ^ 19) (str := 1) (dst := mBM)
      (by norm_num) (by rw [hwin]; norm_num) (by norm_num) (by simp only [regs, mBM]; norm_num)
      (by simp only [mBM]; norm_num) (by simp only [mBM]; (clear * - hsz z1 z2; omega))
      (fun i hi => .inr (by rw [hwin]; simp only [mBM]; (clear * - hi; omega)))
      (fun i hi => by rw [hwin]; simp only [regs]; (clear * - hi; omega))
    refine ⟨fun i hi => ?_, fun y hy h => ?_, m3⟩
    · rw [m1 i hi, k2 _ (by rw [hwin]; simp only [regs]; (clear * - hi; omega)), Nat.one_mul, Nat.add_assoc,
        hW _ (by (clear * - hi; omega)), wStreamM, if_neg hsm]
    · rw [m2 y hy h, k2 y hy]

/-! ## The layout's numbers -/

theorem memM_v : memM = 67108864 := by norm_num [memM]
theorem wB0M_v : wB0M = 33554368 := by norm_num [wB0M]
theorem wB1M_v : wB1M = 17039360 := by norm_num [wB1M]
theorem wB2M_v : wB2M = 2097152 := by norm_num [wB2M]
theorem dB0M_v : dB0M = 8388608 := by norm_num [dB0M]
theorem dB1M_v : dB1M = 4194304 := by norm_num [dB1M]
theorem dB2M_v : dB2M = 2621440 := by norm_num [dB2M]
theorem aB0M_v : aB0M = 524288 := by norm_num [aB0M]
theorem aB1M_v : aB1M = 524320 := by norm_num [aB1M]
theorem aB2M_v : aB2M = 524352 := by norm_num [aB2M]
theorem fB0M_v : fB0M = 1048576 := by norm_num [fB0M]
theorem fB1M_v : fB1M = 1572864 := by norm_num [fB1M]
theorem fB2M_v : fB2M = 1605632 := by norm_num [fB2M]
theorem mBM_v : mBM = 5242880 := by norm_num [mBM]
theorem ws2M_v : ws1M 13 9 = 74752 := by norm_num [ws1M]
theorem ws1M_v : ws1M 16 13 = 745472 := by norm_num [ws1M]
theorem ws0M_v : wsM 19 17 8 = 4988928 := by norm_num [wsM]
theorem ok2M_v : ok1M dB2M = 2625792 := by norm_num [ok1M, dB2M]
theorem ok1M_v : ok1M dB1M = 4198656 := by norm_num [ok1M, dB1M]
theorem ok0M_v : okM dB0M = 8392960 := by norm_num [okM, dB0M]
theorem chB_v : chB = 16777216 := rfl
theorem ansB_v : ansB = 16793600 := rfl
theorem chEnd_v : chEnd = 16801792 := rfl
theorem sgB_v : sgB = 16842752 := rfl
theorem nCp_v : nCp = 278528 := rfl
theorem regs_v : regs = 256 := rfl
theorem capWM0_v : capWM 0 = 753 := layoutXM.1
theorem capWM1_v : capWM 1 = 17737 := layoutXM.2.1
theorem capWM2_v : capWM 2 = 28756 := layoutXM.2.2.1
theorem resWM_v : resWM = 35778 := layoutXM.2.2.2.1
theorem fp0_v : foldPosM pX 0 0 = 1244 := layoutM_P20.2.1
theorem fp1_v : foldPosM pX 1 0 = 1285 := layoutM_P20.2.2.1
theorem fp2_v : foldPosM pX 2 0 = 1315 := layoutM_P20.2.2.2.1


theorem lay2M {sz : ℕ} (h : memM ≤ sz) : Dec1MLay 19 13 9 dB2M wB2M aB2M fB2M fB1M sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> omega)

theorem lay1M {sz : ℕ} (h : memM ≤ sz) : Dec1MLay 19 16 13 dB1M wB1M aB1M fB1M fB0M sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> omega)

theorem lay0M {sz : ℕ} (h : memM ≤ sz) : DecM0Lay 19 19 17 40 8 dB0M wB0M aB0M fB0M sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> omega)

/-! ## The caps, the fold positions -/

theorem capM_length (π : Proof) (i : ℕ) : (capM π i).length = capNM i := by simp [capM]

theorem capOffM_div : capOffM pX 0 / 8 = 748 ∧ capOffM pX 1 / 8 = 17732 ∧ capOffM pX 2 / 8 = 28751 := by
  rw [layoutM_P20.2.2.2.2.2.1, layoutM_P20.2.2.2.2.2.2.1, layoutM_P20.2.2.2.2.2.2.2.1]; decide

theorem capWM_eq (i : ℕ) : capWM i = 5 + capOffM pX i / 8 := rfl

/-- **π's level-`i` cap on the tape** (`i < 3`): the packed words at `capWM i`. -/
theorem capM_tape (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) {i : ℕ} (hi : i < 3) :
    ∀ e (he : e < (capM π i).length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capWM i + 4 * e + m) 0 = (packBytes (capM π i)[e].toList).getD m 0 := by
  intro e he m hm
  have he' : e < 256 := by
    rw [capM_length, capNM] at he; split_ifs at he <;> omega
  have hco : capOffM pX i / 8 ≤ 28751 := by
    obtain ⟨h0, h1, h2⟩ := capOffM_div
    interval_cases i <;> (clear * - h0 h1 h2; omega)
  simp only [capM, List.getElem_map, List.getElem_range, hdD, packBytes_digW (length_wsAt _ _ _)]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [wsAt, List.getElem_map, List.getElem_range]
  rw [capWM_eq, show 5 + capOffM pX i / 8 + 4 * e + m = 5 + (capOffM pX i / 8 + 4 * e + m) by (clear * -; omega),
    tape_pw c π L hs (by (clear * - hm he' hco; omega))]

theorem foldPosM_add (i j : ℕ) : foldPosM pX i j = foldPosM pX i 0 + j := by
  unfold foldPosM; omega

theorem foldPosK_0 {j : ℕ} (hj : j < 6) : foldPosK pX j = foldPosM pX 0 0 + j := by
  rw [foldPosK, if_pos hj, foldPosM_add]
theorem foldPosK_1 {j : ℕ} (hj : j < 4) : foldPosK pX (6 + j) = foldPosM pX 1 0 + j := by
  rw [foldPosK, if_neg (by omega), if_pos (by omega), foldPosM_add, Nat.add_sub_cancel_left]
theorem foldPosK_2 {j : ℕ} (hj : j < 4) : foldPosK pX (10 + j) = foldPosM pX 2 0 + j := by
  rw [foldPosK, if_neg (by omega), if_neg (by omega), foldPosM_add, Nat.add_sub_cancel_left]

/-- A chain answer's `E` element: three words of the answer. -/
theorem rdE_alpha {M : Mem} {a : ℕ} {d : Digest} (h : ∀ m < 3, rd M (a + m) = dw d m) : rdE M a = alphaE d := by
  have h0 := h 0 (by norm_num)
  rw [Nat.add_zero] at h0
  rw [rdE_eq, alphaE, h0, h 1 (by norm_num), h 2 (by norm_num)]

theorem dec_ok2 {wd : ℕ → ℕ → BF64} {α f g : ℕ → BF64.Ext3} (h : decodeMP2 wd α f = some g) :
    2 ^ 9 ≤ (agree1G 13 9 wd α f).length := by
  unfold decodeMP2 decode1G at h; split_ifs at h with hc; exact hc
theorem dec_ok1 {wd : ℕ → ℕ → BF64} {α f g : ℕ → BF64.Ext3} (h : decodeMP1 wd α f = some g) :
    2 ^ 13 ≤ (agree1G 16 13 wd α f).length := by
  unfold decodeMP1 decode1G at h; split_ifs at h with hc; exact hc
theorem dec_ok0 {wd : ℕ → ℕ → BF64} {α f : ℕ → BF64.Ext3} {o : List BF64} (h : decodeMP0 wd α f = some o) :
    2 ^ 17 ≤ (agreeG 19 17 wd α f).length := by
  unfold decodeMP0 decodeG0 at h; split_ifs at h with hc; exact hc

/-! ## The node -/

theorem hasOut_chainLM : hasOut chainLM = false := by
  simp only [chainLM, chainIR, hasOut_seq, hasOut_storesIR, cntIR, cntBody, readAt, sdL, startPs, wordIR,
    lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, st4IR, stNext, nextIR, nextPre]
  simp only [hasOut, Bool.or_false]

set_option maxRecDepth 20000 in
/-- **`EXM` on an `S` node proof in the domain** (BLUEPRINT §6.2, M′): with no state hit, the 14 fold challenges
answered by the first-match chain (`αk k` at `foldPosK pX k`), and the three decoders succeeding on the readings of
`C_main`'s words under π's caps (`wd₀ wd₁ wd₂`), `alphaE` of the answers (`α₀ α₁ α₂`) and π's residual (`f₂`), the node
witness `Xwit π (wStreamM π out)`. The decoders' inputs are given by their values where the programs read them. -/
theorem EXM_node (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0)
    (hS : ¬ StateHit L) (αk : ℕ → Digest)
    (hα : ∀ k < 14, fmAns (fsQL π) zeroDL L (foldPosK pX k) = some (αk k))
    (wd₀ wd₁ wd₂ : ℕ → ℕ → BF64)
    (hw₀ : ∀ q < 2 ^ 19, ∀ t < 64, wd₀ q t = (readRowG 19 8 17 47 L (capM π 0) q).getD t 0)
    (hw₁ : ∀ q < 2 ^ 16, ∀ t < 48, wd₁ q t = (readRowG 16 7 0 48 L (capM π 1) q).getD t 0)
    (hw₂ : ∀ q < 2 ^ 13, ∀ t < 48, wd₂ q t = (readRowG 13 7 0 48 L (capM π 2) q).getD t 0)
    (α₀ α₁ α₂ : ℕ → BF64.Ext3) (ha₀ : ∀ j < 6, α₀ j = alphaE (αk j))
    (ha₁ : ∀ j < 4, α₁ j = alphaE (αk (6 + j))) (ha₂ : ∀ j < 4, α₂ j = alphaE (αk (10 + j)))
    (f₂ : ℕ → BF64.Ext3) (hf₂ : ∀ v < 2 ^ 9, f₂ v = resEM π v)
    (m₂ : ℕ → BF64.Ext3) (hd₂ : decodeMP2 wd₂ α₂ f₂ = some m₂)
    (m₁ : ℕ → BF64.Ext3) (hd₁ : decodeMP1 wd₁ α₁ m₂ = some m₁)
    (out : List BF64) (hd₀ : decodeMP0 wd₀ α₀ m₁ = some out) :
    EXM A c π L = some (Xwit π (wStreamM π out)) := by
  obtain ⟨hπ, hq, ht⟩ := hD
  rw [EXM, if_pos ⟨hπ, hq, ht⟩, EdXM, Eden]
  obtain ⟨s1, hM1, z1, ho1, hden⟩ := den_SM c π L hs h0
  rw [hden]
  set I := (extractorInput c π L).toArray with hI
  have hLt : L.length ≤ (extractorInput c π L).length := by
    have h1 := length_logEntries L
    rw [tape_eq]
    simp only [List.length_append, logWords, List.length_cons]
    (clear * - h1; omega)
  simp only [memM, mpwX] at z1
  -- the flag
  obtain ⟨b1, -, hM2, z2, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
    (by decide) (by norm_num)
  rw [decXM, semXIR_seq]
  generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 z2 bo
  have h6 : I.getD 6 0 ≠ 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num)]; exact hb
  rw [semXIR_ite, if_neg (by rw [b1]; exact h6), nodeM, semXIR_seq]
  -- 1. the index
  have hM3 := inv_sem I (wf_idxIR4 memM pLX) hM2
  have z3 := size_sem I (idxIR4 memM pLX) s2
  have o3 : (semXIR I (idxIR4 memM pLX) s2).o = s2.o := sem_o I _ s2 rfl
  rw [semXIR_seq]
  generalize hs3 : semXIR I (idxIR4 memM pLX) s2 = s3 at hM3 z3 o3
  have hsz3 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s3.M.size := by rw [z3, z2, z1]
  -- 2. the chain
  obtain ⟨ch1, ch2⟩ := chainLM_spec c π L hs hq ht hS s3 hM3 (by rw [chEnd_v]; (clear * - ht z1 z2 z3; omega))
  have hM4 := inv_sem I (P := chainLM) (wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide))) hM3
  have z4 := size_sem I chainLM s3
  have o4 : (semXIR I chainLM s3).o = s3.o := sem_o I _ s3 hasOut_chainLM
  rw [semXIR_seq]
  generalize semXIR I chainLM s3 = s4 at ch1 ch2 hM4 z4 o4
  have hsz4 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s4.M.size := by rw [z4]; exact hsz3
  have hX4 : ∀ a < L.length, rd s4.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [hs3, ch2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))))]
  have hpL : pLX ≤ 2 ^ 60 := by rw [layoutX.1]; norm_num
  have hs2' : memM + L.length + L.length ≤ s2.M.size := by rw [z2, z1, memM_v]; (clear * - hLt; omega)
  -- 3. level 0's word
  rw [show read0M memM pLX (capWM 0) wB0M = readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47 from rfl]
  obtain ⟨r1, r2, r3, hM5⟩ := readGIR_sem (bX := memM) (pL := pLX) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s4 hM4 (by rw [memM_v]; (clear * - ht z1 z2 z3 z4; omega)) hX4 (ht' := 19) (lv := 8) (z := 17) (occ := 47)
    (capW := capWM 0) (wB := wB0M) (cap := capM π 0)
    (fun q hq => by rw [capM_length, capNM, if_pos rfl]; (clear * - hq; omega)) (by rw [capM_length, capWM0_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  have z5 := size_sem I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4
  have o5 : (semXIR I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4).o = s4.o := sem_o I _ s4 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4 = s5 at r1 r2 r3 hM5 z5 o5
  have hX5 : ∀ a < L.length, rd s5.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [r3 a ha, hX4 a ha]
  -- 4. level 1's word
  rw [show read1M memM pLX (capWM 1) wB1M = readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48 from rfl]
  obtain ⟨q1, q2, q3, hM6⟩ := readGIR_sem (bX := memM) (pL := pLX) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s5 hM5 (by rw [z5, memM_v]; (clear * - ht z1 z2 z3 z4; omega)) hX5 (ht' := 16) (lv := 7) (z := 0) (occ := 48)
    (capW := capWM 1) (wB := wB1M) (cap := capM π 1)
    (fun q hq => by rw [capM_length, capNM, if_neg (by norm_num)]; (clear * - hq; omega))
    (by rw [capM_length, capWM1_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  have z6 := size_sem I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5
  have o6 : (semXIR I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5).o = s5.o := sem_o I _ s5 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5 = s6 at q1 q2 q3 hM6 z6 o6
  have hX6 : ∀ a < L.length, rd s6.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [q3 a ha, hX5 a ha]
  -- 5. level 2's word
  rw [show read2M memM pLX (capWM 2) wB2M = readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48 from rfl]
  obtain ⟨p1, p2, -, hM7⟩ := readGIR_sem (bX := memM) (pL := pLX) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s6 hM6 (by rw [z6, z5, memM_v]; (clear * - ht z1 z2 z3 z4; omega)) hX6 (ht' := 13) (lv := 7) (z := 0) (occ := 48)
    (capW := capWM 2) (wB := wB2M) (cap := capM π 2)
    (fun q hq => by rw [capM_length, capNM, if_neg (by norm_num)]; (clear * - hq; omega))
    (by rw [capM_length, capWM2_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  have z7 := size_sem I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6
  have o7 : (semXIR I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6).o = s6.o := sem_o I _ s6 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6 = s7 at p1 p2 hM7 z7 o7
  have hsz7 : 2 ^ 26 ≤ s7.M.size := by rw [z7, z6, z5]; (clear * - ht z1 z2 z3 z4; omega)
  -- the chain answers, kept by the reads
  have hans : ∀ k < 14, ∀ m < 4, rd s7.M (ansB + 4 * foldPosK pX k + m) = dw (αk k) m := fun k hk m hm => by
    have hp := foldPosK_lt hk
    rw [nChainM_eq] at hp
    rw [p2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega)))), q2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega)))), r2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hm hp; omega)))),
      ch1 _ (foldPosK_lt hk) _ (hα k hk) m hm]
    rfl
  -- 6. the fold challenges
  rw [semXIR_seq, acpM, semXIR_seq, semXIR_seq, semXIR_seq]
  obtain ⟨a01, a02, hM8a, z8a, o8a⟩ := acp3IR_sem I s7 hM7 (by (clear * - z1 z2 z3 z4 z5 z6 z7 hsz7; omega)) (src := ansB + 4 * foldPosM pX 0 0)
    (dst := aB0M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) 6 (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 0 0) aB0M 6) s7 = s8a at a01 a02 hM8a z8a o8a
  obtain ⟨a11, a12, hM8b, z8b, o8b⟩ := acp3IR_sem I s8a hM8a (by (clear * - ht z1 z2 z3 z4 z5 z6 z7 z8a; omega)) (src := ansB + 4 * foldPosM pX 1 0)
    (dst := aB1M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) 4 (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 1 0) aB1M 4) s8a = s8b at a11 a12 hM8b z8b o8b
  obtain ⟨a21, a22, hM8, z8, o8⟩ := acp3IR_sem I s8b hM8b (by (clear * - ht z1 z2 z3 z4 z5 z6 z7 z8a z8b; omega)) (src := ansB + 4 * foldPosM pX 2 0)
    (dst := aB2M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) 4 (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega)))
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 2 0) aB2M 4) s8b = s8 at a21 a22 hM8 z8 o8
  have hsz8 : 2 ^ 26 ≤ s8.M.size := by rw [z8, z8b, z8a]; exact hsz7
  -- 7. the residual
  obtain ⟨f1, f2, hM9, z9, o9⟩ := thcpIR_sem I s8 hM8 (a := resWM) (dst := fB2M) (n := 3 * 2 ^ 9)
    (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - z1 z2 z3 z4 z5 z6 z7 z8a z8b z8 hsz8; omega)))
  generalize semXIR I (thcpIR resWM fB2M (3 * 2 ^ 9)) s8 = s9 at f1 f2 hM9 z9 o9
  have hsz9 : memM ≤ s9.M.size := by rw [z9, memM_v]; omega
  -- the fold challenges in place
  have hA0 : ∀ i < 6, ∀ m < 3, rd s8.M (aB0M + 3 * i + m) = dw (αk i) m := fun i hi m hm => by
    rw [a22 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a12 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a01 i hi m hm,
      show ansB + 4 * foldPosM pX 0 0 + 4 * i + m = ansB + 4 * foldPosK pX i + m by rw [foldPosK_0 hi]; ring,
      hans i (by (clear * - hi; omega)) m (by (clear * - hm; omega))]
  have hA1 : ∀ i < 4, ∀ m < 3, rd s8.M (aB1M + 3 * i + m) = dw (αk (6 + i)) m := fun i hi m hm => by
    rw [a22 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a11 i hi m hm, a02 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))),
      show ansB + 4 * foldPosM pX 1 0 + 4 * i + m = ansB + 4 * foldPosK pX (6 + i) + m by rw [foldPosK_1 hi]; ring,
      hans (6 + i) (by (clear * - hi; omega)) m (by (clear * - hm; omega))]
  have hA2 : ∀ i < 4, ∀ m < 3, rd s8.M (aB2M + 3 * i + m) = dw (αk (10 + i)) m := fun i hi m hm => by
    rw [a21 i hi m hm, a12 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), a02 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))),
      show ansB + 4 * foldPosM pX 2 0 + 4 * i + m = ansB + 4 * foldPosK pX (10 + i) + m by rw [foldPosK_2 hi]; ring,
      hans (10 + i) (by (clear * - hi; omega)) m (by (clear * - hm; omega))]
  -- the frame of steps 6, 7 (outside the fold challenges and the residual)
  have K79 : ∀ y, regs ≤ y → (y < aB0M ∨ aB2M + 12 ≤ y) → (y < fB2M ∨ fB2M + 3 * 2 ^ 9 ≤ y) →
      rd s9.M y = rd s7.M y := fun y hy h1 h2 => by
    rw [f2 y hy h2, a22 y hy (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - h1 h2; omega))), a12 y hy (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - h1 h2; omega))), a02 y hy (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - h1 h2; omega)))]
  -- 8. level 2's decoder
  have hW2 : ∀ q < 2 ^ 13, ∀ t < 48, rdK s9.M (wB2M + 48 * q + t) = wd₂ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K79 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), hw₂ q hq t ht']
    exact (show 0 + 48 = 48 from rfl) ▸ p1 q hq t (by omega)
  have hAl2 : ∀ i < 4, rdE s9.M (aB2M + 3 * i) = α₂ i := fun i hi => by
    rw [ha₂ i hi]
    exact rdE_alpha fun m hm => by rw [f2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), hA2 i hi m hm]
  have hF2 : ∀ v < 2 ^ 9, rdE s9.M (fB2M + 3 * v) = f₂ v := fun v hv => by
    rw [hf₂ v hv, rdE_eq, resEM]
    have hc : ∀ m < 3, rd s9.M (fB2M + 3 * v + m) = pw π (resOffM pX / 8 + 3 * v + m) := fun m hm => by
      have hr : resOffM pX / 8 = 35773 := by rw [layoutM_P20.2.2.2.2.2.2.2.2.1]
      rw [Nat.add_assoc, f1 _ (by (clear * - hv hm; omega)), resWM_v, show 35778 + (3 * v + m) = 5 + (resOffM pX / 8 + 3 * v + m) by
        (clear * - hr; omega), tape_pw c π L hs (by (clear * - hv hm hr; omega))]
    have c0 := hc 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at c0
    rw [c0, hc 1 (by norm_num), hc 2 (by norm_num)]
  obtain ⟨e21, e22, e23, hM10⟩ := decMP2IR_sem I s9 hM9 (lay2M hsz9) wd₂ α₂ f₂ hW2 hAl2 hF2
  have z10 := size_sem I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9
  have o10 : (semXIR I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9).o = s9.o := sem_o I _ s9 rfl
  rw [decide_eq_true (dec_ok2 hd₂)] at e21
  have hm₂ := e22 m₂ hd₂
  generalize semXIR I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9 = s10 at e21 hm₂ e23 hM10 z10 o10
  -- 9. the flag, level 1's decoder
  obtain ⟨s11, hM11, z11, o11, k11, e11⟩ := flagIte_sem I s10 hM10 (a := ok1M dB2M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) e21
    (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) okL1)
  rw [okL2, e11, semXIR_seq]
  have hsz11 : memM ≤ s11.M.size := by rw [z11, z10]; exact hsz9
  have K11 : ∀ y, regs ≤ y → (y < dB2M ∨ dB2M + ws1M 13 9 ≤ y) → (y < fB1M ∨ fB1M + 3 * 2 ^ 13 ≤ y) →
      rd s11.M y = rd s9.M y := fun y hy h1 h2 => by rw [k11 y hy, e23 y hy h1 h2]
  have hW1 : ∀ q < 2 ^ 16, ∀ t < 48, rdK s11.M (wB1M + 48 * q + t) = wd₁ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), K79 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))),
      p2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), hw₁ q hq t ht']
    exact (show 0 + 48 = 48 from rfl) ▸ q1 q hq t (by omega)
  have hAl1 : ∀ i < 4, rdE s11.M (aB1M + 3 * i) = α₁ i := fun i hi => by
    rw [ha₁ i hi]
    exact rdE_alpha fun m hm => by
      rw [K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), f2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), hA1 i hi m hm]
  have hF1 : ∀ v < 2 ^ 13, rdE s11.M (fB1M + 3 * v) = m₂ v := fun v hv => by
    rw [← hm₂ v hv]
    exact rdE_congr fun m hm => k11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hv hm; omega)))
  obtain ⟨e11', e12, e13, hM12⟩ := decMP1IR_sem I s11 hM11 (lay1M hsz11) wd₁ α₁ m₂ hW1 hAl1 hF1
  have z12 := size_sem I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11
  have o12 : (semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11).o = s11.o := sem_o I _ s11 rfl
  rw [decide_eq_true (dec_ok1 hd₁)] at e11'
  have hm₁ := e12 m₁ hd₁
  generalize semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11 = s12 at e11' hm₁ e13 hM12 z12 o12
  -- 10. the flag, level 0's decoder
  obtain ⟨s13, hM13, z13, o13, k13, e13'⟩ := flagIte_sem I s12 hM12 (a := ok1M dB1M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) e11'
    (.seq (decMP0IRW dB0M wB0M aB0M fB0M) okL0)
  rw [okL1, e13', semXIR_seq]
  have hsz13 : memM ≤ s13.M.size := by rw [z13, z12, z11, z10]; exact hsz9
  have K13 : ∀ y, regs ≤ y → (y < dB1M ∨ dB1M + ws1M 16 13 ≤ y) → (y < fB0M ∨ fB0M + 3 * 2 ^ 17 ≤ y) →
      rd s13.M y = rd s11.M y := fun y hy h1 h2 => by rw [k13 y hy, e13 y hy h1 h2]
  have hW0 : ∀ q < 2 ^ 19, ∀ t < 64, rdK s13.M (wB0M + 64 * q + t) = wd₀ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K13 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))),
      K79 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), p2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))),
      q2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega))) (.inr (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hq ht'; omega)))), hw₀ q hq t ht']
    exact (show 17 + 47 = 64 from rfl) ▸ r1 q hq t (by omega)
  have hAl0 : ∀ i < 6, rdE s13.M (aB0M + 3 * i) = α₀ i := fun i hi => by
    rw [ha₀ i hi]
    exact rdE_alpha fun m hm => by
      rw [K13 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), K11 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))),
        f2 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega))) (.inl (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hi hm; omega)))), hA0 i hi m hm]
  have hF0 : ∀ v < 2 ^ 17, rdE s13.M (fB0M + 3 * v) = m₁ v := fun v hv => by
    rw [← hm₁ v hv]
    exact rdE_congr fun m hm => k13 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hv hm; omega)))
  obtain ⟨e01, e02, e03, hM14⟩ := decMP0IRW_sem I s13 hM13 (lay0M hsz13) wd₀ α₀ m₁ hW0 hAl0 hF0
  have z14 := size_sem I (decMP0IRW dB0M wB0M aB0M fB0M) s13
  have o14 : (semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13).o = s13.o := sem_o I _ s13 rfl
  rw [decide_eq_true (dec_ok0 hd₀)] at e01
  have hout := e02 out hd₀
  generalize semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13 = s14 at e01 hout e03 hM14 z14 o14
  -- 11. the flag, the stream block, the node output
  obtain ⟨s15, hM15, z15, o15, k15, e15⟩ := flagIte_sem I s14 hM14 (a := okM dB0M) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) e01
    (.seq streamM (outIR mBM))
  rw [okL0, e15, semXIR_seq]
  have hsz15 : memM ≤ s15.M.size := by rw [z15, z14]; exact hsz13
  obtain ⟨st1, -, hM16, z16, o16⟩ := streamM_sem c π L hs s15 hM15 hsz15 out fun j hj => by
    rw [k15 _ (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - hj; omega))), ← rdK_toBitVec, hout j (by omega)]
  rw [outIR_sem c π L hs _ hM16 (mB := mBM) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * -; omega))) (by rw [z16]; ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> (clear * - z1 z2 z3 z4 z5 z6 z7 z8a z8b z8 z9 z10 z11 z12 z13 z14 z15 hsz15; omega))) (wStreamM π out) st1, o16, o15,
    o14, o13, o12, o11, o10, o9, o8, o8b, o8a, o7, o6, o5, o4, o3, bo, ho1, Array.toList_empty, List.nil_append]
  exact decodeWit_outWords π _

end Lvm.X
