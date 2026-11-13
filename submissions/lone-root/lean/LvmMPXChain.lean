-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (i)): the chain scan's specification through `C_main`'s fold
-- challenges. Adapted from `LvmXChainL.lean` (`msgL_ok`, `msgL_last`, `chTabL_getD`, `tabW_chTabL`, `chainL_spec`) at
-- the table `chTabM` (`nChainM pX = 1319` targets, `LvmMPXLayout`).
import LvmMPXLayout

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
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [msgOkL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem msgLM_last : (msgL (nChainM pX)).1 = 286136 := by
  rw [nChainM_eq, msgL]
  decide +kernel

theorem chTabM_getD {p k : ℕ} (hp : p ≤ nChainM pX) (hk : k < 4) :
    chTabM.getD (4 * p + k) 0 = (tabEntL p).getD k 0 :=
  getD_flatMap4 tabEntL tabEntL_length _ p k (by omega) hk

/-- **The table realises `V_S`'s chain** through `C_main`'s folds. -/
theorem tabW_chTabM (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) :
    TabW (extractorInput c π L).toArray (fsQL π) (nChainM pX) chTabM := by
  have hp1 : π.size = 332336 := hs.trans piSize_eq
  refine ⟨chTabM_length, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTabM_getD hpN (by norm_num), tabEntL, if_neg (by omega)]
    show (toWord (5 + (msgL p).1 / 8)).toNat < 2 ^ 62
    have : (msgL p).1 ≤ 332336 := by
      rcases Nat.lt_or_ge p (nChainM pX) with h | h
      · have := (msgLM_ok hp0 h).2.2.1; rw [piSize_eq] at this; omega
      · have hpe : p = nChainM pX := by omega
        rw [hpe, msgLM_last]; omega
    generalize msgL p = m at this
    rw [toNat_toWord (by omega)]; omega
  · obtain ⟨ho, hl, hol, hq⟩ := msgLM_ok hp0 hpN'
    have e0 := chTabM_getD hpN (k := 0) (by norm_num)
    have e1 := chTabM_getD hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntL, if_neg (by omega)]
    have hz : (fsQL π p st).size = 32 + (msgL p).2 := by
      rw [fsQL, if_neg (by omega), ByteArray.size_append, extract_size π (by omega), digestBytes_size]
    refine ⟨by rw [hz]; rfl, by rw [hz]; omega, fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQL_data p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msgL p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · rw [piSize_eq] at hol
      generalize msgL p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by omega⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by omega), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by omega,
        tape_getD_proof c π L (by rw [hp1]; omega), ← List.getD_eq_getElem _ 0,
        extract_words π (by rw [hp1]; omega) (by omega)]

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
