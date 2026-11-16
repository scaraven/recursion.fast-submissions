/- `LvmMPXReadOff` (GOLF2 off-path move, group 26 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXChainL, LvmMPXLayout, LvmMPXRead,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXChainL
import LvmMPXLayout
import LvmMPXRead

-- ===== from `LvmXChainL` =====

section
section
section LvmXChainProg
namespace Lvm.X
open RecursionFast

theorem chEnd_eq : chEnd = 16801792 := rfl
theorem layout_eq : chB = 2 ^ 24 ∧ hB = 2 ^ 24 + 2 ^ 13 ∧ ansB = 2 ^ 24 + 2 ^ 14 ∧
    chEnd = 2 ^ 24 + 2 ^ 14 + 2 ^ 13 := by
  norm_num [chB, hB, ansB, chEnd]

end Lvm.X
end LvmXChainProg
end
end

section
section
section LvmXChainLoop
namespace Lvm.X
open RecursionFast

/-- The heap is kept by every block of a word but the record. -/
theorem lo_restQ : Lo qryIR := lo_qryIR

end Lvm.X
end LvmXChainLoop
end
end

section
section
section LvmXChainLoop
namespace Lvm.X
open RecursionFast

theorem Keep.refl (s : St) : Keep s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end Lvm.X
end LvmXChainLoop
end
end

section
section
section LvmXChainTop
namespace Lvm.X
open RecursionFast

theorem cnt_regs (pL : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (hw : r ≠ rP ∧ r ≠ rN ∧ r ≠ rA ∧ r ≠ rCW ∧ r ≠ rQL ∧ r ≠ rT1 ∧ r ≠ rT2 ∧ r ≠ rKc ∧ r ≠ rKd ∧
      r ≠ rCn5) : rd (semXIR I (cntIR pL) s).M r = rd s.M r := by
  obtain ⟨a, b, c, d, e, f, g, k, l, m⟩ := hw
  refine frame I (cntIR pL) s (wf_cntIR pL) hM r hr ?_
  simp +decide [cntIR, cntBody, readAt, ceil8Ps, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, List.cons_append, List.nil_append]
  simp only [rP, rN, rA, rCW, rQL, rT1, rT2, rKc, rKd, rCn5] at *
  lia

end Lvm.X
end LvmXChainTop
end
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The query at chain position `p`**, the previous answer being `st`. -/
def fsQL (π : Proof) (p : ℕ) (st : Digest) : ByteArray :=
  if p = 0 then q0Query else digestBytes st ++ π.extract (msgL p).1 ((msgL p).1 + (msgL p).2)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem msgs_ok : ((fsMsgs pX).take (nChain pX - 1)).all msgOkL = true := layout_all_P20.2.2.2.2.2.1

theorem nChain_le : nChain pX - 1 ≤ (fsMsgs pX).length := by
  rw [layout_P20.2.1, layout_P20.2.2.2.2.2.1]; decide

theorem msgL_ok {p : ℕ} (hp0 : 0 < p) (hp : p < nChain pX) :
    (msgL p).1 % 8 = 0 ∧ (msgL p).2 % 8 = 0 ∧ (msgL p).1 + (msgL p).2 ≤ piSize pX ∧
      32 + (msgL p).2 ≤ queryCap := by
  have hl := nChain_le
  have hm : (fsMsgs pX)[p - 1]'(by omega) ∈ (fsMsgs pX).take (nChain pX - 1) :=
    List.mem_iff_getElem.mpr ⟨p - 1, by simp; omega, by simp⟩
  have h := List.all_eq_true.mp msgs_ok _ hm
  unfold msgL
  rw [List.getD_eq_getElem _ _ (by (clear * - hp0 hp hl; omega))]
  simp only [msgOkL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem msgL_last : (msgL (nChain pX)).1 = 141664 := by
  rw [layout_P20.2.1, msgL, show 1247 - 1 = 1246 from rfl, layout_P20.2.2.2.2.2.2.1]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem fsQL_size {π : Proof} (hs : π.size = piSize pX) {p : ℕ} (hp0 : 0 < p) (hp : p < nChain pX)
    (st : Digest) : (fsQL π p st).size = 32 + (msgL p).2 := by
  obtain ⟨-, -, h3, -⟩ := msgL_ok hp0 hp
  rw [fsQL, if_neg (by (clear * - hp0; omega)), ByteArray.size_append, extract_size π (by (clear * - hs h3; omega)), digestBytes_size]

theorem fsQL_data {π : Proof} (p : ℕ) (hp0 : 0 < p) (st : Digest) :
    (fsQL π p st).data.toList =
      st.toList ++ (π.extract (msgL p).1 ((msgL p).1 + (msgL p).2)).data.toList := by
  rw [fsQL, if_neg (by omega), ByteArray.data_append, Array.toList_append]
  rfl

theorem msgs_cap : (fsMsgs pX).all (fun m => 32 + m.2 ≤ queryCap) = true := layout_all_P20.2.2.2.2.1

theorem msgL_cap (p : ℕ) : 32 + (msgL p).2 ≤ queryCap := by
  unfold msgL
  by_cases h : p - 1 < (fsMsgs pX).length
  · rw [List.getD_eq_getElem _ _ h]
    exact of_decide_eq_true (List.all_eq_true.mp msgs_cap _ (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]; decide

/-- **Every query after `q₀` carries its state.** -/
theorem stateIn_fsQL (π : Proof) {p : ℕ} (hp0 : 0 < p) (st : Digest) :
    stateIn (fsQL π p st) = some st := by
  have hc := msgL_cap p
  have hd := fsQL_data (π := π) p hp0 st
  have hz : (fsQL π p st).size = 32 + (π.extract (msgL p).1 ((msgL p).1 + (msgL p).2)).size := by
    rw [fsQL, if_neg (by (clear * - hp0; omega)), ByteArray.size_append, digestBytes_size]
  generalize msgL p = m at hc hd hz
  have he : (π.extract m.1 (m.1 + m.2)).size ≤ m.2 := by
    rw [ByteArray.size_extract]; (clear * -; omega)
  generalize fsQL π p st = q at hd hz ⊢
  generalize π.extract m.1 (m.1 + m.2) = x at hd hz he
  have hl : q.data.toList.length = q.size := Array.length_toList
  rw [stateIn, if_pos ⟨by (clear * - hz hl; omega), by (clear * - hc hz he hl; omega)⟩]
  refine congrArg some (Vector.ext fun i hi => ?_)
  rw [Vector.getElem_ofFn, List.getD_eq_getElem _ _ (by (clear * - hz hl hi; omega)), List.getElem_of_eq hd,
    List.getElem_append_left (by simp; omega), Vector.getElem_toList]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem chTabL_getD {p k : ℕ} (hp : p ≤ nChain pX) (hk : k < 4) :
    chTabL.getD (4 * p + k) 0 = (tabEntL p).getD k 0 :=
  getD_flatMap4 tabEntL tabEntL_length _ p k (by (clear * - hp; omega)) hk

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The table realises `V_S`'s chain** on every tape of a proof of `piSize` bytes. -/
theorem tabW_chTabL (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) :
    TabW (extractorInput c π L).toArray (fsQL π) (nChain pX) chTabL := by
  have hp1 : π.size = 332336 := hs.trans piSize_eq
  refine ⟨chTabL_length, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTabL_getD hpN (by norm_num), tabEntL, if_neg (by (clear * - hp0; omega))]
    show (toWord (5 + (msgL p).1 / 8)).toNat < 2 ^ 62
    have : (msgL p).1 ≤ 332336 := by
      rcases Nat.lt_or_ge p (nChain pX) with h | h
      · have := (msgL_ok hp0 h).2.2.1; rw [piSize_eq] at this; (clear * - this; omega)
      · have hpe : p = nChain pX := by (clear * - hpN h; omega)
        rw [hpe, msgL_last]; (clear * -; omega)
    generalize msgL p = m at this
    rw [toNat_toWord (by (clear * - this; omega))]; (clear * - this; omega)
  · obtain ⟨ho, hl, hol, hq⟩ := msgL_ok hp0 hpN'
    have e0 := chTabL_getD hpN (k := 0) (by norm_num)
    have e1 := chTabL_getD hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntL, if_neg (by (clear * - hp0; omega))]
    have hz := fsQL_size hs hp0 hpN' st
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

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **`chainL_spec`**: on a domain tape of an `S` proof (`piSize` bytes) whose log has no state
hit, for every position `p < nChain pX` that the first-match chain answers with `a`, the
machine's answer at `ansB + 4p` is `a`'s four words; the heap outside the chain's region is kept. -/
theorem chainL_spec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nChain pX, ∀ a, fmAns (fsQL π) zeroDL L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray chainL s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray chainL s).M y = rd s.M y) := by
  have hT : ∀ p st, 0 < p → stateIn (fsQL π p st) = some st := fun p st hp => stateIn_fsQL π hp st
  obtain ⟨-, hans, hheap⟩ := chainIR_sem c π L (hs_posL hs) hq ht (N := nChain pX)
    (by rw [nChain_eq]; norm_num) (tabW_chTabL c π L hs) (seedOK_sdL _) (st₀ := zeroDL)
    (by simp [fsQL, q0Query, ByteArray.size, q0Bytes]) s hM hsz
  refine ⟨fun p hp a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nChain pX) (st₀ := zeroDL) hT hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nChain pX) (st₀ := zeroDL) (L := L) (T := fsQL π) hT hS).1
  have hpl : p < (scanC (fsQL π) (nChain pX) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQL π) (nChain pX) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [show chainL = chainIR (posL (piSize pX)) (nChain pX) chTabL sdL from rfl, hans p hpl m hm, hg]

end Lvm.X
end

-- ===== from `LvmMPXLayout` =====

section
namespace Lvm.X
open RecursionFast Lvm

theorem foldPosK_lt {k : ℕ} (hk : k < 14) : foldPosK pX k < nChainM pX := by
  have h := layoutM_P20
  simp only [foldPosK, foldPosM, h.1, nChainM_eq] at *
  have e0 : lvlFsM pX 0 = 41 := by decide +kernel
  have e1 : lvlFsM pX 1 = 30 := by decide +kernel
  rw [e0, e1]
  split_ifs <;> simp <;> omega

end Lvm.X
end

-- ===== from `LvmMPXRead` =====

section
namespace Lvm.X
open RecursionFast

theorem readGIR_rec (bX pL capW wB : ℕ) : readGIR bX pL capW wB (2 ^ 15) 8 (64 - crOcc) crOcc =
    readIR bX pL capW wB := rfl

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`. -/
theorem readGIR_nw (bX pL capW wB nPos D z occ : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) :
    ¬ Writes (readGIR bX pL capW wB nPos D z occ) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [readGIR, crPosG, crLd4, crCapGPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopyG, crZeroG, crZeroBody, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA,
    crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  omega

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast

/-- The shape check: the read depths and occupancy are `layoutM_P20`'s (`19 − 8`, `16 − 7`, `13 − 7`; the root leaf
of `376 = 8 · 47` bytes, the others `384 = 8 · 48`). -/
theorem readM_shape : readDepthM pX 0 = 11 ∧ readDepthM pX 1 = 9 ∧ readDepthM pX 2 = 6 ∧
    (mainL pX 0).row = 8 * 47 ∧ (mainL pX 1).row = 8 * 48 ∧ (mainL pX 2).row = 8 * 48 := by
  decide +kernel

end Lvm.X
end
