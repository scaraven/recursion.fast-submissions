-- New for lvm2 MP-B cap pruning (CAP-X2, 2026-11-17): what S2GB's extractor returns on a node proof in the domain
-- (`EXS_node`'s twin for `EXB20`). Proof-help statements of `ext_eqB_gen`; `EXB_node` is the interface X2 uses.
import LvmS2GBExtProg
import LvmS2GBExtOK
import LvmS2GBExtNodeOut
import LvmXSNodeSem
import LvmS2GBExtNodeFacts

/-!
# What `EXB20` returns on a node

* `capSB π i`, `XwitB π w` (in `LvmS2GBExtNodeOut`): the sent caps and the node witness;
* `chainLS_specB`, `capSB_tape`: the chain and the sent caps at the log position of `|π|`;
* `EXB_leaf`: the leaf (`den_SB`: the parse with the size range);
* **`EXB_node`**: on an `S` node proof in the domain and in the size range, the chain's fold challenges, the
  decoders' success on the walks from the sent caps and π's residual give `XwitB` (`EXS_node`'s twin).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-! ## The chain and the caps at the log position of `|π|` -/

/-- **The table realises `V_S`'s chain** at a stage, on a proof of at least `st.pz` bytes (`tabW_chTabS`). -/
theorem tabW_chTabSB (st : XStage) (hp : ProgOK st) (c : Digest) (π : Proof) (L : Log) (hs : st.pz ≤ π.size) :
    TabW (extractorInput c π L).toArray (fsQLS st π) (nChainS st) (chTabS st) := by
  have hpz := hp.pz_lt
  refine ⟨chTabS_length st, fun p hp0 hpN => ⟨?_, fun hpN' d => ?_⟩⟩
  · rw [chTabS_getD st hpN (by norm_num), tabEntS, if_neg (by (clear * - p st π hp0 hs; omega))]
    show (toWord (5 + (msgLS st p).1 / 8)).toNat < 2 ^ 62
    have : (msgLS st p).1 ≤ st.pz := by have := (msgLS_ok st hp hp0 hpN).2.2.1; (clear * - st p π this hs; omega)
    generalize msgLS st p = m at this
    rw [toNat_toWord (by (clear * - m st π hs hpz p this; omega))]; (clear * - m st π hs hpz p this; omega)
  · obtain ⟨ho, hl, hol, hq⟩ := msgLS_ok st hp hp0 (by (clear * - hpN hs; omega))
    have e0 := chTabS_getD st hpN (k := 0) (by norm_num)
    have e1 := chTabS_getD st hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntS, if_neg (by (clear * - p st π hp0 hs; omega))]
    have hz : (fsQLS st π p d).size = 32 + (msgLS st p).2 := by
      rw [fsQLS, if_neg (by (clear * - p st π hp0 hs; omega)), ByteArray.size_append, extract_size π (by (clear * - st p π hs ho hl hol; omega)), digestBytes_size]
    refine ⟨by rw [hz]; rfl, by rw [hz]; (clear * - st p π hs hpz d ho hl hol; omega), fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQLS_data st p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msgLS st p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · generalize msgLS st p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by (clear * - m st π p d j ho hs; omega)⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by (clear * - m st π p d j hl a hs; omega)⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by (clear * - a st π hs hpz p d j h4 m n hj hol; omega)), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by (clear * - a j st π p d m n hs; omega),
        tape_getD_proof c π L (by (clear * - a j st π p d h4 m n hj hol hs; omega)), ← List.getD_eq_getElem _ 0,
        extract_words π (by (clear * - hol hs; omega)) (by (clear * - j n st π p d h4 m a hj hs; omega))]

/-- **`chainLS_spec` at the log position of `|π|`** (a proof of at least `st.pz` bytes). -/
theorem chainLS_specB (st : XStage) (hp : ProgOK st) (c : Digest) (π : Proof) (L : Log) (hs : st.pz ≤ π.size)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nChainS st, ∀ a, fmAns (fsQLS st π) zeroDL L p = some a → ∀ m < 4,
      Lvm.X.rd (semXIR (extractorInput c π L).toArray (chainIR (posL π.size) (nChainS st) (chTabS st) sdL) s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      Lvm.X.rd (semXIR (extractorInput c π L).toArray (chainIR (posL π.size) (nChainS st) (chTabS st) sdL) s).M y = Lvm.X.rd s.M y) := by
  have hT : ∀ p d, 0 < p → stateIn (fsQLS st π p d) = some d := fun p d hp0 => stateIn_fsQLS st hp π hp0 d
  obtain ⟨-, hans, hheap⟩ := chainIR_sem (pL := posL π.size) c π L (hs_posL rfl) hq ht (N := nChainS st)
    hp.nCh_lt (tabW_chTabSB st hp c π L hs) (seedOK_sdL _) (st₀ := zeroDL)
    (by simp [fsQLS, q0Query, ByteArray.size, q0Bytes]) s hM hsz
  refine ⟨fun p hpN a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nChainS st) (st₀ := zeroDL) hT hS hpN
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nChainS st) (st₀ := zeroDL) (L := L) (T := fsQLS st π) hT hS).1
  have hpl : p < (scanC (fsQLS st π) (nChainS st) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQLS st π) (nChainS st) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [hans p hpl m hm, hg]

theorem hasOut_chainIRB (pL N : ℕ) (tab : List Word) : hasOut (chainIR pL N tab sdL) = false := by
  simp only [chainIR, hasOut_seq, hasOut_storesIR, cntIR, cntBody, readAt, sdL, startPs, wordIR,
    lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, st4IR, stNext, nextIR, nextPre]
  simp only [hasOut, Bool.or_false]

theorem capSB_length (π : Proof) (i : ℕ) : (capSB π i).length = 2 ^ capBB i := by simp [capSB]

/-- π's digests at a level's cap offset on the tape (`capS_tape`'s, `n ≤ 2^7` digests, a proof of at least `st.pz`
bytes). -/
theorem capB_tape (st : XStage) (hp : ProgOK st) (c : Digest) (π : Proof) (L : Log) (hle : st.pz ≤ π.size)
    {i n : ℕ} (hi : i < 3) (hn : n ≤ 2 ^ 7) : ∀ e < n, ∀ m < 4,
      (extractorInput c π L).toArray.getD (capWS st i + 4 * e + m) 0 =
        (packBytes (hdD π (capOffS st i / 8 + 4 * e)).toList).getD m 0 := by
  intro e he m hm
  have hco : capOffS st i / 8 + 4 * 2 ^ 7 ≤ st.pz / 8 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · have := hp.cap0; omega
    · exact hp.cap1
    · exact hp.cap2
  have h8 : st.pz / 8 ≤ π.size / 8 := Nat.div_le_div_right hle
  simp only [hdD, packBytes_digW (length_wsAt _ _ _)]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [wsAt, List.getElem_map, List.getElem_range]
  rw [show capWS st i + 4 * e + m = 5 + (capOffS st i / 8 + 4 * e + m) by rw [capWS]; omega,
    tape_pwN c π L rfl (by omega)]

/-- **π's level-`i` sent cap on the tape** at S2GB (`capS_tape`'s twin, `i < 3`). -/
theorem capSB_tape (c : Digest) (π : Proof) (L : Log) (hs : SzB π) {i : ℕ} (hi : i < 3) :
    ∀ e (he : e < (capSB π i).length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capWS stB20 i + 4 * e + m) 0 =
        (packBytes (capSB π i)[e].toList).getD m 0 := by
  intro e he m hm
  have hle : stB20.pz ≤ π.size := by rw [stB20_pz]; exact szB_lo hs
  have hn : 2 ^ capBB i ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by unfold capBB; split <;> omega)
  have he' : e < 2 ^ capBB i := lt_of_lt_of_eq he (capSB_length π i)
  simp only [capSB, List.getElem_map, List.getElem_range]
  exact capB_tape stB20 progOK_stB20 c π L hle hi hn e he' m hm

/-! ## The parse, the leaf -/

/-- **The parse at S2GB** (`den_SS` with the size range). -/
theorem den_SB (c : Digest) (π : Proof) (L : Log) {dec : XIR} (hwf : WF dec) (hs : SzB π)
    (h0 : π.data[0]? = some 0x53) :
    ∃ s1 : St, Inv s1.M ∧ s1.M.size = memM + mpwX * (extractorInput c π L).length ∧ s1.o = #[] ∧
      den memM mpwX (extIRWithB loB hiB dec) (extractorInput c π L) =
        (semXIR (extractorInput c π L).toArray dec s1).o.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0' : Inv (initSt (memM + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  refine ⟨semXIR I (parseIRB loB hiB) (initSt (memM + mpwX * (extractorInput c π L).length)),
    inv_sem I (wf_extIRWithB (lo := loB) (hi := hiB) hwf).1 h0', by rw [size_sem, initSt_M, size_runPrims,
      Array.size_replicate], by rw [parseB_o, initSt_o], ?_⟩
  have hk : Lvm.X.rd (semXIR I (parseIRB loB hiB) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsK ≠ 0 := by
    rw [parseB_isK _ _ I _ h0']
    have hb := tape_byte0 c π L h0
    have e : I.getD 5 0 &&& 0xFF = kindS := by
      apply BitVec.eq_of_toNat_eq
      rw [lowByte, hI, getD_toArray, hb]; rfl
    rw [if_pos e]; decide
  have hz : Lvm.X.rd (semXIR I (parseIRB loB hiB) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsSz ≠ 0 :=
    (parseB_sz loB hiB (show piStatic P20B < 2 ^ 64 by rw [sizes_P20B.1.1]; norm_num)
      (by rw [hiB_val]; norm_num) I _ h0' (szB_lt hs)
      (by rw [hI, getD_toArray, tape_getD4])).2 (by rw [hiB_eq]; exact hs)
  rw [den, extIRWithB, semXIR_seq, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]

/-- **`EXB20` on an `S` leaf proof** (`EXS_leaf`'s twin). -/
theorem EXB_leaf (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hs : SzB π) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 = 0) :
    EXB20 A c π L = some (leafW π) := by
  by_cases hD : InDomE c π L
  · rw [EXB20, if_pos hD, EdXB20, Eden]
    obtain ⟨s1, hM1, -, ho1, hden⟩ := den_SB c π L wf_decXB20 hs h0
    rw [hden]
    set I := (extractorInput c π L).toArray with hI
    obtain ⟨b1, -, hM2, -, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
      (by decide) (by norm_num)
    rw [decXB20, semXIR_seq]
    generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 bo
    have h6 : I.getD 6 0 = 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pwB c π L hs (by norm_num), hb]
    rw [semXIR_ite, if_pos (by rw [b1, h6]), leafIR, semXIR_seq]
    obtain ⟨e1, -⟩ := emitIR_sem I s2 hM2 (toWord 0)
    have hM3 := inv_sem I (wf_emitIR (toWord 0)) hM2
    generalize semXIR I (emitIR (toWord 0)) s2 = s3 at e1 hM3
    obtain ⟨t1, -⟩ := tcpIR_sem I s3 hM3 (a := 15) (n := 5) (by norm_num)
    rw [t1, e1, bo, ho1]
    have t2 := wsAt_tapeB c π L hs (a := 10) (n := 5) (by norm_num)
    simp only [show (5 + 10 : ℕ) = 15 from rfl] at t2
    rw [t2]
    have hw : witWords (leafW π) = toWord 0 :: wsAt (pw π) 10 5 := by
      simp only [leafW, witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat',
        show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
      simp [wsAt]
    rw [Array.toList_empty, List.nil_append, List.singleton_append, ← hw]
    exact decodeWit_witWords _ (pw π 14).isLt
  · rw [EXB20, if_neg hD, EoutXB20, if_pos h0, if_pos hs, if_pos hb]

/-! ## The node -/

/-- `okL0B` at a stage. -/
def okL0G (st : XStage) : XIR :=
  .seq (.blk [.const eA (toWord (okM dB0M))]) (.seq (.load eW eA) (.ite eW (.seq (streamS st) (outIRB mBM)) (.blk [])))

/-- `okL1B` at a stage. -/
def okL1G (st : XStage) : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB1M))]) (.seq (.load eW eA) (.ite eW (.seq (dec0S st) (okL0G st)) (.blk [])))

/-- `okL2B` at a stage. -/
def okL2G (st : XStage) : XIR :=
  .seq (.blk [.const eA (toWord (ok1M dB2M))]) (.seq (.load eW eA)
    (.ite eW (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) (okL1G st)) (.blk [])))

theorem okL2B_eq : okL2B = okL2G stB20 := rfl

/-- **`EXB20` on an `S` node proof in the domain** (`EXS_node`'s twin: the walks start from the sent caps, `h − c`
levels; the left child is the static part `‖` the π tail). -/
theorem EXB_node (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : InDomE c π L) (hs : SzB π) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0)
    (hS : ¬ StateHit L) (αk : ℕ → Digest)
    (hα : ∀ k < 14, fmAns (fsQLS stB20 π) zeroDL L (foldPosKS stB20 k) = some (αk k))
    (wd₀ wd₁ wd₂ : ℕ → ℕ → BF64)
    (hw₀ : ∀ q < 2 ^ 19, ∀ t < 64,
      wd₀ q t = (readRowG 19 1 (64 - stB20.occ0) stB20.occ0 L (capSB π 0) q).getD t 0)
    (hw₁ : ∀ q < 2 ^ 16, ∀ t < 48, wd₁ q t = (readRowG 16 0 0 48 L (capSB π 1) q).getD t 0)
    (hw₂ : ∀ q < 2 ^ 13, ∀ t < 48, wd₂ q t = (readRowG 13 0 0 48 L (capSB π 2) q).getD t 0)
    (α₀ α₁ α₂ : ℕ → BF64.Ext3) (ha₀ : ∀ j < 6, α₀ j = alphaE (αk j))
    (ha₁ : ∀ j < 4, α₁ j = alphaE (αk (6 + j))) (ha₂ : ∀ j < 4, α₂ j = alphaE (αk (10 + j)))
    (f₂ : ℕ → BF64.Ext3) (hf₂ : ∀ v < 2 ^ 9, f₂ v = resES stB20 π v)
    (m₂ : ℕ → BF64.Ext3) (hd₂ : decodeMP2 wd₂ α₂ f₂ = some m₂)
    (m₁ : ℕ → BF64.Ext3) (hd₁ : decodeMP1 wd₁ α₁ m₂ = some m₁)
    (out : List BF64) (hd₀ : decodeMP0L (loP stB20 π) wd₀ α₀ m₁ = some out) :
    EXB20 A c π L = some (XwitB π (wStreamS stB20 π out)) := by
  obtain ⟨hπ, hq, ht⟩ := hD
  have hp := progOK_stB20
  have hsz := szB_lt hs
  have hlo := szB_lo hs
  have hhi : π.size ≤ 285624 := by
    have := hs.2; rw [sizes_P20B.1.1, sizes_P20B.1.2.2.2.2.2.2] at this; exact this
  have hle : stB20.pz ≤ π.size := by rw [stB20_pz]; exact hlo
  have hcap0 := capSB_tape c π L hs (i := 0) (by decide)
  have hcap1 := capSB_tape c π L hs (i := 1) (by decide)
  have hcap2 := capSB_tape c π L hs (i := 2) (by decide)
  -- the stage's facts for the address bounds (`ProgOK`)
  rw [EXB20, if_pos ⟨hπ, hq, ht⟩, EdXB20, Eden]
  clear hπ
  obtain ⟨s1, hM1, z1, ho1, hden⟩ := den_SB c π L wf_decXB20 hs h0
  rw [hden]
  set I := (extractorInput c π L).toArray with hI
  have hLt : L.length ≤ (extractorInput c π L).length := by
    have h1 := length_logEntries L
    rw [tape_eq]
    simp only [List.length_append, logWords, List.length_cons]
    (clear * - L c π s1 h1; omega)
  simp only [memM, mpwX] at z1
  -- the flag
  obtain ⟨b1, -, hM2, z2, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
    (by decide) (by norm_num)
  rw [decXB20, semXIR_seq]
  generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 z2 bo
  have h6 : I.getD 6 0 ≠ 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pwB c π L hs (by norm_num)]; exact hb
  rw [semXIR_ite, if_neg (by rw [b1]; exact h6), nodeB20, okL2B_eq, read0B, read1B, read2B, semXIR_seq]
  -- from here on the stage is a variable (`obtain`, not `generalize`: the latter is beta-reduced away in the
  -- proof term, and the kernel then evaluates `nChainS stB20` & co., ~6.4 M hb)
  obtain ⟨st, hst⟩ : ∃ st, st = stB20 := ⟨_, rfl⟩
  rw [← hst] at hp hle hα hw₀ hf₂ hd₀ hcap0 hcap1 hcap2 ⊢
  have hocc := hp.occ0
  have hN := hp.nCh_lt
  have hf0 : foldPosS st 0 0 + 6 ≤ nChainS st := by
    have := hp.fold 5 (by decide); rw [foldPosKS_0 st (by decide)] at this; exact this
  have hf1 : foldPosS st 1 0 + 4 ≤ nChainS st := by
    have := hp.fold (6 + 3) (by decide); rw [foldPosKS_1 st (by decide)] at this; exact this
  have hf2 : foldPosS st 2 0 + 4 ≤ nChainS st := by
    have := hp.fold (10 + 3) (by decide); rw [foldPosKS_2 st (by decide)] at this; exact this
  -- the log position from tape word 4
  have hv : pLW I = BitVec.ofNat 64 (posL π.size) := pLW_eq (by rw [hI, getD_toArray, tape_getD4]) (by omega)
  have hpL : posL π.size ≤ 2 ^ 60 := by unfold posL; omega
  rw [(idxIR4D_sim hv memM).sem (wf_idxIR4 memM (posL π.size)) s2 hM2]
  -- 1. the index
  have hM3 := inv_sem I (wf_idxIR4 memM (posL π.size)) hM2
  have z3 := size_sem I (idxIR4 memM (posL π.size)) s2
  have o3 : (semXIR I (idxIR4 memM (posL π.size)) s2).o = s2.o := sem_o I _ s2 rfl
  rw [semXIR_seq]
  generalize hs3 : semXIR I (idxIR4 memM (posL π.size)) s2 = s3 at hM3 z3 o3
  have hsz3 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s3.M.size := by rw [z3, z2, z1]
  have hs2' : memM + L.length + L.length ≤ s2.M.size := by rw [layNum.1, z2, z1]; (clear * - L c π st s1 hLt s2 s3; omega)
  have hm3 : 2 ^ 26 ≤ s3.M.size := Nat.le_trans (Nat.le_add_right _ _) hsz3
  clear z1 z2 z3 hsz3 hLt
  -- 2. the chain
  have hwfC : WF (chainIR (posL π.size) (nChainS st) (chTabS st) sdL) :=
    wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide))
  obtain ⟨ch1, ch2⟩ := chainLS_specB st hp c π L hle hq ht hS s3 hM3 (Nat.le_trans (Nat.le_of_ble_eq_true rfl) hm3)
  have hM4 := inv_sem I hwfC hM3
  have z4 := size_sem I (chainIR (posL π.size) (nChainS st) (chTabS st) sdL) s3
  have o4 : (semXIR I (chainIR (posL π.size) (nChainS st) (chTabS st) sdL) s3).o = s3.o :=
    sem_o I _ s3 (hasOut_chainIRB _ _ _)
  rw [semXIR_seq, (chainIRD_sim hv (nChainS st) (chTabS st) sdL).sem hwfC s3 hM3]
  generalize semXIR I (chainIR (posL π.size) (nChainS st) (chTabS st) sdL) s3 = s4 at ch1 ch2 hM4 z4 o4
  have hm4 : 2 ^ 26 ≤ s4.M.size := by rw [z4]; exact hm3
  clear z4 hm3
  have hX4 : ∀ a < L.length, Lvm.X.rd s4.M (memM + a) =
      Lvm.X.rd (semXIR I (idxIR4 memM (posL π.size)) s2).M (memM + a) :=
    fun a ha => by rw [hs3, ch2 _ (le_add1 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add1 (Nat.le_of_ble_eq_true rfl)))]
  -- 3. level 0's word
  rw [(readGIRD_sim hv memM (capWS st 0) wB0M (2 ^ 19) 18 (64 - st.occ0) st.occ0).sem
    (wf_readGIR _ _ _ _ _ _ _ _) s4 hM4,
    show readGIR memM (posL π.size) (capWS st 0) wB0M (2 ^ 19) 18 (64 - st.occ0) st.occ0 =
      readGIR memM (posL π.size) (capWS st 0) wB0M (2 ^ 19) (19 - 1) (64 - st.occ0) st.occ0 from rfl]
  obtain ⟨r1, r2, r3, hM5⟩ := readGIR_sem (bX := memM) (pL := posL π.size) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) hpL c π L (hs_posL rfl)
    hq ht s2 hM2 hs2' s4 hM4 (by rw [layNum.1]; exact hm4) hX4 (ht' := 19) (lv := 1) (z := 64 - st.occ0)
    (occ := st.occ0) (capW := capWS st 0) (wB := wB0M) (cap := capSB π 0)
    (fun q hq => by rw [capSB_length, capBB, if_pos rfl]; norm_num; omega)
    (by rw [capSB_length, capBB, if_pos rfl]; have := hp.capW0; norm_num; omega)
    (by decide) (by decide) (Nat.lt_of_le_of_lt hocc (by decide)) hcap0
    (Nat.le_of_ble_eq_true rfl) (by rw [Nat.sub_add_cancel hocc]; exact Nat.le_of_ble_eq_true rfl)
  have z5 := size_sem I (readGIR memM (posL π.size) (capWS st 0) wB0M (2 ^ 19) (19 - 1) (64 - st.occ0) st.occ0) s4
  have o5 : (semXIR I (readGIR memM (posL π.size) (capWS st 0) wB0M (2 ^ 19) (19 - 1) (64 - st.occ0) st.occ0) s4).o =
    s4.o := sem_o I _ s4 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM (posL π.size) (capWS st 0) wB0M (2 ^ 19) (19 - 1) (64 - st.occ0) st.occ0) s4 = s5
    at r1 r2 r3 hM5 z5 o5
  rw [Nat.sub_add_cancel hocc] at r1 r2
  have hm5 : 2 ^ 26 ≤ s5.M.size := by rw [z5]; exact hm4
  clear z5 hm4
  have hX5 : ∀ a < L.length, Lvm.X.rd s5.M (memM + a) =
      Lvm.X.rd (semXIR I (idxIR4 memM (posL π.size)) s2).M (memM + a) :=
    fun a ha => by rw [r3 a ha, hX4 a ha]
  -- 4. level 1's word
  rw [(readGIRD_sim hv memM (capWS st 1) wB1M (2 ^ 16) 16 0 48).sem (wf_readGIR _ _ _ _ _ _ _ _) s5 hM5,
    show readGIR memM (posL π.size) (capWS st 1) wB1M (2 ^ 16) 16 0 48 =
      readGIR memM (posL π.size) (capWS st 1) wB1M (2 ^ 16) (16 - 0) 0 48 from rfl]
  obtain ⟨q1, q2, q3, hM6⟩ := readGIR_sem (bX := memM) (pL := posL π.size) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) hpL c π L (hs_posL rfl)
    hq ht s2 hM2 hs2' s5 hM5 (by rw [layNum.1]; exact hm5) hX5 (ht' := 16) (lv := 0) (z := 0) (occ := 48)
    (capW := capWS st 1) (wB := wB1M) (cap := capSB π 1)
    (fun q hq => by rw [capSB_length, capBB, if_neg (by decide)]; norm_num; omega)
    (by rw [capSB_length, capBB, if_neg (by decide)]; have := hp.capW1; norm_num; omega)
    (by decide) (by decide) (by decide) hcap1 (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl)
  have z6 := size_sem I (readGIR memM (posL π.size) (capWS st 1) wB1M (2 ^ 16) (16 - 0) 0 48) s5
  have o6 : (semXIR I (readGIR memM (posL π.size) (capWS st 1) wB1M (2 ^ 16) (16 - 0) 0 48) s5).o = s5.o :=
    sem_o I _ s5 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM (posL π.size) (capWS st 1) wB1M (2 ^ 16) (16 - 0) 0 48) s5 = s6 at q1 q2 q3 hM6 z6 o6
  have hm6 : 2 ^ 26 ≤ s6.M.size := by rw [z6]; exact hm5
  clear z6 hm5
  have hX6 : ∀ a < L.length, Lvm.X.rd s6.M (memM + a) =
      Lvm.X.rd (semXIR I (idxIR4 memM (posL π.size)) s2).M (memM + a) :=
    fun a ha => by rw [q3 a ha, hX5 a ha]
  -- 5. level 2's word
  rw [(readGIRD_sim hv memM (capWS st 2) wB2M (2 ^ 13) 13 0 48).sem (wf_readGIR _ _ _ _ _ _ _ _) s6 hM6,
    show readGIR memM (posL π.size) (capWS st 2) wB2M (2 ^ 13) 13 0 48 =
      readGIR memM (posL π.size) (capWS st 2) wB2M (2 ^ 13) (13 - 0) 0 48 from rfl]
  obtain ⟨p1, p2, -, hM7⟩ := readGIR_sem (bX := memM) (pL := posL π.size) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) hpL c π L (hs_posL rfl)
    hq ht s2 hM2 hs2' s6 hM6 (by rw [layNum.1]; exact hm6) hX6 (ht' := 13) (lv := 0) (z := 0) (occ := 48)
    (capW := capWS st 2) (wB := wB2M) (cap := capSB π 2)
    (fun q hq => by rw [capSB_length, capBB, if_neg (by decide)]; norm_num; omega)
    (by rw [capSB_length, capBB, if_neg (by decide)]; have := hp.capW2; norm_num; omega)
    (by decide) (by decide) (by decide) hcap2 (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl)
  have z7 := size_sem I (readGIR memM (posL π.size) (capWS st 2) wB2M (2 ^ 13) (13 - 0) 0 48) s6
  have o7 : (semXIR I (readGIR memM (posL π.size) (capWS st 2) wB2M (2 ^ 13) (13 - 0) 0 48) s6).o = s6.o :=
    sem_o I _ s6 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM (posL π.size) (capWS st 2) wB2M (2 ^ 13) (13 - 0) 0 48) s6 = s7 at p1 p2 hM7 z7 o7
  have hsz7 : 2 ^ 26 ≤ s7.M.size := by rw [z7]; exact hm6
  clear z7 hm6 hs2' hocc ht hq
  -- the chain answers, kept by the reads
  have hans : ∀ k < 14, ∀ m < 4, Lvm.X.rd s7.M (ansB + 4 * foldPosKS st k + m) = dw (αk k) m :=
    fun k hk m hm => by
      have hp' := hp.fold k hk
      rw [p2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
        q2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_ans hp' hN hm (Nat.le_of_ble_eq_true rfl))),
        r2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_ans hp' hN hm (Nat.le_of_ble_eq_true rfl))),
        ch1 _ hp' _ (hα k hk) m hm]
      rfl
  -- 6. the fold challenges
  rw [semXIR_seq, acpS, semXIR_seq, semXIR_seq, semXIR_seq]
  obtain ⟨a01, a02, hM8a, z8a, o8a⟩ := acp3IR_sem I s7 hM7 (Nat.le_trans (Nat.le_of_ble_eq_true rfl) hsz7)
    (src := ansB + 4 * foldPosS st 0 0) (dst := aB0M) (Nat.le_of_ble_eq_true rfl)
    (le_add1 (Nat.le_of_ble_eq_true rfl)) 6 (Nat.le_of_ble_eq_true rfl) (le_ans hf0 hN)
  generalize semXIR I (acp3IR (ansB + 4 * foldPosS st 0 0) aB0M 6) s7 = s8a at a01 a02 hM8a z8a o8a
  have hm8a : 2 ^ 26 ≤ s8a.M.size := by rw [z8a]; exact hsz7
  obtain ⟨a11, a12, hM8b, z8b, o8b⟩ := acp3IR_sem I s8a hM8a (Nat.le_trans (Nat.le_of_ble_eq_true rfl) hm8a)
    (src := ansB + 4 * foldPosS st 1 0) (dst := aB1M) (Nat.le_of_ble_eq_true rfl)
    (le_add1 (Nat.le_of_ble_eq_true rfl)) 4 (Nat.le_of_ble_eq_true rfl) (le_ans hf1 hN)
  generalize semXIR I (acp3IR (ansB + 4 * foldPosS st 1 0) aB1M 4) s8a = s8b at a11 a12 hM8b z8b o8b
  have hm8b : 2 ^ 26 ≤ s8b.M.size := by rw [z8b]; exact hm8a
  obtain ⟨a21, a22, hM8, z8, o8⟩ := acp3IR_sem I s8b hM8b (Nat.le_trans (Nat.le_of_ble_eq_true rfl) hm8b)
    (src := ansB + 4 * foldPosS st 2 0) (dst := aB2M) (Nat.le_of_ble_eq_true rfl)
    (le_add1 (Nat.le_of_ble_eq_true rfl)) 4 (Nat.le_of_ble_eq_true rfl) (le_ans hf2 hN)
  generalize semXIR I (acp3IR (ansB + 4 * foldPosS st 2 0) aB2M 4) s8b = s8 at a21 a22 hM8 z8 o8
  have hsz8 : 2 ^ 26 ≤ s8.M.size := by rw [z8]; exact hm8b
  clear z8 z8b z8a hsz7 hm8a hm8b
  -- 7. the residual
  obtain ⟨f1, f2, hM9, z9, o9⟩ := thcpIR_sem I s8 hM8 (a := resWS st) (dst := fB2M) (n := 3 * 2 ^ 9)
    hp.resW (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_trans (Nat.le_of_ble_eq_true rfl) hsz8)
  generalize semXIR I (thcpIR (resWS st) fB2M (3 * 2 ^ 9)) s8 = s9 at f1 f2 hM9 z9 o9
  have hsz9 : 2 ^ 26 ≤ s9.M.size := by rw [z9]; exact hsz8
  clear z9 hsz8 hN hf0 hf1 hf2
  -- the fold challenges in place
  have hA0 : ∀ i < 6, ∀ m < 3, Lvm.X.rd s8.M (aB0M + 3 * i + m) = dw (αk i) m := fun i hi m hm => by
    rw [a22 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))),
      a12 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))), a01 i hi m hm,
      show ansB + 4 * foldPosS st 0 0 + 4 * i + m = ansB + 4 * foldPosKS st i + m by
        rw [foldPosKS_0 st hi]; ring,
      hans i (Nat.lt_of_lt_of_le hi (by decide)) m (Nat.lt_of_lt_of_le hm (by decide))]
  have hA1 : ∀ i < 4, ∀ m < 3, Lvm.X.rd s8.M (aB1M + 3 * i + m) = dw (αk (6 + i)) m := fun i hi m hm => by
    rw [a22 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))),
      a11 i hi m hm, a02 _ (le_add3 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add3 (Nat.le_of_ble_eq_true rfl))),
      show ansB + 4 * foldPosS st 1 0 + 4 * i + m = ansB + 4 * foldPosKS st (6 + i) + m by
        rw [foldPosKS_1 st hi]; ring,
      hans (6 + i) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi 6) (by decide)) m
        (Nat.lt_of_lt_of_le hm (by decide))]
  have hA2 : ∀ i < 4, ∀ m < 3, Lvm.X.rd s8.M (aB2M + 3 * i + m) = dw (αk (10 + i)) m := fun i hi m hm => by
    rw [a21 i hi m hm, a12 _ (le_add3 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add3 (Nat.le_of_ble_eq_true rfl))),
      a02 _ (le_add3 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add3 (Nat.le_of_ble_eq_true rfl))),
      show ansB + 4 * foldPosS st 2 0 + 4 * i + m = ansB + 4 * foldPosKS st (10 + i) + m by
        rw [foldPosKS_2 st hi]; ring,
      hans (10 + i) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi 10) (by decide)) m
        (Nat.lt_of_lt_of_le hm (by decide))]
  -- the frame of steps 6, 7 (outside the fold challenges and the residual)
  have K79 : ∀ y, regs ≤ y → (y < aB0M ∨ aB2M + 12 ≤ y) → (y < fB2M ∨ fB2M + 3 * 2 ^ 9 ≤ y) →
      Lvm.X.rd s9.M y = Lvm.X.rd s7.M y := fun y hy h1 h2 => by
    simp only [layNum] at h1
    rw [f2 y hy h2, a22 y hy (by simp only [layNum]; (clear * - y st π s9 h1; omega)), a12 y hy (by simp only [layNum]; (clear * - y st π s9 h1; omega)),
      a02 y hy (by simp only [layNum]; (clear * - y st π s9 h1; omega))]
  -- 8. level 2's decoder
  have hW2 : ∀ q < 2 ^ 13, ∀ t < 48, rdK s9.M (wB2M + 48 * q + t) = wd₂ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K79 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl)))
      (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))), hw₂ q hq t ht']
    exact p1 q hq t ht'
  have hAl2 : ∀ i < 4, rdE s9.M (aB2M + 3 * i) = α₂ i := fun i hi => by
    rw [ha₂ i hi]
    exact rdE_alpha fun m hm => by
      rw [f2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))),
        hA2 i hi m hm]
  have hF2 : ∀ v < 2 ^ 9, rdE s9.M (fB2M + 3 * v) = f₂ v := fun v hv => by
    rw [hf₂ v hv, rdE_eq, resES]
    have hc : ∀ m < 3, Lvm.X.rd s9.M (fB2M + 3 * v + m) = pw π (resOffS st / 8 + 3 * v + m) := fun m hm => by
      rw [Nat.add_assoc, f1 _ (lt_aff0 hv hm (Nat.le_of_ble_eq_true rfl)), resWS, Nat.add_assoc 5,
        ← Nat.add_assoc (resOffS st / 8), tape_pwN c π L rfl (lt_of_lt_of_le (lt_affC hv hm hp.res) (Nat.div_le_div_right hle))]
    have c0 := hc 0 (by decide)
    rw [Nat.add_zero, Nat.add_zero] at c0
    rw [c0, hc 1 (by decide), hc 2 (by decide)]
  obtain ⟨e21, e22, e23, hM10⟩ := decMP2IR_sem I s9 hM9 (lay2M (by rw [layNum.1]; exact hsz9)) wd₂ α₂ f₂ hW2
    hAl2 hF2
  have z10 := size_sem I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9
  have o10 : (semXIR I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9).o = s9.o := sem_o I _ s9 rfl
  rw [decide_eq_true (dec_ok2 hd₂)] at e21
  have hm₂ := e22 m₂ hd₂
  generalize semXIR I (decMP2IR dB2M wB2M aB2M fB2M fB1M) s9 = s10 at e21 hm₂ e23 hM10 z10 o10
  -- 9. the flag, level 1's decoder
  obtain ⟨s11, hM11, z11, o11, k11, e11⟩ := flagIte_sem I s10 hM10 (a := ok1M dB2M) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) e21 (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) (okL1G st))
  rw [okL2G, e11, semXIR_seq]
  have hsz11 : 2 ^ 26 ≤ s11.M.size := by rw [z11, z10]; exact hsz9
  clear z10 z11 hsz9
  have K11 : ∀ y, regs ≤ y → (y < dB2M ∨ dB2M + ws1M 13 9 ≤ y) → (y < fB1M ∨ fB1M + 3 * 2 ^ 13 ≤ y) →
      Lvm.X.rd s11.M y = Lvm.X.rd s9.M y := fun y hy h1 h2 => by rw [k11 y hy, e23 y hy h1 h2]
  have hW1 : ∀ q < 2 ^ 16, ∀ t < 48, rdK s11.M (wB1M + 48 * q + t) = wd₁ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K11 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl)))
        (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
      K79 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl)))
        (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
      p2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))), hw₁ q hq t ht']
    exact q1 q hq t ht'
  have hAl1 : ∀ i < 4, rdE s11.M (aB1M + 3 * i) = α₁ i := fun i hi => by
    rw [ha₁ i hi]
    exact rdE_alpha fun m hm => by
      rw [K11 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl)))
          (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))),
        f2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))), hA1 i hi m hm]
  have hF1 : ∀ v < 2 ^ 13, rdE s11.M (fB1M + 3 * v) = m₂ v := fun v hv => by
    rw [← hm₂ v hv]
    exact rdE_congr fun m hm => k11 _ (le_add2 (Nat.le_of_ble_eq_true rfl))
  obtain ⟨e11', e12, e13, hM12⟩ := decMP1IR_sem I s11 hM11 (lay1M (by rw [layNum.1]; exact hsz11)) wd₁ α₁ m₂ hW1
    hAl1 hF1
  have z12 := size_sem I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11
  have o12 : (semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11).o = s11.o := sem_o I _ s11 rfl
  rw [decide_eq_true (dec_ok1 hd₁)] at e11'
  have hm₁ := e12 m₁ hd₁
  generalize semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11 = s12 at e11' hm₁ e13 hM12 z12 o12
  -- 10. the flag, level 0's decoder
  obtain ⟨s13, hM13, z13, o13, k13, e13'⟩ := flagIte_sem I s12 hM12 (a := ok1M dB1M) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) e11' (.seq (dec0S st) (okL0G st))
  rw [okL1G, e13', semXIR_seq]
  have hsz13 : 2 ^ 26 ≤ s13.M.size := by rw [z13, z12]; exact hsz11
  clear z12 z13 hsz11
  have K13 : ∀ y, regs ≤ y → (y < dB1M ∨ dB1M + ws1M 16 13 ≤ y) → (y < fB0M ∨ fB0M + 3 * 2 ^ 17 ≤ y) →
      Lvm.X.rd s13.M y = Lvm.X.rd s11.M y := fun y hy h1 h2 => by rw [k13 y hy, e13 y hy h1 h2]
  have hW0 : ∀ q < 2 ^ 19, ∀ t < 64, rdK s13.M (wB0M + 64 * q + t) = wd₀ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K13 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl)))
        (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
      K11 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl)))
        (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
      K79 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl)))
        (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
      p2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))),
      q2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add2 (Nat.le_of_ble_eq_true rfl))), hw₀ q hq t ht']
    exact r1 q hq t ht'
  have hAl0 : ∀ i < 6, rdE s13.M (aB0M + 3 * i) = α₀ i := fun i hi => by
    rw [ha₀ i hi]
    exact rdE_alpha fun m hm => by
      rw [K13 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl)))
          (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))),
        K11 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl)))
          (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))),
        f2 _ (le_add2 (Nat.le_of_ble_eq_true rfl)) (.inl (lt_aff hi hm (Nat.le_of_ble_eq_true rfl))), hA0 i hi m hm]
  have hF0 : ∀ v < 2 ^ 17, rdE s13.M (fB0M + 3 * v) = m₁ v := fun v hv => by
    rw [← hm₁ v hv]
    exact rdE_congr fun m hm => k13 _ (le_add2 (Nat.le_of_ble_eq_true rfl))
  obtain ⟨e01, e02, e03, hM14⟩ := dec0S_sem st c π L rfl (by omega) s13 hM13 (by rw [layNum.1]; exact hsz13) wd₀ α₀ m₁
    hW0 hAl0 hF0
  have z14 := size_sem I (dec0S st) s13
  have o14 : (semXIR I (dec0S st) s13).o = s13.o := sem_o I _ s13 (by
    unfold dec0S; split <;> rfl)
  rw [decide_eq_true (dec_ok0L hd₀)] at e01
  have hout := e02 out hd₀
  generalize semXIR I (dec0S st) s13 = s14 at e01 hout e03 hM14 z14 o14
  -- 11. the flag, the stream block, the node output
  obtain ⟨s15, hM15, z15, o15, k15, e15⟩ := flagIte_sem I s14 hM14 (a := okM dB0M) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) e01 (.seq (streamS st) (outIRB mBM))
  rw [okL0G, e15, semXIR_seq]
  have hsz15 : 2 ^ 26 ≤ s15.M.size := by rw [z15, z14]; exact hsz13
  clear z14 z15 hsz13
  obtain ⟨w1, -, hM16, z16, o16⟩ := streamS_sem st c π L rfl (by omega) s15 hM15 (by rw [layNum.1]; exact hsz15) out
    fun j hj => by
      rw [k15 _ (le_add1 (Nat.le_of_ble_eq_true rfl)), ← rdK_toBitVec, hout j hj]
  obtain ⟨ws, hws, hdec⟩ := outIRB_sem c π L hs _ hM16 (mB := mBM) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) (by rw [z16]; exact Nat.le_trans (Nat.le_of_ble_eq_true rfl) hsz15)
    (wStreamS st π out) w1
  rw [hws, o16, o15, o14, o13, o12, o11, o10, o9, o8, o8b, o8a, o7, o6, o5, o4, o3, bo, ho1, Array.toList_empty,
    List.nil_append]
  exact hdec

/-- **`EXB20` on an `S` node proof outside the domain**: the search (`EXS_node_out`'s twin). -/
theorem EXB_node_out (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : ¬ InDomE c π L) (hs : SzB π) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0) :
    EXB20 A c π L = search A (hdD π 2) c := by
  rw [EXB20, if_neg hD, EoutXB20, if_pos h0, if_pos hs, if_neg hb]

end Lvm.XB
