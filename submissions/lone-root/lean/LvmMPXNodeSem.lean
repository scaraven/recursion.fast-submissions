-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iii)): what M′'s extractor `EXM` returns on an `S` proof.
-- Adapted from `LvmXSpec.lean` (`den_S`, `EX_leaf`, `EX_node_out`, `okXIR_sem`, and the `C_rec` node theorem
-- `EX_node` removed in roll 11) at M′'s program `decXM` (`LvmMPXTop`): the chain through `C_main`'s folds
-- (`chainLM_spec`), the three column reads (`readGIR_sem`), the copies, the three decoders (`decMP2IR_sem`,
-- `decMP1IR_sem`, `decMP0IRW_sem`), the stream block and the node output (`outIR_sem`).
import LvmMPXComputes
import LvmMPXChain
import LvmMPXReadSem
import LvmMPXDec0Sem

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
    rw [rd_set_self (by simp only [eW]; omega), e1, toNat_toWord ha64]
  have l2 : ∀ i, i ≠ eW → rd (semXIR I (.load eW eA) s9).M i = rd s9.M i :=
    fun i hi => by rw [eL]; exact rd_set_ne (Ne.symm hi)
  have hM10 := inv_sem I (P := .load eW eA) (show 4 ≤ eW by decide) hM9
  have z10 := size_sem I (.load eW eA) s9
  have o10 : (semXIR I (.load eW eA) s9).o = s9.o := rfl
  rw [semXIR_seq]
  generalize semXIR I (.load eW eA) s9 = s10 at l1 l2 hM10 z10 o10
  have hflag : rd s10.M eW ≠ 0 := by rw [l1, g1 _ (by simp only [eA]; omega), hf]; decide
  rw [semXIR_ite, if_neg hflag]
  refine ⟨s10, hM10, by rw [z10, z9], by rw [o10, o9], fun y hy => ?_, rfl⟩
  simp only [regs] at hy
  rw [l2 _ (by simp only [eW]; omega), g1 _ (by simp only [eA]; omega)]

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
    rw [rd_set_self (by simp only [size_set, eW]; omega), rd_set_ne (by decide),
      rd_set_self (by simp only [eA]; omega), b1]
    rfl
  have k2 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M y = rd s.M y :=
    fun y hy => by
      simp only [regs] at hy
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by simp only [eW]; omega), rd_set_ne (by simp only [eA]; omega),
        b2 _ (by simp only [eW]; omega) (by simp only [rA]; omega)]
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
      (by simp only [mBM]; omega) (fun i hi => .inr (by rw [hwin]; simp only [mBM]; omega))
      (fun i hi => by rw [hwin]; simp only [regs]; omega)
    refine ⟨fun i hi => ?_, fun y hy h => ?_, m3⟩
    · rw [m1 i hi, k2 _ (by rw [hwin]; simp only [regs]; omega), hW _ (by omega), wStreamM, if_pos hsm]
    · rw [m2 y hy h, k2 y hy]
  · rw [if_neg hsm] at r2
    rw [if_pos r2]
    obtain ⟨m1, m2, m3⟩ := mcpIR_sem I s2 hM2 (n := 2 ^ 19) (src := winM + 2 ^ 19) (str := 1) (dst := mBM)
      (by norm_num) (by rw [hwin]; norm_num) (by norm_num) (by simp only [regs, mBM]; norm_num)
      (by simp only [mBM]; norm_num) (by simp only [mBM]; omega)
      (fun i hi => .inr (by rw [hwin]; simp only [mBM]; omega))
      (fun i hi => by rw [hwin]; simp only [regs]; omega)
    refine ⟨fun i hi => ?_, fun y hy h => ?_, m3⟩
    · rw [m1 i hi, k2 _ (by rw [hwin]; simp only [regs]; omega), Nat.one_mul, Nat.add_assoc,
        hW _ (by omega), wStreamM, if_neg hsm]
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

/-- Region arithmetic on M′'s layout: the addresses as numerals, then `omega`. -/
syntax "aom" : tactic
macro_rules
  | `(tactic| aom) => `(tactic| ((try simp only [memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v, mBM_v, ws2M_v, ws1M_v, ws0M_v, ok2M_v, ok1M_v, ok0M_v, chB_v, ansB_v, chEnd_v, sgB_v, nCp_v, regs_v, capWM0_v, capWM1_v, capWM2_v, resWM_v, fp0_v, fp1_v, fp2_v, winM_eq, ok1M, okM, mM, oM, encM, agM] at *) <;> omega))

theorem lay2M {sz : ℕ} (h : memM ≤ sz) : Dec1MLay 19 13 9 dB2M wB2M aB2M fB2M fB1M sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> aom

theorem lay1M {sz : ℕ} (h : memM ≤ sz) : Dec1MLay 19 16 13 dB1M wB1M aB1M fB1M fB0M sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> aom

theorem lay0M {sz : ℕ} (h : memM ≤ sz) : DecM0Lay 19 19 17 40 8 dB0M wB0M aB0M fB0M sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> aom

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
    interval_cases i <;> omega
  simp only [capM, List.getElem_map, List.getElem_range, hdD, packBytes_digW (length_wsAt _ _ _)]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [wsAt, List.getElem_map, List.getElem_range]
  rw [capWM_eq, show 5 + capOffM pX i / 8 + 4 * e + m = 5 + (capOffM pX i / 8 + 4 * e + m) by omega,
    tape_pw c π L hs (by omega)]

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
    omega
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
  obtain ⟨ch1, ch2⟩ := chainLM_spec c π L hs hq ht hS s3 hM3 (by rw [chEnd_v]; omega)
  have hM4 := inv_sem I (P := chainLM) (wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide))) hM3
  have z4 := size_sem I chainLM s3
  have o4 : (semXIR I chainLM s3).o = s3.o := sem_o I _ s3 hasOut_chainLM
  rw [semXIR_seq]
  generalize semXIR I chainLM s3 = s4 at ch1 ch2 hM4 z4 o4
  have hsz4 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s4.M.size := by rw [z4]; exact hsz3
  have hX4 : ∀ a < L.length, rd s4.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [hs3, ch2 _ (by aom) (.inr (by aom))]
  have hpL : pLX ≤ 2 ^ 60 := by rw [layoutX.1]; norm_num
  have hs2' : memM + L.length + L.length ≤ s2.M.size := by rw [z2, z1, memM_v]; omega
  -- 3. level 0's word
  rw [show read0M memM pLX (capWM 0) wB0M = readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47 from rfl]
  obtain ⟨r1, r2, r3, hM5⟩ := readGIR_sem (bX := memM) (pL := pLX) (by aom) (by aom) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s4 hM4 (by rw [memM_v]; omega) hX4 (ht' := 19) (lv := 8) (z := 17) (occ := 47)
    (capW := capWM 0) (wB := wB0M) (cap := capM π 0)
    (fun q hq => by rw [capM_length, capNM, if_pos rfl]; omega) (by rw [capM_length, capWM0_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by aom) (by aom)
  have z5 := size_sem I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4
  have o5 : (semXIR I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4).o = s4.o := sem_o I _ s4 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 0) wB0M (2 ^ 19) (19 - 8) 17 47) s4 = s5 at r1 r2 r3 hM5 z5 o5
  have hX5 : ∀ a < L.length, rd s5.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [r3 a ha, hX4 a ha]
  -- 4. level 1's word
  rw [show read1M memM pLX (capWM 1) wB1M = readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48 from rfl]
  obtain ⟨q1, q2, q3, hM6⟩ := readGIR_sem (bX := memM) (pL := pLX) (by aom) (by aom) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s5 hM5 (by rw [z5, memM_v]; omega) hX5 (ht' := 16) (lv := 7) (z := 0) (occ := 48)
    (capW := capWM 1) (wB := wB1M) (cap := capM π 1)
    (fun q hq => by rw [capM_length, capNM, if_neg (by norm_num)]; omega)
    (by rw [capM_length, capWM1_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by aom) (by aom)
  have z6 := size_sem I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5
  have o6 : (semXIR I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5).o = s5.o := sem_o I _ s5 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5 = s6 at q1 q2 q3 hM6 z6 o6
  have hX6 : ∀ a < L.length, rd s6.M (memM + a) = rd (semXIR I (idxIR4 memM pLX) s2).M (memM + a) :=
    fun a ha => by rw [q3 a ha, hX5 a ha]
  -- 5. level 2's word
  rw [show read2M memM pLX (capWM 2) wB2M = readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48 from rfl]
  obtain ⟨p1, p2, -, hM7⟩ := readGIR_sem (bX := memM) (pL := pLX) (by aom) (by aom) hpL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s6 hM6 (by rw [z6, z5, memM_v]; omega) hX6 (ht' := 13) (lv := 7) (z := 0) (occ := 48)
    (capW := capWM 2) (wB := wB2M) (cap := capM π 2)
    (fun q hq => by rw [capM_length, capNM, if_neg (by norm_num)]; omega)
    (by rw [capM_length, capWM2_v]; norm_num [capNM])
    (by norm_num) (by norm_num) (by norm_num) (capM_tape c π L hs (by norm_num)) (by aom) (by aom)
  have z7 := size_sem I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6
  have o7 : (semXIR I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6).o = s6.o := sem_o I _ s6 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM pLX (capWM 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6 = s7 at p1 p2 hM7 z7 o7
  have hsz7 : 2 ^ 26 ≤ s7.M.size := by rw [z7, z6, z5]; omega
  -- the chain answers, kept by the reads
  have hans : ∀ k < 14, ∀ m < 4, rd s7.M (ansB + 4 * foldPosK pX k + m) = dw (αk k) m := fun k hk m hm => by
    have hp := foldPosK_lt hk
    rw [nChainM_eq] at hp
    rw [p2 _ (by aom) (.inr (by aom)), q2 _ (by aom) (.inl (by aom)), r2 _ (by aom) (.inl (by aom)),
      ch1 _ (foldPosK_lt hk) _ (hα k hk) m hm]
    rfl
  -- 6. the fold challenges
  simp only [acpM, semXIR_seq]
  obtain ⟨a01, a02, hM8a, z8a, o8a⟩ := acp3IR_sem I s7 hM7 (by omega) (src := ansB + 4 * foldPosM pX 0 0)
    (dst := aB0M) (by aom) (by aom) 6 (by aom) (by aom)
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 0 0) aB0M 6) s7 = s8a at a01 a02 hM8a z8a o8a
  obtain ⟨a11, a12, hM8b, z8b, o8b⟩ := acp3IR_sem I s8a hM8a (by omega) (src := ansB + 4 * foldPosM pX 1 0)
    (dst := aB1M) (by aom) (by aom) 4 (by aom) (by aom)
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 1 0) aB1M 4) s8a = s8b at a11 a12 hM8b z8b o8b
  obtain ⟨a21, a22, hM8, z8, o8⟩ := acp3IR_sem I s8b hM8b (by omega) (src := ansB + 4 * foldPosM pX 2 0)
    (dst := aB2M) (by aom) (by aom) 4 (by aom) (by aom)
  generalize semXIR I (acp3IR (ansB + 4 * foldPosM pX 2 0) aB2M 4) s8b = s8 at a21 a22 hM8 z8 o8
  have hsz8 : 2 ^ 26 ≤ s8.M.size := by rw [z8, z8b, z8a]; exact hsz7
  -- 7. the residual
  obtain ⟨f1, f2, hM9, z9, o9⟩ := thcpIR_sem I s8 hM8 (a := resWM) (dst := fB2M) (n := 3 * 2 ^ 9)
    (by aom) (by aom) (by aom) (by aom)
  generalize semXIR I (thcpIR resWM fB2M (3 * 2 ^ 9)) s8 = s9 at f1 f2 hM9 z9 o9
  have hsz9 : memM ≤ s9.M.size := by rw [z9, memM_v]; omega
  -- the fold challenges in place
  have hA0 : ∀ i < 6, ∀ m < 3, rd s8.M (aB0M + 3 * i + m) = dw (αk i) m := fun i hi m hm => by
    rw [a22 _ (by aom) (.inl (by aom)), a12 _ (by aom) (.inl (by aom)), a01 i hi m hm,
      show ansB + 4 * foldPosM pX 0 0 + 4 * i + m = ansB + 4 * foldPosK pX i + m by rw [foldPosK_0 hi]; ring,
      hans i (by omega) m (by omega)]
  have hA1 : ∀ i < 4, ∀ m < 3, rd s8.M (aB1M + 3 * i + m) = dw (αk (6 + i)) m := fun i hi m hm => by
    rw [a22 _ (by aom) (.inl (by aom)), a11 i hi m hm, a02 _ (by aom) (.inr (by aom)),
      show ansB + 4 * foldPosM pX 1 0 + 4 * i + m = ansB + 4 * foldPosK pX (6 + i) + m by rw [foldPosK_1 hi]; ring,
      hans (6 + i) (by omega) m (by omega)]
  have hA2 : ∀ i < 4, ∀ m < 3, rd s8.M (aB2M + 3 * i + m) = dw (αk (10 + i)) m := fun i hi m hm => by
    rw [a21 i hi m hm, a12 _ (by aom) (.inr (by aom)), a02 _ (by aom) (.inr (by aom)),
      show ansB + 4 * foldPosM pX 2 0 + 4 * i + m = ansB + 4 * foldPosK pX (10 + i) + m by rw [foldPosK_2 hi]; ring,
      hans (10 + i) (by omega) m (by omega)]
  -- the frame of steps 6, 7 (outside the fold challenges and the residual)
  have K79 : ∀ y, regs ≤ y → (y < aB0M ∨ aB2M + 12 ≤ y) → (y < fB2M ∨ fB2M + 3 * 2 ^ 9 ≤ y) →
      rd s9.M y = rd s7.M y := fun y hy h1 h2 => by
    rw [f2 y hy h2, a22 y hy (by aom), a12 y hy (by aom), a02 y hy (by aom)]
  -- 8. level 2's decoder
  have hW2 : ∀ q < 2 ^ 13, ∀ t < 48, rdK s9.M (wB2M + 48 * q + t) = wd₂ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K79 _ (by aom) (.inr (by aom)) (.inr (by aom)), hw₂ q hq t ht']
    exact (show 0 + 48 = 48 from rfl) ▸ p1 q hq t (by omega)
  have hAl2 : ∀ i < 4, rdE s9.M (aB2M + 3 * i) = α₂ i := fun i hi => by
    rw [ha₂ i hi]
    exact rdE_alpha fun m hm => by rw [f2 _ (by aom) (.inl (by aom)), hA2 i hi m hm]
  have hF2 : ∀ v < 2 ^ 9, rdE s9.M (fB2M + 3 * v) = f₂ v := fun v hv => by
    rw [hf₂ v hv, rdE_eq, resEM]
    have hc : ∀ m < 3, rd s9.M (fB2M + 3 * v + m) = pw π (resOffM pX / 8 + 3 * v + m) := fun m hm => by
      have hr : resOffM pX / 8 = 35773 := by rw [layoutM_P20.2.2.2.2.2.2.2.2.1]
      rw [Nat.add_assoc, f1 _ (by omega), resWM_v, show 35778 + (3 * v + m) = 5 + (resOffM pX / 8 + 3 * v + m) by
        omega, tape_pw c π L hs (by omega)]
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
  obtain ⟨s11, hM11, z11, o11, k11, e11⟩ := flagIte_sem I s10 hM10 (a := ok1M dB2M) (by aom) (by aom) e21
    (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) okL1)
  rw [okL2, e11, semXIR_seq]
  have hsz11 : memM ≤ s11.M.size := by rw [z11, z10]; exact hsz9
  have K11 : ∀ y, regs ≤ y → (y < dB2M ∨ dB2M + ws1M 13 9 ≤ y) → (y < fB1M ∨ fB1M + 3 * 2 ^ 13 ≤ y) →
      rd s11.M y = rd s9.M y := fun y hy h1 h2 => by rw [k11 y hy, e23 y hy h1 h2]
  have hW1 : ∀ q < 2 ^ 16, ∀ t < 48, rdK s11.M (wB1M + 48 * q + t) = wd₁ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K11 _ (by aom) (.inr (by aom)) (.inr (by aom)), K79 _ (by aom) (.inr (by aom)) (.inr (by aom)),
      p2 _ (by aom) (.inr (by aom)), hw₁ q hq t ht']
    exact (show 0 + 48 = 48 from rfl) ▸ q1 q hq t (by omega)
  have hAl1 : ∀ i < 4, rdE s11.M (aB1M + 3 * i) = α₁ i := fun i hi => by
    rw [ha₁ i hi]
    exact rdE_alpha fun m hm => by
      rw [K11 _ (by aom) (.inl (by aom)) (.inl (by aom)), f2 _ (by aom) (.inl (by aom)), hA1 i hi m hm]
  have hF1 : ∀ v < 2 ^ 13, rdE s11.M (fB1M + 3 * v) = m₂ v := fun v hv => by
    rw [← hm₂ v hv]
    exact rdE_congr fun m hm => k11 _ (by aom)
  obtain ⟨e11', e12, e13, hM12⟩ := decMP1IR_sem I s11 hM11 (lay1M hsz11) wd₁ α₁ m₂ hW1 hAl1 hF1
  have z12 := size_sem I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11
  have o12 : (semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11).o = s11.o := sem_o I _ s11 rfl
  rw [decide_eq_true (dec_ok1 hd₁)] at e11'
  have hm₁ := e12 m₁ hd₁
  generalize semXIR I (decMP1IR dB1M wB1M aB1M fB1M fB0M) s11 = s12 at e11' hm₁ e13 hM12 z12 o12
  -- 10. the flag, level 0's decoder
  obtain ⟨s13, hM13, z13, o13, k13, e13'⟩ := flagIte_sem I s12 hM12 (a := ok1M dB1M) (by aom) (by aom) e11'
    (.seq (decMP0IRW dB0M wB0M aB0M fB0M) okL0)
  rw [okL1, e13', semXIR_seq]
  have hsz13 : memM ≤ s13.M.size := by rw [z13, z12, z11, z10]; exact hsz9
  have K13 : ∀ y, regs ≤ y → (y < dB1M ∨ dB1M + ws1M 16 13 ≤ y) → (y < fB0M ∨ fB0M + 3 * 2 ^ 17 ≤ y) →
      rd s13.M y = rd s11.M y := fun y hy h1 h2 => by rw [k13 y hy, e13 y hy h1 h2]
  have hW0 : ∀ q < 2 ^ 19, ∀ t < 64, rdK s13.M (wB0M + 64 * q + t) = wd₀ q t := fun q hq t ht' => by
    simp only [rdK]
    rw [K13 _ (by aom) (.inr (by aom)) (.inr (by aom)), K11 _ (by aom) (.inr (by aom)) (.inr (by aom)),
      K79 _ (by aom) (.inr (by aom)) (.inr (by aom)), p2 _ (by aom) (.inr (by aom)),
      q2 _ (by aom) (.inr (by aom)), hw₀ q hq t ht']
    exact (show 17 + 47 = 64 from rfl) ▸ r1 q hq t (by omega)
  have hAl0 : ∀ i < 6, rdE s13.M (aB0M + 3 * i) = α₀ i := fun i hi => by
    rw [ha₀ i hi]
    exact rdE_alpha fun m hm => by
      rw [K13 _ (by aom) (.inl (by aom)) (.inl (by aom)), K11 _ (by aom) (.inl (by aom)) (.inl (by aom)),
        f2 _ (by aom) (.inl (by aom)), hA0 i hi m hm]
  have hF0 : ∀ v < 2 ^ 17, rdE s13.M (fB0M + 3 * v) = m₁ v := fun v hv => by
    rw [← hm₁ v hv]
    exact rdE_congr fun m hm => k13 _ (by aom)
  obtain ⟨e01, e02, e03, hM14⟩ := decMP0IRW_sem I s13 hM13 (lay0M hsz13) wd₀ α₀ m₁ hW0 hAl0 hF0
  have z14 := size_sem I (decMP0IRW dB0M wB0M aB0M fB0M) s13
  have o14 : (semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13).o = s13.o := sem_o I _ s13 rfl
  rw [decide_eq_true (dec_ok0 hd₀)] at e01
  have hout := e02 out hd₀
  generalize semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13 = s14 at e01 hout e03 hM14 z14 o14
  -- 11. the flag, the stream block, the node output
  obtain ⟨s15, hM15, z15, o15, k15, e15⟩ := flagIte_sem I s14 hM14 (a := okM dB0M) (by aom) (by aom) e01
    (.seq streamM (outIR mBM))
  rw [okL0, e15, semXIR_seq]
  have hsz15 : memM ≤ s15.M.size := by rw [z15, z14]; exact hsz13
  obtain ⟨st1, -, hM16, z16, o16⟩ := streamM_sem c π L hs s15 hM15 hsz15 out fun j hj => by
    rw [k15 _ (by aom), ← rdK_toBitVec, hout j (by omega)]
  rw [outIR_sem c π L hs _ hM16 (mB := mBM) (by aom) (by aom) (by rw [z16]; aom) (wStreamM π out) st1, o16, o15,
    o14, o13, o12, o11, o10, o9, o8, o8b, o8a, o7, o6, o5, o4, o3, bo, ho1, Array.toList_empty, List.nil_append]
  exact decodeWit_outWords π _

end Lvm.X
