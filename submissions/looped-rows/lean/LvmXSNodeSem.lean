-- New for lvm2 E2F (E2F-L, 2026-11-13): what `EXS st` returns (owner: E2F-L's helper H2). Port of `LvmMPXNodeSem`
-- (and the chain's facts, `LvmXChainL`/`LvmMPXChain`) with the stage's offsets. The statements are frozen
-- (`-- E2F-L frozen`), consumed by `LvmXSExtEq`; the proofs use `LvmXSOut`'s output facts.
-- Side conditions (kernel budget): the node's address bounds are closed by `Nat.le_of_ble_eq_true rfl` on closed
-- terms and the small lemmas `le_add1/2/3`, `lt_aff`, `lt_affC`, `lt_ans`, `le_ans` (each `omega` in a tactic block
-- costs ≈ 20 ms of kernel as an auxiliary lemma); the stage's numeric facts come from `ProgOK`.
import LvmXSComputes
import LvmMPXNodeSem

/-!
# What `EXS st` returns

* `fsQLS st π p a` (the chain's query at position `p`), `capS st π i` (`C_main`'s level-`i` cap from π),
  `resES st π v` (the residual's coefficient `v` from π);
* **`EXS_leaf`** (`b = 0`), **`EXS_node_out`** (`b ≠ 0`, outside the domain), **`EXS_node`** (`b ≠ 0`, in the domain:
  the chain's fold challenges, the decoders' success on π's caps' readings and π's residual give `XwitS`).
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-- **The query at chain position `p`** at a stage (`fsQL`), the previous answer being `a`. -/
def fsQLS (st : XStage) (π : Proof) (p : ℕ) (a : Digest) : ByteArray :=
  if p = 0 then q0Query else digestBytes a ++ π.extract (msgLS st p).1 ((msgLS st p).1 + (msgLS st p).2)

/-- **`C_main`'s level-`i` cap from π** at a stage (`capM`). -/
def capS (st : XStage) (π : Proof) (i : ℕ) : List Digest :=
  (List.range (capNM i)).map fun e => hdD π (capOffS st i / 8 + 4 * e)

/-- **The residual's coefficient `v`** from π at a stage (`resEM`). -/
def resES (st : XStage) (π : Proof) (v : ℕ) : BF64.Ext3 :=
  mkE (wK (pw π (resOffS st / 8 + 3 * v))) (wK (pw π (resOffS st / 8 + 3 * v + 1)))
    (wK (pw π (resOffS st / 8 + 3 * v + 2)))

/-! ## The chain's messages and table at a stage -/

theorem msgLS_ok (st : XStage) (hp : ProgOK st) {p : ℕ} (hp0 : 0 < p) (hpN : p ≤ nChainS st) :
    (msgLS st p).1 % 8 = 0 ∧ (msgLS st p).2 % 8 = 0 ∧ (msgLS st p).1 + (msgLS st p).2 ≤ st.pz ∧
      32 + (msgLS st p).2 ≤ queryCap := by
  have hl := hp.nCh_le
  have hm : (fsMsgsS st)[p - 1]'(by omega) ∈ (fsMsgsS st).take (nChainS st) :=
    List.mem_iff_getElem.mpr ⟨p - 1, by simp; omega, by simp⟩
  have h := List.all_eq_true.mp hp.msgs _ hm
  rw [msgLS, List.getD_eq_getElem _ _ (by omega)]
  simp only [msgOkS, msgOkP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem msgLS_cap (st : XStage) (hp : ProgOK st) (p : ℕ) : 32 + (msgLS st p).2 ≤ queryCap := by
  rw [msgLS]
  by_cases h : p - 1 < (fsMsgsS st).length
  · rw [List.getD_eq_getElem _ _ h]
    exact of_decide_eq_true (List.all_eq_true.mp hp.qcap _ (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]; decide

theorem fsQLS_data (st : XStage) {π : Proof} (p : ℕ) (hp0 : 0 < p) (d : Digest) :
    (fsQLS st π p d).data.toList =
      d.toList ++ (π.extract (msgLS st p).1 ((msgLS st p).1 + (msgLS st p).2)).data.toList := by
  rw [fsQLS, if_neg (by omega), ByteArray.data_append, Array.toList_append]
  rfl

/-- Every query after `q₀` carries its state. -/
theorem stateIn_fsQLS (st : XStage) (hp : ProgOK st) (π : Proof) {p : ℕ} (hp0 : 0 < p) (d : Digest) :
    stateIn (fsQLS st π p d) = some d := by
  have hc := msgLS_cap st hp p
  have hd := fsQLS_data st (π := π) p hp0 d
  have hz : (fsQLS st π p d).size = 32 + (π.extract (msgLS st p).1 ((msgLS st p).1 + (msgLS st p).2)).size := by
    rw [fsQLS, if_neg (by omega), ByteArray.size_append, digestBytes_size]
  generalize msgLS st p = m at hc hd hz
  have he : (π.extract m.1 (m.1 + m.2)).size ≤ m.2 := by
    rw [ByteArray.size_extract]; omega
  generalize fsQLS st π p d = q at hd hz ⊢
  generalize π.extract m.1 (m.1 + m.2) = x at hd hz he
  have hl : q.data.toList.length = q.size := Array.length_toList
  rw [stateIn, if_pos ⟨by omega, by omega⟩]
  refine congrArg some (Vector.ext fun i hi => ?_)
  rw [Vector.getElem_ofFn, List.getD_eq_getElem _ _ (by omega), List.getElem_of_eq hd,
    List.getElem_append_left (by simp; omega), Vector.getElem_toList]

theorem chTabS_getD (st : XStage) {p k : ℕ} (hp : p ≤ nChainS st) (hk : k < 4) :
    (chTabS st).getD (4 * p + k) 0 = (tabEntS st p).getD k 0 :=
  getD_flatMap4 (tabEntS st) (tabEntS_length st) _ p k (by omega) hk

/-- **The table realises `V_S`'s chain** at a stage. -/
theorem tabW_chTabS (st : XStage) (hp : ProgOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz) :
    TabW (extractorInput c π L).toArray (fsQLS st π) (nChainS st) (chTabS st) := by
  have hpz := hp.pz_lt
  refine ⟨chTabS_length st, fun p hp0 hpN => ⟨?_, fun hpN' d => ?_⟩⟩
  · rw [chTabS_getD st hpN (by norm_num), tabEntS, if_neg (by omega)]
    show (toWord (5 + (msgLS st p).1 / 8)).toNat < 2 ^ 62
    have : (msgLS st p).1 ≤ st.pz := by have := (msgLS_ok st hp hp0 hpN).2.2.1; omega
    generalize msgLS st p = m at this
    rw [toNat_toWord (by omega)]; omega
  · obtain ⟨ho, hl, hol, hq⟩ := msgLS_ok st hp hp0 (by omega)
    have e0 := chTabS_getD st hpN (k := 0) (by norm_num)
    have e1 := chTabS_getD st hpN (k := 1) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, tabEntS, if_neg (by omega)]
    have hz : (fsQLS st π p d).size = 32 + (msgLS st p).2 := by
      rw [fsQLS, if_neg (by omega), ByteArray.size_append, extract_size π (by omega), digestBytes_size]
    refine ⟨by rw [hz]; rfl, by rw [hz]; omega, fun j hj => ?_⟩
    rw [hz] at hj
    rw [fsQLS_data st p hp0, packBytes_appendK _ _ (k := 4) (by simp)]
    show _ = if j < 4 then _ else (extractorInput c π L).toArray.getD
      ((toWord (5 + (msgLS st p).1 / 8)).toNat + (j - 4)) 0
    split_ifs with h4
    · rfl
    · generalize msgLS st p = m at ho hl hol hj ⊢
      obtain ⟨a, ha⟩ : ∃ a, m.1 = 8 * a := ⟨m.1 / 8, by omega⟩
      obtain ⟨n, hn⟩ : ∃ n, m.2 = 8 * n := ⟨m.2 / 8, by omega⟩
      rw [ha, hn] at hol ⊢
      rw [hn] at hj
      rw [toNat_toWord (by omega), getD_toArray,
        show 5 + 8 * a / 8 + (j - 4) = 5 + (a + (j - 4)) by omega,
        tape_getD_proof c π L (by rw [hs]; omega), ← List.getD_eq_getElem _ 0,
        extract_words π (by rw [hs]; omega) (by omega)]

/-- **`chainLS_spec`**: the machine's chain answers at a stage are the first-match chain's. -/
theorem chainLS_spec (st : XStage) (hp : ProgOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < nChainS st, ∀ a, fmAns (fsQLS st π) zeroDL L p = some a → ∀ m < 4,
      Lvm.X.rd (semXIR (extractorInput c π L).toArray (chainLS st) s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      Lvm.X.rd (semXIR (extractorInput c π L).toArray (chainLS st) s).M y = Lvm.X.rd s.M y) := by
  have hT : ∀ p d, 0 < p → stateIn (fsQLS st π p d) = some d := fun p d hp0 => stateIn_fsQLS st hp π hp0 d
  obtain ⟨-, hans, hheap⟩ := chainIR_sem (pL := pLS st) c π L (hs_posL hs) hq ht (N := nChainS st)
    hp.nCh_lt (tabW_chTabS st hp c π L hs) (seedOK_sdL _) (st₀ := zeroDL)
    (by simp [fsQLS, q0Query, ByteArray.size, q0Bytes]) s hM hsz
  refine ⟨fun p hpN a ha m hm => ?_, hheap⟩
  have hsc := scanC_answers (N := nChainS st) (st₀ := zeroDL) hT hS hpN
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nChainS st) (st₀ := zeroDL) (L := L) (T := fsQLS st π) hT hS).1
  have hpl : p < (scanC (fsQLS st π) (nChainS st) zeroDL L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQLS st π) (nChainS st) zeroDL L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [chainLS, hans p hpl m hm, hg]

/-! ## The tape, the parse, the leaf -/

/-- π's packed words on the tape of a proof of `pz` bytes. -/
theorem tape_pwN (c : Digest) (π : Proof) (L : Log) {pz : ℕ} (hs : π.size = pz) {j : ℕ}
    (hj : j < pz / 8) : (extractorInput c π L).toArray.getD (5 + j) 0 = pw π j := by
  rw [getD_toArray, tape_getD_proof c π L (by rw [hs]; omega), pw, List.getD_eq_getElem]

theorem wsAt_tapeN (c : Digest) (π : Proof) (L : Log) {pz : ℕ} (hs : π.size = pz) {a n : ℕ}
    (h : a + n ≤ pz / 8) :
    (List.range n).map (fun j => (extractorInput c π L).toArray.getD (5 + a + j) 0) = wsAt (pw π) a n :=
  List.map_congr_left fun j hj => by
    rw [Nat.add_assoc, tape_pwN c π L hs (by simp at hj; omega)]

theorem den_SS (c : Digest) (π : Proof) (L : Log) {pz : ℕ} {dec : XIR} (hwf : WF dec) (hs : π.size = pz)
    (h0 : π.data[0]? = some 0x53) :
    ∃ s1 : St, Inv s1.M ∧ s1.M.size = memM + mpwX * (extractorInput c π L).length ∧ s1.o = #[] ∧
      den memM mpwX (extIRWith pz dec) (extractorInput c π L) =
        (semXIR (extractorInput c π L).toArray dec s1).o.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0' : Inv (initSt (memM + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  refine ⟨semXIR I (parseIR pz) (initSt (memM + mpwX * (extractorInput c π L).length)),
    inv_sem I (wf_extIRWith (pz := pz) hwf).1 h0', by rw [size_sem, initSt_M, size_runPrims,
      Array.size_replicate], by rw [parse_o, initSt_o], ?_⟩
  have hk : Lvm.X.rd (semXIR I (parseIR pz) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsK ≠ 0 := by
    rw [parse_isK _ I _ h0']
    have hb := tape_byte0 c π L h0
    have e : I.getD 5 0 &&& 0xFF = kindS := by
      apply BitVec.eq_of_toNat_eq
      rw [lowByte, hI, getD_toArray, hb]; rfl
    rw [if_pos e]; decide
  have hz : Lvm.X.rd (semXIR I (parseIR pz) (initSt (memM + mpwX * (extractorInput c π L).length))).M
      rIsSz ≠ 0 := by
    rw [parse_regs _ I _ h0', hI, getD_toArray, tape_getD4, hs]
    rw [if_pos (by rfl)]; decide
  rw [den, extIRWith, semXIR_seq, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]

theorem EXS_leaf (st : XStage) (hp : ProgOK st) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof)
    (L : Log) (hs : π.size = st.pz) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 = 0) :
    EXS st A c π L = some (leafW π) := by
  have hc0 := hp.cap0
  by_cases hD : InDomE c π L
  · rw [EXS, if_pos hD, EdXS, Eden]
    obtain ⟨s1, hM1, -, ho1, hden⟩ := den_SS c π L (wf_decXS st hp.out) hs h0
    rw [hden]
    set I := (extractorInput c π L).toArray with hI
    obtain ⟨b1, -, hM2, -, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
      (by decide) (by norm_num)
    rw [decXS, semXIR_seq]
    generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 bo
    have h6 : I.getD 6 0 = 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pwN c π L hs (by omega), hb]
    rw [semXIR_ite, if_pos (by rw [b1, h6]), leafIR, semXIR_seq]
    obtain ⟨e1, -⟩ := emitIR_sem I s2 hM2 (toWord 0)
    have hM3 := inv_sem I (wf_emitIR (toWord 0)) hM2
    generalize semXIR I (emitIR (toWord 0)) s2 = s3 at e1 hM3
    obtain ⟨t1, -⟩ := tcpIR_sem I s3 hM3 (a := 15) (n := 5) (by norm_num)
    rw [t1, e1, bo, ho1]
    have t2 := wsAt_tapeN c π L hs (a := 10) (n := 5) (by omega)
    simp only [show (5 + 10 : ℕ) = 15 from rfl] at t2
    rw [t2]
    have hw : witWords (leafW π) = toWord 0 :: wsAt (pw π) 10 5 := by
      simp only [leafW, witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat',
        show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
      simp [wsAt]
    rw [Array.toList_empty, List.nil_append, List.singleton_append, ← hw]
    exact decodeWit_witWords _ (pw π 14).isLt
  · rw [EXS, if_neg hD, EoutXS, if_pos h0, if_pos hs, if_pos hb]

/-! ## The stream block at a stage -/

theorem streamS_sem (c : Digest) (π : Proof) (L : Log) {pz : ℕ} (hs : π.size = pz) (h15 : 15 ≤ pz / 8)
    (s : St) (hM : Inv s.M) (hsz : memM ≤ s.M.size) (out : List BF64)
    (hW : ∀ j < 2 ^ 20, Lvm.X.rd s.M (winM + j) = BF64.toBitVec (out.getD j 0)) :
    (∀ i < 2 ^ 19, Lvm.X.rd (semXIR (extractorInput c π L).toArray streamM s).M (mBM + i) = wStreamM π out i) ∧
    (∀ y, regs ≤ y → (y < mBM ∨ mBM + 2 ^ 19 ≤ y) →
      Lvm.X.rd (semXIR (extractorInput c π L).toArray streamM s).M y = Lvm.X.rd s.M y) ∧
    Inv (semXIR (extractorInput c π L).toArray streamM s).M ∧
    (semXIR (extractorInput c π L).toArray streamM s).M.size = s.M.size ∧
    (semXIR (extractorInput c π L).toArray streamM s).o = s.o := by
  set I := (extractorInput c π L).toArray with hI
  have hs0 := hM.1
  simp only [regs] at hs0
  have hwin := winM_eq
  simp only [memM] at hsz
  suffices H : (∀ i < 2 ^ 19, Lvm.X.rd (semXIR I streamM s).M (mBM + i) = wStreamM π out i) ∧
      (∀ y, regs ≤ y → (y < mBM ∨ mBM + 2 ^ 19 ≤ y) → Lvm.X.rd (semXIR I streamM s).M y = Lvm.X.rd s.M y) ∧
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
  have r2 : Lvm.X.rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M eW =
      if I.getD 19 0 < toWord (2 ^ 18 + 1) then 1 else 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, eW]; omega), rd_set_ne (by decide),
      rd_set_self (by simp only [eA]; omega), b1]
    rfl
  have k2 : ∀ y, regs ≤ y →
      Lvm.X.rd (semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1).M y = Lvm.X.rd s.M y :=
    fun y hy => by
      simp only [regs] at hy
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by simp only [eW]; omega), rd_set_ne (by simp only [eA]; omega),
        b2 _ (by simp only [eW]; omega) (by simp only [rA]; omega)]
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const eA (toWord (2 ^ 18 + 1)), .op .ltu eW eW eA]) s1 = s2 at hM2 z2 r2 k2
  have hn : I.getD 19 0 = pw π 14 := by rw [show (19 : ℕ) = 5 + 14 from rfl, tape_pwN c π L hs (by omega)]
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

/-! ## The caps, the fold positions, the chain's output -/

theorem capS_length (st : XStage) (π : Proof) (i : ℕ) : (capS st π i).length = capNM i := by simp [capS]

/-- **π's level-`i` cap on the tape** at a stage (`i < 3`). -/
theorem capS_tape (st : XStage) (hp : ProgOK st) (c : Digest) (π : Proof) (L : Log) (hs : π.size = st.pz)
    {i : ℕ} (hi : i < 3) :
    ∀ e (he : e < (capS st π i).length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capWS st i + 4 * e + m) 0 =
        (packBytes (capS st π i)[e].toList).getD m 0 := by
  intro e he m hm
  have hco : capOffS st i / 8 + 4 * capNM i ≤ st.pz / 8 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.cap0
    · exact hp.cap1
    · exact hp.cap2
  have he' : e < capNM i := by rwa [capS_length] at he
  simp only [capS, List.getElem_map, List.getElem_range, hdD, packBytes_digW (length_wsAt _ _ _)]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp only [wsAt, List.getElem_map, List.getElem_range]
  rw [show capWS st i + 4 * e + m = 5 + (capOffS st i / 8 + 4 * e + m) by rw [capWS]; omega,
    tape_pwN c π L hs (by omega)]

theorem foldPosS_add (st : XStage) (i j : ℕ) : foldPosS st i j = foldPosS st i 0 + j := by
  unfold foldPosS; omega

theorem foldPosKS_0 (st : XStage) {j : ℕ} (hj : j < 6) : foldPosKS st j = foldPosS st 0 0 + j := by
  rw [foldPosKS, if_pos hj, foldPosS_add]
theorem foldPosKS_1 (st : XStage) {j : ℕ} (hj : j < 4) : foldPosKS st (6 + j) = foldPosS st 1 0 + j := by
  rw [foldPosKS, if_neg (by omega), if_pos (by omega), foldPosS_add, Nat.add_sub_cancel_left]
theorem foldPosKS_2 (st : XStage) {j : ℕ} (hj : j < 4) : foldPosKS st (10 + j) = foldPosS st 2 0 + j := by
  rw [foldPosKS, if_neg (by omega), if_neg (by omega), foldPosS_add, Nat.add_sub_cancel_left]

theorem hasOut_chainLS (st : XStage) : hasOut (chainLS st) = false := by
  simp only [chainLS, chainIR, hasOut_seq, hasOut_storesIR, cntIR, cntBody, readAt, sdL, startPs, wordIR,
    lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, st4IR, stNext, nextIR, nextPre]
  simp only [hasOut, Bool.or_false]

theorem EXS_node_out (st : XStage) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : ¬ InDomE c π L) (hs : π.size = st.pz) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0) :
    EXS st A c π L = search A (hdD π 2) c := by
  rw [EXS, if_neg hD, EoutXS, if_pos h0, if_pos hs, if_neg hb]

/-! ## Cheap side conditions (kernel-light closers for the node's address bounds) -/

theorem le_add1 {L C x : ℕ} (h : L ≤ C) : L ≤ C + x := Nat.le_trans h (Nat.le_add_right C x)

theorem le_add2 {L C x y : ℕ} (h : L ≤ C) : L ≤ C + x + y :=
  Nat.le_trans h (Nat.le_trans (Nat.le_add_right C x) (Nat.le_add_right _ y))

theorem lt_aff {C a i n m k B : ℕ} (hi : i < n) (hm : m < k) (h : C + a * (n - 1) + k ≤ B) :
    C + a * i + m < B := by
  have : a * i ≤ a * (n - 1) := Nat.mul_le_mul_left a (by omega)
  omega

theorem le_add3 {L C x y z : ℕ} (h : L ≤ C) : L ≤ C + x + y + z :=
  Nat.le_trans (le_add2 h) (Nat.le_add_right _ z)

theorem lt_affC {C a i n m B : ℕ} (hi : i < n) (hm : m < a) (h : C + a * n ≤ B) : C + a * i + m < B := by
  have : a * (i + 1) ≤ a * n := Nat.mul_le_mul_left a hi
  rw [Nat.mul_succ] at this
  omega

theorem lt_ans {x N m B : ℕ} (hx : x < N) (hN : N < 2 ^ 11) (hm : m < 4) (h : ansB + 4 * 2 ^ 11 ≤ B) :
    ansB + 4 * x + m < B := by omega

theorem le_ans {x n N : ℕ} (hx : x + n ≤ N) (hN : N < 2 ^ 11) : ansB + 4 * x + 4 * n ≤ 2 ^ 25 := by
  rw [ansB_v]; omega

theorem lt_aff0 {a i n m k B : ℕ} (hi : i < n) (hm : m < k) (h : a * (n - 1) + k ≤ B) : a * i + m < B := by
  have : a * i ≤ a * (n - 1) := Nat.mul_le_mul_left a (by omega)
  omega

/-- The layout's numbers, for `simp only` before `omega` (the decoders' flags at their numeric workspaces). -/
theorem layNum : memM = 67108864 ∧ wB0M = 33554368 ∧ wB1M = 17039360 ∧ wB2M = 2097152 ∧ dB0M = 8388608 ∧
    dB1M = 4194304 ∧ dB2M = 2621440 ∧ aB0M = 524288 ∧ aB1M = 524320 ∧ aB2M = 524352 ∧ fB0M = 1048576 ∧
    fB1M = 1572864 ∧ fB2M = 1605632 ∧ mBM = 5242880 ∧ ws1M 13 9 = 74752 ∧ ws1M 16 13 = 745472 ∧
    wsM 19 17 8 = 4988928 ∧ ok1M 2621440 = 2625792 ∧ ok1M 4194304 = 4198656 ∧ okM 8388608 = 8392960 ∧
    chB = 16777216 ∧ ansB = 16793600 ∧ chEnd = 16801792 ∧ sgB = 16842752 ∧ nCp = 278528 ∧ regs = 256 ∧
    winM = 12328960 :=
  ⟨memM_v, wB0M_v, wB1M_v, wB2M_v, dB0M_v, dB1M_v, dB2M_v, aB0M_v, aB1M_v, aB2M_v, fB0M_v, fB1M_v, fB2M_v,
    mBM_v, ws2M_v, ws1M_v, ws0M_v, dB2M_v ▸ ok2M_v, dB1M_v ▸ ok1M_v, dB0M_v ▸ ok0M_v, chB_v, ansB_v, chEnd_v,
    sgB_v, nCp_v, regs_v, winM_eq⟩

set_option maxRecDepth 20000 in
/-- **`EXS` on an `S` node proof in the domain** (`EXM_node` at a stage). -/
theorem EXS_node (st : XStage) (hp : ProgOK st) (ho : OutOK st) (A : Digest → Digest → Signed → Bool)
    (c : Digest) (π : Proof) (L : Log)
    (hD : InDomE c π L) (hs : π.size = st.pz) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0)
    (hS : ¬ StateHit L) (αk : ℕ → Digest)
    (hα : ∀ k < 14, fmAns (fsQLS st π) zeroDL L (foldPosKS st k) = some (αk k))
    (wd₀ wd₁ wd₂ : ℕ → ℕ → BF64)
    (hw₀ : ∀ q < 2 ^ 19, ∀ t < 64, wd₀ q t = (readRowG 19 8 (64 - st.occ0) st.occ0 L (capS st π 0) q).getD t 0)
    (hw₁ : ∀ q < 2 ^ 16, ∀ t < 48, wd₁ q t = (readRowG 16 7 0 48 L (capS st π 1) q).getD t 0)
    (hw₂ : ∀ q < 2 ^ 13, ∀ t < 48, wd₂ q t = (readRowG 13 7 0 48 L (capS st π 2) q).getD t 0)
    (α₀ α₁ α₂ : ℕ → BF64.Ext3) (ha₀ : ∀ j < 6, α₀ j = alphaE (αk j))
    (ha₁ : ∀ j < 4, α₁ j = alphaE (αk (6 + j))) (ha₂ : ∀ j < 4, α₂ j = alphaE (αk (10 + j)))
    (f₂ : ℕ → BF64.Ext3) (hf₂ : ∀ v < 2 ^ 9, f₂ v = resES st π v)
    (m₂ : ℕ → BF64.Ext3) (hd₂ : decodeMP2 wd₂ α₂ f₂ = some m₂)
    (m₁ : ℕ → BF64.Ext3) (hd₁ : decodeMP1 wd₁ α₁ m₂ = some m₁)
    (out : List BF64) (hd₀ : decodeMP0 wd₀ α₀ m₁ = some out) :
    EXS st A c π L = some (XwitS st π (wStreamM π out)) := by
  obtain ⟨hπ, hq, ht⟩ := hD
  -- the stage's facts for the address bounds (`ProgOK`)
  have hocc := hp.occ0
  have hN := hp.nCh_lt
  have hf0 : foldPosS st 0 0 + 6 ≤ nChainS st := by
    have := hp.fold 5 (by decide); rw [foldPosKS_0 st (by decide)] at this; exact this
  have hf1 : foldPosS st 1 0 + 4 ≤ nChainS st := by
    have := hp.fold (6 + 3) (by decide); rw [foldPosKS_1 st (by decide)] at this; exact this
  have hf2 : foldPosS st 2 0 + 4 ≤ nChainS st := by
    have := hp.fold (10 + 3) (by decide); rw [foldPosKS_2 st (by decide)] at this; exact this
  rw [EXS, if_pos ⟨hπ, hq, ht⟩, EdXS, Eden]
  clear hπ
  obtain ⟨s1, hM1, z1, ho1, hden⟩ := den_SS c π L (wf_decXS st hp.out) hs h0
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
  rw [decXS, semXIR_seq]
  generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 z2 bo
  have h6 : I.getD 6 0 ≠ 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pwN c π L hs (Nat.lt_of_lt_of_le (by decide) hp.pz15)]; exact hb
  rw [semXIR_ite, if_neg (by rw [b1]; exact h6), nodeS, semXIR_seq]
  -- 1. the index
  have hM3 := inv_sem I (wf_idxIR4 memM (pLS st)) hM2
  have z3 := size_sem I (idxIR4 memM (pLS st)) s2
  have o3 : (semXIR I (idxIR4 memM (pLS st)) s2).o = s2.o := sem_o I _ s2 rfl
  rw [semXIR_seq]
  generalize hs3 : semXIR I (idxIR4 memM (pLS st)) s2 = s3 at hM3 z3 o3
  have hsz3 : 2 ^ 26 + 3 * (extractorInput c π L).length ≤ s3.M.size := by rw [z3, z2, z1]
  have hs2' : memM + L.length + L.length ≤ s2.M.size := by rw [layNum.1, z2, z1]; omega
  have hm3 : 2 ^ 26 ≤ s3.M.size := Nat.le_trans (Nat.le_add_right _ _) hsz3
  clear z1 z2 z3 hsz3 hLt
  -- 2. the chain
  obtain ⟨ch1, ch2⟩ := chainLS_spec st hp c π L hs hq ht hS s3 hM3 (Nat.le_trans (Nat.le_of_ble_eq_true rfl) hm3)
  have hM4 := inv_sem I (P := chainLS st) (wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)))
    hM3
  have z4 := size_sem I (chainLS st) s3
  have o4 : (semXIR I (chainLS st) s3).o = s3.o := sem_o I _ s3 (hasOut_chainLS st)
  rw [semXIR_seq]
  generalize semXIR I (chainLS st) s3 = s4 at ch1 ch2 hM4 z4 o4
  have hm4 : 2 ^ 26 ≤ s4.M.size := by rw [z4]; exact hm3
  clear z4 hm3
  have hX4 : ∀ a < L.length, Lvm.X.rd s4.M (memM + a) =
      Lvm.X.rd (semXIR I (idxIR4 memM (pLS st)) s2).M (memM + a) :=
    fun a ha => by rw [hs3, ch2 _ (le_add1 (Nat.le_of_ble_eq_true rfl)) (.inr (le_add1 (Nat.le_of_ble_eq_true rfl)))]
  -- 3. level 0's word
  rw [show read0S st = readGIR memM (pLS st) (capWS st 0) wB0M (2 ^ 19) (19 - 8) (64 - st.occ0) st.occ0
    from rfl]
  obtain ⟨r1, r2, r3, hM5⟩ := readGIR_sem (bX := memM) (pL := pLS st) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) hp.pL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s4 hM4 (by rw [layNum.1]; exact hm4) hX4 (ht' := 19) (lv := 8) (z := 64 - st.occ0)
    (occ := st.occ0) (capW := capWS st 0) (wB := wB0M) (cap := capS st π 0)
    (fun q hq => by rw [capS_length]; exact Nat.div_lt_of_lt_mul hq)
    (by rw [capS_length]; exact hp.capW0)
    (by decide) (by decide) (Nat.lt_of_le_of_lt hocc (by decide)) (capS_tape st hp c π L hs (by decide))
    (Nat.le_of_ble_eq_true rfl) (by rw [Nat.sub_add_cancel hocc]; exact Nat.le_of_ble_eq_true rfl)
  have z5 := size_sem I (readGIR memM (pLS st) (capWS st 0) wB0M (2 ^ 19) (19 - 8) (64 - st.occ0) st.occ0) s4
  have o5 : (semXIR I (readGIR memM (pLS st) (capWS st 0) wB0M (2 ^ 19) (19 - 8) (64 - st.occ0) st.occ0) s4).o =
    s4.o := sem_o I _ s4 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM (pLS st) (capWS st 0) wB0M (2 ^ 19) (19 - 8) (64 - st.occ0) st.occ0) s4 = s5
    at r1 r2 r3 hM5 z5 o5
  rw [Nat.sub_add_cancel hocc] at r1 r2
  have hm5 : 2 ^ 26 ≤ s5.M.size := by rw [z5]; exact hm4
  clear z5 hm4
  have hX5 : ∀ a < L.length, Lvm.X.rd s5.M (memM + a) =
      Lvm.X.rd (semXIR I (idxIR4 memM (pLS st)) s2).M (memM + a) :=
    fun a ha => by rw [r3 a ha, hX4 a ha]
  -- 4. level 1's word
  rw [show read1M memM (pLS st) (capWS st 1) wB1M = readGIR memM (pLS st) (capWS st 1) wB1M (2 ^ 16) (16 - 7) 0 48
    from rfl]
  obtain ⟨q1, q2, q3, hM6⟩ := readGIR_sem (bX := memM) (pL := pLS st) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) hp.pL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s5 hM5 (by rw [layNum.1]; exact hm5) hX5 (ht' := 16) (lv := 7) (z := 0) (occ := 48)
    (capW := capWS st 1) (wB := wB1M) (cap := capS st π 1)
    (fun q hq => by rw [capS_length]; exact Nat.div_lt_of_lt_mul hq)
    (by rw [capS_length]; exact hp.capW1)
    (by decide) (by decide) (by decide) (capS_tape st hp c π L hs (by decide)) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl)
  have z6 := size_sem I (readGIR memM (pLS st) (capWS st 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5
  have o6 : (semXIR I (readGIR memM (pLS st) (capWS st 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5).o = s5.o :=
    sem_o I _ s5 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM (pLS st) (capWS st 1) wB1M (2 ^ 16) (16 - 7) 0 48) s5 = s6 at q1 q2 q3 hM6 z6 o6
  have hm6 : 2 ^ 26 ≤ s6.M.size := by rw [z6]; exact hm5
  clear z6 hm5
  have hX6 : ∀ a < L.length, Lvm.X.rd s6.M (memM + a) =
      Lvm.X.rd (semXIR I (idxIR4 memM (pLS st)) s2).M (memM + a) :=
    fun a ha => by rw [q3 a ha, hX5 a ha]
  -- 5. level 2's word
  rw [show read2M memM (pLS st) (capWS st 2) wB2M = readGIR memM (pLS st) (capWS st 2) wB2M (2 ^ 13) (13 - 7) 0 48
    from rfl]
  obtain ⟨p1, p2, -, hM7⟩ := readGIR_sem (bX := memM) (pL := pLS st) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) hp.pL c π L (hs_posL hs)
    hq ht s2 hM2 hs2' s6 hM6 (by rw [layNum.1]; exact hm6) hX6 (ht' := 13) (lv := 7) (z := 0) (occ := 48)
    (capW := capWS st 2) (wB := wB2M) (cap := capS st π 2)
    (fun q hq => by rw [capS_length]; exact Nat.div_lt_of_lt_mul hq)
    (by rw [capS_length]; exact hp.capW2)
    (by decide) (by decide) (by decide) (capS_tape st hp c π L hs (by decide)) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl)
  have z7 := size_sem I (readGIR memM (pLS st) (capWS st 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6
  have o7 : (semXIR I (readGIR memM (pLS st) (capWS st 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6).o = s6.o :=
    sem_o I _ s6 rfl
  rw [semXIR_seq]
  generalize semXIR I (readGIR memM (pLS st) (capWS st 2) wB2M (2 ^ 13) (13 - 7) 0 48) s6 = s7 at p1 p2 hM7 z7 o7
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
    rw [f2 y hy h2, a22 y hy (by simp only [layNum]; omega), a12 y hy (by simp only [layNum]; omega),
      a02 y hy (by simp only [layNum]; omega)]
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
        ← Nat.add_assoc (resOffS st / 8), tape_pwN c π L hs (lt_affC hv hm hp.res)]
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
    (Nat.le_of_ble_eq_true rfl) e21 (.seq (decMP1IR dB1M wB1M aB1M fB1M fB0M) (okL1S st))
  rw [okL2S, e11, semXIR_seq]
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
    (Nat.le_of_ble_eq_true rfl) e11' (.seq (decMP0IRW dB0M wB0M aB0M fB0M) (okL0S st))
  rw [okL1S, e13', semXIR_seq]
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
  obtain ⟨e01, e02, e03, hM14⟩ := decMP0IRW_sem I s13 hM13 (lay0M (by rw [layNum.1]; exact hsz13)) wd₀ α₀ m₁ hW0
    hAl0 hF0
  have z14 := size_sem I (decMP0IRW dB0M wB0M aB0M fB0M) s13
  have o14 : (semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13).o = s13.o := sem_o I _ s13 rfl
  rw [decide_eq_true (dec_ok0 hd₀)] at e01
  have hout := e02 out hd₀
  generalize semXIR I (decMP0IRW dB0M wB0M aB0M fB0M) s13 = s14 at e01 hout e03 hM14 z14 o14
  -- 11. the flag, the stream block, the node output
  obtain ⟨s15, hM15, z15, o15, k15, e15⟩ := flagIte_sem I s14 hM14 (a := okM dB0M) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) e01 (.seq streamM (outIRS st mBM))
  rw [okL0S, e15, semXIR_seq]
  have hsz15 : 2 ^ 26 ≤ s15.M.size := by rw [z15, z14]; exact hsz13
  clear z14 z15 hsz13
  obtain ⟨w1, -, hM16, z16, o16⟩ := streamS_sem c π L hs hp.pz15 s15 hM15 (by rw [layNum.1]; exact hsz15) out
    fun j hj => by
      rw [k15 _ (le_add1 (Nat.le_of_ble_eq_true rfl)), ← rdK_toBitVec, hout j hj]
  obtain ⟨ws, hws, hdec⟩ := outIRS_sem st hp.out c π L hs _ hM16 (mB := mBM) (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) (by rw [z16]; exact Nat.le_trans (Nat.le_of_ble_eq_true rfl) hsz15)
    (wStreamM π out) w1
  rw [hws, o16, o15, o14, o13, o12, o11, o10, o9, o8, o8b, o8a, o7, o6, o5, o4, o3, bo, ho1, Array.toList_empty,
    List.nil_append]
  exact hdec

end Lvm.XS
