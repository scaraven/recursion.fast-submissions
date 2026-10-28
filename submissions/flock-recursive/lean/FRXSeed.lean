-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 16: `vk` in an 'N' proof's header;
-- stage S-H2, track L-ext).
import FRXChainFlock

/-!
# The seed block: the seed query's 15 words from the tape

An `'N'` proof carries `vk` in header bytes `16 … 47` (§10 changes 16; `V` asserts it), so the
extractor rebuilds the Fiat–Shamir seed `"FRSEED0" ‖ vk ‖ c ‖ hdr` from the tape alone. The seed's
payload `S = vk ‖ c ‖ hdr` is 14 tape words (`sPos`): `vk` at words `7 … 10`, `c` at `0 … 3`, `hdr`
at `5 … 10`. The 7-byte tag shifts the payload by 7 bytes, so seed word `j` is

* `j = 0`: `tag + (S₀ << 56)`;
* `1 ≤ j ≤ 13`: `(S_{j−1} >> 8) + (S_j << 56)`;
* `j = 14`: `S₁₃ >> 8`.

(`+` equals `|` here: the two parts occupy disjoint bytes.)

* `packBytes_shift7`: the packed words of `t ‖ s` with `|t| = 7` in terms of `s`'s (pure).
* `seedIR`: 15 straight-line blocks `sdW j` (`hB + j := word j`).
* **`seedOK_seedIR`**: `SeedOK seedIR I (fsQ (vkOf π) c π 0 zeroD)` on every SNARK tape.
-/

namespace FR.X

open RecursionFast FR.Snd

/-! ## The `vk` an `'N'` proof carries -/

/-- **The `vk` field of an `'N'` proof**: header bytes `16 … 47` (§10 changes 16). -/
def vkOf (π : Proof) : Digest := bytesAt π 16 32

/-! ## Little-endian numbers of byte slices -/

theorem ofLE_append (a b : List UInt8) : ofLE (a ++ b) = ofLE a + 256 ^ a.length * ofLE b := by
  induction a with
  | nil => simp [ofLE]
  | cons d a ih =>
    rw [List.cons_append, ofLE_cons, ofLE_cons, ih, List.length_cons, Nat.pow_succ]; ring

theorem ofLE_take1 (l : List UInt8) : ofLE (l.take 1) = (l.getD 0 0).toNat := by
  cases l <;> simp [ofLE]

theorem ofLE_take8_mod (l : List UInt8) : ofLE (l.take 8) % 256 = (l.getD 0 0).toNat := by
  have := ofLE_div_mod (l.take 8) 0
  rw [pow_zero, Nat.div_one] at this
  rw [this]
  cases l <;> simp

theorem ofLE_take8_div (l : List UInt8) : ofLE (l.take 8) / 256 = ofLE ((l.drop 1).take 7) := by
  cases l with
  | nil => simp [ofLE]
  | cons x u =>
    rw [List.take_succ_cons, ofLE_cons, List.drop_succ_cons, List.drop_zero]
    have := x.toNat_lt
    omega

/-- Every packed word, as the number of its 8-byte slice (`0` past the end). -/
theorem packBytes_getD' (l : List UInt8) (k : ℕ) :
    (packBytes l).getD k 0 = toWord (ofLE ((l.drop (8 * k)).take 8)) := by
  rw [packBytes_getD]
  split_ifs with h
  · rfl
  · rw [List.drop_eq_nil_of_le (by omega)]; rfl

theorem toWord_shr8 (w : ℕ) (h : w < 2 ^ 64) : toWord w >>> 8 = toWord (w / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_toWord h, toNat_toWord (by omega), Nat.shiftRight_eq_div_pow]

theorem mul56_mod (x : ℕ) : x * 2 ^ 56 % 2 ^ 64 = x % 256 * 2 ^ 56 := by
  rw [show (2 : ℕ) ^ 64 = 256 * 2 ^ 56 by norm_num, Nat.mul_mod_mul_right]

theorem toWord_shl56 (w : ℕ) : toWord w <<< 56 = toWord (w % 256 * 2 ^ 56) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [toWord, BitVec.toNat_ofNat]
  rw [mul56_mod, mul56_mod, Nat.mod_mod, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem toWord_add' (a b : ℕ) : toWord a + toWord b = toWord (a + b) := (BitVec.ofNat_add a b).symm

/-- **The packed words of `t ‖ s`** with a 7-byte `t`, in terms of `s`'s words: word `j` is
`(j = 0 ? t : P_{j−1} >> 8) + (P_j << 56)`. -/
theorem packBytes_shift7 (t s : List UInt8) (ht : t.length = 7) (j : ℕ) :
    (packBytes (t ++ s)).getD j 0 =
      (if j = 0 then toWord (ofLE t) else (packBytes s).getD (j - 1) 0 >>> 8) +
        (packBytes s).getD j 0 <<< 56 := by
  simp only [packBytes_getD']
  rw [toWord_shl56, ofLE_take8_mod]
  rcases j with _ | j
  · rw [if_pos rfl, Nat.mul_zero, List.drop_zero, List.drop_zero, List.take_append,
      List.take_of_length_le (by omega), ht, ofLE_append, ofLE_take1, ht, toWord_add']
    congr 1
    norm_num; ring
  · rw [if_neg (by omega), Nat.add_sub_cancel, toWord_shr8 _ (ofLE_lt64 (by simp)),
      ofLE_take8_div, List.drop_drop, toWord_add', List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, ht,
      show 8 * (j + 1) - 7 = 1 + 8 * j by omega,
      show List.take 8 (List.drop (1 + 8 * j) s) = _ from List.take_add (i := 7) (j := 1),
      List.drop_drop, ofLE_append, ofLE_take1, show 1 + 8 * j + 7 = 8 * (j + 1) by omega,
      show 8 * j + 1 = 1 + 8 * j by omega]
    congr 1
    by_cases hB : 8 * (j + 1) < s.length
    · rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]; norm_num; ring
    · rw [List.drop_eq_nil_of_le (as := s) (i := 8 * (j + 1)) (by omega)]; simp

/-! ## The seed's words from the tape -/

/-- The seed's payload `vk ‖ c ‖ hdr` (112 bytes). -/
def seedPay (c : Digest) (π : Proof) : List UInt8 :=
  (vkOf π).toList ++ (c.toList ++ (π.extract 0 48).data.toList)

/-- The tape word of the payload's word `k < 14`: `vk` at `7 … 10`, `c` at `0 … 3`, `hdr` at
`5 … 10`. -/
def sPos (k : ℕ) : ℕ := if k < 4 then 7 + k else if k < 8 then k - 4 else k - 3

/-- The seed tag's word (7 bytes). -/
def tagSeedW : Word := toWord (ofLE tagSeed)

/-- **Seed word `j`** as the machine computes it from the tape. -/
def seedVal (I : Array Word) (j : ℕ) : Word :=
  (if j = 0 then tagSeedW else I.getD (sPos (j - 1)) 0 >>> 8) +
    (if j < 14 then I.getD (sPos j) 0 <<< 56 else 0)

theorem seedQ_data' (vk c : Digest) (hdr : ByteArray) :
    (seedQ vk c hdr).data.toList = tagSeed ++ (vk.toList ++ (c.toList ++ hdr.data.toList)) := by
  simp [seedQ, bytesOf, ByteArray.data_append]

theorem tape_getD_c (c : Digest) (π : Proof) (L : Log) {i : ℕ} (hi : i < 4) :
    (extractorInput c π L).getD i 0 = (packBytes c.toList).getD i 0 := by
  rw [tape_eq, List.append_assoc, List.append_assoc,
    List.getD_append _ _ _ _ (by rw [packBytes_digest_length]; exact hi)]

theorem seedPay_length (c : Digest) (π : Proof) (hs : π.size = piSize) :
    (seedPay c π).length = 112 := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  have h48 : (π.extract 0 48).data.toList.length = 48 := by
    rw [Array.length_toList]; exact extract_size π (o := 0) (len := 48) (by omega)
  simp only [seedPay, List.length_append, Vector.length_toList, h48]

/-- **The payload's words are tape words** (on a tape of a proof of `piSize` bytes). -/
theorem tape_seed (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {k : ℕ}
    (hk : k < 14) :
    (extractorInput c π L).toArray.getD (sPos k) 0 = (packBytes (seedPay c π)).getD k 0 := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  have hpl : ∀ j, j < 99738 → (extractorInput c π L).getD (5 + j) 0 =
      (packBytes π.data.toList).getD j 0 := fun j hj => by
    rw [tape_getD_proof c π L (by rw [hp]; omega), List.getD_eq_getElem]
  rw [getD_toArray, seedPay, packBytes_append8 _ _ (k := 4) (by simp)]
  unfold sPos
  split_ifs with h4 h8
  · rw [show 7 + k = 5 + (2 + k) by omega, hpl _ (by omega), vkOf,
      show (16 : ℕ) = 8 * 2 from rfl, packBytes_bytesAt π (by omega) h4]
  · rw [packBytes_append8 _ _ (k := 4) (by simp), if_pos (by omega)]
    exact tape_getD_c c π L (by omega)
  · rw [packBytes_append8 _ _ (k := 4) (by simp), if_neg (by omega),
      show k - 3 = 5 + (k - 4 - 4) by omega, hpl _ (by omega),
      show (π.extract 0 48) = π.extract (8 * 0) (8 * 0 + 8 * 6) from rfl,
      extract_words π (by omega) (by omega), Nat.zero_add]

/-- **The machine's seed words are the seed query's** `"FRSEED0" ‖ vkOf π ‖ c ‖ hdr`. -/
theorem seedVal_eq (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) (st : Digest)
    {j : ℕ} (hj : j < 15) :
    seedVal (extractorInput c π L).toArray j =
      (packBytes (fsQ (vkOf π) c π 0 st).data.toList).getD j 0 := by
  have hl := seedPay_length c π hs
  rw [show fsQ (vkOf π) c π 0 st = seedQ (vkOf π) c (π.extract 0 48) by
      unfold fsQ; rw [fsMsgs_ctl.1]; rfl,
    seedQ_data', ← seedPay, packBytes_shift7 _ _ rfl, seedVal]
  have hlo : (if j = 0 then tagSeedW else (extractorInput c π L).toArray.getD (sPos (j - 1)) 0 >>> 8)
      = (if j = 0 then toWord (ofLE tagSeed) else (packBytes (seedPay c π)).getD (j - 1) 0 >>> 8) := by
    by_cases h0 : j = 0
    · simp only [if_pos h0]; exact rfl
    · simp only [if_neg h0]; rw [tape_seed c π L hs (by omega)]
  have hhi : (if j < 14 then (extractorInput c π L).toArray.getD (sPos j) 0 <<< 56 else 0) =
      (packBytes (seedPay c π)).getD j 0 <<< 56 := by
    by_cases h14 : j < 14
    · simp only [if_pos h14]; rw [tape_seed c π L hs h14]
    · simp only [if_neg h14]
      rw [packBytes_getD, if_neg (by omega)]; exact (BitVec.zero_shiftLeft 56).symm
  rw [hlo, hhi]

/-! ## The program -/

/-- The low part. -/ def rSa : ℕ := 212
/-- The high part. -/ def rSb : ℕ := 213
/-- Constant scratch. -/ def rSk : ℕ := 214
/-- The store address. -/ def rSad : ℕ := 215

/-- `rSa :=` the low part of seed word `j`: the tag, or `S_{j−1} >> 8`. -/
def loIR (j : ℕ) : XIR :=
  if j = 0 then .blk [.const rSa tagSeedW]
  else .seq (readAt rSa (sPos (j - 1))) (.blk [.const rSk 8, .op .shr rSa rSa rSk])

/-- `rSb :=` the high part of seed word `j`: `S_j << 56`, or `0` for the last word. -/
def hiIR (j : ℕ) : XIR :=
  if j < 14 then .seq (readAt rSb (sPos j)) (.blk [.const rSk 56, .op .shl rSb rSb rSk])
  else .blk [.const rSb 0]

/-- **Seed word `j`** into `H[j]`. -/
def sdW (j : ℕ) : XIR :=
  .seq (loIR j) (.seq (hiIR j) (.seq (.blk [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))])
    (.store rSad rSa)))

/-- The words `js`, in order. -/
def sdList : List ℕ → XIR
  | [] => .blk []
  | j :: js => .seq (sdW j) (sdList js)

/-- **The seed block**: the seed query's 15 words into `H[0 … 14]`. -/
def seedIR : XIR := sdList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-! ## Well formed; what it writes -/

/-- The registers the seed block writes. -/
def SdReg (i : ℕ) : Prop := i = rSa ∨ i = rSb ∨ i = rSk ∨ i = rSad ∨ i = rA ∨ i = cTmp

theorem wf_sdW (j : ℕ) : WF (sdW j) := by
  unfold sdW loIR hiIR
  split_ifs <;> simp [WF, readAt, Prim.dst, rSa, rSb, rSk, rSad, rA, cTmp]

theorem writes_sdW {j i : ℕ} (h : Writes (sdW j) i) : SdReg i := by
  unfold sdW loIR hiIR at h
  unfold SdReg
  split_ifs at h <;> simp [Writes, readAt, Prim.dst] at h <;> omega

theorem lo_loIR (j : ℕ) : Lo (loIR j) := by
  unfold loIR; split_ifs <;> simp [Lo, readAt, Prim.dst, rSa, rSk, rA, regs]

theorem lo_hiIR (j : ℕ) : Lo (hiIR j) := by
  unfold hiIR; split_ifs <;> simp [Lo, readAt, Prim.dst, rSb, rSk, rA, regs]

theorem wf_sdList : ∀ js : List ℕ, WF (sdList js)
  | [] => by simp [sdList, WF]
  | j :: js => ⟨wf_sdW j, wf_sdList js⟩

theorem writes_sdList : ∀ (js : List ℕ) {i : ℕ}, Writes (sdList js) i → SdReg i
  | [], _, h => by simp [sdList, Writes] at h
  | j :: js, _, h => h.elim writes_sdW (writes_sdList js)

theorem noLoopT_sdList : ∀ js : List ℕ, NoLoopT (sdList js)
  | [] => trivial
  | j :: js => ⟨by unfold sdW loIR hiIR; split_ifs <;> simp [NoLoopT, readAt], noLoopT_sdList js⟩

theorem outs_sdList (t : ℕ) : ∀ js : List ℕ, outs (sdList js) t = 0
  | [] => rfl
  | j :: js => by
    simp only [sdList, outs, outs_sdList t js]
    unfold sdW loIR hiIR; split_ifs <;> simp [outs, readAt]

theorem cost_sdW (j t : ℕ) : cost (sdW j) t ≤ 24 := by
  unfold sdW loIR hiIR; split_ifs <;> simp [cost, readAt, blkSteps]

theorem size_sdW (j : ℕ) : sizeIR (sdW j) ≤ 25 := by
  unfold sdW loIR hiIR; split_ifs <;> simp [sizeIR, readAt, blkSteps]

theorem cost_sdList (t : ℕ) : ∀ js : List ℕ, cost (sdList js) t ≤ 25 * js.length + 1
  | [] => by simp [sdList, cost, blkSteps]
  | j :: js => by
    simp only [sdList, cost, List.length_cons]
    have := cost_sdW j t; have := cost_sdList t js; omega

theorem size_sdList : ∀ js : List ℕ, sizeIR (sdList js) ≤ 26 * js.length + 1
  | [] => by simp [sdList, sizeIR, blkSteps]
  | j :: js => by
    simp only [sdList, sizeIR, List.length_cons]
    have := size_sdW j; have := size_sdList js; omega

theorem cost_seedIR (t : ℕ) : cost seedIR t ≤ 376 := cost_sdList t _
theorem size_seedIR : sizeIR seedIR ≤ 391 := size_sdList _

/-! ## The semantics -/

theorem loIR_sem (I : Array Word) (j : ℕ) (s : St) (hM : Inv s.M) (hp : sPos (j - 1) < 2 ^ 64) :
    rd (semXIR I (loIR j) s).M rSa =
      if j = 0 then tagSeedW else I.getD (sPos (j - 1)) 0 >>> 8 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold loIR
  split_ifs with h0
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rSa]; omega)]
  · rw [semXIR_seq]
    have r1 := rd_readAt I s hM (d := rSa) (by decide) hp
    have hM1 := inv_sem I (P := readAt rSa (sPos (j - 1))) (by simp [WF, readAt, Prim.dst, rSa, rA]) hM
    generalize semXIR I (readAt rSa (sPos (j - 1))) s = s1 at r1 hM1
    have hs1 := hM1.1
    simp only [regs] at hs1
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rSa]; omega), rd_set_self (by simp only [rSk]; omega),
      rd_set_ne (by decide), r1]
    simp [XOp.eval]

theorem hiIR_sem (I : Array Word) (j : ℕ) (s : St) (hM : Inv s.M) (hp : sPos j < 2 ^ 64) :
    rd (semXIR I (hiIR j) s).M rSb = if j < 14 then I.getD (sPos j) 0 <<< 56 else 0 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold hiIR
  split_ifs with h0
  · rw [semXIR_seq]
    have r1 := rd_readAt I s hM (d := rSb) (by decide) hp
    have hM1 := inv_sem I (P := readAt rSb (sPos j)) (by simp [WF, readAt, Prim.dst, rSb, rA]) hM
    generalize semXIR I (readAt rSb (sPos j)) s = s1 at r1 hM1
    have hs1 := hM1.1
    simp only [regs] at hs1
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rSb]; omega), rd_set_self (by simp only [rSk]; omega),
      rd_set_ne (by decide), r1]
    simp [XOp.eval]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rSb]; omega)]

theorem sPos_lt (k : ℕ) : sPos k ≤ k + 7 := by unfold sPos; split_ifs <;> omega

/-- **One seed word**: `H[j] := seedVal I j`; every other heap cell is kept. -/
theorem sdW_sem (I : Array Word) {j : ℕ} (hj : j < 16) (s : St) (hM : Inv s.M)
    (hsz : chEnd ≤ s.M.size) :
    rd (semXIR I (sdW j) s).M (hB + j) = seedVal I j ∧
    (∀ y, regs ≤ y → y ≠ hB + j → rd (semXIR I (sdW j) s).M y = rd s.M y) ∧
    Inv (semXIR I (sdW j) s).M := by
  rw [sdW, semXIR_seq, semXIR_seq, semXIR_seq]
  have l1 := loIR_sem I j s hM (by have := sPos_lt (j - 1); omega)
  have hM1 := inv_sem I (wf_sdW j).1 hM
  have f1 := hframe I (loIR j) s (lo_loIR j)
  have z1 := size_sem I (loIR j) s
  generalize semXIR I (loIR j) s = s1 at l1 hM1 f1 z1
  have h2 := hiIR_sem I j s1 hM1 (by have := sPos_lt j; omega)
  have l2 : rd (semXIR I (hiIR j) s1).M rSa = rd s1.M rSa :=
    frame I (hiIR j) s1 (wf_sdW j).2.1 hM1 rSa (by decide) (by
      unfold hiIR; split_ifs <;> simp [Writes, readAt, Prim.dst, rSa, rSb, rSk, rA])
  have hM2 := inv_sem I (wf_sdW j).2.1 hM1
  have f2 := hframe I (hiIR j) s1 (lo_hiIR j)
  have z2 := size_sem I (hiIR j) s1
  generalize semXIR I (hiIR j) s1 = s2 at h2 l2 hM2 f2 z2
  have hs2 := hM2.1
  simp only [regs] at hs2
  have e3 : semXIR I (.blk [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))]) s2 =
      ⟨runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M, s2.o⟩ := rfl
  rw [e3]
  have hM3 : Inv (runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M) :=
    inv_runPrims (by simp [Prim.dst, rSa, rSad]) hM2
  have a3 : rd (runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M) rSad =
      toWord (hB + j) := by
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rSad]; omega)]
  have v3 : rd (runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M) rSa =
      seedVal I j := by
    simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [rSa]; omega), l2, l1, h2]
    rfl
  have f3 : ∀ y, regs ≤ y →
      rd (runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M) y = rd s2.M y :=
    fun y hy => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl) <;> simp only [Prim.dst, rSa, rSad] <;> simp only [regs] at hy <;> omega) _
  have z3 := size_runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M
  generalize runPrims [.op .add rSa rSa rSb, .const rSad (toWord (hB + j))] s2.M = M3
    at hM3 a3 v3 f3 z3
  have e4 : semXIR I (.store rSad rSa) ⟨M3, s2.o⟩ = ⟨storeM M3 rSad rSa, s2.o⟩ := rfl
  rw [e4]
  have st : ∀ i, i ≠ cTmp → rd (storeM M3 rSad rSa) i = if i = hB + j then rd M3 rSa else rd M3 i :=
    fun i hi => rd_storeM hM3 a3 (by simp only [hB_eq, regs]; omega) (by simp only [hB_eq]; omega)
      (by rw [z3, z2, z1]; simp only [chEnd, hB_eq] at hsz ⊢; omega) (by decide) (by decide) hi
  refine ⟨?_, fun y hy hne => ?_, ?_⟩
  · rw [st _ (by simp only [hB_eq, cTmp]; omega), if_pos rfl, v3]
  · rw [st _ (by simp only [regs] at hy; simp only [cTmp]; omega), if_neg hne, f3 y hy, f2 y hy,
      f1 y hy]
  · have := inv_sem I (P := .store rSad rSa) (s := ⟨M3, s2.o⟩) (by simp [WF, rSad, cTmp]) hM3
    rwa [e4] at this

theorem sdList_sem (I : Array Word) : ∀ (js : List ℕ), js.Nodup → (∀ j ∈ js, j < 16) →
    ∀ s : St, Inv s.M → chEnd ≤ s.M.size →
    (∀ j ∈ js, rd (semXIR I (sdList js) s).M (hB + j) = seedVal I j) ∧
    (∀ y, regs ≤ y → (∀ j ∈ js, y ≠ hB + j) → rd (semXIR I (sdList js) s).M y = rd s.M y) ∧
    Inv (semXIR I (sdList js) s).M
  | [], _, _, s, hM, _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, hM⟩
  | j :: js, hnd, hlt, s, hM, hsz => by
    rw [List.nodup_cons] at hnd
    obtain ⟨a1, a2, a3⟩ := sdW_sem I (hlt j (List.mem_cons_self ..)) s hM hsz
    rw [sdList, semXIR_seq]
    have z1 := size_sem I (sdW j) s
    generalize semXIR I (sdW j) s = s1 at a1 a2 a3 z1
    obtain ⟨b1, b2, b3⟩ := sdList_sem I js hnd.2 (fun k hk => hlt k (List.mem_cons_of_mem _ hk)) s1
      a3 (by rw [z1]; exact hsz)
    refine ⟨fun k hk => ?_, fun y hy hne => ?_, b3⟩
    · rcases List.mem_cons.mp hk with rfl | hk
      · rw [b2 _ (by simp only [hB_eq, regs]; omega) (fun k' hk' h => hnd.1 (by
          rw [show k' = k by omega] at hk'; exact hk')), a1]
      · exact b1 k hk
    · rw [b2 y hy (fun k hk => hne k (List.mem_cons_of_mem _ hk)),
        a2 y hy (hne j (List.mem_cons_self ..))]

/-- **`SeedOK`** for the seed block, on every SNARK tape: its 15 words are the seed query's,
`"FRSEED0" ‖ vkOf π ‖ c ‖ hdr`. -/
theorem seedOK_seedIR (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) (st : Digest) :
    SeedOK seedIR (extractorInput c π L).toArray (fsQ (vkOf π) c π 0 st) := by
  refine ⟨wf_sdList _, fun h => ?_, fun s hM hsz => ?_⟩
  · rcases writes_sdList _ h with h | h | h | h | h | h <;> simp [rCC, rSa, rSb, rSk, rSad, rA, cTmp] at h
  · obtain ⟨a1, a2, -⟩ := sdList_sem (extractorInput c π L).toArray
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] (by decide) (by decide) s hM hsz
    simp only [seedIR]
    refine ⟨fun j hj => ?_, ?_, fun y hy hy2 => a2 y hy fun k hk => ?_⟩
    · rw [a1 j (by simp; omega), seedVal_eq c π L hs st hj]
    · refine frame _ seedIR s (wf_sdList _) hM rCn5 (by decide) fun h => ?_
      rcases writes_sdList _ h with h | h | h | h | h | h <;>
        simp [rCn5, rSa, rSb, rSk, rSad, rA, cTmp] at h
    · have : k < 15 := by simp at hk; omega
      omega

/-! ## Controls -/

/-- **Positive control** of `packBytes_shift7`: word 1 of `t ‖ s` (`|t| = 7`) is
`(S₀ >> 8) + (S₁ << 56)`. -/
theorem shift7_ctl :
    (packBytes ([1, 2, 3, 4, 5, 6, 7] ++ [8, 9, 10, 11, 12, 13, 14, 15, 16] : List UInt8)).getD 1 0 =
      (packBytes ([8, 9, 10, 11, 12, 13, 14, 15, 16] : List UInt8)).getD 0 0 >>> 8 +
        (packBytes ([8, 9, 10, 11, 12, 13, 14, 15, 16] : List UInt8)).getD 1 0 <<< 56 := by
  decide +kernel

/-- **Negative control**: without the shift, the payload's own word is not the seed's word. -/
theorem shift7_ctl_neg :
    (packBytes ([1, 2, 3, 4, 5, 6, 7] ++ [8, 9, 10, 11, 12, 13, 14, 15, 16] : List UInt8)).getD 1 0 ≠
      (packBytes ([8, 9, 10, 11, 12, 13, 14, 15, 16] : List UInt8)).getD 1 0 := by
  decide +kernel

end FR.X
