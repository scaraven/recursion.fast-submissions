-- New for `flock-recursive` (BLUEPRINT §6.2 steps 3–4, the five levels chained; stage S-H2,
-- track L-ext, S-H2j).
import FRXDecLv
import FRXDec

/-!
# The five levels chained

After the node branch's index, level 0's read and the chain replay, the decode runs

`wtabIR tb0 ; (readLv 4 ; decLvIR msg₄ 4) ; (readLv 3 ; decLvIR msg₃ 3) ; … ; decLvIR msg₀ 0`

(`decLevels`). Level `i + 1`'s decoded rows at `obL` feed level `i`'s message step (`msgHIR`);
level 4's message is π's final field (`msgTIR`).

* `readIR_frame`: the ladder read keeps the heap outside its store (from `posLoop`);
* `lvStep_sem`: one read-and-decode step of levels 1–4 on the memory map of `FRXDecLv`;
* **`decLevels_sem`**: level 0's rows at `ob0` are `msgOf 0` (`F`-valued), given the basis-table
  free heap, level 0's word at `colBase`, the chain's answers at `ansB`, the sorted index, the cap
  link `capDig = capPiL`, the final-message link `finalAt = finPi`, and per level `¬ farL` and
  `A_c = jointAgree`.
-/

namespace FR.X

open RecursionFast FR FR.Snd FR.Merkle

/-! ## The read keeps the heap outside its store -/

section Pos

variable {c : Digest} {π : Proof} {L : Log} {i : ℕ}

/-- **The ladder read's frame** (`posLoop`'s): `readIR` keeps every heap cell outside
`[sb, sb + nw·np)`. `readIR_sem` states the store and the index. -/
theorem readIR_frame (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ memX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) (hsz : memX ≤ s.M.size) :
    ∀ y, regs ≤ y → (y < sb ∨ sb + nw * np ≤ y) →
      rd (semXIR (tp c π L) (readIR i cw sb nw sib np) s).M y = rd s.M y := by
  set I := tp c π L
  have hs := hM.1
  simp only [regs] at hs
  have hm : memX = 2 ^ 26 := rfl
  have wf0 : WF (.blk [.const rPp 0, .const rWA (toWord sb), .const rNp (toWord np)]) := by
    simp [WF, Prim.dst, rPp, rWA, rNp]
  have r0 : rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rPp = toWord 0 ∧
      rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rWA = toWord (sb + nw * 0) ∧
      rd (semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
        .const rNp (toWord np)]) s).M rNp = toWord np := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rPp, rWA, rNp]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [Nat.mul_zero, Nat.add_zero]
  have hH0 := hframe I (.blk [.const rPp 0, .const rWA (toWord sb), .const rNp (toWord np)]) s
    (by simp [Lo, Prim.dst, regs, rPp, rWA, rNp])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const rPp 0, .const rWA (toWord sb),
    .const rNp (toWord np)]) s
  rw [readIR, semXIR_seq]
  generalize semXIR I (.blk [.const rPp 0, .const rWA (toWord sb),
    .const rNp (toWord np)]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ rCp → i ≠ cTmp → rd (entryK rCp rNp (toWord np) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK rCp rNp (toWord np) s0.M) rCp = toWord np :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := rCp) (n := rNp) (K := toWord np) hM0 (by decide)
  have e : semXIR I (.loopK rCp rNp (toWord np) (posBody i cw nw sib)) s0 =
      iterL (semXIR I (posBody i cw nw sib)) rCp np ⟨entryK rCp rNp (toWord np) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show np < 2 ^ 64 by omega)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ rCp ∧ y ≠ cTmp := fun y hy => by
    simp only [rCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK rCp rNp (toWord np) s0.M) y = rd s.M y := fun y hy' => by
    rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : nw * (0 + np) = nw * np := by rw [Nat.zero_add]
  obtain ⟨d1, d2, d3⟩ := posLoop hD hX hcw hcap hnw hsib hnp hst hsb hcapn np 0
    ⟨entryK rCp rNp (toWord np) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK rCp rNp (toWord np) s0.M) (memX + a) = _
      rw [hHE _ (by simp only [regs]; omega), hXs a ha])
    (by show rd (entryK rCp rNp (toWord np) s0.M) rPp = _; rw [hE _ (by decide) (by decide), p0])
    (by show rd (entryK rCp rNp (toWord np) s0.M) rWA = _; rw [hE _ (by decide) (by decide), a0])
  intro y hy hy2
  rw [d2 y hy (by rw [Nat.mul_zero, Nat.add_zero, e0]; exact hy2)]
  show rd (entryK rCp rNp (toWord np) s0.M) y = _
  rw [hHE y hy]

end Pos

variable {c : Digest} {π : Proof} {L : Log}

/-- **The read of level `i ∈ [1, 4]` keeps the heap** outside `[stB, stB + 32·2^logNL i)`. -/
theorem readLv_frame (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    ∀ y, regs ≤ y → (y < stB ∨ stB + 32 * 2 ^ logNL i ≤ y) →
      rd (semXIR (tp c π L) (readLv i) s).M y = rd s.M y := by
  have hps : π.size = 797904 := hD.hs.trans piSize_eq
  have hfit := capOffL_fit hi
  have hlog := capLogL_le i
  have hoff := capOffL_le i
  have hmod := capOffL_mod i
  have hcl : 2 ^ capLogL i ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hlog
  have hnp : 2 ^ logNL i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by unfold logNL; omega)
  have hcapn : 2 ^ logNL i ≤ 2 ^ capLogL i * 2 ^ sibL i := by
    rw [← Nat.pow_add]; refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold sibL logNL capLogL; split_ifs <;> omega
  have hsib : sibL i < 64 := by unfold sibL logNL; omega
  exact readIR_frame hD hX s hM hXs (i := i) (cw := capWL i) (nw := 32) (ncap := 2 ^ capLogL i)
    (sb := stB) (cap := capPiL i π) (by unfold capWL; omega)
    (fun e he m hm => by
      simp only [tp, getD_toArray]
      exact tape_capL c π L hmod (by
        have : 32 * e + 32 ≤ 32 * 2 ^ capLogL i := by omega
        omega) hm)
    (by norm_num) hsib (by omega) (by simp only [stB, memX]; omega)
    (by simp only [regs, stB]; omega) hcapn hsz

/-! ## The level parameters -/

theorem lvl_logN {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) : (lvl .N30 i).logN = logNL i := by
  interval_cases i <;> rfl

theorem lvl_sib {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) : (lvl .N30 i).sib = sibL i := by
  interval_cases i <;> rfl

theorem lvl_rows {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) : (lvl .N30 i).rows = 16 := by
  interval_cases i <;> rfl

/-- P1.i's answers are chain positions below `nRep`. -/
theorem p1_lt_nRep {i v : ℕ} (hi : i < 5) (hv : v < (lvl .N30 i).ell) :
    phStart (26 + 5 * i) + 2 * v + 1 < nRep := by
  have : phStart (26 + 5 * i) + 2 * (lvl .N30 i).ell ≤ nRep := by
    unfold phStart; rw [fsStarts_eq]; interval_cases i <;> decide
  omega

/-- **The read is the committed word** of level `i ∈ [1, 4]` when the caps π carries are the
log's (`capDig es i = capPiL i π`, the C phases' absorbs). -/
theorem readLv_wordOf (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {es : Log} {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4)
    (hcap : ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e) :
    ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF (semXIR (tp c π L) (readLv i) s).M (stB + 32 * j + 2 * r) =
        wordOf .N30 L es i r ⟨j, hj⟩ := by
  intro j hj r
  have hR := lvl_rows hi1 hi
  have hr : (r : ℕ) < 16 := hR ▸ r.2
  rw [lvl_logN hi1 hi] at hj
  rw [readLv_spec_F hD hX s hM hXs hsz hi1 hi hj hr, wordOf, colOf, lvl_sib hi1 hi]
  have hcl : capLogL i = (lvl .N30 i).cap := by interval_cases i <;> rfl
  have hq : j / 2 ^ sibL i < 2 ^ capLogL i := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    refine lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) ?_)
    unfold sibL logNL capLogL; split_ifs <;> omega
  rw [hcap _ hq]
  rfl

/-! ## The message steps, from a heap that agrees below `2^24` -/

/-- The `eq` table of level `i` keeps the heap outside `[eqB, eqB + 256)`. -/
theorem eqt_keep (I : Array Word) (s : St) (hM : Inv s.M) (hsz : memX ≤ s.M.size) {i : ℕ}
    (hi : i < 5) :
    Inv (semXIR I (eqtIR (lvl .N30 i).ell (cbS i) eqB) s).M ∧
    ∀ y, regs ≤ y → (y < eqB ∨ eqB + 256 ≤ y) →
      rd (semXIR I (eqtIR (lvl .N30 i).ell (cbS i) eqB) s).M y = rd s.M y := by
  have hl : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have hp : 2 ^ (lvl .N30 i).ell ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl
  obtain ⟨c1, c2⟩ := cbS_le hi
  have eq : eqB = 8421376 := rfl
  have hm : memX = 67108864 := rfl
  obtain ⟨-, h2, h3⟩ := eqtIR_sem I s hM (ℓ := (lvl .N30 i).ell) (cb := cbS i) (eb := eqB)
    (S := fun v => rdK s.M (cbS i + 8 * v)) (by omega) c1 (by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (.inl c2) (fun _ _ => rfl)
  exact ⟨h3, fun y hy hy2 => h2 y hy (hy2.imp_right fun h => le_trans (by omega) h)⟩

/-- The message step of levels `0 … 3`. -/
def lvMsg (i : ℕ) : XIR := msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) obL xbM ybM

/-- The message step of level 4: π's final field. -/
def msg4 : XIR := msgTIR 10 32 finW xbM ybM

/-- `MsgOk` for level 4 from every state of the same size (`msgOk_four`). -/
theorem msg4_keep (c : Digest) (π : Proof) (L es : Log) (hs : π.size = piSize)
    (hfin : ∀ x < 32, finalAt es x = finPi π x) (s : St) (hsz : memX ≤ s.M.size) :
    ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      MsgOk (tp c π L) msg4 s' (lvl .N30 4).logN (mLog .N30 4) (nextMsg .N30 L es 4) :=
  fun s' _ hz => msgOk_four c π L es hs hfin s' (hz ▸ hsz)

/-- `MsgOk` for level `i < 4` from every state that agrees below `2^24`, outside the `eq` table,
with one holding level `i + 1`'s decoded rows at `obL` (`msgOk_lower`). -/
theorem lvMsg_keep {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St)
    (hsz : memX ≤ s.M.size)
    (hdec : ∀ r < (lvl .N30 (i + 1)).rows, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s.M (obL + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x)
    (hF : ∀ r x, msgOf .N30 L es (i + 1) r x = algebraMap F K (msgOf .N30 L es (i + 1) r x).f₀) :
    ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < 2 ^ 24 → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk I (lvMsg i) s' (lvl .N30 i).logN (mLog .N30 i) (nextMsg .N30 L es i) := by
  intro s' _ hz hag
  have hR : (lvl .N30 (i + 1)).rows = 16 := by interval_cases i <;> rfl
  have hm : mLog .N30 (i + 1) ≤ 14 := by interval_cases i <;> decide
  have hk : 2 ^ mLog .N30 (i + 1) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) hm
  have eob : obL = 6291456 := rfl
  have eqb : eqB = 8421376 := rfl
  refine msgOk_lower hi I s' (hz ▸ hsz) (fun r hr x hx => ?_) hF
  rw [← hdec r (hR ▸ hr) x hx]
  have : 2 * 2 ^ mLog .N30 (i + 1) * r ≤ 2 * 2 ^ 14 * 16 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) hr.le
  congr 1
  exact rdF_eq (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))
    (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))

/-! ## One step of levels 1–4: the read, then the decode -/

/-- **Read and decode level `i`** (`1 ≤ i ≤ 4`): the word to `stB`, the rows to `obL`. -/
def stepU (msg : XIR) (i : ℕ) : XIR := .seq (readLv i) (decLvIR msg i 32 stB (cbS i) obL)

/-- The heap the chained decode keeps: below `jb0` (the basis table), the chain's region
`[chB, eqB)`, and from `2^25` on (level 0's word, the index). -/
def KeepR (y : ℕ) : Prop := y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨ 2 ^ 25 ≤ y

/-- **One step of levels 1–4**: from a state `s` that agrees with `s₀` on `KeepR`, where `s₀`
holds the basis table, the chain's answers and the sorted index, `stepU msg i` leaves level `i`'s
decoded rows `msgOf i` at `obL` and keeps `KeepR`. -/
theorem lvStep_sem (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s₀ s : St)
    (hM : Inv s.M) (hsz : memX ≤ s.M.size)
    (hK : ∀ y, regs ≤ y → KeepR y → rd s.M y = rd s₀.M y)
    (hXs : ∀ a < L.length, rd s₀.M (memX + a) = Xi a)
    (hT : ∀ v < 20, ∀ i < 20, rdF s₀.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {es : Log}
    (hans : ∀ p < nRep, ∀ m < 4, rd s₀.M (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0)
    {i : ℕ} {msg : XIR} (hi1 : 1 ≤ i) (hi : i ≤ 4) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hcap : ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hmsg : ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < 2 ^ 24 → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk (tp c π L) msg s' (lvl .N30 i).logN (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR (tp c π L) (stepU msg i) s).M
        (obL + 2 * 2 ^ mLog .N30 i * r + 2 * x)) = msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → KeepR y → rd (semXIR (tp c π L) (stepU msg i) s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) (stepU msg i) s).M := by
  set I := tp c π L
  have hm : memX = 67108864 := rfl
  have ejb : jb0 = 2097152 := rfl
  have ech : chB = 8388608 := rfl
  have eqb : eqB = 8421376 := rfl
  have est : stB = 16777216 := rfl
  have eans : ansB = 8392704 := rfl
  have et : tb0 = 1048576 := rfl
  have hXs' : ∀ a < L.length, rd s.M (memX + a) = Xi a := fun a ha =>
    (hK _ (by simp only [regs]; omega) (.inr (.inr (by omega)))).trans (hXs a ha)
  have hW := readLv_wordOf hD hX s hM hXs' hsz hi1 hi hcap
  have fr := readLv_frame hD hX s hM hXs' hsz hi1 hi
  have hM1 := inv_sem I (wf_readLv i) hM
  have z1 := size_sem I (readLv i) s
  have hnp : 2 ^ logNL i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by unfold logNL; omega)
  rw [stepU, semXIR_seq]
  generalize semXIR I (readLv i) s = s1 at hW fr hM1 z1
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq ((fr _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (hK _ (by simp only [regs]; omega) (.inl (by omega))))
        ((fr _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (hK _ (by simp only [regs]; omega) (.inl (by omega))))
  have hS1 : ∀ v < (lvl .N30 i).ell, rdK s1.M (cbS i + 8 * v) = sAt es i v := by
    refine sAt_words fun v hv m hm4 => ?_
    have hp := p1_lt_nRep (by omega : i < 5) hv
    have hp' : phStart (26 + 5 * i) + 2 * v + 1 < 442 := hp
    rw [(fr _ (by simp only [regs]; omega) (.inl (by omega))).trans
      (hK _ (by simp only [regs]; omega) (.inr (.inl ⟨by omega, by omega⟩))), hans _ hp m hm4]
  obtain ⟨e1, e2⟩ := eqt_keep I s1 hM1 (by rw [z1]; exact hsz) (i := i) (by omega)
  have hmsg1 := hmsg _ e1 (by rw [size_sem, z1]) fun y hy h24 hq =>
    (e2 y hy hq).trans (fr y hy (.inl (by omega)))
  obtain ⟨b1, b2, b3⟩ := decLvU_sem I s1 hM1 hi1 hi hfar hA (by rw [z1]; exact hsz) hT1 hW hS1 hmsg1
  refine ⟨b1, fun y hy hy2 => ?_, b3⟩
  have hy3 : y < stB ∨ stB + 32 * 2 ^ logNL i ≤ y := by
    rcases hy2 with h | h | h
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr (by omega)
  refine (b2 y hy ?_).trans (fr y hy hy3)
  rcases hy2 with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (by omega))

/-- **Level 0's decode** (`decLv0_sem`) from a state agreeing with `s₀` on `KeepR`. -/
theorem lv0Step_sem (I : Array Word) (s₀ s : St) (hM : Inv s.M) (hsz : memX ≤ s.M.size)
    (hK : ∀ y, regs ≤ y → KeepR y → rd s.M y = rd s₀.M y)
    (hT : ∀ v < 20, ∀ i < 20, rdF s₀.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {L es : Log}
    (hans : ∀ p < nRep, ∀ m < 4, rd s₀.M (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s₀.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩)
    {msg : XIR} (hfar : ¬ farL .N30 L es 0)
    (hA : consSet .N30 L es 0 = jointAgree (wordK .N30 L es 0) (decodeL .N30 L es 0))
    (hmsg : ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < 2 ^ 24 → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk I msg s' (lvl .N30 0).logN (mLog .N30 0) (nextMsg .N30 L es 0)) :
    (∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M
        (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) = msgOf .N30 L es 0 r x) ∧
    Inv (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M := by
  have ejb : jb0 = 2097152 := rfl
  have ech : chB = 8388608 := rfl
  have eqb : eqB = 8421376 := rfl
  have eans : ansB = 8392704 := rfl
  have et : tb0 = 1048576 := rfl
  have ecb : colBase = 33554432 := rfl
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (hK _ (by simp only [regs]; omega) (.inl (by omega)))
        (hK _ (by simp only [regs]; omega) (.inl (by omega)))
  have hS1 : ∀ v < (lvl .N30 0).ell, rdK s.M (cbS 0 + 8 * v) = sAt es 0 v := by
    refine sAt_words fun v hv m hm4 => ?_
    have hp := p1_lt_nRep (by norm_num : 0 < 5) hv
    have hp' : phStart (26 + 5 * 0) + 2 * v + 1 < 442 := hp
    rw [hK _ (by simp only [regs]; omega) (.inr (.inl ⟨by omega, by omega⟩)), hans _ hp m hm4]
  have hW1 : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    exact rdF_eq (hK _ (by simp only [regs]; omega) (.inr (.inr (by omega))))
      (hK _ (by simp only [regs]; omega) (.inr (.inr (by omega))))
  obtain ⟨e1, e2⟩ := eqt_keep I s hM hsz (i := 0) (by norm_num)
  have hmsg1 := hmsg _ e1 (by rw [size_sem]) fun y hy _ hq => e2 y hy hq
  obtain ⟨b1, -, b3⟩ := decLv0_sem I s hM hfar hA hsz hT1 hW1 hS1 hmsg1
  exact ⟨b1, b3⟩

/-! ## The five levels -/

theorem le_add3 (a b c : ℕ) : a ≤ a + b + c := by omega
theorem le_add4 (a b c d : ℕ) : a ≤ a + b + c + d := by omega


/-- **The decode of the five levels**: the basis table, then levels 4, 3, 2, 1 (read and decode),
then level 0 (its word read by `read0` at `colBase`), into `ob0`. -/
def decLevels : XIR :=
  .seq (wtabIR tb0) (.seq (stepU msg4 4) (.seq (stepU (lvMsg 3) 3) (.seq (stepU (lvMsg 2) 2)
    (.seq (stepU (lvMsg 1) 1) (decLvIR (lvMsg 0) 0 128 colBase (cbS 0) ob0)))))

/-- **The five levels decode** (BLUEPRINT §6.2 step 4, §6.5 `interp_spec`/`coeffs_spec`): on a
domain tape with the sorted index at `memX`, level 0's word at `colBase` (`read_spec_F`), the
chain's answers at `ansB` (`chain_dec`), and, as the log's transcript `es` provides them, the cap
link `capDig es i = capPiL i π` (levels 1–4), the final-message link `finalAt es = finPi π`, and
at every level a close word with `A_c = jointAgree`: level 0's decoded rows sit at `ob0` as the
`F` values of `msgOf 0` (`f⁽⁰⁾`, row `r` at `ob0 + 2^18 r`). -/
theorem decLevels_sem (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hsz : memX ≤ s.M.size) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a)
    {es : Log}
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩)
    (hans : ∀ p < nRep, ∀ m < 4, rd s.M (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i)) :
    (∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR (tp c π L) decLevels s).M (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) =
        msgOf .N30 L es 0 r x) ∧
    Inv (semXIR (tp c π L) decLevels s).M := by
  set I := tp c π L
  -- the basis table
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM (tb := tb0) (by decide) (by decide)
    (le_trans (by decide) hsz)
  rw [decLevels, semXIR_seq]
  generalize semXIR I (wtabIR tb0) s = s₀ at t1 t2 t3 t4
  have hsz0 : memX ≤ s₀.M.size := t4 ▸ hsz
  have hXs0 : ∀ a < L.length, rd s₀.M (memX + a) = Xi a := fun a ha =>
    (t2 _ (le_trans (by decide) (Nat.le_add_right _ _))
      (.inr (le_trans (by decide) (Nat.le_add_right _ _)))).trans (hXs a ha)
  have hans0 : ∀ p < nRep, ∀ m < 4, rd s₀.M (ansB + 4 * p + m) =
      (packBytes (ansAt es p).toList).getD m 0 := fun p hp m hm4 => by
    rw [t2 _ (le_trans (by decide) (le_add3 _ _ _))
      (.inr (le_trans (by decide) (le_add3 _ _ _))), hans p hp m hm4]
  have hW0 : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s₀.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    exact rdF_eq (t2 _ (le_trans (by decide) (le_add3 _ _ _))
        (.inr (le_trans (by decide) (le_add3 _ _ _))))
      (t2 _ (le_trans (by decide) (le_add4 _ _ _ _)) (.inr (le_trans (by decide) (le_add4 _ _ _ _))))
  have hF : ∀ i < 5, ∀ r x, msgOf .N30 L es i r x = algebraMap F K (msgOf .N30 L es i r x).f₀ :=
    fun i hi => msgOf_embed hi (hfar i hi) (hA i hi)
  -- level 4
  obtain ⟨a1, a2, a3⟩ := lvStep_sem hD hX s₀ s₀ t3 hsz0 (fun _ _ _ => rfl) hXs0 t1 hans0
    (i := 4) (msg := msg4) (by norm_num) le_rfl (hfar 4 (by norm_num)) (hA 4 (by norm_num))
    (hcap 4 (by norm_num) le_rfl) fun s' h1 h2 _ => msg4_keep c π L es hD.hs hfin s₀ hsz0 s' h1 h2
  rw [semXIR_seq]
  have z4 := size_sem I (stepU msg4 4) s₀
  generalize semXIR I (stepU msg4 4) s₀ = s4 at a1 a2 a3 z4
  -- level 3
  obtain ⟨b1, b2, b3⟩ := lvStep_sem hD hX s₀ s4 a3 (z4 ▸ hsz0) a2 hXs0 t1 hans0
    (i := 3) (msg := lvMsg 3) (by norm_num) (by norm_num) (hfar 3 (by norm_num))
    (hA 3 (by norm_num)) (hcap 3 (by norm_num) (by norm_num))
    (lvMsg_keep (i := 3) (by norm_num) I s4 (z4 ▸ hsz0) a1 (hF 4 (by norm_num)))
  rw [semXIR_seq]
  have z3 := size_sem I (stepU (lvMsg 3) 3) s4
  generalize semXIR I (stepU (lvMsg 3) 3) s4 = s3 at b1 b2 b3 z3
  have k3 : ∀ y, regs ≤ y → KeepR y → rd s3.M y = rd s₀.M y := fun y hy h =>
    (b2 y hy h).trans (a2 y hy h)
  -- level 2
  obtain ⟨c1, c2, c3⟩ := lvStep_sem hD hX s₀ s3 b3 (z3 ▸ z4 ▸ hsz0) k3 hXs0 t1 hans0
    (i := 2) (msg := lvMsg 2) (by norm_num) (by norm_num) (hfar 2 (by norm_num))
    (hA 2 (by norm_num)) (hcap 2 (by norm_num) (by norm_num))
    (lvMsg_keep (i := 2) (by norm_num) I s3 (z3 ▸ z4 ▸ hsz0) b1 (hF 3 (by norm_num)))
  rw [semXIR_seq]
  have z2 := size_sem I (stepU (lvMsg 2) 2) s3
  generalize semXIR I (stepU (lvMsg 2) 2) s3 = s2 at c1 c2 c3 z2
  have k2 : ∀ y, regs ≤ y → KeepR y → rd s2.M y = rd s₀.M y := fun y hy h =>
    (c2 y hy h).trans (k3 y hy h)
  -- level 1
  obtain ⟨d1, d2, d3⟩ := lvStep_sem hD hX s₀ s2 c3 (z2 ▸ z3 ▸ z4 ▸ hsz0) k2 hXs0 t1 hans0
    (i := 1) (msg := lvMsg 1) le_rfl (by norm_num) (hfar 1 (by norm_num))
    (hA 1 (by norm_num)) (hcap 1 le_rfl (by norm_num))
    (lvMsg_keep (i := 1) (by norm_num) I s2 (z2 ▸ z3 ▸ z4 ▸ hsz0) c1 (hF 2 (by norm_num)))
  rw [semXIR_seq]
  have z1 := size_sem I (stepU (lvMsg 1) 1) s2
  generalize semXIR I (stepU (lvMsg 1) 1) s2 = s1 at d1 d2 d3 z1
  have k1 : ∀ y, regs ≤ y → KeepR y → rd s1.M y = rd s₀.M y := fun y hy h =>
    (d2 y hy h).trans (k2 y hy h)
  -- level 0
  have hsz1 : memX ≤ s1.M.size := z1 ▸ z2 ▸ z3 ▸ z4 ▸ hsz0
  exact lv0Step_sem I s₀ s1 d3 hsz1 k1 t1 hans0 hW0 (hfar 0 (by norm_num)) (hA 0 (by norm_num))
    (lvMsg_keep (i := 0) (by norm_num) I s1 hsz1 d1 (hF 1 (by norm_num)))

/-! ## Well formed, no `loopT`, no output; the exact cost -/

theorem wf_setA (b : ℕ) : WF (setA b) := by simp [setA, WF, Prim.dst, rA0]
theorem noLoopT_setA (b : ℕ) : NoLoopT (setA b) := trivial
theorem outs_setA (b t : ℕ) : outs (setA b) t = 0 := rfl

theorem wf_decLvIR {msg : XIR} (h : WF msg) (i cs cb cbS ob : ℕ) :
    WF (decLvIR msg i cs cb cbS ob) :=
  ⟨⟨wf_eqtIR .., h, wf_setA _, wf_fwdIR .., wf_setA _, wf_fwdIR .., wf_flagIR ..⟩,
    wf_scanIR .., wf_baryIR .., wf_bfRowsIR ..⟩

theorem noLoopT_decLvIR {msg : XIR} (h : NoLoopT msg) (i cs cb cbS ob : ℕ) :
    NoLoopT (decLvIR msg i cs cb cbS ob) :=
  ⟨⟨noLoopT_eqtIR .., h, noLoopT_setA _, noLoopT_fwdIR .., noLoopT_setA _, noLoopT_fwdIR ..,
    noLoopT_flagIR ..⟩, noLoopT_scanIR .., noLoopT_baryIR .., noLoopT_bfRowsIR ..⟩

theorem outs_decLvIR {msg : XIR} {t : ℕ} (h : outs msg t = 0) (i cs cb cbS ob : ℕ) :
    outs (decLvIR msg i cs cb cbS ob) t = 0 := by
  simp only [decLvIR, decFrontIR, decBackIR, outs, h, outs_eqtIR, outs_setA, outs_fwdIR,
    outs_flagIR, outs_scanIR, outs_baryIR, outs_bfRowsIR]

/-- **The cost of one level** (exact): the message step's, plus the `eq` table, two forward
transforms, the flags, the scan, the interpolation and the row butterflies, plus 11 for the
sequencing and the two `setA`. -/
theorem cost_decLvIR (msg : XIR) {i : ℕ} (hi : i < 5) (cs cb cbS ob t : ℕ) :
    cost (decLvIR msg i cs cb cbS ob) t = cost msg t +
      (12 + 2 ^ (lvl .N30 i).ell * (63 + (lvl .N30 i).ell * 271)) +
      2 * (14 + (lvl .N30 i).logN * (741 * 2 ^ ((lvl .N30 i).logN - 1) + 27)) +
      (12 + 2 ^ (lvl .N30 i).logN * (92 + 156 * (lvl .N30 i).rows)) +
      (16 + 2 ^ (lvl .N30 i).logN * 32) +
      (38 + 2 ^ mLog .N30 i * 2487 + 2 ^ mLog .N30 i * (lvl .N30 i).rows * 108 +
        (2 ^ mLog .N30 i) ^ 2 * 1363 + (2 ^ mLog .N30 i) ^ 2 * (lvl .N30 i).rows * 106) +
      (1 + (lvl .N30 i).rows * (17 + mLog .N30 i * (741 * 2 ^ (mLog .N30 i - 1) + 23))) + 11 := by
  have hl : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have hn : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hm : mLog .N30 i ≤ 17 := by interval_cases i <;> decide
  have hR : (lvl .N30 i).rows ≤ 64 := by interval_cases i <;> decide
  have p1 : 2 ^ (lvl .N30 i).ell < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p2 : 2 ^ ((lvl .N30 i).logN - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p3 : 2 ^ (lvl .N30 i).logN < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p4 : 2 ^ mLog .N30 i < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p5 : 2 ^ (mLog .N30 i - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [decLvIR, decFrontIR, decBackIR, cost, cost, cost, cost, cost, cost, cost, cost, cost,
    cost_eqtIR _ _ _ _ p1 (by omega), cost_fwdIR _ _ _ p2 (by omega),
    cost_flagIR _ _ _ _ _ _ _ _ _ p3 (by omega), cost_scanIR _ _ _ _ _ p3,
    cost_baryIR _ _ _ _ _ _ _ _ _ _ _ p4 (by omega), cost_bfRowsIR _ _ _ _ p5 (by omega)]
  simp only [setA, cost, blkSteps, List.length_cons, List.length_nil, ite_self]
  ring

/-- The message steps' costs. -/
theorem cost_msg4 (t : ℕ) : cost msg4 t = 38446 := by
  rw [msg4, cost_msgTIR _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num

theorem cost_lvMsg {i : ℕ} (hi : i < 4) (t : ℕ) :
    cost (lvMsg i) t = 46 + 36 * 2 ^ (lvl .N30 i).logN + 560 * 2 ^ mLog .N30 (i + 1) := by
  have hn : 2 * 2 ^ (lvl .N30 i).logN < 2 ^ 64 := by interval_cases i <;> decide
  have hk : 8 * 2 ^ mLog .N30 (i + 1) < 2 ^ 64 := by interval_cases i <;> decide
  rw [lvMsg, cost_msgHIR _ _ _ _ _ _ hn hk]

/-- **The five levels' exact costs** (`≈ 2^47.0` in all; level 0's interpolation dominates). -/
theorem cost_levels (t : ℕ) :
    cost (decLvIR msg4 4 32 stB (cbS 4) obL) t = 14546064 ∧
    cost (decLvIR (lvMsg 3) 3 32 stB (cbS 3) obL) t = 261035116 ∧
    cost (decLvIR (lvMsg 2) 2 32 stB (cbS 2) obL) t = 13186204712 ∧
    cost (decLvIR (lvMsg 1) 1 32 stB (cbS 1) obL) t = 823525089508 ∧
    cost (decLvIR (lvMsg 0) 0 128 colBase (cbS 0) ob0) t = 140024626811056 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cost_decLvIR _ (by norm_num), cost_msg4]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl

theorem wf_lvMsg (i : ℕ) : WF (lvMsg i) := wf_msgHIR ..
theorem noLoopT_lvMsg (i : ℕ) : NoLoopT (lvMsg i) := noLoopT_msgHIR ..
theorem outs_lvMsg (i t : ℕ) : outs (lvMsg i) t = 0 := outs_msgHIR ..

theorem wf_decLevels : WF decLevels :=
  ⟨wf_wtabIR _, ⟨wf_readLv _, wf_decLvIR (wf_msgTIR ..) ..⟩, ⟨wf_readLv _, wf_decLvIR (wf_lvMsg _) ..⟩,
    ⟨wf_readLv _, wf_decLvIR (wf_lvMsg _) ..⟩, ⟨wf_readLv _, wf_decLvIR (wf_lvMsg _) ..⟩,
    wf_decLvIR (wf_lvMsg _) ..⟩

theorem noLoopT_decLevels : NoLoopT decLevels :=
  ⟨noLoopT_wtabIR _, ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_msgTIR ..) ..⟩,
    ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩,
    ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩,
    ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩,
    noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩

theorem outs_decLevels (t : ℕ) : outs decLevels t = 0 := by
  simp only [decLevels, stepU, msg4, outs, outs_wtabIR, outs_readLv,
    outs_decLvIR (outs_msgTIR _ _ _ _ _ t), outs_decLvIR (outs_lvMsg _ t)]

/-- **The decode's exact cost**: the basis table (79,606), the four reads (`cost_readLv`), the
five levels (`cost_levels`) and 9 for the sequencing: `140,866,457,335,279 ≈ 2^47.0`. -/
theorem cost_decLevels (t : ℕ) : cost decLevels t = 140866457335279 := by
  obtain ⟨r1, r2, r3, r4⟩ := cost_readLv t
  obtain ⟨l4, l3, l2, l1, l0⟩ := cost_levels t
  simp only [decLevels, stepU, cost, cost_wtabIR, r1, r2, r3, r4, l4, l3, l2, l1, l0]

theorem sizeIR_decLevels : sizeIR decLevels = 53515 := by decide +kernel

/-! ## The node branch: index, level 0's read, the chain, the five levels -/

/-- **The node branch** (BLUEPRINT §6.2 steps 2–4): the log index and level 0's read
(`decRead`), the Fiat–Shamir replay (`chainIR`, answers at `ansB`), then the five levels
(`decLevels`). The chain runs after the read: its frame keeps the index and the column store. -/
def decNode : XIR := .seq decRead (.seq (chainIR nRep chTab seedIR) decLevels)

/-- **The SNARK branch**: a node runs `decNode`, a leaf outputs its witness. -/
def decLN3 : XIR := .seq kindIR (.ite rKN decNode leafIR)

theorem cost_decNode (t : ℕ) : cost decNode t = cost decN t + cost decLevels t + 1 := by
  simp only [decNode, decN, cost]; omega

theorem outs_decNode (t : ℕ) : outs decNode t = 0 := by
  have h1 : outs decRead t = 0 := by simp [decRead, outs, outs_logIR, outs_readIR, read0]
  rw [decNode, outs, outs, h1, outs_chainIR nRep t chTab (sd := seedIR) (outs_sdList t _),
    outs_decLevels]

theorem decOk_decLN3 : DecOk decLN3 where
  wf := ⟨by simp [kindIR, readAt, WF, Prim.dst, rB, rK2, rKN, rKL, rA],
    ⟨decOk_decRead.wf, wf_chainIR nRep chTab (wf_sdList _) (noWrite_seedIR (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)), wf_decLevels⟩,
    by simp [leafIR, outAt, readAt, WF, Prim.dst, rK2, rV2, rA]⟩
  safe := fun c π L hs hq ht => .seq (safe_of_noLoopT noLoopT_leaf.1)
    (.ite (.seq (decOk_decRead.safe c π L hs hq ht)
      (.seq (safe_chainIR c π L hs hq ht nRep chTab (noLoopT_sdList _) (wf_sdList _)
        (noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
        (safe_of_noLoopT noLoopT_decLevels))) (safe_of_noLoopT noLoopT_leaf.2))
  cost := fun t => by
    have h := cost_decN t
    have e : cost leafIR t = 32 := by simp [leafIR, outAt, readAt, cost, blkSteps]
    have e2 : cost kindIR t = 15 := by simp [kindIR, readAt, cost, blkSteps]
    have h2 : decBudget t = 211106098315264 + 8176 * t := by
      simp only [decBudget, fuelBase, fuelPerWord]; norm_num
    rw [h2, decLN3, cost, cost, e, e2, cost_decNode, cost_decLevels]
    omega
  outs := fun t => by
    simp [decLN3, kindIR, leafIR, outAt, readAt, outs, outs_decNode, outCap]
  size := by
    have := sizeIR_decN
    have e : sizeIR leafIR = 35 := by simp [leafIR, outAt, readAt, sizeIR, blkSteps]
    have e2 : sizeIR kindIR = 15 := by simp [kindIR, readAt, sizeIR, blkSteps]
    have e3 : sizeIR decNode = sizeIR decN + 53515 + 1 := by
      rw [decNode, decN, sizeIR, sizeIR, sizeIR, sizeIR_decLevels]
      generalize sizeIR decRead = a
      generalize sizeIR (chainIR nRep chTab seedIR) = b
      omega
    rw [decLN3, sizeIR, sizeIR, e, e2, e3]
    generalize sizeIR decN = a at this ⊢
    omega

/-- **The SNARK branch's cost within its fuel** (F): `cost decLN3 t ≤ 211,106,098,315,264 +
8,176 t` (`fuel_base − 2^27`, `fuel_per_word − 16`), with the decode at
`140,866,457,335,279 ≈ 2^47.0` and `≈ 7.0·10^13 ≈ 2^46.0` left for the output. -/
theorem cost_le_decLN3 (t : ℕ) : cost decLN3 t ≤ 211106098315264 + 8176 * t := by
  have h := decOk_decLN3.cost t
  simp only [decBudget, fuelBase, fuelPerWord] at h
  omega

/-! ## The node branch decodes `f⁽⁰⁾` -/

/-- **The chain keeps the heap** outside `[chB, chEnd)` (`chainIR_sem` for the seed block). -/
theorem chain_frame (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (st₀ : Digest) (s : St)
    (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    ∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (tp c π L) (chainIR nRep chTab seedIR) s).M y = rd s.M y := by
  have h119 : (fsQ (vkOf π) c π 0 st₀).size = 119 := by
    have hp' : π.size = 797904 := hD.hs.trans piSize_eq
    unfold fsQ
    rw [fsMsgs_ctl.1]
    simp only [if_true]
    rw [seedQ, ByteArray.size_append, extract_size π (by omega),
      show (bytesOf (tagSeed ++ (vkOf π).toList ++ c.toList)).size = 71 by
        simp [bytesOf, ByteArray.size, tagSeed]]
  exact (chainIR_sem c π L hD.hs hD.hq hD.ht (N := nRep) (by decide)
    (tabW_chTab (vkOf π) c π L hD.hs) (seedOK_seedIR c π L hD.hs st₀) h119 s hM hsz).2.2

/-- Level 0's committed word is π's column store when π's cap is the log's (`capDig es 0 =
capPi π`, the absorb of `cap₀`). -/
theorem wordOf0_eq {L es : Log} {π : Proof} (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (j : ℕ) (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows) :
    wordOf .N30 L es 0 r ⟨j, hj⟩ = ((colL (frEnc 0) L (capPi π (j / 2 ^ 9)) 9 j).map
      fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := by
  have hj' : j < 2 ^ 18 := hj
  have hq : j / 2 ^ 9 < 2 ^ 9 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  simp only [wordOf, colOf, show (lvl .N30 0).sib = 9 from rfl, hcap0 _ hq]
  rfl

/-- **The node branch decodes `f⁽⁰⁾`** (BLUEPRINT §6.2 steps 2–4, §6.5 up to `output_spec`): on a
domain tape of a node proof whose log has no state hit, if the log's transcript `es` is the
first-match chain the replay reads (`fmAns … = ansAt es`, the chain link of `runLog`) and its
absorbs are π's fields (the caps `capDig es i`, the final message `finalAt es`), and the word of
every level is close with `A_c = jointAgree` (what `final` hands over), then after `decNode` the
heap at `ob0 + 2^18 r + 2x` holds, as an `F` value, coefficient `x` of row `r` of `f⁽⁰⁾`
(`msgOf .N30 L es 0`). -/
theorem decNode_sem (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (hS : ¬ StateHit L)
    (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep, fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (s : St) (hM : Inv s.M) (hsz : memX + L.length + L.length ≤ s.M.size) :
    ∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR (tp c π L) decNode s).M (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) =
        msgOf .N30 L es 0 r x := by
  have hm : memX = 67108864 := rfl
  have ech : chEnd = 8394752 := rfl
  have ecb : colBase = 33554432 := rfl
  -- the index and level 0's read
  have hWF : ∀ q < 2 ^ 18, ∀ r < 64,
      rdF (semXIR (tp c π L) read0 (semXIR (tp c π L) idxIR s)).M (colBase + 128 * q + 2 * r) =
        ((colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q).map
          fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := fun q hq r hr => by
    have := read_spec_F c π L hD s hM hsz hq hr
    rwa [semXIR_seq] at this
  obtain ⟨r1, r2, r3⟩ := idxIR_sorted c π L hD.hs hD.hq hD.ht s hM hsz
  have hM1 : Inv (semXIR (tp c π L) idxIR s).M := inv_sem _ wf_logIR hM
  have z1 := size_sem (tp c π L) idxIR s
  rw [decNode, semXIR_seq, semXIR_seq, show decRead = .seq idxIR read0 from rfl, semXIR_seq]
  generalize semXIR (tp c π L) idxIR s = s1 at r1 r2 r3 hM1 z1 hWF
  have hX : Sorted (tp c π L) L (fun a => rd s1.M (memX + a)) := ⟨r1, r2, r3⟩
  have hsz1 : memX ≤ s1.M.size := by rw [z1]; exact le_trans (by omega) hsz
  have d2 : ∀ a < L.length, rd (semXIR (tp c π L) read0 s1).M (memX + a) = rd s1.M (memX + a) :=
    (readIR_sem hD (Xi := fun a => rd s1.M (memX + a)) hX s1 hM1 (fun _ _ => rfl)
    (i := 0) (cw := capW0) (nw := 128) (ncap := 512) (sb := colBase) (cap := capPi π) (sib := 9)
    (np := 2 ^ 18)
    (by rw [capW0_eq]; norm_num)
    (fun e he m hm => by simp only [tp, getD_toArray]; exact tape_cap c π L hD.hs he hm)
    (by norm_num) (by norm_num) (by norm_num) (by simp only [colBase, memX]; norm_num)
    (by simp only [regs, colBase]; norm_num) (by norm_num) hsz1).2.1
  have hM2 : Inv (semXIR (tp c π L) read0 s1).M := inv_sem _ (wf_readIR ..) hM1
  have z2 := size_sem (tp c π L) read0 s1
  generalize semXIR (tp c π L) read0 s1 = s2 at d2 hM2 z2 hWF
  have hsz2 : memX ≤ s2.M.size := z2 ▸ hsz1
  -- the chain
  have hans : ∀ p < nRep, ∀ m < 4, rd (semXIR (tp c π L) (chainIR nRep chTab seedIR) s2).M
      (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0 := fun p hp m hm4 =>
    chain_dec c π L hD.hs hD.hq hD.ht hS st₀ s2 hM2 (le_trans (by decide) hsz2) hp (hfm p hp) hm4
  have cf := chain_frame c π L hD st₀ s2 hM2 (le_trans (by decide) hsz2)
  have hM3 : Inv (semXIR (tp c π L) (chainIR nRep chTab seedIR) s2).M := inv_sem _
    (wf_chainIR nRep chTab (wf_sdList _) (noWrite_seedIR (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))) hM2
  have z3 := size_sem (tp c π L) (chainIR nRep chTab seedIR) s2
  generalize semXIR (tp c π L) (chainIR nRep chTab seedIR) s2 = s3 at hans cf hM3 z3
  have hXs3 : ∀ a < L.length, rd s3.M (memX + a) = rd s1.M (memX + a) := fun a ha =>
    (cf _ (le_trans (by decide) (Nat.le_add_right _ _))
      (.inr (le_trans (by decide) (Nat.le_add_right _ _)))).trans (d2 a ha)
  have hW3 : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s3.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩ := fun j hj r => by
    have hR : (lvl .N30 0).rows = 64 := rfl
    have hj' : j < 2 ^ 18 := hj
    rw [wordOf0_eq hcap0, ← hWF j hj' r (hR ▸ r.2)]
    exact rdF_eq (cf _ (le_trans (by decide) (le_add3 _ _ _))
        (.inr (le_trans (by decide) (le_add3 _ _ _))))
      (cf _ (le_trans (by decide) (le_add4 _ _ _ _)) (.inr (le_trans (by decide) (le_add4 _ _ _ _))))
  exact (decLevels_sem hD hX s3 hM3 (z3 ▸ hsz2) hXs3 hW3 hans hcap hfin hfar hA).1

/-! ## Controls -/

namespace NodeControls

open FlagControls

/-- Output the words at `as` (scratch registers `210`, `211`). -/
def outWords : List ℕ → XIR
  | [] => .blk []
  | a :: as => .seq (.blk [.const 210 (toWord a)]) (.seq (.load 211 210) (.seq (.out 211) (outWords as)))

/-- `finIR` on a toy tape: one K element from tape words `tw … tw + 3`, then `X[0]`, `Y[0]`. -/
def toyFin (tw : ℕ) : XIR := .seq (finIR 1 tw 260 270) (outWords [260, 261, 270, 271])

/-- **`finIR` reads at `tw`** (positive) **and nowhere else** (negative: from `tw = 1` the element
is shifted by a word): on the tape `[0, 0, 7, 8, 9, 10]`, `f₀ = (7, 8)` to `X`, `f₁ = (9, 10)` to
`Y`. -/
theorem toyFin_run : (toProg 300 0 (toyFin 2)).run [0, 0, 7, 8, 9, 10] 400 = some [7, 8, 9, 10] ∧
    (toProg 300 0 (toyFin 1)).run [0, 0, 7, 8, 9, 10] 400 = some [0, 7, 8, 9] := by
  decide +kernel

/-- `gathIR` on toy rows: 16 rows of one column at `256 + 2r` (row `r`'s word 0 is `r + 1`),
the first two K elements of `X`, `Y`. -/
def toyGath : XIR :=
  .seq (putWords ((List.range 16).flatMap fun r => [toWord (r + 1), 0]) 0)
    (.seq (gathIR 1 256 300 340) (outWords [300, 340, 302, 342]))

/-- **`gathIR` pairs rows `2x`, `2x + 1`** (positive: `X[x]` is row `2x`, `Y[x]` row `2x + 1`;
negative: row 1 goes to `Y[0]`, not to `X[1]`, whose word is row 2's `3`). -/
theorem toyGath_run : (toProg 400 0 toyGath).run [] 2000 = some [1, 2, 3, 4] := by
  decide +kernel

/-- **`MsgOk` is not trivial** (negative): the empty step does not lay out a nonzero message
over a zero `X` row. -/
theorem msgOk_empty_neg (I : Array Word) (s : St) (hM : Inv s.M) (h0 : rdF s.M xbM = 0) :
    ¬ MsgOk I (.blk []) s 0 0 (fun _ => 1) := by
  intro h
  have := ((h s hM rfl fun _ _ _ => rfl).1 0 (by norm_num)).1
  rw [if_pos (by norm_num), Nat.mul_zero, Nat.add_zero] at this
  have e : semXIR I (.blk []) s = s := rfl
  rw [e, h0] at this
  exact absurd this (by decide)

/-- A toy proof: `b` zero bytes, then the byte `1`. -/
def toyPi (b : ℕ) : Proof := ⟨(Array.replicate b 0).push 1⟩

/-- **`finPi` reads π's final field** (positive: a `1` at `finOff` is read, element `0` is
nonzero) **at `finOff`** (negative: a `1` at `finOff − 1` is not read). -/
theorem finPi_toy : finPi (toyPi finOff) 0 ≠ 0 ∧ finPi (toyPi (finOff - 1)) 0 = 0 := by
  decide +kernel

/-- **`KeepR`** holds on the basis table, the chain and level 0's word (positive), and not on the
decoded rows of levels 1–4 nor on level 0's rows (negative: the decode writes them). -/
theorem keepR_ctl : KeepR tb0 ∧ KeepR ansB ∧ KeepR colBase ∧ ¬ KeepR obL ∧ ¬ KeepR ob0 := by
  simp only [KeepR, tb0, jb0, ansB, chB, eqB, colBase, obL, ob0]; omega

end NodeControls

end FR.X
