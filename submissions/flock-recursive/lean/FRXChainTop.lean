-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 14: the fold challenges; stage S-H2,
-- track L-ext).
import FRXChainLoop

/-!
# The chain scan on the machine: the whole program

* `cnt_sem`: the store-free walk leaves the log's word count `wordsOf L` in `rCn5`, from every
  state (this is also `Safe`'s count bound).
* `storesIR_sem`: the table's words land at `chB …`.
* **`chainIR_sem`**: on a domain tape of a SNARK proof, given a table `tab` that realises the
  targets (`TabW`) and a seed block `sd` that writes the seed's 15 words into `H` (`SeedOK`), the
  answers left at `ansB + 4q` are the forward scan's (`scanC`).
-/

namespace FR.X

open RecursionFast

/-! ## The count -/

theorem sub_toWord' {a b : ℕ} (hb : b ≤ a) (ha : a - b < 2 ^ 64) :
    XOp.sub.eval (toWord a) (toWord b) = toWord (a - b) := by
  rw [show a = (a - b) + b by omega, ← add_toWord, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem cntBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : rd s.M rP = toWord p)
    (hp2 : p < 2 ^ 64) :
    rd (semXIR I cntBody s).M rP = toWord (p + 5 + (ceil8 (I.getD p 0)).toNat) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [cntBody, semXIR, ceil8Ps, runPrims, List.foldl, List.cons_append, List.nil_append,
    Prim.run, rP, rQL, rT1, rT2, rKc] at hp ⊢
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne,
    XOp.eval, hp, toNat_toWord hp2]
  change toWord p + ceil8 (I[p]?.getD 0#64) + 5#64 = toWord (p + 5 + (ceil8 (I[p]?.getD 0#64)).toNat)
  generalize ceil8 (I[p]?.getD 0#64) = C
  have := C.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [toWord, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem wf_cntBody : WF cntBody := by
  simp +decide only [cntBody, ceil8Ps, WF, Prim.dst, rP, rQL, rT1, rT2, rKc, and_true,
    List.cons_append, List.nil_append]

theorem cntLoop (I : Array Word) (n : ℕ) (pos : ℕ → ℕ)
    (hpos : ∀ j < n, pos j < 2 ^ 64 ∧ pos (j + 1) = pos j + 5 + (ceil8 (I.getD (pos j) 0)).toNat) :
    ∀ (m j : ℕ) (s : St), j + m = n → Inv s.M → rd s.M rP = toWord (pos j) →
      rd (iterL (semXIR I cntBody) rCW m s).M rP = toWord (pos n)
  | 0, j, s, hj, _, hp => by simp only [iterL]; rw [hp, show j = n by omega]
  | m + 1, j, s, hj, hM, hp => by
    simp only [iterL]
    have hM' : Inv (decS rCW (semXIR I cntBody s)).M := inv_of_frame
      (inv_sem I wf_cntBody hM) (size_decS ..) fun i hi => rd_decS (by simp only [rCW]; omega) _
    refine cntLoop I n pos hpos m (j + 1) _ (by omega) hM' ?_
    rw [rd_decS (by decide), cntBody_sem I s hM hp (hpos j (by omega)).1, (hpos j (by omega)).2]

/-- **The count**: from every state, on a domain tape of a SNARK proof, `(cntIR pL)` leaves the log's
word count in `rCn5`. -/
theorem cnt_sem {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) :
    rd (semXIR (extractorInput c π L).toArray (cntIR pL) s).M rCn5 = toWord (wordsOf L) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have hcnt : (I.getD pL 0).toNat = L.length := by
    rw [hI, getD_toArray, tape_getD_posL4 c π L hs, toNat_toWord (by
      have := length_logEntries L
      have h5 : 5 * L.length ≤ entryOff L L.length := by
        rwa [entries_length, ← entryOff_length] at this
      omega)]
  have hpos : ∀ j < L.length, pL + 1 + entryOff L j < 2 ^ 64 ∧
      pL + 1 + entryOff L (j + 1) = pL + 1 + entryOff L j + 5 +
        (ceil8 (I.getD (pL + 1 + entryOff L j) 0)).toNat := fun j hj => by
    have hq' := hq _ (List.getElem_mem hj)
    have hend' : entryOff L (j + 1) ≤ entryOff L L.length := by
      rw [entryOff_length]; exact entryOff_le_sum L (j + 1)
    rw [entryOff_succ L hj] at hend' ⊢
    rw [hI, getD_toArray, tape_entry4 c π L hs hj, toNat_ceil8 hq']
    simp only [qWords] at hend' ⊢
    omega
  have w0 : WF (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) := by
    simp +decide [readAt, WF, Prim.dst, rP, rN, rA, and_true]
  have hM1 := inv_sem I w0 hM
  have hs1 := hM1.1
  simp only [regs] at hs1
  have hn1 : rd (semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s).M rN =
      I.getD pL 0 :=
    rd_seq_readAt I _ s (by simp +decide [WF, Prim.dst, rP]) hM (by decide)
      (by omega)
  have hp1 : rd (semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s).M rP =
      toWord (pL + 1) := by
    have := hM.1; simp only [regs] at this
    simp only [readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
  rw [cntIR, semXIR_seq, semXIR_seq]
  generalize semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s = s1
    at hM1 hs1 hn1 hp1
  have hc : rCW < s1.M.size := by simp only [rCW]; omega
  have e : semXIR I (.loopT rCW rN ⟨0, 1, 5⟩ cntBody) s1 = iterL (semXIR I cntBody) rCW L.length
      ⟨entryT rCW rN s1.M, s1.o⟩ := by
    simp only [semXIR, rd_entryT hc, hn1, hcnt]
  rw [e]
  have hE : Inv (entryT rCW rN s1.M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; omega)
  have hEp : rd (entryT rCW rN s1.M) rP = toWord (pL + 1 + entryOff L 0) := by
    rw [entryT_frame _ (by decide), hp1]; rfl
  have hP := cntLoop I L.length (fun j => pL + 1 + entryOff L j) hpos L.length 0
    ⟨entryT rCW rN s1.M, s1.o⟩ (by omega) hE hEp
  have hM2 := iterL_inv (f := semXIR I cntBody) (c := rCW) (by decide)
    (fun s h => inv_sem I wf_cntBody h) L.length ⟨entryT rCW rN s1.M, s1.o⟩ hE
  generalize iterL (semXIR I cntBody) rCW L.length ⟨entryT rCW rN s1.M, s1.o⟩ = s2 at hP hM2
  have hs2 := hM2.1
  simp only [regs] at hs2
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [size_set, rCn5]; omega), rd_set_self (by simp only [rKd]; omega),
    rd_set_ne (by decide), hP, sub_toWord' (by omega) (by omega),
    show pL + 1 + entryOff L L.length - (pL + 1) = wordsOf L by
      rw [entryOff_length]; simp only [wordsOf]; omega]

/-- `(cntIR pL)` leaves the heap alone. -/
theorem cnt_heap (pL : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) {y : ℕ} (hy : regs ≤ y) :
    rd (semXIR I (cntIR pL) s).M y = rd s.M y := by
  have lo1 : Lo (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) := by
    simp +decide [Lo, readAt, Prim.dst, regs, rP, rN, rA, and_true]
  have lob : Lo cntBody := by simp +decide [Lo, cntBody, ceil8Ps, Prim.dst, regs, rP, rQL, rT1,
    rT2, rKc, and_true, List.cons_append, List.nil_append]
  have w1 : WF (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) := by
    simp +decide [readAt, WF, Prim.dst, rP, rN, rA, and_true]
  rw [cntIR, semXIR_seq, semXIR_seq]
  have hM1 := inv_sem I w1 hM
  have h1 := hframe I _ s lo1 y hy
  generalize semXIR I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) s = s1 at hM1 h1
  simp only [regs] at hy
  have hE : Inv (entryT rCW rN s1.M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; omega)
  have h2 := iterL_frame (f := semXIR I cntBody) (c := rCW) (i := y) (by decide)
    (by simp only [rCW]; omega) (fun s h => inv_sem I wf_cntBody h)
    (fun s _ => hframe I cntBody s lob y (by simp only [regs]; omega))
    (rd (entryT rCW rN s1.M) rCW).toNat ⟨entryT rCW rN s1.M, s1.o⟩ hE
  simp only [semXIR] at h2 ⊢
  rw [rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl) <;> simp only [Prim.dst, rKd, rCn5] <;> omega) _, h2,
    entryT_frame _ (by simp only [rCW]; omega), h1]

theorem cnt_regs (pL : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (hw : r ≠ rP ∧ r ≠ rN ∧ r ≠ rA ∧ r ≠ rCW ∧ r ≠ rQL ∧ r ≠ rT1 ∧ r ≠ rT2 ∧ r ≠ rKc ∧ r ≠ rKd ∧
      r ≠ rCn5) : rd (semXIR I (cntIR pL) s).M r = rd s.M r := by
  obtain ⟨a, b, c, d, e, f, g, k, l, m⟩ := hw
  refine frame I (cntIR pL) s (wf_cntIR pL) hM r hr ?_
  simp +decide [cntIR, cntBody, readAt, ceil8Ps, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, List.cons_append, List.nil_append]
  simp only [rP, rN, rA, rCW, rQL, rT1, rT2, rKc, rKd, rCn5] at *
  omega

/-! ## The table -/

theorem storesIR_sem (I : Array Word) : ∀ (ws : List Word) (b : ℕ) (s : St), Inv s.M →
    regs ≤ b → b + ws.length ≤ s.M.size → b + ws.length < 2 ^ 64 →
    (∀ i < ws.length, rd (semXIR I (storesIR b ws) s).M (b + i) = ws.getD i 0) ∧
    (∀ y, y ≠ cTmp → y ≠ rAd4 → y ≠ rKd → (y < b ∨ b + ws.length ≤ y) →
      rd (semXIR I (storesIR b ws) s).M y = rd s.M y) ∧
    Inv (semXIR I (storesIR b ws) s).M ∧ (semXIR I (storesIR b ws) s).M.size = s.M.size
  | [], b, s, hM, _, _, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl, hM,
      rfl⟩
  | w :: ws, b, s, hM, hb, hbs, hb2 => by
    have hs := hM.1
    simp only [regs] at hs hb
    simp only [List.length_cons] at hbs hb2
    have hM1 := inv_sem I (P := .blk [.const rAd4 (toWord b), .const rKd w])
      (by simp +decide only [WF, Prim.dst, rAd4, rKd, List.mem_cons, List.mem_nil_iff,
        forall_eq_or_imp, forall_eq, or_false, and_true]) hM
    have a1 : rd (semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s).M rAd4 = toWord b := by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by decide), rd_set_self (by simp only [rAd4]; omega)]
    have k1 : rd (semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s).M rKd = w := by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [size_set, rKd]; omega)]
    have f1 : ∀ y, y ≠ rAd4 → y ≠ rKd →
        rd (semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s).M y = rd s.M y :=
      fun y a b => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b⟩) _
    have z1 := size_sem I (.blk [.const rAd4 (toWord b), .const rKd w]) s
    rw [storesIR, semXIR_seq, semXIR_seq]
    generalize semXIR I (.blk [.const rAd4 (toWord b), .const rKd w]) s = s1 at hM1 a1 k1 f1 z1
    have e2 : semXIR I (.store rAd4 rKd) s1 = ⟨storeM s1.M rAd4 rKd, s1.o⟩ := rfl
    rw [e2]
    have st : ∀ i, i ≠ cTmp → rd (storeM s1.M rAd4 rKd) i = if i = b then w else rd s1.M i :=
      fun i hi => by
        rw [rd_storeM hM1 a1 (by simp only [regs]; omega) (by omega) (by omega) (by decide)
          (by decide) hi, k1]
    have hM2 := inv_sem I (P := .store rAd4 rKd) (by simp +decide only [WF, rAd4, cTmp]) hM1
    rw [e2] at hM2
    obtain ⟨r1, r2, r3, r4⟩ := storesIR_sem I ws (b + 1) ⟨storeM s1.M rAd4 rKd, s1.o⟩ hM2
      (by simp only [regs]; omega) (by simp only [size_storeM]; omega) (by omega)
    refine ⟨fun i hi => ?_, fun y a c d e => ?_, r3, by rw [r4]; simp only [size_storeM]; omega⟩
    · rcases i with _ | i
      · rw [show b + 0 = b from rfl, r2 b (by simp only [cTmp]; omega) (by simp only [rAd4]; omega)
          (by simp only [rKd]; omega) (.inl (by omega))]
        simp only
        rw [st _ (by simp only [cTmp]; omega), if_pos (by omega)]
        rfl
      · rw [show b + (i + 1) = b + 1 + i by omega, r1 i (by simp at hi; omega)]
        rfl
    · simp only [List.length_cons] at e
      rw [r2 y a c d (by omega)]
      simp only
      rw [st y a, if_neg (by omega), f1 y c d]

/-! ## The whole scan -/

/-- **The table words realise the targets** (the list form of `TabOK`). -/
def TabW (I : Array Word) (T : ℕ → Digest → ByteArray) (N : ℕ) (tab : List Word) : Prop :=
  tab.length = 4 * (N + 1) ∧ ∀ p, 0 < p → p ≤ N → (tab.getD (4 * p + 1) 0).toNat < 2 ^ 62 ∧
    (p < N → ∀ st : Digest, tab.getD (4 * p) 0 = toWord (T p st).size ∧ (T p st).size < 2 ^ 64 ∧
      ∀ j < ((T p st).size + 7) / 8, (packBytes (T p st).data.toList).getD j 0 =
        if j < 5 then (if j = 0 then tab.getD (4 * p + 2) 0 else (packBytes st.toList).getD (j - 1) 0)
        else I.getD ((tab.getD (4 * p + 1) 0).toNat + (j - 5)) 0)

/-- **The seed block** writes the seed's 15 packed words into `H`, keeps `rCn5` and the heap
outside `H`. -/
def SeedOK (sd : XIR) (I : Array Word) (Q : ByteArray) : Prop :=
  WF sd ∧ ¬ Writes sd rCC ∧ ∀ s : St, Inv s.M → chEnd ≤ s.M.size →
    (∀ j < 15, rd (semXIR I sd s).M (hB + j) = (packBytes Q.data.toList).getD j 0) ∧
    rd (semXIR I sd s).M rCn5 = rd s.M rCn5 ∧
    (∀ y, regs ≤ y → (y < hB ∨ hB + 16 ≤ y) → rd (semXIR I sd s).M y = rd s.M y)


theorem startPs_vals (pL : ℕ) (M : Mem) (hs : regs ≤ M.size) :
    rd (runPrims (startPs pL) M) rWp = toWord (pL + 1) ∧ rd (runPrims (startPs pL) M) rEo = 0 ∧
    rd (runPrims (startPs pL) M) rPi = toWord 0 ∧ rd (runPrims (startPs pL) M) rTl = toWord 119 ∧
    rd (runPrims (startPs pL) M) rTh = toWord 15 ∧ rd (runPrims (startPs pL) M) rTo = toWord 0 := by
  simp only [regs] at hs
  simp only [startPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption)) | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption)) only [rd_set_self, rd_set_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem startPs_frame (pL : ℕ) (M : Mem) {i : ℕ} (h : i ≠ rWp ∧ i ≠ rEo ∧ i ≠ rPi ∧ i ≠ rTl ∧ i ≠ rTh ∧
    i ≠ rTo ∧ i ≠ rMt) : rd (runPrims (startPs pL) M) i = rd M i := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  apply rd_runPrims_of_not_writes
  simp only [startPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;>
    first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c | exact Ne.symm d |
      exact Ne.symm e | exact Ne.symm f | exact Ne.symm g

/-- **The chain scan, end to end**: on a domain tape of a SNARK proof, with a table that realises
the targets and a seed block that writes the seed's words, the answers at `ansB + 4q` are the
forward scan's; the heap outside `[chB, chEnd)` is kept. -/
theorem chainIR_sem {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    {T : ℕ → Digest → ByteArray} {N : ℕ} (hN : N < 2 ^ 9) {tab : List Word} {sd : XIR}
    {st₀ : Digest} (hT : TabW (extractorInput c π L).toArray T N tab)
    (hsd : SeedOK sd (extractorInput c π L).toArray (T 0 st₀)) (h119 : (T 0 st₀).size = 119)
    (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (scanC T N st₀ L).1 ≤ N ∧
    (∀ q < (scanC T N st₀ L).1, ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N tab sd) s).M (ansB + 4 * q + m) =
        (packBytes ((scanC T N st₀ L).2.2.getD q default).toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N tab sd) s).M y = rd s.M y) := by
  set I := (extractorInput c π L).toArray with hI
  have hW : wordsOf L < 2 ^ 64 := by
    have := tape_entries_end4 c π L hs
    rw [entryOff_length] at this
    simp only [wordsOf]; omega
  have htl : tab.length = 4 * (N + 1) := hT.1
  -- the count
  have c1 := cnt_sem c π L hs hq ht s hM
  have hh1 : ∀ y, regs ≤ y → rd (semXIR I (cntIR pL) s).M y = rd s.M y := fun y hy => cnt_heap pL I s hM hy
  have hM1 := inv_sem I (wf_cntIR pL) hM
  have z1 := size_sem I (cntIR pL) s
  rw [chainIR, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (cntIR pL) s = s1 at c1 hh1 hM1 z1
  -- the table
  obtain ⟨t1, t2, hM2, z2⟩ := storesIR_sem I tab chB s1 hM1 (by simp only [chB_eq, regs]; omega)
    (by rw [z1, htl]; simp only [chB_eq, chEnd] at hsz ⊢; omega) (by rw [htl, chB_eq]; omega)
  try rw [semXIR_seq]
  generalize semXIR I (storesIR chB tab) s1 = s2 at t1 t2 hM2 z2
  have c2 : rd s2.M rCn5 = toWord (wordsOf L) := by
    rw [t2 _ (by decide) (by decide) (by decide) (.inl (by simp only [rCn5, chB_eq]; omega)), c1]
  -- the seed
  obtain ⟨wsd, -, hsd⟩ := hsd
  obtain ⟨d1, d2, d3⟩ := hsd s2 hM2 (by rw [z2, z1]; exact hsz)
  have hM3 := inv_sem I wsd hM2
  have z3 := size_sem I sd s2
  try rw [semXIR_seq]
  generalize semXIR I sd s2 = s3 at d1 d2 d3 hM3 z3
  -- the start
  have hs3 := hM3.1
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := startPs_vals pL s3.M hs3
  have e4 : semXIR I (.blk (startPs pL)) s3 = ⟨runPrims (startPs pL) s3.M, s3.o⟩ := rfl
  rw [e4]
  have hM4 : Inv (runPrims (startPs pL) s3.M) := inv_runPrims (by
    simp [startPs, Prim.dst, rWp, rEo, rPi, rTl, rTh, rTo, rMt]) hM3
  have hh4 : ∀ y, regs ≤ y → rd (runPrims (startPs pL) s3.M) y = rd s3.M y := fun y hy =>
    startPs_frame pL _ (by simp only [regs] at hy; simp only [rWp, rEo, rPi, rTl, rTh, rTo, rMt]; omega)
  have c4 : rd (runPrims (startPs pL) s3.M) rCn5 = toWord (wordsOf L) := by
    rw [startPs_frame pL _ (by decide), d2, c2]
  generalize hM4' : runPrims (startPs pL) s3.M = M4 at v1 v2 v3 v4 v5 v6 hM4 hh4 c4
  -- the loop
  have hc : rCC < M4.size := by have := hM4.1; simp only [regs] at this; simp only [rCC]; omega
  have e5 : semXIR I (.loopT rCC rCn5 ⟨0, 1, 1⟩ (wordIR N)) ⟨M4, s3.o⟩ =
      iterL (semXIR I (wordIR N)) rCC (wordsOf L) ⟨entryT rCC rCn5 M4, s3.o⟩ := by
    simp only [semXIR, rd_entryT hc, c4, toNat_toWord hW]
  rw [e5]
  have hE : Inv (entryT rCC rCn5 M4) := inv_of_frame hM4 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCC]; omega)
  have ef : ∀ i, i ≠ rCC → rd (entryT rCC rCn5 M4) i = rd M4 i := fun i hi => entryT_frame _
    (Ne.symm hi)
  have zE : (entryT rCC rCn5 M4).size = s.M.size := by
    rw [size_entryT, ← hM4', size_runPrims, z3, z2, z1]
  -- the table and the seed in the loop's heap
  have tabE : ∀ i < tab.length, rd (entryT rCC rCn5 M4) (chB + i) = tab.getD i 0 := fun i hi => by
    rw [ef _ (by simp only [rCC, chB_eq]; omega), hh4 _ (by simp only [chB_eq, regs]; omega),
      d3 _ (by simp only [chB_eq, regs]; omega)
        (.inl (by rw [htl] at hi; simp only [chB_eq, hB_eq] at hi ⊢; omega)), t1 i hi]
  have hst : Stat I T N (entryT rCC rCn5 M4) (0, st₀, []) ⟨entryT rCC rCn5 M4, s3.o⟩ := {
    inv := hE
    size := by rw [zE]; exact hsz
    pi := by rw [ef _ (by decide), v3]
    pN := Nat.zero_le _
    len := rfl
    th := by rw [ef _ (by decide), v5]; decide
    tof := by rw [ef _ (by decide), v6]; decide
    tg := fun _ => by
      refine ⟨by rw [ef _ (by decide), v4, h119], by rw [h119]; norm_num, fun j hj => ?_⟩
      rw [h119] at hj
      rw [ef _ (by decide), v5, ef _ (by decide), v6, exW, toNat_toWord (by norm_num),
        if_pos (by omega), ef _ (by simp only [rCC, hB_eq]; omega),
        hh4 _ (by simp only [hB_eq, regs]; omega), d1 j (by omega)]
    ans := fun q hq => absurd hq (Nat.not_lt_zero _)
    heap := fun _ _ _ _ => rfl }
  have hTab : TabOK I T N (entryT rCC rCn5 M4) := fun p hp0 hpN => by
    obtain ⟨a1, a2⟩ := hT.2 p hp0 hpN
    have r : ∀ k < 3, rd (entryT rCC rCn5 M4) (chB + 4 * p + k) = tab.getD (4 * p + k) 0 :=
      fun k hk => by rw [Nat.add_assoc, tabE _ (by rw [htl]; omega)]
    refine ⟨by rw [r 1 (by norm_num)]; exact a1, fun hpN' st => ?_⟩
    obtain ⟨b1, b2, b3⟩ := a2 hpN' st
    refine ⟨by rw [show chB + 4 * p = chB + 4 * p + 0 from rfl, r 0 (by norm_num)]; exact b1, b2,
      fun j hj => ?_⟩
    rw [b3 j hj, r 2 (by norm_num), r 1 (by norm_num)]
  have hent := entriesAt_tape c π L hs hq ht 0 (Nat.zero_le _)
  simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero,
    List.drop_zero] at hent
  obtain ⟨g1, -, -⟩ := scan_sem hTab hN L (0, st₀, []) ⟨entryT rCC rCn5 M4, s3.o⟩ (pL + 1) hst
    (by rw [ef _ (by decide), v1]) (by rw [ef _ (by decide), v2]) hent
  refine ⟨g1.pN, fun q hq m hm => g1.ans q hq m hm, fun y hy hyc => ?_⟩
  have y1 : y < hB ∨ hB + 16 ≤ y := by
    rcases hyc with h | h
    · left; simp only [chB_eq, hB_eq] at h ⊢; omega
    · right; simp only [chEnd, hB_eq] at h ⊢; omega
  have y2 : y < ansB ∨ chEnd ≤ y := by
    rcases hyc with h | h
    · left; simp only [chB_eq, ansB_eq] at h ⊢; omega
    · right; exact h
  have y3 : y < chB ∨ chB + tab.length ≤ y := by
    rw [htl]
    rcases hyc with h | h
    · left; exact h
    · right; simp only [chEnd, chB_eq] at h ⊢; omega
  have hy' := hy
  simp only [regs] at hy'
  rw [g1.heap y hy y1 y2, ef _ (by simp only [rCC]; omega), hh4 y hy, d3 y hy y1,
    t2 y (by simp only [cTmp]; omega) (by simp only [rAd4]; omega) (by simp only [rKd]; omega) y3,
    hh1 y hy]

end FR.X

