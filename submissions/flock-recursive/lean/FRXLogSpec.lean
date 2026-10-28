-- New for `flock-recursive` (BLUEPRINT §6.5 `index_spec`; stage S-H2, track L-ext).
import FRXLog

/-!
# The walk's semantics (`index_spec`, first half)

On a domain tape of a SNARK proof, `walkIR` leaves in `X[k]` (cell `memX + k`) the tape
position of log entry `k`: `posL + 1 + entryOff L k`, where `entryOff L k` sums the words of the
entries before `k` (`5 + ⌈|q|/8⌉` each). `tape_entry` says the tape word there is `|q_k|`.

**`walk_spec`**: for every `k < |L|`, `rd M (memX + k) = toWord (posL + 1 + entryOff L k)`.
-/

namespace FR.X

open RecursionFast

/-- The words of a log entry on the tape. -/
def qWords (e : ByteArray × Digest) : ℕ := 5 + (e.1.size + 7) / 8

/-- The offset of entry `k` from the first entry. -/
def entryOff (L : Log) (k : ℕ) : ℕ := ((L.take k).map qWords).sum

theorem entryOff_succ (L : Log) {k : ℕ} (hk : k < L.length) :
    entryOff L (k + 1) = entryOff L k + qWords L[k] := by
  simp only [entryOff, List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero]

theorem entryOff_length (L : Log) : entryOff L L.length = (L.map qWords).sum := by
  simp [entryOff]

theorem entry_length (e : ByteArray × Digest) :
    (bytesWords e.1.data.toList ++ packBytes e.2.toList).length = qWords e := by
  simp only [List.length_append, bytesWords, List.length_cons, packBytes_length,
    Vector.length_toList, Array.length_toList, qWords]
  show _ + 1 + _ = _
  have : e.1.data.size = e.1.size := rfl
  omega

theorem entries_length (L : Log) :
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).length =
      (L.map qWords).sum := by
  induction L with
  | nil => rfl
  | cons e L ih => rw [List.flatMap_cons, List.length_append, ih, entry_length]; simp

theorem entryOff_le_sum (L : Log) (k : ℕ) : entryOff L k ≤ (L.map qWords).sum := by
  rw [entryOff, ← List.take_append_drop k L, List.map_append, List.sum_append, List.take_append_drop]
  · exact Nat.le_add_right _ _

/-- The word at an entry's offset is its query length. -/
theorem entries_getD : ∀ (L : Log) (k : ℕ) (hk : k < L.length),
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD (entryOff L k) 0 =
      toWord L[k].1.size
  | e :: L, 0, _ => by
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      bytesWords, List.cons_append, List.getD_cons_zero, List.getElem_cons_zero]
    rfl
  | e :: L, k + 1, hk => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    rw [ho, List.flatMap_cons, ← entry_length e, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
    exact entries_getD L k (by simp at hk; omega)

/-- **The tape at entry `k`**: its query length. -/
theorem tape_entry (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {k : ℕ}
    (hk : k < L.length) :
    (extractorInput c π L).getD (posL + 1 + entryOff L k) 0 = toWord L[k].1.size := by
  have hp : π.size = 800640 := hs.trans piSize_eq
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = posL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      hp, posL, Vector.length_toList, List.length_singleton]
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, ← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact entries_getD L k hk

/-- The end of the log on the tape. -/
theorem tape_entries_end (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) :
    posL + 1 + entryOff L L.length ≤ (extractorInput c π L).length := by
  have hp : π.size = 800640 := hs.trans piSize_eq
  have := entryOff_le_sum L L.length
  rw [tape_eq]
  simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
    hp, logWords, List.length_cons, posL, Vector.length_toList, List.length_singleton,
    entries_length]
  omega

/-! ## The guarded store to the heap -/

theorem rd_storeM {M : Mem} (hM : Inv M) {a v x : ℕ} (ha : rd M a = toWord x) (hx : regs ≤ x)
    (hx2 : x < 2 ^ 64) (hxs : x < M.size) (haT : a ≠ cTmp) (hvT : v ≠ cTmp) {i : ℕ}
    (hi : i ≠ cTmp) : rd (storeM M a v) i = if i = x then rd M v else rd M i := by
  have hT : cTmp < M.size := by have := hM.1; simp only [regs, cTmp] at *; omega
  have hB : rd M cBase = 256 := hM.2 1 (by decide)
  have hlt : XOp.ltu.eval (toWord x) 256 = 0 := by
    have : ¬ toWord x < 256 := by
      rw [BitVec.lt_def, toNat_toWord hx2]; simp only [regs] at hx
      exact Nat.not_lt.mpr (le_trans (by decide) hx)
    show (if toWord x < 256 then 1 else 0 : Word) = 0
    rw [if_neg this]
  unfold storeM
  simp only [rd_set_self hT, rd_set_ne (Ne.symm haT), rd_set_ne (Ne.symm hvT), ha, hB, hlt,
    ↓reduceIte, toNat_toWord hx2]
  by_cases h : i = x
  · subst h; rw [if_pos rfl, rd_set_self (by simpa using hxs)]
  · rw [if_neg h, rd_set_ne (Ne.symm h), rd_set_ne (Ne.symm hi)]

/-! ## The walk's loop -/

theorem toWord_add (a b : ℕ) : toWord a + toWord b = toWord (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- **One entry of the walk**: `p` and the write address advance, the heap gets `p` at `x`. -/
theorem walkBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p x : ℕ}
    (hp : rd s.M rP = toWord p) (hx : rd s.M rXA = toWord x) (hp2 : p < 2 ^ 64) (hxr : regs ≤ x)
    (hx2 : x < 2 ^ 64) (hxs : x < s.M.size) :
    rd (semXIR I walkBody s).M rP = toWord (p + 5 + (ceil8 (I.getD p 0)).toNat) ∧
    rd (semXIR I walkBody s).M rXA = toWord (x + 1) ∧
    ∀ i, regs ≤ i → rd (semXIR I walkBody s).M i = if i = x then toWord p else rd s.M i := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  have hsp : rd (storeM s.M rXA rP) rP = toWord p := by
    rw [storeM_frame hM (by decide) (by decide) (by decide), hp]
  have hsx : rd (storeM s.M rXA rP) rXA = toWord x := by
    rw [storeM_frame hM (by decide) (by decide) (by decide), hx]
  have hs1 : rd (storeM s.M rXA rP) cOne = 1 := by
    rw [storeM_frame hM (by decide) (by decide) (by decide), h1]
  have hsz : (storeM s.M rXA rP).size = s.M.size := size_storeM ..
  generalize hS : storeM s.M rXA rP = S at hsp hsx hs1 hsz
  have hSi : ∀ i, regs ≤ i → rd S i = if i = x then toWord p else rd s.M i := fun i hi => by
    rw [← hS, rd_storeM hM hx hxr hx2 hxs (by decide) (by decide)
      (by simp only [regs, cTmp] at hi ⊢; omega), hp]
  simp only [regs] at hs hxr
  simp only [walkBody, semXIR, ceil8Ps, runPrims, List.foldl, List.cons_append,
    List.nil_append, Prim.run, rXA, rP, rQL, rT1, rT2, rKc, cOne] at hS hsp hsx hs1 ⊢
  rw [hS]
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · simp (disch := first | decide | omega | (simp only [size_set]; omega))
      [rd_set_self, rd_set_ne, XOp.eval, hsp, toNat_toWord hp2]
    change toWord p + ceil8 (I[p]?.getD 0#64) + 5#64 = toWord (p + 5 + (ceil8 (I[p]?.getD 0#64)).toNat)
    generalize ceil8 (I[p]?.getD 0#64) = C
    have := C.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [toWord, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp (disch := first | decide | omega | (simp only [size_set]; omega))
      [rd_set_self, rd_set_ne, XOp.eval, hsx, hs1]
    exact (BitVec.ofNat_add x 1).symm
  · rw [← hSi i hi, ← hS]
    simp only [regs] at hi
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_ne]

theorem wf_walkBody : WF walkBody := by
  simp [walkBody, ceil8Ps, WF, Prim.dst, rP, rXA, rQL, rT1, rT2, rKc, cTmp]

/-- **The walk's loop**: `m` iterations from entry `j` write `pos j, …` into `X[j], …` and leave
every other heap cell alone. -/
theorem walkLoop (I : Array Word) (n : ℕ) (pos : ℕ → ℕ)
    (hpos : ∀ j < n, pos j < 2 ^ 64 ∧ pos (j + 1) = pos j + 5 + (ceil8 (I.getD (pos j) 0)).toNat) :
    ∀ (m j : ℕ) (s : St), j + m = n → Inv s.M → memX + n ≤ s.M.size → memX + n < 2 ^ 64 →
      rd s.M rP = toWord (pos j) → rd s.M rXA = toWord (memX + j) → ∀ i, regs ≤ i →
      rd (iterL (semXIR I walkBody) rCW m s).M i =
        if memX + j ≤ i ∧ i < memX + n then toWord (pos (i - memX)) else rd s.M i
  | 0, j, s, hj, _, _, _, _, _, i, _ => by
    simp only [iterL]; rw [if_neg (by omega)]
  | m + 1, j, s, hj, hM, hsz, hn, hp, hx, i, hi => by
    have hjn : j < n := by omega
    have hm : memX = 2 ^ 26 := rfl
    obtain ⟨h1, h2, h3⟩ := walkBody_sem I s hM hp hx (hpos j hjn).1
      (by simp only [regs, hm]; omega) (by omega) (by omega)
    have hM' : Inv (decS rCW (semXIR I walkBody s)).M := inv_of_frame
      (inv_sem I wf_walkBody hM) (size_decS ..) fun i hi => rd_decS (by simp only [rCW]; omega) _
    have hsz' : (decS rCW (semXIR I walkBody s)).M.size = s.M.size := by
      rw [size_decS, size_sem]
    have hp' : rd (decS rCW (semXIR I walkBody s)).M rP = toWord (pos (j + 1)) := by
      rw [rd_decS (by decide), h1, (hpos j hjn).2]
    have hx' : rd (decS rCW (semXIR I walkBody s)).M rXA = toWord (memX + (j + 1)) := by
      rw [rd_decS (by decide), h2, Nat.add_assoc]
    have hh : ∀ i, regs ≤ i → rd (decS rCW (semXIR I walkBody s)).M i =
        if i = memX + j then toWord (pos j) else rd s.M i := fun i hi => by
      rw [rd_decS (by simp only [rCW, regs] at hi ⊢; omega), h3 i hi]
    simp only [iterL]
    rw [walkLoop I n pos hpos m (j + 1) _ (by omega) hM' (by rw [hsz']; exact hsz) hn hp' hx' i hi,
      hh i hi]
    by_cases h : i = memX + j
    · subst h; simp <;> omega
    · by_cases h' : memX + (j + 1) ≤ i ∧ i < memX + n
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg h, if_neg (by omega)]

/-- **`walk_spec`**: on a domain tape of a SNARK proof, the walk leaves in `X[k]` the tape
position of log entry `k`, for every `k < |L|`. -/
theorem walk_spec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : memX + L.length ≤ s.M.size) {k : ℕ} (hk : k < L.length) :
    rd (semXIR (extractorInput c π L).toArray walkIR s).M (memX + k) =
      toWord (posL + 1 + entryOff L k) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  have hcnt : (I.getD posL 0).toNat = L.length := by
    rw [hI, getD_toArray, tape_getD_posL c π L hs, toNat_toWord (by omega)]
  have hpos : ∀ j < L.length, posL + 1 + entryOff L j < 2 ^ 64 ∧
      posL + 1 + entryOff L (j + 1) = posL + 1 + entryOff L j + 5 +
        (ceil8 (I.getD (posL + 1 + entryOff L j) 0)).toNat := fun j hj => by
    have hle := entryOff_le_sum L (j + 1)
    rw [entryOff_succ L hj] at hle ⊢
    have hq' := hq _ (List.getElem_mem hj)
    have hend' : entryOff L (j + 1) ≤ entryOff L L.length := by
      rw [entryOff_length]; exact entryOff_le_sum L (j + 1)
    rw [entryOff_succ L hj] at hend'
    rw [hI, getD_toArray, tape_entry c π L hs hj, toNat_ceil8 hq']
    simp only [qWords] at hend' ⊢
    omega
  -- the state at the loop's entry
  have hM1 := inv_sem I (show WF walkPre by simp [walkPre, readAt, WF, Prim.dst, rP, rXA, rN, rA])
    hM
  have hs1 := hM1.1
  have hcnt' : rd (semXIR I walkPre s).M rN = I.getD posL 0 :=
    rd_seq_readAt I _ s (by simp [WF, Prim.dst, rP, rXA]) hM (by decide) (by simp only [posL]; omega)
  have hp0 : rd (semXIR I walkPre s).M rP = toWord (posL + 1) := by
    have := hM.1; simp only [regs] at this
    simp only [walkPre, readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rXA, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
    rfl
  have hx0 : rd (semXIR I walkPre s).M rXA = toWord memX := by
    have := hM.1; simp only [regs] at this
    simp only [walkPre, readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rXA, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
    rfl
  have hc : rCW < (semXIR I walkPre s).M.size := by simp only [regs] at hs1; simp only [rCW]; omega
  have hE : Inv (entryT rCW rN (semXIR I walkPre s).M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; omega)
  have hEp : rd (entryT rCW rN (semXIR I walkPre s).M) rP = toWord (posL + 1 + entryOff L 0) := by
    rw [entryT_frame _ (by decide), hp0]; rfl
  have hEx : rd (entryT rCW rN (semXIR I walkPre s).M) rXA = toWord (memX + 0) := by
    rw [entryT_frame _ (by decide), hx0, Nat.add_zero]
  have hEs : memX + L.length ≤ (entryT rCW rN (semXIR I walkPre s).M).size := by
    rw [size_entryT, size_sem]; exact hsz
  have e : semXIR I walkIR s = iterL (semXIR I walkBody) rCW L.length
      ⟨entryT rCW rN (semXIR I walkPre s).M, (semXIR I walkPre s).o⟩ := by
    simp only [walkIR, semXIR, rd_entryT hc, hcnt', hcnt]
  rw [e]
  generalize entryT rCW rN (semXIR I walkPre s).M = M0 at hE hEp hEx hEs
  have hn : memX + L.length < 2 ^ 64 := by simp only [memX]; omega
  rw [walkLoop I L.length (fun j => posL + 1 + entryOff L j) hpos L.length 0 ⟨M0, _⟩ (by omega) hE
    hEs hn hEp hEx (memX + k) (by simp only [regs, memX]; omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

end FR.X
