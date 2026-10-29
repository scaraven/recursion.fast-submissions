-- New for  (BLUEPRINT revision 4.2, §6.2 step 2; stage S-H4, pass 4, item 3).
import FRXLookup

/-!
# The log index at revision 4.1: walk and sort with the index base and the log's position as
# parameters

3.x's index (`FRXLog`: `walkIR`, `sortIR`; `FRXLogSpec`, `FRXSortSim`) hard-codes two
constants: the index base `memX = 2^26` and the tape word of `|L|`, `posL = 5 + piSize/8`
(3.x's format). At revision 4.1 the decoder's regions need `2^28` words below the index
(`FRXDec4Map`, Part 25 F2), and a node proof has `|π| = piSizeOf seq4`, which A2′ is changing.
This module is the same programs and proofs with both constants parameters:

* `walkIR4 bX pL`, `sortIR4 bX pL` (`passIR4 pL`), `idxIR4 bX pL := walkIR4 ; sortIR4`;
* `walk_spec4`, `sortIR4_sem`, **`idxIR4_sorted`**: on a tape whose `π` has `5 + ⌈|π|/8⌉ = pL`
  words before `|L|` (`hs`), `X[0..|L|)` at `bX` holds exactly the entries' tape positions,
  strictly sorted by the key (answer, position).

The proofs are 3.x's with `memX ↦ bX`, `posL ↦ pL`; the numerals they used become the hypotheses
`regs ≤ bX ≤ 2^60` and `pL ≤ 2^60`. The pure merge-sort facts (`passes_ok`, `keyLt_order`) and the
programs that never name the constants (`walkBody`, `stepIR`, `swapPs`) are reused.
-/

namespace FR.X

open RecursionFast

section Idx4

variable (bX pL : ℕ)

/-- Before the walk: `|L|`, the first entry's position, `X`'s base. -/
def walkPre4 : XIR :=
  .seq (.blk [.const rP (BitVec.ofNat 64 (pL + 1)), .const rXA (BitVec.ofNat 64 bX)])
    (readAt rN pL)

/-- **The walk.** -/
def walkIR4 : XIR := .seq (walkPre4 bX pL) (.loopT rCW rN ⟨0, 1, 5⟩ walkBody)

/-- Before a pass: empty runs, output index `0`, the step count `|L|`. -/
def passPre4 : XIR :=
  .seq (.blk [.const rI 0, .const rIE 0, .const rJ 0, .const rJE 0, .const rKk 0])
    (readAt rNS pL)

/-- **One merge pass.** -/
def passIR4 : XIR := .seq (.seq (passPre4 pL) (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR)) (.blk swapPs)

/-- Before the sort: `n`, `w = 1`, the bases, the pass count. -/
def sortPre4 : XIR :=
  .seq (readAt rN pL) (.blk [.const rW2 1, .const rSrc (BitVec.ofNat 64 bX),
    .op .add rDst rSrc rN, .const rNP 64])

/-- **The sort**: 64 passes. -/
def sortIR4 : XIR := .seq (sortPre4 bX pL) (.loopK rCP rNP 64 (passIR4 pL))

/-- Walk and sort. -/
def idxIR4 : XIR := .seq (walkIR4 bX pL) (sortIR4 bX pL)

/-- The source base of pass `p`: `X` on even passes, `Y = X + n` on odd ones. -/
def baseX4 (n p : ℕ) : ℕ := if p % 2 = 0 then bX else bX + n

theorem baseX4_ctl (n : ℕ) : baseX4 bX n 0 = bX ∧ baseX4 bX n 1 = bX + n := ⟨rfl, rfl⟩

theorem baseX4_two (n p : ℕ) : baseX4 bX n (p + 1 + 1) = baseX4 bX n p := by
  unfold baseX4
  by_cases h : p % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem wf_walkIR4 : WF (walkIR4 bX pL) := by
  simp +decide [walkIR4, walkPre4, walkBody, ceil8Ps, readAt, WF, Writes, Prim.dst, rP, rXA, rN, rA, rQL,
    rT1, rT2, rKc, rCW, cTmp, regs]



/-! ## The lookup (3.x's `lookIR`, `FRXLookup`) -/

/-- One halving step of the lower-bound search on `[lo, lo + len)`; nothing when `len = 0`. -/
def bsBody4 : XIR :=
  .ite rLn (.seq (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
      .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) (.seq (.load rX rAd)
    (.seq ansLtIR (.ite rF (.blk [.op .add rLo rMd cOne, .op .sub rLn rLn rHf,
      .op .sub rLn rLn cOne]) (.blk [.op .or rLn rHf rHf]))))) (.blk [])

/-- After the search: `rFd := lo < n ∧ answer(X[lo]) = target`. -/
def foundIR4 : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc]) (.seq (.load rX rAd)
    (.seq (aposIR rPa rX) (.seq (.blk [.op .ltu rFd rLo rN]) (.seq (eqTWord 0 rQ0)
      (.seq (eqTWord 1 rQ1) (.seq (eqTWord 2 rQ2) (eqTWord 3 rQ3)))))))

/-- **The lookup** of the target `(rQ0 … rQ3)` in the sorted `X[0..n)`: `rLo :=` the first slot
whose answer is not below the target (64 halvings), `rFd := 1` iff its answer is the target. -/
def lookIR4 : XIR :=
  .seq (.seq (readAt rN pL) (.blk [.const rLo 0, .op .or rLn rN rN, .const rNB 64]))
    (.seq (.loopK rCB rNB 64 (bsBody4 bX)) (foundIR4 bX))


/-- Before the search: `n` from tape word `pL`, `lo := 0`, `len := n`, the step count `64`. -/
def lookPre4 : XIR := .seq (readAt rN pL) (.blk [.const rLo 0, .op .or rLn rN rN, .const rNB 64])

/-- The tape position of entry `k`. -/
def posE4 (L : Log) (k : ℕ) : ℕ := pL + 1 + entryOff L k

/-- What `idxIR4_sorted` gives: `X[0..|L|)` is the set of entry positions, strictly sorted. -/
structure Sorted4 (I : Array Word) (L : Log) (X : ℕ → Word) : Prop where
  srt : ∀ a b, a < b → b < L.length → keyLt I (X a) (X b) = true
  cov : ∀ a < L.length, ∃ k < L.length, X a = toWord (posE4 pL L k)
  all : ∀ k < L.length, ∃ a < L.length, X a = toWord (posE4 pL L k)

theorem lookIR4_eq : (lookIR4 bX pL) = .seq (lookPre4 pL) (.seq (.loopK rCB rNB 64 (bsBody4 bX)) (foundIR4 bX)) := rfl

/-! ## The index's structural obligations (as `DecOk4` will need them) -/

theorem wf_idxIR4 : WF (idxIR4 bX pL) := by
  simp +decide [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, WF, Writes, Prim.dst, rA, rN, rP,
    rXA, rQL, rT1, rT2, rKc, rCW, rW2, rSrc, rDst, rI, rIE, rJ, rJE, rKk, rAd, rX, rY, rPa, rPb, rKa,
    rKb, rF, rG, rH, rCP, rNP, rCS, rNS, rV, regs, cTmp, cOne]

/-- The index's cost (3.x's `cost_logIR`: the constants do not change it). -/
theorem cost_idxIR4 (t : ℕ) : cost (idxIR4 bX pL) t = 2592 + t / 5 * 11871 := by
  simp only [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, cost, blkSteps,
    List.length_cons, List.length_nil, List.length_append, Aff.eval, Nat.one_mul]
  norm_num
  omega

theorem sizeIR_idxIR4 : sizeIR (idxIR4 bX pL) = sizeIR logIR := by
  simp only [idxIR4, logIR, idxIR, walkIR4, walkPre4, walkIR, walkPre, sortIR4, sortPre4, sortIR,
    sortPre, passIR4, passPre4, passIR, passPre, readAt, sizeIR, List.length_cons, List.length_nil]

theorem outs_idxIR4 (t : ℕ) : outs (idxIR4 bX pL) t = 0 := by
  simp [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs, stepIR,
    blockIR, cmpIR, cmpWord, aposIR, readAt, outs]

/-- **The index's loop bounds**, on a tape whose word `pL < 2^64` is a count of at most `t / 5`
(3.x's `safe_logIR`). -/
theorem safe_idxIR4 {I : Array Word} {t : ℕ} (hp : pL < 2 ^ 64) (h : (I.getD pL 0).toNat ≤ t / 5) :
    Safe I t (idxIR4 bX pL) := by
  unfold idxIR4 walkIR4 sortIR4 passIR4
  have hcnt : ∀ (p : XIR) (d : ℕ), WF p → d < regs → ∀ s : St, Inv s.M →
      (rd (semXIR I (.seq p (readAt d pL)) s).M d).toNat ≤ Aff.eval ⟨0, 1, 5⟩ t :=
    fun p d hP hd s hM => by
      rw [rd_seq_readAt I p s hP hM hd hp]
      simpa [Aff.eval] using h
  refine .seq (.loopT (safe_of_noLoopT (by simp [walkPre4, readAt, NoLoopT]))
    (hcnt _ rN (by simp +decide [WF, Prim.dst, rP, rXA]) (by simp [rN, regs]))
    (safe_of_noLoopT (by simp [walkBody, NoLoopT]))) (.seq (safe_of_noLoopT (by
      simp [sortPre4, readAt, NoLoopT])) (.loopK (.seq (.loopT (safe_of_noLoopT (by
      simp [passPre4, readAt, NoLoopT])) (hcnt _ rNS (by simp +decide only [WF, Prim.dst, rI, rIE,
        rJ, rJE, rKk])
      (by simp [rNS, regs])) (safe_of_noLoopT (by
        simp [stepIR, blockIR, cmpIR, cmpWord, aposIR, NoLoopT]))) (.blk _))))

variable {bX pL} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

omit hbX hbX2 hpL in
theorem tape_getD_posL4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) :
    (extractorInput c π L).getD pL 0 = toWord L.length := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList).length = pL := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> omega
  rw [tape_eq, ← hl]
  exact getD_append_length _ _ _

omit hbX hbX2 hpL in
theorem tape_count_le4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    ((extractorInput c π L).toArray.getD pL 0).toNat ≤ (extractorInput c π L).length / 5 := by
  have hlen : pL + 1 + 5 * L.length ≤ (extractorInput c π L).length := by
    have := length_logEntries L
    rw [tape_eq]
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      logWords, List.length_cons, Vector.length_toList, List.length_singleton]
    omega
  rw [getD_toArray, tape_getD_posL4 c π L hs, toNat_toWord (by omega)]
  omega


omit hbX hbX2 hpL in
/-- **The tape at entry `k`**: its query length. -/
theorem tape_entry4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) {k : ℕ}
    (hk : k < L.length) :
    (extractorInput c π L).getD (pL + 1 + entryOff L k) 0 = toWord L[k].1.size := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> omega
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, ← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact entries_getD L k hk

omit hbX hbX2 hpL in
/-- The end of the log on the tape. -/
theorem tape_entries_end4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) :
    pL + 1 + entryOff L L.length ≤ (extractorInput c π L).length := by
  have := entryOff_le_sum L L.length
  rw [tape_eq]
  simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
    logWords, List.length_cons, Vector.length_toList, List.length_singleton,
    entries_length]
  omega

/-- **The walk's loop**: `m` iterations from entry `j` write `pos j, …` into `X[j], …` and leave
every other heap cell alone. -/
theorem walkLoop4 (I : Array Word) (n : ℕ) (pos : ℕ → ℕ)
    (hpos : ∀ j < n, pos j < 2 ^ 64 ∧ pos (j + 1) = pos j + 5 + (ceil8 (I.getD (pos j) 0)).toNat) :
    ∀ (m j : ℕ) (s : St), j + m = n → Inv s.M → bX + n ≤ s.M.size → bX + n < 2 ^ 64 →
      rd s.M rP = toWord (pos j) → rd s.M rXA = toWord (bX + j) → ∀ i, regs ≤ i →
      rd (iterL (semXIR I walkBody) rCW m s).M i =
        if bX + j ≤ i ∧ i < bX + n then toWord (pos (i - bX)) else rd s.M i
  | 0, j, s, hj, _, _, _, _, _, i, _ => by
    simp only [iterL]; rw [if_neg (by omega)]
  | m + 1, j, s, hj, hM, hsz, hn, hp, hx, i, hi => by
    have hjn : j < n := by omega
    obtain ⟨h1, h2, h3⟩ := walkBody_sem I s hM hp hx (hpos j hjn).1
      (by simp only [regs] at hbX ⊢; omega) (by omega) (by omega)
    have hM' : Inv (decS rCW (semXIR I walkBody s)).M := inv_of_frame
      (inv_sem I wf_walkBody hM) (size_decS ..) fun i hi => rd_decS (by simp only [rCW]; omega) _
    have hsz' : (decS rCW (semXIR I walkBody s)).M.size = s.M.size := by
      rw [size_decS, size_sem]
    have hp' : rd (decS rCW (semXIR I walkBody s)).M rP = toWord (pos (j + 1)) := by
      rw [rd_decS (by decide), h1, (hpos j hjn).2]
    have hx' : rd (decS rCW (semXIR I walkBody s)).M rXA = toWord (bX + (j + 1)) := by
      rw [rd_decS (by decide), h2, Nat.add_assoc]
    have hh : ∀ i, regs ≤ i → rd (decS rCW (semXIR I walkBody s)).M i =
        if i = bX + j then toWord (pos j) else rd s.M i := fun i hi => by
      rw [rd_decS (by simp only [rCW, regs] at hi ⊢; omega), h3 i hi]
    simp only [iterL]
    rw [walkLoop4 I n pos hpos m (j + 1) _ (by omega) hM' (by rw [hsz']; exact hsz) hn hp' hx' i hi,
      hh i hi]
    by_cases h : i = bX + j
    · subst h; simp <;> omega
    · by_cases h' : bX + (j + 1) ≤ i ∧ i < bX + n
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg h, if_neg (by omega)]

/-- **`walk_spec4`**: on a domain tape of a SNARK proof, the walk leaves in `X[k]` the tape
position of log entry `k`, for every `k < |L|`. -/
theorem walk_spec4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length ≤ s.M.size) {k : ℕ} (hk : k < L.length) :
    rd (semXIR (extractorInput c π L).toArray (walkIR4 bX pL) s).M (bX + k) =
      toWord (pL + 1 + entryOff L k) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  have hcnt : (I.getD pL 0).toNat = L.length := by
    rw [hI, getD_toArray, tape_getD_posL4 c π L hs, toNat_toWord (by omega)]
  have hpos : ∀ j < L.length, pL + 1 + entryOff L j < 2 ^ 64 ∧
      pL + 1 + entryOff L (j + 1) = pL + 1 + entryOff L j + 5 +
        (ceil8 (I.getD (pL + 1 + entryOff L j) 0)).toNat := fun j hj => by
    have hle := entryOff_le_sum L (j + 1)
    rw [entryOff_succ L hj] at hle ⊢
    have hq' := hq _ (List.getElem_mem hj)
    have hend' : entryOff L (j + 1) ≤ entryOff L L.length := by
      rw [entryOff_length]; exact entryOff_le_sum L (j + 1)
    rw [entryOff_succ L hj] at hend'
    rw [hI, getD_toArray, tape_entry4 c π L hs hj, toNat_ceil8 hq']
    simp only [qWords] at hend' ⊢
    omega
  -- the state at the loop's entry
  have hM1 := inv_sem I (show WF (walkPre4 bX pL) by simp [walkPre4, readAt, WF, Prim.dst, rP, rXA, rN, rA])
    hM
  have hs1 := hM1.1
  have hcnt' : rd (semXIR I (walkPre4 bX pL) s).M rN = I.getD pL 0 :=
    rd_seq_readAt I _ s (by simp [WF, Prim.dst, rP, rXA]) hM (by decide) (by omega)
  have hp0 : rd (semXIR I (walkPre4 bX pL) s).M rP = toWord (pL + 1) := by
    have := hM.1; simp only [regs] at this
    simp only [walkPre4, readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rXA, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
    rfl
  have hx0 : rd (semXIR I (walkPre4 bX pL) s).M rXA = toWord bX := by
    have := hM.1; simp only [regs] at this
    simp only [walkPre4, readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rXA, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
    rfl
  have hc : rCW < (semXIR I (walkPre4 bX pL) s).M.size := by simp only [regs] at hs1; simp only [rCW]; omega
  have hE : Inv (entryT rCW rN (semXIR I (walkPre4 bX pL) s).M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; omega)
  have hEp : rd (entryT rCW rN (semXIR I (walkPre4 bX pL) s).M) rP = toWord (pL + 1 + entryOff L 0) := by
    rw [entryT_frame _ (by decide), hp0]; rfl
  have hEx : rd (entryT rCW rN (semXIR I (walkPre4 bX pL) s).M) rXA = toWord (bX + 0) := by
    rw [entryT_frame _ (by decide), hx0, Nat.add_zero]
  have hEs : bX + L.length ≤ (entryT rCW rN (semXIR I (walkPre4 bX pL) s).M).size := by
    rw [size_entryT, size_sem]; exact hsz
  have e : semXIR I (walkIR4 bX pL) s = iterL (semXIR I walkBody) rCW L.length
      ⟨entryT rCW rN (semXIR I (walkPre4 bX pL) s).M, (semXIR I (walkPre4 bX pL) s).o⟩ := by
    simp only [walkIR4, semXIR, rd_entryT hc, hcnt', hcnt]
  rw [e]
  generalize entryT rCW rN (semXIR I (walkPre4 bX pL) s).M = M0 at hE hEp hEx hEs
  have hn : bX + L.length < 2 ^ 64 := by omega
  rw [walkLoop4 hbX hbX2 hpL I L.length (fun j => pL + 1 + entryOff L j) hpos L.length 0 ⟨M0, _⟩ (by omega) hE
    hEs hn hEp hEx (bX + k) (by simp only [regs] at hbX ⊢; omega), if_pos (by omega),
    Nat.add_sub_cancel_left]


/-- **One pass**: the destination holds `passF` of the source; the bases swap and
`w := min(2w, n)`. -/
theorem passIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ}
    (hL : Lay S D n w s.M.size) (hn : I.getD pL 0 = toWord n)
    (hS : rd s.M rSrc = toWord S) (hD : rd s.M rDst = toWord D) (hW : rd s.M rW2 = toWord w)
    (hN : rd s.M rN = toWord n) :
    Inv (semXIR I (passIR4 pL) s).M ∧ rd (semXIR I (passIR4 pL) s).M rSrc = toWord D ∧
    rd (semXIR I (passIR4 pL) s).M rDst = toWord S ∧
    rd (semXIR I (passIR4 pL) s).M rW2 = toWord (min (2 * w) n) ∧ rd (semXIR I (passIR4 pL) s).M rN = toWord n ∧
    ∀ a < n, rd (semXIR I (passIR4 pL) s).M (D + a) =
      passF (keyLt I) (fun a => rd s.M (S + a)) n w (fun a => rd s.M (D + a)) a := by
  have hs := hM.1
  have Lbn := hL.bn
  have Lbw := hL.bw
  simp only [regs] at hs
  have hP0 : WF (passPre4 pL) := by simp +decide [passPre4, readAt, WF, Prim.dst, rI, rIE, rJ, rJE,
    rKk, rNS, rA, and_true]
  have hlo0 : Lo (passPre4 pL) := by
    simp +decide [Lo, passPre4, readAt, Prim.dst, regs, rI, rIE, rJ, rJE, rKk, rNS, rA,
      and_true]
  have hcnt : rd (semXIR I (passPre4 pL) s).M rNS = toWord n := by
    rw [passPre4, rd_seq_readAt I _ s (by simp +decide only [WF, Prim.dst, rI, rIE, rJ, rJE, rKk]) hM
      (by decide) (by omega), hn]
  have hR0 : Regs (semXIR I (passPre4 pL) s).M S D n w ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [passPre4, readAt, semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rI, rIE, rJ, rJE, rKk, rNS, rA]; omega))
      only [rd_set_self, rd_set_ne] <;>
    first | exact hW | exact hN | exact hS | exact hD | rfl
  have hM0 := inv_sem I hP0 hM
  have hH0 := hframe I _ s hlo0
  have hz0 := size_sem I (passPre4 pL) s
  rw [passIR4, semXIR_seq, semXIR_seq]
  generalize semXIR I (passPre4 pL) s = s0 at hcnt hR0 hM0 hH0 hz0
  have hs0 := hM0.1
  simp only [regs] at hs0
  have e : semXIR I (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR) s0 =
      iterL (semXIR I stepIR) rCS n ⟨entryT rCS rNS s0.M, s0.o⟩ := by
    simp only [semXIR, rd_entryT (show rCS < s0.M.size by simp only [rCS]; omega), hcnt,
      toNat_toWord (show n < 2 ^ 64 by omega)]
  rw [e]
  have hRel : Rel S D n w (fun a => rd s.M (S + a)) (entryT rCS rNS s0.M)
      ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ :=
    Rel.set (M := s0.M) ⟨hM0, hR0, fun a ha => hH0 _ (le_trans hL.rS (by omega)),
      fun a ha => hH0 _ (le_trans hL.rD (by omega)), by simp [Bnd]⟩ (by decide) (by decide)
      (by decide) hL.rS hL.rD _
  have h1 := stepLoop I n ⟨entryT rCS rNS s0.M, s0.o⟩ _ (by rw [size_entryT, hz0]; exact hL) hRel
    (by simp)
  generalize iterL (semXIR I stepIR) rCS n ⟨entryT rCS rNS s0.M, s0.o⟩ = s1 at h1
  obtain ⟨hM1, hR1, -, hd1, -⟩ := h1
  have hs1 := hM1.1
  simp only [regs] at hs1
  have hlo : Lo (.blk swapPs) := by
    simp +decide only [Lo, swapPs, minPs, Prim.dst, regs, rV, rSrc, rDst, rW2, rT1, rT2, rKc]
  refine ⟨inv_sem I (by simp +decide only [WF, swapPs, minPs, Prim.dst, rV, rSrc, rDst, rW2, rT1,
    rT2, rKc])
    hM1, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  rotate_left 4
  · rw [hframe I _ s1 hlo _ (le_trans hL.rD (by omega)), hd1 a ha]; rfl
  all_goals
    simp only [swapPs, minPs, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run]
    simp (disch := first | decide | (simp only [size_set, rV, rSrc, rDst, rW2, rT1, rT2, rKc]; omega))
      only [rd_set_self, rd_set_ne]
    simp only [hR1.S, hR1.D, hR1.w, hR1.n, or_self_eval, add_toWord]
  rw [minP_toWord (by omega) (by omega), two_mul]

/-- **The sort's semantics**: on a heap whose `X[0..n)` holds distinct words, `sortIR4` leaves in
`X[0..n)` exactly those words, strictly sorted by `keyLt`. -/
theorem sortIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n : ℕ}
    (hn : I.getD pL 0 = toWord n) (hn2 : n < 2 ^ 62) (hsz : bX + n + n ≤ s.M.size)
    (hinj : ∀ a b, a < n → b < n → rd s.M (bX + a) = rd s.M (bX + b) → a = b) :
    (∀ a b, a < b → b < n →
      keyLt I (rd (semXIR I (sortIR4 bX pL) s).M (bX + a)) (rd (semXIR I (sortIR4 bX pL) s).M (bX + b)) = true) ∧
    (∀ a < n, ∃ c < n, rd (semXIR I (sortIR4 bX pL) s).M (bX + a) = rd s.M (bX + c)) ∧
    (∀ c < n, ∃ a < n, rd (semXIR I (sortIR4 bX pL) s).M (bX + a) = rd s.M (bX + c)) := by
  have hs := hM.1
  simp only [regs] at hs
  have hP0 : WF (sortPre4 bX pL) := by simp +decide [sortPre4, readAt, WF, Prim.dst, rN, rA, rW2, rSrc,
    rDst, rNP, and_true]
  have hlo0 : Lo (sortPre4 bX pL) := by
    simp +decide [Lo, sortPre4, readAt, Prim.dst, regs, rN, rA, rW2, rSrc, rDst, rNP, and_true]
  -- the registers after `(sortPre4 bX pL)`
  have h0 : rd (semXIR I (sortPre4 bX pL) s).M rN = toWord n ∧ rd (semXIR I (sortPre4 bX pL) s).M rW2 = toWord 1 ∧
      rd (semXIR I (sortPre4 bX pL) s).M rSrc = toWord bX ∧
      rd (semXIR I (sortPre4 bX pL) s).M rDst = toWord (bX + n) ∧ rd (semXIR I (sortPre4 bX pL) s).M rNP = 64 := by
    have hN := rd_readAt I s hM (d := rN) (pos := pL) (by decide) (by omega)
    have hM' := inv_sem I (P := readAt rN pL) (by simp +decide [readAt, WF, Prim.dst, rN, rA,
      and_true]) hM
    rw [hn] at hN
    rw [sortPre4, semXIR_seq]
    generalize semXIR I (readAt rN pL) s = s' at hN hM'
    have hs' := hM'.1
    simp only [regs] at hs'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rN, rW2, rSrc, rDst, rNP]; omega)) only
      [rd_set_self, rd_set_ne]
    · exact hN
    · rfl
    · rfl
    · rw [hN]; exact add_toWord _ _
  have hM0 := inv_sem I hP0 hM
  have hH0 := hframe I _ s hlo0
  have hz0 := size_sem I (sortPre4 bX pL) s
  rw [sortIR4, semXIR_seq]
  generalize semXIR I (sortPre4 bX pL) s = s0 at h0 hM0 hH0 hz0
  obtain ⟨n0, w0, S0, D0, P0⟩ := h0
  have e : semXIR I (.loopK rCP rNP 64 (passIR4 pL)) s0 =
      iterL (semXIR I (passIR4 pL)) rCP 64 ⟨entryK rCP rNP 64 s0.M, s0.o⟩ := by
    simp only [semXIR, entryK64 hM0 P0]
    rfl
  rw [e]
  have hE : ∀ i, i ≠ rCP → i ≠ cTmp → rd (entryK rCP rNP 64 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME : Inv (entryK rCP rNP 64 s0.M) := inv_of_frame hM0 (size_entryK ..)
    fun i hi => hE i (by simp only [rCP]; omega) (by simp only [cTmp]; omega)
  generalize hS0 : (⟨entryK rCP rNP 64 s0.M, s0.o⟩ : St) = T at hE hME
  -- the pass invariant
  have hLay : ∀ p, Lay (baseX4 bX n p) (baseX4 bX n (p + 1)) n (wseq n p) s.M.size := fun p => by
    have := wseq_le n p
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, this, wseq_pos (p := p)⟩ <;>
      unfold baseX4 <;> simp only [regs] at hbX ⊢ <;> split_ifs <;> omega
  have hPI : ∀ p, Inv (iterL (semXIR I (passIR4 pL)) rCP p T).M ∧
      (iterL (semXIR I (passIR4 pL)) rCP p T).M.size = s.M.size ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rSrc = toWord (baseX4 bX n p) ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rDst = toWord (baseX4 bX n (p + 1)) ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rW2 = toWord (wseq n p) ∧
      rd (iterL (semXIR I (passIR4 pL)) rCP p T).M rN = toWord n := by
    intro p
    induction p with
    | zero =>
      simp only [iterL]
      rw [← hS0]
      refine ⟨hME, by rw [size_entryK, hz0], ?_, ?_, ?_, ?_⟩
      · rw [hE _ (by decide) (by decide), S0]; simp only [baseX4, Nat.zero_mod, if_true]
      · rw [hE _ (by decide) (by decide), D0]; simp only [baseX4]; rfl
      · rw [hE _ (by decide) (by decide), w0]; rfl
      · rw [hE _ (by decide) (by decide), n0]
    | succ p ih =>
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih
      obtain ⟨j1, j2, j3, j4, j5, -⟩ := passIR4_sem hbX hbX2 hpL I _ i1 (by rw [i2]; exact hLay p) hn i3 i4 i5 i6
      rw [iterL_succ']
      refine ⟨inv_of_frame j1 (size_decS ..) fun i hi => rd_decS (by simp only [rCP]; omega) _,
        by rw [size_decS, size_sem, i2], ?_, ?_, ?_, ?_⟩
      · rw [rd_decS (by decide), j2]
      · exact (rd_decS (by decide) _).trans (j3.trans (congrArg toWord (baseX4_two bX n p).symm))
      · exact (rd_decS (by decide) _).trans (j4.trans (by simp only [wseq]))
      · rw [rd_decS (by decide), j5]
  have hX : ∀ p, ∀ a < n, rd (iterL (semXIR I (passIR4 pL)) rCP (p + 1) T).M (baseX4 bX n (p + 1) + a) =
      passF (keyLt I) (fun a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n p + a)) n (wseq n p)
        (fun a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n (p + 1) + a)) a := fun p a ha => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hPI p
    have hL := hLay p
    rw [← i2] at hL
    rw [iterL_succ', rd_decS (by have := hL.rD; simp only [regs, rCP] at *; omega)]
    exact (passIR4_sem hbX hbX2 hpL I _ i1 hL hn i3 i4 i5 i6).2.2.2.2.2 a ha
  have hX0 : ∀ a < n, rd (iterL (semXIR I (passIR4 pL)) rCP 0 T).M (baseX4 bX n 0 + a) = rd s.M (bX + a) :=
    fun a ha => by
      simp only [iterL, baseX4, Nat.zero_mod, if_true]
      rw [← hS0, hE _ (by simp only [rCP, regs] at hbX ⊢; omega) (by simp only [cTmp, regs] at hbX ⊢; omega),
        hH0 _ (by simp only [regs] at hbX ⊢; omega)]
  obtain ⟨r1, r2, r3⟩ := passes_ok (keyLt_order I) (by omega)
    (fun p a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n p + a))
    (fun p a => rd (iterL (semXIR I (passIR4 pL)) rCP p T).M (baseX4 bX n (p + 1) + a)) hX
    (fun a b ha hb h => hinj a b ha hb (by rwa [hX0 a ha, hX0 b hb] at h))
  have hB64 : baseX4 bX n 64 = bX := if_pos (by decide)
  simp only [hB64] at r1 r2 r3
  refine ⟨r1, fun a ha => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc, e⟩ := r2 a ha
    exact ⟨c, hc, by rw [e, hX0 c hc]⟩
  · obtain ⟨a, ha, e⟩ := r3 c hc
    exact ⟨a, ha, by rw [e, hX0 c hc]⟩

/-- **The log index** (`index_spec`, sort half): after `(idxIR4 bX pL)` (walk and sort) on a domain tape of a SNARK proof,
`X[0..|L|)` holds exactly the tape positions of the log's entries, strictly sorted by the key
(answer, position). -/
theorem idxIR4_sorted (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size) :
    (∀ a b, a < b → b < L.length →
      keyLt (extractorInput c π L).toArray
        (rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
        (rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + b)) = true) ∧
    (∀ a < L.length, ∃ k < L.length, rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M
      (bX + a) = toWord (pL + 1 + entryOff L k)) ∧
    (∀ k < L.length, ∃ a < L.length, rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M
      (bX + a) = toWord (pL + 1 + entryOff L k)) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  have hW := fun {k : ℕ} (hk : k < L.length) => walk_spec4 hbX hbX2 hpL c π L hs hq ht s hM (by omega) hk
  have hwf : WF (walkIR4 bX pL) := wf_walkIR4 bX pL
  rw [idxIR4, semXIR_seq]
  obtain ⟨r1, r2, r3⟩ := sortIR4_sem hbX hbX2 hpL I (semXIR I (walkIR4 bX pL) s) (inv_sem I hwf hM) (n := L.length)
    (by rw [hI, getD_toArray, tape_getD_posL4 c π L hs]) (by omega) (by rw [size_sem]; exact hsz)
    (fun a b ha hb h => by
      rw [hW ha, hW hb] at h
      have hab := congrArg BitVec.toNat h
      have ea : entryOff L a < entryOff L L.length := entryOff_lt L ha le_rfl
      have eb : entryOff L b < entryOff L L.length := entryOff_lt L hb le_rfl
      rw [toNat_toWord (by omega), toNat_toWord (by omega)] at hab
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · have := entryOff_lt L h' hb.le; omega
      · have := entryOff_lt L h' ha.le; omega)
  refine ⟨r1, fun a ha => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, e⟩ := r2 a ha
    exact ⟨k, hk, e.trans (hW hk)⟩
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, e.trans (hW hk)⟩


/-! ## The lookup's semantics -/

omit hbX hbX2 hpL in
/-- **The tape at entry `k`'s answer**: word `m < 4` of `packBytes L[k].2`. -/
theorem tape_answer4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) {k : ℕ}
    (hk : k < L.length) {m : ℕ} (hm : m < 4) :
    (extractorInput c π L).getD (pL + 1 + entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) 0 =
      (packBytes L[k].2.toList).getD m 0 := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> omega
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, show pL + 1 + entryOff L k + 1 +
      (L[k].1.size + 7) / 8 + m = (pL + 1) + (entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) by
      omega, ← hl, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]
  exact entries_getD_ans L k hk m hm

omit hbX hbX2 hpL in
/-- **The answer read at entry `k`'s position is `packBytes L[k].2`.** -/
theorem ansW_entry4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) {k : ℕ}
    (hk : k < L.length) :
    ansW (extractorInput c π L).toArray (toWord (posE4 pL L k)) = packBytes L[k].2.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have hq' := hq _ (List.getElem_mem hk)
  have hk1 : entryOff L (k + 1) ≤ entryOff L L.length := by
    rcases Nat.lt_or_ge (k + 1) L.length with h | h
    · exact (entryOff_lt L h le_rfl).le
    · rw [show k + 1 = L.length by omega]
  rw [entryOff_succ L hk] at hk1
  have hqw : qWords L[k] = 5 + (L[k].1.size + 7) / 8 := rfl
  have hx : (toWord (posE4 pL L k)).toNat = posE4 pL L k := toNat_toWord (by simp only [posE4]; omega)
  have hap : ∀ j < 4, (aposW I (toWord (posE4 pL L k)) + toWord j).toNat =
      pL + 1 + entryOff L k + 1 + (L[k].1.size + 7) / 8 + j := fun j hj => by
    have h1 : I.getD (posE4 pL L k) 0 = toWord L[k].1.size := by
      rw [hI, getD_toArray]; exact tape_entry4 c π L hs hk
    simp only [aposW, hx, h1]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_ceil8 hq', hx,
      toNat_toWord (show j < 2 ^ 64 by omega), show (1 : Word).toNat = 1 from rfl]
    simp only [posE4] at hx ⊢
    omega
  apply List.ext_getElem (by simp [ansW_length, packBytes_digest_length])
  intro m h1 h2
  have hm : m < 4 := h1
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, ← tape_answer4 c π L hs hk hm,
    ← getD_toArray (extractorInput c π L), ← hI]
  interval_cases m
  · exact congrArg (fun i => I.getD i 0) (hap 0 (by decide))
  · exact congrArg (fun i => I.getD i 0) (hap 1 (by decide))
  · exact congrArg (fun i => I.getD i 0) (hap 2 (by decide))
  · exact congrArg (fun i => I.getD i 0) (hap 3 (by decide))

omit hbX hbX2 hpL in
theorem posE_lt4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) {k : ℕ} (hk : k < L.length) :
    posE4 pL L k < 2 ^ 64 := by
  have := tape_entries_end4 c π L hs
  have := entryOff_lt L hk le_rfl
  simp only [posE4]; omega

omit hbX hbX2 hpL in
/-- **The first preimage is the search's boundary.** On the sorted index, the predicate "the
answer is below `packBytes t`" holds on a prefix; at the prefix's end `b` sits the first entry
of `L` whose answer is `t` (`ansIdx`), and if there is none, no slot has answer `t`. -/
theorem lookup_pure4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    {X : ℕ → Word} (hX : Sorted4 pL (extractorInput c π L).toArray L X) (t : Digest) :
    (∀ a b, a < b → b < L.length →
      ltT (extractorInput c π L).toArray X (packBytes t.toList) b = true →
      ltT (extractorInput c π L).toArray X (packBytes t.toList) a = true) ∧
    ∀ b ≤ L.length,
      (∀ a < b, ltT (extractorInput c π L).toArray X (packBytes t.toList) a = true) →
      (∀ a, b ≤ a → a < L.length →
        ltT (extractorInput c π L).toArray X (packBytes t.toList) a = false) →
      (∀ k, FR.Snd.ansIdx L t = some k → b < L.length ∧ X b = toWord (posE4 pL L k)) ∧
      (FR.Snd.ansIdx L t = none → ∀ a < L.length,
        ansW (extractorInput c π L).toArray (X a) ≠ packBytes t.toList) := by
  set I := (extractorInput c π L).toArray with hI
  set T := packBytes t.toList with hT
  have hA : ∀ a < L.length, ∃ k, ∃ hk : k < L.length, X a = toWord (posE4 pL L k) ∧
      ansW I (X a) = packBytes L[k].2.toList := fun a ha => by
    obtain ⟨k, hk, e⟩ := hX.cov a ha
    exact ⟨k, hk, e, by rw [e]; exact ansW_entry4 c π L hs hq ht hk⟩
  -- the key order splits into the answer order and, on equal answers, the position order
  have hkey : ∀ a b, a < b → b < L.length → lexW (ansW I (X a)) (ansW I (X b)) = true ∨
      (ansW I (X a) = ansW I (X b) ∧ X a < X b) := fun a b hab hb => by
    have := hX.srt a b hab hb
    rw [keyLt, keyW_eq, keyW_eq, lexW_append (ansW I (X a)) (ansW I (X b))
      (by rw [ansW_length, ansW_length])] at this
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hmono : ∀ a b, a < b → b < L.length → ltT I X T b = true → ltT I X T a = true :=
    fun a b hab hb h => by
      rcases hkey a b hab hb with h' | ⟨h', -⟩
      · exact lexW_trans _ _ _ h' h
      · simpa [ltT, h'] using h
  refine ⟨hmono, fun b hbn hlo hhi => ⟨fun k hk => ?_, fun hn a ha he => ?_⟩⟩
  · obtain ⟨hkl, hkt, hfirst⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
    simp only [decide_eq_true_eq] at hkt
    obtain ⟨a0, ha0, e0⟩ := hX.all k hkl
    have hA0 : ansW I (X a0) = T := by rw [e0, ansW_entry4 c π L hs hq ht hkl, hkt]
    -- `p` fails at `a0`, and holds below it
    have hf0 : ltT I X T a0 = false := by simp [ltT, hA0, lexW_irrefl]
    have ht0 : ∀ a < a0, ltT I X T a = true := fun a ha => by
      rcases hkey a a0 ha ha0 with h' | ⟨h', hlt⟩
      · rwa [hA0] at h'
      · exfalso
        obtain ⟨k', hk', e', hA'⟩ := hA a (by omega)
        have hkt' : L[k'].2 = t := packBytes_digest_inj (by rw [← hA', h', hA0])
        rw [e', e0, BitVec.lt_def, toNat_toWord (posE_lt4 c π L hs ht hk'),
          toNat_toWord (posE_lt4 c π L hs ht hkl)] at hlt
        have hkk : k' < k := by
          by_contra hge
          rcases Nat.lt_or_ge k k' with h2 | h2
          · have := entryOff_lt L h2 hk'.le; simp only [posE4] at hlt; omega
          · have : k = k' := by omega
            subst this; omega
        have := hfirst k' hkk
        simp [hkt'] at this
    have hb1 : b ≤ a0 := by
      by_contra h
      have := hlo a0 (by omega)
      rw [hf0] at this; exact absurd this (by decide)
    have hb2 : a0 ≤ b := by
      by_contra h
      have h1 := ht0 b (by omega)
      rw [hhi b le_rfl (by omega)] at h1; exact absurd h1 (by decide)
    have : b = a0 := by omega
    subst this
    exact ⟨ha0, e0⟩
  · obtain ⟨k, hk, -, hA'⟩ := hA a ha
    have := List.findIdx?_eq_none_iff.mp hn L[k] (List.getElem_mem hk)
    have e : L[k].2 = t := packBytes_digest_inj (by rw [← hA', he])
    simp [e] at this

/-- **One halving step** of the machine is `bsStep` on the predicate `ltT`. -/
theorem bsBody4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n lo len : ℕ} {T : List Word}
    {X : ℕ → Word} (hR : SRegs s.M n lo len T) (hb : lo + len ≤ n) (hn : n < 2 ^ 62)
    (hX : ∀ a < n, rd s.M (bX + a) = X a) :
    SRegs (semXIR I (bsBody4 bX) s).M n (bsStep (ltT I X T) (lo, len)).1
      (bsStep (ltT I X T) (lo, len)).2 T := by
  have hs := hM.1
  simp only [regs] at hs
  rw [bsBody4, semXIR_ite, hR.len]
  by_cases h0 : len = 0
  · subst h0
    have h00 : toWord 0 = (0 : Word) := rfl
    rw [if_pos h00]
    have e : bsStep (ltT I X T) (lo, 0) = (lo, 0) := by simp [bsStep]
    rw [e]; exact hR
  have hne : toWord len ≠ 0 := fun h => h0 (by
    have := congrArg BitVec.toNat h; rwa [toNat_toWord (by omega)] at this)
  rw [if_neg hne]
  have e : bsStep (ltT I X T) (lo, len) = if ltT I X T (lo + len / 2) = true then
      (lo + len / 2 + 1, len - len / 2 - 1) else (lo, len / 2) := by simp [bsStep, h0]
  rw [e]
  -- the probe
  have hwf1 : WF (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
      .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) := by
    simp +decide [WF, Prim.dst, rKc, rHf, rMd, rAd]
  have h1 : rd (semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
        .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s).M rHf = toWord (len / 2) ∧
      rd (semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
        .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s).M rMd =
        toWord (lo + len / 2) ∧
      rd (semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
        .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s).M rAd =
        toWord (lo + len / 2 + bX) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rKc, rHf, rMd, rAd]; omega)) only
      [rd_set_self, rd_set_ne] <;>
    rw [hR.len, shr_one_toWord (by omega)]
    · rw [hR.lo, add_toWord]
    · rw [hR.lo, add_toWord]; exact add_toWord _ _
  have hR1 := hR.sem (I := I) hM hwf1 (by
    simp +decide [srL, Writes, Prim.dst, rKc, rHf, rMd, rAd, rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
      exists_eq_left, or_false, and_true])
  have hM1 := inv_sem I hwf1 hM
  have hH1 := hframe I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
    .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s
    (by simp +decide [Lo, Prim.dst, regs, rKc, rHf, rMd, rAd])
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
    .const rKc (BitVec.ofNat 64 bX), .op .add rAd rMd rKc]) s = s1 at h1 hR1 hM1 hH1
  obtain ⟨hf1, hd1, ha1⟩ := h1
  have hs1 := hM1.1
  simp only [regs] at hs1
  -- the load of `X[mid]`
  have hx2 : rd (semXIR I (.load rX rAd) s1).M rX = X (lo + len / 2) := by
    simp only [semXIR]
    rw [rd_set_self (by simp only [rX]; omega), ha1, toNat_toWord (by omega),
      hH1 _ (by simp only [regs] at hbX ⊢; omega), show lo + len / 2 + bX = bX + (lo + len / 2) by
      omega, hX _ (by omega)]
  have hfr2 : ∀ q ∈ [rHf, rMd] ++ srL, rd (semXIR I (.load rX rAd) s1).M q = rd s1.M q :=
    fun q hq => by
      simp only [semXIR]
      exact rd_set_ne ((by decide : ∀ r ∈ [rHf, rMd] ++ srL, rX ≠ r) q hq)
  have hR2 := hR1.sem (I := I) (P := .load rX rAd) hM1 (by simp +decide [WF, rX]) (by
    simp +decide [srL, Writes, rX, rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM2 := inv_sem I (P := .load rX rAd) (by simp +decide [WF, rX]) hM1
  rw [semXIR_seq]
  generalize semXIR I (.load rX rAd) s1 = s2 at hx2 hfr2 hR2 hM2
  -- the comparison
  have hF3 : rd (semXIR I ansLtIR s2).M rF = bW (ltT I X T (lo + len / 2)) := by
    rw [ansLtIR_sem I s2 hM2, hx2, hR2.q]; rfl
  have hfr3 := fun {q : ℕ} (hq : q ∈ [rHf, rMd] ++ srL) => ansLtIR_frame I s2 hM2 hq
  have hR3 := hR2.sem (I := I) (P := ansLtIR) hM2 wf_ansLtIR nw_ansLtIR
  have hM3 := inv_sem I wf_ansLtIR hM2
  have hhf3 : rd (semXIR I ansLtIR s2).M rHf = toWord (len / 2) := by
    rw [hfr3 (by simp), hfr2 _ (by simp), hf1]
  have hmd3 : rd (semXIR I ansLtIR s2).M rMd = toWord (lo + len / 2) := by
    rw [hfr3 (by simp), hfr2 _ (by simp), hd1]
  rw [semXIR_seq]
  generalize semXIR I ansLtIR s2 = s3 at hF3 hR3 hM3 hhf3 hmd3
  have hs3 := hM3.1
  have hc3 : rd s3.M cOne = 1 := hM3.2 0 (by decide)
  simp only [regs] at hs3
  rw [semXIR_ite, hF3]
  by_cases hp : ltT I X T (lo + len / 2) = true
  · rw [hp, if_neg bW_ne_zero, if_pos rfl]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rLo, rLn]; omega)) only
      [rd_set_self, rd_set_ne]
    · rw [hmd3, hc3, add_one_toWord]
    · rw [hR3.len, hhf3, hc3, sub_toWord (by omega) (by omega),
        show (1 : Word) = toWord 1 from rfl, sub_toWord (by omega) (by omega)]
    · exact hR3.n
    · exact hR3.q
  · rw [(Bool.not_eq_true _).mp hp, if_pos bW_false, if_neg (by simp)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rLn]; omega)) only
      [rd_set_self, rd_set_ne]
    · exact hR3.lo
    · rw [hhf3, or_self_eval]
    · exact hR3.n
    · exact hR3.q

omit hbX hbX2 hpL in
theorem wf_bsBody4 : WF (bsBody4 bX) := by
  simp +decide [bsBody4, ansLtIR, aposIR, ceil8Ps, cmpTWord, WF, Prim.dst, rQL, rKc, rT2, rPa,
    rAd, rKa, rG, rH, rF, rHf, rMd, rX, rLo, rLn, and_true, List.cons_append, List.nil_append]

omit hbX hbX2 hpL in
theorem lo_bsBody4 : Lo (bsBody4 bX) := by
  simp +decide [bsBody4, ansLtIR, aposIR, ceil8Ps, cmpTWord, Lo, Prim.dst, regs, rQL, rKc, rT2,
    rPa, rAd, rKa, rG, rH, rF, rHf, rMd, rX, rLo, rLn, and_true, List.cons_append, List.nil_append]

/-- **The search loop**: `m` iterations run `bsRun` and leave the heap alone. -/
theorem bsLoop4 (I : Array Word) {n : ℕ} {T : List Word} {X : ℕ → Word} (hn : n < 2 ^ 62) :
    ∀ (m : ℕ) (s : St) (lo len : ℕ), Inv s.M → SRegs s.M n lo len T → lo + len ≤ n →
      (∀ a < n, rd s.M (bX + a) = X a) →
      Inv (iterL (semXIR I (bsBody4 bX)) rCB m s).M ∧
      SRegs (iterL (semXIR I (bsBody4 bX)) rCB m s).M n (bsRun (ltT I X T) m (lo, len)).1
        (bsRun (ltT I X T) m (lo, len)).2 T ∧
      ∀ x, regs ≤ x → rd (iterL (semXIR I (bsBody4 bX)) rCB m s).M x = rd s.M x
  | 0, _, _, _, hM, hR, _, _ => ⟨hM, hR, fun _ _ => rfl⟩
  | m + 1, s, lo, len, hM, hR, hb, hX => by
    have h1 := bsBody4_sem hbX hbX2 hpL I s hM hR hb hn hX
    have hH := hframe I (bsBody4 bX) s (lo_bsBody4 (bX := bX))
    have hM1 := inv_sem I (wf_bsBody4 (bX := bX)) hM
    have hM' : Inv (decS rCB (semXIR I (bsBody4 bX) s)).M := inv_of_frame hM1 (size_decS ..)
      fun i hi => rd_decS (by simp only [rCB]; omega) _
    have hH' : ∀ x, regs ≤ x → rd (decS rCB (semXIR I (bsBody4 bX) s)).M x = rd s.M x :=
      fun x hx => (rd_decS (by simp only [rCB, regs] at *; omega) _).trans (hH x hx)
    obtain ⟨a, b, c⟩ := bsLoop4 I hn m _ _ _ hM' h1.decS (bsStep_le hb)
      (fun a ha => by rw [hH' _ (by simp only [regs] at hbX ⊢; omega), hX a ha])
    simp only [iterL, bsRun]
    exact ⟨a, b, fun x hx => (c x hx).trans (hH' x hx)⟩

/-- **The found flag**: `rFd = [lo < n ∧ ansW(X[lo]) = T]`; `rLo` is kept. -/
theorem foundIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n lo len : ℕ} {T : List Word}
    (hR : SRegs s.M n lo len T) (hlo : lo ≤ n) (hn : n < 2 ^ 62) :
    rd (semXIR I (foundIR4 bX) s).M rFd =
      bW (decide (lo < n) && decide (ansW I (rd s.M (bX + lo)) = T)) ∧
    rd (semXIR I (foundIR4 bX) s).M rLo = toWord lo := by
  have hs := hM.1
  simp only [regs] at hs
  set x := rd s.M (bX + lo)
  -- the address and the load
  have hwf1 : WF (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
      (.load rX rAd)) := by simp +decide [WF, Prim.dst, rKc, rAd, rX, and_true]
  have hx1 : rd (semXIR I (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
      (.load rX rAd)) s).M rX = x := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, rX]; omega)]
    simp (disch := first | decide | (simp only [size_set, rKc, rAd]; omega)) only [rd_set_self,
      rd_set_ne]
    rw [hR.lo, show XOp.add.eval (toWord lo) (BitVec.ofNat 64 bX) = toWord (lo + bX) from
      add_toWord _ _, toNat_toWord (by omega), rd_set_ne (by simp only [rAd, regs] at hbX ⊢; omega),
      rd_set_ne (by simp only [rKc, regs] at hbX ⊢; omega), show lo + bX = bX + lo by omega]
  have hR1 := hR.sem (I := I) hM hwf1 (by
    simp +decide [srL, Writes, Prim.dst, rKc, rAd, rX, rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3,
      List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
      exists_eq_left, or_false, and_true])
  have hM1 := inv_sem I hwf1 hM
  have e : semXIR I (foundIR4 bX) s = semXIR I (.seq (aposIR rPa rX) (.seq (.blk [.op .ltu rFd rLo rN])
      (.seq (eqTWord 0 rQ0) (.seq (eqTWord 1 rQ1) (.seq (eqTWord 2 rQ2) (eqTWord 3 rQ3))))))
      (semXIR I (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
        (.load rX rAd)) s) := rfl
  rw [e]
  generalize semXIR I (.seq (.blk [.const rKc (BitVec.ofNat 64 bX), .op .add rAd rLo rKc])
      (.load rX rAd)) s = s1 at hx1 hR1 hM1
  -- the answer position
  rw [semXIR_seq]
  have ha2 := aposIR_sem I s1 hM1 (.inl ⟨rfl, rfl⟩)
  rw [hx1] at ha2
  have hR2 := hR1.sem (I := I) (P := aposIR rPa rX) hM1 wf_aposIR' (by
    simp only [srL, aposIR, ceil8Ps, Writes, List.cons_append, List.nil_append]; decide)
  have hM2 := inv_sem I wf_aposIR' hM1
  generalize semXIR I (aposIR rPa rX) s1 = s2 at ha2 hR2 hM2
  -- `lo < n`
  rw [semXIR_seq]
  have hs2 := hM2.1
  simp only [regs] at hs2
  have hwf3 : WF (.blk [.op .ltu rFd rLo rN]) := by simp +decide [WF, Prim.dst, rFd]
  have hf3 : rd (semXIR I (.blk [.op .ltu rFd rLo rN]) s2).M rFd = bW (decide (lo < n)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rFd]; omega), hR2.lo, hR2.n, ltW_toWord (by omega) (by omega)]
  have hfr3 : ∀ q ∈ [rPa] ++ srL, rd (semXIR I (.blk [.op .ltu rFd rLo rN]) s2).M q =
      rd s2.M q := fun q hq => by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne ((by decide : ∀ r ∈ [rPa] ++ srL, rFd ≠ r) q hq)
  have hM3 := inv_sem I hwf3 hM2
  generalize semXIR I (.blk [.op .ltu rFd rLo rN]) s2 = s3 at hf3 hfr3 hM3
  have step : ∀ (s' : St), Inv s'.M → (∀ q ∈ [rPa] ++ srL, rd s'.M q = rd s2.M q) →
      ∀ (w r : ℕ) (p : Bool), w < 4 → (r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) →
      rd s'.M rFd = bW p →
      rd (semXIR I (eqTWord w r) s').M rFd = bW (p && decide ((ansW I x).getD w 0 = rd s2.M r)) ∧
      Inv (semXIR I (eqTWord w r) s').M ∧
      (∀ q ∈ [rPa] ++ srL, rd (semXIR I (eqTWord w r) s').M q = rd s2.M q) :=
    fun s' hM' hq w r p hw hr hf => by
      have hrq : rd s'.M r = rd s2.M r := hq r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      refine ⟨?_, inv_sem I (wf_eqTWord w r) hM', fun q hqm => by
        rw [eqTWord_frame I s' hM' w r hqm, hq q hqm]⟩
      rw [eqTWord_sem I s' hM' hr, hf, hrq, hq rPa (by decide), ha2, ansW_getD I x hw, eq_bW,
        bW_and]
  rw [semXIR_seq]
  obtain ⟨f0, m0, q0⟩ := step s3 hM3 hfr3 0 rQ0 _ (by decide) (.inl rfl) hf3
  generalize semXIR I (eqTWord 0 rQ0) s3 = s4 at f0 m0 q0
  rw [semXIR_seq]
  obtain ⟨f1, m1, q1⟩ := step s4 m0 q0 1 rQ1 _ (by decide) (.inr (.inl rfl)) f0
  generalize semXIR I (eqTWord 1 rQ1) s4 = s5 at f1 m1 q1
  rw [semXIR_seq]
  obtain ⟨f2, m2, q2⟩ := step s5 m1 q1 2 rQ2 _ (by decide) (.inr (.inr (.inl rfl))) f1
  generalize semXIR I (eqTWord 2 rQ2) s5 = s6 at f2 m2 q2
  obtain ⟨f3, -, q3⟩ := step s6 m2 q2 3 rQ3 _ (by decide) (.inr (.inr (.inr rfl))) f2
  refine ⟨?_, by rw [q3 rLo (by decide), hR2.lo]⟩
  rw [f3, ← hR2.q, decide_ansW _ (ansW_length I x)]

/-- **The lookup's semantics**: `rLo` is the lower bound `bsRun` of the target `T` (the words in
`rQ0 … rQ3`) on `X[0..n)`, `rFd` says whether that slot exists and its answer is `T`; the heap
is unchanged. -/
theorem lookIR4_sem (I : Array Word) (s : St) (hM : Inv s.M) {n : ℕ} {T : List Word}
    {X : ℕ → Word} (hn : I.getD pL 0 = toWord n) (hn2 : n < 2 ^ 62)
    (hT : [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3] = T)
    (hX : ∀ a < n, rd s.M (bX + a) = X a) :
    rd (semXIR I (lookIR4 bX pL) s).M rLo = toWord (bsRun (ltT I X T) 64 (0, n)).1 ∧
    rd (semXIR I (lookIR4 bX pL) s).M rFd = bW (decide ((bsRun (ltT I X T) 64 (0, n)).1 < n) &&
      decide (ansW I (rd s.M (bX + (bsRun (ltT I X T) 64 (0, n)).1)) = T)) ∧
    ∀ x, regs ≤ x → rd (semXIR I (lookIR4 bX pL) s).M x = rd s.M x := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf0 : WF (lookPre4 pL) := by simp +decide [lookPre4, readAt, WF, Prim.dst, rN, rA, rLo, rLn,
    rNB, and_true]
  have hlo0 : Lo (lookPre4 pL) := by simp +decide [lookPre4, readAt, Lo, Prim.dst, regs, rN, rA, rLo,
    rLn, rNB, and_true]
  have hR0 : SRegs (semXIR I (lookPre4 pL) s).M n 0 n T ∧ rd (semXIR I (lookPre4 pL) s).M rNB = 64 := by
    have hN := rd_readAt I s hM (d := rN) (pos := pL) (by decide) (by omega)
    have hwfr : WF (readAt rN pL) := by simp +decide [readAt, WF, Prim.dst, rN, rA, and_true]
    have hM' := inv_sem I hwfr hM
    have hq' : [rd (semXIR I (readAt rN pL) s).M rQ0, rd (semXIR I (readAt rN pL) s).M rQ1,
        rd (semXIR I (readAt rN pL) s).M rQ2, rd (semXIR I (readAt rN pL) s).M rQ3] = T := by
      have hf := fun r (hr : r ∈ [rQ0, rQ1, rQ2, rQ3]) => FR.X.frame I _ s hwfr hM r
        ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r < regs) r hr) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp +decide [readAt, Writes, Prim.dst, rN,
            rA, rQ0, rQ1, rQ2, rQ3, or_false])
      rw [hf rQ0 (by simp), hf rQ1 (by simp), hf rQ2 (by simp), hf rQ3 (by simp)]
      exact hT
    rw [hn] at hN
    rw [lookPre4, semXIR_seq]
    generalize semXIR I (readAt rN pL) s = s' at hN hM' hq'
    have hs' := hM'.1
    simp only [regs] at hs'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLo, rLn, rNB]; omega)) only
      [rd_set_self, rd_set_ne]
    · rfl
    · rw [hN, or_self_eval]
    · exact hN
    · exact hq'
  have hM0 := inv_sem I hwf0 hM
  have hH0 := hframe I (lookPre4 pL) s hlo0
  rw [lookIR4_eq, semXIR_seq, semXIR_seq]
  generalize semXIR I (lookPre4 pL) s = s0 at hR0 hM0 hH0
  obtain ⟨hR0, hB0⟩ := hR0
  have e : semXIR I (.loopK rCB rNB 64 (bsBody4 bX)) s0 =
      iterL (semXIR I (bsBody4 bX)) rCB 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ := by
    simp only [semXIR, entryKB hM0 hB0]
    rfl
  rw [e]
  have hE : ∀ i, i ≠ rCB → i ≠ cTmp → rd (entryK rCB rNB 64 s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hME : Inv (entryK rCB rNB 64 s0.M) := inv_of_frame hM0 (size_entryK ..)
    fun i hi => hE i (by simp only [rCB]; omega) (by simp only [cTmp]; omega)
  have hRE : SRegs (entryK rCB rNB 64 s0.M) n 0 n T :=
    ⟨(hE _ (by decide) (by decide)).trans hR0.lo, (hE _ (by decide) (by decide)).trans hR0.len,
      (hE _ (by decide) (by decide)).trans hR0.n, by
        rw [hE rQ0 (by decide) (by decide), hE rQ1 (by decide) (by decide),
          hE rQ2 (by decide) (by decide), hE rQ3 (by decide) (by decide)]; exact hR0.q⟩
  have hHE : ∀ x, regs ≤ x → rd (entryK rCB rNB 64 s0.M) x = rd s.M x := fun x hx => by
    rw [hE x (by simp only [rCB, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
      hH0 x hx]
  obtain ⟨l1, l2, l3⟩ := bsLoop4 hbX hbX2 hpL I (X := X) hn2 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ 0 n hME hRE
    (by omega) (fun a ha => by rw [hHE (bX + a) (by simp only [regs] at hbX ⊢; omega), hX a ha])
  generalize iterL (semXIR I (bsBody4 bX)) rCB 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ = s1 at l1 l2 l3
  have hle := bsRun_le (p := ltT I X T) (n := n) 64 0 n (by omega)
  obtain ⟨f1, f2⟩ := foundIR4_sem hbX hbX2 hpL I s1 l1 l2 (le_trans (Nat.le_add_right _ _) hle) hn2
  have hH1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => (l3 x hx).trans (hHE x hx)
  refine ⟨f2, ?_, fun x hx => (hframe I (foundIR4 bX) s1 (by
    simp +decide [foundIR4, aposIR, ceil8Ps, eqTWord, Lo, Prim.dst, regs, rKc, rAd, rX, rQL,
      rT2, rPa, rFd, rKa, rH, and_true, List.cons_append, List.nil_append]) x hx).trans (hH1 x hx)⟩
  rw [f1, hH1 _ (by simp only [regs] at hbX ⊢; omega)]

/-- **`lookup_spec`**, parametric in the target `t`. On a domain tape of a SNARK proof, take a
state `s₂` whose `X[0..|L|)` is the one `idxIR4` left and whose `rQ0 … rQ3` hold
`packBytes t`. If `t` is the answer of some log entry, `(lookIR4 bX pL)` sets `rFd = 1` and `rLo` to a
slot `b` whose `X[b]` is the tape position of the **first** such entry (`FRLog.ansIdx`);
otherwise `rFd = 0`. `X` is unchanged, so it is still the sorted index. -/
theorem idx_lookup4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size) (t : Digest)
    (s₂ : St) (hM₂ : Inv s₂.M)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    (hT : [rd s₂.M rQ0, rd s₂.M rQ1, rd s₂.M rQ2, rd s₂.M rQ3] = packBytes t.toList) :
    (∀ k, FR.Snd.ansIdx L t = some k → ∃ b < L.length,
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rLo = toWord b ∧
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rFd = 1 ∧
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M (bX + b) = toWord (posE4 pL L k)) ∧
    (FR.Snd.ansIdx L t = none →
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rFd = 0) ∧
    Sorted4 pL (extractorInput c π L).toArray L
      (fun a => rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M (bX + a)) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  generalize semXIR I (idxIR4 bX pL) s = s1 at r1 r2 r3 hX₂
  set X : ℕ → Word := fun a => rd s1.M (bX + a) with hXd
  have hSX : Sorted4 pL I L X := ⟨r1, r2, r3⟩
  have hX₂' : ∀ a < L.length, rd s₂.M (bX + a) = X a := hX₂
  obtain ⟨l1, l2, l3⟩ := lookIR4_sem hbX hbX2 hpL I s₂ hM₂ (n := L.length) (X := X)
    (by rw [hI, getD_toArray, tape_getD_posL4 c π L hs]) (by omega) hT hX₂'
  obtain ⟨hmono, hpure⟩ := lookup_pure4 c π L hs hq ht hSX t
  obtain ⟨b1, b2, b3⟩ := bsRun_spec (p := ltT I X (packBytes t.toList)) (n := L.length)
    (by omega) hmono
  obtain ⟨hsome, hnone⟩ := hpure _ b1 b2 b3
  have hXb : ∀ a < L.length, rd (semXIR I (lookIR4 bX pL) s₂).M (bX + a) = X a := fun a ha => by
    rw [l3 _ (by simp only [regs] at hbX ⊢; omega), hX₂' a ha]
  refine ⟨fun k hk => ?_, fun hk => ?_, ⟨fun a b hab hb => ?_, fun a ha => ?_, fun k hk => ?_⟩⟩
  · obtain ⟨hb, e⟩ := hsome k hk
    obtain ⟨hkl, hkc⟩ := FR.Snd.ansIdx_lt hk
    refine ⟨_, hb, l1, ?_, by rw [hXb _ hb, e]⟩
    rw [l2, hX₂' _ hb, e, ansW_entry4 c π L hs hq ht hkl, hkc]
    simp [hb, bW]
  · rw [l2]
    by_cases hb : (bsRun (ltT I X (packBytes t.toList)) 64 (0, L.length)).1 < L.length
    · rw [hX₂' _ hb]
      have := hnone hk _ hb
      simp [hb, bW]
      exact this
    · simp [hb, bW]
  · rw [hXb a (by omega), hXb b hb]; exact r1 a b hab hb
  · rw [hXb a ha]; exact r2 a ha
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, by rw [hXb a ha]; exact e⟩


end Idx4

end FR.X
