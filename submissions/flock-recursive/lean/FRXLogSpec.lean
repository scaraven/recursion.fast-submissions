-- G6: this module also holds the former modules `FRXLog` (one section each, in import order).
import FRXComputes

section G6_FRXLog

-- New for `flock-recursive` (BLUEPRINT §6.2 step 2; stage S-H2, track L-ext).

/-!
# The log index: walk and sort (§6.2 step 2)

On a SNARK proof (`|π| = piSize`) the log starts at tape word `posL = 5 + piSize/8 = 94,465`
(its length `|L|`), its entries at `94,466`. An entry at position `p` is `|q|` (one word), the
query's `⌈|q|/8⌉` packed words, then the answer (4 words) at `apos p = p + 1 + ⌈|q|/8⌉`.

* `walkIR`: one pass over the entries; `X[k] :=` the position of entry `k`, `X` at `memX` (the
  memory per tape word). Loop count `|L|` read from `posL` just before the loop, cap `t / 5`
  (an entry takes at least five words).
* `sortIR`: a bottom-up merge sort of `X` (64 passes of width `1, 2, 4, …`, capped at `n`, from
  `X` to `Y = X + n` and back) by the key `(answer words 0…3, position)`, lexicographic and
  unsigned; the position breaks ties, so the first entry with an answer comes first (the
  first-preimage order). 64 is even, so the result is back in `X`.
* `logIR := walkIR ; sortIR`, the SNARK branch so far: `Safe` on every domain tape of a proof of
  `piSize` bytes (`safe_logIR`), its cost `cost_logIR` within `decBudget`, no output
  (`decOk_logIR`).

* `lookIR`: the lower bound of a target answer `(rQ0 … rQ3)` in the sorted `X` (64 halvings),
  `rFd := 1` iff found: a routine for the later phases, parametric in the target.
* `logIR := idxIR := walkIR ; sortIR`.

Semantics: `FRXLogSpec` (walk), `FRXSortSim` (sort), `FRXLookup` (lookup).
-/

namespace FR.X

open RecursionFast

/-- The tape word of `|L|` on a SNARK proof. -/
def posL : ℕ := 5 + 99738

/-! ## Registers (user registers `75 …`) -/

/-- `|L|`. -/ def rN : ℕ := 75
/-- Tape position. -/ def rP : ℕ := 76
/-- Write address into `X`. -/ def rXA : ℕ := 77
/-- `|q|`. -/ def rQL : ℕ := 78
/-- Scratch. -/ def rT1 : ℕ := 79
/-- Scratch. -/ def rT2 : ℕ := 80
/-- Constant scratch. -/ def rKc : ℕ := 81
/-- The walk's counter. -/ def rCW : ℕ := 82
/-- Run width. -/ def rW2 : ℕ := 83
/-- Source base. -/ def rSrc : ℕ := 84
/-- Destination base. -/ def rDst : ℕ := 85
/-- Left head. -/ def rI : ℕ := 86
/-- Left end. -/ def rIE : ℕ := 87
/-- Right head. -/ def rJ : ℕ := 88
/-- Right end. -/ def rJE : ℕ := 89
/-- Output index. -/ def rKk : ℕ := 90
/-- Address scratch. -/ def rAd : ℕ := 91
/-- Left element. -/ def rX : ℕ := 92
/-- Right element. -/ def rY : ℕ := 93
/-- Left answer position. -/ def rPa : ℕ := 94
/-- Right answer position. -/ def rPb : ℕ := 95
/-- Key word (left). -/ def rKa : ℕ := 96
/-- Key word (right). -/ def rKb : ℕ := 97
/-- `1` iff the left element goes first. -/ def rF : ℕ := 98
/-- Scratch. -/ def rG : ℕ := 99
/-- Scratch. -/ def rH : ℕ := 100
/-- The pass counter. -/ def rCP : ℕ := 101
/-- The pass count (`64`). -/ def rNP : ℕ := 102
/-- The step counter. -/ def rCS : ℕ := 103
/-- The step count (`|L|`). -/ def rNS : ℕ := 104
/-- Scratch. -/ def rV : ℕ := 105
/-- Target answer word 0. -/ def rQ0 : ℕ := 106
/-- Target answer word 1. -/ def rQ1 : ℕ := 107
/-- Target answer word 2. -/ def rQ2 : ℕ := 108
/-- Target answer word 3. -/ def rQ3 : ℕ := 109
/-- The search's lower end. -/ def rLo : ℕ := 110
/-- The search's length. -/ def rLn : ℕ := 111
/-- Half the length. -/ def rHf : ℕ := 112
/-- The probe slot. -/ def rMd : ℕ := 113
/-- The search's counter. -/ def rCB : ℕ := 114
/-- The search's step count (`64`). -/ def rNB : ℕ := 115
/-- `1` iff the target was found. -/ def rFd : ℕ := 116

/-! ## Blocks -/

/-- `d := ⌈M[s]/8⌉` (`(s >> 3) + (0 < s & 7)`), scratch `rKc`, `rT2`. -/
def ceil8Ps (d s : ℕ) : List Prim :=
  [.const rKc 3, .op .shr d s rKc, .const rKc 7, .op .and rT2 s rKc, .const rKc 0,
   .op .ltu rT2 rKc rT2, .op .add d d rT2]

/-- `d := min(M[a], M[b])`, branch-free, scratch `rKc`, `rT2`, `rT1`. -/
def minPs (d a b : ℕ) : List Prim :=
  [.op .ltu rT2 a b, .const rKc 0, .op .sub rT2 rKc rT2, .op .xor rT1 a b, .op .and rT1 rT1 rT2,
   .op .xor d b rT1]

/-! ## The walk -/

/-- Before the walk: `|L|`, the first entry's position, `X`'s base. -/
def walkPre : XIR :=
  .seq (.blk [.const rP (BitVec.ofNat 64 (posL + 1)), .const rXA (BitVec.ofNat 64 memX)])
    (readAt rN posL)

/-- One entry: `X[k] := p`; `p += 1 + ⌈|q|/8⌉ + 4`. -/
def walkBody : XIR :=
  .seq (.store rXA rP) (.seq (.input rQL rP)
    (.blk (ceil8Ps rT1 rQL ++ [.op .add rP rP rT1, .const rKc 5, .op .add rP rP rKc,
      .op .add rXA rXA cOne])))

/-- **The walk.** -/
def walkIR : XIR := .seq walkPre (.loopT rCW rN ⟨0, 1, 5⟩ walkBody)

/-! ## The merge sort -/

/-- `d := apos M[q]`, the answer position of the entry at `M[q]`. -/
def aposIR (d q : ℕ) : XIR :=
  .seq (.input rQL q) (.blk (ceil8Ps d rQL ++ [.op .add d d q, .op .add d d cOne]))

/-- Fold in key word `w`: `rF := (a_w < b_w) ∨ (a_w = b_w ∧ rF)`. -/
def cmpWord (w : ℕ) : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 w), .op .add rAd rPa rKc]) (.seq (.input rKa rAd)
    (.seq (.blk [.op .add rAd rPb rKc]) (.seq (.input rKb rAd)
      (.blk [.op .ltu rG rKa rKb, .op .eq rH rKa rKb, .op .and rH rH rF, .op .or rF rG rH]))))

/-- `rF := key(src[i]) < key(src[j])`: the positions, then the answer words `3, 2, 1, 0`. -/
def cmpIR : XIR :=
  .seq (.blk [.op .add rAd rSrc rI]) (.seq (.load rX rAd) (.seq (.blk [.op .add rAd rSrc rJ])
    (.seq (.load rY rAd) (.seq (aposIR rPa rX) (.seq (aposIR rPb rY)
      (.seq (.blk [.op .ltu rF rX rY]) (.seq (cmpWord 3) (.seq (cmpWord 2)
        (.seq (cmpWord 1) (cmpWord 0))))))))))

/-- A new block when both runs are used up: `i := k`, `iE := min(k + w, n)`, `j := iE`,
`jE := min(k + 2w, n)`. -/
def blockIR : XIR :=
  .seq (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH])
    (.ite rG (.blk ([.op .or rI rKk rKk, .op .add rV rKk rW2] ++ minPs rIE rV rN ++
      [.op .or rJ rIE rIE, .op .add rV rV rW2] ++ minPs rJE rV rN)) (.blk []))

/-- One output element: choose, write `dst[k]`, advance. -/
def stepIR : XIR :=
  .seq blockIR (.seq (.blk [.op .ltu rG rI rIE, .op .ltu rH rJ rJE])
    (.seq (.ite rG (.ite rH cmpIR (.blk [.const rF 1])) (.blk [.const rF 0]))
      (.seq (.ite rF (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
          (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]))
        (.seq (.load rV rAd) (.seq (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])
          (.store rAd rV))))))

/-- Before a pass: empty runs, output index `0`, the step count `|L|`. -/
def passPre : XIR :=
  .seq (.blk [.const rI 0, .const rIE 0, .const rJ 0, .const rJE 0, .const rKk 0])
    (readAt rNS posL)

/-- After a pass: swap the bases, `w := min(2w, n)`. -/
def swapPs : List Prim :=
  [.op .or rV rSrc rSrc, .op .or rSrc rDst rDst, .op .or rDst rV rV, .op .add rV rW2 rW2] ++
    minPs rW2 rV rN

/-- **One merge pass.** -/
def passIR : XIR := .seq (.seq passPre (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR)) (.blk swapPs)

/-- Before the sort: `n`, `w = 1`, the bases, the pass count. -/
def sortPre : XIR :=
  .seq (readAt rN posL) (.blk [.const rW2 1, .const rSrc (BitVec.ofNat 64 memX),
    .op .add rDst rSrc rN, .const rNP 64])

/-- **The sort**: 64 passes. -/
def sortIR : XIR := .seq sortPre (.loopK rCP rNP 64 passIR)

/-! ## The lookup (lower bound by binary search) -/

/-- Fold in answer word `w` against the target register `r`:
`rF := (a_w < r) ∨ (a_w = r ∧ rF)`. -/
def cmpTWord (w r : ℕ) : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 w), .op .add rAd rPa rKc]) (.seq (.input rKa rAd)
    (.blk [.op .ltu rG rKa r, .op .eq rH rKa r, .op .and rH rH rF, .op .or rF rG rH]))

/-- `rF :=` the answer of the entry at `rX` is below the target `(rQ0 … rQ3)`, lexicographically
from word 0. -/
def ansLtIR : XIR :=
  .seq (aposIR rPa rX) (.seq (.blk [.const rF 0]) (.seq (cmpTWord 3 rQ3) (.seq (cmpTWord 2 rQ2)
    (.seq (cmpTWord 1 rQ1) (cmpTWord 0 rQ0)))))

/-- One halving step of the lower-bound search on `[lo, lo + len)`; nothing when `len = 0`. -/
def bsBody : XIR :=
  .ite rLn (.seq (.blk [.const rKc 1, .op .shr rHf rLn rKc, .op .add rMd rLo rHf,
      .const rKc (BitVec.ofNat 64 memX), .op .add rAd rMd rKc]) (.seq (.load rX rAd)
    (.seq ansLtIR (.ite rF (.blk [.op .add rLo rMd cOne, .op .sub rLn rLn rHf,
      .op .sub rLn rLn cOne]) (.blk [.op .or rLn rHf rHf]))))) (.blk [])

/-- Equality of answer word `w` with the target register `r`, and-ed into `rFd`. -/
def eqTWord (w r : ℕ) : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 w), .op .add rAd rPa rKc]) (.seq (.input rKa rAd)
    (.blk [.op .eq rH rKa r, .op .and rFd rFd rH]))

/-- After the search: `rFd := lo < n ∧ answer(X[lo]) = target`. -/
def foundIR : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 memX), .op .add rAd rLo rKc]) (.seq (.load rX rAd)
    (.seq (aposIR rPa rX) (.seq (.blk [.op .ltu rFd rLo rN]) (.seq (eqTWord 0 rQ0)
      (.seq (eqTWord 1 rQ1) (.seq (eqTWord 2 rQ2) (eqTWord 3 rQ3)))))))

/-- **The lookup** of the target `(rQ0 … rQ3)` in the sorted `X[0..n)`: `rLo :=` the first slot
whose answer is not below the target (64 halvings), `rFd := 1` iff its answer is the target. -/
def lookIR : XIR :=
  .seq (.seq (readAt rN posL) (.blk [.const rLo 0, .op .or rLn rN rN, .const rNB 64]))
    (.seq (.loopK rCB rNB 64 bsBody) foundIR)

/-- Walk and sort. -/
def idxIR : XIR := .seq walkIR sortIR

/-- **The log index** (the SNARK branch so far): walk and sort. The lookup `lookIR` is a
routine the later phases call with their own targets. -/
def logIR : XIR := idxIR

/-! ## Well formed, cost, size -/

theorem wf_logIR : WF logIR := by
  simp +decide only [logIR, idxIR, lookIR, bsBody, ansLtIR, cmpTWord, eqTWord, foundIR, rQ0, rQ1,
    rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, walkIR, walkPre, walkBody, sortIR, sortPre, passIR,
    passPre, swapPs, stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, WF, Writes,
    Prim.dst, List.mem_append, rA, rN, rP, rXA, rQL, rT1, rT2, rKc, rCW, rW2, rSrc, rDst, rI, rIE,
    rJ, rJE, rKk, rAd, rX, rY, rPa, rPb, rKa, rKb, rF, rG, rH, rCP, rNP, rCS, rNS, rV, regs, cTmp,
    cOne, or_false, and_true, List.cons_append, List.nil_append]

theorem cost_logIR (t : ℕ) : cost logIR t = 2592 + t / 5 * 11871 := by
  simp only [logIR, idxIR, walkIR,
    walkPre, walkBody, sortIR, sortPre, passIR, passPre, swapPs, stepIR, blockIR, cmpIR, cmpWord,
    aposIR, ceil8Ps, minPs, readAt, cost, blkSteps, List.length_cons, List.length_nil,
    List.length_append, Aff.eval, Nat.one_mul]
  norm_num
  omega

theorem sizeIR_logIR : sizeIR logIR ≤ 2 ^ 19 := by
  simp only [logIR, idxIR, walkIR, walkPre, walkBody, sortIR, sortPre, passIR, passPre, swapPs, stepIR,
    blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps, List.length_cons,
    List.length_nil, List.length_append]
  norm_num

theorem outs_logIR (t : ℕ) : outs logIR t = 0 := by
  simp [logIR, idxIR, walkIR, walkPre, walkBody, sortIR, sortPre, passIR, passPre, swapPs, stepIR,
    blockIR, cmpIR, cmpWord, aposIR, readAt, outs]

/-! ## Loop bounds -/

/-- A program with no `loopT`. -/
def NoLoopT : XIR → Prop
  | .seq p q | .ite _ p q => NoLoopT p ∧ NoLoopT q
  | .loopK _ _ _ b => NoLoopT b
  | .loopT .. => False
  | _ => True

theorem safe_of_noLoopT {I : Array Word} {t : ℕ} : ∀ {P : XIR}, NoLoopT P → Safe I t P
  | .blk _, _ => .blk _
  | .load .., _ => .load _ _
  | .store .., _ => .store _ _
  | .input .., _ => .input _ _
  | .out _, _ => .out _
  | .seq _ _, h => .seq (safe_of_noLoopT h.1) (safe_of_noLoopT h.2)
  | .ite _ _ _, h => .ite (safe_of_noLoopT h.1) (safe_of_noLoopT h.2)
  | .loopK .., h => .loopK (safe_of_noLoopT h)

/-- `readAt d pos` leaves tape word `pos` in `d`. -/
theorem rd_readAt (I : Array Word) (s : St) (hM : Inv s.M) {d pos : ℕ} (hd : d < regs)
    (hp : pos < 2 ^ 64) : rd (semXIR I (readAt d pos) s).M d = I.getD pos 0 := by
  have hs := hM.1
  simp only [readAt, semXIR, runPrims, List.foldl, Prim.run]
  simp only [regs, rA] at hs hd
  rw [rd_set_self (by simp only [size_set]; omega), rd_set_self (by simp only [rA]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]

/-- A prefix ending in `readAt d pos` leaves tape word `pos` in `d`. -/
theorem rd_seq_readAt (I : Array Word) (p : XIR) (s : St) (hP : WF p) (hM : Inv s.M) {d pos : ℕ}
    (hd : d < regs) (hp : pos < 2 ^ 64) :
    rd (semXIR I (.seq p (readAt d pos)) s).M d = I.getD pos 0 :=
  rd_readAt I _ (inv_sem I hP hM) hd hp

/-- **The log index's loop bounds**, on a tape whose word `posL` is a count of at most `t / 5`. -/
theorem safe_logIR {I : Array Word} {t : ℕ} (h : (I.getD posL 0).toNat ≤ t / 5) :
    Safe I t logIR := by
  unfold logIR idxIR
  have hcnt : ∀ (p : XIR) (d : ℕ), WF p → d < regs → ∀ s : St, Inv s.M →
      (rd (semXIR I (.seq p (readAt d posL)) s).M d).toNat ≤ Aff.eval ⟨0, 1, 5⟩ t :=
    fun p d hP hd s hM => by
      rw [rd_seq_readAt I p s hP hM hd (by simp only [posL]; omega)]
      simpa [Aff.eval] using h
  refine .seq (.loopT (safe_of_noLoopT (by simp [walkPre, readAt, NoLoopT]))
    (hcnt _ rN (by simp +decide only [WF, Prim.dst, rP, rXA]) (by simp [rN, regs]))
    (safe_of_noLoopT (by simp [walkBody, NoLoopT]))) (.seq (safe_of_noLoopT (by
      simp [sortPre, readAt, NoLoopT])) (.loopK (.seq (.loopT (safe_of_noLoopT (by
      simp [passPre, readAt, NoLoopT])) (hcnt _ rNS (by simp +decide only [WF, Prim.dst, rI, rIE,
        rJ, rJE, rKk])
      (by simp [rNS, regs])) (safe_of_noLoopT (by
        simp [stepIR, blockIR, cmpIR, cmpWord, aposIR, NoLoopT]))) (.blk _))))

/-! ## The domain tape of a SNARK proof -/

theorem length_logEntries (L : Log) : 5 * L.length ≤
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).length := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, bytesWords,
      packBytes_digest_length] at ih ⊢
    omega

theorem tape_getD_posL (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) :
    (extractorInput c π L).getD posL 0 = toWord L.length := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList).length = posL := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      hp, posL, Vector.length_toList, List.length_singleton]
  rw [tape_eq, ← hl]
  exact getD_append_length _ _ _

theorem tape_count_le (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    ((extractorInput c π L).toArray.getD posL 0).toNat ≤ (extractorInput c π L).length / 5 := by
  have hlen : posL + 1 + 5 * L.length ≤ (extractorInput c π L).length := by
    have := length_logEntries L
    have hp : π.size = 797904 := hs.trans piSize_eq
    rw [tape_eq]
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      hp, logWords, List.length_cons, posL, Vector.length_toList, List.length_singleton]
    omega
  rw [getD_toArray, tape_getD_posL c π L hs, toNat_toWord (by omega)]
  omega

/-- **The log index meets the SNARK branch's obligations.** -/
theorem decOk_logIR : DecOk logIR where
  wf := wf_logIR
  safe := fun c π L hs _ ht => safe_logIR (tape_count_le c π L hs ht)
  cost := fun t => by
    rw [cost_logIR]; simp only [decBudget, fuelBase, fuelPerWord]; omega
  outs := fun t => by rw [outs_logIR]; exact Nat.zero_le _
  size := sizeIR_logIR

end FR.X

end G6_FRXLog

section G6_FRXLogSpec

-- New for `flock-recursive` (BLUEPRINT §6.5 `index_spec`; stage S-H2, track L-ext).

/-!
# The walk's semantics (`index_spec`, first half)

On a domain tape of a SNARK proof, `walkIR` leaves in `X[k]` (cell `memX + k`) the tape
position of log entry `k`: `posL + 1 + entryOff L k`, where `entryOff L k` sums the words of the
entries before `k` (`5 + ⌈|q|/8⌉` each). `tape_entry` says the tape word there is `|q_k|`.

**`walk_spec`**: for every `k < |L|`, `rd M (memX + k) = toWord (posL + 1 + entryOff L k)`.

**Parameters (S-H4 pass 5).** The walk and its proofs take the index base `bX` and the tape word `pL`
of `|L|` (`walkIR4`, `walk_spec4`, `tape_entry4`, …); 3.x's statements are their instances at
`memX`, `posL` (`hs_posL`).
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

/-! ## The walk at a parametric base and log position

The index base `bX` and the tape word `pL` of `|L|` are parameters (S-H4 pass 5: one
copy of each proof). 3.x's programs and statements are the instances at `bX = memX`,
`pL = posL` (below); revision 4.1 instantiates them at its own base and log position. -/

section Idx

variable (bX pL : ℕ)

/-- Before the walk: `|L|`, the first entry's position, `X`'s base. -/
def walkPre4 : XIR :=
  .seq (.blk [.const rP (BitVec.ofNat 64 (pL + 1)), .const rXA (BitVec.ofNat 64 bX)])
    (readAt rN pL)


/-- **The walk.** -/
def walkIR4 : XIR := .seq (walkPre4 bX pL) (.loopT rCW rN ⟨0, 1, 5⟩ walkBody)


theorem wf_walkIR4 : WF (walkIR4 bX pL) := by
  simp +decide [walkIR4, walkPre4, walkBody, ceil8Ps, readAt, WF, Writes, Prim.dst, rP, rXA, rN, rA, rQL,
    rT1, rT2, rKc, rCW, cTmp, regs]




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



end Idx

/-! ## 3.x's instances (`memX`, `posL`) -/

/-- 3.x's proof size puts `|L|` at `posL`. -/
theorem hs_posL {π : Proof} (hs : π.size = piSize) : 5 + (π.size + 7) / 8 = posL := by
  rw [hs, piSize_eq, posL]

theorem walkIR_eq : walkIR = walkIR4 memX posL := rfl

/-- **The tape at entry `k`**: its query length. -/
theorem tape_entry (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {k : ℕ}
    (hk : k < L.length) :
    (extractorInput c π L).getD (posL + 1 + entryOff L k) 0 = toWord L[k].1.size :=
  tape_entry4 c π L (hs_posL hs) hk

/-- The end of the log on the tape. -/
theorem tape_entries_end (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) :
    posL + 1 + entryOff L L.length ≤ (extractorInput c π L).length :=
  tape_entries_end4 c π L (hs_posL hs)

/-- **`walk_spec`**: on a domain tape of a SNARK proof, the walk leaves in `X[k]` the tape
position of log entry `k`, for every `k < |L|`. -/
theorem walk_spec (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : memX + L.length ≤ s.M.size) {k : ℕ} (hk : k < L.length) :
    rd (semXIR (extractorInput c π L).toArray walkIR s).M (memX + k) =
      toWord (posL + 1 + entryOff L k) :=
  walk_spec4 (bX := memX) (pL := posL) (by decide) (by decide) (by decide) c π L (hs_posL hs) hq ht s hM hsz hk

end FR.X

end G6_FRXLogSpec
