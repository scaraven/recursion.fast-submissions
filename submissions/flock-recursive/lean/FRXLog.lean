-- New for `flock-recursive` (BLUEPRINT §6.2 step 2; stage S-H2, track L-ext).
import FRXComputes

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
def posL : ℕ := 5 + 100080

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
  simp [logIR, idxIR, lookIR, bsBody, ansLtIR, cmpTWord, eqTWord, foundIR, rQ0, rQ1, rQ2,
    rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, walkIR, walkPre, walkBody, sortIR, sortPre, passIR, passPre, swapPs, stepIR,
    blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, WF, Writes, Prim.dst, List.mem_cons,
    List.mem_append, List.mem_nil_iff, rA, rN, rP, rXA, rQL, rT1, rT2, rKc, rCW, rW2, rSrc, rDst,
    rI, rIE, rJ, rJE, rKk, rAd, rX, rY, rPa, rPb, rKa, rKb, rF, rG, rH, rCP, rNP, rCS, rNS, rV,
    regs, cTmp, cOne]

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
    (hcnt _ rN (by simp [WF, Prim.dst, rP, rXA]) (by simp [rN, regs]))
    (safe_of_noLoopT (by simp [walkBody, NoLoopT]))) (.seq (safe_of_noLoopT (by
      simp [sortPre, readAt, NoLoopT])) (.loopK (.seq (.loopT (safe_of_noLoopT (by
      simp [passPre, readAt, NoLoopT])) (hcnt _ rNS (by simp [WF, Prim.dst, rI, rIE, rJ, rJE, rKk])
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
  have hp : π.size = 800640 := hs.trans piSize_eq
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
    have hp : π.size = 800640 := hs.trans piSize_eq
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
