-- Ported from `flock-recursive` `FRXLookup.lean` (rf-k kk/base 8bff272b) for lvm (WP-3): namespace
-- `Lvm.X`; `ansIdx` (FR's `FRLog`) is defined here, FR's 3.x instances at `posL`/`piSize` are dropped.
import LvmXComputes

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmNodeSoundCircOff`, outside its import closure.)

-- ===== merged from `LvmXLog` (GOLF module merge: `LvmXLog.lean` is now a stub importing `LvmXLookup`) =====
section
-- Ported from `flock-recursive` `FRXLogSpec.lean` (with its former `FRXLog`; rf-k kk/base 8bff272b)
-- for lvm (WP-3): namespace `Lvm.X`; FR's 3.x instances at a fixed `posL`/`piSize` are dropped, the
-- programs take the index base `bX` and the tape word `pL` of `|L|` (FR's `…4` versions; lvm's
-- instance is `bX = memX`, `pL = posL pz`).

section LvmXLogS

/-!
# The log index: walk and sort (§6.2 step 2)

On a SNARK proof of `pz` bytes the log starts at tape word `posL pz = 5 + ⌈pz/8⌉`
(its length `|L|`), its entries at `posL pz + 1`. An entry at position `p` is `|q|` (one word), the
query's `⌈|q|/8⌉` packed words, then the answer (4 words) at `apos p = p + 1 + ⌈|q|/8⌉`.

* `walkIR4 bX pL`: one pass over the entries; `X[k] :=` the position of entry `k`, `X` at `bX`.
  Loop count `|L|` read from `pL` just before the loop, cap `t / 5` (an entry takes at least five
  words).
* `sortIR4 bX pL` (`LvmXSort`): a bottom-up merge sort of `X` (64 passes of width `1, 2, 4, …`,
  capped at `n`, from `X` to `Y = X + n` and back) by the key `(answer words 0…3, position)`,
  lexicographic and unsigned; the position breaks ties, so the first entry with an answer comes
  first (the first-preimage order). 64 is even, so the result is back in `X`.
* `idxIR4 bX pL := walkIR4 ; sortIR4` (`LvmXSort`): `decOk_idx` gives `DecOk` at lvm's instance.
* `lookIR4 bX pL` (`LvmXLookup`): the lower bound of a target answer `(rQ0 … rQ3)` in the sorted
  `X` (64 halvings), `rFd := 1` iff found: a routine the later phases call with their targets.

Semantics: this module (walk), `LvmXSort` (sort), `LvmXLookup` (lookup).
-/

namespace Lvm.X

open RecursionFast

/-- The tape word of `|L|` on a SNARK proof of `pz` bytes: `5 + ⌈pz/8⌉` (the digest, `|π|`, the
proof's packed words). -/
def posL (pz : ℕ) : ℕ := 5 + (pz + 7) / 8

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

/-- One entry: `X[k] := p`; `p += 1 + ⌈|q|/8⌉ + 4`. -/
def walkBody : XIR :=
  .seq (.store rXA rP) (.seq (.input rQL rP)
    (.blk (ceil8Ps rT1 rQL ++ [.op .add rP rP rT1, .const rKc 5, .op .add rP rP rKc,
      .op .add rXA rXA cOne])))

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

/-- After a pass: swap the bases, `w := min(2w, n)`. -/
def swapPs : List Prim :=
  [.op .or rV rSrc rSrc, .op .or rSrc rDst rDst, .op .or rDst rV rV, .op .add rV rW2 rW2] ++
    minPs rW2 rV rN

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

/-- Equality of answer word `w` with the target register `r`, and-ed into `rFd`. -/
def eqTWord (w r : ℕ) : XIR :=
  .seq (.blk [.const rKc (BitVec.ofNat 64 w), .op .add rAd rPa rKc]) (.seq (.input rKa rAd)
    (.blk [.op .eq rH rKa r, .op .and rFd rFd rH]))

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
  rw [rd_set_self (by simp only [size_set]; (clear * - hd hs; omega)), rd_set_self (by simp only [rA]; (clear * - hs; omega)),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]

/-- A prefix ending in `readAt d pos` leaves tape word `pos` in `d`. -/
theorem rd_seq_readAt (I : Array Word) (p : XIR) (s : St) (hP : WF p) (hM : Inv s.M) {d pos : ℕ}
    (hd : d < regs) (hp : pos < 2 ^ 64) :
    rd (semXIR I (.seq p (readAt d pos)) s).M d = I.getD pos 0 :=
  rd_readAt I _ (inv_sem I hP hM) hd hp

/-! ## The domain tape of a SNARK proof -/

theorem length_logEntries (L : Log) : 5 * L.length ≤
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).length := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, bytesWords,
      packBytes_digest_length] at ih ⊢
    (clear * - L e ih; omega)

end Lvm.X

end LvmXLogS

section LvmXLogSpec

/-!
# The walk's semantics (`index_spec`, first half)

On a domain tape of a SNARK proof, `walkIR4 bX pL` leaves in `X[k]` (cell `bX + k`) the tape
position of log entry `k`: `pL + 1 + entryOff L k`, where `entryOff L k` sums the words of the
entries before `k` (`5 + ⌈|q|/8⌉` each). `tape_entry` says the tape word there is `|q_k|`.

**`walk_spec4`**: for every `k < |L|`, `rd M (bX + k) = toWord (pL + 1 + entryOff L k)`.

**Parameters.** The walk and its proofs take the index base `bX` and the tape word `pL`
of `|L|` (`walkIR4`, `walk_spec4`, `tape_entry4`, …); lvm's instance is `memX`, `posL pz`
(`hs_posL`).
-/

namespace Lvm.X

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
  (clear * - e this; omega)

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
      List.getElem?_append_right (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - e L k; omega))), Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
    exact entries_getD L k (by simp at hk; (clear * - hk; omega))

/-! ## The guarded store to the heap -/

theorem rd_storeM {M : Mem} (hM : Inv M) {a v x : ℕ} (ha : rd M a = toWord x) (hx : regs ≤ x)
    (hx2 : x < 2 ^ 64) (hxs : x < M.size) (haT : a ≠ cTmp) (hvT : v ≠ cTmp) {i : ℕ}
    (hi : i ≠ cTmp) : rd (storeM M a v) i = if i = x then rd M v else rd M i := by
  have hT : cTmp < M.size := by have := hM.1; (clear * - this; (try simp only [regs, cTmp] at *); omega)
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
      (by simp only [regs, cTmp] at hi ⊢; (clear * - hi; omega)), hp]
  simp only [regs] at hs hxr
  simp only [walkBody, semXIR, ceil8Ps, runPrims, List.foldl, List.cons_append,
    List.nil_append, Prim.run, rXA, rP, rQL, rT1, rT2, rKc, cOne] at hS hsp hsx hs1 ⊢
  rw [hS]
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · simp (disch := first | decide | (clear * - S s p x hs hsz; omega) | (simp only [size_set]; (clear * - S s p x hs hsz; omega)))
      [rd_set_self, rd_set_ne, XOp.eval, hsp, toNat_toWord hp2]
    change toWord p + ceil8 (I[p]?.getD 0#64) + 5#64 = toWord (p + 5 + (ceil8 (I[p]?.getD 0#64)).toNat)
    generalize ceil8 (I[p]?.getD 0#64) = C
    have := C.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [toWord, BitVec.toNat_add, BitVec.toNat_ofNat]
    (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - p C; omega))
  · simp (disch := first | decide | (clear * - S s p x hs hsz; omega) | (simp only [size_set]; (clear * - S s p x hs hsz; omega)))
      [rd_set_self, rd_set_ne, XOp.eval, hsx, hs1]
    exact (BitVec.ofNat_add x 1).symm
  · rw [← hSi i hi, ← hS]
    simp only [regs] at hi
    simp (disch := first | decide | (clear * - i s p x S hi; omega) | (simp only [size_set]; omega)) [rd_set_ne]

theorem wf_walkBody : WF walkBody := by
  simp [walkBody, ceil8Ps, WF, Prim.dst, rP, rXA, rQL, rT1, rT2, rKc, cTmp]

/-! ## The walk at a parametric base and log position

The index base `bX` and the tape word `pL` of `|L|` are parameters; lvm's instance is
`bX = memX`, `pL = posL pz`. -/

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
      Vector.length_toList, List.length_singleton] <;> (clear * - hs; omega)
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
    (clear * - hs this; omega)
  rw [getD_toArray, tape_getD_posL4 c π L hs, toNat_toWord (by (clear * - L pL c π hs ht hlen; omega))]
  (clear * - hs hlen; omega)



omit hbX hbX2 hpL in
/-- **The tape at entry `k`**: its query length. -/
theorem tape_entry4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) {k : ℕ}
    (hk : k < L.length) :
    (extractorInput c π L).getD (pL + 1 + entryOff L k) 0 = toWord L[k].1.size := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> (clear * - hs; omega)
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, ← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - c π L k; omega))),
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
  (clear * - pL L π hs this; omega)


/-- **The walk's loop**: `m` iterations from entry `j` write `pos j, …` into `X[j], …` and leave
every other heap cell alone. -/
theorem walkLoop4 (I : Array Word) (n : ℕ) (pos : ℕ → ℕ)
    (hpos : ∀ j < n, pos j < 2 ^ 64 ∧ pos (j + 1) = pos j + 5 + (ceil8 (I.getD (pos j) 0)).toNat) :
    ∀ (m j : ℕ) (s : St), j + m = n → Inv s.M → bX + n ≤ s.M.size → bX + n < 2 ^ 64 →
      rd s.M rP = toWord (pos j) → rd s.M rXA = toWord (bX + j) → ∀ i, regs ≤ i →
      rd (iterL (semXIR I walkBody) rCW m s).M i =
        if bX + j ≤ i ∧ i < bX + n then toWord (pos (i - bX)) else rd s.M i
  | 0, j, s, hj, _, _, _, _, _, i, _ => by
    simp only [iterL]; rw [if_neg (by (clear * - hj; omega))]
  | m + 1, j, s, hj, hM, hsz, hn, hp, hx, i, hi => by
    have hjn : j < n := by (clear * - hj; omega)
    obtain ⟨h1, h2, h3⟩ := walkBody_sem I s hM hp hx (hpos j hjn).1
      (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2 hj; omega)) (by (clear * - hj hn hjn; omega)) (by (clear * - hj hsz hjn; omega))
    have hM' : Inv (decS rCW (semXIR I walkBody s)).M := inv_of_frame
      (inv_sem I wf_walkBody hM) (size_decS ..) fun i hi => rd_decS (by simp only [rCW]; (clear * - hi; omega)) _
    have hsz' : (decS rCW (semXIR I walkBody s)).M.size = s.M.size := by
      rw [size_decS, size_sem]
    have hp' : rd (decS rCW (semXIR I walkBody s)).M rP = toWord (pos (j + 1)) := by
      rw [rd_decS (by decide), h1, (hpos j hjn).2]
    have hx' : rd (decS rCW (semXIR I walkBody s)).M rXA = toWord (bX + (j + 1)) := by
      rw [rd_decS (by decide), h2, Nat.add_assoc]
    have hh : ∀ i, regs ≤ i → rd (decS rCW (semXIR I walkBody s)).M i =
        if i = bX + j then toWord (pos j) else rd s.M i := fun i hi => by
      rw [rd_decS (by simp only [rCW, regs] at hi ⊢; (clear * - hi; omega)), h3 i hi]
    simp only [iterL]
    rw [walkLoop4 I n pos hpos m (j + 1) _ (by (clear * - hj; omega)) hM' (by rw [hsz']; exact hsz) hn hp' hx' i hi,
      hh i hi]
    by_cases h : i = bX + j
    · subst h; simp <;> (clear * - hj hjn; omega)
    · by_cases h' : bX + (j + 1) ≤ i ∧ i < bX + n
      · rw [if_pos h', if_pos (by (clear * - hj h'; omega))]
      · rw [if_neg h', if_neg h, if_neg (by (clear * - hj h h'; omega))]


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
    rw [hI, getD_toArray, tape_getD_posL4 c π L hs, toNat_toWord (by (clear * - hs ht hend h5; omega))]
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
    (clear * - hs ht hend hj hq' hend'; omega)
  -- the state at the loop's entry
  have hM1 := inv_sem I (show WF (walkPre4 bX pL) by simp [walkPre4, readAt, WF, Prim.dst, rP, rXA, rN, rA])
    hM
  have hs1 := hM1.1
  have hcnt' : rd (semXIR I (walkPre4 bX pL) s).M rN = I.getD pL 0 :=
    rd_seq_readAt I _ s (by simp [WF, Prim.dst, rP, rXA]) hM (by decide) (by (clear * - hpL hs; omega))
  have hp0 : rd (semXIR I (walkPre4 bX pL) s).M rP = toWord (pL + 1) := by
    have := hM.1; simp only [regs] at this
    simp only [walkPre4, readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rXA, rN, rA]
    simp (disch := first | decide | (clear * - s bX pL c π L k this; omega) | (simp only [size_set]; (clear * - s bX pL c π L k this; omega))) [rd_set_self, rd_set_ne]
    rfl
  have hx0 : rd (semXIR I (walkPre4 bX pL) s).M rXA = toWord bX := by
    have := hM.1; simp only [regs] at this
    simp only [walkPre4, readAt, semXIR, runPrims, List.foldl, Prim.run, rP, rXA, rN, rA]
    simp (disch := first | decide | omega | (simp only [size_set]; (clear * - s bX pL c π L k this; omega))) [rd_set_self, rd_set_ne]
    rfl
  have hc : rCW < (semXIR I (walkPre4 bX pL) s).M.size := by simp only [regs] at hs1; simp only [rCW]; (clear * - hs1; omega)
  have hE : Inv (entryT rCW rN (semXIR I (walkPre4 bX pL) s).M) := inv_of_frame hM1 (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rCW]; (clear * - hi; omega))
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
  have hn : bX + L.length < 2 ^ 64 := by (clear * - hbX2 hs ht hk hend h5 hcnt; omega)
  rw [walkLoop4 hbX hbX2 hpL I L.length (fun j => pL + 1 + entryOff L j) hpos L.length 0 ⟨M0, _⟩ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) hE
    hEs hn hEp hEx (bX + k) (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), if_pos (by (clear * - hk hcnt; omega)),
    Nat.add_sub_cancel_left]



end Idx

/-! ## lvm's instance: `bX = memX`, `pL = posL pz` (WP-13 instantiates the parametric statements) -/

/-- A proof of `pz` bytes puts `|L|` at `posL pz`. -/
theorem hs_posL {pz : ℕ} {π : Proof} (hs : π.size = pz) : 5 + (π.size + 7) / 8 = posL pz := by
  rw [hs, posL]

end Lvm.X

end LvmXLogSpec
end
-- ===== end of `LvmXLog` =====

-- ===== merged from `LvmXSort` (GOLF module merge: `LvmXSort.lean` is now a stub importing `LvmXLookup`) =====
section
-- Ported from `flock-recursive` `FRXSortSim.lean` (with its former `FRXSortSpec`, `FRXMerge`; rf-k kk/base
-- 8bff272b) for lvm (WP-3): namespace `Lvm.X`, FR's 3.x instance (`idxIR_sorted` at `posL`/`piSize`) dropped,
-- `decOk_idx` (lvm's instance of FR's `decOk_logIR`) added.

section LvmXSortSpec


/-!
# The sort's key comparison

`cmpIR` compares the entries at `src[i]` and `src[j]` by the key `keyW I x = [a₀, a₁, a₂, a₃, x]`
(the four answer words of the entry at tape position `x`, then `x` itself), lexicographically
and unsigned (`lexW`). **`cmpIR_sem`**: it leaves `1` in `rF` exactly when `keyLt I x y`.

This is the first brick of the sort's correctness (S-H2-RESULT, Part 3).
-/

namespace Lvm.X

open RecursionFast

/-- The answer position of the entry at tape position `x`, as the program computes it. -/
def aposW (I : Array Word) (x : Word) : Word := ceil8 (I.getD x.toNat 0) + x + 1

/-- The sort key of the entry at `x`: its four answer words, then `x`. -/
def keyW (I : Array Word) (x : Word) : List Word :=
  [I.getD (aposW I x + 0).toNat 0, I.getD (aposW I x + 1).toNat 0,
   I.getD (aposW I x + 2).toNat 0, I.getD (aposW I x + 3).toNat 0, x]

/-- Lexicographic `<` on word lists, unsigned. -/
def lexW : List Word → List Word → Bool
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && lexW as bs)
  | _, _ => false

/-- The sort order. -/
def keyLt (I : Array Word) (x y : Word) : Bool := lexW (keyW I x) (keyW I y)

/-- A 0/1 word. -/
def bW (p : Bool) : Word := if p then 1 else 0

/-- One step of the machine's lexicographic fold. -/
theorem fold_bW (a b : Word) (p : Bool) :
    XOp.or.eval (XOp.ltu.eval a b) (XOp.and.eval (XOp.eq.eval a b) (bW p)) =
      bW (decide (a < b) || (decide (a = b) && p)) := by
  by_cases h1 : a < b <;> by_cases h2 : a = b <;> cases p <;>
    simp [XOp.eval, bW, h1, h2]

theorem cmpWord_sem (I : Array Word) (s : St) (hM : Inv s.M) (w : ℕ) (hw : w < 2 ^ 64) :
    rd (semXIR I (cmpWord w) s).M rF =
      XOp.or.eval (XOp.ltu.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0)
          (I.getD (rd s.M rPb + BitVec.ofNat 64 w).toNat 0))
        (XOp.and.eval (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0)
          (I.getD (rd s.M rPb + BitVec.ofNat 64 w).toNat 0)) (rd s.M rF)) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [cmpWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rPb, rKa, rKb, rG,
    rH, rF]
  simp (disch := first | decide | (clear * - s w hs; omega) | (simp only [size_set]; (clear * - s w hs; omega))) only [rd_set_self,
    rd_set_ne]
  rfl

theorem wf_cmpWord (w : ℕ) : WF (cmpWord w) := by
  simp [cmpWord, WF, Prim.dst, rKc, rAd, rKa, rKb, rG, rH, rF]

theorem cmpWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w : ℕ) {r : ℕ}
    (hr : r = rPa ∨ r = rPb) : rd (semXIR I (cmpWord w) s).M r = rd s.M r :=
  frame I _ s (wf_cmpWord w) hM r (by rcases hr with rfl | rfl <;> decide) (by
    rcases hr with rfl | rfl <;>
      simp [cmpWord, Writes, Prim.dst, rKc, rAd, rKa, rKb, rG, rH, rF, rPa, rPb, cTmp])

theorem aposIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {d q : ℕ}
    (hdq : (d = rPa ∧ q = rX) ∨ (d = rPb ∧ q = rY)) :
    rd (semXIR I (aposIR d q) s).M d = aposW I (rd s.M q) := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  rcases hdq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [aposIR, ceil8Ps, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run, rKc, rT2, rQL, rPa, rPb, rX, rY, cOne] at h1 ⊢
    simp (disch := first | decide | (clear * - s hs; omega) | (simp only [size_set]; (clear * - s hs; omega))) only [rd_set_self,
      rd_set_ne, h1]
    simp only [aposW, ceil8, XOp.eval]
    rfl

theorem wf_aposIR {d q : ℕ} (hd : d = rPa ∨ d = rPb) : WF (aposIR d q) := by
  rcases hd with rfl | rfl <;> simp [aposIR, ceil8Ps, WF, Prim.dst, rQL, rKc, rT2, rPa, rPb]

theorem aposIR_frame (I : Array Word) (s : St) (hM : Inv s.M) {d q r : ℕ}
    (hd : d = rPa ∨ d = rPb) (hr : r ∈ [rX, rY, rPa, rPb, rSrc, rI, rJ]) (hrd : r ≠ d) :
    rd (semXIR I (aposIR d q) s).M r = rd s.M r := by
  refine frame I _ s (wf_aposIR hd) hM r ?_ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hd with rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [aposIR, ceil8Ps, Writes, Prim.dst, rQL, rKc, rT2, rPa, rPb, rX, rY, rSrc, rI, rJ]

/-- **The comparison**: `rF := keyLt I x y` for `x = src[i]`, `y = src[j]`. -/
theorem cmpIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    (hi : regs ≤ (rd s.M rSrc + rd s.M rI).toNat) (hj : regs ≤ (rd s.M rSrc + rd s.M rJ).toNat) :
    rd (semXIR I cmpIR s).M rF = bW (keyLt I (rd s.M (rd s.M rSrc + rd s.M rI).toNat)
      (rd s.M (rd s.M rSrc + rd s.M rJ).toNat)) := by
  set x := rd s.M (rd s.M rSrc + rd s.M rI).toNat
  set y := rd s.M (rd s.M rSrc + rd s.M rJ).toNat
  have hs := hM.1
  simp only [regs] at hs hi hj
  -- the two loads
  have h4 : rd (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M rX = x ∧
      rd (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M rY = y := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, XOp.eval, rAd, rX, rY, rSrc, rI, rJ, x,
      y] at hi hj ⊢
    constructor <;>
      simp (disch := first | decide | omega | (simp only [size_set]; (clear * - s hs; omega))) only [rd_set_self,
        rd_set_ne]
  have hM4 : Inv (semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s)))).M :=
    inv_sem I (P := .load rY rAd) (by simp [WF, rY]) (inv_sem I (by simp [WF, Prim.dst, rAd])
      (inv_sem I (P := .load rX rAd) (by simp [WF, rX]) (inv_sem I (by simp [WF, Prim.dst, rAd])
        hM)))
  rw [cmpIR, semXIR_seq, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (.load rY rAd) (semXIR I (.blk [.op .add rAd rSrc rJ])
      (semXIR I (.load rX rAd) (semXIR I (.blk [.op .add rAd rSrc rI]) s))) = s4 at h4 hM4
  obtain ⟨hx4, hy4⟩ := h4
  -- the answer positions
  rw [semXIR_seq]
  have hM5 := inv_sem I (wf_aposIR (q := rX) (.inl rfl)) hM4
  have ha5 := aposIR_sem I s4 hM4 (.inl ⟨rfl, rfl⟩)
  have hx5 := aposIR_frame I s4 hM4 (q := rX) (.inl rfl) (r := rX) (by simp) (by decide)
  have hy5 := aposIR_frame I s4 hM4 (q := rX) (.inl rfl) (r := rY) (by simp) (by decide)
  generalize semXIR I (aposIR rPa rX) s4 = s5 at hM5 ha5 hx5 hy5
  rw [semXIR_seq]
  have hM6 := inv_sem I (wf_aposIR (q := rY) (.inr rfl)) hM5
  have hb6 := aposIR_sem I s5 hM5 (.inr ⟨rfl, rfl⟩)
  have ha6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rPa) (by simp) (by decide)
  have hx6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rX) (by simp) (by decide)
  have hy6 := aposIR_frame I s5 hM5 (q := rY) (.inr rfl) (r := rY) (by simp) (by decide)
  generalize semXIR I (aposIR rPb rY) s5 = s6 at hM6 hb6 ha6 hx6 hy6
  -- the position comparison
  rw [semXIR_seq]
  have hs6 := hM6.1
  simp only [regs] at hs6
  have hf7 : rd (semXIR I (.blk [.op .ltu rF rX rY]) s6).M rF = bW (lexW [x] [y]) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rF, rX, rY] at hx6 hy6 hx5 hy5 hx4 hy4 ⊢
    rw [rd_set_self (by (clear * - hs6; omega)), hx6, hy6, hx5, hy5, hx4, hy4]
    by_cases h : x < y <;> simp [XOp.eval, bW, lexW, h]
  have hwf7 : WF (.blk [.op .ltu rF rX rY]) := by simp [WF, Prim.dst, rF]
  have hM7 := inv_sem I hwf7 hM6
  have hfr7 : ∀ r, r = rPa ∨ r = rPb → rd (semXIR I (.blk [.op .ltu rF rX rY]) s6).M r =
      rd s6.M r := fun r hr => frame I _ s6 hwf7 hM6 r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;> simp [Writes, Prim.dst, rF, rPa, rPb])
  have ha7 := hfr7 rPa (.inl rfl)
  have hb7 := hfr7 rPb (.inr rfl)
  generalize semXIR I (.blk [.op .ltu rF rX rY]) s6 = s7 at hf7 hM7 ha7 hb7
  -- the four answer words
  have step : ∀ (s' : St), Inv s'.M → rd s'.M rPa = aposW I x → rd s'.M rPb = aposW I y →
      ∀ (w : ℕ) (p : Bool), w < 4 → rd s'.M rF = bW p →
      rd (semXIR I (cmpWord w) s').M rF = bW (decide (I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 <
          I.getD (aposW I y + BitVec.ofNat 64 w).toNat 0) ||
        (decide (I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 =
          I.getD (aposW I y + BitVec.ofNat 64 w).toNat 0) && p)) ∧
      Inv (semXIR I (cmpWord w) s').M ∧ rd (semXIR I (cmpWord w) s').M rPa = aposW I x ∧
      rd (semXIR I (cmpWord w) s').M rPb = aposW I y := fun s' hM' ha hb w p hw hf =>
    ⟨by rw [cmpWord_sem I s' hM' w (by (clear * - hw; omega)), ha, hb, hf, fold_bW],
     inv_sem I (wf_cmpWord w) hM', by rw [cmpWord_frame I s' hM' w (.inl rfl), ha],
     by rw [cmpWord_frame I s' hM' w (.inr rfl), hb]⟩
  rw [ha6, ha5, hx4] at ha7
  rw [hb6, hy5, hy4] at hb7
  rw [semXIR_seq]
  obtain ⟨f3, m3, a3, b3⟩ := step s7 hM7 ha7 hb7 3 _ (by decide) hf7
  generalize semXIR I (cmpWord 3) s7 = s8 at f3 m3 a3 b3
  rw [semXIR_seq]
  obtain ⟨f2, m2, a2, b2⟩ := step s8 m3 a3 b3 2 _ (by decide) f3
  generalize semXIR I (cmpWord 2) s8 = s9 at f2 m2 a2 b2
  rw [semXIR_seq]
  obtain ⟨f1, m1, a1, b1⟩ := step s9 m2 a2 b2 1 _ (by decide) f2
  generalize semXIR I (cmpWord 1) s9 = s10 at f1 m1 a1 b1
  obtain ⟨f0, -, -, -⟩ := step s10 m1 a1 b1 0 _ (by decide) f1
  rw [f0]
  rfl

end Lvm.X

end LvmXSortSpec

section LvmXMerge


/-!
# The merge pass, as a pure state machine

`mstep` is one step of `stepIR` on abstract state (`MS`: the heads `i`, `j`, the run ends `iE`,
`jE`, the output index `k`, the destination as a function, and a ghost block start `lo`).
`Good` is the invariant; **`pass_ok`**: `n` steps from the empty state, on a source whose runs of
width `w` are strictly sorted and which is injective on `[0, n)`, leave a destination whose
blocks of width `2w` are strictly sorted and draw their values from the same source block.
No permutation is tracked (S-H2-RESULT, Part 3, steps 3–4).
-/

namespace Lvm.X

open RecursionFast

/-- A strict order, total on distinct words (`keyLt`'s properties, `keyLt_order`). -/
structure SOrd (lt : Word → Word → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

/-- The abstract state of a merge pass. -/
structure MS where
  lo : ℕ
  i : ℕ
  iE : ℕ
  j : ℕ
  jE : ℕ
  k : ℕ
  dst : ℕ → Word

/-- `f` with `v` at `k`. -/
def upd (f : ℕ → Word) (k : ℕ) (v : Word) : ℕ → Word := fun a => if a = k then v else f a

/-- A new block when both runs are used up (`blockIR`). -/
def bstart (n w : ℕ) (s : MS) : MS :=
  if s.i = s.iE ∧ s.j = s.jE then
    { s with lo := s.k, i := s.k, iE := min (s.k + w) n, j := min (s.k + w) n,
             jE := min (s.k + w + w) n }
  else s

/-- The left head goes next. -/
def takeL (lt : Word → Word → Bool) (src : ℕ → Word) (s : MS) : Bool :=
  decide (s.i < s.iE) && (!decide (s.j < s.jE) || lt (src s.i) (src s.j))

/-- **One step** (`stepIR`). -/
def mstep (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (s : MS) : MS :=
  let s := bstart n w s
  if takeL lt src s then { s with dst := upd s.dst s.k (src s.i), i := s.i + 1, k := s.k + 1 }
  else { s with dst := upd s.dst s.k (src s.j), j := s.j + 1, k := s.k + 1 }

/-- The invariant. -/
structure Good (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (s : MS) : Prop where
  ord : s.lo ≤ s.i ∧ s.i ≤ s.iE ∧ s.iE ≤ s.j ∧ s.j ≤ s.jE ∧ s.jE ≤ n
  ends : s.iE ≤ s.lo + w ∧ s.jE ≤ s.lo + 2 * w ∧ (s.j < s.jE → s.iE = s.lo + w) ∧
    (s.jE = min (s.lo + 2 * w) n ∨ s.jE = s.lo)
  algn : 2 * w ∣ s.lo
  kk : s.k + s.iE = s.i + s.j
  srt : ∀ a b, s.lo ≤ a → a < b → b < s.k → lt (s.dst a) (s.dst b) = true
  mem : ∀ a, s.lo ≤ a → a < s.k → ∃ c, s.lo ≤ c ∧ c < s.jE ∧ s.dst a = src c
  heads : ∀ a, s.lo ≤ a → a < s.k → (s.i < s.iE → lt (s.dst a) (src s.i) = true) ∧
    (s.j < s.jE → lt (s.dst a) (src s.j) = true)
  dmem : ∀ a, a < s.lo → ∃ c, c < s.lo ∧ c / (2 * w) = a / (2 * w) ∧ s.dst a = src c
  dsrt : ∀ a b, a < b → b < s.lo → a / (2 * w) = b / (2 * w) → lt (s.dst a) (s.dst b) = true

theorem div_eq_of_block {w m a : ℕ} (h1 : w * m ≤ a) (h2 : a < w * m + w) : a / w = m :=
  Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h1) (by rw [Nat.succ_mul, Nat.mul_comm]; exact h2)

theorem good_init (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (d : ℕ → Word) :
    Good lt src n w ⟨0, 0, 0, 0, 0, 0, d⟩ where
  ord := by simp
  ends := by simp
  algn := dvd_zero _
  kk := rfl
  srt := fun _ _ _ _ h => absurd h (by dsimp only; (clear * -; omega))
  mem := fun _ _ h => absurd h (by dsimp only; (clear * -; omega))
  heads := fun _ _ h => absurd h (by dsimp only; (clear * -; omega))
  dmem := fun _ h => absurd h (by dsimp only; (clear * -; omega))
  dsrt := fun _ _ _ h => absurd h (by dsimp only; (clear * -; omega))

/-- **`bstart` keeps the invariant**, and afterwards a head is available. -/
theorem good_bstart {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (hw : 0 < w)
    {s : MS} (hg : Good lt src n w s) (hk : s.k < n) :
    Good lt src n w (bstart n w s) ∧ ((bstart n w s).i < (bstart n w s).iE ∨
      (bstart n w s).j < (bstart n w s).jE) ∧ (bstart n w s).k = s.k ∧
      (bstart n w s).dst = s.dst := by
  unfold bstart
  split
  · next h =>
    obtain ⟨hi, hj⟩ := h
    obtain ⟨o1, o2, o3, o4, o5⟩ := hg.ord
    obtain ⟨e1, e2, e3, e4⟩ := hg.ends
    have hkj : s.k = s.jE := by have := hg.kk; (clear * - hi hj this; omega)
    obtain ⟨m, hm⟩ := hg.algn
    -- the closed block ends aligned: `jE = lo + 2w` or the block is empty
    have hal : 2 * w ∣ s.k := by
      rw [hkj]
      rcases e4 with e4 | e4
      · exact ⟨m + 1, by rw [e4, Nat.min_eq_left (by (clear * - hk hkj hm e4; omega)), hm]; ring⟩
      · exact ⟨m, by rw [e4, hm]⟩
    have hblk : ∀ a, s.lo ≤ a → a < s.jE → a / (2 * w) = m := fun a h1 h2 =>
      div_eq_of_block (by (clear * - hm h1; omega)) (by (clear * - e2 hm h2; omega))
    refine ⟨⟨by simp; (clear * - hk hkj; omega), ⟨by simp, by simp; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - s w n; omega)), fun h => by simp at h ⊢; (clear * - hkj h; omega),
      Or.inl (by simp; (clear * - hkj; omega))⟩, hal, by simp,
      fun a b ha hab hb => absurd hb (by simp at ha ⊢; (clear * - hkj ha hab; omega)),
      fun a ha hak => absurd hak (by simp at ha ⊢; (clear * - ha; omega)),
      fun a ha hak => absurd hak (by simp at ha ⊢; (clear * - ha; omega)), fun a ha => ?_,
      fun a b hab hb hd => ?_⟩, by simp; (clear * - hw hk hkj; omega), rfl, rfl⟩
    · simp only at ha ⊢
      by_cases hlo : a < s.lo
      · obtain ⟨c, hc, hcd, hce⟩ := hg.dmem a hlo
        exact ⟨c, by (clear * - hi hj o1 o3 hkj hm hc; omega), hcd, hce⟩
      · obtain ⟨c, hc1, hc2, hce⟩ := hg.mem a (by (clear * - hm hlo; omega)) (by omega)
        exact ⟨c, by (clear * - hkj hc2; omega), by rw [hblk c hc1 hc2, hblk a (by (clear * - hm hlo; omega)) (by (clear * - hkj ha; omega))], hce⟩
    · simp only at hb hd ⊢
      by_cases hb' : b < s.lo
      · exact hg.dsrt a b hab hb' hd
      · by_cases ha' : s.lo ≤ a
        · exact hg.srt a b ha' hab (by (clear * - hb; omega))
        · exfalso
          have h1 : a / (2 * w) < m := by
            rw [Nat.div_lt_iff_lt_mul (by (clear * - hw; omega))]; rw [hm] at ha'; linarith
          have h2 : b / (2 * w) = m := hblk b (by (clear * - hm hb'; omega)) (by (clear * - hkj hb; omega))
          (clear * - hd h1 h2; omega)
  · next h =>
    refine ⟨hg, ?_, rfl, rfl⟩
    have := hg.ord
    (clear * - h this; omega)

/-- **One step keeps the invariant** and advances `k`. -/
theorem good_mstep {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w)
    (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b)
    {s : MS} (hg : Good lt src n w s) (hk : s.k < n) :
    Good lt src n w (mstep lt src n w s) ∧ (mstep lt src n w s).k = s.k + 1 := by
  obtain ⟨hg', hav, hkk, -⟩ := good_bstart hw hg hk
  unfold mstep
  generalize bstart n w s = t at hg' hav hkk
  rw [← hkk] at hk ⊢
  obtain ⟨o1, o2, o3, o4, o5⟩ := hg'.ord
  obtain ⟨e1, e2, e3, e4⟩ := hg'.ends
  obtain ⟨m, hm⟩ := hg'.algn
  -- the runs: `[lo, iE)` is run `2m`, `[iE, jE)` is run `2m + 1`
  have e2m : w * (2 * m) = 2 * w * m := by ring
  have e2m1 : w * (2 * m + 1) = 2 * w * m + w := by ring
  have runL : ∀ a, t.lo ≤ a → a < t.iE → a / w = 2 * m := fun a h1 h2 =>
    div_eq_of_block (by rw [e2m]; (clear * - hm e2m h1; omega)) (by rw [e2m]; (clear * - e1 hm e2m e2m1 h2; omega))
  have runR : ∀ a, t.j < t.jE → t.iE ≤ a → a < t.jE → a / w = 2 * m + 1 := fun a hj h1 h2 => by
    have := e3 hj
    exact div_eq_of_block (by rw [e2m1]; (clear * - hm e2m e2m1 h1 this; omega)) (by rw [e2m1]; (clear * - e2 hm e2m e2m1 h2; omega))
  dsimp only
  by_cases hL : takeL lt src t = true
  · rw [if_pos hL]
    simp only [takeL, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt] at hL
    obtain ⟨hiL, hc⟩ := hL
    refine ⟨⟨by simp; (clear * - o1 o3 o4 o5 hm e2m hiL; omega), ⟨by simp; omega, by simp; omega, fun h => by simp at h; exact e3 h,
      by simp; exact e4⟩,
      ⟨m, hm⟩, by simp; have := hg'.kk; (clear * - hkk this; omega), ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only [upd]
    · intro a b ha hab hb
      rw [if_neg (by (clear * - hkk hab hb; omega))]
      by_cases hbk : b = t.k
      · rw [if_pos hbk]; exact (hg'.heads a ha (by (clear * - hkk hab hbk; omega))).1 hiL
      · rw [if_neg hbk]; exact hg'.srt a b ha hab (by (clear * - hkk hb hbk; omega))
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']; exact ⟨t.i, by (clear * - o1; omega), by (clear * - o3 o4 hiL; omega), rfl⟩
      · rw [if_neg hak']; exact hg'.mem a ha (by (clear * - hkk hak hak'; omega))
    · intro a ha hak
      have hiR : ∀ h : t.j < t.jE, lt (src t.i) (src t.j) = true := fun h => by
        rcases hc with hc | hc
        · (clear * - h hc; omega)
        · exact hc
      by_cases hak' : a = t.k
      · rw [if_pos hak']
        exact ⟨fun h => hsrt _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - t; omega))) (by (clear * - o3 o4 o5 h; omega)) (by rw [runL _ (by omega) (by omega),
          runL _ (by (clear * - o1 hm e2m; omega)) h]), hiR⟩
      · rw [if_neg hak']
        have hh := hg'.heads a ha (by (clear * - hkk hak hak'; omega))
        exact ⟨fun h => ho.trans _ _ _ (hh.1 hiL) (hsrt _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - t; omega))) (by (clear * - o3 o4 o5 h; omega))
          (by rw [runL _ (by (clear * - o1; omega)) (by (clear * - hiL; omega)), runL _ (by (clear * - o1 hm e2m; omega)) h])), hh.2⟩
    · intro a ha
      have := hg'.kk
      rw [if_neg (by (clear * - hkk o1 o3 hm e2m ha this; omega))]; exact hg'.dmem a ha
    · intro a b hab hb hd
      have := hg'.kk
      rw [if_neg (by (clear * - hkk o1 o3 hm e2m hab hb this; omega)), if_neg (by (clear * - hkk o1 o3 hm e2m hb this; omega))]; exact hg'.dsrt a b hab hb hd
  · rw [if_neg hL]
    simp only [takeL, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt, not_and, not_or] at hL
    -- the right head is available, and below the left head when that one is
    have hjR : t.j < t.jE := by
      by_contra h
      rcases hav with h' | h'
      · exact (hL h').1 (by (clear * - o4 h; omega))
      · exact h h'
    have hji : t.i < t.iE → lt (src t.j) (src t.i) = true := fun h => by
      have hne : src t.i ≠ src t.j := fun he => by
        have := hinj _ _ (by (clear * - o3 o5 hjR h; omega)) (by (clear * - o5 hjR; omega)) he; (clear * - o3 h this; omega)
      rcases ho.total _ _ hne with h1 | h1
      · exact absurd h1 (by have := (hL h).2; simpa using this)
      · exact h1
    refine ⟨⟨by simp; (clear * - o1 o2 o3 o5 hm e2m hjR; omega), ⟨by simp; omega, by simp; omega, fun h => by
      simp at h; exact e3 (by (clear * - hjR; omega)), by simp; exact e4⟩, ⟨m, hm⟩, by simp; have := hg'.kk; (clear * - hkk this; omega), ?_, ?_, ?_, ?_,
      ?_⟩, rfl⟩ <;> simp only [upd]
    · intro a b ha hab hb
      rw [if_neg (by (clear * - hkk hab hb; omega))]
      by_cases hbk : b = t.k
      · rw [if_pos hbk]; exact (hg'.heads a ha (by (clear * - hkk hab hbk; omega))).2 hjR
      · rw [if_neg hbk]; exact hg'.srt a b ha hab (by (clear * - hkk hb hbk; omega))
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']; exact ⟨t.j, by (clear * - o1 o2 o3 hm e2m; omega), by omega, rfl⟩
      · rw [if_neg hak']; exact hg'.mem a ha (by (clear * - hkk hak hak'; omega))
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']
        exact ⟨hji, fun h => hsrt _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - t; omega))) (by (clear * - o5 h; omega)) (by rw [runR _ hjR (by omega) (by omega),
          runR _ hjR (by (clear * - o3; omega)) h])⟩
      · rw [if_neg hak']
        have hh := hg'.heads a ha (by (clear * - hkk hak hak'; omega))
        exact ⟨hh.1, fun h => ho.trans _ _ _ (hh.2 hjR) (hsrt _ _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - t; omega))) (by (clear * - o5 h; omega))
          (by rw [runR _ hjR (by (clear * - o3; omega)) (by (clear * - hjR; omega)), runR _ hjR (by (clear * - o3; omega)) h]))⟩
    · intro a ha
      have := hg'.kk
      rw [if_neg (by (clear * - hkk o1 o3 hm e2m ha this; omega))]; exact hg'.dmem a ha
    · intro a b hab hb hd
      have := hg'.kk
      rw [if_neg (by (clear * - hkk o1 o3 hm e2m hab hb this; omega)), if_neg (by (clear * - hkk o1 o3 hm e2m hb this; omega))]; exact hg'.dsrt a b hab hb hd

/-! ## One pass -/

/-- `m` steps. -/
def mrun (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) : ℕ → MS → MS
  | 0, s => s
  | m + 1, s => mrun lt src n w m (mstep lt src n w s)

/-- **The pass**: `n` steps from the empty state. -/
def passF (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (d : ℕ → Word) : ℕ → Word :=
  (mrun lt src n w n ⟨0, 0, 0, 0, 0, 0, d⟩).dst

theorem good_mrun {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w) (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) :
    ∀ m (s : MS), Good lt src n w s → s.k + m ≤ n →
      Good lt src n w (mrun lt src n w m s) ∧ (mrun lt src n w m s).k = s.k + m
  | 0, s, hg, _ => ⟨hg, rfl⟩
  | m + 1, s, hg, hm => by
    obtain ⟨h1, h2⟩ := good_mstep ho hw hsrt hinj hg (by (clear * - s n w m hm; omega))
    obtain ⟨h3, h4⟩ := good_mrun ho hw hsrt hinj m _ h1 (by (clear * - lt src n w s m hm h2; omega))
    exact ⟨h3, by simp only [mrun]; rw [h4, h2]; (clear * - s m lt src n w; omega)⟩

/-- What a pass delivers. -/
structure PassOut (lt : Word → Word → Bool) (src d : ℕ → Word) (n w : ℕ) : Prop where
  mem : ∀ a < n, ∃ c < n, c / (2 * w) = a / (2 * w) ∧ d a = src c
  srt : ∀ a b, a < b → b < n → a / (2 * w) = b / (2 * w) → lt (d a) (d b) = true

/-- **`pass_ok`**: a pass on a source with strictly sorted runs of width `w`, injective on
`[0, n)`, gives strictly sorted blocks of width `2w` drawn from the same source blocks. -/
theorem pass_ok {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w) (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) (d : ℕ → Word) :
    PassOut lt src (passF lt src n w d) n w := by
  obtain ⟨hg, hk⟩ := good_mrun ho hw hsrt hinj n _ (good_init lt src n w d) (by simp)
  simp only [Nat.zero_add] at hk
  unfold passF
  generalize mrun lt src n w n ⟨0, 0, 0, 0, 0, 0, d⟩ = s at hg hk
  obtain ⟨o1, o2, o3, o4, o5⟩ := hg.ord
  obtain ⟨e1, e2, -, -⟩ := hg.ends
  obtain ⟨m, hm⟩ := hg.algn
  have hkk := hg.kk
  have hblk : ∀ a, s.lo ≤ a → a < s.jE → a / (2 * w) = m := fun a h1 h2 =>
    div_eq_of_block (by (clear * - hm h1; omega)) (by (clear * - e2 hm h2; omega))
  have hlt : ∀ a, a < s.lo → a / (2 * w) < m := fun a ha => by
    rw [Nat.div_lt_iff_lt_mul (by (clear * - hw; omega))]; rw [hm] at ha; linarith
  refine ⟨fun a ha => ?_, fun a b hab hb hd => ?_⟩
  · by_cases hlo : a < s.lo
    · obtain ⟨c, hc, hcd, hce⟩ := hg.dmem a hlo
      exact ⟨c, by (clear * - hk o1 o3 hm hkk hc; omega), hcd, hce⟩
    · obtain ⟨c, hc1, hc2, hce⟩ := hg.mem a (by (clear * - hm hlo; omega)) (by (clear * - hk hkk ha; omega))
      exact ⟨c, by (clear * - hk o5 hkk hc2; omega), by rw [hblk c hc1 hc2, hblk a (by (clear * - hm hlo; omega)) (by (clear * - hk o2 o4 o5 hkk ha; omega))], hce⟩
  · by_cases hb' : b < s.lo
    · exact hg.dsrt a b hab hb' hd
    · by_cases ha' : s.lo ≤ a
      · exact hg.srt a b ha' hab (by (clear * - hk hkk hb; omega))
      · exfalso
        have := hlt a (by (clear * - hm ha'; omega))
        have := hblk b (by (clear * - hm hb'; omega)) (by (clear * - hk o2 o4 hkk hb; omega))
        omega

/-- A pass's output is injective on `[0, n)`. -/
theorem PassOut.inj {lt : Word → Word → Bool} {src d : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hp : PassOut lt src d n w) (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) :
    ∀ a b, a < n → b < n → d a = d b → a = b := by
  intro a b ha hb he
  by_contra hne
  have key : ∀ a b, a < b → b < n → d a = d b → False := fun a b hab hb he => by
    by_cases hd : a / (2 * w) = b / (2 * w)
    · have := hp.srt a b hab hb hd
      rw [he, ho.irrefl] at this; cases this
    · obtain ⟨c, hc, hcb, hca⟩ := hp.mem a (by (clear * - hab hb; omega))
      obtain ⟨c', hc', hcb', hca'⟩ := hp.mem b hb
      have := hinj c c' hc hc' (by rw [← hca, ← hca', he])
      subst this
      exact hd (hcb.symm.trans hcb')
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key a b h hb he
  · exact key b a h ha he.symm

/-- The runs of the next width `min(2w, n)` are sorted. -/
theorem PassOut.runs {lt : Word → Word → Bool} {src d : ℕ → Word} {n w : ℕ}
    (hp : PassOut lt src d n w) :
    ∀ a b, a < b → b < n → a / min (2 * w) n = b / min (2 * w) n → lt (d a) (d b) = true := by
  intro a b hab hb hd
  refine hp.srt a b hab hb ?_
  by_cases h : 2 * w ≤ n
  · rwa [Nat.min_eq_left h] at hd
  · rw [Nat.div_eq_of_lt (by (clear * - hab hb h; omega)), Nat.div_eq_of_lt (by (clear * - hb h; omega))]

/-! ## 64 passes -/

/-- The run widths: `1`, then `min(2w, n)`. -/
def wseq (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | p + 1 => min (2 * wseq n p) n

theorem wseq_eq {n : ℕ} (hn : 0 < n) : ∀ p, wseq n p = min (2 ^ p) n
  | 0 => by simp [wseq]; omega
  | p + 1 => by
    rw [wseq, wseq_eq hn p, pow_succ]
    rcases Nat.le_total (2 ^ p) n with h | h
    · rw [Nat.min_eq_left h]; (clear * - p n; omega)
    · rw [Nat.min_eq_right h]; (clear * - n p hn h; omega)

/-- **The sort's correctness, pure form**: if each array is a pass of the previous one at width
`wseq n p`, starting from an array `X 0` injective on `[0, n)`, then after 64 passes the array is
strictly sorted on `[0, n)` and holds exactly the values of `X 0` there. -/
theorem passes_ok {lt : Word → Word → Bool} (ho : SOrd lt) {n : ℕ} (hn : n < 2 ^ 63)
    (X : ℕ → ℕ → Word) (ds : ℕ → ℕ → Word)
    (hX : ∀ p, ∀ a < n, X (p + 1) a = passF lt (X p) n (wseq n p) (ds p) a)
    (hinj : ∀ a b, a < n → b < n → X 0 a = X 0 b → a = b) :
    (∀ a b, a < b → b < n → lt (X 64 a) (X 64 b) = true) ∧
    (∀ a < n, ∃ c < n, X 64 a = X 0 c) ∧ (∀ c < n, ∃ a < n, X 64 a = X 0 c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact ⟨fun _ _ _ h => absurd h (by (clear * - h; omega)), fun _ h => absurd h (by (clear * - h; omega)),
      fun _ h => absurd h (by (clear * - h; omega))⟩
  -- the invariant after `p` passes
  have inv : ∀ p, (∀ a b, a < n → b < n → X p a = X p b → a = b) ∧
      (∀ a b, a < b → b < n → a / wseq n p = b / wseq n p → lt (X p a) (X p b) = true) ∧
      (∀ a < n, ∃ c < n, X p a = X 0 c) := by
    intro p
    induction p with
    | zero =>
      refine ⟨hinj, fun a b hab _ hd => ?_, fun a ha => ⟨a, ha, rfl⟩⟩
      simp only [wseq, Nat.div_one] at hd; (clear * - hab hd; omega)
    | succ p ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      have hw : 0 < wseq n p := by rw [wseq_eq hn0]; have := Nat.one_le_two_pow (n := p); (clear * - hn hn0 this; omega)
      have hp := pass_ok ho hw i2 i1 (ds p)
      have hp' : PassOut lt (X p) (X (p + 1)) n (wseq n p) :=
        ⟨fun a ha => by rw [hX p a ha]; exact hp.mem a ha, fun a b hab hb hd => by
          rw [hX p a (by (clear * - hab hb; omega)), hX p b hb]; exact hp.srt a b hab hb hd⟩
      refine ⟨hp'.inj ho i1, hp'.runs, fun a ha => ?_⟩
      obtain ⟨c, hc, -, hce⟩ := hp'.mem a ha
      obtain ⟨c', hc', hce'⟩ := i3 c hc
      exact ⟨c', hc', hce.trans hce'⟩
  obtain ⟨i1, i2, i3⟩ := inv 64
  have hw64 : wseq n 64 = n := by rw [wseq_eq hn0]; exact Nat.min_eq_right (by (clear * - hn hn0; omega))
  refine ⟨fun a b hab hb => i2 a b hab hb (by
    rw [hw64, Nat.div_eq_of_lt (by (clear * - hw64 hab hb; omega)), Nat.div_eq_of_lt hb]), i3, fun c hc => ?_⟩
  -- completeness: `n` distinct values among the `n` values of `X 0`
  classical
  have hsub : (Finset.range n).image (X 64) ⊆ (Finset.range n).image (X 0) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_range] at hv ⊢
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨c, hc, he⟩ := i3 a ha
    exact ⟨c, hc, he.symm⟩
  have hcard : ((Finset.range n).image (X 0)).card ≤ ((Finset.range n).image (X 64)).card := by
    rw [Finset.card_image_of_injOn (fun a ha b hb he => i1 a b (by simpa using ha)
      (by simpa using hb) he)]
    exact (Finset.card_image_le).trans (by simp)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : X 0 c ∈ (Finset.range n).image (X 64) := by
    rw [heq]; exact Finset.mem_image_of_mem _ (by simpa using hc)
  simp only [Finset.mem_image, Finset.mem_range] at this
  exact this

/-! ## `keyLt` is a strict total order -/

theorem lexW_irrefl : ∀ l : List Word, lexW l l = false
  | [] => rfl
  | a :: l => by simp [lexW, lexW_irrefl l]

theorem lexW_trans : ∀ l₁ l₂ l₃ : List Word, lexW l₁ l₂ = true → lexW l₂ l₃ = true →
    lexW l₁ l₃ = true
  | a :: l₁, b :: l₂, c :: l₃, h1, h2 => by
    simp only [lexW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · left; rw [BitVec.lt_def] at *; (clear * - a c b h1 h2; omega)
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, lexW_trans l₁ l₂ l₃ h1 h2⟩
  | [], _, _, h, _ => by simp [lexW] at h
  | _ :: _, [], _, h, _ => by simp [lexW] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexW] at h

theorem lexW_total : ∀ l₁ l₂ : List Word, l₁.length = l₂.length → l₁ ≠ l₂ →
    lexW l₁ l₂ = true ∨ lexW l₂ l₁ = true
  | [], [], _, h => absurd rfl h
  | a :: l₁, b :: l₂, hl, h => by
    simp only [lexW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hab : a = b
    · subst hab
      rcases lexW_total l₁ l₂ (by simpa using hl) (fun e => h (by rw [e])) with h' | h'
      · exact .inl (.inr ⟨rfl, h'⟩)
      · exact .inr (.inr ⟨rfl, h'⟩)
    · have hne : a.toNat ≠ b.toNat := fun e => hab (BitVec.eq_of_toNat_eq e)
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact .inl (.inl (BitVec.lt_def.mpr h'))
      · exact .inr (.inl (BitVec.lt_def.mpr h'))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **`keyLt I` is a strict total order** (the position is the key's last word). -/
theorem keyLt_order (I : Array Word) : SOrd (keyLt I) where
  irrefl := fun a => lexW_irrefl _
  trans := fun a b c => lexW_trans _ _ _
  total := fun a b hab => lexW_total _ _ (by simp [keyW]) (fun e => hab (by
    simp only [keyW, List.cons.injEq] at e; exact e.2.2.2.2.1))

end Lvm.X

end LvmXMerge

section LvmXSortSim


/-!
# Simulating the merge sort: `stepIR` by `mstep`, `passIR` by `passF`, `sortIR` by `passes_ok`

* Word-level facts: the branch-free `min` (`minW_toWord`), the `eq`/`ltu` flags.
* `Rel S D n w src M σ`: the registers hold the pass state `σ : MS` (`Regs`), the heap holds the
  source at `S + ·` and `σ.dst` at `D + ·` on `[0, n)`; `Lay` is the pass layout.
* `blockIR_sem`, `choose_sem`, `tail_sem`, **`stepIR_sem`**: one step is `mstep (keyLt I)`.
* **`passIR_sem`**: a pass writes `passF` of the source into the destination, swaps the bases and
  sets `w := min(2w, n)`.
* **`sortIR_sem`**: 64 passes leave `X[0..n)` strictly sorted by `keyLt` and holding exactly the
  initial (distinct) values (`passes_ok`).
* **`idxIR4_sorted`**: on a domain tape of a SNARK proof, after `idxIR4` `X[0..|L|)` holds exactly
  the log entries' tape positions, sorted by (answer, position).

(S-H2-RESULT, Parts 5 and 6.)

**Parameters.** The sort and the index take the index base `bX` and the tape word `pL`
of `|L|` (`sortIR4`, `idxIR4`, `idxIR4_sorted`); lvm's instance is `memX`, `posL pz`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-- The branch-free `min` of `minPs`: `b ^^^ ((a ^^^ b) &&& (0 - [a < b]))`. -/
theorem minW (a b : Word) :
    b ^^^ ((a ^^^ b) &&& (0 - XOp.ltu.eval a b)) = if a < b then a else b := by
  by_cases h : a < b
  · have h1 : (0 : Word) - 1 = BitVec.allOnes 64 := by decide
    simp only [XOp.eval, h, ↓reduceIte, h1, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]
  · simp only [XOp.eval, h, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

/-- `min` of two small numbers as words. -/
theorem minW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    toWord b ^^^ ((toWord a ^^^ toWord b) &&& (0 - XOp.ltu.eval (toWord a) (toWord b))) =
      toWord (min a b) := by
  rw [minW]
  by_cases h : a < b
  · rw [if_pos ((toWord_lt_toWord ha hb).2 h), Nat.min_eq_left h.le]
  · rw [if_neg (fun h' => h ((toWord_lt_toWord ha hb).1 h')), Nat.min_eq_right (by (clear * - h; omega))]

/-- The `eq` flag on small numbers. -/
theorem eqW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.eq.eval (toWord a) (toWord b) = bW (decide (a = b)) := by
  simp only [XOp.eval, bW]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg (fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_toWord ha, toNat_toWord hb] at this))]
    simp [h]

/-- The `ltu` flag on small numbers. -/
theorem ltW_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.ltu.eval (toWord a) (toWord b) = bW (decide (a < b)) := by
  simp only [XOp.eval, bW, toWord_lt_toWord ha hb]
  by_cases h : a < b <;> simp [h]


/-! ## Word helpers -/

theorem add_toWord (a b : ℕ) : XOp.add.eval (toWord a) (toWord b) = toWord (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem or_self_eval (x : Word) : XOp.or.eval x x = x := BitVec.or_self

/-- `minPs` as the machine evaluates it. -/
theorem minP_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.xor.eval (toWord b) (XOp.and.eval (XOp.xor.eval (toWord a) (toWord b))
      (XOp.sub.eval 0 (XOp.ltu.eval (toWord a) (toWord b)))) = toWord (min a b) :=
  minW_toWord ha hb

theorem bW_and (p q : Bool) : XOp.and.eval (bW p) (bW q) = bW (p && q) := by
  cases p <;> cases q <;> decide

theorem bW_ne_zero : bW true ≠ 0 := by decide

theorem bW_false : bW false = 0 := rfl

/-! ## The heap frame of store-free, loop-free code -/

/-- No store, no loop, every destination a register. -/
def Lo : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => Lo p ∧ Lo q
  | .ite _ p q => Lo p ∧ Lo q
  | _ => False

/-- **Heap frame**: such code leaves every cell `≥ regs` alone. -/
theorem hframe (I : Array Word) : ∀ (P : XIR) (s : St), Lo P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [Lo] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframe I q _ h.2 x hx).trans (hframe I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframe I q s h.2 x hx
    · exact hframe I p s h.1 x hx
  | .store .., _, h, _, _ => h.elim
  | .loopK .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-! ## The relation between the machine and `MS` -/

/-- The nine registers of a merge pass. -/
def regL : List ℕ := [rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst]

/-- The registers hold `σ`'s indices and the pass parameters `S`, `D` (the bases), `n`, `w`. -/
structure Regs (M : Mem) (S D n w : ℕ) (σ : MS) : Prop where
  i : rd M rI = toWord σ.i
  iE : rd M rIE = toWord σ.iE
  j : rd M rJ = toWord σ.j
  jE : rd M rJE = toWord σ.jE
  k : rd M rKk = toWord σ.k
  w : rd M rW2 = toWord w
  n : rd M rN = toWord n
  S : rd M rSrc = toWord S
  D : rd M rDst = toWord D

theorem Regs.frame {M M' : Mem} {S D n w : ℕ} {σ : MS} (h : Regs M S D n w σ)
    (hf : ∀ r ∈ regL, rd M' r = rd M r) : Regs M' S D n w σ where
  i := (hf rI (by simp [regL])).trans h.i
  iE := (hf rIE (by simp [regL])).trans h.iE
  j := (hf rJ (by simp [regL])).trans h.j
  jE := (hf rJE (by simp [regL])).trans h.jE
  k := (hf rKk (by simp [regL])).trans h.k
  w := (hf rW2 (by simp [regL])).trans h.w
  n := (hf rN (by simp [regL])).trans h.n
  S := (hf rSrc (by simp [regL])).trans h.S
  D := (hf rDst (by simp [regL])).trans h.D

theorem regL_lt : ∀ r ∈ regL, r < regs := by decide

theorem Regs.sem {I : Array Word} {P : XIR} {s : St} {S D n w : ℕ} {σ : MS}
    (h : Regs s.M S D n w σ) (hM : Inv s.M) (hP : WF P) (hw : ∀ r ∈ regL, ¬ Writes P r) :
    Regs (semXIR I P s).M S D n w σ :=
  h.frame fun r hr => Lvm.X.frame I P s hP hM r (regL_lt r hr) (hw r hr)

/-- The indices stay in range. -/
def Bnd (n : ℕ) (σ : MS) : Prop := σ.i ≤ σ.iE ∧ σ.j ≤ σ.jE ∧ σ.iE ≤ n ∧ σ.jE ≤ n

/-- The layout of a pass: source at `S`, destination at `D`, disjoint heap ranges of `n` cells. -/
structure Lay (S D n w sz : ℕ) : Prop where
  rS : regs ≤ S
  rD : regs ≤ D
  sS : S + n ≤ sz
  sD : D + n ≤ sz
  disj : S + n ≤ D ∨ D + n ≤ S
  bS : S + n < 2 ^ 64
  bD : D + n < 2 ^ 64
  bn : 3 * n + 2 < 2 ^ 64
  bw : w ≤ n + 1
  pw : 0 < n → 0 < w

/-- **The simulation relation**: the machine's memory holds the pass state `σ`. -/
structure Rel (S D n w : ℕ) (src : ℕ → Word) (M : Mem) (σ : MS) : Prop where
  inv : Inv M
  rg : Regs M S D n w σ
  hs : ∀ a < n, rd M (S + a) = src a
  hd : ∀ a < n, rd M (D + a) = σ.dst a
  bnd : Bnd n σ

theorem bstart_props {n w : ℕ} {σ : MS} (hB : Bnd n σ) (hk : σ.k < n) (hw : 0 < w) :
    (bstart n w σ).k = σ.k ∧ (bstart n w σ).dst = σ.dst ∧ Bnd n (bstart n w σ) ∧
      ((bstart n w σ).i < (bstart n w σ).iE ∨ (bstart n w σ).j < (bstart n w σ).jE) := by
  unfold bstart Bnd at *
  split
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only <;> (clear * - hk hw; omega)
  · exact ⟨rfl, rfl, by (clear * - hB; omega), by omega⟩

/-! ## `blockIR` -/

theorem lo_blockIR : Lo blockIR := by
  simp +decide only [Lo, blockIR, minPs, Prim.dst, regs, rG, rH, rI, rIE, rJ, rJE, rKk, rV, rT1,
    rT2, rKc, and_true, List.cons_append, List.nil_append]

theorem wf_blockIR : WF blockIR := by
  simp +decide only [WF, blockIR, minPs, Prim.dst, rG, rH, rI, rIE, rJ, rJE, rKk, rV, rT1, rT2, rKc,
    and_true, List.cons_append, List.nil_append]

/-- **`blockIR` computes `bstart`.** -/
theorem blockIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ} {σ : MS}
    (hR : Regs s.M S D n w σ) (hB : Bnd n σ) (hk : σ.k < n) (hn : 3 * n + 2 < 2 ^ 64)
    (hw : w ≤ n + 1) : Regs (semXIR I blockIR s).M S D n w (bstart n w σ) := by
  have hs := hM.1
  simp only [regs] at hs
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hwf1 : WF (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) := by
    simp +decide only [WF, Prim.dst, rG, rH]
  have h1 : rd (semXIR I (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) s).M
      rG = bW (decide (σ.i = σ.iE) && decide (σ.j = σ.jE)) := by
    have hi := hR.i; have hiE := hR.iE; have hj := hR.j; have hjE := hR.jE
    simp only [semXIR, runPrims, List.foldl, Prim.run, rG, rH, rI, rIE, rJ, rJE] at hi hiE hj hjE ⊢
    simp (disch := first | decide | (clear * - s n w σ hs; omega) | (simp only [size_set]; (clear * - s n w σ hs; omega))) only [rd_set_self,
      rd_set_ne]
    rw [hi, hiE, hj, hjE, eqW_toWord (by (clear * - hn b1 b3; omega)) (by (clear * - hn b3; omega)), eqW_toWord (by (clear * - hn b2 b4; omega)) (by (clear * - hn b4; omega)),
      bW_and]
  have hR1 := hR.sem (I := I) hM hwf1 (by simp +decide only [regL, Writes, Prim.dst, rG, rH, rI,
    rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true])
  have hM1 := inv_sem I hwf1 hM
  rw [blockIR, semXIR_seq, semXIR_ite]
  generalize semXIR I (.blk [.op .eq rG rI rIE, .op .eq rH rJ rJE, .op .and rG rG rH]) s = s1
    at h1 hR1 hM1
  unfold bstart
  by_cases hc : σ.i = σ.iE ∧ σ.j = σ.jE
  · rw [if_pos hc, h1, decide_eq_true hc.1, decide_eq_true hc.2]
    rw [Bool.and_self, if_neg bW_ne_zero]
    have hs1 := hM1.1
    simp only [regs] at hs1
    obtain ⟨i1, iE1, j1, jE1, k1, w1, n1, S1, D1⟩ := hR1
    simp only [rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst] at i1 iE1 j1 jE1 k1 w1 n1 S1 D1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, minPs, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst, rV, rT1, rT2,
      rKc] <;>
    simp (disch := first | decide | (clear * - s1 s n w σ hs1; omega) | (simp only [size_set]; (clear * - s1 s n w σ hs1; omega))) only [rd_set_self,
      rd_set_ne] <;>
    simp only [i1, iE1, j1, jE1, k1, w1, n1, S1, D1, or_self_eval, add_toWord] <;>
    simp (disch := omega) only [minP_toWord, add_toWord, or_self_eval]
  · rw [if_neg hc, h1, show (decide (σ.i = σ.iE) && decide (σ.j = σ.jE)) = false by simpa using hc,
      if_pos bW_false]
    exact hR1


/-! ## `stepIR`, piece by piece -/

/-- The run flags. -/
def flagsIR : XIR := .blk [.op .ltu rG rI rIE, .op .ltu rH rJ rJE]
/-- The choice: `rF := takeL`. -/
def chooseIR : XIR := .ite rG (.ite rH cmpIR (.blk [.const rF 1])) (.blk [.const rF 0])
/-- The head that goes next: its address in `rAd`, the head advanced. -/
def advIR : XIR := .ite rF (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
  (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne])
/-- The write `dst[k] := src[h]`, `k += 1`. -/
def tailIR : XIR :=
  .seq (.load rV rAd) (.seq (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne]) (.store rAd rV))

theorem stepIR_eq : stepIR = .seq blockIR (.seq flagsIR (.seq chooseIR (.seq advIR tailIR))) :=
  rfl

theorem add_one_toWord (a : ℕ) : XOp.add.eval (toWord a) 1 = toWord (a + 1) :=
  (BitVec.ofNat_add a 1).symm

/-- **The choice** leaves `takeL` in `rF`. -/
theorem choose_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w : ℕ} {src : ℕ → Word}
    {τ : MS} (hR : Regs s.M S D n w τ) (hrS : regs ≤ S) (hbS : S + n < 2 ^ 64) (hB : Bnd n τ)
    (hsrc : ∀ a < n, rd s.M (S + a) = src a)
    (hG : rd s.M rG = bW (decide (τ.i < τ.iE))) (hH : rd s.M rH = bW (decide (τ.j < τ.jE))) :
    rd (semXIR I chooseIR s).M rF = bW (takeL (keyLt I) src τ) := by
  obtain ⟨b1, b2, b3, b4⟩ := hB
  have hs := hM.1
  simp only [regs] at hs hrS
  rw [chooseIR, semXIR_ite]
  by_cases g : τ.i < τ.iE
  · rw [hG, decide_eq_true g, if_neg bW_ne_zero, semXIR_ite]
    by_cases h : τ.j < τ.jE
    · rw [hH, decide_eq_true h, if_neg bW_ne_zero]
      have ha : ∀ a < n, regs ≤ (rd s.M rSrc + toWord a).toNat ∧
          rd s.M (rd s.M rSrc + toWord a).toNat = src a := fun a ha => by
        rw [hR.S, toWord_add, toNat_toWord (by (clear * - hbS ha; omega)), hsrc a ha]
        exact ⟨by simp only [regs]; (clear * - hrS; omega), rfl⟩
      rw [cmpIR_sem I s hM (by rw [hR.i]; exact (ha _ (by (clear * - b3 g; omega))).1)
        (by rw [hR.j]; exact (ha _ (by (clear * - b4 h; omega))).1), hR.i, hR.j, (ha _ (by (clear * - b3 g; omega))).2,
        (ha _ (by (clear * - b4 h; omega))).2]
      simp [takeL, g, h]
    · rw [hH, decide_eq_false h, if_pos bW_false]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [rF]; (clear * - hs; omega))]
      simp [takeL, g, h, bW]
  · rw [hG, decide_eq_false g, if_pos bW_false]
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rF]; (clear * - hs; omega))]
    simp [takeL, g, bW]

theorem lo_cmpIR : Lo cmpIR := by
  simp +decide only [Lo, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, regs, rAd, rX, rY, rPa, rPb,
    rKa, rKb, rF, rG, rH, rQL, rKc, rT2, and_true, List.cons_append, List.nil_append]

theorem wf_cmpIR : WF cmpIR := by
  simp +decide only [WF, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, rAd, rX, rY, rPa, rPb, rKa, rKb,
    rF, rG, rH, rQL, rKc, rT2, and_true, List.cons_append, List.nil_append]

/-- **The write**: `dst[k] := src[h]`, `k += 1`; the source and the other registers stay. -/
theorem tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {S D n w h : ℕ} {src : ℕ → Word}
    {τ : MS} (hL : Lay S D n w s.M.size) (hR : Regs s.M S D n w τ) (hk : τ.k < n) (hh : h < n)
    (hA : rd s.M rAd = toWord (S + h)) (hsrc : ∀ a < n, rd s.M (S + a) = src a)
    (hdst : ∀ a < n, rd s.M (D + a) = τ.dst a) :
    Inv (semXIR I tailIR s).M ∧
    Regs (semXIR I tailIR s).M S D n w { τ with k := τ.k + 1, dst := upd τ.dst τ.k (src h) } ∧
    (∀ a < n, rd (semXIR I tailIR s).M (S + a) = src a) ∧
    (∀ a < n, rd (semXIR I tailIR s).M (D + a) = upd τ.dst τ.k (src h) a) := by
  have hs := hM.1
  have hc1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  obtain ⟨Lr, Ld, LsS, LsD, Ldj, LbS, LbD, -, -, -⟩ := hL
  simp only [regs] at hs Lr Ld
  have e : semXIR I tailIR s = semXIR I (.store rAd rV) (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s) := rfl
  have hwf2 : WF (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) := by
    simp +decide only [WF, Prim.dst, rV, rAd, rKk, and_true]
  have hM2 := inv_sem I hwf2 hM
  have hH2 := hframe I (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne]))
    s (by simp +decide only [Lo, Prim.dst, regs, rV, rAd, rKk, and_true])
  have hz2 := size_sem I (.seq (.load rV rAd) (.blk [.op .add rAd rDst rKk,
    .op .add rKk rKk cOne])) s
  have hF2 : ∀ r ∈ [rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst], rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M r = rd s.M r := fun r hr =>
    frame I _ s hwf2 hM r (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr;
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr;
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp +decide only [Writes, Prim.dst, rV, rAd, rKk, rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst,
          or_false])
  have hA2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rAd = toWord (D + τ.k) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; (clear * - s I S D n h τ hs hz2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hR.D, hR.k, add_toWord]
  have hK2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rKk = toWord (τ.k + 1) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; (clear * - s I S D n h τ hs hz2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hR.k, hc1, add_one_toWord]
  have hV2 : rd (semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s).M rV = src h := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rAd, rKk, rV]; (clear * - s I S D n h τ hs hz2; omega))) only
      [rd_set_self, rd_set_ne]
    rw [hA, toNat_toWord (by (clear * - hh LbS; omega)), hsrc h hh]
  rw [e]
  generalize semXIR I (.seq (.load rV rAd)
      (.blk [.op .add rAd rDst rKk, .op .add rKk rKk cOne])) s = s2 at hM2 hH2 hz2 hF2 hA2 hK2 hV2
  have hst : ∀ i, i ≠ cTmp → rd (semXIR I (.store rAd rV) s2).M i =
      if i = D + τ.k then src h else rd s2.M i := fun i hi => by
    rw [← hV2]
    exact rd_storeM hM2 hA2 (by simp only [regs]; (clear * - Ld; omega)) (by (clear * - hk LbD; omega)) (by (clear * - hk LsD hz2; omega)) (by decide)
      (by decide) hi
  have hreg : ∀ r ∈ [rI, rIE, rJ, rJE, rW2, rN, rSrc, rDst],
      rd (semXIR I (.store rAd rV) s2).M r = rd s.M r := fun r hr => by
    have h1 : r < regs ∧ r ≠ cTmp := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hst r h1.2, if_neg (by simp only [regs] at h1; (clear * - Ld h1; omega)), hF2 r hr]
  refine ⟨inv_sem I (P := .store rAd rV) (by simp +decide only [WF, rAd, cTmp]) hM2,
    ⟨(hreg rI (by simp)).trans hR.i, (hreg rIE (by simp)).trans hR.iE,
      (hreg rJ (by simp)).trans hR.j, (hreg rJE (by simp)).trans hR.jE, ?_,
      (hreg rW2 (by simp)).trans hR.w, (hreg rN (by simp)).trans hR.n,
      (hreg rSrc (by simp)).trans hR.S, (hreg rDst (by simp)).trans hR.D⟩,
    fun a ha => ?_, fun a ha => ?_⟩
  · rw [hst rKk (by decide), if_neg (by simp only [rKk]; (clear * - Ld; omega)), hK2]
  · rw [hst _ (by simp only [cTmp]; (clear * - Lr; omega)), if_neg (by (clear * - hk Ldj ha; omega)), hH2 _ (by simp only [regs]; (clear * - Lr; omega)),
      hsrc a ha]
  · rw [hst _ (by simp only [cTmp]; (clear * - Ld; omega))]
    by_cases hak : a = τ.k
    · subst hak; rw [if_pos rfl]; simp [upd]
    · rw [if_neg (by (clear * - hak; omega)), hH2 _ (by simp only [regs]; (clear * - Ld; omega)), hdst a ha]
      simp [upd, hak]


/-- **`advIR`** for a head register `r ∈ {rI, rJ}` holding `h`: `rAd := S + h`, `r := h + 1`. -/
theorem adv_blk (I : Array Word) (s : St) (hM : Inv s.M) {S h : ℕ} {r : ℕ} (hr : r = rI ∨ r = rJ)
    (hS : rd s.M rSrc = toWord S) (hh : rd s.M r = toWord h) :
    rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M rAd = toWord (S + h) ∧
    rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M r = toWord (h + 1) ∧
    ∀ q ∈ regL, q ≠ r → rd (semXIR I (.blk [.op .add rAd rSrc r, .op .add r r cOne]) s).M q =
      rd s.M q := by
  have hs := hM.1
  have hc1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  have hr' : r < 256 ∧ r ≠ rAd ∧ r ≠ cOne := by rcases hr with rfl | rfl <;> decide
  simp only [semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, fun q hq hqr => ?_⟩
  · rw [rd_set_ne hr'.2.1, rd_set_self (by simp only [rAd]; (clear * - hs; omega)), hS, hh, add_toWord]
  · rw [rd_set_self (by simp only [size_set]; (clear * - hs hr'; omega)), rd_set_ne (Ne.symm hr'.2.1),
      rd_set_ne (by decide : rAd ≠ cOne), hc1, hh, add_one_toWord]
  · have hq' : q ≠ rAd := by
      simp only [regL, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [rd_set_ne (Ne.symm hqr), rd_set_ne (Ne.symm hq')]

theorem lo_flagsIR : Lo flagsIR := by simp +decide only [Lo, flagsIR, Prim.dst, regs, rG, rH]
theorem wf_flagsIR : WF flagsIR := by simp +decide only [WF, flagsIR, Prim.dst, rG, rH]
theorem lo_chooseIR : Lo chooseIR := by
  simp only [Lo, chooseIR]; exact ⟨⟨lo_cmpIR, by simp [Prim.dst, regs, rF]⟩,
    by simp [Prim.dst, regs, rF]⟩
theorem wf_chooseIR : WF chooseIR := by
  simp only [WF, chooseIR]; exact ⟨⟨wf_cmpIR, by simp [Prim.dst, rF]⟩, by simp [Prim.dst, rF]⟩
theorem nw_flagsIR : ∀ r ∈ regL, ¬ Writes flagsIR r := by
  simp +decide only [regL, Writes, flagsIR, Prim.dst, rG, rH, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc,
    rDst, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq,
    exists_eq_left, or_false, and_true]

theorem nw_chooseIR : ∀ r ∈ regL, ¬ Writes chooseIR r := by
  simp +decide only [regL, Writes, chooseIR, cmpIR, cmpWord, aposIR, ceil8Ps, Prim.dst, rAd, rX, rY,
    rPa, rPb, rKa, rKb, rF, rG, rH, rQL, rKc, rT2, rI, rIE, rJ, rJE, rKk, rW2, rN, rSrc, rDst,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left,
    or_false, and_true, List.cons_append, List.nil_append]

/-- **One step**: `stepIR` maps a state holding `σ` to one holding `mstep σ`. -/
theorem stepIR_sem (I : Array Word) (s : St) {S D n w : ℕ} {src : ℕ → Word} {σ : MS}
    (hL : Lay S D n w s.M.size) (hR : Rel S D n w src s.M σ) (hk : σ.k < n) :
    Rel S D n w src (semXIR I stepIR s).M (mstep (keyLt I) src n w σ) ∧
      (mstep (keyLt I) src n w σ).k = σ.k + 1 := by
  obtain ⟨hM, hRg, hsrc, hdst, hB⟩ := hR
  obtain ⟨tk, tdst, tB, tav⟩ := bstart_props hB hk (hL.pw (by (clear * - hk; omega)))
  have hR1 := blockIR_sem I s hM hRg hB hk hL.bn hL.bw
  have hM1 := inv_sem I wf_blockIR hM
  have hH1 := hframe I _ s lo_blockIR
  have hz1 := size_sem I blockIR s
  have Lr := hL.rS
  have Ld := hL.rD
  have LbS := hL.bS
  have Lbn := hL.bn
  simp only [regs] at Lr Ld
  simp only [mstep]
  rw [stepIR_eq, semXIR_seq]
  generalize bstart n w σ = τ at tk tdst tB tav hR1
  generalize semXIR I blockIR s = s1 at hR1 hM1 hH1 hz1
  obtain ⟨b1, b2, b3, b4⟩ := tB
  -- the flags
  have hfl : rd (semXIR I flagsIR s1).M rG = bW (decide (τ.i < τ.iE)) ∧
      rd (semXIR I flagsIR s1).M rH = bW (decide (τ.j < τ.jE)) := by
    have hs1 := hM1.1
    simp only [regs] at hs1
    simp only [flagsIR, semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rG, rH]; (clear * - s1 s S D n σ τ hz1 hs1; omega))) only [rd_set_self,
      rd_set_ne]
    · rw [hR1.i, hR1.iE, ltW_toWord (by (clear * - Lr LbS b1 b3; omega)) (by (clear * - Lr LbS b3; omega))]
    · rw [hR1.j, hR1.jE, ltW_toWord (by (clear * - Lr LbS b2 b4; omega)) (by (clear * - Lr LbS b4; omega))]
  have hR2 := hR1.sem (I := I) hM1 wf_flagsIR nw_flagsIR
  have hM2 := inv_sem I wf_flagsIR hM1
  have hH2 := hframe I _ s1 lo_flagsIR
  have hz2 := size_sem I flagsIR s1
  rw [semXIR_seq]
  generalize semXIR I flagsIR s1 = s2 at hfl hR2 hM2 hH2 hz2
  -- the choice
  have hsrc2 : ∀ a < n, rd s2.M (S + a) = src a := fun a ha => by
    rw [hH2 _ (by simp only [regs]; (clear * - Lr; omega)), hH1 _ (by simp only [regs]; (clear * - Lr; omega)), hsrc a ha]
  have hF := choose_sem I s2 hM2 hR2 hL.rS LbS ⟨b1, b2, b3, b4⟩ hsrc2 hfl.1 hfl.2
  have hR3 := hR2.sem (I := I) hM2 wf_chooseIR nw_chooseIR
  have hM3 := inv_sem I wf_chooseIR hM2
  have hH3 := hframe I _ s2 lo_chooseIR
  have hz3 := size_sem I chooseIR s2
  rw [semXIR_seq]
  generalize semXIR I chooseIR s2 = s3 at hF hR3 hM3 hH3 hz3
  have hsrc3 : ∀ a < n, rd s3.M (S + a) = src a := fun a ha => by
    rw [hH3 _ (by simp only [regs]; (clear * - Lr; omega)), hsrc2 a ha]
  have hdst3 : ∀ a < n, rd s3.M (D + a) = τ.dst a := fun a ha => by
    rw [hH3 _ (by simp only [regs]; (clear * - Ld; omega)), hH2 _ (by simp only [regs]; (clear * - Ld; omega)),
      hH1 _ (by simp only [regs]; (clear * - Ld; omega)), hdst a ha, tdst]
  have hL3 : Lay S D n w s3.M.size := by rw [hz3, hz2, hz1]; exact hL
  -- the write
  rw [semXIR_seq, advIR, semXIR_ite, hF]
  by_cases hT : takeL (keyLt I) src τ = true
  · have hi : τ.i < τ.iE := by simp [takeL] at hT; exact hT.1
    rw [hT, if_neg bW_ne_zero, if_pos rfl]
    obtain ⟨a1, a2, a3⟩ := adv_blk I s3 hM3 (.inl rfl) hR3.S hR3.i
    have hR4 : Regs (semXIR I (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne]) s3).M S D n w
        { τ with i := τ.i + 1 } := ⟨a2, (a3 rIE (by simp [regL]) (by decide)).trans hR3.iE,
      (a3 rJ (by simp [regL]) (by decide)).trans hR3.j,
      (a3 rJE (by simp [regL]) (by decide)).trans hR3.jE,
      (a3 rKk (by simp [regL]) (by decide)).trans hR3.k,
      (a3 rW2 (by simp [regL]) (by decide)).trans hR3.w,
      (a3 rN (by simp [regL]) (by decide)).trans hR3.n,
      (a3 rSrc (by simp [regL]) (by decide)).trans hR3.S,
      (a3 rDst (by simp [regL]) (by decide)).trans hR3.D⟩
    have hP : Lo (.blk [.op .add rAd rSrc rI, .op .add rI rI cOne]) := by
      simp +decide only [Lo, Prim.dst, regs, rAd, rI]
    have hM4 := inv_sem I (P := .blk [.op .add rAd rSrc rI, .op .add rI rI cOne])
      (by simp +decide only [WF, Prim.dst, rAd, rI]) hM3
    obtain ⟨t1, t2, t3, t4⟩ := tail_sem I _ hM4 (by rw [size_sem]; exact hL3) hR4
      (by show τ.k < n; (clear * - hk tk; omega))
      (h := τ.i) (by (clear * - b3 hi; omega)) a1 (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; (clear * - Lr; omega)),
        hsrc3 a ha]) (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; (clear * - Ld; omega)),
        hdst3 a ha])
    exact ⟨⟨t1, t2, t3, t4, ⟨by show τ.i + 1 ≤ τ.iE; (clear * - hi; omega), b2, b3, b4⟩⟩, by simp only; (clear * - tk; omega)⟩
  · have hj : τ.j < τ.jE := by
      by_contra hj
      apply hT
      simp only [takeL, hj, decide_false, Bool.not_false, Bool.true_or, Bool.and_true,
        decide_eq_true_eq]
      (clear * - tav b1 b2 hj; omega)
    rw [Bool.not_eq_true] at hT
    rw [hT, if_pos bW_false, if_neg (by simp)]
    obtain ⟨a1, a2, a3⟩ := adv_blk I s3 hM3 (.inr rfl) hR3.S hR3.j
    have hR4 : Regs (semXIR I (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]) s3).M S D n w
        { τ with j := τ.j + 1 } := ⟨(a3 rI (by simp [regL]) (by decide)).trans hR3.i,
      (a3 rIE (by simp [regL]) (by decide)).trans hR3.iE, a2,
      (a3 rJE (by simp [regL]) (by decide)).trans hR3.jE,
      (a3 rKk (by simp [regL]) (by decide)).trans hR3.k,
      (a3 rW2 (by simp [regL]) (by decide)).trans hR3.w,
      (a3 rN (by simp [regL]) (by decide)).trans hR3.n,
      (a3 rSrc (by simp [regL]) (by decide)).trans hR3.S,
      (a3 rDst (by simp [regL]) (by decide)).trans hR3.D⟩
    have hP : Lo (.blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne]) := by
      simp +decide only [Lo, Prim.dst, regs, rAd, rJ]
    have hM4 := inv_sem I (P := .blk [.op .add rAd rSrc rJ, .op .add rJ rJ cOne])
      (by simp +decide only [WF, Prim.dst, rAd, rJ]) hM3
    obtain ⟨t1, t2, t3, t4⟩ := tail_sem I _ hM4 (by rw [size_sem]; exact hL3) hR4
      (by show τ.k < n; (clear * - hk tk; omega))
      (h := τ.j) (by (clear * - b4 hj; omega)) a1 (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; (clear * - Lr; omega)),
        hsrc3 a ha]) (fun a ha => by rw [hframe I _ s3 hP _ (by simp only [regs]; (clear * - Ld; omega)),
        hdst3 a ha])
    exact ⟨⟨t1, t2, t3, t4, ⟨b1, by show τ.j + 1 ≤ τ.jE; (clear * - hj; omega), b3, b4⟩⟩, by simp only; (clear * - tk; omega)⟩


/-! ## The pass -/

theorem regL_ne {c : ℕ} (hc : c ∉ regL) : ∀ r ∈ regL, c ≠ r := fun _ hr he => hc (he ▸ hr)

/-- A write to a counter outside `regL` and below `regs` keeps the relation. -/
theorem Rel.set {S D n w : ℕ} {src : ℕ → Word} {M : Mem} {σ : MS} (h : Rel S D n w src M σ)
    {c : ℕ} (hc : c ∉ regL) (hc4 : 4 ≤ c) (hcr : c < regs) (hS : regs ≤ S) (hD : regs ≤ D)
    (v : Word) : Rel S D n w src (M.setIfInBounds c v) σ where
  inv := inv_of_frame h.inv (size_set ..) fun i hi => rd_set_ne (by (clear * - hc4 hi; omega))
  rg := h.rg.frame fun r hr => rd_set_ne (regL_ne hc r hr)
  hs := fun a ha => (rd_set_ne (by (clear * - hcr hS; omega))).trans (h.hs a ha)
  hd := fun a ha => (rd_set_ne (by (clear * - hcr hD; omega))).trans (h.hd a ha)
  bnd := h.bnd

theorem Rel.decS {S D n w : ℕ} {src : ℕ → Word} {s : St} {σ : MS}
    (h : Rel S D n w src s.M σ) (hS : regs ≤ S) (hD : regs ≤ D) :
    Rel S D n w src (decS rCS s).M σ :=
  h.set (by decide) (by decide) (by decide) hS hD _

/-- **`n − k` steps** of the pass's loop run `mrun`. -/
theorem stepLoop (I : Array Word) {S D n w : ℕ} {src : ℕ → Word} :
    ∀ (m : ℕ) (s : St) (σ : MS), Lay S D n w s.M.size → Rel S D n w src s.M σ → σ.k + m = n →
      Rel S D n w src (iterL (semXIR I stepIR) rCS m s).M (mrun (keyLt I) src n w m σ)
  | 0, _, _, _, hR, _ => hR
  | m + 1, s, σ, hL, hR, hm => by
    obtain ⟨h1, h2⟩ := stepIR_sem I s hL hR (by (clear * - σ n m hm; omega))
    simp only [iterL, mrun]
    exact stepLoop I m _ _ (by rw [size_decS, size_sem]; exact hL) (h1.decS hL.rS hL.rD)
      (by rw [h2]; (clear * - σ m n I w src hm; omega))

/-! ## The sort: 64 passes -/

theorem iterL_succ' (f : St → St) (c : ℕ) :
    ∀ (k : ℕ) (s : St), iterL f c (k + 1) s = decS c (f (iterL f c k s))
  | 0, _ => rfl
  | k + 1, s => iterL_succ' f c k (decS c (f s))

theorem wseq_le (n : ℕ) : ∀ p, wseq n p ≤ n + 1
  | 0 => by simp [wseq]
  | p + 1 => by simp only [wseq]; (clear * - n p; omega)

theorem wseq_pos {n : ℕ} (hn : 0 < n) (p : ℕ) : 0 < wseq n p := by
  rw [wseq_eq hn]; exact lt_min (Nat.two_pow_pos p) hn

/-- The count of the sort's loop. -/
theorem entryK64 {M : Mem} (hM : Inv M) (hN : rd M rNP = 64) :
    rd (entryK rCP rNP 64 M) rCP = 64 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds rCP 64) rNP = 64 := by rw [rd_set_ne (by decide), hN]
  have h2 : rd (M.setIfInBounds rCP 64) rCP = 64 := rd_set_self (by simp only [rCP]; (clear * - hs; omega))
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp]; (clear * - hs; omega))]
  rw [if_pos (by decide), rd_set_ne (by decide), h2]

/-! ## The log index after walk and sort -/

theorem entryOff_lt (L : Log) {a b : ℕ} (h : a < b) (hb : b ≤ L.length) :
    entryOff L a < entryOff L b := by
  induction b with
  | zero => (clear * - h; omega)
  | succ b ih =>
    rw [entryOff_succ L (by (clear * - hb; omega))]
    have : 5 ≤ qWords L[b] := Nat.le_add_right _ _
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · have := ih h' (by (clear * - hb; omega)); omega
    · subst h'; (clear * - L a hb this; omega)

/-! ## The sort and the index at a parametric base and log position

The index base `bX` and the tape word `pL` of `|L|` are parameters; lvm's instance is
`bX = memX`, `pL = posL pz`. -/

section Idx

variable (bX pL : ℕ)

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


theorem baseX4_two (n p : ℕ) : baseX4 bX n (p + 1 + 1) = baseX4 bX n p := by
  unfold baseX4
  by_cases h : p % 2 = 0
  · rw [if_pos (by (clear * - p h; omega)), if_pos h]
  · rw [if_neg (by (clear * - p h; omega)), if_neg h]


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
  (clear * - t; omega)


theorem sizeIR_idxIR4 : sizeIR (idxIR4 bX pL) ≤ 2 ^ 19 := by
  simp only [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps,
    List.length_cons, List.length_nil, List.length_append]
  norm_num


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
      (by decide) (by (clear * - hpL; omega)), hn]
  have hR0 : Regs (semXIR I (passPre4 pL) s).M S D n w ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [passPre4, readAt, semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rI, rIE, rJ, rJE, rKk, rNS, rA]; (clear * - s bX pL n w hs; omega)))
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
    simp only [semXIR, rd_entryT (show rCS < s0.M.size by simp only [rCS]; (clear * - hs hz0; omega)), hcnt,
      toNat_toWord (show n < 2 ^ 64 by (clear * - Lbn; omega))]
  rw [e]
  have hRel : Rel S D n w (fun a => rd s.M (S + a)) (entryT rCS rNS s0.M)
      ⟨0, 0, 0, 0, 0, 0, fun a => rd s.M (D + a)⟩ :=
    Rel.set (M := s0.M) ⟨hM0, hR0, fun a ha => hH0 _ (le_trans hL.rS (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - S a; omega)))),
      fun a ha => hH0 _ (le_trans hL.rD (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - D a; omega)))), by simp [Bnd]⟩ (by decide) (by decide)
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
  · rw [hframe I _ s1 hlo _ (le_trans hL.rD (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - D a; omega)))), hd1 a ha]; rfl
  all_goals
    simp only [swapPs, minPs, semXIR, runPrims, List.foldl, List.cons_append, List.nil_append,
      Prim.run]
    simp (disch := first | decide | (simp only [size_set, rV, rSrc, rDst, rW2, rT1, rT2, rKc]; (clear * - s1 bX pL s n w s0 hs1; omega)))
      only [rd_set_self, rd_set_ne]
    simp only [hR1.S, hR1.D, hR1.w, hR1.n, or_self_eval, add_toWord]
  rw [minP_toWord (by (clear * - Lbn Lbw; omega)) (by (clear * - Lbn; omega)), two_mul]


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
    have hN := rd_readAt I s hM (d := rN) (pos := pL) (by decide) (by (clear * - hpL; omega))
    have hM' := inv_sem I (P := readAt rN pL) (by simp +decide [readAt, WF, Prim.dst, rN, rA,
      and_true]) hM
    rw [hn] at hN
    rw [sortPre4, semXIR_seq]
    generalize semXIR I (readAt rN pL) s = s' at hN hM'
    have hs' := hM'.1
    simp only [regs] at hs'
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rN, rW2, rSrc, rDst, rNP]; (clear * - s' bX pL s n hs'; omega))) only
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
    fun i hi => hE i (by simp only [rCP]; (clear * - hi; omega)) (by simp only [cTmp]; (clear * - hi; omega))
  generalize hS0 : (⟨entryK rCP rNP 64 s0.M, s0.o⟩ : St) = T at hE hME
  -- the pass invariant
  have hLay : ∀ p, Lay (baseX4 bX n p) (baseX4 bX n (p + 1)) n (wseq n p) s.M.size := fun p => by
    have := wseq_le n p
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by (clear * - hn2; omega), this, wseq_pos (p := p)⟩ <;>
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
      refine ⟨by (try dsimp only); exact hME, by rw [size_entryK, hz0], ?_, ?_, ?_, ?_⟩
      · rw [hE _ (by decide) (by decide), S0]; simp only [baseX4, Nat.zero_mod, if_true]
      · rw [hE _ (by decide) (by decide), D0]; simp only [baseX4]; rfl
      · rw [hE _ (by decide) (by decide), w0]; rfl
      · rw [hE _ (by decide) (by decide), n0]
    | succ p ih =>
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih
      obtain ⟨j1, j2, j3, j4, j5, -⟩ := passIR4_sem hbX hbX2 hpL I _ i1 (by rw [i2]; exact hLay p) hn i3 i4 i5 i6
      rw [iterL_succ']
      refine ⟨inv_of_frame j1 (size_decS ..) fun i hi => rd_decS (by simp only [rCP]; (clear * - hi; omega)) _,
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
    rw [iterL_succ', rd_decS (by have := hL.rD; (clear * - this; (try simp only [regs, rCP] at *); omega))]
    exact (passIR4_sem hbX hbX2 hpL I _ i1 hL hn i3 i4 i5 i6).2.2.2.2.2 a ha
  have hX0 : ∀ a < n, rd (iterL (semXIR I (passIR4 pL)) rCP 0 T).M (baseX4 bX n 0 + a) = rd s.M (bX + a) :=
    fun a ha => by
      simp only [iterL, baseX4, Nat.zero_mod, if_true]
      rw [← hS0, hE _ (by simp only [rCP, regs] at hbX ⊢; (clear * - hbX hbX2; omega)) (by simp only [cTmp, regs] at hbX ⊢; (clear * - hbX hbX2; omega)),
        hH0 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega))]
  obtain ⟨r1, r2, r3⟩ := passes_ok (keyLt_order I) (by (clear * - hn2; omega))
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
  have hW := fun {k : ℕ} (hk : k < L.length) => walk_spec4 hbX hbX2 hpL c π L hs hq ht s hM (by (clear * - hsz; omega)) hk
  have hwf : WF (walkIR4 bX pL) := wf_walkIR4 bX pL
  rw [idxIR4, semXIR_seq]
  obtain ⟨r1, r2, r3⟩ := sortIR4_sem hbX hbX2 hpL I (semXIR I (walkIR4 bX pL) s) (inv_sem I hwf hM) (n := L.length)
    (by rw [hI, getD_toArray, tape_getD_posL4 c π L hs]) (by (clear * - hs ht hend h5; omega)) (by rw [size_sem]; exact hsz)
    (fun a b ha hb h => by
      rw [hW ha, hW hb] at h
      have hab := congrArg BitVec.toNat h
      have ea : entryOff L a < entryOff L L.length := entryOff_lt L ha le_rfl
      have eb : entryOff L b < entryOff L L.length := entryOff_lt L hb le_rfl
      rw [toNat_toWord (by (clear * - hs ht hend ea; omega)), toNat_toWord (by (clear * - hs ht hend hab eb; omega))] at hab
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · have := entryOff_lt L h' hb.le; (clear * - hab this; omega)
      · have := entryOff_lt L h' ha.le; (clear * - hab this; omega))
  refine ⟨r1, fun a ha => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, e⟩ := r2 a ha
    exact ⟨k, hk, e.trans (hW hk)⟩
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, e.trans (hW hk)⟩



end Idx

/-- **The log index at lvm's instance** (`bX = memX`, `pL = posL pz`) meets the SNARK branch's
obligations (FR's `decOk_logIR`). -/
theorem decOk_idx {pz : ℕ} (hpz : pz < 2 ^ 64) : DecOk pz (idxIR4 memX (posL pz)) where
  pz_lt := hpz
  wf := wf_idxIR4 _ _
  safe := fun c π L hs _ ht => safe_idxIR4 _ _ (by unfold posL; (clear * - hpz hs; omega))
    (tape_count_le4 c π L (hs_posL hs) ht)
  cost := fun t => by
    rw [cost_idxIR4]; simp only [decBudget, fuelBase, fuelPerWord]; (clear * -; omega)
  outs := fun t => by rw [outs_idxIR4]; exact Nat.zero_le _
  size := sizeIR_idxIR4 _ _

end Lvm.X

end LvmXSortSim
end
-- ===== end of `LvmXSort` =====

/-!
# The lookup: the first entry with a given answer

* `tape_answer`, `ansW_entry`: the four answer words of entry `k` on the tape are
  `packBytes L[k].2`; the sort key of entry `k` is its answer then its position.
* `bsStep`/`bsRun`: the pure lower-bound search; `bsRun_spec`: on a predicate that holds on a
  prefix of `[0, n)`, 64 halvings from `(0, n)` end at the prefix's length.
* `lookIR_sem` (the machine runs `bsRun` and sets the found flag) and `idx_lookup`
  (`lookup_spec`: after `idxIR4`, any target's lookup finds its first preimage, `ansIdx`).

**Parameters.** The lookup takes the index base `bX` and the tape word `pL` of `|L|`
(`lookIR4`, `Sorted4`, `posE4`, `idx_lookup4`); lvm's instance is `memX`, `posL pz`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The first entry with an answer (FR's `ansIdx`) -/

/-- The index of the first log entry whose answer is `st`. -/
def ansIdx (L : Log) (st : Digest) : Option ℕ := L.findIdx? fun e => decide (e.2 = st)

theorem ansIdx_lt {L : Log} {st : Digest} {i : ℕ} (h : ansIdx L st = some i) :
    ∃ hi : i < L.length, L[i].2 = st := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, by simpa using hp⟩

/-! ## The answers on the tape -/

/-- The answer words of an entry within the log's words. -/
theorem entries_getD_ans : ∀ (L : Log) (k : ℕ) (hk : k < L.length) (m : ℕ), m < 4 →
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD
      (entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) 0 = (packBytes L[k].2.toList).getD m 0
  | e :: L, 0, _, m, hm => by
    have hb : (bytesWords e.1.data.toList).length = 1 + (e.1.size + 7) / 8 := by
      simp only [bytesWords, List.length_cons, packBytes_length, Array.length_toList]
      have : e.1.data.size = e.1.size := rfl
      (clear * - this; omega)
    have hp := packBytes_digest_length e.2
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      List.getElem_cons_zero, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_append]; (clear * - e m L hm hb hp; omega)),
      List.getElem?_append_right (by (clear * - hm hb; omega)), ← List.getD_eq_getElem?_getD, hb]
    congr 1
    (clear * - hm; omega)
  | e :: L, k + 1, hk, m, hm => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    have ih := entries_getD_ans L k (by simp at hk; (clear * - hk; omega)) m hm
    rw [ho, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entry_length]; (clear * - hk hm; omega)), ← List.getD_eq_getElem?_getD, entry_length]
    simp only [List.getElem_cons_succ]
    rw [← ih]
    congr 1
    (clear * - hk hm; omega)

/-- The four answer words of the entry at tape position `x`. -/
def ansW (I : Array Word) (x : Word) : List Word :=
  [I.getD (aposW I x + 0).toNat 0, I.getD (aposW I x + 1).toNat 0,
   I.getD (aposW I x + 2).toNat 0, I.getD (aposW I x + 3).toNat 0]

theorem keyW_eq (I : Array Word) (x : Word) : keyW I x = ansW I x ++ [x] := rfl

theorem ansW_length (I : Array Word) (x : Word) : (ansW I x).length = 4 := rfl

/-- `packBytes` is injective on digests. -/
theorem packBytes_digest_inj {d d' : Digest} (h : packBytes d.toList = packBytes d'.toList) :
    d = d' := by
  have h1 := readDigest_packBytes d []
  rw [h, readDigest_packBytes d' []] at h1
  simpa using h1.symm

/-! ## Lexicographic order on keys -/

theorem lexW_append : ∀ (a b : List Word), a.length = b.length → ∀ x y : Word,
    lexW (a ++ [x]) (b ++ [y]) = (lexW a b || (decide (a = b) && decide (x < y)))
  | [], [], _, x, y => by simp [lexW]
  | a :: as, b :: bs, hl, x, y => by
    have ih := lexW_append as bs (by simpa using hl) x y
    simp only [List.cons_append, lexW, ih, List.cons.injEq]
    by_cases h1 : a < b <;> by_cases h2 : a = b <;> simp [h1, h2]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-! ## The pure lower-bound search -/

/-- One halving of `[lo, lo + len)`. -/
def bsStep (p : ℕ → Bool) (st : ℕ × ℕ) : ℕ × ℕ :=
  if st.2 = 0 then st
  else if p (st.1 + st.2 / 2) then (st.1 + st.2 / 2 + 1, st.2 - st.2 / 2 - 1)
  else (st.1, st.2 / 2)

/-- `m` halvings. -/
def bsRun (p : ℕ → Bool) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, st => st
  | m + 1, st => bsRun p m (bsStep p st)

/-- The search's invariant: `p` holds below `lo`, fails on `[lo + len, n)`. -/
def BsInv (p : ℕ → Bool) (n : ℕ) (st : ℕ × ℕ) : Prop :=
  st.1 + st.2 ≤ n ∧ (∀ a < st.1, p a = true) ∧ ∀ a, st.1 + st.2 ≤ a → a < n → p a = false

theorem bsStep_inv {p : ℕ → Bool} {n : ℕ}
    (hp : ∀ a b, a < b → b < n → p b = true → p a = true) {st : ℕ × ℕ} (h : BsInv p n st) :
    BsInv p n (bsStep p st) ∧ (bsStep p st).2 ≤ st.2 / 2 := by
  obtain ⟨lo, len⟩ := st
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  unfold bsStep
  by_cases h0 : len = 0
  · simp only [h0, if_true]; exact ⟨⟨by simpa [h0] using h1, h2, by simpa [h0] using h3⟩, by simp⟩
  rw [if_neg h0]
  by_cases hm : p (lo + len / 2) = true
  · rw [if_pos hm]
    refine ⟨⟨by simp only; (clear * - h1 h0; omega), fun a ha => ?_, fun a ha han => h3 a (by simp only at ha; (clear * - ha; omega)) han⟩,
      by simp only; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - len; omega))⟩
    simp only at ha
    rcases Nat.lt_or_ge a lo with h | h
    · exact h2 a h
    · rcases Nat.lt_or_ge a (lo + len / 2) with h' | h'
      · exact hp a _ h' (by (clear * - h1 h h'; omega)) hm
      · rw [show a = lo + len / 2 by (clear * - ha h'; omega)]; exact hm
  · rw [if_neg hm]
    refine ⟨⟨by simp only; (clear * - h1; omega), h2, fun a ha han => ?_⟩, by simp only; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - len; omega))⟩
    simp only at ha
    rcases Nat.lt_or_ge a (lo + len) with h | h
    · cases e : p a
      · rfl
      · rcases Nat.lt_or_ge (lo + len / 2) a with h' | h'
        · exact absurd (hp _ a h' han e) hm
        · exact absurd (show p (lo + len / 2) = true by rw [show lo + len / 2 = a by (clear * - ha h'; omega)]; exact e)
            hm
    · exact h3 a h han

theorem bsRun_inv {p : ℕ → Bool} {n : ℕ}
    (hp : ∀ a b, a < b → b < n → p b = true → p a = true) :
    ∀ (m : ℕ) (st : ℕ × ℕ), BsInv p n st → BsInv p n (bsRun p m st) ∧
      (bsRun p m st).2 ≤ st.2 / 2 ^ m
  | 0, st, h => ⟨h, by simp [bsRun]⟩
  | m + 1, st, h => by
    obtain ⟨h1, h2⟩ := bsStep_inv hp h
    obtain ⟨h3, h4⟩ := bsRun_inv hp m _ h1
    refine ⟨h3, h4.trans ?_⟩
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right h2

/-- **The lower bound**: 64 halvings from `(0, n)` end at `lo` with `p` true below and false on
`[lo, n)`. -/
theorem bsRun_spec {p : ℕ → Bool} {n : ℕ} (hn : n < 2 ^ 64)
    (hp : ∀ a b, a < b → b < n → p b = true → p a = true) :
    (bsRun p 64 (0, n)).1 ≤ n ∧ (∀ a < (bsRun p 64 (0, n)).1, p a = true) ∧
      ∀ a, (bsRun p 64 (0, n)).1 ≤ a → a < n → p a = false := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := bsRun_inv hp 64 (0, n)
    ⟨by simp, fun a ha => absurd ha (Nat.not_lt_zero _), fun a ha han => by simp at ha; (clear * - han ha; omega)⟩
  have h0 : (bsRun p 64 (0, n)).2 = 0 := by
    have : n / 2 ^ 64 = 0 := Nat.div_eq_of_lt hn
    simp only at h4; (clear * - h4 this; omega)
  rw [h0, Nat.add_zero] at h1 h3
  exact ⟨h1, h2, h3⟩


/-! ## The first preimage in the sorted index -/

/-- The search predicate: the answer at slot `a` is below the target words `T`. -/
def ltT (I : Array Word) (X : ℕ → Word) (T : List Word) (a : ℕ) : Bool := lexW (ansW I (X a)) T

/-! ## The machine: word helpers and the search registers -/

theorem shr_one_toWord {a : ℕ} (ha : a < 2 ^ 64) : XOp.shr.eval (toWord a) 1 = toWord (a / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_ushiftRight, toNat_toWord ha, toNat_toWord (by (clear * - a ha; omega))]
  simp [Nat.shiftRight_eq_div_pow]

theorem sub_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b ≤ a) :
    XOp.sub.eval (toWord a) (toWord b) = toWord (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_sub, toNat_toWord ha, toNat_toWord (by (clear * - b a ha hb; omega)), toNat_toWord (by (clear * - a b ha hb; omega))]
  (clear * - b a ha hb; omega)

theorem eq_bW (a b : Word) : XOp.eq.eval a b = bW (decide (a = b)) := by
  by_cases h : a = b <;> simp [XOp.eval, bW, h]

/-- The answer words as the machine reads them. -/
theorem ansW_getD (I : Array Word) (x : Word) {w : ℕ} (hw : w < 4) :
    I.getD (aposW I x + BitVec.ofNat 64 w).toNat 0 = (ansW I x).getD w 0 := by
  interval_cases w <;> rfl

theorem ansW_eq (I : Array Word) (x : Word) : ansW I x =
    [(ansW I x).getD 0 0, (ansW I x).getD 1 0, (ansW I x).getD 2 0, (ansW I x).getD 3 0] := rfl

/-- The search's registers. -/
def srL : List ℕ := [rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3]

/-- The registers hold the search state `(lo, len)`, the count `n` and the target `T`. -/
structure SRegs (M : Mem) (n lo len : ℕ) (T : List Word) : Prop where
  lo : rd M rLo = toWord lo
  len : rd M rLn = toWord len
  n : rd M rN = toWord n
  q : [rd M rQ0, rd M rQ1, rd M rQ2, rd M rQ3] = T

theorem srL_lt : ∀ r ∈ srL, r < regs := by decide

theorem SRegs.sem {I : Array Word} {P : XIR} {s : St} {n lo len : ℕ} {T : List Word}
    (h : SRegs s.M n lo len T) (hM : Inv s.M) (hP : WF P) (hw : ∀ r ∈ srL, ¬ Writes P r) :
    SRegs (semXIR I P s).M n lo len T := by
  have hf := fun r hr => Lvm.X.frame I P s hP hM r (srL_lt r hr) (hw r hr)
  exact ⟨(hf rLo (by simp [srL])).trans h.lo, (hf rLn (by simp [srL])).trans h.len,
    (hf rN (by simp [srL])).trans h.n, by
      rw [hf rQ0 (by simp [srL]), hf rQ1 (by simp [srL]), hf rQ2 (by simp [srL]),
        hf rQ3 (by simp [srL])]; exact h.q⟩

/-! ## `ansLtIR` and `eqTWord` -/

theorem cmpTWord_sem (I : Array Word) (s : St) (hM : Inv s.M) {w r : ℕ} (hw : w < 4)
    (hr : r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) :
    rd (semXIR I (cmpTWord w r) s).M rF =
      XOp.or.eval (XOp.ltu.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0) (rd s.M r))
        (XOp.and.eval (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0) (rd s.M r))
          (rd s.M rF)) := by
  have hs := hM.1
  simp only [regs] at hs
  rcases hr with rfl | rfl | rfl | rfl <;>
  · simp only [cmpTWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rKa, rG, rH, rF,
      rQ0, rQ1, rQ2, rQ3]
    simp (disch := first | decide | (clear * - s w hs; omega) | (simp only [size_set]; (clear * - s w hs; omega))) only [rd_set_self,
      rd_set_ne]
    rfl

theorem wf_cmpTWord (w r : ℕ) : WF (cmpTWord w r) := by
  simp +decide only [cmpTWord, WF, Prim.dst, rKc, rAd, rKa, rG, rH, rF, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

/-- Registers `cmpTWord` keeps. -/
theorem cmpTWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w r : ℕ) {q : ℕ}
    (hq : q ∈ [rPa, rX, rHf, rMd] ++ srL) : rd (semXIR I (cmpTWord w r) s).M q = rd s.M q :=
  frame I _ s (wf_cmpTWord w r) hM q
    ((by decide : ∀ r ∈ [rPa, rX, rHf, rMd] ++ srL, r < regs) q hq) (by
    simp only [srL, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [cmpTWord, Writes, Prim.dst, rKc, rAd, rKa, rG, rH, rF, rPa, rX, rHf, rMd,
        rLo, rLn, rN, rQ0, rQ1, rQ2, rQ3, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp,
        exists_eq_left, or_false])

theorem wf_aposIR' : WF (aposIR rPa rX) := wf_aposIR (.inl rfl)

theorem aposIR_frame' (I : Array Word) (s : St) (hM : Inv s.M) {q : ℕ}
    (hq : q ∈ [rX, rHf, rMd] ++ srL) : rd (semXIR I (aposIR rPa rX) s).M q = rd s.M q :=
  frame I _ s wf_aposIR' hM q
    ((by decide : ∀ r ∈ [rX, rHf, rMd] ++ srL, r < regs) q hq) (by
    simp only [srL, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [aposIR, ceil8Ps, Writes, Prim.dst, rQL, rKc, rT2, rPa, rX, rHf, rMd, rLo,
        rLn, rN, rQ0, rQ1, rQ2, rQ3, or_false, List.cons_append, List.nil_append])

/-- **The answer comparison**: `rF := ansW(rX) <_lex (rQ0, …, rQ3)`. -/
theorem ansLtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I ansLtIR s).M rF = bW (lexW (ansW I (rd s.M rX))
      [rd s.M rQ0, rd s.M rQ1, rd s.M rQ2, rd s.M rQ3]) := by
  set x := rd s.M rX
  have hM1 := inv_sem I wf_aposIR' hM
  have ha1 := aposIR_sem I s hM (.inl ⟨rfl, rfl⟩)
  have hq1 : ∀ q ∈ [rQ0, rQ1, rQ2, rQ3], rd (semXIR I (aposIR rPa rX) s).M q = rd s.M q :=
    fun q hq => aposIR_frame' I s hM
      ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r ∈ [rX, rHf, rMd] ++ srL) q hq)
  rw [ansLtIR, semXIR_seq]
  generalize semXIR I (aposIR rPa rX) s = s1 at hM1 ha1 hq1
  have hs1 := hM1.1
  simp only [regs] at hs1
  rw [semXIR_seq]
  have hwf2 : WF (.blk [.const rF 0]) := by simp +decide only [WF, Prim.dst, rF]
  have hM2 := inv_sem I hwf2 hM1
  have hf2 : rd (semXIR I (.blk [.const rF 0]) s1).M rF = bW false := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rF]; (clear * - hs1; omega))]; rfl
  have hfr2 : ∀ q ∈ [rPa, rQ0, rQ1, rQ2, rQ3], rd (semXIR I (.blk [.const rF 0]) s1).M q =
      rd s1.M q := fun q hq => by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne ((by decide : ∀ r ∈ [rPa, rQ0, rQ1, rQ2, rQ3], rF ≠ r) q hq)
  generalize semXIR I (.blk [.const rF 0]) s1 = s2 at hM2 hf2 hfr2
  have step : ∀ (s' : St), Inv s'.M → rd s'.M rPa = aposW I x →
      (∀ q ∈ [rQ0, rQ1, rQ2, rQ3], rd s'.M q = rd s.M q) →
      ∀ (w r : ℕ) (p : Bool), w < 4 → (r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) → rd s'.M rF = bW p →
      rd (semXIR I (cmpTWord w r) s').M rF = bW (decide ((ansW I x).getD w 0 < rd s.M r) ||
        (decide ((ansW I x).getD w 0 = rd s.M r) && p)) ∧
      Inv (semXIR I (cmpTWord w r) s').M ∧ rd (semXIR I (cmpTWord w r) s').M rPa = aposW I x ∧
      (∀ q ∈ [rQ0, rQ1, rQ2, rQ3], rd (semXIR I (cmpTWord w r) s').M q = rd s.M q) :=
    fun s' hM' ha hq w r p hw hr hf => by
      have hrq : rd s'.M r = rd s.M r := hq r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)
      refine ⟨?_, inv_sem I (wf_cmpTWord w r) hM', by
        rw [cmpTWord_frame I s' hM' w r (by simp), ha], fun q hqm => by
        rw [cmpTWord_frame I s' hM' w r
          ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r ∈ [rPa, rX, rHf, rMd] ++ srL) q hqm), hq q hqm]⟩
      rw [cmpTWord_sem I s' hM' hw hr, ha, hf, hrq, ansW_getD I x hw, fold_bW]
  rw [semXIR_seq]
  obtain ⟨f3, m3, a3, q3⟩ := step s2 hM2 (by rw [hfr2 rPa (by simp), ha1])
    (fun q hq => by rw [hfr2 q ((by decide : ∀ r ∈ [rQ0, rQ1, rQ2, rQ3], r ∈ [rPa, rQ0, rQ1, rQ2, rQ3]) q hq),
      hq1 q hq]) 3 rQ3 _ (by decide)
    (.inr (.inr (.inr rfl))) hf2
  generalize semXIR I (cmpTWord 3 rQ3) s2 = s3 at f3 m3 a3 q3
  rw [semXIR_seq]
  obtain ⟨f2, m2, a2, q2⟩ := step s3 m3 a3 q3 2 rQ2 _ (by decide) (.inr (.inr (.inl rfl))) f3
  generalize semXIR I (cmpTWord 2 rQ2) s3 = s4 at f2 m2 a2 q2
  rw [semXIR_seq]
  obtain ⟨f1, m1, a1, q1⟩ := step s4 m2 a2 q2 1 rQ1 _ (by decide) (.inr (.inl rfl)) f2
  generalize semXIR I (cmpTWord 1 rQ1) s4 = s5 at f1 m1 a1 q1
  obtain ⟨f0, -, -, -⟩ := step s5 m1 a1 q1 0 rQ0 _ (by decide) (.inl rfl) f1
  rw [f0, ansW_eq I x]
  rfl


theorem wf_ansLtIR : WF ansLtIR := by
  simp +decide only [ansLtIR, aposIR, ceil8Ps, cmpTWord, WF, Prim.dst, rQL, rKc, rT2, rPa, rAd, rKa,
    rG, rH, rF, and_true, List.cons_append, List.nil_append]

theorem ansLtIR_frame (I : Array Word) (s : St) (hM : Inv s.M) {q : ℕ}
    (hq : q ∈ [rHf, rMd] ++ srL) : rd (semXIR I ansLtIR s).M q = rd s.M q :=
  frame I _ s wf_ansLtIR hM q ((by decide : ∀ r ∈ [rHf, rMd] ++ srL, r < regs) q hq)
    ((by simp only [srL, ansLtIR, aposIR, ceil8Ps, cmpTWord, Writes, List.cons_append,
      List.nil_append]; decide : ∀ r ∈ [rHf, rMd] ++ srL, ¬ Writes ansLtIR r) q hq)

theorem nw_ansLtIR : ∀ r ∈ srL, ¬ Writes ansLtIR r := by
  simp only [srL, ansLtIR, aposIR, ceil8Ps, cmpTWord, Writes, List.cons_append, List.nil_append]
  decide

theorem bsStep_le {p : ℕ → Bool} {n lo len : ℕ} (h : lo + len ≤ n) :
    (bsStep p (lo, len)).1 + (bsStep p (lo, len)).2 ≤ n := by
  unfold bsStep; split_ifs <;> simp only <;> omega

/-! ## The search loop and the found flag -/

theorem SRegs.decS {s : St} {n lo len : ℕ} {T : List Word} (h : SRegs s.M n lo len T) :
    SRegs (decS rCB s).M n lo len T :=
  ⟨(rd_decS (by decide) s).trans h.lo, (rd_decS (by decide) s).trans h.len,
    (rd_decS (by decide) s).trans h.n, by
      rw [rd_decS (by decide), rd_decS (by decide), rd_decS (by decide), rd_decS (by decide)]
      exact h.q⟩

theorem bsRun_le {p : ℕ → Bool} {n : ℕ} :
    ∀ (m lo len : ℕ), lo + len ≤ n → (bsRun p m (lo, len)).1 + (bsRun p m (lo, len)).2 ≤ n
  | 0, _, _, h => h
  | m + 1, lo, len, h => bsRun_le m _ _ (bsStep_le h)

theorem eqTWord_sem (I : Array Word) (s : St) (hM : Inv s.M) {w r : ℕ}
    (hr : r = rQ0 ∨ r = rQ1 ∨ r = rQ2 ∨ r = rQ3) :
    rd (semXIR I (eqTWord w r) s).M rFd = XOp.and.eval (rd s.M rFd)
      (XOp.eq.eval (I.getD (rd s.M rPa + BitVec.ofNat 64 w).toNat 0) (rd s.M r)) := by
  have hs := hM.1
  simp only [regs] at hs
  rcases hr with rfl | rfl | rfl | rfl <;>
  · simp only [eqTWord, semXIR, runPrims, List.foldl, Prim.run, rKc, rAd, rPa, rKa, rH, rFd,
      rQ0, rQ1, rQ2, rQ3]
    simp (disch := first | decide | (clear * - s hs; omega) | (simp only [size_set]; (clear * - s hs; omega))) only [rd_set_self,
      rd_set_ne]
    rfl

theorem wf_eqTWord (w r : ℕ) : WF (eqTWord w r) := by
  simp +decide only [eqTWord, WF, Prim.dst, rKc, rAd, rKa, rH, rFd, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem eqTWord_frame (I : Array Word) (s : St) (hM : Inv s.M) (w r : ℕ) {q : ℕ}
    (hq : q ∈ [rPa] ++ srL) : rd (semXIR I (eqTWord w r) s).M q = rd s.M q :=
  frame I _ s (wf_eqTWord w r) hM q ((by decide : ∀ r ∈ [rPa] ++ srL, r < regs) q hq) (by
    simp only [srL, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [eqTWord, Writes, Prim.dst, rKc, rAd, rKa, rH, rFd, rPa, rLo, rLn, rN, rQ0,
        rQ1, rQ2, rQ3, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])

theorem decide_ansW (A : List Word) (hA : A.length = 4) (t0 t1 t2 t3 : Word) (p : Bool) :
    (p && decide (A.getD 0 0 = t0) && decide (A.getD 1 0 = t1) && decide (A.getD 2 0 = t2) &&
      decide (A.getD 3 0 = t3)) = (p && decide (A = [t0, t1, t2, t3])) := by
  match A, hA with
  | [a0, a1, a2, a3], _ => simp [Bool.and_assoc]

/-! ## The lookup -/

theorem entryKB {M : Mem} (hM : Inv M) (hN : rd M rNB = 64) :
    rd (entryK rCB rNB 64 M) rCB = 64 := by
  have hs := hM.1
  simp only [regs] at hs
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds rCB 64) rNB = 64 := by rw [rd_set_ne (by decide), hN]
  have h2 : rd (M.setIfInBounds rCB 64) rCB = 64 := rd_set_self (by simp only [rCB]; (clear * - hs; omega))
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp]; (clear * - hs; omega))]
  rw [if_pos (by decide), rd_set_ne (by decide), h2]

/-! ## A lookup after the log index -/

/-! ## The lookup at a parametric base and log position

The index base `bX` and the tape word `pL` of `|L|` are parameters; lvm's instance is
`bX = memX`, `pL = posL pz`. -/

section Idx

variable (bX pL : ℕ)

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


variable {bX pL} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

omit hbX hbX2 hpL in
/-- **The tape at entry `k`'s answer**: word `m < 4` of `packBytes L[k].2`. -/
theorem tape_answer4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL) {k : ℕ}
    (hk : k < L.length) {m : ℕ} (hm : m < 4) :
    (extractorInput c π L).getD (pL + 1 + entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) 0 =
      (packBytes L[k].2.toList).getD m 0 := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> (clear * - hs; omega)
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, show pL + 1 + entryOff L k + 1 +
      (L[k].1.size + 7) / 8 + m = (pL + 1) + (entryOff L k + 1 + (L[k].1.size + 7) / 8 + m) by
      (clear * - hk; omega), ← hl, List.getElem?_append_right (by (clear * - hk hm; omega)), Nat.add_sub_cancel_left,
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
    · rw [show k + 1 = L.length by (clear * - hk h; omega)]
  rw [entryOff_succ L hk] at hk1
  have hqw : qWords L[k] = 5 + (L[k].1.size + 7) / 8 := rfl
  have hx : (toWord (posE4 pL L k)).toNat = posE4 pL L k := toNat_toWord (by simp only [posE4]; (clear * - ht hk hend hq' hk1 hqw; omega))
  have hap : ∀ j < 4, (aposW I (toWord (posE4 pL L k)) + toWord j).toNat =
      pL + 1 + entryOff L k + 1 + (L[k].1.size + 7) / 8 + j := fun j hj => by
    have h1 : I.getD (posE4 pL L k) 0 = toWord L[k].1.size := by
      rw [hI, getD_toArray]; exact tape_entry4 c π L hs hk
    simp only [aposW, hx, h1]
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, toNat_ceil8 hq', hx,
      toNat_toWord (show j < 2 ^ 64 by (clear * - hk hj; omega)), show (1 : Word).toNat = 1 from rfl]
    simp only [posE4] at hx ⊢
    (clear * - hs ht hk hend hq' hk1 hqw hx hj; omega)
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
  simp only [posE4]; (clear hk hs; omega)


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
      (∀ k, ansIdx L t = some k → b < L.length ∧ X b = toWord (posE4 pL L k)) ∧
      (ansIdx L t = none → ∀ a < L.length,
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
        obtain ⟨k', hk', e', hA'⟩ := hA a (by (clear * - ha0 ha; omega))
        have hkt' : L[k'].2 = t := packBytes_digest_inj (by rw [← hA', h', hA0])
        rw [e', e0, BitVec.lt_def, toNat_toWord (posE_lt4 c π L hs ht hk'),
          toNat_toWord (posE_lt4 c π L hs ht hkl)] at hlt
        have hkk : k' < k := by
          by_contra hge
          rcases Nat.lt_or_ge k k' with h2 | h2
          · have := entryOff_lt L h2 hk'.le; simp only [posE4] at hlt; (clear * - hlt this; omega)
          · have : k = k' := by (clear * - hge h2; omega)
            subst this; (clear * - hlt; omega)
        have := hfirst k' hkk
        simp [hkt'] at this
    have hb1 : b ≤ a0 := by
      by_contra h
      have := hlo a0 (by (clear * - h; omega))
      rw [hf0] at this; exact absurd this (by decide)
    have hb2 : a0 ≤ b := by
      by_contra h
      have h1 := ht0 b (by (clear * - h; omega))
      rw [hhi b le_rfl (by (clear * - hbn ha0 h; omega))] at h1; exact absurd h1 (by decide)
    have : b = a0 := by (clear * - hb1 hb2; omega)
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
    have := congrArg BitVec.toNat h; rwa [toNat_toWord (by (clear * - hb hn; omega))] at this)
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
    simp (disch := first | decide | (simp only [size_set, rKc, rHf, rMd, rAd]; (clear * - s bX pL n lo len hs; omega))) only
      [rd_set_self, rd_set_ne] <;>
    rw [hR.len, shr_one_toWord (by (clear * - hb hn; omega))]
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
    rw [rd_set_self (by simp only [rX]; (clear * - hs1; omega)), ha1, toNat_toWord (by (clear * - hbX2 hb hn; omega)),
      hH1 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2 hb hn; omega)), show lo + len / 2 + bX = bX + (lo + len / 2) by
      (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega), hX _ (by (clear * - hb hn h0; omega))]
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
    simp (disch := first | decide | (simp only [size_set, rLo, rLn]; (clear * - s3 bX pL s n lo len s1 hs3; omega))) only
      [rd_set_self, rd_set_ne]
    · rw [hmd3, hc3, add_one_toWord]
    · rw [hR3.len, hhf3, hc3, sub_toWord (by (clear * - hb hn; omega)) (by (clear * - hb hn; omega)),
        show (1 : Word) = toWord 1 from rfl, sub_toWord (by (clear * - hb hn; omega)) (by (clear * - hb hn h0; omega))]
    · exact hR3.n
    · exact hR3.q
  · rw [(Bool.not_eq_true _).mp hp, if_pos bW_false, if_neg (by simp)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [semXIR, runPrims, List.foldl, Prim.run] <;>
    simp (disch := first | decide | (simp only [size_set, rLn]; (clear * - s3 bX pL s n lo len s1 hs3; omega))) only
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
      fun i hi => rd_decS (by simp only [rCB]; (clear * - hi; omega)) _
    have hH' : ∀ x, regs ≤ x → rd (decS rCB (semXIR I (bsBody4 bX) s)).M x = rd s.M x :=
      fun x hx => (rd_decS (by (clear * - hx; (try simp only [rCB, regs] at *); omega)) _).trans (hH x hx)
    obtain ⟨a, b, c⟩ := bsLoop4 I hn m _ _ _ hM' h1.decS (bsStep_le hb)
      (fun a ha => by rw [hH' _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hX a ha])
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
    rw [rd_set_self (by simp only [size_set, rX]; (clear * - hs; omega))]
    simp (disch := first | decide | (simp only [size_set, rKc, rAd]; (clear * - s bX pL n lo hs; omega))) only [rd_set_self,
      rd_set_ne]
    rw [hR.lo, show XOp.add.eval (toWord lo) (BitVec.ofNat 64 bX) = toWord (lo + bX) from
      add_toWord _ _, toNat_toWord (by (clear * - hbX2 hlo hn; omega)), rd_set_ne (by simp only [rAd, regs] at hbX ⊢; (clear * - hbX hbX2; omega)),
      rd_set_ne (by simp only [rKc, regs] at hbX ⊢; (clear * - hbX hbX2; omega)), show lo + bX = bX + lo by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
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
    rw [rd_set_self (by simp only [rFd]; (clear * - hs2; omega)), hR2.lo, hR2.n, ltW_toWord (by (clear * - hlo hn; omega)) (by (clear * - hn; omega))]
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
    have hN := rd_readAt I s hM (d := rN) (pos := pL) (by decide) (by (clear * - hpL; omega))
    have hwfr : WF (readAt rN pL) := by simp +decide [readAt, WF, Prim.dst, rN, rA, and_true]
    have hM' := inv_sem I hwfr hM
    have hq' : [rd (semXIR I (readAt rN pL) s).M rQ0, rd (semXIR I (readAt rN pL) s).M rQ1,
        rd (semXIR I (readAt rN pL) s).M rQ2, rd (semXIR I (readAt rN pL) s).M rQ3] = T := by
      have hf := fun r (hr : r ∈ [rQ0, rQ1, rQ2, rQ3]) => Lvm.X.frame I _ s hwfr hM r
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
    simp (disch := first | decide | (simp only [size_set, rLo, rLn, rNB]; (clear * - s' bX pL s n hs'; omega))) only
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
    fun i hi => hE i (by simp only [rCB]; (clear * - hi; omega)) (by simp only [cTmp]; (clear * - hi; omega))
  have hRE : SRegs (entryK rCB rNB 64 s0.M) n 0 n T :=
    ⟨(hE _ (by decide) (by decide)).trans hR0.lo, (hE _ (by decide) (by decide)).trans hR0.len,
      (hE _ (by decide) (by decide)).trans hR0.n, by
        rw [hE rQ0 (by decide) (by decide), hE rQ1 (by decide) (by decide),
          hE rQ2 (by decide) (by decide), hE rQ3 (by decide) (by decide)]; exact hR0.q⟩
  have hHE : ∀ x, regs ≤ x → rd (entryK rCB rNB 64 s0.M) x = rd s.M x := fun x hx => by
    rw [hE x (by (clear * - hx; (try simp only [rCB, regs] at *); omega)) (by (clear * - hx; (try simp only [cTmp, regs] at *); omega)),
      hH0 x hx]
  obtain ⟨l1, l2, l3⟩ := bsLoop4 hbX hbX2 hpL I (X := X) hn2 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ 0 n (by dsimp only; exact hME) (by dsimp only; exact hRE)
    (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - n; omega))) (fun a ha => by rw [hHE (bX + a) (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hX a ha])
  generalize iterL (semXIR I (bsBody4 bX)) rCB 64 ⟨entryK rCB rNB 64 s0.M, s0.o⟩ = s1 at l1 l2 l3
  have hle := bsRun_le (p := ltT I X T) (n := n) 64 0 n (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - n; omega)))
  obtain ⟨f1, f2⟩ := foundIR4_sem hbX hbX2 hpL I s1 l1 l2 (le_trans (Nat.le_add_right _ _) hle) hn2
  have hH1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => (l3 x hx).trans (hHE x hx)
  refine ⟨f2, ?_, fun x hx => (hframe I (foundIR4 bX) s1 (by
    simp +decide [foundIR4, aposIR, ceil8Ps, eqTWord, Lo, Prim.dst, regs, rKc, rAd, rX, rQL,
      rT2, rPa, rFd, rKa, rH, and_true, List.cons_append, List.nil_append]) x hx).trans (hH1 x hx)⟩
  rw [f1, hH1 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega))]


end Idx

end Lvm.X
