-- New for lvm (WP-13a), after FR's `FRXDec4F0` (`ext4IRWith`, `DecOk4`, `computes4`, `E4X`) and
-- `FRXSpec` (`E`, `Eout`, `InDomE`; rf-k/submissions/flock-recursive/lean@kk/base): lvm's SNARK branch,
-- the extractor program `extX`, its specification `EX` and `Computes`.
import LvmXSearch
import LvmXDecCost
import LvmXRead2
import LvmXDec1Cost
import LvmXOutSeg
import LvmXChainL
import LvmXKeccak

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmXTopOff`, outside its import closure.)

-- ===== merged from `LvmXNode` (GOLF module merge: `LvmXNode.lean` is now a stub importing `LvmXTop`) =====
section
-- New for lvm (WP-13a), after FR's `FRXSpec` (`outIR`, `slotIR`, the node output) and `FRXLeaf`
-- (rf-k/submissions/flock-recursive/lean@kk/base): lvm's node witness and its output program.

/-!
# The node witness and the output program (BLUEPRINT §6.2 step 7)

**The witness** `Xwit π w` of an `S` proof with `b = 1` whose `C_rec` decodes to the message
words `w` (`2^19`; column `l` at words `l·2^14 + i`, stream lane `17i + l` = `crecIdx`, the
signature column 17):

`node c_L (leafStmt h n) ⟨reassembleL tr', tr', σ'⟩ ⟨encode (leaf s n), [], σ_leaf⟩`

with `c_L, s, n, h, σ_leaf` π's header fields (packed words 6–9, 10–13, 14, 15–18, 19–615), `tr'`
the trace read off the stream (`readTraceL`), `σ'` the signature column's 597 words.
**`witWords_Xwit`**: its output words are `outWords π w`.

**The program** `outIR mB` (after the decoder left `w` at `mB`): the tag, `c_L` (tape copy),
`leafStmt h n` (`LvmXKeccak`), `|π'|`, the stream copied to `sgB` (`copyIR`), the proof's and the
trace's segments over it (`LvmXOutSeg`), the signature column, the right child. **`outIR_sem`**.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## The witness -/

/-- π's packed word `j`. -/
def pw (π : Proof) (j : ℕ) : Word := (packBytes π.data.toList).getD j 0

/-- A signature from its 597 words: the index, 133 chain values, 16 path digests. -/
def sigOfF (f : ℕ → Word) : Sig :=
  ⟨(f 0).toNat, (List.range wotsLen).map fun k => digW (wsAt f (1 + 4 * k) 4),
    (List.range sigHeight).map fun k => digW (wsAt f (1 + 4 * wotsLen + 4 * k) 4)⟩

theorem flatMap_digW (f : ℕ → Word) (a : ℕ) : ∀ m : ℕ,
    ((List.range m).map fun k => digW (wsAt f (a + 4 * k) 4)).flatMap (fun d => packBytes d.toList) =
      wsAt f a (4 * m)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_digW f a m, List.map_singleton,
      List.flatMap_singleton, packBytes_digW (length_wsAt _ _ _), show 4 * (m + 1) = 4 * m + 4 by ring,
      wsAt_add]

theorem sigWords_sigOfF (f : ℕ → Word) : sigWords (sigOfF f) = wsAt f 0 597 := by
  have h1 := flatMap_digW f 1 wotsLen
  have h2 := flatMap_digW f (1 + 4 * wotsLen) sigHeight
  simp only [sigWords, sigOfF, h1, h2, toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show (597 : ℕ) = 1 + (4 * wotsLen + 4 * sigHeight) from rfl, wsAt_add, wsAt_add]
  simp [wsAt, wotsLen]

/-- The stream lane `u` of a decoded `C_rec` message: column `u mod 17`, row `⌊u/17⌋`. -/
def crecIdx (u : ℕ) : ℕ := u % 17 * 2 ^ 14 + u / 17

/-- The stream's lanes. -/
def laneOf (w : ℕ → Word) (u : ℕ) : Word := w (crecIdx u)

/-- The signature column (column 17). -/
def sigCol (w : ℕ → Word) (j : ℕ) : Word := w (17 * 2 ^ 14 + j)

/-- `π`'s header digest at packed word `j`. -/
def hdD (π : Proof) (j : ℕ) : Digest := digW (wsAt (pw π) j 4)

/-- **The node witness** of an `S` proof (`b = 1`) whose `C_rec` decodes to `w`. -/
def Xwit (π : Proof) (w : ℕ → Word) : Wit :=
  .node (hdD π 6) (leafStmt (hdD π 15) (pw π 14).toNat)
    ⟨reassembleL (readTraceL (laneOf w)), readTraceL (laneOf w), sigOfF (sigCol w)⟩
    ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩

theorem toWord_toNat' (x : Word) : toWord x.toNat = x := by simp [toWord]

theorem signed_right (π : Proof) :
    signedWords ⟨WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat), [], sigOfF fun j => pw π (19 + j)⟩ =
      (toWord 48 :: toWord 0 :: wsAt (pw π) 10 4 ++ [pw π 14]) ++ [toWord 0] ++
        wsAt (fun j => pw π (19 + j)) 0 597 := by
  have hl : (WitnessSending.encode (.leaf (hdD π 10) (pw π 14).toNat)).data.toList.length = 48 := by
    rw [Array.length_toList]; exact WitnessSending.size_encode_leaf _ _
  rw [signedWords, bytesWords, hl, WitnessSending.encode_data, packBytes_wordsBytes, sigWords_sigOfF]
  simp only [witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat', logWords,
    List.length_nil, List.flatMap_nil, List.cons_append, List.append_assoc]

end Lvm.X
end
-- ===== end of `LvmXNode` =====

-- ===== merged from `LvmXEmit` (GOLF module merge: `LvmXEmit.lean` is now a stub importing `LvmXTop`) =====
section
-- New for lvm (WP-13a): small output emitters (a constant word, a copy of tape words) and the copy of
-- the decoded stream to a contiguous buffer. FR's counterparts are `FRXLeaf.leafIR`/`outAt`
-- (rf-k/submissions/flock-recursive/lean@kk/base); the loop lemma is `LvmXSeg.loopK_emit`.

/-!
# Emitters and the stream copy

* `emitIR w`: output the constant `w` (`emitIR_sem`).
* `tcpIR a n`: output tape words `a … a + n − 1` (`tcpIR_sem`).
* `copyIR mB`: `sgB + u := M[mB + crecIdx u]` for `u < 17·2^14`, the stream's lanes in a contiguous
  buffer (`copyIR_sem`).

Registers `120 … 129`. None of these writes a heap cell but `copyIR` (the buffer only).
-/

namespace Lvm.X

open RecursionFast Lvm

/-- The word emitted. -/ def eW : ℕ := 120
/-- The tape position / the lane. -/ def eP : ℕ := 121
/-- The loop count. -/ def eN : ℕ := 122
/-- The loop counter. -/ def eC : ℕ := 123
/-- The row `⌊u/17⌋`. -/ def eQ : ℕ := 124
/-- The column `u mod 17`. -/ def eR : ℕ := 125
/-- An address. -/ def eA : ℕ := 126
/-- Constant scratch. -/ def eK : ℕ := 128

/-- The stream buffer's base. -/
def sgB : ℕ := 16842752
/-- The stream buffer's lanes: `17 · 2^14`. -/
def nCp : ℕ := 278528

theorem nCp_eq : nCp = 17 * 2 ^ 14 := rfl

/-! ## A constant -/

/-- Output the constant `w`. -/
def emitIR (w : Word) : XIR := .seq (.blk [.const eW w]) (.out eW)

theorem wf_emitIR (w : Word) : WF (emitIR w) := by
  simp +decide [emitIR, WF, Prim.dst, eW]

theorem emitIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (w : Word) :
    (semXIR I (emitIR w) s).o.toList = s.o.toList ++ [w] ∧
    (∀ y, y ≠ eW → rd (semXIR I (emitIR w) s).M y = rd s.M y) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun y hy => ?_⟩
  · simp only [emitIR, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
    rw [rd_set_self (by simp only [eW]; omega)]
  · simp only [emitIR, semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne (Ne.symm hy)

/-! ## A copy of tape words -/

/-- One word: `out I[eP]`, `eP += 1`. -/
def tcpBody : XIR := .seq (.input eW eP) (.seq (.out eW) (.blk [.op .add eP eP cOne]))

/-- **Output tape words `a … a + n − 1`.** -/
def tcpIR (a n : ℕ) : XIR :=
  .seq (.blk [.const eP (toWord a), .const eN (toWord n)]) (.loopK eC eN (toWord n) tcpBody)

theorem wf_tcpIR (a n : ℕ) : WF (tcpIR a n) := by
  simp +decide [tcpIR, tcpBody, WF, Writes, Prim.dst, eW, eP, eN, eC, cTmp, regs]

theorem tcpBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p : ℕ} (hp : rd s.M eP = toWord p)
    (hp2 : p < 2 ^ 64) :
    (semXIR I tcpBody s).o.toList = s.o.toList ++ [I.getD p 0] ∧
    rd (semXIR I tcpBody s).M eP = toWord (p + 1) ∧
    (∀ y, y ≠ eW → y ≠ eP → rd (semXIR I tcpBody s).M y = rd s.M y) ∧
    (semXIR I tcpBody s).M.size = s.M.size := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs
  simp only [tcpBody, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
  refine ⟨?_, ?_, fun y h1 h2 => ?_, by simp⟩
  · rw [rd_set_self (by simp only [eW]; omega), hp, toNat_toWord hp2]
  · simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [hp, h1]
    exact add_one_toWord p
  · rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]

/-- **The tape copy**: `n` tape words from `a` are output; only `eW, eP, eN, eC, cTmp` change. -/
theorem tcpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a n : ℕ} (h : a + n < 2 ^ 64) :
    (semXIR I (tcpIR a n) s).o.toList = s.o.toList ++ (List.range n).map (fun j => I.getD (a + j) 0) ∧
    (∀ y, y ≠ eW → y ≠ eP → y ≠ eN → y ≠ eC → y ≠ cTmp → rd (semXIR I (tcpIR a n) s).M y = rd s.M y) ∧
    Inv (semXIR I (tcpIR a n) s).M ∧ (semXIR I (tcpIR a n) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf := wf_tcpIR a n
  have hM1 : Inv (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M := inv_sem I hwf.1 hM
  have p1 : rd (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M eP = toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have n1 : rd (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M eN = toWord n := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ eP → y ≠ eN →
      rd (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).M y = rd s.M y :=
    fun y a b => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b) _
  have z1 := size_sem I (.blk [.const eP (toWord a), .const eN (toWord n)]) s
  have o1 : (semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s).o = s.o := rfl
  rw [tcpIR, semXIR_seq]
  generalize semXIR I (.blk [.const eP (toWord a), .const eN (toWord n)]) s = s1 at hM1 p1 n1 f1 z1 o1
  -- the loop
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ rd t.M eP = toWord (a + j) ∧
    (∀ y, y ≠ eW → y ≠ eP → y ≠ eN → y ≠ eC → y ≠ cTmp → rd t.M y = rd s.M y) ∧ t.M.size = s.M.size
  have h0 : Q 0 ⟨entryK eC eN (toWord n) s1.M, s1.o⟩ := by
    dsimp only [Q]
    refine ⟨inv_of_frame hM1 (size_entryK eC eN (toWord n) s1.M) fun i hi => entryK_frame _ (by simp only [eC]; omega)
        (by simp only [cTmp]; omega), ?_, fun y a b c d e => ?_, by rw [size_entryK, z1]⟩
    · rw [entryK_frame _ (by decide) (by decide), p1, Nat.add_zero]
    · rw [entryK_frame _ (Ne.symm d) (Ne.symm e), f1 y b c]
  have hf : ∀ j t, j < n → Q j t → (semXIR I tcpBody t).o.toList = t.o.toList ++ [I.getD (a + j) 0] ∧
      Q (j + 1) (decS eC (semXIR I tcpBody t)) := by
    intro j t hj ⟨q1, q2, q3, q4⟩
    obtain ⟨b1, b2, b3, b4⟩ := tcpBody_sem I t q1 q2 (by omega)
    refine ⟨b1, inv_of_frame (inv_sem I hwf.2.2.2.2 q1) (size_decS ..) fun i hi =>
      rd_decS (by simp only [eC]; omega) _, by rw [rd_decS (by decide), b2, Nat.add_assoc],
      fun y a b c d e => by rw [rd_decS (Ne.symm d), b3 y a b, q3 y a b c d e], by rw [size_decS, b4, q4]⟩
  obtain ⟨l1, l2⟩ := loopK_emit I (b := tcpBody) Q (fun j => [I.getD (a + j) 0]) s1 hM1 (by decide)
    (by decide) (by decide) (by omega) n1 h0 hf
  refine ⟨?_, l2.2.2.1, l2.1, l2.2.2.2⟩
  rw [l1, o1, flatMap_single]

/-! ## The stream copy -/

/-- The address arithmetic of lane `eP`: `eA := mB + (eP mod 17)·2^14 + ⌊eP/17⌋`. -/
def cpAddrPs (mB : ℕ) : List Prim :=
  [.const eK 17, .op .divu eQ eP eK, .op .remu eR eP eK, .const eK (toWord (2 ^ 14)),
   .op .mul eA eR eK, .op .add eA eA eQ, .const eK (toWord mB), .op .add eA eA eK]

/-- One lane: `sgB + eP := M[mB + crecIdx eP]`, `eP += 1`. -/
def copyBody (mB : ℕ) : XIR :=
  .seq (.blk (cpAddrPs mB)) (.seq (.load eW eA) (.seq (.blk [.const eK (toWord sgB),
    .op .add eA eP eK]) (.seq (.store eA eW) (.blk [.op .add eP eP cOne]))))

/-- **The stream copy.** -/
def copyIR (mB : ℕ) : XIR :=
  .seq (.blk [.const eP 0, .const eN (toWord nCp)]) (.loopK eC eN (toWord nCp) (copyBody mB))

theorem wf_copyIR (mB : ℕ) : WF (copyIR mB) := by
  simp +decide [copyIR, copyBody, cpAddrPs, WF, Writes, Prim.dst, eW, eP, eN, eC, eQ, eR, eA, eK,
    cTmp, regs]

theorem crecIdx_lt {u : ℕ} (hu : u < nCp) : crecIdx u < 2 ^ 19 := by
  simp only [crecIdx, nCp] at hu ⊢; omega

theorem semXIR_blk_M (I : Array Word) (ps : List Prim) (s : St) :
    (semXIR I (.blk ps) s).M = runPrims ps s.M := rfl

theorem cpAddr_frame (mB : ℕ) (M : Mem) {y : ℕ} (a : y ≠ eQ) (b : y ≠ eR) (c : y ≠ eA)
    (d : y ≠ eK) : rd (runPrims (cpAddrPs mB) M) y = rd M y := by
  have hw : ∀ p ∈ cpAddrPs mB, p.dst ≠ y := fun p hp => by
    simp only [cpAddrPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm a | exact Ne.symm b | exact Ne.symm c | exact Ne.symm d
  exact rd_runPrims_of_not_writes hw _

theorem cpAddr_val (M : Mem) (hs : 256 ≤ M.size) {mB u : ℕ} (hu : u < nCp)
    (hmB : mB < 2 ^ 40) (hp : rd M eP = toWord u) :
    rd (runPrims (cpAddrPs mB) M) eA = toWord (mB + crecIdx u) := by
  simp only [nCp] at hu
  simp only [cpAddrPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  rw [hp, show (17 : Word) = toWord 17 from rfl, divu_toWord (a := u) (b := 17) (by omega) (by norm_num),
    remu_toWord (a := u) (b := 17) (by omega) (by norm_num), mulW_toWord, add_toWord, add_toWord,
    show mB + crecIdx u = u % 17 * 2 ^ 14 + u / 17 + mB by unfold crecIdx; omega]

theorem copyBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {mB u : ℕ} (hu : u < nCp)
    (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size)
    (hp : rd s.M eP = toWord u) :
    rd (semXIR I (copyBody mB) s).M (sgB + u) = rd s.M (mB + crecIdx u) ∧
    rd (semXIR I (copyBody mB) s).M eP = toWord (u + 1) ∧
    (∀ y, regs ≤ y → y ≠ sgB + u → rd (semXIR I (copyBody mB) s).M y = rd s.M y) ∧
    Inv (semXIR I (copyBody mB) s).M ∧ (semXIR I (copyBody mB) s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hmB
  have hu' := hu
  simp only [sgB, nCp] at hu' hmB2 hsz
  have hci := crecIdx_lt hu
  have hwf : WF (.blk (cpAddrPs mB)) := by
    intro q hq; simp only [cpAddrPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prim.dst, eQ, eR, eA, eK]
  -- the address
  have a1 : rd (semXIR I (.blk (cpAddrPs mB)) s).M eA = toWord (mB + crecIdx u) := by
    rw [semXIR_blk_M]; exact cpAddr_val s.M hs hu (mB := mB) (by omega) hp
  have f1 : ∀ y, y ≠ eQ → y ≠ eR → y ≠ eA → y ≠ eK →
      rd (semXIR I (.blk (cpAddrPs mB)) s).M y = rd s.M y := fun y a b c d => by
    rw [semXIR_blk_M]; exact cpAddr_frame mB s.M a b c d
  have hM1 := inv_sem I hwf hM
  have z1 := size_sem I (.blk (cpAddrPs mB)) s
  rw [copyBody, semXIR_seq]
  generalize semXIR I (.blk (cpAddrPs mB)) s = s1 at a1 f1 hM1 z1
  -- the load
  obtain ⟨l1, l2, hM2⟩ := load_sem I s1 hM1 (d := eW) (p := eA) (x := mB + crecIdx u) (by decide)
    (by decide) a1 (by omega)
  have z2 := size_sem I (.load eW eA) s1
  rw [semXIR_seq]
  generalize semXIR I (.load eW eA) s1 = s2 at l1 l2 hM2 z2
  -- the store address
  have hwf3 : WF (.blk [.const eK (toWord sgB), .op .add eA eP eK]) := by
    simp +decide [WF, Prim.dst, eK, eA]
  have a3 : rd (semXIR I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2).M eA =
      toWord (sgB + u) := by
    have hs2 := hM2.1
    simp only [regs] at hs2
    rw [semXIR_blk_M]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
    rw [l2 _ (by decide), f1 _ (by decide) (by decide) (by decide) (by decide), hp, add_toWord,
      Nat.add_comm]
  have f3 : ∀ y, y ≠ eK → y ≠ eA →
      rd (semXIR I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2).M y = rd s2.M y :=
    fun y a b => rd_blk_of_not_dst I _ s2 (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b)
  have hM3 := inv_sem I hwf3 hM2
  have z3 := size_sem I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const eK (toWord sgB), .op .add eA eP eK]) s2 = s3 at a3 f3 hM3 z3
  -- the store
  obtain ⟨c1, c2, hM4⟩ := store_sem I s3 hM3 (p := eA) (v := eW) (x := sgB + u) (by decide)
    (by decide) a3 (by simp only [regs, sgB]; omega) (by simp only [sgB]; omega)
    (by rw [z3, z2, z1]; simp only [sgB]; omega)
  have z4 := size_sem I (.store eA eW) s3
  rw [semXIR_seq]
  generalize semXIR I (.store eA eW) s3 = s4 at c1 c2 hM4 z4
  -- `eP += 1`
  have hwf5 : WF (.blk [.op .add eP eP cOne]) := by simp +decide [WF, Prim.dst, eP]
  have hs4 := hM4.1
  simp only [regs] at hs4
  have hreg : ∀ y, y < 256 → y ≠ sgB + u := fun y hy => by simp only [sgB]; omega
  refine ⟨?_, ?_, fun y hy hne => ?_, inv_sem I hwf5 hM4, by rw [size_sem, z4, z3, z2, z1]⟩
  · rw [rd_blk_of_not_dst I _ s4 (by simp [Prim.dst, eP, sgB]; omega), c1,
      f3 _ (by decide) (by decide), l1, f1 _ (by simp only [eQ, sgB] at *; omega)
        (by simp only [eR]; omega) (by simp only [eA]; omega) (by simp only [eK]; omega)]
  · rw [semXIR_blk_M]
    simp only [runPrims, List.foldl, Prim.run]
    have h1 : rd s4.M cOne = 1 := hM4.2 0 (by decide)
    rw [rd_set_self (by simp only [eP]; omega), h1, c2 _ (hreg _ (by decide)) (by decide),
      f3 _ (by decide) (by decide), l2 _ (by decide), f1 _ (by decide) (by decide) (by decide)
        (by decide), hp]
    exact add_one_toWord u
  · simp only [regs] at hy
    rw [rd_blk_of_not_dst I _ s4 (by simp [Prim.dst, eP]; omega), c2 _ hne (by simp only [cTmp]; omega),
      f3 _ (by simp only [eK]; omega) (by simp only [eA]; omega), l2 _ (by simp only [eW]; omega),
      f1 _ (by simp only [eQ]; omega) (by simp only [eR]; omega) (by simp only [eA]; omega)
        (by simp only [eK]; omega)]

/-- **The stream copy**: `sgB + u` holds the message word `crecIdx u` for every `u < 17·2^14`;
the heap outside the buffer is kept; no output. -/
theorem copyIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {mB : ℕ} (hmB : regs ≤ mB)
    (hmB2 : mB + 2 ^ 19 ≤ sgB) (hsz : sgB + nCp ≤ s.M.size) :
    (∀ u < nCp, rd (semXIR I (copyIR mB) s).M (sgB + u) = rd s.M (mB + crecIdx u)) ∧
    (∀ y, regs ≤ y → (y < sgB ∨ sgB + nCp ≤ y) → rd (semXIR I (copyIR mB) s).M y = rd s.M y) ∧
    Inv (semXIR I (copyIR mB) s).M ∧ (semXIR I (copyIR mB) s).M.size = s.M.size ∧
    (semXIR I (copyIR mB) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs
  have hwf := wf_copyIR mB
  have hO : (semXIR I (copyIR mB) s).o = s.o := sem_o I _ s rfl
  rw [copyIR, semXIR_seq] at hO ⊢
  have hM1 := inv_sem I hwf.1 hM
  have p1 : rd (semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s).M eP = toWord 0 := by
    rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]; rfl
  have n1 : rd (semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s).M eN = toWord nCp := by
    rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ eP → y ≠ eN → rd (semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s).M y = rd s.M y :=
    fun y a b => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · exact Ne.symm a
      · exact Ne.symm b)
  have z1 := size_sem I (.blk [.const eP 0, .const eN (toWord nCp)]) s
  generalize semXIR I (.blk [.const eP 0, .const eN (toWord nCp)]) s = s1 at hM1 p1 n1 f1 z1 hO
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M eP = toWord j ∧
    (∀ u < j, rd t.M (sgB + u) = rd s.M (mB + crecIdx u)) ∧
    (∀ y, regs ≤ y → (y < sgB ∨ sgB + j ≤ y) → rd t.M y = rd s.M y)
  have h0 : Q 0 ⟨entryK eC eN (toWord nCp) s1.M, s1.o⟩ := by
    dsimp only [Q]
    refine ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1], by rw [entryK_frame _ (by decide)
      (by decide), p1], fun u hu => absurd hu (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    simp only [regs] at hy
    rw [entryK_frame _ (by simp only [eC]; omega) (by simp only [cTmp]; omega),
      f1 _ (by simp only [eP]; omega) (by simp only [eN]; omega)]
  have hstep : ∀ j t, j < nCp → Q j t → Q (j + 1) (decS eC (semXIR I (copyBody mB) t)) := by
    intro j t hj ⟨q1, q2, q3, q4, q5⟩
    obtain ⟨b1, b2, b3, b4, b5⟩ := copyBody_sem I t q1 hj hmB hmB2 (by rw [q2]; exact hsz) q3
    have hrd : ∀ y, regs ≤ y → rd (decS eC (semXIR I (copyBody mB) t)).M y =
        rd (semXIR I (copyBody mB) t).M y := fun y hy => rd_decS (by simp only [regs, eC] at *; omega) _
    have hcl : crecIdx j < 2 ^ 19 := crecIdx_lt hj
    refine ⟨inv_decS b4 (by decide), by rw [size_decS, b5, q2], by rw [rd_decS (by decide), b2], fun u hu => ?_,
      fun y hy hy' => ?_⟩
    · rw [hrd _ (by simp only [regs, sgB]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with h | rfl
      · rw [b3 _ (by simp only [regs, sgB]; omega) (by omega), q4 u h]
      · rw [b1, q5 _ (by simp only [regs] at hmB ⊢; omega) (.inl (by simp only [sgB] at hmB2 ⊢; omega))]
    · rw [hrd _ hy, b3 _ hy (by omega), q5 _ hy (by omega)]
  have := loopK_run I (copyBody mB) Q ⟨s1.M, s1.o⟩ hM1 (by decide) (by decide) (by decide) n1
    (by simp only [nCp]; norm_num) h0 hstep
  obtain ⟨r1, r2, -, r4, r5⟩ := this
  refine ⟨r4, fun y hy hy' => r5 y hy hy', r1, r2, hO⟩

/-! ## A copy of tape words to the heap -/

/-- One word: `M[eA] := I[eP]`, `eP += 1`, `eA += 1`. -/
def thcpBody : XIR :=
  .seq (.input eW eP) (.seq (.store eA eW) (.blk [.op .add eP eP cOne, .op .add eA eA cOne]))

/-- **Tape words `a … a + n − 1` to the heap at `dst`.** -/
def thcpIR (a dst n : ℕ) : XIR :=
  .seq (.blk [.const eP (toWord a), .const eA (toWord dst), .const eN (toWord n)])
    (.loopK eC eN (toWord n) thcpBody)

theorem wf_thcpIR (a dst n : ℕ) : WF (thcpIR a dst n) := by
  simp +decide [thcpIR, thcpBody, WF, Writes, Prim.dst, eW, eP, eN, eC, eA, cTmp, regs]

theorem thcpBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {p x : ℕ} (hp : rd s.M eP = toWord p)
    (hx : rd s.M eA = toWord x) (hp2 : p + 1 < 2 ^ 64) (hxr : regs ≤ x) (hx2 : x + 1 < 2 ^ 64)
    (hxs : x < s.M.size) :
    rd (semXIR I thcpBody s).M x = I.getD p 0 ∧ rd (semXIR I thcpBody s).M eP = toWord (p + 1) ∧
    rd (semXIR I thcpBody s).M eA = toWord (x + 1) ∧
    (∀ y, y ≠ eW → y ≠ eP → y ≠ eA → y ≠ cTmp → y ≠ x → rd (semXIR I thcpBody s).M y = rd s.M y) ∧
    Inv (semXIR I thcpBody s).M ∧ (semXIR I thcpBody s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs hxr
  rw [thcpBody, semXIR_seq]
  have i1 : rd (semXIR I (.input eW eP) s).M eW = I.getD p 0 := by
    show rd (s.M.setIfInBounds eW (I.getD (rd s.M eP).toNat 0)) eW = _
    rw [rd_set_self (by simp only [eW]; omega), hp, toNat_toWord (by omega)]
  have g1 : ∀ y, y ≠ eW → rd (semXIR I (.input eW eP) s).M y = rd s.M y := fun y hy =>
    rd_set_ne (Ne.symm hy)
  have hM1 := inv_sem I (P := .input eW eP) (show 4 ≤ eW by decide) hM
  have z1 := size_sem I (.input eW eP) s
  generalize semXIR I (.input eW eP) s = s1 at i1 g1 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := eA) (v := eW) (x := x) (by decide) (by decide)
    (by rw [g1 _ (by decide), hx]) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (.store eA eW) s1
  generalize semXIR I (.store eA eW) s1 = s2 at c1 c2 hM2 z2
  have hx' : ∀ r, r < 256 → r ≠ x := fun r hr => by omega
  have h1 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  refine ⟨?_, ?_, ?_, fun y a b c d e => ?_, inv_sem I (by simp +decide [WF, Prim.dst, eP, eA]) hM2,
    by rw [size_sem, z2, z1]⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, eP, eA]; omega), c1, i1]
  · rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [eP]; omega), h1,
      c2 _ (hx' _ (by decide)) (by decide), g1 _ (by decide), hp]
    exact add_one_toWord p
  · rw [semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, eA]; omega), rd_set_ne (show eP ≠ eA by decide),
      rd_set_ne (show eP ≠ cOne by decide), h1, c2 _ (hx' _ (by decide)) (by decide), g1 _ (by decide), hx]
    exact add_one_toWord x
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact ⟨Ne.symm b, Ne.symm c⟩), c2 _ e d, g1 _ a]

/-- **The tape-to-heap copy.** -/
theorem thcpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a dst n : ℕ} (ha : a + n < 2 ^ 63)
    (hd : regs ≤ dst) (hd2 : dst + n < 2 ^ 63) (hds : dst + n ≤ s.M.size) :
    (∀ j < n, rd (semXIR I (thcpIR a dst n) s).M (dst + j) = I.getD (a + j) 0) ∧
    (∀ y, regs ≤ y → (y < dst ∨ dst + n ≤ y) → rd (semXIR I (thcpIR a dst n) s).M y = rd s.M y) ∧
    Inv (semXIR I (thcpIR a dst n) s).M ∧ (semXIR I (thcpIR a dst n) s).M.size = s.M.size ∧
    (semXIR I (thcpIR a dst n) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs hd
  have hwf := wf_thcpIR a dst n
  have hO : (semXIR I (thcpIR a dst n) s).o = s.o := sem_o I _ s rfl
  rw [thcpIR, semXIR_seq] at hO ⊢
  set B := (Prim.const eP (toWord a)) :: (Prim.const eA (toWord dst)) :: [Prim.const eN (toWord n)]
  have hM1 := inv_sem I hwf.1 hM
  have v : rd (semXIR I (.blk B) s).M eP = toWord a ∧ rd (semXIR I (.blk B) s).M eA = toWord dst ∧
      rd (semXIR I (.blk B) s).M eN = toWord n := by
    rw [semXIR_blk_M]; simp only [B, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;> simp (disch := first | decide | omega | exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption) | (simp only [size_set]; exact Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))) only [rd_set_self, rd_set_ne]
  have f1 : ∀ y, y ≠ eP → y ≠ eA → y ≠ eN → rd (semXIR I (.blk B) s).M y = rd s.M y :=
    fun y x1 x2 x3 => rd_blk_of_not_dst I _ s (by
      simp only [B, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl | rfl)
      · exact Ne.symm x1
      · exact Ne.symm x2
      · exact Ne.symm x3)
  have z1 := size_sem I (.blk B) s
  obtain ⟨v1, v2, v3⟩ := v
  generalize semXIR I (.blk B) s = s1 at hM1 v1 v2 v3 f1 z1 hO
  let Q : ℕ → St → Prop := fun j t => Inv t.M ∧ t.M.size = s.M.size ∧ rd t.M eP = toWord (a + j) ∧
    rd t.M eA = toWord (dst + j) ∧ (∀ i < j, rd t.M (dst + i) = I.getD (a + i) 0) ∧
    (∀ y, regs ≤ y → (y < dst ∨ dst + j ≤ y) → rd t.M y = rd s.M y)
  have h0 : Q 0 ⟨entryK eC eN (toWord n) s1.M, s1.o⟩ := by
    dsimp only [Q]
    refine ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1], by rw [entryK_frame _ (by decide)
      (by decide), v1, Nat.add_zero], by rw [entryK_frame _ (by decide) (by decide), v2, Nat.add_zero],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    simp only [regs] at hy
    rw [entryK_frame _ (by simp only [eC]; omega) (by simp only [cTmp]; omega),
      f1 _ (by simp only [eP]; omega) (by simp only [eA]; omega) (by simp only [eN]; omega)]
  have hstep : ∀ j t, j < n → Q j t → Q (j + 1) (decS eC (semXIR I thcpBody t)) := by
    intro j t hj ⟨q1, q2, q3, q4, q5, q6⟩
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := thcpBody_sem I t q1 q3 q4 (by omega) (by simp only [regs]; omega)
      (by omega) (by rw [q2]; omega)
    have hrd : ∀ y, y ≠ eC → rd (decS eC (semXIR I thcpBody t)).M y = rd (semXIR I thcpBody t).M y :=
      fun y hy => rd_decS (Ne.symm hy) _
    refine ⟨inv_decS b5 (by decide), by rw [size_decS, b6, q2], by rw [hrd _ (by decide), b2, Nat.add_assoc],
      by rw [hrd _ (by decide), b3, Nat.add_assoc], fun i hi => ?_, fun y hy hy' => ?_⟩
    · rw [hrd _ (by simp only [eC]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [b4 _ (by simp only [eW]; omega) (by simp only [eP]; omega) (by simp only [eA]; omega)
          (by simp only [cTmp]; omega) (by omega), q5 i h]
      · exact b1
    · simp only [regs] at hy
      rw [hrd _ (by simp only [eC]; omega), b4 _ (by simp only [eW]; omega) (by simp only [eP]; omega)
        (by simp only [eA]; omega) (by simp only [cTmp]; omega) (by omega), q6 _ (by simp only [regs]; omega)
        (by omega)]
  obtain ⟨r1, r2, -, -, r5, r6⟩ := loopK_run I thcpBody Q ⟨s1.M, s1.o⟩ hM1 (by decide) (by decide)
    (by decide) v3 (by omega) h0 hstep
  exact ⟨r5, r6, r1, r2, hO⟩

theorem cost_thcpIR (a dst n t : ℕ) (hn : n < 2 ^ 64) : cost (thcpIR a dst n) t = 14 + n * 13 := by
  simp only [thcpIR, thcpBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

end Lvm.X
end
-- ===== end of `LvmXEmit` =====

-- ===== merged from `LvmXNodeIR` (GOLF module merge: `LvmXNodeIR.lean` is now a stub importing `LvmXTop`) =====
section
-- New for lvm (WP-13a), after FR's `FRXSpec` (`outIR`, `seg_step`, `setR`; rf-k/submissions/
-- flock-recursive/lean@kk/base): the node witness's output program and its semantics.

/-!
# The node output program (BLUEPRINT §6.2 step 7)

`outIR mB` emits `outWords π w` (`LvmXNode`) when the decoded message `w` sits at `mB`:
the tag, `c_L`, `leafStmt h n` (Keccak), `|π'|`, then the stream is copied to `sgB` and the proof's
and trace's segments are emitted over it, the signature column, the right child. **`outIR_sem`**.
-/

namespace Lvm.X

open RecursionFast Lvm

/-- Point the segment compiler at the source `R` (base offset 0, kind flag off). -/
def setR (R : ℕ) : XIR := .blk [.const oR (toWord R), .const oKF 0, .const (oBd 0) 0]

/-- The signature column's base. -/
def sigB (mB : ℕ) : ℕ := mB + 17 * 2 ^ 14

/-- **The node output.** -/
def outIR (mB : ℕ) : XIR :=
  .seq (emitIR (toWord 1)) (.seq (tcpIR 11 4) (.seq (leafStmtIR 20 19)
  (.seq (emitIR (toWord (piSize pX))) (.seq (copyIR mB)
  (.seq (setR sgB) (.seq (segIR apC 0 pSegL) (.seq (segIR apC 0 trSegL)
  (.seq (setR (sigB mB)) (.seq (segIR apC 0 (.cp 0 597))
  (.seq (emitIR (toWord 48)) (.seq (emitIR (toWord 0)) (.seq (tcpIR 15 5)
  (.seq (emitIR (toWord 0)) (tcpIR 24 597))))))))))))))

/-! ## Steps -/

theorem setR_sem (I : Array Word) (t : St) (hM : Inv t.M) (R : ℕ) :
    Inv (semXIR I (setR R) t).M ∧ (semXIR I (setR R) t).M.size = t.M.size ∧
    (∀ y, regs ≤ y → rd (semXIR I (setR R) t).M y = rd t.M y) ∧
    rd (semXIR I (setR R) t).M oR = toWord R ∧ rd (semXIR I (setR R) t).M oKF = 0 ∧
    rd (semXIR I (setR R) t).M (oBd 0) = toWord 0 ∧ (semXIR I (setR R) t).o = t.o := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨inv_sem I (by simp +decide [setR, WF, Prim.dst, oR, oKF, oBd]) hM, size_sem .., fun y hy => ?_,
    ?_, ?_, ?_, rfl⟩
  · exact rd_blk_of_not_dst I _ t (by simp only [regs] at hy; simp [Prim.dst, oR, oKF, oBd]; (clear * - hy; omega))
  · rw [setR, semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_ne (by decide), rd_set_self (by simp only [oR]; (clear * - hs; omega))]
  · rw [setR, semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [size_set, oKF]; (clear * - hs; omega))]
  · rw [setR, semXIR_blk_M]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, oBd]; (clear * - hs; omega))]; rfl

/-- A segment from a state in context with base 0: its words, the context and the base kept. -/
theorem seg_step (I : Array Word) {M₀ : Mem} {R : ℕ} (hA : ∀ x, regs ≤ (addrW apC (toWord R) x).toNat)
    (seg : Seg) (hok : okSeg seg = true) (hd : depthSeg seg ≤ 2) (t : St) (hc : Ctx M₀ R false t)
    (hb : rd t.M (oBd 0) = toWord 0) :
    (semXIR I (segIR apC 0 seg) t).o.toList = t.o.toList ++ segOut (src M₀ apC R) false 0 seg ∧
    Ctx M₀ R false (semXIR I (segIR apC 0 seg) t) ∧ rd (semXIR I (segIR apC 0 seg) t).M (oBd 0) = toWord 0 :=
  ⟨segIR_sem I apC hA seg 0 0 t hok (by (clear * - hd; omega)) hc hb, ctx_segIR I apC seg 0 (by (clear * - hd; omega)) hc,
    (frame I _ t (wf_segIR apC seg 0 (by (clear * - hd; omega))) hc.inv _ (by simp [oBd, regs])
      (noW_segIR apC seg 0 _ (.inr (.inr (.inr rfl))))).trans hb⟩

end Lvm.X
end
-- ===== end of `LvmXNodeIR` =====

/-!
# The extractor program and `Computes` (BLUEPRINT §6.2, §6.3)

`extX = extWith piSize decX` (`LvmXComputes`: `'S'` and `|π| = piSize` → `decX`, `'S'` and another size
→ nothing, else the `W` copy). The SNARK branch `decX` reads the flag `b` (π word 1):

* `b = 0`: `leafIR` outputs `witWords (leaf s n)` (π words 10–14);
* `b ≠ 0`: `nodeIR`: the log index (`idxIR4`, WP-3), the chain scan (`chainL`, through `α₁`), the
  column reads of `C_rec`'s level 0 (`readIR`, WP-13b), `α₀` copied, the column reads of level 1
  (`read1IR`, lvm2 X-REC2 DEC), `α₁` and `f₂` copied, the level-1 decoder (`dec1IR`) writing `f₁`
  where v1's decoder reads it, and if it succeeded (`ok1B`) the level-0 decoder (`decIR`, WP-13b)
  and, if that succeeded too (`okB`), the node output (`outIR`).

Heap layout (all below `memX = 2^25`): level 0's decoder (`decLay_example`: `aB = 2^19`,
`fB = aB + 64`, `wB = 2^20`, `dB = 2^22`, message at `dB + 2^20`); level 1's (`dec1Lay_example`:
`a1B = 2^19 + 24`, word `w1B = 2^23`, workspace `d1B = 2^23 + 2^21`, `f2B = 2^23 + 2^22`, output
`fB`); the chain's at `2^24`, the stream buffer at `2^24 + 2^16`; the log index at `memX`.

**`decOk_decX`**, **`computesX`**: `Computes extX (EX A) fuel` with the declared fuel
`fuel t = 2^46 + 2^13 t` (`LvmXComputes.fuel`); `extX_caps`: within the budget and `progCap`.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## Layout -/

/-- The log's tape word on an `S` proof. -/
def pLX : ℕ := posL (piSize pX)
/-- The decoder's workspace. -/
def dBX : ℕ := 2 ^ 22
/-- The read word. -/
def wBX : ℕ := 2 ^ 20
/-- `α`. -/
def aBX : ℕ := 2 ^ 19
/-- `f₁`. -/
def fBX : ℕ := 2 ^ 19 + 64
/-- The tape word of `C_rec`'s cap. -/
def capWX : ℕ := 5 + capRecOff pX / 8
/-- The tape word of `C_rec`'s level-1 cap. -/
def cap1WX : ℕ := 5 + capRec1Off pX / 8
/-- The tape word of `f₂`. -/
def f2WX : ℕ := 5 + f2Off pX / 8
/-- Level 1's read word. -/
def w1BX : ℕ := 2 ^ 23
/-- Level 1's decoder workspace. -/
def d1BX : ℕ := 2 ^ 23 + 2 ^ 21
/-- `α₁`. -/
def a1BX : ℕ := 2 ^ 19 + 24
/-- `f₂`. -/
def f2BX : ℕ := 2 ^ 23 + 2 ^ 22

/-! ## The SNARK branch -/

/-- The flag register. -/
def rBb : ℕ := 130

/-- **The leaf output**: tag `0`, the chain start (π words 10–13), the length (π word 14). -/
def leafIR : XIR := .seq (emitIR (toWord 0)) (tcpIR 15 5)

/-- `α_j` (answer words 0–2 of chain position `alphaPos j`) to `aB + 3j`. -/
def acpIR : XIR :=
  .seq (mcpIR 3 (ansB + 4 * alphaPos pX 0) 1 aBX) (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 1) 1 (aBX + 3))
  (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 2) 1 (aBX + 6)) (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 3) 1 (aBX + 9))
  (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 4) 1 (aBX + 12)) (mcpIR 3 (ansB + 4 * alphaPos pX 5) 1 (aBX + 15))))))

/-- Three words of each of `n` chain answers (answer `j` at `src + 4j`) to `dst + 3j`. -/
def acp3IR (src dst : ℕ) : ℕ → XIR
  | 0 => .blk []
  | n + 1 => .seq (acp3IR src dst n) (mcpIR 3 (src + 4 * n) 1 (dst + 3 * n))

/-- `α₁_j` (answer words 0–2 of chain position `alpha1Pos j`) to `a1B + 3j`, `j < 4`. -/
def a1cpIR : XIR := acp3IR (ansB + 4 * alpha1Pos pX 0) a1BX 4

/-- After the decoder: the node output if it succeeded. -/
def okXIR : XIR :=
  .seq (.blk [.const eA (toWord (okB dBX))]) (.seq (.load eW eA) (.ite eW (outIR (mB dBX)) (.blk [])))

/-- After the level-1 decoder: if it succeeded, the level-0 decoder and `okXIR`. -/
def ok1XIR : XIR :=
  .seq (.blk [.const eA (toWord (ok1B d1BX))]) (.seq (.load eW eA)
    (.ite eW (.seq (decIR dBX wBX aBX fBX) okXIR) (.blk [])))

/-- **The node branch.** -/
def nodeIR : XIR :=
  .seq (idxIR4 memX pLX) (.seq chainL (.seq (readIR memX pLX capWX wBX) (.seq acpIR
    (.seq (read1IR memX pLX cap1WX w1BX) (.seq a1cpIR (.seq (thcpIR f2WX f2BX (3 * 2 ^ 9))
      (.seq (dec1IR d1BX w1BX a1BX f2BX fBX) ok1XIR)))))))

/-- **The SNARK branch**: by the flag `b` (tape word 6). -/
def decX : XIR := .seq (readAt rBb 6) (.ite rBb nodeIR leafIR)

/-- **The extractor program.** -/
def extX : XProg := extWith (piSize pX) decX

/-! ## Well formed, no `loopT` but the index's and the chain's, output, size, cost -/

theorem wf_leafIR : WF leafIR := ⟨wf_emitIR _, wf_tcpIR _ _⟩

theorem wf_acpIR : WF acpIR := by
  simp only [acpIR, WF]; exact ⟨wf_mcpIR .., wf_mcpIR .., wf_mcpIR .., wf_mcpIR .., wf_mcpIR .., wf_mcpIR ..⟩

theorem wf_outIR (m : ℕ) : WF (outIR m) := by
  simp only [outIR, WF]
  refine ⟨wf_emitIR _, wf_tcpIR _ _, wf_leafStmtIR _ _, wf_emitIR _, wf_copyIR _, ?_, wf_segIR _ _ _ (by
    have := segs_ok.2.2.2; omega), wf_segIR _ _ _ (by have := segs_ok.2.1; omega), ?_,
    wf_segIR _ _ _ (by decide), wf_emitIR _, wf_emitIR _, wf_tcpIR _ _, wf_emitIR _, wf_tcpIR _ _⟩ <;>
  simp +decide [setR, WF, Prim.dst, oR, oKF, oBd]

theorem wf_okXIR : WF okXIR := by
  refine ⟨by simp +decide [WF, Prim.dst, eA], show 4 ≤ eW by decide, wf_outIR _, by simp [WF]⟩

theorem wf_acp3IR (src dst : ℕ) : ∀ n, WF (acp3IR src dst n)
  | 0 => by simp [acp3IR, WF]
  | n + 1 => ⟨wf_acp3IR src dst n, wf_mcpIR ..⟩

theorem wf_ok1XIR : WF ok1XIR := by
  refine ⟨by simp +decide [WF, Prim.dst, eA], show 4 ≤ eW by decide, ⟨wf_decIR _ _ _ _, wf_okXIR⟩,
    by simp [WF]⟩

theorem wf_nodeIR : WF nodeIR :=
  ⟨wf_idxIR4 _ _, wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)),
    wf_readIR _ _ _ _, wf_acpIR, wf_read1IR _ _ _ _, wf_acp3IR _ _ _, wf_thcpIR _ _ _,
    wf_dec1IR _ _ _ _ _, wf_ok1XIR⟩

theorem wf_decX : WF decX := by
  refine ⟨?_, wf_nodeIR, wf_leafIR⟩
  simp +decide [readAt, WF, Prim.dst, rA, rBb]

theorem noLoopT_tcpIR (a n : ℕ) : NoLoopT (tcpIR a n) := by simp [tcpIR, tcpBody, NoLoopT]
theorem noLoopT_emitIR (w : Word) : NoLoopT (emitIR w) := by simp [emitIR, NoLoopT]
theorem noLoopT_copyIR (m : ℕ) : NoLoopT (copyIR m) := by simp [copyIR, copyBody, NoLoopT]
theorem noLoopT_thcpIR (a d n : ℕ) : NoLoopT (thcpIR a d n) := by simp [thcpIR, thcpBody, NoLoopT]
theorem noLoopT_setR (R : ℕ) : NoLoopT (setR R) := trivial

theorem noLoopT_outIR (m : ℕ) : NoLoopT (outIR m) :=
  ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_leafStmtIR _ _, noLoopT_emitIR _, noLoopT_copyIR _,
    noLoopT_setR _, noLoopT_segIR _ _ _, noLoopT_segIR _ _ _, noLoopT_setR _, noLoopT_segIR _ _ _,
    noLoopT_emitIR _, noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_emitIR _, noLoopT_tcpIR _ _⟩

theorem noLoopT_acpIR : NoLoopT acpIR :=
  ⟨noLoopT_mcpIR .., noLoopT_mcpIR .., noLoopT_mcpIR .., noLoopT_mcpIR .., noLoopT_mcpIR ..,
    noLoopT_mcpIR ..⟩

theorem noLoopT_okXIR : NoLoopT okXIR := ⟨trivial, trivial, noLoopT_outIR _, trivial⟩

theorem noLoopT_acp3IR (src dst : ℕ) : ∀ n, NoLoopT (acp3IR src dst n)
  | 0 => trivial
  | n + 1 => ⟨noLoopT_acp3IR src dst n, noLoopT_mcpIR ..⟩

theorem noLoopT_ok1XIR : NoLoopT ok1XIR :=
  ⟨trivial, trivial, ⟨noLoopT_decIR .., noLoopT_okXIR⟩, trivial⟩

theorem noLoopT_sdL : NoLoopT sdL := ⟨trivial, trivial⟩

/-- **The SNARK branch's loop bounds** on every domain tape of an `S` proof. -/
theorem safe_decX (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length decX := by
  have hpz : piSize pX < 2 ^ 64 := by rw [piSize_eq]; norm_num
  refine .seq (safe_of_noLoopT (by simp [readAt, NoLoopT])) (.ite ?_ (safe_of_noLoopT
    ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _⟩))
  refine .seq ((decOk_idx hpz).safe c π L hs hq ht) (.seq ?_ (.seq (safe_of_noLoopT (noLoopT_readIR ..))
    (.seq (safe_of_noLoopT noLoopT_acpIR) (.seq (safe_of_noLoopT (noLoopT_read1IR ..))
      (.seq (safe_of_noLoopT (noLoopT_acp3IR ..)) (.seq (safe_of_noLoopT (noLoopT_thcpIR ..))
        (.seq (safe_of_noLoopT (noLoopT_dec1IR ..)) (safe_of_noLoopT noLoopT_ok1XIR))))))))
  exact safe_chainIR c π L (hs_posL hs) hq ht _ _ noLoopT_sdL wf_sdL
    (nw_sdL _ (by decide) (by decide) (by decide))

/-! ## Cost -/

theorem cost_tcpIR (a n t : ℕ) (hn : n < 2 ^ 64) : cost (tcpIR a n) t = 12 + n * 8 := by
  simp only [tcpIR, tcpBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

theorem cost_copyIR (m t : ℕ) : cost (copyIR m) t = 12 + nCp * 31 := by
  simp only [copyIR, copyBody, cpAddrPs, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show nCp < 2 ^ 64 by simp only [nCp]; norm_num)]
  norm_num
  omega

/-! The output segments' costs, outputs and sizes, block by block: a block's segment's measures do
not depend on its lane (`segPC_u`, …) and are `LvmXLayout`'s closed forms (`segPC`, …) whose sums
over the blocks `layout_all_P20` decides with the other numbers at `P20` (three decisions on the
segments cost 2–3 s of kernel time each). -/

private theorem segPC (b : Blk) : segCost (blkPSeg 0 b) + 1 = blkPCostL b := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPO (b : Blk) : segOuts (blkPSeg 0 b) = blkPOutsL b := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPS (b : Blk) : segSize (blkPSeg 0 b) + 1 = blkPSizeL b := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segTC (b : Blk) : segCost (blkTSeg 0 b) + 1 = blkTCostL b := by
  cases b with
  | one c len => rfl
  | opn t row path => rfl
private theorem segTO (b : Blk) : segOuts (blkTSeg 0 b) = blkTOutsL b := by
  cases b with
  | one c len => rfl
  | opn t row path => rfl
private theorem segTS (b : Blk) : segSize (blkTSeg 0 b) + 1 = blkTSizeL b := by
  cases b with
  | one c len => rfl
  | opn t row path => rfl

private theorem segPC_u (u : ℕ) (b : Blk) : segCost (blkPSeg u b) = segCost (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPO_u (u : ℕ) (b : Blk) : segOuts (blkPSeg u b) = segOuts (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPS_u (u : ℕ) (b : Blk) : segSize (blkPSeg u b) = segSize (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segTC_u (u : ℕ) (b : Blk) : segCost (blkTSeg u b) = segCost (blkTSeg 0 b) := by
  cases b <;> rfl
private theorem segTO_u (u : ℕ) (b : Blk) : segOuts (blkTSeg u b) = segOuts (blkTSeg 0 b) := by
  cases b <;> rfl
private theorem segTS_u (u : ℕ) (b : Blk) : segSize (blkTSeg u b) = segSize (blkTSeg 0 b) := by
  cases b <;> rfl

private theorem segPCs : ∀ (u : ℕ) (bs : List Blk), segCost (blkPSegs u bs) = (bs.map blkPCostL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkPSegs, segCost, segPCs _ bs, segPC_u, List.map_cons, List.sum_cons, ← segPC b]; omega
private theorem segPOs : ∀ (u : ℕ) (bs : List Blk), segOuts (blkPSegs u bs) = (bs.map blkPOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkPSegs, segOuts, segPOs _ bs, segPO_u, List.map_cons, List.sum_cons, ← segPO b]
private theorem segPSs : ∀ (u : ℕ) (bs : List Blk), segSize (blkPSegs u bs) = (bs.map blkPSizeL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkPSegs, segSize, segPSs _ bs, segPS_u, List.map_cons, List.sum_cons, ← segPS b]; omega
private theorem segTCs : ∀ (u : ℕ) (bs : List Blk), segCost (blkTSegs u bs) = (bs.map blkTCostL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkTSegs, segCost, segTCs _ bs, segTC_u, List.map_cons, List.sum_cons, ← segTC b]; omega
private theorem segTOs : ∀ (u : ℕ) (bs : List Blk), segOuts (blkTSegs u bs) = (bs.map blkTOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkTSegs, segOuts, segTOs _ bs, segTO_u, List.map_cons, List.sum_cons, ← segTO b]
private theorem segTSs : ∀ (u : ℕ) (bs : List Blk), segSize (blkTSegs u bs) = (bs.map blkTSizeL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkTSegs, segSize, segTSs _ bs, segTS_u, List.map_cons, List.sum_cons, ← segTS b]; omega

private theorem segAll : (segCost pSegL = 2262010 ∧ segCost trSegL = 2673767 ∧
      segCost (.cp 0 597) = 21506) ∧
    (segOuts pSegL = 41542 ∧ segOuts trSegL = 75594 ∧ segOuts (.cp 0 597) = 597) ∧
    (segSize pSegL = 69710 ∧ segSize trSegL = 74134 ∧ segSize (.cp 0 597) = 50) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := layout_all_P20.2.2.2.2.2.2.2
  refine ⟨⟨?_, ?_, rfl⟩, ⟨?_, ?_, rfl⟩, ⟨?_, ?_, rfl⟩⟩
  · rw [pSegL, segCost, segCost, segPCs, h1]
  · rw [trSegL, segCost, segCost, segCost, segCost, segCost, segCost, segCost, segTCs, h2]; rfl
  · rw [pSegL, segOuts, segOuts, segPOs, h3]
  · rw [trSegL, segOuts, segOuts, segOuts, segOuts, segOuts, segOuts, segOuts, segTOs, h4]; rfl
  · rw [pSegL, segSize, segSize, segPSs, h5]
  · rw [trSegL, segSize, segSize, segSize, segSize, segSize, segSize, segSize, segTSs, h6]; rfl

theorem segCosts : segCost pSegL = 2262010 ∧ segCost trSegL = 2673767 ∧ segCost (.cp 0 597) = 21506 :=
  segAll.1

/-- **The node output's cost.** -/
theorem cost_outIR (m t : ℕ) : cost (outIR m) t ≤ 15800000 := by
  have h1 := cost_segIR apC pSegL 0 t
  have h2 := cost_segIR apC trSegL 0 t
  have h3 := cost_segIR apC (.cp 0 597) 0 t
  rw [segCosts.1] at h1; rw [segCosts.2.1] at h2; rw [segCosts.2.2] at h3
  simp only [outIR, cost, emitIR, setR, blkSteps, List.length_cons, List.length_nil,
    cost_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num), cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    cost_tcpIR _ _ t (show 597 < 2 ^ 64 by norm_num), cost_leafStmtIR, cost_copyIR, nCp]
  norm_num
  omega

theorem cost_acpIR (t : ℕ) : cost acpIR t = 335 := by
  simp only [acpIR, cost, cost_mcpIR _ _ _ _ t (show 3 < 2 ^ 64 by norm_num)]

theorem cost_sdL (t : ℕ) : cost sdL t = 8 := by
  simp only [sdL, cost, blkSteps, List.length_cons, List.length_nil]; norm_num

theorem chTabL_len : chTabL.length = 4992 := by rw [chTabL_length, nChain_eq]

theorem cost_acp3IR (src dst t : ℕ) : ∀ n, cost (acp3IR src dst n) t = 1 + 56 * n
  | 0 => rfl
  | n + 1 => by
    rw [acp3IR, cost, cost_acp3IR src dst t n, cost_mcpIR _ _ _ _ t (by norm_num)]; ring

/-- The level-1 phase: reads, `α₁`, `f₂`, decoder. -/
theorem cost_lvl1 (t : ℕ) :
    cost (read1IR memX pLX cap1WX w1BX) t + cost a1cpIR t + cost (thcpIR f2WX f2BX 1536) t +
      cost (dec1IR d1BX w1BX a1BX f2BX fBX) t ≤ 2 ^ 32 + 20300 := by
  have h1 := dec1_fixed_le memX pLX cap1WX w1BX d1BX a1BX f2BX fBX t
  rw [a1cpIR, cost_acp3IR, cost_thcpIR _ _ _ t (by norm_num)]
  omega

/-- The flag test of level 1, v1's decoder and the output. -/
theorem cost_ok1XIR (t : ℕ) : cost ok1XIR t ≤ 265710864928 + 21100000 + 200 := by
  have hO := cost_outIR (mB dBX) t
  simp only [ok1XIR, okXIR, cost, blkSteps, List.length_cons, List.length_nil, cost_decIR,
    Nat.max_def]
  split_ifs <;> omega

/-- **The SNARK branch's cost**: the fixed `≈ 2^37.95` (level-0 decoder) plus `< 2^32` (level 1)
plus `≈ 2,547` steps a word. -/
theorem cost_decX (t : ℕ) : cost decX t ≤ 2 ^ 39 + t / 5 * 11895 + t * 168 := by
  have hC := cost_chainIR (posL (piSize pX)) (nChain pX) t chTabL sdL
  rw [chTabL_len, cost_sdL] at hC
  have hR := (cost_readIR memX pLX capWX wBX t).2
  have h1 := cost_lvl1 t
  have h2 := cost_ok1XIR t
  simp only [decX, nodeIR, leafIR, readAt, cost, blkSteps, List.length_cons,
    List.length_nil, cost_idxIR4, show chainL = chainIR (posL (piSize pX)) (nChain pX) chTabL sdL
      from rfl, hC, hR, cost_acpIR, cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), emitIR,
    show 3 * 2 ^ 9 = 1536 from rfl, Nat.max_def]
  split_ifs <;> omega

/-! ## Output, size -/

theorem outs_tcpIR (a n t : ℕ) (hn : n < 2 ^ 64) : outs (tcpIR a n) t = n := by
  simp [tcpIR, tcpBody, outs, toNat_toWord hn]

theorem segOutsV : segOuts pSegL = 41542 ∧ segOuts trSegL = 75594 ∧ segOuts (.cp 0 597) = 597 :=
  segAll.2.1

theorem outs_outIR (m t : ℕ) : outs (outIR m) t ≤ 164753 := by
  have h1 := outs_segIR apC pSegL 0 t
  have h2 := outs_segIR apC trSegL 0 t
  have h3 := outs_segIR apC (.cp 0 597) 0 t
  rw [segOutsV.1] at h1; rw [segOutsV.2.1] at h2; rw [segOutsV.2.2] at h3
  simp only [outIR, outs, emitIR, setR, outs_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num),
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), outs_tcpIR _ _ t (show 597 < 2 ^ 64 by norm_num),
    outs_leafStmtIR, copyIR, copyBody, Nat.zero_add, Nat.add_zero]
  simp [outs] at *
  omega

theorem outs_acp3IR (src dst t : ℕ) : ∀ n, outs (acp3IR src dst n) t = 0
  | 0 => rfl
  | n + 1 => by rw [acp3IR, outs, outs_acp3IR src dst t n, outs_mcpIR]

theorem outs_decX (t : ℕ) : outs decX t ≤ outCap := by
  have h := outs_outIR (mB dBX) t
  simp only [decX, nodeIR, ok1XIR, okXIR, leafIR, readAt, outs, outs_idxIR4, outs_readIR, outs_decIR,
    emitIR, outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), show chainL = chainIR (posL (piSize pX))
      (nChain pX) chTabL sdL from rfl, outs_chainIR (posL (piSize pX)) (nChain pX) t chTabL
      (show outs sdL t = 0 by simp [sdL, outs])]
  simp [acpIR, outs_mcpIR, thcpIR, thcpBody, outs, outCap, outs_read1IR, outs_dec1IR,
    outs_acp3IR, a1cpIR] at *
  omega

theorem segSizes : segSize pSegL = 69710 ∧ segSize trSegL = 74134 ∧ segSize (.cp 0 597) = 50 :=
  segAll.2.2

theorem sizeIR_idxX : sizeIR (idxIR4 memX pLX) = 294 := by decide +kernel

/-! `sizeIR`'s equations as propositional rewrites (not `rfl` lemmas): `simp` rewrites with them by
`congrArg` instead of casting the goal, a cast that made the kernel evaluate `sizeIR decX` (the
chain table included) on both sides (8 s). -/
private theorem szBlk (ps : List Prim) : sizeIR (.blk ps) = blkSteps ps.length := by rw [sizeIR]
private theorem szLoad (d a : ℕ) : sizeIR (.load d a) = 1 := by rw [sizeIR]
private theorem szStore (a s : ℕ) : sizeIR (.store a s) = 5 := by rw [sizeIR]
private theorem szInput (d a : ℕ) : sizeIR (.input d a) = 1 := by rw [sizeIR]
private theorem szOut (s : ℕ) : sizeIR (.out s) = 1 := by rw [sizeIR]
private theorem szSeq (p q : XIR) : sizeIR (.seq p q) = sizeIR p + sizeIR q + 1 := by rw [sizeIR]
private theorem szIte (c : ℕ) (p q : XIR) : sizeIR (.ite c p q) = sizeIR p + sizeIR q + 1 := by
  rw [sizeIR]

theorem sizeIR_acp3IR (src dst : ℕ) : ∀ n, sizeIR (acp3IR src dst n) = 1 + 31 * n
  | 0 => rfl
  | n + 1 => by
    rw [acp3IR, szSeq, sizeIR_acp3IR src dst n]
    simp only [mcpIR, mcpLoop, mcpBody, szSeq, sizeIR, blkSteps, List.length_cons, List.length_nil]
    simp
    omega

theorem sizeIR_read1X : sizeIR (read1IR memX pLX cap1WX w1BX) ≤ 2 ^ 12 := by decide +kernel

theorem sizeIR_dec1X : sizeIR (dec1IR d1BX w1BX a1BX f2BX fBX) ≤ 2 ^ 14 := by decide +kernel

theorem sizeIR_decX : sizeIR decX ≤ 2 ^ 19 := by
  have h1 := sizeIR_read1X
  have h2 := sizeIR_dec1X
  have h3 := sizeIR_acp3IR (ansB + 4 * alpha1Pos pX 0) a1BX 4
  simp only [decX, nodeIR, okXIR, ok1XIR, leafIR, outIR, readAt, emitIR, setR, acpIR, a1cpIR, szBlk,
    szLoad, szStore, szInput, szOut, szSeq, szIte, blkSteps,
    List.length_cons, List.length_nil, sizeIR_idxX, show chainL = chainIR (posL (piSize pX))
      (nChain pX) chTabL sdL from rfl, sizeIR_chainIR, chTabL_len, sizeIR_readIR, sizeIR_decIR,
    sizeIR_leafStmtIR, sizeIR_segIR, segSizes.1, segSizes.2.1, segSizes.2.2]
  simp [tcpIR, tcpBody, copyIR, copyBody, cpAddrPs, thcpIR, thcpBody, mcpIR, mcpLoop, mcpBody, sdL,
    sizeIR, blkSteps]
  omega

/-! ## `DecOk` and `Computes` -/

/-- **The SNARK branch meets `DecOk`** (`LvmXComputes`). -/
theorem decOk_decX : DecOk (piSize pX) decX where
  pz_lt := by rw [piSize_eq]; norm_num
  wf := wf_decX
  safe := fun c π L hs hq ht => safe_decX c π L hs hq ht
  cost := fun t => by
    have := cost_decX t
    simp only [decBudget, fuelBase, fuelPerWord]
    omega
  outs := outs_decX
  size := sizeIR_decX

/-! ## The extractor specification and `Computes` -/

/-- **The contract's `Computes` domain** (FR `InDomE`). -/
def InDomE (c : Digest) (π : Proof) (L : Log) : Prop :=
  π.size ≤ 8 * outCap ∧ (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64

instance (c : Digest) (π : Proof) (L : Log) : Decidable (InDomE c π L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The in-domain extractor**: the program's decoded denotation (a total computable function). -/
def EdX : Digest → Proof → Log → Option Wit := Eden memX mpwX (extIRWith (piSize pX) decX)

/-- The leaf witness an `S` proof with `b = 0` carries: `(s, n)` from its header. -/
def leafW (π : Proof) : Wit := .leaf (hdD π 10) (pw π 14).toNat

/-- **The extractor outside the domain** (FR B-15): a `W` proof decoded, an `S` leaf's witness, an
`S` node searched under the key it carries (`vk`, π words 2–5), any other `S` nothing. -/
def EoutX (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) : Option Wit :=
  if π.data[0]? = some 0x53 then
    (if π.size = piSize pX then (if pw π 1 = 0 then some (leafW π) else search A (hdD π 2) c) else none)
  else WitnessSending.decode π

/-- **The extractor specification** `E`: `EdX` on the domain, `EoutX A` outside (`A`: the
certificate's `S.acc`). -/
def EX (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then EdX c π L else EoutX A c π L

/-- **`Computes extX (EX A) fuel`** with the declared fuel `2^46 + 2^13 t`, for every `A`. -/
theorem computesX (A : Digest → Digest → Signed → Bool) : Computes extX (EX A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computesWith decOk_decX c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem extX_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ extX.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWith decOk_decX.size⟩

end Lvm.X
