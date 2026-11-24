-- lvm6 X2 (BLUEPRINT v3 §2.1, §3 step 3; FORMAT6 v2 §T `STREAM` map, §8): the node witness's two children read
-- off the decoded `STREAM` window. The right child (the witness-sending leaf `⟨encode (leaf xs), [], σ_leaf⟩`)
-- and both signatures are output here, with exact cost; the left child's trace and proof are specified (season 1's
-- stream reading and length-classifier reassembly, made generic in the schedule's lengths) for the next part.
import Lvm6XLeaf

/-!
# The children of the node witness

`STREAM` (slots 33–34) decoded is a table of `2^20` words, word `w = r + 2^19 (slot − 33)`; the extractor holds
it as `W : ℕ → Word` (FORMAT6 v2 §T). Three base offsets are `Shape` constants (CD): the trace stream `tB`, the
child's signature `sB` and the leaf signature `sLB` (`σ'` and `σ_leaf` adjacent: `sLB = sB + 597`).

* **`sigOf W b`**: the signature in `readSig`'s order at `b` (index, 133 chain values, 16 path digests, 4 words
  each); **`sigWords_sigOf`**: its output words are the 597 words verbatim, so any 597 words denote a signature.
* **`outCpIR src n`**: output `n` consecutive heap words; `outCpIR_sem`, `cost_outCpIR` (`12 + 8n`).
* **`rightOf n q σ`** `= ⟨encode (.leaf (xs6 n q)), [], σ⟩`, the right child of BLUEPRINT §2.1;
  **`signedWords_rightOf`**: `16 + 32n`, the leaf witness's words, `0` (the empty trace), the signature.
  **`rightOutIR`**, **`rightOutIR_sem`**, **`cost_rightOutIR`** (`4819 + 28 n`: `7,344,851` at `n = 2^18`).
* The left child (specification, program in the next part): **`readTrace6 lens W`** reads the trace off the
  stream lanes as season 1's `readTraceL` does, generic in the schedule's query lengths `lens` (the stream is the
  byte stream `traceDigest` hashes **with its tag byte `0x54`**, so `q₀` straddles lanes 1–2 and every later
  entry `|q|, q, a` is lane-aligned from lane 6); **`reassemble6 leafLs tr`** spells the proof: `HDR` from the
  seed (`a₀ ‖ HDR`, FORMAT6 v2.5: 32 bytes dropped), then per entry by its length: a node query (64 B) the half that is
  not the previous answer, a leaf query (a length in `leafLs`) its bytes, any other query its message after the
  32-byte state. **`leftOf6`**, **`nodeWit6`**: the node witness `node c' L ⟨π', tr', σ'⟩ (rightOf n q σ_leaf)`;
  **`witWords_nodeWit6`**: its words, in output order.
-/

namespace Lvm6.X

open RecursionFast Lvm.X

/-! ## Signatures in the window -/

/-- **The signature at word `b`** of the window, in `readSig`'s order. -/
def sigOf (W : ℕ → Word) (b : ℕ) : Sig :=
  ⟨(W b).toNat, (List.range wotsLen).map fun e => digW (wsAt W (b + 1 + 4 * e) 4),
    (List.range sigHeight).map fun e => digW (wsAt W (b + 1 + 4 * wotsLen + 4 * e) 4)⟩

theorem flatMap_wsAt4 (W : ℕ → Word) (u : ℕ) :
    ∀ k, (List.range k).flatMap (fun e => wsAt W (u + 4 * e) 4) = wsAt W u (4 * k)
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_wsAt4 W u k, List.flatMap_singleton,
      show 4 * (k + 1) = 4 * k + 4 by ring, wsAt_add]

/-- **A signature's words are the window's 597 words.** -/
theorem sigWords_sigOf (W : ℕ → Word) (b : ℕ) : sigWords (sigOf W b) = wsAt W b 597 := by
  have e1 : (List.range wotsLen).flatMap (fun e => packBytes (digW (wsAt W (b + 1 + 4 * e) 4)).toList) =
      wsAt W (b + 1) 532 := by
    rw [List.flatMap_congr (fun e _ => packBytes_digW (length_wsAt W _ 4)), flatMap_wsAt4 W (b + 1) wotsLen,
      show 4 * wotsLen = 532 from rfl]
  have e2 : (List.range sigHeight).flatMap
      (fun e => packBytes (digW (wsAt W (b + 1 + 4 * wotsLen + 4 * e) 4)).toList) = wsAt W (b + 533) 64 := by
    rw [List.flatMap_congr (fun e _ => packBytes_digW (length_wsAt W _ 4)),
      flatMap_wsAt4 W (b + 1 + 4 * wotsLen) sigHeight, show 4 * wotsLen = 532 from rfl,
      show 4 * sigHeight = 64 from rfl, show b + 1 + 532 = b + 533 by ring]
  simp only [sigWords, sigOf, List.flatMap_map, e1, e2, toWord_toNat]
  rw [show 597 = 1 + 532 + 64 from rfl, wsAt_add, wsAt_add, show b + 1 + 532 = b + 533 by ring,
    show wsAt W b 1 = [W b] by simp [wsAt]]
  simp

/-! ## The contiguous output copy -/

/-- The value. -/ def rCV : ℕ := 246
/-- The source pointer. -/ def rCP : ℕ := 247
/-- The count. -/ def rCN : ℕ := 248
/-- The loop counter. -/ def rCC : ℕ := 249

/-- One word: output `M[p]`, `p += 1`. -/
def cpBody : XIR := .seq (.load rCV rCP) (.seq (.out rCV) (.blk [.op .add rCP rCP cOne]))

/-- **Output `n` heap words** from `src`. -/
def outCpIR (src n : ℕ) : XIR :=
  .seq (.blk [.const rCP (toWord src), .const rCN (toWord n)]) (.loopK rCC rCN (toWord n) cpBody)

theorem wf_outCpIR (src n : ℕ) : WF (outCpIR src n) := by
  simp +decide [outCpIR, cpBody, WF, Writes, Prim.dst, rCV, rCP, rCN, rCC, regs, cTmp]

theorem noLoopT_outCpIR (src n : ℕ) : NoLoopT (outCpIR src n) := by
  simp [outCpIR, cpBody, NoLoopT]

theorem sizeIR_outCpIR (src n : ℕ) : sizeIR (outCpIR src n) = 20 := by
  simp [outCpIR, cpBody, sizeIR, blkSteps]

/-- **The exact cost**: `12 + 8n` steps. -/
theorem cost_outCpIR (src n t : ℕ) (hn : n < 2 ^ 64) : cost (outCpIR src n) t = 12 + 8 * n := by
  simp [outCpIR, cpBody, cost, blkSteps, toNat_toWord hn]
  ring

theorem outs_outCpIR (src n t : ℕ) (hn : n < 2 ^ 64) : outs (outCpIR src n) t = n := by
  simp [outCpIR, cpBody, outs, toNat_toWord hn]

section Sem

variable (I : Array Word)

/-- **The copy's run**: it appends the `n` heap words from `src` and writes registers only. -/
theorem outCpIR_sem (s : St) (hM : Inv s.M) {src n : ℕ} (hsrcr : regs ≤ src) (hsrc : src + n < 2 ^ 64) :
    (semXIR I (outCpIR src n) s).o.toList = s.o.toList ++ wsAt (rd s.M) src n ∧
    (∀ x, regs ≤ x → rd (semXIR I (outCpIR src n) s).M x = rd s.M x) ∧
    Inv (semXIR I (outCpIR src n) s).M := by
  have hs := hM.1
  simp only [regs] at hs hsrcr
  have hn : n < 2 ^ 64 := by omega
  set pre : XIR := .blk [.const rCP (toWord src), .const rCN (toWord n)] with hpre
  have e : semXIR I (outCpIR src n) s = semXIR I (.loopK rCC rCN (toWord n) cpBody) (semXIR I pre s) := by
    simp only [outCpIR, hpre, semXIR_seq]
  have wpre : WF pre := by simp +decide [hpre, WF, Prim.dst, rCP, rCN]
  have hM0 := inv_sem I wpre hM
  have r0 : rd (semXIR I pre s).M rCP = toWord src ∧ rd (semXIR I pre s).M rCN = toWord n ∧
      (semXIR I pre s).o = s.o ∧ ∀ x, regs ≤ x → rd (semXIR I pre s).M x = rd s.M x := by
    simp only [hpre, semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, trivial, fun x hx => ?_⟩
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rCP, rCN]; omega))
        only [rd_set_self, rd_set_ne]
    · simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rCP, rCN]; omega))
        only [rd_set_self, rd_set_ne]
    · simp only [regs] at hx
      simp (disch := first | decide | (simp only [rCP, rCN]; omega)) only [rd_set_ne]
  obtain ⟨p0, n0, o0, k0⟩ := r0
  rw [e]
  generalize semXIR I pre s = s0 at hM0 p0 n0 o0 k0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ rd s'.M rCP = toWord (src + j) ∧
    (∀ x, regs ≤ x → rd s'.M x = rd s.M x) ∧ s'.o.toList = s.o.toList ++ wsAt (rd s.M) src j
  have hE : ∀ i, i ≠ rCC → i ≠ cTmp → rd (entryK rCC rCN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK rCC rCN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, fun x hx => ?_, ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0, Nat.add_zero]
    · simp only [regs] at hx
      rw [hE _ (by simp only [rCC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
    · rw [o0]; simp [wsAt]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS rCC (semXIR I cpBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4⟩
    have hs' := i1.1
    have h1 : rd s'.M cOne = 1 := i1.2 0 (by decide)
    simp only [regs] at hs'
    have wb : WF cpBody := by simp +decide [cpBody, WF, Prim.dst, rCV, rCP]
    have hd : ∀ y, y ≠ rCC → rd (decS rCC (semXIR I cpBody s')).M y = rd (semXIR I cpBody s').M y :=
      fun y hy => rd_decS (Ne.symm hy) _
    refine ⟨inv_decS (inv_sem I wb i1) (by decide), ?_, fun x hx => ?_, ?_⟩
    · rw [hd _ (by decide)]
      simp only [cpBody, semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rCV, rCP]; omega))
        only [rd_set_self, rd_set_ne, i2, h1, XOp.eval]
      rw [toWord_add_one, Nat.add_assoc]
    · rw [hd _ (by simp only [regs, rCC] at *; omega)]
      simp only [regs] at hx
      simp only [cpBody, semXIR, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [rCV, rCP]; omega)) only [rd_set_ne]
      exact i3 x (by simp only [regs]; omega)
    · rw [show (decS rCC (semXIR I cpBody s')).o = (semXIR I cpBody s').o from rfl]
      simp only [cpBody, semXIR, runPrims, List.foldl, Prim.run, Array.toList_push]
      simp (disch := first | decide | (simp only [Array.size_setIfInBounds, rCV, rCP]; omega))
        only [rd_set_self, rd_set_ne, i2, toNat_toWord (show src + j < 2 ^ 64 by omega)]
      rw [i4, i3 _ (by simp only [regs]; omega), wsAt_add, List.append_assoc]
      simp [wsAt]
  have hfin := loopK_run I cpBody P s0 hM0 (c := rCC) (n := rCN) (K := n)
    (by decide) (by decide) (by decide) n0 hn h0 hstep
  obtain ⟨f1, -, f3, f4⟩ := hfin
  exact ⟨f4, f3, f1⟩

end Sem

/-! ## The right child -/

/-- **The right child** of the node witness (BLUEPRINT §2.1): the witness-sending leaf proof of the extracted data,
the empty trace, the leaf signature. -/
def rightOf (n : ℕ) (q : Cols) (σ : Sig) : Signed := ⟨WitnessSending.encode (.leaf (xs6 n q)), [], σ⟩

theorem length_leafWords (n : ℕ) (q : Cols) : (leafWords n q).length = 2 + 4 * n := by
  simp only [leafWords, List.length_cons, List.length_flatMap, List.length_range, blkW, List.length_nil,
    List.map_const', List.sum_replicate, smul_eq_mul]
  ring

/-- **The right child's words**: the proof's length `16 + 32n` and its words (the leaf witness's), the empty
trace, the signature. -/
theorem signedWords_rightOf (n : ℕ) (q : Cols) (σ : Sig) :
    signedWords (rightOf n q σ) = toWord (16 + 32 * n) :: leafWords n q ++ [toWord 0] ++ sigWords σ := by
  simp only [signedWords, rightOf, bytesWords, WitnessSending.encode_data, packBytes_wordsBytes, witWords_xs6,
    wordsBytes_length, length_leafWords, logWords, List.length_nil, List.flatMap_nil, List.cons_append,
    List.append_assoc, List.singleton_append]
  rw [show 8 * (2 + 4 * n) = 16 + 32 * n by ring]

/-- **The right child's output**: `16 + 32n`, the leaf witness from the columns at `colB` (stride `S`), `0`, then
the 597 window words of `σ_leaf` from `sLB`. -/
def rightOutIR (n colB S sLB : ℕ) : XIR :=
  .seq (.blk [.const rLV (toWord (16 + 32 * n))]) (.seq (.out rLV) (.seq (leafOutIR n colB S)
    (.seq (.blk [.const rLV 0]) (.seq (.out rLV) (outCpIR sLB 597)))))

theorem wf_rightOutIR (n colB S sLB : ℕ) : WF (rightOutIR n colB S sLB) :=
  ⟨by simp +decide [WF, Prim.dst, rLV], trivial, wf_leafOutIR n colB S, by simp +decide [WF, Prim.dst, rLV],
    trivial, wf_outCpIR sLB 597⟩

theorem noLoopT_rightOutIR (n colB S sLB : ℕ) : NoLoopT (rightOutIR n colB S sLB) :=
  ⟨trivial, trivial, noLoopT_leafOutIR n colB S, trivial, trivial, noLoopT_outCpIR sLB 597⟩

/-- **The exact cost**: `4819 + 28 n` steps. -/
theorem cost_rightOutIR (n colB S sLB t : ℕ) (hn : n < 2 ^ 64) :
    cost (rightOutIR n colB S sLB) t = 4819 + 28 * n := by
  simp [rightOutIR, cost, cost_leafOutIR n colB S t hn, cost_outCpIR sLB 597 t (by norm_num), blkSteps]
  omega

theorem outs_rightOutIR (n colB S sLB t : ℕ) (hn : n < 2 ^ 64) :
    outs (rightOutIR n colB S sLB) t = 601 + 4 * n := by
  simp only [rightOutIR, outs, outs_leafOutIR n colB S t hn, outs_outCpIR sLB 597 t (by norm_num)]
  omega

/-- **The right child's run**: it appends `signedWords (rightOf n q (sigOf M sLB))` for the columns
`q m r = M[colB + m·S + r]`, and writes registers only. -/
theorem rightOutIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n colB S sLB : ℕ} (hcol : regs ≤ colB)
    (hS : colB + 2 * n + 3 * S < 2 ^ 64) (hslr : regs ≤ sLB) (hsl : sLB + 597 < 2 ^ 64) :
    (semXIR I (rightOutIR n colB S sLB) s).o.toList = s.o.toList ++
      signedWords (rightOf n (fun m r => rd s.M (colB + m * S + r)) (sigOf (rd s.M) sLB)) ∧
    (∀ x, regs ≤ x → rd (semXIR I (rightOutIR n colB S sLB) s).M x = rd s.M x) ∧
    Inv (semXIR I (rightOutIR n colB S sLB) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  rw [signedWords_rightOf, sigWords_sigOf]
  simp only [rightOutIR, semXIR_seq]
  -- the length word
  have hM1 := inv_sem I (P := .blk [.const rLV (toWord (16 + 32 * n))]) (by simp +decide [WF, Prim.dst, rLV]) hM
  have k1 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rLV (toWord (16 + 32 * n))]) s).M x = rd s.M x :=
    fun x hx => by
      simp only [regs] at hx
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      exact rd_set_ne (by simp only [rLV]; omega)
  have v1 : rd (semXIR I (.blk [.const rLV (toWord (16 + 32 * n))]) s).M rLV = toWord (16 + 32 * n) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rLV]; omega)
  have o1 : (semXIR I (.blk [.const rLV (toWord (16 + 32 * n))]) s).o = s.o := rfl
  generalize semXIR I (.blk [.const rLV (toWord (16 + 32 * n))]) s = s1 at hM1 k1 v1 o1
  have e2 : semXIR I (.out rLV) s1 = ⟨s1.M, s1.o.push (toWord (16 + 32 * n))⟩ := by
    simp only [semXIR, v1]
  rw [e2]
  -- the leaf witness
  obtain ⟨l1, l2, l3⟩ := leafOutIR_sem I ⟨s1.M, s1.o.push (toWord (16 + 32 * n))⟩ hM1 hcol hS
  dsimp only at l1 l2 l3
  generalize semXIR I (leafOutIR n colB S) ⟨s1.M, s1.o.push (toWord (16 + 32 * n))⟩ = s2 at l1 l2 l3
  have hcolr : ∀ m r, rd s1.M (colB + m * S + r) = rd s.M (colB + m * S + r) :=
    fun m r => k1 _ (by simp only [regs] at hcol ⊢; omega)
  simp only [hcolr] at l1
  -- the zero word
  have hs2 := l3.1
  simp only [regs] at hs2
  have hM3 := inv_sem I (P := .blk [.const rLV 0]) (by simp +decide [WF, Prim.dst, rLV]) l3
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rLV 0]) s2).M x = rd s2.M x := fun x hx => by
    simp only [regs] at hx
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_ne (by simp only [rLV]; omega)
  have v3 : rd (semXIR I (.blk [.const rLV 0]) s2).M rLV = 0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    exact rd_set_self (by simp only [rLV]; omega)
  have o3 : (semXIR I (.blk [.const rLV 0]) s2).o = s2.o := rfl
  generalize semXIR I (.blk [.const rLV 0]) s2 = s3 at hM3 k3 v3 o3
  have e4 : semXIR I (.out rLV) s3 = ⟨s3.M, s3.o.push 0⟩ := by simp only [semXIR, v3]
  rw [e4]
  -- the signature
  obtain ⟨c1, c2, c3⟩ := outCpIR_sem I ⟨s3.M, s3.o.push 0⟩ hM3 hslr hsl
  dsimp only at c1 c2 c3
  have hsig : wsAt (rd s3.M) sLB 597 = wsAt (rd s.M) sLB 597 := by
    simp only [wsAt]
    refine List.map_congr_left fun j _ => ?_
    have hx : regs ≤ sLB + j := by simp only [regs] at hslr ⊢; omega
    exact (k3 _ hx).trans ((l2 _ hx).trans (k1 _ hx))
  refine ⟨?_, fun x hx => (c2 x hx).trans ((k3 x hx).trans ((l2 x hx).trans (k1 x hx))), c3⟩
  rw [c1, Array.toList_push, o3, l1, Array.toList_push, o1, hsig]
  simp [toWord_zero', witWords_xs6]

/-! ## The left child (specification) -/

/-- **The trace on the stream lanes `W`** (FORMAT6 v2 §T, with the tag byte; season 1's `readTraceL` with the
schedule's query lengths `lens` of entries `1 … qS − 1`): `q₀` from lane 1's bytes 1–7 and lanes 2–5, then each
entry `|q|, q, a` from lane 6 on at its static lane (the length lanes are not read). -/
def readTrace6 (lens : List ℕ) (W : ℕ → Word) : Trace :=
  q0Ent W :: (walk 6 lens).map fun x => entAt W x.1 x.2

/-- One entry's contribution to the proof after the previous answer `prev`: a node query its half that is not
`prev`, a leaf query (a length in `leafLs`) its bytes, any other query its message after the 32-byte state. -/
def piece6 (leafLs : List ℕ) (prev : Digest) (e : ByteArray × Digest) : List UInt8 :=
  if e.1.data.toList.length = 64 then
    (if e.1.data.toList.take 32 = prev.toList then e.1.data.toList.drop 32 else e.1.data.toList.take 32)
  else if e.1.data.toList.length ∈ leafLs then e.1.data.toList
  else e.1.data.toList.drop 32

/-- The contributions of a run of entries. -/
def pieces6 (leafLs : List ℕ) : Digest → Trace → List UInt8
  | _, [] => []
  | prev, e :: tr => piece6 leafLs prev e ++ pieces6 leafLs e.2 tr

/-- **The proof a trace spells** (FORMAT6 v2.5 §3, §6): `HDR` from the seed `a₀ ‖ HDR` (its first 32 bytes
dropped), then every later entry's contribution; `q₀` contributes nothing. -/
def reassemble6 (leafLs : List ℕ) : Trace → Proof
  | _ :: sd :: tr => bArr (sd.1.data.toList.drop 32 ++ pieces6 leafLs sd.2 tr)
  | _ => bArr []

/-- **The left child**: the proof the stream's trace spells, the trace, the signature `σ'` at `sB`. The stream's
lanes are window words from `tB`. -/
def leftOf6 (lens leafLs : List ℕ) (W : ℕ → Word) (tB sB : ℕ) : Signed :=
  ⟨reassemble6 leafLs (readTrace6 lens fun u => W (tB + u)), readTrace6 lens (fun u => W (tB + u)), sigOf W sB⟩

/-- **The node witness** of BLUEPRINT §2.1 from the child's statement `c'`, the leaf statement `L`, the decoded tree
columns `q` and the decoded window `W`. -/
def nodeWit6 (lens leafLs : List ℕ) (c' L : Digest) (n : ℕ) (q : Cols) (W : ℕ → Word) (tB sB sLB : ℕ) : Wit :=
  .node c' L (leftOf6 lens leafLs W tB sB) (rightOf n q (sigOf W sLB))

/-- **The node witness's words**, in output order: tag, `c'`, `L`, the left child, the right child. -/
theorem witWords_nodeWit6 (lens leafLs : List ℕ) (c' L : Digest) (n : ℕ) (q : Cols) (W : ℕ → Word)
    (tB sB sLB : ℕ) :
    witWords (nodeWit6 lens leafLs c' L n q W tB sB sLB) = toWord 1 :: packBytes c'.toList ++
      packBytes L.toList ++ signedWords (leftOf6 lens leafLs W tB sB) ++
      (toWord (16 + 32 * n) :: leafWords n q ++ [toWord 0] ++ wsAt W sLB 597) := by
  rw [nodeWit6, witWords, signedWords_rightOf, sigWords_sigOf]

end Lvm6.X
