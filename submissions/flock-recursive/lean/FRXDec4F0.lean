-- G6: this module also holds the former modules `FRX4Prog`, `FRX4Ext`, `FRXChain4` (one section each, in import order).
import FRXSpec
import FRVerifierC4
import FRSoundness4Frame
import FRXDec
import FRXLevel
import FRVIR4
import FRSoundness4TailFold
import FRXDec4Levels
import FRXMsg

section G6_FRX4Prog

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11 … B-15; §6.2 step 1, §6.4; stage S-H3).

/-!
# The revision 4.1 extractor program: the parse, the kind dispatch, the aggregate leaf

`ext4IRWith nd` reads `|π|` (tape word 4) and the first proof byte (the low byte of tape word 5)
and branches as `FRVerifier4.kindOf4` does:

* `'A'` (`aggByte`), any size: **`aggIR`** outputs the leaf witness `(s, n)` of the aggregate:
  `s` is `π`'s bytes `64 … 95` (the first segment's `hdr.pub`, `FRAgg.aggWit`) and `n` its bytes
  `8 … 15` (`hdr_A`'s `enc64 n`). Each of the five words is read from the tape and **masked** by
  `8j < |π|`, so that a short proof reads zeros where the tape already holds the log;
* a node byte (`N2`, `N4`, `N8`) with `|π| = piSizeOf seq4`: the **node branch `nd`**, a parameter
  under `DecOk4` (well formed, loop bounds on the domain, a cost within `decBudget`, at most
  `outCap` words, at most `2^19` statements);
* a node byte with another size, or a bare segment byte (`L30`, `L31`, `L32`): no output;
* anything else, and the empty proof: the `W` branch `wIR` (3.x's), which copies `π`'s packed
  words.

The kind flag `rIsK` is cleared on an empty proof: tape word 5 is then the log's first word, not a
proof byte (3.x did not need this: its `bad` and an empty `W` both output nothing; here `'A'` would
output a leaf).

**Why `nd` is a parameter.** 3.x's node decoder (`FRXNode.decNode`) decodes `f⁽⁰⁾` at `m = 30`
in `2^47.0` steps. At `ladderOf 31` (`N2`) the same five levels cost `2^49.0`, and at
`ladderOf 32` (`N4`/`N8`) `2^51.0`, over the contract's cap `B t = 2^48 + 2^16 t`: level 0's
barycentric interpolation is quadratic in `k = 2^(m − 13)` (`logs/S-H3/fuel-check.txt`; S-H2
RESULT Part 24). The revision 4.1 node decoder needs a different level-0 algorithm. Until it
exists the certificate's branch is `nd := .blk []` (`ext4`), which outputs nothing.

The memory is `memX4 = 2^28` words (S-H4, Part 25 F2: the level-0 decoder holds `f⁽⁰⁾`'s codeword,
`2^27` words at `m = 32`), `mpwX = 3`; the fuel (`fuel t = 3·2^46 + 2^13 t`, claim.json) is 3.x's. The
node branch's budget is `decBudget4 = fuelBase − 2^29 + (fuelPerWord − 16) t`.
-/

namespace FR.X.X4

open RecursionFast FR.X

/-! ## Registers (above every 3.x register in use) -/

/-- `1` iff the first proof byte is `'A'`. -/ def rIsA : ℕ := 248
/-- `1` iff the first proof byte is a node byte. -/ def rIsN : ℕ := 249
/-- `1` iff `|π| ≠ 0`. -/ def rNZ : ℕ := 250
/-- The mask `8j < |π|`. -/ def rMk : ℕ := 251

/-! ## The parse and the dispatch -/

/-- `w = b` as a flag word. -/
def isW (w b : Word) : Word := if w = b then 1 else 0

/-- `d := (rB0 = b)`. -/
def eqPs (d : ℕ) (b : Word) : List Prim := [.const rK b, .op .eq d rB0 rK]
/-- `d := d ||| (rB0 = b)`. -/
def orPs (d : ℕ) (b : Word) : List Prim := [.const rK b, .op .eq rT rB0 rK, .op .or d d rT]
/-- `rB0 :=` its low byte. -/
def normPs : List Prim := [.const rK 0xFF, .op .and rB0 rB0 rK]
/-- `rIsK := (rIsK ||| rIsA ||| rIsN) &&& (|π| ≠ 0)`. -/
def finPs : List Prim :=
  [.op .or rIsK rIsK rIsA, .op .or rIsK rIsK rIsN, .const rK 0, .op .ltu rNZ rK rLen,
   .op .and rIsK rIsK rNZ]
/-- `rIsSz := (|π| = piSizeOf seq4)`. -/
def szPs : List Prim := [.const rK (BitVec.ofNat 64 876304), .op .eq rIsSz rLen rK]

/-- The kind flags: `rIsA` (`'A'`), `rIsN` (`N2`/`N4`/`N8`), `rIsK` (`'A'`, a node or a segment
byte, and `|π| ≠ 0`), `rIsSz` (`|π| = piSizeOf seq4`). -/
def kindPs4 : List Prim :=
  normPs ++ eqPs rIsA 0x41 ++ eqPs rIsN 0x4D ++ orPs rIsN 0x4E ++ orPs rIsN 0x4F ++
    eqPs rIsK 0x50 ++ orPs rIsK 0x4B ++ orPs rIsK 0x4C ++ finPs ++ szPs

theorem kindPs4_length : kindPs4.length = 27 := rfl

/-- The parse: `rLen := |π|`, `rB0 :=` tape word 5, the flags. -/
def parse4 : XIR := .seq (readAt rLen 4) (.seq (readAt rB0 5) (.blk kindPs4))

/-- Output proof word `j` (tape word `5 + j`), masked by `8j < |π|`. -/
def outW (j : ℕ) : XIR :=
  .seq (readAt rW (5 + j))
    (.seq (.blk [.const rK (BitVec.ofNat 64 (8 * j)), .op .ltu rMk rK rLen, .op .mul rW rW rMk])
      (.out rW))

/-- **The aggregate leaf's output**: the tag `0`, proof words `8 … 11` (bytes `64 … 95`, the
first segment's start), proof word `1` (bytes `8 … 15`, `n`). -/
def aggIR : XIR :=
  .seq (.seq (.blk [.const rW 0]) (.out rW))
    (.seq (outW 8) (.seq (outW 9) (.seq (outW 10) (.seq (outW 11) (outW 1)))))

/-- **The revision 4.1 extractor's program**, with the node branch `nd`. -/
def ext4IRWith (nd : XIR) : XIR :=
  .seq parse4 (.ite rIsK (.ite rIsA aggIR (.ite rIsN (.ite rIsSz nd (.blk [])) (.blk []))) wIR)

/-- **The obligations on the node branch** for `Computes` (3.x's `DecOk` at `piSizeOf seq4`). -/
structure DecOk4 (nd : XIR) : Prop where
  /-- Well formed. -/
  wf : WF nd
  /-- Its loop bounds hold on every domain tape of a proof of `piSizeOf seq4` bytes. -/
  safe : ∀ c (π : Proof) (L : Log), π.size = Rev4.piSizeOf Rev4.seq4 → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    Safe (extractorInput c π L).toArray (extractorInput c π L).length nd
  /-- Its cost is within `decBudget4` (the fuel less the `memX4` prologue). -/
  cost : ∀ t, cost nd t ≤ decBudget4 t
  /-- It outputs at most `outCap` words. -/
  outs : ∀ t, outs nd t ≤ outCap
  /-- It compiles to at most `2^19` statements. -/
  size : sizeIR nd ≤ 2 ^ 19

/-- The program with the node branch `nd`. -/
def ext4With (nd : XIR) : XProg := toProg memX4 mpwX (ext4IRWith nd)

/-- **The node branch delivered so far**: none (no output). -/
def ndNone : XIR := .blk []

theorem decOk4_ndNone : DecOk4 ndNone where
  wf := by simp [ndNone, WF]
  safe := fun _ _ _ _ _ _ => .blk _
  cost := fun t => by simp [ndNone, cost, blkSteps, decBudget4, fuelBase, fuelPerWord]; omega
  outs := fun t => by simp [ndNone, outs]
  size := by simp [ndNone, sizeIR, blkSteps]

/-- **The revision 4.1 extractor program** `ext4 := toProg 2^28 3 (ext4IRWith ndNone)`. -/
def ext4 : XProg := ext4With ndNone

/-! ## Well formed, cost, size, fuel -/

theorem wf_parse4 : WF parse4 := by
  simp only [parse4, readAt, WF]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide

theorem wf_outW (j : ℕ) : WF (outW j) := by
  simp only [outW, readAt, WF, List.mem_cons, List.mem_nil_iff, Prim.dst, rA, rW, rK, rMk]
  simp_all

theorem wf_aggIR : WF aggIR := by
  refine ⟨⟨by simp [WF, Prim.dst, rW], trivial⟩, wf_outW _, wf_outW _, wf_outW _, wf_outW _,
    wf_outW _⟩

theorem wf_ext4IRWith {nd : XIR} (h : WF nd) : WF (ext4IRWith nd) :=
  ⟨wf_parse4, ⟨wf_aggIR, ⟨h, by simp [WF]⟩, by simp [WF]⟩, wf_wIR⟩

theorem cost_outW (j t : ℕ) : cost (outW j) t = 11 := by
  simp [outW, readAt, cost, blkSteps]

theorem cost_aggIR (t : ℕ) : cost aggIR t = 63 := by
  simp [aggIR, cost, cost_outW, blkSteps]

theorem cost_ext4IRWith (nd : XIR) (t : ℕ) :
    cost (ext4IRWith nd) t ≤ 200 + cost nd t + 8 * t := by
  simp only [ext4IRWith, parse4, readAt, kindPs4_length, wIR, wPre, wCntPs, wBody, cost, blkSteps,
    List.length_cons, List.length_nil, Aff.eval, Nat.div_one, cost_aggIR]
  norm_num; omega

theorem sizeIR_ext4IRWith (nd : XIR) : sizeIR (ext4IRWith nd) ≤ 200 + sizeIR nd := by
  simp only [ext4IRWith, parse4, readAt, kindPs4_length, wIR, wPre, wCntPs, wBody, aggIR, outW, sizeIR,
    blkSteps, List.length_cons, List.length_nil]
  norm_num; omega

/-- **The fuel covers the program** whenever the node branch is within `decBudget4`. -/
theorem fuel_covers4 {nd : XIR} (h : ∀ t, cost nd t ≤ decBudget4 t) (t : ℕ) :
    memX4 + mpwX * t + cost (ext4IRWith nd) t + 8 ≤ fuel t := by
  have := h t
  have := cost_ext4IRWith nd t
  simp only [memX4, mpwX, fuel, fuelBase, fuelPerWord, decBudget4] at *
  omega

/-- The program is within `progCap`. -/
theorem size_ext4With {nd : XIR} (h : sizeIR nd ≤ 2 ^ 19) : (ext4With nd).body.size ≤ progCap := by
  have := sizeIR_ext4IRWith nd
  simp only [ext4With, toProg, size_compile, sizeIR, initPs, blkSteps, List.length_cons,
    List.length_nil, progCap]
  norm_num; omega

/-! ## The parse's registers -/

theorem parse4_o (I : Array Word) (s : St) : (semXIR I parse4 s).o = s.o := by
  simp [parse4, readAt, semXIR]

theorem runPrims_append (a b : List Prim) (M : Mem) :
    runPrims (a ++ b) M = runPrims b (runPrims a M) := List.foldl_append ..

theorem rd_eqPs {d : ℕ} (b : Word) (M : Mem) (hd : d ≠ rK) (hdl : d < 256) (hM : 256 ≤ M.size) :
    rd (runPrims (eqPs d b) M) d = isW (rd M rB0) b := by
  simp only [eqPs, runPrims, List.foldl, Prim.run, rK, rB0] at hd ⊢
  simp (disch := first | omega | (simp only [size_set]; omega))
    [rd_set_self, rd_set_ne, XOp.eval, isW]

theorem rd_orPs {d : ℕ} (b : Word) (M : Mem) (hd : d ≠ rK) (hd2 : d ≠ rT) (hdl : d < 256)
    (hM : 256 ≤ M.size) : rd (runPrims (orPs d b) M) d = rd M d ||| isW (rd M rB0) b := by
  simp only [orPs, runPrims, List.foldl, Prim.run, rK, rB0, rT] at hd hd2 ⊢
  simp (disch := first | omega | (simp only [size_set]; omega))
    [rd_set_self, rd_set_ne, XOp.eval, isW]

theorem rd_szPs (M : Mem) (hM : 256 ≤ M.size) :
    rd (runPrims szPs M) rIsSz = isW (rd M rLen) (BitVec.ofNat 64 876304) := by
  simp only [szPs, runPrims, List.foldl, Prim.run, rK, rIsSz, rLen]
  simp (disch := first | omega | (simp only [size_set]; omega))
    [rd_set_self, rd_set_ne, XOp.eval, isW]

theorem rd_normPs (M : Mem) (hM : 256 ≤ M.size) :
    rd (runPrims normPs M) rB0 = rd M rB0 &&& 0xFF := by
  simp only [normPs, runPrims, List.foldl, Prim.run, rK, rB0]
  simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, XOp.eval]

theorem rd_finPs (M : Mem) (hM : 256 ≤ M.size) :
    rd (runPrims finPs M) rIsK = ((rd M rIsK ||| rd M rIsA) ||| rd M rIsN) &&&
      (if (0 : Word) < rd M rLen then 1 else 0) := by
  simp only [finPs, runPrims, List.foldl, Prim.run, rK, rIsK, rIsA, rIsN, rNZ, rLen]
  simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, XOp.eval]
  rfl

/-- The low byte of tape word 5 against `b`. -/
def bOf (I : Array Word) (b : Word) : Word := isW (I.getD 5 0 &&& 0xFF) b

theorem semXIR_blk4 (I : Array Word) (ps : List Prim) (s : St) :
    semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ := rfl

/-- The parse's memory: `kindPs4` after the two tape reads. -/
theorem parse4_M (I : Array Word) (s : St) (hM : Inv s.M) : ∃ M, 256 ≤ M.size ∧
    rd M rLen = I.getD 4 0 ∧ rd M rB0 = I.getD 5 0 ∧ (semXIR I parse4 s).M = runPrims kindPs4 M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨(semXIR I (.seq (readAt rLen 4) (readAt rB0 5)) s).M, ?_, ?_, ?_, ?_⟩
  rotate_left 3
  · rw [parse4, semXIR_seq, semXIR_seq, semXIR_blk4, semXIR_seq]
  all_goals simp only [readAt, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rB0]
  all_goals simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]
  all_goals try exact hs

theorem parse4_sz (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parse4 s).M rIsSz = isW (I.getD 4 0) (BitVec.ofNat 64 876304) := by
  obtain ⟨M, h0, h1, -, e⟩ := parse4_M I s hM
  rw [e, kindPs4]
  simp only [runPrims_append]
  rw [rd_szPs _ (by simp only [size_runPrims]; omega)]
  simp (disch := decide) only [rd_runPrims_of_not_writes]
  exact congrArg (isW · _) h1

theorem parse4_len (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parse4 s).M rLen = I.getD 4 0 := by
  obtain ⟨M, h0, h1, -, e⟩ := parse4_M I s hM
  rw [e, kindPs4]
  simp only [runPrims_append]
  simp (disch := decide) only [rd_runPrims_of_not_writes]
  exact h1

theorem parse4_A (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parse4 s).M rIsA = bOf I 0x41 := by
  obtain ⟨M, h0, -, h2, e⟩ := parse4_M I s hM
  rw [e, kindPs4]
  simp only [runPrims_append]
  simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
    [rd_runPrims_of_not_writes, rd_eqPs, rd_normPs]
  rw [h2]; rfl

theorem parse4_N (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parse4 s).M rIsN = (bOf I 0x4D ||| bOf I 0x4E) ||| bOf I 0x4F := by
  obtain ⟨M, h0, -, h2, e⟩ := parse4_M I s hM
  rw [e, kindPs4]
  simp only [runPrims_append]
  simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
    [rd_runPrims_of_not_writes, rd_orPs, rd_eqPs, rd_normPs]
  rw [h2]; rfl

theorem parse4_K (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parse4 s).M rIsK =
      ((((bOf I 0x50 ||| bOf I 0x4B) ||| bOf I 0x4C) ||| bOf I 0x41) |||
        ((bOf I 0x4D ||| bOf I 0x4E) ||| bOf I 0x4F)) &&&
      (if (0 : Word) < I.getD 4 0 then 1 else 0) := by
  obtain ⟨M, h0, h1, h2, e⟩ := parse4_M I s hM
  rw [e, kindPs4]
  simp only [runPrims_append]
  simp (disch := decide) only [rd_runPrims_of_not_writes]
  rw [rd_finPs _ (by simp only [size_runPrims]; omega)]
  simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
    [rd_runPrims_of_not_writes, rd_orPs, rd_eqPs, rd_normPs]
  rw [h1, h2]; rfl

end FR.X.X4

end G6_FRX4Prog

section G6_FRX4Ext

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11 … B-15; §6.4, §6.5; stage S-H3).

/-!
# The revision 4.1 extractor `E4X`, `computes4`, and the laws `FRSoundness4Frame` needs

* **The denotation per kind** (`den` of `ext4IRWith nd`, on every log, `|π| < 2^64`):
  `den4_W` (a `W` proof: its packed words), `den4_bad` (nothing), `den4_agg` (an aggregate:
  `witWords (aggLeaf π)`, with `aggLeaf π = .leaf (bytesAt π 64 32) (Rev4.rdLE64 π 8)`), and `den4_node`
  (a node: what `nd` outputs from the parse's state).
* **`E4X nd A`** (B-15 on revision 4.1's kinds): `Ed4 nd`, the decoded denotation, on the contract's
  domain `InDomE`; outside it `Eout4 A`: `W` decoded, `A` its leaf, a node searched under the key
  it carries (`FRXSearch.search`), `bad` none. **`computes4`**: `Computes (ext4With nd) (E4X nd A)
  fuel` for every node branch under `DecOk4` and every `A`.
* **`extOff_E4X`**: `E4X` meets `FRSoundness4Frame.ExtOff` (`W` decoded on every size, an aggregate's
  `aggWit` returned).
* **`nodeExt_E4X`**: `NodeExtLog` for `E4X`, from `NodeSoundLog` (outside the domain, through the
  search) and **`NodeDecLaw4`**, the node branch's law on the domain: on an accepted node run on a
  good log, with the transcript `es` the run reads and the chain links `Links` (S-H2's `E_node`
  hypotheses, a parameter here), `nd`'s output decodes to `readW κ L es`, and that is a witness.
  This is the interface the revision 4.1 node decoder must meet; it is not discharged here (the
  3.x decoder exceeds the fuel at `m = 31/32`, `FRX4Prog`'s header).
* `ks4_E4X`: `FRSoundness4Frame.ks4_of` at `S.E = E4X nd S.acc`.
-/

namespace FR.X.X4

open RecursionFast FR.X

/-! ## Packed words of short byte windows -/

theorem ofLE_zeros : ∀ n, ofLE (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, ofLE_cons, ofLE_zeros n]; rfl

theorem ofLE_append_zeros (l : List UInt8) (n : ℕ) : ofLE (l ++ List.replicate n 0) = ofLE l := by
  rw [ofLE_append, ofLE_zeros]; simp

/-- Zero bytes appended do not change the packed words. -/
theorem packBytes_pad (l : List UInt8) (z j : ℕ) :
    (packBytes (l ++ List.replicate z 0)).getD j 0 = (packBytes l).getD j 0 := by
  rw [packBytes_getD, packBytes_getD, List.length_append, List.length_replicate]
  by_cases h : 8 * j < l.length
  · rw [if_pos (by omega), if_pos h, List.drop_append_of_le_length (by omega),
      List.take_append, List.take_replicate, ofLE_append_zeros]
  · rw [if_neg h]
    split_ifs with h2
    · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        List.drop_replicate, List.take_replicate, ofLE_zeros]; rfl
    · rfl

theorem bytesAt_pad (q : ByteArray) (o n : ℕ) :
    (bytesAt q o n).toList = ((q.data.toList ++ List.replicate (o + n) 0).drop o).take n := by
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  have hk : k < n := by simpa using h1
  rw [Vector.getElem_toList, getElem_bytesAt _ _ _ _ hk, List.getElem_take, List.getElem_drop,
    List.getElem_append]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default _ _ (by omega), List.getElem_replicate]

/-- **A 32-byte window at a word boundary packs to four of the string's words**, on every size
(missing bytes read `0`, missing words are `0`). -/
theorem packBytes_bytesAt' (q : ByteArray) (a : ℕ) {m : ℕ} (hm : m < 4) :
    (packBytes (bytesAt q (8 * a) 32).toList).getD m 0 = (packBytes q.data.toList).getD (a + m) 0 := by
  rw [bytesAt_pad, show 32 = 8 * 4 from rfl, packBytes_take8 _ hm, packBytes_drop8, packBytes_pad]

theorem packBytes_bytesAt4 (q : ByteArray) (a : ℕ) :
    packBytes (bytesAt q (8 * a) 32).toList = [(packBytes q.data.toList).getD a 0,
      (packBytes q.data.toList).getD (a + 1) 0, (packBytes q.data.toList).getD (a + 2) 0,
      (packBytes q.data.toList).getD (a + 3) 0] := by
  rw [packBytes_digest_eq4, packBytes_bytesAt' q a (by decide), packBytes_bytesAt' q a (by decide),
    packBytes_bytesAt' q a (by decide), packBytes_bytesAt' q a (by decide), Nat.add_zero]

theorem bytesAt_succ (q : ByteArray) (o n : ℕ) :
    (bytesAt q o (n + 1)).toList = byteAt q o :: (bytesAt q (o + 1) n).toList := by
  simp only [bytesAt, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
  congr 1
  congr 1
  funext i
  rw [show o + (↑i + 1) = o + 1 + ↑i by omega]

theorem ofLE_bytesAt (q : ByteArray) : ∀ (n o : ℕ),
    ofLE (bytesAt q o n).toList = ((List.range n).map fun i => (byteAt q (o + i)).toNat * 256 ^ i).sum
  | 0, _ => rfl
  | n + 1, o => by
    rw [bytesAt_succ, ofLE_cons, ofLE_bytesAt q n (o + 1), List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map, ← List.sum_map_mul_left]
    congr 1
    · simp
    · refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [show o + (i + 1) = o + 1 + i by omega, pow_succ]
      ring

theorem rdLE64_eq (π : Proof) (o : ℕ) : Rev4.rdLE64 π o = ofLE (bytesAt π o 8).toList := by
  rw [ofLE_bytesAt]; rfl

theorem rdLE64_lt (π : Proof) (o : ℕ) : Rev4.rdLE64 π o < 2 ^ 64 := by
  rw [rdLE64_eq]
  have := ofLE_lt (bytesAt π o 8).toList
  simpa using this

/-- `n`'s word is the string's word `a`. -/
theorem toWord_rdLE64 (π : Proof) (a : ℕ) :
    toWord (Rev4.rdLE64 π (8 * a)) = (packBytes π.data.toList).getD a 0 := by
  rw [rdLE64_eq, bytesAt_pad, ← packBytes_pad π.data.toList (8 * a + 8) a, packBytes_getD,
    if_pos (by simp; omega)]

/-! ## The aggregate leaf -/

/-- **The leaf witness of an aggregate proof**: the first segment's start (bytes `64 … 95`) and
`n` (bytes `8 … 15`). -/
def aggLeaf (π : Proof) : Wit := .leaf (bytesAt π 64 32) (Rev4.rdLE64 π 8)

/-- `aggWit` returns `aggLeaf`'s fields (segments of `piSizeOf seq4 ≥ 48` bytes). -/
theorem aggWit_eq {π : Proof} {s : Digest} {n : ℕ} (h : Rev4.aggWit (Rev4.piSizeOf Rev4.seq4) π = some (s, n)) :
    aggLeaf π = .leaf s n := by
  generalize hps : Rev4.piSizeOf Rev4.seq4 = S at h
  replace hps : S = 876304 := hps ▸ Rev4.piSizeOf_seq4
  simp only [Rev4.aggWit, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨v, ⟨π₁, hh, hv⟩, hvn⟩ := h
  simp only [Prod.mk.injEq] at hvn
  obtain ⟨rfl, rfl⟩ := hvn
  rw [aggLeaf]
  refine congrArg (Wit.leaf · _) ?_
  simp only [Rev4.aggSegs] at hh
  rcases hk : (byteAt π 1).toNat with _ | k
  · rw [hk] at hh; simp at hh
  · rw [hk, List.range_succ_eq_map, List.map_cons, List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [Rev4.segView, Option.map_eq_some_iff] at hv
    obtain ⟨κ, -, rfl⟩ := hv
    refine Vector.ext fun i hi => ?_
    rw [getElem_bytesAt _ _ _ _ hi, getElem_bytesAt _ _ _ _ hi, toList_extract, hps]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega)]
    congr 2
    omega

/-! ## The flags on an extractor tape -/

section Tape
variable (c : Digest) (π : Proof) (L : Log)

theorem tape4 : (extractorInput c π L).toArray.getD 4 0 = toWord π.size := by
  rw [getD_toArray, tape_getD4]

/-- With a nonempty proof, the low byte of tape word 5 is the proof's first byte. -/
theorem bOf_tape (hπ : 0 < π.size) (v : Word) (hv : v.toNat < 256) :
    bOf (extractorInput c π L).toArray v = if (byteAt π 0).toNat = v.toNat then 1 else 0 := by
  have h0 : π.data[0]? = some (byteAt π 0) := by
    rw [byteAt_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by exact hπ)]; rfl
  have hb := tape_byte0 c π L h0
  rw [bOf, isW, getD_toArray]
  congr 1
  apply propext
  rw [← BitVec.toNat_inj, lowByte, ← hb, toNat_toUInt8]

end Tape

/-! ## The kinds by their first byte -/

section Kinds
variable {π : Proof}

theorem kindOf4_eq (π : Proof) : Rev4.kindOf4 π =
    if byteAt π 0 = Rev4.aggByte then .agg else match Rev4.NodeKind.ofByte? (byteAt π 0) with
      | some κ => if π.size = Rev4.piSizeOf Rev4.seq4 then .node κ else .bad
      | none => if (Rev4.SegKind.ofByte? (byteAt π 0)).isSome then .bad else .W := rfl

theorem kindOf4_agg (h : Rev4.kindOf4 π = .agg) : byteAt π 0 = Rev4.aggByte := by
  rw [kindOf4_eq] at h
  generalize byteAt π 0 = b at h ⊢
  by_contra h1
  rw [if_neg h1] at h
  cases hn : Rev4.NodeKind.ofByte? b <;> rw [hn] at h <;> simp only at h <;> split_ifs at h

theorem nodeOfByte_eq {b : UInt8} {κ : Rev4.NodeKind} (h : Rev4.NodeKind.ofByte? b = some κ) :
    b = κ.byte := by
  unfold Rev4.NodeKind.ofByte? at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> assumption

theorem kindOf4_node {κ : Rev4.NodeKind} (h : Rev4.kindOf4 π = .node κ) :
    byteAt π 0 = κ.byte ∧ π.size = 876304 := by
  rw [kindOf4_eq] at h
  generalize byteAt π 0 = b at h ⊢
  by_cases h1 : b = Rev4.aggByte
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    cases hn : Rev4.NodeKind.ofByte? b with
    | none => rw [hn] at h; simp only at h; split_ifs at h
    | some κ' =>
      rw [hn] at h; simp only at h
      split_ifs at h with hs
      cases h
      exact ⟨nodeOfByte_eq hn, hs.trans Rev4.piSizeOf_seq4⟩

theorem kindOf4_W (h : Rev4.kindOf4 π = .W) : byteAt π 0 ≠ Rev4.aggByte ∧
    (∀ κ : Rev4.NodeKind, byteAt π 0 ≠ κ.byte) ∧ ∀ κ : Rev4.SegKind, byteAt π 0 ≠ κ.byte := by
  rw [kindOf4_eq] at h
  generalize byteAt π 0 = b at h ⊢
  by_cases h1 : b = Rev4.aggByte
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    cases hn : Rev4.NodeKind.ofByte? b with
    | some κ' => rw [hn] at h; simp only at h; split_ifs at h
    | none =>
      rw [hn] at h; simp only at h
      split_ifs at h with h2
      refine ⟨h1, fun κ he => ?_, fun κ he => h2 ?_⟩
      · rw [he, Rev4.NodeKind.ofByte?_byte] at hn; cases hn
      · rw [he, Rev4.SegKind.ofByte?_byte]; rfl

theorem segOfByte_eq {b : UInt8} {κ : Rev4.SegKind} (h : Rev4.SegKind.ofByte? b = some κ) :
    b = κ.byte := by
  unfold Rev4.SegKind.ofByte? at h
  split_ifs at h with h1 h2 h3 <;> cases h <;> assumption

theorem kindOf4_bad (h : Rev4.kindOf4 π = .bad) :
    (∃ κ : Rev4.NodeKind, byteAt π 0 = κ.byte ∧ π.size ≠ 876304) ∨
      ∃ κ : Rev4.SegKind, byteAt π 0 = κ.byte := by
  rw [kindOf4_eq] at h
  have hps := Rev4.piSizeOf_seq4
  generalize byteAt π 0 = b at h ⊢
  by_cases h1 : b = Rev4.aggByte
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    cases hn : Rev4.NodeKind.ofByte? b with
    | some κ' =>
      rw [hn] at h; simp only at h
      split_ifs at h with hs
      exact .inl ⟨κ', nodeOfByte_eq hn, hps ▸ hs⟩
    | none =>
      rw [hn] at h; simp only at h
      split_ifs at h with h2
      obtain ⟨κ, hκ⟩ := Option.isSome_iff_exists.1 h2
      exact .inr ⟨κ, segOfByte_eq hκ⟩

theorem pos_of_byte {b : UInt8} (h : byteAt π 0 = b) (hb : b ≠ 0) : 0 < π.size := by
  by_contra h0
  rw [byteAt, dif_neg (by omega)] at h
  exact hb h.symm

end Kinds

/-! ## The flags after the parse, per kind -/

theorem pos_toWord {n : ℕ} (h : n < 2 ^ 64) : ((0 : Word) < toWord n) ↔ 0 < n := by
  rw [BitVec.lt_def, toNat_toWord h]; rfl

section Flags
variable (c : Digest) (π : Proof) (L : Log)

/-- The state after the parse, on the extractor's tape. -/
def st1 : St := semXIR (extractorInput c π L).toArray parse4
  (initSt (memX4 + mpwX * (extractorInput c π L).length))

theorem inv_st1 : Inv (st1 c π L).M :=
  inv_sem _ wf_parse4 (inv_initSt (Nat.le_add_right_of_le (by simp only [regs, memX4]; norm_num)))

theorem st1_o : (st1 c π L).o = #[] := by rw [st1, parse4_o, initSt_o]

theorem bOf_byte (hπ : 0 < π.size) (v : Word) (n : ℕ) (hv : v.toNat = n) (hn : n < 256) :
    bOf (extractorInput c π L).toArray v = if (byteAt π 0).toNat = n then 1 else 0 := by
  rw [bOf_tape c π L hπ v (by omega), hv]

theorem flagK_W (hW : Rev4.kindOf4 π = .W) (hs : π.size < 2 ^ 64) : rd (st1 c π L).M rIsK = 0 := by
  rw [st1, parse4_K _ _ (inv_initSt (Nat.le_add_right_of_le (by simp only [regs, memX4]; norm_num))),
    tape4]
  rcases Nat.eq_zero_or_pos π.size with h0 | hp
  · rw [if_neg (by rw [pos_toWord hs]; omega)]; exact BitVec.and_zero
  · obtain ⟨hA, hN, hS⟩ := kindOf4_W hW
    have ne : ∀ u : UInt8, byteAt π 0 ≠ u → (byteAt π 0).toNat ≠ u.toNat := fun u h e =>
      h (UInt8.toNat_inj.1 e)
    have := ne _ hA; have := ne _ (hN .N2); have := ne _ (hN .N4); have := ne _ (hN .N8)
    have := ne _ (hS .L30); have := ne _ (hS .L31); have := ne _ (hS .L32)
    simp only [Rev4.aggByte, Rev4.NodeKind.byte, Rev4.SegKind.byte, UInt8.toNat_ofNat] at *
    rw [bOf_byte c π L hp _ 80 rfl (by norm_num), bOf_byte c π L hp _ 75 rfl (by norm_num),
      bOf_byte c π L hp _ 76 rfl (by norm_num), bOf_byte c π L hp _ 65 rfl (by norm_num),
      bOf_byte c π L hp _ 77 rfl (by norm_num), bOf_byte c π L hp _ 78 rfl (by norm_num),
      bOf_byte c π L hp _ 79 rfl (by norm_num)]
    simp_all

/-- The flags after the parse on a nonempty proof, by its first byte `n`. -/
theorem flags (hs : π.size < 2 ^ 64) (hp : 0 < π.size) :
    rd (st1 c π L).M rIsK = (((((if (byteAt π 0).toNat = 80 then 1 else 0) |||
      (if (byteAt π 0).toNat = 75 then 1 else 0)) ||| (if (byteAt π 0).toNat = 76 then 1 else 0)) |||
      (if (byteAt π 0).toNat = 65 then 1 else 0)) |||
      (((if (byteAt π 0).toNat = 77 then 1 else 0) ||| (if (byteAt π 0).toNat = 78 then 1 else 0)) |||
        (if (byteAt π 0).toNat = 79 then 1 else 0))) &&& 1 ∧
    rd (st1 c π L).M rIsA = (if (byteAt π 0).toNat = 65 then 1 else 0) ∧
    rd (st1 c π L).M rIsN = ((if (byteAt π 0).toNat = 77 then 1 else 0) |||
      (if (byteAt π 0).toNat = 78 then 1 else 0)) ||| (if (byteAt π 0).toNat = 79 then 1 else 0) ∧
    rd (st1 c π L).M rIsSz = isW (toWord π.size) (BitVec.ofNat 64 876304) ∧
    rd (st1 c π L).M rLen = toWord π.size := by
  have h0 : Inv (initSt (memX4 + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le (by simp only [regs, memX4]; norm_num))
  have hb := fun v n hv hn => bOf_byte c π L hp v n hv hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [st1, parse4_K _ _ h0, tape4, if_pos ((pos_toWord hs).2 hp), hb _ 80 rfl (by norm_num),
      hb _ 75 rfl (by norm_num), hb _ 76 rfl (by norm_num), hb _ 65 rfl (by norm_num),
      hb _ 77 rfl (by norm_num), hb _ 78 rfl (by norm_num), hb _ 79 rfl (by norm_num)]
  · rw [st1, parse4_A _ _ h0, hb _ 65 rfl (by norm_num)]
  · rw [st1, parse4_N _ _ h0, hb _ 77 rfl (by norm_num), hb _ 78 rfl (by norm_num),
      hb _ 79 rfl (by norm_num)]
  · rw [st1, parse4_sz _ _ h0, tape4]
  · rw [st1, parse4_len _ _ h0, tape4]

theorem isW_sz (hs : π.size < 2 ^ 64) :
    isW (toWord π.size) (BitVec.ofNat 64 876304) = if π.size = 876304 then 1 else 0 := by
  rw [isW]
  congr 1
  apply propext
  rw [← BitVec.toNat_inj, toNat_toWord hs, BitVec.toNat_ofNat]

end Flags

/-! ## The denotation per kind -/

section Den
variable (nd : XIR) (c : Digest) (π : Proof) (L : Log)

/-- The branch after the parse. -/
def br4 (nd : XIR) : XIR := .ite rIsK (.ite rIsA aggIR (.ite rIsN (.ite rIsSz nd (.blk [])) (.blk []))) wIR

theorem den4_split : den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) =
    (semXIR (extractorInput c π L).toArray (br4 nd) (st1 c π L)).o.toList := by
  simp only [den, ext4IRWith, semXIR_seq, st1, br4]

/-- **A `W` proof**: the denotation is its packed words, on every log. -/
theorem den4_W (hW : Rev4.kindOf4 π = .W) (hs : π.size < 2 ^ 64) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) = packBytes π.data.toList := by
  rw [den4_split, br4, semXIR_ite, if_pos (flagK_W c π L hW hs),
    wIR_sem _ _ (inv_st1 c π L) (by rw [tape4, toNat_ceil8 hs]; omega), st1_o, tape4,
    toNat_ceil8 hs, Array.toList_empty, List.nil_append]
  refine List.ext_getElem (by
    simp only [List.length_map, List.length_range, packBytes_length]
    rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
  simp only [List.getElem_map, List.getElem_range, getD_toArray]
  exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)

/-- **A `bad` proof**: no output. -/
theorem den4_bad (hB : Rev4.kindOf4 π = .bad) (hs : π.size < 2 ^ 64) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) = [] := by
  rw [den4_split]
  rcases kindOf4_bad hB with ⟨κ, hb, hz⟩ | ⟨κ, hb⟩
  · have hp := pos_of_byte hb (by cases κ <;> decide)
    obtain ⟨hK, hA, hN, hZ, -⟩ := flags c π L hs hp
    rw [isW_sz π hs, if_neg hz] at hZ
    have hn : (byteAt π 0).toNat = κ.byte.toNat := by rw [hb]
    rw [br4, semXIR_ite, if_neg (by rw [hK, hn]; cases κ <;> decide), semXIR_ite,
      if_pos (by rw [hA, hn]; cases κ <;> decide), semXIR_ite,
      if_neg (by rw [hN, hn]; cases κ <;> decide), semXIR_ite, if_pos hZ]
    simp [semXIR, st1_o]
  · have hp := pos_of_byte hb (by cases κ <;> decide)
    obtain ⟨hK, hA, hN, -, -⟩ := flags c π L hs hp
    have hn : (byteAt π 0).toNat = κ.byte.toNat := by rw [hb]
    rw [br4, semXIR_ite, if_neg (by rw [hK, hn]; cases κ <;> decide), semXIR_ite,
      if_pos (by rw [hA, hn]; cases κ <;> decide), semXIR_ite,
      if_pos (by rw [hN, hn]; cases κ <;> decide)]
    simp [semXIR, st1_o]

/-- **A node proof**: the denotation is the node branch's output from the parse's state. -/
theorem den4_node {κ : Rev4.NodeKind} (hN : Rev4.kindOf4 π = .node κ) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) =
      (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList := by
  obtain ⟨hb, hz⟩ := kindOf4_node hN
  have hs : π.size < 2 ^ 64 := by omega
  have hp := pos_of_byte hb (by cases κ <;> decide)
  obtain ⟨hK, hA, hN', hZ, -⟩ := flags c π L hs hp
  rw [isW_sz π hs, if_pos hz] at hZ
  have hn : (byteAt π 0).toNat = κ.byte.toNat := by rw [hb]
  rw [den4_split, br4, semXIR_ite, if_neg (by rw [hK, hn]; cases κ <;> decide), semXIR_ite,
    if_pos (by rw [hA, hn]; cases κ <;> decide), semXIR_ite,
    if_neg (by rw [hN', hn]; cases κ <;> decide), semXIR_ite, if_neg (by rw [hZ]; decide)]

end Den

/-! ## The aggregate branch -/

theorem outW_sem (I : Array Word) (s : St) (hM : Inv s.M) (j : ℕ) (hj : 8 * j < 2 ^ 64) :
    (semXIR I (outW j) s).o.toList = s.o.toList ++
      [I.getD (5 + j) 0 * (if BitVec.ofNat 64 (8 * j) < rd s.M rLen then 1 else 0)] ∧
    rd (semXIR I (outW j) s).M rLen = rd s.M rLen ∧ Inv (semXIR I (outW j) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, ?_, inv_sem I (wf_outW j) hM⟩
  · simp only [outW, readAt, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | omega | (simp only [size_set, rA, rW, rK, rMk]; omega) |
        (simp only [rA, rW, rK, rMk, rLen]; omega))
      [rd_set_self, rd_set_ne, XOp.eval, Array.toList_push]
    rw [Nat.mod_eq_of_lt (show 5 + j < 18446744073709551616 by omega)]
  · simp only [outW, readAt, semXIR, runPrims, List.foldl, Prim.run, rA, rW, rK, rMk, rLen]
    simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne]

theorem mask_word (c : Digest) (π : Proof) (L : Log) (hs : π.size < 2 ^ 64) (j : ℕ) (hj : 8 * j < 2 ^ 64) :
    (extractorInput c π L).toArray.getD (5 + j) 0 *
      (if BitVec.ofNat 64 (8 * j) < toWord π.size then 1 else 0) = (packBytes π.data.toList).getD j 0 := by
  have m1 : ∀ x : Word, x * 1 = x := fun x => by simp
  have m0 : ∀ x : Word, x * 0 = 0 := fun x => by simp
  have hlt : (BitVec.ofNat 64 (8 * j) < toWord π.size) ↔ 8 * j < π.size := by
    rw [BitVec.lt_def, toNat_toWord hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  by_cases h : 8 * j < π.size
  · rw [if_pos (hlt.2 h), m1, getD_toArray, tape_getD_proof c π L (by omega),
      List.getD_eq_getElem]
  · rw [if_neg (fun h' => h (hlt.1 h')), m0, packBytes_getD, if_neg (by
      rw [← WitnessSending.size_eq_length]; omega)]

/-- **An aggregate proof**: the denotation is the leaf witness `aggLeaf π`, on every log. -/
theorem den4_agg (nd : XIR) (c : Digest) (π : Proof) (L : Log) (hA : Rev4.kindOf4 π = .agg)
    (hs : π.size < 2 ^ 64) :
    den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) = witWords (aggLeaf π) := by
  have hb := kindOf4_agg hA
  have hp := pos_of_byte hb (by decide)
  have hn : (byteAt π 0).toNat = 65 := by rw [hb]; rfl
  obtain ⟨hK, hA', -, -, hL⟩ := flags c π L hs hp
  rw [den4_split, br4, semXIR_ite, if_neg (by rw [hK, hn]; decide), semXIR_ite,
    if_neg (by rw [hA', hn]; decide)]
  have hM := inv_st1 c π L
  have ho := st1_o c π L
  generalize st1 c π L = s1 at *
  set I := (extractorInput c π L).toArray with hI
  have hs1 := hM.1
  simp only [regs] at hs1
  set s2 : St := ⟨s1.M.setIfInBounds rW 0, s1.o.push 0⟩ with hs2
  have e0 : semXIR I (.seq (.blk [.const rW 0]) (.out rW)) s1 = s2 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, hs2]
    simp (disch := first | omega | (simp only [size_set]; omega)) [rd_set_self, rW]
  have h2M : Inv s2.M := inv_sem I (P := .blk [.const rW 0]) (by simp [WF, Prim.dst, rW]) hM
  have h2L : rd s2.M rLen = toWord π.size := by
    simp only [hs2]; rw [rd_set_ne (by simp [rW, rLen]), hL]
  have h2o : s2.o.toList = [0] := by simp [hs2, ho]
  rw [aggIR, semXIR_seq, e0]
  clear_value s2
  obtain ⟨o8, l8, i8⟩ := outW_sem I s2 h2M 8 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 8) s2 = s3 at o8 l8 i8
  obtain ⟨o9, l9, i9⟩ := outW_sem I s3 i8 9 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 9) s3 = s4 at o9 l9 i9
  obtain ⟨o10, l10, i10⟩ := outW_sem I s4 i9 10 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 10) s4 = s5 at o10 l10 i10
  obtain ⟨o11, l11, i11⟩ := outW_sem I s5 i10 11 (by norm_num)
  rw [semXIR_seq]; generalize semXIR I (outW 11) s5 = s6 at o11 l11 i11
  obtain ⟨o1, -, -⟩ := outW_sem I s6 i11 1 (by norm_num)
  rw [o1, o11, o10, o9, o8, h2o, l11, l10, l9, l8, h2L, hI, mask_word c π L hs 8 (by norm_num),
    mask_word c π L hs 9 (by norm_num), mask_word c π L hs 10 (by norm_num),
    mask_word c π L hs 11 (by norm_num), mask_word c π L hs 1 (by norm_num)]
  have e1 := packBytes_bytesAt4 π 8
  have e2 := toWord_rdLE64 π 1
  simp only [show 8 * 8 = 64 from rfl, show 8 * 1 = 8 from rfl] at e1 e2
  rw [aggLeaf, witWords, e1, e2]
  rfl

/-! ## The extractor `E4X` -/

/-- **The in-domain extractor**: the decoded denotation of `ext4IRWith nd`. -/
def Ed4 (nd : XIR) : Digest → Proof → Log → Option Wit := Eden memX4 mpwX (ext4IRWith nd)

/-- **The extractor outside the domain** (B-15 on revision 4.1's kinds): `W` decoded, an aggregate's
leaf, a node searched under the key it carries, `bad` none. -/
def Eout4 (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) : Option Wit :=
  match Rev4.kindOf4 π with
  | .W => WitnessSending.decode π
  | .agg => some (aggLeaf π)
  | .node _ => search A (vkOf π) c
  | .bad => none

/-- **The revision 4.1 extractor specification**: `Ed4 nd` on the domain, `Eout4 A` outside it. -/
def E4X (nd : XIR) (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) :
    Option Wit :=
  if InDomE c π L then Ed4 nd c π L else Eout4 A c π L

section E
variable {nd : XIR} {A : Digest → Digest → Signed → Bool} {c : Digest} {π : Proof} {L : Log}

theorem size_lt_of_dom (h : InDomE c π L) : π.size < 2 ^ 64 := by
  have := h.1; rw [outCap] at this; omega

/-- `E4X` decodes a `W` proof, on every size. -/
theorem E4X_W (hW : Rev4.kindOf4 π = .W) : E4X nd A c π L = WitnessSending.decode π := by
  by_cases h : InDomE c π L
  · rw [E4X, if_pos h, Ed4, Eden, den4_W nd c π L hW (size_lt_of_dom h)]; rfl
  · rw [E4X, if_neg h, Eout4, hW]

/-- `E4X` returns an aggregate's leaf, on every size. -/
theorem E4X_agg (hA : Rev4.kindOf4 π = .agg) : E4X nd A c π L = some (aggLeaf π) := by
  by_cases h : InDomE c π L
  · rw [E4X, if_pos h, Ed4, Eden, den4_agg nd c π L hA (size_lt_of_dom h), aggLeaf,
      decodeWit_witWords (.leaf (bytesAt π 64 32) (Rev4.rdLE64 π 8)) (rdLE64_lt π 8)]
  · rw [E4X, if_neg h, Eout4, hA]

/-- `E4X` returns nothing on a `bad` proof. -/
theorem E4X_bad (hB : Rev4.kindOf4 π = .bad) : E4X nd A c π L = none := by
  by_cases h : InDomE c π L
  · rw [E4X, if_pos h, Ed4, Eden, den4_bad nd c π L hB (size_lt_of_dom h)]; rfl
  · rw [E4X, if_neg h, Eout4, hB]

/-- On a node proof in the domain, `E4X` is what the node branch outputs. -/
theorem E4X_node {κ : Rev4.NodeKind} (hN : Rev4.kindOf4 π = .node κ) (h : InDomE c π L) :
    E4X nd A c π L = decodeWit (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList := by
  rw [E4X, if_pos h, Ed4, Eden, den4_node nd c π L hN]

/-- Outside the domain a node proof is searched under the key it carries. -/
theorem E4X_node_out {κ : Rev4.NodeKind} (hN : Rev4.kindOf4 π = .node κ) (h : ¬ InDomE c π L) :
    E4X nd A c π L = search A (vkOf π) c := by
  rw [E4X, if_neg h, Eout4, hN]

/-- **`E4X` meets `ExtOff`** (`FRSoundness4Frame`). -/
theorem extOff_E4X (nd : XIR) (A : Digest → Digest → Signed → Bool) : Rev4.ExtOff (E4X nd A) :=
  ⟨fun _ _ _ hW => E4X_W hW, fun _ π _ s n hA ha => by rw [E4X_agg hA, aggWit_eq ha]⟩

end E

/-! ## Halting within the fuel: `computes4` -/

theorem safe_parse4 (I : Array Word) (t : ℕ) : Safe I t parse4 :=
  .seq (.seq (.blk _) (.input _ _)) (.seq (.seq (.blk _) (.input _ _)) (.blk _))

theorem safe_outW (I : Array Word) (t j : ℕ) : Safe I t (outW j) :=
  .seq (.seq (.blk _) (.input _ _)) (.seq (.blk _) (.out _))

theorem safe_aggIR (I : Array Word) (t : ℕ) : Safe I t aggIR :=
  .seq (.seq (.blk _) (.out _)) (.seq (safe_outW ..) (.seq (safe_outW ..) (.seq (safe_outW ..)
    (.seq (safe_outW ..) (safe_outW ..)))))

theorem outs_aggIR (t : ℕ) : outs aggIR t = 6 := by
  simp [aggIR, outW, readAt, outs]

/-- The loop bounds of the branch after the parse, on every domain tape. -/
theorem boundsOk_br4 {nd : XIR} (hnd : DecOk4 nd) (c : Digest) (π : Proof) (L : Log)
    (h : InDomE c π L) (s1 : St) (hM : Inv s1.M)
    (hz : rd s1.M rIsSz ≠ 0 → π.size = Rev4.piSizeOf Rev4.seq4) :
    BoundsOk (extractorInput c π L).toArray (extractorInput c π L).length (br4 nd) s1 := by
  have hs := size_lt_of_dom h
  have hwf := wf_ext4IRWith hnd.wf
  rw [br4, boundsOk_ite]
  by_cases hK : rd s1.M rIsK = 0
  · rw [if_pos hK]
    exact boundsOk_of_safe (safe_wIR hs (tape4 c π L) (by have := tape_length c π L; omega))
      hwf.2.2 _ hM
  · rw [if_neg hK, boundsOk_ite]
    by_cases hA : rd s1.M rIsA = 0
    · rw [if_pos hA, boundsOk_ite]
      by_cases hN : rd s1.M rIsN = 0
      · rw [if_pos hN]; trivial
      · rw [if_neg hN, boundsOk_ite]
        by_cases hZ : rd s1.M rIsSz = 0
        · rw [if_pos hZ]; trivial
        · rw [if_neg hZ]
          exact boundsOk_of_safe (hnd.safe c π L (hz hZ) h.2.1 h.2.2) hnd.wf _ hM
    · rw [if_neg hA]
      exact boundsOk_of_safe (safe_aggIR _ _) wf_aggIR _ hM

theorem ext4IRWith_eq (nd : XIR) : ext4IRWith nd = .seq parse4 (br4 nd) := rfl

-- `br4` is irreducible here: a `BoundsOk … (br4 nd) s` hypothesis is otherwise unfolded and
-- evaluated on the concrete tape (maximum recursion depth).
attribute [local irreducible] br4 in
/-- **The program halts within the fuel with at most `outCap` words** on every domain tape. -/
theorem halts4 {nd : XIR} (hnd : DecOk4 nd) (c : Digest) (π : Proof) (L : Log)
    (h1 : π.size ≤ 8 * outCap) (h2 : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (h3 : (extractorInput c π L).length ≤ 2 ^ 64) :
    ∃ o, (ext4With nd).run (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap := by
  have h : InDomE c π L := ⟨h1, h2, h3⟩
  have hs := size_lt_of_dom h
  have hreg : regs ≤ memX4 := by simp only [regs, memX4]; norm_num
  have hwf := wf_ext4IRWith hnd.wf
  have h0 : Inv (initSt (memX4 + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  have hden : den memX4 mpwX (ext4IRWith nd) (extractorInput c π L) =
      (semXIR (extractorInput c π L).toArray (ext4IRWith nd)
        (initSt (memX4 + mpwX * (extractorInput c π L).length))).o.toList := rfl
  generalize hs0 : initSt (memX4 + mpwX * (extractorInput c π L).length) = s0 at h0 hden
  have hz := parse4_sz (extractorInput c π L).toArray s0 h0
  rw [tape4, isW_sz π hs] at hz
  have hB0 := boundsOk_br4 hnd c π L h (semXIR (extractorInput c π L).toArray parse4 s0)
    (inv_sem _ wf_parse4 h0) fun hz' => by
      rw [Rev4.piSizeOf_seq4]; by_contra hne; rw [if_neg hne] at hz; exact hz' hz
  generalize hI : (extractorInput c π L).toArray = I at hB0 hden
  have hB : BoundsOk I (extractorInput c π L).length (ext4IRWith nd) s0 := by
    rw [ext4IRWith_eq]
    exact (boundsOk_seq (p := parse4) (q := br4 nd)).2
      ⟨boundsOk_of_safe (safe_parse4 _ _) wf_parse4 _ h0, hB0⟩
  have hrun := run_toProg (P := ext4IRWith nd) (input := extractorInput c π L)
    (f := fuel (extractorInput c π L).length) hreg hwf (by rw [hs0, hI]; exact hB)
    (fuel_covers4 hnd.cost _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  rw [← hden]
  rcases hk : Rev4.kindOf4 π with _ | _ | _ | κ
  · rw [den4_W nd c π L hk hs, packBytes_length, ← WitnessSending.size_eq_length]
    rw [outCap] at h1 ⊢; omega
  · rw [den4_bad nd c π L hk hs]; exact Nat.zero_le _
  · rw [den4_agg nd c π L hk hs]; simp [aggLeaf, witWords, outCap, packBytes_digest_length]
  · rw [den4_node nd c π L hk]
    have hz : π.size = Rev4.piSizeOf Rev4.seq4 := (kindOf4_node hk).2.trans Rev4.piSizeOf_seq4.symm
    have := outs_le (I := (extractorInput c π L).toArray) (extractorInput c π L).length nd _ hnd.wf
      (inv_st1 c π L) (boundsOk_of_safe (hnd.safe c π L hz h2 h3) hnd.wf _ (inv_st1 c π L))
    rw [st1_o, Array.size_empty, Nat.zero_add] at this
    rw [Array.length_toList]; exact this.trans (hnd.outs _)

/-- **`Computes (ext4With nd) (E4X nd A) fuel`**, for every node branch under `DecOk4` and every
`A` (on the domain `E4X nd A = Ed4 nd`). -/
theorem computes4 {nd : XIR} (hnd : DecOk4 nd) (A : Digest → Digest → Signed → Bool) :
    Computes (ext4With nd) (E4X nd A) fuel := fun c π L h1 h2 h3 => by
  obtain ⟨o, ho, hl, hd⟩ := computes_Eof fuel (by simp only [regs, memX4]; norm_num)
    (wf_ext4IRWith hnd.wf) (fun c π L h1 h2 h3 => halts4 hnd c π L h1 h2 h3) c π L h1 h2 h3
  exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem ext4_caps {nd : XIR} (hnd : DecOk4 nd) :
    (∀ t, fuel t ≤ extractorBudget t) ∧ (ext4With nd).body.size ≤ progCap :=
  ⟨fuel_le_budget, size_ext4With hnd.size⟩

/-! ## The node law: `NodeExtLog` for `E4X` -/

/-- **What the revision 4.1 node branch must meet** (S-H2's `E_node` at revision 4.1). The node's
cell map and its chain links are parameters: the revision 4.1 node circuit (block-kind map,
`StmtN`/`NodeResid` with `1 + k` slots) is S-E's and does not exist yet.
* `Links κ L es π c`: S-H2's `E_node` hypotheses at the node kind `κ` and the transcript `es` the
  verifier's run reads off `L`: the chain links `fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)`
  (at `seq4`'s positions), the cap links `capDig es i = capPiL i π`, the final link
  `finalAt es x = finPi π x`, `¬ StateHit L`, and per level `¬ farL` and `A_c = jointAgree` (at
  `ladderOf κ.m`).
* `readW κ L es`: the witness read off `f⁽⁰⁾` (S-H2's `FR.readWit` at revision 4.1: the previous
  node, or for `N8` the first aggregate, and the aggregate child `hdr_A ‖ π₁ ‖ … ‖ π_k` with
  `tr_A = tr₁ ‖ … ‖ tr_k`, read from `FRNodeLayout4`'s H and L regions).
* `out`: on the domain and under the links, the branch outputs `witWords (readW κ L es)` from the
  parse's state, and the witness fits the output format. -/
structure NodeDec4 (nd : XIR) where
  /-- The chain links (S-H2's `E_node` hypotheses at revision 4.1). -/
  Links : Rev4.NodeKind → Log → Log → Proof → Digest → Prop
  /-- The witness read off `f⁽⁰⁾`. -/
  readW : Rev4.NodeKind → Log → Log → Wit
  /-- The decode law. -/
  out : ∀ κ c π L es, Rev4.kindOf4 π = .node κ → InDomE c π L → Links κ L es π c →
    (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList = witWords (readW κ L es) ∧
      (readW κ L es).Fits

/-- **`E4X` on a linked node proof in the domain** is the witness read off `f⁽⁰⁾`. -/
theorem E4X_node_dec {nd : XIR} (D : NodeDec4 nd) {A : Digest → Digest → Signed → Bool}
    {κ : Rev4.NodeKind} {c : Digest} {π : Proof} {L es : Log} (hN : Rev4.kindOf4 π = .node κ)
    (h : InDomE c π L) (hl : D.Links κ L es π c) : E4X nd A c π L = some (D.readW κ L es) := by
  obtain ⟨ho, hf⟩ := D.out κ c π L es hN h hl
  rw [E4X_node hN h, ho, decodeWit_witWords _ hf]

/-- **The node law of `FRSoundness4Frame` for `E4X`**: outside the domain from `NodeSoundLog`
(the search, as `nodeExt_E4`); on the domain from the decode law `D` and `hL`, S-G's side: an
accepted node run on a good log has a transcript `es` meeting the links, and `readW κ L es` is a
witness of the relation (3.x: `rel_readWit`, S-G2/S-G3's link discharge). -/
theorem nodeExt_E4X {nd : XIR} (D : NodeDec4 nd) {Vnode : Rev4.NodeProgs} {vk : Digest}
    {Good : Log → Prop} {S : Submission} (hq : S.qV = Rev4.qV4)
    (hN : Rev4.NodeSoundLog Vnode vk Good (RecursionFast.Rel (S.acc vk)))
    (hL : ∀ κ L c π, Good L → Rev4.kindOf4 π = .node κ → InDomE c π L →
      (Vnode κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ RecursionFast.Rel (S.acc vk) c (D.readW κ L es)) :
    Rev4.NodeExtLog Vnode vk Good (E4X nd S.acc) (RecursionFast.Rel (S.acc vk)) :=
  fun κ L c π hG hk h => by
    by_cases hd : InDomE c π L
    · obtain ⟨es, hl, hr⟩ := hL κ L c π hG hk hd h
      exact ⟨_, E4X_node_dec D hk hd hl, hr⟩
    · obtain ⟨hvk, hw⟩ := hN κ L c π hG hk h
      obtain ⟨w, hs, hr⟩ := search_spec_acc (A := S.acc) (vk := vk)
        (fun _ _ ha => sFits_of_acc (by rw [hq]; decide) ha) hw
      exact ⟨w, by rw [E4X_node_out hk hd, hvk]; exact hs, hr⟩

open scoped NNReal in
/-- **`KS` for revision 4.1's verifier at `S.E = E4X nd S.acc`** (`FRSoundness4Frame.ks4_of`):
the node law from the decode law `D`, `NodeSoundLog` and S-G's links `hL`. -/
theorem ks4_E4X (impl₀ : OpImpl) (implN : Rev4.NodeKind → OpImpl) (cells : Rev4.NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = Rev4.VC4 impl₀ implN cells) (hq : S.qV = Rev4.qV4)
    {nd : XIR} (D : NodeDec4 nd) (hE : S.E = E4X nd S.acc) {ε : ℝ≥0} (μ : Log → ℝ≥0)
    (h0 : μ [] = 0)
    (hstep : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256)
    (hS : Rev4.SegSoundLog (Rev4.VsegC impl₀) vk fun L => L.length ≤ logCap ∧ μ L < 1)
    (hN : Rev4.NodeSoundLog (Rev4.VnodeC implN cells) vk (fun L => L.length ≤ logCap ∧ μ L < 1)
      (RecursionFast.Rel (S.acc vk)))
    (hL : ∀ κ L c π, (L.length ≤ logCap ∧ μ L < 1) → Rev4.kindOf4 π = .node κ → InDomE c π L →
      (Rev4.VnodeC implN cells κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ RecursionFast.Rel (S.acc vk) c (D.readW κ L es)) :
    KS (RecursionFast.Rel (S.acc vk)) (S.V vk) S.E ε S.qV :=
  Rev4.ks4_of impl₀ implN cells S vk hV hq (hE ▸ extOff_E4X nd S.acc) μ h0 hstep hS
    (hE ▸ nodeExt_E4X D hq hN hL)

/-! ## Controls -/

section Controls
variable {A : Digest → Digest → Signed → Bool} (c : Digest) (L : Log)

/-- (+) `E4X` decodes a witness-sending proof (every node branch). -/
theorem E4X_encode (nd : XIR) (w : Wit) :
    E4X nd A c (WitnessSending.encode w) L = WitnessSending.decode (WitnessSending.encode w) :=
  E4X_W (Rev4.kindOf4_encode w)

/-- (−) `E4X` extracts nothing from a bare segment proof (`L32`'s byte), nor from a node byte of
the wrong size. -/
theorem E4X_bad_ctl (nd : XIR) :
    E4X nd A c ⟨#[Rev4.SegKind.L32.byte]⟩ L = none ∧ E4X nd A c ⟨#[Rev4.NodeKind.N4.byte]⟩ L = none :=
  ⟨E4X_bad (by decide), E4X_bad (by decide)⟩

/-- A toy aggregate proof: `'A'`, `k = 1`, `n = 5` (byte 8), the first segment's start byte `7`
(byte 64). -/
def toyA : Proof := ⟨(List.range 96).toArray.map fun i =>
  if i = 0 then 0x41 else if i = 1 then 1 else if i = 8 then 5 else if i = 64 then 7 else 0⟩

/-- (+/−) The aggregate's leaf reads `n` at bytes `8 … 15` (not at `0 … 7`, where `'A'` and `k`
sit) and the start at byte 64 (not 63). -/
theorem aggLeaf_ctl : Rev4.kindOf4 toyA = .agg ∧ Rev4.rdLE64 toyA 8 = 5 ∧ Rev4.rdLE64 toyA 0 ≠ 5 ∧
    (bytesAt toyA 64 32)[0] = 7 ∧ byteAt toyA 63 = 0 := by
  decide +kernel

/-- (+) `E4X` returns the toy aggregate's leaf. -/
theorem E4X_toyA (nd : XIR) : E4X nd A c toyA L = some (aggLeaf toyA) := E4X_agg aggLeaf_ctl.1

/-- (−) **The certificate's current node branch extracts nothing**: with `ndNone`, a node proof in
the domain gives `none` (the revision 4.1 node decoder is missing, `FRX4Prog`'s header). -/
theorem E4X_ndNone_node {κ : Rev4.NodeKind} {π : Proof} (hN : Rev4.kindOf4 π = .node κ)
    (h : InDomE c π L) : E4X ndNone A c π L = none := by
  rw [E4X_node hN h]
  simp [ndNone, semXIR, st1_o]
  rfl

/-- (−) **The decode law is not vacuous**: no `NodeDec4 ndNone` has a linked node input in the
domain (the empty branch outputs nothing, every `witWords` has a tag). -/
theorem not_nodeDec4_ndNone (D : NodeDec4 ndNone) {κ : Rev4.NodeKind} {π : Proof} {es : Log}
    (hN : Rev4.kindOf4 π = .node κ) (h : InDomE c π L) (hl : D.Links κ L es π c) : False := by
  have := (D.out κ c π L es hN h hl).1
  simp only [ndNone, semXIR, runPrims_nil, st1_o, Array.toList_empty] at this
  cases hw : D.readW κ L es <;> rw [hw] at this <;> simp [witWords] at this

/-- (+) A decode law with no linked input is met by every branch (the law constrains only linked
node inputs). -/
def nodeDec4_none (nd : XIR) : NodeDec4 nd :=
  ⟨fun _ _ _ _ _ => False, fun _ _ _ => .leaf 0 0, fun _ _ _ _ _ _ _ h => h.elim⟩

end Controls

end FR.X.X4

end G6_FRX4Ext

section G6_FRXChain4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 2, A.4; stage S-H4, pass 6, item 2).

/-!
# The chain scan at revision 4.1: the targets of an item sequence, the table, `chain_spec4`

3.x's `FRXChainFlock` with the item sequence a parameter `S : Seq` (rev44's `seq4` has 486
Fiat–Shamir items; another revision's sequence is another `S`):

* `fsMsgs4 S`: per Fiat–Shamir position, the π byte range `(o, len)` of the absorbed message, read
  off `phasesOf S` exactly as `FRVIR4.genPhase4` asks (`fieldOffOf S f + phaseOffOf S n f`,
  `j · roundBytes` per round); `none` for a squeeze. Controls at `seq4`: `fsMsgs4_items` (the kinds
  and lengths are `fsItems4`), `fsMsgs4_aligned` (8-byte aligned inside `piSizeOf seq4`).
* `fsQ4 S vk c π p st`: the query at position `p` (A.2); position 0 is the seed
  `seedQ vk c hdr` (`fsQ4_zero`).
* `chTab4 S N`, **`tabW_chTab4`**: the table realises `fsQ4 S` on every tape of a proof of
  `piSizeOf S` bytes whose messages are aligned (`hA`, a decided check per sequence).
* **`chain_spec4`**: on a log with no state hit, the answer at `ansB + 4p` (`p < N`) is the
  first-match chain's (`fmAns`); **`chain_dec4`** for the seed block `seedIR` (`vkOf π`).
* At `seq4`: `nRep4 = 456` (through P1.4's last round, `phStart4 47`), the P1 challenges' words
  **`cbS4 i`** and **`sAt4_words`** (they hold `T4.sAt es i`).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

/-! ## The Fiat–Shamir messages of an item sequence -/

/-- A phase's Fiat–Shamir positions in `S`'s format: the absorbed π range, or `none` for a squeeze. -/
def phaseMsgs4 (S : Seq) (n : ℕ) : Sh → List (Option (ℕ × ℕ))
  | .seed => [some (0, 48)]
  | .absorb f len => [some (fieldOffOf S f + phaseOffOf S n f, len)]
  | .squeezes k _ => List.replicate k none
  | .uni f => [some (fieldOffOf S f + phaseOffOf S n f, uniBytes), none]
  | .rounds f k _ inK => (List.range k).flatMap fun j =>
      [some (fieldOffOf S f + phaseOffOf S n f + j * roundBytes inK, roundBytes inK), none]
  | .queries _ => []

/-- **The Fiat–Shamir messages of `S`** in item order. -/
def fsMsgs4 (S : Seq) : List (Option (ℕ × ℕ)) :=
  ((List.range (phasesOf S).length).zip (phasesOf S)).flatMap fun np => phaseMsgs4 S np.1 np.2.2

/-- A message is 8-byte aligned and inside a proof of `P` bytes. -/
def msgOkB (P : ℕ) : Option (ℕ × ℕ) → Bool
  | some (o, len) => o % 8 == 0 && len % 8 == 0 && decide (o + len ≤ P)
  | none => true

/-- Position 0 is the seed's `hdr` (bytes `0 … 47`), in every sequence. -/
theorem fsMsgs4_zero (S : Seq) : (fsMsgs4 S).getD 0 none = some (0, 48) := by
  have h : (phasesOf S).length = (phasesOf S).length - 1 + 1 := by simp [phasesOf]
  unfold fsMsgs4; rw [h, List.range_succ_eq_map]; rfl

/-- **The query at Fiat–Shamir position `p`** of `S`, the previous answer being `st` (A.2). -/
def fsQ4 (S : Seq) (vk c : Digest) (π : Proof) (p : ℕ) (st : Digest) : ByteArray :=
  match (fsMsgs4 S).getD p none with
  | some (o, len) => if p = 0 then seedQ vk c (π.extract o (o + len))
      else absorbQ st (π.extract o (o + len))
  | none => squeezeQ st

theorem fsQ4_zero (S : Seq) (vk c : Digest) (π : Proof) (st : Digest) :
    fsQ4 S vk c π 0 st = seedQ vk c (π.extract 0 48) := by
  unfold fsQ4; rw [fsMsgs4_zero]; rfl

theorem stateIn_fsQ4 (S : Seq) (vk c : Digest) (π : Proof) {p : ℕ} (hp : 0 < p) (st : Digest) :
    stateIn (fsQ4 S vk c π p st) = some st := by
  unfold fsQ4
  split
  · rw [if_neg (by omega)]; exact stateIn_absorbQ st _
  · exact stateIn_squeezeQ st

/-! ## The table -/

/-- One table entry of the message list `ms`: `tl`, the tape offset of the message, the tag word, `0`. -/
def tabEntM (ms : List (Option (ℕ × ℕ))) (p : ℕ) : List Word :=
  match ms.getD p none with
  | some (o, len) => [toWord (40 + len), toWord (5 + o / 8), tagAbsW, 0]
  | none => [toWord 40, 0, tagSqzW, 0]

/-- One table entry of `S` (`tabEntM` at `fsMsgs4 S`). -/
def tabEnt4 (S : Seq) (p : ℕ) : List Word := tabEntM (fsMsgs4 S) p

/-- **The table** of `S`: entries `0 … N` (`= (List.range (N + 1)).flatMap (tabEnt4 S)`, `chTab4_eq`;
written with `fsMsgs4 S` outside the entries so the compiled table computes it once: INIT, 7 s of
the badge's start-up). -/
def chTab4 (S : Seq) (N : ℕ) : List Word := (List.range (N + 1)).flatMap (tabEntM (fsMsgs4 S))

theorem chTab4_eq (S : Seq) (N : ℕ) : chTab4 S N = (List.range (N + 1)).flatMap (tabEnt4 S) := rfl

theorem tabEnt4_length (S : Seq) (p : ℕ) : (tabEnt4 S p).length = 4 := by
  unfold tabEnt4 tabEntM; split <;> rfl

theorem chTab4_length (S : Seq) (N : ℕ) : (chTab4 S N).length = 4 * (N + 1) := by
  rw [chTab4_eq, List.length_flatMap]
  simp only [tabEnt4_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem chTab4_getD (S : Seq) {N p k : ℕ} (hp : p ≤ N) (hk : k < 4) :
    (chTab4 S N).getD (4 * p + k) 0 = (tabEnt4 S p).getD k 0 :=
  getD_flatMap4 (tabEnt4 S) (tabEnt4_length S) _ p k (by omega) hk

theorem msgOkB_of {S : Seq} {P p o len : ℕ} (hA : (fsMsgs4 S).all (msgOkB P) = true)
    (h : (fsMsgs4 S).getD p none = some (o, len)) : o % 8 = 0 ∧ len % 8 = 0 ∧ o + len ≤ P := by
  have hp : p < (fsMsgs4 S).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h; cases h
  have hm := List.all_eq_true.mp hA _ (List.getElem_mem hp)
  rw [List.getD_eq_getElem _ _ hp] at h
  rw [h] at hm
  simp only [msgOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨hm.1.1, hm.1.2, hm.2⟩

/-- **The table realises `S`'s targets** on every tape of a proof inside which every message of
`S` lies 8-byte aligned (`hA`). -/
theorem tabW_chTab4 (S : Seq) (N : ℕ) (vk c : Digest) (π : Proof) (L : Log) (hπ : π.size < 2 ^ 60)
    (hA : (fsMsgs4 S).all (msgOkB π.size) = true) :
    TabW (extractorInput c π L).toArray (fsQ4 S vk c π) N (chTab4 S N) := by
  refine ⟨chTab4_length S N, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTab4_getD S hpN (by norm_num), tabEnt4, tabEntM]
    split
    · next o len h =>
      have := msgOkB_of hA h
      show (toWord (5 + o / 8)).toNat < 2 ^ 62
      rw [toNat_toWord (by omega)]; omega
    · show (0 : Word).toNat < 2 ^ 62; decide
  · have e0 := chTab4_getD S hpN (k := 0) (by norm_num)
    have e1 := chTab4_getD S hpN (k := 1) (by norm_num)
    have e2 := chTab4_getD S hpN (k := 2) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, e2]
    unfold fsQ4 tabEnt4 tabEntM
    split
    · next o len h =>
      obtain ⟨ho, hl, hol⟩ := msgOkB_of hA h
      rw [if_neg (by omega)]
      have hsz := extract_size π (o := o) (len := len) (by omega)
      refine ⟨by rw [absorbQ_size, hsz]; rfl, by rw [absorbQ_size, hsz]; omega, fun j hj => ?_⟩
      rw [absorbQ_size, hsz] at hj
      rw [absorb_words]
      show _ = if j < 5 then (if j = 0 then tagAbsW else _) else
        (extractorInput c π L).toArray.getD ((toWord (5 + o / 8)).toNat + (j - 5)) 0
      split_ifs with h5 h0
      · rfl
      · rfl
      · rw [toNat_toWord (by omega), getD_toArray, show 5 + o / 8 + (j - 5) = 5 + (o / 8 + (j - 5))
          by omega, tape_getD_proof c π L (by omega), ← List.getD_eq_getElem _ 0,
          show o = 8 * (o / 8) by omega, show 8 * (o / 8) + len = 8 * (o / 8) + 8 * (len / 8) by
          omega, extract_words π (by omega) (by omega), show 8 * (o / 8) / 8 = o / 8 by omega]
    · refine ⟨by rw [squeezeQ_size]; rfl, by rw [squeezeQ_size]; norm_num, fun j hj => ?_⟩
      rw [squeezeQ_size] at hj
      rw [squeeze_words st (by omega), if_pos (show j < 5 by omega)]
      rfl

/-! ## The specification -/

/-- The seed query is 119 bytes. -/
theorem seedQ_size (vk c : Digest) (π : Proof) (h48 : 48 ≤ π.size) :
    (seedQ vk c (π.extract 0 48)).size = 119 := by
  rw [seedQ, ByteArray.size_append, extract_size π (o := 0) (len := 48) (by omega),
    show (bytesOf (tagSeed ++ vk.toList ++ c.toList)).size = 71 by
      simp [bytesOf, ByteArray.size, tagSeed]]

/-- **`chain_spec4`**: on a domain tape of a proof inside which `S`'s messages lie aligned, whose
log has no state hit, for every position `p < N` that the first-match chain of `S`'s targets
answers with `a`, the machine's answer at `ansB + 4p` is `a`'s four words; the chain keeps the
heap outside `[chB, chEnd)`. The seed block `sd` must write the seed's words (`SeedOK`). -/
theorem chain_spec4 (S : Seq) {pL N : ℕ} (hN : N < 2 ^ 9) (vk c : Digest) (π : Proof) (L : Log)
    (hs : 5 + (π.size + 7) / 8 = pL) (h48 : 48 ≤ π.size) (hπ : π.size < 2 ^ 60)
    (hA : (fsMsgs4 S).all (msgOkB π.size) = true)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) {sd : XIR} {st₀ : Digest}
    (hsd : SeedOK sd (extractorInput c π L).toArray (fsQ4 S vk c π 0 st₀))
    (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < N, ∀ a, fmAns (fsQ4 S vk c π) st₀ L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) sd) s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) sd) s).M y = rd s.M y) := by
  have h119 : (fsQ4 S vk c π 0 st₀).size = 119 := by rw [fsQ4_zero]; exact seedQ_size vk c π h48
  obtain ⟨-, hans, hfr⟩ := chainIR_sem c π L hs hq ht hN (tabW_chTab4 S N vk c π L hπ hA) hsd h119
    s hM hsz
  refine ⟨fun p hp a ha m hm => ?_, hfr⟩
  have hsc := scanC_answers (N := N) (st₀ := st₀) (fun p st hp => stateIn_fsQ4 S vk c π hp st)
    hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := N) (st₀ := st₀) (L := L) (T := fsQ4 S vk c π)
    (fun p st hp => stateIn_fsQ4 S vk c π hp st) hS).1
  have hpl : p < (scanC (fsQ4 S vk c π) N st₀ L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQ4 S vk c π) N st₀ L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [hans p hpl m hm, hg]

/-- **The replayed answers for the seed block** `seedIR`: the first-match chain from the seed
`"FRSEED0" ‖ vkOf π ‖ c ‖ hdr`. -/
theorem chain_dec4 (S : Seq) {pL N : ℕ} (hN : N < 2 ^ 9) (c : Digest) (π : Proof) (L : Log)
    (hs : 5 + (π.size + 7) / 8 = pL) (h48 : 48 ≤ π.size) (hπ : π.size < 2 ^ 60)
    (hA : (fsMsgs4 S).all (msgOkB π.size) = true)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (st₀ : Digest) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < N, ∀ a, fmAns (fsQ4 S (vkOf π) c π) st₀ L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) seedIR) s).M
        (ansB + 4 * p + m) = (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) seedIR) s).M y = rd s.M y) :=
  chain_spec4 S hN (vkOf π) c π L hs h48 hπ hA hq ht hS
    (by rw [fsQ4_zero]; exact seedOK_seedIR4 c π L h48) s hM hsz

/-! ## At `seq4`: the controls, the positions replayed, the P1 challenges -/

/-- Control: `seq4` has 486 Fiat–Shamir positions (revision 4.4.1: the cap check's four after `Pf`). -/
theorem fsMsgs4_length : (fsMsgs4 seq4).length = 486 := by decide +kernel

/-- The item kind of a message entry (position `0` is the seed). -/
def msgItem4 : ℕ → Option (ℕ × ℕ) → Item
  | 0, _ => .seed
  | _ + 1, some (_, len) => .absorb len
  | _ + 1, none => .squeeze

/-- **Control: the kinds and lengths are `seq4`'s Fiat–Shamir items** (`T4.fsItems4`). -/
theorem fsMsgs4_items :
    (List.range 486).map (fun p => msgItem4 p ((fsMsgs4 seq4).getD p none)) = fsItems4 := by
  rw [← fsMsgs4_length, map_range_getD]; decide +kernel

/-- **Control: every message of `seq4` is aligned and inside a proof of `piSizeOf seq4` bytes.** -/
theorem fsMsgs4_aligned : (fsMsgs4 seq4).all (msgOkB (piSizeOf seq4)) = true := by
  rw [piSizeOf_seq4, seq4_eq]; decide +kernel

/-- The positions replayed at `seq4`: through P1.4's last round. -/
def nRep4 : ℕ := 456

/-- Control: P1.4 (phase 46) starts at position 448 and has 4 rounds (8 items), and the final
message's absorb (phase 47) is at `nRep4`: every P1.i challenge (`T4.sAt es i l`, position
`phStart4 (26 + 5i) + 2l + 1`, `l < 4` for `i ≥ 1`, `l < 6` for `i = 0`) sits below `nRep4`. -/
theorem nRep4_ctl : phStart4 46 = 448 ∧ phStart4 47 = nRep4 ∧
    (List.range 5).map (fun i => phStart4 (26 + 5 * i)) = [332, 375, 402, 426, 448] := by
  simp only [phStart4, fsStarts4_eq, nRep4]; decide

/-- **The P1.i challenges' words** in the chain's answers: `ansB + 4 (phStart4 (26 + 5i) + 1)`. -/
def cbS4 (i : ℕ) : ℕ := ansB + 4 * (phStart4 (26 + 5 * i) + 1)

/-- The challenges' words are `T4.sAt` (3.x's `sAt_words` at `phStart4`). -/
theorem sAt4_words {M : Mem} {es : Log} {i ℓ : ℕ}
    (h : ∀ v < ℓ, ∀ m < 4, rd M (ansB + 4 * (phStart4 (26 + 5 * i) + 2 * v + 1) + m) =
      (packBytes (ansAt es (phStart4 (26 + 5 * i) + 2 * v + 1)).toList).getD m 0) :
    ∀ v < ℓ, rdK M (cbS4 i + 8 * v) = T4.sAt es i v := by
  intro v hv
  rw [T4.sAt, kAt]
  refine rdK_of_words fun m hm => ?_
  rw [← h v hv m hm, cbS4]
  congr 1
  ring

/-- The challenges' region at every level: inside the answers, above the basis table, below the
levels' regions (`map4`'s `fb = 2^24`), and their positions below `nRep4`. -/
theorem cbS4_bounds {i : ℕ} (hi : i < 5) {ℓ : ℕ} (hℓ : ℓ ≤ (if i = 0 then 6 else 4)) :
    2 ^ 20 + 800 ≤ cbS4 i ∧ cbS4 i + 8 * ℓ + 4 ≤ chEnd ∧ phStart4 (26 + 5 * i) + 2 * ℓ ≤ nRep4 := by
  have e := nRep4_ctl.2.2
  simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.cons.injEq] at e
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := e
  simp only [cbS4, ansB, chEnd, nRep4]
  interval_cases i <;> simp_all <;> omega

/-! ## Controls -/

/-- (−) **`msgOkB` rejects** a misaligned message and one past the proof's end; (+) it accepts the
seed's `hdr`. -/
theorem msgOkB_ctl : msgOkB 876304 (some (4, 8)) = false ∧ msgOkB 100 (some (96, 8)) = false ∧
    msgOkB 876304 (some (0, 48)) = true := by decide

/-- (value) **`seq4`'s targets at positions 2 and 3**: `cap₀`'s absorb of π's bytes
`20,896 … + 16,384`, then a squeeze (`Z1`'s first). -/
theorem fsMsgs4_ctl : (fsMsgs4 seq4).getD 2 none = some (20896, 16384) ∧
    (fsMsgs4 seq4).getD 3 none = none := by
  rw [seq4_eq]; decide +kernel

/-- (+/−) **The queries**: position 2 absorbs `cap₀` into the state, position 3 squeezes it (and
is not an absorb). -/
theorem fsQ4_ctl (vk c : Digest) (π : Proof) (st : Digest) :
    fsQ4 seq4 vk c π 2 st = absorbQ st (π.extract 20896 (20896 + 16384)) ∧
    fsQ4 seq4 vk c π 3 st = squeezeQ st := by
  constructor <;> unfold fsQ4 <;> simp only [fsMsgs4_ctl] <;> rfl

/-- (value) **The table's entry for `cap₀`**: the query length `40 + 16,384`, the tape word
`5 + 20,896/8`, the absorb tag. -/
theorem tabEnt4_ctl : tabEnt4 seq4 2 = [toWord (40 + 16384), toWord (5 + 20896 / 8), tagAbsW, 0] := by
  unfold tabEnt4 tabEntM; simp only [fsMsgs4_ctl]

/-- (value/−) **The P1 challenges' words** per level; they differ between levels. -/
theorem cbS4_ctl : (List.range 5).map cbS4 = [ansB + 1332, ansB + 1504, ansB + 1612, ansB + 1708,
    ansB + 1796] ∧ cbS4 4 ≠ cbS4 3 := by
  simp only [cbS4, phStart4, fsStarts4_eq]; decide +kernel

end FR.X

end G6_FRXChain4

section G6_FRXDec4F0

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 steps 2–4; stage S-H4, pass 6, items 1–2
-- composed, item 4's decode half).

/-!
# The node branch's decode at a revision 4.1 node kind (`decF04`)

3.x's `FRXNode.decF0` at a node kind `κ`, on revision 4.4.1's format (`seq4`, `piSizeOf seq4 = 876,304`):

`idxIR4 memX4 pL4 ; readK4 0 ; chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR ; decLevels4 κ`

(the log index at `memX4`, level 0's word at `map4.l0.cb`, the Fiat–Shamir replay with the answers
at `ansB`, the five levels). The format enters through `pL4` (the log's tape word), `cw4 i` (the
caps' tape words), `tw4` (the final message's tape word) and `cbS4 i` (the P1 challenges in the
chain's answers); `fmt4_ctl` checks them against `fsMsgs4 seq4` at the cap and final absorbs.

**`decF04_sem`**: on a domain tape of a node proof of kind `κ` whose log has no state hit, if the
log's transcript `es` is the first-match chain the replay reads (`fmAns … = ansAt es`), its cap and
final absorbs are π's fields (`capPi4`, `finPi4`), and every level's word is close with
`A_c = jointAgree`, then level 0's rows `1 … 7` sit at `map4.l0.ob` as `msgOf κ L es 0 (1 + q)`.

**`kindNd4`** reads the node byte (tape word 5's low byte) into two flags for the branch's `ite`
(`N2`: `m = 31`; `N4`: `m = 32`; `N8` shares `N4`'s ladder, `decLevels4_m`).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

attribute [local irreducible] entryK storeM runPrims

/-! ## Main's format at `seq4` -/

/-- The log's tape word: `5 + ⌈|π|/8⌉` at `|π| = piSizeOf seq4`. -/
def pL4 : ℕ := 5 + (piSizeOf seq4 + 7) / 8

/-- Level `i`'s cap in π: the caps field, then the earlier levels' caps. -/
def capFO4 (i : ℕ) : ℕ := fieldOffOf seq4 fCaps + capOff4 seq4 i

/-- **Cap entry `e` of level `i`** as π carries it. -/
def capPi4 (i : ℕ) (π : Proof) (e : ℕ) : Digest := bytesAt π (capFO4 i + 32 * e) 32

/-- Its tape word. -/
def cw4 (i : ℕ) : ℕ := 5 + capFO4 i / 8

/-- The final message in π (field `fFinal`). -/
def finFO4 : ℕ := fieldOffOf seq4 fFinal

/-- **The final message's element `x`** as π carries it. -/
def finPi4 (π : Proof) (x : ℕ) : K := chK (bytesAt π (finFO4 + 32 * x) 32)

/-- Its tape word. -/
def tw4 : ℕ := 5 + finFO4 / 8

/-- (value) The format's numbers at `seq4`. -/
theorem fmt4_vals : pL4 = 109543 ∧ (List.range 5).map capFO4 = [20896, 37280, 45472, 53664, 61856] ∧
    finFO4 = 70048 ∧ piSizeOf seq4 = 876304 := by
  simp only [pL4, finFO4, piSizeOf_seq4]
  rw [seq4_eq]
  decide +kernel

/-- **Control: the offsets are the absorbs'**: `fsMsgs4 seq4` absorbs π's bytes
`capFO4 i … + 32·2^cap` at the cap positions (`T4.capPos i`) and `finFO4 … + 32·2^7` at the
final message (`phStart4 47`). -/
theorem fmt4_ctl : (List.range 5).map (fun i => (fsMsgs4 seq4).getD (T4.capPos i) none) =
      (List.range 5).map (fun i => some (capFO4 i, 32 * 2 ^ (seq4.lv i).cap)) ∧
    (fsMsgs4 seq4).getD (phStart4 47) none = some (finFO4, 32 * 2 ^ 7) := by
  simp only [T4.capPos, phStart4, fsStarts4_eq, capFO4, finFO4]
  rw [seq4_eq]
  decide +kernel

/-- The caps' depths do not depend on the kind. -/
theorem lv_cap4 (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    (Snd.CKind.lv κ i).cap = if i = 0 then 9 else 8 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> rfl

/-! ## The tape at the format's fields -/

section Tape

variable (c : Digest) (π : Proof) (L : Log)

/-- **The tape at a cap entry** of level `i ≤ 4` at `seq4`'s offsets. -/
theorem tape_cap4 (hps : π.size = piSizeOf seq4) {i e m : ℕ} (hi : i < 5)
    (he : e < 2 ^ (if i = 0 then 9 else 8)) (hm : m < 4) :
    (tp c π L).getD (cw4 i + 4 * e + m) 0 = (packBytes (capPi4 i π e).toList).getD m 0 := by
  obtain ⟨-, hv, -, hs⟩ := fmt4_vals
  rw [tp, getD_toArray, cw4, capPi4]
  have e0 : capFO4 i % 8 = 0 ∧ capFO4 i + 32 * 2 ^ (if i = 0 then 9 else 8) ≤ 70048 := by
    simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.cons.injEq] at hv
    interval_cases i <;> simp_all
  have hp : (if i = 0 then 9 else 8) ≤ 9 := by split_ifs <;> omega
  have hp2 : 2 ^ (if i = 0 then 9 else 8) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hp
  exact tape_capL c π L e0.1 (by rw [hps, hs]; omega) hm

/-- **The tape at the final message**: the two tape pairs of element `x < 128` are `finPi4`. -/
theorem tapeF_fin4 (hps : π.size = piSizeOf seq4) {x : ℕ} (hx : x < 128) :
    (⟨tapeF (tp c π L) (tw4 + 4 * x), tapeF (tp c π L) (tw4 + 4 * x + 2)⟩ : K) = finPi4 π x := by
  obtain ⟨-, -, hf, hs⟩ := fmt4_vals
  have T : ∀ m < 4, (tp c π L).getD (tw4 + 4 * x + m) 0 =
      (packBytes (bytesAt π (finFO4 + 32 * x) 32).toList).getD m 0 := fun m hm => by
    rw [tp, getD_toArray]
    exact tape_capL c π L (off := finFO4) (by rw [hf]) (by rw [hps, hs, hf]; omega) hm
  rw [finPi4, chK_words, tapeF, tapeF, ← T 0 (by norm_num), ← T 1 (by norm_num),
    ← T 2 (by norm_num), ← T 3 (by norm_num)]
  rfl

end Tape

/-! ## The kind dispatch -/

/-- The flag `N2`. -/ def rF2 : ℕ := 246
/-- The flag `N4`. -/ def rF4 : ℕ := 247

/-- **The node byte's flags**: `rF2 := (byte = N2)`, `rF4 := (byte = N4)` (tape word 5's low byte). -/
def kindNd4 : XIR :=
  .seq (readAt rB0 5) (.blk (X4.normPs ++ X4.eqPs rF2 0x4D ++ X4.eqPs rF4 0x4E))

theorem wf_kindNd4 : WF kindNd4 := by
  simp +decide only [kindNd4, readAt, X4.normPs, X4.eqPs, WF, Prim.dst, rA, rB0, rF2, rF4, rK,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

theorem lo_kindNd4 : Lo kindNd4 := by
  simp +decide only [kindNd4, readAt, X4.normPs, X4.eqPs, Lo, Prim.dst, rA, rB0, rF2, rF4, rK, regs,
    List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

/-- **The node byte's flags** on a nonempty proof: `rF2` is `1` iff the first byte is `N2`'s,
`rF4` iff it is `N4`'s; the heap and the output are kept. -/
theorem kindNd4_sem (c : Digest) (π : Proof) (L : Log) (hπ : 0 < π.size) (s : St) (hM : Inv s.M) :
    rd (semXIR (tp c π L) kindNd4 s).M rF2 = (if byteAt π 0 = NodeKind.N2.byte then 1 else 0) ∧
    rd (semXIR (tp c π L) kindNd4 s).M rF4 = (if byteAt π 0 = NodeKind.N4.byte then 1 else 0) ∧
    (∀ y, regs ≤ y → rd (semXIR (tp c π L) kindNd4 s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) kindNd4 s).M ∧ (semXIR (tp c π L) kindNd4 s).o = s.o ∧
    (semXIR (tp c π L) kindNd4 s).M.size = s.M.size := by
  have hs := hM.1
  simp only [regs] at hs
  have r5 := rd_readAt (tp c π L) s hM (d := rB0) (pos := 5) (by decide) (by norm_num)
  have hM1 := inv_sem (tp c π L) (P := readAt rB0 5) (by simp +decide [readAt, WF, Prim.dst, rA, rB0]) hM
  have z1 := size_sem (tp c π L) (readAt rB0 5) s
  have o1 : (semXIR (tp c π L) (readAt rB0 5) s).o = s.o := by simp [readAt, semXIR]
  have b2 := X4.bOf_tape c π L hπ 0x4D (by decide)
  have b4 := X4.bOf_tape c π L hπ 0x4E (by decide)
  have fr := hframe (tp c π L) kindNd4 s lo_kindNd4
  have e2 : ((byteAt π 0).toNat = (0x4D : Word).toNat) ↔ byteAt π 0 = NodeKind.N2.byte := by
    rw [show NodeKind.N2.byte = 0x4D from rfl, ← UInt8.toNat_inj]; rfl
  have e4 : ((byteAt π 0).toNat = (0x4E : Word).toNat) ↔ byteAt π 0 = NodeKind.N4.byte := by
    rw [show NodeKind.N4.byte = 0x4E from rfl, ← UInt8.toNat_inj]; rfl
  rw [kindNd4, semXIR_seq]
  rw [kindNd4, semXIR_seq] at fr
  generalize semXIR (tp c π L) (readAt rB0 5) s = s1 at r5 hM1 z1 o1 fr
  have hs1 : 256 ≤ s1.M.size := by rw [z1]; omega
  refine ⟨?_, ?_, ?_, inv_sem _ (by simp +decide only [X4.normPs, X4.eqPs, WF, Prim.dst, rB0, rF2, rF4,
    rK, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]) hM1, o1, by rw [size_sem, z1]⟩
  · rw [X4.semXIR_blk4]
    simp only [X4.runPrims_append]
    simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
      [rd_runPrims_of_not_writes, X4.rd_eqPs, X4.rd_normPs]
    rw [r5]
    have := b2; simp only [X4.bOf, tp] at this ⊢
    rw [this]; exact if_congr e2 rfl rfl
  · rw [X4.semXIR_blk4]
    simp only [X4.runPrims_append]
    rw [X4.rd_eqPs _ _ (by decide) (by decide) (by simp only [size_runPrims]; omega)]
    simp (disch := first | decide | omega | (simp only [size_runPrims]; omega)) only
      [rd_runPrims_of_not_writes, X4.rd_normPs]
    rw [r5]
    have := b4; simp only [X4.bOf, tp] at this ⊢
    rw [this]; exact if_congr e4 rfl rfl
  · exact fr

/-- The branch of a node kind: `N2`'s, `N4`'s or `N8`'s program. -/
def pickNd (κ : NodeKind) (P2 P4 P8 : XIR) : XIR :=
  match κ with
  | .N2 => P2
  | .N4 => P4
  | .N8 => P8

/-- **The dispatch on the node byte**. -/
def ndK4 (P2 P4 P8 : XIR) : XIR := .seq kindNd4 (.ite rF2 P2 (.ite rF4 P4 P8))

/-- On a node proof of kind `κ`, the dispatch runs `κ`'s branch after the flags. -/
theorem ndK4_sem (c : Digest) (π : Proof) (L : Log) {κ : NodeKind} (hb : byteAt π 0 = κ.byte)
    (hπ : 0 < π.size) (P2 P4 P8 : XIR) (s : St) (hM : Inv s.M) :
    semXIR (tp c π L) (ndK4 P2 P4 P8) s = semXIR (tp c π L) (pickNd κ P2 P4 P8) (semXIR (tp c π L) kindNd4 s) := by
  obtain ⟨f2, f4, -⟩ := kindNd4_sem c π L hπ s hM
  rw [ndK4, semXIR_seq]
  generalize semXIR (tp c π L) kindNd4 s = s1 at f2 f4
  have h42 : NodeKind.N4.byte ≠ NodeKind.N2.byte := by decide
  have h82 : NodeKind.N8.byte ≠ NodeKind.N2.byte := by decide
  have h84 : NodeKind.N8.byte ≠ NodeKind.N4.byte := by decide
  have h24 : NodeKind.N2.byte ≠ NodeKind.N4.byte := by decide
  have o1 : (1 : Word) ≠ 0 := by decide
  cases κ <;> simp only [semXIR, f2, f4, hb, pickNd, if_true, if_false, h42, h82, h84, h24, o1,
    if_pos, if_neg, not_false_eq_true]

/-! ## The decode at a node kind -/

/-- **The decode at node kind `κ`**: the index, level 0's read, the chain, the five levels. -/
def decF04 (κ : NodeKind) : XIR :=
  .seq (idxIR4 memX4 pL4) (.seq (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128)
    (.seq (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) (decLevels4 (.node κ) pL4 cw4 cbS4 tw4)))

/-- **The decode at a node kind leaves `f⁽⁰⁾`'s rows `1 … 7`** (BLUEPRINT §6.2 steps 2–4; 3.x's
`decF0_sem`): on a domain tape of a proof of `piSizeOf seq4` bytes whose log has no state hit, if
the log's transcript `es` is the first-match chain the replay reads, its cap absorbs are π's caps
(`capPi4`), its final absorb is π's final field (`finPi4`), and every level's word is close with
`A_c = jointAgree`, then after `decF04 κ` the heap at `map4.l0.ob + 2^(mLog 0 + 1) q + 2x` holds,
as an `F` value, coefficient `x` of row `1 + q` of `f⁽⁰⁾` (`msgOf κ L es 0`). -/
theorem decF04_sem (κ : NodeKind) (c : Digest) (π : Proof) (L : Log) (hD : Dom4 pL4 c π L)
    (hps : π.size = piSizeOf seq4) (hS : ¬ StateHit L) (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep4, fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap : ∀ i < 5, ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, T4.capDig es i e = capPi4 i π e)
    (hfin : ∀ x < 2 ^ T4.mLog (.node κ) 4, T4.finalAt es x = finPi4 π x)
    (hfar : ∀ i < 5, ¬ T4.farL (.node κ) L es i)
    (hA : ∀ i < 5, T4.consSet (.node κ) L es i =
      jointAgree (T4.wordK (.node κ) L es i) (T4.decodeL (.node κ) L es i))
    (s : St) (hM : Inv s.M) (hsz : memX4 + L.length + L.length ≤ s.M.size) :
    ∀ q < 7, ∀ x < 2 ^ T4.mLog (.node κ) 0,
      algebraMap F K (rdF (semXIR (tp c π L) (decF04 κ) s).M
        (map4.l0.ob + 2 * 2 ^ T4.mLog (.node κ) 0 * q + 2 * x)) = T4.msgOf (.node κ) L es 0 (1 + q) x := by
  set I := tp c π L
  obtain ⟨hpL, hcv, hfv, hsv⟩ := fmt4_vals
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  have hps' : π.size = 876304 := hps.trans hsv
  have hpL60 : pL4 ≤ 2 ^ 60 := by rw [hpL]; norm_num
  have hb : regs ≤ memX4 := by simp only [regs]; omega
  have hb2 : memX4 ≤ 2 ^ 60 := by omega
  -- the tape at the caps
  have hcapT : ∀ i < 5, ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, ∀ m < 4,
      I.getD (cw4 i + 4 * e + m) 0 = (packBytes (T4.capDig es i e).toList).getD m 0 :=
    fun i hi e he m hm => by
      rw [hcap i hi e he]
      exact tape_cap4 c π L hps hi (by rw [← lv_cap4 (.node κ) hi]; exact he) hm
  have hcw : ∀ i < 5, cw4 i + 4 * 2 ^ (Snd.CKind.lv (.node κ) i).cap < 2 ^ 62 := fun i hi => by
    rw [lv_cap4 (.node κ) hi]
    simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.cons.injEq] at hcv
    simp only [cw4]
    interval_cases i <;> simp_all
  -- the index
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hb hb2 hpL60 c π L hD.hs hD.hq hD.ht s hM hsz
  have hM1 : Inv (semXIR I (idxIR4 memX4 pL4) s).M := inv_sem _ (wf_idxIR4 memX4 pL4) hM
  have z1 := size_sem I (idxIR4 memX4 pL4) s
  rw [decF04, semXIR_seq, semXIR_seq, semXIR_seq]
  generalize semXIR I (idxIR4 memX4 pL4) s = s1 at r1 r2 r3 hM1 z1
  have hX : Sorted4 pL4 I L (fun a => rd s1.M (memX4 + a)) := ⟨r1, r2, r3⟩
  have hsz1 : memX4 ≤ s1.M.size := by rw [z1]; omega
  -- level 0's read
  obtain ⟨w1, w2, w3, hM2⟩ := readK4_sem hpL60 hD hX s1 hM1 (fun _ _ => rfl) hsz1 (κ := .node κ)
    (es := es) (i := 0) (cw := cw4 0) (sb := map4.l0.cb) (nw := 128) (by norm_num) (hcw 0 (by norm_num))
    (hcapT 0 (by norm_num)) (by rw [(lv04_nums κ).2.2.1]) (by norm_num)
    (by have := (lv04_nums κ).1; omega) (by simp only [regs]; omega)
  have z2 := size_sem I (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) s1
  generalize semXIR I (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) s1 = s2 at w1 w2 w3 hM2 z2
  have hsz2 : memX4 ≤ s2.M.size := z2 ▸ hsz1
  -- the chain
  obtain ⟨ch1, ch2⟩ := chain_dec4 seq4 (N := nRep4) (by decide) c π L hD.hs (by omega) (by omega)
    (by rw [hps]; exact fsMsgs4_aligned) hD.hq hD.ht hS st₀ s2 hM2 (by simp only [chEnd]; omega)
  have hM3 : Inv (semXIR I (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) s2).M := inv_sem _
    (wf_chainIR pL4 nRep4 _ (wf_sdList _) (noWrite_seedIR (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))) hM2
  have z3 := size_sem I (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) s2
  generalize semXIR I (chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR) s2 = s3 at ch1 ch2 hM3 z3
  have kc : ∀ y, chEnd ≤ y → rd s3.M y = rd s2.M y := fun y hy =>
    ch2 y (by simp only [regs, chEnd] at hy ⊢; omega) (.inr hy)
  have hXs3 : ∀ a < L.length, rd s3.M (memX4 + a) = rd s1.M (memX4 + a) := fun a ha =>
    (kc _ (by simp only [chEnd]; omega)).trans (w2 a ha)
  have hW3 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv (.node κ) 0).logN) (r : Fin (Snd.CKind.lv (.node κ) 0).rows),
      rdF s3.M (map4.l0.cb + 128 * j + 2 * r) = T4.wordOf (.node κ) L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← w1 j hj r]
    exact rdF_eq (kc _ (by simp only [chEnd]; omega)) (kc _ (by simp only [chEnd]; omega))
  have hS3 : ∀ i < 5, ∀ v < (Snd.CKind.lv (.node κ) i).ell, rdK s3.M (cbS4 i + 8 * v) = T4.sAt es i v := by
    intro i hi
    refine sAt4_words fun v hv m hm => ?_
    have hl : (Snd.CKind.lv (.node κ) i).ell ≤ (if i = 0 then 6 else 4) := by
      rcases κ with _ | _ | _ <;> interval_cases i <;> decide
    have hp := (cbS4_bounds hi hl).2.2
    exact ch1 _ (by omega) _ (hfm _ (by omega)) m hm
  -- the five levels
  have hfinT : ∀ x < 2 ^ T4.mLog (.node κ) 4,
      T4.finalAt es x = ⟨tapeF I (tw4 + 4 * x), tapeF I (tw4 + 4 * x + 2)⟩ := fun x hx => by
    have : 2 ^ T4.mLog (.node κ) 4 ≤ 2 ^ 7 := (msg4_four_params (.node κ)).2.2
    rw [hfin x hx, tapeF_fin4 c π L hps (by omega)]
  exact (decLevels4_sem hpL60 hD hX s3 hM3 (z3 ▸ hsz2) hXs3 hW3
    (fun i hi1 hi => hcw i (by omega)) (fun i hi1 hi => hcapT i (by omega))
    (fun i hi => by
      have hl : (Snd.CKind.lv (.node κ) i).ell ≤ (if i = 0 then 6 else 4) := by
        rcases κ with _ | _ | _ <;> interval_cases i <;> decide
      obtain ⟨b1, b2, -⟩ := cbS4_bounds hi hl
      exact ⟨by omega, by simp only [chEnd] at b2; omega⟩)
    hS3 hfinT (by simp only [tw4]; omega) hfar hA).1

/-! ## Well formed, loop bounds, cost, output, size -/

theorem wf_seedIR4 : WF seedIR ∧ ¬ Writes seedIR rCC ∧ ¬ Writes seedIR rCn5 :=
  ⟨wf_sdList _, noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem wf_decF04 (κ : NodeKind) : WF (decF04 κ) :=
  ⟨wf_idxIR4 memX4 pL4, wf_readK4 .., wf_chainIR pL4 nRep4 _ wf_seedIR4.1 wf_seedIR4.2.1,
    wf_decLevels4 ..⟩

theorem outs_decF04 (κ : NodeKind) (t : ℕ) : outs (decF04 κ) t = 0 := by
  rw [decF04, outs, outs, outs, outs_idxIR4, outs_readK4, outs_decLevels4,
    outs_chainIR pL4 nRep4 t _ (sd := seedIR) (outs_sdList t _)]

/-- **The decode's loop bounds** on every domain tape of a proof of `piSizeOf seq4` bytes: the
index and the chain count at most `|L| ≤ t/5` entries and the log's words; the rest has no tape
loop. -/
theorem safe_decF04 (κ : NodeKind) (c : Digest) (π : Proof) (L : Log) (hps : π.size = piSizeOf seq4)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length (decF04 κ) := by
  have hs : 5 + (π.size + 7) / 8 = pL4 := by rw [hps]; rfl
  have hpL : pL4 = 109543 := fmt4_vals.1
  exact .seq (safe_idxIR4 memX4 pL4 (by omega) (tape_count_le4 c π L hs ht))
    (.seq (safe_of_noLoopT (noLoopT_readK4 ..))
      (.seq (safe_chainIR c π L hs hq ht nRep4 _ (noLoopT_sdList _) wf_seedIR4.1 wf_seedIR4.2.2)
        (safe_of_noLoopT (noLoopT_decLevels4 ..))))

/-- The decode's cost: the index, level 0's read, the chain, the five levels. -/
theorem cost_decF04_eq (κ : NodeKind) (t : ℕ) : cost (decF04 κ) t = (2592 + t / 5 * 11871) +
    cost (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) t +
    (34 + 9 * (4 * (nRep4 + 1)) + cost seedIR t + t / 5 * 24 + t * 179) +
    cost (decLevels4 (.node κ) pL4 cw4 cbS4 tw4) t + 3 := by
  rw [decF04, cost, cost, cost, cost_idxIR4, cost_chainIR, chTab4_length]
  ring

/-- **The decode's cost** at each node kind: `≤ 27,118,215,163,902 + 2,558 t` at `N2`
(`m = 31`) and `≤ 108,136,600,478,701 + 2,558 t` at `N4`, `N8` (`m = 32`): the five levels
(`cost_decLevels4`), level 0's read (`≤ 85,731,573,774`, `m = 32`'s), and `19,457` for the
index's and the chain's constants, the seed block and the sequencing. -/
theorem cost_le_decF04 (t : ℕ) :
    cost (decF04 .N2) t ≤ 27032483570671 + 85731573774 + 19457 + 2558 * t ∧
    cost (decF04 .N4) t ≤ 108050868885470 + 85731573774 + 19457 + 2558 * t ∧
    cost (decF04 .N8) t ≤ 108050868885470 + 85731573774 + 19457 + 2558 * t := by
  have hs := cost_seedIR t
  obtain ⟨d2, d4, d8⟩ := cost_decLevels4 pL4 cw4 cbS4 tw4 t
  have r : ∀ κ : NodeKind, cost (readK4 pL4 (.node κ) 0 (cw4 0) map4.l0.cb 128) t ≤ 85731573774 := by
    intro κ
    rw [cost_readK4 _ _ (by norm_num) _ _ _ _ (by norm_num)]
    cases κ <;> decide
  have h5 : t / 5 * 11871 + t / 5 * 24 ≤ 2379 * t := by omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [cost_decF04_eq] <;>
    [(rw [d2]; have := r .N2); (rw [d4]; have := r .N4); (rw [d8]; have := r .N8)] <;>
    simp only [nRep4] at * <;> omega

/-! ## Controls -/

/-- (−) **The cap offsets use each level's cap depth**: level 1's cap starts `32·2^9` bytes after
level 0's (whose cap has `2^9` entries), not `32·2^8`. -/
theorem capFO4_ctl : capFO4 1 = capFO4 0 + 32 * 2 ^ 9 ∧ capFO4 1 ≠ capFO4 0 + 32 * 2 ^ 8 := by
  have h := fmt4_vals.2.1
  simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.cons.injEq] at h
  omega

/-- A toy proof whose first byte is `b`. -/
def toyB (b : UInt8) : Proof := ⟨#[b]⟩

/-- (+/−) **The dispatch reads the node byte**: on `N2`'s byte `rF2` is set and `rF4` is not; on
`N4`'s byte the reverse; (+) `pickNd` runs the kind's branch. -/
theorem kindNd4_ctl (c : Digest) (L : Log) (s : St) (hM : Inv s.M) (P2 P4 P8 : XIR) :
    rd (semXIR (tp c (toyB 0x4D) L) kindNd4 s).M rF2 = 1 ∧
    rd (semXIR (tp c (toyB 0x4D) L) kindNd4 s).M rF4 = 0 ∧
    rd (semXIR (tp c (toyB 0x4E) L) kindNd4 s).M rF2 = 0 ∧
    rd (semXIR (tp c (toyB 0x4E) L) kindNd4 s).M rF4 = 1 ∧
    pickNd .N8 P2 P4 P8 = P8 := by
  have b2 : byteAt (toyB 0x4D) 0 = 0x4D := rfl
  have b4 : byteAt (toyB 0x4E) 0 = 0x4E := rfl
  obtain ⟨a1, a2, -⟩ := kindNd4_sem c (toyB 0x4D) L (by decide) s hM
  obtain ⟨c1, c2, -⟩ := kindNd4_sem c (toyB 0x4E) L (by decide) s hM
  rw [a1, a2, c1, c2, b2, b4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- (−) **The decode is the kind's**: `N2`'s decode is not `N4`'s (the ladders differ). -/
theorem decF04_ctl : decF04 .N2 ≠ decF04 .N4 := fun h => by
  have e2 := cost_decF04_eq .N2 0
  have e4 := cost_decF04_eq .N4 0
  rw [h] at e2
  rw [e2, (cost_decLevels4 pL4 cw4 cbS4 tw4 0).2.1] at e4
  rw [(cost_decLevels4 pL4 cw4 cbS4 tw4 0).1] at e4
  rw [cost_readK4 _ _ (by norm_num) _ _ _ _ (by norm_num),
    cost_readK4 _ _ (by norm_num) _ _ _ _ (by norm_num)] at e4
  revert e4; decide

end FR.X

end G6_FRXDec4F0
