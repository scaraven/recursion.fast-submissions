-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11 … B-15; §6.2 step 1, §6.4; stage S-H3).
import FRXSpec
import FRVerifier4

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

The memory (`memX = 2^26`, `mpwX = 3`) and the fuel (`fuel t = 3·2^46 + 2^13 t`, claim.json) are
3.x's; a node decoder at `m = 32` holds `f⁽⁰⁾`'s `2^25` cells and may need a larger `mem`.
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
def szPs : List Prim := [.const rK (BitVec.ofNat 64 798192), .op .eq rIsSz rLen rK]

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
  /-- Its cost is within `decBudget`. -/
  cost : ∀ t, cost nd t ≤ decBudget t
  /-- It outputs at most `outCap` words. -/
  outs : ∀ t, outs nd t ≤ outCap
  /-- It compiles to at most `2^19` statements. -/
  size : sizeIR nd ≤ 2 ^ 19

/-- The program with the node branch `nd`. -/
def ext4With (nd : XIR) : XProg := toProg memX mpwX (ext4IRWith nd)

/-- **The node branch delivered so far**: none (no output). -/
def ndNone : XIR := .blk []

theorem decOk4_ndNone : DecOk4 ndNone where
  wf := by simp [ndNone, WF]
  safe := fun _ _ _ _ _ _ => .blk _
  cost := fun t => by simp [ndNone, cost, blkSteps, decBudget, fuelBase, fuelPerWord]; omega
  outs := fun t => by simp [ndNone, outs]
  size := by simp [ndNone, sizeIR, blkSteps]

/-- **The revision 4.1 extractor program** `ext4 := toProg 2^26 3 (ext4IRWith ndNone)`. -/
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

/-- **The fuel covers the program** whenever the node branch is within `decBudget`. -/
theorem fuel_covers4 {nd : XIR} (h : ∀ t, cost nd t ≤ decBudget t) (t : ℕ) :
    memX + mpwX * t + cost (ext4IRWith nd) t + 8 ≤ fuel t := by
  have := h t
  have := cost_ext4IRWith nd t
  simp only [memX, mpwX, fuel, fuelBase, fuelPerWord, decBudget] at *
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
    rd (runPrims szPs M) rIsSz = isW (rd M rLen) (BitVec.ofNat 64 798192) := by
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
    rd (semXIR I parse4 s).M rIsSz = isW (I.getD 4 0) (BitVec.ofNat 64 798192) := by
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
