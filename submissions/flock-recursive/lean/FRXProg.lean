-- New for `flock-recursive` (BLUEPRINT §6.2, §6.4; stage S-H2, track L-ext).
import FRXDsl
import FRFormat

/-!
# The extractor program `ext`

BLUEPRINT §6.2 step 1 (parse) and the frame every later step runs in.

`extIRWith dec` reads the proof's length `|π|` (tape word 4) and its first byte (the low byte of
tape word 5) and branches as `kindOf` does (`FRFormat`):

* a first byte that is not a kind byte (`'L'`, `'P'`, `'N'`): the **`W` branch** copies the
  proof's `⌈|π|/8⌉` packed words to the output (`wIR`; loop cap `t`, BP-C-R2-M2), so the output
  is `packBytes π` and denotes `WitnessSending.decode π` (`FRXComputes.ext_W`);
* a kind byte and `|π| = piSize`: the **SNARK branch** `dec` (decode and output, §6.2 steps 2–5);
* a kind byte and another length: no output (`kindOf = bad`).

The SNARK branch is a parameter. Its obligations for `Computes` are `DecOk` (well formed, loop
bounds on every domain tape with `|π| = piSize`, a cost within `decBudget`, at most `outCap`
output words, at most `2^19` statements). `ext := extWith dec₀` fixes the branch delivered so far.

## Loop bounds without semantics: `Safe`

`BoundsOk` is a property of the run. `Safe I t P` is a syntactic sufficient condition: every
`loopT` of `P` sits right after a prefix `pre` that sets its count register to a value at most the
cap from **every** state (in practice: `pre` reads the count from a fixed tape position, the
discipline of the S-H1 review: "each `loopT` count is loaded by `input` immediately before its
loop"). `boundsOk_of_safe` turns it into `BoundsOk` from every state satisfying `Inv`.
-/

namespace FR.X

open RecursionFast

/-! ## `Safe` -/

/-- **Loop bounds that hold from every state**: every `loopT` is preceded by a prefix after which
its count is at most its cap at `t`, whatever the state before. -/
inductive Safe (I : Array Word) (t : ℕ) : XIR → Prop
  | blk (ps) : Safe I t (.blk ps)
  | load (d a) : Safe I t (.load d a)
  | store (a v) : Safe I t (.store a v)
  | input (d a) : Safe I t (.input d a)
  | out (v) : Safe I t (.out v)
  | seq {p q} : Safe I t p → Safe I t q → Safe I t (.seq p q)
  | ite {c p q} : Safe I t p → Safe I t q → Safe I t (.ite c p q)
  | loopK {c n K b} : Safe I t b → Safe I t (.loopK c n K b)
  | loopT {pre c n cap b} : Safe I t pre →
      (∀ s : St, Inv s.M → (rd (semXIR I pre s).M n).toNat ≤ cap.eval t) → Safe I t b →
      Safe I t (.seq pre (.loopT c n cap b))

theorem rd_entryT {c n : ℕ} {M : Mem} (hc : c < M.size) : rd (entryT c n M) c = rd M n := by
  simp [entryT, rd_set_self hc]

/-- **`Safe` gives the loop bounds** from every state satisfying `Inv`. -/
theorem boundsOk_of_safe {I : Array Word} {t : ℕ} {P : XIR} (h : Safe I t P) :
    WF P → ∀ s : St, Inv s.M → BoundsOk I t P s := by
  induction h with
  | blk | load | store | input | out => intro _ _ _; trivial
  | seq _ _ ihp ihq => intro hP s hM; exact ⟨ihp hP.1 s hM, ihq hP.2 _ (inv_sem I hP.1 hM)⟩
  | ite _ _ ihp ihq =>
    intro hP s hM; simp only [BoundsOk]; split
    · exact ihq hP.2 s hM
    · exact ihp hP.1 s hM
  | @loopK c n K b _ ih =>
    intro hP s hM j _
    have h0 : Inv (entryK c n K s.M) := inv_of_frame hM (size_entryK ..)
      fun i hi => entryK_frame _ (by have := hP.1; omega) (by simp only [cTmp]; omega)
    exact ih hP.2.2.2 _ (iterL_inv (by have := hP.1; omega)
      (fun s' h' => inv_sem I hP.2.2.2 h') j _ h0)
  | @loopT pre c n cap b _ hcnt _ ihpre ihb =>
    intro hP s hM
    refine ⟨ihpre hP.1 s hM, ?_⟩
    have hM' := inv_sem I hP.1 hM
    have hP2 := hP.2
    have hc : c < (semXIR I pre s).M.size := by have := hM'.1; have := hP2.2.1; omega
    have h0 : Inv (entryT c n (semXIR I pre s).M) := inv_of_frame hM' (size_entryT ..)
      fun i hi => entryT_frame _ (by have := hP2.1; omega)
    refine ⟨by rw [rd_entryT hc]; exact hcnt s hM, fun j _ => ?_⟩
    exact ihb hP2.2.2.2 _ (iterL_inv (by have := hP2.1; omega)
      (fun s' h' => inv_sem I hP2.2.2.2 h') j _ h0)

/-! ## Registers of the parse and the `W` branch (user registers, §6.4) -/

/-- Address scratch. -/ def rA : ℕ := 64
/-- `|π|`, tape word 4. -/ def rLen : ℕ := 65
/-- Constant scratch. -/ def rK : ℕ := 66
/-- The `W` branch's word count `⌈|π|/8⌉`. -/ def rCnt : ℕ := 67
/-- Scratch. -/ def rT : ℕ := 68
/-- The word read. -/ def rW : ℕ := 69
/-- The tape position. -/ def rPos : ℕ := 70
/-- The `W` loop's counter. -/ def rC : ℕ := 71
/-- The first proof byte. -/ def rB0 : ℕ := 72
/-- `1` iff the first byte is a kind byte. -/ def rIsK : ℕ := 73
/-- `1` iff `|π| = piSize`. -/ def rIsSz : ℕ := 74

/-! ## The parse (§6.2 step 1) -/

/-- `M[d] :=` tape word `pos`. -/
def readAt (d pos : ℕ) : XIR := .seq (.blk [.const rA (BitVec.ofNat 64 pos)]) (.input d rA)

/-- `⌈w/8⌉` as the machine computes it: `(w >> 3) + (w & 7 ≠ 0)` (no `+ 7` that could wrap,
S-H1 review). -/
def ceil8 (w : Word) : Word := (w >>> 3) + (if (0 : Word) < (w &&& 7) then 1 else 0)

/-- `rCnt := ⌈M[rLen]/8⌉`, `rPos := 5`. -/
def wCntPs : List Prim :=
  [.const rK 3, .op .shr rCnt rLen rK, .const rK 7, .op .and rT rLen rK, .const rK 0,
   .op .ltu rT rK rT, .op .add rCnt rCnt rT, .const rPos 5]

/-- The `W` loop's prefix: `|π|` from tape word 4, the count, the start position. -/
def wPre : XIR := .seq (readAt rLen 4) (.blk wCntPs)

/-- The `W` loop's body: output tape word `rPos`, advance. -/
def wBody : XIR := .seq (.input rW rPos) (.seq (.out rW) (.blk [.op .add rPos rPos cOne]))

/-- **The `W` branch**: copy `⌈|π|/8⌉` tape words from word 5 (cap `t`, BP-C-R2-M2). -/
def wIR : XIR := .seq wPre (.loopT rC rCnt ⟨0, 1, 1⟩ wBody)

/-- The kind bytes `'L'`, `'P'`, `'N'` (`Kind.byte`). -/
def kindPs : List Prim :=
  [.const rK 0xFF, .op .and rB0 rB0 rK,
   .const rK 0x4C, .op .eq rIsK rB0 rK, .const rK 0x50, .op .eq rT rB0 rK, .op .or rIsK rIsK rT,
   .const rK 0x4E, .op .eq rT rB0 rK, .op .or rIsK rIsK rT,
   .const rK (BitVec.ofNat 64 piSize), .op .eq rIsSz rLen rK]

/-- The parse: `rLen := |π|`, `rB0 :=` the first proof byte, the flags `rIsK`, `rIsSz`. -/
def parseIR : XIR := .seq (readAt rLen 4) (.seq (readAt rB0 5) (.blk kindPs))

/-- **The extractor's program**, with the SNARK branch `dec`. -/
def extIRWith (dec : XIR) : XIR := .seq parseIR (.ite rIsK (.ite rIsSz dec (.blk [])) wIR)

/-! ## The program, the fuel -/

/-- The fixed memory: `2^26` words (§6.2). -/
def memX : ℕ := 2 ^ 26
/-- The memory per tape word (§6.2). -/
def mpwX : ℕ := 3

/-- `claim.json`'s `fuel_base` (`3 · 2^46 ≈ 2^47.58`, blueprint B-10). -/
def fuelBase : ℕ := 3 * 2 ^ 46
/-- `claim.json`'s `fuel_per_word` (`2^12`). -/
def fuelPerWord : ℕ := 2 ^ 13

/-- **The declared fuel** `fuel t = fuel_base + fuel_per_word · t` (`claim.json`). -/
def fuel (t : ℕ) : ℕ := fuelBase + fuelPerWord * t

/-- What the SNARK branch may cost: the fuel less the memory, the parse and the `W` branch, with
room to spare. -/
def decBudget (t : ℕ) : ℕ := fuelBase - 2 ^ 27 + (fuelPerWord - 16) * t

/-- **The obligations on the SNARK branch** for `Computes`. -/
structure DecOk (dec : XIR) : Prop where
  /-- Well formed. -/
  wf : WF dec
  /-- Its loop bounds hold on every domain tape of a proof of `piSize` bytes. -/
  safe : ∀ c (π : Proof) (L : Log), π.size = piSize → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    Safe (extractorInput c π L).toArray (extractorInput c π L).length dec
  /-- Its cost is within `decBudget`. -/
  cost : ∀ t, cost dec t ≤ decBudget t
  /-- It outputs at most `outCap` words. -/
  outs : ∀ t, outs dec t ≤ outCap
  /-- It compiles to at most `2^19` statements. -/
  size : sizeIR dec ≤ 2 ^ 19

/-- The program with the SNARK branch `dec`. -/
def extWith (dec : XIR) : XProg := toProg memX mpwX (extIRWith dec)

/-! ## The fixed parts: well formed, cost, size -/

theorem wf_extIRWith {dec : XIR} (h : WF dec) : WF (extIRWith dec) := by
  simp only [extIRWith, parseIR, readAt, kindPs, wIR, wPre, wCntPs, wBody, WF, Writes, Prim.dst,
    List.mem_cons, List.mem_nil_iff, rA, rLen, rK, rCnt, rT, rW, rPos, rC, rB0, rIsK, rIsSz, regs,
    cTmp, cOne]
  refine ⟨?_, ?_⟩ <;> simp_all

theorem cost_extIRWith (dec : XIR) (t : ℕ) :
    cost (extIRWith dec) t = 33 + max (max (cost dec t) 1 + 1) (23 + 8 * t) := by
  simp only [extIRWith, parseIR, readAt, kindPs, wIR, wPre, wCntPs, wBody, cost, blkSteps,
    List.length_cons, List.length_nil, Aff.eval, Nat.div_one]
  norm_num; omega

theorem sizeIR_extIRWith (dec : XIR) : sizeIR (extIRWith dec) = 65 + sizeIR dec := by
  simp only [extIRWith, parseIR, readAt, kindPs, wIR, wPre, wCntPs, wBody, sizeIR, blkSteps,
    List.length_cons, List.length_nil]
  norm_num; omega

/-- **The fuel covers the program** whenever the SNARK branch is within `decBudget`. -/
theorem fuel_covers {dec : XIR} (h : ∀ t, cost dec t ≤ decBudget t) (t : ℕ) :
    memX + mpwX * t + cost (extIRWith dec) t + 8 ≤ fuel t := by
  have := h t
  rw [cost_extIRWith]
  simp only [memX, mpwX, fuel, fuelBase, fuelPerWord, decBudget] at *
  omega

/-- The declared fuel is within the contract's budget `B t = 2^48 + 2^16 t`. -/
theorem fuel_le_budget (t : ℕ) : fuel t ≤ extractorBudget t := by
  simp only [fuel, fuelBase, fuelPerWord, extractorBudget]; omega

/-- The program is within `progCap`. -/
theorem size_extWith {dec : XIR} (h : sizeIR dec ≤ 2 ^ 19) : (extWith dec).body.size ≤ progCap := by
  simp only [extWith, toProg, size_compile, sizeIR, sizeIR_extIRWith, initPs, blkSteps,
    List.length_cons, List.length_nil, progCap]
  norm_num; omega

end FR.X
