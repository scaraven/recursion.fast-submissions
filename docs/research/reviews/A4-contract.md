<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A4-contract.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A4: adversarial review of the compiled contract v0.2 (round 2)

Date 2026-10-10. Scope: `contract/RecursionFast/Contract/*.lean` (every line), the vendored `Rv64`/`Decode`
that the contract reaches, `Challenge/*.lean.in`, `Controls/`, `Library/`, `scripts/` (render, hygiene, CI,
vendor), `audit/` comparator configs, against `design/DESIGN.md` v0.2, D3 §1.6/§3/§4, and the round-1
reviews A1–A3. I did not modify `contract/`. Probes live in `probes/a4-probes/` and run with
`cd contract && lake env lean ../probes/a4-probes/<file>.lean` (4.7–6.7 s each).

## Verdict in one paragraph

The **security core of the base track holds up**. I found no way to satisfy `Certificate0` or
`Certificate1` with a verifier that is unsound or incomplete for R1CS over K. Raw oracle messages,
contract-fixed challenge types with a defined tape encoding, the round cap, the per-round error cap,
`Agrees` over all `i, x` and raw transcripts with honest VK/IDX, and the accepting-run cost clause over
the same quantifiers close the round-1 holes C1–C3 and M3 as claimed. The decoder and semantics also
match qemu on about 9,000 differential cases. Two problems are critical. **(F1)** The T2 cost clause can
never be met by an accumulation scheme whose fold or decider reads an accumulator oracle. I prove this
in Lean, so T2 can only be won by plain-only accumulators, which in the IT model collapse to
`fullRecAcc`. **(F2)** The challenge statement does not pin the deployed image or the shape-derived
score inputs (FS, B, V, `inWords`). A submission can use `@[implemented_by]` so that every
compiled-evaluation path (emulator input, score computation, published binary) sees a different object
than the kernel-checked certificate, and the comparator accepts this. Both fixes are small.

## Findings, ranked

### F1 (critical for T2): no `Certificate2` exists if fold or decide ever QUERYs an input-accumulator oracle

*Where.* `Accumulation.lean:36` `AccStmt A := (Fin A.plain → K) × List Oracle`: the oracles are untyped,
with shapes of any size. `Accumulation.lean:86` `Reduction.AcceptingCostAtMost` is `∀ s tr v st, runOn … = some (v, st) → v ≤ c`
over **all** `s`, including statements whose oracles do not have the declared shapes. `Machine.lean:215`
`query` checks only `l < leaves` and `writable dst bytes`. `Machine.lean:92` `addQuery` charges `logLen − logLeaf`
levels from the *actual* shape. `Certificate.lean:79` applies the clause to `fold` and `decide`.

*Attack / argument.* Take any accepting run that QUERYs input oracle `j`. Replace oracle `j` by its
zero-extension, i.e. `logLen + d` with the same `logLeaf` and `get` unchanged everywhere. On the
original run every queried `l` satisfies `l < leaves`, so each QUERY still succeeds, writes the same
leaf and leaves the same state. The run therefore still accepts with the same final state. Only
`qLevels` grows, by `d` per QUERY to `j`. Since `d` is arbitrary, no claim `c` bounds the accepting
runs. `Agrees` makes the spec accept these ill-shaped inputs too, because the machine cannot tell them
apart. The spec cannot reject them on shape alone.

*Evidence (Lean, no sorry, standard axioms):* `probes/a4-probes/T2CostUnsat.lean`.
- `qimg_levels : ∀ L tape rest, ∃ v s, run qimg tape (deepOracle L :: rest) = some (v, s) ∧ v.qLevels = L`. This is a
  symbolic proof for every `L`. `qimg` is a 6-instruction image: QUERY oracle 0 leaf 0, then HALT(1).
- `decide_cost_unsat (sz) (A : Accumulation sz) (c) : ¬ A.decide.AcceptingCostAtMost A.decideView qimg c`. The same
  holds for fold (`fold_cost_unsat`).
- `no_certificate2 : S.decideImage = qimg → ¬ Certificate2 S claim`, for every claim.

*Consequence.* fold and decide can never read an accumulator oracle, so accumulator oracles are
decorative. The accumulator is effectively its plain part of at most 2^12 K-elements. In the IT model
that cannot commit to a witness or bind the index: `VK ≤ 2^10` is not injective on indices. So a sound
`embed` must do the full verification, and T2 degenerates to `fullRecAcc`, i.e. T1 plus overhead. This
contradicts DESIGN §6 ("`r ≤ 16` accumulator oracles … reachable only by QUERY"). It also contradicts D3
§4.1, whose clause quantified over oracles "respecting the declared oracle lengths". RESULT §8.7 calls
the ill-shaped inputs "harmless: quantified universally". That holds for `Secure`, which only becomes
stricter, but not for the cost clause.

*Fix (preferred).* Type the accumulator oracles:
`abbrev AccStmt (A : AccShape) := (Fin A.plain → K) × ((j : Fin A.oracles.length) → OVal (A.oracles.get j))`.
Have `foldView`/`decideView` build the `List Oracle` with `List.ofFn`. Then `Agrees`, `Secure` and the cost
clause range only over well-shaped inputs, and `SelectOk` becomes a typing fact. *Minimal fix.* Add a
hypothesis `(∀ o ∈ inputs, shapes = A.acc.oracles)` to `Reduction.AcceptingCostAtMost` for fold and decide.
Then add a control showing that an oracle-reading decider satisfies the clause, i.e. the positive
counterpart of `qimg`.

### F2 (critical): the deployed image and the score's shape inputs are not bound by the statement; compiled extraction is spoofable

*Where.* `Certificate.lean:43–52` and `Challenge/T1.lean.in:14–22`. The challenge renders only `claim`.
`submission : Submission1` is a `definition_names` entry, so its body (image *and* protocols) is the
solver's. The score needs `n`, `Σ chalWords`, `#msg rounds`, `Σ 2^logLen` and `vkLen` (`Cost.lean:48–65,86`),
none of which appears in the statement. The same holds for T0 (shape, `vkLen`) and T2 (three images,
`acc.plain`, `vkLen`, three shapes). RESULT §6.10 limits the computability gate to VK/IDX/prover/extractor.

*Attack.* The harness has to read the image bytes (emulator, badge, publication) and the shape scalars
(score) out of the solution's terms. Any compiled evaluation (`#eval`, `lake exe`, `Lean.Compiler`)
follows `@[implemented_by]`. The kernel and the comparator never see that attribute. Probe
`probes/a4-probes/UnboundImage.lean`:
`@[implemented_by shownImage] def submittedImage : Image := provedImage`. The kernel gives `submittedImage = provedImage` by
`rfl`, and `kernel_len` uses no axioms. But `#eval submittedImage.code.length` prints `5`, not `3`, and the data
is `[42]`. Likewise a round count of `2^14` evaluates to `1`, which would understate the FS surcharge by about
750k. Kernel-side extraction instead (`whnf`/`reduce`) can be defeated by terms that do not normalise or
are `noncomputable` (`oddShape` in the same file). There is then simply no value to read.

*Fix.* Evaluate nothing from the solution.
1. The image is challenge data. Render `def image : Image := ⟨[…], […]⟩` from the submitted `.bin` into
   the challenge, outside `definition_names`. Drop `image` from `Submission1`/`2`, or add a clause
   `submission.image = image`.
2. Render every score input as a claimed scalar and add equality clauses to the certificate, e.g.
   `(S.protocol c).n = {{c16.rounds}}`, `shapeSum … Round.chalWords = …`, `… msgCount = …`, `blowupNum = …`,
   `(S.protocol c).vkLen = …`. Better still, render the claimed `S⁴` as a ℚ literal and add
   `scoreFourth (S.protocol c).shape (classSz c) (S.protocol c).inWords (claim c) = {{c16.S4}}`. Then the
   kernel proves the score, and the scorer only takes geometric means.
3. Keep the hygiene/gate scan (F3) as defense in depth, not as the binding mechanism.

### F3 (major): the computability gate is (a) scoped too narrowly and (b) presumably text-based, and text scans are bypassable

*Where.* RESULT §6.10 (gate = harness scan, VK/IDX/prover/extractor only). `scripts/check-hygiene.sh` is the only
scanner in the repo. It strips `/-…-/` with a non-nesting regex and greps words.

*Evidence.* `probes/a4-probes/GateBypass.lean`. With `def opener := "/-"` and `def closer := "-/"` around it,
`@[implemented_by shownImage] def imgA` is invisible to the hygiene regex (0 hits). Compiled code runs the
other image (`#eval` → 4 instructions, kernel term 3). `probes/a4-probes/HygieneBypass.lean.txt` lists further
constructs the same regex misses: a `sorry` hidden the same way, `set_option debug.skipKernelTC true in`,
`set_option synthInstance.maxHeartbeats 0`, `decide +native` (which uses `Lean.ofReduceBool` without the word
`native_decide`), `unsafe`, `opaque`, `partial`, `run_cmd`. `scripts/AxiomAudit.lean` checks 36 named
declarations, not every theorem in Library/Controls.

*Fix.* Implement the gate on the **elaborated environment**. For every constant in the closure of the
submitted definitions, check `isNoncomputable`, `Compiler.implementedByAttr.getParam?`, `isExtern`, `csimp`,
and `unsafe`/`partial`/`opaque`. Run `collectAxioms` on *every* theorem of Library/Controls. Replay the
organiser library through lean4export plus the kernel (comparator-style) so that `skipKernelTC` cannot
matter. With F2's fix the gate stops being load-bearing for the score.

### F4 (major): the score is not a Lean function of the certificate; T0's score is undefined

*Where.* `Cost.lean:65` gives `scoreFourth` for one protocol. Nothing assembles `Score_T1` from a
`Submission1` (which `inWords`, which `sz`). `Score_T2` is not defined anywhere (per-step `inWords` = `4+vkLen+nx`,
`4+2·plain`, `4+plain`; the `/64`). T0 is "virtual query cost + bytes" in DESIGN §11, but no formula exists.
`Challenge/T0.lean.in:15` says only the query fields of the claim are meaningful. The `alu…sys` fields of a T0
claim are unconstrained by `Certificate0.cost`, because `QProg.cost` never increments them.
*Risk.* Each scorer has to reinvent the assembly. Agents will hunt for any inconsistency between scorer code and
DESIGN text. *Fix.* Add `def Score1 (S) (claim) : Fin 3 → ℚ` (the `S⁴` per class), `Score2`, `Score0` (for T0, say
explicitly whether `fsCost` and `byteCost` apply, and with `weighted` over query fields only). Then bind them via F2.2.

### F5 (minor): `render-challenge.py` accepts JSON booleans and unused keys

`isinstance(True, int)` is true, so `"c16.alu": true` renders `alu := True`. Lean then rejects it
(`probes/a4-probes/render/T1bool.lean`), so the effect is harmless, but the check is not what it says. Extra
keys are silently ignored, and integers with more than 4300 digits crash Python's `str()`. *Fix:* use
`type(v) is int`, require the key set to equal the placeholder set exactly, and cap values at `< 2^64`.

### F6 (minor): FS and byte pricing gaps

`fsCost` (`Cost.lean:48`) does not price absorbing the FS prefix (`… ‖ MTroot(IDX) ‖ VK i ‖ x`, DESIGN §5). That
prefix is about 8 KiB plus `8·vkLen` bytes. The term is constant across submissions except for the `vkLen`
part. Meanwhile `byteCost` charges `8·inWords` (header, VK, `x`) as "proof bytes", consistent with DESIGN §7
`tapeBytes` but not with what a proof contains. Neither is exploitable as far as I can see. Record both as
judgements (O12).

### F7 (minor): pipeline configuration

`ci.sh` runs the comparator with `fake-landrun.sh`, which is not a sandbox. The comment says so, but the
production verifier must use real landrun and a fresh build tree (comparator README assumption 2: never
build the solution in the checking environment first). `enable_nanoda: false` means a single kernel.
`lakefile.toml` uses `packagesDir` shared with a concurrently edited leanerVM tree, so a `lake update` there
moves this project's trusted Mathlib. *Fix:* pin the production config, with a second kernel if available
and an isolated `.lake`.

### Notes

- **N1.** A `b = 64` index challenge is a uniform K element, so DESIGN §3 / D3 §1.6 "no K-valued challenges" is
  not literally true. It is harmless: the cap still forces any such round to have no bad challenges unless
  several are batched in one round, which is legitimate parallel repetition, and the price is the same
  1/16 per random bit as E. Reword the design text.
- **N2.** The memory map (Harvard code at `0x1000`, data words from address 0 overlapping that range, tape at 2^32,
  natural alignment required) is not a standard RISC-V load layout. Running the proved image inside a real
  RISC-V zkVM for recursion needs a loader that reproduces exactly this map. Misaligned accesses fault, which
  is stricter than RISC-V and therefore harmless for soundness.
- **N3.** One QUERY is one fuel step but may write up to 2^33 words (limited only by `writable`). A
  harness emulator that materialises writes can be made to do 2^36 such steps on a *rejecting* adversarial
  transcript. That is DoS only. Implement QUERY lazily, as in the closed form.
- **N4.** Already documented and still open: interactive union bound not proved (RESULT §8.1); tree
  composition (O14); no lemma links `K.toBytes`/`E.toBytes` to the tape words the FS harness must produce
  (§8.4); 316 ZisK lines reachable in the trusted closure (§8.6). `Instruction` has no `DecidableEq`, so a
  decode lemma needs `rfl`, not `decide`. This is a small usability trap for the L0 library.

## What I tried that did NOT break it

1. **Decoder and semantics vs qemu** (`probes/a4-probes/difftest/`, `qemu-riscv64 -cpu max`, `run.sh SEED`):
   - 4 × 1,200 random register-only cases (OP incl. M and Zbc, OP-32 W-ops, OP-IMM incl. 6-bit shifts, OP-IMM-32, LUI)
     with edge-case operands (`INT_MIN/−1`, `/0`, shift ≥ 32);
   - all 4,129 distinct words the contract decodes out of 20,000 random words in those opcode spaces, with
     no SIGILL;
   - 800 store/load width and offset combinations.

   **0 mismatches.** W-op overflow and division by zero, `clmulr`, and `SLLIW` with bit 25 set (rejected) are
   all correct.
2. **A2-C1 serializer**: not expressible, since messages are raw `OVal`. `Agrees` covers every raw string.
3. **A2-C2 challenge encoding**: `Round.tapeWords` gives E as 3 limbs, then indices zero-extended. Admission
   `b ≤ 64`. Cardinalities (`natCard_chal`) are real.
4. **A2-C3 round cap**: a structure field (`n_le`). The hit control checks out.
5. **RBR-KS vacuity tricks.** An empty `WitMid` is impossible (`extractOut` from `Unit` forces the last stage to be
   nonempty, and `extractMid` propagates that). Tiny challenge types (`chal 0 []`, `b = 0`) force zero bad
   challenges. The worst-case-per-prefix quantifiers are `∀ s c tr`. The chain argument goes through.
6. **Agrees/cost quantifiers**: all `i : Index sz` (adversarial indices included), all `x`, every raw message,
   every challenge, honest VK/IDX only. The machine sees `i` only through QUERY on IDX. The tape is a
   function of `(VK i, x, tr)`.
7. **Coercions** (`probes/a4-probes/Coercions.lean`): `weighted`, `blowup` (1/3, not 0), `⌈B/8⌉` and the decider
   cap all compute in ℚ with coercions at the leaves.
8. **Cost under-counting.** The QUERY price equals D2's. `logLeaf > logLen` is excluded for messages and IDX
   (T0/T1). `sys` counts only the HALT. Splitting oracles into many small rounds is priced at 46 FS + 4 B per
   round, so it gains nothing. Rejecting paths are unpriced by design (D3 §4.3). Fuel counts steps, which does
   not affect the score.
9. **Memory map.** The tape window equals the tape cap, and admission keeps the tape inside it. `OUT_BASE` is
   zero-initialised and writable. Addresses wrap mod 2^64 and are then range-checked. Fetch requires
   4-alignment, JALR clears bit 0, and misaligned targets reject, matching RV64 without C.
10. **Padding**: `pad_sat_iff` holds in both directions. The data maps are trusted and simple.
11. **T0**: `eval` and `cost` follow the same path with the machine's oracle numbering. `agrees` is a Prop
    equality over all transcripts.
12. **T2 shape attacks**: `trivialAcc0` is not expressible, a fold that drops an input fails KS unless
    `Racc = univ`, and `select` cannot invent oracles (`getD default` is excluded by `SelectOk`).
13. **Render injection**: the placeholder regex is `[A-Za-z0-9_.]+` and values are integers, so no Lean text
    can be injected (see F5 for the boolean quirk).
14. **Moving work into preprocessing**: `VK ≤ 2^10` and IDX is index-only, so neither can tabulate over
    `x ∈ K^1024`. A2-M4's satisfiability table no longer fits.

## Auditability

- **Size.** The trusted surface is 582 code lines of contract plus the vendored code it reaches (about
  940 lines: `execInstrBr`, `decode`, `MachineState`, and ZisK code that is dead at run time). It also
  relies on the meaning of a few Mathlib notions: `Nat.card`, `Finset.filter … card`, `ℝ≥0`, `Fin.foldl`,
  `Fin.snoc`, `Fin.induction`.
- **Time.** A cryptographer who reads Lean needs about 1–1.5 days for `Contract/` and about one more day for
  the machine and the vendored semantics. Without Lean experience, budget 3–5 days.
- **Hardest definitions, in order:**
  1. `Security.lean` (`Transcript` prefixes indexed by `Fin (n+1)`, `castSucc`/`succ`, `cast E.eqIn`, the `∃ w`
     in `Bad` over the next-stage witness);
  2. `Machine.lean` (memory is `Word → Word` keyed by *aligned* address, so `initState` and `query` define it
     on every key but only aligned keys are ever read; the closed-form QUERY; `execute`'s nested matches);
  3. `Accumulation.lean` (views, `select` with `getD default`, untyped oracle lists; this is exactly where F1
     hides);
  4. `Cost.lean` (score ingredients that are not wired to any certificate, F4).
- **Outside Lean.** The trust story still depends on unwritten harness code: score extraction (F2), FS
  derivation and encoding, the gate (F3) and the emulator (N3). An auditor cannot sign off on "what the
  score means" until F2 and F4 move that into the statement.

## Prioritised fix list

1. **F2**: render the image into the challenge, and render plus prove every score input (ideally the claimed
   `S⁴` per class) in the certificate. Evaluate nothing from the solution.
2. **F1**: type the accumulator oracles (`AccStmt` with `OVal (A.oracles.get j)`), or restrict the fold/decide
   cost clause to well-shaped inputs. Add a positive control in which an oracle-reading decider meets a cost
   bound. Correct RESULT §8.7.
3. **F4**: define `Score0/1/2` in `Cost.lean`/`Certificate.lean`. Settle the T0 formula.
4. **F3**: an environment-based gate covering everything the harness touches, `collectAxioms` on all
   organiser theorems, and a kernel replay of the library.
5. **F5–F7**: harden the render script, pin the production comparator config, isolate `packagesDir`.
6. Notes N1–N4: design text and harness guidance.

## Probe index

| File | Shows |
|---|---|
| `probes/a4-probes/T2CostUnsat.lean` | F1: `qimg_levels` (∀ L), `decide_cost_unsat`, `fold_cost_unsat`, `no_certificate2` |
| `probes/a4-probes/UnboundImage.lean` | F2: `implemented_by` makes compiled evaluation of image/shape disagree with the kernel term |
| `probes/a4-probes/GateBypass.lean`, `HygieneBypass.lean.txt` | F3: text-scan bypasses |
| `probes/a4-probes/Coercions.lean` | coercions in score ingredients are correct |
| `probes/a4-probes/render/` | F5 boolean rendering |
| `probes/a4-probes/difftest/` (`gen*.py`, `run.sh`, `Diff*.lean`, `Mem.lean`, `Filter.lean`) | qemu differential tests, 0 mismatches |
