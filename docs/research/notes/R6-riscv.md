<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `notes/R6-riscv.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# R6: RISC-V semantics, proof tooling and execution speed

Research note for recursion.fast. Author: R6 subagent, 2026-10-10.
Measurements are in `probes/riscv-probe/` (see its `RESULT.md`).

Labels used throughout:
- **[V]** verified: I read the source or ran the experiment myself.
- **[I]** inference: my reading or extrapolation, not checked.

## 0. Pinned revisions

| Repo | Revision | Toolchain | Notes |
|---|---|---|---|
| riscv-zkvm (local, read-only) | `6810fc14d9c40373101321cefaec59df8d82e3e7` (main, 2026-10-06, "Merge PR #17 docs/release-cache-blocker") | v4.33.1 | lean-sail `079463134b9c` (official v5); Sail RISC-V 0.13.1 `27224ccb2290`; Sail compiler 0.20.3 |
| riscv-zkvm as pinned by sig.golf **and** ots.golf | `4634e41b229da4256e4a1f1688b94133fffa4af0` (2026-09-08, "Merge PR #12 feat/sp1-mem-cell") | v4.33.0 in that commit | **only on branch `origin/sp1-backend`; not an ancestor of main HEAD** (merge-base `afcbc45` = v0.3.0) [V]; lean-sail *fork* `dhsorens/lean-sail@8d57a8b5` |
| sig.golf-dev | `eaa0c7f97ea24fd61319d19ce1952c66ccef424f` | v4.33.1 | VCVio `25f26bf`, mathlib v4.33.1 |
| ots.golf-dev | `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c` | v4.33.1 | leanerVM `8563b05`, which brings in ArkLib `dca90385` (v4.33.1) |
| ots.golf-submissions (cloned to `probes/riscv-probe/ext/`) | `30cff1406373fc31dee9be4a3c7c814c50944569` | v4.33.1 | reference RISC-V proofs |
| ArkLib (local) | HEAD `db7005f` (v4.34.0) | v4.34.0 | last v4.33.1 commit is `68726031f` (2026-09-20), the parent of the 4.34 bump `fa14552d4` [V] |

## 1. What riscv-zkvm provides

### 1.1 Both a Sail extraction and a hand-written model

`README.md:6-13` [V]:

> | `RiscvZkvm.Sail` | Lean extraction of the official `riscv/sail-riscv` specification — **generated**, not hand-maintained |
> | `RiscvZkvm.Rv64` | a hand-written, computable RV64IM machine model (`Instr`, `MachineState`, `step`) |
> | `RiscvZkvm.Rv64.SailEquiv` | the tie between them: 51 per-instruction `*_sail_equiv` theorems plus step/run simulation |
> | `RiscvZkvm.Rv64.Logic` | the program logic: separation logic over `MachineState`, the CPS specification layer, a weakest-precondition framework, and the symbolic-execution tactics |

It also has `RiscvZkvm.Interpreter` and the `riscv-zkvm-run` CLI (`lakefile.toml:59-63`). The
package is Mathlib-free: "`lean-sail` is the only package dependency — there is no Mathlib"
(`README.md:31-32`). The repo exists to serve `Verified-zkEVM/evm-asm`, about 2,500 of whose
roughly 3,000 modules depend on it (`README.md:62-71`), and it treats the `Instr` constructors,
`MachineState` fields and `step` semantics as public API.

Module map (`find`, line counts from `wc`) [V]. The total is 94,159 lines of Lean.

- **`RiscvZkvm/Sail/**` (120 generated files plus the `Sail.lean` root; PROVENANCE says `expected_lean_files = 121`).** Sail modules `main, I_insts, M_insts,
  Zicsr_insts, K_core, Zkr, Zicboz, Zicbom_insts` (`sail-import/PROVENANCE.toml`). These are
  proof-oriented and `noncomputable`: "the proof extraction is `noncomputable`, so the Sail
  decoder does not evaluate" (`docs/validation.md:133-138`). Building `RvfiDii` alone took about
  14 GiB RSS and "tens of minutes of CPU time" (`docs/maintenance.md:102-104`).
- **`RiscvZkvm/Rv64/`.** `Basic.lean` (731 lines: `Reg`, `Instr`, `MachineState`),
  `Execution.lean` (917: `execInstrBr`, `step`, `stepN`), `Word.lean` (230: memory zones),
  `Instructions.lean`, `Program.lean`, `Bytes.lean`, `ZiskAccel.lean` (907: ZisK CSR
  accelerators) and `CoreTactics.lean`. My heuristic count gives about 1.07k
  definition lines on the semantics path (Basic 321 + Execution 340 + Word 78 + Instructions 198
  + Decode 134), plus 433 in ZiskAccel. The rest are lemmas [V, heuristic].
- **`RiscvZkvm/Rv64/SailEquiv/**`.** About 9.3k lines; per-instruction proofs (`ALUProofs`,
  `MExtProofs`, `BranchProofs`, `MemProofs`, Vmem*), `StepRun.lean`.
- **`RiscvZkvm/Rv64/Logic/**`.** About 20.2k lines. `SepLogic.lean` (3,201 lines), `CPSSpec.lean`, `WP/*`,
  and `Tactics/{RunBlock, SeqFrame, XPerm, XCancel, WP, SymStep, ...}`.
- **`RiscvZkvm/Interpreter/`.** `Decode.lean` (174), `Elf.lean`, `State.lean` (efficient state),
  `Run.lean`, `Cli.lean`.

### 1.2 The hand model (the one everyone actually uses)

- **Instructions** (`Basic.lean:110-239`) [V]. Full RV64I and M at the AST level, with these
  exceptions and additions:
  - Only `ADDIW` from the W family; `ADDW … REMUW` are absent (`docs/validation.md:127-132`).
  - Pseudo-instructions `MV`, `LI`, `NOP`.
  - `ECALL`, `EBREAK`, `FENCE`.
  - `CSRS csr rs1`, the ZisK accelerator call. It is the only CSR form, and "unmodeled ids trap".

  There is **no Zbb, Zbc/Zbkc (clmul), Zba, A, F/D or C** in the hand model. The Sail JSON
  config marks `Zbc`, `Zbkb`, `Zbkc` as `"supported": true` (`sail-import/rv64d_v256_e64.json:681-690`),
  but the selected Sail modules do not include the bitmanip instruction files: `grep -ri clmul
  RiscvZkvm/` finds nothing [V].
- **State** (`Basic.lean:250-268`) [V]. `regs : Reg → Word`. `mem : Word → Word` is
  "doubleword-addressable (8-byte aligned addresses map to 64-bit words)". Sub-word stores
  read-modify-write the containing doubleword (`Word.lean:186-215`, `replaceByte`/`alignToDword`).
  `code : Word → Option Instr` is a **separate** code map (Harvard), so stores cannot modify
  code. Further fields are `pc`, `committed`, `publicValues`, `privateInput` and `inputBufBase`.
- **Step** (`Execution.lean:341-433`) [V]. `step : MachineState → Option MachineState` fetches
  from `code` (an AST, no decoding) and checks the validity and alignment of every load and store.
  `none` means a trap or a halt:

  > "Returns none if no instruction at PC (stuck/halted), or if the instruction is ECALL with
  > t0 = 0 (HALT syscall, following SP1 convention). LD/SD trap (return none) on misaligned or
  > out-of-range dword addresses." (`Execution.lean:328-340`)

  `stepN n` is `Option.bind` iteration (`Execution.lean:804-806`). `execInstrBr`
  (`Execution.lean:38`) is the total per-instruction transition.
- **ECALL hooks** (`Execution.lean:406-432`) [V]. They are selected by `t0` (x5):
  - `0`: HALT (`none`);
  - `0x02`: WRITE to fd 13 (public values);
  - `0x10`: `write_output`;
  - `0xF2`: `read_input` (zkvm-standards C ABI);
  - anything else: "other ecalls continue", i.e. a no-op.

  ZisK precompiles are `CSRS` ids with **concrete** semantics (`ZiskAccel.lean:1-40`):
  Keccak-f[1600] (0x800), Arith256Mod `d := (a*b + c) mod m` with an exact 512-bit
  intermediate (0x802), SHA-256 compression (0x805), secp256k1 and BN254 add/double.
  The module states the policy: "the project's trusted base is the three classical axioms — an
  axiomatized accelerator contract would widen it".
- **Memory map** (`Word.lean:38-118`) [V]. Valid data zones are `[0x20, 0x78000000]`,
  input `[0x40000000, 0x40002000]` and RAM `[0xa0000000, 0xc0000000]`.
  "The `.text`/`.rodata` window `[0x80000000, 0xa0000000)` is deliberately NOT a zone, and this
  is load-bearing for soundness" (`Word.lean:58-59`): code and data are separate maps, so a store
  into the text window would desynchronise them.
- **Executability** [V]. The hand model is computable. `Interpreter/State.lean` explains why a
  second state type exists: "`setMem` extends it by one closure layer per store, so reading a cell
  after N stores costs O(N). Booting an ELF and running millions of instructions is not possible
  against that representation" (`State.lean:6-12`). `ExecState` uses `Std.HashMap` but "execution
  still goes through the model's own `RiscvZkvm.Rv64.step`" (`State.lean:14-19`). The bridge is not
  proved. The documented **known gaps** (`docs/validation.md:105-150`) are:
  1. the `riscv-tests` corpus cannot run, because of the memory map and the absence of M-mode CSRs;
  2. W-ops are missing;
  3. "`decode` is not tied to Sail": no theorem relates `Interpreter.decode` to Sail's
     `encdec_backwards`;
  4. "`stepExec` is not proved to simulate `step`".

  ISA-conformance evidence instead comes from executing the *Sail* model through upstream's Lean
  emulator (50/50 `rv64ui-p` tests, `docs/validation.md:56-58`).
- **SailEquiv** [V]. `sailStep_run_sim` (`SailEquiv/StepRun.lean:327-334`) proves: if `RunInv
  lo hi sRv sSail`, the fetched `i` is `simulable`, `toSailInstr? i = some si` and `step sRv =
  some sRv'`, then Sail's `sailStep si` succeeds and preserves `RunInv`. Its side conditions are
  `RAM_MEM_START ≤ lo`, `hi ≤ RAM_MEM_END` and `stepSideCond`. `sailStepN_run_sim` (`:381-387`)
  lifts this to `stepN`.

  Limits [V]: ECALL, EBREAK, FENCE, CSRS, MV, LI and NOP are excluded by `Instr.simulable`
  (`StepRun.lean:50-57`). The relation is stated at the **AST** level (`toSailInstr?`), so
  decoding of raw words is outside it.
- **Trusted base and CI gates** [V]. Every `Rv64.*` and `Interpreter.*` declaration (3,500)
  uses only 7 axioms: `propext`, `Classical.choice`, `Quot.sound`, plus 4 Sail platform axioms
  (`load_reservation`, `match_reservation`, `plat_term_write`,
  `sys_enable_experimental_extensions`) (`docs/validation.md:152-172`).
  `scripts/check-forbidden-tactics.sh` rejects `native_decide` and `bv_decide` anywhere,
  including in generated code (`AGENTS.md:34`, `validation.md:162-166`).
  Downstream contracts that import only `RiscvZkvm.Rv64.Execution` (ots.golf, sig.golf) depend
  on no Sail axioms. This follows from their `permitted_axioms` lists, which contain only the
  three classical axioms (`sig.golf verifier/comparator.json:12`) [V].

### 1.3 Docs and the "release cache blocker"

The docs are `README.md`, `AGENTS.md`, `CHANGELOG.md`, `docs/{validation, maintenance, tactics,
release-refresh, interpreter-roadmap, refresh-review, structural-cancel-*}.md` and
`docs/agents/wp-framework.md`.

The blocker (`docs/release-refresh.md:15-36`, `README.md:35-38`) [V]:

> "**Release status: held as a draft.** … The v5 ambiguous-namespace warning serializes its
> absolute source path into `Sail.Sail.olean`. A fresh consumer builds the same runtime at a
> different path, changing that olean's hash and invalidating the extraction through legacy
> transitive imports."

So the `v0.4.0` (Lean 4.33.1) prebuilt-olean archive cannot be reused by consumers: they would
rebuild the 14 GiB Sail extraction. The README advises "Do not bump downstream pins to it yet. The
published `v0.3.1` release uses Lean 4.33.0." The fix is waiting on upstream lean-sail PR #14.

Lean 4.34.1 is "deferred: its intrinsic `assert` syntax collides with generated Sail runtime
calls" (`release-refresh.md:41-42`, Sail issue #1765).

**Consequence [V, probe].** The blocker and the 4.34 deferral affect **only** the Sail library.
I copied `Rv64/*`, `Interpreter/*` and `Rv64/Logic/**` **unchanged** into a Sail-free Lake
project on Lean v4.34.1:
- Rv64 + Interpreter built in 2m14s with 0 warnings, and the runner gives identical output.
- Logic built in 49 s with 47 deprecation warnings (`probes/riscv-probe/rv64-on-434/`).

### 1.4 How sig.golf and ots.golf consume it

Neither contract uses Sail, SailEquiv or the Logic library. Both import only the hand model
[V: `grep runBlock|cpsTriple|Rv64.Logic` finds nothing in either contract or submission].

| | sig.golf (`SigGolf/Riscv.lean`, 226 lines) | ots.golf (`OptimalOTS/RiscvMachine.lean` 130, `Riscv.lean` 47, `RiscvHint.lean` 217) |
|---|---|---|
| Imports | `RiscvZkvm.Rv64.Execution`, `Rv64.StepOn`, `Interpreter.Decode` (`:1-4`) | `RiscvZkvm.Rv64` (`RiscvMachine.lean:2`) |
| Image | `code : List (BitVec 32)` **raw encodings** + `data : List Byte` (`:20-22`) | `code : List Instr` **AST**, no encodings (`RiscvMachine.lean:45-47`) |
| Decoder in trust base | yes: own `decodeInstruction` for ECALL/EBREAK, the 10 W-ops and SRAIW, else riscv-zkvm `decode` (`:80-108`) | none (AST loaded by `loadProgram codeBase`) |
| Semantics | own `ordinaryStep`: `execInstrBr` after its own bounds/alignment check over a flat 16 MiB memory (`MEMORY_BYTES = 2^24`), rejects CSRS/LI/MV/NOP (`:129-147`) | riscv-zkvm `step` itself; `admittedInstruction` rejects LI/MV/NOP/CSRS/EBREAK and odd branch offsets (`:37-42`) |
| Machine loop | `execute : Nat → MachineState → OracleComp HashSpec Execution` with cycles and compressions (`:204-224`) | `execute : ℕ → MachineState → OracleComp Spec Outcome`, `Outcome = Option (Bool × ℕ)` (`:107-128`) |
| Syscalls | `t0=0`: HASH(a0 input, a1 bytes, a2 out), whole 64-byte blocks; `t0=1`: HALT, success iff `a0=0`; anything else is failure | `t0=0`: HALT (a0∈{0,1}); `t0=1`: HASH(a0 ptr, a1 *bits*, a2 out); anything else traps |
| Layout | code at `0x1000` (`fetch`, `:156-161`), data at top of memory, `sp` there | code `0x1000`, data `0x200000`, pk/msg/sig at `0x400000…`, `sp=0x1000000` (`:25-30`) |
| Limits | `MAX_PROGRAM_BYTES = 2^20`, `CYCLE_LIMIT = 2^32` (`Parameters.lean:34-40`) | ≤ 262,144 instructions, ≤ 1 MiB data, `byteSize < 1 MiB` (`RiscvMachine.lean:52-54`) |

Both are deterministic given the oracle answers, Harvard, and have no self-modifying code.

The pinned `4634e41` differs from main HEAD in ways these contracts rely on [V, `git diff
4634e41 HEAD`]:
- It has 4 extra `Instr` constructors (`SUBW`, `SRLW`, `SLLIW`, `SRLIW`) and decoder clauses.
- It has `isValidOutputRange`, which ots.golf's `hashArgumentsValid` uses.
- It has `StepOn.lean`, which contains `memAccess`, used by sig.golf's `memoryArgumentsValid`.
  The module is explained as "backend-parametric stepper … `stepOn .zisk = step` holds by
  `rfl`" (`git show 4634e41:RiscvZkvm/Rv64/StepOn.lean`).

So **ots.golf and sig.golf cannot be bumped to riscv-zkvm main without contract edits**, and
a recursion.fast pin of main HEAD would have different semantics from theirs.

## 2. Proof tooling and methodology

### 2.1 riscv-zkvm `Rv64.Logic` (the evm-asm style)

This is separation logic over `MachineState` with `cpsTriple`/`cpsTripleWithin n entry exit
codeReq pre post` (`docs/tactics.md`). Tactics [V]:
- `runBlock` is "the main workhorse": it composes `@[spec_gen]` per-instruction specs with
  automatic framing.
- `seqFrame` composes triples.
- `xcancel`, `xperm` and `xsimp` handle AC-permutation and cancellation of `**` chains.
- `wp_rv64*` is backward weakest-precondition over a CFG certificate (`docs/agents/wp-framework.md`).
  It includes `wp_rv64_leaf_synth`, which computes `cfg.pre` from a postcondition, and bounded-loop
  helpers `wp_rv64_loop_nat`/`_sound`.
- `sym_step` is a prototype that only covers ADDI/ADD/LUI/SLLI (`Tactics/SymStep.lean:1-25`).

There are also "grindsets": `rv64_addr`, `reg_ops`, `byte_alg` (`grind` + `simp only` closers).
Neither `bv_decide` nor `native_decide` is allowed. The CHANGELOG (v0.4.0) records soundness-of-tooling bugs that
were fixed: "`xperm` no longer reports success on a permutation it did not find …
the declaration was admitted with `sorryAx` by ordinary error recovery, so `#print axioms` was
the only honest witness". This is a reminder that tactic bugs show up as `sorryAx` and must be
caught by an axiom audit.

**Measured scaling of `runBlock` [V, probe].** I used straight-line ALU blocks with an explicit
postcondition (`probes/riscv-probe/riscv-zkvm/Probe/RB*.lean`). The times are wall time
including about 2.0 s of import loading:

| n | 2 | 8 | 32 | 128 |
|---|---|---|---|---|
| wall | 2.2 s | 2.3 s | 4.3 s | 161 s |

The cost is strongly superlinear (≈80× for 4× n). The negative control (wrong
postcondition) is rejected. The practical rule is blocks of at most 30-60 instructions,
composed with `seqFrame`/WP.

`Rv64.Logic` builds in 54 s on top of Rv64 (66 jobs, 1.8 GB RSS) [V].

### 2.2 sig.golf: reflective symbolic executor plus kernel evaluation

`submission/SigGolfCandidate/Rv/*` (2,289 lines, *submission-side and untrusted*) [V]:
- **`Expr.lean`.** A symbolic word language `E` over atoms `E.reg r` / `E.ld a` of an initial
  state, with constant folding and address normalisation.
- **`Micro.lean`.** "`classify_sound` proves that `ordinaryStep` agrees with the (much smaller)
  concrete micro-semantics `Micro.exec`".
- **`Exec.lean`.** `symRun cfg code pc fuel : Option Result` symbolically executes straight-line
  raw words. It stops before ECALL and after a branch or jump, and it returns `none` on
  unresolved aliasing.
- **`Sound.lean:558`.** `symRun_sound`: `symRun … = some r` → `Steps image s r.steps r.cycles
  (r.toState s)` under the obligations `r.obligs s`.
- **`Tactic.lean:1-12`.** `sym_eval` / `sym_block`: "the left-hand side is evaluated by the
  compiled executor (untrusted), the result is turned into a literal term, and the equation is
  then certified by the **kernel** alone (`Eq.refl` …). No `Lean.ofReduceBool`/`native_decide`
  is involved".
- **`Api.lean`.** `BlockSpec image entry k c P Q` with `BlockSpec.of_symRun`, and
  `Steps.iterate` (line 64), a loop-invariant lemma for loops whose body is a block.
- **`Steps.lean`.** `Steps.execute`: `execute (fuel + k) image s = (·.charge c 0 0) <$> execute
  fuel image t`, plus HASH and HALT laws.

The per-program proofs (`Verify/*`, 61 files, 9,530 lines) are dominated by Boolean checkers
evaluated by `decide +kernel`. For example, `Verify/ChainCheckA00.lean` is ten lines of the form
`theorem chainCheck_0_0 : chainCheck 0 0 = true := by decide +kernel` (270 uses in the
submission). The comment there says "the import chain serializes this family to bound parallel
build memory". Many files raise `maxRecDepth` (up to 100,000) and `maxHeartbeats` (up to 5·10^6).

Scale [V, by counting `Images.lean`]: the four images have 175 + 2,967 + 287 + 72,992 (verify,
heavily unrolled) instructions. RISC-V-level proof directories total about 37k lines:
- Rv 2.3k, Verify 9.5k, Sign 12.3k, Keygen 3.1k, Expand 6.2k, Equiv 6.0k, Ref 1.8k, Budget 3.3k;
- plus `Images.lean` (14.9k lines of literals).

The security proof (`SphincsSecurity`) adds a further 90.5k lines. That is about 0.13 lines of
`Verify` proof per *static* verify instruction, possible only because the unrolled code is
regular and checked by kernel evaluation [V numbers; I interpretation]. The repo does not
document a build time; the hosted verifier allows "the verifier's four-hour, 24 GiB limit"
(`README.md:55`, `verifier/verify.py:31`) [V].

### 2.3 ots.golf: hand-written block lemmas over riscv-zkvm `step`

`ots.golf-submissions/formal/Submissions/UpperRiscv` (`30cff14`, claim 341 cycles) [V]:
- `Refines fuel s q c := observe fuel s = q ∧ ∀ b cycles, some (b, cycles) ∈ support (execute
  fuel s) → cycles ≤ c` (`Refines.lean:15-17`), with composition rules `Refines.steps`,
  `.linear`, `.hash`, `.halt`, `.branch`.
- Straight-line code is handled by `LinearReady s code` (per-instruction admissibility and memory
  validity at the actual intermediate state) and
  `linear_steps : PureSteps code.length s (code.foldl execInstrBr s)` (`BlockExecution.lean:110-160`).
  The proofs then compute with `simp`/`omega`/`decide` on `foldl execInstrBr`.
- The image is written in Lean as `List Instr` macros (`Program.lean`, e.g. `copy128`, `reject`).
  The README says: "The Lean-exported image equals an independent generator and passes 16,330
  exact oracle-transcript executions" (`README.md:13-16`), and `NOTES.md` adds "An exact
  worst-case search over the same cost model gives 341". Validation by differential execution
  supplements the proof; it is not part of the certificate.
- Scale: 15,616 instructions (mostly replicated jump-table copies) and 88 data bytes. The
  submission root is 20.6k lines, of which about 3.5k are machine-level (`BlockExecution`,
  `Mixed*`, `Refines`, `MachineFacts` …); the rest is security, counting and arithmetic [V
  counts]. Build time is not documented.
- The ots.golf contract docs (`docs/upper-riscv.md`) give the methodology: "exact refinement of
  the Lean verifier by the machine's oracle computation, preserving queries", with
  `Verifier.image_refines` composed from per-phase `*_refines` lemmas.

### 2.4 Summary of methodology and cost

The common pattern in all three projects:
1. Fix the image as a Lean constant.
2. Split it into basic blocks.
3. Prove a per-block Hoare/refinement fact.
4. Compose the facts along the CFG, with loop invariants proved by induction (`Steps.iterate`,
   `chainsFrom_refines` by induction over chains, `wp_rv64_loop_nat`).
5. Prove the final equality to a Lean reference function, either as an oracle computation or
   as a value.
6. Accumulate cycle bounds alongside each fact.

The cost [I, from the data above]:
- **Lines per instruction.** Roughly 0.1-0.3 lines per *static* instruction for regular,
  table- or unroll-heavy code verified by reflection or kernel evaluation (sig.golf, ots.golf).
  Hand-written separation-logic proofs (evm-asm style) cost far more per *distinct* block, since
  each block needs a stated postcondition. Both are dominated by the *semantic* bridge (BitVec
  facts to field or number theory), not by instruction stepping.
- **Elaboration.** `runBlock` costs about 0.1 s per block of 8, 2 s per block of 32, and is
  impractical beyond about 100.
- **Decision procedures.** `bv_decide` and `native_decide` are excluded in practice: both add
  `Lean.ofReduceBool`, and every contract permits only the three classical axioms.
  `decide +kernel`, `omega`/`bv_omega`, `simp` and `grind` are allowed.

## 3. Execution speed (measured)

All runs are on this machine (`probes/riscv-probe/RESULT.md`) [V]:

| Emulator | Trust status | Rate (instr/s) | 10^7 instr | 10^9 instr |
|---|---|---:|---:|---:|
| `riscv-zkvm-run` (executes `Rv64.step` through `ExecState`) | semantics = proof model; HashMap bridge **unproved** | **0.35-0.37 M/s** (10,000,007 in 26.8 s; gcc guest 21,000,024 in 59.5 s) | ≈27 s | ≈45 min |
| `fastemu`: my UInt64/ByteArray Lean interpreter, about 200 lines | unverified, but in Lean | 7.7-9.1 M/s (10^8 in 10.9 s) | ≈1.2 s | ≈2 min |
| `rustemu`: naive Rust switch interpreter, about 90 lines | unverified | 70-110 M/s (10^9 in 10.2 s) | 0.1 s | ≈10 s |
| `qemu-riscv64` 10.2.1, user-mode JIT | unverified, no exact count (no TCG plugin installed) | ≈1.4 G/s (10^8 in 0.07 s) | — | <1 s |

All counting emulators agree exactly on the retired counts and `a0` for five ELFs, a small
differential test. The `riscv-zkvm-run` profile shows `lean_apply_1` 16%, closure-backed
register access ≈24%, malloc/free ≈11% and GMP ≈8%. The register file is `Reg → Word`, rebuilt
every step, and `BitVec 64` is a `Nat`, so values ≥ 2^63 become GMP bignums. `fastemu` loses
about 30% to per-step allocation, so a mutable-local loop would likely reach 30-100 M/s [I].

Implications:
- A trusted Lean emulator running riscv-zkvm's own `step` is fine for runs up to about 10^7
  (under 30 s) but too slow for 10^9 (45 min per run).
- A UInt64-based Lean emulator covers 10^9 in minutes. Its refinement to `Rv64.step` would be
  provable cheaply because `UInt64` is a wrapper over `BitVec 64` [I]. Alternatively, it can be
  differential-tested against `riscv-zkvm-run` on short traces.
- Rust or QEMU tools are suitable as untrusted fast paths for agents, cross-checked against the
  Lean emulator on sampled inputs.

Note that sig.golf and ots.golf **never measure**: cycle bounds are *proved* worst-case
theorems, and the scored number is the submitted claim (`sig.golf scripts/run.py:21-25`).

## 4. Producing images and binding them to the theorem

- **sig.golf** [V]. Images are raw `List (BitVec 32)` literals in a generated file
  (`Images.lean:1`: "Generated by work/py/export_lean.py … Do not edit"). They are chunked into
  lists of 256 words, with `set_option maxRecDepth 8192`. The theorem `SigGolf.Challenge.certificate
  : SigGolf.Certificate submission 11712` is about the Lean constant `submission`, which contains
  the images. Binding is **by definitional identity**, with no digest. The comparator checks the
  exported statement against the trusted challenge and audits axioms. Since the decoder is in the
  trusted base, the bytes proven are the bytes a real core would execute.
- **ots.golf** [V]. `code : List Instr` (AST) is built from Lean macros. Again, binding is the
  Lean constant itself. An extra `image_size` theorem bounds `byteSize` (`docs/upper-riscv.md`).
  A sha256 of a canonical JSON export is recorded only for reproducibility (`NOTES.md`). The
  encoding and assembler are not in the trust path, because the competition machine *is* the AST
  machine.
- **From C, Rust or assembly** [V, probe]. `apt-get install gcc-riscv64-unknown-elf` (gcc 14.2.0)
  works. With `-march=rv64im -mabi=lp64 -mcmodel=medany -nostdlib -T link.ld` and text at
  `0x80000000`, data and stack in RAM at `0xa0000000`, a C guest runs unmodified on
  `riscv-zkvm-run`. However, `int32_t` arithmetic makes gcc emit `addw/subw/sllw/mulw/divuw/sraiw`
  (`cc/w.c`), which riscv-zkvm HEAD cannot decode. Compiled code therefore needs a model with the
  full W family (as sig.golf adds), or a compiler discipline that avoids them. LLVM/Rust
  `riscv64im` targets will also emit W-ops [I].
- **A recommended binding for recursion.fast** [I]:
  1. The image is a Lean `List (BitVec 32)` (+ data) constant generated from an ELF by a trusted
     script.
  2. CI regenerates it from the submitted ELF and checks byte equality.
  3. The claim records the sha256 of the ELF's loadable segments for the website.
  4. The theorem is stated about the constant, as in sig.golf.

## 5. Cost-model options and extensions

- **sig.golf** (`RULES.md:84-91`, `Riscv.lean:150-154, 214`) [V]:
  - 1 cycle per ordinary instruction;
  - **4** for `MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU` and their W forms;
  - HASH at 8 cycles per 64-byte compression, with no dispatch fee;
  - HALT 1;
  - a faulting instruction is charged 1;
  - plus a witness charge `⌈W/256⌉` (`Parameters.lean:92-93`).

  The score is `S × C`.
- **ots.golf RISC-V** (`RiscvMachine.lean:4-13`, `docs/upper-riscv.md`) [V]:
  - **1 cycle for every instruction including MUL/REMU**;
  - HALT 1;
  - HASH `max(1, ⌈bits/512⌉)`, with repeated queries charged again and no dispatch fee.

  The "hinted" track (`RiscvHint.lean`) charges only accepting runs (`CyclesAtMost` over
  `some (true, cycles)`), while the deterministic track charges every run. The leanISA track
  has its own weights (out of scope here; see R1).
- **Extensions** [V]:
  - riscv-zkvm's hand model is RV64IM without the W-ops (except ADDIW; `4634e41` adds 4 more,
    and sig.golf adds all 10 + SRAIW).
  - There is no Zbb, Zbc/Zbkc `clmul` or Zba anywhere in the executable or hand model.
  - ZisK CSR precompiles exist with concrete semantics: Keccak-f, SHA-256f, Arith256Mod,
    curve add/dbl. They set a precedent for a *field-multiplication precompile with concrete
    Lean semantics*.
- **Relevance to binary fields** [I]. Without `clmul`, a GF(2^128) multiply in RV64IM costs
  hundreds of cycles (bit-sliced or table-based). With `clmul`/`clmulh` (Zbc) it costs
  ≈4 clmul pairs plus reduction, ≈20-30 instructions. The measured Goldilocks
  mul+reduce+accumulate is **21 instructions per iteration** including loop overhead
  (`cc/field.c` → 21,000,024 retired for 10^6 iterations) [V]. If recursion.fast wants
  binary-tower designs (Binius-style) to compete, the contract must add Zbc (and probably Zbb)
  to the instruction type, its semantics and the decoder. This is about 4-10 constructors and
  roughly 50-100 trusted lines [I]. The alternative is a field precompile ECALL with a fixed
  cycle price, like sig.golf's HASH. Either choice changes which designs win and must be decided
  explicitly (PLAN critique item 10).

## 6. Implications for recursion.fast

1. **Model to pin.** Use the hand model `RiscvZkvm.Rv64` (`Instr`, `MachineState`,
   `execInstrBr`) as the instruction semantics, and wrap it in a **contract-owned** machine file
   as ots.golf and sig.golf do. That file holds the image, layout, admitted instructions, ECALL ABI
   (HALT, HASH or oracle, plus any transcript or field precompile) and cycle pricing. Do not import
   Sail, SailEquiv or Logic into the contract; the trust story is "hand model, proved equivalent to
   Sail for 51 instructions in riscv-zkvm".
   - Pin choice [I]. Pinning main HEAD `6810fc1` or later loses the 4 W-ops and
     `isValidOutputRange`/`memAccess` that ots/sig use from `4634e41`. Pinning `4634e41` keeps
     parity with them but sits on an unmerged branch with a forked lean-sail.
   - Recommendation [I]: own the W-op extension in the contract, as sig.golf does
     (`Riscv.lean:66-147`), on top of main's `execInstrBr`. Prefer **raw encodings + decoder** so
     that standard toolchains can produce images, and accept that the decoder is trusted and
     tested rather than proved against Sail.
   - Use a flat, contract-defined memory with explicit bounds and alignment, as sig.golf does,
     rather than riscv-zkvm's ZisK zone map.
2. **Proof burden** [I]. A SNARK verifier has three parts:
   - field and extension arithmetic routines: a few hundred static instructions each, verified
     once and used as BlockSpecs;
   - loops (sumcheck rounds, Merkle paths, FRI/WHIR folding, query loops) with invariants;
   - parsing and transcript code.

   Following sig.golf's architecture (reflective symbolic executor + `decide +kernel` + loop
   lemmas), the RISC-V refinement layer for a verifier of about 10-30k static instructions is
   plausibly 10-40k lines. Correctness of field-arithmetic routines (BitVec to `ZMod p`) needs
   `omega`/`bv_omega`/`ring` without `bv_decide`. The ArkLib-facing equivalence (Lean reference
   verifier = ArkLib verifier) is a separate and likely larger layer.
   - **Organisers should ship the tooling.** A reusable verified symbolic executor, block and
     loop lemmas, and a field-arithmetic library would make the baseline feasible and keep
     submissions short.
   - Keep blocks small. `runBlock` is superlinear: 161 s for a 128-instruction block.
   - Budget build memory. sig.golf serializes `decide +kernel` imports to bound parallel memory,
     and its hosted limit is 4 h / 24 GiB.
3. **Emulator for measurement** [V numbers, I recommendation]. If any cost is *measured*
   rather than proved (benchmark instances, honest-prover time, sanity checks of claims):
   - Use a Lean UInt64 emulator proved, or at least differential-tested, equal to the contract's
     `execute`. It runs at about 9 M instr/s in a naive version and plausibly 30-100 M/s
     optimised, so 10^9-cycle verifier runs take minutes.
   - `riscv-zkvm-run` (0.37 M/s) is fine only up to about 10^7.
   - Offer agents an untrusted Rust or QEMU fast path (100 M - 1 G instr/s) and cross-check it
     on sampled inputs.
   - Preferably, keep the score a **proved worst-case cycle bound**, as in both golf
     competitions, and use measurement only as a CI cross-check: run the emulator on the
     benchmark instances and require `measured ≤ claimed`.
4. **Toolchain conflict with ArkLib (v4.34.0)** [V facts, I recommendation]:
   - (a) Pin ArkLib `68726031f` (the last v4.33.1 commit, 2026-09-20). ots.golf already
     co-builds riscv-zkvm `4634e41` with ArkLib `dca90385` via leanerVM `8563b05` on v4.33.1. The
     cost is losing 359 newer ArkLib commits (including "native VCVio probabilities").
   - (b) Use ArkLib HEAD on v4.34.x and **vendor** riscv-zkvm's `Rv64/*` (+ `Interpreter/Decode`,
     optionally `Logic`) as source. I verified that these build unchanged on v4.34.1 (0 warnings;
     Logic has deprecation warnings only), since they are Mathlib-free and Sail-free. The cost is
     that SailEquiv cannot come along until Sail #1765 is fixed, and the contract's trust note
     must cite the riscv-zkvm revision whose SailEquiv proofs cover the copied definitions
     (`diff`-checked).
   - (c) Wait for riscv-zkvm to release on 4.34.x. Its README defers this pending upstream
     fixes, so the timeline is unknown.

   Recommendation: **(b) for the MVP**, with a CI check that the vendored files are byte-identical
   to a named riscv-zkvm commit. Revisit (a) if ArkLib HEAD turns out to be unstable (sorry
   status, see R4).
