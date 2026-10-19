<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A3-feasibility.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A3: Adversarial review of feasibility (proof burden, check time, toolchain, harness)

Reviewer: A3. Date 2026-10-10. Scope: `design/DESIGN.md` v0.1, D1 §1.4/§2/§6, D2 §2/§3.1/§6.5/§7, R1/R2/R4/R6
and the probes. **The orchestrator's mid-review changes are in force**:
- the relation is over **K = GF(2^64)** (`x^64+x^4+x^3+x+1`), with challenges in **E = K[y]/(y^3+y+1)**;
- the ISA gains **Zbc**;
- O1 (BabyBear) is void;
- the cost clause will probably be **"worst case over accepting runs + termination within a fuel cap"**;
- prover messages are **raw vectors `Fin len → F`** with contract-fixed challenge shapes, and `Agrees` must hold for **all oracle contents** (A1/A2).

New measurements are in `probes/a3-probes/` (`RESULT.md`). Labels:
- **[V]** I ran or read it;
- **[I]** inference or estimate.

## 0. Verdict

**Conditionally feasible.**

**The MVP baseline.** It can be proved in about **3–4.5k Lean lines** and checked in **about 20–25 min cold / about 8 min
warm** on this machine, which is inside the 1-hour requirement. D2's 3–5k estimate survives calibration. This holds only
if three things happen before P3:
1. the machine/ABI is frozen (today three incompatible machines exist, C1);
2. the cost and termination quantifiers stop ranging over adversarial *index* data and raw tapes (C2);
3. the organisers ship a RISC-V proof library (C3). Stock tactics over the riscv-zkvm hand model hit several hard
   traps, one of which costs 266 s of kernel time and then fails on a single JAL step.

**A competitive (Spartan/GKR + WHIR-class) entry.** Its proof burden is **45–100k lines** even with organiser
libraries, and **100–170k** without them, i.e. sig.golf scale. The critical path is a hash-based PCS with RBR
*knowledge* soundness over binary-field RS codes. It exists nowhere (ArkLib: WHIR absent, FRI/Binius unproved; leanerVM:
WHIR "not built" and targeted only at RBR *soundness*). Without organiser-built L3–L5 (§4) and a reference succinct
submission, I expect the leaderboard to stall at the trivial or hybrid baseline for months.

**Check budgets.** T1/T2 (3 h / 8 CPU / 48 GiB) suffices for submissions up to about 2–3× sig.golf, but the
budget must be specified in CPU time, single-threaded replay time and per-process memory, not lines (M4).

## 1. Ranked findings

| ID | Sev. | Finding | Fix |
|---|---|---|---|
| C1 | critical | Three incompatible machines: `baseline.S`, DESIGN §3 and the P1 `Machine.lean` | Freeze one machine spec, then rewrite and re-measure the baseline |
| C2 | critical | The baseline's claimed cost bound is false under the "∀ tape, ∀ O" quantifiers; all-raw-tape termination is costly | Honest header/VK/IDX in every machine clause; fuel exhaustion = reject |
| C3 | critical | No importable RISC-V proof tooling; stock tactics hit hard traps (measured) | Organiser library L0–L2 before P3; baseline built on it |
| M1 | major | 4 GiB data memory cannot hold the binary-field baseline's index at 2^24 | Memory bound 2^36 with a sparse emulator, or streaming QUERY |
| M2 | major | A competitive entry is sig.golf-scale; the PCS with RBR-KS is the critical path and exists nowhere | Organiser library L3–L5 + reference succinct submission; T0 season first |
| M3 | major | Comparator replay vs declaration-local options and computational certificates in the trusted closure | P1 runs the real comparator on the full closure; `pratt`; leanchecker patch if needed |
| M4 | major | Check budgets stated in lines; memory per process; single-threaded replay floor | Budgets in CPU-h / replay-h / RSS; serialise heavy modules |
| M5 | major | O5: T0 has no query semantics | Contract-owned query-tree type `QProg` (§6.2), also usable as the T1 refinement midpoint |
| M6 | major | Toolchain: binary-field components live in leanerVM (v4.34.1, ArkLib 7653a90), not at the DESIGN pin (v4.34.0, db7005f) | Pin v4.34.1 + leanerVM's dependency set, or port; decide now |
| m1 | minor | 1 MiB image literal: 194 s, 8.9 GB in one process | Budget it; separate module; chunk-wise admission |
| m2 | minor | Demonstration runs need `IDX i`: running a candidate's Lean indexer or trusting the native one | Computable-indexer rule + sandboxed eval, mismatch = flag |
| m3 | minor | O7: Lean emulator at 9 M/s, about 11 min per 2^24 baseline run; needs Zbc and sparse memory | Optimised UInt64 emulator (30–100 M/s), differential tests |
| m4 | minor | sig.golf's reflective executor relies on `implemented_by`/`evalExpr` metaprograms | Explicit policy: allowed in the organiser library (kernel re-checks); decide for submissions |
| n1 | note | Binary fields *lower* the proof burden of field arithmetic | Define `clmul*` via CompPoly `carryLessMul` |
| n2 | note | O4: accepting-runs-only saves less than expected once C2's fix is in | Adopt it with fuel exhaustion = reject and no separate termination theorem |
| n3 | note | D1's KoalaBear `norm_num` probe did not succeed | Correct D1 Appendix A |

### C1 (critical): three incompatible machines

**Evidence [V]:**
- **`probes/d2-probes/guest/baseline.S`** (the 61-instruction "baseline image" in DESIGN §8):
  - expects `a0..a5` = pointers/lengths of vk, x and tape *in memory*;
  - reads the CSR index from `vk`;
  - does **no QUERY**;
  - accepts with `a0 = 0`;
  - is BabyBear `mul`/`remu`.
- **DESIGN §3 / D2 §2.3–2.4**:
  - a tape layout (`sz ‖ VK ‖ x ‖ challenges`);
  - oracles reachable only by `QUERY` (`t0 = 1`), HALT `t0 = 0` with `a0 = 1` = accept;
  - 4 GiB memory.
- **`probes/p1-contract-toolchain/RecursionFast/Machine.lean`** (304 lines, the concurrent P1 skeleton) is
  sig.golf's machine:
  - `t0 = 0` HASH, `t0 = 1` HALT (success iff `a0 = 0`), `t0 = 2` SAMPLE;
  - **16 MiB** memory;
  - no QUERY, no Zbc;
  - it was failing to build when I read it (`build1.log`: `HAdd (QueryImpl …)` instance).

**Consequences.**
- None of the three is the machine the baseline will be certified on.
- The baseline's cycle formula `18·nnz + 54·N + …`, the "61 instructions" and D2's proof estimate are measurements of
  an image that does not exist under the contract.
- With K = GF(2^64), the inner loop becomes `ld`/`clmul`/`clmulh`/`xor` with lazy reduction.
- Elements become 8 bytes, which changes `B_k`, the QUERY charges and the memory footprint (M1).

**Fix.**
1. Write a one-page machine specification before any more P1/P3 work: syscall numbers and arguments, accept
   convention, tape layout, QUERY leaf write semantics (closed form, see C3), memory size, Zbc semantics, weights.
2. Make P1's `Machine.lean` implement exactly that.
3. Rewrite `baseline.S` against it (binary field, 2 QUERYs or a streaming loop, M1), re-measure with `cyclemu`,
   and recompute D2 §7.1. [I] Estimate with lazy reduction: about 20 cycles per nonzero + about 150 per row. That is
   about 8–9×10^9 cycles at the 2^24 caps, versus 6.0×10^9 for BabyBear.

### C2 (critical): the cost and termination quantifiers make the baseline's bound false and its proof expensive

**What the clauses say.** D2 §3.1 `CyclesAtMost` quantifies over "∀ tape with header sz, ∀ O respecting the declared
oracle lengths". D1 `Terminates` quantifies over "every raw tape and oracle function". The A1/A2 refinement is that
`Agrees` holds "for all oracle contents".

**Why the baseline's bound fails [V, by reading `baseline.S`].** Trip counts come from data:
- the row count `N` comes from `VK`, and
- each inner loop count `cnt` comes from the index.

With an adversarial VK/IDX, `cnt` is any 32-bit value, and the loop walks past its buffer until a load faults at the
end of memory. The worst case is therefore set by the memory size, not by `nnz`: about `2^32/8 · 18 ≈ 10^10` cycles in
every class, including 2^16. So the official claim `C_16 = 2.4×10^7` is **not a theorem** about this image. Proving
*any* bound needs a ranking argument ("the cursor strictly increases and faults at `MEMORY`") on every loop. Adding
cumulative `cnt ≤ nnz` and `col < n` checks restores the closed form, but it costs about 2 cycles per nonzero and about
400–800 extra proof lines [I].

**Why honest index data is the right model.** `VK i` and `IDX i` are outputs of the deterministic Lean indexer. The
harness computes them and absorbs `MTroot(IDX i)` into the FS state (D1 §3.1); no adversary chooses them. `Secure` and
`Agrees` are already stated for `IDX i` only (D1 §1.4).

**Fix (no loss of meaning).** Quantify every machine clause over:
- honest preprocessing: `sz` admissible, header = `ser sz`, `VK = VK i`, oracle 0 = `IDX i` for some index `i` of the
  class;
- adversarial public input `x`, **all raw prover-oracle contents** (the A1/A2 rule) and all challenge vectors.

Make fuel exhaustion a reject (D2 §2.3 already says so) and **delete the raw-tape `Terminates`** (see O4 in §6.1). The
DoS bound on rejecting runs is then the contract's fuel constant, enforced by construction.

**What this buys.** With raw vectors and contract-fixed shapes, prover data never determines a loop trip count in any
sensible verifier; trip counts come from `sz` and `VK i`. Cost proofs then follow the loop invariants with no ranking
arguments. Binary fields add a further simplification: every 64-bit word is a K element. So "all raw oracle contents"
equals "all well-typed transcripts", and no canonicity checks are needed (unlike BabyBear's `< p`).

### C3 (critical): there is no proof tooling, and the hand model has traps

**What exists [V].**
- **riscv-zkvm `Rv64.Logic`.** `runBlock` costs 161 s at 128 instructions (R6 §2.1). ots.golf's and sig.golf's
  contracts do not import it.
- **sig.golf's reflective executor** (`SigGolfCandidate/Rv/*`, 2,289 lines) is *submission-side*, written against
  sig.golf's `ordinaryStep`/`execute` in `OracleComp`, and uses `implemented_by`/`evalExpr` (m4).
- **ots.golf's `Refines` calculus** (about 3.5k lines) is written against ots.golf's machine.

None is importable as is.

**Calibration (`probes/a3-probes/InnerLoop.lean`, 332 lines, proved) [V].** I proved the baseline's inner loop
(12 instructions, 18 cycles per iteration) over `execInstrBr` with stock tactics:
- per-iteration semantics;
- exact cycle count `18n+1` for all `n`;
- the no-overflow invariant;
- the `ZMod p` meaning of the accumulator.

It checks in about 10 s. Cost: about 8.5 lines per instruction in forward style, plus 48 lines of loop induction and
55 lines of arithmetic bridge. The traps met on the way, each of which an agent will meet too:

1. **Naive unfolding diverges.** `simp only [run, execInstrBr, …]` over 12 steps did not finish in more than 5 min.
2. **A concrete JAL offset breaks `whnf` and the kernel.** `(execInstrBr s (.JAL .x0 1000)).mem = s.mem` by `rfl`
   hits "maximum recursion depth". With offset `0` or `4`, or a symbolic offset, it is instant (`Jal5.lean`). The same
   goal by `simp [execInstrBr]` elaborates, then **kernel type checking takes 266 s and fails with "deep recursion"**
   (`Jal2.lean`). This one line made the whole 12-step proof take 5 min and then fail. The workaround is per-instruction
   lemmas with symbolic immediates, instantiated afterwards.
3. **`decide` on BitVec constants** (`signExtend21 0x1FFFD4 = -44`) causes kernel deep recursion. `unfold; rfl` works.
4. **Literal spelling.** Immediates written `0xFFF` are `OfNat` terms that simp rewrites to `4095#12`, so lemmas
   stated with the source spelling silently never fire.
5. **Primality by `norm_num`** needs a declaration-local `maxRecDepth` (M3).

This is a toy machine: no decoder, no bounds or alignment checks, no QUERY. The real proof adds decode facts for raw
words and `accessValid` obligations; for example `z[col]` is in range only because `IDX i` has `col < n`.

**Fix.** The organisers ship library L0–L2 (§4) **before** the baseline is proved, and the baseline is proved *with*
it as the published starter:
- per-instruction lemmas with symbolic operands for every `Instruction` of the contract (incl. W-ops, Zbc);
- decode lemmas for raw words;
- closed-form QUERY/tape readback lemmas;
- a block executor (sig.golf `symRun` port);
- counted-loop and early-exit combinators with cost threading.

In the contract, QUERY's memory effect must be a **closed form**, `mem' a = if dst ≤ a < dst+8·len then leaf … else
mem a`, not a fold of `setMem` over `2^28` words (`writeWords`). Otherwise every readback lemma is an induction over
the leaf.

### M1 (major): 4 GiB is not enough for the binary-field baseline at 2^24

At the class caps (`nnz = 2^28`, `m = 2^24`), the index must be a raw vector of 8-byte K elements (A1/A2 rule), with
`(col, val)` per nonzero and 3 counts per row. That is `2^28·16 + 3·2^24·8 ≈ 4.4 GiB` for the index alone, plus
128 MiB for `z`. It does not fit D2 §2.3's `2^32`-byte memory, so the "whole-oracle QUERY" baseline cannot run at 2^24.

**Fix**, either:
- (a) set `MEMORY_BYTES = 2^36`. The Lean model is a function, so this is free; the trusted emulator must use sparse
  or lazily allocated pages. This is the recommended option, since it keeps the baseline at 2 QUERYs; or
- (b) stream the index with a fixed leaf size (e.g. 2^16 elements per leaf). This adds an outer loop to the image
  and about 300–500 proof lines.

Either way D2 §7.1's `B_k` and score must be recomputed for 8-byte elements.

### M2 (major): competitive proof burden and the critical path

**Spec security for a Spartan/GKR + PCS design over K/E, in the unconditional track.**

| Component | Status [V: R4 §6, R5 §3.1] | Lines if built [I] |
|---|---|---|
| sumcheck RBR-KS | legacy ArkLib tainted; native ArkLib sumcheck soundness-only; **leanerVM `ToArkLib/Sumcheck*` built, over K/E** | port 2–4k |
| batching, GKR grand product, query-check, append (#615 port) | **built in leanerVM** | port 2–4k |
| Spartan reduction + sparse matrix evaluation (SPARK/memory checking via grand product) | ArkLib skeleton (4 sorries) | 5–15k |
| PCS: WHIR/BaseFold/FRI-Binius RBR-**KS** over additive RS domains | ArkLib: WHIR absent, FRI and Binius unproved (11/54 baseline entries); leanerVM: WHIR "not built", targeted at RBR *soundness* for the list relation, not KS (R5 §3.2) | 15–40k (UDR) |
| proximity gaps | UDR correlated agreement for lines sorry-free; Johnson CA `sorry` | (included above) |

**RISC-V side** for a verifier of about 3–10k static instructions:
- E arithmetic: 6–9 clmul pairs + reduction per E multiply;
- sumcheck round checks, eq/MLE evaluation, folding, query-leaf checks;
- refinement with L0–L2 tooling: 10–30k lines; without it, 40–80k (sig.golf's refinement layers were 33k for simple
  algorithms, R2 §3.2);
- cost bounds: 2–5k.

**Totals [I]:**
- with organiser libraries: 45–100k lines;
- without: 100–170k lines.

**Is it realistically entered?** sig.golf shows that agents *can* produce and maintain a 154k-line proof (2.8 CPU-h,
R2 §3.5). So a determined team can enter, but only after the PCS exists.

**The critical path is the PCS**, with knowledge soundness in the UDR, over binary-field RS codes. A competitive
unconditional entry also pays the UDR query multiplier (S7 ≈ 3× S2 in D2 §7.3).

**A cheaper interim PCS** is a Ligero/Brakedown-style tensor-code commitment. It uses ArkLib's sorry-free DG25 tensor
gaps and AHIV22 lemma, and its proof is plausibly 5–10k lines [I]. My back-of-envelope cost under this cost model at
2^24 is about 3×10^7 cycles, the same order as D2's S1 [I, unmodelled; D2 should run it through `trajectory.py`].

**Fix:** the organiser library plan in §4, a reference succinct submission (L5), and a T0-first season (S6).

### M3 (major): comparator replay against the trusted import closure

**Evidence [V]:**
- `Nat.Prime 2013265921` **and** KoalaBear `Nat.Prime 2130706433` by `norm_num` fail with "(kernel) deep recursion"
  at default settings, in both environments. Re-running `probes/d1-probes/Prime.lean` exits 1, so D1 Appendix A's
  "7.1 s" was not a success.
- Both pass with `set_option maxRecDepth 100000 in`. R3 records that **comparator's fresh-environment replay ignores
  declaration-local recursion limits**, and that the proximity prize had to swap comparator's replay for `leanchecker`
  because of CompPoly's KoalaBear Ext6 certificate (63-line patch, `notes/R3-proximity-prize.md:229-235`).
- The new field stack has the same shape:
  - CompPoly `BF64/Basic.lean` sets `maxRecDepth 4000`;
  - `BF64/BaseCertificate.lean` is a 552-line generated Rabin certificate;
  - `Ext3.lean` uses `decide +kernel`.
- `lake env leanchecker CompPoly.Fields.Binary.BF64.{Basic,BaseCertificate,Ext3}` passes (1 min 49 s). Comparator
  itself was not run.
- CompPoly's `pratt` proves BabyBear primality at default limits in 6.3 s, so certificate-style proofs avoid the issue.

**Fix:**
- P1 must run the **pinned comparator** end to end on a challenge that imports the full trusted closure (contract
  + `CompPoly.Fields.Binary.BF64.Ext3` + ArkLib `ProtocolSpec` + Rv64) and on the baseline. If it fails, adopt the
  proximity prize's leanchecker-replay patch and record it in the trusted-surface list (D1 §6.2 item 2).
- Ban declaration-local `maxRecDepth`/`maxHeartbeats` in contract files.
- Use Pratt or Rabin certificates that replay at default limits.
- Add an agent-facing rule: "a proof that needs `set_option maxRecDepth … in` may fail replay; check with the
  harness before submitting".

### M4 (major): check-time budgets

**Rates [V/I].**

| Source | Measurement |
|---|---|
| sig.golf | 154.5k lines: 2.83 CPU-h elaboration (10.5× parallel on 32 cores) + 23 min single-threaded export/replay |
| sig.golf `Verify/` | 9.5k lines: 1,252 s CPU, i.e. about 2.2 CPU-min per 1k lines for refinement proofs (twice the average) |
| ots.golf record | 20.6k lines: 25 min on this machine, dominated by one 176-line `decide +kernel` module (472 s) |
| my probe | about 330 lines in about 10 s |

**T1/T2 at 3 h / 8 CPU / 48 GiB [I].**
- Elaboration at about 6× effective parallelism on 8 CPUs: 2.2 CPU-min per 1k lines gives about 22 min of wall time
  per 100k lines.
- Replay: about 9 s per 1k lines plus the Mathlib/ArkLib closure export, about 15 min per 100k lines.
- So 100k lines take about 40 min and 200k about 75 min: inside 3 h. Margin about 2× at 250k lines.
- **Line counts are a poor proxy:** a single `decide +kernel` table can cost more than 10k ordinary lines.

**Memory.**
- One 1 MiB image literal module: 8.9 GB peak (m1).
- sig.golf aggregate PSS: 11.3 GB.
- Eight concurrent heavy modules at 6–9 GB each can exceed 48 GiB.

**Fix:**
- State budgets as (i) total elaboration ≤ 16 CPU-h, (ii) export + replay ≤ 75 min single-threaded,
  (iii) peak RSS ≤ 48 GiB aggregate and ≤ 16 GiB per process, (iv) 3 h wall.
- Run Lake with `-j8` and a per-process memory limit.
- The renderer emits the image literal as its own module.
- Keep sig.golf's "serialise `decide +kernel` families through the import graph" advice in AGENTS.md.
- MVP: "< 15 min" (D2 §7.2) is achievable **warm only**; cold is about 20–25 min (§3.3).

### M5 (major): O5, T0 needs a query semantics; proposed resolution

D1's verifiers are pure functions of the full transcript, so "number and price of queries" is undefined. ArkLib's
`numQueries` is `sorry` (R4 §9). VCVio `IsQueryBound` counts calls, not depth-weighted prices, and drags `OracleComp`
into the trusted text.

**Proposal: a contract-owned query tree of about 40 trusted lines.** Uncompiled sketch:

```lean
inductive QProg (O : Fin k → Type) (α : Type) where
  | done  : α → QProg O α
  | query : (j : Fin k) → (leaf : ℕ) → (Leaf j → QProg O α) → QProg O α   -- one priced QUERY
def QProg.eval  : QProg O α → (∀ j, Oracle j) → α
def QProg.price : QProg O α → (∀ j, Oracle j) → ℕ        -- Σ P_Q(j) along the path (adaptive)
-- T0 certificate clauses (for every admissible sz, index i, x, all raw prover-oracle contents, all challenges):
--   eval (Vq sz (VK i) x ρ) (oracles (IDX i) msgs) = V (VK i) x (IDX i) (transcript msgs ρ)       -- QAgrees
--   price … ≤ Q_k                                                                                  -- QCost
```

Properties:
- Local computation is free.
- Queries may be adaptive.
- `price` is exactly the T1 QUERY charge, so T0 is a lower bound for T1 by construction.
- The same `QProg` can serve as the **midpoint of the T1 refinement**: prove spec = `QProg` once (protocol-level, no
  RISC-V), then machine = `QProg` *between queries*. This splits machine proofs at syscalls, which is where the
  executor stops anyway.

T0 thus reuses D1's definitions unchanged and adds no probability.

### M6 (major): toolchain pin vs the binary-field components

With K/E, the most valuable existing components are leanerVM's `ToArkLib/*`:
- sumcheck (plain/normalized), batching, GKR grand product, fingerprint, query-check;
- the KnowledgeAppend port (582 lines).

They are built on **Lean v4.34.1, ArkLib 7653a90**, prebuilt on this machine. DESIGN pins ArkLib db7005f on
**v4.34.0** (P1 uses v4.34.0). The legacy layer is byte-identical between the two (R4 §1). riscv-zkvm `Rv64` builds
unchanged on v4.34.1 (R6 §1.3). The A3 probe environment (v4.34.0) builds Rv64 in 60 s.

**Fix:** pin **v4.34.1 + leanerVM's mathlib/ArkLib/VCVio/CompPoly set**, so that leanerVM components are importable
(or vendorable) without a port. Then confirm with R8 that CompPoly's BF64/Ext3 at that pin has the `Field` instances
and lemmas (`toQuot_mul`, `reduce`, `foldStep`) used in n1. Decide before P1 freezes, because a later bump costs every
submission a port (ots.golf: 46 pin changes in 10 days; sig.golf carries a 1.8k-line transfer layer).

### m1 (minor): image literals

**Measured** (`LitDefs16/18.lean`, 256-word chunks, balanced `++` tree, sig.golf style):

| Words | Elaboration | Peak RSS |
|---:|---:|---:|
| 2^16 | 56 s | 3.3 GB |
| 2^18 (the 1 MiB cap) | 194 s | 8.9 GB |

`length = 2^16 := by decide +kernel` adds 25 s and peaks at 6.0 GB. Comparable to sig.golf's 183 s for 146k words.

**Fix:**
- Render images in a separate module.
- State `byteSize` admission per chunk (sig.golf `Submission.lean:71-90`).
- Count the literal in the budget (about 3–5 min elaboration + replay at the cap).
- Optionally lower the cap for T1 to 512 KiB. Unrolled tables are the only reason to go near 1 MiB.

### m2 (minor): the indexer in demonstration runs

The trusted emulator needs `IDX i` bytes. Getting them means either running the candidate's Lean indexer, which is
candidate code (fine in the sandbox, but noncomputable indexers cannot run), or trusting the native indexer, whose
mismatch D2 §2.1 only "flags".

**Fix:** require `I` computable; evaluate it in the sandbox on the benchmark (compiled, not interpreted); a mismatch
blocks the record. It never blocks the proved score.

### m3 (minor): O7, the 2^24 baseline demonstration

[I] The binary baseline at the 2^24 caps is about 5–6×10^9 *instructions* and about 4.5 GiB touched memory. At 9 M/s
(R6 §3) that is **about 11 min per run**, plus software `clmul` in the emulator: 2^29 clmul-class operations at about
100 ns is about 1 min. Acceptable for a few hidden instances, but:
- the emulator needs sparse memory (M1) and Zbc;
- it must be refined to, or differential-tested against, the contract's `execute`;
- a mutable-state UInt64 loop at 30–100 M/s (R6 §3) would bring a run to 1–3 min.

The native "prover" is the identity, but the harness must Merkle-hash about 4.5 GiB for the FS prefix: seconds.

### m4 (minor): metaprogramming policy

The only proven high-throughput technique, sig.golf's `sym_eval`, uses `@[implemented_by]` + `evalExpr` and
re-checks the result with `Eq.refl` in the kernel. ots.golf scans submissions *against* such constructs.

**Fix:** allow them in the organiser library; decide explicitly for submissions. The kernel replay makes it sound;
the sandbox makes it safe.

### n1 (note): binary fields simplify the arithmetic bridge

CompPoly defines `BF64.mul a b = ofBitVec (reduce (carryLessMul (w := 128) a b))`, with
`reduce = lowHalf ∘ foldStep ∘ foldStep`, where `foldStep` is a carry-less multiply of the high half by `0x1B`
(`BF64/Impl.lean:120`, `Reduce.lean:167`) [V]. A RISC-V routine (`clmul`/`clmulh` of the operands, then two folds via
`clmul`/`clmulh` by `0x1B`) mirrors this definition step for step.

If the contract **defines** `clmul`/`clmulh`/`clmulr` as the halves of `carryLessMul (w := 128)`, the refinement is
nearly definitional. No overflow bounds are needed, unlike the 55-line BabyBear bridge in my probe. Lazy reduction
(XOR-accumulate 128-bit products, reduce once per row) needs only linearity of `reduce`, which follows from
`toQuot_add`/`toQuot_mul` [I].

Two cautions:
- never `decide` a concrete `carryLessMul`: a `Fin.foldl` over 64 BitVec-128 steps in the kernel;
- QEMU-differential-test the decoder clauses for Zbc.

E = GF(2^192) multiplication should be an organiser-verified routine (L2).

## 2. What the baseline must prove (with the decisions in force)

**Spec side.** `pSpec` has one round, P→V, message `z : Fin (1+nx+nw) → K` (raw vector), no challenges. The indexer
gives:
- `VK i = (m, n)`;
- `IDX i` = CSR as a raw vector of K elements (counts, `(col, val)` pairs).

The verifier is `decide (z 0 = 1 ∧ z[1..nx] = x ∧ (A *ᵥ z) * (B *ᵥ z) = C *ᵥ z)`. Obligations:
- perfect completeness;
- RBR-KS with ε = 0 (KSF `Holds s (tr 0)`, no bad challenges; D1 `toy_secure` is the template);
- cap and admission.

**Machine side,** for every admissible `sz`, `i`, `x`, every raw `z` (C2 quantifiers):
- `Agrees`: the image's HALT decision = the spec decision. This includes every early exit:
  - length mismatch is impossible (shapes are contract-fixed);
  - `z[0] ≠ 1`, `x` mismatch and the first failing row each reject, and match the spec's `∀`.
- `CyclesAtMost` on accepting runs: closed form in `sz`.
- `BytesAtMost`, image size, layout.

**Lemmas behind them:**
- (a) **CSR lemma:** Σ over the serialised row = `(A *ᵥ z) r` (Finset sum over support);
- (b) QUERY readback: memory after the 2 QUERYs holds the serialisations;
- (c) the arithmetic bridge (clmul/XOR/`reduce` ↔ `BF64` ops);
- (d) per-block semantics for the 6 blocks and 4 loops (prologue + 2 QUERYs, x-check loop, row loop, matrix loop,
  nnz loop, row check, accept/reject);
- (e) loop invariants:
  - x-loop: "prefix equal";
  - rows: "all rows < r hold";
  - nnz: accumulator = partial sum;
- (f) cost threading;
- (g) decode facts for 60–70 raw words.

## 3. Realistic baseline proof plan

### 3.1 Effort

| # | Component | Lines (with L0–L2) | Lines (without) | Basis |
|---|---|---:|---:|---|
| 1 | Spec, completeness, RBR-KS, cap, non-vacuity | 200–350 | 200–350 | D1 `LocalDefs` toy (525 lines total incl. defs), R4 probe 50 lines |
| 2 | CSR serialisation + sum lemma (a) | 200–400 | 200–400 | Finset sum over support, Fin/raw-vector plumbing |
| 3 | Tape/QUERY readback, layout, decode facts (b, g) | 100–200 | 500–900 | library lemma vs hand proofs per word |
| 4 | Block proofs, about 65 instructions (d) | 150–300 | 550–800 | probe: 103 lines per 12 instructions forward style; executor about 3× shorter |
| 5 | Loop inductions, 4 loops (e) | 200–350 | 250–400 | probe: 48 lines per loop |
| 6 | Arithmetic bridge, K ops (c) | 50–100 | 150–300 | n1; probe's ZMod bridge is 55 lines |
| 7 | Decision composition incl. all early exits | 400–700 | 500–800 | casework over 5 reject sites vs spec `∀` |
| 8 | Accepting-run cost closed form + byte bound | 150–300 | 200–400 | threaded through invariants |
| 9 | Admission, image equality, assembly | 50–100 | 100–200 | `decide` per chunk, `rfl` |
| | **Total** | **1.5–2.8k** + library | **2.7–4.5k** | D2's 3–5k is credible for the hand route |

**Elapsed effort [I]:**
- L0–L2 first: 3–6 organiser agent-weeks;
- then the baseline: about 1 agent-week;
- hand route: 2–3 agent-weeks, with high variance from the C3 traps.

### 3.2 Check time on this machine

| Step | Estimate |
|---|---|
| Submission elaboration (4k lines at the probe's rate of about 30 lines/s) | 2–5 CPU-min |
| Comparator export + replay of the ZMod/Finset/Matrix + BF64/Ext3 + ArkLib `ProtocolSpec` + Rv64 closure (ots.golf replay 190–320 s for 22k declarations) | 4–8 min |
| Trusted build, warm (contract + Rv64 1 min; ArkLib subset + VCVio + CompPoly 5 min, R4 §7) | 6–8 min |
| Trusted build, cold (`cache get` 4–5 min + the above) | 10–13 min |

Total: about 8 min warm, about 20–25 min cold. Both are inside the 1 h requirement.

## 4. Organiser library plan (untrusted, kernel-checked, importable)

| Lib | Content | Size [I] | Needed for | Order |
|---|---|---:|---|---|
| L0 Machine facts | symbolic-operand step lemmas for every contract instruction (incl. W, Zbc), raw-word decode lemmas, `accessValid` lemmas, closed-form QUERY/tape readback, layout | 1.5–2.5k | baseline | 1 (with P1) |
| L1 Executor + combinators | port of sig.golf `symRun`/`symRun_sound`/`BlockSpec`/`Steps.iterate` to the contract machine; counted-loop, early-exit-loop (`∀ ↔ no reject`) and `QProg`-segment combinators; accepting-run cost judgement (sig.golf `Good`) | 3–5k | baseline (optional), every T1 entry | 2 |
| L2 Field routines | verified RISC-V routines + specs + cycle counts: K mul (clmul + 2 folds), lazy-XOR accumulate + reduce, E = K[y]/(y^3+y+1) mul/square, inverse-by-hint check, eq(r,·) and Lagrange evaluation loops | 2–4k | T1 succinct | 3 |
| L3 IOP components on local defs | leanerVM sumcheck/batch/GKR/query-check ported or bridged to D1's `RbrKS`/`KSF`; sequential composition (append) and D1 G2 frame rule | 3–7k | T0/T1 succinct | 3 (parallel) |
| L4 PCS | UDR, knowledge-sound, hash-based PCS over binary RS (additive domains), from ArkLib UDR correlated agreement; interim option a tensor-code (Ligero/Brakedown) PCS from DG25 | 15–40k (interim 5–10k) | any succinct entry | **critical path** |
| L5 Reference succinct submission | Spartan-or-GKR + L4, T1 certified | 10–20k | proves viability; seeds the leaderboard | 4 |
| L6 Harness | renderer about 0.4k Py; sampler about 0.15k (bias-free for K/E: any 64/192 hash bits are elements); trusted emulator about 0.6k Lean + diff tests about 0.3k; native-prover sandbox + round IPC + Merkle/FS about 1k; benchmark generators 2–4k (binary-field R1CS: reuse leanVM's) | 4.5–6.5k | launch | parallel |

**Critical path:** L4 → L5. L0–L1 gate the MVP; L2–L3 gate any succinct T1 entry.

## 5. Check-budget risks (summary)

The risks, each detailed in §1:
- the single-threaded replay floor (about 9 s per 1k lines);
- per-process memory from literals and `decide +kernel`;
- comparator ignoring local options (M3);
- line counts being a poor proxy (M4).

The 3 h budget itself is adequate.

## 6. Open items

### 6.1 O4: accepting runs (sig.golf) vs all runs, after the C2 fix

**Under "∀ raw tape, ∀ oracle" (D1/D2 as written).** All-runs costs every data-driven loop a ranking argument plus
bound checks in the image. My estimate is +20–40% of the machine-level proof and +10% cycles for the baseline [I].

**After C2's fix** (honest header/VK/IDX, raw prover vectors, fixed shapes), the two clauses differ only on early
rejects, whose cost is ≤ the accepting path's in any monotone verifier. The difference is then about 5–15% of the
machine proof: cost threading on the reject exits.

**The real saving from the sig.golf form comes from deleting the termination theorem**, *if* "termination within a
fuel cap" means fuel exhaustion = reject:
- `execute` always returns within fuel, so nothing is proved;
- `Agrees` already forces honest (spec-accepting) runs to halt before the fuel runs out.

If instead "termination" is a theorem that every run HALTs or faults before the fuel cap, it is an all-runs bound with
a looser constant, and its burden is essentially that of all runs (ranking arguments again).

**Recommendation:**
- accepting-run `CyclesAtMost`;
- no separate termination theorem;
- the fuel constant (e.g. 2^36) as the DoS bound by construction.

Rejecting runs do not enter recursion (only accepted proofs are re-verified), so nothing of value is lost.
Non-vacuity: completeness + `Agrees` guarantee that honest runs accept, so the accepting-run bound is never empty.

### 6.2 O5

Resolved by `QProg` (M5).

### 6.3 O7

Acceptable with M1 and m3 fixes. Optimise the emulator before hidden-instance runs at 2^24.

## 7. Simplifications that keep the competition's value

| # | Simplification | Proof saving | Value lost | Recommend |
|---|---|---|---|---|
| S1 | Honest preprocessing in all machine clauses (C2) | large (ranking arguments, bound checks) | none (the index is not adversarial) | **yes, v1** |
| S2 | Accepting-run cost, fuel exhaustion = reject, no termination theorem (O4) | 5–15% + the termination theorem | DoS bound becomes the fuel constant | **yes, v1** |
| S3 | Fixed shape per class: the harness pads to `(2^k, 2^k, 2^(k+4))` with a contract-proved `pad` preserving satisfiability (ArkLib `pad_preserves_relation`); certificates only at the class shape, `nx ≤ 2^16` kept | large for succinct designs: WHIR/sumcheck parameters become constants, errors by `norm_num`, no "∀ sizes ≤ cap" casework | uniformity below the cap (scores are taken at the caps anyway); small instances pay padding, which is the cost model's view already | **yes, v1** |
| S4 | Organiser-verified field routines as admitted building blocks (L2) | the hardest BitVec↔field proofs | none (agents may still hand-roll) | **yes** |
| S5 | Field precompile ECALLs instead of S4 | more than S4 | changes design rankings; a new trusted price | no (S4 suffices) |
| S6 | T0 (Lean-only, `QProg`) season first; T1 opens when L1–L2 ship | lets protocol and security work start with 0 RISC-V proof | none; T0 records carry into T1 via the `QProg` midpoint | **yes** |
| S7 | A verifier IR/DSL with a verified compiler to RV64IM | an order of magnitude on refinement | low-level golf, the competition's RISC-V flavour; compiler 5–15k lines | later, optional route alongside raw images |
| S8 | Interim tensor-code PCS track until L4 exists | moves the critical path from 15–40k to 5–10k lines | none if flagged | **yes** |

## 8. Prioritised fix list

1. **Freeze the machine spec** (C1): syscalls, accept convention, closed-form QUERY, `MEMORY_BYTES = 2^36` with a
   sparse emulator (M1), Zbc defined via `carryLessMul` (n1). Align P1's `Machine.lean`; rewrite `baseline.S` for K;
   re-measure; update D2 §7.1 and DESIGN §8.
2. **Restate the machine clauses** (C2, S1, S2): honest header/VK/IDX; all raw prover vectors and challenges; `Agrees`
   + accepting-run `CyclesAtMost` + `BytesAtMost`; fuel exhaustion = reject; delete raw-tape `Terminates`.
3. **Pin the toolchain** (M6): v4.34.1 + leanerVM's dependency set; confirm the BF64/Ext3 API with R8.
4. **Comparator end-to-end in P1** (M3) on the trusted closure + baseline; patch to leanchecker if needed; contract
   uses `pratt`/Rabin certificates and no local options; correct D1 Appendix A (n3).
5. **Ship L0–L1, then prove the baseline with them** (C3), avoiding the documented traps (symbolic-immediate lemmas,
   no `decide` on BitVec, `n#w` literals).
6. **Adopt `QProg`** for T0 and as the T1 refinement midpoint (M5); open T0 first (S6).
7. **Fixed shape per class with harness padding** (S3).
8. **Budgets in CPU-h / replay / RSS**, image module separate, Lake `-j8` with memory limits (M4, m1).
9. **Plan and staff L2–L5**; L4 (PCS with RBR-KS) is the critical path; interim tensor-code PCS track (S8).
10. **Harness:** computable-indexer rule (m2), optimised differential-tested emulator (m3), metaprogramming policy (m4).
