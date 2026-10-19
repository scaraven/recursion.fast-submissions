<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A6-contract-v03.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A6: adversarial review of the trusted contract v0.3 (round 3)

Date 2026-10-11. Scope: `contract-v03/` as described in `contract-v03/RESULT.md`. I read every line of
`RecursionFast/Contract/*.lean`, the four challenge stubs, `scripts/{render-challenge.py, Gate.lean, ci.sh,
run-comparator.sh, check-hygiene.sh, dummy-claim.py}`, the comparator README and its `Main.lean`, DESIGN §15,
D4 §2–5 and A4. I attacked mainly what v0.3 adds, and re-checked the earlier fixes.

All probes are under `probes/a6-probes/`. The Lean probes are run with
`cd contract-v03 && lake env lean ../probes/a6-probes/<file>`. Two probes are separate Lean-core-only mini
projects (`gateproj/`, `cmpproj/`), each with a `README.txt`. I edited nothing in `contract-v03/` and did not run
a `lake build` there.

## Verdict

The machine semantics hold up: harts, first touch, the 18 counters and the timer. I found no way for an
accepting run to under-count a counter or a first-touch set. I also found no race that the sequentialised hart
semantics hides, and no hole in the region checks, whether through QUERY, sub-word stores or nested spawns.
Positive and negative kernel probes back this.

The serious problems are elsewhere:
- **G0, pipeline (critical, conditional).** The comparator accepted a **false** statement when the solution
  had been built in the checking tree before the comparator ran. That is the order `scripts/ci.sh` uses.
- **P1, score meaning (high).** Leaf bytes are still priced at v0.2's hash rate in all four profiles and on
  the latency board. This undoes A4-F6 and moves the score-optimal leaf size 4–8× above the real optimum.
- **G1 and G2, gate (medium).** Both defeat the gate's own goal (compiled code = kernel term). G1 uses
  `@[init]` on an ordinary `def`. G2 rewrites a trusted `.olean` at build time. Both pass the real gate binary.

The fixes are small. Do not freeze v0.3 for season 1 before G0 and P1 are fixed.

## Findings, ranked

### G0 (critical, conditional on harness order): the comparator accepts a false statement if the solution was built first

- **Where:** `scripts/ci.sh:12` (`lake build … RecursionFastAudit`, which builds ToyChallenge **and**
  ToySolution), then `ci.sh:17-18` (the gate reads ToySolution), and only then `ci.sh:51` (comparator).
  Comparator README, assumption 2: "you have not previously tried to compile the Solution file".
- **Probe:** `probes/a6-probes/cmpproj/`, with the real comparator binary and fake landrun.
  - The stand-in contract has an unsatisfiable `Good s := s.vk = 42 ∧ s.vk = 43`.
  - The solution imports a module `Tamper` whose elaboration (`#eval` + `IO.Process`) rewrites
    `.lake/build/lib/lean/RecursionFast/Contract.olean` with `Good := True`. It uses an atomic rename, since the
    running process has the old file mmapped.
  - Lake does not notice: traces are computed from sources, and `lake build Contract` afterwards rebuilds nothing.
- **Result:**
  - **A.** Fresh tree, comparator first: `Const does not match … 'RecursionFast.Good'`. Correctly rejected.
  - **B.** `lake build Contract Solution` first, then the comparator: **"Your solution is okay!"** The challenge
    module was elaborated for the first time against the tampered contract, so both sides agree on `Good = True`.
- **Why it matters:**
  - Real landrun does not help. The comparator itself grants the build write access to the project's `.lake`
    (`Main.lean`, `safeLakeBuild`), and the contract `.olean`s live in that same build directory.
  - v0.3 adds two steps that need the solution's `.olean`s: the gate, and the badge path (compiled
    prover/indexer). Running either before the comparator in the same tree reproduces B.
- **Fix:**
  1. Run the comparator **first**, in a fresh tree where no solution code has ever run.
  2. Run the gate and badge afterwards, in a separate copy.
  3. Ship the contract, the vendored code and the packages as a separate lake package outside the project's
     writable `.lake`, mounted read-only.
  4. Record sha256 of every organiser-built `.olean` before any solution code runs, and re-verify before each
     later step.
  5. Reorder `ci.sh` and add `cmpproj` scenario B as a CI regression: it must be rejected under the production
     order.

### P1 (high, score meaning): leaf bytes are priced at v0.2's hash rate (`q_bytes/8`) in every profile and on the latency board

- **Where:**
  - `Cost.lean:126-127`, `Profile.C … + (P.PH + 35) * c.qLevels + c.qBytes / 8`.
  - `Machine.lean:397-398`, QUERY bubble `QUERY_LEVEL_CYCLES·levels + 2^logLeaf`.
- **The mismatch:**
  - In v0.2, `q_bytes/8` was exactly the leaf hash at `P_H = 8` per 64-byte compression.
  - v0.3 rescaled `P_H` per profile (72/174/100/200) for the Merkle levels and for the FS absorption of
    `VK ‖ x` (A4-F6, `⌈(inWords−4)/8⌉·P_H`), but left the leaf at 1 per element.
  - Hashing a leaf of `2^L` elements really costs `⌈2^L/8⌉·P_H`, which is 9–25× more than charged.
  - On the latency board the leaf costs `2^L` cycles, against 1,560 cycles per 64 bytes for a level: 195× too low.
  - A depth-0 QUERY (`logLeaf = logLen`) therefore reads a whole committed vector with no hashing price at all.
  - D4 §4.2 copied v0.2's term. Nothing in D4 argues for it.
- **Probe:** `probes/a6-probes/Pricing.lean` (contract functions, `#eval` and `norm_num`).
  - **(a) A4-F6 undone.** Move a 1,024-word VK out of the tape (`vkLen = 0`) into the index oracle (shape
    `⟨10,10⟩`, admissible), and read it with one depth-0 QUERY. The `C+FS+⌈λB⌉` term for that component drops:

    | Profile | Before | After | Change |
    |---|---:|---:|---:|
    | ZisK | 21,276 | 13,084 | −38 % |
    | SP1 | 48,176 | 26,928 | −44 % |
    | RISC Zero | 37,950 | 35,214 | −7 % (paging partly compensates) |
    | Jolt | 54,710 | 30,134 | −45 % |

    If the leaf were priced at the profile's `P_H`, it would cost **exactly** the F6 price (ZisK 21,276,
    SP1 48,176, Jolt 54,710). So the gap is purely the leaf term.
  - **(b)** One depth-0 leaf of 2^10 elements costs 2,048 in every profile (`leafPrice`).
  - **(c) Design distortion.** For openings of a `2^26`-element oracle, the leaf size that minimises the price
    is `L = 6–7` as charged, but `L = 4` if hashed. At the charged optimum the real price is 10–39 % above
    the real optimum: ZisK 2,860 vs 2,602; SP1 6,959 vs 5,050; RISC Zero 4,369 vs 3,274; Jolt 7,869 vs 5,674.
    The charged price itself understates the real one by up to 1.6×. The score therefore rewards large folding
    factors and leaves more than real recursion does.
- **Fix:**
  - Add a counter `qBlocks += ⌈8·2^logLeaf / 64⌉` in `CostVec.addQuery`, and in `Profile.C` replace
    `q_bytes/8` by `P_H·qBlocks`. Keep `λ·q_bytes` in `B`.
  - The cheaper approximation `P_H·q_bytes/64` under-prices leaves below 64 bytes by up to 8×.
  - Latency board: bubble `QUERY_LEVEL_CYCLES·(levels + ⌈2^logLeaf/8⌉)`.
  - This changes the vector, so do it before any v0.3 certificate exists.

### G1 (medium, pipeline): `@[init]` on an ordinary `def` makes compiled code differ from the kernel term, and the gate passes it

- **Where:** `scripts/Gate.lean:134-147`. Rule 3 checks only `implemented_by`, `extern` and `csimp` entries.
  Rule 2 flags `opaque`, but `@[init f] def x := 0` is a plain `defnInfo`.
- **Probe:** `probes/a6-probes/gateproj/InitSol.lean`.
  - `@[init evilInit] def vk : Nat := 0` with `evilInit : IO Nat := pure 1337`.
  - `theorem cert : submission.vk = 0 := rfl` is accepted by the kernel.
  - The compiled `badge` executable prints `compiled submission.vk = 1337`.
  - The **built gate binary** (`contract-v03/.lake/build/bin/gate InitSol InitSol.cert --computable
    InitSol.submission,InitSol.vk`) prints `gate: PASS`.
- **Impact:** the badge path (compiled indexer/prover) can run different code from the certified definitions.
  This is exactly what A4-F2/F3 asked the gate to exclude. The score is unaffected, since it is rendered.
- **Fix:** in rule 3, reject every untrusted module that registers an `[init]`/`[builtin_init]` entry
  (`regularInitAttr`, `builtinInitAttr`; or `getInitFnNameFor?`/`isIOUnitInitFn` over its constants).
  Also reject `@[export]` entries, which allow symbol interposition in a linked badge executable. Run the
  badge executable in its own process, never inside a trusted emulator process.

### G2 (medium, pipeline): the gate's "trust by location / import graph" reads files the solution build can rewrite

- **Where:**
  - `Gate.lean:61-82`. Contract modules are trusted if they are reachable through the imports *recorded in*
    `RecursionFast/Contract.olean`.
  - Mathlib is trusted if its `.olean` path contains `/packages/<pkg>/`.
  - Core is trusted if the path `startsWith sysroot` (a plain string prefix).
  - RESULT §10.10 assumes the packages are read-only. But the comparator sandbox makes the whole project
    `.lake` writable, and that is where both the contract build and, in a standard setup, `.lake/packages` live.
- **Probe:** `probes/a6-probes/gateproj/TamperSol.lean` + `TamperCert.lean`.
  - Elaborating the solution compiles a new module `RecursionFast.Contract.Evil` (with
    `@[implemented_by shownVk] def evilVk := 0`) into the build directory.
  - It then replaces `RecursionFast/Contract.olean` by one that imports it. Lake does not notice.
  - The gate binary on `TamperCert cert --computable submission`: **PASS**. `Evil` is "contract by import graph",
    so its `implemented_by` is never reported.
  - `lake env lean --run Badge2.lean` prints `compiled submission.vk = 1337`, while the kernel value is `0`.
  - The same works by dropping `Mathlib/Evil.olean` into a writable `.lake/packages/mathlib/…`.
- **Fix:** the hash manifest of G0, step 4. The gate should trust a module iff its `.olean` sha256 is in the
  organiser's manifest; drop location and import-graph trust. Run the gate after the comparator, on a fresh copy.

### R1 (low–medium, pipeline): the renderer reads any harness-readable file named by the claim

- **Where:** `render-challenge.py:71-72` (`os.path.join(base, v["code"])`). An absolute path or `..` escapes
  the claim directory, and symlinks are followed.
- **Probe:** `probes/a6-probes/render/`.
  - `claim-traversal.json` points `image.code`/`image.data` at `/tmp/a6-secret.bin`.
  - The rendered `T1-traversal.lean` contains the file as `image_code_0 = 0x…` and decodes to
    `b'SECRET-HARNESS-TOKEN-0123456789a'`.
- **Impact:** any harness-readable file whose length is a multiple of 4 or 8 and at most 1 MiB is published
  in the challenge text, including other teams' pending images.
- **Fix:** `p = realpath(join(base, v))`. Require `commonpath([p, base]) == base`, a regular file and no symlink.
  Better, the harness supplies the image paths itself, not the claim.

### H1 (low, score meaning): `SPAWN`/`JOIN` cost one `sys` each on the M-zk board

- **Where:**
  - `Machine.lean:406, 418`: the child gets a fresh register file.
  - `Cost.lean:110-118`: `sys` has weight 1.
- **Impact:**
  - A zkVM has no harts. The deployed image needs a runtime that saves and restores context, about 60–70
    loads/stores per spawn.
  - On M-zk, a spawn is therefore a call that preserves all 31 parent registers for about 3 `sys`.
  - The gain is small, since the child must load its inputs. But it is a free channel, and it is the only
    place where harts change the M-zk vector beyond summing.
- **Fix:** count spawns as their own counter, priced per profile at a context switch (about 64), or document
  the choice.

### F1 (low–medium, deployment fidelity): fuel exhaustion is a reject, and with harts the budget rule is per-hart and inherited

- **Where:**
  - `Machine.lean:384`: `| 0, … => none`.
  - `Machine.lean:412`: the child gets the parent's *remaining* fuel, and the parent's fuel is not reduced by
    the child's steps.
  - DESIGN:61: "the deployed verifier semantics includes the fuel cap".
- **Impact:**
  - A malicious submitter can plant a backdoor: "on a magic transcript, loop more than 2^36 steps, then
    `HALT(1)`".
  - The model rejects that run, so `Agrees` and the security theorem hold. A deployment that does not
    replicate the exact per-hart inherited budget accepts it.
  - A native latency-board verifier will not count instructions.
  - This was already true in v0.2 (single counter). With harts the rule is unusual and unlikely to be copied.
- **Fix, either of:**
  - Add a certificate clause `NoTimeout`: on every input, `execute` HALTs or faults before the fuel runs out.
    This means proof burden on rejecting paths too.
  - Use one global step budget (all harts), and state the exact budget rule in the challenge text as part of
    the deployed semantics.

### T1 (low, latency realism): the scoreboard has no structural hazards beyond two slots

- **Where:** `Timer.lean:37-40`.
- **Impact:** two loads/stores per cycle, a fully pipelined divider (two 16-cycle divides issue per cycle),
  and no WAW stall (a later short-latency write lowers `ready`). Memory-bound loops (Merkle path copies,
  table-driven field code) look about 2× faster than on an in-order core with one memory port. D4 §4.5 lists
  ILP and cache limits but not these.
- **Fix:** one memory port and an unpipelined divider (about 6 trusted lines). Or document them and calibrate
  on the board (D4 §6.2).

### Notes

- **N1:** DESIGN §15.2 F3 says the gate checks "debug options". It cannot: `.olean`s carry no trace of them
  (RESULT §5). Reword.
- **N2:** `Profile.w : List ℚ` is zipped with 18 counters, so a seasonal profile with 14 entries silently
  stops charging `mPages`. Use `Fin 15 → ℚ`.
- **N3** (`probes/a6-probes/EpsComputable.lean`): honest errors `2^-130` written with `ℝ≥0` operations are
  noncomputable (e1, e2). That makes `submission` noncomputable, so the gate's `--computable submission`
  fails. A `ℚ≥0` cast compiles (e3). The toy passes only because `ε = 0`. Document the idiom, or name the
  badge-path constants separately.
- **N4:** check SP1's `m_words = 0.12` against D4's own data. MemoryLocal 16 + MemoryBump 15 per touched
  address, over 144 per `add`, gives about 0.22 [unverified].
- **N5:** the claim "every interleaving yields the same state at JOIN" (`Machine.lean:339-340`) is the M-cpu
  deployment's trust basis, and it is argued only in prose. I found no counterexample (below). A short
  written proof in the design (or an interleaving-semantics lemma in the library) would make it auditable.
- **N6:** `q_count` has weight 0 in every profile, so the per-QUERY syscall overhead is free. This is minor
  once P1 is fixed.

## What I tried that did not break it

1. **Harts region discipline** (`probes/a6-probes/harts/HartsProbe.lean`, `hp.S`, kernel evaluation at the
   full fuel):
   - S0 accepts. The child's QUERY lands in its `Wr` and is read by the parent after JOIN. The child's QUERY,
     touches and HALT are in the summed vector (`sys 4, qCount 1, qBytes 64, mWords 23, mPages 3`,
     `W = 4029, S = 4026`).
   - Each of these rejects:
     - S1: the child's QUERY overruns `Wr`.
     - S2: the parent QUERYs into a live child's `Wr`.
     - S3: the parent makes a byte store into a live child's `R`.
     - S4: a child spawns a grandchild whose `Wr` is the child's read-only `R`.
     - S5: JOIN with a wrong handle.

   By code reading:
   - siblings may share `R` but never write each other's regions;
   - grandchildren are confined to their parent's regions;
   - zero-length regions are harmless;
   - with 8-aligned regions, sub-word accesses cannot straddle a region boundary;
   - the JOIN merge (`has a 8`) covers every aligned key of `Wr`; unaligned keys are never read;
   - handles are unique;
   - HALT with a live child rejects;
   - SPAWN without the flag traps.

   I found no race that a parallel runtime would expose.
2. **Counter and first-touch completeness.**
   - Every fetch, load/store (sub-word included) and QUERY destination is touched, by every hart, in shared sets.
   - The JOIN merge needs no touch (the child already touched).
   - Code and data keys are disjoint.
   - The tape and data image are not pre-touched.
   - `kind` covers every decoded instruction, and W-ops are classified by op.
   - The timer is advanced in every `execute` arm. `opOf` covers every opcode the decoder accepts, and FENCE
     falls to the conservative default.
   - A wait at JOIN adds no work. W/S match D4 §3.2's series-parallel fold.
   - Spawn storms pay 4,000 cycles of work per child.
3. **Score functions.**
   - All weights are ≥ 0, so a componentwise-worse vector never scores better.
   - Every factor is ≥ 4^4 (`B ≥ 32` tape bytes), so the product never collapses to 0.
   - The ℚ coercions and the `fs` ceiling are correct. The `scoreT2Fourths` table and `scoreLat3` are monotone.
   - Every score input (image incl. `harts`, summaries, claims, `W`/`S`, scores) is rendered, and bound by the
     `summary`/`score` clauses (A4-F2/F4 hold).
4. **Sparse index.**
   - Entries are `Fin`-typed, so nothing is out of range.
   - Duplicates are summed, which is consistent in characteristic 2.
   - `nnz_le` bounds the list length, explicit zeros included.
   - Security is `∀ i`, so a VK/IDX that depends on the representation is harmless.
   - `IdxAdmissible` caps `IDX`.
5. **A4-F1:** `AccStmt` is typed by the declared shape, and `SelectOk` is part of `Secure`. **A4-F5:** strict
   key set and types, and no Lean injection (but see R1).
6. **Comparator in the correct order** (`cmpproj` scenario A) rejects the tamper. The challenge export goes to
   memory through stdout, so a later solution build cannot alter it.

## Vacuity and auditability versus v0.2

I found no new vacuity: `Agrees`, `Secure` and the cost and latency clauses quantify as in v0.2. The auditing
burden grew by about 213 trusted lines, concentrated in `execute`. The hardest new reading is the
`Ctx.allows`/SPAWN/JOIN trio together with the informal race-freedom argument (N5), and `Acct`'s keyed
first-touch sets. The weak points have moved from Lean to the harness: build order (G0), the trust anchors
(G1, G2) and the renderer (R1).

## Fix list (priority order)

1. **G0:** comparator first, in a fresh tree. Contract, vendored code and packages read-only, outside the
   project `.lake`. An `.olean` hash manifest. Reorder `ci.sh`, and add the `cmpproj` regression.
2. **P1:** a `qBlocks` counter priced at `P_H`, and the leaf hash in the latency bubble (before any v0.3
   certificate exists).
3. **G1/G2:** the gate rejects untrusted `[init]`/`[builtin_init]`/`[export]` entries and trusts by hash
   manifest. The badge runs in its own process.
4. **R1:** path containment in the renderer.
5. **F1, H1, T1:** a `NoTimeout` clause or a global budget, stated in the challenge text. Spawn pricing on M-zk.
   One memory port and an unpipelined divider, or documentation.
6. **N1–N6:** documentation and type hygiene.

## Probe index

| Path | Shows |
|---|---|
| `probes/a6-probes/cmpproj/` (`README.txt`) | **G0**: the comparator accepts a false statement after a prior solution build; rejects it in a fresh tree |
| `probes/a6-probes/Pricing.lean` | **P1**: F6 undone by moving the VK into IDX; flat leaf price; leaf-size optimum shifted |
| `probes/a6-probes/gateproj/InitSol.lean`, `Badge.lean` | **G1**: `@[init]` divergence passes the built gate |
| `probes/a6-probes/gateproj/TamperSol.lean`, `TamperCert.lean`, `Badge2.lean` | **G2**: `.olean` tampering at build time makes an `implemented_by` "trusted" |
| `probes/a6-probes/render/` | **R1**: arbitrary file rendered into the challenge |
| `probes/a6-probes/harts/` (`hp.S`, `HartsProbe.lean`) | region discipline holds (S0 accepts, S1–S5 reject) |
| `probes/a6-probes/EpsComputable.lean` | N3: computability of `ε` |
