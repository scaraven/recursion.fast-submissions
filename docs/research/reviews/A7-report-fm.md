<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A7-report-fm.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A7: formal-methods / zkVM review of the report draft (sections 02, 06, 07, 08, 10, 12, 13, A, C)

Reviewer stance: Lean 4 kernel and elaboration, proof engineering, TCB analysis, RISC-V and cost models.
Ground truth: `contract-v03/` (compiled sources, `RESULT.md` incl. §R3, `NOTICE-P2d.md`, `scripts/harness.sh`,
`scripts/ci.sh`, `scripts/Gate.lean`, `logs/v03/`), `submissions/baseline-v03/` (incl. `logs/orch-recheck.log`),
`reviews/A4`, `reviews/A6`, `design/DESIGN.md` §15. The report was not edited.

## Method and what was re-checked

- **Verbatim check of every Lean listing** labelled `Contract/*.lean` (07, 08, App. A): a script normalised
  whitespace and searched each listing segment (split at `-- …`) in the compiled source
  (`/tmp/a7scripts/verb.py`, `verb2.py`). Result: all listings are verbatim except the **App. A `Cost.lean`
  listing (C1)**. The other divergences are the declared omissions (`namespace`, header) and the silent
  omissions inside listings labelled "abridged".
- **`lake env lean` probes in `contract-v03`** (scratch dir `/tmp/a7probe/`):
  - `P1.lean`: `def e2 : ℝ≥0 := (2:ℝ≥0)⁻¹ ^ 128` and `def e3 : ℝ≥0 := errorCap` fail to compile
    ("depends on 'NNReal.instInv' / 'errorCap', which is 'noncomputable'").
  - `P2.lean`: `((1/2^128 : ℚ≥0) : ℝ≥0)` compiles. This confirms A6-N3 (M2).
  - `ir/IrC.lean`: a naive overwrite of `vk`'s IR entry with `evil`'s did **not** change `#eval` (m19).
- **Numbers recomputed.**
  - `scripts/loc.py` on the contract: **796 code / 471 comment / 269 blank / 1,536 total**; `Cost.lean`
    73/61/35/169.
  - `logs/v03/axioms.log`: 31 module lines, **1,501** declarations.
  - Baseline: closed forms, Table `tab:base-counters` and `S_risc0,16 = 147,427,411` recomputed by hand from
    `Cost.lean`. All match.
  - CI and harness timings (614 s, 353 s, 115/175 s, 35,093 manifest entries, 3,630/3,597/29 modules,
    365.8/373.2 s) match `logs/v03/ci-round3.log`, RESULT §R3 and `orch-recheck.log`.
- **Read in full:**
  - `Machine.lean`, `Cost.lean`, `Security.lean`, `Certificate.lean`, `Accumulation.lean`, `Gate.lean`,
    `harness.sh`, `ci.sh`, the vendored `Decode.lean`, and the `Library/{Timer,RbrSound,Transfer}.lean`
    signatures;
  - the RISC-V claims: the Zbc encodings (`funct7 = 5`, `funct3` 1/3/2), `clmulr` = bits 126..63, the W-op
    edge cases, the `ECALL`-only `0x73` arm, the CSR/ZisK accelerator arm unreachable (so "dead at run time"
    is true), the doubleword-keyed memory, the per-hart fuel, the first-touch keys, the timer.

Overall: the cryptographic and Lean *statements* in 07/08 are faithfully transcribed and correctly
quantified. The weak points of the draft are four:
- stale text left behind by round 3 (App. A `Cost.lean`, the checklist, App. C);
- an over-strong reading of the computability gate;
- implementation status presented as fact (badge path, emulator, preflight, `leanchecker`);
- an incomplete trusted-surface list.

---

## Findings (ranked)

### C1 (critical): App. A reproduces the superseded `Profile.C`, and its audit instruction is wrong

**Where:**
- `A-lean-contract.tex:1106-1108` (`Profile` docstring);
- `A-lean-contract.tex:1132-1134` (`Profile.C`);
- `A-lean-contract.tex:1069-1071` (the "Check" sentence).

**Problem:**
- The appendix claims "Every other line is verbatim" (l. 11), but it shows the pre-round-3 definition
  `... + (P.PH + 35) * c.qLevels + c.qBytes / 8` and the docstring "`PH` per Merkle level".
- The compiled contract (`Cost.lean:75-77`) charges `P.PH * ((c.qBytes : ℚ) / 64 + c.qCount)`.
- The Check paragraph tells auditors that "`q^count` carries no weight and the query counters are priced
  only through `(P_H+35) q^lev + q^bytes/8`".
- So the one trusted score function an auditor reads in the appendix is the one A6-P1 found wrong. It also
  contradicts §10 (l. 351-358) and §12 (scores computed with the new price).

**Evidence:** `verb.py` output (3 unmatched lines, all in `Cost.lean`); `NOTICE-P2d.md` table.

**Fix:**
- Replace the listing lines with `Cost.lean:41-77` verbatim. That is the `Profile` docstring "...the hash price
  `PH` per 64-byte compression (a Merkle level, a 64-byte block of a QUERY leaf, a transcript absorption)..."
  and the 8-line `Profile.C` docstring, then:

      def Profile.C (P : Profile) (c : CostVec) : ℚ :=
        ((P.w.zip c.toList).map fun (a, n) => a * n).sum + (P.PH + 35) * c.qLevels +
          P.PH * ((c.qBytes : ℚ) / 64 + c.qCount)

- Replace l. 1069-1071 with: "the 15 weights of each profile match \cref{tab:cost-profiles}
  (\lean{zip} stops at the shorter list, so the three query counters are priced only through
  $(P_H+35)\,q^{\mathrm{lev}}+P_H\,(q^{\mathrm{bytes}}/64+q^{\mathrm{count}})$, and a profile with fewer than
  15 weights would silently drop counters, A6-N2)".
- Add a CI step that diffs every App. A listing against the source (the script above is 30 lines).

### M1 (major): computability is presented as closing A2-M4. It does not: Lean-computable is not feasible

**Where:**
- `07-protocol-model.tex:363-369` ("otherwise `IDX` could be the table x ↦ [∃w R1CS], which nobody can
  compute ... the gate rejects a noncomputable `VK`, `IDX`...");
- `08-security.tex:430` (row "Indexer ... closed by computability gate; badge-path evaluation");
- `13-threats.tex:95` (S8);
- `10-cost.tex:608`;
- `06-architecture.tex:194-195`.

**Problem:**
- The satisfiability table *is* Lean-computable. `K` is a `Fintype` (`Library/Field.lean: card_K`), `R1CS` has
  a contract `Decidable` instance (`R1CS.lean:63`), and `∃ w : Fin nw → K` is decidable by enumeration.
- The report itself says this about extractors (`08-security.tex:264-266`: "a computable brute-force
  extractor ... The computability gate therefore excludes nothing"). The two passages contradict each other.
- What actually closes A2-M4 is the badge path. It evaluates the compiled indexer within time and memory
  budgets on hidden indices, and it gates records only, not the proved score.
- For cryptographers new to Lean: `noncomputable` means "has no compiled code" (it uses `Classical.choice`,
  `Real` inverse, ...). It does not mean "infeasible".

**Fix:** in 07 replace "which nobody can compute, making ... undeployable." by:

> "which is computable in Lean's sense (enumeration over the finite $K^{n_w}$) but infeasible. Lean's
> `noncomputable` marks definitions without compiled code (choice, real inverses), not expensive ones. The
> gate therefore only guarantees that the key and index oracle *have* compiled code; feasibility is
> enforced by the badge path, which runs the compiled indexer on hidden indices under a time and memory
> budget and gates record eligibility, not the proved score."

Change the 08 table row "Closed by" to "badge-path evaluation under budget (records only); the gate ensures
compiled code exists". Change 13 S8 the same way.

### M2 (major): gate rule (iv) on `submission` rejects every protocol with a nonzero error written with `ℝ≥0` operations

**Where:** `06-architecture.tex:191-192`, `07-protocol-model.tex:366-369`, `A-lean-contract.tex:458`.

**Problem:**
- The harness checks `--computable RecursionFast.Challenge.submission`; the baseline and the toy both have
  ε = 0.
- `Protocol.ε : ChallengeIdx → ℝ≥0` is a data field, so a declared error `errorCap` or `(2:ℝ≥0)⁻¹^130`
  makes `submission` noncomputable. My `P1.lean` probe gives "failed to compile ... depends on
  'errorCap'".
- So the first succinct submission fails the gate unless it knows the `ℚ≥0`-cast idiom.
- "hence VK, IDX, the prover and the extractor" also hides that ε and every other data field are checked.
- This is A6-N3, mentioned only in passing at `13-threats.tex:252-254`.

**Fix:** after (iv) in 06 add:

> "Because \lean{ε} is a data field, errors must be written computably, e.g.\
> \lean{((1/2^130 : ℚ≥0) : ℝ≥0)}; \lean{errorCap} and \lean{ℝ≥0} inverses are \lean{noncomputable} (A6-N3).
> v0.4 should name the badge-path functions (\lean{VK}, \lean{IDX}, prover) as separate constants rather
> than \lean{submission}."

Mirror this in the 07 indexer paragraph and in the App. A Protocol check.

### M3 (major): the gate, and the badge, run on a second, independent build of the solution

**Where:** `06-architecture.tex:177-218` and Decision A-3 (`:221-234`); `harness.sh:121-150`.

**Problem:**
- Stage 1 builds the solution in `WORK/cmp`. Stage 2 builds it again from source in `WORK/gate`, and the
  badge runs that second build.
- Nothing checks that the two builds agree. Solution elaboration is arbitrary code (`#eval`, `run_cmd`, `elab`),
  and the two trees differ visibly (paths `…/cmp` vs `…/gate`).
- A solution can therefore emit, in the gate tree only, a different `submission` (e.g. an indexer that
  writes the A1-M3 magic word). It can make `certified` type-check there by environment manipulation:
  `debug.skipKernelTC` leaves no trace and is "invisible to the gate", and no kernel replays the gate tree.
- The gate then passes, and the badge compares the native indexer against a Lean indexer that was never
  certified. That reopens H1/A1-M3 for records. The proved score is unaffected.

**Evidence:** `harness.sh:122-147` (two `mkfresh` + two builds, no comparison); `Gate.lean:34-35` (debug
options not seen); RESULT §R3.1 ("Lean builds are bit-reproducible here").

**Fix:** add to Decision A-3:

> "5. The gate and badge operate on the build that comparator verified: after stage 1 the solution's
> \code{.olean}s are hashed, and stage 2 requires bit-identical \code{.olean}s (builds are reproducible), or
> the gate loads the stage-1 build read-only."

Add a regression probe that switches `submission` on `IO.currentDir`.

### M4 (major): implementation status is presented as fact; several trusted components do not exist yet

**Where:**
- `06-architecture.tex:125-151` (steps 1-3), `:127` ("harness.sh implements steps 4-8"), `:261-276`
  (badge (i)-(v)), `:298`, `:301` (trust table);
- `13-threats.tex:145` (H10);
- `08-security.tex:464` (G row).

**Problem:**
- *Preflight and source policy (steps 1-3).* `harness.sh` has no preflight (systemd unit, seccomp, Landlock,
  refusing root), no source or import allow-list, and no blob-level export. These are design.
- *Badge.* Stage 3 is a generic `--badge "CMD"` hook. Badge steps (i)-(v) are not implemented.
- *Emulator.* There is no organiser "trusted emulator". The only one is P3b's `submissions/baseline-v03/emu/rfemu.c`,
  which P3b itself calls unverified, differential-tested on two instances with m = 2.
- *leanchecker.* It is not a harness stage. The harness replays with the Lean kernel and with nanoda (when
  the config names it). `leanchecker` runs only in `ci.sh` on `SkipKernel` and in the baseline's `check.sh`.
  `SkipKernel` has never been run through comparator or the harness, so "the replays are the binding
  check" (`06:171-173`) rests on `leanchecker` evidence only.
- *Other planned items.* The FS prefix and sampler, and `elf2image` (`06:79`), are not implemented.

**Fix:**
- Add a column "v0.3 status: implemented / planned" to the CI step list and to `tab:arch-trusted`.
- Replace `06:127` with: "\code{scripts/harness.sh} implements stages 0-2 (steps 4-6) and a hook for the
  badge command; steps 1-3, the badge checks (i)-(v), the trusted emulator, the Fiat--Shamir prefix and
  the sampler are specified here but not yet implemented."
- In `06:298` replace "\code{leanchecker} replay" with "\code{leanchecker} (CI and submitter check only)".
- Add `SkipKernel` to the harness regression.

### M5 (major): the trusted-surface table is incomplete

**Where:** `06-architecture.tex:296-305`.

**Problem:** the table omits these items, all of which are in the TCB:

1. *The Lean elaborator and frontend for the challenge.* The meaning of the statement is the elaborated term
   of the organiser-elaborated challenge.
2. *Lake.* G0 was a Lake behaviour, and Lake resolves which `.olean` is loaded.
3. *The Lean compiler and runtime.* The badge's compiled indexer and prover, and the `gate` and `axiomaudit`
   executables, are compiled Lean.
4. *Host tools.* The Python interpreter running the renderer, manifest and harness glue (Python ≥ 3.11 for
   `tomllib`), `bubblewrap`, and `sha256sum`.
5. *Unpinned binaries.* The comparator, `lean4export` and `nanoda_bin` binaries are not covered by the
   `.olean` manifest.
6. *Contract-used library definitions not listed.* `![…]` (`Matrix.vecCons`, used by `profiles`),
   `List.ofFn`, `Fin.cons`/`Fin.append`/`Fin.snoc`/`Fin.induction`, `Set`, and core `BitVec`.
7. *QEMU difftest coverage* (`probes/a4-probes/difftest/gen*.py`). It covers register ALU, M, Zbc, W-ops
   and load/store widths, not branches, `JAL`/`JALR`/`AUIPC` control flow or fetch.

**Fix:**
- Extend the row "Lean kernel and checking stack" to: "Lean v4.34.1 kernel, elaborator (for the challenge),
  Lake, compiler (badge path, gate, axiom audit); comparator, \code{lean4export}, nanoda (binaries not
  hash-pinned)...".
- Add a row "Host tools: Python 3.11+, bubblewrap, sha256sum, the harness shell scripts".
- In the vendored-model row write "differential tests against QEMU for register, M, Zbc, W-op and
  load/store semantics (control flow not covered)".

### M6 (major): §10 shows Lean that is not the contract's

**Where:** `10-cost.tex:192-201` and `10-cost.tex:470-485`.

**Problem 1, the cost clause (l. 192-201).** It presents a fictional `AcceptingCostAtMost`: `Index k`,
`RawMessages k`, `load img k (VK i) x ρ`, and `execute … = some (true, v)` with
`execute : … → Option (Bool × CostVec)`. None of these exists in the contract. The real clause
(`Cost.lean:31-32`) quantifies over `i`, `x` and a full transcript `tr`, and `execute` returns
`Option (Acct × SB × MachineState)`.

**Problem 2, the timer theorems (l. 470-485).** The listing gives the probe model's signatures:
- `.now` (the contract `SB` has `slot`/`ready`);
- `time_append` without the `Ok a` hypothesis;
- `length_le_time : ops.length ≤ time ops`, where the library proves `≤ 2 * time ops`.

It also says composition is "proved for the single-issue probe model" and "the dual-issue variant adds slot
occupancy ... without changing the proof structure". In fact `Library/Timer.lean` (174 lines) already proves
`run_slack`, `time_append`, `time_blocks` and `length_le_time` for the contract's dual-issue `SB`.

**Fix:**
- Replace the first listing by the contract text, as in 07 l. 651-655, or label it "schematic, not contract
  text".
- Replace the second by the library signatures:
  - `theorem run_slack {sb : SB} (h : Bounded sb) (ops : List Op) : …`
  - `theorem time_append (a b : List Op) (ha : Ok a) : time (a ++ b) ≤ time a + time b + Lmax`
  - `theorem time_blocks : ∀ bs, (∀ b ∈ bs, Ok b) → …`
  - `theorem length_le_time (ops : List Op) : ops.length ≤ 2 * time ops`
- Change the text to "proved for the contract's dual-issue scoreboard in \code{Library/Timer.lean}".

### M7 (major): the auditor guidance describes superseded gate rules

**Where:**
- `A-lean-contract.tex:1576-1577` (checklist: "trust rule (by .olean location and import graph, not by
  name)");
- `13-threats.tex:151` (L3: "allowed in the organiser library (kernel re-checks)"; "policy for submissions
  open");
- `07-protocol-model.tex:368` (gate list without `init`/`export`).

**Problem:**
- Since R3 the gate trusts only by content hash (`Gate.lean:11-18`) and rejects `init`, `builtin_init` and
  `export` entries.
- The organiser Library is *not* in the manifest (29 project entries: `RecursionFast.Contract*` and
  `RiscvZkvm*`), so it is untrusted. An `implemented_by` there is rejected like a solution's.

**Fix:**
- Checklist: "the environment gate's trust rule (by content hash against the organiser manifest, never by
  name, location or import graph: \lean{SpoofCert}, A6-G2) and its rejection list (incl.\ \lean{init},
  \lean{builtin\_init}, \lean{export})".
- 13 L3, Mitigation: "...rejected in any untrusted module, the organiser library included (gate rule iii)".
  Residual: "--".
- 07 l. 368: "... any \lean{implemented\_by}, \lean{extern}, \lean{csimp}, \lean{init} or \lean{export}
  entry registered by an untrusted module".

### M8 (major): App. C cannot reproduce the v0.3 numbers the report relies on

**Where:** `C-reproducibility.tex:15-27`, `:37-48`, `:54-74`.

**Problem:**
- The layout and commands are v0.2 only. App. C lacks:
  - `contract-v03` CI (614 s);
  - `org-build.sh`, the manifest check, the harness;
  - `probes/a6/Pricing.lean`;
  - the `cmpproj`/`gateproj` regressions;
  - `submissions/baseline-v03/scripts/check.sh` (815 s);
  - `emu/measure.sh`;
  - `reviews/A6`;
  - `submissions/baseline-v03`.
- The pins omit:
  - nanoda (v0.4.19, `tools/ext/nanoda_lib`);
  - bubblewrap, qemu-riscv64 and riscv64 binutils;
  - Python ≥ 3.11;
  - the `riscv-zkvm` checkout taken by `ci.sh`/`check-vendor.sh`.
- `contract-v03` builds only next to `contract/` (`packagesDir = ../contract/.lake/packages`).
- `C:68` runs `probes/a2-probes/...` relative to `/path/to/leanerVM`, but the file is in
  `recursion.fast/probes/`.

**Fix:** add a v0.3 block:

    cd contract-v03
    scripts/ci.sh <riscv-zkvm checkout>              # 614 s; logs/v03/ci-round3.log
    scripts/org-build.sh .lake/org
    python3 -I scripts/olean-manifest.py check --org .lake/org scripts/olean-manifest.sha256
    (cd .lake/org && lake env .lake/build/bin/axiomaudit)       # logs/v03/axioms.log
    lake env lean probes/a6/Pricing.lean
    tests/pipeline/cmpproj.sh; tests/pipeline/gateproj.sh .lake/org/.lake/build/bin/gate
    cd .. && submissions/baseline-v03/scripts/check.sh           # 815 s, CHECK OK
    submissions/baseline-v03/emu/measure.sh 16 20 24

Also:
- add `reviews/A6`, `submissions/baseline-v03` and `probes/a6-probes` to the layout;
- add the tool pins;
- note the `../contract` dependency;
- fix the A2 path: "`lake env lean <recursion.fast>/probes/a2-probes/A2Probes.lean` from a leanerVM
  checkout".

### M9 (major): a decider all-runs requirement is claimed for v0.3 but is not in the contract

**Where:**
- `13-threats.tex:139` (H4 "v0.3: $C^{\mathrm{all}}_{\mathrm{dec}}\le8C_{\mathrm{dec}}$");
- `13-threats.tex:325` ("until the v0.3 decider requirement");
- `02-objectives.tex:99-100` ("an optional all-runs bound is displayed as a badge").

**Problem:** `Certificate2` has no all-runs clause, and no badge computes one. `10-cost.tex:250-253` correctly
says "planned ... not yet in the v0.3 contract". DESIGN §7 l. 122 still says "required from v0.3".

**Fix:**
- H4 mitigation: "$F=2^{36}$ per hart; planned: optional all-runs badge and, for T2 deciders,
  $C^{\mathrm{all}}_{\mathrm{dec}}\le8C_{\mathrm{dec}}$ (not in v0.3)".
- Residual 8: "Up to $2^{36}$ steps per rejection per hart (and $(\#\mathrm{spawns}+1)\cdot2^{36}$ with
  harts) until an all-runs requirement is added".
- 02: "...is planned as a displayed badge".

---

### m1 (minor): stale counts

**Where and actual values:**
- 795 code / 463 comment / 1,527 total lines appear at `07:7`, `02:157`, `A:36`, `A:1589` (also 00, 01). The
  actual values are **796 / 471 / 1,536**.
- App. A `tab:app-loc` gives `Cost.lean` 72/53/160. The actual value is **73/61/169**.
- The axiom audit is quoted as "1,492 declarations of the 30 organiser modules" (`06:205`). The current log
  shows **1,501 across 31 module entries**.
- `08:464` says "13 malformed claims". The actual count is 22 (13 schema, 7 path, 2 A6).
- 00/01 say "about 940 reachable lines". Elsewhere the figure is 930.

**Fix:** regenerate from `scripts/loc.py` and `logs/v03/axioms.log`.

### m2 (minor): an orphaned docstring in a "verbatim" listing

**Where:** `07-protocol-model.tex:334-335`.

**Problem:** "A full transcript: a value for every round." is kept, but its declaration `FullTranscript` is
dropped, and the docstring visually attaches to `MessageIdx`.

**Fix:** restore `abbrev FullTranscript := (i : Fin n) → (sh i).Ty`, or insert `-- …` and drop the docstring.

### m3 (minor): the body of `Protocol.Secure` is elided where it matters

**Where:** `08-security.tex:162-173`.

**Problem:** `def Secure : Prop := -- …` hides the one-line body in the section that defines security.

**Fix:** show `SecureWith (rel sz) Set.univ P.prover P.specVerifier P.extractor P.ε`.

### m4 (minor): the converse of Theorem `thm:sec-collapse` is not mechanised

**Where:** `08-security.tex:268-273`.

**Problem:** `Library/RbrSound.lean` has `SF.toKSF` and `SF.rbrKS_of_rbr` only. "Every KSF yields an RBR
state function" is argued in prose at l. 231-232.

**Fix:** "Conversely (argued, not mechanised: take $\exists w,\,S_m$), ...".

### m5 (minor): wrong first-touch mechanics, and a combinator that does not exist

**Where:** `10-cost.tex:181-182`, `:189-190`.

**Problem:**
- `execute` threads *three* Finsets (`words`, `pages`, `dirty`). The counts are their cardinalities taken at
  the end (`Acct.vec`), not increments made on insertion.
- The "library combinator for loops that write [base, base+8n)" does not exist (RESULT §10.5: "only per-touch
  cardinality lemmas"). The baseline wrote its own footprint invariant.

**Fix:** "\lean{execute} threads three \lean{Finset}s (doublewords, pages, written pages); the counters are
their cardinalities"; "the library has per-touch cardinality lemmas; a loop footprint combinator is planned".

### m6 (minor): the profile table omits `n_sys`

**Where:** `10-cost.tex:316-328`.

**Problem:**
- `n_sys` has weight 1 in every profile and is not in the table.
- `FENCE` (and any leftover) is classed as `add`.
- "imm." in the `n_add` row means `addi`/`addiw` only (`andi`/`ori`/... are `logic`).

**Fix:** add a row "$n_{\mathrm{sys}}$ (HALT, SPAWN, JOIN) & 1 & 1 & 1 & 1 & 1" and change the label to
"(add, sub, addi, lui, auipc, W forms, fence)".

### m7 (minor): the T0 to T1 "lower bound by construction" is too strong

**Where:** `07-protocol-model.tex:726-733`.

**Problem:** `Agrees` does not transfer query counts. A T1 image may memoise or skip a `QProg`'s duplicate
queries, so its query counters can be smaller than the T0 claim. Also, no library lemma relates `QProg` to the
machine.

**Fix:** "a lower bound for the T1 score of an image that issues at least the query program's queries";
"T0 protocol and security proofs carry over into T1".

### m8 (minor): row errors in the threat catalogue

**Where:** `13-threats.tex`.

**Problem and fix:**
- l. 105: `scoreLat4` should be `scoreLat3`.
- l. 154 (L5): "contract imports CompPoly's proved instances" is false. The contract imports no CompPoly and
  declares no `Field` instance.
- l. 160 (L11): "Lean core and Mathlib only" should be "Lean core, Mathlib and vendored `RiscvZkvm`".
- l. 158 (L9): residual "honest 1 MiB literal: 194 s, 8.9 GB" is pre-chunking. Use 13 s / 2.0 GB to
  elaborate, 80 s / 9 GB per prefix-walk lookup.
- l. 145 (H10): "leanchecker" is not a harness kernel (M4).

### m9 (minor): stale footnote in the baseline section

**Where:** `12-baseline.tex:224-226`.

**Problem:** the footnote says §10 "compares the fuel with D3's weighted cycle estimate, which gives the
factor 8.5". §10 no longer does.

**Fix:** delete the footnote.

### m10 (minor): problems in §02

**Where:** `02-objectives.tex`.

**Problem and fix:**
- *The figure.* The "Lean checking" box at l. 31-34 lists "environment gate ... comparator ...", which
  inverts Decision A-3. Use "comparator first (fresh tree), then gate (second fresh tree)".
- *A wrong citation.* l. 108-109 cites `sec:baseline` for "5-6×10^6 cycles" for a succinct verifier. The
  baseline is 3.09×10^9. Cite `subsec:bench-trajectory` instead.
- *An inaccurate term.* l. 161 calls the security definitions "first-order statements about finite sets".
  `SecureWith` existentially quantifies a state function. Write "statements about finite sets, with an
  existentially quantified state function".

### m11 (minor): A3's estimate given as a measurement

**Where:** `06-architecture.tex:388`.

**Problem:** "The baseline (about 3-4.5k lines) checks in about 8 min warm and 20-25 min cold" is A3's
pre-registered estimate. The measured values are 1,920 lines, about 6 min per harness run and 815 s for the
full check (`12:tab:base-time`).

**Fix:** use the measured values.

### m12 (minor): a script that does not exist

**Where:** `06-architecture.tex:79`.

**Problem:** "a trusted `elf2image` script is offered". No such script exists in the workspace.

**Fix:** write "will be offered".

### m13 (minor): fuel described as the DoS bound for any image

**Where:** `07-protocol-model.tex:468`, `10-cost.tex:597`, `02-objectives.tex:98`.

**Problem:** "within F steps per hart ..., which is the denial-of-service bound" is true only for images
without harts. A child inherits the parent's remaining fuel, and the parent is not charged. A run can
therefore take $(\#\text{spawns}+1)\cdot2^{36}\approx2^{52}$ steps, and a deployment must copy this rule
(A6-F1, H12).

**Fix:** "...which bounds DoS at $2^{36}$ steps for an image without harts and
$(\#\mathrm{spawns}+1)\cdot2^{36}$ with harts (H12)".

### m14 (minor, clarity for newcomers): Lean notions used as evidence but never explained

**Where:** 07, 12.

**Problem:** definitional and propositional equality are never explained, though "by `rfl`" and
"definitionally" are used as evidence:
- K ≡ `BF64`;
- `Challenge.image = image` is `rfl`;
- `exact m3` versus `simp [m3]`.

`decide +kernel` (kernel evaluation, GMP `Nat`, list walking, 80 s / 9 GB per lookup) is defined only in
the glossary.

**Fix:** add a three-sentence box in 07 §proto-fields, roughly: "`rfl` asks the kernel to reduce both sides
to the same normal form (definitional equality); it trusts nothing beyond the kernel but can be expensive;
a `simp` proof instead builds a chain of rewrites (propositional equality), which a second kernel may check
far more slowly (§12, nanoda)".

### m15 (minor): the hart race-freedom claim is stated as fact

**Where:** `07-protocol-model.tex:485-487`, `10-cost.tex:515-518`.

**Problem:** "every interleaving reaches the same state at JOIN" is the deployment trust basis of M-cpu, and
it is argued only in prose (A6-N5; RESULT §10.4: no race-freedom lemma).

**Fix:** append "(argued, not proved in Lean; A6-N5)".

### m16 (minor): hart accounting wording

**Where:** `10-cost.tex:525`.

**Problem:** "At JOIN a child's counters are added to its parent's" is wrong. One shared `Acct` is threaded
through the nested `execute`, so the child's counts are charged at SPAWN time. The totals are the same.

**Fix:** "a child's counters accumulate in the run's single accounting state".

### m17 (minor, suggested probe): compiled code is assumed to equal the kernel definition

**Where:** `06-architecture.tex:186-196`.

**Problem:** the gate assumes compiled code equals the kernel definition unless an attribute says otherwise.
Other environment extensions that carry compiled code (IR) are not compared.

**Evidence:** my naive overwrite of the `declMapExt` entry did not take effect (`/tmp/a7probe/ir/IrC.lean`
prints 0).

**Fix:** a dedicated probe should confirm this before launch. The badge could instead recompile the
indexer from source in a clean process.

---

## Verified correct (no action)

- **07/08 statements.** The `Agrees` quantifiers (all `i`, `x`, raw `tr`; honest `VK`/`IDX`), `isSome`
  acceptance, `PerfectComplete` for every `ρ`, `KSF`'s three laws, `Bad` over next-stage witnesses, `RbrKS`
  worst case with `Nat.card` on finite, non-empty challenge types (`Library/Challenges.lean`), and the
  `SecureWith` cap. All listings in 07/08/App. A except `Cost.lean` are verbatim.
- **Machine.**
  - Zbc encodings and `clmulr` bits;
  - W-op division and remainder by zero and overflow;
  - `ECALL` accepted only as the exact word; CSR/ZisK arm unreachable;
  - natural alignment and the tape write window;
  - QUERY closed form; HALT semantics;
  - per-hart fuel; first-touch keys (code and data apart, dirty pages counted twice);
  - timer constants (latencies 1/3/3/16, penalty 5, 1,560/level + leaf, 2,000 spawn/join).
- **Score and certificates.** Profile weights against Table `tab:cost-profiles`, the FS and B formulas,
  `Certificate1`/`Latency1`/`Certificate2` clauses, caps (2^{k+10}, 2^{k+8}, 2^16 queries, tape 2^20, V ≤ 2^8).
- **Baseline.** Closed forms, 3,087,007,761 steps (4.49 % of F), the `tab:base-counters` values and
  `S_{risc0,16}` (recomputed), harness ACCEPT for T1 and L1 with both kernels, gate closures 24,388/24,406,
  and the axioms (`orch-recheck.log`).
- **Pipeline narrative.** The A6-G0 incident, the manifest figures, and the gate rules (i)-(iii) match
  `Gate.lean`.
