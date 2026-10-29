# G2 journal: elaboration time of the heaviest `FRX*` modules

Track G2. Goal: cut the certificate build's CPU time in 15 `FRX*` modules without changing any
statement. Worktree HEAD `2f437ed`; build tree `logs/fr-build-G2` (copied from `logs/fr-build-INT10`,
`MINE.txt` = the 15 modules); logs `logs/G2/`. Report: `reviews/G2-golf.md`.

## 2026-10-29

- **Setup.** `logs/fr-build-G2`, `b.sh` logs to `logs/G2/build-last.log`. Initial build
  `FR Solution FRSubmission4Cert` green (2,558 jobs). Originals saved in `logs/G2/before/`.
- **Statement hashes.** `logs/G2/tool/StmtHash.lean` writes, for every constant of the 15 modules,
  its kind, the hash of its type and (definitions) the hash of its value. Baseline:
  `logs/G2/stmt-before.txt` (5,057 constants).
- **Baseline.** `logs/G2/tools/measure.sh` (sequential, `taskset` one core, `--profile`, no trace):
  `logs/G2/measure-base/summary.txt`.
- **Traced profile of FRXBary** (`prof.sh`, `trace.profiler` threshold 50 ms): 392 CPU-s against 98
  plain, so tracing every module was stopped; traces are taken per module on demand.
  `tools/leaves.py` aggregates the leaf tactic steps and outermost `isDefEq`/`whnf`.
- **Finding 1 (FRXBary).** About 75 % of the traced time is `isDefEq` of
  `rd { M := entryK c n K M, o := o }.M i =?= rd (entryK c n K M) i` (and the same with
  `Array.size`), raised by term-mode frame facts (`ef i …`, `size_entryK ..`) against the
  `loopK_run` invariant `P 0 ⟨entryK …, s.o⟩`. Lazy delta unfolds `entryK` (greater height than the
  projection `St.M`) before reducing the projection, then tries to decide its
  `if rd M₂ cTmp = 0` (`instDecidableEqBitVec` on symbolic words), fails, and backtracks: 2–6 s per
  occurrence. Fix: `attribute [local irreducible] entryK` after the module's `open`. FRXBary 97.6 →
  45.3 CPU-s, no other edit. Applied (`entryK storeM`) to the 11 other modules that use them through
  lemmas only; `FRXDsl` (which defines and unfolds them) excluded.
- **Finding 2 (FRXOut, FRXMsg, FRXEqT, FRXFwd).** The same lazy-delta pattern with `runPrims`:
  `{ M := runPrims ps M, o := o }.M =?= runPrims ps M` unfolds `runPrims` (a `foldl` over the
  concrete primitive list) first: `rw [m1] at m2` in `sibHit_sem` 4.3 s, `inv_sem I hw0 hM` against
  `Inv (runPrims (gPre …) s.M)` 9 s (`gathIR_sem`, `finIR_sem`), `omPs_frame` 5 s. `runPrims` added to
  the local `irreducible` list in FRXOut, FRXMsg, FRXEqT, FRXFwd, FRXFlag, FRXBaryTop. In FRXBfly,
  FRXBary, FRXRead, FRXSortSim, FRXAgree and FRXLookup it breaks `rfl` steps that need
  `runPrims [] M = M` (e.g. `semXIR I (.blk []) s = s`), so there it stays reducible.
- **FRXMsg.** `have hM0 : Inv (runPrims (gPre …) s.M) := inv_sem I hw0 hM` elaborates `inv_sem`
  with `s` still a metavariable; replaced by `have h := inv_sem I hw0 hM; rwa [e0] at h` (both
  sites).
- **FRXEqT.** `nwk i (by tauto)`: `tauto` on a 6-way into 8-way disjunction, 9 s traced per site (two
  sites). Replaced by the term `hi.imp_right (Or.imp_right (Or.imp_right (Or.imp_right
  (Or.imp_right Or.inl))))`.
- **Finding 3 (FRXBfly, FRXFwd, FRXBflyDefs).** `WF`/`Writes`/`Lo` side conditions proved by `simp`
  unfolding `mulF` into `mulFC`'s 117 primitives (and `redC`), per case (`pairBody_nw`: 8 cases).
  New `simp` lemmas `mulF_wf_iff`, `mulF_writes_iff` (FRXBflyDefs; from `wf_mulF`, `nw_mulF`) and
  `mulF_lo_iff` (FRXBfly; from `mulFC_dst`); the 14 `simp` lists drop `mulF, mulFC, redC` and name
  these instead (`logs/G2/tools/mulf.py`). `wf_bflyIR` moved below the new lemmas (same statement).
  `mulF_lo_iff` takes `d < 255`: with `d + 1 < regs` the default discharger fails to close
  `172 + 1 < regs` ("failed to assign proof").
- **FRXDsl.** The same `entryK` pattern inside FRXDsl's own lemmas (`frame`, `compile_correct`,
  `steps_le_cost`, `outs_le`: `h0 : Inv (entryK …)` against `Inv { M := entryK …, … }.M`, 2–3 s
  each). `attribute [local irreducible] entryK` placed after the definitions (before
  `size_storeM`); the lemmas that need its body use `unfold entryK`, which still works. 38.4 → 17.4
  CPU-s.
- **FRXField.** G1's `binop%` pattern: `[.op …] ++ redC … ++ [.op …]` leaves elaborated without
  an expected type (`mulFC` 7.3 s traced, `invBC` 3.6 s). Ascribed `([…] : List Prim)` in `mulBC`,
  `betaC`, `invBC`, `mulFC`, `sqFC`, `invFC`, `alphaC` (G1's `ascribe.py`), reflowed to 100
  columns. Elaboration category 9.8 → 2.9 s; 40.4 → 35.0 CPU-s.
- **Build r1** (`logs/G2/build-r1.log`): `FR Solution FRSubmission4Cert` green, 2,572 jobs.
- **Statement check r1** (`logs/G2/stmt-r1.txt`, `tools/cmpstmt.py`): all 2,024 user constants of
  the 15 modules keep their type hash, every `def` (including the 7 ascribed FRXField definitions)
  its value hash; the only additions are `mulF_wf_iff`, `mulF_writes_iff`, `mulF_lo_iff`. The 3,033
  auxiliary constants of theorems (`_proof_n`, `_simp_n`, the `_f` of recursive theorems) are proof
  internals and are skipped.
- **Finding 4 (all modules but FRXDsl, FRXField): `WF`/`Writes`/`Lo`/`LoK` side conditions by full
  `simp`.** `simp [prog defs, WF, Prim.dst, reg defs]` searches the whole default simp set over the
  unfolded program (FRXLookup: `ansLtIR_frame` 8.3 s traced, 9 cases of 0.9 s). Measured in
  `logs/G2/scratch/nw.lean`: `simp only [defs, Writes]; decide` 0.3 s against 1.3 s. Converted
  mechanically (`tools/sdec.py`, `tools/sdecloop.sh`) to `simp +decide only [same list, list
  lemmas]`: the program definitions are unfolded, `List.mem_cons`/`forall_eq_or_imp`/… expand the
  literal lists, and `+decide` closes the closed numeral facts (`4 ≤ 140`, `155 = 140`; plain
  `simp only` here runs no `Nat` literal simprocs, and a final `decide` fails to synthesize
  `Decidable` for the larger conjunctions). The loop elaborates the module and leaves unconverted
  every call whose block reports an error (FRXBfly 1, FRXOut 2, FRXBary 1 call kept). Then
  `tools/prune.py` removes the added list lemmas that the `unusedSimpArgs` linter reports unused
  (−2,800 names) and drops the parentheses. FRXLookup by hand: `ansLtIR_frame` (one `decide` over
  all 9 registers instead of 9 `simp` cases), `nw_ansLtIR` and the `aposIR` frame
  (`simp only [defs, Writes]; decide`). FRXLookup 37.6 → 17–23 CPU-s.
- **FRXBary, FRXBaryTop.** `nlinarith` (Mathlib, run by the interpreter) for
  `2k·c + 2s + 1 < 2k·C` from `2k(c+1) ≤ 2k·C`: replaced by `rw [Nat.mul_add, Nat.mul_one] at this;
  omega` (4 sites). FRXBary interpretation 6.5 → 2.0 s.
- **Noise.** The VM's load went from 7 to above 20 during the session (another track's prover on 26
  cores); one module's CPU time varies by ±25 % between runs. Before/after figures are taken
  interleaved, minimum of the runs (`tools/measure.sh`).
- **Build r2** (`logs/G2/build-r2.log`): `FR Solution FRSubmission4Cert` green, 2,575 jobs.
  Statements (`logs/G2/stmt-r2.txt`, `logs/G2/check-r2.log`): 0 differences over 2,024 user
  constants; added `mulF_wf_iff`, `mulF_writes_iff`, `mulF_lo_iff`. Axioms (`logs/G2/axioms.log`):
  `propext`, `Classical.choice`, `Quot.sound` for all 5,328 constants of the 15 modules,
  `certificate_sub4` and `certified`. Source rule: 357 files, 0 findings.
- **Final measurement** (`logs/G2/measure-fin1`, `measure-fin2`; before/after interleaved, two cores,
  minimum of 2): 725.9 → 420.4 CPU-s (−42 %); kernel 110.7 → 110.1 s. Table and what was declined:
  `reviews/G2-golf.md`.
