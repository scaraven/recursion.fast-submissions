# G2: elaboration time of the heaviest `FRX*` modules

Track G2 targets the certificate build cap. The S-I run (40810876665) took 882 s against
`build_s = 600`. The scope is 15 modules: `FRXBary`, `FRXMsg`, `FRXAgree`, `FRXOut`, `FRXRead`, `FRXFwd`,
`FRXBfly`, `FRXFlag`, `FRXField`, `FRXBaryTop`, `FRXEqT`, `FRXLookup`, `FRXDsl`, `FRXBflyDefs` and
`FRXSortSim`. No other module was edited.

The work is uncommitted, in the worktree at HEAD `2f437ed`. The build tree is `logs/fr-build-G2`
(copied from `logs/fr-build-INT10`, `MINE.txt` = the 15 modules); logs are in `logs/G2/`. The running
record is `stages/G2-JOURNAL.md`.

## 1. Result

**Method.** Sequential elaboration on one pinned core: `lean -DElab.async=false --profile`, no trace.
CPU time is user + sys.

- "before" is the saved original source (`logs/G2/before/`), run against the same tree; "after" is the
  worktree.
- Before and after alternate, two rounds, on two cores. Each figure is the **minimum** of the two runs,
  because other tracks (a prover on 26 cores) took the VM's load from 7 to above 20 during the session,
  and a single module varied by up to ±25 % between runs.
- Logs: `logs/G2/measure-fin1/` and `measure-fin2/` (`summary.txt`); the first baseline is
  `logs/G2/measure-base/`.
- "7763" is the EPYC 7763 runner's CPU-s for the module (`logs/S-I/run-40810876665/build-modules.txt`).

| module | 7763 | before: CPU s, min (runs) | after: CPU s, min (runs) | change | kernel s, before → after |
|---|---|---|---|---|---|
| FRXBary | 69 | 95.2 (95.2 / 99.9) | 33.2 (43.1 / 33.2) | −65 % | 6.6 → 6.8 |
| FRXMsg | 54 | 76.2 (76.2 / 83.2) | 46.9 (47.2 / 46.9) | −39 % | 11.8 → 12.2 |
| FRXAgree | 53 | 35.6 (42.9 / 35.6) | 31.9 (33.7 / 31.9) | −10 % | 19.9 → 20.2 |
| FRXOut | 47 | 76.0 (85.1 / 76.0) | 35.8 (36.0 / 35.8) | −53 % | 3.1 → 3.0 |
| FRXRead | 46 | 53.2 (53.2 / 59.3) | 24.1 (32.2 / 24.1) | −55 % | 5.6 → 5.6 |
| FRXFwd | 46 | 53.8 (60.8 / 53.8) | 19.7 (19.7 / 21.2) | −63 % | 4.4 → 3.9 |
| FRXBfly | 43 | 60.4 (61.4 / 60.4) | 37.6 (51.1 / 37.6) | −38 % | 8.7 → 8.4 |
| FRXFlag | 39 | 49.0 (49.6 / 49.0) | 41.7 (48.0 / 41.7) | −15 % | 19.3 → 19.3 |
| FRXField | 34 | 46.0 (57.3 / 46.0) | 37.4 (43.9 / 37.4) | −19 % | 12.2 → 12.0 |
| FRXBaryTop | 32 | 31.4 (38.0 / 31.4) | 18.8 (22.8 / 18.8) | −40 % | 5.6 → 5.2 |
| FRXEqT | 28 | 40.4 (44.1 / 40.4) | 19.1 (20.1 / 19.1) | −53 % | 2.7 → 2.5 |
| FRXLookup | 27 | 29.5 (40.1 / 29.5) | 17.4 (21.8 / 17.4) | −41 % | 2.4 → 2.3 |
| FRXDsl | 22 | 33.9 (33.9 / 36.5) | 22.4 (24.0 / 22.4) | −34 % | 5.5 → 5.8 |
| FRXBflyDefs | 16 | 13.2 (14.1 / 13.2) | 9.8 (10.0 / 9.8) | −25 % | 0.4 → 0.3 |
| FRXSortSim | 16 | 32.0 (32.0 / 36.3) | 24.7 (24.7 / 28.8) | −23 % | 2.5 → 2.5 |
| **total** | **572** | **725.9** | **420.4** | **−42 %** | **110.7 → 110.1** |

Each module's figure includes its fixed import cost, 3–6 s.

- **On the 7763.** Scaled by module, the cut is about 240 of the 572 CPU-s these modules take there.
  This is an estimate from the local ratio, not a measurement.
- **Kernel time** is unchanged at about 110 s. Of it, 52 s is the `decide +kernel` machine controls in
  `FRXAgree`, `FRXFlag` and `FRXField` (§3).

**Code lines** (`logs/org20/scripts/loc.py`, code column): 11,158 → 11,346 (+188, +1.7 %). The `simp`
lists below are longer than the `simp [...]` calls they replace.

**Checks.**

- **Build.** `lake build FR Solution FRSubmission4Cert` is green: 2,575 jobs (`logs/G2/build-r2.log`).
- **Statements** (`logs/G2/tool/StmtHash.lean`, `tools/cmpstmt.py`; `logs/G2/stmt-before.txt` against
  `stmt-r2.txt`, `logs/G2/check-r2.log`).
  - **0 differences** over the 2,024 user constants of the 15 modules: every type hash is unchanged, and
    every `def` keeps its value hash. This includes the seven FRXField definitions given type
    ascriptions.
  - The 3,033 auxiliary constants of theorems were skipped. These are `_proof_n`, `_simp_n` and the `_f`
    of recursive theorems; they are proof internals, renumbered by the edits.
  - Added: `mulF_wf_iff`, `mulF_writes_iff` (FRXBflyDefs) and `mulF_lo_iff` (FRXBfly).
- **Axioms** (`logs/G2/tool/Ax.lean`, `logs/G2/axioms.log`). The 5,328 constants of the 15 modules use
  only `propext`, `Classical.choice` and `Quot.sound`. So do `FR.Sub4.certificate_sub4` and
  `RecursionFast.Challenge.certified`.
- **Source rule.** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive` reports
  357 files, 0 findings (`logs/G2/source-rule.log`).

## 2. What changed

### 2.1 Lazy delta through `entryK`/`runPrims` (FRXBary, FRXDsl, FRXOut, FRXMsg, FRXEqT, and others)

The largest cost was one unification pattern. A loop invariant is stated on `⟨entryK c n K M, o⟩`
(`loopK_run`'s `P 0 ⟨entryK …, s.o⟩`). A frame fact about `entryK c n K M` is then checked against the
form with the projection. For example:

- `ef i …`, `size_entryK ..` and `h0 : Inv (entryK …)` against `rd { M := entryK …, o := … }.M i` or
  `Inv { M := entryK …, … }.M`.

Lazy delta unfolds `entryK` before the projection `St.M`, because `entryK` is the higher definition. It
then tries to decide `entryK`'s `if rd M₂ cTmp = 0` (`instDecidableEqBitVec` on symbolic words), fails,
and backtracks. This costs 2–6 s per occurrence (`logs/G2/prof-base/FRXBary.log.raw`). FRXBary had 21
such terms (13 on `rd`, 8 on `Array.size`), about 75 % of its traced time.

`runPrims` (a `foldl` over a literal primitive list) causes the same pattern. Examples:

- `rw [m1] at m2` in `sibHit_sem`, 4.3 s;
- `inv_sem I hw0 hM` against `Inv (runPrims (gPre …) s.M)` in `gathIR_sem`/`finIR_sem`, 9 s each;
- `omPs_frame`, 5 s.

**Fix:** `attribute [local irreducible] entryK storeM` after the module's `open`.

- In FRXOut, FRXMsg, FRXEqT, FRXFwd, FRXFlag and FRXBaryTop, the list is `entryK storeM runPrims`.
- In FRXBfly, FRXBary, FRXRead, FRXSortSim, FRXAgree and FRXLookup, a `rfl` needs `runPrims [] M = M`
  (for example `semXIR I (.blk []) s = s`), so `runPrims` stays reducible there.
- FRXDsl defines `entryK`, so its `attribute [local irreducible] entryK` comes after the definitions.
  Its lemmas reach the body with `unfold entryK`, which still works.

The attribute is local: no declaration and no downstream module sees it. `FRBlake2sGeneric` uses the
same form. FRXBary alone went from 97.6 to 45.3 CPU-s with this one line (`logs/G2/try/summary.txt`).

FRXMsg also elaborated `inv_sem I hw0 hM` with `s` still a metavariable. These became
`have h := inv_sem I hw0 hM; rwa [e0] at h` (2 sites).

### 2.2 `WF`/`Writes`/`Lo` side conditions: `simp +decide only` (12 modules)

The pattern was `simp [prog defs, WF, Prim.dst, reg defs]`: the full default simp set run over an
unfolded program, often once per register (`rcases … <;> simp […]`).

- FRXLookup's `ansLtIR_frame` took 8.3 s traced (9 cases of 0.9 s).
- A scratch test (`logs/G2/scratch/nw.lean`) measured `simp only [defs, Writes]; decide` at 0.3 s,
  against 1.3 s for the full `simp`.

The calls became `simp +decide only [same list, list lemmas]`:

- `List.mem_cons`, `forall_eq_or_imp`, `exists_eq_or_imp`, `forall_eq` and the like expand the literal
  lists;
- `+decide` closes the closed numeral facts (`4 ≤ 140`, `155 = 140`).

Plain `simp only` runs no `Nat` literal simprocs here. A trailing `decide` cannot synthesize `Decidable`
for the larger conjunctions.

The conversion is mechanical:

- `logs/G2/tools/sdec.py` rewrites each `simp [...]` that names `WF`, `Writes`, `Lo` or `LoK` and is not
  `at h`.
- `tools/sdecloop.sh` elaborates the module and leaves unconverted every call whose block reports an
  error. Kept: 1 call in FRXBfly, 2 in FRXOut and 1 in FRXBary, which were not terminal or not closed.
- `tools/prune.py` removes the added list lemmas that the `unusedSimpArgs` linter reports unused (about
  2,800 names), so each list keeps only what it uses.

FRXLookup also has three hand edits:

- `ansLtIR_frame`: one `decide` over all nine registers instead of nine `simp` cases;
- `nw_ansLtIR` and the `aposIR` frame in `foundIR_sem`: `simp only [defs, Writes]; decide`.

The FRXSortSim control `not_lo_heap` changed its proof the same way; its statement is unchanged.

### 2.3 `mulF` never unfolded in side conditions (FRXBfly, FRXFwd, FRXBflyDefs)

Some `WF`/`Writes`/`Lo` simps unfolded `mulF` into `mulFC`'s 117 primitives and `redC`. Examples are
`pairBody_nw` (8 cases) and `fpairBody_nw`, `wf_fwdIR`, `wf_bflyIR`. There are three new `simp` lemmas:

- `mulF_wf_iff`, from `wf_mulF`, in FRXBflyDefs;
- `mulF_writes_iff`, from `nw_mulF`, in FRXBflyDefs;
- `mulF_lo_iff`, from `mulFC_dst`, in FRXBfly. Its hypothesis is `d < 255`. With `d + 1 < regs`, the
  default discharger fails on `172 + 1 < regs` ("failed to assign proof").

The 14 lists drop `mulF, mulFC, redC` and name these lemmas instead (`tools/mulf.py`). `wf_bflyIR` moved
below the new lemmas; its statement is unchanged.

### 2.4 Definitions: `binop%` with list-literal leaves (FRXField)

This is G1's finding. In `[.op …] ++ redC … ++ [.op …]`, each list leaf elaborates without an expected
type. It fails, and the elaborator retries it later: `mulFC` took 7.3 s traced and `invBC` 3.6 s.

The fix ascribes the leaves as `([…] : List Prim)` (G1's `ascribe.py`) in `mulBC`, `betaC`, `invBC`,
`mulFC`, `sqFC`, `invFC` and `alphaC`. The lines are reflowed to 100 columns. The elaboration category
fell from 17.0 to 3.5 s (fin1). The value hashes of all seven definitions are unchanged (§1).

### 2.5 Smaller edits

- **FRXEqT `eqBody_sem`.** `nwk i (by tauto)` turned a 6-way disjunction into an 8-way one, at 9 s
  traced per site (2 sites). It is now the term `hi.imp_right (Or.imp_right (Or.imp_right
  (Or.imp_right (Or.imp_right Or.inl))))`.
- **FRXBary, FRXBaryTop.** `nlinarith` (Mathlib, run by the interpreter) proved
  `2k·c + 2s + 1 < 2k·C` from `2k(c+1) ≤ 2k·C`. It is now `rw [Nat.mul_add, Nat.mul_one] at this;
  omega` (4 sites). FRXBary's interpretation time fell from 6.5 to 2.0 s.

## 3. Declined, and why

- **The `decide +kernel` machine controls** cost about 52 kernel-s locally:
  - `FRXAgree` `toyScan_two`/`toyScan_six`, about 20 s;
  - `FRXFlag` `toyFlag_run`, 17 s;
  - `FRXField` `mulK_kat`/`mulF_kat`/`mulF_bad_const`, about 10 s;
  - `FRXDsl`'s toys, a few s.

  Each one evaluates `XProg.run` (the core's `XStmt.exec`) in the kernel. Memory is an `Array` of 260–300
  words, so every `getD`/`setIfInBounds` walks a list. The fuel, memory size and program are part of each
  statement. Any proof must run the machine, and nothing I can change in the proof makes the kernel's
  `Array` cheaper. These are the positive and negative controls the rules require.

  A cheaper control would need a smaller statement: fewer memory words, such as `toProg` with registers
  placed lower, or a shorter program. That decision belongs to the module owner and the orchestrator.
- **`omega` in FRXMsg, FRXBfly and FRXOut.**
  - In the traces, `omega` costs 21.6 s in FRXMsg, 10.6 s in FRXBfly and 7.2 s in FRXOut. The FRXMsg
    figure includes the kernel check of its auxiliary `_proof_n`; FRXMsg's 12 kernel-s are mostly
    those.
  - The calls are spread over about 190 sites, each 0.1–0.4 s, typically
    `(by simp only [regs]; omega)` for `regs ≤ yb + 2 * x`. The large contexts include three
    disjunctions (`hd`, `hdx`, `hdy`), on which omega splits.
  - A real cut means restructuring each step: derive the address facts once and reuse them, or `clear`
    the disjunctions per call. That is per-proof work, which I did not start (`tools/omparent.py`
    aggregates the calls by parent step).
- **`runPrims` irreducible in the other six modules.** In FRXBfly, FRXBary, FRXRead, FRXSortSim,
  FRXAgree and FRXLookup, between 1 and 2 `rfl`/term steps per module need `runPrims` to unfold. Making
  it irreducible there means rewriting those steps. FRXBfly's remaining runPrims-like `isDefEq` costs
  about 4 s traced.
- **FRXOut's remaining `simp` (about 11 s).** It is spread over:
  - `simp (disch := …) only [rd_set_self, rd_set_ne]` chains, 0.2–1 s each;
  - `simp [depthSeg] at h; omega` in the structural recursions `wf_segIR`/`loK_segIR` (8 × 0.25 s);
  - `simp [wrL, …]` writes-list facts.

  None dominates.
- **Kernel time in general.** It is unchanged at 110 s here. The certificate's kernel replay (H-cert:
  372 s against `kernel_s = 600`) is not made worse.

## 4. For the orchestrator

- **The `entryK`/`runPrims` lazy-delta pattern is likely elsewhere.** It appears wherever a term-mode
  frame fact about `entryK …`/`runPrims …` meets `{ M := …, o := … }.M`. In FRXNode, FRXLag and the
  FRXChain* modules (off limits here), `attribute [local irreducible] entryK storeM` is the first thing
  to try.
- **Finding it.** Run `trace.profiler` and look at the outermost `Meta.isDefEq` entries
  (`logs/G2/tools/leaves.py`). Tracing inflates such a module up to 4× (FRXBary: 392 against 98
  CPU-s), so profile one module at a time.
- **The `simp +decide only` conversion is mechanical.** `tools/sdecloop.sh <Module>` followed by
  `tools/prunemod.sh <Module>` converts and prunes a module's lists. It applies to any module with
  `simp [prog, WF/Writes/Lo, …]` side conditions.
- **Tools** (`logs/G2/tools/`):
  - `measure.sh`, `one.sh`, `ab.sh`: timing;
  - `prof.sh`, `leaves.py`, `omparent.py`: traces;
  - `sdec.py`, `sdecloop.sh`, `prune.py`, `prunemod.sh`, `mulf.py`: the conversions;
  - `cmpstmt.py` with `logs/G2/tool/StmtHash.lean`: statement and definition hashes;
  - `logs/G2/tool/Ax.lean`: axioms.
- **Build warnings.** The converted lists still carry some `unusedSimpArgs` warnings on their original
  names. The original `simp [...]` calls named, for example, `Prim.dst` or register definitions that
  the `+decide` form no longer needs. They are warnings only, and I left them, so each list stays a
  superset of the original's names.
