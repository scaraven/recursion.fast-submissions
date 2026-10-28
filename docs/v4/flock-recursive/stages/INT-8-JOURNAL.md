# INT-8 journal (revision 4.3, route (A): group-uniform `gen4`)

## 2026-10-28 — set-up and design

- Build tree `logs/fr-build-INT8` (copy of `logs/fr-build-orch`, warm; `snap.sh` with
  `MINE="FRVIR4 FRVIRFinals4 FRVerifierC4 FRShape4 FRVIR4Mux …"`), against `logs/org20`. Baseline
  `lake build FR` green, 2,503 jobs (`logs/INT-8/build-baseline.log`).
- Read: TRACK-RULES, BLUEPRINT changes 28, S-E12c §1, the modules, the S-F4 dumps. Op-name diffs of the
  S-F4 dumps (finals only; the skeletons agree within a group): N2 vs N4 = 19 inserted ops in `finPf`
  (mB-family point coordinates `mulKF`/`addK`, `getK`/`addK` of `nc`, the cells' `mulK`, one pad
  `addK` the other way); N4 vs N8: no op-name difference (cells differ in register choices);
  L30/L31 vs L32: the same families plus `nc` and the pad chain.
- **Design decisions** (each recorded with its reason in the RESULT):
  1. `gen4` keeps its fixed mode `.fixed p.tix` and its constant tables (R4/P4 are generic over
     `p : KindP` and rely on `tix`: R4Link's `(ofSeg σ).tix = .L32`). "The group program at `ι` is
     `gen4 (G ι)`" is therefore the **specialisation** statement: the group program's ops with every
     kind table read at `ι` (`Op.at`) are, list for list, `gen4 (G ι)`'s ops; proved structurally
     (generic in `S`, `G`, the context), and its `exec` corollary (`exec impl ι` of the group program
     = `exec impl' p.tix` of `gen4 (G ι)` when `impl'` reads at `p.tix` what `impl` reads at `ι`).
  2. The finals take a count source `P` and a per-index table `Q : Kind → FinP` (default
     `fun _ => P`): every per-kind datum (`kv`, `lrR`, `e2R`, `e4R`, the cells) is read in a kind
     table `(Q κ).…`; every count (op numbers, register layout) is `P`'s. `finalsOf P` is unchanged
     in name and, at the default, reads the same values (R4's statements stand).
  3. `finPf`: point families as a list (`fams`, 3.x `[30]`), E4 points as a list (`e4s`, 3.x `[23]`),
     a family selector table `fsel`, the pad chain per family, `nc` the group's (25; the shorter
     kinds' extra coordinate is a factor `1`: `P₀[nc−1]` reads `0`, the cell's bit is `0`); the cells
     by kind table (`ck`: `keep` per coordinate) since `N4`/`N8` differ in register choices.
  4. The final message: the skeleton's `finalOps4` reads the (empty) tail of `m* = 32`, uniform; the
     kind's zero tail moves to the end of `finPf` ("after the exports"): one read per distinct `m < 32`
     of the group, gated by the kind's `m`. Exact: every kind checks exactly its old tail.
  5. `hashStmt` → `.input 1` in `stmtOps4`; the fact `stmtDigest p.tix (stmt) = c` is checked by
     `VsegC`/`VnodeC` after the run (`OProg.bind`): same queries, same accept.

## Implementation

- `FRVIRFinals4`: `KV.fsel`; `FinP` without `mB`, with `fams`, `e4s`, `ck`, `ncell`, `tails`; every
  generator takes `Q` last (default `fun _ => P`), so R4's `gFinLr P fi b` etc. keep their meaning;
  the `¬ck` branches read `Q .L32` (= `P` at the default), so `finalsOf_seq3` holds literally (proof
  of `gFinPf_3` re-done: three `simp only` passes, the third with `padReg`, `padW`, `gTailOps`).
  New: `pfCand`, `pfCandA`, `selOps`/`selOut`, `gCellOpsK`/`gCellsOpsK`/`gCellsAccK`, `padW`,
  `padsOps`, `padsReg`, `gTailOps`, and their `noAsk_*` lemmas (for R4d's `Qry` repair).
- `FRVIR4`: `stmtOps4` imports `c` (`.input 1`); `finalOps4` reads `m*`'s tail (uniform);
  `stmtBytes4`, `stmtOk4`.
- `FRVerifierC4`: `kvOf` per group (`segFams = [30, 31]`, `nodeFams = [31]`, `nodeE4s = [25, 24]`),
  `segFinP`/`nodeFinP` with the group counts; `runStmt` (run, then the fact; `queries_bind_ret`,
  `runSeq_bind_ret`, `runLog_bind_ret`); `VsegC`/`VnodeC` via `runStmt`; controls `kv_ctrl`,
  `runStmt_iff`, `runStmt_wrong`, `stmtOk4_unique`, `runStmt_queries`.
- `FRVIR4At` (new): `Op.at`, `OpImpl.fixK`, `evalOp_at`, `exec_forall₂`, `exec_at`, `noHash_of_at`,
  the finals' map lemmas (`map_at_finOps4`), `finOps4_counts`, `fixKV_const`.
- `FRVIR4Mux`: `nodeAt`/`segAt`, `nodeQ`/`segQ`, `progNodeGK`, `progNodeG` (compat), `progSegG`;
  `finalOpsG`/`Grp.ms`/`groupFinP` removed.
- `FRVIR4Uni` (new): `skeletonG_at`, `progNodeGK_rel`/`progSegG_rel`, `progNodeGK_exec`/
  `progSegG_exec`, length controls.
- Pitfalls met: `Op.at` must be `_root_.FR.Op.at` (dot notation); `congr 1` / `exact` against
  `(skeleton4 …).2` made Lean whnf the skeleton (timeouts): rewrite `nodeGrp ι` to
  `.ofNode (nodeAt ι)` first and give the implicit arguments.
- `lake build FR` (build tree with three R4 modules patched, `logs/INT-8/r4-repairs/*.diff`): green,
  2,505 jobs (`logs/INT-8/b9.log`). Unpatched: `FRSoundness4R4Fin`, `FRSoundness4Qry`,
  `FRSoundness4R4FrE` fail (b6.log); `R4Acc`, `R4Run`, `R4Ref`, `R4Stmt` build unchanged.

## Dumps, checks, measurements

- Dumps (`logs/INT-8/dump.sh`, the S-F4 tool as `IRDump8.lean`, plus `group N|S`): 3 m 20 s.
  Ops: L30 = L31 = L32 = 106,237; N2 = N4 = N8 = 106,485; the group programs the same. `items.json`
  byte-identical to S-F4's; `summary.txt` (skeletons) identical. Within a group the op names agree
  line for line; the lines differ in kind tables only, plus Z2's `packF` operand of a segment (the
  group's `packFK`, read with `pf = true`).
- Old → new op changes (difflib on op names, `dd.py`): `hashStmt` → `input` at op 7; Lr/E's five
  `packF` → `packFK`; `finPf`: N2 +25 `mulKF`, +1 `packK`, +1 `getK`, +1 `addK`, +225 `keep`, +9 `mulK`,
  +1 `piField`, +1 `assertZero` (the tail); L30 +10 `const`, +62 `mulKF`, +8 `packK`, +81 `addK`,
  +6 `keep`, +2 `getK`, +2 `piField`, +2 `assertZero`.
- Axioms (`logs/INT-8/axioms.log`, 45 declarations incl. R4's repaired `flag_gFinLr`/`flag_gFinE`):
  standard only. Source rule: 296 files, 0 findings (`logs/INT-8/source-rule.log`).
- Profiles (sequential, `-DElab.async=false`, wall incl. imports / kernel): FRVIR4 15.9 s / 0.72 s,
  FRVIRFinals4 20.4 s / 1.76 s, FRVerifierC4 8.5 s / 0.02 s, FRVIR4At 10.5 s / 0.55 s, FRVIR4Mux
  9.3 s / 0.05 s, FRVIR4Uni 8.9 s / 0.12 s (`logs/INT-8/prof-*.log`).
- R4d's untracked `FRSoundness4R4Ex` compiles against these changes (`logs/INT-8/r4ex.log`); the
  other untracked R4/S-CN4 files depend on untracked modules and were not tried.
- Differential run (`logs/INT-8/accdiff/`): HEAD's programs (tree `fr-build-INT8old`, a copy of the
  orchestrator's at HEAD) against INT-8's, each kind, 2 pseudo-random proofs with the true statement
  digest and 1 with a wrong one, under a kind-blind mock implementation and a mock oracle; every
  active assertion's operand digests printed.

## HEAD moved (67e5c76 → ad3fbeb)

- S-E12d, S-T2, S-CN4b, R4e and R4f were committed during the stage; none touched my modules.
  Re-snapshotted twice. At `2e5b79a` the same three R4 modules failed (same errors); with the same
  repairs FR is green. At `ad3fbeb`: green, 2,519 jobs with `FRVIR4Uni` (`build-final.log`).
  Axioms re-run (45 declarations, standard); source rule 299 files, 0 findings.
- Differential run results (`accdiff/cmp.log`): `L32`/`N4`/`N8` identical; `L30`/`L31`/`N2` differ
  only by the tail check moving (same digest) to the end; with a wrong digest, the program's
  statement assert becomes `c = c` (the fact rejects). Every `finPf` check compares the same values.
