# INT-8 RESULT: revision 4.3, route (A) — group-uniform `gen4`

## Status

All six items are done, with deviations listed below.

- **The groups are uniform.** Within each group the three kinds' programs have one op list up to
  kind tables:
  - segments `L30` = `L31` = `L32`: 106,237 ops;
  - nodes `N2` = `N4` = `N8`: 106,485 ops.
  This is kernel-checked (`node_lengths`, `seg_lengths`) and visible in the dumps.
- **The group program read at index `ι` is the kind's program, op for op.** Each op's kind tables
  are read at `ι` (`Op.at`). This is a structural, `rfl`-level proof (`progNodeGK_rel`,
  `progSegG_rel`). Its run at `ι` is the kind program's run (`progNodeGK_exec`, `progSegG_exec`).
- **`lake build FR FRVIR4Uni` is green** (2,519 jobs) at HEAD `ad3fbeb` once three R4 modules get
  small proof repairs. I made those repairs only in my build tree; R4's files in the worktree are
  untouched. Without the repairs, `FRSoundness4R4Fin`, `FRSoundness4Qry` and `FRSoundness4R4FrE`
  fail (see "For R4d").
- HEAD moved during this stage (`67e5c76` → `ad3fbeb`: S-E12d, S-T2, S-CN4b, R4e, R4f). I
  re-snapshotted and re-verified at `ad3fbeb`: the same three repairs, and every new R4 module builds
  unchanged. None of those commits touched my modules.
- No R4 or P4 statement changes.
- `finalsOf_seq3` (3.x) is intact.
- `items.json` is byte-identical to S-F4's.
- Axioms are standard only, and the source rule reports 0 findings.

## 1. What was built

Code lines are from `logs/org20/scripts/loc.py` (`logs/INT-8/loc.txt`). At HEAD the five edited
modules had 902 code lines.

| Module | Code (HEAD → now) | What |
|---|---|---|
| `FRVIR4` | 133 → 137 | `stmtOps4`: `hashStmt` → `.input 1`. `finalOps4`: reads `m*`'s (empty) tail, the same for every kind. New `stmtBytes4`, `stmtOk4` (the statement fact). |
| `FRVIRFinals4` | 369 → 447 | `KV.fsel`. `FinP`: `mB` removed; `fams`, `e4s`, `ck`, `ncell`, `tails` added. Every generator takes a last argument `Q : Kind → FinP` (default `fun _ => P`): per-kind data (`kv`, `lrR`, `e2R`, `e4R`, cells) are read in kind tables from `Q κ`, counts from `P`. `finPf` rebuilt (below). New generators `selOps`/`selOut`, `pfCand`/`pfCandA`, `gCellOpsK`/`gCellsOpsK`/`gCellsAccK`, `padW`/`padsOps`/`padsReg`, `gTailOps`, and their `noAsk_*` lemmas. `gFinPf_3` re-proved; `finalsOf_seq3` and `finOps4_seq3` unchanged. |
| `FRVerifierC4` | 45 → 99 | `kvOf` per group (`segFams = [30, 31]`, `nodeFams = [31]`, `nodeE4s = [25, 24]`). `segFinP`/`nodeFinP` with the group counts (`nc = 25`, `ck`, `tails`). `runStmt` = run, then the fact (`OProg.bind`), with `queries_bind_ret`, `runSeq_bind_ret`, `runLog_bind_ret`. `VsegC`/`VnodeC` via `runStmt`. Controls. |
| `FRShape4` | 199 → 199 | Comments only (the `ell0` note names `gTailOps`). |
| `FRVIR4Mux` | 156 → 151 | `nodeAt`/`segAt`, groups as `fun ι => .ofNode (nodeAt ι)`. `finalOpsG`, `Grp.ms`, `groupFinP` removed; the group skeleton uses `finalOps4`. New `nodeQ cells`/`segQ`, `progNodeGK cells` (per-kind cells), `progSegG`. `progNodeG (cells : List ℕ)` is kept as `progNodeGK fun _ => cells`. `finOps4F P Q`. |
| `FRVIR4At` (new) | 313 | `Op.at h pf ι`, `Op.isHash`, `OpImpl.fixK`. The bridge lemmas: `evalOp_at`, `exec_forall₂`, `exec_at`, `noHash_of_at`, `reloc_at`. "Map at ι = itself" for every 3.x sub-generator. The finals' reading `map_at_finOps4`, plus `finOps4_counts`, `fixKV_const`. |
| `FRVIR4Uni` (new) | 241 | `skeletonG_at`; `nodeFin_at`/`segFin_at`; `progNodeGK_rel`/`progSegG_rel`; `progNodeGK_exec`/`progSegG_exec`; the controls. |

### How `finPf` is made uniform

Within a group the kinds differ in:
- `m`, and with it `finPf`'s point families, E4 point length, `nc` and the pad chain;
- the nodes' real Lr/E2/E4 counts;
- the cells (`N4` and `N8` have the same counts but different register choices).

Each difference is handled as follows:

- **Point families.** All families of the group are computed: `m* = 32`, then each `m` in `fams`.
  The kind's family is selected by kind tables. `selA` picks `m*`; otherwise `fsel` picks the index
  in `fams`, through `selOps` (a chain of `keep`s). `rsWeight`'s `ptIx` table picks the kind's
  claims, including the node's E4 point of its own length (`e4s`).
- **Pad chains.** One chain per family, selected the same way.
- **`nc`.** The group's 25. For a shorter kind (`N2`: 24), `getK` past `P₀`'s 24 entries reads `0`,
  so the extra coordinate is `1 + 0 = 1`. The cell's bit 24 is `0` (`hcells4`: cells < `2^(m−7)`).
  The extra factor is therefore exactly `1`.
- **Cells.** With `ck`, each cell coordinate is a `keep` on the kind's cell bit (225 ops per node
  program).
- **Lr/E points.** `packFK` with the kind's exact lists.
- **The final message's zero tail.** Moved from the skeleton to the end of `finPf`, after the exports
  (`gTailOps`): one read per `m < 32` of the group, gated by the kind's `m`. No earlier register
  moves.

## 2. Items

1. **Uniform finals per group**: done as in §1. Deviations 1 and 2 cover the padding and dummies.
2. **One final field**: `finalOps4` reads `m*`'s tail in the skeleton, the same for every kind.
   Unlike the blueprint text, the kind's own tail check is kept, in the finals (deviation 3).
3. **`hashStmt` → `.input` plus the fact**:
   - `stmtOps4` imports `c`.
   - The fact is `stmtOk4 S p inp := decide (stmtDigest p.tix (stmtBytes4 S inp.π) = inp.c)`, over
     the same 128 bytes the `msg` register held.
   - `VsegC`/`VnodeC` check it after the run (`runStmt`), so V still checks the statement and asks
     the same queries (`runStmt_queries`).
   - For the slot interface, the fact is what `imp` carries.
4. **The equality**:
   - `skeletonG_at`: the group skeleton read at `ι` is `skeleton4 S (G ι)`, ops and context. It is
     generic in `S`, `G`, `ι`.
   - `map_at_finOps4`, `nodeFin_at`, `segFin_at`: the group finals read at `ι` are the kind's
     `finOps4`.
   - `progNodeGK_rel` / `progSegG_rel`: the two programs are related op by op (`List.Forall₂`).
     Each op is the other read at `ι`: `packF` for the skeleton's segment operand, `packFK` in the
     finals.
   - `progNodeGK_exec` / `progSegG_exec`: if `impl'.fixK κ = impl.fixK ι`, then
     `exec impl ι inp (group).ops = exec impl' κ inp (kind program).ops`. Only `targetS`, `slotW`
     and `linkWAll` read the kind.
   - `hashStmt` is excluded by two readings of it (`noHash_of_at`).
   - Every step is definitional or structural; there is no evaluation of programs.
   - **Accept unchanged** (measured, `logs/INT-8/accdiff/cmp.log`). HEAD's programs were run
     against INT-8's, for every kind, on 2 pseudo-random proofs with the true statement digest and
     1 with a wrong one. The run used a kind-blind mock implementation and a mock oracle, and printed
     a digest of the operands of every active assertion.
     - `L32`, `N4`, `N8`: identical outputs.
     - `L30`, `L31`, `N2`: two differences. The skeleton's tail check now reads an empty field, and
       the identical tail check (same digest) appears at the end.
     - With the wrong digest, one more difference: the program's statement assertion becomes `c = c`.
       The fact line ("fact false") is the rejection: `runStmt_wrong`.
     - Every other check, including all of `finPf`, compares the same values.
     - This is a measurement on random inputs, not a theorem. A full simulation proof is what route
       (A) avoids.
   - The soundness relations still hold: R4's statements (`relLr4`, `relE4`, `fields_of_accept4`,
     …) are unchanged and re-proved; see "For R4d".
5. **R4 re-run**:
   - `R4Acc`, `R4Run`, `R4Ref`, `R4Stmt` build **unchanged**.
   - Three modules need proof repairs (listed under "For R4d").
   - `noAsk_finOps4` still holds, once `Qry` is repaired.
   - At `ad3fbeb`, R4e/R4f's `R4Ex`, `R4Fld`, `R4FrCtrl`, `R4FrCtrlB`, `R4FrS`, `R4FrZ`, `R4FrLc`,
     `R4FrRS`, `R4Tail`, `R4RndK`, `R4W0` build unchanged.
6. **Dumps**: `logs/INT-8/dump/` (`dump.sh`, 3 m 20 s), with `SHA256SUMS`. Details in "For P2".

## 3. Controls

| Control | What it shows |
|---|---|
| `node_lengths`, `seg_lengths`, `progNodeGK_length`, `progSegG_length` (+) | One op count per group (kernel, from the op-for-op relation, no evaluation). Measured: 106,237 / 106,485. |
| `kv_ctrl` (+) | The tables pick each kind's family and claims (`N4` `[0,2,4,6]`, `N2` `[1,3,5,7]`, `L31` family 1). |
| `at_ctl` (−) | The reading depends on the index: the group's Lr point read at `L32` (17 coordinates) is not the one read at `P30` (16). |
| `noHash_ctl` (−) | The two `hashStmt` readings differ, so `noHash_of_at` is not vacuous. |
| `runStmt_iff` (+) | The verifier accepts iff the run accepts and the fact holds. |
| `runStmt_wrong`, `stmtOk4_unique` (−) | A wrong `hashStmt` fact rejects, whatever the run; of two digests at most one passes. |
| `runStmt_queries` (+) | The fact asks nothing. |
| `finP_ctrl`, `VC4_rejects`, `grp_ctl`, `grp_bytes`, `merkleOpsG_ctl` (±) | Kept. `grp_ctl` lost its `Grp.ms` conjuncts: `Grp.ms` is gone. |
| "An honest proof accepted at each kind" | No honest 4.x proof exists in Lean (P2's prover is Rust). Its stand-in is the differential run above: every check of 4.3 compares what 4.2 compared, so an honest proof passes iff it did. **For P2**: run an honest proof per kind through the reloaded `ir.rs`. |

## 4. Builds and times

- Final build: `lake build FR FRVIR4Uni` at HEAD `ad3fbeb` with the three R4 repairs, green, 2,519
  jobs (`logs/INT-8/build-final.log`; the full rebuild at `67e5c76` took 3 m 15 s, `b9.log`).
- Unrepaired R4 build: `logs/INT-8/b6.log`; at `2e5b79a` the same three modules failed (the same
  errors; that log was overwritten by the repaired build).
- Profiles (sequential, `-DElab.async=false --profile`; wall time includes import loading,
  `logs/INT-8/prof-*.log`):

  | Module | Wall (s) | Type checking (s) |
  |---|---|---|
  | `FRVIR4` | 15.9 | 0.72 |
  | `FRVIRFinals4` | 20.4 | 1.76 |
  | `FRVerifierC4` | 8.5 | 0.02 |
  | `FRVIR4At` | 10.5 | 0.55 |
  | `FRVIR4Mux` | 9.3 | 0.05 |
  | `FRVIR4Uni` | 8.9 | 0.12 |

- Axioms: `logs/INT-8/axioms.log`, 45 declarations, `propext`/`Classical.choice`/`Quot.sound` only.
- Source rule: `logs/INT-8/source-rule.log`, 299 files, 0 findings.

## 5. Statement and definition changes, with rulings

- **R4 and P4: none.** Every R4 statement elaborates as before. The new trailing argument `Q` of
  `gFin*`, `finalsOf` and `finOps4 P outs b` has default `fun _ => P`, so `gFinLr P fi b`,
  `finalsOf P`, `finOps4 P` and `gen4 seq4 p (finOps4 P)` keep their meaning. Ruling: the
  blueprint's "no statement changes".
- **`finalsOf_seq3`, `finOps4_seq3`**: unchanged.
- **Definitions changed** (mine, per the ruling (A)):
  - `FinP`, `KV`, `fin3P`, `kv3`.
  - `stmtOps4`, `finalOps4`.
  - `segFinP`/`nodeFinP`/`kvOf`.
  - `VsegC`/`VnodeC`: now `runStmt`. `acc_eqC4` and `VC4_agg_extract` are unchanged and still
    proved.
  - `gen4G`'s final tail; `progNodeG`.
- **My controls**:
  - `grp_ctl` lost two conjuncts (`Grp.ms` removed).
  - `progG_fin` now states the `Q`-finals (`cells : NodeKind → List ℕ`).

## 6. Deviations from the blueprint (revision 4.3, changes 28)

1. **No padded points for Lr/E2/E4.** The kinds' exact lists are `packFK` kind tables of unequal
   lengths.
   - Why: E2's point register also feeds `evalM`, and R4's `relE4` states `evalM` on the unpadded
     point. A `(0, 0)` pad needs a zero register in Lr/E, which adds ops before the exports.
   - Consequence: the compiler handles unequal-length `packFK` as `skip 1`, as for 3.x's `gFinZ`.
     L-circ must bind those operands.
   - The only padding used is the exact factor `1` of `nc`.
2. **The "missing ops" are not gated dummies.** Every kind computes every family of its group, its
   pad chain and the group's `nc`, and selects its own by tables. The only ops placed after the
   exports are the final tails. The values the kind uses are its own (exact, see §2 item 4).
3. **The final tail is still checked.** The blueprint reads "one zero-padded field of the largest
   `m`", which would drop the check that a kind's final message is zero beyond `2^(m−25)` K
   elements. Dropping it makes V accept finals of larger degree for `N2`/`L30`/`L31`: the level-4
   encoding check then binds a 128-coefficient message to that kind's shorter code, a protocol
   change. Instead the skeleton reads `m*`'s (empty) tail, uniformly, and the kind's tail is checked
   in the finals (`gTailOps`, gated by `m`). **Ruling requested**: keep this exact form, or drop the
   check?
4. **"`gen4 κ` by definition" is a structural `rfl`-level theorem** (`Op.at`), not a literal
   equality. `gen4` stays fixed-mode with constant tables and `tix` (R4Link relies on
   `(ofSeg σ).tix = .L32`), while the group program's tables are per index.
5. **The statement fact is checked by `VsegC`/`VnodeC`**, after the run. Without this, V would no
   longer check the statement.

## For P2 (the dumps)

- Files: `logs/INT-8/dump/ops-{L30,L31,L32,N2,N4,N8}.txt`, `group-N.txt`, `group-S.txt` (the mux
  programs), `items.json`, `summary.txt`, `fsummary.txt`, `last.txt`, `IRDump8.lean`, `SHA256SUMS`.
- Cells are S-F4's placeholders (`oneCell + k`), so the dumps compare with S-F4's. Real cells change
  only `keep` tables.
- **Op counts**:

  | Kind | Before (S-F4) | Now |
  |---|---|---|
  | `L30` | 106,064 | 106,237 |
  | `L31` | 106,072 | 106,237 |
  | `L32` | 106,081 | 106,237 |
  | `N2` | 106,221 | 106,485 |
  | `N4` | 106,240 | 106,485 |
  | `N8` | 106,240 | 106,485 |

  Registers: 97,409 for the segments, 97,657 for the nodes. Skeletons: identical counts and
  registers (`summary.txt` identical).
- **`items.json` is byte-identical**, so the transcript (`seq4`) is unchanged.
- **Changes, in program order** (`dd.py`, old against new):
  1. Op 7: `hashStmt r… → r…` becomes `input 1 → r…`. The program's assertion is then `c = c`.
     **The native `acc` must check `stmtDigest(tix, π[48 .. 176)) = c` after the run** (`stmtOk4`):
     `tix = L32` (leaf statement) for segments, `N30` (node statement) for nodes.
  2. The skeleton's final tail is `piField 0 (fo + 4096) 0` with `assertZero` (an empty field) for
     every kind.
  3. Lr/E: five `packF` become `packFK`. In a fixed-kind dump these print the kind's list, as
     before.
  4. `finPf`, nodes (`N2` against `N4`): +25 `mulKF`, +1 `packK` (the second E4 point / `m*`
     family), +1 `getK`, +1 `addK` (`nc` 25), +225 `keep` (cells by table), +9 `mulK` (25-factor
     products).
  5. `finPf`, segments (`L30` against old `L30`): +10 `const`, +62 `mulKF`, +8 `packK`, +81 `addK`,
     +6 `keep`, +2 `getK` (the three families, their selection, the pad chains).
  6. The kind's zero tails, at the very end: one `piField fFinal …` and one gated `assertZero` per
     `m` in `tails`.
- Within a group, op names agree line for line and lines differ in kind tables only. The one
  exception is the segment's Z2 `packF`, which is a `packFK` in `group-S.txt`.

## For R4d (proofs to repair; no statement changes)

Diffs are in `logs/INT-8/r4-repairs/*.diff`, applied and built in `logs/fr-build-INT8`.

- **`FRSoundness4R4Fin`**
  - `flag_gFinLr`, `flag_gFinE`: Lr/E's points are now `cond P.ck (.packFK …) (.packF …)`.
  - Repair: `cases hc : P.ck <;> cases hn : P.kv.node κ <;> simp only [hc, Bool.cond_true,
    Bool.cond_false, hn, …]`.
- **`FRSoundness4Qry`**
  - `noAsk_gFinLr`, `noAsk_gFinE`: `cases hc : P.ck <;> simp [gFinLr, Op.item?, hc]` (and `gFinE`).
  - `noAsk_gFinPf`: new generators. Repair: `cases hc : P.ck`, then `simp only` with
    `noAsk_selOps`, `noAsk_padsOps`, `noAsk_gCellsOpsK`, `noAsk_gTailOps` (in `FRVIRFinals4`),
    `List.filterMap_flatMap`, `Bool.cond_true/false`, then `simp`.
  - `queries_VsegC`, `queries_VnodeC`: add `runStmt_queries` after `VsegC`/`VnodeC` in the `rw`.
  - `noAsk_finOps4` and `ks_queriesC4` then go through unchanged.
- **`FRSoundness4R4FrE`**
  - `opsOut_gFinLr`: `cases hc : P.ck <;> simp [gFinLr, opsOut, Op.outs, hc]`.
- **No repair needed** (at `ad3fbeb`): every other R4 module (`R4Acc`, `R4Run`, `R4Ref`, `R4Stmt`,
  `R4At`, `R4Chain`, `R4Outs`, `R4Rnd`, `R4RndK`, `R4View`, `R4Kind`, `R4Link`, `R4FinLc`,
  `R4FinRS`, `R4FinSh`, `R4FinCtrl`, `R4Ctrl`, `R4Ex`, `R4Fld`, `R4FrCtrl`, `R4FrCtrlB`, `R4FrS`,
  `R4FrZ`, `R4FrLc`, `R4FrRS`, `R4Tail`, `R4W0`) and every `P4*` module.
- For new work: wherever `gFinLr`, `gFinE` or `gFinPf` is unfolded on an abstract `P`, case on
  `P.ck` (`cases hc : P.ck`, `hc`, `Bool.cond_true/false` in the `simp` set).
- The brief's "`R4Stmt`'s `hashStmt` lemmas" do not exist at HEAD; `R4Stmt` builds unchanged.

## For L-circ (S-E12c/d)

- The prototype programs changed, so regenerate `FRNodeRows4Hint` and the prototype dump. The
  hint at HEAD is the old programs'; FR still builds, so nothing kernel-checks it against the program.
- Compile the prototypes from `progNodeGK N4c.cells4` (per-kind cells) and `progSegG`.
  `protoProg 0 = progNodeG (cells4 .N4)` uses `N4`'s cells at every index, so at `P30`/`N30` it is
  `progNode .N2/.N8` with `N4`'s cells.
- `soundN`/`soundS`:
  - From `compileT_sound`'s run at `ι`, use `progNodeGK_exec`/`progSegG_exec` with
    `impl'.fixK κ = impl.fixK ι` and `κ = (KindP.of… _).tix`. A kind-blind slot `impl` for
    `targetS`/`slotW`/`linkWAll` gives it.
  - `VnodeC`/`VsegC` = `runStmt`: the extra conjunct is `stmtOk4`, the `hashStmt` fact for `imp`.
- The group's Lr/E `packFK` operands have unequal lengths across the node kinds (deviation 1).

## Open questions

1. Deviation 3: keep the exact tail check in the finals (as built), or drop it as the blueprint text
   reads?
2. `FR.lean` should import `FRVIR4Uni` (and so `FRVIR4At`) so that `lake build FR` checks them.
   `FR.lean` is not in my edit set.
3. Padded Lr/E points (deviation 1): needed by L-circ's compiler? If so, the padding needs a zero
   register in Lr/E and an unpadded copy for `evalM`. That is an R4 proof change, but no statement
   change.
