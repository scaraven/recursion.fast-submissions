# CK RESULT: prototype 0's unequal-length `keep` chain compiled into rows (SRA §4.2)

Track CK, 2026-10-29. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at HEAD `27459d9`,
re-snapshotted onto **`74a2528`** (ASK-P) for the final build and every regeneration. Build tree
`logs/fr-build-CK` (copy of `fr-build-SRA`; MINE = `FRVIRCompile FRVIRCompileSound FRVIRCompileK
FRVIRFinals4 FRNodeRows4Hint FRVIRTplSet FRNodeRows4Model`, every other module HEAD's text). Logs
`logs/CK/`; journal `CK-JOURNAL.md`. No sub-agents, nothing committed, no `sorry`. Every lake/lean/probe
ran in a 16 GB scope under `timeout`.

## 0. Summary

| Item | State |
|---|---|
| The gap | **Closed.** Prototype 0's op#109053 `assertEq` is now row-enforced; prototype 0 has **14** foreign flags (was 15), prototype 1 **79** (`logs/CK/forsdump2.log`) |
| Option | **Neither 1 nor 2 literally: a compile-side extension, no change to V** (§1). V's op list, registers, values and every V proof are unchanged |
| Foreign flags now | **93** in all: **2** kind-byte `assertEq (piField 0 48 1) const` (one per prototype) and **91** `assertZero (piField 0 o len)` zero pins on proof bytes (13 + 78). Nothing else (§3). (SRA §4.1's "92 zero pins" is a miscount of its own table: 13 + 78 = 91.) |
| Statement changes | **None.** `tplExt4`'s *definition* gains the new extension; every theorem statement is unchanged (§2) |
| Build | `lake build FR Solution FRSubmission4Fin` (+ probes) at `74a2528`: **green, 5,056 jobs, 0 `sorry`** (`logs/CK/build-full2b.log`; at `27459d9`: 2,655 jobs, `build-full.log`) |
| Axioms | 12 declarations incl. `RecursionFast.Challenge.certified`, `extGetK_okK`, `tplExt4_okK`, `compileTF4_soundAt`: ⊆ {`propext`, `Classical.choice`, `Quot.sound`} (`logs/CK/axioms.log`) |
| Source rule | 442 files, 0 findings (`logs/CK/source-rule.log`) |
| Fit | p0 rows in its region 700,160 → **706,304** (< arR2 720,896), skeleton cells end 283,546 (≤ arA1 290,816), 0 overlaps; p1 unchanged; **N8 unchanged** (§4) |
| Hint | regenerated: `hintLay0`'s row bases only (+6,144 … +6,656); `hintLay1` unchanged. Same at `27459d9` and `74a2528` |
| Plan, KAT | `inR true`; `plan4t check` **N2, N4, N8 equal true** (full sparse sums, 3,600 s cap; N8 848 s); MxKat (ASK-P's reference) **33/33 true** |
| V(N4), plan init | V(N4) own kind 275.8 → 297.2 ms best; plan init 6.2–7.4 s (HEAD) vs 6.7–9.3 s (CK) (§5) |

## 1. Diagnosis and the option chosen

- The five `keep`s (op#101817–101821) are `FRVIRFinals4.gFinPf`'s
  `.keep selA (pfCandA P Pp s) (selOut …)` for `s < 5`: the `m*` family's tails `P₁ … P₄` and `P₀`
  against the other family's, of lengths `n` and `n − 1` (AK19/AK18 … AK25/AK24).
- They were **not** plain `skip`s. The kind mux (`tplExtKM`, S-E12f) already gave them **per-kind
  slots** (`CS.kslots`, `keepK`: the kind's operand), with no kind-free slot. Their consumers:
  - `tensorW` (the tails, in `gLvOps`): templated per kind (`.tensorWK`);
  - `rsWeight` (`P₀`): an import;
  - **`getK (sb + 4) v`, `v < 25`** (`P₀`'s coordinates): left to `opOut`, which reads only the
    kind-free slot and skipped it.
- Everything after depended on those 25 `getK`s: `addK one`, the cells' `keep`/product chains
  (`gCellsOpsK`), the reserve-cell chain, the level sums (`gLvsOps`), the final `mulK`s. It ended in
  `finPf`'s `assertEq (pe + nf + 1) (claimN fi "Pf")` = op#109053. (SRA §4.2 called this the (β′) cap
  check. It is `finPf`'s final equation, whose level sums contain the cap-entry MAC terms
  `piElemK × getK (eqTableK …)`; the (β′) family's own three `assertEq`s were already tracked.)
- **Fix:** give `getK` of a kind-muxed register a kind mux of the kinds' forms. That is the smallest
  sound change:
  - Option 1 (zero-pad in `keep`) would break `RepS`: the value at the shorter kind is an
    `ak (n − 1)`, so a slot of type `ak n` cannot represent it. It would need a new `Ty` or a
    weaker `RepS`, which every op's proof would have to absorb.
  - Option 2 (pad `gPfPts`) changes V: `rsWeight`'s and `tensorW`'s inputs, the registers, and the
    proofs over `gFinPf` (`FRSoundness4R4Wt`, `W0R`, `PfRun`, `PfFlag`, `Full`, `LinkP`).
  - The extension changes neither V nor any statement.

## 2. The compile change and its soundness

**New module `FRVIRCompileK`** (79 code lines, 4 theorems):

- `mux3 P cs x o`: the three kinds' forms `x κ`. If they agree, their common form with no row.
  Otherwise three fresh cells `c_κ` with the rows `sel_κ · x_κ = c_κ` and the form `c_L + c_P + c_N`.
  **`mux3_ev`**: under `SelOk w P κ`, if the rows hold, the form evaluates to `x κ`.
- `gkForm cs a i j κ = (asAK (cs.slotK a κ)).getD (2i + j) []`. Beyond a kind's length it is `[]`,
  which is `getK`'s value there (`Array.getD … 0`).
- `kindTyped cs a`: `a` has no kind-free slot but has a slot at every kind.
- `getKK`: per F component, `mux3` over `gkForm` (six fresh cells, at most six rows).
- `extGetK`: `getK a i` with `kindTyped cs a` goes to `getKK`; every other op gets `none`.
- **`extGetK_okK : ExtOkK impl tc extGetK κ`**, for every `impl`, `tc` and `κ`. Its result has the
  op's arity, no `kin`, no ask, and represents `.k ((rd regs a).toAK.getD i 0)` from the operand's
  per-kind `RepS` (`InvK`'s third conjunct).

**`FRVIRTplSet`** (513 → 515 code lines): `import FRVIRCompileK`, and

```lean
def tplExt4 (F : TFilt) (R : ShR) (tc : TCtx) : Ext :=
  (tplExt4S F R tc).orElse fun P cs op =>
    if R.kmux then ((tplExtKM F tc).orElse extGetK) P cs op else none
```

`tplExt4_okK`'s proof changes in one line: `(tplExtKM_okK hT L).orElse extGetK_okK`. **Its statement
is unchanged.** So `compileTF4_soundAt`, B3's `compileFromX_run`, C1's replay induction and everything
over `Xof π`/`XofT π` hold as before (they are generic in an `ExtOkK` extension). `tplExt4_imp`
(no route: `tplExtF`) is unchanged, so 3.x is unaffected.

**No theorem statement changed.** The definitions that changed are `tplExt4` (and through it
`compileTF4`, `protoCS`, `protoRows`, `nodeIRows4`), `hintLay0`, and `FRNodeRows4Model`'s literal
`protoRowsN` (§4).

**Controls** (`FRVIRCompileK`, `decide +kernel`):

| | (+) | (−) |
|---|---|---|
| `extGetK` | `extGetK_ctl`: a kind-muxed register's `getK` is tracked as `K`, with 6 mux rows at element 0 and at element 1 (beyond the shorter kinds); kinds' forms that agree give 0 rows | `extGetK_ctl`: a register with a kind-free slot, and one without a slot at some kind, are left to `opOut` |
| `gkForm` | `gkForm_ctl`: `L32`'s form of element 1 is cell 2 | `gkForm_ctl`: `P30`'s is `[]`, so no kind-free form exists and the mux is needed |

`tplExtKM_ctl` (S-E12f's controls of the kind mux through `tplExt4`) re-checks unchanged.

## 3. Foreign flags and `skip`s after the change

`logs/CK/forsdump2.log` (SRA's `ForsDump`) and `logs/CK/ckskips2.log` (new probe `CKSkips`), at `74a2528`:

- **Prototype 0, 14 flags:**
  - reg 10: the kind byte `assertEq (piField 0 48 1) const`;
  - 13 `assertZero (piField 0 o len)` at regs 11, 182, 597, 1203, 1504, 1914, 2246, 48708, 57170,
    57232, 57233, 57234 and 100346 (offsets as in SRA's `fors-list.txt`, minus the reg-100345 entry).
- **Prototype 1, 79 flags:** the kind byte at reg 10, and 78 `assertZero (piField 0 …)`, the same
  list as SRA's.
- **No other `skip` reaches an assertion.** In both prototypes the only untracked results of non-byte
  ops are:
  - one `const` (the kind byte, compared with `piField 0 48 1`);
  - the per-kind registers (p0: 11 `packFK`, 5 `keep`; p1: 4 `packFK`, 10 `keep`).
- The only consumer of an untracked non-byte register without a per-kind slot is `const → assertEq`
  (the kind byte).
- **Unequal-type `keep`s:** exactly five per prototype (p0 op#101817–101821, p1 op#101770–101774). All
  have per-kind slots. Their `getK`s are now tracked by `extGetK`, and their `tensorW`s by `.tensorWK`.

The foreign-flag list is now exactly SRA §4.1's two classes: the kind byte, and the zero pins on proof
bytes.

## 4. Regenerated artifacts, fit

| Artifact | Result (`logs/CK/`) |
|---|---|
| compile delta (`ckdelta.log`, `ckmoved.log`) | p0 skeleton rows 189,352 → 196,072 (+6,720), cells 276,634 → 283,546 (+6,912), **4,392 registers newly tracked**; template keys and instance counts equal, 0 instance inputs differ, 0 aux differ, imports 38,776 (same registers); p1 rows +64, cells +256, 50 newly tracked |
| hint (`laydump4.log`, `laydump4-2.log`; `FRNodeRows4Hint.before.lean`) | `hintLay0`: every group's row base +6,144 … +6,656 (cells unchanged: top-down); `hintLay1` unchanged; identical at `74a2528` |
| `plan4t init` (`plan4t-init2.log`) | `inR true` |
| `cellfit2.log` | 0 overlaps (both); p0 free below the lowest instance 130,470, free in all 243,349 |
| `arenafit2.log` | p0 skeleton cells end 283,546 ≤ arA1 290,816 (7,270 spare); last row 706,303 < arR2 720,896 (14,592 spare); 0 instances or row entries on arena cells; p1 unchanged |
| node dump (`nodedump/`, `nodedump4-run.log`) | p0 656,486 indexed rows, last index 706,303, cells 4…283,546, 14 foreign; p1 686,080 rows, 79 foreign |
| `plan4t check` (`plan4t-check2.log`) | `evalMT4` = sparse sum over `nodeIRowsP`: **N2 equal true** (174 s), **N4 equal true** (303 s), **N8 equal true** (848 s; 22 min wall for the run) |
| MxKat (`mxkat3.log`, ASK-P's updated reference with `arV4`) | 33 `= face798's true`, 0 false. With the pre-ASK-P reference (`mxkat2.log`) every non-empty support differs: that probe is stale since `74a2528`, not because of CK. At `27459d9` with the old reference: 34/34 true (`mxkat.log`) |

**N8's check**: the full sparse sum, run under a 3,600 s cap (ASK-P's 1,800 s cap cut it); it finished
in 848 s, `equal true`. MxKat compares N8 too, at random points.

**Row model** (`FRNodeRows4Model`, unowned, edited as a measured literal):
- `protoRowsN` 700,160 → **706,304**; node region 945,568 → 951,712 (≤ `2^20`).
- `mRowModel4_eq`: N2 3,533,688 (was 3,527,544), N4 5,494,664 (was 5,488,520), **N8 7,843,904
  unchanged**. N8 has no previous-node slot, and the segment prototype's region is unchanged, so N8
  stays 1.0185× under `N_M / 1.05`.
- `mRows4_le` (statement unchanged) re-checks.

## 5. V and plan init (cap fit only)

`logs/CK/vtime-ab.log`/`.summary` (`abv.sh`, 4 alternating rounds × 21 runs, core 27, load ≈ 5;
HEAD = ASK-P's `askp-bin` at `74a2528`, CK = `ck-bin`). Best, ms (median of medians):

| | HEAD | **CK** |
|---|---|---|
| V(N4), own kind | 275.8 (314.6) | **297.2** (329.9) |
| V(N4), all three kinds | 322.1 (346.3) | **343.8** (376.3) |
| `evalMT4` N4 | 157.9 | 179.6 |

- The new ≈ 6.7 k rows of prototype 0 are sparse skeleton rows: about +20 ms, far inside
  `verify_s` 10 s.
- **Plan init** (`plan4t-init-ab.log`, `abinit.sh`, 4 alternating rounds, core 27):
  - HEAD 6.57 / 6.88 / 7.24 / 7.44 s wall;
  - CK 6.99 / 7.11 / 7.17 / 9.27 s wall (one outlier);
  - user time 6.2–6.8 s (HEAD) vs 6.7–7.5 s (CK);
  - inside `ready_s` 10 s.
- Today's base is ASK-P's ≈ 7 s, not 5.5 s: ASK-P's own A/B against IMP was 5.4 → 7.3 s.

## 6. Kernel time, code lines

Sequential profiles: one core, `Elab.async=false` (`logs/CK/profile-<m>.log`):

| Module | type checking | tactics | CPU-s (user) | code lines |
|---|---|---|---|---|
| `FRVIRCompileK` (new) | 0.09 s | 0.22 s | 5.8 | 79 (4 thm) |
| `FRVIRTplSet` | 0.87 s (HEAD 0.74) | 2.19 s (2.09) | 15.9 (HEAD 14.9) | 513 → 515 |
| `FRNodeRows4Hint` | 0.001 s | — | 3.8 | 37 → 37 |
| `FRNodeRows4Model` | 0.02 s | 0.03 s | 4.3 | 34 → 34 |

There is no `decide` over a row list or a program. The two controls are `decide +kernel` on a 4-register
state.

## 7. What moved (for other tracks)

- **Unchanged:** both prototypes' op lists, op indices and register numbers (V is untouched); template
  keys, instance counts and instance input forms; auxiliary imports; template cells (`hintLay*`'s cell
  bases); arenas, bits and the reserve cells (`rsvRel` ≤ 116,603, all before the change; `ckmoved.log`:
  `true / true`).
- **Prototype 0:**
  - every register from **93,116** (op#101824, the first `getK`) on has new skeleton cells, shifted by
    +6 there and growing to +6,912 at the end (`next` 276,634 → 283,546). This includes
    **12,577 import registers from reg 99,829 on**;
  - skeleton rows from **116,833** on shift (+6,720 at the end);
  - every template group's row base moves by +6,144 … +6,656 (the new `hintLay0`);
  - the region's last row is 706,303.
- **Prototype 1:**
  - registers from **93,084** on: cells +0 … +256, including 12,577 imports from reg 96,139;
  - skeleton rows from 118,951 on: +64;
  - template rows unchanged.
- **C1b / R3:** their templates are generic in `protoCS` (no literal register or cell at or above
  these points in their files: grepped). R3's `rsWeight` (op#101823, reg 93,115) is before the change.
  Any dumped or KAT'd cell list from before `CK` (e.g. a replay template's operand cells after reg
  93,116) must be re-dumped.
- **ASK-P:**
  - its folds are over `protoCS`/`nodeIRows4`, so they follow, and the build is green;
  - doc-only diff for `FRNodeRows4ArenaPlace`'s module doc and `arR2`'s doc:
    "700,160 / 686,080 in the region" → "706,304 / 686,080", and the "margin of 20.7 k" →
    **14.6 k** rows (720,896 − 706,304).
  - B2″'s "cell margin 13.7 k" is now 7,270 cells below arA1.

## 8. What E1's prover must change

- **Nothing in its code.** `mfill` runs the (unchanged) program and writes the registers'
  single-cell forms; the forward row solve then fills the rest:
  - `getKK`'s rows `sel_κ · x_κ = c_κ` solve `c_κ`;
  - the newly tracked chain's `muxOut` (`g·(y−x) = v − x`) and `mulK`/`mulKF` rows solve their output
    cells.
  - The `getK` register's form `c_L + c_P + c_N` is multi-term. It is only checked, not written.
- **Re-dump and rebuild** at the commit that lands CK: `nodedump4` (as `logs/CK/nodedump/`), with
  `planform4`/`protodump` as in E1 §2, the blob (`nodeblob.b64`), then `node-kat` (expect 0 failing
  rows). Prototype 0's 6,720 extra rows are ordinary M rows, and no new auxiliary cell table is needed.

## 9. Files

- New: `submissions/flock-recursive/lean/FRVIRCompileK.lean`.
- Edited:
  - `FRVIRTplSet.lean` (import, `tplExt4`, one proof line; unowned);
  - `FRNodeRows4Hint.lean` (regenerated);
  - `FRNodeRows4Model.lean` (literal `protoRowsN` and its sums and doc; unowned).
- Not edited (owned, not needed): `FRVIRCompile`, `FRVIRCompileSound`, `FRVIRFinals4`.
- Docs: `stages/CK-RESULT.md`, `stages/CK-JOURNAL.md`.
- **Orchestrator:** `FR.lean` needs no change: `FRVIRCompileK` is imported by `FRVIRTplSet`.
- Build tree only (dev): probes `logs/fr-build-CK/probe/CKSkips.lean`, `CKDelta.lean` and
  `CKMoved.lean`; `MxKat.lean` copied from ASK-P's tree; `ax/AxCK.lean`; `logs/CK/abv.sh` and
  `abinit.sh`.
