# B2″ (track L-circ): RESULT — cell packing, the arenas placed, the row model

Stage B2″ of `submissions/flock-recursive`, 2026-10-29, worktree `recursion.fast-submissions-rev44`
(`v4/rev44`). Started at HEAD `4832220`, re-snapshotted on **`213c407`** (RSV-V) for the hint, the
measurements and the final build. Build tree `logs/fr-build-B2pp` (copy of `fr-build-B2p`; my modules
symlinked; `override/FR.lean` = HEAD's + one import; `scan/` = RSV-V's sorried copies of HEAD's 7 red
declarations, probes and the scan build only). Logs `logs/B2pp/`; journal `B2pp-JOURNAL.md`. Every
lean/lake/probe ran in a 16 GB scope with a timeout. No sub-agents, nothing committed.

## Summary

| Item | State |
|---|---|
| 1. (c3) | done: `cellsOf` counts a chunk-evaluated key's used cells (`rowW 8`: +15.9 k free) |
| 2. (b′) | done, **no statement changed** (mechanism differs from B2′'s sketch, §1.1). Packed: `phiRS 7` and two/three `tensorWK` keys, 3 per window. Free cells below the templates **136,914 (p0) / 164,050 (p1)**, from 7,945 / 56,905 |
| 3. hint, measurements | hint regenerated at `213c407` (worktree `FRNodeRows4Hint`); `inR true`; `evalMT4` = sparse (N2/N4/N8); A/B §2; `plan4t init` 5.2 s min / 5.5 med (target 5 s: **not quite met**, HEAD itself 5.3) |
| 4. (a) | done: the binding writes the consumers' import cells (`ALv.off`, `aCell`); arena₁, the binding's rows and the bits placed (`FRNodeRows4ArenaPlace`); `a1_cells4`, `arena_elem4`, `bit_cells4`; closed forms `a1V4_eq`, `a2V4_eq`, `bitV4_eq`, checked at full size at run time |
| 5. model | re-based: N8 7,843,840, **1.0185×** under `N_M/1.05` |
| build | `lake build FR Solution FRNodeSound4Ctrl FRSoundness4XCtrl FRSubmission4Cert FRNodeRows4ArenaPlace FRNodeRows4Model`: green with the 7 HEAD declarations sorried (`build-scan-2.log`, 2,592 jobs, exactly 7 `sorry` warnings); without them the only errors are HEAD's (`build-head.log`). **No new break.** |
| KATs | plan-form `KAT PASS` (`planform-kat.log`); cap-check `PASS` (`capkat.log`) |
| axioms / source rule | 47 of mine ⊆ {propext, Classical.choice, Quot.sound}; `certified` shows `sorryAx` only through HEAD's 7 (`axioms.log`). Source rule: 378 files, 0 findings |

## 1. Items 1–2: the cells

### 1.1 The mechanism (deviation from B2′'s R2.4 sketch)

B2′ proposed one piece per group of `g` instances, cut like a skeleton block. That cannot keep
`tinRP_rows` and `slotRP_rows`, which are list equalities over `cs.tins`: a group's instances are not
consecutive there. So in B2″ **every instance stays one proto-piece, with its rows unchanged**. The
piece is laid over its window's base and bits, and it carries its **member's template**: the locals
moved by `j·s`, where `j` is the instance's place in the window. Each member index is therefore a key.
The members are built once per key (`KM.pk`), so `toPiece`'s `withPtrEq` still holds. The rows do not
move, so the packing costs no rows (B2′ estimated +4.6 k / +6.0 k).

- **Layout field.** In `FRVIRTplExt`, a layout entry's cell field `f` is either `b` or `w + 64·g`
  (`cW`, `cG`, `cS`). `TLay.cb := gb + mo`, which equals `c + i·2^b` for an unpacked entry. **The
  `TLay` type and every literal layout keep their meaning.**
- **Policy.** `packOf` (`pkKey`, `usedN`/`cUsed`, `packN`) picks the window. `packMax := 4`: at
  `g ≤ 16`, `kp` rose 27 → 65 ms and `evalMT4` N4 rose ≈ 147 → 201 ms (`plan4t-1.log`). A member key
  costs one template preparation per evaluation, ≈ 2.7 µs per template row. B2′'s group keys would
  have had the same cost.
- **`fitCells` (`FRVIRTplSet`).** Only the hint generator uses `cellsOf` + `fitCells`.
- **Proofs (`FRVIRTplBuild`).** `tinRP` picks `tinRPp` when the layout's field is the key's `PK.f`;
  otherwise it uses `tinRPu`, the old body. **`tinRP_rows` keeps its statement.** It is re-proved from
  `tinRPu_rows` (the old proof) and `tinRPp_rows`, with `shRows_inst`, `mkPK_get`, `pkOf_get`,
  `mkKM_pk`, `TLay.cb_eq` and `pkSel_spec`.
- **Untouched.** `compileTF4_soundAt`, `evalMT4_eq`, `hfit4`, `ProtoFit`, `slotRP_rows` and
  `planData4_rows` are unchanged in text and in proof.

### 1.2 Cells (`cellfit-3.log`, new probe `CellFit`: 0 overlaps of instances' used cells)

| | p0 | p1 |
|---|---|---|
| skeleton cells | 277,102 | 277,102 |
| lowest instance | 414,016 | 441,152 |
| **free below** | **136,914** | **164,050** |
| packed keys | `phiRS 7`, `tensorWK [19,18,19]`, `[16,15,16]` | `phiRS 7`, `tensorWK [19,17,18]`, `[10,8,9]` |

## 2. Item 3: measurements (`ab-1.log`/`.summary`, 4 alternating rounds, core 22)

Binaries: `21ade15`'s (`B2p/b4-bin`); HEAD `213c407` with its own hint (`h213-bin`: my code, unpacked
hint, isolates the packing); B2″ (`pk-bin`). All three report `inR true`.

| | 21ade15 | 213c407 | **B2″** |
|---|---|---|---|
| keys | 176 | 182 | 200 |
| `plan4t init` min / med (s) | 5.9 / 6.0 | 5.3 / 5.3 | **5.2 / 5.5** |
| `kp` min (ms) | 26.2 | 27.3 | 32.2 |
| `evalMT4` N2 min / med | 144.6 / 145.9 | 142.6 / 151.6 | 152.3 / 157.5 |
| `evalMT4` N4 min / med | 147.1 / 151.8 | 146.0 / 159.5 | **155.2 / 162.0** |
| `evalMT4` N8 min / med | 106.5 / 113.6 | 110.9 / 118.5 | 116.7 / 126.8 |

The packing costs ≈ +9 ms of `evalMT4` (+6 %). `kp` takes 5 ms of that: 18 more keys, each a
template preparation. `plan4t check` at `4832220` + packing (`plan4t-check-2.log`): `evalMT4` equals
the sparse sum for N2, N4 and N8.

## 3. Item 4: the arenas placed

### 3.1 The rows (`FRNodeRows4ArenaRows`)

`ALv` gains the import windows `c`, `C`, `off`, and `aCell A₂ v p q = A₂ + C + p·2^c + off q`.
`a2Rows` row `R₂ + B + p·2^a + q` now copies arena₁'s `A₁ + E + S·p + q` into the import cell. There
are new bit rows `bitRow`/`bitRows` (`x·x = x`).

### 3.2 Placement (`FRNodeRows4ArenaPlace`, M-relative to a slot's region; both prototypes)

| | cells | rows |
|---|---|---|
| arena₁, `arN = 4·chainLenOf seq4` = 96,936 | `[290,816, 387,752)` | `[852,992, 949,928)` |
| the binding (import cells: B4's) | — | `[720,896, 852,992)` (`arR2N` = 132,096 index space) |
| bits, 8,320 | `[389,120, 397,440)` | `[950,272, 958,592)` |

- **Margins.** 13.7 k cells above the skeleton and 16.6 k below the lowest instance. 20.7 k rows
  above the prototypes and 57 k below the link region, for the other ≈ 12.6 k pack rows.
- **Static check.** `arena_rows` and `arena_cells` are kernel-checked.
- **Gap check.** The gap against the compiled prototypes is checked on the dump (`arenafit.log`, new
  probe `ArenaFit`): skeleton ≤ `arA1`, bits ≤ lowest instance, 0 instances or row entries on arena
  cells, last prototype row < `arR2`.
- **Format.** `arN` comes from the format (orchestrator), so a format change only moves `arN_eq`'s
  literal.

### 3.3 Run-time check (`arenatime-1.log`, N4 slot 1, full size)

`a1V4`, `a2V4` and `bitV4` each equal their sparse sum. The `a2V4` check runs 5 levels, 871
positions, `off q = 2q+1`. Times: arena₁ 0.17 ms, the binding 25.0–25.9 ms, bits 0.33 ms per slot.
These use absolute coordinates and `gN` high parts.

## 4. Item 5: the row model (`FRNodeRows4Model`)

- **Inputs.** `protoRowsN` 700,160 and `protoRowsS` 686,080 (`nodedump4-run.log`).
- **Pack map.** `packMapN` 212,632: arena₁ 96,936 plus the binding's 85,946 used rows.
  `packMapN_arN` ties it to `arN`.
- **Regions.** Node 945,560, segment 980,480, spare 621,000.
- **Totals.** N2 3,527,520, N4 5,488,480, **N8 7,843,840: 1.0185× under 7,989,150**. That leaves
  18,164 rows of slack per segment region.

## 5. Files, code lines (`loc.py`, `loc.txt`), CPU-s (sequential, one core, user; `cpu.log`)

| Module | code HEAD → now | thm | CPU-s now (HEAD) |
|---|---|---|---|
| `FRVIRTplExt` | 459 → 498 | 23 | 9.2–9.3 (8.5) |
| `FRVIRTplSet` | 507 → 513 | 35 | 13.9–14.3 |
| `FRVIRTplPlan` | 291 → 295 | 2 | 5.4–6.0 |
| `FRVIRTplBuild` | 1,150 → 1,264 | 92 | 15.8–23.1 (load spike in round 1) |
| `FRNodeRows4ArenaRows` | 160 → 233 | 23 | 6.8–6.9 (5.8–6.3) |
| `FRNodeRows4ArenaPlace` (new) | 66 | 10 | 6.2 (one kernel evaluation of `chainLenOf seq4` in `arN_eq`, ≈ 2.4 s) |
| `FRNodeRows4Model` | 32 → 34 | 5 | 3.5 (3.6) |
| `FRNodeRows4Hint` | 37 → 37 | 0 | 3.5–4.2 |
| `FR.lean` | +1 import (`FRNodeRows4ArenaPlace`) | | |

**Kernel trap.** A proof that compares a format-derived size inside arithmetic makes the kernel
evaluate `chainLenOf seq4`, about 2.4 s each time; `simp`'s congruence proofs do that. Use
`rw [arN_eq]`.

**Dev probes** (`fr-build-B2pp/probe/`): `CellFit`, `ArenaFit`, `ArenaTime` (updated).

## For P2

- **What moved.** Only template instances' **cells** move. Packed keys' instances sit at `gb + j·s`;
  the layout's field is `w + 64·g`. Rows, the program and witness values are unchanged.
- **Keys.** The plan form has 200 keys. A packed key's members are separate keys, with local offsets
  moved by `j·s`.
- **New dump.** `logs/B2pp/nodedump/`: `plan-form-p0.bin` 1,190,088 B, `-p1.bin` 1,202,225 B, `mrows`,
  `groups`, …, `planform_kat.py` (649,915 / 641,628 rows rebuilt, 0 differ, **KAT PASS**).
- **Your action.** Re-embed the plan form and every cell-indexed vector, and rerun the start-up KAT.
- **Witness layout.** An honest witness must place each packed instance's locals at its
  `TLay.cb = gb + mo`.
- **Arenas.** The arena cells are not yet in `nodeIRows4` (B4). Once they are, the prover fills
  arena₁ = stream elements, the import cells = their elements, and the bits.

## For B4

- **Interface.** With `w κ.oneCell = 1` and the placed rows holding:
  - `a1_cells4`: arena₁'s cell `e` is `sCell b0 e`;
  - **`arena_elem4`**: `w (oneCell + σ·2^20 + C + p·2^c + off q) = w (sCell b0 (E + S·p + q))`;
  - `bit_cells4`.

  An ask's answer and operand cells are import cells. Pick each import class's `ALv` (`E`, `S`, its
  windows `C`, `c`, offsets `off`, rows `B`, `a` with `LvIn`) from the compile's import registers;
  the theorem then gives "import cell = stream element", which is `ATAsk`/`ATImp`'s representation
  fact.
- **Values.** `a1V4_eq` (k = 17), `a2V4_eq` (alignment: `2^a ∣ σ·2^20 + arR2 + B`,
  `2^c ∣ oneCell + σ·2^20 + C`, `off q < 2^c`, `S ≤ 2^a`), `bitV4_eq` (k = 14).
- **Folding into `nodeIRows4`.**
  - Adding these rows to `nodeIRows4` (and `evalMT4`) changes `evalMT4_eq`'s meaning. That is B4's
    step, not mine.
  - Rows stay below the link region (`arena_rows`) and above both prototypes. Make that a checked
    fact, like `ProtoFit`, with `arenafit`'s checks as the model.
  - The binding is M-to-M inside the slot's region, so `copy_val`'s identity makes it once per node
    at region-local coordinates. Measured per slot at absolute coordinates: 25 ms.
- **Reserve cells.** RSV-V's 52 reserve cells (M-relative ≤ 116,492) lie in the skeleton's cells,
  clear of every arena and template.

## Deviations

1. **(b′) per member key, not per group** (§1.1): rows unchanged, no statement changed, more keys;
   `packMax = 4` bounds the keys' preparation cost.
2. **`a2_cells`/`arena_elem` restated** at `aCell` (B2′'s interface theorems, not the soundness
   chain; the brief asked for "import cell = stream element").
3. `packMapN` stays a literal with `packMapN_arN` (§5: kernel cost); `arN` itself is from the format.

## Open questions

1. **`plan4t init` ≤ 5 s.** B2″ measures 5.2 s min and 5.5 s median; HEAD measures 5.3 s. The rest
   is A2″'s V program construction plus the plan's stages (B2′ §1.4).
2. **The packing's +9 ms of `evalMT4`.**
   - Lever: a member key's `one`/`u` preparation is its base key's; only `loc` depends on the shift.
   - Sharing it (a `Key` that names its base and shift, `kprep3` on the shifted locals only) would
     bring it near 0 and allow `packMax` > 4.
   - Cost: a change in `FRVIRTplRun`/`Fast`'s preparation and `kp_shared`'s proof.
3. **Cell margins are thin by design.** If a later program grows the skeleton by > 13.7 k cells, or
   the prototypes by > 20.7 k rows, move `arA1`/`arR2` (`arenafit` reports it).
4. **Coordination.** RSV-V2 is editing `FRShape4`/`FRNodeKinds4`/`FRX4*` in the worktree. My tree
   took them from HEAD. After its landing, rerun `laydump4` + `mkhint.py`, `arenafit` and
   `cellfit`. `arN` follows the format, so only `arN_eq`'s and the model's literals move.
