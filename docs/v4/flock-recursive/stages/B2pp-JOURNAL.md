# B2″ (track L-circ): JOURNAL

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `4832220`. Build tree
`logs/fr-build-B2pp` (copy of `fr-build-B2p`; `MINE.txt` = my modules, symlinked; `override/` = the
hint at HEAD, since RSV-V's worktree copy is at its own program). Logs `logs/B2pp/`. Every lean/lake/probe
in a 16 GB scope with a timeout. No sub-agents, nothing committed.

Brief: B2′'s §R2.4 in order: (c3), (b′), hint + measurements, (a), model.

## Coordination with RSV-V (same worktree)

- 12:40: the worktree's `FRNodeRows4Hint` is RSV-V's (`git diff`), and its `FR.lean` lacks HEAD's
  `import FRNodeRows4ArenaRows` (a stale working copy). My tree takes the hint from `override/`
  (= HEAD's, mine) and `FR.lean` from HEAD. I do not touch RSV-V's working copies.

## Item 1–2: (c3) and (b′) (on HEAD `4832220`)

- **(c3)** `FRVIRTplSet.cellsOf`/`fitCells`: a key with `12 < tRbits` takes `(n − 1)·2^b + cUsed`.
- **(b′) mechanism (deviation from B2′'s R2.4 sketch).** B2′ proposed one piece per *group* of `g`
  instances (rows contiguous, cut like a skeleton block). That cannot keep `tinRP_rows`/`slotRP_rows`
  as list equalities: a group's instances are not consecutive in `cs.tins`. Instead every instance
  stays one proto-piece, with **rows unchanged** (no row cost), over its window's base and bits, with
  its **member's template** (`shRows (j·s)`: locals moved by the member offset): one key per member
  index `j < g`. The members are built once per key in `KM.pk` (`mkPK`, so `withPtrEq` holds).
  - `FRVIRTplExt`: `cW`/`cG`/`cS` (a layout entry's cell field `f` is `b`, or `w + 64·g` if packed:
    the `TLay` type and every literal layout keep their meaning), `TLay.gb`/`TLay.mo`,
    `TLay.cb := gb + mo` (= `c + i·2^b` unpacked), `auxEnd`, `usedN`, `cUsed`, `pkKey`, `packN`,
    `packOf`; controls `TLay.cb_ctl`, `packN_ctl`.
  - `FRVIRTplPlan`: `TLay.bits` = `cW f`; `TLay.cf`.
  - `FRVIRTplBuild`: `shW`, `shRows`, `PK`, `mkPK`, `pkOf`, `KM.pk`, `pkSel`, `tinRPp`; the old
    `tinRP` is `tinRPu`; `tinRP` picks `tinRPp` iff the layout's field is the key's `PK.f`.
    `tinRP_rows` **statement unchanged**, re-proved via `tinRPu_rows` (the old proof) and
    `tinRPp_rows` (`shRows_inst`, `mkPK_get`, `pkOf_get`, `mkKM_pk`, `TLay.cb_eq`, `pkSel_spec`).
  - First run, `g ≤ 16` (`plan4t-1.log`): keys 176 → 390, pieces unchanged, `inR true`, but `kp`
    27–34 → 65 ms and `evalMT4` N4 ≈ 147.7 → 201 ms. A key's preparation is ≈ 2.7 µs a template
    row per evaluation, and `g` members cost `g` preparations. B2′'s group pieces would have had the
    same preparation cost (a group key has `g·nr` rows).
  - **`packMax := 4`** (`plan4t-2.log`): packed `phiRS 7` (3 per `2^9`), `tensorWK` 306/261 (p0),
    296/161 (p1) (3 per `2^10`/`2^9`). Keys 194, `kp` 32–34 ms, `evalMT4` N2/N4/N8 best
    154.5/155.2/121.3 (same core, not yet alternating). `cellfit-2.log` (new probe `CellFit`):
    0 overlaps, free below the lowest instance **137,481 (p0) / 164,105 (p1)** (need 105,200).
- 13:xx: orchestrator: RSV-V committed `213c407` (HEAD red at 7 `FRSoundness4*`, RSV-S's). Its 52
  reserve cells (`rsvRel`, M-relative 6 … 116,492) lie inside the skeleton's cells (< 276,535): clear
  of every template and of the arenas' gap. Re-snapshot on HEAD; the hint regenerated last.

## Item 3: hint and measurements (re-snapshot on HEAD `213c407`)

- HEAD `213c407` is red at `FRSoundness4Qry` (`noAsk_gFinE`/`_gFinB'`/`_gFinPf`), which
  `FRNodeRows4Plan` imports: my build tree takes RSV-V's sorried copy from `fr-build-RSV`
  (`fr-build-B2pp/scan/`, copied into `override/`) **for the probes only**.
- `laydump4-3.log` → hint (`override/FRNodeRows4Hint.lean`, = the worktree's at the end).
  Packed: p0 `phiRS 7` (201 = 9 + 64·3), `tensorWK [19,18,19]`, `[16,15,16]` (202); p1 `phiRS 7`,
  `tensorWK [19,17,18]` (202), `[10,8,9]` (201).
- `cellfit-3.log`: 0 overlaps; skeleton cells 277,102 (both); free below the lowest instance
  **136,914 (p0) / 164,050 (p1)**.
- `plan4t-3.log`: keys 200 (HEAD's hint: 182), pieces 10,049 + 10,292, `inR true`.
- `plan4t-check-2.log` (at `4832220` + packing): `evalMT4` = the sparse sum for N2, N4, N8.
- **A/B** (`ab-1.log`, `ab-1.summary`; 4 rounds alternating, core 22): `21ade15`'s binary
  (`B2p/b4-bin`), HEAD `213c407` with its own hint (`h213-bin`: my code, unpacked hint), and B2″
  (`pk-bin`):

  | | 21ade15 | 213c407 | B2″ |
  |---|---|---|---|
  | init min / med (s) | 5.9 / 6.0 | 5.3 / 5.3 | 5.2 / 5.5 |
  | kp min | 26.2 | 27.3 | 32.2 |
  | N2 min / med | 144.6 / 145.9 | 142.6 / 151.6 | 152.3 / 157.5 |
  | N4 min / med | 147.1 / 151.8 | 146.0 / 159.5 | 155.2 / 162.0 |
  | N8 min / med | 106.5 / 113.6 | 110.9 / 118.5 | 116.7 / 126.8 |

  Packing costs ≈ +9 ms of `evalMT4` (N4 min), +5 of it in `kp` (18 member keys). `nodedump4-run.log`
  (pk-bin): prototype rows 700,160 / 686,080.

## Item 4: (a), the placement (`FRNodeRows4ArenaRows`, new `FRNodeRows4ArenaPlace`)

- `ALv` gains the import windows (`c`, `C`, `off`); `aCell`; `a2Rows` writes the import cell;
  `a2_cells`/`arena_elem` restated at `aCell` (B2′'s interface theorems, not the chain); `bitRow`,
  `bitRows`, `bit_cells`; `a2M`/`a2M_eq` (the import side per level: one diagonal run × the window's
  `S` products), `a2V`/`a2V_eq` (one state per position on arena₁'s side), `bitV`/`bitV_eq`.
  Controls `bitRow_ctl` (F has characteristic 2: `2·2 = 2`, so the negative uses `F.y`), `aCell_ctl`.
- Placement (`arenafit.log`, new probe `ArenaFit`): cells arena₁ `[290,816, 387,752)`, bits
  `[389,120, 397,440)` (skeleton ends 277,102; lowest instance 414,016 / 441,152); rows binding
  `[720,896, 852,992)`, arena₁ `[852,992, 949,928)`, bits `[950,272, 958,592)` (prototype rows end
  700,160 / 686,080; link region from 1,015,808). 0 instances or row entries on arena cells.
- `arenatime-1.log` (probe `ArenaTime` at the placed addresses, N4 slot 1, 23/25 coordinates): `a1V4`,
  `a2V4` (5 levels, 871 positions, `off q = 2q + 1`), `bitV4` = their sparse sums; a1 0.17 ms, the
  binding 25.0–25.9 ms (gN high parts, absolute coordinates), bits 0.33 ms per slot.
- Orchestrator (RSV-V2 changes the format): arena sizes from the format. `arN := 4·chainLenOf seq4`
  with `arN_eq` (one kernel evaluation of `chainLenOf seq4`, ≈ 2.4 s); proofs use `rw [arN_eq]`, not
  `simp` (a `simp` congruence proof made the kernel re-evaluate it per theorem: ArenaPlace 10.9 →
  6.2 CPU-s). `FR.lean` dropped from `MINE` (an `override/FR.lean` = HEAD + my import) so RSV-V2's
  worktree edits never enter my tree.

## Item 5: model

- `protoRowsN` 700,160; `packMapN` 212,632 (a literal; `packMapN_arN : packMapN = arN + 115696`
  ties it to the format, the model's own theorems never touch `arN`: 3.5 CPU-s). N8 7,843,840,
  1.0185× under `N_M/1.05`.

## Final checks

- `build-scan-2.log`: `lake build FR Solution FRNodeSound4Ctrl FRSoundness4XCtrl FRSubmission4Cert
  FRNodeRows4ArenaPlace FRNodeRows4Model` green (2,592 jobs) with RSV-V's sorried copies of HEAD's 7
  red declarations; exactly those 7 `sorry` warnings. Without them (`build-head.log`) the only errors
  are HEAD's (`FRSoundness4R4Fin` 205/247, `FRSoundness4Qry` 143/146/156): no new break.
- `axioms.log` (48): mine ⊆ {propext, Classical.choice, Quot.sound}; `certified` has `sorryAx` from
  the 7 (scan tree only). `source-rule.log`: 378 files, 0 findings. `planform-kat.log`: KAT PASS.
  `capkat.log`: PASS.
