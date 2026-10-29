# IMPC journal (track IMPC: the `ATImp` import classes, `SlotRunA`'s aux facts, SRA's requests)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `74a2528`). Build tree `logs/fr-build-IMPC`
(copy of `fr-build-ASKP`, `MINE.txt` = my modules, snapshot onto `74a2528`). Logs `logs/IMPC/`.

## 2026-10-29

- Base build at HEAD (`FRNodeRows4AskInp FRNodeRsvLink FRNodeRows4AskPosR FRNodeRun4Ctrl`): green, 2,518 jobs.
- Read: ASK-P/IMP/SRA/B3 RESULTs, PACK §1.3/§4, `FRNodeRun4` (`ATImp`: generic over `regs` with `InvK`
  at the op), `FRVIR4`/`FRVIRFinals4` generators.
- **Finding (scope): `bitOf` is not `ATImp`-able.** `ATImp` quantifies over every register file with
  `InvK`; `bitOf n h`'s operand `n` is an `idx`/`shrN` register, untracked (slot `none`), so its value is
  unconstrained in the obligation. `bitOf` (15.3 k per prototype) must stay a residual import of
  `SlotRunA` (on the concrete run) and needs register provenance. The siblings' value, by contrast, is a
  function of the trace (`sib4` reads the trace's P2 answers), so it is `ATImp`-able with bit cells.
- (β′) removed every `piDigestAt` (prototypes: 0). The cap check's reads are static `piElemK`/`piElem`
  (`A`, caps) and `piDigest` (`D`): proof fields.
- New `FRNodeRows4AskI` (low, below `FRNodeRows4`): tables `itOffA`, `itemsA`, `phasesA`, `phIxA`,
  `pSegs`; `phItem`, `pfLoc`, `winE`; rows `a1Row`, `pfRows`, `chRows`; `impcRows`, `impcCov`, **`impcTG`**.
- Probe `probe/ImpcStat.lean` (`logs/IMPC/impcstat.log`): per prototype, covered: `piElem` 4,199/4,201,
  `piElemK` 1,891/1,891, `piDigest` 872/8,300 (the rest: 7,4xx siblings + the statement's unaligned reads),
  `chF` 291/291, `chK` 31/31; **10,078 / 10,015 rows, 0 `failR`**. Uncovered non-siblings: the
  statement's `h`/`n` reads at π bytes 49, 65 (`piElem`), 49, 81 (`piDigest`) — stmt byte 1 and 33,
  not element-aligned.
- `FRNodeRows4AskIS` (soundness): tables ↔ `itOff`/`itAt`/`phIx`, `pfLoc_spec` (per shape via
  `reassemble4_byte` + `ctb4_*`), `winE_spec`, `win_slot`, `PfCells`, `pfCells_of_rows`, `atImp_impc`,
  `withImpc`, `gap4Imp_of_impc`. Green.
- V probe (`probe/ImpcV.lean`, `logs/IMPC/impcv.log`): classes-only rows (10.1 k/proto) ≈ 14 ms per
  prototype in `askV`; with `felems` (≈ 27.9 k more) ≈ 65 ms per prototype → split into `colTG`.
- Provenance design: register → `piField` (`provL`, passed to the generator as `pv`); zero pins at the
  `assertZero` op (gated `gate act · A₁(e) = 0`); column words at the `dotKF` op (from its `aux`); a
  failing row where the compile made those ops imports (keeps `ATImp` vacuous there).
- Probe: p0 fors 15 (pre-CK): 12 zero-pinnable; residual cap equation (CK), stmt tail (π 113, 63 B,
  unaligned), tag byte (π 48). p1 79: 77 pinnable; residual stmt tail (π 89, 87 B), tag byte. felems aux
  871/871 bound; `bits 20` aux 1,627 not bound.
- `FRNodeRows4AskIR`: `evalOp_len`, `execA_prov`, `trail_fors`, `trail_aux`, `flag_zpin`, `aux_col`,
  `xof_felems` (felems only at `dotKF`; covers CK's `extGetK`), `zPin`, `colOk`, `SlotRunI`,
  `slotRunA_of_impc`, `withImpcC`, **`gap4Imp_of_impcR`**. Green.
- CK landed (`44a4975`): re-snapshotted; my modules green on it.
- Final: full build `FR Solution FRSubmission4Fin FRNodeRows4AskIR` at `44a4975` + mine green (2,667
  jobs, 0 sorry); axioms 23 decls ok; source rule 447 files 0 findings; kernel 0.04/0.39/0.76 s.
- Post-CK probes: p0 fors 14 (12 pinned; open stmt tail π113/63 B, tag byte π48), p1 79 (77; π89/87 B,
  tag). V: impcTG 16–18 ms/proto, +colTG 54–57 ms/proto; plan init +0.1–0.3 s/proto (+0.8 more with col).
- RESULT written (`IMPC-RESULT.md`).
