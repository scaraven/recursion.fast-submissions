# C1 (track L-circ): JOURNAL — the previous-node slot's replay `R` (PACK-4.4 §6.2, stage table C1)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `7bbbf49`). Build tree
`logs/fr-build-C1` (a copy of `fr-build-RSVS2b`: HEAD snapshot, RSV-S2b's build-tree-only sorries via
`patchdec.py`/`autosorry.txt`; `mymods.txt` = this track's modules). Logs: `logs/C1/`.

## 0. Findings before writing code (2026-10-29)

- Prototype 0's program (`logs/E1/nodedump/proto-p0.txt`) has **one** op of each kind:
  `targetS r45` (line 184; operand `AF20`, a plain slot), `shiftTarget r57057 r57058 r57056 r834`
  (65,628), `linkWAll r57080 r57081` (65,650; both operands **per-kind slots**, `AF28`/`AF27`/`AF28`),
  `evalL r57122 r57149` (65,729; per-kind `AF17`…/`AF25`…), `evalM` (65,868; RSV2's), `rsWeight r93114
  {per-kind claim lists} r2262 r790 act r93113` (101,824; `ρ` per-kind `AK`).
- **`shiftTarget` at prototype 0 is `0`.** Its `bnd` operand `r57056` is the constant
  `packFK [0,0,0,0,1,…]` at every kind (`mregs-p0.txt`: forms `1:0 2:0 3:0`, coefficient 0 on the
  selector cells), so both `digestMle` terms vanish: `shiftTargetI κs τ θ bnd = eq(τ,last)·0 + κs·0`.
  The replay is one row `one · out = 0` behind a compile-time check that `bnd`'s first four forms
  have only zero coefficients at every kind (S-E14 priced it at ≈ 2.2 k rows).
- The ops' values at prototype 0, index `ι`: `implP impl₀ base 0 ι = (implN4F base (nodeAt ι)).fixK .N30`:
  `linkWAll` = `linkWAll4I (nodeAt ι)`, `targetS` = `targetSNode4I (nodeAt ι)`, `evalL` =
  `evalL4I (nodeAt ι)`, `rsWeight` = `rsWeightF4 (nodeAt ι)` (all concrete); `shiftTarget` =
  `(base ν).shiftTarget` (abstract: a hypothesis `(base ν).shiftTarget = shiftTargetI`, `rfl` at the
  certificate's `base = fun _ => implC …`).
- **Mechanism chosen**: one kind-muxed template per op (`FRVIRTplKMux.kmuxT`: per selector index the
  kind's sub-template on its own operand block, outputs `Σ_j sel_j · out_j`), instantiated by the
  replay `RT` on cells of the spare region, plus one copy row per output component tying the
  import's cells to the template's outputs. Soundness: `kmuxT_ok` + the per-kind template's
  correctness (a pure-function identity, gate for gate, as S-E3/S-E12e's templates).

## 1. Log
- 17:20 build tree `fr-build-C1` (copy of `fr-build-RSVS2b`); `lake build FRNodeRows4RepCtrl FRNodeRun4S
  FRVerifierImplNode4F …` green (2,365 jobs, `logs/C1/build0.log`).
- `FRNodeRows4RepK` (new): `RT.orElse`, the kind-muxed op replay `KOp`/`kRows`/`rtK`, `KOk`,
  **`rtK_ok`** (`KOk` ⇒ `RTOk`, generic: `kmuxT_ok` + copy rows), prototype 0's `shiftTarget`
  (`rtST0`, **`rtST0_ok`** under `STBase base`). Green. Trap: passing the gate hypothesis `h`
  directly to `kmuxT_ok` times out at `whnf` (elaboration order); `(by exact h)` is instant.
- `FRVIRTplRepLW` (new): `tplLW ν a b` (gate for gate `linkWAll4I ν`), `tabsG`, `famG`/**`famG_ev`**,
  `lwE_ev`, `lwFams_ev`, **`tplLW_ok`**.
- `FRVIRTplRepLW` green. Traps: (1) `Eqns.append` leaves `0 + nlocs …` offsets; matching them against
  the named offsets (`lwK8` …) by defeq unfolds `nlocs` of the tables (`whnf` timeout): `zero_add` in
  the `simp` set and typed `have`s (`mulsG_eqns (k := lwK9 …)`). (2) `split_ifs` splits the spec's
  `if σ = 0` too: the spec is restated over σ-indexed arrays (`linkWOneF_congr`, `linkWAll4I_eq'`).
  (3) `first | exact if_pos rfl | …` on the wrong branch unfolds `Array.ofFn 498` (recursion depth):
  `simp only [↓reduceIte, one_ne_zero]`.
- **Two assignments.** Prototype 0's region is full (PACK §6.1), so the replay's locals must be in the
  spare region, but S-E14's `compileFromX_soundR` evaluates the replay rows at the slot's own
  assignment (`slotAsg`), whose cells beyond the frame are slot 1's. `RTOkW` (rows at `w'`, `Agree B w
  w'`, `SelOk w' P`), each template checking at compile time that the forms it reads are below
  `B = repB = 2^40` (`linLt`); `FRNodeRows4RepW`: `compileFromX_soundRW` (S-E14's induction, rows at
  `w'`), `repMapC`/`repAsg` (frame cells as `slotAsg`, locals to the spare region from cell
  `κ.vslots·2^20`), `slotImp_of_repW`, `repIRowsW` (slot 0's rows from row `κ.vslots·2^20`, a segment
  slot's at S-E14's `v·2^20 + repBase`), `repHoldsW_of`, `gap4Imp_of_repW`, `repOkW_rtC1`. Green.
  B3's `compileFromX_run` (`FRNodeRun4`, PORT's) uses `RTOk` at one assignment: it needs the same
  generalization (RESULT: the diff).
- Controls (`FRNodeRows4RepNCtrl`) green. Probe `probe/RepV.lean` (`logs/C1/repv-1.log`, load 14–17):
  honest-locals KAT of `tplLW` true for N2/N4/N8 (13,848 / 14,360 / 14,360 rows); slot 0's replay
  rows 42,601 (196,410 terms); `growsVal3` 52.4 ms (N2) / 60.2 ms (N4) vs `evalMT4` 147.8 / 173.3 ms;
  `growsVal3 = rows3` KAT true; `repRowsP rtC1 0` along the trail 131–135 s (a second compile: must
  not run at process start).
- Kernel trap: `ev_agree` by induction + `rw [Lin.ev_cons, hA _ h.1, …]` = 28 s of kernel type checking
  (whole module 30.9 s); `List.map_congr_left` under `Lin.ev`: 0.2 s for the module.
- Golf: the per-constructor `simp [...] at hc` (60 `Op` constructors) → `exact absurd hc
  Bool.false_ne_true` (defeq); `simp [evalOp]` → `Res.noConfusion h`: RepK 25.6 → 10.1 s wall.
- Axioms (29 declarations) ⊆ {propext, Classical.choice, Quot.sound}; source rule 420 files, 0 findings.
- Stopped here (context budget): `targetS`, `evalL`, `rsWeight` and the fold/plan integration are in
  RESULT §5–§6.
