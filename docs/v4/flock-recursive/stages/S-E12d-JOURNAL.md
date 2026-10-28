# S-E12d (track L-circ): journal

Stage S-E12d, 2026-10-28. Base HEAD `67e5c76` (blueprint 4.3). Build tree `logs/fr-build-SE12d`
(a copy of `fr-build-SE12c` with its probes), against `logs/org20`. Logs in `logs/S-E12d/`.

- Baseline: `lake build FR FRNodeRows4Fit FRNodeRows4Model` green at HEAD, 2,497 jobs (6 min 43 s wall,
  most of it re-building HEAD's changes since S-E12c's tree).
- S-CN4's `FRNodeTarget4`, `FRNodeTarget4W`, `FRVerifierImplNode4` are untracked in the worktree
  (in progress); not at HEAD, so not in this tree.
- Design (item 1): a new module `FRVIRTplSet` (the filter `TFilt`, `tplExtF`, `KeyImpl`, `ImplTF`,
  `tplExtF_ok` via `fixT`, `compileTF_sound`, `keys41`). 3.x's `tplExt`/`ImplT`/`compileT`/
  `compileT_sound` are left unchanged (so 3.x is literally today's); `tplExtF allK = tplExt`.
  The plan's compile (`compMS`) is generalised over the extension family `X : TCtx → Ext`, with
  3.x's `compMS := compMSX tplExt` (rfl).
- `FRVIRTplSet` built. Final: 136 code lines, 12 theorems (with the negative control `implTF_all_shiftMask`). Two traps: `rfl` on `(fixT impl).eqZ = Impl.eqZI` (and `rowW`) hits max
  recursion (the elaborator unfolds the closed `lagW xT 64 denS`); `constructor <;> intros <;>
  simp only [fixT]` works (as `implCWith_implT`). `evalOp_fixT` with `rfl` tried first on every op
  timed out at `whnf`; routing through `simp only [tplExt] at hX` first fixes it.
- `compMS` → `compMSX X` (3.x `compMS := compMSX tplExt`, `compMS_rfl`); `compMSX_T`;
  `protoF π := keys41`, `protoCS` at `compileTF`; `planData4` at `compMSX (tplExtF (protoF π))`;
  `planData4_rows` needed `compileTF` in its `rw` list (statement unchanged).
- Full build on `67e5c76` + these: green, 2,498 jobs (`logs/S-E12d/build-67e5c76.log`).
- S-CN4 committed (`c2c6fba`): re-snapped; build green (4,818 jobs with the probes).
- Item 3: `LayDump4` at `layOfF (protoF π)`: the `.shiftMask 18 18` / `.shiftMask 36 18` groups
  are gone; `FRNodeRows4Hint` rewritten. Plan: process start 1.86 / 1.81 / 1.82 s, `inR true`;
  `evalMT4` N2 82.4, N4 80.1, N8 54.7 ms best, equal to the sparse sum for all three
  (`plan4t-check.log`). Dump regenerated (`logs/S-E12d/nodedump/`, 25 s; 3,031 instances,
  indexed rows 485,231 / 484,527, i.e. −2,071 = 3.x's `shiftMask` template).
- INT-8 not committed (HEAD `29d0016` is R4d): the prototypes stay S-E12b's `gen4G`; seam left.
- R4d committed (`29d0016`): re-snapped. Final build `FR FRNodeRows4Fit FRNodeRows4Model FRVIRTplSet`
  green, 2,504 jobs (`logs/S-E12d/build-final.log`). Axioms: 25 declarations, all within
  `propext`/`Classical.choice`/`Quot.sound`; the four rfl checks of `ax/AxE12d.lean` pass. Source
  rule: 284 files, 0 findings.
- Item 4 (S-E8's per-op method, `vtime4 prof`): `rsWeight` 40.5 ms at N4 against 8.75 ms at 3.x's
  N30. Its operands at N4: `|r| = 7`, four claims of 25 coordinates, `|ρ| = 25`, all F points. The
  fast path `wEvalKF` is gated on 23 coordinates (`rsWeightF`), so claim 2 falls back to
  `wEvalKC`. `evalM` +8.6 ms. Everything else within ±2 ms.
- V(N4) (`vtime4`, 21 reps, core 29, load ≈ 2–2.5): best 205.4 / 204.7, median 214.7 / 210.8
  (3.x stand-ins); with S-CN4's `shiftMask4I`/`linkWAll4I` (`cn4`): best 205.6 / 208.8, median
  210.9 / 218.4. 3.x N30 on the same core: best 178.5, median 191.6.
- INT-8's edits to `FRVIR4`/`FRVIRFinals4`/`FRVerifierC4` are in the worktree, uncommitted; my
  tree builds HEAD's versions.
- Item 2 not started in code: the segment template needs a new `TKey` (full rebuild), the node's
  needs a kind mux and `ExtOk` at one kind. Design in the RESULT's handover.
