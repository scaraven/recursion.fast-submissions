# RSV-S3 RESULT: `finPf`'s reserve chain, `W₀` at 69 cells, the `StmtN4R` route to the certificate

Track RSV-S3, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`; started at
`50a7f52` (RSV-S2a WIP), final build at `154744b` (PORT, B4 landed). Build tree `logs/fr-build-RSVS3` (copy of `fr-build-RSVS2a`, re-snapshotted onto
`50a7f52`); logs `logs/RSVS3/`. Journal `stages/RSV-S3-JOURNAL.md`. No sub-agents, nothing committed.

## 0. Summary

- **Done (kernel-checked, no `sorry` in any of this track's modules):** RSV-S2a §5 items 1–5 and
  RSV-S2b §5 item 5 in its PORT-safe form.
  1. `R4PfFlag.gFinPfR` carries `gFinPf`'s second cell chain (`nrcell` cells, `keep rsv`);
     `gFinPf_reloc` builds again with its old shape (`simp only` + `rfl`).
  2. `w0V4` gains the reserve term where `rsvOps ∧ rsv`.
  3. `flag_gFinPf4`: the second chain is one block (`run_rsvChain`), continued from the first
     chain's accumulator and last power (`run_gCellsOpsK` now also returns the power register).
  4. `R4W0R.w0V4_eq4`, `wV4_of_fields` take `hcl : P.cells ++ P.rcells = cellsC cells κc` (+ `hrc`);
     the two chains are one sum over 69 cells (`cells2_sum`).
  5. `PfFin`, `R4Full`, `XRun` (with the orchestrator's `implN4F_hMS` change), `XFinal` build.
  6. The certificate chain has `StmtN4R` forms (`X4.certificate_rev4R`, `R4.certificate_rev4HR`, …);
     the old `StmtN4` forms keep their statements and are now proved through them, so PORT's and
     B4's files build unchanged. Switching `Gaps4` itself is PORT's file (§5, exact edits).
  7. **`lake build FR Solution` green** at HEAD `154744b` in the build tree (`logs/RSVS3/final.log`,
     2,640 jobs). It needs one edit in PORT's `FRNodeLinks4`, applied in the build tree only and
     requested in §5.2, and one build-tree stub of a red at HEAD that is not this track's
     (`FRXSig4H.xRows_of_stmt`). Axioms of 27 theorems, PORT's `certificate_sub4` included:
     `propext`, `Classical.choice`, `Quot.sound` only (`logs/RSVS3/axioms-154744b.log`). Kernel: §4.
- Also fixed: `R4FrCtrl.relE4_rejects` (red since RSV-S2a's `relE4` branches on `rsvOps`; proof only).
- **Not done:** `gap4Imp_of_rsv` (optional, per the orchestrator's message), left for the next track
  with a plan (§5.4).

## 1. What was built (code lines, the core's `loc.py`, HEAD → now)

| Module | Change | code |
|---|---|---|
| `FRSoundness4R4PfRun` | `gCellsPwK` (the chain's last power register), `gCellsPwK_eq`; `run_gCellsOpsK` also returns that register's value `Pw·κ′ⁿ` | 402 → 414 |
| `FRSoundness4R4PfFlag` | `gFinPfR` with the second chain (`c9`, `acc9`, `cr`, `ce := cond rsvOps (cr+1) c9`); `map_cond`; `gFinPf_reloc` re-proved; `cv4`; `w0V4` with the reserve term; `pr_rebase`; **`run_rsvChain`**; `flag_gFinPf4` B9 → B9′ → B10 | 507 → 587 |
| `FRSoundness4R4W0R` | **`cells2_sum`**; `w0V4_eq4`, `wV4_of_fields` at `hcl : P.cells ++ P.rcells = …`, `hrc` | 233 → 251 |
| `FRSoundness4R4FrCtrl` | `relE4_rejects`: proof cases on `rsvOps` | 44 → 45 |
| `FRSoundness4XRun` | `wV4_of_fields` calls pass `hrc` (`rfl`; node `by cases ν <;> rfl`) | 222 → 223 |
| `FRNodeStmtR4` | `X4.Resid4R`, `resid4R_of`, **`certificate_rev4R`** | 160 → 190 |
| `FRSoundness4XRunG` | imports `FRNodeStmtR4`; `ks_rev4HR`, `Resid4HR`, `resid4HR_of_H`, `resid4R_of_HR`, **`certificate_rev4HR`**; `ks_rev4H`/`certificate_rev4H` proved through them | 105 → 147 |
| `FRNodeSound4K` | `P4f.ks_rev4H`, `Resid4H.gap`, `certificate_rev4H` over `StmtN4R` (via `ks_rev4R`/`certificate_rev4R`) | 75 → 76 |

`FRNodeStmtR4` was a leaf before (nothing imported it, so it was not on `FR`'s build); through
`XRunG` it now is.

## 2. Statement changes, with reasons

| Declaration | Change | Reason |
|---|---|---|
| `R4.gFinPfR` (def) | the second chain + `keep rsv`, `ce := cond rsvOps (cr + 1) c9`, `.keep node (cond rsvOps cr acc9) z0` | must equal `gFinPf` relocated (`gFinPf_reloc`, text unchanged) |
| `R4.w0V4` (def) | cell term `if node then (if rsvOps ∧ rsv then cellsVal4 … rcells nrcell 0 (κ′²·κ′^ncell) cv4 else cv4) else 0`; `cv4` = the old term | RSV2: W₀ batches the reserve's 60 cells at `κ′^{11+i}`. `relPf4`, `wV4` unchanged in text |
| `R4.run_gCellsOpsK` | conclusion gains `(rd … (gCellsPwK nc n pw b)).toF = Pw·κ′ⁿ` | the second chain starts from the first chain's last power; strengthening, only user `flag_gFinPf4` |
| `R4.flag_gFinPf4` | none (text) | — |
| `R4.w0V4_eq4`, `R4.wV4_of_fields` | `hcl : P.cells ++ P.rcells = P4b.cellsC cells κc` (was `P.cells = …`); new `hrc : P.rcells.length = if (P.rsvOps && P.rsv) = true then P.nrcell else 0` | RSV-S2b §5.2. `hrc` is needed because `N8` has `nrcell = 60` but `rcells = []` (gate off): it says the cells the chain reads are exactly the list, and none when the gate is off. Both hold by `rfl` at `segFinP`/`nodeFinP` |
| `P4f.ks_rev4H`, `P4f.Resid4H.gap`, `P4f.certificate_rev4H` (`FRNodeSound4K`) | `hGap`/`gap` over `∀ … ch, StmtN4R … ch → Gap4 …` (was `StmtN4 → Gap4`); `P4f.resid4_of_H` returns `X4.Resid4R` | RSV-S2b §5 item 5; weaker hypothesis. No users outside the module |
| `R4.ks_rev4H`, `R4.certificate_rev4H`, `R4.Resid4H`, the `G`/`GH` forms | none (text); proofs go through the `R` forms | PORT's `FRSubmission4Cert`, `FRNodeLinks4*` and B4's `FRNodeRows4PackSound` use them |
| `R4.relE4_rejects` (control) | none (text) | — |

New: `X4.Resid4R`, `X4.resid4R_of`, `X4.certificate_rev4R`, `R4.Resid4HR`, `R4.resid4HR_of_H`,
`R4.resid4R_of_HR`, `R4.ks_rev4HR`, `R4.certificate_rev4HR`, `R4.cells2_sum`, `R4.run_rsvChain`,
`R4.pr_rebase`, `R4.map_cond`, `R4.cv4`, `R4.gCellsPwK`, `R4.gCellsPwK_eq`.

## 3. Build, axioms, sorries

**Final state (after the orchestrator's message: HEAD `154744b` = PORT `c4eca2b` + G5 docs merge +
B4 `7537acd` + PORT erratum).** The build tree was re-snapshotted onto `154744b`. The old decoder
and B3 stubs are dropped (`FRNodeRun4S.gap4Imp_of_run`/`execA_proto`, `FRXChain4`, `FRXDec4*` are
HEAD's real text; `patchdec-50a7f52.py` keeps the old list). `lake build FR Solution`: **green**,
`logs/RSVS3/final.log` (2,640 jobs). Two build-tree changes remain, both in other tracks' files:

- `FRNodeLinks4.acceptRunL4_node` (PORT's): the edit of §5 request 2, applied in the build tree only
  (`patchdec.py`). It builds with it. It is red at HEAD because the call still uses `cells4`
  (`auto-1.log`).
- `FRXSig4H.xRows_of_stmt` (S-H4/PORT's file): sorried. It is red at HEAD independently of this track:
  `maximum recursion depth` at `rw [extRowsC, if_pos rfl, …]` (line 41), after B4's `7537acd`
  changed `FRNodeRows4Ext`. It is not on `certificate_sub4`'s path.

`FRSoundness4R4FrE` (`e_end4`, `not_rejEndE4_node`, `e_in4`, `e_fin4`, `not_rejFinE4_node`),
`R4FrRS.e_bind4` and `R4Start.start4_of_fields` **build at HEAD**: they are this track's symlinked
worktree text, built with no stub (`auto-1.log`: `Built FRSoundness4R4FrE`). PORT's tree predates
`50a7f52`. Axioms at `154744b` (`axioms-154744b.log`): all 27 probed theorems, **including PORT's
`certificate_sub4`**, depend on `propext`, `Classical.choice`, `Quot.sound` only. No `sorryAx`
anywhere on its path (`sorrydeps-154744b.log`).

**First pass, at `50a7f52`** (kept for the record; `logs/RSVS3/at-50a7f52/`):

- Build tree: HEAD `50a7f52` text for every module but this track's (all `FRSoundness4*`,
  `FRNodeStmtR4`, `FRNodeSound4K`: symlinks to the worktree). `lake build FR Solution`:
  **green**, `logs/RSVS3/at-50a7f52/auto-12.log` (2,635 jobs).
- Build-tree-only sorries (other tracks' reds at `50a7f52`; `patchdec.py` + `autosorry.txt`):
  RSV-S's decoder list (`FRXChain4` `fsMsgs4_zero`/`fsMsgs4_length`/two `decide +kernel`,
  `FRXDec4Levels` cost, `FRXDec4F0.fmt4_vals`/`lv_cap4`, `FRNodeRun4S.execA_proto`/`gap4Imp_of_run`);
  PORT's `FRNodeLinks4.acceptRunL4_node`, `FRNodeLinks4Run.fmAns_of_run4`, `FRXOut4.reassemble4_size`/
  `pf4_size`, `FRXOut4W.segTr_eq`/`signedWords_agg`/`sgnX_fits`/`readW4_fits`, `FRXOut4P.rl_vS`,
  `FRXOut4A.aggL_eq'`/`chR_agg`/`aggRegs_sem`, `FRXOut4O.cso_pfIR`/`cso_trS`/`cso_trB`, `FRXNd4.nd_out`.
- **Axioms** (`logs/RSVS3/axioms.log`, `scratch/Ax.lean`): `run_gCellsOpsK`, `gFinPf_reloc`,
  `run_rsvChain`, `flag_gFinPf4`, `cells2_sum`, `w0V4_eq4`, `wV4_of_fields`, `relPf4_of_fields`,
  `fin4_of_fields`, `hz_of_fields`, `finRest4_full`, `acceptTail4_node`, `relE4_rejects`,
  `acceptRun4_seg/_node`, `runFacts4H_C`, `X4.ks_rev4R`, `X4.certificate_rev4R`, `X4.certificate_rev4`,
  `R4.ks_rev4HR`, `R4.certificate_rev4HR`, `R4.ks_rev4H`, `R4.certificate_rev4H`, `P4f.ks_rev4H`,
  `P4f.certificate_rev4H`, `P4f.certificate_rev4GH`: **`propext`, `Classical.choice`, `Quot.sound`
  only** (two of them without `Classical.choice`).
- `FR.Sub4.certificate_sub4` (PORT's): `+ sorryAx`. Its direct `sorryAx` users
  (`logs/RSVS3/sorrydeps.log`, `scratch/SorryDeps.lean`): `FRXNd4.nd_out`, `FRXOut4W.readW4_fits`,
  `FRXOut4O.cso_trB`/`cso_trS`/`cso_pfIR`, `FRXDec4F0.fmt4_vals`, `FRXDec4Levels.cost_decLevels4`:
  all build-tree stubs of other tracks' reds. `R4.certificate_rev4HR` has none.
- No `sorry` in any worktree source of this track. Source rule (`logs/RSVS3/source-rule.log`):
  420 files, 0 findings.

## 4. Kernel time

Two measures (`logs/RSVS3/`). This machine was loaded during them (other tracks' builds).

**(a) Per-declaration kernel replay of the whole closure** (`KReplay.lean`, the H-cert probe's tool,
on `Solution`'s non-control names, one core: `kr/kreplay-upper.tsv`, 12 min wall; table
`kernel-table.txt`), summed per module and compared with H-cert3's (`e840553`, run 40884559372, on
a 7763). The non-entry closure (Mathlib, core) calibrates the machines: 92.6 s here, 37.0 s on the
7763, factor 2.504. Column "7763" is the local figure divided by that factor. The tree is at `50a7f52`
with other tracks' reds stubbed, so the entry total (236.6 s at 7763 speed vs H-cert3's 299.7 s)
is not a certificate figure. Main's G5 golf, merged since H-cert3, also explains the drop.

| Module | here (s) | at 7763 (s) | H-cert3 (s) |
|---|---|---|---|
| `FRSoundness4R4PfFlag` | 1.537 | 0.614 | 0.617 |
| `FRSoundness4R4PfRun` | 1.067 | 0.426 | 0.550 |
| `FRSoundness4R4W0R` | 0.607 | 0.242 | 0.287 |
| `FRSoundness4R4PfFin` | 0.633 | 0.253 | 0.292 |
| `FRSoundness4R4Full` | 0.066 | 0.026 | 0.034 |
| `FRSoundness4R4FrCtrl` (+`FrCtrlB`) | 0.040 | 0.016 | 0.022 |
| `FRSoundness4XRun` | 0.138 | 0.055 | 0.059 |
| `FRSoundness4XRunG` | 0.044 | 0.018 | 0.019 |
| `FRNodeStmtR4` | 0.185 | 0.074 | — |
| `FRNodeSound4K` | 0.014 | 0.006 | 0.008 |
| **all `FRSoundness4*` + `FRNodeStmtR4` + `FRNodeSound4K`** | 120.49 | **48.11** | **46.19** |

Each module this track touched is within noise of, or below, its H-cert3 figure. The second chain
costs no measurable kernel time: `flag_gFinPf4` is block-wise. The family's +1.9 s against H-cert3
comes from modules this track did not change, which differ from `1782ab4` through earlier rev44
work: `TailC` +3.1, `R4Cap` +1.5 (new since H-cert3), `TailD` +0.8, `R4Fin` +0.7 (RSV-S2a's
reserve branches), `RsvRun`/`RsvStack` +0.3 (new). Offsetting them: `Pos` −1.1, `TailHide` −0.6,
`TailStep` −0.5.

**(b) Sequential profiles** (one core, `Elab.async=false`; `prof-summary.txt`, `profile-<m>.log`),
"type checking" = kernel:

| Module | wall | kernel | tactics |
|---|---|---|---|
| `R4PfRun` | 17.3 s | 1.49 s | 3.45 s |
| `R4PfFlag` | 23.7 s | 1.72 s | 6.22 s |
| `R4W0R` | 10.3 s | 0.59 s | 0.85 s |
| `R4FrCtrl` | 9.6 s | 0.40 s | 1.59 s |
| `XRun` | 10.1 s | 0.16 s | 0.88 s |
| `XRunG` | 7.2 s | 0.04 s | 0.02 s |
| `FRNodeStmtR4` | 7.8 s | 0.16 s | 0.30 s |
| `FRNodeSound4K` | 7.1 s | 0.01 s | — |
| `R4PfFin` | 10.6 s | 0.79 s | 1.11 s |
| `R4Full` | 8.8 s | 0.08 s | 0.19 s |

RSV-S2a's `R4PfFlag` had no profile, because it did not build. Every module checks in under 25 s
wall, with no simp over the op lists.

## 5. Open items and requests

1. RSV-S2a §5 and RSV-S2b §5 items 1–3 and 5 are closed (§0).
2. **PORT, `FRNodeLinks4.acceptRunL4_node`: needed now. HEAD is red there with this track's
   `wV4_of_fields`, and was already red at `50a7f52`.** Since RSV2, W₀ batches `cellsX = cells4 ++ rsvCells`
   (`X4.W0X`), and `XRun.acceptRun4_node` already uses it. Replace lines 68–69:
   ```lean
     have hW := wV4_of_fields hF hkC (finTabs4_node ν _ _) (ptIx_node4 ν _ _ _) (cells := X4.cellsX)
       hcellsX rfl rfl (by cases ν <;> rfl) (show seq4.mStar - 7 = 25 by rw [seq4_mStar])
   ```
   This is verified in the build tree (`b7.log`, `final.log`). Nothing else in the theorem changes.
3. **B4/PORT, `FRXSig4H.xRows_of_stmt`**: red at HEAD (`maximum recursion depth` at line 41, after
   `7537acd`'s `FRNodeRows4Ext`). This track has not touched it.
4. **`gap4Imp_of_rsv`: not started, left for the next track** (the orchestrator's optional item). Plan:
   `SlotRunA`'s import conjunct is over *all* of `impAP rt A 0`, and the facts it needs about the
   evalM inputs come from `compileX_run`, which itself assumes `SlotRunA`. So the proof needs a
   **prefix form of `compileX_run`**: `RepS` for every register of the trail before the stacked
   `evalM` op, from the rows, aux and asks of that prefix. Then:
   (i) pin prototype 0's `evalM` op and its 57 input / 3 output registers, which are `rsvRel`'s cells
   via `(protoCS 0).slot`; that `rsvRel` is that op's slot map should come from a `decide`-free
   lemma on the compile, as `rsvcells.py` checks it outside Lean;
   (ii) show `impAP rt A 0` contains exactly the three output registers (or that the others are
   covered);
   (iii) take the input values from the prefix `RepS` at `rsvRel[0..57)`, rewrite them with
   `PubCellsR4` (`StmtN4R.2.1`) into `ch`, and apply `N4c.evalM_childV` (with `StmtN4R.2.2`) for the
   outputs' `RepS`.
   It plugs into `R4.Resid4HR.slots` through `gap4Imp_of_run`'s `h`.
5. **PORT, `FRSubmission4Cert`** (when `gap4Imp_of_rsv` needs the child claim in `Gap4R`'s
   discharge; until then nothing breaks):
   ```lean
   def Gaps4 : Prop :=
     ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
       N4s.Gap4R implB (fun _ => implB) X.pf4 κ vk c₁ c₂ w

   theorem resid4H_of … : Snd.R4.Resid4HR (Impl.finC finPf) Layout.lRows 0 sub4 nd D vk :=
     ⟨⟨N4s.I4 _ _ (Impl.implCWith_implT _ _) fun _ => Impl.implCWith_implT _ _, N4s.rd4 X.pf4,
       N4s.I4_rows _ _ _ _, fun κ w c₁ c₂ ch hS => N4s.resid4_of _ _ X.pf4 hS.1
         (N4s.gap4_of_rows X.pf4 pfHdr_pf4 hS.1 (hG vk κ w c₁ c₂ ch hS))⟩,
       fun κ L c π hG' hk hd hr => hL vk κ L c π hG' hk hd hr⟩

   theorem certificate_sub4 (h : Open4) : Certificate sub4 :=
     Snd.R4.certificate_rev4HR (Impl.finC finPf) Layout.lRows 0 sub4 sub4_V sub4_qV sub4_E sub4_ε
       sub4_ext sub4_fuel decOk4_nd nodeDec4_nd (resid4H_of h.gap h.dec) complete_rev4 delta_rev4
   ```
   `FRNodeLinks4.resid4H_of_res`, `FRNodeLinks4Sub`, `FRNodeLinks4SigH` build `R4.Resid4H`; they keep
   working (`R4.resid4HR_of_H` converts), or switch to `Resid4HR` with `fun κ w c₁ c₂ _ hS => hRes κ
   w c₁ c₂ hS.1`. `hL_of_res` stays at `StmtN4` (the links need no child claim).
6. **B4, `FRNodeRows4PackSound`** (off the certificate's path): `Resid4GR.gap`/`ks_rev4GR`/
   `certificate_rev4GR` may move to `StmtN4R` the same way (`gap4_of_rows pf hpf hS.1`, route through
   `R4.certificate_rev4HR`); nothing breaks if they do not.
7. `FRNodeCircuit4`: not touched. No other track's worktree file was edited.
