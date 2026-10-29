# RSV-S2a RESULT: the reserve's flags, the E checks and `finB′`'s start (RSV-S §5 items 1–3; item 4 open)

Track RSV-S2a, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`; started at
`b156c27`, re-snapshotted onto `e464756` (A1′) and `7bbbf49` (RSV-S2b). Build tree
`logs/fr-build-RSVS2a` (copy of `fr-build-RSVS`; `mymods.txt` links only this track's modules, every
other module is HEAD's text; `patchdec.py` as RSV-S's). Logs `logs/RSVS2a/`. Journal
`stages/RSV-S2a-JOURNAL.md`. No sub-agents, nothing committed.

## 0. Summary

- **Done (kernel-checked in the build tree, no `sorry`):**
  - RSV-S §5 item 1: `R4Fin.flag_gFinE`'s reserve branch (`flag_gFinE1`), block by block
    (`run_gFinE0off`, the 60 reads, `run_rsvBC`, `run_rsvSOps`, `run_rsvTl`, joined by
    `pureRun_seq`). Module build 10 s; no 168-op simp.
  - Item 2: `R4Fin.flag_gFinB'`'s reserve branch (`flag_gFinB'1`): `run_gB0`, the generic Horner
    chain `run_rsvHorner` (+ `hornerV_eq_sum`), the 9-op tail.
  - Item 3: `R4FrE.e_end4`, `e_in4`, `e_fin4` (and their `not_rej*` theorems unchanged in text)
    against the new `RejEndE4`, `c4E4`, `RejFinE4`; `relE4_of_accept` builds.
  - From item 4: `FrRS.relE4_of_fields`, `e_bind4`, new `FrRS.rsvEx_of_fields`;
    `Start.start4_of_fields`/`start4_seg`/`start4_node` against RSV-S2b's `vStarL4` (see §3 for the
    build state).
  - RSV-S2b's request 1: `R4FrE.rsvZero4` (exact statement of RSV-S2b-RESULT §5.1).
  - Orchestrator's request: `Qry.ks_queriesC4` uses `traces_spacers_le_qV`.
- **Open:** item 4's `finPf` half (`gFinPfR` with the second chain, `relPf4`/`w0V4` with the reserve
  cells, `PfFin`, `R4W0R.w0V4_eq4`/`wV4_of_fields` with `hcl : P.cells ++ P.rcells = …`): §5.

## 1. What was built

| Module | Change |
|---|---|
| `FRSoundness4RsvRun` (new) | `rd_appAt`, `pureRun_mapRange` (n one-output ops, generic), `getD_mapRange`, `getD_take'`, `length_mapRange`, **`run_rsvSOps`** (36 ops, generic registers), **`hornerV`**, **`hornerV_eq_sum`**, **`run_rsvHorner`** (Horner chain, generic registers) |
| `FRSoundness4RsvStack` (new) | `arr_getD`, `e2R_ge`, `mStack_congr'`, `mStack_lin`, `mStack_own`, `mixed_entry`, **`mStack_sP`** (the stacked call at V's 32/25 entries in `RejFinE4`'s terms) |
| `FRSoundness4RsvHM` (new) | **`implN4F_hMS`**: `NI4F.implN4F_hMX` in `e_fin4`'s `hM` form (`mStack` of the entries) |
| `FRSoundness4R4Fin` | `rd_revAccAt`; `run_gFinE0off`; `rsvBC`, `rsvTl`, `rsvEOps_split` (`rfl`); `run_rsvBC`, `run_rsvTl`, `rsvSOps_reloc`, `getD_lt'`, **`flag_gFinE1`**; `gB0`, `rsvBTl`, `gFinB'_rsv`, `run_gB0`, **`flag_gFinB'1`**; `flag_gFinE`/`flag_gFinB'` closed |
| `FRSoundness4R4FrE` | `child_vals4`, `mStL_eq4`, `xL_eq4`, `pxL_eq4`, `pyL_eq4`, `sL_eq4`; `opsOut_gFinE`, `gFinE_ex_lt`; `e_end4`, `e_in4`, `e_fin4` re-proved; **`rsvZero4`** |
| `FRSoundness4R4FrRS` | `e_bind4` (proof); new **`rsvEx_of_fields`** |
| `FRSoundness4R4Start` | `start4_of_fields` (reserve term; `hrsv`), `start4_seg`, `start4_node` |
| `FRSoundness4Qry` | `ks_queriesC4`: `traces_spacers_le_qV` (A1′'s request) |

## 2. Statement changes, with reasons

| Theorem | Change | Reason |
|---|---|---|
| `R4.flag_gFinB'` | gains `hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < r.size` | the Horner block reads `finE`'s 60 exports; the relation reads them from `r` (Start supplies it: `gFinE_ex_lt`) |
| `R4.flag_gFinE` | conclusion gains `∀ i < rsvN, P.rsvOps = true → rd (r ++ L) ((gFinE …).2.drop 1 |>.getD i 0) = .f (pe4 … fLrEnd (48 + 16 i))` | `finB′`'s reserve term must be read back as the child claim's values (`rsvEx_of_fields` → `Start`); consumers' `⟨L, h, -⟩` patterns unchanged |
| `R4.e_end4` | RHS gains `etaL·eq(lowA p_x, r)·(m̂* − X)` | `RejEndE4` (ii″) |
| `R4.e_fin4`, `not_rejFinE4_node` | `hM` is now `∀ τ σ, τ.size = 32 → impl.evalM τ σ = (P4b.mStack srcE (τ[23+·]) (τ[·]) (σ[·]), 0, 0)`; conclusion is `RejFinE4`'s RHS (+ `κ_E⁴·eq(p_y, r′)·mStack s x̂ ŷ`) | RSV2's one stacked call; for `implN4F` the hypothesis is `implN4F_hMS` |
| `R4.start4_of_fields` | gains `hrsv : P4b.nRsv (kindOfC es) = if (P.rsvOps && P.rsv) then rsvN else 0` | links the program's reserve flag to the log's kind (seg: `rfl`; node: `cases ν <;> rfl`) |
| `R4.finRest4_of_fields` (`R4LinkP`) | gains the same `hrsv` | passes it to `start4_of_fields` |
| `R4.FinTabs4` (`R4Full`) | new field `rsv` | `finRest4_full` supplies `hrsv` from the tables (`rfl` for both kinds) |
| `R4.rsvZero4` (new) | RSV-S2b-RESULT §5.1's statement verbatim | XRun's `RsvZero` |
| `R4.e_in4` | text unchanged (`c4E4` gained `κ_E⁴ m̂*`) | — |

Definitions: none of `relE4`, `vStar4`, `relB4` changed text (RSV-S's statements stand).

## 3. Build, times

- Build tree on `7bbbf49` (+ this track's worktree modules), `logs/RSVS2a/b15.log`: **green** for
  `RsvRun`, `RsvStack`, `RsvHM`, `R4Fin` (11 s), `R4FinLc/Sh/RS/Ctrl`, `R4FrE` (7.9 s), `R4FrRS`,
  `R4Start`, `R4LinkP`; `Qry` green (`b12.log`). **Red**: `R4PfFlag.gFinPf_reloc` (item 4, §5) and what
  sits behind it (`PfFin`, `W0R`, `R4Full`). No `sorry` in any touched source.
- Sequential profiles (one core, `Elab.async=false`; `logs/RSVS2a/prof-summary.txt`,
  `profile-<m>.log`), kernel = "type checking":

  | Module | wall | kernel | tactics |
  |---|---|---|---|
  | `RsvRun` | 9.7 s | 0.56 s | 1.34 s |
  | `RsvStack` | 8.9 s | 0.36 s | 0.53 s |
  | `RsvHM` | 7.7 s | 0.01 s | 0.07 s |
  | `R4Fin` | 36.5 s | 3.41 s | 7.5 s |
  | `R4FrE` | 24.5 s | 2.39 s | 4.04 s |
  | `R4FrRS` | 15.1 s | 0.31 s | 1.1 s |
  | `R4Start` | 9.7 s | 0.31 s | 0.87 s |
  | `R4LinkP` | 9.7 s | 0.40 s | 0.78 s |
  | `Qry` | 45.3 s | 0.72 s | 0.57 s |

  The two reserve branches add ≈ 7.3 s of kernel over the five new modules and `R4Fin`/`FrE` (RSV-S's
  `R4Fin`/`FrE` profiles at HEAD are not in a log; the delta is not measured).
- Source rule (`logs/RSVS2a/source-rule.log`): 412 files, 0 findings. Axioms: not checked (the
  certificate does not build yet).

## 4. Requests to other tracks' files

1. **`FRSoundness4XRun` line ~120** (owner: RSV-S2b / the chain): `not_rejFinE4_node NI4F.srcE4 NI4F.srcL4
   (NI4F.implN4F_hM _ ν) …` becomes `(implN4F_hMS _ ν)` (module `FRSoundness4RsvHM`, add the import).
2. `FRSoundness4R4FinCtrl` builds unchanged (`relB4_fin3P`). `R4FrCtrl` not re-checked.
3. **Modules touched outside my list** (no owner listed; downstream of `Start`/`PfFin`):
   `FRSoundness4R4LinkP.finRest4_of_fields` gains `hrsv` (passed to `start4_of_fields`);
   `FRSoundness4R4Full.FinTabs4` gains the field `rsv : P4b.nRsv κc = if (P.rsvOps && P.rsv) then rsvN
   else 0` (`finTabs4_seg`/`finTabs4_node` by `rfl`; every user builds `FinTabs4` through them).
   `R4W0R` is mine now (RSV-S2b §5.2; not yet changed).

## 5. Open, in order (handover)

Everything left is `finPf`'s half of RSV-S §5 item 4 plus RSV-S2b's request 2. The red point in the
build tree is `FRSoundness4R4PfFlag.gFinPf_reloc` (line 130: `rfl` times out, because `gFinPf` now
has the second cell chain and `gFinPfR` does not); `PfFin`, `W0R`, `R4Full` sit behind it.

1. **`R4PfFlag.gFinPfR`**: insert, after the first chain (`gCellsOpsK … P.ncell 0 z0 cb (cb + 1)`),
   `FRVIRFinals4.gFinPf`'s reserve block with `Q := fun _ => P`:
   `cond P.rsvOps (gCellsOpsK nc one (wb+2) (wb+(nc+2)) kp (fun j _ => P.rcells.getD j 0) P.nrcell 0 acc9
   (c9 - 1) c9 ++ [.keep (fun _ => P.rsv) (gCellsAccK nc P.nrcell acc9 c9) acc9]) []` (read `acc9`,
   `c9`, and the shifted `ce`, `lb`, … exactly from `gFinPf` at `FRVIRFinals4` 541–590), then
   re-prove `gFinPf_reloc` (it was `rfl` after the simp; keep that shape).
2. **`R4PfFlag.w0V4`**: add, where `P.rsvOps && P.rsv` (and `node`), the second chain's value:
   `cellsVal4 P.nc ρ kp (fun j => P.rcells.getD j 0) P.nrcell 0 (kp^11) A` with `A` the first chain's
   sum, i.e. `Σ_{i<60} κ′^{11+i}·eq(rcell_i, ρ)` (the chain starts at power `c9 − 1`: check it is
   `κ′^{11}` in `gFinPf`). `relPf4` is unchanged in text (it goes through `w0V4`).
3. **`R4PfFlag.flag_gFinPf4`** (the run): after block 9 (the first chain, `run` of `gCellsOpsK` with
   `cellsVal4`), run the second chain with the same lemma from the first chain's registers
   (`pureRun_seq`), then the `keep`; the `ce`/`lb`/… shift is the second chain's width. Reuse
   `run_gCellsOpsK`/`cellsVal4` (PfRun) unchanged.
4. **`R4W0R.w0V4_eq4`, `wV4_of_fields`**: `hcl : P.cells ++ P.rcells = P4b.cellsC cells κc` (RSV-S2b
   §5.2, XRun already calls them with `rfl`); in the node case `cellsVal4_sum` twice and
   `Finset.sum_range_add` over `9 + 60` (as `P4b.pubPart_eq`), with `hncell`, `P.nrcell =
   P.rcells.length`; segments: both lists empty. Hypotheses `hncell` may need a companion
   `hnr : P.nrcell = P.rcells.length` and the `rsvOps ∧ rsv` gate: on `N8` `rsvCells = []` so the
   gate's value does not matter (`cellsVal4` over 0 cells is the identity).
5. **`R4PfFin`**: `relPf4_of_fields`, `fin4_of_fields`, `hz_of_fields` re-checked (texts unchanged;
   the weight gains the reserve term through `w0V4`).
6. Then the certificate build (`FR Solution FRSubmission4Cert`) with the decoder/B3 patches as
   PORT leaves them, the axiom check, and the sequential kernel profile.

Notes for the next agent: block proofs are cheap (`R4Fin` 10 s with both reserve branches); never
`refine ⟨_, ?_⟩` on `some (L, f) = some (?L, g)` (whnf timeout: state `∃ L f, run = some (L, f) ∧ f =
…`); `omega` does not see through `Reg`-typed arithmetic (`show (… : ℕ) < …` first); `rd_revAccAt`
handles blocks whose base is `c + k`.
