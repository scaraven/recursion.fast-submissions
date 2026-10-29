# RSV-S2a JOURNAL: the reserve's flags and the E/Pf discharges (RSV-S §5 items 1–4)

Track RSV-S2a, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `b156c27`
(RSV-S WIP). Build tree `logs/fr-build-RSVS2a` (a copy of `fr-build-RSVS`; `mymods.txt` = this track's
modules only, the rest HEAD snapshots; `patchdec.py` as RSV-S's). Logs `logs/RSVS2a/`. No sub-agents,
nothing committed.

## 1. Setup

- `cp -a logs/fr-build-RSVS logs/fr-build-RSVS2a` (31 s); scripts log to `../RSVS2a/`.
- `mymods.txt`: `FRSoundness4R4Fin R4FrE R4PfFlag R4PfFin R4FrRS R4Start Qry` + new `FRSoundness4RsvRun`.
- Baseline `logs/RSVS2a/b0-baseline.log`: everything up to `R4Fin` cached; `R4Fin` red at the two
  reserve branches (lines 340, 408), as handed over.

## 2. Work log

- New `FRSoundness4RsvRun` (generic, no `pe4`): `rd_appAt`, `pureRun_mapRange` (n one-output ops),
  `getD_mapRange`, `run_rsvSOps` (36 ops, generic registers), `hornerV`, `hornerV_eq_sum`,
  `run_rsvHorner` (the Horner chain of `rsvBOps`). Builds.
- Note: `omega` treats `Reg`-typed arithmetic (`d + 2 * k - 1 : Reg`) as atoms: `show (… : ℕ)` first.
- `FRSoundness4R4Fin`: **both reserve branches proved** (no sorry), 10 s lake build.
  - `flag_gFinE1` (rsvOps): blocks A (`run_gFinE0off`, the old simp with `act`/`own` off, gives the
    facts at `b+4, 8, 10, 16, 17, 35`), the 60 reads (`pureRun_mapRange`; `rsvEOps_split` by `rfl`
    shows the four read maps are one map `48 + 16 j`), `rsvBC` (`run_rsvBC`, simp with
    `rd_revAccAt` at base `c + 60`), `rsvSOps` (`run_rsvSOps`), `rsvTl` (`run_rsvTl`), joined by
    `pureRun_seq`; the flag is `relE4`'s branch up to `rfl`.
  - `flag_gFinB'1`: `run_gB0` (own ops, gate `¬rsv`), `run_rsvHorner` (59 steps), the 9-op tail
    (`rsvBTl`), `hornerV_eq_sum`, `ring`.
  - **Statement change**: `flag_gFinB'` gains `hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < r.size`
    (the Horner reads `finE`'s 60 exports from the file).
  - Lesson: `refine ⟨_, ?_⟩`/`Prod.ext rfl` on a `some (L, f) = some (?L, g)` goal timed out in
    `whnf`; state block results as `∃ L f, run = some (L, f) ∧ f = …` and `exact ⟨_, _, rfl, ?_⟩`.
- Orchestrator: A1′ committed `e464756`; applied `traces_spacers_le_qV` in `FRSoundness4Qry.ks_queriesC4`;
  build tree re-snapshotted onto `e464756` (`b3.log`: R4Fin, Qry green).
- New `FRSoundness4RsvStack` (`FR.Snd.P4b`): `arr_getD`, `e2R_ge`, `mStack_congr'`, `mStack_lin`,
  `mStack_own`, `mixed_entry`, **`mStack_sP`** (the stacked call at V's 32/25 entries is
  `f̂·(M̃_A+κ_E M̃_B+κ_E² M̃_C)_ν(r_E2, r′) + w·mStack s (x̂) (ŷ)`).
- `FRSoundness4R4FrE` green: `child_vals4`, `mStL_eq4`, `xL_eq4`, `pxL_eq4`, `pyL_eq4`, `sL_eq4`;
  `e_end4` (+ child term, `CharTwo.sub_eq_add`), `e_in4` (+ `κ_E⁴ m̂*`), `e_fin4` (statement change:
  `hM` in `mStack` form at a 32-entry row point; conclusion = `RejFinE4`'s RHS).
- `FrE`: `opsOut_gFinE` (168 / 38), `gFinE_ex_lt`; `flag_gFinE` gains the export values conjunct;
  `FrRS.rsvEx_of_fields`; `Start.start4_of_fields` against RSV-S2b's `vStarL4` (`hrsv`), `start4_seg`,
  `start4_node`. New `FRSoundness4RsvHM.implN4F_hMS` (XRun's `hM`).
- Orchestrator: RSV-S2b committed `7bbbf49`; re-snapshotted; `rsvZero4` added (S2b §5.1).
- `run_horner` clashed with `FRVIRFinalsCoreSG.run_horner` (R4P4 picked mine): renamed `run_rsvHorner`.
- `start4_of_fields`' new `hrsv` reaches `R4LinkP.finRest4_of_fields` and `R4Full` (`FinTabs4.rsv`).
- Build `b15.log`: green through `R4Fin`, `FinLc/Sh/RS/Ctrl`, `FrE`, `FrRS`, `Start`, `LinkP`, `RsvHM`;
  red at `R4PfFlag.gFinPf_reloc` (item 4, handed over). Source rule 412 files, 0 findings.
- Stopped for context (≈ 75 %): RESULT §5 is the handover.
