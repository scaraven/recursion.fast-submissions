# S-G4 journal: `hFin` (the finals read off the log)

Base HEAD `b1d8c46`. Build tree `logs/fr-build-SG4/` (copied from `fr-build-SG3`; `snap.sh` takes
HEAD's version of every other module, S-G4's modules are symlinks; `b.sh` builds under the 16G
cap and prints errors only).

## 2026-10-28

- Set up the tree; `lake build FRSoundnessAcc FRSoundnessAccSem` replays green at HEAD.
- **Step 2a** (`FRSoundnessAccSeg`): `refPhases_at` (phase `k` of a run of phases: the trace
  before it, its `refPhase` run from the generator's context `genPhases (ps.take k)`, `ExtA` into
  the run's registers, its flag among the flags); `phase_at` on the table from `ctx₀`, with
  `(fsOf tr items).drop (phStart k) = fsOf trk (psItems (phases.drop k))`; `skeleton_outs`
  (`outs[k]` is what phase `k` pushes). Table rows: `phases_lvl` (row `26 + 5i + k` is
  `levelPhases i`'s `k`), `phases_pf` (row 51), `phaseIx_P1 = 26`, `phaseIx_Pf = 51`.
  - The two `phaseIx` facts compare row names with `decide` on `piopPhases`' 26 names (the
    level rows are opened by `simp [levelPhases]`). This is a decide over the names of the table
    rows only, not over a program or the item list; recorded as a deviation.
- HEAD moved to `937e14d` (S-E8's commit) while I worked; `snap.sh` re-read HEAD, so S-G4 is
  built against `937e14d` (`evalOp`'s `dotKF` is now `dotKFF`; `refPhase` still says `dotKF`).
- **Step 2b, rounds** (`FRSoundnessAccVal`): `roundsT_vals` (13 registers per K round: `rs` the
  challenge, register 12 the `g(r)`); `SkRun` (the accepted skeleton bundle); `rounds_view`: a K
  rounds phase with a free first claim, on the log: `outs[n] = (b+2) :: rs ++ [b+13K+2]`,
  `b+2 ↦ rSum … 0`, `rs[j] ↦ chK (ansAt … (phStart n + 2j + 1))`, last `↦ rVal … (K−1)`, the
  in-phase checks `rSum (l+1) = rVal l`, and `cAt (n+1)).foldR = rs`.
- **Step 5** (`FRSoundnessAccEq`): `eqTab_getD` (bit `v` ↔ coordinate `v`), controls
  `eqTab_ctl`/`eqTab_rev_ne` (the reversed order gives a different entry); `dotKF_eq_sum`;
  `fhVal_mle` (`final̂ = mleN 7 finV sf`); `tensorWS_unit`; `encVal_eq_encAt` (Horner over 2^7 is
  `encAt κ 4 m p` when the π elements past `2^mLog` are zero).
- **Step 2b, queries/squeezes** (`FRSoundnessAccQry`, `FRSoundnessAccLvl`): `stepsT_path`,
  `posT_path`, `posAllT_path` (the trace's Merkle steps are an `openPath … runLog L` on a log
  with no repeated query); `pos_view`, `coords_view`, `queries_view`, `final_view` + `finV_zero`;
  `genPhase_out_lt`/`skeleton_out_lt` (every out register is below the skeleton's size, for the
  `hin` hypotheses of the flag lemmas).
  - `omega` ignores comparisons at type `Reg` (an `abbrev` of `ℕ`): `simp only [Reg]` or an
    `(α := ℕ)` ascription is needed.
- **Step 2b, by level** (`FRSoundnessAccPf`, `FRSoundnessAccCol`): `p1_facts`, `pf_facts`,
  `kc_facts`, `ys_facts` in `FinIn` terms (`fi.outs = skeleton.2.outs`); `capDig_eq` (the log's
  cap entry is π's at the verifier's offset; S-H2's `capOffL_fsMsgs`, `fsMsgs_ctl`, S-G's
  `capPos_eq`); `phaseOff_add_le`/`fieldOff_add_le` (a column lies inside π, so `dotKF` sees all
  `2^ℓ` rows).
- **Step 6** (`FRSoundnessAccW`): `tailList`/`tailList_eq` (the tails as `ptL`), `tail_vals`,
  `lvStepV_eq` (one level step is `wHatL`'s, `tensorW` at the spec), `wV_eq`.
- **Assembly** (`FRSoundnessAccLog`): `noAsk_finZ/Lc/Sh/Lr`, `noAsk_sf`, `kindOf_fsQ`,
  `finalAt_fsQ` (needs `phaseOff 47 fFinal = 0`, `decide`, ~170 ms), `pfRefs_lt` (every register
  `finPf` reads is a skeleton out), **`finLog_of_run`**, **`hAcc_of_fin`**, `tensorW_implC`.
  - `rfl`/`congr 1` attempts on mismatched branches unfold `sAt`/`pfP` and time out: closers
    ordered `omega` first, explicit `congrArg` instead of `congr 1`.
- Axioms (`logs/S-G4/axioms.log`, 141 declarations): only `propext`, `Classical.choice`,
  `Quot.sound`. Source rule: 147 files, 0 findings (`logs/S-G4/source-rule.log`).
