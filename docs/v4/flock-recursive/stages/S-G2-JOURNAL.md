# S-G2 journal (`ligerito_final`)

Base: worktree `v4/flock-recursive`, HEAD `c6b0d47` at the start; `0e93332` (blueprint 3.14 (D),
S-E7) landed during the stage, with no change to the Ligerito tail or A.9's `finP`/`finPf`.

## 2026-10-28

- Read TRACK-RULES, BLUEPRINT §2.3 (P), §5.1–§5.4, A.9 (`finP i`, `finPf`), A.10 (P1.i … Pf and
  "What `final` then gets"), §10 changes 17–21; S-G RESULT (S-G1i/S-G1j), S-H2 Parts 15–17.
- Read the tail as built: `FRSoundnessTailD` (`lvW`, `lvC`, `c1`, `D1`, `DCi`, `DP2`, `DP3`,
  `DPf`, `DT`, `RejT`), `FRSoundnessTailO` (handoffs), `FRSoundnessTailM` (stability),
  `FRSoundnessCompose` (`RejC`, `DkC`, `FrontObl`, `chainStab_of`), `FRSoundnessWalk`
  (`walk_back`, `DH_of_noEsc`), `FRSoundnessTruths` (`farL`, `decodeL`, `msgOf`, `truthP2/C/P3`,
  `truthC_of`), `FRSoundnessHide` (`DH`, `consSet_eq_of_DH`), `FRSoundnessWeights`
  (`mleN_nextW`, `mleN_foldW`), `FRKState.FinalLaw`, `FRVIRFinalsSG` (`finP4`, `finPf`, `lvStepV`).
- Design decision: `FRSoundnessLigerito` is imported by `FRSoundnessHide` (for `eqBits_eq_eq`), so
  `ligerito_final` cannot live there (it needs the tail dooms, which import Hide). New module
  `FRSoundnessLigFinal` (imports `FRSoundnessCompose`).
- Design decision: the "induction from Pf upwards" is S-G's `walk_back` (generic); `ligerito_final`
  takes `¬ DT` on every tail prefix and reads the dooms at three positions per level (P1.i's first
  absorb, C.i, P2.i's last answer). `ligerito_final_of_walk` derives these from what `final` has.
- **Finding (level 4).** The tail batches level 4's queries into Pf (`lvC 5 = vNext 4 (c1 4)`,
  `wPf` includes level 4's tensor weights), while the verifier does not: `finP 4` checks each
  `y_q = Enc₄(final)[p_q]` directly and asserts `claim0 Pf = claimN P1.4`, and `finPf`'s weight
  `wV = lvsV [1,2,3,4] w0V` has only levels 0–3's tensor weights. Pf's first claim is `free`
  (`initClaim`), so the verifier's round-0 check is `g(0)+g(1) = c1 4`, `RejT`'s is
  `g(0)+g(1) = lvC 5`. Kernel-checked consequence: `pf_round0_conflict`. `ligerito_final` reads no
  P3.4/Pf doom, so it is unaffected; `FinalLaw`'s "accepted ⇒ ¬ D at the end" is blocked.
- Built in `logs/fr-build-SG2` (copy of `fr-build`); HEAD moved and `FRVIR.lean` became dirty in
  the worktree (another agent), so switched to a snapshot tree (`snap.sh`: HEAD's modules, mine
  symlinked).
- Built `FRSoundnessLigFinal` (337 code lines): `LigeritoOut`, `ligerito_final`,
  `ligerito_final_of_walk`, Pf's end (`DPf_end_iff`), the level step at the spec
  (`mleP_lvW_succ`, `mleP_pad`), Merkle (`colOf_of_path`, `foldAt_of_cols`), the level-4 finding
  (`lvC_five_eq`, `pf_round0_conflict`), controls (`ligeritoOut_nil`, `not_ligeritoOut_one`).
  Fixes on the way: `congr` timeouts replaced by explicit point equalities; `cap_binding` rewritten
  on the hypothesis, not the goal.
- Green, axioms clean (26 declarations, `logs/S-G2/axioms.log`), source rule 123 files / 0
  findings, sequential profile 11.7 s wall, ≈ 2.7 s type checking. RESULT written.
