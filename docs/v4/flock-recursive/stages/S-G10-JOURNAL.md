# S-G10 JOURNAL

- **Base.** HEAD `feca303`. Build tree `logs/fr-build-SG10`: a copy of `fr-build-orch` with its
  `.lake`; `snap.sh` with `MINE="FRSoundnessFr…"` (HEAD's sources, my modules symlinked). INT-5's
  worktree edits (`FRVIRFinals*`, `FRVerifierImpl*`, `FRSoundnessAccLog`, …) are not in the tree.
- Every lean/lake command: `systemd-run --user --scope -q -p MemoryMax=16G (12G for single files)
  -p MemorySwapMax=0 -- timeout …` (`b.sh`, `c.sh`).

## Pass 1

1. **Infrastructure (`FRSoundnessFrRun`).**
   - `accept_fields` forgets the register files: the rest's field `k` gets only `ExtA R₀ Rk`, so a
     field's reads of `zhat` (finRS's exports) and `ex` (earlier fields' exports) have no values.
     New **`accept_chain`** (in my module, `accept_fields` untouched): `finRS` from `R₀` exactly,
     the rest from `Rs k`, `Rs 0 = R₀ ++ L₀`, `Rs (k+1) = Rs k ++ L_k` (`fields_chain`,
     `chain_ext`).
   - Views by name: `one_view`/`oneR_view` (`.squeezes 1 (.one _)`), `coordsR_view`, `outsR_lt`,
     `phaseIx_vals` (17 names, `decide` on `piopPhases.findIdx` only).
   - Log ↔ input: `vkL_fsQ`, `stL_fsQ`, `msgAt_abs`, `sliceL_fsQ`; `phaseOff_stmt`,
     `phaseOff_rs0` (`decide` on the phase table's byte counts, like S-G4's `phaseOff_47`).
   - `finRS`'s exports are below its outputs: `opsOut_finRS = 4117`, `finRS_ex_lt`.
2. **hStart (`start_run`)**: done, generic in `impl` with `phiRS` at spec. `relB` on `Rs 5`
   (`finB′`), `v_RS` from `exec_finRS` on `R₀` (determinism against `accept_chain`'s `L₀`),
   `rsV_eq` (`phiRS` spec, RS1 coordinates, `sliceL_fsQ`), `κ′` by `oneR_view`, `pubH` by
   `vkL_fsQ`/`stL_fsQ`, `K.smulF_one`.
3. **F rounds (`FRSoundnessFrRnd`)**: `roundsT_chalF` (register 3 of each F round is
   `chF a₂ 0`), `refPhase_roundsF`, `genPhase_roundsF`, **`chalsF_view`** (`chals fi name K`'s
   `j`-th register holds `rch (phStart n) es j`, any init claim, degree 2 or 3).
4. **INT-5 landed (`9d1f906`)** mid-pass. Re-snapshotted; `lake build FRSoundnessFrRnd` green on
   `9d1f906` (2,389 jobs; nothing of mine needed a repair: `finRS`, `relB`, `exec_finRS` unchanged).
5. **Stop point (hW0 at 3.16).** `w0V`'s claim-2 term now carries the kind factor (`rsWeightS`,
   `kwSL`), while `W₀L` (`wrsL`, `gL`) has the plain `Φ(eq(p₁, ·))`. For N30 the two differ unless
   `β = 1` (`rsWeight_kind_eq`, `kwS_hashA_ne_plain`), so `hW0` in `kstate_front_of`'s form is not
   provable with the current `W₀L`. RESULT §4.
6. Checks: axioms (36 names, standard only), source rule (178 files, 0 findings), name grep
   (`initVals_length` clashed with `FRVIRSpec`'s: renamed `initValsF_length`), sequential profiles.
