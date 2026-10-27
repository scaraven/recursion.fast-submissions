# S-G journal (track L-cert: knowledge soundness)

Base: branch `v4/flock-recursive`, HEAD `cf2f7b3`, blueprint revision 3.9. Build tree
`logs/fr-build-SG` (HEAD's versions of other tracks' modules via `snap.sh`, the S-G modules
symlinked; `.lake` copied from `fr-build-cert`). Every `lake`/`lean` run used the 16 G scope and a
`timeout`.

## 2026-10-27

1. Read TRACK-RULES, blueprint §5, §7, A.9, §10 changes 1–9, the contract's `KState`, the core
   library's `Library/Security.lean`, spartan-srom's `SoundnessLog` and `SoundnessKSBase` Part A
   (the template), and S-0's `FRTranscriptDefs` (items, queries, `windows`, `carried`, `frEnc`).
2. Design point found before writing: spartan-srom charges a chain on `L₀ = L.take cut` (the log
   before the chain's single commitment absorb). Flock absorbs the caps of levels 1–4 and the
   final message in the middle of the chain (phase `C` of each level), so their Merkle trees are
   not in that prefix. Changed `L₀ L j` to `L.take j` (the log before the chain's last entry). The
   generic `muG_step` keeps its proof shape; the per-row lemmas inherit a stability obligation
   (`D`/`φ` read the same trees off `L.take i` and `L` when `L` has no bad event; this is what
   `FRMerkle.colL_prefix` gives for trees under caps absorbed in the chain).
3. Second design point: the blueprint's window count `≤ (queryCap/16 + 1)·logCap` assumes every
   logged query has at most `queryCap` bytes, but the knowledge state's log holds arbitrary oracle
   queries. `wins q` is empty for a query longer than `queryCap` (no verifier asks one). The window
   hit includes the entry's own query (`i ≤ j`), and both offsets `7 + 16k` (the seed's) and
   `8 + 16k` are taken for every query (a superset of `inPlay`). Count:
   `|L|·(2^17 + 2) + 2^17 + 1`, `badCount_frac_le`: `≤ 2^-142` per query (blueprint: `2^-144`).
4. `FRLog` written (forest, frontier, `extCount_split`, chains over `fsItems = items.filter isFS`,
   `bad_step_le`): built at the first attempt after renaming `Item.fsCheck` to `fsCheck` (dot
   notation looks in `FR.Item`, S-0's namespace) and a classical `DecidablePred IsChain`.
5. `FRSoundnessDefs` Part A (`muG`, `muG_step` with the new `hloc` form) built at the first
   attempt. Part B: `lastAns`, `ext1`, `ext`, `condCount`, `condCount_split`, `condCount_last`.
6. Challenge fibers in `FRLog`: `chFEquiv : Digest ≃ F × F`, `chKEquiv : Digest ≃ K`,
   `card_chF2_fiber`, `card_chF_fiber` (`|S|·2^128`), `card_chK_fiber` (`|S|`). A first version
   with `Finset.card_bij` and `simp` hit `maxRecDepth` (instance mismatch between a classical and a
   `Finset.decidableMem` filter); `Finset.card_equiv` with `[DecidablePred P]` fixed it.
7. `FRVIRFinalsSG.lagV_eq_lagrangeWeight` (S-F open 2): `lagV l lo` is
   `lagrangeWeight sNode l ⟨lo, _⟩` at the 64 nodes `quirky_claim_split` uses, via
   `Fin.succAboveEmb` for `others lo` and `CharTwo.neg_eq`.
8. `FRSoundnessLigerito.eqBits_eq_eq` (A.2).
9. Controls: `not_bad_nil`, `bad_self_state`, `bad_collision`, `matches_seed`,
   `not_matches_squeeze`, `muG_empty`, `muG_bad_self`.
10. Axioms (scratch `#print axioms` outside the entry): `muG_step`, `bad_step_frac`,
    `card_chF_fiber`, `card_chK_fiber`, `condCount_split`, `matches_seed`,
    `lagV_eq_lagrangeWeight`: `propext`, `Classical.choice`, `Quot.sound`.
11. Sequential profiles (`lean -DElab.async=false --profile`, one core): `logs/S-G/profile-*.log`.
12. Stopped here (the brief's conservative pace): the per-phase doom predicates over the Flock
    layout, the row lemmas, `ligerito_final`, `final`, `finP`/`finPf` and `kstate` are not
    started. RESULT §5 lists what each needs.

## 2026-10-27 (S-G3)

13. Rulings received (§10 changes 10). S-G3 started: read A.9's finP/finPf rows, `FRVIR` (op
    set, `genPhase`, `posOps`), S-F's finals and the native `prover/ligerito.rs` verifier
    (`verify`, `weight_eval`, `u_hat`, `consistency_weights`).
14. Found: `rsWeight` is not in `FRVIR.Op`/`OpImpl` yet (only `mbp`), and `evalM`'s column point is
    `AF` while Ligerito's point is in K. `finPf` is blocked on both; its formula from the native
    verifier is recorded in RESULT §3.
15. `finP` written. A first version built the unit vectors with `packK` from `0`/`1` registers;
    replaced by `const` `AK` vectors (register-independent, simpler proofs).
16. Proofs: `run_accOps`, `flag_finPLow`; `run_layer`, `run_horner`, `run_encOps`,
    `run_positions`, `flag_finP4`; `hornerVal_eq`; `noAsk_finP`. Pitfalls:
    - `omega` failed on goals whose base register was a `set` variable. The cause was a broken
      `hb` proof left behind by a regex rename (`simp [(r.size + L.length), …]`), which confused
      the later goals. I replaced `set` with explicit expressions.
    - `pr_op` needs the exact `[] ++ [v₀] ++ …` shape of the register list.
17. Dump: a private copy `logs/fr-build-SG/dump/IRDumpSG.lean` (`lake build irdumpsg`), with the
    full finals and array constants printed; outputs in `logs/S-G/dump/`.

## 2026-10-27 (S-G1, part 1)

18. Ported the template's `hloc_of` to the charging log `L.take i`. The only change in substance:
    the last step compares `condCount` on `L` and on `L.take i`, which needs `hstab` (equality of
    `EscAtG` on every formal extension `ext (es.take k) as`; the `dropLast` of an extension is
    again one).
19. Flock helpers: `split40` / `eq_squeezeQ` (a squeeze item with state `st` is `squeezeQ st`),
    `matches_append_iff`, `ext_take`. Pitfall: dependent `getElem` indices (`es.length - 1 + 1`)
    cannot be `rw`ritten. I used `congr 1; omega` on the `getElem` equality instead.
20. `fsRanges` computed from `phases`; `RndOK` by a boolean check under `decide +kernel` (7 s of
    kernel time in total). The values are pinned in `fsRanges_eq`.
21. `card_idx_fiber`: `natLE` through `finFunctionFinEquiv`; the indices through
    `finFunctionFinEquiv.symm` at base `2^b` (`finFunctionFinEquiv_symm_apply_val` is exactly
    `idxOf`); the count through `finProdFinEquiv`.
22. Stopped before the doom predicates (budget). RESULT S-G1 §3 has the plan.

## 2026-10-27 (S-G1b)

23. Read TRACK-RULES, S-G-RESULT (all), `FRSoundnessDefs` Parts A–D, the template's
    `SpartanSromSoundnessDefs` (Rej/Alg/Doom), blueprint §5.1–§5.2, A.2–A.4 and §10 changes 10–11,
    and `roundOpsF` / `FRVIRSpec.g3` (the degree-3 round: `c₃ := claim + (c₁ + c₂)`, so no check).
24. Plan: deliver the readers and the words, then one phase end to end with every obligation and
    the step at `εR`, then generalise. Chosen phase: the degree-3 F rounds (Z3; same shape as Lr2,
    E2), generic in the truth.
25. `FRSoundnessStepA`: readers, `fsStarts` (`decide +kernel`, pinned), `capPos`, `capDig`,
    `colOf`, `wordOf`, `FarAt`. Pitfalls:
    - `decide` on a concrete seed query hit `maxRecDepth`; `decide +kernel` works;
    - controls must not quantify over the answer (`decide` needs a closed goal).
26. `FRSoundnessStepB`. Pitfalls:
    - `(bind0 · chF a 0)` parses as `fun x => bind0 x chF a 0`; write `(bind0 · (chF a 0))`.
    - `set κ := kindOf es` left `nr (kindOf es)` from rewritten hypotheses as a separate omega
      atom; drop the `set`.
    - `(Finset.mem_filter.mp ha).2` and `refine Finset.mem_filter.mpr …` under `open Classical`
      hit `maxRecDepth` (instance unification); `rw [Finset.mem_filter] at ha` and
      `simp only [Finset.mem_filter, …]` work.
    - `hA.mono (by omega)` inside `simp only [...]` arguments runs `omega` on an open
      metavariable; give `(l := j)`.
    - `g3_check`: `simp` on `peval` of a literal array produced `pure` and a kernel timeout.
      Generalise the three `readF`s and use `peval_four` (via `peval_eq_sum`), then
      `linear_combination … * CharTwo.two_eq_zero`.
    - The `constructorNameAsVariable` linter crashed on `D3_single`; switched off for that
      declaration, as in FRLog.
27. Obligations: `habs` by the odd-offset squeeze check, `hmid`/`hround` by the checked gap to
    the multi-squeeze phases (`condCount_eq_zero`), `hsingle` by `D3_single`, `hstab` by
    `TruthStable`. `z3_step` and `rounds3_step` give the step law at `εR`; `lr2_phase` and
    `e2_phase` use `roundsPhase_of` (two kernel checks each).
28. Times, axioms and the source rule recorded in RESULT S-G1b §2. Stopped here (budget):
    the composed doom, the truths, the degree-2/K rounds and the multi-squeeze rows are in RESULT
    S-G1b §5.

## 2026-10-27 (S-G1c, part 1)

29. Blueprint 3.10 (A.10, changes 12): composition ratified; per-phase truths tabled; the P2 bound
    to be kernel-checked here.
30. `FRSoundnessStepC`.
    - Composition: `stepObl_compose`, under `RejOK` (`mono`, `sq`, `stab`).
    - The rows: `single_F_le`/`single_K_le`, `round_row_F`/`round_row_K`.
    - The P2 row: `card_idx_in` → `card_pos_in` → `p2_round_le` → `p2_hround`.
    - Pitfalls:
      - `norm_num` will not evaluate `3^290` (core's `Nat.pow` evaluation stops above exponent
        256); `decide +kernel` on ℚ works (15 cases, fast).
      - `rw [← Fin.prod_const]` rewrote `2 ^ b` inside `Fin (2 ^ b)` (motive error); state the
        product form with `show`.
      - `per * s` and `s * per` are separate `omega` atoms.
      - `dif_pos` is deprecated: add a `vAt_of_lt` lemma proved by `simp`.
31. Stopped at a natural boundary (budget). The truths, the per-phase dooms, the coordinate
    `hround` rows and the `Dp` assembly remain (RESULT S-G1c §4).

## 2026-10-27 (S-G1c, part 2)

32. `FRSoundnessTruths`: `wordK`, `codeK`, `farL`, `decodeL` (`decodeL_spec`), `farL_congr`,
    control `not_farL_nil`; `frEncW` (carried ∩ wins; the node children are windows at 8 and 40),
    `colL_frEncW`, `not_hit_of_not_bad`, `colL_take`. `if_pos`/`dif_pos` are deprecated; use
    `ite_eq_left`/`dite_eq_left`.
33. Stopped at this boundary (budget). Next: (a) cap entries are absorb windows; (b) the cap's own
    absorb; then `A_c` and the remaining truths, the dooms and `Dp`, and the coordinate rows
    (RESULT S-G1c part 2 §4).
