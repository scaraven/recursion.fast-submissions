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
