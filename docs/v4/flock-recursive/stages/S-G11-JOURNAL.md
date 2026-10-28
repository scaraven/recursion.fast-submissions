# S-G11 JOURNAL

- Base HEAD `aa805c4`; moved to `549797e` (S-N1 committed, rulings O0/O1) during item 1. Build tree
  `logs/fr-build-SG11` (copy of `fr-build-orch` with `.lake`); `snap.sh` with
  `MINE=<all FRSoundnessFr*>`. Logs `logs/S-G11/`. Every lean/lake call under the 16G scope (12G for
  single files) with `timeout`.

## Item 1: the kind factor (done)

- `FRSoundnessFrW0`: `import FRKindWeight`; new `indKW i t = selOf (KW.ivsQ 16 κ_i) t`,
  `kfT κ es t` (node: `kindFac indKW (fAt es 98 0) ⟨t % 2^16⟩`; leaf: `1`), `kfT_congr`.
  `wrsL`: claim index 1's `eqPts` times `kfT κ es (y / 2^7)`. `wrsL_congr` repaired.
- `FRSoundnessFrRS`: `gL`: claim index 1 times `kfT κ es (u / 2^7)`. `wrsL_eq`, `fipL_eq` (text
  unchanged) build as they were; `gL_congr` repaired; `hfin_RS1` (c = 10) unchanged.
- Proof repairs (claims 0, 2, 3: `if_neg`, `mul_one`): `FrPend` (`trueL_three`), `FrBind`
  (`trueL_zero`), `FrS` (`trueL_two`).
- `FRSoundnessFrZM.trueL_one`: **statement change** — the summand gains `kfT (kindOf es) es t`.
  `zfL_leaf` (text unchanged) gets `kfT` = 1 on a leaf. `pendLc_pendBad` unchanged.
- Build `b4.log`/`b5.log` green (FrRnd + ExtAll, 2,398 jobs on `549797e`).

## Item 2: the node's L (done, except `NodeL.front`, which is item 4's)

- New module `FRSoundnessFrLN` (imports `FRSoundnessFrDF`): `selOf_nonneg`, `selOf_castF`,
  `nodeBK_free`, `nodeKinds_cover`, `nodeKinds_inj`, `selOf_pos`, **`indKW_eq`** (via ℤ:
  `part_one` sums to 1, all ≥ 0, the block's own kind ≥ 1), `ind_succ_eq`, `kfT_node`, `kind_node`,
  `kfT_nodeK`, `zfL_eq`, `tN`, `kindOf_node`, **`trueL_node`**; `PLc`, `pLc_reads`, **`RejLcN`**,
  **`L3BadN`**, **`PendLcN`**, **`oLcV`**; `rejLcN_reads`, `rejLcN_ok`, `l3BadN_reads`,
  `pendLcN_reads`, `l3N_habs`, `l3bN_single` (7·2^128); **`nodeLF`**.
- Controls: `kfT_leaf`, `kfT_node_one` (+), `kfT_node_zero` (−: β = 0 kills hashA's block),
  `not_oLcV`, `not_rejLcN_leaf`.
- `RejLcN` keeps `RejLc2`'s form `Σ_j v′_j M̃_j(r_k)` with `zlmFR` (free = identity); 3.16's walk +
  `free` term is the verifier side, matched in item 4 (`linM_free_mle`).
- Build `b9.log` green.

## Coordinator rulings (mid-pass)

- O0: target `kstate_front` through S-N1's `kstate_front_ofR` (`FRSoundnessExtR`), not
  `kstate_front_of`. O1: `truthE` over `Layout.nodeRows` stays; leave a seam (list the lemmas).

## Item 3: `hW0` (done)

- New module `FRSoundnessFrW0V` (imports `FRSoundnessFrRnd`, `FRSoundnessFrLN`).
  - Spec side: `iota_Phi`, `iota_eqPts_bits`, `mle_eq_pow`, `mle_plain`, `indK`, `iota_kindFac`,
    `indK_bit`, `ptOfK_split`, `mle_kind0` (`rsWeight_kind_eq` at `fs = []`), `kwSL_eq`, `ptOf_sq`,
    `termP`, `termK`, `eqPts_append`, `kwSL_one`, `mle_add'`, `rsRL_length`, `termW`,
    `mle_zipIdx`, `rsPtsL_len`, **`mleW_spec`**, **`wHat0_spec`**.
  - Run side: `map_window`, `map_window'`, `chals_len`, `coordsR_len`, `srcVal_f`, `chalsV`,
    `zSrc_val`, `chalsW`, `chalsW'`, `lcSrc_val`, `shSrc_val`, `eSrc_val`, **`rsPtsV_eq`**,
    **`p0_vals`**, `phStart_10`, **`w0V_run`** (`hW0`'s exact form, for any `impl` whose
    `rsWeight` meets `rsWeightS`).
- Build `b11.log` green.

## Item 5 (partial): `kstate_front_W`

- New module `FRSoundnessFrKS` (imports `FRSoundnessFrW0V`, `FRSoundnessExtR`):
  `kstate_front_ofR` with `hStart := start_run`, `hW0 := w0V_run`, `NodeL := nodeLF + hLcN`.
  Left: `hE`, `hI` (ExtIfaceR), `hOut`, `hfit`, `hLcN`, `hFrontV`. Build `b12.log` green.

## Coordinator heads-up (core PR #20): no final `kstate_front`

- `FRSoundnessFrKS` (the `kstate_front_W` draft) removed from the entry; kept at
  `logs/S-G11/FRSoundnessFrKS.lean.draft` (built green, `b12.log`; axioms in `axioms.log`).
- Checks: `lake build FR` green (2,405 jobs, `build-FR.log`); axioms 76 names clean; source rule
  184 files, 0 findings; name grep clean; sequential profiles `time-*.log`.
- Stopped here: item 4 (`hFrontV`, `NodeL.front` = `AccFront … RejLcN`) handed over in the RESULT §7.
