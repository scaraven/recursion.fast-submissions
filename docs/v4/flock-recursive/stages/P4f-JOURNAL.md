# P4f journal: `FrontHi DFhi` (phases 13 … 25, positions 170 … 331)

Base: HEAD `39fb161` (X4). Build tree `logs/fr-build-P4f` (copy of `fr-build-X4`; `b.sh` logs to
`logs/P4f/`; `MINE.txt`: `FRSoundness4P4fDF FRSoundness4P4fObl FRSoundness4P4fCtrl`). All
lean/lake runs in the 16G (12G single-file) scope under `timeout`. No sub-agents, no commits.

## Layout (`fsStarts4_eq`, `fsRanges4_eq`, `p4b_pos`)

| phase | start | items |
|---|---|---|
| 13 Lr1 | 170 | squeezes 170 … 178 (`(169, 9)`) |
| 14 Lr2 | 179 | absorb 179 (13 → 14), rounds 180 … 212 |
| 15 Lrend | 213 | absorb (14 → 15) |
| 16 Lr3 | 214 | squeeze `κ_L` (15 → 16) |
| 17 E1 | 215 | squeezes 215 … 226 (`(214, 12)`) |
| 18 E2 | 227 | absorb 227 (17 → 18), rounds 228 … 272 |
| 19 Eend | 273 | absorb (18 → 19) |
| 20 E3 | 274 | squeeze `κ_E` (19 → 20) |
| 21 E4 | 275 | absorb 275 (20 → 21), rounds 276 … 324 |
| 22 E4end | 325 | absorb (21 → 22) |
| 23 RS0 | 326 | absorb (22 → 23) |
| 24 RS1 | 327 | squeezes 327 … 330 (`(326, 4)`) |
| 25 B′ | 331 | squeeze `κ′` (24 → 25) |
| P1.0 | 332 | handoff absorb |

## Decisions

- Dooms (3.x's `DF 13 … 25` with X4's background): `bg20X` = far ∨ ¬PubOK4 ∨ PendZ ∨ PendLc ∨
  PendLcN ∨ D2S; `bg12X` = bg20X ∨ nE4; `bg16X` = bg20X ∨ BatBadLr4; `D16X` = bg16X ∨ nE4.
  Phase 13 is `msD (DF4a P4X 12) (bg12X ∨ ZCwLr4) 169 9`: phase 12's `BgA4` (far, public, L rows,
  M rows) goes into Lr1's charge (L rows) and `bg12X` (the rest).
- **Finding F1 (the segment bound).** P4a's `endS4`/`pendS4_pendBad4` (and so `dF4a12_pendBad4`)
  assume `lastL es < 2^nbC` on a segment (`V_A`'s `n ≤ cap`), which no final of the segment program
  asserts. At RS0 the doom must turn `D2S` into `PendBad4` on every log (a segment log with
  `n > cap` whose S2 claim is false would otherwise escape at RS0 with no charge). The bound is
  not needed: in `final_seg` only the end term `eq(τ‖0, L)·eq(r‖0, L+1)` uses it, and for
  `L ≥ 2^nb` both sides of it are `0` (`eqAtR_padN` at a bit past `nb`). New: `final_segU`
  (`Lb < 2^18`, from `lastL_lt`), `wSumSegU`, `endS4U`, `pendS4U` in `FRSoundness4P4fDF`.
  P4a's statements unchanged.

## Log

1. `FRSoundness4P4fDF`: `final_segU` (copy of `final_seg`, only `hc` changed: `eqAtR_padN` at
   `Lb < 2^18`, both branches of `Lb + 1 < 2^nb`), `wSumSegU`, `endS4U`, `pendS4U`; the parts
   `far0X`, `PubX`, `bg20X`, `bg12X`, `bg16X`, `D16X`, `DRS0X`/`DRS1X`/`DBX`; **`DFhi`**; reads
   (`rd_*`); **`dPend_X`** (phase 22 → `DPend4` with `okX`: `pendZ4_pendBad4`, `pendLc4_pendBad4`
   at `segInd_zlm4`, `pendLcN4_pendBad4` at `kfInd4`, `pendS4U` at `hNS4`, `pendE4_pendBad4`);
   **`dfhi_ss`** (`SameStab4 (phStart4 k + 1) (DFhi k)`, 13 ≤ k ≤ 25: reads lemmas for the
   backgrounds, ends, batches, RS; the log form `D3G_same`, `TEb4_same`/`c4E4_agree`,
   `D2_congrL`, `zCG_same` for the rounds and E's pending claim; `ss_msD4` for Lr1/E1/RS1).
2. `FRSoundness4P4fObl`: one certificate `frontClsHi_check` (`decide +kernel` over
   `(fsItems4.take 332).zipIdx`, positions `< 170` passed), `ph_checkHi` (phases at the 10
   boundary points, rounds phases' starts/ends), `phOf4_eq` inside the rounds phases;
   `fsRanges_hi`; `ms_hi`, `habs_hi`, `hsingle_hi`, `hfin_hi` (via `hfin_frame`: escape ⇒ entry
   doom ∧ ¬ final, background read before the phase), `handoff_hi` (`ip_W0X`: `trueSum_tabs`,
   `fTab_F`, `nrP0`), `hstab_hi`, `chain_hi`; **`frontHi_X`**, `frontObl_P4f`,
   `frontChainStab_P4f`, **`ks_rev4F`**, **`certificate_rev4F`**.
   - E3's count needed `convert … using 3` (the frame's `DecidablePred` for a λ-`U` differs from
     `e4_single_batchE`'s; a direct `le_trans` hit max recursion), as P4a's L3β.
   - `fsRanges_hi` by `omega` over the 15-way disjunction cost 1.13 s of tactic time; split by
     `rcases` first (now negligible).
3. `FRSoundness4P4fCtrl`: controls.
4. Checks: `b.sh FR FRSoundness4P4fCtrl` green, 2,536 jobs; axioms (83 declarations) within the
   three; source rule 319 files, 0 findings; sequential profiles.
