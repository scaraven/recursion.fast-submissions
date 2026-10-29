# INT-10 RESULT: the size/cap interface amendment (R4i's F1), `SegOut4` discharged

HEAD `7292eab` (R4i). Build tree `logs/fr-build-INT10` (a copy of `fr-build-R4i`; `logs/org20`;
`MINE.txt` = the five edited modules plus `XFinal`/`P4fObl`, unchanged). Every lean/lake command
ran in the 16G scope (12G for single files) under `timeout`. No sub-agents. Nothing committed.

## Ruling applied (orchestrator): amend the interfaces, not the programs

A segment is only ever verified inside `V_A`, and `V_A` checks `π.size = 48 + k · segSize` and
`1 ≤ n ≤ cap` before it runs any segment program. Statement changes, each justified by that ruling:

| Declaration | Change |
|---|---|
| `Rev4.SegSoundLog` (`FRSoundness4Agg`) | gains `π.size = piSizeOf seq4 →` (after `segView π = some v`, before `1 ≤ v.n`) |
| `Rev4.VA_sound_log` | also returns `π.size = 48 + (byteAt π 1).toNat * segSize` (`VAwith`'s size check) |
| `Rev4.VA_extract_log`, `Rev4.VA_rel_log` | `segSize` fixed at `piSizeOf seq4` (it is the size `SegSoundLog` now names); the size is supplied by `Snd.R4.piSize_aggSegs`. `V4_agg_extract_log` is unchanged (it already used `piSizeOf seq4`) |
| `X4.RunFacts4.seg` (`FRSoundness4XLaws`) | gains `π.size = piSizeOf seq4 → v.n ≤ v.kind.cap →`; it is now literally R4i's `RunFacts4S` (`runFacts4S_seg`) |
| `X4.segSound_X` | statement unchanged; it passes `hπ` and `hcap` to `RunFacts4.seg` |

`FRSoundness4Agg` now imports `FRSoundness4R4Link` (for `piSize_aggSegs`; R4Link imports only
`FRVerifierC4`, already in every downstream closure; no cycle).

## Proofs repaired / added

- `FRSoundness4XCtrl`: `runFacts4_false` (two more binders).
- `FRSoundness4XRun`: **`runFacts4H_C`** (unconditional `RunFacts4` at the concrete ops:
  `⟨runFacts4S_C, runFacts4_node_C⟩`); `runFacts4_C` keeps its statement (`_hO` now unused);
  `runFacts4S_seg`.
- `FRSoundness4XRunG`: **`ks_rev4H`**, **`Resid4H`** (= `Resid4G` minus `out`), `resid4_of_H`,
  `resid4H_of_G`, **`certificate_rev4H`**. `ks_rev4G`, `Resid4G`, `certificate_rev4G`, `SegOut4`
  are kept with their statements (S-N2's untracked `FRNodeSound4K` uses them) and now follow from
  the `H` forms. `FRSoundness4XFinal`, `FRSoundness4P4f*`, `Frame`, `TailLig`, `FRX4Ext`: no edit
  needed (they take `RunFacts4`/`SegSoundLog` as hypotheses or use `V4_agg_extract_log`).

**`ks_rev4H`'s remaining hypotheses**: definitional `hV` (concrete ops), `hq`, `hE`, `hε`;
residuals 3–4 (S-N2) `I`, `rd`, `hI`, `hRes`; residual 5 (S-H4) `D`; residual 6 (S-H4) `hL`.
**`certificate_rev4H`**: in addition `hext`, `hfuel` (definitional), `hnd` (residual 7, S-H4),
`hR : ∀ vk, Resid4H …` (= residuals 3–4 and 6 per `vk`), `hC` (completeness) and `hδ` (S-I).
No `SegOut4`, no `RunFacts4`.

## Controls (`FRSoundness4Agg`)

| Definition | Positive | Negative |
|---|---|---|
| `SegSoundLog` (amended) | `segSoundLog_lucky`, `segSoundLog_off` | `not_segSoundLog_true` (now on `badSegP`: `badSeg` zero-padded to `piSizeOf seq4` bytes, same view, `badSegP_view`) |
| the size hypothesis | `segSoundLog_off`: `VsegOff` (accepts exactly the proofs of another size) meets `SegSoundLog` | `not_segSoundLog0_off`: `VsegOff` fails the size-free form `SegSoundLog0` (the 96-byte `badSeg`, false chain `0 → 0`); `VA_off_reject`: `V_A` at `piSizeOf seq4` never accepts with `VsegOff`. So the size-free form asks for runs `V_A` never makes; the amended one is what `V_A` needs |

New helpers: `padTo`, `padTo_size`, `byteAt_padTo`, `badSegP`, `SegSoundLog0` (control only), `VsegOff`.

## Checks

- `lake build FR FRSoundness4XRunG FRSoundness4R4Full FRSoundness4R4ColsCtrl FRSoundness4R4FrCtrl
  FRSoundness4R4FrCtrlB FRSoundness4R4Tail FRSoundness4P4fCtrl FRSoundness4XCtrl`: **green, 2,546
  jobs** (`logs/INT10/build-final.log`).
- Compatibility: S-N2's untracked `FRNodeSound4K` (with its `FRNodeRead4*`/`FRNodeSound4*`) builds
  against the amended modules (`logs/INT10/build-sn2-compat.log`, 2,537 jobs); not part of the tree.
- **Axioms** (`logs/fr-build-INT10/ax/AxINT10.lean`, `logs/INT10/axioms.log`): all 64 theorems of the
  five edited modules within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`logs/org20/scripts/source-rule.py`): 333 files, 0 findings (`logs/INT10/source-rule.log`).
- Times (sequential, one core, `logs/INT10/prof-*.log`): `FRSoundness4Agg` 18.5 s wall, type
  checking 1.15 s (its 9.8 s of `contradiction`/`assumption` tactic time is pre-existing: HEAD's Agg
  shows the same entries); `FRSoundness4XRunG` 7.6 s wall.

## Lines (`loc.py`: total / code / thm, HEAD → now)

| Module | HEAD | now |
|---|---|---|
| `FRSoundness4Agg` | 213 / 141 / 12 | 298 / 194 / 18 |
| `FRSoundness4XRun` | 293 / 216 / 17 | 300 / 216 / 19 |
| `FRSoundness4XRunG` | 106 / 66 / 9 | 161 / 105 / 13 |
| `FRSoundness4XLaws`, `FRSoundness4XCtrl` | | ±3 lines (binders, docstring) |

## Open items

1. S-I: switch to `certificate_rev4H` (`hR : ∀ vk, Resid4H …`); S-N2: `ks_rev4GH`/`Resid4GH` can drop
   `hO`/`out` by calling `ks_rev4H`/`certificate_rev4H`. After that, `SegOut4`, `ks_rev4G`,
   `Resid4G`, `certificate_rev4G`, `runFacts4_C` can be deleted.
2. Blueprint: Appendix A's `SegSoundLog`/`RunFacts4` should record the size (and, for `RunFacts4.seg`,
   the cap) hypothesis.
