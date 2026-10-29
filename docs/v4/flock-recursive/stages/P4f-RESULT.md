# P4f RESULT: X4's residual 1 discharged: `frontHi_X : FrontHi DFhi`

- **Base.** HEAD `39fb161` (X4). **Build tree** `logs/fr-build-P4f` (a copy of `fr-build-X4`;
  `b.sh` logs to `logs/P4f/`; `MINE.txt` lists the three new modules; `logs/org20`). Journal:
  `P4f-JOURNAL.md`.
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under
  `timeout`. No sub-agents. Nothing committed. Only new `FRSoundness4P4f*` modules were written. No
  existing module was edited and no statement was changed. Every new name lives in `FR.Snd.P4f`
  (grepped first: no `P4f` namespace or module existed).

**Imports for `FR.lean`:** add `import FRSoundness4P4fCtrl`. It pulls `P4fObl`, which pulls `P4fDF`,
`XFinal` and `XFront`.

## Status

| Item | State |
|---|---|
| 1. Dooms for phases 13 … 25 carrying `BgA4` | **Done**: `DFhi` (`FRSoundness4P4fDF`) |
| 2. `FrontObl`'s fields at positions ≥ 170 | **Done**: `ms_hi`, `habs_hi`, `handoff_hi`, `hsingle_hi`, `hfin_hi`, `hstab_hi`, `chain_hi`, from one checked classification (`frontClsHi_check`) |
| 3. `frontHi_X : X4.FrontHi DFhi` | **Done**, with no hypotheses. `frontObl_P4f : T4.FrontObl RejFX (DFX DFhi) W0X c0X` and `frontChainStab_P4f` hold unconditionally. `ks_rev4F` and `certificate_rev4F` are X4's theorems with `hHi` gone. |

**Checks:**
- `lake build FR FRSoundness4P4fCtrl`: **green, 2,536 jobs** (`logs/P4f/build-final.log`).
- **Axioms**: all 83 declarations of the three modules use only `propext`, `Classical.choice`,
  `Quot.sound`, and none uses `sorryAx` (`logs/fr-build-P4f/ax/AxP4f.lean`, `logs/P4f/axioms.log`).
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 319
  files, 0 findings (`logs/P4f/source-rule.log`).

## 1. What was built (`loc.py`, `logs/P4f/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4P4fDF` | 356 / 261 / 28 | **F1** (§4): `final_segU`, `wSumSegU`, `endS4U`, `pendS4U`. The parts: `far0X`, `PubX`, **`bg20X`**, **`bg12X`**, **`bg16X`**, **`D16X`**, `DRS0X`/`DRS1X`/`DBX`. **`DFhi`**. Reads: `rd_far0X`, `rd_PubX`, `rd_bg20X`, `rd_nE4X`, `rd_bg12X`, `rd_batLr`, `rd_bg16X`, `rd_D16X`, `rd_zcwLr`, `rd_zcwE`, `rd_endLr`, `rd_endE`, `rd_DRS0X`/`rd_DRS1X`/`rd_DBX`. **`dPend_X`**. `phStart_hi`. The `SameStab4` lemmas `ss_D3Lr4`, `ss_D3E4`, `ss_batE4`, `ss_D4E4`, `ss_pendE4`, `ss_df12` and **`dfhi_ss`**. |
| `FRSoundness4P4fObl` | 485 / 380 / 28 | `absPtsHi`, `sqPtsHi`, `rndPhHi`, `rndClsHi`, `frontClsHi`. **`frontClsHi_check`**, `ph_checkHi`, `frontClsHi_of`, `pt_phHi`, `rnd_phHi`, `abs_clsHi`, `sq_clsHi`, `fsRanges_hi`, `phOf4_at`, `ph_msHi`. **`ms_hi`**, **`habs_hi`**, **`hsingle_hi`**. **`hfin_frame`**, `df12_split`, **`hfin_hi`**. `nrP0`, `locX`, `ip_W0X`, **`handoff_hi`**. `len_stabExt`, **`hstab_hi`**, **`chain_hi`**. **`frontHi_X`**, `frontObl_P4f`, `frontChainStab_P4f`, **`ks_rev4F`**, **`certificate_rev4F`**. |
| `FRSoundness4P4fCtrl` | 81 / 41 / 12 | controls (§5) |
| **total** | 922 / 682 / 68 | |

## 2. The dooms

These are 3.x's `DF 13 … 25` (`FRSoundnessFrDF`) at X4's background. Phase 12's doom
`DF4a P4X 12 = (BgA4 ∨ PendZ ∨ PendLc ∨ PendLcN) ∨ D2S` carries `BgA4` (far, public cells, L rows,
M rows). Each part of it is reduced at one place:

- Lr1 reduces the L rows: Lr1's charge.
- E1 reduces the M rows: E1's charge.
- Lr3 and E3 reduce Lr's batch.
- RS0 reduces the pending claims: they become `DPend4` and then `DRS0_4`.
- B′ keeps far and the public cells until `DB4`, which becomes P1.0's `D1 0`.

```lean
def bg20X L es := far0X L es ∨ ¬ PubX L es ∨ PendZ zw ∨ PendLc M zw ∨ PendLcN M zw ∨ D2S wN zw  -- at P4X
def bg12X L es := bg20X L es ∨ nE4 src4 srcE4 L es
def bg16X L es := bg20X L es ∨ BatBadLr4 src4 srcL4 L es
def D16X  L es := bg16X L es ∨ nE4 src4 srcE4 L es
noncomputable def DFhi : ℕ → Log → Log → Prop
  | 13 => msD (P4a.DF4a X4.P4X 12) (bg12X ∨ ZCwLr4) 169 9      | 14 => bg12X ∨ D3Lr4
  | 15 => bg12X ∨ EndBadLr4                                     | 16 => D16X
  | 17 => msD D16X (bg16X ∨ ZCwE4) 214 12                       | 18 => bg16X ∨ D3E4
  | 19 => bg16X ∨ EndBadE4                                      | 20 => bg20X ∨ BatBadE4
  | 21 => bg20X ∨ D4E4                                          | 22 => bg20X ∨ PendE4
  | 23 => DRS0_4 src4 kf4 far0X PubX  | 24 => msD DRS0X DRS1X 326 4  | 25 => DB4 src4 kf4 cells4 far0X
  | _ => False
```

`far0X` is `BgA4`'s first disjunct and `PubX = PubOK4 src4 cells4`; both read before position 3.
RS0's bindings are X4's `okX`.

## 3. The obligations (positions 170 … 331)

| Position | Item | Field | Lemma |
|---|---|---|---|
| 170 … 178 (Lr1), 215 … 226 (E1), 327 … 330 (RS1) | multi-squeeze | `ms`, `hfin` | `msD` by definition. Charge (`hfin_frame`): `lr4_zc_count` (≤ 17/2^128), `e4_zc_count` (≤ 23/2^128), `rs1_hfin4` (≤ 10/2^128), each ≤ `deltaR` by `coord_le_deltaR` |
| 179, 227 | absorb | `habs` | `lr4_habs_outer`, `e4_habs_outer` |
| 180 … 212, 228 … 272, 276 … 324 | rounds | `habs`/`hsingle` | `*_outer_append`/`e4_inner_appendE`; `lr4_single_outer`, `e4_single_outer` (3·2^128), `e4_single_innerE` (2·2^128, from `¬ RejInE4`) |
| 213, 273 | absorb | `habs` | `lr4_habs_end`, `e4_habs_end` (`RejEndLr4`/`RejEndE4` ⊂ `RejF4b`) |
| 214 (Lr3), 274 (E3) | squeeze | `hsingle` | `lr4_single_batch` (2·2^128), `e4_single_batchE` (3·2^128) |
| 275 | absorb | `habs` | `e4_habs_innerE` |
| 325 | absorb | `habs` | `e4_habs_end4` (`RejFinE4` ⊂ `RejF4b` or `PendE4`) |
| 326 | absorb | `habs` | `dPend_X` then `habs_RS0_4` at `okReads_X` (`RejRS4 okX` ⊂ `RejF4b` or `DRS0_4`) |
| 331 (B′) | squeeze | `hsingle` | `single_B4` at `hcells4P4b` (10·2^128) |
| 332 | absorb | `handoff` | `DB4` → T4's `D1 W0X c0X 0`: `closeP_zero`, and on a close word `ip_W0X` (`lvT`, `trueSum_tabs`, `fTab_F`, `nrP0`) with `locX`/`lvT_same` across the absorb |
| phases 13 … 25 | — | `hstab`, `chain` | `dfhi_ss` on `T4.same_stabX`/`T4.same_chain` |

The single squeezes and the rounds frame through P4a's `card_frame2_4`, with the background
reading before the squeeze. The largest count is E3's: 3·2^128 ≤ 239·2^128.

**The classification** is one `decide +kernel` certificate, `frontClsHi_check`, over
`(fsItems4.take 332).zipIdx`. Positions below 170 pass trivially. Every other absorb is a boundary
point (`absPtsHi`) or a round absorb (`rndPhHi`, even offset). Every other single squeeze is a
boundary point (`sqPtsHi`) or a round squeeze (odd offset).

The phases come from two sources:
- at the 10 boundary points, the small `ph_checkHi`;
- inside the rounds phases, `phOf4_eq` from their starts.

No position is decided on its own.

**`ks_rev4F`'s hypotheses.** These are X4's `ks_rev4` without `hHi`:
- the definitional ones: `hV`, `hq`, `hE`, `hε`;
- residual 2: `hRun : X4.RunFacts4 (VsegC impl₀) (VnodeC (implN4F base) cells4) vk`;
- residuals 3–4: `I`, `rd`, `hI`, `hRes`;
- residual 5: `D : NodeDec4 nd`;
- residual 6: `hL`, which is stated at `X4.GoodX DFhi`.

`certificate_rev4F` additionally takes `hext`, `hfuel`, `hnd` (residual 7), `hR`, `hC` (residual 8)
and `hδ` (residual 9). It no longer takes `hHi`.

## 4. Findings and deviations

- **F1. A segment's `n ≤ cap` was needed at RS0, and no final asserts it. It is not needed.** The
  pending S claim (`D2S`, part of `bg20X`) must become RS0's `PendBad4` on every log.
  - P4a's `endS4`, `pendS4_pendBad4` and `dF4a12_pendBad4` assume `lastL es < 2^nbC` on a
    segment. That is `V_A`'s `n ≤ cap`, and no final of the segment program asserts it (P4a F1/D4).
  - With that assumption kept, consider a segment log with `n > cap` whose S2 claim is false. It
    would leave RS0 neither rejected nor doomed. Its doom would also have to be carried from Lr1
    on, or Lr1's charge would be 1.
  - The bound is used in only one place in `final_seg`: the end term
    `eq(τ‖0, L)·eq(r‖0, L+1)`. For `2^nb ≤ L < 2^18` both sides of that term are `0`
    (`eqAtR_padN` at a set bit past `nb`; `eqAtR_pad_past`). So `final_segU`, `wSumSegU`,
    `endS4U` and `pendS4U` hold with only `L < 2^18`, which is `lastL_lt`.
  - P4a's statements are unchanged. P4a may want to restate `endS4`, `pendS4_pendBad4` and
    `dF4a12_pendBad4` without `hL` (§6).
- **F2. No value is asserted by no final.** Every check `FrontHi` reads is in X4's `RejF4b`:
  - `RejEndLr4` at 213 and `RejEndE4` at 273;
  - `RejInE4` in E4's rounds;
  - `RejFinE4` at 325;
  - `RejRS4 okX` at 326.

  The background is reduced only through P4b's units and the bindings in `okX`. `hcells4P4b`
  (nine public cells inside level 0) is S-E's theorem.
- **D1. Phase 13 is `msD` over `DF4a P4X 12` itself**, which is not in the form `Bg ∨ U`. So
  `hfin` goes through a new frame, `hfin_frame` (entry ⇒ `Bg ∨ U`, `Bg ∨ U'` ⇒ final), instead of
  T4's `esc_msD_frame`, which needs an equation. `df12_split` splits phase 12's doom.
- **D2. E3's count uses `convert … using 3`**, as P4a's L3β does: the frame's `DecidablePred`
  instance for a λ-bound `U` is not syntactically `e4_single_batchE`'s, and a direct `le_trans`
  hit the recursion limit.

## 5. Controls (`FRSoundness4P4fCtrl`, and the main theorems)

| Definition | Positive | Negative |
|---|---|---|
| `DFhi` | `DFhi_of_far` (a far word dooms phases 14 … 25 except E1 and RS1, the `msD` phases), `DFhi13_of_far` (after Lr1's last answer) | `DFhi_out` (phases 12 and 26 are `False`), `not_DFhi25_true` (a close word with the true claim clears B′) |
| `bg12X`, `bg16X` | `bg12X_of_nE`, `bg16X_of_bat` | `bg12X_seg`, `bg16X_seg` (on a segment they are `bg20X`) |
| `frontClsHi` | `frontClsHi_pos` (180 squeeze, 181 absorb, 328 squeeze) | `frontClsHi_neg` (213 is no squeeze class, 214 no absorb class) |
| F1 (`final_segU`) | `eqAtR_pad_past` (past the blocks the end term is 0) | `eqAtR_pad_in` (inside the blocks it is `eq(τ, L)`) |
| `FrontHi DFhi` | `frontHi_X`, `frontObl_P4f`, `ks_rev4F`, `certificate_rev4F` | — (its content is `T4.FrontObl`; vacuous dooms fail Lr1's charge) |

## 6. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `logs/P4f/prof-*.log`)

| Module | wall (import ≈ 3.9–4.2 s) | type checking | tactic execution | max RSS |
|---|---|---|---|---|
| `FRSoundness4P4fDF` | 8.8 s | 0.34 s | 0.66 s | 2.95 GB |
| `FRSoundness4P4fObl` | 10.6 s | 1.20 s (`frontClsHi_check` ≈ 0.6 s) | 0.75 s | 2.98 GB |
| `FRSoundness4P4fCtrl` | 7.0 s | 0.05 s | 0.11 s | 2.94 GB |

Two `decide +kernel` calls are certificates: `frontClsHi_check` (332 items) and `ph_checkHi` (13
phase values). The controls' `decide` runs on `frontClsHi` at five positions. No `trueSum` is
evaluated at a concrete size.

## 7. Open questions

1. F1: should P4a's `endS4`, `pendS4_pendBad4`, `dF4a12_pendBad4` and `final_seg` be restated
   without the segment bound, by moving `final_segU`/`endS4U` into P4a's modules? The front is
   complete as it stands, so this is a cleanup.
2. With residual 1 gone, `frontObl_X`/`ks_rev4` could take `DFhi` concretely. Should
   `ks_rev4F`/`certificate_rev4F` replace X4's `ks_rev4`/`certificate_rev4` as S-I's entry points?
