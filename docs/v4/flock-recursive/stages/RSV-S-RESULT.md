# RSV-S RESULT: the reserve's soundness chain in RSV2's stacked form (partial; handover)

Track RSV-S, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `face798`.
Build tree `logs/fr-build-RSVS` (a copy of `fr-build-A3b`, re-snapshotted on HEAD by `mysnap.sh`;
`mymods.txt` links every `FRSoundness4*` module to the worktree). Logs `logs/RSVS/`. Journal
`stages/RSV-S-JOURNAL.md`. Spec: `RSV-V2-RESULT.md` §8, `RSV-V-RESULT.md` §5, `design/RSV2.md` §5,
`reviews/RSV2-review.md`, `A3p-RESULT.md` Run 2. No sub-agents and nothing committed.

**This is a handover, not a finished stage.** The build is not green. §5 lists what is open, in the
order to do it.

## 0. Summary

- **Done (kernel-checked in the build tree):**
  - **E-phase restated in RSV2's stacked form** (`FRSoundness4P4bNames`, `FRSoundness4P4bE`), with
    the doom chain carried through the front (`FRSoundness4P4fDF`, `FRSoundness4P4fObl`,
    `FRSoundness4XFront` build: `logs/RSVS/b-p4f.log`):
    - E1's escape: `ZCwE4` is `F̃(τ) + η·D ≠ 0`; the entry doom is `nE4 ∨ ChildBad4`; the charge is
      `≤ 24/2^128` for every kind (`e4_zc_count`), with the review's form for `N2` (E1's table on 24
      coordinates, coordinate 22 unread: the table is constant in it).
    - E2 is a zerocheck plus the linear claim: six tables (`T3E4`), `outerExprR` (degree 3);
      `trueSum_T3E4` (`= F̃(τ) + η·D`), `final_T3E4`, `e4_habs_end` with a wrong **quadruple**
      `(â, b̂, ĉ, m̂*)`.
    - E3 batches five claims (degree 4): `e4_single_batchE ≤ 4·2^128` (RSV2's row: `8/2^128`).
    - E4: four tables (`TEb4`), `innerExprR` (degree 2), `final_TEb4`, `e4_habs_end4` against the
      new `RejFinE4` (iv″).
    - New `FRSoundness4RsvMLE`: **the constant-extension lemma** and the fixed evaluation in one
      (`mle_eq_hiPt`, `matMLE_hiRow`, `matMLE_hiCol`), E1's 24-coordinate table (`zcT`, `mle_zcT`,
      `zcT_ne`).
  - **Three of the seven red declarations fixed**: `FRSoundness4Qry.noAsk_gFinE`, `noAsk_gFinB'`,
    `noAsk_gFinPf` (proofs only).
  - **`relE4`, `vStar4` restated** (RSV-V §5's false-but-compiling definitions): with the reserve,
    `relE4` is (v) ∧ the zero conjuncts ∧ (ii″) ∧ (iii″) ∧ (iv″) (the claim's `X`, the one stacked
    `evalM` at the 32/25-entry points); `vStar4` gains `κ′^{11}·Σ_{i<60} κ′^i v_i` where `rsv`.
    Without the reserve both are the old relations (`relE4o`, `vStar4o`), and `flag_gFinE0`,
    `flag_gFinB'o` prove those cases.
  - `fsMsgs4_ends` restated (1,008 / 112).
  - Source rule: 405 files, 0 findings (`logs/RSVS/source-rule.log`).
- **Open (§5):** the reserve branches of `flag_gFinE` and `flag_gFinB'`; everything downstream of
  `R4Fin` (the R4 discharges against the new checks, `gFinPf_reloc`/`relPf4`/`PfFin`, `FrRS`,
  `Start`); B′ at 69 cells; the chain lemma `gap4Imp_of_rsv` and `StmtN4`; the four controls; the
  certificate build.

## 1. What was built (code lines, the core's `loc.py`, HEAD → now)

| Module | Change | code |
|---|---|---|
| `FRSoundness4RsvMLE` (new) | `hiPt`, `lowA`, `hiPt_self`, `eq_hiPt_split`, **`mle_eq_hiPt`**, `matMLE_row`/`_col`, **`matMLE_hiRow`/`_hiCol`**, `mle_add'`/`mle_sub'`, `mle_const`, `mle_hiTab`, `mle_coord`, **`zcT`**, `mle_zcT`, **`zcT_ne`**, `hiPt_ctl` | — → 129 |
| `FRSoundness4P4bNames` | the child claim (`pxL`, `pyL`, `sL`, `xL`, `mStL`, `etaL`), **`mStack`**, **`truthChild4`**, `dChild`, **`ChildBad4`**, `xHat`, `outerExprR`, `innerExprR`; E restated: `ZCwE4`, `T3E4`, `D3E4`, `mHatT`, `EndBadE4`, `c4E4`, `cTab4`, `TEb4`, `BatBadE4`, `D2Eb4`, `RejEndE4`, `RejFinE4` | 157 → 204 |
| `FRSoundness4P4bE` | `child_agree`, `etaL_agree`, `dChild_agree`, `xHat_agree`, `truthChild_iff`, `mle_mStack_row`/`_col`; `zcE4`, `e4_zc_count`, `T3E4_same`/`_local`/`_size`/`_get`, `mle_yTab`, `trueSum_T3E4`, `final_T3E4`, `e4_habs_outer`, `e4_single_outer`, `e4_outer_append`, `e4_habs_end`, `zcwE4_reads`, `endBadE4_reads`, `D3E4_same`, `rejEndE4_agree`, `rejEndE4_log`; `cTab4_agree`, `c4E4_agree`, `TEb4_*`, `sum_cTab4`, `trueSum_TEb4`, `batch_count5`, `single_batchE_at`, `e4_single_batchE`, the E4 rounds, `final_TEb4`, `e4_habs_end4`, `rejFinE4_log` | 401 → 691 |
| `FRSoundness4P4fDF` | `D16X` gains `ChildBad4`; `rd_childX`, `rd_D16X`; `ss_D3E4`, `rd_zcwE`, `rd_endE` re-pointed | 261 → 264 |
| `FRSoundness4P4fObl` | `hsingle_hi` (Lr3's frame, E3's `4·2^128`), `hfin_hi`'s E1 case (`nE4 ∨ ChildBad4`, `24/2^128`) | 380 → 380 |
| `FRSoundness4R4Fin` | `relE4o` (old), `rsvPx4`/`rsvPy4`/`rsvS4`, `relE4` (reserve branch), `rd_getD_toF`, `flag_gFinE0` (old proof), `flag_gFinE` (reserve case **open**); `vStar4o`, `vStar4`, `flag_gFinB'o` (old proof), `flag_gFinB'` (reserve case **open**) | 226 → 308 |
| `FRSoundness4R4FrE` | `fsMsgs4_ends` (1,008 / 112); `hin_E` gains `η` and register `0` | 453 → 455 |
| `FRSoundness4Qry` | `noAsk_gFinE0`, `noAsk_gFinE`, `noAsk_gFinB'`, `noAsk_gFinPf` | 173 → 180 |

## 2. Every statement change, with its reason

**Definitions whose meaning changed** (all forced by RSV2's V side, which RSV-V2 built):
- `P4b.ZCwE4`: was `ZCwG` (the residual's extension at `τ`); now `F̃(τ) + η·D ≠ 0`, `D` the child
  claim's defect. RSV2 §2.6: E1's 24 coordinates `τ ‖ η` test one multilinear table.
- `P4b.D3E4`: E2's tables gain `η·eq(p_x, ·)` and `Y(x) = Σ_i s_i M̃_i(x ‖ p_x[e2R,23), p_y) − X`;
  the summand `outerExprR` (degree 3).
- `P4b.EndBadE4`: a wrong quadruple (`(â, b̂, ĉ)` or `m̂*` against `mHatT`).
- `P4b.RejEndE4`: (ii″) `clR = eq(τ, r)(âb̂ + ĉ) + η·eq(p_x, r)·(m̂* − X)` (V computes `+ X`; equal in
  characteristic 2).
- `P4b.c4E4` gains `κ_E⁴·m̂*`; `P4b.TEb4` gains `κ_E⁴·eq(p_y, ·)` and `C(y)`; `P4b.BatBadE4`,
  `D2Eb4` over `innerExprR`.
- `P4b.RejFinE4`: (iv″) adds `κ_E⁴·eq(p_y, r′)·M̃*(x̂, r′ ‖ p_y[ncR, 25))`.
- New: `P4b.truthChild4`, `ChildBad4`, `mStack`, `mHatT`, `xHat`.
- `P4f.D16X` gains `ChildBad4` (the doom E1 reduces).
- `R4.relE4`: the reserve branch (RSV2 §2.2) as V computes it; the old relation is `relE4o`.
- `R4.vStar4`: the reserve term where `rsvOps ∧ rsv`; the old value is `vStar4o`.

**Theorems restated:**

| Theorem | Change | Reason |
|---|---|---|
| `P4b.e4_zc_count` | hypothesis `nE4 ∨ ChildBad4`; bound `24/2^128` (was `e2R κ/2^128`) | E1's table has 24 variables for every kind (review finding 5) |
| `P4b.e4_single_batchE` | bound `4·2^128` (was `3·2^128`) | five claims, degree 4 in `κ_E` (review finding 8) |
| `P4b.e4_habs_end` | wrong quadruple | `m̂*` joins Eend's message |
| `P4b.e4_habs_end4`, `rejFinE4_log`, `rejEndE4_log`, `D4E4_reads`, … | same texts over the new names | — |
| `R4.flag_gFinB'` | the export is `vStar4o` (was `vStar4`) | `finB′` exports its own `v*₀` (`b + 30`) in both cases; only the assert sees the reserve |
| `R4.flag_gFinE` | `hin` gains `(coordsR fi "E1").getD 23 0` (`η`) and register `0` | the reserve block reads them |
| `R4.fsMsgs4_ends` | 1,008 and 112 | RSV2's `fLrEnd`, `fEEnd` |

`εR = 15/2^124` and `claim.json` are untouched. E1's row is `24/2^128`, E3's `4·2^128 ≤ 239·2^128`; both
inside `deltaR` (`coord_le_deltaR`).

## 3. Build, checks

- `lake build FRSoundness4P4fObl FRSoundness4XFront` is **green** (2,419 jobs, `logs/RSVS/b-p4f.log`):
  the E-phase restatement carries through the front's obligations.
- `FRSoundness4R4Fin`: two open goals (the reserve branches), nothing else red (`chk` log in the build
  tree). Downstream scan: §4.
- The decoder's merge breaks (another track's) are sorried in the build tree only
  (`fr-build-RSVS/patchdec.py`): `FRXChain4.fsMsgs4_zero`, `fsMsgs4_length`, `fsMsgs4_items`,
  `fsMsgs4_ctl`; `FRXDec4Levels.cost_decLevels4`.
- Source rule: 0 findings. No `sorry` in the worktree.
- **Build-tree state for the next agent:** `fr-build-RSVS/src/FRSoundness4R4Fin.lean` is a sorried
  *copy* (the scan's); run `mysnap.sh` to relink the worktree's modules before building.
- Axioms for `certified`: not checked (the tree is not green).

## 4. The red set now

Scan `logs/RSVS/b-scan2.log`: the build tree with the two open goals of `R4Fin` sorried (build tree
only), `lake build FR Solution FRSubmission4Cert FRSoundness4XCtrl FRNodeSound4Ctrl
FRSoundness4TailShift`.

- **This track's** (all from the restatement; §5 items 1–3):
  - `FRSoundness4R4Fin.flag_gFinE`, `flag_gFinB'`: the reserve branch (one open goal each).
  - `FRSoundness4R4FrE`: `e_end4`, `not_rejEndE4_node`, `e_in4`, `not_rejInE4_node`, `e_fin4`,
    `not_rejFinE4_node` (they target the new `RejEndE4`/`c4E4`/`RejFinE4`; `relE4_of_accept` builds
    after `hin_E` gained `η` and register `0`).
  - Not reached behind `FrE` (RSV-V §5's list, still to restate): `FrRS.relE4_of_fields`,
    `Start.start4_of_fields`/`start4_node`, `PfFlag.gFinPfR`/`gFinPf_reloc`/`relPf4`,
    `PfFin.relPf4_of_fields`/`fin4_of_fields`/`hz_of_fields`, and the controls `FrCtrl.relE4_fin3P`,
    `FinCtrl.relB4_fin3P` (these two should hold: `fin3P` has the reserve off).
- **Not this track's** (main's merge; sorried in the build tree only, `patchdec.py`):
  `FRXChain4.fsMsgs4_zero`, `fsMsgs4_length`, `fsMsgs4_items`, `fsMsgs4_ctl`;
  `FRXDec4Levels.cost_decLevels4`; `FRXDec4F0.fmt4_vals`, `lv_cap4`; `FRNodeRun4S.execA_proto`,
  `gap4Imp_of_run` (B3's); `FRXOut4` (lines 318, 367).

Lake build times of the touched modules (`b-p4f.log`, `b-scan2.log`; not the sequential profile the
rules ask for, which waits for a green tree): `RsvMLE` 4.4 s, `P4bNames` 4.9 s, `P4bRows` 5.7 s, `P4bE`
10 s, `P4fDF` 6.7 s, `P4fObl` 7.5 s, `XFront` 6.7 s, `R4Fin` 7.5 s.

## 5. Open, in order (the handover)

1. **`flag_gFinE`, reserve branch.** One `simp` over the expanded 168 ops ran 9 min 40 s and reached
   4,000,000 heartbeats; on the unexpanded list (without `generalize`) a run hit the 16G cap (OOM,
   `journalctl`: scope `run-p173655`). Do it in blocks with `pr_seq2`/`pureRun_rebase`
   (`FRSoundness4R4PfFlag` has the pattern, `run_selSlots`):
   - A: `gFinE0 … (fun _ => false) false` (38 outputs; the old proof's simp, its asserts true) giving
     `rd` facts at `b + 4` (`r2`), `b + 8`, `b + 10`, `b + 16`, `b + 17` (`r4`), `b + 35`;
   - B: the 60 reads and `m̂*` (a `List.range` map: one induction lemma), the three `piField`s and the
     five zero asserts (flag = the zero conjuncts);
   - C: the packs, `eqPt`s, products and the four constants (`c + 64 … c + 75`);
   - D: `rsvSOps` (36 ops, generic in its registers: one lemma);
   - E: the tail (`d + 36 … d + 53`), whose flag is (ii″) ∧ (iii″) ∧ (iv″).
   `relE4`'s reserve branch is written in the values these blocks produce (`rd_getD_toF` turns the
   mixed entries' register reads into `getD` on value lists).
2. **`flag_gFinB'`, reserve branch**: the Horner block `rsvBOps` (59 steps; an induction lemma) and
   `κ′^{11}`; `vStar4` is stated as `v*₀ + κ′^{11}·Σ κ′^i v_i`.
3. **`FRSoundness4R4FrE`**: `relE4_of_accept` (unchanged text; `hin` needs `η` and `0`), then `e_end4`,
   `e_in4`, `e_fin4` against the new `RejEndE4`/`c4E4`/`RejFinE4`: the child terms read Lrend's message
   through `msg_abs4` at 213 (1,008 bytes) and Eend's at 273; `e_fin4`'s `hM` becomes
   `NI4F.implN4F_hMX` (32-entry row point), and the stacked spec meets `mStack` at `xHat`, `r′ ‖ p_y`
   (`ptA` reads `e2R κ`/`ncR κ` coordinates: the constant extension is built in).
4. **`FRSoundness4R4PfFlag`/`PfFin`**: `gFinPfR` with the second chain (`nrcell` cells, `keep rsv`),
   `relPf4`, `relPf4_of_fields`, `fin4_of_fields`, `hz_of_fields` (weight `+ Σ κ′^{11+i} eq(c_i, ρ)`).
   `FrRS.relE4_of_fields`, `Start.start4_of_fields`/`start4_node` (P4b's `vStarL4` must gain the
   same term).
5. **B′ at 69 cells** (`FRSoundness4P4bB`): `PubOK4` keeps the nine (it reads at 3); the 60 are a new
   `PubOKR4` (reads 214) that joins the dooms from phase 16 to B′ (`bg16X`, `bg20X`'s users, `DRS0X`,
   `DRS1X`, `DBX`'s `PubX` argument), and `single_B4`/`bTerms4`/`hcells` go to `Fin 71`, `70·2^128`.
6. **The chain**: `nodeRun_X` gains `PubCellsR4` and `truthChild4` from the phase-16 prefix
   (`T4.tail_of_accept` refutes `D16X` there); `RunFacts4.node`'s `NodeLog` must carry
   `msgAt es 213 = fLrEnd(π)`; `StmtN4` gains `PubCellsR4 κ w (childVals π)` (it then needs `π`;
   `FRNodeCircuit4` is not this track's module). Then `gap4Imp_of_rsv`.
7. Controls (RSV2 §5 item 8): `truthChild_pos`, `childBad_neg`, `kindChange_pos`, `n8_zero`.

## 6. Open questions

1. `StmtN4` lives in `FRNodeCircuit4` (A1′/RSV-V2's); adding `PubCellsR4 κ w (childVals π)` changes its
   signature for every user. Who makes that change?
2. B′'s 60 cells cannot ride in `BgA4` (it reads at 3, the cells' targets at 213). §5 item 5 is the
   design I propose; the orchestrator should confirm it before the next track restructures `bg16X`/`bg20X`.
