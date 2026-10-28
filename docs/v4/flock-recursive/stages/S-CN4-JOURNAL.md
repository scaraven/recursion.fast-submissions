# S-CN4 journal (the node's verifier ops at the revision 4.1 layout; closes P4e's D11)

Build tree `logs/fr-build-SCN4` (copy of `fr-build-INT6`, `logs/org20`; `MINE.txt` lists the three new
modules). HEAD at start `0fd05ce`, moved to `94ee843` (QUEUE rulings: D10 keep the start term; D11 is
S-CN4's). Every lake/lean command in the 16G scope with `timeout`. No sub-agents, no commits.

## Pass 1

- Read P4e (P4a-RESULT "Pass 5"), `FRSoundness4P4aNS` (`wNode4`, `wNS4`), `FRVIRFinals4.gShCore`,
  R4c's `relSh4` (`FRSoundness4R4FinSh`): on a node, `finSh` (ii)'s weight is
  `E·slotW 0 + linkSum (linkWAll κ (τ‖θ) (r‖r_pos)) κ_s 8 ((Sh + κ_s E₀)·slotW 2) κ_s²` with
  `(E, Sh, E₀) = shiftMask τ₁₈ r₁₈` (τ, r zero-padded to 18) and `κ = N30` (`KindP.ofNode`).
- `slotW` needs no new op: the node's chain blocks keep 3.x's slot maps (h_in at 0, h_out at 256),
  `slotBase 0 = 256`, `slotBase 2 = 0`; `slotWS`/`slotWI` stay.
- `FRNodeTarget4` (specs): `nbN`, `nodeE4`, `rbOf4`, `targetSNode4S`, `lkE`/`lkSh`/`lkE0`,
  `shiftMask4S`, `linkW4S`, `linkWAll4S`; layout numbers without the soundness modules
  (`chLen_facts` by `decide` per kind, `chainLk4_iff`, `srcB4_lt'`, `mirB4_lt'`).
- `FRVerifierImplNode4`: `shP` (successor prefix sum by the low bit, `shP_eq`), `shiftMask4I`
  (prefix sums less chain 0's last block, `sum_lk`), `shiftMask4_meets`; `bt` (9 + (nb − 9)
  `eq` tables, `bt_eq`), `linkWOne4`, `linkWAll4I`, `linkWAll4_meets`.
- `FRNodeTarget4W` (bridge to P4e): `sum_lkW4`, `sum_shN4`, `sum_famW4'`, **`final_node4`**,
  `linkSum_eq8`, **`wSumNode4`**, **`wNS4_node4`**, **`peL_node4`**.
- Lessons: `pad18`/`tauL`/`rbL`/`rpL`/`peL`/`mC` exist both in `FR.Snd` (3.x) and `FR.Snd.P4a`;
  qualify `P4a.`. `congr 2` on the final equation timed out in `whnf`; rewriting the sum explicitly
  is instant. `famW4`'s implicit `n` is `nbC (.node ν)` vs `nbN ν`: restate with `have e : … := `.
- Controls: `lk_cube` (Boolean points), `shiftMask4_ctrl` (N4: link 0→1 is 1; chain 0's last block
  → chain 1's start is 0; E at that block 0), `linkW4S_x0`, `linkW4_ctrl` (x family hit 1 / off 0),
  `chainLk4_ctrl` (decide), `lkE0_ctrl` (the start term is nonzero at r = 0: D10).
- `implN4 base tS ν` / `specN4` / `implN4_meets` (targetS from the parameter `tS`).
- Timing (`logs/S-CN4/time-2.log`, core 7, best of 40): F product 81 ns; `shiftMask4I` 0.38 ms
  (3.x 0.40); `linkWAll4I` 2.07 / 2.17 / 2.19 ms (N2/N4/N8; 3.x 1.84). `time-1.log` printed the
  fraction without zero padding (2.73 = 2.073); fixed in `time-2`.
- Checks: `lake build FR FRNodeTarget4 FRVerifierImplNode4 FRNodeTarget4W` green, 2,500 jobs at
  snapshot HEAD `67e5c76` (`build-final.log`); axioms (`axioms.log`); source rule 279 files,
  1 finding, in R4c's uncommitted `FRSoundness4R4FrE.lean:189` (`export`), none in mine.
- Stopped before `targetSNode4I` (context): handover in the RESULT.

## Pass 2 (track S-CN4b, 2026-10-28)

Build tree `logs/fr-build-SCN4b` (copy of `fr-build-SCN4`, `logs/org20`; `MINE.txt` adds
`FRNodeTarget4C`, `FRVerifierImplNode4T`; `b.sh` = snapshot + build + the probe `scn4btime`).
HEAD `c2c6fba`. Logs in `logs/S-CN4b/`. 16G scope, `timeout`; no sub-agents, no commits.

- **`FRNodeTarget4C`** (closed form, `FR.NT4C`): `tgtE_fin` (the new bit lemma: any `t < 2^32`);
  `tF`, `ivS`, **`sum_contig`** (a sum over a tiled range is the sum over the tiles, by induction
  on `contig`), **`blkW4_layout`** (`layout_contig` + `tgt_of_mem`; the layout is never evaluated);
  pieces `chain_piece` (`body_sum` + the final last block), `stmt_piece`, `wots_map`/`wots_piece`,
  `tail_piece` (`fin_target`); `clsW`/`ctrG`/`finG`/`stepG`, **`Gc4`**, **`blkW4_eq`** (one
  `ring` after the pieces), `Gc4_hi`, `targetSNode4_blk`, **`targetS_node4_eq`**; `lay_bounds`,
  `clsW_congr`, `finG_congr`, `stepG_congr`.
- **`FRVerifierImplNode4T`** (computed, `FR.NI4T`): `pfx9`/`twoF9`/`sepSum9` (3.x's at base
  512), `tabs9` over S-CN4's `bt`, `eq9`, `rangeI9`; counters `colT` (one cut pass over the
  columns), `sepD` (rows of the range summed directly), `ctrK`, `ctrArr` (short bodies direct);
  `clsTab4`, `gAt4`, `gArr4`, **`targetSNode4I`**, **`targetSNode4_meets`**; **`implN4T`**,
  **`implN4T_meets`** (no `tS` hypothesis); controls.
- Lessons (kernel): (1) after `List.map_map` the WOTS intervals are `(ivS w p ∘ f) iv`; any
  defeq check of that against `ivS w p ⟨…⟩` made the kernel unfold `ivS` (a `Finset.sum` over
  `range (wotsBase + … − wotsBase …)`): *deep recursion*. Fix: `wots_map` states the rebased list
  for an abstract `g`, struct equalities by `tiv_eq` + `omega`, then `g := ivS w p`. (2) `congr 1`
  and `rfl` try to close `Σ_{l<512}`/`pfxAux g 512` by evaluation (max recursion): use
  `congrArg₂`, and a lemma generic in `k` (`pfxAux_getD`). (3) `rw` with `fun _ => rfl` against a
  metavariable array function tried higher-order unification through `ctrG`: give the function.
- Timing (`time-1.log`): first form 3.26/3.39/3.75 ms (N2/N4/N8), 3.x 1.97: the counters (26 bits
  × 4 bodies, a 512-entry prefix array per bit) were 2.3 ms. `time-2`: shared column passes
  (`col3`, a tuple per step: 74 ns per column) 2.47–2.78 ms. `time-3`: `colT` (three `sumTo`s cut at
  `l₀`, `l₁`) and short bodies (`n < 512`, the key leaves) directly from their `eq` values:
  **1.49 / 1.64 / 1.80 ms** (3.x 1.95).
- Speed-ups (S-CN4's list): `shiftMask4I` through `prefixQ`/`shQ` (index-shifted recursion,
  `prodTo` loop instead of `prodAt`'s `Fin` product, factors from `mArr`): 0.38 → 0.13 ms.
  `linkWAll4I` through `linkWOneF` (per-slot arrays of `eq(τ,·)`, `eq(τ,·) eq(r,·)` on the WOTS
  blocks and `eq(r,·)` on `WM`; `SW` factored out): 2.07–2.19 → 1.69–1.82 ms; the rest is the field
  weights `SW`/`MI` (not touched). `time-4.log`.
- Coordinator's request (S-T2 §6): `implN4`/`specN4`/`implN4_meets` through `Impl.withRS4`,
  `withRS4S`, `withRS4_meets` (re-snapshot at `1ee751b`); `specN4`'s `rsWeight` is `rsWeightS4 ν`.
- Final checks: build 2,508 jobs (`build-final.log`), 23 axiom lines clean, source rule 293 files
  0 findings, profiles `prof-*.log`, loc `loc.txt`. RESULT "Pass 2" written (§P2.6 is the op shape
  for S-E12d).

### For S-E12d

`targetSNode4I`'s op shape is in `S-CN4-RESULT.md` §P2.6: tables (`eqTable(zLo)`, `bt nb` with
prefix arrays), ten class weights over the layout constants, 26 body-counter bits (`ctrArr`: key
leaves direct, chains `colT`/`sepD`), 32 final-block counter bits (`finG`), `w43`'s 16 field bits,
`G` at 1,153 positions from `clsTab4`, then `Σ_{hi<19}`. `shiftMask4I` and `linkWAll4I` changed
shape (`prefixQ`/`shQ` over `mArr`; `linkWOneF` over per-slot arrays): §P2.6.
