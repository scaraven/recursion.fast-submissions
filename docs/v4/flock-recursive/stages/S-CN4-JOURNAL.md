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
