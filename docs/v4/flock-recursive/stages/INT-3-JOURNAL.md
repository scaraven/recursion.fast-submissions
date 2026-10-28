# INT-3 JOURNAL: revision 3.14 across S-0, S-C, S-F, S-G; `FR.lean` complete

Started 2026-10-28 at HEAD `937e14d`. Build tree `logs/fr-build-INT3` (`snap.sh`: HEAD's sources,
this pass's modules symlinked to the worktree; `.lake` copied from `fr-build-e8`, same HEAD). Logs in
`logs/INT-3/`. Every lean/lake command under the 16G scope with a `timeout`.

## Reading

- Changes 21 / revision 3.14 block; QUEUE (INT-3 entry, rulings); INT-2-RESULT; S-CN §5–§7; S-E8 §6.
- `finB′` already has no `κ′ v_E` term (changes 18) and nine cells; `truthB'`/`truthBN` already
  over `cellsOf` = `Node.pubCells` (9). Item "finB′ / truthB′ at `J_f = 9`" is a check, not a change.
- `finE` (v) is in HEAD (INT-2).
- No `truthS1` exists in S-G (FRSoundnessPIOP's header: "the node's S truth … not built here").
- **A.6 map vs S-CN's `fam`**: A.6 pins `off_f` = `x` 0, `j` 399, `end9` 400, `end41` 467, `l` 533,
  `r0` 549, `r31` 565. S-CN's `fam` has `j` at 581, `end9` at 399, `end41` at 466. `wmB`/`mirB`/`mpos`
  match A.6; `fam`'s `mir` for families 1–4 does not. Fix in `FRNodeTarget` (S-C).
- `slotW_in` by kind: `ImplT.slotW : ∀ κ, impl.slotW κ = slotWI` (L-circ's template statement)
  would be false if `implC.slotW` depended on the kind. Choice: keep `implC.slotW` kind-free and
  select in `finSh` with `keep Kind.isNode (slotW 2 …) (slotW 1 …)` (existing ops). Deviation.

## Log
- IR: `linkW` → `linkWAll (tt rr)` (AF 8) and a new `shiftMask (tau r)` (F × F × F, the node's
  chain-masked weights); `OpImpl`/`Meets` fields; `Op.outs`/`Op.nOut` = 3 for `shiftMask`
  (first forgot `Op.outs`: the register numbering of later fields depends on it).
- `piDigest` → `digestAt`: `digestAt_eq` added to `FRVIRSpec.exec_merkleOps`, the `absorb` case of
  `exec_genPhase`, and `FRVIRFinalsSF.flag_finB'` (else a heartbeat timeout).
- `finSh` rewritten (61 registers after `bndOps`); `flag_finSh` needs `maxRecDepth 8192`.
- L-circ repairs: `FRVIRCompile` import cases (`linkWAll` AF 8, `shiftMask` 3 F) and `nOut`;
  `FRVIRTplExt`: `.linkW`'s zero template, `ImplT.linkW` and its case removed (the op is gone; a
  node's `linkWAll` is not 0); `FRVIRTemplates` section title.
- `FRVerifierImplNode`: `ptA_extract`, `linkWAll_eqS`, `shiftMaskI`, `shiftMask_meets`. A `rw`/
  `congr 1` against sums over `range (chainN − 1)` timed out in `whnf`: generalise `chainN`, and
  use `exact`/`congrArg₂` instead of `congr 1`.
- `FRShift`: `ChainLinksM`, `chainDM`, `chainD0M`, `chainLinksM_iff`, `shift_sound_masked`, `shWM`,
  `shift_sum_masked`. Built first time.
- `FRSoundnessShift` (new, S-G): `ShHoldsN`, `truthS1N`, `chainPartN_iff`, `shift_sound_node`,
  `sh_reads_chain_only`, `fam_blocks_ge`, controls.
- Coordinator (mid-task): import `FRNodeRead`, `FRNodeReadW`, `FRNodeReadLayout` too (HEAD now
  `4e382bb`, S-H2 part 20); not `FRSoundnessAccSeg`.
- `relE_e4end` (FRVIRFinalsSF): `tauto` hit maxRecDepth; `split` + `simp only [Bool.and_eq_true]`.
- `FR.lean` imports; `lake build FR` green, 2,358 jobs (`logs/INT-3/build-FR-1.log`).
- Axioms clean (`axioms.log`); source rule 141 files, 0 findings.
- Re-dump: items.json identical to INT-2, piSize 797,904; ops +9.
- V (N30): best 168.7 / 170.1 ms, median 173.9 / 182.3 ms; linkWAll 1.87 ms, shiftMask 0.48 ms.
- Sequential profiles of the 11 changed modules (`profile-*.log`). RESULT written.
