# ASK-P journal

Track ASK-P (positional machinery + arena folds). Worktree rev44, HEAD 616b57c. Build tree
`logs/fr-build-ASKP` (copy of fr-build-IMP, MINE.txt = my modules, snap.sh unchanged). Logs `logs/ASKP/`.

## 2026-10-29

- 19:42 tree copied, snapshot at 616b57c, baseline `FR Solution FRSubmission4Fin` green (2,648 jobs, `logs/ASKP/build-base.out`).
- Read IMP §5, B2″, B3, B5, PACK §1.3/§4/§5, FRNodeRows4Arena*, FRNodeRead/Read4, FRXOut4, FRNodeRows4PackSound.
- Orchestrator message: simplest correct evaluation is fine (sparse ok if V ≪ 10 s, plan init extra ≲ 3 s); no effort on keyed/closed forms for speed. Kernel time still hard cap.
- Existing machinery found: `Read.readItems_getElem` (3.x FRNodeReadW: entry j at the prefix sum) — reuse; `segi_elem`/`seg0_elem` (PackSound: stream byte ↔ H cell); `pfView_reassemble4` (fields 0/1 only).
- Design (fold): circular imports forbid naming B3's `AT`/`askRowsX` in `FRNodeRows4`; new low module
  `FRNodeRows4AskPosT` restates them (`TG`, `trailRows`) + memoized `trailMS` (compMSX's memo; repRowsP's
  131 s trap avoided) + `inpTG` (IMP's AT.inp rows). `FRNodeRows4`: `askTG` (= TG.none.add inpTG; ASK-T edits),
  `askRowsT`, `askPI` (rows at π·2^20+arR2+k), `ArFit`, `slotB0`, `arIRows4` (a1 ++ ask moved ++ bits, or a
  rejecting row at the region's last index), `nodeIRows4` per slot `slotRows4 ++ arIRows4 ++ linkIRows4`;
  helpers mem_node_slot/ar/link. a2Rows4 (ALv) NOT folded: the binding range holds the template rows
  (sparse, once per prototype via the copy identity); ALv data would be ASK-T's choice anyway.
- Proof-only edits in FRNodeSound4 (slotRows_hold) and FRNodeSound4R (linkRows_hold): use mem_node_slot/link.
- Fit: ar_idx, ar_mem, ar_nodup, slot_mem/slot_nodup over three parts (old ones renamed *0). hfit4 unchanged.
- Plan: Plan4 gains ar0/ar1 (arOf = trailMS), ag0/ag1, hR adds ArFit (inR checks ivBelow, lengths, inSlotB);
  protoV4 adds askV (sparse grouped, 21/23 tables); slotV4 adds arV4 (a1V4 + bitV4 per slot); nodeIRowsP
  fallback with arIRowsP. Statement changes: protoV4_eq (protoRows π ++ askPI π), Plan4.hR, mkPlan4 args;
  a1V_eq/a1V4_eq hypotheses weakened (k+7≤m → k+5≤m ∧ 7≤m; 24≤m → 22≤m: N2 has m=22).
- FRNodeRows4Plan builds.
- 2026-10-29 ~21:xx: SRA landed (27459d9); re-snapshotted. Added `rsvTG` (SRA's AT.rsv rows restated) to
  `askTG` = (none + inp) + rsv, matching `withRsv (fun _ => AT.none)` by rfl. New FRNodeRows4AskPosF (folds:
  askFold, askFold_rsv, arFit_of, a1_slot, bit_slot) builds. Full `FR Solution FRSubmission4Fin AskPosF`
  green (2,651 jobs, 0 sorry; logs/ASKP/build-2.log).
- FRNodeRows4AskPos (reader spec, alignment, slot_ans/qbyte/qelem + arena versions) builds.
- Note: the stream's last block may be an aggregate's candidate final block: bridge lemmas exclude the last item.
- FRNodeRows4AskPosR (reassemble4 per field/phase/shape, slot_pfAbsorb) builds.
- Measurements: plan4t init 5.35 → 7.07 s user (median, 5 alternating runs); V(N4) own 268.5 → 279.8, all
  313.1 → 328.5 ms (best, 4 rounds); a1V4 ≈ 0.25 ms, bitV4 ≈ 0.4 ms per slot, askV 3.6 ms per prototype;
  MxKat PASS; plan4t check N2 equal true (sparse 422 s).
- Kernel: FRNodeRows4Fit type checking 8.45 s → 3.48 s after fixing ar_mem/ar_idx (2.4 s each: the kernel
  evaluated arN = 4·chainLenOf seq4 through omega's facts; `rw [arN_eq]` first, ar_mem's index part via ar_idx).
- Orchestrator: V budget is ~1.5 s VM/check, plan init ≲ 15 s VM: the fold's +11–15 ms and +1.7 s fit.
- HEAD moved to 24ee435 (R3); re-snapshotted; final build running.
- Final: build at 24ee435 + mine green (2,658 jobs, 0 sorry); axioms 67 decls OK incl. certified; source rule
  439 files 0 findings; plan4t check N2/N4 equal true (N8 sparse cut by the 1,800 s timeout). RESULT written.
