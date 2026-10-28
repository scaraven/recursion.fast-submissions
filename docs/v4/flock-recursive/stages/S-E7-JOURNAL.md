# S-E7 (track L-circ): JOURNAL

Stage S-E7, 2026-10-28, HEAD `dbe47d4` (revision 3.14).

- I read changes 21, in particular (D) and the per-track list, and S-F2-RESULT §6.
- Build tree `logs/fr-build-e7`, a copy of `fr-build-e6` with HEAD's snapshot.
- V at the start (`vtime-N-{1,2,3}.log`): **227.4 / 232.6 / 233.9 ms best, 236.7–249.7 ms median**.
  The per-op profile is in `prof-N.log`.
- Kill-test arithmetic, from the measured 227.4 ms:
  - plus `linkWAll` 1.9, the remaining templates 3, `R`'s closed forms 5, and the fused child
    walks 16: 253.3 ms, 1.04× (below the 1.05× asked);
  - with the walks as implemented: 267.3 ms, over the cap.
- So the fit needs the hot spots. The ownership of each is in the RESULT §2:
  - `dotKF`, `tensorW` and `maskRows` are L-circ-local;
  - `idx` and `askNode` need S-0's definitions, which `FRSoundness*` unfolds.
- I drafted `FRVIR.dotKFF` (a fused loop) and reverted it unproved.
- I stopped for context length (one long session from S-E5 on). The RESULT lists the items in
  order.
