# H-cert journal

- 2026-10-28. Read the certificate job at the pin `6d05d00`: `evaluate.yml` `certificate` runs
  `harness/evaluate.py cert`; step 3 is `lake build +Challenge +Solution` in a fresh tree inside
  the sandbox (12G scope) within `build_s`; step 4 is the comparator (d03acab, lean4export 076e8e5)
  in a 14G scope within `kernel_s`: two sandboxed `lake build`s (up to date), two lean4export runs
  (the challenge's, then the solution's, each of the `theorem_names` + `definition_names` +
  primitive closure), parse, compare, axioms, then `Environment.replay` of the solution export in
  the Lean kernel, single threaded. No lean4checker, no nanoda (the evaluation's `nanoda` input
  defaults to false).
- Proxy (no Solution.lean): `lake build FR` (FR imports all 190 entry modules); comparator with
  challenge = solution = `FR` and every FR-declared theorem (8,736) / definition (4,962) as targets.
- Local check of the probe on the VM: `logs/H-cert/local/` (HEAD 2ef39b3 tree `logs/fr-build-Hcert`).
- Pushed `probe/cert-time` and `probe/cert-time-2` (commit f2921f7, HEAD + probe files +
  `.github/probe.conf`): runs 40737683146 and 40737761222.
- Local VM: comparator full 768 s wall (accepts), KReplay full 540 s / core 401 s kernel; the
  VM was loaded (≈ 2× the 7763 on the kernel).
- Runs 1–2 (7763 ×2): build 711.6 / 611.5 s, over build_s; comparator full 501.5 / 410.9 s.
- Second probe commit d3ddcd4 (core set, sampler, KReplay): runs 40742497683 (9V45),
  40742498014 (6973P-C); the sampler died under `set -e`. Third commit 2630866 fixes it: runs
  40746452591 (8573C), 40746452803 (9V74), 40751551643 (9V74), 40751551049 (7763: build 613.4 s,
  comparator core 371.7 s, KReplay core 207.0 s).
- Branches probe/cert-time{,-2,-3,-4} deleted; local worktree and branch removed.
- RESULT written: build_s exceeded on the 7763 (3/3), kernel_s fits (core 1.61×).
