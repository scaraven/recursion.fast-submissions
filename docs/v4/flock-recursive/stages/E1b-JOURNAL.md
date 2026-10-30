# E1b journal (the native prover brought to the node circuit at `e447823`)

Track E1b, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `e447823`). Prover
`submissions/flock-recursive/prover/`. Logs `logs/E1b/`. Lean tree `logs/fr-build-E1b` (copy of
`fr-build-SEGR2`'s `.lake`, sources re-snapshotted by `snap.sh` from `git show e447823:` — no symlinks into
the worktree, so FEL's edits do not leak in). Every lake/cargo/probe run in a 16 GB scope with a timeout.

## Log

- 03:45 Read E1-RESULT/JOURNAL, RUN1 §0, the prover sections of IMP, ASK-P, ASK-T, R3, C1b, IMPC, IMPC2,
  REPF, SEG-R1, SEG-R2. Node rows at HEAD: `nodeIRows4 = slots (slotRows4 ++ arIRows4 ++ linkIRows4) ++
  repAllRows`; `arIRows4` = arena₁ copy rows (H → M), the ask-template rows `askPI` (pure move of the
  prototype's), the bit rows; replay rows `repIRowsW rtC1d` (segment slots: pure move into SEG-R2's bands;
  slot 0 of N2/N4: the spare region `κ.vslots`).
- 03:50 New probe `probe/NodeDumpX.lean` (tree only): `mask-p{π}` (`askRowsT π`), `mrep-p{π}`
  (`repRowsP (rtC1d π) π`, raw: locals at `repB + j`), consts, fit checks, `mxkat.txt` (`evalMT4 planOf4`
  at MxKat's LCG points). Dump (`logs/E1b/dump.sh`): IR dumps and `proto-p*.txt` byte-equal to E1's
  (segment side unchanged); askRowsT 130,914 / 154,333 (slack 35 at p1), repRowsP 562,758 / 38,805,
  repFitB true, plan inR true.
- 04:00 Prover: `mfill::load_extra` (ask rows, generated bit rows, p1 replay rows moved by `seg_row`/
  `seg_cell`; p0's replay rows → `Proto::spare`), arena₁ written by the fill from the slot's stream,
  `node::extend_links` (a1 rows per slot + slot 0's replay rows into the kind table), `spare_fill`
  (slot 0's replay locals by the worklist over `spare`), blob v3 (`FRNB3`: extra + spare rows), image v3.
- 04:05 N8 k=1 first run: active slots 0 failed rows after a **packing** solve (`try_pack`: bit
  decompositions `sel·(x + Σ x^h b_h) = 0`); inactive sub-slots failed on (a) the statement tag read
  (element 13 byte 0 = 0x4c), (b) the `input` cells (= arena elements 1–4 = `vk ‖ c_in`, tied by the
  statement link rows to vk and the slot's hashA output), (c) the replay copy rows (import = template
  output ≠ 0). Fixes: the phantom segment carries `vk ‖ c_in` and the leaf tag (`phantom_seg`), the
  inactive fill pre-sets no import, solves, then zeroes the imports still unknown and solves again.
  N8 k=1: 0 failing M rows, 0 failing link rows.
- 04:08 **Lean V at e447823 accepts N8 (k 1) and N2 over it** (`logs/E1b/r2/chain.txt`), canaries
  rejected; plan check `PLAN-CHECK OK` (inR, lk eok, askRowsT 130,914/154,333 ≤ 154,368).
- 04:12 Blob 22,664,736 B (b64; raw 67 MB: spare rows 13.6 MB of it). plan-kat equal (incl. spare rows),
  planform_kat PASS, **mx-kat PASS** (Rust M̃ = Lean evalMT4 for N2/N4/N8 at two points).
- 04:15 Chain at e447823 with the dump (`logs/E1b/r2/chain.txt`): **10/10 nodes accepted** by the Lean V
  (N8 k1, N2←N8, N4←N8 k2, N4←N2 k2, N2←N4 k1, N2←N2 k2, N4←N2 k4, N4←N4 k3, N4←N4 k1, N8 k2+k4),
  10/10 canaries rejected, 0 failing rows.
- 04:20 Profile (N4 full support): the link loops (now ≈ 1.3 M rows: arena₁ + slot 0's replay) were
  sequential: parallelized (`KindTab::links_eval`, `links_cols` over a by-cell index built once by a
  counting sort, `land_items` two-pass parallel landing); kind tables built once in parallel
  (`kind_tabs_static`, also used by `Pre`). Inactive fill: the two-phase solve is recorded with
  `ZERO_ENTRY` entries and replayed (the setup's cached inactive fill holds only for vk = 0).
  Prototype 0's inactive fill dropped from setup/warm (slot 0 is never inactive; its phantom would not hold).
- 04:35 cargo test: 56 passed, 1 ignored (`logs/E1b/cargo-test-1.txt`). Node A/B on 4 VM cores
  (`logs/E1b/nab/ab.txt`; E1 binary at 7537acd vs E1b): see RESULT §4.
- 04:45 Setup 122.7–141 s on 12 VM cores (E1: 167 s), peak RSS 7.4–7.7 GB, 302 MB.
- 04:50 Orchestrator: FEL committed at **3d9ae68**. Re-snapshot (`COMMIT=3d9ae68 ./snap.sh`), probes rebuilt,
  re-dump: changed `maux`, `mrows`, `plan-form`, `mxkat` only (as FEL §7 says); planform_kat PASS, blob
  22,663,716 B (sha256 f542403e…), plan-kat equal, mx-kat PASS. e447823's dumps kept as `*-e447823`.
- 04:55 Chain at 3d9ae68 with the embedded blob (`logs/E1b/r3`): N8 and N2 accepted, 0 conflicts (FEL's
  aliased aux writes equal the arena values).
- 05:10 Chain at 3d9ae68 (`logs/E1b/r3/chain.txt`): **10/10 accepted** (N8 k1, N2←N8, N4←N8 k2, N4←N2 k2,
  N2←N4 k1, N2←N2 k2, N4←N2 k4, N4←N4 k3, N4←N4 k1, N8 2×k4 over 2^20 each), 10/10 canaries rejected.
  (An extra `N8 --agg 4194304` line was dropped: that is k = 16, not a valid aggregate.)
- 05:20 Stream `st1` (cargo binary, setup 110 s on 16 VM cores): 9/9 Lean V accept incl. the full-length
  first step, 9/9 canaries rejected, rc 0. `prover.s` determinism: two clean builds identical
  `09570a1b…` (34.7 MB), gcc 1.95 s. Stream `st2` with the asm-linked binary: 4/4 accepted, rc 0.
- 05:40 Node A/B round 2 (final binary vs E1's, 4 cores): 7763 Δ e2+e4 N2 +0.29, N4 +0.39, N8 +0.11 s;
  projection in RESULT §4 (stream_s mean ≈ 1,651, max ≈ 1,813 of 1,920; V checks at ≈ 0.8 s on the 7763
  are the main new harness cost). cargo test 57 passed. RESULT written. Done; no handover needed.
