# P2r journal (prover-only performance at rev44: factored E1b rows, E2/E4, start-up)

Track P2 of the orchestrator's brief, 2026-10-30. The stage name `P2` is taken by track P's stage of
2026-10-27 (`P2-RESULT.md`, `P2-JOURNAL.md`), so this stage's files are `P2r-*` (P2 at rev44).

- **Worktree.** `/home/devops/Verified-zkEVM/rf-p2`, branch `p2-work` at `4537909` (RUN2), made with
  `git worktree add` from the rev44 worktree. The rev44 worktree was not touched.
- **Prover.** `submissions/flock-recursive/prover/`. **Logs.** `logs/P2/` (gitignored).
- Every cargo, prover and Lean V run ran in a 16 GB scope under `timeout`. No sub-agents were used,
  and nothing was committed or pushed. No Lean source was touched.

## Log

- 07:25 Read E1b-RESULT/JOURNAL and RUN2-RESULT. A step is aggregate + witness + node prove. On the 7763 the
  node is ≈ 40 % of a mean step (E1b's model: N2 4.38 s of a 9.91 s mean step), and E1b's e2 + e4 are
  ≈ 1.4 s (N2) and ≈ 2.0 s (N4) of it. So even deleting e2/e4 outright could not buy the brief's ≈ 2.2 s a
  step; the factorization alone is worth a fraction of that. Plan: factor the rows, then the other e2/e4
  costs and the start-up.
- 07:30 Worktree `rf-p2`. Copied E1b's dumps (`logs/E1b/{dump,nodedump}`, which the node-kat IR check reads
  from the working tree), `r3/*.signed`, `st1/setup` (as `logs/P2/setup-e1b`), `stream.sh`, `chain.sh`,
  `project.py`, and the Lean V `e1verify` (built at `3d9ae68`; `git diff 3d9ae68 4537909` touches only
  `prover/`) into `logs/P2/`. Baseline binary `logs/P2/prover-old` (cargo, `37deb5c` sources, sha256 `c449b73a…`).
- 07:35 Baseline N4 profile on 4 VM cores (`nab/base-n4-0.log`): e2 5.3, e4 12.1 of 54.7 s. The link work
  (lk.*) is ≈ 2.3 s of e2 + e4. The E4 sumcheck is 8.8 s on its own.
- 07:40 Liveness probe in the E4 sumcheck (`nab/live-n4.log`, `live-n8.log`). With `2^12`-entry chunks, W is
  64 % live (N4) and 99.5 % (N8), and the child table G is 99.8 % live. But only 15.6 % / 22.5 % / 32 % of
  the entries are nonzero: the arena₁ H cells (4 of every 128 cells along the chains) make every chunk live.
- 07:50 **Factored rows** (`mfill::Ext`, `node::set_ext`). A kind table keeps `node-N*.txt`'s link rows only.
  The arena₁ rows are handled slot by slot. Slot 0's replay rows are computed once from prototype 0's
  `spare`, with a by-cell index (`SpareIx`) shared by N2 and N4. All four operations take the factored path:
  `m_matvec`, `child_rows`, `add_cols` (own W and the child columns), and `nodeops::eval_m`/`eval_mx`.
  `node::check` checks the factored rows directly. The full table (`kind_tab_full`, E1b's rows as link
  rows) is kept as the reference for tests. **First N4: π identical** (`a440b237…`), NODE-IR ok, 0 bad
  rows.
- 08:00 `bench-ext` (full vs factored, same process, every output compared: equal). Kind tables
  0.58 → 0.23 s. Child rows −0.3/−0.4 s, child columns −0.55 s on 4 VM cores. Spans: the dense
  `comb3`/`add_run` passes dominate the child terms, not the link rows any more.
- 08:10 Start-up profile (`su-old`, `su-new*`): kind tables 0.58 s of 1.78 s. Most of the rest was the base
  link rows' by-cell index, a counting sort over the `2^25`-cell range (0.09–0.19 s per kind for 35–83 k
  rows). `cell_index` now sorts the terms when the range is large (same entries, same order: test
  `cell_index_matches_counting_sort`). The spare index keeps the counting sort, since its range is small.
  Kind tables 0.30 → 0.10 s.
- 08:25 **E4 sumcheck** (`sumcheck::prove_pairs_support`). It now works over runs of consecutive live chunks
  with the vector kernels (`round_ff`, `fold`), where it had per-pair scalar loops. A closed-form eq pair
  gives per chunk `h_c·round_ff(P, le)`, since the message is linear in Q. `prove_pair_support` is the
  one-pair case. N4 sumcheck 8.8 → 5.4 s on the VM at `a = 12`.
- 08:40 Chunk size `a`, measured in process (`FLOCK_E4_BENCH`: the same tables at each `a`, outputs
  compared, best of two; `nab/e4b-n4.log` … `e4e-n4.log`). a = 3/4: 4.9–5.0 s; 12: 5.4–5.6 s; 5: 6.4–6.6 s;
  6/8: 7.2–7.5 s. The VM is non-monotonic here: 6 and 8 are slower than 12, consistently in two orders.
  I did not chase it, because the VM's portable products do not price the runner's vector kernels. I
  chose **a = 4**, the fastest measured and the least data touched. N8 (W only): 3.6 → 2.8 s.
- 08:55 E2: RSV2's extra product `η·eq(p_x, ·)·Q` in closed form (`EqProd`: no `2^logM` eq table, no fold
  of P). `msg_pairs` uses `round_ff`; `comb3` and `add_run` use `axpy`. **N4, N2: π identical.** I tried the
  E2 c-part with `round_ff` too, but reverted it: on the portable tier it computes 3 products per pair
  where 1 is needed, and N8's e2 regressed by 0.15 s (`nab/r1/phases.txt`).
- 09:05 Start-up: the data tag is now a two-level hash (64 parts in parallel). The image file is read with
  `read_at` in parallel pieces, and the image's large arrays are copied in parallel pieces.
  **New tag → new setup** (`setup-new`, 164 s on 8 cores, 302 MB as before). The kind tables now run
  beside plan loading (small gain: they share the 4 cores).
- 09:20 **Start-up A/B** (`su-ab.txt`, 6 rounds alternating, 4 cores, process start → `ready`): old median
  1.640 s → **new 0.898 s**.
- 09:25 Without the pre-fault (`pf0/`, measurement only): an N2 step (131,072) peaks at 3.6 GB RSS, an N4 at
  2^20 at 7.0 GB, and an N8 first step at 7.6 GB. The 6000 MiB pre-fault zeroes ≈ 3.7 GB that an N2 step
  never uses. That is an open lever, not taken (RESULT §6).
- 09:30 cargo test: one old test (`scatter_gather_and_matvec_match`) called the reference on a factored
  table. It now compares the factored gather with the full table's reference. **59 passed, 1 ignored**
  (`cargo-test-2.txt`).
- 09:45 **Chain** (`chain/`): plan check OK; **10/10 accepted by the Lean V, 10/10 canaries rejected**, 0 bad
  rows. **Every `.signed` output is byte-identical to E1b's `r3` chain** (`chain/identity.txt`).
- 10:00 `prover.s`: two clean `build-asm.sh` runs, **identical**, sha256 `37754901…` (35,147,062 B); gcc 1.6 s.
- 10:20 **Stream st1** (cargo binary, fresh setup 103 s on 16 cores): 9/9 Lean V accept, 9/9 canaries reject,
  native acc 9/9. Full-length first step included.
- 10:35 **Stream st2** (asm-linked binary of the final `prover.s`): 4/4 accept, canaries reject.
- 10:40 Final node A/B (`nab/ab.txt`, final binary) and the projections (`project-7763.txt`,
  `project-9v74.txt`).
- 11:05 Final A/B (final binary, `nab/phases.txt`): 7763-scaled e2 + e4 deltas are N2 −0.34, N4 −0.38 and
  N8 −0.11 s. Projection for RUN2's 9V74: `stream_s` 1,688.7 → ≈ 1,603 s (1.20×) at the measured draw, and
  1,866 → ≈ 1,780 s (1.08×) at the max of 20,000 draws. ≈ 86 s saved, against the brief's ≈ 235 s. RESULT
  written. Done.
