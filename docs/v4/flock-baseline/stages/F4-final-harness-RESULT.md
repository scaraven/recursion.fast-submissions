# F4: `spartan-srom` through the fixed v4 harness — RESULT, 2026-10-23

Status: **done; not committed.**

| | |
|---|---|
| Entry | committed tree **`745c7d8`**: the Lean fix pass at core `81e1ebf`, D-6 caps, the byte-level node reader, golf. `prover.s` SHA-256 `7a30e654…` |
| Harness | the core after its fix pass, **`81e1ebf`** (`docs/v4/stages/B-harness-RESULT.md` §9) |
| Workarounds | none: default organiser roots (no `RF_ORG_ROOTS`), the entry as committed |
| Discipline | as in F3: a private package tree, `taskset -c 0-15`, every command under `timeout`, nothing written to shared trees or core worktrees |
| Logs | the worktree's `logs/f4/` (written `H/` below) |
| Machine | the shared 32-vCPU VM, lightly loaded this time (load average below 3) |

The F3 comparison is `F3-harness-RESULT.md`.

## Verdicts

| Run | Verdict | Numbers | Log |
|---|---|---|---|
| `org-setup.sh` (default roots) | ok, 4 min 12 s | roots now include CompPoly: allowlist 10,816 modules, manifest 34,374 files | `H/org-setup.log` |
| **`cert`** (Lean kernel) | **ok**, 9 min 52 s | details in the table below | `H/cert.{log,json,rsmon.json}` |
| **`cert --nanoda`** | **ok**, 16 min 36 s: `kernels: ['lean']`, `second_kernel`: "nanoda: over budget (cap 14G, peak 14.00 GiB); checked by the Lean kernel only" | Lean run ok, 360.6 s. nanoda run `over budget` (exit -15, scope `memory.peak` 15,032,385,536 bytes, 396.3 s); `nanoda_bin` reached 13.60 GB RSS after about 341 s | `H/cert-nanoda.{log,json,curve}` |
| **`bench`, `smoke.toml`, all parts** | **ACCEPT** | `T_tree` 0.140 s, `t_leaf` 0.0689 s, `t_merge` 0.0138 s, `t_link` 0.0827 s, **`S` = 1.794** | `H/bench-smoke.{log,json}`, `H/bench-smoke-reverify.log` |
| `bench`, `season.toml` unchanged | **REJECT**, 33 s after start | "tree1: prover tree exit 3; prover output (tail): 'spartan-srom-prover: oracle service: a Fiat–Shamir query of 1572898 bytes is above queryCap = 1048576 (the service refuses it)'" | `H/bench-season.{log,json}` |
| `bench`, `season.toml` unchanged, `--parts calibrate,stream --stream-repeats 1` | **REJECT**, 34 s after start | "stream1 outputs: stream1 leaf 0 rejected by acc" | `H/bench-season-stream.{log,json}` |
| frontier `r = 2, n = 128` | **ACCEPT** | `T_tree` 0.814 s, root `acc` 547 ms, root `π` 936,916 bytes, DoS `max_ns` 401 ms | `H/fr-tree-r2-n128.*` |
| frontier `r = 2, n = 256` | **REJECT** | "tree1 root and samples: tree1 root rejected by acc", root `π` 1,166,724 bytes > `proofCap` | `H/fr-tree-r2-n256.*` |

The certificate job in detail:

| | |
|---|---|
| Lean-kernel run | 353.8 s, scope peak 4.25 GB (cap 14 GiB) |
| · `Solution` build | 147 s, the largest `lean` 4.13 GB |
| · kernel phase | about 144 s; comparator 3.67 GB |
| binding | "byte-identical (134 artifacts)", 67 built modules |
| gate-tree build | 173 s |
| gate | PASS, 18 s, 2.49 GB RSS; 28 CompPoly modules pinned |
| badge build | 16 s |

**The smoke run** (`H/bench-smoke.json`; per-check times re-run on core 15 in
`H/bench-smoke-reverify.log`):

| What | Result |
|---|---|
| prover binary | `fecda6a0…`, 2,818,664 bytes |
| tree checks | root `acc` 416.5 ms in the run (403 ms re-run); samples: leaves 87–97 ms, `N1` bundles 193–196 ms |
| stream checks | leaves 90–174 ms; nodes 1–4 (bundles of 2–5) 353, 307, 417, 488 ms |
| `T_V` | `T_triv_best_ns` 120,818, cap 12.1 µs, `max_ns` 505.7 ms, 19 of 19 checks over the cap. Not enforced at the smoke shape. The result now records `remeasured` and the best-of statistic (RB-M1) |
| canaries rejected | 76 tree (the new `trace-query` canary included), 20 stream, 32 liveness |
| DoS | 64 inputs rejected, `max_ns` 312 ms, median 17.2 ms |
| liveness | ok, `ran: true`, 3 witnesses from a 30,820-entry log; the badge took 17.1 s, 143 MB |
| service | 5.46 M calls/s on 1 thread, 104.9 M on 32; `service_refusals` empty |

**The season tree.** The prover itself checks `queryCap` and stops before sending the query, so the
service's refusal counter is 0. The run stopped 14.1 s into the tree run, at 6.41 GB RSS. The cause
is unchanged from F3: the 1,572,898-byte `absorb` of `ū` at `n = 2^18`.

**The season stream.**

- Leaf 0 at `n_f = 2^16` now completes: 14.4 s, **2.64 GB RSS** (scope 2.71 GB), well inside 11 GiB.
- Its file is 5,990,112 bytes with **`π` = 2,791,559 bytes**, so `acc` rejects it at
  `proofCap` = 2^20.
- The stopping rule moved from the memory cap (F3) to **`proofCap`**, as expected.

## What changed since F3

| | F3 (`8111b71` on `a874f87`) | F4 (`745c7d8` on `81e1ebf`) |
|---|---|---|
| frozen entry, default setup | REJECT: false rebuild-binding failure (Q7); with V, REJECT: CompPoly `@[csimp]` (Q2) | **ok**: no workaround |
| certificate job | 14 min 22 s (V, CompPoly roots); comparator 513 s; badge build 74 s (986 objects compiled) | **9 min 52 s**; comparator 354 s; badge build 16 s (CompPoly objects prebuilt by `org-setup`) |
| `--nanoda` | PROVISIONAL: "comparator: exit -15, the certificate does not check" (nanoda OOM, Lean kernel never ran) | **ok**: the Lean kernel runs alone first; nanoda's OOM is reported as `over budget` with cap and peak, and does not touch the verdict (Q12) |
| smoke `T_tree` / `t_leaf` / `t_merge` / `S` | 0.896 s / 0.2512 s / 0.0373 s / 6.666 | **0.140 s / 0.0689 s / 0.0138 s / 1.794** (3.7× lower `S`) |
| smoke root `acc` / `T_V` max | 979 ms / 1,592 ms | **416 ms / 506 ms** |
| smoke DoS `max_ns` | 443 ms | 312 ms |
| liveness | 24.1 s | 17.1 s |
| season tree message | "prover tree exit 3" only, with no reason in the result | the prover's stderr tail with the `queryCap` reason (Q13) |
| season tree failure | after 27.6 s, 6.5 GB | after 14.1 s, 6.41 GB |
| season stream | OOM at 11 GiB after 25 s, reported as "proof.bin: missing; stderr: " | leaf completes (2.64 GB, 14.4 s), "leaf 0 rejected by acc" at `proofCap` |
| frontier | `r = 2`: `n = 128` ACCEPT, `n = 256` REJECT | the same, with the same `π` sizes (936,916 / 1,166,724 bytes); the rest of F3's frontier table stands |

## Frictions: new, and still open from F3

**New, or seen for the first time:**

1. RB-m4 makes `--parts stream` alone a harness error when `T_V` is enforced. The season stream must
   be run as `--parts calibrate,stream`. That computes the season's whole tree instance (64 × 2^18
   chain digests) and the 2.66 s chain checker three times before the stream starts: 14 s here.
   This is sound, but `--parts stream` no longer works for the season file.
2. A rejected tree run still leaves no `tree` record in the JSON: no `T_tree`, no `prover_head`, no
   `T_V` block. The reason string now carries the prover's tail, which is what mattered (F3
   friction 4, mostly fixed).

**Still open from F3:**

- "rejected by acc" still gives no reason (size cap, signature or verifier); F3 friction 6.
- `t_leaf` = Σ / `M` over `M + 1` leaves: 0.0689 against a mean of 0.0551.
- The calibration still runs `threads_32` under a 16-core affinity.
- Stream, canary and DoS `acc` times are still absent from the result.
- A private writable package tree is still required: the copy took 4 min 8 s, `org-setup` 4 min
  12 s.

**Not observed:** the OOM reporting (Q14) was not exercised, because the golfed prover no longer
runs out of memory at `n_f = 2^16`. nanoda still does not fit 14 GiB on this entry (F3 measured
more than 20 GB, not finished). With Q12 that costs only the second check, not the verdict. A
`--nanoda` job now takes 16 min 36 s instead of 9 min 52 s, because the separate nanoda run (396 s,
until its kill) comes on top of the Lean run.
