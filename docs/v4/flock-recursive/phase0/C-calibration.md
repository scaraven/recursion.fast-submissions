# Calibration: `spartan-srom` through the real evaluation workflow at core `15dac52`

Runs `40493471459` (smoke, `split = false`) and `40493470932` (season, `split = true`), started on
2026-10-27 by `.github/workflows/eval-push.yml` (FR-D7) on branches
`eval/spartan-srom-{smoke,season}-15dac52`. They evaluate `submissions/spartan-srom` unchanged
(prover `733b3a30…`). Artifacts and logs are in `logs/gh/<run>/` and `logs/gh/<run>.log`.

## The runner (measured)

AMD EPYC 7763 (Zen 3), 4 vCPU, 16 GB, image ubuntu24 `20261023.334.3`. SIMD: AVX2, SHA-NI,
PCLMULQDQ, VPCLMULQDQ (256-bit). **No AVX-512 and no GFNI.** The design's earlier runs saw EPYC
9V45/9V74; runners are heterogeneous, so a result records its CPU.

## The certificate job (season caps)

| Phase | Measured | Cap |
|---|---:|---:|
| entry build (17.9k Lean lines, 66 modules) | 179.8 s | 600 s |
| comparator, Lean kernel | 105.1 s | 600 s |
| gate | PASS | 120 s |
| job, with a cold organiser cache | 6 min 21 s (smoke), 6 min 47 s (season) | 30 min |

A cold `setup` (no cache yet at this pin) took 10 min 45 s and 13 min 19 s, before any entry code
ran. Later runs hit the cache.

**What it means for the recursive entry.** At the baseline's mix of proofs, the caps allow
roughly 3.3× its build and 5.7× its kernel time. That is about 55k lines of similar Lean before
the build cap binds (an estimate, linear in lines; `decide`-heavy proofs scale worse).

## The benchmark

| | Smoke | Season |
|---|---|---|
| verdict | **ACCEPT** | REJECT |
| reasons | — | tree: a 1,572,898-byte Fiat–Shamir query is above `queryCap`; stream: leaf 0 is rejected by `acc` (above `proofCap`) |
| `T_triv,best` (chain checker, one core) | 68.7 µs | **2.059 s** |
| `T_V` cap (`T_triv,best / 10`) | 6.9 µs, reported only | **205.9 ms**, enforced |
| score | `T_tree` 0.081 s, `t_link` 0.024 s, `S` 0.560 | — |
| root `acc` | 293 ms (2.17 MB bundle of four leaves) | — |
| service, 64-byte queries | 10.7M calls/s on 1 thread, 30.0M on 4 | 11.2M, 30.0M |
| service key generation | 675 ms | 671 ms |

The season verdict is the expected one for a non-recursive baseline (design §3.6). The pipeline
itself (plan, setup, setup-tools, certificate, benchmark parts, attest) ran green end to end on
GitHub for the first time at this pin.
