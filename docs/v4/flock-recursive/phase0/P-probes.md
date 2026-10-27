# Runner probes, run `40496884479` (2026-10-27)

`.github/workflows/probe.yml` on branch `probe/phase0`, image ubuntu-24.04. Artifacts are in
`logs/gh/probe-40496884479/`.

## The runners are heterogeneous (measured)

Four CPU models have appeared across three runs: AMD EPYC 7763 (Zen 3: AVX2 and 256-bit
VPCLMULQDQ, **no AVX-512**), AMD EPYC 9V74 (Zen 4: AVX-512), Intel Xeon 8370C (Ice Lake: AVX-512)
and Intel Xeon Platinum 8573C (AVX-512). The prover must dispatch at run time. The season shape
must pass on the slowest model, the 7763.

## Compiled Lean (`probe/lean-field`, EPYC 9V74, one core)

| Operation | ns (median) |
|---|---:|
| GF(2^128) product, "holes" on 64-bit words (`h64`) | 45.8 latency, 43.8 throughput |
| the same on 32-bit halves (`h32`) | 56.2 |
| boxed `h64`, a real call | 54.6 |
| dot product of 1024 boxed / inline elements, per term | 56.2 / 48.8 |
| GF(2^128) squaring | 8.7 |
| GF(2^64) product (`h64`) | 21.0 |
| BLAKE2s `compressF` | 134.6 |

All 5,706 known answers agree. Chain checker at the season shape: 1.78–1.79 s on this 9V74. The
EPYC 7763 calibration run measured 2.06 s, so `T_V` is 178–206 ms depending on the runner. At
about 50 ns a product, 1–3 × 10^5 products cost 5–15 ms, so **`T_V` does not bind**.

## Flock at `48f4bfe` (`probe/flock-bench`, Xeon Platinum 8573C, AVX-512 + VPCLMULQDQ path)

| | 1 thread | 4 threads |
|---|---:|---:|
| BLAKE3 compressions/s, batch 2^14 | 35,973 | 79,300 |
| BLAKE3 compressions/s, batch 2^16 | 53,306 | 118,400 |
| SHA-256 compressions/s, batch 2^16 | 23,431 | 52,584 |

- **One BLAKE3 batch proof at 2^16, 4 threads:** Secure (120-bit UD) 619.0 KiB, Fast 406.6 KiB.
  Peak memory 3.38 GB.
- **Tower example** (8 leaves × 4,096, Chain128): per node proof 1.27–1.30 s online (prove
  1.25–1.28 s), verify 33 ms, proof 252.8 KiB. The whole run took 64.1 s, with a root discharge of
  2.64 s.
- The per-stage `tower_online_bench` test failed on the runner. It is Flock's test and not needed
  here.

**What it means (estimate).** On an AVX-512 runner, BLAKE2s costs about 1.43× BLAKE3 in AND
constraints, so Flock's kernels would give about 83k compressions/s on 4 threads. The tree's 2^24
leaf compressions would then take about 200 s, inside the 600 s cap. The Zen 3 runner is the
open case: the kernel kill test (K) measures it.
