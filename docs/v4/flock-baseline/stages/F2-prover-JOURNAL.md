# F2 (native prover) journal

Short running notes so a successor can continue. Logs under `logs/f2/` (gitignored).

## Done
- Read the blueprint, F0 results, PROVER.md, FORMAT.md, PROTOCOL.md, rfh/*.py, contract layouts.
- v3 sources extracted to `logs/f2/v3/`; v3 cargo prover built (`logs/f2/v3-target/release/`,
  `logs/f2/v3-build.log`). Service binaries copied to `logs/f2/rf-oracle`, `logs/f2/rf-bench`
  (sha256 d6003237…, 5a6b9f77…) from `recursion.fast-v4h/service/target/release/`.
- Crate skeleton: v3 sources copied into `submissions/spartan-srom/prover/`.

## Next (for a successor)
- Run the smoke through `run-benchmark.py` with F1's compiled badge (`verify`, `liveness`) once F1's
  `Run` exists: `taskset -c 0-15 python3 -I -B …/harness/run-benchmark.py --season …/smoke.toml
  --entry submissions/spartan-srom --badge <F1 badge> --service logs/f2/rf-oracle --bench
  logs/f2/rf-bench --work … --out …` (the stand-in badge `logs/f2/badge-native/` shows the layout).
- Compare `prover dump-proof --oracle v3 DIR` (= v3's KAT leaves) with F1's Lean `P` under `katOracle`.
- Rerun everything: `logs/f2/run-all.sh` (builds the .s three times, KATs, qemu, selftest, harness,
  benchmarks).

## Problems
- See RESULT §6 (frictions) and §7 (open problems).

## 2026-10-22, session 1 (continued)
- Done: crate ported (`oracle.rs`, `service.rs`, `format.rs`, `acc.rs`, `make.rs` new; transcript,
  prover, verifier, kat oracle-generic; field.rs pclmulqdq dispatch). 27 unit tests pass (cargo).
- Done: leaf bytes = v3 cargo prover at n = 1, 16, 64 and dump-proof/transcript dumps identical
  (cargo build, `logs/f2/kat-cargo/`).
- Done: selftest.py tree (r=2, n=16) and stream (M=4) against rf-oracle: all accepted by
  verify-native, canaries rejected (cargo build; `logs/f2/st-cargo*`).
- Done: build-asm.sh: prover.s 8,673,931 B sha256 632431c9…, deterministic over two clean builds;
  binary 2,694,200 B (`logs/f2/build-asm-{a,b}.log`).
- Done: pclmulqdq path checked under qemu-x86_64 (-cpu Haswell / max: selftest-field + proofs equal
  v3's; Haswell,pclmulqdq=off: portable path, same proofs). `logs/f2/qemu-kat/summary-clean.log`.
- Problem (toolchain, not entry): this VM's static glibc 2.43 (Ubuntu) needs AVX2 at start-up
  (`init_cpu_features` executes `vmovd`): a static hello-world SIGILLs under qemu Nehalem,
  Westmere, SandyBridge. The runner links with its own glibc (24.04), so no effect on the entry.
- Done (final code): prover.s 8,685,873 B sha256 96139ac2…; binary 2,698,448 B sha256 2f12e96b…;
  identical over 2 clean builds + a crate copy in another directory (`logs/f2/build-asm-{a,b,c}.log`).
- Done with the asm binary (`logs/f2/prover-asm`): KATs vs v3 cargo (`logs/f2/kat-asm.log`), selftest
  tree/stream/keyed-kat/sizes (`logs/f2/selftest-asm.log`), harness smoke (run-benchmark.py,
  smoke.toml, all parts) with a NATIVE stand-in badge `logs/f2/badge-native/` (verify-native,
  extract-check, Python chain checker): pass (`logs/f2/harness-smoke.{log,json}`).
- Next: measurements n = 16 … 65536 (keyed vs service), RESULT.
- Harness notes: t_leaf = Σ of M+1 leaf times / M (bench.py); calibration uses os.cpu_count()
  (32) even under taskset 0-15.

## 2026-10-22, final
- Long socket paths (≥ 100 bytes) connect through `/proc/self/fd/<dir>/<name>` (a 109-byte test path
  failed with `path must be shorter than SUN_LEN`); node requests log build vs SIGN.
- Final prover.s 8,699,228 B sha256 13544017…; binary 2,698,536 B sha256 30b46975…; `run-all.sh`
  all green (`logs/f2/run-all.log`); previous run's logs in `logs/f2/prev/`.
- Stream links within proofCap: 5 at n_f = 16, 1 at 1024, 0 at 4096 (`logs/f2/links-n*.log`).
- RESULT written: `F2-prover-RESULT.md`.
