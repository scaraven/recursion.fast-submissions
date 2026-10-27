# S-F2 journal (track L-cert: the concrete `OpImpl`, `V`, the compiled-`V` probe)

Branch `v4/flock-recursive`, HEAD `c8e1869`. Build tree `logs/fr-build-cert` (`snap.sh`: HEAD's
other-track modules, L-cert's files as symlinks). Probe `probe/fr-vtime/` (outside the entry).

## 2026-10-27

- Read TRACK-RULES, S-F-RESULT (rev 3.9 follow-up inventory), BLUEPRINT §3, A.8, A.9.
- Surveyed the owners' code. Found four interface gaps in `OpImpl` (S-0's `FRVIR`):
  - `targetS`, `slotW` (slot map 1), `linkW` depend on the kind; `OpImpl`'s fields get no kind, and
    P30 and N30 have the same operand lengths, so no single field can be right for both;
  - `shiftTarget τ θ bnd` has no `κ_s` operand, which A.9 `finSh` (i) and the native leaf verifier
    (`leaf.rs`: `eq(τ,1…1)·h̃(θ) + κ_s·s̃(θ)`) need.
- `FRVerifierImpl` v1: implementations of every op, specs for the resolved ones; `lagrangeS_meets`.
  `rw` closing goals by `rfl` hit `whnf` timeouts on sums over `Fin 64`/`Fin 127`; `rewrite` avoids it.
- Probe v1 (HEAD's sources): **`V` on a synthetic N30 proof took 283 s**. Per-op profile
  (`logs/S-F2/prof-N-1.log`): `piDigest` 7,554 ops 233 s, `piDigestAt` 27 s, `piElem` 15 s, `piElemK`
  6.8 s. Cause: `FRTranscriptDefs.bytesAt` reads `q.data.getD (o + i) 0`; in compiled code
  `ByteArray.data` copies the whole 755,680-byte proof into a boxed `Array UInt8` per byte read.
- My ops were slow too: `xS` is a `Finset` sum over `Fin 7` per call (`lagrangeS` 127 ms, `eqZ`
  13 ms, `rowW` 16 ms). Fixed with a node table `skipTab`/`xT` (now 4.9 / 0.7 / 3.9 ms).
- Probe v2 on a private copy (`logs/S-F2/src-fast`) where only `bytesAt` runs as `q.get! (o + i)`
  (`implemented_by`, probe only): warm `runSeq` 202 ms (N30), 198 ms (P30), 203 ms (L32);
  `traceDigestF` 12–13 ms. Without `finPf` (S-G1d) and with `evalL` on no rows.
- `Layout.nodeRows finC` (S-E2's `evalM` rows: `compileMux` of both slots) did not finish in 600 s;
  a longer background run is in `logs/S-F2/rows-1.log`.
- `nodeRows` is quadratic: `FRVIRCompile.CS.add` appends `cs.rows ++ o.rows` on lists inside a
  `foldl`. The second run was stopped after 17 min at 155 MB. `evalM`/`evalMK` need S-E2's templates.
- Proved: `eqZ`, `rowW`, `phiRS`, `shiftEq`, `tensorW` (table `wTab`, `prodTo`), `slotW`,
  `rsWeight` (char-2 `eq`, `c_k` once over F), `shiftTarget` (with `κ_s`), the leaf `targetS`
  (`targetSLeaf_meets`, every `b`), `evalMK` (`sparseK_eq`). Assembled `implC`, `specC`,
  `implC_meets`, `finC`, `VC`. Controls: `ctrl_lag_self/other`, `ctrl_slotW_hit/miss`.
- `implC_meets`: `exact`ing the per-op lemmas against the record's projections hit `maxRecDepth`
  (Lean unfolded `eqZI`/`rowWI` to `Array.ofFn` of size `2^14` before the projection). It works
  after `simp only [OpImpl.Meets, implC, specC]`.
- Final probe on `src-fast` (9 reps, `logs/S-F2/vtime-*-final.log`): N30 best 182.7 ms, median
  193.4 ms; P30 177.4 / 181.1 ms; L32 177.6 / 181.9 ms; `traceDigestF` 12.5 ms.
- Module: 454 code lines, 11.5 s wall, kernel 0.90 s, 2.8 GB. Axioms: the standard three. Source
  rule: 0 findings.
