# S-E7 (track L-circ): RESULT — stopped early, with context exhausted

Stage S-E7, 2026-10-28, HEAD `dbe47d4` (revision 3.14). Build tree `logs/fr-build-e7` (a copy of
S-E6's tree, `snap.sh`). Logs are in `logs/S-E7/`. Nothing is committed, and **no source file is
changed**: one draft (`FRVIR.dotKFF`) was reverted, because its proof was not finished.

I stopped at the start of item 1, as the brief allows when the context gets long. S-E7 resumed
directly after S-E5 and S-E6 in one long session. What follows is the measured starting point, the
kill-test arithmetic, and the items in order with what each needs.

## 1. Measured at the start (VM, one idle core, N30, full 3.13/3.14 finals, real L rows)

| | best | median | Log |
|---|---|---|---|
| **V (`vtime v N`, warm `runSeq`)** | **227.4 / 232.6 / 233.9 ms** | 236.7–249.7 ms | `vtime-N-{1,2,3}.log` |

`traceDigestF` was 12.0–13.0 ms, its baseline.

Per-op profile (`prof-N.log`; the profiled run takes 312 ms in all):

| Op | ops | ms |
|---|---|---|
| `evalM` | 1 | 73.3 |
| `dotKF` | 871 | 30.7 |
| `askNode` | 7,552 | 22.9 |
| `idx` | 871 | 19.8 |
| `tensorW` | 1,627 | 13.1 |
| `walkAB` | 1 | 11.9 |
| `maskRows` | 1 | 8.5 |
| `mulK` | 16,406 | 8.4 |
| `rsWeight` | 1 | 7.3 |
| `piDigest` | 7,555 | 7.3 |
| `phiRS` | 512 | 7.2 |

## 2. The kill-test arithmetic (changes 21 (D), "measure first")

Measured 227.4 ms, plus:
- `linkWAll` 1.9 ms;
- the remaining templates ≈ 3 ms;
- `R`'s closed forms ≈ 5 ms;
- the child's two walks: 16 ms fused, or 30 ms as implemented.

That gives:
- **with the fused walks: ≈ 253.3 ms VM, 264 / 253.3 = 1.04×.** This is **below the brief's 1.05×
  margin**.
- with the walks as implemented: ≈ 267.3 ms, **over the cap**.

**So the fit needs the hot-spot work** (S-F2 §6), as the blueprint's FR-D2 frontier says. The
targets, from the profile (savings are estimates, not measured):

| Hot spot | Now | Cause | Fix | Expected | Where the fix lives |
|---|---|---|---|---|---|
| `dotKF` | 30.7 ms | ≈ 1 µs per column element against 2 F products (`felems`' arrays, `zipWith`) | a fused loop `dotKFF` | ≈ −18 ms | `dotKF`/`felems` are used only in `FRVIR` and L-circ's template modules (`FRVIRTplLag`/`Core`/`Ext`), so this is self-contained: define `dotKFF`, prove `dotKFF_eq` (both sides as `Finset` sums), and use it in `evalOp`. **It is the first thing to do.** |
| `idx` | 19.8 ms | `natLE`: a 32-term bignum sum, then a bignum division, per op | read only the ≤ 4 bytes the field needs | ≈ −18 ms | `idxOf`/`natLE` are unfolded in `FRLog`, `FRSoundnessStepA`/`C` and `FRVIRSpec`. Changing the definition breaks them; a twin in `evalOp` needs `idxOfF_eq` in `FRVIRSpec`'s simp sets. **That is S-0's or the integration agent's** (`FRSoundness*` is off-limits for me). |
| `askNode` | 22.9 ms | `nodeQ`'s list-built 72-byte query, and the trace's byte compare | build the query as a `ByteArray` | ≈ −10 ms (part of the 22.9 is the oracle's compare) | `nodeQ` is unfolded in `FRMerkle`, `FRSoundnessTruths`, `FRVIRSpec` and `FRXRead*`. **S-0 / integration.** |
| `tensorW` | 13.1 ms | 7 × 20-term `wAtT` sums per op | iterate the set bits of `j` only | ≈ −8 ms | `Impl.tensorWI` (`FRVerifierImplOps`, free), with `tensorW_meets` re-proved |
| `maskRows` | 8.5 ms | `filter` over `blockKinds` per row | precompute the per-row mask once (a table over the 2^14 rows) | ≈ −6 ms | `FRVIR.maskRows`, used only in `FRVIR` and `FRVIRTplTab` |

With the L-circ-local three (`dotKF`, `tensorW`, `maskRows`, ≈ −32 ms), the projection is
**≈ 221 ms (1.19×)**. Adding the S-0 pair (`idx`, `askNode`) gives ≈ 193 ms.

The child's walks also have to be the fused 16 ms: `walkABF` and its template form
(`walkRows_mle`). This is item 3's `walkAB` template, together with item 2's shared `Ĉ` for
`A₀`/`B₀`.

## 3. Remaining items, in order

1. **`T_V`.**
   - `dotKFF` (+ `dotKFF_eq`, `evalOp`'s `dotKF` case, `tplExt_ok`'s `dotKF` case rewritten by the
     lemma);
   - `tensorWI` by set bits;
   - `maskRows` by a precomputed mask;
   - measure V after each.
   - Then request `idx`/`askNode` from S-0/INT-3, with the fixes above.
2. **`R` in the §4.4 layout.**
   - `evalMT` restructured over the closed set `𝒞`: one `Ĉ(τ_lo, σ_lo)` per public matrix, shared
     by the instances and `R`'s u-rows. S-E5's `kprep3` is that computation per key; `Inc_f`,
     `Addr`, `A₀`/`B₀` and the pack/base patterns join `𝒞`.
   - The lemmas `replay_mle`, `plan_wf`, `replay_sound` (= `compileT_sound`), `inc_mle`,
     `eqTree_mle`.
2. **3.14 S-E items.**
   - `FRNodeLayout`: `wmSlot = 146`, `hEnd = 47,594`, `regions_fit`.
   - The mux's mirror addresses per A.6's pinned map (`wmB σ = wmBase + 146σ`; source `g` at block
     `wmB σ + ⌊g/4⌋`, positions `256(g mod 4) + [0, 256)`). This must be one function, used by the
     `linkWAll` template and the dump.
   - `mRowModel`: `R` at 259 k, `tplTargetSNode` 16 k, `tplLinkWAll` 15 k (the claim-5 row was
     already dropped in S-E6).
   - Templates:
     - `tplTargetSNode`;
     - `tplLinkWAll` (S-CN's `linkWAllI`);
     - `walkAB` (fused);
     - `rsWeight` (4 points muxed by kind);
     - `shiftTarget` (the bits of `bnd`);
     - `finPf`'s 745 `tensorW` (a zero-padded `keep` of arrays of different lengths).
4. **Re-dump** to `logs/S-E7/nodedump/` with every register bound, and report the rows per slot
   and per node and the blocks.

## 4. State left

- **No source file changed.** The worktree's L-circ modules are HEAD's (S-E6 committed).
- `logs/fr-build-e7` is ready, with the probes (`VTime`, `E5Eval`, `NodeDumpT`, `E6Rows`, …)
  using the full finals.
