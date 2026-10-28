# S-E8 (track L-circ): RESULT — the `T_V` kill test passes: V 169.4 ms, projected ≈ 195 ms (1.35×)

Stage S-E8, 2026-10-28, HEAD `0e93332`. Build tree `logs/fr-build-e8` (S-E7's tree; `snap.sh` now
also symlinks `FRVIR`, `FRVIRSpec`, `FRVerifierImplOps`). Logs are in `logs/S-E8/`. The journal is
`S-E8-JOURNAL.md`. Nothing is committed.

Every hot op of V now runs a fast twin, and each twin is proved equal to its reference. No
statement changed: `implC_meets`, `acc_eq` and `runSeq_runIR` have their HEAD statements, and only
proofs were repaired (§2). **V (N30) is 169.4 ms best on the VM, down from 231–235 ms**, which puts
the projected total at **≈ 195 ms, a 1.35× margin under the ≈ 264 ms cap**. The target was ≤ 230 ms
(1.15×), so the stop rule does not apply.

## 1. V per step (VM, one idle core, `vtime v N 21`: 21 warm `runSeq` runs)

| Step | best (ms) | median (ms) | Logs |
|---|---|---|---|
| Baseline (HEAD) | 235.0 / 231.2 / 232.2 | 241.8 / 238.5 / 250.9 | `vtime-N-0{a,b,c}` |
| 1. `dotKF` → `dotKFF` | 209.0 / 206.9 | 219.0 / 224.5 | `vtime-N-1{a,b}` |
| 2. `tensorW` → `tensorWF` (first version, `2 ^ _` divisors) | 209.7 / 210.7 | 215.3 / 217.9 | `vtime-N-2{a,b}` |
| 2. `tensorWF` with literal divisors | 206.2 / 204.9 | 213.1 / 210.5 | `vtime-N-2{c,d}` |
| 3. `maskRows` (one shared mask past row 1152) | 200.4 / 201.4 | 207.3 / 210.7 | `vtime-N-3{a,b}` |
| 4. `idx` → `idxOfF` | 177.8 / 183.7 | 186.0 / 204.0 | `vtime-N-4{a,b}` |
| 5. `askNode` → `nodeQF` | 172.3 / 172.1 | 184.2 / 179.8 | `vtime-N-5{a,b}` |
| **6. final** (+ `piDigestAt` → `digestAt`, controls) | **173.4 / 170.9 / 169.4** | **176.9 / 178.6 / 177.4** | `vtime-N-6{a,b,c}` |
| (experiment, not kept) + `piDigest` → `digestAt` | 164.1 / 167.3 | 172.6 / 173.2 | `vtime-N-6x-{a,b}` |

- `traceDigestF`, the quiet-core check, read 11.6–16.9 ms throughout, against S-E7's 12.0–13.0.
- Per-op profile (`prof-N-*.log`; the profiled run carries its own overhead):

  | Op | S-E7 | Final |
  |---|---|---|
  | `dotKF` | 30.7 | 6.9 |
  | `idx` | 19.8 | 0.8 |
  | `tensorW` | 13.1 | 8.4 |
  | `maskRows` | 8.5 | 2.1 |
  | `askNode` | 22.9 | 16.7 |

  Most of the remaining `askNode` time is the probe's own `randDigest` answers: 8.9 ms per 7,552
  (`nq-proto.log`). `runSeq` does not run them.
- **`askNode`, split** (`nq-proto.log`, per 7,552 queries): building the query took 10.1 ms with
  `nodeQ` and takes 2.9 ms with `nodeQF`. **The oracle's compare costs 0.12 ms.** `ByteArray`'s
  `DecidableEq` is `lean_sarray_dec_eq`, which is a memcmp.

**A finding to pass on:** `2 ^ k : ℕ` runs slowly in compiled code, ≈ 60 ns per power. The first
`wAtF` used `j / 2 ^ (8 b)`, and it was *slower* than the original (44.7 ms vs 43.7 ms per 1,627
ops). With literal divisors it takes 26.6 ms (`tw-proto3.log`). The same cost was the bulk of
`idxOf`, with its `natLE` sum of `256 ^ i` and its `2 ^ (i b)`. Hot code should use shifts and
literals.

## 2. Files and lines (core `loc.py`, code lines, HEAD → now)

| File | code | What changed |
|---|---|---|
| `FRVIR.lean` | 441 → 580 | Six twins, each with its `_eq` lemma. The `maskRows` body. Controls. `evalOp`'s `dotKF`, `idx`, `askNode` and `piDigestAt` cases run the twins. |
| `FRVerifierImplOps.lean` | 331 → 382 | `wByte`, `wB`/`wB_eq`, `wAtF`/`wAtF_eq`, `tensorWF`/`tensorWF_eq`, the `tensorW` controls |
| `FRVerifierImpl.lean` | 86 → 87 | `implCWith.tensorW := tensorWF`; the proofs of `implCWith_meets` and `implCWith_implT` (statements unchanged) |
| `FRVIRSpec.lean` | 1285 → 1285 | `exec_posHead` (+`dotKFF_eq`, `idxOfF_eq`), `exec_merkleOps` (+`nodeQF_eq`), `exec_posTail` (+`digestAt_eq`): simp sets only |
| `FRVIRTplExt.lean` | 337 → 337 | `tplExt_ok`'s `dotKF` case: `rw [hx', dotKFF_eq]` |
| `FRVIRTplTab.lean` | 194 → 194 | `tplMaskRows_ok`: `maskRows_eq, maskOf` in its simp set |

`FRVIR.lean` is now 932 lines in total. No other module was touched; `FRX*`, `FRSoundness*`,
`FRShift`, `FRVIRFinals*` and `FRNodeLayout` are HEAD's. The twins:

- **`fAt`/`dotKFF`.**
  - `fAt b o` reads an F in place: `fAt_eq : fAt b o = F.ofBytes (bytesAt b o 16)`.
  - `dotKFF` is one tail-recursive loop over `min (col.size / 16) w.size` rows:
    `dotKFF_eq : dotKFF w col = dotKF w col`.
- **`wAtF`/`tensorWF`.**
  - 60 byte tables of 256 F each, computed once. `wAtF` makes 3 lookups instead of a 20-term sum:
    `wAtF_eq : wAtF v j = wAtT v j`.
  - `r_v · Ŵ` becomes `smulF`, two F products instead of a K product:
    `tensorWF_eq : tensorWF j r = tensorWI j r`.
  - Iterating over `j`'s set bits, as the brief proposed, does not pay. `wAtT` is ≈ 30 % of the op;
    the K products are the rest (`tw-proto.log`).
- **`maskRows`.**
  - `maskOf kindW k` is the old per-row sum, verbatim.
  - The body computes `maskOf` for rows `≤ pinEnd = 1152` and one shared value past that row:
    `isZeroRow_of_gt`, `maskOf_of_gt`.
  - The A.8 reading is the lemma `maskRows_eq : maskRows kindW rowW = rowW.mapIdx fun k w => w *
    maskOf kindW k`.
- **`idxOfF`.** The definition is `if b ≤ 24 then dWin a (i b / 8) >>> (i b % 8) % (1 <<< b) else
  idxOf b a i`.
  - `dWin` is four bytes, zero past byte 32.
  - **`idxOfF_eq : idxOfF b a i = idxOf b a i` holds for every `b`, `a`, `i`**, with no condition on
    the parameters.
  - Proof: `natLE_sum`, `sum_lt_pow`, `natLE_split`, then `Nat.add_mul_div_left` and
    `Nat.add_mul_mod_self_left`.
  - `idxOf`, `natLE` and `nodeQ` are unchanged.
- **`nodeQF`.** The query is built from arrays: `nodeQF_eq : nodeQF i l r = nodeQ i l r`.
- **`digestAt`.** One 32-byte slice: `digestAt_eq : digestAt q o = bytesAt q o 32`.

## 3. The projection

The additions are S-E7's: `linkWAll` 1.9 ms, the remaining templates ≈ 3 ms, `R`'s closed forms
≈ 5 ms, and the child's fused walks 16 ms, which item 7 confirms. They total 25.9 ms.

| Base | V | Projected | Margin vs ≈ 264 ms |
|---|---|---|---|
| final best | 169.4 | **195.3 ms** | **1.35×** |
| final, middle best | 170.9 | 196.8 ms | 1.34× |
| final, median of medians | 177.4 | 203.3 ms | 1.30× |
| with the `piDigest` request (§6.1) | 164.1 | 190.0 ms | 1.39× |

**Item 7: the child's walk.**
- The prototype is in `cw-proto.log`. It computes `Â₀(τ_lo, σ_lo)` and `B̂₀(τ_lo, σ_lo)` from two
  `eq` tables over the block's 14 row bits and 14 column bits (3.2–5.0 ms each), then one fused
  `walkImpl` (8.9–9.3 ms).
- Total: **15.2 / 15.8 / 17.8 ms**.
- The two values are computed once, at the node's single point, and shared by both slots. That is
  the blueprint's "16 ms fused", and V's own `walkAB` costs the same 8.9 ms.
- Two ways to make the eq tables cheaper. Neither is measured:
  - build them by `t − t·x`, which halves the products;
  - extend `evalMT`'s `tbOf` prefix tables, which already reach 12 and 13 bits, to 14.

  Either would bring the walk to ≈ 12–13 ms.

## 4. Controls

The controls are kernel-checked by `decide +kernel` through the twins. They sit in the twins' own
modules, so `lake build FR` checks them; `FRVIRTplControls` is not imported by `FR` (§6.4). Each
negative control shows that the `_eq` statement has teeth: a broken twin would fail it.

| Twin | (+) | (−) |
|---|---|---|
| `dotKFF` | `dotKF_pos : dotKF #[1] col1 = 1` | `dotKF_neg`: the loop one row short is not `dotKF` on a 2-row column |
| `idxOfF` | `idxOf_pos`: bits `[8,12)` = 1, `[12,24)` = 32, and past the end = 0, on the digest `0…31` | `idxOf_neg`: the window one byte late is not `idxOf` |
| `nodeQF` | `nodeQ_pos`: size 72, byte 6 = the level | `nodeQ_neg`: swapping the children changes the query |
| `digestAt` | `bytesAt_pos`: a digest inside `q`, and one zero-padded past its end | `bytesAt_neg`: offset 8 ≠ offset 9 |
| `maskRows` | `maskOf_pos`: row 0's mask is the 4 non-pinning kinds; past `pinEnd` all 9 | `maskOf_neg`: row 1100 differs from the shared value, so `pinEnd` cannot be lowered |
| `tensorWF` | `tensorW_pos`/`tensorWF_pos`: `j = 0` gives `1 + u` | `wByte_neg`: the third byte table's entry for `2^16` is `Ŵ_0(D[2^16]) ≠ 0`, so a twin that drops bits 16–19 is wrong |

The positive content of each twin is its `_eq` theorem, which has no hypotheses.

## 5. Build, kernel, audit

- **`lake build FR` is green** in `logs/fr-build-e8` (`build-FR.log`: 2,324 jobs, 0 errors).
- **Axioms** (`axioms.log`, 28 declarations): `acc_eq`, `implC_meets`, `implCWith_meets`,
  `implCWith_implT`, `runSeq_runIR`, `tplExt_ok`, `tplMaskRows_ok`, every `_eq` and every control.
  They use only `propext`, `Classical.choice` and `Quot.sound`.
- **Source rule:** 133 files, 0 findings.
- **Sequential profiles** (`-DElab.async=false --profile`, one core; `prof-FR*.log`):

  | Module | wall | kernel |
  |---|---|---|
  | `FRVIR` | 18.2 s | 1.97 s (the controls ≈ 1.2 s) |
  | `FRVerifierImplOps` | 14.9 s | 3.94 s (`wByte_neg` 2.7 s) |
  | `FRVIRSpec` | 52.6 s | 5.24 s |

  A first `tensorW` control through `wByte` cost 7 s of kernel, because the kernel builds a
  256-entry `Array.ofFn` for each entry. I replaced it.

## 6. Deviations and open questions

1. **Request to S-F (`FRVIRFinalsSF`): add `digestAt_eq` to the `simp only` of `flag_finB'`.**
   - That is the only blocker for running `piDigest` as `digestAt`. I checked the repair on a
     private copy in the build tree, then reverted it.
   - The gain is **≈ −5 ms of V** (164.1 / 167.3 ms best).
   - Once the repair is in, L-circ switches `evalOp` and adds `digestAt_eq` to
     `FRVIRSpec.exec_merkleOps` and to the `absorb` case. I have tested that too.
2. **Blocked twins, ≈ −2.5 ms each (estimates):**
   - **`eqTable`** by `t − t·x`. `FRVIRCompile` unfolds `eqTab`, and that module is not on my
     list. `FRVIRFinalsSF`/`SG` state `eqTab` via `pr_op`.
   - **`piElem`/`piElemK`** by `fAt`. `FRVIRFinals.pe`, `FRVIRFinalsSF.sv` and
     `FRVIRFinalsSG.finV` are closed by `rfl` over `bytesAt`.
3. **`maskRows` is a body change, not a twin.**
   - `FRVIRFinals.relLc` states `maskRows`, and `flag_finLc` closes by
     `simp only [evalOp …]; exact ⟨_, rfl⟩`, so a twin would break it.
   - The A.8 reading is now the lemma `maskRows_eq`; `maskOf` is the old body.
4. **`FRVIRTplControls` is not imported by `FR.lean`**, so `lake build FR` does not check its
   controls. Orchestrator: import it, or move its controls.
5. **`tensorW`'s fix differs from the brief.** It uses byte tables and `smulF`, not set bits (§2).
6. **The `piDigestAt` twin gives no measurable gain on its own** (871 ops). I kept it because it is
   the twin the `piDigest` request needs.
7. **What remains in V.**
   - `evalM` is 57.7 ms, the largest op.
   - Next: `walkAB` 8.7, `tensorW` 8.4, `mulK` 7.7, `piDigest` 7.2, `rsWeight` 6.9, `dotKF` 6.9,
     `phiRS` 6.3, `eqTable` 5.2 ms.
   - Apart from `piDigest` and `eqTable`, these are field arithmetic (S-A's, final) or `evalM`'s
     structure. I found no clean twin among them.
   - `perf` is unavailable (`perf_event_paranoid = 4`), so I did not profile inside `evalM`.
   - `FRVIRTplFast.hfac` still computes `x % 2 ^ (S − A)` per instance, ≈ 3 k calls. I estimate
     ≈ 0.4 ms; not changed.
8. **Blueprint (orchestrator).** Update §10 changes 21 (D) and the `T_V` row of the margins table:
   - V is 169.4 ms VM measured;
   - the projection is ≈ 195 ms, 1.35×;
   - the FR-D2 frontier is closed without (e).
