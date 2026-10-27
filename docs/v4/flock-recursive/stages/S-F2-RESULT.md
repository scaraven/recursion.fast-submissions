# S-F2 RESULT: the concrete `OpImpl`, `specC`, `Meets`, `V`, and the compiled-`V` probe

Track L-cert. Branch `v4/flock-recursive`, HEAD `c8e1869`. Built in `logs/fr-build-cert` (HEAD's
other-track modules; L-cert's files as symlinks), in the 16 GB scope. Not committed.

## 1. What was built

| File | Code lines (`loc.py`) | Content |
|---|---|---|
| `lean/FRVerifierImpl.lean` (new) | 454 (39 theorems) | per-op implementations `…I`, specifications `…S`, `…_meets`; `implC`, `specC`, **`implC_meets`**; `finC`, **`VC`**; controls |
| `probe/fr-vtime/` (new, outside the entry) | `VTime.lean`, `gen.sh` | `vtime v L/P/N` (V on a synthetic proof, warm `runSeq`), `vtime prof K` (per-op profile), `vtime ops`, `vtime rows` |

No other track's module was edited.

### Per op

"Exact" means the spec is the owner's definition. "Gap" means `OpImpl`'s signature cannot carry it
(§4).

| Op | Implementation (`implC`) | Specification (`specC`), owner's definition | `Meets` |
|---|---|---|---|
| `lagrangeS` | Lagrange weights `numL · den`; denominators and `P^z`'s weights on `S` are closed tables (`den127`, `denL`, `lamAtS`) | `(interpolateAt node127 (z2Vals …) λ, interpolateAt lNode pz λ)` (FRSkip; A.8 3.8 order: `vals[0…63]` = `P^z` on `Λ`) | `lagrangeS_meets` (exact) |
| `eqZ` | 64 weights at `λ` × `eq(ρ₁, bit 6)` | `lagrangeWeight sNodeF λ (i mod 64) · eq(ρ₁, bit 6 of i)` | `eqZ_meets` (exact) |
| `rowW` | 64 weights ⊗ `eqTable` of 8 coordinates | `FRSpartan.rowW` (p = 8) | `rowW_meets` (exact) |
| `phiRS` | `phiApply` | `FRRingSwitch.Phi` | `phiRS_meets` (exact) |
| `shiftEq` | `shiftPair` | `Σ_{u,v} eq(τ,u) succT u v eq(v,r)` (FRShift) | `shiftEq_meets` (exact; equal lengths) |
| `tensorW` | the novel-basis table `wTab` (closed), `prodTo` | `FRRSEval.tensorTwin D 20` (S-D) | `tensorW_meets` (exact) |
| `rsWeight` | `c_k(r″)` once over F; `eq` as `Π(1 + a + b)` (char 2) | `Σ_j κ^j Σ_{k<128} c_k(r″) eqPts(r_j^{2^k}, ρ)` (`weight_mle`'s right side, `phiTable`) | `rsWeight_meets` (exact; `|r″| = 7`) |
| `walkA`, `walkB` | `Eval.walkImpl` | `Eval.walkSpecA/B` (S-E2) | `walkA_eq`, `walkB_eq` (S-E2) |
| `kindInd` | `Eval.kindIndImpl` | `Eval.kindIndSpec` | `kindInd_eq` (S-E2) |
| `evalM` | `Eval.evalMImpl fin` (S-E2's sparse sum) | `evalRowsSpec 21 23 (nodeRows fin)` | `evalM_eq` (S-E2). **Not runnable** (§3.3) |
| `evalL` | `Eval.evalLImpl lRows` | `evalRowsSpec 15 23 lRows` | `evalL_eq`; `lRows` is a parameter (no module fixes L's rows) |
| `evalMK` | `sparseEvalK` (new) | `matMLEK`: `Σ_{x,y} eq(τ,x) M[x][y] eq(σ,y)` over K (new) | `evalMK_meets` via `sparseK_eq` (exact). Not runnable, as `evalM` |
| `slotW` | two `eqTable`s of 10 coordinates, 256 terms | `Σ_{σ<256} eq(θ,σ) eq(r, base_s + σ)`: `slotW_mle`'s right side, P2 §7.5 (4)'s reading; bases 256 (Out), 520 (`d`), 0 (`h_in`) | `slotW_meets`. **Gap**: slot 1 is a leaf's `d`; the node's In slot needs the kind |
| `shiftTarget` | `Π τ_l · d̃(h) + κ_s · d̃(s)`, `d̃` over the digest bits (`bitF`, A.7) | `FRShift.shiftTarget (θ) (τ) κ_s sV hV` with the boundary digests as bit tables | `shiftTarget_meets` (exact for every `κ_s`). **Gap**: the op has no `κ_s`; `implC` takes a stand-in `κs₀` |
| `targetS` | `Σ_hi eq(r_lo, hi) E_chain(σ + 64 hi)` over a closed `chainTab` | `FRPubTarget.targetS` over `8 + b` variables with the leaf's `E` (every block a chain block), any `b` | `targetSLeaf_meets` (exact for leaves). **Gap**: the node's `E` (A.6, per-block patterns) is not written, and the op gets no kind |
| `linkW` | `0` | `0` (leaf: no families, P2 §7.5 (7)) | trivial. **Gap**: the node's families are not defined in Lean |
| `kindFoldWeight` | `0` | `0` | trivial. Not used by revision 3.9's `gen`. Its signature returns F from a K point (§4) |

**`implC_meets fin lRows κs₀ : (implC fin lRows κs₀).Meets (specC fin lRows κs₀)`**.

### `V`

`finC pf := sfFinals finP pf` and `VC pf lRows κs₀ := Vwith (implC (finC pf) lRows κs₀) (finC pf)`.
`VC` is parametric in three things:

- `finPf` (S-G1d; not in HEAD);
- L's rows (S-E2);
- the stand-in `κs₀` (S-0: `shiftTarget` needs the operand).

`FRVerifier`'s `acc_eq`, `complete`, `V_W_sound` apply to it unchanged.

## 2. Build and kernel times

**Measured** (`logs/S-F2/profile-FRVerifierImpl.log`): sequential, `lake env lean
-DElab.async=false --profile`, 16 GB scope.

| Module | wall | import | elaboration | tactic exec. | simp | type checking (kernel) | peak RSS |
|---|---|---|---|---|---|---|---|
| `FRVerifierImpl` | 11.5 s | 3.61 s | 0.35 s | 1.19 s | 0.74 s | 0.90 s | 2.8 GB |

**Checks:**

- Axioms (`logs/S-F2/axioms.txt`): all 16 audited statements (`implC_meets`, every `…_meets`, the
  controls) depend on exactly `propext`, `Classical.choice` and `Quot.sound`.
- Source rule: 72 files, 0 findings. The build has no warnings.
- `ctrl_lag_self` needs `set_option maxRecDepth 4000`. The reason is the instance check between F's
  `1` and `Field`'s `1`.
- Proof note: `rw`'s closing `rfl` tries `whnf` on sums over `Fin 64`/`Fin 127` and on the closed
  tables, and times out. The proofs use `rewrite`, and `congrArg (Array.ofFn (n := …))` with the
  size explicit.

## 3. The compiled-`V` probe (`probe/fr-vtime`, VM, one core, `taskset -c 9`, 16 GB scope)

**Input.** A synthetic SNARK proof:

- `piSize` = 755,680 random bytes, kind byte `L`/`P`/`N`;
- an oracle that answers each query with a fresh pseudo-random digest. Its trace (8,874 entries,
  1,366,767 bytes) is replayed with `runSeq`, as `acc` does.

**Why a synthetic proof times a real one.** `gen` is straight-line: every op runs, and assertions
only clear the flag. The run therefore does the same work on any `piSize` input.

**Real leaf proof: not used.** It would need the Rust prover built and run through `rf-oracle`, and
it would exercise the same op list.

`finPf` is `pending` (S-G1d), and `evalL` runs on no rows.

### 3.1 HEAD as it is: 283 s

`logs/S-F2/prof-N-1.log`. The time goes to the proof readers:

| Op | count | time |
|---|---|---|
| `piDigest` | 7,554 | 233 s |
| `piDigestAt` | 871 | 27 s |
| `piElem` | 1,025 | 15 s |
| `piElemK` | 227 | 6.8 s |

**Cause: `FRTranscriptDefs.bytesAt` reads `q.data.getD (o + i) 0`.** In compiled code,
`ByteArray.data` copies the whole 755,680-byte proof into a boxed `Array UInt8` for every byte read.
`kindSel` (`inp.π.data.getD 0 0`, 2.6 ms), `VProg.kindOn` and `FRFormat.kindOf`
(`π.data[0]?`) each make one such copy per run.

### 3.2 With `bytesAt` reading `q.get! (o + i)`

This is measured in a private copy, `logs/S-F2/src-fast`: `implemented_by` on `bytesAt`, probe only.
The definition in the entry is unchanged.

| Kind | warm `runSeq`, best / median of 9 | `traceDigestF` | peak RSS |
|---|---|---|---|
| N30 | **182.7 / 193.4 ms** | 12.5 ms | 134 MB |
| P30 | 177.4 / 181.1 ms | 12.6 ms | 133 MB |
| L32 | 177.6 / 181.9 ms | 14.5 ms | 133 MB |

Logs: `logs/S-F2/vtime-{N,P,L}-final.log`.

**Against the cap:**

- `acc` on the VM costs about 195 ms (N30: 182.7 + 12.5). `SigOk` (≈ 0.3 ms) is not included.
- The runner's `T_V` cap is ≈ 206 ms. With the VM ≈ 1.28× slower, the VM-equivalent cap is
  **≈ 264 ms**.
- That leaves **≈ 69 ms** on the VM for what is not yet in the program: `finPf`, the real `evalL`
  rows and the templated `evalM`/`evalMK`.

**Per-op profile, N30** (`logs/S-F2/prof-N-final.log`; 212.8 ms including the probe's per-op timers):

| Op | count | time |
|---|---|---|
| `dotKF` | 871 | 26.3 ms |
| `askNode` | 7,552 | 22.2 ms |
| `idx` | 871 | 19.7 ms |
| `walkA` + `walkB` | 2 | 30.2 ms (the walk runs twice) |
| `mulK` | 16,060 | 8.0 ms |
| `maskRows` | 1 | 7.3 ms |
| `piDigest` | 7,554 | 6.9 ms |
| `phiRS` | 512 | 6.3 ms |
| `tensorW` | 882 | 4.6 ms |
| `eqTable` | 8 | 4.4 ms |
| `lagrangeS` | 1 | 2.8 ms |
| `rowW` | 1 | 2.8 ms |
| `targetS` | 1 | 1.7 ms |

**Micro-timings of ops `finPf` will add** (`logs/S-F2/ops-fast.log`):

- `rsWeight` (4 claims, 23 coordinates): 7.6 ms. It took 16.4 ms before the char-2 `eq` and the
  shared `c_k`.
- `tensorW`: 5.8 µs per call.

**Optimisations in this module, with the per-call times before and after:**

| Change | Op | Before | After |
|---|---|---|---|
| node table `xT` (`xS` was a `Finset` sum over `Fin 7` per call) | `lagrangeS` | 127 ms | 3 ms |
| | `eqZ` | 13 ms | 0.5 ms |
| | `rowW` | 16 ms | 2.5 ms |
| folds instead of `Finset` sums and products | `tensorW` | 23 µs | 5.8 µs |

### 3.3 `evalM`/`evalMK` are not runnable as specified

`Layout.nodeRows finC` did not finish in 600 s (`vtime ops`/`rows`; a second run was stopped after
17 min at 155 MB).

**Cause: `FRVIRCompile.CS.add` appends `cs.rows ++ o.rows` on `List`s in a `foldl`.** That is
quadratic in the ≈ 1.2 M rows per slot. The same holds for `imp` and `fors`.

Even with linear compilation, a sparse sum over the node's ≈ 2.4 M rows needs at least 2 products
per entry with split `eq` tables, which is seconds. **The templated evaluation (S-E2 deviation D-6,
§4.4) is needed for `T_V`.**

## 4. Interface gaps and deviations (with reasons)

1. **Kind-dependent ops** (S-0's `FRVIR`). `targetS`, `slotW` (map 1) and `linkW` depend on the
   proof's kind. `evalOp` has `κ`, but `OpImpl`'s fields do not receive it, and P30 and N30 have
   the same operand lengths.
   - **Request:** give these three fields a `Kind` argument and pass `κ` in `evalOp`.
   - Until then, `implC` fills them with the leaf kinds' functions. These are exact for L32/P30
     only. The node's `targetS`, `linkW` and In slot are S-C's (A.6's per-block `E` patterns, the
     link families).
2. **`shiftTarget` has no `κ_s` operand.** A.9 `finSh` (i) and the native leaf verifier need
   `eq(τ, 1…1)·h̃(θ) + κ_s·s̃(θ)`. `shiftTargetI κs` and its proof take `κ_s`; `implC` takes a
   stand-in `κs₀`. **Request (S-0):** pass S1's coordinate 28.
3. **`kindFoldWeight`.** A.8 types it `AF, F, AK → F`, but `Ŵ_β` at a K point is in K. Revision
   3.9's `gen` does not use it. I gave it `0` and did not write a spec. **S-C/S-0:** drop it or fix
   the signature.
4. **`slotW`'s reading** follows P2 §7.5 (4): `σ < 256` as a 10-bit index, with the sum restricted
   to `σ < 256`. The bases (256 Out, 520 leaf `d`, 0 `h_in`) are A.6's.
5. **`targetS`'s point.**
   - `r_lo = (ρ₁ … ρ₇, Z1's first coordinate)`, per A.2 (the native `pe_on_s(&r[..8])`).
   - The spec quantifies over `b` block bits. For a leaf the result does not depend on `b`, and
     `specC` uses `b = 16`.
6. **`evalM`/`evalL`** are S-E2's, unchanged. `evalMK` is new (spec and proof), the same sparse
   form over K.
7. **`V` is `VC pf lRows κs₀`, parametric.** S-G1d's `finPf` is not in HEAD, L's rows are not
   defined, and `κs₀` stands for the missing operand.

## 5. Controls (§5.6)

| Control | Shows |
|---|---|
| `ctrl_lag_self` (+) | The computed Lagrange weights at node `i` give `1` at `i`. They are the Lagrange basis, not just equal to some expression. |
| `ctrl_lag_other` (−) | They give `0` at another node. |
| `ctrl_slotW_hit` (+) | `slotWI s` at the Boolean points `θ = σ₀`, `r = base_s + σ₀` is `1`. |
| `ctrl_slotW_miss` (−) | It is `0` when `r` is the position of another slot index. |
| `…_meets` | Each implementation equals its owner's definition (not itself). |
| probe | `implC` runs on full-size inputs of all three kinds (§3). |

## 6. Remaining, by owner

- **S-0** (`FRTranscriptDefs`, `FRVIR`, `FRFormat`). Without the first item, `V` takes 283 s.
  - `bytesAt` with `q.get! (o + i)` (or `q[o + i]?.getD 0`), with its lemmas adjusted;
  - the `π.data` reads in `kindSel`, `kindOn`, `kindOf`;
  - `Kind` arguments for `targetS`/`slotW`/`linkW`, and the `κ_s` operand of `shiftTarget`;
  - optionally one `walkAB` op, saving one 15 ms walk.
- **S-E2.**
  - Linear `compileMux` (e.g. rows accumulated reversed or in an `Array`).
  - **Templated `evalM`/`evalMK`/`evalL` (D-6)**, proved equal to `evalRowsSpec`/`evalMKS`.
  - L's row list. After that, `implC`'s `evalL` takes it in place of the parameter.
- **S-C.** The node's `targetS` (`E` for the nine block kinds, with per-block patterns), the
  node's `linkW` (families), the node's In slot map, and `kindFoldWeight` (item 3).
- **S-G1d.** `finPf`, which then replaces `VC`'s parameter.
- **Hot spots for `T_V` outside this module:** `dotKF` 26 ms, `askNode` 22 ms, `idx` 20 ms,
  `maskRows` 7 ms.
- **`FR.lean`** should import `FRVerifierImpl` (whoever owns the aggregator).

## 7. Open questions

1. Who rules on items 1–3 of §4? They change `FRVIR` and `FRVIRFinals.finSh`, and the S-0 proofs
   that read those fields.
2. The ≈ 69 ms VM margin (≈ 54 ms on the runner) must cover `finPf` and the templated `evalM`,
   `evalMK` and `evalL`. If it is too tight, the hot spots in §6 are the next targets.
