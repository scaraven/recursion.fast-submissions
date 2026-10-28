# S-T1 journal (track: verifier time; V for N30 back under its cap)

Build tree `logs/fr-build-T1` (INT-5's copied; `snap.sh` with `MINE="FRKindWeight FRVerifierImplOps
FRVerifierImpl FRVIR"`: HEAD `9d1f906` for every other module). Logs in `logs/T1/`. Every lean/lake
and probe command in the 16G scope with a `timeout`. Nothing committed.

## Baseline (HEAD `9d1f906`)

- `vtime-N-0a` (core 21, load ≈ 4–7 from S-N1/S-G10 builds): best 237.2 ms, median 247.8 ms.
- `prof-N-0a` (core 23): evalM 96.4, **rsWeight 38.6**, askNode 18.2 (most of it the probe's own
  `randDigest`), walkAB 16.2, tensorW 8.7, mulK 8.1, dotKF 7.3, eqTable 7.3, phiRS 7.2 ms.
- Basic costs (`basic-0`, tight loops): F mul ≈ 100 ns, F sq ≈ 20 ns, K mul ≈ 350 ns, `smulF` ≈ 190 ns,
  adds 5–9 ns. `KW.kwI` ≈ 256 µs per stage call (≈ 640 K products).
- `rsw-info`: in the N30 run all four claim points are in F (every coordinate has `f₁ = 0`); ρ is not.

## Step 1: `rsWeight`'s claim 2 by dyadic blocks (`wEvalKF`), the other claims in F (`wEvalCF`)

Idea. Per stage, `kwS = Σ_t w(t) Π_l e_l(t_l)`. Each item is two prefix sums (char 2); a prefix sum
`[0, x)` is the sum over the dyadic blocks of its set bits (`psum_cubes`); an even pattern is the
run minus the odd one (`itemTerms`), so only odd pattern blocks remain. All items' blocks (417),
merged by key and level, are 58 + 23 keys (closed constants `skelM`, `skelP`). A block's fixed-bit
product is `ofF(F part) · (K part)`: the F part is the claim point's (stage-dependent, but stage `k`'s
is stage 0's `2^k`-th power: one F squaring per block per stage), the K part ρ's (fixed). Per stage:
one `smulF` per block, two Horner sums over the levels (`s_l = 1 + q_l + ρ_l`), `eq(q_hi, ρ_hi)`.
The other three claims: the point squared in F (`F.sq`, 20 ns) instead of a K product.

Probe (`kf-3`, 20 random inputs, equal to the reference on all): per call `wEvalKC` 40 ms →
`wEvalKF` 4.3 ms; `wEvalC` 1.7 ms → `wEvalCF` 1.1 ms.

Proof chain (all kernel-checked, no statement of HEAD changed):
- `FRKindWeight`: `psum_cubes`, `psum_succ_one`, `psum_two_mul`, `item_terms` (char 2), `termV_keys`,
  `kwS_items` (kwI_eq's tail, now shared; kwI_eq re-proved through it), `kwS_keys`, `keys_grp`
  (fibres by level, `mergeSort_perm`, `mergeAdj_sum`), `keyW_split`, `prod_fix_ofF`, `gsum_mkEnt`,
  `hornerK_eq`, **`kwS_fast`** (one stage).
- `FRVerifierImplOps`: `fold_sim`, **`wEvalCF_eq`**, `mkEnt_sq` (Frobenius on F), `sqG_gmK`,
  `kf_fold`, **`wEvalKF_eq`**, `ofF_f0`, **`rsWeightF_eq : rsWeightF = rsWeightI`** (no hypotheses).
- `FRVerifierImpl`: `implCWith.rsWeight := rsWeightF`; `implCWith_meets` re-proved
  (`rsWeightF_eq.trans rsWeight_meets`), text unchanged.

Measured: `prof-N-1a` rsWeight 38.6 → **8.3 ms**; V `vtime-N-1a` 200.0 ms best (median 211.3),
`vtime-N-1b` 203.8 ms best. Interleaved A/B under load ≈ 8 (`vtime-N-s1-*`): HEAD 233.8 / 244.3,
T1 210.9 / 213.8.

Controls: `cubesOf_pos/neg`, `allKeys_counts` (417 blocks, none on the even side), `plan_even`,
`rsF_guard_pos/neg`. Note: `decide +kernel` cannot evaluate `skelM`/`skelP` (`List.mergeSort` is
well-founded recursion), so the merged counts 58 + 23 are a probe measurement (`kf-*`).

## Coordinator message (core PR #20)

`T_V` is now scored continuously (`κ·max(x, x³)`, `x = V/v_ref + |π|/2 MiB`); the kill rule no
longer applies. Continue with the best ms per unit of effort.

## Step 2: `tensorW` at F points (`tensorWG`)

`dom-0`: 882 of 1,627 `tensorW` points are in F (dotKF's weights never; mulK's left operand in
16,011 of 16,406 ops, but `mulK` is an `evalOp` case that `FRVIRCompile`/`FRVIRFinalsSG` unfold:
not touched). `tensorWG` runs the product in F when every coordinate has `f₁ = 0`.
`tg-0`: 1,627 calls at an F point 5.76 → 2.58 ms. `tensorWG_eq : tensorWG = tensorWF` (no
hypotheses); `implCWith_meets`, `implCWith_implT` re-proved. Profile tensorW 8.9 → 7.0–7.2 ms.

## Step 3: `phiRS` squarings by `F.sq` (`phiRSF`)

`phiApply` squares with `a * a` (≈ 100 ns); `F.sq` is ≈ 20 ns. `phiRSF` (`sqItF`, `frobMapF`),
`phiRSF_eq : phiRSF = phiRSI`; `ImplT.phiRS` is discharged by `funext phiRSF_eq`.
Profile phiRS 6.2 → 2.4–2.5 ms.

## Step 4: `evalM`'s key preparation in one pass (`kprep3F`)

`em-0`: in `evalMT`, `tbOfK` 5.7 ms, `kprep3` (90 keys × 3 matrices) 33 ms, `nodeV3` ≈ 85 ms.
Counts (`ks-0`): 20,318 key rows, 107 k terms. `kprep3` walked each key's rows 9 times (3 `zipIdx`
allocations per matrix). `kprep3F`: one pass over the rows for the three matrices (`kpGo`), each row
form read once (`tStep`); `inpNF` without `zipIdx`. Proofs: `kp1_eq`, `kpGo_eq`, `foldl_zipIdx_fst`,
`inpNF_eq`, **`kprep3F_eq`**; `kprep3_eq` re-proved (text unchanged). `kprep3` 33.7 → 21.6 → 19.3 ms;
`nodeV3` ≈ 85 → 71–75 ms.

## Step 5: the patterns' inner sums shared by the slots (`inr3`, `ectx3W`)

`ctx-0/1`: both slots have the same shared-form numbers; `inr3` costs 2.8 ms per slot. `nodeV3`
computes it once when the numbers agree (`nodeV3_slots`; `nodeV3_eq` re-proved, text unchanged;
`ectx3` is `ectx3W … (inr3 …)`, so `FRNodeDag` is unchanged). Below the run-to-run noise of
`nodeV3`; kept (−2.8 ms by the part's own timing).

## Not taken

- `mulK` with an F operand (≈ −2.5 ms): `evalOp` case unfolded by `FRVIRCompile` and S-G's finals.
- `eqTable` by `t − t·x` (≈ −2.5 ms): blocked as in S-E8 (FRVIRCompile, FRVIRFinalsSF/SG).
- `preTabs` by halving (≈ −1.3 ms; ≈ −3 ms with `tbOf` sharing `slo`/`tlo`): proof work in `tbOf`.
- one constant `one·E(one) + sv` per key and slot (≈ −3 ms): `slotV3_eq`'s default-value cases.
- `walkAB` (8.7 ms) is `FRBlake2sWalk`'s walk; `dotKF` weights are K; `rsWeight` is now ≈ 8 ms
  (3 × 1.1 `wEvalCF` + 4.3 `wEvalKF`), near its product floor (31 K products of Horner, 81 `smulF`
  per stage).

## Final

`lake build FR` green on HEAD `7088398` + the five modules (2,407 jobs, `build-FR-1.log`); axioms
(`axioms.log`, 44 names) clean; source rule 183 files, 0 findings.

