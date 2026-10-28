# S-T1 RESULT: verifier time. V (N30) 228.4–228.9 → 177.9–180.9 ms best on the VM (−48 to −51 ms)

Stage S-T1, 2026-10-28. HEAD `9d1f906` at the start, `7088398` at the end. The commits in between
change only soundness and extractor modules, not V's code. Build tree `logs/fr-build-T1`: INT-5's
tree, copied. `snap.sh` takes HEAD for every module except the five below, which are symlinked to the
worktree. Logs are in `logs/T1/`; the journal is `S-T1-JOURNAL.md`. Every lean, lake and probe
command ran in the 16G scope with a `timeout`. Nothing is committed.

No statement changed. `acc_eq`, `implC_meets`, `implCWith_meets`, `implCWith_implT`,
`rsWeight_meets`, `kwI_eq`, `wEvalKC_eq`, `evalMT_eq`, `kprep3_eq`, `nodeV3_eq` and `slotV3_eq` keep
their text. Every fast version is a twin with an `_eq` lemma that has no hypotheses, or a proof
repair.

## 1. V per step (VM, 21 warm `runSeq` runs; best / median, ms)

| Step | run | best | median | log |
|---|---|---|---|---|
| HEAD | core 21, load ≈ 5 | 237.2 | 247.8 | `vtime-N-0a` |
| 1. `rsWeight`: claim 2 by dyadic blocks, other claims in F | core 21 / 23 | 200.0 / 203.8 | 211.3 / 214.9 | `vtime-N-1a/1b` |
| 1, A/B, load ≈ 8 | HEAD / T1 | 233.8, 244.3 / 210.9, 213.8 | | `vtime-N-s1-*` |
| 2. + `tensorWG`, 3. + `phiRSF`, 4. + `kprep3F` | | | | profiles below |
| **1–4, A/B, load ≈ 1–2** | **HEAD / T1** | **228.9, 228.4 / 180.9, 177.9** | 241.8, 238.4 / 185.3, 187.6 | `vtime-N-s4-*` |
| 1–5, final, A/B, load ≈ 6–10 | HEAD / T1 | 239.7, 240.4 / 176.3, 186.8 | 255.1, 264.9 / 209.1, 212.4 | `vtime-N-fin-*` |

The A/B runs (`logs/T1/ab.sh`) time HEAD's binary (`vtime-head`, INT-5's build of `9d1f906`) and
T1's at the same time on two cores, then swap the cores.

**Per op** (`prof-N-*`, one profiled run, ms):

| Op | HEAD (`prof-N-0a`) | final (`prof-N-fin`) |
|---|---|---|
| `evalM` | 96.4 (83–89 in quieter runs) | 72.5 |
| `rsWeight` | 38.6 | 8.2 |
| `walkAB` | 16.2 (8.8–9.7 in later runs) | 8.7 |
| `tensorW` | 8.7 | 7.0–8.5 |
| `phiRS` | 7.2 | 2.5 |
| `mulK` / `dotKF` / `eqTable` | 8.1 / 7.3 / 7.3 | 8.1 / 7.9 / 4.9 |
| `askNode` | 18.2 | 15.7 (mostly the probe's own `randDigest`; `runSeq` does not run it) |

Inside `evalMT` (`em-*`): `kprep3` 33.7 → 19.3 ms, `nodeV3` ≈ 85 → 71–75 ms, `tbOfK` 5.7 ms
(unchanged).

## 2. The projection

These figures use the quiet A/B run (177.9–180.9 ms).

| | VM | 7763 (÷ 1.19) | V / v_ref (206.0 ms) |
|---|---|---|---|
| HEAD + 18.5 ms of additions | 247.2 | 207.7 | 1.01 |
| **T1 + 18.5 ms of additions** | **196.4–199.4** | **165.0–167.6** | **0.80–0.81** |
| T1 + 12.5 ms (see below) | 190.4–193.4 | 160.0–162.5 | 0.78–0.79 |

The brief's target was VM best plus additions ≤ 205 ms. That is met: 196–199 ms.

S-E11's 18.5 ms of additions includes "the kind factor 6". That cost is now inside the measured V,
so the additions still to come are ≈ 12.5 ms: the templates 4, `D̂` 1.5, `R` 7. Under PR #20's
continuous score, V's term of `x` is ≈ 0.80 of v_ref, against ≈ 1.01 at HEAD.

## 3. What was built (code lines from the core's `loc.py`, HEAD → now)

| Module | Code | Change |
|---|---|---|
| `FRKindWeight` | 405 → 814 | **The fast form of `kwS`.** `cubesOf`, `fixB`, `fixK`, `itemTerms`, `termKeys`, `allKeys`, `mergeAdj`, `selM`/`selP`, `grpM`/`grpP`, closed constants `skelM`/`skelP`, `mkEnt`, `gsum`, `hornerK`, `sqG`. Proofs: `psum_cubes`, `psum_succ_one`, `psum_two_mul`, `item_terms` (char 2), `termV_keys`, `kwS_items`, `kwS_keys`, `keys_grp`, `mergeAdj_sum`, `keyW_split`, `prod_fix_ofF`, `gsum_mkEnt`, `hornerK_eq`, **`kwS_fast`**. `kwI_eq` is re-proved through `kwS_items`. Controls in §4. |
| `FRVerifierImplOps` | 507 → 702 | `wEvalCF`, `kfStep`, `wEvalKF`, **`rsWeightF`**, **`tensorWG`**, `sqItF`/`frobMapF`/**`phiRSF`**. Proofs: `fold_sim`, **`wEvalCF_eq`**, `mkEnt_sq` (Frobenius on F), `sqG_gmK`, `kf_fold`, **`wEvalKF_eq`**, `ofF_f0`, **`rsWeightF_eq`**, `prodTo_ofF`, `K_ofF_f0`, `getD_inF`, **`tensorWG_eq`**, `sqItF_eq`, `frobMapF_eq`, **`phiRSF_eq`**. |
| `FRVerifierImpl` | 95 → 96 | `implCWith`: `tensorW := tensorWG`, `rsWeight := rsWeightF`, `phiRS := phiRSF`. `implCWith_meets` and `implCWith_implT` re-proved, text unchanged. |
| `FRVIRTplRun` | 326 → 378 | `KS`, `tStep`, `kp1`, `kpGo`, `inpNF`, **`kprep3F`**. Proofs: `foldl_tStep`, `kp1_eq`, `kOne`, `kpGo_eq`, `foldl_zipIdx_fst`, `inpNF_eq`, **`kprep3F_eq`**. |
| `FRVIRTplFast` | 400 → 415 | `kprep3 := kprep3F`. `inr3` and `ectx3W` (`ectx3` is defined through them, so `FRNodeDag` is unchanged). `nodeV3` shares `inr3` between the slots. `nodeV3_slots` added; `kprep3_eq`, `slotV3_eq` and `nodeV3_eq` re-proved, text unchanged. |

`FRVIR` is unchanged. No other module was touched, and the HEAD commits after `9d1f906` did not touch
these five.

**The `rsWeight` method.**
- Per stage `k`, `kwS = Σ_t w(t) Π_l e_l(t_l)`. Each item is two prefix sums (characteristic two).
- A prefix sum `[0, x)` is the sum over the dyadic blocks of `x`'s set bits (`psum_cubes`).
- An even pattern is the run minus the odd pattern, so every pattern block is odd.
- The 417 blocks merge into 58 + 23 keys (`skelM`, `skelP`).
- A block's fixed-bit product is `ofF(F part) · (K part)`:
  - the F part comes from the claim point, which is in F in every N30 run (`rsw-info`). Stage `k`'s
    F part is stage 0's `2^k`-th power, so each stage costs one F squaring per block;
  - the K part comes from `ρ` and is the same at every stage.
- Per stage that leaves one `smulF` per block, two Horner sums (`s_l = 1 + q_l + ρ_l`) and
  `eq(q_hi, ρ_hi)`.
- Per call: `wEvalKC` 40 ms → `wEvalKF` 4.3 ms; `wEvalC` 1.7 → `wEvalCF` 1.1 ms (`kf-3`).
- The fallback paths, for a point not in F or sizes other than 23, are the reference functions.

## 4. Controls

Each `_eq` above holds for every input. The controls below show that the guards and decompositions
have teeth.

| Twin | (+) | (−) |
|---|---|---|
| dyadic blocks | `cubesOf_pos`: `[0, 11)` over 4 bits is `{10}, {8,9}, [0,8)`; `[0, 16)` is one block | `cubesOf_neg`: with the key `x >>> j` instead of `x >>> (j+1)` the blocks differ |
| odd-side rewrite | `allKeys_counts`: 417 blocks, none on the even side | `plan_even`: the plan itself has `hashB1`'s even pattern |
| `rsWeightF` guard | `rsF_guard_pos`: a point in F takes the fast path | `rsF_guard_neg`: a point with `u` falls back |
| `tensorWG` guard | `inF_pos`: `ofF 3` is read exactly | `inF_neg`: `u ≠ ofF u.f₀`, and the guard rejects `u` |
| `phiRSF` | `sqItF_ctrl`: `sqItF 1 u = u·u` | `sqItF_ctrl`: `sqItF 1 u ≠ u` |
| `kprep3F` | `kprep3F_eq` (no hypotheses) | none separate; the existing `evalM` controls run through it |
| `kwS_fast` | the existing `kwS_cube`, `kwS_hashA` (+), `kwS_hashA_ne_plain` (−) on the spec | |

Numeric cross-checks:
- `kf-*`: `wEvalKF = wEvalKC` and `wEvalCF = wEvalC` on 3 + 20 random inputs.
- `tg-0`: `tensorWG = tensorWF` on 1,627 indices.

## 5. Checks

- **`lake build FR` is green** on HEAD `7088398` plus the five modules: 2,407 jobs
  (`build-FR-1.log`).
- **Axioms** (`axioms.log`, 44 names): the theorems above, every `_eq`, every control, `acc_eq`,
  `implC_meets`, `evalMT_eq`. They use only `propext`, `Classical.choice` and `Quot.sound`; the
  controls use `propext`, or `propext` and `Quot.sound`.
- **Source rule:** 183 files, 0 findings (`source-rule.log`).
- **Sequential profiles** (one core, `-DElab.async=false --profile`; `profile-*.log`):

| Module | wall | type checking | tactics | max RSS |
|---|---|---|---|---|
| `FRKindWeight` | 22.7 s | 2.99 s | 6.21 s | 2.79 GB |
| `FRVerifierImplOps` | 23.9 s | 4.62 s | 4.38 s | 3.12 GB |
| `FRVIRTplRun` | 17.7 s | 0.39 s | 1.25 s | 2.83 GB |
| `FRVIRTplFast` | 9.9 s | 0.16 s | 0.93 s | 2.83 GB |
| `FRVerifierImpl` | 6.5 s | 0.01 s | 0.03 s | 2.77 GB |

## 6. Deviations and open items

1. **`kprep3F` and `inr3` sit in L-circ's evaluator modules** (`FRVIRTplRun`, `FRVIRTplFast`), which
   the brief allows.
2. **The skeleton's merged counts (58 + 23) are a measurement, not a kernel fact.** `List.mergeSort`
   is well-founded recursion, so `decide +kernel` gets stuck on `skelM`. Correctness does not depend
   on the counts: `keys_grp` holds for any merge.
3. **Levers not taken.** Each would need a module outside this track or a larger proof:
   - `mulK` with its left operand in F (16,011 of 16,406 ops): about −2.5 ms. It needs a change to
     `evalOp`'s `mulK` case, which `FRVIRCompile` and `FRVIRFinalsSG` unfold.
   - `eqTable` by `t − t·x`: about −2.5 ms. Blocked as in S-E8.
   - One constant `one·E(one) + sv` per key and slot: about −3 ms. It needs `slotV3_eq` to handle
     the default-value cases.
   - `preTabs` by halving: about −1.3 ms, or about −3 ms if `tbOf` also shares `slo` and `tlo`.
   - `walkAB`, 8.7 ms, is `FRBlake2sWalk`'s walk.

   What remains is `evalM`'s sparse pieces and instances (≈ 20 ms per slot) and op overhead
   (`mulK`, `addK`, `selectHalf`, about 15 ms together).
4. **For the blueprint (orchestrator):**
   - the `T_V` row: V (N30) ≈ 178–181 ms VM measured;
   - the projection ≈ 191–199 ms VM, ≈ 0.78–0.81 of v_ref;
   - `rsWeight` is ≈ 8 ms, not 38–40.
