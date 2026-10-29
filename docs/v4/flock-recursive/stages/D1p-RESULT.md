# D1-probe: RESULT. D1 (the `evalM` replay) or §8's reserve

Track D1-probe, 2026-10-29. Base: worktree HEAD (`v4/flock-recursive`), with A2″'s `seq4` read from
`v4/rev44` (`394f6ce`). Build tree `logs/fr-build-D1p` (a copy of `fr-build-orch`). Logs are in
`logs/D1p/`. Every lean and lake command ran in the 16G scope under `timeout`. No sub-agents. Nothing
is committed, and nothing under `lean/` was changed.

## 1. Recommendation: take the reserve now, folded into A2″'s regeneration

**The fixed point closes; the cost does not.** The core lemma is proved (§2). R's u-rows have the
MLE `eq(τ_hi)·eq(σ_hi)·[(1−σ_b)·Ĉ − σ_b·diag]`, built from the same `Ĉ(τ_lo, σ_lo)` that the
parent's own instances of `C` need. The value R computes at the child's point is that `Ĉ`, so the
fixed point has no cycle and adds no new matrix. The same holds for gathers (`gather_self`): a
gather's u-rows are the gather rows themselves.

What D1 cannot avoid is a V cost for every irregular entry of the child's M:
- the 76.7 k sparse skeleton rows (`40,064 + 36,660`, `logs/S-E13a/plan4t-fold.log`);
- the 5,396 instance factors and inputs of each prototype;
- the child's WOTS, `aggPad`, `aggChk` and link rows.

Each such entry needs at least one gathered value in R. The MLE of that value is a sparse sum
(`Ĝ`), which V must evaluate on top of its own pass, because no value V already computes shares
those weights. So **ΔV(D1) ≥ ≈ 1 F product per sparse row (≈ 15 ms VM), plus R's template part
(7–15) and PK-M6's WOTS replay (4–18): 26–79 ms VM.** That is above §8's 25 ms kill line unless S-E12b's
sparse-skeleton templating lever, which is not built and has no measured yield, removes most of the
skeleton. D1's best case (+11 ms VM) depends on that lever and on C0.

| | D1 | Reserve (as specified in §3) |
|---|---|---|
| ΔV, VM ms | 11 (lever + C0) / **26 floor** / 48 mid / 79 high | **≈ 2** (child of the same kind); ≈ 9 (other kind, without C0) |
| Δ\|π\| | 0 | **+896 B** |
| Prover | ≈ 0 | M_child·eq(r̄*_y) per prototype + the E2/E4 terms: **+0.1–0.3 s per node, estimated** (the node's E4 measured 0.38 s, `m_matvec` < 0.17 s; P2 §20.9) |
| **ΔS** (`logs/D1p/score.log`) | **+0.07** / **+0.17** / +0.34 / +0.61 | **+0.08 … +0.26** (V +0.013 … 0.058; P̄ +0.07 … 0.20) |
| Rows | 330–400 k in the spare region | 0 (−330–400 k; the spare region keeps R's other 221 k) |
| Risk | V depends on an unbuilt lever; the kill line can only be measured after R is built, at the end of the order; a miss means a **second `seq4` regeneration** | prover figure not measured; N8's H stays inside its `lBase` (below) |

Basis: S-I (`v_ref` 206.6 ms, V 157.9 runner ms, κ 0.2667, VM→7763 ratio 1.19), A2″'s
`|π| = 875,280`, and PACK §6.3's best case for the other lines (49 ms VM). The ranges cross only at
D1's best case, which needs an unmeasured lever. The reserve is bounded, removes the fixed point and
330–400 k rows, and must be decided now (it changes `seq4`). **Take the reserve.**

## 2. Lean: the core lemma (`logs/fr-build-D1p/src/FRD1pScratch.lean`; a copy is in `logs/D1p/`)

`loc.py`: 191 / 133 code / 13 theorems. `lake build FRD1pScratch` is green (2,275 jobs,
`logs/D1p/build.log`). Sequential elaboration takes 11.6 s wall with 0.23 s of type checking
(`scratch-2.log`). Axioms ⊆ {propext, Classical.choice, Quot.sound}, with no `sorryAx`
(`axioms.log`). The source rule reports 0 findings (`source-rule.log`). The module is generic over
a `CommRing` and an arbitrary matrix, and is built on `TEval.eqN`/`eqN_split`.

- `placed_eq`: a block at aligned bases has MLE `hi(τ, X)·hi(σ, Y)·Ĉ(τ_lo, σ_lo)`.
- `replay_val`: u-rows `u_r = Σ_c C[r,c]·e_c` over `e = eq(σ, ·)` give `Σ_r eq(τ, r)·u_r = Ĉ(τ, σ)`.
  This is `replay_sound`'s arithmetic.
- `diag_eq`: `Σ_{r<2^a} eq(τ,r)·eq(σ,r) = Π_{l<a}(τσ + (1−τ)(1−σ))·Π_{a≤l<b}(1−σ)` (the
  outputs' and v-rows' stride-1 class, O(b)).
- `ublock_chat`: for the u-block as one `2^a × 2^(b+1)` block (the table at local `[0, 2^b)`, the
  outputs at `2^b + r`), `Ĉ_block = (1−σ_b)·Ĉ − σ_b·diag`.
- **`fixed_point`**: the instances of `C` together with its u-block evaluate to a closed form in the
  single value `Σ_r eq(τ_lo, r)·u_r`, which is the replay's own output. This is the core of
  `replay_mle`.
- `gather_self`: the u-rows of an incidence matrix `addr` are the gather rows `u_r = e(addr r)`.
- Controls:
  - (+) `chat_ctl`;
  - (−) `unaligned_ctl`: an unaligned base breaks the closed form;
  - (−) `table_ctl`: without the eq table, `replay_val` fails.

What remains for D1, besides the cost:
- a replay template and its proof for every class of `evalMT4`: keys, instance factors, inputs,
  sparse rows, slot copies with the kind mux, the arenas' diagonal, shift and automaton forms, the
  cap-check templates, and the link and WOTS rows;
- `replay_sound`: a row-level re-proof of `evalMT4_eq`;
- `evalM_eq` over 𝒞 and `plan_wf`.

R must also be regenerated after every plan change (B0, B2′, C0, C1).

## 3. The reserve, made exact, and a correction to PACK §6.4/§8

PACK's reserve is a separate 23-round sumcheck, with `eq(r_child, r_parent)` "from the H cells".
That is underspecified in two ways:
- (a) The child's **row** point `r*_x` must be reduced as well. Otherwise V needs a second `evalM`
  at another row point, costing about another 85 ms.
- (b) V does not see H, so the child's point must be in π and bound to the circuit by point claims.

**Construction.** The protocol already batches L's claim at `r_Lr` into E4. The child's claim
`(a*,b*,c*) = M_child(r*_x, r*_y)` is batched the same way, and **no rounds are added**:
- **E2** gets the term `η·eq(r̄*_x, x)·(Ã* + ηB̃* + η²C̃*)(x, r̄*_y)`, with degree ≤ 3 unchanged.
  - Its initial claim is `c₀^{E2} = η(a* + ηb* + η²c*)`.
  - `η` is E1's spare coordinate 23 (12 squeezes give 24 coordinates; `e2 = 23`).
  - Its end value `m̂*` goes in Eend.
- **E4**: `c₀ += κ_E⁴·m̂*`, and the summand gets `+ κ_E⁴·W*_E2(y)·eq(r̄*_y, y)`, with degree 2
  unchanged.
- **finE**:
  - (ii) `+ η·eq(r̄*_x, r_E2)·m̂*`;
  - (iv) `+ κ_E⁴·W*_E2(r′)·eq(r̄*_y, r′)`.

  `W*` is `evalMT4` of the child's kind at the parent's own point `(r_E2, r′)`. It reuses `protoV4`
  (both prototypes), so it is free when the kinds are equal and adds only that kind's slot and link
  terms otherwise.
- Every term is gated by the parent's `hasPrev`, which is `false` for N8. A leaf is a dummy.
- **B′/finPf**: 52 new public cells at `κ′^{j+2}`. They are slot 0's `r_E2` (23) and `r′` (25)
  registers, `evalM`'s three outputs and `kindElem`.
- **ε**: E1's row becomes `(e2 + 3)/2^128` and E3's batch goes from 6 to 9 claims (`8/2^128`).
  Both stay below the per-query maximum of `2^-120.36`; `εR` is unchanged.

**The `seq4` change for A2″.** No new item and no new phase, so item positions and phase indices
do not move.

| Phase | Item | Field | Today | Reserve | Content |
|---|---|---|---|---|---|
| `Lrend` | absorb | `fLrEnd` | 48 B | **880 B** | `â_L ‖ b̂_L ‖ ĉ_L` (48) ‖ `r̄*_x` (23 × 16) ‖ `r̄*_y` (25 × 16) ‖ `a* ‖ b* ‖ c*` (48) ‖ `kindElem*` (16) |
| `Eend` | absorb | `fEEnd` | 48 B | **112 B** | `â_M ‖ b̂_M ‖ ĉ_M` (48) ‖ `m̂*` (16) ‖ `0^48` |

The figures that move:
- `|π|` +896 to 876,176;
- the stream +896 B = **14 whole blocks**, so a segment stream is `64 · 24,234` and alignment is
  kept;
- items 8,783 and positions unchanged;
- `hUsed`: N2 +42, N4 +70, N8 +112 (195,080 → 195,192). N8's `lBase` stays at 195,328, still
  ≤ 195,584.

Lrend is absorbed before E1, so `η` and `κ_E` come after the claim is bound. It is also before B′,
so `κ′` comes after the π copy that the point claims check.

Lean work for the reserve:
- A2″: two field lengths and the size and region literals (`piSizeOf_seq4`, `streamBytesOf_seq4`,
  `chainLenOf_seq4`, `hUsed_eq`, `regions_fit`, `regions_need_levers`), and two rows of
  `reassemble`;
- S-C/S-G: E2 as a zerocheck plus a linear claim, and `truthE` gains `truthChild`;
- `finE`, `finPf`, and `PubCells4` (+52);
- the node chain: `Gap4.imp`'s three `evalM` registers are discharged by the point claims and the
  parent's `truthChild`, not by R;
- P2: the E2/E4 terms and the fields.

## 4. Open questions

1. Measure the prover's added matvec per prototype (`M_proto·eq(r̄*_y,lo)`) before relying on +0.3 s.
2. The same mechanism could defer `evalL` too: about +17 × 16 B plus one more batched claim. It would
   drop R's 15–25 k `evalL` rows and the carry-automaton proof. This is out of this probe's scope.
3. A2″ should confirm N8's `lBase` with R-A′'s spacers in place (`hUsed_eq` is taken before them).
