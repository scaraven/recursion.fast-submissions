# R-OPS: binding the previous-node slot's remaining ops (`evalL`, `targetS`, `linkWAll`, `rsWeight`, `shiftTarget`)

Design memo, track R-OPS, 2026-10-30. Worktree `recursion.fast-submissions-rev44` at `6a93cc8`
(v4/rev44). Memo only: no Lean, no prover, no build, nothing committed. Read: `QUEUE.md`,
`PACK-4.4.md` §6–§8, §11.2, `RSV2.md`, `reviews/RSV2-review.md`, `stages/C1-RESULT.md`,
`C1-JOURNAL.md`, `D1p-RESULT.md`, `S-E14-RESULT.md`, `RSV-V-RESULT.md`, `RSV-V2-RESULT.md`,
`B5-RESULT.md`, `RSV-S-RESULT.md`, `RSV-S2b-RESULT.md`, `INT-9-RESULT.md` (per-op V profile); Lean:
`FRVerifierImplNode4F` (`evalL4I`), `FRNodeTarget4` (`targetSNode4S`, `linkWAll4S`),
`FRVerifierImplOps` (`shiftTargetI`, `rsWeightS`), `FRVerifierImplOps4` (`rsWeightF4`, `kwSL4`),
`FRVIR` (`Op`, `OpImpl`), `FRVIRCompile` (`imports`, `encV`), `FRVIRFinals4` (`gShCore`, `gFinE0`,
`rsvEOps`, `gFinPf`, `gPfPts`, `gLcSrc`, `gShSrc`), `FRVIRFinalsCore` (`linkOps`, `linkSum`),
`FRVerifierC4` (`rsvRel`, `ptIx`), `FRNodeRows4Rep` (`SlotImpR`), `FRShape4` (`seq4`, `phasesOf`),
`FRNodeLayout4` (`hUsed_eq`, `regions_fit`), `FRSoundnessCoreSteps` (`epsR`, `deltaR`,
`coord_le_deltaR`), `FRVIRTplCore` (`TKey`), `logs/org20/…/Security.lean` (`errorCap = 2^-120`).

## 0. Summary and recommendation

1. **Three of the five ops are closed forms in the child's challenges and public constants**
   (`evalL4I ν rL r4`, `targetSNode4S ν r`, `linkWAll4S ν tt rr`), so the cheapest sound binding is
   neither a replay nor a sumcheck: **make the child's operand registers and the op's outputs public
   cells** (the reserve's `PubCellsR4` mechanism, 60 cells today) and let **`V(P)` recompute the op
   on the public values and `assertEq`**. No doom, no new challenge, no FS position moves, no new
   error row beyond B′'s point-claim count. V pays the op once more (`evalL` 11 ms, `targetS` 2 ms,
   `linkWAll` 2 ms VM: INT-9's profile) instead of C1's 52–60 ms for `linkWAll`'s rows alone.
2. **The ceilings are cells, not time.** B′'s row `(70 + N′)/2^128` must stay `≤ 239/2^128`
   (`coord_le_deltaR`) for `εR = 15/2^124` to hold: **`N′ ≤ 169` new cells**. N8's H has 356 blocks
   before `lBase`'s bound and every replayed proof carries the field: **`N′ ≤ 178`**. The naive
   inventory for the three ops is 168 cells (§4): inside both ceilings by 1 and 10. **Adopt `tdot`**
   (§4.2: `targetS` folded into its only consumer, `lagrangeS`, which is additive in the 64 target
   values: 1 output instead of 64), giving **`N′ = 108`**: `J_f = 177`, N8 margin 140 blocks.
3. **`rsWeight` cannot be carried**: its operands are the child's `ρ ∈ K^25` (50 cells), the Z3 and
   L2 points (33) and `r″ ‖ κ ‖ β` (9): 94 cells, over every ceiling, and the segment slots need the
   same op `k` times where no carry exists at all. **`rsWeight` is a replay with closed-form
   templates** (squaring chains, product chains, Horner, `phiTable`'s tree, the kind factor's dyadic
   sums: all diagonal/shifted-diagonal MLEs of the kind D1p proved), shared by prototypes 0 and 1.
   Its fallback (full carry under a second point-claim family batched by `κ_E` plus N8 lever L5) is
   priced in §5.
4. **`shiftTarget` stays C1's one row** (its value is `0` at prototype 0).
5. **Reject the reserve route for these ops**: `evalL` could fold into Lr1's spare coordinate and
   E4 like RSV2, but it costs four soundness stages for −8 ms of V against the carry; `targetS`,
   `linkWAll`, `rsWeight` are not hypercube sums with a low-degree witness multiplier.
6. Score: **ΔV ≈ +15 ms VM (+12.6 runner, ≈ +0.10 s of S)** for the three ops, plus ≈ 1–3 ms for
   `rsWeight`'s templates if the closed forms land; `|π|` +1,728 B; prover ≈ 0; `εR` unchanged.

## 1. The question, the constraints

Slot 0 of a parent `P` (N2/N4) replays `V(C)` of the previous node `C`. `SlotImpR rtC1` (C1) still
assumes the import registers of `targetS`, `evalL`, `rsWeight` at prototype 0 (plus the segment
slots' `targetS`, `shiftTarget`, `rsWeight` and dead `evalM`/`evalL`). The reserve (RSV2) binds
`evalM` through `PubCellsR4 κ w (childVals π)` (60 cells of `fLrEnd`, B′'s point claims) and
`truthChild4` (the parent's E2/E4). Constraints every route must meet:

| Constraint | Value | Source |
|---|---|---|
| Fiat–Shamir order | a value batched by a challenge is absorbed before it; `fLrEnd` is item 213 (before E1), B′'s `κ′` after RS1 | A3′'s (β) lesson; RSV2 §2.6 |
| B′'s row | `(J_f + 1)/2^128 ≤ 239/2^128`; today `J_f = 69` | `coord_le_deltaR`, `single_B4` (`Fin 71`) |
| the cap | `εR = 15/2^124 = 240/2^128 ≤ errorCap = 2^-120 = 256/2^128` | `boundsOK_claim`; `logs/org20` `Security.lean:127` |
| N8's H | `hUsed 195,220`, `hEnd 195,228`, `lBase 195,328`, bound `195,584`: 356 blocks; every replayed proof (8 at N8) carries `fLrEnd` | `hUsed_eq`, `regions_fit` |
| V's price | `0.0076 s` of S per runner ms at `x ≈ 1.4`; VM → runner ÷ 1.19 | PACK §6.3 |
| rows | sparse replay rows cost ≈ 0.3 µs per term (1.2–1.4 µs per row) | C1 §4 |

## 2. The ops: what each computes, from what

Sizes at `seq4` (`z1 19, z3 26, s2 28, lr 17, e2 23, e4 25, pf 7`; S1 has `m* − 14 + 11 = 29`
coordinates; `nb = 17/18`, `logL = 16/17` for N2 / N4-N8). "Child-muxed" = the register's cells
are the child's challenge cells, with one mux cell per position whose source differs by kind.

| Op (prototype 0) | Specification | Operands (registers of `V(C)`) | Outputs | V's own cost (N4, VM) | Rows if replayed |
|---|---|---|---|---|---|
| `evalL` | `evalL4I ν rL r4`: the MLE of `lRows4 ν` (public) at `(rL, r4)` | `rL` = Lr2's point (`lrEx fi 1`, 16/17), `r4` = E4's point (`b + 17`) = `p_y[< e4R]` **already carried** | 3 F (third is `0`) | 11.0–11.3 ms (`evalL4I`; INT-9 lever −4.5) | ≈ 82 k products direct; 15–25 k with the carry automaton (unwritten) |
| `targetS` | `targetSNode4S ν r` over `8 + nb` variables (`zLo r`, `r[1 … nb]`) | `pt` = Z1's packed point (19) | **64 F** (`af 64`) | 1.95 ms | ≈ 24 k; ≈ 4–5 k products per kind but mirrors S-CN4b's ≈ 450 lines gate for gate |
| `linkWAll` | `linkWAll4S ν tt rr`: 8 WOTS link families at `srcB4`/`mirB4` | `tt` = S1's `τ ‖ θ` (28), `rr` = S2's `r_blk ‖ r_pos` (28) | 8 F | 1.93 ms (2.07/2.17/2.19 N2/N4/N8) | C1's `tplLW`: 42,601 rows, 196,410 terms, **52–60 ms**; plan 131 s |
| `rsWeight` | `rsWeightS4 ν r″ ps κ β ρ = Σ_j κ^j Σ_{k<128} c_k(r″)·w_{j,k}(ρ)`, claim 2 by the kind factor `kwSL4 ν` | `r″` = RS1[0..7), `κ` = RS1[7], `β` = L3β, `ρ` = the selected `P₀` point `(sb + 4)` ∈ **K^25**, `ps` = the Z (Z3's 26), Lc (L2's last 7 ‖ Z3's block coords), Sh (S2's 28, shared), E4 (shared) points (`ptIx = [0,2,4,6]`) | 1 K (2 F) | 9.8 ms (`wEvalKF4` fast path) | ≈ 45.6 k (claims) + 68.5 k (kind factor), K-arithmetic |
| `shiftTarget` | `shiftTargetI κs τ θ bnd` | `bnd` is the constant `0⁴ ‖ last` at prototype 0 | 1 F = `0` | 0 | **1 row (C1, done)** |

`linkOps` consumes the 8 link weights only through `Σ_f κ_s^{f+2}·w_f` (`linkSum`); `lagrangeS`
consumes the 64 target values only through `Σ_{b<64} ℓ_b(λ)·pe_b` (`z2Vals`: `pe_b` is *added* to
`P^z*(skipNode b)`; `interpolateAt` is linear). Both consumers are therefore scalar dots with
weights in one challenge: §4.2 uses this.

## 3. The three routes, judged per op

### 3.1 (a) Replay: rows in the spare region (C1's `KOp`/`rtK` mechanism)

Sound by `compileFromX_soundRW` (the op's value is whatever the template's gates compute from the
operands' cells at the aligned state). No error term, no FS content. The cost is V: every term of
every row is a product unless the rows have a closed-form MLE. C1's measurement (`linkWAll`,
one kind-muxed instance per kind: 52–60 ms) is the rate to expect for any op whose template is
*one large instance*: keying buys nothing without many instances, and closed forms need a
per-template MLE lemma (the S-E9 program, never built). PACK §6.2's "7 ms for all of `R`"
assumes those closed forms. Verdicts: `shiftTarget` yes (1 row); `linkWAll`, `targetS`, `evalL`
no (the carry is cheaper by 10–30× in V and needs no template proof); `rsWeight` **yes, as the only
route**, with closed forms (§5).

### 3.2 (b) The reserve: the child's claim proved by the parent's sumchecks

Applies when the child's value is `Σ_x eq(point, x)·T(x)` over a hypercube the parent already
sums over, with `T` public: `evalM` (RSV2) and `evalL` (`lRows4`'s MLE, `logL ≤ 17` rows,
`m − 7 = 25` columns). An `evalL` reserve would be RSV2 on the Lr phase: Lr1 squeezes 18
coordinates for 17 rounds, so a spare `η_L` exists; E2 → Lr2 (zerocheck + `η_L·eq(q_x, x)·(Σ s′·L̃(x ‖ hi,
q_y) − Y)`, degree 3 unchanged), E4 gains `κ_E⁵·eq(q_y, y)·Σ s′ L̃(q_x, y ‖ hi)` (E3's batch degree 4 → 5,
row 5), finE's own `evalL` becomes a stacked call at the mixed point. Cells: `q_x` 17 + `s′` 9 + `Y₃` 3
= 29 (the carry needs 20). V: the stacked `evalL` sums the kinds in `supp(s′)`; `slotL` is
kind-independent per slot but the slot count is the maximum kind's (8), so ≈ +3 ms against the own
call — the carry's `evalL` recompute is 11 ms, so the reserve saves ≈ 8 ms VM (≈ 0.05 s of S) for a
restatement of the Lr dooms (`ZCw`/`D3`/`RejEnd`/`RejFin` of Lr, a `truthChildL4`, E3's count,
`relE4`'s Lr conjuncts): RSV-S + S2a + S2b + S3 again. **Rejected** on cost; it stays the fallback
if `evalL`'s recompute must go to zero and the carry automaton (§7 lever) fails. `targetS` is an
MLE over `8 + nb = 26` variables (no parent phase has that dimension) with 64 outputs (64 claims);
`linkWAll` and `rsWeight` are products of 25–28 witness-linear factors: not sumcheck-shaped.
**Not applicable.**

### 3.3 (c) The public-op route: carry the operands and the outputs, `V(P)` recomputes

**Mechanism** (RSV2's, extended). The child's operand registers and the op's output registers are
cells of slot 0 (`rsvRel`-style M-relative cells, one per position, mux cells included). `P`'s
`fLrEnd` carries their values; `finPf`'s second cell chain and `finB′`'s Horner bind them by B′'s
point claims (`PubCellsR4`); `V(P)`'s finals read the values from `fLrEnd`, run **its own op**
on the child's kind and assert equality with the carried outputs (`assertEq`, gated `rsv`, as the
reserve's (ii″)–(iv″)). The child's kind is the one extra public cell: the child's header kind
element (RSV-V's `kindElem*`, "the seed's `piElem 0 0`, tied to the selector by the seed's assert"),
decoded by `kindOfElem`; V dispatches the op on it. To keep the `Op` set fixed, tag the call by the
operand's size as RSV2 tags `evalM` by a 32-entry point: `evalL (rL ‖ kindElem) r4` (18 entries),
`targetS (pt ‖ kindElem)` (20), `linkWAll (tt ‖ kindElem) rr` (29); `implN4F` dispatches to
`base (kindOfElem e)` and the `_meets`/`_hL`-style lemmas state the spec at the tagged size.

**Soundness (no doom).** For an accepted run of `V(P)`: (1) `PubCellsR4`: the cells hold
`fLrEnd`'s values (B′/finPf; `single_B4` at `Fin (71 + N′)`); (2) the finals' flag: `V(P)`
asserted `out = op_{ν_C}(in)` on those values (`relE4`'s new conjuncts, as `rsvEOps`'s asserts are
`relE4`'s (ii″)–(iv″) today); (3) the kind cell equals the slot's selector kind (`kindN`'s tie);
(4) the run of `V(C)` fed the op the registers whose cells are those positions, so the spec's
output at those inputs equals the carried outputs: `RepS` at the output slots (`evalM_childV`'s
shape, `FRNodeStmtR4`). Steps (2)–(4) are equalities of pure functions; only (1) is probabilistic
and it is the existing point-claim argument with a longer list. **FS order**: the carried values
sit in `fLrEnd` (213), before every squeeze that follows; the only challenge that batches them is
`κ′` (B′, after RS1); the asserts involve no challenge. Nothing of A3′'s kind can occur.

**Error.** B′'s row becomes `(70 + N′)/2^128`; E1/E3/E4 unchanged. `εR = 15/2^124` **holds iff
`N′ ≤ 169`** (`coord_le_deltaR`). Between 170 and 185 the entry would need `εR = 16/2^124`
(`errorCap`, with `epsR`/`deltaR`/`coord_le_deltaR`'s 239 and `hfin_ml`'s `hn′` re-based):
**not recommended**. Beyond that, a second family (§5.3).

### 3.4 Per-op verdict

| Op | Route | Cells (child-muxed) | ΔV (VM) | Prover | Lean (beyond the shared §6 work) | Risk |
|---|---|---|---|---|---|---|
| `shiftTarget` | (a) C1's row | 0 | 0 | 0 | none (`rtST0`, done) | none |
| `evalL` | **(c)** | `rL` 17 + out 3 = **20** | **+11** (−4.5 with INT-9's lever; ≈ 0 with §7's closed form) | copies | `evalLN4` dispatch + `_eq`; `evalL_childV` | low |
| `targetS` | **(c) with `tdot`** | `pt` 19 + `λ` 1 + out 1 = **21** (83 without `tdot`) | **+2** (+0.1 for 64 Lagrange weights at `λ_C`) | copies; Z witness gains one cell | `tdot` op, `tplLagrangeS` arity, `targetSNode4I`/`targetSLeafI` dot forms, `RejZ` flags; `tdot_childV` | moderate (touches finZ for every kind) |
| `linkWAll` | **(c)** | `tt` 28 + `rr` 28 + out 8 = **64** (58 with an `ldot` op: `Σ_f κ_s^{f+2} w_f`, +`κ_s`) | **+2** | copies; **−42,601 template locals** | `linkWAllN4` dispatch + `_eq`; `linkWAll_childV`; retire `tplLW`/`kLW` (or keep as a control) | low |
| kind | (c) | **1** | 0 | copies | `kindElemN`/`kindOfElem` revived from RSV-V | low |
| `rsWeight` | **(a) with closed forms** (§5) | 0 | **+1–3** if the closed forms land; +130 as sparse rows | the template's witness (K-arithmetic locals, ≈ 110 k cells in the spare region) | the §5 library + two templates + `KOk` proofs | **high**: the library is unbuilt |

## 4. The cell inventory, the two ceilings, and the levers

### 4.1 Inventory (prototype 0; sizes are the child-muxed maxima)

| Carried | Cells | Note |
|---|---|---|
| today: `p_x` 23, `p_y` 25, `s` 9, `X₃` 3 | 60 | `rsvRel` |
| `evalL`: `rL` (Lr2, 16/17 → 17), out 3 | 20 | `r4 = p_y[< e4R]` shared |
| `targetS`: `pt` (Z1, 18/19 → 19), out 64 | 83 | → **21** with `tdot` (`λ` = Z2's challenge, out 1) |
| `linkWAll`: `tt` (S1 `τ ‖ θ`, 27/28 → 28), `rr` (S2, 27/28 → 28), out 8 | 64 | → 58 with `ldot` |
| kind element | 1 | |
| **`N′`, plain** | **168** | `J_f = 237`, row `238/2^128` ✓ (margin 1); N8 `hEnd + 336 = 195,564 ≤ 195,584` ✓ (margin 20 blocks) |
| **`N′`, with `tdot`** (padded to a multiple of 4 for 64-B alignment) | **108** | `J_f = 177`, row `178` ✓; N8 `+216 → 195,444` ✓ (margin 140) |
| `N′`, with `tdot` and `ldot` | 100 | `J_f = 169`; N8 `+200` |
| `rsWeight` if carried: `r″` 7, `κ` 1, `β` 1, `ρ` 50, Z3 26, L2 7, out 2 | **94** | S2 and E4 shared; **over both ceilings** with any of the rows above |

`fLrEnd = 48 + 16·(60 + N′)` is block-aligned iff `N′ ≡ 0 (mod 4)`: 168 → 3,696 B (`48 + 57·64`);
108 → 2,736 B (`48 + 42·64`). Stream per proof +42 / +27 blocks; N8 replays 8 proofs. The
inventory is from the generators (`gShCore`, `gFinE0`, `uniTail`), not from a dump: **stage R0
audits it on `mregs-p0.txt`** before any field length is fixed.

### 4.2 `tdot`: fold `targetS` into `lagrangeS`

`uniTail`: `.targetS pt → pe (64)`, `.lagrangeS vals λ pe → (P^{ab}*(λ), P^z*(λ))` with
`P^{ab}*(λ) = Σ_{b<127} ℓ_b(λ)·z2Vals_b`, `z2Vals_b = P^z*(skipNode b) + pe_b` for `b < 64`. Define
`tdot pt λ := Σ_{b<64} ℓ_b(λ)·targetS(pt)_b` (one F) and `lagrangeS′ vals λ t := (Σ_b ℓ_b(λ)·z2Vals_b[pe := 0] + t, P^z*(λ))`.
Same arithmetic, same messages, no FS change; the import of `targetS` at every slot becomes one cell
(the segment slots' `targetSSegI` template gains a 64-term dot: ≈ 560 rows instead of ≈ 500).
Modules: `FRVIR` (`Op.tdot`, `OpImpl.tdot`, `OpSpec`), `FRVIRCompile` (`imports cs [.f]`),
`FRVIRTplLag` (`tplLagrangeS n m` with a scalar input; its `_ok`), `FRVIRTplSet` (`ImplT`),
`FRVerifierImplOps` (`tdotLeafI`), `FRNodeTarget4`/`FRVerifierImplNode4T` (`tdotNode4I`,
`_meets`), `FRVIRFinals` (`uniTail`), R4's `not_rejZ_seg4`/`not_rejZ_node4` (`peL_*` composed with
the weights), S-G's Z truth (reads `relZ` unchanged in content), P2's `finZ` witness (64 cells → 1).
About ten modules, mechanical; the Z soundness statements keep their meaning.

### 4.3 Other trims (reserve)

`ldot` (−6); `evalL`'s zero output by a row (−1); deriving the kind from `s` (not sound: `s` is
not an indicator) — no. N8 levers if the stream binds: L5 (half-size `D`, −1,742 blocks, a
collision lemma family at `2^-128` per fresh node query), L3 (−444, positions move).

## 5. `rsWeight`

### 5.1 Why not the carry

94 cells (§4.1): `ρ` is the Pf/fold point in `K` (25 coordinates = 50 cells), the Z3 and L2 points
are not otherwise carried. `108 + 94 = 202 > 185` (the cap's absolute ceiling) and `> 178` (N8).
And the segment slots run `rsWeight` with three claims (`ptIx` `[0,3,6]` …) `k ≤ 8` times on
challenge registers that no carry reaches: the op needs a row-level binding there regardless.

### 5.2 The replay with closed forms (recommended)

`rsWeightF4` is a composition of: `phiTable r″` (128 coefficients from 7 coordinates: a tree),
per claim `j` and stage `k` the Frobenius images `r_{j,l}^{2^k}` (100 squaring chains of 127 steps),
per stage the product `Π_{l<25}(1 + r_{j,l}^{2^k} + ρ_l)` in `K` (512 product chains of 25 factors;
`eq(a, ρ) = Π(1 + a_l + ρ_l)` in characteristic 2), the Horner sum over `k` with `c_k` (4 chains of
128), `κ^j`, and for claim 2 the kind factor `kwSL4 ν` (`KW4.skel4 ν`: 7 Frobenius stages of
per-bit factors and dyadic range sums over ≈ 22 kind intervals, `β`'s squaring chains). As rows this
is ≈ 45.6 k + 68.5 k (PACK §6.2), ≈ 130 ms as sparse pieces (C1's rate): not viable. Every piece
is a **chain over contiguous locals**: `x_{i+1} = x_i·x_i` (A, B diagonal, C shifted diagonal),
`y_{l+1} = y_l·f_l` (one wiring term per input), `h_{k+1} = h_k·c + t_k` (Horner). A chain's rows
have an MLE in `O(log)` from `diag_eq` (D1p) and the shift-window form (PK-m2); a template made of
chains costs `≈ (#inputs + O(log))` per chain: ≈ 100·25 + 512·30 + 4·130 + kind factor ≈ 12 k
≈ **20–25 k products ≈ 1–3 ms VM**, PACK's figure. What is missing is (i) the chain MLE lemmas
(three shapes) and the tree form of `phiTable`/`eqTable`, (ii) a plan piece `Piece.chain` in
`FRNodeRows4Plan` with its `_eq` to `rows3`, (iii) the two templates (claims; kind factor) as
`KOp`s mirroring `wEvalKF4`/`wEvalCF`/`kwSL4I` gate for gate with `KOk` (C1's mechanism, proved
once by `rtK_okW`). The same templates serve prototype 1 (three claims, no kind factor) at `k`
instances, where keying pays twice.

### 5.3 The fallback: carry under a second point-claim family

If the chain library misses its budget (§8), `rsWeight` at slot 0 can still be carried: batch the
extra cells by **`κ_E`** (E3, after `fLrEnd` at 213): `claim0(P1) += κ′^{71 + N′}·Σ_i κ_E^i v′_i`,
weight `+ κ′^{71 + N′}·Σ_i κ_E^i eq(c′_i, ρ)`; a new doom at E3, `PubBad4′ := (∃ i, f(c′_i) ≠ v′_i) ∧
Σ_i κ_E^i (f(c′_i) − v′_i) = 0`, prefix-determined (`f⁽⁰⁾` from the commitment, `v′` from 213),
charged `94/2^128` on E3's row (`4 + 94 ≤ 239`); `single_B4` gains one coefficient (`Fin (72 + N′)`).
The stream then needs N8's L5 (`108 + 94 = 202` cells, 404 blocks > 356). Cost: V +9.8 ms
(`rsWeightF4` once more), an RSV-S2b-sized restatement (`PubOKR4′` into the DRS `Pub` argument,
`vStarL4`, `gFinPfR`'s third chain, `BatBadE4 ∨ PubBad4′`, `e4_single_batchE`'s count) and L5's
collision lemmas; the segment slots stay open. It removes every template from slot 0, which is
why it is worth keeping as the kill-line exit.

## 6. The concrete changes (the recommended route)

**Format** (`FRShape4`, `FRNodeKinds4`, `FRNodeLayout4`, `FRX4Prog/Ext`, `reassemble`): `lrEnd`
1,008 → **2,736** (with `tdot`; `N′ = 108`), `fLrEnd = â_L ‖ b̂_L ‖ ĉ_L ‖ p_x ‖ p_y ‖ s ‖ X₃ ‖ rL (17) ‖
outL (3) ‖ pt (19) ‖ λ (1) ‖ t (1) ‖ tt (28) ‖ rr (28) ‖ w (8) ‖ kind (1) ‖ pad (2)`; `piSizeOf seq4`
+1,728; `segB`/`cLen`/`sBlk` +27 blocks; `hUsed_eq` N2/N4/N8 +81/+135/+216; `regions_fit`
(N8 `lBase 195,584`). No item, no phase, no position moves.

**V** (`FRVIRFinals4`, `FRVerifierImplNode4F`, `FRVerifierC4`): `rsvEOps` gains a block
`rsvOps2`: `piElem fLrEnd` × `N′` (exports for B′), `piField` zero asserts where `¬rsv`,
`packFK` of the carried arrays with the kind element appended, `.evalL (…) (ry.take e4R)`,
`.tdot (…) (λ)`, `.linkWAll (…) (rr)`, three `assertEq` (gated `rsv`; the N8 parent asserts the
block zero as today). `evalLN4`/`tdotN4`/`linkWAllN4` dispatch on the operand size; `_eq` lemmas;
`kindElemN`/`kindOfElem`. `rsvRel` 60 → 168 (from the regenerated dump; one cell per register
position); `nodeFinP … nrcell`; `rsvBOps`' Horner over 168; `gFinPf`'s second chain at 168;
`FinP.nrcell`; `FRVIR4At`/`Uni` counts; hints regenerated (`inR = true`); `VTime4` with a child of
every kind; `RsvKat` chains `N8 → N4 → N2 → N2` with (−) controls per op (a perturbed output, a
perturbed operand with the prover honest at it, a wrong kind element).

**Soundness** (RSV-S's modules): `R4Fin.relE4` (or a new `relOps4`) gains (vi) `outL = evalL4I
ν_C rL (p_y[< e4R])`, (vii) `t = tdot ν_C pt λ`, (viii) `w = linkWAll4S ν_C tt rr`, with `ν_C =
kindOfElem kind`; `flag_gFinE` in blocks (S2a's `pr_seq2` method; `rsvOps2` as its own block F);
`vStar4`/`vStarL4` over `60 + N′`; `P4bB.PubOKR4`/`bTerms4`/`single_B4` at `Fin (71 + N′)`;
`PfFlag.gFinPfR`, `PfFin.hz_of_fields` at `nrcell = 168`; `FRNodeCircuit4.PubCellsR4` unchanged in
form; `FRNodeStmtR4`: `truthOpsV` (the three equalities as read from `childVals π`), `StmtN4R :=
StmtN4 ∧ PubCellsR4 ∧ truthChildV ∧ truthOpsV`, `evalL_childV`/`tdot_childV`/`linkWAll_childV` on
`evalM_childV`'s pattern, the kind tie `kindElem_sel` (from `kindN`'s rows); `gap4Imp_of_rsv`
discharges every slot-0 import of `impRP rtR 0` where `rtR 0 = rtST0` (C1's row) and `rtR 1 =
rtLinkSegW` (S-E14's zeros). Controls: (+) an honest chain's cells satisfy (vi)–(viii); (−) `outL + 1`,
`t + 1`, `w_3 + 1` each fail the flag; (−) a wrong kind element fails `kindElem_sel`.

**Prover** (E1): copy the registers into `fLrEnd` (as the 60 today); the Z witness cell for `t`;
no `tplLW` locals. The kind element is the child's header byte already in H.

## 7. Error budget, V, P, |π|

- **`εR`**: E1 `24`, E3 `4`, E4 `2` per round, B′ `70 + N′ = 178` (`≤ 239`): `εR = 15/2^124`,
  `claim.json` unchanged. (Plain 168 cells: B′ `238`, still inside; `tdot` + `ldot`: `170`.)
- **V (N4, VM)**: `evalL4I ν_C` 11.0, `tdotNode4I` 2.0, `linkWAll4I` 2.1, `finPf` +108 cells
  (`eq(c_i, ρ)` weights ≈ 2.5 k products) 0.2, B′ Horner 0.0: **≈ +15 ms** (12.6 runner,
  **+0.10 s** of S); with INT-9's `evalL` lever +11; **lever**: `evalL4I` by the carry automaton
  (`Σ_{j<nJ} eq(rL, σ nJ + j)·eq(r4_lo, 299 + j)` in `O(14)` per slot, S-E14 §2) makes both the own
  and the child's call ≈ 0.1 ms: **−11 own, −11 child**, one `evalL4I_eq` re-proof. `rsWeight`'s
  chains +1–3. Against the alternatives: C1's `linkWAll` rows alone +52–60; PACK's keyed `R` 7–14
  (unbuilt closed forms for five ops).
- **Prover**: copies only; the K-arithmetic witness of `rsWeight`'s template (≈ 110 k locals, one
  pass) when R4 lands. P̄ ≈ +0.00 s.
- **`|π|`**: 876,304 → **878,032** (+1,728 B); `x`'s size term +0.0008; stream `64·24,263` per
  segment (`1,551,104 + 1,728`); N8 `hEnd 195,444 ≤ 195,584`.
- **Build**: ≈ 10 touched modules on the V side, ≈ 12 on the soundness side; kernel cost is
  symbolic (no `decide` over 168 cells: `pubPart_eq`'s pattern). `flag_gFinE` is the elaboration
  risk (S2a: 9 min 40 s / OOM before the block method).

## 8. The plan, with definitions of done and kill lines

| Stage | Content | Done when | Kill line → exit |
|---|---|---|---|
| **R0** (audit, no Lean; ≤ 1 agent-stage, scripts only) | from `logs/RSV2/dump`'s `mregs-p0.txt`/`mkslots-p0.txt`: the cells of `rL`, `pt`, `λ`, `tt`, `rr`, the outputs, the kind element, per kind; mux cells; `N′` plain and with `tdot`/`ldot`; the field length, alignment, `hUsed`/`hEnd` per kind; the per-op V figures re-measured on rev44's binary (`vtime ops`) | a table in `R0-RESULT.md` with `N′`, `J_f + 1 ≤ 239`, N8 `hEnd ≤ 195,584`, and the chosen trims | `N′ > 169` with both dots → §5.3's second family goes **before** R1; N8 margin `< 64` blocks → L5 before R1 |
| **R1** (V side; RSV-V2's shape) | `tdot` (§4.2), the format, `rsvOps2`, dispatch ops and `_eq`, `rsvRel`, hints, dump, `VTime4`, `RsvKat` | build green at the known red set; `inR = true`; V(N4) measured for a child of each kind; program sizes; the KAT's (+)/(−) rows; E1 told the field layout | measured ΔV `> 25 ms` VM → stop; find the cause before R2 (the ops cost 15 by INT-9's profile) |
| **R2** (soundness; S2a/S2b's shape) | §6's soundness list; `SlotImpR rtR` with only `rsWeight` (both prototypes) and the segment `targetS`/`shiftTarget` left | `gap4Imp_of_rsv` covers `evalM`, `evalL`, `tdot`, `linkWAll` at slot 0; `coord_le_deltaR` at `70 + N′`; axioms clean; the controls | `flag_gFinE` over budget → split `rsvOps2` into its own generator with its own flag lemma (R4FrE reads two) |
| **R3** (the chain library) | chain MLEs (square, product-with-inputs, Horner), the `phiTable`/`eqTable` tree, dyadic range sums; `Piece.chain` in the plan with `_eq`; KAT against `rows3` | a toy template (100 chains × 127 steps + 512 products × 25) evaluates in `≤ 1 ms` VM and the lemmas are kernel-checked | the shapes do not close in one stage → §5.3 for slot 0; re-plan the segment slots (then the only open R item) |
| **R4** (`rsWeight` templates) | claims template (prototypes 1 and 0) and the kind factor (prototype 0) as `KOp`s with `KOk`; rows at the second assignment; keyed through R3; `rsWeight` leaves `impRP` | V(N4) Δ `≤ 10 ms` for slot 0 and `≤ 10 ms` for `k = 4` segment slots; `rsWeight ∉ impRP rtR π` for `π ≤ 1` | Δ `> 10 ms` → §5.3 for slot 0 |
| **R5** (segment slots) | segment `tdot` (≈ 560 rows, R3's tree), `shiftTarget` (3.1 k: the digest bits from the arena's bit rows, `Eθ`'s tree), C2 (drop or pin the dead `evalM`/`evalL`) | `SlotImpR rtR = ∅` at both prototypes; `Gap4R.imp` closed | — |
| **R6** (lever, any time after R1) | `evalL4I` carry-automaton closed form; `evalL4I_eq` re-proved | V(N4) −11 ms own, −11 child | — |

R1 and R3 are independent and can run in parallel; R2 follows R1; R4 follows R3 (and R2 for the
fold); R5 follows R4. The orchestrator's merge order with B4 (`aggChk` rows) and PORT is as C1's:
the fold edits to `FRNodeRows4` are the integrator's.

## 9. Open questions

1. **`tdot` versus the thin margins.** Plain carry (168) fits with margins of 1 cell and 20 blocks;
   `tdot` touches finZ for every kind. I recommend `tdot`; the orchestrator may prefer the audit's
   numbers first (R0 decides).
2. **The kind element's cell.** RSV-V used the child's seed register; confirm in R0 that the
   header's kind byte register is one cell tied to the selector by `kindN`'s rows (S-E13a), and that
   the N8 parent's zero block asserts it zero (as `fLrEnd[48, …)` today).
3. **`rsWeight` for the segment slots** is the largest open item after this memo; §5.2's library is
   the only route found. If the orchestrator wants a price before R3, a one-stage probe (R3's toy
   template on the plan's evaluator) answers it.
4. **Retiring C1's `tplLW`/`FRVIRTplRepLW`** (381 lines, a KAT'd template with no consumer under
   this route): keep `KOp`/`rtK`/`rtST0`/`compileFromX_soundRW` (R4 uses them); drop the rest at the
   next golf, or keep `tplLW_ok` as a (−) control that the carried `linkWAll` equals the gate form.
