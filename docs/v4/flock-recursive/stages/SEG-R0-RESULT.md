# SEG-R0 (track SEG-R): RESULT — probes for the segment-program replay

Stage SEG-R0, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `2aa619d` = FOLD2
`97d578b` + the SEG-R memo; the Lean tree is FOLD2's). Build tree `logs/fr-build-SEGR0`: a copy of
`fr-build-SRA`, whose `src/` is byte-identical to HEAD's lean tree (checked file by file). MINE is
empty. The tree also holds a frozen copy of SIB's untracked `FRNodeRows4AskC.lean` (sha256 `533083ae…`,
`logs/SEGR0/AskC.sha256`), added as a library root. Probes are in `probe/` and copied to
`logs/SEGR0/probe/`: `SegOps`, `SegTpl`, `SegFit` and `SegV`. Logs are in `logs/SEGR0/`.

Every lake command and every probe ran under `systemd-run --user --scope -p MemoryMax=16G
-p MemorySwapMax=0 -- timeout …`, each pinned with `taskset`. The probes ran on cores 29 and 31 while
the load average was 1.6–2.9 on 32 cores. CF's and SIB's builds were running on other cores at the
time. Nothing is committed, no worktree source was edited, and no agents were spawned.

## 0. Verdict

- **The kill line is not hit.** The kill line is locals > 49 k in the F-point form. The F-point segment
  replay needs **38.5–39.7 k locals per slot** with sparse rows, and **42.9–44.2 k** with CF's
  power-of-two padding. Two cell bands give 49,062 free cells.
- **The orchestrator's ≈ 5 k margin line is hit if the templates are built as the memo describes**
  (unfolded, with CF padding: margin 4.9 k, or 4.1 k with the memo's `shiftTarget`/`targetS` forms). It
  is **not hit** if the 10 constant claim coordinates are folded (margin **6.2 k**). It is also not hit
  if a **third cell band** is used. This band was measured free and is not in the memo:
  `[1,003,010, 1,015,728)`, 12,718 cells between the instance groups, which makes the margin ≥ 17 k.
  **Recommendation:** fold the constants (§1.1). Take the third band as well, or else merge the cell bands
  (per-prototype `arA1`) before R1 if CF's padding grows.
- **The K-general fallback does not fit two bands** (49,448 locals sparse).
- **Rows fit** once `arR2N` is cut to its used extent. With SIB that extent is **154,333** (cut to
  154,368), which leaves band A 34,816 and band B 27,136, together **61.9 k ≥ 43.2 k** (CF-padded). Band
  B is **27.1 k with SIB, not the memo's 45 k**. The slack at the top of `[arR2, arR2 + arR2N)` is
  contiguous, not interleaved, because the template rows are `arR2 + k` for `k < |askRowsT π|`.
- **Memo corrections** (each measured on the compiled program, §6):
  - Claim 1 (index 0) has **6** constant coordinates, not 7. The coordinate memo-numbered 7 is a `chF`.
  - Only the 6 constant claim coordinates and the 4 zero ones are shared across kinds. **Every
    `mulKF` coordinate is a separate cell per kind**, so the input mux costs **186 products** (plus 6
    for `ρ`), and the `f₁` forcing rows number **186**, not 75. The memo's per-kind mux on `τ` and on
    `targetS`'s `r` is not needed: the compiler's `packFK` has already muxed them, and their forms are
    identical at every kind.
  - The templates are smaller than the memo estimated: `shiftTarget` is **1.3 k** rows (memo ≈ 3.1 k) and
    `targetS` is **0.14 k**.
- **`evalM` per segment check: 64–66 ms** (3.x `evalMT nodePlan`). `evalL` costs 3.5 ms.
  **Building `nodePlan` fresh takes 1.45–1.57 s; `lPlan` takes 48 ms.**
- **Critical for the start-up saving:** `nodePlan`, `lPlan` and `implCN` are **initialised eagerly by
  `FRVerifierImplCore`'s module initializer**, whether or not anything references them. A plan-free
  `implB` alone saves nothing at start-up. They must also stop being compiled top-level constants
  (`noncomputable`, or a `Unit →` function). See §4.
- **No segment-side theorem reads `spec.evalM`/`spec.evalL`** (§5).

## 1. Template sizes (item 1; `SegTpl`, `logs/SEGR0/segtpl1.log`, `segtpl2.log`)

How they were built: with R3's `FRVIRTplChain` gadgets (`phiG`, `sqChainF`/`sqChainK`, `prodK`, `mulK`,
`smulK`, `mulF`), driven by a `StateM` wrapper that appends each `GM` at the next local. Each template was
checked by a KAT with honest gate evaluation at the three segment widths (L32 25, P30 23, N30 24). The
reference values are `Impl.rsWeightF r ps κ 1 ρ`, `Impl.shiftTargetI` and `targetSSegI`. At every width
and in every variant, **all outputs are equal and all rows hold**. Two negative controls also pass: a
perturbed local fails a row, and a perturbed claim coordinate changes `rsWeightF`.

The P30 and N30 KATs run on the 25-wide template with zero padding. They therefore also check
numerically that **`β = 1` collapses claim 2's kind factor to plain `eq`** (the `wEvalKF` and `wEvalKC`
branches) at `|ρ|` = 23, 24 and 25.

### 1.1 `rsWeight` (one template at `n = 25`, three claims)

| Variant | gates = locals = rows | terms | parts | CF padded (chains 2^7, stage 2^8) |
|---|---|---|---|---|
| F-point, no folding (memo) | **38,193** | 208,015 | phiG 247, chains 75 × 127 = 9,525, stages 128 × 222 = 28,416, κ^j 5 | 42,620 (+4,427) |
| **F-point, 10 constants folded** | **36,923** | 204,205 | chains 65 × 127 = 8,255 | **41,340 (+4,417)** |
| F-point, folded + the 4 zeros hoisted | 35,780 | 196,966 | stages 128 × 213 | 41,340 (213 still pads to 256: no gain under CF) |
| K-general (`sqChainK`) | 47,718 | 293,740 | chains 75 × 254 = 19,050 | 52,220 (+4,502) |

What "folding" assumes: the 6 pinned constants of claim index 0 (the `pinnedRho` values, `f₁ = 0`) and
the 4 zeros of claim index 2 are template constants. The zeros' forms are syntactically zero
(`zeroLin`). The pinned constants' forms are `P.kc` (`c·Σ_κ sel_κ`), so they need about 10 forcing rows
(`one·form = c`). Folding removes 10 chains.

**Per slot, with the input mux and forcing rows from the compiled forms (§6):**

| | locals | rows |
|---|---|---|
| template (folded) | 36,923 | 36,923 |
| mux: claims' `f₀` at kind-varying positions | 186 | 186 |
| mux: `ρ` (positions 46–49, L and N only) | 6 | 6 |
| forcing rows `one·f₁ = 0` (every kind's `mulKF` claim cell) | — | 186 |
| forcing rows for the 10 constants | — | ≈ 10 |
| copy rows | — | 2 |
| **total, folded** | **37,115** | **≈ 37,313** |
| total, not folded | 38,385 | 38,573 |
| total, K-general (`f₀` and `f₁` muxed: 378; no `f₁` rows) | 48,096 | 48,098 |

### 1.2 `shiftTarget` (`shiftTargetI κs τ θ bnd`; `τ`, `θ`, `bnd`, `κs` have identical forms at every kind: no mux)

| Variant | gates | terms | parts | + decomposition | locals | rows |
|---|---|---|---|---|---|---|
| eq table over 10 `θ` coordinates (memo) | 1,553 | 7,753 | eq table 1,022, digest sums 512, `eq(τ, L)` 17, final 2 | 512 bit locals, 512 `bit·bit = bit`, 4 linear rows, 1 copy | 2,065 | 2,070 |
| **8 coordinates × `(1−θ₈)(1−θ₉)`** (σ < 256) | **787** | 3,667 | 254 + 512 + 17 + 4 | same | **1,299** | **1,304** |

The decomposition row `one·Σ_b bit_b·bitBasis b = e` holds on all four halves in the KAT.

### 1.3 `targetS` (`targetSSegI r`; `r` (af37) has identical forms at every kind: no mux)

| Variant | gates | terms | parts | locals | rows (+ 18 `b·b = b`, + 64 copy) |
|---|---|---|---|---|---|
| 64 output products (memo) | 116 | 1,620 | range factor 52, outputs 64 | 116 | 198 |
| **outputs linear: `α_σ R + β_σ (r₀R)`** (the leaf part is affine in `r₀`) | **53** | 233 | 52 + 1 | **53** | **135** |

The range factor costs 52 gates: 17 suffix products of `1 + b_j + r_j`, 18 products `b_l(1 + r_l)` and
17 products by the suffixes.

## 2. Rows: the template range and the bands (item 2; `SegFit`, `logs/SEGR0/segfit-N2.log`, `segfit-N4.log`)

Method: `nodeIRowsP planOf4 κ` gives every row of the node (N2: 3,547,650 rows; N4: 5,348,572). The
probe takes the first segment slot's region (σ = 1) and records every row index in it, and every cell any
row reads in it. Instances, skeleton, arena₁ and bits are added as reserved ranges. Band offsets below
are region-relative.

| | p0 | p1 |
|---|---|---|
| `askRowsT π` at HEAD (FOLD2) | 114,320 | **135,997** |
| SIB's `sibTG` rows (frozen `AskC`) | 16,594 | 18,336 |
| **with SIB** | 130,914 | **154,333** |
| `arR2N` (FOLD2) | 180,560 | |

The used extent is `[arR2, arR2 + |askRowsT 1|)`, contiguous (`askPI`), so all of the slack is at the
top. This answers the memo's open question §8.1.

**Free row runs ≥ 256 in a segment region as placed (N2; N4 identical except for the link tail):**

| Run | size | note |
|---|---|---|
| `[686,080, 720,896)` | **34,816** | **band A**: prototype 1 ends at 686,079. With the memo's 2,048-row margin it is 32,768. |
| `[856,893, 901,456)` | **44,563** (HEAD) / **26,227** (with SIB) | the slack of `arR2N`, inside the template index range: usable only after the cut |
| `[1,014,792, 1,015,808)` | 1,016 | `repSegB`'s `2^10` minus `linkWAll`'s 8 rows |
| `[1,033,638, 2^20)` | 14,938 (N4: 13,976) | the unused tail of the link region (reserved by `linkN`; not counted) |
| six runs of 264–1,794 inside the prototype | — | unusable |

**The `arR2N` cut (request to the integrator), 2^8-aligned as `arRb` is:**

| | `arR2N` | `arR1` | arena₁ end | `arRb` | bits end = new `repSegB` | **band B** `[…, 2^20 − 2^15)` | A + B |
|---|---|---|---|---|---|---|---|
| HEAD (no SIB) | 136,192 | 857,088 | 954,032 | 954,112 | 970,496 | **45,312** | 80,128 |
| **with SIB** | **154,368** | 875,264 | 972,208 | 972,288 | 988,672 | **27,136** | **61,952** |

Prototype 0 is unaffected: its rows end at 706,303 < `arR2`, and its template rows take 130,914 with
SIB. If the integrator wants headroom for later ask templates (`closeTG` has 0 rows today), every row of
headroom comes out of band B.

## 3. Cells and the fit (item 3; same logs)

**Free cell runs ≥ 256 in a segment region:**

| Band | Range | size | with SIB |
|---|---|---|---|
| 1 (memo) | `[405,504, 441,152)` (above the bits, below the lowest instance) | **35,648** | unchanged |
| 2 (memo) | `[277,402, 290,816)` (skeleton end → arena₁) | **13,414** | unchanged |
| **3 (new)** | `[1,003,010, 1,015,728)` (a gap between instance groups) | **12,718** | unchanged |
| small | `[387,760, 389,120)` minus 4 used cells: 336 + 1,020; 387; 264; 3 × 1,794 at the top | — | — |

**SIB adds no cells.** Its 18,336 rows read 51,984 cells of the region, all of them already used or
reserved (arena and bits cells). There are 0 new cells and 0 entries outside region 1.

**Demand per segment slot** (§1; `evalM`/`evalL` zero rows 6; `linkWAll` 8, existing):

| Form | locals | rows | margin, 2 bands (49,062) | margin, 3 bands (61,780) |
|---|---|---|---|---|
| **recommended**: F-point folded, `tplSTS` 8-coordinate, `tplTSS` linear, sparse | **38,467** | **38,766** | **10,595** | 23,313 |
| recommended, CF-padded (`rsGSeg` chains 2^7, stage 2^8) | 42,884 | 43,183 | **6,178** | 18,896 |
| F-point not folded, CF-padded | 44,164 | 44,453 | **4,898** (< 5 k) | 17,616 |
| memo's forms (not folded, 10-coordinate, 64 products), CF-padded | 44,993 | 45,282 | 4,069 (< 5 k) | 16,787 |
| K-general, sparse | 49,448 | 49,551 | **−386** | 12,332 |
| K-general, CF-padded | 53,950 | 54,053 | −4,888 | 7,830 |

Rows: every form above fits band A + band B (61,952 with SIB). The margin is ≥ 16.7 k for the
F-point forms (CF-padded) and 7.9 k for the K-general one. Contiguity: CF's stage group needs 32,768 contiguous rows and locals. That fits band A
(34,816 rows, or exactly 32,768 with the margin) and cell band 1 (35,648). The chain group (8,320) fits
band B and cell band 2.

**Verdict against the kill lines.**

- Locals > 49 k with the F-point form: **no**. The worst case is 44,993.
- The orchestrator's cell margin after CF's padding below ≈ 5 k: **yes for the memo's unfolded forms**
  (4.1–4.9 k), **no once the 10 constants are folded** (6.2 k). With a third band it is 16–19 k.

**Report:** fold the constants, and either use band 3 in `repMapC` (a three-band map) or merge the cell
bands (per-prototype `arA1`) before R1. Without folding, "merge the cell bands first" applies.

## 4. V and start-up of the 3.x plan (item 4; `SegV`, `logs/SEGR0/segv1.log`, core 29)

`progS32` under `Sub4.implS` (= `implSeg Impl.implCN`), 151,226 ops, run op by op on a pseudo-random
proof (`π[0] = L32`). Seven runs; the figures are per check:

| Op | best | median | operand sizes |
|---|---|---|---|
| **`evalM`** (`TEval.evalMT nodePlan`) | **63.9 ms** | **65.7 ms** | `|τ| = 23`, `|σ| = 25` |
| `evalL` (`evalLT lPlan`) | 3.5 ms | 3.5 ms | 17, 25 |
| `rsWeight` | 39.2 ms | 39.6 ms | |
| `targetS` | 3.9 ms | | |
| `shiftTarget` | 0.28 ms | | |
| whole segment program (instrumented) | 236 ms | 238 ms | |

Pinning `evalM`/`evalL` therefore saves **≈ 67–69 ms on every segment (leaf) check**. This is a
different check from the node check, which is where the new template rows add their V.

**Building the plans fresh** (each argument depends on the command line, so neither is a closed term):
`TEval.planOf (finC finPf)` took **1,450 / 1,536 / 1,572 ms**, and `TEval.planL Layout.lRows` took **48 ms**.

**Start-up: which constants carry the plans (orchestrator item 1; `logs/SEGR0/grep-nodePlan.txt`).**

| Where | `implCN` | `nodePlan` | `lPlan` | in `Solution`'s import closure |
|---|---|---|---|---|
| `FRVerifierImplCore` (defs) | def | def | def | **yes** |
| `FRSubmission4V` (`implB := Impl.implCN`; C: `implB`, `implS`, `implNN2/4/8`) | code | — | — | yes |
| `FRSubmission4Cert` (C: `Vnode4`'s lambda, via `implB`) | code | — | — | yes |
| `FRNodeRsvLink` (`implR := { Impl.implCN with evalM := … }`, a control) | code | — | — | no |
| `FRNodePlan` (`implCN_eq`, rfl), `FRNodeRows4RepF` (`unfold Impl.implCN` in a proof) | proof | — | — | no |
| docstrings: `FRSoundness4XRunG`, `FRSubmission4`, `FRSubmission4Cert` | — | — | — | — |
| `ColdWarm.c` (a probe) | code | — | — | — |

The only compiled references to `nodePlan` and `lPlan` are inside `FRVerifierImplCore.c`. But that
module's initializer runs `nodePlan = _init_…nodePlan()`, `lPlan = …` and `implCN = …` **eagerly**
(lines 378–383 of the C file). This matches INIT §1's finding that every top-level nullary `def` is
computed at process start. `FRVerifierImplCore` is in `Solution`'s closure (320 modules,
`solution-closure.txt`).

So the **−1.5 s needs two edits**:

1. The plan-free `implB` (`implC0`). This also rewires `FRSubmission4Cert`'s `Vnode4`.
2. Make `Impl.nodePlan`, `Impl.lPlan` and `Impl.implCN` **non-initialised**. Either mark them
   `noncomputable`, which leaves no IR and therefore no initializer, or turn them into
   `Unit →` functions. In both cases `FRNodeRsvLink.implR` must move to `implC0`. Otherwise
   `noncomputable` propagates to it.

`implCN_eq` (rfl) and the proofs are unaffected.

## 5. Readers of `spec.evalM`/`spec.evalL` on the segment side (item 5; `logs/SEGR0/grep-evalM-readers.txt`)

- `OpImpl.Meets` has `evalM` and `evalL` as conjuncts 8 and 9. No segment-side file projects them: the
  `.2⁷.1` and `.2⁸.1` hits are on other structures.
- The segment soundness files (`FRSoundness4P4aSeg`, `FRSoundness4XRun(G)`, `FRSegment`,
  `FRSoundness4R4FrS`, `…Link`, `…Start`, `…FrCtrlB`, `FRSoundnessAccSeg`, `FRNodeSound4`,
  `FRSegTarget4`) contain no `evalM`/`evalL` reads. Their `hL` names are unrelated hypotheses.
- `R4FrE`'s `hM`/`hL` (lines 484–611) are node-only (`ν`, `e_fin4`). `FRSoundness4R4Fin:526`'s `evalM` is
  under `!P.kv.node κ ||`.
- `specSeg` users (`FrE:704`, `FrS:520`, `Link:36–41`, `Start:220`, `XRun:39–45`, `FrCtrlB`, `VerifierC4:139`)
  read `tensorW`, `rsWeight`, `shiftTarget`, `shiftMask`, `slotW` and `linkWAll` only.
- `implSeg_meets` passes `h8`/`h9` through. With both sides pinned they become `rfl`.
- **The precondition holds**: pin `evalM`/`evalL` (route (a) §4.1). The fallback (e) is not needed.

## 6. The memo's facts, checked on the compiled program (item 6; `SegOps`, `logs/SEGR0/segops.log`, `segops2.log`)

The probe reads `protoProg 1` (151,226 ops, 143,392 registers) and `protoCS 1` (`cs.next` 1,325,978;
14 per-kind slots). It maps each register to its defining op. Operand forms are `kOps cs ι` per kind,
exactly what a `KOp` sees.

| Fact | Result | Cheap in Lean, or forcing rows? |
|---|---|---|
| `rsWeight` (op 101,781) `act` false at every kind | **true** (`act = [L false, P false, N false]`); `β = r883` is unread | **Cheap**: a literal of the op, checked by `kRSS.cov` (a `Bool` on the op). No rows. |
| three claims per kind; widths | L `ak25` ×3, P `ak23` ×3, N `ak24` ×3; `ρ` the same width; `r″ af7`, `κ f`, `β f` | **Cheap**: `inOk` on the types (below) |
| every claim coordinate an F-point | **true**. Claim index 0: 6 `const K` (pinned values, `f₁ = 0`) + 19/17/18 `mulKF (const K 1) chF`. Index 1: 25/23/24 `mulKF (const K 1) chF`. Index 2: 3 `mulKF` + **4 `const K 0`** + 18/16/17 `mulKF`. Every `mulKF` has `a = const K 1` (so `a.f₁ = 0`) at every kind. | **Forcing rows** for the `mulKF` coordinates: their `f₁` is a fresh cell per kind (186 cells), equal to 0 only through the prototype's own `mulKF` row (`x·0 = cell₁`), which `KOk` abstracts away. So: 186 rows `one·f₁ = 0`, no locals. The `const` coordinates' `f₁` forms are syntactically zero (`zeroLin`): decidable at plan time, no row. |
| `r92569 = const K 1` | **true** for every `mulKF` claim coordinate (the `a` operand is `const K 1` at all kinds) | Not needed once the `f₁` rows exist. Checking it on the 151 k-op program by `decide` would be expensive; a generator lemma would be cheap. |
| `evalM` (op 65,814) and `evalL` (65,819) feed only an all-kinds-inactive `assertEq` | **true**. Forward closure: `evalM → mulF, mulF, addF, addF, addF, mulF → assertEq` (op 65,828) and `evalL → mulF, mulF, addF, addF, mulF, addF, mulF →` the same `assertEq`, with `act = [false, false, false]`. No other reader, and no FS absorb. | **Not needed for soundness.** After the pin, `zeroRows` binds the six cells to the pinned value (`RTOkW` with no hypothesis). If a proof ever needed "the pin does not change V", the cheap route is `gFinE0`'s `act` literal (a structural generator lemma), not `decide` on the program. |
| operand forms across kinds (the input mux) | `targetS` `r`: 37/37 positions identical. `shiftTarget` `τ`, `θ`, `bnd`, `κs`: all identical (the compiler's `packFK` mux already applied). `rsWeight` `r″`, `κ`: identical. `ρ`: 46 of 50 identical, 4 kind-varying (6 products). Claims, per claim index aligned: `f₀` 19 + 25 + 21 kind-varying positions (54 + 72 + 60 = **186 products**), 6 identical (the pinned constants), 4 zero. | Decidable at plan time on forms (`kOps`). |

**`kRSS.cov`/`inOk` (orchestrator item 2).**

- `cov op := match op with | .rsWeight _ ps _ _ act _ => kinds.all (!act ·) && kinds.all ((ps ·).length == 3) | _ => false`.
- `inOk ts := ts = [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] ∧ 23 ≤ m ≤ 25`. The operand list is
  `rsArgs`'s `[r, κ, β, ρ] ++ ps ι`. This gives `Meets`' `r.size = 7` and `23 ≤ |ρ|`.
- Any other type list at any index already yields `rejRow` through `kRows` (`bs.all K.inOk` false).
- An `rsWeight` with some `act` true is not covered. It stays an import and is not rejected, because
  `inOk` sees types, not the op. If a `rejRow` is wanted there as well, give `KOpD` an op-aware
  `inOk : Op → List Ty → Bool`, or make `cov` accept every `rsWeight` and test `act` inside it.
- `KOkD`'s derived facts are the 186 `f₁ = 0` forcing rows plus, if folding, the ≈ 10 constant rows.

## 7. `repSegB` (orchestrator item 4)

`repSegB = 31·2^15 − 2^10 = 1,014,784 = arRb + arNb` today. `linkWAll`'s 8 segment rows sit at
`[repSegB, repSegB + 8)`. Its `2^10` room ends exactly at the link region (`repRow0_ctl`:
`repSegB + 2^10 = slotM4 − linkN`).

With the cut, define **`repSegB := arRb + arNb`** symbolically. That is 988,672 with SIB, or 970,496
without SIB. It becomes the first row of band B, which then reaches up to `slotM4 − linkN`. The
segment's replay rows then lie in band B from `repSegB`, with the overflow in band A.

| Lemma or definition | Change |
|---|---|
| `repConsts` (`FRNodeRows4Fit:514`) | `arRb + arNb ≤ repSegB` becomes `rfl`. `repSegB + 2^10 + linkN ≤ slotM4` becomes `repSegB + |B| + linkN ≤ slotM4` with `|B| = slotM4 − linkN − repSegB`. `arR2 ≤ repSegB` stands. The literal `repSegB = 1014784` changes to the new value. Proof: the same `norm_num`. |
| `repRow0_ctl` (`FRNodeRows4RepFCtrl:33`) | `repSegB + 2^10 = slotM4 − linkN` becomes `repSegB + |B| = …`. N8's slot 0 (a segment) is at the new `repSegB`. |
| `slotA_idx`, the replay-index lemma (`Fit:542`, `:582–587`) | `[repSegB, repSegB + 2^10)` becomes `[repSegB, slotM4 − linkN) ∪ [688,128, arR2)`. Band A needs a new init check: prototype 1's rows end below 688,128 (they end at 686,079). Prototype 0 regions do not use band A (their rows reach 706,303). |
| `repAllRows`'s rejecting row at `(repSegB, rejR κ)` (`FRNodeRows4:301`, `Plan:1411`) | Moves with `repSegB`. It stays free in region 0 for both prototypes. |
| `repFitB 1` | `2^10` becomes `|B| + |A|` rows; locals per the band map (§3) |

## 8. Files

- **Probes** (under `logs/fr-build-SEGR0/probe/`, copied to `logs/SEGR0/probe/`): `SegOps.lean` (§6),
  `SegTpl.lean` (§1), `SegFit.lean` (§2–3) and `SegV.lean` (§4).
- **Logs** (`logs/SEGR0/`):
  - probe output: `segops.log`, `segops2.log`, `segtpl1.log`, `segtpl2.log` (with the measured
    constants), `segfit-N2.log`, `segfit-N4.log`, `segv1.log`;
  - greps and the import closure: `grep-evalM-readers.txt`, `grep-nodePlan.txt`,
    `solution-closure.txt`, `closure.py`;
  - build output: `build-*.out`;
  - SIB's module: `AskC.sha256`, `FRNodeRows4AskC.lean.copy`.
- **Run times**: `segops` 20 s, `segtpl` 21 s, `segfit` N2 62 s (4.0 GB), N4 85 s (5.1 GB), `segv` 26 s.
