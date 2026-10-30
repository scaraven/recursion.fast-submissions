# SEG-R1 (track SEG-R): RESULT — the `rtKD` wrapper, `rsWeight`'s segment replay, the dead ops pinned, the init cut

Stage SEG-R1, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `0f7d3a3` = SEG-R0).
Build tree `logs/fr-build-SEGR1` (a copy of `fr-build-SEGR0`, re-snapshotted onto HEAD by `snap1.sh`: HEAD
files by `git show`, MINE symlinked, **every other non-HEAD module removed**, so SIB's/CF2's untracked
modules are not in the tree). Logs `logs/SEGR1/`. Nothing committed, no agents spawned. Every lake/lean
command ran under `systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0 -- timeout …`.

## 0. Verdict

| item | status |
|---|---|
| 1. `rtKD` (generic wrapper: canonical inputs, kind mux, zero-forcing rows, template forcing rows, constant hints) | **done**, `rtKD_okW : KOkD → RTOkW` |
| 2a. `rsWeight` template (F-point claim part, 10 constant coordinates folded) | **done**: `rsSegT`, 36,923 gates (= SEG-R0), `ok_rsSegT`, `rsWeightF_seg`, `kRSS_ok`; KATs at 25/23/24 pass |
| 2b. `shiftTarget` (787 gates + 512 bit locals), `targetS` (53 gates) templates | **not done** (context budget; §6 has the exact plan). Both stay imports of prototype 1 at `rtC1d 1`. |
| 3. `kRSS.cov`/`inOk` | **done** (act all false, 3 claims, `[af 7, f, f, ak m ×4]`, `23 ≤ m ≤ 25`) |
| 4. `evalM`/`evalL` pinned to zero in `implSeg`, zero rows | **done** (`rtEvZ`, `rtEvZ_okW`, no hypothesis) |
| 5. init win | **done**: start-up **−2.0 s** user (median 21.6 → 19.6 s), segment check **−70 ms** |
| assembly | `rtSeg1 = linkWAll ∪ evalM/evalL ∪ rsWeight`; `rtC1d`, `rtC1d_ok`, `repOkW_rtC1d`, `repOkW_rtC1dB` (at `Sub4.implB`) |

`lake build FR Solution FRSubmission4Fin FRNodeRows4RepSeg start0` green (`build-final.out`, 5,237 jobs).
Axioms: only `propext`, `Classical.choice`, `Quot.sound` (`axioms.log`, 15 declarations incl.
`Challenge.certified`). Source rule: 467 files, 0 findings (`source-rule.log`). No `sorry`.

**The new modules are not imported by `FR.lean`** (not my file): the orchestrator should add
`import FRNodeRows4RepSeg` (it pulls `FRNodeRows4RepSegK`, `FRVIRTplSegR`) to `FR.lean`. They build as
explicit targets here.

## 1. Mechanism: `rtKD` (`FRNodeRows4RepSegK`, 319 lines)

- **`KOpD`** = C1's `KOp` with one template over `W` **canonical inputs**: `lay ts p` (the encoding
  position canonical input `p` reads at operand types `ts`; `none` = `0`), `zf ts` (encoding positions
  forced to `0`), `T : List (Option F) → GM (List LinT × List RowT)` (the template, given per-input
  constant hints, with its own forcing rows over its inputs/locals — the hook for `shiftTarget`'s bit
  decomposition and `targetS`'s `b·b = b`).
- **The mux** (`kdPos`/`kdAll`): a canonical input whose three kinds' forms are syntactically equal is
  that form (hint `some 0` if zero, `some c` if it is `P.kc (fun _ => c)`: the pinned constants, value by
  `kc_ev`, **no row**); otherwise three mux locals `m_ι` with rows `sel_ι · f_ι = m_ι`, input `Σ m_ι`.
  Simplification vs SEG-R0: no zero-skip (always 3 products per kind-varying position): +15 locals, the
  proof is one `cases ι`.
- **`kdRows`**: mux rows, zero rows `one · f = 0` (every kind's forced positions), the template's gate
  rows and forcing rows (locals after the mux's), copy rows on the import's cells; `rejRow` on any other
  shape (no blocks, `inOk` false at some index, forms or outputs not below `B`, wrong output count).
- **`KOkD impl ι K`** (pure functions): at the selected index, the inputs are the operands' encodings
  through `lay`, the forced positions are zero, hints hold ⇒ wherever the gate equations and forcing rows
  hold, the outputs are the value. **`rtKD_okW : KOkD impl ι K → RTOkW impl X (rtKD K B cb) ι B`.**
- **`rtEvZ`** (`isEvML`, `zeroF3`): `one · out = 0` on the three `F` cells of `evalM`/`evalL`.
  **`rtEvZ_okW`**: `RTOkW (implP impl₀ base 1 ι) (Xof 1) (rtEvZ B) ι B`, no hypothesis.
- Fixed point under recursion: rows only, no op/import/format/FS change (as SEG-R §3 (a)).

## 2. `rsWeight` (`FRVIRTplSegR` 195 lines, `FRNodeRows4RepSeg` 363 lines)

- **`rsSegT cst`** (133 canonical inputs: `r″` 0–6, `κ` 7, `ρ_l` at `8+2l`/`9+2l`, claim `j` coord `l`'s `f₀`
  at `58+25j+l`): `phiG`, `chainC` (`sqChainF 127`, or 128 constants when hinted), per claim `rsStage`
  (`foldL` over `k < 128`: `prodK` of 25 factors `1 + a^{2^k} + ρ_l` then `smulK c_k`), `κ²`, `κS₁`, `κ²S₂`.
  **`ok_rsSegT`**: outputs = `encK (rsSegV …)` of the input values.
- **`rsWeightF_seg`**: `|r″| = 7`, three claims of `m` F-point coordinates, `|ρ| = m`, `23 ≤ m ≤ 25` ⇒
  `Impl.rsWeightF r ps κ 1 ρ = rsSegV r κ (ρ padded to 25) (claims' f₀)` — via `rsWeightF_eq`,
  `rsWeight_meets`, `Snd.kwSL_one` (claim 2's kind factor at `β = 1`), `eqPts_pad` (char 2, zero padding),
  `sqIter_ofF`.
- **`kRSS`** = `⟨isRSS, rsArgs, rssIn, 133, rssLay, rssZf, rsSegT, [.k]⟩`:
  - `cov` (`isRSS`): `.rsWeight` with `act` false at every index **and** 3 claims at every index. Any
    other `rsWeight` is **not covered and stays an import** (it is not rejected): `cov` cannot be made to
    reject without an op-aware row, and `protoProg 1` has no such op (SEG-R0 §6); at R2 `impBP (rtC1d 1)`
    would list it if one appeared.
  - `inOk` (`rssIn`): `[af 7, f, f, ak m, ak m, ak m, ak m]`, `23 ≤ m ≤ 25`. Other types at any index ⇒
    **`rejRow`** (kdRows' `inOk` check).
  - `zf` (`rssZf`): every claim coordinate's `f₁` (`3m` per kind: 216 rows over the three kinds; the 30
    rows on the constant coordinates are `one · 0 = 0`; SEG-R0's 186 are the `mulKF` ones) ⇒ F-points.
- **`kRSS_ok`**: `KOkD (implP impl₀ base 1 ι) ι kRSS`, given `impl₀.rsWeight = Impl.rsWeightF`
  (`SegBase`; `segBase_implB : SegBase Sub4.implB := ⟨rfl, rfl⟩`).
- **Controls** (kernel): `isRSS_pos`; `isRSS_neg_act` (act true at P30 ⇒ not covered); `isRSS_neg_claims`;
  `rssIn_pos` (23/24/25); `rssIn_neg` (26, 22); `rssIn_neg'` (claim width ≠ ρ width; `af 8`); `rssZf_pos`.

### 2.1 KATs (`probe/SegKat.lean`, `logs/SEGR1/segkat.log`; honest gate evaluation of the Lean `rsSegT`)

| width | gates = locals = rows | out = `encK (rsWeightF r ps κ 1 ρ)` | rows hold | (−) perturbed local | (−) `f₁ ≠ 0` moves `rsWeightF` |
|---|---|---|---|---|---|
| L32, m = 25 | 36,923 | true | true | fails a row | true |
| P30, m = 23 | 36,161 (padding hinted 0) | true | true | fails a row | true |
| N30, m = 24 | 36,542 | true | true | fails a row | true |

**On the real program** (`repRowsP rtSeg1 1`, the compile trail of `protoProg 1`): **37,362 rows, 0
rejecting rows** (`rtC1c 1`: 8). Breakdown: linkWAll 8, evalM/evalL 6, mux 207 (69 kind-varying
positions × 3: 65 claim + 4 ρ), zero rows 216 (75 + 69 + 72), template 36,923 (the 10 constants were
detected and folded), copy 2. Locals per segment slot: 207 + 36,923 = **37,130**.
Not yet checked: the full node instance with a real witness (mux/zero rows on real cells) — R2's MxKat.

## 3. Item 4: the pin (`FRSegTarget4`)

`implSeg impl₀ := { impl₀ with …, evalM := fun _ _ => (0,0,0), evalL := fun _ _ => (0,0,0) }`,
`specSeg` likewise; `implSeg_meets` keeps its statement (conjuncts 8, 9 are `fun _ _ => rfl`).
SEG-R0 §5's precondition (no segment-side reader) held: the full build is green with no other change.

## 4. Item 5: the init cut, and statement changes

Route (deviation from "`implB := implC0`", same effect, smaller blast radius): **`implB` stays
`Impl.implCN`** (now `noncomputable`), so `Gaps4`, `Open4`, `repOk_rtC1cB`, `implT_implB` (RepF, CF2's),
`gap4Imp_*` (SIB's) and the certificate's definitional `implB ≡ implC (finC finPf) lRows 0` are untouched.
The *compiled* constants are built on the new plan-free **`Impl.implC0`** (FRVerifierImplCore: `implCWith`'s
fields, `evalM`/`evalL` zero):

| declaration | change |
|---|---|
| `Impl.nodePlan`, `Impl.lPlan`, `Impl.implCN` | `noncomputable` (no initializer); bodies unchanged |
| `Impl.implC0` | new |
| `Sub4.implB` | `noncomputable`; body unchanged |
| `Sub4.implS` | `implSeg Impl.implC0` (was `implSeg implB`); **`implS_eq : implS = implSeg implB`** |
| `Sub4.implNN2/4/8` | `implN4F (fun _ => Impl.implC0) ν`; **`implNN_eq`** |
| `implSeg_implC0`, `implN4F_implC0` | new: `rfl` congruences **generic in the plans** (no plan is ever whnf'd) |
| `VsegF_eq`, `VnodeF_eq`, `V4F_eq`, `sub4_V` | **statements unchanged**; the first two now `rw [implS_eq]`/`implNN_eq` |
| `Sub4.Vnode4` (Cert) | `noncomputable abbrev` (Prop-only use) |
| `N4s.implR` (RsvLink control) | `{ Impl.implC0 with evalM := … }` |
| `implSeg`, `specSeg` | `evalM`/`evalL` pinned (item 4) |

No other statement changed. `ColdWarm` (probe) exists only in the flock worktree's old build trees; any
probe that names `Impl.implCN`/`Sub4.implB` in compiled code must switch to `Impl.implC0`/`Sub4.implS`.

**A/B** (`logs/SEGR1/ab.sh`, alternating, core 27, while builds ran on cores 0–23; binaries `binA` = HEAD,
`binB` = HEAD + items 4–5):

| probe | A (HEAD) | B | Δ | log |
|---|---|---|---|---|
| `start0` (badge import closure), user s, 5 rounds | 21.53, 21.54, 21.61, 21.91, 23.50 | 19.12, 19.44, 19.56, 19.82, 19.92 | **−2.05 s** (median) | `ab-start0.log` |
| `segv` (one segment check, `progS32`), median of 7 per run, 3 runs | 246.5, 255.9, 248.0 ms | 174.7, 177.8, 183.6 ms | **≈ −70 ms** (evalM 65–70 ms, evalL 3.5 ms → 0) | `ab-segv.log` |

## 5. Kernel / build cost

Per-module `lake env lean` (elaboration + kernel, user s, under load): `FRNodeRows4RepSegK` 40.0,
`FRVIRTplSegR` 4.9, `FRNodeRows4RepSeg` 10.6. `FRSubmission4V` 4.1 → 8.4 s in the build log (load; its new
proofs are two `rw`s). `RepSegK`'s 40 s is a golf target (probably `kdPos_ev`'s `cases ι <;> simp` and
`rtKD_okW`'s `simp`s); none of it is on the certificate path until R2. Trap found: `congr 1` on
`encK A = encK B` with `B = rsWeightF …` whnf's `rsWeightF` (heartbeat timeout) — use `congrArg encK`.

## 6. What remains for R1 (`shiftTarget`, `targetS`), exactly

Both are `KOpD`s on the same wrapper; SEG-R0's `SegTpl` shapes are the templates.

- **`kTSS`** (`targetS`, `[af 37]`, `lay p = p` for `p < 37`, `zf = []`): template `tsSegT` = 52-gate range
  factor `R = Π m_j + Σ_l b_l(1 + r_l)Π_{j>l} m_j` (`m_j = 1 + b_j + r_{1+j}`, `b_l = I (19+l)`), one gate
  `r₀·R`, outputs `a0_σ R + (a1_σ − a0_σ)(r₀R)` (`a0/a1 = targetSLeafI` at `r₀ = 0/1`, computed at
  build), forcing rows `⟨I(19+l), I(19+l), I(19+l)⟩` (18). Lemmas: (i) `prefixP n e (c+1) = prefixP n e c +
  prodAt e c` (from `prefixP_eq`); (ii) `prefixP`'s low-bit recursion at `c = val(L)` gives
  `S<(L) = S<(L') + [L₀](1 − r₀)·eq(r', L')` = the template's `Q<` recursion, with `testBit_lastAtV` for
  the bits; (iii) `targetSLeafI r` is affine in `r[0]` (`eqTable_ofFn_getD`, `Fin.prod_univ_castSucc` on
  coordinate 7 of `zLo`).
- **`kSTS`** (`shiftTarget`, `[af 18, af 10, af 22, f]`): template `stSegT` = 512 `pad` bit locals with
  forcing rows `bit·bit = bit` and `one·Σ_b bitBasis b · bit_b = e` (4 halves; `W4.bitF_pk`/`bitF_pkO`
  give `bit_b = bitF e b`), the 8-coordinate eq table (254 gates, constants folded), 512 `bit·E[σ]`,
  `eq(τ, L)` (17), `(1−θ₈)(1−θ₉)` and the two final gates (787). Lemma: `eqTable_ofFn_getD` +
  `σ < 256 ⇒ bits 8, 9 clear` splits `Eθ[σ] = E₈[σ]·(1−θ₈)(1−θ₉)`; `digestMle` as the bit sum; needs
  `impl₀.shiftTarget = shiftTargetI` (`SegBase.2`, already in place).
- `rtSeg1 := … .orElse (rtKD kTSS repB cbTSS) .orElse (rtKD kSTS repB cbSTS)`; `rtC1d_ok` gains two
  `orElse_okW` arms. Extra rows ≈ 1.45 k, locals ≈ 1.35 k (SEG-R0 §1.2–1.3).

## 7. The R2 diffs (after SIB and CF2 land)

1. **`FR.lean`**: `import FRNodeRows4RepSeg`.
2. **The fold** (`FRNodeRows4.repAllRows`, `RepFit`/`repFitB`, `FRNodeRows4RepF`): every `rtC1c` →
   `rtC1d`; `repOk_rtC1cB` → `repOk_iff.2 repOkW_rtC1dB`; `repFold`, `gap4Imp_rtC1c`, `gaps4_of_runA`,
   SIB's `gaps4_of_runS`/`gap4Imp_of_bitsS` (`FRNodeRun4BT`) at `rtC1d`. The prototype-0 arm of `rtC1d`
   is literally `rtN0c`, so every prototype-0 lemma is unchanged.
3. **Constants**: `arR2N` 180,560 → **154,368** (with SIB; SEG-R0 §2); `repSegB := arRb + arNb`
   (symbolic; 988,672 with SIB); `repConsts`, `repRow0_ctl`, `slotA_idx` per SEG-R0 §7's table.
4. **`repRow0`** for `protoOf κ v = 1`: row `k` of the slot's replay rows at
   `k < |B| → v·2^20 + repSegB + k`, else `v·2^20 + 688,128 + (k − |B|)`, `|B| = slotM4 − linkN − repSegB`
   (27,136 with SIB); band A `[688,128, 720,896)` = 32,768 ≥ 37,362 − 27,136 + margin; new init check
   `protoRows 1 < 688,128` (prototype 1 ends at 686,079). `repIRowsW` must then map row indices by this
   two-band function instead of `repRow0 + p.2`.
5. **`repMapC`** for `protoOf κ v = 1` and `c ≥ repB`: `j := c − cbRSS` (`cbRSS = repB + 2^12`; the 37,130
   locals are `[cbRSS, cbRSS + 37,130)`) ↦ `κ.oneCell + v·2^20 + (j < 35,648 ? 405,504 + j : 1,003,010 +
   (j − 35,648))` (cell bands 1 and 3; band 2 `[277,402, 290,816)` stays free for `kSTS`/`kTSS`, ≈ 1.35 k).
   `repCellOk 1` allows those ranges; `repFitB 1`: rows ≤ 59,904 (A + B), locals < 48,366 (bands 1 + 3).
6. **`repV4`**: segment slots share one `rv₁` (prototype 1's template value, REPF's `repV0_eq` pattern);
   V ≈ +55–75 ms VM sparse (SEG-R §4.4), a few ms after CF's `Rep` closed forms (chain groups: 65 × 127,
   stage group 384 × 222 → pad 256).
7. **`FRNodeRows4Model.segRegion`**: 49,000 → the measured 37,362 rows (+ ≈ 1.45 k after §6).

## 8. Prover cells (E1)

Per segment slot (prototype 1): the six dead cells `r57244..46`, `r57251..53` = **0**; mux locals
`m_{p,ι} = sel_ι · f_ι(p)` (the selected kind's form value, 0 at the others), 207 cells; template locals
by honest gate evaluation of `rsSegT` (the hints from `kdIn` at plan time) on the canonical inputs, 36,923
cells, at `repMapC`'s cells; the zero rows hold already (each kind's claim `f₁` cell is the prototype's
`mulKF (const K 1) x` output, i.e. 0); copy rows: the import cell `r93083` = template output.

## 9. Files

New: `FRNodeRows4RepSegK.lean`, `FRVIRTplSegR.lean`, `FRNodeRows4RepSeg.lean`. Edited: `FRVerifierImplCore`,
`FRSegTarget4`, `FRSubmission4V`, `FRSubmission4Cert`, `FRNodeRsvLink`. Probes `logs/SEGR1/probe/`
(`SegKat.lean`, `AxSEGR1.lean`, `snap1.sh`); binaries `logs/SEGR1/binA|binB`.

## 10. Open questions

1. Should an `rsWeight` with some `act` true at prototype 1 be rejected rather than left an import? It
   cannot occur in `protoProg 1`; an op-aware `inOk` (`KOpD.inOk : Op → List Ty → Bool`) would do it.
2. The orchestrator must add `import FRNodeRows4RepSeg` to `FR.lean` (not my file).
3. SIB's working-tree `FRNodeRun4BT.lean` names `Sub4.implB` only in theorems — unaffected by the
   `noncomputable`; any compiled use elsewhere must use `Impl.implC0`.
