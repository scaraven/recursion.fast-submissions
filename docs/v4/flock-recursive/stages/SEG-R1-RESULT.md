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
| 2b. `shiftTarget` (787 gates + 512 bit locals), `targetS` (53 gates) templates | not done in SEG-R1 (§6 has the plan); **done in SEG-R1b** (§ SEG-R1b below): neither is an import of prototype 1 at `rtC1d 1` any more. |
| 3. `kRSS.cov`/`inOk` | **done** (act all false, 3 claims, `[af 7, f, f, ak m ×4]`, `23 ≤ m ≤ 25`) |
| 4. `evalM`/`evalL` pinned to zero in `implSeg`, zero rows | **done** (`rtEvZ`, `rtEvZ_okW`, no hypothesis) |
| 5. init win | **done**: start-up **−2.0 s** user (median 21.6 → 19.6 s), segment check **−70 ms** |
| assembly | `rtSeg1 = linkWAll ∪ evalM/evalL ∪ rsWeight`; `rtC1d`, `rtC1d_ok`, `repOkW_rtC1d`, `repOkW_rtC1dB` (at `Sub4.implB`) |

`lake build FR Solution FRSubmission4Fin FRNodeRows4RepSeg start0` green (`build-final.out`, 5,237 jobs).
Axioms: only `propext`, `Classical.choice`, `Quot.sound` (`axioms.log`, 15 declarations incl.
`Challenge.certified`). Source rule: 467 files, 0 findings (`source-rule.log`). No `sorry`.

`FR.lean` imports `FRNodeRows4RepSeg` since `9a3019d` (the orchestrator's addition at commit; it pulls
`FRNodeRows4RepSegK`, `FRVIRTplSegR` and, after SEG-R1b, `FRNodeRows4RepSegT`, `FRVIRTplSegT`).

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

## 7. The R2 diffs (after SIB and CF2 land; updated by SEG-R1b and the SIB/SEG-R1 review)

1. **`FR.lean`**: done (`9a3019d` imports `FRNodeRows4RepSeg`).
2. **The fold** (`FRNodeRows4.repAllRows`, `RepFit`/`repFitB`, `FRNodeRows4RepF`): every `rtC1c` →
   `rtC1d`; `repOk_rtC1cB` → `repOk_iff.2 repOkW_rtC1dB`; `repFold`, `gap4Imp_rtC1c`, `gaps4_of_runA` at
   `rtC1d`; and SIB's closure route: **`gap4Imp_of_close` / `gap4Imp_rtC1cC` / `gaps4_of_runC`**
   (`FRNodeRun4CT.lean`, l. 72/144/157 at `9a3019d`), i.e. `SlotRunC`'s `rt` argument `rtC1c` → `rtC1d`.
   (`gaps4_of_runS` and its siblings no longer exist: SIB removed them.) The prototype-0 arm of `rtC1d` is
   literally `rtN0c`, so every prototype-0 lemma is unchanged.
3. **Constants**: `arR2N` 180,560 → **154,368** (with SIB; SEG-R0 §2); `repSegB := arRb + arNb`
   (symbolic; 988,672 with SIB); `repConsts`, `repRow0_ctl`, `slotA_idx` per SEG-R0 §7's table.
4. **`repRow0`** for `protoOf κ v = 1`: row `k` of the slot's replay rows at
   `k < |B| → v·2^20 + repSegB + k`, else `v·2^20 + 688,128 + (k − |B|)`, `|B| = slotM4 − linkN − repSegB`
   (27,136 with SIB); band A `[688,128, 720,896)` = 32,768 ≥ **38,805** − 27,136 = 11,669 (SEG-R1b's
   measured total, `logs/SEGR1b/segkat.log`); new init check `protoRows 1 < 688,128` (prototype 1 ends at
   686,079). `repIRowsW` must then map row indices by this two-band function instead of `repRow0 + p.2`.
5. **`repMapC`** for `protoOf κ v = 1` and `c ≥ repB`, two pieces:
   - `c < cbRSS` (`[repB, repB + 2^12)`: `kTSS`'s locals from `cbTSS = repB`, 55 used; `kSTS`'s from
     `cbSTS = repB + 2^9`, 1,301 used; highest used offset 1,812) ↦ `κ.oneCell + v·2^20 + 277,402 +
     (c − repB)`: **cell band 2** `[277,402, 290,816)`, 4,096 ≤ 13,414 reserved, 1,813 touched;
   - `c ≥ cbRSS`: `j := c − cbRSS` (`cbRSS = repB + 2^12`; the 37,130 locals are `[cbRSS, cbRSS + 37,130)`)
     ↦ `κ.oneCell + v·2^20 + (j < 35,648 ? 405,504 + j : 1,003,010 + (j − 35,648))` (cell bands 1 and 3).
   `repCellOk 1` allows those ranges; `repFitB 1`: rows ≤ 59,904 (A + B), locals `< 2^12` below `cbRSS`
   (band 2) and `< 48,366` from `cbRSS` (bands 1 + 3).
6. **`repV4`**: segment slots share one `rv₁` (prototype 1's template value, REPF's `repV0_eq` pattern);
   V ≈ +55–75 ms VM sparse (SEG-R §4.4), a few ms after CF's `Rep` closed forms (chain groups: 65 × 127,
   stage group 384 × 222 → pad 256). SEG-R1b adds 1,443 rows (≈ 4.3 k terms), negligible.
7. **`FRNodeRows4Model.segRegion`**: 49,000 → the measured **38,805** rows (`repRowsP rtSeg1 1`: linkWAll 8,
   evalM/evalL 6, rsWeight 37,348, targetS 137, shiftTarget 1,306).
8. **Uncovered replay ops must fail in the circuit**, not be shown absent by kernel evaluation: R2 should add
   a closure-style failing row (`failRT`) for an `isRep` op that `(rtC1d π).cov` does not cover (e.g. `rt.cov`
   passed into `askTG`, or an op-aware `inOk`), so that `impQP (rtC1d π) … π = []` follows structurally, as
   `impB_sub` does for the closure. Do **not** discharge it by `decide`/`rfl` over `impQP`, which would make
   the kernel evaluate the whole compile of `protoProg π` (review should-fix 2). On the real `protoProg 1`
   the probe already finds no uncovered replay op under `rtSeg1` (§ SEG-R1b), so the failing row costs no
   honest completeness.

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

## SEG-R1b

Stage SEG-R1b, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Base: HEAD `9db5ee0`
(SIB `648720f` + SEG-R1 `9a3019d` + review `b63754e` + CF2 `9db5ee0`; the tree re-snapshotted as each landed).
Build tree `logs/fr-build-SEGR1b` (a copy of `fr-build-SEGR1`; `snap1.sh`: HEAD files by `git show`, MINE
symlinked, every other non-HEAD module removed, so SEG-R2's working files are not in the tree). Logs
`logs/SEGR1b/`. Nothing committed, no agents spawned; every lake/lean/prover command under `systemd-run
--user --scope -p MemoryMax=16G -p MemorySwapMax=0 -- timeout …`.

### R1b.0 Verdict

| item | status |
|---|---|
| `tsSegT` (`targetS`) + `ok_tsSegT` | **done**: 55 gates, 18 forcing rows `L_l · L_l = L_l`; outputs = `targetSSegI r` |
| `stSegT` (`shiftTarget`) + `ok_stSegT` | **done**: 789 gates, 512 bit locals (`pad`), 516 forcing rows; output = `shiftTargetI κs τ θ bnd` |
| `kTSS`, `kSTS`, `kTSS_ok`, `kSTS_ok` | **done** (`kTSS_ok` has no hypothesis; `kSTS_ok` needs `SegBase.2`) |
| `rtSeg1` = linkWAll ∪ evalM/evalL ∪ rsWeight ∪ targetS ∪ shiftTarget; `rtC1d_ok`, `repOkW_rtC1d`, `repOkW_rtC1dB` | **done**: two more `orElse_okW` arms; statements unchanged |
| controls (kernel), KATs | **done** (R1b.3) |
| on `protoProg 1`: rows of `repRowsP rtSeg1 1` | **38,805**, **0 rejecting**; residual replay-op imports under `rtC1d 1`: **none** (was targetS, shiftTarget, rsWeight, evalM, evalL under `rtC1c 1`) |
| honest ACCEPT after the `evalM`/`evalL` pin (review should-fix 1) | segments **accepted** at L30, L31, L32 (canaries rejected); nodes: E1's saved node proofs are **rejected**, as they already were before the pin (RUN1); see R1b.5 |

`lake build FR Solution FRSubmission4Fin FRNodeRows4RepSeg segkat e1verify` green at `9db5ee0` + SEG-R1b
(`logs/SEGR1b/build-final.log`, 5,110 jobs). Axioms: only `propext`, `Classical.choice`, `Quot.sound`
(`logs/SEGR1b/axioms.log`, 19 declarations incl. `Challenge.certified`; `kTSS_cov`/`kSTS_cov` use `propext`
only, `lay_ctl` none). Source rule: 480 files, 0 findings (`logs/SEGR1b/source-rule.log`; the count
includes SEG-R2's working files). No `sorry`.

### R1b.1 Files

| file | lines (loc.py: code) | content |
|---|---|---|
| `FRVIRTplSegT.lean` (new) | 437 (331) | `leaf_affine`, `rangeG`/`ok_rangeG`/`range_step`, `prefixP_succ`, `sum_bits_rgVal`, `tsSegT`/`ok_tsSegT`; `bitsG`, `packL`, `digRows`, `bits_of_pack`, `bits_dig`, `ok_digRows`, `eqAtR_ten`, `digest_eq`, `mulAddF`, `stSegT`/`ok_stSegT` |
| `FRNodeRows4RepSegT.lean` (new) | 170 (111) | `kTSS`/`tssIn`/`tssLay`/`kTSS_ok`; `kSTS`/`stArgs`/`stsIn`/`stsLay`/`kSTS_ok`; controls |
| `FRNodeRows4RepSeg.lean` (SEG-R1's) | 375 (280) | `import FRNodeRows4RepSegT`; `cbTSS := repB`, `cbSTS := repB + 2^9`; `rtSeg1` extended; `rtC1d_ok`'s two new arms |

No other module touched. Probes: `logs/SEGR1b/probe/SegKat.lean` (SEG-R1's, extended), `AxSEGR1b.lean`,
`E1Verify.lean` (E1's, unchanged); `logs/SEGR1b/acc/prove.sh`, `verify.sh`.

### R1b.2 The templates

- **`tsSegT`** (canonical inputs = `r`'s 37 entries; `zf = []`; hints ignored). `targetSLeafI r` reads `r`
  only through `r₀` (`leafI_eq`), and each eq-table entry over `zLo [x]` is a constant times `x` or `1 − x`
  (`eqZ_getD`, `eqTable_ofFn_getD` + `Fin.prod_univ_castSucc`), so **`leaf_affine`**: entry `σ` is
  `α_σ + r₀(β_σ − α_σ)` with `α = targetSLeafI #[0]`, `β = targetSLeafI #[1]` (template constants `tsA0`,
  `tsA1`, two 64-entry arrays computed at process start). The range factor: `rangeG` over the pairs
  `(L_l, r_blk,l)` (low first; 3 gates a pair: `P ← (1 + b + x)P′`, `q ← b(1 + x)`, `t ← qP′`, `Q ← Q′ + t`)
  computes `(prodAt e L, prefixP 18 e L)` on Boolean bits (`ok_rangeG` via `range_step`: `prodAt`'s and
  `prefixP`'s low-bit steps; characteristic two makes `eq(b, x) = 1 + b + x` and `1 − x = 1 + x`), and
  `segRangeI r = prefixP 18 e (L + 1) = prefixP 18 e L + prodAt e L` (**`prefixP_succ`**), `L = lastAt r 19 =
  rgVal …` (`sum_bits_rgVal`). Then one gate `r₀ · R`; outputs `α_σ R + (β_σ − α_σ)(r₀R)`.
  **`ok_tsSegT`**: wherever the gate equations and the 18 forcing rows hold, the outputs are
  `(targetSSegI r).toList`. 54 + 1 = **55 gates** (SEG-R0 counted 53: the top pair's `P′ = 1` product and the
  bottom's are not special-cased; simplest sound form).
- **`stSegT`** (canonical inputs `τ` 0–17, `θ` 18–27, `bnd` 28–49, `κs` 50; hints ignored). Two `bitsG 256`
  (`pad` locals, no gate equation) for `h` and `s`; forcing rows `digRows`: `bit·bit = bit` (256 each) and
  `one · Σ_{b<128} E_b bit_b = half` (2 each). **`ok_digRows`** (from `W4.bitF_sumO`): the locals are
  `digBit`'s bits of the halves. Eq table over `θ₀ … θ₇` (`eqTblG`, 255 gates); digest sums `Σ_σ bit_σ E[σ]`
  (2 × 256 gates); `eq(τ, L)` by a fold of 18 products of `1 + τ_l + L_l` (`eq_lin`); `(1 − θ₈)(1 − θ₉)`;
  `eL · dh`, `κs · ds + ·` (`mulAddF`), times the factor. **`digest_eq`**: `digestMle Eθ h0 h1 = (Σ_σ bit_σ
  E₈[σ]) (1 − θ₈)(1 − θ₉)` (`eqAtR_ten`: bits 8, 9 of `σ < 256` are clear). **`ok_stSegT`**: output
  `= shiftTargetI κs τ θ bnd`. **789 gates** (SEG-R0: 787), **1,301 locals**, 516 forcing rows.
- **`kTSS`** = `⟨isTS, tsArgs, tssIn, 37, tssLay, [], tsSegT, [.af 64]⟩`, `tssIn` = exactly `[af 37]`.
  **`kTSS_ok`**: `KOkD (implP impl₀ base 1 ι) ι kTSS`, no hypothesis (`implP … 1`'s `targetS` at a leaf kind
  is `targetSSegI`).
- **`kSTS`** = `⟨isST, stArgs, stsIn, 51, stsLay, [], stSegT, [.f]⟩`, `stsIn` = exactly
  `[af 18, af 10, af 22, f]`. **`kSTS_ok`** under `impl₀.shiftTarget = shiftTargetI` (`SegBase.2`, `rfl` at
  `Sub4.implB`).
- **Cells**: `cbTSS = repB` (mux, then 55 locals; ≤ 3·37 + 55 = 166 < 2^9 even if every position were muxed),
  `cbSTS = repB + 2^9` (≤ 3·51 + 1,301 = 1,454 < 2^12 − 2^9). Both lie in `[repB, cbRSS)`, disjoint from
  `rsSegT`'s `[cbRSS, cbRSS + 37,130)`; R2 maps that block to cell band 2 (§7.5). On `protoProg 1` no
  position is muxed (the forms are kind-free, as SEG-R0 found), highest used offset 1,812.

### R1b.3 Controls and KATs

Kernel (`FRNodeRows4RepSegT`): `kTSS_cov`, `kSTS_cov` (+ covered / − the other op); `tssIn_ctl`
(+ `af 37`; − `af 36`, two operands); `stsIn_ctl` (+ the segment's; − a `bnd` of width 4, `τ` of 16, `κs : K`);
`lay_ctl` (+ last entry read; − nothing past it); **`tsRow_neg`** (a non-Boolean `L` entry fails its forcing
row); **`pack_neg`** (a flipped digest bit fails the pack row: Boolean packs of one half are unique). The
positive semantic controls are `ok_tsSegT`/`ok_stSegT` themselves.

KATs (`logs/SEGR1b/segkat.log`, honest gate evaluation of the Lean templates; the bit `pad` locals filled
with the true digest bits):

| template | case | outputs = op value | all rows hold | (−) perturbed local | (−) other |
|---|---|---|---|---|---|
| `tsSegT` | L32 (18 L bits), P30, N30 (16) | `targetSSegI r`: true ×3 | true ×3 | fails ×3 | non-Boolean `L` entry fails a forcing row ×3; flipped `L` bit moves `targetSSegI` and the template follows ×3 |
| `stSegT` | 3 random instances | `shiftTargetI`: true ×3 | true ×3 | fails ×3 | flipped digest bit fails a forcing row ×3; non-Boolean bit fails ×3 |
| `rsSegT` | L32/P30/N30 (SEG-R1's, re-run) | true | true | fails | `f₁ ≠ 0` moves `rsWeightF` |

**On the real program** (`repRowsP rtSeg1 1`): **38,805 rows, 0 rejecting**; per op: targetS 137
(55 gate + 18 forcing + 64 copy), shiftTarget 1,306 (789 + 516 + 1), linkWAll 8, evalM 3, evalL 3, rsWeight
37,348. **Locals per segment slot**: 37,130 (rsWeight, from `cbRSS`) + 55 (targetS) + 1,301 (shiftTarget)
= **38,486**; the two new ones in `[repB, repB + 1,813)`. **Uncovered import ops of prototype 1**, replay
ops only: under `rtC1c 1` targetS 1, shiftTarget 1, evalM 1, evalL 1, rsWeight 1; **under `rtC1d 1`: none**
(the remaining uncovered imports are asks, `bitOf`, `chF`/`chK`, `askCol`/`askNode` and others that
SIB's closure classes handle, `logs/SEGR1b/segkat.log`).

### R1b.4 Kernel and build cost

`lake env lean -Dprofiler=true` per module (core 28, `logs/SEGR1b/prof-*.log`):

| module | type checking (kernel) | elaboration | user, whole file |
|---|---|---|---|
| `FRVIRTplSegT` | 2.76 s (1.96 s in a second run; no declaration ≥ 0.25 s) | 5.7 s | 16.3 s |
| `FRNodeRows4RepSegT` | 0.60 s | 0.35 s | 6.1 s |
| `FRNodeRows4RepSeg` (whole module, SEG-R1's kRSS included) | 2.82 s | 1.24 s | 10.6 s |

None of it is on the certificate path at `9db5ee0` (only `FR.lean` imports `FRNodeRows4RepSeg`; `Solution`
does not). Once R2 folds `rtC1d` into the certificate's closure, expect ≈ +3.4 s kernel from the two new
modules (plus RepSeg's share). Init: `tsA0`/`tsA1` are two `targetSLeafI` evaluations (64 × 256 products)
at process start, well under 1 ms of work; the templates are built only when `rtSeg1`'s rows are.

### R1b.5 Honest acceptance after the `evalM`/`evalL` pin (review should-fix 1)

`e1verify` (E1's probe, unchanged: the badge's `parseSigned` + `accF` with `V := Sub4.V4F`, `qV = 36,000`)
built in this tree at `9db5ee0` + SEG-R1b, run on honest signed files and on the flipped-statement canary
(`logs/SEGR1b/acc/verify-final.log`; the same at `9a3019d`+SIB in `verify.log`):

| file | kind | Lean V | canary |
|---|---|---|---|
| `acc/agg-3.bin` (new: E1's prover, `prove-agg 3`) | aggregate, segs `[L30:3]` | **accept** (143 ms) | reject |
| `acc/agg-100000.bin` (new, `prove-agg 100000`) | aggregate, segs `[L31:100000]` | **accept** (155 ms) | reject |
| `E1/r1/agg2.bin` | aggregate, segs `[L32:262144, L32:137857]` | **accept** (310 ms) | reject |
| `E1/r4/*.signed` (10 files) | nodes N2 ×3, N4 ×5, N8 ×2 | **reject** | reject |

- The pin is on the **segment** path only: `VsegF = runStmt implS (progSK κ)`, `implS = implSeg Impl.implC0`;
  the three segment kinds (`SegKind` = L30/L31/L32; the `Kind` indices L32/P30/N30 are the transcript kinds
  the replay muxes) are all accepted with the pin in place, canaries rejected. The new aggregates come from
  E1's prover binary (`logs/E1/target/release/flock-prover`, E1's IR dump) through a fresh `rf-oracle`
  (`acc/prove.sh`, `acc/agg-*.log`: native `acc` and the dumped program accept too).
- **Nodes**: `VnodeF = runStmt (implNK κ) (progNK κ)` does not read `implSeg`, so the pin cannot change a node
  verdict. E1's node proofs (`7537acd`) are rejected at HEAD because the node circuit changed after E1 (IMP's
  statement rows, ASK-T, REPF, FOLD2, SIB, CF2); RUN1-RESULT §1 already records that E1's proofs are rejected
  at `200b531`, before the pin. An honest node ACCEPT at HEAD needs E1's re-dump, blob rebuild and re-prove
  (a prover-side stage); **not done here** (too heavy for this stage's tree and scope).

### R1b.6 Deviations

1. Gate counts 55 (`tsSegT`) and 789 (`stSegT`) against SEG-R0's 53 and 787: the generic recursions do not
   special-case a factor `1` (`rangeG`'s base `P = 1`; the `eq(τ, L)` fold starts from `C 1`). +4 rows, simpler
   proofs.
2. The templates ignore the constant hints (`cst`); sound (a hint only says an input equals a constant), and
   on `protoProg 1` no `targetS`/`shiftTarget` input is folded anywhere in SEG-R0's counts.
3. Helper names `eqF`, `bval`, `bitRows` clashed with CF2's `FRVIRTplRepLG.eqF` and others after `9db5ee0`;
   renamed `rgEqF`, `rgVal`, `digRows`.

### R1b.7 Open questions / for the orchestrator

1. Commit `FRVIRTplSegT.lean`, `FRNodeRows4RepSegT.lean` (new) and `FRNodeRows4RepSeg.lean`; `FR.lean`
   already imports `FRNodeRows4RepSeg`. SEG-R2 (journal) plans to move `kTSS`/`kSTS` (and `rtSeg1`, `rtC1d`)
   into an upstream `FRNodeRows4SegD`; its overlay must take these names (`cbTSS`, `cbSTS`, `tsSegT`,
   `stSegT`, `rgEqF`, `digRows`, …).
2. Node honest ACCEPT at HEAD needs a prover re-dump (R1b.5); RUN1 has the same open item.
3. The E1 prover still produces segment proofs that HEAD accepts, so the pin does not change honest segment
   proofs.

