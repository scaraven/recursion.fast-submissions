# S-E12f (track L-circ): RESULT. INT-9's F1: kind-muxed `tensorW`/`eqPt` templates, no `gen4` padding

Stage S-E12f, 2026-10-29. Base HEAD `faa2f4b` (INT-9). Build tree `logs/fr-build-SE12f` (a copy of
`fr-build-INT9`, against `logs/org20`). Logs are in `logs/S-E12f/`; the journal is
`S-E12f-JOURNAL.md`. Every lean, lake, probe and python command ran in a 16 GB scope with a timeout.
Nothing is committed. No program (`gen4`, `FRVIR4*`), `FRVerifierImplNode4*`, `FRSoundness*`, `FRX*`
or `prover/` file was edited. (Other agents' files changed in the worktree during the stage —
`claim.json`, `FRSubmission4*.lean`, `Solution.lean`, `probe/p2t10/`, `prover/` — are not mine.)

## Status

| Item | State |
|---|---|
| 1. Routed per-kind `tensorW` template | **Done**, as `TKey.tensorWK [n_L, n_P, n_N]`, `tplTensorWK`, `tplTensorWK_ok`; one sub-template per kind and a selector mux. The kind's constants (the point's length per kind) are in the key; the per-kind operand comes from **per-kind slots** in the compile state (deviation 1). The `impl` requirement is `ImplTF`'s `tensorW` field, which `implTF_implN4F` (unchanged, re-checked) and `implTF_keys41` (segment) already give. |
| 2. The same for `eqPt` | **Done**: `TKey.eqPtK [(n, m)_κ]`, `tplEqPtK`, `tplEqPtK_ok` (no `impl` field). |
| 3. Keys, hint, plan check, dump | **Done.** `keys41` keeps both keys (it drops only 3.x's `shiftMask`). Hint regenerated; `plan4t check`: 108 keys, `inR true`, `evalMT4` = sparse sum for N2/N4/N8. **Imports back to S-E12e's level: 26,638 / 26,655** (INT-9: 27,386 / 27,401; S-E12e: 26,639 / 26,656). Plan start 1.87–1.91 s (5 runs; ≤ 2 s, margin thin: see §4). Dump, protos and plan form in `logs/S-E12f/nodedump/`, KAT PASS. |
| 4. V(N4) with `implN4F` | **Done.** Best 184.3 / 189.4 ms (INT-9: 177.6 / 179.0); interleaved with INT-9's binary 185.2 / 183.9 against 179.9 / 176.3 ms (+5–8 ms, all in `evalM`). |

## 1. Why a route alone could not bind these ops (diagnosis)

From `logs/INT-9/nodedump/proto-p{0,1}.txt`:

- The 745 `tensorW` are `tensorW j r` with `r` one of four registers (290/178/145/132 uses). Each
  `r` is a `keep` chain over the kinds' `packK` points of **different lengths**, e.g.
  `r93828 = keep {L} r93632 (keep {N} r93744 r93686)` (10/8/9 `K`s). `opOut`'s `keep` on two
  different types is `skip 1` (untracked), so `tensorW` saw no operand and became an import.
  `j` is an `idx` with kind-dependent widths (12/10/11 etc.), but `tensorW` reads `j` as 20 aux bits
  whatever its width (`AuxK.bits logNMax`): the width does not block the template and needs no
  key entry.
- The two `eqPt` read `packFK`s whose kinds' lists differ in length (17/16/17, 23/22/23).
- A slot is kind-free (`Option (Ty × List Lin)`), so it cannot represent a value whose type depends
  on the kind; and a route is static, so `RouteOk R impl κ` cannot state "at kind `κ`, register `r`
  holds the kind's source register's value" (a fact about the run). The fix therefore extends the
  compile state, and the route stays as S-E12e left it.

## 2. What was built

| Module | New | Code lines (`loc.py`, HEAD → now) | Theorems | Change |
|---|---|---|---|---|
| `FRVIRCompile` | edit | 885 → 897 | 61 | `Out.kin` (per-kind slots of the first result), `CS.kslots`, `CS.slotK`; `CS.add`/`CS.init` carry them; `opOut_kin` |
| `FRVIRCompileSound` | edit | 281 → 496 | 31 | `ExtOkK`, `ExtOkAt.toK`, `Ext.orElse`, `ExtOkK.orElse`, `KsOk`, `InvK`, `invK_add`, `compileFromX_soundK`, **`compileX_soundK`** |
| `FRVIRTplCore` | edit | 210 → 212 | 23 | `TKey.tensorWK ns`, `TKey.eqPtK ps` |
| `FRVIRTplKMux` | **yes** | 0 → 221 | 19 | input substitution (`subW`, `Gate.sub`, `pullE`, `eqns_sub`), the mux `kmuxT`/`kmuxT_ok`, `tplTensorWK(_ok)`, `tplEqPtK(_ok)`, controls |
| `FRVIRTplExt` | edit | 442 → 447 | 21 | `tplOf` cases, `twkLocs`, `cregion` case |
| `FRVIRTplBuild` | edit | 1087 → 1088 | 79 | `keyInfo`'s `tensorWK` case (`keyInfo_eq` unchanged) |
| `FRVIRTplSet` | edit | 255 → 484 | 34 | `tplExtKM` (the kind-mux extension) and `tplExtKM_okK`; S-E12e's extension renamed `tplExt4S`; `tplExt4 := tplExt4S.orElse (route ? tplExtKM)`; `tplExt4_okK`; `compileTF4_soundAt` (statement unchanged) via `compileX_soundK`; controls |
| `FRNodeRows4Hint` | regenerated | 28 → 36 | 0 | the new layouts |

`FRVIRTplBuild` was already over 1,000 code lines at HEAD (1,087); this stage adds one.

### The mechanism

- **Per-kind slots** (`FRVIRCompile`). An extension may set `Out.kin := some f`: at kind `κ` the
  op's first result is represented by the slot `f κ` (its kind-free slot is then `none`). `CS.add`
  records `(register, f)` in `CS.kslots`; **`CS.slotK i κ`** is register `i`'s per-kind slot, else its
  slot. `opOut` and every 3.x extension leave `kin = none` (`opOut_kin`, `tplExt_kin`,
  `tplExt4S_kin`), so 3.x compiles have no per-kind slots.
- **Soundness with per-kind slots** (`FRVIRCompileSound`).
  - `InvK w cs regs κ := Inv w cs regs ∧ KsOk cs ∧ ∀ i, RepS w (cs.slotK i κ) (rd regs i)`.
  - `ExtOkK impl tc X κ` is `ExtOkAt` with the per-kind slots among the hypotheses and, among the
    conclusions, that a set `kin` represents the result at `κ`.
  - `compileFromX_soundK` is S-E12e's induction over `InvK` (`invK_add` is the step);
    `compileX_soundK` has `compileX_soundAt`'s statement with `ExtOkK` for `ExtOkAt`.
  - `ExtOkAt.toK` lifts an extension that sets no `kin`; `ExtOkK.orElse` composes two.
- **The kind-mux extension** `tplExtKM F tc` (`FRVIRTplSet`):
  - `keep act n o` that `opOut` leaves untracked: `kin κ = slotK (if act κ then n else o) κ`
    (`keepK`), so chains resolve;
  - `packFK xs` with lists of unequal lengths: `kin κ = af |xs κ|` of the kind's list (`packFKK`);
  - `tensorW j r` where `slotK r κ` is an `ak n_κ` at every kind: key `.tensorWK [n_L, n_P, n_N]`,
    inputs the three kinds' forms, `j`'s 20 aux bit cells (as 3.x's `tensorW`), the selector forms;
  - `eqPt a b` with per-kind `af` operands: key `.eqPtK [(n_κ, m_κ)]`.

  Each kind's forms are checked to have their type's length, so the template's input blocks have
  fixed offsets whatever the unselected kinds' forms are.
- **`tplExt4 F R`** tries S-E12e's `tplExt4S` first, then `tplExtKM` when the route is not `.imp`
  (`ShR.kmux`). So `tplExt4_imp` (`tplExt4 F .imp = tplExtF F`) and `compileTF4_imp` keep their
  statements, and 3.x stays `rfl`-equal (`compMS = compMSX tplExt`, `compileT`/`compileTF` as
  `compileX`, `protoCS π = compileTF4 keys41 (protoR π) …`: all checked by `rfl` in
  `ax/AxE12f.lean`).
- **The templates** (`FRVIRTplKMux`). `kmuxT σ so nout ts`: sub-template `j` is `ts[j]` with input
  `i` replaced by the form `σ j i` and its locals after the previous ones; then per output `c` the
  products `sel_j · out_{j,c}`, and output `c` is their sum (`tplMaskN`'s mux). `σ j` reads the
  kind's block and the shared tail, and is `[]` beyond them, so the original templates' total
  `InpIs` holds at the pulled-back wires (`pullE`) and `tplTensorW_ok`/`tplEqPt_ok` are reused as
  they are. **`kmuxT_ok`**: with the selectors one-hot at `j₀`, sub-template `j₀`'s equations hold at
  its wires and the outputs are its outputs. `tplTensorWK_ok`/`tplEqPtK_ok` instantiate it.

### Statements

- `compileTF4_soundAt` and `protoCS_soundAt` keep their statements (re-proved through
  `compileX_soundK`). Their hypotheses are as before: `ImplTF F impl`, `RouteOk R impl κ`, and the
  compiled rows/instances/aux/imports. The `tensorWK` key adds to `ImplTF` only the existing
  `tensorW = tensorWI` field.
- S-E12e's `tplExt4_okAt` is now **`tplExt4S_okAt`**, the same statement about the same function
  under its new name. The new `tplExt4` is not `ExtOkAt`-sound (its kind-mux needs the per-kind
  slots), and its soundness is `tplExt4_okK`.

## 3. Hint, plan, dump (`logs/S-E12f/`)

- **Hint** (`laydump4.log`, 17.9 s): prototype 0 gains `tensorWK [19,18,19] / [16,15,16] /
  [13,12,13] / [10,9,10]` (290/178/145/132 instances) and `eqPtK [(17,17),(16,16),(17,17)]`,
  `[(23,23),(22,22),(23,23)]`, and `[(26,26),(25,25),(26,26)]`. Prototype 1 gains `tensorWK [19,17,18] /
  [16,14,15] / [13,11,12] / [10,8,9]` and `eqPtK [(26,26),(24,24),(25,25)]`. The `[(26,26),…]` `eqPt` was an import
  in S-E12e too, which accounts for the one import below S-E12e's count.
- **Plan check** (`plan4t-check.log`): 108 keys (96), pieces 6,406 + 6,408 (instances 5,396 +
  5,396), `inR true`; `evalMT4` equals the sparse sum for N2, N4 and N8. Best N2 115.2 ms, N4 85.4 ms,
  N8 63.4 ms. The sparse reference ran 12 min, with N2's best affected by load.
- **Plan start** (`plan4t-init-{1..5}.log`, core 29, load ≈ 2): 1.91, 1.91, 1.87, 1.87, 1.90 s.
  Interleaved with INT-9's binary on the same core (`plan4t-ab.log`): S-E12f 1.91, 2.08, 1.94,
  1.91 s; INT-9 1.75, 1.77, 1.71, 1.72 s. That is +0.15–0.3 s. It is within 2 s except one run.
  Stage times (`planstage-{1,2}.log`, new probe `PlanStage`): `mkKM` 137–143 ms, compiles 253 + 215–287 ms,
  `slotRP` 425–440 ms, grouping 189–198 ms, pieces 118–120 ms.
- **Node dump** (`nodedump4-run.log`, 40 s; `protodump`, `planform4`), see the README:

  | Prototype | Indexed rows | Rows in the region | Instances | Import registers | Aux | Per-kind slots |
  |---|---|---|---|---|---|---|
  | 0 | 603,404 | 730,493 | 3,033 | **26,638** | 2,498 | 14 |
  | 1 | 593,997 | 725,885 | 3,033 | **26,655** | 2,498 | 14 |

  Against INT-9, prototype 0 has −748 import registers and prototype 1 has −746. The 745 `tensorW`
  aux reads of `j`'s bits are back. The programs are unchanged: `proto-p{0,1}.txt` are byte-identical
  to INT-9's.
- **Plan form**: 969,350 / 970,966 bytes (INT-9: 869,157 / 871,735). `planform_kat.py`: 603,404 /
  593,997 rows, 0 differ, 0 non-unit products, `KAT PASS` (`planform-kat.log`).

## 4. V(N4) (S-E8's method, `vtime4 21 n4f`, core 30, load ≈ 2)

| Run | V(N4) best / median | `evalMT4` best | Log |
|---|---|---|---|
| a | 189.4 / 193.2 ms | 87.7 ms | `vtime4-n4f-a.log` |
| b | 184.3 / 189.2 ms | 86.9 ms | `vtime4-n4f-b.log` |
| A/B with INT-9 | S-E12f 185.2, 183.9; INT-9 179.9, 176.3 ms | 86.6, 92.7 against 77.6, 77.0 ms | `vtime4-ab.log` |

The cost is `evalM`'s: +12 keys, and 745 instances with three kinds' inputs. At the 1.19 ratio,
V(N4) is ≈ 155–159 ms on the 7763, against the 206 ms cap.

## For P2 (dump changes)

Full text in `logs/S-E12f/nodedump/README.md` ("S-E12f changes"). In short:

- **Programs and register numbering are unchanged.** The kind-muxed `keep`/`packFK` registers stay
  `untracked` in `mregs`. Their per-kind forms are in the new `mkslots-p{π}.txt`.
- **New keys `tensorWK [n_L,n_P,n_N]` and `eqPtK [(n,m)_κ]`.**
  - Inputs: the three kinds' operand blocks (selector order `L32 P30 N30`), then for `tensorWK`
    `j`'s 20 bit cells (aux `bits 20`, at `cb + 5·Σn + 6 + i`), then the 3 selector forms. They are
    listed per instance in `mtinsk-p{π}.txt`.
  - Gate order: sub-template `L32`, `P30`, `N30`, each the existing `tensorW`/`eqPt` template on its
    kind's block, locals one after the other. Then per output component `c` the 3 products
    `sel_j·out_{j,c}` (locals `K + 3c + j`).
  - **Every sub-template's locals are filled, whichever kind is selected.**
- **Rows:** +174,589 (p0) and +166,893 (p1) indexed rows against INT-9; +116,013 and +109,181
  against S-E12e. The region now ends at 730,493 / 725,885 rows of `2^20`. Each kind-muxed instance
  holds three sub-templates. `tensorWK [19,…]` is 286 rows in a 512-row stride (lever below).
- **Plan form:** 108 keys, ≈ 0.97 MB per prototype. The format is unchanged.

## Checks

- **Build:** `lake build FR FRVerifierImplNode4F FRVIRTpl4Bridge FRNodeRows4Fit FRNodeRows4Model
  FRVIRTplSet FRVIRTplKMux FRNodeRows4Plan` (plus the probes) is green: 2,530 jobs for the entry targets (`build-entry.log`), 4,888 with the probes
  (`build-final.log`), no `sorry`. The first full build at this design was also 2,530 jobs (`build-1.out`, 6 min 38 s).
  `FRVerifierImplNode4F`'s `implTF_implN4F` compiles unchanged over the two new keys.
- **Axioms** (`axioms.log`, `ax/AxE12f.lean`): 46 declarations, each within `propext`,
  `Classical.choice` and `Quot.sound`. They are:
  - the new ones;
  - `compileTF4_soundAt`, `protoCS_soundAt`, `planData4_rows`, `evalMT4_eq`;
  - INT-9's node ops (`implTF_implN4F`, `implN4F_hM`/`_hL`, `evalL4I_eq`, …);
  - 3.x's (`compileT_sound`, `tplExt_ok`, `compileX_sound`, `compileTF_sound`, `compMS_T`, …).

  The file's `rfl` examples (3.x instance, `protoProg`, `protoCS`) and the R4 composition
  `not_rejFinE4_node … (implN4F_hM …)` check.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`):
  324 files, 0 findings (`source-rule.log`; the count includes other agents' new files).
- **Sequential profiles** (`Elab.async=false`, one core, `profile-*.log`):

  | Module | Wall | Type checking | Tactics |
  |---|---|---|---|
  | `FRVIRCompile` | 31.6 s | 1.16 s | 8.57 s |
  | `FRVIRCompileSound` | 12.2 s | 0.33 s | 1.26 s |
  | `FRVIRTplKMux` | 9.0 s | 0.38 s | 0.65 s |
  | `FRVIRTplSet` | 16.3 s | 0.48 s | 1.91 s |
  | `FRVIRTplExt` | 11.3 s | 0.28 s | 1.79 s |
  | `FRNodeRows4Hint` | 6.4 s | 0.001 s | — |

  **Kernel trap, again (recorded).** The first `FRVIRTplKMux` took 30 s of type checking and
  24 s of `obtain`.
  1. `subW_ev`'s `nil` case was `rfl`. The kernel compared
     `(List.map (fun t => t.2 * t.1.ev e) []).sum` with the `pullE` version **argument first**, so
     it unfolded the two lambdas into `F`'s multiplication. Fix: rewrite both sides to `0` (`ev_nil`).
  2. `kmuxT_ok`'s `h` against `tplEqPtK`'s unfolding with the lambdas `fun q => q.1 + q.2` and
     `fun q => tplEqPt q.1 q.2` written twice cost 20 s of unification. Fix: name them (`epW`, `epT`).
  3. `simp [tplEqPt]` to count outputs was replaced by `rw [List.getElem_map]; rfl`.

  Now 0.38 s type checking and 0.65 s tactics. The dump regenerated after these proof edits is
  identical, file for file.

## Controls

| Definition | (+) | (−) |
|---|---|---|
| `CS.slotK`, `Out.kin`, `keepK`, `packFKK`, `tplExtKM`, `tplExt4` | `tplExtKM_ctl` (kernel `decide` on a compiled 4-op program): the `keep` of `ak 2`/`ak 1` has slot `ak 2` at `L32` and `ak 1` at `N30`; the `packFK` has `af 1` at `P30`; the instances are `.eqPtK [(2,2),(1,1),(1,1)]` and `.tensorWK [2,1,1]` | `tplExtKM_ctl`: under route `.imp` there are no instances and no per-kind slots, and both ops are imports (2 import registers); a `keep` on one type is left to `opOut` |
| per-kind slots needed | `keepK_ctl`: `keepK` is `ak 2` at `L32` | `keepK_ctl`: `ak 1` at `P30`, so no single slot represents the register at every kind (hence `slotK`/`ExtOkK`) |
| `ExtOkK`, `compileX_soundK` | `ExtOkAt.toK`; `compileTF4_soundAt`/`protoCS_soundAt` are re-proved through it, statements unchanged | the `.imp` half of `tplExtKM_ctl` |
| `kmuxT`, `tplTensorWK`, `tplEqPtK` | `kmuxT_ok`, `tplTensorWK_ok`, `tplEqPtK_ok`; `tplTensorWK_nlocs` (`5·Σn + 6` locals); `tplKMux_outs` (2 and 1 outputs) | measured: the dump's imports fall by 748/746 and its rows rise, so the templates act |
| the prototypes | `plan4t check`: `inR true`, `evalMT4` = sparse sum (three kinds); plan-form KAT | — |

## Deviations

1. **Per-kind slots in the compile state, not the route, supply the kind's operand.** The ruling
   asked for routed per-kind templates with the kind's constants supplied by the route
   (`RouteOk`).
   - The constants (each kind's point length) are in the key (`tensorWK ns`, `eqPtK ps`), as for
     `maskN`.
   - The operand's per-kind value cannot come from a route (§1). It comes from `CS.slotK`, which is
     sound by the new invariant `InvK`. `RouteOk` is unchanged, and the new keys need nothing kind-indexed
     of `impl`.
   - The orchestrator's ruling holds otherwise: one sub-template per kind, a selector mux, and no
     program padding.
2. **The `idx` width is not in the key.** `tensorW` reads `j` as 20 aux bits at every width, so the
   kind-dependent width (12/10/11 …) does not need templating. The kind-dependent part is the
   point's length.
3. **The core compiler's state grew two fields** (`Out.kin`, `CS.kslots`). 3.x's compiles leave
   them empty (`opOut_kin`, `tplExt_kin`), and every 3.x statement and `rfl` check is unchanged.
4. **S-E12e's `tplExt4` is renamed `tplExt4S`** (with `tplExt4S_okAt`, `tplExt4S_imp`). The name
   `tplExt4` is now the composed extension, so `compileTF4`, `protoCS` and `planData4` pick it up
   without edits.
5. **A bonus key:** the `eqPt` on `[(26,26),(25,25),(26,26)]` (prototype 0) and
   `[(26,26),(24,24),(25,25)]` (prototype 1) was an import already in S-E12e. The kind mux templates
   it too.

## Open questions and levers

1. **Plan start margin.** 1.87–1.94 s, with one run at 2.08 s. The extra ≈ 0.2 s is in the bigger
   instances (`slotRP` 425–440 ms, compiles) and 12 more keys (`mkKM`). If it binds:
   - give `tensorWK` a split layout (`splitOf`: 256 + 32 rows instead of 512). This also saves
     ≈ 65k rows per prototype for P2 and the region;
   - or share each kind's point forms across a key's instances (the same `r` serves 132–290
     instances).
2. **Rows.** Each `tensorWK` instance carries three sub-templates (286 rows for `[19,…]`). A single
   circuit on a padded mux of `r` (`r′_v = Σ_κ sel_κ·r_κ,v`, then one `tensorW 19`) would be ≈ 200
   rows. The ruling chose per-kind sub-templates. Revisit only if M's rows or P2's time bind.
3. `FRVIRTplBuild` is over 1,000 code lines (1,088; 1,087 at HEAD).
