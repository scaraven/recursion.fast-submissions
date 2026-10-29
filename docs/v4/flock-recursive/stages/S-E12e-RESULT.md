# S-E12e (track L-circ): RESULT. The two 4.1 `shiftMask` templates, routed per prototype; hint, dump and plan regenerated; V(N4) before and after S-T2's lever

Stage S-E12e, 2026-10-28. Base HEAD `036eb7e` (S-E12d). HEAD moved during the stage (S-T2
`1ee751b`, S-CN4b `3ef2c51`, R4e `2e5b79a`, R4f `ad3fbeb`); none of them touches an L-circ module.
The build tree `logs/fr-build-SE12e` (a copy of `fr-build-SE12d`, against `logs/org20`) was
re-snapshotted on `2e5b79a`, then on `ad3fbeb`; both final builds are green (§6).
Logs are in `logs/S-E12e/`; the journal is `S-E12e-JOURNAL.md`. Every lean, lake and probe command
ran in a 16 GB scope with a timeout. Nothing is committed. INT-8 has not committed, so the seam of
S-E12d §3 stays (§3).

## Status

| Item (S-E12d §8) | State |
|---|---|
| 1. The segment's `shiftSegI` template | **Done.** `TKey.shiftSeg`, `tplShiftSeg` (290 rows), `tplShiftSeg_ok`; `segMaskV_eq : segMaskV = shiftSegI` (`rfl`). |
| 2. The node's `chainLk4` template, kind-muxed, sound at one kind | **Done.** `TKey.maskN n m ks`, `tplMaskN` (2,161 rows), `tplMaskN_ok`; `ExtOkAt`, `compileX_soundAt`; `maskNV_eq : maskNV (nodeQ ν) = shiftMask4I ν`. |
| 3. Both keys in the 4.1 set; hint, dump, plan check | **Done.** `keys41` already keeps both keys; the per-prototype route `protoR` picks one. Plan start 1.74–1.80 s (S-E12d's binary 1.75–1.85 s, same core, interleaved). |
| 4. V(N4) before and after S-T2's `rsWeight` lever | **Done.** Best 202.8 / 202.9 ms before, **170.3 / 173.2 ms after** (`rsWeight` 40.5 → 9.0 ms). |

## 1. The templates

### The segment: `FRVIRTplSeg` (new; 285 code lines, 19 theorems)

`segMaskV` is a copy of `Rev4.shiftSegI` (that module is downstream of the templates), and
`lastAtV` is a copy of `lastAt`; `FRVIRTpl4Bridge.segMaskV_eq` proves `segMaskV = shiftSegI` by `rfl`.

**`tplShiftSeg n m`** (inputs `τL : AF n`, `r : AF m`; 290 rows) mirrors `shiftSegI`:

- **The bits** `b_l = [τL₁₈₊ₗ = 1]`. `isOneG` uses an inverse of `x − 1` and one product
  `s = (x − 1)·(x − 1)⁻¹`, and sets `b = 1 − s`. The product is needed because `Gate.Eqn (.inv a)`
  pins only `i = a⁻¹`.
- **`eq(τ, r)`** (`facsG` and `prodG`, as `tplEqPt`) and **`shift(τ, r)`** (`shiftG`).
- **`eq(τ, L)`**: per coordinate `bτ + (1 − b)(1 − τ)`.
- **The carries** `c_{l+1} = c_l b_l` (`scanG`), the bits of `L + 1` as
  `d_l = b_l + c_l − 2c_{l+1}`, then `eq(r, L + 1)`.
- **The guard** `1 − c₁₈ = [L + 1 < 2^18]`, two products, and **`eq(r, 0)`** (`eqAtG`).

The lemmas:

- **`testBit_succ_carry`**: bit `l` of `L + 1` is bit `l` of `L` xor "the bits below `l` are all set".
- **`lt_two_pow_iff_carry`**: for `L < 2^n`, `L + 1 < 2^n` iff not all `n` bits of `L` are set.
- **`testBit_lastAtV`**: from a copy of P4a's `testBit_sum_bits`, over a predicate.

**`tplShiftSeg_ok`**: from the gate equations, `one = 1` and the inputs, the outputs are
`encV` of `segMaskV τL r`.

### The node: `FRVIRTplMaskN` (new; 217 code lines, 13 theorems)

`maskNV q` is S-CN4's first computed `shiftMask4I`, written over the constants
`q = (nb, chLen₀, chLen₁)` with copies of `mF` and `shP` (`mFV`, `shPV`).

**`tplMaskN n m ks`** (inputs `τ`, `r`, then one selector form per kind) consists of:

- the shared products `t_l = τ_l r_l`;
- per entry of `ks`, a sub-circuit **`blkG`** that mirrors `maskNV` gate for gate:
  - `prefixG` and `shG`, which follow `prefixP`'s and `shP`'s own recursion (the low bit first;
    `prodAtG` for `prodAt`);
  - four `eqAtG`;
  - two products;
- the mux `out_i = Σ_j sel_j · out_{j,i}` (9 products).

The proofs:

- **`prefixG_ev`** and **`shG_ev`** are by induction on that recursion;
- **`blkG_ev`**: one sub-circuit computes `maskNV q`;
- **`tplMaskN_ok`**: with the selector inputs one-hot at `j₀ < |ks|`, the outputs are `encV` of
  `maskNV ks[j₀] τ r`.

At the node's constants this is 2,161 rows (model before building: N2 749, N4 714, N8 724, plus 18
shared products and 9 mux products, less sharing).

`FRVIRTpl4Bridge.maskNV_eq` proves `maskNV (nodeQ ν) = NI4.shiftMask4I ν`. S-CN4b changed
`shiftMask4I` during this stage: it now reads the factors from a table (`prefixQ`/`shQ`). So the
proof shows that `maskNV` meets `shiftMask4S`, by S-CN4's earlier argument (`sum_lk`, `prefixP_eq`,
`shP_eq`), and then rewrites with `shiftMask4_meets`.

## 2. One kind, and the route

**`FRVIRCompileSound`** (edited):

- **`ExtOkAt impl tc X κ`** is `ExtOk` with the run's kind fixed.
- `ExtOk.at`; **`extOk_iff`**: `ExtOk ↔ ∀ κ, ExtOkAt`.
- **`compileFromX_soundAt`**: the induction, now over `ExtOkAt`.
- **`compileX_soundAt`**.
- `compileFromX_sound` and `compileX_sound` keep their statements; they are now derived (`hX.at κ`).

**`FRVIRTplSet`** (edited; 136 → 255 code lines):

- **`ShR`** (`imp | seg | node ks`): the prototype's `shiftMask` route.
- `kIx`: a selector index's position in `kinds`.
- **`tplExt4 F R`**: `tplExtF F`, except that a `shiftMask` on `af n, af m` goes to the route's key
  when `F` keeps it. The node's instance reads `kinds.map P.sel` after `τ` and `r`.
- `tplExt4_imp`: `tplExt4 F .imp = tplExtF F`.
- **`RouteOk R impl κ`**: the segment's `shiftMask` for `.seg`; for `.node ks`,
  `kIx κ < |ks|` and `impl.shiftMask = maskNV ks[kIx κ]`.
- **`tplExt4_okAt`**: `ImplTF F impl → RouteOk R impl κ → ExtOkAt impl L.ctx (tplExt4 F R L.ctx) κ`.
- **`compileTF4`**, `compileTF4_imp` (`= compileTF` without a route), **`compileTF4_soundAt`**.
- `layOfF4`.

**`FRVIRTplCore`**: `TKey.shiftSeg n m` and `TKey.maskN n m ks` (a full rebuild).
**`FRVIRTplExt`**: `tplOf` cases for both keys.

**`FRNodeRows4`**:

- `nodeOf` (selector index ↦ `N4`/`N2`/`N8`), with `nodeGrp_nodeOf`;
- `nodeQ ν = (ν.m − 14, chLen ν 0, chLen ν 1)`;
- **`protoR π`**: `.node (kinds.map (nodeQ ∘ nodeOf))` for prototype 0, `.seg` for prototype 1;
- `protoCS π := compileTF4 (protoF π) (protoR π) …`.

**`FRNodeRows4Plan`**: `planData4` at `tplExt4 (protoF π) (protoR π)`. `planData4_rows`
keeps its statement.

**`FRVIRTpl4Bridge`** (new; 65 code lines, 13 theorems):

- `segMaskV_eq`, `maskNV_eq`;
- **`routeOk_implSeg`**: `implSeg impl₀` meets prototype 1's route at every kind;
- **`routeOk_implN4`**: `NI4.implN4 base tS (nodeOf ι)` meets prototype 0's route at index `ι`;
- **`protoCS_soundAt π`**: `compileTF4_soundAt` at prototype `π`'s set, route, layout, selectors,
  base and program.

## 3. Hint, dump, plan

- **`FRNodeRows4Hint`** was regenerated by `laydump4 0` at `layOfF4` (`laydump4.log`, 7.9 s):
  - prototype 0 has `.maskN 18 18 [(18, 23168, 92672), (17, 23168, 46336), (18, 92672, 92672)]` at
    row 393,216, with 12 cell bits;
  - prototype 1 has `.shiftSeg 36 18` at row 391,168, with 9 cell bits.
- **Node dump**: `logs/S-E12e/nodedump/` (`SHA256SUMS`; README updated; `nodedump4-run.log`, 24.6 s).
- **Plan** (`plan4t-check.log`): 100 keys (S-E12d: 98), 6,405 + 6,407 pieces, `inR true`.
  `evalMT4` equals the sparse sum for N2, N4 and N8. Best times: N2 81.5 ms, N4 86.9 ms,
  N8 57.4 ms.
- **Plan start**:

  | Run | Times |
  |---|---|
  | `plan4t-init-{1..6}.log`, core 29, load 3–5 | 1.88, 2.08, 1.90, 1.85, 1.82, 1.79 s |
  | Interleaved with S-E12d's binary, same core (`plan4t-ab.log`) | **1.74–1.80 s** against 1.75–1.85 s |

  The two templates add nothing measurable at process start.
- **INT-8 seam**: INT-8 is uncommitted. `protoProg` still points at S-E12b's `gen4G`
  (`FRVIR4Mux` was dropped from my overlay, so the build uses HEAD's). When INT-8 lands, do the
  following:
  1. point `protoProg` at the uniform programs;
  2. run `laydump4 0` into the hint, run `nodedump4`, and run `plan4t check`.

  A node program whose `shiftMask` operands are not `af 18, af 18` would fall back to an import; the
  key's sizes come from the operands.

### For P2 (dump changes)

The 4.1 `shiftMask` is no longer an import, in either prototype. Its three results are the
template's output forms in `mregs-p{π}.txt`: 26,642 → 26,639 import registers in prototype 0. Each
prototype has one more instance (3,032).

- **Prototype 0** has 2,161 more rows (487,391 indexed). Its later groups moved down one
  4,096-row slot and 4,096 cells.
  - The template computes all three kinds' masks and muxes them by the slot's selector copies. The
    prover fills every sub-circuit's locals, whichever kind is selected.
- **Prototype 1** has 290 more rows (484,816 indexed). Its later groups keep their rows and moved
  by 4,096 cells.
- An inverse gate's two locals are `a⁻¹` (with `0⁻¹ = 0`) and `a·a⁻¹`.

The README spells this out with the gate order.

## 4. V(N4) by S-E8's method (VM, core 30, 21 reps; load ≈ 6–8)

| Configuration | Best | Median | Log |
|---|---|---|---|
| Before the lever (3.x `rsWeight` stand-in, `vtime4 21`) | 202.8 / 202.9 ms | 209.7 / 208.1 ms | `vtime4-before-{a,b}.log` |
| **After** (`NI4.implN4` with S-T2's `withRS4`, `vtime4 21 cn4`) | **170.3 / 173.2 ms** | 172.8 / 181.5 ms | `vtime4-after-{a,b}.log` |

Per op after the lever (`vtime4 prof 7 cn4`, `prof4-n4-cn4.log`):

- `rsWeight` **9.0 ms** (S-E12d: 40.5 ms);
- `evalM` 86.3 ms (S-E12d: 81.6 ms; +2,451 template rows, and higher load);
- `walkAB` 9.5 ms;
- `shiftMask` 0.12 ms.

The operand print is unchanged: `|r| = 7`, four claims of 25 coordinates, `|ρ| = 25`. At the 1.19
ratio, V(N4) is ≈ 143–146 ms best on the 7763, against the 206 ms cap.

## 5. What was built

| Module | New | Code lines (HEAD → now) | Theorems |
|---|---|---|---|
| `FRVIRTplCore` | edit | 208 → 210 | 23 |
| `FRVIRTplSeg` | yes | 0 → 285 | 19 |
| `FRVIRTplMaskN` | yes | 0 → 217 | 13 |
| `FRVIRTplExt` | edit | 439 → 442 | 21 |
| `FRVIRCompileSound` | edit | 240 → 281 | 22 |
| `FRVIRTplSet` | edit | 136 → 255 | 20 |
| `FRNodeRows4` | edit | 87 → 95 | 10 |
| `FRNodeRows4Plan` | edit (4 lines) | 494 → 494 | 42 |
| `FRNodeRows4Hint` | regenerated | 31 → 34 | 0 |
| `FRVIRTpl4Bridge` | yes | 0 → 65 | 13 |

Probes (outside the entry) in `logs/fr-build-SE12e/probe`: `LayDump4` (`layOfF4`, the new keys),
`PlanM4`, `NodeDump4`. The axiom file is `ax/AxE12e.lean`.

**Sequential profiles** (`Elab.async=false`, one core; `profile-*.log`; peak RSS ≈ 2.75 GB each):

| Module | Wall | Type checking | Tactics |
|---|---|---|---|
| `FRVIRTplSeg` | 9.5 s | 0.30 s | 0.94 s |
| `FRVIRTplMaskN` | 9.0 s | 0.13 s | 0.49 s |
| `FRVIRCompileSound` | 10.1 s | 0.19 s | 0.66 s |
| `FRVIRTplSet` | 11.2 s | 0.19 s | 0.98 s |
| `FRVIRTpl4Bridge` | 6.5 s | 0.08 s | 0.17 s |
| `FRNodeRows4Plan` | 14.8 s | 0.80 s | 2.62 s |

## 6. Checks

- **Build**: `lake build FR FRVIRTpl4Bridge FRNodeRows4Fit FRNodeRows4Model FRVIRTplSet` is green
  at `2e5b79a` plus these modules: 2,517 jobs, 5 min 33 s wall, no `sorry` (`build-final.log`).
  Re-run at `ad3fbeb` (R4f adds three soundness modules): green, 2,520 jobs, no `sorry`
  (`build-ad3fbeb.log`).
- **Axioms** (`axioms.log`, `ax/AxE12e.lean`): 47 declarations, each within `propext`,
  `Classical.choice` and `Quot.sound`. They are the new ones, the one-kind forms, and the
  untouched 3.x statements (`compileT_sound`, `tplExt_ok`, `compileTF_sound`, `compMS_T`,
  `evalMT_eq`, `implC_meets`, `node_m_sound`, `acc_eq`). The rfl checks of S-E12d still pass, plus
  `protoCS π = compileTF4 keys41 (protoR π) …`.
- **Source rule**: 299 files, 0 findings (`source-rule.log`).

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `tplExt4` | `tplExt4_ctl`: on `af 36, af 18`, route `seg` gives key `.shiftSeg 36 18`; route `node ks` gives `.maskN 36 18 ks` | `tplExt4_ctl`: route `imp` leaves it an import |
| `RouteOk` | `routeOk_ctl`: at `P30` it asks entry 1's mask | `routeOk_implN4_ctl`: prototype 0's route at `P30` holds iff the mask is `N2`'s, so not for `N4`'s or `N8`'s (hence `ExtOkAt`) |
| `ExtOkAt` | `extOk_iff`; `compileFromX_sound` is derived from it, statement unchanged | the route control above |
| `tplShiftSeg` | `tplShiftSeg_ok`; `tplShiftSeg_outs` (3 outputs); `carry_ctl` (5 → 6 flips bit 1) | `carry_ctl` (not the plain bit); `guard_ctl` (`allLow 7 3` true, `allLow 6 3` false) |
| `tplMaskN` | `tplMaskN_ok`; `prefixP_ctl` (`c = 4` counts `x = 3`) | `prefixP_ctl` (`c = 3` does not) |
| `protoR` | `protoR_ctl`: the constants are `N4`'s, `N2`'s and `N8`'s, in selector order | — |
| the prototypes | measured: `inR true`, `evalMT4` = sparse sum (all kinds) | the dump: −3 import registers, +2,161 / +290 rows, so the templates act |

## Deviations and requests

1. **A route, not a filter, selects the 4.1 key** (`ShR`, `tplExt4 F R`).
   - The node template needs the group's per-kind constants. They live downstream of `tplOf`, so
     they travel in the key (`ks`), and only the route can supply them.
   - `keys41` is unchanged and already keeps both new keys.
   - The handover's per-key `KeyImplAt` over the set would be contradictory: `keys41` contains
     `.maskN n m ks` for every `ks`. The kind-indexed requirement is therefore `RouteOk R impl κ`,
     next to the kind-free `ImplTF F impl`.
2. **The node template muxes three per-kind sub-circuits.** The handover proposed one circuit with
   the constants' bits as selector forms. The cost is ≈ 2,161 rows against an estimated ≈ 1,000;
   both fit one 4,096-row instance, and process start is unchanged (§3). The gain:
   - the proof is induction on `prefixP`/`shP`'s own recursion;
   - there is no digit-DP lemma and no 17-versus-18-coordinate lemma for `N2`;
   - the sub-circuit is generic in its constants.

   If M's rows ever bind, the bit-form circuit is the alternative.
3. **`maskNV` mirrors S-CN4's `prefixP`/`shP` form**, not S-CN4b's new table form. The two are
   equal through `shiftMask4S` (`maskNV_eq`).
4. **`FR.lean`** is not edited. `FRVIRTplSeg` and `FRVIRTplMaskN` are in `FR`'s closure through
   `FRVIRTplExt`. **`FRVIRTpl4Bridge` is not.** Request to the `FR.lean` owner: add
   `import FRVIRTpl4Bridge`. The module is built as a root of the entry's library either way.
5. **The INT-8 seam is unchanged** (§3).

## Open questions

1. The node soundness consumer (S-G / R4) should use `protoCS_soundAt` with
   `routeOk_implN4 base tS ι`. It also needs `ImplTF keys41 (implN4 …)`: `implN4` now goes through
   S-T2's `withRS4`, so the templated fields (`kindFoldWeight`, `slotW`, …) must still be 3.x's.
   That is the owner's check; `ImplTF` does not involve `rsWeight`.
