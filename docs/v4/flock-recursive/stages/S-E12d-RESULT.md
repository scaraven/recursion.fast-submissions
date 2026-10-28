# S-E12d (track L-circ): RESULT, pass 1. The per-revision template set (revision 4.3 (a)), the regenerated hint and dump, the profile of V(N4) outside `evalM`

Stage S-E12d, 2026-10-28. Base HEAD `67e5c76` (blueprint 4.3). The tree was re-snapshotted on
`c2c6fba` (S-CN4) and `29d0016` (R4d). Build tree `logs/fr-build-SE12d` is a copy of
`fr-build-SE12c` with its probes, against `logs/org20`. Logs are in `logs/S-E12d/`; the journal is
`S-E12d-JOURNAL.md`. Every lean, lake and probe command ran in a 16 GB scope with a timeout. Probes
ran on core 29 (load ≈ 2–4). Nothing is committed.

**This is a multi-pass track.** §8 is the handover.

## Status

| Item | State |
|---|---|
| 1. The template filter; `ImplT`/`compileT_sound` over it; the plan's proofs generalised; 3.x unchanged | **Done** (§1). |
| 2. 4.1 prototypes at the 4.1 set; templates for `chainLk4`'s mask and `shiftSegI` | **Half done.** Both prototypes compile at `keys41`: 3.x's `shiftMask` template is gone and the op is an import. S-CN4 landed (`c2c6fba`). **The two templates are not built**; their design is in §8. |
| 3. `FRNodeRows4Hint` and the node dump regenerated | **Done at `keys41`** (§3). INT-8's uniform `gen4` is not committed (it is in the worktree, uncommitted), so the prototypes are still S-E12b's `gen4G`. The seam is `protoProg` (§3). |
| 4. Profile of V(N4) outside `evalM` | **Done** (§4). **The +27 ms is `rsWeight`:** its fast path is gated on 3.x's 23 coordinates, and seq4 has 25. Levers are listed. |

## 1. Item 1: the template set

**`FRVIRTplSet`** (new; 136 code lines, 12 theorems):

- **`TFilt := TKey → Bool`**: a revision's set of template keys. `allK` is 3.x's set (every key);
  **`keys41`** is every key except `.shiftMask`.
- **`tplExtF F tc`**: `tplExt` keeping an instance only if its key is in `F`. Any other op falls
  back to `opOut`, which makes `shiftMask` an import. **`tplExtF_all : tplExtF allK tc = tplExt tc`.**
- **`KeyImpl impl k`**: `ImplT`'s field for key `k`'s op, or `True` for keys whose op reads no
  `OpImpl` field. **`ImplTF F impl := ∀ k, F k → KeyImpl impl k`.**
  - `ImplT.toF : ImplT impl → ImplTF F impl` holds for every `F`.
  - **`implTF_all : ImplTF allK impl ↔ ImplT impl`**: 3.x's set asks exactly `ImplT`.
  - `implTF_keys41`: `ImplTF keys41 {impl with shiftMask := sm}` holds for any `sm`, for example
    `implSeg`'s `shiftSegI` or `implN4`'s `shiftMask4I ν`.
- **`tplExtF_ok : ImplTF F impl → ExtOk impl L.ctx (tplExtF F L.ctx)`.** The proof reuses
  `tplExt_ok` at `fixT impl`, which is `impl` with the ten templated fields set to 3.x's
  (`fixT_implT`). **`evalOp_fixT`**: an op that `tplExt` templates with key `k` reads only `k`'s
  field, so where `impl` meets `KeyImpl impl k`, it runs the op exactly as `fixT impl` does.
- **`compileTF F L P base ops := compileX (tplExtF F L.ctx) P base ops`**, with `compileTF_all`.
- **`compileTF_sound`**: `compileT_sound`'s statement with `compileTF F` and `ImplTF F` in place of
  `compileT` and `ImplT`.
- **`layOfF F`**: `layOf` at `F`.

**The generalisations** (each statement is the old one with the set or the extension as a
parameter; no statement was weakened):

| Old | Generalised | 3.x instance |
|---|---|---|
| `tplExt tc` | `tplExtF F tc` | `tplExtF_all` (propositional; `tplExt` itself is unchanged) |
| `ImplT impl` | `ImplTF F impl` | `implTF_all` (↔) |
| `compileT_sound` | `compileTF_sound` | `compileT_sound` unchanged |
| `compMS L P …` (`FRVIRTplBuild`) | **`compMSX X L P …`** over an extension family `X : TCtx → Ext` | `compMS := compMSX tplExt`, **`compMS_rfl : compMS = compMSX tplExt := rfl`** |
| `compMS_eq` | `compMSX_eq` (`= compileFromX (X L.ctx) …`) | `compMS_eq`: same statement, proved by `compMSX_eq tplExt` |
| `compMS_T` (`FRVIRTplFast`) | `compMSX_T` (`= compileX (X L.ctx) …`) | `compMS_T` unchanged (file untouched) |
| `slotRP_rows` | already generic over any `CS` and layout | unchanged |
| `planData4`/`planData4_rows` | at `compMSX (tplExtF (protoF π))`; `protoCS π := compileTF (protoF π) …`; **`protoF π := keys41`** | `planData4_rows`: statement unchanged |

**The 3.x checks.** 3.x's `tplExt`, `ImplT`, `compileT`, `compileT_sound`, `tplExt_ok`,
`compMS_T`, `FRVIRTplFast` and every 3.x consumer are untouched. `compMS` is rfl-equal to the
generalised compile, and `compMS_eq`'s statement is unchanged. `implC_meets`, `evalMT_eq`,
`node_m_sound` and `acc_eq` build unchanged. `ax/AxE12d.lean` checks four `rfl` equalities:

- `compMS = compMSX tplExt`;
- `compileT L P b o = compileX (tplExt L.ctx) P b o`;
- `compileTF keys41 … = compileX (tplExtF keys41 …) …`;
- `protoCS 0 = compileTF keys41 …`.

Two traps, recorded for the next agent:

- `rfl` on `(fixT impl).eqZ = Impl.eqZI` (and on `rowW`) hits the maximum recursion depth: the
  elaborator unfolds the closed `lagW xT 64 denS`. Use
  `constructor <;> intros <;> simp only [fixT]` instead, as `implCWith_implT` does.
- `evalOp_fixT` with `rfl` tried first on every constructor timed out at `whnf`. Reducing
  `tplExt` at the hypothesis first fixes it.

## 2. Measurements

| What | Value | Log |
|---|---|---|
| plan process start (`plan4t init`) | **1.86 / 1.81 / 1.82 s** (≤ 2 s); `inR true` | `plan4t-init-{1,2,3}.log` |
| plan pieces | keys 98 (S-E12c: 100), pieces 6,404 + 6,406, instances 5,394 + 5,394 | `plan4t-check.log` |
| `evalMT4` best (median) | N2 82.4 (88.9), N4 80.1 (86.3), N8 54.7 (56.5) ms; **equal to the sparse sum for all three kinds** | `plan4t-check.log` |
| V(N4), 3.x stand-ins, 21 reps | best **205.4 / 204.7**, median 214.7 / 210.8 ms | `vtime4-a.log`, `vtime4-a2.log` |
| V(N4) with S-CN4's `shiftMask4I`, `linkWAll4I` | best 205.6 / 208.8, median 210.9 / 218.4 ms | `vtime4-cn4.log`, `vtime4-cn4b.log` |
| 3.x V(N30), same core | best 178.5, median 191.6 ms | `vtime3-n30.log` |
| build `FR FRNodeRows4Fit FRNodeRows4Model FRVIRTplSet` | green, **2,504 jobs** | `build-final.log` |

At the ratio 1.19, V(N4) is ≈ 172–175 ms on the 7763 (best), against the 206 ms cap. The VM median
(211–218 ms) is under the 230 ms kill line.

**Sequential profiles** (`prof.sh`, `Elab.async=false`, one core; `profile-*.log`):

| Module | wall | type checking | tactics | peak RSS |
|---|---|---|---|---|
| `FRVIRTplSet` (new) | 8.7 s | 0.08 s | 0.52 s | 2.80 GB |
| `FRVIRTplBuild` | 16.3 s | 0.74 s | 2.53 s | 2.88 GB |
| `FRNodeRows4` | 7.1 s | 0.12 s | 0.08 s | 2.81 GB |
| `FRNodeRows4Plan` | 11.9 s | 0.57 s | 1.55 s | 2.85 GB |
| `FRNodeRows4Hint` | 6.2 s | 0.00 s | — | 2.77 GB |

## 3. Item 3: hint and dump

- **`FRNodeRows4Hint`**, regenerated by `LayDump4` at `layOfF (protoF π)` (`laydump4.log`, 2.7 s).
  The `.shiftMask 18 18` and `.shiftMask 36 18` groups are gone, and the later groups moved up by
  one 4,096-row slot. The header says how it was generated.
- **Node dump**: `logs/S-E12d/nodedump/` (352 MB, `SHA256SUMS`; probe `nodedump4`, 25 s). Each
  prototype now has 3,031 instances and 485,231 / 484,527 indexed rows, that is 2,071 rows fewer:
  3.x's `shiftMask` template. `shiftMask`'s three results are import cells (`mregs-p{π}.txt`). The
  P2 README is updated: the prover writes `shiftMask4I ν` for a node and `shiftSegI` for a
  segment.
- **Seam for INT-8.** INT-8's uniform `gen4` is not committed. When it lands:
  1. point `protoProg π` (`FRNodeRows4`, one definition) at the uniform group programs;
  2. re-run `laydump4 0` into `FRNodeRows4Hint` and `nodedump4` into a new dump directory;
  3. re-run `plan4t check` and the build.

  A stale hint is still sound: it fails `ProtoFit`, and the node is then unprovable.

## 4. Item 4: V(N4) outside `evalM` (S-E8's method)

`vtime4 prof 7` runs `progNode .N4` op by op under `implN4`. The kind index is `N30`. Times per op
kind are summed and averaged over 7 runs. The pseudo-random oracle answers are excluded, so
`askNode` is not comparable with S-E8's figure. The 3.x side is `vtime prof N`, three runs
(`prof4-n4.log`, `prof3-n30-{1,2,3}.log`).

| Op kind | 4.1 `N4` (106,240 ops) | 3.x `N30` (106,106 ops) | Δ |
|---|---|---|---|
| `evalM` | 81.6 | 73.0 | **+8.6** |
| **`rsWeight`** | **40.5** | **8.75** | **+31.8** |
| `walkAB` | 9.9 | 9.5 | +0.4 |
| `tensorW` (1,627) | 8.2 | 7.9 | +0.3 |
| `mulK` / `addK` | 7.9 / 4.3 | 9.9 / 5.8 | −3.5 |
| `dotKF` (871) | 7.0 | 7.6 | −0.6 |
| `eqTable` (12) | 4.2 | 5.5 | −1.3 |
| `evalL`, `lagrangeS`, `rowW`, `maskRows`, `phiRS`, `targetS`, `linkWAll`, `slotW`, `eqZ` | within ±0.6 each | | |

(The probe prints hundredths without zero padding, so an entry printed "2.8" may be 2.08 ms. This
does not affect any entry above 4 ms.)

**The finding.** The `rsWeight` op at `N4` has `|r| = 7`, four claims of 25 coordinates (all `F`
points) and `|ρ| = 25` (`prof4-n4-rsw.log`). `rsWeightF` takes the fast kind-factor fold `wEvalKF`
only when `p.size = 23 ∧ ρ.size = 23`, which are 3.x's `N30` sizes. At seq4's 25 coordinates,
claim 2 falls back to the generic `wEvalKC` (`KW.kwI` per stage). That costs ≈ 32 ms, which
accounts for all of the +27 ms in V. The rest of the 4.1 program is at or under 3.x's.

**Levers, in order of size:**

1. **`rsWeight` at seq4: a 4.1 `wEvalKF`** whose block skeleton (`KW.skelM`/`skelP`, today 3.x's
   node layout, 16 block bits) is built from the 4.1 layouts (`nodeLayout4`, 18 block bits). The
   4.1 `rsWeight` needs the 4.1 kind factor (`kfInd4`) anyway: the measured op is the 3.x stand-in
   at the 4.1 sizes. Expected gain ≈ 30 ms, so V(N4) ≈ 175 ms best on the VM. `FRVerifierImplOps`
   and `FRKindWeight` are not L-circ's; this is a request to their owner (S-T1/S-C, or S-CN4 with
   the 4.1 `implN`).
2. **`evalM`, +8.6 ms**: the levers of S-E12c §2 (the 70 ms index check is at process start, not
   here). Within `evalMT4`: the two prototypes' `ectx3`/`slotV3`.
3. Nothing else is over 1.5 ms apart. The 4.1 program's `piDigest`/`askNode`/`selectHalf` path is
   at 3.x's cost.

## 5. What was built

| Module | New | Content | Code (HEAD → now) |
|---|---|---|---|
| `FRVIRTplSet` | yes | `TFilt`, `allK`, **`tplExtF`**, `tplExtF_all`, **`compileTF`**, `compileTF_all`, **`KeyImpl`**, **`ImplTF`**, `ImplT.toF`, **`implTF_all`**, `fixT`, `fixT_implT`, **`evalOp_fixT`**, **`tplExtF_ok`**, **`compileTF_sound`**, `layOfF`, **`keys41`**, `implTF_keys41`, `ctlCS`, controls `implTF_all_shiftMask`, `tplExtF_ctl`, `keys41_ctl` | 0 → 136 (12 thm) |
| `FRVIRTplBuild` | edit | `compMS` → **`compMSX X`** (the extension family a parameter), `compMSX_eq`, **`compMSX_T`**; `compMS := compMSX tplExt`, `compMS_rfl`, `compMS_eq` (same statement) | 1,073 → 1,087 |
| `FRNodeRows4` | edit | imports `FRVIRTplSet`; **`protoF`**; `protoCS` at `compileTF (protoF π)` | 85 → 87 |
| `FRNodeRows4Plan` | edit | `planData4` at `compMSX (tplExtF (protoF π))`; `planData4_rows` (statement unchanged) | 493 → 494 |
| `FRNodeRows4Hint` | regenerated | layouts at `keys41` | 32 → 31 |

Probes in `logs/fr-build-SE12d/probe` (outside the entry):

- `LayDump4`, now at `layOfF`;
- `PlanM4`, now at `compMSX`;
- `VTime4` gains `prof` (per-op profile), `cn4` (S-CN4's `NI4.implN4` with 3.x's `targetS`/`evalL`
  stand-ins) and the `rsWeight` operand print.

## 6. Checks

- **Build:** `lake build FR FRNodeRows4Fit FRNodeRows4Model FRVIRTplSet` is green at `29d0016` plus
  these modules: 2,504 jobs, no `sorry` (`build-final.log`). It was also green at `67e5c76` plus
  these modules: 2,498 jobs (`build-67e5c76.log`).
- **Axioms** (`axioms.log`, `ax/AxE12d.lean`): 26 declarations, each within `propext`,
  `Classical.choice` and `Quot.sound`. They are the new ones, the generalised ones and the
  untouched 3.x ones (`compileT_sound`, `tplExt_ok`, `compMS_T`, `evalMT_eq`, `implC_meets`,
  `node_m_sound`, `acc_eq`). The four `rfl` checks of §1 pass.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 285
  files, 0 findings (`source-rule.log`).

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `tplExtF` | `tplExtF_ctl`: `shiftMask` on two `af` registers is templated under `allK`; `shiftEq` under `keys41` | `tplExtF_ctl`: `shiftMask` is not templated under `keys41` |
| `keys41` | `keys41_ctl` (`eqZ` kept) | `keys41_ctl` (`shiftMask` dropped) |
| `ImplTF` | `implTF_all` (3.x: exactly `ImplT`); `implTF_keys41` (met with any `shiftMask`) | `implTF_all_shiftMask`: `ImplTF allK` pins `shiftMask` to 3.x's `NodeI.shiftMaskI` |
| `protoCS` at `keys41` | measured: `inR true`, `evalMT4` = sparse sum (`plan4t-check.log`) | the dump: 2,071 rows fewer than at `allK` (S-E12c's dump), so the filter acts |

## Deviations and requests

1. **The plan's compile is generalised over the extension family** (`compMSX X`), not over the
   filter alone. This keeps 3.x's instance `rfl`-equal (`compMS_rfl`): the alternative
   (`tplExt := tplExtF allK`) would make `tplExt` a filtered term, equal to today's only
   propositionally.
2. **`tplExt`, `ImplT`, `compileT` and `compileT_sound` are unchanged.** The filtered forms are new
   declarations in a new module. `tplExtF_ok` is derived from `tplExt_ok` (`fixT`), not re-proved
   case by case.
3. **`planData4` uses one set per prototype** (`protoF π`, both `keys41` today) rather than taking
   the sets as arguments. The 4.1 node and segment templates will differ by prototype (§8).
4. **Request (owner of `rsWeight`'s 4.1 implementation):** lever 1 of §4.
5. **`FR.lean`:** no change needed. `FRVIRTplSet` is in `FR`'s closure through `FRNodeRows4`.

## 8. Handover: the remaining items, in order

1. **The segment's `shiftSegI` template** (prototype 1). It needs no kind mux: `implSeg`'s
   `shiftMask` is kind-free.
   - **New key** `TKey.shiftSeg (n m : ℕ)` (`FRVIRTplCore`; a full rebuild). `tplOf` case. Update
     `LayDump4`'s `keyS`.
   - **Template module `FRVIRTplSeg`**, imported by `FRVIRTplExt`. `FRSegTarget4` is downstream of
     `FRVIRTplExt` (through `FRVerifierImpl`), so state `_ok` against a local copy `segMaskV` of
     `shiftSegI` (with `lastAt`). Then prove `segMaskV = shiftSegI` by `rfl` in a downstream module.
   - **Inputs:** `τL` (36) and `r` (18). Built with the existing builders:
     - `E`: `mulsG` + `eqFac` + `prodG`, as `tplEqPt`.
     - The bits `b_l = [τL₁₈₊ₗ = 1]`: an `inv` gate on `I(18+l) − 1`, with `b = 1 − s`.
     - `eqAtR(τ, L)`: per coordinate `τ + s − 2sτ` (one `mul`), then `prodG`.
     - The carries: `c₀ = 1`, `c_{l+1} = c_l·b_l` (`mul`).
     - The bits of `L + 1`: `d_l = b_l + c_l − 2c_{l+1}` (linear), then `eqFac(d_l, r_l)` (one
       `mul` each), then `prodG`.
     - `[L + 1 < 2^18] = 1 − c₁₈`.
     - `Sh = shiftG(τ, r) + (1 − c₁₈)·P₁·P₂`: `shiftG_ev` gives the shift.
     - `E0 = prodG (1 − r_l)`.
     - About 250 rows.
   - **The lemmas:** `lastAt`'s bits (`testBit` of `Σ_{l<18} b_l 2^l`), the bits of `L + 1` by the
     carry, and `L + 1 < 2^18 ↔ ¬∀ l, b_l`.
   - **Routing:** `tplExt4 F tc` = `tplExtF F tc`, except at `.shiftMask t r` with operands
     `af 36, af 18`, which goes to `.shiftSeg 36 18` when `F` has it. Add the case
     `KeyImpl impl (.shiftSeg ..) := impl.shiftMask = segMaskV`, plus `tplExt4_ok` (from
     `tplExtF_ok` and the new case). Set `protoF 1 := keys41 ∪ {shiftSeg}`.
2. **The node's `chainLk4` template** (prototype 0). The group runs `N4`/`N2`/`N8` at index `ι`, and
   the run's `impl` is `NI4.implN4 … (nodeGrp ι)`, whose `shiftMask` is `shiftMask4I (nodeGrp ι)`.
   So:
   - **`ExtOk` at one kind:** add `ExtOkAt impl tc X κ`, `ExtOk → ExtOkAt`, and
     `compileFromX_soundAt`/`compileX_soundAt` (`FRVIRCompileSound`). The old statements are kept
     and derived. Make the key requirement kind-indexed (`KeyImplAt impl κ k`, with
     `KeyImpl` its kind-free part).
   - **The template is kind-muxed.** The per-kind constants are template inputs as selector forms
     `P.kc` (linear, no rows):
     - the bits of `c = chLen₀ + chLen₁ − 1`;
     - the bits of `a = chLen₀ − 1` and of `chLen₀`;
     - the coordinate gate `g = [nb = 18]` (`N2` has 17: use `g·τ₁₇`, `g·r₁₇`, one `mul` each, so
       that coordinate 17's factor is 1 when inactive).
   - **The computations:**
     - The prefix sum `Σ_{y<c}` by the digit DP over `c`'s bits (≈ 5 `mul` per coordinate).
     - The successor sum `shP` as `nb` suffix prefix sums. Their bounds `(c + 2^t − 1) >> (t+1)`
       are per-kind constants as well, as bits: O(nb²) ≈ 1,000 rows.
     - The `eqAtR`s at the constants: in characteristic 2, `b r + (1−b)(1−r) = 1 + b + r`, linear
       in `b`.
   - **`_ok`:** under `SelOk w P κ`, the outputs are `shiftMask4I (nodeGrp κ) τ r`. State it
     against S-CN4's `shiftMask4S` through `shiftMask4_meets`. Set
     `protoF 0 := keys41 ∪ {shiftMaskN4}`.
3. **Regenerate** `FRNodeRows4Hint` (`laydump4 0`), the dump (`nodedump4`) and `plan4t check`
   after 1–2, and again after INT-8 (§3 seam).
4. **V:** re-measure with lever 1 of §4 when its owner lands it. Then re-run the `rsWeight` operand
   print (`vtime4 prof 1`).
