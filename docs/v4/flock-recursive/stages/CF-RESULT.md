# CF (track L-circ): RESULT — closed-form evaluation of the replay blocks (interim: handover)

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `407260d`; snapshots moved to `32e4e9c`
(INIT) and `97d578b` (FOLD2). Build tree `logs/fr-build-CF` (`mysnap.sh`: HEAD + this track's modules
linked, `mymods.txt`). Logs `logs/CF/`. Every lake/lean/probe in a 16 GB scope under `timeout`. No
sub-agents, nothing committed, no `sorry`. Journal: `CF-JOURNAL.md`.

**Status: stopped at the context limit, mid-stage.** Done and kernel-checked: the generic closed form, the
`rsWeight` template re-laid-out as repeated patterns with its soundness proof, the plan-side block trail
and the `rsWeight` block's evaluator with its equality theorem. **Not done**: wiring the evaluator into
`Plan4`/`rvOf` (so V and init are still REPF's sparse route over the new template), the structural
`RepFit` check, `evalL` (design in §5). The A/B at `97d578b` is in §3.2. §6 is the handover.

## 1. What was built

### 1.1 `FRVIRTplCF` (new, generic; green)

- `rowsAt gs k` (a gate list's rows from local `k`; `Tpl.rows = rowsAt · 0`), `nrows`, `RowT.sub`,
  **`rowsAt_sub`** (substituted gates have substituted rows).
- **`tm s t e X rows`** = `Σ_i eq(t, X+i)·⟨form_i, e⟩` (matrix `s`, 20 row coordinates); `tm_append`,
  **`tm_sub`** (substitution = pull-back of the wires, `pullE`).
- **`Rep`** (`n` instances of a pattern padded to `2^p` rows and locals, instance `s` at local
  `K + s·2^p`, its inputs through placeholders `Ph.cst f | Ph.var fs`), `Rep.gates`, `tm_repI`.
- **`Rep.tm_rep`**: the closed form for **any** row offset `X` and local offset: row `X + s·2^p + r`
  splits at bit `p` into a low part and a carry that depend on `r` only (`gN_spl`), so
  `tm = Σ_r eq_p(t, lo_r)·Σ_τ c_τ·cW_r(τ)`, `cW` an instance sum (`Σ_s T(s + c_r)·w_s`).
- The per-call evaluator: `Rep.ctx` (instance sums once: `S(c)`, `D(c,c')`, the placeholders' `Z`),
  `Rep.pass` (one pass over the pattern's rows); **`Rep.eval_eq`** (= `tm`).
- Segments `SG` (`irr` gates | `rep`), `sgGates`, the builder **`SM`** (`bind`, `map`, `lift` of a `GM`,
  `rep`), `SM.Ok` with `ok_bind/map/mono/lift` and **`SM.ok_rep`** (a pattern correct at every
  placeholder-valued wire assignment is correct at every instance; through `eqns_sub`).
- `sgVal`, **`sgVal_eq`** (segments' value = `tm` of their rows, the fitting patterns in closed form).

### 1.2 `FRNodeRows4RepCFRs` (new; green)

- **`rsGS`**: `rsWeight`'s sub-template as segments: `phiG`, powers of `β`, the blocks once (`blockOG`:
  `W₀`, `G`; irregular), **one 127-step `K` squaring chain per block** (`chainS`, `p = 8`), powers of `κ`,
  **one chain per claim coordinate** (`chainS`), **stage group A** (`patA`, 128 instances: per claim
  `j ≠ 1` `c_k·eq(p_j^(2^k), ρ)`, for claim 1 the 7-coordinate prefix), **stage group B** (`patB`, 128
  instances: claim 1's kind factor at stage `k` times the prefix times `c_k`; `kindG` at pattern index 0
  with stage values, `ok_kindGS`/`ok_levelGS`), then `κ^j·Σ_k` per claim (irregular).
- **`ok_rsGS`**: `rsGS` computes `rsRef ν r ps κ β ρ` (same hypotheses and conclusion as R3's `ok_rsG`).
- Helpers: `flatK/flatV/kfAt`, `unflat` (+ `unflat_flatten`), slots `kv`, sources `Src`, `phOf`
  (+ `phOf_inp`), `pOf`/`fit_pOf` (the stride from the pattern size), `repA`, `chainP`.

### 1.3 Plan side (new; green, not yet wired)

- `FRVIRTplCFE`: `tmG` (split-table row weights, fold; `tmG_eq`), prepared segments `PS`/`prepS`,
  **`psVal_eq`** (= `sgVal`), `sgNr`/`nrows_sgGates`; the locals bound check `psLocOk` with
  **`psLocOk_rows`** (for the structural `RepFit`).
- `FRNodeRows4RepCFP`: `rm` (rows at cell weights) with **`rowsVal_locF`/`rowsVal_locL`** (REPF's
  `repLocF`/`repLocL` values are `rm` at `wF`/`wL`), **`rm_inst`**, **`tm_subsG`** (the kind mux's
  sub-templates at their wires), `KP`/`kpOf` (an `rsWeight` op prepared: the three kinds' prepared
  segments, mux rows, copy rows), `kopV` and **`kopV_eq`** (`kopV … (kpOf P cs op outs) = rm … (kRows kRS
  repB cbRS P cs op outs)`); the block trail `RBlk`, `blk0`, `trailMB`, **`trailMB_eq`**, `arBlk0`,
  **`arBlk0_eq`** (`arBlk0.1 = askRowsT 0`, `arBlk0.2.flatMap RBlk.rows = repRowsP (rtC1c 0) 0`).

### 1.4 Edits to existing files (mine)

- `FRNodeRows4Defs`: `rsT` builds `rsGS` (`⟨sgGates g.1 0, …⟩`); import `FRNodeRows4RepCFRs`;
  **`repB` `@[noinline]`** (INIT's proposal 1); **`cbTS = repB + 2^19 + 2^16`, `cbEvL = repB + 2^19 + 2^16
  + 2^14`** (the padded template has 504,784 locals: up to `repB + 570,320`, past the old `cbTS`).
- `FRNodeRows4RepRsK`: `kRS_ok` uses `ok_rsGS` (statement unchanged).
- `FRNodeRows4RepLCtrl`: `cb_ctl` at the new sizes.

## 2. Statement changes

| Declaration | Change | Why |
|---|---|---|
| `N4s.rsT` (def) | `rsGS` segments instead of `rsG` gates | closed-form layout |
| `N4s.repB` (def) | `@[noinline]` (value unchanged) | start-up (INIT) |
| `N4s.cbTS`, `N4s.cbEvL` (defs) | `+2^16 − 2^14`, `+2^16 + 2^14 − 2^15` | the padded `rsWeight` locals |
| `cb_ctl` (control) | sizes 504,784 | idem |

`kRS_ok`, `rtRs_okW`, every `RepOk`/`Gaps4`/certificate statement, `evalMT4_eq`, `evalMX4_eq`,
`implN4F_hMX`, `slots_val`, `hfit4`: **unchanged** (the plan module is untouched so far).

## 3. Measurements so far

### 3.1 The new `rsWeight` sub-templates (`probe/CFRs.lean`, core 29; `logs/CF/cfrs5.log`, `cfrs6.log`)

| Kind | rows = locals (R3) | segments | build | closed form, 3 matrices | sparse (`tmG`), 3 matrices |
|---|---|---|---|---|---|
| N2 | 163,137 (146,837) | 4 irr + 4 rep | 1.26 s | 225–228 ms | 369 ms |
| N4 | 167,192 (155,094) | idem | 1.33 s | 237–251 ms | 404 ms |
| N8 | 174,449 (170,373) | idem | 1.50 s | 255–297 ms | 446 ms |

**KAT: the closed form equals the sparse value** for all three kinds and matrices (random points,
random wires, offsets `X = 3·2^15 + 1234`, locals from `5·2^16 + 77`; `cfrs5.log`).

Per segment (matrix `a` only, N4, `cfrs6.log`): blocks once (11,022 irregular rows) 11.3 ms; the two chain
groups 1.4 + 1.5 ms (125 and 100 chains: **the closed form works**: was ≈ 57 k rows sparse); stage
group A (251 placeholders) 26.5 ms; group B (603 placeholders) 42.5 ms. **The stage groups' cost is the
placeholders' instance sums `Z_i(c) = Σ_s T(s+c)·⟨σ_s,i, e⟩`** (≈ 220 k form evaluations per kind), and
`psVal` recomputes `Rep.ctx` per matrix (×3).

### 3.2 At `97d578b`, with and without CF (the plan still on the sparse route)

Build trees: `logs/fr-build-CF` (HEAD + CF), `logs/fr-build-CFH` (pure HEAD snapshot). Final build
`lake build FR Solution FRSubmission4Fin plan4t vtime4 cfrs FRNodeRows4RepCFP FRNodeRows4RepLCtrl`
**green, 5,076 jobs** (`logs/CF/cf8.log`).

| | HEAD `97d578b` | HEAD + CF | log |
|---|---|---|---|
| `plan4t init` (core 29, alternating, 2 rounds) | 19.8 / 22.3 s wall, **18.3 s user**, 2.03 GB | 21.9 / 23.6 s wall, **20.9–21.1 s user**, 2.07 GB | `plan4t-init-ab.log` |
| V(N4) own kind, best / median (21 runs) | 1,900.7 / 1,949.9 ms (core 31) | 1,916.3 / 1,988.1 ms (core 29) | `vtime-head.log`, `vtime-cf.log` |
| `evalMT4` N4 best | 1,862.8 ms | 1,837.5 ms | idem |

**CF alone is a small regression (+2.7 s init, V ±1 %) until it is wired into the plan** (§6 step 1): the
plan still materialises the (now 33 k rows larger) template, and building `rsGS` costs 1.26–1.50 s per
kind (R3's `rsG` ≈ 1 s): the var placeholders' arrays rebuild a pattern per (instance, stage) pair
(`SM.rep`'s result closure re-runs `pat 0`; let-bind it, cache each chain's result list). Once wired, the
replay value's `rsWeight` part is the closed form (§3.1: ≈ 85 ms per kind per matrix now, ≈ 25–30 ms per
kind for all three after §6 step 3), and none of its ≈ 505 k rows is built, fit-checked, split or grouped
at start-up (REPF measured ≈ 3.9 s of `arRepOf` and ≈ 2.8 s of fit/split/grouping on all 846 k rows).
V(N4) has grown since REPF (1,785 → 1,901 ms) through FOLD2's ask rows, not CF.

## 4. Kernel / hygiene

- **Axioms** (`logs/fr-build-CF/ax/AxCF.lean`, `logs/CF/axioms.log`): `Rep.eval_eq`, `sgVal_eq`, `SM.ok_rep`,
  `ok_rsGS`, `kRS_ok`, `psVal_eq`, `psLocOk_rows`, `kopV_eq`, `arBlk0_eq`, `rowsVal_locF/L`, `cb_ctl`:
  all ⊆ {propext, Classical.choice, Quot.sound}.
- **Source rule**: `submissions/flock-recursive`, 466 files, **0 findings**.
- No `sorry`, no `decide` on large data; all proofs symbolic. Kernel CPU per module not profiled
  (elaboration of `FRNodeRows4RepCFRs` ≈ 30 s wall, `FRVIRTplCF` ≈ 7 s, `FRNodeRows4RepCFP` ≈ 10 s on
  the build log).

## 5. `evalL` (not started): recommended structure

C1b §6.1's carry split, taken to its end: `Σ_{j<nJ} eq(rL, σ·nJ + j)·eq(r4_lo, 299 + j)` is a shifted
diagonal sum of two `eq` functions; **a carry automaton** (LSB first; states: the two addition carries and
the count's carry, 8 values per level) computes it in ≈ 20 levels × 20 gates ≈ 400 gates per slot, with no
tables; `Σ_{i<N} eq(rL, i)` likewise (≈ 80 gates). Template ≈ 400·vslots + 500 rows per kind
(≈ 8–10 k kind-muxed, from 319.5 k). Proof: the automaton's value lemma (by induction on the level:
`S_l(cA, cB, cn) = Σ_{j < ⌊n/2^l⌋ + cn} eq_l(⌊A/2^l⌋ + cA + j)·eq_l(⌊B/2^l⌋ + cB + j)`, the even/odd
split), then `tplEvL_ok`'s statement re-proved. `Rep.gN_spl`/`gN_split` are the needed `eq` facts.

## 6. Handover (in order)

1. **Wire the evaluator into the plan** (`FRNodeRows4Plan`, mine): `planOf4D` takes `arBlk0` instead of
   `arRepOf 0` for prototype 0 (`arRepOf 1` stays); `rgF/rgL` become the grouped rows of the `.sp` blocks
   only, at their offsets (offset of a block = Σ earlier lengths; an `.rs` block's length is
   `kpLen (kpOf …)` = `Σ nr + |mux| + |copy|`, or `|alt|`: lemma to add); new fields `kps : List (ℕ × KP)`
   with `hkps`; `rvOf` adds `Σ kopV` (frame: `w = wF`, `lam = 0`; local: `w = wL`, `lam = 1`; `hw`
   holds since `cbRS = repB + 2^16`); `rvOf_get`'s statement is unchanged: prove it from
   `rowsVal_locF/L` at `X = 0`, `rm_append` over `arBlk0.2.flatMap`, `rowsVal_append` for the sparse
   part, `kopV_eq` for the `.rs` blocks.
2. **`RepFit` without the rows**: `inR`'s `repFitB 0 rl0` becomes `(Σ lengths ≤ 2^20) && (.sp blocks:
   cells) && (.rs blocks: kpFit)`, `kpFit` = `ok` → one/ins cells `repCellOk 0`, `psLocOk nl_j` per
   sub-template, `Σ nl ≤ 2^20 − 2^16`, mux rows' locals, copy rows' cells; `¬ok` → `alt`'s cells. The
   lemma: `psLocOk_rows` + `rowLocLt_sub` for the kmux substitution + instLin's cells (one, ins, `cb + k`).
   It is sound and incomplete; the fallback (`rp0`) stays.
3. **Speed** (measured costs §3.1): one `Rep.ctx` per group per call for all three matrices (an `F3`
   pass); `Z` lazily per (placeholder, carry) (thunks); the chain-read placeholders in closed form
   (their forms are chain-group locals at stride `2^8`: `Σ_s T(s+c)·eq(u, H + i·2^8 + 2s + δ)` splits at
   bit 8 into `Σ_κ eq_hi(H' + i + κ)·V(c, δ, κ)`, `V` shared by all chains) — that removes almost all of
   group A/B's cost. The blocks-once rows (≈ 11–13 k per kind) stay sparse; group them with the other
   `.sp` rows (`grows`) rather than `tmG`.
4. `evalL` (§5); then `targetS`/`linkWAll` if V still exceeds ≈ 0.7 s.
5. INIT's proposal 2 (`compMSXA` fusion) for `trailMB` too; `planData4` `noncomputable`.
6. A/B at the HEAD of the day (V `abv.sh`-style alternating, `plan4t init` best of 3), MxKat with REPF's
   reference (`logs/fr-build-REPF`), `plan4t check` N2/N4, axioms, source rule, kernel CPU per module.

## 7. Files (absolute paths under `/home/devops/Verified-zkEVM/recursion.fast-submissions-rev44/submissions/flock-recursive/lean/`)

New: `FRVIRTplCF.lean`, `FRVIRTplCFE.lean`, `FRNodeRows4RepCFRs.lean`, `FRNodeRows4RepCFP.lean`.
Edited: `FRNodeRows4Defs.lean`, `FRNodeRows4RepRsK.lean`, `FRNodeRows4RepLCtrl.lean`.
Probe (build tree only): `logs/fr-build-CF/probe/CFRs.lean`.
