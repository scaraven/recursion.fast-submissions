# R0 (track R-OPS): RESULT — the cell audit of the public-op route

Stage R0, 2026-10-29. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `6d1a933`, plus the
review `9cfb96e`). This audit edits no Lean or prover sources and commits nothing. Scripts, probes and
logs are under `logs/R0/`. Every lake, lean and probe command ran in a 16 GB scope with a timeout.
It answers R-OPS §8's R0 row and the six review items routed by the orchestrator
(`reviews/R-OPS-review.md`).

## 0. Verdict

| Item | Result |
|---|---|
| `N′`, plain | **168**, confirmed cell by cell on the RSV2 dump (all distinct and disjoint from `rsvRel`'s 60 cells). |
| `N′`, with `tdot` | **106** real cells (+2 pad = **108**), confirmed. With `tdot` and `ldot`: 100 (must be padded to 104, see §3.3). |
| B′'s row `70 + N′ ≤ 239` | `tdot`: **176** (pads asserted zero) or 178 (pads point-claimed). Plain: 238, margin 1. `εR = 15/2^124` holds in both. |
| `fLrEnd`, `\|π\|` | `tdot`: 1,008 → **2,736 B**, `\|π\|` 876,304 → **878,032** (+1,728), stream `64·24,263`. |
| N8's H | `tdot`: `hEnd` 195,228 → **195,444** ≤ 195,584 (margin **140** blocks). Plain: 195,564 (margin **20** < 64: plain trips R-OPS's N8 kill line). |
| Kill criterion | **Not triggered.** With `tdot`, `N′ = 108 ≤ 169` and the N8 margin is 140 ≥ 64. No exit needed. R1 can start with `tdot`. |
| New constraints for R1 | (a) `tt`'s N2 repack is an **erase at position 17**, not a `take`. (b) The `targetS`/`tdot` size tag **20 collides** with the own call (Z1's `pt` has 20 entries). (c) `N′ ≡ 0 (mod 4)` is required (`strideB_eq`), and **N4's `hEnd ≤ lBase` fails at `N′ = 100`**. (d) `kindOfElem` returns `none` on junk; V(P) should reject explicitly. |
| V cost (VM, best) | Child N2 / N4 / N8: `evalL4I` 8.2 / 11.0 / 15.3 ms, `tdot` 2.4 / 2.6 / 2.8, `linkWAll4I` 1.7 / 1.8 / 1.8. The `finPf` weights for 108 more cells are ≈ 1.8 ms (estimate). **ΔV ≈ 14 / 17 / 22 ms**, against the memo's 15 and R1's 25 ms kill line. |

## 1. Method and sources

- **The dump.** The inventory comes from `logs/RSV2/dump/group-N.txt`, the kind-muxed node program
  that slot 0 replays, with 154,920 ops. In that file kind `L` is N4, `P` is N2 and `N` is N8: the
  seed's constant `r3` is `4e20…` / `4d1f…` / `4f20…`, i.e. `NodeKind.byte ‖ m`. The register → cell
  map is `logs/RSV2/nodedump/mregs-p0.txt` (prototype 0, M-relative cells). Both are RSV2's dumps,
  and RSV-S3/C1 changed neither program.
- **The script.** `logs/R0/r0cells.py` (log `r0cells.log`, cells `cells.json`) does the following:
  1. It finds the unique `targetS`, `lagrangeS`, `linkWAll`, `evalL` and `evalM` ops.
  2. It reads each operand's per-kind register list from its `packF`/`packFK` line.
  3. It takes the union over the three kinds.
  4. It checks that every register in the union is one `F` cell with coefficient 1 in `mregs-p0`.
  5. It lists each register's defining op.
  6. It checks that the cells are distinct and disjoint from RSV-V2's `rsvRel`, which it rebuilds
     with `rsvcells.py`'s rule.
- **The fit.** `logs/R0/probe/R0Fit.lean` and `R0Fit2.lean` evaluate `piSizeOf`, `streamBytesOf`,
  `chainLenOf`, `hUsed`, `hEnd`, `lBase` and the N8 bound. They use `seq4` with
  `lrEnd := 1,008 + 16·n` and ran via `lake env lean` in `logs/fr-build-RSVS3`. Logs: `fit.log` and
  `fit2.log`.
- **V.**
  - **The probe tree.** `logs/R0/fr-build-R0` is a copy of `logs/fr-build-B4`'s sources and `.lake`
    (`ir`, `lib`). The 9 symlinked sources were replaced by their `HEAD` content. B4's tree is the
    newest V build (`7537acd`).
    - Its V path is HEAD's: across the 137-module import closure of the probe, the only source
      differences from `HEAD` are proofs in `FRNodeCircuit4`, `FRSoundness4Qry` and
      `FRXChainFlock`. No `def` differs.
    - `lake build r0ops` rebuilt nothing: 4,703 jobs, only the probe compiled.
  - **The standalone probe.** `probe/R0Ops.lean` times each op once per repetition, round-robin
    (alternating), with all inputs depending on the repetition index so that no closed term is
    hoisted. It ran on core 30 at load 4.9–6.2 of 32 cores, 15 repetitions, twice (`ops-1.log`,
    `ops-2.log`).
  - **In context and baseline.** The in-program profile is B4's `vtime4 prof 5 n4f`
    (`prof-b4-1.log`). The V(N4) baseline is `vtime4 21 n4f [s4]`, alternating, 2 rounds
    (`vtime-base.log`).
  - **The term rate.** The per-term rate is C1's `repv check`, re-run (`repv.log`).

## 2. The inventory (prototype 0, the child's program)

Every operand register below is a `chF` of a squeeze answer: the `chF`/`chK` class of PACK §1.3,
aliased to the answer halves by B3's `ATImp`, which is the same class as `rsvRel`'s 60 cells. Each
is one `F` cell with coefficient 1, and none is a mux cell (§4.1).

| Carried | Registers (group line) | Cells (M-relative) | Per kind N4 / N2 / N8 | Union | N2's positions from the union |
|---|---|---|---|---|---|
| `evalL`: `rL` (Lr2's point) | `r1236 … r1492` step 16 (packFK → `r57122`, line 65,691) | 1077 … 1253 step 11 | 17 / 16 / 17 | 17 | positions 0–15 (`take 16`; position 16 = `r1492` is squeezed at every kind and unread at N2) |
| `evalL`: `r4` (E4's point) | `r1925 … r2224` + `r2237` (packFK → `r57149`) | `p_y`'s 1579 … 1809 + **1819** | 25 / 24 / 25 | 25 | 0–23 |
| `evalL`: out | `r57157 r57158 r57159` | 116492–116494 | 3 | 3 | — |
| `targetS`: `pt` (Z1) | `r16 r17 r19 r20 … r44` (packF → `r45`, AF20, line 51) | 21, 22, 25, 26, …, 54, 57 (first 19 of 20) | 19 / 18 / 19 read (`zLo` = `r[0]`, `rbOf4` = `r[1 … nb]`) | 19 | 0–17 |
| `tdot`: `λ` (Z2) | `r49` (`chF r48 0`, line 55) | 63 | 1 | 1 | — |
| `targetS`: out | `r178` (AF64, line 184) | 191 … 254 | 64 (→ 1 new cell `t` with `tdot`) | 64 | — |
| `linkWAll`: `tt` (S1 `τ ‖ θ`) | `r792 … r817, r819 … r832` (packFK → `r57080`, line 65,648) | 696, 697, 700, …, 749 | 28 / 27 / 28 | 28 | **erase position 17** (`r817`, cell 729): N2's τ is positions 0–16 and its θ is 18–27 |
| `linkWAll`: `rr` (S2) | `r843 … r1194` step 13 (packFK → `r57081`) | 760 … 1030 step 10 | 28 / 27 / 28 | 28 | 0–26 (`take 27`: N2's `r_pos` starts at union position 17) |
| `linkWAll`: out | `r57082` (AF8) | 116446–116453 | 8 | 8 | — |
| kind element | `r2` (`piElem 0 0`) | **6** | 1 | 1 | — |

**`r4` sharing.** `evalL`'s `r4` equals `p_y`'s registers at positions 0–23 for every kind. At N4/N8
its 25th entry is `r2237` (cell 1819). The 25th entry of `rsvRel`'s `p_y` is the mux register `r57287`
(cell 116600): `r57287 = r57245 · getF(packFK {N4: r2237, N2: r57217, N8: r2237})`, where `r57245` is
`const 1` at every kind. It equals `r2237`'s value only through the compiled mux and `mulF` rows. Two
options:

- Rely on those rows. They are skeleton rows (`SlotRows`) and they hold.
- Or carry cell 1819 too. This is **free**: 106 + 1 = 107 pads to the same 108 (recommended: the
  binding then needs no mux lemma).

**Totals.**

| Variant | Cells | Padded (`≡ 0 mod 4`) | Check |
|---|---|---|---|
| plain: `rL` 17 + out 3 + `pt` 19 + out 64 + `tt` 28 + `rr` 28 + out 8 + kind 1 | **168** | 168 | distinct, disjoint from `rsvRel`: PASS |
| `tdot`: `pt` 19 + `λ` 1 + `t` 1 replace `targetS`'s 83 | **106** (107 with cell 1819) | **108** | PASS |
| `tdot` + `ldot` (8 outs → `Σ_f κ_s^{f+2} w_f` + `κ_s` = `r834`) | 100 | **104** (100 fails N4, §3.3) | — |
| plain + `ldot` | 162 | 164 | — |
| `tdot`, `linkWAll` kept on C1's rows | 42 | 44 | — |

The memo's 168 and 108 are **confirmed**.

## 3. Field length, error row, fit

### 3.1 B′'s row (`coord_le_deltaR`: `c ≤ 239`; today `single_B4` is `Fin 71`, row 70 = 1 + 9 public + 60 reserve)

| `N′` (cells in `J_f`) | `J_f` | B′'s row | ≤ 239 |
|---|---|---|---|
| 168 (plain) | 237 | 238 | yes, margin 1 (169 with cell 1819: 239, margin 0; padding to 172 then only works if the pads are zero-asserted, not claimed) |
| 106 (`tdot`; pads zero-asserted) | 175 | **176** | yes |
| 108 (`tdot`; pads claimed, the memo's count) | 177 | 178 | yes |
| 100 (`tdot` + `ldot`) | 169 | 170 | yes |
| 185 (ceiling at `εR = 16/2^124`) | 254 | 255 | — |

The pad cells need not be point claims. If they are zero-asserted (`assertZero (piField fLrEnd …)`,
as `fEEnd[64,112)` today) they are not in `J_f`.

### 3.2 Format (`R0Fit2.lean`, `fit2.log`)

| `N′` | `lrEnd` | `\|π\|` | stream bytes | `chainLenOf` | N2 `hEnd`/`lBase` | N4 `hEnd`/`lBase` | N8 `hEnd`/`lBase`/bound | N8 margin |
|---|---|---|---|---|---|---|---|---|
| 0 (today) | 1,008 | 876,304 | 1,551,104 | 24,236 | 74,017 / 74,240 | 122,501 / 122,624 | 195,228 / 195,328 / 195,584 | 356 |
| 104 | 2,672 | 877,968 | 1,552,768 | 24,262 | 74,095 / 74,240 | 122,631 / 122,880 | 195,436 / 195,584 | 148 |
| **108** | **2,736** | **878,032** | 1,552,832 | 24,263 | 74,098 / 74,240 | 122,636 / 122,880 | **195,444** / 195,584 | **140** |
| 144 | 3,312 | 878,608 | 1,553,408 | 24,272 | 74,125 / 74,240 | 122,681 / 122,880 | 195,516 / 195,584 | 68 |
| 168 (plain) | 3,696 | 878,992 | 1,553,792 | 24,278 | 74,143 / 74,240 | 122,711 / 122,880 | 195,564 / 195,584 | **20** |
| 176 | 3,824 | 879,120 | 1,553,920 | 24,280 | 74,149 / 74,240 | 122,721 / 122,880 | 195,580 / 195,584 | 4 |
| 180 | 3,888 | 879,184 | 1,553,984 | 24,281 | 74,152 / 74,240 | 122,726 / 122,880 | 195,588 > 195,584 | **fails** |

- Each 4 cells add one block per proof, 8 blocks to N8's H (two 4-segment aggregates).
- **N8's ceilings:**
  - fit: `N′ ≤ 176`;
  - the margin ≥ 64 kill line: `N′ ≤ 144`.
  - The memo's "178" ignores alignment.

### 3.3 Two constraints the memo does not state

- **`N′ ≡ 0 (mod 4)`.** At `N′ = 106` and 107 the stream is `≡ 32` and `≡ 48 (mod 64)`, so
  `strideB_eq`'s `segB = 64·cLen` fails; at 107 the 2-segment aggregate is not whole blocks either
  (`fit.log`). Hence the padding.
- **N4's tail crosses its `lBase` at `N′ = 100`.**
  - `hUsed` is 122,622, so `lBase = ⌈hUsed⌉₂₅₆ = 122,624`, while `hEnd = hUsed + 4 = 122,626`. That
    breaks `hEnd_le`.
  - The window is `hUsed ∈ (122,620, 122,624]`. `N′ = 96` and 104 are clear. `tdot + ldot` must
    therefore pad to 104, not 100.
  - Any future `N′` should be re-run through `R0Fit2.lean`.

## 4. The review's items

### 4.1 Operand binding

At every child kind each operand position is a `chF` register: §2's "defining op" column, from
`r0cells.log`. The group program is one op list for all kinds, so every `chF` and its squeeze run at
every kind. A kind only selects which registers its `packFK` reads.

- **The binding is the `chF` alias.** It is the same as for `rsvRel`'s `p_x`/`p_y` registers:
  PACK §1.3's "challenge conversions `chF`/`chK` → answer halves", proved as one `ATImp` summand of
  B3's ask template (`B3-RESULT` §2; IMP-RESULT item 3, **not yet built**). The answer is the squeeze
  item's answer, which `ATAsk`'s FS links tie to the transcript. In `SlotImpR` these registers are
  imports today, as `rsvRel`'s are, and they leave `impRP` exactly when the `chF` summand lands. The
  public-op route adds no new import class.
- **No mux cells are needed.** The kind-muxed `packFK` operands (`r57080`, `r57081`, `r57122`,
  `r57149`) are **untracked** in `mregs-p0`: no cell exists. Carrying the **union** of the three
  kinds' registers, at most 28 per operand, needs no mux cell. V(P) repacks by the child's kind:
  - for N2, `rL.take 16`, `pt` positions 0–17, `rr.take 27`, `r4.take 24`, and **`tt.eraseIdx 17`**;
  - for N4/N8, the full union.

  `linkWAll4I N2` reads `tt[0,17)` as τ and `tt[17,27)` as θ, so a `take 27` would read `r817` as θ₀.
  That would be a silent wrong value, caught only by the (−) control. **R1 must implement the erase
  and add a control with an N2 child.**
- **The one register with a mux is `r4`'s 25th entry.** It is handled in §2: carry cell 1819, which
  is free.

### 4.2 Kind element

- **The chain.** The kind cell is cell 6, which holds `r2 = piElem 0 0`, the child's header element.
  The child's program asserts `assertEq r2 r3 {all}` (group line 5), where
  `r3 = const {N4: 4e20…, N2: 4d1f…, N8: 4f20…}` compiles to `Σ_ι sel_ι·kConst_ι` over the selector
  cells 1–3 (`mregs`: `r3 = 1:4e20 2:4d1f 3:4f20`).
- **The rows.** `FRVIRCompile.compile`'s `.assertEq` emits the row
  `gate·(cell 6 − Σ_ι sel_ι·c_ι) = 0` (`FRVIRCompile.lean:445`, gate `allK`). The selectors are tied
  to the slot's H kind byte by `kindRow` (`FRNodeRows4Pack.kindRow`, `FRNodeRows4PackSound.kindRow_sel`:
  `w h5 = kConst G ι` for the selected `ι`). `SlotImpR`'s `SelOk` makes the selector one-hot.
- **What follows.** For the `ι` that `SlotImpR` quantifies over, cell 6 = `kindElemN ν_ι`. Then
  `kindOfElem (cell 6) = some ν_ι`, the kind whose `implP … ι` produced the op outputs. That is the
  memo's step (3). B′/`PubCellsR4` ties the carried value to cell 6.
- **Junk.** `kindOfElem` (RSV-V's, `logs/fr-build-B2pp/src/FRVerifierImplNode4F.lean:251`, deleted
  in RSV2) is `[N2, N4, N8].find? (kindElemN · = x)`: **`none` on junk**. RSV-V's dispatch then
  *quietly* returned `(0,0,0)` (`evalMD4`, `evalMD4_ctl`'s fourth conjunct). On an accepted run the
  rows make junk impossible, so that is sound. **Recommended for R1**: on `none` the ops' asserts
  fail. Gate the `rsvOps2` asserts by "`kindOfElem kind ≠ none`", or have the dispatch return a value
  that fails `assertEq`. The (−) control "a wrong kind element" then fails V and not only
  `kindElem_sel`.
- **N8 parent.** N8 has no previous slot. Its `fLrEnd[48, …)` zero assert (`assertZero piField 6512
  960`, active at `N` only) must widen to the new length. The kind cell is then 0 and
  `kindOfElem 0 = none` (RSV-V's control).

### 4.3 Padding and tags

| Item | Does the op read it? | Needs a zero assert? |
|---|---|---|
| N2's `rL` position 16 (`r1492`, cell 1253) | No: `evalL4I` reads `rL` only through `bt κ.dims.logL rL` (`logL` = 16 at N2) | No. It is a bound `chF` value at every kind, not free prover data. |
| N2's `pt` position 18, `tt` position 17, `rr` position 27, `r4` position 24 | Not after the repack (§4.1) | No (bound `chF` values) |
| `pt`'s 20th entry (`r44`, not carried) | No: `targetSNode4S` reads `r[0]` and `r[1 … nb]`, at most 19 entries | — |
| the 2 pad cells (1 with cell 1819) | — | **Yes** (they are free bytes of `fLrEnd`): `assertZero` on their `piField`, as `fEEnd[64,112)`. Then they need not be point claims (§3.1). |
| `evalL`'s third output (`r57159`, cell 116494) | V(C) consumes it (`mulF r57161 r57159`, line 65,732); `evalL4I`'s third component is the literal `0` | Its cell is an op import, so it must be bound. Either carry it (V(P) asserts `= 0` through the recompute; counted in the 3) or bind it by one replay row `cell = 0` (−1 cell). |

**Size tags** (own calls in the node program, one op each: `r0cells.log`):

| Op | Own call's operand sizes (N2 / N4 / N8) | Memo's tag | Collision? |
|---|---|---|---|
| `evalL` | `rL` 16 / 17 / 17, `r4` 24 / 25 / 25 | `rL ‖ kind` = 18 | no |
| `targetS` / `tdot` | **`pt` = 20 at every kind** (`r45`, packF, AF20) | `pt (19) ‖ kind` = **20** | **yes**. Use 21 (carry `pt`'s 20th cell too, or tag at a size the own call never has), or put the tag on another operand. The lemma "no own call has the tagged size" must be stated per op. |
| `linkWAll` | `tt`, `rr` 27 / 28 / 28 | `tt ‖ kind` = 29 | no |
| `evalM` (RSV2) | `τ` 22 / 23 / 23 | 32 | no |

Since `tdot` is a new `Op`, its child call could also dispatch on a distinct op (e.g. `tdotC`) rather
than on a size. That would avoid the tag entirely.

### 4.4 `tdot`

- **Programs.** In the node program the target values `r178` are read only by `lagrangeS r177 r49
  r178` (line 185; `grep` finds no other use). In the segment program `r271` is likewise read only by
  `lagrangeS` (`group-S.txt` line 277).
- **Soundness.** The verifier's `targetS` output enters only through the Z3 head bridges
  (`R4FrZ.z3_head_seg4`/`z3_head_node4` via `hpe`/`hTS`, `R4Rnd`'s `lagrangeS` value, and `R4Ref`'s
  register file). Elsewhere `peL` is the *specification* `Σ_u eq(r,u)·E(σ,u)` (`P4aNames.peL`), not a
  V output:
  - `Z2D`'s doom (`z2_single4`'s `hb` at a node `b`);
  - `skip_pair_bad_le`;
  - `c0Z = interpolateAt node127 (z2Vals pz pab pe) λ`.

  `z2Vals` adds `pe_b` at `b < 64` and `interpolateAt` is linear, so
  `c0Z = interp(z2Vals[pe := 0], λ) + Σ_{b<64} ℓ_b(λ)·pe_b`. That is an identity: the dooms and their
  counts are unchanged, and only the bridges' `hTS` hypotheses take the dot form. **Confirmed.**

### 4.5 The kill criterion, corrected

- **The real exits.** §5.3 adds 94 cells, so it is not an exit for `N′ > 169`. The exits are `ldot`,
  keeping `linkWAll` on C1's rows, and `εR = 16/2^124`.
- **Against 169:**
  - plain 168, margin 1;
  - plain + `ldot` 162 (pad 164);
  - `tdot` 106 (pad 108);
  - `tdot` + `ldot` 100 (pad 104);
  - `tdot` with `linkWAll` on C1's rows 42 (pad 44);
  - and up to 185 under `εR = 16/2^124`.
- **Verdict.** All are ≤ 169. With the N8 margin line (≥ 64 blocks, so `N′ ≤ 144`), only the plain
  variants fail, at 20 blocks (168) and 28 blocks (164). **`tdot` (108) is the choice. No exit is needed.**

### 4.6 `rsWeight`

- **Rate (re-measured, `repv.log`):** **0.29–0.33 µs per term**, 1.34–1.51 µs per row (§5.3).
- **Direct op (this audit):**
  - `rsWeightF4` (4 claims, F-point fast path) is **9.1 ms at N4 and 8.5 ms at N2** standalone.
  - It is 9.6 ms in V(N4)'s profile.
- **Template estimates at the measured rate (0.29–0.33 µs per term):**

  | Form | Size | V |
  |---|---|---|
  | as sparse rows (PACK §6.2: 45.6 k claim rows + 68.5 k kind-factor rows ≈ 114 k rows, ≈ 4.6 terms/row as in C1's `tplLW`) | ≈ 525 k terms | **≈ 150–175 ms** |
  | as closed-form chains, the memo's 20–25 k products | — | **≈ 5.8–8.3 ms** |
  | the chains plus the review's ≥ 12.8 k wiring terms | ≈ 33–38 k terms | **≈ 9.5–12.5 ms** |

  The last figure is at or above V's own direct op cost (9.1 ms). R4's kill line is 10 ms for slot
  0, so it is marginal. The memo's 1–3 ms needs `O(log)` closed forms for the wiring too.
- **Witness cells.**
  - **Slot 0.** C1's `tplLW` has gates = locals = rows (13.8–14.4 k), so ≈ 114 k rows means
    ≈ 114 k F locals. At most 2× that holds if K locals take two cells (`Ty.len .k = 2`), so 114–228 k
    cells. Slot 0's template goes to the spare M region `vslots·2^20 + j` (C1's placement): N2 has
    1 spare region of 2^20 and N4 has 3. C1's `tplLW` uses 42.6 k cells there, and R-OPS retires it.
    **228 k + 42.6 k ≤ 1,048,576: fits** (≈ 26 %), rows likewise.
  - **Segment slots (R5).** N8 has no spare region (8 of 8 slots). In-slot, prototype 1 has
    259,925 free cells, 164,006 of them contiguous below the lowest instance (`RSV2/cellfit.log`).
    Its rows have only ≈ 34.8 k free rows before arena₂'s binding rows plus ≈ 90 k above the bits
    (`RSV2/arenafit.log`: last row 686,079, binding `[720,896, …)`, bits end 958,592). A
    114 k-row template **does not fit contiguously** in a segment slot's rows. That is R5's problem
    and does not affect R1–R4.

## 5. V measurements (VM, rev44's compiled verifier; core 30, load 4.9–6.2 / 32)

### 5.1 Standalone, alternating, best of 15 (two runs agree within 0.5 %; `ops-1.log`, `ops-2.log`)

| Op | child N2 | child N4 | child N8 |
|---|---|---|---|
| `evalL4I` | **8.18** (median 8.49) | **10.99** (11.33) | **15.31** (15.92) |
| `targetSNode4I` | 1.58 | 1.73 | 1.90 |
| `tdot` = `targetSNode4I` + 64 Lagrange weights at the child's `λ` + dot | **2.44** | **2.61** | **2.76** |
| `linkWAll4I` | **1.70** | **1.79** | **1.82** |
| `rsWeightF4` (4 claims, F-points) | 8.52 | 9.11 | — |

| Own-kind op | best |
|---|---|
| `lagrangeSI` (own `lagrangeS`) | 2.70 |
| the `tdot` fold alone (64 weights via `numL`, 126 products each, + dot) | **0.90** |

- **The `tdot` fold costs 0.9 ms, not the memo's 0.1.** `lagW` builds each weight as a 126-term
  product. A barycentric form, `ℓ_b(λ) = Π(λ − x_j) · den_b / (λ − x_b)` with one batched inversion,
  is ≈ 0.02 ms. That is a lever for R1.
- **In context** (V(N4)'s own program, `vtime4 prof 5 n4f`, per op): `evalL` 11.56, `rsWeight` 9.62,
  `lagrangeS` 2.92, `targetS` 1.99, `linkWAll` 1.88, `shiftTarget` 0.26 ms. This matches INT-9's
  profile within 0.5 ms.

### 5.2 ΔV of the route (per child kind; VM ms)

| Term | N2 child | N4 child | N8 child | Source |
|---|---|---|---|---|
| `evalL4I ν_C` | 8.2 | 11.0 | 15.3 | measured |
| `tdot ν_C` | 2.4 | 2.6 | 2.8 | measured (−0.85 with barycentric weights) |
| `linkWAll4I ν_C` | 1.7 | 1.8 | 1.8 | measured |
| `finPf`'s weights for 108 cells (`gCellOpsK`: 25 `keep` + 25 `mulK` + 3 per cell) and B′'s Horner, `piElem` exports | ≈ 1.9 | ≈ 1.9 | ≈ 1.9 | estimate from the profile's per-op means (`mulK` 0.47 µs, `keep` 0.16 µs, `piElem` 0.92 µs); memo: 0.2 |
| **total** | **≈ 14** | **≈ 17** | **≈ 22** | |

- **Against the budget.** The memo's ≈ +15 ms holds for an N4 child. An N8 child (the
  `N8 → N4` step of `RsvKat`'s chain) costs ≈ 22 ms, within R1's 25 ms kill line by ≈ 3 ms. The
  levers, in order:
  1. R6's `evalL` carry automaton: −15 at an N8 child;
  2. barycentric `tdot` weights: −0.85;
  3. a shared `eq(·, ρ)` table for `finPf`'s cells: ≈ −1.5.
- **Baseline at HEAD's V** (`vtime-base.log`, 2 alternating rounds, best of 21): V(N4) **270.7 ms**
  with an own-kind child support (`s4`) and **314.0 ms** with all kinds; `evalMT4` N4 147.2 ms.

### 5.3 The per-term rate (C1's `repv`, re-run)

Re-run of C1's `repv check` (`logs/fr-build-C1`'s binary: the evaluator `grows 2048 4096` +
`growsVal3` is unchanged since C1). The run was on core 30, load 6.2 / 32, 6 min 27 s
(`logs/R0/repv.log`). It replays slot 0's 42,601 rows and 196,410 terms (C1's `tplLW` rows).

| | `growsVal3` best / median | per term (best) | per row (best) | `evalMT4` same process |
|---|---|---|---|---|
| N2 | 56.9 / 69.7 ms | **0.290 µs** | 1.34 µs | 153.8 ms |
| N4 | 64.1 / 67.3 ms | **0.327 µs** | 1.51 µs | 171.1 ms |

The measured rate is **0.29–0.33 µs per term**, about 8 % above C1's 0.27–0.31.

- The KAT `growsVal3 = rows3` passes.
- An earlier run on core 28 (`repv-core28-contended.log`) was uniformly 2.2× slower, including
  `evalMT4`. The core was contended, so that run is discarded.

## 6. For R1 (deviations from the memo, all small)

1. Carry the **union** registers, not muxed arrays. The N2 repack is `take` everywhere except
   `tt.eraseIdx 17`. Add a (−)/(+) control with an N2 child.
2. Carry cell 1819 (`r2237`) as `r4`'s 25th entry (free under the padding), or prove the
   `r57287 = r2237` mux equality.
3. `tdot`'s child tag must not be 20. Use 21, or a distinct op.
4. Pad to `N′ ≡ 0 (mod 4)` and zero-assert the pads. Re-check N4's `hEnd ≤ lBase` window for any
   `N′` other than 108 (`R0Fit2.lean`).
5. `kindOfElem = none` must fail V(P)'s asserts.
6. `evalL`'s third output: carry it (asserted 0) or bind it by a one-row replay template.
7. Price `finPf`'s per-cell weights at ≈ 17 µs per cell. Prefer barycentric `tdot` weights.

## 7. Logs and scripts (`logs/R0/`)

| File | What |
|---|---|
| `r0cells.py`, `r0cells.log`, `cells.json` | the inventory (per register: cell, import flag, defining op), checks, repack positions |
| `probe/R0Fit.lean`, `probe/R0Fit2.lean`, `fit.log`, `fit2.log` | field length, `\|π\|`, stream, `hUsed`/`hEnd`/`lBase` per kind at `N′` |
| `fr-build-R0/probe/R0Ops.lean`, `build-r0ops.log`, `ops-1.log`, `ops-2.log` | standalone per-op V |
| `prof-b4-1.log` | B4's `vtime4 prof 5 n4f` (in-program per-op profile) |
| `vtime-base.log` | V(N4) baseline, own-kind and all-kinds supports |
| `repv.log` | C1's `repv check` re-run (per-term rate) |
| `repv-core28-contended.log` | the discarded first `repv` run (contended core, uniformly 2.2× slow) |
| `closure.txt` | the probe's import closure (the V-path equality check against `HEAD`) |
