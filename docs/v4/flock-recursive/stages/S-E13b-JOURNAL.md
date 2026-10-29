# S-E13b JOURNAL: the WOTS rows, `aggChk`, `aggPad` (Gap4's `wots`, `aggChk`, `aggPad`)

Base: HEAD `75eff21` (S-N2). Build tree `logs/fr-build-SE13b` (a copy of `fr-build-SE12f`, `snap.sh`
against `logs/org20`). Logs: `logs/S-E13b/`. 16G scope, `timeout` on every build. No sub-agents.

## 0. Design note (item 1): rows, regions, cells, cost

### 0.1 Where the rows go (allocation; S-E13a please avoid)

- **Modules (new):** `FRNodeRows4Wots` (the rows' definitions and their row-level lemmas),
  `FRNodeRows4WotsS` (the soundness: a 4.1 `wots_sound` and `Gap4.wots`'s discharge),
  `FRNodeRows4Agg` (the `aggPad` rows and `Gap4.aggPad`'s discharge; `aggChk`'s part).
  Namespace **`FR.W4`**.
- **Folding.** `nodeIRows4`'s shape is fixed by `FRNodeSound4*` (they unfold it to
  `flatMap (slotRows4 ++ linkIRows4)` and use `linkIRows4 = (linkRows4 κ σ).zipIdx.map (f ·, ·.1)`
  for any index map `f`). So the new rows are appended to **`linkRows4 κ 1`** (slot 1 exists for
  every kind and is a segment slot) and `linkIRows4` maps link row `j ≥ 8` to the region-1 slack.
  `lRows4` is frozen (`FRSoundness4XFront.lRows4_fit` and `FRVerifierImplNode4F`'s closed-form
  `evalL` unfold it); no new L rows.
- **M row indices** (M-relative): region 1's slack, **from `2^20 + 2^19` (= 1,572,864)**:
  WOTS of signed child `σ` at `2^20 + 2^19 + σ·2^14 + j`; `aggPad` of aggregate `a` at
  `2^20 + 2^19 + 2^15 + a·2^12 + j`. (Prototype 1's rows end at `2^20 + 551,805`; link rows at the
  region's last 8.)
- **New cells: L only**, in signed child `σ`'s `2^14` L stride (`Lc σ o := lBase·128 + σ·2^14 + o`),
  past A.7's 8,519 used elements (`sig` 0–298, digits 299–564, step selectors 565–963, position bits
  964–8515, kind selector 8516–8518):
  | offset | content |
  |---|---|
  | 8704 + t, t < 16 | the index bits `b_t` of `idx` |
  | 8720 + i, 1 ≤ i ≤ 132 | the checksum running products `R_i` |
  | 8960 + 128 t + q, t < 16, q < 128 | the bits of `r_t`'s element 1 (byte 31 extraction) |
  | 11008 + 2 (j − 1) + h, 1 ≤ j ≤ 4, h < 2 | the `k`-mux terms `T_{j,h} = [k = j]·h_out(F_j)_h` |
  | 11264 + 128 (j − 2) + q, 2 ≤ j ≤ maxK, q < 128 | `aggPad`: the bits of main block `aggL j − 1`'s element 7 |
  Nothing else in L is touched. No new M cells (the rows read M's `one` and the selector copies).

### 0.2 The WOTS rows of signed child `σ` (`W4.wotsRows κ σ`)

Cells: H element `hc b e := b·128 + e` (`h_in` 0–1, `h_out` 2–3, message 4–7); WOTS blocks
`wotsB κ σ + o` (step `(i, s)`: `o = 3i + s`; leaf block `u`: `399 + u`; path `B1_t`: `466 + 2t`,
`B2_t`: `467 + 2t`); mirror source `g`: elements `mc g h := (wmB κ σ + g/4)·128 + 2(g mod 4) + h`;
`E_q := bitBasis q`; `eq(x, y)` is the row `one · (x − y) = 0`.

| Rows | Cells | Count |
|---|---|---|
| W1 index: `b_t (1 − b_t) = 0`; `idx = Σ_t E_t b_t`; `mc 399 0 = idx` (the `j` family's mirror) | L `idx`, aux | 18 |
| W2 selectors: `s₀ = (1 − b₀)(1 − b₁)`, `s₁ = 1 − b₁`, `1 − s₂ = b₀ b₁` (S-E2 F-2) | L digits, step selectors | 399 |
| W3 chain `i`: `mc(3i) = ots_i`; `mc(3i+1) − ots = s₀ (h_out(3i) − ots)`; `mc(3i+2) − ots = s₁ (h_out(3i+1) − ots)`; `mcEnd i − ots = s₂ (h_out(3i+2) − ots)`, per element | H, `WM`, L | 1,064 |
| W4 key leaf links `h_in(u+1) = h_out(u)` | H | 132 |
| W5 path `t`: `h_in(B2) = h_out(B1)`; `l − cur = b_t (sib − cur)`, `r − sib = b_t (cur − sib)` (mirrors 533+t, 549+t); **byte 31 of `r`**: the 128 bits of `mc(549+t) 1`, Boolean, and `mc(565+t) 0 = Σ_{q<8} E_q β_{120+q}` | H, `WM`, L | 2,176 |
| W6 root `h_out(B2_15) = vk` (`seedC κ σ 0/1`, pinned by `PubCells4`) | H | 2 |
| W7 digits → the digest: `Σ_q E_q bit_{128h+q} = h_out(final)_h`; an aggregate: `T_{j,h} = ind_j · h_out(F_j)_h`, `Σ_j T_{j,h} = Σ_q E_q bit_{128h+q}`, `ind_j = S_{j−1} − S_j` (`j < maxK`), `S_{maxK−1}` | H, L, M selector copies | 2 / 2 + 2·maxK |
| W8 checksum, multiplicatively: `R_{i+1} = R_i · f_i` (`R_0 = R_133 = one`), `f_i = g^{3−d_i}` (`i < 128`) or `g^{−4^t c_t}` (the checksum digits), each linear in `b₀, b₁, s₂` (`b₀b₁ = 1 − s₂`); `ord g > 1023` makes `Σ(3 − dᵢ) = Σ 4^t c_t` | L | 133 |
| **total per child** | | **≈ 3,926** (agg. + 8) |

**Why byte 31 costs 2,048 rows.** The `r31` family (`NodeT.fam 7`) links `B2_t`'s byte 0 to
mirror source `565 + t` at bits 0–7, while `r0` puts `r`'s bytes 0–30 at source `549 + t`. The
mux works on F elements, and moving byte 31 of `r`'s element 1 (bits 120–127) to bits 0–7 of
another element is not F-linear: it needs the element's bits. **Proposed blueprint change (S-C,
P2, the verifier's `linkWAll`)**: give `r31` the source `549 + t` with `mbo = 248` (as `end41hi`
shares `end41lo`'s source at `mbo = 184`). Then byte 31 is the r mux's own output, and W5 drops to
6 rows per `t` (−4,096 rows per node).

### 0.3 `aggPad` (R-4-m2), per aggregate `a` (`σ = aggChild κ a`)

`r_j := aggB j − 64 (aggL j − 1)` is 64, 63, 62, 61 for `j = 1 … 4` (`segB − 1 ≡ 63 mod 64`), so
from `j = 2` the final block's element 7 is cut inside a byte range: its tail must be zero and its
head equal to main block `aggL j − 1`'s.
- `j < maxK`: `ind_j·(F_j's h_in − main(aggL j − 2)'s h_out) = 0` (2), elements 4–6 `ind_j·(F_j − main(aggL j − 1)) = 0` (3);
  element 7: `j = 1` equal (1); `j ≥ 2`: main's element 7 decomposed (128 Boolean + 1), and
  `ind_j · (F_j,7 − Σ_{q < 8 (r_j − 48)} E_q δ_q) = 0` (1).
- `j = maxK` (the final block is main's last): its element 7 decomposed, `ind_maxK · (main_7 − Σ_{q<8(r−48)} E_q δ_q) = 0`.
- Cost per aggregate: `N2` 136, `N4`/`N8` 406.

### 0.4 `aggChk`

`aggChecks (c_A) (n) (e) vs`:
- `c_A = leafStmt e n`: the `hashA` block `cAB κ a` computes `leafStmt` of its message
  (`hashA_leafStmt`), and `PubCells4` pins `stC` = its `h_out` halves to `c_A`'s. **No rows**: a
  theorem (D2's halves lemma).
- `1 ≤ k ≤ 4`: the activity rows and `kAct_le`. No rows.
- each `1 ≤ nᵢ ≤ cap`, `Σ nᵢ = n`, the last `h = e`, the chaining `startᵢ₊₁ = hᵢ`: these read the
  sub-slots' segment views `segView (pf trᵢ)`. With `pf` a parameter of the reader, no row can bind
  them; they need the pack map (S-E13a) that ties a sub-slot's header fields to its import cells.
  The rows themselves (over those cells) are: the chaining `S_{i+1}·(startᵢ₊₁ − hᵢ) = 0` (2 per
  pair), the last end `Σ_j ind_j hⱼ₋₁ = e` (with `e`, `n` cut out of `hashA`'s unaligned message by
  decomposing its elements 4–6: 3·128 Boolean rows), `Σ nᵢ = n` multiplicatively with a generator of
  large order, `nᵢ` in range by decomposition (64 Boolean rows each). Deferred to the pack map.

### 0.5 Totals (rows per node)

WOTS 2 × ≈3,926 (+16 for `N8`'s two aggregates' muxes), `aggPad` 136 / 406 / 812: `N2` ≈ 8,000,
`N4` ≈ 8,270, `N8` ≈ 8,690 (model: 5,576 for WOTS). `mRowModel4` stays far inside `N_M/1.05`.

## 1. Log
- Build tree `logs/fr-build-SE13b` copied from `fr-build-SE12f`, `snap.sh` at HEAD `75eff21`: `lake build
  FRNodeSound4Ctrl FRVerifierImplNode4F FRNodeRows4Model FRNodeRows4Fit` green (2,539 jobs).
- `FRNodeRows4Wots` (the rows; namespace `FR.W4`), `FRNodeRows4WotsB` (bytes ↔ elements ↔ block
  bits: `fb`, `fb_bit`, `readByte_hc`, `readDigest_digestOf`, `msgByte_hc`, `digestOf_eq`, the rows'
  readings `eqR_val`/`boolR_val`/`muxR_val`/`gateR_val`, `bitF_pk`): compile.
- `FRNodeRows4WotsS` part 1: `fam_byte` (any link family's bytes from `truthS4`),
  `nodeKind4_wots`, `holds_wots`, `j_byte`, **`step_out`** (a step block outputs `wotsStep idx i s x`).
  `FRNodeRows4Wots` imports `FRNodeCircuit4` (for `finBlk`); checked: no cycle (`FRNodeRows4` is not in
  `FRNodeCircuit4`'s closure).
- **`wots_sound4` proved** (`FRNodeRows4WotsF`): on `truthZ4`, `truthS4`, `lRows4`, `PubCells4` and
  `∀ r ∈ wotsRows κ σ S, r.Holds w`: `SigOk vk (mD κ σ w) (readSig4 κ σ w) = true`, `mD` the digest of
  the digit bits. Modules: `FRNodeRows4WotsT` (`sel_val`, `mux_rows`, `chain_end`),
  `FRNodeRows4WotsL` (`leaf_bytes`, `leaf_out`: the key leaf as a 4,265-byte stream through
  `chain_digest`), `FRNodeRows4WotsP` (`idx_lt`, `idx_bit`, `r31_byte`, `path_out`, `root_vk`),
  `FRNodeRows4WotsD` (`mD`, `msgDigits_mD`, `gW_order`/`gW_inj`: `x` has order > 1023 by three
  kernel-checked powers on 10 squarings, `bpowL`), `FRNodeRows4WotsF` (`facI_ev`, `prod_fac`, `csum`,
  `wotsDigits_mD`, `wots_sound4`).
- Probe: a linear `x^n` (1,667 multiplications) took ≈ 45 s of kernel; square-and-multiply on the bit
  list ≈ 2 s (`logs/fr-build-SE13b/scratch/T2.lean`).
- **Row-index allocation corrected**: prototype 1's rows reach `2^20 + 551,805 > 2^20 + 2^19`, so the
  node rows start at **`2^20 + 3·2^18` (M-relative 1,835,008)**, and `InSlot`/`pieceInB` now reserve
  the top `2^18` rows of every region (was 8) for the link and node rows (the prototypes end at
  551,805 < 786,432).
- `FRNodeRows4WotsK`: `hDig4_mD` (the `k`-mux on S-E12c's activity profile), **`gap4_wots`**.
  `FRNodeRows4Agg`: **`gap4_aggPad`**, `xRows_hold`, **`gap4_wots_aggPad`** (with `hfold`).
- **Collision avoided**: S-E13a is editing `FRNodeRows4` (link region `linkN = 2^15`, `linkRowsB4`,
  `packRows4`) and proposes appending `extRows4 κ σ` after `packRows4`. I did **not** edit `FRNodeRows4`;
  `FRNodeRows4Ext.extRows4` is ready (slot 1 = `xRows κ`, 7,992 / 8,266 / 8,680 rows), and the discharge
  takes `hfold : ∀ r ∈ xRows κ, r ∈ linkRows4 κ 1`. My earlier row-index plan (§0.1) is superseded by
  S-E13a's link region.
- Cell bound for `hfit4` by `decide +kernel` over the rows: ≈ 24 s of kernel per kind (`scratch/T6.lean`):
  too slow; left for a structural lemma.
- Controls `FRNodeRows4WotsCtrl`; axioms clean; source rule 0 findings; profiles in `logs/S-E13b/`.
- **Handover** (in order): RESULT §7 — (1) the fold in `FRNodeRows4` (+ `hfit4`'s cell bound,
  `mRowModel4`, `V` measured); (2) `aggChk` (`c_A` part needs no rows; the view checks wait for the
  pack map); (3) the blueprint items (`r31` family, A.7, A.11).
