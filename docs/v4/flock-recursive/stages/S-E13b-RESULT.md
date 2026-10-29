# S-E13b RESULT: the WOTS rows, `aggPad`, `aggChk` (S-N2's `Gap4.wots`, `.aggPad`, `.aggChk`)

Base: HEAD `75eff21` (S-N2). Build tree `logs/fr-build-SE13b` (a copy of `fr-build-SE12f`; `snap.sh`
snapshots HEAD and links the 12 new modules, `MINE.txt`), against `logs/org20`. Logs: `logs/S-E13b/`.
Every lake/lean command ran in the 16G scope under `timeout`. No sub-agents. Nothing committed. **No
existing module was edited** (S-E13a is editing `FRNodeRows4`/`FRNodeRows4Fit`/`FRNodeRows4Plan` in
parallel; the fold is one line in its `linkRows4`, §3). Journal: `S-E13b-JOURNAL.md` (§0 is the design
note of item 1).

## Status

| Item | State |
|---|---|
| 1. Design note | **Done** (JOURNAL §0): rows, regions, cells, cost; allocations written first. |
| 2. WOTS rows + 4.1 `wots_sound` | **Done.** `W4.wotsRows κ σ S` (3,926 rows per previous node, 3,924 + 2·maxK + 2 per aggregate); **`wots_sound4`**: `SigOk vk (mD κ σ w) (readSig4 κ σ w)` from `truthZ4`, `truthS4`, `lRows4`, `PubCells4` and the rows. |
| 3. `aggChk` | **Not discharged.** Its segment-view checks read `segView (pf trᵢ)`, which no row can reach without S-E13a's pack map (its B1–B3). Design in JOURNAL §0.4; the `c_A` part needs no rows (open, §6). |
| 4. `aggPad` | **Done.** `W4.padRows`; **`gap4_aggPad`**: `AggPad4 κ a (kA (rd4 pf) κ w a) w` for every aggregate. |
| 5. Fold + discharge | **Discharged up to the fold.** **`gap4_wots`**, **`gap4_aggPad`**, **`gap4_wots_aggPad`** (from `StmtN4` and `hfold : ∀ r ∈ xRows κ, r ∈ linkRows4 κ 1`). The fold is S-E13a's proposed `linkRows4 = linkRowsB4 ++ packRows4 ++ extRows4` (`FRNodeRows4Ext.extRows4`); not applied, to avoid a write collision in `FRNodeRows4`. `hfit4`, `mRowModel4`, the plan: §3. |

**Checks.**
- `lake build FRNodeRows4WotsCtrl` (all 12 modules) green: 2,460 jobs (`fr-build-SE13b/last.log`).
- **Axioms** (`logs/S-E13b/axioms.log`, `fr-build-SE13b/ax/AxSE13b.lean`): `wots_sound4`, `gap4_wots`,
  `gap4_aggPad`, `gap4_wots_aggPad`, `xRows_hold`, `gW_order`, `chain_end`, `leaf_out`, `path_out`,
  `csum`, `hDig4_mD`: `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 353
  files, 0 findings (`logs/S-E13b/source-rule.log`).
- **`FR.lean`**: add `import FRNodeRows4WotsCtrl` (it pulls the other eleven).

## 1. What was built (`loc.py`, `logs/S-E13b/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeRows4Wots` | 240 / 107 / 1 | Cells `hc`, `mc` (A.6's `WM` map), `Lc`, `E`; row forms `eqR`, `boolR`, `muxR`, `gateR`, `pk`; **`idxRows`**, **`selRows`**, **`chainRows`**, **`leafRows`**, **`pathRows`**, **`rootRows`**, **`ind`**, **`digRows`**, **`gW`**, `fac`, `facI`, **`sumRows`**, **`wotsRows`**; **`padRows`**, `lastR`. |
| `FRNodeRows4WotsB` | 215 / 146 / 22 | Bytes ↔ elements ↔ block bits: `fb`, `bitN`, **`fb_bit`**, `bitsB4_bit`, `zN4_eq`, `bit_of_zN4`, **`readByte_hc`**, `readDigest_hc`, **`msgByte_hc`**, **`digestOf_eq`**, `readDigest_digestOf`, `digestOf_congr`; the rows' readings `eqR_val`, `boolR_val`, **`muxR_val`**, `gateR_val`; `pk_ev`, **`bitF_pk`**. |
| `FRNodeRows4WotsS` | 173 / 124 / 10 | `md`, `md_get`; **`fam_byte`** (any link family's bytes, from `truthS4`); **`nodeKind4_wots`**, `holds_wots`; `idxOf`, `enc64_idx`, `j_byte`; **`step_out`** (a step block outputs `wotsStep idx i s x`). |
| `FRNodeRows4WotsT` | 127 / 91 / 6 | `digV`, `otsD`; **`sel_val`** (S-E2 F-2's selectors), `dig_mux`, **`mux_rows`**, **`chain_end`** (chain `i`'s end is `wotsChain idx i dᵢ (3 − dᵢ) otsᵢ`). |
| `FRNodeRows4WotsL` | 170 / 138 / 6 | `flat_get`, `fb'`, `leafW`, `endsD`, `leafMsg_get`, **`leaf_bytes`**, **`leaf_out`** (the key leaf's 67 blocks are `wotsLeaf idx ends`, via `chain_digest`). |
| `FRNodeRows4WotsP` | 210 / 166 / 11 | `idx_bitF`, `idx_testBit`, **`idx_lt`**, **`idx_bit`**, `j_mirror`; `curD`, `sibD`, **`r31_byte`**, **`path_out`** (`path_node` per level); `pub_vk`, **`root_vk`**. |
| `FRNodeRows4WotsD` | 128 / 87 / 11 | `pkD`, **`mD`**, `byte_digit`, `flatMap4_getD`, **`msgDigits_mD`**; `bpowL`, `bval`, `gW_255/771/641`, `dvd_small`, **`gW_order`**, **`gW_inj`**. |
| `FRNodeRows4WotsF` | 182 / 145 / 9 | `lbit`, `fac_ev`, `bit_pow`, `facI_ev`, `prod_fac`, `lsum_range`, **`csum`**, **`wotsDigits_mD`**, **`wots_sound4`**. |
| `FRNodeRows4Ext` | 51 / 22 / 2 | `actW`, **`xRows`**, **`extRows4`**, **`xRows_length`** (7,992 / 8,266 / 8,680), `extRows4_length_le`. |
| `FRNodeRows4WotsK` | 123 / 98 / 6 | `actW_eq`, **`ind_ev`**, `readDigest_mD`, **`hDig4_mD`** (the `k`-mux), `readSig_rd4`, **`gap4_wots`**. |
| `FRNodeRows4Agg` | 179 / 146 / 7 | `zN4_of_elem`, `zN4_bit`, `lastR_le`, `maxK_le`, **`gap4_aggPad`**, **`xRows_hold`**, **`gap4_wots_aggPad`**. |
| `FRNodeRows4WotsCtrl` | 58 / 33 / 9 | the controls (§4). |
| **total** | 1,856 / 1,303 / 100 | |

### The rows (per signed child `σ`; JOURNAL §0.2)

| Rows | What they say | Count |
|---|---|---|
| `idxRows` | 16 Boolean index bits, `idx = Σ_t E_t b_t`, the `j` mirror = `idx` | 18 |
| `selRows` | `s₀ = (1 − b₀)(1 − b₁)`, `s₁ = 1 − b₁`, `1 − s₂ = b₀ b₁` | 399 |
| `chainRows` | `x_{i,0} = ots_i`; `x_{i,s} − ots = s_{s−1}(h_out(i, s−1) − ots)`; `e_i − ots = s₂ (h_out(i, 2) − ots)` | 1,064 |
| `leafRows` | `h_in(u + 1) = h_out(u)` | 132 |
| `pathRows` | `h_in(B2) = h_out(B1)`; `l − cur = b_t(sib − cur)`; `r − sib = b_t(cur − sib)`; byte 31 of `r` through `r`'s element 1's 128 bits | 2,176 |
| `rootRows` | `h_out(B2_15) = vk` (the seed payload's cells) | 2 |
| `digRows` | `Σ_q E_q bit_{128h+q} = m_h`, `m` the final block's `h_out` (aggregate: `T_{j,h} = [k = j]·h_out(F_j)_h`, `Σ_j T_{j,h} = …`) | 2 / 2 + 2·maxK |
| `sumRows` | `R_{i+1} = R_i f_i`, `R_0 = R_133 = 1`, `f_i = g^{3−dᵢ}` / `g^{−4^t c_t}` (linear in `b₀, b₁, s₂`) | 133 |

`aggPad` per aggregate: `135·(maxK − 1) + 1` rows. **Totals (`xRows_length`, kernel): `N2` 7,992,
`N4` 8,266, `N8` 8,680** (the model had 5,576 for WOTS).

### The main theorems

```lean
theorem wots_sound4 (hZ : truthZ4 κ w) (hS : truthS4 κ w) (hL : ∀ r ∈ lRows4 κ, r.Holds w)
    (hP : PubCells4 κ w vk c₁ c₂) (hσ : σ < 2) (hW : ∀ r ∈ wotsRows κ σ S, r.Holds w) :
    SigOk vk (mD κ σ w) (N4s.readSig4 κ σ w) = true

theorem gap4_wots_aggPad (pf) (hfold : ∀ r ∈ xRows κ, r ∈ linkRows4 κ 1)
    (hS : StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w) :
    (∀ σ < 2, SigOk vk (hDig4 κ σ (kOf (N4s.rd4 pf) κ w σ) w) ((N4s.rd4 pf).sgn κ σ w).σ = true) ∧
      ∀ a < nAgg κ, AggPad4 κ a (kA (N4s.rd4 pf) κ w a) w
```

The two conclusions are `Gap4.wots` and `Gap4.aggPad` verbatim. `gap4_wots`/`gap4_aggPad` take the
rows' truth `hX : ∀ r ∈ xRows κ, r.Holds w` directly.

**How `wots_sound4` goes** (3.x's `Wots.wots_sound`, every hypothesis from blocks, families or rows):
- `idx < 2^16` and its bits (`idx_lt`, `idx_bit`); the `j` bytes of every step and leaf block are
  `enc64 idx` (`j_byte`: the `j` family to mirror 399, the index row).
- Each chain: `step_out` (w43 block + `x`/`j` families + pins) and the mux rows on the selectors
  (`sel_val`) give `wots_chain_sound`'s hypotheses (`chain_end`).
- The key leaf: a 4,265-byte stream (`hashB1 tagWotsLeaf`, 65 `stream`, `streamEnd41`), linked by
  `leafRows`, padded by `streamEnd41`'s pins, its bytes from the `end9`/`end41lo`/`end41hi` mirrors
  (`leaf_bytes`) — `chain_digest` gives `wotsLeaf idx ends` (`leaf_out`).
- Each path level: `path_node` with the `l`/`r0`/`r31` families, the mux rows and byte 31
  (`r31_byte`); `root_vk` from `PubCells4`.
- The digits: `mD`'s 128 message digits are the digit cells (`msgDigits_mD`); the checksum rows give
  `Σ(3 − dᵢ) = Σ 4^t c_t` (`csum`, through `gW_inj`), so `wotsDigits mD` is the circuit's digits.
- **`gW_order`**: `x ∈ GF(2^64) ⊂ F` has order > 1023. Every divisor of `2^128 − 1` below 1024
  divides 255, 771 or 641 (`dvd_small`, `decide +kernel` on 1,023 `Nat` mods) and `x^255`, `x^771`,
  `x^641 ≠ 1` (`decide +kernel` on square-and-multiply, `bpowL`: ≈ 2 s; a linear power took ≈ 45 s).

## 2. Design decisions and deviations

1. **The rows are M rows in slot 1's link region** (S-E13a's `2^15` rows), not L rows: `lRows4` is
   frozen (`FRSoundness4XFront.lRows4_fit` and `FRVerifierImplNode4F`'s closed-form `evalL` unfold it).
   New cells are **L only**, past A.7's 8,519 used elements of signed child `σ`'s stride (JOURNAL
   §0.1: 8704–11648). No new M cells.
2. **Byte 31 of `r` costs 2,048 rows per child.** The `r31` family links `B2`'s byte 0 to mirror
   `565 + t` at bits 0–7; moving bits 120–127 of `r`'s element 1 there is not F-linear, so the rows
   decompose the element (128 Boolean rows + 2). **Proposed blueprint change (S-C, P2, `linkWAll`):**
   `r31`'s source `549 + t` with `mbo = 248` (as `end41hi` shares `end41lo`'s at 184); `pathRows` then
   loses 130 rows per level (−4,160 per node).
3. **The checksum is multiplicative** (`g^{Σ(3−dᵢ)} = g^{Σ 4^t c_t}` with `ord g > 1023`): 133 product
   rows, no binary adder. The model's "digits → `h_out` 266" are 2 wide linear rows per child here.
4. **`aggPad`'s cut is inside element 7** (`lastR k` = 64, 63, 62, 61): main block `aggL j − 1`'s
   element 7 is decomposed for `2 ≤ j ≤ maxK` (the `maxK` case is the main chain's own padding).
5. **The model under-counted**: WOTS 2 × 2,788 → 2 × ≈3,930 (+ the leaf/path links and the index the
   model left out, + byte 31). `aggPad` was not in the model.
6. **`aggChk` is not discharged** (item 3): `aggChecks`' per-segment checks are about
   `segView (pf (slotTr …))`; `pf` is the reader's parameter and the segments' fields reach the
   circuit only through the slots' import cells (the pack map, S-E13a, with its B1: segments `i ≥ 1`
   are unaligned).

## 3. The fold, `hfit4`, `mRowModel4`, the plan (for S-E13a / the orchestrator)

- **The fold** (one edit in `FRNodeRows4`, S-E13a's file): `import FRNodeRows4Ext`, and
  `linkRows4 κ σ := linkRowsB4 κ σ ++ packRows4 κ σ ++ W4.extRows4 κ σ`. Then
  `hfold := fun r hr => List.mem_append_right _ (by simp [W4.extRows4, hr])`, and
  `gap4_wots_aggPad` turns `Gap4`'s `wots` and `aggPad` into theorems for `resid4_of`.
- **`hfit4`**: slot 1's link rows grow by 7,992–8,680 (`extRows4_length_le ≤ 8,680`), inside the
  23,854 the link region leaves. The cell bound (`< 2^(logM+2)`: H and L cells below `oneCell`, the
  selector copies below `oneCell + vslots·2^20`) is **open**: `decide +kernel` over the rows works but
  costs ≈ 24 s of kernel per kind (`scratch/T6.lean`), so it should be a structural lemma.
- **`mRowModel4`**: `wotsRows4 := 2 * 2788` should become the node rows (7,992 / 8,266 / 8,680); every
  kind stays far inside `N_M / 1.05` (`N2` 2.16 M of 4.19 M).
- **The plan** (≤ 2 s at process start): unaffected — the node rows are closed constants per kind, no
  compile pass. **`V`**: ≈ 25–35 k entries at slot 1 (the packing rows have 128–130 terms), one product
  per entry with S-E13a's split eq tables; to be measured with S-E13a's `VTime4` after the fold.

## 4. Controls (`FRNodeRows4WotsCtrl`)

| Definition | (+) | (−) |
|---|---|---|
| `boolR` | `boolR_pos` (`0`, `1`) | `boolR_neg` (`y`: `y(1 − y) ≠ 0`, kernel) |
| `muxR` | `muxR_ctl` (selector 1 takes `x`, 0 takes `y`) | `muxR_neg` |
| `digV` | `digV_ctl` (bits `(1,1)` → 3) | `digV_ctl` (`(0,1)` → 2) |
| `gW` | `gW_order` | `one_not_inj` (`1` does not separate exponents) |
| `lastR` | `lastR_eq` | `lastR_ne` |
| `ind` | `ind_ctl` (`k = 2`: `ind 2 = 1`, `ind 1 = ind 3 = 0`) | (same) |
| `wotsRows`/`padRows` | `wots_sound4`, `gap4_aggPad` (their soundness) | `not_aggPad4` (S-E12a) binds the padding |

A positive control of the rows' joint satisfiability (an honest node witness) needs `node_complete`
and P2's witness; not built.

## 5. Times (sequential `lake env lean -DElab.async=false --profile`, one core, 16G; `logs/S-E13b/profile-*.log`)

| Module | wall | type checking | tactics |
|---|---|---|---|
| `FRNodeRows4Wots` | 7.4 s | 0.01 s | 0.00 s |
| `FRNodeRows4WotsB` | 12.7 s | 0.80 s | 1.14 s |
| `FRNodeRows4WotsS` | 15.3 s | 1.66 s | 1.30 s |
| `FRNodeRows4WotsT` | 10.1 s | 0.20 s | 0.63 s |
| `FRNodeRows4WotsL` | 16.1 s | 2.34 s | 2.54 s |
| `FRNodeRows4WotsP` | 13.4 s | 0.95 s | 1.79 s |
| `FRNodeRows4WotsD` | 15.3 s | 4.32 s | 0.60 s |
| `FRNodeRows4WotsF` | 11.5 s | 0.79 s | 0.91 s |
| `FRNodeRows4Ext` | 20.9 s | **11.7 s** | 0.05 s |
| `FRNodeRows4WotsK` | 10.3 s | 0.36 s | 0.80 s |
| `FRNodeRows4Agg` | 10.1 s | 1.67 s | 1.06 s |
| `FRNodeRows4WotsCtrl` | 7.0 s | 0.04 s | 0.02 s |

Imports ≈ 6 s of each wall. Kernel ≈ 25 s in all; **`xRows_length`'s `simp` proof costs 11.7 s of
type checking** (the kernel re-checks the list lengths) — a golf target (a length lemma per row family
instead of one `simp` over the whole list). `FRNodeRows4WotsD`'s 4.3 s are `dvd_small` and the three
powers. Final build: `lake build FR FRNodeRows4WotsCtrl` green, 2,564 jobs (`logs/S-E13b/build-final.log`).

## 6. For P2 (the prover)

The node witness must fill, per signed child `σ` (L stride `σ`, `Lc σ o = lBase·128 + σ·2^14 + o`):
- **8704 + t** (`t < 16`): bit `t` of `idx`, as `0`/`1`; `Lc σ 0 = Σ_t E_t b_t` (so `idx`'s other bits
  zero) and the `j` mirror (source 399, element 0) **equal to the idx element** (its `c₁` zero).
- **8720 + i** (`1 ≤ i ≤ 132`): `R_i = Π_{j<i} f_j` with `f_j = x³·x⁻¹^{dⱼ}` (`j < 128`),
  `x⁻¹^{4^t cₜ}` (checksum digit `t = j − 128`), `x = ⟨2, 0⟩`.
- **8960 + 128t + q**: bit `q` of mirror `549 + t`'s element 1 (`r`'s bytes 16–31); mirror `565 + t`'s
  element 0 is **exactly** `r`'s byte 31 in its low byte, zeros above.
- **11008 + 2(j − 1) + h** (aggregates): `T_{j,h} = [k = j]·h_out(F_j)_h`.
- **11264 + 128(j − 2) + q** (aggregates, `2 ≤ j ≤ maxK`): bit `q` of main block `aggL j − 1`'s
  element 7.
- The mirrors: `x_{i,0} = ots_i`, `x_{i,s} = s ? h_out(i, s−1) : ots_i`, `e_i = [dᵢ < 3] ? h_out(i, 2) :
  ots_i` (`end9`/`end41` sources), `l = b ? sib : cur`, `r = b ? cur : sib` — whole elements, both
  halves (the unlinked bits of a mirror source must still equal the muxed element's).
- The key leaf blocks' `h_in` = the previous block's `h_out`; `B2`'s `h_in` = `B1`'s `h_out`.
- An aggregate of `k < maxK` segments: `F_{a,k}`'s `h_in` and elements 4–6 as main's, element 7 main's
  cut at `lastR k` bytes (zeros after); `k = maxK`: main's last block's element 7 zero past `lastR`.

## 7. Open questions / handover (in order)

1. **The fold** (§3), then `hfit4`'s cell bound for `extRows4` (structural), `mRowModel4`, and `V`'s
   measurement. Then `resid4_of`'s `hG.wots`/`hG.aggPad` can come from `gap4_wots_aggPad` (a new
   `Gap4R` without them, as S-E13a does for its items).
2. **`aggChk`**: (a) `c_A = leafStmt e n` from the `hashA` block (`hashA_leafStmt`) and `PubCells4`'s
   `stC` cells (`digestOf_halves`) — needs `enc64 (hAn) = ` bytes 33–40 (`hAn < 2^64`); no rows.
   (b) `1 ≤ k ≤ 4`: `ActK`, `maxK ≤ 4`. (c) The view checks need the pack map for sub-slots `i ≥ 1`
   (S-E13a's B1, R-A′) and `pf`'s spec (B3).
3. **Blueprint**: the `r31` family change (§2.2); A.7's L layout for the new aux cells (JOURNAL §0.1);
   A.11's WOTS row count.
