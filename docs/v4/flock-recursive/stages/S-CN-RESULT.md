# S-CN RESULT: the node's `targetS` and `linkW` (blueprint revision 3.13, gap 3)

Track S-CN, 2026-10-28, branch `v4/flock-recursive`. This covers S-C's part (the specifications
and their MLE lemmas) and S-F2's part (the computable forms and `_meets`). `implC` is not wired
here: that waits for INT-2 and is described in §6. Nothing was committed.

Logs are in `logs/S-CN/`. The build tree is `logs/fr-build-S-CN/`. Its `src/` is a snapshot of
HEAD `c66dbc0`, with my two modules symlinked in, so other tracks' edits in progress cannot break
it. Every `lake`/`lean` run used the 16G scope and a `timeout`.

## 1. What was built

| Module (new) | Code lines (`loc.py`) | Content |
|---|---|---|
| `FRNodeTarget` (S-C part) | 597 (43 theorems) | `nodeTgt` (S-G's `Snd.nodeKind` verbatim: `logs/S-CN/Bridge.lean` checks `nodeTgt = nodeKind` by `rfl`), `nodeE`, **`targetSNodeS`**, `blkW`, **`targetSNode_blk`**. Kind bits: `tgtE_ctr` (the counter `64 v` split off), `tgtE_w43` (`i`, `s` split off), `tgtE_*_hi`. Closed form `Gc` = `chainC` + `stmtC` + `wotsC` (`ctrC`, `w43C`, ten classes `cls`). **`blkW_eq`**, **`targetS_node_eq`**, `Gc_hi`. Link families: `Fam`, `fam` (8 families), `wmB`/`srcB`/`mirB`/`fpos`/`mpos`, `slotWL`, **`linkWS`**, **`linkInd`**, `fam_bounds`, **`linkInd_sum`**, **`linkW_mle`**. Controls (§4). |
| `FRVerifierImplNode` (S-F2 part) | 407 (34 theorems) | Two-level `eq` tables (`eqAtR_split`), prefix arrays (`pfx`), separable range sums (`twoF_eq`, `sepSum_eq`), `Tabs`/`tabs`/`tabsE`, `eqbI`, `rangeI`, the counter `ctrI` (`ctrI_eq`), `clsTab`, `Wts`, `e43`/`w43I`, `gAt`/`gArr` (`gAt_eq`), **`targetSNodeI`**, **`targetSNode_meets`**. `tab10`/`eq10`, `linkWOne`, **`linkWI`**, **`linkWAllI`**, `linkWSA`, **`linkW_meets`**, **`linkWAll_meets`**. Controls (§4). |

No existing module was edited. `FR.lean` needs `import FRNodeTarget` and
`import FRVerifierImplNode` once `implC` uses them (§6).

**What the statements say.**

- `targetSNodeS r = Array.ofFn σ ↦ FRPubTarget.targetS (zLo r ++ r[1..16]) E σ` with
  `E(σ, (hi, blk)) = nodeE blk (σ + 64 hi)`. This uses the leaf's convention exactly
  (`targetSLeafS 16`).
- `targetS_node_eq : targetSNodeS r = ofFn σ ↦ Σ_{hi<256} eq(r_lo, hi) · Gc r_blk (σ + 64 hi)`.
  `Gc` is the closed form of `Σ_blk eq(r_blk, blk) E(blk, ·)` (`blkW_eq`, for every position
  `p < 2^14`). It is built per region:
  - each constant class: a kind's bits times a range sum of `eq(r_blk, ·)` or single-block terms;
  - the stream counter: `Σ_k eq(r_blk, lo + k) · bit_j(k + 2)` on `t_lo`'s bits 6–31;
  - each chain's last block (`t = 1,481,344`, final): its own class;
  - `w43`'s `i`/`s`: 399-term table sums.
- `linkWS f τ θ r_blk r_pos = Σ_{σ<2} Σ_{t<n_f} eq(τ, src) · (eq(r_blk, src) · slotW(field) −
  eq(r_blk, mirBlk) · slotW(mirPos))`. This is A.8's formula with θ made explicit:
  `slotW(pos) = Σ_{s<8 len} eq(θ, s) eq(r_pos, pos s)`.
- `linkW_mle`: `linkWS` equals `Σ_{u,s,y,q} eq(τ,u) eq(θ,s) eq(r_blk,y) eq(r_pos,q) ·
  linkInd f u s y q`. That is the multilinear extension of the source-minus-mirror indicator over
  the `16 + 10 + 16 + 10` variables.
- `linkInd_sum` gives the indicator's meaning against any weights. With `Ψ = z`:
  `Σ_σ Σ_t A(src) Σ_s B(s) (z(src, field s) − z(mirBlk, mirPos s))`. This is the family's
  residual, zero when every field equals its mirror.
- `targetSNode_meets : targetSNodeI r = targetSNodeS r` and
  `linkW_meets : linkWI f τ θ rb rp = linkWSA f τ θ rb rp` hold for every `r` and every `f`.
  Neither has a hypothesis.

## 2. Build and kernel times

Sequential elaboration (`lean -DElab.async=false --profile`, one core):

| Module | Wall | Type checking (kernel) | Peak RSS | Log |
|---|---|---|---|---|
| `FRNodeTarget` | 19.8 s (imports 3.6 s) | 3.45 s | 2.8 GB | `profile-FRNodeTarget.log` |
| `FRVerifierImplNode` | 12.2 s (imports 3.7 s) | 1.17 s | 2.8 GB | `profile-FRVerifierImplNode.log` |

The only `decide`s are the eight concrete target bits in `nodeBit_pos`/`nodeBit_neg`
(interpretation 1.3 s in total). Nothing runs `decide` over the layout or a table. The layout is
handled by sum splitting (`sum_range_mul`, `sum_wots`) and lemmas on `nodeTgt`'s regions.

Axioms (`axioms.log`): all 21 audited statements use `propext`, `Classical.choice`, `Quot.sound`
or a subset. There is no `sorry`. Source rule: `source-rule: 121 files, 0 finding(s)`
(`source-rule.log`).

## 3. Cost on the VM

`logs/S-CN/time-5.log`. The probe is `SCNTime.lean`, `taskset -c 5`, best of 40 runs. Operand
generation is included: 0.09 ms for `targetS`, 0.34 ms for the four `linkW` points.

| Op | Best | Products (count of the code) |
|---|---|---|
| F product (reference) | 80 ns | — |
| `targetSLeafI` (today's `implC`, for comparison) | 1.58 ms | 16.6 k |
| **`targetSNodeI`** | **2.00 ms** | ≈ 3.9 k products + ≈ 45 k additions (86 prefix arrays, 1,153 × 13 lookups) |
| `linkWI`, one family (`x` / `j`) | 0.88 / 0.82 ms | tables ≈ 2.3 k + 6 per source + 3 per field bit |
| **`linkWI` × 8 (as `linkOps` calls it)** | **4.35 ms** | ≈ 35 k |
| `linkWAllI` (tables shared) | 1.90 ms | ≈ 19 k |

Effect on `T_V` (N30, 204.9 ms):
- `targetS`: about +0.4 ms over the leaf function it replaces for nodes.
- `linkW` with today's interface (8 calls, the tables rebuilt each time): about +4.0 ms, so V is
  about 209.5 ms against the ≈ 264 ms cap.
- With one shared-table op (§6.3): about +1.55 ms.

These are above the blueprint's estimate of ≈ 1,300 products for `linkW`. The cost is per source:
each `eq` read costs one product from the two-level tables. §7 lists the cuts.

## 4. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `nodeTgt`/`nodeE` (kind constants, offsets) | `nodeBit_pos`: `one` set on chain block 0 and on `hashA`; chain block 1's counter `t = 128` sets bit 7 (`p = 1031`); `hashB1 tagNode`'s `0x4E` sets byte 0 bit 1; `w43` step `(1, 2)` sets `i` bit 0 and `s` bit 1 | `nodeBit_neg`: chain block 1's bit 6 is clear (a counter off by one, `64 k`, would set it); `hashA`'s `0x4C` has byte 0 bit 1 clear (a wrong tag constant is detected); `s` bit 0 clear; `WM` unpinned; `f0` set on the chain's last block and clear on the one before it |
| `Gc`/`blkW` (closed form) | `Gc_controls`: `Gc (cube 1) 1031 = 1` | `Gc (cube 1) 1030 = 0` |
| `targetSNodeI` | `targetSNodeI_blk`: at a Boolean block point it reads that block's target | `targetSNodeI_free`: at a `free` block point (`≥ wmBase`) it is the zero array |
| `linkWS`/`linkWI` | `linkW_hit`/`linkWI_hit`: family `x` reads `1` at its first source, field bit 0 = position 600 (byte 11) | `linkW_off`: position 601 reads `0` (a wrong offset is detected); `linkW_mir`: the mirror cell reads `−1` (the mirror side is present and has the opposite sign) |
| `linkInd`, `fam` | `linkInd_sum` (the residual identity) | `fam_bounds` (every source, mirror and position lies inside the `2^16 × 2^10` cube that `linkW_mle` sums over) |

## 5. Deviations from the blueprint (the sound readings chosen)

**D-1. 8 link families, not 7: `end41` crosses a block boundary.**
- Counterexample. End `k` of the key leaf is at stream byte `9 + 32k`. For `k = 2u + 1` that is
  block `u`, byte 41, and 32 bytes run to byte `73 > 64`. A.8's `end41` field "(offset 41, 32 B)"
  does not fit in one block.
- Reading chosen: `end41lo` is block `u` bytes 41–63 (23 B, mirror bits 0–183); `end41hi` is block
  `u + 1` bytes 0–8 (9 B, mirror bits 184–255). Both use the same mirror source `466 + u`, `u < 66`.
- Only 66 odd ends exist (`k ≤ 131`; byte 41 of the last block is pinned zero), not 67. The
  family count is `nLinkFam = 8`, which `FRVIRFinals` already has.

**D-2. The mirror cells must be in elements 0–7 of their block.**
- Counterexample. Sh's claim point has three element coordinates from S2, then four zeros
  (`FRVIRFinalsSG.shSrc`; §2 step 4: 10 collapse rounds over the positions `< 1024`). So a family
  can read only positions `< 1024` of a block.
- A.6's map `WMbase_σ·128 + 2(off_f + t) + p` places mirror element `2(off+t)+p` at element
  `(2(off+t)+p) mod 128` of its block. For example, `x`'s source `t = 4` is element 8, at
  position 1024, which no `linkW` can read. The mirror side of the identity would then be missing
  for most sources.
- Reading chosen: mirror source `g` of slot `σ` is in block `wmB σ + ⌊g/4⌋`, at positions
  `256 (g mod 4) + [0, 256)` (elements `2(g mod 4)`, `+1`). `wmB σ = wmBase + 146 σ`, so there
  are 146 blocks per slot.
- These blocks end at 47,586, before `lBase = 47,616`, so `nodeLayout` (where everything from
  `wmBase` on is `free`) is unchanged. `FRNodeLayout`'s `wmSlot = 10` and `hEnd = 47,322` become
  wrong as documentation and need S-E's update.
- The map is three definitions (`wmB`, `mirB`, `mpos`). Changing it changes only them, `fam_bounds`
  and the controls' numerals.

**D-3. `WMbase_σ = wotsBase_σ + 498` (A.6) is wrong.**
- Counterexample. With the consecutive layout, `wotsBase_0 + 498 = wotsBase_1`, which is slot 1's
  first `w43` block.
- Reading chosen: `wmB σ` as in D-2, after both WOTS runs (`FRNodeLayout.wmBase`).

**D-4. The chain's last block.**
- Under revision 3.13 the stream is 1,481,344 = 64 × 23,146 bytes. The last block's
  `t_lo = 1,481,344` therefore equals the counter form `64(k+1)`; only `f0` differs. A.8 says
  1,437,760, the revision 3.12 value.
- I keep the blueprint's structure (a single-block term for the last block, class `cls 2 =
  blockTarget 1481344 true`). It is exact whatever the stream length is.

**D-5. `w43`'s `s`.**
- `s` is `o mod 3 ∈ {0,1,2}`, as S-G's `nodeKind` has it (`nodeKind_controls`: offset 5 is
  `w43 1 2`). This differs from the blueprint text's `w_{i,1..3}`. The spec follows `nodeKind`.
  If the contract numbers steps from 1, `nodeKind`, the mux and the spec change together.

## 6. Wiring into `implC` (after INT-2 lands)

**6.1 `targetS`.** In `FRVerifierImpl`:
- `implCWith`: `targetS κ r := if κ.isNode then NodeI.targetSNodeI r else targetSLeafI r`.
- `specC`: `targetS κ r := if κ.isNode then NodeT.targetSNodeS r else targetSLeafS 16 r`.
- `implC_meets`: split on `κ.isNode` and use `targetSNode_meets` or `targetSLeaf_meets 16`.

The operand is the same Z1 point as the leaf's, `r[0]` then the 16 block coordinates. S-G's Z1/Z2
truth over the node `targetS` can use `targetS_node_eq` and `nodeTgt = Snd.nodeKind` (`rfl`).

**6.2 `linkW` needs θ and `r_pos`.**
- `W_f` contains `slotW(θ, r_pos)`, but `.linkW tau f r` passes only `τ` and `r_blk`
  (`FRVIRFinals.linkOps`). The op has to receive all four points.
- The least-change form keeps `OpImpl.linkW : Kind → Array F → ℕ → Array F → F`:
  - `finSh` packs `τ ‖ θ` (S1's first `m − 14` coordinates, then 18–27) and `r_blk ‖ r_pos` (S2's
    first `m − 14`, then the next 10);
  - `implCWith`: `linkW κ a f c := if κ.isNode then NodeI.linkWI f (a.extract 0 16)
    (a.extract 16 26) (c.extract 0 16) (c.extract 16 26) else 0`;
  - `specC` the same with `linkWSA`, and `linkW_meets` in `implC_meets`.
- Leaves keep `0` (P2-RESULT item 7).
- The new registers change `finSh`'s register numbering and `relSh`/`flag_finSh` (S-0/S-F).

**6.3 Shared tables (recommended).** With 8 calls, the four points' tables are rebuilt 8 times:
4.35 ms against 1.90 ms. One op `linkWAll τθ r → AF 8` (implemented as `NodeI.linkWAllI`, with
`linkWAll_meets`) followed by 8 `getF` would save about 2.5 ms of `T_V`.

**6.4 Related gap, not mine.** `slotW 1` (the In slot) is the leaf's `d` at 520. A node's Sh needs
`h_in` (slot map 2, base 0), selected by kind as `targetS` is.

## 7. Open questions

1. **D-2's mirror map** needs the orchestrator's ruling. It affects P2's mirror writes, S-E's mux
   output addresses and `FRNodeLayout`'s `wmSlot`/`hEnd`.
   - The chosen placement uses elements 0–3 (positions 0–511) of `free` `WM` blocks. That is sound
     only if the node's Sh `Out`/`In` tables do not read `WM` blocks' `h_in`/`h_out` slots.
   - They must not anyway: consecutive non-chain blocks are not linked, so the node's Sh has to
     mask to chain blocks.
   - If they do read them, use elements 4–7 (two sources per block, 291 blocks per slot). That does
     not fit before `lBase`, so `WM` would have to go in the L–M gap `[47,740, 49,152)`.
2. **The node's Sh identity itself** (`truthS1`'s `ShHolds` with the 8 terms) is S-G's. `linkW_mle`
   and `linkInd_sum` are the pieces it needs: the in-table term `Σ_{y,q} W_f(y, q) z(y, q)` at the
   Sh point is `linkWS`, and its Boolean-table value is the residual.
3. **Cost cuts if `T_V` needs them**, all inside `FRVerifierImplNode`, no statement changes:
   - source-side sums via the product table `eq(τ,·)·eq(r_blk,·)` and `sepSum` (stride-1 families);
   - `j`'s constant mirror factored out (800 sources);
   - mirror terms grouped by mirror block;
   - together about 3 products per source instead of 6, saving about 1 ms with the shared op.
4. **A.11's template counts.** `tplLinkW` at ≈ 2,500 rows per family is below what this op costs
   for `x` and `j` (≈ 6 n_f + 3 · 8 len products: about 5.6 k each with the generic loop). S-E
   should size the templates from §3, or from the cut forms in item 3.
