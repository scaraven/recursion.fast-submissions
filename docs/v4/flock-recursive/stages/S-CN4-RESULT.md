# S-CN4 RESULT: the node's verifier ops at the revision 4.1 layout (closes P4e's D11 for `finSh`)

Track S-CN4, 2026-10-28, branch `v4/flock-recursive`. HEAD at start `0fd05ce`; it moved to `94ee843`
(QUEUE: D10 keep the start term, D11 is S-CN4's) and `67e5c76` during the pass. Build tree
`logs/fr-build-SCN4` (copy of `fr-build-INT6`, against `logs/org20`; `MINE.txt` lists the three new
modules). Logs in `logs/S-CN4/`. Journal: `S-CN4-JOURNAL.md`. Every lake/lean command ran in the 16G
scope (12G for single files) under `timeout`. No sub-agents. Nothing committed. No existing module
was edited and no statement changed. Every new name was grepped first (namespaces `FR.NT4`,
`FR.NI4`, `FR.Snd.CN4` are new).

**State.** Items 1, 2 and 4 are done for `shiftMask`, `slotW` and `linkWAll`, and items 1 and 2 for
`targetS`. Item 3 is done for `shiftMask` and `linkWAll` (`slotW` needs no new op). **Not done:
`targetSNode4I`** (item 3 for `targetS`). `implN4` therefore takes the node's `targetS`
implementation as a parameter `tS` with the hypothesis `tS ν = targetSNode4S ν`. Handover below.

## 1. What was built

| Module (new) | total / code / thm | Content |
|---|---|---|
| `FRNodeTarget4` (specs, `FR.NT4`) | 160 / 70 / 12 | `nbN` (17/18), **`nodeE4`**, `rbOf4`, **`targetSNode4S`**, `nodeE4_etN4`; **`lkE`**, **`lkSh`**, **`lkE0`**, **`shiftMask4S`**; `slotBase_node4`; **`linkW4S`**, **`linkWAll4S`**; layout numbers without the soundness modules: `chLen_facts` (`decide` per kind), **`chainLk4_iff`**, `fam_src_lt4`, `fam_mir_lt4`, `wotsB_hUsed`, `srcB4_lt'`, `mirB4_lt'`; `chainLk4_ctrl` |
| `FRVerifierImplNode4` (computed, `FR.NI4`) | 367 / 281 / 15 | **`shP`** (the successor's prefix sum by the low bit) and **`shP_eq`**; `mF`, **`shiftMask4I`**, `sum_lk`, **`shiftMask4_meets`**; `lo9`, `hiN`, `BT`, **`bt`**, `eqAtR_split9`, **`bt_eq`**; `linkWOne4`, **`linkWAll4I`**, `linkWOne4_eq`, **`linkWAll4_meets`**; **`implN4`**, **`specN4`**, **`implN4_meets`**; controls `lk_cube`, `shiftMask4_ctrl`, `linkW4S_x0`, `linkW4_ctrl` |
| `FRNodeTarget4W` (bridge to P4e, `FR.Snd.CN4`) | 238 / 181 / 11 | `sum_lkW4`, `sum_shN4`, `sum_famW4'`, **`final_node4`**; `linkSum_eq8`, **`wSumNode4`**, `ptA_pad`, `ptA_app`, **`wNS4_node4`**; **`peL_node4`**; `lkE0_ctrl` |
| total | 765 / 532 / 38 | `loc.py`, `logs/S-CN4/loc.txt` |

**Main statements.**

```lean
-- the specifications (FRNodeTarget4)
def targetSNode4S (ν) (r : Array F) : Array F :=
  Array.ofFn (n := 64) fun σ => FR.targetS (ℓ := 8 + nbN ν) (Fin.append (zLo r) (rbOf4 ν r))
    (fun σ u => nodeE4 ν (u.val / 256) (σ + 64 * (u.val % 256))) σ
def shiftMask4S (ν) (τ r : Array F) : F × F × F :=          -- read at nb = m − 14 entries
  (Σ_{y<2^nb} [chainLk4 ν y] eq(τ,y) eq(r,y), Σ [chainLk4 ν y] eq(τ,y) eq(r,y+1), eq(r,0) + eq(r,chLen ν 0))
def linkWAll4S (ν) (tt rr : Array F) : Array F           -- tt = τ ‖ θ, rr = r_blk ‖ r_pos (nb + 10)
  -- family f: Σ_σ Σ_t eq(τ, srcB4) (eq(r, srcB4) slotWL(fpos) − eq(r, mirB4) slotWL(mpos))
-- slotW: 3.x's slotWS (slot maps 0 → 256, 2 → 0), `slotBase_node4`
-- the meets (FRVerifierImplNode4), no hypotheses
theorem shiftMask4_meets (ν) (τ r : Array F) : shiftMask4I ν τ r = shiftMask4S ν τ r
theorem linkWAll4_meets (ν) (tt rr : Array F) : linkWAll4I ν tt rr = linkWAll4S ν tt rr
theorem implN4_meets (ν) (h : (base ν).Meets (spec ν)) (htS : ∀ r, tS ν r = targetSNode4S ν r) :
    (implN4 base tS ν).Meets (specN4 spec ν)
-- the MLE lemmas against P4e (FRNodeTarget4W)
theorem final_node4 (τ rb : Fin (nbN ν) → F) (θ rp : Array F) (κ : F) :
    Σ_q Σ_y eqAtR rb y * eqAtR (ptA 10 rp) q * wNode4 ν τ (ptA 10 θ) κ y q =
      lkE ν τ rb * slotWS 0 θ rp + ((lkSh ν τ rb + κ * lkE0 ν rb) * slotWS 2 θ rp +
        Σ_{f<8} κ ^ (f + 2) * linkW4S ν f τ (ptA 10 θ) rb (ptA 10 rp))
theorem wNS4_node4 (ν) (es : Log) : wNS4 (.node ν) es = wSumNode4 ν es
theorem peL_node4 (hν : kindOfC es = .node ν) (hr : ∀ l < nbN ν + 1, r.getD l 0 = coordAt es 2 l) :
    targetSNode4S ν r = Array.ofFn (P4a.peL (zlm4 N4c.indN4 N4c.etN4) es)
```

`wSumNode4 ν es` is `relSh4`'s node value `w_out + w_in` on the specifications, with the registers
at the log's values: `shiftMask4S ν (pad18 τ) (pad18 r_blk)`, `slotWS 0/2 θ r_pos`,
`linkSum (linkWAll4S ν (τ ++ θ) (r_blk ++ r_pos)) κ_s 8 ((Sh + κ_s E₀)·slotW₂) κ_s²`.

**The algorithms.**
- `shiftMask4I`: by `chainLk4_iff`, the mask is `[0, c)` less `a` (`c = chLen₀ + chLen₁ − 1`,
  `a = chLen₀ − 1`). So `E = prefixP nb (eq·eq) c − eq(τ,a) eq(r,a)`,
  `Sh = shP nb mF c − eq(τ,a) eq(r,a+1)`, `E₀ = eq(r,0) + eq(r,chLen₀)`. `shP` recurses on bit 0:
  `x = 2u` steps to `2u + 1` (factor `(1−τ₀) r₀`, then a `prefixP` on the rest at `⌈c/2⌉`),
  `x = 2u + 1` to `2(u + 1)` (factor `τ₀ (1−r₀)`, then `shP` on the rest at `⌊c/2⌋`).
- `linkWAll4I`: 3.x's `linkWOne` with `srcB4`/`mirB4`, `eq` of an `nb`-coordinate block point
  from two tables (`bt`: low 9 coordinates, 512 entries; high `nb − 9`), one product per read;
  `θ`/`r_pos` tables shared (3.x's `tab10`).

## 2. Build, kernel and VM times

- `lake build FR FRNodeTarget4 FRVerifierImplNode4 FRNodeTarget4W`: green, 2,500 jobs, at a fresh
  snapshot of HEAD `67e5c76` with the three modules (`logs/S-CN4/build-final.log`).
- Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile`,
  `logs/S-CN4/prof-*.log`):

  | Module | wall (import ≈ 3.8 s) | type checking | interpretation | max RSS |
  |---|---|---|---|---|
  | `FRNodeTarget4` | 7.8 s | 0.29 s | 0.56 s (`decide`: `chLen_facts`, `chainLk4_ctrl`) | 2.80 GB |
  | `FRVerifierImplNode4` | 11.2 s | 0.80 s | 0.81 s | 2.82 GB |
  | `FRNodeTarget4W` | 8.5 s | 0.40 s | 0.52 s | 3.01 GB |

  The only `decide`s: `chLen_facts` (four inequalities per kind on constants), `chainLk4_ctrl`,
  three bounds in `shiftMask4_ctrl`, `nbN_bounds`. Nothing evaluates the layout, a table or a sum.
- **VM cost** (`logs/S-CN4/time-2.log`, compiled probe `logs/fr-build-SCN4/probe/SCN4Time.lean`,
  `taskset -c 7`, best of 40; F product 81 ns):

  | Op | N2 | N4 | N8 | 3.x (for comparison) |
  |---|---|---|---|---|
  | `shiftMask4I` | 0.378 ms | 0.380 ms | 0.387 ms | `shiftMaskI` 0.397 ms |
  | `linkWAll4I` | 2.066 ms | 2.171 ms | 2.194 ms | `linkWAll4I` 1.835 ms |

  `slotW` is 3.x's `slotWI` (unchanged). Possible cuts, not done: `shP` re-enumerates `Fin k` in
  `prodAt` at every level (O(nb³) list walks); an array form is O(nb²) (≈ 0.05 ms expected, not
  measured). `linkWAll4I` pays one table product per source read (2 × 1,046 sources); sharing
  `eq(τ,·)·eq(r,·)` per WOTS block (498 per slot) would halve it.

## 3. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `chainLk4` mask (`shiftMask4S`'s) | `chainLk4_ctrl`: block 0 and chain 1's second-to-last block are linked | `chainLk4_ctrl`: chain 0's last block and chain 1's last block are not |
| `lkE`, `lkSh` (`shiftMask4S`/`I`) | `lk_cube`; `shiftMask4_ctrl`: on `N4`, `Sh` at the Boolean points 0 → 1 is `1` | `shiftMask4_ctrl`: `Sh` at chain 0's last block → chain 1's start is `0` (3.x's unmasked shift gives `1`), `E` there is `0` |
| `lkE0` (start term, D10) | `lkE0_ctrl`: at `r = 0` the starts' weight is `1` (chain 0's start `1`, chain 1's `0`) | `lkE0_ctrl` is the non-vacuity: `E₀` is not the zero function, so the D10 term is live (dropping it, J = 9, changes the weight) |
| `linkW4S`/`linkWAll4S`/`I` | `linkW4_ctrl`: family `x` on `N4` reads `1` at its first source, field bit 0 (position 600) | `linkW4_ctrl`: position 601 (a wrong offset) reads `0` |
| `targetSNode4S`, `nodeE4` | `nodeE4_etN4` (it is `etN4`, whose controls are S-E12a's `nodeBK4_controls`, `nodeKind4_fin2`); `peL_node4` | `peL_node4` ties it to the PIOP's `P^e`; no evaluation control yet (comes with `targetSNode4I`) |
| `implN4`/`specN4` | `implN4_meets` | — (parameters `base`, `tS`) |
| `wSumNode4` | `wNS4_node4` | through `final_node4`, P4e's `res_ne_node4` (a failed `ShHoldsN4` leaves a nonzero residual) |

Axioms (`logs/S-CN4/axioms.log`): the 18 audited statements use `propext`, `Classical.choice`,
`Quot.sound` or a subset; no `sorryAx`. Source rule (`logs/S-CN4/source-rule.log`): 279 files,
1 finding, **in R4c's uncommitted `FRSoundness4R4FrE.lean:189` (`export`)**, none in this track's
modules.

## 4. Deviations

- **`slotW` has no 4.1 op.** The node's chain blocks keep 3.x's slot maps (`h_in` at `0 … 255`,
  `h_out` at `256 … 511`), so the kind-free `slotWI`/`slotWS` is right; `implN4` pins
  `slotW := slotWI`, `specN4` `slotWS`, so the node's specification fixes all four ops.
- **The ops dispatch on the kind index** (`implSeg`'s pattern): `targetS`/`linkWAll` take the
  4.1 node's form when `κ.isNode` (a node program's index is `N30`, `KindP.ofNode`) and `base ν`'s
  otherwise; `shiftMask` is the node's for every index.
- **D10 kept:** `shiftMask4S`'s `E₀ = eq(r,0) + eq(r,chLen₀)`, matching `wNode4`'s `shN4` (J = 10).
- **`implN4` takes `tS`** (see the handover): `implN4_meets` needs `tS ν = targetSNode4S ν`.

## 5. For P4/X4 (how `hNS4` is discharged)

`hNS4` is `rfl` today (`wNS4` is the extension by definition). It is now a theorem about the node
ops: **`wNS4_node4 ν es : wNS4 (.node ν) es = wSumNode4 ν es`**. X4's chain:
1. R4c's `flag_gFinSh` gives `relSh4 impl κ inp fi r P` for the node program, `impl = implN4 base tS ν`.
2. `implN4_meets ν hbase htS` turns `impl.shiftMask`, `impl.slotW κ 0/2`, `impl.linkWAll κ` into
   `shiftMask4S ν`, `slotWS 0/2`, `linkWAll4S ν` (`P.vn = false`, `P.kv.node κ = true`, so
   `relSh4`'s `e`, `sh`, `e0` are `shiftMask`'s and `sIn` is `slotW κ 2`).
3. With the registers at the log's values (`τ` = `pad18 (tauL)`, `r_blk` = `pad18 (rbL)`,
   `tt = (tauL ++ thL).toArray`, `rr = (rbL ++ rpL).toArray`, `θ = thL`, `r_pos = rpL`,
   `κ_s = ksL`; R4's register readings, as for the segment's `wSumSeg`), `relSh4`'s
   `w_out + w_in` is `wSumNode4 ν es` (`linkSum_eq8` gives the closed sum).
4. `wNS4_node4` rewrites it to `wNS4 (.node ν) es`, so the program asserts P4c's
   `oSh4 wNS4 (.node ν) es`.
5. Z2 on a node: `peL_node4` (`targetSNode4S` at Z1's point is the PIOP's `P^e`), once `tS` meets
   `targetSNode4S`.

`FR.lean`: add `import FRNodeTarget4W` (it pulls `FRNodeTarget4`) and
`import FRVerifierImplNode4`.

## 6. For S-E12c (op shapes for the templates)

- **`shiftMask4I ν τ r`** (operands 18 entries, the first `nb` read): per coordinate the four
  factors `mF l b b' = eq(τ_l,b) eq(r_l,b')` (4 products); `prefixP nb` on `mF l b b`
  (`n(n+1)/2` products); `shP nb` (a sum of `nb` `prefixP`s on suffixes, O(nb³) as written, O(nb²)
  with suffix arrays); 4 `eqAtR` at constants (`chLen₀ − 1`, `chLen₀`, `0`); 2 subtractions.
  Constants per kind: `chLen ν 0`, `chLen ν 0 + chLen ν 1 − 1`.
- **`linkWAll4I ν tt rr`** (`nb + 10` entries each; output 8 F): `eqTable` of 9 and `nb − 9`
  coordinates for `τ` and `r_blk` (`bt`), 3.x's `tab10` for `θ`, `r_pos`, `Eθ` (256 entries); per
  family `SW` (`fbits` products), `MI` (`fbits`), `MS` (4); per source `t` of each slot: 3 table
  reads (`srcB4` twice, `mirB4`), 4 products. Sources per slot 399 + 400 + 67 + 66 + 66 + 16 + 16 +
  16 = 1,046. Block addresses: `wotsB ν σ + src t` and `wmB ν σ + ⌊mir t / 4⌋`.
- **`slotW`**: 3.x's `slotWI` (template unchanged).
- **`targetS`**: pending (`targetSNode4I`, below).

## 7. Open questions

1. `FR.lean` imports (§5).
2. R4c's source-rule finding (`FRSoundness4R4FrE.lean:189`, the word `export`).
3. Should `shP` be rewritten in array form now (≈ 0.3 ms per node verification)?

## 8. Handover (remaining, in order)

1. **`targetSNode4I ν r` and `targetSNode4_meets : targetSNode4I ν r = targetSNode4S ν r`**, in a new
   module (`FRVerifierImplNode4T`, or extend `FRVerifierImplNode4`). Plan (3.x:
   `FRNodeTarget` `targetSNode_blk`/`Gc`/`blkW_eq`, `FRVerifierImplNode` `targetSNodeI`):
   - `P^e(σ) = Σ_{hi<256} eq(zLo r, hi)·G(σ + 64 hi)`, `G(p) = Σ_{blk<2^nb} eq(r_blk, blk)·nodeE4 ν blk p`
     (3.x's `targetSNode_blk` over `8 + nbN ν`).
   - Split `G` by the interval list: a generic lemma from `N4c.layout_contig`
     (`Σ_{blk < blocks} f blk = Σ_{iv ∈ nodeLayout4 ν} Σ_{o < hi − lo} f (lo + o)`) and
     `N4c.tgt_of_mem` (a block's target is its interval's `tgt`). No evaluation of the layout.
   - Closed form per piece: each chain (`streamStart`; body `streamTarget bytes (o+1)`: counter
     `64 (o + 2)` for `o < chLen − 2`, the last block final with `t = chBytes`, need
     `nBlocks (chBytes ν σ) = chLen ν σ`, `N4c.aggL_nBlocks`), `hashStmt` per verifier slot, each
     WOTS run (3.x's `wots_part` with `wb σ` → `wotsB ν σ`, generalise its proof over the weight
     `g`), the tail (`maxK − 1` final candidates `blockTarget (aggB (j+1)) true`, then `hashA`),
     `free` = 0. New bit lemma: `tgtE (blockTarget t fin) p = tgtE (blockTarget 0 fin) p +
     [1024 ≤ p < 1056] bit (p − 1024) of t` for `t < 2^32` (3.x's `tgtE_ctr` without `64 ∣ t`).
   - Computed form: `bt`-style tables of `r_blk` with prefix arrays over 512 (port 3.x's `pfx`,
     `twoF`, `sepSum`, `ctrI` from base 256 to base 512), the constant classes as precomputed bit
     tables (3.x's `clsTab`, plus `blockTarget 0 true`), `G` on `p < 1153`, then the 64 outputs.
   - Controls: a Boolean block point reads that block's target; a `free` block point gives `0`.
   - Then instantiate `implN4 base (fun ν => targetSNode4I ν) ν` and measure it.

## Pass 2 (track S-CN4b, 2026-10-28): `targetSNode4I`, `implN4T`, the two speed-ups, `rsWeight`

HEAD at start `c2c6fba`, re-snapshotted at `1ee751b` (S-T2) for the `rsWeight` wiring. Build tree
`logs/fr-build-SCN4b` (copy of `fr-build-SCN4`, `logs/org20`; `b.sh` = snapshot + capped build +
the probe `scn4btime`). Logs in `logs/S-CN4b/`. Every lake/lean command in the 16G scope under
`timeout`. No sub-agents, nothing committed. Names grepped first (namespaces `FR.NT4C`, `FR.NI4T`
are new). Statements of S-CN4's theorems unchanged (`shiftMask4_meets`, `linkWAll4_meets`,
`implN4_meets` keep their text; see "Deviations" for `specN4`).

### P2.1 What was built

| Module | total / code / thm | Content |
|---|---|---|
| `FRNodeTarget4C` (new, `FR.NT4C`) | 536 / 402 / 35 | **`tgtE_fin`** (the new bit lemma, any `t < 2^32`); `tF`, `blkW4`, `ivS`; **`sum_contig`** (a sum over a tiled range is the sum over the tiles); **`blkW4_layout`** (from `layout_contig` + `tgt_of_mem`, no evaluation of the layout); pieces `body_sum`, `fin_one`, `chain_piece`, `stmt_piece`, `wots_map`/`wots_piece` (3.x's `wots_part` at `wotsB`, any weight), `fin_target`, `tail_piece`; closed form `clsW`, `ctrS`, `ctrG`, `finG`, `stepG`, **`Gc4`**; **`blkW4_eq`** (`G = Gc4`, any block weight), `Gc4_hi`, `targetSNode4_blk`, **`targetS_node4_eq`**; `lay_bounds`, `lastB_lt`, `clsW_congr`, `finG_congr`, `stepG_congr` |
| `FRVerifierImplNode4T` (new, `FR.NI4T`) | 533 / 404 / 29 | base 512: `pfx9`, `twoF9`, `sepSum9`, `tabs9` (over S-CN4's `bt`), `eq9`, `rangeI9`; counters `colT`, `sepD`, `cc`, `eOf`, `ctrK`, `ctrArr` (+ `_eq`s); `clsTab4`, `clsBit4`, `gAt4`, `gArr4`, `rbArr`, **`targetSNode4I`**, `gArr4_eq`, **`targetSNode4_meets`**; **`implN4T`**, **`implN4T_meets`**; controls |
| `FRVerifierImplNode4` (S-CN4's, edited) | 498 / 383 / 21 (was 367 / 281 / 15) | `prodTo`, `prodQ`, `prefixQ`, `shQ` (+ `_eq` to `prodAt`/`prefixP`/`shP`), `mArr`, `mQ`: **`shiftMask4I`** in loop/array form; **`linkWOneF`** (+ `linkWOneF_eq`): **`linkWAll4I`** with per-block shared products; `implN4`/`specN4`/`implN4_meets` through S-T2's `Impl.withRS4`/`withRS4S`/`withRS4_meets` |
| total | 1,567 / 1,189 / 85 | `logs/S-CN4b/loc.txt` |

**Main statements.**

```lean
theorem tgtE_fin {t p : ℕ} (ht : t < 2 ^ 32) (hp : p < 2 ^ 14) (fin : Bool) :
    tgtE (blockTarget t fin) p = tgtE (blockTarget 0 fin) p +
      if 1024 ≤ p ∧ p < 1056 then bF (t.testBit (p - 1024)) else 0
theorem sum_contig (f : ℕ → F) : contig ivs a b = true →
    ∑ x ∈ range (b - a), f (a + x) = (ivs.map fun iv => ∑ o ∈ range (iv.hi - iv.lo), f (iv.lo + o)).sum
theorem blkW4_eq (ν) (w : ℕ → F) (hp : p < 2 ^ 14) : blkW4 ν w p = Gc4 ν w p
theorem targetS_node4_eq (ν) (r : Array F) : targetSNode4S ν r = Array.ofFn (n := 64) fun σ =>
    ∑ hi ∈ range 19, eqAtR (zLo r) hi * Gc4 ν (eqAtR (rbOf4 ν r)) (σ + 64 * hi)
theorem targetSNode4_meets (ν) (r : Array F) : targetSNode4I ν r = targetSNode4S ν r
def implN4T (base : NodeKind → OpImpl) (ν) : OpImpl := implN4 base (fun ν => targetSNode4I ν) ν
theorem implN4T_meets (ν) (h : (base ν).Meets (spec ν)) : (implN4T base ν).Meets (specN4 spec ν)
```

**`Gc4 ν w p`** (`w` any block weight; `w = eq(r_blk, ·)` for `targetS`): `Σ_{c<10} clsW c ·
tgtE(cls4 c, p)` + `[1030 ≤ p < 1056] ctrG (p − 1030)` + `[1024 ≤ p < 1056] finG (p − 1024)` +
`w43`'s two step fields. `cls4` is 3.x's `cls` with class 2 the counter-free final block
`blockTarget 0 true`. Class weights: 0 `streamStart` (both chain starts); 1 stream bodies (both
chain bodies `[chBase σ + 1, + chLen σ − 2)`, both key leaves `[wotsB σ + 400, + 65)`); 2 final
blocks (`lastB ν σ = chBase σ + chLen σ − 1`, the tails' candidates `[finB a, + maxK − 1)`);
3 `hashA` (`stmtB + 3v`, `cAB a`); 4 `hashB1 tagNode`; 5 `hashB2` (statements, paths); 6 `w43`;
7 `hashB1 tagWotsLeaf`; 8 `streamEnd41`; 9 `hashB1 tagSigNode`. `finG j` = `Σ_σ w(lastB σ) bit_j
(chBytes σ) + Σ_a Σ_i w(finB a + i) bit_j(aggB (i + 1))`.

### P2.2 Build, kernel, VM times

- `lake build FR FRNodeTarget4 FRVerifierImplNode4 FRNodeTarget4W FRNodeTarget4C
  FRVerifierImplNode4T FRVerifierImplOps4`: green, 2,508 jobs, snapshot of HEAD `1ee751b` with
  the five modules (`logs/S-CN4b/build-final.log`).
- Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile`,
  `logs/S-CN4b/prof-*.log`; import ≈ 3.9 s): `FRNodeTarget4C` 13.5 s wall, type checking 1.65 s;
  `FRVerifierImplNode4T` 12.7 s, 1.52 s; `FRVerifierImplNode4` 16.9 s, 1.19 s (S-CN4: 11.2 s,
  0.80 s). Max RSS 2.77 GB. No declaration over 0.35 s. The only `decide`s are on constants
  (`chain_facts`, `maxK_le`, `lay_bounds`' `hEnd ≤ 2^nb`, the controls' bits); nothing evaluates
  the layout, a table or a sum.
- **VM** (`logs/S-CN4b/time-4.log`, compiled probe `logs/fr-build-SCN4b/probe/SCN4bTime.lean`,
  `taskset -c 7`, best of 40; F product 82 ns, F addition 3.7 ns):

  | Op | N2 | N4 | N8 | 3.x | S-CN4 |
  |---|---|---|---|---|---|
  | `targetSNode4I` | 1.503 ms | 1.670 ms | 1.799 ms | `targetSNodeI` 1.932 ms | — |
  | `shiftMask4I` | 0.130 ms | 0.127 ms | 0.129 ms | `shiftMaskI` 0.395 ms | 0.38 ms |
  | `linkWAll4I` | 1.694 ms | 1.799 ms | 1.815 ms | `linkWAllI` 1.849 ms | 2.07–2.19 ms |

  `targetSNode4I`'s path to this (`time-1` … `time-3`): 3.26–3.75 ms with a 512-entry prefix
  array per counter bit (the counters were 2.3 ms); `colT` (one pass over the columns cut at the
  range's ends, the carry classes shared by all bits, rows summed directly) and short bodies
  (`n < 512`: the key leaves) straight from their `eq` values brought it to 1.5–1.8 ms. Now:
  `tabs9` 0.22–0.27 ms, one chain's counters 0.25 ms (N8: 0.38), the `gAt4` loop over 1,153
  positions ≈ 0.4 ms, the final `Σ_hi` ≈ 0.1 ms.

### P2.3 Controls

| Definition | Positive | Negative |
|---|---|---|
| `targetSNode4I` | `targetSNode4I_blk`: at a Boolean block point `b` it reads block `b`'s target bits `nodeE4 ν b` | `targetSNode4I_free`: at a block point past `hEnd` it is `0` |
| `Gc4`/`nodeE4` (evaluated, `N4`) | `nodeE4_ctrl`: chain 0's block 1 reads counter bit 7 (`t = 128`); chain 1's last block reads `t`'s bit 0 (`aggB 4` is odd: not a `64k` counter) and the final flag; the tail's `F_{0,1}` reads the flag and bit 13 of `aggB 1 = 0x16A000` | `nodeE4_ctrl`: block 1's bit 6 is `0`; chain 1's second-to-last block's flag is `0`; `F_{0,1}`'s bit 12 is `0` |
| `blkW4` | `blkW4_cube` (Boolean point reads the block) | through `targetSNode4I_free` |
| `implN4T` | `implN4T_meets` | — (parameter `base`) |

Axioms (`logs/S-CN4b/axioms.log`): 23 statements, each `[propext, Classical.choice,
Quot.sound]`. Source rule (`logs/S-CN4b/source-rule.log`): 293 files, 0 findings.

### P2.4 Deviations

- **`implN4T` instead of changing `implN4`'s signature**: `implN4 base tS ν` and `implN4_meets`
  (with `htS`) stay; `implN4T base ν := implN4 base targetSNode4I ν`, `implN4T_meets` has no `tS`
  hypothesis.
- **`rsWeight` (coordinator's request, S-T2 §6, in place):** `implN4` is `{ Impl.withRS4 (base ν) ν
  with … }`, `specN4` `{ Impl.withRS4S (base ν) ν with … }`, `implN4_meets` destructures
  `Impl.withRS4_meets ν h`. `implN4_meets`' text is unchanged, but **`specN4`'s `rsWeight` is now
  `rsWeightS4 ν`** (3.x's `rsWeightS` was the wrong spec for 4.1 nodes, S-T2's `kwS4_ne_3x`).
  `FRVerifierImplNode4` imports `FRVerifierImplOps4`. R4d's uncommitted `FRSoundness4R4FrS`
  (`nodeOps_of_meets`) reads `specN4`'s `shiftMask`/`linkWAll` fields only; I could not build it
  (it is not in HEAD).
- `shiftMask4I`/`linkWAll4I` are new definitions (same statements of `_meets`). `shiftMask4I` is
  now `prefixQ`/`shQ` (index-shifted, `Nat.fold` products) over `mArr`; `linkWAll4I` is
  `linkWOneF` over per-slot arrays. The old `linkWOne4` stays as the proof's reference.
- `Gc4` is in class-weight form (not 3.x's per-piece `Gc`), so the computed side is a direct
  congruence (`clsW_congr`, …) with no `ring`.

### P2.5 Open questions

1. `FR.lean`: add `import FRVerifierImplNode4T` (pulls `FRNodeTarget4C`, `FRVerifierImplNode4`,
   `FRVerifierImplOps4`) and `import FRNodeTarget4W`.
2. Whoever instantiates the node's ops (INT-8/X4) should use `implN4T base ν` (and
   `implN4T_meets`), not `implN4 base tS ν`.
3. Further cuts, not done: `gAt4` (0.4 ms: 10 nested-array lookups per position; a flat table or
   per-position class lists); `linkWAll4I`'s field weights `SW`/`MI` (≈ 3 products per field bit
   per family, now its largest part); `shQ` is `O(nb³)` (suffix products would make it `O(nb²)`).

### P2.6 For S-E12d (the op shapes for the template)

- **`targetSNode4I ν r`** (operand: `r[0]` and `r[1 … nb]`; output 64 F):
  1. `zLo r` → `eqTable` (256 entries); `rb = r[1 … nb]` → `bt nb` (`A`: 512, `B`: `2^(nb−9)`),
     prefix arrays `PA`, `PB` (513 entries each, additions).
  2. Ten class weights `W_c` (`clsW` at `eq9`/`rangeI9`): single blocks (one product each,
     `eq9 x = A[x mod 512]·B[⌊x/512⌋]`), ranges by `sepSum9` (4 products). Blocks read: chain
     starts `chBase σ`, bodies `[chBase σ + 1, + chLen σ − 2)`, last blocks `lastB σ`, statements
     `stmtB + 3v + {0,1,2}` (`v < vslots`), WOTS `wotsB σ + {0…398 (range), 399, 400…464 (range),
     465, 466 + 2t, 467 + 2t}`, tails `[finB a, + maxK − 1)` (range) and `cAB a`.
  3. Counter bits `CT[0…25]` (positions 1030…1055): per body `ctrArr` — key leaves (`n = 65`)
     directly from 65 `eq9`s; chains by `ctrK`: bits `j < 9` one column pass (`colT`, cut at
     `lo mod 512`, `(lo+n) mod 512`) with mask `bit_j((l + eOf lo) mod 512)`, rows
     `[⌊lo/512⌋, ⌊(lo+n)/512⌋)` summed directly (`sepD`, 3 products); bits `j ≥ 9`: two carry
     classes' column sums (`cc`, once per body), row masks `bit_{j−9}(h + ⌊e/512⌋ (+1) − Q)`; `0`
     once `2^j > n + 1`.
  4. Final-block bits `FB[0…31]` (positions 1024…1055): `Σ_σ eq9(lastB σ)·bit_j(chBytes σ) +
     Σ_a Σ_i eq9(finB a + i)·bit_j(aggB (i+1))` (constants per kind: `chBytes ν σ`, `aggB k`).
  5. `w43` fields `WI[0…7]`, `WS[0…7]` (positions 584…599): 2 × 399 `eq9` products, masked sums by
     `⌊o/3⌋`, `o mod 3`.
  6. `G[p]` for `p < 1153`: `Σ_c [clsBit4 c p] W_c + CT + FB + WI + WS` (`clsTab4`: 10 × 1153
     constant bits, class 2 = `blockTarget 0 true`); then `out[σ] = Σ_{hi<19} eqTable[hi]·G[σ + 64 hi]`.
  Constants per kind: `nb`, `chBase/chLen/chBytes ν σ`, `stmtB`, `vslots`, `wotsB ν σ`, `nAgg`,
  `finB ν a`, `cAB ν a`, `maxK`.
- **`shiftMask4I`**: as S-CN4 §6, but `prefixP`/`shP` are `prefixQ`/`shQ` over `mArr` (4 factors per
  coordinate, `4 nb` products once); `prodQ` a loop.
- **`linkWAll4I`**: per slot `σ`: `Eτ[o] = eq(τ, wotsB σ + o)` (498), `EP[o] = Eτ[o]·eq(r, wotsB σ +
  o)` (498), `EM[o] = eq(r, wmB σ + o)` (146); per family `f`: `SW`, `MI`, `MS[c]` as before, then
  `Σ_σ SW·Σ_t EP[src t] − Σ_t Eτ[src t]·EM[⌊mir t/4⌋]·MS[mir t mod 4]` (2 products per source).
