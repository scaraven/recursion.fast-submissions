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
