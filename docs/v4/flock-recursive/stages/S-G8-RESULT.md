# S-G8 RESULT (pass 1): Z's and the leaf's L bindings, `zlmFR`, `accept_fields`; handover

- **Base.** HEAD `0751f44`.
- **Build tree.** `logs/fr-build-SG8`: a copy of `fr-build-SG7`, `.lake` included, so nothing was
  rebuilt from scratch. `snap.sh` symlinks `FRSoundnessFr*`, `FRSoundnessAccSem` and
  `FRSoundnessAccLog` to the worktree.
- **Records.** Logs are in `logs/S-G8/`; the journal is `S-G8-JOURNAL.md`.
- **Constraints.** Every lean/lake command ran in a capped scope (16G for builds, 12G for single
  files) with a `timeout`. No sub-agents were used. Nothing is committed.

## Status

**Done:**
- **Item 1.** `pendZ_pendBad`.
- **Item 2.** `zlmFR`:
  - Z's statement against `truthZN` (node) and `truthZ` (leaf, as an iff);
  - `peL` against `targetS`;
  - `Bits` and `IndKinds`;
  - the leaf's `pendLc_pendBad` and `rejLc2_ok`.
- **Item 3.** `accept_fields` strengthened. This is a statement change that only adds
  information (§4.1).

**Not done:** items 4–7. §5 gives them in order.

**Builds and checks:**
- `lake build FR` is green (2,386 jobs, `logs/S-G8/build-FR.log`), including the changed
  `FRSoundnessAccSem` and `FRSoundnessAccLog`.
- `lake build FRSoundnessFrZM` is green. No `sorry`.
- Axioms (`logs/S-G8/axioms.log`, all 61 theorems of the two new modules plus `fields_ok` and
  `accept_fields`): only `propext`, `Classical.choice` and `Quot.sound` (51 use all three,
  4 `[propext, Quot.sound]`, 6 `[propext]`).
- Source rule (`logs/S-G8/source-rule.log`): 168 files, 0 findings.

**Imports for `FR.lean`'s owner.** Add `import FRSoundnessFrZM`. It imports `FRSoundnessFrBind`,
which imports `FRSoundnessFrL` and `FRSoundnessFrS`.

## 1. What was built (code lines from `scripts/loc.py`, `logs/S-G8/loc.log`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrBind` (new) | 127 / 99 / 6 | `zZ_eq`, `cwL_zero`, `zPtL_length`, `zrL_drop`; **`trueL_zero`** (RS claim 1's true value is `P^z(λ)` at Z1's point); **`pendZ_pendBad`** |
| `FRSoundnessFrZM` (new) | 570 / 438 / 53 | the pins (`blockTarget_isNone`, `kindTarget_isNone`, `pins_*`, **`nodeKind_pins`**, `pins_chain`); `chained_unique`, **`ind_iff`**; **`zlmFR`** (`bkOf`, `bkIdx`, `kMat`, `jOf`), `zlmFR_bits`, `zlmFR_indKinds`; `zHolds_iff_blocks`, **`zHolds_iff_truthZN`**, **`zHolds_iff_truthZ`**; `peL_range`, `zrL_append`, **`peL_node`**, **`peL_leaf`**; **`trueL_one`**, `zfL_leaf`, **`pendLc_pendBad`**, **`rejLc2_ok`**; controls |
| `FRSoundnessAccSem` (changed) | 199→217 / 158→171 | **`exAt`**; `fields_ok` and **`accept_fields`** with the witnesses (§4.1) |
| `FRSoundnessAccLog` (proof repair) | 523→528 / 435→440 | `finLog_of_run` rebuilds the old existential form after the call |

### The statements

```lean
theorem trueL_zero (L es : Log) : trueL (kindOf es) L es 0 = (pzT L es).eval (lamL es)
theorem pendZ_pendBad {oSh} {L es : Log} (h : PendZ L es) : PendBad (okRS oZ oSh) L es

noncomputable def zlmFR : ZLM where
  Ak := kMat Block.circuitR1CS.A          -- 0 on the kind's zeroRows; free: identity; else circuit row
  Bk := kMat Block.circuitR1CS.B
  Ind κ j t := if κ.isNode then (if bkOf j = nodeBK t then 1 else 0) else (if j.val = 0 then 1 else 0)
  Et κ t p := if κ.isNode then NodeT.nodeE t p.val else chainE p.val
theorem zHolds_iff_truthZN {L es} (hn : kindOf es = .N30) :
    ZHolds zlmFR L es ↔ truthZN (kindOf es) L es
theorem zHolds_iff_truthZ {L es} (hn : (kindOf es).isNode = false) :
    ZHolds zlmFR L es ↔ truthZ (fun _ => Chain.chainTarget) (2 ^ qL (kindOf es)) (kindOf es) L es
theorem peL_node {es} (hn : kindOf es = .N30) {r : Array F}
    (hr : ∀ l < 17, r.getD l 0 = coordAt es 2 l) : NodeT.targetSNodeS r = Array.ofFn (peL zlmFR es)
theorem peL_leaf {es} (hn : (kindOf es).isNode = false) {r : Array F}
    (hr : ∀ l < 17, r.getD l 0 = coordAt es 2 l) : targetSLeafS 16 r = Array.ofFn (peL zlmFR es)
theorem ind_iff {blk} (h : blk < nodeBlocks) (b : BlockKind) : Ind b blk = true ↔ b = nodeBK blk
theorem zlmFR_bits : zlmFR.Bits
theorem zlmFR_indKinds : zlmFR.IndKinds
theorem trueL_one (L es : Log) : trueL (kindOf es) L es 1 = ∑ t ∈ range (2 ^ qL (kindOf es)),
    ∑ j ∈ range (2 ^ 14), eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * zW (kindOf es) L es (j + 2 ^ 14 * t)
theorem pendLc_pendBad {oZ oSh} {L es} (h : PendLc zlmFR L es) : PendBad (okRS oZ oSh) L es
theorem rejLc2_ok (M : ZLM) (hp : fsItems[97]? ≠ some .squeeze) : RejOK (RejLc2 M)
```

- **`zlmFR` is the verifier's shape.**
  - The masks are A.6's `zeroRows`, which is what `maskRows` applies.
  - `free` is the identity, A.6's `(var k, var k)`.
  - The node's indicator is `nodeBK`; `ind_iff` shows it equals `nodeLayout`'s `Ind`.
  - The targets are `nodeE` (`targetSNodeS`'s) and `chainE` (`targetSLeafS`'s).
- **A consistency check came out clean.** `nodeKind_pins` proves that every target `nodeKind`
  assigns pins exactly the rows that `zeroRows (nodeBK blk)` lists. These are the A.6 table the
  verifier masks with and the block targets of `FRBlockKinds`/`FRBlockStream`. No discrepancy
  was found.
- **`truthZN` and `truthZ` reduce to `ZHolds` both ways.** For the free blocks, `z² = z` holds
  on bits (`zBk_bit`). The leaf's `SL` (ruled: `ShHoldsL ∧ ZHolds`) can take
  `ZHolds zlmFR`, and `zHolds_iff_truthZ` hands S-H2l `leaf_of_truthZ`'s hypothesis.
- **`peL_*` is stated for any register array `r` with `r[l] = coordAt es 2 l` (`l < 17`).** That
  is Z1's coordinate register, which the verifier passes as `(coordsOf …).toArray`
  (`FRVIRSpec:564`). Item 5 supplies the register view.
- **An `L32` leaf's two high block coordinates sum out**, because `chainE` does not depend on the
  block.

## 2. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`). Logs are `logs/S-G8/time-<module>.log` / `.rss`.

| Module | Wall (import ≈ 3.9–5.5 s) | Type checking | Max RSS |
|---|---|---|---|
| `FRSoundnessFrBind` | 9.1 s | 1.35 s | 2.93 GB |
| `FRSoundnessFrZM` | 40.6 s (`simp` 23 s, mostly the `pins_*` case splits) | 4.25 s | 3.11 GB |
| `FRSoundnessAccSem` | 10.7 s | 0.10 s | 2.77 GB |
| `FRSoundnessAccLog` | 35.0 s | 1.21 s | 2.92 GB |

**`decide` uses.** None runs over a program, a table or the item list. The `decide`s are:
- `m24` (three kinds);
- `jOf_controls` (a `BlockKind` inequality);
- `hb : chain ≠ free`.

The pins are proved by `omega` on intervals, not by enumerating positions. Uniqueness of the
kind uses `nodeLayout_chained`, which already existed.

## 3. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `zlmFR.Ind` (`jOf`) | `ind_jOf_self` (a block's own kind has indicator 1) | `ind_ne` (every other kind has 0); `jOf_controls` (node block 0 is `streamStart`, not `chain`) |
| `kMat` | `kMat_row` (an unpinned row of `stream` is the circuit's row); `kMat_free_id` (`free` is the identity) | `kMat_pinned` (`chain`'s row 0, `h_in`, is zero) |
| `zlmFR` as a whole | `zHolds_iff_truthZN`, `zHolds_iff_truthZ` (equivalent to the independent per-block statements) | the same iff theorems (a block violating its R1CS falsifies `ZHolds`) |
| `bkOf`/`bkIdx` | `bkOf_idx` | `bkOf_eq_iff` (no other index gives the kind) |
| `exAt` | `accept_fields` (the verifier's own fold) | — (definitional mirror of `runFields`) |

## 4. Deviations, findings and statement changes

1. **Statement change in `FRSoundnessAccSem` (R-V-m2). It only adds information.** The old
   form was:
   `(∃ Rk exk L, … finRS ⟨outs, [], exk⟩ …) ∧ ∃ zh, ∀ k hk, ∃ Rk exk L, … rest[k] ⟨outs, zh, exk⟩ …`.
   The new form is:
   `(∃ Rk L, … finRS ⟨outs, [], #[]⟩ …) ∧ ∀ k hk, ∃ Rk L, … rest[k] ⟨outs, zhRS, exAt outs zhRS
   fin.rest (next + opsOut finRS) #[zhRS] k⟩ …`, with `zhRS = (fin.finRS ⟨outs, [], #[]⟩
   skeleton.2.next).2`.
   - `fields_ok` changes in the same way: `exk := exAt outs zh fs R.size ex k`.
   - The old statement follows from the new one by forgetting. `FRSoundnessAccLog` does exactly
     that, in 4 lines, as a proof repair.
   - `FRSoundnessAccVal` is unaffected.
2. **The node's L stays parked** (INT-5, blueprint 3.16). `zlmFR` is defined for all kinds, so
   the node's Z (Z1–Zend, L1, L2) is fully instantiated. Only L3/L3β, the node's `RejLc2` and the
   Lc → RS0 link need INT-5's relations. §5, item 4 gives the hypothesis's intended shape.
3. **`ind_iff` versus the verifier's `kindIndSpec`.** The verifier evaluates
   `mle (selOf (kindIvs κ))`. `ind_iff` relates `Layout.Ind` (the same intervals, as `List.any`)
   to `nodeBK`. A lemma `selOf (kindIvs κ) t = ofBool (Layout.Ind κ t)` is still needed for the
   node's L. It is a small list lemma, for whoever writes the node's L3.

## 5. Handover: what is left, in order

Positions: Z1 3–12, Z2 13–14, Z3 15–66, Zend 67, L1 68, L2 69–96, L3 97, L3β 98, S1 99–113, S2
114–169, Lr1 170–177, Lr2 178–207, Lrend 208, Lr3 209, E1 210–220, E2 221–262, Eend 263, E3 264,
E4 265–310, E4end 311, RS0 312, RS1 313–316, B′ 317, P1.0 318.

Use `M := zlmFR` throughout. Its hypotheses are discharged: `zlmFR_bits`, `zlmFR_indKinds`. The
bridges at RS0 are:
- `pendZ_pendBad` (claim 1);
- `pendLc_pendBad` (claim 2, leaf);
- `pendS_pendBad` (claim 3);
- `pendE_pendBad` (claim 4).

1. **Item 4: assembly.**
   - **`DF k`.** For each phase, `DF k := Bg_k ∨ U_k`, with `DF 2 := far₀ ∨ ¬ Stmt fin SL` and
     `SL κ L es := ShHoldsL … ∧ ZHolds zlmFR L es`.
     - Z1's `hprev` needs `¬ Stmt → ¬ ZHolds zlmFR ∨ Bg`. Get it from `zHolds_iff_truthZN`
       (node; `StmtN`'s first conjunct) or from `SL`'s second conjunct (leaf).
     - The background terms carry, in order:
       - `far₀`, `¬ PubOK`, and the not-yet-reduced statement parts;
       - `PendZ` from Z3 on (`Reads 15`);
       - the leaf's `PendLc` from L3β on (`Reads 99`);
       - `D2S` from Lr1 on (`Reads 170`);
       - Lr's `BatBad` into E3;
       - `PendE` from E4 end.
     - At 312, `DF 22 → DPend (okRS oZ oSh)` (`habs_RS0` takes `DPend` as a hypothesis), using
       the four bridges above.
   - **`RejF`.** `rejOK_or` of:
     - `RejZ zlmFR` (`rejZ_ok`);
     - `RejL2` (`rejL2_ok`);
     - `RejLc2 zlmFR` (`rejLc2_ok`);
     - `RejS2` (`rejS2_ok`);
     - the `RejEnd`s (`e_rejEnd_ok`);
     - `RejInE`, `RejE4`;
     - `RejRS (okRS oZ oSh)` (`rejRS_ok` with `okRS_reads oZ_reads oSh_reads`);
     - the node's L hypothesis (below).
   - **`FrontObl`.** Use one checked classification of positions 0 … 317 (as `tailCls_check`).
     It discharges the `fsItems` hypotheses at 67, 69 + 2j, 97, 114 + 2j, 263, 265 + 2j and 312.
   - **`FrontChainStab`.** Build it from `Reads.chain`.
   - **The node's L as one named hypothesis** (suggested shape: a structure `NodeL RejN L3N PendN`).
     Its fields:
     - `RejOK RejN`;
     - `Reads 98 L3N`;
     - `Reads 99 PendN`;
     - `habs` at 97: `D2L zlmFR L es → RejN ∨ L3N` on a node;
     - L3β's single count ≤ 8·2^128;
     - `PendN → PendBad (okRS' …)` at claim 2;
     - `hFront`'s part: the accepted run gives `¬ RejN`.

     If INT-5 changes the Lc binding (`W_β`), the `okRS` claim-2 binding `v = vBetaL` must
     follow. So keep `okRS`'s Lc binding a parameter in the hypothesis, or wait for INT-5's
     relations.
2. **Item 5: `hW0`, `hStart`, `hFront`** (S-G5 §5 items 8–10).
   - Use the new `accept_fields`: field `k` runs with `zhat = finRS`'s exports and
     `ex = exAt …`.
   - For Z: `relZ` gives `¬ RejZ zlmFR` and `oZ`. Z2's `targetS` operand is Z1's coordinate
     register; `peL_node`/`peL_leaf` turn it into `peL zlmFR` once the register view
     `r[l] = coordAt es 2 l` is shown.
   - For S: `relSh` against `c0S`/`oSh` through `implC_meets` and the register views.
   - For E: `finE` (iv)–(v) gives `¬ RejE4`.
   - For the leaf's Lc: `finLc` gives `¬ RejL2`, `¬ RejLc2`, and `v = vBetaL` at claim 2.
3. **Item 6: `kstate_front`.**
   - Compose `kstate_of_front` with `FrontObl`.
   - Compose `finalLaw_of_run`/`hAcc_of_fin` with `hExt_of_iface`.
   - Remaining hypotheses: `ExtIface` (with `SL`), the `implC` facts, and the node's L.
4. **Item 7: final checks.** The axioms of `kstate_front` and the source rule. The source rule
   was run this pass: 168 files, 0 findings.

## 6. Open questions

1. Is the `FRSoundnessAccLog` proof repair acceptable under item 3's scope? It touches no
   statement.
2. **`SL` for S-H2l/S-E.** Proposal: `SL κ L es := ShHoldsL (m−14) (zNode κ L es) (sbL κ es)
   (hbL κ es) ∧ ZHolds zlmFR L es`. `zHolds_iff_truthZ` gives them the per-block `truthZ` form.
