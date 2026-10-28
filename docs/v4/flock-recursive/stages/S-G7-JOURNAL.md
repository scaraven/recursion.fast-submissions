# S-G7 JOURNAL: the PIOP front, continued from S-G6's handover

- Base HEAD: `3175db2`.
- Build tree: `logs/fr-build-SG7`.
  - Copied from `fr-build-SG6`'s scripts. Its `.lake` was copied from `fr-build-INT4`, which holds HEAD's oleans, so nothing was rebuilt.
  - `snap.sh` takes HEAD's sources and symlinks every `FRSoundnessFr*` to the worktree.
  - `c.sh` compiles one module (`lake env lean`) under a 12G cap; `errs.py` filters the errors.
- The fork (items 2–3) used its own tree, `logs/fr-build-SG7z`.
- Every lean/lake command ran in a capped scope (16G for builds, 12G for single-module checks) with a `timeout`.
- Logs are in `logs/S-G7/`. Nothing is committed.

## Organisation

- I spawned one fork for items 2 (L) and 3 (Z), with its own build tree. Its notes are in `logs/S-G7/ZL-notes.md`.
- I did item 1 (S) myself. At most two Lean processes ran at a time.

## Item 1: S

### The bridge (`FRSoundnessFrSh`, new, pure algebra)

- **Design.**
  - The S2 sumcheck is one product `Σ_{y,q} W(y,q) z(y,q)`. It has `nb = m − 14` block coordinates, bound first, and 10 position coordinates. The table index is `y + 2^nb q`.
  - Everything is stated with `ℕ`-indexed `range` sums and `eqAtR`. That is the verifier's own form (`shiftMaskS`, `linkWS`, `slotWS`), so no `Fin`-indexed table meets a concrete size.
  - I did not reuse FRShift's `join`/`mle` form. Re-deriving the identities in `ℕ` form was shorter than bridging `Fin (2^(s+n))` to `range`.
- **Weights.**
  - `wLeaf`: out at `eq(τ,y)·slot_256`, in at `(shift + κ eq(0,·))·slot_520`.
  - `wNode`: out at `[lk y] eq(τ,y)·slot_256`, in at `([lk(y−1)] eq(τ,y−1) + κ([y=0]+[y=N]))·slot_0`, plus `Σ_f κ^(f+2) famW f`.
  - `slotT` is the slot table. `famW` is the extended `linkInd`.
- **True sum.**
  - `sh_sum_leaf`: `Σ W z = eq(τ,last) h̃(θ) + κ s̃(θ) + resSum`. The target cancels in characteristic two.
  - `sh_sum_node`: `Σ W z = resSum`. The node's target is `0`.
  - `resLeaf` (J = 2) and `resNode` (J = 10) are ℕ-indexed residual tables.
- **The truths fail ⇒ a residual table is nonzero.**
  - `res_ne_leaf` uses `ShHoldsL`, the new leaf truth.
  - `res_ne_node` uses `ShHoldsN`. It goes through `resNode_src`, which is `linkInd_sum` at indicator weights plus `srcB_inj`: a family's sources lie in distinct blocks (`fam_src_lt`, `fam_src_inj`).
- **Final value, the bridge proper.**
  - `final_leaf` and `final_node`: the weight's extension at `(r_blk, r_pos)` is `w_out + w_in` exactly as `relSh` builds it, on the specifications:
    - a leaf: `eqPoint`/`shiftEqS` on the 18-coordinate padded points (`eqPoint_pad`, `shiftEqS_pad`), `slotWS 0/1`, `linkSum` of `0^8`;
    - a node: `shiftMaskS` (`sum_chainLk` reindexes `[lk y]` to `c·N + k`), `slotWS 2`, and `linkSum (linkWAllS (τ‖θ) (r_blk‖r_pos))`, with `linkSum_eq` and `linkW_mle`.
- **Schwartz–Zippel row for S1.**
  - `selC`, `DoomS`, `bS`, `doomS_step`.
  - Only the read coordinates are charged: `τ`'s first `nb` of the 18 drawn, and `θ`'s 10. `κ_s` is charged `J − 1`.
  - So the row is `nb + 10 + J − 1`: 35 on a node (§5.2's `26 + 9`), 29 for L32, 27 for P30.
  - Charging all 18 drawn `τ` coordinates would give 37 on a node, over §5.2's row, so `selC` skips the unread ones.
- **Lessons.**
  - `congr 1` on sums over `range (2^16)`/`range (2^10)` hit max recursion three times. I replaced it with explicit `have`s and `rw`.
  - `simp_all` inside a large context also recursed. Moving the case lemmas out (`resLeaf_zero`, `resLeaf_one`, `resNode_*`) fixed it.
  - `rw [show 10 = … from rfl]` also rewrote `Fin 10`. Rewriting `range 10` instead fixed it.
  - `ptA_toArray` without arguments rewrote an `Array` variable through `Array.mk` eta. Passing explicit arguments fixed it.
  - No kernel trouble: type checking stayed under 0.1 s in `FrSh`.

### On the log (`FRSoundnessFrS`, new)

- **Readers.**
  - S1: `coS`, `tauL`, `thL`, `ksL`.
  - S2: `rbL`, `rpL`.
  - The leaf boundary `bndL`: `hdr` bytes 16–47 at seed-query offset 87, and `stmt` bytes 1–32 at `msgAt 1` offset 1.
  - `sbL` and `hbL` are the boundary bits (`digBit`). `pad18` pads to 18 coordinates.
- **Initial claim.** `c0S` is `shiftTargetS` exactly as `relSh` applies it. `c0S_eq` puts it in the residual's terms via `shiftTargetS_pad` and `mle_digTbl`; a node's is `0` (`digBit_zero`).
- **Tables.** `TS = [W, z]` (`wS`, `zNode`). `trueSum_TS` is `c0S + resSum`.
- **S1.**
  - `truthSK`/`truthS`: `truthS1N` on a node, `ShHoldsL` on a leaf. `S2Bad` is S1's final doom.
  - `TR` and `TR_mle` turn the residual tables into arrays; `tr_ne` gives a nonzero one.
  - `s1_hfin` is the frame lemma at `(98, 15)`, built from `seq_round_le`, `esc_msD_frame` and `doomS_step`.
- **S2.**
  - `D2S` is `D2 114 16 readF chF c0SL nrS innerExpr TS`.
  - `habs_S2`, `single_S2` (2·2^128), `append_S2`, `RejS2`, `rejS2_ok`, `chk_of_not_rejS2`, `chkS_same`, `D2S_reads` (`Reads 170`).
- **End.**
  - `wSumL` is `relSh`'s `w_out + w_in` on the specifications. `claimSL` is the last claim. **`oSh κ es v := claimSL = wSumL·v`**.
  - `wSumL_eq` is the bridge on the log.
  - `trueL_two`: RS claim 3's true value is `ẑ` at S2's point, through the Sh point's four zero coordinates (`eqAtR_zeros4`) and the 7 low coordinates `xSL`.
  - `endS`: `D2S` past 170 means `¬ oSh … (trueL … 2)`. `pendS_pendBad` turns that into `PendBad (okRS oZ oSh)`, for any `oZ`.
  - `oSh_reads` is in `okRS_reads`' form.
- **Controls.** `shHoldsL_zero`, `not_shHoldsL_start`, `slotT_cube`, `slotT_off`, `c0S_node`, `oSh_unique`, `not_D2S_short`.

## Items 2–3 (fork): Z, L

See `logs/S-G7/ZL-notes.md` and the RESULT §1.

- Z (Z1–Zend) and the leaf's L (L1–L3β) are proved as parametric units, over the matrices parameter `ZLM`.
- The node's L3/L3β bindings are parked under R-V-M1/M2, now ruled in blueprint 3.16; INT-5 implements them.
- `pendZ_pendBad` and the leaf's `pendLc_pendBad` are not done.

## Coordinator messages during the pass

1. **The R-V review.**
   - M1 and M2: the node's Lc claim. I relayed them to the fork, which parked the node's L.
   - m2: `accept_fields` quantifies `zh`/`exk` existentially, so `oZ`/`oSh` must not be built on it. Strengthening it is mine; it is not done this pass (RESULT §5, item 3).
2. **Blueprint 3.16 is committed.**
   - R-V-M1 ruling (a): the kind factor in RS claim 2's weight.
   - R-V-M2: `free` has mask weight 0, and `finLc` (ii) gains `(1+α)·v_free·⟨rowW, eq⟩`.
   - INT-5 does the verifier side. The node's L is to be written against 3.16, or kept parametric until INT-5 lands.

## Item 7: headers

- `FRSoundnessFrPend`'s and `FRSoundnessFrRS0`'s module headers no longer say `finZ` binds nothing. They name `relZ` (INT-4) and the concrete bindings `FRSoundnessFrZ.oZ` and `FRSoundnessFrS.oSh`.
- Only the text changed.

## Checks

- `lake build FRSoundnessFrS FRSoundnessFrL FRSoundnessFrExt` is green (2,343 jobs, no `sorry`).
- Axioms (`logs/S-G7/axioms.log`): all 101 theorems of `FrSh`/`FrS` use only `propext`, `Classical.choice` and `Quot.sound`.
- The fork's axioms are in `axioms-ZL.log`.
- Source rule: 163 files, 0 findings.
- Name clashes: `sum_range_mul` clashed with `FRNodeTarget`'s, so I renamed mine to `sum_range_mul_split`. The fork renamed its `rbL` to `rbLc`.

**Stopped here (context).** The RESULT §5 is the handover.
