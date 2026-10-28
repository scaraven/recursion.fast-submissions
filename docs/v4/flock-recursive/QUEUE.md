# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-28. **Rebased onto core PR #20 (pin `6d05d00`, commit `987e679`); blueprint revision 4.0** (§0.1 B-11…B-17, §10 changes 25). Build trees use `logs/org20`.

## Running (revision 4.1; 6 agents, FR-D8)

- S-E13: the plan build ≤ 2 s per process (B-16), generic piece lemma replacing `Plan.ok`'s run-time comparison.
- H-cert: the certificate's build/kernel time on a 4-vCPU runner against 600 s / 600 s.
- T4: the Ligerito tail at `seq4` (+14 positions).
- P4a: front Z, L, S, Sh at `seq4` with the segment deltas (`SegHolds`, range factor, masked successor, `lastOps`).
- P4b: front Lr, E, RS, B′, W0 at shifted positions, per-kind node dims, O1 over `nodeIRows`.
- S-H3: the Rev4 computable extractor (`V4with` dispatch, A and N2/N4/N8, `computes4`, the node law for `FRSoundness4Frame`).

## Waiting

- **Certificate build budget (H-cert, `0864c53`): over the cap.** `lake build FR` takes 611–712 s on the 7763 against `build_s` 600 s (kernel replay fits: 372 s, 1.6×). Levers, in order: G1 golf of the S-0/S-F finals (running); golf of the FRX* top modules after S-H3; **retire the 3.x-only modules from `lean/`** once the Rev4 theorem composes (X4: the 3.x S-G chain, the 3.x extractor paths, P30/tree remnants; move T4's 195 position-free imports to a shared module first); keep controls cheap. Question to the user (organiser): a larger `build_s` (the 30-minute job has room). Re-measure with `probe/cert-time` after each integration; S-I must run the real `evaluate.py cert` (gate 120 s, badge 180 s unmeasured).

- **R4 (after P4a/P4b fix their `Rej*` names):** the program layer on `gen4` (`accept_chain`, views, `finLog`) and the front checks once (S-G13 §6).
- **S-E12′ (after S-E13):** the Rev4 node circuit in Lean: N2/N4/N8 block-kind maps, targets, kind indicators, `StmtN`/`NodeResid` with 1 + k slots, `childOk4`, the aggregate's padding/counter claim (R-4-m2); all import rows, `R`, templates; dumps for P2's node prover.
- **X4 (after T4, P4a/b, R4, S-E12′, S-H3):** per-kind `SegSoundLog`, nodes, the final Rev4 theorem via `ks4_of`; retire the 3.x S-G chain from the entry (build budget, S-G13 F4).

- **4.0 critical path:** S-0′ → S-E12′ (all import rows, `R`, templates on N4/N8, plan ≤ 2 s per process) ∥ S-G12′ (`truthE` over `nodeIRows`, 1+k slot truths, `hRes`, the walk bridge, `hFrontV`, `kstate_front` via `ks_of_front`) → P2′ node prover on the full dumps → stream dry run (S ≈ 3.7–4.1 s projected) → S-I certificate (600 s build/kernel) → H evaluation on GitHub. The items below written for revision 3.x are superseded where §10 changes 25 (c) lists them obsolete (the tree, `P30`, `proofCap` margins, the `T_V` gate).

- **Critical path to a certified node:** S-E12 (all remaining circuit rows: kind-factor and `free`-term templates, τ-op templates, `tplTargetSNode`, `tplLinkWAll`, `rsWeight`, 745 `tensorW`, the WOTS mux rows, the pack map and `input w` alias, `R` with the sparse-skeleton templating and instance-AP layout) → `hRes` (S-N2) → S-G12 (`truthE` over `compileT`) → `kstate` unconditional → P2 node prover on the full dump and the stream-link measurement → S-I certificate (600 s build/kernel) → H runs.

- **R-V (after INT-4): adversarial review of the verifier's finals.** Does every claimed or exported value (`zhat` 0…nRS, every sub-protocol's final claim, every absorbed message the finals read, every `ex` export) reach an `assertEq`? Is every `relX` the blueprint's A.9 row? Method: a dataflow table from the dumped program (`logs/INT-4/dump`) plus the `flag_fin*` statements, not prose. The `finZ` miss passed every per-field proof because a relation only covers what it names.
- **S-G7 (after INT-4):** the front's S, L, Z, assembly (`DF`/`RejF`, `FrontObl`, `FrontChainStab`), `hW0`, `hStart`, `hFront`, `kstate_front` (S-G6-RESULT §5).
- **S-E11 (after S-E10, INT-4):** the τ-ops as templates, `tplTargetSNode`, `tplLinkWAll`, `rsWeight` (`sq127`/`eqK`), the 745 `tensorW`, then `R` with the reserve levers; the full node dump.
- **P2 (after S-E11):** the node prover from the full dump (XOR cells, `phiRS` split, 18-coordinate τ, `finZ`'s assert, `linkWAll`/`shiftMask`); **re-measure the stream link (the thinnest margin, ≈ 3.0 s of 3.1 s)**.

- **INT-3 (after S-E7 item 1): the 3.14 items outside S-E.** S-0 `finSh` with the `linkWAll` op and packed points (`κ_s^{f+2}`; `relSh`/`flag_finSh`); S-C `shift_sound_masked`, `linkWAllS` on the pinned map; S-F `implC` kind-selected `linkWAll`/`slotW_in`, `linkWAll_meets` in `implC_meets`, `finB′` without `κ′ v_E` (`J_f = 9`); S-G chain-masked node `truthS1`, `sh_reads_chain_only`, `truthB′` at `J_f = 9`, the E4-end binder in `truthE4`; `FR.lean` imports FRNodeTarget, FRVerifierImplNode, FRVIRTplRep, FRVIRCompileSound, FRVIRTplPlan.
- ~~S-E9 after INT-3~~ (running; INT-3 closed `ebcc8f1`, V 168.7 ms VM best). Was: the replay `R` in 3.14 (D)'s uniform layout (`replay_mle`, `plan_wf`, `replay_sound`, `inc_mle`, `eqTree_mle`, `evalMT` sharing each `Ĉ`), the fused child walk (prototype 15.2–17.8 ms), `FRNodeLayout` `wmSlot = 146`/`hEnd = 47,594`/`regions_fit`, the mux mirror addresses, `mRowModel`, the templates (`tplTargetSNode`, `tplLinkWAll`, `walkAB`, `rsWeight`, `shiftTarget`, 745 `tensorW`), the re-dump for P2.
- **H-probe (after INT-3):** V (N30) on a GitHub runner: `probe/fr-vtime` has no `run.sh` yet (it must build the entry on the runner); replaces the ≈ 264 ms VM-equivalent estimate. VM: 169.4 ms best at S-E8 (`937e14d`), projected ≈ 195 ms.
- **Then:** `FrontObl`, `FrontChainStab`, `hFront`, `hExt` (S-G); the S-E H-side assembly of `node_sound` (pack map, `input w` alias, SigOk, W-kind children, `node_complete`).
- **P2 node prover** after S-E7's re-dump: mirror writes per A.6 (146 blocks/slot), `end41` split, `linkWAll` weights, the chain mask in Sh, `slotW_in = h_in`.

- **After INT-2:** re-verify `lake build FR`, commit; wire S-E5's `evalLT` into `implC` (+≈ 4.5 ms); re-measure V; S-H2h with the moved positions (FRX constants: nRep, chTab/fsMsgs, capW0/capOffL, piSize tape facts).
- **After S-CN:** S-E templates `tplTargetSNode` (≈ 10k rows) and `tplLinkW` (≈ 2,500 rows per family); S-G the node S truth (`ShHolds` + 7 terms), Z1/Z2 tables over the node `targetS`; re-dump for P2.
- ~~S-E5: T_V, the skeleton~~ (closed `9dbab71`: V 204.9 ms VM best). Measured: V without evalM 150 ms VM; evalM 545 ms (flat evaluator), of which ≈ 440 ms is the untemplated skeleton (≈ 120k rows per slot: Merkle steps, finP4's Horner). To do: block templates by placing compile's rows into aligned regions (cell renaming preserves soundness; plan-time key check; roundtrip lemma; S-E4-RESULT §6); aligned cell allocation; F-9 (materialise `cur` in Merkle steps, ≈ +15k rows per slot); the import classes; finE's evalM with κ_E (Ã + κB̃ + κ²C̃). Target: V + evalM ≤ 230 ms VM.

- **P2 node prover**: needs S-E3's node dump (logs/S-E3/nodedump/, which now has template groups and the WOTS order) and the F-7 outcome (it may change the node circuit). Leaf proofs are dump-exact (P2 §11).
- **S-E (the H-side assembly of node_sound)**: the pack map from H trace/stream cells to the M imports. This covers the r17/r18 bindings (S-E3 §9), `input w` as an alias of the public seed cells (S-E3's proposal: no rows, `PubCells` binds vk/cᵢ), SigOk and the format facts, W-kind children, node_complete; the remaining templates (tensorW, rsWeight, walkA/B, kindInd, rowW, shiftTarget, the child's evalM/evalMK/evalL replay); F-8 (track kindInd/packFK); per-generator row counts for RowsFit (S-G's truthE_iff hypothesis; false for an arbitrary fin).
- S-G2: ligerito_final, final (with fsQ_gen, ChainStab), FinalLaw; then kstate.
- S-I: certificate assembly (Solution.lean, claim.json at B-10 with fuel_per_word 8,192, the εR arithmetic, axioms, the 600 s build/kernel check). H: GitHub harness runs.
- Golf: FRVIRFinalsSG (1,526 lines, budget 400) and the large L-ext modules.

## Closed

S-A `8ff873c`; S-C `ebac8c2`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 `47158b1`; S-E2/S-E3 `8447c50`; S-F `c8e1869`; S-F2 `8f22b86`; S-G through `ac43569`; S-H2 through `11fb3a5`; INT-1 `5fc7d3b`; S-E5 `9dbab71`. FR builds as a whole.

## Rulings

- **2026-10-28 (P4e, S-H4, RET-1):** D10 keep the node Sh start term (J = 10). D11: the 4.1 node ops (`targetS`, `shiftMask`, `slotW`, `linkWAll` at `nodeLayout4`) are S-CN4's. S-H4's level-0 interpolation (GF(2^64) differences, prefix/suffix products, 261 steps/pair) replaces the batched-inversion wording of 4.2 (A); the node decoder's memory is **2^28** words (the full level-0 codeword), not 2^27; `fuel_base` stays. RET-1's Core extraction is in; `tail_shift`'s move out of T4's closure is approved for the next retirement pass; the Rev4 closure still holds 62 3.x soundness modules through direct 3.x imports in P4a/P4b/R4/`FRSoundness4Pos`/`FRXLevel` (re-point at T4's copies or Core before retiring).

- **S-E12a, 2026-10-28:** an aggregate child's public statement cells are its `hashA` block's output `c_A` (`N4c.cells4`), not the trace's seed payload (segment 1's statement): S-E12b's provisional `pfCells4` must follow. D1 (candidate final blocks per k′ for the aggregate's padding obligation), D2 (one `hashA` per aggregate), D3–D6 accepted; blueprint A.6/A.7 and B-13's mux set {N2, N4, N8} to be updated.

- **S-G12′, 2026-10-28:** F2 `AccFrontK` (with the proof's kind byte) is the right form; `AccFront` to be retired at the next integration. F3: generalising S-G's E chain over an entries source (so `truthE`/`nE`/`RejE4`/`hfit` read `nodeIRows`' indexed rows) is O1's ruled restatement.

- **Lever 5 declined, 2026-10-28 (S-D3):** 32 rows at level 0 is sound (kernel-checked `pcsLevelsR_ok`), but priced with the proved sizes it gains S −0.02 s (the final message doubles: V +13 ms) and needs the domain bound 21 bits across four modules and qV 39,112 > 36,000. Alternative B (one more fold at level 1, −0.09 s) deferred. `FRLadder5` archived in `docs/v4/flock-recursive/attic/`, outside the entry.
- **S-F4, 2026-10-28:** the segment's shift successor is masked at its last block `L` (required for soundness: `shift_unmasked_link`); `SegSound` replaced by `SegSoundOn`/`segSoundOn_of_KS` (extraction on good traces). Blueprint B-12 to state both.
- **Agent budget:** FR-D8 raised to 6 concurrent agents (the user, 2026-10-28).

- **B-15 as built (S-H2n, `9398792`), accepted 2026-10-28:** outside the domain `E` dispatches on the proof's kind (decode on W, `search` under `vkOf π` on a node SNARK, the denotation on a leaf, `none` on bad), since `vkOf π` is the KS key only on an accepted node run; `E` takes the acceptance `A` as a parameter (`hE_of_accV` for `A := accV implC finC`); the search bounds traces by the certificate's 2^16. Blueprint text to follow at the next revision. Old routes with `hWB`/`hOut` to be retired once integration uses `kstate_front_ofE'`.

- **S-N1, 2026-10-28 (orchestrator):** O0: `ExtIface` was false as stated (the chain is not tied to π); the linked route `RunLink`/`ExtIfaceR`/`kstate_front_ofR` is adopted. O1: the E truth must be stated over the templated rows V evaluates (`nodeIRows (planOf fin)`/`compileT`), not `Layout.nodeRows`: a stage after S-G11 (S-G12: `truthE`, `nE`, `RejE4`, `hfit`). O2/O2b (the circuit rows for every import: pack map, `R`, the templates, the WOTS selector/digit/mirror mux) are S-E's and make up `hRes : StmtN → NodeResid`. O3 to the blueprint.

- **S-G7, 2026-10-28:** S1's doom is charged only on the τ coordinates the residual reads (node 35 = 26 + 9, L32 29, P30 27 ≤ §5.2). The leaf statement `SL` := `ShHoldsL` (block y+1's `d` at 520 = block y's `h_out` at 256, with the hdr/stmt digests as start and end) ∧ `ZHolds` with a leaf's matrices; `Stmt` keeps `Reads 3`. Ratified.

- **Plan time, revising 3.15 (e), 2026-10-28 (orchestrator):** the badge's `NS` is the monotonic time of parsing π and evaluating `acc` only (`.contract/harness/badge/Verify.lean.in` lines 9–26, `timedCheck`), so a closed top-level plan constant, initialized at process start, is outside every check's `NS`. Process start counts only against the batch timeout `verify_s · n + 60 s ≥ 70 s` (`rfh/checks.py` `verify`). Ruling: the plan is built at process start, **≤ 5 s on the VM**; a control measures that a cold process's first check is not slower than its warm checks (the plan is not lazily computed inside `acc`). The 0.2 s bound is withdrawn (S-E10 showed literals need a kernel proof about `compileT`); the blueprint is to record this at the next revision.

- **Blueprint 3.15 batch (to issue when S-E9 lands):** lBase 47,616 in A.7/§4.3; the S-G2 level-4 tail (§5.2 P3.4 row 0, A.10); `T_V` measured (169 ms VM) and the (D) frontier note; INT-3's `shiftMask` op (A.8), `slotW_in` selected in `finSh` by `keep`; **INT-3 decision 3 (checked, no hole)**: the node's Sh start term `κ_s(eq(0,·)+eq(N,·))` has target 0 in characteristic 2, so Sh binds only `In(0) = In(N)`; `h0` at **both** chain starts comes from the public target (`streamStart.h0Pin = true`, `nodeKind 0 = nodeKind chainN = streamStart.target`, `Kind.hIn_eq_h0`); state it in §4.2.
- **P2 after S-E9:** `ir.rs` must interpret `linkWAll` and `shiftMask` (it still reads `linkW`), the A.6 mirror map, the chain mask, the `h_in` In slot, and the node's S2 initial claim 0.

- **S-H2k, 2026-10-28:** the extractor emits the trace's length words as constants (`enc64 qlen`), not copies of the stream, so `FinalLaw` gains no hypothesis. Blueprint fix pending: A.7 and the §4.3 table still give L's base block as 46,336 (`lBase` is 47,616 since 3.12).
- **S-E8, 2026-10-28:** the `T_V` kill test passes (V 169.4 ms VM best, projected ≈ 195 ms, 1.35×); the §10 changes 21 (D) frontier note and the `T_V` row are to be updated at the next revision. Hot compiled code uses shifts and literals, not `2 ^ k` (≈ 60 ns per power).

- **S-G2 level-4 ruling, 2026-10-28** (blueprint §5/§10 at the next revision): the tail follows the verifier. Level 4 is checked directly (`y_q = Enc₄(final)[p_q]`), Pf starts from `c1 4`, `finPf`'s weight covers levels 0–3 (`wPf` = zero-padded `wFold 4`), P3.4's doom `msD (DP2 4) (finP2 4) …` (its `κ_c⁽⁴⁾` squeezes stay in the transcript, unused), Pf's doom `¬ truthP3 4 ∨ D2`. No verifier change; the error rows can only go down.

- **INT-2 decisions, ratified 2026-10-28** (to enter the blueprint as change 21, batched with S-CN's findings):
  (1) E4end absorbs 32 B (`f̂(r′)` ‖ 16 zero bytes), keeping the stream at 64 · 23,146 so that `stream_padded`
  holds with no padding cell; piSize **797,904** (1.31×), stream counter 1,481,344.
  (2) `finE` (v) binds the E4end message (value = `α₄`, the extra half zero) for every kind.
  (3) `r_Lr` is Lr2's final point (the lincheck's row point is the zerocheck's final point, as for `r_E2`).
  Still to fix in the blueprint: A.9's `finB′` row (`κ′ v_E`); `mRowModel`'s claim-5 row (11,400 rows, an over-count).

- FRVIRSpec budget: judged per shape, not ×15 phases. Re-check when the queries shape is proved.
- The phase-final checks (`fin : Finals`) go to a new module `FRVIRFinals`, owned by S-F (the
  verifier), which consumes S-C's lemma forms.

## Next (in order, as slots free)

1. S-G (soundness), S-H2
   (the extractor program; see the notes below), S-I (certificate), H (harness runs).

## Carried into the S-0 fix pass

- Take `nMax`/`logNMax` from `FRRS`.
- Add the real `MerkleEnc` instance (`frEnc i` from `nodeQ`/`colQ`/`parseNode`/`parseCol`/`carried`;
  a scratch version already elaborates, S-D-RESULT fix pass).

## Notes for S-H2 (from the S-H1 review, plus S-D2)

- No tape-length loop nested inside another. Each `loopT` count is loaded by `input`
  immediately before its loop.
- Query lengths as `|q| >> 3` plus `(|q| & 7 ≠ 0)`; never `(|q| + 7)/8`.
- The decoder: a butterfly inverse NTT (O(ℓ·2^ℓ)), proved equal to S-D2's `coeffsAt` spec, using
  `decode_row_D` (agreement on 2^ℓ positions decodes to the message).

## Kernel-time total (sequential, VM)

S-A 15 s, S-C ≈ 22 s, S-D ≈ 4 s, S-E1 7 s, S-H1 27 s, S-0 ≈ 12 s: about 87 s.

## Deferred

- X128, the 128-bit profile memo (the user's optional side question).
