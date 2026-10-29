# Orchestrator queue (FR-D8: at most 3 concurrent agents)

Last updated 2026-10-28. **Rebased onto core PR #20 (pin `6d05d00`, commit `987e679`); blueprint revision 4.0** (§0.1 B-11…B-17, §10 changes 25). Build trees use `logs/org20`.

## Running — as of 2026-10-29 (6 agents, FR-D8)

Main (`v4/flock-recursive`):
- S-H4 pass 6: `FRXDec4Levels`, the 4.1 chain table (parametric in the item sequence), `FRXOut4`, `FRXNd4` (`nd`), the plug into `FRX4Prog`/`FRX4Ext`/`FRSubmission4*` on main.
- RET-3: retirement step 4 (3.x verifier shapes out of `Solution`'s closure).
- B0 (done, held uncommitted in the worktree, frozen at `logs/B0-orch-copy`): prototypes 630,016 / 618,496 rows (−100 k / −107 k), `evalMT4` parity; commits together with P2⁹'s re-embedded plan form so main's prover and V stay consistent.
- P2⁹: stream-proof nondeterminism, then prover levers.

Design:
- A2″ (rev44): the (β′) V change per PACK §11.4 + review `PACK-4.4-b2-review.md` (PB-M2 L2 scope via `Seq.cap4`, minors), L1 + L2, interim skeleton-op cap check; then A3′ (PB-M1's doom chain) ∥ B2′ (templates), A1′ (spacers), P2.

`v4/rev44` (worktree `../recursion.fast-submissions-rev44`): at `e4b7d5f` (main merged); its V (A2′) is **unsound** until A2″ lands (β′).

## Waiting

- **Node-circuit gaps (S-N2's `Gap4`, 2026-10-29): rows still to build — the soundness gap of the node.** (1) `imp`: the pack map (proof fields ≈ 9.8k, oracle answers ≈ 8.9k, `bitOf` ≈ 7.5k per prototype → H's stream cells), the `input` alias, the auxiliary imports, the foreign flags, `stmtOk4`; (2) `kindN`/`kindS` (follow from the pack map); (3) `wf` (stream tag and length words pinned); (4) `aggChk` (`V_A`'s checks against `c_A` in-circuit); (5) `aggPad` (k-gated candidate final block links, R-4-m2); (6) `wots` (2 × 2,788 WOTS mux rows); (7) the replay `R` of the child's six ops (`evalM`, `evalL`, `targetS`, `shiftTarget`, `linkWAll`, `rsWeight`). Owners: S-E13a (1–3), S-E13b (4–6), then R.

- **The residuals of `ks_rev4` / `certificate_rev4` (X4, 2026-10-29)** — the whole remaining soundness work:
  1. `FrontHi` (front phases 13–25 over the composed dooms): P4f.
  2. `RunFacts4` (AcceptTail per run + statement/`vk` views, incl. a 4.1 `vkOf_of_run`): R4h, then R4.
  3–4. `SlotIface4` instance (`lrows = lRows4`, `irows = nodeIRows4`) and `hRes : StmtN4 → NodeResid4` (incl. the signature part): S-E, after S-E12f.
  5–7. `NodeDec4 nd`, the node links `hL`, `DecOk4 nd`: S-H4.
  8–9. Completeness and δ: S-I — via the witness-sending path (`complete4`, δ = 0), to confirm against the contract's `Certificate`.

- **INT-9 (after S-E12e, INT-8): the node's `evalM`/`evalL` wiring.** `implN4`/`implN4T` take `evalM`/`evalL` from the 3.x base (`implC`), i.e. 3.x's plan, not the 4.1 node rows. They must be S-E12b's `evalMT4 κ` (= MLE of `nodeIRows4 κ`, `evalMT4_eq`) and the 4.1 L rows (`lRows4`), with `_meets`; this discharges R4's `RejFinE4` parameters `hM`/`hL` (R4d D11). Owner: L-circ + the node-ops module.

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

S-A `8ff873c`; S-C `ebac8c2`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 `47158b1`; S-E2/S-E3 `8447c50`; S-F `c8e1869`; S-F2 `8f22b86`; S-G through `ac43569`; S-H2 through `11fb3a5`; INT-1 `5fc7d3b`; S-E5 `9dbab71`; … S-N2 `75eff21`; INT-10 `1c5a738`; RET-2 `1a342e7`; S-H4 p5 `a84753a`; G3 `302b523` (12 modules −30 % CPU; the finals' flag modules need a block-wise read lemma, ≈ 66 CPU-s); S-H4 p4 `6d79280`; S-H4 p2–3 `170c2ee` (lagIR, level decode at CKind); P2⁸ `2d9dd8c` (7763: step + overhead 11.41 s, M ≤ 83, truncated 30.4 %, P̄ 8.43 s; prover.s f0841393…); G2 `4ac68fc` (15 FRX modules −42 % CPU); PACK-4.4.1 + review; S-E13b `ce2a4ad`; D-PK memo `PACK-4.4.md` (committed, under review); P2⁷ `5e99fba` (7763: step + overhead 12.78 s, M ≤ 74, truncated ≈ 52 %; S-E13a/b's matrices and cells, 0 failing rows on honest witnesses; prover.s 5e1bab39…); S-E14 `f5ad181` (replay mechanism; segment `linkWAll` only); S-E13a `8cc8ccd` (kindN, kindS@0, wf@0, wots, aggPad closed through `gap4_of_rows : StmtN4 → PfHdr pf → Gap4R → Gap4`; `Gap4R` = imp, kindS/wf at i ≥ 1, aggChk; V(N4) +≈30 ms; new node dump for P2); S-I `2f437ed` (residuals 8–9 closed; `Solution` PROVISIONAL under `Open4`; **cert build 882 s on the 7763 > `build_s` 600 → REJECT**: 307 modules, 2,975 CPU-s, need ≤ 2,020 (≤ 1,550 for 1.3×); bench probe season S = 6.421, truncated at M = 63) (`SegOut4` gone: `ks_rev4H`/`certificate_rev4H`; open: drop `hO`/`out` from S-N2's `ks_rev4GH`, then delete the G forms, `SegOut4`, `runFacts4_C`). FR builds as a whole.

## Rulings

- **Re-pin to core `64378d2` (PR #20 head, 2026-10-29 09:32):** M = 96 constant, `stream_s` 1,920 s, **`build_s` 1,200 s** (certificate job 40 min, benchmark 50 min); harness/docs only, no Lean change (`logs/org20`'s harness files refreshed in place). The certificate build (696 s on the 7763) fits with 1.7×; the stream (96 × ≈ 11.1 s ≈ 1,066 s) fits with 1.8×. Build-budget tracks (RET-3, G4) wind down; the critical path is `nd` (S-H4) and rev44 (A2″ → A3′ ∥ B2′ → A1′ → … → E1).

- **User, 2026-10-29 (announced, not yet in the core):** the stream length becomes **M = 96, constant**, and `stream_s` grows **1.5× or 2×** (1,440 or 1,920 s). Plan against it now: with P2⁹'s 11.10 s per step + overhead on the 7763, 96 steps ≈ 1,066 s — fits 1,440 s with ≈ 1.35× margin. The orchestrator watches the core's PR #20 head (`6d05d00`) and the open-PR list for the change, then re-pins (`logs/org20` successor) and re-measures.

- **User, 2026-10-29 (revised):** reviews of each task by a **cheaper Opus subagent** (effort lower) to spot issues/friction early and speed the submission; no Fable/full adversarial reviews; the bar is `HARNESS: ACCEPT`; golf stays.

- **(β′), 2026-10-29:** adopted (PACK §11 + review PB: soundness confirmed value by value, ε unchanged; L1 + L2 both needed; L4 rejected — a lost stream ends the evaluation). The doom chain is PB-M1's carried form (`DT 52 := DPf ∨ ¬truthCap`, 53 gates on Σ ≠ 0, 54/55 split on `A = Â(ζ)`), not §11's literal `DT 53/55`.

- **B0, 2026-10-29:** `splitMin = 32` kept (V parity; 16 would save 24.6 k rows at +3 % `evalMT4`); the cap check must be templates (B0 measured A2′'s skeleton form at ≈ 55–65 k sparse rows, ≈ 30 ms per prototype); B0 lands on main with P2⁹'s re-embed, then merges into rev44.

- **A3′, 2026-10-29:** PACK-4.4.1's (β) is **forgeable**: the path digests `cur_r` have no Fiat–Shamir item before ζ, z (Q.i shares P3.i's start in `fsStarts4`), so a prover with two openings per read solves identity (I) as 512 GF(2)-linear equations in 871 choice bits (≈ 20k compressions). The memo and its review both read the stream order as the FS order. rev44's V is unsound; D-PK writes (β′) (absorb the 871 digests before ζ) with the N8 overflow (≈ 1,280 blocks) priced, then a fresh review.
- **Cert probe, 2026-10-29 (run 40839253556, EPYC 7763, after RET-2, G2, G3):** `build_s` **696.2 s** (was 882.2), 250 modules, ≈ 2,332 CPU-s; comparator 46.9 s, gate 12.2 s, badge 59.1 s. ≈ −320 CPU-s still needed (RET-3, step 2, the finals' flag modules).

- **Branching, 2026-10-29 (orchestrator):** revision 4.4.1 is built on **`v4/rev44`** (worktree `../recursion.fast-submissions-rev44`, `logs/org20`/`logs/pkgs` symlinked to this worktree's). `v4/flock-recursive` stays the consistent, deliverable entry (its prover matches its V); main's tracks (S-H4, B0, P2, golf) are merged into rev44 periodically; rev44 merges back once E1 (the prover port) and the harness dry run pass. A2′ is rev44's `f853d37` (WIP: red at A3′'s two modules).
- **A2′, 2026-10-29:** the cap has **1,408** entries (2^9 + 3·2^8 + 2^7), not 1,920 (memo error): `A` = 45,088 B, `piSizeOf seq4` = 843,280, stream 64·23,875, `D_z` row 1,407/2^256. Accepted as built (no padding to 61,472). Accumulators in the finals (ζ, z are squeezed after the positions); no `powIdx` op. **V(N4) 233 → 513 ms and the plan 4.2–5.3 s** until B2′ templates the cap check (≈ 58.8 k untemplated rows per prototype + ≈ 35 k rows fallen out of instance pieces): accepted as rev44's intermediate state; B2′'s cap-check templating is pulled forward after B0.

- **PACK-4.4.1, 2026-10-29 (orchestrator):** adopted (review `reviews/PACK-4.4-review.md`: adopt with fixes, all applied). ζ reuses P3.4's κ_c (sound per the review); the §8 reserve's E phase is **not** appended now (D1 first, kill line 25 ms VM); S-E13a's H-cell pins retire with B2′; the 12/79 foreign flags are listed before B3 is sized; S-H4 writes `reassemble` field by field. ΔS of the full binding: +0.36 s best, +0.86 s worst (S-I's basis). The certificate build after the plan ≈ 2,400–2,500 CPU-s against 2,020: the `build_s` question stays with the user.
- **RET-2, 2026-10-29:** committed `1a342e7`; ≈ −400 CPU-s. The dropped 3.x modules stay in `lean/` until `Solution`'s closure is final; `FRNodeSoundA`'s re-point (53 modules out of `FRNodeSound4Ctrl`'s closure, not `Solution`'s) is not needed for the certificate.
- **S-H4, 2026-10-29:** pass 1 (`0fd05ce`, 2026-10-28 21:37) was not resumed for ≈ 8 h (orchestrator's slip: the queue listed it as running); pass 2 started 06:00.

- **S-E13b, 2026-10-29 (orchestrator):** committed `ce2a4ad`. Its proposal to give the `r31` link family source 549 + t with `mbo = 248` (saving 4,160 rows per node, ≈ 0.2 % of `N_M`) is **deferred**: it changes `linkWAll`'s spec, V and the prover for a small gain. Revisit after `R` and the build budget.

- **INT-8 (`3b13ba5`), 2026-10-29:** each kind's exact final-tail check is kept (dropping it would let V accept higher-degree finals for N2/L30/L31: a protocol change); deviations 2–5 accepted (exact per-kind Lr/E point lists, all families computed then selected, the group-to-kind equality as a theorem, the statement fact checked in `VsegC`/`VnodeC`). The native `acc` checks `stmtDigest(tix, π[48..176)) = c` after the run.
- **Node M rows on the runner (P2⁗), 2026-10-29:** embedded in `prover.s` in plan form (templates once, instance placements, sparse skeleton rows), rebuilt at prover start, KAT against the full dump; no Rust port of `compileTF`. INT-9 exports the plan form.

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
