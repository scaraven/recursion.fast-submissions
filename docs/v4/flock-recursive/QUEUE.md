# Orchestrator queue (at most 6 concurrent agents)

Last updated 2026-10-30. Core pin `422f2f9` (PR #20 merged: M = 96, stream_s 1,920, build_s 1,200). Deliverable branch `v4/flock-recursive`; revision 4.4.1 on `v4/rev44`. Build trees use `logs/org20`.

## Ruling (user, 2026-10-30): acceptance over performance

The baseline only has to be accepted. Choose routes by the least sound implementation and proof effort that fits the hard caps:

| Cap | Limit | Today |
|---|---|---|
| build_s | 1,200 | |
| kernel_s | 600 | ≈ 380 s at main; the tight one |
| gate_s | 120 | |
| badge_s | 180 | |
| step_s | 60 | |
| ready_s | 10 | prover service start (≈ 0.66 s), **not V** |
| verify_s | 10 | per honest check; V ≈ 0.3 s VM |
| **DoS per-item** (`[dos]` item_factor · v_ref) | ≈ 2.07 s on the 7763 (10 × 206.6 ms); 100 items ≤ 180 s | **V's binding cap.** About 1.1 s VM is expected after the replay templates |
| badge start | 30 s, **and it counts against stream_s ≈ 29 times per stream** | 11.7 s on the runner at 200b531: **binding via stream_s** |
| setup_s | 240 | prover setup, 167 s on VM cores, unmeasured on the runner |
| prover build_s | 120 (`[caps]`) | gcc of the 23 MB `prover.s`, unmeasured |
| stream_s at M = 96 | 1,920 | |

- **Dropped:** V/P speed levers, ms kill lines and golf for score. Golf only when a cap is at risk.
- **Consequences for running tracks:**
  - R3 picks the least-effort sound `rsWeight` binding; sparse replay is acceptable.
  - R1 may choose plain or `tdot`.
  - ASK-P's folds may be sparse.
  - E1 targets acceptance and cap fit, not P̄.

## Running — as of 2026-10-30

**Milestone, rev44 `616b57c`:** the whole certificate (`FR`, `Solution`, `FRSubmission4Fin`) builds green with no sorry, and the axioms of `certified` are clean. Its only hypothesis is `Gaps4` = `Gap4R.imp`: per active slot, `SlotImp`.

Landed since the last update:
- **IMP `616b57c`:**
  - **Gap:** `aggChk` is discharged at the top.
  - **PK-m7 statement rows:** built, with `stmtOk4` proved at every active slot. The `input` import class is discharged.
  - **Composition:** `pfView_pf4`, and `AT.add` to combine import classes.
  - **Orchestrator fixes:** `FR.lean` imports, and `FRNodeRows4RepNCtrl`'s `ctlP` renamed to `ctlPN`.
- **R0 `4f6e694`:**
  - **Cells:** N′ = 108 with `tdot`. B′'s row is 176/178 ≤ 239, N8 has 140 blocks of margin, and |π| is 878,032.
  - **V cost:** ΔV of 14/17/22 ms for an N2/N4/N8 child, against a 25 ms kill line.
  - **Constraints for R1:**
    - N′ ≡ 0 mod 4;
    - the `tt` repack erases position 17;
    - the tdot tag is 21;
    - the pads are zero-asserted;
    - a `none` kind fails.
  - **`rsWeight`:** 5.8–12.5 ms as closed-form chains, which is marginal against its 10 ms line.

Running on rev44:
- **ASK-P landed `74a2528`.**
  - **Fold:** arena₁, the ask-template rows and the bit rows are folded into `nodeIRows4`, gated by `ArFit`.
  - **Positional machinery:** the reader, element alignment, `reassemble4` per field and the arena₁ bridge (API in ASK-P-RESULT §5).
  - **Templates:** `askTG` in the low module FRNodeRows4AskPosT. ASK-T replaces `TG.none`; IMPC adds `.add impcTG`, and the orchestrator merges it.
  - **Cost:** V(N4) +11/+15 ms, plan init 7.07 s.
  - **Open:** the arena₁ last-4 tie to `aggPad`; the N8 sparse plan check is too slow (> 1,800 s).
- **ASK-T landed `ae8b8d8`.**
  - **`ATAsk`:** holds for every ask, including the last item (via `AggPad4`).
  - **`askTG`:** `askTGT` + `inpTG` + `rsvTG` + `impcTG`.
  - **`gap4Imp_of_askT`:** `Gap4.imp` follows from `RepOk` + the replay fold + `SlotRunA` (withImpc). `Gaps4`'s text is unchanged.
  - **Fixed:** a V start-up stack overflow (`provLT`).
  - **Cost:** V(N4) 445/489 ms VM, which is not a cap issue. Plan init is 7.8–8.0 s wall VM, which is binding through stream_s. Levers: `pfLoc` caching (to INIT), and answer-slot aliasing in the compile.
- **IMPC landed `87519f4`.** The generators are `impcTG`/`colTG`.
  - **Covered by `impcTG`:** `piElem` 4,199/4,201, `piElemK` all, `piDigest` 872/8,300, `chF`/`chK` all; cap reads under (β′) are proof reads. About 34 ms V per node.
  - **`colTG`:** the `felems` aux facts, 871/871. About 110 ms V per node; deferred.
  - **Also proved:** the `execA_prov` byte invariant and the zero-pin flags (12/13, 77/78).
  - **Wiring:** `impcTG` goes into `askTG` via ASK-T.
  - **Open, for a later track IMPC2:**
    - `bitOf` (not an `ATImp` class; via `SlotRunA` on the concrete run);
    - siblings and `bits 20` (bit decomposition, about 15.9k bit cells vs the 8,320-cell bit area);
    - 2 mid-element flags per prototype (the stmt tag byte and the zero tail);
    - 4 unaligned statement reads.
- **IMPC2 design landed `3577618`.**
  - **Bit area:** grows to 16,384 cells in M.
  - **Rows:** `bitOf` takes rows plus a run proof; siblings become an `ATImp` class; `bits 20` and the mid-element flags and unaligned stmt reads go over the statement bit cells.
  - **Cost:** about 64.5k/81k template rows. V ≈ +0.25 s; init +1.5–4.4 s, which is too much under the stream constraint.
  - **Layout:** REPF was asked to move `repSegB` to 31·2^15 − 2^10.
- **IMPC2 landed `91e0d61`** (modules only, not folded).
  - **Generators:** `bitTGB` (decomposition, `bitOf`, `bits 20`) and `bitTGR` (siblings, unaligned reads), with `TG.addD`. Proved: `atImp_bitB` and `gap4Imp_of_bitsB`.
  - **Probe:** 0 failing rows and full coverage.
  - **Cost:** init about +1.0 s (target 0.5). The lever is the compile placing the `bitOf`/`tensorW` cells directly on the bit cells, about +0.3 s; it is with INIT.
  - **Fold:** waits on REPF's `repSegB`. The patch is `logs/IMPC2-orch-copy/patch.py`.
- **HEAD fix `b52ee6e`:** ASK-T's `ctlP` clashed with RepCtrl's, so `FR` did not build at `ae8b8d8`. Renamed to `ctlPT`. Lesson: build `FR` from a clean snapshot before every commit that adds modules to FR.
- **Note:** at HEAD, `FRNodeRows4AskBS` (outside FR) fails to build unpatched (line 171), because it assumes the folded `askTG`. The fold stage must make it build. The clean submission branch must contain no non-building modules.
- IMPC2b: `atImp_bitR`, the run proofs (`execA_idx`, `bitOf`/`bits`/`flag_stmt`, `SlotRunB`, `gap4Imp_of_bitsR`). The goal is `Gaps4` from the rows alone.
- **IMPC2b reported.**
  - **Proved:** the run proofs (`execA_ri`, bit order, `StmtBits`/`PosBits` from rows, `impA_bits`, `aux_bits`, `flag_stmt`) and `bitTGS`/`atImp_bitS`. `gaps4_of_runS` reduces `Gaps4` to `SlotRunB`.
  - **Remaining in `SlotRunB`:**
    - p0/p1: 7,426 sibling reads (the kind tie; route in IMPC2b-RESULT §5) and 871 `felems` (`colTG`);
    - **p1: 5 replay ops of the segment program** (`rsWeight`, `evalL`, `evalM`, `shiftTarget`, `targetS`), which `rtC1c 1` does not cover;
    - a closure generator, to make `SlotRunB` vacuous in the kernel.
  - **FOLD2 landed `97d578b`:** IMPC2 + IMPC2b folded (`bitTGB`, `bitTGS`, bit area 16,384, run proofs). `Gaps4` ← `SlotRunB` (`gaps4_of_runS`). Built from a clean snapshot + overlay (`logs/fr-build-SRA/orch.sh`): 2,684 jobs, no sorry.
- **SIB landed `648720f`.** Sibling reads (`sibTG`, `atImp_sib`, `sibOk_of`) and the closure (`TG.close`: a failing row at any unhandled import or foreign flag) are folded into `askTG`. `Gaps4` ← `SlotRunC` (`gaps4_of_runC`, `FRNodeRun4CT`): the `felems` cells (871 per prototype) plus uncovered replay imports (p0: none; p1: `targetS`, `shiftTarget`, `evalM`, `evalL`, `rsWeight`).
  - **Init +2.7 s user** (budget was +0.2 s). Accepted: the reads are needed for soundness; that budget was the orchestrator's, not a hard cap. Re-measure after CF2. Kernel: ≈ 7.5 s over SIB's modules (`atImp_sib` 4.35 s; G6 target).
- **SEG-R design landed `2aa619d`.**
  - **Dead ops:** `evalM`/`evalL` at prototype 1 are dead, so they are pinned to zero and `nodePlan` leaves the segment checks (init −1.3 s).
  - **rsWeight:** an F-point claim part, about 37k gates (the kind factor collapses).
  - **Small templates:** `targetSSegI` about 140 rows, `shiftTargetI` about 3.1k.
  - **Placement:** replay templates in each segment slot's own region via `rtKD`, needing about 40k rows and 40k cells per slot. It fits only if `arR2N` shrinks.
- **SEG-R0 landed.**
  - **Fit:** the F-point templates fit (≈ 39k locals per slot). There is a third free cell band (12.7k), and cutting `arR2N` to 154,368 gives band B 27k rows.
  - **Facts verified** on `protoProg 1`: 186 forcing rows are needed, not 75.
  - **Start-up:** the ~1.5 s init win needs `nodePlan`/`lPlan`/`implCN` made noncomputable.
- **SEG-R1 landed `9a3019d`.** `rtKD`/`KOkD`/`rtKD_okW`, `rtEvZ`, the `rsWeight` F-point template `rsSegT` (36,923 gates), `rtSeg1`, `rtC1d`, `repOkW_rtC1dB`, `cov`/`inOk`; `evalM`/`evalL` pinned in `implSeg`. On `protoProg 1`: 37,362 rows, none rejecting. `implB`/`nodePlan`/`lPlan`/`implCN` noncomputable; compiled op sets on `Impl.implC0` (`implS_eq`, `implNN_eq`); certificate statements unchanged. Init −2.05 s user, segment check −70 ms. `FR` imports `FRNodeRows4RepSeg`.
  - **SEG-R1b landed `bb0880c`:** `tsSegT`/`stSegT`, `kTSS`/`kSTS` arms of `rtSeg1`. On `protoProg 1`: 38,805 rows, 0 rejecting, no uncovered replay op; 38,486 locals per segment slot. Honest segment ACCEPT after the pin (L30/L31/L32; canaries reject). Node files predate the node circuit → E1 re-dump after SEG-R2. Kernel ≈ +3.4 s once folded.
  - **Review `b63754e` (SIB + SEG-R1): no blocker.** Closure total; compiled V = proved V (`implS_eq`/`implNN_eq` by `rfl`, no plan unfolded). Should-fix:
    1. honest ACCEPT logged after the `evalM`/`evalL` pin (L30/L32/P30/N30, N2/N4/N8) → SEG-R1b;
    2. empty `impQP` by **failing rows on `rt.cov`** (closure-style; op-aware `inOk` rejects `rsWeight` with `act` true), never by kernel evaluation of the compile (≈ 26k ops) → SEG-R2;
    3. R2 rewires `gap4Imp_of_close`/`gap4Imp_rtC1cC`/`gaps4_of_runC` (`FRNodeRun4CT`) at `rtC1d`; `gaps4_of_runS` is gone → SEG-R1b fixes the RESULT §7 text.
    - Notes: `atImp_sib` 4.35 s kernel (`cases op <;> simp` at `FRNodeRun4CS.lean:45`; G6). SIB's +2.7 s init waiver recorded above (net +0.65 s with SEG-R1).
- **CF2 landed `9db5ee0`.** Closed forms wired into `Plan4`; `evalL` by carry automata (replay 319.5k → 3.9k rows); plan fusion. Plan init 20.3 → 9.4–10.9 s user, RSS 2.0 → 0.9 GB; V(N4) 1.92 → 0.85 s VM. MxKat 33/33, `plan4t check` N2/N4/N8 equal. `FR` imports `FRNodeRows4RepCFCtrl`. **Speed work stops here** (acceptance over performance: 0.85 s ≪ 2.06 s DoS cap; init ≈ 10 s ≪ 30 s badge start; ≈ 300 s of stream_s).
- **SEG-R2 running** (on `9db5ee0`): fold `rtC1d`, constants and bands, failing rows for uncovered replay ops (no kernel evaluation of `impQP`), residual → `felems` only, honest ACCEPT. SEG-R1b's two arms land separately.
- **FEL design landed `bba76cf`; review `FEL-review` committed.** Route: compile aliasing — `dotKF`'s aux cells := arena₁ cells of the column's windows; a non-aliasable `dotKF` is refused and failed by SIB's closure; `felems_of_pf` from `PfCells`. 0 rows, 0 cells, no certificate statement change.
  - **FEL implementation: after SEG-R2.** Apply the review: (B1) the `tplExt_ok` → `compileTF4_soundAt` chain is stated at `L.ctx`, so it must carry the alias (6 call sites); (S3) prefer overriding only the `dotKF` arm at the `Xof` level over a new `TCtx` field; (S1) `pv` computed once or a per-prototype alias table (init kill line +0.3 s); (S2) generic `colAW pv win base` so controls use toy inputs, never `winE` on real tables in the kernel; P1 also compares plan-walk instance inputs; the prover's `mfill` must accept equal double writes.
  - SEG-R2 brief: SEG-R1-RESULT §7 (fold `rtC1c` → `rtC1d`, `arR2N` 154,368, `repSegB := arRb + arNb`, two-band `repRow0`/`repIRowsW`, `repMapC` bands 1 + 3, shared `rv₁`, `segRegion`). Prover cells: §8.
- **Running:**
  - **Review of SEG-R:** no blocker. The route is a fixed point (rows only; no op or import added), and the dead ops are pinned soundly.
    - **Should-fix:**
      - `kRSS.cov` must check `act` all false, the claim count and the widths;
      - band B needs the `arR2N` cut, measured after SIB;
      - the cell margin is ≈ 5 k after CF's padding; kill line: merge the cell bands;
      - `repSegB`/`repConsts` must move;
      - SEG-R2 waits on SIB.
    - **Init kill line:** if the `nodePlan` cut fails, it is +0.4 s × 29 per stream. Routed to SEG-R0.
- **Process lesson:** after committing from a build tree's copies, sync the worktree files (`git checkout HEAD -- …`). Stale FRNodeRun4*/FR.lean sat in the worktree after REPF's commit.
- **Collision guard:** ASK-T (the `askTG` line and imports) and REPF (the split and fold) both edit FRNodeRows4.lean. Each was told to touch only its own hunks; the orchestrator merges at freeze.
- **SRA landed `27459d9`.**
  - **`Gaps4`:** now over `StmtN4R`; the top hypothesis only shrank.
  - **Reserve link:** `gap4Imp_of_rsv` via the `AT.rsv` summand, in FRNodeRsvLink, which `FR` imports. The prefix form of `compileX_run` was not needed.
  - **Foreign flags:** p0 15, p1 79 (the kind byte and proof-byte zero pins, which wait on ASK-P).
  - **Finding:** in prototype 0, five `keep` ops over unequal-length `packK` arrays compile to `skip`. So the (β′) batched MAC cap check (reg 100345) is enforced by no row.
- **CK landed `44a4975`.** `getK` on kind-split registers now compiles to rows (FRVIRCompileK, `extGetK_okK`, no statement changed, V untouched).
  - **What it closes:** prototype 0's `finPf` final equation, including the (β′) MAC terms, is row-enforced.
  - **Foreign flags left:** only the kind byte and the proof-byte zero pins (p0 14, p1 79).
  - **Cost:** p0 +6,720 rows. V(N4) +21 ms, now 297/344 ms VM; plan init 7.0–9.3 s wall.
  - **Checks:** `plan4t check` passes on N2/N4/N8 (N8 in 848 s).
  - **Prover:** needs only a re-dump and a rebuilt blob.
- **R1 (stopped, `4838ac0`): the public-op route is unsound at recursion depth ≥ 2.** V(P)'s recompute ops become free imports when the grandparent replays V(P). R-OPS is marked superseded.
  - **New route:** replay templates at slot 0 for `evalL`, `targetS` and `linkWAll` (C1's `tplLW`), with no format change, at ≈ +90 ms V.
  - RSV2's stacked `evalM` is unaffected, because it is a fixed point.
- **C1b landed `77bfc19`.**
  - **Proved:** the replay templates for `targetS` (11.4k rows, ~64 ms V) and `evalL` (319.5k rows, ~345 ms V direct). `rtC1c` covers all five prototype-0 ops.
  - **Projected V(N4) after the fold:** ≈ 1.45 s VM ≈ 1.22 s runner. That is under the DoS cap of 2.07 s, a margin of about 1.7×.
  - **Levers if RUN1's runner numbers make it tight:**
    - `rsWeight` in closed form (R3 §4.2, −0.7 s);
    - `evalL` by carry-split (C1b §6, −0.32 s).
- **REPF landed `407260d`.**
  - **Fold:** the replay rows (`rtC1c`) are in `nodeIRows4`, and the replay part of `Gaps4` is discharged (`gaps4_of_runA`: `Gaps4` from `SlotRunA` at `rtC1c` alone). B3 is switched to RTOkW, with FRNodeRows4Defs split out.
  - **Over the caps:**
    - V(N4) 1.78 s VM (≈ 1.5 s runner vs the 2.06 s DoS cap);
    - plan init 20 s wall VM (+12.5 s ≈ +375 s of stream: **breaks stream_s**);
    - memory 1.95 GB.
- **CF landed `f041d03`** (WIP, at the context limit).
  - **Built:** the generic closed form for repeated template segments (`Rep.tm_rep`), and rsWeight rebuilt as repeated groups (`ok_rsGS`), proved and equal to sparse.
  - **Not yet wired:** V and init have not improved yet (init +2.7 s from the larger template build).
- CF2: CF-RESULT §6 steps 1–6.
  - Wire `arBlk0`/`kopV`, and add a structural `RepFit`.
  - Per-call contexts; let-bind `SM.rep`.
  - The evalL carry automaton.
  - Fusion.
  - The final A/B.
  - Targets: V ≤ 0.7 s VM, init ≤ 9 s.
  - The import-cycle split (a FRNodeRows4 defs module).
  - Replay rows into `nodeIRows4`, with the plan built in one pass from the final compile.
  - The fix for `tplLW`'s 216 s init.
  - `repRowsP = repRowsFin`.
  - The discharge `gap4Imp_of_repW` with `rtC1c`. The FRNodeRun4* switch to `RTOkW` is merged after ASK-T.
- **R3:** the closed-form chain template library. It first prices `rsWeight` against the 10 ms line, and if over, stops and reports the §5.3 fallback.
- **E1 landed `200b531`.**
  - **Acceptance:** the native prover at 4.4.1 is accepted end to end by rev44's Lean V. That covers a 10-node chain with kind changes and k = 1..4, the rf-oracle streams including the full-length first step, and canaries rejected. The decoder's output-stage KAT matches.
  - **Projected to the 7763:** worst first step 41.9 s (cap 60) and stream mean 1,150 / max 1,311 s (cap 1,920). `prover setup` is unmeasured on the runner (167 s on VM cores; budget 240 s).
  - **Still to do:** IMP's rows (re-dump, `AUX_L`) and R1's 108 cells (`RSV_REL`/`LREND_LEN` are hard-coded).
- **RUN1 landed `9249a56`** (11 runner runs, probe branches deleted).
  - **The real evaluate.yml REJECTs at stream step 1.** The prover's node blob predates IMP's stmt rows (`616b57c`), so it needs a re-dump. This is expected drift: the prover resyncs once the V rows settle.
  - **Measured on a 7763:**

    | Quantity | Measured | Cap | Margin |
    |---|---|---|---|
    | build | 752–812 s | 1,200 | 1.48× |
    | kernel, `certified` | 396.8 s | 600 | 1.51× |
    | **kernel, upper set** | **497.8 s** | 600 | **1.21×** |
    | gate | 13–14 s | 120 | |
    | badge | 60–64 s | 180 | |
    | `setup` | 60–70 s | 240 | |
    | prover build | ≈ 2 s | 120 | |
    | first step | 43.8 s | 60 | 1.37× |
    | later step | ≈ 25 s | 60 | |
    | ready | 0.8 s | 10 | |
    | V per check | 0.20–0.26 s | | |
    | v_ref | 206 ms | | |
    | DoS worst item | 29 ms | 2.06 s | |
    | **stream** | ≈ 1,530 s; **heavy draw 1,680** | 1,920 | **1.26×; 1.14×** |

  - **New binding constraint, V start-up:** about 11.7 s on the runner. V starts about 29 times per stream, so 1 s of V init ≈ 30 s of stream.
  - **Runner tiers vary:** 7763, 9V74, 9V45 and Xeon 8573C all appeared.
- **INIT landed `32e4e9c`.** V start-up is cut by 12–13 s outside the replay blocks, with outputs bit-identical.
  - **Biggest fixes:** `chTab4` (−7 s), the phase offsets plus the `finOps4` table (−3.7 s), and `eqTblG` (−1.6 s).
  - **Start-up now:** 17.3–18.3 s user at 407260d + INIT, and the rest is the replay blocks (CF). Before REPF it was 6.1–6.4 s.
  - **Proposals passed to CF:** `repB` noinline (−1.9 s), plan fusion (−1.0 s), `noncomputable` plan data.
  - **Budget per structure:** sparse ≈ 47 ms / 100k rows, keyed 85–95 ms, closed form 0.
  - **Levers not taken:** `impcTG` (≈ −0.15 s) and IMPC2's compile placement (≈ −0.7 s), each a stage of its own.
- **Kernel watch:** the upper set is at 1.21×, and Gaps4's discharge modules will add to it. G6 golf is needed before the cert probe.

**Then:**
- ASK-T (the `ATAsk` templates: FS links, Merkle mux, pins, seed, columns) ∥ IMPC (the `ATImp` classes: proof fields, siblings, `chF`/`chK`, `bitOf`, cap reads), both after ASK-P;
- the replay fold (C1/C1b/R3 rows into `nodeIRows4`, split FRNodeRows4's definitions, B3 → `RTOkW`, `repRowsP` replaced) after ASK-P and C1b;
- R4 (`rsWeight`) after R3;
- R5 (segment slots), with `targetSSegI`'s 560-row rewrite owned by R5;
- `Gaps4` = ∅;
- G6 (golf, including G5's deferred `FRNodeLayout4`/`FRNodeRows4Ext` changes);
- a cert probe on the runner;
- a clean submission branch;
- the evaluation.

### Earlier entries (this session)


Main (`v4/flock-recursive`, core `422f2f9`; the certificate assumes only `Open4F := Gaps4`):
- **G5 landed `edf11b4`.** On a 7763 `certified` takes 379.7 s, down from 461.7 (margin 1.58×). KReplay went 224.3 → 154.8 s and the comparator's peak memory 8.7 → 4.5 GiB. No statement changed.
  - **Root cause:** the kernel unfolds `HAdd.hAdd` before user definitions, so a defeq step between differently shaped closed ℕ sums evaluates them in full. G5-golf.md has the fix patterns; the tools are in logs/G5/tool/.
  - **Why 150 s is out of reach:** what remains is about 52.8 s of 17.5k declarations under 50 ms each, 44 s in FRSoundness4*/FRNodeRows4*, and 30 s outside FR (14.5 s of it core-owned `basePoly_irreducible`).
  - **Merge into rev44:** after PORT lands, since G5 touched FRX*. PORT carries G5's FRXNd4/FRXChain*/`cso_outIR4` changes by hand.

`v4/rev44` (HEAD `953838d` = RSV-V2 + main merged + B5 + RSV-S WIP + A1′ + RSV-S2b + RSV-S2a + PORT + main merge + B4 + C1 (partial) + RSV-S3; red at RSV-V's 7 declarations and possibly decoder literals):
- **RSV-S2a landed `50a7f52`** (WIP).
  - **Proved:** the reserve branches of `flag_gFinE`/`flag_gFinB'` (in blocks; `R4Fin` builds in 11 s), `R4FrE`'s `e_end4`/`e_in4`/`e_fin4` (`mStack_sP`, `implN4F_hMS`), `rsvZero4`, `FrRS`/`Start` at the stacked form, and `Qry` with spacers.
  - **Orchestrator edit:** XRun now uses `implN4F_hMS` plus its import.
  - **Red:** `R4PfFlag.gFinPf_reloc`; `gFinPfR` lacks the second chain.
- **RSV-S3 landed `953838d`.**
  - **Proofs:** finPf's second chain, `w0V4`'s reserve cells (`hcl`, `hrc`), and the `StmtN4R` forms (`Resid4R`, `certificate_rev4R`, `ks_rev4HR`, `certificate_rev4HR`); the old `ks_rev4H`/`certificate_rev4H` keep their statements.
  - **Build:** `FR` and `Solution` are green in its tree, and the axioms are clean on `certificate_sub4`'s path. Kernel time is at H-cert3's level (48.1 vs 46.2 s over FRSoundness4*).
  - **Orchestrator edit:** the 2-line FRNodeLinks4 fix (`cellsX`).
  - **Worktree red:** only `FRXSig4H.xRows_of_stmt` (max recursion since B4), now with IMP.
  - **Open:** `gap4Imp_of_rsv` needs a prefix form of `compileX_run` (RSV-S3-RESULT §5.4), in FRNodeRun4*. It is scheduled after IMP. Then `Gaps4` goes to `StmtN4R` (§5.5).
- **RSV-S2b landed `7bbbf49`.**
  - **B′ at 69 cells via the DRS `Pub` route:** `single_B4` is `Fin 71`, 70·2^128, and εR is unchanged.
  - **The four reserve controls:** in `FRSoundness4RsvCtrl`.
  - **`FRNodeStmtR4`:** `StmtN4R`, `nodeRunR_X`, `evalM_childV` and `ks_rev4R`. The `FRNodeCircuit4` laws are generalised over `St → StmtN4`.
  - **Still open:**
    - `gap4Imp_of_rsv`. This is S2b item 4, wiring `evalM_childV` into `SlotRunA`'s slot-0 imports, and it waits on PORT's `gap4Imp_of_run`.
    - The switch of `hRes` to `StmtN4R` downstream. It is mechanical.
  - Three requests routed to S2a: `rsvZero4`, `R4W0R`'s `hcl`, and the new form for `start4_of_fields`. XRun stays red until S2a delivers them.
- **The review of RSV-S found no soundness issue.** Every challenge comes after every value it batches, `ChildBad4` is charged at 24/2^128 through E1's exit, and εR stays 15/2^124. It settled the two open questions:
  - **Q2, B′'s 60 extra cells:** `PubOKR4` goes only into `DRS0X`/`DRS1X`'s `Pub` argument (phase 23 is a post-doom). `bg16X`/`bg20X` are unchanged.
  - **Q1, the node statement:** `StmtN4` keeps its signature. `nodeLaws4C'` and its two siblings are generalised over `St → StmtN4`, and a downstream `StmtN4R := StmtN4 ∧ PubCellsR4 ∧ truthChildV` is used on the gap4Imp path. That edit to `FRNodeCircuit4` waits until A1′ has landed.
  - The four controls for `ChildBad4` are required.
- **PORT landed `c4eca2b`.**
  - **Builds:** 84 modules plus `Solution` and `FRSubmission4Fin`, with `Open4F := Gaps4` unchanged.
  - **Realign:** deleted and replaced by a copy loop. The 2^27 buffer and `ldIx` stay, for `finBlk` when k < maxK.
  - **Spacers in `aggTr`:** `nW` is 193,888, and `reassemble4` covers all 20 fields (`pf4` had been 77,872 B short). There are 486 FS positions.
  - **Kernel:** about 178 → 39 s over the comparable modules.
  - **Untested:** the decoder KAT against a prover stream waits on E1.
  - **Merge:** main was merged into rev44 (`253516c`, docs only). G5's `FRNodeLayout4`/`FRNodeRows4Ext` golf, about 5.7 s of kernel, is deferred until after B4 and C1, then redone by hand.
- **B4 landed `7537acd`.**
  - **The gap:** `aggChk` is discharged in rows (`aggChk_of_rows`), with the new hypothesis `PfView`. `gap4_of_rowsI` takes `imp` explicitly. `Gap4R` = `imp` only.
  - **Rows:** check rows N2 1,144, N4 2,074, N8 4,148. The link region holds ≤ 20,979 of 32,768. `extRows4_length_le` is now 12,056.
  - **V:** V(N4) rises 2.9 ms for own kind and 6.9 ms for all kinds. MxKat and `plan4t check` pass.
  - `FR.lean` imports `FRNodeRows4AggChkCtrl`.
- IMP: closes `Gap4R.imp`, covering B4-RESULT §6:
  - the arena ask templates meeting B3's `ATOk`;
  - PK-m7's statement rows;
  - `pfView_reassemble4`;
  - the wiring of `gap4_of_rowsI` into FRSubmission4*.
  It owns Arena*/Agg*/FRNodeRun4*/FRNodeLinks4*/FRSubmission4*.
- Review of PORT (cheap Opus): no blockers. A doc erratum was appended to PORT-RESULT: `pf4` was short by 77,024 B, not 77,872. Two hard-coded lengths (486, 8783) are guarded by the decided length lemmas.
- **C1 landed `6a93cc8`** (partial; additions only).
  - **Proved by replay rows:** `shiftTarget` (constant 0 at prototype 0: one row, `STBase`) and `linkWAll` (`tplLW`, 13.8–14.4k rows), evaluated at a second assignment in slot 0's spare region (`RTOkW`, `compileFromX_soundRW`).
  - **Problem:** V costs 52–60 ms per call for these two alone, against PACK §6.2's 7–14 ms budget for all of R. `evalL` would be about 82k products per kind, and `repRowsP` takes 131 s if computed at plan init.
  - **Not done:** the fold into `nodeIRows4`, which is an import cycle with FRNodeRows4.
  - `FR.lean` imports `FRNodeRows4RepNCtrl`.
- **R-OPS (Fable) landed, rev44 `6d1a933`.**
  - **`evalL`, `targetS`, `linkWAll`:** public-op route. The child's operands and outputs become public cells (the reserve's B′ mechanism), and V(P) recomputes and asserts. There is no new challenge or FS position, and the cost is about +15 ms VM.
  - **`tdot`:** folds `targetS` into `lagrangeS`, giving N′ = 108 new cells. εR holds while N′ ≤ 169, and N8 keeps 140 blocks.
  - **`shiftTarget`:** C1's one row.
  - **`rsWeight`:** closed-form chain templates (1–3 ms VM), falling back to a second claim family.
  - **Rejected:** the reserve (sumcheck) route for all five ops.
  - **Plan:** R0 audit → R1 V side ∥ R3 chain library → R2 soundness (incl. `gap4Imp_of_rsv`) → R4 `rsWeight` → R5 segment slots → R6 `evalL` lever.
- R0: the cell audit and a re-measure of per-op V on rev44, with no source edits. It now also covers the review's items 1–6 (operand binding per kind, the kind-element tie, pads and tags, `tdot`'s readers, the corrected kill exits, `rsWeight`'s per-term rate).
- **Review of R-OPS** (`reviews/R-OPS-review.md`): no blockers.
  - **Sound:** FS order is fine, `tdot` is an exact identity, and the budget arithmetic holds (N′ 108, row 178 ≤ 239; N8 within `lBase`).
  - **Preconditions for R1:**
    - operands proved to be computed by rows;
    - the kind element tied to the mux selector, with junk rejected;
    - zero asserts on the pads;
    - a size-tag lemma.
  - **`rsWeight`:** likely 6–7.5 ms, not 1–3.
  - **Plan fixes:**
    - an explicit prover stage, with or before R1;
    - R2's dependencies listed;
    - R2 shrinks `rtR`'s import set inside IMP's `SlotImpR` hypothesis;
    - a named owner for `targetSSegI`'s rewrite.
- E1: prover port to 4.4.1's format: D/A fields, L1/L2, the reserve's 1,008/112-B fields and E2/E4 terms, spacers, arenas, the packed plan form and phantom pins. It runs end to end against rev44's Lean V, covering kind-changing chains, k = 1/2/4 and the worst-case first step against step_s 60. It prints B5's `eok`. It leaves a hook for B4's `aggChk` rows and owns `prover/`.
- Review of A1′ (cheap Opus): no blockers.
  - **Soundness:** the free spacer bytes enter only the ignored spacer answer, `wf` is proved for every segment and spacer, and `ctrlA_no_spacer` is a real control. S2b is asked to confirm that no ROM-consistency argument ranges over spacer entries.
  - **For E1:** prove or test that the main chain after `aggL k − 1` is message-free, so phantom pins never conflict. Exercise it with k = 1 and k = 2.
  - **Minor cleanup (later golf):** `lastR_no_spacer` and `aggChainLen_eq`'s 5th conjunct are bare arithmetic. Restate them through the definitions or rename them. `pbC` (FRNodeRows4Wots:109) may be dead.
  - **For B4:** `main_not_final2` now distinguishes k = 2 by the final flag only; B4 has been told. B4's fit is in the link region (≈ 19.5k of 32,768), not H.

Landed on rev44: **A1′ `e464756`**.
- `Gap4R` is now `imp`, `aggChk`.
- The stride is 64·24,238 (whole blocks); N8 still fits with 256 blocks spare.
- V(N4) rises by 8.3 ms for own kind and 25.3 ms for all kinds, because each sub-slot now has its own pinned block. The lever is to share runs across sub-slots, which differ only by an offset.
- Pins are ungated, so the prover writes phantom constants at inactive sub-slots.
- `VA_sound_log`'s proof line changed (intersperse).
- `ks_queriesC4` needs `traces_spacers_le_qV`; that is routed to S2a.
- Review of B5 (cheap Opus) found no blockers; the fast path is fully covered by `linkV4_eq`/`slots_val`. The should-fix items:
  - **(a) Clash with A1′.** `pinKeys`/`hpkr`/`extIRows`/`wfLen` assume one pinned block per slot, equal to `wfSeg`. A1′'s per-sub-slot blocks need a segment-carrying key and a re-proof of `linkV4_eq`. A1′ has been told; `innAt`'s `find?` should become an indexed `Array`.
  - **(b) Silent slowdown.** If `cokB` fails at runtime, V silently falls back to `growsVal3`. The bench and E1 should print `(lkArr κ).all (·.eok)`.
  - **(c) Sharing may shrink.** Per-sub-slot blocks may reduce sharing across kinds, so re-measure V(N4) after A1′.

Landed on rev44: **B5 `9a41aac`**. V(N4) with own kind only 276.6 → 263.8 ms; with all three kinds 347.6 → 288.4 ms. Each extra kind now costs +16–18 ms, against +37–38 ms before. `protoV4` (≈ 125 ms) is now the bulk of the own-kind call. Its open lever is sharing prototype 1's low tables with prototype 0, worth about 5 ms.

**Then:** `Gaps4` discharged (S2b item 4 `gap4Imp_of_rsv` after PORT; the `hRes` switch to `StmtN4R`) → E1 (prover: D/A fields, L1/L2, reserve's E2/E4 terms and 1,008/112-B fields, spacers, arenas, packed plan form) → cert probe → evaluation.

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

S-A `8ff873c`; S-C `ebac8c2`; S-D `8e6dad7`; S-E1 `2d5a811`; S-H1 `40b2f81`; S-0 `47158b1`; S-E2/S-E3 `8447c50`; S-F `c8e1869`; S-F2 `8f22b86`; S-G through `ac43569`; S-H2 through `11fb3a5`; INT-1 `5fc7d3b`; S-E5 `9dbab71`; … S-N2 `75eff21`; INT-10 `1c5a738`; RET-2 `1a342e7`; RET-3 `0aaa99b`; RET-4 `ea3e130`; S-H4 p6–8 `5f39f5a`/`b562c50`/`cb849a3`; S-L4 `00e308f` (hL discharged); **S-H4 pass 11 `1782ab4`: `nd` complete — the certificate assumes only `Open4F := Gaps4`**; B3 `1f400d9` (compileFromX_run); rev44: A2″ `1987618`, A3′ run 2 `e14db30`; B2′ `21ade15` (cap check templated, V(N4) 275 ms); RSV-V `213c407`; B2″ `7602c97` (arenas placed); RSV-V2 `06375d6` (chain green on (β′) at εR; guard RejG := RejC ∧ cdOK; GoodX now over RejG — accepted); S-H4 p5 `a84753a`; G3 `302b523` (12 modules −30 % CPU; the finals' flag modules need a block-wise read lemma, ≈ 66 CPU-s); S-H4 p4 `6d79280`; S-H4 p2–3 `170c2ee` (lagIR, level decode at CKind); P2⁸ `2d9dd8c` (7763: step + overhead 11.41 s, M ≤ 83, truncated 30.4 %, P̄ 8.43 s; prover.s f0841393…); G2 `4ac68fc` (15 FRX modules −42 % CPU); PACK-4.4.1 + review; S-E13b `ce2a4ad`; D-PK memo `PACK-4.4.md` (committed, under review); P2⁷ `5e99fba` (7763: step + overhead 12.78 s, M ≤ 74, truncated ≈ 52 %; S-E13a/b's matrices and cells, 0 failing rows on honest witnesses; prover.s 5e1bab39…); S-E14 `f5ad181` (replay mechanism; segment `linkWAll` only); S-E13a `8cc8ccd` (kindN, kindS@0, wf@0, wots, aggPad closed through `gap4_of_rows : StmtN4 → PfHdr pf → Gap4R → Gap4`; `Gap4R` = imp, kindS/wf at i ≥ 1, aggChk; V(N4) +≈30 ms; new node dump for P2); S-I `2f437ed` (residuals 8–9 closed; `Solution` PROVISIONAL under `Open4`; **cert build 882 s on the 7763 > `build_s` 600 → REJECT**: 307 modules, 2,975 CPU-s, need ≤ 2,020 (≤ 1,550 for 1.3×); bench probe season S = 6.421, truncated at M = 63) (`SegOut4` gone: `ks_rev4H`/`certificate_rev4H`; open: drop `hO`/`out` from S-N2's `ks_rev4GH`, then delete the G forms, `SegOut4`, `runFacts4_C`). FR builds as a whole.

## Rulings

- **H-cert3, 2026-10-30 (at `1782ab4`):** build 804 s direct on the 7763 (1.49×), badge 61 s (2.9×), gate 13.5 s — but the **kernel is tight**: `certified` 413.8 / 461.7 s on two 7763s (**1.30×**), upper set 566.5 s (1.06×); comparator peak 8.7 GiB. Dominant: `FR.X.realign_sem` 44.8 s kernel (S-H4 pass 10), `FRXNd4` 12.1 s, `FRSkip` 9.1 s, ≈ 20 new `FRX*` modules at 2–5 s. rev44's `Gaps4` proofs will add more → G5 (kernel golf) now.

- **H-cert2, 2026-10-29 (at `ea3e130`):** every certificate cap fits — build ≈ 736 s scaled to the 7763 (679.7 s direct) vs 1,200 (1.63×); kernel (comparator on `certified` + `submission`) 265.2 s vs 600 (2.26×), upper bound over the whole FR closure 441.4 s (1.36×) — watch the kernel as rev44's `Gaps4` proofs join the closure; `probe/cert2` measures it.

- **D1 vs reserve, 2026-10-29 (D1-probe):** the `replay_mle` fixed point closes (Lean scratch `attic/FRD1pScratch.lean.txt`: `placed_eq`, `ublock_chat`, `fixed_point`), but D1 costs 26–79 ms VM (≥ the 25 ms kill line) for its gather blocks. **The reserve is adopted, as corrected by D1-probe**: the child's `evalM` claim batched into E2 (η = E1's spare coordinate) and E4 (`κ_E⁴·W*`), both points carried in π and bound by point claims, gated off for N8's missing previous node and for leaves; **no new item or phase**: `fLrEnd` 48 → 880 B, `fEEnd` 48 → 112 B; |π| 876,176, stream 64·24,234, N8 `hUsed` 195,192 (lBase 195,328 ≤ 195,584); εR unchanged; `Gap4.imp`'s three `evalM` registers are discharged by the point claims and `truthChild`, not by R. Folded into rev44 by RSV-V (V side) then RSV-S (S-C/S-G: E2 zerocheck + linear claim, `truthChild`).

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
