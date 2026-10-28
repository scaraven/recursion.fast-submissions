# R4 JOURNAL: the program layer on `gen4`, the front checks once

Base: HEAD `4841734` (P4a pass 1). Build tree `logs/fr-build-R4` (a copy of `fr-build-SG13`;
`b.sh` = `snap.sh` + capped build, log `logs/R4/build-last.log`). HEAD's `lake build FR` green in
it (2,436 jobs).

## §0 Plan (written before the proofs)

**What exists for `gen4`:** the generator (`FRVIR4`), the items (`FRSoundness4Qry.items_gen4`,
`noAsk_finalsOf`), the positions (`FRSoundness4Pos`). **What does not:** any reference semantics.
3.x's `refPhase`/`exec_skeleton` (`FRVIRSpec`) and `fsQ_gen` (`FRVIRChain`) are stated over 3.x's
`Phase` table and `genPhase`; nothing relates `exec` of `gen4` to anything. So item 1 starts one
level lower than the brief's "rebuild `Acc*`": the reference semantics of `genPhase4` itself.

**Reuse.** `gen4` addresses π absolutely (`piField 0 o`), and `absOff 0 o = o`; so 3.x's exec
lemmas with `f := 0` and an absolute `o` apply verbatim: `exec_sqzC`, `exec_sqzOps`, `exec_uni`,
`exec_roundsT'`, `exec_absorb`, the `sqzT`/`roundsT`/`uniVals`/`coordVals` references and their
chain lemmas (`sqzT_chain`, `roundsT_chain`, `ChainOK`, `qOf` — `qOf` already takes absolute
`(o, len)`). The finals' field lemmas (`fields_chain`, `fields_ok`, `field_flag`) are generic in
the fields, so they apply to `finOps4 P` once it is written as a `Finals` with relocated fields.

**New (module `FRSoundness4R4Ref`):**
- generic `exec` facts: the flag factors (`exec_ok_and`); a run appends exactly `opsOut` registers
  and consumes exactly one trace entry per ask (`exec_ext`);
- `refPhase4`: 3.x's references for squeezes/uni/rounds; the seed and absorbs as `ans1` then a
  `pureRun` of the pure tail (`stmtOps4`, `lastOps`, `finalOps4`, the end-zero check), so
  `P4a.run_lastOps` gives the `L` bits directly; the **queries phase as its own `exec`** (no copy
  of 3.x's Merkle reference: the front checks never read a query phase's values, and the chain
  needs only that it consumes non-FS entries and keeps `st`);
- `exec_genPhase4`, `genPhase4_ctx`, `refPhases4`, `exec_skeleton4`.

**Then (`FRSoundness4R4Chain`):** `phaseMsgs4`/`fsMsgs4` (absolute offsets), `refPhase4_chain`,
`skeleton4_chain`, `fsQ_gen4`, `matches_fsQ4` (a `decide` certificate: `fsMsgs4`'s item kinds are
`fsItems4`, and every message fits in `piSizeOf seq4`), `runLog_chain4`; `accept_chain4` (finals as
relocated fields).

**F1 (statement offset)**, a small separate check: `oOf seq4 1 fStmt = 48`, so `lastOps` reads
`digestAt π 81`, and `idxOfF 24 (digestAt π 81) 0 = rdLE64 π 81 % 2^24`.

## Log

### Pass 1

- **F1 (item 3) closed, no gap** (`FRSoundness4R4Stmt`): `stmtOff4 : fieldOffOf seq4 fStmt +
  phaseOffOf seq4 1 fStmt = 48` (certificate), `lastN_eq : idxOfF 24 (digestAt π (48+33)) 0 =
  rdLE64 π 81 % 2^24`, `lastN_of_le`, `segView_lastN` (on `V_A`'s range `n ≤ cap ≤ 2^18` the
  program's index is `segView`'s `n`). Controls `lastN_wrap` (−: `2^24` reads `0`), `lastN_five` (+).
- **`FRSoundness4R4Ref` green**: `exec_ok_and`, `exec_ext` (generic); `refPhase4` (queries phase =
  its own `exec`); `exec_genPhase4`, `genPhase4_next`, `genPhase4_ctx`, `refPhases4`,
  `exec_genPhases4`, `genPhases4_next`, `exec_skeleton4`, `skeleton4_next`.
  Traps met: `FR.Snd.msgAt`/`coordsOf`/`lastAns` shadow `FR`'s (qualify); `Reg` needs
  `dsimp only [Reg]` before `omega`; `genPhase4_ctx`'s `omega` hit max recursion until the big
  `exec` hypotheses were cleared.
- **`FRSoundness4R4Chain` green**: `phaseMsgs4`, `msgsFrom4`, `fsMsgs4`, `refPhase4_chain`,
  `refPhases4_chain`, `skeleton4_chain`, `fsQ_gen4`, `shOK_seq4` (certificate).
- Coordinator: T4 and S-E13 committed (HEAD `087f416`); re-snapshotted (snap.sh takes HEAD).
- **`FRSoundness4R4Run` green**: `fsMsgs4_len`/`_items`/`_fit` (certificates, `decide +kernel`
  over `seq4`'s 482-entry table), `fsCheck_qOf`, `matches_fsQ4`, **`runLog_chain4`**; `relocFin`,
  `relocFin_ops`, `finOps4_eq : finOps4 P = (relocFin P.S (finalsOf P)).ops`, `noAsk_relocFin`;
  **`accept_chain4`** (item 1).
- **`FRSoundness4R4At` green** (`refPhases4_at`, `phase_at4`, `skeleton4_outs`, `SkRun4`,
  `skRun4_of_accept`); **`FRSoundness4R4View` green** (`sqz_entries4`, `coords_view4`, `one_view4`);
  `FRSoundness4R4Ctrl` (controls). Short-name clash `fsOf_length` removed (3.x's used).
- Final: `lake build FR FRSoundness4R4Ctrl` 2,457 jobs green; axioms 76 theorems clean; source rule
  237 files 0 findings. Profiles: `FRSoundness4R4Chain` has one 33.9 s kernel check (not the
  `shOK_seq4` certificate, 18 ms alone): flagged as F2, first item of the handover.
- Stopped here (context long). Handover: R4-RESULT §6.

### Pass 2 (R4b)

- Build tree `logs/fr-build-R4b` (copy of R4's; logs `logs/R4b/`). Re-snapshotted after P4c's commit
  (`ed98f9e`).
- **Item 0.** Bisected `FRSoundness4R4Chain` with prefix files: `refPhase4_chain` is 0.1 s; the 34 s
  are `fsQ_gen4`, and inside it `∃ ms, fsMsgs4 S = some (0, 48) :: ms := ⟨_, rfl⟩` (sorry variants:
  33.6 s with it, 0.5 s without). Fixed through `phasesOf S = ("seed", .seed) :: ps`. `-Dtrace.profiler`
  names the kernel declaration: `fsMsgs4_items` 11.3 s (quadratic `getD` under `range 482`) →
  linear restatement 2.05 s. Chain 34.3 → 0.49 s, Run 12.6 → 2.93 s.
- **Coordinator (P4c F2).** `FRSoundness4R4Link`: segment `linkWAll = 0^8` (`rfl` at `.L32`),
  `linkSum_zero`, `run_linkOps_zero` (family-by-family `pureRun`). Trap: `rd_app_left` rewrites the
  first `rd (_ ++ _)` it meets; give the array explicitly.
- **Item 1.** `FRSoundness4R4Rnd`: the log's message is read off the query (`msgAt_of_q`), so no
  table certificate; `rounds3_log`/`rounds2_log` by induction with the log offset `P + 2j`; dummies
  by `roundsT_dummy`. Traps: `Reg`-typed `<`/`∃ b` defeat `omega` (state `∃ b : ℕ`, `lt_reg`,
  `replace h : u < _ := h` after generalizing to `u : ℕ`); `congr 1` on `Val.f` timed out (use
  `congrArg Val.f`); `.uni`/`.rounds` dot constructors inside `some (…)` cost 11 s of header
  elaboration (write `Sh.uni`).
- Open questions answered: `piSize_node4`, `piSize_aggSegs`; S-H3 has no `fsQ4` (its node links are
  the parameter `NodeDec4.Links`).
- Final: 2,468 jobs green; 117 theorems' axioms clean; source rule 257 files, 0 findings.
  Stopped with items 2–4 in the RESULT's Pass 2 handover (context long).

### Pass 3 (R4c)

- Build tree `logs/fr-build-R4c` (copy of R4b's; `b.sh` logs to `logs/R4c/`). Baseline (HEAD `4919027`)
  green. Re-snapshotted to HEAD `94ee843` (P4e, S-H4 committed) for the final build.
- **Item 2 (flags at `FinP`)**: `FRSoundness4R4Fin` (`pe4`, `evalOp_reloc`, `reloc_pi*`,
  `flag_gFinZ`, `flag_gFinLr`, `flag_gFinE`, `flag_gFinB'`), `FRSoundness4R4FinSh` (`flag_gFinSh`,
  four cases `P.vn × P.kv.node`), `FRSoundness4R4FinLc` (`flag_gFinLc`, generated from 3.x's text;
  `dotOps_reloc`, `lcTail_reloc`), `FRSoundness4R4FinRS` (`run_elemOps4` … `exec_gFinRS`, the kit on
  relocated ops). Relations are 3.x's with sizes/kind tables/reads from `P` (`relZ4` …); controls
  `relZ4_fin3P`, `relLr4_fin3P`, `relB4_fin3P`, `relLc4_fin3P` (+: equal to 3.x's at `fin3P`),
  `relZ4_rejects`, `relLr4_rejects` (−).
  Traps: `simp only [reloc]` unfolds `reloc S (wop i)` into a match on an opaque `wop i`: rewrite
  with `hwr` first, then unfold `reloc`. `reloc` on a field read needs `hf : f < 19` in the simp
  set (else an unreduced `if`), and `absOff_zero` (else `rfl` whnf's `fieldOffA`).
  `gFinSh`'s link part: kept general (`linkSum (impl.linkWAll …)`) in `relSh4`, so the front check
  closes it with `linkWAll_seg*` + `linkSum_zero` rather than `run_linkOps_zero`.
- **Missing fact (b), outs before `next`** (`FRSoundness4R4Outs`): `opsOut_*` for every generator,
  `genPhase4_out_lt`, `genPhases4_split`, `cAt4_succ`, `cAt4_next_mono`, `cAt4_outs`, `OutsLt`,
  `cAt4_outsLt` (from the run's `CtxOk`, as 3.x), **`segPt_lt`** (`uni_view4`'s `hpt`, any `n > 3`),
  **`skeleton4_out_lt`**. Trap: `rfl` for `opsOut (lastOps o b) = 94` hits max recursion
  (`opsOut_flatMap` instead).
- **Missing fact (a), the kind** (`FRSoundness4R4Kind`): `seed_byte4` (the seed's `assertEq` and
  `ofBytes_inj` give `byteAt π 0 = p.byte`), `kindOfC_byte4` (byte 71 of the seed query),
  **`kindOfC_seg4`**, **`kindOfC_node4`**, `dims_seg4`, `dims_node4` (`z3 = m − 6`, `s2 = nb + 10`,
  node `lr/e2/e4 = lrR/e2R/ncR`). Trap: any `simp` that meets `bytesOf ([…] ++ replicate 46 0)`
  hits max recursion: `generalize` it first.
- **Item 3 started**: `FRSoundness4R4Acc`: `fields_of_accept4` (every field's relocated run from a
  file extending the skeleton's, flag `true`), `skel_pos4`, `outsOf_lt4`, `hin_Lr`,
  **`relLr4_of_accept`** (the template). Trap (cost me four bisections): **never let the unifier
  see `(skeleton4 seq4 p).2.outs` under a reducible head** (`List.drop`, `headD`): `rfl` against it,
  `rcases … rfl`, or `List.mem_of_mem_drop` on `coordsR ⟨skeleton…⟩` whnf's `skeleton4` (heartbeat
  timeout). State register bounds for an abstract `fi` (`hin_Lr`) and instantiate.
- Stopped with items 3 (rest) and 4 in the RESULT's Pass 3 handover (context long).

### Pass 4 (R4d)

- Build tree `logs/fr-build-R4d` (copy of R4c's; `b.sh` logs to `logs/R4d/`; `MINE.txt` adds
  `FRSoundness4R4Ex`, `FRSoundness4R4FrE`). Baseline at HEAD `5eb34a6`: green (2,494 jobs).
- Coordinator (mid-pass): blueprint 4.3 route (A), INT-8 will make `gen4` uniform per group; proofs
  unfolding `finOps4 P` will need repair after INT-8 lands. Front checks here go through `FinP`
  fields and the `flag_gFin*` lemmas; the few op-list facts used (`gFinLr`'s two exports and 14
  outputs, `gFinRS`'s exports and 4,117 outputs) are isolated lemmas (`opsOut_gFinLr`,
  `opsOut_gFinRS`, `gFinRS_ex_lt`).
- **`exAt` bookkeeping** (`FRSoundness4R4Ex`): `baseAt`, `exAt_succ`, `fields_ex4` (field `k`'s file
  `Rs k` has size `baseAt … k`, so `Ex (k+1) = (Ex k).push (field k's exports at (Rs k).size)`;
  `zhat` registers lie in `Rs 0`), `lrEx_eq4`.
- **Front checks** (`FRSoundness4R4FrE`): generic views by name (`coordsR_view4`, `chals_view4`,
  `claimN3z_view4`, `one_name_view4`, `msg_abs4` + one table certificate `fsMsgs4_ends` for 213,
  273, 325, 326). `RejEndLr4` (`lr_end4`), `relE4_of_accept` (with `lrEx`'s values), `RejEndE4`
  (`e_end4`), `RejInE4` (`e_in4`, `chk2F_c0`), `RejFinE4` (`e_fin4`; `evalM`/`evalL` at the node
  rows' `matMLE` are parameters `hM`, `hL`), each with a segment version through the gate.
  Traps: `Nat.exists_eq_succ_of_ne_zero` gives `n.succ` (rewrites against `n + 1` fail);
  `rw [ptA_toArray, ptA_toArray, …]` fails once the instances are exhausted (use `simp only`).
- Also: `relLc4_of_accept` + `l2_chk4` (`RejL2`, both kinds; one more certificate `fsMsgs4_front`
  for 67, 97); controls module `FRSoundness4R4FrCtrl` (`rel{E,Sh,RS}4_fin3P`, `*_rejects`,
  `baseAt_ctl`); `linkSum_seg4`.
- Coordinator notes: the source rule flags the word `export` in comments (reworded); S-CN4 committed
  (`c2c6fba`): re-snapshotted, rebuilt green (2,503 jobs). INT-8 not landed at the stop.
- Final: axioms 239 theorems clean; source rule 281 files 0 findings; profiles in `logs/R4d/`.
  Stopped (context long) with the RESULT's Pass 4 handover: S2, Sh's node link, Z, Lc, RS, AcceptTail.

### Pass 5 (R4e)

- Build tree `logs/fr-build-R4e` (copy of R4d's; `b.sh` logs to `logs/R4e/`; `MINE.txt` adds
  `FRSoundness4R4FrS`, `FRSoundness4R4Fld`). Baseline at HEAD `29d0016`: green (2,503 jobs).
  INT-8 not committed at the start (its journal: `finalsOf P` keeps its name and default values;
  `stmtOps4`'s `hashStmt` becomes `.input 1`).
- **`Fields4`** (`FRSoundness4R4Fld`): one choice of `zhat`, files and exports for every field,
  with `finRS`'s run kept (`fields_ex4`'s are existential per call, so two fields' facts could not
  be joined; RS's `α_j` must meet Z's/Lc's/Sh's/E's bindings on the same registers).
- **`RejS2`** (`FRSoundness4R4FrS`): `seedQ4`, `seed_bytesAt4`, `stmt_msg4`, `nStmt_eq4`,
  `bnd_seg4` (the log's public reads are π's); `last_view4` (segment `stmt` phase: `lastOps`'
  registers through P4a's `run_lastOps`, via `pureRun_append`/`pureRun_rebase`); `relSh4_of_fields`;
  `s1_view4`, `s2r_view4`, `s2_from_head4`; `sh_head_seg4/_node4` (head = `c0S`, `shiftTarget` at
  `shiftTargetS` a parameter `hST`); `s2_chk_*`, `not_rejS2_*`.
- **Item 3, the Sh binding**: `sh_bind_seg4` (`wSumSeg`, `linkSum_zero`), `sh_bind_node4`
  (`wSumNode4`, `CN4.wNS4_node4`): `oSh4 wNS4 κ es (fv (Rs 2) (zh.getD 2 0))`; op facts as
  parameters `hSM hSW hLW`, discharged by `segOps_of_meets` / `nodeOps_of_meets`.
- Traps: `congr 1` on `(w_out + w_in) * v = W * v` whnf's the whole weight (heartbeat timeout at
  the declaration): use `congrArg (· * v)`. `chk2F_c0 rfl` with implicit claims timed out: give
  `c0`/`c0'`. `exact ⟨…, _, Rs 2, rfl, …⟩` against `skeleton4` (R4c trap 1) again: give `fi`.
- **Items 4–6**: `FRSoundness4R4FrZ` (Z3 head `c0Z` via Z2's `lagrangeS`/`targetS`; `coords_pt_view4`,
  `pt_cAt4`, `uni_cAt5`; `peL_seg` needs `lastAt pe 19 = lastL`: `lastAt_pad19`; `z_chk4`),
  `FRSoundness4R4FrLc` (3.x's `lc_ii_run` ported as `lc_ii4` through `lc_bridge`, the kind flag from
  `hnode : P.kv.node p.tix = p.tix.isNode`), `FRSoundness4R4FrRS` (`rs_alpha4`: `exec_gFinRS`'s exports
  on `Fields4`; bindings `z_bind4`, `lc_bind4` (Horner by `simp` + `ring` on the 8 values), `e_bind4`,
  `sh_bind_*`; `not_rejRS4_*`).
- Coordinator mid-pass: S-T2 (`rsWeightS4`) and S-CN4b (`implN4T`, `targetSNode4_meets`) committed;
  re-snapshotted to `3ef2c51`, rebuilt green (2,514 jobs). `nodeC_params` instantiates the node
  statements' op parameters at `implN4T`. The `rsWeightS4` bridge is left as handover item 2.
- Controls `FRSoundness4R4FrCtrlB`. Final: axioms 311 theorems clean; source rule 295 files 0 findings;
  profiles in `logs/R4e/`. INT-8 still uncommitted at the stop. Stopped with the RESULT's Pass 5
  handover: INT-8 repairs, the RS weight bridge, `AcceptTail`, `hM`/`hL`.

### Pass 6 (R4f)

- Build tree `logs/fr-build-R4f` (copy of R4e's; `b.sh` logs to `logs/R4f/`; `MINE.txt` adds
  `FRSoundness4R4W0`, `FRSoundness4R4RndK`). Baseline at HEAD `2e5b79a`: `lake build FR` green
  (`logs/R4f/build-last.log` of the first run). INT-8 not committed at the start (its edits in the
  shared working tree; the build tree snapshots HEAD).
- **Item 1, the RS weight bridge** (`FRSoundness4R4W0`): `kf4_frob` (`kf4_eq`: one monomial per block,
  so Frobenius is `β ↦ β^(2^k)`), `mle_kind4` (the extension of `eq(q,·)·kf4_γ(block)` over `7 + n`
  coordinates is `kwSL4`; `mle_split` at `7 + n`, no use of `rsWeight_kind_eq`'s indicator form),
  `termK4`, the generic claim-by-claim `mle_wTab` (claim 2's term a hypothesis), **`mleW_node4`**
  (`rsWeightS4 ν` at L3β's `β`), **`mleW_seg4`** (3.x's `rsWeightS` at `β = 1`, any `kf`),
  `rsWS4`/`mleW_spec4`, **`wHat0_spec4`** (T4's `Ŵ₀(P₀)` = `rsWS4` + the cells' `eqCell` sum). Built
  first time except: `congr 1` on a `K` sum (R4e's trap 1 again: use `congrArg (· + _)`), a beta-redex
  before `rw [K.algebraMap_eq_ofF]`.
- **K rounds** (`FRSoundness4R4RndK`): `roundsK_log` (3.x's K rounds as `clR2 … 32 readK chK`, all real),
  `clValK` (R4b's `clVal` reads `initVals … false`: a K phase's first claim needs `true`),
  `genPhase4_roundsK` (stated for any `S`: at `seq4` the `simp` of `genPhase4` timed out),
  `rounds_atK4`, **`roundsK_view4`**, **`p1_view4`**, **`pf_view4`**. Trap: unqualified `sAt` is 3.x's
  (`phStart`); T4's is `T4.sAt` (`phStart4`).
- **`AcceptTail`** (`FRSoundness4R4Tail`): `FinLog4` (3.x's `FinLog` at T4's reads; every name
  qualified `T4.`), `acceptTail4_of_finLog` (built first time), `rounds_of_run4`, `FinRest4`,
  `acceptTail4_of_run` (`chain`/`len` from `runLog_chain4`, rounds from the run, the rest named);
  `not_rejF4a_seg4/node4`; controls.
- Final: build `FR` + R4's controls + `FRSoundness4R4Tail` green (2,517 jobs); axioms 354 theorems
  clean; source rule 299 files 0 findings (after rewording two "init" comments); profiles in `logs/R4f/`.
  INT-8 still uncommitted at the stop. Stopped (context long) with the RESULT's Pass 6 handover:
  INT-8 repairs, `start`, `cols` (`posOps4`), `link`, then `pf0`/`enc`/`fin` after INT-8.
