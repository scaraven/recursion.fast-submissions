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
