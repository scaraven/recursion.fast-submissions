# PORT — the decoder `nd`, the node links and the run existence on rev44 (revision 4.4.1's format) — RESULT

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `e464756` (A1′). Build tree
`logs/fr-build-PORT` (copy of `fr-build-A1`; `MINE` = every `FRX*`, `FRNodeLinks4*`, `FRNodeRun4*`,
`FRSubmission4*`; CPUs 16–23). Logs `logs/PORT/`. Journal `PORT-JOURNAL.md`. Nothing committed; no
sub-agents; no `sorry` in worktree sources.

## 0. Status

| Item | State |
|---|---|
| Owned modules (84) + `Solution` | **green** (`logs/PORT/build8.log`, 2,527 jobs) with the scaffold below |
| `FRSubmission4Fin` (`Open4F := Gaps4`, `certificate_sub4F`, `certified (h : Open4F)`) | **builds on rev44**, statements unchanged, `Gap4R` = `imp`, `aggChk` (A1′) |
| Realign deleted | **done**: `realign`, `rlBody`, `RlInv`, `rlBody_step`, `realign_sem`, `cso_realign`, `noLoopT_realign`, `realign_keep`, `rl_vS` gone; a plain copy loop replaces them |
| Kernel | owned modules ≈ 178 s → 39 s type checking (§4); `FRXOut4R` 80 s → 2.7 s |
| G5 (main `edf11b4`) carried by hand | `FRXNd4` (`sizeIR_seq`, `sizeIR_ndK4`), `FRXChain4`/`FRXChainFlock` (`map_range_getD`), `FRXOut4O.cso_outIR4` (opaque programs) |
| Axioms | 49 declarations (`logs/PORT/axioms.log`): every decoder theorem ⊆ {propext, Classical.choice, Quot.sound}; `sorryAx` only through the scaffold's RSV-S stubs (§5) |
| Source rule | 420 files, 0 findings (`logs/PORT/source-rule.log`) |
| Decoder KAT against a prover stream | **not run**: no rev44 node proof/stream exists before E1 (§6) |

**Scaffold (build tree only, `scaffold/apply.sh`).** HEAD-red RSV-S declarations replaced by `sorry` in the tree's
copies: A1's (`R4Fin.flag_gFinE/B'`, `Qry.noAsk_gFin{E,B',Pf}`, `R4FrE.fsMsgs4_ends`,
`R4PfFlag.gFinPf_reloc`, the `traces_spacers_le_qV` line) plus, newly red at HEAD after A1's commit:
`FRSoundness4R4FrE.{e_end4, not_rejEndE4_node, e_in4, e_fin4, not_rejFinE4_node}`,
`FRSoundness4R4FrRS.e_bind4`, `FRSoundness4R4Start.start4_of_fields`.

## 1. What changed, by module (`loc.py` code lines HEAD → now: `logs/PORT/loc-{before,after}.txt`)

| Module | Change | code |
|---|---|---|
| `FRXChain4` | `fsMsgs4_zero` re-proved for every `S` (`phasesOf S` now ends with `capChkPh S`, so not `rfl`); 482 → 486 positions; cap₀ at 20,896 (was 19,872); G5's `map_range_getD` in `fsMsgs4_items` | 187 → 189 |
| `FRXChainFlock` | G5: `map_range_getD`, `fsMsgs_items` linear | 182 → 188 |
| `FRXDec4Levels` | `cost_decLevels4`: 27,032,483,570,671 / 108,050,868,885,470 (by `#eval`, `scratch/DecLv.lean`) | = |
| `FRXDec4F0` | `fmt4_vals` (`pL4` 109,543; caps 20,896 … 61,856; `finFO4` 70,048; 876,304); `lv_cap4`: level 4's cap is 8 (`cap4 = 8`); `cost_le_decF04` literals | = |
| `FRXOut4` | **`reassemble4 S tr` over all 20 fields** (`nFields4`: fields 18/19 are `D`/`A`, the cap check's absorbs); `aB`/`aBytes4` gone; `reassemble4_size : … = piSizeOf S`; `pf4_size` 876,304 | 253 → 250 |
| `FRXPf4` | `pSeg4` over `nFields4`; `proof_words4` at `reassemble4 S` (no row-18 fit) | 434 → 432 |
| `FRXOut4W` | `vS` from `i·strideB`; `segTr_eq` etc. with `hD : i·strideB + segB ≤ streamB`; **`signedWords_agg` with the spacer entries** (`spW`, `spAns`) and the count `k·|items| + (k − 1)`; `sgnX_fits` via `aggTrace_length`/`mem_aggTrace` (the spacer query is 89 B) | 248 → 268 |
| `FRXOut4C` (kept) | `vS_get`: virtual word `u` is chain word `i·(strideB/8) + u` (no shift); new **`spAns_words`** (spacer `i`'s answer = four shift-1 pairs from chain word `i·(strideB/8) − 4`) | 85 → 114 |
| `FRXOut4R` | realign deleted; **copy loop** `cpBody`, `cpSeg`, `CpInv`, `cpBody_step`, `cpSeg_sem`; `nW` 185,344 → **193,888** (`segB/8`) | 429 → 364 |
| `FRXOut4P` | `cp_vS` (was `rl_vS`); `prevIR` copies | 145 → 143 |
| `FRXOut4A` | `segLoop κ P E` (a prefix program per segment); **`spPre`** (`i ≥ 1`: 13 constant words `spW` as a `.wd` segment over the buffer, then `shw4` at shift 1 from `i·(strideB/8) − 4`); `cntW` (`k·(|items|+1) − [0<k]`); `aggRegs` in two blocks, `qJ = k·sBlk − 3·[0<k]` (`jLv`); `aggL_eq'`, `AggN.nb`, `dV`, `chR_agg`, `aggRegs_sem`, `spPre_sem`, `cntW_val`, `aggIR4_sem` re-proved | 410 → 558 |
| `FRXOut4O` | `wf_segLoop`/`noLoopT` for the prefix; `cso_*` re-decided (`cso_cpSeg`, `cso_spPre`); G5's opaque-program `cso_outIR4` | 166 → 187 |
| `FRXNd4` | `outs_outIR4 ≤ 2,500,000`; G5's `sizeIR_seq`, `sizeIR_ndK4`, `sizeIR_decF04`, `decOk4_nd.size`, `nd_ne_ndNone` | 86 → 93 |
| `FRXOut4Ctrl` (kept) | `redirect_ctl` at `jLv 1`; new `spacer_ctl` | 15 → 18 |
| `FRXOut4E`, `FRXOut4F` | docs only | = |
| `FRNodeLinks4` | `acceptRunL4_node`: `FinLog4` has 9 fields (`cap`) | = |
| `FRNodeLinks4Run` | `fmAns_of_run4` over 486 positions; **`fsMsgs4_X : X.fsMsgs4 seq4 = R4.fsMsgs4 seq4`** (R4's table is now its own definition, so the old defeq became a 486-entry unfolding) | 101 → 105 |
| `FRNodeRun4S` | 8905 → 8783 (`itemsOf_seq4_len`) | = |
| `FRSubmission4Cert` | `pfHdr_pf4` without `aBytes4`; the `gap` row's doc | = |

**Format numbers re-decided** (all `decide`, they fail loudly if the layout moves): `hEnd_fit`, `wb_fit`, `stC_ok`,
`sel_ok`, `aggN` (`AggN` with `aggL maxK` 48,474 / 96,950), `chR_prev` (`24236 < hEnd`), `cso_*`. `memX4`/the buffer:
`bufB = 2^27`, `bufB + 2^22 ≤ |M|` still holds (`nd_out` builds). `decBudget4`, `sizeIR nd ≤ 2^19`
(`3·(57,067 + 48,000) + 15`), `outs ≤ outCap = 2^24`: `decOk4_nd` builds. Exact `outIR4` (`scratch/Cso.lean`): cost
120.7 M / 212.6 M / 367.8 M (was 163 M / 289 M / 505 M), outputs 911,525 / 1,518,411 / 2,428,763, size 46,500 /
46,588 / 47,965 at N2 / N4 / N8.

## 2. Statement changes (every one; each follows the format, none weakens a load-bearing statement)

- `FRXChain4`: `fsMsgs4_length` (486), `fsMsgs4_items` (`range 486`), `msgOkB_ctl`, `fsMsgs4_ctl`, `fsQ4_ctl`,
  `tabEnt4_ctl` (cap₀ 20,896): controls at the new `seq4`.
- `FRXDec4Levels.cost_decLevels4`, `FRXDec4F0.cost_le_decF04`, `fmt4_vals`: new literals. `lv_cap4`: `if i = 0 then 9
  else 8` (was `… else if i = 4 then 7 else 8`); `tape_cap4`'s `he` follows.
- `FRXOut4`: **`reassemble4 (S) (tr)`** (was `reassemble4 S aB tr`, fields 0–17 + row 18 fitted to `aB`), `pf4 =
  reassemble4 seq4`, `pfHdr_reassemble4` (no `aB`), `reassemble4_size : (reassemble4 S tr).size = piSizeOf S`, `pf4_size`
  876,304; `aBytes4` deleted. Reason: rev44's `piSizeOf` sums 20 fields; the old `pf4` was 77,872 bytes short.
- `FRXPf4`: `pSeg4` over `nFields4`; `proof_words4` at `reassemble4 S`.
- `FRXOut4W`: `vS` (stride); `segTr_eq`, `vS_length`, `hB_vS`, `pf4_words`, `logWords_segTr`, `entries_segTr`
  take `hD : i·strideB + segB ≤ streamB`; **`signedWords_agg`**: the count word is `k·|items| + (k − 1)` and the traces'
  part is `flatMap (fun i => (if i = 0 then [] else spW ++ packBytes (spAns … i)) ++ segOut (V i) … trBody4)` — this is
  exactly `V_A`'s trace (`aggTrace`, A1′), which the reader `sgn4` now returns.
- `FRXOut4C.vS_get`: `= chW … (i·(strideB/8) + u)` (was a shifted pair at `D = i(segB − 1)`).
- `FRXOut4R`: `nW = 193888`; `cpSeg_sem` replaces `realign_sem` (buffer word `u` = loader word `q + u`, `q = i·(strideB/8)`).
- `FRXOut4P.cp_vS` replaces `rl_vS` (same conclusion, `cpSeg`).
- `FRXOut4A`: `segLoop κ P E` and `segLoop_sem` (prefix `P` emitting `pre i`, output `flatMap (pre i ++ out i)`);
  `aggL_eq' (hk : 1 ≤ k) : aggL k = jLv k + 1`; `AggN.nb` (stride); `dV`, `chR_agg`, `aggRegs_sem` at `jL = jLv k`.
  **`aggIR4_sem`, `prevIR_sem`, `outIR4_sem` unchanged.**
- `FRXOut4O.cso_outIR4`: outputs `≤ 2,500,000` (was 2,300,000), size `≤ 48,000` (was 45,000); `FRXNd4.outs_outIR4`
  follows. `cso_pfIR`/`cso_trS`/`cso_trB`: new exact values.
- `FRXOut4Ctrl.redirect_ctl`: stated at `jLv 1` (= the old `1·(segB−1)/64` numerically).
- `FRNodeLinks4Run.fmAns_of_run4`: `∀ q < 486` (was 482; stronger).
- `FRNodeRun4S.execA_proto`, `slotImp_of_runA`: `hl : tr.length = 8783` (was 8905; `slotTr4_length`).
- Unchanged: `Open4F`, `open4_of_F`, `certificate_sub4F`, `certificateR_sub4F`, `certified`, `Open4`, `LinksD4`,
  `readW4`, `nd`, `decOk4_nd`, `nd_out`, `nodeDec4_nd`, `links4_sigH`, `hL_of_res`, `gap4Imp_of_run`'s conclusion.

## 3. Decisions and deviations

1. **The buffer and the `ldIx` redirect stay.** With `strideB ≡ 0 (mod 64)` no shift is needed, but (a) the last
   segment's final block is the candidate block `finBlk` when `k < maxK`, so the loader keeps its redirect, and (b)
   `segIR` reads a linear shape, so segment `i`'s words still go to the buffer at `2^27` — by a plain copy (`cpSeg`,
   one load + store per word, ≈ 17.3 M steps a segment) instead of the shifted pair. Not dead, so not removed.
2. **`FRXOut4C` and `FRXOut4Ctrl` are kept, not deleted.** Only their realign parts were dead: `FRXOut4C` holds `chW`,
   `chainBytes4_getD`, `hAe_words`, `hAn_word` (used by the header and now `spAns_words`); `FRXOut4Ctrl` holds the
   output's controls (`redirect_ctl`, `ladder_ctl`, `offB_ctl`, `kc_ctl`, `nd_ctl`, new `spacer_ctl`).
3. **A1′'s "`nW` unchanged" was wrong**: `segB` grew with RSV2 (1,482,752 → 1,551,104), so `nW = segB/8` is 193,888.
4. **`pf4` gained fields 18/19** (§2): A1′ listed `pf4/reassemble` as unchanged; the build showed
   `reassemble4_size` false at rev44.
5. **Spacer emission**: the 89-byte query is a constant (`spW`, 13 words, emitted as `.wd` constants through
   `bufSeg`), the answer is read from H (`shw4`, shift 1): A1′ §7's "1-byte shift of 5 words" is four shifted pairs.
6. **Kernel trap found and fixed** (`aggIR4_sem` 102 s → 4 s): `simp only [List.nil_append]` under a binder is a
   definitional (`rfl`-lemma) step, so the kernel checked `[] ++ packBytes (bl (pf4 …)) ≡ packBytes (…)` by unfolding
   `packBytes` of a whole proof. Fixed by rewriting with the theorem (`List.flatMap_congr … List.nil_append`). Found
   with G5's `KProf` and a scratch congrArg-mismatch scanner (`logs/fr-build-PORT/scratch/Diff.lean`, outside the entry).

## 4. Kernel time (type checking, `lean -DElab.async=false --profile`, one core, shared VM under load)

After: `logs/PORT/prof-after.txt`, `prof-after2.txt` (`profile-<m>.log`). Before: rev44 HEAD could not build these
modules (upstream red), so "before" is main's last measurement of the same module (`flock/logs/G5/prof-*-before.log`,
`S-H4j`, `S-H4h`, `S-H4e`, `S-L4`, `B3`).

| Module | before (main) | after (rev44) |
|---|---|---|
| `FRXOut4R` | 80 s (G5-before; `realign_sem` alone 44.8 s, H-cert3) | **2.74 s** |
| `FRXNd4` | 36.6 s (G5-before) | **2.62 s** (G5's helpers) |
| `FRXChain4` | 16.7 s | 7.1 s |
| `FRXChainFlock` | 14.6 s | 5.12 s |
| `FRXOut4O` | 14.7 s (G5-before; 6.87 s S-H4j) | 4.71 s |
| `FRXOut4A` | 3.03 s | 4.04 s (spacer proofs) |
| `FRXDec4Levels` | 5.3 s | 4.95 s |
| `FRXDec4F0` | 3.12 s | 3.3 s |
| `FRXPf4` | 1.94 s | 1.87 s |
| `FRXOut4W` | 0.88 s | 0.79 s |
| `FRXOut4C` | — (not profiled on main) | 1.01 s |
| `FRXOut4P` | 0.70 s | 0.66 s |
| `FRXOut4` | — | 0.55 s |
| `FRNodeLinks4Run` | 0.43 s | 1.32 s (`fsMsgs4_X`, ≈ 0.9 s) |
| `FRNodeRun4S` | 0.12 s | 0.20 s |
| `FRNodeLinks4`, `FRXOut4Ctrl`, `FRSubmission4Cert`, `FRSubmission4Fin` | < 0.05 s | < 0.05 s |
| **sum (comparable rows)** | **≈ 178 s** | **≈ 39 s** |

Against main *after* G5 (`realign_sem` 0.03 s there), the net saving of this port is smaller: the realign module's
remaining weight, the copy loop being shorter, and G5's helpers re-applied.

## 5. Axioms and what is still open

`logs/PORT/axioms.log` (`ax/AxPORT.lean`): `decOk4_nd`, `nd_out`, `nodeDec4_nd`, `outIR4_sem`, `aggIR4_sem`,
`prevIR_sem`, `spPre_sem`, `segLoop_sem`, `cpSeg_sem`, `cpBody_step`, `cp_vS`, `vS_get`, `spAns_words`,
`signedWords_agg/_prev`, `sgnX_fits`, `chR_agg`, `aggRegs_sem`, `cntW_val`, `cso_outIR4`, `proof_words4`,
`reassemble4_size`, `pfHdr_reassemble4`, `pf4_size`, `cost_decLevels4`, `cost_le_decF04`, `fmt4_vals`, `lv_cap4`,
`fsMsgs4_*`, `fsMsgs4_X`, `fmAns_of_run4`, the controls: ⊆ {propext, Classical.choice, Quot.sound}.
`certified`, `certificate_sub4F`, `open4_of_F`, `certificate_sub4`, `linksD4_of_run`, `acceptRunL4_node`, `hL_of_res`,
`links4_sigH`, `execA_proto`, `slotImp_of_runA`, `gap4Imp_of_run` show `sorryAx` **only through the scaffold's
RSV-S stubs** (the R4/X4 run chain and `noAsk_finOps4`); the worktree has no `sorry`.

Remaining red in my modules: **none**. Remaining open for the certificate: `Open4F = Gaps4` (`Gap4R` = `imp` via
B3's `gap4Imp_of_run` + B4's ask templates, and `aggChk`, B4) and RSV-S's HEAD-red declarations.

## 6. Tests

- Proved, not sampled: the output program's semantics (`outIR4_sem`) covers the spacer entries and every `k ≤ maxK`.
- **Not run: a decode KAT against the prover's dump.** S-H4's probes were toy runs (`lagIR`, `E4X` toys); a KAT of
  `nd` needs a node proof π and its log at 4.4.1's format, i.e. E1's prover. A1′'s `logs/A1p/nodedump/` holds the node
  circuit's rows (M rows, link rows), not a proof stream, so it cannot feed the decoder. Measured instead: the program
  sizes/costs by `#eval` (`scratch/Cso.lean`, `scratch/DecLv.lean`, `scratch/F0.lean`, `scratch/Ch4.lean`).

## 7. Requests for other tracks

- **RSV-S (S2a/S2b)**: HEAD is red at `FRSoundness4R4FrE.{e_end4, not_rejEndE4_node, e_in4, e_fin4, not_rejFinE4_node,
  fsMsgs4_ends}`, `FRSoundness4R4FrRS.e_bind4`, `FRSoundness4R4Start.start4_of_fields`, `R4Fin.flag_gFin{E,B'}`,
  `Qry.noAsk_gFin{E,B',Pf}`, `R4PfFlag.gFinPf_reloc`, and `FRSoundness4Qry.ks_queriesC4` still needs A1′'s one-line
  change (`exact traces_spacers_le_qV`). My build depends on them only through the scaffold.
- **B4**: `gap4Imp_of_run` is unchanged in shape; its trace length is now 8,783 (`slotTr4_length`).
- **Orchestrator**: (a) G5's `FRNodeLayout4`/`FRNodeRows4Ext` changes are not in rev44 (as instructed); (b) the
  `nW`/`pf4` corrections to A1′'s list (§3.3–3.4); (c) `FR.lean` needs no change (it imports `FRXOut4Ctrl`,
  `FRSubmission4Fin`, `FRNodeRun4Ctrl`, which all build).

## 8. Files touched (worktree)

`submissions/flock-recursive/lean/`: `FRXChain4`, `FRXChainFlock`, `FRXDec4Levels`, `FRXDec4F0`, `FRXOut4`, `FRXPf4`,
`FRXOut4W`, `FRXOut4C`, `FRXOut4R`, `FRXOut4E`, `FRXOut4F`, `FRXOut4P`, `FRXOut4A`, `FRXOut4O`, `FRXNd4`,
`FRXOut4Ctrl`, `FRNodeLinks4`, `FRNodeLinks4Run`, `FRNodeRun4S`, `FRSubmission4Cert` (`.lean`);
`docs/v4/flock-recursive/stages/PORT-RESULT.md`, `PORT-JOURNAL.md`. Build tree and logs: `logs/fr-build-PORT/`,
`logs/PORT/`.

## Erratum (orchestrator, from the review of `c4eca2b`)

"`pf4` was 77,872 bytes short" (§ on `reassemble4`, and the commit message) is wrong. Fields 0–17
sum to 799,280 at rev44, so the old `pf4` was short by 876,304 − 799,280 = **77,024** = 27,872 (D) +
49,152 (A). The review found no blockers; its notes: the literals `486` (`FRNodeLinks4Run:67,71`) and
`8783` (`FRNodeRun4S:48,90`) could be stated as `(fsMsgs4 seq4).length` / `(itemsOf seq4).length`
(safe today: the decided length lemmas would fail loudly), and `FRShape4:389`'s docstring still says
`piSizeOf seq4 = 798,192`.
