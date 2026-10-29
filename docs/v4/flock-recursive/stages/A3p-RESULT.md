# A3′ RESULT: blocked. The batched cap check (β) is unsound as built; the certificate cannot be restated

Track A3′, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `f853d37`.
Build tree `logs/fr-build-A3`, logs `logs/A3p/`. Journal: `stages/A3p-JOURNAL.md`. No sub-agents,
nothing committed, **no source file changed**.

## 0. Summary

- **Stopped at item 1.** PACK §3.3's soundness argument, and the A3′ restatement in §9.1, need the
  path digests `cur_r` to be fixed before ζ: "a polynomial of degree ≤ 870 in ζ whose
  coefficients are fixed by items ≤ Q.4, before ζ".
- **They are not fixed.** The Fiat–Shamir chain absorbs no column, no sibling and no path digest:
  - `fsItems4` is "the item sequence without the column and node queries";
  - Q.i has no Fiat–Shamir item (`fsStarts4`: Q.i and P3.i both start at 370, 397, 421, 443, 463).

  So ζ and z are functions of the chain alone, and the prover picks π's columns and siblings after
  both are known.
- **The consequence is a practical forgery, not a proof gap.** `F` has characteristic 2, and (I)
  is GF(2)-linear in the digest bits. Bellare–Micciancio's linear-algebra attack opens arbitrary
  (uncommitted) columns that pass (I) and (II). It costs about 20 k compressions and one
  512 × 871 GF(2) elimination (§2).
  - `ks_rev4H`/`certificate_rev4H` at A2′'s V are therefore **false** at any small ε, with
    `logCap = 2^96` to spare.
  - No restatement can make them build. In particular `pathDig (L, es)` does not exist: V's
    `cur_r` is a function of π.
- **ε**, as asked: `D_ζ ≤ 870/2^256` and `D_z ≤ 1,407/2^256` both fit inside εR's slack (§3). That
  is moot until the construction binds `cur_r`.
- **Fix: bind the path digests in the chain before the batching challenge** (§4). The cheapest
  sound variant I see overflows N8's H by 1,280 blocks. The orchestrator must rule.

## 1. What V does (A2′'s code, read)

- `FRVIR4.posOps4`:
  - `piField 0 (co + p·colBytes i)`: the column, from π;
  - `merkleOps4 … (so + p·sib·32)`: the siblings, from π;
  - `shrN`: the cap index.

  There is no compare. `cur_r = curOfY sL y` is the path's root.
- `FRVIRFinals4.capChkOps`:
  - `ζ = chK` of `(lvOuts fi 4 4)[1] − 1`: P3.4's first answer;
  - `z = chK` of CapChkZ's answer;
  - `aL += ζ^r·lo(cur_r)`, `aH += ζ^r·hi(cur_r)` (`splitDigest`, `mulKF`, `addK`);
  - `aZ`, and the entries' sums with `A` (π field 18);
  - three `assertEq`.

## 2. The attack (journal §4 has the details)

- **Linearity.** Fix ζ. Then `φ_r(d) := (ζ^r·lo d, ζ^r·hi d) ∈ K² ≅ GF(2)^512` is GF(2)-linear in
  `d`'s 256 bits (`CharP F 2`, `CharP K 2`).
- **The identities.** Let `T := Σ_k A_k·(lo cap_k, hi cap_k)`, with `A` the honest vector for ζ and
  the `k_r`. Since `A` is honest, (II) holds exactly, and (I) reads `Σ_r φ_r(d_r) = T`.
- **Two openings per read.** For each read, take two openings whose fold is the value the prover
  needs (e.g. one top sibling changed: one compression). Call their roots `d_r⁰` and `d_r¹`.
- **The linear system.** Solve `Σ_r b_r·φ_r(d_r¹ − d_r⁰) = T − Σ_r φ_r(d_r⁰)` over GF(2). There
  are 871 unknowns and 512 equations, and the system has full rank except with probability
  `≤ 2^{−358}`. Open read `r` with `d_r^{b_r}`.
- **Why this forges.** The openings are free, so a cheating prover answers every query with a
  column of the encoding it needs (Ligerito without binding). The PIOP's committed word is then
  never checked, and a false statement is accepted.
- **Any per-read additive batching fails the same way.** A logUp form fails too, and it is worse
  in characteristic 2: a repeated fake digest cancels mod 2.

## 3. ε (the brief's question)

| Row | Where | Bound | Budget | Fits |
|---|---|---|---|---|
| `D_z` | phase 53, single squeeze (`hsingle`) | count 1,407 | `N = 239·2^128` (`N_le`) | yes |
| `D_ζ` | P3.4's 5-squeeze phase (`hround`; `finP3 4 = finP2 4` today, no κ_c row) | `870/2^256` | `deltaR = epsD − 2^{−142}`, ≈ `15/2^124` | yes |

With these rows `εR = 15/2^124` and `claim.json` would stand. But `D_ζ` cannot be stated (§0).

## 4. Fixes, for the orchestrator (numbers from A2′'s §6 constants)

1. **(β′) Bind, then batch.** The phases after `Pf`:

   ```
   absorb D (field 19: the 871 path digests, 27,872 B); squeeze ζ;
   absorb A (45,088 B); squeeze z
   ```

   - **V.** Per position, a **static** `piDigest (fieldOff D + 32r)` and `assertEq cur`. The index
     is static, so there is no mux: this is what B2 needed. (I)/(II) then run on `D`, and PACK's
     SZ argument holds, because `D` is in the chain before ζ.
   - **The dooms.** `D_ζ`/`D_z` become prefix-determined, with `pathDig := D_r` from the chain.
     §9.1's statements then work, with `D_ζ` at the new ζ squeeze.
   - **Stream.** `80 + 27,872 + 80 = 28,032 = 64·438`, still whole blocks. A segment is then
     `1,556,032 = 64·24,313` bytes.
   - **N8.**
     - Stride 24,315, and `aggL 4 = 97,258`.
     - `hUsed = 2·97,258 + 2,196 = 196,712`, `hEnd = 196,720`, and `lBase = 196,864`.
     - The bound is 195,584, so **N8 overflows by 1,280 blocks**. Today's spare is 2,304
       blocks, and 8 slots × 438 = 3,504.
   - **Other sizes.** `|π| = 871,152`. Items 8,909, so `qV = 35,639 ≤ 36,000`.
2. **N8 levers to make (β′) fit.** This is the orchestrator's call: 7 segment slots; or a
   smaller `A`; or deeper caps at some level, which PACK §3.2 priced.
3. **Revert to the pre-A2′ V.** That V does a per-position dynamic `piDigestAt` and `assertEq`,
   and it is sound. The chain at HEAD `4d5700c` is certified. It keeps the R1CS mux cost that B2
   was meant to remove.

PACK §3.2's table and the PACK review (PK-*) both miss this. The phrase "fixed by items ≤ Q.4"
treats V's query order in the stream as if it were the Fiat–Shamir chain. Column and node queries
are stream items, not chain items.

## 5. State left

- **Source.** No module edited. The worktree is A2′'s HEAD, red in `FRSoundness4TailD` and
  `FRSoundness4R4Run`.
- **Build tree** `logs/fr-build-A3`:
  - a copy of `fr-build-orch`, with `fr-build-A2`'s oleans;
  - `snap.sh` pinned to the main worktree's `logs/pkgs` and `logs/org20`, the paths the oleans were
    built against;
  - `MINE="FRSoundness4TailD FRSoundness4R4Run"`.

  The baseline `./b.sh FR` reproduces A2′'s two red modules (`logs/A3p/build-0-baseline.log`,
  2,575 jobs).
- **Not done.** Items 1–5 (restatements, `482 → 484`, the re-run, controls, checks). Each depends
  on the ruling in §4. Under (β′), §9.1's plan applies almost unchanged, with `pathDig := D_r`
  and the position checks restated to `cur = D_r`.

## 6. Open questions

1. Which fix: (β′) with an N8 lever, the revert, or another binding?
2. Under (β′), should ζ stay P3.4's? It cannot: ζ must come after `D`. So (β′) has two new
   squeezes, and PK Q1's "a fresh ζ buys nothing" is withdrawn.
3. Should A2′'s V go back to `4d5700c`'s V until the ruling, so that `v4/rev44` does not carry an
   unsound verifier?

---

# Run 2 (2026-10-29): the chain restated for (β′), certificate green at εR = 15/2^124

Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `394f6ce` (A2″ + main). Build tree
`logs/fr-build-A3b` (a copy of `fr-build-A2pp`, re-snapshotted on HEAD; `mymods.txt` lists the modules
linked to the worktree), logs `logs/A3b/`. Journal: `A3p-JOURNAL.md` § Run 2. No sub-agents, nothing
committed. Spec: PACK-4.4 §11.1, §11.5, as corrected by `reviews/PACK-4.4-b2-review.md` PB-M1.

## R2.0 Summary

- **Done: `lake build FR Solution FRSubmission4Cert FRSoundness4XCtrl FRNodeSound4Ctrl
  FRSoundness4TailShift` is green** (`logs/A3b/build-5.log`, 2,589 jobs), on A2″'s (β′) V.
  `ks_rev4H`, `certificate_rev4H`, `ks_rev4GR`, `certificate_sub4` and `certified` keep their
  statement text and ε (`εR = 15/2^124`, no constant touched, `claim.json` unchanged). Axioms:
  `propext`, `Classical.choice`, `Quot.sound` only (`logs/A3b/axioms.log`). Source rule: 0 findings.
- **All 10 red declarations are fixed** (§R2.2), and the false-but-compiling statements are restated:
  `capO` → `dO` (the position reference now compares `cur` with the static `D_r`), every 482 meaning
  "end of the chain" → 486, the phase table to 55.
- **The batched cap check is proved on the run**: new `FRSoundness4R4Cap` runs `capChkOps` family by
  family and gives `T4.capChk4` on the log (`capChk4_of_fields`, now `FinRest4.cap`).
- **The doom chain is PB-M1's**, with one addition the review missed (§R2.1): the composed checks
  `RejC` must be guarded by the cap truth once `D` is in the chain (`RejG`), or the end of an accepted
  chain cannot be refuted when `D` is false.
- **`cap_of_chk` is proved** (`T4.cap_of_chk : capChk4 → ¬DZeta → ¬DZ → truthCap`), and the two
  escape counts are kernel theorems: `card_dZeta ≤ 870`, `card_dZ ≤ 1,535`, both `≤ N = 239·2^128`.
- **Controls**: `capChk_pos`, `capChk_neg`, `dZeta_ctl`, `dZeta_neg`, `dz_ctl` (§R2.5).

## R2.1 The gap in PB-M1, and its fix (no ε change)

- PB-M1 refutes `DT 55`'s three disjuncts under acceptance. But the composed doom is
  `DC (RejC …) (Dp DkC)` and `RejC ∋ RejT`.
- `RejT`'s round-0 check of P1.(i+1) is `Chk2` against `lvC (i+1) = vNext … (c1 i)`, the batched folds
  `foldAtN` of the **committed** words. An accepted run satisfies it only if each opened column is the
  committed one: `y_eq_foldAtN4` needs `openPath … = some (capDig …)`, which is `truthCap` now.
- So with `D` false, an accepted chain can carry `RejT` from P1.1 on:
  - `DC` holds at the end through `RejT`, so `hend` (`¬DC` at the end) is unprovable;
  - the potential charges no `ζ`/`z` escape once `Rej` holds (`stepObl_compose`).
- **Fix**: `RejG RejF c₀ L es := RejC RejF c₀ L es ∧ cdOK es`, with
  `cdOK es := es.length ≤ phStart4 52 ∨ truthCap es`.
  - `RejG` is not monotone at the `CapD` absorb: a `RejC` log can lose `cdOK`.
  - So `PhaseObl.rej` becomes `RejSq` (`sq`, `stab`; no `mono`), and a new field
    `PhaseObl.hrej : Rej L es → Rej L (es ++ [x]) ∨ Dk … (es ++ [x])` covers absorbs. At `CapD` a lost
    `cdOK` is `¬truthCap`, which is `DT 52` (`hrej_G`).
  - The generic `StepObl` still only needs the composed `DC` to be monotone at absorbs, which holds.
- At the end of an accepted chain: `truthCap` gives `¬RejC` (the old argument); `¬truthCap` gives
  `¬cdOK`. With PB-M1's three disjuncts refuted, `not_DC_end` holds.
- Before `CapD` (every front and level obligation), `RejG ↔ RejC` (`not_rejC_of`, `rejG_of`), so
  `FrontObl` is unchanged.
- **Consequence for the open residuals.** `X4.GoodX` (the good logs of the open residual `hL` in
  `ks_rev4H`/`ks_rev4GR`) is now `muT (RejG RejFX c0X) …` instead of `muT (RejC …)`. The theorem texts
  are unchanged; the residual's log predicate is the new potential's (§R2.4).

## R2.2 The red set: what each became

| Module | Declaration | Now |
|---|---|---|
| `TailD` | `phOf_ge` | split by `phStart4 52 … 55` (`p < phStart4 52 → 51`, `= 52`, `= 53`, `= 54`, `≥ phStart4 55 → 55`) |
| `TailD` | `rounds_check` | 486 items |
| `TailC` | `tailCls_check` | classes checked up to `phStart4 52`; the four cap positions are `cap_items` |
| `R4Run` | `fsMsgs4_len` | 486 |
| `R4Run` | `fsCheck_qOf` | `q < 486` |
| `R4Run` | `matches_fsQ4` | 486 |
| `R4Run` | `finOps4_eq` | `finOps4 P = opsOfFields finRS (rest ++ [capF P.S])` (the cap check as a 13th field) |
| `R4PosT` | `exec_posOps4` | the reference `posT4` takes `dO` and checks `cur = D_r` (π at `dO + 32·p`, static) |
| `R4Qv` | `genPhase4_queries_ops` | `posOps4 … (dOff4 S i) …` |
| `R4PfRun` | `gLvsOps_4` | proof only: `seq4_ell_star` (`ell` agrees with `lvlStar` at every level) |

## R2.3 What was built, file by file (code lines by the core's `loc.py`, HEAD → now)

| Module | Change | code |
|---|---|---|
| `FRSoundness4TailCap` (new) | the cap check on the log: `dAt`, `zetaK`, `aAt`, `zK`, `kCap`, `capG`, `loD`/`hiD`, `capIL/IR/IIL/IIR`, `aHat`, `aHon`, `capChk4`, `capSig0`, `truthCap`, `DZeta`, `DZ`, `cap_of_chk`; `sum_aHat`, `capI_sub`, `capII_sub`, `card_poly_root` (SZ over `K`), `card_dZeta`, `card_dZ`; congruences `capD/capZeta/capA/capZ_congr`; controls | — → 383 |
| `FRSoundness4TailStep` | `RejSq`, `PhaseObl.rej : RejSq`, `PhaseObl.hrej`, `stepObl_compose` with `hrej` | 670 → 683 |
| `FRSoundness4TailD` | `DTl` (levels), `DCap*` (PB-M1's chain), `DT` = levels / Pf / cap; `DT_lvl`, `DT_cap`; `phOf_check`/`phOf_bounds` to 55; `phOf_ge`; `rounds_check` | 197 → 226 |
| `FRSoundness4TailM` | `DT_Q`; `DPf_append`, `DCap_stab`; `DT_stab` to 55 | 261 → 279 |
| `FRSoundness4TailC` | `front_check` to 30 phases; `tailCls_check` to `phStart4 52`; `cap_items`, `cdOK`, `RejG`, `rejG_sq`, `hrej_G`, `habs_cap`, `single_cap`; `phaseObl_of`, `muT_laws_of_front`, `chainStab_of` at `RejG` | 323 → 471 |
| `FRSoundness4TailLig` | `AcceptTail` (`len`, `p1`/`lvl4` under `truthCap`, `cap`); `not_DC_end` (PB-M1 + guard); `colOf_of_dpath`, `foldAt_of_dcols`, `truthP3_four_of_dcols`; `RejG` in `tail_of_accept`, `ks4_of_front`; control `not_acceptTail_of_cons` takes `truthCap` | 400 → 448 |
| `FRSoundness4R4Run` | 486; `capF`, `opsOfFields`, `finals_ops_fields`, `runFields_snoc`, `opsOfFields_snoc`, `finOps4_eq`, `noAsk_finOps4`; `accept_chain4` over `opsOfFields rs fs` | 179 → 226 |
| `FRSoundness4R4At` | `SkRun4` at 486; `skRun4_of_accept` via `finals_ops_fields` | 157 → 158 |
| `FRSoundness4R4PosT` | `capO` → `dO`; `posT4` checks `cur = D_r`; `exec_posTail4` (static `piDigest`); `posT4_path`/`posAllT4_path` give the path to `D_r` and the cap-index and `D_r` registers | 327 → 350 |
| `FRSoundness4R4Qv` | `dOff4`; `queries_view4` with the `kOfY`/`dOfY` registers and the path to `D_r` | 163 → 178 |
| `FRSoundness4R4Cols` | `dMsg4`, `dAt_eq4`; `ys_facts4`, `cols4_of_run` end at `T4.dAt` | 166 → 171 |
| `FRSoundness4R4Cap` (new) | `reloc_capChk`; block runs (`pureRun_vals`, `run_head`, `run_powChain`, `run_bitPow(s)`, `run_macD(s)`, `run_macA(s)`, `run_asserts`); `lvR`/`qR`, `sum_reads`, `ranges_getD`; **`capChk_run`**; `one_ans4`, `reads_view4`, `aMsg4`, `aAt_eq4`, `capG_eq4`, `loD/hiD_bytesAt`; **`capChk4_of_fields`** | — → 986 |
| `FRSoundness4R4Tail` | `FinLog4`/`FinRest4.cols` to `dAt`, new `cap`; `y_eq_foldAtN4`, `p1_of_finLog4`, `lvl4_of_finLog4` take `truthCap`; `acceptTail4_of_finLog` at 486; control `finLog4_rounds_of_acceptTail` takes `truthCap` | 160 → 159 |
| `FRSoundness4R4Acc`/`Ex`/`Fld` | `rest ++ [capF]`; `Fields4.cap` | 73/107/96 → 73/110/108 |
| `FRSoundness4R4FrE`, `R4P4` | `SkRun4.hq` bound (proofs only) | 453, 322 |
| `FRSoundness4R4LinkP` | imports `R4Cap`; `finRest4_of_fields` adds `cap` | 117 → 118 |
| `FRSoundness4R4PfRun` | `seq4_ell_star`, `gLvsOps_4` | 397 → 402 |
| `FRSoundness4P4aDF` | `ph_check4a`/`phStart4_mono` to 55 | 395 |
| `FRSoundness4XLaws` | `GoodX` at `RejG`; `stmt4_of_tail`'s length | 81 |
| `FRSoundness4XRun` | `FinLog4` built with `hFR.cap` | 216 |

| `FRSoundness4CapCtrl` (new) | `dZeta_inst`: a concrete chain in `D_ζ` (imported by `FR`) | — → 88 |
| `FR` | `import FRSoundness4CapCtrl` | +1 line |

Touched: 25 modules (3 new), 5,260 → 6,996 code lines in the 23 soundness modules (+1,736; the two new
proof modules 1,369), plus the control module and one import line.

## R2.4 Every statement change, with its reason

**Kept (text and ε):** `ks_rev4H` (both namespaces), `certificate_rev4H`, `ks_rev4G`, `ks_rev4GR`,
`ks_rev4GH`, `certificate_sub4`, `certificateR_sub4`, `certified`. `epsR`, `epsD`, `epsH`, `deltaR`,
`N_le`, `logCap`, `badCount`: untouched. The new rows fit `hsingle`'s `N = 239·2^128` with room.

**Definitions whose meaning changed** (all forced by (β′)):
- `T4.DT`: phases 52–55 carry PB-M1's chain (`DCapD` … `DCapZ`); the level part is `DTl`, unchanged.
- `T4.PhaseObl`: `rej : RejSq` (was `RejOK`), new field `hrej` (§R2.1). `stepObl_compose` takes `hrej`.
- `T4.AcceptTail`: `len : phStart4 55 + 1 ≤ length` (was `pfStart + 14`); `p1`, `lvl4` under
  `truthCap` (they read the committed words); new `cap : capChk4`.
- `R4.FinLog4`/`FinRest4`: `cols` ends at `some (T4.dAt es i q)` (was `capDig …`, which V no longer
  checks); new `cap : T4.capChk4 es`. `Fields4`: new `cap` (the cap check's run).
- `R4.SkRun4`: `len`, `hq` at 486. `R4.posT4`/`posAllT4`: `dO` (the level's first committed digest)
  instead of `capO`, and the check `cur = D_r`.
- `X4.GoodX`: the potential `muT (T4.RejG RejFX c0X) …` (was `RejC`). It occurs in the open residual
  `hL` of `ks_rev4H`/`ks_rev4GR`/`Resid4G*` (the node links), so that residual is now stated over the
  new potential's good logs; the theorem texts are unchanged. Reason: §R2.1 (the old potential cannot
  refute an accepted chain with `D` false).

**Theorems restated** (statement change, reason):
| Theorem | Change | Reason |
|---|---|---|
| `T4.phOf_ge` | split at `phStart4 52 … 55` | the phase table has 56 phases |
| `T4.phOf_bounds`, `phOf_check` | `≤ 55`, range 486 | idem |
| `T4.DT_stab` | `k ≤ 55` | idem |
| `T4.rounds_check` | 486 items | idem |
| `T4.tailCls_check`, `tail_cls` | up to `phStart4 52` | the cap positions are handled by `cap_items` |
| `T4.front_check`, `front_facts` | 30 phases after P1.0 | `phOf_lt_26` with `phOf ≤ 55` |
| `T4.phaseObl_of`, `muT_laws_of_front`, `chainStab_of`, `ligerito_final_of_walk`, `not_DC_end`, `tail_of_accept`, `ks4_of_front` | `RejC` → `RejG` | §R2.1 |
| `T4.not_DT_of_not_DC` | generic in `Rej` | idem |
| `T4.not_acceptTail_of_cons` (control) | takes `truthCap` | `AcceptTail.lvl4` is conditional |
| `R4.fsMsgs4_len`, `fsCheck_qOf`, `matches_fsQ4`, `runLog_chain4`, `acceptTail4_of_finLog` | 482 → 486 | the chain's length |
| `R4.finOps4_eq` | `= opsOfFields finRS (rest ++ [capF])` | the cap check is appended to the finals |
| `R4.accept_chain4` | over `opsOfFields rs fs` | idem |
| `R4.exec_posTail4`, `exec_posOps4`, `exec_posAll4`, `posT4_path`, `posAllT4_path`, `exec_queries4`, `genPhase4_queries_ops`, `queries_view4` | `dO`/`dOff4`, `D_r`; the views add the cap-index and `D_r` registers | V reads `D_r` statically and asserts `cur = D_r` |
| `R4.ys_facts4`, `cols4_of_run` | end at `T4.dAt` | idem |
| `R4.y_eq_foldAtN4`, `p1_of_finLog4`, `lvl4_of_finLog4` | take `truthCap` | the opened column is the committed one only then |
| `R4.fields_of_accept4`, `fields_ex4`, `fields4_of_accept` | (statements unchanged; proofs over `rest ++ [capF]`) | — |
| `R4.finLog4_rounds_of_acceptTail` (control) | takes `truthCap` | `AcceptTail.p1` is conditional |
| `P4a.ph_check4a`, `phStart4_mono` | to 55 | the phase table |

**Proof-only fixes:** `R4.gLvsOps_4` (`seq4_ell_star`), `R4.capDig_eq4`, `R4.finalAt_eq4`,
`R4.msg_abs4` (the `SkRun4.hq` bound), `X4.stmt4_of_tail`.

## R2.5 Controls

| Control | Shows |
|---|---|
| `T4.capChk_pos` (+) | an honest prover passes: `truthCap ∧ aHon → capChk4` (the three asserts are complete) |
| `T4.capChk_neg` (−) | a dishonest `A` fails (II) at some `z`: at `CapChkZ`, `¬aHon → ∃ a, ¬capChk4 (ext1 es a)` (≤ 1,535 of 2^256 answers pass) |
| `T4.dZeta_ctl` (+) | `DZeta` at `CapZeta`'s answer `a` is exactly "`D` false and `chK a` a common root of (I)'s two polynomials" (`sigP loD`, `sigP hiD`) — a `D_r ≠ cap[k_r]` log at a root `ζ` is in `D_ζ` |
| `T4.dZeta_inst` (+) | a concrete chain in `D_ζ`: two reads committed to `d₁` under zero caps, `ζ = 1` a root in characteristic 2 (`FRSoundness4CapCtrl`) |
| `T4.dZeta_neg` (−) | a false `D` is not an escape at every `ζ`: `¬truthCap → ∃ a, ¬DZeta (ext1 es a)` |
| `T4.dz_ctl` (+) | `DZ` at `CapChkZ`'s answer is exactly "`A` dishonest and `chK a` a root of `Σ_k (A_k − Â_k)·X^k`" |
| `T4.cap_of_chk` | the brief's bridge: `capChk4 → ¬DZeta → ¬DZ → truthCap` |
| `T4.card_dZeta`, `card_dZ` | the two `hsingle` rows: ≤ 870 and ≤ 1,535 answers |

`attack_neg` (PACK §11.5, PB-m12) is not built here: PB-m12 places it as a V-run control (A2″ ran it
as a KAT, `logs/A2pp/dump/capkat.txt`); at the log level the attack's choice after `ζ` is not
expressible, and `dZeta_ctl`/`dZeta_inst` carry the doom-level counterpart.

## R2.6 Build and kernel times

- Builds (16G scope, `logs/A3b/`): `build-0-baseline.log` (HEAD: red in `TailD`, `R4Run`),
  `build-3.log`, `build-4.log` (green, 2,588 jobs), `build-5.log` (green with the control, 2,589 jobs).
- Sequential profiles (one core, `-DElab.async=false --profile`; `logs/A3b/profile-<m>.log`,
  `profile-summary.txt`). Wall includes ≈ 6 s of import loading per module.

| Module | wall | type checking | tactics |
|---|---|---|---|
| `TailStep` | 18.0 s | 5.6 s | 1.8 s |
| `TailCap` (new) | 13.6 s | 0.9 s | 1.8 s |
| `TailD` | 20.9 s | 11.8 s | 1.0 s |
| `TailM` | 10.2 s | 1.5 s | 0.9 s |
| `TailC` | 27.4 s | 17.0 s | 1.9 s |
| `TailLig` | 14.5 s | 2.3 s | 2.8 s |
| `CapCtrl` (new) | 9.8 s | 0.8 s | 1.2 s |
| `R4Run` | 12.0 s | 3.2 s | 0.5 s |
| `R4At` / `Acc` / `Ex` / `Fld` | 9.4 / 6.6 / 7.8 / 7.2 s | ≤ 0.5 s | ≤ 0.4 s |
| `R4FrE` | 11.6 s | 1.4 s | 1.6 s |
| `R4PosT` / `R4Qv` | 12.8 / 13.2 s | 0.7 / 0.2 s | 1.0 / 0.7 s |
| `R4Cols` | 12.6 s | 4.4 s | 1.0 s |
| `R4Cap` (new) | 30.2 s | 4.0 s | 6.3 s |
| `R4Tail` / `R4LinkP` / `R4P4` | 7.3 / 7.8 / 10.4 s | ≤ 0.8 s | ≤ 1.2 s |
| `R4PfRun` | 14.3 s | 1.1 s | 2.8 s |
| `P4aDF` / `XLaws` / `XRun` | 10.6 / 6.9 / 7.9 s | ≤ 1.3 s | ≤ 0.9 s |

- Sum ≈ 303 s wall over the 24 modules (≈ 144 s of it import loading). `TailD` is within one phase of
  its 18 CPU-s (lake: 18 s at HEAD's failing build → 16 s now). The two new proof modules add ≈ 44 s
  wall (≈ 32 s net of loading); the 600 s certificate budget must be re-measured on the runner with
  the other tracks' changes (B2′'s templates move `capChkOps`).

## R2.7 Checks

- Axioms (`logs/A3b/Axioms.lean`, `axioms.log`): 41 theorems, among them `certified`,
  `certificate_sub4`, `ks_rev4H` (both), `ks_rev4GR`, `cap_of_chk`, the counts, the controls,
  `capChk_run`, `capChk4_of_fields`, every red declaration: `propext`, `Classical.choice`,
  `Quot.sound` or fewer. No `sorry` in the worktree's modules of this track.
- Source rule (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`,
  `logs/A3b/source-rule.log`): 377 files, 0 findings (the worktree, other tracks' WIP included).

## R2.8 Deviations

1. **`RejG` and `PhaseObl.hrej`** (§R2.1): beyond PB-M1; without them the end of an accepted chain
   with `D` false is not refutable. No ε change.
2. **`D_ζ`/`D_z` are escape sets** (`DZeta`, `DZ`), as PB-M1 asks; the dooms are `DCapD … DCapZ`.
   "Σ ≠ 0" is `¬capSig0` ((I) at the honest weights, both F halves).
3. **The cap check is appended as a 13th final field** (`capF`) for the run's bookkeeping
   (`accept_chain4` over `opsOfFields`), not as an extra suffix: the three field lemmas keep their
   statements.
4. **Phase numbers 51–55 stay literal** in `DT`/`phOf_ge`; positions are `phStart4 k` throughout.
   A later phase would move `capPh_pos`, `phOf_check`'s 486, `cap_items` and the literals 486 in
   `R4Run`/`R4At`/`R4Tail` (`fsMsgs4_len`, `SkRun4`, `runLog_chain4`, `acceptTail4_of_finLog`).
5. **`attack_neg` not built** (§R2.5).

## R2.9 Open questions

1. `X4.GoodX` now carries `RejG`: the open residual `hL` (node links, `Open4`) is stated over the new
   potential's good logs. Does the orchestrator accept this as the residual's new form?
2. **Concurrent tracks in this worktree.** RSV-V and B2′ edit V-side modules here (`FRShape4`,
   `FRVIRFinals4`, `FRVIR4At`, `FRVIR4Uni`, `FRVIRCompile`, `FRX4*`, `FRNode*`, …; uncommitted). This
   run builds HEAD's V (only this track's modules are linked into `logs/fr-build-A3b`). In particular
   B2′'s templates rewrite `capChkOps`: `FRSoundness4R4Cap` (the families and `capChk_run`) proves
   HEAD's form and must follow; `reloc_capChk`, `capChk4_of_fields` and the T4 side do not depend on
   the op layout.
3. The certificate's 600 s budget: re-measure after the merge with B2′/RSV-V.
