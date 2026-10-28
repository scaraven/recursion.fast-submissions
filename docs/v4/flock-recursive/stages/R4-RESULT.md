# R4 RESULT (pass 1): the reference semantics of `gen4`, the chain, `accept_chain4`, F1; handover

- **Base.** HEAD `4841734` at start, re-snapshotted to `087f416` (T4, S-E13 committed) at the
  coordinator's request. **Build tree** `logs/fr-build-R4` (copy of `fr-build-SG13`; `b.sh` =
  `snap.sh` + capped build; `MINE.txt` lists the seven new modules). Logs in `logs/R4/`. Journal:
  `R4-JOURNAL.md` (§0 is the plan, written before the proofs).
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under
  `timeout`. No sub-agents. Nothing committed. No existing module edited, no statement changed.
  All names are in the new namespace **`FR.Snd.R4`**; every top-level short name was checked
  against all `FR*.lean` (one clash, `fsOf_length`, removed in favour of 3.x's).

## Status

| Item | State |
|---|---|
| 1. `accept_chain4` | **Done**, one level lower than planned: there was no reference semantics for `gen4` at all, so this pass built it (`refPhase4` … `exec_skeleton4`), the Fiat–Shamir chain (`fsQ_gen4`, `runLog_chain4`), then `accept_chain4`. |
| 2. Views | **Started**: the backbone (`phase_at4`, `skeleton4_outs`, `SkRun4`, `skRun4_of_accept`) and the squeeze views (`coords_view4`, `one_view4`). Rounds (deg 2/3, `.zero`), Z2's univariate, claim0/claimN by name: not started (§5). |
| 3. F1, the statement offset | **Done, no gap**: `stmtOff4`, `lastN_eq`, `lastN_of_le`, `segView_lastN`. |
| 4. Front checks | Not started (§5). |
| 5. `finLog4`/`AcceptTail` | T4 is committed: the target is `FR.Snd.T4.AcceptTail RejF W₀ c₀ L j`. Its `chain` and `len` fields come from `runLog_chain4` now; the rest is named in §5. |

**Checks.**
- `lake build FR FRSoundness4R4Ctrl`: green, 2,457 jobs (`logs/R4/build-final.log`).
- **Axioms** (`logs/R4/axioms.log`, all 76 theorems of the seven modules): within `propext`,
  `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`):
  237 files, 0 findings (`logs/R4/source-rule.log`).

**Imports for `FR.lean`:** `import FRSoundness4R4Ctrl` (it pulls `FRSoundness4R4View`, `…At`,
`…Run`, `…Chain`, `…Ref`, `…Stmt`).

## 1. What was built (`loc.py`, `logs/R4/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4R4Stmt` | 72 / 35 / 7 | **F1**: `stmtOff4`, `dByte_bytesAt`, **`lastN_eq`**, `lastN_of_le`, **`segView_lastN`**; controls `lastN_wrap`, `lastN_five` |
| `FRSoundness4R4Ref` | 533 / 454 / 19 | generic: **`exec_ok_and`**, `ask_outs`, `vals_item`, **`exec_ext`**; `seedTail4`, `absTail4`, `segPtRegs`, **`refPhase4`**, `exec_abs4`, `exec_tail`, `genPhase4_absorb`, **`exec_genPhase4`**, `genPhase4_next`, **`genPhase4_ctx`**, `refPhases4`, `StartOk4`, `exec_genPhases4`, `genPhases4_next`, `startOk4`, **`exec_skeleton4`**, `skeleton4_next` |
| `FRSoundness4R4Chain` | 290 / 236 / 8 | `phaseMsgs4`, `msgsFrom4`, **`fsMsgs4`**, `shOK4`, `isSeed4`, `itemsL_allFS`, `pureRun_base`, **`refPhase4_chain`**, `refPhases4_chain`, `ctx0`, `skeleton4_chain`, **`fsQ_gen4`**, `shOK_seq4` |
| `FRSoundness4R4Run` | 228 / 172 / 16 | certificates `fsMsgs4_len`/`_items`/`_fit`; `fsCheck_qOf`, `stateIn_qOf`, **`matches_fsQ4`**, **`runLog_chain4`**; `relocF`, `relocFin`, `relocFin_ops`, **`finOps4_eq`**, `noAsk_relocFin`; **`accept_chain4`** |
| `FRSoundness4R4At` | 209 / 157 / 13 | `psItems4`, **`refPhases4_at`**, `cAt4`, `phStart4_eq_sum`, **`phase_at4`**, `genPhase4_outs`, `genPhases4_outs`, **`skeleton4_outs`**; **`SkRun4`**, **`skRun4_of_accept`** |
| `FRSoundness4R4View` | 101 / 77 / 4 | `rd_phase4`, `sqz_entries4`, **`coords_view4`**, **`one_view4`** |
| `FRSoundness4R4Ctrl` | 43 / 20 / 7 | the controls (§4) |
| **total** | 1,476 / 1,151 / 74 | |

## 2. The main statements

```lean
-- F1: the segment program and V_A read the same n
theorem stmtOff4 : fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt = 48
theorem lastN_eq (π : ByteArray) : idxOfF 24 (digestAt π (48 + 33)) 0 = rdLE64 π 81 % 2 ^ 24
theorem segView_lastN (hv : segView π = some v) (hcap : v.n ≤ v.kind.cap) :
    idxOfF 24 (digestAt π (fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt + 33)) 0 = v.n

-- generic run facts (any op list)
theorem exec_ext : exec impl κ inp ops ⟨r, ok⟩ tr = some (s, tr') →
    ∃ L, s.regs = r ++ L.toArray ∧ L.length = opsOut ops ∧
      ∃ seg, tr = seg ++ tr' ∧ seg.length = (ops.filterMap Op.item?).length

-- gen4's skeleton is its reference
theorem exec_skeleton4 (ok ops tr) :
    exec impl κ inp ((skeleton4 S p).1 ++ ops) ⟨#[], ok⟩ tr =
      (refPhases4 impl κ inp S p (phasesOf S) 0 ⟨0, 0, 0, [], [], 0, #[]⟩ #[] tr).bind fun y =>
        exec impl κ inp ops ⟨#[] ++ y.1.toArray, ok && y.2.1.all id⟩ y.2.2

-- the Fiat–Shamir chain, and the log's chain
theorem fsQ_gen4 (hS : ((phasesOf S).drop 1).all (fun ph => shOK4 ph.2 && !isSeed4 ph.2) = true)
    (fin : FinOps) (h : semIR impl (gen4 S p fin) inp es = some b) :
    (fsOf es (itemsOf S)).length = (fsMsgs4 S).length ∧ ∀ q < (fsMsgs4 S).length,
      ((fsOf es (itemsOf S)).getD q default).1 =
        qOf inp q ((fsMsgs4 S).getD q none) ((fsOf es (itemsOf S)).getD (q - 1) default).2
theorem runLog_chain4 (impl p fin) (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 p fin) inp).runLog L = some true) :
    ∃ tr, semIR impl (gen4 seq4 p fin) inp tr = some true ∧ (∀ e ∈ tr, e ∈ L) ∧
      ∃ j, G.IsChain L j ∧ entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4) ∧
        (entriesOf L (pathOf L j)).length = 482

-- the finals
theorem finOps4_eq (P : FinP) : finOps4 P = (relocFin P.S (finalsOf P)).ops
theorem accept_chain4 (fin : Finals) (hna : …) (h : semIR impl (gen4 S p fin.ops) inp tr = some true) :
    ∃ y, refPhases4 impl p.tix inp S p (phasesOf S) 0 ctx0 #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      (skeleton4 S p).2.next = (#[] ++ y.1.toArray).size ∧
      ∃ L₀, pureRun … (fin.finRS ⟨outs, [], #[]⟩ next).1 (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
        ∃ Rs, Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray ∧ ∀ k hk, ∃ L,
          pureRun … ((fin.rest[k]) ⟨outs, zhat, exAt …⟩ (Rs k).size).1 (Rs k) [] = some (L, true) ∧
          Rs (k + 1) = Rs k ++ L.toArray
-- At the concrete programs: `rw [finOps4_eq] at h`, then `accept_chain4 … (relocFin P.S (finalsOf P))
-- (noAsk_relocFin P.S (noAsk_finalsOf P)) h`.

-- views
theorem coords_view4 (h : SkRun4 impl p inp tr y) (hn) (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = (b + 3 * k) :: (List.range (2 * k)).map (fun x => b + 3 * (x / 2) + 1 + x % 2) ∧
      b + 3 * k + 1 ≤ (#[] ++ y.1.toArray).size ∧
      ∀ x < 2 * k, rd (#[] ++ y.1.toArray) (b + 3 * (x / 2) + 1 + x % 2) =
        .f (chF (ansAt (fsOf tr (itemsOf seq4)) (phStart4 n + x / 2)) (x % 2))
theorem one_view4 (h : SkRun4 impl p inp tr y) (hn) (hsh : (phasesOf seq4)[n].2 = .squeezes 1 .one) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = [b] ∧ b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) b = .f (fAt (fsOf tr (itemsOf seq4)) (phStart4 n) 0)
```

## 3. Design and deviations

- **D1. The reference semantics was missing, so item 1 started below `accept_chain`.** 3.x's
  `refPhase`/`exec_skeleton` and `fsQ_gen` are stated over 3.x's `Phase` table and `genPhase`;
  nothing related `exec` of `gen4` to anything. `gen4` addresses π absolutely (`piField 0 o`,
  `absOff 0 o = o`), so 3.x's exec lemmas for squeezes, the univariate round and the rounds
  (`exec_sqzC`, `exec_sqzOps`, `exec_uni`, `exec_roundsT'`) and their chain lemmas (`sqzT_chain`,
  `roundsT_chain`, `qOf`, which already takes absolute `(o, len)`) apply at field `0`. These were
  reused, not copied.
- **D2. A query phase's reference is its own `exec`.** The front never reads a query phase's
  values, and the chain needs only that a query phase consumes column/node entries and keeps `st`.
  The generic `exec_ext` gives both, so 3.x's Merkle reference (`stepT`/`posT`/`posAllT`,
  ≈ 250 lines) was not ported. If a later item needs a level's column values (`truthP3 … 4` in
  `AcceptTail.lvl4`), port `posT` then for `posOps4`/`merkleOps4` (their `act` is a constant `h < sib`).
- **D3. The seed and the absorbs' checks are `pureRun`s** of their ask-free tails (`seedTail4`,
  `absTail4`: `stmtOps4`, a segment's `lastOps`, `finalOps4`, the end-zero check). P4a's
  `run_lastOps` then gives the segment's `L` bits directly.
- **D4. The finals are a `Finals` with relocated fields** (`relocFin`), not a new field kit:
  `finOps4_eq` makes 3.x's generic `fields_chain`/`fields_ok`/`field_flag` apply unchanged.
  `accept_chain4` is therefore stated for any `fin : Finals` asking nothing.
- **D5. `SkRun4` carries `qOf … (fsMsgs4 seq4)`** (the program's queries) in place of 3.x's
  `X.fsQ` (the extractor's). Linking `fsMsgs4` to S-H3's Rev4 extractor, if it has an `fsQ4`, is a
  one-certificate step (both are tables over `phasesOf seq4`).
- **F1 (P4a's): no gap.** `stmt` sits at offset 48 (`stmtOff4`), so `lastOps` reads
  `digestAt π 81`; its index is `rdLE64 π 81 mod 2^24` (`lastN_eq`); on `V_A`'s range
  `n ≤ cap ≤ 2^18` they are equal (`segView_lastN`). P4a's `lastL_eq` needs `nStmt es = v.n`; with
  `segView_lastN` and the stmt message on the log being π's bytes 48–175 (the stmt absorb's message,
  `refPhase4_chain`'s `qOf` at position 1, message `(48, 128)`: `fsMsgs4_ctl`) this is a short
  lemma for X4.
- **F2. Kernel time.** `FRSoundness4R4Chain` type-checks in 34.3 s sequential (one declaration,
  33.9 s; the `shOK_seq4` certificate alone is 18 ms, so it is in `refPhase4_chain`'s proof term:
  most likely a `rfl` that makes the kernel unfold a `genPhase4` match, S-E13's trap). With the
  certificate budget over its cap (H-cert), **localise and fix this first** in the golf pass (split
  the cases into lemmas, rewrite `genPhase4` only by equations). `FRSoundness4R4Run`'s 12.6 s are the
  three `fsMsgs4` certificates over the 482-entry table.
- No value asserted by no final was met in this scope (the pass did not reach the finals' flags).

## 4. Controls (`FRSoundness4R4Ctrl`, `FRSoundness4R4Stmt`, `FRSoundness4R4At`)

| Definition | Positive | Negative |
|---|---|---|
| `refPhase4` | `refPhase4_sqz0` (an empty squeeze run passes, consuming nothing) | `refPhase4_seed_nil` (a seed with no entry fails), `refPhase4_abs_wrong` (an absorb answered for another query fails) |
| `fsMsgs4` | `fsMsgs4_len`, `fsMsgs4_items`, `fsMsgs4_ctl` (message 1 is `stmt` at 48, 128 bytes) | `fsMsgs4_ctl` (message 3, in Z1, is a squeeze) |
| `relocFin` | `relocFin_ops`, `finOps4_eq` | `relocF_moves` (relocation to `seq4` moves `E`) |
| `SkRun4` | `skRun4_of_accept` | `not_skRun4_nil` |
| `cAt4` | `cAt4_ctl` (`cAt4 0 = ctx0`; after the seed `next = 4`) | `cAt4_ctl` (`next ≠ 0`) |
| `exec_ext` | the lemma | `exec_ask_nil` (an ask on an empty trace fails) |
| F1 | `lastN_five` | `lastN_wrap` (`n = 2^24` reads `0`: the range hypothesis is needed) |

## 5. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `logs/R4/prof-*.log`)

| Module | wall (import ≈ 4 s) | type checking | max RSS |
|---|---|---|---|
| `FRSoundness4R4Stmt` | 7.0 s | 0.13 s | 2.8 GB |
| `FRSoundness4R4Ref` | 19.3 s | < 0.2 s per declaration | 2.9 GB |
| `FRSoundness4R4Chain` | 43.9 s | **34.3 s** (F2) | 6.0 GB |
| `FRSoundness4R4Run` | 20.1 s | 12.6 s (the three `fsMsgs4` certificates) | 4.3 GB |
| `FRSoundness4R4At` | 9.0 s | < 0.2 s | 3.0 GB |
| `FRSoundness4R4View` | 7.2 s | 0.25 s | 3.0 GB |
| `FRSoundness4R4Ctrl` | 6.1 s | 0.03 s | 2.9 GB |

`decide` uses: position/table certificates only (`stmtOff4`, `shOK_seq4`, `shOK_all_seq4`,
`fsMsgs4_len`/`_items`/`_fit`, `fsMsgs4_ctl`, `κ.cap ≤ 2^18`), all `decide +kernel` over `seq4`'s
phase table, as S-G13's. None runs over a program, a register file or a `trueSum`.

## 6. Handover: the remaining items, in order

0. **F2 first** (golf): find the 33.9 s declaration in `FRSoundness4R4Chain` (bisect
   `refPhase4_chain`'s cases into separate lemmas) and remove the kernel unfolding.
1. **The remaining views** (`FRSoundness4R4View`, template 3.x `FrRndV`/`FrRnd`/`AccVal`/`FrLc`):
   - `genPhase4_rounds`: `outs[n] = cl :: rs ++ [last]` for `.rounds f k deg false`, with
     `b' = next + width`, `rs[j] = b' + w j + 3`;
   - `roundsF2_view4` (degree 2, `Chk2` holds for real rounds, the last register is `clR2 … k`),
     `roundsF3_view4` (degree 3, `clR … k`), for the real count `realRounds p name k` (dummies keep
     the claim and their message is zero: `roundsT`'s flag), and the `.zero` init (`Lr2`, `E2`);
   - `uni_view4` (Z2): node `outs = [b+3, b+133, b+134]`, segment `[b+4, b+134, b+135]` with the
     packed `segPtRegs` operand at `b` (its value: Z1's coordinates, zero-padded, then `lastOuts`'
     `L` bits — use P4a's `run_lastOps`/`lastVals_bit` through the stmt phase's `pureRun` (D3));
   - claim0/claimN by name: `phaseIx` over `phasesOf seq4` (a certificate, as `phaseIx_vals`).
2. **The finals' flags at `FinP`** (needed by every front check): `flag_gFinZ`, `flag_gFinLc`,
   `flag_gFinSh`, `flag_gFinLr`, `flag_gFinE`, `exec_gFinRS`, `flag_gFinB'` on relocated ops
   (`pureRun` of `(… ).map (reloc P.S)`; `evalOp (reloc S op)` reads `absOff 0 (fieldOffOf S f + o)`).
   3.x's `flag_fin*` proofs are the template; the sizes (`P.S.z3`, `P.lrR`, …) stay symbolic.
3. **The front checks**, one per name, each as `¬ Rej L (entriesOf L (pathOf L j))` on the chain of
   `runLog_chain4`, for every kind (`p = .ofSeg κ` / `.ofNode ν`, `P = segFinP κ`/`nodeFinP ν cells`):
   `P4a.RejZ (zlm4 indN etN)` (Z3 rounds view + `relZ`; `c0Z`'s `peL` needs the segment's
   `targetSSeg` spec, `implSegC_meets`), `P4a.RejL2` (L2 rounds view), `P4a.RejLc2`/`RejLcN` (3.x's
   `lc_ii_run` on `gFinLc`), `P4a.RejS2` (S2 rounds view), `P4b.RejEndLr4`/`RejEndE4` (`gFinLr`/`gFinE`
   (ii) after `lrR`/`e2R` real rounds), `RejInE4` (E4's real rounds), `RejFinE4 srcE srcL` (`gFinE` (iv),
   `mle_wEb4`), `RejRS4 (okRS4 oZ oLc oSh)` (`gFinRS`'s slices). Node matrices stay parameters.
4. **`AcceptTail` (T4)**: `chain`, `len` from `runLog_chain4` (482 = `pfStart + 14`); `rejF` from
   item 3; `p1`/`pf` from K-rounds views of P1.i/Pf (`inK = true`, free init); `lvl4` needs level 4's
   column values (port `posT` for `posOps4`, D2) and `flag_gFinP 4`; `fin` from `flag_gFinPf`.

## 7. Open questions

1. Is a Rev4 `X.fsQ4` (S-H3) planned? If so, `SkRun4.hq` should be restated against it with one
   certificate (`fsMsgs4 seq4` = its table) so the extractor and the program share one chain (D5).
2. The proof-size hypothesis `inp.π.size = piSizeOf seq4` of `runLog_chain4`: which check
   discharges it at revision 4.1 (`V4with`'s dispatch, or `acc`)? 3.x took `π.size = piSize` the same
   way.
3. Unused-`simp`-argument linter warnings remain in `FRSoundness4R4Ref` (harmless; for the golf pass).

## Pass 2 (track R4b; HEAD `ed98f9e`)

- **Build tree** `logs/fr-build-R4b` (a copy of `fr-build-R4`; `b.sh` logs to `logs/R4b/`; `MINE.txt`
  adds `FRSoundness4R4Rnd`, `FRSoundness4R4Link`). Re-snapshotted from HEAD after P4c's commit.
  Every lean/lake command ran in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. Only R4's modules edited, two new `FRSoundness4R4*` modules (every
  new short name grepped first). No statement of another track changed.
- **Checks.** `lake build FR FRSoundness4R4Ctrl FRSoundness4R4Rnd FRSoundness4R4Link`: green, 2,468
  jobs (`logs/R4b/build-final.log`). Axioms (`logs/R4b/axioms.log`, all 117 theorems of the nine
  modules): within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. Source rule: 257
  files, 0 findings (`logs/R4b/source-rule.log`).
- **Imports for `FR.lean`:** add `import FRSoundness4R4Rnd` and `import FRSoundness4R4Link` (next
  to R4's `import FRSoundness4R4Ctrl`).

### Item 0: kernel cost (done)

| Module | type checking before | after | cause, fix |
|---|---|---|---|
| `FRSoundness4R4Chain` | 34.3 s | **0.49 s** | Not `refPhase4_chain` (0.1 s): `fsQ_gen4`'s zero case, `∃ ms, fsMsgs4 S = some (0, 48) :: ms := ⟨_, rfl⟩` (bisected with `#exit`-style prefixes, then `sorry` variants: 33.6 s on that term alone). Now `phasesOf S = ("seed", .seed) :: ps := ⟨_, rfl⟩` and `simp only [fsMsgs4, hps, msgsFrom4, phaseMsgs4, …, qOf]`. |
| `FRSoundness4R4Run` | 12.6 s | **2.93 s** | `fsMsgs4_items` (11.3 s) indexed the 482-entry table with `getD q` under `List.range 482` (quadratic). Restated as the linear `.seed :: (fsMsgs4 seq4).tail.map (X.msgItem 1) = fsItems4` (2.05 s; `X.msgItem` reads only `q = 0`, `msgItem_succ`); `fsItems4_getElem` unchanged in statement. `fsMsgs4_head` is now proved for every `S` without evaluating the table (0.40 s → 0). |

Per-declaration figures: `lean -DElab.async=false -Dtrace.profiler=true -Dtrace.profiler.threshold=300`
(the `[Kernel]` lines name the declaration). Remaining: `fsMsgs4_items` 2.05 s, `fsMsgs4_fit` 0.59 s.

### Coordinator's item (P4c's F2): a segment's `finSh` has no link weight — confirmed

`FRSoundness4R4Link`:
- `linkWAll_segC`/`linkWAll_segS` (`rfl`): on the segment program the kind index is
  `(KindP.ofSeg σ).tix = .L32` (not a node), and `implSeg (implC …)` and `specSeg (specC …)` both
  answer `Array.replicate nLinkFam 0`; `linkWAll_seg_of_meets`: so does every implementation meeting
  `specSeg (specC …)` (`Meets`' 14th clause is unconditional).
- `linkSum_zero`: `linkSum 0^8 κ_s n acc pow = acc` (`relSh`'s link term vanishes).
- **`run_linkOps_zero`** (the program): if register `b + 25` holds `.af 0^8` (and `b + 22`,
  `b + 26`, `ks` hold F values, `|r| = b + 27`), `linkOps ks b` passes, appends 32 registers, and
  register `b + 57` (the `addF (b + 16) (b + 57)` operand) holds register `b + 22`'s value. Through
  `pureRun_linkFam` (one family appends `0, 0, acc, pow·κ_s`) and `pureRun_linkFams` (induction).
- Controls: `linkSum_ctl` (−: `W₀ = 1` moves the accumulator), `linkWAll_nodeC` (+: a node's is
  `linkWAllI`).
- So P4c's `wSumSeg` (no link term) is the program's value; the `gFinSh` flag lemma at `FinP`
  (item 2 below) will meet `linkOps` with `b + 25 = linkWAll …` and close it with
  `run_linkOps_zero`.

### Item 1: the remaining views (done) — `FRSoundness4R4Rnd`

No message table is needed: a round's query is `absorbQ d msg`, so the log's `msgAt` is the
program's message (`msgAt_of_q`, `readF_piMsg`).
- **Trace level**: `roundsT_dummy` (dummy rounds keep the claim), **`rounds3_log`** (degree 3: the
  claim after `n` rounds from round `j ≤ real` is `clR P c₀ … (min real (j + n))`), **`rounds2_log`**
  (degree 2: `clR2 P 16 readF (chF · 0) …`, and on a passing run every real round's `Chk2 P …`),
  `round_entries`, `shift_entries`, `roundsT_first`.
- **Phase level**: `rounds_at4` (a rounds phase of an accepted run: `roundsT` with
  `realRounds p name k` real rounds from `clVal`, its `2k` entries are the log's from `phStart4 n`),
  `genPhase4_rounds` (`outs[n] = clReg … :: rs ++ [last]`, every init), **`rounds_core4`**.
- **Views** (any init: `.free`, `.zero` (Lr2, E2), `.uni` (Z3)): **`roundsF3_view4`** (Z3, Lr2,
  E2) and **`roundsF2_view4`** (L2, S2, E4): `outs[n]`'s head holds `clVal …` (the claim the rounds
  start from); `getD (j + 1)` holds `rch P es j`; the last register holds
  `clR/clR2 P (fun _ _ => c) L es (min (realRounds p name k) k)` once the head holds `.f c`; degree
  2 adds `∀ l < min real k, Chk2 P … (fun _ _ => c) L es l`. Real counts are the program's
  (`realRounds_vals`: `p.d.seq.z3/s2/lr/e2/e4`, L2's 14).
- **`uni_view4`** (Z2, node and segment): with `s = 0`/`1`, `outs[n] = [b+s+3, b+s+133, b+s+134]`;
  `λ = fAt es (P+1) 0`; the two `lagrangeS` values on `uniEs` at `λ` with `targetS κ pe`; the
  message's 127 coefficients are the log's (`readF (msgAt es P) (16 i)`); a node's `pe` is the `pt`
  register's array; **a segment's `pe` is the packed operand in register `b`**, equal to the
  `segPtRegs` registers' values once those precede the phase (`hpt`).
- **By name**: `phases4_rounds` (indices 4, 5, 8, 12, 14, 18, 21 of `phasesOf S`, structural, any
  `S`), `phaseIx4_rounds` (3.x's `phaseIx` gives the same numbers: from `phaseIx_vals`),
  `initClaim_vals`, **`outsOf_skel`** (`outsOf`/`claim0`/`claimN` of a `FinIn` with
  `fi.outs = (skeleton4 seq4 p).2.outs` are the views' head/last), `chals_getD`.
- Controls: `clReg_ctl`, `clVal_ctl` (+/−), `roundsT_zero_ctl`.

### R4's open questions

1. **`inp.π.size = piSizeOf seq4`** — answered, two lemmas in `FRSoundness4R4Link`:
   `piSize_node4 : kindOf4 π = .node ν → π.size = piSizeOf seq4` (`kindOf4` returns `.node` only at
   that size; S-H3's `kindOf4_node` gives the literal `798192`), and `piSize_aggSegs : π.size = 48 +
   k · segSize → ∀ s ∈ aggSegs segSize k π, s.size = segSize` (`VAwith (piSizeOf seq4)` checks the
   size before running `Vseg` on `aggSegs`).
2. **`X.fsQ4`**: S-H3 has **none**. `FRX4Prog`/`FRX4Ext` keep the node's chain links as the
   parameter `NodeDec4.Links` (its doc names 3.x's `fsQ` "at seq4's positions"). When X4
   instantiates `Links`, the table is `fsMsgs4 seq4` (`qOf inp q (fsMsgs4 seq4)[q]`, as `SkRun4.hq`);
   no second chain exists to equate.

### Times (sequential, `logs/R4b/prof-*.log`)

| Module | wall | type checking | max RSS |
|---|---|---|---|
| `FRSoundness4R4Chain` | 15.5 s | **0.49 s** (was 34.3 s) | 2.9 GB |
| `FRSoundness4R4Run` | 10.7 s | **2.93 s** (was 12.6 s) | 3.2 GB |
| `FRSoundness4R4Rnd` (new) | 15.8 s | 1.41 s | 3.0 GB |
| `FRSoundness4R4Link` (new) | 13.1 s | 0.48 s | 2.8 GB |

Net kernel change for the certificate: −43.5 s + 1.9 s. Elaboration trap met: `phases4_rounds`
with `.uni`/`.rounds` dot constructors in `some (…)` took 11.4 s in the header; `Sh.uni`/`Sh.rounds`
fixed it (< 0.2 s).

`loc.py` (`logs/R4b/loc.txt`): `FRSoundness4R4Rnd` 579 / 477 / 27, `FRSoundness4R4Link`
176 / 120 / 15; R4 total now 2,243 / 1,756 / 117.

### Handover (remaining items, in order)

2. **The finals' flags at `FinP` on the relocated ops.** For each field `gFin*` of `finalsOf P`,
   a `flag_*` lemma `∃ L, pureRun impl κ inp ((gFin* P fi b).1.map (reloc P.S)) r [] = some (L, rel*)`
   with `rel*` the 3.x relation (`relZ`, `relLc`, `relSh`, `relLr`, `relE`, `relRS`, `relB'`) at
   `P`'s sizes; `evalOp (reloc S op)` reads `absOff 0 (fieldOffOf S f + o)` (prove one
   `evalOp_reloc` for general `S`, as `evalOp_reloc_seq3`). Template: 3.x's `flag_finSh`
   (`FRVIRFinals`, one `simp only` over the ops) and its siblings; `finalsOf_seq3` relates the
   fields at `fin3P`. For `gFinSh` with `P.vn` (segment), meet `linkOps` with `run_linkOps_zero`.
3. **The front checks** on `runLog_chain4`'s chain, per kind (`.ofSeg σ`/`.ofNode ν`), each from
   `accept_chain4` (finals as `relocFin P.S (finalsOf P)`, `finOps4_eq`), item 2's flags, and this
   pass's views: `P4a.RejZ` (`roundsF3_view4` at Z3 (n = 5) + `relZ`; the init is `.uni`: Z2's
   register `b+s+133` from `uni_view4`; `c0Z`'s `peL` reads the segment's `targetSSeg`, so needs
   `implSegC_meets` and the `segPtRegs` bound `hpt`, i.e. "outs of earlier phases < next", not yet
   proved for `gen4`), `RejL2` (`roundsF2_view4` at n = 8), `RejLc2`/`RejLcN` (`gFinLc`, 3.x's
   `lc_ii_run` path), `RejS2` (`roundsF2_view4` at n = 12; `Chk2 … c0SL` from the head's value
   `= c0S es` by `gFinSh` (i)), `P4b.RejEndLr4`/`RejEndE4` (`roundsF3_view4` at 14/18, init
   `.zero`), `RejInE4` (`roundsF2_view4` at 21), `RejFinE4 srcE srcL` (`gFinE` (iv)),
   `RejRS4 (okRS4 oZ oLc oSh)` (`gFinRS`). Two links are still needed for every check: (a) **the
   program's kind is the chain's**: `kindOfC es` (byte 71 of the log) against `p` (so `mC 6
   (kindOfC es) = p.d.seq.z3`, `nrS = p.d.seq.s2`, `ncR ν = p.d.seq.e4` …); (b) `min (realRounds …)
   k = realRounds …` (`seg_fits`/node dims ≤ `seq4`).
4. **`AcceptTail` (T4)**: `chain`, `len` from `runLog_chain4` (482 ≥ `pfStart + 14`); `rejF` from
   item 3; `p1`/`pf` need K-round views (`inK = true`; this pass did F only: port 3.x's
   `rounds_view` to `rounds_at4`'s form, `roundKVals`); `lvl4` needs level 4's column values
   (port `posT` for `posOps4`, R4's D2) and `flag_gFinP 4`; `fin` from `flag_gFinPf`.
