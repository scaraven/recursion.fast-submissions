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

## Pass 3 (track R4c; HEAD `4919027`, re-snapshotted to `94ee843`)

- **Build tree** `logs/fr-build-R4c` (a copy of `fr-build-R4b`; `b.sh`/logs to `logs/R4c/`;
  `MINE.txt` adds the eight new modules). Every lean/lake command ran in the 16G scope (12G for single
  files) under `timeout`. No sub-agents. Nothing committed. Only R4's modules and new
  `FRSoundness4R4*` modules written; every new short name grepped first (`relZ4`, `pe4`, `sv4`,
  `OutsLt`, … are new). No statement of another track changed; `FRVIRFinals*` untouched (G1).
- **Imports for `FR.lean`:** add `import FRSoundness4R4Acc` (it pulls `FRSoundness4R4FinCtrl`,
  `…Fin`, `…FinSh`, `…FinLc`, `…FinRS`, `…Outs`, `…Kind`), next to R4/R4b's imports.

### Status

| Item | State |
|---|---|
| 2. Finals' flags at `FinP` | **Done** for every field the front reads: `flag_gFinZ`, `flag_gFinLc`, `flag_gFinSh`, `flag_gFinLr`, `flag_gFinE`, `exec_gFinRS`, `flag_gFinB'` (all on `(gFin* P fi r.size).1.map (reloc P.S)`, any `P`, any kind index). `gFinP`/`gFinPf` (item 4's) not started. |
| Missing fact: the kind | **Done**: `kindOfC_seg4`, `kindOfC_node4` (from the seed's check), `dims_seg4`, `dims_node4`. |
| Missing fact: outs before `next` | **Done**: `segPt_lt` (`uni_view4`'s `hpt`), `skeleton4_out_lt`, `cAt4_outsLt`. |
| 3. Front checks | **Started**: the run bridge `fields_of_accept4` and its template `relLr4_of_accept` (the relation holds on an accepted run, on a file extending the skeleton's). No `¬ Rej*` closed yet. |
| 4. `AcceptTail` | Not started. |

**Final checks** (HEAD `94ee843` re-snapshotted, R4's 17 modules overlaid):
- `lake build FR` + the 17 R4 modules: **green, 2,494 jobs** (`logs/R4c/build-final.log`).
- **Axioms** (`logs/R4c/axioms.log`, all 188 theorems of the 17 modules): within `propext`,
  `Classical.choice`, `Quot.sound` (10 use none); no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 274
  files, 0 findings (`logs/R4c/source-rule.log`).
- **Times** (sequential, one core: `taskset -c 0 lake env lean -DElab.async=false --profile`;
  `logs/R4c/prof-*.log`; import ≈ 4 s):

  | Module | wall | type checking | max RSS |
  |---|---|---|---|
  | `FRSoundness4R4Fin` | 14.4 s | 0.27 s | 2.9 GB |
  | `FRSoundness4R4FinSh` | 28.4 s | **3.68 s** (`flag_gFinSh`: four unrolled cases with 32 link ops each) | 3.1 GB |
  | `FRSoundness4R4FinLc` | 12.2 s | 0.56 s | 2.9 GB |
  | `FRSoundness4R4FinRS` | 15.7 s | 0.11 s | 2.9 GB |
  | `FRSoundness4R4Outs` | 45.7 s | 0.14 s (elaboration: `genPhase4_out_lt`'s simp; golf target) | 3.0 GB |
  | `FRSoundness4R4Kind` | 8.0 s | < 0.1 s | 3.0 GB |
  | `FRSoundness4R4FinCtrl` | 7.0 s | < 0.1 s | 3.0 GB |
  | `FRSoundness4R4Acc` | 7.2 s | < 0.1 s | 3.0 GB |

  Net kernel cost of the pass ≈ 4.9 s, 3.7 s of it `flag_gFinSh` (if the budget needs it: prove
  `relSh4`'s link part once through `run_linkOps_zero`-style family lemmas instead of unrolling, as 3.x
  could not). No `decide` over a program, a register file or a table in this pass (only
  `kind_zero_none` over the kind-byte decoder, and `dims_*` over three kinds).

### What was built (`loc.py`, `logs/R4c/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4R4Fin` | 251 / 196 / 11 | `pe4` (a read at `fieldOffOf S f + o`), **`evalOp_reloc`** (one lemma, every read form, general `S`), `reloc_piElem`/`_piField`/`_piDigest`, `evalOp_pi*0`; `relZ4` + **`flag_gFinZ`**, `relLr4`/`vLv4` + **`flag_gFinLr`** (exports `v_L`, Lr2's point), `relE4` + **`flag_gFinE`** (export `r′`), `pubH4`/`vStar4`/`relB4` + **`flag_gFinB'`** |
| `FRSoundness4R4FinSh` | 110 / 91 / 1 | `relSh4` (with `P.vn`: `τ ‖ L` operand, `E`/`Sh`/`E₀` from `shiftMask`, `bnd`'s last block `L`) + **`flag_gFinSh`** |
| `FRSoundness4R4FinLc` | 170 / 128 / 4 | `lcV4`, `lcRhi4`, `lcWalk4`, `lcVf4`, `lcFree4`, `relLc4` + **`flag_gFinLc`**; `dotOps_reloc`, `lcTail_reloc`, `lcFree4_leaf` |
| `FRSoundness4R4FinRS` | 333 / 287 / 5 | `sv4`, `rsLeafZero4`; `run_elemOps4`, `run_elemsOps4`, `run_claimOps4`, `run_rsTail4`; `rsW4`, `rsAlpha4`, `rsTv4`, `rsV4`, `relRS4`, `rsRefs4` + **`exec_gFinRS`** (flag `relRS4`, exports `α_j = rsAlpha4`, `v_RS = rsV4`) |
| `FRSoundness4R4Outs` | 253 / 201 / 26 | `opsOut_*` (absorb, `lastOps` 94, seed 4, squeezes, uni 136, rounds `w·n`, Merkle `6n`, position `posW4`); **`genPhase4_out_lt`**, `genPhases4_split`, `cAt4_succ`, `cAt4_next_mono`, `cAt4_size`, `cAt4_outs`, `OutsLt`, `genPhase4_outsLt`, **`cAt4_outsLt`**, **`segPt_lt`**, **`skeleton4_out_lt`** |
| `FRSoundness4R4Kind` | 106 / 78 / 7 | **`seed_byte4`**, `kindOfC_byte4`, **`kindOfC_seg4`**, **`kindOfC_node4`**, `dims_seg4`, `dims_node4` |
| `FRSoundness4R4FinCtrl` | 91 / 52 / 11 | the controls (below) |
| `FRSoundness4R4Acc` | 98 / 73 / 6 | **`fields_of_accept4`**, `skel_pos4`, `outsOf_lt4`, `hin_Lr`, **`relLr4_of_accept`** |
| **new total** | 1,412 / 1,106 / 71 | R4 total now 3,655 / 2,862 / 188 |

### Main statements

```lean
theorem evalOp_reloc (hf : f < 19) (o len k : ℕ) :
    evalOp impl κ inp regs (reloc S (.piField f o len)) = .vals [.b (inp.π.extract (fieldOffOf S f + o) (fieldOffOf S f + o + len))] true ∧
    evalOp impl κ inp regs (reloc S (.piElem f o)) = .vals [.f (pe4 S inp f o)] true ∧ … (piElemK, piDigest, piDigestAt)
theorem flag_gFinZ (hin : ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" P.S.z3 ++ [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinZ P fi r.size).1.map (reloc P.S)) r [] = some (L, relZ4 κ inp fi r P)
-- likewise flag_gFinLr (+ exports), flag_gFinE (+ export), flag_gFinB' (+ export), flag_gFinSh, flag_gFinLc,
-- exec_gFinRS (+ exports α_j, v_RS)
theorem segPt_lt (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) (h3 : 3 < n)
    (hn : n ≤ (phasesOf seq4).length) : ∀ x ∈ segPtRegs seq4 p (cAt4 seq4 p n).outs, x < (cAt4 seq4 p n).next
theorem skeleton4_out_lt (h : refPhases4 …) : ∀ m, ∀ x ∈ (skeleton4 seq4 p).2.outs.getD m [], x < (#[] ++ y.1.toArray).size
theorem kindOfC_seg4 (h : SkRun4 impl (.ofSeg σ) inp tr y) : kindOfC (fsOf tr (itemsOf seq4)) = .seg σ
theorem kindOfC_node4 (h : SkRun4 impl (.ofNode ν) inp tr y) : kindOfC (fsOf tr (itemsOf seq4)) = .node ν
theorem fields_of_accept4 (P : FinP) (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ zh Rs, (∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)) ∧
      ∀ k (hk : k < 12), ∃ ex L, pureRun impl p.tix inp (((finalsOf P).rest[k] ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true)
theorem relLr4_of_accept (P : FinP) (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ fi R, fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R ∧ relLr4 p.tix inp fi R P = true
```

### Design and deviations

- **D6. The relations are 3.x's, generalised, not reused verbatim.** 3.x's `relZ` … hard-code
  `Kind.m`, 3.x's sizes (Z3 26, Lr 15, …) and `pe` (3.x's field offsets); at `segFinP σ` the program's
  kind index is `.L32` (so `Kind.m = 32`) while the kind's `m` is `σ.m`, and `seq4`'s offsets differ
  from 3.x's past field 7. So each relation `rel*4` is 3.x's text with `P.kv.m κ`, `P.kv.node κ`,
  `P.S.*`, `P.lrR/e2R/e4R` and `pe4 P.S`; the controls `rel*4_fin3P` prove each equals 3.x's at
  `fin3P` (Z, Lr, B′, Lc), so nothing was lost in the generalisation.
- **D7. `relSh4` keeps the link term general** (`linkSum (impl.linkWAll κ tt rr) …`). The brief
  asked for `run_linkOps_zero` inside the flag lemma; keeping the flag kind-free and closing the link
  term at the front check (`linkWAll_seg*` gives `0^8`, then `linkSum_zero`) needs no second proof of
  the 32 link ops. `run_linkOps_zero` stays available.
- **D8. `exec_gFinRS` reruns 3.x's kit on relocated ops** (`run_elemOps4` …): RS0's slice reads move
  with `seq4`'s RS0 offset, so 3.x's `run_claimOps` could not be reused. The kit takes the weight op's
  invariance `reloc S (wop i) = wop i` as a hypothesis (every `wop` is `getF`/`const`).
- **D9. Kind by the seed, not by `kindOf4 π`.** `seed_byte4` reads the program's own check
  (`hdr`'s first 16 bytes against `[p.byte, m, 0…]`), so it holds on every accepted run, whatever the
  dispatcher did.
- No value asserted by no final was met in this scope.

### Controls (`FRSoundness4R4FinCtrl`)

| Definition | Positive | Negative |
|---|---|---|
| `relZ4`, `flag_gFinZ` | `relZ4_fin3P` (= 3.x's `relZ` at `fin3P`) | `relZ4_rejects` (a wrong `c_Z` register gives `false`) |
| `relLr4`, `flag_gFinLr` | `relLr4_fin3P`, `relLr4_leaf` | `relLr4_rejects` (a node's wrong end claim gives `false`) |
| `relB4`, `pubH4`, `vStar4` | `relB4_fin3P` | (3.x's `relB` negative carries over through `relB4_fin3P`) |
| `relLc4` and its parts | `relLc4_fin3P` | `lcFree4_leaf` (a leaf's free term vanishes: the node/leaf split is live) |
| `pe4` | `pe4_seq3` (= 3.x's `pe` at `seq3`) | `reloc_seq4_moves` (S-F4's: `seq4` moves `E`) |
| `OutsLt` | `outsLt_ctx0` | `not_outsLt_self` |
| `kindOfC_byte4` | `kindOfC_seg4`/`_node4` | `kind_zero_none` (byte `0` is no kind: the `p.byte ≠ 0` hypothesis is needed) |

`relE4`, `relSh4`, `relRS4` have no `fin3P` agreement lemma yet (their 3.x relations read `oE4end`,
`Array.replicate 18`, `rsLeafZero` through `absOff`; each is a `pe4_seq3`-style rewrite): **todo**
for the next pass, with a negative each (`relE4` with a wrong E4-end message, …).

### Traps (for whoever continues)

1. **`skeleton4` must never reach the unifier under a reducible head.** `rfl : fi.outs = (skeleton4 seq4
   p).2.outs` with `fi` a metavariable, `rcases … with rfl` on `x = (outsOf ⟨skeleton…⟩ n).headD 0`, and
   `List.mem_of_mem_drop` on `coordsR ⟨skeleton…⟩ n` all whnf `skeleton4` (heartbeat timeout at the
   declaration). State register bounds for an abstract `fi` (`hin_Lr`), give `fi` explicitly, and only
   then instantiate.
2. `simp only [reloc]` on `reloc S (wop i)` unfolds into a match on the opaque `wop i`: rewrite with
   `reloc S (wop i) = wop i` first.
3. Unfolding `reloc` on a read leaves `if f < 19 …` unless `hf : f < 19` is in the simp set, and
   `absOff 0 x` must go through `absOff_zero` (else `rfl` evaluates `fieldOffA`).
4. Any simp that meets `bytesOf ([p.byte, m] ++ List.replicate 46 0)` hits max recursion:
   `generalize` the constant.

### Handover (remaining items, in order)

3. **The front checks** (each `¬ Rej L es` on `es = fsOf tr (itemsOf seq4)`, then on
   `entriesOf L (pathOf L j)` by `runLog_chain4`). Pattern: `rel*4_of_accept` (copy `relLr4_of_accept`
   with the field index of `(finalsOf P).rest` = `[Z, Lc, Sh, Lr, E, B′, P0…P4, Pf]`, `hin_*` for an
   abstract `fi`); `val_eqv_f` on the conjunct; then each register through the views, rewriting
   `outsOf ⟨skeleton…⟩ name` by `outsOf_skel` + `phaseIx4_rounds`:
   - **`RejEndLr4`** (first; all pieces exist): `P = nodeFinP ν cells`, `kindOfC_node4` + `onNode_iff`;
     `claimN Lr2` = `clR 179 (fun _ _ => 0) L es (min (realRounds p "Lr2" 17) 17)` from
     `roundsF3_view4` at `n = 14` (head `.f 0`: `clVal .zero`); `phStart4 14 = 179`, `phStart4 13 = 170`
     (`fsStarts4_eq`); `min … = lrR ν` (`dims_node4`, `P4b.dims_le`); Lr1's coordinates = `tauS`'s
     `coordAt es 169 l` (`coords_view4` at Lr1's index); Lr2's challenges = `rch 179 es j` = `rxs`;
     `pe4 seq4 inp fLrEnd (16 j)` = `vEnd 17 179 es j` = `readF (msgAt es 213) (16 j)` through
     `SkRun4.hq 213` (one table certificate: `(fsMsgs4 seq4).getD 213 none = some (fieldOffOf seq4
     fLrEnd, 48)`) and R4b's `msgAt_of_q`/`readF_piMsg`; `eqPoint` to `eq ∘ ptOf` by
     `FRVerifierImplOps.eqPoint_eq`.
   - `RejEndE4` (n = 18, Eend at 273, `relE4` 1st conjunct), `RejInE4` (n = 21 `roundsF2_view4`'s
     `Chk2`, head `= claim0 E4` = `relE4` 2nd conjunct = `c4E4 es`: needs `lrEx fi 0` = `vLv4`, i.e.
     `exAt`'s bookkeeping that `ex[4]` is `gFinLr`'s exports), `RejFinE4 srcE srcL` (`relE4` 3rd
     conjunct; the node plan's `evalM`/`evalL` must meet `wEb4`: parameters), `RejZ` (`relZ4` 1st
     conjunct at n = 5; head = Z2's `b+s+133` from `uni_view4` with `segPt_lt` for a segment; target
     spec `implSegC_meets` → `peL`), `RejL2` (n = 8), `RejLc2`/`RejLcN` (`relLc4` 3rd conjunct, 3.x's
     `lc_bridge` path), `RejS2` (n = 12; head = `relSh4` 1st conjunct; `shiftTarget` spec → `c0S`;
     a segment's `bnd` tail is `lastRegs` = P4a's `run_lastOps` bits), `RejRS4 (okRS4 oZ oLc oSh)`
     (`exec_gFinRS`'s `rsAlpha4` = `alphaL4` through `sv4` = `sliceL4` (`msgAt es 326`) and
     `rsW4` = `cwL4`).
   - Still owed for item 2: `fin3P` agreement controls for `relE4`, `relSh4`, `relRS4` (+ a negative
     each).
4. **`AcceptTail` (T4)**: `chain`, `len` from `runLog_chain4`; `rejF` from item 3; `p1`/`pf` need
   K-round views (port 3.x's `rounds_view` to `rounds_at4`'s form); `lvl4` needs level 4's column
   values (port `posT` for `posOps4`, R4's D2) and the flags of `gFinP 4`/`gFinPf` at `FinP`
   (`flag_finP4`, `flag_finPf`'s generalisation, not started).

## Pass 4 (track R4d; HEAD `5eb34a6`, re-snapshotted to `c2c6fba`)

- **Build tree** `logs/fr-build-R4d` (a copy of `fr-build-R4c`; `b.sh` logs to `logs/R4d/`; `MINE.txt`
  adds `FRSoundness4R4Ex`, `FRSoundness4R4FrE`, `FRSoundness4R4FrCtrl`). Every lean/lake command ran
  in the 16G scope (12G for single files) under `timeout`. No sub-agents. Nothing committed. Only new
  `FRSoundness4R4*` modules written (every new short name grepped first); no existing module edited,
  no statement changed.
- **Re-snapshot.** Built first at `5eb34a6`, then at `c2c6fba` (blueprint 4.3, S-E12c, S-CN4), on the
  coordinator's instruction. **INT-8 had not landed** when this pass stopped: its repairs are not
  applied (see the handover).
- **Imports for `FR.lean`:** add `import FRSoundness4R4FrCtrl` (it pulls `FRSoundness4R4FrE`,
  `FRSoundness4R4Ex`).

### Status

| Item | State |
|---|---|
| `exAt` bookkeeping (`lrEx` holds `vLv4`) | **Done**: `baseAt`, `exAt_succ`, `fields_ex4`, `lrEx_eq4` |
| `RejEndLr4` | **Done**: `lr_end4`, `not_rejEndLr4_node`, `not_rejEndLr4_seg` |
| `RejEndE4` | **Done**: `relE4_of_accept`, `e_end4`, `not_rejEndE4_node/_seg` |
| `RejInE4` | **Done**: `e_in4`, `not_rejInE4_node/_seg` |
| `RejFinE4 srcE srcL` | **Done, with the node matrix facts as parameters** `hM`/`hL` (`evalM`/`evalL` = the node rows' `Eval.matMLE`): `e_fin4`, `not_rejFinE4_node/_seg` |
| `RejL2` | **Done** (both kinds): `relLc4_of_accept`, `l2_chk4`, `not_rejL2_4` |
| `relSh4`'s link term on a segment | **Done**: `linkSum_seg4` (`linkWAll_seg_of_meets` + `linkSum_zero`). The node chain (S-CN4 §5) is not started |
| Controls for `relE4`, `relSh4`, `relRS4` | **Done**: `relE4_fin3P`, `relSh4_fin3P`, `relRS4_fin3P` (+), `relE4_rejects`, `relSh4_rejects`, `relRS4_rejects` (−) |
| `RejZ`, `RejLc2`/`RejLcN`, `RejS2`, `RejRS4` | Not started (handover) |
| `AcceptTail` | Not started (handover) |

**Final checks** (HEAD `c2c6fba`, R4's 20 modules overlaid):
- `lake build FR FRSoundness4R4FrCtrl`: **green, 2,503 jobs** (`logs/R4d/build-final.log`).
- **Axioms** (`logs/R4d/axioms.log`, `logs/fr-build-R4d/ax/AxR4d.lean`; all 239 theorems of the 20 R4
  modules): within `propext`, `Classical.choice`, `Quot.sound` (229 use some, 10 none); no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 281
  files, 0 findings (`logs/R4d/source-rule.log`). The word `export` was reworded in two comments
  (coordinator's note).
- **Times** (sequential, one core: `taskset -c 0 lake env lean -DElab.async=false --profile`;
  `logs/R4d/prof-*.log`; import ≈ 4 s):

  | Module | wall | type checking | tactic execution | max RSS |
  |---|---|---|---|---|
  | `FRSoundness4R4Ex` | 8.4 s | 0.51 s | 1.21 s | 3.0 GB |
  | `FRSoundness4R4FrE` | 11.8 s | 1.34 s (incl. the two `fsMsgs4` certificates) | 1.58 s | 3.0 GB |
  | `FRSoundness4R4FrCtrl` | 6.6 s | 0.02 s | 0.07 s | 3.0 GB |

  Net kernel cost of the pass ≈ 1.9 s. No `decide` over a program, a register file or a sum: only the
  two message-table certificates (`fsMsgs4_ends`: 213, 273, 325, 326; `fsMsgs4_front`: 67, 97) and
  `cases ν <;> decide` on three-kind dimension facts. No `show` over a skeleton; typed op lists were
  not needed (no op-list elaboration here).

### What was built (`loc.py`, `logs/R4d/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4R4Ex` | 142 / 107 / 6 | `opsOut_gFinRS` (4,117), `gFinRS_ex_lt`; `baseAt`, `exAt_zero`, **`exAt_succ`**; **`fields_ex4`** (field `k` runs from `Rs k` with outputs list `Ex k`, `Ex (k+1) = (Ex k).push (field k's list at (Rs k).size)`, `zhat` in `Rs 0`); `lrEx_eq4` |
| `FRSoundness4R4FrE` | 557 / 453 / 38 | views by name: `ph4`, `val_eqv_f4`, **`fsMsgs4_ends`**, **`msg_abs4`**, **`coordsR_view4`**, **`chals_view4`**, **`claimN3z_view4`**, **`one_name_view4`**; `kindOfC_acc_node/_seg`; Lr: `vEnd_lr4`, **`lr_end4`**, `not_rejEndLr4_*`; E: `hin_E`, `rest_gFinLr/E/Lc`, `opsOut_gFinLr` (14), **`relE4_of_accept`**, `vEnd_e4`, **`e_end4`**, `not_rejEndE4_*`, `chk2F_c0`, **`e_in4`**, `not_rejInE4_*`, `clR2_c0_succ`, **`e_fin4`**, `not_rejFinE4_*`; L: `fsMsgs4_front`, `hin_Lc`, **`relLc4_of_accept`**, **`l2_chk4`**, `not_rejL2_4`; `linkSum_seg4` |
| `FRSoundness4R4FrCtrl` | 77 / 43 / 7 | controls (below) |
| **new total** | 776 / 603 / 51 | R4 total now 4,431 / 3,465 / 239 |

### Main statements

```lean
theorem fields_ex4 (P : FinP) (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ zh Rs Ex, (∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)) ∧
      (∀ x ∈ zh, x < (Rs 0).size) ∧ ∀ k (hk : k < 12), (Ex k).size = k + 1 ∧ ∃ L,
        pureRun impl p.tix inp (((finalsOf P).rest[k] ⟨outs, zh, Ex k⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true) ∧
        Rs (k + 1) = Rs k ++ L.toArray ∧ Ex (k + 1) = (Ex k).push ((finalsOf P).rest[k] ⟨outs, zh, Ex k⟩ (Rs k).size).2
theorem relE4_of_accept (P : FinP) (h : …) : ∃ y, SkRun4 impl p inp tr y ∧ ∃ fi R3 R,
    fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R3 ∧ ExtA R3 R ∧ (∀ x ∈ fi.zhat, x < R.size) ∧
    relE4 impl p.tix inp fi R P = true ∧ fv R (lrEx fi 0) = vLv4 inp fi R3 P ∧
    (rd R (lrEx fi 1)).toAF = ((chals fi "Lr2" P.lrR).map (fv R3)).toArray
theorem lr_end4 (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR 179 (fun _ _ => 0) L es (lrR ν) = eq (ptOf (lrR ν) (tauS (lrR ν) 169 es)) (ptOf (lrR ν) (rxs (lrR ν) 179 es)) *
      (vEnd 17 179 es 0 * vEnd 17 179 es 1 + vEnd 17 179 es 2)            -- es = fsOf tr (itemsOf seq4)
theorem e_end4 (h : … nodeFinP ν cells …) (L) : clR 227 (fun _ _ => 0) L es (e2R ν) = eq (…214…) (…227…) * (…)
theorem e_in4 (h : … nodeFinP ν cells …) (L) : ∀ l < ncR ν, Chk2 275 16 readF (fun d => chF d 0) c4E4 L es l
theorem e_fin4 (srcE srcL) (hM : ∀ r2 r4, r2.size = e2R ν → r4.size = ncR ν → impl.evalM r2 r4 = (matMLE (srcE ν).ea …, …))
    (hL : ∀ rL r4, rL.size = lrR ν → r4.size = ncR ν → impl.evalL rL r4 = (matMLE (srcL ν).ea …, …)) (h) (L) :
    clR2 275 16 readF (fun d => chF d 0) c4E4 L es (ncR ν) = mle (wEb4 srcE srcL ν es) (ptOf (ncR ν) (rPt4 ν es)) * readF (msgAt es 325) 0
theorem l2_chk4 (P : FinP) (hP : P.S = seq4) (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) (L) :
    ∀ l < 14, Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es l
-- and ¬ P4b.RejEndLr4 / RejEndE4 / RejInE4 / RejFinE4 srcE srcL, ¬ P4a.RejL2 on `fsOf tr (itemsOf seq4)`, per kind
```

On the chain of `runLog_chain4` these transfer by its `entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4)`.

### Design and deviations

- **D10. `fields_ex4` restates `fields_of_accept4` with the fold's outputs** (it does not change it).
  `accept_chain4` gives field `k` the list `exAt … k` computed at the fold's own bases; `baseAt`/
  `exAt_succ` and `(Rs k).size = baseAt … k` (by `pureRun_len`) make `Ex (k+1)` the push of field
  `k`'s list at the base it actually ran from. That is the whole of the `lrEx`-holds-`vLv4` bookkeeping.
- **D11. Node matrix facts are parameters** (`hM`, `hL` of `e_fin4`): `evalM`/`evalL` equal the node
  rows' `Eval.matMLE` at the points, the form `P4b.mle_wEb4` consumes. S-CN4's node ops do not
  include `evalM`/`evalL` specs; whoever owns them discharges `hM`/`hL` (any spec giving the three
  `matMLE`s implies them).
- **D12. Few op-list facts, isolated** (for INT-8): `opsOut_gFinLr` (14 outputs), `gFinLr`'s two
  outputs `[b + 13, b + 4]` (used by `rfl`/`show` in `relE4_of_accept`), `opsOut_gFinRS` (4,117) and
  `gFinRS_ex_lt`, and the rest's indices `rest_gFinLc/Lr/E` (1, 3, 4). Everything else goes through
  `FinP` fields, `flag_gFin*` and the views.
- No value asserted by no final was met in this scope.

### Controls (`FRSoundness4R4FrCtrl`)

| Definition | Positive | Negative |
|---|---|---|
| `relE4` | `relE4_fin3P` (= 3.x's `relE`) | `relE4_rejects` (a wrong E4-end value register gives `false`, both kinds) |
| `relSh4` | `relSh4_fin3P` (= 3.x's `relSh`) | `relSh4_rejects` (an S2 first-claim register without an F value gives `false`) |
| `relRS4` | `relRS4_fin3P` (= 3.x's `relRS`) | `relRS4_rejects` (a leaf with nonzero fourth slices gives `false`) |
| `baseAt`, `exAt` | `baseAt_ctl` (field 1's base is `b + 1`; `exAt` pushes `[b]`) | `baseAt_ctl` (the base is not `b`) |

### Traps (new)

1. `Nat.exists_eq_succ_of_ne_zero` gives `n.succ`: rewrites against `n + 1` then fail silently.
   Use `⟨x - 1, by omega⟩`.
2. `rw [ptA_toArray, ptA_toArray, …]` fails once the distinct instances are used up; `simp only`.
3. `List.size_toArray` did not fire on `l.toArray.size` after `Array.size_append` (it became
   `toList.length`); `have : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl` or `simp`.
4. Giving `fi` as `_` in the final `exact ⟨…, rfl, …⟩` against `(skeleton4 seq4 p).2.outs` hit R4c's
   trap 1 (heartbeat timeout): give `⟨outs, zh, Ex k⟩` explicitly.
5. `simp [relE4, Val.eqv]` unfolds every `eqv` into a 7-way match; rewrite the one conjunct to
   `false` first and `simp only` the `&&`s.

### Handover (remaining items, in order)

0. **INT-8 repairs** when its commit appears: re-snapshot, apply INT-8's "For R4d" list. In this
   pass's modules, look first at D12's lemmas (`opsOut_gFinLr`, `gFinLr`'s outputs used in
   `relE4_of_accept`, `opsOut_gFinRS`, `gFinRS_ex_lt`, `rest_gFin*`) and at `fields_ex4` (it unfolds
   nothing of `finOps4` beyond `finOps4_eq`/`accept_chain4`).
1. **`RejS2`** (n = 12, `roundsF2_view4`, `nrS κ` real rounds): head = `relSh4` (i) =
   `shiftTarget ks τ θ bnd` (`flag_gFinSh` needs a `relSh4_of_accept`: copy `relLc4_of_accept`,
   field index 2, `hin` over `coordsR S1`, `chals S2`, `lastRegs`, `zeroReg`, `zhat 2`); then
   `c0S es` needs the `shiftTarget` spec (segment: `implSegC_meets`; node: S-CN4's specs via
   `implN4_meets`), `τ = pad18 (tauL)` by `coordsR_view4` (S1, n = 11), `θ = thL`, `ks = ksL`, and
   `bnd`: a segment's `lastRegs` values are P4a's `run_lastOps` bits (`lastBits es`), a node's
   `lastPad`. The `Chk2 … c0SL` transfer is `chk2F_c0`.
2. **`relSh4`'s node link term**: S-CN4 §5's chain (`implN4_meets` → `shiftMask4S`, `slotWS`,
   `linkWAll4S`; `linkSum_eq8`; `wSumNode4 ν es`; `wNS4_node4`), giving `oSh4 wNS4`; the segment's is
   `linkSum_seg4` (done).
3. **`RejZ`** (n = 5, `roundsF3_view4`, head = Z2's `b+s+133` from `uni_view4`; `segPt_lt` for a
   segment's `hpt`; `targetS`: segment `implSegC_meets`, node the parameter `tS` until
   `targetSNode4I` (S-CN4's next) with `peL_node4`); then `relZ4` (i) through `coordsR_view4` (Z1,
   n = 3) and `chals_view4` (Z3), Zend's message by `fsMsgs4_front.1`.
4. **`RejLc2`/`RejLcN`**: `relLc4` (ii) on `relLc4_of_accept` (done), 3.x's `lc_ii_run`/`lc_bridge`
   path with `walkAB`/`rowW`/`eqZ` at their specs as parameters (3.x's `hW hR hZ`); L3's values
   are `fsMsgs4_front.2` (`lcV4` = the log's `vL`).
5. **`RejRS4 (okRS4 oZ oLc oSh)`**: `exec_gFinRS` (needs a `relRS4_of_accept`, field `finRS` on the
   skeleton file itself: `accept_chain4`'s `L₀`) gives `α_j = rsAlpha4`; `sv4 = sliceL4` by
   `msg_abs4` at 326 (`fsMsgs4_ends.2.2.2`), `rsW4 = cwL4` (weights from L2/S2/RS1 challenges by
   `chals_view4`/`coordsR_view4`); the bindings: `oZ` from `relZ4` (ii), `oLc` from `relLc4` (iii)
   (`zhat 1`), `oSh` from item 2, `okE4` from `relE4`'s `e4` (done in `e_fin4`'s `hα`).
6. **`AcceptTail` (T4)**: `chain`, `len` from `runLog_chain4` (482 ≥ `pfStart + 14`); `rejF` from
   items 1–5 and this pass; `p1`/`pf`: K-round views (port 3.x's `rounds_view` to `rounds_core4`'s
   form, `roundKVals`); `lvl4`: level 4's column values (port `posT` for `posOps4`, R4's D2) and the
   flags of `gFinP 4`/`gFinPf` at `FinP` (`flag_gFinP`, `flag_gFinPf`, not started; after INT-8, as
   the final field becomes one zero-padded field).

## Pass 5 (track R4e; HEAD `29d0016`, re-snapshotted to `1ee751b`, then `3ef2c51`)

- **Build tree** `logs/fr-build-R4e` (a copy of `fr-build-R4d`; `b.sh` logs to `logs/R4e/`; `MINE.txt`
  adds `FRSoundness4R4Fld`, `FRSoundness4R4FrS`, `FRSoundness4R4FrZ`, `FRSoundness4R4FrLc`,
  `FRSoundness4R4FrRS`, `FRSoundness4R4FrCtrlB`). Every lean/lake command ran in the 16G scope (12G for
  single files) under `timeout`. No sub-agents. Nothing committed. Only new `FRSoundness4R4*` modules
  written (every short name grepped first); no existing module edited, no statement changed.
- **Re-snapshots** on the coordinator's instructions: S-T2 (`1ee751b`), S-CN4b (`3ef2c51`). **INT-8 had
  not committed** when this pass stopped (its edits are in the shared working tree, uncommitted; the
  build tree uses HEAD's files), so item 1 (INT-8's repairs) is still open.
- **Imports for `FR.lean`:** add `import FRSoundness4R4FrCtrlB` (it pulls `FRSoundness4R4FrRS` →
  `FrLc` → `FrZ` → `FrS` → `Fld`, and `FRVerifierImplNode4T`).

### Status

| Item | State |
|---|---|
| 1. INT-8's repairs | **Open**: INT-8 not committed |
| 2. `RejS2` | **Done**, both kinds: `not_rejS2_seg4`, `not_rejS2_node4` (`shiftTarget` at `shiftTargetS`: parameter `hST`) |
| 3. `relSh4`'s node link term | **Done**: `sh_bind_node4` (`oSh4 wNS4`, through `wSumNode4` and `CN4.wNS4_node4`); the segment's `sh_bind_seg4` (`wSumSeg`) |
| 4. `RejZ` | **Done**, both kinds: `not_rejZ_seg4` (`targetSSegS`, P4c's `peL_seg` with `lastOps`' bits), `not_rejZ_node4` (`targetSNode4S`, `peL_node4`); `targetS` at its spec is the parameter `hTS`, discharged for `implN4T` by `targetSNode4_meets` (`nodeC_params`) |
| 5. `RejLc2`/`RejLcN` | **Done**, both kinds: `lc_ii4` (3.x's `lc_ii_run` ported; `walkAB`/`rowW`/`eqZ` specs the parameters `hW hR hZ`, as 3.x), `not_rejLc_seg4`, `not_rejLc_node4` |
| 6. `RejRS4 (okRS4 oZ oLc4 (oSh4 wNS))` | **Done**, both kinds: `not_rejRS4_seg` (any `wNS`), `not_rejRS4_node` (`wNS4`) |
| 7. `AcceptTail` | **Not started** (handover) |
| Coordinator: the RS front's `rsWeightS4` bridge | **Not started** (handover, with the exact form asked) |

**Final checks** (HEAD `3ef2c51`, R4's 26 modules overlaid):
- `lake build FR FRSoundness4R4FrCtrl FRSoundness4R4FrCtrlB`: **green, 2,514 jobs** (`logs/R4e/build-final.log`).
- **Axioms** (`logs/R4e/axioms.log`, `logs/fr-build-R4e/ax/AxR4e.lean`; all 311 theorems of the 26 R4
  modules): within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 295
  files, 0 findings (`logs/R4e/source-rule.log`).
- **Times** (sequential, one core: `taskset -c 0 lake env lean -DElab.async=false --profile`;
  `logs/R4e/prof-*.log`; import ≈ 4–5 s; `FrCtrlB` at `3ef2c51`, the others at `1ee751b`):

  | Module | wall | type checking | tactic execution | max RSS |
  |---|---|---|---|---|
  | `FRSoundness4R4Fld` | 7.6 s | 0.12 s | 1.02 s | 2.9 GB |
  | `FRSoundness4R4FrS` | 10.9 s | 0.82 s | 1.49 s | 3.0 GB |
  | `FRSoundness4R4FrZ` | 9.4 s | 0.58 s | 1.14 s | 3.0 GB |
  | `FRSoundness4R4FrLc` | 7.4 s | 0.16 s | 0.44 s | 3.0 GB |
  | `FRSoundness4R4FrRS` | 11.2 s | 0.30 s | 0.99 s | 2.9 GB |
  | `FRSoundness4R4FrCtrlB` | 6.6 s | 0.05 s | 0.15 s | 2.9 GB |

  Net kernel cost of the pass ≈ 2.0 s. No `decide` over a program, a register file or a sum; one
  small certificate (`fieldOff_hdr_stmt4`: `seq4`'s `hdr`/`stmt` offsets), the rest `cases κ <;> decide`
  on kind constants.

### What was built (`loc.py`, `logs/R4e/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4R4Fld` | 125 / 96 / 5 | **`Fields4`** (one accepted run's `zhat`, files, exports and `finRS`'s run), **`fields4_of_accept`**, `Fields4.chain/zlt'/sk_lt/pos` |
| `FRSoundness4R4FrS` | 538 / 429 / 31 | the log's public reads (`seedQ4`, `seed_bytesAt4`, `stmt_msg4`, `nStmt_eq4`, `bnd_seg4`); **`last_view4`** (a segment's `lastOps` registers, P4a's `run_lastOps`); `relSh4_of_fields`; `s1_view4`, `s2r_view4`, `s2_from_head4`, `lastRegs_view4`; **`sh_head_seg4/_node4`** (S2's head is `c0S`); `s2_chk_*`, **`not_rejS2_seg4/_node4`**; **`sh_bind_seg4/_node4`**; `segOps_of_meets`, `nodeOps_of_meets`, `shiftTarget_of_meets` |
| `FRSoundness4R4FrZ` | 306 / 248 / 15 | `coords_pt_view4`, `pt_cAt4`, `uni_cAt5`, `lastAt_pad19`, `lag_c0Z`; **`z3_head_seg4/_node4`** (Z3's head is `c0Z`); `relZ4_of_fields`, `clR_c0_eq`, **`z_chk4`**, **`not_rejZ_seg4/_node4`** |
| `FRSoundness4R4FrLc` | 176 / 147 / 5 | `relLc4_of_fields`, `lcV4_eq`, **`lc_ii4`**, **`not_rejLc_seg4/_node4`** |
| `FRSoundness4R4FrRS` | 261 / 204 / 11 | `Fields4.fv_zh`, `rs_vals4`, `lam_view4`, **`rs_alpha4`** (`α_j = alphaL4`); `z_bind4`, `lc_bind4`, `relE4_of_fields`, `e_bind4`; **`not_rejRS4_seg/_node`** |
| `FRSoundness4R4FrCtrlB` | 88 / 61 / 5 | controls (below) |
| **new total** | 1,494 / 1,185 / 72 | R4 total now 5,925 / 4,650 / 311 |

### Main statements

```lean
structure Fields4 (impl p inp tr) (P : FinP) (y) (zh : List Reg) (Rs : ℕ → Array Val) (Ex : ℕ → Array (List Reg)) : Prop
  -- sk : SkRun4 …; ext; zlt; zh_eq : zh = ((finalsOf P).finRS ⟨outs, [], #[]⟩ |skel|).2; rs : finRS's run; fld : field k's run
theorem fields4_of_accept (P) (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) : ∃ y zh Rs Ex, Fields4 impl p inp tr P y zh Rs Ex
theorem not_rejS2_seg4 (hST) (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L) :
    ¬ P4a.RejS2 L (fsOf tr (itemsOf seq4))                    -- and not_rejS2_node4 (nodeFinP ν cells)
theorem sh_bind_node4 (hST hSM hSW hLW) (hF : Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex) :
    P4a.oSh4 P4a.wNS4 (kindOfC es) es (fv (Rs 2) (zh.getD 2 0)) -- and sh_bind_seg4 (any wNS)
theorem not_rejZ_seg4 (hLS hTS) (indN etN) (h) (L) : ¬ P4a.RejZ (P4a.zlm4 indN etN) L es
theorem not_rejZ_node4 (hLS) (hTS : ∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r) (h) (L) :
    ¬ P4a.RejZ (P4a.zlm4 N4c.indN4 N4c.etN4) L es
theorem lc_ii4 (hW hR hZ) (hF) (hPS : P.S = seq4) (hnode) (hκ) (M) (hA : M.Ak = zlmFR.Ak) (hB) (L) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 =
      ∑ j, P4a.vM (kindOfC es) es j * mle (linM (M.Ak j) (M.Bk j) (P4a.rwL es) (alL es)) (ptOf 14 (rkL es))
theorem not_rejLc_seg4 (hW hR hZ) (indN etN) (h) (L) : ¬ P4a.RejLc2 (zlm4 indN etN) L es ∧ ¬ P4a.RejLcN (zlm4 indN etN) L es
theorem rs_alpha4 (hZ) (hF) (hPS) (hm : P.kv.m p.tix = (kindOfC es).m) (j : Fin 4) (hj : j < (rsPtsL4 κ es).length) :
    P4b.alphaL4 κ es j = fv (Rs 0) (zh.getD j 0)
theorem not_rejRS4_node (hZ hLS hST hSM hSW hLW) (h) (L) :
    ¬ P4b.RejRS4 (P4b.okRS4 P4a.oZ P4a.oLc4 (P4a.oSh4 P4a.wNS4)) L es   -- and not_rejRS4_seg (any wNS)
-- es = fsOf tr (itemsOf seq4)
```

The op parameters are equations about `impl` at the spec forms (`hZ`: `eqZ = eqZS`, `hLS`: `lagrangeS =
lagrangeSS` at 127 values, `hTS`: `targetS` at the kind's spec, `hST`, `hSM`, `hSW`, `hLW`, and 3.x's
`hW`, `hR`). **`segC_params`** / **`nodeC_params`** prove all of them for the concrete ops
(`implSeg (implC …)`, S-CN4b's `implN4T` over `implC`), so none is an assumption left open.

### Design and deviations

- **D13. `Fields4`.** `fields_ex4` (R4d) gives each field's run with existential `zhat`/files; the RS
  bindings need `finRS`'s `α_j` and Z's/Lc's/Sh's/E's relations on the *same* registers, so `Fields4`
  packages one choice (plus `finRS`'s run, which `fields_ex4` dropped). `fields4_of_accept` reruns
  `fields_ex4`'s proof; `fields_ex4` itself is unchanged. New `rel*_of_fields` (Z, Lc, Sh, E) sit beside
  R4d's `rel*_of_accept` (`relSh4_of_accept` is now a corollary).
- **D14. Op facts as equations, not `Meets`.** Each front statement takes only the op equations it
  uses; `segOps_of_meets`/`nodeOps_of_meets` and the controls `segC_params`/`nodeC_params` derive them
  from `Meets`. This keeps the statements independent of how S-CN4b/S-T2 assemble `specN4`
  (`withRS4S` changed `specN4` mid-pass; nothing here broke).
- **D15. `RejZ`'s `M`.** The segment's is any `zlm4 indN etN` (its targets are `EtSeg`, so the node
  maps do not matter); the node's is `zlm4 N4c.indN4 N4c.etN4` (what `peL_node4` speaks of).
- **D16. `not_rejRS4_seg` holds for every `wNS`** (a segment's Sh binding reads `wSumSeg`); the node's is
  at `P4a.wNS4`.
- No value asserted by no final was met in this scope.

### Controls (`FRSoundness4R4FrCtrlB`)

| Definition / parameter | Positive | Negative |
|---|---|---|
| `Fields4` | `fields4_of_accept` | `not_fields4_nil` (no fields on an empty trace) |
| the segment statements' op parameters | `segC_params` (`implSeg (implC …)` meets all nine) | `clR2_c0_dep` (the claim switch needs its hypothesis) |
| the node statements' op parameters | `nodeC_params` (`implN4T` over `implC` meets all nine; `targetS` by `targetSNode4_meets`) | as above |
| `lastAt_pad19` | `lastAt_pad19_ctl` | — (an equation) |

### Traps (new)

1. **`congr 1` on `(w_out + w_in) * v = W * v`, `.f a = .f b` or an `interpolateAt` equation** whnf's the
   whole term (heartbeat timeout or max recursion at the declaration): use `congrArg (· * v)`,
   `congrArg Val.f`, or `funext` lemmas and `rw`.
2. `chk2F_c0 rfl` with implicit claims timed out: give `c0`/`c0'`.
3. Again R4c's trap 1: `exact ⟨…, _, Rs 2, rfl, …⟩` against `skeleton4` — give `fi` explicitly;
   `s1_view4 … rfl` likewise needs `(fi := ⟨…⟩)`.
4. `show (impl.eqZ _ _).getD i 0 = …` on `rsW4` timed out: `simp only [rsW4, P4b.cwL4, cwF]` instead.
5. A `Reg`-typed `<` (`headD` of an outs list) defeats `omega` (R4b's trap): wrap with `lt_reg`.
6. `simp` cannot rewrite the `n` of `eq (ptOf n a) (ptOf n b)` (dependent `Fin n`): `rw` all occurrences at
   once.
7. `rw [h] at hlen` with `h : seq4.s2 = 28` also rewrites `chals fi "S2" seq4.s2` inside: use
   `hlen.trans h`.

### Handover (remaining items, in order)

1. **INT-8's repairs** when its commit appears (re-snapshot: `b.sh` snapshots HEAD each run). Places
   that unfold `finOps4`/`finalsOf` beyond `finOps4_eq`/`accept_chain4`: R4d's D12 lemmas (`rest_gFin*`,
   `opsOut_gFinLr`, `gFinLr`'s outputs in `relE4_of_accept`/`relE4_of_fields`, `opsOut_gFinRS`,
   `gFinRS_ex_lt`); this pass adds `rest_gFinSh`, `rest_gFinZ` (index 2, 0), `Fields4.zh_eq`/`rs`
   (`(finalsOf P).finRS` = `gFinRS P`, used by `rs_vals4` through `exec_gFinRS`; INT-8's working tree gives
   `gFinRS` a `Q` table argument), and `last_view4` (`absTail4`'s segment `stmt` case:
   `stmtOps4 ++ lastOps`; robust to `stmtOps4`'s content, it uses only that its run succeeds).
2. **The coordinator's RS bridge** (S-T2): state the Φ form of P4b's `wrsL4 kf` against
   `Impl.rsWeightS4 ν` at `kf := N4c.kf4 ν` (3.x's `rsWeight_kind_eq` form), using
   `KW4.kwS4_eq`/`kwS4_fast` in `FRKindWeight4`. It feeds `AcceptTail`'s `start`/W₀ (P4b's `W₀L4`,
   `c₀L4`), i.e. `finPf`'s `rsWeight` call; S-CN4b's `specN4` now carries `rsWeightS4 ν` (`withRS4S`).
3. **`AcceptTail` (T4)**: `chain`, `len` from `runLog_chain4`; `rejF` from R4d's and this pass's
   `not_rej*` (they are on `fsOf tr (itemsOf seq4)`; transfer to `entriesOf L (pathOf L j)` by
   `runLog_chain4`); `p1`/`pf`: K-round views (port 3.x's `rounds_view` to `rounds_core4`'s form,
   `roundKVals`); `lvl4`: level 4's column values (port `posT` for `posOps4`, R4's D2) and the flags of
   `gFinP 4`/`gFinPf` at `FinP` (`flag_gFinP`, `flag_gFinPf`: not started; after INT-8, whose final field
   becomes one zero-padded field). Read every field through `Fields4` (one `fields4_of_accept`).
4. `RejFinE4`'s node matrix parameters `hM`/`hL` (R4d's D11) are still parameters: whoever owns the node
   plan's `evalM`/`evalL` specs discharges them (S-CN4b did not).
