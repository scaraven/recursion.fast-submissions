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
