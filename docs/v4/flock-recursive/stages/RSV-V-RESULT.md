# RSV-V RESULT: the reserve's V side (the previous node's `evalM` claim in the parent's E-phase)

Track RSV-V, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`. Started at
HEAD `394f6ce`; final checks at HEAD `21ade15` (A3′ run 2 `e14db30` and B2′ on top). Build tree
`logs/fr-build-RSV` (copied from `fr-build-A2pp`, re-snapshotted on each new HEAD); logs `logs/RSV/`.
Journal: `stages/RSV-V-JOURNAL.md`. Spec: `D1p-RESULT.md` §3 (main worktree). No sub-agents, nothing
committed, no `FRSoundness4*` module edited.

## 0. Summary

- **Done.** `seq4`'s `Lrend` is 880 bytes and `Eend` 112 (`Seq.lrEnd`, `Seq.eEnd`; no item, no phase,
  no Fiat–Shamir position moves). `|π| = 876,176`, the stream `64 · 24,234`, `hUsed` +42/+70/+112
  (74,007 / 122,481 / 195,192), N8's `lBase` 195,328 ≤ 195,584: D1p's figures, all kernel-checked.
- **The V programs** (`FRVIRFinals4`) carry the child-claim terms in finE (ii)/(iii)/(iv), the 52 values
  in B′ at `κ′^{11…62}` and the 52 cells in finPf, for every node kind, on where the kind has a
  previous node (`N2`, `N4`) and asserted zero for `N8`; the segment group's finals are unchanged.
- **Three points the spec leaves open are decided** (§3): E2 stays a zero-claim zerocheck (the child
  term is written with `− v*`); an `N2` parent of an `N4`/`N8` child sums over its own coordinates and
  fixes the child's higher ones (the mixed point); `W*` of another kind is a second, kind-tagged
  `evalM` (`NI4F.evalMN4`), free for a same-kind child.
- **One finding for the orchestrator (§7, F1): the reserve as specified does not close the node
  chain when consecutive nodes have different kinds.** The in-circuit replay of `V(child)` then has a
  second `evalM` import (`W*` of the grandchild's kind), which the parent's 52 cells do not discharge.
- **KAT passes** (13 cases, `logs/RSV/rsvkat-4.log`), the plan-form KAT passes, A2″'s cap-check KAT
  still passes. **Red set: 7 declarations in 4 `FRSoundness4*` modules** (§5), against A3′'s restated
  chain (`e14db30`) and B2′ (`21ade15`).

## 1. What was built (code lines, the core's `loc.py`, HEAD `394f6ce` → now; `logs/RSV/loc.txt`)

| Module | Change | code |
|---|---|---|
| `FRShape4` | `Seq.lrEnd`/`eEnd` (defaults 48; `seq4` 880/112), `phasesOf` reads them; `seq3_eq`/`seq4_eq` (14 fields); `fieldSizesOf_seq4`, `piSizeOf_seq4 876176`, `streamBytesOf_seq4 1550976`, `chainLenOf_seq4 24234` | 239 → 241 |
| `FRVIRFinals4` | `FinP.rsvOps` (count), `rsv`, `rcells` (per kind), `nrcell` (count); `rsvRx/Ry/Abc/Kind`; **`rsvEOps`** (finE's child block, 87 registers); `gFinE0` (finE's own ops, gate a parameter); `gFinE` (exports the 52 values); `exE`; **`rsvBOps`** (B′'s values); `gFinB'`; `gFinPf`'s second cell chain + `keep rsv`; `noAsk_rsvEOps`, `noAsk_rsvBOps`; `fin3P`, `fin3P_S`; `capChkOps`' hoisted `aO`/`cO` (B2′'s request; op list unchanged) | 519 → 581 |
| `FRVIR4At` | `SameCounts` + `rsvOps`, `nrcell`; `map_at_gFinE`/`gFinB'`/`gFinPf` by cases on `rsvOps`; `gFinE_ex` | 326 → 331 |
| `FRVIR4Uni` | `nodeQ_counts`, `segQ_counts` (two more components) | 241 → 242 |
| `FRVerifierC4` | **`rsvRel`** (52 M-relative cells, from the dump), **`rsvCells κ`**; `segFinP` (reserve off), `nodeFinP` (`true, κ.hasPrev, rsvCells κ, 52`) | 99 → 106 |
| `FRVerifierImplNode4F` | `kindElemN`, `kindOfElem`, `sub3`; **`evalMPair`** (two kinds' difference, one `protoV4`) + `_eq`; **`evalMD4`/`evalMDS4`** + `_eq`; **`evalMN4`/`evalMNS4`** (dispatch on a 24-entry row point) + `_eq`; `implN4F`/`specN4F` re-pointed; `implN4F_meets`, `implN4F_hM` (an `e2R`-sized point is not tagged); `implN4F_ctl` restated; `evalMD4_ctl`; `slotV4_noPrev`, `slots_true` | 236 → 307 |
| `FRNodeCircuit4` | **`PubCellsR4`**; `rsvCells_ctl` | 300 → 307 |
| `FRNodeLayout4` | `aggChainLen_eq` (48,468 / 96,936), `aggChainLen_k3` (72,702), `hUsed_eq` (74,007 / 122,481 / 195,192), `regions_need_levers` (no-L2 stream 1,556,928), docs | 59 |
| `FRNodeKinds4` | `segB 1550976`, `cLen 24234`, `hEnd_eq` (74,009 / 122,485 / 195,200) | 393 |
| `FRX4Prog`, `FRX4Ext` | `875280` → `876176` | 169, 543 |
| `FRVIRTpl4Bridge` | `protoR_ctl` `(24234, 96936)`, `(24234, 48468)`, `(96936, 96936)` | 65 |
| `FRVerifierImplNode4T` | `nodeE4_ctrl`'s doc (`aggB 1 = 0x17AA80`; bits 13/12 still 1/0) | 404 |
| `FRNodeRows4Hint` | regenerated (`laydump4` + B2′'s `mkhint.py`, on HEAD `21ade15` + this track) | 35 |

Touched: 13 modules, +155 code lines. Probes (dev-only, in the build tree): `probe/RsvKat.lean` (the KAT),
`probe/RsvCells.lean` (too slow as written, replaced by reading `nodedump4`'s `mregs-p0.txt`),
`VTime4` (`kidN2`/`kidN4`: the child-kind tag).

## 2. The construction as built (registers: `FRVIRFinals4.rsvEOps`' doc)

With `η` = E1's coordinate 23, `κ_E` E3's challenge, `v* = a* + ηb* + η²c*`, `M̃_η = Ã + ηB̃ + η²C̃`:

- **finE (ii′)**: `claimN(E2) = eq(τ, r_E2)(âb̂ − ĉ) + η·eq(r̄*_x[<e2R], r_E2)·(m̂* − v*)`.
- **finE (iii′)**: `claim0(E4) = â + κ_E b̂ + κ_E² ĉ + κ_E³ v_L + κ_E⁴ m̂*`.
- **finE (iv′)**: `claimN(E4) = (M̃_own + κ_E³ L̃)(r_E2, r′)·f̂(r′) + κ_E⁴·eq(r̄*_y[<e4R], r′)·W*_η`,
  `W* = M̃_{κ*}(x̂, ŷ)`, `x̂ = r_E2 ‖ r̄*_x[e2R, 23)`, `ŷ = r′ ‖ r̄*_y[e4R, 25)`.
  V computes `W* = own evalM + evalM(x̂ ‖ kindElem*, ŷ)`; the second call returns `M̃_{κ*} − M̃_ν` at
  `(x̂, ŷ)` (`0`, unevaluated, when `κ* = ν`).
- The three own asserts are gated `node ∧ ¬rsv`, the three new ones `rsv`; `fEEnd[64, 112)` is zero
  for every kind; `fLrEnd[48, 880)` and `fEEnd[48, 64)` are zero where `rsv` is off (`N8`, segments).
- **B′**: `claim0(P1) = vRS + κ′²·S₉ + κ′^{11}·Σ_{i<52} κ′^i v_i` (gated `rsv`; the own assert `¬rsv`),
  `v = r̄*_x ‖ r̄*_y ‖ a* ‖ b* ‖ c* ‖ kindElem*` (finE's exports).
- **finPf**: the 52 cells `rsvCells κ` continue the cell chain at `κ′^{11…62}`; `keep rsv` selects the
  61-cell or the 9-cell sum.
- **The cells** (`rsvCells κ = 3·2^logM + rsvRel`, M-relative cells of slot 0's prototype 0): E2's 23
  challenges, E4's 25, the own `evalM`'s three outputs, the kind element (`hdr[0…16)`). Each register
  is a single import cell (`logs/RSV/nodedump/mregs-p0.txt`). `rsvCells_ctl`: 52 for `N2`/`N4`, none for
  `N8`, inside slot 0's region and `f`, distinct, disjoint from `cells4`.

Program sizes (`logs/RSV/dump/fsummary.txt`): segment programs unchanged (151,226 ops); node programs
151,474 → 154,433 ops (+2,959: finE +93, B′ +111, finPf +2,757 (52 cells × 53) − 2), registers
146,594.

## 3. Decisions on what the spec leaves open

1. **E2's initial claim stays `0`.** E2's `initClaim` is `.zero` (a skeleton `const`); D1p's
   `c₀ = η·v*` would need a new init form and move every later register. The child term is written
   `η·eq(r̄*_x, x)·(M̃*_η(x, r̄*_y) − v*)`, whose cube sum is `η(M̃*_η(r̄*) − v*)` (`Σ_x eq = 1`). The
   soundness is the spec's: own sum `S(τ)` plus `η·D`, `D` fixed before E1, `η` independent of `τ`, so
   `+1/|F|` (E1's row `(e2 + 3)/2^128`). The prover's E2 summand carries the `− v*` (For P2).
2. **Kinds of different dimensions.** An `N2` parent (22/24 real E2/E4 rounds) may have an `N4` or
   `N8` child (23/25 coordinates). The parent's sums run over its own coordinates; the child's higher
   coordinates are fixed (the mixed point). Each kind's `M̃` is read at its own coordinates only
   (`evalMT4`, and `evalMS4` through `ptOf`): the constant extension. So an `N2` child's dummy 23rd E2
   challenge (in `r̄*_x[22]`) is harmless and needs no zeroing; the KAT covers `N4 ← N2`, `N2 ← N4`,
   `N2 ← N8`.
3. **`W*` of another kind.** The op set has one `evalM`; `implN4F ν` evaluates kind `ν`. The second
   call is tagged by its row point's length (24 = 23 coordinates + `kindElem*`), so no `Op` changes.

## 4. Build, KATs, measurements

**Build.** At HEAD `21ade15`, `lake build FR Solution FRSoundness4TailShift FRSoundness4XCtrl
FRNodeSound4Ctrl` is green with exactly the 7 declarations of §5 sorried in the build tree
(`logs/RSV/scan/`, the last `build-*.log`). At `e14db30` the same 7, nothing else
(`logs/RSV/scan/run2/`). All this track's modules build without `sorry`.

**Axioms** (`logs/RSV/axioms.log`, `fr-build-RSV/ax/AxRSV.lean`): 40 touched theorems; `propext`,
`Classical.choice`, `Quot.sound` or fewer; no `sorryAx`.

**Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 377
files, 0 findings (`logs/RSV/source-rule.log`).

**CPU-s per touched module** (sequential, `lean -DElab.async=false --profile`, one core, load ≈ 4;
CPU = user + system, so ≈ 4 s of import each; `logs/RSV/profile-*.log`, `profile-summary.txt`):

| Module | CPU-s | type checking | A2″ |
|---|---|---|---|
| `FRShape4` | 17.2 | 7.37 s | 21.1 |
| `FRVIRFinals4` | 27.0 | 1.64 s | 26.4 |
| `FRVIR4At` | 12.7 | 0.64 s | 13.7 |
| `FRVIR4Uni` | 9.3 | 0.12 s | 12.0 |
| `FRVerifierC4` | 6.5 | 0.02 s | — |
| `FRVerifierImplNode4F` | 11.4 | 1.25 s | — |
| `FRX4Prog` | 10.1 | 0.44 s | 12.3 |
| `FRX4Ext` | 12.4 | 1.33 s | 15.5 |
| `FRNodeLayout4` | 16.4 | 9.89 s | 16.4 |
| `FRNodeKinds4` | 18.4 | 2.30 s | 18.6 |
| `FRNodeCircuit4` | 11.3 | 1.03 s | — |
| `FRVIRTpl4Bridge` | 6.6 | 0.09 s | 7.2 |
| `FRVerifierImplNode4T` | 12.1 | 1.51 s | 13.0 |
| `FRNodeRows4Hint` | 6.6 | 0.00 s | 6.1 |
| **total** | **178.0** | | |

(The three re-profiled on the final tree, `21ade15` + this track; the others at `e14db30` + this track:
their sources did not change since.)

**The reserve KAT** (`probe/RsvKat.lean`; `logs/RSV/rsvkat-1.log`, re-run identical after `rsvRel`
and `evalMPair`: `rsvkat-3.log`; 34 s). Full V runs of `progNode κP` op by op under a consistent random
oracle and a toy op implementation: `evalM` is the MLE of 48 random sparse entries per node kind,
dispatched exactly as `NI4F.evalMN4`. π is zero except the child claim (honest `a*, b*, c*` at a
random point) and the E2/E4 round messages, which are the honest prover's for the child terms,
written round by round in Fiat–Shamir order; `m̂*` is honest at the mixed point. The zero witness makes
the own terms vanish (checked: E4's own final value is `0`).

| Parent ← child | Reserve asserts (ii′, iii′, iv′) failing | Own asserts | Zero asserts | E-phase round asserts failing |
|---|---|---|---|---|
| (+) N4 ← N4 / N2 / N8, honest | none | none | none | 0 |
| (+) N2 ← N2 / N4 / N8, honest | none | none | none | 0 |
| (−) N4 ← N4, `m̂* + 1` | (ii′), (iii′) | none | none | 0 |
| (−) N2 ← N8, `m̂* + 1` | (ii′), (iii′) | none | none | 0 |
| (−) N4 ← N4 / N2, wrong child point (`r̄*_x[0] + 1`, the prover honest at it) | (ii′) | none | none | 0 |
| (−) N2 ← N4, wrong child point | (ii′) | none | none | 0 |
| (+) N8, child fields zero (gated off) | none (gated) | none | none | 0 |
| (−) N8, one nonzero byte in `fLrEnd[48…)` | none (gated) | none | `fLrEnd`'s | 0 |

In every case the other 874 failing ops are the zero proof's PIOP checks (Z, Lc, Sh, RS, Pf, caps),
identical across cases. E2's rounds have no per-round assert (degree 3: `c₃` is derived), so a wrong
point surfaces at (ii′), as the sumcheck says. The segment group's finals are unchanged (`rsvOps =
false`; `fsummary`: 151,226 ops as before).

**Dumps** (`logs/RSV/dump/`, `SHA256SUMS`; `logs/RSV/dump.sh`): `ops-{L30,L31,L32,N2,N4,N8}.txt`,
`group-{N,S}.txt`, `items.json` (8,783 items; `Lrend` absorb `len` 880, `Eend` 112), `summary.txt`
(field offsets), `fsummary.txt`, `last.txt`, `capkat.txt` (A2″'s cap-check KAT, PASS: honest
accepted, `A_0 + 1`, `D_100` and both attack orders rejected). **Node dumps** (`logs/RSV/nodedump/`,
`SHA256SUMS`): `nodedump4`, `protodump`, `planform4`; **plan-form KAT PASS** (`logs/RSV/planform-kat.log`:
644,900 / 636,693 rows rebuilt, 0 differ). These node dumps are at `e14db30` + this track (before B2′'s
layout); see §8 for the re-run on `21ade15`.

**V(N4), interim** (`vtime4 21 n4f`, core 29, `logs/RSV/vtime4-2.log`, `vtime4-3.log`; A2″'s binary
as "before", run alternately on the same core):

| | best (a / b) | median (a / b) |
|---|---|---|
| before (A2″'s V, `fr-build-A2pp`) | 413.0 / 409.8 ms | 428.6 / 430.8 ms |
| after, child tag absent or same kind (N4) | 416.5 / 410.8; 412.4 / 419.4 ms | 437.8 / 428.7; 458.5 / 439.4 ms |
| after, child of another kind (N2), two `evalMT4` | 1,018.9 / 1,028.7 ms | 1,062.3 / 1,068.4 ms |
| after, child of another kind (N2), `evalMPair` (one more `protoV4`) | 737.8 / 728.7 ms | 754.9 / 766.3 ms |

The same-kind child costs nothing measurable (the added ≈ 3k ops are K arithmetic). A child of another
kind costs one more prototype evaluation (`protoV4`, ≈ 300 ms here with the cap check untemplated):
see F2. (The first timing run, `vtime4.log`, showed 650 ms `evalMT4`: HEAD's stale hint made `inR`
false; regenerating it fixed that.)

## 5. For RSV-S: the red set and the statements that change

**Method.** A2″'s scan (`logs/RSV/scan/scan.sh`, `errdecls.py`, `sorry.py`), build tree only.

**The build failures (complete: with these 7 sorried the build is green, at `e14db30` and at
`21ade15`):**

| Module | Declaration | Why |
|---|---|---|
| `FRSoundness4R4Fin` | `flag_gFinE` | finE's op list is `gFinE0 … ++ rsvEOps …` under `rsvOps`; its flag is no longer `relE4` for a node with `rsv` |
| `FRSoundness4R4Fin` | `flag_gFinB'` | B′'s ops gain `rsvBOps`; `relB4`/`vStar4` lack `κ′^{11}·S` |
| `FRSoundness4Qry` | `noAsk_gFinE`, `noAsk_gFinB'`, `noAsk_gFinPf` | proof only: the new blocks ask nothing (`FRVIRFinals4.noAsk_rsvEOps`, `noAsk_rsvBOps`; `gFinPf`'s chain is `gCellsOpsK`) |
| `FRSoundness4R4FrE` | `fsMsgs4_ends` | false: the messages at 213 and 273 are 880 and 112 bytes |
| `FRSoundness4R4PfFlag` | `gFinPf_reloc` | false: `gFinPfR` lacks the second cell chain and the `keep rsv` |

**Statements that are false but compile behind those** (from the dependency graph):
- `FRSoundness4R4Fin.relE4`, `relB4`, `vStar4` (the definitions to restate), and through them
  `FRSoundness4R4FrE.relE4_of_accept`, `e_end4`, `not_rejEndE4_node`, `e_in4`, `not_rejInE4_node`,
  `e_fin4`, `not_rejFinE4_node`; `FRSoundness4R4FrRS.relE4_of_fields` (`e_bind4` stays true: E4 end
  is unchanged); `FRSoundness4R4Start.start4_of_fields`, `start4_node`.
- `FRSoundness4R4PfFlag.gFinPfR` and `relPf4`, and `FRSoundness4R4PfFin.relPf4_of_fields`,
  `fin4_of_fields`, `hz_of_fields` (the weight gains the 52 cells' `κ′^{11+i}·eq(c_i, ρ)` under `rsv`).
- `FRSoundness4R4FrE.vEnd_lr4`, `lr_end4` and every reader of `fsMsgs4_ends` (they read the first 48
  bytes of the two messages: still true, the lengths in the statement are not).
- Controls `FRSoundness4R4FrCtrl.relE4_fin3P`, `FRSoundness4R4FinCtrl.relB4_fin3P` stay true (`fin3P`
  has the reserve off).

**The S-C/S-G and T4/P4b statements that change** (P4b's names, `FRSoundness4P4bNames`; positions
unchanged: E1 after 214, E2 227…, Eend 273, E3 274, E4 275…, E4end 325, B′ after RS1):
1. **E2 is a zerocheck plus a linear claim.** `ZCwE4`, `D3E4`, `EndBadE4` and `RejEndE4`
   (`RejEndG (e2R κ) 214 227 23`): on `rsv` kinds the summed table is
   `eq(τ, x)(Az·Bz − Cz)(x) + η·eq(r̄*_x[<e2R], x)·(M̃*_η(x ‖ hi, r̄*_y) − v*)`, `η = coordAt es 214 23`,
   `r̄*`, `v*` from the Lrend message (213, bytes 48…880), `M* = entMat (srcE κ*)`, `κ*` the kind of
   `kindElem*`. E1's doom row (the multilinear zero test, `hfin_ml` in `FRSoundness4TailStep`) becomes
   `(e2 + 3)/2^128`: `η` adds one coordinate of the same Schwartz–Zippel argument.
2. **`truthE` gains `truthChild`.** The node's statement gains: the child claim of its own proof is
   true, `(a*, b*, c*) = M̃_{κ*}(r̄*_x, r̄*_y)` (the MLE of `nodeIRows4 κ*`, `ptOf` at `κ*`'s
   coordinates). `nE4` (the RowsBad doom) stays; a new doom `ChildBad4 := ¬ truthChild` joins E1's
   escape (the `η·D` term).
3. **E3's batch goes from 6 to 9 claims.** `c4E4` gains `+ κ_E⁴·m̂*` (`readF (msgAt es 273) 48`);
   `wEb4` gains `+ κ_E⁴·eq(r̄*_y[<e4R], y)·W*(y)`, `W*(y) = M̃*_η(r_E2 ‖ hi_x, y ‖ hi_y)`; `BatBadE4`
   (E3's doom) is the batch of `â, b̂, ĉ, v_L` (6 field values counted as A2′ did) plus `m̂*` and its two
   η-components: `8/2^128`. `D2Eb4`, `RejInE4`, `RejFinE4` read the new `c4E4`/`wEb4`.
4. **B′ and finPf**: `vStar4` gains `κ′^{11}·Σ_i κ′^i v_i` under `rsv`; P4b's `PubOK4`/`single_B4`
   gains the second cell family `rsvCells κ` (`hcells4P4b` for the 9 stays); `FRNodeCircuit4.StmtN4`
   gains `PubCellsR4 κ w (childVals π)`.
5. **εR is unchanged** (both rows stay below the per-query `2^-120.36`).

**For A3′'s restated modules** (`FRSoundness4TailCap`, `TailD`/`TailC`/`TailLig`, `FRSoundness4R4Cap`):
none of their declarations breaks. `R4Cap.capChk4_of_fields` reads `capChkOps`' op list, which B2′'s
hoist leaves unchanged (`aO`, `cO` are `let`s of the same values); the reserve changes no phase index,
so `phStart4 52 … 55` (482 … 485), `fsItems4` and `TailC.tailCls_check` stand.

**The node chain: how `Gap4.imp`'s three `evalM` registers are discharged.** For a parent `P` of kind
`κ` with `hasPrev`, slot 0 replays `V(C)` of the previous node `C`. Its own `evalM` op outputs three
import registers (M-relative cells 116,490…116,492 of prototype 0, `rsvRel[48..51)`), at the point of
`C`'s E2 and E4 challenges (registers whose cells are `rsvRel[0..48)`), for the kind whose element sits
in cell `rsvRel[51]` (the seed's `piElem 0 0`, tied to the selector by the seed's assert).
1. `PubCellsR4 κ w v` (from B′/finPf's point claims on `P`'s own `f`): those 52 cells hold `P`'s
   `fLrEnd` values `v = r̄*_x ‖ r̄*_y ‖ a* ‖ b* ‖ c* ‖ kindElem*`.
2. `truthChild` of `P` (from `P`'s E-phase, item 2): `(a*, b*, c*) = M̃_{κ*}(r̄*_x, r̄*_y)` with `κ*`
   decoded from `kindElem*`.
3. So the three registers equal `evalMS4 κ_C` at `C`'s own E2/E4 point (constant extension: an `N2`
   child's 23rd coordinate is read by no `M̃_{N2}`), which is `SlotImp`'s `evalM` fact at
   `base κ_C`, `evalMN4_eq` with an untagged point. `R` is not needed for them.
**Not discharged (F1)**: when `C` itself has a previous node of another kind, `V(C)`'s second (tagged)
`evalM` is a further import (three more cells) that no claim of `P` covers.

## 6. For P2 (`prover/`)

- **The format.** `|π| = 876,176`; field offsets `logs/RSV/dump/summary.txt` (`fLrEnd` at 6,464, 880
  bytes; `fEEnd` at 9,680, 112 bytes; every field after 8 moves by 832, after 10 by 896).
  `fLrEnd = â_L ‖ b̂_L ‖ ĉ_L ‖ r̄*_x (23 × 16) ‖ r̄*_y (25 × 16) ‖ a* ‖ b* ‖ c* ‖ kindElem*`; for an `N2`
  child, `r̄*_x[22]` and `r̄*_y[24]` are its dummy rounds' challenges, copied as they are.
  `fEEnd = â_M ‖ b̂_M ‖ ĉ_M ‖ m̂* ‖ 0^48`. `N8` writes zeros in both child parts.
- **E2** (decision 1): the summand is `eq(τ,x)(Az·Bz − Cz)(x) + η·eq(r̄*_x[<n], x)·(M*_η(x ‖ hi, r̄*_y)
  − v*)`, claim `0`, `n` the node's own E2 rounds (`N2` 22: the 23rd round stays a zero dummy). `η` is
  E1's 24th coordinate. `m̂* = M*_η(r_E2 ‖ hi_x, r̄*_y)`.
- **E4**: claim `+ κ_E⁴ m̂*`, summand `+ κ_E⁴·eq(r̄*_y[<n′], y)·M*_η(r_E2 ‖ hi_x, y ‖ hi_y)`.
- The KAT's honest prover for the child terms (`RsvKat.roundPoly`) is a reference for both.
- **The stream** is `64 · 24,234`; `aggB k = 1 + k · 1,550,975`; `hUsed` 74,007 / 122,481 / 195,192.

## 7. Findings for the orchestrator

- **F1 (major): the reserve does not close across kind changes.** `V(child)` replays the child's own
  finE, whose `W*` needs `M̃` of the grandchild's kind. If that kind differs from the child's, the
  value is a second `evalM` import in the parent's circuit, and the 52 cells (one claim on one kind)
  do not cover it; the imports grow by one claim per level unless they are bounded. Kind changes are
  normal (`N8 → N4 → N2 …`; `N2` is 86 % of steps). A closed form, for decision: every node's claim
  is one linear claim on the **kind-stacked** matrix, `Σ_{κ,m} s_{κ,m}·M̃_{κ,m}(p) = X`, with the 9
  coefficients `s` and `X` public; V's single tagged `evalM` returns `Σ s′·M̃(p)` for its own `s′`
  (own kind's `(f̂, κ_E f̂, κ_E² f̂)` plus `κ_E⁴·eq·s_child`), evaluated with one `protoV4`. That is
  48 + 9 + 1 = 58 cells and a different `fLrEnd` (976 bytes, not whole blocks: needs a pad). The same
  closure for an `N2` parent of a larger child needs every node's E-phase at 23/25 coordinates, or the
  mixed point carried into the claim. Neither is in this track; the spec's format is implemented.
- **F2: the other-kind child costs one more `protoV4`** (≈ 300 ms now, ≈ half `evalMT4` after
  B2′'s templates). Removing it needs the own call and the tagged call merged (one call returning
  `own_κE` and `W*_η`, with `κ_E`, `η` in the tag), which changes what the 3 public `evalM` cells mean.
- **F3: files in the worktree that are not this track's.** `FR.lean` differs from HEAD (it lacks
  B2′'s `import FRNodeRows4ArenaRows`), and `FRVIRTplBuild`, `FRVIRTplExt`, `FRVIRTplPlan`,
  `FRVIRTplSet` are modified (B2″'s journal is in `stages/`). This track changed none of them (its 13
  modules are §1's; my attempt to restore `FR.lean` to HEAD was refused by the sandbox, so it is left
  as found). Commit only §1's modules for RSV-V.

## 8. Re-run on HEAD `21ade15` (B2′), and the orchestrator's two requests

- **B2′'s hoist** in `capChkOps` (`let aO`, `let cO`, `macAOps aO cO k …`) is applied verbatim
  (`logs/B2p/FRVIRFinals4-hoist.diff`); the op list is unchanged, and `FRSoundness4R4Cap` builds.
- **`FRNodeRows4Hint`** regenerated on `21ade15` + this track (`laydump4`, `logs/RSV/laydump4-3.log`;
  `logs/B2p/mkhint.py`): `plan4t init` → `inR true`, 5.1 s, 504 MB (`logs/RSV/plan4t-init-2.log`).
- **Scan** (`logs/RSV/scan/`, rounds 1–4): the same 7 declarations, nothing else; green at 2,591 jobs.
- **The 52 cells are unchanged** under B2′'s cell layout (`logs/RSV/nodedump2/`, same `rsvRel`).
- **Plan-form KAT PASS** (`logs/RSV/planform-kat-2.log`: 649,915 / 641,628 rows, 0 differ); reserve KAT
  identical (`rsvkat-4.log`); IR dumps and A2″'s cap-check KAT regenerated (`logs/RSV/dump/`: PASS).
- **V(N4), interim, after B2′** (`logs/RSV/vtime4-4.log`; "before" is B2′'s own binary,
  `fr-build-B2p`, at `21ade15` without this track; core 29, load ≈ 4–5):

  | | best (a / b) | median (a / b) |
  |---|---|---|
  | before (B2′) | 276.5 / 272.4 ms | 294.2 / 286.0 ms |
  | after, no tag / same-kind child (N4) | 273.9 / 274.8; 274.8 / 273.2 ms | 298.5 / 288.7; 292.2 / 283.4 ms |
  | after, child of another kind (N2) | 471.7 / 462.6 ms | 506.2 / 488.2 ms |

  The same-kind child is free; another kind's child costs ≈ +190 ms (one more `protoV4` plus the two
  kinds' slot sums; `evalMT4 N4` is ≈ 150 ms now): F2.
