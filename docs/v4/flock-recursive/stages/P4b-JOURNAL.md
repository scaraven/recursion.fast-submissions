# P4b JOURNAL: the soundness front's Lr, E (with O1), RS, B′, W0 at revision 4.1

- Base: HEAD `7e14be6` (branch `v4/flock-recursive`). Build tree `logs/fr-build-P4b` (a copy of
  `fr-build-SG13` with its `.lake`; `snap.sh` + `MINE.txt`; `logs/org20`). Logs `logs/P4b/`.
- `lake build FR` on HEAD in the new tree: green, 2,428 jobs (`logs/P4b/build-0.log`).
- Every lean/lake command runs in the 16G scope under `timeout`. No sub-agents. Nothing committed.
  The worktree's modified `FRVIR*`/`FRVIRTpl*` files are S-E13's; `snap.sh` builds HEAD's text.

## 0. Decisions (written before any proof)

### 0.1 What the 3.x unit depends on, and what it does not

- The round dooms `D3`, `D2`, `ans3`, `Wrong2/3`, `Chk2`, `clR`, `clR2` read the kind only through
  `nr (kindOf es)`. **With a constant `nr := fun _ => n` they are kind-free**, so the whole round
  machinery (`D3_single`, `D2_single`, `D2_append_iff`, `wrong2_congr`, …) is reused as is, with no
  copy. The kind enters the Rev4 dooms through one gate: `OnNode P L es := ∃ κ, kindOfC es = .node κ
  ∧ P κ L es`, where `P κ` is the unit at node kind `κ`'s fixed dims.
- The 3.x Rows unit (`FRSoundnessRows`) is tied to 3.x in three places only: `zC` (3.x `fF` at
  `kindOf`), the gate `on (kindOf es)`, and `Same`/`Reads` (3.x `wordK`, `capPos`). Its end absorb
  sits at `b2 + 2a`, i.e. it assumes slots = real rounds. At Rev4 the slots are `seq4`'s (Lr 17,
  E2 23, E4 25) and a node kind's real rounds can be fewer (`N2`: 16, 22, 24), so the generic unit
  takes **both** the real count `a` and the slot count `A` (end absorb at `b2 + 2A`).
- `tauS`, `rxs`, `vEnd`, `kapB`, `c4`, `clR`, `clR2`, `rchs2` are position-generic and kind-free:
  reused (`vEnd A b2`, `kapB A b2`, `c4 A b2` with the slot count).

### 0.2 The generalisation (new modules; 3.x is an instance)

- **Entries source** (`ESrc`: the `A`, `B`, `C` entries `Eval.Entries`). The matrices are
  `entMat E a nc x y := Eval.entry E x y`. 3.x's `rowMat sel rows` is `entMat (entriesOf sel rows)`
  by `rfl` (`ESrc.ofRows`). **O1**: `ESrc.ofIRows rows` is `TEval.entriesI .a/.b/.c rows` over
  indexed rows, as `evalMS` reads `nodeIRows (planOf fin)`; `truthEI`/`sat_entMat_iffI` need the
  row indices distinct (`RowsFitI`: indices `Nodup` and `< 2^a`, cells `< 2^nc`).
- **What the front reads** (`Src`): an abstract `Same` relation `Sm` (laws: `agree`, `mono`,
  `ofAgree`) and `f⁽⁰⁾` `fz` (law: `fz_same` from position 3). 3.x: `Same`, `fF (kindOf es)`
  (`src3`). Rev4: T4's `Same`/`fF` at `CKind`'s ladder (not mine: T4 ports the Ligerito words), so
  every P4b statement is parametric in `Src`. `ReadsS R p P` is 3.x's `Reads` at `R.Sm`
  (`reads_iff_readsS`: `Iff.rfl` at `src3`).
- Node data that is S-E's (F3) is a parameter: the M rows' and L rows' entries per node kind
  (`srcE srcL : NodeKind → ESrc`), the node's public cells, the kind factor's indicators.

### 0.3 Positions (`phStart4_shift`) for P4b's phases

| phase | 3.x | Rev4 | notes |
|---|---|---|---|
| Lr1 (zerocheck, multi-squeeze after `s0`) | `s0 = 169`, 8 squeezes | `s0 = 169`, 9 squeezes (170 … 178) | `⌈17/2⌉` |
| Lr2 rounds | `b2 = 178`, 15 | `b2 = 179`, 17 slots (real `logL`: 16/17/17) | |
| Lrend / Lr3 (`κ_L`) | 208 / 209 | 213 / 214 | |
| E1 | `s0 = 209`, 11 | `s0 = 214`, 12 (215 … 226) | |
| E2 rounds | `b2 = 221`, 21 | `b2 = 227`, 23 slots (real `logM`: 22/23/23) | |
| Eend / E3 (`κ_E`) | 263 / 264 | 273 / 274 | |
| E4 rounds | `b4 = 265`, 23 | `b4 = 275`, 25 slots (real `m − 7`: 24/25/25) | |
| E4end | 311 | 325 | |
| RS0 / RS1 (4 squeezes) / B′ / P1.0 | 312 / 313 / 317 / 318 | 326 / 327 / 331 / 332 | |

Cells: Lr's and E's `nc = m − 7` (24/25/25), as `σ` (`coords_eq`).

### 0.4 The names R4 needs (fixed in `FRSoundness4P4bNames`, namespace `FR.Snd.P4b`)

All take `R : Src` only where they read `f⁽⁰⁾`; the checks (`Rej*`) read only the log.

| name | meaning (Rev4) | 3.x |
|---|---|---|
| `RejEndLr4` | node, `214 ≤ |es|`, Lr2's claim after `lrR κ` rounds `≠ eq(τ_Lr, r_Lr)·(â b̂ + ĉ)` (Lrend at 213) | `RejEnd 15 lrOn 169 178` |
| `RejEndE4` | the same for E2 (`b2 = 227`, Eend at 273, `e2R κ` rounds) | `RejEnd 21 lrOn 209 221` |
| `RejInE4` | node, some E4 round `l < ncR κ` absorbed and its `g(0)+g(1) ≠` claim | `RejInE4` |
| `RejFinE4 srcE srcL` | node, `326 ≤ |es|`, E4's claim after `ncR κ` rounds `≠ W(r′)·α_E` | `RejE4` |
| `RejRS4 ok` | `327 ≤ |es|`, some claim's binding fails at the slices' value `α_j` | `RejRS` |
| `okRS4 oZ oLc oSh` | RS0's bindings; E's is `okE4` (E4end's value, 325) | `okF` |

Dooms (with `R`, `srcE`, `srcL`): `RowsBadLr4`/`ZCwLr4`/`D3Lr4`/`EndBadLr4`/`BatBadLr4`,
`nE4` (O1) /`ZCwE4`/`D3E4`/`EndBadE4`, `BatBadE4`, `D4E4`, `PendE4`; RS0: `PendBad4`, `DPend4`,
`DRS0_4` (`FRSoundness4P4bRS`). (Final names; see the log for the renames.)

## 1. Log

- **Names first** (`FRSoundness4P4bNames`, 328 lines): built green on the first try (4.3 s). The
  names of §0.4 are final except the renames forced by 3.x's names in `FR.Snd` (resolution in a
  nested namespace collects every level, so a short name shared with `FR.Snd` would be ambiguous):
  `RejE4` → **`RejFinE4`**, `wE4` → `wEb4`, `T4E` → `TEb4`, `rE4` → `rPt4`, `D2E` → `D2Eb4`, and a `4`
  suffix on the others (`RejEndLr4`, `RejEndE4`, `RejInE4`, `RejRS4`, `okRS4`, `okE4`, `nE4`, …).
  `FSrc` (not `Src`: S-E13's untracked `FRVIRTplBuild` has an `inductive Src`).
- **Generic unit** (`FRSoundness4P4bRows`): every 3.x proof ported with `R.Sm`/`R.fz` in place of
  `Same`/`fF (kindOf ·)`; the rounds' dooms are 3.x's `D3` with `nr := fun _ => a` (no copy of
  `StepB`/`StepE`). O1's indexed-row lemma needs **distinct indices** (`RowsFitI`), unlike 3.x's row
  list, where the index is the position.
- **Rev4 E** (`FRSoundness4P4bE`): one instance-mismatch trap. `onNode_card` instantiated at an
  explicit `P := fun κ L es => A ∨ B` makes the classical `DecidablePred` instance
  `propDecidable ((fun …) κ L es)`, while the per-kind lemma's is `instDecidableOr …`; unifying them
  hit `maxRecDepth`. Fix: bridge with `card_filter_imp fun d hd => hd` (instances are implicit
  there). `trueSum_TEb4` is algebra over the symbolic `ncR κ` (no `cases κ` near a `trueSum`).
- T4 (parallel) has `FR.Snd.T4.RejOK` over `fsItems4`/`G.IsChain`/`fsRnd4`. Not imported (unfinished
  module); P4b's checks are `RejLog4` (mono, `sq` at `fsItems4`, independent of `L`), from which
  T4's `RejOK.stab` is immediate (a log-only check reads the same under any charging log).
- **RS0** (`FRSoundness4P4bRS`): `PendBad4`, `DPend4`, `DRS0_4`, `habs_RS0_4`, `rejRS4_log`,
  `trueL4_three`, `pendE4_pendBad4`, `rs1_count4`. Far and the public cells are parameters `F0`, `Pub`
  (T4's and S-E's); the kind factor is `kf` (S-E's indicators at revision 4.1).
- Final: `lake build FR` + the four modules green (2,432 jobs), axioms (191 names) within the three,
  source rule 223 files 0 findings. Stopped here (context); RS1's frame, B′, W0, DF/Obl/Stab and
  the instantiation are the handover (RESULT §6).
