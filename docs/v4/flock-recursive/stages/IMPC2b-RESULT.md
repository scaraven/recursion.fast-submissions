# IMPC2b (track L-circ): RESULT — the bits' run proofs, the statement reads, `Gaps4` from `SlotRunB`

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `91e0d61`; re-snapshotted onto
**`407260d`** (REPF) at the orchestrator's request. Build tree `logs/fr-build-IMPC2b` (copy of
`fr-build-IMPC2`, `snap.sh` = HEAD text + my modules as symlinks, then `patch.py` (IMPC2's, unchanged) and
`patch2.py` (mine, §6)). Logs `logs/IMPC2b/`; journal `IMPC2b-JOURNAL.md`. Every lake/lean/probe ran in a 16 GB
scope under `timeout`. No sub-agents, nothing committed, no `sorry`.

## 0. Summary

| Item | State |
|---|---|
| `execA_idx` (register provenance for `idx`/`shrN`/answers/digests/bytes/constants) | **Done**: `execA_ri` (generic over the op list, no program evaluated) |
| bit order of `F.ofBytes`, `natLE`, `idxOfF` | **Done**: `F.bit_ofBytes`, `testBit_natLE`, `bit_dlo`/`bit_dhi`, `testBit_idxOfF`, `F.eq_of_bit` |
| `StmtBits` / `PosBits` | **Done, from the rows**: `stmtBits_of_glob`, `posBits_of_glob` (decomposition rows at the seed's ask: `first_ask`, `seed_rows`) |
| the `bitOf` import conjunct | **Done**: `impA_bits` (every `bitOf` whose next op is a `selectHalf` on it; the probe: all of them) |
| the `bits n` aux conjunct | **Done**: `aux_bits` + `xof_bits` (only a `tensorW` carries `bits`) |
| `flag_stmt` (tag byte + zero tail) | **Done**: `flag_stmt` from `StmtBits` (+ IMPC's zero pins kept) |
| `SlotRunB`, the reduction | **Done**: `slotRunA_of_bits` |
| `atImp_bitR`, statement reads | **Done** as a separate generator `bitTGS` (`atImp_bitS`); folded (phase 2a) |
| `atImp_bitR`, **siblings** | **Not done** (§5): needs the kind tie (`trM4` = selector's `m`) and the sibling-level `PosBits`; `bitTGR`'s siblings stay unfolded |
| final discharge | **`gaps4_of_runS`**: `Sub4.Gaps4` from `SlotRunB` at `rtC1c` over `withBitsS askAq` (composes with REPF: `RepOk`, the replay fold and the template fold are theorems) |
| honest completeness (probe `bitstat2`) | **0 failing rows** in `bitTGB`, `bitTGS` and the whole folded `askTG`, both prototypes; template rows p0 **114,320** / p1 **135,997** ≤ `arR2N` 180,560 |
| Build | `lake build FR Solution FRSubmission4Fin FRNodeRun4BT bitstat2`: **green, 5,252 jobs, 0 `sorry`** (`build-final.log`), with `patch.py` + `patch2.py` |
| Axioms / source rule | 36 declarations incl. `certified`, each ⊆ {propext, Classical.choice, Quot.sound} (`axioms.log`); 462 files, 0 findings (`source-rule.log`) |

## 1. What remains (exact), per prototype, after `gaps4_of_runS`

`SlotRunB rt A impl π ι inp tr w` (`FRNodeRun4BF`) is `SlotRunA` with three filters:

```lean
∀ s, execA impl ι inp (protoProg π).ops St.init tr = some (s, []) →
  (∀ a ∈ (protoCS π).aux, isBitsA a = false → <aux fact>) ∧                    -- felems only
  (∀ i ∈ impBP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)) ∧          -- impAX less the bitOf imports
  (∀ p ∈ (protoCS π).fors, zPin (pvP π) p = false → stFlag (bitTabP π) p = false → <flag>)
```

What those lists hold on the real compile (`bitstat2.log`, at `rtC1c`, `withBitsS askAq`):

| conjunct | p0 | p1 | discharge route |
|---|---|---|---|
| aux, not `bits` | 871 (`felems`, the `dotKF` column words) | 871 | IMPC's `colTG` (`aux_col`), not folded (orchestrator: V / row cap) |
| residual imports `impBP` | **7,426**: all sibling reads `piDigest fSibs` | **7,431**: 7,426 siblings + **5** replay ops `rsWeight, evalL, evalM, shiftTarget, targetS` | siblings: `bitTGR`'s sibling rows + `atImp_sib` (§5). The 5 p1 ops: not covered by `rtC1c 1` (REPF's template covers only `linkWAll` in the segment prototype) |
| foreign flags, not `zPin`/`stFlag` | **0** (of 14) | **0** (of 79) | — |

So `Gaps4` is **not yet provable from the rows alone**. Two further gaps remain even after those classes:

1. **The emptiness of the residual lists is a fact about the program** (the probe), not a kernel theorem.
   `SlotRunB`'s flag conjunct is vacuous on the compile, but stating so needs a decision over the 155k-op
   program. The route that avoids it is a *closure* generator: at every op where the compile records a
   foreign flag / residual import / aux entry that no class handles, emit `failRT` (so the residual
   conjuncts become vacuous by `failRT_not`). Not built.
2. The siblings (§5) and p1's 5 replay ops.

## 2. The theorems (modules, `loc.py`: total / code / thm, `loc.txt`)

| module | lines | content |
|---|---|---|
| `FRNodeRun4BL` (new) | 407 / 321 / 26 | bit order (`testBit_natLE`, `F.bit_ofBytes`, `bit_dlo`/`bit_dhi`, `testBit_idxOfF`, `F.eq_of_bit`); `SrcV`, `stBit`, **`StmtBits`**, **`PosBits`**, **`SrcOk`**; `RIV`, **`execA_ri`**; **`srcOk_of`**; **`selRows_ev`** |
| `FRNodeRun4BR` (new) | 334 / 274 / 12 | `compileFromX_slot_lt`; `bitNx`, `impBX`, **`impA_bits`**; **`xof_bits`**, `auxBRows_mem`, **`aux_bits`**; **`stFlag`**, **`flag_stmt`** |
| `FRNodeRun4BS` (new) | 391 / 340 / 16 | **`first_ask`**, **`seed_rows`**; **`stmtBits_of_glob`**; `ansCell_some`, `cls_ex`, **`ans_half`**, `mkTab_ans`, **`posBits_of_glob`** |
| `FRNodeRun4BF` (new) | 241 / 197 / 7 | `xofA_aux`; **`SlotRunB`**, **`slotRunA_of_bits`**; `bitsB_rows`, `gap4Imp_of_bitsR` (fold over `withBitsB`, a hypothesis) |
| `FRNodeRun4BT` (new) | 275 / 226 / 9 | **`rdWin_ev`**, `stRd_rep`, **`atImp_bitS`**, `xofA_read`; `withBitsS`, **`askFold_bitsS`**, **`gap4Imp_of_bitsS`**, **`gap4Imp_rtC1cS`**, **`gaps4_of_runS`**; controls |
| `FRNodeRows4AskB` (edited) | 509 / 307 / 1 | guards (§3), `stCells`, `rdCells`/`rdOk`/`stRdRowsS`, `bitCovS`/`bitRowsS`/**`bitTGS`** |
| `FRNodeRows4AskBS` (edited) | 220 / 144 / 14 | `askFold_bitsB` removed; `Circ.akS` (clash fix) |

In words:

- **`execA_ri`**: on the answer-driven run, every register's `riAcc` entry describes its value on the
  final registers: `.ans k` → the trace's answer `k`; `.idx a b i` → `idxOfF (b ι) (rd (a ι)) (i ι)`;
  `.shr`, `.dig o` (`digestAt π o`), `.pf o len`, `.cb bs`.
- **`srcOk_of`**: with `StmtBits` and `PosBits`, every `bitSrc r h ι` holds bit `h` of register `r`.
- **`impA_bits`**: an induction along the compile's trail and the run together; a `bitOf r h` import whose
  next op is `selectHalf b _ _` with `b` its register: the next op's `bitRowsB` rows (`selRows`) make its
  cell the source, which holds bit `h` of `r` (`r < b` by the row guard).
- **`stmtBits_of_glob`**: each statement element row `A₁(e) = [k=0]·tag + Σ e_j·cell` with `PfCells` and
  Boolean cells: each cell is its message bit, the bits no cell takes (tail) are zero, byte `so` is the tag.
- **`posBits_of_glob`**: each answer half's rows (`ansRows`, the selected kind's class representative,
  `cls_ex`) with arena₁ = the trace's answer halves (`a1_slot`, `slot_ans'`): each `ansCell ι k j` holds bit
  `j` of `natLE` of answer `k`.
- **`atImp_bitS`**: an unaligned statement read's import slots are its window values (`rdWin_ev`).
- **`gaps4_of_runS`**: `(∀ vk κ w c₁ c₂ ch, StmtN4R … → ∀ v active, ∀ ι SelOk, SlotRunB (rtC1c π) (withBitsS askAq π) (implP implB …) π ι (slotIn …) (slotTr …) (slotAsg …)) → Sub4.Gaps4`.

## 3. Statement / definition changes (all)

| declaration | change | why |
|---|---|---|
| `FRNodeRows4AskB.riOf` | takes the register count `n`; `idx`/`shrN` recorded only on registers `< n`; `.cb` only for a byte constant equal at all three kinds | otherwise `bitSrc` could claim a source for a later register or another kind's constant (unsound in `srcOk_of`/`flag_stmt`) |
| `riAcc` | passes `acc.size` | — |
| `bitRowsB` (`bitOf` case) | also `r < b` | the run reads `r` before the `bitOf` |
| `auxBRows` | takes the register count; a `bits n` entry needs `r <` it and `n` cells, else `failRT` | the aux fact reads `regs.extract 0 m` |
| `ansRows` | `failRT` unless every cell `< arNb` | Boolean cells (`bit_slot`) |
| `idxSrc` (`.dig`) | also `i·b + h < 256` | `natLE` has 256 bits |
| `globRows` check | also `1 ≤ z` | the tag byte is not in the tail |
| `stElRow` | its cells named `stCells` (same value) | the proofs refer to them |
| new `bitTGS` (+ `bitCovS`, `bitRowsS`, `stRdRowsS`, `rdCells`, `rdOk`) | the statement-read half of `bitTGR` | foldable now (`atImp_bitS`) |
| `FRNodeRows4AskBS.askFold_bitsB` | **removed** | false once `askTG` folds `bitTGS` (row indices move); replacement `askFold_bitsS` |
| `FRNodeRows4AskBS.tplExt4_tw_imp` | `akS` → `Circ.akS` | REPF's `FRNodeRows4Defs` adds `FR.N4s.akS`, which shadows it: **HEAD's AskBS does not build at 407260d** (HEAD's FR does not import it) |

Honest rows unchanged by the guards: `bitstat2` gives 0 failing rows (§0). `bitTGB` rows p0 48,051 / p1 62,695
(= IMPC2's), `bitTGS` 6 / 8.

## 4. Kernel time (`lean -DElab.async=false --profile`, core 27, `profile-*.log`)

| module | type checking | tactics |
|---|---|---|
| `FRNodeRows4AskB` | 0.12 s | 0.00 s |
| `FRNodeRows4AskBS` | 0.10 s | 0.69 s |
| `FRNodeRun4BL` | 1.07 s | 2.95 s |
| `FRNodeRun4BR` | 0.67 s | 1.82 s |
| `FRNodeRun4BS` | 0.77 s | 1.45 s |
| `FRNodeRun4BF` | 0.21 s | 0.79 s |
| `FRNodeRun4BT` | 0.33 s | 0.91 s |

≈ 3.1 s new type checking (my five new modules), no declaration above 190 ms; nothing decided over a
table, the program or the format (the only `decide`s are the toy controls). None of it is on `certified`'s
path until `Gaps4` is routed through `gaps4_of_runS`.

## 5. Not done: the siblings (`atImp_bitR`'s other half)

`bitTGR`'s sibling rows (`b·(A₁(l) − A₁(r)) = sib − A₁(r)`, `gate(inactive)·sib = 0`) are not folded. Their
`ATImp` needs, at a covered `piDigest` in an `fSibs` part (`sibLoc o = (i, p, h, k)`):

1. π's bytes there = `sib4 seq4 (trM4 tr) i h (posOf4 … p) q_k` (`reassemble4_byte` + `ctb4_sibs`: exist);
2. **the kind tie**: `trM4 tr = (G ι).d.m` for the selected `ι`. Route: `kindRow_sel` (stream element 5 =
   `kConst G ι`) + `kind_byte`-style reading of the seed's byte 71 + `CKind.ofByte?` of `(G ι).byte`, for every
   active slot (the prev slot and sub-slots, as `gap4_of_rows`' `kindN`/`kindS` cases);
3. the position cell `posCell i p h` = bit `h` of `posOf4 … p` at that `m`: from `PosBits`
   (`ansCell ι k ((p % per)·logN + h) = posCell i p h` for `h < logN_ι`) + `testBit_idxOfF`, and `phAns` =
   the P2 answers `ansList` places (a bridge between `ansOf4`/`phAns` and `ansList`);
4. the node query's halves on arena₁ (`qElT k`, `+2`): ASK-T's `dig_entry`/`slot_qelem`.

Then fold `bitTGR` restricted to siblings (or `bitTGR` with `bitCovR` less the statement reads) as
`withBitsS … |>.addD`, and `SlotRunB`'s residual imports lose the 7,426 siblings.

## 6. The exact diffs to others' files (`logs/IMPC2b/others.diff`; tree: `patch.py` then `patch2.py`)

- **`patch.py`** (IMPC2's, applies unchanged at 407260d): `FRNodeRows4ArenaPlace` constants
  (`arNb` 16,384, `arR2N` 180,560, `arRb` 998,400), `askTG` folds `bitTGB`, `askTGI` restated,
  `FRNodeRun4AskT`'s `askFold_askT`/`gap4Imp_of_askT` deleted.
- **`patch2.py`**:
  1. `FRNodeRows4.askTG`: after the `bitTGB` fold, `|>.addD (bitTGS (same extension) π (same table))`.
  2. `FRNodeRows4RepF`: delete `gap4Imp_rtC1c` and `gaps4_of_runA` (they call the deleted
     `gap4Imp_of_askT`); replacements `FRNodeRun4BT.gap4Imp_rtC1cS` / `gaps4_of_runS`.
  3. `FRNodeRows4RepFCtrl.repRow0_ctl`: `arRb + arNb < N4s.repSegB` → `≤` (IMPC2's bit rows end exactly at
     `repSegB = 1,014,784`; `FRNodeRows4Fit.repConsts` allows it).
- `FR.lean`: `import FRNodeRun4BT` (pulls BF, BS, BR, BL, AskBS).
- Re-dump the plan form / MxKat / V(N4) / `plan4t init`: `askTG`'s rows changed (not measured here).

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `stFlag` | `stFlag_ctl`: tag check and zero tail | other tag, operand after the flag, a read off the tail |
| `bitNx` | `bitNx_ctl`: `bitOf` then `selectHalf` on it | another register, another next op |
| `riOf` guards | `riOf_ctl`: `idx` on an earlier register | on a later one; a kind-varying constant |
| the generators on the compile | `bitstat2`: 0 failing rows, `askTG` within `arR2N` | — |
| `selRows`, `addD` | IMPC2's `selRows_ctl`, `addD_ctl` | — |

## 8. Files

- New: `submissions/flock-recursive/lean/FRNodeRun4BL.lean`, `FRNodeRun4BR.lean`, `FRNodeRun4BS.lean`,
  `FRNodeRun4BF.lean`, `FRNodeRun4BT.lean`.
- Edited: `FRNodeRows4AskB.lean`, `FRNodeRows4AskBS.lean`.
- Docs: `docs/v4/flock-recursive/stages/IMPC2b-RESULT.md`, `IMPC2b-JOURNAL.md`.
- Tree (dev): `logs/fr-build-IMPC2b/patch2.py`, `probe/BitStat2.lean`, `ax/AxIMPC2b.lean`; logs in `logs/IMPC2b/`.
