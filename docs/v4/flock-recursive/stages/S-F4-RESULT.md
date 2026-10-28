# S-F4 RESULT: the finals over `Seq`, the segment's variable last block, `Vseg`/`Vnode`

- **Where:** worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive`, HEAD
  `47c5c6c` (S-0′). Pin `6d05d00`.
- **Build tree:** `logs/fr-build-SF4` (against `logs/org20`; HEAD snapshot plus the files below).
- **Logs:** `logs/S-F4/`. Journal: `S-F4-JOURNAL.md`.
- Nothing is committed.

## 1. What was built (loc: `logs/S-F4/loc.txt`, core `scripts/loc.py`)

| Module | code / total | Content |
|---|---|---|
| `FRVIRFinals4` (new) | 366 / 511 | `KV`, `FinP`, `kv3`, `fin3P`; the nine fields over `FinP` (`gFinZ`, `gFinLc`, `gFinSh` with `gShCore`/`gBndOps`/`gPadB`, `gFinLr`, `gFinRS`, `gFinE`, `gFinB'`, `gFinP` with `gFinPTop`, `gFinPf` with `gPfPts`, `gCellsOps`, `gLvsOps`, `padOps`); `finalsOf`; **`finalsOf_seq3`** (via `gFinX_3` per field, `phaseOffOf_seq3`); `reloc`, **`evalOp_reloc_seq3`**, `exec_reloc_seq3`, `opsOut_reloc`, `item_reloc`; `finOps4`, **`finOps4_seq3`**; controls. 26 theorems. |
| `FRSegTarget4` (new) | 149 / 238 | `lastAt`; `segRangeI`/`segRangeS`, `targetSSegI`/`targetSSegS`, **`targetSSeg_meets`**, **`range_cube`**; `shiftSegI`/`shiftSegS`, **`shiftSeg_meets`**, `shiftMle_cube`, **`shiftSeg_cube`**, **`shift_unmasked_link`**; `implSeg`, `specSeg`, **`implSeg_meets`**. 13 theorems. |
| `FRVerifierC4` (new) | 45 / 104 | `kvOf`, `segFinP`, `nodeFinP`, **`progSeg`**, **`progNode`**, **`VsegC`**, **`VnodeC`**, `VC4`; **`acc_eqC4`**, **`implSegC_meets`**, **`VC4_agg_extract`**; controls. |
| `FRVIR4` (edited) | 133 / 213 (+51 lines) | `lastOps`, `lastOuts`, `segPtOp`; `genPhase4`: a segment's `stmt` phase reads `L`, its Z2 `targetS` operand carries it. |
| `FRAgg` (edited) | 294 / 422 (+71 lines) | `SegSoundOn`, `SegKSOn`, **`segSoundOn_of_KS`**, **`VA_extract_on`**. `SegSound` and `VA_extract` unchanged. |
| `FR.lean` | +3 imports | `FRVIRFinals4`, `FRSegTarget4`, `FRVerifierC4`. |

No 3.x statement changed. No forbidden module was touched.

## 2. Build, kernel, checks

- **Build:** `lake build FR` is green, 2,419 jobs (`logs/S-F4/build-FR.log`).
- **Axioms:** 22 key theorems use only `propext`, `Classical.choice` and `Quot.sound` (`axioms.log`,
  `Axioms.lean`).
- **Source rule:** 195 files, 0 findings (`source-rule.log`). No `sorry`, no `native_decide`.
- **Sequential profiles** (one core, `-DElab.async=false`, `prof-*.log`):

| Module | wall | elaboration | kernel |
|---|---|---|---|
| FRVIRFinals4 | 54.9 s | 45.3 s | 0.55 s |
| FRSegTarget4 | 8.0 s | 0.1 s (tactics 0.4 s) | 0.20 s |
| FRVerifierC4 | 6.0 s | 0.04 s | 0.003 s |
| FRVIR4 | 14.8 s | 7.4 s | 0.78 s |
| FRAgg | 33.1 s | 0.2 s | 24.5 s (S-0′'s byte controls, unchanged) |

  FRVIRFinals4's elaboration is the `gFinX_3` `rfl`s (17.6 s, 12.7 s and 6.2 s for the three
  largest). It is a golf target: per-field `simp only` normal forms would be cheaper.
- **OOM found and fixed:** `simp only [Function.comp_apply, FR.targetS]` inside `targetSSeg_meets`
  (a goal over `Fin (2^(8 + 18))`) went past the 16 G cap. It was bisected under a 6 G cap with
  `lake env lean` and replaced by `rw`.

## 3. Items

### 3.1 The finals over `Seq` (`FRVIRFinals4`)

**Parameters (`FinP`):**
- `S : Seq`: rounds, coordinates, ladder `S.lv`, in-field phase offsets `phaseOffOf S`, final
  message `2^S.pf`.
- `kv : KV`: 3.x's KC tables `m`, `isNode`, `is32`, `rsPtIx`. In a revision-4 program these are
  constants (`kvOf`).
- The node's real counts `lrR`, `e2R`, `e4R` (3.x: 15, 21, 23).
- `finPf`'s second point family `mB` (3.x: 30). The first family is `S.mStar`.
- The node's public cells and their coordinates `nc` (3.x: `pfCells`, 23).
- `vn`: the variable last block.

**Specialisation:**
- **`finalsOf_seq3 : finalsOf fin3P = sfFinals finP finPf`.** This is an equality of the `Finals`
  structures, field by field (`gFinZ_3` … `gFinPf_3`).
- So at 3.x's parameters every flag lemma (`flag_finZ` … `flag_finPf`) applies unchanged, with the
  same relations.

**Addressing:**
- The fields keep 3.x's field-relative reads.
- `finOps4 P` relocates them to `S`'s format (`reloc S`: `piElem f o ↦ piElem 0 (fieldOffOf S f +
  o)` for `f < 19`, and likewise for `piField`, `piElemK`, `piDigest`, `piDigestAt`).
- At `seq3` the relocation changes no op's value (`evalOp_reloc_seq3`). Hence **`finOps4_seq3`**:
  `exec` of `finOps4 fin3P` equals `exec` of 3.x's finals ops.
- `reloc` preserves `Op.outs` and `Op.item?`, so registers and items are unchanged.

**Controls:**
- (+) `finalsOf_seq3`, `finOps4_seq3`.
- (−) `gOE4end_seq4`: E4 end moves inside the E field at `seq4`.
- (−) `reloc_seq4_moves`: E's field offset differs.
- (+) `finP_ctrl`: `N2`'s real counts are 16 / 22 / 24, and a segment's `m` is its own.

**Not done here:**
- `flag_fin*` restated over `FinP` (the relations at `seq4`'s sizes).
- The relations are 3.x's with the parameters substituted; the proofs are S-G12′'s migration (see §6).

### 3.2 The segment's variable last block (`FRVIR4`, `FRSegTarget4`, `gFinSh` with `vn`)

**Where `n` enters.**
- The segment's `stmt` phase runs `lastOps` (94 ops). They compute `n mod 2^24` from `stmt` bytes
  33–40 (`piDigest`, `idx … 24`), then its 18 bits (`bitOf`, `selectHalf` → F `0`/`1`), then the
  borrow chain `L = n − 1` in F (`L_k = n_k + c_k`, `c_{k+1} = (1 + n_k) c_k`).
- `stmt`'s outputs become `b :: zero :: L₀ … L₁₇`.
- Bits `≥ m − 14` of `L` are zero, since `n ≤ 2^(m−14)`; `V_A` checks `1 ≤ nᵢ ≤ cap`.
- Measured: `logs/S-F4/dump/last.txt`, nine values of `n` from 1 to `2^18`, all with `L = n − 1`.
- `n ≤ 2^(m−14)` blocks: the segment occupies `2^(m−14)` blocks, and `L` addresses one of them.

**What each weight does on blocks past `L` (blocks `y`, Boolean points):**

| Weight | Segment form | On the blocks | Theorem |
|---|---|---|---|
| Z2's `targetS` | `targetSLeaf(r) · Σ_{t ≤ L} eq(r_blk, t)`, with operand `r ‖ L` (37 entries: Z1's position coordinate, the `m − 14` block coordinates zero-padded to 18, `L`) | `E_chain` on `t ≤ L`, **0 past `L`**: a free block meets the homogeneous `(Az)(Bz) = z`, which the zero block satisfies | `targetSSeg_meets` (spec = `FRPubTarget.targetS` with the masked `E`), `range_cube` (`[u ≤ L]`), `segRangeI_eq` (prefix sums) |
| Sh's `E` (`w_out`) | `eq(τ, r)`, unmasked | `[y′ = y]` | `shiftSegS` |
| Sh's successor (`w_in`) | `shift(τ, r) + eq(τ, L) eq(r, L + 1)` (char 2; no term when `L + 1 = 2^18`) | **`[y′ = y + 1 ∧ y ≠ L]`**: the link `L → L + 1` is cut | `shiftSeg_meets`, `shiftSeg_cube`; (−) `shift_unmasked_link` (the unmasked weight is 1 there) |
| Sh's `E₀` | `eq(r, 0)` | block 0 | `shiftSegS` |
| Sh's target (`bnd[4…21]`) | `L`'s bits | `eq(τ, L) h̃ + κ_s s̃` | `gBndOps` with `vn`; `shiftTargetI` unchanged |
| `linkWAll` | leaf: `0⁸` | — | 3.x |
| Lc's walk, L3's `v`, claim 2's `rsWeight` | **unchanged**: every segment block is a chain block, `v = [v_chain, 0⁷]`, `β` gated to 1 | the matrix identity holds for every `z` | 3.x |
| RS claims, Ligerito | unchanged | `z` is committed whole | 3.x |

**The residual per block** is `Out(y) + [y ≠ L] In(y+1) + [y = L] h`:
- for `y < L`: the links;
- at `L`: `Out(L) = h`;
- past `L`: links among the free blocks, and the top block's `Out = 0`. The zero blocks meet these.

**Why the successor must be masked.** Without the mask the residual at `L` is
`Out(L) + In(L+1) + h`, so a nonzero `In(L + 1)` in a free block would move the end. P2′'s reading
in 13.3 ("shift tables unchanged") is unsound on the verifier's side. With the zero witness the
prover's messages are the same either way.

**Ops.**
- The verifier passes `L` to `shiftMask`, through the operand `τ ‖ L` (`gFinSh`'s extra `packFK`
  when `vn`). It selects `shiftMask`'s three outputs (`keep` with `act = true`).
- `implSeg impl₀` is `impl₀` with the segment's `targetS` (on the leaf kinds) and `shiftMask`.
  **`implSeg_meets`** follows from `impl₀.Meets spec₀`.

### 3.3 `Vseg`, `Vnode` (`FRVerifierC4`)

**Programs.**
- `progSeg κ = genSeg κ (finOps4 (segFinP κ))`.
- `progNode κ cells = genNode κ (finOps4 (nodeFinP κ cells))`.
- In both, `kvOf m node` gives constant tables, `finPf` uses the kind's own `m` family
  (`selA = false`, `mB = m`; padding `Π_{x ∈ sf[m−25..7)} (1 + x)`), and the node's real counts are
  `logL`, `logM`, `m − 7`.

**Verifiers.**
- `VsegC impl₀ κ vk c π = runIR (implSeg impl₀) (progSeg κ) ⟨vk, c, π⟩`.
- `VnodeC implN cells`: the node kind's ops `implN κ` (`evalM`, `evalL`, `targetS`, `linkWAll`,
  `shiftMask` from the node plan) stay parameters, as in 3.x, and so do its public cells.
- `VC4 = V4with VsegC VnodeC`.

**Theorems.**
- **`acc_eqC4`**: `acc_eq4` at `VC4`.
- **`implSegC_meets`**: `implC_meets`'s analogue, with 3.x's `implC`/`specC` as the base.
- **`VC4_agg_extract`**: an accepted `A` proof on a good trace yields `aggWit`, `n ≤ chainCap` and
  `c = leafStmt (chainEnd s n) n`. It needs **`SegKSOn (VsegC impl₀) vk Good`**: on a good trace,
  an accepted segment run has a table meeting `SegHolds`. The chain half is proved
  (`segSoundOn_of_KS` through `seg_sound` = `leaf_sound`).

**Controls.**
- (+) `finP_ctrl`.
- (−) `VC4_rejects`: a segment byte at the top, or a node of the wrong size, is rejected with no
  query.

### 3.4 Dumps (`logs/S-F4/dump/`, `SHA256SUMS`; tool `IRDumpF4.lean`, script `logs/S-F4/dump.sh`)

| Kind | file | ops | skeleton | finals | registers | asks = items | items |
|---|---|---|---|---|---|---|---|
| L30 | `ops-L30.txt` | 106,064 | 62,143 | 43,920 | 97,238 | true | 8,905 |
| L31 | `ops-L31.txt` | 106,072 | 62,143 | 43,928 | 97,246 | true | 8,905 |
| L32 | `ops-L32.txt` | 106,081 | 62,143 | 43,937 | 97,255 | true | 8,905 |
| N2 | `ops-N2.txt` | 106,221 | 62,051 | 44,169 | 97,394 | true | 8,905 |
| N4 | `ops-N4.txt` | 106,240 | 62,051 | 44,188 | 97,413 | true | 8,905 |
| N8 | `ops-N8.txt` | 106,240 | 62,051 | 44,188 | 97,413 | true | 8,905 |

- Every total includes one `accept`.
- A segment's skeleton is S-0′'s 62,048 ops, plus `lastOps` (94) and the Z2 operand (1).
- `items.json` is byte-identical to S-0′'s. `summary.txt` and `fsummary.txt` hold the counts;
  `last.txt` holds the `lastOps` runs.
- **The node dumps use placeholder public cells** (`oneCell + k`, 9 cells): the op count does not
  depend on their values, but the `prodKOps` registers do.
- These are measurements, not kernel theorems.

## 4. Deviations

1. **`SegSound` is not provable for any Fiat–Shamir program.** It quantifies over every trace, and a
   trace may answer the queries at will. The brief asked for "`SegSound` from `leaf_sound`".
   - Delivered instead: `SegSoundOn Good` / `SegKSOn Good`. The chain half is proved; the
     extraction half on good traces is the SNARK's, i.e. S-G's per-kind potential with its error.
   - `VA_extract_on` and `VC4_agg_extract` use them. `VA_extract` keeps its old hypothesis,
     unchanged.
2. **The flags at `seq4`** (`flag_fin*` over `FinP`) are not restated; see §3.1.
3. **Segment-specific op semantics:** a segment's `targetS` reads a 37-entry operand, and its
   `shiftMask` reads `τ ‖ L`. These are new implementations under the existing op names (`implSeg`).
   The `Op` type and 3.x's `OpImpl` are unchanged.
4. **`FR.lean`**: three imports added (as S-0′ did), so that `lake build FR` covers the new modules.

## 5. For P2′

**`n`, the last block and the tables.**
- `n` enters the program in three places: `stmt` bytes 33–40 (`enc64 n`), Z2's `targetS` (range
  factor `Σ_{t < n} eq(r_blk, t)`, as your `range_eq`), and `finSh`'s `bnd[4…21]` (`L = n − 1`).
- **Prover tables:** unchanged with the zero witness, apart from `P^e`'s range factor (already
  done).
- **Verifier semantics: two new op behaviours in a segment program (your `ir.rs`):**
  - `targetS x`: `x` has 37 entries (position coordinate, 18 zero-padded block coordinates, then
    `L`'s 18 bits). The result is the leaf target × `Σ_{t ≤ L} eq(x[1..19), t)`.
  - `shiftMask t r`: `t` = `τ` (18) ‖ `L` (18). The result is `(eq(τ, r), shift(τ, r) + [L + 1 <
    2^18] eq(τ, L) eq(r, L + 1), eq(r, 0))`.
  - The segment's `finSh` selects these with `keep … true`; nodes keep the chain-masked
    `shiftMask`.
- **`lastOps`** uses only existing ops: `piDigest`, `idx` with 24 bits, `bitOf`, `selectHalf` on F
  registers, `addF`/`mulF`.

**What the finals do per kind:**
- `finZ`: `take (m − 13)` / `(m − 6)`.
- `finSh`: `m − 14` block coordinates zero-padded to 18.
- `finPf`: the kind's own family. Padding `(1 + sf₅)(1 + sf₆)` for `L30`, `(1 + sf₆)` for `L31`,
  none for `L32`/`N4`/`N8`. `N2` (`m = 31`): `(1 + sf₆)`.
- Node checks (`finLr`, `finE`) at `N2` take 16 / 22 / 24 coordinates. E4 end is at
  `phaseOffOf seq4 (E4end) fE`.

**Dumps.** Re-baseline the KATs to `logs/S-F4/dump/` (the finals are now present; S-0′'s
`ops-*.txt` are superseded).

## 6. For S-E12′

**The segment sub-slots' circuit.**
- `lastOps` (94 ops) in the `stmt` phase.
- Z2's 37-entry `targetS` operand: a template for the leaf target × the prefix-sum range factor
  (`segRangeI`: `prefixP` over 18 coordinates).
- The segment `shiftMask` (`shiftSegI`: `eqPoint`, `shiftPair` and one correction term).
- The segment program's `finSh` reads `stmt`'s outputs 1–19 (`zeroReg`, `lastRegs`).

**Node programs.**
- `progNode κ cells` needs the public cells (3.x: `pfCells`, M's `one` cell and the two signed
  children's seed payloads).
- The node's `implN κ`: `evalM`/`evalL` (`τ` = `logM`, `σ` = `m − 7`), `targetS`, `linkWAll`,
  `shiftMask`, with their specs and `Meets`. `nodeFinP`'s `nc = m − 7` (24 / 25 / 25) sizes
  `finPf`'s cell points.

**Node statement.** `finB′` is 3.x's (one cell, then `vk`, `c₁`, `vk`, `c₂`). If the 4.1 node's
public input differs, `gFinB'` needs the change.

## 7. Open questions

1. **S-G12′:**
   - `flag_fin*` over `FinP` (the generic relations at `seq4`);
   - the segment's shift soundness: `FRShift.shift_sound` with the masked successor and the last
     block `L`, then `SegKSOn` per kind;
   - the node potential with `progNode`.
2. **Golf:** FRVIRFinals4's `gFinX_3` proofs take 45 s of elaboration. FRAgg's byte controls take
   24.5 s of kernel time (S-0′).
3. **Kernel-checked semantics of `lastOps`:** a `pureRun` lemma for the borrow chain is not proved.
   The dump's `last.txt` measures it at nine values.
4. **Blueprint:** B-12 should state the masked successor and the `targetS` range factor, as in the
   table in §3.2.
