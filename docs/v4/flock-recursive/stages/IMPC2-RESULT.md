# IMPC2 (track L-circ): RESULT — the shared bit area, its generator, and the bits' classes folded

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `3577618`, re-snapshotted onto
**`ae8b8d8`** (ASK-T). Build tree `logs/fr-build-IMPC2` (copy of `fr-build-IMPC`; `MINE.txt` = my modules,
everything else HEAD's text; `patch.py` applies the diffs of §6 locally). Logs `logs/IMPC2/`; journal
`IMPC2-JOURNAL.md`. Every lake/lean/probe ran in a 16 GB scope under `timeout`. No sub-agents, nothing
committed, no `sorry`. **No existing module was edited**; the edits others own are exact diffs (§6).

## 0. Summary

| Item | State |
|---|---|
| IMPC2 step 2: the generator, all four items | **Done**: `FRNodeRows4AskB` (`bitTGB` + `bitTGR`), generic in the prototype's op list and kind group (no literal op, register, offset or tag: the statement's layout and every provenance are read off the program) |
| Honest completeness (probe `bitstat`) | **0 `failR`** in both prototypes; **every** `bitOf` (15,265 / 15,283), sibling read (7,426 / 7,426), `tensorW` (1,627 / 1,627) and unaligned statement read (4 / 5) matched |
| Rows | p0 **64,651** / p1 **81,039** (design 64,537 / 81,039); with ASK-T + `impcTG`: 130,914 / 154,333 (needs `arR2N` 180,560, i.e. REPF's `repSegB` move) |
| Bit area | position-major 14,684 + spares 1,188 + statement 512 = **16,384** (p0 needs all of it, p1 16,192) |
| **Init (binding cap)** | Real process, A/B `plan4t init` (`plan4t-init-ab.log`): phase 1 (`bitTGB`, 48k / 63k rows) **+0.9 s user** (7.23–7.60 → 8.26–8.40 s). In-process, all of IMPC2: **≈ +1.0 s** (≈ +0.5 s per prototype: trail +0.30–0.40 s, grouping +0.16–0.21 s), down from +2.6 s at first cut. **Above the +0.5 s target**: §4 has the cause and the lever (compile aliasing, not in my files) |
| V | `askV` +75–100 ms per prototype (≈ +0.18 s per node with both prototypes) |
| Step 3 (proofs) | **Partly**: `AT.addD` and its `ATAsk`/`ATImp`/`ATOk` transfer; **`atImp_bitB`** (the bits' generator is sound to fold now); **`gap4Imp_of_bitsB`** (ASK-T's discharge with `bitTGB` folded); the `F`-bit core (`bit_bitsLin`, **`decomp_cell`**). **Open**: `ATImp` of `bitTGR` (siblings, statement reads) and the run proofs (`execA_idx`, `SlotRunB`) — §7 |
| Build | **`lake build FR Solution FRSubmission4Fin FRNodeRows4AskBS bitstat plan4t`: green, 5,031 jobs, 0 `sorry`**, with the §6 diffs applied (`patch.py`; `build-final.log`). **HEAD `ae8b8d8`'s own `FR` does not build** (§6.4) |
| Axioms / source rule | 21 declarations incl. `certified`, all ⊆ {propext, Classical.choice, Quot.sound} (`axioms.log`); source rule 454 files, 0 findings (`source-rule.log`) |

## 1. What was built (`loc.py`: total / code / thm; `logs/IMPC2/loc.txt`)

| module | lines | content |
|---|---|---|
| `FRNodeRows4AskBL` (new, low: imports `FRVIRTplCore`) | 92 / 60 / 8 | `F.bit`, `bit_add`, `bit_zero`, **`eBit`**, `eBit_shl_toNat`, **`bit_eBit`**, `bit_eBit_mul`, **`bit_bitsLin`**, **`decomp_cell`**, `eBit_ctl` (the design's `FRBits128`) |
| `FRNodeRows4AskB` (new, **below `FRNodeRows4`**: imports `AskBL`, `AskI`, `AskT`, `FRVIR4Mux`) | 458 / 273 / 1 | layout (`lvT`, `posBT`, `posCell`, `nPos`), provenance (`RI`, `riOf`, `riAcc`), statement layout (`StSpec`, `tagScan`, `tailScan`), **`BTab`/`mkTab`/`bitTab`**, `ansCell`, `stCell`, `idxSrc`, **`bitSrc`**, rows (`selRows`, `ansRows`, `stElRow`, `globRows`, `sibLoc`, `sibRows`, `stWin`, `stRdRows`, `auxBRows`), **`bitTGB`**, **`bitTGR`**, **`TG.addD`**, `bitTG` |
| `FRNodeRows4AskBS` (new, above `FRNodeRun4AskT`) | 225 / 147 / 15 | **`AT.addD`**, `askCtx_addD_left/right`, `atAsk_addD`, `atImp_addD`, `atOk_addD`, `opOut_selectHalf_imp`, `tplExt4_tw_imp`, `tplExt4_imp_tc`, **`atImp_bitB`**, `XofA`, `bitTabP`, `withBitsB`, **`askFold_bitsB`**, **`gap4Imp_of_bitsB`**, controls |

## 2. The generator

### 2.1 Layout (relative to `arBt`; `posCell` is kind-free)

- **Positions** `[0, 14,684)`: bit `h` of position `p` of level `i` is `posB_i + p·logN*_i + h`
  (`logN*` = `seq4`'s level at `m* = 32`, the largest). A kind with `logN_κ < logN*` leaves the top cells of
  each position unused (E1 writes 0 there).
- **Spares** `[14,684, 15,872)`: under kind `κ`, answer `q` of level `i` (used iff `q < sq_κ`) has its bits
  `j ≥ usedBits = min(per, t − q·per)·logN` at `nPos + sp_κ[g] + (j − usedBits)` (`g` the global answer index).
  The kinds share the range (one is selected); its size is the kinds' maximum (1,188 at `m = 32`).
- **Statement bits** `[15,872, 15,872 + 8(z − 1))`: message bit `b` (`8 ≤ b < 8z`) at `stmtB + b − 8`. Byte 0
  is the tag and bytes `≥ z` the zero tail: both constants, never cells. `z` = 65 (node) / 41 (segment).

`ansCell κ k j` is the cell of bit `j` of P2 answer item `k` under kind `κ` (a position bit, or a spare);
`none` if `κ` does not use the answer. `stCell b` is a statement bit's cell, the tail's zero, or `none`.

### 2.2 Tables (once per prototype, `mkTab`: 18–25 ms)

- **Provenance** `riAcc 0 ops #[]` (array over registers, tail-recursive): `.ans k` (ask `k`'s answer), `.idx a
  b i`, `.shr n s`, `.dig o` (a `piDigest` at absolute `o`), `.pf o len`, `.cb bytes`.
- **The statement's layout** from the program: the tag is the `assertEq` of a 1-byte `piField` and a 1-byte
  constant (`so = 48`, tag 78 / 76); the tail is the `assertZero` of a `piField` starting inside `[so, so+128)`.
- Each kind's ladder (`seq4.lvK (G ι).d.m`), the P2 answers' places (`ansList`, from `phasesOf seq4`), the
  spares' bases.

### 2.3 Rows

`bitSrc r h ι` follows the provenance: an `idx a b i` gives bit `h` of `idxOfF (b ι) (a ι) (i ι)`: zero if
`h ≥ b ι`, else bit `i·b + h` of the digest `a ι` (`ansCell` of an answer; `stCell` of a statement digest); a
`shrN n s` of an `idx` gives bit `h + s ι`. `selRows` turns the three kinds' sources into one copy row (all
agree), one product row `g_A·(a − b) = imp − b` (two classes), or one gated row per kind (three); a missing
source is `failRT`.

| class | where | rows | count p0 / p1 |
|---|---|---|---|
| decomposition (answers) | the seed's ask, once | per answer half and class of kinds with one map: `g·(A₁(aElT k + c) − Σ_{j<128} e_j·cell) = 0` | 238 / 348 |
| decomposition (statement) | the seed's ask, once | element `k < L/16`: `A₁(winE(so+16k)) − Σ e_j·cell = [k = 0]·tag·one` | 8 / 8 |
| `bitOf r h` | the **next op**, its `selectHalf` (bit operand = the last register) | `selRows` on the import cell | 15,265 / 29,799 |
| `bits n` aux | `tensorW` | `selRows` per aux cell | 32,540 / 32,540 |
| siblings | `piDigest` in an `fSibs` part (`sibLoc`) | per half `b·(A₁(l_c) − A₁(r_c)) = sib_c − A₁(r_c)`, `l`, `r` the node item's query elements `qElT`, `qElT + 2`; `gate(inactive)·sib_c = 0` | 16,594 / 18,336 |
| unaligned statement reads | `piElem`/`piElemK`/`piDigest` with `stWin` | per window `imp − Σ_{i<128} e_i·s(8(o+16c−so)+i) = 0` | 6 / 8 |

`bitTGB` = decomposition + `bitOf` + `bits` (covers `selectHalf`, `tensorW`: never imports, so its `ATImp` is
vacuous, `atImp_bitB`). `bitTGR` = siblings + statement reads (`ATImp` classes, proofs open).

### 2.4 Two composition findings

- **`TG.add` cannot hold `bitTGR`.** `add` asks every side for rows at any covered op, and `impcTG`'s
  `pfRows` answers `failRT` at a read whose windows are not elements: exactly the siblings and the
  unaligned statement reads. **`TG.addD`** asks each side only at its own covered ops and the asks
  (`addD_ctl`: + no row at the other side's op; − `add` gives the refusal). `B.cov` once per op, `A.cov`
  only at `B`'s ops.
- **`bitOf` rows go at the following `selectHalf`**, whose `pre` is the `bitOf` and whose bit operand is the
  last register. Covering the `bitOf` itself would put an unprovable `ATImp` obligation on it (IMPC §5.2).

## 3. The theorems, in words

- **`bit_bitsLin`**: over Boolean cells with distinct indices `< 128`, bit `j` of `Σ e_i·w(c_i)` is "some `c_i`
  with `i = j` holds 1". **`decomp_cell`**: if a row says `x = Σ e_i·w(c_i)`, each cell is `x`'s bit.
- **`atAsk_addD`, `atImp_addD`, `atOk_addD`**: `A.addD B` is sound if `A` is (`ATOk`) and `B`'s covered imports are.
- **`tplExt4_imp_tc`**: at a `selectHalf`/`tensorW` the extension's import flag does not depend on the
  template bodies, only the layout (so `bitTGB` reads it off `XofA π`, the template-free context).
- **`atImp_bitB (hX)`**: `ATImp impl X (bitTGB Xa π T).toAT κ inp w` whenever `Xa` agrees with `X` on the import
  flag at `selectHalf`/`tensorW` (`xofA_imp` for `XofA`/`Xof`).
- **`askFold_bitsB`** (`askFold` by `rfl` once `askTG` is edited) and **`gap4Imp_of_bitsB`**: ASK-T's
  `gap4Imp_of_askT` verbatim over `withBitsB askAq := (withImpc askAq π).addD (bitTGB (XofA π) π (bitTabP π)).toAT`:
  from `RepOk`, the replay fold, the ask fold, `StmtN4R` and `SlotRunA (rt π) (withBitsB askAq π) …`,
  every active slot's `SlotImp`. **Composes**: same hypotheses as `gap4Imp_of_askT`, `SlotRunA` over the
  larger template (more rows, so only more facts on the run).

## 4. Measurements (`logs/IMPC2/bitstat*.log`, one core, load 3–5)

| | p0 | p1 |
|---|---|---|
| `bitTG` rows / entries | 64,651 / 267,568 | 81,039 / 308,482 |
| failing rows | 0 | 0 |
| matched: `bitOf`, siblings, `tensorW`, stmt reads | 15,265, 7,426, 1,627, 4 | 15,283, 7,426, 1,627, 5 |
| bit area needed | 16,384 | 16,192 |
| tables (`mkTab`) | 19 ms | 18–25 ms |
| process start, trail (`askTG0` → `+ bitTG`) | 776–820 → 1,081–1,167 ms | 675–751 → 1,017–1,111 ms |
| process start, index + group + fit | 135–149 → 310–327 ms | 162–180 → 364–377 ms |
| `askV` (`askTG0` → `+ bitTG`) | 75–77 → 149–172 ms | 80–86 → 173–180 ms |

So **init ≈ +0.48–0.52 s per prototype, ≈ +1.0 s per process**; V(node) ≈ +0.18 s (both prototypes).
The real process confirms it for phase 1 (`plan4t-init-ab.log`, alternating, core 5): base 7.23 / 7.60 / 7.50 s
user, with `bitTGB` folded 8.38 / 8.26 / 8.40 s: **+0.9 s** for its 48,051 / 62,695 rows (the full fold adds
16.6k / 18.3k more cheap sibling rows).

**What it took** (first cut `bitstat.log`: +1.1–1.6 s per prototype): building a `tensorW` template per op in
`stepOut` (≈ 0.8 s per prototype) → `bitTGB` reads `imp`/`aux` off the template-free context
(`tplExt4_imp_tc`); the kind maps recomputed in `ansRows` → `kt`; a mux built at every `selectHalf` → the
extension alone; `Lin.sub`'s product per term → `subN`; `eBit` → a table.

**Why it stays at ≈ +1.0 s.** The per-class runs (`bitstat5.log`) put the cost on the rows themselves
(≈ 2.5 µs per row to generate, ≈ 2.5 µs to group), not on lookups. The only levers are fewer rows or a
cheaper representation, and both are in other tracks' files:

1. **Compile aliasing (owner: the compile, `FRVIRTplExt`/`FRVIRCompile`, INIT).** 47.8k (p0) / 62.3k (p1)
   of my rows are copies of a `bitOf` import cell or a `tensorW` aux cell onto a bit cell. If the compile
   made the `bitOf` slot and the `tensorW` aux cells *be* the bit cells (it needs `bitSrc`'s provenance, which
   `BTab` already computes; the zero sources need a pinned zero cell), those rows vanish: ≈ 35k rows remain,
   projected **≈ +0.3 s** init (≈ 7 µs a row all in) and most of my V gone.
2. **An ungrouped evaluator (owner: `FRNodeRows4Plan`, REPF/INIT).** Measured in `bitstat6.log`: it saves the
   grouping (≈ 0.25 s per prototype, ASK-T's rows included) but costs +85–120 ms of V per prototype. Per badge
   batch (start-up once, 8 checks) that is a net loss, so I do not recommend it.

## 5. Build, axioms, kernel

- **Build** (`build-final.log`): `lake build FR Solution FRSubmission4Fin FRNodeRows4AskBS bitstat plan4t` green,
  5,031 jobs, 0 `sorry`, at `ae8b8d8` + my three modules + `patch.py` (§6.1–6.4: arena constants, the
  phase-1 `askTG` fold, `askTGI`, the removal in `FRNodeRun4AskT`, the `ctlP` rename). Build time is not
  meaningful here (incremental, shared machine).
- **Axioms** (`axioms.log`, `ax/AxIMPC2.lean`): `RecursionFast.Challenge.certified` and 20 of mine
  (`bit_add`, `bit_eBit`, `bit_bitsLin`, `decomp_cell`, `eBit_ctl`, `addD_none`, `askCtx_addD_left/right`,
  `atAsk_addD`, `atImp_addD`, `atOk_addD`, `opOut_selectHalf_imp`, `tplExt4_tw_imp`, `tplExt4_imp_tc`,
  `atImp_bitB`, `xofA_imp`, `askFold_bitsB`, `gap4Imp_of_bitsB`, `selRows_ctl`, `addD_ctl`): each ⊆
  {propext, Classical.choice, Quot.sound}.
- **Kernel** (`lean -DElab.async=false --profile`, core 26, `profile-*.log`):

  | module | type checking | tactics | wall (mostly import) |
  |---|---|---|---|
  | `FRNodeRows4AskBL` | 0.12 s | 0.18 s | 7.1 s |
  | `FRNodeRows4AskB` | 0.12 s | 0.00 s | 7.9 s |
  | `FRNodeRows4AskBS` | 0.11 s | 0.70 s | 8.9 s |

  ≈ 0.36 s of new type checking. Nothing is decided over a table, a program or the format (every check of
  the generator runs at process start and fails into `failRT`). None of it is on `certified`'s path until
  `Gaps4` is routed through `gap4Imp_of_bitsB`; `FRNodeRows4` itself only gains the `addD` term.

## 6. The exact diffs (others' files)

### 6.1 `FRNodeRows4ArenaPlace` (after REPF's `repSegB := 31·2^15 − 2^10 = 1,014,784` lands)

```diff
-def arNb : ℕ := 8320
+def arNb : ℕ := 16384
-def arR2N : ℕ := 132096
+def arR2N : ℕ := 180560
-def arRb : ℕ := 950272
+def arRb : ℕ := 998400
 theorem a1Rows4_ctl … :
-      some (2 ^ 20 + 852997, …) ∧
-    (a1Rows4 κ 1 0)[5]?.map Prod.fst ≠ some 852997 := by
+      some (2 ^ 20 + 901461, …) ∧
+    (a1Rows4 κ 1 0)[5]?.map Prod.fst ≠ some 901461 := by
```
(and the doc table: bits `[389,120, 405,504)`, rows `[998,400, 1,014,784)`, binding `[720,896, 901,456)`, arena₁
rows `[901,456, 998,400)`). `arRb + arNb = 1,014,784 = repSegB`; `arRb + arNb + 2^15 ≤ 2^20`; `arNb ≤ 2^14`
(`bitV4` unchanged). With HEAD's `Fit` (no `repSegB`) the arena proofs and `arConsts` build unchanged.

### 6.2 `FRNodeRows4` (`askTG`; REPF also edits this file)

```diff
 import FRNodeRows4AskI
+import FRNodeRows4AskB
 …
 def askTG (π : ℕ) : TG :=
   (((askTGT (XofT π) π).add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)).add
-    (impcTG (XofT π) π (provLT 0 (protoProg π).ops))
+    (impcTG (XofT π) π (provLT 0 (protoProg π).ops)) |>.addD
+    (bitTGB (tplExt4 (protoF π) (protoR π) ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩) π
+      (bitTab (protoProg π).ops (if π = 0 then nodeGrp else segGrp)))
```
This is **phase 1** (`bitTGB`: decomposition, `bitOf`, `bits`; sound to fold now, `atImp_bitB`). Phase 2 appends
`|>.addD (bitTGR (same extension) π (same table))` once `atImp_bitR` exists (§7).

### 6.3 Collateral (ASK-T/IMPC's `rfl` folds), in the same commit as 6.2

- `FRNodeRows4AskIS`: `def askTGI (π : ℕ) : TG := askTG π` →
  ```lean
  def askTGI (π : ℕ) : TG :=
    (((askTGT (XofT π) π).add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)).add
      (impcTG (XofT π) π (provLT 0 (protoProg π).ops))
  ```
  (`withImpc_askT`, `withImpcC_askT` then hold by `rfl` as before: they compare the pre-fold generator).
- `FRNodeRun4AskT`: **delete** `askFold_askT` and `gap4Imp_of_askT` (from "`/-- **Today's fold**`" to the
  `Controls` header). Once `askTG` folds `bitTGB`, `askIRows4 (withImpc askAq)` is no longer the fold (row
  indices move), so `askFold_askT` is false. Their replacements are `FRNodeRows4AskBS.askFold_bitsB` and
  `gap4Imp_of_bitsB` (same hypotheses). No other user (`grep`).
- `FR.lean`: `import FRNodeRows4AskBS` (pulls `AskB`, `AskBL`).

### 6.4 HEAD's `FR` does not build (independent of IMPC2)

At `ae8b8d8`, `lake build FR` fails: `FR.lean` imports both `FRNodeRows4RepCtrl` (l. 23 `def ctlP`) and
`FRNodeRun4AskT` (l. 49 `def ctlP`), both in `FR.N4s` ("environment already contains 'FR.N4s.ctlP'"). Fix
(applied locally): rename ASK-T's to `ctlPT` in `FRNodeRun4AskT` (7 occurrences, its control section only).
- Re-dump the plan form, MxKat, V(N4), `plan4t init`: `protoV4`'s value changes.

These four are exactly `logs/fr-build-IMPC2/patch.py`, with which the full build of §5 ran.

## 7. Open (step 3, what remains)

1. **`atImp_bitR`** (siblings and unaligned statement reads as `ATImp` classes), given
   - `StmtBits`: the statement cells are the slot's message bits — from `globRows`' element rows, `bit_slot`,
     `decomp_cell`, `a1_slot`, and `F.ofBytes`' bit order (the one missing lemma: bit `8k + t` of
     `F.ofBytes v` is bit `t` of byte `k`);
   - `PosBits`: a position cell is bit `h` of `posOf4 seq4 m i ans p` for the selected kind's `m` — from
     `ansRows`, `slot_ans'`, `decomp_cell`, and `natLE`'s/`idxOf`'s bit order;
   - **the kind risk**: `sib4`/`posOf4` read the trace's ladder `trM4`, the rows the selector's; the tie is
     A1′'s `kindS`/`kindN` (stream element 5 = `Σ_ι K_ι s′_ι`, `packHead4`).
   Then the diff of §6.2 phase 2.
2. **The run proofs**: `execA_idx` (an `idx` register holds `idxOfF` of its answer; a `shrN` its shift),
   the `bitOf` import conjunct (rows at the `selectHalf`, `bitSrc`), the `bits` aux conjunct, `flag_stmt` (tag
   byte and zero tail from the statement element rows), `SlotRunB`, `gap4Imp_of_bitsR`. Nothing needs a
   decision over the program: every check in the generator becomes `failRT`.
3. `colTG` (orchestrator's decision): with my rows, p1 has no room for its 27.9k (IMPC2 §0).
4. The init lever of §4 item 1 (compile aliasing) if the start-up budget needs the 0.6 s.

## 8. What E1 must fill

Per slot (frame `oneCell + σ·2^20`), once 6.1 lands:
- **Bit cells** `arBt + j`, `j < 16,384`:
  - `posCell i p h` = bit `h` of position `p` of level `i` under the slot's kind (bit `(p mod per)·logN + h` of
    answer `⌊p/per⌋`), for `h < logN_κ`; **0** for `logN_κ ≤ h < logN*`;
  - spares: the used answers' remaining bits at `nPos + sp_κ[g] + (j − usedBits)`;
  - statement bits `stmtB + b − 8` = bit `b` of the statement message (`8 ≤ b < 8z`);
  - every other cell 0.
- **Template rows** (`σ·2^20 + arR2 + k`): phase 1 adds 48,051 (p0) / 62,695 (p1) rows; phase 2 16,600 / 18,344.
  They hold on the honest witness: `bitOf` imports and `bits` aux cells hold the bits, the siblings the
  query halves (zero at inactive depths), the statement windows their bytes; 0 failing rows on the compile.
- An honest statement and answers at **inactive** sub-slots too (the decomposition rows are not gated by
  activity).

## 9. Controls

| Definition | (+) | (−) |
|---|---|---|
| `eBit`, `F.bit` | `eBit_ctl`: `eBit 3` has bit 3, `eBit 100` bit 100 | neither has a neighbouring bit |
| `decomp_cell` / decomposition rows load-bearing | `decomp_cell`: the cells are the element's bits | (a cell other than the bit breaks the row: `bit_bitsLin`) |
| `selRows` | `selRows_ctl`: copy (all agree), one product row (two classes), three gated rows | a kind without a source: `[failRT]` |
| `TG.addD` | `addD_ctl`: a refusing side is not asked at the other's op; both at an ask | `add` asks it: the refusal is a row |
| the generator on the real compile | `bitstat`: 0 `failR`, every op of each class matched | — |
| the fold composes | `askFold_bitsB` (`rfl` once 6.2 is applied; built with `patch.py`) | — |

## 10. Files

- New: `submissions/flock-recursive/lean/FRNodeRows4AskBL.lean`, `FRNodeRows4AskB.lean`, `FRNodeRows4AskBS.lean`.
- Docs: `docs/v4/flock-recursive/stages/IMPC2-RESULT.md`, `IMPC2-JOURNAL.md`.
- Build tree (dev): `logs/fr-build-IMPC2/patch.py`, `probe/BitStat.lean`, `ax/AxIMPC2.lean`, `scratch/Bits.lean`,
  `scratch/Tw.lean`.
