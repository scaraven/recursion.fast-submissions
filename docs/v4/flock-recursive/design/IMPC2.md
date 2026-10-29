# IMPC2: closing IMPC's four open import items (design, read-only)

Basis: rev44 `87519f4` plus the uncommitted ASK-T and REPF trees. Ruling: **accepted, not fast**, so
each item takes the least-effort sound route within the caps (V ≪ 2.07 s, plan init < ≈ 15 s, kernel,
N8). Every count below was read from the code (`FRVIR4`, `FRVIR4Mux`, `FRVIRFinals4`,
`FRVIRTplExt`/`TplRep`, `FRNodeRows4ArenaPlace`, `FRBlockKinds`, `FRNodeCircuit4`, `FRXOut4.sib4`) and
checked with arithmetic on `seq4`'s ladders. Row and V figures are projections from IMPC's measured
≈ 1.5 µs per sparse template row (`logs/IMPC/impcv-ck.log`). They are not measurements.

## 0. Findings that shape every option

- **The import cells are free M cells, and H cannot help.** H's cells are packed 128-bit words
  (`FRNodeCircuit4.zW4 = unpack (w (b/128))`), so neither the stream nor the hash blocks expose a
  bit to an F-linear row. A row's coefficients are F constants, and a byte shift, a byte mask or a
  bit of an element is GF(2)-linear but not F-linear. **Every item therefore needs Boolean cells in
  M.** Route (c), "prove it on the concrete run", only says *where the proof lives* (`SlotRunA`
  versus `ATImp`). It never removes the rows.
- **Route (a), changing V, does not remove the bit problem either, and is rejected for all four
  items.** V has no op that masks or shifts an F element; adding one (a new `Op` constructor)
  touches every `cases op` (`FRVIR`, `FRVIRCompile*`, `FRVIRTpl*`, `FRVIR4At`,
  `FRVIRFinals4.reloc`, `FRNodeRows4AskT`), and its template would itself need bit cells. Moving
  `h`/`n` to aligned offsets changes the `stmt` field, which *is* the hash message
  `tagLeaf ‖ h ‖ enc64 n` (`stmtLeafBytes`) that IMP's `stmtRowsS` copies into `hashA`, so the
  misalignment moves to H. Either way V's program, its soundness proofs (`FRSoundness4R4Stmt`,
  `R4Fin*`, `XRun`, `flag_fin*`), the prototypes, MxKat and the prover KATs change, and the same
  rows are still needed.
- **One shared bit area serves all four items.** IMPC's 15.9k is exact: 62 answers × 256 =
  15,872. Lay it out as PACK §5.2 planned, **position-major and bottom-aligned**: bit `h` of
  position `p` of level `i` is cell `posB_i + p·logNmax_i + h` (14,684 cells at m = 32); the answer
  bits no position uses go to a shared spare range of 1,188 cells (the m = 32 worst case; m = 31
  needs 779, m = 30 needs 1,138); the statement bits take 512 more (§3–4). The total is **16,384 =
  2^14 exactly**, so `bitV4`'s 14-bit automaton is unchanged (`bitV_eq` needs only `N ≤ 2^k`). The
  cells run `[389,120, 405,504)`, below p0's lowest template instance at 414,016 (re-check `arenafit`
  after CK); the fallback is k = 15. L is not used: an L-owner change for no gain.
- **Decomposition rows, one per answer half and per distinct kind map.** The row is
  `g·(A₁(ansE k, half) − Σ_{j<128} e_j·cell_κ(k, j)) = 0`, where `e_j` is the unit `x^{j mod 64}·y^{⌊j/64⌋}`
  and `g` is a selector form. `F` is `GF(2^64)[y]` on two little-endian `UInt64`s, and its addition
  is XOR. So Boolean `b_j` give exactly the element whose bits are `b_j`, and the bits are unique
  (lemma `decomp_bits`). This matches `natLE`'s bit order: `FRVIR.idxOfF`, and FRNodeReadP l. 216's
  `testBit (p%per·logN + h)`.
  - p0 (N4, N8 at m 32; N2 at m 31): 124 rows, using `s_N2·(D₃₁ − D₃₂) = H − D₃₂`.
  - p1 (m 32, 30, 31): 348 gated rows.
- **The template-row range does not fit p1 as laid out today.** It holds ASK-T's 62,180 + `impcTG`'s
  11,108 + this design's 81,039 = **154,333 rows**. `arR2N` can grow to at most 148,816 while REPF's
  segment replay rows sit at `repSegB = 30·2^15`, because `arRb + arNb ≤ repSegB`
  (`FRNodeRows4Fit.repConsts`). REPF uses 8 rows there. With **`repSegB := 31·2^15 − 2^10 =
  1,014,784`**, `arR2N` can be 180,560: 26k of margin for p1 and 50k for p0.
  `colTG`'s 27,856 rows then **no longer fit** (182,189 for p1): the `felems` take IMPC §3's
  compile-alias route. Lowering `arR2` is unsafe: CK added 6,720 rows to p0 after B2″'s 700,160.

## 1. Item 1: `bitOf` (15,265 per prototype in p0, 15,283 in p1)

These split into 7,426 Merkle steps (`merkleOpsG`), 7,839 cap-index bits (`bitPowOps`, 871 reads ×
`capMax` 9) and 18 bits of the segment's `n` (`lastOps`).

| option | what | verdict |
|---|---|---|
| (a) | a `bitOf` on the answer register with a kind-table index (an `Op` change), which makes it `ATImp`-able | rejected (§0); the same rows are still needed |
| (b) only | rows tie the import cell to a bit cell | necessary, not sufficient: `ATImp` cannot see the operand (IMPC §5.2) |
| **(b)+(c)** | rows, plus the proof on the run (`SlotRunA`'s import conjunct) | **recommended** |

**Rows.** Merkle `bitOf j h`: `1·(imp − cell(p,h)) = 0`, the same for every kind
(`h < sib_max ≤ logN_κ`): 7,426 rows. Cap bit `t` is bit `sib_κ + t` of `j`, a different cell per
kind: in p0 one row, `s_P30·(c(sib₃₁+t) − c(sib₃₂+t)) = imp − c(sib₃₂+t)` (7,839 rows); in p1 three
gated rows `s_κ·(imp − c(sib_κ+t)) = 0` plus a pin at `t ≥ cap` (22,355). The 18 bits of `n` are
copies of statement bit cells (§4).

**Proof.** Extend IMPC's `execA_prov` with `execA_idx`: on the answer-driven run an `idx a b i`
register holds `idxOfF (b ι) (tr[k_a].2) (i ι)`, and a `shrN` register that value shifted. `PosBits`
(from the decomposition rows, `bit_slot` and ASK-P's `slot_ans`): a bit cell is bit `j` of the slot
trace's answer `k` under the selected kind's map. The generator emits `failR` on any `bitOf` whose
provenance does not match; unmatched ops then contradict the rows, so nothing is decided over the
program.

**Definition of done.** `bitOf ∉` the residual of the new `SlotRunB`, with `gap4Imp_of_bitsR`
proved. The probe shows 0 `failR` and every `bitOf` matched in both prototypes.

## 2. Item 2: siblings (7,426 `piDigest fSibs`) and `bits 20` (1,627 `tensorW` × 20)

`bits 20` covers 745 `tensorW` in `gLvOps` and 126 × 7 in `gEncOps`, which is 32,540 aux cells.

| option | what | verdict |
|---|---|---|
| (a) | V reads the node payload instead of `sib` | rejected: it changes π's format and V |
| PACK's form `l + r + a·cur` | uses `cur`'s cell | rejected: on the run, `cur`'s cell is what `compileX_run` *concludes*, so this is circular inside `SlotRunA` |
| **(b) as `ATImp`** | `sib = r + b·(l − r)`, where `l`, `r` are the node query's arena₁ halves (byte 8 and byte 40; `sib4` takes `r` at bit 0) and `b = cell(p,h)` | **recommended**: it is a function of the trace alone, so it is `ATImp`-able |
| grow `arNb` | 8,320 → 16,384 | **recommended** (§0); L is rejected |

**Rows for the siblings.** One product row per F half, `b·(l − r) = imp − r`: 14,852 rows, the
same for every kind. At depths whose activity depends on the kind, one gated zero row `g·imp = 0`
with `g = Σ_{h ≥ sib_κ} s_κ`: 1,742 rows (p0), 3,484 (p1). An honest inactive depth has
`l = r = 0` (V asks `nodeQF i zeroD zeroD`), so the product row holds there too.

**Proof for the siblings.** `atImp_sib (h : SibCells w π inp)`, in the pattern of `atImp_impc`.
`SibCells` comes from `StmtN4` through `a1_slot`, `slot_qelem`, `PosBits`, and `reassemble4`'s spec
for `fSibs` (ASK-P's `ctb4_sibs`, `sib4`). It also needs **the reader's kind byte `trM4` to equal the
selector's kind** (A1′'s `kindS`/`kindN`, flagged in IMPC §5.1): the main proof risk of this item.

**Rows for `bits 20`.** Aux cell `i`'s value is `cell(p,i)` if `i < logN_κ`, else `0`. One row covers
every kind: `g_i·cell(p,i) = aux`, with `g_i = Σ_{κ: i<logN_κ} s_κ`. That is 32,540 rows. The proof is
`SlotRunA`'s aux conjunct, through `execA_idx` and `PosBits`.

**Definition of done.**
- Siblings are in `cov`, and `impAP` holds no `piDigest`.
- Every `bits` aux entry is bound, so the residual aux is the `felems` only (`colTG` or the alias).

## 3. Item 3: the two mid-element foreign flags per prototype

| option | what | verdict |
|---|---|---|
| (a) | a whole-element read plus a mask, or splitting the tail read at π 112 | rejected: there is no mask op, and the part below byte 64 stays byte-level |
| (c-H) | the hash blocks' `msgPin`s: `hashA` byte 0 = `tagLeaf` and bytes 41–63 = 0; `hashB1` byte 0 = tag; `hashB2` bytes 1–63 = 0 (`FRBlockKinds` l. 199–207), through IMP's `stmtRowsS`/`stmtByte_prev`, plus 4 aligned pins for p1's bytes 64–127 | sound, 4 rows; separate lemma chains for p0 and p1, plus the activity gate |
| **(b)** | build the tag and the tail into the statement decomposition rows that item 4 needs anyway | **recommended**: about 0 extra cost, one shared lemma |

**Rows.** Write the statement element `E_k` (π `48 + 16k`, stream element `13 + k`).
- `E0 = F.ofBytes([tag, 0^15]) + Σ_{8≤i<128} e_i s_i`.
- The tail bytes are left out of the sums, which forces them to 0:
  - p0: `E4 = Σ_{i<8} e_i s_i`, and `E5–E7 = 0`;
  - p1: `E2 = Σ_{i<72} e_i s_i`, and `E3–E7 = 0`.
- **8 rows per prototype.**

**Proof.** `flag_stmt`, in `SlotRunA`'s flag conjunct. It uses `execA_prov` (the registers hold π's
bytes), `StmtBits` (from the rows, `decomp_bits` and `PfCells`), and `pfLoc_spec` for the `stmt`
absorb.

**Definition of done.** The probe lists 0 open foreign flags in p0 and in p1.

## 4. Item 4: the unaligned statement reads

These are `gBndOps` `piElem fStmt 1/17` (π 49, 65), `gFinB'` `piDigest fStmt 1/33` (π 49, 81), and in
p1 `lastOps` `piDigest 0 81`.

| option | what | verdict |
|---|---|---|
| (a) | aligned statement layout, or V reads aligned elements | rejected (§0): the field is the hash message; there is no shift op |
| (c) only | prove it on the run | impossible: the import cells are free |
| **(b)** | statement bit cells; each read is one linear row per F half: `imp − Σ_{i<128} e_i·s_{8·o+i} = 0` | **recommended** |

**Cells and rows.**
- Bit cells: p0 needs bytes 1–64 (E0 bits 8 to 127, E1–E3, E4 bits 0 to 7), which is 512. p1 needs
  bytes 1–40, which is 320. One range of 512 serves both.
- Rows: 5 decomposition rows (p0) or 3 (p1), 6 import rows (p0) or 8 (p1), and 18 copy rows for the
  bits of `n` (p1).
- These are static π reads, so **`ATImp`** applies: `atImp_stmt (h : StmtBits w π inp)`, with the
  generator in the shape of `impcTG`.

**Definition of done.** The four reads are in `cov`, and `impAP` holds no statement read.

## 5. Totals, costs and checks (projected)

| | p0 | p1 |
|---|---|---|
| new template rows | 64,537 | 81,039 |
| with ASK-T and `impcTG` | 130,800 | 154,333 (cap 180,560, after REPF's `repSegB` move) |
| new cells | 8,064 bits (same range, both prototypes) | — |
| V per node, both prototypes | ≈ +0.22 s rows + ≈ 0.03 s for the decomposition rows' ≈ 75k entries | — |

- **V(N4)** projects to ≈ 0.70 s VM (ASK-T's 417.5 ms + `impcTG`'s 34 ms + ≈ 0.25 s): ≈ 3× under
  2.07 s; the runner-to-VM ratio is unmeasured (H-probe). Above ≈ 1.2 s on the runner, the lever is
  `a1V4`-style structured evaluators for the four regular copy families (Plan, REPF's file).
- **Plan init:** +1.5–4.4 s at IMPC's 10–30 µs a row, close to the 15 s cap: the generator must be
  table-driven (`Array` provenance like `provL`, `@[irreducible]` tables against ASK-T's
  `protoV4_eq` recursion trap, no list scans). **Measure first** (step 2).
- **Kernel:** ≈ 1,500 lines in 4 modules, ≈ 2–4 s by IMPC's ratio (1.2 s for 1,078 lines). Nothing is
  decided over the tables: checks run at plan time and failures become `failR`.
- **N8 and the stream:** unchanged. **E1:** writes the bit cells (per-kind position-major map, the
  spare, the statement bits) and an honest statement at inactive sub-slots, as for ASK-T's rows.

## 6. Modules

New modules, nobody else's files:
- `FRBits128`, low: `decomp_bits`, `natLE`/`F.ofBytes` bit order, unaligned windows as bit sums.
- `FRNodeRows4AskB`, below `FRNodeRows4` (imports `FRNodeRows4AskI`): tables, `posTG`, `stmtTG`.
- `FRNodeRows4AskBS`: `PosBits`, `StmtBits`, `SibCells` from `StmtN4`; `atImp_sib`, `atImp_stmt`.
- `FRNodeRows4AskBR`, above `FRNodeRun4AskT`: `execA_idx`, the `bitOf`/`bits`/`flag_stmt` conjuncts,
  `SlotRunB`, `gap4Imp_of_bitsR`.

Edits: `FRNodeRows4ArenaPlace` (owner free: `arNb` 16,384, `arRb` 998,400, `arR2N` 180,560);
`FRNodeRows4Fit` (REPF: `arConsts`, `repConsts`); `FRNodeRows4Defs` (REPF: `repSegB`); `FRNodeRows4`
(orchestrator, after ASK-T: `askTG … .add posTG .add stmtTG`); `FRNodeRows4AskIS`/`AskIR`'s `rfl`
controls; `FRSubmission4Cert`/`Fin` (route `Gaps4`); `FR.lean`.

## 7. Order (no file conflicts)

1. **Now, as a message to REPF before it lands:** `repSegB := 31·2^15 − 2^10`. It is REPF's own
   constant and saves a later edit to `Fit`.
2. **Now, in parallel with ASK-T and REPF (BIT-A):** `FRBits128` and `FRNodeRows4AskB` (new
   modules), plus the probe `bitstat` (private build tree): rows per class, `failR` (must be 0),
   matched `bitOf`/aux/siblings/reads, `askV` ms, plan-init delta. **Kill line:** p1 above 180k
   rows or plan init above 14 s reopens the cap-bit layout (a second kind-free cap-bit
   decomposition: −14.5k p1 rows, +7.8k cells) and `colTG`.
3. **After ASK-T lands (BIT-B):** `FRNodeRows4AskBS` and `AskBR`, proved against the committed
   `askAq`. The orchestrator then makes the `askTG` edit and restates IMPC's `rfl` controls.
4. **After REPF lands:** the `ArenaPlace` and `Fit` constants, the plan re-dump, MxKat, V(N4) and
   plan init measured, the full FR build, axioms and kernel profiles.
5. **Before step 4:** the orchestrator decides `colTG` (alias): the only remaining aux residual.
6. **E1:** the prover writes the bits; it ends with `eok` and 0 failing rows on N2, N4 and N8.

Overall done: `Gaps4` discharged with `SlotRunB` reduced to the `felems` (nothing after `colTG`);
build green, no `sorry`, the three axioms only, source rule clean.
