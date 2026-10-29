# PACK-4.4: binding the node circuit's imports (the pack map, B1–B4, the replay `R`) — a proposal for blueprint revision 4.4

Design track D-PK, 2026-10-29. Base: HEAD after S-E13a/S-E13b/S-E14 (worktree `v4/flock-recursive`).
Nothing here is built; every row count that is not marked *measured* is a count from the dumps
(`logs/S-E12f/nodedump`, `logs/S-E13a/nodedump`) or from the formulas given next to it. Sources
read: BLUEPRINT §4.3–§4.4, A.5–A.7, A.11, changes 26–28; S-N2, S-E13a (+JOURNAL), S-E13b, S-E14
(+JOURNAL §0–§1.10), S-E6 §4–§7, S-E3 §9, S-E12a–f, INT-8/9; Lean (read only): `FRNodeSound4`,
`FRNodeSound4R` (`Gap4`, `SlotImp`, `SlotRun`), `FRNodeRead4` (`rd4`), `FRNodeRows4`,
`FRNodeRows4Pack`, `FRNodeRows4Plan` (`linkV4`, `wfSum`), `FRNodeCircuit4`, `FRNodeKinds4`,
`FRNodeLayout4`, `FRVIRCompile` (`opOut`, `imports`, `CS`), `FRVIR` (`evalOp`), `FRVIR4Mux`
(`merkleOpsG`, `posOpsG`), `FRTranscriptDefs`, `FRAgg`, `FRVerifier4`.

**Units used throughout.** VM figures. An F product 0.2 µs; an *irregular* row (a row whose cells
are not inside an aligned piece of its prototype: H, L, `WM`, or scattered M cells) 0.6 µs in
`evalMT4` (S-E13a, measured on the `wf` pins); a *structured* row (inside the prototypes' aligned
pieces, evaluated through the plan's keys and the copy identity) ≈ 0.06 µs: INT-9 measures
`evalM` at 85 ms for N4's ≈ 1.46 M prototype rows. VM → EPYC 7763 ratio 1.19. The score's
`x = V/206.6 ms + |π|/2 MiB`, `V̄ = 0.2667·max(x, x³)`; today `x ≈ 1.39–1.44`, so
`dV̄/dV ≈ 0.2667·3x²/206.6 ≈ 7.8 ms⁻¹·10⁻³`, i.e. **+10 ms of runner V ≈ +0.078 s of S**, and
**+100 KB of π ≈ +0.075 s of S**.

---

## 0. Summary and recommendation

1. **Diagnosis (§1).** The compiled prototypes' imports are fresh M cells because `opOut`
   allocates every import on `cs.next` (`FRVIRCompile.imports`/`impSlots`) and the copy mechanism
   moves *every* cell by `(σ−π)·2^20` (`mvC`), which cannot be right for an H cell whose slot
   offset is `(chBase_σ − chBase_π)·128`. Placing an import register *at* an H cell is sound for
   every statically addressed class (`holds_rowMapC` holds for any move function), but it does
   not remove the cost: each H cell referenced by a prototype row is one irregular entry
   (0.6 µs) in *every* slot, which is S-E13a's ≈ 40 ms per bound slot either way. The cost is
   intrinsic to *scattered* H references, not to whether they sit in a pack row or a consuming
   row. The only V-cheap binding is a **stride-1 copy of the whole stream into an M arena**
   (one row per stream element, rows and cells in stream order): its MLE is the diagonal
   range sum, `O(log)` per slot (§5). Two classes cannot be bound statically at all: the Merkle
   **sibling** (`piDigest fSibs`, which A.5 defines as "the half not at bit `h`") and the **cap
   read** (`piDigestAt`, a witness-indexed lookup, B2). The sibling disappears in
   characteristic 2 (`sib = l + r + cur`, §1.3); the cap read needs a protocol change (§3).
2. **B1 (§2): adopt R-A′ in its general form**: `V_A` asks one spacer absorb between segments,
   its length chosen so that the segment stride is `≡ 0 mod 64` and `≡ 1 mod 16`. With the B2
   change below the spacer is **81 B** (an absorb of a 1-byte message), not 129. There is no
   alternative: a byte-shifted field is GF(2)-linear, not F-linear, and binding it costs
   130 rows per element (S-E13b's `r31` pattern), ≈ 12 M rows per sub-slot.
3. **B2 (§3): replace the 871 cap lookups by a batched polynomial check** ("(β)"): the segment
   proof carries the per-cap aggregated selectors `A ∈ K^1920` (61,440 B), formed with the
   transcript's last `κ_c` as `ζ`; one final phase absorbs `A` and squeezes `z ∈ K`; `V` checks
   `Σ_r ζ^r cur_r = Σ_k A_k cap[k]` and `Σ_k A_k z^k = Σ_r ζ^r z^{k_r}`. In the circuit every cap
   read becomes a static read and the
   checks are ≈ 37 k template rows per slot. Costs: `|π|` +7.7 % (+0.047 s of S), V's own check
   +≈ 5 ms VM (+0.03 s), stream +4.2 % per segment — **N8 fits H with 324 blocks to spare**
   (§3.4), ε unchanged (two SZ rows at `≤ 2^{-245}`). The alternatives (full paths, smaller
   caps, a lookup PIOP with a second commitment, the mux) are priced and rejected in §3.2.
4. **B4 (§4): one generic theorem `compileFromX_run`**, the trace-building twin of S-E14's
   `compileFromX_soundR`: an induction along the compile trail, never over the 106 k ops of a
   concrete program, with a per-`ask` obligation discharged by an `AskBound` predicate defined on
   the trail (pins, FS links, Merkle mux rows). It produces `SlotRun`'s `exec … = some (s, [])`
   for the reader's trace, so `Gap4.imp` becomes a theorem with residual `∅` for every class.
5. **Layout (§5): two arenas per slot.** Arena₁ (92,672 cells, one per stream element, rows at
   `R₁ + e`) binds H by the `O(log)` diagonal; arena₂ (≈ 88 k cells, one per element a template
   consumes, laid at power-of-two instance strides per level) is bound to arena₁ by M-to-M copy
   rows whose MLE is a shift-window automaton: ≈ 60 products per position, 52 k products per
   prototype, and **identical for both prototypes** (one item sequence), so ≈ 11 ms VM per node.
   Every consuming row of the prototype then reads M cells inside aligned pieces (0.06 µs/row).
6. **The row budget (§6)** forces one layout change: **the previous-node slot owns two `2^20`
   regions** (its prototype in one; its arenas, `R` and the `evalM` replay in the other). Then
   N2 = 4 regions of 4, N4 = 6 of 8, N8 = 8 of 8 (the segment slot at ≈ 995 k of 1,048 k rows:
   N8 needs the two prototype levers S-E6 §5 lists, −90 k, to stay under `N_M/1.05`).
7. **The V budget (§6.3):** V(N4) ≈ 215 (today, without S-E13a/b's rows) + 19 (pack map) + 10
   (cap check) + 7 (`R` without `evalM`, keyed) + 7–15 (`evalM` replay) + 7 (WOTS/aggChk)
   ≈ **265–273 ms VM ≈ 223–229 ms runner** (worst case 309/260 if the sparse skeleton is not
   templated), `x ≈ 1.49–1.52`, `V̄ ≈ 0.88–0.93 s` against 0.71–0.79 today: **+0.1 … +0.2 s of
   S** (worst +0.5), the price of a sound node. S-T1/S-E11's levers (−25 ms) are unchanged and
   would bring it back to ≈ 0.75–0.80. `R`'s six ops cost 7 ms only as *keyed* templates
   (§6.2); as sparse pieces they are S-E14's 130 ms.
8. **Build order (§7):** (A) the protocol changes first, since every position in R4/P4 depends
   on `seq4` — B2's final phase is *appended* (no existing item moves), R-A′ changes only `V_A`;
   (B) the compiler: aliases, arenas, the staged run theorem; (C) the `R` templates;
   (D) `evalM`'s replay in the spare region with S-E12b's levers; (E) P2.
9. **If (D) does not fit V** (its 7–33 ms is the least certain figure), the least-bad scope
   change is §8's: keep the previous node's `evalM` as the *one* remaining import, discharged
   not by rows but by the **parent's E-phase**: the child's `evalM` claim is folded into the
   parent's own lincheck as a second point claim on `f` (the blueprint's option (c) of
   S-E6 §4), which removes `R`'s fixed point from the circuit at the price of one extra
   sumcheck phase (23 F rounds, +1,104 B of π, +≈ 2 ms of V).

---

## 1. Diagnosis: why the imports are not H cells, and what aliasing buys

### 1.1 The mechanism

`FRVIRCompile.opOut` compiles every oracle answer, proof field, challenge conversion and
answer bit as `imports cs [ty]`: the register's slot is `some (ty, [cell (cs.next + j)])`, a
fresh M cell, and the register goes into `cs.imp`. `compileTF4_soundAt` then takes
`∀ i ∈ imp, RepS w (slot i) (rd s.regs i)` as a hypothesis — S-N1's O2, S-N2's `Gap4.imp`.
Prototype `π` is compiled once at M-relative base `π·2^20 + 4` and every slot is
`mvRows π σ` = the prototype's rows with *all* cells shifted by `(σ−π)·2^20` (`FRNodeRows4.mvC`).
Blueprint A.7/A.11 assumed "trace cells need no rows" because the imported cell *would be* the
H cell. That needs two things the compile does not have: (i) a cell map `H_σ : element → cell`
per slot, `sCell (chBase κ σ') e = (b0 + e/4)·128 + 4 + e mod 4`, whose slot dependence is a
block offset, not `(σ−π)·2^20`; (ii) for the sibling and the cap read, a *static* address — which
does not exist (§1.3, §3).

### 1.2 What aliasing would cost in V

Suppose the compile had a piecewise move (M cells by `(σ−π)·2^20`, H cells by
`(chBase_σ − chBase_π)·128`): `holds_rowMapC` holds for any `f`, so soundness is unchanged.
Evaluation is not: `copy_val` needs every cell of a copied row inside the slot's region
(`eq(τ_hi, σ)·eq(u_hi, σ)·MLE_lo(prototype)`), so every row with an H entry leaves the copy and
is evaluated per slot, one product per entry at 0.6 µs. The H entries per slot are
≈ 17.8 k (answers: 8,905 digests × 2 halves) + 10.4 k (proof fields) + 7.6 k (`bitOf`) + 0.35 k
(challenges) + 27.9 k (`dotKF`'s column words, the `felems` auxiliary imports) ≈ **64 k
entries ≈ 38 ms per slot** — the same figure whether they sit in S-E13a-style pack rows (2 entries
+ `one`) or in the consuming rows. So **aliasing saves rows and cells (−63 k rows, −27 k cells
per slot) but no V**; V is saved only by making the H references *regular* (§5).

### 1.3 Per-class table: the cheapest sound binding

Counts per prototype from S-N2 §2 (`mregs-p{0,1}.txt` joined to `proto-p{0,1}.txt`). "Arena"
means the binding of §5: the register's slot is the arena₂ cell (no row of its own), arena₂ is
copied from arena₁ (M-to-M, once per node in V), arena₁ from H (`O(log)` per slot).

| Class (per slot) | Count | Where the value is | Binding | Rows per slot | V, formula → µs | Prover |
|---|---|---|---|---|---|---|
| oracle answers `askSeed/Absorb/Squeeze/Node/Col` | 8,905 D = 17,810 F | the item's answer, 2 aligned elements | slot := arena cells (alias) | 0 own; share arena₁/₂ | in the arena total (§5.4): ≈ 0.05 ms per slot + ≈ 11 ms per node | writes the arenas (copies) |
| proof fields `piElem`/`piDigest`/`piElemK` **except siblings** | ≈ 2.8 k F + 1,068 D + 355 K | = query payload elements of their item (A.5 rows 0–16) | alias to the arena cells of the payload (B3: `pf`'s positional spec is a lemma, no row) | 0 | 0 beyond the arena | — |
| **siblings** `piDigest fSibs` | 7,552 D | the half of the node payload *not* at bit `h` (A.5) | **linear form** `sib = l + r + cur` (char 2; `l`, `r` the payload's arena cells, `cur` the previous answer's), sound given the Merkle mux row below | 0 | 0 | — |
| Merkle mux (B4's node links; replaces `selectHalf`'s 4 `muxOut` rows per step) | 7,552 steps | `cur` is the half at bit `b_h`: `b·(l + r) = cur + l` per half | 2 product rows per step, inside the position template (arena₂, regular) | **15,104** (−30,208 `muxOut` rows: net −15 k) | structured: 15 k × 0.06 µs ≈ 0.9 ms per prototype | — |
| FS links (absorb/squeeze state = previous answer) | 468 items × 2 | arena₁ cells at fixed offsets | linear rows `M(st_k) = M(ans_{k−1})`, M-to-M | 936 | irregular-in-region: 936 × 0.6 ≈ 0.6 ms per prototype (×1 per node via the copy) | — |
| `wf` pins (tag, length words) | 8,905 | item starts | pins on arena cells: inside the position templates for Q items (7,552 + 871), 482 FS pins as rows | 8,905 (replacing S-E13a's H-cell pins) | templates: ≈ 0.5 ms; 482 × 0.6 ≈ 0.3 ms per prototype | — |
| answer bits `bitOf` | 7,552 (node) / 7,570 (seg) | bit `i·b_κ + h` of a P2 squeeze answer | slot := the L position-bit cell, **per-kind** (`Out.kin`, S-E12f: the bit index depends on `b_κ`); the 62 answers' 256 bits tied by 124 linear rows `H_half = Σ_j x^j b_j` on arena₁; the 8,320 bits L does not hold are M Boolean cells (`b(1−b) = 0`, a stride-1 template) | 124 + 8,320 | structured: 8.4 k × 0.06 ≈ 0.5 ms per prototype | writes 8,320 bits |
| `tensorW` index bits (aux `bits 20`) | 745 × 20 | the same L bits | the same cells (the `idx` register's bits are the answer's bits) | 0 | 0 | — |
| `dotKF` column words (aux `felems 64/16`) | 290 × 64 + 581 × 16 = 27,856 | the column payload's elements | aux cells := arena₂ cells of the column (regular instance stride) | 0 | 0 beyond the arena | — |
| challenge conversions `chF`/`chK` | 289 + 29 | halves / both halves of a squeeze answer | alias (a `chK` is the two halves' form) | 0 | 0 | — |
| `input` (`vk`, `c`) | 4 / 3 | `vk`, `c₁`: the public seed cells (`PubCells4`); a segment's `c`: `leafStmt e n` | `vk`/`c₁`: alias to `seedC σ 0..3` (S-E3 §9's proposal, no row); a segment's `c`: alias to the slot's `hashA` block's `h_out` cells (elements 2–3), tied to the stmt payload by §4.2's 8 gated rows (exist in the model, not yet in `nodeIRows4`) | 8 | 8 × 0.6 ≈ 5 µs | — |
| `hashStmt` fact `stmtOk4` | 1 | `stmtDigest grp (stmt) = c` | for a segment: true by the reader's definition (`slotIn`'s `c := leafStmt (view)`, and `hashA`'s output *is* that digest: `hashA_leafStmt`); for the previous node: `hashB1/B2` blocks + `PubCells4`'s `c₁` | 0 | 0 | — |
| **cap reads** `piDigestAt` | 871 D | cap entry at witness index `k = j >> sib` | **no static binding**: §3 | §3: ≈ 37 k template rows | §3: ≈ 2 ms per prototype | writes `A`, the powers |
| foreign flags | 12 / 79 | ops `opOut` leaves foreign (`assertBit`, type-failed asserts, `.hashStmt`) | per op: a lemma on the generator (the flag is `true` on every run) or a row; list from `fors` in the dump | ≤ 100 | — | — |
| the ten replay registers | 10 | the slot's own ops | `R` (§6; S-E14's mechanism) | §6 | §6 | — |
| the run's existence | 1 | — | B4's theorem (§4), no rows beyond the above | 0 | 0 | — |

**Per-slot total of the pack map proper:** arena₁ 92,672 + arena₂ ≈ 88,000 + mux 15,104 −
30,208 + FS 936 + pins 8,905 + bits 8,444 + `input` 8 ≈ **184 k rows, 189 k cells**, against
S-E13a's 63 k irregular rows. More rows, ≈ 50× less V: **≈ 2.5 ms per prototype + ≈ 11 ms per
node for the arena₂ link + 0.05 ms per slot** (§5.4), against ≈ 38 ms per slot.

---

## 2. B1: the aggregate's unaligned segments — ruling recommendation

**The fact.** `|traceBytes tr| = segB − 1 = 1,482,751 ≡ 15 (mod 16)`; segment `i` of the aggregate
stream `0x54 ‖ tr₁ ‖ … ‖ tr_k` starts at byte `1 + i·1,482,751 ≡ 1 − i (mod 16)`. Every field of a
sub-slot `i ≥ 1` straddles two H elements (S-E13a B1).

**Why no binding exists without re-alignment.** The pack `f[e] = bits [128e, 128e+128)` makes a
byte shift inside F a GF(2)-linear map that is not F-linear (multiplication by `x^8` is not a
scalar). The only encodings of a shifted equality are (i) the element's 128 bits as Boolean cells
plus two pack rows (S-E13b's `r31`: 130 rows per element) — 92,672 elements × 130 ≈ **12 M rows per
sub-slot**, 11× a region; (ii) Frobenius rows (`a² = c`, 127 per element, S-E13b's `phiRS` pattern)
— same order. Neither fits. So the H layout must put every segment at a 16-aligned offset.

**The options.**

| Option | Change | Owners | Cost |
|---|---|---|---|
| **R-A′ (general form): `V_A` asks a spacer absorb between consecutive segments**, `absorbQ 0³² 0^s` with `s` such that the segment stride `(segB − 1) + Δ_B2 + (49 + s)` is `≡ 0 mod 64` (and `≡ 1 mod 16`, automatic) | `FRAgg.VAwith` (`seqAll` with the spacer between the `segProgs`), `aggTr`/the reader (`segTr`'s offset `1 + i·stride`), `FRNodeKinds4` (`aggB k = 64·L·k − 128` whole blocks; `aggL`), the prover (writes the spacer's item), `qV` +3 | S-0′/FRAgg, S-E (reader, layout), P2 | `k − 1` queries and `(k−1)·(49+s)` stream bytes: **with §3's B2 change the spacer is 81 B** (`s = 1`): `1,482,751 + 61,680 = 1,544,431 ≡ 47 (mod 64)`, so `49 + s ≡ 17`, `s = 1`. Without B2: 129 B as S-E13a proposed. |
| R-B: pad `seq4` so `|traceBytes| ≡ 0 mod 16` (a 1-byte-longer item) | every segment proof, `FRTranscriptDefs`, R4/P4 positions | all | rejected: moves every position in R4/P4 for the same effect |
| R-C: hash each segment in its own digest chain | changes the signed message (`SigOk vk (traceDigest tr_A)`), `FRAgg`, the WOTS statement | all | rejected: the aggregate is one signed trace by B-11 |

**Ruling recommended: R-A′, general form.** Two consequences, both simplifications:
- sub-slot `i`'s stream is sub-slot 0's shifted by `L_seg·i` blocks (`L_seg = 24,133` with B2,
  23,170 without), so every per-slot row family is the same family at a block offset — exactly
  the shape `copy_val` and §5's arena bind need (`kindS`/`wf` at `i ≥ 1` follow by S-E13a's
  lemmas with `chainBytes4_elem` at the shifted element);
- the aggregate stream of `k` segments is `L_seg·k − 2` **whole** blocks, so R-4-m2's
  partial last block disappears: `AggPad4`'s message-prefix clause becomes "the candidate final
  block `F_{a,k}` carries the main chain's block `aggL k − 1` entirely" (its `h_in` the main chain's
  block `aggL k − 2`'s output, its message the block's; only the counter/flag target differs);
  S-E13b's `padRows` lose the element-7 decomposition (−130 rows per candidate) and `lastR` is 64.

Modules touched: `FRAgg` (`VAwith`, `VA_sound`, `VA_extract*`, `VA_queries_le`, `aggRest`, the
controls), `FRNodeRead4.segTr`, `FRNodeKinds4` (`segB`→stride, `aggB`, `aggL`, `tailIvs`),
`FRNodeCircuit4.AggPad4`, `FRNodeRows4Agg`, `FRNodeRows4PackSound` (`packB` for every sub-slot),
`FRVerifier4` (`qV` arithmetic: `4·8,894 + 3 = 35,579 ≤ 36,000`), P2 (`prover.s`: the spacer item;
its answer is unused).

---

## 3. B2: the cap reads — ruling recommendation

### 3.1 The problem, exactly

`posOpsG` ends each position with `shrN j sib → k`, `piDigestAt 0 capO k → c`, `assertEq cur c`
(`proto-p0.txt` 2676–2678): `c = digestAt π (capO + 32k)` with `k = j >> sib` a register. The
cap is the `cap_i` absorb's payload — `2^9/2^8/2^8/2^8/2^7` digests = 1,920 entries, all H cells
at static addresses — but *which* entry is a witness. An R1CS has no cheap dynamic read: the mux
`c = Σ_k eq(bits(k), k)·cap[k]` is `2^c − 1` eq-tree products plus `2^c` MACs per half,
≈ `3·2^c` rows per read: **871 reads ≈ 1.34 M rows per slot** (S-E13a's ≈ 0.8 M used the cheaper
bit-serial mux tree, 2·2^c), 1.3× a region. No restructuring of `seq4` makes `k` public: `k` is
bits of a squeeze answer, witness in the circuit by construction.

### 3.2 The options, priced

The H budget is the binding constraint. N8 (8 segment slots, `m = 32`) has `hUsed = 187,540` of
`196,608 − 1,024` (L) blocks: **7,936 blocks of slack, ≈ 1,000 per slot ≈ 4.3 % of a segment
stream** (`FRNodeLayout4.regions_fit`). Any option that grows the stream by more than that per
segment forces N8 to `m = 33`, which breaks "one item sequence for every kind" (the slot-0 mux
over `{N2, N4, N8}`, B-13) — not a local change.

| Option | What changes | Rows / slot | Stream / segment | `\|π\|` | V (own) | Prover | ε | Verdict |
|---|---|---|---|---|---|---|---|---|
| (a) full paths to a single root (caps of size 1) | `seq4`: +9/8/8/8/7 node queries per position = +7,132 items (8,891 → 16,023); every position moves in R4/P4 | +14 k (mux rows) | +7,132 × 112 B = +12.5 k blocks (**+54 %**) | +228 KB −45 KB: **+183 KB** (+0.14 s S) | +0.7 ms | +0.67 s per N4 node (12.5 k × 5 × 10.8 µs) | — | **rejected**: N8 ✗, `qV = 64,092 + 3 > 36,000` (fits `2^16` barely) |
| (j) caps at depth 4 (16 entries) + mux | `seq4`: +3,648 items; caps 2.5 KB | +42 k (templated mux, `shared` class) | +6,384 blocks (**+28 %**) | +74 KB (+0.06 s) | ≈ 0 | +0.35 s per N4 | — | **rejected**: N8 ✗ |
| (j″) caps at depth 6 + mux | +1,906 items | +166 k | +3,336 blocks (**+14 %**) | +26 KB | ≈ 0 | +0.18 s per N4 | — | **rejected**: N8 ✗ |
| (j‴) caps at depth 7 | +1,035 items | +333 k | +1,811 blocks (+7.8 %) | +5 KB | — | — | — | rejected: rows ✗ (segment slot 725 k + 333 k + arenas > `2^20`), N8 ✗ |
| (b) a lookup argument with a prover-committed auxiliary (logUp inverses, a permutation) | a second Ligerito commitment after the challenge | small | — | — | — | +≈ 30 % | new | **rejected**: a second PCS instance per proof |
| (b′) LogUp-GKR (no second commitment) | a new multi-layer sumcheck phase in `seq4` (dummy in segments) | ≈ 10 k | +≈ 2 KB | +≈ 2 ms | small | small | new sumcheck family | not recommended: a new proof system for S-C/S-G, R4/P4 positions move |
| **(β) batched polynomial check with prover-supplied aggregated selectors** (§3.3) | **one final phase appended to `seq4`** (1 absorb of 61,440 B, 1 K squeeze); `piDigestAt` → static `piDigest`; `gen4`'s cap assert → the two identities | **≈ 37 k** (templates: power chains, bit-products, shared-cell MACs) | **+965 blocks (+4.2 %)** | **+61,440 B (+7.7 %; +0.047 s S)** | **+≈ 5 ms VM (+0.03 s S)** | computes `A` (trivial) | +2 rows `≤ 2^{-245}` | **adopt** |
| (c) the mux at depth 9 | none | 1.34 M | — | — | — | — | — | does not fit |

### 3.3 The construction (β)

Let the reads of all five levels be indexed `r = 0 … 870` in item order, with index `k_r` (the
register `k`, `c_i` bits), path output `cur_r` (a digest = 2 F), and let `cap` be the 1,920
entries of all caps concatenated (`cap_i[k]` at `off_i + k`, `off = 0, 512, 768, 1024, 1280`).

- **Proof:** a new field `A` of `1,920` K elements (61,440 B), appended after the siblings (A.3
  row 18). Its honest value needs a challenge that is already in the transcript when `A` is
  written (the prover absorbs `A` before the final squeeze): take `ζ` **= the first K coordinate
  of `P3.4`'s `κ_c` squeeze**, which follows every query (A.4 row 46). The prover sends
  `A_{off_i+k} = Σ_{r at level i, k_r = k} ζ^r`, the final phase squeezes `z ∈ K`, and the check is:
  - (I) `Σ_r ζ^r·cur_r = Σ_k A_k·cap[k]` (over K, `cur`/`cap` as F-halves: two identities);
  - (II) `Σ_k A_k·z^k = Σ_r ζ^r·z^{k_r + off_{lvl(r)}}`.
- **Soundness.** (II) is an identity of two polynomials in `z` of degree `< 1,920`, checked at
  a fresh `z ∈ K` after `A` is fixed: by SZ, except with probability `1,919/2^256 < 2^{-245}`,
  `A_k = Σ_{r: k_r = k} ζ^r` for every `k`. Substituting into (I): `Σ_r ζ^r (cur_r − cap[k_r]) = 0`
  with `cur, k, cap` fixed before `ζ` was squeezed (they are determined by the items up to Q.4,
  and P3.4's squeeze follows them): a polynomial of degree `≤ 870` in `ζ`, so except with
  probability `870/2^256`, `cur_r = cap[k_r]` for all `r` — the truth today's `assertEq` gives.
  Both are per-fresh-query error rows `≪ εR = 15/2^124`; `εR` is unchanged. (If the reviewer
  prefers `ζ` fresh, add a second K squeeze to the final phase: +80 B of stream, same bound.)
- **`V` (`gen4`):** at each position `piDigestAt … ; assertEq` is replaced by `mulK`
  accumulations: `acc_I += ζ^r·cur_r` (a K×F product per half), `acc_II += ζ^r·zpow(k_r)`; after
  the final phase: `zpow(k)` for `k < 1,920` by one K power chain (1,919 products), `Σ A_k cap[k]`
  (1,920 K×F ×2), `Σ A_k z^k` (1,920 K), `z^{k_r}` as `Π_b (1 + bit_b(k_r)·(z^{2^b} − 1))`
  (9 K products per read, `z^{2^b}` by 11 squarings) — ≈ 1,919 + 3,840 + 1,920 + 7,839 ≈ 15.5 k
  K-equivalent products ≈ **5 ms VM** (a K product ≈ 3 F products). The native `acc` (P2's
  `ir.rs`) follows the dump.
- **Circuit (per slot, templates with regular instances):** the `ζ^r` chain 871 K products
  (2,613 rows), `z^{2^b}` 11 K squarings (33), per read `z^{k_r}` 9 K products (27 rows × 871 =
  23.5 k; the bits are the L position bits already bound), `ζ^r·cur_r` and `ζ^r·z^{k_r}` (871 × 5
  = 4.4 k), `A_k·cap[k]` and `A_k·z^k` (1,920 × 5 = 9.6 k, `cap`/`A` arena cells at fixed
  addresses: the `shared` class), the sums linear: **≈ 40 k rows per slot**, all `local`/`shared`
  classes, ≈ 2.4 ms VM per prototype at 0.06 µs.
- **Items:** `seq4` gains, after `Pf`, phase `CapChk = [absorb fA 61,440; squeeze z]` (A.4 row
  48). `items_length` 8,891 → 8,893; `piSize` 797,904 → 859,344; the stream per segment
  `1,482,752 → 1,544,432` B (+61,680: the absorb item 61,520 + the squeeze 80 + the 80 of a
  second squeeze if `ζ` is made fresh); blocks 23,168 → 24,133 (+4.2 %).

### 3.4 Fit and costs of (β)

- **N8's H:** `8 × 24,133 = 193,064` chain blocks + 2,196 (hashStmt, WOTS, WM, spare, tails as
  today) = 195,260 ≤ 196,608 − 1,024: **fits by 324 blocks**. With R-A′'s 81-B spacers the
  aggregate chain is `4·1,544,431 + 3·81 + 1 = 6,177,968 B = 96,531` blocks, two of them
  193,062: the same. There is no room for anything else in N8's H; a future change that adds a
  stream byte must take it from `A` (e.g. `A` over F with two independent `ζ`s: same bytes; or
  caps at depth 8 at level 0: `A` −8 KB, siblings +9 KB — no).
- **N2/N4:** chains `+965` blocks per slot; N4 `hUsed` 117,589 → ≈ 122,500 of 196,608 − 1,024.
- **`|π|`:** +61,440 B → `x` +0.0293 → **`V̄` +0.047 s**. **V:** +5 ms VM ≈ +4 ms runner →
  **+0.03 s**. Total **≈ +0.08 s of S**.
- **Prover (segment):** `A` is 871 K additions; the extra absorb ≈ 0. Node prover: +965 H blocks
  per slot × 10.8 µs ≈ +10 ms per slot (+0.05 s per N4 node).
- **What moves:** R4's `Fin*`/`R4Acc`/`R4Run` (the cap assert's final-phase form; positions are
  *appended*, nothing before `Pf` moves), P4 (none: positions on `seq4` up to `Pf` unchanged),
  S-C (the two identities' lemma: `capChk_sound`), S-G (the Q-phase truth unchanged, the doom
  gains the two SZ rows), S-0′ (`gen4`'s `posOpsG`/`finalOps4`), `FRTranscriptDefs` (`items`,
  `fA`, `piSize`), `FRFormat`, P2 (`ir.rs`, `prover.s`: `A`, the spacer), L-circ (the templates
  `tplPowChain`, `tplBitPow`, `tplMacShared`).

---

## 4. B4: the run's existence — the structure of the theorem

### 4.1 What is to be proved

`SlotRun impl π ι inp tr w` (`FRNodeSound4`) asks for `∃ s, exec impl ι inp (protoProg π).ops
St.init tr = some (s, [])` on the reader's trace `tr = slotTr4 κ v w` (`FRNodeRead4`: `seq4`'s
items read off `chainBytes4` from the segment's stream offset), plus the auxiliary, import and
foreign facts. `exec` (`FRVIR.exec`) consumes the trace at every `ask`: it continues only if the
query the registers determine equals the trace item's query, and then binds the answer. So the
run exists iff, at every `ask`, **the query computed from the registers' values equals the
stream's item**. Nothing else can fail (`.vals vs ok` always steps; `ok = false` only clears
`s.ok`, which `protoCS_soundAt` later refutes from the rows).

### 4.2 The shape: a trace-building twin of `compileFromX_soundR`

The theorem must not evaluate the program (kernel budget; S-E13's trap). S-E14 shows the
pattern: `compileFromX_soundR` is an induction along the compile trail `(cs, op)` with the
invariant `InvK w cs regs κ` (every register so far is represented by its slot), discharging a
covered op's import from rows named *by the trail*. B4 is the same induction with the trace
threaded through:

```
theorem compileFromX_run (hX : ExtOkK impl tc X κ) (hA : AskBound impl X ab κ) (base)
    (hP : SelOk w P κ) (hr : rows hold) (ht : template instances hold) (hx : aux facts)
    (hi : ∀ i ∈ impRX X P rt (CS.init base) ops, RepS w (slot i) …)      -- the uncovered imports
    (hs : StreamOf w b0 tr)                                               -- the H bridge: tr is read off H at b0
    (hab : ∀ r ∈ askRowsX X P ab (CS.init base) ops, r.Holds w) :
    ∃ s, exec impl κ inp ops St.init tr = some (s, []) ∧ InvK w (compileX X P base ops) s.regs κ
```

The induction is over `ops` with the accumulator `(cs, s, tr_rest)`; the invariant is
`InvK w cs s.regs κ ∧ tr_rest = drop (asksSoFar cs) tr`. Per op:

- a non-ask op: `exec` steps to `.vals`; `InvK` is extended exactly as in `compileFromX_soundK`
  (the op's rows/templates/imports give the new register's `RepS`);
- an **ask**: `AskBound` (defined on the trail like S-E14's `RTOk`) states, per ask constructor,
  that the rows `askRowsX` emitted at this `cs` tie the query's registers' cells to the arena
  cells of item `asksSoFar cs` — and the H bridge turns arena cells into the item's bytes. Then
  `evalOp … = .ask q` with `q = the item's query`, `exec` continues with the item's answer `a`,
  and the answer register's slot (the arena cells of the answer: §1.3's alias) represents `a`
  by the bridge: `InvK` extends.

**The per-item H-to-H (arena-to-arena) links `AskBound` needs**, by ask constructor:

| Ask | Query bytes = | Rows (per item) | Where |
|---|---|---|---|
| `askSeed hdr` | `"FRSEED0" ‖ vk ‖ c ‖ hdr` | `vk`, `c`: the `input` registers alias the seed cells (`PubCells4` gives the values); `hdr`: `piField 0 0 48` aliases the same cells (`pf`'s spec): none | — |
| `askAbsorb st msg len` | `tag ‖ st ‖ msg` | `st` (a register = the previous answer's alias) vs the payload's state cells: **2 linear rows** (M-to-M on arena₁); `msg` = `piField`'s alias = the payload: none; `len`: the pin | FS links |
| `askSqueeze st` | `tag ‖ st` | 2 linear rows | FS links |
| `askCol i col` | `tag ‖ column` | `col = piField fCols …` aliases the payload: none; the tag/length pin | position template |
| `askNode i h l r act` | `tag ‖ l ‖ r` | `l, r` are `selectHalf` results; with the sibling alias `sib = l_H + r_H + cur` the two `muxOut` register pairs are *replaced* by the payload's own cells and the **2 product rows** `b_h·(l_H + r_H) = cur + l_H` per half (`cur` the previous answer's alias; the col answer at `h = 0`); inactive kinds (`act κ = false`: the dummy depth) keep `assertZero`'s gated rows and the query `nodeQF i 0 0`: the payload is pinned zero by the same gated rows | position template |

The pins of the length word and tag (`wf`) are the same `AskBound` rows: the item's first element
`enc64 |q| ‖ tag`. **So B4's rows are exactly §1.3's FS links, Merkle mux rows and pins; there is
no separate "B4 row".** The theorem's cost is the generic induction (one new module, S-E14's
size: ≈ 400 code lines), plus one lemma per ask constructor.

### 4.3 How it fits `rd4` and `SlotIface4`

- `hs : StreamOf w b0 tr` is `FRNodeRows4PackSound`'s bridge (`chainBytes4_elem`,
  `readByte_cell`, `seg0_elem`) generalised to every sub-slot's offset (R-A′: `b0 + L_seg·i`).
  With arena₁ bound to H by §5's copy rows, the bridge is stated on arena cells
  (`w (A₁ + e) = F.ofBytes (stream bytes [16e, 16e+16))`), proved once from the copy rows.
- `pf`'s positional spec (B3) enters only as `RepS` of the alias slots: `piElem f o` aliases the
  arena cells of the item holding field `f`; the lemma `reassemble_field : bytesAt (reassemble tr)
  (absOff f o) n = bytes of item I(f)'s payload at o'` is A.5 read as a definition — S-H4's
  `reassemble` must be *defined* field by field so that these are `rfl`-style lemmas (one per
  A.3 row; the sibling row 17 is `reassemble_sib : digestAt π (sibOff i p h) = the half not at
  bit h of the node item's payload`, used by the sibling alias's `RepS`).
- `SlotRun` then holds with its import conjunct restricted to `impRX` (the uncovered imports:
  after §5 and §6, none), its aux conjunct from the arena (the `felems` aux cells are arena₂
  cells; the `bits 20` are L cells), its foreign conjunct from the per-op lemmas. `SlotImp` holds
  at every selectable index (the arena rows are index-independent; the per-kind aliases go
  through `CS.slotK`), with `stmtOk4` from `slotIn`'s definition (segment) or `PubCells4` +
  `hashB` (node). **`Gap4.imp` becomes `gap4Imp_of_arena`**, a theorem from `StmtN4`, and
  `resid4_of` loses its last `Gap4` field; `kindN`/`kindS` already follow (S-E13a; at `i ≥ 1`
  by R-A′), `wf` is the pins, `aggChk`'s (c) is §6.2's 1.3–2.7 k rows per aggregate.

---

## 5. The layout: the full pack map with a closed-form MLE

### 5.1 The stream's geometry (one segment, `seq4`)

`1,482,752` B = `92,672` elements = `23,168` blocks today; with §3, `1,544,432` B = `96,527`
elements = `24,133` blocks. Element `e` is H cell `sCell b0 e = (b0 + e/4)·128 + 4 + e mod 4`. Since
`4 + e mod 4` occupies bits 0–2 and `e/4` starts at bit 7, **`eq(σ, sCell b0 e) = eq(σ_{2..6},
(1,0,0,0,0)) · eq(σ̃, 4·b0 + e)`** where `σ̃` is `σ` with coordinates 2–6 removed: the H side is an
affine function of `e` on a 20-coordinate point. Items: FS items 468 (the seed 7 elements, an
absorb of 48 B 6, a squeeze 5, …), per level `i` and position `p`: one column item (level 0:
70 elements = `1 ‖ 67 ‖ 2`; levels 1–4: 22 = `1 ‖ 19 ‖ 2`) then `sib_i` node items of **7
elements** (`len‖tag ‖ l(2) ‖ r(2) ‖ ans(2)`): the position group is **147** elements at level 0
(`70 + 11·7`), `92 / 78 / 64 / 57` at levels 1–4. These strides are not powers of two, which is
the whole difficulty: a template instance at a non-aligned base costs `≈ 60` products (the
shift-window automaton, §5.3) instead of `O(1)`.

### 5.2 The two arenas (M-relative, per slot; the same addresses in both prototypes)

| Region (M-relative cells of the slot's region) | Size | Content | Bound by |
|---|---|---|---|
| **arena₁** `A₁ + e`, `e < 96,527` (`A₁ = 2^18`, aligned to `2^17`) | 96,527 cells | stream element `e` | **copy rows** `R₁ + e : one·(M(A₁+e) − H(sCell b0 e)) = 0`, `R₁` aligned to `2^17` |
| **arena₂** `A₂ + lvlBase_i + p·2^{a_i} + q`, `q < stride_i` (`2^{a_0} = 256`, `2^{a_{1..4}} = 128/128/64/64`) | `Σ_i t_i·2^{a_i} = 290·256 + 178·128 + 145·128 + 132·64 + 126·64 ≈ 132 k` cells (≈ 88 k used) | position `p` of level `i`: its 147/92/78/64/57 elements, in stream order | **M-to-M copy rows** `R₂ + lvlBase_i + p·2^{a_i} + q : M(A₂…+q) = M(A₁ + E_i + S_i·p + q)` |
| the FS items' elements | — | read directly in arena₁ (468 items at fixed addresses: `shared` class) | — |

- **The prototype's consuming rows** read arena₂ (the position templates: column fold `dotKF`,
  the Merkle mux rows, the `wf` pins of the Q items, the cap-check products) and arena₁'s FS
  elements (fixed addresses). Every such row is inside an aligned piece of the prototype →
  structured, 0.06 µs, evaluated **once per prototype** by the copy identity.
- **Why two arenas.** Arena₁ gives the per-slot H bind as a stride-(1,1) diagonal — `O(log)`
  per slot, which matters because the H base differs per slot (`4·b0_σ`); arena₂ gives the
  templates power-of-two instance strides. One arena cannot do both: a template reading
  arena₁ has instance stride 147 and costs ≈ 60 products *per instance per slot* (≈ 52 k × 5
  slots ≈ 52 ms per node), while an arena laid out regularly and bound to H directly costs the
  same 60 per instance per slot on the H side. The arena₁↔arena₂ link is M-to-M, so it is paid
  once per prototype — and since both prototypes have the same item sequence and the same
  arena addresses, its low-coordinate MLE is the same value for both: **once per node**.

### 5.3 The closed forms

Write `τ = (τ_lo, τ_hi)` at the region boundary (bit 20) and `u = (u_lo, u_hi)` for the cell
point. The slot factors `eq(τ_hi, σ)·eq(u_hi, σ)` are `copy_val`'s (already in the plan).

1. **Arena₁ ↔ H** (per slot `σ`, stream base `b0`): rows `R₁ + e`, `e < N_e`:
   `Â += Σ_e eq(τ, R₁+e)·eq(u, one)`, `B̂ += Σ_e eq(τ, R₁+e)·eq(u, A₁+e) + Σ_e eq(τ, R₁+e)·eq(u_{2..6}, 4)·eq(ũ, 4b0+e)`.
   With `R₁`, `A₁` aligned to `2^17 > N_e`: `Σ_{e<N} eq(τ_lo17, e)·eq(u_lo17, e)` is the **diagonal
   range sum** `D_N(τ_lo, u_lo) = Σ_{dyadic blocks of [0,N)} Π_b (τ_b u_b + (1−τ_b)(1−u_b))·(prefix
   eq factors)`: `≤ 17` blocks × 17 products ≈ **300 products**. `Σ_{e<N} eq(τ_lo, e)·eq(ũ, c + e)`
   with `c = 4b0` a constant is the **shift-by-constant diagonal**: the carry automaton with the
   carry `∈ {0,1}` and the range flag: `4 states × 20 bits × 2 ≈ 160 products`. `Σ_e eq(τ, R₁+e)`
   is a range sum (`≈ 40`). **≈ 500 products ≈ 0.1 ms per slot.** The sub-slot's `b0 = b0_agg +
   L_seg·i` (R-A′) changes only `c`.
2. **Arena₂ ↔ arena₁** (per node): per level `i`, `Σ_{p<t_i} eq(τ_hi', p)·Σ_{q<S_i} eq(τ_lo', q)·[eq(u, A₂+…+q) − eq(u, A₁ + E_i + S_i p + q)]`.
   The arena₂ term is aligned (`eq(u_hi, p)·D_{S_i}`): `O(log)`. The arena₁ term needs, per `p`,
   `W(X_p) = Σ_{q<S_i} eq(τ_lo', q)·eq(u, X_p + q)` at `X_p = A₁ + E_i + S_i p`: the
   **shift-window automaton** (`q`'s 8 bits, carry `∈ {0,1}`, range `q < S_i`, then the high part
   `eq(u_hi, (X_p + q)_hi)` for the two possible carries): **≈ 60 products per instance**. Total
   `871 × 60 ≈ 52 k products ≈ 10.5 ms`, **once per node** (both prototypes share it). The
   `eq(τ_hi', p)` factors are table lookups.
3. **Pins on arena cells inside the position templates** are ordinary template rows (`one` and
   a constant per level): part of `Â_tpl`, no extra cost. The 482 FS pins and 936 FS links:
   rows over fixed arena₁ addresses → `shared` class, `≈ 1,400 × 2` eq lookups ≈ 0.6 ms per
   prototype.
4. **The position templates** (one key per level: the column fold's `2·rows_i` rows, the `sib_i`
   Merkle mux pairs, the `1 + sib_i` pins, the cap-check per-read products): instances at
   stride `2^{a_i}` in both rows and cells → the existing `local` class (`eqInner · Â_tpl`),
   `Â_tpl` once per key: `|tpl| ≈ 150–400` products.

**Arena₁'s `one` entries** (`Â += Σ_e eq(τ,R₁+e) eq(u,one)`) are a range sum times one lookup.

### 5.4 V cost of the pack map against the 0.6 µs/row baseline

| Part | Rows per slot | Baseline (irregular, 0.6 µs/row) | This layout |
|---|---|---|---|
| arena₁ ↔ H | 96,527 | 58 ms per slot | 0.1 ms per slot |
| arena₂ ↔ arena₁ | ≈ 88 k | 53 ms per slot | 10.5 ms **per node** |
| Merkle mux, FS links, pins, bit rows, cap-check templates | ≈ 70 k | 42 ms per slot | ≈ 4 ms per prototype (0.06 µs/row) |
| **N4 (5 slots, 2 prototypes)** | | **≈ 760 ms** (S-E13a's 40 ms/slot was for 63 k rows without the cap check: 200 ms) | **≈ 19 ms VM** |

The uncertainty is the automaton's constant (60 products per instance is a count of its
transitions; the measured F product is 0.2 µs). A 2× miss gives 30 ms. Either is far below the
baseline. The row cost is the price: ≈ 190 k rows and ≈ 230 k cells per slot (§6).

---

## 6. The integrated feasibility: pack map + `R` against `N_M` and V

### 6.1 Rows per slot region (`2^20 = 1,048,576`; prototypes measured, `logs/S-E13a/nodedump4-run.log`)

| Part | Previous-node slot (prototype 0) | Segment slot (prototype 1) | Source |
|---|---|---|---|
| prototype as compiled today | 730,493 | 725,885 | measured |
| − `muxOut` rows of `selectHalf` (replaced by the Merkle mux rows below) | −30,208 | −30,208 | 2 × 2 per step × 7,552 |
| − the cap `assertEq`/`piDigestAt` (→ §3's templates) | ≈ 0 | ≈ 0 | |
| pack map: arena₁ 96,527 + arena₂ 83,333 + Merkle mux 15,104 + FS links 936 + pins 8,905 + bit rows 8,444 + `input` 8 | 213,257 | 213,257 | §1.3, §5.2 |
| §3's cap check | 40,000 | 40,000 | §3.3 |
| `R` without `evalM` (S-E14 §2: `targetS` 24 k, `linkWAll` 35 k, `shiftTarget` 2.2 k, `rsWeight` + kind factor 135 k, `evalL` 25 k) | 221,000 | 49,000 (after the dead `evalM`/`evalL` are dropped from the generator) | S-E14 |
| `evalM` replay (`R` proper): eq trees 48 k, keys 30 k, the child's arena₂ automaton as a 60-row template × 871 instances 52 k, the sparse skeleton's companions 55 k (templated, S-E12b lever) … 120 k (not), closed forms 8 k, outputs 1 k | **≈ 250–320 k** (S-E14's 90 k for the child's irregular link region is gone: the child's pack map is §5's) | — | §4.4, S-E9's classes, §5 |
| link region (S-E12c rows, WOTS/aggPad 8–8.7 k at slot 1, aggChk ≈ 2.7 k per aggregate) | reserved 32,768 | reserved 32,768 | S-E13a/b |
| **total in one region** | **1,457–1,527 k ✗** | **1,030,702 (98.3 %)** | |
| prototype levers (S-E6 §5: `phiRS` 134 rows in 256-row pieces −62 k; skeleton padding −29 k) | −91 k | −91 k | S-E6 |
| **total with levers** | 1,366–1,436 k ✗ | **939,702 (89.6 %)** | |

**The previous-node slot does not fit one region under any combination** (even without
`evalM` it is 1,207 k; without `evalM` and with the levers 1,116 k). **Layout rule for 4.4: the
previous-node slot owns two regions** — region A: the prototype (700,285 + the levers) and the
link region; region B: its arenas, `R` and the `evalM` replay (213 + 40 + 221 + 250–320 =
724–794 k, 69–76 %). The segment slots stay one region each. Cells: region A the prototype's
190.6 k; region B arena₁/₂ 180 k + bits 8 k + `R`'s (S-E14: `[2^19, 2^20)`) — fits.

| Kind | Regions used / available | Rows used | `N_M/1.05` | Margin |
|---|---|---|---|---|
| N2 (`m = 31`, `2^22`) | 2 + 2 = 4 / 4 | 733 k + 794 k + 2 × 940–1,031 k = 3.41–3.59 M | 3.99 M | 1.11–1.17× |
| N4 (`m = 32`, `2^23`) | 2 + 4 = 6 / 8 | 1.53 M + 4 × 940–1,031 k = 5.29–5.65 M | 7.99 M | 1.41–1.51× |
| N8 (`2^23`) | 8 / 8 | 8 × 940 k = **7.52 M** (without the levers 8.25 M ✗) | 7.99 M | **1.06× with the levers** |

So N8 depends on the two prototype levers (both are layout/alignment changes inside the compile
hint, no statement changes). A second N8 lever if needed: arena₂ holds only the consumed
elements (today 83 k; dropping the 3 padding elements per column item and the `len‖tag` elements
of node items to arena₁-side `shared` pins saves ≈ 10 k rows at +5 ms per prototype).

### 6.2 What `R` costs in V, and the two kinds of "template"

The plan evaluates three kinds of rows at very different prices: **keyed template instances**
(`Â_tpl` once per key, `O(log)` per instance; INT-9's 85 ms over ≈ 1.46 M rows is dominated by
them), **sparse pieces** (one product per entry, 0.6 µs per row: S-E13a's measurement, and the
`40,745 + 36,557` sparse skeleton rows of the two prototypes), and **closed forms** (`O(log)`
regardless of size). S-E14's "no closed form, ≈ 130 ms" prices `R`'s ops as sparse pieces.
Each of them has instance structure and can be keyed:

| Op (prototype 0) | Rows | Key structure | Products (`Σ |tpl|` + instances·`O(log)`) → ms |
|---|---|---|---|
| `rsWeight` claims | 45.6 k | 4 claims × 23 coordinates × a 127-step squaring chain (92 instances of one chain key), `eq(r^{2^k}, ρ)` products per stage (7 × 4 instances) | ≈ 3 k → 0.6 |
| the kind factor (`FRKindWeight4`) | 68.5 k | per Frobenius stage (7 instances): per-bit factors (25), dyadic range sums over the ≈ 22 kind intervals (a sum template per interval), `β`'s chains (7 × 127, the chain key) | ≈ 12 k → 2.4 |
| `targetSNode4S ν` | 24 k | eq tree over `zLo r` (tree key), per interval class the range sums (≈ 22 instances), the `w43` 399-term table (one linear key), muxed by `kmuxT` over 3 kinds | ≈ 8 k → 1.6 |
| `linkWAll4I ν` | 35 k | per family (8 instances) the source/mirror sums and `slotW` range forms, shared eq tables | ≈ 10 k → 2 |
| `evalL4I ν` | 15–25 k | the carry automaton per dyadic piece (≤ 14 instances) | ≈ 3 k → 0.6 |
| `shiftTarget` | 2.2 k | `Eθ` tree, `eq(τ, last)` | ≈ 0.5 k → 0.1 |
| **total** | 221 k | | **≈ 37 k products ≈ 7 ms VM per node** (as sparse pieces: 130 ms) |
| `evalM` replay | 250–320 k | u-rows share `Ĉ` with the parent's own keys (free), v-rows/sums `O(log)`, the arena₂ automaton key (871 instances), the sparse companions **if templated** | **≈ 7–15 ms**; +25 ms if the sparse skeleton stays sparse (S-E12b's lever not built) |

### 6.3 The V budget (N4, VM ms, best)

| Part | ms | Note |
|---|---|---|
| today, without S-E13a/b's rows (the brief: 213–225; INT-9 `implN4F` 178–179 unloaded) | 215 | S-E13a/b's +30 ms are replaced |
| pack map (§5.4) | 19 (–30) | 10.5 per node + 2.5 per prototype + 0.1 per slot |
| cap check: V's own identities 5 + templates 2 × 2.4 | 10 | §3.3 |
| `R` without `evalM`, keyed (§6.2) | 7 | 130 if left as sparse pieces |
| `evalM` replay | 7–15 (–40) | needs S-E12b's sparse-skeleton lever |
| WOTS/aggPad/aggChk link rows (≈ 11 k irregular at slot 1; S-E13a measured 17 ms at the fold's load) | 7 | templatable to ≈ 2 (chain stride 3, path stride 2) |
| **V(N4)** | **265–273 (worst 309)** VM ≈ **223–229 (260) runner** | |
| `x = V/206.6 + 859,344/2^21` | 1.49–1.52 (1.67) | |
| `V̄ = 0.2667·x³` | **0.88–0.93 (1.24) s** | today 0.71–0.79 |
| with S-T1's F-side kind factor and S-E11's `evalM` levers (−25 ms VM) | 0.75–0.80 | |

**ΔS ≈ +0.1 … +0.2 s (worst +0.5)**, of which 0.08 is B2's `|π|` and own check. P̄ gains the
node prover's +10 ms per slot for the longer stream (+0.05 s per N4) and `A`'s negligible cost.

### 6.4 Options the orchestrator asked to be weighed

| Option | Effect | Verdict |
|---|---|---|
| (1) closed forms per op (§6.2) and the two arenas (§5) | the design above: every `R` op and every import keyed; V +50–60 ms VM; two regions for the node slot | **recommended** |
| (2) move the child's `evalM` into the parent's PIOP (S-E6 §4 (c)): the child's `evalM(r_E2, r′)` claim becomes a point claim the *parent's* E-phase proves — the parent's lincheck is run on the matrix `[M_parent ; R-free]` with a second evaluation point folded by `κ_E` | removes `R` proper (−250–320 k rows, −7–40 ms V, the fixed point gone) at +1 E-phase (23 F rounds, +1,104 B of π, +≈ 2 ms V) — **but** the child's point `(r_E2, r′)` is witness (H cells), and a sumcheck at a witness point is not a lincheck: the parent would prove `Σ_x eq(r_child, x)·M(x)·…` with `eq(r_child, ·)` a *witness* table — a degree-3 sumcheck over `2^23` cells with a witness multiplier: 23 rounds of degree 3, and the eq table itself (2^23 K) is never materialised; the verifier's final check needs `eq(r_child, r_parent)` — computable from the H cells. Sound and standard ("proof-carrying" evaluation), but a new phase in S-C/S-G and the prover (+1 lincheck ≈ +0.3 s per node) | **the reserve** (§8): take it only if (1)'s `evalM` replay misses V by > 30 ms |
| (3) smaller children (`m = 31` segments only, `L32` dropped) | `R` unchanged in structure; the item sequence shrinks (positions 290 → fewer bits, same `t_i`), stream −3 %: nothing structural | no |
| (4) split a slot across two `2^20` regions | adopted for the previous-node slot (§6.1); a segment slot does not need it | adopted |
| (5) a different recursion shape (no previous-node slot: every step's node verifies only segments, the chain of nodes replaced by a tree) | removes prototype 0's `R` entirely (−221–540 k rows, −14–55 ms) but PR #20's step relation needs the previous node's acceptance in the step's witness (`Rel`'s node clause); a tree of nodes brings back 3.x's `P30`/tree costs (B-1 withdrawn) | no |
| (6) the `evalL` replay at `lRows4`'s `2^14` strides as 64-row chunks (S-E14's 125 k) | fits V only as the automaton key | subsumed by (1) |

---

## 7. Build plan

Tracks, in dependency order. Every stage keeps the build green and the kernel structural (the
new theorems are inductions along the compile trail; the only `decide +kernel` stay the shape
facts). Owners as in the blueprint's §7; "L-circ" is S-E.

| # | Track | Modules | Depends on | Delivers |
|---|---|---|---|---|
| A1 | **S-0′ / FRAgg: R-A′ general form** | `FRAgg` (`VAwith`, `VA_sound`, `VA_extract*`, `VA_queries_le`, controls), `FRVerifier4` (`qV` arithmetic) | — | the spacer absorb (`49 + s` B, `s` from A2's `seq4`); `kindS`/`wf` at `i ≥ 1` follow by S-E13a's lemmas |
| A2 | **S-0′ / FRTranscriptDefs: the `CapChk` phase** (§3.3) | `FRTranscriptDefs` (`items`, `fA`, `piSize`, `streamBytes`), `FRFormat`, `FRVIR4`/`FRVIR4Mux` (`posOpsG` accumulators, `finalOps4` + `capChkOps`), `FRVIRFinals4` (`finCap`) | — | `piDigestAt` gone from the programs; `items_length = 8,893`; dumps regenerate (positions before `Pf` unchanged) |
| A3 | **S-C: `capChk_sound`**; **S-G: the Q-phase doom** gains the two SZ rows | `FRVIRSpec`/`FRVIRFinalsCore`, the Rev4 truths (`truthQ4`) | A2 | the error accounting (§9) |
| A4 | **R4/P4**: re-run with the appended phase (`R4Acc`/`R4Run`/`R4Ref`, `R4Stmt`); P4's positions unchanged | — | A2 | no statement changes |
| B1 | **L-circ: aliases in the compile** — `opOut` takes an `Arena` parameter (per-prototype arena bases and the item→element table from `itemsOf seq4`, built once at process start like `wfSeg`); `piElem`/`piDigest`/`askX`/`chF`/`chK`/`input`/`felems` aux → arena/seed/`hashA` forms; `bitOf` → per-kind L slots (`Out.kin`); the sibling → the linear form; `selectHalf` on Merkle operands → the 2 mux rows | `FRVIRCompile` (an `Arena` field in `Params`, the import cases), `FRVIRCompileSound` (`RepS` of the alias forms as hypotheses `ArenaOk`), `FRNodeRows4Pack` (the element table), `FRNodeRows4Hint` | A2 | prototypes with ≈ 26 k fewer import registers; `compileX_soundK` with `ArenaOk` |
| B2 | **L-circ: the arenas' rows and their MLE** — `arenaRows κ σ` (arena₁↔H, arena₂↔arena₁, FS links, FS pins, bit rows), the position templates (one key per level), `tplArena_mle` (the diagonal range sum, the shift-by-constant and shift-window automata, with their proofs), the two-region node slot in `nodeIRows4`/`InSlot`/`ProtoFit`/`copy_val` | `FRNodeRows4`, `FRNodeRows4Plan`, `FRNodeRows4Fit`, new `FRNodeRows4Arena`, `FRVIRTplArena` | B1 | `evalMT4_eq` re-proved; V measured (`VTime4`); the row model updated (`protoRowsN` 730,493 − 30,208) |
| B3 | **L-circ: `compileFromX_run`** (§4) with `AskBound`, `gap4Imp_of_arena`; the foreign flags enumerated from `fors` (lemma or row each) | new `FRNodeRows4Run`, `FRNodeSound4R` (`Gap4` loses `imp`), `FRNodeRows4PackSound` | B2, S-H4's `reassemble` field lemmas (B3 of S-E13a) | **`Gap4` = `aggChk (c)` only** |
| B4 | **L-circ: `aggChk (c)`** (the views' chaining/sum/end/cap as rows: element decompositions 130 rows per element, a 64-bit adder) | `FRNodeRows4Agg` | A1, B2 | `Gap4 = ∅`; `ks_rev4GR` without `hGap` |
| C1 | **L-circ: the `R` keys** (§6.2): `rsWeight` claims (reuse `tplRsWeight`), the kind factor, `targetSNode`, `linkWAll`, `evalL`'s automaton, `shiftTarget`; each an `RT` with `RTOk` (S-E14's mechanism) and a key in the plan | `FRNodeRows4Rep*`, `FRVIRTpl*` | B2 | `SlotImpR` down to `evalM` |
| C2 | **S-0′: drop the segment group's `evalM`/`evalL`** (or the non-interference lemma) | `FRVIR4Mux` | — | prototype 1's six dead imports gone |
| D1 | **L-circ: `evalM`'s replay** in region B: the u/v-row layout over the plan's keys, the sparse-skeleton templating (S-E12b lever), the instance AP, the child's arena automaton key; `replay_mle`, `replay_sound` | `FRNodeRows4RepM` (new), `FRNodeRows4Plan` | B2, C1, S-E12b's levers | `SlotImpR = ∅`; `rep` discharged; V measured |
| E1 | **P2**: `ir.rs` (the `CapChk` phase, `A`), `prover.s` (the spacer, `A`, the arenas = copies, the 8,320 bit cells, the power chains, the `R` cells), the two-region node slot, the KAT against the dumps | — | A2, B2, C1, D1 | the honest node witness; the completeness KAT S-E13a/b asked for |
| F | **S-I**: `claim.json` (`qV` unchanged at 36,000; `ε` unchanged), the certificate on `ks_rev4GR` without `hGap` | — | all | |

What P2 must change, in one list: the segment prover writes `A` (871 K additions) and absorbs
it; the aggregate prover writes the spacer items; the node prover fills arena₁ (a copy of the
stream, 96,527 cells per slot), arena₂ (83 k copies), the 8,320 non-position bits of the P2
answers, the cap-check chains (`ζ^r`, `z^{2^b}`, `z^{k_r}`, the MACs), `R`'s cells as S-E14 §1.9,
and lays the previous-node slot over two regions; the native `acc` mirrors the new finals.

---

## 8. If the `evalM` replay does not fit V: the least-bad scope change

The one figure with a 5× spread is the `evalM` replay (7–40 ms). If after D1 it measures above
≈ 30 ms VM, take option (2) of §6.4: **the child's `evalM` claim is proved by the parent's
PIOP, not replayed.** Concretely: the previous-node slot's `evalM` register stays an *import*
(2 × 3 F cells); the node's E-phase gains a second lincheck instance at the child's point — the
parent's prover proves `Σ_x eq(r_child, x)·A_parent(x)… = evalM_child` — and the verifier's `finE`
gains the check `eq(r_child, r_parent)`-weighted. Rows: −250–320 k; V: −7–40 + 2 ms; π: +1,104 B;
prover: +1 lincheck per node (≈ +0.3 s per N4, ΔP̄ ≈ +0.1 s); Lean: S-C's lincheck lemma at a
witness-valued `eq` table (the table is the shift argument's `eqPt` structure evaluated on H
cells; `FRSumcheck`'s generic soundness applies), S-G's E truth with two instances, no change to
`KState`/`ε`. It is a bounded protocol change and it removes the fixed point for good; it is
*not* recommended first because (1) keeps the PIOP as it is and its cost is within +0.2 s.

If instead **the row budget** fails (N8 over `N_M/1.05` after the levers), the least-bad change
is N8 with 7 segment slots (`segSlots N8 = 7`): step 1 covers `≤ 7·2^18` compressions, which
exceeds the step cap `2^20` already; nothing in PR #20 needs 8.

---

## 9. ε accounting, and open questions

- **ε.** Two new per-fresh-query rows, both `≤ 2^{-245}`: (II)'s SZ at `z` (degree `< 1,920` over
  K) and (I)'s at `ζ` (degree `≤ 870`, charged to P3.4's squeeze, which already carries the
  `κ_c` doom `≤ 9/2^128`: the row becomes `9/2^128 + 870/2^256`). `εR = 15/2^124` is unchanged; the
  per-fresh-query maximum stays the E/Z rows'. R-A′'s spacer answers are unused: no row. The pack
  map, `R` and B4 add no error: they are circuit rows (soundness is `compile*_sound`).
- **`qV`:** segment 8,893 items; aggregate `4·8,893 + 3 = 35,575 ≤ 36,000`.
- **Open for the orchestrator.** (i) `ζ` as P3.4's `κ_c` (reuse) or a fresh K squeeze (+80 B
  stream per segment; N8's 324-block slack holds 8 × 2 blocks). (ii) The two-region node slot
  changes `copy_val`'s slot factor for region B (no prototype there: B's rows are the arenas and
  `R`, evaluated by their own closed forms) — confirm that `ProtoFit`'s index check extends to
  region pairs. (iii) The 79 foreign flags of prototype 1 must be listed before B3 is sized.
  (iv) S-H4's `reassemble` should be written field by field (A.3 rows) so that `reassemble_field`
  is definitional. (v) Whether to keep S-E13a's H-cell `wf` pins and kind tie until B2 lands
  (they are sound and cost 15 ms) or retire them with the arenas (recommended: retire, the pins
  move into the position templates and the 482 FS pins).
