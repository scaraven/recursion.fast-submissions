# PACK-4.4: binding the node circuit's imports (the pack map, B1–B4, the replay `R`) — a proposal for blueprint revision 4.4

**Revision 4.4.1 (2026-10-29): re-issued after `reviews/PACK-4.4-review.md` (adopt with fixes). §2, §3.3–§3.4, §5.2, §6.1, §6.3, §7, §8, §9 are re-issued; §0's figures corrected; the fix log is §10. Superseded text is not kept.**

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
2. **B1 (§2): adopt R-A′ as S-E13a proposed**: `V_A` asks the 129-B spacer absorb between
   segments; with the block-aligned CapChk the segment stride is `64·24,133` and the aggregate
   stream is whole blocks for every `k` (`aggB k = 64·(24,133k − 2)`). There is no
   alternative: a byte-shifted field is GF(2)-linear, not F-linear, and binding it costs
   130 rows per element (S-E13b's `r31` pattern), ≈ 12 M rows per sub-slot.
3. **B2 (§3): replace the 871 cap lookups by a batched polynomial check** ("(β)"): the segment
   proof carries the per-cap aggregated selectors `A ∈ K^1920` (61,440 B), formed with the
   transcript's last `κ_c` as `ζ`; one final phase absorbs `A` and squeezes `z ∈ K`; `V` checks
   `Σ_r ζ^r cur_r = Σ_k A_k cap[k]` and `Σ_k A_k z^k = Σ_r ζ^r z^{k_r}`. In the circuit every cap
   read becomes a static read and the
   checks are ≈ 48 k template rows per slot. The phase is block-aligned (`A` padded to 61,472 B):
   `piSizeOf seq4` 798,192 → 859,664, items 8,905 → 8,907, the segment stream 23,168 → 24,131
   blocks. Costs: `|π|` +7.7 % (+0.03 s of S), V's own check +5–6 ms VM (+0.04 s), stream +4.2 %
   per segment — **N8 fits H with 256 blocks to spare** (§3.4), ε unchanged (two SZ rows at
   `≤ 2^{-245}`). R4's `cols` and S-G's tail are *restated* (§9.1), not re-run. The alternatives (full paths, smaller
   caps, a lookup PIOP with a second commitment, the mux) are priced and rejected in §3.2.
4. **B4 (§4): one generic theorem `compileFromX_run`**, the trace-building twin of S-E14's
   `compileFromX_soundR`: an induction along the compile trail, never over the 106 k ops of a
   concrete program, with a per-`ask` obligation discharged by an `AskBound` predicate defined on
   the trail (pins, FS links, Merkle mux rows). It produces `SlotRun`'s `exec … = some (s, [])`
   for the reader's trace, so `Gap4.imp` becomes a theorem with residual `∅` for every class.
5. **Layout (§5): two arenas per slot.** Arena₁ (92,672 cells, one per stream element, rows at
   `R₁ + e`) binds H by the `O(log)` diagonal; arena₂ (≈ 88 k cells, one per element a template
   consumes, laid at power-of-two instance strides per level) is bound to arena₁ by M-to-M copy
   rows whose MLE is a shift-window automaton: ≈ 150 products per position, 131 k products per
   prototype, and **identical for both prototypes** (one item sequence), so ≈ 26 ms VM per node
   (4.4.1: was 60 / 11 ms; PK-m2).
   Every consuming row of the prototype then reads M cells inside aligned pieces (0.06 µs/row).
6. **The row budget (§6)**: every slot's region holds its prototype, its arenas and its cap
   check (the copy identity needs them together: PK-M3); the previous-node slot's spare region
   holds `R` and the `evalM` replay. The segment slot is at 1,060 k rows — **S-E6 §5's two
   prototype levers (−91 k, track B0) are a prerequisite**, after which N2 = 4 regions of 4,
   N4 = 6 of 8, N8 = 8 of 8 at 1.03× under `N_M/1.05`. The Merkle `selectHalf`/`keep` rows stay
   as compiled (PK-M4); only the sibling import cells go.
7. **The V budget (§6.3), on the measured basis** (S-I: V 157.9 ms runner, `v_ref` 206.6,
   `V̄ = 0.400`): ΔV ≈ 60 ms VM best (arena₂ automaton 26 at 150 products per instance, cap check
   11, `R` keyed 7, `evalM` replay 7, templates/rows 9) to 124 worst → V runner 208–262,
   `x = 1.42–1.68`, **`V̄ = 0.76–1.26 s`: ΔS ≈ +0.36 s best, +0.86 worst**, the price of a sound
   node against S = 6.42. 4.4's "+0.1 … +0.2" mixed two `v_ref`s and is withdrawn. `R`'s ops
   cost 7 ms only as *keyed* templates (§6.2); as sparse pieces they are S-E14's 130 ms.
8. **Build order (§7): the review's corrected one** — A2′ (CapChk) → A1′ (R-A′) → A3′ (the
   restated `cols`/dooms) ∥ B0 (the prototype levers) → B1′ → B2′ → C0 (template the WOTS/link
   rows) → B3/B4 → C1/C2 → D1 or the reserve → E1, with RET (changes 27 (B), G2) in parallel
   from A2′ on, and F's done including `evaluate.py cert ≤ 600 s`. Track briefs for A2′, A1′,
   A3′, B0 in §7.1; the build-budget account in §7.2 (≈ 3,400 CPU-s before retirement against
   2,020: the organiser's `build_s` question must be asked now).
9. **§8 decides D1 against the reserve on the measured basis:** D1 first (ΔS +0.05 best) with a
   kill line at 25 ms VM of replay cost, beyond which the reserve (the child's `evalM` claim in
   the parent's E-phase, ΔS ≈ +0.21–0.25 from the extra lincheck's prover time) wins. N8 with 7
   slots is not needed.

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
| **siblings** `piDigest fSibs` | 7,552 D | the half of the node payload *not* at bit `h` (A.5) | **per-kind form** `sib = l + r + v`, `v = a·cur` (char 2; `l`, `r` the payload's arena cells, `cur` the previous answer's, `a` the depth's activity: at a dummy depth `v = 0`, as `assertZero` demands — PK-M4/m3) | 3,484 (2 per kind-varying depth per position) | structured | — |
| Merkle mux (B4's node links) | 7,552 steps | `selectHalf`'s `muxOut` rows and `keep`'s, **kept as compiled** (they are gated by construction; an ungated `b·(l + r) = cur + l` forces `cur = 0` at dummy depths: PK-M4); their operands become arena₂ cells | 0 new | structured | — |
| FS links (absorb/squeeze state = previous answer) | 467 items × 2 (the seed has no state) | arena₁ cells at fixed offsets | linear rows `M(st_k) = M(ans_{k−1})`, M-to-M | 934 | `shared` class: ≈ 0.6 ms per prototype (×1 per node via the copy) | — |
| `wf` pins (tag, length words) | 8,905 | item starts | pins on arena cells: inside the position templates for Q items (7,552 + 871), 482 FS pins as rows | 8,905 (replacing S-E13a's H-cell pins) | templates: ≈ 0.5 ms; 482 × 0.6 ≈ 0.3 ms per prototype | — |
| answer bits `bitOf` | 7,552 (node) / 7,570 (seg) | bit `i·b_κ + h` of a P2 squeeze answer | slot := the L position bit at `p·maxb + h` (kind-independent: bottom-aligned per position, §5.2); the 62 answers' 256 bits tied by **3 gated decomposition rows per half** `s_κ·(H − Σ_j x^j b_{π_κ(j)}) = 0` (372); the 8,320 bits L does not hold are M Boolean cells; the 9 cap bits per read (`sib_κ + t`: kind-dependent) by kind-mux rows (7,839) | 372 + 8,320 + 7,839 | structured: ≈ 1 ms per prototype | writes 8,320 bits |
| `tensorW` index bits (aux `bits 20`) | 745 × 20 | the same L bits | the same cells (the `idx` register's bits are the answer's bits) | 0 | 0 | — |
| `dotKF` column words (aux `felems 64/16`) | 290 × 64 + 581 × 16 = 27,856 | the column payload's elements | aux cells := arena₂ cells of the column (regular instance stride) | 0 | 0 beyond the arena | — |
| challenge conversions `chF`/`chK` | 289 + 29 | halves / both halves of a squeeze answer | alias (a `chK` is the two halves' form) | 0 | 0 | — |
| `input` (`vk`, `c`) | 4 / 3 | `vk`, `c₁`: the public seed cells (`PubCells4`); a segment's `c`: `leafStmt e n` | `vk`/`c₁`: alias to `seedC σ 0..3` (S-E3 §9's proposal, no row); a segment's `c`: alias to the slot's `hashA` block's `h_out` cells (elements 2–3), tied to the stmt payload by §4.2's 8 gated rows; the previous node's `hashB1`/`hashB2` messages tied to the proof's `stmt` field (8 rows) and `hashB2.h_in = hashB1.h_out` (2): PK-m7, stated once in B4 | 18 | 18 × 0.6 ≈ 11 µs | — |
| `hashStmt` fact `stmtOk4` | 1 | `stmtDigest grp (stmt) = c` | for a segment: true by the reader's definition (`slotIn`'s `c := leafStmt (view)`, and `hashA`'s output *is* that digest: `hashA_leafStmt`); for the previous node: `hashB1/B2` blocks + `PubCells4`'s `c₁` | 0 | 0 | — |
| **cap reads** `piDigestAt` | 871 D | cap entry at witness index `k = j >> sib` | **no static binding**: §3 | §3: ≈ 40 k template rows (+7.8 k kind-mux rows counted above) | §3: ≈ 2.5 ms per prototype | writes `A`, the powers |
| foreign flags | 12 / 79 | ops `opOut` leaves foreign (`assertBit`, type-failed asserts, `.hashStmt`) | per op: a lemma on the generator (the flag is `true` on every run) or a row; list from `fors` in the dump | ≤ 100 | — | — |
| the ten replay registers | 10 | the slot's own ops | `R` (§6; S-E14's mechanism) | §6 | §6 | — |
| the run's existence | 1 | — | B4's theorem (§4), no rows beyond the above | 0 | 0 | — |

**Per-slot total of the pack map proper (4.4.1):** arena₁ 96,524 + arena₂ 85,946 + sibling 3,484
+ FS 934 + pins 8,907 + bits 16,531 + `input`/`stmt` 18 = **212,344 rows**, ≈ 277 k cells with
the cap check, against S-E13a's 63 k irregular rows. More rows, ≈ 10–20× less V: **≈ 3 ms per
prototype + 26 ms per node for the arena₂ link + 0.1 ms per slot** (§5.4), against ≈ 38 ms per
slot.

---

## 2. B1: the aggregate's unaligned segments — ruling recommendation (4.4.1)

**The fact.** `streamBytesOf seq4 = 1,482,752 = 64·23,168` (`chainLenOf_seq4`): a single proof's
stream is whole blocks today, so `traceBytes = segB − 1 ≡ 63 (mod 64)`, `≡ 15 (mod 16)`; segment
`i` of `0x54 ‖ tr₁ ‖ … ‖ tr_k` starts at byte `1 + i·(segB − 1) ≡ 1 − i (mod 16)`: every field of a
sub-slot `i ≥ 1` straddles two H elements (S-E13a B1). Any appended CapChk phase (§3) keeps
`traceBytes ≡ 63 (mod 64)` because every item after the seed has `slen ≡ 0 (mod 16)`
(`items_aligned`) and §3's phase is `≡ 0 (mod 64)`; the misalignment is the `0x54 ‖ seed` prefix,
so **no spacer-free variant exists** (PK-M1, PK-review Q7).

**Why no binding exists without re-alignment.** A byte shift inside F is GF(2)-linear, not
F-linear; the only encodings are the 128-bit decomposition (S-E13b's `r31` pattern, 130 rows per
element: `96,524 × 130 ≈ 12.5 M` rows per sub-slot, 12× a region) or Frobenius rows (same order).

**The options.**

| Option | Change | Owners | Cost |
|---|---|---|---|
| **R-A′ (S-E13a's form): `V_A` asks the spacer `absorbQ 0³² 0⁴⁹` (129 B) between consecutive segments** | `FRAgg.VAwith` (the spacer program between `segProgs`, `seqAll`), the reader (`sgn4`/`segTr`: spacer entries inserted, offset `1 + i·(segB − 1 + 129)`), `FRNodeKinds4` (`aggB k = 64·(24,133·k − 2)`, `aggL`, `tailIvs`), `FRNodeCircuit4.AggPad4` (`r = 64`), `FRNodeRows4Agg` (`padRows` without the element-7 decomposition), the spacer pins (9 elements per spacer: length word, tag, state, message), `VA_queries_le` (`4·qS + 3`), `qV` arithmetic, P2 | S-0′/FRAgg, S-E, P2 | `k − 1` queries, `129·(k−1)` stream bytes (+2 blocks per added segment, +6 per aggregate); `qV`: `4·8,907 + 3 = 35,631 ≤ 36,000` |
| R-B: pad `seq4` by one byte | every segment proof, R4/P4 positions | all | rejected: moves every position for the same effect |
| R-C: one digest chain per segment | the signed message, `FRAgg`, WOTS | all | rejected: the aggregate is one signed trace (B-11) |

**Ruling recommended: R-A′ at 129 B, with §3's CapChk block-aligned** (`≡ 0 mod 64`). With
`traceBytes = 1,544,383 ≡ 63 (mod 64)` the stride is `1,544,512 = 64·24,133` blocks and the
aggregate of `k` segments is `1 + k·1,544,383 + 129(k−1) = 64·(24,133k − 2)` bytes: **whole blocks
for every `k`** (`k = 4`: 96,530). Consequences, now true as stated: sub-slot `i`'s stream is
sub-slot 0's shifted by `24,133·i` blocks (so `kindS`/`wf` at `i ≥ 1` follow by S-E13a's lemmas
at the shifted element, and every per-slot row family is one family at a block offset); R-4-m2's
partial last block is gone: `AggPad4`'s `r = aggB k − 64(aggL k − 1) = 64`, so the candidate final
block `F_{a,k}` carries main block `aggL k − 1`'s message entirely (`h_in` = block `aggL k − 2`'s
output) and S-E13b's `padRows` lose their element-7 decomposition (−130 rows per candidate).
`aggChainLen_eq`'s residues (63/61/62) become 0. The spacer's query bytes are constants: 9 pin
rows per spacer on arena₁ (PK-m4); its answer is unused by `V_A` and unconstrained.

What does not move: `π_A`, `aggSegs`, `segView`, `VAwith`'s size check, the extractor's segment
parse, INT-10's size hypotheses (PK-m13); `seq4`'s positions (R-A′ is `V_A`'s program).

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
| (a) full paths to a single root (caps of size 1) | `seq4`: +9/8/8/8/7 node queries per position = +7,132 items (8,905 → 16,037); every position moves in R4/P4 | +14 k (mux rows) | +7,132 × 112 B = +12.5 k blocks (**+54 %**) | +228 KB −45 KB: **+183 KB** (+0.14 s S) | +0.7 ms | +0.67 s per N4 node (12.5 k × 5 × 10.8 µs) | — | **rejected**: N8 ✗, `qV = 64,092 + 3 > 36,000` (fits `2^16` barely) |
| (j) caps at depth 4 (16 entries) + mux | `seq4`: +3,648 items; caps 2.5 KB | +42 k (templated mux, `shared` class) | +6,384 blocks (**+28 %**) | +74 KB (+0.06 s) | ≈ 0 | +0.35 s per N4 | — | **rejected**: N8 ✗ |
| (j″) caps at depth 6 + mux | +1,906 items | +166 k | +3,336 blocks (**+14 %**) | +26 KB | ≈ 0 | +0.18 s per N4 | — | **rejected**: N8 ✗ |
| (j‴) caps at depth 7 | +1,035 items | +333 k | +1,811 blocks (+7.8 %) | +5 KB | — | — | — | rejected: rows ✗ (segment slot 725 k + 333 k + arenas > `2^20`), N8 ✗ |
| (b) a lookup argument with a prover-committed auxiliary (logUp inverses, a permutation) | a second Ligerito commitment after the challenge | small | — | — | — | +≈ 30 % | new | **rejected**: a second PCS instance per proof |
| (b′) LogUp-GKR (no second commitment) | a new multi-layer sumcheck phase in `seq4` (dummy in segments) | ≈ 10 k | +≈ 2 KB | +≈ 2 ms | small | small | new sumcheck family | not recommended: a new proof system for S-C/S-G, R4/P4 positions move |
| **(β) batched polynomial check with prover-supplied aggregated selectors** (§3.3) | **one final phase appended to `seq4`** (1 absorb of 61,472 B — `A` padded to a block-aligned phase — and 1 K squeeze); `piDigestAt` → static `piDigest`; `gen4`'s cap assert → the two identities; R4's `cols` and S-G's tail restated (§9.1) | **≈ 48 k** (templates: power chains, bit-products, shared-cell MACs, cap-bit kind-mux rows) | **+963 blocks (+4.2 %)** | **+61,472 B (+7.7 %; +0.03 s S)** | **+5–6 ms VM (+0.04 s S)** | computes `A` (trivial) | +2 rows `≤ 2^{-245}` | **adopt** |
| (c) the mux at depth 9 | none | 1.34 M | — | — | — | — | — | does not fit |

### 3.3 The construction (β) (4.4.1: block-aligned, `seq4`'s constants) — **SUPERSEDED by §11 (β′)**

> **Unsound as specified** (A3′, 2026-10-29): Q.i has no Fiat–Shamir item, so `cur_r` is chosen after `ζ` and `z`; §11 gives the sound form. Kept for the record of what A2′ built.

Reads `r = 0 … 870` in item order over the five levels, index `k_r = j_r >> sib_κ` (the cap's 9/8/8/8/7
bits), path output `cur_r` (a digest, 2 F halves), `cap` the 1,920 entries of the five caps
concatenated (`cap_i[k]` at `off_i + k`, `off = 0, 512, 768, 1024, 1280`).

- **Challenges.** `ζ ∈ K` := the first 32 bytes of P3.4's first squeeze (`kcAt es 4 0`): it follows
  every query (`fsStarts4`: P3.4 at entry 463, after Q.4) and is unused today (`finP3 4 = finP2 4`,
  "κ_c⁽⁴⁾ changes nothing"). `z ∈ K` := the CapChk squeeze. A fresh `ζ` buys nothing (PK Q1).
- **Proof.** A new field `A` (A.3 row 18, after the siblings): `A_{off_i+k} = Σ_{r at level i, k_r = k} ζ^r`,
  1,920 K elements = 61,440 B, **padded with 32 zero bytes to 61,472 B** so that the CapChk phase is
  `≡ 0 (mod 64)` in the stream (the absorb item `80 + 61,472 = 61,552`, the squeeze 80: 61,632 =
  64·963). `piSizeOf seq4`: **798,192 → 859,664**; `items`: **8,905 → 8,907**; the segment stream
  **1,482,752 → 1,544,384 = 64·24,131** (whole blocks kept: `chainLenOf_seq4`'s invariant).
- **The check (`V`, after `Pf`):** (I) `Σ_r ζ^r·cur_r = Σ_k A_k·cap[k]` (two identities, one per
  F half; `ζ^r·cur_r` a K×F product); (II) `Σ_k A_k·z^k = Σ_r ζ^r·z^{k_r + off_{lvl(r)}}`.
- **Soundness.** (II) is an identity of polynomials in `z` of degree `< 1,920` at a fresh `z`
  after `A` is absorbed: except with probability `1,919/2^256`, `A_k = Σ_{r: k_r = k} ζ^r` for all
  `k`. Then (I) reads `Σ_r ζ^r (cur_r − cap[k_r]) = 0`, a polynomial of degree `≤ 870` in `ζ` whose
  coefficients are fixed by items `≤ Q.4`, before `ζ`: except with probability `870/2^256`,
  `cur_r = cap[k_r]` for every `r` — today's per-position `assertEq`. Both are per-fresh-query rows
  `≤ 2^-245`; the maximum row stays P2's `2^-120.36`; **`εR = 15/2^124` and `claim.json` are
  unchanged** (PK-m5).
- **`V` (`gen4`):** per position, `piDigestAt; assertEq` → `acc_I += ζ^r·cur_r`, `acc_II += ζ^r·zpow[k_r + off]`
  with `zpow[k]` a native power table (1,919 K products once; indexed, not bit-products: PK-m11),
  `ζ^r` by one chain (870); after CapChk `Σ A_k cap[k]` (3,840 K×F), `Σ A_k z^k` (1,920 K): ≈ 8.5 k
  K-equivalents ≈ 3 F products each ≈ **5–6 ms VM**. The native `acc` follows the dump.
- **Circuit (per slot, keyed templates):** the `ζ^r` chain (871 K: 2,613 rows), `z^{2^b}` (11 K
  squarings: 33), `z^{k_r + off}` as `z^{off}·Π_t (1 + c_t·(z^{2^t} − 1))` over the 9 cap bits
  (27 rows × 871 = 23,517; the cap bits are **kind-muxed** linear rows `c_t = Σ_κ s_κ·L(p·maxb + sib_κ + t)`,
  9 per read = 7,839: PK-m3, §5.2), `ζ^r·cur_r` and `ζ^r·z^{k_r}` (871 × 5 = 4,355), `A_k·cap[k]`
  and `A_k·z^k` (1,920 × 5 = 9,600; `A`/`cap` at fixed arena₁ addresses: the `shared` class), the
  sums linear: **≈ 40 k + 7.8 k rows per slot**, `local`/`shared` classes, ≈ 2.5 ms VM per
  prototype at 0.06 µs.
- **Items:** `seq4` gains phase 52 `CapChk = [absorb fA 61,472; squeeze z]` after `Pf` (A.4 row
  48): FS entries 468 → 470 (`fsStarts4` entry 470, `phOf_ge`'s `468`/`51` → `470`/`52`, `DT 52`).

### 3.4 Fit and costs of (β) with R-A′ (4.4.1)

- **N8's H** (`hUsed_eq`: 187,540 = 2·92,672 + 2,196; the bound is `lBase ≤ 196,608 − 1,024 =
  195,584`, `lBase = ⌈hUsed/256⌉·256`, `hEnd = hUsed + 8 ≤ lBase`): chains `2 × 96,530 = 193,060`,
  `hUsed = 195,256`, `hEnd = 195,264`, `lBase = 195,328`: **fits, 256 blocks to spare (0.13 %)**.
  Nothing else may enter N8's H; a future stream byte must come out of `A` (e.g. caps at depth 8
  at level 0 trade 8 KB of `A` for 9 KB of siblings: no). N4: `hUsed` 117,589 → 122,410
  (previous node 24,131, aggregate 96,530, 1,749 fixed). N2: 24,131 + 2·24,133 − 2 + fixed.
- **`|π|`:** 859,664 B, `x_size = 0.4099` (was 0.3806): **+0.03 s of `V̄`** at `x ≈ 1.4`
  (`dV̄/dx = 0.2667·3x² ≈ 1.57`). **V:** +5–6 ms VM ≈ +5 ms runner: +0.04 s. **Total ≈ +0.07 s of S.**
- **Prover.** Segment: `A` is 871 K additions; the absorb ≈ 0. Node: +963 H blocks per slot
  (`24,131 − 23,168`) × 10.8 µs ≈ +10 ms per slot, +0.05 s per N4 node.
- **What moves (PK-M2, PK-m10) — a restatement, not a re-run:** `FRTranscriptDefs` (`items`,
  `fA`, `piSize`, `streamBytes`, the shape `decide`s), `FRFormat`, `FRShape4`
  (`itemsOf_seq4_length 8907`, `piSizeOf_seq4 859664`, `streamBytesOf_seq4`, `chainLenOf_seq4
  24131`, `traces_le_qV` at `4·8,907 + 3`), `FRVIR4`/`FRVIR4Mux` (`posOpsG` accumulators,
  `capChkOps`), `FRVIRFinals4` (`finCap`), `FRX4Prog.szPs`/`FRX4Ext` (the `798192` literal), S-H4's
  `reassemble` (row 18), `FRSoundness4Pos` (`fsItems_length 470`), `FRNodeRead4`
  (`segTr_length`/`slotTr4_length` 8,907), **R4** (`FinLog4.cols`/`FinRest4.cols`, `ys_facts4`/
  `cols4_of_run`: §9's exact statements), **S-G** (`D_ζ`, `D_z`, `DT 52`, `truthCap`, the bridge
  into `truthP3_four_of_cols` and the level-`i` `DP3 i`: §9), P2 (`ir.rs`, `prover.s`: `A`, the
  spacer), L-circ (`tplPowChain`, `tplBitPow` kind-muxed, `tplMacShared`). Positions before `Pf`
  do not move, so P4's position lemmas re-run unchanged.

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

### 5.2 The two arenas (M-relative, **in the slot's own region**; the same addresses in both prototypes) (4.4.1)

PK-M3: the arenas must sit in the region of the slot whose prototype reads them, or
`InSlot`/`ProtoFit`/`slotV4`'s copy identity fails and prototype 0's consuming rows become
per-slot irregular. So **every slot's region holds its prototype, its arenas, the bit rows and the
cap-check templates at the same M-relative offsets; the previous-node slot's *spare* region holds
only `R` and the `evalM` replay** (keyed closed forms that may read region A's cells, as S-E14
planned). `R`'s cells stay at S-E14's `[2^19, 2^20)` of the spare region; the arenas take the
prototype's region's cells `[190,584 + …, 2^19)`: arena₁ 96,524 + arena₂ 132,096 allocated + bits
8,320 + cap-check cells ≈ 40 k ≈ **277 k cells**, packed above the prototype's 190.6 k without the
`2^17` alignment of 4.4 (`A₁`'s diagonal then carries a constant offset: the shift-by-constant
automaton on the M side too, +160 products per slot).

| Region (M-relative cells of the slot's own region) | Size | Content | Bound by |
|---|---|---|---|
| **arena₁** `A₁ + e`, `e < 96,524` | 96,524 cells | stream element `e` | copy rows `R₁ + e : one·(M(A₁+e) − H(sCell b0 e)) = 0` |
| **arena₂** `A₂ + lvlBase_i + p·2^{a_i} + q`, `q < S_i` (`S = 147/92/78/64/57`, `2^a = 256/128/128/64/64`; level 3 has no slack) | 132,096 allocated, **85,946 used** (PK-m1: `Σ_i t_i·S_i`) | position `p` of level `i`, its `S_i` elements in stream order | M-to-M copy rows `R₂ + … : M(A₂ …) = M(A₁ + E_i + S_i p + q)` |
| the FS items' elements | — | read in arena₁ at fixed addresses (`shared` class) | — |
| **position bits (L)** | the 7,552 L bits per slot, laid **bottom-aligned per position**: bit `h` of position `p` at `L(p·maxb + h)` (kind-independent for `bitOf j h`); the cap bits `sib_κ + t` are kind-dependent and reach rows through 9 kind-mux linear rows per read | — | the 62 answers' 256 bits tied by **3 gated decomposition rows per half** `s_κ·(H − Σ_j x^j b_{π_κ(j)}) = 0` (372 rows) over the L bits and 8,320 M Boolean cells |
| the **sibling** | no cells: the per-kind form `l + r + v` with `v = a·cur` (`a` the activity selector of the depth: at a dummy depth `v = 0`, so the form is `0` as `assertZero` demands; PK-M4/PK-m3) | — | 2 product rows per kind-varying depth per position: `871 × 2 × 2 = 3,484` rows |

- **`selectHalf` and `keep` stay as compiled** (PK-M4): the mux rows are already gated by
  construction (`muxOut`), and an ungated replacement forces `cur = 0` at dummy depths. The 4.4
  "−15 k" saving is withdrawn; only the sibling *import cells* go (−15,104 cells).
- **Why two arenas** (unchanged): arena₁ gives the per-slot H bind as a stride-(1,1) diagonal,
  `O(log)` per slot; arena₂ gives the templates power-of-two instance strides. The arena₁↔arena₂
  link is M-to-M at the same addresses in both prototypes, so its low-coordinate MLE is one
  value per node.

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
   `eq(u_hi, (X_p + q)_hi)` for the two possible carries): per bit 4 states × 2 transitions ×
   (a τ-factor, a u-factor, an accumulate) ≈ 16 products, 8 bits, plus the high part ≈ 24:
   **≈ 150 products per instance** (PK-m2; 4.4's 60 counted the transitions only). Total
   `871 × 150 ≈ 131 k products ≈ 26 ms`, **once per node** (both prototypes share it). The
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
| arena₁ ↔ H | 96,524 | 58 ms per slot | 0.1 ms per slot |
| arena₂ ↔ arena₁ | 85,946 | 52 ms per slot | **26 ms per node** (150 products × 871 instances; 52 at a 2× miss) |
| sibling rows, FS links, pins, bit rows, cap-check templates | ≈ 78 k | 47 ms per slot | ≈ 3 ms per prototype (0.03–0.06 µs/row, PK-m8) |
| **N4 (5 slots, 2 prototypes)** | | **≈ 785 ms** (S-E13a's 40 ms/slot was for 63 k rows without the cap check: 200 ms) | **≈ 33 ms VM** (59 at a 2× miss on the automaton) |

The automaton's 150 products per instance is a transition count at 0.2 µs per F product; it is
the largest single line of §6.3 and the first thing B2′ must measure. The row cost is the price:
≈ 252 k rows and ≈ 277 k cells per slot (§6).

---

## 6. The integrated feasibility: pack map + `R` against `N_M` and V

### 6.1 Rows per slot region (`2^20 = 1,048,576`; prototypes measured, `logs/S-E13a/nodedump4-run.log`) (4.4.1)

| Part | Previous-node slot, region A | Segment slot | Source |
|---|---|---|---|
| prototype as compiled (`selectHalf`/`keep` kept; the sibling and cap imports lose cells only) | 730,493 | 725,885 | measured |
| arena₁ 96,524 + arena₂ 85,946 + FS links 934 (467 items × 2) + pins 8,907 + bit rows 8,320 + 372 + cap-bit kind-mux 7,839 + sibling rows 3,484 + `input`/`stmt` rows 18 | 212,344 | 212,344 | §1.3, §5.2, PK-m1/m3/m7 |
| cap-check templates (§3.3) | 40,000 | 40,000 | |
| link region (S-E12c rows; WOTS/`aggPad` 8–8.7 k and `aggChk` ≈ 2.7 k at slot 1) | 32,768 reserved | 32,768 reserved | |
| **total, one region** | **1,015,605 (96.9 %)** | **1,059,997 ✗ (101.1 %)** | |
| S-E6 §5's two prototype levers (`phiRS` 134-in-256 pieces −62 k; skeleton padding −29 k): **track B0, a prerequisite of B2′** | −91,000 | −91,000 | PK-M4 |
| **total with B0** | **924,605 (88.2 %)** | **968,997 (92.4 %)** | |
| **spare region (previous-node slot only):** `R` without `evalM` 221 k + `evalM` replay 330–400 k (§6.2, the child's WOTS/`aggPad`/link/`aggChk` replay included: PK-M6) | 551–621 k (53–59 %) | — | S-E14, §6.2 |
| `R` without `evalM` (segment: after C2 drops the dead `evalM`/`evalL`) | — | 49,000 **(inside the 968,997 above)** | S-E14 |

**The segment slot does not fit without B0** (1.1 % over); with B0 it is at 92.4 %. **The
previous-node slot keeps one region for its prototype + arenas and one spare region for `R`** —
no change to `nodeLayout4`, `N_M`, the mux or `lSlots`; `NodeKind.mSlot`, `InSlot`, `hfit4`'s
"selector copies below `oneCell + vslots·2^20`" bound and `ProtoFit`'s check learn that region
`vslots` (N2: 3, N4: 5) is slot 0's spare. `mRows4_le` (stale `protoRowsN = 551,805`) is re-based
on the measured prototypes or retired in favour of `ProtoFit` per region (PK Q4).

| Kind | Regions used / available | Rows used (with B0) | `N_M/1.05` | Margin |
|---|---|---|---|---|
| N2 (`m = 31`, `2^22`) | 1 + 1 + 2 = 4 / 4 | 925 k + 571 k + 2 × 969 k = 3.43 M | 3.99 M | 1.16× |
| N4 (`m = 32`, `2^23`) | 1 + 1 + 4 = 6 / 8 | 1.50 M + 4 × 969 k = 5.37 M | 7.99 M | 1.49× |
| N8 (`2^23`) | 8 / 8 | 8 × 969 k = **7.75 M** (without B0: 8.48 M ✗) | 7.99 M | **1.03×** |

N8's margin is thin; the levers in reserve for it, in order: (i) arena₂ restricted to the
elements templates consume (the 3 padding elements per column item: −2,613 rows; the node items'
`len‖tag` elements pinned on arena₁ instead: −7,552 rows at +4.5 ms per prototype); (ii) the
cap-check bit-products as 3 sub-templates per kind instead of kind-mux rows (−7.8 k, +47 k: no);
(iii) `segSlots N8 = 7` (§8: not needed on the figures above).

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
| `evalM` replay | 330–400 k | u-rows share `Ĉ` with the parent's own keys (free), v-rows/sums `O(log)`, the arena₂ automaton key (871 instances), the sparse companions **if templated**, the child's WOTS/link rows **if C0 templated them** | **≈ 7–15 ms**; +25 ms if the sparse skeleton stays sparse (S-E12b's lever not built); +10–18 ms without C0 (PK-M6) |

### 6.3 The V budget on the measured basis (PK-M5) (4.4.1)

**Basis.** S-I's season run 40809858010 on the 7763: `v_ref = 206.6 ms` (`T_triv/10`), `V_i =
143.6–162.4 ms, mean 157.9`, `|π| = 798,192`, `x = 157.9/206.6 + 0.3806 = 1.145`, **`V̄ = 0.400 s`**
(HEAD `48d25ef`: before S-E13a/b's rows and before `R`). Every Δ below is added to **157.9 ms
runner** (≈ 188 ms VM at 1.19); S-E13a/b's +30 ms VM are replaced by this layout, not added.
`dV̄/dV = 0.2667·3x²/206.6 ≈ 0.0076 s per runner ms` at `x ≈ 1.4`.

| Part (VM ms) | best | worst | Note |
|---|---|---|---|
| arena₁↔H `O(log)` per slot (5 slots) | 0.5 | 1 | §5.3 item 1 (+160 for the M-side offset) |
| arena₂↔arena₁ shift-window automaton, **150 products per instance** (PK-m2), 871 instances, once per node | 26 | 52 | 4.4 said 10.5 (60/instance) |
| position templates, FS links/pins, bit rows (≈ 2 × 70 k structured rows at 0.03–0.06 µs) | 5 | 8 | PK-m8 |
| cap check: V's own identities 5–6 + templates 2 × 2.5 | 11 | 14 | §3.3, PK-m11 |
| `R` without `evalM`, keyed (§6.2) | 7 | 14 | 130 if left as sparse pieces |
| `evalM` replay (D1) | 7 | 15 (+25 if the sparse skeleton is not templated) | needs S-E12b's lever |
| the child's WOTS/`aggPad`/link/`aggChk` rows in the parent (after C0 templates them) and in `R` | 4 | 20 (without C0: 7 + 10–18 muxed ×3) | PK-M6 |
| **ΔV (VM)** | **60** | **124 (149)** | |
| **ΔV (runner, ÷1.19)** | **50** | **104 (125)** | |
| V runner | 208 | 262 (283) | |
| `x = V/206.6 + 0.4099` | 1.417 | 1.678 (1.780) | |
| **`V̄ = 0.2667·x³`** | **0.76** | **1.26 (1.50)** | today **0.400** |
| **Δ`V̄` = ΔS (V side)** | **+0.36** | **+0.86 (+1.10)** | |

Plus the prover side: +0.05 s per N4 node for the longer stream (≈ +0.03 s of P̄). **The price of
a sound node on the measured basis is ≈ +0.4 s of S at best, +0.9 s as the worst case of every
line, against S = 6.42.** The two largest and least certain lines are the arena₂ automaton (26–52)
and the replays (11–35); S-T1's F-side kind factor and S-E11's `evalM` levers (−25 ms VM, outside
this memo) would recover ≈ 0.16 s. 4.4's "+0.1 … +0.2 s" mixed `v_ref = 177.8` (changes 28's
"today") with 206.6 and is withdrawn.

### 6.4 Options the orchestrator asked to be weighed

| Option | Effect | Verdict |
|---|---|---|
| (1) closed forms per op (§6.2) and the two arenas (§5) | the design above: every `R` op and every import keyed; ΔV +60 ms VM best (§6.3); a spare region for the node slot's `R` | **recommended** |
| (2) move the child's `evalM` into the parent's PIOP (S-E6 §4 (c)): the child's `evalM(r_E2, r′)` claim becomes a point claim the *parent's* E-phase proves — the parent's lincheck is run on the matrix `[M_parent ; R-free]` with a second evaluation point folded by `κ_E` | removes `R` proper (−330–400 k rows, −7–58 ms V, the fixed point gone) at +1 E-phase (23 F rounds, +1,104 B of π, +≈ 2 ms V) — **but** the child's point `(r_E2, r′)` is witness (H cells), and a sumcheck at a witness point is not a lincheck: the parent would prove `Σ_x eq(r_child, x)·M(x)·…` with `eq(r_child, ·)` a *witness* table — a degree-3 sumcheck over `2^23` cells with a witness multiplier: 23 rounds of degree 3, and the eq table itself (2^23 K) is never materialised; the verifier's final check needs `eq(r_child, r_parent)` — computable from the H cells. Sound and standard ("proof-carrying" evaluation), but a new phase in S-C/S-G and the prover (+1 lincheck ≈ +0.3 s per node) | **the reserve** (§8): take it if (1)'s `evalM` replay measures above §8's kill line (25 ms VM) |
| (3) smaller children (`m = 31` segments only, `L32` dropped) | `R` unchanged in structure; the item sequence shrinks (positions 290 → fewer bits, same `t_i`), stream −3 %: nothing structural | no |
| (4) a second region for the previous-node slot | adopted for `R` and the `evalM` replay only (§6.1); the prototype, arenas and cap check stay together in the slot's own region (PK-M3) | adopted as corrected |
| (5) a different recursion shape (no previous-node slot: every step's node verifies only segments, the chain of nodes replaced by a tree) | removes prototype 0's `R` entirely (−221–540 k rows, −14–55 ms) but PR #20's step relation needs the previous node's acceptance in the step's witness (`Rel`'s node clause); a tree of nodes brings back 3.x's `P30`/tree costs (B-1 withdrawn) | no |
| (6) the `evalL` replay at `lRows4`'s `2^14` strides as 64-row chunks (S-E14's 125 k) | fits V only as the automaton key | subsumed by (1) |

---

## 7. Build plan (4.4.1: the review's corrected order, with the build budget)

Owners as in the blueprint's §7 ("L-circ" is S-E). Every stage records its modules' CPU-s
(`lean -DElab.async=false --profile`, one core) in its RESULT and re-measures `plan4t init`
(PK-m6); the kernel stays structural (inductions along the compile trail; the `decide +kernel`
facts on `seq4` stay on shape parameters).

| # | Stage | Modules (existing: S-I CPU-s from `logs/S-I/run-40810876665/build-modules.txt`) | Depends on | Delivers | Δ CPU-s (estimate, §7.2) |
|---|---|---|---|---|---|
| A2′ | CapChk, block-aligned (§3.3) | `FRTranscriptDefs` 17, `FRFormat` 4.4, `FRShape4` 23, `FRVIR4` 11, `FRVIR4Mux` 8.1, `FRVIRFinals4` 25, `FRX4Prog` 5, `FRX4Ext` 9.2, `FRSoundness4Pos` 16, S-H4's `reassemble` | — | `piDigestAt` gone; `items 8,907`, `piSizeOf seq4 859,664`; dumps regenerate | +10 |
| A1′ | R-A′ at 129 B (§2) | `FRAgg` 15, `FRNodeKinds4` 14, `FRNodeCircuit4` 6.2, `FRNodeRead4`, `FRNodeRows4Agg`, `FRNodeRows4Pack` (spacer pins), `FRVerifier4` | A2′ (the stride) | whole-block aggregates, spacer entries in the reader, `4·qS + 3` | +8 |
| A3′ | the restated `cols` and the two dooms (§9.1) | `FRSoundness4R4Tail` 2.3, `FRSoundness4R4Cols` 3.0 (+Ctrl 2.3), `FRSoundness4TailTruths` 7.3, `FRSoundness4TailD` 18, `FRSoundness4TailLig` 11, `FRSoundness4R4Run` 6, `R4Ref` 15, `R4Acc` 2.7 | A2′ | `truthCap` from `¬D_ζ ∧ ¬D_z`; the tail composes again | +20 |
| B0 | S-E6 §5's prototype levers | `FRVIRCompile` 26 (`CS.align` for `phiRS` 134→ a 134-row piece in 256 with the gap used, the skeleton padding), `FRNodeRows4Hint` 3.3, `FRNodeRows4Model` | — | prototypes ≤ 640 k rows each (measured) | +3 |
| B1′ | compiler aliases | `FRVIRCompile` 26, `FRVIRCompileSound` 7.3, `FRVIRTplKMux` 5.3 | A2′, B0 | `Params.Arena`; `piElem`/`piDigest`/`askX`/`chF`/`chK`/`input`/`felems` as alias forms; `bitOf` L slots; the sibling's per-kind form; `compileX_soundK` with `ArenaOk` | +15 |
| B2′ | arenas, links, pins, bits, cap-check templates in the slot's own region (§5.2) | `FRNodeRows4` 6.9, `FRNodeRows4Fit` 14, `FRNodeRows4Plan` 9.5, new `FRNodeRows4Arena`, `FRVIRTplArena` (three automata + `tpl_mle`), `FRNodeRows4PackSound` | B1′ | `evalMT4_eq` re-proved; V and plan time measured | +55 |
| C0 | template S-E13b's WOTS/`aggPad`, S-E12c's link rows, B4's `aggChk` rows | `FRNodeRows4Wots*` (12 modules, S-E13b), `FRNodeRows4Ext` | B2′ | their `Ĉ` closed (parent 7 → 2 ms; `R` −25 k rows) | +15 (−12 if `xRows_length`'s 11.7 s `simp` goes) |
| B3 | `compileFromX_run`, `AskBound`, `gap4Imp_of_arena`; the 12/79 foreign flags listed and discharged | new `FRNodeRows4Run`, `FRNodeSound4R`, `FRNodeRows4PackSound` | B2′, A2′ (`reassemble_field`) | `Gap4 = aggChk (c)` | +30 |
| B4 | `aggChk (c)` (views' chaining/sum/end/cap; PK-m7's `hashA`/`hashB` rows stated once) | `FRNodeRows4Agg` | A1′, B2′ | `Gap4 = ∅` | +10 |
| C1 | the six `R` keys (§6.2) | `FRNodeRows4Rep*`, `FRVIRTpl*` | B2′ | `SlotImpR` down to `evalM` | +60 |
| C2 | drop the segment group's `evalM`/`evalL` | `FRVIR4Mux` | — | prototype 1's six dead imports gone | 0 |
| **D1 / §8** | the `evalM` replay in the spare region **or** the §8 reserve — decided on §8's kill line | `FRNodeRows4RepM` (new) or S-C/S-G's new E instance | C0, C1, S-E12b's levers | `SlotImpR = ∅` | +40 / +60 |
| E1 | P2 | `prover.s`, `ir.rs` | A, B, C, D | the honest node witness; the completeness KAT | — |
| **RET** | changes 27 (B) steps 2–4, RET-3, G2 | the 3.x extractor/front/shapes | can run from A on | build CPU −575 … −625 (27 (B)), G2 on the 43 `FRX*` (804 s) | −900 … −1,000 |
| F | S-I | `Solution`, `claim.json` unchanged (`ε`, `qV = 36,000`) | all | **`evaluate.py cert` ≤ 600 s is part of done**, not only `HARNESS: ACCEPT` | — |

### 7.1 Track briefs (for the orchestrator to start A2′, A1′, A3′, B0)

**A2′ — CapChk (S-0′ / FRTranscriptDefs).** Modules: `FRTranscriptDefs` (`fA := 18`, `nFields 19`,
`piopPhases` unchanged, a new `capChkPhase : Phase := ⟨"CapChk", .absorb fA 61,472⟩` followed by
`⟨"CapChkZ", .squeezes 1 (.one fun _ => true)⟩` appended after `finalPhase`; `streamBytes_eq`,
`items_aligned`'s successor lemma, `fsStarts` entries 469–470), `FRFormat` (`fieldSize fA = 61,472`,
`piSize = 859,664`), `FRShape4` (`itemsOf_seq4_length : 8907`, `piSizeOf_seq4 : 859664`,
`streamBytesOf_seq4 : 1544384`, `chainLenOf_seq4 : 24131`, `qV4`'s `traces_le_qV` at
`4·8907 + 3 ≤ 36000`), `FRVIR4Mux`/`FRVIR4` (`posOpsG`: replace `shrN; piDigestAt; assertEq` by
`shrN k; mulKF ζpow_r cur → t; addK acc_I t; mulK ζpow_r zpow[k + off] → t'; addK acc_II t'` where
`ζpow_r` is a chain register and `zpow` is read by a new op `powIdx z k` (V: a table lookup; the
template: the bit-product), `finalOps4` gains `capChkOps`: `piElemK fA 32k → A_k` (1,920 reads),
the two sums, `assertEq acc_I Σ A_k cap[k]`, `assertEq acc_II Σ A_k z^k`), `FRVIRFinals4`
(`finCap` as a `Finals` field over `OpImpl`), `FRX4Prog.szPs`/`FRX4Ext` (the `798192` literal and
its lemmas → `859664`), S-H4's `reassemble` (row 18 `A` from the CapChk absorb's payload, bytes
`0 … 61,440`). Statements that change: every literal above; `kcAt es 4 0`'s first 32 bytes are
read as `ζ` by a new `zetaAt es : K`. Definition of done: `lake build FR` green with the regenerated
dumps (`ops-*.txt`, `items.json`); `streamBytesOf_seq4 = 64·24,131` by `decide +kernel` on shape
parameters only; the S-F4 dumps' KAT; the dump's CapChk item at FS entries 469–470; the plan-form
KAT (P2⁗) re-run; CPU-s of each module in the RESULT.

**A1′ — R-A′ (S-0′ / FRAgg, S-E reader).** Modules: `FRAgg` (`spacerQ := absorbQ (Vector.replicate
32 0) (List.replicate 49 0)`, `spacer : OProg Bool := .ask spacerQ (fun _ => .ret true)`;
`VAwith` runs `seqAll (intersperse spacer (segProgs …))`; `VA_sound`'s `trs` gains the spacer
entries between the segment runs; `VA_extract`/`VA_extract_on`/`VA_complete` through it;
`VA_queries_le : … ≤ 4·qS + 3`; `seqAll_queries_le` unchanged), `FRVerifier4` (`V4_queries_le`,
`ks_queries4` at `35,631`), `FRNodeKinds4` (`segB := 1544384`, `cLen := 24131`, `spacerB := 129`,
`aggB k := 64·(24133·k − 2)`, `aggL k := 24133·k − 2`, `aggL_eq`, `tailIvs` targets
`streamTarget (aggB (j+1)) (aggL (j+1) − 1)`), `FRNodeLayout4` (`aggChainLen`, `hUsed_eq`:
N2/N4/N8 recomputed, `regions_fit`), `FRNodeRead4` (`segTr κ σ k i w` at offset `1 + i·(segB − 1 +
129)`; `sgn4`'s aggregate trace = `intersperse [(spacerQ, answer read at the spacer's offset)]`
over the sub-slot traces), `FRNodeCircuit4` (`AggPad4` with `r = 64`: the message-prefix clause
is the whole block), `FRNodeRows4Agg`/`FRNodeRows4Wots` (`padRows` without the element-7
decomposition; `lastR k = 64`), `FRNodeRows4Pack`/`FRNodeRows4` (`packB` for every sub-slot at
`b0 + 24133·i`; 9 pin rows per spacer: `enc64 89 ‖ "FRABS000"`, the 32 zero state bytes, the 49
zero message bytes, as whole elements), `FRNodeRows4PackSound` (`kindS`/`wf` at `i ≥ 1`:
`chainBytes4_elem` at the shifted element). Definition of done: `Gap4R` loses `kindS`/`wf` at
`i ≥ 1`; `aggChainLen_eq`'s residues are 0; `hUsed_eq` N8 = 195,256 and `regions_fit` by
`decide` on the literals; the row dump's spacer pins; the aggregate control (`ctrlA_*`) with
spacers; CPU-s recorded.

**A3′ — the restated `cols` and the two dooms (one owner for R4 + S-G).** Modules:
`FRSoundness4R4Tail` (`FinLog4.cols`/`FinRest4.cols` as in §9.1 (a)), `FRSoundness4R4Cols`
(`ys_facts4`/`cols4_of_run` produce the computed `d_{i,q}` and `capChk4 es` from the finals'
`finCap`; `capDig_eq4` unchanged), `FRSoundness4TailTruths` (`truthCap`, `D_ζ`, `D_z`),
`FRSoundness4TailD` (`DT 52 := D_z`, `finCap` in the phase table, `phOf_ge : 470 ≤ p → phOf4 p =
52`, `fsStarts4` entry 470, the Pf doom's background hypothesis replaced by `truthCap`),
`FRSoundness4TailLig` (`truthP3_four_of_cols` and the level-`i` `colOf_of_path`/`foldAt_of_cols`
take `truthCap` as the hypothesis; `cap_of_chk : accept es → ¬D_ζ es → ¬D_z es → truthCap es`),
`FRSoundness4R4Run`/`R4Ref`/`R4Acc` (re-run with the tabled `finOps4` + `capChkOps`). Statements
that change: §9.1 lists them verbatim. Definition of done: `ks_rev4GR` (or its successor) builds
with the same `ε` (`εR = 15/2^124`, the row table gains `D_ζ 870/2^256`, `D_z 1919/2^256`); the
controls `dZeta_ctl` (a wrong `cur_r` at a bad `ζ` is in `D_ζ`), `dz_ctl`, `capChk_pos`
(an honest `A` passes) and `capChk_neg` (a wrong `A_k` fails (II) at a generic `z`); CPU-s
recorded; `FRSoundness4TailD`'s 18 s does not grow by more than the one new phase.

**B0 — the prototype levers (L-circ).** Modules: `FRVIRCompile` (`CS.align`'s policy: a template
of 134 rows aligned to 256 wastes 122 rows per instance — allocate `phiRS`'s 512 instances at a
134-row stride inside one 2^16-row piece with `instRows` padded to 136 (= 8·17) and the evaluator's
instance eq over `inst·136` by the stride-136 range form, **or** keep the 256 alignment and fill
the 122-row gap with the next key's instances; the skeleton's inter-group padding (`29,142` rows,
S-E6 §5) removed by aligning only groups above `2^12` rows as S-E6 did for templates),
`FRVIRTplFast`/`FRNodeRows4Plan` (the evaluator's instance stride), `FRNodeRows4Hint`
(regenerated by `LayDump4`), `FRNodeRows4Model` (`protoRowsN := the measured value`). Statements
that change: none in the soundness chain (`compileT_sound` holds at any layout; `ProtoFit` is
checked at process start); `mRows4_le` re-based. Definition of done: `nodedump4-run.log` shows
each prototype's region ≤ 640,000 rows (today 730,493 / 725,885: −91 k is the target, −62 k the
minimum for N8's fit at `segSlots = 8`); `inR true`; `evalMT4` not slower than S-E12c's 84–90 ms;
`plan4t init` ≤ 2.0 s; CPU-s recorded.

### 7.2 The build budget (PK-M7)

S-I: 2,975 CPU-s over 307 modules (`build-modules.txt`), `lake build FR` 882 s wall against
`build_s = 600`; the target is ≤ 2,020 CPU-s (≤ 1,550 for 1.3×). The 12 modules ≥ 30 s are 533 s,
eleven of them `FRX*`. Not in that run (HEAD `48d25ef`): S-E13a's six modules (≈ 50 CPU-s by their
profiles, 88 s wall minus imports), S-E13b's twelve (≈ 80; `FRNodeRows4Ext` 11.7 s of kernel for
one `simp` length proof), S-E14's three (≈ 35): **+165 already queued**. This plan's Δ column
sums to **+265 (D1) / +285 (reserve) CPU-s**, by S-E13a/b's measured rate for modules of the same
shape (an automaton `tpl_mle` ≈ `FRNodeRows4Fit`'s 14–25 s; an `RT` with `RTOk` ≈ S-E14's 10–12).
So the build arrives at **≈ 3,400 CPU-s before retirement**, and must lose ≈ 1,400 to reach
2,020: changes 27 (B) steps 2–4 (−575 … −625, estimated there), G2's golf of the 13 `FRX*`
decoder modules (their 804 s: −250 … −350 at G1's measured −43 %), the retirement of the 3.x
`FRX` node extractor (step 2, inside the 575), `xRows_length`'s 11.7 s and S-E13b's per-row
`simp`s (−20). **That reaches ≈ 2,400–2,500, not 2,020**: the certificate stays over `build_s`
by ≈ 20 % unless the organiser raises `build_s` (QUEUE's open question: ask it now, with these
numbers) or the 3.x decoder infrastructure (`FRXBary` 69, `FRXMsg` 54, `FRXAgree` 53, `FRXOut` 47,
`FRXRead` 46: 269 s) is replaced by S-H4's smaller decoder. F's definition of done is therefore
`evaluate.py cert ≤ 600 s`, and RET runs in parallel from A2′ on, not after D1.

---

## 8. The scope decision on the measured basis (PK-M5)

**D1 (the `evalM` replay) against the reserve (the child's `evalM` claim in the parent's E-phase):**

| | D1: replay in the spare region | Reserve: a second E instance at the child's point |
|---|---|---|
| V (VM) | 7–15 ms best, +25 if the sparse skeleton stays sparse, +10–18 for the child's WOTS rows without C0: **7–58** | ≈ 2 ms (23 rounds of a degree-3 sumcheck, `eq(r_child, r_parent)` from H cells) |
| Δ`V̄` at `x ≈ 1.4` (0.0076 s per runner ms) | **+0.045 … +0.37 s** | **+0.013 s** |
| `|π|` | 0 | +1,104 B (23 F rounds × 48): +0.0008 s |
| Prover | `R`'s cells (one pass over the run) ≈ 0 | one more lincheck per node: +≈ 0.3 s per N2/N4 node; a step is ≈ 8.9 s: **+0.2 s of P̄** (every step has a node) |
| Rows | 330–400 k in the spare region | 0 (the spare region holds `R`'s 221 k only) |
| ε | 0 | one new per-fresh-query row `≤ 3/2^128` per round within `εR` (PK-m9) |
| Lean | `replay_mle`/`replay_sound` + the fixed point (S-E6 §4's blocker, unproved so far), S-E12b's two levers, ≈ 40 CPU-s | a new sumcheck family in S-C (a witness multiplier, `FRSumcheck` generic) + an S-G phase + R4/P4 positions for a new phase in `seq4` (every node proof grows a phase; the segment proofs carry it as dummies), ≈ 60 CPU-s |
| Score, best → worst | **+0.05 → +0.37 s** | **+0.21 → +0.25 s** |

**Decision.** D1 first, with a **kill line: if the `evalM` replay's measured `evalMT4` cost
exceeds 25 ms VM (≈ +0.16 s), or `replay_mle`'s fixed point is not closed within C1's budget,
switch to the reserve.** Below the line D1 wins by ≈ 0.1–0.2 s and keeps the PIOP as it is; above
it the reserve wins and also removes the fixed point for good. The reserve's protocol change must
be priced into A2′'s item sequence *now* only if we want its phase appended at the same time as
CapChk (one dump regeneration instead of two): recommended if the orchestrator expects the kill
line to be hit; otherwise it is appended later at the same cost.

**N8 with 7 segment slots: not needed.** With B0's −91 k N8 is at 1.03× under `N_M/1.05` and its
H has 256 blocks to spare (§3.4, §6.1). `segSlots N8 = 7` stays the fallback if B0 delivers less
than −62 k (the point where 8 × segment slot exceeds `N_M/1.05`).

---

## 9. The restated statements (PK-M2), ε accounting, and open questions

### 9.1 R4's `cols` and S-G's dooms — exact statements — **SUPERSEDED by §11.4–§11.5**

> `D_ζ` as stated here is not prefix-determined (`pathDig es i q` is a function of π, not of the chain). §11.5 restates it over the committed field `D`.

Today (`FRSoundness4R4Tail`): `FinLog4.cols` / `FinRest4.cols` say, for every level `i < 5` and
query `q`:
`∃ col ss, ss.length = sib i ∧ (openPath (frEnc i) col (qPos es i q) ss).runLog L = some (capDig es i (qPos es i q / 2^(sib i))) ∧ y i q = Σ_r eq(s_i, r)·col_r`,
derived by `R4Cols.ys_facts4`/`cols4_of_run` from the per-position `assertEq cur c` through
`capDig_eq4`. (β) deletes that compare, so:

(a) **`FinRest4.cols` (and `FinLog4.cols`) become:**
`∃ col ss d, ss.length = sib i ∧ (openPath (frEnc i) col (qPos es i q) ss).runLog L = some d ∧ pathDig es i q = d ∧ y i q = Σ_r eq(s_i, r)·col_r`
— the path's digest is *computed* (`pathDig es i q`, a function of the log), not compared —
**plus one new conjunct of the record**, `capChk4 es`:
`Σ_{(i,q)} ζ(es)^{r(i,q)}·pathDig es i q = Σ_k A(es)_k·capAll es k ∧ Σ_k A(es)_k·z(es)^k = Σ_{(i,q)} ζ(es)^{r(i,q)}·z(es)^{qPos es i q / 2^(sib i) + off i}`
with `ζ es := chK (kcAt es 4 0)`, `z es := chK (the CapChk squeeze's answer)`, `A es` the
absorbed field, `capAll es` the five caps concatenated, `r(i,q)` the read's ordinal. `capDig_eq4`
stays (it is about the absorbed cap). `ys_facts4`/`cols4_of_run` produce (a) from the run facts of
`posOpsG`'s accumulators and `finCap`.

(b) **The two dooms** (`FRSoundness4TailTruths`), both prefix-determined:
`D_ζ es := (∃ i q, pathDig es i q ≠ capDig es i (qPos es i q / 2^(sib i))) ∧ Σ_{(i,q)} ζ(es)^{r(i,q)}·(pathDig es i q − capDig es i …) = 0`
(the bad `ζ`s are the roots of a nonzero polynomial of degree `≤ 870` over `K`: `|bad| ≤ 870`,
charged `870/2^256` at P3.4's first squeeze, whose row is 0 today);
`D_z es := A es ≠ (fun k => Σ_{(i,q): qPos …/2^sib + off i = k} ζ(es)^{r(i,q)}) ∧ (the second identity holds)`
(`|bad| ≤ 1,919`, charged `1,919/2^256` at phase 52's squeeze: `DT 52 := D_z`).

(c) **The truth and the bridge:** `truthCap es := ∀ i q, pathDig es i q = capDig es i (qPos es i q / 2^(sib i))`;
`cap_of_chk : capChk4 es → ¬ D_ζ es → ¬ D_z es → truthCap es` (two SZ steps, over K);
`truthP3_four_of_cols` and the level-`i` bridges `colOf_of_path`/`foldAt_of_cols` take `truthCap
es` where they took the per-query `openPath … = capDig` conjunct; the Pf doom's background
hypothesis becomes `truthCap`, discharged by the final case split (`accept ∧ ¬D_ζ ∧ ¬D_z`).
Literals: `fsStarts4` entry 470, `phOf_ge : 470 ≤ p → phOf4 p = 52`, `DT 52`, `fsItems_length =
470`.

### 9.2 ε

Two new per-fresh-query rows, `870/2^256` (at P3.4's first squeeze, row 0 today) and
`1,919/2^256` (phase 52); the per-fresh-query maximum stays P2's `2^-120.36`; `εR = 15/2^124`,
`claim.json` unchanged. R-A′'s spacer answers are unused: no row. The pack map, `R` and B4 are
circuit rows: no error term. If §8's reserve is taken: 23 rows of `3/2^128` (degree-3 rounds),
below `εR`.

### 9.3 Open for the orchestrator

(i) `ζ` reused from P3.4 (recommended; no circularity, PK Q1) or a fresh squeeze (+80 B per
segment: N8's 256 blocks hold `8 × 2`). (ii) Whether to append the reserve's E phase to `seq4` in
A2′ (§8). (iii) The 12/79 foreign flags, to be listed from `fors` before B3 is sized. (iv) S-H4's
`reassemble` written field by field (A.3 rows 0–18) so `reassemble_field` is definitional.
(v) Retire S-E13a's H-cell pins and kind tie with B2′ (they cost 15 ms and are superseded).
(vi) The organiser's `build_s` question, with §7.2's numbers.

---

## 10. Fix log (revision 4.4.1, against `reviews/PACK-4.4-review.md`)

**Majors — all applied.**

| # | Fix |
|---|---|
| PK-M1 | The block-aligned CapChk (`A` padded to 61,472 B; the phase 61,632 B = 64·963), the 129-B spacer, `seq4`'s constants (8,905 → 8,907 items, `piSizeOf` 798,192 → 859,664, the segment stream 23,168 → 24,131 blocks, the stride 24,133, `aggB k = 64·(24,133k − 2)`). §2, §3.3, §3.4 re-issued; N8's spare recomputed at 256 blocks (`lBase` 195,328 ≤ 195,584); `qV` 35,631. The 81-B variant and the "whole blocks in the 81-B variant" claim are withdrawn. |
| PK-M2 | §9.1 gives `FinLog4.cols`/`FinRest4.cols`'s new statement, `capChk4`, `D_ζ`, `D_z`, `truthCap`, `cap_of_chk` and the literals that move (`fsStarts4` 470, `phOf_ge`, `DT 52`, `fsItems_length`); A3′'s brief names the modules; §3.4's "what moves" lists R4/S-G/FRX/S-H4; "no statement changes" is withdrawn. |
| PK-M3 | §5.2/§6.1: the arenas, bit rows and cap check sit in the slot's own region with the prototype; the spare region holds `R` and the `evalM` replay only; the cell plan packs ≈ 277 k cells below `2^19` without the `2^17` alignment (one more shift-by-constant on the M side). |
| PK-M4 | `selectHalf`/`keep` kept as compiled; the sibling is a per-kind form `l + r + a·cur` (2 rows per kind-varying depth, 3,484 per slot); the −15 k saving withdrawn; B0 (S-E6's levers) is a prerequisite of B2′ with its own brief. |
| PK-M5 | §6.3 re-done on S-I's run (V 157.9 ms runner, `v_ref` 206.6, `V̄` 0.400): ΔS +0.36 best, +0.86 worst; §0 and §8 use it. |
| PK-M6 | C0 added before D1 (template S-E13b's WOTS/`aggPad`, S-E12c's link rows, B4's `aggChk` rows); the `evalM` replay's row and V lines carry the child's link-row replay (+30 k / +10–18 ms without C0). |
| PK-M7 | §7.2: the build arrives at ≈ 3,400 CPU-s (2,975 + 165 queued + 265–285 planned) and reaches ≈ 2,400–2,500 after changes 27 (B), G2 and the `simp` cleanups — still over 2,020; RET runs from A2′ on, F's done includes `evaluate.py cert ≤ 600 s`, and the organiser's `build_s` question is to be asked now. |

**Minors.**

| # | Answer |
|---|---|
| PK-m1 | Fixed: arena₂ 85,946 rows (`Σ t_i S_i`), 132,096 allocated cells; level 3 noted at zero slack. |
| PK-m2 | Fixed: 150 products per instance, 26 ms per node (52 at 2×); §5.3, §5.4, §6.3 updated. |
| PK-m3 | Decided: the position bits are laid bottom-aligned per position so `bitOf j h` is a kind-free L cell (no `kin`); the decomposition is 3 gated rows per half (372); the 9 cap bits per read reach rows through kind-mux linear rows (7,839 per slot, counted in §6.1); the sibling's per-kind form through `CS.slotK` with `a·cur`; `tensorW`'s `bits 20/19` read the same cells through its existing `tensorWK` kind mux. |
| PK-m4 | Fixed in A1′'s brief: spacer entries in `sgn4`/`segTr`, 9 pin rows per spacer (length word, tag, state, message), `VA_queries_le` at `4·qS + 3`, `segTr`'s offset `1 + i·(segB − 1 + 129)`. |
| PK-m5 | Fixed (§3.3, §9.2): P3.4's row is 0 today; the maximum row is P2's `2^-120.36`. |
| PK-m6 | Fixed: every B/C/D stage re-measures `plan4t init` ≤ 2.0 s (the arena tables are closed constants built like `wfSeg`; the `R` keys and the extended `ProtoFit` are the risk). |
| PK-m7 | Fixed: 467 FS links; the `hashB1`/`hashB2` rows (8 + 2) and the segment's `hashA` rows stated once in B4 (§1.3's `input` row). |
| PK-m8 | Accepted: 0.03 µs for structured rows, 0.6 for sparse; the per-prototype figures are kept conservative at 0.06. |
| PK-m9 | Accepted: the reserve's error row (`3/2^128` per round, 23 rounds) and its S-C/S-G phase are now in §8's table and §9.2. |
| PK-m10 | Fixed: the literals are listed in §3.4 and A2′/A3′'s briefs (`szPs`, `fsItems_length`, `segTr_length`, `traces_le_qV`, `aggChainLen_eq`, `reassemble` row 18); INT-10's hypotheses unaffected. |
| PK-m11 | Fixed: V indexes `zpow[k]` (5–6 ms); the bit-product form is the circuit's only. |
| PK-m12 | Fixed: §5.3 item 1's `one` and M terms are shared across slots; the per-slot cost is the H term's 160 + the offset's 160. |
| PK-m13 | Noted in §2: `π_A`, `aggSegs`, `segView`, `VAwith`'s size check and INT-10's hypotheses are untouched. |

**Build order:** the review's corrected order adopted as §7 without change, with C0 and RET placed
as it says; the briefs for A2′, A1′, A3′, B0 are §7.1.

---

## 11. Addendum (β′): a sound batched cap check, and N8's overflow

Written 2026-10-29 after A3′'s finding (`recursion.fast-submissions-rev44/docs/v4/flock-recursive/stages/A3p-RESULT.md`, A2′'s `A2p-RESULT.md`; rev44 HEAD `ccdde20`). A2′'s V (`FRVIRFinals4.capChkOps`, `FRVIR4.posOps4`) is read, not built.

### 11.0 The flaw, restated in the certified model

The Fiat–Shamir chain is `fsItems4 = (itemsOf seq4).filter Item.isFS`: the seed, the absorbs and
the squeezes. Column and node queries are stream items but **not chain items**; `fsStarts4` puts
Q.i and P3.i at the same entry (370, 397, 421, 443, 463). So every challenge, `ζ` and `z`
included, is a function of the chain alone, and the prover chooses π's columns and siblings — hence
every path digest `cur_r` — after both are known. §3.3's "fixed by items ≤ Q.4" confused the
stream's item order with the chain. Over `GF(2)` the identity (I) is GF(2)-linear in the digest
bits, so with two candidate openings per read (one top sibling changed: one compression) and the
honest `A`, the prover solves `Σ_r b_r·φ_r(d_r¹ − d_r⁰) = T − Σ_r φ_r(d_r⁰)`: 512 equations in
871 unknowns over GF(2), full rank except with probability `≤ 2^-358`. The openings are then free
and the Merkle commitment binds nothing. **Every additive per-read batching whose summands are
chosen after the challenge fails this way**, logUp forms included (a repeated fake cancels mod 2).

### 11.1 The sound construction (β′): commit the path digests, then batch

**Fiat–Shamir order (`seq4`, after `Pf`):**

```
phase 52  CapD     absorb  D   field fD = 18, 871 · 32 = 27,872 B     (FS entry 482)
phase 53  CapZeta  squeeze ζ   (K: all 32 bytes)                      (FS entry 483)
phase 54  CapChk   absorb  A   field fA = 19, 1,408 · 32 + 32 = 45,088 B  (FS entry 484)
phase 55  CapChkZ  squeeze z   (K)                                    (FS entry 485)
```

`D_r` is the honest prover's path root of read `r` (reads in item order: level 0's 290, then 178,
145, 132, 126); `A_{off_i + k} = Σ_{r at level i, k_r = k} ζ^r`, `k_r = j_r >>> sib_κ(i)`; the 32 zero
bytes after `A` keep the phase block-aligned. Each phase's stream bytes are `≡ 0 (mod 64)`:
`80 + 27,872 + 80 = 28,032 = 64·438`, `80 + 45,088 + 80 = 45,248 = 64·707`.

**`V` per position** (`posOps4`): after `shrN` (the cap index `k_r`), a **static** read
`piDigest fD (32·r)` and `assertEq cur_r D_r`. There is no dynamic index anywhere: that is what B2
needed from the circuit (the import is an arena alias, 0 rows; the assert is 2 linear rows).

**`V` after `Pf`** (`capChkOps`): `ζ := chK(CapZeta's answer)`, `z := chK(CapChkZ's answer)`,
(I) `Σ_r ζ^r·D_r = Σ_k A_k·cap[k]` (two K identities, lo/hi halves), (II) `Σ_k A_k·z^k =
Σ_r ζ^r·z^{k_r + off_i}`, three `assertEq`, exactly A2′'s construction with `D_r` (the committed
field) in place of the position's `cur_r` register, and `ζ` from phase 53 instead of P3.4.

**Why it is immune to A3′'s attack.** The attacker must write `D` before `ζ` exists. Afterwards
each read's opening must hash to the committed `D_r` (the static assert), so the "two openings per
read" freedom is gone: a second opening with the same root is an oracle collision, which the
Merkle lemmas (`cap_binding`, `openPath`) already charge. With `D` and `cap` fixed and `A` the
honest selector sums, (I) is `Σ_r ζ^r (D_r − cap[k_r]) = 0`, a nonzero polynomial in `ζ` unless every
`D_r = cap[k_r]`; a dishonest `A` must pass (II) at a `z` chosen after `A`. Nothing on the right of
either identity is chosen after its challenge.

**Soundness in the model the certificate proves (S-G doom counting over `Log`).** The potential
charges, at each chain squeeze, the measure of the answers that put the log into a *doom*
(`FRSoundness4TailStep`: `hsingle` for a single-squeeze phase — the bad answers' count `≤ N`,
`N = 239·2^128` (`N_le`) —, `hround` for a multi-squeeze phase). Two new dooms, both decided by
the chain prefix at their squeeze:

| Doom | At | Statement (over the log `es` at the squeeze) | Bad answers | Row |
|---|---|---|---|---|
| `D_ζ es` | phase 53 (`DT 53`), `hsingle` | `(∃ r, D_r es ≠ capDig es (lvl r) (k_r es)) ∧ Σ_r ζ(es)^r·(D_r es − capDig es (lvl r) (k_r es)) = 0` (both K halves) — `D_r es` read from the CapD absorb's payload in the chain, `capDig` from the C.i absorbs, `k_r es` from P2.i's answers: all in the prefix | the roots of a nonzero polynomial of degree `≤ 870` over `K`: **`≤ 870`** | `870/2^256` |
| `D_z es` | phase 55 (`DT 55`), `hsingle` | `A es ≠ (fun k => Σ_{r: off + k_r es = k} ζ(es)^r) ∧ Σ_k A(es)_k·z(es)^k = Σ_r ζ(es)^r·z(es)^{k_r es + off}` — `A es` from the CapChk absorb's payload, `ζ es` from phase 53 | roots of a nonzero polynomial of degree `< 1,408`: **`≤ 1,407`** | `1,407/2^256` |

Both counts are `≤ N` by many orders, so `hsingle`'s obligation is met with room; `deltaR`
(`= epsD − 2^-142`, A3′ §3) is untouched because the per-fresh-query maximum stays P2's
`2^-120.36`; **`εR = 15/2^124` and `claim.json` are unchanged**, as A3′ §3 computed for the
counts 870 and 1,407. `truthCap es := ∀ r, D_r es = capDig es (lvl r) (k_r es)` and `cap_of_chk :
accept → ¬D_ζ es → ¬D_z es → truthCap es`; with the per-position run fact `openPath … = some (D_r
es)` (from the static assert, `cols4_of_run`), `truthCap` gives today's `openPath … = capDig …`,
so `FinRest4.cols`'s *original* conjunct is recovered under `¬D_ζ ∧ ¬D_z` and the level-`i`
bridges (`colOf_of_path`, `foldAt_of_cols`, `truthP3_four_of_cols`) are unchanged in statement.

**Alternatives weighed.** (i) Absorbing each level's `D_i` before P3.i and reusing `κ_c` as `ζ_i`:
5 absorbs and 5 `A_i` items cost 880 B of headers against 320, and `κ_c`'s bytes are used
(2 coordinates of the first answer): no. (ii) Half-size `D` (absorb `lo(D_r) + θ·hi(D_r) ∈ F`,
`θ` a pre-Q challenge; 13,936 B): needs a new collision row of `2^-128` per fresh node query on a
128-bit linear image of the oracle's answers — within `εR` numerically, but a new lemma family in
`FRMerkle`/`cap_binding`; kept as §11.2's reserve lever L5. (iii) A separate digest of `D`
(hashing `D` through the oracle): 436 node queries = 48.8 KB of stream, worse than absorbing `D`.
**(β′) as above is recommended.**

### 11.2 N8's overflow: levers priced (A2′'s constants)

Constants (A2′ §6, A3′ §4): `A` 1,408 entries = 45,088 B; A2′'s segment stream `1,528,000 =
64·23,875`; stride 23,877; N8 `hUsed = 2·95,506 + 2,196 = 193,208`, `lBase 193,280`, bound
`195,584`: **2,304 blocks spare**. (β′) adds the `CapD` phase, 438 blocks per segment: a segment is
`1,556,032 = 64·24,313`, the stride 24,315, `aggL 4 = 97,258`, `hUsed = 2·97,258 + 2,196 =
196,712`, `lBase = 196,864`: **over by 1,280 blocks** (A3′). `|π| = 871,152`, items 8,909,
`qV = 4·8,909 + 3 = 35,639`.

| # | Lever | N8 blocks | Stream / `|π|` / positions | What else it costs | Verdict |
|---|---|---|---|---|---|
| L1 | **Reclaim `WM`**: `hUsedN κ = wotsB κ 2 + wmSlot4·κ.vslots + 8` reserves 146 mirror blocks per *verifier* slot, but only the two *signed children* have WOTS runs and mirrors (`wmB κ σ`, `σ < 2`; A.6: 581 sources per signed child). N8 reserves 1,168, uses 292 | **−876** (N2 −146, N4 −438) | none | `FRNodeKinds4.hUsedN`, `FRNodeLayout4.hUsed_eq`/`regions_fit`, `aggChild`/`nodeLayout4`'s `freeIv (wmB κ 0) (hUsedN κ)` — literals and one definition; the mirror addresses do not move | **adopt** |
| L2 | **Cap depth 8 at level 4** (`ladder32` level 4 `⟨4,12,126,7⟩ → ⟨4,12,126,8⟩`, `ladder30` `⟨4,10,126,7⟩ → ⟨4,10,126,8⟩`: `sib` 5→4 and 3→2) | −126 node items × 112 B = −14,112 B; `cap₄` 128→256 entries: +4,096 B in the C.3 absorb; `A` 1,408→1,536: +4,096 B; net **−5,920 B = −92.5 blocks per segment: −740 for N8**; with `A`'s 32-B pad dropped the segment is `1,550,080 = 64·24,220` (whole), stride 24,222, `aggL 4 = 96,886` | `|π|` 871,152 + 4,096 + 4,096 − 4,032 = **875,312**; items 8,909 − 126 = 8,783; level 4's Q items shrink (positions after Q.4 move: P3.4, Pf, CapD…; FS entries do not: Q items are not FS items) | `FRTranscriptDefs.ladder32/30`, `capBytes 3`, `merkleOps4` depth at level 4, `A.3`/`A.4` counts, `aggL` literals, R4/P4's level-4 position lemmas; `D_z` degree `< 1,536` (row 1,535) | **adopt** |
| L3 | Cap depth 9 at level 1 (`sib` 10→9) | −178·112 + 2·8,192 = −3,552 B: **−444** | levels 1–4's positions move | more of L2's cost for less | reserve |
| L4 | **N8 with 7 slots** (aggregates `maxK` 4 and 3) | −24,315 − 3·146: **−24,750** | — | step 1 is `prover first` with **two chains** (changes 25 (3)), each `n ∈ [2^17, 2^20]` i.i.d. `∝ 1/n²`; a chain needs 4 segments iff `n > 3·2^18`: `P = (1/786,432 − 1/2^20)/(1/2^17 − 1/2^20) = 4.8 %`. With a fixed chain order the second chain overflows its 3 slots in **4.8 % of streams**; if the node may order the chains by size, both must exceed `3·2^18`: **0.23 %**. A failed step 1 loses the stream | **rejected** |
| L5 | Half-size `D` (§11.1 (ii)) | −13,936 B = −217.75 blocks per segment: **−1,742** | `|π|` −13,936 | a new collision lemma family (`2^-128` per fresh node query) in S-C/S-G | reserve |
| L6 | Deeper caps at level 0 (`sib` 11→10) | −290·112 + 2·16,384 = +288 B | — | — | no |
| L7 | N8 at `m = 33` | fits trivially | every node proof's shape (+1 round in Z/E/S, +1 sibling per position ≈ +97 KB of `|π|` for **every** node, which is what the harness verifies: `x_size` +0.046) | breaks "one item sequence for every kind" (B-13): the slot-0 mux | **rejected** |
| L8 | Shrink L to `2^13` per verifier slot | −512 | — | `lRows4`/`evalL4I` frozen at stride `2^14`; S-E13b's cells at 8704–11648 | no |

**Recommendation: L1 + L2.** N8 after both: chains `2 × 96,886 = 193,772`, fixed blocks `2,196 −
876 = 1,320`, `hUsed = 195,092`, `hEnd = 195,100`, `lBase = 195,328 ≤ 195,584`: **fits with 256
blocks to spare** (0.13 %). N4: `24,220 + 96,886 + (1,749 − 438) = 122,417` of 195,584; N2:
`24,220 + 48,442 + fixed` ≪ bound. If a later change needs more than 256 blocks in N8, L5 is the
next lever (−1,742) and L3 the one after. L4 (7 slots) is not available: it fails step 1.

### 11.3 Cost against the revert (option 2: the per-position dynamic read)

S-I's basis: `v_ref = 206.6 ms`, V 157.9 ms runner, `|π| = 798,192`, `V̄ = 0.400`;
`dV̄/dx ≈ 1.57` at `x ≈ 1.4`, i.e. 0.0076 s per runner ms and 0.75 s per MiB.

| | revert: `piDigestAt` + `assertEq` per position (HEAD `4d5700c`'s V) | (β′) with L1 + L2 |
|---|---|---|
| soundness of `V` | sound (A3′) | sound (§11.1) |
| circuit rows per slot to bind the cap reads | the mux: `≈ 3·2^c` per read, **≈ 1.34 M** — does not fit a region: the node stays unprovable (`Gap4.imp` open) | static `D` aliases 0 + 2 assert rows per read 1,742 + the (I)/(II) **templates** ≈ 48 k + the cap-bit kind-mux rows 7.8 k: **≈ 58 k structured rows** (as skeleton ops, A2′'s way: 55–65 k *sparse* rows per prototype at ≈ 30 ms of `evalMT4` each — §11.7: not acceptable) |
| parent `evalM` (V of the node that *contains* the slot) | — | ≈ 2.5 ms VM per prototype as templates (B2′); A2′'s untemplated interim is +280 ms VM and must not ship |
| `V`'s own time | 0 | ≈ 9 ms VM (A2′'s profile of the cap-check ops) + 871 static reads ≈ 0: **+7.6 ms runner → +0.058 s** |
| `|π|` | 798,192 | **875,312 (+77,120 B = +0.0368 of `x`): +0.058 s** |
| stream per segment | 23,168 blocks | 24,220 (+4.5 %): node prover +11 ms per slot (+0.06 s per N4 node, ≈ +0.03 s of `P̄`) |
| `qV` | 35,631 | `4·8,783 + 3 = 35,135` |
| ε | — | unchanged (`870/2^256`, `1,535/2^256` rows) |
| **ΔS** | **0, with no sound node** | **≈ +0.15 s** (`V̄ ≈ 0.52`), the price of binding the cap reads |

Against 4.4.1's (β) the difference is the `D` field: +27,872 B of `|π|` (+0.02 s) and two more items.

### 11.4 The changes to A2′'s V, exactly

1. **Fields** (`FRTranscriptDefs`, `FRShape4`): `fD := 18` (the 871 path digests, 27,872 B),
   `fA := 19` (unchanged content, 1,536 entries after L2: 49,152 B, **no pad**: the two phases are
   `28,032 = 64·438` and `80 + 49,152 + 80 = 49,312 = 64·770.5` — so with L2 the pad is 32 B again
   on `A` *or* the level-4 change absorbs it: `1,482,752 + 28,032 + 4,096 − 14,112 + 49,312 =
   1,550,080 = 64·24,220` exactly, so **`A` has no pad under L2**; without L2 keep A2′'s 32-B pad);
   `nFields4 := 20`; `piSizeOf seq4 := 875,312` (871,152 without L2); `streamBytesOf_seq4 :=
   1,550,080` (1,556,032 without L2); `chainLenOf_seq4 := 24,220` (24,313).
2. **Phases** (`FRShape4.capChkPh S`): `[("CapD", .absorb fD 27872), ("CapZeta", .squeezes 1 .one),
   ("CapChk", .absorb fA (aBytes S)), ("CapChkZ", .squeezes 1 .one)]` — phases 52, 53, 54, 55;
   `capChk_aligned` for both absorb+squeeze pairs; `items`: 8,905 + 4 − 126 = **8,783** (8,909
   without L2); `traces_spacers_le_qV` at `4·8,783 + 3`.
3. **`fsStarts4`** (`FRSoundness4Pos`): `fsItems4_length := 486` (482 + 4); `fsStarts4_eq` gains
   `482, 483, 484, 485`; `phOf_ge : 482 ≤ p → phOf4 p ∈ {52 … 55}` by cases; `DT 53 := D_ζ`,
   `DT 55 := D_z`, `DT 52`/`DT 54` (absorbs) carry no doom.
4. **`posOps4`** (`FRVIR4`; `posOpsG` the same): `[.idx …, .piField 0 (co + p·colBytes i) …, .askCol,
   .dotKF] ++ merkleOps4 K.sib i b L.sib 0 (b+2) (so + p·L.sib·32) (b+4) ++ [.shrN b (fun _ => K.sib),
   .piDigest fD (dO + 32·p), .assertEq (curOfY L.sib (b+3)) (b + 4 + 6·L.sib + 1) allK]` with `dO :=
   fieldOff fD + 32·(Σ_{i' < i} t_{i'})` passed like `co`/`so`; `posW4 S i := 4 + 6·sib + 3`
   (A2′'s `+ 1`); `kOfY` unchanged; level 4's `L.sib` is 4 (`ladder30`'s 2) under L2.
5. **`capChkOps`** (`FRVIRFinals4`): `zetaA := (outs of phase 53).head − 1` (A2′ read `lvOuts fi 4
   4`: P3.4 — **this is the unsound line**); `za := (outs of phase 55).head − 1`; `capReads S fi w`
   returns, per read, the **`D` register** `b + 4 + 6·sib + 1` of its position (not `curOfY`), with
   the cap-index register as before; `capMax S` 9; `capEntries S` 1,536 (L2) with `off = 0, 512,
   768, 1024, 1280`; the head, the chains, (I), (II) and the three `assertEq` as A2′;
   `noAsk_capChkOps`, `capChkOps_off/_head`, `map_at_capChkOps` re-proved; `finOps4 := (finals ++
   capChkOps).map reloc` as A2′ (deviation 4 stands).
6. **The format and `reassemble`**: A.3 rows 18 (`D`: the CapD absorb's message, item 8,781 under
   L2, bytes `40 … 40 + 27,872`) and 19 (`A`: item 8,783 − 2, all `49,152` bytes); S-H4's generic
   `rsPhase` handles both with no special case (A2′ §6).
7. **Layout** (L1 + L2): `FRNodeKinds4.hUsedN κ := wotsB κ 2 + wmSlot4·2 + 8`, `segB`, `cLen`,
   `aggB/aggL` (stride 24,222), `FRNodeLayout4.hUsed_eq` (N8 195,092), `hEnd_eq`, `regions_fit`;
   `FRTranscriptDefs.ladder32/ladder30` level 4, `capBytes 3 = 8,192`.
8. **The prover** (P2): writes `D` (its own path roots, in read order) before squeezing `ζ`; `A`
   after; the level-4 cap at 256 entries; the native `acc` follows the dump.
9. **Untouched from A2′**: `Seq.capChk`, `aBytes`'s shape, `capReadOps`/`capEntryOps`'s arithmetic,
   `ir.rs`'s op kinds (all existing), the 3.x modules (`seq3` has no cap check).

### 11.5 A3′'s brief, rewritten

**A3′ — the restated `cols` and the two dooms (one owner for R4 + S-G), on V as in §11.4.**
Modules: `FRSoundness4R4Tail` — `FinLog4.cols`/`FinRest4.cols` keep their per-`(i, q)` conjunct in
the form `∃ col ss, ss.length = sib i ∧ (openPath (frEnc i) col (qPos es i q) ss).runLog L = some
(dAt es i q) ∧ y i q = Σ_r eq(s_i, r)·col_r` with **`dAt es i q := the 32 bytes at offset `32·r(i,q)` of
the CapD absorb's payload in `es`** (prefix-determined), and gain one conjunct `capChk4 es` (the
two identities over `dAt`, `capDig`, `A es`, `ζ es`, `z es` as §11.1); `FRSoundness4R4Cols` —
`ys_facts4`/`cols4_of_run` from the per-position `assertEq cur D_r` and the finals' three asserts
(`capDig_eq4` unchanged); `FRSoundness4TailTruths` — `truthCap`, `D_ζ`, `D_z` (§11.1's table);
`FRSoundness4TailD` — `DT 53 := D_ζ`, `DT 55 := D_z`, the phase table 52–55, `phOf_ge`, the Pf
doom's background hypothesis `truthCap`; `FRSoundness4TailLig` — `cap_of_chk : capChk4 es → ¬D_ζ
es → ¬D_z es → truthCap es` (two SZ steps over `K`: `Polynomial.card_roots'`-style bounds 870 and
1,535), then `truthP3_four_of_cols`/`colOf_of_path`/`foldAt_of_cols` take `truthCap` and are
otherwise unchanged; `FRSoundness4TailStep` — the two `hsingle` rows (counts 870, 1,535 `≤ N`);
`FRSoundness4R4Run`/`R4Ref`/`R4Acc` — re-run with `finOps4 = finals ++ capChkOps` and `posOps4`'s
three trailing ops (`exec_posOps4` in `R4PosT`: the reference `posT4` compares `cur` with `D_r`,
not with the cap entry); `FRSoundness4Pos` — `486`, `fsStarts4_eq`. Statements that change: those
named, and nothing else in the tail (the level-`i` dooms keep the log-side `truthP3`). Definition
of done: `ks_rev4GR` (or its successor) builds at `εR = 15/2^124` with the row table extended by
`D_ζ 870/2^256` and `D_z 1,535/2^256`; controls `dZeta_ctl` (a `D_r ≠ cap[k_r]` log at a root
`ζ` is in `D_ζ`), `dz_ctl`, `capChk_pos` (an honest `D`, `A` passes), `capChk_neg` (a wrong `A_k`
fails (II) at a generic `z`), **`attack_neg`** (A3′'s two-opening log: the static assert rejects
one of the two openings — the control that §3.3 lacked); `FRSoundness4TailD` within +1 phase of
its 18 CPU-s; CPU-s recorded. Prerequisite: A2′ re-issued per §11.4 (the orchestrator's open
question 3: until then `v4/rev44` carries an unsound V and should sit at `4d5700c`'s V).

### 11.6 Fix log (addendum)

- §3.3 and §9.1 marked superseded; §3.2's (β) row, §3.4, §6.1, §6.3 and §7's A2′/A3′ lines are to
  be read with §11's constants: `|π| = 875,312` (`x_size` 0.4174), stream 24,220 blocks per segment,
  items 8,783, `qV` 35,135, rows per slot ≈ 58 k for the cap check, N8 at 256 blocks of spare
  after L1 + L2. The V-side ΔS of §6.3 grows by ≈ +0.02 s (the `D` field); §8's decision is
  unaffected.
- The review (PK Q1) and 4.4.1 both accepted "fixed by items ≤ Q.4"; the error was treating
  stream items as chain items. The control `attack_neg` is added to A3′'s done so that the
  certificate carries the counterexample.

### 11.7 (β′) priced on B0's measured prototypes; templates, not skeleton ops; the order

B0 (`stages/B0-RESULT.md`, "For A2′"): prototypes **630,016 (p0) / 618,496 (p1)** rows in their
regions (from 730,493 / 725,885); N8's modelled rows 7,620,864 = 1.048× under `N_M/1.05`. A2′'s cap
check compiled as skeleton ops adds **55–65 k sparse rows per prototype** (≈ 690 k / 680 k) and
**≈ 30 ms of `evalMT4` per prototype** (0.5 µs per sparse row: the plan evaluates skeleton rows one
product per entry). That is 60 ms VM per N2/N4 node (two prototypes), ≈ +0.38 s of S on S-I's
basis — more than the whole cap check is worth. **(β′)'s check must enter the circuit as keyed
templates** (`local`/`shared` classes), which is what B2′ owns:

| Template key | Instances per slot | Rows | Inputs | Class | V per prototype |
|---|---|---|---|---|---|
| `tplPowChain` (K: `a_{i+1} = a_i·g`) | 2 (the `ζ^r` chain, 871 steps; the `z^k` chain, 1,536 steps) | 3 per step: 2,613 + 4,608 | `ζ`, `z` (arena aliases of the two squeeze answers) | local (stride 3) | ≈ 0.1 ms |
| `tplSqChain` (K squarings `z^{2^t}`, 11 steps) | 1 | 33 | `z` | local | ≈ 0 |
| `tplBitPow` (`Π_t (1 + c_t·(z^{2^t} − 1))`, 9 K products) | 871 | 27 each: 23,517 | the 9 kind-muxed cap bits (`c_t = Σ_κ s_κ·L(…)`: 7,839 linear rows, their own key), `z^{2^t}` (shared) | local, instance stride 32 | ≈ 0.3 ms |
| `tplMacD` (`ζ^r·D_r` K×F ×2 halves, `ζ^r·z^{k_r}` K; running sums) | 871 | 5 each: 4,355 | `D_r` (arena₁ aliases: the CapD payload, 871 × 2 fixed cells), the chains | shared (fixed arena cells) + local | ≈ 0.4 ms (1,742 eq lookups) |
| `tplMacA` (`A_k·cap[k]` K×F ×2, `A_k·z^k` K; sums) | 1,536 | 5 each: 7,680 | `A_k`, `cap[k]` (arena₁ aliases, 3,072 + 3,072 fixed cells), the `z^k` chain | shared + local | ≈ 1.2 ms (6,144 lookups) |
| the three final asserts, the per-position `assertEq cur D_r` | — | 6 + 1,742 | — | inside the position template / linear | ≈ 0 |
| **total** | | **≈ 52.4 k rows per slot** | | | **≈ 2 ms VM per prototype** (4 per node) |

**Rows per slot region with B0 and the templates:** segment slot `618,496 + 212,344 (pack map, §6.1)
+ 52,400 + 49,000 (R) + 32,768 (link) = 965,008 (92.0 %)`; previous-node slot's region A
`630,016 + 212,344 + 52,400 + 32,768 = 927,528 (88.5 %)`. **N8: `8 × 965,008 = 7,720,064` against
`N_M/1.05 = 7,990,232`: 1.035×** (B0's 1.048× was before the pack map and the cap templates; with
A2′'s skeleton-op check instead of the templates the segment slot is 974,608 and N8 1.025× — it
fits, but at +60 ms VM per node). The spare region is unchanged (§6.1).

**Who builds what, in what order.**
1. **A2″** (S-0′/FRTranscriptDefs, the V change of §11.4): `posOps4`'s static read + assert,
   `capChkOps` on `D`, the four phases, the fields, the layout levers L1 + L2. Its compiled
   prototypes may carry the cap check as skeleton ops **as an interim**, but A2″'s RESULT must not
   quote that V as the design's: it reports `evalMT4` with and without the cap-check rows, and
   the prototypes' region rows (expected ≈ 690 k / 680 k).
2. **B2′** (L-circ) builds the five keys above as `tplExt` extensions (the same mechanism as
   S-E12f's `tensorWK`: a key per op pattern, `tpl_mle` for each class, `compileT_sound` through
   `tplX_sound`), regenerates `FRNodeRows4Hint` (`laydump4`) and measures `evalMT4` and `plan4t
   init` ≤ 2.0 s. B2′ depends on A2″'s ops being in the tree; **A2″ and B2′ land in that order,
   and no V(N4) or `P̄` figure for 4.4 is quoted before B2′'s**. The arenas (§5.2) are B2′'s
   other half and are needed for `D`/`A`/`cap` to be fixed arena cells; until the arenas, the
   templates' `D`/`A`/`cap` inputs are H cells (irregular, ≈ 6 k lookups ≈ 4 ms per prototype:
   acceptable as an interim).
3. **A3′** (R4 + S-G, §11.5) depends only on A2″'s V (the ops and the phases), not on B2′: it runs
   in parallel with B2′.
4. **P2** fills `D` and `A` and the templates' chain cells after B2′'s dump.
