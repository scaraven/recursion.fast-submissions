# PACK-4.4 review: adversarial reading of `design/PACK-4.4.md` (D-PK)

Reviewer: PK-review (Fable), 2026-10-29. Worktree `v4/flock-recursive` at HEAD `8dd02b5`. Read: the
memo in full; BLUEPRINT §0.1, §4.3–§4.4, §5.2, A.3–A.7, A.11, changes 25–28; S-N2, S-E13a (+JOURNAL
§1), S-E13b, S-E14 (+JOURNAL §0–§1.10), S-E6 §4–§5, S-E12b §4–§5, INT-9, INT-10, S-I; QUEUE.md; the
core's `harness/season.toml` and `PROVER.md` (the score). Lean, read only: `FRTranscriptDefs`
(`Item.qlen`, `streamBytes`, `items_aligned`), `FRShape4` (`itemsOf_seq4_length`, `piSizeOf_seq4`,
`streamBytesOf_seq4`, `chainLenOf_seq4`, `qV4`), `FRAgg` (`VAwith`, `VA_queries_le`), `FRNodeKinds4`
(`segB`, `aggB`, `aggL`, `hUsedN`, `tailIvs`), `FRNodeLayout4` (`hUsed_eq`, `regions_fit`, `lBase`),
`FRNodeRead4` (`segTr`, `sgn4`), `FRNodeCircuit4` (`AggPad4`), `FRNodeRows4` (`mvC`, `InSlot`,
`ProtoFit`), `FRNodeRows4Plan` (`slotV4`), `FRNodeRows4Model`, `FRNodeRows4Wots` (`lastR`),
`FRNodeSound4` (`SlotRun`, `SlotImp`), `FRVIR4`/`FRVIR4Mux` (`posOps4`, `posOpsG`, `merkleOpsG`),
`FRVIRCompile` (`muxOut`, `keep`, `selectHalf`, `assertEq`, `assertZero`), `FRVIR` (`exec`),
`FRSoundness4TailTruths` (`truthP3`, `kcAt`), `FRSoundness4TailD` (`finP3`, `DPf`, `DT`,
`phOf_ge`), `FRSoundness4TailLig` (Part E, `truthP3_four_of_cols`), `FRSoundness4R4Cols`
(`capDig_eq4`, `ys_facts4`, `cols4_of_run`), `FRSoundness4R4Tail` (`FinLog4.cols`,
`FinRest4.cols`), `FRMerkle.cap_binding`, `FRX4Prog` (`szPs`); the dumps
`logs/S-E13a/nodedump4-run.log`, `logs/S-E12f/nodedump/proto-p0.txt` (the position's ops). No
file other than this one was written; no Lean was built (every fact below is a theorem already in
the tree, a definition read from it, or arithmetic shown in place).

**Verdict in one line: the direction (R-A′, (β), two arenas, keyed `R`) is right; the memo's
numbers are not, and three of its structural claims are false as written. Adopt with the fixes
below; re-issue §2, §3.3–§3.4, §5.2, §6.1 and §6.3 before track A starts.**

---

## 0. The majors in one table

| # | Where | What is wrong | Consequence |
|---|---|---|---|
| PK-M1 | §2, §3.3–§3.4, §9 | The byte arithmetic mixes two variants (2 and 3 items), uses 3.x's constants (8,891 items, `piSize` 797,904) where `seq4` has 8,905 and 798,192, and the "whole blocks, `lastR = 64`, R-4-m2 disappears" claim is false in the 81-B variant | `aggL`, `AggPad4`, S-E13b's `padRows`, N8's H margin and the spacer length are all mis-stated |
| PK-M2 | §3.4, §7 A3–A4, §9 | "(β): R4 no statement changes; S-G's Q truth unchanged" is false: `FinLog4.cols`/`FinRest4.cols` (`FRSoundness4R4Tail`), `ys_facts4`/`cols4_of_run` (`R4Cols`) state per-query `openPath … = capDig`, which (β) no longer yields; S-G's per-level use of `colOf_of_path` and the Pf doom need a new CapChk doom | A3/A4 are a restatement, not a re-run |
| PK-M3 | §6.1, §9 (ii) | The two-region split (prototype in A; arenas, `R`, `evalM` in B) breaks `InSlot`/`ProtoFit`/`slotV4`: prototype 0's consuming rows read arena cells outside their region, so the copy identity the memo prices with (0.06 µs per row, "once per node") does not apply to the previous-node slot; the cell plan (`A₁ = 2^18`, arena₂ 132 k) also runs into `R`'s cells `[2^19, 2^20)` | V for prototype 0 is per-slot irregular again, or a new "cross-region" class; fix: arenas with the prototype, `R` + `evalM` alone in the spare region |
| PK-M4 | §1.3, §6.1 | The Merkle mux row `b·(l + r) = cur + l` must be activity-gated (at a dummy depth `l = r = 0` and the ungated row forces `cur = 0`): 2 rows per half as today's `selectHalf`, plus `keep`'s 2 rows per step. Net saving −15 k is 0 | segment region 1,045,806 (99.7 %) before the levers; the S-E6 levers are a prerequisite of B2, not a reserve |
| PK-M5 | §6.3, units | `V̄` "today 0.71–0.79" is 4.3's figure at `v_ref = 177.8`; the plan's 0.88–0.93 uses 206.6. On one `v_ref` and the measured runner V (157.9 ms, `V̄ = 0.400`, S-I §5.2) the plan is `V̄ ≈ 0.70–0.75` best, 1.0 worst: **ΔS ≈ +0.30 … +0.6 s**, not +0.1 … +0.2 | the scope decision (§8) is being made on a wrong delta |
| PK-M6 | §6.1 row "evalM replay", §6.2 | "S-E14's 90 k for the child's irregular link region is gone" is false: §5 replaces the pack *pins*, not S-E13b's WOTS/`aggPad` rows (25–35 k irregular entries per kind) nor S-E12c's link rows; the child's `R` must still replay them, muxed over 3 kinds | +≈ 30 k rows and +10–18 ms VM unless the WOTS rows are templated first (a prerequisite of D1 the order omits) |
| PK-M7 | §7 | No build-budget line. The build is 882 s against 600 (S-I F1); the plan adds ≥ 10 `FRNodeRows4*`/`FRVIRTpl*` modules (S-E13a/b measured 7–25 s wall each) and a compiler change (`Slot` as linear forms) inside the certificate's core induction | F is unreachable without a retirement step inside the order |

Minors PK-m1 … PK-m13 in §2. §3 answers the brief's seven questions; §4 gives the verdict and the
corrected order.

---

## 1. Majors

### PK-M1 — the byte arithmetic (B1, B2, N8's fit)

**Facts from the tree.** `Item.qlen`: absorb `8 + 32 + len`, squeeze `8 + 32`; an item's stream
bytes are `8 + qlen + 32` (`Item.slen`), so an absorb item is `80 + len` B and a squeeze item 80 B.
`items_aligned`: every item after the seed has `slen ≡ 0 (mod 16)`, which forces `len ≡ 0 (mod 16)`
for any new absorb. `itemsOf_seq4_length : 8905`; `piSizeOf_seq4 : 798192`;
`streamBytesOf_seq4 : 1482752 = 64 · 23168` (`chainLenOf_seq4`: **the segment stream is a whole
number of blocks today**); `aggB k = 1 + k·(segB − 1)`, `aggL k = ⌈aggB k / 64⌉`;
`AggPad4`'s `r = aggB k − 64·(aggL k − 1)` = S-E13b's `lastR`.

**What the memo writes.** `items_length 8,891 → 8,893` (3.x's `items`, not `seq4`); `piSize
797,904 → 859,344` (3.x's); the stream `1,482,752 → 1,544,432 B (+61,680 = 61,520 + 80 + 80 of a
second squeeze if ζ is made fresh)`; `blocks 23,168 → 24,133`; `segB − 1 = 1,544,431 ≡ 47 (mod 64)`,
spacer `49 + s ≡ 17`, `s = 1`, 81 B; "the aggregate stream of k segments is `L_seg·k − 2` whole
blocks, R-4-m2's partial last block disappears, `lastR` is 64".

**Recomputation.**

| Variant | CapChk bytes | segment stream | blocks | `traceBytes mod 64` | spacer `≡ 1 − that` | spacer | stride (blocks) | aggregate, `k = 4` |
|---|---|---|---|---|---|---|---|---|
| memo, 2 items (ζ reused) | 61,520 + 80 = 61,600 | 1,544,352 | **24,130.5** (not whole) | 31 | ≡ 33 | 80 + 17 = **97 B** | 1,544,449 / 64 — **not whole** (≡ 1) | `1 + 4·1,544,351 + 3·97 = 6,177,696 ≡ 32 (mod 64)`: partial last block of 32 B |
| memo, 3 items (fresh ζ) | 61,680 | 1,544,432 | 24,131.75 | 47 | ≡ 17 | 81 B | 1,544,512 = 64·24,133 | `6,177,968 ≡ 48 (mod 64)`: **partial last block of 48 B**, 96,530.75 → 96,531 blocks |
| **fixed: CapChk `≡ 0 (mod 64)`** (e.g. field `A` padded to 61,472 B: `61,552 + 80 = 61,632`) | 61,632 | 1,544,384 | **24,131** | 63 | ≡ 1 | **129 B** (S-E13a's) | 1,544,512 = 64·24,133 | `1 + 4·1,544,383 + 3·129 = 6,177,920 = 64·96,530`: **whole** |

So: (i) the memo's 24,133 is neither variant's segment block count; (ii) its two variants are mixed
(item count from one, bytes from the other); (iii) **in both of its variants the aggregate stream is
not a whole number of blocks** — the "`L_seg·k − 2` whole blocks" claim, the `lastR = 64` claim
and the "−130 rows per candidate" claim are false (with the 3-item variant `lastR = 48`: element 7
is whole-element zero, so the decomposition goes, but the message-prefix clause of `AggPad4` stays
exactly as it is); (iv) the invariant that a single proof's stream is whole blocks
(`chainLenOf_seq4`, INT-2's reason for the 32-B E4end) is broken by both variants: the
previous-node slot's chain gets a partial last block. The fixed variant restores S-E13a's original
R-A′ (129 B, `aggB k = 64·(L₀ k + 2k − 2)`), under which every claim of §2's "two consequences" is
true. Note the fixed variant's `|π|` is 798,192 + 61,472 = 859,664 (x_size 0.4099, same as the
memo's 0.4098 to three digits).

**N8's H, recomputed** (`hUsed_eq`: N8 187,540 = 2 × 92,672 + 2,196; the bound is `lBase ≤ mBase −
nL/128 = 196,608 − 1,024 = 195,584` with `lBase = ⌈hUsed/256⌉·256`, `regions_fit`; `hEnd = hUsed +
nAgg·maxK = hUsed + 8` must also be `≤ lBase`):

| Variant | chain blocks (2 aggregates) | `hUsed` | `lBase` | spare to 195,584 |
|---|---|---|---|---|
| memo (3 items, 81 B) | 2 × 96,531 = 193,062 | 195,258 | 195,328 | 326 |
| fixed (129 B, padded A) | 2 × 96,530 = 193,060 | 195,256 | 195,328 | 328 |

The fit stands (≈ 0.17 %), the memo's "324" happens to be near. N4: `hUsed` 117,589 → ≈ 122,410
(previous node 23,168 → 24,131; aggregate 92,672 → 96,530). `qV`: `4·8,907 + 3 = 35,631 ≤ 36,000`
(`VA_queries_le` gives `4·qS`; the spacer's three queries must be added to its statement, PK-m4).

**Fix.** Choose the block-aligned variant (`A`'s absorb payload padded to 61,472 B, or any CapChk
of `≡ 0 (mod 64)` bytes with each `len ≡ 0 (mod 16)`); spacer 129 B; restate §2's table, §3.3's
items line, §3.4, §9's `qV`, and the `|π|` in §6.3 with `seq4`'s constants.

### PK-M2 — (β) is a restatement of R4's `cols` facts and of S-G's tail, not a re-run

**Facts.** `FRSoundness4R4Tail.FinLog4.cols` and `FinRest4.cols` (the accepted run's checks on the
log) say, for every level `i < 5` and query `q`: `∃ col ss, ss.length = sib ∧ (openPath (frEnc i)
col (qPos …) ss).runLog L = some (capDig es i (qPos / 2^sib)) ∧ y i q = Σ_r eq(s_i, r)·col_r`.
`R4Cols.ys_facts4`/`cols4_of_run` derive them from the skeleton run, through `capDig_eq4` ("level
`i`'s cap entry on the log is π's **where `posOps4` compares**") — i.e. from the per-position
`assertEq cur c` that (β) deletes. S-G consumes them per level: `TailLig.colOf_of_path` /
`foldAt_of_cols` turn V's fold of the *opened* column into `foldAt` on the *log's* column (which is
what `truthP2`, `truthP3`, `consErr` are defined on, via `wordOf`/`colL` under the cap), and
`truthP3_four_of_cols` discharges Pf's background doom `¬ truthP3 4` from exactly this per-query
path fact. `DT 51 = DPf`, `phOf_ge : 468 ≤ p → phOf4 p = 51`, `fsStarts4_eq` ends at 468: the FS
entry count and the last phase index are literals in statements.

**Failure scenario.** Build A2–A4 as the memo says: `posOpsG` accumulates `acc_I`, `acc_II`, the
finals check (I)/(II). Then `ys_facts4` is unprovable (no run fact gives `openPath … = capDig` for
a single `q`), `FinRest4.cols` cannot be instantiated, `truthP3_four_of_cols` and the level-`i`
bridges `DP3 i` lose their hypotheses, and the tail's `kstate` does not compose. Nothing in the
memo's A3 ("`capChk_sound`; the Q-phase doom gains the two SZ rows") names where the per-query
fact comes back from.

**What is actually needed (sound, and the right shape).**
1. `FinRest4.cols` becomes: for every `(i, q)` there are `col, ss, y` with `y i q = fold(col)` and a
   *computed* path digest `d_{i,q} := (openPath … ).runLog L`; plus the two identities
   `Σ_r ζ^r·d_r = Σ_k A_k·cap[k]` (as F-halves) and `Σ_k A_k z^k = Σ_r ζ^r z^{k_r + off}` with
   `A` the absorbed field and `z` the CapChk squeeze. (`capDig_eq4` stays: it is about the absorbed
   cap, not about the compare.)
2. Two new per-squeeze bad events: `D_ζ` at P3.4's first squeeze (`kcAt es 4 0` read as K):
   "`∃ r, d_r ≠ cap[k_r]` and `Σ_r ζ^r (d_r − cap[k_r]) = 0`", size `≤ 870` in `K`; `D_z` at the
   CapChk squeeze: "`A ≠ (Σ_{r: k_r = k} ζ^r)_k` and (II) holds", size `< 1,920`. Charged `870/2^256`
   and `1,919/2^256`. (P3.4's row today is **0**, `finP3 4 = finP2 4` — "κ_c⁽⁴⁾ changes nothing" —
   not the memo's `9/2^128`; the sum is immaterial for `εR`.)
3. The assembly: `accept ∧ ¬D_ζ ∧ ¬D_z ⇒ ∀ r, d_r = cap[k_r]`, after which today's per-level
   derivation applies verbatim. This is a doom established at the *end* of the log and consumed by
   the level-`i` dooms over *prefixes*; in the `msD` chain it is cleanest as: the level-`i` doom's
   statement keeps the log-side `truthP3`, and the bridge from V's check to it takes the binding as
   a hypothesis discharged by the final case split (the Pf doom `DPf` already has this "background"
   shape for level 4). Either way `DT` gains a phase 52, `fsStarts4` an entry 470, `phOf_ge`'s 468
   and 51 move — the "P4: none, R4: no statement changes" line is false for these literals too.
4. ε: unchanged, `εR = 15/2^124`, the maximum row stays P2's `2^-120.36` (§5.2; the memo says "the
   E/Z rows'", a slip). `claim.json` unchanged.

Fixed-before-ζ, circularity, the extractor: fine — see §3 Q1.

**Fix.** A3 is "the two SZ dooms and the restated `cols`" (S-G + R4, one owner); A4 re-runs
`R4Acc`/`R4Run`/`R4Ref` *and* rewrites `R4Cols` and `R4Tail`'s structures; add `FRX4Prog`/
`FRX4Ext`/`FRShape4` (the `798192` literal in `szPs` and its lemmas) and S-H4's `reassemble` row 18
to A2's deliverables.

### PK-M3 — the two-region slot contradicts the copy identity and the cell plan

**Facts.** `InSlot π rows` requires, for every row of prototype `π`, the row index inside
`[π·2^20, (π+1)·2^20 − linkN)` **and every cell of every matrix inside `[π·2^20, (π+1)·2^20)`**;
`ProtoFit` is `InSlot` for both prototypes; `slotV4` scales a prototype's value by
`hiF lm t σ · hiF lm u σ` — the *same* `σ` on rows and cells. The memo itself states the
consequence (§1.2): "`copy_val` needs every cell of a copied row inside the slot's region; every
row with an [outside] entry leaves the copy and is evaluated per slot".

**Failure scenario.** Region A = slot 0's region holds prototype 0; region B (the spare) holds its
arenas. Prototype 0's position templates (the `dotKF` folds, the Merkle mux rows, the pins, the
cap-check products: the ≈ 100 k consuming rows §5.2 says "read arena₂") now reference cells in
region B. `ProtoFit` is false (`inR` false at process start → the rejecting row: the node is
unprovable). If `InSlot` is relaxed, `slotV4`'s factor is wrong for those rows, and they must be
evaluated by a new "cross-region local" class — per slot for prototype 0 only — so the "≈ 11 ms
per node, once" of §5.4 does not hold for the previous-node slot, and the two prototypes no longer
share the arena₂ link's low-coordinate MLE (the memo's §5.2 argument needs *the same arena
addresses in both prototypes*).

**Cells.** `A₁` aligned to `2^17` above the prototype's cells (`4 … 190,583`) forces `A₁ = 2^18`;
arena₂'s 132,096 allocated cells at any `2^a`-aligned base above `A₁ + 96,527` end past
`2^19 = 524,288`, S-E14's `R` cell range `[2^19, 2^20)` (JOURNAL §0). With the bits (8,320) and the
cap-check chains (≈ 40 k cells) the arena side needs ≈ 280 k cells above 190.6 k: it fits below
`2^19` only if packed without the `2^17` alignment, or if `R`'s cells move.

**Fix (the memo's own numbers make it fit).** Slot 0's region: prototype (730,493 as laid, i.e.
including its 127 k of alignment gaps) + arenas 213 k + cap check 40 k + link 32,768 =
**1,016,518 (97 %)** before the levers, **925,518 (88 %)** with S-E6's two levers (PK-M4 says the
Merkle saving is 0, so no −15 k here either). The spare region: `R` without `evalM` 221 k +
`evalM` replay 250–320 k (+ PK-M6's 30 k) = **≈ 500–570 k (48–54 %)**, all of its `2^20` cells free.
Then every slot's arenas are at the same M-relative offsets, the copy identity holds for both
prototypes, and `R`'s rows (keyed closed forms, not copies) may read region A's cells from region
B as S-E14 already planned. `nodeLayout4`, `N_M`, the mux and `lSlots` are untouched;
`NodeKind.mSlot`, `InSlot`, `hfit4`'s "selector copies below `oneCell + vslots·2^20`" bound and
the plan's `ProtoFit` check must learn that region `vslots` is slot 0's second region (N2: 3,
N4: 5).

### PK-M4 — the Merkle mux rows are not 2 per step, and the saving is not real

**Facts.** `merkleOpsG`: per depth `h`: `piDigest` (sib), `bitOf`, `selectHalf (b+1) cur b → l`,
`selectHalf (b+1) b cur → r`, `askNode … act`, **`keep act ans cur`** (carry `cur` through a
dummy depth), `assertZero b (¬act)`. `selectHalf` compiles to `muxOut`: one row per component,
2 per digest, so 4 per step (30,208 per slot — the memo's figure); `keep` with a kind-varying
`act` compiles to `muxOut` too: **2 more rows per step, 15,104 per slot**, which the memo's table
does not list. `assertEq`/`assertZero` rows are gated by `P.gate act` as their `A` factor.

**Failure scenario.** Replace the four `muxOut` rows by `b·(l + r) = cur + l` per half (one R1CS
row `⟨b, l + r, cur + l⟩`, 2 per step). At a dummy depth of an `L30`/`L31` child the payload is
pinned `0^64` (the memo's own AskBound row), so `l = r = 0` and the row reads `0 = cur`: the
carried `cur` must be zero, which an honest `L30` segment violates at every position (its
`cur` at depth 9 is a real digest). The row must be gated: `v = b·(l + r)`, `a·(v − cur − l) = 0`
— 2 rows per half, **4 per step, as today**. (`a·b` cannot be folded into `b`: both are witness
cells.) The sibling alias `sib = l + r + cur` has the same dummy-depth problem (`assertZero b`
says `sib = 0` there while `cur ≠ 0`): it is sound only as a **per-kind slot** (`CS.slotK`: the
form for `h < sib κ`, the zero cells otherwise), which the compile supports (S-E12f) but the memo
does not say (PK-m3).

**Row budget, recomputed (segment slot, one region, memo's other figures kept).** The memo's
1,030,702 is `725,885 − 30,208 + 15,104 + 213,257 + 40,000 + 49,000 + 32,768` (the `keep` rows are
already inside the compiled 725,885). With the `selectHalf` rows kept and no new mux rows the
`−30,208 + 15,104` term is 0: **1,045,806 (99.7 %)**, 2,770 rows spare before the levers,
**954,806 (91 %)** with them. With PK-m1's arena₂ recount (+2,613) and the cap check at the memo's own 40 k (§3.3 says
37 k in one place and 40 k in another) the pre-lever figure crosses `2^20`. **So S-E6 §5's two
levers (`phiRS` 134-in-256 −62 k; skeleton padding −29 k; both unapplied: `logs/S-E13a/
nodedump4-run.log` shows 603,404 indexed rows in a 730,493-row region, S-E12c lists `phiRS
512 × 134`) are a prerequisite of B2**, to be built and measured before the arena rows are laid,
and N8's "1.06×" is "1.046× under `N_M/1.05`" at best. Note `mRows4_le` is a *model* theorem on a
stale `protoRowsN = 551,805` (S-E14 §3.4); the operative constraint is `ProtoFit` per region.

### PK-M5 — the `V̄`/ΔS arithmetic mixes two `v_ref`s and two "todays"

**Facts.** `season.toml`: `κ = 0.2667 = 1.5 · v0`, `v0 = 177.8 ms`, `s_ref = 2 MiB`, `v_ref =
T_triv/10` measured per run; S-I's season run 40809858010 on the 7763 measured `T_triv = 2,065.7
ms`, **`v_ref = 206.6 ms`, `V_i = 143.6–162.4 ms (mean 157.9), |π| = 798,192`, `x ≤ 1.167`,
`V̄ = 0.400 s`** (HEAD `48d25ef`, P2⁶: before S-E13a/b's rows and before `R`). The memo's "today
`x ≈ 1.39–1.44`, `V̄ = 0.71–0.79`" is changes 28's figure computed with `V/177.8` and a loaded VM
V of 213–223 ms; the memo's plan figures use `V/206.6`.

**Recomputation on one basis** (`v_ref = 206.6`, `|π| = 859,664`, VM→7763 at the memo's 1.19;
the memo's ΔV is relative to a 215 ms "today" that it says excludes S-E13a/b's rows, as the runner
measurement does):

| Case | ΔV VM | V runner | `x` | `V̄` | Δ`V̄` vs measured 0.400 |
|---|---|---|---|---|---|
| memo best (+50–58) | +50–58 | 200–207 | 1.378–1.412 | **0.70–0.75** | **+0.30 … +0.35** |
| memo worst (+94) | +94 | 237 | 1.557 | 1.01 | +0.61 |
| with this review's corrections: automaton ×2.5 (PK-m2, +15), WOTS replay (PK-M6, +10–18), V's own check at 9 ms unless the power table is indexed (PK-m11, +4) | +79–95 | 224–238 | 1.49–1.56 | 0.88–1.01 | **+0.48 … +0.61** |

So the price of the sound node is **≈ +0.3 s of S at best and ≈ +0.5–0.6 s as priced here**, not
+0.1–0.2; the memo's "−25 ms levers bring it back to 0.75–0.80" is likewise on the wrong base. This
changes the weighting of §8's reserve (option (2), the child's `evalM` in the parent's PIOP, whose
V cost is ≈ 2 ms) against the `evalM` replay (7–40 ms): the reserve should be priced on this basis
before D1 is started, not after.

### PK-M6 — the `evalM` replay still has to replay the child's irregular link rows

**Facts.** S-E14 JOURNAL §1.6: the child's `R` must include "the child's link region: S-E12c's
link rows, S-E13a's 2 × 8,906 pack rows and S-E13b's 7,992–8,680 WOTS/`aggPad` rows — irregular H
cells: one product per entry ≈ 90 k". §5 of the memo replaces the **pack pins** (they move into
the position templates) — but S-E13b's rows (25–35 k entries at slot 1: the 128–130-term packing
rows) and S-E12c's link rows stay irregular, the memo's own §6.3 prices the *parent's* evaluation
of them at 7 ms "templatable to ≈ 2", and the `aggChk` rows (B4, 1.3–2.7 k with a 64-bit adder)
are new irregular rows.

**Failure scenario.** D1 lays the replay at 250–320 k rows with "the child's arena₂ automaton as a
60-row template" and finds that `replay_mle` has no term for the child's WOTS rows: either `R`
gains ≈ 30 k product rows whose eq-table reads are at the child's constant (row, cell) pairs —
sparse rows for the parent, ≈ 0.6 µs each, **×3 kinds in the mux ≈ 15–50 ms VM** — or the WOTS,
`aggPad`, link and `aggChk` rows are templated first so that their `Ĉ` is a closed form. The
second is cheaper and also takes the parent's own 7 ms to ≈ 2 (§6.3), but it is a stage (C0) the
build order does not have, and it must precede D1.

### PK-M7 — the certificate build budget is not in the plan

**Facts.** S-I: `lake build FR` 882 s on the 7763 against `build_s = 600` (REJECT before the
benchmark); 307 modules, 2,975 CPU-s, ≤ 2,020 needed (≤ 1,550 for 1.3×). S-E13a/b/14 measured
their new modules at 7–25 s wall each (`FRNodeRows4Fit` 24.8 s, `…WotsL` 16.1 s, `…Ext` 20.9 s
with 11.7 s of kernel for one `simp` length proof). The memo adds: `FRVIRCompile` (`Arena`,
`Slot` as linear forms for the sibling and the `chK` aliases, which touches `RepS`, `comp`,
`muxOut`, `imports` and the invariant of `compileX_soundK`/`_soundR`), `FRVIRCompileSound`,
`FRNodeRows4Arena`, `FRVIRTplArena` (three automata with `tpl_mle` proofs), `FRNodeRows4Run`
(≈ 400 lines), `FRNodeRows4Agg` (new rows), six `RT` templates with `RTOk` proofs
(`FRNodeRows4Rep*`), `FRNodeRows4RepM` (`replay_mle`, `replay_sound`), plus the restatements of
PK-M2 in R4/S-G and the two-region edits in Fit/Plan/Model/Hint/PackSound. By S-E13's measured
rate that is ≥ 150–250 CPU-s more on a build that must lose ≥ 950.

**Fix.** Every track in §7 records its modules' CPU-s (`--profile`, one core) in its RESULT; the
retirement steps (changes 27 (B) 2–4, RET-2/3, G2) are placed in the order **before F**, and F's
definition of done includes `evaluate.py cert` under 600 s, not only `HARNESS: ACCEPT`. The
`decide +kernel` facts over `seq4`'s shapes (`streamBytesOf_seq4`, `phasesOf_shQ4`, `shAl`,
`fsStarts4_eq`) re-run with one more phase; keep them on shape parameters as S-E13a did.

---

## 2. Minors

- **PK-m1 (arena₂ count).** Position groups 147/92/78/64/57 × positions 290/178/145/132/126 =
  42,630 + 16,376 + 11,310 + 8,448 + 7,182 = **85,946** copy rows, not 83,333 (§6.1) or "≈ 88 k"
  (§5.2); allocated cells 290·256 + 178·128 + 145·128 + 132·64 + 126·64 = 132,096 ✓. Per-level
  strides hold (`147 < 256`, `92 < 128`, `78 < 128`, `64 ≤ 64`, `57 < 64`); level 3 has no slack.
- **PK-m2 (the shift-window automaton's constant).** `Σ_{q<S} eq(τ_lo, q)·eq(u, X + q)` from the
  LSB: states = carry (2) × "`q < S` so far" (2); per bit two transitions (`q_b`), each a product
  of the `τ`-factor and the `u`-factor plus an accumulate: ≈ 4 × 2 × 2 = 16 products per bit
  × 8 bits = 128, then the high part `eq(u_hi, (X + q)_hi)` for the two carries ≈ 2 × 12: **≈ 150
  products per instance, not 60**: 871 × 150 × 0.2 µs ≈ **26 ms VM per node** (the memo allows
  "a 2× miss gives 30 ms", so this is within its stated uncertainty, but §6.3 uses 10.5). The
  shift-by-constant automaton (160) and the diagonal range sum (300) are right. All of this is in
  `F` (`evalMT4 (t u : ℕ → F)`), so the 0.2 µs unit applies.
- **PK-m3 (per-kind aliases).** The sibling alias at dummy depths, the `bitOf` slots (`Out.kin`),
  the `z^{k_r}` bit-products (`k_r = j >> sib κ`: the *position* of the 9 cap bits inside `j`
  depends on `κ`), and `tensorW`'s `bits 20/19` must go through `CS.slotK`; rows cannot be
  per-kind, so a row that reads a per-kind cell needs the kind mux `Σ_κ s_κ·cell_κ` (+1 linear row
  per such read: +9 per cap read ≈ +7.8 k per slot) or a kind-independent re-basing of the bits.
  Say which.
- **PK-m4 (the spacer in the reader and in the rows).** `sgn4` builds an aggregate's trace as
  `(List.range k).map slotTr4 |>.flatten` — with R-A′ the trace `V_A` runs has the spacer entries
  between segments, so the reader must insert them (their query is the constant
  `absorbQ 0³² 0^s`, their answer the 32 stream bytes), and the circuit must pin the spacer's
  state and message bytes (not only its length word): 129 B = 9 elements, ≈ 9 pin rows per
  spacer. `VA_queries_le`'s `4·qS` becomes `4·qS + 3`. `segTr`'s offset `1 + i·(segB − 1)` becomes
  `1 + i·(segB − 1 + 129)`.
- **PK-m5 (ε text).** P3.4's row is 0 today, not `9/2^128`; the per-fresh-query maximum is P2's
  `2^-120.36`, not "the E/Z rows'"; `εR` and `claim.json` unchanged — correct conclusion, wrong
  sentences.
- **PK-m6 (the plan's 2 s).** B-16's cap is met at 1.80–2.03 s (S-E12c, S-E13a 1.94–2.42 with the
  fold). The arena tables, six `R` keys, the replay's keys and the extended `ProtoFit`/`xOkK`
  checks are all process-start work; the memo prices none of it. Each of B2, C1, D1 must
  re-measure `plan4t init`.
- **PK-m7 (uncounted small rows).** FS links are 467 (the seed has no state), not 468 × 2; the
  previous node's `stmtOk4` needs the `hashB1`/`hashB2` message cells tied to the proof's `stmt`
  field (8 element rows) and `hashB2.h_in = hashB1.h_out` (2 rows) — the table gives 0; the
  segment's `hashA` message (`tagLeaf ‖ e ‖ enc64 n`) is tied to the *view* cells, which `aggChk
  (c)` also reads: the 8 gated rows should be stated once, in B4.
- **PK-m8 (the 0.06 µs unit).** INT-9's 85 ms / 1.46 M rows is an average that includes the two
  prototypes' 77 k sparse skeleton rows at ≈ 0.6 µs (≈ 46 ms); the structured rows cost
  ≈ 0.03 µs. The memo's per-prototype figures (2.5 ms for 70 k rows) are conservative; fine.
- **PK-m9 (§8's reserve).** Correctly shaped (a public multilinear at a witness point, the eq table
  never materialised, `eq(r_child, r_parent)` from H cells), but "no change to `KState`/ε" is
  optimistic: it is a new sumcheck family with a witness multiplier of degree 3 over 23 rounds —
  a new per-fresh-query row (`3/2^128` per round, within `εR`) and a new S-C/S-G phase. Keep it
  as the reserve; price its Lean cost against D1's before D1 (PK-M5).
- **PK-m10 (statements the memo says do not move, but do).** `FinLog4.cols`/`FinRest4.cols`
  (PK-M2); `phOf_ge`'s 468/51 and `DT`'s `k = 51`; `fsItems_length = 468` (`FRSoundness4Pos`);
  `FRX4Prog.szPs`'s `798192` and `FRX4Ext`/`FRShape4`'s copies; `traces_le_qV` (`4 · 8,905`);
  `segTr_length`/`slotTr4_length` (8,905); `aggChainLen_eq`'s residues (63/61/62 → 0 with the
  129-B variant, which is the point of R-A′); S-H4's `reassemble` (A.3 row 18). INT-10's
  `SegSoundLog`/`RunFacts4.seg` size hypotheses are stated as `piSizeOf seq4` and are unaffected
  in statement; `piSize_aggSegs` re-runs.
- **PK-m11 (V's own cap check).** The memo's count (1,919 + 3,840 + 1,920 + 7,839 ≈ 15.5 k
  K-equivalents) at its own "a K product ≈ 3 F products" is ≈ 9 ms, not 5. V need not form
  `z^{k_r}` by bit-products: it has `zpow[k]` for all `k < 1,920` and can index it (native
  code), which drops the 7,839 and gives ≈ 5–6 ms. Say so; the bit-product form is the circuit's.
- **PK-m12 (the structured-row price for the sub-slots' `R₁ + e` rows).** The arena₁ ↔ H rows
  are `one · (M − H)` rows with two cells; their `B̂` side has the H term per slot (0.1 ms) ✓, but
  the `Â` side (`one`) and the M term are range sums over `R₁ + e` that depend on `R₁` only —
  shared across slots; fine, but §5.3 item 1 counts them per slot.
- **PK-m13 (INT-10 interaction, for the record).** R-A′ changes the *trace*, not `π_A`:
  `aggSegs`, `segView`, `VAwith`'s size check `48 + k·segSize`, the extractor's segment parse and
  INT-10's size hypotheses are untouched. The `W`/DoS column sees three more fixed queries per
  aggregate (≈ 0 ms).

---

## 3. The brief's questions

| Q | Answer |
|---|---|
| 1. (β)'s soundness in the certified model | **Sound in principle; the accounting is misdescribed (PK-M2).** `cur_r` (V's path output at depth `sib κ`, the kind from the seed), `k_r` (`idx` bits of P2.i's answers), `cap` (C.i absorbs) are all determined by items `≤ Q.4`; P3.4's first squeeze follows Q.4 (`fsStarts4`: P3.4 at entry 463) and its `κ_c⁽⁴⁾` is **unused** (`finP3 4 = finP2 4`), so reusing its first 32 bytes as `ζ ∈ K` has no circularity and costs no second use; `A` is absorbed after `ζ`, `z` squeezed after `A`. The two bad sets are prefix-determined and of size ≤ 870 and < 1,920 in `K = GF(2^256)` (B-4: `K = F[u]/(u²+u+α)`, `F = GF(2^128)`; `chK` reads all 32 bytes): `≤ 2^-246` each, so `εR = 15/2^124` and `claim.json` are unchanged (max row P2's). The extractor's decoding reads the log's columns under the cap (`colL`) and is unaffected; what changes is how the per-query `openPath = capDig` fact reaches S-G's per-level bridges: it is now available only after CapChk, under `¬D_ζ ∧ ¬D_z`. A fresh ζ squeeze buys nothing. |
| 2. R-A′ | The spacer interacts with: `VAwith` (the programs), `sgn4`/`segTr` (PK-m4), `aggB`/`aggL`/`tailIvs`/`AggPad4`'s `r` (PK-M1: `r = 64` only in the block-aligned variant), `hUsedN`/`regions_fit` (recomputed above), `VA_queries_le` (+3), `kindS`/`wf` at `i ≥ 1` (follow by the block shift, as the memo says), the spacer pins. `hdr_A`, INT-10's size hypotheses, the extractor's segment parse: untouched. "Positions before `Pf` do not move" is true for `seq4`'s positions; R-A′ touches none of them (it is `V_A`'s program, outside `seq4`). |
| 3. The arenas | Closed forms are real: the diagonal range sum (≈ 300), the shift-by-constant carry automaton (≈ 160), the shift-window automaton (**≈ 150 per instance, not 60**: PK-m2). Prices at 0.2 µs/F product: arena₁↔H 0.1 ms per slot ✓; arena₂↔arena₁ **≈ 26 ms per node** (10.5 claimed), once per node only after PK-M3's fix; templates ≈ 2.5 ms per prototype ✓. The H binding is sound: `sCell b0 e` is the F element whose 16 bytes are stream bytes `[16e, 16e+16)` (`chainBytes4_elem`, `readByte_cell`), the copy row equates F elements, and equality of F elements is equality of the 16 bytes; the bit decomposition `eq(σ, sCell) = eq(σ_{2..6}, 10000)·eq(σ̃, 4b0 + e)` is right (`4 + e mod 4` occupies bits 0–2 with bit 2 set, `b0 + e/4` starts at bit 7). The seed's 1-byte offset is already absorbed by `items_aligned` (every item after the seed is 16-aligned at offset `≡ 0 mod 16` because `1 + 159 = 160`). |
| 4. The two-region slot | Breaks `InSlot`/`ProtoFit`/`slotV4` as laid (PK-M3); with the arenas in slot 0's region it breaks nothing: `nodeLayout4` (H), the mux, `N_M`, `lSlots` are untouched; `mSlot`, `hfit4`'s selector-copies bound and `ProtoFit`'s check must name the second region. N8 has no previous node, so none of this touches N8; N8's "1.06×" is **1.046× under `N_M/1.05` with the levers** and **does not fit `2^20` per region without them** once PK-M4 and PK-m1 are applied (the memo's own pre-lever 98.3 % was already 1.7 % of slack). The stale `protoRowsN` is not the memo's problem (it uses the measured 725,885 / 730,493), but `mRows4_le` must be re-based on the measured prototypes and the new rows, or retired in favour of `ProtoFit`. |
| 5. V and the score | V(N4) ≈ 265–273 VM is low by ≈ 30 ms on this review's counts (≈ 295–305 best); the `V̄` formula is right (`season.toml`: `κ = 0.2667`, `s_ref = 2 MiB`, cubic above `x = 1`); `v_ref = 206.6` is the measured value of run 40809858010; the memo's "today" is on `v_ref = 177.8` — **ΔS ≈ +0.30 … +0.35 s (memo's V) or +0.48 … +0.61 s (corrected), against the measured `V̄ = 0.400`** (PK-M5). |
| 6. Missing items | Foreign flags (12/79): listed as open, fine. Auxiliary imports: `felems` → arena₂ ✓, `bits 20` → L bits ✓ with PK-m3. `stmtOk4`: PK-m7. `aggChk`: B4 ✓ (its `c_A` half needs no rows, S-E13a §6). `input`: ✓ (`vk`/`c₁` to `seedC`, a segment's `c` to `hashA`). `kindS`/`wf` at `i ≥ 1`: ✓ by the block shift. **Missing:** R4/S-G restatements (PK-M2), FRX/S-H4 constants (PK-m10), the spacer entries and pins (PK-m4), the WOTS/`aggPad`/link templating before D1 (PK-M6), the build budget (PK-M7), the plan time (PK-m6). Lean cost: the memo's plan is at least S-E13a + S-E13b + S-E14 in size again, on top of a build 1.47× over its cap. |
| 7. Simpler alternatives | B2: (a)/(j)/(j″) rightly rejected on N8's H (54 %/28 %/14 % against 4.3 % of slack); (b′)/LogUp-GKR rightly deferred; a `z` taken from the *parent's* transcript (A as M cells, no bytes in π) was not weighed — it saves 61 KB of `|π|` (−0.03 s) but makes (II) a parent-PIOP phase (the memo's rejected class (b)); not worth it. B1: no spacer-free variant exists (any appended CapChk has `len ≡ 0 mod 16`, so `segB − 1 ≡ 63 mod 64` stays; the misalignment is the `0x54 ‖ seed` prefix), so R-A′ is forced; S-E13a's 129-B form is the consistent one. Arenas: a one-arena layout with stride-147 instances costs 60–150 products per instance **per slot** (≈ 50–130 ms per N4) — the two-arena form is right. The Merkle mux: keep `selectHalf`/`keep` as compiled (PK-M4); only the sibling *import* is removed. `R`: keyed templates are the only V-feasible form (S-E14 §1.10 agrees); the memo's per-op row counts are unproved but plausible. |

---

## 4. Verdict and the corrected build order

**Adopt with the listed fixes.** The constructions are the right ones; the memo cannot be built from
as written because its byte arithmetic (PK-M1), its region split (PK-M3), its Merkle row count
(PK-M4) and its score delta (PK-M5) are wrong, and because two tracks it marks "no statement
change" are restatements (PK-M2, PK-m10). Re-issue §2, §3.3–§3.4, §5.2, §6.1, §6.3 and §9 with
`seq4`'s constants and the figures above, then start.

**Corrected order** (owners as in the memo; each stage records its modules' CPU-s):

| # | Stage | Change from the memo |
|---|---|---|
| A2′ | `CapChk` with `≡ 0 (mod 64)` stream bytes (`A` padded to 61,472 B), `piSizeOf seq4 = 859,664`, `items 8,907`; `posOpsG` accumulators + finals; `FRX4Prog`/`FRX4Ext`/`FRShape4` literals; S-H4's `reassemble` row 18; the shape `decide`s re-run | PK-M1, PK-m10 |
| A1′ | R-A′ with the **129-B** spacer; `aggB k = 64·(L₀k + 2k − 2)` whole blocks; `sgn4`/`segTr` with spacer entries; spacer pins; `VA_queries_le` `4·qS + 3`; `AggPad4` with `r = 64` and S-E13b's `padRows` without the decomposition | PK-M1, PK-m4 |
| A3′ | S-G: `D_ζ` at P3.4's first squeeze, `D_z` at phase 52, `DT`/`fsStarts4`/`phOf_ge` extended, the end-of-log binding feeding the level-`i` bridges; R4: `FinLog4.cols`/`FinRest4.cols`/`ys_facts4`/`cols4_of_run` restated as the two identities + computed path digests; `R4Acc`/`R4Run`/`R4Ref` re-run | PK-M2 (one owner for S-G + R4) |
| B0 | S-E6's two prototype levers built and measured (`ProtoFit`, `plan4t`), **before** any arena row | PK-M4 |
| B1′ | Compiler aliases (`Arena`, per-kind alias slots for the sibling/`bitOf`/`z^{k_r}` bits, `Slot` forms); `keep`/`selectHalf` kept; `compileX_soundK` with `ArenaOk` | PK-M4, PK-m3 |
| B2′ | Arenas, FS links/pins, bit rows, cap-check templates **in the slot's own region** (slot 0 included); the spare region holds only `R` + `evalM`; `tplArena_mle` with the automata at their real constants; V measured; plan time measured | PK-M3, PK-m2, PK-m6 |
| C0 | Template S-E13b's WOTS/`aggPad`, S-E12c's link rows and B4's `aggChk` rows (chain stride 3, path stride 2) | PK-M6 |
| B3, B4 | as the memo (`compileFromX_run`, `aggChk (c)`), B4 with PK-m7's rows | — |
| C1, C2 | as the memo (the six `R` keys; drop the dead segment ops) | — |
| D1 | `evalM` replay in the spare region, with C0's `Ĉ`s; **decide D1 vs §8 on PK-M5's basis before starting** | PK-M5, PK-M6 |
| E1 | P2 as the memo, plus the spacer entries and the padded `A` | — |
| RET | changes 27 (B) steps 2–4 / RET-3 / G2 to bring the build under 600 s | PK-M7 |
| F | S-I: `claim.json` unchanged (`ε`, `qV = 36,000`); `evaluate.py cert` ≤ 600 s is part of done | PK-M7 |

What this review did not do: no Lean probe was run (every cited fact is a theorem or definition
already in the tree, or arithmetic shown above); no row count of a template that does not yet
exist was independently derived beyond the automaton (PK-m2) and the arena₂ sum (PK-m1); the
memo's `R`-key product counts (§6.2) are taken as its estimates.
