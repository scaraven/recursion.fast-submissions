# E1 RESULT — the native prover at revision 4.4.1 (`v4/rev44`)

Track E1, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`; started at HEAD
`e464756` (A1′), finished against HEAD **`7537acd`** (B4, after PORT `c4eca2b`). Prover
`submissions/flock-recursive/prover/` (P2⁹'s crate at start, `prover.s` `1b84a5f1…`). Logs `logs/E1/`;
journal `E1-JOURNAL.md`. Lean build tree `logs/E1/fr-build` (a copy of `fr-build-A1`, every source a HEAD
copy, re-snapshotted at `7537acd`; the HEAD-red RSV-S declarations stubbed in the tree's copies only by
A1's `scaffold/apply.sh`). Nothing committed, no sub-agents, nothing pushed. Every cargo/lake/lean run in
a 16 GB scope with a timeout.

## 0. Summary

| Item of the brief | State |
|---|---|
| 1. Everything but B4's rows; a hook for them | done, and **B4's rows are filled** too (B4 landed during the track): a table-driven link-row solver (`node::solve_aux`, `AUX_L`) |
| 2. Segment proofs at the new format | done: 20 fields, `|π|` 876,304, level-4 cap 8, siblings 4/3/2, the (β′) phases `CapD`/`CapZeta`/`CapChk`/`CapChkZ`, `fLrEnd` 1,008 / `fEEnd` 112; spacers between an aggregate's segments |
| 2. Node proofs N2/N4/N8 | done: layout (spacers, L1), phantom pins, spacer bits `spC`, packed plan form, RSV2's reserve (60 child-claim values, E2/E4 child terms, `m̂*`, B′'s 60 cells), the stacked `evalM` in the IR, B4's `aggChk` cells |
| 3. End to end: the rev44 Lean V | **every node proof accepted**, every canary rejected: a 10-node kind-changing chain at `7537acd` (§3.1), a service stream of 8 steps with the full-length first step (§3.2), the A/B stream (§4); aggregates with k = 1, 2, 3, 4 |
| 3. Decoder `nd` (orchestrator) | **output stage EQUAL** on N8 (k 1 and k 4 + 4), N4 (k 4, previous N2), N2 (k 2, previous N4); canary mismatches (§3.3). `decF04` itself cannot run (≈ 2.7·10^13 cost units) |
| 3. P̄, worst first step, M = 96 fit | §4 (VM A/B scaled to the 7763 by the base's own per-step ratios) |
| 4. V's B5 plan self-check printed | `e1verify --plan`: `plan: inR true lk2.eok true lk4.eok true lk8.eok true (lkArr N2/N4/N8 true/true/true)` |
| 5. Determinism | two clean `build-asm.sh` runs: **`prover.s` identical**, 22,984,542 B, sha256 `aac53ced3f8dfcc248474a30cb6477c9d4d75d7bc26f3fd8f2574fa684096d0e` (`logs/E1/asm/det.txt`) |
| cargo test | 56 passed, 1 ignored (`logs/E1/cargo-test-3.txt`) |
| source rule | 422 files, 0 findings (`logs/E1/source-rule.log`) |

## 1. What changed in the prover (crate 17,868 `.rs` lines, was 16,884; +1,072 −88)

| file | change |
|---|---|
| `params.rs` | 20 fields (`F_D` 18, `F_A` 19), `FIELD_SIZES` at HEAD, `PI_SIZE` 876,304, `CAP_LOG[4]` 8, `STAR_SIB[4]` 4, `N_ITEMS` 8,783, `N_FS_ITEMS` 486, `CAP_READS` 871, `CAP_ENTRIES` 1,536, `CAP_OFF`, `LREND_LEN` 1,008, `EEND_LEN` 112, the reserve offsets |
| `items.rs` | the four cap-check phases; Lrend/Eend lengths (`reassemble` takes `D`, `A` like any absorb) |
| `ligerito.rs` | **(β′)**: `cap_check` after Pf (absorb `D` = each read's cap entry in read order, `ζ = chK`, `A_g = Σ_{r: off+k_r = g} ζ^r` by `selectors`, absorb `A`, squeeze `z`); the native verifier reads `D_r` statically, asserts `cur = D_r`, checks (I) lo/hi and (II) |
| `leaf.rs` | a segment's Lrend (1,008 B) and Eend (112 B) zero |
| `agg.rs`, `ir.rs` | the spacer `absorbQ 0³² 0⁴⁹` (`"FRABS000" ‖ 0^81`) between segments (prover, native `V_A`, `ir::run_agg`) |
| `node.rs` | layout (`SEG_B` 1,551,104, `C_LEN` 24,236, `SPACER_B` 129, `S_BLK` 24,238, `agg_b` with spacers, `h_used` with one `WM` per signed child); `agg_in` splits `k·8,783 + k − 1` entries; **`agg_stream`**: an aggregate child's main-chain bytes with the phantom constants of every inactive sub-slot (spacer elements 0–5, each item's `enc64 |q| ‖ tag`, the seed element's bytes 1–15; the kind element 5 zero); **`spC`** cells (spacer answer bits, replacing S-E13b's element-7 bits); **`solve_aux` + `AUX_L`** (B4); the `agg_chk_fill` hook (empty, documented) |
| `nodeprove.rs` | **RSV2's reserve**: `child_claim` (the 60 values at `rsvRel`), `fLrEnd = vl ‖ p_x ‖ p_y ‖ s ‖ X₃`, E2 with the extra pair `(η·eq(p_x), Σ s M̃(·‖hi, p_y) + X)` (`zc_abc_x`), `fEEnd = vm ‖ m̂* ‖ 0^48`, E4 with the pair `(Σ s M̃(x̂, ·‖hi), κ_E⁴·eq(p_y))`, B′ with the 60 cells at `κ′^{11…70}`; **factorized** child tables (`proto_matvec` at `eq(p_y[<20])`, `proto_scatter` at `eq(r_E2[<20])`, once per prototype for every slot and kind, landed into the parent's rows/cells with the constant extension: `land`, `add_run`); the own `W_M(r_E2)` from the same `T_π` (`own_w_m`) |
| `nodeops.rs` | **`eval_mx`** (`evalMX4`: the two prototype sums shared by every slot and kind, then each kind's slot factors and link rows), `eval_mx_ref`; tests `eval_mx_matches_ref`, `layout_figures` at rev44 |
| `sumcheck.rs` | **`prove_pairs_support`**: several sparse pairs, each with its own live chunks, the dense side a table or `Q::Eq` (closed-form eq, never materialized); test `pairs_support_same_messages` |
| `ir.rs`, `plan.rs` | `NodeCtx` with the three kind tables (`NodeCtx::new`, `kt()`), `evalM` on a 32-entry point = `eval_mx`; `kind_tabs`, `kind_tabs_static` |
| `mfill.rs` | `LONG_FORM` 256: a register form of more terms is not kept (only single-cell forms are written; A2″'s cap-check running sums were 90 % of `mregs`); default dump `logs/E1/nodedump` |
| `mle.rs` | `eq_table`'s copy step in parallel |
| `kat.rs`, `items.rs`, `ir.rs` | default dump `logs/E1/dump` |
| `main.rs` | `PROVE-LEAF`/`PROVE-AGG` print the statement; `node-kat` prints `vk`/`c`, `FLOCK_PROF` spans, `--dkat DIR` (the decoder KAT's inputs) |
| `nodeblob.b64` | from `logs/E1/nodedump` at `7537acd`: 11,367,584 B (raw 46.6 MB; was 7.4 MB: the kind tables carry A1′'s pins at every sub-slot and B4's rows) |
| `prover.s` | regenerated (§0) |

π identity was kept through every speed change (KATs on the keyed local oracle: N2 over N8
`3e0852b3…`, N4 full support `49bb344b…`, before and after each of the factorizations, the shared
prototype sums and the per-pair support).

## 2. Data and dumps

- IR dumps `logs/E1/dump` (`logs/E1/dump.sh`; `irdumpa2pp` at HEAD): `ops-*`, `items.json` byte-equal at
  `e464756` and `7537acd` (and to RSV-V2's).
- Node dump `logs/E1/nodedump` (`nodedump4`, `planform4`, `protodump` at `7537acd`; `SHA256SUMS` in
  `logs/E1/nodedump-SHA256SUMS`): `planform_kat.py` KAT PASS; the prover's `plan-kat`: prototypes,
  register forms (≤ 256 terms), programs and kind tables equal, decode 0.40 s (VM). At `7537acd` only
  `node-N*.txt` changed against `e464756` (B4's check rows).

## 3. End-to-end acceptance

### 3.1 The node chain at `7537acd` (`logs/E1/r4/chain.txt`; `node-kat … --prove`, keyed oracle, test signer)

Each output checked by the dumped Lean program (IR, `stmtOk4`, 8,783 asks) and by **the rev44 Lean V**
(`e1verify`: the badge's `parseSigned` + `accF` with `V := FR.Sub4.V4F`, `qV := 36,000`, built at
`7537acd`), its canary (statement's last bit flipped) rejected; every witness relation checked first
(`node::check`: H, chain, links, public cells, L, M rows, link rows incl. B4's: 0 failing).

| node | previous | aggregate | Lean V (timed, after a warm run; VM ms) |
|---|---|---|---|
| N8 | — | 2 × k 1 | accept 300 |
| N2 | N8 | k 1 | accept 343 |
| N4 | N8 | k 2 | accept 368 |
| N4 | N2 | k 2 | accept 406 |
| N2 | N4 | k 1 | accept 367 |
| N2 | N2 | k 2 | accept 345 |
| N4 | N2 | k 4 | accept 357 |
| N4 | N4 | k 3 | accept 334 |
| N4 | N4 | k 1 | accept 382 |
| N8 | — | 2 × k 4 | accept 430 |

Transitions N8→N2, N8→N4, N2→N4, N4→N2, N2→N2, N4→N4; the child claim's support grows to all three
kinds from the third node on. k = 1 and k = 2 (the review's request: the main chain after `aggL k − 1`
carries the phantom constants and no pin conflicts) pass for N2, N4 and N8. The same chain at
`e464756` (before B4) passed the same way (`logs/E1/r2/chain.txt`).

### 3.2 A stream through the service (`logs/E1/st1`, at `e464756`; and the A/B's new stream, §4, at `7537acd`)

`logs/E1/stream.sh` (P2's `probe/p2t13/stream.sh` plus `e1verify` on every output), `prover setup` then
`first`/`step` with the ready/go/done handshake, rf-oracle's real WOTS signatures:

| step | chain(s) | kind | Lean V | canary | native acc |
|---|---|---|---|---|---|
| 1 | 2^20 + 2^20 (**full-length first step**, k 4 + 4) | N8 | accept | reject | accept |
| 2 | 131,072 | N2 | accept | reject | accept |
| 3 | 300,001 (k 2) | N2 | accept | reject | accept |
| 4 | 786,432 (k 3) | N4 | accept | reject | accept |
| 5 | 2^20 (k 4) | N4 | accept | reject | accept |
| 6 | 131,072 | N2 | accept | reject | accept |
| 7 | 600,001 (k 3) | N4 | accept | reject | accept |
| 8 | 262,144 | N2 | accept | reject | accept |

At **`7537acd`** with the asm-linked binary of the final `prover.s` (`logs/E1/st2`, chains 2^20 + 2^20,
786,432, 131,072): step 1 N8 (**full-length first step**, k 4 + 4) accept, step 2 N4 accept, step 3 N2
accept; canaries rejected; native acc the same. The A/B's new stream at `7537acd` (§4, P2's 9-chain
list, 8 steps): 8/8 accepted by the Lean V, 8/8 canaries rejected.

### 3.3 The decoder `nd` (PORT's request; `logs/E1/dkat/dkat.txt`, probe `logs/E1/fr-build/probe/E1Dec.lean`)

`nd = ndK4 (decF04 κ ; outIR4 κ)`. **`decF04` cannot be run**: its proved cost is ≈ 2.7·10^13 units
(`cost_decLevels4`; it re-decodes Ligerito's level 0 from the prover's whole query log). The probe
therefore starts at its **proved postcondition**: memory `memX4` words, the constant cells `kval`
(`Inv`), and the prover's `f` (`node-kat --dkat DIR`: the node's witness cells) at `wAddr κ e` for every
`Dec0 e` (`HeapW`, `decF04_wF`'s conclusion). It runs `outIR4 κ` under `semXIR` (the machine's
semantics) and compares the output words with `witWordsF (.node c₀ c₁ p₀ p₁)` of the node's actual
signed children (`outIR4_sem`'s right side through `witWordsF_eq`):

| node | children | output words | result |
|---|---|---|---|
| N8 | 2 aggregates, k 1 | 608,071 | **EQUAL** |
| N8 | 2 aggregates, k 4 (6 spacer entries) | 2,428,729 | **EQUAL** |
| N4 | previous N2 + aggregate k 4 (3 spacers) | 1,518,394 | **EQUAL** |
| N2 | previous N4 + aggregate k 2 (1 spacer) | 911,508 | **EQUAL** |
| (−) N2, one bit of `f` flipped in the aggregate's stream (element 20) | | | MISMATCH, 2 words (304,061, 523,158) |

So PORT's output stage at 4.4.1's format (spacer entries, the count word, `reassemble4` over 20
fields, the segment offsets at `i·strideB`, `prevIR`) reproduces the children byte for byte from an
honest `f`. Not covered: `decF04` (the chain, the five levels' decode from the log).

## 4. Times

**Method.** The dev VM has no pclmulqdq (portable tier) and 32 loaded cores, so its times are not the
runner's. Both provers ran on the VM on **4 cores** (24–27, the runner's 4 vCPUs): the base (HEAD's
`prover.s` `1b84a5f1…`, P2⁹ with B0's blob, its own `prover setup`) and the new one (the asm-linked
binary of `aac53ced…` or the same code cargo-built, its own setup), and each phase is scaled to the EPYC
7763 by **the base's own ratio** for that phase (base 7763 = P2⁹'s record run 40845544755, same binary,
same chain list). No runner was used (nothing pushed).

**Node proof, phase by phase** (`logs/E1/nab/nab.txt`, `node-kat --prove`, 2 alternating rounds, best;
only E2/E4 changed — commit, Z, Lc, Sh, RS, Ligerito agree within noise):

| node (child claim's support) | base VM e2 / e4 | new VM e2 / e4 | VM/7763 ratio e2 / e4 | **new 7763 e2 + e4** | base 7763 | Δ node |
|---|---|---|---|---|---|---|
| N8 (none) | 1.274 / 5.697 | 1.234 / 4.027 | 5.02 / 7.99 | 0.25 + 0.50 | 0.25 + 0.71 | **−0.22 s** (the own `W_M` from the prototype sums) |
| N2 ← N8 ({N8}) | 0.553 / 2.90 | 1.663 / 4.391 | 5.22 / 8.22 | 0.32 + 0.53 | 0.11 + 0.35 | +0.39 s |
| N2, full support ({N2, N4, N8}) | — | 2.336 / 5.588 | 5.22 / 8.22 | 0.45 + 0.68 | 0.11 + 0.35 | **+0.67 s** |
| N4, full support | 0.931 / 5.077 | 3.435 / 8.413 | 5.01 / 9.15 | 0.69 + 0.92 | 0.19 + 0.56 | **+0.86 s** |

The child claim's support holds all three kinds from the third node of a stream on, so the full-support
rows are the typical step. The node parts used below (P2⁹'s, request − aggregate, plus Δ): **N2 3.58 s,
N4 5.93 s, N8 5.46 s** (P2⁹: 2.91 / 5.07 / 5.68).

**The stream** (`logs/E1/ab2`, both provers, P2's 9-chain list on 4 VM cores; `scale.py` scales each
step's aggregate and node parts by the base's ratios): the aggregates are unchanged (new/base on the VM
0.995, range 0.79–1.26: noise); the per-step node parts agree with the table for N2 (3.30 over N8,
step 2) and N4 (5.62); the N8 step ran under extra load (every unchanged phase +30 %) and is replaced by
the phase table. **Start-up** 0.97 → 1.19 s on the VM (the larger blob/image, three kind tables): ≈ 0.66 s
on the 7763 (P2⁹ 0.53). `prover setup`: 167 s on 12 VM cores (the base's 142 s on 32), 265 MB.

**Projection** (`logs/E1/project.py`: P2⁹'s model at the current rules, M = 96, `stream_s` 1,920,
`step_s` 60; segment fits P2⁹'s; `logs/E1/nab/project-node.txt`):

| | P2⁹ (base) | **E1 (rev44)** |
|---|---|---|
| node parts N2 / N4 / N8 | 2.91 / 5.07 / 5.68 s | **3.58 / 5.93 / 5.46 s** |
| start-up · overhead per step | 0.53 · 1.91 s | 0.66 · 2.04 s |
| steps 2^17 / 2^18 / 2^20 | 5.19 / 7.47 / 23.31 s | **5.86 / 8.14 / 24.17 s** |
| first step 2^18 + 2^18 | 14.80 s | 14.58 s |
| **worst first step 2^20 + 2^20** (k 4 + 4) | 42.16 s | **41.94 s** (step_s 60: 1.43×) |
| mean step + overhead | 11.09 s | **11.92 s** |
| stream at M = 96 (mean / p99 / max of 20,000 draws) | 1,072 / 1,168 / 1,231 s | **1,150 / 1,247 / 1,311 s** of 1,920 (1.67× on the mean) |
| **P̄** | 8.09 s | **8.77 s** |

The reserve (RSV2's E2/E4 child terms) costs ≈ +0.7 s per N2 and +0.9 s per N4 node on the 7763;
nothing else in the step moved measurably. Levers left: the E4 child term's sumcheck support (the
child kinds' M regions land on a larger share of the parent's cells than the own `W`), E2's dense
child table over `2^logM` rows, and the start-up's node data (11.4 MB blob; a binary form of the kind
tables, which A1′ and B4 grew from 12.3 to 26.3 MB of text).

### 4.1 The hard caps (the orchestrator's priority: acceptance and fit, not P̄)

| cap | E1 (7763, projected from the VM A/B) | margin |
|---|---|---|
| `step_s` 60, worst first step (2^20 + 2^20, N8 over two k = 4 aggregates) | 41.9 s | 1.43× |
| `step_s` 60, worst later step (2^20, N4) | 24.2 s | 2.5× |
| `stream_s` 1,920 at M = 96 | mean 1,150 s, max of 20,000 draws 1,311 s | 1.46× on the max |
| `ready_s` 10 | start-up ≈ 0.66 s (VM, 4 cores: 1.19 s) | ≫ |
| `prover setup` (240 s budget on the runner) | 167 s on 12 portable-tier VM cores; P2⁹'s same work took 56–65 s on the 7763 | measure on a runner |
| peak RSS | 7.0 GB (setup), ≤ 7.1 GB per request (VM) | (11 GB) |

## 5. Deviations and findings

1. **B4's cells by a generic rule, not by hand.** `solve_aux` reads the kind table: the cells of
   `AUX_L`'s ranges are solved from the link rows that read them (one linear unknown, or a packing
   row's bits). B4's 2,200 cells per aggregate child need no B4-specific code; IMP's rows (arena ask
   templates, PK-m7 statement rows) need only their range in `AUX_L` if their cells are L cells of the
   same kind, or a second table if they live elsewhere. Cells no row determines stay zero (an inactive
   sub-slot's length inverse: 6 in N8 at k 1).
2. **Register forms of more than 256 terms are dropped** (`mfill::LONG_FORM`); the fill only writes
   single-cell forms, the rest were only checked. The blob's register forms fall 27.7 → 3.2 MB per
   prototype.
3. **The decoder KAT starts at `decF04`'s postcondition** (§3.3).
4. **VM timings are not runner timings**: the dev VM has no pclmulqdq (portable tier), so field-heavy
   phases run ≈ 8–9× slower than on the 7763; §4 scales by the base's own measured ratios. No probe
   branch was pushed (the repository's rule: no pushing unless the user asks).
5. The `node_ops_match_lean` KAT file (`logs/P2/r41p8/nodeops-kat.txt`) predates rev44's layout; the
   node ops are covered instead by the Lean V's acceptance of every node proof.

### 5.1 What is hard-coded (for R1's `fLrEnd` 2,736 B / 108 cells and ASK-P's arena folds)

Table-driven already: the node matrices, the plan form, the link rows (every kind table from the dump;
a new row family needs no code if its cells are filled by `solve_aux` or by the slots' fills), the item
sequence's phase list (`items.rs`), the segment offsets/spacers (from `SEG_B`, `SPACER_B`).

Hard-coded (each a constant with its Lean source named next to it):
- `params.rs`: `FIELD_SIZES` (20 fields), `PI_SIZE`, `LREND_LEN` 1,008, `EEND_LEN` 112, `RSV_RX/RY/S/X`,
  `CAP_LOG`, `STAR_SIB`, `N_ITEMS`, `N_FS_ITEMS`, `CAP_READS`, `CAP_ENTRIES`, `CAP_OFF`.
- `nodeprove.rs`: **`RSV_REL`** (the 60 cells, `FRVerifierC4.rsvRel` literal); `child_claim` takes them in
  order and `prove` splits them as `p_x` 23 ‖ `p_y` 25 ‖ `s` 9 ‖ `X₃` 3 (`rsv[..23]`, `[23..48]`,
  `[48..57]`, `[57]`); `fLrEnd = vl ‖ rsv` assumes `LREND_LEN = 48 + 16·|RSV_REL|`; `fEEnd = vm ‖ m̂* ‖ 0^48`;
  B′ puts the cells at `κ′^{11 + i}`; E1's `η` is coordinate 23. **R1 changes all of these** (a longer
  `RSV_REL`, its split, and whatever the 108 values mean in E2/E4).
- `node.rs`: `SEG_B`, `C_LEN`, `SPACER_B`, `S_BLK`, `WOTS_SLOT`, `WM_SLOT`; the L cell offsets of the
  signature (`299 …`), the bits (`299 + 266 + 399`), the kind selector (`8516`), S-E13b's (`8704`, `8720`,
  `8960`, `11008`), the spacer bits (`11264`); `AUX_L` (B4's `12,288 … 14,487`).
- `nodeops.rs`: `eval_mx`'s point split (23 + 9, `s_k` at `23 + 3k`) and the 25-entry column point.

## 6. What remains

- **IMP's rows** (arena ask templates, PK-m7's statement rows): re-dump, rebuild the blob, run
  `node-kat` and look at `link_rows_bad`; extend `AUX_L` (or add a cell table) for any new auxiliary
  cells; the rows' other cells (stream, arenas = stream elements) are already in the witness.
- A runner measurement (a `probe/` branch) if the orchestrator pushes one: `logs/E1/ab.sh` and
  `logs/E1/stream.sh` are the VM forms of P2's probe.
- Speed: §4's levers.

## 7. Files

Prover (all under `submissions/flock-recursive/prover/`): `params.rs`, `items.rs`, `ligerito.rs`,
`leaf.rs`, `agg.rs`, `ir.rs`, `node.rs`, `nodeprove.rs`, `nodeops.rs`, `sumcheck.rs`, `plan.rs`,
`mfill.rs`, `mle.rs`, `kat.rs`, `main.rs`, `stream.rs`, `nodeblob.b64`, `prover.s`. Docs:
`docs/v4/flock-recursive/stages/E1-RESULT.md`, `E1-JOURNAL.md`. Logs and probes: `logs/E1/` (build tree
`fr-build` with `probe/E1Verify.lean`, `probe/E1Dec.lean`; `dump.sh`, `svc.sh`, `stream.sh`, `ab.sh`,
`scale.py`, `project.py`, `asm/det.sh`, `dkat/run.sh`).
