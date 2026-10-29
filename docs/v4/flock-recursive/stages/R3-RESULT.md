# R3 (track R-OPS): RESULT — `rsWeight`'s replay at the previous-node slot, and a chain-template library

Stage R3, 2026-10-29. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `616b57c`). Build
tree `logs/fr-build-R3`, a copy of `fr-build-IMP` (HEAD), re-snapshotted, with MINE =
`FRVIRTplChain FRNodeRows4RepRsV FRNodeRows4RepRs FRNodeRows4RepRsK FRNodeRows4RepRsCtrl`. Logs are in
`logs/R3/`. Every lake, lean and probe command ran in the 16G scope under `timeout`. No sub-agents.
Nothing is committed. Journal: `R3-JOURNAL.md`.

## 0. Verdict

The goal changed mid-track. The orchestrator dropped the 10 ms kill line and asked for the simplest
sound binding within the hard caps. That is what was built.

| Item | Result |
|---|---|
| Soundness | **Done and kernel-checked.** `kRS_ok : KOk (implP impl₀ base 0 ι) ι kRS` holds at every index. The replay template computes `rsWeightF4 (nodeAt ι)`, kind factor included, for **any** claim points in `K`. `rtRs_okW` and `rtR3_ok` give `RTOkW` at `repB` through C1's `rtK_okW`. |
| Route | C1's `KOp`/`rtK` with sparse rows. Templates are built with a new generic chain library (`FRVIRTplChain`) because it is the simpler thing to prove. |
| KATs | Honest witness against `rsWeightF4` for N2, N4 and N8, with claim points in `K` and in `F`: all rows hold and the outputs are equal. `growsVal3 = rows3`: PASS (`r3rs-1.log`). |
| Spare-region fit | **Fits.** 472,310 rows and locals, kind-muxed, from cell `repB + 2^16`. With `linkWAll`'s 42,601 that is about 515 k of 1,048,576. |
| Kernel | 0.85 s of type checking over the five modules (`prof-summary.txt`). |
| Axioms and source rule | Axioms ⊆ {propext, Classical.choice, Quot.sound}. 0 findings, 439 files (`axioms.log`, `source-rule.log`). |
| **Plan init (hard cap)** | **Fails.** Building the rows takes **2.93–3.06 s** (template, kmux, `instRow`) plus **0.94 s** of grouping (`grows`), about **3.9 s** best on core 31 (`r3rs-3.log`). That is more than the ≈ 3 s budget for *all* replay templates combined, before C1b's `evalL`/`targetS`. Runs on a contended core were 6–15 s. |
| **V** | **+0.72 s VM** (`growsVal3` best 715 ms, 2.99 M terms at 0.24 µs per term). This is inside verify_s 10 s, but about 5× the "+150 ms is fine" the orchestrator expected. |

**Recommendation.** Plain sparse rows are sound but do not fit the init cap. Even with every cheap
lever the rows stay at about 2.5–3 s of init for this op alone (§4). Two ways forward:

1. **(Recommended) Closed-form evaluation of this same template's uniform parts.** 93 % of its rows
   are chains and per-stage instances (§4.2). The soundness side does not change: the `Ok` proofs do
   not depend on layout, so alignment pads cost no re-proof.
2. Re-budget init for this op (about 3.9 s, ≈ 3 s with lever L2).

## 1. What was built (code lines from the core's `loc.py`; `logs/R3/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRVIRTplChain` | 290 / 187 / 28 | **The chain-template library (generic).** See §1.1. |
| `FRNodeRows4RepRsV` | 146 / 89 / 13 | The template's arithmetic as a value function, `rsRef`, and **`rsWeightF4_ref`**: `rsWeightF4 ν r ps κ β ρ = rsRef ν r ps κ β ρ` when `|r″| = 7`. **`block_frob`**: a block's stage-`k` term is `W₀^(2^k)·G`. Also `kwSL4I_ref` and `claim_ref`. |
| `FRNodeRows4RepRs` | 297 / 216 / 18 | The node-kind template over input forms, **`rsG`**, and **`ok_rsG`** (it computes `rsRef`). Its pieces are `blockG`, `levelG`, `kindG`, `termG` and `claimG`, each with an `ok_` lemma. |
| `FRNodeRows4RepRsK` | 253 / 183 / 15 | `rsShape` (`[af 7, f, f, ak m] ++ ak ns`), the input forms `kIn`/`cIn`, the sub-template **`rsT ν ts`**, and the `KOp` **`kRS`**. **`kRS_ok`**, `cbRS = repB + 2^16`, **`rtRs`** with `rtRs_okW`, **`rtN0R = rtN0.orElse rtRs`**, and **`rtR3 π`** (`rtC1` plus `rsWeight`) with **`rtR3_ok`**. |
| `FRNodeRows4RepRsCtrl` | 58 / 26 / 8 | The controls (§3). |
| **total** | 1,044 / 701 / 82 | |

### 1.1 The library (`FRVIRTplChain`), reusable by C1b and the fold

- **`GM α := ℕ → List Gate × α`**: a gadget builder. Given its first local, it returns its gates and
  its result, which is a set of forms over the template's wires. It has `ret`, `bind` (the second
  part's locals follow the first's) and `map` (post-process, no gate copy).
- **`GM.Ok e g P`**: wherever the gate equations of `g` hold at `e`, from any first local, its result
  satisfies `P`. Its rules are `ok_ret`, `ok_bind`, `ok_map` and `ok_mono`. The list combinators have
  lemmas too: `ok_mapL` for independent instances, `ok_foldL` for a chain through a list, and
  `ok_iterL` for an `n`-step chain that returns every value. **No offset arithmetic appears in any
  proof**, unlike the hand-placed locals of `FRVIRTplRepLW`.
- **Gadgets.**
  - `mulF` is one gate.
  - On `K` as pairs of `F` forms (`KF`, value `evK`): `mulK` (Karatsuba, 3 gates), `sqK` (2 gates)
    and `smulK` (2 gates).
  - Linear, with no gates: `oneK`, `zeroK`, `addK`, `sumK`, `ofFK` and `oneSubK`.
- **Chains**, each with its value lemma:

  | Chain | Computes |
  |---|---|
  | `sqChainF`, `sqChainK` | `x^(2^i)` for `i ≤ n`, as `sqIter` |
  | `powF` | `x^i` |
  | `prodK` | `Π` |
  | `hornerKG` | `KW.hornerK` |
  | `phiG` | `phiTable`'s tree |

- **Performance lesson.** Write `g.bind fun x => ret y` as `g.map`. A trailing `ret` bind copies the
  gate list and recomputes `nlocs` at every level, which is quadratic. On this template it took the
  N4 build from 4.6 s to 0.8–1.1 s (`r3prof-1/2.log`).

### 1.2 The template (per node kind; `rsG`)

`rsWeightF4` branches on data (`f₁ = 0` takes the `F` fast path), and the dump shows real `f₁` cells
on claims 1 and 3. The template therefore computes the **`K`-general** value. Claim 2's kind factor,
`kwSL4I`, computed afresh at each of the 128 stages, would cost about 2,000 `K` products per stage,
which is about 730 k rows per kind. That does not fit.

The template instead uses the fact that `x ↦ x^(2^k)` is a ring map in characteristic 2
(`block_frob`). For each skeleton block, `W₀ = (Σ_{i∈p} β^i)·Π q_b` and `G = Π ρ_b` are computed once,
then `W₀`'s squaring chain. Per stage, a block costs 5 rows.

Rows for N4 (the counts add up to the measured 155,094):

| Part | Rows |
|---|---|
| `phiG` | 247 |
| powers of `β` and `κ` | 12 |
| blocks once (`W₀`, `G`; 125 blocks, 1,899 fixed bits) | 11,019 |
| `W₀` chains | 31,750 |
| claim-coordinate chains (4 × 25 × 127 × 2) | 25,400 |
| `eq` products for claims 1, 3, 4 (128 × 3 × 24 × 3) | 27,648 |
| claim 2 per stage (`eq_hi` 18 + level products 375 + Horner 57 + 3, × 128) | 57,984 |
| `c_k`, `κ^j` (`smulK`) | 1,032 |

| Kind | gates = locals = rows | terms |
|---|---|---|
| N2 (`ρ`, claims `AK24`, 17 block bits, 118 blocks) | 146,837 | 930,099 |
| N4 (`AK25`, 18 bits, 125 blocks) | 155,094 | 982,636 |
| N8 (`AK25`, 18 bits, 146 blocks) | 170,373 | 1,081,211 |
| **kind-muxed (`kTpl kRS`)** | **472,310** | **2,993,982** |

Skeleton sizes are in `logs/R3/skel.log`. The operand sizes come from the RSV2 dump (`mkslots-p0`):
`r″ = r93114 AF7`, `κ = r2262`, `β = r790`, `ρ = r93113 AK25/24/25`, and claims
`r92759 r92810 r92861 r92912` (N4/N8) or `r92784 …` (N2), `AK25/AK24`. `act` is true at every kind.

### 1.3 The theorems

```lean
theorem RsR.rsWeightF4_ref (ν) (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) (hr : r.size = 7) :
    rsWeightF4 ν r ps κ β ρ = rsRef ν r.toList (ps.map Array.toList) κ β ρ.toList
theorem RsR.block_frob (k β q ρ p) : K.ofF ((p.2.map ((sqIter k β) ^ ·)).sum) *
    (p.1.map fun b => KW.ew (fun l => sqIter k (q l)) ρ b.1 b.2).prod = sqIter k (w0V β q p) * gV ρ p
theorem Tpl.ok_rsG (h1 : e.one = 1) (ν) (hr : rI.map (LinT.ev e) = r) (hp : pI.map (List.map (evK e)) = ps)
    (hκ : κI.ev e = κ) (hβ : βI.ev e = β) (hρ : ρI.map (evK e) = ρ) :
    Ok e (rsG ν rI pI κI βI ρI) fun o => evK e o = rsRef ν r ps κ β ρ
theorem N4s.kRS_ok (ι : Kind) : KOk (implP impl₀ base 0 ι) ι kRS
theorem N4s.rtR3_ok (hZ : LinkZero impl₀) (hB : STBase base) (hπ : π ≤ 1) (ι : Kind) :
    RTOkW (implP impl₀ base π ι) (Xof π) (rtR3 π) ι repB
```

`rtR3` replaces `rtC1` wherever the integrator wants `rsWeight` out of prototype 0's imports. That
requires `repOkW_rtR3`, a one-line copy of `repOkW_rtC1`, plus §5's fold.

## 2. Design choices and deviations

1. **The `K`-general template, not the `F` fast path.** Templates are total functions: every `Gate`
   defines a new local, and `KOp.T` sees only operand *types*. So an "`f₁ = 0`" precondition cannot
   be asserted. The claim registers also have real `f₁` cells.
2. **The Frobenius factoring of the kind factor** (`block_frob`). Without it, the kind factor is
   about 730 k rows per kind.
3. **C1's `kTpl` kind mux, unchanged.** This triples the claim part (55 k rows per kind), which is
   lever L2 in §4.
4. **The memo's R3 scope (closed-form MLEs, `Piece.chain`) was not built.** The orchestrator's change
   of goal dropped it. §4 shows the init cap brings it back.

## 3. Controls and KATs

| Definition | (+) | (−) |
|---|---|---|
| `rsShape` | `rsShape_pos`: the node operands parse | `rsShape_neg`: `AF6`, a missing `β`, or an `AF` claim |
| `isRS`, `rsArgs` | `isRS_pos`: all-`act`; operands `r, κ, β, ρ` then the index's claims | `isRS_neg`: `act` false at `P30`; another op |
| `rsT` | (KAT below) | `rsT_neg`: other types give no gates, and `rsIn` is false |
| chain gadgets | `chain_sizes` (2 gates per `K` square, 3 per product, Horner); `sqChain_reads` (step 2 reads step 1's locals) | — |
| `cbRS` | `cbRS_pos`: above `linkWAll`'s locals | — |
| `rsG`/`kRS` (numeric; `probe/R3Rs.lean`, `logs/R3/r3rs-1.log`) | N2, N4, N8 with random `K` claim points and with `F` points (`f₁ = 0`): the honest locals satisfy all rows, and the outputs `= encK (rsWeightF4 ν …)` | a perturbed local fails a row; `rsWeightF4` at a perturbed `ρ₉` (a block coordinate) differs |
| grouped rows | KAT `growsVal3 = rows3` on the 472,310 kind-muxed rows: true | — |

## 4. Measurements and the caps

**Build** (`probe/R3Rs.lean`, `R3Prof.lean`). Core 31, load about 5 of 32, best of 3
(`r3rs-3.log`):

| Step | Time |
|---|---|
| kind-muxed template + `instRow` | 2.93–3.06 s |
| `grows 2048 4096` | 0.94 s |
| `growsVal3` per call (tables included) | best 715 ms, median 792 ms |

On a contended core 30, the same steps took 6.0–7.0 s and 14.8–15.5 s, and `growsVal3` 688 ms
(`r3rs-1/2.log`). Per N4 sub-template: gates 0.8–1.3 s, `Tpl.rows` 0.2–0.4 s, `instRow` 0.4–1.2 s.
C1's `kmuxT` substitution roughly doubles the three sub-templates' cost (`r3prof-3.log`).

### 4.1 Levers inside the sparse route (estimates from the counts above, not built)

| Lever | Rows | Init | V | Lean |
|---|---|---|---|---|
| L1: a direct row generator (no `Tpl` → `kmuxT` → `instRow` passes) | same | −1–2 s | 0 | a generator, plus a proof that it equals `kRows`' rows |
| L2: share the claim part across kinds (input mux, one `K`-general claim block) | −110 k (−23 %) | −0.9 s | −0.17 s | an `rtK` variant whose template sees all blocks and the selectors (≈ `rtK_okW`), a mux gadget, re-stated `ok_rsG` |
| L3: one union skeleton for N2/N4/N8 at 18 bits (exponents muxed by `sel·β^i`) | −80–100 k | −0.7 s | −0.13 s | a padding lemma (`kwS4 ν 18 (q‖0) (ρ‖0) = kwS4 ν 17 q ρ`), a merged-skeleton lemma |

Even with L1–L3 together, this op alone needs about 2–2.5 s of init and about 0.35 s of V.

### 4.2 The closed-form route on this template (recommended next stage)

The `Ok` proofs never mention local numbers, so the template can be re-laid-out with `Gate.pad`
alignment (a `GM.align` gadget with a trivial `ok`) at no cost to soundness. With aligned layout:

| Part | Share | Structure | V |
|---|---|---|---|
| all chains (claim coordinates: 100 per kind; `W₀`: 118–146 per kind) | ≈ 37 % | power-of-two stride gadget instances, reading the previous instance | O(log) per chain group, a few hundred products |
| per-stage instances (`eq` products, level products, Horner) | ≈ 56 % | uniform over `k ∈ [0,128)`; `ρ` and `G_p` read as broadcast factors (`Σ_k eq(τ_k, k) × eq(u, cell)`) | O(log) per instance class, plus ≈ 25 + 125 broadcast terms per kind |
| blocks once (11–13 k rows per kind) | ≈ 7 % | irregular (fixed bits differ per block) | ≈ 70 k terms per kind, ≈ 50 ms V and ≈ 0.3 s init over 3 kinds; a fixed-bit trie would shrink it |

- **Lean work.** A box-piece MLE lemma (eq factorizes over disjoint bit fields; diagonal and
  shifted-diagonal range sums), a structured-piece description emitted by the aligned builder with
  its expansion `= rows3`, and a `Piece` in `FRNodeRows4Plan` (others' module).
- **Expected outcome (estimate).** V of a few ms plus about 50 ms of sparse once-rows. Init well
  under 1 s.

## 5. Edits for other tracks' files (not made here)

1. `FR.lean`: add `import FRNodeRows4RepRsCtrl`, which pulls in the other four modules.
2. The fold (integrator): `rtC1` → `rtR3` in `FRNodeRows4RepW` (`repOkW_rtR3` is `repOkW_rtC1`'s proof
   with `rtR3_ok`), and `repIRowsW rtR3`. **This is blocked on the init cap (§4)**: C1's `repRowsP`
   trail is 131 s, and this template's rows alone take ≈ 3.9 s.
3. E1 (prover): the honest witness is the gate evaluation in order. `probe/R3Rs.lean`'s `honest` is
   that evaluation for 472 k locals in the spare region, from cell `κ.vslots·2^20 + 2^16`.

## 6. Open questions

1. Is the init budget firm (≈ 3 s for all replay templates)? If yes, rsWeight needs §4.2's closed
   form. Sparse rows cannot get there (≥ 2 s for this op alone, with every lever).
2. Should C1b build its `evalL`/`targetS` templates with `FRVIRTplChain`? It is generic. The
   `map`-instead-of-`ret` rule matters for build time. An aligned layout from the start would make
   §4.2's closed form apply to them too.

## 7. Logs and probes (`logs/R3/`; probes in `logs/fr-build-R3/probe/`)

| File | What |
|---|---|
| `skel.log` (`R3Skel.lean`) | skeleton sizes per kind |
| `r3rs-1.log`, `r3rs-2.log`, `r3rs-3.log` (`R3Rs.lean`) | counts, the honest-witness KATs, build time, grouping, `growsVal3`, `growsVal3 = rows3` |
| `r3prof-1/2/3.log` (`R3Prof.lean`) | the build-time breakdown, before and after `GM.map` |
| `axioms.log` (`ax/AxR3.lean`), `source-rule.log`, `loc.txt` | hygiene |
| `prof-summary.txt`, `profile-*.log` | CPU-s and kernel time per module (one core, `-DElab.async=false --profile`) |

**CPU-s per module** (user + system, including about 4 s of import, load about 5):

| Module | user + sys (s) | type checking | tactics |
|---|---|---|---|
| `FRVIRTplChain` | 5.62 + 2.86 | 0.18 s | 0.48 s |
| `FRNodeRows4RepRsV` | 5.65 + 3.03 | 0.15 s | 1.06 s |
| `FRNodeRows4RepRs` | 6.06 + 3.86 | 0.18 s | 0.79 s |
| `FRNodeRows4RepRsK` | 6.61 + 3.32 | 0.33 s | 1.48 s |
| `FRNodeRows4RepRsCtrl` | 3.97 + 2.92 | 0.02 s | 0.01 s |
| **kernel in all** | | **0.85 s** | |
