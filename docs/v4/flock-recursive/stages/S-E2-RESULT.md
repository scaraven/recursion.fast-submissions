# S-E2 (track L-circ, second half): RESULT

Stage S-E, second half: the node circuit's compiler, mux, WOTS/`hashStmt` and layout, for
`submissions/flock-recursive`. 2026-10-27, branch `v4/flock-recursive` (uncommitted, on `f411b1e`),
against BLUEPRINT **revision 3.5**. Build tree `logs/fr-build-circ` (`snap.sh`: HEAD's versions
of other tracks' modules, since S-0's fix pass is editing `FRTranscriptDefs`/`FRFormat`/`FRVIR`/
`FRVIRSpec` in the working tree). Logs under `logs/S-E2/`. Journal: `S-E2-JOURNAL.md`.

**Status.** Done: (1) `compile_sound` (**FR-R3′ kill test passes: 782 code lines ≤ 1,000**),
(2) `compile_mux_sound`, (3) `wots_sound`, `hashStmt_sound` (with finding F-1), (4) `nodeLayout`
and its checks (closed form, deviation D-2). **Not done:** (5) `node_sound` / `node_complete`
(`FRNodeCircuit`), `FRVIREval` (`evalM_eq`, `evalL_eq`, `impl ⊨ OpSpec`), the VM measurement
(FR-R4′). See §6.

## 1. What was built

Code lines by `.contract/scripts/loc.py` (`logs/S-E2/loc.txt`):

| Module | code (total) | Budget (§7) | Content |
|---|---|---|---|
| `FRVIRCompile` | 782 (1,006) | 1,200 | rows over linear forms of M's cells; slots (`Ty` + one form per F component, `encV`); `opOut` per op, `compile`; `opOut_sound`, `compileFrom_sound`, **`compile_sound`** |
| `FRVIRMux` | 69 (133) | 600 | `muxP`, `compileMux`, `OneHotRows`, `oneHot_of_rows`, **`compile_mux_sound`**, `semIR_mux_eq`, controls |
| `FRWots` | 100 (165) | 700 | `wots_chain_sound`, `sigRoot_bits`, **`wots_sound`**, `w43_step`, `path_node`, **`hashStmt_sound`**, `hashStmt_ungated_vacuous` |
| `FRNodeLayout` | 77 (161) | 400 | `nodeLayout` (82 kind intervals), `Ind`, `Sel`, `kindIvs`, the checks, `mRowModel` |
| **total** | **1,028** (1,465) | | |

### Main statements (all **kernel**; axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, `logs/S-E2/axioms.log`)

- **`Circ.compile_sound`**: for selector forms one-hot at `κ` (`SelOk`, with `one` = 1), if
  `exec impl κ inp ops St.init tr = some (s, tr')`, every row of `compile P base ops` holds at `w`,
  every **import** register's cells hold its value and every **foreign** assertion's flag holds
  (on the register prefix at that op), then `s.ok = true` and every tracked register's cells hold
  its value (`RepS`). Arithmetic ops with rows (A.8 costs): `const` (selector-linear, 0), `mulF`
  1, `addF` 0, `mulK` 3, `addK` 0, `mulKF` 2, `invF` 3 (`inv(1−sel) = 0` included), `packF`,
  `packK`, `getF`, `getK` 0, `eqTable` `2^v − 1`, `keep`/`selectHalf` 1 per component (alias when
  the activity is kind-independent), `splitDigest` 0, `assertEq`/`assertZero` 1 per component
  (gated product; type mismatch ⇒ the gate must be 0), `assertOneHot` 3 + 1, `assertBit`, `accept`.
- **`Circ.compile_mux_sound`**: selector cells one-hot at `κ` and `hdr`'s kind byte `κ.byte` ⇒
  `semIR impl ⟨.mux, ops⟩ inp tr = some true` (plus the register representation).
  **`oneHot_of_rows`**: Boolean selector cells with the three product rows and the linear row are
  one-hot.
- **`Wots.wots_chain_sound`**, **`Wots.wots_sound`** (→ the contract's `SigOk vk m σ`),
  **`Wots.w43_step`** (→ `wotsStep`), **`Wots.path_node`** (→ `sigNode`),
  **`Wots.hashStmt_sound`** (A → `leafStmt h n`; B1–B2 → `nodeStmt c₁ c₂`).
- **`Layout.nodeLayout_chained`**, `nodeLayout_end`, `regions_fit` (`hEnd = 45,966 ≤ 46,336`,
  L before M, `Mbase + 16,384 = 2^16`), `usedBlocks_le`, `mRows_le` (per slot `529,201 ≤ 2^20`,
  per node `≤ 2^21`).

## 2. Build and kernel times

Sequential elaboration (`lean -DElab.async=false --profile`, one process, under the 12 GB scope),
`logs/S-E2/profile-*.log` (**measured**, this VM, not the 4-vCPU runner):

| Module | wall (incl. imports) | tactic exec | type checking | peak RSS |
|---|---|---|---|---|
| `FRVIRCompile` | 58.2 s | 5.6 s (simp 5.3 s) | 0.95 s | 2.7 GB |
| `FRVIRMux` | 10.3 s | 2.2 s (`decide` controls) | 1.37 s | 2.7 GB |
| `FRWots` | 7.6 s | 0.2 s (simp 1.6 s) | 0.10 s | 1.9 GB |
| `FRNodeLayout` | 6.6 s | 0.26 s | 0.19 s | 2.6 GB |

## 3. Controls

| Control | Kind | Shows |
|---|---|---|
| `three_hot_sum` / `three_hot_fails` | neg. | the selector `(1,1,1)` passes `Σ s = 1` (char 2) but fails the product rows: no kind fixed |
| `hotN_rows`, `hotN_selOk` | pos. | a one-hot selector satisfies the rows and is `SelOk` |
| `kindProg_rows_N` / `kindProg_rows_L` | pos./neg. | the mux rows of a kind-dependent constant hold under the right kind's selector and **fail under a wrong child kind's** |
| `hashStmt_ungated_vacuous` | neg. | the ungated `stmt` wiring is unsatisfiable (F-1) |
| `ind_controls`, `ind_controls_neg`, `chained_neg` | pos./neg. | `Ind`/`Sel` on chosen blocks; `WM` and L have no kind; an overlapping layout fails the order check |

Every load-bearing definition has a non-vacuity witness: `SelOk` (`fixedP_ok`, `hotN_selOk`),
`Row.Holds`/`compile` (`kindProg_rows_N`), `OneHotRows` (`hotN_rows`), `nodeLayout`
(`nodeLayout_chained`). `compile_sound`'s hypotheses are satisfiable for the toy program (`kindProg`
has no imports or foreign ops).

## 4. Deviations

- **D-1** (build): against HEAD's S-0 modules (`snap.sh`), not the working tree; re-run once S-0's
  fix pass lands (new ops `eqPt`, `rowW`, `shiftEq`, `linkW` fall into `opOut`'s default branch:
  untracked and foreign, so the proofs stay valid; they should become imports).
- **D-2** (B-2's kill test): the blueprint's "`decide` over `rows (compileMux (gen Mux))`" is
  replaced by **closed-form checks** over the layout constants and §4.3's row model
  (`mRowModel`), after an uncapped `#eval` of the compiler over the 61,753-op skeleton caused the
  16:37 OOM (journal). The link `compile`'s count = `mRowModel` needs `gen fin` and per-phase
  count lemmas (open, §6).
- **D-3** (`compile_sound`'s interface): ops the compiler does not arithmetise are **imports**
  (their cells' values a hypothesis: trace cells, irregular entries, L bits, the `FRVIREval`
  templates) or **untracked**; an assertion on an untracked operand (bytes: `stmtOk`'s tag/`enc64`/
  zero checks, `finalOps`' and `uniTail`'s padding) is **foreign** (its flag a hypothesis). Not
  yet arithmetised: `eqTableK`, `dotKF`, `packFK` (kind-dependent lengths), `kindInd`, `maskRows`.
- **D-4**: `hashStmt_sound` states the leaf and node halves with separate message hypotheses (F-1).
- **D-5**: M's constant `1` is `Params.one` with `one.ev w = 1` assumed (F-4).

## 5. Findings for the blueprint (proposed smallest changes)

- **F-1 (major, completeness/vacuity)**: §4.2's 8 `stmt` element equalities are ungated, but block
  A pins `tagLeaf` and B1 `tagNode` at byte 0 (and A pins bytes 41–63 to zero, where a node's `c₂`
  lies), so every slot's rows are unsatisfiable and the displayed `hashStmt_sound` is vacuous
  (`hashStmt_ungated_vacuous`). Change: gate A's four equalities by `s_L + s_P` and B1's, B2's by
  `s_N` (8 product rows instead of linear).
- **F-2 (major, completeness)**: §4.2 "the end `e_i = h_out(w_{i,3})` (copies)" is wrong for digit
  `3` (then `e_i = ots_i`). Change: `e_i = sel_{i,3}·h_out(w_{i,3}) + (1 − sel_{i,3})·ots_i`, with
  the three selectors per chain `[d<1]`, `[d<2]`, `[d<3]` (A.7's 399 = 133 × 3, as
  `wots_chain_sound`), and state the rows tying them to the digit bits `(b₀, b₁)`: `[d<1] =
  (1−b₀)(1−b₁)`, `[d<2] = 1 − b₁`, `[d<3] = 1 − b₀b₁` (2 products per chain, 266 per slot; not in
  §4.3's count).
- **F-3 (minor)**: §4.3's categories sum to **529,201** per slot, not 526,076; the node total
  1,062,628 is not twice either. Margins still hold (1.98× per slot half).
- **F-4 (minor)**: nothing pins M's `one` cell; proposal: a point claim `f[Mbase] = 1` batched with
  `PubCells`.

## 6. Open (not done in this stage)

1. **`FRNodeCircuit.node_sound`/`node_complete`**: not started. Needs `gen fin` (S-0), `PubCells`,
   `ShHolds` with the link families, `FR.readSigned`, and the glue: one-hot rows → `SelOk`
   (`oneHot_of_rows`) → `compile_mux_sound`; the imports discharged by the trace cells (pack map)
   and the `FRVIREval` templates; the foreign flags by the H blocks' pins / point claims;
   `wots_sound` fed by `w43_step`/`path_node` and the link families; the key leaf by
   `FRBlockStream.stream_sound`.
2. **`FRVIREval`** (`impl`, `evalM_eq`, `evalL_eq`, `impl ⊨ OpSpec`): not started.
3. The M-row count of `compileMux (gen fin)` as closed-form per-phase lemmas (D-2).
4. FR-R4′'s VM build/kernel measurement for the whole entry.
5. The A.6 dump KAT (S-E1's `kindRows` exists; the prover's side is P2's).

## 7. Revision 3.6 pass (on `109761a`, against BLUEPRINT `58c3834`)

Built against S-0's **working-tree** `FRTranscriptDefs`/`FRFormat`/`FRVIR` (they build now; they
define `eqPt`, `rowW`, `shiftEq`, `linkW`): `WT="FRTranscriptDefs FRFormat FRVIR"
logs/fr-build-circ/snap.sh`. All builds under the 16 GB scope. Source rule: 0 findings. Axioms:
⊆ {`propext`, `Classical.choice`, `Quot.sound`} (`logs/S-E2/axioms.log`).

| Change (§10, changes 4) | Where | State |
|---|---|---|
| `eqPt`, `shiftEq`, `linkW` imports of type F, `rowW` of type `AF 2^14` | `FRVIRCompile.opOut` | done; `compile_sound` unchanged (kernel) |
| gated `stmt` rows; `hashStmt_sound` restated (gates as hypotheses, kind-conditional conclusions; `node` = `s_N`) | `FRWots.hashStmt_sound` | done (kernel); the gating's arithmetic is `compile`'s gated `assertEq` |
| selectors `[d<1]`, `[d<2]`, `[d<3]` from the digit bits by 2 product rows | `FRWots.digitSel_sound` (+ `digitSel_neg`) | done (kernel) |
| `e_i` muxed by `sel_{i,3}` | `FRWots.wots_chain_sound`'s `hend` (already the muxed form) | done |
| `f[Mbase] = 1` | `FRNodeLayout.oneCell = Mbase · 128` (`Params.one`) | constant done; the `PubCells` clause belongs to `node_sound` (pending) |
| row model | `FRNodeLayout.mRowModel` (+ mirror mux 2,600, selector rows 266) | `mRows_le`: 532,067 per slot ≤ `2^20` |

**F-3′ (minor, still open):** §4.3 (revision 3.6) states 531,588 per slot. Its listed numbers sum
to 532,151, or 532,143 with the 8 `stmt` equalities counted once (they are listed twice, under the
lincheck and as "gated `stmt` equalities"). `evalM`'s stated 210,570 is not its formula
`2 × 74,587 + 2 × 22,468 + 2^14 = 210,494`. `mRowModel` uses the formula and counts the
equalities once: 532,067, margin 1.97×.

### `FRVIREval` (new, 57 code lines; 7.2 s wall, sequential)

L-circ's share of `impl ⊨ OpSpec` (S-0-m2's owner table), spec and implementation proved equal:

- `walkA_eq`, `walkB_eq`: `walkAB` at row weights `rowW` and column weights `colW` is `Σ_k
  rowW[k]·(A₀ colW)_k` (resp. `B₀`), for all arrays (S-E1's `walk_eq_sum`);
- `kindInd_eq`: `kindIndImpl` (prefix sums over `Layout.kindIvs`) equals `kindIndSpec` (the
  indicator MLEs `Σ_t eq(r′,t) Ind_κ(t)` over `2^16` blocks), via `ind_mle_eq` (single-`eq` form
  of S-C's `selWeight_eq`) and `kindIvs_le` (from `nodeLayout_chained`, with no evaluation).

**Not done:** `evalM_eq`, `evalL_eq`. The M and L matrices are `compileMux (gen fin)`'s rows, so
they need S-0's `gen fin`. The whole `OpImpl.Meets impl spec` also needs the other owners'
fields (S-C, `FRPubTarget`). `node_sound` waits for S-0, as instructed.

Line counts (`logs/S-E2/loc.txt`): `FRVIRCompile` 784, `FRVIRMux` 69, `FRWots` 114,
`FRNodeLayout` 80, `FRVIREval` 57; **total 1,104 code lines**.

## 8. After S-0's fix pass (HEAD `afc2928`, BLUEPRINT revision 3.7)

Built against HEAD (`logs/fr-build-circ/snap.sh` copies HEAD's other-track modules; S-0 has
nothing in progress in the working tree). 16 GB scope. Source rule: 0 findings. Axioms ⊆
{`propext`, `Classical.choice`, `Quot.sound`} for all 15 audited statements
(`logs/S-E2/axioms.log`).

### New and changed

- **`FRVIREval`** (129 code lines):
  - `sparse_eq`: a sparse matrix's MLE `Σ_{x,y} eq(τ,x) eq(σ,y) M[x][y]` over the cube equals the
    sum over its entries of `coef · eq(τ, row) · eq(σ, cell)` (entries outside the cube drop out);
  - **`evalM_eq`**: `evalMImpl fin` (the sparse sum over the A/B/C entries of `nodeRows fin`)
    equals the MLE of the node's M matrices. `nodeRows fin` is both slots'
    `compileMux (gen fin .mux)` rows, with selector cells in L (`selCells`, A.7 offset 8,383) and
    fresh cells from `slotBase σ = oneCell + 1 + σ·2^20`;
  - **`evalL_eq`**: the same for a row list `lRows` (L's Lr rows; A.7 describes them but no
    module fixes them);
  - `walkA_eq`, `walkB_eq`, `kindInd_eq` (§7).

  The implementation costs one product per entry. The blueprint's templated evaluation
  (`tpl_mle`, `shift_mle`, `irregular_mle`, `O(templates)`) is **not** done (deviation D-6). As
  stated, `evalM` costs the replay's row count. That count is already §4.3's "evalM replay"
  budget for the child's irregular entries. For the node's own M matrices it is the whole M row
  count, about 2^20 products. This exceeds §3.1's verifier estimate, so the templates are needed
  for `T_V` (open).
- **`PubCells`** (`FRNodeCircuit`): `w Layout.oneCell = 1`, the point claim `f[Mbase] = 1`. The
  `vk` and `cᵢ` cells enter as the slots' `input` imports.
- **`node_m_sound`** (`FRNodeCircuit`), with `slot_sound`: if `PubCells` holds and both slots
  satisfy `SlotHolds`, both children's **mux** programs accept: `semIR impl (gen fin .mux) inpᵢ
  trᵢ = some true`. `SlotHolds` contains:
  - the selector cells are bits and satisfy the one-hot rows;
  - every compiled row holds;
  - at the kind the selector picks: `hdr`'s kind byte is that kind's, the run uses its trace up,
    the imports' cells hold their values and the foreign flags hold.

  The statement is over `fin` with no hypotheses on S-F's or S-G's fields: whatever they contain,
  the compiled rows check `gen fin` as it stands.
- **`FRNodeLayout`** (revision 3.7): `chainN = 22,472`, `hEnd = 45,974`, and `mRowModel` with
  imports 74,461, `evalM` `2·74,461 + 2·22,472 + 2^14`, gated asserts `2·431 + 2·871 + 600`, and
  selector and kind rows 4. **F-3″ (minor): §4.3 states 531,618; its listed numbers sum to
  531,610** (`mRowModel_sum`). `mRows_le` holds (1.97×).

### Not done

1. **`node_sound` over the packed witness `z`** (`Holds blockR1CS_E` on the used blocks,
   `ShHolds` with the link families, `LrHolds`, `EHolds`, `readSigned`, conclusion
   `accWith V …`). It needs S-F's `V`/`accWith`. The H side of the assembly is also missing:
   discharging `SlotHolds`' imports from the trace cells (the pack map) and the foreign flags from
   the H blocks' pins and point claims.
2. **`node_complete`/`nodeWitness`**: not started.
3. The templated `evalM`/`evalL` (D-6), and the definition of L's row list.
4. Linking `compile`'s actual row count to `mRowModel` (D-2).

### FR-R4′: build and kernel time of S-E2's modules

**Measured** on this VM, sequential (`lean -DElab.async=false --profile`, one process each, 16 GB
scope), `logs/S-E2/profile-*.log`, `logs/S-E2/r4.txt`:

| Module | wall | import | elaboration | tactic exec. | type checking (kernel) |
|---|---|---|---|---|---|
| `FRVIRCompile` | 24.6 s | 3.5 s | 0.86 s | 5.99 s | 1.00 s |
| `FRVIRMux` | 10.3 s | 3.4 s | 0.20 s | 2.34 s | 1.42 s |
| `FRWots` | 7.7 s | 2.5 s | 0.13 s | 0.20 s | 0.10 s |
| `FRNodeLayout` | 6.7 s | 3.4 s | 0.10 s | 0.25 s | 0.20 s |
| `FRVIREval` | 8.2 s | 3.5 s | 0.14 s | 0.39 s | 0.10 s |
| `FRNodeCircuit` | 5.8 s | 3.5 s | 0.03 s | 0.03 s | 0.02 s |
| **total** | **63.3 s** | | | | **2.84 s** |

Peak RSS is 2.7 GB or less per module. The only noticeable kernel cost is the `decide` controls
in `FRVIRMux`. Code lines: 1,217 in total (`logs/S-E2/loc.txt`).

## 9. Revisions 3.8–3.9 and `node_sound` (HEAD `757dfa8`)

### Build blockers in HEAD (not S-E2's; reported)

- **B-1:** `FR.toF_f` is declared in both `FRVIRSpec` (S-0, line 260) and `FRVIRFinalsSF` (S-F,
  line 166). Any module importing both fails, including `FRVerifier`. In the private tree
  `logs/fr-build-circ/src/` I commented out S-F's copy (after `snap.sh`); the entry file is
  unchanged.
- **B-2:** `FR.eW` is declared in both `FRSpartan` (S-C) and `FRVIRFinalsSF` (S-F), so no module
  can import both, and `FR.lean`, which imports all modules, cannot build. To work around it, the
  slots' compiled programs (`selCells`, `slotBase`, `slotCS`, `nodeRows`) moved from `FRVIREval`
  to `FRNodeLayout`, so `FRNodeCircuit` imports `FRVerifier` without `FRSpartan`.

### Compiler and layout (revision 3.8.2/3.9)

- `opOut` follows the 3.8 op set:
  - `selWeight` and `targetMLE` are removed;
  - `lagrangeS` is an import of two F registers, `targetS` an import of `AF 64`, `eqZ` an import
    of F;
  - `Op.nOut` gives `lagrangeS` 2 results.

  `FRVIRCompile` is now 786 code lines, so **FR-R3′ still passes**. 3.9's `rsWeight` and `phiRS`
  are not in HEAD's `FRVIR` yet. Until S-0 adds them they fall into the default branch (untracked
  and foreign, still sound). When S-0 removes `mbp`, its line in `opOut` must go.
- `FRNodeLayout`:
  - the kind `free` covers `[wmBase, 2^16)` (`WM`, the spares, L and M; `Sel ≡ 1`);
  - `nodeLayout_end` now ends at `2^16`;
  - `ind_controls_free` replaces the old negative control;
  - `chainN = 22,465`, `hEnd = 45,960`;
  - `mRowModel` follows revision 3.9 (`Φ` 69,632, Z's Lagrange weights 4,032, `rsWeight` 12,800,
    the `free` kind's 16,384): **618,664 per slot**, `mRows_le` holds at 1.69×.
  - **F-3″ persists:** the stated 1,237,344 per node is 16 above twice the listed numbers, i.e.
    the 8 `stmt` equalities are still counted twice.

### `node_sound` (`FRNodeCircuit`)

- **`PubCells w vk c₁ c₂ pad`** (A.7, revision 3.9): the nine public cells in order map to
  `1`, `vk`'s, `c₁`'s, `vk`'s and `c₂`'s F halves, then six zeros. The order is `oneCell`, then
  the seed payload cells (`seedCell σ e = (σ·chainN + ⌊(1+e)/4⌋)·128 + 4 + (1+e) mod 4`), then the
  padding cells `pad`, which are a parameter. `PubCells.one` extracts the `one` cell; the control
  `pubCells_nodup` shows the nine cells are distinct.
- **`child_sound`**: a SNARK child (`kindOf p.π = .snark k`) satisfies `accV impl fin vk c p = true`
  given:
  - its format facts: proof size ≤ `proofCap`, trace length ≤ `qV`, query sizes ≤ `queryCap`;
  - `SigOk vk (traceDigest p.tr) p.σ`, which is `wots_sound`'s conclusion;
  - `w oneCell = 1` and the slot's `SlotHolds`.

  The route is S-F's `V_snark`, then `runSeq_runIR`, then `gen_fixed_eq` (the fixed-kind and mux
  programs have the same op list), then `semIR_mux_eq` (the kind byte, read off `kindOf` by
  `byte_of_kindOf`), then `slot_sound`.
- **`node_sound`**: under one `PubCells`, both SNARK children are accepted:
  `accV … c₁ p₁ = true ∧ accV … c₂ p₂ = true`.

All audited statements use at most `propext`, `Classical.choice` and `Quot.sound`
(`logs/S-E2/axioms.log`); source rule: 0 findings.

### Still open

1. **The H-side assembly is not done**, so `SlotHolds`' imports and foreign flags, `SigOk` and
   the format facts remain hypotheses of `node_sound`. Each needs its own route:
   - the imports from the trace cells (pack map, `irregular_mle`);
   - the foreign byte checks from the H blocks' pins and point claims;
   - `SigOk` from `w43_step`, `path_node`, the key-leaf stream and the link families;
   - the format facts from `FRFormat`/`items`.
2. W-kind children are not covered (`V_W`).
3. `node_complete`/`nodeWitness`: not started.

### FR-R4′ (measured, sequential, 16 GB scope, `logs/S-E2/profile-*.log`)

| Module | wall | tactic exec. | kernel |
|---|---|---|---|
| `FRVIRCompile` | 27.1 s | 6.79 s | 1.12 s |
| `FRVIRMux` | 10.3 s (§8) | 2.34 s | 1.42 s |
| `FRWots` | 7.7 s (§8) | 0.20 s | 0.10 s |
| `FRNodeLayout` | 7.6 s | 0.28 s | 0.23 s |
| `FRVIREval` | 8.3 s | 0.37 s | 0.10 s |
| `FRNodeCircuit` | 6.8 s | 0.09 s | 0.05 s |
| **total** | **67.8 s** | | **3.0 s** |

Code lines: **1,272** (`logs/S-E2/loc.txt`).

## 10. Unblocking S-F2 and P2 (HEAD `d37a009`)

1. **`compile` is linear.** `CS.add` used to append to the rows, imports and foreign lists, which
   was quadratic. It now prepends: `rows := o.rows.reverseAux cs.rows`, imports prepended,
   foreign entries consed. `CS.rowList := rows.reverse` gives the rows in program order, and
   `nodeRows` uses it. The proofs (`compileFrom_mono`, `compileFrom_sound`) are adjusted;
   `compile_sound` is unchanged. `FRVIRCompile` is 794 code lines, so **FR-R3′ still passes**.
   **Measured:** the compiled dump tool builds both slots' rows of `compileMux (gen fins .mux)`
   and writes them out in **66 s wall, 145 MB RSS** (`logs/S-E2/nodedump-run.log`).
2. **Templated `evalM`/`evalMK`/`evalL` (D-6): not done.** The obstacle is that `compile`
   allocates cells and rows sequentially per op, not in §4.4's power-of-two-aligned templates. A
   templated MLE first needs the compiler to emit A.7's template layout, with each phase's
   repeated op block at an aligned base and its rows indexed `tplBase + inst·2^a + j`. Then each
   template's MLE is `eq(prefix) · Σ_inst eq(inst) · (inner)`. That is a redesign of the
   compiler's allocation, plus per-template lemmas equating the templated sum to `matMLE`
   (`sparse_eq` is the base case). For S-F2, `FR.Eval.evalRows a b rows τ σ` (sparse, proved
   equal to the MLE by `evalRows_eq`) is the callable implementation today.
3. **L's row list (done).** `FRNodeLayout.lBitCells σ` lists slot σ's declared bit-elements in
   A.7's order after `sig`: digits 133, step selectors 399, position bits 7,552, kind selector 3.
   `lRows` holds the rows `b·(one − b) = 0` for both slots (`lRows_length = 16,174 ≤ 2^15`).
   `lRows_sound` shows the rows make those cells bits. `selCells_mem` shows the selector cells
   are among them. `evalL_eq` applies with `lRows`.
   **Finding F-5 (minor):** A.7 says "digits 133 as bit-elements", but a base-4 digit is two bits
   (266 bit-elements, or 256 + checksum by revision 3.5's text). `lBitCells` follows A.7's
   literal 133, consistent with `selCells`' offset 8,383. The blueprint should fix the count.
4. **Dumps for P2** (`probe/fr-nodedump/`, compiled, outside the entry; built against the private
   HEAD view `logs/fr-build-circ/src`; output `logs/S-E2/nodedump/`):
   - (a) `mrows-σ.txt`: each slot's M rows in program order, `row | A | B | C` with `cell:coef`
     (F little-endian hex). `mregs-σ.txt`: register → import flag, type, and one linear form
     per F component (the register/import → M-cell map).
   - (b) `lrows.txt`: L's rows and the bit-cell ranges.
   - (c) `layout.txt`: `nodeLayout`'s 83 intervals for the 9 kinds, including `free` over
     `[wmBase, 2^16)` (WM is its first 20 blocks), plus `oneCell`, `Mbase`, `Lbase`, `wmBase`.
   - (d) **The link families' slot maps: not dumped.** They live in S-0's/S-C's `linkW`/`slotW`
     implementations (the op takes a family id); I did not find a slot-map table to export.

   **Measured counts and finding F-6 (major, for the row model and P2):** the compiled program
   has **68,795 rows and 114,378 cells per slot, 27,691 import registers and 173 foreign
   assertions** (`nodedump-run.log`). This is far below `mRowModel`'s 618,664 because the
   compiler emits rows only for the arithmetic ops. The structured ops are **imports** whose rows
   belong to their replay templates, which no module emits yet: `lagrangeS`, `walkA/B`,
   `evalM/L`, `tensorW`, `rsWeight`/`phiRS`, `dotKF`, `eqTableK`, `kindFoldWeight`, `slotW`,
   `linkW`, the Merkle node and column imports, and the folds. So **the dump is the arithmetic
   skeleton plus the import map; the replay templates' rows are still to be emitted.** That is
   item 2's work.
5. **The H-side assembly of `node_sound`: not done.**

`FR.toF_f` (S-0/S-F) still clashes at HEAD; the private build tree patches S-F's copy. `FR.eW`
(S-C/S-F) also still clashes and is avoided (§9). Source rule: 0 findings. All builds and the dump
ran under the 16 GB scope.
