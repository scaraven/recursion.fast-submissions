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
