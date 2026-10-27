# S-E2 (track L-circ, second half): JOURNAL

Branch `v4/flock-recursive`, BLUEPRINT revision 3.5 (`f411b1e`). Build tree `logs/fr-build-circ`
(L-circ's tree). S-0's fix pass is editing `FRTranscriptDefs`/`FRFormat`/`FRVIR`/`FRVIRSpec` in the
working tree (mid-edit, `FRTranscriptDefs` did not build), so `logs/fr-build-circ/snap.sh` builds
against **HEAD's** versions of every other track's module (copied into `logs/fr-build-circ/src/`)
with S-E2's own modules symlinked in. Re-run `snap.sh` once S-0 lands.

## 2026-10-27

### (1) `FRVIRCompile` + `compile_sound` — FR-R3′ kill test: **PASS**

- `compile_sound` (kernel; axioms `propext`, `Classical.choice`, `Quot.sound`;
  `logs/S-E2/Axioms.lean`): **781 code lines** for the whole module (1,004 total, `loc.py`), against
  the 1,000-line kill test. It covers every arithmetic op of A.8 except `eqTableK`, `dotKF`, `packFK`
  (imports / untracked for now; see below), with `keep`, `selectHalf`, `splitDigest`, `eqTable`,
  `assertEq`/`assertZero` (gated), `assertOneHot`.
- Design: rows `⟨a,w⟩·⟨b,w⟩ = ⟨c,w⟩` over linear forms of M's cells; a register's **slot** is a
  static type and one linear form per F component (`encV`: F 1, K 2, digest 2 = `splitDigest`'s
  halves, arrays per element), or untracked. Non-arithmetic ops are **imports** (fresh typed
  cells; their values a hypothesis — discharged later by the trace cells / templates) or
  **untracked** (bytes, naturals); an assertion over an untracked operand is **foreign** (its flag a
  hypothesis, on the register prefix at that point). Kind-dependent data are selector-linear with
  selector forms `Params.sel`; `compile_sound` is proved once for any selector forms one-hot at the
  run's kind (`SelOk`), so the fixed kind (constant forms) and the mux (three cells) are the same
  theorem: this is what makes `compile_mux_sound` cheap.
- The constant `1` of M is a parameter `Params.one` with `one.ev w = 1` (SelOk). Who pins M's `one`
  cell is an open question for the blueprint (E's target covers H only).

### (2) `FRVIRMux` + `compile_mux_sound`: done (kernel)

`muxP` (three selector cells), `compileMux = compile (muxP …)`, `oneHot_of_rows` (Boolean cells +
three product rows + the linear row ⇒ one-hot), `compile_mux_sound` (one-hot at `κ` and `hdr`'s
kind byte `κ` ⇒ `semIR (mux) = some true`), `semIR_mux_eq`. Controls by `decide` on toy
assignments: `three_hot_sum` / `three_hot_fails` (the `(1,1,1)` selector passes the linear row,
fails the products), `hotN_rows`, `hotN_selOk`, `kindProg_rows_N` (positive) and
`kindProg_rows_L` (negative: a wrong kind's selector makes the rows of a kind-dependent constant
fail).

### (3) `FRWots`: done (kernel)

`wots_chain_sound` (three steps, selectors `[d<1]`, `[d<2]` on steps 2–3 and `[d<3]` on the end:
3 bits per chain = A.7's 399), `sigRoot_bits`, `wots_sound` (→ the contract's `SigOk`),
`w43_step`, `path_node`, `hashStmt_sound` (leaf and node halves with **separate** message
hypotheses), `hashStmt_ungated_vacuous` (finding F-1: §4.2's ungated 8 equalities make A and B1
share a message, unsatisfiable since A pins `tagLeaf` and B1 `tagNode`).

### 16:30–16:37: the OOM was mine

`logs/S-E2/count.lean` ran `#eval` of `compileMux … (gen (fun _ _ => []) .mux).ops` (61,753 ops,
interpreted; the compiler's `rows`/`slots` appends are quadratic in the interpreter) under
`lake env lean` with no memory cap: exit 137 at 16:37. Replaced (rule of the coordinator): no
evaluation of the whole program or layout. `nodeLayout`'s checks are closed-form arithmetic over
the layout constants plus a sortedness check of the ~80 interval endpoints; the M-row budget is
a closed-form row model (deviation D-2). All later commands run under
`systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 -- timeout …`.

### (4) `FRNodeLayout`: done (closed form)

82 kind intervals; `nodeLayout_chained` (order/disjointness), `regions_fit`, `usedBlocks_le`,
`mRows_le`. Finding F-3: §4.3's row categories sum to 529,201 per slot, not 526,076.

### (5) `node_sound`: not started (token budget); plan in RESULT §6.

All modules built under the 12 GB scope; sequential profiles `logs/S-E2/profile-*.log`; source
rule 0 findings.

### Revision 3.6 pass

The four cell-reading ops are now imports in the compiler. Also done: `hashStmt_sound` restated
with the gates, `digitSel_sound`, `oneCell`, and the row model updated (F-3′: the stated 531,588
still does not equal the sum of its categories, 532,067). New module `FRVIREval`: `walkA_eq`,
`walkB_eq`, `kindInd_eq`. `evalM`/`evalL` and `node_sound` wait for S-0's `gen fin`. Built against
S-0's working-tree `FRVIR` (it builds), with the 16 GB scope.
