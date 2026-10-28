# S-E12a JOURNAL: the revision 4.1 node circuit's specification (N2/N4/N8, 1 + k slots)

Base: HEAD `4acc3b3`. Build tree `logs/fr-build-SE12a` (copied from `fr-build-SG13`, `logs/org20`;
`MINE.txt` lists my modules). Logs: `logs/S-E12a/`. Namespace **`FR.N4c`**. Modules (new):
`FRNodeKinds4` (the block-kind map, targets, indicators, layout facts) and `FRNodeCircuit4`
(`StmtN4`, `NodeResid4`, `node_sound4`, the node laws, `hfit4`).

## 0. For S-E12b: the names of `NodeResid4` (fixed first; read this section)

`NodeResid4 I rd κ vk w` is a structure over the node witness `w : Asg` (`f⁽⁰⁾`), the node kind `κ`,
a **reader** `rd : Read4` (the pack map's read of the children from `w`) and a **slot interface**
`I : SlotIface4 Vseg Vnode` (S-E12b's compiled rows). Verifier slots are numbered `v < κ.vslots`:
`N2`/`N4`: `v = 0` the previous node, `v = 1 …` the segment sub-slots; `N8`: `v = 0 … 7` segment
sub-slots (aggregate 0: `0 … 3`, aggregate 1: `4 … 7`). Signed children `σ ∈ {0, 1}`: `N2`/`N4`
`σ = 0` the previous node, `σ = 1` the aggregate; `N8` both aggregates. Aggregates `a < nAgg κ`.

**`SlotIface4 Vseg Vnode`** (S-E12b instantiates it; one per node kind group, slot-indexed):

| field | meaning |
|---|---|
| `imp κ v w inp tr : Prop` | **imports**: the slot's imported registers (π bytes from H via the pack map, `vk`, `c`, the trace cells, L bits) hold the input's values |
| `rep κ v w inp tr : Prop` | **R**: the replay rows' claims (the run's registers are R's) |
| `tpl κ v w : Prop` | **templates**: every template instance row of slot `v` holds |
| `selN κ v w κ' : Prop`, `selS κ v w κ' : Prop` | the slot's kind selector picks `κ'` (node group `{N2, N4, N8}`, segment group `{L30, L31, L32}`) |
| `soundN` | `selN … κ' → imp → rep → tpl → (Vnode κ' vk c π).runSeq tr = some true` |
| `soundS` | `selS … κ' → imp → rep → tpl → (Vseg κ' vk c π).runSeq tr = some true` |

**`NodeResid4` items** (per item, as fields):

| field | owner | content |
|---|---|---|
| `imp v`, `rep v`, `tpl v` | S-E12b (M rows) | the interface's three predicates at slot `v`'s read input and trace |
| `selP` | S-E12b (one-hot rows) | `N2`/`N4`: slot 0's selector picks the previous node's kind `κ'`, and `π₁` has byte 0 `κ'.byte`, size `piSizeOf seq4` |
| `selA a i` | S-E12b | an active sub-slot `i < k_a` of aggregate `a` picks its segment's kind (`segView` of the read proof) |
| `pack σ` | pack map | the read signed child's format: `π.size < 2^64`, `|tr| ≤ qV4`, every query `≤ queryCap` |
| `aggFmt a` | pack map | `π_A`'s parse: `|π_A| = 48 + k · piSizeOf seq4`, byte 0 `'A'`, bytes 2–7 zero, the views of its `k` segments are the active sub-slots' |
| `aggTr a` | pack map | `tr_A` is the active sub-slots' traces concatenated |
| `aggChk a` | M rows + `hashA` (`c_A`, O-1) | `V_A`'s checks `aggChecks c_A n e vs` (statement, `1 ≤ k ≤ 4`, ranges, `Σ nᵢ = n`, `e_k = e`, chaining) |
| `kOk a` | M rows (R-4-m2) | `childOk4`: `k_a ≤ κ.maxK` (`N2`: 2) |
| `aggPad a` | M rows / S links (R-4-m2) | the `k`-gated final block: the candidate final block `F_{a,k}`'s `h_in` and message prefix are the main chain's, its padding bytes are zero (counter and final flag: `F_{a,k}`'s public target) |
| `wots σ` | M rows (O2b: digits, selector mux, mirror) | `SigOk vk (hDig4 κ σ k w) σ_σ`: WOTS verifies the H digest selected by `k` (the `k`-mux) |

The H-side lemma **`hDig4 … = traceDigest tr`** (from `truthZ4`/`truthS4`, `aggPad`, `pack`) is
not a residual item: it is a theorem obligation of the H side (BLAKE2s chain, `blake2s_chain`),
a hypothesis `DigOK4` of `node_sound4` until proved.

## 1. Layout decisions (block-kind map)

- H as `FRNodeLayout4.hUsed` (S-0′): main chains (prev `23,168` / aggregate `aggChainLen maxK`),
  `hashStmt` 3 per verifier slot, WOTS per signed child (498), `WM` 146 per verifier slot, 8 spare.
- **New, after `hUsed`** (in the slack before L): per aggregate `a`, `maxK` blocks: the candidate
  final blocks `F_{a,k′}` for `k′ = 1 … maxK − 1` (kind `stream`, target
  `streamTarget (1 + k′(S − 1)) (aggChainLen k′ − 1)`: counter and final flag of a `k′`-segment
  stream), then `c_A`'s `hashA` block (O-1). `k = maxK` uses the main chain's last block (final).
  `hEnd4 = hUsed + nAgg · maxK`: `N2` 70,957, `N4` 117,593, `N8` 187,548, all `≤ lBase`.
- The mirror `WM` serves the signed children's WOTS link families (`σ < 2`), as 3.x; S-0′ sized it
  per verifier slot, so `(vslots − 2) · 146` blocks stay `free`.

## 2. Pass 1 progress

- `FRNodeKinds4` green (`./chk.sh`, ~10 s): `TIv`, `nodeLayout4` (89 / 97 / 110 intervals),
  `layout_contig` (the certificate, `decide` on the endpoints only), the generic tiling lemmas
  (`contig_cover`, `contig_unique`, `ivAt_spec`), `nodeBK4`, `nodeKind4`, `Ind4`, `Sel4`,
  `kindIvs4`, `ind4_iff`, `sel4_true`, `nodeBK4_ne_chain`, `KindTgt`, `layout_tgtOk`,
  `nodeKind4_kind`, `nodeKind4_none_iff`, `bk_of_mem`, `tgt_of_mem`, `hEnd_le`, `ctr_final`,
  `indN4`, `etN4`, `kf4` (`kf4_eq`), `cells4` (`hcells4`), `chainLk4` (`chainLk4_stream`),
  `nodeBK4_wots`, `srcB4`/`mirB4` (`mir4_fits`), controls.
- `FRNodeCircuit4` green: `StmtN4`, `SlotIface4`, `Read4`, `NodeResid4` (names as §0, plus
  `chainMsg`), `AggPad4`, `DigLemma4`, `sig_of`, `agg_acc` (through `VA_complete`), `prev_acc`,
  **`node_sound4`**, `nodeSoundLog4_of`, `nodeExtLog4_of`, `nodeLaws4C` (`VC4`, `E4`),
  `zlm4_indKinds`, `HFit4`, `rowsFitI_of_sorted`, `hfit4_of`, controls.
- Item change for S-E12b: **`chainMsg σ`** (pack map): the stream the chain hashes (`chainBytes4`,
  `Stream.streamBytes` over the chain's blocks, the final block `F_{a,k}` for `k < maxK`) is
  `0x54 ‖ traceBytes tr`.
- Next: prove `DigLemma4` (the H side) from `Stream`'s chain argument.

## 3. Pass 1 end

- `FRNodeCircuit4Dig`: `chain_digest`, `digLemma4` (proved), `node_sound4'`, `nodeLaws4C'`.
- Final checks: build green (2,466 jobs), axioms 161 within the three, source rule 249 files 0
  findings, profiles. RESULT written.

## 4. Note for S-E12b (read after its JOURNAL and `FRNodeRows4`)

- **Public cells differ for an aggregate child.** `FRNodeRows4.pfCells4` puts every signed
  child's statement halves at its chain's seed payload (elements 2, 3). For an **aggregate** child
  the seed payload holds **segment 1's** statement `c_seg1 = leafStmt e₁ n₁`, not the aggregate's
  `c_A = leafStmt e n` that the node statement `nodeStmt c₁ c₂` names. `N4c.cells4` (`stC`) takes
  them from `c_A`'s `hashA` block's `h_out` (elements 2, 3 of block `cAB κ a`). Its `vk` halves
  stay the seed payload's. For the previous node the two maps agree. `chainBase4` agrees with
  `N4c.chBase`.
- Use `N4c.cells4` as the node finals' `cells` (`nodeFinP κ (cells κ)`, `VC4`'s `cells`).
  `hcells4P4b` is P4b's `hcells` at it.
