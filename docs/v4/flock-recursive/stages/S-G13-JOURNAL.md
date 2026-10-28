# S-G13 JOURNAL: knowledge soundness for the revision 4.1 verifier (`V4with VsegC VnodeC`)

- Base: HEAD `e189221` (branch `v4/flock-recursive`). Build tree `logs/fr-build-SG13` (a copy of
  `fr-build-SG12` with its `.lake`; `snap.sh` + `MINE.txt`; `logs/org20`). Logs `logs/S-G13/`.
- `lake build FR` on HEAD in the new tree: green, 2,424 jobs, all cached (`build-0.log`).
- Every lean/lake command runs in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. The worktree's modified `FRVIR*`/`FRVIRTpl*` files are S-E13's
  (L-circ, in progress); `snap.sh` builds HEAD's text of them, and this track does not touch them.

## 0. Step 1: the route (written before any proof)

### 0.1 Facts that decide it (measured or read off the code)

1. **Positions.** `seq4`'s Fiat–Shamir item list has 482 items (3.x: 468; `logs/fr-build-SG13/scratch/Pos.lean`).
   Its phase starts are 3.x's up to `Lr1` (position 170) and then shift:

   | phases (number in `phasesOf`) | 3.x start | `seq4` start | shift |
   |---|---|---|---|
   | 0–13 (seed … `Lr1`) | 0 … 170 | same | 0 |
   | 14 `Lr2` | 178 | 179 | +1 (`Lr1` 9 squeezes, not 8) |
   | 15–17 `Lrend`, `Lr3`, `E1` | 208, 209, 210 | 213, 214, 215 | +5 (`Lr2` 17 rounds) |
   | 18 `E2` | 221 | 227 | +6 (`E1` 12 squeezes) |
   | 19–21 `Eend`, `E3`, `E4` | 263, 264, 265 | 273, 274, 275 | +10 (`E2` 23 rounds) |
   | 22–51 (`E4end` … `Pf`) | 311 … 454 | 325 … 468 | +14 (`E4` 25 rounds) |

   So Z, L, S (positions < 170) sit at the same positions; Lr, E, RS, B′ and the whole Ligerito tail
   move. Every doom definition carries its positions as literals (`FrE`: 138 literal positions,
   `FrL` 76, `FrS` 75, `FrObl` 64, …), and the 3.x item list is global (`FRLog.fsItems`, used by
   `Matches`/`IsChain`/`chains`, hence by `muG` and every obligation).
2. **Kinds.** The chain's kind is 3.x's 3-constructor `Kind` (`StepA.kindOf es`, byte 71), case-split
   throughout (`FrS` 99 uses, `LigFinal` 82, `FrZ` 77). Rev4 has six SNARK kinds (`SegKind ⊕
   NodeKind`, m ∈ {30, 31, 32}; `L31`/`N2` use the new `ladderOf 31`). `Kind` cannot be extended
   (S-0′ §0: 105 case splits, some in forbidden modules).
3. **Programs.** `gen4 seq3 (.ofSeg .L32) (finOps4 fin3P)` equals 3.x's `gen … (.fixed .L32)` only
   up to register renaming, and that is a **measurement** (S-0′ §3, `regmap-4.0-seq3.log`), not a
   theorem. `finalsOf_seq3`/`finOps4_seq3` relate the finals' *fields*, not the skeletons. So the
   program layer (`accept_chain`, `finLog_of_run`, every view, `start_run`, `w0V_run`, `lc_ii_run`)
   can never be inherited by instantiation: on `gen4` it is new work on every route.
4. **Node circuit.** Rev4 has the node layouts' sizes (`FRNodeLayout4`) but no block-kind map,
   targets or residual for `N2`/`N4`/`N8` (3.x: `FRNodeCircuit`, `nodeKind`, `nodeBK`, `Layout.*`,
   `StmtN`, `NodeResid`). Those are S-E's (L-circ). The node's Z/S/L truths need them; the segment's
   need only `SegHolds`/`FRSegTarget4`, which exist.
5. **Build budget.** The harness builds every module of `lean/` (`gen.sh`: every module a root, as
   `evaluate.py`'s `mkfresh`). Two full S-G chains in the entry double the soundness build.
   The 3.x chain is ≈ 22,000 lines in 74 modules, with a linear import chain ≈ 50 deep.

Module groups of the 3.x chain (lines, `wc -l`):

| group | modules | lines | depends on positions | on `Kind` | on the 3.x program |
|---|---|---|---|---|---|
| F foundation | `FRLog` (chain part), `Defs`, `StepA`, `Front`, `Compose` | 2,561 | `fsItems`, `fsRanges`, `fsStarts` | little | no |
| T Ligerito tail | `StepB…E`, `Truths`, `Hide`, `Walk`, `Phases`, `Fold`, `Weights`, `Tail*`, `LigFinal`, `Ligerito` | 6,086 | `phStart (26+5i)` symbolic, `fsStarts_eq` | ladder only (`lvl κ i`) | no |
| P front PIOP | `PIOP`, `Shift`, `Rows`, `FrZ`, `FrZM`, `FrL`, `FrLN`, `FrS`, `FrSh`, `FrPend`, `FrBind`, `FrExt`, `FrE`, `FrB`, `FrRS0`, `FrRS`, `FrW0`, `FrDF`, `FrObl`, `FrStab` | 7,639 | literal | heavy (node matrices, layout, dims) | no |
| R program | `Acc*` (14), `FrRun`, `FrRnd`, `FrRndV`, `FrW0V`, `FrLc`, `FrWalk`, `FrK`, `FrKS` | 5,484 | via `phases`/`fsMsgs` | some | **yes** |
| X extraction | `Ext*` (6), `4Agg` | 1,244 | little | yes | node relation |

### 0.2 The three routes, by what they touch

- **(A) Finish 3.x, then port.** 3.x front checks (`RejL2`, `RejRS` 0–3, `RejZ`, `RejS2`, 2× `RejEnd`,
  `RejInE`, `RejE4`) on `gen`'s views; O1 in place in `Rows`, `FrE`, `FrDF`, `FrStab`, `FrObl`, `PIOP`,
  `Weights` (3.x statements change); `hQ`. Then the port re-certifies every concrete fact at `seq4`
  and Kind4 in all 74 modules. **By fact 3 the front checks and the views are proved twice** (once on
  `gen`, once on `gen4`), and O1 is done in place on 3.x and then ported. Kernel: two chains until 3.x
  is retired.
- **(B) Generalise first.** Every doom, `Reads n`, `single`/`habs` count and `decide` certificate of
  F, T, P restated over a positions structure and a kind interface, with 3.x as the instance
  (`itemsOf_seq3`, `phasesOf_seq3`). Literal arithmetic (`omega`/`norm_num` on `209 + 1 + 11 = 221`)
  becomes relational facts bundled per `Seq` and certified per `Seq` by `decide`; every `cases κ` over
  3 kinds is re-done over an abstract kind type. **R cannot be generalised with 3.x as an instance**
  (fact 3), so B saves nothing there. One chain in the end. Per line B is the most expensive (every
  statement edited, 3.x re-checked after each edit through a 2,400-job rebuild, concurrent with
  other tracks building on the same modules).
- **(C) Hybrid, chosen.**
  1. **Generic foundation, new modules** (not edited in place): `MatchesI fs`, `IsChainI fs`,
     `chainsI fs`, their lemmas, `muGI fs` and its step law, generic over the item list `fs` (the
     proofs never inspect a position). 3.x is the instance `fs := fsItems` by `rfl` (control).
  2. **The Rev4 positions and kinds**, concrete at `seq4`: `fsItems4`, `fsStarts4`/`phStart4`,
     `fsRanges4` with their `decide` certificates; `Kind4` (`SegKind ⊕ NodeKind` read from byte 71)
     with its per-kind data (`m`, `isNode`, ladder `ladderOf m`, the node dims and real rounds).
  3. **Port T and P by copy** to `FRSoundness4*` modules at `seq4`/`Kind4`: the algebra lemmas are
     imported, not copied (they are position-free: `lin_*`, `bz_*`, `batch_*`, `Rows`' generic unit,
     the MCA/Ligerito lemmas); only the concrete instances (dooms, `Reads n`, `habs`/`single` at
     positions, the obligations' case tables) are copied with the position map of §0.1. The
     semantic deltas are done in the copy: segments (`SegHolds` with `n`, the masked successor,
     `targetS` range factor), node dims per kind (Lr 17 / E2 23 / E4 25, τ 22/23, σ 24/25), **O1**
     (E over `nodeIRows` per node kind) directly in the Rev4 E unit.
  4. **R on `gen4` once**, with the 3.x modules as template: `accept_chain4`, `finLog4_of_run`, the
     views, `flag_fin*` over `FinP`, then **the front checks once, at Rev4 only**. 3.x's remaining
     checks, its O1 and its `hQ` are **not** done (they would be proved again on `gen4`).
  5. X and the composition (Rev4 `E`, per-kind `SegSoundLog`, nodes with `childOk4`, the final
     theorem) at Rev4.
  6. At integration the orchestrator retires the 3.x S-G chain (fact 5), so the certificate holds
     one chain.

  Total: foundation ≈ 1,200 lines new; T ≈ 6,000 lines copied with a uniform `+14` shift and a
  ladder by `m`; P ≈ 7,600 lines copied, positions < 170 unchanged, the rest shifted, plus the
  semantic deltas; R ≈ 5,500 lines new against `gen4` (the template's structure kept); X/compose
  ≈ 1,500 lines. Against A it saves the 3.x front checks and 3.x O1 (≈ 2,500 lines) and the second
  kernel copy; against B it avoids re-proving 3.x after symbolic generalisation and the per-`Seq`
  fact bundles, at the price of a temporary second copy of T and P that is deleted with 3.x.

### 0.3 Parallel split (for the orchestrator)

After C1–C2 (this pass), the work splits into four parts on disjoint new modules:

| part | modules (new) | needs |
|---|---|---|
| **T4** the Ligerito tail at `seq4` | `FRSoundness4Tail*`, `…4LigFinal`, `…4Compose` | C1, C2 |
| **P4a** Z, L, S, Sh (positions < 170) | `FRSoundness4FrZ*`, `…4FrL*`, `…4FrS*` | C1, C2; the node half also needs S-E's Rev4 node block-kind map (fact 4) |
| **P4b** Lr, E (with O1), RS, B′, W0 | `FRSoundness4FrE`, `…4FrB`, `…4FrRS*`, `…4FrW0` | C1, C2; `nodeIRows (planOf fin)` per node kind |
| **R4** the program layer on `gen4` | `FRSoundness4Acc*`, `…4Views`, `…4Flags` | C2 only (views are doom-free); the front checks need P4's `Rej*` names |

T4, P4a/P4b and R4 can run three at a time. X4/composition follows them.

### 0.4 Order inside this pass

1. (e) the per-program query bounds `qS = 8,905` (`FRSoundness4Qry`): self-contained, closes
   `ks_queries4`'s hypotheses for `VC4`.
2. C1 the generic foundation (`FRSoundnessFrChain`, `FRSoundnessFrMu`).
3. C2 the Rev4 positions and kinds (`FRSoundness4Pos`).
4. Handover with the split of §0.3.

## Log

### Item (e), the query bounds (done): `FRSoundness4Qry`

- `items_merkleOps4`, `items_posOps4`, `noAsk_lastOps`, `noAsk_stmtOps4`, **`items_genPhase4`** (every
  shape, both kinds of `KindP`: a segment's `lastOps` and Z2 operand ask nothing), `items_genPhases4`,
  **`items_gen4`** (= `itemsOf S`). The 3.x lemmas `items_sqzOps`, `items_roundsOps` (generic in
  `real`), `flatMap_range_const` are reused.
- The finals: `noAsk_gFin*` for the nine fields of `finalsOf P` (helpers `noAsk_gCellsOps`,
  `noAsk_gLvsOps`, `noAsk_padOps`, `noAsk_gEncOps`), **`noAsk_finalsOf`** in `accept_chain`'s
  hypothesis form (R4 will need it), `noAsk_ops`, **`noAsk_finOps4`** (through `item_reloc`).
- **`queries_VsegC`/`queries_VnodeC` = 8,905**, **`ks_queriesC4`** (`ks_queries4` with `qS = 8,905`).
- Finding: 3.x's `hQ` is already available as `queries_gen` (= 8,891); only a `Vwith`-level wrapper
  is missing. Not done (route C: 3.x is the template only).

### C1, the generic foundation (done): `FRSoundnessFrChain`

- A mechanical copy (a text-substitution script) of `FRLog`'s
  chain part and `FRSoundnessDefs` Parts A–C into namespace `FR.Snd.G` over `class FsSeq` (`fs`,
  `1 ≤ |fs|`). Only `fsItems` → `FsSeq.fs` and `one_le_fsItems` → `FsSeq.one_le` changed.
- Every copied declaration that does not read the list was dropped again (the linter's "unused
  `[FsSeq]`" list, plus the defs `EscAtG`, `termG`, `lastAns`, `ext1`, `ext`, `condCount`, `StabExt`,
  `pRoundG`); inside `FR.Snd.G` those names resolve to `FR.Snd`'s. What remains: `Matches`,
  `IsChain`, `chains`, `EscG`, `sumG`, `muG` and the 24 theorems that read them (`chains_append`,
  `isChain_new*`, `muG_step`, `matches_append_iff`, `ext_take`, `RndOK`, `hloc_of`, `muG_step_of`).
- 3.x as the instance: `fs3` (an `abbrev`, not an instance), `matches_fs3`, `isChain_fs3`,
  `chains_fs3`, `muG_fs3`, all `rfl`.

### C2, the Rev4 positions and kinds (done): `FRSoundness4Pos`

- `fsItems4` (482), **`instance fsSeq4`** (the only `FsSeq` instance), `fsStarts4`/`phStart4`,
  **`fsStarts4_eq`**, **`phStart4_shift`** (against 3.x: 0 / +1 / +5 / +6 / +10 / +14), `phOf4`,
  `fsRanges4`, `fsRnd4`, `rangesOK4_eq`, **`fsRanges4_eq`**, `fsRnd4_zero`, **`fsRnd4_ok`**.
- `CKind` (`seg SegKind | node NodeKind`), `byte`, `m`, `isNode`, `ofByte?`, `ofByte?_byte`, `lv`
  (`lvOf m`), `m_mem`; **`kindOfC es`** (byte 71), `kindOfC_congr`.
- Controls: `matches4_seed` (+), `not_matches4_squeeze` (−), `fsItems4_ne` (−: the instance changes
  what a chain is), `kindOfC_ctrl` (+/−).
- Kernel 10.7 s (sequential), mostly `rangesOK4_eq` (6 s) and the `decide` certificates; 3.x's
  `rangesOK_eq`/`fsStarts_eq` are the same kind of cost.

### Items (f)/(g) frame (done): `FRSoundness4Frame`

- `E4 A` (B-15 on `kindOf4`), `ExtOff E`, `NodeExtLog`, `NodeSoundLog`, **`finalLaw4`** (for any
  extractor meeting `ExtOff`), `extOff_E4`, `nodeExt_E4` (the search, `search_spec_acc`,
  `sFits_of_acc` at `qV4 ≤ qMax`), **`ks4_of`** (any potential with `empty`/`step` at `ε`, plus
  `SegSoundLog` and `NodeExtLog` at `Good L := |L| ≤ logCap ∧ μ L < 1`), **`ks4_E4`**.
- Why `ExtOff`/`NodeExtLog` and not `hE : S.E = E4 S.acc` only: B-15's computable `E` is the
  extractor program's denotation on its domain (`X.E = if InDomE then Ed else Eout`); its revision
  4.1 form is S-H's. The frame serves both.
- Controls: `E4_W` (+), `E4_bad` (−), `not_extOff_none` (−), `nodeSoundLog_false` (+),
  `not_nodeSoundLog_true` (−, a size-generic node proof: no 798,192-byte term is built).
- Lesson: a `let π := ⟨#[b] ++ Array.replicate 798191 0⟩` with `show`/`rfl` hits max recursion;
  quantify over the size (`∀ n, 1 ≤ n → ∃ π, …`) and instantiate.

### Checks (end of pass 1)

- `lake build FR` + the four modules: green, 2,428 jobs (`logs/S-G13/build-final.log`).
- Axioms (36 names, `logs/S-G13/axioms.log`): within `propext`, `Classical.choice`, `Quot.sound`; no
  `sorryAx`.
- Source rule: 204 files, 0 findings (`logs/S-G13/source-rule.log`).
- Names: every new top-level name grepped over all `FR*.lean`: one declaration each. The `FR.Snd.G`
  copies share their short names with `FR.Snd`'s by design (different full names).
