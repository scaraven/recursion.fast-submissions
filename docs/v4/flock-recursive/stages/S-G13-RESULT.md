# S-G13 RESULT (pass 1): the route, the query bounds, the generic potential, `seq4`'s positions, the Rev4 frame; handover

- **Base.** HEAD `e189221`. **Build tree** `logs/fr-build-SG13` (a copy of `fr-build-SG12` with its
  `.lake`, `logs/org20`; `MINE.txt` lists the four new modules). Logs in `logs/S-G13/`. Journal:
  `S-G13-JOURNAL.md` (§0 is the route plan, written before any proof).
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under
  `timeout`. No sub-agents. Nothing committed. No existing module was edited and no existing
  statement changed. The worktree's modified `FRVIR*`/`FRVIRTpl*` files (S-E13's) were not touched;
  `snap.sh` builds HEAD's text of them.

## Status

| Item | State |
|---|---|
| Step 1: the route | **Done** (journal §0): route **(C)**, a hybrid. Reasons and estimates below. |
| (e) query bounds `qS = 8,905` | **Done**: `queries_VsegC`, `queries_VnodeC`, `ks_queriesC4`. |
| Generic potential over an item list (C1) | **Done**: `FRSoundnessFrChain` (3.x is the `rfl` instance). |
| `seq4`'s positions, multi-squeeze phases, chain kind (C2) | **Done**: `FRSoundness4Pos`. |
| (f)/(g) the Rev4 `E` and the final theorem's frame | **Done as a frame**: `E4`, `finalLaw4`, `ks4_of`, `ks4_E4`. The final theorem now has exactly three open inputs (§3). |
| The potential at `seq4` (dooms, obligations, `step`) | Not started: parts T4, P4a, P4b (§6). |
| `flag_fin*` over `FinP`, views over `gen4`, `finLog` on `gen4` | Not started: part R4 (§6). |
| Front checks, O1 | Not started; to be done once, at Rev4 only (route C). |
| Per-kind `SegSoundLog`, nodes N2/N4/N8, `hRes` | Not started (§6). **The node half is blocked on S-E** (F3). |

**Checks:**
- `lake build FR` plus the four modules: green, 2,428 jobs (`build-final.log`).
- **Axioms** (`axioms.log`, 36 names): within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule:** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`:
  204 files, 0 findings (`source-rule.log`).
- **Names.** Every new top-level name was grepped against all `FR*.lean` (untracked included): one
  declaration each. The `FR.Snd.G` copies (`Matches`, `IsChain`, `chains`, `muG`, `muG_step_of`, …)
  share their short names with `FR.Snd`'s by design; their full names differ.

**Imports for `FR.lean`:** add `import FRSoundness4Frame` (it pulls `FRSoundness4Qry` and
`FRSoundness4Agg`) and `import FRSoundness4Pos` (it pulls `FRSoundnessFrChain`).

## 1. The route (journal §0, summarised)

Three facts decide it:
1. **`gen` is not provably `gen4 seq3`.** S-0′ measured the skeletons equal up to register renaming,
   but no theorem says so; `finalsOf_seq3`/`finOps4_seq3` relate only the finals' fields. So the
   program layer (`accept_chain`, `finLog_of_run`, every view, `start_run`, `w0V_run`, `lc_ii_run`,
   ≈ 5,500 lines in 22 modules) is new work on `gen4` on every route. Proving the remaining 3.x front
   checks first (route A) proves them twice.
2. **Positions and kinds are literal throughout the 3.x chain.** The global `fsItems` sits under
   `Matches`/`IsChain`/`muG`. Literal positions fill the dooms (`FrE` 138, `FrL` 76, `FrS` 75,
   `FrObl` 64). The 3-constructor `Kind` is case-split everywhere and cannot be extended (S-0′ §0).
   `seq4`'s positions equal 3.x's below 170 (Z, L, S) and shift by +1 … +14 after (table in journal
   §0.1). Generalising all of it in place (route B) means re-expressing hundreds of statements over a
   positions structure, with per-`Seq` fact bundles, and re-checking 3.x after each edit.
3. **The harness builds every module of `lean/`** (`gen.sh`, as `evaluate.py`'s `mkfresh`). A
   second full chain doubles the soundness build until one is deleted.

**Route C:**
- **(C1, done)** A generic potential over an item list `FsSeq`. These proofs never inspect a position.
- **(C2, done)** `seq4`'s positions and the chain kind, as concrete certificates.
- **(T4, P4a, P4b)** Port the dooms and obligations by copy at `seq4`/`CKind`. The position map is
  mechanical. Import the algebra (`lin_*`, `bz_*`, `batch_*`, `Rows`' unit, the MCA/Ligerito lemmas);
  do not copy it. Make the semantic deltas in the copy: segments, node dims per kind, **O1**.
- **(R4)** Build the program layer once on `gen4`, then do **the front checks once, at Rev4**.
- **(X4)** The per-kind laws and the composition.
- **Integration.** Retire the 3.x S-G chain, so that the certificate builds one chain.

Against A, C saves the 3.x front checks, 3.x's O1 and 3.x's `hQ` (≈ 2,500 lines). Against B, it
avoids symbolic generalisation and the 3.x re-checks. Its cost is a temporary second copy of T and P,
deleted with 3.x.

## 2. What was built (`loc.py`, `logs/S-G13/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4Qry` | 227 / 166 / 28 | `items_merkleOps4`, `items_posOps4`, `noAsk_lastOps`, `noAsk_stmtOps4`, **`items_genPhase4`**, `items_genPhases4`, **`items_gen4`**; `noAsk_gFin*` (nine fields; helpers `noAsk_gCellsOps`, `noAsk_gLvsOps`, `noAsk_padOps`, `noAsk_gEncOps`, `noAsk_gShCore`), **`noAsk_finalsOf`**, `noAsk_ops`, **`noAsk_finOps4`**; **`queries_VsegC`**, **`queries_VnodeC`**, **`ks_queriesC4`** |
| `FRSoundnessFrChain` | 712 / 585 / 24 | `class FsSeq`; in `FR.Snd.G`: `Matches`, `IsChain`, `chains`, `chains_append`, `mem_chains`, `isChain_new`, `matches_append`, `isChain_new_of_seed/_extend`, `EscG`, `sumG`, `muG`, `muG_step`, `matches_append_iff`, `ext_take`, `RndOK`, `hloc_of`, **`muG_step_of`**; `fs3`, `matches_fs3`, `isChain_fs3`, `chains_fs3`, `muG_fs3` |
| `FRSoundness4Pos` | 186 / 96 / 15 | `fsItems4` (482), **`instance fsSeq4`**, `fsStarts4`, `phStart4`, **`fsStarts4_eq`**, **`phStart4_shift`**, `phOf4`, `fsRanges4`, `fsRnd4`, `rangesOK4_eq`, **`fsRanges4_eq`**, **`fsRnd4_ok`**; `CKind` (`byte`, `m`, `isNode`, `ofByte?`, `lv`), **`kindOfC`**, `kindOfC_congr`; controls |
| `FRSoundness4Frame` | 177 / 105 / 11 | **`E4`**, `ExtOff`, `NodeExtLog`, `NodeSoundLog`, **`finalLaw4`**, `extOff_E4`, `nodeExt_E4`, **`ks4_of`**, **`ks4_E4`**; controls |
| **total** | 1,302 / 952 / 78 | |

## 3. The main statements

```lean
theorem items_gen4 (S : Seq) (p : KindP) (fin : FinOps) (hfin : ∀ outs b, (fin outs b).filterMap Op.item? = []) :
    (gen4 S p fin).ops.filterMap Op.item? = itemsOf S
theorem queries_VsegC (impl₀ : OpImpl) (H) (κ : SegKind) (vk c : Digest) (π : Proof) :
    ((VsegC impl₀ κ vk c π).queries H).length = 8905          -- likewise queries_VnodeC
theorem ks_queriesC4 … (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4) (vk : Digest) :
    ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV

class FsSeq where fs : List Item; one_le : 1 ≤ fs.length          -- FR.Snd.G
theorem G.muG_step_of [FsSeq] (hrnd : RndOK rnd) (h0 : rnd 0 = none) … :   -- 3.x's, over FsSeq.fs
    ∑ a : Digest, muG D (pRoundG D rnd) (L ++ [(q, a)]) ≤ (muG D (pRoundG D rnd) L + (badCount / 2^256 + δ)) * 2^256
instance fsSeq4 : G.FsSeq := ⟨fsItems4, _⟩
theorem fsRnd4_ok : G.RndOK fsRnd4

def E4 (A) (c) (π) (_L) : Option Wit := match kindOf4 π with
  | .W => decode π | .agg => (aggWit (piSizeOf seq4) π).map (fun p => .leaf p.1 p.2)
  | .node _ => X.search A (X.vkOf π) c | .bad => none
theorem ks4_of (impl₀ implN cells S vk) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4)
    (hE : ExtOff S.E) (μ : Log → ℝ≥0) (h0 : μ [] = 0)
    (hstep : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst → ∑ a, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2^256)
    (hS : SegSoundLog (VsegC impl₀) vk fun L => L.length ≤ logCap ∧ μ L < 1)
    (hN : NodeExtLog (VnodeC implN cells) vk (fun L => L.length ≤ logCap ∧ μ L < 1) S.E (Rel (S.acc vk))) :
    KS (Rel (S.acc vk)) (S.V vk) S.E ε S.qV
```

**So the Rev4 final theorem needs exactly three more inputs:**
1. a potential `μ` with `empty` and `step` at `εR`: the doom chain at `seq4`, through `G.muG_step_of`;
2. `SegSoundLog (VsegC impl₀) vk Good`, at every segment kind;
3. `NodeExtLog (VnodeC implN cells) vk Good S.E (Rel (S.acc vk))`, at every node kind.
   At `E4` this is `NodeSoundLog`: the run's key, plus a witness of the node relation.

The hypotheses left on the final theorem should then be:
- `hV`, `hq`;
- `hE` (`ExtOff` and the extractor's node law, or `S.E = E4 S.acc`);
- `hRes` (per node kind);
- `hfit` (per node kind's plan);
- `implSegC_meets` and the node kinds' `Meets`.

## 4. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `prof-*.log`)

| Module | wall (import ≈ 5 s) | kernel (type checking) | max RSS |
|---|---|---|---|
| `FRSoundness4Qry` | 28.2 s (four `simp`s 1.5–3.7 s: `items_genPhase4`, `noAsk_gFinLc`/`gShCore`) | 0.14 s | 2.83 GB |
| `FRSoundnessFrChain` | 12.9 s | < 0.1 s per declaration | 2.68 GB |
| `FRSoundness4Pos` | 19.3 s | 10.7 s (`rangesOK4_eq` ≈ 6 s, `fsStarts4_eq`, `fsRanges4_eq`, `fsItems4_length`) | 3.44 GB |
| `FRSoundness4Frame` | 7.0 s | 0.22 s | 2.87 GB |

`decide` uses: the `seq4` position certificates (`decide +kernel` over the 482-item list, as 3.x's
`fsStarts_eq`/`rangesOK_eq` over 468), kind-byte facts, and `36000 ≤ 2^16`. None runs over a
program or a table.

## 5. Findings and deviations

- **F1. 3.x's `hQ` already exists in substance.** `FRVIRSpec.queries_gen` gives 8,891 queries for
  `genWith fin m`; only a `Vwith`-level wrapper is missing. I did not write it (route C: 3.x is the
  template).
- **F2. `E4` is the specification extractor.** Its node branch is `X.search` (B-15's `Eout`).
  B-15's certificate `E` is `if InDomE then Ed else Eout`, where `Ed` is the extractor program's
  denotation; that program's revision 4.1 form (an `A` branch, the six kinds) is S-H's. So the frame
  is stated for any `S.E` meeting `ExtOff` and `NodeExtLog`, and `ks4_E4` is its `E4` instance.
  **Ask:** which `E` the Rev4 certificate uses. If `E4`, someone must prove its `Computes`; if a
  Rev4 `X.E`, S-H must provide `ExtOff` and the `Ed` node law.
- **F3. The Rev4 node circuit is not defined in Lean (it blocks the node half).** The node's Z/S/L
  truths and `NodeSoundLog` need, per `N2`/`N4`/`N8`:
  - the block-kind map (3.x: `FRSoundnessFront.nodeBK`, `FRNodeCircuit.nodeKind`, over `Layout.*`);
  - the block targets (`targetS`'s spec on the node layout);
  - the kind indicators of the 3.16 kind factor (`indKW`/`KW.nodeKinds`);
  - the statement/residual pair `StmtN`/`NodeResid` (S-N1's `hRes`), with 1 + k slots and R-4-m2's
    padding and byte-counter claim.

  `FRNodeLayout4` has only the region sizes. These are S-E's (L-circ, S-E13 in progress). Until they
  exist, the ported node dooms must take them as parameters.
- **F4. Build budget.** See §1, fact 3. **Ask:** retire the 3.x S-G chain (the `FRSoundness*`
  modules that only 3.x imports) once Rev4 is complete.
- **F5. `FsSeq` is a class with one global instance** (`fsSeq4`). 3.x's list is the `abbrev fs3`,
  not an instance, so the two never meet in instance search. Ported modules can then write
  `G.Matches es` and read `fsItems4` by `rfl` (`fs_eq4`).
- No value the argument needs was found missing from the finals in this pass. The pass did not reach
  the flag lemmas.

## 6. Handover: the remaining items, in order, and the parallel split

After C1/C2 the work splits into **four parts on disjoint new modules**. T4, P4a/P4b and R4 can run
three at a time; X4 follows.

**Common rules for the ports:**
- Import the 3.x modules for their position-free algebra. Copy only the concrete instances.
- Position map (`phStart4_shift`): identity below 170. Then `+1` in `Lr2` (`178 → 179`), `+5` for
  `Lrend`/`Lr3`/`E1`, `+6` in `E2`, `+10` for `Eend`/`E3`/`E4`, `+14` from `E4end` (311 → 325) to the
  end. The rounds in `Lr2`/`E2`/`E4` grow from 15/21/23 to 17/23/25, and `E1`/`Lr1` gain a squeeze.
- Read the chain kind with `kindOfC` (`CKind`), the ladder with `CKind.lv`, chains with `G.Matches`,
  and phases with `fsRnd4`.
- Re-certify each `decide` table (`frontCls_check`, `tailCls_check`, `absPts`/`sqPts`/`rndPh`,
  `nsqPts`, `p1Start_zero`) on `fsItems4`.

1. **T4, the Ligerito tail at `seq4`.**
   - Copy the instances of `StepB…E`, `Truths`, `Hide`, `Walk`, `Phases`, `Fold`, `Weights`,
     `Tail`, `TailD`, `TailO`, `TailM`, `LigFinal` and `Compose`. These are positions ≥ 332 (3.x
     318) and a uniform `+14`.
   - The kind enters only through the ladder (`lvl κ i` → `κ.lv i`; `m ∈ {30, 31, 32}`). `L31`/`N2`
     use the new `ladderOf 31`, so `mLog`, `nrP` and `padV` need their 6-kind tables.
   - Deliver `muT4`, `PhaseObl4` and `kstate`'s `empty`/`step` via `G.muG_step_of fsRnd4_ok
     fsRnd4_zero`. The interface to the front is `FrontObl` (`RejF`, `DF`, `W₀`, `c₀`), unchanged in
     form.
2. **P4a: Z, L, S, Sh** (positions < 170, unchanged).
   - Port `FrZ`, `FrZM`, `FrL`, `FrLN`, `FrS`, `FrSh`, `FrPend`, `FrBind`, `FrExt`, `Shift` and the
     `PIOP`/`Truths` instances to `CKind`.
   - **Segment deltas:** `SegHolds` (`1 ≤ n ≤ cap`, free blocks past `L`); Z2's `targetS` with the
     range factor (`targetSSeg_meets`); Sh's masked successor (`shiftSeg_meets`, `shiftSeg_cube`;
     `shift_unmasked_link` is the negative); `L` from `lastOps` (S-F4 §7 Q3: no `pureRun` lemma yet,
     so this part must prove one).
   - **Node:** parametric in F3's maps until S-E delivers them.
3. **P4b: Lr, E, RS0/RS, B′, W0** (shifted positions).
   - Port `Rows`' instances, `FrE`, `FrB`, `FrRS0`, `FrRS`, `FrW0`, `FrDF`, `FrObl`, `FrStab`.
   - Node dims per kind: Lr 17 (`N2` 16 real); E2 23 (22); E4 25 (24); τ 22/23; σ 24/25 (`finP_ctrl`,
     `coords_eq`).
   - **O1 here:** state `truthE`/`nE`/`RejE4`/`hfit` over `nodeIRows (planOf fin)`, per node kind,
     through an entries source (ruling S-G12′ F3). Do not do it first on 3.x.
4. **R4: the program layer on `gen4 seq4 p (finOps4 P)`.**
   - The template is 3.x's `Acc*`, `FrRun`, `FrRnd`, `FrRndV`, `FrW0V`, `FrLc`, `FrWalk`, `FrK`.
   - Deliver `accept_chain4` (it takes `noAsk_finalsOf`, done here), `runLog_chain4`, `matches_fsQ4`,
     `kindOfC_fsQ`, and `flag_fin*` over `FinP` (at `seq4`'s sizes; `finalsOf_seq3` keeps 3.x's).
   - Deliver the views over `genPhase4` and `finLog4_of_run`.
   - Then **the front checks once**:
     - `RejL2`: round 0 via `relLc` (i) and the Zend view;
     - `RejRS` claims 0–3;
     - `RejZ`, `RejS2`;
     - the two `RejEnd`s (a degree-3 / `.zero` rounds view);
     - `RejInE`, `RejE4`.

     They need P4's `Rej*` names (fix those names first, in a stub module, so that R4 can start in
     parallel).
5. **X4: the laws and the composition.**
   - **`SegSoundLog (VsegC impl₀)`:** from R4's accepted run and T4/P4's `¬ doom ⇒ truths ⇒
     SegHolds`, then `seg_sound`. It uses `1 ≤ n` (`lastOps`, R-4-M2).
   - **`NodeExtLog`/`NodeSoundLog` per `N2`/`N4`/`N8`:**
     - slot 1 over `{N2, N4, N8}`, the sub-slots over `{L30, L31, L32}`;
     - `childOk4` as a truth of `N2`'s relation;
     - `hRes` naming the aggregate's padding/counter claim (R-4-m2: unaligned at `k = 2, 3, 4`).

     This needs F3.
   - **The final theorem:** `ks4_of` (or `ks4_E4`) with `μ := muT4`. Then the axioms, the source
     rule and the sequential profiles.

## 7. Controls

| Definition | Positive | Negative |
|---|---|---|
| `G.Matches` / `FsSeq` (generic) | `matches_fs3` … `muG_fs3` (3.x is the instance, `rfl`) | `fsItems4_ne` (the `seq4` instance is a different list) |
| `G.Matches` at `fsSeq4` | `matches4_seed` | `not_matches4_squeeze` |
| `CKind.ofByte?` / `kindOfC` | `kindOfC_ctrl`: `0x4D ↦ N2`, `0x4B ↦ L31`; `CKind.ofByte?_byte` | `kindOfC_ctrl`: `0x41` (the aggregate) is no chain kind; the empty log reads the default |
| `fsRnd4` | `fsRanges4_eq`, `fsRnd4_ok` | `fsRnd4_zero` (the seed is in no phase) |
| `E4` / `ExtOff` | `E4_W`, `extOff_E4` | `E4_bad` (a bare segment byte, a node byte of the wrong size); `not_extOff_none` |
| `NodeSoundLog` | `nodeSoundLog_false` | `not_nodeSoundLog_true` (the accept-all node program fails it) |
| `queries_*` | `= 8,905` exactly (an equality, not a bound) | (`fieldOffs`'s `seq4 ≠ seq3`, S-0′) |

## 8. Open questions

1. F2: which extractor does the Rev4 certificate use (`E4` with a `Computes` proof, or a Rev4 `X.E`
   from S-H)?
2. F3: when will S-E's Rev4 node circuit maps exist, and in which modules? The node half of P4 and
   X4 waits on them.
3. F4: may the 3.x S-G chain be retired from `lean/` once the Rev4 theorem is complete?
4. Should the generic potential (`FRSoundnessFrChain`) replace `FRLog`/`FRSoundnessDefs` in place at
   that integration? `fs3` already shows 3.x is its instance by `rfl`.
