# S-G9 RESULT (pass 1): the front assembled (`DF`, `RejF`, `FrontObl`, `FrontChainStab`, `NodeL`); `kstate_front_of`; handover

- **Base.** HEAD `62a25fb`.
- **Build tree.** `logs/fr-build-SG9`, a copy of `fr-build-SG8` with its `.lake`, so nothing was
  rebuilt from scratch. `snap.sh` takes HEAD's sources for every other module and symlinks only
  `FRSoundnessFr*`. `FRSoundnessAccSem` and `FRSoundnessAccLog` are no longer symlinked: INT-5 has
  edited `FRSoundnessAccLog` in the worktree, and that edit names its in-progress `dotOps_noAsk` and
  `lcHead`.
- **Records.** Logs are in `logs/S-G9/`; the journal is `S-G9-JOURNAL.md`. The journal's §2
  tabulates every phase lemma used, with its hypotheses and conclusion; §3 gives the `DF` table.
- **Constraints.** Every lean/lake command ran in a capped scope (16G for builds, 12G for single
  files) under a `timeout`. No sub-agents were used. Nothing is committed. No existing module was
  edited.

## Status

**Done:**
- **Item 1.** `DF k` for all 26 phases, and `RejF`.
- **Item 2.** `FrontObl`, from one checked classification of positions 0 … 317.
- **Item 3.** `FrontChainStab`, and `hstab` alongside it.
- **Item 4.** `NodeL` as one hypothesis. Claim 2's binding stays a parameter `oLc`.
- **The composition.** `kstate_front_of` builds the `KState`. Its remaining hypotheses are:
  - `ExtIface` with `Stmt (finC finPf) SLeaf`;
  - `NodeL`;
  - the M rows' fit `hfit` (§4.1);
  - the extractor's `W` branch `hE`;
  - the three run facts `hStart`, `hW0` and `hFrontV`.

**Not done:**
- **Item 5.** Discharging `hStart`, `hW0` and `hFrontV` from the accepted run.
- **Item 6 in its final form.** `kstate_front`, whose only hypotheses are `ExtIface`, `NodeL` and
  the `implC` facts, waits on item 5.

§5 is the ordered handover.

**Checks:**
- `lake build FRSoundnessFrK` is green (2,384 jobs, no `sorry`, `logs/S-G9/build-FrK.log`). It builds
  all four new modules, plus `FRSoundnessAccLog` at HEAD.
- **Axioms** (`logs/S-G9/axioms.log`). All 122 new theorems and definitions were checked, including
  `kstate_front_of`. They use only `propext`, `Classical.choice` and `Quot.sound`: 100 use all
  three, 7 `[propext, Quot.sound]`, 11 `[propext]`, and 4 use none.
- **Source rule** (`logs/S-G9/source-rule.log`): 173 files, 0 findings.
- **Name clashes.** Every new declaration was grepped against every `FR*.lean`. `SS` clashed with
  `FR.X.SS` (`FRXChainDefs`) and is renamed `SameStab`. No other clash.

**Imports for `FR.lean`'s owner.** Add `import FRSoundnessFrK`. It imports the chain
`FRSoundnessFrObl` → `FRSoundnessFrStab` → `FRSoundnessFrDF` → `FRSoundnessFrZM`, and also
`FRSoundnessAccLog`.

## 1. What was built (code lines from `scripts/loc.py`, `logs/S-G9/loc.log`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrDF` | 367 / 246 / 25 | **`SLeaf`** (the ruled leaf statement), `truthS_same`, `sLeaf_reads`; **`okF oLc`** (RS0's bindings, Lc's a parameter), `okF_reads`, the bridges `okF_pendZ`/`okF_pendS`/`okF_pendE`/`okF_pendLc`/`okF_pendN`, `pendLc_ne`; **`NodeLF`**; the background parts (`far0`, `nPub`, `nS`, `nLr`, `nE`, `bgZ`, `bg5`, `bg10`, `bg20`, `bg12`, `bg16`); **`DF`**; **`stmt_split`**; **`dPend_of`**; **`rejE4_ok`**; **`RejF`**; controls |
| `FRSoundnessFrStab` | 252 / 180 / 34 | **`SameStab q P`** (reads the same under `Same L X L' X X.length` on `X` of at least `q` entries) and its closure lemmas; each part's stability; **`df_ss`**; **`df_stab`** (`FrontObl.hstab`); **`ss_rejF`**; **`frontChainStab`**; controls |
| `FRSoundnessFrObl` | 535 / 457 / 30 | **`frontCls_check`** (the classification), `abs_cls`, `sq_cls`; `nsq_check`/`nsq` (the item shapes the `RejOK`s need); **`rejF_ok`**; the backgrounds' `Reads`; `card_frame2`, `card_or_le`; **`obl_habs`**, **`obl_single`**, **`obl_ms`**, **`obl_hfin`**; **`frontObl`**; controls |
| `FRSoundnessFrK` | 107 / 71 / 4 | **`AccFront`** (`hFront`'s form), **`NodeL`**, `rejF_split`, **`kstate_front_of`**; controls |
| **Total** | 1,261 / 954 / 93 | |

### The statements

```lean
def SLeaf (κ : Kind) (L es : Log) : Prop :=
  ShHoldsL (nbS κ) (zNode κ L es) (sbL κ es) (hbL κ es) ∧ ZHolds zlmFR L es
def okF (oLc : Kind → Log → F → Prop) (κ : Kind) (es : Log) : ℕ → F → Prop  -- 0 oZ | 1 oLc | 2 oSh | _ okE
structure NodeLF (oLc) (RejN L3N PendN : Log → Log → Prop) : Prop where
  rej : RejOK RejN;  rejReads : Reads 98 RejN;  rejLen : ∀ L es, RejN L es → 98 ≤ es.length
  l3Reads : Reads 98 L3N;  pendReads : Reads 99 PendN
  habs : ∀ L es x, es.length = 97 → (kindOf es).isNode = true → D2L zlmFR L es →
    RejN L (es ++ [x]) ∨ L3N L (es ++ [x])
  single : ∀ L es, es.length = 98 → (univ.filter fun a => L3N L es ∧ ¬ PendN L (ext1 es a)).card ≤ 8 * 2 ^ 128
  pend : ∀ L es, PendN L es → ¬ oLc (kindOf es) es (trueL (kindOf es) L es 1)
  okReads : ∀ κ es es', Agree es es' 312 → oLc κ es = oLc κ es'
  leaf : ∀ es v, (kindOf es).isNode = false → (oLc (kindOf es) es v ↔ v = vBetaL es)
structure NodeL (impl vk oLc RejN L3N PendN) : Prop extends NodeLF oLc RejN L3N PendN where
  front : AccFront impl vk RejN
def DF (fin : Finals) (L3N PendN : Log → Log → Prop) : ℕ → Log → Log → Prop   -- journal §3
def RejF (fin) (oLc) (RejN) (L es : Log) : Prop :=
  RejZ zlmFR L es ∨ RejL2 L es ∨ RejLc2 zlmFR L es ∨ RejS2 L es ∨ RejEnd 15 lrOn 169 178 L es ∨
    RejEnd 21 lrOn 209 221 L es ∨ RejInE L es ∨ RejE4 (Layout.nodeRows fin) L es ∨
    RejRS (okF oLc) L es ∨ RejN L es

theorem stmt_split (hfit : RowsFit (Layout.nodeRows fin) 21 23) (h : ¬ Stmt fin SLeaf L es) :
    ¬ ZHolds zlmFR L es ∨ nS L es ∨ nLr L es ∨ nE fin L es ∨ nPub L es
theorem frontChainStab (hN : NodeLF oLc RejN L3N PendN) :
    FrontChainStab (RejF fin oLc RejN) (DF fin L3N PendN)
theorem frontObl (hN : NodeLF oLc RejN L3N PendN) (hfit : RowsFit (Layout.nodeRows fin) 21 23) :
    FrontObl (RejF fin oLc RejN) (DF fin L3N PendN) W₀L c₀L
noncomputable def kstate_front_of (S : Submission) (vk : Digest) (κs₀ : F)
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV) (hE : …W branch…)
    (hI : ExtIface S vk W₀L c₀L (Stmt (finC finPf) SLeaf))
    (hN : NodeL (implC (finC finPf) Layout.lRows κs₀) vk oLc RejN L3N PendN)
    (hfit : RowsFit (Layout.nodeRows (finC finPf)) 21 23)
    (hStart : …) (hW0 : …)                        -- hAcc_of_fin's exact forms
    (hFrontV : AccFront (implC …) vk (RejF (finC finPf) oLc fun _ _ => False)) :
    KState (Rel (S.acc vk)) (S.V vk) S.E epsR
```

### Design

- **`DF`.** `DF 2 = far₀ ∨ ¬ Stmt fin SLeaf`, which is what `hExt_of_iface` takes, by `rfl`.
  - The backgrounds carry the following, in order, until their unit reduces them:
    - `far₀` and `¬PubOK`;
    - the not-yet-reduced statement parts: S's truth until S1, `RowsBad lRows` until Lr1,
      `RowsBad (nodeRows fin)` until E1;
    - the pending claims: `PendZ` from Z3, the leaf's `PendLc` and the node's `PendN` from L3β,
      `D2S` from S2's end, Lr's `BatBad` from Lr3 into E3.
  - At 312, `dPend_of` turns `DF 22` into `DPend (okF oLc)` through the five bridges. Then
    `DF 23 = DRS0`, `DF 24 = msD DRS0 DRS1 312 4`, and `DF 25 = DB`.
  - The multi-squeeze dooms (`DF 3, 11, 13, 17, 24`) are `msD` literally, so `ms` holds by `rfl`.
    The entries the units take as equalities (`DF 10, 12, 16`) are written in the units' `Bg ∨ U`
    form.
- **The classification** (`frontCls_check`) is one `decide +kernel` pass over
  `(fsItems.take 318).zipIdx`. Each absorb is either one of the 15 boundaries `absPts` or a
  rounds-phase absorb of `rndPh`. Each single squeeze is either one of the 6 `sqPts` or a
  rounds-phase squeeze. Each class comes with `phOf (p − 1)` and `phOf p`. `nsq_check` derives the
  "not a squeeze" facts that the `RejOK` lemmas ask for: positions 67, 97, 263, 311 and 312, plus
  69 + 2j, 114 + 2j and 265 + 2j. This includes `fsItems[97]? ≠ squeeze` for `rejLc2_ok`.
- **The single-squeeze counts** are all within 239·2^128:
  - Z2 126, Z3 3, L1 1, L2 2;
  - L3β 7 + 8 (leaf + `NodeL.single`, `card_or_le`);
  - S2 2, Lr2 3, Lr3 2, E2 3, E3 3, E4 2, B′ 10.
- **Stability.** `hstab` and `FrontChainStab` both supply `Same L X L' X X.length`. Every front part
  reads `L` only through `f⁽⁰⁾`, so `df_ss` shows each `DF k` is stable on `X` of at least
  `phStart k + 1` entries. Each check is guarded by its position (`ss_rejF`).

## 2. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`). Logs are `logs/S-G9/time-<module>.log` / `.rss`.

| Module | Wall (import ≈ 4–5 s) | Type checking (≥ 100 ms entries) | Max RSS |
|---|---|---|---|
| `FRSoundnessFrDF` | 10.1 s | < 0.1 s | 2.82 GB |
| `FRSoundnessFrStab` | 7.8 s | 0.11 s | 2.82 GB |
| `FRSoundnessFrObl` | 28.8 s | 11.4 s (6.47 s `frontCls_check`; 1.5 s each for `obl_habs`, `obl_single`, `frontObl`) | 3.37 GB |
| `FRSoundnessFrK` | 7.0 s | < 0.1 s | 2.85 GB |

- **`decide` uses.**
  - `frontCls_check`: the checked classification, `+kernel`.
  - `nsq_check`: `+kernel`, with no `fsItems`.
  - `frontCls_controls`/`frontCls_pos`: four single positions.
  - `phStart_vals`/`ph_vals`: literal phase starts against `fsStarts_eq`.
- **A 15 s `omega` was removed.** It was splitting `fsRanges`' 15-way disjunction; that is now an
  explicit `rcases`.

## 3. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `SLeaf` | `stmt_leaf_iff` (a leaf's statement is exactly `truthS ∧ ZHolds zlmFR`) | `not_stmt_leaf_of` (failing Z rows falsify it) |
| `okF` | `okF_one_iff`, `okF_zero_iff` | `not_okF_three` (claim 4 refuses all but E4 end's value) |
| `NodeLF` / `NodeL` | `nodeLF_ex`, `nodeL_ex` (satisfiable: the interface is not contradictory) | `not_nodeLF_true`, `not_nodeL_true` (a binding accepting everything fails on a leaf) |
| `DF` | `DF_of_far` (a far word dooms phases 2–22 outside the `msD` phases: the background is live) | `not_DF25` (B′'s doom fails on a close word with a true claim) |
| `RejF` | `rejF_of_rejN` | `not_rejF_short` (no verifier check fails on a log shorter than 68) |
| `SameStab` | `ss_controls` | `not_ss_log` (a predicate of the whole log is not stable) |
| `frontCls` | `frontCls_pos`, `frontCls_check` | `frontCls_controls` (67 is no squeeze class, 16 no absorb class) |
| `AccFront` | `accFront_false` | none: a negative control needs an accepted run (completeness, S-I) |

## 4. Deviations and findings

1. **A new hypothesis, `hfit : RowsFit (Layout.nodeRows fin) 21 23`.**
   - **Why it is needed.** `¬ Stmt` on a node contains `¬ truthE fin`. E1's unit consumes
     `RowsBad (nodeRows fin) 21 23 lrOn`. The two are related only through `truthE_iff`, which
     takes `RowsFit`.
   - **Who owns it.** `QUEUE.md` (S-E) lists it as "per-generator row counts for RowsFit (S-G's
     truthE_iff hypothesis)".
   - **What it is.** It is a static fact about the M rows, not a value a final asserts.
   - **What would remove it.** `ExtIface`'s statement could take `RowsBad` instead of `truthE`. That
     would change `StmtN`, so it is not done here.
2. **Claim 2's binding is the parameter `oLc`**, as the task asked.
   - `okF oLc` replaces `okRS oZ oSh` at RS0.
   - `NodeLF.leaf` pins `oLc` to `v = v_β` on a leaf. The leaf's `PendLc` bridge then goes through
     `pendLc_ne`.
   - The existing `okRS`-based bridges are not used. Their `PendBad` hides the claim index, so they
     cannot be transferred to a different binding. They are re-proved from the same lemmas
     (`trueL_zero`, `endS`, `trueL_three`, `zfL_leaf`).
3. **`NodeL` has more fields than S-G8 §5's sketch.**
   - **Added for the chain stability of `RejF`:** `rejReads`, `rejLen`.
   - **Added for RS0's `OkReads`:** `okReads`.
   - **Added for the leaf's claim 2:** `leaf`.
   - **The `front` field covers `¬ RejN` only.** On a node, claim 2's binding at `alphaL 1` sits
     inside `RejRS (okF oLc)`, so it is part of `hFrontV`; §5 discusses this.
4. **`kstate_front_of`, not `kstate_front`.** Item 5 is not discharged. The three run facts are
   named hypotheses in `hAcc_of_fin`'s exact form. `hFrontV` is `AccFront` of `RejF` with
   `RejN := False`; `rejF_split` puts `NodeL.front` back.
5. **`hE` stays a hypothesis.** It is `hAcc_of_fin`'s hypothesis on the extractor's `W` branch.
6. **The verifier is `VC finPf Layout.lRows κs₀`** (`FRVerifierImpl`). `κs₀` stays a parameter, as
   it is there.
7. **No statement of `finalLaw_of`, `hAcc_of_fin`, `kstate_of_front`, `ligerito_final` or
   `ExtIface` was changed.** No existing module was edited.

## 5. Handover: what is left, in order

1. **Item 5a: `hFrontV`.** For each conjunct below, show that an accepted run of
   `implC (finC finPf) Layout.lRows κs₀` gives `¬` that check on the chain `es = fsOf tr items`.
   The route is the strengthened `accept_fields` (`exAt`, `finRS`'s exports) and the register views
   (`coords_view`, `rounds_view`, `peL_node`/`peL_leaf` with `r[l] = coordAt es 2 l`).
   - `RejZ` ← `relZ` (first conjunct).
   - `RejL2` ← `finLc` (i) and L2's round asserts (`chk_of_not_rejL2`'s `Chk2`).
   - `RejLc2` (leaf) ← `finLc` (ii).
   - `RejS2` ← `relSh`'s rounds.
   - `RejEnd` ← `finLr` (ii) and `finE` (ii).
   - `RejInE` ← E4's round asserts.
   - `RejE4` ← `finE` (iv).
   - `RejRS (okF oLc)`, claim by claim, with `rsAlpha = alphaL` (`exec_finRS`, `impl.eqZ = eqZS`):
     - claim 0: `oZ`, from `relZ`'s second conjunct;
     - claim 1: on a leaf, `v = v_β` from `finLc` (iii) and then `NodeLF.leaf`; on a node, INT-5's
       relation;
     - claim 2: `oSh`, from `relSh`'s second conjunct, `claimSL = wSumL · α`;
     - claim 3: `okE`, from `finE` (v).

   **Once INT-5 lands, move the node's claim-1 part into `NodeL`.** It is the node's Lc binding.
   Restate `NodeL.front` as `AccFront … (fun L es => RejN L es ∨ (isNode ∧ 313 ≤ len ∧ ¬ oLc …
   (alphaL … 1)))` and drop it from `hFrontV`.
2. **Item 5b: `hStart`** (S-G5 §5 item 9). It comes from:
   - `relB`;
   - `exec_finRS`'s `rsV` → `vRSL`;
   - `pubH` with `inp.vk = vkL` and the statement bytes `stL`.
3. **Item 5c: `hW0`** (S-G5 §5 item 8). The steps are:
   - `implC_meets` gives `rsWeight = rsWeightS`;
   - `weight_mle` and `eqCellK_eq`/`mleN_w0F` give `wHatL W₀L … 0`.
4. **Item 6: `kstate_front`.** Instantiate `kstate_front_of` with items 5a–5c. What remains is
   `ExtIface`, `NodeL`, `hfit` (S-E), `hE`, and the `implC` facts.
5. **Item 7.** Run the axioms of `kstate_front` and the source rule again.

## 6. Open questions

1. **`hfit` (§4.1).** Should it stay a hypothesis until S-E proves the M rows' fit? The alternative
   is to restate `StmtN`'s E part as `¬ RowsBad`, which changes `ExtIface`'s `St`.
2. **The node's claim-2 front part:** in `NodeL` or in `hFrontV` (§5.1)? This pass keeps it in
   `hFrontV` and `NodeL.front = ¬ RejN`, which is S-G8's sketch.
3. **`FR.lean`:** add `import FRSoundnessFrK`.
