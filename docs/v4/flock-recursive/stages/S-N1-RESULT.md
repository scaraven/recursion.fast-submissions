# S-N1 RESULT: `ExtIface` (the extractor's output is a witness)

- **Base.** Started at HEAD `feca303`. HEAD moved to `aa805c4` (INT-5, S-G10) during the stage.
  The last builds, the axiom run and the final `lake build FR FRSoundnessExtAll` (2,405 jobs) used
  `aa805c4`'s sources: `snap.sh` re-snapshots HEAD on every build. Rechecked:
  `logs/S-N1/build-aa805c4.log`.
- **Build tree.** `logs/fr-build-SN1`, a copy of `fr-build-orch` with its `.lake`; `snap.sh` with
  `MINE` = the six new modules. Nothing was rebuilt from scratch.
- **Logs.** `logs/S-N1/`. The journal is `S-N1-JOURNAL.md`; its §1 is the plan table, item 1.
- **Constraints.** Every lean/lake command ran under the 16 GB scope and a `timeout`. No
  sub-agents. Nothing committed. No existing module was edited: no `FRVIR*`, `FRVerifierImpl*`,
  `FRSoundnessFr*`, `FRX*`, `BLUEPRINT.md`, `FR.lean`, and no repair in `FRNodeCircuit`. No
  statement of `node_sound`, `leaf_sound`, `ExtIface`, `E_node` or `kstate_front_of` was changed.

## Status

**`ExtIface` as stated is not provable, for any `St` (finding O0, §2).** Its hypotheses never tie
the chain `j` to the proof `π`. In its place this stage builds:

- the linked interface **`ExtIfaceR`**;
- the route that keeps the link, **`kstate_front_ofR`**, from S-G's own lemmas;
- **`extIfaceR_of`**: `ExtIfaceR` for `St := Stmt (finC finPf) SLeaf`, with one hypothesis left,
  the node circuit's residual `hRes`;
- **`kstate_front_ofE`**: `kstate_front_of`'s hypotheses with `ExtIface` replaced by `hRes`, plus
  `hOut` for logs outside the extractor's domain (O3).

| Item | State |
|---|---|
| 1. Plan table | **Done.** Journal §1. |
| 2. H-side assembly | **Partly done.** Done: the format facts (`readSigned_fmt`, including every query `≤ queryCap`); the `W`-kind children excluded (`child_kind`); `PubCells` binds the children's statements (`readStmt_of_pubCells`). Not done: the pack map and the `input w` alias are compiler changes in `FRVIR*`, L-circ's modules. `SigOk` has no rows (O2b). |
| 3. Truths → `node_sound`'s hypotheses | **Partly done.** Done: `PubOK → PubCells` (`pubCells_of_pubOK`); `truthLr → SlotHolds.bits` (`selBits_of_lRows`). `truthZN` and `truthS1N` are per-block `HoldsE` and `ShHoldsN` by definition. **Blocked: `truthE` → `SlotHolds.rows/trows/run`** (O1, O2). |
| 4. `accWith` for both children | **Done modulo the residual.** `rel_readWit`: `PubCells` + `c = nodeStmt c₁ c₂` + the L rows + `NodeResid` give `Rel (accV …) c (readWit w)` through `node_sound`. |
| 5. The leaf case, then `W` | **Done.** `rel_leaf_of_run`: `SLeaf` on the run's chain plus the run's statement check make `E_leaf`'s witness valid. `W` and `bad` are covered by `hAcc_of_finR` (S-G's `acc_W`, `not_acc_bad`). |
| 6. `extIface_holds` | **Replaced** by `extIfaceR_of` (O0). Its only hypothesis besides `hV`, `hq`, `hE : S.E = X.E` and `ImplT` is `hRes`. **Every `E_node` chain link is proved** from the run (`E_node_of_run`, §3). `hfit` is not needed. |
| 7. `node_complete` | **Not started** (it needs the same circuit pieces as O1/O2). |

**Checks:**
- **Build.** `lake build FR FRSoundnessExtAll` is green: 2,405 jobs, 18.8 s, no `sorry`
  (`logs/S-N1/build-final.log`).
- **Axioms** (`logs/S-N1/axioms.log`). All 77 new declarations use only standard axioms: 57 use
  `[propext, Classical.choice, Quot.sound]`, 10 `[propext, Quot.sound]`, 10 `[propext]`.
- **Source rule** (`logs/S-N1/source-rule.log`): 181 files, 0 findings.
- **Names.** All 77 new names were grepped against every `FR*.lean`, the worktree's in-progress
  files included. The one clash, `find_of_mem` with S-G's `FRSoundnessAccQry`, was renamed
  `findSnd_of_mem`, which uses S-G's.

**Imports for `FR.lean`.** Add `import FRSoundnessExtAll`. It pulls in all of `FRSoundnessExtR`,
`FRSoundnessExtStmt`, `FRSoundnessExtLinks`, `FRNodeSoundA` and `FRSoundnessExtLeaf`.

## 1. What was built (code lines by `scripts/loc.py`, `logs/S-N1/loc.log`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundnessExtR` | 221 / 163 / 8 | `RunLink`, `InDom`, **`ExtIfaceR`**, `extIfaceR_of_iface`; **`hAcc_of_finR`**, **`finalLaw_ofR`**, **`hExt_of_ifaceR`**, **`kstate_front_ofR`**; controls |
| `FRSoundnessExtStmt` | 136 / 89 / 11 | **`stmt_view`** (the run's `stmtOk` flag); `stLog_eq`, `seed_query`, `seed_byte`, `seed_bytesAt`, `kindOf_chain`; **`c_node_of_run`**, **`vkOf_of_run`** |
| `FRSoundnessExtLinks` | 108 / 70 / 7 | `findSnd_of_mem`, **`fmAns_of_run`**, `cap0_of_run`, `capL_of_run`, `final_of_run`, `fF_N30`, **`E_node_of_run`** |
| `FRNodeSoundA` | 270 / 181 / 22 | `toListLE_eq_ofFn`, `enc64_toListLE`, `wordBytes_ofBytes`, `wordsBytes_elemWords`, **`digestOf_halves`**; `pubCells_vals`, **`readStmt_of_pubCells`**, `pubCells_of_pubOK`; `shapeQ`, `shape_qlen`, `phases_shapeQ`, **`items_qlen_le`**, `readItems_qlen`, **`readSigned_fmt`**; `selBits_of_lRows`, `kindOf_of_byte`, **`SlotRest`**, `slotHolds_of`, **`child_kind`**; **`NodeResid`**, **`rel_readWit`**; controls |
| `FRSoundnessExtLeaf` | 219 / 157 / 18 | `testBit_ofListLE`, `getLsbD_ofBytes`, `bitF_ofBytes`, `bytesAt_toList_getD`, `digestBit_bytesAt`, **`digBit_readF`**; `zBlk_pos`, `sbL_leaf`, `hbL_leaf`, **`chainLinks_of_shHoldsL`**, `chainEnd_of_sLeaf`; `extract_getD`, `sum_enc64`, **`c_leaf_of_run`**, **`rel_leaf_of_run`**; controls |
| `FRSoundnessExtAll` | 119 / 81 / 3 | `vkL_of_chain`, **`extIfaceR_of`**, **`kstate_front_ofE`**; control |
| **Total** | 1,073 / 741 / 69 | |

### The main statements

```lean
def RunLink (impl) (fin) (vk c : Digest) (π : Proof) (L : Log) (j : ℕ) : Prop :=
  ∃ k tr, FR.kindOf π = .snark k ∧ semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true ∧
    (∀ e ∈ tr, e ∈ L) ∧ entriesOf L (pathOf L j) = fsOf tr items
def InDom (c π L) : Prop := (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64
def ExtIfaceR impl fin S vk W₀ c₀ St : Prop :=      -- ExtIface's hypotheses, plus:
  ∀ L c π j, … → RunLink impl fin vk c π L j → InDom c π L → … → ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w

structure NodeResid (impl fin vk) (w : Asg) : Prop where     -- the node circuit's residual
  slot₁ : SlotRest impl fin 0 w ⟨vk, readStmt w 1, (readSigned 1 w).π⟩ (readSigned 1 w).tr
  slot₂ : SlotRest impl fin 1 w ⟨vk, readStmt w 2, (readSigned 2 w).π⟩ (readSigned 2 w).tr
  sig₁  : SigOk vk (traceDigest (readSigned 1 w).tr) (readSigned 1 w).σ = true
  sig₂  : SigOk vk (traceDigest (readSigned 2 w).tr) (readSigned 2 w).σ = true
-- SlotRest = SlotHolds without `bits`: oneHot, rows, trows, run (field for field)

theorem extIfaceR_of (hV : S.V = Vwith impl (sfFinals finP finPf)) (hq : S.qV = qV)
    (hE : S.E = X.E) (hT : Circ.ImplT impl)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es → NodeResid impl (sfFinals finP finPf) (vkL es) (fF .N30 L es)) :
    ExtIfaceR impl (sfFinals finP finPf) S vk W₀ c₀ (Stmt (finC finPf) SLeaf)

noncomputable def kstate_front_ofE (S vk κs₀) (hV : S.V = VC finPf Layout.lRows κs₀) (hq) (hE : S.E = X.E)
    (hRes : …) (hOut : ∀ L c π, L.length ≤ logCap → ¬ Bad L → runLog = some true → ¬ InDom c π L → ∃ w, …)
    (hN : NodeL …) (hfit : RowsFit …) (hStart …) (hW0 …) (hFrontV …) :
    KState (Rel (S.acc vk)) (S.V vk) S.E epsR

theorem rel_readWit (hT : ImplT impl) (hp : PubCells w vk c₁ c₂) (hc : c = nodeStmt c₁ c₂)
    (hLr : ∀ r ∈ Layout.lRows, r.Holds w) (hR : NodeResid impl fin vk w) : Rel (accV impl fin vk) c (readWit w)
theorem rel_leaf_of_run (hk : k.isNode = false) (hkπ : FR.kindOf π = .snark k) (h : SkRun impl k ⟨vk, c, π⟩ tr y)
    (acc) (hS : SLeaf k L (fsOf tr items)) : Rel acc c (.leaf (bytesAt π 16 32) (leafN k))
theorem E_node_of_run (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hk : FR.kindOf π = .snark .N30) (hD : InDom c π L) (hLig : LigeritoOut W₀ c₀ L (fsOf tr items)) :
    X.E c π L = some (FR.readWit (fF .N30 L (fsOf tr items)))
theorem stmt_view (h : SkRun impl κ inp tr y) :
    stmtDigest κ (FR.msgAt inp fStmt 0 128) = inp.c ∧ (κ.isNode = false → n-bytes = enc64 (leafN κ)) ∧
      (κ.isNode = true → bytesAt inp.π (absOff fHdr 16) 32 = inp.vk)
```

## 2. Findings: statements that are wrong or gaps that cannot be proved

### O0. `ExtIface` does not tie `j` to `π`, so it is false for any `St`

**The gap.** `ExtIface`'s hypotheses mention `π` only in `(S.V vk c π).runLog L = some true`. The
chain `j` is any chain of `L`, and `St`, `¬ far₀`, the length and `LigeritoOut` are facts about
that chain alone.

**Counterexample (an argument, not kernel-checked).** Take `L = L₂ ++ L₁`:
- `L₁` is a log on which `V` accepts a proof `π` of a statement `c` that has no witness. Such a
  log is a Fiat–Shamir forgery whose answers are picked so that every check passes. For example,
  a sumcheck round can send `g = h + δ(X − r₀)` with the next answer mapping to `r₀`. Such logs
  exist because the verifier's soundness error is not zero.
- `L₂` is an honest prover's run on another statement `c'`. Its chain `j` meets `St`, `¬ far₀`,
  `pfStart + 14 ≤ |es|` and `LigeritoOut`.

With `¬ Bad (L₂ ++ L₁)`, `ExtIface` would give a witness for `c`, and none exists. No choice of
`St` repairs this, because `St` reads only `(L, es)` and never sees `π`.

**The cause is upstream.**
- `hAcc_of`/`hAcc_of_fin` build `AcceptTail L j` from `runLog_chain`'s `j`. That `j` comes with
  `semIR … tr = some true`, `∀ e ∈ tr, e ∈ L` and `entriesOf L (pathOf L j) = fsOf tr items`.
- `finalLaw_of`'s `hAcc` returns only `∃ j, AcceptTail …`, so those facts are lost.
- `hExt`/`ExtIface` then quantify over every `j`.

**The repair, in new modules.** `RunLink` carries those facts. `hAcc_of_finR`, `finalLaw_ofR`,
`hExt_of_ifaceR` and `kstate_front_ofR` are S-G's proofs, copied and kept linked.
`kstate_front_ofR` has `kstate_front_of`'s hypotheses with `ExtIfaceR` in place of `ExtIface`, plus
`hOut` (O3). `extIfaceR_of_iface` shows the new interface asks less than the old one.

### O1. `truthE` reads the untemplated circuit; `SlotHolds` and `evalM` read the templated one

- `truthE fin` is "every row of `Layout.nodeRows fin` holds". Those rows are
  `(slotCS fin σ).rowList` with `slotCS = compileMux … (gen fin .mux).ops`, which is `compile`
  **without templates**.
- `SlotHolds.rows/trows` read `TEval.slotCST fin σ` (`compileT (slotLay …)`, with templates) and
  its `tplRows`.
- The deployed `evalM` is `evalMS (planOf fin)`, the MLE of `nodeIRows`, built from `compileT`'s
  indexed rows (`Plan.ok`).

These are different row lists, with different cells for every templated op's outputs. So `truthE`
does not give `SlotHolds.rows`. S-G's E-phase dooms (`nE`, `RejE4 (nodeRows fin)`) are about a
circuit the verifier does not evaluate. The run fact `¬ RejE4 (nodeRows fin)` in `hFrontV` would
need `evalM = MLE(nodeRows)`, which `implC` does not satisfy (`evalMT_eq` is against
`nodeIRows`). **Proposed:** S-G restates `truthE`/`nE`/`RejE4` over `nodeIRows (planOf fin)`, the
indexed templated rows, and `RowsFit` (`hfit`) over the same list.

### O2. `SlotHolds.run`'s import hypotheses have no rows

`SlotHolds.run` *assumes*, at the selected kind:
- the run exists and uses up its trace;
- every auxiliary import holds;
- every import register's cells hold their values (`RepS`);
- every foreign flag holds.

No row forces these. The import registers (S-E6 §6, S-E9 §4) include:
- the trace cells (no pack map);
- the outputs of `rsWeight`, `shiftTarget`, 745 `tensorW`, `targetS`, `linkW`, `evalL`, and the
  child `evalM` (no replay `R`).

A prover can write any value into such a cell and every row still holds. For example, it can put
the child's claimed `evalM` value there instead of the matrix MLE. The child's real verifier then
rejects while `StmtN` holds. So `StmtN → SlotRest` is not provable with the current circuit.

**O2b.** No row list contains the WOTS selector mux, the digit rows or the mirror sources. `SigOk`
of a read child is therefore not a consequence of `StmtN` either.

Both are the residual `NodeResid`, the one hypothesis `hRes` of `extIfaceR_of`.

### O3. The extractor's domain

`E_leaf` and `E_node` need `∀ e ∈ L, |q| < 2^64` and a tape of at most `2^64` words (contract
`Computes`). `FinalLaw` covers `L.length ≤ logCap = 2^96`, so it reaches logs outside that domain.
The contract allows `E` to be a choice outside the domain, but the entry's `X.E` is the program
everywhere, and nothing is known of it there.

`ExtIfaceR` takes `InDom` as a hypothesis, and `kstate_front_ofE` takes the out-of-domain case as
`hOut`. **For the orchestrator:** define `S.E := if InDom c π L then X.E c π L else Eₛ c π L`, where
`Eₛ` is the non-computable decoded witness: `readWit (fF .N30 L es)` on a node, the leaf witness
on a leaf, `decode π` on `W`, with `es` the chain of first matches from `(vk, c, π)`.
`Computes` still holds, since it constrains only the domain. `hOut` then follows from the same
argument, because `rel_readWit` and `rel_leaf_of_run` do not use `InDom`; only `E_leaf`/`E_node`
do. Two caveats: this needs O0's link for long logs too, and `E` takes no `vk`, so `es` must be
found from `(c, π, L)` alone. On a node `π`'s `hdr.pub` is `vk` (`vkOf_of_run`); a leaf needs
none. Not done here.

## 3. `E_node`'s chain links (item 6): all proved from the run

| link | lemma | source |
|---|---|---|
| `fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)`, `p < nRep` | `fmAns_of_run` | `SkRun.hq`; no repeated query (`¬ Bad`, S-G's `find_of_mem`); `vkOf π = vk` (`vkOf_of_run`, the node's `hdr.pub = vk` flag) |
| `capDig es 0 e = capPi π e`, `capDig es i e = capPiL i π e` | `cap0_of_run`, `capL_of_run` | S-G's `capDig_eq`, `capOff_abs` |
| `finalAt es x = finPi π x` | `final_of_run` | S-G's `finalAt_fsQ` |
| `¬ StateHit L` | in `E_node_of_run` | `¬ Bad L` |
| `¬ farL .N30 L es i`, `consSet = jointAgree` | in `E_node_of_run` | `LigeritoOut.close`, `.agree`, with `kindOf es = N30` (`kindOf_chain`) |

All of these need `es` to be the run's chain, which is O0's `RunLink`.

## 4. Build and kernel times

Sequential profiles: `taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`, under `/usr/bin/time -v`. Logs: `logs/S-N1/time-<module>.{log,rss}`.

| Module | Wall (import ≈ 5 s) | Entries ≥ 100 ms | Max RSS |
|---|---|---|---|
| `FRSoundnessExtR` | 6.8 s | none | 2.89 GB |
| `FRSoundnessExtStmt` | 7.9 s | one `simp`, 0.69 s | 2.90 GB |
| `FRSoundnessExtLinks` | 7.1 s | type checking 0.17 s ×2, `rfl` 0.16–0.18 s | 2.92 GB |
| `FRNodeSoundA` | 7.3 s | none | 2.90 GB |
| `FRSoundnessExtLeaf` | 7.9 s | none | 2.90 GB |
| `FRSoundnessExtAll` | 6.3 s | none | 2.89 GB |

**`decide` uses.**
- `phases_shapeQ` is `+kernel` over the 52 phases' shape parameters (`shapeQ`), not over the
  8,891-item list. It is below 100 ms.
- `testBit_ofListLE_ctl`, `sum_enc64` (the two leaf lengths, 8 bytes each) and `sum_enc64_neg`
  are small closed terms.
- A general `sum_enc64` (`n < 2^64`, `omega`) caused a kernel deep recursion and was restated for
  the two lengths.

## 5. Controls

| Definition | Positive | Negative |
|---|---|---|
| `RunLink` | used by `hAcc_of_finR` (built from `runLog_chain`) | `not_runLink_W` (a `W` proof has no link) |
| `InDom` | `inDom_nil` | `not_inDom_of_big` (a query of `2^64` bytes is outside) |
| `ExtIfaceR` | `extIfaceR_false`, `extIfaceR_of_iface` | none kernel-checked: it needs an accepted run (S-I) |
| `SlotRest` / `NodeResid` | (they are `node_sound`'s hypotheses; `slotHolds_of` reconstructs `SlotHolds`) | `not_slotRest_zero` (all selectors 0 with `one = 1` fails the one-hot rows) |
| `shapeQ` / `items_qlen_le` | `phases_shapeQ`, `shapeQ_ctl` (seed 119) | `shapeQ_ctl` (an absorb of `queryCap` bytes exceeds the cap) |
| `digestOf_halves` | `digestOf_ctl` (any digest's halves read back) | `readStmt_not_vk` (slot 1 reads `c₁`'s cells, not `vk`'s) |
| `testBit_ofListLE` / `digBit_readF` | `testBit_ofListLE_ctl` (bit 0 of byte 0; bit 8 is byte 1's bit 0) | `testBit_ofListLE_ctl` (bit 8 of `[1,0]` is false), `sum_enc64_neg` (big-endian order fails) |
| `hRes` (as `kstate_front_ofE`'s hypothesis) | `hRes_vacuous` (vacuous on a chain whose `PubOK` fails) | — |

## 6. Deviations

1. **`extIface_holds` is `extIfaceR_of`** (O0). `ExtIface` is false as stated, so it was not
   targeted. `kstate_front_ofR`/`kstate_front_ofE` replace `kstate_front_of`'s use of it. The
   copied proofs are S-G's, with the link kept and the statements otherwise identical.
2. **`hfit` is not a hypothesis** of `extIfaceR_of`. The node case never goes through `truthE`
   (O1).
3. **The residual is one named hypothesis, `hRes`**, not a lemma, because of O1, O2 and O2b.
   `NodeResid` is stated field for field from `SlotHolds` (minus `bits`, which is proved) and
   `accWith`'s `SigOk`.
4. **`kindOf_chain`** duplicates S-G's `kindOf_fsQ`, which I found afterwards. It is harmless and
   can be dropped in a golf.
5. **The pack map and the `input w` alias** (S-E3 §9) are changes to `FRVIRCompile`. They belong
   to L-circ and are not done. With O1/O2 fixed they would discharge `SlotRest.run`'s trace and
   public imports.

## 7. Open questions (for the orchestrator)

1. **O0.** Adopt `RunLink`/`ExtIfaceR` and the linked route (`kstate_front_ofR`), or restate
   `AcceptTail`/`finalLaw_of` in S-G's modules so that `hAcc` keeps the link?
2. **O1.** Restate S-G's E truth (`truthE`, `nE`, `RejE4`, `hfit`) over the templated indexed rows
   `nodeIRows (planOf fin)`, which `evalM` evaluates?
3. **O2/O2b.** The circuit needs rows for every import register that `SlotHolds.run` assumes: the
   pack map for trace cells, templates or the replay `R` for the structured ops, and the WOTS
   mux and digit rows. Until then `hRes` stays a hypothesis. Which track owns `StmtN → NodeResid`?
4. **O3.** Rule `S.E` outside `InDom` (a choice branch), and with it `hOut`.
5. **`FR.lean`:** add `import FRSoundnessExtAll`.
