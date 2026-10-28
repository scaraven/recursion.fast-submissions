# S-N1 JOURNAL: `ExtIface` (the extractor's output is a witness)

Base: HEAD `feca303`. Build tree `logs/fr-build-SN1` (a copy of `fr-build-orch` with its `.lake`;
`snap.sh` with `MINE` = my modules). Logs in `logs/S-N1/`.

## 0. Setup

- `cp -a fr-build-orch/{.lake,src,…} fr-build-SN1/`; `MINE="" ./snap.sh`; `lake build FRSoundnessFrK
  FRXNodeRun FRNodeCircuit FRNodeReadP FRVerifierImpl`: 2,388 jobs, nothing rebuilt (3 s,
  `logs/S-N1/build0.log`).
- `FRSoundnessFrRun` (S-G10, in progress) is **not** in HEAD; not imported. Its `stL_fsQ`,
  `vkL_fsQ`, `msgAt_abs` would be useful; I re-derive what I need under other names.

## 1. Plan table (item 1)

`ExtIface S vk W₀ c₀ St` asks, for every `L c π j` with `L.length ≤ logCap`, `¬ Bad L`,
`runLog = some true`, `IsChain L j`, `pfStart + 14 ≤ |es|`, `¬ far₀`, `St L es`, `LigeritoOut`:
`∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w`, where `es = entriesOf L (pathOf L j)`.

Conclusion, case by case (`FR.kindOf π`):

| case | conclusion's conjunct | lemma that gives it | gap |
|---|---|---|---|
| `W` | `E = decode π`, `Rel` | `acc_W` (S-G) with `hE` | none |
| `bad` | (vacuous) | `not_acc_bad` | none |
| `snark k`, any | the chain `j` is the run's chain | **nothing**: `ExtIface` has no hypothesis linking `j` to `(c, π)`; `runLog_chain` gives *some* `j₀` | **O0 (statement)** |
| `snark k`, any | `E`'s domain (`∀ e ∈ L, |q| < 2^64`, tape `≤ 2^64` words) for `E_leaf`/`E_node` | nothing: `L.length ≤ logCap = 2^96` | **O3 (statement / `S.E`)** |
| `snark k`, `k ≠ N30` | `E = some (.leaf (bytesAt π 16 32) (leafN k))` | `E_leaf` | domain (O3) |
| leaf | `leafN k ≤ chainCap` | arithmetic (`k.m ≤ 32`) | none |
| leaf | `c = leafStmt (chainEnd s n) n` | the run's `stmtOk` flag (`refPhase` phase 1) gives `c = leafStmt h n`, `h = stmt[1..33)`; `SLeaf` = `ShHoldsL ∧ ZHolds` → `zHolds_iff_truthZ` → `leaf_of_truthZ` gives `chainEnd s' n = h'` with `s'`, `h'` the log's `bndL` digests | the link `es` = run's chain (O0); the bit bridge `digBit (readF ·) = digestBit` |
| `snark N30` | `E = some (readWit w)`, `w = fF .N30 L es` | `E_node` | its chain links (below), domain (O3) |
| node | `c = nodeStmt (readStmt w 1) (readStmt w 2)` | `stmtOk` flag: `c = nodeStmt (stL es 0) (stL es 1)`; `PubOK` → `PubCells` → `readStmt w (σ+1) = stL es σ` | link (O0) |
| node | `acc c_σ p_σ` format: `|π| ≤ proofCap`, `|tr| ≤ qV`, `|q| ≤ queryCap` | `reassemble_size`, `readTrace_length`, a qlen bound | qlen bound per item (structural) |
| node | `SigOk vk (traceDigest tr_σ) sig_σ` | blueprint: `blake2s_chain` (Z + Sh chain part) + `wots_sound` (WOTS blocks, `FamPartN`, digit rows) + `readTrace_of_stream` | digit rows and length asserts live in M rows read through **imports** (O2) |
| node | `runSeq tr_σ = some true` | `node_sound` ← `SlotHolds` ← `truthE`, `truthLr`, imports | **O1** (`truthE` reads `nodeRows` = untemplated `compileMux`; `SlotHolds` reads `slotCST` = `compileT` + template rows); **O2** (`SlotHolds.run`'s import hypotheses have no rows) |
| node | children are SNARKs (not `W`) | `SlotHolds.run`: `π.data[0]? = κ.byte`; `|π| = piSize` | as above (part of `run`) |

E_node's chain links and their sources (item 6):

| link | source |
|---|---|
| `fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p)`, `p < nRep` | `runLog_chain` + `¬ Bad` (no repeated query: the first match is the chain's entry) + `vkOf π = vk` (`stmtOk`'s node clause `hdr.pub = vk`) — **only if `es` is the run's chain (O0)** |
| `capDig es i = capPiL i π`, `capDig es 0 = capPi π`, `finalAt es x = finPi π x` | the absorbs' messages are π's bytes (`fsQ`'s chain: `msgAt_fsQ`), again on the run's chain |
| `¬ StateHit L` | `¬ Bad L` |
| `¬ farL .N30 L es i` (`i < 5`) | `LigeritoOut.close` |
| `consSet = jointAgree` | `LigeritoOut.agree` |

## 2. Findings before any code

### O0. `ExtIface` does not tie the chain `j` to `(c, π)` (statement too strong)

`ExtIface`'s hypotheses mention `π` only in `(S.V vk c π).runLog L = some true`; `j` is any chain
of `L`. Take `L = L₂ ++ L₁` where `L₁` is an accepted run of a proof `π` whose statement `c` has no
witness (a Fiat–Shamir forgery: answers chosen so every check passes; such logs exist because the
verifier's soundness error is nonzero, e.g. a sumcheck round `g = h + δ(X − r₀)` with the answer
mapping to `r₀`), and `L₂` an honest prover's run on another statement `c'`, whose chain `j`
satisfies `St`, `¬ far₀`, `pfStart + 14 ≤ |es|` and `LigeritoOut`. With `¬ Bad (L₂ ++ L₁)`,
`ExtIface` gives a witness for `c`, which does not exist. So `ExtIface` holds for no sound-but-not-
perfectly-sound verifier, and no `St` on `es` alone can repair it (`St` does not see `π`).

Upstream cause: `hAcc_of`/`hAcc_of_fin` build `AcceptTail L j` from `runLog_chain`'s `j`, together
with the link `entriesOf L (pathOf L j) = fsOf tr items` (and `semIR … tr = some true`,
`∀ e ∈ tr, e ∈ L`), but `finalLaw_of`'s `hAcc` returns only `∃ j, AcceptTail …`: the link is
dropped, and `hExt`/`ExtIface` quantify over every `j`.

Repair (done here, in new modules, without editing S-G's): `RunLink` (the dropped facts),
`ExtIfaceR` (`ExtIface` with `RunLink`), `hAcc_of_finR`, `finalLaw_ofR`, `hExt_of_ifaceR`,
`kstate_front_ofR` (same hypotheses as `kstate_front_of`, `ExtIfaceR` for `ExtIface`).

### O3. `E`'s domain

`E_leaf`/`E_node` need `∀ e ∈ L, e.1.size < 2^64` and `(extractorInput c π L).length ≤ 2^64`
(`Computes`' domain, contract `Extractor.lean`). `FinalLaw` covers `L.length ≤ logCap = 2^96`, so a
log of `2^62` entries is in `FinalLaw`'s range and outside `E`'s domain. The contract says that
outside the domain `E` is unconstrained "and may be a non-constructive choice"; the entry's
`X.E = Eof ext fuel` is the program everywhere, so nothing is known about it there. `ExtIfaceR`
therefore takes the domain as a hypothesis (`InDom`), and `kstate_front_ofR` takes the
out-of-domain case as a separate named hypothesis `hOut` (for the orchestrator: `S.E` should be
`if InDom then X.E else choice`, which `Computes` allows).

### O1, O2 (the node's circuit)

- **O1.** `truthE fin` = every row of `Layout.nodeRows fin` = `(slotCS fin σ).rowList`, `slotCS =
  compileMux … (gen fin .mux).ops` (`compile`, **no templates**). The deployed circuit is
  `compileT` with templates: `SlotHolds.rows/trows` read `TEval.slotCST fin σ` (`compileT (slotLay
  …)`) and its `tplRows`; the verifier's `evalM` is `evalMS (planOf fin)` = the MLE of
  `nodeIRows (planOf fin)`, built from `compileT`'s indexed rows (`Plan.ok`). Different row lists,
  different cell numbering for every templated op's outputs. S-G's E-phase (`nE`, `RowsBad
  (nodeRows fin)`, `RejE4 (nodeRows fin)`) is therefore stated for the untemplated circuit, while
  the verifier evaluates the templated one: the run fact `¬ RejE4 (nodeRows fin)` (in `hFrontV`)
  would need `evalM impl = MLE(nodeRows)`, which is not `implC`'s `evalMT_eq`.
- **O2.** `SlotHolds.run` *assumes* at the selected kind: the run exists and consumes its trace,
  every auxiliary import, every import register's cells (`RepS`), every foreign flag. These are not
  consequences of any row: per S-E6 §6 and S-E9 §4 the import registers include the trace cells
  (the pack map is not built), and the outputs of `walkAB`'s replay, `rsWeight`, `shiftTarget`,
  745 `tensorW`, `targetS`, `linkW`, `evalM`, `evalL` (no template or replay `R`). A prover writes
  any value into such a cell and every row still holds; e.g. the child's `evalM` claim can be the
  claimed value instead of the matrix MLE, so the child's real verifier rejects while `StmtN`
  holds. So `StmtN` → `SlotHolds` is not provable with the current circuit.

## 3. Work log

1. **`FRSoundnessExtR`** (the repaired route). `RunLink`, `InDom`, `ExtIfaceR`,
   `extIfaceR_of_iface` (ExtIface → ExtIfaceR), `hAcc_of_finR` (copy of `hAcc_of_fin`'s proof,
   keeping `k, tr, hk, hsem, hin, hes`), `finalLaw_ofR` (copy of `finalLaw_of`, split on `InDom`),
   `hExt_of_ifaceR`, `kstate_front_ofR`. Built first try except a control (`by cases he, ?_`
   parsed as a two-target `cases`).
2. **`FRSoundnessExtStmt`**. `stmt_view` from `phase_at 1` and `refPhase`'s `fStmt` flag
   (`simp only [↓reduceIte, Bool.and_eq_true, …]` after the `rfl` substitution).
   `stLog_eq`, `seed_query`, `seed_byte`, `seed_bytesAt`, `kindOf_chain` (duplicates S-G's
   `kindOf_fsQ`, which I found later), `c_node_of_run`, `vkOf_of_run`. Pitfall: `FR.msgAt`
   (input) vs `FR.Snd.msgAt` (log) — write `FR.msgAt` explicitly. `seedQ` is `FR.seedQ`, not
   `X.seedQ`.
3. **`FRSoundnessExtLinks`**. Every `E_node` link from `SkRun`: `fmAns_of_run` (induction on `p`,
   S-G's `find_of_mem`; my first helper of that name clashed — renamed `findSnd_of_mem`, lesson:
   grep before naming), `cap0_of_run`, `capL_of_run` (S-G's `capDig_eq`, `capOff_abs`),
   `final_of_run` (`finalAt_fsQ`), `fF_N30`, `E_node_of_run`.
4. **`FRNodeSoundA`**. `digestOf_halves` through `toListLE_eq_ofFn`/`enc64_toListLE`/
   `wordBytes_ofBytes` (B64's `toBytes_ofBytes` + `toBytes_toList`); `pubCells_vals` (one
   `simp only` over the 9-element lists), `readStmt_of_pubCells`; `items_qlen_le` via `shapeQ`
   per shape and one `decide +kernel` over the **52 phases' shape parameters** (not the item
   list; below 100 ms); `readSigned_fmt`; `selBits_of_lRows`; `child_kind`; `SlotRest`,
   `NodeResid`, `rel_readWit`.
5. **`FRSoundnessExtLeaf`**. `testBit_ofListLE` (`Nat.testBit_two_pow_mul_add`),
   `bitF_ofBytes`, `digBit_readF`; first attempt unfolded `Impl.digBit`/`readF` together and hit
   a `whnf` timeout — fixed by rewriting with `digestBit_bytesAt` first and `rw [Impl.digBit]`;
   `chainLinks_of_shHoldsL`, `chainEnd_of_sLeaf`; `sum_enc64` with a general `n < 2^64` and
   `omega` gave a **kernel deep recursion**: restated for the two leaf lengths and closed by
   `decide` (8 bytes); `c_leaf_of_run`, `rel_leaf_of_run`.
6. **`FRSoundnessExtAll`**. `vkL_of_chain`, `extIfaceR_of`, `kstate_front_ofE`.
7. Checks: axioms (77 declarations), source rule (181 files, 0), names (77, no clash), sequential
   profiles, final build `lake build FR FRSoundnessExtAll` (2,405 jobs).

## 4. More findings

- **O2b (SigOk).** No row list of the node contains the WOTS selector mux, the digit rows or the
  mirror cells' sources (grep: only `FRWots` and `FRNodeCircuit`'s docstring mention them);
  `nodeRows` is the verifier program's compile and `lRows` is Booleanity only. So `SigOk` of a read
  child is not a consequence of `StmtN` either: it is in `NodeResid`.
- The H-side digest (`blake2s_chain` over the chain blocks, `ChainPartN`) gives the chain's last
  `h_out`; equating it with `traceDigest (readTrace w σ)` needs `readTrace_of_stream`, whose
  hypothesis (the length words are `enc64 qlen`) is asserted by M rows over import cells (O2).
