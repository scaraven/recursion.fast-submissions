# X4 RESULT (pass 1): revision 4.1's knowledge soundness composed, every gap a named hypothesis

- **Base.** HEAD `bb5d352` (R4g). **Build tree** `logs/fr-build-X4` (a copy of `fr-build-R4g`;
  `b.sh` logs to `logs/X4/`; `MINE.txt` lists the four new modules). Journal: `X4-JOURNAL.md`.
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under
  `timeout`. No sub-agents. Nothing committed. Only new `FRSoundness4X*` modules written; no existing
  module edited, no statement changed. Every new short name was grepped first (`srcL4`/`srcE4` exist in
  `NI4F`, so none of mine reuse them).
- **R4h** had not committed: its fields (`FinRest4.pf0`, `.enc`, `.fin`) sit inside the residual
  `RunFacts4` (below).

**Imports for `FR.lean`:** add `import FRSoundness4XCtrl` (it pulls `XFinal` → `XLaws` → `XFront`).

## Status

| Item | State |
|---|---|
| 1. The composed `FrontObl` at `seq4` | **Done for phases 0 … 12 and every cross-cutting field**: `frontObl_X : FrontHi DFhi → T4.FrontObl RejFX (DFX DFhi) W0X c0X`, `frontChainStab_X`. `loc`, `rej`, and `ms`/`habs`/`hsingle`/`hfin`/`hstab` below 170 come from existing lemmas. **Phases 13 … 25 are the residual `FrontHi`**: P4b's handover item 2 (their dooms and `FrontObl` obligations) was never run, so no lemma exists to discharge them (§4). `BgA`/`NodeRest4` (P4e's open point): **done** (`bgA4_cover`). |
| 2. The segment law | **Done from the residuals**: `segSound_X : FrontHi DFhi → RunFacts4 … → SegSoundLog Vseg vk (GoodX DFhi)` (`chainEnd_of_truths` on the three-entry prefix). |
| 3. The node law | **Done from the residuals**: `nodeRun_X` (the per-run `StmtN4` that `nodeLaws4C'` asks) and `nodeSound_X` (`NodeSoundLog` through `nodeLaws4C'`); `NodeExtLog` at `E4X` through S-H3's `ks4_E4X` with the links `hL`. |
| 4. `ks_rev4` | **Done**: `KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV` at `S.V = VC4 impl₀ (implN4F base) cells4`, `S.E = E4X nd S.acc`, `S.ε = εR`. Hypotheses: the definitional ones and the residuals of §2 only. |
| 5. The `Certificate` map | **Done**: `certificate_rev4 : … → Certificate S` (§3). |

**Checks:**
- `lake build FR FRSoundness4XCtrl`: **green, 2,533 jobs** (`logs/X4/build-final.log`).
- **Axioms** (`logs/fr-build-X4/ax/AxX4.lean`, `logs/X4/axioms.log`): `ks_rev4`, `certificate_rev4`,
  `frontObl_X`, `frontChainStab_X`, `segSound_X`, `nodeRun_X`, `nodeSound_X`, `bgA4_cover`,
  `lRows4_fit`, `okReads_X`, `ss_rejFX` and five controls: all 16 within `propext`,
  `Classical.choice`, `Quot.sound`; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 313
  files, 0 findings (`logs/X4/source-rule.log`).

## 1. What was built (`loc.py`, `logs/X4/loc.txt`: total / code / thm)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4XFront` | 313 / 226 / 19 | **`src4`** (P4b's `FSrc` at 4.1: T4's `Same`, `fF` at the log's kind), `witOf_src4`, `pvL`; **`BgA4`** (far₀ ∨ ¬`PubOK4` ∨ `RowsBadLr4` ∨ `nE4` at `cells4`, `srcL4`, `srcE4`), `bgA4_reads`, **`lRows4_fit`**, **`bgA4_cover`**; `P4X := front4 zW BgA4`, `P4X_ok`, **`stmt_split4X`**; `okX`, `rbL_congrX`, **`okReads_X`**, **`RejF4b`**, **`RejFX`**, `rejOK_of_log4`, `rejF4b_log`, **`rejOK_X`**, **`ss_rejFX`**; **`DFX`**, `W0X`, `c0X`, **`FrontHi`**; `phStart4_13`, `p1Start_zero4`, `phOf4_le12`, `DFX_lo`, `DFX_hi`, **`frontObl_X`**, **`frontChainStab_X`** |
| `FRSoundness4XLaws` | 126 / 80 / 4 | **`GoodX`**, **`SegLog`**, **`NodeLog`**, **`RunFacts4`**, `agree_take3`, **`stmt4_of_tail`**, **`segSound_X`**, **`nodeRun_X`** |
| `FRSoundness4XFinal` | 107 / 64 / 3 | **`nodeSound_X`**, **`ks_rev4`**, `Resid4`, **`certificate_rev4`** |
| `FRSoundness4XCtrl` | 79 / 42 / 10 | controls (§5) |
| **total** | 625 / 412 / 36 | |

## 2. The final theorem and its residual hypotheses

```lean
theorem ks_rev4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    {DFhi : ℕ → Log → Log → Prop} (hHi : FrontHi DFhi)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV
```

`impl₀` is the segment base (`VsegC impl₀` runs `implSeg impl₀`), `base` the node base of INT-9's
`implN4F`; the real ones are `Impl.implC fin lRows κs₀` for both (`FRSoundness4R4ColsCtrl`). The
implementations enter only through `RunFacts4` (R4's op parameters, discharged per kind by
`segC_params`, `phiRS_*`, `implN4F_hM/_hL`).

**Residual hypotheses** (`hV`, `hq`, `hE`, `hε` and, for the certificate, `hext`, `hfuel` define
the submission; S-I sets them by `rfl`):

| # | Name | Statement | Owner | Status |
|---|---|---|---|---|
| 1 | `hHi : FrontHi DFhi` | `FrontObl`'s `ms`, `habs`, `hsingle`, `hfin` at positions `≥ 170`, `handoff` (into T4's `D1 W0X c0X 0`), and `hstab`/`chain` at phases 13 … 25, over the composed `DFX DFhi`/`RejFX` (`FRSoundness4XFront`) | **P4b** (its handover item 2: define `DFhi` 13 … 25 from `RowsBadLr4`…`D4E4`, `PendE4` → `DPend4` → `DRS0_4` → `DRS1_4` → `DB4`, 3.x's `FrDF`/`FrObl`/`FrStab` as template; the units exist: `lr4_*`, `e4_*`, `habs_RS0_4`, `rs1_hfin4`, `single_B4`) | open |
| 2 | `hRun : RunFacts4 …` | `seg`: an accepted segment run on a log with `¬ Bad L` has a chain `j` with `T4.AcceptTail RejFX W0X c0X L j` and `SegLog v es` (kind, start `bytesAt (entAt es 0).1 87 32`, end `bytesAt (msgAt es 1) 1 32`, `nStmt es`); `node`: `AcceptTail` and `NodeLog κ vk c π es` (kind, `X.vkOf π = vk`, `vkL es = vk`, `c = nodeStmt (stL es 0) (stL es 1)`) | **R4** (assembly: `acceptTail4_of_run` with `fields4_of_accept` + `finRest4_of_fields`, `¬ RejFX` from `not_rejF4a_*` and the five `not_rej*_seg/node` of P4b's checks; views: `kindOfC_acc_*`, `vkL_eq4`, `stL_eq4`, `stmtOps4`'s `piDigest 0 16 = input 0` for `vkOf`, `stmtOk4` for `c`, `segView` for `SegLog`) and **R4h** (`pf0`, `enc`, `fin`) | open: every piece but R4h's three fields and the four statement views exists |
| 3 | `I`, `rd`, `hI` | an `N4c.SlotIface4 (VsegC impl₀) (VnodeC (implN4F base) cells4)` with `lrows = lRows4`, `irows = nodeIRows4`, and the read `rd` | **S-E** (no instance exists in `lean/`) | open |
| 4 | `hRes` | `StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w → NodeResid4 I rd κ vk c₁ c₂ w` (imports, replay, templates, selectors, pack/format, chain bytes, the aggregate's parse and padding/counter claim R-4-m2; the signature part S-H4 F's `sig_of_H` refers to is inside it) | **S-E** | open |
| 5 | `D : NodeDec4 nd` | the node decoder's `Links`, `readW` and decode law | **S-H4** | open |
| 6 | `hL` | on a good log, an accepted node run inside the extractor's domain has a transcript meeting `D.Links` whose `readW` is a witness | **S-H4** (with S-G's link discharge, 3.x's `rel_readWit`) | open |
| 7 | `hnd : DecOk4 nd` (certificate) | `WF`, `Safe`, cost, outputs, size of the node branch | **S-H4** | open |
| 8 | `hC` (certificate) | `∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ` | **completeness track / S-I** | open (not in X4's scope) |
| 9 | `hδ` (certificate) | `S.δ ≤ completenessCap` | **S-I** | open |

**Discharged here** (no longer hypotheses): `HFit4` (`hfit4`, S-E's, used in `bgA4_cover`), the L
rows' fit (`lRows4_fit`, new), `BgA`/`NodeRest4` (`bgA4_cover`), `OkReads4` for RS0's bindings
(`okReads_X`, new: `rejRS4_log` had never been instantiated), `FrontLocal` (`frontLocal4`),
`RejOK` and the checks' chain stability of the composed `RejF` (`rejOK_X`, `ss_rejFX`), `hstep`/`h0`
(`muT_laws_of_front`), `epsR ≤ errorCap`, `qV4 ≤ 2^16`, the fuel and program caps (`ext4_caps`),
`Computes` (`computes4`, given `DecOk4`).

## 3. The `Certificate` map (core `6d05d00`, `RecursionFast/Contract/Certificate.lean`)

`Certificate S` has four fields; there is no separate `Solution` structure at the pin.

| Field | Source |
|---|---|
| `secure : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV` | `ks_rev4` at every `vk` (residuals bundled per key as `Resid4`) |
| `complete : ∀ vk, CompleteWithError …` | residual 8 |
| `computes : Computes S.ext S.E S.fuel` | `computes4 hnd S.acc` with `S.ext = ext4With nd`, `S.fuel = X.fuel`, `S.E = E4X nd S.acc` |
| `cap` | `epsR_le_errorCap` (with `S.ε = epsR`), `hδ`, `qV4 = 36000 ≤ 2^16`, `(ext4_caps hnd).1/.2` |

```lean
theorem certificate_rev4 (impl₀ base S) {nd} (hV hq hE hε) (hext : S.ext = ext4With nd)
    (hfuel : S.fuel = X.fuel) (hnd : DecOk4 nd) (D : NodeDec4 nd) {DFhi} (hHi : FrontHi DFhi)
    (hR : ∀ vk, Resid4 impl₀ base S nd D DFhi vk) (hC : ∀ vk, CompleteWithError …) (hδ : S.δ ≤ completenessCap) :
    Certificate S
```

S-I's `Solution`/claim then needs: the `Submission` term with these fields (`V := VC4 …`,
`E := E4X nd (acc)`, `ε := epsR`, `qV := qV4`, `ext := ext4With nd`, `fuel := X.fuel`), and the
residuals 1–9. `CertificateR`'s `bounds` are numbers against the rendered claim (S-I's).

## 4. Findings and deviations

- **F1. Phases 13 … 25 of the front were never composed.** P4b's RESULT lists them as its item 2
  ("waits for P4a's and T4's finals"); no pass ran it. The composition is therefore parametric in
  `DFhi` with the obligations as `FrontHi`. `FrontHi` is stated over the composed dooms so that the
  boundary at 170 (Lr1's `msD` over `DF4a P4X 12 = bg10_4 ∨ D2S`, whose background is `BgA4`) is
  the owner's: `DFhi 13 … 25` must carry `BgA4` (far₀, `PubOK4`, `RowsBadLr4`, `nE4`) and reduce it,
  as 3.x's `bg12`/`bg16`/`bg20`/`DRS0`/`DRS1`/`DB` do.
- **F2. No `FSrc` instance at revision 4.1 existed** (P4b left it a parameter, open question 1):
  `src4` is it.
- **F3. `rejRS4_log` needed `OkReads4` at RS0's real bindings, which nobody had proved**:
  `okReads_X` (`oSh4 wNS4`'s congruence: `claimSL4` by `clR2_same`, `wSumL4` by `wNLocal4` on a node
  and `s1_congr4`/`nStmt_congr` on a segment).
- **F4. The vk in π is asserted, but no 4.1 view exposes it.** `stmtOps4` (node branch) asserts
  `piDigest 0 16 = input 0`, i.e. `X.vkOf π = vk`, which `NodeSoundLog` and `E4X`'s off-domain
  branch need. R4 has no 4.1 analogue of 3.x's `stmt_view`/`vkOf_of_run`; it is inside residual 2.
  No value the argument needs was found asserted by no final.
- **D1. `hfin` below 170** is not `hfin4a` (whose `condCount` reads `DF4a` at every position): it
  calls `z1_hfin4`/`s1_hfin4` at `Dk := DFX DFhi` (they are generic in `Dk`).
- **D2. The per-kind laws read the three-entry prefix** (`stmt4_of_tail`): `tail_of_accept`'s
  `¬ DC` at `p = 2` is `¬ DF4a P4X 2`, so `Stmt4` holds on `es.take 3`; the statement's bytes, kind
  and `nStmt` are read off entries 0 and 1 (`agree_take3`), so no reads lemma for `ZHolds`/`truthS`
  is needed.
- **D3. `ks_rev4` is stated at `S.ε` with `hε : S.ε = epsR`** (the contract's `KS` is at `S.ε`), and
  generic in the bases `impl₀`/`base` (the real ones are `Impl.implC …`).
- **D4. Not touched:** `FR.lean` (import to add above), the 3.x chain (retirement is the
  orchestrator's call, S-G13 F4).

## 5. Controls (`FRSoundness4XCtrl`, and the main theorems)

| Definition | Positive | Negative |
|---|---|---|
| `BgA4` | `bgA4_cover` (a node's failed L row, M row or public cell), `bgA4_of_far` | `bgA4_seg` (on a segment only level 0's distance is left) |
| `RejFX`/`RejF4b` | `rejFX_of_rejS2` | `rejF4b_seg` (on a segment only RS0's slice check is left), `not_rejFX_short` (nothing before 68 entries on a segment) |
| `DFX` | `DFX_lo`, `DFX_hi` | `not_DFX_out` (phases 0, 1 never doomed) |
| `GoodX` | `goodX_nil` | — (T4's `muT`) |
| `SegLog`/`NodeLog` | `segSound_X`, `nodeRun_X` consume them | `not_segLog_node`, `not_nodeLog_seg` |
| `RunFacts4` | `runFacts4_false` (programs that never accept) | — (an accepted run needs `AcceptTail.len`: 482 entries) |
| `FrontHi` | `frontObl_X`, `frontChainStab_X` (it is exactly what T4 still needs) | — (its satisfiability is P4b's deliverable; 3.x's `frontObl` is the template instance) |

## 6. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `logs/X4/prof-*.log`)

| Module | wall (import ≈ 3.9 s) | type checking | tactic execution |
|---|---|---|---|
| `FRSoundness4XFront` | 8.9 s | 0.39 s | 0.47 s |
| `FRSoundness4XLaws` | 6.7 s | 0.08 s | 0.15 s |
| `FRSoundness4XFinal` | 6.7 s | 0.01 s | 0.03 s |
| `FRSoundness4XCtrl` | 6.2 s | 0.02 s | 0.03 s |

No `decide` over a program, table or layout: `lRows4_fit` first used `decide +kernel` on the layout
constants (3 × 2.4 s kernel, `hUsed` unfolds `chainLenOf seq4`) and now uses `regions_fit`,
`lSlots_fit`, `mSlots_fit` and `omega` (module kernel 7.6 s → 0.39 s). Max RSS ≈ 2.9–3.0 GB.

## 7. Handover: the remaining items, in order

1. **R4 (assembly, `RunFacts4`).** Per kind, from `runStmt`'s acceptance: `runLog_chain4`'s chain;
   `acceptTail4_of_finLog`'s fields via `fields4_of_accept` + `finRest4_of_fields` (op parameters by
   `segC_params`, `phiRS_segC`/`phiRS_nodeF`, `implN4F_hM/_hL`; `hm` by `dm_seg4`/`dm_node4`);
   `¬ RejFX` from `not_rejF4a_seg4/node4` and `not_rejEndLr4_*`, `not_rejEndE4_*`, `not_rejInE4_*`,
   `not_rejFinE4_*` (at `NI4F.srcE4`/`srcL4`), `not_rejRS4_*` (at `okX`); then the views
   `SegLog`/`NodeLog` (a 4.1 `stmt_view` from `stmtOps4`'s flags and `stmtOk4`). Needs R4h's
   `pf0`/`enc`/`fin`.
2. **P4b (`FrontHi`).** Define `DFhi` 13 … 25 and prove the seven fields (F1).
3. **S-E.** The slot interface `I`/`rd` at `lRows4`/`nodeIRows4` and `hRes`.
4. **S-H4.** `nd`, `DecOk4 nd`, `NodeDec4 nd`, the links `hL`.
5. **S-I.** The `Submission` term, `certificate_rev4`, completeness, `δ`.

## 8. Open questions

1. Should `RunFacts4` be split between R4 (the `AcceptTail` part) and a statement-view owner, or
   stay one R4 item?
2. `FrontHi` fixes the background `BgA4` at INT-9's row sources and `cells4`. If P4b prefers other
   sources (e.g. per-kind plans), `BgA4` and `bgA4_cover` change with them (one module).
