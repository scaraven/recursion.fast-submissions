# S-L4 RESULT: residual `hL` (the node links) from the circuit residual

Base: HEAD `ea3e130` (RET-4) plus S-H4 pass 8's worktree `FRXSig4`, `FRXSig4H`, `FRXSig4W` (being
committed; the stage started at `2bf06e2` and re-snapshotted at `b562c50` and `ea3e130`). Build tree `logs/fr-build-SL4` (copy of `logs/fr-build-orch`; `snap.sh` with
`MINE="FRNodeLinks4 FRNodeLinks4Run FRNodeLinks4Sub FRNodeLinks4SigH FRXSig4 FRXSig4H FRXSig4W"`). Logs in `logs/S-L4/`; journal
`S-L4-JOURNAL.md`. Every lake/lean command ran in the 16G scope under `timeout`. No sub-agents, nothing
committed, no existing module edited.

## Status

**`hL` is proved from the circuit residual and the run**, for any decoder that meets a two-field
interface, and **`Open4.dec` (`Links4 nd D`) is proved from `Open4.gap` (`Gaps4`) and `SigH4 sg`**
for S-H4's decoder shape (links `LinksD4`, witness `readW4 sg`). At the orchestrator's chosen
reader `sigH`, **`links4_sigH : Gaps4 → Links4 nd D`** (`FRNodeLinks4SigH`, through pass 8's
`readW4_sigH`/`sig_of_H`). So once `nd` lands with `Links := LinksD4` and `readW := readW4 sigH`,
`Open4` needs only `gap`.

| Theorem | Statement (short) | Module |
|---|---|---|
| **`hL_of_res`** | `hRes` at a reader `rd` (`StmtN4 → NodeResid4 I rd`) + `ReadIface4 D rd vk` ⇒ `hL` exactly as `ks_rev4H`/`Resid4H.links` state it | `FRNodeLinks4` |
| `resid4H_of_res` | the same ⇒ `Resid4H fin lRows κs₀ S nd D vk` | `FRNodeLinks4` |
| **`linksD4_of_run`** | on the run's chain (`RunLink4`, `AcceptTail`, `GoodX`) S-H4's `LinksD4` holds | `FRNodeLinks4Run` |
| **`readW4_law`** | `SigH4 sg vk` ⇒ `ReadW4 (readW4 sg) (rd4 pf4) vk` | `FRNodeLinks4Run` |
| **`hL_of_sig`** | `D.Links ⊇ LinksD4`, `D.readW = readW4 sg`, `SigH4 sg vk`, `hRes` at `rd4 pf4` ⇒ `hL` | `FRNodeLinks4Run` |
| **`links4_of_gaps`** | `D.Links ⊇ LinksD4`, `D.readW = readW4 sg`, `∀ vk, SigH4 sg vk`, `Gaps4` ⇒ `Links4 nd D` | `FRNodeLinks4Sub` |
| `resid4H_of_gaps` | the same ⇒ `Resid4H … sub4 nd D vk` | `FRNodeLinks4Sub` |
| `readW4_sigH_law`, `sigH4_sigH` | `ReadW4 (readW4 sigH) (rd4 pf4) vk` (`readW4_sigH`); `SigH4 sigH vk` (`sig_of_H`) | `FRNodeLinks4SigH` |
| **`links4_sigH`** | `D.Links ⊇ LinksD4`, `D.readW = readW4 sigH`, `Gaps4` ⇒ `Links4 nd D` | `FRNodeLinks4SigH` |
| `resid4H_sigH` | the same ⇒ `Resid4H … sub4 nd D vk` | `FRNodeLinks4SigH` |

## 1. What was built (`loc.py`, `logs/S-L4/loc.txt`: total / code / thm)

| Module | loc | Content |
|---|---|---|
| `FRNodeLinks4` (imports only `FRSoundness4XRunG`) | 232 / 147 / 9 | `implNC`; **`RunLink4`** (S-N1's `RunLink` at 4.1: trace, `SkRun4`, `semIR`, `tr ⊆ L`, `IsChain`, entries = `fsOf tr (itemsOf seq4)`, `stmtOk4`); **`acceptRunL4_node`** (`acceptRun4_node` keeping `runLog_chain4`'s `tr ⊆ L` and chain); `fF_take3`; **`nodeRunL4`** (`nodeRun_X` with the chain kept: `StmtN4` on `T4.fF (.node κ) L es` at `stL es 0`, `stL es 1`, `c = nodeStmt …`); **`ReadW4`**, **`ReadIface4`**, **`hL_of_res`**, `resid4H_of_res`; controls `not_runLink4_nil`, `pubCells4_unique`, `readWP`, `readW4_readWP`, `readW4_leaf` |
| `FRNodeLinks4Run` (+ `FRXOut4`) | 174 / 101 / 13 | `wF_eq_fF`, `cap_lv_node`, `fin_lv_node`, `findSnd_of_mem4`, **`fmAns_of_run4`** (3.x `fmAns_of_run` at `seq4`, 482 positions), **`linksD4_of_run`**, `readIface4_of`, **`SigH4`**, **`readW4_law`**, **`hL_of_sig`**; controls `linksD4_stateHit`, `sigH4_readSig4`, `sigH4_ne`, `lv_node_ctl` |
| `FRNodeLinks4Sub` (+ `FRSubmission4Cert`) | 35 / 18 / 2 | **`links4_of_gaps`**, `resid4H_of_gaps` |
| `FRNodeLinks4SigH` (+ `FRXSig4H`) | 42 / 18 / 4 | `readW4_sigH_law`, `sigH4_sigH`, **`links4_sigH`**, `resid4H_sigH` |
| **total** | 483 / 284 / 28 | |

### The interface (what S-H4's decoder must meet; `ReadIface4 D rd vk`)

```lean
def ReadW4 (readW : NodeKind → Log → Log → Wit) (rd : N4c.Read4) (vk : Digest) : Prop :=
  ∀ κ L es c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ (T4.fF (.node κ) L es) →
    readW κ L es = .node c₁ c₂ (rd.sgn κ 0 (T4.fF (.node κ) L es)) (rd.sgn κ 1 (T4.fF (.node κ) L es))

structure ReadIface4 (D : NodeDec4 nd) (rd : N4c.Read4) (vk : Digest) : Prop where
  links : ∀ κ L c π j, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    RunLink4 fin lRows κs₀ κ vk c π L j → T4.AcceptTail RejFX W0X c0X L j →
    D.Links κ L (entriesOf L (pathOf L j)) π c
  readW : ReadW4 D.readW rd vk
```

`hL_of_res`'s proof: `nodeRunL4` gives the chain `j` and `StmtN4` on its `f⁽⁰⁾`; `hRes` gives
`NodeResid4 I rd`; `node_sound4'` (`DigLemma4` discharged) gives `Rel (accV4 …) (nodeStmt c₁ c₂)
(.node c₁ c₂ (rd.sgn …) (rd.sgn …))`; `acc_eqC4` and `ReadW4` turn it into `Rel (S.acc vk) c
(D.readW κ L es)`; `ReadIface4.links` gives `D.Links`. Both fields are discharged for S-H4's
decoder: `links` by `linksD4_of_run` (every conjunct of `LinksD4` from the run, table below), `readW`
by `readW4_law` given `SigH4`.

| `LinksD4` conjunct | from |
|---|---|
| `¬ StateHit L` | `¬ Bad L` (`muT_lt_one` on `GoodX`) |
| `∃ st₀, fmAns (fsQ4 seq4 (vkOf π) c π) st₀ L p = some (ansAt es p)`, `p < nRep4` | `st₀ = zeroD`; `fmAns_of_run4` (no repeated query, `SkRun4.hq`, `tr ⊆ L`), `vkOf_node4` |
| caps `capDig es i e = capPi4 i π e` | R4's `capDig_eq4`, `cap_lv_node` (node caps = `seq4`'s) |
| final `finalAt es x = finPi4 π x` | R4's `finalAt_eq4`, `fin_lv_node` (`2^mLog 4 ≤ 128`) |
| `¬ farL`, `consSet = jointAgree` | `T4.tail_of_accept` (`frontObl_X`, `frontChainStab_X` at `P4f.frontHi_X`) → `LigeritoOut.close`/`.agree` |

## 2. Checks and times (logs in `logs/S-L4/`)

- **Build**: `lake build FR Solution FRNodeLinks4 FRNodeLinks4Run FRNodeLinks4Sub FRNodeLinks4SigH`
  green on HEAD `ea3e130` + pass 8's `FRXSig4*` + these modules, **2,605 jobs** (`build5.log`;
  earlier `build-final.log`, 2,601 jobs on `b562c50` without `FRNodeLinks4SigH`).
- **Axioms** (`axioms.log`, `logs/fr-build-SL4/ax/AxSL4.lean`, 27 declarations, every theorem
  above and every control): 24 use `propext, Classical.choice, Quot.sound`, 3 only `propext`; no
  `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`):
  381 files, 0 findings (`source-rule.log`).
- **Sequential elaboration** (`lean -DElab.async=false --profile`, one core, imports included,
  `time-*.txt`, `prof-*.log`): `FRNodeLinks4` 8.0 s wall (5.2 s user), `FRNodeLinks4Run` 7.8 s (type
  checking 0.43 s), `FRNodeLinks4Sub` 6.3 s, `FRNodeLinks4SigH` 7.3 s. No `decide` on large terms (only `cases κ <;> decide`
  on ladder numerals).
- **Closure**: `FRNodeLinks4` adds no module to `Solution`'s closure besides itself (its import
  `FRSoundness4XRunG` already is in it); `FRNodeLinks4Run` imports `FRXOut4` and `FRNodeLinks4Sub`
  imports `FRSubmission4Cert`, both already in `Solution`'s closure at `b562c50`. No 3.x
  soundness-front module is imported directly.

## 3. Controls

| Control | Kind | What it shows |
|---|---|---|
| `not_runLink4_nil` | − | `RunLink4` never holds on the empty log (no chain) |
| `pubCells4_unique` | lemma | the public cells fix `c₁`, `c₂` (`Circ.digest_ext`) |
| `readW4_readWP` | + | `ReadW4` is satisfiable for every reader `rd` and key (`readWP`: the digests the cells carry, `rd`'s children) |
| `readW4_leaf` | − | a decoder outputting a leaf violates `ReadW4` as soon as one chain meets a node statement |
| `linksD4_stateHit` | − | `LinksD4` fails on a log with a state hit |
| `sigH4_readSig4` | + | `SigH4` holds for L's own reader |
| `sigH4_ne` | − | `SigH4 sg` fails for any `sg` that differs from `readSig4` on a statement-meeting witness |
| `lv_node_ctl` | value | `N2`'s level-0 cap depth is 9; the final message has 64 (`N2`) and 128 (`N4`) elements |

`linksD4_of_run` is itself the positive control of `LinksD4` (it holds on every accepted run's chain).

## 4. Deviations and findings

1. **`hL` needs the run's chain, not `nodeRun_X`'s existential `w`.** `nodeRun_X` loses `j`, so the
   decoded witness cannot be tied to `StmtN4`'s `w`. `nodeRunL4` keeps it and states `w =
   T4.fF (.node κ) L es` (via `src4.fz_same` from the three-entry prefix).
2. **`acceptRun4_node` drops `tr ⊆ L` and `IsChain`** that the first-match link needs (3.x O0's
   `RunLink`). `acceptRunL4_node` is its proof copied with those kept (27 lines; `FRSoundness4XRun`
   is not mine to edit). If R4's owner adds them to `acceptRun4_node`, `acceptRunL4_node` reduces to
   it.
3. **The signature is a named obligation, `SigH4 sg vk`.** Pass 7's `readW4 sg` reads the signature
   from H; `node_sound4'` proves the relation for `rd4 pf4`'s L signature. `ReadW4` takes `StmtN4`
   (not just `PubCells4`) so that `sig_of_H` can use the rows. S-H4 pass 8's `sig_of_H` has
   exactly this shape (`sigH4_sigH`), and its `readW4_sigH` gives the read law directly
   (`readW4_sigH_law`), as the orchestrator asked. `FRNodeLinks4SigH` depends on pass 8's
   `FRXSig4*`, which were uncommitted when built: commit them together.
4. **Parametricity.** `hL_of_res` is parametric in the reader `rd` (any `N4c.Read4`, e.g. `rd4 pf`
   for any `pf`) and in the decoder `D`; the format enters through `rd` and `D.readW`. The run side
   (`RunLink4`, `acceptRunL4_node`, `fmAns_of_run4`, `linksD4_of_run`) refers to `seq4`,
   `itemsOf seq4` and `piSizeOf seq4` by name, as all of R4/X4 does: on `v4/rev44` the modules port
   by recompiling against that branch's `seq4` and R4 lemmas (`runLog_chain4`, `capDig_eq4`,
   `finalAt_eq4`); the numerals `482` (positions) and `128` (`fin_lv_node`) are the only constants,
   and both are checked against `SkRun4.len` and the ladder.

## 5. For the orchestrator / S-H4 (integration)

- When `nd` lands with `nodeDec4_nd : NodeDec4 nd` having `Links := LinksD4`, `readW := readW4 sigH`:
  `Links4 nd nodeDec4_nd = links4_sigH nodeDec4_nd (fun _ _ _ _ _ h => h) rfl h.gap`.
  **`Open4` then reduces to `gap : Gaps4`.**
- Import order: `FRSubmission4Cert` cannot import `FRNodeLinks4Sub`/`FRNodeLinks4SigH` (cycle).
  Either import `FRNodeLinks4Run` and `FRXSig4H` into `FRSubmission4Cert` and inline
  `links4_of_gaps` there (5 lines), or keep these modules downstream and state the final
  certificate in a module after them.
- `FR.lean`: add `import FRNodeLinks4SigH` (pulls in the other three).

## 6. Open questions

- **Q1.** Should R4's owner extend `acceptRun4_node` with `tr ⊆ L` and `IsChain` (then
  `acceptRunL4_node` becomes a one-liner)?
- **Q2.** Which module holds the final `Open4` (with `dec` dropped): `FRSubmission4Cert` importing
  `FRNodeLinks4Run`, or a new downstream module (§5)?
