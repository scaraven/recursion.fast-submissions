# RET-4 RESULT: `FRNodeSoundA` out of `FRNodeRows4PackSound`'s closure (PATH-review F2)

- **Base.** HEAD `2bf06e2` + RET-3's uncommitted files (its `MINE.txt`, 38 modules) + RET-4's 4 files.
- **Build tree.** `logs/fr-build-RET4` (copied from `fr-build-orch`; `MINE.txt`, `b.sh`, `chk.sh`).
- **Logs and tools.** In `logs/RET4/`. The use scan is `fr-build-RET4/scratch/Uses.lean` → `uses.txt`; the
  hashes `scratch/StmtHash{,A}.lean` → `stmt-{before,after}.txt`; the closures RET-3's `tool/clos.py`
  → `clo-{before,after}.json`, summary `closure-summary.txt`.
- **Rules followed.** Every lean/lake command ran in the 16G scope under `timeout`. No sub-agents. Nothing committed.

## Status

| Check | Result |
|---|---|
| What the route reads | Two modules of the route import `FRNodeSoundA`: `FRNodeRead4` and **`FRNodeRows4WotsB`** (the review named only the first; re-pointing `FRNodeRead4` alone drops nothing). The term-level use scan over every kept FR module of the closure finds **3** constants of the 74 dropped modules: `Snd.digestOf_halves` (`WotsB`, `WotsP`), `Snd.enc64_toListLE` (`WotsS`), `Snd.readItems_qlen` (`FRNodeSound4R`). The other 48 hits are equation lemmas, splitters and `_sparseCasesOn` lemmas realised in a dropped module whose base definition lives in a kept one; Lean realises them again where needed. `Read.digestOf`, `readSigned`, `Read.readItems` (the review's three) are in `FRNodeRead`, which stays in the closure through S-H4's `FRXOut → FRNodeReadP`. |
| Move | **6 theorems** moved verbatim from `FRNodeSoundA` into the new `FRNodeReadCore`: the 3 above plus their internal dependencies `toListLE_eq_ofFn`, `wordBytes_ofBytes`, `wordsBytes_elemWords`. Two contiguous chunks (old lines 33–78 and 147–156). The text was checked identical with `diff`. |
| Statements | `stmt-before.txt` = `stmt-after.txt`: the type hash **and the proof-term hash** of all 6 are identical. |
| Imports | `FRNodeRead4`, `FRNodeRows4WotsB`: `import FRNodeSoundA` → `import FRNodeReadCore`. `FRNodeSoundA`: + `import FRNodeReadCore`, and the two chunks are replaced by `-- RET-4:` pointer lines. No other edits. |
| Build | `lake build FR Solution FRNodeRows4PackSound FRNodeSound4Ctrl`: **green**, 2,599 jobs, 0 errors (`build-final.log`). The only warnings in the touched files were there before. |
| Axioms | `ax/AxRET4.lean` → `axioms.log`: all 6 names are in `FRNodeReadCore` and use only `propext`, `Classical.choice`, `Quot.sound`. |
| Source rule | `logs/org20/scripts/source-rule.py submissions/flock-recursive`: 380 files, **0 findings** (`source-rule.log`). |

## Closure of `FRNodeRows4PackSound`

Times are from `logs/probe-cert-g3/probe-si-cert/out/build.log` (G3, 7763). That probe built only `Solution`'s
closure. So the modules it left out are filled in from S-I's `logs/S-I/run-40810876665/build-modules.txt`,
and the rest are counted as untimed.

| | Modules | CPU-s (G3) | + CPU-s (S-I, for G3-untimed) | Untimed in both |
|---|---|---|---|---|
| Before | 327 | 2,316.2 (244 timed) | 420.1 (57) | 26 |
| After | 254 | 2,136.0 (232 timed) | 0 | 22 |
| **Dropped** | **74** | **180.2** (12) | **420.1** (57) | 5 (`FRNodeSoundA`, `FRNodeReadLayout`, `FRSoundnessExtLinks`, `FRXNodeRun`, `FRXLeaf`) |
| Added | 1 (`FRNodeReadCore`) | — | — | 9.6 s locally (`build-final.log`, VM under load) |

**Net ≈ −600 CPU-s** at 7763 times (180.2 + 420.1), plus the 5 untimed dropped modules, minus `FRNodeReadCore`
(≈ 10 s). This matches the review's 75 modules / ≈ 597 CPU-s. The dropped modules are the 3.x soundness stack
(`FRSoundness{Fr*,Acc*,Step*,Tail*,…}`, `FRKState`) and the 12 3.x verifier modules that RET-3 took out of
`Solution`'s closure (`FRVIRSpec`, `FRVIRFinalsSG`, `FRNodeTarget`, …), which were still on this route.

## Files (`loc.py`: total / code / thm)

- `FRNodeReadCore` (new): 82 / 55 / 6. Imports `FRNodeReadW` (`Read.digestW_toList`) and `FRVIRCompile` (`dlo`, `dhi`). Both are already in the closure.
- `FRNodeSoundA`: 270 / 181 / 22 → 218 / 133 / 16.
- `FRNodeRead4`, `FRNodeRows4WotsB`: one import line each.

## Notes and open questions

1. **Not touched (owned by others):** `FRXOut4`/`FRXSig4` (S-H4, untracked in the worktree) import `FRNodeRead4`. They use `Snd.digestOf_halves`, which `FRNodeReadCore` still provides, and no other remaining `FRNodeSoundA`/`FRNodeReadLayout` name (grep). `FRSoundnessExtAll` still imports `FRNodeSoundA`; it is not on this route.
2. **What still pulls in the 3.x node read:** `FRNodeRead`/`ReadW`/`ReadS`/`ReadP` remain through `FRXOut → FRNodeReadP` (S-H4). RET-3 §4.2 covers it. `FRNodeReadCore` is the natural home for those 4 `FRNodeReadS` declarations too.
3. Item 2 of the review's action (a `probe/si-cert` run with a `Solution` that imports `FRNodeRows4PackSound`) is not part of RET-4.
