# S-L4 JOURNAL: residual `hL` (the node links) from the circuit residual

Track S-L4 (2026-10-29). Worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive`, HEAD
`2bf06e2`. Build tree `logs/fr-build-SL4` (copy of `logs/fr-build-orch`, `snap.sh` with
`MINE="FRNodeLinks4 …"`). Logs `logs/S-L4/`. 16G scope, `timeout`, no sub-agents, nothing committed.

## 1. Reading (what `hL` needs)

- `hL` (`FRSoundness4XRunG.lean:81–83`, `Resid4H.links`): for every accepted node run on a good log
  (`GoodX P4f.DFhi`), in the domain (`InDomE`), some `es` with `D.Links κ L es π c` and
  `Rel (S.acc vk) c (D.readW κ L es)`.
- `nodeRun_X` (`FRSoundness4XLaws.lean:109`) gives `StmtN4` on **some** `w`: the chain `j` is lost
  in the existential. It is `src4.fz L (es.take 3) = T4.fF (.node κ) L (es.take 3)` with
  `es = entriesOf L (pathOf L j)`, at `pvL = (vk, stL es 0, stL es 1)`.
- `node_sound4'` (`FRNodeCircuit4Dig.lean:292`, `DigLemma4` discharged): `StmtN4` + `NodeResid4 I rd`
  give `Rel (accV4 …) (nodeStmt c₁ c₂) (.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w))`.
- So `hL` = (i) the run's chain `es` meets `D.Links`, and (ii) `D.readW κ L es` is
  `.node c₁ c₂ (rd.sgn κ 0 w) (rd.sgn κ 1 w)` at `w = T4.fF (.node κ) L es`.
- S-H4 pass 7's `FRXOut4.lean` (untracked, in progress): `wF κ L es e = (T4.msgOf (.node κ) L es 0
  (e % 64) (e / 64)).f₀` (= `T4.fF (.node κ) L es` unfolded), `stD κ σ w` (the statements from the
  `stC` cells; `stD_of_pubCells`), and a finding: the signature cannot be read from L (row 0 not
  decoded), revision 4.3 reads it from H. So the decoder's signed children may **not** be `rd4 pf`'s
  (`readSig4` reads L): the theorem must be parametric in the reader `rd`, and `hRes` is then asked
  at the decoder's reader.
- `acceptRun4_node` loses `runLog_chain4`'s `∀ e ∈ tr, e ∈ L` and `IsChain`; the links (3.x
  `fmAns_of_run`) need them, so `RunLink4` keeps them (a copy of its proof).
- Closure: `FRSoundness4XRunG` does not import `FRNodeSoundA`/`FRNodeRead4`; importing only it adds
  nothing to `Solution`'s closure (computed from the imports).

## 2. Work log
1. Copied `logs/fr-build-orch` → `logs/fr-build-SL4`; first build (old HEAD `2bf06e2`) killed when
   HEAD moved to `b562c50` (S-H4 pass 7: `Open4 = gap : Gaps4, dec : ∃ D, Links4 nd D`; `FRXOut4`
   committed with `LinksD4`, `readW4 sg`, `readW4_eq`, `stD_of_pubCells`, `sgnX_eq`). Re-snapshot.
2. Aligned with pass 7: the decoder's witness `readW4 sg` takes the **signature from H** (`sg`), so
   it equals the reader `rd4 pf4`'s node witness only where `sg = readSig4` (`readW4_eq`'s `hs`).
   That agreement is a new named obligation **`SigH4 sg vk`** (S-G/S-E's `sig_of_H`), stated over
   every `w` meeting `StmtN4`.
3. Modules (new, mine): `FRNodeLinks4` (generic: `RunLink4`, `acceptRunL4_node`, `nodeRunL4`,
   `ReadW4`, `ReadIface4`, **`hL_of_res`**, `resid4H_of_res`, controls); `FRNodeLinks4Run`
   (S-H4's decoder: `fmAns_of_run4`, **`linksD4_of_run`**, `wF_eq_fF`, `SigH4`, `readW4_law`,
   **`hL_of_sig`**, controls); `FRNodeLinks4Sub` (**`links4_of_gaps : Gaps4 → (∀ vk, SigH4 sg vk) →
   Links4 nd D`**, `resid4H_of_gaps`).
4. Fixes: `runLog_chain4 _ _ _` hit "maximum recursion depth" unifying `progNode` with `gen4`; stated
   the run's type explicitly at `implNC` (`hrun''`) and passed the arguments. `fF_take3` rewrote in
   the wrong direction. `LigeritoOut`'s fields cannot be `rw`'d at the structure level; rewrote the
   kind per field.
5. Found S-H4 pass 8's untracked `FRXSig4H.sig_of_H : StmtN4 … w → ∀ σ < 2, sigH κ σ w = readSig4 κ σ w`:
   exactly `SigH4 sigH vk` (`fun κ w c₁ c₂ hS => X.sig_of_H hS`). Not imported (untracked, running).
6. Builds green (`build4.log`, `build-final.log`: `FR Solution` + the three modules, 2,601 jobs);
   axioms (23 declarations) within the three standard ones; source rule 380 files, 0 findings.
7. Orchestrator note: use pass 8's `readW4_sigH` (`readW = readW4 sigH`). Added `FRNodeLinks4SigH`
   (`readW4_sigH_law`, `sigH4_sigH`, `links4_sigH : Gaps4 → Links4 nd D`, `resid4H_sigH`). HEAD moved
   to `ea3e130` (RET-4); re-snapshotted with pass 8's `FRXSig4*` from the worktree. `build5.log` green,
   2,605 jobs; axioms 27 declarations clean; source rule 381 files, 0 findings.
