# S-N2 JOURNAL: residuals 3–4 of `ks_rev4F` (the `SlotIface4` instance, its reader, `hRes`)

Build tree `logs/fr-build-SN2` (copy of `fr-build-SE12f`, `logs/org20`; `MINE.txt` = this track's
modules). Logs `logs/S-N2/`. Every lake/lean command in the 16G scope under `timeout`. No sub-agents.

## 0. Survey (before writing)

- `SlotIface4.soundN/soundS` need, from rows + selectors + `imp`/`rep`/`tpl`, `runSeq` of
  `VnodeC`/`VsegC` (= `runStmt`: the run, then `stmtOk4`).
- Available: `protoCS_soundAt` (S-E12e/f; needs `ImplTF`, `RouteOk`, `SelOk`, the run `exec … = some`,
  rows, template rows, aux, imports, foreign flags), `progNodeGK_exec`/`progSegG_exec` (INT-8; needs
  `impl'.fixK κ = impl.fixK ι`), `runStmt_iff`, `runSeq_runIR`.
- `nodeIRows4` cells are M cells and L selector bits only (`slot_mem`); `lRows4` are bit rows on L.
  **No row of either references an H cell.** The WOTS rows exist only in the row model
  (`wotsRows4`). So every `NodeResid4` item that ties H (stream bytes, digests, `F_{a,k}`) or the
  signature to anything is a missing constraint.

## 1. Item 1: `SlotIface4` (`FRNodeSound4`) — done

- `slotIRows_snd`: a slot's indexed rows are `rowList ++ tplRows` (no evaluation).
- `slotRows_hold`/`slotRows_of`: `truthEI (nodeIRows4 κ)` (+ `one = 1` for the `¬ ProtoFit` branch)
  gives slot `v`'s compiled and template rows at `slotAsg κ v w`.
- `implP`: the kind's ops read at `tix` (`fixK .N30` / `fixK .L32`): kind-blind, so
  `progNodeGK_exec`'s hypothesis is `rfl` (`fixK_fixK`). `implTF_fixK`, `routeOk_fixK`,
  `implTF_implSeg`.
- `imp := SlotImp`: exactly `protoCS_soundAt`'s run-dependent hypotheses at every selectable
  index, plus `stmtOk4`. `rep := True` (no `R` in the circuit). `tpl := SlotRows`.
- `soundN`/`soundS` proved. First build green.

## 2. Reader (`FRNodeRead4`) — done

- `kAct` (Nat.find over the activity), traces from H's `chainBytes4` (3.x `readItems`), proofs
  `pf` (parameter: seq4 reassembly is S-H4's), `π_A` = `aggHdr` + fitted slot proofs, `(e, n)` from
  `hashA`, signatures from L (`readSig4`). `kA_rd4`: header `k` = `kAct`.

## 3. Item 2: `hRes` (`FRNodeSound4R`) — done as `resid4_of` + `Gap4`

- Proved from rows/reader: `tpl`, `rep`, the selector halves of `selP`/`selA` (with `actK_kAct`:
  the reader's `kAct` meets S-E12c's `ActK` from the activity rows), `slotP`, `aggTr`, `aggFmt`
  (`aggSegs_flat`), `kOk`, `pack` (sizes; `traces_le_qV`; queries ≤ `queryCap` by one
  `decide +kernel` over `seq4`'s 26 + 5·nLevels phase shapes, `phasesOf_shQ4`).
- `chainMsg` reduced to `wf` (`chainMsg_of_wf`, `FRNodeRead4W.stream_of_wf`): tag byte + length
  words; the converse `wf_of_chainMsg` holds too.
- Gaps (no rows): `imp`, `kindN`, `kindS`, `wf`, `aggChk`, `aggPad`, `wots`.
- Converse control `gap4_of_resid`: `NodeResid4` ⇒ `Gap4`, so `hGap` asks no more than `hRes`.
- Imports by producing op (`logs/S-E12f/nodedump`, `mregs` × `proto`): see RESULT §2.
- Observation: the group program's first ops are `piElem 0 0`, `const {L,P,N}`, `assertEq`: the
  kind header is checked in the run, on an imported cell. So `kindN`/`kindS` follow from `imp` plus
  that assertion; not proved (it needs the program's first ops, a generator evaluation).

## 4. Item 3: `ks_rev4H`, `certificate_rev4H` (on P4f), `ks_rev4GH`, `certificate_rev4GH` (on R4i's
`ks_rev4G`, committed `7292eab` during the stage) — done.

## 5. Checks
- `lake build FR FRNodeSound4Ctrl`: 2,552 jobs green (`logs/S-N2/build-final.log`).
- Axioms: 46 declarations, standard only (`logs/S-N2/axioms.log`).
- Source rule: 333 files, 0 findings.
- Profiles: `logs/S-N2/profile-*.log`; max type checking 0.30 s.
