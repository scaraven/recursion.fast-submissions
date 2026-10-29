# S-E12f (track L-circ): JOURNAL. INT-9 F1: kind-muxed `tensorW`/`eqPt` templates

Base HEAD `faa2f4b` (INT-9). Build tree `logs/fr-build-SE12f` (copy of `fr-build-INT9`, against
`logs/org20`); logs in `logs/S-E12f/`. Every lean/lake/probe command in a 16 GB scope with a timeout.

## Diagnosis (from `logs/INT-9/nodedump/proto-p{0,1}.txt`)

- The 745 `tensorW` are `tensorW j r` with `r ∈ {r93825 … r93828}` (290/178/145/132 instances).
  Each `r` is a `keep` chain over the kinds' `packK` points of **different lengths**, e.g.
  `r93828 = keep {L} r93632 (keep {N} r93744 r93686)` (`packK` of 10/8/9 `K`s). The compiler's
  `keep` on two types that differ is `skip 1` (untracked), so `tensorW` falls back to `opOut`
  (an import). `j` is an `idx` with kind-dependent widths, but `tensorW` reads `j` as 20 aux bits
  whatever its width (`AuxK.bits logNMax`): the width is not what blocks the template.
- The 2 `eqPt` (prototype 0) read two `packFK` whose kinds' lists differ in length (17/16/17,
  23/22/23): `packFK` is then `skip 1`.
- So the blocker is the **operand**: its value at kind `κ` has a kind-dependent type, and a slot
  (`Option (Ty × List Lin)`, kind-free) cannot represent it. A route (static per-prototype
  constants, `RouteOk R impl κ`) cannot supply the fact "register `r` holds the kind's source
  register at kind `κ`": it is a fact about the run, not about `impl`.

## Design

- **Per-kind slots** in the compile state: `Out.kin : Option (Kind → Slot)` (the per-kind slot of
  the op's first result) and `CS.kslots` (register ↦ per-kind slot); `CS.slotK i κ` reads it, else
  the slot. Only an extension sets `kin`; `opOut` and every 3.x extension leave it `none`.
- **`InvK`** (the compile invariant at the run's kind): `Inv` + `KsOk` + `∀ i, RepS w (slotK i κ)`.
  **`ExtOkK`**: `ExtOkAt` with the per-kind slots among the hypotheses and `kin` among the
  conclusions; `compileFromX_soundK`/`compileX_soundK`.
- **`tplExtKM`** (the kind-mux extension), tried after `tplExt4`'s old cases (`tplExt4S`):
  - `keep act n o` that `opOut` leaves untracked: `kin κ = slotK (act κ ? n : o) κ`;
  - `packFK xs` with lists of unequal length: `kin κ = af |xs κ|` of the kind's list;
  - `tensorW j r` with `r` per-kind `ak n_κ`: key `.tensorWK [n_L, n_P, n_N]`;
  - `eqPt a b` with per-kind `af`: key `.eqPtK [(n, m)_κ]`.
- **Templates** (`FRVIRTplKMux`): a generic kind mux `kmuxT` of sub-templates by input
  substitution (`subW`, `pullE`, `eqns_sub`): sub-template `j` reads its kind's operand block and
  the shared tail; outputs `Σ_j sel_j · out_j`. `tplTensorWK`, `tplEqPtK` and their `_ok`.

## Implementation log

- `FRVIRCompile`: `Out.kin`, `CS.kslots` (appended last; `CS.add`/`CS.init` extended), `CS.slotK`,
  `opOut_kin`. 3.x's definitions are unchanged otherwise; `CS.add` stores `kin` only when set.
- `FRVIRCompileSound`: `ExtOkK`, `ExtOkAt.toK`, `Ext.orElse`/`ExtOkK.orElse`, `KsOk`, `InvK`,
  `lookup_ge`, `slot_add_old`, `invK_add`, `CS.align_kslots`/`align_slotK`, `compileFromX_soundK`
  (S-E12e's induction over `InvK`), `compileX_soundK`. The old theorems are untouched.
- `FRVIRTplCore`: `TKey.tensorWK ns`, `TKey.eqPtK ps`. `FRVIRTplExt`: `tplOf` cases, `twkLocs`,
  `cregion` case. `FRVIRTplBuild`: `keyInfo`'s matching case (`keyInfo_eq` unchanged).
- `FRVIRTplKMux` (new): `subW`, `Gate.sub`, `pullE`, `eqns_sub`, `subsG`, `kmuxT`, `kmuxT_ok`,
  `flatten_getD`, `tplTensorWK(_ok)`, `tplEqPtK(_ok)`. The sub-template's inputs past its operand
  and shared tail are substituted by `[]` so that `InpIs` (total) holds at the pulled-back wires;
  otherwise the selectors would sit there.
- `FRVIRTplSet`: S-E12e's `tplExt4` renamed `tplExt4S` (its theorem `tplExt4S_okAt`, statement
  unchanged up to the name); the new `tplExt4 := tplExt4S.orElse (route ? tplExtKM)`;
  `tplExt4_imp` (same statement); `tplExtKM_okK`; `tplExt4_okK`; `compileTF4_soundAt` (same
  statement) now by `compileX_soundK`. Each kind's operand forms are checked to have their type's
  length in the extension, so the template's input blocks have fixed offsets whatever the
  unselected kinds' forms are.
- Pitfall: `simp at h` does not reduce `({ tplOut … with aux := … }).kin`; `simp [tplOut] at h`.
- Pitfall: `List.getElem?_eq_getElem` inside `simp only [...]` with an elaborated bound failed on
  metavariables; give the list explicitly (`(l := [a, b, c])`).

## Regeneration and measurements

- Hint (`laydump4`, 17.9 s); `plan4t check` (12 min, sparse references): 108 keys, `inR true`,
  `evalMT4` = sparse for N2/N4/N8; plan start 1.87–1.91 s (A/B vs INT-9: 1.91–2.08 vs 1.71–1.77).
- Node dump (+ `mkslots`, `mtinsk`), protodump (protos byte-identical to INT-9's), planform4
  (969,350 / 970,966 B), KAT PASS. Imports 26,638 / 26,655.
- V(N4) `vtime4 21 n4f`: best 184.3 / 189.4 ms; A/B 185.2 / 183.9 vs INT-9 179.9 / 176.3.
- Kernel trap in `FRVIRTplKMux` (30 s type checking, 24 s `obtain`): `rfl` on `subW_ev`'s nil case
  (lambda-first defeq into `F`'s multiplication) and unification of repeated lambdas in
  `tplEqPtK`; fixed (`ev_nil` rewrites; `epW`/`epT`). After: 0.38 s / 0.65 s. Dump unchanged.
- Final: entry build 2,530 jobs green; axioms 46 within the three; source rule 0 findings.
