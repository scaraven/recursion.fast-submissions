# FEL: RESULT — the `felems` cells aliased to arena₁; `Gaps4` proved; `certified` unconditional

Stage FEL, 2026-10-30. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `e447823` = SEG-R2). Design
`design/FEL.md`; review `reviews/FEL-review.md` applied (S3 variant). Build tree `logs/fr-build-FEL` (a copy of
`fr-build-SEGR2` with its `.lake`; `snapF.sh` symlinks every worktree module into `src/`). Logs `logs/FEL/`. Every
lake/lean/probe run in a 16 GB scope under `timeout`. Nothing committed, no sub-agents, `prover/` not touched.

## 0. Verdict

| item | status |
|---|---|
| aliasing + `felems_of_pf` | **done**: `dotKF`'s column cells are arena₁'s cells of the column's window elements (`tplExt4A`, `colA`); a column without elements is refused (an import, failed by the closure); `felems_of_pf` from `PfCells` alone |
| close it | **done**: `N4s.gaps4_fel : Sub4.Gaps4`, `Sub4.open4F_holds : Open4F`, **`theorem certified : CertificateR declared submission`** (no hypothesis) |
| axioms | `Challenge.certified`: `[propext, Classical.choice, Quot.sound]`; 31 declarations checked (`logs/FEL/axioms.log`) |
| source rule | 482 files, 0 findings (`logs/FEL/source-rule.log`) |
| build | `lake build FR Solution FRSubmission4Fin FRNodeRows4Model` green, 2,707 jobs (`logs/FEL/build-final.log`) |
| honest completeness | per prototype **871 aliased / 0 refused / 0 failRT**, 27,856 cells all in region `π`'s arena₁; `askTG` rows 130,914 / 154,333 (unchanged; 0 rows added); plan walk's instances = `protoCS`'s (`logs/FEL/felstat.log`) |
| `plan4t check` | N2 / N4 / N8 **equal true** (`logs/FEL/plan4t-check.log`) |
| MxKat | **PASS** (`logs/FEL/mxkat.log`; the reference is computed in-process from the sparse rows, nothing to re-dump) |
| `plan4t init` A/B | ≈ **+0.3 s user** (median 8.46 → 8.75 s), RSS +17 MB (`logs/FEL/init-ab.log`) — at the kill line (§5) |
| V(N4) A/B | equal within noise: best 1000 / 966 → 1012 / 976 ms (`logs/FEL/v-ab.log`) |
| kernel | changed modules already on the path: +0.28 s; **40 modules newly on `certified`'s path** (the gap chain, now proved): +29.2 s type checking ⇒ ≈ 420 s of 600 (§6) |

## 1. Route (review S3) and why

The review's S3: override only the `dotKF` arm at the extension level, `tplExt4A F R tc al` (= `tplExt4` at every
other op), instead of a new `TCtx` field. Less total work, measured by the import graph: a `TCtx` field rebuilds
365 modules downstream of `FRVIRTplCore` and edits every anonymous `⟨tp, cb⟩` context plus B1's five-lemma chain;
the override sits under `FRNodeRows4Defs` (107 modules downstream), touches no template module, and its soundness is
`tplExt4_okK` plus one arm (`dkX_ok`, a copy of `tplExt_ok`'s ≈ 10-line `dotKF` case; it needs no `ImplTF` step,
`dotKF` reads no `OpImpl` field). B1 is answered by `tplExt4A_okK`, which every `ExtOkK` site now uses (§2).

The few generic lemmas stated at `tplExt4 F R tc` (import / foreign flags) were **generalised** to any extension
whose outputs are neither (`ExtFl`), rather than duplicated (statement changes in §3).

`Defs` imports `FRNodeRows4AskI` for `winE`/`provOf` (the design's fallback; no cycle, `AskI`'s closure does not
contain `Defs`), so there is no `FRNodeRows4Win` cut.

### The alias (S1, S2)

- `colEs win sz x len` (generic window map and proof size): the elements of the windows of bytes `[x, x + len)`, if
  `len ≡ 0 mod 16`, `x + len ≤ sz` and every window has one; `colCells base n es`: cell `b` is `base + e_b`, the zero
  form past the last window. Controls run on toy inputs (`FelCtl.colEs_ctl`, `colCells_ctl`, `lookup_ctl`): no
  `winE`, no `piSizeOf seq4` in the kernel.
- **Computed once per process** (S1): `esC0` (prototype 0's columns' elements, keyed by the field's bytes `(x, len)`),
  `colT0`/`colT1` (column register ↦ elements; prototype 1's through `esC0`, falling back to `colEs` on a miss) are
  closed constants. `colA π col n` is a `List.lookup` into `colTP π`; a register not in the table is refused. Proved
  against the specification: `colTab_lookup`, `esCache_lookup`, `colEWC_eq`, `colTP_lookup`, `colA_some`.
- Cells keep the literal form `π * slotM4 + arA1 + e` (`base := π * slotM4 + arA1`), so `PfCells` applies by
  instantiation (`aux_colW`'s `hpc`), with no `HAdd` unfolding.

## 2. Files (code lines by `scripts/loc.py`: total / code, HEAD → now)

- **`FRVIRTplAlias`** (new, 143 / 94): `dkA` (the aliased arm), `tplExt4A`, `dkX`; `tplExt4A_ne`, `dkA_some`,
  `dkA_isNone`, `dkX_ok`, `dkX_kin`, **`tplExt4A_okK`**; control `dkA_ctl` (alias taken: aux and instance inputs;
  `al = none` refused; column not yet a register refused; another op is `tplExt4`'s).
- **`FRNodeRows4Defs`** (511 / 246 → 610 / 295): imports `FRVIRTplAlias`, `FRNodeRows4AskI`; `pvP` (moved from
  `AskIR`), `colEs`, `colEW`, `colCells`, `dotColsAcc`/`dotCols` (tail-recursive), `esCache`, `colEWC`, `colTab`,
  `esC0`, `colT0`, `colT1`, `colTP`, `colA`, **`XofC π tc := tplExt4A (protoF π) (protoR π) tc (colA π)`**, **`Xof π :=
  XofC π (protoLay π).ctx`**; `xof_dk`, `xof_ne`. Docstring of `repRow0` (n2).
- **`FRNodeRows4`** (424 / 197 → 425 / 197): `protoCS π := compileX (Xof π) …`; `XofT π := XofC π (protoLay π).ctx`;
  `askTG`'s `Xa := XofC π ⟨…⟩`.
- **`FRNodeRows4AskBS`** (220 / 144 → 223 / 147): `XofA π := XofC π ⟨fun _ => ⟨[], []⟩, (protoLay π).cb⟩`; `xofA_imp`'s
  proof (`tplExt4A_ne`).
- **`FRNodeRows4AskIR`** (449 / 352 → 450 / 353): `pvP` removed (moved); `xof_felems`'s proof (the `dotKF` case first).
- **`FRNodeRun4BR`** (334 / 274 → 345 / 285): `xof_bits`'s proof (a `dotKF`'s aux entry is `felems`).
- **`FRNodeRun4BF`** (241 / 197 → 244 / 200): `xofA_aux`'s proof; `ExtOkK` site → `tplExt4A_okK`.
- **`FRNodeRun4BT`**, **`FRNodeRun4CS`** (279 / 220, 95 / 72, unchanged size): `xofA_read`/`xofA_sib` unfold lists gain
  `XofC, tplExt4A`; `BT`'s `ExtOkK` site.
- **`FRNodeRun4CA`** (123 / 94 → 151 / 113): `ExtFl`, `extFl_tplExt4`, `extFl_tplExt4A`, `tplExt4A_isNone`;
  `stepOut_imp_of`, `stepOut_foreign_of` generalised.
- **`FRNodeRun4CB`** (357 / 260 → 359 / 260): `atImp_close`, `atOk_close`, `impB_sub` generalised (`ExtFl`);
  `xofA_isNone` via `tplExt4A_isNone`; `extFl_xof`.
- **`FRNodeRun4CT`** (237 / 168 → 236 / 167): `atOk_close (extFl_xof _)`; `ExtOkK` site.
- **`FRNodeRows4RepW`**, **`FRNodeRun4S`** (145 / 87, 146 / 91): `ExtOkK` sites → `tplExt4A_okK … (colA _)`.
- **`FRVIRTpl4Bridge`** (117 / 65): `protoCS_soundAt`'s proof is `compileX_soundK (tplExt4A_okK …)`.
- **`FRNodeRows4Plan`** (1792 / 1334 → 1791 / 1333), **`RepFD`**, **`RepCFW`**, **`RepCFP`**: the walks' extension
  `tplExt4 (protoF π) (protoR π)` → `N4s.XofC π` (`planData4`, `arOf`, `planDataB`, `arRepOf`, `repRowsP_trail`'s statement, `arBlkN`,
  `arBlk0`); `planData4_rows`'s proof (`rfl` after `rw`).
- **`FRNodeRun4FE`** (new, 227 / 164): §4.
- **`FRSubmission4Fin`** (45 / 12 → 56 / 15): imports `FRNodeRun4FE`; **`open4F_holds : Open4F := N4s.gaps4_fel`**,
  `certificate_sub4' : Certificate sub4`.
- **`Solution`** (35 / 14 → 33 / 14): header comment; `certified` without hypothesis. The stub is otherwise verbatim
  (checked against `org20/harness/challenge/Challenge.lean.in`, including `certified`'s docstring).
- **`FRNodeRows4Model`**: `mRowModel4_eq`'s docstring (n3: `N8` fits; it would stop fitting with more than 28,350
  rows more per segment region).
- **`FR.lean`**: `import FRNodeRun4FE`, `import FRVIRTplAlias` (both after `import FRNodeRun4CT`). No other import change.

Dead after FEL (kept; golf may retire): `colTG`, `colRows`, `auxRows`, `colOk`, `aux_col`, `SlotRunI`, `slotRunA_of_impc`,
`withImpcC`, `askTGIC`, `compileTF4`'s use at the prototypes.

## 3. Statement changes

| declaration | change |
|---|---|
| `protoCS` (def) | `compileTF4 (protoF π) (protoR π) (protoLay π) …` → `compileX (Xof π) …` (the `dotKF` arm aliased) |
| `Xof`, `XofT`, `XofA` (defs), `askTG`'s `Xa` | `tplExt4 … ctx` → `XofC π ctx` = `tplExt4A … ctx (colA π)` |
| `pvP` (def) | moved `FRNodeRows4AskIR` → `FRNodeRows4Defs`, same name and body |
| `planData4`, `arOf`, `planDataB`, `arRepOf`, `arBlkN`, `arBlk0` (defs), `repRowsP_trail` (its right side) | walk extension `tplExt4 (protoF π) (protoR π)` → `N4s.XofC π` |
| `stepOut_imp_of`, `stepOut_foreign_of` | generalised: any `X` with `hX : ExtFl X` (was: `tplExt4 F R tc`) |
| `atImp_close`, `atOk_close` | hypothesis `hX : X = tplExt4 F R tc` → `hX : ExtFl X` (weaker hypothesis) |
| `impB_sub` | generalised: any `X` with `hfl : ExtFl X` (was: `tplExt4 F R tc`) |
| `Challenge.certified` | **`(h : FR.Sub4.Open4F)` removed**: now the challenge's exact statement |

Unchanged statements: `Gaps4`, `Open4F` (`:= Gaps4`), `SlotRunF`, `SlotRunC`, `gaps4_of_runF`, `gap4Imp_of_close`,
`protoCS_soundAt`, `planData4_rows`, `arOf_eq`, `planDataB_eq`, `xof_felems`, `xof_bits`, `xofA_imp`, `xofA_aux`,
`xofA_read`, `xofA_sib`, `xofA_isNone`, `slotRunB_of_close`, `ProtoFit`, `ArFit`, `arR2N`, every row and cell count.
New theorems: §2, §4.

## 4. The proof (`FRNodeRun4FE`)

- `aux_colW` (generic: window map `win`, base `base`, `hpc : ∀ o e, win o = some e → w (base + e) = F.ofBytes
  (bytesAt inp.π o 16)`): `colEs win sz x len = some es`, `sz ≤ inp.π.size`, the register holds `inp.π.extract x (x +
  len)` ⇒ `(colCells base n es).map (Lin.ev w) = (AuxK.felems n).val (rd (regs.extract 0 m) r)`.
- `xof_felemsA`: a `felems n` entry of `stepOut (Xof π) P cs op` has `col < cs.slots.size` and `colA π col n = some
  cells` (`dkA_some`; a non-`dotKF` op carries none, `xof_felems`).
- **`felems_of_pf`** `(hpc : PfCells w π inp) (hsz : inp.π.size = piSizeOf seq4) (he : execA impl ι inp (protoProg
  π).ops St.init tr = some (s, []))`: every non-`bits` aux entry of `protoCS π` holds — `trail_aux` (the trail point),
  `xof_felemsA`, `colA_some`, `execA_prov` (the register's bytes), `aux_colW`. No program, table or compile evaluated.
- `slotRunF_of_pf`, and **`gaps4_fel : Sub4.Gaps4 := gaps4_of_runF fun _ κ w _ _ _ hS v hv _ _ => slotRunF_of_pf
  (pfCells_of_rows hS.1 hv) (by rw [slotIn_π, slotπ_size])`**.

Final statement and axioms (`logs/FEL/axioms.log`):

```
theorem certified : CertificateR declared submission :=
  FR.Sub4.certificateR_sub4F declared FR.Sub4.boundsOK_claim FR.Sub4.open4F_holds
'RecursionFast.Challenge.certified' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Measurements (logs under `logs/FEL/`)

- **felstat** (`felstat.log`, probe `fr-build-FEL/probe/FelStat.lean`): tables 871 / 871 columns, 0 without
  elements. Per prototype: `dotKF` 871, refused 0; `felems` entries 871 (290 × `felems 64`), 27,856 cells, all arena₁
  cells of region `π` (0 outside, 0 zero forms), every instance's cells consecutive; `askTG` 130,914 / 154,333 rows,
  **0 failRT** (p1: 35 rows of `arR2N` slack, unchanged); plan walk (`compMSX (XofC π)`) = `protoCS π`: `tins` equal
  (3,035 / 3,033 instances), aux and row counts equal (review N5's P1 line).
- **`plan4t check`** (`plan4t-check.log`, core 29): N2 equal true (sparse 259 s), N4 true (401 s), N8 true (565 s).
  Pieces 10,049 + 10,289 (ins 7,889 + 8,128), as at HEAD; `slotV3 p0` changed (the instances' inputs moved).
- **MxKat** (`mxkat.log`): 33 × true, **MX KAT PASS**.
- **`plan4t init`** (`init-ab.log`, core 27, 5 alternating rounds, A = `logs/SEGR2/binB/plan4t` = HEAD, B =
  `logs/FEL/binB/plan4t`): A user 9.36 / 8.62 / 8.02 / 8.46 / 8.42 s, B 9.49 / 8.62 / 8.70 / 8.75 / 9.06 s; median
  +0.29 s; RSS 991 → 1,008 MB. Machine load 3–13 (other agents). The first form (two independent tables, no shared
  cache) measured +0.8 s (journal); sharing prototype 0's elements halved it. **At the kill line (+0.3 s), not
  clearly under it.** The next lever (not done, speed only): memoise `pfLoc` per item (`winE`'s 17 `find?`s over
  `pSegs` dominate).
- **V(N4)** (`v-ab.log`, core 28, `vtime4 21 n4f s4`, 2 rounds): `runSeq` best A 999.9 / 966.1 ms, B 1011.9 / 975.9
  ms; `evalMT4 N4` best 933 / 869 → 897 / 881 ms. No measurable change (load 7–13).

## 6. Kernel and build time (`lean -DElab.async=false --profile`, one core; `prof-summary.txt`, `prof-newpath.txt`,
HEAD: `headprof-summary.txt`, HEAD sources `headsrc/` against `fr-build-SEGR2`'s HEAD oleans)

- Changed modules already on `certified`'s path (type checking HEAD → FEL): `Defs` 0.10 → 0.13 s, `FRNodeRows4`
  0.20 → 0.21, `Plan` 1.57 → 1.73, `RepFD` 0.02 → 0.02, `RepCFW` 0.23 → 0.25, `RepCFP` 0.23 → 0.21, `Tpl4Bridge`
  0.09 → 0.18, `Fin`, `Solution`, `Model` < 0.02: **+0.28 s**.
- **Newly on the path**: `certified` now proves `Gaps4`, so its closure gains the gap chain (`Solution`'s closure
  332 → 372 modules): `AskBS`, `AskIR`, `AskIS`, `AskInp`, `AskPos*`, `AskStmtS`, `AskT{B,H,S}`, `Rep`, `RepF`, `RepK`,
  `RepLT`, `RepN`, `RepRsK`, `RepS`, `RepSeg*`, `RepW`, `RsvLink`, `Run4`, `Run4AskT`, `BF`, `BL`, `BR`, `BS`, `BT`,
  `CA`, `CB`, `CD`, `CS`, `CT`, `Ctrl`, `FE`, `S`, `FRVIRTplAlias`, `FRVIRTplRepL`: **29.2 s type checking** (largest:
  `FRNodeRun4CS` 9.0 s, `AskTH` 2.6 s, `AskTS` 1.8 s, `CD` 1.75 s). With SEG-R2's ≈ 390 s: **≈ 420 s of the 600 s
  cap**. Among the changed modules (HEAD → FEL): `AskBS` 0.10 → 0.14, `AskIR` 0.75 → 0.76, `BR` 0.65 → 0.71, `BF`
  0.28 → 0.21, `BT` 0.40 → 0.37, `CS` 8.94 → 9.02, `CA` 0.36 → 0.39, `CB` 0.15 → 0.15, `CT` 0.89 → 0.89 s; new `FE`
  0.17 s, `Alias` 0.09 s.
- **Build time**: the 40 new modules' single-core elaboration sums to ≈ 607 s wall (each including ≈ 7 s of import
  loading; `FRVIRTplRepL` 54 s, `AskIS` 63 s, `RepSegK` 35 s). If the harness's `build_s` cap counts the certificate
  build, check it (open question 1).

## 7. Prover impact (E1b owns `prover/`; nothing edited)

- **Re-dump needed** (INT-9 / E1b's `NodeDumpX` from the FEL tree):
  - `maux-p{π}.txt`: the 871 `felems` entries' cells are now `π·2^20 + arA1 + e` (M-relative, arena₁), consecutive per
    column; the 1,627 `bits` entries are unchanged.
  - `plan-form-p{π}.bin` and the blob (`nodeblob.b64`): each `dotKF` instance's input forms (`Piece.ins … own`) end in
    arena₁ cells instead of the instance's window cells after its `2n` locals. Piece and instance counts unchanged.
  - E1b's `mxkat.txt` (`evalMT4 planOf4` at MxKat's points): values change with the plan.
  - Unchanged: `mregs` (no register slot moves; `dotKF`'s output forms are the template's), rows, `mask-p{π}`
    (`askRowsT`), `mrep-p{π}`, `proto-p{π}`, the layout, cell counts.
- **`mfill`**: the aliased cells are arena₁ cells, which the fill writes first from the slot's stream; the aux pass
  then writes the same cells with the register's elements. `mfill.rs`'s `set` already counts a conflict only for an
  **unequal** value (E1b's comment at the arena write, `mfill.rs:873`), so equal double writes are checks; expect 0
  conflicts on the honest run. The old window cells stay allocated and are referenced by no row: the fill leaves them
  unknown/zero, which is harmless.
- After the re-dump: `plan4t check`/MxKat as above, then the node ACCEPT.

## 8. Review findings

- **B1**: every `ExtOkK` site (RepW, BF, BT, CT, S, Tpl4Bridge) uses `tplExt4A_okK`, which covers the aliased compile.
- **S1**: elements computed once per process in closed tables, prototype 1 through prototype 0's cache; `colA` is a
  lookup. Init ≈ +0.3 s (first form +0.8 s).
- **S2**: generic `colEs`/`colCells` (`colAW` itself was not needed); controls on toy inputs.
- **S3**: taken (§1).
- **S4**: landed after SEG-R2 (HEAD `e447823`); line numbers re-read.
- **N5 / P1**: the plan walk's instances compared with `protoCS`'s (equal).
- Orchestrator addendum n2, n3: docstrings reworded (`repRow0`, `mRowModel4_eq`).

## 9. Deviations from the design

1. Override at the extension (S3) instead of the `TCtx` field; generic `ExtFl` lemmas instead of `tplExt4_imp_tc`'s
   `hcol` and the `isNone` binder changes.
2. No `FRNodeRows4Win` cut: `Defs` imports `AskI` (the memo's fallback).
3. `colA` refuses a column missing from the per-prototype table, which holds exactly the program's `dotKF` columns;
   honest run: 871 of 871 present.
4. The elements of prototype 1's columns come from prototype 0's (a cache keyed by the field's bytes; proved
   transparent by `colEWC_eq`).

## 10. Open questions

1. The certificate's closure grew by 40 modules (+29 s kernel, ≈ +600 s single-core elaboration). The kernel cap fits
   (≈ 420 / 600 s); whether a `build_s` cap applies to the certificate build is for the orchestrator to check with the
   harness.
2. `plan4t init` +0.3 s is at the kill line; the `pfLoc` memo is the next lever if the cap needs it.
