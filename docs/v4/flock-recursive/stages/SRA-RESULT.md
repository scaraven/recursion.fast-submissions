# SRA RESULT: `Gaps4` over `StmtN4R`, the reserve's binding of slot 0's `evalM`, the foreign flags

Track SRA, 2026-10-29. Worktree `recursion.fast-submissions-rev44` (`v4/rev44`, HEAD `616b57c`). Build
tree `logs/fr-build-SRA` (copy of `fr-build-IMP`, re-snapshotted onto `616b57c`; MINE = this track's
modules; every other module is HEAD's text, so ASK-P's uncommitted edits to
`FRNodeRows4`/`Fit`/`Plan`/`FRNodeSound4`/`FRNodeSound4R` are **not** in this build). Logs `logs/SRA/`;
journal `SRA-JOURNAL.md`. No sub-agents, nothing committed, no `sorry` in the worktree. Every lake/lean
ran in a 16 GB scope under `timeout`.

## 0. Summary

| Item | State |
|---|---|
| 3. `Gaps4` to `StmtN4R`, `certificate_sub4` through `certificate_rev4HR` | **Done.** The hypothesis only shrank: converse `gaps4_of_N`. `PubCellsR4`/`truthChildV` are not added to `Open4F`; the accepted run gives them on its own chain (`nodeRunRL4`). |
| 2. `gap4Imp_of_rsv` | **Done** (`FRNodeRsvLink`). It does not go through a prefix form. The reserve is one more `AT` summand (`AT.rsv`, IMP's `AT.add`). Slot 0's three `evalM` outputs leave `SlotRunA`'s residual imports. |
| 1. Prefix form of `compileX_run` | **Not built: not needed** (deviation, §3). `ATImp` already receives the prefix invariant `InvK` at the covered op. |
| 4. `SlotRunA` without the arena | **The foreign flags are listed and classified** (§4): 15 (prototype 0) / 79 (prototype 1), from the compiled prototypes (`logs/SRA/forsdump.log`). **None can be discharged without the arena.** 92 are zero pins on proof bytes and 2 are kind-byte checks. **One is a soundness gap that no row covers today:** the (β′) cap-check equation in prototype 0 (§4.2). Exact requests to ASK-P: §6. |
| Build | `lake build FR Solution FRSubmission4Fin FRNodeRsvLink`: **green, 2,649 jobs, 0 `sorry`** (`logs/SRA/build-full.log`) |
| Axioms | 22 declarations, `RecursionFast.Challenge.certified` included: ⊆ {`propext`, `Classical.choice`, `Quot.sound`} (`logs/SRA/axioms.log`, `fr-build-SRA/ax/AxSRA.lean`) |
| Source rule | 428 files, 0 findings (`logs/SRA/source-rule.log`) |

## 1. The new exact form of `Gaps4`

```lean
def Gaps4 : Prop :=
  ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
    ∀ v, N4c.Active4 (N4s.rd4 X.pf4) κ w v →
      N4s.SlotImp implB (fun _ => implB) κ v w (N4c.slotIn (N4s.rd4 X.pf4) κ vk c₁ w v)
        ((N4s.rd4 X.pf4).slotTr κ v w)
```

`StmtN4R = StmtN4 ∧ PubCellsR4 κ w ch ∧ truthChildV srcE4 ch`. `Open4F := Gaps4`, and `certified (h : Open4F)`
keeps its text. **Shrink:** `gaps4_of_N` derives the new `Gaps4` from IMP's `StmtN4` form, and
`gaps4_of_gap4R` still holds. The reverse direction is the point of the change: at a kind change
`SlotImp` at slot 0 is not provable from `StmtN4` alone (RSV-S2b §5.5).

**How the run supplies `ch`:**
- `certificate_sub4` now calls `Snd.R4.certificate_rev4HR` (RSV-S3's). Its `secure` leg passes
  `StmtN4R` to `hRes` via `nodeSoundR_X`.
- The links leg (`Links4`, which `links4_sigH` derives from `Gaps4`) needs the same. **`nodeRunRL4`**
  gives `StmtN4R` on the run's own chain at `ch := rsvL (.node κ) es`:
  - `PubCellsR4` from RS0's `Pub`, and `truthChild4` from E1's entry doom (`X4.rsv_of_tail`);
  - the two zero outputs from `R4.rsvZero4` on the run.

  `hL_of_resR` and `hL_of_sigR` are `hL_of_res`/`hL_of_sig` with `hRes` over `StmtN4R`.

### 1.1 What `Gaps4` reduces to (`gap4Imp_of_rsv`, a theorem, not yet the hypothesis)

At every key and every `StmtN4R` witness (the parts still open are in bold):

- **`RepOk rt`**: the replay, kept explicit as instructed.
- **The folds** `repIRows4 rt κ v ⊆ nodeIRows4 κ` and `askIRows4 (withRsv Aq) κ v b ⊆ nodeIRows4 κ`.
- Then, per active slot `v` and selectable `ι`:
  - **`ATOk … (Aq π) …`**: the ask templates (ASK-P);
  - **`SlotRunA (rt π) (withRsv Aq π) …`**: aux facts, the residual imports
    `impAP rt (withRsv Aq) π` (they exclude asks, `Aq`-covered ops, `input` and **slot 0's `evalM`**),
    and the foreign flags.

`withRsv Aq π := (withInp Aq π).add (AT.rsv (Xof π) π)`.

`Gaps4` was not restated in this decomposed form. It is logically stronger than `SlotImp`: it names
templates. So it would be growth, not shrink, under the converse test IMP used. The switch to the
decomposed form is left for when its parts are proved.

## 2. Statement changes

| declaration | change | reason |
|---|---|---|
| **`Sub4.Gaps4`** | `∀ vk κ w c₁ c₂, StmtN4 … →` → `∀ vk κ w c₁ c₂ ch, StmtN4R … ch →` | **shrink** (`gaps4_of_N`): the reserve's cells and the true child claim are available |
| `Sub4.gap4_of_gaps` | `hS : StmtN4R … ch` (was `StmtN4`) | follows `Gaps4` |
| `Sub4.resid4H_of` | returns `R4.Resid4HR` (was `Resid4H`); its slots over `StmtN4R` | RSV-S3 §5.5 |
| `Sub4.certificate_sub4` | text unchanged; proof via `certificate_rev4HR` | RSV-S3 §5.5 |
| `Sub4.resid4H_of_gaps`, `Sub4.resid4H_sigH` | return `Resid4HR` (no other users) | follow `resid4H_of` |
| `Sub4.links4_of_gaps` | text unchanged; proof via `hL_of_sigR` | `Gaps4` over `StmtN4R` |
| `Open4`, `Open4F`, `open4_of_F`, `certificate_sub4F`, `certificateR_sub4F`, `certified` | text unchanged; meaning shrinks with `Gaps4` | — |

**New** (FRNodeLinks4/Run):
- `Snd.L4.nodeRunRL4`, `Snd.L4.hL_of_resR`, `Snd.L4.hL_of_sigR`;
- `Sub4.gaps4_of_N` (the converse).

The old `hL_of_res`/`hL_of_sig` are kept unchanged.

## 3. `FRNodeRsvLink` (new): the reserve as an ask template

- **`AT.rsv X π`**:
  - It covers `evalM` ops at prototype 0 (`cov op := π == 0 && isEvalM op`).
  - **Its rows** (`rsvRowsT`), per kind:
    - the row point's slot must be `af 32` on the cells `tauC j` (`rsvRel[0,23) ‖ rsvRel[48,57)`);
    - the column point's slot must be `af 25` on `sigC j` (`rsvRel[23,48)`);
    - the outputs must be three `F` slots on `rsvC 57…59`.
  - **Per component:**
    - no row if the component is syntactically that cell (`eqRowIf`; the compile's layout per
      `rsvcells.py`, so the honest fold adds **0 rows**);
    - otherwise one row `1·(l − c) = 0`;
    - `failR` if a slot has the wrong shape.
- **`atImp_rsv`** gives `ATImp` given two facts:
  - `impl.evalM = (implN4F base ν).evalM`;
  - the cells hold a true claim (`RsvCells w ch ∧ truthChildV srcE4 ch`).

  Proof: from `AskCtx`'s `InvK` at the op, the operands are `ch`'s `p_x ‖ s` and `p_y` (`argRows_ev`,
  `af_of_rep`). `N4c.evalM_childV` then gives `X₃`, and the output rows put `X₃` on the import cells.
- **`rsvCells_slot0`**: at a kind with a previous node, `PubCellsR4 κ w ch` gives
  `RsvCells (slotAsg κ 0 w) ch` (`oneCell_rsv`: `κ.oneCell = 3·2^logM`, by `decide` per kind).
- **`atImp_rsv_slot`**: the template's `ATImp` at every slot of a node meeting `StmtN4R`. At slot 0 of
  `N2`/`N4` it uses the reserve; elsewhere the template covers nothing.
- **`gap4Imp_of_rsv`**: IMP's `gap4Imp_of_runS` at `withRsv Aq`, with
  `atOk_add (atOk_add hAq (atImp_inp …)) (atImp_rsv_slot …)`.

**Why no prefix form (deviation from RSV-S3 §5.4).**
- `compileFromX_run` already threads the invariant. At a covered op `ATImp` receives `InvK w cs regs ι`
  at the op's own compile state and registers, which is the run's prefix.
- So a template covering `evalM` sees its operand registers' values without any prefix lemma. Making
  the reserve an `AT` summand both removes the outputs from `impAP` and supplies their `RepS`.
- `execA_prefix` is unchanged and unused here.

**Controls** (`FRNodeRsvLink`):

| Definition | (+) | (−) |
|---|---|---|
| `AT.rsv` | `atRsv_cov` (prototype 0's `evalM`) | `atRsv_cov` (not prototype 1's, not `evalL`) |
| `eqRowIf`, `argRows` | `eqRowIf_ctl`, `argRows_cells` (on its cells: no row) | `eqRowIf_ctl` (another cell: one row) |
| `atImp_rsv` (`RsvCells`/`truthChildV` load-bearing) | — | **`atImp_rsv_neg`**: the setup is a concrete `CS` with the reserve layout (rows empty) at `wCtl`, and an `evalM` returning `X₃[1] = 1`. `ATImp` fails there. |

## 4. The foreign flags (`SlotRunA`'s third conjunct)

Dumped from the compiled prototypes by `fr-build-SRA/probe/ForsDump.lean` (dev-only executable;
`logs/SRA/forsdump.log`, `forsctx*.log`, `forsorigin.log`). Prototype 0 has 15 flags (154,920 ops,
147,077 registers); prototype 1 has 79. That is INT-9's 12 / 79, and prototype 0 has grown by 3.

### 4.1 The classes

| Class | p0 | p1 | The flag | What discharges it |
|---|---|---|---|---|
| `assertEq (piField 0 48 1) (const)` (reg 10) | 1 | 1 | byte 48 of the slot's proof is the kind byte | a kind fact on `slotIn`'s `π` (A1′'s `kindS`/`kindN` read that byte off the stream): needs `π`'s byte 48 = stream byte, ASK-P's positional spec |
| `assertZero (piField 0 o len)`, bytes of the proof | 13 | 78 | `act ι → π[absOff 0 o, +len) = 0` (padding: `fEEnd[64,112)`, `fLrEnd[48,1008)` where `rsv` is off, the 48-byte zero tails of each `fLv` level, the zero-length `piField 0 74144 0`, `72096`/`71072` 2048/3072-byte tails) | where `act ι` is false, `flagOf` is `true` trivially; otherwise **zero pins on the arena₁ cells** of those bytes (≈ len/16 rows each) and the bridge "proof bytes = stream bytes" |
| **`assertEq` of an untracked `mulK` against `keep` (p0 reg 100345)** | 1 | 0 | the (β′) cap check's batched MAC equation | **none today**: §4.2 |

The `assertZero` flags that are `act`-gated (`falsetruefalse`, `falsefalsetrue`, `falsetruetrue`)
hold for free at the other indices. A one-line lemma on `flagOf … (.assertZero a act)` with
`act ι = false` gives it; it was not added because nothing consumes it before ASK-P's pins exist.

### 4.2 Finding: (β′)'s cap-check equation is not enforced by any row (prototype 0)

- At op#101817–101821, five `keep act n o` ops select between `packK` arrays of different lengths
  per kind (AK19/AK18, AK16/AK15, AK13/AK12, AK10/AK9, AK25/AK24).
- `opOut`'s `keep` requires `t = t'`, so these get `skip 1`, an untracked slot.
- From there an 852-register chain is untracked (815 `addK`, 31 `mulK`, 4 `keep`, 1 `getK`, 1
  `mulKF`; `forsorigin.log`). It ends in `assertEq 100344 52605` at op#109053, which compares that
  chain with a tracked `keep`. The comparison is foreign.
- So the circuit has **no row** for this equation: the MAC sum over the cap entries
  (`piElemK × getK (eqTableK …)`). It is (β′)'s batched check, the only binding of the 871 cap reads
  `piDigestAt` (B3 §6 Q3).
- `SlotRunA`'s flag conjunct makes it a hypothesis, so nothing unsound is *claimed*. But it can never
  be discharged from rows as compiled.
- **Fix options** (owners: the compile, `FRVIRCompile`, or R1/R3's templates):
  1. compile `keep` over `af`/`ak` arrays of unequal lengths by zero-padding the shorter to the
     longer and emitting `muxOut` (the semantics must agree: `Val.ak` of the shorter array);
  2. make the generator emit equal-length arrays (pad the `packK` lists to the kinds' maximum).

  Either turns the chain into rows (≈ 850 registers, mostly linear `addK`, so a few hundred rows).

## 5. Build, axioms, kernel time

- **Build** (`logs/SRA/build-full.log`): `lake build FR Solution FRSubmission4Fin FRNodeRsvLink`,
  **2,649 jobs, green, 0 `sorry` warnings**. Baseline at HEAD before any edit: green, 2,648 jobs
  (`base-build.log`).
- **Axioms** (`logs/SRA/axioms.log`): 22 declarations, among them `RecursionFast.Challenge.certified`,
  `certificate_sub4(F)`, `gap4Imp_of_rsv`, `atImp_rsv`, `nodeRunRL4` and `atImp_rsv_neg`. All
  ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, and no `sorryAx`.
- **Kernel time.** Sequential profile, one core (27), `Elab.async=false`, load ≈ 3
  (`logs/SRA/prof-summary.txt`, `profile-<m>.log`). The figures are type checking / tactics:

  | module | kernel | tactics | before |
  |---|---|---|---|
  | `FRNodeRsvLink` (new) | 0.50 s | 1.10 s | — |
  | `FRNodeLinks4` | 0.09 s | 0.27 s | — |
  | `FRNodeLinks4Run` | 1.02 s | 0.27 s | 0.98 s (HEAD text, same run: `profile-FRNodeLinks4Run-HEAD.log`; the time is HEAD's) |
  | `FRNodeLinks4Sub`, `FRNodeLinks4SigH`, `FRSubmission4Fin` | < 0.01 s | — | — |
  | `FRSubmission4Cert` | 0.03 s | 0.03 s | 0.03 s (IMP) |

  New kernel time is about 0.55 s. All of it is off `certified`'s path except `nodeRunRL4`/`hL_of_resR`
  (≈ 0.05 s); `FRNodeRsvLink` is not imported by the certificate. There is no `decide` over a row list
  or a program. `oneCell_rsv` is `decide` per kind (3 closed equations), and
  `tauC_ne`/`sigC_ne` are `decide` over 32/25 literals, in the control only.
- **Code lines** (core `loc.py`, code / thm, HEAD → now): `FRNodeRsvLink` new 219 / 21;
  `FRNodeLinks4` 147 → 197; `FRNodeLinks4Run` 105 → 120; `FRSubmission4Cert` 59 → 64;
  `FRNodeLinks4Sub` 18 → 18; `FRNodeLinks4SigH` 18 → 18; `FRSubmission4Fin` 12 → 12.

## 6. What remains, and the exact requests

**To the orchestrator:**
1. `FR.lean`: add `import FRNodeRsvLink`. It is not on `certified`'s path, but its theorems and
   controls should be on `FR`'s build.
2. The finding in §4.2: route it to the compile's owner (or to R1/R3).

**To ASK-P** (the arena-side facts `SlotRunA` and the folds need, stated on the answer-driven run
`s` of prototype `π` on `slotTr4 κ v w`, at `inp = slotIn …`):

1. **The fold of the reserve's rows.** `askIRows4 (withRsv Aq) κ v b ⊆ nodeIRows4 κ`. With the
   compile's layout the reserve contributes no rows, so this is the claim that prototype 0's `evalM`
   operand and output slots *are* the `rsvRel` cells at every kind. `rsvcells.py` checks it; the plan
   (B5) can check it at process start. A kernel proof needs a compile fact, which is the same
   obligation as `inp_cells`/`AT.inp`'s pattern. If the compile ever differs, one row per differing
   component is folded instead (`eqRowIf`).
2. **The aux facts**, per `a ∈ (protoCS π).aux`:
   ```lean
   a.1.1.map (Lin.ev (slotAsg κ v w)) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)
   ```
   - `felems n`: the aux cells are arena₂ cells of the column payload. Needed lemma: for the
     `dotKF` operand `col` (a `piField fCols …`), `rd regs col = .b (π.extract …)`, and the arena₂
     cells hold `F.ofBytes` of those bytes, 16 by 16.
   - `bits 20`: the cells are the L position bits `p·maxb + h`. Needed lemma: those L cells hold the
     bits of the `idx` register's value (a squeeze answer's bits, `bitOf`).
3. **The foreign flags** (§4.1):
   - (a) For each `assertZero (piField 0 o len)` with `act ι`: arena₁ cells
     `[(absOff 0 o)/16, …)` of the item carrying those bytes are pinned to `0`, plus the positional
     spec `π.extract (absOff 0 o) (absOff 0 o + len) = stream bytes …` (`reassemble4`'s per field).
   - (b) The kind byte: `π[48] = kindByte (kindP π ι)` from the same positional spec and A1′'s kind
     rows.
   - The per-flag list with offsets is `logs/SRA/fors-list.txt`.

   Register provenance (which op produced an `assertZero`'s operand) is a fact about the 155 k-op
   program. A kernel proof wants a cheap form: a byte-register invariant along `execA`, so that every
   `piField` register holds its bytes, plus the dump's op indices. That machinery is shared with the
   ask templates' `prev_piField`, so it is best built once in ASK-P's positional module.
4. **The residual imports** `impAP rt (withRsv Aq) π`: whatever `Aq` and the replay do not cover.
   This track removed `input` (IMP) and slot 0's `evalM`.

**Kept explicit, as instructed:** `RepOk rt` and the replay fold (`hfoldR`); nothing was switched to
C1's `RTOkW`.

## 7. Files

- New: `submissions/flock-recursive/lean/FRNodeRsvLink.lean`.
- Edited: `FRNodeLinks4.lean`, `FRNodeLinks4Run.lean`, `FRNodeLinks4Sub.lean`, `FRNodeLinks4SigH.lean`,
  `FRSubmission4Cert.lean`, `FRSubmission4Fin.lean` (doc).
- Docs: `stages/SRA-RESULT.md`, `stages/SRA-JOURNAL.md`.
- Build tree only (dev): `logs/fr-build-SRA/probe/ForsDump.lean` (+ its `lean_exe` entry), `ax/AxSRA.lean`.
