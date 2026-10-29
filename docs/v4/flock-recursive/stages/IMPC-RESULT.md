# IMPC (track L-circ): RESULT — static proof reads, challenge conversions, zero-pinned flags, column words

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `74a2528`, re-snapshotted onto
**`44a4975`** (CK) for the final build. Build tree `logs/fr-build-IMPC` (copy of `fr-build-ASKP`;
`MINE.txt` = my three modules, everything else HEAD's text). Logs `logs/IMPC/`; journal `IMPC-JOURNAL.md`.
Every lake/lean/probe ran in a 16 GB scope under `timeout`. No sub-agents, nothing committed, no `sorry`
in the worktree. **No existing module was edited.**

## 0. Summary

| Item | State |
|---|---|
| `ATImp` proof fields: static `piElem`/`piElemK`/`piDigest` whose 16-byte windows are stream elements | **Done**: `atImp_impc` given `PfCells`, and `pfCells_of_rows` from `StmtN4`. Per prototype it covers 4,199/4,201 `piElem`, 1,891/1,891 `piElemK` and 872/8,300 `piDigest`. The uncovered reads are the siblings and four unaligned statement reads (§5) |
| `ATImp` `chF`/`chK` | **Done**: bound to the answer register's own cells, through `InvK`. 291 + 31 per prototype |
| `ATImp` cap reads under (β′) | **Done, as proof fields**. (β′) leaves no `piDigestAt` in either prototype. The cap check reads `A`/caps (`piElemK`/`piElem`) and `D` (`piDigest`) at static offsets, and all of these are covered. Since CK (`44a4975`) the check's equation is rows |
| `ATImp` siblings (`l + r + a·cur`) | **Not done**: needs the position-bit decomposition (§5.1) |
| `ATImp` `bitOf` → bits | **Cannot be `ATImp`** (§5.2). The operand is an untracked `idx`/`shrN` register, and `ATImp` is generic over the register file. `bitOf` stays a residual import of `SlotRunA` |
| aux `felems` (column words) | **Done** (`colTG`, `aux_col`, `xof_felems`): 871/871 per prototype. It costs V (§3), so it is a separate generator |
| aux `bits 20` | **Not done**: 1,627 per prototype, same decomposition as §5.1 |
| SRA §6.3, the register invariant along `execA` | **Done generically**. `execA_prov`: a `piField`'s register holds its bytes on every answer-driven run, with no program evaluated. `trail_fors`/`trail_aux`: a compile flag or aux entry sits at a trail point whose template rows hold |
| SRA §6.3, foreign flags | **Zero pins done** (`flag_zpin`): p0 12/13, p1 77/78. **Open**: the stmt tag byte (1 per prototype) and the statement's zero tail (1 per prototype), both sub-element byte facts (§5.3) |
| Discharge | **`gap4Imp_of_impcR`** with `colTG`, **`gap4Imp_of_impc`** without it |
| Build | **`lake build FR Solution FRSubmission4Fin FRNodeRows4AskIR`: green, 2,667 jobs, 0 `sorry`** at `44a4975` plus my files (`logs/IMPC/build-full.log`) |
| Axioms | 23 declarations, `RecursionFast.Challenge.certified` included, all ⊆ {`propext`, `Classical.choice`, `Quot.sound`} (`logs/IMPC/axioms.log`, `fr-build-IMPC/ax/AxIMPC.lean`) |
| Source rule | 447 files, 0 findings (`logs/IMPC/source-rule.log`) |

## 1. What was built (`loc.py`: total / code / thm; `logs/IMPC/loc.txt`)

| module | lines | content |
|---|---|---|
| `FRNodeRows4AskI` (new, **below `FRNodeRows4`**) | 220 / 119 / 0 | Tables (`itOffA`, `itemsA`, `phasesA`, `phIxA`, `pSegs`). The locator `phItem`, `pfLoc`, `winE`. Rows `a1Row`, `pfRows`, `chRows`. Provenance `provL`/`provOf`, `winsOk`, `zRows`. Column rows `colRows`/`auxRows`. **`impcRows`/`impcCov`/`impcTG X π pv`**, **`colTG X π pv`** |
| `FRNodeRows4AskIS` (new) | 409 / 311 / 28 | Table lemmas, **`pfLoc_spec`**, `winE_spec`, **`win_slot`**, **`PfCells`**, **`pfCells_of_rows`**, `pfRows_ev`, `chRows_ev`, **`atImp_impc`**, **`atImp_col`**, `withImpc`, **`gap4Imp_of_impc`**, controls |
| `FRNodeRows4AskIR` (new) | 449 / 352 / 25 | `evalOp_len`, **`execA_prov`**, **`trail_fors`**, **`trail_aux`**, **`flag_zpin`**, **`aux_col`**, **`xof_felems`**, `zPin`, `colOk`, **`SlotRunI`**, **`slotRunA_of_impc`**, `withImpcC`, **`gap4Imp_of_impcR`**, controls |

### 1.1 The generator (`impcTG X π pv`)

The generator is a `TG` (ASK-P's), generic in the extension `X`, the prototype `π` and the program's
`piField` registers `pv = provL 0 (protoProg π).ops`. It is generic over the op trail (CK's row shift
changes nothing).

- **Static proof reads.** `pfLoc o` finds the field's phase part (`pSegs`), then the shape (`phItem`:
  seed, absorb, uni, rounds, columns; not the siblings). From these it gives the item `k` and the query
  byte `q` of proof byte `o`. `winE o` accepts a window `[o, o+16)` when four things hold:
  - its 16 bytes are query bytes `[q, q+16)` of one item;
  - `1 + itOff k + 8 + q ≡ 0 (mod 16)`;
  - the window lies inside the query;
  - the item is not in the last block.

  The window is then element `(1 + itOff k + 8 + q)/16`. A covered read gets one row per F component,
  `1·(l − A₁(e)) = 0`, at arena₁'s cell `π·2^20 + arA1 + e`. A shape mismatch gives `failR`. `cov` is a
  function of the op alone: `winE` succeeds for every window.
- **`chF a c` (`c < 2`), `chK a`.** The import cells are set equal to the answer register's slot
  `[a₀, a₁]` (no per-kind slot; otherwise `failR`).
- **Zero pins.** At `assertZero a act`, if `provOf pv a = some (f, o, len)`, `a <` the register count and
  `winsOk f o len` holds (`len ≡ 0 mod 16`, inside the proof, every window an element), the generator
  emits `gate act · A₁(e_t) = 0` for each window. If the compile made the op an import, it emits `failR`,
  which keeps `ATImp` vacuous there.
- **`colTG`.** At a `dotKF`, each `felems n` aux entry on a `piField` register (`r <` the register count)
  gets two kinds of row:
  - aux cell `b` equals arena₁'s cell of window `b` (`b < len/16`);
  - otherwise the cell is `0`.

  If the `dotKF` is an import, `colTG` emits `failR`.

### 1.2 The theorems, in words

- **`pfLoc_spec`**: for every trace, proof byte `o` of `reassemble4 seq4 tr` is query byte `q` of entry
  `k`. Per shape this goes through ASK-P's `reassemble4_byte` and `ctb4_*`, with `itemsOf_phIx` for
  `k < 8,783`.
- **`win_slot`**: at an active slot, a window `winE` accepts is its element's H cell (`slot_qelem`), in
  arena₁'s range. **`pfCells_of_rows`**: `StmtN4` gives `PfCells` at every active slot, via `a1_slot`.
- **`atImp_impc (h : PfCells w π inp) : ATImp impl X (impcTG X π pv).toAT κ inp w`**. **`atImp_col`** needs
  no hypothesis.
- **`execA_prov`**: `execA … ops s0 tr = some (s, _)` and `(r, f, o, len) ∈ provL s0.regs.size ops` give
  `s.regs[r]? = some (.b (π.extract …))`.
- **`trail_fors` / `trail_aux`**: every compile flag or aux entry `p` has a trail point `c` with
  `c.slots.size = p.2`, at which the template's rows for that op lie in `askRowsX`.
- **`xof_felems`**: in `Xof π`'s compile, only a `dotKF` carries a `felems` aux. The proof goes through
  `tplExt`, `tplExtKM` and CK's `extGetK`.
- **`slotRunA_of_impc`**: `SlotRunA` follows from five things:
  - the template contains `impcTG`'s and `colTG`'s rows;
  - the rows hold at the slot;
  - `PfCells`;
  - `|π| = piSizeOf seq4`;
  - the residual **`SlotRunI`**. This is `SlotRunA` with the aux conjunct restricted to `colOk = false`
    and the flag conjunct to `zPin = false`. The residual-import conjunct is unchanged, over `impAP`,
    which no longer contains the covered classes.

**`gap4Imp_of_impcR`** (the composable discharge), with `withImpcC Aq π := ((withRsv Aq π).add impcTG).add colTG`:

```lean
theorem gap4Imp_of_impcR (hT₀ hT hok) (hpf : PfHdr X.pf4) (hpv : PfView X.pf4) (hfoldR)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withImpcC Aq) κ v b, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      ATOk … (Aq (protoOf κ v)) … ∧ SlotRunI (rt π) (withImpcC Aq π) … ) :
    ∀ v, Active4 (rd4 X.pf4) κ w v → SlotImp impl₀ base κ v w (slotIn …) ((rd4 X.pf4).slotTr κ v w)
```

`gap4Imp_of_impc` is the same without `colTG`: `withImpc`, residual over `SlotRunA`.

## 2. The `askTG` edit (for the orchestrator, after ASK-T lands)

In `FRNodeRows4.lean`, add `import FRNodeRows4AskI` (it imports only `FRNodeRows4AskPosT` and
`FRNodeKinds4`), then make the generator:

```lean
def askTG (π : ℕ) : TG :=
  ((((ASK-T's generator).add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)).add
    (impcTG (XofT π) π (provL 0 (protoProg π).ops))).add
    (colTG (XofT π) π (provL 0 (protoProg π).ops))      -- optional: the column words, §3
```

For `withImpcC` the fields must also line up on the high side:
- `withImpcC Aq π` is literally the `AT` of this generator: `withImpc` uses `Xof`, which is `XofT`'s body,
  and `pvP π = provL 0 (protoProg π).ops`.
- `askFold` then applies with `hA := fun π _ => ⟨rfl, rfl⟩`. The controls `withImpc_none` and
  `withImpcC_none` check this by `rfl` against local copies (`askTGI`, `askTGIC`) of the edited `askTG`.

**Collateral (ASK-P/ASK-T's `FRNodeRows4AskPosF`).** `withRsv_none` and `askFold_rsv` state that `askTG`
is `withRsv (fun _ => AT.none)`. After the edit they must be restated at
`(withRsv (fun _ => AT.none) π).add (impcTG (Xof π) π (provL 0 (protoProg π).ops)).toAT` (plus `colTG`),
which is my `withImpc(C)` at `Aq = fun _ => AT.none`. The certificate's `Gaps4` route then calls
`gap4Imp_of_impcR` in place of `gap4Imp_of_rsv`.

## 3. Measurements (`logs/IMPC/`, core 28, load 2–4)

| | `impcTG` | `+ colTG` |
|---|---|---|
| rows per prototype | 11,043 (p0) / 11,108 (p1), 0 `failR` | 38,899 / 38,964, 0 `failR` |
| `askV` per prototype (V, sparse) | **16–18 ms** | 54–57 ms |
| V per node with both prototypes (N2, N4) | **≈ 34 ms** | ≈ 110 ms |
| plan init (fold into `askTG`'s trail, `impcinit.log`) | **+0.1–0.3 s per prototype** | +0.8–0.9 s per prototype more |
| grouping (`grows`) at plan init | 25 ms | 150 ms |

Sources: `impcstat-ck.log`, `impcv-ck.log`, `impcinit.log`. `askV` is the plan's evaluator for the
template rows (`FRNodeRows4Plan.askV`), measured standalone on the generator's rows indexed as `askPI`
would index them.

- The arena template range `arR2N = 132,096` holds both generators: 8 + 11.1 k + 27.9 k rows.
- **Recommendation**: fold `impcTG` now (≈ 34 ms V per node, +0.4 s plan init).
- `colTG` costs ≈ 75 ms V per node more. That is beyond "tens of ms", at ≈ 1.4 µs per 3-entry copy row.
  The cheap route is either of:
  - aliasing in the compile: `tplExt`'s `dotKF` aux cells := arena₁ cells, 0 rows; owner the compile/templates;
  - a structured evaluator for these copies, one diagonal block per instance like `a1V4`, in
    `FRNodeRows4Plan`.

  Until then, `gap4Imp_of_impc` (without `colTG`) is the composable form, and the column words stay in
  the residual.
- No V measurement with `askTG` actually edited was made (that requires rebuilding everything above
  `FRNodeRows4`). After the edit, re-run `plan4t init`, MxKat (its reference `askV` input changes) and V(N4).

## 4. Kernel time (`lean -DElab.async=false --profile`, one core, `prof.sh`, `profile-*.log`)

| module | type checking | tactics | wall (mostly import) |
|---|---|---|---|
| `FRNodeRows4AskI` | 0.04 s | — | 7.0 s |
| `FRNodeRows4AskIS` | 0.39 s | 1.11 s | 10.7 s |
| `FRNodeRows4AskIR` | 0.76 s | 2.63 s | 14.8 s |

New kernel time is ≈ **1.2 s**. No declaration exceeds the profiler's 100 ms threshold. No `decide` runs
over the format, a program or a table. The window checks (`winE`, `winsOk`) are computed at process
start, never in the kernel: soundness is stated for whatever windows they accept. None of these modules
is on `certified`'s path until the orchestrator routes `Gaps4` through `gap4Imp_of_impcR`. When that
happens the cost is ≈ 1.2 s plus the `askTG` fold.

## 5. What remains (exactly), and the foreign flags

Per prototype, after `gap4Imp_of_impcR`.

**Residual imports (`impAP`)**:
- the siblings, ≈ 7,428 `piDigest` in `fSibs`;
- `bitOf`, 15,265 / 15,283;
- the four unaligned statement reads: π 49, 65 (`piElem`); 49, 81 (`piDigest`), i.e. stmt bytes 1–32
  (`h`) and 33–40 (`enc64 n`);
- every non-ask import that neither the replay nor ASK-T covers.

**Aux**: the 1,627 `bits 20` entries.

**Foreign flags** (CK: p0 14, p1 79):
- p0: 12 zero-pinned, 2 open;
- p1: 77 zero-pinned, 2 open.

The open ones are listed in §5.3.

### 5.1 Siblings and `bits 20`: the position-bit decomposition (design, not built)

The sibling's value is a function of the trace alone: `sib4 … (posOf4 … phAns p) q` is the node query's
half not at bit `h` of the position, or zero at an inactive depth. So it is `ATImp`-able once a cell holds
that bit. The plan:

- **Bit cells.** For each P2 answer half `H` (62 answers × 2 halves), add a row
  `1·(H − Σ_{j<128} e_j·b_j) = 0`.
  - `e_j ∈ F` is the unit vector of bit `j`. `F` is `GF(2^64)[y]` on two `UInt64`s and addition is XOR,
    so `Σ b_j e_j` with `b_j ∈ {0,1}` is the element with those bits, and the decomposition is unique.
  - The `b_j` sit in ASK-P's bits area (`arBt`, 8,320 cells, Boolean by `bit_slot`).
  - **The area is too small** for 62 × 256 = 15,872 bits. Either it grows, or the bits go to L as PACK
    planned (7,552 in L, an L-owner change).
- **Siblings.** A kind-gated mux needs an auxiliary product cell per kind-varying depth. At an active
  depth, `sib = r + bit·(l − r)`; at an inactive depth, `0` (the `assertZero` already present). This also
  needs `trM4` (the trace's seed kind byte) equal to the selector's kind. That is A1′'s `kindS`/`kindN`.
- **`bits 20`.** The aux cells equal the `idx` register's bits. The value comes through provenance
  (`execA_prov`'s pattern, extended to `idx`/`shrN` registers, whose values are functions of an answer
  register) and the bit cells. **`bitOf`** is the same: rows at the following `selectHalf` (where
  `pre = bitOf`) can tie the `bitOf` import cell to the bit cell, while `bitOf` stays in `impAP` and is
  discharged on the run.

### 5.2 Why `bitOf` is not an `ATImp` class (B3's table listed it)

`ATImp` quantifies over every register file meeting `InvK`. `bitOf n h`'s operand `n` is an `idx`
(`skip 1`) or `shrN` (`skip 1`) register, whose slot is `none`, so `InvK` leaves its value free. Its
`PrevOk` covers only the previous op (`piDigest` in `merkleOps4`). Hence no template can make `ATImp`
hold at a `bitOf`. The binding must go through `SlotRunA` on the concrete run, as in §5.1.

### 5.3 The open foreign flags

Both prototypes have two open flags:
- **The statement tag byte** (`assertEq (piField 0 48 1) const`, register 10 in SRA's list): one byte,
  π 48, which is stmt byte 0, element 0 byte 0.
- **The statement's zero tail.** In p0 (node), `assertZero (piField 0 113 63)`: stmt bytes 65–127. In
  p1 (segment), `piField 0 89 87`: stmt bytes 41–127.

Each starts mid-element: the stream elements of the stmt message begin at stmt byte 0, and 65 and 41 are
not ≡ 0 (mod 16). A byte-level fact inside an element is not F-linear, so it needs one of:
- the stmt element's bit decomposition (as §5.1, 16 elements); or
- a lemma from the `hashA`/`hashB` statement blocks, if their message words are cells (IMP's
  `stmtRowsS`/`P` tie stream elements 13–20 to the block messages).

The aligned part of the zero tail (whole elements 5–7 / 3–7) could be pinned with the current machinery.
The flag, however, needs every byte.

## 6. Cells and rows E1 must fill

- **No new cells.** The covered import cells take their true values; the arena₁ cells are already
  E1's (ASK-P §7).
- After the `askTG` edit, the template rows at `π·2^20 + arR2 + k` gain:
  - ≈ 11.1 k rows per prototype for `impcTG`: `1·(import − A₁(e)) = 0`, `1·(chF cell − answer half) = 0`,
    and the zero pins;
  - ≈ 27.9 k more for `colTG`.
- They hold on honest witnesses:
  - the import cells hold the windows;
  - the pinned elements are zero bytes when `act`;
  - the `dotKF` aux cells are the column words.

  `impcstat-ck.log` shows 0 `failR` on the real compile.
- **Re-dump the plan form**: `protoV4`'s value changes.

## 7. Controls

| Definition | (+) | (−) |
|---|---|---|
| `impcCov` | `impcCov_ctl`: `chF 0 0`, `chK` covered | `chF 0 2`, `input` not covered |
| `chRows` | `chRows_ctl`: a digest slot gives the row tying the first half | an untracked register gives `failRT` |
| `a1Row` / `PfCells` load-bearing | (rows hold where `PfCells` holds: `atImp_impc`) | `a1Row_neg`: the import cell `≠` the arena cell breaks the row |
| `provL` / `provOf` | `provL_ctl`: registers 0 and 2 of `[piField, input, piField]` | register 1 (`input`) has none |
| the zero-pin flag | `flag_ctl`: zero bytes give `true` | a nonzero byte gives `false` (what the pins exclude) |
| the edit composes | `withImpc_none`, `withImpcC_none` (`rfl`) | — |
| completeness on the real compile | `impcstat-ck.log`: 0 `failR`; 12/77 flags, 871 `felems` bound | — |

## 8. Open items for the orchestrator

1. The `askTG` edit and the `AskPosF` restatement (§2). Route `Gaps4` through `gap4Imp_of_impcR`, or
   `gap4Imp_of_impc` while `colTG` waits on V.
2. `colTG`'s V cost (§3): alias the `dotKF` aux cells in the compile, or evaluate them structurally.
3. The position-bit decomposition (§5.1) for the siblings, `bits 20` and `bitOf`. It needs ≈ 15.9 k bit
   cells: the bits area (8,320) grows, or L holds them.
4. The two stmt flags and the four unaligned statement reads (§5.3), at the byte level.
5. ASK-P §6.1 (the stream's last block): `winE` refuses items in the last block, so none of my bindings
   depends on it.

## 9. Files

- New: `submissions/flock-recursive/lean/FRNodeRows4AskI.lean`, `FRNodeRows4AskIS.lean` and
  `FRNodeRows4AskIR.lean`.
- Docs: `docs/v4/flock-recursive/stages/IMPC-RESULT.md`, `IMPC-JOURNAL.md`.
- Build tree only (dev): `logs/fr-build-IMPC/probe/ImpcStat.lean`, `ImpcV.lean` and `ImpcInit.lean`,
  `logs/fr-build-IMPC/ax/AxIMPC.lean`, `logs/fr-build-IMPC/scratch/AuxT.lean`.
- **`FR.lean` (orchestrator)**: `import FRNodeRows4AskIR`, which pulls `AskIS` and `AskI`.
