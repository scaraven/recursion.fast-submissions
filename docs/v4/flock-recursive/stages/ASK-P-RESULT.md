# ASK-P (track L-circ): RESULT — the arena folds into `nodeIRows4`, the reader's and `reassemble4`'s positional specs

Worktree `recursion.fast-submissions-rev44` (`v4/rev44`). Started at `616b57c`, re-snapshotted onto
**`24ee435`** (SRA `27459d9` + R3) for the final build. Build tree `logs/fr-build-ASKP` (copy of `fr-build-IMP`;
`MINE.txt` symlinks my modules). Logs `logs/ASKP/`; journal `ASK-P-JOURNAL.md`. Every lake/lean/probe ran
in a 16 GB scope under `timeout`. No sub-agents, nothing committed, no `sorry` in the worktree.

## 0. Summary

| Item | State |
|---|---|
| 5. folds into `nodeIRows4` | **Done**: per slot `slotRows4 ++ arIRows4 ++ linkIRows4`; `arIRows4` = arena₁ (`a1Rows4`) ++ the slot prototype's **template rows** (`askRowsT`, at `v·2^20 + arR2 + k`) ++ the bits (`bitRows4`), under the checked fit `ArFit` (else one rejecting row). **`a2Rows4` (B2″'s `ALv` binding) is not folded**: the binding's row range holds the ask templates' own rows (§1.2) |
| plan / V | **Done**: `evalMT4_eq`, `evalMX4_eq`, `implN4F_hMX`, `slots_val`, `hfit4`, `linkV4_eq` **textually unchanged**; `inR true`; MxKat PASS; `plan4t check` equal (§3) |
| 4. arena₁ bridge (prototype frame) | **Done**: `a1_slot`, `bit_slot` (from `StmtN4`'s rows) |
| 1. reader's positional spec | **Done**: `readItems_getElem?`, `slotTr4_getElem?` |
| 2. element alignment | **Done**: `itOff_al`, `ans_al`, `itOff_le`, `slot_byte`, `slot_ans(A)`, `slot_qbyte`, `slot_qelem(A)` |
| 3. `reassemble4` per field | **Done**: `reassemble4_byte` + per shape (`ctb4_seed/absorb/uni/rounds/cols/sibs`), `itemsOf_phIx`, `slotπ_byte`; composite `slot_pfAbsorb` |
| SRA §6.1 (reserve fold) | **Done**: `askFold_rsv` (`withRsv (fun _ => AT.none)`), generic `askFold` |
| SRA §6.2–6.3 | partly: zero pins / kind byte of absorb fields via `slot_pfAbsorb`; `felems`, `bits 20`, the byte-register invariant **open** (§6) |
| build | **`lake build FR Solution FRSubmission4Fin FRNodeRows4AskPosR` green at `24ee435` + mine** (2,658 jobs, 0 `sorry` warnings, `logs/ASKP/build-final.log`) |
| axioms / source rule | 67 declarations incl. `certified` ⊆ {propext, Classical.choice, Quot.sound} (`axioms.log`, `fr-build-ASKP/ax/AxASKP.lean`); source rule 439 files, 0 findings (`source-rule.log`) |

## 1. The fold

### 1.1 Why a restated generator (`FRNodeRows4AskPosT`, new, below `FRNodeRows4`)

B3's `AT`/`askRowsX`, IMP's `AT.inp` and SRA's `AT.rsv` live above `FRNodeRows4` (they import the
soundness chain, which imports `FRNodeRows4`), so `nodeIRows4` cannot name them. The low module
restates them exactly:

- `TG` (= `AT`'s two fields), `TG.none`, `TG.add`; **`trailRows`** = `askRowsX` verbatim.
- **`trailMS`**: the same fold with `compMSX`'s template memo, tail-recursive (reversed accumulator).
  **`trailMS_eq`/`trailMS_T`**: it is `trailRows`. This is what keeps process start cheap: without
  the memo every op rebuilds its template (`repRowsP`'s 131 s trap).
- `inpTG` (= IMP's `AT.inp` rows), `rsvTG` (= SRA's `AT.rsv` rows; `rsvCT`/`tauCT`/`sigCT`/`eqRowIfT`/
  `argRowsT`/`outRowsT` restate `FRNodeRsvLink`'s).

In `FRNodeRows4`: **`askTG π := (TG.none.add (inpTG (XofT π) π)).add (rsvTG (XofT π) π)`**, so that
`withRsv (fun _ => AT.none) π` has `askTG π`'s fields **by `rfl`** (`withRsv_none`). **ASK-T/IMPC:
replace `TG.none` by your generator** (defined below `FRNodeRows4`, e.g. in a module imported by
`FRNodeRows4AskPosT`); `askFold` then discharges `hfoldA` for `withRsv Aq` with `Aq π := (yourTG π).toAT`.

### 1.2 What `arIRows4` holds, and the deviation from B2″'s `a2Rows4`

`arIRows4 κ σ := if ArFit then a1Rows4 κ σ (slotB0 κ σ) ++ absRows4 κ (mvRows π σ (askPI π)) ++ bitRows4 κ σ
else [(arRej σ, rejR κ)]`, `π = protoOf κ σ`, `askPI π` = `askRowsT π` indexed at `π·2^20 + arR2 + k`.

- **`ArFit`** (`∀ π ≤ 1`): the prototype's rows lie below `π·2^20 + arR2`; at most `arR2N = 132,096`
  template rows; their cells in region `π` (`InSlot`). The plan checks it (on the pieces' intervals:
  `ivBelow`) and `arFit_of` derives it from the statement's rows (the rejecting row fails at `one = 1`).
  The rejecting row sits at the region's last index, which the link rows never reach
  (`linkRows4_length_le`).
- **B2″'s `a2Rows4` (structured `ALv` copies arena₁ → import cells) is not folded.** Its `ALv`s
  (windows, offsets) are a choice of which import cell takes which stream element: that is the ask
  template's binding, i.e. ASK-T's. With the orchestrator's "simplest correct" rule, the binding range
  `[arR2, arR2 + arR2N)` holds the **template rows themselves** (`askRowsT`), evaluated sparsely once
  per prototype through the copy identity. ASK-T can emit `cpRow one (answer cell) (π·2^20 + arA1 + e)`
  rows from its generator; `a1_slot` then gives "answer cell = stream element". `a2V4`/`a2V4_eq` stay
  available if a structured form is wanted later.
- Today's template rows: prototype 0 **8** rows (4 `input` ops × 2; the reserve's 0 rows), prototype 1
  **6** rows (`ArTime`: `ar0 8 ar1 6`).

### 1.3 Fit (`FRNodeRows4Fit`)

`ar_idx` (indices: `[arR2, arRb + arNb)` of the region if `ArFit`, else `arRej σ`), `ar_mem` (cells: M's or
the slot's H stream, `slotB0_cell`), `ar_nodup`, `slot_idx`, `link_idx`; `slot_mem`/`slot_nodup` now over
the three parts (the old ones kept as `slot_mem0`/`slot_nodup0`). **`hfit4`'s proof and statement are
unchanged.**

### 1.4 Plan and V (`FRNodeRows4Plan`)

- `Plan4` gains `ar0/ar1` (`arOf π` = `trailMS`, with `har`), `ag0/ag1` (grouped `askPI`, `hag`); `hR`
  now also gives `ArFit`; `inR` adds `ivBelow` for both prototypes, the two lengths and `inSlotB` of the
  template rows.
- `protoV4` adds `askV` (the template rows at the prototype's point, split tables over 21/23
  coordinates, sparse: one product per entry); `slotV4` adds **`arV4`** = `a1V4 + bitV4` per slot
  (B2″'s closed forms, a few automaton runs).
- Fallback `nodeIRowsP` with `arIRowsP` (rows-based `arFitB`; `arIRowsP_eq`).
- `slots_val` re-proved (copy identity over `protoRows π ++ askPI π`, `a1V4_eq`, `bitV4_eq`).
- `FRVerifierImplNode4F`: **unchanged** (only rebuilt).

## 2. Statement changes

| declaration | change | why |
|---|---|---|
| **`nodeIRows4`** (def) | per slot `slotRows4 ++ arIRows4 ++ linkIRows4` (was `slotRows4 ++ linkIRows4`) | the fold; `StmtN4`/`StmtN4R` now also assert arena₁, the template rows and the bits |
| `Plan4` (structure) | fields `ar0 ar1 har ag0 ag1 hag`; **`hR : inR → ProtoFit ∧ lowKeys ∧ ArFit`** | the plan's checks |
| `mkPlan4` | `+ (ar0 ar1) (har)` | — |
| `protoV4` / **`protoV4_eq`** | value and statement over `protoRows π ++ askPI π` | the template rows at the prototype |
| `slotV4` (def) | `+ arV4 κ t u σ` | arena₁ and bits |
| `nodeIRowsP` (def) | `+ arIRowsP` | fallback |
| `a1V_eq` | hypothesis `k + 7 ≤ m` → `k + 5 ≤ m`, `7 ≤ m` (**weaker**) | `N2` has `m = logM + 2 = 22 < 24` |
| `a1V4_eq` | `24 ≤ m` → `22 ≤ m` (**weaker**) | same |
| `slot_mem`, `slot_nodup` (Fit) | over the three parts; old texts as `slot_mem0`, `slot_nodup0` | — |
| `slotRows_hold` (`FRNodeSound4`), `linkRows_hold` (`FRNodeSound4R`) | **proof only** (via `mem_node_slot`/`mem_node_link`) | the new append shape |

Unchanged in text: `evalMT4_eq`, `evalMS4`, `slots_val`, `evalMX4_eq`, `implN4F_hMX`, `hfit4`,
`linkV4_eq`, `planData4_rows`, `ProtoFit`, `SlotRows`, every `Gaps4`/certificate statement.

## 3. Measurements (load 2–6; another track's build ran part of the time)

- **`plan4t init`** (`plan4t-init-ab.log`, 5 alternating runs, core 29, user s): IMP's binary
  5.12–5.81 (median 5.35); **ASK-P 6.91–7.37 (median 7.07)**, wall ≈ 7.3 s: **+1.7 s** (the two memoized
  trail folds `arOf`), within the 3 s budget and under `ready_s` 10 s. Lever not taken: reuse
  `planData4`'s template memo (changes `planData4`'s type).
- **V(N4)** (`vtime-ab.summary`, `abv.sh`, 4 rounds × 21, core 27; IMP's binary vs mine, best ms):

  | | IMP | **ASK-P** |
  |---|---|---|
  | V(N4), own kind | 268.5 | **279.8** (+11) |
  | V(N4), all three kinds | 313.1 | **328.5** (+15) |
  | `evalMT4` N4 | 144.3 | 158.2 |
  | `evalMX4` all | 191.1 | 213.2 |

  Parts (`ArTime`, core 26): `a1V4` 0.22–0.29 ms and `bitV4` 0.3–0.5 ms per slot; `askV` 3.6 ms per
  prototype (its four eq tables).
- **Correctness at run time**: `plan4t check`: `evalMT4` = the sparse sum over `nodeIRowsP` (which
  holds every arena row sparsely): **N2 equal true** (sparse 422 s), **N4 equal true** (569 s); N8's sparse
  sum did not finish inside the 1,800 s timeout (`evalMT4` N8 best 288.6 ms under load in that run);
  **MxKat PASS** (`mxkat.log`; its reference slot value gains `arV4`).

### 3.1 Budgets (the orchestrator's corrected caps)

V per check ≲ 1.5 s VM, plan init ≲ 15 s VM: the fold costs **+11–15 ms of V(N4)** (arena₁ and bits
≈ 0.7 ms per slot, the template rows ≈ 3.6 ms per prototype, mostly their eq tables) and **+1.7 s of
plan init** (7.3 s wall in all). The template rows are sparse; when ASK-T's ≈ 40 k rows per prototype
arrive they cost ≈ 0.6 µs/row once per prototype (≈ 50 ms per node), not per slot.

## 4. Kernel time (`lean -DElab.async=false --profile`, one core, load 2–6; `cpu.txt`)

| module | type checking | tactics | before |
|---|---|---|---|
| `FRNodeRows4AskPosT` (new) | 0.05 s | 0.11 s | — |
| `FRNodeRows4` | 0.17 s | 0.15 s | 0.16 s (IMP) |
| `FRNodeRows4Fit` | **3.48 s** | 4.05 s | (8.45 s in my first version: `ar_mem`/`ar_idx` 2.4 s each, see below) |
| `FRNodeRows4Plan` | 1.05 s | 4.99 s | 1.03 s (B5) |
| `FRVerifierImplNode4F` (rebuilt only) | 1.13 s | 1.49 s | 1.19 s (B5) |
| `FRNodeSound4` / `FRNodeSound4R` | 0.06 / 0.24 s | 0.24 / 0.54 s | — |
| `FRNodeRows4ArenaRows` / `ArenaPlace` | 0.41 / 0.03 s | 0.71 / 0.04 s | — |
| `FRNodeRows4AskPosF` (new) | 0.09 s | 0.10 s | — |
| `FRNodeRows4AskPos` (new) | 0.81 s | 0.67 s | — |
| `FRNodeRows4AskPosR` (new) | 1.21 s | 1.51 s | — (largest declaration `reassemble4_byte` 0.25 s) |

New kernel time ≈ **+2.2 s** in new modules plus Fit's additions; no declaration of mine above 0.25 s
(`trace.profiler`, threshold 150 ms). **Trap found:** a proof that leaves `arN` (`= 4·chainLenOf seq4`)
among `omega`'s facts made the kernel evaluate the format (2.4 s per declaration); `rw [arN_eq]` before
`omega` removes it (B2″'s rule, now applied in `ar_idx`/`ar_mem`).

## 5. API (for ASK-T, IMPC, SRA)

**Folds (`FRNodeRows4AskPosF`, namespace `FR.N4s`)**
- `askRowsX_trail : askRowsX X P A cs pre k ops = trailRows X P ⟨A.cov, A.rows⟩ cs pre k ops`
- `askRowsP_eq (hc : A.cov = (askTG π).cov) (hr : A.rows = (askTG π).rows) : askRowsP A π = askRowsT π`
- `withRsv_none π : (withRsv (fun _ => AT.none) π).cov = (askTG π).cov ∧ … .rows = (askTG π).rows` (rfl)
- `arFit_of (hone : w κ.oneCell = 1) (hE : truthEI (nodeIRows4 κ) w) : ArFit`
- **`askFold (hA : ∀ π ≤ 1, (A π).cov = (askTG π).cov ∧ (A π).rows = (askTG π).rows) hone hE :
  ∀ v < κ.vslots, ∀ p ∈ askIRows4 A κ v arR2, p ∈ nodeIRows4 κ`** (B3's/IMP's/SRA's `hfoldA` at `b = arR2`)
- **`askFold_rsv hone hE`**: the same at `withRsv (fun _ => AT.none)` (SRA §6.1)
- `a1_hold`, `bit_hold`: the slot's arena₁/bit rows hold
- **`a1_slot hone hE (hv : v < κ.vslots) (he : e < arN) : slotAsg κ v w (protoOf κ v * slotM4 + arA1 + e) = w (sCell (slotB0 κ v) e)`**
- `bit_slot … (hj : j < arNb) : slotAsg … (π·2^20 + arBt + j) = 0 ∨ … = 1`
- `slotAsg_frame : slotAsg κ v w (protoOf κ v * slotM4 + c) = w (κ.oneCell + v * slotM4 + c)`
- `TG.toAT`, `mapC_comp`, `rowMapC_comp`

**Reader and alignment (`FRNodeRows4AskPos`, `FR.N4s`)** — `itOff k` = prefix sum of `seq4`'s item
stream lengths; `itAt k` = item `k`; `slotStr κ v w` = the slot's stream; `segIx κ v` its segment.
- `readItems_getElem? B its o k : (readItems B o its)[k]? = its[k]?.map (entryAt B (o + Σ_{j<k} slen))`
- **`slotTr4_getElem? : (slotTr4 κ v w)[k]? = (itemsOf seq4)[k]?.map (entryAt (slotStr κ v w) (1 + segIx κ v * strideB + itOff k))`**
- `entryAt_qbyte` (query byte `j` = stream byte `o + 8 + j`), `entryAt_abyte` (answer byte `j` = `o + 8 + qlen + j`)
- **`slot_byte (hv : Active4 (rd4 pf) κ w v) (hx : 16·⌊x/16⌋ + 80 ≤ segB) : (slotStr κ v w).getD (segIx κ v * strideB + x) 0 = (F.toBytes (w (sCell (slotB0 κ v) (x/16))))[x % 16]`**
- `itOff_al (1 ≤ k) : (1 + itOff k) % 16 = 0`; `ans_al : (1 + itOff k + 8 + (itAt k).qlen) % 16 = 0`;
  `itOff_le : 1 + itOff k + (itAt k).slen ≤ segB`; `itE k`, `ansE k` (the item's / answer's first element)
- **`slot_ans hv hk he hb : dlo e.2 = w (sCell (slotB0 κ v) (ansE k)) ∧ dhi e.2 = w (sCell … (ansE k + 1))`**
  (`hb : 1 + itOff k + (itAt k).slen + 64 ≤ segB`: not the last item, §6)
- **`slot_ansA hone hE hv hvs hk he hb`**: the same with arena₁ cells `slotAsg κ v w (π·2^20 + arA1 + ansE k (+1))`
- `slot_qbyte … (hj : j < qlen) : byteAt e.1 j = (F.toBytes (w (sCell (slotB0 κ v) ((1 + itOff k + 8 + j)/16))))[…]`
- **`slot_qelem` / `slot_qelemA`**: an aligned 16-byte query window is `w`/arena₁ of element `(1 + itOff k + 8 + j)/16`

**`reassemble4` (`FRNodeRows4AskPosR`, `FR.X`)** — `phIx S n` = phase `n`'s first item; `phAns S a n`.
- **`reassemble4_byte (hf : f < nFields4) (hn) (hj : j < bytesToL) : byteAt (reassemble4 S tr) (fieldOffOf S f + phaseOffOf S n f + j) = (ctb4 S (trM4 a) a (phIx S n) (phAns S a n) (phasesOf S)[n].2 f).getD j 0`**
- `ctb4_seed` (`hdr` = seed query bytes from 71), `ctb4_absorb`/`ctb4_uni` (query bytes from 40),
  `ctb4_rounds` (round `p`: item `ix + 2p`, bytes from 40), `ctb4_cols` (position `p`: item
  `ix + (1+sib)p`, bytes from 8), `ctb4_sibs` (`sib4` of node item `ix + (1+sib)p + 1 + h`)
- `itemsOf_phIx : (itemsOf S)[phIx S n + q]? = ((phasesOf S)[n].2.itemsL S.lv)[q]?`
- `slotπ_byte : byteAt ((rd4 pf4).slotπ κ v w) i = byteAt (pf4 (slotTr4 κ v w)) i`; `slotTr_getD`
- **`slot_pfAbsorb hv hn (hsh : (phasesOf seq4)[n].2 = .absorb g len) hg (hj : j < len) hb : byteAt (slotπ) (fieldOffOf seq4 g + phaseOffOf seq4 n g + j) = (F.toBytes (w (sCell (slotB0 κ v) ((1 + itOff (phIx seq4 n) + 8 + (40 + j))/16))))[…]`**
  (the generators' `piField 0 (o f)` bytes; with `slot_qelem` an aligned `piElem` is an H/arena₁ cell)

**Low level (`FRNodeRows4AskPosT`, `FRNodeRows4`, `FR.Rev4`)**: `TG`, `trailRows`, `trailMS(_eq,_T)`,
`inpTG`, `rsvTG`, `askTG`, `askRowsT`, `askPI`, `ArFit`, `slotB0`, `arRej`, `arIRows4`,
`mem_node_slot/ar/link`.

## 6. Open items

1. **The stream's last block.** For an aggregate with `k < maxK`, its last segment's last block is the
   candidate final block `finB + (k−1)`, not the main chain's. Every bridge lemma excludes it
   (`16·e + 80 ≤ segB`; `hb` excludes exactly the last item, since items are ≥ 80 bytes). The last
   item's answer and arena₁'s last 4 elements need `aggPad`'s tie between the candidate block and
   the main chain (or arena₁ reading `blkOf` for the last block). Owner: ASK-T/IMPC with B4's `aggPad`.
2. **SRA §6.2** (`felems` aux = column bytes; `bits 20` = the `idx` answer's bits) and **§6.3's
   byte-register invariant** along `execA`: not built. The positional half is here (`ctb4_cols`,
   `slot_qelemA` give a column's 16-byte words as arena₁ cells; `slot_pfAbsorb` the zero pins and the
   kind byte of absorb fields); what remains is the register provenance (which op made a register),
   a statement over the compile trail like `askRowsX`.
3. **`a2Rows4`** (structured binding) unused; see §1.2.
4. `plan4t init` +1.7 s: reuse `planData4`'s memo in `arOf` if the budget tightens.
5. CK's compile fix and R1's field-length change: no literal of mine depends on them (the fit is
   checked at process start; `arN` follows the format; the positional lemmas are generic in `seq4`).

## 7. Cells and rows E1 must fill

Per slot `σ` of every kind (absolute cells, rows of M):
- **arena₁**: cell `oneCell + σ·2^20 + arA1 + e` (`arA1 = 290,816`) = H cell `sCell (slotB0 κ σ) e` for
  `e < arN = 96,944`; rows `σ·2^20 + arR1 + e` (`arR1 = 852,992`).
- **bits**: cells `oneCell + σ·2^20 + arBt + j` (`arBt = 389,120`, `j < 8,320`) must be `0`/`1` (zeros
  until a class uses them); rows `σ·2^20 + arRb + j` (`arRb = 950,272`).
- **template rows**: rows `σ·2^20 + arR2 + k` (`arR2 = 720,896`): prototype 0 8 rows, prototype 1 6 rows
  today — IMP's `input` rows (the compiled `input` ops' digest cells = the `inC` cells, IMP-RESULT §6)
  and SRA's reserve rows (0 rows with the compile's layout). Re-dump the plan form: `protoV4`'s value
  changed.

## 8. Files

New: `FRNodeRows4AskPosT.lean`, `FRNodeRows4AskPosF.lean`, `FRNodeRows4AskPos.lean`,
`FRNodeRows4AskPosR.lean`. Edited: `FRNodeRows4.lean`, `FRNodeRows4Fit.lean`, `FRNodeRows4Plan.lean`,
`FRNodeRows4ArenaRows.lean`, `FRNodeRows4ArenaPlace.lean`, `FRNodeSound4.lean` (proof, 2 lines),
`FRNodeSound4R.lean` (proof, 2 lines). Code lines (`loc.txt`, HEAD → now): `FRNodeRows4` 156 → 186,
`FRNodeRows4Fit` 443 → 627, `FRNodeRows4Plan` 863 → 983, `ArenaRows` 233 → 234; new 83 + 87 + 199 + 185.
**`FR.lean` (orchestrator)**: `import FRNodeRows4AskPosR` (pulls `AskPos`, `AskPosF`; `AskPosT` comes with
`FRNodeRows4`). Build-tree probes (dev): `probe/ArTime.lean`, `probe/MxKat.lean` (reference gains `arV4`).
