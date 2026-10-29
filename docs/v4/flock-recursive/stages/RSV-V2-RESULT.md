# RSV-V2 RESULT: the reserve's V side as RSV2's stacked `evalM`

Track RSV-V2, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`. Started at
HEAD `213c407` (RSV-V); rebased on `7602c97` (B2″) when the orchestrator said B2″ had landed. Build
tree `logs/fr-build-RSV2` (a copy of `fr-build-RSV`, re-snapshotted on each HEAD); logs `logs/RSV2/`.
Journal: `stages/RSV-V2-JOURNAL.md`. Spec: main's `design/RSV2.md` §4, with `reviews/RSV2-review.md`
as the orchestrator applied it. No sub-agents and nothing committed. No `FRSoundness4*` module was
edited; the build tree carries RSV-V's sorried copies of the 7, which are in
`logs/RSV2/sorried-copies/`.

## 0. Summary

- **Done.**
  - The format: `Seq.lrEnd` is 1,008 bytes, `|π|` is 876,304 and the stream is `64 · 24,236`.
  - The V programs: one stacked `evalM` per node, the 60-value B′ and finPf, and `evalMX4` with
    `evalMX4_eq`.
  - Dumps, the plan-form KAT, the hint, `rsvRel`, `cellfit` and `arenafit`, all on B2″'s layout.
  - The reserve KAT, every transition in both directions.
  - V(N4) measured against `213c407`'s binary and B2″'s, in alternating runs.
  - **Red set: exactly the same 7 declarations as RSV-V** (§4).
- **Review finding 1 applied.** 11 of the 60 values are copied into one cell each (`× one`). The 9
  coefficients `s^P` end in an `addF`, and the mixed-point entries 22 and 24 are `muxEl` sums.
  `rsvcells.py` checks on the dump that every one of the 60 registers is exactly one cell with
  coefficient 1: PASS.
- **The KAT found a bug in my first `rsvEOps`.** (ii″) added the parent's own `X^P` instead of the
  claim's `X`. With `s = 0` the two are equal, so only the full-support cases could show it. The bug
  is fixed, and every case now passes (§5).
- **Major finding (§7): δ is not 0–11 ms.**
  - Each extra kind in the support costs **+21 … +24 ms** of V(N4) (VM, best). Full support costs
    **+51 ms**: V(N4) is 324 ms, against 272–274 ms for one kind.
  - A kind's slot sums are ≈ 30 ms whatever its slot count. Of that, `linkV4` takes ≈ 29 ms, and
    rebuilding its rows at each call accounts for ≈ 9 ms.
  - On the score, full support gives `V̄_i` = 1.40 s, against 0.94 s for B2″ with a same-kind child.
    That is **+0.46 s per step**, and from step 3 on most steps have full support.
  - RSV2 is still below RSV-V as built (1.45 s on average, with the chain open). The levers are in
    `FRNodeRows4Plan` (L-circ's module; §7).

## 1. What was built (code lines, the core's `loc.py`, HEAD `7602c97` → now; `logs/RSV2/loc.txt`)

| Module | Change | code |
|---|---|---|
| `FRShape4` | `seq4.lrEnd` 1,008; `seq4_eq`, `fieldSizesOf_seq4`, `piSizeOf_seq4 876304`, `streamBytesOf_seq4 1551104`, `chainLenOf_seq4 24236`; `NodeKind.ix` (0/1/2), `NodeKind.all`, `all_ix` | 241 → 244 |
| `FRVIRFinals4` | `FinP.kix`; `rsvRx/Ry/S/X` 48/416/816/960, `rsvN = 60`; **`rsvSOps`** (the nine `s^P`); **`rsvEOps`** (RSV2 §2.2, the register map in §2); `gFinE0 … own` (with `own = false`, the own `evalM` becomes three `const 0`); `gFinE` (own asserts off under `rsvOps`, 60 exports); `rsvBOps` over `rsvN`; `noAsk_rsvEOps` re-proved | 581 → 607 |
| `FRVIR4At` | `map_at_gFinE`, `finOps4_counts`: `rsvSOps` in the simp sets | 331 |
| `FRVerifierC4` | **`rsvRel`**: 60 cells read off the dump; `nodeFinP … rsvN κ.ix` | 106 → 107 |
| `FRVerifierImplNode4F` | removed: `kindElemN`, `kindOfElem`, `sub3`, `evalMPair`, `evalMD4`/`evalMDS4`, `evalMD4_ctl`. Added: `sOf`, `dot3`, **`evalMX4`**/**`evalMXS4`**/**`evalMX4_eq`**, `evalMN4` at size 32, `evalMS4_src`, **`implN4F_hMX`**, **`evalMX4_ctl`**. Changed: `implN4F_hM` (32 in place of 24), `implN4F_ctl` | 307 → 330 |
| `FRNodeCircuit4` | `PubCellsR4` doc; `rsvCells_ctl` (60 cells) | 307 |
| `FRNodeKinds4` | `segB 1551104`, `cLen 24236`, `hEnd_eq` 74,015 / 122,495 / 195,216 | 393 |
| `FRNodeLayout4` | `aggChainLen_eq` (48,472 / 96,944), `_k3` (72,708), `hUsed_eq` (74,013 / 122,491 / 195,208), `regions_need_levers` (1,557,056) | 59 |
| `FRX4Prog`, `FRX4Ext` | `876176` → `876304` | 169, 543 |
| `FRVIRTpl4Bridge` | `protoR_ctl` `(24236, 96944)`, `(24236, 48472)`, `(96944, 96944)` | 65 |
| `FRVerifierImplNode4T` | doc: `aggB 1 = 0x17AB00` (bits 13 and 12 still 1 and 0) | 404 |
| `FRNodeRows4ArenaPlace` (B2″'s) | `arN_eq` 96,944 | 66 |
| `FRNodeRows4Model` (B2″'s) | `packMapN` 212,640; `regions_sum`, `mRowModel4_eq` (3,527,544 / 5,488,520 / 7,843,904; `N8` still 1.0185× under `N_M / 1.05`), docs | 34 |
| `FRNodeRows4Hint` | regenerated last (`laydump4` + `mkhint.py`): only the `maskN` literal moves | 37 |

15 modules touched, +53 code lines. Dev-only probes, in the build tree and copied to
`logs/RSV2/probes/`:
- `RsvKat2` (the KAT);
- `VTime4` (`s2`/`s4`/`s8` keep those kinds' coefficient blocks, and `evalMX4` is timed by support);
- `XBrk` (the breakdown of `evalMX4`).

`logs/RSV2/rsvcells.py` reads `rsvRel` off the dump and checks it.

## 2. The construction as built (`rsvEOps`, registers from `c = b + 38`)

| Registers | Contents |
|---|---|
| `c … c+22`, `c+23 … c+47`, `c+48 … c+56`, `c+57 … c+59` | imports `p_x`, `p_y`, `s`, `X₃` (`fLrEnd` 48 / 416 / 816 / 960) |
| `c+60` | `m̂*` (`fEEnd` 48) |
| `c+61 … c+63` | zero fields: `fEEnd[64,112)` (all kinds); `fLrEnd[48,1008)`, `fEEnd[48,64)` (where `¬rsv`). Then `assertZero X₃[1]`, `X₃[2]` (all kinds) |
| `c+64`/`c+65`, `c+66`/`c+67` | `p_x[<e2R]`, `eq(p_x, r_E2)`; `p_y[<e4R]`, `eq(p_y, r′)` |
| `c+68`, `c+69`, `c+70`, `c+71` | `κ_E⁴`, `w = κ_E⁴·eq(p_y, r′)`, `f̂κ_E`, `f̂κ_E²` |
| `c+72 … c+74`, `c+75` | kind indicators `[kix = 0/1/2]` (kind-table `const`s), `one` |
| `d = c+76`: `d … d+35` | `rsvSOps`: `own_i = ind_{i/3}·t_{i%3}`, `ch_i = w·s_i`, sums, **`s^P_i = one·(own_i + ch_i)`** (`d+27 … d+35`, single cells) |
| `d+36 … d+38`, `d+39 … d+41` | entry 22 of `x̂`: muxed `packFK`, `getF`, `× one`; entry 24 of `ŷ` likewise |
| `d+42`, `d+43` | the row point `chals E2 [0,22) ‖ x̂₂₂ ‖ s^P` (32 entries) and the column point `chals E4 [0,24) ‖ ŷ₂₄` (25). Both lists are the same for every kind: no mux |
| `d+44 … d+46` | **the one `evalM`**; `X^P = d+44` |
| (ii″) `d+50` | `b+8 + η·eq(p_x, r_E2)·(m̂* + X)` (`X = c+57`; characteristic 2) `= claimN(E2)`, gate `node` |
| (iii″) `d+52` | `b+16 + κ_E⁴m̂* = claim0(E4)`, gate `node` |
| (iv″) `d+53` | `X^P + b+35 = claimN(E4)`, gate `node` (`b+35 = κ_E³·L̃·f̂`: the own `evalM` is zero) |

- `gFinE` exports `b+17 :: [c, c+60)`.
- `rsvBOps` is Horner over the 60 values; its registers run `d … d+117` and `e = d + 118 … e+7`.
- `gFinPf` takes `nrcell = 60` from `nodeFinP`.
- Program sizes (`logs/RSV2/dump/fsummary.txt`): node programs have 154,920 ops (RSV-V 154,433, +487;
  the review estimated +480) and 147,077 registers. Segment programs are unchanged at 151,226.
- The kind constants are `const`s on `FinP.kix`, a new per-kind field. The node kind's identity was not
  in `FinP`, and `Q κ` now carries it. `fixKV` leaves it alone, so `map_at_*` still close by `rfl`.

## 3. Deviations from RSV2 §4, with reasons

1. **The 11 single cells** (review finding 1; RSV2 §2.2 and §4.3 as written cannot be bound).
   - The nine `s^P` and the entries 22 and 24 are each `mulF one ·`: 11 product rows.
   - The 32- and 25-entry points then carry no mux (`rsvcells.py` asserts that both `packFK` lists are
     the same for every kind).
   - Why the check is in Python: `rsvCells_ctl` cannot read the dump, and a Lean check would need the
     prototype's compile, which takes more than 25 minutes (RSV-V's `RsvCells`).
2. **`hEnd`** is 74,015 / 122,495 / 195,216: the review's figures. `decide` refused the memo's.
3. **`gFinE0` gains a parameter `own`** (default `true`), rather than `rsvOps` being read inside it. The
   numbering `b+18 … b+37` is kept, as RSV2 recommends.
4. **`ltbOf` is shared** between `N4` and `N8` inside `evalMX4` (the same `logM`; ≈ −4 ms).
5. `regions_need_levers`' negative literal 1,556,928 → 1,557,056 (review nit).
6. **B2″'s `FRNodeRows4ArenaPlace`/`FRNodeRows4Model`**: only the literals that follow the stream.
   - `arN_eq`; `packMapN` (+8); the model's sums.
   - B2″'s `arN` is `4·chainLenOf seq4`, as the orchestrator said.
   - These edits were needed for the build after B2″ landed.

## 4. Build, red set, axioms, source rule, CPU-s

- **Build.** At `7602c97` with this track, `lake build FR Solution FRSoundness4TailShift
  FRSoundness4XCtrl FRNodeSound4Ctrl` (plus the probes) is green at 4,950 jobs
  (`logs/RSV2/build-final.log`). It uses the 7 sorried copies. All of this track's modules build
  without `sorry`.
- **The red set is exact.** I ran `logs/RSV2/scan/` from HEAD's unsorried `FRSoundness4*`, build tree
  only: 4 rounds, ending green at 2,592 jobs (`scan/build-4.log`, `scan/sorried.txt`). `scan/run1/`
  holds the earlier run, before the (ii″) fix and B2″, which gave the same set. The 7 declarations:
  - `FRSoundness4R4Fin.flag_gFinE`, `flag_gFinB'`
  - `FRSoundness4Qry.noAsk_gFinE`, `noAsk_gFinB'`, `noAsk_gFinPf`
  - `FRSoundness4R4FrE.fsMsgs4_ends`
  - `FRSoundness4R4PfFlag.gFinPf_reloc`

  The only `sorry` in the worktree is in a comment in `Solution.lean`.
- **Axioms** (`logs/RSV2/axioms.log`, `ax/AxRSV2.lean`): 47 theorems, each with `propext`,
  `Classical.choice`, `Quot.sound` or fewer; no `sorryAx`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 378
  files, 0 findings (`logs/RSV2/source-rule.log`).
- **CPU-s** (sequential, `lean -DElab.async=false --profile`, one core; user + system, including ≈ 3.5 s
  of import; `logs/RSV2/profile-*.log`, `cpu.txt`):

  | Module | CPU-s | type checking | RSV-V |
  |---|---|---|---|
  | `FRShape4` | 17.1 | 7.42 s | 17.2 |
  | `FRVIRFinals4` | 24.5 | 1.73 s | 27.0 |
  | `FRVIR4At` | 11.7 | 0.66 s | 12.7 |
  | `FRVIR4Uni` | 9.6 | 0.13 s | 9.3 |
  | `FRVerifierC4` | 7.1 | 0.03 s | 6.5 |
  | `FRVerifierImplNode4F` | 11.7 | 0.98 s | 11.4 |
  | `FRX4Prog` | 10.3 | 0.46 s | 10.1 |
  | `FRX4Ext` | 13.0 | 1.40 s | 12.4 |
  | `FRNodeLayout4` | 16.6 | 9.84 s | 16.4 |
  | `FRNodeKinds4` | 18.5 | 2.33 s | 18.4 |
  | `FRNodeCircuit4` | 12.2 | 1.31 s | 11.3 |
  | `FRVIRTpl4Bridge` | 6.9 | 0.08 s | 6.6 |
  | `FRVerifierImplNode4T` | 12.0 | 1.50 s | 12.1 |
  | `FRNodeRows4ArenaPlace` | 9.0 | 0.02 s | — |
  | `FRNodeRows4Model` | 6.6 | 0.02 s | — |
  | `FRNodeRows4Hint` | 6.1 | 0.00 s | 6.6 |
  | **total** | **192.9** | | |

  The first `FRVIRFinals4` was 53.7 CPU-s. Two things caused it:
  - `gFinE0`'s `cond own … ++ […]` without type ascriptions: 14.4 s of elaboration;
  - a broad `simp` in `noAsk_rsvEOps`: 12.4 s.

  The ascriptions and `simp only [rsvEOps, rsvSOps, List.filterMap_append, List.filterMap_map]; rfl`
  bring it to 24.5 CPU-s.

## 5. KATs, dumps, cells

**The reserve KAT** (`probe/RsvKat2.lean`, `logs/RSV2/rsvkat2-2.log`, re-run identical on the final
code as `rsvkat2-3.log`; 60 s, 2.5 GB).

How it runs:
- Full V runs of `progNode κ`, op by op, under a consistent random oracle.
- A toy `evalM`: 48 random sparse entries per kind, dispatched as `NI4F.evalMN4` (size 32 → `Σ_κ ⟨s_κ, M̃_κ⟩`).
- A zero witness (`f̂ = 0`), with honest E2/E4 rounds for the child terms. The prover's summands
  carry a per-entry `lim`, so a kind's coordinates above the parent's are fixed and the ones it lacks
  are constant.
- **Chains**: each parent's child claim is the previous run's stacked call read off its registers
  (32 + 25 inputs, 3 outputs), as the circuit binds it.
- Every run also checks the `s^P` wiring against `[κ = κ_P]·f̂·κ_E^m + κ_E⁴·eq·s`.

| Case | (ii″, iii″, iv″) failing | zero asserts failing | E-phase rounds failing |
|---|---|---|---|
| chain `N8* → N4 → N2 → N2 → N4 → N4` (`N8*`: random π, so `f̂ ≠ 0`; its real `N8`-only claim feeds the chain) | none at every parent | none | 0 |
| chain `N8* → N2 → N4 → N2` | none at every parent | none | 0 |
| chain `c0` (random point, full support, honest `X`) `→ N4 → N2 → N2 → N4 → N4` | none at every parent | none | 0 |
| chain `c0 → N2 → N4` | none | none | 0 |
| (−) `N4` and `N2` parents: `X + 1` | (ii″) | none | 0 |
| (−) `s_7 + 1` (an `N8` coefficient), prover honest at the stated `s` | (ii″) | none | 0 |
| (−) `p_x[0] + 1`, prover honest at it | (ii″) | none | 0 |
| (−) `X₃[1] ≠ 0` | none | `X₃[1]` | 0 |
| (+) `N8`, zero block | none | none | 0 |
| (−) `N8`, junk in `fLrEnd[48]` | none | `fLrEnd` | 0 |
| (−) `N8`, junk in `X₃[1]` | none | `fLrEnd`, `X₃[1]` | 0 |
| wiring, `f̂ ≠ 0` (`N4`, `N2`) | not consulted (the toy has no own R1CS) | — | — |

- Transitions covered:
  - the real `N8` claim into both `N4` and `N2`;
  - `N4 → N2`, `N2 → N2`, `N2 → N4` and `N4 → N4`, each with an `N8`-only claim and with a
    full-support claim.
- The `s^P` wiring is correct in every run; with `f̂ ≠ 0` the own block sits at the own kind's index
  only.
- `X₃ = (X, 0, 0)` for every honest call.
- The other ≈ 874 failing ops are the zero proof's PIOP checks, the same in every case.
- Limit: with a zero witness, `f̂ = 0`, so an honest chain's support does not grow. Full support was
  injected (`c0`) instead.

**Dumps.**
- IR dumps are in `logs/RSV2/dump/` (`SHA256SUMS`). `items.json` has `Lrend` `len` 1008, and
  `summary.txt` lists the field offsets (§9). A2″'s cap-check KAT passes (`capkat.txt`).
- Node dumps are in `logs/RSV2/nodedump/`, at `7602c97` with this track and the regenerated hint.
  `plan4t init` gives `inR true` (`plan4t-init.log`).
- **Plan-form KAT PASS** (`planform-kat.log`): 649,761 and 641,656 rows rebuilt, 0 differ (B2″ at RSV-V's
  program had 649,915 and 641,628).

**Cells.**
- `rsvRel` (`rsvcells.log`, PASS) is unchanged from the preview on HEAD's layout:
  - E2 challenges 1,318 … 1,549;
  - mixed entry 22 at 116,596;
  - E4 challenges 1,579 … 1,809;
  - mixed entry 24 at 116,600;
  - `s^P` at 116,584 … 116,592;
  - `X₃` at 116,601 … 116,603.
- Every cell is in the skeleton, which ends at 276,634.
- `cellfit.log`: 0 overlaps. The lowest instance is above 137,382 free cells (p0).
- `arenafit.log`: the skeleton ends at 276,634, below arena₁ at 290,816, and the lowest instance is at
  414,016, above the bits' end at 397,440. **The 60 cells clear the arenas and the templates.**

## 6. (Unchanged from RSV2) `εR`

No phase index and no item moves. B′'s row is `70/2^128`, below `2^-120.36`. Nothing here touches `εR`.

## 7. V(N4) and δ (finding for the orchestrator)

The runs alternate on core 29 over 4 rounds, with VM ms best of 21 runs, from `logs/RSV2/abv.sh` and
`vtime-ab.log`/`vtime-ab.summary`. Rounds 3–4 had load up to 13; the best values stand.

| Binary | V(N4) best | `V̄_i` (S-I basis) |
|---|---|---|
| `213c407` (RSV-V), same-kind child | 266.6 | 0.904 s |
| `213c407`, `N2` child (second `protoV4`) | 454.5 | 3.105 s |
| B2″ (`7602c97` at RSV-V's program), same-kind | 271.5 | 0.941 s |
| **RSV2, support {N4}** (own kind only) | **273.6** | 0.957 s |
| **RSV2, {N4, N2}** | **294.6** | 1.126 s |
| **RSV2, {N4, N8}** | **297.4** | 1.150 s |
| **RSV2, all three** | **324.2** | **1.397 s** |

`evalMX4` alone, in the same runs, by support (best): {N4} 154.7–159.1, +N2 183.9–193.8, +N8
184.8–202.9, all 213.7–233.5 ms.

**Where the time goes** (`XBrk`, `xbrk-2.log`):
- `protoV4` is shared.
- Each kind's slot sums take **≈ 29–32 ms whatever its slot count** (3, 5 or 8). Nearly all of it is
  `linkV4`.
  - ≈ 9–10 ms of that rebuilds the link rows at every call: `linkHead4`, `extRowsC`, `grows` over
    ≈ 8.8k pinned elements and ≈ 8k extension rows per kind.
  - The rest is `wfSum` and `growsVal3` arithmetic over ≈ 17.5k entries.
- `ltbOf` takes 2.6–3.9 ms per `logM`.
- RSV2 assumed ≈ 0–1.5 ms per slot (from B2′'s per-kind figures). The cost is per kind, not per slot,
  and the support holds all three kinds from step 3 on for most steps.

**Score.**
- Full support: 324 ms, `V̄_i = 1.40 s`. That is **+0.46 s per step** over B2″'s same-kind 0.94 s,
  against the review's ceiling of ≤ 0.13 s.
- Still below RSV-V as built: 0.75·0.904 + 0.25·3.105 = 1.45 s, and that chain is open.

**Levers.** All are in `FRNodeRows4Plan`, which is L-circ's module and not mine.
- (a) **Build each kind's link rows once** at plan init, as `grows` lists in `Plan4`, and evaluate
  them per call: ≈ −9.5 ms per kind, ≈ −28 ms at full support (`V̄_i` ≈ 1.14 s).
- (b) **Share the kind-independent parts of `wfSum`.** Slot `σ`'s pinned elements have the same rows
  and coefficients for every kind (`linkBase σ`, `wfSeg`). Only `gs(sCell b0 ·)` reads the kind's
  stream block. The `gt·e1` and `gt·p.2` sums are therefore per slot, not per kind.
- (c) A kind whose `s_κ = 0` is already skipped.

## 8. For RSV-S

**The red set** (exact; §4) is the 7 above. With RSV2's content:
- `flag_gFinE`: finE is now `gFinE0 … (fun _ => false) false` followed by `rsvEOps`. The own asserts
  are off, the own `evalM` is three `const 0`, and the three claims are asserted by `rsvEOps`, gated
  `node`.
- `flag_gFinB'`: `rsvBOps` over 60 values (`κ′^{11 … 70}`).
- `noAsk_gFinE`, `noAsk_gFinB'`, `noAsk_gFinPf` follow from `noAsk_rsvEOps`, `noAsk_rsvBOps` and
  `noAsk_gCellsOpsK`.
- `fsMsgs4_ends` uses the lengths 1,008 and 112.
- `gFinPf_reloc` needs the 60-cell second chain and `keep rsv`.

**The statements that change**, following RSV2 §5 with the review's corrections:
1. **`FRSoundness4R4Fin`**: `relE4` for node kinds becomes (ii″) ∧ (iii″) ∧ (iv″) ∧ the zero
   conjuncts, with the values below. `vStar4` gains `κ′^{11}·Σ_{i<60} κ′^i v_i` where `rsv`.
   `flag_gFinE` and `flag_gFinB'` are re-proved against §2's op lists.
   - `p`, `s`, `X₃` come from `fLrEnd` at 48/416/816/960, and `m̂*` from `fEEnd 48`.
   - (ii″) uses the **claim's** `X` (`c+57`).
   - (iv″) is `impl.evalM (x̂ ++ s^P) ŷ`, with `x̂` 23 and `s^P` 9 entries (32), and `ŷ` 25.
   - The zero conjuncts are `X₃[1] = X₃[2] = 0`, `fEEnd[64,112) = 0`, and, where `¬rsv`,
     `fLrEnd[48,1008) = 0` and `fEEnd[48,64) = 0`.
2. **`FRSoundness4Qry`**: the three `noAsk`s (proof only).
3. **`FRSoundness4R4FrE`** and **`FRSoundness4R4FrRS`**, **`FRSoundness4R4Start`**:
   - `fsMsgs4_ends` (1,008 / 112);
   - `relE4_of_accept`, `e_end4`, `not_rejEndE4_node`, `e_in4`, `not_rejInE4_node`, `e_fin4`,
     `not_rejFinE4_node`, with `e_fin4`'s `hM` in **`NI4F.implN4F_hMX`**'s form: at a 32-entry row
     point, `evalM = (Σ_κ dot3 (sOf τ κ.ix) (matMLE (srcE4 κ).e{a,b,c} (ptA (e2R κ) τ) (ptA (ncR κ) σ)), 0, 0)`.
     `implN4F_hM` still covers points of size `e2R`.
   - `vEnd_lr4`, `lr_end4`;
   - `relE4_of_fields` (`FRSoundness4R4FrRS`); `start4_of_fields`, `start4_node`
     (`FRSoundness4R4Start`).
4. **`FRSoundness4R4PfFlag`/`PfFin`**: `gFinPfR` with the 60-cell chain and `keep rsv`; `relPf4`,
   `relPf4_of_fields`, `fin4_of_fields`, `hz_of_fields`. The weight gains
   `Σ_{i<60} κ′^{11+i}·eq(c_i, ρ)`.
5. **`FRSoundness4P4bNames`** (positions unchanged):
   - **E2 and `ChildBad4`.** The summed table is
     `eq(τ,x)R(x) + η·eq(p_x[<e2R], x)·(Σ_i s_i·M̃_i(x ‖ p_x[e2R,23), p_y) − X)`. Then
     `truthChild4 := X = Σ_i s_i·M̃_i(p)` and `ChildBad4 := ¬truthChild4`.
   - **E1's escape (review finding 5).** `η` is coordinate 23 for every kind.
     - For `N4`/`N8`, `n = e2R + 1 = 24`.
     - For `N2`, `n = 24` with the table constant in coordinate 22 (the review's form: the
       polynomial lives on coordinates 0–21 and 23 and is duplicated along 22). The bound stays
       `24/2^128`.
     - New lemmas: a variant of `zcG_count`/`ZCwG` with the `η·D` half, and a **constant-extension
       lemma** (the MLE of a table constant in a variable). Neither exists yet; `FRMLE`'s
       `mle_fixLow`/`mle_fix0` help.
   - **E3/E4.** `c4E4` gains `κ_E⁴·m̂*`. `wEb4` gains `κ_E⁴·eq(p_y[<e4R], y)·Σ_i s_i·M̃_i(x̂, y ‖ p_y[e4R,25))`.
     `BatBadE4` stays at ≤ `8/2^128`. `RejFinE4` goes through the stacked spec (`evalMXS4`).
   - **B′ (review).** `PubOK4`/`single_B4`, `bTerms4` and `hcells` go from 9 to **69** cells
     (`Fin 11` → `Fin 71`), with the row at `70/2^128`. `StmtN4` gains `PubCellsR4 κ w (childVals π)`.
6. **The chain** (`gap4Imp_of_rsv`): `SlotImp`'s `evalM` fact at slot 0. It follows from these:
   - `PubCellsR4`: 60 cells, each **one** cell (`rsvcells.py`).
   - **The 11 product rows `cell = one · form`.** These are the one step beyond RSV2 §2.4. Each row's
     `Holds`, with `w one = 1`, says the cell is the linear form that `evalM` consumed: the
     `addF` sum for `s^P`, and the `muxEl` sum for entries 22 and 24.
   - `truthChild4` and the two zero asserts.
   - `evalMN4_eq` at size 32 (`evalMNS4 = (evalMXS4, 0, 0)`).

   The `N8` parent has nothing to discharge.
7. Controls as in RSV2 §5 item 8. `NI4F.evalMX4_ctl` gives the V-side (+)/(−):
   - (+) one kind's coefficients give that kind's combination;
   - (+) zero coefficients give 0;
   - (−) a change `e` on kind `κ` changes `X` by `⟨e, M̃_κ⟩`.

## 9. For P2 (`prover/`)

- **The format.** `|π|` is 876,304. The field offsets are in `logs/RSV2/dump/summary.txt`: `fLrEnd` at
  6,464 (1,008 B), `fEEnd` at 9,808 (112 B), and every field after 8 moves by +128 against RSV-V.
  - `fLrEnd = â_L ‖ b̂_L ‖ ĉ_L ‖ p_x (23) ‖ p_y (25) ‖ s (9) ‖ X₃ (3)`.
  - `fEEnd = â_M ‖ b̂_M ‖ ĉ_M ‖ m̂* ‖ 0^48`.
  - `N8` writes zeros in `fLrEnd[48,1008)` and `fEEnd[48,64)`.
- **The child claim is copied from the child's own V values.**
  - `p_x = r_E2^C[<e2R_C] ‖ p^G_x[e2R_C, 23)` and `p_y = r′^C[<e4R_C] ‖ p^G_y[e4R_C, 25)`.
  - `s_{κ,m} = [κ = κ_C]·f̂_C·κ_{E,C}^m + κ_{E,C}⁴·eq(p^G_y[<e4R_C], r′^C)·s^G_{κ,m}`, with
    `κ.ix` = `N2` 0, `N4` 1, `N8` 2.
  - `X = Σ_i s_i·M̃_i(p)`, and `X₃ = (X, 0, 0)`.
  - The support grows to every kind seen below.
- **E2**: the summand is `eq(τ,x)(Az·Bz − Cz)(x) + η·eq(p_x[<n], x)·(Σ_i s_i·M̃_i(x ‖ p_x[n,23), p_y) − X)`,
  claim `0`, with `n` the node's own E2 rounds. A kind with fewer row coordinates than `n` is
  constant in the extra ones.
- **`m̂* = Σ_i s_i·M̃_i(r_E2 ‖ p_x[n,23), p_y)`.**
- **E4**: claim `+ κ_E⁴ m̂*`; summand `+ κ_E⁴·eq(p_y[<n′], y)·Σ_i s_i·M̃_i(x̂, y ‖ p_y[n′,25))`.
- `RsvKat2.runNode` is a reference for both: entries carry a per-entry `lim`.
- **The stream** is `64 · 24,236`, `aggB k = 1 + k · 1,551,103`, and `hUsed` is 74,013 / 122,491 /
  195,208. Arena₁ has 96,944 elements.

## 10. Open questions for the orchestrator

1. **δ (§7)**: +0.46 s of `V̄` per step at full support. Should L-circ's levers (a)/(b) in
   `FRNodeRows4Plan` be scheduled before P2 measures the node? The memo's §3.2 figures (0–11 ms,
   ≤ +0.13 s) do not hold.
2. In the KAT the support does not grow along a chain, because `f̂ = 0` under a zero witness. A
   full-witness KAT is P2's.
3. RSV2 §6 (no uniform node shape) still stands: δ is per kind present in the support, and a uniform
   shape would not remove `N8`'s slot sums.
