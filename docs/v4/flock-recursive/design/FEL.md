# FEL: the `felems` residual — design memo

Worktree `recursion.fast-submissions-rev44`, HEAD `9db5ee0` (2026-10-30). No Lean edited, nothing built,
nothing committed. Every fact below is a file line of `submissions/flock-recursive/lean/` or a line of an
existing log; the counts come from `logs/IMPC/impcstat-ck.log` and `logs/SIB/sibstat-final.log`.

## 0. Verdict

**Route 1, compile aliasing**: the `dotKF` template's column cells become arena₁'s cells of the column's
16-byte windows, decided inside the compiler extension (`TCtx` gains one field; `Xof π` carries the
prototype's alias map). **0 rows, 0 new cells, no V change per check, no new op or import** (R1's
constraint is met: nothing is recomputed, the cells already exist). The aux conjunct of `SlotRunC`
is then a theorem from `PfCells` alone — for **every** compile, not only the honest one — because a
`dotKF` whose column cannot be aliased gets **no** aux entry: the extension refuses it, the op becomes an
import, and SIB's closure already emits the failing row there (`impRows`, `FRNodeRows4AskC.lean:179`).
Route 2 does not fit either prototype's row budget and costs V and init; route 3 is false (§4).

## 1. What the `felems` are

- **Producer.** Only `dotKF w col` (`xof_felems`, `FRNodeRows4AskIR.lean:246`; `tplExt_felems` :226,
  `tplExtKM_felems` :233, `extGetK_aux` :240). The arm is `FRVIRTplExt.lean:219–226`: with `w`'s slot
  `.ak n`, it allocates `cells := cell (cb + 2n + b)`, `b < n`, in the instance's window after the `2n`
  locals (`hintLay0/1`: windows `2^8` for `dotKF 64`, `2^6` for `dotKF 16`, `FRNodeRows4Hint.lean:31–32,
  50–51`), passes `lw ++ cells` as the instance's inputs, and records `aux := [(cells, col, .felems n)]`.
  `CS.add` stamps the register count: `(cells, col, .felems n, cs.slots.size)` (`FRVIRCompile.lean:202`).
- **Program.** `posOps` (`FRVIR.lean:827–833`): `.piField fCols (co + p·colBytes i) (colBytes i)`,
  `.askCol i (b+1)`, `.dotKF w (b+1)` — the column register is the `piField`'s. Per prototype 290
  `felems 64` + 581 `felems 16` = 871 entries, 27,856 cells (PACK §1.3 l.140).
- **Value each cell must hold** (`AuxK.val`, `FRVIRTplCore.lean:348–350`): cell `b` = `(felems bytes)[b]`,
  the `F` element of bytes `[16b, 16b+16)` of the register, `0` past the end.
- **Where the kernel needs them.** `SlotRunC` (`FRNodeRun4CB.lean:223–227`), conjunct (a):
  `∀ a ∈ (protoCS π).aux, isBitsA a = false → a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)`.
  That hypothesis feeds `compileX_sound` through `tplExt_ok`'s `dotKF` case, which uses it as `hc` and
  nothing else about the cells (`FRVIRTplExt.lean:435–445`: `inpIs_of (by rw [List.map_append, hxl, hc])`).
- **Whole set.** `impcstat-ck.log:9,16`: `aux 2498: felems bound 871, bits 1627, other []` per prototype —
  the non-`bits` aux cells are exactly the 871 `felems`; all 871 satisfy `colOk` (`AskIR:288`: `provOf`
  succeeds, `col <` the count, `winsOk`). `sibstat-final.log:4,8`: residual `aux felems 871` each.
- **Why they are unbound today.** The cells occur only as multiplicands of the instance's `mulsG`
  products (`tplDotKF`, `FRVIRTplLag.lean:468–474`); no row pins them. `colTG` (`AskI:229–239`, one copy
  row `1·(cell − A₁(e)) = 0` per cell, `a1Row` :101) was never folded: V ≈ +75 ms per node and the rows no
  longer fit (IMPC-RESULT §3 l.144–148; IMPC2 §0 l.46–49).

## 2. The arena fact that replaces the rows

`PfCells w π inp := ∀ o e, winE o = some e → w (π·slotM4 + arA1 + e) = F.ofBytes (bytesAt inp.π o 16)`
(`FRNodeRows4AskIS.lean:186–187`) holds at every active slot from the statement's rows alone
(`pfCells_of_rows` :195–201, via `a1_slot`/`win_slot`). `winE` (`AskI:88–97`) accepts a 16-byte window
that is one element of one item, aligned, outside the last block; `winsOk f o len` (`AskI:161–163`)
checks it for every window of a `piField`. `aux_col` (`AskIR:183–221`) already proves the aux fact from
`PfCells` + the copy rows; **the alias removes the copy rows from that proof and changes nothing else.**
Arena₁ is an M region of the slot (`π·2^20 + arA1 + e`, `e < arN`), so the aliased rows stay inside the
slot and keep the copy evaluation (`pieceInB`/`linInB_spec`, `FRNodeRows4Plan.lean:80–100`; PACK §1.2's
"no V saved" caveat is about H cells, not arena₁).

## 3. Route 1 in detail

### 3.1 Definitions (new or changed)

| where | what |
|---|---|
| `FRVIRTplCore.TCtx` (:333–335) | new field `col : Option (ℕ → ℕ → Option (List Lin)) := none`. `none`: 3.x behaviour (fresh cells). `some f`: `f col n = some l` aliases, `= none` **refuses** (the arm returns `none`, so the op is an import). |
| `FRVIRTplExt.tplExt`, `dotKF` arm (:219–226) | `match cs.slot w with \| some (.ak n, lw) => match tc.col with \| none => (today) \| some f => match (if col < cs.slots.size then f col n else none) with \| some cells => some { tplOut … (lw ++ cells) [.k] with aux := [(cells, col, .felems n)] } \| none => none`. `imp`/`foreign`/`slots`/`tin` shape unchanged. |
| `TLay.ctx` (`FRVIRTplExt.lean:149`) | `{ tpl := tplOf, cb := L.cb }` (anonymous constructors must spell the third field: the 12 control contexts at `FRVIRTplSet.lean:637–700`, the walks' `⟨tlook M, L.cb⟩` at `FRVIRTplBuild.lean:102`, `FRInitFuse.lean:21–107`, `FRNodeRows4RepFD.lean:30–43`, `FRNodeRows4RepCFP.lean:342–353`, `FRNodeRows4AskPosT.lean:68` become `{ L.ctx with tpl := tlook M }`; their `hc` stay `rfl`-shaped). |
| new leaf module `FRNodeRows4Win.lean` | `winE` and what it needs, cut from `AskI:41–163` (`itOffA`, `itemsA`, `phasesA`, `phIxA`, `PSeg`, `pSegs`, `phItem`, `pfLoc`, `winE`, `provL`/`provAcc`/`provLT`/`provOf`, `winsOk`); imports `FRNodeKinds4` only (`seq4`, `segB`, `absOff`, `piSizeOf` are below `FRNodeRows4Defs`; `AskI`'s closure does not contain `Defs` and vice versa — checked by an import walk). `AskI` imports it; `AskIS`'s proofs are untouched. Fallback if the cut is tangled: `Defs` imports `AskI` (no cycle; it serialises `Rep*`/`Plan` behind `AskPosT`'s closure — a build-order cost, not a soundness one). |
| `FRNodeRows4Defs` (before `Xof`, :140) | `pvP π := provLT 0 (protoProg π).ops` (moved from `AskIR:297`); `colCell π f o len b := if b < len/16 then (match winE (absOff f o + 16b) with \| some e => Lin.cell (π·slotM4 + arA1 + e) \| none => []) else []`; `colA π col n := match provOf (pvP π) col with \| some (f,o,len) => if winsOk f o len then some ((List.range n).map (colCell π f o len)) else none \| none => none`; `protoCtx π := { (protoLay π).ctx with col := some (colA π) }`; `XofC π : TCtx → Ext := fun tc => tplExt4 (protoF π) (protoR π) { tc with col := some (colA π) }`; **`Xof π := XofC π (protoLay π).ctx`** (defeq `tplExt4 … (protoCtx π)`). Keep the cell expression syntactically `π * slotM4 + arA1 + e` as in `PfCells`. |
| `FRNodeRows4.protoCS` (:69–70) | `compileX (Xof π) (protoP π) (baseR π) (protoProg π).ops` (so `protoCS_X`, `FRNodeRows4Rep.lean:455`, stays `rfl`); `XofT π := Xof π`; `askTG`'s `Xa` (:235) and `XofA π` (`AskBS:155`) become `tplExt4 … { protoCtx π with tpl := fun _ => ⟨[], []⟩ }` — **they must carry `col`**, or `xofA_isNone` (`CB:313`) and the closure's `impRows` would disagree with the compile. |
| walk call sites | `tplExt4 (protoF π) (protoR π)` → `XofC π` at `FRNodeRows4Plan.lean:57–58, 69, 71, 619, 639, 642, 659`, `RepFD:51, 64`, `RepCFW:152`, `RepCFP:362` (and the dev probes). `planData4_rows` (:64–73) unfolds `protoCS` to `compileX (XofC π (protoLay π).ctx)` instead of `compileTF4`. |

`colA` is total on the honest program: `provOf` succeeds for every `dotKF` column (it is the preceding
`piField`), and `winsOk` held for all 871 (`colOk`, `impcstat-ck.log`). Cells past `len/16` are the zero
form `[]` (`Lin.ev_nil`), matching `AuxK.val`'s `getD b 0`. The instance's fresh window is unchanged (the
old aux cells stay allocated and unreferenced; `tplOut` adds no `fresh`), so no layout, row index or cell
count moves: `ProtoFit`/`ArFit`/`hintLay` are as before.

### 3.2 Lemmas (new module `FRNodeRun4FE.lean`, below `FRNodeRun4CT`; ≈ 120 lines)

1. `colA_some {π col n l} : colA π col n = some l → ∃ f o len, provOf (pvP π) col = some (f,o,len) ∧ winsOk f o len = true ∧ l = (List.range n).map (colCell π f o len)` — unfold.
2. `aux_colA` — `aux_col` (`AskIR:183–221`) minus `hrows`: hypotheses `hone`-free, `hpc : PfCells w π inp`, `hpr`, `hw`, `hsz : absOff f o + len ≤ inp.π.size`, `hreg : regs[col]? = some (.b (inp.π.extract …))`, `hrs : col < sz`; conclusion `((List.range n).map (colCell π f o len)).map (Lin.ev w) = (AuxK.felems n).val (rd (regs.extract 0 sz) col)`. In the `b < len/16` branch `Lin.ev_cell` then `hpc _ _ he` replaces the `a1Row` step; the `else` branch is `Lin.ev_nil`.
3. `tplExt_felems'` (extends `AskIR:226`): `tplExt tc P cs op = some o → a ∈ o.aux → a.2.2 = .felems n → tc.col = some f → ∃ w col, op = .dotKF w col ∧ a.2.1 = col ∧ col < cs.slots.size ∧ f col n = some a.1`.
4. `xof_felems_alias` (the `xof_felems` unfolding, `AskIR:246–272`, one more arm): `a ∈ (stepOut (Xof π) P cs op).aux → a.2.2 = .felems n → a.2.1 < cs.slots.size ∧ colA π a.2.1 n = some a.1`.
5. **`felems_of_pf`** `{impl ι inp tr s w π} (hpc : PfCells w π inp) (hsz : inp.π.size = piSizeOf seq4) (he : execA impl ι inp (protoProg π).ops St.init tr = some (s, [])) : ∀ a ∈ (protoCS π).aux, isBitsA a = false → a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1)`. Proof: `trail_aux` (`AskIR:109–127`, with any `A`; the rows clause is unused) gives the trail point `c`, `c.slots.size = a.2`, `a.1 ∈ (stepOut (Xof π) P c op).aux`; `isBitsA a = false` gives `.felems n`; 4 then 1; `execA_prov` (`AskIR:41`) + `provOf_mem` (:71) give `hreg`; `hsz` + `winsOk`'s bound give the extract's size; 2 closes. No row, no generator, no kernel evaluation of the program.
6. `slotRunC_of_imp {rt A …} (hpc) (hsz) (himp : ∀ s, execA … = some (s, []) → ∀ i ∈ impQP rt A π, RepS w ((protoCS π).slot i) (rd s.regs i)) : SlotRunC rt A impl π ι inp tr w` — conjunct (a) by 5, (b) by `himp`.
7. Composition with SEG-R2 (which discharges (b) by failing rows at uncovered replay ops and rewires to `rtC1d`): `gaps4_fel : Sub4.Gaps4 := gaps4_of_runC' (fun … hS v hv ι hι => slotRunC_of_imp (pfCells_of_rows hS.1 hv) (by rw [slotIn_π, slotπ_size]) (SEG-R2's (b) lemma))` at whatever name SEG-R2 gives `gaps4_of_runC` (`FRNodeRun4CT.lean:155–163`) at `rtC1d`. `Solution`/`FRSubmission4Cert` then apply `certified` to `gaps4_fel`; `Open4F := Gaps4` is closed. If SEG-R2 is not yet landed, FEL ships 1–6 and the residual of `SlotRunC` is (b) alone.

### 3.3 Proofs that move (edits in place, statements kept unless noted)

- `tplExt_ok`'s `dotKF` case (`FRVIRTplExt.lean:435–445`): two more `split` branches; the alias branch
  is the same 10 lines (it uses only `hc`). `tplExt4S_okAt`/`tplExt4_okK` (`TplSet:251, 535`) unchanged.
- `tplExt_flags`, `tplExt4_flags` (`CA:38–71`): `split`-driven, should pass; the alias output is a
  `tplOut` (no `imp`/`foreign`).
- `tplExt_isNone`, `tplExt4_isNone` (`CA:72–100`) gain a `col` binder: contexts `⟨tp, cb, col⟩`,
  `⟨tp', cb, col⟩`. `tplExt4_tw_aux` (`BF:25`), `tplExt4_tw_imp` (`AskBS:87`) likewise;
  `tplExt4_imp_tc` (`AskBS:118`) gains `hcol : tc.col = tc'.col` (statement change; its callers' contexts
  share `col`). `xofA_aux` (`BF:55`), `BT:171`, `CS:91`: `simp only` unfold lists — add `protoCtx`.
- `tplExt_bits` (`BR:163`), `tplExtKM_felems`, `extGetK_aux`: untouched (no `dotKF` there).
- `compileTF4_imp` (`TplSet:546`), `tplExt4_imp` (:528): hold with the same `tc` on both sides.
- Dead after FEL (keep; golf may retire): `colTG`, `auxRows`, `colRows`, `colOk`, `SlotRunI`,
  `slotRunA_of_impc`, `withImpcC`, `askTGIC`, `atImp_col`, `aux_col` (`AskI:177–239`, `AskIR:288–437`,
  `AskIS:339`). `slotRunA_of_impc`'s `hcC`/`hrC` branch becomes vacuous, not false.

### 3.4 What does not change

`SlotRunC`, `Gaps4`, `certified`, every `gaps4_of_*` statement, `ProtoFit`, `ArFit`, `arR2N`, the row and
cell counts of both prototypes, the template bodies, `TLay`/`hintLay`, the replay templates. The plan form
stores an instance's own input forms verbatim (`Piece.ins k xh ch own`, checked by `own.all (linInB π)`,
`Plan:80–100`); arena cells pass that check. `Out.aux` cells were never required fresh (`ExtOk`,
`FRVIRCompileSound.lean:74–87`, takes the aux fact as a hypothesis).

### 3.5 Costs

| | before | after | source |
|---|---|---|---|
| rows per prototype | — | **0** new; `colTG`'s 27,856 never needed | §1 |
| cells | 27,856 aux cells allocated, free | the same cells allocated, unreferenced; 0 new | §3.1 |
| V per check | — | unchanged row/cell counts; inputs read arena cells instead of window cells | §3.4 |
| V init (process start) | — | `colA` per `dotKF`: one `provOf` (`find?` over `pvP`), `len/16` `winE` calls (17 `pfLoc` each) — the work `colTG` would have done, minus rows; `impcTG`'s ≈ 10 k windows cost +0.4 s (IMPC §3 l.141), so expect ≤ +0.3 s user. Measure (P3). Lever: an `Array` for `provOf`, `winE` once per window (the definition above calls it once in `winsOk` and once in `colCell`: compute the element list once). | |
| kernel | ≈ 390 s used of 600 | + one small module (`felems_of_pf` ≈ `aux_col`'s size; `xof_felems_alias` ≈ `xof_felems`'s). Expect < 3 s. | SIB §5 pattern |
| build | — | +1 module, the `Win` cut, ≈ 20 touched modules re-checked | |
| prover (E1) | `mfill` writes the aux cells from `maux-p{π}.txt` (`prover/mfill.rs:505–537`) | after the re-dump the aux cells **are** arena₁ cells, which the arena fill already writes with the same values; `mfill` must treat an already-set equal cell as a check, not a conflict. Plan form re-dump (INT-9 export), MxKat, `plan4t check`. | |

## 4. The other routes

- **Route 2, `colTG` rows in another band.** Per prototype 27,856 rows, in every slot of that prototype.
  Template range after SEG-R2: `arR2N` 154,368 vs rows 130,914 (p0, margin 23,454) / 154,333 (p1, margin
  35) — neither margin holds 27,856. Bands A + B (59,904 with SIB, SEG-R0 §2 l.138–141) are SEG-R2's
  segment replay (37,362 + ≈ 1.45 k, SEG-R1 §7 l.164–175): ≈ 21 k left < 27,856. CF2's cut (prototype 0's
  row blocks 373,550 → 57,972, `CF2-RESULT.md:91`) frees rows in slot 0's region only; a segment slot
  (prototype 1) gains nothing, and p0's own rows are below `arR2` (SEG-R0 l.142). A re-cut of `arR2` is
  ruled out (IMPC2 §0 l.49). Even if placed: V ≈ +75 ms per node (IMPC §3 l.144) and init in the order of
  SIB's +2.7 s for 16.6–18.3 k sibling rows (SIB §4). A second binding range would also need its own
  `askPI`/`ArFit` fit lemmas. Dominated.
- **Route 3, "already determined by existing rows".** False: the cells are multiplicands only (§1), so a
  prover sets them freely and `dotKF`'s output with them. The alias is the structural route.
- **Alias with a fresh fallback** (refuse nothing): then a non-aliased entry would stay in the residual
  and need a failing-row generator and a fold edit (SIB's `atImp_col` pattern). Refusing instead makes
  the op an import, which the closure already fails (`closeCov (.dotKF ..) = true` by `opImp`,
  `AskC:107–113, 155`; `extCan (.dotKF ..) = true` :173; `impRows` :179; `atImp_close`, `impB_sub`,
  `CB:81, 218`), so no generator, no fold change, no `askTG` edit. Completeness is a probe (P1).

## 5. Stage plan (FEL)

Files: `FRVIRTplCore` (field), `FRVIRTplExt` (arm, `TLay.ctx`, `tplExt_ok`), `FRVIRTplSet` (12 contexts),
`FRVIRTplBuild`, `FRInitFuse`, `FRNodeRows4RepFD`, `FRNodeRows4RepCFP` (contexts; `hc`), `FRNodeRows4AskPosT`
(context), new `FRNodeRows4Win`, `FRNodeRows4AskI` (cut; imports `Win`), `FRNodeRows4Defs` (`pvP`, `colCell`,
`colA`, `protoCtx`, `XofC`, `Xof`), `FRNodeRows4AskIR` (drop `pvP`), `FRNodeRows4` (`protoCS`, `Xa`),
`FRNodeRows4AskBS` (`XofA`, two lemmas), `FRNodeRun4CA`/`BF`/`BT`/`CS` (context lemmas, unfold lists),
`FRNodeRows4Plan`/`RepCFW` (call sites), new `FRNodeRun4FE`, `FR.lean` (import), then `FRSubmission4Cert`/
`Solution` once SEG-R2's (b) lemma exists. Owner boundary: `RepSeg*`/`TplSegT` (SEG-R2, SEG-R1b) untouched.

Controls (`FRNodeRun4FE`): (+) `colA_ctl`: a toy `pv` with one 32-byte register at an aligned element pair
gives two arena cells; a 48-byte one at `n = 4` gives three cells and `[]`; (−) an unaligned offset gives
`none`; a register not in `pv` gives `none`. (+) `tplExt` alias arm on `ctlCS` with `col := some (fun _ n => some (cells))`:
`aux = [(cells, col, .felems n)]`, `tin` inputs `lw ++ cells`; (−) with `col := some (fun _ _ => none)` it is
`none`, and `impRows` at it is `[failRT P]` (`impRows_ctl`'s shape, `CT:215`); (−) `col ≥ cs.slots.size`
gives `none`; (+) `tc.col = none` reproduces today's fresh cells (`rfl` against the old arm's value).

Kernel-time hazards: no `decide` over `pvP`, `winE` or the program; `felems_of_pf` must not unfold
`protoCS`/`protoProg` (use `protoCS_X` and `trail_aux`). Keep `π * slotM4 + arA1 + e` literal in `colCell`
so `hpc _ _ he` rewrites without a defeq that unfolds `HAdd.hAdd` on `arA1` (G5's root cause, QUEUE §Running).
The `split`-heavy `tplExt_*` lemmas grow at front-end time only; if `tplExt4_isNone` exceeds ≈ 20 s to
check, prove the `dotKF` arm as a separate lemma and `rw` it. Profile as SIB §5 (`profile-*.log`).

Definition of done: FR green with `FR.lean` importing `FRNodeRun4FE`; axioms of `certified` ⊆ the three;
source rule 0 findings; P1 shows 871 aliased, 0 refused, 0 failing rows per prototype; P3 init Δ ≤ +0.3 s;
`Gaps4` closed (with SEG-R2) or `SlotRunC`'s residual = (b) alone (without); RESULT with the counts.

## 6. Probes (tree `logs/fr-build-FEL`, copied from `logs/fr-build-SRA/{snap.sh,b.sh,run.sh}`; logs `logs/FEL/`)

Every run: `systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 -- timeout <s> …` as `b.sh`/`run.sh`
do; waits by `kill -0 $PID` under `timeout`; probes stay in `logs/`.

| id | probe | expect | kill line |
|---|---|---|---|
| P0 | `b.sh FRNodeRows4Defs FRVIRTplSet` after the field and the arm (`TMO` 1800) | green | an unfixable `split` in `tplExt_isNone` → the parameter route (thread `al` through `tplExtF`/`tplExt4S`/`tplExt4`; ≈ 70 one-token edits, same proofs) |
| P1 | `felstat` (from `SibStat.lean`): walk both prototypes with `XofC π`; count `felems` aux entries, refused `dotKF` (`stepOut … .imp`), `failRT` in `askTG`'s rows, cells outside `[π·2^20 + arA1, + arN)`, instances whose elements are consecutive | 871 / 0 / 0 / 0 per prototype; rows 130,914 / 154,333 unchanged | any refused or failing: list the column (`winE`'s last-block rule, ASK-P §6.1) — fallback is `colTG`'s rows for those columns only |
| P2 | `b.sh FR` (`TMO` 2400), `AxFEL` axiom check, `source-rule.py` | green, 3 axioms, 0 findings | — |
| P3 | `plan4t init` A/B, 5 alternating runs (SIB's `ab.sh`) | Δ ≤ +0.3 s user | > 0.3 s: `provOf` as an `Array`, elements computed once per column; > 1 s: memoise `pfLoc` per item |
| P4 | kernel profile of `FRNodeRun4FE`, `FRVIRTplExt`, `FRNodeRun4CA` | Δ < 3 s | > 5 s: split the unfolding lemmas per arm |
| P5 | after the re-dump: `plan4t check` N2/N4/N8, MxKat, V(N4) | V Δ ≈ 0 | V Δ > 20 ms: a dotKF instance lost its shared-input classification — inspect `piecesOf` |
