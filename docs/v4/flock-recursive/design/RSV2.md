# RSV2: the reserve across node kinds — one stacked linear claim per node

Design track D-RSV2, 2026-10-29. Memo only; no Lean built, nothing committed. Inputs read:
`stages/D1p-RESULT.md` (main), rev44's `stages/RSV-V-RESULT.md` (HEAD `213c407`), `BLUEPRINT.md`
§0.1 (B-11 … B-13), §4.3–4.4, §5.2, changes 25–26, `design/PACK-4.4.md` §8, §11, the core's
`harness/PROVER.md` §3 (the score), and rev44's Lean, read-only: `FRVIRFinals4` (`rsvEOps`,
`gFinE0`, `gFinE`, `rsvBOps`, `gFinB'`), `FRVerifierImplNode4F` (`evalMPair`, `evalMD4`,
`evalMN4`), `FRNodeRows4Plan` (`protoV4`, `starPt`, `slotV4`, `linkV4`, `evalMT4`),
`FRVerifierC4` (`rsvRel`, `rsvCells`, `nodeFinP`), `FRNodeCircuit4` (`PubCellsR4`, `StmtN4`,
`NodeResid4`), `FRNodeSound4` (`SlotRun`, `SlotImp`), `FRVIR` (`Op.evalM`, `exec`),
`FRVIRCompile` (`.evalM` → `imports cs [.f, .f, .f]`; `packFK`'s per-element mux),
`FRSoundness4P4bNames` (the E-phase dooms), `FRSoundness4R4Fin` (`relE4`, `vStar4`, `relB4`),
`FRSoundness4TailStep` (`hfin_ml`), `FRShape4` (`NodeKind.dims`), and `logs/RSV/vtime4-4.log`.

## 0. Summary and recommendation

1. **F1 is a shape problem, not a cost problem.** RSV-V binds, for the previous node `C` of a parent
   `P`, *one kind's three MLE values at C's own point* (52 cells). But what `V(C)` actually consumes
   in its finE (iv′) is **one scalar**: a linear combination of the nine matrices `M_{κ,m}`
   (`κ ∈ {N2, N4, N8}`, `m ∈ {A, B, C}`) at **one point** — its own kind's three with weights
   `f̂·(1, κ_E, κ_E²)`, plus its own child's combination with weight `κ_E⁴·eq(·)`. Whenever C's child
   has another kind, that functional has support on two kinds and RSV-V's one-kind claim misses the
   rest (the `W*` import). **Fix: make the imported object exactly the functional V consumes.** Every
   node's `evalM` becomes one call `evalM(p_x ‖ s, p_y)` at a 23/25-coordinate point `p` (the mixed
   point RSV-V already forms) with **nine public coefficients `s`**, returning `X = Σ_{κ,m} s_{κ,m}·
   M̃_{κ,m}(p)` (and two zero outputs). The parent carries `(p, s, X₃)` in `fLrEnd` (**60 cells**,
   `fLrEnd` 880 → **1,008 B**, no pad) and proves `Σ s·M̃(p) = X` in its own E2/E4 exactly as the
   reserve does today, with `s` in place of `(1, η, η²)` on one kind. The import shape is then the
   same for every kind and every depth, so the chain closes across every transition (§2.5). `εR`
   is unchanged (§2.6).
2. **F2 disappears without any protocol change beyond 1.** `protoV4` reads only the low 20 row and
   column coordinates (`starPt`: `l < 20`), so RSV-V's second `protoV4` at the mixed point
   recomputed the first one's value exactly; the kinds differ only in the slot sums (`slotV4`,
   `linkV4`, `ltbOf`). The stacked call evaluates `protoV4` once and forms every kind's slot sum from
   it. **V(N4) returns to ≈ 275 ms VM for every child kind, plus the slot sums of the kinds in the
   coefficients' support: ≈ 0–11 ms VM by B2′'s per-kind figures (§3.2), to be measured.** On the
   score, F2 as built costs **+0.59 s of V̄** (25.0 % of the stream's steps change kind, each at
   `x = 2.32`, `V̄_i = 3.32 s` against 0.97 s); RSV2 costs **+0.00 … +0.09 s** against the ideal.
3. **No uniform node shape, no uniform E-phase dimension is needed** (§6). The only uniformity the
   construction needs is the claim's point at 23/25 coordinates, which RSV-V's mixed point already
   provides; an `N2` parent sums over its 22/24 coordinates and keeps the claim's higher
   coordinates fixed, as RSV-V does. Making every node `N4`-shaped would cost ≈ +1.0–1.3 s of `P̄`
   (changes 26, item 2) to save ≤ 0.09 s of `V̄`.
4. **The `Op` set is unchanged.** The stacked call is `Op.evalM` with a 32-entry row point
   (23 coordinates ‖ 9 coefficients), as RSV-V tagged its second call by a 24-entry point;
   `evalMPair`/`evalMD4` and the kind element go away. The exact V, format and cell changes against
   `213c407` are in §4; RSV-S's brief in §5.

## 1. The problem, exactly

Notation (RSV-V §2): `η` = E1's coordinate 23; `κ_E` = E3's challenge; `f̂ = ẑ claim 3` (`fz`);
`e2R κ, e4R κ` = `(22, 24)` for `N2`, `(23, 25)` for `N4`, `N8`; `M̃_{κ,m}` the MLE of
`nodeIRows4 κ`'s matrix `m` on `logM κ` row and `logM κ + 2` column coordinates, read at a longer
point by **constant extension** (`evalMS4` uses `ptOf κ.dims.logM`: the higher coordinates are not
read — RSV-V decision 2).

**What `V(C)` computes in finE (iv′) today** (`rsvEOps`, for a node `C` of kind `κ_C` whose previous
node `G` has kind `κ_G`, with `G`'s claim `(r̄*, a*, b*, c*, kindElem*)` in C's `fLrEnd`):

```
claimN(E4) = f̂·(Ã + κ_E B̃ + κ_E² C̃)_{κ_C}(r_E2, r′) + κ_E³·L̃·f̂
           + κ_E⁴·eq(r̄*_y[<e4R], r′)·(Ã + ηB̃ + η²C̃)_{κ_G}(x̂, ŷ),
x̂ = r_E2 ‖ r̄*_x[e2R, 23),  ŷ = r′ ‖ r̄*_y[e4R, 25).
```

`V(C)` obtains the first line's three values from its own `evalM(r_E2, r′)` and the third line's
from a tagged `evalM(x̂ ‖ kindElem*, ŷ)` returning `M̃_{κ_G} − M̃_{κ_C}` at `(x̂, ŷ)`
(`evalMPair`; `0` when `κ_G = κ_C`).

**F1.** In `P`'s circuit (slot 0 replays `V(C)`), both calls' outputs are import registers
(`FRVIRCompile`: `.evalM` → `imports cs [.f, .f, .f]`), i.e. `Gap4.imp`'s open facts. RSV-V's 52
cells and `truthChild(P)` discharge the first call (three values of kind `κ_C` at `(r_E2, r′)`).
The second call's three outputs are discharged only when `κ_G = κ_C` (the spec returns `0` without
evaluating, which rows can pin). When `κ_G ≠ κ_C` nothing in `P` speaks about `M̃_{κ_G}` at C's
point: the chain is open at every kind change. Kind changes are the stream's normal course: step 1
is `N8`; every later step is `N2` with probability `6/7` and `N4` with `1/7` (`k = ⌈n/2^18⌉ ≤ 2`
iff `n ≤ 2^19`; the `1/n²` density on `[2^17, 2^20]` gives `P(n ≤ 2^19) = 6/7`); so step 2 always
changes kind and each later step changes it with probability `2·(6/7)(1/7) = 12/49 = 24.5 %`: in a
96-step stream, **24.0 of the 95 parents** (25.0 % of all steps) have a child of another kind.

**F2.** The tagged call costs one more `protoV4` (`vtime4-4.log`: V(N4) 273.9/274.8 → 471.7/462.6 ms
best with an `N2` child). But `protoV4 pl t u node` reads `t`, `u` only through `starPt`
(`FRNodeRows4Plan` 287: `if l < 20 then t l else …`), so its value at `(x̂, ŷ)` is its value at
`(r_E2, r′)`: the second evaluation is a pure recomputation. The kinds differ only in `ltbOf
κ.dims.logM`, `hiF`, and `linkV4 L κ σ` over their `vslots` — the slot sums.

**What `V(C)` actually needs** is therefore one scalar of the form

```
X^C = Σ_{κ,m} s^C_{κ,m} · M̃_{κ,m}(x̂, ŷ),
s^C_{κ,m} = [κ = κ_C]·f̂·κ_E^m  +  κ_E⁴·eq(p^G_y[<e4R], r′)·s^G_{κ,m},      (m ∈ {0,1,2})
```

where `s^G` is G's own coefficient vector: the support of `s^C` is the set of kinds in the chain
below `C`. That is the object to import and to bind; nothing smaller closes.

## 2. The construction (RSV2)

### 2.1 The claim and the op

**The stacked matrix.** Let `𝓜 = (M_{κ,m})_{κ ∈ (N2,N4,N8), m ∈ (A,B,C)}`, nine public matrices
(the three kinds' `nodeIRows4`), each read at a point `p = (p_x, p_y) ∈ F^23 × F^25` by constant
extension (`M̃_{N2}` reads `p_x[<22], p_y[<24]`). Index `i = 3·k + m` with `k = 0, 1, 2` for
`N2, N4, N8`.

**The op.** `Op.evalM t s` unchanged; the node's implementation dispatches on the row point's size:

```
evalMN4 pl ν τ σ := if τ.size = 32 then (evalMX4 pl τ σ, 0, 0) else evalMT4 pl ν τ σ
evalMX4 pl τ σ   := if pl.inR then
                      let v := protoV4 pl t u true                       -- once
                      Σ_{k<3} ⟨s_k, sum3 (slotV4 κ_k t u (ltbOf (logM κ_k) t u) v.1 v.2) (range (vslots κ_k))⟩
                    else Σ_{k<3} ⟨s_k, rows3 (logM κ_k) (logM κ_k + 2) t u (nodeIRowsP pl κ_k)⟩
   with τ = p_x[0..23) ‖ s[0..9),  s_k = (τ[23+3k], τ[24+3k], τ[25+3k]),  ⟨s_k, (a,b,c)⟩ = s_{k,0}a + s_{k,1}b + s_{k,2}c
evalMXS4 τ σ     := Σ_{k<3} ⟨s_k, evalMS4 κ_k τ σ⟩                        -- the spec
```

`evalMX4_eq : evalMX4 pl τ σ = evalMXS4 τ σ` is `evalMT4_eq` three times plus `slots_true`
(already proved: `N8`'s slot sum at `node = true` equals its sum at `node = false`). `ν` (the
node's own kind) no longer enters `evalM`: the own kind is in `s`. A kind with `s_k = (0,0,0)`
may be skipped (an optimisation; the spec is the sum either way).

**The claim a node carries about its previous node** (`fLrEnd`, 1,008 B):

```
fLrEnd = â_L ‖ b̂_L ‖ ĉ_L (48)  ‖ p_x (23 × 16 = 368) ‖ p_y (25 × 16 = 400) ‖ s (9 × 16 = 144) ‖ X₃ (3 × 16 = 48)
offsets  rsvRx = 48, rsvRy = 416, rsvS = 816, rsvX = 960;  1,008 = 48 + 15·64: block-aligned, no pad.
fEEnd  = â_M ‖ b̂_M ‖ ĉ_M ‖ m̂* ‖ 0^48 (112 B, unchanged)
```

`(p, s, X₃)` are the input entries and the three outputs of the child's single `evalM` call, copied
from the parent's circuit registers; `X₃ = (X, 0, 0)` for an honest child. `N8` writes zeros in
`fLrEnd[48, 1008)` and `fEEnd[48, 64)` (asserted where `rsv = hasPrev` is off, as RSV-V does).

### 2.2 What `V(P)` computes (node kinds; the segment group is untouched)

With `η`, `κ_E`, `f̂` as above, `p = p^C` the claim's point, `v_L` Lr's value, `L̃` as today:

- **(ii″) E2's end:** `claimN(E2) = eq(τ, r_E2)·(âb̂ − ĉ) + η·eq(p_x[<e2R], r_E2)·(m̂* − X)`.
  E2 stays a zero-claim zerocheck (RSV-V decision 1); its summand is
  `eq(τ,x)(Az·Bz − Cz)(x) + η·eq(p_x[<e2R], x)·(Σ_i s_i·M̃_i(x ‖ p_x[e2R, 23), p_y) − X)`, degree ≤ 3.
- **(iii″) E4's initial claim:** `claim0(E4) = â + κ_E b̂ + κ_E² ĉ + κ_E³ v_L + κ_E⁴ m̂*` (as RSV-V).
- **(iv″) E4's end:** `claimN(E4) = X^P + κ_E³·(Ã_L + κ_L B̃_L + κ_L² C̃_L)(r_Lr, r′)·f̂`, with
  `X^P = evalM(x̂ ‖ s^P, ŷ)`, `x̂ = r_E2 ‖ p_x[e2R, 23)`, `ŷ = r′ ‖ p_y[e4R, 25)` and
  `s^P_{κ,m} = [κ = κ_P]·f̂·κ_E^m + κ_E⁴·eq(p_y[<e4R], r′)·s_{κ,m}` (nine registers: 3 products
  `f̂κ_E^m`, 9 products by the kind constant `[κ = κ_P]` — a kind-dependent constant, selector-linear
  under the mux —, 1 product `κ_E⁴·eq`, 9 products with `s`, 9 sums).
  E4's summand gains `κ_E⁴·eq(p_y[<e4R], y)·Σ_i s_i·M̃_i(x̂, y ‖ p_y[e4R, 25))`, degree 2.
- **Zero asserts:** `X₃[1] = X₃[2] = 0` (two `assertZero` on the imports, every node kind);
  `fEEnd[64, 112) = 0` (every kind); `fLrEnd[48, 1008) = 0` and `fEEnd[48, 64) = 0` where `¬rsv`.
- **No own `evalM` call remains in the node program**, and the own (ii)/(iii)/(iv) asserts of
  `gFinE0` are off for every node kind (`N8` included: its child block is zero, so (ii″)–(iv″)
  reduce to the own checks: `η·eq(0, r_E2)·(0 − 0) = 0`, `κ_E⁴·0`, `s^P = own`). The three
  asserts (ii″)–(iv″) are gated by `node` only; `rsv` gates the zero asserts.
- **B′:** `claim0(P1) = vRS + κ′²·S₉ + κ′^{11}·Σ_{i<60} κ′^i v_i`, `v = p_x ‖ p_y ‖ s ‖ X₃` (finE's
  exports), gated `rsv` as RSV-V (the own assert where `¬rsv`): `N8` has no slot 0, hence no
  cells to claim. (Since `N8`'s `v` is asserted zero, one ungated list would assert the same value;
  the gate is kept so that B′ and finPf select the same cell set.)
- **finPf:** 60 cells `rsvCells κ` at `κ′^{11 … 70}` where `rsv` (`keep rsv` as now; `rsvCells N8
  = []`); `rsvRel` re-read from the dump: the 48 entries of the packed mixed point — for entries
  22 and 24 the compiler's per-element mux cell, `FRVIRCompile` 303 —, the 9 coefficient
  registers, the three outputs.

### 2.3 The prover (P2)

- E2: `m̂* = Σ_i s_i·M̃_i(r_E2 ‖ p_x[e2R,23), p_y)`; the child table over `x ∈ {0,1}^{e2R}` is
  `Σ_i s_i·M̃_i(x ‖ hi, p_y) − X` — per prototype three matvecs by `eq(p_y[<logM+2])`-vectors, then
  the per-kind slot weights and `s`: the same six matvecs the reserve needs today (the kinds share
  the two prototypes; a kind's weight is a scalar per slot).
- E4: the vector `y ↦ Σ_i s_i·M̃_i(x̂, y ‖ hi)`: per prototype three vector-matrix products by
  `eq(x̂)`, as today.
- `fLrEnd`: copy the child's `(p, s, X₃)` registers; `s^P` is not in π (the parent of `P` computes
  it in its circuit and `V(P)` in its finE).
- Cost: unchanged from D1p's estimate (**+0.1–0.3 s per node, unmeasured**; D1p open question 1
  stands). The stacked form adds nine scalar products per prototype row block, nothing else.

### 2.4 What the child's verifier imports, and how each import is bound

Slot 0 of `P` replays `V(C)` (`SlotRun`/`SlotImp`, `FRNodeSound4`). Its imports and their bindings
after RSV2:

| Import in `V(C)`'s replay | Registers | Bound by |
|---|---|---|
| C's proof fields: `fLrEnd` (`p^G`, `s^G`, `X₃^G`), `fEEnd` (`m̂*_G`), every other `piElem`/`piField` | arena₁ aliases of C's stream cells | the pack map (S-E13a `imp`), unchanged |
| C's challenges (`η_C`, `r_E2^C`, `κ_E^C`, `r′^C`, `κ_L^C`, `κ′_C`, …) | squeeze answers | the FS chain's H rows, unchanged |
| C's `f̂_C` (`ẑ` claim 3), `v_L` | RS messages | the pack map, unchanged |
| the mixed point `x̂_C ‖ s^C`, `ŷ_C` | 48 + 9 registers: C's challenge registers for `l < e2R_C`/`e4R_C`, C's `fLrEnd` imports for the two higher entries (kind-muxed cells), 9 computed registers | computed by rows from the above (the mux rows for entries 22/24; the `s^C` product rows) |
| **C's `evalM` outputs `X₃^C`** | 3 import registers, `rsvRel[57..60)` | **`PubCellsR4 κ_P w (childVals π_P)` (60 cells) ∧ `truthChild(P)`: `X = Σ_i s_i·M̃_i(p)` ∧ `V(P)`'s two zero asserts** |
| C's `evalL`, `targetS`, `shiftTarget`, `linkWAll`, `rsWeight` outputs | import registers | `R`/templates (QUEUE's node-circuit gap item 7), unchanged by RSV2 |

Discharge of the `evalM` fact in `SlotImp` (replacing RSV-V §5's three-step argument):
1. `PubCellsR4` (from `P`'s B′/finPf point claims on its own `f`): the 60 cells hold `P`'s `fLrEnd`
   values `p ‖ s ‖ X₃`.
2. `truthChild(P)` (from `P`'s E-phase): `X = Σ_i s_i·M̃_i(p)`; `V(P)` asserted `X₃[1] = X₃[2] = 0`.
3. The run of `V(C)` fed its `evalM` the registers whose cells are `rsvRel[0..57)`, so the spec's
   output at those inputs is `evalMXS4 (p_x ‖ s) p_y = (Σ_i s_i·M̃_i(p), 0, 0) = X₃`: `RepS` holds at
   the three output cells. `evalMN4_eq` at a 32-entry point. `R` is not needed.

Segment slots (the aggregate's `k` sub-verifiers) have no E content (`relE4`: `if node then … else
e4`): their `.evalM` outputs are dead imports whose binding is `R`'s (item 7 above) and is not
touched here. The aggregate's own checks (`aggChk`, `aggPad`, the chaining) are untouched.

### 2.5 Closure across every transition

The import of slot 0 has the same shape — `(p ∈ F^48, s ∈ F^9, X₃ ∈ F^3)` — for every child kind
and the same binding for every parent kind, so the chain is closed by induction on the step:

| Parent ← child | `p` | `s^C`'s support | what `P` proves |
|---|---|---|---|
| `N2`/`N4` ← `N8` (step 2) | `N8`'s own 23/25 point | `{N8}` | `Σ s·M̃(p) = X` with the child's own `N8` coefficients |
| `N2` ← `N2` | C's mixed point: `r_E2^C[<22] ‖ p^G_x[22]`, `r′^C[<24] ‖ p^G_y[24]` | `{N2, N8, …}` | the parent sums over 22/24 coordinates, the claim's coordinates 22/24 fixed |
| `N2` ← `N4`, `N4` ← `N2`, `N4` ← `N4` | C's point (23/25) | every kind below | as above; an `N4` parent sums over all 23/25 |
| `N8` (step 1) | none | — | nothing: child block zero, (ii″)–(iv″) reduce to the own checks |

The support of `s` grows to every kind that has occurred in the chain (from step 3 on, typically
all three), which is why one claim with nine coefficients is the right object and a per-kind claim
is not. `P`'s own `V` evaluates `protoV4` once and sums the slots of the kinds in `supp(s^P)`.

The constant extension is what makes a single 23/25-coordinate point serve every kind: for `P =
N2` and `κ = N4`, `x ↦ M̃_{N4}(x ‖ p_x[22], p_y)` on `{0,1}^22` is multilinear with the top
coordinate fixed in `F`, and `Σ_x eq(p_x[<22], x)·M̃_{N4}(x ‖ p_x[22], p_y) = M̃_{N4}(p_x, p_y)`; for
`P = N4` and `κ = N2`, `x ↦ M̃_{N2}(x[<22], p_y[<24])` on `{0,1}^23` is constant in `x_22` and
`Σ_x eq(p_x, x)·(…) = M̃_{N2}(p_x[<22], p_y[<24])`. Both are `evalMS4 κ`'s value at `p` (`ptOf`
truncation): the spec and the sumcheck agree with no case split beyond what RSV-V already has.

### 2.6 Soundness in the S-G doom model; `εR`

Dooms are decided by the chain prefix at a squeeze (`FRSoundness4TailStep.PhaseObl`: `hsingle`
for a single squeeze, `hfin` through `hfin_ml` for a multi-squeeze zero test). `fLrEnd` (item 213)
is absorbed before E1, so `p`, `s`, `X` are prefix-determined when `η`, `κ_E` are drawn; `fEEnd`
(273) before E3.

| Phase | Doom (node kinds) | Row | Lemma |
|---|---|---|---|
| E1 (`hfin`, 12 squeezes = 24 coordinates `τ ‖ η`) | the table `T(x) = eq(τ,x)·R(x) + η·eq(p_x[<e2R], x)·(Σ_i s_i M̃_i(x ‖ hi, p_y) − X)` sums to a multilinear polynomial `Σ_x eq(τ,x)R(x) + η·D`, `D = Σ_i s_i·M̃_i(p) − X`, in `e2R + 1 ≤ 24` variables; nonzero iff `RowsBad (nE4)` or `ChildBad4 (D ≠ 0)`; dooms where it vanishes at the drawn `(τ, η)` | `(e2R + 1)/2^128 ≤ 24/2^128 = 2^-123.4` | `hfin_ml` with `n = e2R + 1 ≤ r·2 = 24` (unchanged lemma; the hypothesis `hn` holds) |
| E2 rounds | degree-3 rounds (`eq·M̃` is degree 2 per variable) | `3/2^128` per round | `D3_single`, unchanged |
| Eend (absorb `m̂*`) | `habs` | — | |
| E3 (`κ_E`) | `BatBadE4`: the five batched claims `â, b̂, ĉ, v_L, m̂*` — a nonzero polynomial of degree ≤ 4 in `κ_E` | RSV-V's accounting `8/2^128 = 2^-125` is an upper bound and stands | `batch_bad_le` |
| E4 rounds | degree 2 (`eq(p_y, y)·M̃(x̂, y‖hi)` is degree 2) | `2/2^128` per round | `D2`, unchanged |
| finE (iv″) | `RejFinE4` reads the stacked `evalM` at the 32-entry point | no row (a check) | `e_fin4` with `hM` restated |
| B′ (`κ′`) | `J_f = 9 + 60 = 69` point claims, powers `κ′² … κ′^{70}` | `70/2^128 = 2^-121.9` (RSV-V: `62/2^128`) | `single_B4` |

Every row is below the per-fresh-query maximum `2^-120.36` (P2's), so `deltaR` and **`εR = 15/2^124`
are unchanged**, as RSV-V §5 item 5 found for its rows. Why the stacked form keeps E1's row linear
in `η`: the alternative of importing nine raw values `Y_i = M̃_i(p)` and batching them with powers
`η^{i+1}` (57 cells, no `s` in π) makes the E1 polynomial degree 10 in `η`, outside `hfin_ml`'s
multilinear form (a new lemma, and a `(e2R + 10)/2^128` row); with public coefficients the child
term is `η·D` exactly as RSV-V's.

`truthChild(P)` for the chain is the statement `(p, s, X₃) = childVals π_P → X = Σ_i s_i·M̃_i(p)`
with `M̃_i` the MLEs of `nodeIRows4 κ_i` (`entMat (srcE κ_i)` at `e2R κ_i`/`ncR κ_i`, `ptOf`); it
is the `¬ChildBad4` conjunct that joins `truthE` under `accept ∧ ¬dooms`.

## 3. F2: the options, priced

### 3.1 The score basis and the frequency of kind changes

`V̄ = κ·(1/M)·Σ_i max(x_i, x_i³)`, `x_i = V_i/v_ref + |π_i|/2 MiB`, `κ = 0.2667 s` (PROVER.md §3:
**per step**, so a slow step is charged cubically on its own). S-I's basis: `v_ref = 206.6 ms`,
VM → 7763 ratio 1.19. V(N4) today (B2′ + RSV-V, same-kind child): 275 ms VM best = 231 ms runner;
`|π| = 876,176`: `x = 1.536`, `x³ = 3.63`, `V̄_i = 0.967 s`. With a child of another kind (RSV-V as
built): 467 ms VM = 392 ms runner, `x = 2.317`, `x³ = 12.44`, **`V̄_i = 3.32 s`**. Kind changes:
`1 + 94·12/49 = 24.0` of 96 steps (§1), **25.0 %**. V(N2) and V(N8) are not measured; `evalMT4`
N2/N4/N8 = 144.7/147.7/113.0 ms (B2′), so V(N2) ≈ V(N4) and V(N8) ≈ 35 ms less; the table uses
V(N4) for every step.

### 3.2 The options

| Option | V (VM ms), N4 parent | `\|π\|` | rows (slot 0, per prototype) | prover | `ΔV̄` vs RSV-V same-kind (0.967) | closes F1? |
|---|---|---|---|---|---|---|
| **RSV-V as built** (second `protoV4` on a kind change) | 275 same kind; **467** other kind | 876,176 | +≈ 3.0 k ops (52 cells) | D1p's +0.1–0.3 s/node | **+0.59 s** over the stream (0.75·0.967 + 0.25·3.32 = 1.556) | **no** |
| (a) uniform E-phase dimension (every node's E2/E4 at 23/25 rounds; `N2`'s `e2R`/`e4R` 22/24 → 23/25, `dims.logM` 22 → 23 for the sumcheck only) | as (b) | as (b) | as (b) | `N2`'s E2/E4 tables doubled (a zero upper half) or one trivial extra round each; `N2` is 86 % of nodes | as (b) | only with (b)'s coefficients; by itself no |
| (b) **one evaluation point** = the mixed point `(x̂, ŷ)`, one `protoV4` (RSV2's op) | 275 + slot sums of `supp(s)`: **+0 … +11** (3 + 5 + 8 = 16 `slotV4`/`linkV4` instead of 5, two more `ltbOf`; B2′: N4 − N2 = 3.0 ms for 2 slots more; N8 is 34.7 ms below N4 with 3 slots more and without `slotV3 p0` (34.9): 0–1.5 ms per slot) | **876,304** (+128) | +≈ 0.35 k ops: 8 more imports (0 rows), ≈ 31 product rows for `s^P`, 2 mux rows (entries 22/24, already in RSV-V), finPf +8 cells × 53 ops, B′ +16 ops; −1 `evalM` import (3 cells) | unchanged (§2.3) | **+0.000 … +0.087 s** (`δ` = 0 / 5 / 11 ms VM: 0.967 / 1.006 / 1.054) | **yes** |
| (c) batching the child's claim with the parent's own `evalM` at a shared point | this is (b): the own evaluation and the child's are one linear functional at one point, with public coefficients; nothing separate to batch | | | | | |

(a) is subsumed: with coefficients, the point already has 23/25 entries for every kind and the
`N2` parent's sums over 22/24 coordinates are the spec's `ptOf` truncation (§2.5). It would move
`e2R N2`, `ncR N2`, every `OnNode` doom's dimension for `N2`, P4b's E positions for the formerly
dummy 23rd E2 round, and `nodeIRows4 N2`'s row space; it buys nothing in V or in the circuit.
**Recommendation: (b) = RSV2.** The one figure to measure is `δ` (the extra slot sums): if it is
above ≈ 5 ms VM, the lever is sharing `slotV4`'s scaled prototype value between `N4` and `N8` at
equal `σ` (same `logM`, same `hiF` weights; only `linkV4` differs by `packB`), and skipping kinds
with `s_k = 0` costs nothing.

**Stream figures for (b)** (from RSV-V's: `fLrEnd` +128 B): `|π| = 876,304`; a segment stream
`1,551,104 = 64·24,236` (+2 blocks); `aggL k = k·24,236` (48,472 / 72,708 / 96,944); `hUsed`
74,013 / 122,491 / 195,208 (+6 / +10 / +16); `hEnd` 74,021 / 122,499 / 195,216; **`N8`'s `lBase`
stays 195,328 ≤ 195,584** (112 blocks inside the 256-rounding, 256 spare above); items 8,783,
positions and phase indices unchanged (no new item, no new phase). `x`'s size term 0.4178 → 0.4179.

## 4. The exact changes to rev44 at `213c407`

### 4.1 Format

| Module | Change |
|---|---|
| `FRShape4` | `Seq.lrEnd`: `seq4` **1,008** (was 880); `seq4_eq`; `fieldSizesOf_seq4`; `piSizeOf_seq4 876304`; `streamBytesOf_seq4 1551104`; `chainLenOf_seq4 24236` |
| `FRNodeKinds4` | `segB 1551104`, `cLen 24236`, `hEnd_eq` (74,021 / 122,499 / 195,216) |
| `FRNodeLayout4` | `aggChainLen_eq` (48,472 / 96,944), `aggChainLen_k3` (72,708), `hUsed_eq` (74,013 / 122,491 / 195,208), `regions_fit` (N8 `lBase` 195,328 unchanged), `regions_need_levers` |
| `FRX4Prog`, `FRX4Ext` | `876176 → 876304` |
| `FRVIRTpl4Bridge` | `protoR_ctl` `(24236, 96944)`, `(24236, 48472)`, `(96944, 96944)` |
| `reassemble` (S-H4's `rsPhase`) | the Lrend row's length; no special case |

### 4.2 V (`FRVIRFinals4`)

- Offsets: `rsvRx 48`, `rsvRy 416`, **`rsvS 816`, `rsvX 960`**; `rsvAbc`, `rsvKind` deleted.
- **`rsvEOps`** (registers from `c`): imports `piElem fLrEnd` ×(23 + 25 + 9 + 3) = **60** (exports
  for B′), `piElem fEEnd 48` (`m̂*`); zero asserts `piField fEEnd 64 48` (all kinds), `piField
  fLrEnd 48 960` and `piField fEEnd 48 16` where `¬rsv`; `assertZero` on the imports `X₃[1]`,
  `X₃[2]` (all node kinds); `packFK (rx.take e2R)`/`eqPt (b+4)`, `packFK (ry.take e4R)`/`eqPt (b+17)`
  as now; the nine `s^P` registers (`mulF` ×22, `addF` ×9: `f̂·κ_E^m` from `fz`, `kE`, `b+10`;
  `.const (fun κ => .f [κ = N2])` etc. — three kind constants; `κ_E⁴·eq` from `b+10`); **one**
  `packFK (fun κ => chals fi "E2" e2R ++ rx.drop e2R ++ sRegs)` (32 entries), `packFK (chals "E4"
  e4R ++ ry.drop e4R)` (25), **one** `.evalM`; (ii″) with `X` in place of `v*` (the `η v*` products
  go); (iii″) as now; (iv″) `assertEq (X^P + kE³·wL·fz) (claimN "E4")`, where `wL` is `gFinE0`'s
  `b + 32` (its `evalL` chain stays). Gates: (ii″)–(iv″) by `node`, the zero asserts by `rsv`/`allK`.
- **`gFinE0`** for the node group (`rsvOps`): the own `.evalM (b+4) (b+17)` replaced by three
  `.const (fun _ => .f 0)` so that `b + 18 … 37` keep their numbers (the (iv) chain computes zeros,
  its assert is off), `act := fun _ => false`; or the own block cut and renumbered — RSV-V kept
  numbering to bound the restatement; recommended again. The segment group is untouched.
- **`gFinE`**: exports `(b + 17) :: 60 registers`.
- **`rsvBOps`**: Horner over 60 values (`List.range 59`), `κ′^{11}` as now, the claim
  `vRS + κ′²·S₉ + κ′^{11}·S` asserted where `rsv`; `gFinB'`'s own assert where `¬rsv`, as now.
- **`gFinPf`**: the second cell chain over `P.nrcell = 60` cells, `keep rsv`, as now.
- `FinP`: `nrcell := 60`; `noAsk_rsvEOps`, `noAsk_rsvBOps` re-proved (no `ask` added).
- `FRVIR4At`, `FRVIR4Uni`: the `SameCounts`/`nodeQ_counts` components for the new op counts.
- Expected program sizes: node programs ≈ 154,433 + ≈ 350 − 1 `evalM`; segment programs 151,226
  unchanged.

### 4.3 Cells and the circuit

- `FRVerifierC4.rsvRel`: **60** M-relative cells, re-read from `nodedump4`'s `mregs-p0.txt`:
  the stacked call's row-point entries 0..22 (for `l < e2R` of the muxed kind the E2 challenge
  cells; entry 22 the mux cell `Σ_κ sel_κ·x_{κ,22}`), the column-point entries 0..24 (entry 24 the
  mux cell), the nine `s` registers' cells, the call's three output cells; `rsvCells κ = 3·2^logM
  + rsvRel` where `hasPrev`, `[]` for `N8` (no slot 0), as now; `nodeFinP … 60`.
- `FRNodeCircuit4.PubCellsR4` unchanged in form (60 values); `rsvCells_ctl`: 60 for `N2`/`N4`,
  none for `N8`, inside slot 0's region and `f`, distinct, disjoint from `cells4`.
- `FRNodeRows4Hint`: regenerated (`laydump4`, B2′'s `mkhint.py`); `inR` must come back `true`.
- Rows: slot 0's prototype gains ≈ 31 product rows (`s^P`) and ≈ 320 rows of finPf's longer
  chain, loses one `evalM` import; no new import class.

### 4.4 The node's `evalM` (`FRVerifierImplNode4F`)

- Delete `kindElemN`, `kindOfElem`, `sub3`, `evalMPair`, `evalMD4`/`evalMDS4` and their lemmas;
  add `evalMX4`, `evalMXS4`, `evalMX4_eq` (§2.1; from `evalMT4_eq` and `slots_true`);
  `evalMN4 pl ν τ σ := if τ.size = 32 then (evalMX4 pl τ σ, 0, 0) else evalMT4 pl ν τ σ`,
  `evalMNS4` likewise, `evalMN4_eq`.
- `implN4F_hM`: a point of size `e2R ν ∈ {22, 23}` is untagged (unchanged proof); **add
  `implN4F_hMX`**: at a 32-entry row point `evalM = (Σ_{k<3} ⟨s_k, matMLE (srcE4 κ_k)⟩ (ptA (e2R κ_k) τ) (ptA (ncR κ_k) σ), 0, 0)` — the form RSV-S's `RejFinE4` needs.
- `implN4F_ctl`, `evalMD4_ctl` → `evalMX4_ctl`: (+) `s` on one kind returns that kind's
  `κ_E`-combination; (−) a coefficient on another kind changes the value; (+) `s = 0` gives `0`.
- `VTime4`: the child-kind tag replaced by a coefficient vector with full support (the measurement
  of `δ`, §3.2, alternated with `213c407`'s binary on one core).
- KAT (`probe/RsvKat.lean`): chains `N8 → N4 → N2 → N2` and `N8 → N2 → N4` with honest `s`
  of full support; (−) `X + 1`; (−) one `s_i + 1`; (−) `p_x[0] + 1` with the prover honest at it;
  (−) `X₃[1] ≠ 0`; (+/−) `N8`'s zero block.

### 4.5 The soundness modules (red set, for RSV-S)

Unchanged from RSV-V §5's list of 7 build failures, with RSV2's content: `flag_gFinE`, `flag_gFinB'`
(`FRSoundness4R4Fin`), `noAsk_gFinE`/`gFinB'`/`gFinPf` (`FRSoundness4Qry`), `fsMsgs4_ends`
(`FRSoundness4R4FrE`: 1,008 and 112), `gFinPf_reloc` (`FRSoundness4R4PfFlag`).

## 5. Brief for RSV-S (the soundness restatement)

Owner: one agent on rev44 after RSV-V2 (the V side of §4) builds green with the same 7 sorries.
Modules and statements, in dependency order:

1. **`FRSoundness4R4Fin`**: `relE4` for node kinds becomes (ii″) ∧ (iii″) ∧ (iv″) ∧ (v), reading
   `p`, `s`, `X₃` from `fLrEnd` at `rsvRx/rsvRy/rsvS/rsvX`, `m̂*` from `fEEnd 48`, with
   `impl.evalM (x̂ ++ s^P) ŷ` (32/25 entries) in (iv″) and the two zero conjuncts `X₃[1] = X₃[2] = 0`;
   `vStar4` gains `κ′^{11}·Σ_{i<60} κ′^i v_i` for node kinds; `relB4` unchanged in form;
   `flag_gFinE`, `flag_gFinB'` re-proved against the new op lists.
2. **`FRSoundness4Qry`**: `noAsk_gFinE`, `noAsk_gFinB'`, `noAsk_gFinPf` from `noAsk_rsvEOps`,
   `noAsk_rsvBOps`, `gCellsOpsK`.
3. **`FRSoundness4R4FrE`**: `fsMsgs4_ends` (1,008 / 112); `relE4_of_accept`, `e_end4`,
   `not_rejEndE4_node`, `e_in4`, `not_rejInE4_node`, `e_fin4`, `not_rejFinE4_node` with the new
   `relE4`; `e_fin4`'s `hM` hypothesis in the form `implN4F_hMX` gives; `vEnd_lr4`, `lr_end4`
   (first 48 bytes of the two messages, lengths updated). **`FRSoundness4R4FrRS.relE4_of_fields`**;
   **`FRSoundness4R4Start.start4_of_fields`, `start4_node`**.
4. **`FRSoundness4R4PfFlag`**: `gFinPfR` with the second cell chain (60) and `keep node`; `relPf4`;
   **`FRSoundness4R4PfFin`**: `relPf4_of_fields`, `fin4_of_fields`, `hz_of_fields` (the weight gains
   `Σ_{i<60} κ′^{11+i}·eq(c_i, ρ)` for node kinds).
5. **`FRSoundness4P4bNames`** (positions unchanged: E1 after 214, E2 227…, Eend 273, E3 274,
   E4 275…, E4end 325, B′ after RS1):
   - `ZCwE4`, `D3E4`, `EndBadE4`, `RejEndE4` (`RejEndG (e2R κ) 214 227 23`): the summed table on
     node kinds is `eq(τ,x)(Az·Bz − Cz)(x) + η·eq(p_x[<e2R], x)·(Σ_i s_i·M̃_i(x ‖ p_x[e2R,23), p_y) − X)`,
     `η = coordAt es 214 23`, `p, s, X` from the Lrend message (213; bytes 48 … 1,008),
     `M̃_i = entMat (srcE κ_i)` at `e2R κ_i`/`ncR κ_i` read by `ptOf` at `κ_i`'s coordinates;
   - **`truthChild4 es := X = Σ_i s_i·M̃_i(p)`**, **`ChildBad4 := ¬truthChild4`**, joining `nE4`
     in E1's escape (the `η·D` term; `hfin_ml` at `n = e2R + 1`);
   - `c4E4 += κ_E⁴·m̂*` (`readF (msgAt es 273) 48`); `wEb4 += κ_E⁴·eq(p_y[<e4R], y)·Σ_i s_i·
     M̃_i(r_E2 ‖ p_x[e2R,23), y ‖ p_y[e4R,25))`; `BatBadE4` (row ≤ `8/2^128`); `D2Eb4`, `RejInE4`,
     `RejFinE4` read the new `c4E4`/`wEb4`, `RejFinE4`'s `W(r′)` through the stacked `evalM` spec;
   - `PubOK4`/`single_B4` with the second cell family `rsvCells κ` (60; `J_f = 69`, row
     `70/2^128`); `FRNodeCircuit4.StmtN4` gains `PubCellsR4 κ w (childVals π)`.
6. **The chain** (`FRNodeSound4`/`FRNodeRows4Rep`): `gap4Imp_of_rsv` — `SlotImp`'s `evalM` fact at
   slot 0 from `PubCellsR4` + `truthChild4` + the zero asserts (§2.4), `evalMN4_eq` at a 32-entry
   point; the `N8` parent case is the zero claim (no previous node: `isPrevSlot` false, nothing to
   discharge).
7. **`εR`**: the row table gains nothing new in kind: E1 `(e2R + 1)/2^128`, E3 `8/2^128`, B′
   `70/2^128`, all `< 2^-120.36`; `ks_rev4GR` (or its successor) builds at `εR = 15/2^124`;
   `claim.json` unchanged.
8. Controls: `truthChild_pos` (an honest chain's `X`), `childBad_neg` (`X + 1` is in `ChildBad4`
   and E1's escape fails at a generic `(τ, η)`), `kindChange_pos` (the `N2 ← N4` and `N4 ← N2`
   discharges go through with full-support `s`), `n8_zero` (the zero claim is `truthChild4`).
   Statements of the 3.x chain and of `FRSoundness4TailCap`/`TailD`/`TailC`/`TailLig`/`R4Cap`
   are untouched (no phase index moves; `capChkOps` unchanged).

## 6. Does the clean answer need a uniform node shape?

No. The three kinds keep `nodeLayout4`, the slot-0 mux over `{N2, N4, N8}` and `N_M = 2^22/2^23`
as they are; the claim's point is uniform (23/25) by the mixed point, and the claim's coefficient
vector is uniform (nine entries) because it ranges over all three kinds' matrices. What a uniform
shape would change, for the record:

| | as is (RSV2) | every node `N4`-shaped (`N8` cannot: 8 segments) |
|---|---|---|
| `V` | one `protoV4`; slot sums of `supp(s)`: + 0–11 ms VM | one `protoV4`; one kind's slot sums (`N8` still separate): saves ≤ 11 ms VM, ≤ 0.09 s of `V̄` |
| prover `P̄` | tight packing kept | `N2` (86 % of nodes) at `N4`'s 5 slots and `m = 32`: changes 26 item 2 in reverse, **≈ +1.0–1.3 s of `P̄`** |
| Lean | §4 | `NodeKind.dims`, `nodeLayout4`, `hUsed_eq`, `regions_fit`, `childOk4`, the mux, every `OnNode` doom at `N2` |

Recommendation: keep the kinds; adopt RSV2.

## 7. Open points for the orchestrator

1. **Measure `δ`** (the extra slot sums) on RSV-V2's binary before quoting V(N4); the ceiling from
   B2′'s per-kind figures is ≈ 11 ms VM (+0.09 s of `V̄`), the expectation a few ms.
2. The prover's reserve cost is still D1p's estimate (+0.1–0.3 s per node); RSV2 does not change
   the work, but P2 must measure it (D1p open question 1).
3. D1p's open question 2 (deferring `evalL` the same way, dropping `R`'s `evalL` rows) composes
   with RSV2 unchanged: it would be a second stacked claim (`lrR κ` + `ncR κ` coordinates, three
   coefficients per kind) with the same import shape; not part of this track.
4. The segment slots' dead `evalM`/`evalL` imports (E is node-only) are `R`'s/C1's (QUEUE item 7);
   if the compiler lists them as `imp` registers they need a binding of the same trivial kind as
   RSV2's two zero outputs (rows pinning the dead cells, or exclusion from `imp`); to be settled
   there, not here.
