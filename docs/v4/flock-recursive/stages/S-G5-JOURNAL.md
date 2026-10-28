# S-G5 JOURNAL: the PIOP front (Z1 … B′) of the knowledge-soundness proof

Base HEAD `f1c0390` (S-G4). Build tree `logs/fr-build-SG5` (copied from `fr-build-SG4`, `.lake`
reused). `snap.sh` takes HEAD's sources and symlinks `FRSoundnessFr*` (S-G5's modules, and
`FRSoundnessFront`, which the glob also matches: S-G5 may repair it) to the worktree. `b.sh`
builds under the 16G scope with a `timeout`.

## Pass 1 (2026-10-28)

### 1. The interface (read off HEAD)

- `FrontObl RejF DF W₀ c₀` (`FRSoundnessCompose`): `loc` (`FrontLocal`), `rej` (`RejOK`), `ms`
  (`msD` form of every multi-squeeze range before P1.0), `habs` (absorbs before P1.0), `handoff`
  (B′'s doom at P1.0's first absorb gives `D1 0`), `hsingle` (`≤ 239·2^128` per single squeeze),
  `hfin` (`condCount ≤ deltaR` per range), `hstab` (on `StabExt` extensions).
- `FrontChainStab RejF DF`: `RejF` and `DF k` read the same off `L.take j` and `L` on the chain.
- `hAcc_of_fin` (`FRSoundnessAccLog`) leaves `hStart`, `hW0`, `hFront`; `finalLaw_of_run` /
  `finalLaw_of` leave `hExt`.
- **`hExt` only needs the doom of phase 2** (`cap₀`): it receives `¬ DC` on every prefix of the
  accepted chain. If `DF 2 := far₀ ∨ ¬ Stmt` (`Stmt` = every statement truth of the kind on the
  decoded `f⁽⁰⁾`), the prefix of length 3 gives `¬ far₀ ∧ Stmt`, and `Reads 3` carries it to the
  whole chain. The later phases' dooms only serve the counts. This is the design below.

### 2. The design of `DF`

`DF k = Bg_k ∨ U_k` (S-G1j's shape). `far₀ := farL κ L es 0` is in every `Bg_k`, `k ≥ 2`. The
statement parts not yet reduced stay in `Bg_k` until their sub-protocol starts; a finished
sub-protocol leaves its pending claims (claims on `ẑ`/`f̂` at a point: `α_Z`, `α_Lc`, `α_Sh`,
`v_L`, `α_E`) in `Bg_k` until RS0 consumes them. Every `Bg_k` term `Reads (phStart k)`.

- `Stmt κ` (phase 2): `truthZ`/`truthZN` (Z), `truthS1N`/leaf `ShHolds` (S), `truthLr` and
  `truthE` (node), `PubCells` (node, B′'s cells). (`truthLc` is not a statement part: L is the
  lincheck of Z's `â, b̂`.)
- The pending claims: `α_Z = P^z*(λ)` (Z2), `α_Lc` (L3's `v_β`, `finLc` (ii)), `α_Sh` (S2's end,
  `finSh` (ii)), `v_L` (Lrend's triple, batched into E4), `α_E = α₄` (E4 end, `relE_e4end`).
- RS0's doom: some pending claim wrong ⇒ (with `finRS`'s column check `rsAlpha` passing) some
  slice wrong: `¬ truthRS0`. RS1: `rs1_of_not_truthRS0` (`10/2^128`). B′: `v_RS` wrong or a
  public cell wrong, and `v*` batched true: `batch_pow_bad_le` at 10.
- Handoff: `DF 25 = far₀ ∨ (¬ far₀ ∧ c₀ ≠ ⟨W₀, f⁽⁰⁾⟩)` in `D1 0`'s form (`closeP_zero`, `D2` with
  no answered round).

### 3. `W₀`, `c₀` (log readers mirroring the registers of `w0V` and `relB`)

- `W₀ L es y = rsW(y) + [node] Σ_k κ′^(k+2) [y = pfCells_k]` (`w0F`'s form, in K), with
  `rsW(y) = Σ_j κ^j Φ_{r″}(eq(p_j, cube y))` over the kind's claim points `p_j` (`rsPtIx`: Z, Lc,
  Sh, and E4 for a node), `r″` = RS1's coordinates 0–6, `κ` = RS1's coordinate 7 (`rsWeightS` is
  its extension by `weight_mle`).
- `c₀ L es = ι(v_RS + [node] κ′²·pubH(κ′))`, `v_RS = Σ_j κ^j Σ_i bb_i Φ_{r″}(s_{j,i})` (`rsV`),
  `s_{j,i}` read off RS0's message (`rsOff`), `κ′` = B′'s answer, `pubH` over the seed's `vk`
  and the statement's `c₁`, `c₂`.
- Both read entries `< 318 = p1Start 0` only: `FrontLocal` by `Agree`.

### 4. Per-phase plan (positions from `fsStarts_eq`)

| k | Phase (positions) | Truth / doom `DF k` (U part) | `FrontObl` field | Existing lemma | Missing |
|---|---|---|---|---|---|
| 0 | seed (0) | `False` | — (no FS absorb/squeeze item obligation) | — | — |
| 1 | stmt (1, absorb) | `False` | `habs` trivial | — | — |
| 2 | cap₀ (2, absorb) | `far₀ ∨ ¬ Stmt` | `habs` trivial (from `False`) | `farL`, truths in `PIOP`, `Shift` | `Stmt`, its `Reads 3` |
| 3 | Z1 (3–12, 10 sq) | `msD (DF 2) (Bg ∨ ¬Z ∧ zc residual vanishes)` | `ms`, `hfin` (17/2^128) | `coords_round_le`, `seq_round_le`, `zerocheck_bad_le`? | Z unit: the node `targetS` table, the zerocheck residual |
| 4 | Z2 (13 abs, 14 sq λ) | `Wrong` at λ | `habs` (13), `hsingle` (14): `skip_pair_bad_le` 126 | `FRSkip.skip_pair_bad_le`, `z2Vals` | Z2 readers, truth `truthZ2` |
| 5 | Z3 (15–66, 26 rounds deg 3) | `D3` | `habs`/`hsingle` per round | `D3_single`, `z3_phase`, `z3_step`, `D3_first_absorb` | instantiation |
| 6 | Zend (67) | `â, b̂` wrong (`finZ`) | `habs` | `RejEnd` (Rows) pattern | `finZ` relation in log terms |
| 7 | L1 (68, α) | batched `Wrong` | `hsingle`: `batch_bad_le` 2 | `batch_single` | L readers |
| 8 | L2 (69–96, 14 rounds deg 2) | `D2` | `habs`/`hsingle` | `D2_single`, `D2_first_absorb` | tables `lin_trueSum_kinds` |
| 9 | L3 (97, 8 `v`) | `v_kind` wrong | `habs` | `lin_final_kinds` | — |
| 10 | L3β (98, β) | batched wrong | `hsingle`: `batch_pow_bad_le` 9 | `batch_single` | — |
| 11 | S1 (99–113, 15 sq) | `¬ ShHolds ∧ batched masked sum = target` | `ms`, `hfin` (26 + 9) | `shift_sound_node`, `shift_sum_masked`, `seq_round_le` | the `eqAtR`→`mle` bridge (INT-3 open 3) |
| 12 | S2 (114–169, 28 rounds deg 2) | `D2` | `habs`/`hsingle` | `D2_single` | `relSh` in log terms |
| 13 | Lr1 (170–177, 8 sq) | zerocheck `ZCw` | `ms`, `hfin` 15 | **`lr_zc_hfin`** | assembly only |
| 14 | Lr2 (178–207, 15 rounds deg 3) | `D3` (outer) | `habs`/`hsingle` | **`habs_outer`**, **`single_outer`**, `lr_outer_phase` | assembly |
| 15 | Lrend (208) | `EndBad` | `habs` | **`habs_end`**, `lr_rejEnd_ok` | assembly |
| 16 | Lr3 (209, κ_L) | `BatBad` | `hsingle` | **`lr_single_batch`** | assembly |
| 17 | E1 (210–220, 11 sq) | `ZCw` | `ms`, `hfin` 21 | `zc_hfin` | E instantiation (`lr_unit_pos` pattern) |
| 18 | E2 (221–262, 21 rounds deg 3) | `D3` | `habs`/`hsingle` | `habs_outer`, `single_outer`, `e2_phase` | E instantiation |
| 19 | Eend (263) | `EndBad` | `habs` | `habs_end` | E instantiation |
| 20 | E3 (264, κ_E, 6 claims) | `BatBad` | `hsingle` (5/2^128) | `single_batch` (3 claims) | **six-claim batching** (Lr's `v_L` with `κ_E³`) |
| 21 | E4 (265–310, 23 rounds deg 2) | `D4 = D2` | `habs`/`hsingle` | `habs_inner`, `single_inner` | `relE` (iv) final in log terms |
| 22 | E4end (311) | `α₄` pending | `habs` | `relE_e4end` | log form |
| 23 | RS0 (312, 8192 B) | `¬ truthRS0` | `habs` | `truthRS0` | the column check ⇒ slice wrong |
| 24 | RS1 (313–316, 4 sq) | batched switched claim true | `ms`, `hfin` (10/2^128) | `rs1_of_not_truthRS0`, `hfin_rs1`, `rs1_round_le` | assembly |
| 25 | B′ (317, κ′) | `v*` batched true | `hsingle` (10), `handoff` | `truthP1_zero`, `batch_single`, `cells_sum_of_pub` | handoff form |

`RejF`: the units' asserts (`RejEnd`, `RejIn`, …) and the absorbed-message zero checks, joined by
`rejOK_or`. `hstab`/`FrontChainStab`: `Reads.stab`/`Reads.chain` on every `Bg`/`U` term.

### 5. Order of work (this pass)

1. `W₀`, `c₀` and `loc` (new module `FRSoundnessFrW0`), with controls.
2. Then the phases in the table's order, as far as the pass reaches.

### 6. Log

- `FRSoundnessFrW0` (new): `zPtL`, `lcPtL`, `shPtL`, `ePtL`, `rsPtsL`, `rsCoL`, `rsRL`, `rsKL`, `kpL`,
  `bitsL`, `wrsL`, `sliceL`, `rsTvL`, `vRSL`, `vkL`, `stL`, `pubHL`, `vStarL`, **`W₀L`**, **`c₀L`**;
  reader congruences at `Agree 317` (`rsPtsL_congr`, `wrsL_congr`, `vRSL_congr`, `pubHL_congr`)
  and `318` (`vStarL_congr`); **`frontLocal_W0`** (`FrontObl.loc`). Controls: `frW0_starts`,
  `rsPtsL_node`/`rsPtsL_leaf`, `vRSL_zero`, `c₀L_leaf`, `vStarL_node_ne`, `W₀L_off`. Green.
  - Lesson: `congr 1` on `List.ofFn pinnedRho ++ _` whnf-loops (the constant); use `congrArg`.
- `FRSoundnessFrB` (new): `pubL`, `PubOK`, `fipL`, **`DRS1`** (RS1's doom at its end), **`DB`**
  (B′'s doom), `nrP_zero` (`nrP 0 κ = κ.m − 7`), `cells_lt`, `pubHL_eq`, `ip_W0`
  (`⟨W₀, f⁽⁰⁾⟩ = ι(fip + Σ κ′^(k+2) f[cell_k])`), `batch_count`, `bTerms`, **`single_B`**
  (`hsingle` at 317: `≤ 10·2^128`), **`handoff_B`** (`FrontObl.handoff`). Green.
  - Lessons: (1) `card ≤ 10 * 2 ^ 128` against a lemma's `k * 2 ^ 128` with `k` not yet assigned
    makes the unifier evaluate the literal (max recursion): pass `(k := 10)`. (2) A Classical
    `filter` instance against `instDecidableAnd` also recursed: `batch_count` takes
    `[DecidablePred P]` and re-proves `single_F_le`'s two steps.
- **Design finding (RS0, for the next pass).** The RS claims `α_j` have no message of their own:
  `finRS` *computes* them from RS0's slices (`rsAlpha`), and the other finals assert them against
  the sub-protocols' claimed values (`finZ`: `P^z*(λ)`; `finLc`; `finSh` (ii); `finE` (v) `α₄`).
  So the pending claims before RS0 are the sub-protocols' *claimed* values (`P^z*(λ)`, `c_Sh`,
  …) being false, `RejF` from position 313 on contains the finals' slice equations
  (`rsAlpha_j(slices) = claimed_j`), and RS0's `habs` is `rs_column` + `ml_claim_split`.
- `FRSoundnessFrRS` (new): `gL`, `sL`, **`DRS0`**, `fsL`, `vRSL_eq`, `wrsL_eq`, `fipL_eq`,
  **`hfin_RS1`**. Green. `rsPtsL_congr`/`gL_congr` lowered to `Agree 311` (E4's last challenge
  is at 310) so that RS1 can use `Agree 313`. Lesson: `tauto` and `set X := ext …` both hit
  whnf timeouts here; explicit terms and `generalize` work.
- Axioms (45 theorems) and the source rule (152 files, 0 findings) clean; sequential profiles
  7–8 s per module. `ip_W0`'s two `congr 1` (9.5 s) replaced by `congrArg`.
- **Stopped here (context).** `S-G5-RESULT.md` §5 is the handover, in order: RS0 + `RejRS`, E,
  Lr, S, L, Z, the assembly, `hW0`, `hStart`, `hFront`, `kstate_front`.
