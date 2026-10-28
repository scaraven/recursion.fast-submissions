# S-G5 RESULT (pass 1): the front's `W₀`, `c₀`; B′, the handoff and RS1 proved; handover

Base HEAD `f1c0390`. Build tree `logs/fr-build-SG5` (copied from `fr-build-SG4`; `snap.sh` takes
HEAD's sources and symlinks `FRSoundnessFr*` to the worktree; the glob also matches
`FRSoundnessFront`, which is unchanged). Logs in `logs/S-G5/`. Journal: `S-G5-JOURNAL.md` (the
per-phase plan table is its §4). Every lean/lake command ran in the 16G scope with a `timeout`.
Nothing is committed.

**Status.** This is a multi-pass stage. Pass 1 delivers items 1 (concrete `W₀`, `c₀`; `RejF` and
`DF` are designed but not yet assembled) and three of the 26 phases' obligations (B′'s `hsingle`,
the B′ → P1.0 `handoff`, RS1's `hfin`), plus `FrontObl.loc`. §5 is the handover, in order.

`lake build FRSoundnessFrRS` is green (2,303 jobs; it builds all three new modules). No `sorry`.

- **Axioms** (`logs/S-G5/axioms.log`, all 45 theorems of the three modules): `propext`,
  `Classical.choice`, `Quot.sound` only (31 use all three; the others fewer).
- **Source rule** (`logs/S-G5/source-rule.log`): 152 files, 0 findings.

## 1. What was built (code lines from `scripts/loc.py`, `logs/S-G5/loc.log`)

| Module | Total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrW0` | 248 / 137 / 19 | The readers of the claim points (`zPtL`, `lcPtL`, `shPtL`, `ePtL`, `rsPtsL`, mirroring `zSrc`, `lcSrc`, `shSrc`, `eSrc`, `rsPtIx`), RS1's `r″`, `κ` (`rsRL`, `rsKL`), B′'s `κ′` (`kpL`), the RS weight table **`wrsL`** (`y ↦ Σ_j κ^j Φ_{r″}(eq(p_j, y))`), RS0's slices (`sliceL`), **`vRSL`** (`rsV`), the public values (`vkL`, `stL`, `pubHL` = `pubH`), **`vStarL`** (`vStar`); **`W₀L := ι ∘ w0F wrsL (cellsOf κ) κ′`**, **`c₀L := ι v*`**; reader congruences; **`frontLocal_W0 : FrontLocal W₀L c₀L`** (`FrontObl.loc`) |
| `FRSoundnessFrB` | 237 / 170 / 14 | `pubL`, **`PubOK`** (`Node.PubCells` on `f⁽⁰⁾` and the log's `vk`, `c₁`, `c₂`), **`fipL`** (`⟨W_rs, f⁽⁰⁾⟩`), **`DRS1`** (RS1's doom at its end), **`DB`** (B′'s doom), `nrP_zero`, `cells_lt`, `pubHL_eq`, **`ip_W0`** (`⟨W₀, f⁽⁰⁾⟩ = ι(fip + Σ_k κ′^(k+2) f[cell_k])`), `batch_count`, `bTerms`, **`single_B`**, **`handoff_B`** |
| `FRSoundnessFrRS` | 161 / 109 / 12 | `gL`, `sL` (four claims; a leaf's fourth is `0`), **`DRS0`** (RS0's doom at its absorb), **`vRSL_eq`** (`v_RS = Σ_j κ^j rsT_j`), **`wrsL_eq`**, **`fipL_eq`** (`⟨W_rs, f⁽⁰⁾⟩ = Σ_j κ^j rsTruth_j`, by `pack_unpack`), **`hfin_RS1`** |
| **Total** | 646 / 416 / 45 | |

### The statements

```lean
-- FrontObl.loc
theorem frontLocal_W0 : FrontLocal W₀L c₀L
-- FrontObl.hsingle at B′'s squeeze (position 317; DF 24 there is msD … DRS1 312 4 = DRS1)
theorem single_B (L es : Log) (hl : es.length = 317) :
    (univ.filter fun a => DRS1 L es ∧ ¬ DB L (ext1 es a)).card ≤ 10 * 2 ^ 128
-- FrontObl.handoff
theorem handoff_B {L es : Log} (x : ByteArray × Digest) (hl : es.length = 318) (hd : DB L es) :
    D1 W₀L c₀L 0 L (es ++ [x])
-- FrontObl.hfin at RS1's range (312, 4)
theorem hfin_RS1 {Dk : ℕ → Log → Log → Prop} (hmem : (312, 4) ∈ fsRanges)
    (hprev : Dk (phOf 312) = DRS0) (hfin : Dk (phOf 313) = msD (Dk (phOf 312)) DRS1 312 4)
    (L es₀ : Log) (hl : es₀.length = 313) : condCount (DPos (Dp Dk)) L es₀ 4 [] ≤ deltaR
```

- `single_B`'s count is §5.2's B′ row: the batch `Σ_{i<11} κ′^i v_i` of `(v_RS, 0, pub_0 … pub_8)`
  against `(⟨W_rs, f⟩, 0, f[cell_0] … f[cell_8])` (`batch_pow_bad_le` at degree 10). A far word
  never escapes (`farL` reads before 317).
- `hfin_RS1` is §5.2's RS1 row, `(7 + J_z − 1) = 10`: `rs1_of_not_truthRS0` at `J' = 3`. A leaf
  runs the same four-claim batch with a zero fourth claim (`gL`, `sL`), so one statement covers
  both kinds.
- `handoff_B`: `DB` is `D1 0`'s form at no answered round (`hRnd = 0`, `closeP_zero`, `ans3 = 0`);
  the proof is locality (`lvT_same`, `frontLocal_W0`).

## 2. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`), logs `logs/S-G5/time-<module>.log`:

| Module | Wall (≈ 3.8 s import) | Type checking | Max RSS |
|---|---|---|---|
| `FRSoundnessFrW0` | 7.6 s | 227 ms | 2.75 GB |
| `FRSoundnessFrB` | 8.2 s | 171 ms | 2.76 GB |
| `FRSoundnessFrRS` | 7.4 s | 107 ms | 2.75 GB |

No `decide` over a program, table or item list. The only `decide`s: `frW0_starts` (nine phase
starts, against `fsStarts_eq`), `nrP_zero`, `Kind.m_le`, `cells_lt`'s `oneCell` bound (one
inequality). Two `congr 1` in `ip_W0` cost 9.5 s and were replaced by `congrArg`.

## 3. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `rsPtsL` (and the point readers) | `rsPtsL_node`: a node takes 4 points of 23 coordinates | `rsPtsL_leaf`: an `L32` leaf takes 3 points of 25 |
| reader positions | `frW0_starts`: the literals are the phases' starts (`fsStarts_eq`) | — |
| `vRSL` | `vRSL_zero`: zero slices give `v_RS = 0` | (`DRS1_of_ne` below uses a wrong one) |
| `c₀L`, `vStarL` | `c₀L_leaf`: a leaf's claim is `ι v_RS` | `vStarL_node_ne`: a node with `κ′ = 1` and zero digests has `v* = v_RS + 1` |
| `W₀L` | `W₀L_off`: off the cells it is the RS weight | (`ip_W0` is the cells' part) |
| `DB` | `DB_of_far` | `not_DB_true`: close word and true claim |
| `DRS1` | `DRS1_of_ne` | — |
| `PubOK` | — | `pubOK_leaf`: a leaf never fails it |
| `gL`, `DRS0` | `truthRS0_gL_true`: the true slices satisfy RS0's truth | `gL_leaf_three`: a leaf's fourth claim has no weight |

## 4. Deviations and decisions

1. **The design of `DF`** (journal §2): `DF k = Bg_k ∨ U_k` with `far₀` in every `Bg_k` from
   phase 2 on. **`DF 2 := far₀ ∨ ¬ Stmt`**, where `Stmt κ` is every statement part on the decoded
   `f⁽⁰⁾` (Z, S, Lr, E, and `PubOK`). This makes `hExt` need only the prefix of length 3: `¬ DC`
   there is `¬ far₀ ∧ Stmt`, carried to the chain by `Reads 3`. The later dooms serve the counts.
   `PubOK` stays a background term until B′ (it is in `DRS0`, `DRS1`).
2. **`W₀L`, `c₀L` ignore `L`** (they read only chain entries). They are written in the registers'
   own form (`w0F`, `vStar`, `rsV`, `pubH`) so that `hW0`/`hStart` become register-to-reader
   rewrites plus `weight_mle`.
3. **The RS claims have no message of their own** (finding, journal). `finRS` computes `α_j` from
   RS0's slices (`rsAlpha`). The other finals assert them against the sub-protocols' claimed
   values. So RS0's doom (`DRS0`) is reached from the sub-protocols' *claimed* values being false,
   and `RejF` from position 313 on must contain the finals' slice equations. RS0's `habs` is then
   `rs_column` + `ml_claim_split` (§5, step 1).

## 5. Handover: what is left, in order

Positions (`fsStarts_eq`): Z1 3–12, Z2 13–14, Z3 15–66, Zend 67, L1 68, L2 69–96, L3 97, L3β 98,
S1 99–113, S2 114–169, Lr1 170–177, Lr2 178–207, Lrend 208, Lr3 209, E1 210–220, E2 221–262,
Eend 263, E3 264, E4 265–310, E4end 311, RS0 312, RS1 313–316, B′ 317, P1.0 318.

1. **RS0 (phase 23) and `RejF`'s slice part.** `DF 22` (E4 end) = `far₀ ∨ ¬PubOK ∨` some pending
   claimed value false: `P^z*(λ)` (Z2's message), `α_Lc` (`finLc`), `c_Sh` against
   `(w_out + w_in)·ẑ_Sh` (`finSh` (ii)), `α₄` (`relE_e4end`, E4 end's message). `RejRS` (positions
   ≥ 313): `rsAlpha_j(slices) ≠` the claimed value (the form `finZ`/`finLc`/`finSh`/`finE` assert;
   read their relations off `FRVIRFinals`/`FRVIRFinalsSF`). `habs` at 312: `rs_column` with the
   inner weights `rsW` (`eqZ λ ρ₁`, `eq` at the low 7 coordinates, `bb`) and `ml_claim_split`
   (the claim's truth is the `rsW`-weighted sum of the true slices `Σ_u g_j(u) Q_i(u)`), giving
   `¬ truthRS0 … (gL) (sL)`, i.e. `DRS0`. Check that `gL`'s outer points are exactly the high
   23 coordinates `ml_claim_split` leaves (`zPtL` etc. mirror `zSrc`, so they should be).
2. **E (phases 17–22)**: instantiate the Rows unit as `lr_unit_pos` does (`s0 = 209`, `b2 = 221`,
   `a = 21`, end absorb 263, `κ_E` at 264, inner rounds from 265, `nc = 23`; precondition
   `209 + 1 + 11 = 221`). E3's batching has **six** claims (`â_M, b̂_M, ĉ_M` and `κ_E³·(Lr's
   three)`): `single_batch` is for three; use `batch_count` (FrB) at `k = 5`. E4's final:
   `relE` (iv). E4 end: `relE_e4end`.
3. **Lr (phases 13–16)**: assembly only (`lr_zc_hfin`, `habs_outer`, `single_outer`,
   `habs_end`, `lr_single_batch`). Lr's lincheck claim `v_L` becomes a pending claim batched into
   E3.
4. **S (11–12)**: `truthS1N`/`shift_sound_node`; the bridge `shiftMaskS`/`linkWAllS` (`eqAtR`)
   → `mle`/`shWM` (INT-3 open item 3). S1's `hfin` by `hfin_seq` (`26 + 9`).
5. **L (7–10)**: `lin_trueSum_kinds`, `lin_final_kinds`; L1 `batch_count` at `k = 1`, L3β at
   `k = 8`; L2 `D2_single`.
6. **Z (3–6)**: the Z unit (zerocheck over the node `targetS`, `skip_pair_bad_le` at Z2,
   `D3_single`/`z3_phase` at Z3, `finZ` at Zend).
7. **Assembly**: `Stmt`; the concrete `DF k` (a 26-way definition by `k`) and `RejF` (`rejOK_or`
   of the units' asserts and `RejRS`); `FrontObl`'s fields by a position classification of
   `0 … 317` (one checked list, as `tailCls_check`); `FrontChainStab` from `Reads.chain`. For B′:
   `hsingle` at 317 is `single_B` after `msD`'s `ite_neg` (317 > 312 + 4), and `handoff` is
   `handoff_B`.
8. **`hW0`**: `w0V impl κ fi r' = wHatL W₀L L es 0`. Needs `impl.rsWeight = rsWeightS`
   (`implC_meets`) and the register views of S-G4 (`coords_view` for RS1/Z1, `rounds_view` for
   L2/S2/Z3/E4, `p1_facts` for `P₀`). Algebra: `rsWeightS` = `mleN` of `ι ∘ wrsL` by
   `weight_mle` (and `Phi` commuting with `algebraMap F K`), the cells by `eqCellK_eq` and
   `mleN_w0F`.
9. **`hStart`**: `relB` (from `accept_fields`, as S-G4 did for `finP`), `exec_finRS`'s `rsV`
   (register reads → `vRSL`; `impl.phiRS = phiRSS` from `implC_meets`), `pubH` with `inp.vk` =
   `vkL` (the seed query) and `π`'s statement bytes = `stL` (the absorb message).
10. **`hFront`**: `¬ RejF` from the accepted run's final flags (the same views).
11. **`kstate_front`**: `kstate_of_front` with `FrontObl` and `finalLaw_of_run`/`hAcc_of_fin`
    with `hFront`, `hStart`, `hW0`, leaving `hExt` and the `implC` facts.

## 6. Open questions

1. `FR.lean`'s owner: add `import FRSoundnessFrRS` (it imports the other two).
2. Is `DF 2 := far₀ ∨ ¬ Stmt` the interface S-H2l/S-E want for `hExt`? Then `hExt`'s
   obligation is `¬ far₀ ∧ Stmt ∧ LigeritoOut ⇒ witness`, and `Stmt` should be agreed with
   them (proposal: `truthZN`/`truthZ`, `truthS1N`, `truthLr`, `truthE`, `PubOK`).
