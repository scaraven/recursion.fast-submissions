# S-G2 RESULT: `ligerito_final`

Base: worktree `v4/flock-recursive` at HEAD `c6b0d47`. HEAD moved to `0e93332` during the stage
(blueprint 3.14 (D), S-E7). Neither commit touches the Ligerito tail or A.9's `finP`/`finPf`. The
build and checks below ran on a snapshot of `0e93332`'s modules with S-G2's modules symlinked in
(`logs/fr-build-SG2/snap.sh`). The worktree's `FRVIR.lean` is being edited by another agent and
did not build at the time.

**Status.**
- `ligerito_final` is stated and proved. So is its form from the walk
  (`ligerito_final_of_walk`), which takes exactly what `FinalLaw` will have.
- No sorry; axioms are `propext`, `Classical.choice`, `Quot.sound` only. Source rule: 123 files,
  0 findings.
- **One finding blocks `FinalLaw` (not `ligerito_final`).** The tail's level-4 doom does not
  match A.9's `finP 4`/`finPf` (§5). `ligerito_final` does not read P3.4's or Pf's doom, so it
  holds either way. But `FinalLaw`'s step "accepted ⇒ the composed doom is false at the chain's
  end" cannot be proved against the current `RejT`/`DPf`.

## 1. What was built (code lines from the core's `scripts/loc.py`)

| File | Total / code / theorems | Content |
|---|---|---|
| `FRSoundnessLigFinal.lean` (new) | 493 / 337 / 36 | Part A: positions (`lig_pos_check`) and prefix reads (`same_take`); **`p1_of_not_D1`**, **`c_of_not_DCi`**, **`p2_of_not_DP2`** (each reads one tail doom at one position). Part B: **`LigeritoOut`**, **`ligerito_final`**, `LigeritoOut.claim0`, **`LigeritoOut.level0_committed`**. Part C: `not_DT_of_not_DC`, **`not_D_prefix`**, **`ligerito_final_of_walk`**. Part D: `bindL_ofFn_mle`, `pfPt`, `trueSum_tPf_end`, **`DPf_end_iff`**, `mleP`, `mleP_zero`, **`mleP_lvW_succ`**, `mleP_pt_split`, **`mleP_pad`**. Part E: **`colOf_of_path`**, **`foldAt_of_cols`**. Part F: `lvC_five_eq`, **`pf_round0_conflict`**. Part G: the controls and their helpers (`readK_nil`, `decodeL_nil`, `msgOf_nil`, …) |
| `FRSoundnessLigerito.lean` | 27 / 9 / 1 | The docstring now points to `FRSoundnessLigFinal`; no code change |

`ligerito_final` cannot live in `FRSoundnessLigerito`. `FRSoundnessHide` imports that module for
`eqBits_eq_eq`, and the tail's dooms import `FRSoundnessHide`, so the import would be circular.

**Requested from the owner of `FR.lean`:** add `import FRSoundnessLigFinal`. It is not on `FR`'s
import path yet.

### The statement

```lean
structure LigeritoOut (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (L es : Log) : Prop where
  close  : ∀ i < 5, ¬ farL (kindOf es) L es i
  claim  : ∀ i < 5, lvC c₀ i L es =
    ∑ y ∈ range (2 ^ nrP i (kindOf es)), lvW W₀ i L es y * fTab (kindOf es) L es i y
  folded : ∀ i < 5, c1 c₀ i L es = foldSum W₀ i L es
  near   : ∀ i < 5, truthP2 (kindOf es) L es i
  fold   : ∀ i < 5, truthC (kindOf es) L es i
  cons   : ∀ i < 5, truthP3 (kindOf es) L es i
  agree  : ∀ i < 5, consSet (kindOf es) L es i =
    jointAgree (wordK (kindOf es) L es i) (decodeL (kindOf es) L es i)

theorem ligerito_final (hF : FrontLocal W₀ c₀) {L es : Log} (hlen : p3S0 4 < es.length)
    (hD : ∀ p, p1Start 0 ≤ p → p < es.length → ¬ DT W₀ c₀ (phOf p) L (es.take (p + 1)))
    (hH : DH L es) : LigeritoOut W₀ c₀ L es
```

What `LigeritoOut` says, level by level, for `i < 5`:
- `close`: the word read under its cap is `eᵢ`-close (`¬ far_i`).
- `fold`: the next level's message is the fold of level `i`'s decoded messages. At level 4 the
  next message is the final message. This is the per-level consistency across folds.
- `near`, `cons`: the codeword agreement (P2) and the query consistency (P3).
- `agree`: `A_c = jointAgree`. This is the hypothesis S-H2's `level_decode` takes.
- `claim`: P1.i's initial claim is `⟨Wᵢ, f⁽ⁱ⁾⟩`.

Level 0 is where the handoff to the PIOP front happens:
- **`claim0`**: `c₀ L es = Σ_y W₀ L es y · ι(fF κ L es y)`. The claim RS/B′ hand P1.0 is the
  inner product of their weight with the decoded, F-valued level-0 message.
- **`level0_committed`**: every prefix `es.take p` with `p > capPos 0` reads the same close word,
  the same `msgOf … 0` and the same `fF`. The front's truths, which are evaluated on prefixes,
  therefore talk about the same `f⁽⁰⁾`.

`ligerito_final` is parametric in `W₀` and `c₀`, which carry the claims and points from RS/B′.
It reads neither E nor the node relation.

**How it is proved.** The "induction from Pf upwards" is S-G's generic `walk_back`. Given `¬ DT`
on every prefix, each level `i` reads three dooms, at three positions:
- `D1 i` at P1.i's first absorb (`hRnd = 0`, so `closeP 0 ↔ ¬ farL` and `ans3 = 0`). This gives
  `close` and `claim`.
- `DCi i` at C.i. This gives `near` and `folded`.
- `DP2 i` at P2.i's last answer (`msD`'s `fin`). This gives `cons`.

The remaining facts come from existing lemmas:
- `truthC_of` (unique decoding) gives `fold`.
- `consSet_eq_of_DH` gives `agree`.
- The `_same` lemmas carry each prefix's reads to the whole chain.

P3.i and Pf are never read.

## 2. The hypotheses `ligerito_final` leaves for `FinalLaw`

`ligerito_final_of_walk` is the form `FinalLaw` calls:

```lean
theorem ligerito_final_of_walk (hF : FrontLocal W₀ c₀)
    (hS : ChainStab (DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀))))
    (hb : ¬ Bad L) (hE : ¬ EscG (DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀))) L)
    (hEH : ¬ EscG DH L) (hci : IsChain L j)
    (hlen : p3S0 4 < (entriesOf L (pathOf L j)).length)
    (hend : ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L (entriesOf L (pathOf L j))) :
    LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j))
```

Where each hypothesis comes from in `FinalLaw`:

1. **`hb`, `hE`, `hEH`**: `muT_lt_one` from `muT Rej Dk L < 1`. Done.
2. **`hS`**: `chainStab_of hF hFS`. It needs the front's `FrontChainStab RejF DF` (owner: S-G,
   the front).
3. **`hF : FrontLocal W₀ c₀`**: the front's. `W₀` and `c₀` read only what lies before P1.0.
4. **`hci`, `hlen`**: `runLog_chain` (not built). An accepted run's FS items form a chain of all
   468 entries.
5. **`hend`**: the composed doom is false at the chain's end (position 467, phase 51). It has three
   parts:
   - **`¬ RejF`**: the front's asserts pass (front, waiting on 3.14).
   - **`¬ RejT c₀`**: every P1.i and Pf round check holds against the tail's claims `lvC`. For
     `i ≥ 1`, `lvC i` is `vNext` of `foldAtN`, the log-read column folds. The verifier's claims
     use the opened columns. **`foldAt_of_cols`** (from `cap_binding`, given `¬ Collision` ⊂
     `¬ Bad`) makes the two equal when each opened column's path evaluates to its cap entry. For
     P1.0, `c₀` must be the verifier's `v*` (the front's). **Pf's round 0 is blocked: §5.**
   - **`¬ DPf`**: by **`DPf_end_iff`**, `DPf` at the end ⇔ `c_{Pf} ≠ W̃_f(ρ)·final̂(ρ)` in the
     tables' extensions at Pf's challenges (`pfPt`). `FinalLaw` matches this with `finPf`'s
     `relPf` (`wV·padV·finHat`) in three steps:
     - (a) `final̂`: `finHat` is `mleN 7 (finalAt es) (pfPt es)` (the `eqTableK` spec).
     - (b) Levels 1–4: `lvsV [1,2,3,4]` is the four applications of **`mleP_lvW_succ`**, which
       is `lvStepV`'s formula at the spec: `û(P₀)·(Wᵢ(sᵢ, P[1..]) + Σ_q eq(κ_c, q)·tensorW(p_q,
       P[1..]))`. The P30 padding is **`mleP_pad`**, and level 4's fold is `mleN_foldW`.
     - (c) Level 0: `w0V` is `mleP (nrP 0) W₀ P₀`. This is the RS weight's extension
       (`weight_mle`, S-C) plus `mleN_w0F`: the front's, parametric here.
     Step (b) is blocked at level 4 by §5: `wPf` contains level 4's tensor weights and `wV` does
     not.
6. **`DH`** is supplied inside `ligerito_final_of_walk` by `DH_of_noEsc`.

After `LigeritoOut`, `FinalLaw` uses:
- `close` and `agree` for the extractor (S-H2 `level_decode`, the `'N'` case of
  `ext_good_tape`);
- `claim0` and `level0_committed` for the front's truths (B′ → RS → E/L/S/Z) on `f⁽⁰⁾`;
- then `leaf_sound`/`node_sound`.

## 3. Build and kernel times

- Build: `lake build FRSoundnessLigerito FRSoundnessLigFinal` in `logs/fr-build-SG2` is green
  (2,278 jobs). Logs: `logs/S-G2/build0.log` (warm-up) and `build1.log`. `build1.log` records
  the snapshot tree's first run, which stopped on an error later fixed; the rerun was green with
  no warnings in S-G2's modules.
- Sequential profile (`taskset -c 0 lake env lean -DElab.async=false --profile`):

| Module | Wall (incl. ≈ 3.5 s import) | Type checking (items over 100 ms) | Max RSS | Log |
|---|---|---|---|---|
| `FRSoundnessLigFinal` | 11.7 s | 1.27 s (`lig_pos_check`, a `decide` over `fsStarts`), 1.25 s (`pf_round0_conflict`), 0.15 s | 2.90 GB | `logs/S-G2/profile-FRSoundnessLigFinal.log`, `time-…` |
| `FRSoundnessLigerito` | 5.9 s | none over 100 ms | 2.62 GB | `logs/S-G2/profile-FRSoundnessLigerito.log` |

  The two declarations were named with `-Dtrace.profiler=true` (elaboration 1.29 s each).
  `decide` runs only on `fsStarts` positions (`lig_pos_check`) and on one 32-byte `K.ofBytes`
  (`K_ofBytes_zero`, 167 ms). No `decide` runs over a table, a layout or a program.
- Axioms: `logs/S-G2/axioms.log`, 26 declarations. All use `propext`, `Classical.choice`,
  `Quot.sound`. `K_ofBytes_zero` uses `propext` and `Quot.sound`; `lig_pos_check` uses only
  `propext`.
- Source rule: `python3 -I .contract/scripts/source-rule.py submissions/flock-recursive` reports
  123 files, 0 findings.

## 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `ligeritoOut_nil` | positive | `LigeritoOut` holds on the empty chain of the empty log with `W₀ = 0`, `c₀ = 0`. Every word decodes to the zero codeword (`decodeL_nil`, via `rs_eq_of_agree`), every message and claim is `0` (`msgOf_nil`, `lvC_nil`, `c1_nil`), `A_c = univ = jointAgree`. The bundle is satisfiable. |
| `not_ligeritoOut_one` | negative | The same chain with `c₀ = 1` fails `LigeritoOut`: level 0's claim gives `1 ≠ ⟨0, f⁽⁰⁾⟩ = 0`. A one-parameter substitution flips it, so the `claim` field is not vacuous. |
| `mleP_zero` | value | `mleP 0 W ρ = W 0` |
| `DPf_end_iff`, `trueSum_tPf_end` | iff / equality | Pf's end doom is exactly the final check in extensions, not an approximation |
| `pf_round0_conflict` | finding | §5 |

**Not built: a concrete instance of `ligerito_final`'s hypotheses `hD`/`hH`.** It would need
`¬ DT` at every tail position of a concrete 468-entry chain. These hypotheses are the output of
`walk_back`/`DH_of_noEsc` (`ligerito_final_of_walk`), so their satisfiability is `FinalLaw`'s
`hend`. That is exactly what §5 blocks.

## 5. Finding: the tail batches level 4, the verifier does not (blocks `FinalLaw`)

**The tail (S-G1i, `FRSoundnessTailD`)** treats level 4 like levels 0–3:
- Pf's initial claim is `lvC 5 = vNext 4 (c1 4) = c1 4 + Σ_q eq(κ_c⁽⁴⁾, bits₉(q))·y_q`, which
  `lvC_five_eq` states, `rfl`.
- Pf's weight `wPf` is `wNext 4 (wFold 4 …)`, which includes level 4's tensor weights.
- `RejT`'s Pf round-0 check is `g(0) + g(1) = lvC 5`.

**The verifier (A.9; `FRVIRFinalsSG`)** does not batch level 4:
- `finP 4` checks each `y_q = Enc₄(final)[p_q]` directly and asserts
  `claim0 Pf = claimN P1.4 = c1 4`.
- Pf's first claim is `free` (`initClaim`, the first message's `c₁ + c₂`), so the verifier's
  round-0 check is `g(0) + g(1) = c1 4`.
- `finPf`'s weight is `lvsV [1,2,3,4] w0V`, which carries only levels 0–3's tensor weights:
  `lvOps k` uses `kcOf (k−1)` and `ysOf (k−1)`.
- P3.4's five squeezes (`κ_c⁽⁴⁾`) are in the transcript, but the verifier never reads them.

**Consequence (`pf_round0_conflict`, kernel-checked).** `¬ RejT` together with the verifier's
round-0 equation forces `Σ_q eq(κ_c⁽⁴⁾, q)·foldAtN 4 (p_q) = 0`. For the honest prover this is
false in general. An accepted run therefore generally has `RejT` true, so the composed doom holds
at the end and `walk_back` gives nothing. Likewise `¬ DPf` at the end is not the verifier's final
check (`wPf` ≠ the weight `wV` evaluates). `FinalLaw` cannot be proved against the current
`DkC`/`RejC`.

**Proposed fix (S-G's tail modules; not edited here, since they are not S-G2's).** Make the tail
match the verifier at level 4:
1. `lvC 5 := c1 4`, and `wPf` := `wFold 4` zero-padded (no `wNext`).
2. P3.4's doom := `msD (DP2 4) (finP2 4) (p3S0 4) 5`, so that nothing escapes on the unused
   `κ_c⁽⁴⁾`. `hfin` is then `0`: P2.4's final doom reads no P3.4 answer.
3. Pf's doom := `¬ truthP3 4 ∨ D2 …` with the new `lvC 5`/`wPf`. The background `¬ truthP3 4` is
   fixed after P2.4 and never escapes. At the end it contradicts `finP 4`'s direct checks, via
   `foldAt_of_cols`.
4. `habs_Pf_first` then goes through `truthC 4` (`foldSum 4 = ⟨wFold 4, final⟩`).

`ligerito_final` is unaffected. It reads `D1`, `DCi` and `DP2` only, and these do not change. The
alternative, adding level 4's batching to `finP 4`/`finPf`, costs verifier ops and duplicates the
direct check, so the tail is the side to change.

## 6. Deviations

1. **New module `FRSoundnessLigFinal`** instead of `FRSoundnessLigerito`, because of the import
   cycle (§1). `FR.lean` must import it.
2. **`ligerito_final` takes `¬ DT` per prefix, not "no escape".** The induction is S-G's generic
   `walk_back`; `ligerito_final_of_walk` packages it with `ChainStab`. This keeps
   `ligerito_final` free of the front's `RejF`/`DF`, which wait on 3.14.
3. **Positions read: P1.i's first absorb, C.i, P2.i's last answer.** `close (i+1)` comes from
   `D1 (i+1)`, not from `finP3 i`. This avoids P3.4/Pf (§5). The hypothesis needs only
   `p3S0 4 < |es|`, not the full chain.
4. **The weight chain stops at `mleP_lvW_succ`/`mleP_pad`.** Matching it to `finPf`'s registers
   (`lvsV`, `w0V`, `padV`, `finHat`) is `FinalLaw`'s run-semantics work, and level 4's part waits
   on §5's fix.

## 7. Open questions

1. **§5:** should the tail change (proposed), or the verifier? The answer decides whether
   `FinalLaw` is provable.
2. Who adds `import FRSoundnessLigFinal` to `FR.lean`?
3. `FinalLaw` still needs `runLog_chain`. It also needs the register-to-log bridge for `finP i`
   (opened columns ↦ `foldAt_of_cols`) and for `finPf` (`lvsV ↦ mleP_lvW_succ`,
   `finHat ↦ mleN 7 finalAt`). These are S-G's `final` items, after 3.14.

---

# Pass 2: the level-4 tail fix, `FinalLaw`'s `hend`, and `FinalLaw` reduced to named obligations

Base HEAD `8b0439e`. The orchestrator ruled on §5: the tail changes to match the verifier, and
the verifier is unchanged. Built on a snapshot of HEAD (`logs/fr-build-SG2/snap.sh`) with S-G2's
modules symlinked in, because the worktree's `FRVIR*` files are being edited by S-E8.
`lake build FRSoundnessLigFinal FRSoundnessFront FRSoundnessRows` is green (2,301 jobs; this
covers every module that imports the tail). No sorry. Axioms: `logs/S-G2/axioms-pass2.log`, 32
declarations, all `propext`, `Classical.choice`, `Quot.sound`; `pfP_eq` and `ptL_four_lt` use only
`propext` and `Quot.sound`. Source rule: 124 files, 0 findings.

## P2.1 The tail fix (`FRSoundnessTailD`, `TailO`, `TailM`)

Four definitions change, as ruled. The `κ_c⁽⁴⁾` items stay in the transcript, so no position
moves.

| Definition | Before | After |
|---|---|---|
| `lvC (i+1)` | `vNext i (c1 i)` | `vNext i (c1 i)` for `i < 4`; **`c1 4`** for `i = 4` (`lvC_succ`, `lvC_five`) |
| `wPf` | `wNext 4 (wFold 4)`, zero-padded | **`wFold 4`**, zero-padded |
| `finP3 i` | `(i < 4 ∧ far_{i+1}) ∨ lvC (i+1) ≠ nxSum i` | the same for `i < 4`; **`finP2 4`** for `i = 4`, so `DP3 4 = msD (DP2 4) (finP2 4) …` |
| `DPf` | `D2 …` | **`¬ truthP3 κ L es 4 ∨ D2 …`**, with the new `lvC 5` and `wPf` |

Re-proved with their statements kept: `chain_same`, `tPf_same`, `habs_P1_next`, `habs_Pf`,
`habs_Pf_first` (P3.4 → Pf now goes through `truthC 4` and `sum_wPf`), `single_Pf` (the level-4
background never escapes; the count of 2 now comes from `single_Pf_D2`), `hfin_P3`, `finP3_stab`
and `DPf_stab`. `FRSoundnessCompose` (`phaseObl_of`, `kstate_of_front`, `chainStab_of`,
`rejT_same`) needed no edit.

One statement changed: **`nxSum_eq` now takes `i < 4`.** Its `i = 4` case described the old `wPf`
and is false for the new one. Pf's sum is now `sum_wPf`.

New lemmas: `lvC_succ`, `lvC_five`, `sum_wPf`, `single_Pf_D2`. `mLog4_le` moved from `TailM` to
`TailD`.

**Error rows (for §5.2's table; the error only goes down):**
- **P3.4: `9/2^128` → 0.** `hfin_P3` at `i = 4` is `condCount_eq_zero`: the final doom
  `finP2 4` reads no P3.4 answer, so no `κ_c⁽⁴⁾` escapes.
- P3.0 to P3.3: `9/2^128` each, unchanged.
- **Pf: unchanged.** At most 2 escapes per round (`2/2^256`). The background `¬ truthP3 4` is
  fixed after P2.4 and never undooms.
- P1.4 and P2.4: unchanged.
- The maximum (P2.0, `2^-120.36`) and `phaseObl_of`'s `N = 239·2^128` are unchanged.

`pf_round0_conflict` is removed. In its place, the control **`pf_round0_agree`** shows that
`RejT`'s check of Pf's round 0 is now exactly the verifier's: `g(0) + g(1) = c1 4`, which is
`claim0 Pf = claimN P1.4` with `initClaim "Pf" = free`.

## P2.2 `hend` for Pf and level 4 (`FRSoundnessLigFinal`, Part F)

- **`truthP3_four_of_cols`**: `finP 4`'s direct checks give `truthP3 4`. For each query, the
  opened column's path evaluates to its cap entry, and its fold equals `Enc₄(final)[p_q]`. The
  proof goes through `foldAt_of_cols`, and `nextMsg 4 = finalAt`.
- **`DPf_end_chain`**: at the chain's end,
  `DPf ↔ ¬ truthP3 4 ∨ c_{Pf} ≠ wHatL 4 · Π_{mLog₄ ≤ v < 7} (1 − ρ_v) · final̂(ρ)`. This is A.9's
  `relPf` (`wV · padV · finHat`) at the spec. The pieces:
  - `wHatL`: the verifier's `lvsV [1,2,3,4] w0V` at the spec;
  - `ptL` (with `ptD`): the verifier's points `Pₖ` (`tailRegs`), with `ptL_lt`;
  - `pfP`: Pf's challenges, read as `rchs2`;
  - `mleP_lvW_chain`: level `k`'s table at `Pₖ` is `wHatL k`, for `k ≤ 4`;
  - `mleN_wPf`: the padding (`mleP_pad`) and level 4's fold (`mleN_foldW`).
- **`pf_round0_agree`**: covers `¬ RejT` for Pf's round 0.

## P2.3 `FinalLaw` (`FRSoundnessLigFinal`, Part H)

- **`AcceptTail RejF W₀ c₀ L j`** is what an accepted SNARK run gives on the log for the tail. Its
  fields:
  - `chain`: `IsChain L j`;
  - `len`: `468 ≤ |es|`;
  - `rejF`: `¬ RejF`;
  - `p1`, `pf`: every P1.i and Pf round check (`Chk2`);
  - `lvl4`: `truthP3 4`;
  - `fin`: `relPf` in `DPf_end_chain`'s form.
- **`not_DC_end`**: `AcceptTail` gives `¬ DC (RejC …) (Dp (DkC …))` at the chain's end. This is
  `hend`.
- **`finalLaw_of`**:
  ```lean
  theorem finalLaw_of (S : Submission) (vk : Digest) (hF : FrontLocal W₀ c₀)
      (hFS : FrontChainStab RejF DF)
      (hAcc : ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
        (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨ ∃ j, AcceptTail RejF W₀ c₀ L j)
      (hExt : ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
        AcceptTail RejF W₀ c₀ L j →
        (∀ p < |es|, ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L (es.take (p + 1))) →
        LigeritoOut W₀ c₀ L es → ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) :
      FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀)
  ```
  Here `es = entriesOf L (pathOf L j)`. Proved: `muT_lt_one`, `chainStab_of`, `not_DC_end`,
  `not_D_prefix`, `ligerito_final_of_walk`. With `kstate_of_front`, the knowledge state at `εR`
  needs exactly four hypotheses: `FrontObl`, `FrontChainStab`, `hAcc`, `hExt`.
- **Controls:**
  - `not_acceptTail_of_cons` (negative): one inconsistent level-4 query refutes `AcceptTail`;
  - `pfP_eq`, `ptL_four_lt` (values): `pfP` is Pf's `kAt`, and `P₄` starts with `s₄`;
  - `pf_round0_agree` (the iff above).

**What is left, precisely:**

1. **The front** (S-G, after INT-3):
   - **`FrontObl RejF DF W₀ c₀`**: all of its fields (`loc`, `rej`, `ms`, `habs`, `handoff`,
     `hsingle`, `hfin`, `hstab`) for concrete `RejF`, `DF`, `W₀ = ι ∘ w0F Wrs cells κ′` and
     `c₀ = v*`.
   - **`FrontChainStab RejF DF`**.
   - The row Spartan unit exists (`FRSoundnessRows`). The Z/L and S units, and the RS0 … B′ dooms,
     are not built.
   - INT-3 owns the node `truthS1`/`sh_reads_chain_only`, `truthB′` at `J_f = 9`, and the E4-end
     binder in `truthE4`. They enter only through `DF` and `hExt`.
2. **`hAcc`** (not INT-3):
   - `runLog_chain`: an accepted run's FS entries are the chain of a log entry. The tools are
     `fsQ_gen` (S-0) and `¬ Bad` (no repeated query: unique preimages for `pathOf`).
   - The `W` branch: the proof is copied and `Rel` is decided (§5.4).
   - The finals in log terms:
     - P1.i round checks: `roundOpsK`'s semantics against `Chk2`, with `lvC i` equal to the
       verifier's claim registers. For `i ≥ 1` this is `finPLow` plus `foldAt_of_cols` on P2.i's
       `askCol`/Merkle ops. For `i = 0` it is the front's `c₀`.
     - Pf: `pf_round0_agree` and `finP4`'s `assertEq`.
     - `lvl4`: `finP4`'s `encFlag` (`run_encOps`: `encVal = encAt 4 finalAt`) plus
       `truthP3_four_of_cols`.
     - `fin`: `relPf` with `wV = wHatL 4` (the reads `sRegs`/`kcOf`/`ysOf`/`tailRegs` ↦
       `sAt`/`kcAt`/`qPos`/`ptL`), `padV = Π (1 − pfP v)` (characteristic 2), and
       `finHat = mleN 7 finalAt pfPt` (`eqTableK`).
     - `w0V = mleP (nrP 0) W₀ (ptL 0)` is the front's (`weight_mle`, `mleN_w0F`).
   - I did not attempt `runLog_chain`. It needs `V`'s run semantics on the hashed trace
     (`accWith`, `semIR` over the log's answers), which did not fit this pass.
3. **`hExt`** (the front plus S-H2):
   - from no doom on every front prefix and `LigeritoOut.claim0`/`level0_committed`: the PIOP
     truths on `f⁽⁰⁾`, then `leaf_sound`/`node_sound`, which give `Rel`;
   - `S.E c π L` is the extractor's output by `ext_good_tape`'s `'N'` case, which takes
     `LigeritoOut.close`/`agree` per level.

## P2.4 Files and times

| Module | Code (HEAD → now) | Theorems | Wall (sequential) | Type checking (items > 100 ms) | Max RSS |
|---|---|---|---|---|---|
| `FRSoundnessTailD` | 190 → 205 | 22 → 25 | 17.9 s | 4.92 s, 3.70 s (`rounds_check`/`phOf_check`, as before) | 3.21 GB |
| `FRSoundnessTailO` | 268 → 302 | 26 → 28 | 11.2 s | 1.28 s | 2.89 GB |
| `FRSoundnessTailM` | 250 → 261 | 22 → 21 | 9.4 s | 0.33 s | 2.76 GB |
| `FRSoundnessCompose` | 324 (unchanged) | 23 | 16.1 s | 1.87, 1.27, 2.07, 1.25 s | 2.95 GB |
| `FRSoundnessLigFinal` | 337 → 449 | 36 → 45 | 11.9 s | 1.25 s (`lig_pos_check`), 0.16 s | 2.88 GB |

Logs: `logs/S-G2/profile2-*.log` and `time2-*.log`. Code lines are from the core's `loc.py`. No
`decide` runs over a table, a layout or a program.

## P2.5 Open questions

1. §5.2's P3 row should read `9/2^128` for levels 0–3 and 0 for level 4 (P2.1). The blueprint's
   A.10 rows P3.4 and Pf should say: "P3.4: no escape; Pf: background `¬ truthP3 4` (`finP 4`'s
   direct check), claim `c1 4`, weight `wFold 4` padded". A.9 is unchanged.
2. Who takes `runLog_chain` and the finals-to-log bridges in `hAcc`? These are S-0/S-F's
   `exec_fin*` semantics and S-G's log side.
