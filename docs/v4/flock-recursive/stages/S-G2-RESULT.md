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
