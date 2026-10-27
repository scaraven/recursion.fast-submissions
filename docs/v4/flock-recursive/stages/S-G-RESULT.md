# S-G RESULT (track L-cert: knowledge soundness), part 1

Base `cf2f7b3`, blueprint revision 3.9. **Status: partial.** The generic potential, its `step`
law with the H row, the log and chain machinery, the challenge fibers and the multi-answer
martingale are built and kernel-checked. Two bridges that other tracks asked for are proved. The
Flock-specific doom predicates, the §5.2 rows, `ligerito_final`, `final`, `finP`/`finPf` and
`kstate` are **not started** (§5). I stopped here because the brief asked for a conservative pace.
No sorry, no new axioms. The source rule passes (51 files, 0 findings).

## 1. What was built

Code lines from the core's `scripts/loc.py`:

| File | Code | Content |
|---|---|---|
| `FRLog.lean` (new) | 613 | `stateIn`; **`Bad`** = collision ∨ window hit ∨ state hit ∨ repeat; **`bad_step_le`** / `bad_step_frac` (the H row's count); the forest (`ansIdx`, `predIdx`, `back`, `pathOf`, `back_append_old`, `back_new`); the frontier (`frontier_append`); **`extCount_split`**; chains over the Fiat–Shamir items (`fsCheck`, `fsItems`, `Matches`, `IsChain`, `chains`, `chains_append`, `isChain_new` and its converses); **challenge fibers** (`chFEquiv : Digest ≃ F × F`, `chKEquiv : Digest ≃ K`, `card_chF2_fiber`, `card_chF_fiber = |S|·2^128`, `card_chK_fiber = |S|`); controls |
| `FRSoundnessDefs.lean` (new) | 303 | Part A: `L₀`, `EscAtG`, `EscG`, `termG`, `sumG`, **`muG`**, `muG_empty`, `muG_lt_one`, **`muG_step`** (error `badCount/2^256 + δ` from a local inequality `hloc` and `hseed`), `badCount_frac_le` (`≤ 2^-142`). Part B: `lastAns`, `ext1`, `ext`, **`condCount`**, `condCount_split`, `condCount_last` |
| `FRSoundnessLigerito.lean` (new) | 9 | **`eqBits_eq_eq`** (A.2, S-D-m4) |
| `FRVIRFinalsSG.lean` (new) | 43 | **`lagV_eq_lagrangeWeight`** (S-F open 2): `finRS`'s computed skip weight is `lagrangeWeight` at the 64 nodes of `quirky_claim_split` (`sNode`) |
| `FR.lean` | +4 | imports the four modules |

Statements worth reading:

```lean
theorem muG_step (δ : ℝ≥0)
    (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0)
    (hloc : ∀ (L : Log) (i : ℕ) (q : ByteArray), ¬ Bad L → IsChain L i →
      q ∉ L.map Prod.fst → stateIn q = some L[i]!.2 →
      ∑ a : Digest, (if Matches (entriesOf L (pathOf L i) ++ [(q, a)]) then
          (if EscAtG D L (entriesOf L (pathOf L i) ++ [(q, a)]) then 1 else 0) +
            φ L (entriesOf L (pathOf L i) ++ [(q, a)]) else 0) ≤
        2 ^ 256 * ((if q = squeezeQ L[i]!.2 then φ (L₀ L i) (entriesOf L (pathOf L i)) else 0) +
          δ))
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D φ L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D φ (L ++ [(q, a)]) ≤ (muG D φ L + ((badCount : ℝ≥0) / 2 ^ 256 + δ)) * 2 ^ 256

theorem bad_step_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤
      L.length * (2 ^ 17 + 2) + (2 ^ 17 + 1)
```

`muG_step` has the contract's `KState.step` form once `δ` is fixed. `kstate` then needs only
`hseed`, `hloc` (the rows) and `final`.

## 2. Build and kernel times

Single core, sequential elaboration (`lean -DElab.async=false --profile`), logs in
`logs/S-G/profile-<module>.log`:

| Module | Wall (with 3.5 s import) | Elaboration | Type checking | Max RSS |
|---|---|---|---|---|
| `FRLog` | 11.4 s | 0.40 s (tactics 1.3 s) | 0.68 s | 2.6 GB |
| `FRSoundnessDefs` | 8.6 s | 0.16 s | 0.15 s | 2.6 GB |
| `FRVIRFinalsSG` | 9.2 s | 0.02 s | 0.03 s | 2.6 GB |

`FRSoundnessLigerito` builds in 3.7 s (lake). No `decide` on a program, layout or table. The one
`decide` that touches `items` reuses S-0's `qlen_mod`.

Axioms: a scratch `#print axioms` was run outside the entry on `muG_step`, `bad_step_frac`,
`card_chF_fiber`, `card_chK_fiber`, `condCount_split`, `matches_seed` and
`lagV_eq_lagrangeWeight`. Each prints `propext`, `Classical.choice`, `Quot.sound`.

## 3. Controls

| Control | Shows |
|---|---|
| `not_bad_nil` | `Bad` is not trivially true: the empty log is not bad. |
| `bad_self_state` | A squeeze answered by its own state is bad. This is the `i = j` case that keeps the forest acyclic. |
| `bad_collision` | Two different queries with one answer are bad. |
| `matches_seed` | `Matches` is inhabited: a seed query with a 48-byte header, alone, matches. |
| `not_matches_squeeze` | `Matches` is not trivial: a squeeze alone does not match, because a chain starts at a seed. |
| `muG_empty` / `muG_bad_self` | The potential is `0` on the empty log and `1` on a bad log. |

§5.6's controls for the potential were not done: "the step at one phase and its failure at
`ε = 2^-121` on Z2" needs the Z2 doom predicate.

## 4. Deviations from the blueprint (with reasons)

1. **`L₀ L j = L.take j`** (the log before the chain's last entry), not spartan-srom's "before
   the cut". The caps of levels 1–4 and the final message are absorbed mid-chain, so their trees
   are not in a prefix fixed at the first absorb. Consequence: each row's `hloc` must show that its
   `D`/`φ` read the same values off `L.take i` and `L` under `¬ Bad L`. For trees under caps
   absorbed in the chain, this is `colL_prefix`/`colL_append`.
2. **`Bad`'s window hit**:
   - The window hit counts only queries of at most `queryCap` bytes. The knowledge state's log holds
     arbitrary oracle queries, and a longer query would make the count unbounded. The blueprint's
     `(queryCap/16 + 1)·logCap` silently assumes the restriction.
   - The window hit includes the entry's own query (`i ≤ j`).
   - It takes both offsets `7 + 16k` and `8 + 16k` for every query, a superset of `inPlay`.

   The H row becomes `≤ 2^-142` (`badCount_frac_le`), not `2^-144`. §5.2's total
   `2^-120.36 + 2^-142` stays below `εR`. Please update §5.1/§5.2.
3. **`Bad` has no "flipped group" event.** §5.1 lists one, but the blueprint never defines it.
   Please define it, or drop it if it is a spartan-srom leftover.
4. **The chains are over `fsItems = items.filter isFS`** (451 items, the same for every kind). The
   column and node queries are not on chains: they carry no state, so only `Bad` charges them.
   This is how I read §5.1's "`Matches` re-parameterised by the item sequence".
5. **The challenge fibers are in `FRLog`**, not in a separate `FRTranscript` (§7 lists
   `FRTranscript` for the fiber counts and `Matches`). This saves a module.
6. **`lagV_eq_lagrangeWeight` and `eqBits_eq_eq` are proved, but no consumer uses them yet.**

## 5. Open items (not started), and what each needs

1. **The Flock doom predicates and `φ`** (`FRSoundnessDefs`, the template's Part C). Each needs:
   - the phase of each Fiat–Shamir position, computable from `phases` (a `rnd`-like map for the
     multi-squeeze phases Z1, S1, Lr1, RS1, E1, P2.i, P3.i);
   - the messages and challenges read off a chain, at those positions;
   - the committed words `W⁽ⁱ⁾` read off `L` under each absorbed cap (`colL (frEnc i)`);
   - per-phase `Doom` relative to the decoded `f⁽ⁱ⁾`, the dummy rounds (`real κ`), and the kind
     from the seed's header.

   This is the bulk of the stage: spartan-srom's equivalent is about 3,000 lines for a much
   smaller transcript.
2. **The rows (`FRSoundnessStepA/B`).** I checked whether S-C's and S-D's counts fit the step
   form, and **found no misfit**. Every count is a bound on bad challenges in F or K:
   - `round_bad_le` / `round_escape_le`, `skip_pair_bad_le` (126), `batch_pow_bad_le`,
     `batch2_bad_le`, `pair_bad_le`/`seq_bad_le` (two coordinates per answer), `rs1_joint`;
   - `round_bad_cover` (P1) and `positions_bad_le` (P2, in ℚ over `Fin t → Fin n`).

   They enter `hloc` in one of two ways:
   - through `card_chF2_fiber`/`card_chK_fiber`, for single-squeeze phases;
   - through `condCount` with `condCount_split`/`condCount_last`, for multi-squeeze phases (the
     phase's whole bad probability is charged at its first squeeze).

   Two pieces are still missing: a `card_idx_fiber` for P2 (positions from `idxOf` bits; the
   unused bits are uniform), and a generic `hloc_of` (the template's §9.3 step 4, re-done for
   deviation 1).
3. **`ligerito_final`** (the per-level induction with `fold_preserves`/`fold_lift`/`mca_ud_line_K`/
   `interp_F_D`/`positions_bad_le`/`cap_binding`). It needs one more Merkle piece: the final walk
   needs `¬ Hit (frEnc i)`, whose `carried` has no size cap. The plan is to instantiate a
   `MerkleEnc` with `carried` restricted to queries of at most `queryCap` bytes (`colL` does not
   read `carried`), and to prove `carried q ⊆ wins q` for those queries, so that this `Hit` implies
   `WinHit`. That stays inside L-cert.
4. **`finP i`, `finPf` and their `exec_fin*` lemmas** (A.9; `rsWeight` with the leaf's 3 points,
   `evalM(r_{E2}, ρ)`, A.7's cell order, P30's padding). Not started. They go in `FRVIRFinalsSG`.
5. **`final` (`FRSoundnessFinal`) and `kstate vk` (`FRKState`).** Not started. Whether `final`
   discharges `node_sound`'s H-side hypotheses or carries them was not reached.

## 6. Questions for the orchestrator

1. Deviation 2 (the H row at `2^-142`, windows only on queries of at most `queryCap` bytes, the
   self case) and deviation 3 (what is "a flipped group"?).
2. Deviation 1 moves a stability obligation onto every row. Is it acceptable, or should `L₀`
   carry the per-level absorb indices instead?
3. The remaining scope (§5) is well beyond the size of this pass. Should S-G be split, for
   example as S-G1 (doom predicates and rows), S-G2 (Ligerito and `final`) and S-G3
   (`finP`/`finPf`), each with its own review?

---

# S-G3: `finP i`, `finPf`, the dump

Base `c6089f7` (HEAD). Built against HEAD's versions of other tracks' modules. S-0's uncommitted
edits (`FRVIRSpec`, `FRVIRFinals`, `FRFormat`, `FRTranscriptDefs`) are not included, so this must
be rebuilt and re-dumped once they land.

**Status:**
- **`finP 0 … 4` are done.** Ops, flag lemmas, no-ask lemma and meaning lemmas are proved.
- **The dump is done, with `finPf` still pending.**
- **`finPf` is blocked** on two interface items owned by S-0, L-circ and S-E2 (§3 below).

## 1. What was built (`FRVIRFinalsSG.lean`, 447 code lines in total; 43 lines were S-G part 1)

The source is the native verifier (`prover/ligerito.rs`, `verify`/`weight_eval`), read against
A.9.

**Locating level `i`'s outputs.** Level `i`'s phases are at `phaseIx "P1" + 5i + {0,…,4}` (`lvOuts`).
`Q`'s outputs are the column folds `y_q`; the skeleton already computes
`y_q = dotKF(col_q, eqTableK(s_i))`. Each position's `idx` register is `y_q − 3` (`FRVIR.posOps`).

**`finP i`, `i < 4` (`finPLow`).**
- It computes `claimN(P1.i) + Σ_q eq(κ_c, bits₉(q))·y_q`, with `κ_c` the first 9 coordinates of
  P3.i, using `eqTable`, `getF`, `mulKF` and `addK`.
- It asserts this equals `claim0(P1.(i+1))`, the free initial claim of the next fold sumcheck.
- It exports the batched claim.

**`finP 4` (`finP4`).**
- For each of the 126 positions it checks `y_q = Enc₄(final)[p_q]`:
  - `Ŵ_v(D[p]) = tensorW p e_v` for `v < 7`, with `e_v` constant `AK 7` unit vectors;
  - then Horner over the 128 final-message elements, top bit first.
- It asserts that Pf's free initial claim equals `claimN(P1.4)`. The native verifier adds nothing
  at the last level.
- The `m = 30` padding is zero (`FRVIR.finalOps` asserts it), so the sum over `2^7` equals the
  sum over `2^5`.

**Lemmas:**
- `flag_finPLow`: the field asks nothing, its flag is `relPLow` (the binder equation), and its
  export holds `vNext`.
- `flag_finP4`: the flag is `relP4` (every `y_q = encVal p_q`, and the Pf binder).
- `noAsk_finP`: `finP i` asks nothing (`items_gen`'s hypothesis).
- Meaning lemmas:
  - `accV_eq`: the accumulator is `A + Σ_k e[q+k]·Y_k`.
  - **`hornerVal_eq`**: Horner's value is `Σ_{c<2^v} X_c · Π_{u<v} W_u^{bit_u(c)}`. With `W_u = Ŵ_u(D[p])` this is the novel-basis encoding `Σ_c final[c]·X_c(D[p])` (`FRRS.novelX`).
- Run lemmas (generic, reusable): `run_indep`, `run_frozen`, `run_accOps`, `run_layer`,
  `run_horner`, `run_encOps`, `run_positions`.

**Axioms.** A scratch `#print axioms` on `flag_finPLow`, `flag_finP4`, `hornerVal_eq`, `noAsk_finP`
and `accV_eq` shows only `propext`, `Classical.choice` and `Quot.sound`. The source rule finds
nothing (53 files, 0 findings). There are no lines over 100 characters and no warnings.

**Timing.** Sequential single-core run: 20.2 s wall (3.5 s of it import), 3.5 s elaboration
(5.3 s tactics), 0.66 s type checking, 2.6 GB (`logs/S-G/profile-FRVIRFinalsSG.log`).

## 2. The dump (`logs/S-G/dump/`)

`logs/fr-build-SG/dump/IRDumpSG.lean` is a private copy of S-0's `probe/fr-irdump/IRDump.lean`. I
did not edit S-0's tool. The copy differs in three ways:
- the finals are `sfFinals finP pending` (S-0's, S-F's and S-G's `finP`; `finPf` pending);
- array constants print as `AF:[…]`/`AK:[…]`, where S-0's tool prints `arr`;
- it is built as `lake build irdumpsg` in the S-G tree.

Outputs:
- `ops-{L,P,N,M}.txt`: 185,375 lines each;
- `items.json`;
- `summary.txt`: ops 185,360; registers 53,164; asks = items = 8,874; `piSize` 755,664 (HEAD).

Sections are marked `-- final finP i (S-G)`. finP 0 is 875 ops, finP 4 is 33,148 ops. sha256 of
`ops-L.txt`: `e31ea2ab2ae0f0a9…`.

**HEAD's skeleton differs from S-0's last dump** (`logs/S-0/dump`, made from S-0's working tree).
For example, L3 absorbs 112 bytes at HEAD and 128 bytes in S-0's tree. P2 should take the dump made
after S-0 lands. To regenerate:
`bash logs/fr-build-SG/snap.sh && lake build irdumpsg && .lake/build/bin/irdumpsg ops L`, run in
`logs/fr-build-SG` under the 16 G scope.

## 3. `finPf`: blocked, with its exact specification

Two interface items block it:
1. **`rsWeight` is not in the op set.** A.8 (revision 3.9) lists `rsWeight r″ pts κ ρ → K`, which
   replaces `mbp`. `FRVIR.Op` and `OpImpl` still have only `mbp`. Owner: S-0 (op and `OpImpl`
   field) with S-C (`OpSpec`, `weightEval`).
2. **`evalM` cannot take Ligerito's point.** The point `ρ` is in K (the P1 and Pf challenges are
   `chK`), but A.8's `evalM τ σ` has `σ : AF 23` and `OpImpl.evalM : Array F → Array F → F×F×F`.
   The E weight `(Ã_M + κ_E B̃_M + κ_E² C̃_M)(r_{E2}, ρ)` needs `σ ∈ K^23`.
   - Proposed change: a K-point form `evalMK : AF 21 → AK 23 → K × K × K` (or `evalM` with
     `σ : AK`).
   - Owners: S-0 (op), S-E2 (`evalM_eq` over K), L-circ (`FRVIREval`).
   - The same holds for any other weight evaluated at `ρ`.

With both ops in place, `finPf` follows directly from the native verifier. Notation:
- `s_k` are P1.k's 4 or 6 K challenges and `sf` are Pf's 7 challenges.
- `μ = 7` for L32 and `μ = 5` for the `m = 30` kinds.
- `P_4 = s_4 ++ sf[0..μ)`, and `P_k = s_k ++ P_{k+1}[1..]` for `k = 3 … 0`. `P_0` has `m − 7`
  coordinates.
- `û(β) = 1 + β(1 + u)`, where `u` is the K basis element of the coordinate split
  (`ligerito.rs::u_hat`).

Then:

```
Ŵ_4(P_4) = (Π_{k=1..4} û(s_k[0]))·w0(P_0)
         + Σ_{i=0..3} (Π_{k=i+1..4} û(s_k[0])) · Σ_q eq(κ_c^{(i)}, bits₉(q))·tensorW(p_q^{(i)}, P_{i+1}[1..])
w0(ρ)    = rsWeight(r″, pts, κ, ρ)                              -- a leaf: 3 points
         + [node] κ′·evalMK(r_{E2}, ρ) + Σ_{k} κ′^{k+2} eq(cell_k, ρ)   -- A.7's cell order, finE export 1
check:     claimN(Pf) = Ŵ_4(P_4) · Π_{x ∈ sf[μ..7)} (1 + x) · final̂(sf)     -- final̂: eqTableK(sf) · final (128 terms)
```

**What `finPf` needs that A.9 leaves unstated:**
- The `û` factors, which are A.9's "fold factors of levels > i".
- That `P_{i+1}` drops the first coordinate of each later level, because that coordinate is the
  coordinate-split bit.
- The padding factor applies to the whole weight, for both `m = 30` kinds (P30 and N30), not only
  P30.

Please put these into A.9.

## 4. Other findings

1. **Cost of `finP 4`.** The blueprint estimates `2·2^7·126 ≈ 32 k` products. The op form here is,
   per position, 7 `tensorW` plus 127 `mulK` and 127 `addK`. In the node's M rows (`mulK` is 3
   rows, `tensorW` is `2v` rows), that is about 60 k rows. This is an estimate from A.8's row
   column, not a measurement.

   A cheaper form needs a new op that gives the F table `X_c(D[p])` at a runtime position, followed
   by 128 `mulKF`. L-circ should decide.
2. **A.9's finP row versus the native verifier.** They agree: the batched claim for `i < 4`, the
   direct check and no claim update at the last level, and `κ_c` as 9 coordinates
   `eq(κ_c, bits₉(q))` over the query number `q` (not the position).
3. **Dump tool.** S-0's `IRDump` prints array constants as `arr`. P2 cannot read the unit vectors
   from that, so the tool should adopt the `AF:[…]`/`AK:[…]` printing.

## 5. Next

- `finPf`, as soon as `rsWeight` and a K-point `evalM` are in `FRVIR`.
- Then a re-dump after S-0 lands.
- Then S-G1: the doom predicates, the §5.2 rows, `card_idx_fiber` and `hloc_of`.
