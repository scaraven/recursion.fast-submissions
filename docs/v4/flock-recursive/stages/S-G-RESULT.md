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

---

# S-G1 (part 1): the step machinery for the rows

Base `334aa75`. **Status: partial.** Built: the generic reduction from per-position facts to
`muG_step` (`hloc_of`, `muG_step_of`), Flock's multi-squeeze phase map (`fsRnd`, checked), and
`card_idx_fiber`. **Not started:** the doom predicates over the Flock transcript and the §5.2 row
lemmas themselves (§3 lists what they need). No sorry, no new axioms. Source rule: 56 files, 0
findings. No warnings, no lines over 100 characters.

## 1. What was built (code lines from `loc.py`)

| File | Code (total) | Added |
|---|---|---|
| `FRLog.lean` | 665 | **`card_idx_fiber`** (A.2): for `k b ≤ 256`, the answers whose first `k` indices of `b` bits equal a given `f` number exactly `2^(256 − k b)`; `natLEEquiv : Digest ≃ Fin 2^256` (`natLE` is little-endian base 256, via `digestEquiv` and `finFunctionFinEquiv`); `idx_mod` |
| `FRSoundnessDefs.lean` | 601 | Part C: `split40`, **`eq_squeezeQ`**, **`matches_append_iff`**, `ext_take`, `ext_dropLast`; `RndOK`, **`pRoundG D rnd`** (the conditional-count charge), **`hloc_of`**, **`muG_step_of`**. Part D: **`fsRanges`**, **`fsRnd`**, `rangesOK_eq` (`decide +kernel`), `fsRnd_ok : RndOK fsRnd`, `fsRnd_zero`, control `fsRanges_eq` |

**`hloc_of` / `muG_step_of`.** These give the contract's `step` law for `muG D (pRoundG D rnd)`
with error `badCount/2^256 + δ`, from six facts about a doom predicate `D`. They are what each
row (or group of rows) must supply:

1. `habs`: an absorb never undooms (`D L es → D L (es ++ [x])` at an absorb item).
2. `hmid`: a middle answer of a multi-squeeze phase neither dooms nor undooms.
3. `hsingle`: at a single squeeze outside every phase, at most `N ≤ 2^256 δ` answers escape.
   This is where the F/K rows enter: `card_chF_fiber`/`card_chF2_fiber`/`card_chK_fiber` turn a
   bad-challenge count `B` into `B·2^128` (F) or `B` (K) answers.
4. `hround`: a multi-squeeze phase's escape count from its entry is at most `δ` (`condCount`).
   This is where Z1, S1, Lr1, RS1, E1 (Schwartz–Zippel over F coordinates, two per answer), P2
   (`card_idx_fiber` with `positions_bad_le`) and P3 enter.
5. `hstab`: on a non-bad log, `D` gives the same answer on the charging log `L.take i` and on
   `L`, for every formal extension of every prefix of the chain. This is part 1's deviation 1,
   now an explicit obligation. For trees under caps absorbed in the chain, it follows from
   `FRMerkle.colL_prefix`/`colL_append`, plus the self-window case (`WinHit` with `i = j`).
6. `rnd 0 = none` (the seed is in no phase).

**The Flock phase map.** `fsRanges_eq` pins the phases, each as (entry position, number of
squeezes):

| Phase | Ranges |
|---|---|
| Z1 | `(2, 10)` |
| S1 | `(98, 15)` |
| Lr1 | `(169, 8)` |
| RS1 | `(240, 4)` |
| E1 | `(244, 11)` |
| P2.0 … P2.4 | `(313, 25)`, `(352, 13)`, `(379, 10)`, `(403, 8)`, `(425, 6)` |
| P3.0 … P3.4 | `(338, 5)`, `(365, 5)`, `(389, 5)`, `(411, 5)`, `(431, 5)` |

These are positions in the 451 Fiat–Shamir items. A phase's entry may itself be a squeeze, as
for E1 after RS1 and P3 after P2. `hloc_of` handles that, because the charge at a phase's last
answer is `0`.

**Axioms.** A scratch `#print axioms` was run on `muG_step_of`, `card_idx_fiber` and `fsRnd_ok`:
only `propext`, `Classical.choice`, `Quot.sound`.

## 2. Times

Sequential single-core runs (`logs/S-G/profile-*.log`):

| Module | Wall | Type checking | Note |
|---|---|---|---|
| `FRLog` | 12.8 s | 0.77 s | |
| `FRSoundnessDefs` | 20.0 s | 7.75 s, 3.3 GB | `rangesOK_eq` and `fsRanges_eq` are `decide +kernel` over the 451-item `fsItems` (5.75 s + 1.23 s of kernel time) |

If kernel time gets tight, a hand-written position table proved equal once would be cheaper.

## 3. Not started: the doom predicates and the rows

The remaining work, in order:

1. **Transcript readers.** The message and challenge at each Fiat–Shamir position, from the A.4
   positions (Z2's 127 values, each round's 3 coefficients, the F coordinates and K challenges of
   each squeeze), and the kind from the seed's header.
2. **The committed words.** `W⁽ⁱ⁾` read off `L` under the cap absorbed at level `i`
   (`colL (frEnc i)`, with `carried` capped at `queryCap` as planned in part 1), and the
   decoded `f⁽ⁱ⁾` (`interp_F`, `coeffs_of_values`) or "far".
3. **`D` per phase.** "The running claim is false for the true `f`/witness", or "far" for the
   Ligerito levels. Each row then discharges `habs` and `hmid` (structural), and `hsingle` or
   `hround` with S-C's and S-D's counts:
   - single squeezes: `round_bad_le_of_check`, `skip_pair_bad_le` (Z2: 126), `batch_*_bad_le`;
   - multi-squeeze phases: `zerocheck_bad_le` with `pair_bad_le`/`seq_bad_le`, `rs1_joint`,
     `round_bad_cover` (P1), `positions_bad_le` with `card_idx_fiber` (P2).
4. **`hstab`** for that `D`.

Nothing found so far contradicts the step form. `δ` must be at least the P2 row
(`2^-120.36`), and `N` at most `2^256 δ`.

**Question.** S-G1's remaining part is the largest piece of L-cert. spartan-srom's equivalent is
about 3,000 lines, for one level and one kind. Should it run as its own stage with a fresh agent
and budget, starting from this RESULT?

---

# S-G1b: the readers, the committed words, the round doom and the step law at `εR`

Base `e293029` ("S-G1 part 1"), built against HEAD's versions of other tracks' modules
(`logs/fr-build-SG`, `snap.sh`). **Status: partial.**

Built:
- (1) the transcript readers;
- (2) the committed words under each cap;
- the contract's `step` at `εR = 15/2^124` from the five obligations (`step_epsR`);
- (3)–(4) **one phase end to end**: the degree-3 F rounds, with all five obligations and the step
  law proved. This is generic in the phase's position and its "truth". It is instantiated at Z3,
  and its position facts are checked for Lr2 and E2.

Not done: the composed doom over all 451 positions, and the truths it needs (§5). No sorry, no
new axioms. Source rule: 61 files, 0 findings. No warnings, no lines over 100 characters.

## 1. What was built (code lines from `loc.py`)

| File | Code | Content |
|---|---|---|
| `FRSoundnessStepA.lean` (new) | 61 | **Readers** (A.2): `entAt`, `ansAt`, `msgAt` (the absorb's payload, from query byte 40), `readF`/`readK`, `fAt es p c` (F coordinate `c` of the answer at `p`), `kAt`, `coordAt` (coordinate `2s + c` of a multi-squeeze phase), `posAt` (P2's `k`-th index, `idxOf`), **`kindOf`** (byte 71 of the seed query = the header's kind byte; `L32` otherwise); `Agree`, `entAt_append`, `agree_append`, `kindOf_congr`. **Phase starts**: `fsStarts`/`phStart` (51 phases), control `fsStarts_eq`. **Committed words**: `capPos` (cap₀ at 2, else `C.(i−1)`; `capPos_eq = [2, 313, 352, 379, 403]`), `capDig` (cap entry `c`: the message bytes `32c…32c+31`), **`colOf`** (`colL (frEnc i)` from cap entry `p / 2^sib`, height `sib`), **`wordOf`** (row `r` at position `p` = the column's F element `r`; `0` where no column is read), **`FarAt`** (no agreement set makes the word `JointClose`), `colOf_congr` |
| `FRSoundnessStepB.lean` (new) | 346 | Part A: **`epsR = 15/2^124`**, **`deltaR = εR − 2^-142`**, `err_le_epsR` (`badCount/2^256 + deltaR ≤ εR`), `N_le_deltaR`, **`StepObl`** (the five obligations of `hloc_of` as one structure), **`step_epsR`**, `condCount_eq_zero`. Part B: the degree-3 rounds: `g3At` (the coefficients `c₀, c₁, c₂, claim + (c₁ + c₂)`, as `roundOpsF … 3` / `FRVIRSpec.g3`), `rch`/`rchs`, `clR` (the running claims), `ans3`, `Wrong3`, **`D3`**, `g3_check`, `bindAll_append`/`bindAll_size`, `D3_append_iff`, `wrong3_ext1`, **`D3_single`** (≤ `3·2^128` escaping answers), `RoundsPhase`, `TruthLocal`, `TruthStable`, **`rounds3_obl`**, `three_le_deltaR`, **`rounds3_step`**. Part C: `z3_phase` (`b = 15`, 26 items, `mm 6` real), `z3_start`, **`z3_step`**. Part D: `roundsPhase_of` (from two kernel checks), `lr2_phase` (`b = 178`), `e2_phase` (`b = 256`) |
| `FR.lean` | +2 | imports the two modules |

The statement that matters most:

```lean
theorem z3_step {e : Expr} {T : Log → Log → Array (Array F)} {c0 : Log → Log → F}
    (hTc : TruthLocal 15 c0 T) (he : e.deg = 3)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ mm 6 (kindOf es)) (hst : TruthStable c0 T)
    (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : muG (D3 15 c0 (mm 6) e T) (pRoundG (D3 15 c0 (mm 6) e T) fsRnd) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG (D3 15 c0 (mm 6) e T) (pRoundG (D3 15 c0 (mm 6) e T) fsRnd) (L ++ [(q, a)]) ≤
      (muG (D3 15 c0 (mm 6) e T) (pRoundG (D3 15 c0 (mm 6) e T) fsRnd) L + epsR) * 2 ^ 256
```

This is `KState.step` for the potential of the round doom `D3`, with error `εR`. Its
hypotheses on the truth are:
- `TruthLocal`: the truth reads only the entries before the phase;
- `hsz`: the table sizes;
- `TruthStable`: the truth reads the same values off `L.take i` and `L` on a non-bad log (§10
  changes 10).

**`D3`** (the round doom):
- `D3 L es` holds when `b < |es|` and the claim after the answered rounds,
  `ans3 = min (nr κ) ⌊(|es| − b)/2⌋`, differs from `trueSum e (bindAll T (r_0 … r_{l−1}))`;
- the round challenge `r_l` is `chF` of the answer at `b + 2l + 1`, coordinate 0;
- the dummy rounds (`l ≥ nr κ`) keep the claim, so `D3` is constant there.

How each obligation is discharged:
- `hsingle` is `round_escape_le` plus `card_chF_fiber`.
- `habs` uses the checked fact that the odd offsets of the phase are squeezes.
- `hmid` and `hround` use the checked fact that no multi-squeeze phase meets the round phase, so
  `D3` is constant on those phases and `condCount = 0`.
- `hstab` is `TruthStable`.

## 2. Times (sequential, one core: `taskset -c 0 lean -DElab.async=false --profile`)

| Module | Wall (with ≈ 3.6 s import) | Type checking | Max RSS | Log |
|---|---|---|---|---|
| `FRSoundnessStepA` | 7.8 s | 1.27 s (`fsStarts_eq`, the two `kindOf` controls: `decide +kernel`) | 2.8 GB | `logs/S-G/profile-FRSoundnessStepA.log` |
| `FRSoundnessStepB` | 11.5 s | 0.24 s + 0.57 s (the `fsItems` checks of `z3_phase`, `lr2_phase`, `e2_phase`) | 2.7 GB | `logs/S-G/profile-FRSoundnessStepB.log` |

No `decide` or `simp` runs over a program, layout or table. The kernel checks touch only `fsItems`
(the 451 items) and `fsRanges`.

**Axioms** (`logs/S-G/axioms-S-G1b.log`, a scratch `#print axioms` outside the entry):
- `z3_step`, `rounds3_obl`, `step_epsR`, `z3_phase`, `D3_first_absorb` and `wordOf_nil`:
  `propext`, `Classical.choice`, `Quot.sound`;
- `kindOf_P30`, `fsStarts_eq` and `capPos_eq`: `propext` only.

## 3. Controls

| Control | Shows |
|---|---|
| `fsStarts_eq`, `capPos_eq`, `z3_start` | The phase starts and the cap positions are A.4's (Z3 at 15, the caps at 2, 313, 352, 379, 403). |
| `kindOf_P30` / `kindOf_default` | The kind reader is not constant: a header byte `'P'` gives `P30`, and a non-kind byte gives `L32`. |
| `wordOf_nil` | On the empty log no column is read, so the word is `0`. |
| `D3_first_absorb` (positive) | A false initial claim dooms the chain at the phase's first absorb (`D3` is satisfiable). |
| `not_D3_before` (negative) | Before the phase's first absorb nothing is doomed. |
| `three_le_deltaR`, `err_le_epsR` | The Z3 row (`3·2^128` answers) and the H row (`2^-142`) fit `εR`. |

Not done: §5.6's "failure at `ε = 2^-121` on Z2" needs the Z2 doom. A positive control for
`colOf` on a real Merkle path is also missing; it belongs with S-G2's `cap_binding`.

## 4. Deviations and design decisions

1. **The error split.** `εR = 15/2^124 ≈ 2^-120.093` and `δ = deltaR = εR − 2^-142` (still ≈ 2^-120.093).
   - Every row must be at most `deltaR`, and a single-squeeze row must satisfy
     `N ≤ 2^256·deltaR` (`N_le_deltaR`).
   - The P2 row (`2^-120.36`) is below `deltaR` numerically, but **not yet kernel-checked**:
     `positions_bad_le`'s `(1 − e/n)^t ≤ deltaR` must be shown at the five levels. This can be
     done here or in S-I.
2. **One phase, generic in its truth.** `D3` takes the initial claim `c0` and the tables `T` (of an
   `Expr` of degree 3) as parameters. The positions, the message decoding, the challenge map and
   the five obligations are concrete. What the truth must satisfy is three explicit predicates
   (`TruthLocal`, the sizes, `TruthStable`). The parametric form is deliberate: the truth of Z3 is
   the zerocheck over the decoded witness, and its definition belongs to the composition (§5).
3. **`D3` is a single-phase slice.**
   - It is `False` before the phase. `z3_step` is therefore the step law of a potential that
     charges only Z3; it is not yet the entry's `kstate`, whose `final` needs the full doom.
   - In the composed doom the guard `b < |es|` becomes the handoff from the previous phase (see
     §5).
   - The per-round lemmas `D3_single`, `wrong3_ext1` and `D3_append_iff` carry over unchanged.
4. **The round message is decoded from the absorb query, not from `π`.** `g3At` reads
   `c₀ ‖ c₁ ‖ c₂` from the payload at `b + 2l` and sets `c₃ = claim + (c₁ + c₂)`, as
   `FRVIRSpec.g3`. The two agree once `runLog_chain` (S-G2) identifies the query payload with
   `π`'s field.
5. **`StepObl`** packages `hloc_of`'s five obligations. `step_epsR` is the only place where
   `muG_step_of` meets `εR`.
6. **`set_option linter.constructorNameAsVariable false in`** on `D3_single`. The linter crashed
   (`maxRecDepth`) on that proof. FRLog already sets the same option.

## 5. Not done, and what each piece needs

1. **The composed doom `D`** over the 451 positions. This is the next stage's core. The design
   that the slice supports:
   - `D L es` is the doom of the phase containing position `|es| − 1`, or `Rej` (a failed assert,
     which is monotone);
   - the handoff from one phase to the next is `habs` at the next phase's first absorb (rounds
     phases, `Zend`, `L3`, `Lrend`, `RS0`, `Eend`, `C.i`). At a phase that starts with a squeeze
     (Z1 after `cap₀`; L1, S1, E1, B′, P3), it is the escape count at that squeeze;
   - each handoff is one protocol lemma (for example Z2's skip relation `FRSkip` giving Z3's
     initial claim). The truth of each phase is then a definition, not a parameter.
2. **The truths.** Each phase's tables and initial claim depend on another track:
   - Z (the zerocheck `Expr` and tables over the decoded witness, Z2's claim at `λ`): S-E/L-circ's
     node and leaf semantics;
   - L, S, Lr, RS, E: S-E1/S-E2's link, shift, ring-switch and `evalM` definitions;
   - B′, P1–P3, Pf: Ligerito (S-G2's `ligerito_final`).

   This needs no new interface: the S-C/S-D lemmas give the counts. It does need agreed
   definitions of what each phase claims (an `Expr` and tables per phase). I propose that
   S-G1c write them from `FRVIRSpec`'s phase meanings.
3. **Degree-2 F rounds (L2, S2, Lr4) and K rounds (P1, Pf).**
   - They need `Rej`, because the verifier asserts `c₁ + c₂ = claim`. `round_escape_le` already
     covers the check.
   - The K form needs `card_chK_fiber` (N = 2, `kAt`).
   - This is a direct copy of Part B with `D = Rej ∨ Wrong`.
4. **The multi-squeeze phases** (`hround`).
   - Z1, S1, Lr1, RS1, E1 and P3 need `seq_bad_le`/`pair_bad_le` over `coordAt`, with the
     coordinates and the answers linked through `chFEquiv`.
   - P2 needs `card_idx_fiber` with `positions_bad_le` over `posAt`.
   - These are the only rows that use `condCount` in earnest. They are not started.
5. **`TruthStable` for the real truths.** Words read under a cap need "`¬ Bad L` implies
   `¬ Hit (frEnc i)` on the queries read". This is part 1's planned `MerkleEnc` with `carried`
   capped at `queryCap`. They also need the case where the chain's last entry is the cap's own
   absorb: there the node that answers a cap digest precedes the absorb, by the window hit.
   `colOf_congr` covers the chain side.

## 6. Questions for the orchestrator

1. Is the composition design of §5.1 (the doom of the current phase, with handoffs at `habs` and
   at the first squeeze) acceptable? Also, should the per-phase truths be fixed as an interface
   (one `Expr` with tables and an initial claim per phase) before S-G1c?
2. Should the P2 bound `(1 − eᵢ/nᵢ)^{tᵢ} ≤ deltaR` be kernel-checked here (S-G1c) or in S-I?

---

# S-G1c (part 1): the composed doom and the generic rows

Base `e1ad02c` (blueprint revision 3.10, A.10). **Status: partial, commit-ready.**

Built:
- the composition `D = Rej ∨ D_φ` and its reduction to per-phase obligations;
- every count lemma A.10 needs at single squeezes (F and K) and at sumcheck rounds (F and K);
- the P2 row end to end: the index counting over answer tuples, and the kernel-checked
  `(1 − eᵢ/nᵢ)^{tᵢ} ≤ deltaR` at all ten levels.

Not started:
- `FRSoundnessTruths` (the `truth*` definitions);
- the per-phase dooms `D_φ`;
- the multi-squeeze coordinate rows (Z1, S1, Lr1, RS1, E1, P3);
- the final assembly of `Dp` over the 451 positions.

§4 lists what each needs. No sorry, no new axioms. Source rule: 62 files, 0 findings. No
warnings, no lines over 100 characters.

## 1. What was built (`FRSoundnessStepC.lean`, 310 code lines; `FR.lean` +1 import)

- **Part A: composition (A.10, ratified).**
  - `DPos Dp L es := Dp (|es| − 1) L es` and `DC Rej Dp := Rej ∨ DPos Dp`.
  - **`RejOK`** has three fields: `mono`; `sq` (appending at a squeeze position does not change
    `Rej`, because every asserted check completes at an absorb); and `stab` (the charging log).
  - Supporting lemmas: `rej_ext` (`Rej` is constant along a multi-squeeze phase), `condCount_congr`
    and `sq_of_fsRnd`.
  - **`stepObl_compose`**: `StepObl (DC Rej Dp) fsRnd δ N` follows from the five obligations for
    `DPos Dp`, each with the extra assumption `¬ Rej`. With that assumption a round row may use
    "the check passed". With `step_epsR` (S-G1b) this gives `KState.step` at εR for the whole
    transcript once `Dp` is assembled.
- **Part B: the single-squeeze and round rows.**
  - `single_F_le`: escapes only at a first F coordinate in `S` gives `≤ |S|·2^128`.
  - `single_K_le`: the K version gives `≤ |S|`.
  - **`round_row_F`** (`≤ deg e · 2^128`) and **`round_row_K`** (`≤ deg e`): from a false claim,
    the answers that pass the round check and make the next claim true. These are the count lemmas
    for the degree-2 and degree-3 F rounds and for the K rounds (P1, Pf); `Rej` supplies the check.
- **Part C: the P2 row.**
  - The ladder: `lvN`/`lvK`/`lvE` (`n`, `k = n/2^(i+1)`, `e = ⌊(n − k)/2⌋`), with control
    `lv_eq_pcsLevels` (these are `pcsLevels`, where `mca_ud_line` is checked).
  - **`p2_row_le_q`**: `(1 − eᵢ/nᵢ)^{tᵢ} ≤ 15/2^124 − 2^-142` at every level of every kind.
    - It is proved by `decide +kernel` on rationals. `norm_num` cannot do it: core's `Nat.pow`
      evaluation stops at exponents above 256.
  - `p2_row_le` states the same bound against `deltaR`, via `deltaR_coe`.
  - **`card_idx_in`**: the answers whose first `c` indices lie in `S` number `|S|^c·2^(256−cb)`
    (`card_idx_fiber` summed over `S^c`).
  - **`card_pos_in`**: over `r` answers with `per` indices each, the tuples whose first `t` indices
    lie in `S` number `Π_s |S|^{c_s}·2^(256 − c_s b)`, where `c_s = pc per t s` and
    `sum_pc` gives `Σ c_s = t`.
  - Supporting lemmas: `ansAt_ext` (the answers of a formal extension) and `vAt`.
  - **`p2_round_le`**: if the escape puts the first `t` positions (`posAt`) in `S`, the phase's
    `condCount ≤ (|S|/2^b)^t`.
  - `p2_params` (checked): `per ≥ 1`, `per·log₂n ≤ 256`, and `t ≤ sq·per` for every kind. `sq` is
    sized for `m* = 32`, and the m = 30 kinds fit inside it.
  - **`p2_hround`**: given the set `S` with `|S| + eᵢ < nᵢ` and the escape-in-`S` property, the P2
    phase's charge is `≤ deltaR`. This is the hround row of P2.i, missing only the truth `A_c`.
- **Controls:**
  - `rejOK_false` (positive);
  - `not_rejOK_len` (negative: a `Rej` that changes at Z1's first squeeze is not `RejOK`);
  - `pc_last` (level 0's last answer carries 2 indices);
  - `lv_eq_pcsLevels`.

## 2. Times and axioms

- **Time:** a sequential single-core run takes 9.8 s wall, 3.7 s of it import, with 2.7 GB max
  RSS (`logs/S-G/profile-FRSoundnessStepC.log`). Type checking is below the profiler's threshold.
  The 15 rational checks of `p2_row_le_q` are `decide +kernel`.
- **Axioms** (`logs/S-G/axioms-S-G1c.log`):
  - `stepObl_compose`, `p2_hround`, `p2_row_le_q`, `card_pos_in`, `round_row_F` and `round_row_K`:
    `propext`, `Classical.choice`, `Quot.sound`;
  - `not_rejOK_len`: `propext`, `Quot.sound`;
  - `lv_eq_pcsLevels`: `propext`.

## 3. Deviations

1. **`RejOK.sq`.** `Rej` must not change when an entry is appended at a squeeze position. A
   check that reads a challenge is placed at the next absorb (A.10's checks are all at absorbs).
   The last check, `finPf`, reads Pf's last challenge and has no later absorb, so it stays with
   `final` (accepted run), not with `Rej`.
2. **P2's answers.** The phase has `sq` answers sized for `m* = 32` for every kind. `p2_params`
   checks that the m = 30 kinds' indices fit. The unused indices are unconstrained, which
   `card_pos_in` counts exactly.
3. **`set_option linter.constructorNameAsVariable false`** is set for the whole module. The
   linter crashes (`maxRecDepth`) on the Digest-fiber statements, as in FRLog and StepB.

## 4. Not done, and what each piece needs

1. **`FRSoundnessTruths`.** The truths split by who owns their definitions:

   | Truths | Needs | Owner | Status |
   |---|---|---|---|
   | Ligerito: `decode_i` (rows of a `JointClose` witness), `far_i` (`FarAt`, StepA), `A_c` for P2, `truthC`, `truthP1`, `truthP3`, `truthPf` | `FRProximityFold`/`FRRS` only | L-cert | can start now |
   | `truthZ0`/`Z2`/`Zend` | `unpack` (`FRFormat`, S-0), `A₀^κ`/`B₀^κ` (`FRBlockLayout`), `E` (`FRPubTarget`) | other tracks | — |
   | `truthL3`, `truthS1` | `lin_trueSum_kinds`, `shift_sound`/`slotW_mle` (S-C) | S-C | — |
   | `truthLr` | `evalL`/L layout (`FRVIREval`, L-circ) | L-circ | — |
   | `truthRS` | `rsT`/`rsTruth` (S-C `FRRingSwitch`) | S-C | — |
   | `truthE` | `evalM`, `compileMux` matrices (S-E2) | S-E2 | — |
   | `truthB′` | the public cells, from `FRNodeLayout` | other tracks | — |

   All of these exist at HEAD except `evalMK` and `rsWeight` (S-G3 §3). Where a definition is
   missing, the plan is to state it as a hypothesis.
2. **The per-phase dooms and `Dp`.** These are the D3-style definitions per phase:
   - `Wrong2` for the asserted rounds, closed by `round_row_F`/`round_row_K`;
   - `D3` for Z3, Lr2 and E2 (S-G1b);
   - the batch rows, through `single_F_le` with `batch_pow_bad_le`;
   - P2 through `p2_hround`.

   Each also needs its handoff at the next absorb or squeeze, and `Dp p := D_{φ(p)}` through
   `phStart`.
3. **The multi-squeeze coordinate rows** (Z1, S1, Lr1, RS1, E1, P3; `hround`). These need a
   `card_pos_in` analogue for F coordinates (`coordAt` over `chFEquiv`), combined with
   `seq_bad_le`/`pair_bad_le`/`rs1_joint`. It is the same counting pattern as P2, at
   `2^128`-element coordinates.
4. **`TruthStable` for word reads.** As in S-G1b §5.5: the bridge from `¬ Bad L` to
   `¬ Hit (frEnc i)`, and the cap's own absorb.

---

# S-G1c (part 2): the Ligerito words, and "no bad event, no Merkle hit"

Base: HEAD after S-G1c part 1. **Status: partial, commit-ready.**

The new module is `FRSoundnessTruths.lean`: 93 code lines, plus one import in `FR.lean`. There
is no sorry and no warning. The source rule passes (63 files, 0 findings).

## 1. Part A: the level words

These are A.10's notation for the Ligerito truths.

| Definition or theorem | What it is |
|---|---|
| `wordK` | Level `i`'s word in K. |
| `codeK κ i` | The level's code, `rsCode (Dpts nᵢ) kᵢ`. |
| **`farL`** | `far_i`: no agreement set makes the word `JointClose` at radius `eᵢ`. |
| `not_farL_iff` | `¬ farL` holds iff some family of codeword rows agrees with the word on at least `n − e` positions. |
| **`decodeL`** | The decoded codeword rows: a choice from `not_farL_iff`, and `0` when the word is far. |
| **`decodeL_spec`** | The decoded rows lie in the code and agree with the word on at least `nᵢ − eᵢ` positions. |
| `farL_congr` | The word reads only the entries up to the cap's absorb. |
| `not_farL_nil` | Positive control: the empty log gives the zero word, which is a codeword. |

## 2. Part B: no bad event, no Merkle hit (item 4, first half)

| Definition or theorem | What it is |
|---|---|
| `frEncW i` | Level `i`'s encoding with `carried` filtered to the query's windows (`wins`). Its `carried_nodeQ` holds because both children of a node query are windows at offsets 8 and 40. |
| `colL_frEncW` | `colL (frEncW i) = colL (frEnc i)`, since `colL` never reads `carried`. |
| **`not_hit_of_not_bad`** | `¬ Bad L → ¬ Hit (frEncW i) L`: a hit under `frEncW` is a window hit. |
| **`colL_take`** | On a non-bad log, a column read under a digest that an entry of `L.take n` carries within its windows is the same on `L.take n` and on `L`. This is `colL_prefix` plus `colL_append`. It is the `hstab` read of A.10 for every word under a cap absorbed strictly inside the chain's prefix. |

## 3. Time and axioms

- **Time:** 7.4 s wall single-core, 3.9 s of it import, 2.6 GB
  (`logs/S-G/profile-FRSoundnessTruths.log`).
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound` (`logs/S-G/axioms-S-G1c-2.log`).

## 4. Remaining work, in the coordinator's order

1. **The other truths.**
   - **P2's consistency set `A_c`.** It needs the index map between levels (A.2's coordinate
     split: next row `(x mod 8)·2 + c`, column `x div 8`) and `foldRows` on columns.
   - **`truthC`, `truthP1`, `truthP3`, `truthPf`.** These are `decodeL` plus the fold and
     `novelX_tensor`. `truthPf` takes `evalMK` and `rsWeight` as hypotheses.
   - **The PIOP truths (Z, L, S, Lr, RS, E, B′).** These are as in part 1 §4.1.
   - **The negative control for `farL`.** It needs an explicitly far word.
2. **The per-phase dooms and `Dp` over `phStart`.** Not started.
3. **The multi-squeeze coordinate rows.** Not started.
4. **Stability, second half.**
   - **(a) Cap entries are windows.** Each cap entry is a window of the cap's absorb query
     (offset `40 + 32c = 8 + 16(2 + 2c)`, query size at most `40 + 8192 ≤ queryCap`). This is
     byte-level: `bytesAt (absorbQ st msg) (40 + 32c) 32 = bytesAt msg (32c) 32`, plus the chain
     entry at `capPos i` being `absorbQ`.
   - **(b) The cap's own absorb.** This is the case where the chain's last entry is that absorb.
     The first preimage of a cap digest is then strictly before the absorb: a later one is a hit,
     and the absorb itself is a window self-hit. So the top step of `colL` reads the same entry on
     `L.take i`, and `colL_take` covers the children.

---

# S-G1c (part 3): stability of word reads finished; `FR` builds again; re-dump with `finP`

Base `81f19b2`, after S-0 landed. **Status: partial, commit-ready.**

- `FR.lean` builds as a whole against HEAD (`lake build FR`, 2,277 jobs).
- There is no sorry and no warning in S-G's modules.
- The source rule passes: 64 files, 0 findings.
- Axioms are only `propext`, `Classical.choice` and `Quot.sound` (`logs/S-G/axioms-S-G1c-3.log`).

## 1. Stability, second half (item 1)

This is `FRSoundnessTruths` Part C. The module is now 162 code lines.

- **`bytesAt_extract40`**: reading the message at `o` is the same as reading the absorb query at
  `40 + o`.
- **(a) `cap_carried`**: cap entry `c` of an absorb of `len ≥ 32(c + 1)` bytes is a window of
  that absorb query, at offset `40 + 32c = 8 + 16(2 + 2c)`. Hence it is in `(frEncW j).carried`
  of the query, for any query of at most `queryCap` bytes.
- **(b) The cap's own absorb**, in three steps:
  - `ans_lt_of_carried`: on a non-bad log, any entry answering a digest that entry `i` carries
    comes strictly before `i`. A later entry would be a hit; entry `i` itself would be a window
    self-hit.
  - `pre_take_own`: hence `pre (L.take i) d = pre L d`.
  - **`colL_take_own`**: the column read under a digest that entry `i` carries is the same on
    `L.take i` and on `L`. The top step uses `pre_take_own`; the children use `colL_take`.

Together with `colL_take` (part 2), this covers every word read A.10 lists. For the chain at a
cap's absorb position, `TruthStable` reduces to `cap_carried` plus one of the two `colL_take`
lemmas.

## 2. Fixes for `FR.lean`

`FR.lean` did not build because two names in `FRVIRFinalsSG` clashed with other modules:

| Old name | Clashed with | New name |
|---|---|---|
| `accV` (the finals' accumulator), with `accV_eq` | `FRVerifier.accV` | `accVal`, `accVal_eq` |
| `sNode` (the skip nodes in F) | `FRSpartan.sNode : Fin 64 → Fin 128` | `sNodeF` |

S-G3 §1's statement `accV_eq` now reads `accVal_eq`.

## 3. The re-dump (`logs/S-G/dump/`)

- **Tool.** The private copy `logs/fr-build-SG/dump/IRDumpSG.lean` was refreshed from S-0's
  current tool (`probe/fr-irdump/IRDump.lean` at `81f19b2`, which prints arrays and the
  revision 3.9 ops). It differs in two ways only: it imports `FRVIRFinalsSG`, and it uses
  `fins := sfFinals finP pending`.
- **Contents.** It dumps S-0's and S-F's finals and `finP 0 … 4`. **`finPf` is still a pending
  placeholder**, marked `-- final finPf (S-G): PENDING placeholder`.
- **Outputs:**
  - `ops-{L,P,N,M}.txt`, 185,390 lines each;
  - `items.json`;
  - `summary.txt`: ops 185,377; registers 53,164; asks = items = 8,874; `piSize` 755,680.
- The sha256 of `ops-L.txt` begins `346c647431826922`.
- **To regenerate**, in `logs/fr-build-SG` under the 16G scope:
  `bash snap.sh && lake build irdumpsg && .lake/build/bin/irdumpsg ops L`.

## 4. Not done, for a fresh invocation

1. **`finPf` with the real ops** (`rsWeight`, `evalMK`, `phiRS` are now in `FRVIR`). The formula
   is S-G3 §3's, with §10 changes 11 (the `û` factors, each later level's point without its first
   coordinate, the padding factor for both m = 30 kinds). It needs:
   - the ops;
   - `flag_finPf` and `noAsk_finPf`, like `finP4`'s lemmas;
   - a re-dump, which P2 is waiting on.
2. **S-G1c items 2–5:**
   - the remaining truths (`A_c`, `truthC`/`P1`/`P3`/`Pf`, the PIOP truths);
   - the per-phase dooms and `Dp` over `phStart`;
   - the multi-squeeze coordinate rows;
   - the instantiated `KState.step` at εR for the whole transcript.

I stopped here because the context of this invocation is long.

---

# S-G1d: `finPf` with the real ops, its lemmas, the re-dump; the Ligerito truths; the coordinate row

Base: HEAD `c8e1869` (S-F's `finRS` on the revision 3.9 op set), built against HEAD's versions of
other tracks' modules (`logs/fr-build-SG/snap.sh`). **Status: item 1 done; items 2–4 partial;
item 5 not started.** `FR` builds as a whole with the new import (`logs/S-G/build-FR-S-G1d.log`,
2,278 jobs). No sorry and no warning in S-G's modules. The source rule passes (70 files, 0
findings). Axioms are only `propext`, `Classical.choice` and `Quot.sound`
(`logs/S-G/axioms-S-G1d.log`). There are no lines over 100 characters.

## 1. `finPf` (item 1, `FRVIRFinalsSG`)

**The ops** follow the native verifier (`ligerito.rs::verify`/`weight_eval`, `leaf.rs::claim_points`,
`ringswitch.rs::rs_weight`, `mle.rs::mle_k`). With `μ = m − 25`, `P₄ = s₄ ++ sf[..μ]`,
`Pₖ = sₖ ++ Pₖ₊₁[1..]` and `û(β) = 1 + β(1 + u)`:

```
Ŵₖ(Pₖ) = û(Pₖ[0]) · (Ŵₖ₋₁(Pₖ₋₁) + Σ_q eq(κ_c⁽ᵏ⁻¹⁾, bits₉(q)) · tensorW(p_q⁽ᵏ⁻¹⁾, Pₖ[1..]))
Ŵ₀(ρ)  = rsWeight(r″, pts, κ, ρ) + [node] κ′·(Ã + κ_E B̃ + κ_E² C̃)(r_E2, ρ) + [node] Σ_k κ′^(k+2) eq(cell_k, ρ)
check:   claimN(Pf) = Ŵ₄(P₄) · Π_{x ∈ sf[μ..7)} (1 + x) · final̂(sf)
```

Register blocks, in order:
1. the constants `1`, `1 + u`, `0` of K;
2. 17 K points (`pfPts`), built by `PtSrc`: an F register through `mulKF one`, a K register
   through `addK · 0`, or a constant. They are:
   - the claim points at `m = 32` and `m = 30`, as the native `claim_points`:
     - Z: `ρ₂ … ρ₇` and Z1's `m − 13` coordinates;
     - Lc: L2's challenges `7 … 13` and Z3's real challenges from `8`;
     - Sh: S2's challenges `m − 7 … m − 5`, four zeros, S2's first `m − 14`;
     - the node's Lr point (provisional, §4 item 1);
   - the tails `P₁[1..] … P₄[1..]` and `P₀`, at both `m`. They differ only in their last two
     coordinates (Pf's challenges 5 and 6);
3. `keep is32` picks the kind's tails and `P₀`;
4. `packF r″`, `rsWeight` (the claim points by kind: `rsPtIx`, three for a leaf, four for a
   node), `evalMK(r_E2, P₀)` (`finE`'s export 1), the E combination, `κ′·E`;
5. `ρ_v` and `1 + ρ_v` for the 23 coordinates, `κ′²`, then the nine cells
   (`eq(cell, P₀)` as a 23-term product, `Σ κ′^(k+2)·eq`);
6. `Ŵ₀`, with the node terms through `keep isNode`;
7. the four level steps (`eqTable(κ_c)`, `tensorW` per query, `accOps`, `û`);
8. `final̂(sf)`: `eqTableK(sf)` and 128 products;
9. the padding factor (`keep is32` against `(1 + sf₅)(1 + sf₆)`), the products and the
   `assertEq`.

**The lemmas:**
- **`flag_finPf`**: under `∀ x ∈ pfRefs fi, x < r.size`, `finPf` asks nothing and its flag is
  **`relPf`**. `relPf` is `claimN(Pf) = wV · padV · finHat` in K (`relPf_iff`), where:
  - `wV` is `lvsV` over `lvStepV` from `w0V`;
  - `finHat` is `fhVal`, which `fhVal_eq` shows is `Σ_c final[c]·eq(sf, c)`;
  - the cells' sum is `cellsVal`, which `cellsVal_eq` shows is `Σ_k κ′^(k+2)·eqCellK`.
- **`noAsk_finPf`**: `finPf` asks nothing.

The proof runs 13 blocks, each on the register file the previous block left
(`pureRun_rebase`, `pr_seq`; `ExtA` carries reads forward). Its loop lemmas are `run_ptsOps`,
`run_prodKOps`, `run_cellsOps`, `run_lvOps`/`run_lvsOps` and `run_fhOps`. It also has
`pureRun_len`/`evalOp_outs_len` (a run appends `opsOut` registers) and `lvsV_congr`.

**The dump** (`logs/S-G/dump/`):
- **Tool.** `logs/fr-build-SG/dump/IRDumpSG.lean` with `fins := sfFinals finP finPf`; regenerate
  with `logs/fr-build-SG/redump.sh`; log in `logs/S-G/redump-S-G1d.log`.
- **`summary.txt`:** ops 105,700; registers 53,164; asks = items = 8,874; `piSize` 755,680.
- **Sections.** `ops-{L,P,N,M}.txt` are 105,713 lines each. **No section is PENDING.**
  `finPf` is 4,163 ops; `finRS` is now S-F's 4,119.
- **sha256:** `ops-L` `d9652595…`, `ops-P` `b6f59935…`, `ops-N` `8f882cef…`, `ops-M` `9bfbf2d8…`.

## 2. The Ligerito truths (item 2, partial; `FRSoundnessTruths` Part D)

The layout is the native prover's:
- level `i`'s row `r` holds the message coefficients `c ↦ f[c·rows + r]` (novel basis,
  `ntt.rs::encode`);
- the next level's F vector is `split` of the folded K message. K element `x` sits in rows
  `2(x mod 8) + b`, column `x div 8`.

| Definition | Meaning |
|---|---|
| `sAt`, `foldAt` | P1.i's challenges; the column fold `y_j = Σ_r eq(sᵢ, r)·W⁽ⁱ⁾[r][j]` |
| `mLog`, `msgOf`, `fTab`, `foldMsg` | `log₂ kᵢ`; row `r`'s decoded message (`coeffsOfValuesD` of `decodeL`); `f⁽ⁱ⁾` as a table; `fold_z(f⁽ⁱ⁾)` |
| `nextMsg`, `finalAt`, `encAt` | `f⁽ⁱ⁺¹⁾` as level `i`'s folded message (`i < 4`: from level `i + 1`'s rows; `i = 4`: the final message); `Enc_{kᵢ}` (`encF`) |
| **`consSet`** (`A_c`), **`truthP2`** | the positions where `y_j = Enc(f⁽ⁱ⁺¹⁾)[j]`; `|A_c| ≥ nᵢ − eᵢ` |
| `consSet_card_of_not` | `¬ truthP2 → |A_c| + eᵢ < nᵢ`, which is `p2_hround`'s hypothesis |
| **`truthC`** | `f⁽ⁱ⁺¹⁾ = fold_z(f⁽ⁱ⁾)` on the `kᵢ` coordinates |
| `kcAt`, `qPos`, `consErr`, **`truthP3`**, `p3Batch` | `κ_c`; the queried positions; `y_q − Enc[p_q]`; all errors zero; the batched `Σ_q eq(κ_c, bits₉(q))·err_q` |
| **`truthP1`**, **`truthPf`** | in the level's weight table `W` (a parameter): `¬ far_i → c = ⟨W, f⁽ⁱ⁾⟩`; `c = ⟨W, final⟩` |

Controls:
- `foldAt_nil`;
- `not_truthP3_of` with `lvl_t_pos` (`truthP3` is refuted by one error);
- `mLog_eq`: the message logs `19, 16, 13, 10, 7` and `17, 14, 11, 8, 5`, with
  `2^mLog = lvK`.

## 3. The coordinate row (item 4, partial; new module `FRSoundnessStepD`, 43 code lines)

- **`card_coords_in`**: the answer tuples whose coordinates (`chFEquiv` per answer) lie in
  `B ⊆ (F × F)^r` number exactly `|B|`. This is `Equiv.piCongrRight chFEquiv`.
- **`coords_round_le`**: if a multi-squeeze phase's escape puts its coordinate tuple in `B`, its
  conditional count from the entry is at most `|B| / 2^(256r)`. `coords_prob` restates this as
  `|B| / |F × F|^r`.

This is the F-coordinate analogue of `card_pos_in`/`p2_round_le` that Z1, S1, Lr1, RS1, E1 and
P3 need. Controls: `card_coords_univ` (the full set counts `2^(256r)`) and `card_coords_empty`.

## 4. Deviations, open points, and what remains

**Deviations and open points:**
1. **The Lr claim point (node only) is provisional.**
   - `lrSrc` is Lr4's challenges `7 … 14`, then `lrHi`: the 15 bits of `Lbase·128/2^8 = 23,168`
     (`lrHi_eq`).
   - A.8 says only "Lr: its point". `finLr` passes Lr4's 15 challenges as `evalL`'s `σ`, but A.8
     types that `σ` as `AF 23`. `finRS` reads Lr4's first 7 challenges as the bit coordinates.
   - The native verifier has no node.
   - S-F or L-circ must fix the point (A.8). `finPf` changes only in `lrSrc`.
2. **The cells.** `finPf` claims the nine cells of `finB′`'s `pubH`:
   - `pfCells_spec`: nine distinct cells, the first M's `one` cell;
   - the formula is `Node.seedCell`'s.

   The six zero padding cells of A.7 and S-E2's `PubCells pad` are claimed by neither `finB′`
   nor `finPf`, so the two sides stay consistent. If the padding cells must be pinned, both
   fields gain the same six terms (owners S-F and S-G).
3. **Points by kind.**
   - `keep is32` selects the `m = 32` or `m = 30` point, and `rsWeight`'s `pts` is a
     kind-dependent register list.
   - Every point is built from register-level coordinates.
   - The row cost of this, the `mulKF` per F coordinate and the `addK` copies, is not
     measured.
4. **The finals budget is exceeded.** A.9 allots S-G 400 lines; `FRVIRFinalsSG` is now 1,526
   code lines, of which `finPf`'s run proof is about 900. A golf pass could shorten it, for
   example with one generic straight-line block lemma.
5. **`truthP2`'s doom differs from A.10's form.**
   - It is phrased as `¬ (|A_c| ≥ nᵢ − eᵢ)`, and the P2 doom is `¬ truthP2 ∧` every index in
     `A_c`. A.10 has `(far_i ∨ f⁽ⁱ⁺¹⁾ ≠ fold(f⁽ⁱ⁾)) ∧ …`.
   - The count is then direct (`consSet_card_of_not` with `p2_hround`).
   - The far case stays with P1's line doom (`fold_preserves` off `lineBad`).
   - A.10's form follows from it with a uniqueness lemma that is not proved yet: `¬ far_i`
     and `truthP2 i` give `truthC i`, by `fold_lift`, `decodeL_spec`, `coeffs_unique` and
     `rs_eq_of_agree` with `2e + k ≤ n`.
6. `FRSoundnessTruths` now imports `FRRSEval` (`coeffsOfValuesD`, `encF`).

**Not done, in order:**
- **Item 2, the rest:**
  - the uniqueness lemma above;
  - `W_i` as tables for `truthP1`: level 0's from `rsWeight`'s spec, `evalM`'s matrices and the
    cells; later levels by fold plus tensor;
  - `lvsV`'s relation to those tables;
  - the PIOP truths (Z, L, S, Lr, RS, E, B′), which still need the other tracks' definitions
    (S-G1c part 1 §4.1).
- **Item 3:** the per-phase dooms and `Dp` over `phStart`.
- **Item 4:** the per-phase bad sets with their Schwartz–Zippel counts, fed to
  `coords_round_le`.
- **Item 5:** the instantiated `KState.step`.

## 5. Times (sequential, one core: `taskset -c 0 lean -DElab.async=false --profile`)

| Module | Wall (≈ 3.6 s import) | Elaboration | Type checking | Max RSS | Log |
|---|---|---|---|---|---|
| `FRVIRFinalsSG` | 89.6 s | 37 s (`flag_finPf` ≈ 28 s) | 5.08 s | 3.37 GB | `logs/S-G/profile-FRVIRFinalsSG-S-G1d.log` |
| `FRSoundnessTruths` | 8.3 s | 0.20 s | 0.33 s | 2.66 GB | `logs/S-G/profile-FRSoundnessTruths-S-G1d.log` |
| `FRSoundnessStepD` | 6.8 s | 0.04 s | 0.04 s | 2.65 GB | `logs/S-G/profile-FRSoundnessStepD-S-G1d.log` |

No `decide` or `simp` runs over a program or a table. The `decide`s are on lists of at most
15 small numbers or K constants (`pfCells_spec`, `lrHi_eq`, `mLog_eq`).

## 6. Questions for the orchestrator

1. **The Lr point.** Which point is it (§4 item 1)? It affects the node's `finPf`, `finRS` and
   `finLr`.
2. **The padding cells.** Do they stay unclaimed, or are they pinned (§4 item 2)?
3. **The P2 doom.** Is `truthP2`'s phrasing acceptable for A.10 (§4 item 5)?

---

# S-G1e: uniqueness, the weight tables, Hide, the per-phase dooms, the bad sets, `KState.step`

Base: HEAD `3aaa778`, built against HEAD's versions of other tracks' modules
(`logs/fr-build-SG/snap.sh`, with the worktree's `FR.lean`). **Status:** item 1 resolved without
the edit (§1: the padding cells do not exist); items 2–5 built in generic form, with the PIOP
truths and the per-phase handoffs still parametric (§6). `FR` builds as a whole
(`logs/S-G/build-FR-S-G1e.log`, 2,280 jobs). No sorry, no warning in S-G's modules, no line over
100 characters. Axioms: `propext`, `Classical.choice`, `Quot.sound` only
(`logs/S-G/axioms-S-G1e.log`). Source rule: 77 files, 1 finding, in `FRVIRTemplates.lean:74`
("partial"), which is another track's new, uncommitted module. S-G's files have none.

## 1. Item 1: the six padding cells. Not pinned, because they do not exist

- The node's hashed stream is `streamBytes = 1,437,760` bytes (`FRTranscriptDefs.streamBytes_eq`).
  That is exactly `64 · 22,465 = 64 · chainN`, so each chain's last block is **full** and has no
  padding bytes. `Stream.Padded w L` quantifies over `L ≤ p < 64·nBlocks L`, which is empty here.
- **`stream_padded`** (`FRSoundnessTruths` Part E) proves `Padded w streamBytes` for **every**
  assignment `w`. `stream_sound`'s padding hypothesis therefore needs no point claim.
- The "three padding cells per chain" date from the old 1,440,336-byte stream, whose last block
  held 16 bytes (S-E1 review). Pinning six cells to `0` now would pin six **trace cells** of the
  chains' last blocks (bytes of the last item's query and answer). The honest prover would then
  fail `finB′`/`finPf` (a completeness break), so I made **no change** to `finB′` (S-F) or `finPf`.
- Needed elsewhere:
  - A.7 and §4.3 should drop the padding cells (`J_f ≤ 15`, not 21);
  - S-E2's `pubVals` should drop `List.replicate 6 0`. As written, `PubCells w vk c₁ c₂ pad` is
    **false** unless `pad` has exactly six cells, because the two lists' lengths must match.
    `node_sound` uses only `PubCells.one`;
  - with the padding cells dropped, `finB′` and `finPf` already agree (nine cells each, S-G1d §4
    item 2), and no dump changes.

## 2. What was built (code lines from `loc.py`)

| File | Code (total) | Added in S-G1e |
|---|---|---|
| `FRSoundnessTruths.lean` | 419 | Parts E, F, G (below); `import FRBlockStream` |
| `FRSoundnessStepE.lean` (new) | 493 | Parts A–E and the controls (below) |
| `FR.lean` | +1 | `import FRSoundnessStepE` |
| `logs/fr-build-SG/snap.sh` | — | `FRSoundnessStepE` added to `MINE` |

**`FRSoundnessTruths`**
- **Part E: uniqueness.**
  - **`truthC_of`**: `i < 5 → ¬ farL κ L es i → truthP2 κ L es i → truthC κ L es i`.
  - The proof:
    - decoded rows are `Enc` of messages (`exists_msg`), and `msgOf` recovers them
      (`msgOf_eq`, by `coeffs_unique`);
    - the fold of the decoded rows and `Enc(nextMsg)` are codewords that agree with the column
      fold on `jointAgree`, resp. on `A_c`;
    - these two sets meet in `≥ nᵢ − 2eᵢ ≥ kᵢ` positions (`card_inter_ge`, `lv_params`), so the
      codewords are equal (`rs_eq_of_agree`);
    - `enc_injective` then gives the messages.
  - Also in Part E: `stream_padded` (§1).
- **Part F: the weight tables.**
  - `gW κ i p x = X_x(D[p])` (`encAt_eq_sum`: `Enc(m)[p] = Σ_x m_x·G_p(x)`; its MLE is `tensorW p`).
  - **`wNext`** is P3.i's table `Wf + Σ_q eq(κ_c, bits₉(q))·G_{p_q}`, and `vNext` is the batched
    claim `c + Σ_q eq(κ_c, q)·y_q`.
  - **`vNext_eq`**: from `c = ⟨Wf, fold_z(f⁽ⁱ⁾)⟩`, `truthC` and `truthP3`, we get
    `v_{i+1} = ⟨wNext Wf, f⁽ⁱ⁺¹⁾⟩`.
  - **`wSplit W y = W(y/2)·(1 or u)`** is the coordinate split (its MLE in the split bit is A.9's
    `û(β)`). **`wSplit_sum`**: `⟨wSplit W, fTab (i+1)⟩` over level `i + 1`'s
    `4 + mLog` variables equals `⟨W, nextMsg⟩` (`lv_next`: 16 rows, `mLog` drops by 3).
  - So `W_{i+1} = wSplit (wNext (W_i bound at sᵢ))`, and `truthP1 (i+1)` follows from `truthP1 i`
    through the P1 rounds, C.i and P3.i.
  - Level 0's table stays a parameter (see §6).
- **Part G: hidden disagreement** (the coordinator's addition, §10 changes 14).
  - **`hideL`** (`Hide_i`): some `j ∉ jointAgree` with `Σ_r eq(sᵢ, r)·(W⁽ⁱ⁾[r][j] − V[r][j]) = 0`.
  - **`consSet_eq_jointAgree`**: `¬ far_i ∧ truthC i ∧ ¬ Hide_i → A_c = jointAgree`. This is the
    fact `final` hands the extractor (S-H2 Part 11 Q2).
  - `card_not_jointAgree`: at most `eᵢ` positions lie outside `jointAgree`.
  - **`hide_round_le`**: per round, at most `|P|` challenge values make one of `|P|` nonzero
    difference tables vanish (`zerocheck_bad_le` over K, union bound). Over `ℓᵢ` rounds this is
    `eᵢℓᵢ/|K|`.
  - `hide_fits`: `2 + eᵢ ≤ 2^20` at every level, which is inside P1's `N ≤ 2^66`.

**`FRSoundnessStepE`**
- **Part A: the multi-squeeze bad sets** (item 4).
  - `pairsEquiv`: `(F×F)^r ≃ F^{2r}`, pair `s` coordinate `c` at `2s + c`, as `coordAt`.
  - **`flat_round_le`**: escapes that put the `2r` coordinates in `W` are charged
    `|W|/2^(256r)`.
  - **`seq_round_le`**: from `seq_bad_le`, a coordinate-list doom that loses `b i` values at
    coordinate `i` is charged `Σ b/2^128`.
  - **`mlDoom`/`mlDoom_step`/`ml_round_le`**: the multilinear zero test (`bindL`, `tbl_bind0`,
    `zerocheck_bad_le`) is charged `n/2^128` for `n ≤ 2r` variables. This covers Z1, Lr1, E1 and P3.
  - **`rs1_round_le`**: RS1's `(r″, κ)` (coordinates `0…6`, `7`) in a set of `c·|F|^7`, which is
    `rs1_joint`'s form, is charged `c/2^128`.
  - `coord_le_deltaR` (`c ≤ 239 → c/2^128 ≤ deltaR`) and `coord_rows_le` (A.10's counts 20, 33,
    15, 10, 21, 9).
- **Part B: the phase map** (item 3).
  - **`phOf p`** is the last phase that starts at or before `p` (a `Q` phase is never returned).
  - **`Dp Dk p := Dk (phOf p)`**.
  - The facts:
    - `phOf_start` (checked: every phase with FS items is its first position's phase);
    - `phOf_succ` (generic: the phase changes only at a phase start);
    - `ms_check`/`ms_phOf` (checked: each `fsRanges` phase is one phase starting at `s0 + 1`,
      with `r ≥ 2`).
- **Part C: multi-squeeze dooms.**
  - **`msD prev fin s0 r`**: inside the phase, the entry's doom at the entry; at the last
    answer, `fin`. `MsForm Dk` requires this form for all 15 phases.
  - **`hmid_of_msForm`** discharges `hmid` at **every** multi-squeeze position.
  - **`esc_msD`**: an escape means "the entry is doomed and `fin` fails". This feeds every
    `hround` row.
- **Part D: the whole transcript** (item 5).
  - **`PhaseObl Rej Dk N`** holds what is left per phase: `habs` (inside a phase and the
    handoffs at a phase's first absorb), `hsingle`, `hfin` (each multi-squeeze phase's charge
    `≤ deltaR`) and `hstab`.
  - **`kstate_step`**: from `N ≤ 2^256·deltaR` and `PhaseObl`, the contract's `KState.step` law
    at `εR` holds for `muG (DC Rej (Dp Dk)) (pRoundG … fsRnd)`. The proof is `stepObl_compose`
    plus `step_epsR`.
  - `hfin_ml`, `hfin_seq`, `hfin_rs1` and `hfin_p2` discharge `PhaseObl.hfin` per phase shape
    from Part A and `p2_hround`.
- **Part E: the asserted rounds.**
  - **`D2`**, over a field `R` with a coefficient reader `rd`, width `wd` and challenge map `ch`
    (F: L2, S2, Lr4; K: P1.i, Pf). It mirrors `D3`, but the check is `Chk2`, which `Rej` must
    supply.
  - `D2_append_iff`: absorbs inside the phase.
  - **`D2_single`**: at most `2·M` escaping answers, with `M` from the fiber count
    (`card_chF_fiber`: `2^128`; `card_chK_fiber`: 1).

## 3. Controls

| Control | Shows |
|---|---|
| `phOf_examples` | `phOf 12 = 3` (Z1's last), `13 = 4` (Z2), `339 = 29` (P3.0, not Q.0), `450 = 50` (Pf) |
| `msD_inside_last` | `msD` is the entry's doom inside the phase and `fin` at the last answer |
| `mlDoom_nil` / `not_mlDoom_zero` | a nonzero table is doomed, and the zero table never is |
| `phaseObl_false` | `PhaseObl` is satisfiable (empty doom, `N = 0`): the structure is not contradictory |
| `D2_first_absorb` / `not_D2_before` | a false initial claim dooms the asserted rounds at their first absorb; nothing is doomed before |
| `not_hideL_of_univ` | with full agreement, nothing can hide |
| `coord_rows_le`, `hide_fits` | A.10's coordinate counts fit `deltaR`, and the hiding count fits P1's budget |

## 4. Times (sequential, one core: `taskset -c 0 lean -DElab.async=false --profile`)

| Module | Wall (≈ 3.8 s import) | Type checking | Max RSS | Log |
|---|---|---|---|---|
| `FRSoundnessTruths` | 11.8 s | 0.95 s | 2.70 GB | `logs/S-G/profile-FRSoundnessTruths-S-G1e.log` |
| `FRSoundnessStepE` | 15.5 s | 4.6 s (`phOf_start`, `ms_check`, `phOf_examples`: `decide +kernel` on the 51 phase starts and the 15 ranges) | 2.87 GB | `logs/S-G/profile-FRSoundnessStepE-S-G1e.log` |

A first version checked `phOf (p + 1) = phOf p` at all 450 positions by `decide +kernel`, which
cost 10.8 s of kernel time. The generic `phOf_succ` replaced it. No `decide` or `simp` runs over a
program, layout or table.

## 5. Deviations

1. **Item 1 not applied**, for the reason in §1.
2. **The degree-2 rounds are a new generic `D2`**, not a refactor of `D3`: `D3` (Z3, Lr2, E2) is
   unchanged. `D2` takes the check from `Rej` (`Chk2`, stated as `g(0) + g(1) = claim`; with the
   asserted `c₁ + c₂ = claim` this is characteristic two).
3. **`PhaseObl.hstab` is per phase index**: every `Dk k` must be stable on the chain-prefix
   extensions, for every `k`. This is slightly stronger than "the phase of the extension's
   length", and simpler to supply.
4. **P1.i's proximity/cancellation doom and `Hide_i` are not yet in a `Dk`** (§6 item 2). The
   counting lemmas are built (`hide_round_le`, the earlier `round_bad_cover`).

## 6. Not done, and questions

1. **The concrete `Dk`, `Rej` and the handoffs.** These need:
   - the PIOP truths over `z = unpack f⁽⁰⁾`: Z (`A₀^κ`, `E`), L, S, Lr, RS, E and B′. They need
     the F-valued level-0 message (an `interp_F_D` projection of `decodeL` 0), `unpack`
     (`FRFormat`), and other tracks' layouts (S-G1c part 1 §4.1). Each is a definition plus one
     handoff lemma (`PhaseObl.habs` at its first absorb, or `hsingle` at its first squeeze);
   - level 0's weight table `W₀` from `rsWeight`, `evalM(r_{E2}, ·)` and the nine cells, and its
     relation to `finPf`'s `lvsV` (S-G2, `ligerito_final`).

   The step law needs nothing more than `PhaseObl`. Every multi-squeeze charge has its wrapper
   (`hfin_*`), and the rounds have `D3_single`/`D2_single`.
2. **Where does `Hide_i` sit in the potential? (question.)**
   - `final` needs `¬ Hide_i` on accepted, non-escaped chains. With one doom `D`, `final` derives
     the truths backwards from `¬ D` at the end, so a Hide component must make Hide an **escape**:
     doomed before the hiding challenge, not doomed after.
   - The natural component, "every disagreeing position's partially bound difference is still
     nonzero", is **true** in the benign close-but-not-codeword case. `habs` would carry it to the
     chain's end, where acceptance cannot refute it.
   - Two ways out:
     - (a) a second potential, `μ_H` for the Hide component alone, frozen after P1.i. Its per-query error
       `max_i eᵢ/|K| ≤ 2^18/2^256 = 2^-238` would **add** to `εR`, which is negligible but
       still a change to the claimed error;
     - (b) a P1.i doom that combines Hide with the claim's truth, so that a non-escaped end
       refutes it.
   - (b) needs a blueprint statement of what is doomed. Please rule on it.
3. **A.7/§4.3 and S-E2's `pubVals`**: drop the padding cells (§1).
4. **Golf.** `FRVIRFinalsSG` is still 1,526 code lines (budget 400). Not touched here.

---

# S-G1f: handover (context long). After the rulings of §10 changes 15

Base `94ab897` (S-G1e committed). **Status:** one lemma added; the rest is handed over.

## 1. Built

`FRSoundnessStepE` gains **`step_add`**: two step laws, with errors `ε₁` and `ε₂`, give the step
law of `μ₁ + μ₂` with error `ε₁ + ε₂` wherever `μ₁ + μ₂ < 1`. This is the combinator for
`μ = μ_doom + μ_Hide`. It builds, and so does `FRSoundnessStepE` (`lake build`, 16G scope). It
takes no hypothesis beyond the two step laws, so its axioms are those of `Finset.sum_add_distrib`
and `ring`.

## 2. Next, in order (for a fresh invocation)

1. **`μ_Hide` and the combined KState** (ruling Q1, option (a)).
   - **The budget.** `kstate_step` spends all of `εR`: `deltaR = εR − 2^-142`, and the H row
     takes `2^-142`. The sum therefore needs slack.
     - Re-run `stepObl_compose` at `δ' = deltaR − ε_H`.
     - Every row still fits. The largest is P2, `2^-120.36` against `deltaR ≈ 2^-120.09`, so
       `p2_row_le_q` needs only its right-hand side lowered by `ε_H`. The coordinate rows are
       `≤ 33/2^128`.
     - The single-squeeze `N`s are `≤ 126·2^128` (Z2) and `≤ 2^66` (P1).
   - **`μ_Hide`.** Use `muG` with the doom `DH L es := ¬ hideSoFar`, with Hide's charge at P1.i's
     squeezes.
     - Per round: `hide_round_le` (`≤ eᵢ` K values, so `N = eᵢ ≤ 2^18`, `hide_fits`), through
       `D2`-style plumbing with `card_chK_fiber`.
     - Frozen after P1.i: `DH` is constant outside the P1 rounds, so `habs`, `hmid` and `hround`
       are trivial there.
     - Its `muG` also charges `Bad` (another `2^-142`).
   - **The total.** `ε_doom' + ε_H ≤ εR` with
     `ε_doom' = 2^-142 + δ'` and `ε_H = 2^-142 + 2^18/2^256`. This is a kernel-checkable `ℝ≥0`
     inequality, like `err_le_epsR`. Then apply `step_add`.
   - **What `final` gets.** `μ_doom + μ_Hide < 1` gives `muG_lt_one` for both, so no Hide escape,
     hence `¬ hideL` at each level, hence `A_c = jointAgree` (`consSet_eq_jointAgree`).
2. **The PIOP truths.**
   - The F-valued level-0 message: project `fTab κ L es 0` through `K → F`.
     - `interp_F_D` (`FRProximityFold`) gives that the decoded rows of an F-word close to the
       code are F-codewords, so the projection loses nothing.
   - Then `z = unpack f⁽⁰⁾` (`FRFormat`).
   - Then the truths, as A.10's table:
     - Z: `FRSpartan` (`bz_trueSum`), `A₀^κ` (`FRBlockLayout`), `E` (`FRPubTarget`),
       `FRSkip.z2Vals`;
     - L: `lin_trueSum_kinds`;
     - S: `shift_sound`, `slotW_mle`;
     - Lr: `FRVIREval.evalL`;
     - RS: `rsT`/`rsTruth`;
     - E: `evalM`;
     - B′: the nine cells, no padding.
3. **Level 0's weight table `W₀`.**
   - It has `rsWeight`'s spec (`weightEval`, S-C), `evalM(r_{E2}, ·)` and the nine cells
     `eq(cell_k, ·)`.
   - Relate it to `finPf`'s `lvsV`/`w0V` (`FRVIRFinalsSG`) through `vNext_eq` and `wSplit_sum`.
4. **The concrete `Dk` and `Rej`, and `PhaseObl`.**
   - `Dk` per phase:
     - `D3` for Z3, Lr2 and E2;
     - `D2` (F) for L2, S2 and Lr4;
     - `D2` (K) for P1.i and Pf, plus the far/cancellation doom (`round_bad_cover`);
     - `msD` with `fin` for the 15 multi-squeeze phases;
     - the single-squeeze `Wrong` dooms for L1, L3β, Lr3, E3 and B′;
     - the absorb phases.
   - `Rej`: the finals' and the rounds' asserts (`Chk2`).
   - The handoffs: one lemma per phase start.
   - `hfin` comes from `hfin_ml` (Z1, Lr1, E1, P3), `hfin_seq` (S1), `hfin_rs1` (RS1) and
     `hfin_p2` (P2; `S = consSet`, `consSet_card_of_not`).
5. **`kstate vk`** (S-G2, `FRKState`).
   - `empty`: `muG_empty`.
   - `step`: item 1.
   - `cert`.
   - `final`: `ligerito_final`, then `leaf_sound`/`node_sound`; with `capPi = capDig` and the
     `V_W` size, per the rulings since revision 3.10.

The PIOP truths (item 2) need other tracks' definitions at their current HEAD. Check that
`FRFormat.unpack` and the S-E3 `pubVals` fix have landed before starting.
