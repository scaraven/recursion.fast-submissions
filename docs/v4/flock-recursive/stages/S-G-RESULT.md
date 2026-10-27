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
