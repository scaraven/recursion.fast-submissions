# S-G6 JOURNAL: the PIOP front, continued from S-G5's handover

Base HEAD `d332644`. Build tree `logs/fr-build-SG6` (copied from `fr-build-SG5`, `.lake` reused;
`snap.sh` takes HEAD's sources and symlinks `FRSoundnessFr*` to the worktree). Logs in
`logs/S-G6/`. Every lean/lake command runs in the 16G scope with a `timeout`. Nothing committed.

Orchestrator rulings: `DF 2 := far₀ ∨ ¬ Stmt` approved (`ExtIface : ¬ far₀ ∧ Stmt ∧ LigeritoOut
⇒ witness`, a named `Prop`); the RS claims have no message, `RejF` from 313 holds the finals'
slice equations, RS0's `habs` is `rs_column` (+ `ml_claim_split` upstream).

## Log

### Item 1: RS0 and `RejF`'s slice part (`FRSoundnessFrRS0`, new)

- Design: a claim's *binding* is a predicate `ok κ es j v` (the final that uses claim `j` accepts
  `v`), read before 312 (`OkReads`). `PendBad ok` (some binding fails at the true value
  `trueL`), `DPend ok = far₀ ∨ ¬PubOK ∨ PendBad ok` (E4 end's doom), `RejRS ok` (from 313: some
  binding fails at the slices' value `alphaL`). `habs_RS0`: `DPend` at 312 ⇒ `RejRS ∨ DRS0`
  after the absorb (`rs_column`). The bindings are a parameter: the concrete `ok` is
  `finLc`'s `v = v_β`, `finSh`'s `c_Sh = (w_out + w_in)·v`, `finE`'s `v = E4 end's value`, and
  `finZ`'s `v = P^z*(λ)` (see the finding below).
- `cwL` is factored through a value-level `cwF` (`cwL κ es = cwF (λ) (xLL es) (xSL κ es)`): a
  `match`-level `funext`/`rcases` proof of `cwL_congr` hit a **kernel** deterministic timeout
  (124 s); the factored `rw` proof is instant.
- **Finding (blocking for Z; verifier, not this track).** The blueprint (A.9's `finZ` row, line
  1126 and the "Claim values" ratification, line 1512) says `finZ` binds `α_Z = P^z*(λ)`. The
  implemented `finZ` (`FRVIRFinals.lean:140`) has no such `assertEq`: its ops end with
  `assertEq (b + 13) (claimN fi "Z3")` (the `eq·â·b̂ = c_Z` check), and its third export
  `(outsOf fi "Z2").getD 2 0` (`P^z*(λ)`) is read by no later field (`Finals.ops` passes the
  exports in `ex`; only `lrEx` reads `ex`, at index 4). `fi.zhat.getD 0 0` (`α_Z`) is read by no
  field. So on an accepted run nothing relates RS claim 1's slices to Z2's message: the Z
  c-claim is unchecked, and the Z sub-protocol's pending claim cannot reach RS0's doom. Needed:
  `finZ` gains `.assertEq ((outsOf fi "Z2").getD 2 0) (fi.zhat.getD 0 0) allK` (S-F / S-0's
  module; re-run `flag_finZ`, `exec_finZ`, the dumps and `piSize`-independent controls).
- `FRSoundnessFrRS0` green (2,304 jobs).

### Item 2: E (`FRSoundnessFrE`, new)

- Outer half: `FRSoundnessRows`' unit as is at `s0 = 209`, `b2 = 221`, `a = 21`, `nc = 23`,
  `lrOn` (`e_zc_hfin`, `e_habs_outer`, `e_single_outer`, `e_habs_end`, `e_rejEnd_ok`);
  `e_unit_pos` (positions, by `fsStarts_eq`, no `decide` over the item list).
- Inner half new (the unit's is three-claim): `c4E = c4 21 221 + κ_E³·c4 15 178` (finE (iii)),
  `wE4 = wInn(M, κ_E) + κ_E³·wInn(L, κ_L)`, `T4E = [wE4, z]`, `trueSum_T4E`; `BatBadE`; `D4E`
  (guarded by `lrOn`: on a leaf `D2`'s claim is the end message's batch, which no doom
  produces); `RejInE`. **E3 is four claims** (`â_M, b̂_M, ĉ_M, v_L`, degree 3 in `κ_E`), not six:
  `κ_L` is fixed at Lr3, so Lr's three claims enter as one (`v_L`). The pending Lr doom is Lr's
  `BatBad` (`v_L` false). `single_batchE`: `3·2^128` (`batch_count4`), below §5's row.
- E4 end: `okE es v := v = E4 end's value` (`finE` (v)); `RejE4` (`finE` (iv) on the log:
  the last claim is not `W(r′)·α_E`); `PendE` (E4 end's value is not `ẑ(r′)`); `habs_E4end`.
- **Lessons (OOM).** The first build was killed by the 16G scope. Bisected with scratch copies
  under `lake env lean` (8–12G caps): (1) `simp only [Matrix.cons_val_*]` on `![…] k` uses
  `rfl`-lemmas as casts; using the result against a concrete `trueSum … 23` made the **kernel**
  lazy-unfold `trueSum` over `2^23` cells. Fix: `batch_count4`, the vector algebra over abstract
  values. (2) the same for full `simp [innerExpr, Expr.eval, …]` on `#[a, b].getD i`: replaced by
  generic `rfl` lemmas (`innerExpr_eval2`, `arrGetD_pair0/1`, `rE4_def`) used by `rw`. (3)
  `refine card_le_card fun d hd => …` with a term-mode `mem_filter` and Mathlib's
  `monotone_filter_right` hit max recursion on `Finset Digest`; `card_filter_imp` (instances as
  implicit arguments, unified, not synthesized; proof by `simp only [mem_filter]`) works.
- `FRSoundnessFrE` green (2,305 jobs).
- Lr (item 3, assembly only): `lr_habs_outer`, `lr_single_outer`, `lr_habs_end` added to
  `FRSoundnessFrE` (the unit at `lRows`, `s0 = 169`, `b2 = 178`; with S-G1j's `lr_zc_hfin`,
  `lr_single_batch`, `lr_rejEnd_ok` that is every Lr obligation; Lr's `BatBad` is pending into
  E3, where `single_batchE` consumes it).

### Ruling 1: `ExtIface` (`FRSoundnessFrExt`, new)

- `StmtN fin κ` (node: `truthZN ∧ truthS1N ∧ truthLr ∧ truthE fin ∧ PubOK`); `Stmt fin SL`
  (by kind; the leaf part `SL` is a parameter: the leaf's S/chain truths are not stated on the
  log yet); `stmt_reads` (`Reads 3`, from `fF_same`).
- `ExtIface S vk W₀ c₀ St`: accepted run, `IsChain L j`, past Pf, `¬ far₀`, `St`, `LigeritoOut`
  ⇒ witness. `¬ far₀` is also `LigeritoOut.close 0`; kept to match the ruling's wording.
- `hExt_of_iface`: `ExtIface` + `Reads 3 St` + `DF 2 = far₀ ∨ ¬ St` ⇒ `finalLaw_of`'s `hExt`
  (prefix of length 3, `phOf_two`, `DkC_lt`, `same_append` on `take 3 ++ drop 3`). Green first
  time.

### E4 end → RS0 (`FRSoundnessFrPend`, new)

- `okRS oZ oSh` (the concrete bindings: Lc `v = v_β` (`vBetaL`), E `okE`; Z and Sh parameters),
  `okRS_reads`. `trueL_three`: on a node RS claim 4's true value is `ẑ(r′)` (`pack_unpack`,
  `eqPts_eq`, `ptOf_bitsL`; sums moved to `range` to cross `Fin (2^nrP 0 κ)` vs `Fin (2^23)`).
  `pendE_pendBad`: E's pending doom (`habs_E4end`'s output) is RS0's `PendBad` at claim 4. So the
  chain E2 → Eend → E3 → E4 → E4 end → RS0 → RS1 → B′ → P1.0 is closed on the log, except for
  the Z and Sh bindings and the background terms.
- Checks: axioms over all 74 new theorems (`logs/S-G6/axioms.log`: 65 use the three, 4
  `[propext, Quot.sound]`, 2 `[propext]`, 3 none); source rule 156 files, 0 findings
  (`logs/S-G6/source-rule.log`); sequential profiles `logs/S-G6/time-*.log`; no new name clashes
  (declaration-head grep over every `FR*.lean`).
- **Stopped here (context).** RESULT §5 is the handover.
