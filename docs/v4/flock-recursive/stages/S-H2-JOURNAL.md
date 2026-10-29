# S-H2 journal (track L-ext, second half: the extractor program)

Base: branch `v4/flock-recursive`, HEAD `53c2e13`. Build tree `logs/fr-build-SH2` (copy of
`fr-build/gen.sh`, `.lake` seeded from `fr-build-ext`); every command under the 16G scope.

1. Read TRACK-RULES, BLUEPRINT §1.4, §6, §7, §10 (extractor rows), QUEUE "Notes for S-H2", the
   contract's `Machine.lean`/`Extractor.lean`, `FRXDsl`'s statements, `WitnessSending.computes`.
2. Fuel: `claim.json` declares `fuel_base = 2^46`, `fuel_per_word = 2^12`; the blueprint says
   `2^47.5 + 2^12 t` and estimates the decoder at `2^46.52 + 2^11 t`. Used `claim.json`'s figure
   (the harness checks it); flagged (RESULT §6, Q1).
3. Design: the SNARK branch is a parameter `dec` with obligations `DecOk`; `Safe` (an inductive
   predicate) gives `BoundsOk` from every state when each `loopT` follows a prefix that sets its
   count to at most the cap from every state (the S-H1 note "count loaded by `input` right before
   the loop", generalised). `computesWith` is proved once for every `dec`.
4. `FRXProg` built first try after fixing two numeric constants (cost 33 + …, size 65 + …).
5. `FRXComputes`: whnf timeouts (heartbeats) in three places, all from the unifier evaluating the
   **concrete** program on an abstract state:
   * passing `h0 : Inv (entryT …)` where `Inv (⟨entryT …, o⟩ : St).M` is expected: lazy delta
     unfolds `entryT`/`semXIR` instead of the projection — fixed by `generalize` of the memory;
   * `refine ⟨_, ?_⟩` on `BoundsOk I t (extIRWith dec) s0` — fixed with `Iff.rfl` lemmas
     `boundsOk_seq`/`boundsOk_ite` and `rw`;
   * `by_cases hk : rd (semXIR I parseIR s0).M rIsK = 0` ran `runPrims` (diagnostics: 16k
     `List.foldl` unfoldings) — fixed by `generalize hs1 : semXIR I parseIR s0 = s1` first.
   Lesson for S-H3: never let a tactic see `semXIR I <concrete program> s` in a decidable
   proposition; generalise the state.
6. `FRXSpec`: `E_W` (any `W` proof under `2^64` bytes), `E_bad`, `ext_encode`; kernel toy runs
   with a 260-word memory need `piSize_eq` rewritten before `decide +kernel` (else the kernel
   evaluates the phase table).
7. Axioms of `computes`, `ext_encode`, `ext_bad`, `E_W`: `propext, Classical.choice, Quot.sound`;
   toy runs: `propext, Quot.sound`. Source rule: 53 files, 0 findings.
8. Stopped before the decoder (§6.2 steps 2–5) per the conservative-pace instruction; plan in
   the RESULT §7.

## Part 2

9. Coordinator: fuel `3·2^46 + 4096 t` (B-10); `E_W` keeps `π.size < 2^64`. Updated `fuelBase`.
10. Sort cost with cap `t` for a count of log entries: `64 · 186 · t ≈ 11,900 t`, over `4096 t`.
    The cost model cannot express `t / 5` with `Aff = a + b·t`; added a divisor to `Aff`
    (`FRXDsl`, L-ext's own module), controls updated. Sort now `≈ 2,374 t`.
11. `FRXLog`: walk + 64-pass bottom-up merge sort; `wf` by `simp`, `cost_logIR` closed form via
    `norm_num; omega` (values read off a scratch `#eval`), `Safe` via `NoLoopT` +
    `rd_seq_readAt` + `tape_count_le`. `ext` moved to `FRXExt` so that the SNARK branch can come
    after the tape lemmas.
12. `FRXLogSpec`: `tape_entry` (the tape word at an entry's offset is `|q|`), `rd_storeM`,
    `walkBody_sem`, `walkLoop`, `walk_spec`. Pitfalls met: a full `simp` with
    `WitnessSending.size_eq_length` loops (use `simp only`); `toWord x + 1#64` against
    `toWord_add_one` timed out in `whnf` (use `BitVec.ofNat_add`); the unfolded `ceil8` must be
    put back with `change` before arithmetic.
13. Stopped before the sort's semantics (token budget); plan in RESULT Part 2.

## Part 3

14. `FRXSortSpec`: `cmpIR_sem`. Pitfalls: a load's result depends on whether its computed
    address is a register (needs `regs ≤ address` hypotheses); `rfl` between two `XIR` terms
    with different `seq` association fails (rewrite with `semXIR_seq` along the program's own
    right-nested shape instead of regrouping); composition through `generalize` of each
    intermediate state, with `FRXDsl.frame` for the registers a block does not write.
15. Designed the remaining sort proof to avoid permutation tracking (membership + strict
    sortedness + injectivity, then a cardinality argument). Stopped on the token budget.

## Part 4

16. `FRXMerge`: the pure merge machine and its invariant compiled after four rounds. Notes: the
    invariant's run-end clause had to allow the empty initial block (`jE = lo`), and an
    alignment argument at block close distinguishes `jE = lo + 2w` from the empty block; the
    `let` in `mstep` needs `dsimp only` before `by_cases` on `takeL`; `passes_ok` and
    `keyLt_order` compiled first time. Stopped before the register-level simulation (step 2).

## Part 5

17. `FRXSortSim`: `minW` (branch-free min), `eqW_toWord`, `ltW_toWord`; compiled first time.
    Stopped: this agent's context is long; RESULT Part 5 is a handover brief for step 2.

## Part 6

18. `FRXSortSim`: `Rel`/`Regs`/`Lay`/`Lo` + `hframe`; `blockIR_sem`, `choose_sem`, `tail_sem`,
    `stepIR_sem`, `stepLoop`, `passIR_sem`, `sortIR_sem`, `logIR_sorted`. `stepIR` is split as
    `blockIR ; flagsIR ; chooseIR ; advIR ; tailIR` by `rfl`. The step needs no sortedness, only
    `Bnd`, so `passes_ok` is applied unchanged. Pitfalls met:
    - `rfl` or `assumption` time out in `whnf` on `0 = toWord 0` with tape facts in context;
    - a `let`-bound base function makes `rw`'s closing `rfl` time out (use `def baseX`);
    - multi-line `(by …)` needs `;`;
    - implicit arguments must be given before a `by` argument can run.

    Profile: 27.1 s wall, type checking 2.43 s. Stopped before the binary-search lookup (token
    budget); plan in RESULT Part 6.

## Part 7

19. Lookup.
    - `FRXLog`: `lookIR` (64-step lower bound), `foundIR`, `lookCIR` (looks up `c`), and
      `logIR := idxIR ; lookCIR`. The cost constant went from 2,592 to 9,095; `decOk` re-proved.
    - `FRXLookup`: `tape_answer`, `ansW_entry`, `bsRun_spec`, `lookup_pure` (against
      `FRLog.ansIdx`), `lookIR_sem`, `logIR_lookup`.
    - `logIR_sorted` renamed `idxIR_sorted`.
    - Pitfalls:
      - `rw [ansW_eq]` rewrites inside its own result; use a lemma over a 4-element list;
      - `revert; decide` fails when the goal has free variables; use a closed `decide` fact;
      - give implicit arguments before a `by` argument needs them;
      - the toy control needs `decide +kernel`.

    Profile: `FRXLookup` 33.6 s wall, type checking 2.56 s. Stopped before phase 3 (token budget).

## Part 8

20. Per the coordinator, the walks start from π's cap-0 entries, not from `c`. I removed
    `lookCIR`, so `logIR := idxIR` (cost back to 2,592 + ⌊t/5⌋·11,871). `logIR_lookup` becomes
    `idx_lookup`, parametric in the target. `cost lookIR = 6486`. Pitfall: a `set X := fun a =>
    …` does not capture `rd s.M (memX + a)` in hypotheses stated pointwise. Restate them with `X`
    (`hX₂'`) and pass `(X := X)` explicitly. Stopped before phase 3 (context long); handover in
    RESULT Part 8.

## Part 9

21. Phase 3, the ladder read of level 0.
    - `FRXReadDefs`: the program (per-position walk, masked copy), the word facts and the parser
      iffs. `cost_read0 = 18,001,952,782`. `decRead := logIR ; read0` with `DecOk`.
    - `FRXRead`: the semantics, from the blocks up to `read_spec` and `read_spec_F`, plus
      controls.
    - `FRXExt`: `decSnark := decRead`.
    - Pitfalls met:
      - `refine ⟨fun … => by tac1; tac2, …⟩` lets the `by` swallow the rest. Parenthesise:
        `(by tac1; tac2)`.
      - `omega` hit the maximum recursion depth on `sizeIR logIR + … ≤ 2^19`. Use an exact
        size lemma (`sizeIR_logIR_eq = 294`) and `norm_num`.
      - The cost `simp` needs `(toWord (2^18)).toNat = 2^18` as an explicit rewrite before
        `norm_num`, else it hits the maximum recursion depth.
      - `rw [Nat.add_zero]` failed silently on `getD (… + 0)`; `simp only [Nat.add_zero]` works.
      - `rw` of an equation under `decide` fails (motive). Use `decide_eq_decide.mpr` and
        `Bool.decide_and`.
      - A `'(by omega)` inside a `∀ … → …` statement does not see the arrows' hypotheses. Name
        them: `∀ (_ : …)`.
      - `show rd (entryK …) … = _` on `(⟨entryK …, o⟩ : St).M` costs about 1.4 s each (a golf
        candidate).
    - Profile: `FRXRead` 53.1 s wall, type checking 5.2 s. Stopped after phase 3 with the RESULT
      written (Part 9). The open questions are Q1 (`L32`/leaves) and Q2 (the cap link).
22. Phase 5, pure half (`FRXDecodeB`): `bflyLevel`/`bflyRun`, `bflyRun_block` (the block
    invariant against `coeffsAt`, by induction on the level, with the IH applied to blocks `2b`
    and `2b + 1`), `bfly_decode_D`, `firstK`, `decode_agree`. Most of it compiled first time.
    Pitfall: `Finset.sort` does not reduce under `decide`, not even `decide +kernel`. Defining
    `firstK` as a scan of `List.range n` makes it decidable, and it matches the machine's scan.

## Part 10

23. The leaf branch (coordinator's Q1: `s` is in the header, `n = leafN k`).
    - `decLN := kindIR ; ite rKN decRead leafIR` with `DecOk`.
    - `FRXLeaf`: `run_leaf`, `E_leaf`.
    - Pitfalls:
      - `cases hk` on `PKind.snark k = if … then … else …` fails with "dependent elimination".
        Use `by_cases` on the size, then `simp [hs] at hk`.
      - `simp only` turns the `o` conjunct into `True`, so `rfl` no longer fits; use `trivial`.
      - Numerals in the program (`0x4C`) display as `76`. State the byte lemmas with a `Word`
        and a `UInt8` argument and `hvu : v.toNat = u.toNat := rfl`.
      - `rw [E, Eof]` fails on `E`'s equation lemma. Use
        `show (ext.run …).bind decodeWit = _`.
    - Stopped: context long. Items 2–6 are handed over in RESULT Part 10.

## Part 11

24. Items 2–3 of the Part 10 handover (butterflies and the agreement scan on the machine).
    - Upstream drift: HEAD moved to `eba6537` (S-0's `kindOf` now reads `byteAt? π 0`). `FRXSpec`
      and `FRXLeaf` failed to build. Repaired by adding the `@[simp]` lemma `byteAt?_eq` to their
      seven `kindOf` simps; no statement changed.
    - `FRXBflyDefs`: `ldF`/`stF`, `alphaIR`, `pairBody` (= `pairPs ; alphaIR ; arithIR ; stF ;
      stF ; q += 1`), `levelIR`, `bflyIR`, and the table program `wtabIR` (`row0IR`, `rowIR`).
      `divu`/`remu`/`mul` give the pair's positions in one flattened loop per level (a nested
      block × offset loop would be charged `K²` by `loopK`'s constant cap).
    - `FRXBfly`: `iterL_ind`/`loopK_eq` (generic loop invariants), `ldF_sem`, `stF_sem`,
      `alphaIR_sem`, the pure pair lemmas (`pairOf`, `pair_cases`, `bflyLevel_lo/hi`),
      `pairBody_sem`, `levelIR_sem`, **`bflyIR_sem`**, `wtabIR_sem`, **`bflyIR_decode`**.
    - `FRXAgree`: `scanIR`, `scanIR_sem`, `firstK_scan`, `scan_decode`, two kernel toy runs.
    - Pitfalls met:
      - `rfl` between two `seq` associations of the same program does not hold (different
        terms); rewrite both sides with `semXIR_seq` instead (`simp only [semXIR_seq]` at the
        facts, then `generalize` the flattened state).
      - A `have e : semXIR I P s = semXIR I Q (…) := rfl` timed out in `whnf` (the unifier
        evaluates the program); same fix.
      - `generalize … at h` without `⊢` leaves the goal on the old term; the unifier then
        unfolds `iterL` 20 times (maximum recursion).
      - The loop count `(20 : Word).toNat` from `loopK_eq` must be rewritten to `20` before
        `generalize` matches the invariant's state.
      - `rowIR_sem` needs `maxRecDepth 8000` (kernel deep recursion on the 554-statement `invF`
        list inside the program term).
      - `eq_bW` rewrites the outer `eq` first; give its arguments.
      - `show rd (entryK …) x = _` costs ~1.5 s each (29 of them): `dsimp only` does the same
        projection reduction for free (FRXBfly 111 s → 62 s sequential).
    - Profile (sequential, one core): FRXBflyDefs 13.7 s, FRXBfly 62.0 s (type checking 8.9 s),
      FRXAgree 35.7 s (type checking 19.8 s, of which ≈ 18 s the two toy runs).
    - Analysis for items 4–6 (RESULT Part 11 §4): the level-0 agreement set cannot be computed
      from level 0 alone; the fold-consistency set needs the fold challenges (a Fiat–Shamir
      chain replay, absent from §6.2) and a "no hidden disagreement" event (absent from A.10).
      Stopped there: both need the coordinator.

## Part 12

25. Coordinator's answers (stage-review changes 14): `fuel_per_word = 8192`, `Hide_i` in P1's
    doom (`final` supplies `A_c⁽ⁱ⁾ = jointAgree⁽ⁱ⁾`), column values read in place. `FRXProg`'s
    `fuelPerWord := 2^13`; `decOk_decRead`/`decOk_decLN` re-proved by changing their linear
    constant (`2^13 − 16 = 8176`). `computes`, `ext_caps`, `E_leaf` re-check (axioms standard).
    Build `logs/S-H2/build11b.log` (2 min 50 s, rebuilding from `FRXProg` down). Stopped:
    this agent's context is long; items 1–6 of the coordinator's new list handed over in RESULT
    Part 12.

## Part 13

26. Item 1 (the fold challenges).
    - Design change: a query-keyed merge sort cannot be costed (a comparison costs a query's
      length, charged at the loop cap; a bounded-prefix key leaves unbounded group scans). Instead,
      one forward pass over the log's words with the next target in hand (`chainIR`, 176 steps a
      word). It is proved equal to `runLog`'s first-match chain under `¬ StateHit`
      (`scanC_fm`, by `reverseRecOn`).
    - New modules: `FRXChainDefs`, `FRXChain`, `FRXChainSem`, `FRXChainLoop`, `FRXChainTop`,
      `FRXChainFlock`. The fast loop: edit the module, copy it to `logs/fr-build-SH2/scratch/T*.lean`,
      run `lake env lean` (10–20 s, no rebuild), and bisect timeouts by cutting the proof with
      `sorry` (a small script).
    - Pitfalls met:
      - `omega` hits the **maximum recursion depth** on a hypothesis such as `ansB + 2 ^ 11 ≤ size`
        when `ansB` is a def whose body is `2 ^ 23 + 2 ^ 12`. Define layout constants as literals
        (`chB := 8388608`) and keep `2^k` out of the hypotheses omega sees (`chEnd`).
      - `exact lemma _` against `rd (semXIR I (.blk ps) s).M i` timed out in `whnf` for a 5-prim
        `ps` named by a def. Fix: `have e : semXIR I P s = ⟨runPrims ps s.M, s.o⟩ := rfl`, then
        `simp only [e]` (it reduces the projection), then a standalone frame lemma
        (`nextPs_frame`). `set P := …` plus `generalize` over it also timed out.
      - `congr 1` on `bW (… && …) = bW (decide …)` and on `toWord a = toWord b` triggers expensive
        `rfl` attempts (`whnf` timeouts, max recursion). Use `congrArg bW` and `decide_eq_decide`,
        or rewrite with `show a = b by omega`.
      - `split_ifs <;> first | rfl | …` timed out where `rfl` compared `rd M 206` with
        `rd M (203 + (i − b))`. Put the cheap alternatives (`omega`, explicit `rw [show …]`)
        before `rfl`.
      - `if_neg (by …)` with an undetermined condition rewrites the *first* `ite` in the goal and
        leaves a side goal the tactic cannot see. Give the condition: `if_neg (show ¬ … by …)`.
      - Pass implicit arguments before `by` arguments (`st4IR_sem … (b := ansB + 4 * p)`,
        `ansPs_sem (qw := qw) (m := m)`). Otherwise `omega` sees a metavariable and fails or
        recurses.
      - A multi-line `disch := …` or a `simp only […]` broken before `at` inside parentheses does
        not parse. Keep each on one line.
      - `generalize … at h` does not rewrite inside a structure hypothesis's fields (`he.ans`).
        Rewrite the projected fact itself (`rw [hqw] at a0`).
    - Blocked on `vk`: the seed carries `vk` and `E` takes none (V4-6). See RESULT Part 13 Q1 (the
      proposal: `'N'` hdr's `pub := vk`, checked by `V`).
    - Profiles: every new module is under 20 s on one core. `FRXChainFlock`'s type checking is
      12.4 s, of which `fsMsgs_items` (`decide +kernel` over 451 items) is 9.8 s.
    - Stopped with Part 12's items 2–6 untouched: item 1 waits on Q1, and this agent's context is
      long.

## Part 14

27. Seed block, wiring, interpolation, revision 3.12.
    - `FRXSeed`: the 7-byte shift lemma (`packBytes_shift7`), proved through `ofLE_append` /
      `ofLE_take1` / `ofLE_take8_div` and `toWord_shr8` / `toWord_shl56` (`Nat.mul_mod_mul_right`).
      Seed word `j` is `(j = 0 ? tag : S_{j−1} >> 8) + (S_j << 56)`.
    - `FRXDec`: `cntIR` re-associated, because `Safe.loopT` needs `.seq pre (.loopT …)` literally.
      `decSnark := decLN2`.
    - Pitfalls met:
      - **`zeroD` was auto-bound** in `FRXChainFlock`: `FRVIR` is not imported. An unknown
        lower-case name silently becomes an implicit argument.
      - `run_leaf`'s closing `rfl` became a **kernel deep recursion** once `decSnark` contained
        `chTab`: the kernel unfolds `semXIR`'s structural recursion over the whole program. Use
        rewrites (`decSnark, decLN2, semXIR_seq`) instead.
      - The shared name `mul_toWord` (FRXBfly / FRXChainSem) would clash on a joint import.
        Renamed it in the chain module.
      - `rw [← toWord_zero']` rewrote the `0` inside the program literal too. Use
        `p1.trans toWord_zero'.symm`.
      - `congr 1` and `rfl` on `runPrims [a, a'] M = runPrims [a'] (runPrims [a] M)` time out.
        Split the list by `show … = [a] ++ [a'] from rfl` and `runPrims_append` twice.
      - Heartbeats count per declaration, so a timeout may surface at a cheap step.
      - Conditional `simp` lemmas (`bnw_mulF : … → (Writes (mulF d a b) i ↔ False)`) keep `WF`
        and `Writes` goals from unfolding `mulFC`.
    - Revision 3.12 (coordinator's message): every constant in the list, plus
      `capW0_eq`/`tape_cap` (2,795/2,790) and `chTab` 1,888. `FRVIRChain` builds.
    - Profiles: `FRXBary` takes 91 s sequential; the others are under 14 s.
    - Stopped before `sBody_sem` (context long); handover in RESULT Part 14 §8.

## Part 15

28. The interpolation finished; the read made per-level.
    - `FRXBaryTop`: `sBody_sem` compiled almost first time by composing the delivered loop lemmas,
      generalising each intermediate state (`generalize … at … ⊢`). Then `sLoop_sem` (invariant
      over targets, `cell_ne` for output-cell injectivity), `baryIR_sem`, `baryIR_interp`, and
      level 0's layout (`bary0_interp`).
    - `FRXReadDefs`/`FRXRead`: the read is generalised in place. The parameters are the level
      byte, the cap word, the store base and the column words, and the cap is abstract (`cap`,
      `hcap`). `read0` is an instance, so the level-0 statements and costs are unchanged.
      `FRXReadLv` holds the levels 1–4 instances and costs.
    - Pitfalls met:
      - A `simp` discharger `(simp only [size_set]; exact …)` fails when there is no `size_set`
        to rewrite ("no progress"), and `rd_set_self` then silently stays unapplied. Use
        `((try simp only [size_set]); exact …)`.
      - **A structure field named like a parameter** (`tb : regs ≤ tb`) shadows the parameter in
        later fields. Name fields differently (`rt`, `tj`, …).
      - `split_ifs` did not split an `ite` on the right whose `Decidable` instance came from
        `simp only [baryVal, …]` unfolding (the instance's type mismatched under `implicit`
        transparency). Use `rw [sValM, baryVal]`, then `by_cases h0` and `if_pos h0`/`if_neg h0`
        on both sides.
      - `rw [eAt]` fails under a `Finset.sum` binder. Rewrite inside `sum_congr`'s per-term goal.
      - With a parametric stride `nw`, `omega` treats `nw * (j + 1)` and `nw * j` as unrelated
        atoms. Supply `Nat.mul_succ` and `Nat.mul_le_mul_left` facts.
      - `(by simp only [regs]; omega)` fails when the fact needed is a hypothesis `regs ≤ sb` (simp
        only rewrites the goal). Plain `omega` works with `regs` as an atom.
      - When a section variable `{i}` is used only in a proof term, `inv_sem I wf_nodeBody`
        cannot infer it. Write `(wf_nodeBody (i := i))`. A `def` (`WalkSt`) gets an explicit
        `(i : ℕ)`.
    - Profiles (sequential): FRXBaryTop 28.9 s, FRXReadLv 8.5 s, FRXRead 53.1 s (unchanged).
    - Stopped: context long. Handover in RESULT Part 15 §7 (folds, `Enc`, flags, per-level decode,
      output, `'N'` case, wiring).

## Part 16

29. Item 2 of Part 15 §7, bottom-up pieces (pure decode chain, `Enc`, the `eq` table).
    - `FRXEncB` (pure): the forward butterflies `fwdLevel`/`fwdRun` (`bflyLevel`'s inverse,
      top-down), `fwdRun_block` (block invariant by induction, `sum_novel_succ` and
      `normW_block`), **`fwdRun_enc`**. A message zero-padded to `2^logN` gives `encF` at every
      position in one run, so there are no cosets and no offset register (deviation 1 of
      RESULT Part 16).
    - `FRXLevel` (pure, imports `FRSoundnessTruths`): K coordinates (`foldAt_f₀/₁`, `encF_f₀/₁`,
      `nextMsg_coords`, `mem_consSet_iff`), `chK_words`/`rdK_of_words`, and **`level_decode`**:
      `¬ farL` plus `A_c = jointAgree` give `msgOf` as interpolation and butterflies in `F`.
      `truthC` is not needed for the decode, because the flags test `consSet` itself.
    - `FRXFwd`: the program was copied from `FRXBfly`'s pair/level proofs (script-substituted)
      with a new arithmetic and a count-down level loop (`rKf`, `fPre`: `rLv := rK − 1`,
      `rTr := tb + 40 rLv`). It compiled almost unchanged.
    - `FRXEqT`: `eqtIR`, a direct product per entry (`ℓ` factors, `ite` on the bit), with
      `eqBody_sem`, `eqEnt_sem`, `eqtIR_sem` and `sAt_words` (the chain answers become `eqtIR`'s
      input, with positions kept symbolic through `phStart`).
    - Pitfalls met:
      - **A `.blk` named by a def, frame lemma by `rd_runPrims_of_not_writes` against
        `semXIR I (.blk ps) s`**: this timed out (whnf, 200 k heartbeats) for `bitPs` (5 prims with
        a `.const eK 8`) but not for `omPs`. Fix: `have e : semXIR I (.blk ps) s = ⟨runPrims ps
        s.M, s.o⟩ := rfl; simp only [e]` inside a standalone lemma (journal item 26's trick
        again). `have g : rd (semXIR …).M … := ⟨facts about runPrims⟩` (defeq ascription) also
        timed out; state the block lemma on `semXIR` directly.
      - `(by tauto)` to weaken a disjunction hypothesis timed out inside a loop step. Use
        `hi.imp_right fun h => h.imp_right …`.
      - The implicit `eb`/`cb` of a lemma must be given before the `(by omega)` arguments
        (journal item 26 again), else omega sees metavariables.
      - A heap-size fact is lost by `generalize` unless `size_sem` is taken before it.
      - `simp` does not evaluate `Nat.testBit 1 1`; state it as `rfl` facts for the control.
    - Upstream drift during the build: INT-2 (revision 3.13) is editing S-0's modules in the
      worktree (`piSize = 797,888`), so `FRSoundnessDefs` and `FRXLog` (its `piSize_eq` use) no
      longer build there. I verified on a snapshot of HEAD plus the four new modules
      (`logs/fr-build-SH2s`).
    - Coordinator's heads-up (3.13): the new code keeps positions symbolic (`phStart`, `ansB`,
      parameters `cb`/`eb`/`tb`). The constants to update after INT-2 are the existing ones
      (`nRep`, `chTab`/`fsMsgs`, `capW0`/`capOffL`, `piSize`-dependent tape facts).

## Part 17

30. Revision 3.13 and the fold's row step.
    - The coordinator patched five `FRX` modules (INT-2's list). I fixed the other three
      (`FRXReadLv`'s cap offsets and controls, `FRXLeaf`'s and `FRXSeed`'s `piSize` facts).
      They are constants only, and the build is green (`build17c.log`).
    - `FRXFlag`: `fBody_sem` was written in the `eqBody_sem` style. One pitfall: a long chained
      `rdF_eq (… |>.trans …)` term for a heap cell after two frames failed (`simp` made no
      progress, metavariables). Fix: a local `hh5 : ∀ i, regs ≤ i → rd s5.M i = rd s.M i`, then
      `rdF_eq (hh5 _ _) (hh5 _ _)`.
    - Stopped: context long. Handover in RESULT Part 17.

## Part 18 (track S-H2i)

31. `flagIR` finished (Part 17 §What remains, item 1), own tree `logs/fr-build-SH2i`.
    - Program: `fEnt` = `zPs` (accumulators 0, `gE := eb`, row count) ; `addrPs gW gJ cb cs` ;
      `loopK gC2 gN2 R fBody` ; `X[j]` load and `cmpPs` ; `Y[j]` load and `cmpPs2` ;
      `addrPs gT gJ fb 1` ; `store` ; `gJ += 1`. `flagIR` loops it `n` times.
      Cost `12 + n (92 + 156 R)` (`cost_flagIR`, read off a scratch `#eval` outside the entry).
    - `cmp_word`: the zero test of the four word differences is `[a = e ∧ b = f]` in `F`.
    - `fEnt_sem` (one position), `flagIR_sem` (the flags `flagV` of the initial heap, the heap
      outside `[fb, fb + n)` kept), `flagV_consSet` (flag `≠ 0` iff `j ∈ consN`, through
      `mem_consSet_iff`). Control `toyFlag_run` (`decide +kernel`): flags `[1, 0]`.
    - Pitfalls: `rw [hd, b3]` closed `toWord (a + 2) = toWord (a + 2·(r+1))` by `rfl` in one
      build and not in the next after an edit upstream of it; use `exact congrArg toWord (by ring)`.
      `tauto` on a 3-way disjunction into `TK` timed out (whnf); give the injections. `open FR.Snd`
      is needed for `nextMsg`/`sAt`/`consSet` (otherwise auto-bound implicits: "Function expected").
32. The message rows (`FRXMsg`): `zeroIR`, `finIR` (tape, level 4), `gathIR` (levels 0–3),
    `msgTIR`/`msgHIR`, and the `nextMsg` specs `msg4_next` (with `finalAt es = finPi π` as the C.4
    chain-link hypothesis) and `msgH_next`.
    - `finIn` as four `inW` blocks (one `input` + increment each); one flat block of four inputs
      timed out in `simp` (whnf). Compose small block lemmas instead.
    - `ring` does not identify `x / 2 ^ 3` with `x / 8`; rewrite `(2:ℕ)^3 = 8` first.
    - `Nat.le_of_lt_succ (Nat.mod_lt x _)` gives `x % Nat.succ 7`, which omega treats as another
      atom than `x % 8`; state `4k(x % 8) ≤ 4k·7` with `Nat.mul_le_mul_left _ (by omega)`.
33. One level composed (`FRXDecLv`): `bfRowsIR` (unrolled rows), `decBack_sem`, `MsgOk`,
    `decFront_sem`, `decLv_sem`, the instances `decLvU_sem`, `decLv0_sem`, `msgOk_four`,
    `msgOk_lower`, `layLv`.
    - **`set` on a list built from `List.range 2^18`** made `generalize` unify `Jl.length` with
      `2^mLog` by evaluation (whnf timeout) when one hypothesis (`hM2`) still mentioned
      `Jl.length`. Rewrite every hypothesis, and introduce such lists opaquely
      (`obtain ⟨Jl, hJl⟩ : ∃ Jl, Jl = … := ⟨_, rfl⟩`).
    - **omega hit "maximum recursion depth"** on simple goals in contexts with `hs : π.size =
      piSize` (msgOk_four) and in some contexts with `Fin (lvl …).rows` binders. Not isolated;
      the workaround is explicit `le_trans (by decide) …` for the constant comparisons.
    - Higher-order unification of `fwdIR_enc`'s message `c` failed; pass it explicitly.
    - Costs per level read off a scratch `#eval` (outside the entry): level 0 `1.40·10^14`,
      level 1 `8.2·10^11`, the rest below `1.4·10^10`.
    - Profiles: FRXFlag 44.8 s (kernel 15.2 s, the toy run), FRXMsg 71.2 s, FRXDecLv 24.2 s.
    - Stopped: context long. Handover in RESULT Part 18 §7.

## Part 19 (track S-H2j)

34. Own tree `logs/fr-build-SH2j` (a copy of `fr-build-SH2i`, then `snap.sh`: HEAD's modules of the
    other tracks, mine symlinked, because S-E8 is editing `FRVIR*` in the worktree).
35. Item A, `readIR_frame` (new module `FRXNode`): `readIR_sem`'s proof with the last step taken from
    `posLoop`'s frame conjunct; `readIR_sem` unchanged. `readLv_frame` for levels 1–4.
36. Item B, the five levels (`decLevels`, `decLevels_sem`):
    - `lvStep_sem` (read and decode of level `i ∈ [1,4]`) takes a reference state `s₀` (after
      `wtabIR`) and the agreement on `KeepR` (below `jb0`, `[chB, eqB)`, from `2^25`); it rebuilds
      `hT`, `hS` (`sAt_words` with `p1_lt_nRep`), the index and the word (`readLv_wordOf`: the
      `F` reading is `wordOf` once `capDig es i = capPiL i π`).
    - The message step is passed as "`MsgOk` from every state agreeing below `2^24` outside the
      `eq` table" (`msg4_keep`, `lvMsg_keep`); `eqt_keep` gives the `eq` table's frame without
      `hS` (take `S v := rdK s.M (cbS i + 8v)`).
    - Program order: `decNode := decRead ; chainIR ; decLevels`. The chain has a heap frame
      (`chainIR_sem`), the index (`idxIR`) has none, so the chain runs after the read.
37. Item C: `cost_decLvIR` (exact, generic in `i`), `cost_levels` (the five numbers of Part 18's
    table, now theorems), `cost_decLevels = 140,866,457,335,279`; `sizeIR_decLevels = 53,515`
    (`decide +kernel`, 0.9 s kernel); `WF`, `NoLoopT`, `outs` of `decLvIR` and `decLevels`.
38. Items E and F: `decNode_sem` (index, read, chain, levels), `decOk_decLN3`,
    `cost_le_decLN3`; `decSnark := decLN3` (FRXExt); FRXLeaf's proof follows the new branch name
    (statement unchanged). `ext_node` (new module `FRXNodeRun`): the run halts with no output,
    and the final heap holds `f⁽⁰⁾`.
39. Pitfalls:
    - **`omega` and large atoms.** `omega` failed with "maximum recursion depth" on goals whose
      atoms were `sizeIR decRead`, `sizeIR (chainIR …)`, and in a context with
      `(semXIR I (wtabIR tb0) s).M.size`. `generalize` the atoms first, or give the bounds by
      `le_trans (by decide) …` (helpers `le_add3`, `le_add4`). This is probably Part 18's
      pitfall too: `omega` compares atoms up to definitional equality.
    - **A hypothesis stated with an unfolded definition** (`readIR_sem` gives
      `semXIR … (readIR 0 capW0 …) s1`, the goal has `read0`): `generalize` did not abstract
      it, and a later `.trans` made the elaborator evaluate `semXIR` (whnf timeout at the
      declaration). State the fact with the folded name (`have d2 : … read0 … := …`).
    - Lean's `one_ne_zero` at `Word` needs `NeZero 1`; use `(by decide : (1 : Word) ≠ 0)`.
40. Item D is blocked: no `FR.readSigned`/`reassemble` from the packed witness (A.5/A.7) exists.
41. Checks: the whole entry (`FR`, `FRXNodeRun`) is green in the snapshot tree (3 min 4 s,
    `build19`); the axioms are the three standard ones (`axioms19.log`); the source rule reports
    128 files and 0 findings. Profile: `FRXNode` 70.4 s, of which ≈ 49 s is the kernel on the toy
    runs (`finPi_toy` 23.3 s). Handover in RESULT Part 19 §8 (D first).

## S-H2k (2026-10-28): `FR.readSigned`, the node output

42. Build tree `logs/fr-build-SH2k` (copied from SH2j with its `.lake`; `snap.sh` links only the
    modules that exist: `FRXNode FRXNodeRun FRXExt FRXLeaf FRNodeRead FRNodeReadLayout FRXOut*`).
43. Item 4 first (kernel cost of the toys). Measured: a concrete kernel run of the DSL costs
    ≈ 185 ms per machine operation on a 296-cell memory (`decide +kernel` of 20 `add`s: 3.7 s),
    independent of `toProg` vs `semXIR` (`toyGath` via `semXIR`: 20.3 s; 1 iteration of
    `gBody`: 5.7 s). No instance of `gathIR` (8k iterations) fits 3 s. `toyGath_run` is replaced
    by `toyGath_ctl` (from `gathIR_sem` on every state: `X[0]`, `Y[0]`, `X[1]` are rows 0, 1, 2;
    `X[1]` is not row 1). `finPi_toy` keeps its statement; the proof reduces the 64 kB toy proof
    to its 32 read bytes (`byteAt_toyPi`), 205 ms. `elaborating `norm_num` on a goal containing
    `semXIR … (gathIR …)` timed out at whnf: `generalize` the state first.
44. Item 1: `FRNodeRead` (element view `w : ℕ → F`, A.7): `streamCell`, `streamWord`,
    `stream`, `readTrace` (fixed item shape, the length word not read), `readSig`, `readStmt`,
    `FR.readSigned σ w`, `FR.readWit`. Controls: `readTrace_of_stream` (the reader inverts
    `0x54 ‖ traceBytes tr`), `readSig_idx_ctl`, `readStmt_ctl`; `FRNodeReadLayout` checks the
    constants and `streamCell (σ+1) (1+e) = Node.seedCell σ e`.
45. Item 2, pure half (`FRNodeReadW`): `reassemble_eq` (the walk field by field: `cont`,
    `Appends`, `rsPhase_spec`, `foldl_rsPhase`); `readTrace_getD`, `qBytes_readTrace`,
    `stream_slice`; `logWords_readTrace` (`trW` over the aligned items); `sigWords_readSig`.
    Pitfall: `simp only [List.foldl_map] at` + `generalize` made the kernel unfold the phase walk
    (32 s, deep recursion); stating the folded form first is free.
46. Stopped before the output program (context). Checks: build green (`build20`), axioms
    standard (`axioms20.log`), source rule 136 files / 0 findings, profiles `*.20.*`
    (`FRXNode` 70.4 s → 26.6 s). Handover: RESULT Part 20 §5.

## S-H2l (2026-10-28): the node output (`FRXOut`), `ext_node` with the witness

47. Build tree `logs/fr-build-SH2l` (a copy of `fr-build-SH2k` with its `.lake`; `snap.sh` links
    `FRNodeReadS FRNodeReadP FRXOut FRXOutRun` too; `c.sh` compiles one module in the capped scope).
48. Design. The output program does no stores: it reads `f⁽⁰⁾` at `ob0` through an address block
    (`addr = R + ((u>>1)&m)<<18 + (u>>s3)<<s4 + (u&1)`), so a stream word and an L word are each
    one computed load. Both slots' streams therefore need no gather into `obL`. What is emitted is
    described by a segment language (`Seg`: `wd`, `cp`, `rep`, `cat`, `shw`/`sh8` for the seed's
    straddling words, `kite` on the child kind, `sib` for one level's siblings), with a pure
    semantics `segOut W κ b` (`FRNodeReadS`), compiled once (`FRXOut`).
49. `FRNodeReadS`: `logWords_trSeg` (one `rep` per phase over `tItems`; `trWf_rep`,
    `trWf_congr` for the node items whose `h` differ), `entryW_seed` (the 15 straddling words:
    `shw_bytes`, `sh8_bytes`), `sigWords_sigSeg` (`lPairs`), `stmtWords`. `FRNodeReadW` gained
    `tail_slen_le` (the 3.5 s `decide +kernel` once, shared).
    Pitfalls: `List.toArray l |>.toList` is not `rfl`-cheap (a `foldl`): `rw [List.toList_toArray]`
    first. `congr 1` on `map f (range 14) ++ … = … ++ …` timed out at whnf: use
    `congrArg₂ (· ++ ·)`. `List.drop_eq_getElem_cons` rewrote the outer `drop 1` first: give it
    the instance (`show a < ws.length`). `congr 1` on `lWord w σ x = lWord w σ y` hit max
    recursion: rewrite the index with `show … by omega`.
50. `FRNodeReadP` (pure, done): `pSeg` mirrors `ctbs` field by field (`pPh`, `pRest`, the seed's
    `hdr`), with the invariant `PrevInv` (after a `P2` phase the answers are its items') and the
    decided `qOk` (every `queries i` follows level `i`'s `P2`). `drop_rep`/`drop_cons_item` give
    the items and offsets inside a phase; `qB`/`cpSlice` turn a query slice into stream words;
    `ans_bit` and `testBit_posOf` give a position bit as a stream-word bit; `sib_one`.
    `proof_words`, `traceKind_lvl` (byte 80 = low byte of word 10), `segLen_pSeg = 99738`
    (`decide +kernel`), `reassemble_size`, `signedWords_readSigned`, `witWords_readWit`,
    `readWit_fits`.
51. `FRXOut` (machine, done): `segIR` (registers 200–224 for the leaves, `226 + 3d`… for `rep` at
    depth `d`), `ldw_sem`, `cpIR_sem`, `sibHit_sem`, `sibH_sem`, `sibP_sem`, `sibIR_sem`,
    `segIR_sem`, `wf_segIR`, `loK_segIR`, `noW_segIR`, `noLoopT_segIR`, `ctx_segIR`.
    Pitfalls: a 14-prim block's `rd` chain timed out with a `decide` discharger (it tried to
    evaluate the array size); discharge with `simp only [names]; omega` only, and read the heap
    through `rd_runPrims_of_not_writes`. `exact cpIR_sem …` against the `segIR` goal timed out
    in unification: `rw [segIR, segOut]` first. `generalize` a state only after rewriting the
    goal to mention it (`semXIR_seq`, `semXIR_blk`), else the goal keeps the folded program.
52. `FRXOutRun`: `outIR` (tag, statements, per slot the kind flag, `slotSeg`, `sigSeg`), the
    address lemmas `addrS_toNat`/`addrL_toNat` (`src_stream`, `src_l`), `outIR_out`. Numbers
    read off a scratch `#eval` (`scr/ev.lean`, outside the entry): cost 21,609,039, outs 571,019,
    size 22,421; then `decide +kernel` (`cost_noLoopT` removes `t`).
    Pitfalls: kernel deep recursion or timeouts at a declaration came from `rfl` closing a goal
    `[] ++ witWords X = witWords X` or `a + b + 1 + c + 1 = a + b + d` after `rw`: the kernel
    unfolds the big side (`witWords (readWit …)`, `cost decN`). Close with `List.nil_append`,
    or `generalize` the big atoms and `omega`. A `rfl` between a two-block `seq` and one
    `runPrims` list needs the lists in program order.
53. `FRXNode`: `decF0` (old body), `decNode := decF0 ; outIR`; `decF0_sem` (old proof),
    `decNode_sem` (same statement: `outIR` is `LoK`, the heap is kept), `decNode_out`,
    `cost_le_decLN3_node`. `FRXNodeRun`: `ext_node` (the witness), `E_node`. A name clash
    (`bit_word` in `FRXEqT`) surfaced only when `FRXNode` imported both: renamed `bit_shr_word`.
54. Checks: whole entry plus the new modules green (`build21`, 4 min 59 s wall on the shared VM);
    axioms standard (`axioms21.log`); source rule 152 files, 0 findings (`source21.log`).
55. Profiles (`*.21.*`): FRXOut 57.7 s (elaboration), FRNodeReadP 21.3 s (4.9 s kernel on the decided phase-table facts), FRXNode 28.3 s. Re-built on HEAD d332644 (`build21b`). Handover: RESULT Part 21 §7.
56. S-H2m (3.17 O3): `den`/`Eden`/`den_of_run` (`FRXComputes`; a halting run's output is the denotation, via `runs_body` + `exec_mono`), `E := Eden …`, `computes_Eof` restated, `E_W`/`E_bad` over `Eden`, `den_leaf` + `E_leaf` without domain, `E_node` via `den_of_run` (domain kept). Finding O3′: `semXIR` is the 64-bit machine (word-addressed tape), so the node case cannot extract beyond tape word 2^64; `hOut` is dischargeable only for W/bad/leaf. Pitfall: `rw [ho]` with `ho : (extWith decSnark).run …` against a goal stated with `ext.run`: `show (extWith decSnark).run _ _ = _` first. Stopped at the coordinator's request (core PR #20); build green, axioms standard, source rule clean (`axioms22.log`, `source22.log`). Remaining: RESULT Part 22 §3.
57. S-H2n (B-15, revision 4.0; pin 6d05d00, HEAD a3bc63a). Build tree `logs/fr-build-SH2n` (copy of INT-6's, `snap.sh` with `MINE`); baseline `lake build FR` green (`logs/S-H2n/build0.log`, 2,408 jobs).
    Finiteness check: `acc` bounds `|π| < 2^64`, `|tr| ≤ S.qV ≤ 2^16` (certificate cap), each query `≤ queryCap`; `SigOk` bounds `idx < 2^16`, `|ots| = 133`, `|path| = 16`; digests are 32 bytes; a leaf has `n ≤ chainCap`. The witness space of `Rel (S.acc vk) c` is finite. Plan: a generic `Finder α := (α → Option Wit) → Option Wit` (first `some` over a fixed enumeration; `Sound`, `Covers`), built from `fRet`/`fBind`/`fOr`/`fNat`, so no large list is ever a closed term (the compiler lifts closed terms to module start-up).
    Design finding (deviation from B-15's text): the search tests `acc (vkOf π)`, and `vkOf π = vk` only on an accepted SNARK node run (`vkOf_of_run`). For a `W` proof `vkOf π` is arbitrary bytes, and for a leaf SNARK the search could return a node witness for the wrong key. So outside the domain `E` dispatches on the kind: `W` → `WitnessSending.decode π` (closes `WBeyond` by `wBeyond_of_decode`), node SNARK → `search`, leaf SNARK → the denotation (`E_leaf` is domain-free), `bad` → `none`.
    `X.E` takes the search's acceptance `A : Digest → Digest → Signed → Bool` as a parameter (the verifier is parametric in `finPf`, `lRows`, `κs₀`); the certificate instantiates `A := S.acc`.
58. `FRXSearch` (finders, `search`, `search_spec`, `sFits_of_acc`, controls) built with three repairs: `covers_fNat` via `Option.isSome_or`; `ByteArray` size via `Array.length_toList` + `rfl` (`simp [ByteArray.size]` hit max recursion); a `rw` of `d.toList.length` failed on a dependent motive, so `rwa [Vector.length_toList]` on the instance. Name clashes renamed (`relB` → `relDec`, `sound_bind` → `sound_fBind`, …). Pitfall: inside `FR.X`, `Rel` is not the contract's `Rel`; write `RecursionFast.Rel`.
59. `FRXExt`: `Ed`, `InDomE`, `Eout`, `E A`, `computes A`. Restated `ext_W` (all sizes), `ext_bad`, `ext_encode`, `E_leaf`, `E_node`; new `E_node_out`. Soundness repairs pass `A` (`hE : S.E = X.E A`). `FRSoundnessExtE`: `wBeyond_E`, `ExtIfaceE`, `extIfaceE_of` (an out-of-domain node: `E_node_out` + `rel_readWit` + `vkOf_of_run`; no new hypothesis), `hExt_of_ifaceE`, `finalLaw_ofE`, `kstate_front_ofE'` (no `hOut`, no `hWB`). It built on the first try.
60. Checks: `lake build FR` green (2,410 jobs); axioms standard (`logs/S-H2n/axioms.log`); source rule 188 files, 0 findings; probe executable `import FR` built (4,819 jobs) and ran (47 s, 1.1 GB; `E` on W/bad, `search` referenced); sequential profiles `logs/S-H2n/prof-summary.txt`. RESULT Part 23.
61. **S-H3 (revision 4.1 extractor), plan (item 1), before any proof.** HEAD `7e14be6`, build tree
    `logs/fr-build-SH3` (copy of `fr-build-SG13`, `logs/org20`), logs `logs/S-H3/`.
    *Carries over unchanged:* the DSL (`FRXDsl`, `semXIR`, `cost`, `Safe`/`BoundsOk`, `toProg`,
    `den`/`Eden`/`den_of_run`/`computes_Eof`); the parse helpers (`readAt`, tape lemmas
    `tape_getD4`, `tape_getD_proof`, `tape_byte0`, `lowByte`); the `W` branch (`wIR`, `wIR_sem`,
    `safe_wIR`; `E_W`'s argument); the read/sort/lookup machinery (`idxIR`, `look_spec`,
    `read_spec`, parametric in the level); the search (`FRXSearch`, kind-free); the per-level
    decode `decLvIR`/`level_decode` *as an algorithm* (parametric in `logN`, `mLog`, rows).
    *Must change:* (a) the parse and the kind dispatch (`'A'` any size; `N2/N4/N8` at
    `|π| = piSizeOf seq4 = 798,192`; bare segment bytes `bad`; else `W`; an empty proof must not
    read the log's first word as a kind byte); (b) the aggregate leaf (new: `(s, n)` from `π`'s
    bytes 64–95 and 8–15, any size); (c) the item positions at `seq4` (`phStart4_shift`: identity
    below 170, then +1 … +14) in the chain replay; (d) the node's level decode at `m = 31/32`
    (`ladderOf m`, `mLog 0 = m − 13`); (e) the output: two signed children, the second an
    aggregate `hdr_A ‖ π₁ ‖ … ‖ π_k` with `tr_A = tr₁ ‖ … ‖ tr_k` (slot σ's stream at H block
    `chainLenOf seq4` for `N2/N4`, `aggChainLen 4` for `N8`'s second child), segment `i`'s trace
    starts at stream byte `1 + (i − 1)·1,482,751`, i.e. **unaligned** for `i ≥ 2` (shift
    `(i − 1)·7 mod 8`), so 3.x's aligned `segIR` needs a shifted-copy leaf; (f) the fuel.
    *Fuel check (f), done first (`logs/S-H3/fuel-check.{py,txt}`, the exact formula of
    `cost_decLvIR` per level of `ladderOf m`):* the five levels cost `2^47.00` at `m = 30` (3.x),
    **`2^49.00` at `m = 31` (`N2`) and `2^51.00` at `m = 32` (`N4`/`N8`)**, against the contract's
    cap `B t = 2^48 + 2^16 t` (claim.json: `3·2^46 + 2^13 t`). Level 0's barycentric
    interpolation is quadratic in `k = 2^(m−13)` (`k²·(1363 + 106·64)`): 5.6·10^14 at `m = 31`,
    2.24·10^15 at `m = 32`. `2^16 t` cannot pay for it: the log of an extractable node has
    `t ≈ 2^27` words. **So 3.x's node decoder does not carry over to any revision 4.1 node kind
    within the contract's budget.** Options (for the coordinator; not this track's call):
    (i) a quasi-linear erasure decoder at level 0 (what the contract's `2^48` term assumes:
    erasure locator by a subproduct tree, coset FFTs; `≈ 10^12` steps); (ii) decode only the
    rows the output reads (H's message slots are rows 4–7 of level 0, `e mod 64 ∈ {4..7}`), with
    S-E placing every signature value in H's WOTS/path blocks instead of L, and a cheaper
    weight loop (one batched inversion instead of one per pair): `m = 32` then ≈ 1.6·10^14.
    *Plan for this track, given (f):* deliver everything that does not depend on the node
    decoder, with the node branch a **parameter** `nd : XIR` under `DecOk4` (cost within the
    fuel, loop bounds, outputs) and a semantic law (`NodeDecLaw4`), so that the decoder slots in:
    `FRX4Prog` (parse, dispatch, `aggIR`, `DecOk4`, fuel), `FRX4Ext` (`den` on each kind,
    `computes4`, `E4X` with B-15's out-of-domain dispatch, `ExtOff`, `NodeExtLog` from the node
    law). The certificate instance uses `nd := .blk []` (no output) until the decoder exists.
62. S-H3 build: `FRX4Prog` (parse4, `ext4IRWith`, `aggIR`, `DecOk4`, fuel) and `FRX4Ext` (denotations per
    kind, `E4X`, `computes4`, `extOff_E4X`, `NodeDec4`, `nodeExt_E4X`, `ks4_E4X`, controls), namespace
    `FR.X.X4`. Pitfalls:
    - **A 27-prim block's `rd` chain** times out (`whnf`): `simp only [runPrims, List.foldl, Prim.run]`
      builds a tower whose values embed the earlier arrays. Fix: build the flag block from small lists
      joined by `++` (`eqPs`, `orPs`, `normPs`, `finPs`, `szPs`), `runPrims_append`, one lemma per piece
      (`rd_eqPs` …), and skip non-writing pieces with `simp (disch := decide) only [rd_runPrims_of_not_writes]`.
    - `decide` in a discharger evaluates array sizes; drop it from register chains (Part 21's pitfall).
    - **`BoundsOk … (br4 nd) s` in a `have`** (even `:= by sorry`) hit "maximum recursion depth": the
      elaborator/linter `whnf`s the type, unfolds `br4`, and evaluates the parse on the concrete tape.
      Fix: `attribute [local irreducible] br4 in` and `ext4IRWith_eq` (`rfl`, stated outside).
    - `run_toProg` against `initSt (memX + …)`: generalize the state and the tape first (3.x's
      `halts_of_tape` pattern); a `rfl` that meets `initSt 2^26` evaluates it.
    - `rdLE64_eq` by `simp; ring` hit **kernel deep recursion only under `lake build`** (async kernel
      thread stack), not under `lake env lean`. Fix: an induction (`ofLE_bytesAt`), no big `ring` term.
    - `simp` turns `byteAt π 0` into `π.data[0]?.getD 0`; `generalize byteAt π 0 = b` before case
      analysis on `kindOf4` (`kindOf4_eq`, `rfl`).
    - Literal `(1 : Word)` does not match `mul_one`'s pattern after `if_pos`; `have m1 : ∀ x : Word,
      x * 1 = x := fun x => by simp`.
63. S-H3 checks: `lake build FR FRX4Prog FRX4Ext` green (2,430 jobs, `logs/S-H3/build-final.log`); 25
    axiom lines standard (`axioms.log`); source rule 235 files, 0 findings; probe `import FR` +
    `import FRX4Ext` built (4,859 jobs) and ran 49 s / 1.1 GB (`probe-run.log`: `E4X` on W true, on a
    bare segment false, on the toy aggregate `leaf s[0] = 7, n = 5`; `ext4` 170 statements); profiles
    FRX4Prog 9.5 s (kernel 0.42 s), FRX4Ext 12.1 s (kernel 1.26 s). RESULT Part 24.
64. S-H4 (pass 1) design. Revision 4.2 (A)(ii) adopted with one change of method: the evaluation domain is
    `D x = ofB64 x` (`FRRS.D`), so every difference `D s − D J_u` is the one-word `B64` value `s ⊕ J_u`
    and its products cost `mulB` (13 steps), not `mulF` (57). The Lagrange numerator `Π_{u≠t}(s ⊕ J_u)`
    is the prefix product `P_t` (stored by a forward pass) times the suffix product `Q_t` (a register in a
    backward pass): Montgomery's pass without its inversion (the Lagrange form needs only the product;
    no `ℓ(s) = 0` case). Weights `W_t` are `k` `invB`, folded into the values `Y_c[t] = W_t y_c(J_t)`.
    Exact cost `27 + k(1,122 + 72C) + k²(101 + 40C)`: **261 steps per pair at C = 4** (blueprint's
    estimate 60 + 424 = 484). Cost model `logs/S-H4/fuel-check4.py`: decoder levels at m = 32
    7.5–8.5·10^13 (2^46.1–2^46.3), 2.5–2.8× under `decBudget`; m = 31 1.9–2.1·10^13.
    Levels 1–4 need **all** rows: level i's decoded message (all 16 rows) is level i−1's `nextMsg`
    (`msgHIR` reads rows `2(x mod 8)`, `2(x mod 8)+1` for every `x`), so the agreement set of level i−1
    depends on every row. Level 0 needs all 64 rows of the *word* for its flags (linear) but only
    rows 4–7 of the *message*.
    **Memory finding**: f⁽⁰⁾'s codeword at m = 32 is 2^20 positions × 64 rows × 2 words = 2^27 words
    (3.x stores it whole at `colBase`); the blueprint's `mem = 2^27` counts the message (2^25 cells).
    With every other region the decoder needs ≈ 2^27 + 2^25 words: `memX` must be 2^28 (fuel cost
    2^28 steps, negligible), and the index base (3.x hard-codes `memX` in `walkPre`) moves with it.
65. S-H4 build of `FRXLag` (new, 920 lines / 738 code / 52 theorems): `lagIR` (`yTabIR` weights and
    values, `tgIR` targets: `fwdL`, `bwdL` with `accIR C` unrolled rows, `stAcc C`), `lagVal`,
    **`lagVal_eq`** (= `interpF D J y s`), `cost_lagIR`, `wf/noLoopT/outs_lagIR`, and the machine
    semantics of the weights and values: `wInL_sem`, `wLoop_sem`, `yLd_sem`, `ySt_sem`, `yRowL_sem`,
    `yLoop_sem`, `wyBody_sem`, **`yTab_sem`**. Not yet: the target half (`fwdL`/`bwdL`/`accIR`/
    `stAcc`/`tgBody`/`tgIR`) and `lagIR_sem`. Pitfalls (new):
    - `rw [semXIR_seq]` repeatedly rewrites the *outermost* `seq`, not the next one in program order:
      flatten once with `simp only [body, semXIR_seq, semB]` and then `generalize` innermost-first.
    - `generalize e = x at h₁ h₂` does **not** touch the goal: write `at h₁ h₂ ⊢`.
    - `rd {M := m, o := o}.M i` against `rd m i` can time out in `whnf` (seen at `refine ⟨a1, …⟩`):
      `dsimp only` then `generalize` the memory in hypotheses and goal.
    - `toWord (x + 1 + 1)` against `toWord (x + 2)` times out: `h.trans (congrArg toWord (by omega))`.
    - A frame lemma `f _ (by decide)` with the index left to unification elaborates `decide` on a
      metavariable: give the index (`hb lgQ …`, `b4 (yb + 2 * (C * t + c)) …`).
    - `obtain … := lemma …` has no expected type: pass implicit layout arguments (`(cb := cb)`) or
      `omega` sees fresh atoms.
    - `invB` as its own `XIR` node (not `invBC` spliced into a block) keeps `WF`/`Writes` by `simp` cheap
      (`nw_invB`, `wfB_inv` at numerals) and costs the same (1,033 + 9 + 1 = 2·522 − 1).
66. S-H4 checks: `lake build FRXLag FR` green (2,476 jobs); 13 axiom lines standard; source rule 267 files,
    1 finding in G1's uncommitted `FRVIRSpec.lean:259` (not mine); `FRXLag` profile 85 s wall, kernel
    < 0.5 s (elaboration: three `loopK_run` `refine`s 7–11 s, `nlinarith` 3–4 s; golf before the build
    budget sees it). Probe (4,951 jobs, 5.8 s run): compiled `lagIR` on a 4-target, 2-row toy equals a
    direct `F` Lagrange interpolation (and not the neighbouring rows). Handover in RESULT Part 25 §6.
67. **S-H4 pass 2** (2026-10-29). HEAD `a91d355`, build tree `logs/fr-build-SH4b` (copy of `fr-build-SH4`,
    `snap.sh` on HEAD, `MINE` = `FRXLag FRXLagT` + the new modules), logs `logs/S-H4b/`. The worktree
    has other tracks' uncommitted edits (RET-2's `FRSoundnessCore*`, G2's golf); not touched.
68. Item 1 done in a new module **`FRXLagT`** (the target half of `lagIR`): `fwd_blk`, `fwdL_sem`,
    `fwdLoop_sem` (prefix products at `pb + t`), `accRow_sem`, `accIR_sem` (induction on `C`),
    `bwd_ptr`, `bwd_mul`, `bwdL_sem`, `bwdLoop_sem` (invariant over `Ico (k − j) k`, `sufP (k − j)`),
    `stRow_sem`, `stAcc_sem`, `rd_zeros`, `tgBody_sem`, `out_ne`/`outC_lt` (distinct targets' cells by
    `mod k`), `tgIR_sem`, **`lagIR_sem`** (output row `c` at `ob + 2s + 2kc` is
    `lagVal J k s y_{c₀+c}`; heap outside `[pb, ob + 2kC)` kept) and **`lagIR_interp`** (`= interpF D J y s`).
    Layout: `regs ≤ jb`, `jb + k ≤ pb`, `pb + k ≤ yb`, `yb + 2Ck ≤ ob`, `yb + 2Ck ≤ cb`, and
    `ob + 2k(C + 1) ≤ |M|` (one row of slack: `stAcc_sem`'s bound is stated at `o + 2kC`).
    Pitfalls: a frame lemma applied as `b3 _ (by decide) …` with the index left to `rw` fails
    ("expected type must not contain free variables"): give the index. `rw [rdB]` unfolds only the
    first instance: `unfold rdB`. `omega` treats `2 * k * c` and `k * c` as unrelated atoms:
    `Nat.mul_assoc` first. A `let` invariant `P` must be `dsimp only [P]` before `rw` on its
    `k − (j + 1)`.
69. Re-snapshot on HEAD `1263569` (G2 and RET-2 landed). Pitfall: `lake env lean` on a module whose
    imports' oleans are stale reports "environment already contains" clashes (an old
    `FRSoundness4TailTruths` olean still importing `FRSoundnessDefs`): build new modules as `lake build`
    targets (`snap.sh` with `MINE` lists them as roots).
70. Item 2 (`FRXDec4Level`, `FRXDec4Back`): 3.x's `level_decode` ported verbatim over T4's `CKind`
    truths; `decBack4IR = scanIR ; lagIR 2^m C c₀ ; bfRowsIR m` with the map `BackLay4` as a parameter;
    `decBack4_sem` follows `decBack_sem` with `lagIR_sem` for `baryIR_sem`. Pitfalls: inside
    `namespace FR.X`, `T4.x` does not resolve (write `Snd.T4.x`), and an unqualified `CKind` becomes
    an auto-bound implicit (write `Snd.CKind`); `rw [← hlen]` rewrote every `2^m`: rewrite a
    specialised `lagVal_eq` instance at `hlen` instead. `cost_back0_m32 = 71,758,669,416,262`.
71. Item 2′ (`FRXDec4Front`, `FRXDec4Lv`): `decFront_sem` ported with every base a parameter
    (`FrontLay4`, `MsgOk4`); it built on the first try. `decLv4_sem` composes the halves on
    `tb < fb < [jb, pb, yl, ob] < eb < xb < yb ≤ cb`; `omega` needed `2·2^m·(C + 1) = 2·2^m·C + 2·2^m`.
72. Checks: build green (2,479 jobs with `FRX4Ext`, `FRSubmission4Cert`); 18 axiom lines standard;
    source rule 362 files, 0 findings. Profiles: `FRXLagT` 75 s (was 87 s; a `show` across a
    `let`-bound `runPrims` of four prims took 8 s each: rewrite with a `runPrims_append` instance
    normalised by `simp only [List.cons_append, List.nil_append]`), the others 8–16 s. RESULT Part 26;
    handover §6 there.
73. Pass 3, first step (coordinator: Q1/Q2 answered; G2's fix first). `attribute [local irreducible]
    entryK storeM runPrims` in the six S-H4 modules. Two `rfl` base cases (`runPrims [] M = M`) then
    failed: rewrite with `semB, runPrims_nil`. Back-to-back CPU (load 20–24): `FRXLag` 89–100 s →
    53–65 s, `FRXLagT` 73.6 s → 57.6 s. `tgBody_sem` still 25 s: the trace shows an ungeneralised
    nested state as an expected type; split it into per-phase lemmas next. The tape is not in memory
    (`toProg` = `mem + mpw·t` zero words; `.input` reads the tape), so the map's only fixed neighbour
    is the index at `memX`. Context long: handover in RESULT Part 27 §3.
74. **S-H4 pass 4** (2026-10-29). HEAD `632a20f`, build tree `logs/fr-build-SH4c` (copy of `fr-build-SH4b`,
    `snap.sh` on HEAD, `MINE` = the six S-H4 modules + `FRXDec4Msg FRXDec4Map FRXRead4`), logs
    `logs/S-H4c/`. Baseline `lake build FRXDec4Lv FRXLagT FRX4Ext FR` green, 2,581 jobs (`build0.log`).
    A2′ has not landed (`A2p-RESULT.md` is a draft; its worktree edits to `FRShape4`, `FRX4Prog`, … were
    not used: `snap.sh` takes every non-`MINE` module from HEAD).
75. Item 1, `FRXDec4Msg`: `msg4_params` (per kind and level: `kᵢ = 8kᵢ₊₁`, `8kᵢ₊₁ ≤ nᵢ`, `log nᵢ ≤ 20`;
    `decide`), `msgH4_next`, **`msgOk4_lower`**, `nextMsg4_four`, **`msgOk4_four`** (the tape link `hfin`
    is a hypothesis: the final field's offset is A2′'s), controls `msg4_four_ctl`, `msgOk4_empty_neg`.
    Pitfalls: `kᵢ₊₁ ≤ 2^14` (3.x) is false at `m = 32` (`k₁ = 2^16`); `semXIR I (.blk []) s = s` is no
    longer `rfl` under `local irreducible runPrims` (`rw [semB, runPrims_nil]`); after `rw [e.1, e.2]` the
    goal `0 = 0 ∧ 0 = 0` is not closed by `rw`'s `rfl` (state the goal as `e` itself).
76. Item 2, `FRXDec4Map`: `LvMap`, `LvMap.Ok` (the level's regions in order, `ob + 2k(C + 1) ≤ eb`),
    `Map4`, `Map4.Ok m` (numerals only: sizes `2^(m − 12 − 2i)`/`2^(m − 13 − 3i)`, the chain's region
    `[chB, chEnd)` between `tb` and the levels, levels 1–4 keep level 0's word, level 1's rows below
    level 0's `eq` table, `l0.cb + l0.cs·2^(m−12) ≤ ix = memX4 = 2^28`), the literal `map4` (one record
    for `m = 31` and `32`), `map4_ok31`/`map4_ok32` by `decide`; controls (−) overlap, slack, fit, rows.
    Pitfall: write the sizes as `m - 12 - 2 * 1` (not `m - 14`) so that `interval_cases i` leaves the
    literal conjunct syntactically; `Rev4.NodeKind`, not `Snd.NodeKind`.
77. Item 3 (first half), `FRXRead4`. **Finding: `posL` is hard-coded as well as `memX`.** Every index,
    lookup and read program reads `|L|` at `posL = 5 + 99,738` (3.x's `piSize`): `walkPre`, `passPre`,
    `sortPre`, `lookIR`, and the chain (`FRXChain*`, 21 uses). A 4.1 node proof has `|π| = piSizeOf seq4`
    (798,192 at HEAD; 859,664 after A2′), so all of them need the log's position as a parameter, not
    only the base. Ported mechanically (a Python rename `memX ↦ bX`, `posL ↦ pL`, defs applied to their
    parameters outside `simp` lists, `hs : 5 + (|π| + 7)/8 = pL` for `π.size = piSize`, `hm : memX = 2^26`
    replaced by section hypotheses `regs ≤ bX ≤ 2^60`, `pL ≤ 2^60` with `include`/`omit … in`): walk and
    sort (`walk_spec4`, `passIR4_sem`, `sortIR4_sem`, **`idxIR4_sorted`**), `wf/cost/size/outs/safe_idxIR4`,
    the lookup (`bsBody4_sem`, `bsLoop4`, `foundIR4_sem`, `lookIR4_sem`, **`idx_lookup4`**,
    `Sorted4`, `posE4`). Pitfalls: `simp +decide only [WF, Prim.dst, …]` cannot decide `WF` once a
    constant word is a variable (`BitVec.ofNat 64 pL`): use `simp +decide [ … ]`; a lemma with included
    hypotheses takes them first (`walkLoop4 hbX hbX2 hpL I …`), but its own recursive call does not;
    `omit … in` must precede the doc comment. 1,015 lines; 40.8 CPU-s sequential.
78. Checks: `lake build FRXRead4 FRXDec4Map FRXLagT FR Solution` green, 2,590 jobs (`build-final.log`);
    25 axiom lines within the three (`axioms.log`); source rule 365 files, 0 findings. Not done in this
    pass: the read (`FRXRead`'s `getIR … readIR`, 1,200 lines on `lookIR`, `posL` and 3.x's cap offsets),
    the chain at `seq4`, items 4–7. Handover in RESULT Part 28 §6.
79. **S-H4 pass 5** (2026-10-29). HEAD `6d79280`, build tree `logs/fr-build-SH4d` (copy of `fr-build-SH4c`),
    logs and tools `logs/S-H4d/`. Ruling Q2: generalise the 3.x index/read/chain in place, one copy of each
    proof. G3 held `FRXChain*`, `FRXLog`, `FRXNode`, `FRXOutRun` uncommitted at the start; so the index,
    lookup and read went first (none of G3's), the chain after G3's commit (`302b523`, re-snapshot on
    `4d5700c`).
80. Index and lookup (`fold1.py`): `FRXRead4`'s parametric declarations moved, verbatim, into `FRXLogSpec`,
    `FRXSortSim`, `FRXLookup` (one `section Idx` each: `variable (bX pL)` for the programs, then
    `variable {bX pL} (hbX …) include` for the theorems); the 3.x statements replaced by term proofs
    `X4 (bX := memX) (pL := posL) (by decide) ×3 … (hs_posL hs) …`. `Sorted`, `posE` became `abbrev`s of
    `Sorted4 posL`, `posE4 posL` (the anonymous constructor in `FRXNode` needs a reducible head). Built on
    the first try.
81. Read (`fold2.py`, `fold3.py`): `FRXReadDefs`'s `getIR`/`nodeBody`/`colIR` take `bX pL` in place,
    `posBody4`/`readIR4` new, 3.x `readIR` keeps its literal body. `FRXRead` partitioned by a token closure
    (`cls.py`): independent lemmas first (`section Indep`), then `section Read4` with the `Dom4`-only
    lemmas, the program lemmas, then `include hbX hbX2 hpL` and the machine lemmas. Pitfalls: the rename's
    "inside brackets" test (meant for simp lists) also skipped list literals (`[(tp …).getD (posE L k …`):
    fix by hand; a recursive theorem's self-call does not take the included hypotheses; `stmt()` cut at
    the first `:= by` also cut a pattern-matching proof (`posLoop`'s arms); program lemmas with implicit
    `bX pL` need `(bX := bX) (pL := pL)` at use sites. `FRXRead4` deleted; `lake build FR Solution …`
    green (2,589 jobs, `build1.log`).
82. CPU A/B, side by side (`cpu-before.txt`, `cpu-after.txt`): 179.2 → 144.3 CPU-s over the six modules
    plus `FRXRead4` (44.6). `FR` alone +9.7 (it did not import `FRXRead4`).
83. Chain (`fold4.py`), on G3's versions: `cntIR pL`, `startPs pL`, `chainIR pL N tab sd` in place;
    `cnt_sem`, `chainIR_sem`, `entriesAt_tape`, `wordsOf_le`, `safe_chainIR` at `pL` with the 4.1 `hs`;
    `safe_cntIR pL (hp : pL < 2^64)`; callers `chainIR posL nRep …`, `hs_posL hs`. Pitfall: the regex also
    wrapped `startPs` inside simp lists (`[…, (startPs pL), …]`: "invalid simp theorem"). `FRXNode`'s
    `readIR_frame` (a near copy of `readIR_sem`'s proof) moved to `FRXRead` as `readIR4_frame`, its 3.x
    form an instance. Build green (`build2.log`, 2,589 jobs); 20 axiom lines standard; source rule 364
    files, 0 findings. Not started: `FRXDec4Levels`, the 4.1 chain table (after A2′), `FRXOut4`, `FRXNd4`.
    RESULT Part 29.
84. Orchestrator notes during the pass: G3 committed (`302b523`), re-snapshotted; A2′ landed on `v4/rev44`
    (cap 1,408 entries, `A` = 45,088 B, `piSizeOf seq4` = 843,280 there; main unchanged at 798,192):
    `reassemble4` must take row 18's size as a parameter (or from `aBytes`); the `FRX4Prog`/`FRX4Ext`/
    `FRSubmission4*` patch list applies on rev44. Final build on `1a37e37` (QUEUE-only after `4d5700c`):
    2,589 jobs green (`build-final.log`); source rule 364 files, 0 findings.
85. **S-H4 pass 6** (2026-10-29). HEAD `cb12cc4` (`a84753a` + a QUEUE commit), build tree `logs/fr-build-SH4e`
    (copy of `fr-build-SH4d`, `snap.sh` on HEAD, `MINE` = the pass's modules), logs `logs/S-H4e/`. Baseline
    `lake build FR Solution FRSubmission4Cert FRXDec4Lv FRXDec4Map FRXDec4Msg FRXLagT` green, 2,589 jobs
    (`build0.log`). Ruling on pass 5's Q1: `FRXLog`'s four 3.x programs stay until the 3.x decoder retires.
86. Item 1, `FRXDec4Levels` (new): `readK4` (= `readIR4 memX4 pL i cw sb nw (lv κ i).sib 2^logN`),
    `readK4_sem` (the read is `T4.wordOf κ L es i` given the tape link to `T4.capDig es i`), `msgT4`/`msgU4`/
    `msg04`, `decU4`, `dec04`, `stepU4`, `decLevels4 κ pL cw cbS tw`, `KeepR4`, `lvStep4_sem`, `msgT4_ok`,
    `msgU4_ok`, `msg04_ok`, `lv0Step4_sem`, **`decLevels4_sem`**, `wf/noLoopT/outs/cost_decLv4IR`,
    `cost_readK4`, `cost_stepU4`, `cost_dec04`, **`cost_decLevels4`** (`18,780,858,425,058` at `N2`,
    `75,054,361,432,716` at `N4`/`N8`, by `rfl` after the formula; equal to `logs/S-H4/fuel-check4.py`'s
    model), `decLevels4_m` (the program reads the kind only through `m`).
    **Pitfall (new): `omega` and `C + n` with `C` a non-reducible constant.** `map4.tb + 800 ≤ x ⊢ map4.tb ≤ x`
    fails with "maximum recursion depth": `omega`'s preprocessing reduces `C + 800` at reducible
    transparency, cannot unfold `C`, and unfolds `Nat.add` on the literal 800 digit by digit (`+ 256`
    passes, `+ 800` does not; `memX4 = 2^28` next to `map4.lU.eb + 256` fails too). Fix: `map4` and
    `memX4` are `abbrev`s, `memX4` with the literal value `268435456` (`memX4_eq : memX4 = 2^28`), and the
    proofs carry `map4_nums` (the literal's projections as equations) for `omega`.
    Pitfall: a section `variable {c : Digest}` captures `∀ c < 4` in a statement (`OfNat Digest 4`): name
    the bound row `q`. `blkSteps` leaves `if 1 = 0 then 1 else 1`: `ite_self` in the `simp only` set.
87. Item 2, `FRXChain4` (new), parametric in the item sequence `S`: `phaseMsgs4 S`, `fsMsgs4 S`,
    `msgOkB`, `fsQ4 S`, `fsQ4_zero`, `stateIn_fsQ4`, `tabEnt4`, `chTab4 S N`, **`tabW_chTab4`** (hypotheses
    `|π| < 2^60` and the decided alignment check `hA`), `seedQ_size`, **`chain_spec4`**, **`chain_dec4`**;
    at `seq4`: `fsMsgs4_length` (482), **`fsMsgs4_items`** (`= T4.fsItems4`), **`fsMsgs4_aligned`**,
    `nRep4 = 456`, `nRep4_ctl` (P1.0 … P1.4 start at 332, 375, 402, 426, 448; the final absorb at 456),
    `cbS4`, `sAt4_words`, `cbS4_bounds`. `FRXSeed` generalised in place (pass 5's rule): `seedPay_length`,
    `tape_seed` take `48 ≤ |π|`; new `seedVal_eq4`, `seedOK_seedIR4` (any proof of ≥ 48 bytes, the query
    `seedQ (vkOf π) c hdr`), `fsQ_zero`; 3.x's `seedVal_eq`, `seedOK_seedIR` are now one-line instances.
    Pitfall: `decide +kernel` on a `seq4` computation gets stuck unless `seq4_eq` (and `piSizeOf_seq4`) are
    rewritten first (`fsItems4_length`'s pattern).
88. Item 4's decode half, `FRXDec4F0` (new): main's format at `seq4` (`pL4 = 99,779`, `capFO4`, `capPi4`,
    `cw4`, `finFO4 = 64,928`, `finPi4`, `tw4`; `fmt4_vals`, **`fmt4_ctl`**: the offsets are `fsMsgs4 seq4`'s at
    `T4.capPos i` and `phStart4 47`), `tape_cap4`, `tapeF_fin4`, `lv_cap4`; the node-byte dispatch `kindNd4`
    (registers 246, 247; `X4.normPs`/`eqPs`), `kindNd4_sem`, `pickNd`, `ndK4`, `ndK4_sem`; **`decF04 κ`** =
    `idxIR4 memX4 pL4 ; readK4 0 ; chainIR pL4 nRep4 (chTab4 seq4 nRep4) seedIR ; decLevels4 κ`,
    **`decF04_sem`** (3.x's `decF0_sem` at a node kind: rows 4–7 of `f⁽⁰⁾` at `map4.l0.ob`), `wf/outs/safe_decF04`,
    `cost_decF04_eq`, **`cost_le_decF04`**. `decF04_sem` built on the first try.
89. Item 5's memory half on main (`FRXProg`, `FRX4Prog`, `FRX4Ext`): `memX4 := 268435456` (`memX4_eq`) and
    `decBudget4` in `FRXProg` (one definition; `FRXDec4Map`'s removed); `DecOk4.cost` at `decBudget4`,
    `ext4With` at `memX4`, `fuel_covers4` at both; `FRX4Ext`'s 21 `memX` → `memX4`. It built unchanged
    (`build1.log`, 2,372 jobs; `FRXProg` sits under most of the extractor, so the edit rebuilds it all).
    `sizeIR (decF04 κ) = 56,236` by `#eval`; a `decide +kernel` proof costs 10.1 s kernel: left for a
    component lemma set.
90. Item 6, not done: `tgBody_sem`'s 21.6 s is 14.8 s in its final `refine` (`trace-FRXLagT.log`), whose
    expected type holds the ungeneralised nested states: `generalize runPrims ([…] ++ zeroPs C) s2.M = M3 at
    … ⊢` misses the goal (a probe with `runPrims _ s2.M` matched nothing either), so all later
    `generalize`s miss it too. `FRXLagT` restored unchanged. `FRXChain4`: ≈ 12 s kernel in one
    `decide +kernel` over `fsMsgs4 seq4`.
91. Checks: `lake build FR Solution FRSubmission4Cert FRXDec4F0 FRXDec4Lv FRXLagT` green, 2,592 jobs
    (`build-final.log`); 45 axiom lines within the three, incl. `certificate_sub4` and `certified`
    (`axioms.log`); source rule 372 files, 0 findings. Sequential CPU: `FRXDec4Levels` 22.1 s,
    `FRXChain4` 28.9 s, `FRXDec4F0` 20.2 s (`cpu-summary.txt`). Not done: item 3 (`FRXOut4`), hence `nd`,
    `NodeDec4 nd`, the plug of `nd`. RESULT Part 30, handover §6.
92. **S-H4 pass 7** (2026-10-29). HEAD `5f39f5a`, build tree `logs/fr-build-SH4f` (copy of `fr-build-SH4e`,
    `snap.sh` on HEAD; `MINE` adds `FRXOut4 FRSubmission4 FRSubmission4Cert`), logs `logs/S-H4f/`. Baseline
    rebuilt the soundness tree (HEAD moved since SH4e's snapshot): 2,592 jobs, green.
93. **Finding: rows 4–7 do not hold everything `readW` reads.** Level 0 has 64 rows (`ladderOfR 6`), cell `e`
    is row `e mod 64`. H's message slots are rows 4–7, but the aggregates' segment count `kAct` reads the
    selector cells `κ.oneCell + selR σ ι` (rows 1–3: `oneCell ≡ 0 mod 128`, `selR = σ·2^20 + 1 + selIx`), and
    an aggregate's statement `stC κ σ h = cAB·128 + 2 + h` is its `c_A` block's `h_out` (rows 2–3). L's
    signature cells `lBase·128 + σ·2^14 + j` cover all 64 rows. No H message determines `k` (the `k`-mux reads
    `selSum`, M rows). Kernel-checked: `out_cells_rows`. Fix inside the decoder: level 0 decodes rows 1–7
    (`c₀ = 1`, `C = 7`); cost +3.3·10^13 at `N4` (`1.08·10^14` total, `decBudget4 = 2.11·10^14`).
94. Rows 1–7: `map4.l0` re-laid (`ob = 26,214,400`, `eb = 34,603,008`, `xb`, `yb` after; `Map4.Ok` at `C = 7`);
    `dec04 … 7 1 …`; `lv0Step4_sem`, `decLevels4_sem`, `decF04_sem` now `∀ q < 7, … msgOf … 0 (1 + q)`;
    exact costs recomputed by the cost formula (Python) and checked by the existing `rfl` proofs:
    `27,032,496,972,783` (`N2`), `108,050,895,689,694` (`N4`, `N8`). All proofs went through unchanged
    otherwise (`decLv4_sem` is parametric in `c₀`, `C ≤ 16`).
95. `FRXOut4` (new, 253 code lines): `Dec0`, `wF` (= `T4.fF (.node κ)` unfolded), `wAddr`, **`decF04_wF`**;
    `out_cells_dec0`, `out_cells_rows`; **`kSel`** (computable segment count) and **`kSel_eq`** (`= kAct`,
    via `Nat.find_eq_iff` and a `find?`-on-`range` lemma); **`stD`**, **`stD_of_pubCells`** (statements read
    from cells need no link: `digestOf_halves`); **`reassemble4 S aB`** (3.x's `ctbs` over `Sh`, every
    contribution fitted to its size by `qB4`, so the layout is trace-independent), `pf4`, `aBytes4 = 0`,
    **`pfHdr_reassemble4`** (S-E13a's `PfHdr`), **`reassemble4_size`**; **`LinksD4`**, **`sgnX`**, **`readW4 sg`**,
    `sgnX_eq`, **`readW4_eq`** (on `PubCells4` and `sig_of_H`, `readW4` is `.node c₁ c₂ (rd4 pf4 …)`).
    Pitfall: `ByteArray.extract` past the end is short, so a 3.x-style `reassemble` violates `PfHdr` on a short
    seed query; `qB4 = fitL n ∘ extract` fixes the length.
96. Coordinator's PATH-review notes applied to the plug's statement: `Open4` restated over S-E13a's route
    (`gap : Gaps4` = `StmtN4 → Gap4R` at `pf4`; `dec : ∃ D : NodeDec4 ndNone, Links4 ndNone D`, `Links4`
    named for S-L4); `resid4H_of` composes `I4`, `rd4 pf4`, `resid4_of ∘ gap4_of_rows`; `certificate_sub4` via
    `certificate_rev4H` (no `SegOut4`), `decOk4_ndNone` proved; `not_boundsOK_qV` at `qV4 − 1`. Pitfall:
    `X4.GoodX` is `Snd.X4.GoodX` from `FR.Sub4`.
97. Checks: `lake build FR Solution FRSubmission4Cert FRXOut4 FRXDec4F0 FRXLagT` green, 2,593 jobs
    (`build-final.log`); 28 axiom lines within the three (`axioms.log`, incl. `certificate_sub4`,
    `certified`); source rule 373 files, 0 findings. `FRXOut4` 11.6 s sequential. Not done: `outIR4`, `nd`,
    `nodeDec4_nd`, the plug of `nd`, item 4 (`tgBody_sem`, reflow). RESULT Part 31.
98. **S-H4 pass 8** (2026-10-29). HEAD `b562c50`, build tree `logs/fr-build-SH4g` (copy of `fr-build-SH4f`,
    `snap.sh` on HEAD; `MINE` adds `FRXSig4 FRXSig4H FRXSig4W`), logs `logs/S-H4g/`. Baseline (HEAD moved:
    RET-3) rebuilt to 2,598 jobs, green (`build0.log`).
99. **Q2 ruling applied: `sg := sigH`** (`FRXSig4`, new). `sigH κ σ w` reads H message bytes only
    (`hMB w b p` = byte `p mod 16` of element `4 + ⌊p/16⌋` of block `b`, rows 4–7, `hMB_dec0`): the index is
    `ofLE` of the key leaf's `j` field (block `wb 399`, bytes 1–8); `ots_i` = block `wb 3i`'s `x` field
    (bytes 11–42); sibling `t` = the `l` field (block `wb (466+2t)`, bytes 1–32) if index bit `t` is 1,
    else the `r` field (bytes 33–63 of that block, byte 0 of `wb (467+2t)`). All in rows 4–7: no extra rows.
100. **`sig_of_H`** (`FRXSig4H`, new): `StmtN4 … w → ∀ σ < 2, sigH κ σ w = readSig4 κ σ w`, **no hypothesis
    beyond `StmtN4`** — every H↔L equality has a row or family: index (`j` family `fam_byte`/`j_byte`, the
    index row `j_mirror`, `ofLE_enc64`); `ots` (`x` family, chain row `x_{i,0} = ots_i`); siblings (`l`,
    `r0`, `r31` families, the two mux rows by the index bit `idx_bit`, `r31_byte`). The node rows' truth
    `xRows_of_stmt` is S-E13a's fold split (`xOkK`, `rejR`) as in `wots_aggPad_of_rows`. Corollary
    **`readW4_sigH`**: on `StmtN4` at `wF κ L es`, `readW4 sigH κ L es = .node c₁ c₂ (rd4 pf4 …)` (for S-L4).
    Pitfalls: names `hB`, `rH`, `sibH`, `hB_eq` already exist in `FR.X` (3.x `FRXOut`), `shW` in `FR`
    (`FRShift`): renamed `hMB`, `hMD`, `rFH`, `sibFH`, `shWd`; `W4.idxOf` vs `FR.idxOf` (qualify).
101. **The signature's output words** (`FRXSig4W`, new, item 2's first piece): H's message slots as a byte
    stream (`hMBs`, block `⌊p/64⌋`) and word stream (`hMW w n`: word `n mod 2` of element `4 + (n mod 8)/2`
    of block `⌊n/8⌋`); the machine's shifted pair `shWd W s n = (W n >>> 8s) + (W (n+1) <<< (64 − 8s))`;
    **`wOf_hMBs`** (any `0 < s < 8`, via `shift_digit`, `shWd_byte`), **`packBytes_hMBs`**,
    **`sigWords_sigH`**: `sigWords (sigH κ σ w) = shWd 1 (8·b₃₉₉) :: ⋃ᵢ 4×shWd 3 (8·b_{3i}+1+j) ++
    ⋃ₜ 4×shWd 1 (8·b_{466+2t} + (bit ? 0 : 4) + j)` (the `r` field runs into the next block, as the stream
    does). Heap side: **`hAddr_eq`** (3.x's `addrW` shape `(3,3,2)` at stride `2^(mLog 0 + 1)`, base
    `ob + 3·stride`), **`hMW_heap`** (from `decF04_wF`'s conclusion).
102. Checks: `lake build FR Solution FRSubmission4Cert FRXSig4H FRXSig4W` green, **2,601 jobs**
    (`build1.log`); 15 axiom lines within the three (`axioms.log`, incl. `certificate_sub4`, `certified`,
    `sig_of_H`); source rule 380 files, 0 findings. Sequential: `FRXSig4` 8.8 s (2.5 s kernel: the
    `decide +kernel` control), `FRXSig4H` 7.6 s, `FRXSig4W` 11.0 s (`profile-*.log`). `FRSubmission4Cert`
    imports the two (doc updated; `Open4` unchanged).
103. Not done: `outIR4` (beyond the signature's pure half), `FRXNd4`, the plug, item 5. RESULT Part 32 §6 is
    the handover with the design worked out (the chain stream is the same H message word stream, so one
    shifted, redirected loader serves the signature, the traces and the proofs).
104. **S-H4 pass 9** (2026-10-29). HEAD `cb849a3`, build tree `logs/fr-build-SH4h` (copy of `fr-build-SH4g`,
    `snap.sh` on HEAD; `MINE` adds `FRXOut FRXOutRun FRXTr4 FRXPf4 FRXOut4W` and the names reserved for
    `FRXOut4R FRXNd4 FRSubmission4Fin Solution`), logs `logs/S-H4h/`. Baseline `build0.log`: 2,602 jobs, green.
105. **Design choice for the shifts and the redirect: a realign buffer, not a shifted loader.** Segment `i`'s
    trace starts at stream byte `1 + i(segB − 1)`, i.e. byte shift `i(segB − 1) mod 8 ∈ {0, 7, 6, 5}`. Instead
    of a byte shift and redirect registers inside `FRXOut`'s `ldw` (which would change `LW`/`Prot`/`Ctx` and
    every 3.x proof that threads them), the output will (a) copy `finBlk`'s 8 message words onto the main
    chain's last block (a no-op when `k = maxK` and for a previous node), (b) realign segment `i`'s `segB`
    bytes into an aligned scratch buffer (`vS`, one runtime loop, shift amounts in registers:
    `lo = H(n) >>> 8s`, `hi = (H(n+1) <<< 1) <<< (63 − 8s)`, which is `0` at `s = 0`), (c) run 3.x's `segIR`
    over the buffer with the linear shape `⟨0, 1, 1, _⟩` (`addrW = R + n`). The only `FRXOut` edit is the row
    stride (`AP.st`), needed for the H loader at `2^(mLog 0 + 1)`. Deviation from the pass-8 ruling's letter
    ("byte shift and redirect registers in `AP`"), not its intent (`segIR_sem` carries over unchanged).
106. **`FRXOut` in place:** `AP` gains `st` (row shift); `addrW`/`ldPs` use `toWord ap.st` for the literal `18`;
    `apS := ⟨3, 3, 2, 18⟩`, `apL := ⟨63, 7, 1, 18⟩`. Every 3.x statement unchanged (the exact costs
    `cost_outIR = 21,609,039`, `outs_outIR`, `sizeIR_outIR` re-decided as before). `FRXOutRun FRXNode
    FRXNodeRun` rebuilt green.
107. **`FRXTr4` (new, 160 code lines):** 3.x's trace-word lemmas over any word list `Ws` and any `S`:
    `entryW_alignedL`, `readItems_wordsL`, `entryW_seedL`, `trW_eqL`; `tPh4`/`tSegs4` over `Sh` with `S.lv`,
    `segOut_tPh4`, `segOut_tSegs4`, `itemsOf_cons`; `trSeg4 S`, `TrOk4 S` (decided: `trOk4_seq4`, via a Bool
    `all` — a plain `decide +kernel` on the `∀ ∈` hits deep recursion over 8,905 items); **`logWords_trSeg4`**.
    Control `trOk4_ctl`: `seq4` with a 33-byte `E4end` fails.
108. **`FRXPf4` (new, 434 code lines):** 3.x's `proof_words` over `reassemble4 S` (`ctb4`/`ctbs4`, fitted
    slices `qB4`, `sib4`/`posOf4` at the kind's ladder `m`), `sOff4`, `wo4`, `pPh4`, `pRest4`, `fSeg4`, `pSeg4 S m`,
    `qHead4`/`qOk4`, `PfOk4` (decided, `pfOk4_seq4`), `LadOk4 S m` (`ladOk4_seq4` for `m ∈ {30, 31, 32}`),
    `mOfB` (`mOfB_mem`); `qBytes4`, `fitL_self`, `cpSlice4`, `ans_bit4`, `sib_one4`, `pPh4_spec`, `pRest4_spec`,
    **`trM4_eq`** (the ladder is `mOfB` of word 10's low byte), **`proof_words4`**. Pitfall: an inline
    `match` in a hypothesis elaborates with extra discriminants (`hd`, `hns`) and cannot be passed on; name it
    (`qHead4`).
109. **`FRXOut4W` (new, 248 code lines):** `vS κ σ k i w` (segment `i`'s `segB` stream bytes from
    `i(segB − 1)`, packed), `readItems_drop`, `readItems_take`, `wordsBytes_packBytes8`, **`segTr_eq`**
    (`segTr = trOf seq4 (vS …)`), `pf4_words`, `logWords_segTr`, `entries_segTr`, `trBody4`, `hdrWords`,
    `aggHdr_words`, `hAn_lt`; **`signedWords_prev`**, **`signedWords_agg`** (`k = kSel`), **`witWords_readW4`**,
    **`readW4_fits`**. Pitfalls: `show`/`congr 1` on `sgnX`/`aggPf` goals time out in `whnf` (they unfold
    `pf4`): state `sgnX_π`, `sgnX_tr`, `aggPf_eq` as `rfl` lemmas over variables and `rw`; use
    `List.map_congr_left` as a rewrite instead of `congr`.
110. Measurements (scratch `#eval`, `logs/S-H4h/SegSz.lean`, outside the entry): compiled `pSeg4 seq4 32` is
    4,940 statements (its field 17, the siblings, 1,245), `trSeg4 seq4` 4,904; `segLen` 99,774 and 185,345
    words; `depthSeg = 1`; `okSeg` holds at all three ladders; cost 4,186,985 and 6,603,369 steps. Output
    bound: ≤ 2.3·10^6 words against `outCap = 2^24`.
111. Checks: `lake build FR Solution FRSubmission4Cert FRXOut4W` green, 2,609 jobs (`build-final.log`); 20
    axiom lines within the three (`axioms.log`, incl. `certificate_sub4`, `certified`, `proof_words4`,
    `signedWords_agg`); source rule 384 files, 0 findings. Sequential (`-DElab.async=false`, wall incl.
    imports): `FRXTr4` 11.1 s, `FRXPf4` 14.9 s, `FRXOut4W` 9.3 s (`profile-*.log`).
112. Not done: the machine half of `outIR4` (chain words ↔ heap, the copy, the realign loop, kSel, header,
    signature and statement emitters, `outIR4_sem`, cost), `FRXNd4`, the plug (coordinator's ruling:
    `FRSubmission4Fin`), item 4. RESULT Part 33 §7 is the handover.
113. **S-H4 pass 10** (2026-10-29). Started on HEAD `91d74b0` with pass 9 uncommitted in the worktree (snapshot
     + `MINE` symlinks); pass 9 landed as `8e88890` during the pass, HEAD `1f400d9` at the end; re-snapshotted and
     rebuilt green (2,614 jobs). Build tree `logs/fr-build-SH4i` (copy of `SH4h`), logs `logs/S-H4i/`; `e.sh`
     prints only a module's errors.
114. **Item 1 (`FRXOut4C`, 85 code lines):** `chW`, `chainBytes4_getD`, `vS_get` (the virtual word is
     `shWd chW (D mod 8) (⌊D/8⌋ + u)` at every shift, `shWd_zero`), `hAe_words`, `hAn_word`. Pitfalls: a literal
     `List.range 41`/`ofLE` over `List.range 8` unfolded by `simp`/`ring` hit kernel deep recursion (3.5 min, then
     the error); a generic `streamBytes_getD'` and an inductive `ofLE_range8` fix both.
115. **Design change: the redirect in the loader, not `finCopy`.** `ldIx cb jL Δ n = n + cb + [⌊n/8⌋ = jL]·Δ`,
     three registers; `Δ = 0` except an aggregate with `k < maxK`. H is never written; one frame `OF` (heap below
     `bufB = 2^27` kept) holds for the whole output. Buffer shape `apB = ⟨3,3,2,20⟩` (3.x's stream shape: `hA` holds
     for every word; a linear shape would wrap at `2^64` and fail `segIR_sem`'s `hA`).
116. **`FRXOut4R` (429 code lines):** `ldC_sem`, `rlBody_step` (one realigned word: two loads through the loader,
     `shr`/`shl`/`shl`/`add`, the address block, the guarded store; ≈ 150 lines of register bookkeeping),
     `realign_sem` (setup block, `loopK_emit` with `RlInv`). Pitfall: a Python patch that replaced up to the end of
     the file dropped `end FR.X` and silently made a later append a no-op (the file still elaborated); re-appended.
117. Checks: build green (`build2.log`), 11 axiom lines within the three (`axioms.log`), source rule 389 files,
     0 findings.
118. Not done (context): the emitters (`shwIR`, `sigIR`, `pfIR` ladder, `kSelIR`, statements), the child programs,
     `outIR4_sem`, cost/size, `FRXNd4`, the plug, item 6. RESULT Part 34 §6 is the handover.
119. **S-H4 pass 11** (2026-10-29). Started on HEAD `1f400d9` with pass 10 uncommitted (worktree symlinks); pass 10
     landed as `7a0afa8` during the pass, HEAD `b4d7457` at the end (no other `lean/` change). Build tree
     `logs/fr-build-SH4j` (copy of `SH4i`, `snap.sh` on HEAD), logs `logs/S-H4j/`; baseline `build0.log` 2,614 jobs.
     Ruling on pass 10's Q1 (loader redirect `ldIx` instead of `finCopy`) accepted.
120. **Emitters (`FRXOut4E`):** `shwC κ` is the realign body without the store (`oX := shWd (ldG …) s n`, `ldG` the
     loader's word); `shwO` emits and steps `qN`, `shw4` four of them; `ldA`/`outAs` emit heap words at constant
     addresses; `loopK_emitR` (count `k ≤ K` in a register: `entryK_countR`, the `ltu` branch). The signature
     `sigIR κ σ = sigHd; otsIR; pathIR` (index word kept in `qIx`; 133 chains × 4 shift-3 pairs, `qN += 20`; 16 levels,
     `qN := qP + 4 − ((idx >>> t) &&& 1) <<< 2`, `offB_eval`): `sigIR_sem` = `sigL` over the heap's H words.
     Pitfalls: `rw` after which the goal is `toWord (8·(b+399)) = toWord (8b+3192)` makes `rw`'s closing `rfl`
     recurse through `Nat.mul` on a let-bound `b` (max recursion): state the index equalities in the exact target
     form first; `trivial` tries `decide` on such goals (same); a single 120-line proof hit a kernel deterministic
     timeout, split into `sigHd_sem`/`otsIR_sem`/`pathIR_sem` it checks.
121. **Buffer, ladder, count (`FRXOut4F`, `FRXOut4K`):** `bufSeg sg = setB; segIR apB 0 sg` (`seg_step` over the
     buffer); `pfIR = setB; ladF; ite qF0 (pfS 30) (ite qF1 (pfS 31) (pfS 32))`, three copies of `pSeg4` (14,878
     statements) instead of a field-17 split; `mOfB_eq` (case split over the six kind bytes), `low_iff`. `kSelIR κ a n`
     (unrolled, `alive &&= [Σlo = 1 ∧ Σhi = 0]`, `qK += alive`; `F_one_iff`, `sum3_one`: F addition is XOR, rfl);
     `kc_find`: the running count is `find?`'s index, so `qK = kSel`.
122. **Children (`FRXOut4P`, `FRXOut4A`):** `HeapW` (decF04_wF's conclusion), `hMW_heapW` (blocks below `hEnd`),
     `ChR` (loader = chain words, blocks below `hEnd` up to a bound), `rl_vS` (after `realign`, `vS … = src M apB bufB`
     on the segment), `prevIR_sem` (= `signedWords_prev`), `chR_prev`, `sigL_eq`, `idx_word`; `aggHd_sem` (header via
     `hAn_word`, `hAe_words`), `aggRegs_sem` (`qJ = ⌊k(segB−1)/64⌋`, `qDl = dV`), `chR_agg` (redirect correct for
     `1 ≤ k ≤ maxK`), `segLoop_sem` (generic: realign + emitter per segment, outputs as pure functions of `i`), `aggIR4_sem`
     (= `signedWords_agg`). Finding: `c_A` is H's last block for the last aggregate (`cAB + 1 = hEnd`); the header
     reads stay inside it.
123. **`FRXOut4O`:** `outIR4 κ` (tag, `outAs (stA κ)`, child 0, child 1), **`outIR4_sem`** (= `witWords (readW4 sigH κ L es)`),
     WF, NoLoopT; costs from components (`decide +kernel` on `pfIR`, both trace segments; the rest `decide +kernel` per
     kind): `cso_outIR4` cost ≤ 6·10^8 (exact 163,163,886 / 289,278,962 / 504,585,753), outputs ≤ 2.3·10^6, size ≤ 45,000.
124. **`FRXNd4`:** `nd := ndK4 (decF04 κ; outIR4 κ)…`, `decOk4_nd`, `nd_out`, `nodeDec4_nd := ⟨LinksD4, readW4 sigH, …⟩`.
     Pitfall: closing `[] ++ witWords X = witWords X` by `rfl` made the kernel unfold `witWords (readW4 …)` (deterministic
     timeout); `rw [Array.toList_empty, List.nil_append]` instead.
125. **The plug:** `FRSubmission4` (`ext4With nd`, `E4X nd`), `FRSubmission4Cert` (`Open4.dec : Links4 nd nodeDec4_nd`,
     `certificate_sub4` with `decOk4_nd`), new `FRSubmission4Fin` (`Open4F := Gaps4`, `open4_of_F` via `links4_sigH`,
     `certificate_sub4F`, `certificateR_sub4F`), `Solution.certified (h : Open4F)`, `FR` imports `FRSubmission4Fin`.
126. **Controls (`FRXOut4Ctrl`, `FR` only):** `redirect_ctl`, `ladder_ctl`, `offB_ctl`, `kc_ctl`, `nd_ctl`; in the certificate's
     closure `FRSubmission4Fin.nodeDec4_nd_parts`, `sub4_ext_ne_none`, `FRXNd4.nd_ne_ndNone`.
127. **Kernel traps** (first sequential profile: `kStep_sem` 70.6 s, `aggIR4_sem` 97.8 s of type checking): (a) a hypothesis
     about `rd t.M (selA … + j)` used at `j = 0` against `rd t.M (selA …)` — the kernel unfolded `selA`/`wAddr` on both
     sides; (b) `set V := fun i u => (vS …).getD u 0` — checking `hV` re-evaluated `vS` (chain bytes). Fixed (exact forms;
     opaque `V` by `obtain ⟨V, hVd⟩ : ∃ V, V = …`): 0.3 s and 3.0 s. Dropping `at *` from the dischargers did not matter.
128. Checks: `lake build FR Solution FRSubmission4Fin` green, 2,623 jobs (`build3.log`); 18 axiom lines within the three, no
     `sorryAx` (`axioms.log`, incl. `certificate_sub4F`, `certificate_sub4`, `certified`); source rule 398 files, 0 findings.
     New kernel time ≈ 51 s (35.6 s of it `sizeIR_decF04`).
129. **`Open4F = Gaps4`** exactly; `certified (h : FR.Sub4.Open4F)`. Not done: the `tgBody_sem` split. RESULT Part 35.
