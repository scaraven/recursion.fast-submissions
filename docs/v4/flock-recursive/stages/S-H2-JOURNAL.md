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
