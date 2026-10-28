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
