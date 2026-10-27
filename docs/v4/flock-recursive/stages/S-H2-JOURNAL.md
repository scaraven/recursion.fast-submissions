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
