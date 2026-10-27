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
