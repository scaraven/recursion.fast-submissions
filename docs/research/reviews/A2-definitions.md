<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A2-definitions.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A2: adversarial review of the security definitions (soundness, non-vacuity, auditability)

Reviewer: A2. Date 2026-10-10. Scope: `design/DESIGN.md` v0.1 (decisions in force, including the orchestrator
overrides: BabyBear, `errorCap = 2^-128`, leaf-returning QUERY), `design/D1-security.md` (all of it),
`probes/d1-probes/LocalDefs.lean` (every line) and its `RESULT.md`, `design/D2-cost-incentives.md` §2 and §3.1,
`notes/R4` §3, §3.6–3.8, `notes/R5` §3.3 and §7.3, `notes/R7` §1, and `notes/R1` §3–4. I also cross-checked
`reviews/A1-incentives.md`.

Primary sources I checked myself:
- **Chiesa–Yogev book**, version of 2026-03-25: Def. 23.2.1–23.2.5, 31.1.1, 31.1.2 and 31.1.6; Thm. 25.2.1, 26.1.1,
  31.2.1, 31.3.1, 32.8.9 and 32.8.10; Lemma 18.5.10.
- **WARP**: Bünz–Chiesa–Fenzi–Wang, *Linear-Time Accumulation Schemes*, ePrint 2025/753, version of 2025-05-28.
  I checked Def. 2.6/2.7, Thm. 2.8, App. B (Def. B.1/B.2, Thm. B.4, Construction B.5, Claim B.6) and App. C.

**Method.** I read every definition as an adversarial submitter would. Where an attack exists I built it in Lean against
a verbatim copy of D1's definitions.

**Evidence.** All evidence is in `probes/a2-probes/A2Probes.lean` (1,040 lines). Lines 3–505 are
`LocalDefs.lean:16-518` verbatim (checked by `diff`). My sections A–F follow. To rebuild, run
`probes/a2-probes/build.sh`; it assembles the file from `_LocalDefsBody.lean` + `_part{A..F}.lean`. It runs as
`cd /home/devops/Verified-zkEVM/leanerVM && lake env lean <file>`, takes 13.6 s wall and 3.5 GB, and is sorry-free.
Every theorem below prints `[propext, Classical.choice, Quot.sound]`.

| § | Lean artefact (A2Probes.lean line) | What it shows |
|---|---|---|
| A | `flagged_secure` (544), `flagMachine_agrees` (564), `flagMachine_accepts_false` (578) | `Secure` + `Agrees` hold, and the machine accepts a false statement |
| B | `hitRed_secure` (666), `hit_reject_card` (680), `hit_reject_le_half` (692) | with no round cap, `Secure` holds at `ε = errorCap` while soundness error ≥ 1/2 |
| C | `trivialAcc0_secure` (782), `fullRecAcc_secure` (823) | `accLen ≤ accCap` is decorative; the full R1CS instance is the accumulator |
| D | `SF.rbrKS_of_rbr` (898) | RBR *soundness* + brute force ⇒ the contract's RBR-KS, same ε, any verifier |
| E | `chain_extracts` (975) | **positive**: the local KSF gives straight-line backward extraction (WARP Claim B.6) |
| F | `shapeSpec`, `shapeChalFintype` (1001–1040) | compiled skeleton of the main fix (contract-fixed round shapes) |

---

## Findings, ranked

### C1 (critical): `Secure` is blind to the serializer, and `Agrees` covers only typed transcripts, so the deployed machine may accept anything outside `ser`'s image

**Problem.** `Protocol` (LocalDefs:242-258) has submitter-chosen message types `pSpec.Type j` and a serializer
`ser j : Message j → Fin (msgLen j) → F`.
- `Protocol.Secure` (:272-277) never mentions `ser` or `msgLen`.
- D1 §1.4's `Agrees` quantifies over `tr : P.pSpec.FullTranscript`, i.e. only over machine inputs of the form `ser ∘ tr`.

The real adversary of a compiled verifier commits to *arbitrary* strings in `Σ^l`. This is the IOP model of every theorem
D1 cites: CY Def. 23.2.1 says "`(Π1, …, Πi)` are IOP strings", and WARP Def. B.1 has the same quantifier. On strings
outside `range (ser j)` the machine is constrained by `Terminates` alone.

**Lean counterexample (§A).** `flagged` is the toy "send the witness" protocol with `ser w := Fin.cons 1 w`, i.e. a
flag word `1` is prepended.
- `flagged_secure` is proved by *the toy's own proof terms*, because `Secure` reads none of the changed fields.
- `flagMachine` accepts whenever the flag word is not `1`, and otherwise checks R1CS on the tail.
- `flagMachine_agrees` proves D1's decision agreement on every index, instance and typed transcript.
- `flagMachine_accepts_false` proves that, for `badIndex` (unsatisfiable at every size with `m ≥ 1`), the all-zero proof
  string is accepted.

So `Secure ∧ Agrees ∧ Terminates` holds for a deployed verifier that accepts a false statement with an empty proof.

**Why the 3-line transfer lemma does not rescue it.** D1 §1.4 says "`Agrees` + `Secure P` ⇒ the machine verifier (as a
pure verifier) satisfies the same `Secure`". That is true, but only for the machine *restricted to typed transcripts*. The
object that BCS/COS compile is the machine on raw strings. The transfer needs `ser` to be surjective (for messages) and a
measure-preserving bijection (for challenges, C2). Neither is stated, and the typed-message style that ArkLib encourages
(subtypes, `Polynomial`, structured records) violates them by default.

A1-C1 found the same gap as a cost exploit ("typed promise", which gives free proximity). The Lean evidence here shows
the stronger consequence: soundness of the deployed verifier is lost outright, and no cost analysis is needed to see it.

**Fix (cheap; compiled skeleton in §F).** The submitter declares a *shape* and the contract owns the types:

```lean
inductive Round | msg (len : ℕ) | chal (k : ℕ)          -- prover oracle of len elements | k elements of Ext
def Round.ty : Round → Type | .msg len => Fin len → F | .chal k => Fin k → Ext
@[reducible] def shapeSpec (sh : Fin n → Round) : ProtocolSpec n := ⟨fun i => (sh i).dir, fun i => (sh i).ty F Ext⟩

structure Protocol (sz : Sizes) where
  n : ℕ
  n_le : n ≤ roundCap                                   -- C3
  shape : Fin n → Round
  leaf : (j : Fin n) → ℕ                               -- machine-only (QUERY granularity)
  vkLen : ℕ;  vkLen_le : vkLen ≤ vkCap;  VK : Index F sz → Fin vkLen → F
  idxLen : ℕ;  IDX : Index F sz → Fin idxLen → F
  prover : Strategy (Index F sz × PubInput F sz) (Wit F sz) Unit Unit (shapeSpec F Ext shape)
  verify : (Fin vkLen → F) → PubInput F sz → (Fin idxLen → F) → (shapeSpec F Ext shape).FullTranscript → Bool
  WitMid : Fin (n + 1) → Type
  E : Extractor.RoundByRound … (shapeSpec F Ext shape) WitMid
  ε : (shapeSpec F Ext shape).ChallengeIdx → ℝ≥0
```

There are no `ser`, `msgLen` or `chalFin` fields. A typed transcript now *is* an assignment of oracle contents and tape
challenges, so `Agrees ∀ tr` quantifies over every adversarial string. Submitters who want structured messages decode
inside `verify`, which is what the deployed verifier must do anyway.

### C2 (critical): challenge types and their tape encoding are undefined in the Lean text, and every natural harness rule breaks soundness or the trust path

**Problem.** D1 §2.1 promises "a serializer `serC`". `Protocol` has no such field, so the tape contents (D1 §1.4
`challengesOf P tr`) are unspecified. The harness must sample "uniformly from `pSpec.Challenge i`", which is an
arbitrary submitter `Fintype`.
- **(a) Sample the type.** This needs candidate code (an enumeration, possibly noncomputable) on the trust path,
  contradicting D2-4. A1-M1 notes the same, and also notes that `serC` gives free verifier work.
- **(b) Sample the codomain of `serC` uniformly.** Out-of-image tapes then occur with high probability, and `Agrees` is
  silent on them. Counterexample (not compiled; it has the same shape as §A): add one challenge round of type `Unit` with
  `serC () := (0,0,0,0,0)`. The spec stays the toy, so `Secure` holds with `ε = 0`, and the machine accepts whenever the
  tape challenge is non-zero. Acceptance probability is `1 − p^-5`.
- **(c) A non-injective `serC` with pushforward sampling** is sound: acceptance depends only on `serC c`, and the
  pushforward of uniform is what the spec measures. But the harness cannot compute the pushforward without running
  candidate code.

**Fix.** Same as C1. Challenge types are `Fin k → Ext`, with `Ext` the contract's degree-5 binomial extension of
BabyBear. Serialization is the contract's little-endian canonical one, and sampling uses ≥ 128 hash bits per base
coefficient (D1 §3.1). `[Fintype]`/`[Nonempty]` become derived facts (`shapeChalFintype`, §F), not submitter data. If
A1's challenge menu is adopted (`(Fin d → F)^a × (Fin 2^b)^c`), it slots in as more `Round` constructors.

### C3 (critical, cheap fix): no bound on the number of rounds; the per-round cap then bounds nothing

**Problem.** `ε i ≤ errorCap` caps each round. Interactive soundness is `≤ Σ_i ε_i` (CY Claim 31.1.3), and the compiled
bound is `(t + k)·max ε`. Neither `Protocol` nor `Reduction` bounds `n`. DESIGN §6's "rounds ≤ 2^10" is a harness
admission rule, not a Lean clause.

**Lean counterexample (§B).** The protocol has `k` challenge rounds in `Fin (2^130)`, no prover messages and the empty
relation, and accepts iff some challenge is `0`.
- `hitRed_secure` is the full `Reduction.Secure` at `ε = errorCap` for every `k`. The state function is "a zero has
  appeared"; each round has at most one bad challenge.
- `hit_reject_card` shows that exactly `(N−1)^k` of the `N^k` transcripts reject.
- `hit_reject_le_half` shows `2(N−1)^N ≤ N^N`. So at `k = N` the false statement is accepted with probability ≥ 1/2,
  and the transcript space is the challenge space because there are no prover messages.

D1 §2.4 says "A submitter cannot make the cap vacuous". That is false as the Lean text stands. On the base track the
attack is blocked only incidentally, by the tape cap, *if* `serC` were injective (C2). On the accumulation track
(`Reduction`, :407-416) nothing blocks it.

**Fix.** Add `n_le : n ≤ roundCap` to `Protocol` and `Reduction` (C1 sketch), with `roundCap` the same constant used in
the headline bound. In the tree theorem, `k_tree` is the composed round count and must be stated, not left implicit.

### M1 (major): G4. The local RBR-KS does imply the hypothesis needed, but not via the theorem cited. The knowledge headline has unbounded extraction time. The fix D1 proposed (`full`-iff) is unnecessary.

1. **CY Thm 31.3.1 does not apply as cited.** Its hypothesis is CY Def. 31.1.6. That definition requires:
   - a *witness-free* state function `RBRState(x, trc)`;
   - a single *polynomial-time* extractor `E(x, (Π_j)_{j∈[k]})` that sees all prover strings but *no* verifier
     challenges;
   - the event `(x, w) ∉ R ∧ State flips 0→1`.

   The local `KSF` has a witness-indexed state and a per-move backward extractor that reads challenges, with no
   efficiency requirement. It is not an instance of Def. 31.1.6, and I see no generic conversion: the backward chain
   needs the challenges.
2. **The right citation is WARP Thm B.4 with Construction B.5** (ePrint 2025/753, App. B). Its SR extractor is the
   backward chain `w_k := w′, w_{i−1} := E_rbr(x, π1ρ1…πiρi, w_i)`. Its proof (Claim B.6) uses exactly:
   - `full` in the direction "accepted with output witness ⇒ state true";
   - prover moves in the direction "state true after ⇒ true before";
   - `empty` in the direction "state at ∅ ⇒ in R";
   - the per-move bound, worst case over prefixes, with a union bound over the ≤ `t + k` distinct moves.

   ArkLib's two deviations (`extractMid` at prover moves; one-directional `full`) are harmless.

   **Mechanized (§E):** `chain_extracts` proves, for the *local* definitions, that an accepting full transcript in which
   no challenge is bad for its own prefix yields `(s, cast E.eqIn (chain … 0)) ∈ relIn`. Here `chain` is the
   reverse-induction composition of `extractOut` and every `extractMid`, including those at prover moves. That is
   Claim B.6. The rest of Thm B.4 is the union bound.

   So D1 G4's proposal "if the knowledge version needs the `full` iff, add it" is **not needed**. WARP Def. 2.7 states
   an iff but its proof never uses the other direction. Do not add it: it would make honest KSFs harder to write and
   buys nothing.
3. **Efficiency is the real gap.** WARP Def. 2.7 ("efficient deterministic extractor") and CY Def. 31.1.6
   ("polynomial-time") both require it. Thm B.4/CY Thm 32.8.10 then give `et_ARG = Σ et_i + et_MT + O(r·k·t log t)`.
   With an arbitrary Lean extractor `et` is unbounded, and by M2 it is in effect brute force. So the compiled
   *knowledge* statement holds only with an unbounded extractor, which is not a knowledge statement in the
   computational sense.

   The compiled *soundness* statement is fully justified:
   - KSF ⇒ witness-free RBR soundness with the same ε. Take `State(s, tr) := ∃ w, toFun m s tr w`; the laws transfer
     directly, and the bad events coincide by definition of `Bad`.
   - CY Thm 31.2.1 gives SR soundness `(t+k)·ε`.
   - CY Thm 32.8.9 gives `ε_ARG ≤ (t+k)·ε + 4.5t²/2^λ` (+ the side conditions of m1).
4. **Citation slip.** CY Thm 32.8.9 is the holographic *soundness* theorem. Holographic *knowledge* is Thm 32.8.10,
   straight-line case, whose hypothesis is CY Def. 32.6.4. Def. 32.6.4's extractor receives `(i, x, Π, σ, ρ, tr_sr)`, so
   the backward chain qualifies.
5. **Adaptivity is fine.** In the SR game the adversary chooses `(i, x)` adaptively (CY Def. 32.6.4, WARP Def. B.1).
   The local `RbrKS` is `∀ s ∀ i ∀ tr` (worst case over statements and prefixes), which is exactly WARP's `max` over
   the statement set `Z`.

**Fix (wording plus one non-trusted lemma).**
- DESIGN §4 should state the headline as *soundness*: CY 31.2.1 + 32.8.9, unconditional. State *knowledge* as "WARP
  Thm B.4 + CY 32.8.10 with an extractor of unbounded running time (L1); polynomial `et` only on the L2
  efficient-extraction track".
- Move `chain_extracts` into `Bridge/` together with the interactive corollary (knowledge error `Σ_i ε_i` by a union
  bound over rounds). That corollary is also a cheap independent sanity check of the definition.

### M2 (major, known but now formal): the named computable extractor adds no content; L1 "knowledge soundness" equals RBR soundness exactly

**Lean (§D).** `SF.rbrKS_of_rbr`: for *any* verifier with a witness-free RBR-soundness state function at errors ε
(counting form), and any witness finder `bf` that succeeds on the language, `SF.toKSF bf` is a local `KSF` with
extractor `bfE bf`, and `RbrKS` holds with the *same* ε. For R1CS over BabyBear, `Wit sz` is finite and `R1CS` is
decidable, so a computable `bf` exists by enumeration. D1 §2.5's computability gate therefore excludes nothing.

The converse also holds (M1.3). So at L1, `Protocol.Secure` = perfect completeness + worst-case RBR **soundness** + cap,
and the `E` field is decoration.

Consequences:
- **Report wording.** "Information-theoretic knowledge soundness with a named extractor" invites a reading the theorem
  does not support. Say "RBR soundness; extractor named but unconstrained (L1)".
- **Accumulation track.** One-step certificates certify RBR *soundness* reductions `L(rel) → L(Racc)`,
  `L(Racc)² → L(Racc)`, `L(Racc) → ⊤`. In the IT model these compose to soundness of the tree, which is meaningful.
  Recursive deployment needs extraction with polynomial `t_E` (CGSY24's `N·t_E`), so the L2 extractor track is what
  gives T2 records security meaning. Elevate it in the roadmap, or label T2 records "IT soundness only".

Positive corollary: `WitMid` and state-function freedom (types that "encode the future", `toFun ≡ True` after round 0,
and so on) cannot weaken soundness. `chain_extracts` is generic in `WitMid`, and `acceptAll_no_KSF` plus §B's analysis
show that every escape must be paid for at some challenge round.

### M3 (major): the accumulation track's caps and machine interface are not in the definitions

1. **`accLen ≤ accCap` is decorative.** `Accumulation.Secure` (:451-454) never mentions `serAcc` or `accLen`, and
   `serAcc` is unconstrained. **Lean (§C):** `trivialAcc0_secure` is a full `Accumulation.Secure` whose accumulator
   *statement* is an entire R1CS instance `(A, B, C, x)` (3·m·cols + nx elements), with `accLen = 0` and
   `serAcc := Fin.elim0`. D1 §4.3's "the size cap is what forces this baseline to do work" does not hold in the text.
2. **If the cap is made real (injective `serAcc`), D1's trivial baseline violates it.** Its accumulator contains the
   index. The real trivial baseline is "full recursion": `Racc := univ` over `Unit`, `embed` = the whole verifier,
   `fold` = `decide` = accept-all. **Lean:** `fullRecAcc_secure`. It satisfies any cap and scores
   `C_leaf + 0 + 0` = T1 cost. This is not an exploit, since each deployed node must verify a full proof, but it is the
   baseline T2 must beat.
3. **The leaf verifier is not holographic.** `embed : Reduction (Index × PubInput) …` gives the verifier the whole
   index as a Lean value. The base track's `VK`/`IDX` discipline (`vkLen ≤ vkCap`, `IDX` only via priced QUERY) is
   absent. The same holds for `fold`, which reads arbitrary `AccStmt` values for free (ots.golf's free-lookup-table
   lesson).
4. **The output-oracle "selection" is uncompiled, and decision-only `Agrees` is insufficient for reductions with
   outputs.** The fold verifier's output statement must be pinned by an output-agreement clause, and the transfer lemma
   must transport `serAcc (V s tr)`, not just `isSome`.

**Fix (sketch).**

```lean
structure AccShape (sz : Sizes) where
  plain : ℕ;  plain_le : plain ≤ accCap sz          -- A1-m4: make accCap constant 2^12
  r : ℕ;  r_le : r ≤ accOracleCap;  oLen : Fin r → ℕ  -- accumulator oracles, fixed shape per size
abbrev AccStmt (sh : AccShape sz) := (Fin sh.plain → F) × ((j : Fin sh.r) → Fin (sh.oLen j) → F)
-- embed's input statement is (VK i, x) with IDX i as oracle 0, exactly as in `Protocol`;
-- fold's output oracle part is `sel : Fin sh.r → InputOracleRef ⊕ (shape message index)`, and its
-- spec verifier must output `(plainOut, fun j => resolve sel j)`; Agrees includes plainOut equality.
```

In the IT model the oracle part is passed as a full value, as in ArkLib's `OracleStatement`. On the machine it is
reachable only through QUERY. All three reductions use C1's shapes and C3's round cap.

### M4 (major): the indexer is an arbitrary, possibly noncomputable Lean function, so the certified statement can be about a VK nobody can compute

`VK`, `IDX : Index F sz → …` (:249-251) are unconstrained.
- The security theorem then holds for verifiers whose honest key is, e.g., `IDX i := fun x => decide (∃ w, R1CS i x w)`:
  a satisfiability table. With M2's brute-force extractor the KS proof is trivial. A1-n2 notes it fits at `nx ≤ 1`.
- In deployment the key must be computed by someone. D2 §2.1's check "native indexer reproduces the spec byte-for-byte"
  cannot be executed for a noncomputable spec (A1-M3: VK/IDX backdoors).
- This does not move the *score*, which is worst case over the class. It does make the certified object potentially
  undeployable, and every security claim is relative to that key.

**Fix.**
- `VK`, `IDX` (and `Strategy`) pass the same computability gate as `E`: no `noncomputable`, and no `implemented_by`,
  `extern` or `csimp` in their closure.
- On the badge path the harness evaluates them (A1-M3's fix) and requires the native indexer's output to equal them on
  every benchmark index.
- Long-term (T3), a RISC-V indexer image with `Agrees`.

### m1 (minor): the derivation of the compiled bound is slightly wrong and missing its side conditions

DESIGN §4: `κ(t) ≤ (t+k)·2^-128 + 4.5t²/2^256 ≤ t/2^127 for k ≤ t ≤ 2^120`.

- **Arithmetic.** `(t+k)·2^-128 ≤ t·2^-127 ⇔ k ≤ t`, and the hash term is strictly positive. So at `k = t` the claimed
  inequality is false. It is correct iff `k + 4.5t²/2^128 ≤ t`. For `t ≤ 2^120` the hash term is
  `≤ 4.5·2^-8·t ≈ 0.018t`, so `k ≤ t/2` suffices with room to spare. Restate as "`≤ t/2^127` for `2k ≤ t ≤ 2^120`".
  With `roundCap = 2^10` this covers every `t ≥ 2^11`.
- **Side conditions.** The `3.5t²/2^λ` / `4.5t²/2^λ` simplifications in CY Thm 25.2.1/26.1.1/32.8.9/32.8.10 hold only if
  `t ≥ 2·l_0` and `t ≥ 2(log l + 1)·l`. With `ℓ_j ≤ 2^34` at k = 24 that means `t ≳ 2^40`. For smaller `t` use
  monotonicity of `κ^mm_MT` in `t`:
  `κ(t) ≤ (t+k)·ε + 4.5·max(t, t*)²/2^256` with `t* ≈ 2^41`. The extra term is `≈ 2^-171`, negligible, but the
  headline should be written with `max(t, t*)` or with the condition stated.
- **Citations.** For soundness use CY 31.2.1 + 32.8.9. For knowledge use WARP B.4 + CY 32.8.10 (M1). The `k` in these
  theorems is the number of (message, challenge) rounds, so it is ≤ `n`.

### m2 (minor): trusted cone and auditability

Line counts (`LocalDefs.lean`, code lines excluding comments, blank lines and the non-trusted bridge, toy and controls):

| Part | Code lines | Total lines |
|---|---:|---:|
| §1–2 (Strategy, transcript, completeness, KSF, Bad, RbrKS) | 47 | 86 |
| §4–5 (R1CS, Protocol, Secure) | 53 | 88 |
| §8 (Reduction, Accumulation) | 35 | 51 |
| **Security definitions, total** | **≈135** | **≈225** |

The fixes above add ≈40 code lines (Round/shape ≈15, caps ≈5, accumulator shape ≈20). With the machine (~150),
Refinement/Certificate (~55) and Budget (~10), the trusted contract is ≈390 code lines. That is in line with sig.golf
(412 code / 712 total, R2 §1) and about 1.8× ots.golf's RISC-V track (≈220 code lines, R1 §2.1). It is auditable in an
afternoon by a cryptographer with a Lean guide.

The imported cone is the problem.
- `LocalDefs` imports `ArkLib.OracleReduction.Security.RoundByRound` (to get `Extractor.RoundByRound`). That pulls the
  whole ArkLib security layer and VCVio into the trusted cone, contrary to D1 §2.6.
- Even `ProtocolSpec/Basic.lean` (944 lines) imports `OracleInterface` → VCVio, CompPoly `MvPolynomial`, and
  Schwartz–Zippel.
- Comparator compares only constants reachable from the statements. But instance resolution while elaborating the stub
  happens in this environment. ots.golf was bitten by a sorried instance reached through imports (R1 §4.3).

**Fix.**
- With C1's shapes the vocabulary needed is tiny: `Direction`, `Fin n → Round`, transcripts as
  `(i : Fin k) → (sh (castLE i)).ty`, `Fin.snoc`, `Fin.take`, and a 5-line local `Extractor`. Define it in
  `Contract/Vocabulary.lean` over Mathlib only.
- Prove `local ⇔ ArkLib` in `Bridge/`, as D1 already plans. This removes ArkLib from the trusted cone entirely.

Pitfalls a non-Lean cryptographer will trip on, each needing one line of the AUDIT doc:
- `Transcript m` is the prefix of *length* `m`. `m.castSucc` and `m.succ` are "before/after move `m`".
- `cast E.eqIn` is an identity coercion between equal types.
- `Bad`'s `∃ w` ranges over the *next-stage* knowledge witness; the extractor maps it *backwards*.
- `Fin.induction … match hDir` builds the honest transcript.
- `Set.univ` / `Unit` is the output relation of a proof system.
- The counting form is `#bad ≤ ε·|C|` in `ℝ≥0`, which is the right choice: no `Pr`, no `ENNReal`.
- `NoOracle` / `emptySpec.{0,0}` is inert noise and disappears with the local `Extractor`.

### m3 (minor): Lean text is behind the decisions in force

- `errorCap = 2^-130` (:236) vs DESIGN `2^-128`.
- `Sizes` lacks `nnz` (DESIGN §2), and `Index` lacks the `support.card ≤ nnz` obligation.
- `Admissible` (`m ≤ 2^24, nx ≤ 2^16, nw ≤ 2^24`) is not tied to the classes.
- The admission caps (`ℓ_j ≤ 2^(k+10)`, `Σℓ_j ≤ 64(N+nnz)`, `idxLen`, leaf sizes dividing lengths, tape ≤ 2^20 B,
  `Q_k ≤ 2^16`, rounds) appear nowhere in Lean.

Any cap the harness or the cost theorem relies on must be a certificate clause rendered into the statement. Otherwise it
is the leanerVM A5 lesson again: "every size cap the verifier checks must be in the relation or an explicit hypothesis"
(R5 §3.3 item 4).

### m4 (minor): composition caveats the L2 tree theorem must state

- Parallel composition with *shared* challenges adds errors. A pair state `S1 ∧ S2` flips if either flips. D1's "N
  enters only through k" is correct only if every node draws its own challenges (FS per node, as deployed). The tree
  theorem must be stated for the sequentialised protocol with independent challenges.
- The tree's `k` is `N·k_embed + (N−1)·k_fold + k_dec`, so C3's cap and m1's `2k ≤ t` side condition apply to the tree.
  That is fine for `t ≫ N`, but it must be written down.

### m5 (minor): harness obligations at the statement boundary

The Lean machine reads values of `F`. The deployed loader reads bytes.
- The harness must reject non-canonical encodings (u32 ≥ p) of `x`, `VK`, tape challenges and oracle leaves, or define
  their reduction.
- The FS prefix (D1 §3.1) should also absorb the *shape and the claim hash*, for domain separation across protocols and
  sizes.
- The SR theorems assume `rnd_i` is a function of `(i, x, Π_≤i)`. The FS transcript must therefore absorb every prover
  message root, including depth-0 ("plain") rounds.

### n1 (note): what I tried that does *not* break the definitions

- **Quantification and form.** The order `∀ s ∀ i ∀ tr` is worst case and adaptive (M1.5), and has no prover
  quantifier. The counting form and the bridge `RbrKS.toArk` are correct.
- **`Fintype`/`Nat.card` tricks.**
  - A submitter-supplied `Fintype` instance cannot distort `Fintype.card`, since `Fintype` is a subsingleton.
  - `Nat.card = 0` on infinite types is closed by `[Fintype]`, and `ε·0` is closed by `[Nonempty]`. Both become
    automatic under C1/C2.
- **Laws, transcripts and universes.**
  - A `Unique` transcript at round 0 makes `default` canonical.
  - `cast E.eqIn` is benign by proof irrelevance.
  - `Decidable` instances cannot lie, since they carry proofs.
  - Universes are fixed at `Type` and caused no issues.
- **Completeness.** It is non-vacuous: the relation is nonempty at every size, and `rejectAll_not_complete` holds.
  "∀ challenge vectors" is equivalent to probability 1 for deterministic provers.
- **Soundness.** It is non-vacuous: `badIndex_unsat` holds, and accept-all has no KSF on one-message schedules.
- **Statement freedom on the base track.** `m = 0` sizes make every statement true, which is legitimate. The base track
  has no submitter relation.
- **Lean-level attacks** (`local notation`, environment hacks, `native_decide`) are comparator's job and unaffected by
  these definitions. The statement-level holes above are exactly what comparator cannot see, because any term of the
  stated `Submission` type wins.

### n2 (note): agreement with A1

C1/C2 here and A1-C1/M1 are the same root cause. A1 measured the cost incentive; §A shows the soundness break, so the
fix is mandatory independently of incentives. M4 here matches A1-M3/n2, and M3.2 is consistent with A1-m4
(`accCap = 2^12`, `x` bound at embed).

---

## What a human auditor must check (after the fixes)

1. `R1CS`, `z = (1, x, w)`, `rel`. The field is BabyBear and its primality is proved.
2. `Round`/`shapeSpec`. Message types must be `Fin len → F` and challenge types `Fin k → Ext`, with `Ext` and its
   serializer the contract's.
3. `Strategy.transcript` (honest run), `PerfectComplete`.
4. `KSF` (3 laws), `Bad`, `RbrKS` (counting form). Read these with the M1 explanation: backward extraction, worst case
   over prefixes.
5. `Protocol` caps (`n ≤ roundCap`, `vkLen ≤ vkCap`, lengths) and `Secure` (`∀ i, ε i ≤ 2^-128`).
6. Machine, `Agrees`, `Terminates`, cost clauses. `Agrees` must quantify over *all* shaped transcripts, i.e. all oracle
   contents, and over all indices and instances.
7. Accumulation shape, the three `Reduction.Secure`, and output agreement.
8. Harness prose: sampler, canonical encodings, FS prefix, bytes→literal binding.
9. Cited meta-theorems with exact numbers: CY 31.2.1, 32.8.9 (soundness), WARP B.4 + CY 32.8.10 (knowledge, unbounded
   `et` at L1), plus m1's side conditions.

## Verdict

The *core* RBR-KS definition is sound and non-vacuous, and it implies what the compilation theorems need.
`chain_extracts` mechanizes the extraction step of WARP Thm B.4. No `full`-iff is needed, and `WitMid` freedom is
harmless.

The *submission interface* around it is not yet a sound contract. Three critical, cheap-to-fix holes let a submission
satisfy the full certificate while the deployed verifier accepts false statements:
- typed messages/serializers (C1, Lean counterexample);
- undefined challenge encoding and sampling (C2);
- no round cap (C3, Lean counterexample).

The accumulation track's cap and machine interface are decorative as written (M3, Lean counterexample). "Knowledge" at
L1 is exactly RBR soundness (M2, Lean theorem), and the headline must say so (M1). With the fixes the trusted base stays
≈390 code lines over Mathlib only, comparable to sig.golf and auditable by a cryptographer.

**Do not launch on the current `Protocol`/`Reduction` structures.**

## Prioritised fix list

1. **C1 + C2.** Replace submitter message and challenge types and serializers with contract round shapes
   (`Round.msg len | Round.chal k`, `Fin len → F`, `Fin k → Ext`). Drop the `ser`/`chalFin` fields. `Agrees` then
   covers all adversarial strings. ≈15 trusted lines; skeleton compiled in §F.
2. **C3.** Add `n_le : n ≤ roundCap` to `Protocol` and `Reduction`, and use the same `roundCap` in the headline.
3. **M3.** Accumulation:
   - give the accumulator a fixed shape (plain ≤ `accCap`, fixed oracle lengths);
   - give `embed` the base track's VK/IDX holographic interface;
   - add output agreement and the selection map;
   - replace the baseline by `fullRecAcc` (or keep `trivialFold` only for a non-holographic illustration).
4. **M1 / m1.** Rewrite DESIGN §4's headline:
   - soundness: CY 31.2.1 + 32.8.9;
   - knowledge: WARP B.4 + CY 32.8.10, extractor time unbounded at L1;
   - fix `2k ≤ t` and the `t ≥ t*` side condition.

   Put `chain_extracts` and the Σε interactive corollary in `Bridge/`. Do **not** add a `full`-iff.
5. **M2.** Relabel L1 "RBR soundness (extractor named, unconstrained)". Make the L2 efficient-extraction track the
   prerequisite for calling T2 records "knowledge"/"recursion-ready".
6. **M4.** Put `VK`, `IDX` and `Strategy` through the computability gate (no `noncomputable`, `implemented_by`, `extern`
   or `csimp`), and evaluate them on the badge path.
7. **m2.** Restate the vocabulary and `Extractor` locally over Mathlib; move all ArkLib imports to `Bridge/`.
8. **m3 / m5.** Sync the Lean text with DESIGN (128, `nnz`, all admission caps as certificate clauses), and specify
   canonical encodings and the FS prefix (with the shape and claim hash) in the AUDIT doc.
9. **Controls.** Add §A–C of `A2Probes.lean` to `Controls/Negative.lean`, restated against the fixed definitions, where
   they must *fail to compile* or be provably refuted. Keep §E as a positive control.
