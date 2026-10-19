<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `notes/R4-arklib.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# R4: ArkLib definitions and status, for recursion.fast

Author: R4 research subagent. Date: 2026-10-10.

**Repositories examined.** All were read-only. I did not modify or push anything.

| Repo | Revision | Notes |
|---|---|---|
| ArkLib | HEAD `db7005f84a9dbad7ff2abbbb4e8feeeac6f4dfd8` (2026-10-08, "feat(proximityGens): Proof of Theorem 6.1 (#1285)") | toolchain `leanprover/lean4:v4.34.0`; pins VCVio `d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0` and CompPoly `v4.34.0-patch2` |
| ArkLib pinned by leanerVM | `7653a901ed466c88a2e61a3075011b73d7bb2316` (2026-09-26) | at `/home/devops/Verified-zkEVM/leanerVM/.lake/packages/Arklib`; leanerVM HEAD `8aaf8a0`, toolchain v4.34.1, VCVio `a4232d0`, mathlib `v4.34.1` |

**Labels.** Every claim below is marked as one of:
- **[V]**: verified by reading the source, grepping, or compiling.
- **[I]**: my inference. Inferences carry a reason.

Paths are relative to the ArkLib root unless they are absolute.

---

## 0. Executive summary

1. **[V] ArkLib has two independent protocol frameworks.**
   - **Legacy `ArkLib/OracleReduction/`.** Its carrier is `ProtocolSpec n`. This is where `Reduction`, `OracleReduction`, `Proof`, completeness, soundness, KS, RBR soundness and RBR KS are defined. All existing protocol developments use it: sumcheck spec, FRI, STIR, Binius, ToyProblem, and leanerVM.
   - **Native `ArkLib/Interaction/`.** Its carrier is PolyFun `TypeTree`. It is new, sorry-free, and much harder to read. At HEAD it has ordinary RBR soundness, witness-indexed RBR knowledge certificates, and a sorry-free **state-restoration knowledge soundness** theorem.
2. **[V] The legacy security definitions are mostly sound, readable and usable.**
   - My probe proves perfect completeness and RBR KS of a toy "send the witness, check R1CS" protocol, sorry-free, in about 120 lines.
   - It also proves a **non-vacuity** check: an always-accepting verifier is *not* RBR knowledge sound.
3. **[V] Almost every general theorem that relates the legacy notions is `sorry`.** This includes:
   - `rbrKnowledgeSoundness_implies_knowledgeSoundness`, `rbrSoundness_implies_soundness` and `knowledgeSoundness_implies_soundness`.
   - Every generic `append` / `seqCompose` / `liftContext` soundness, KS, RBR and RBR-KS theorem.
   - The SR-to-plain implications and FS completeness.

   Proven exceptions:
   - RBR KS ⇒ RBR soundness.
   - Worst-case RBR ⇒ averaged RBR.
   - One-shot RBR KS ⇒ RBR KS.
   - `append` of **worst-case RBR soundness** when the first verifier is pure (soundness only, not knowledge).
4. **[V] There is a signature bug in `Proof.knowledgeSoundness` and `Proof.rbrKnowledgeSoundness`.** They take `relation : Set (Statement × Bool)`, which forces the witness type to `Bool`. They cannot be used for R1CS; the probe reproduces the type error. Use the `Verifier.*` forms with `acceptRejectRel` instead.
5. **[V] There is no BCS transform**; it exists only as commented-out code. Basic Fiat–Shamir is *defined*, but its only theorem, completeness, is `sorry` and is stated with a constant challenge oracle. Duplex-sponge FS is a skeleton with 19 sorries, and its "key lemma" concludes `True`.
6. **[V] Concrete protocols.** No end-to-end, sorry-free SNARK verifier exists in ArkLib.
   - Legacy sumcheck RBR KS is stated but tainted. Spartan is a skeleton. FRI, STIR, Binius and BatchedFRI are unproved.
   - WHIR, Ligero, Brakedown, Nova or folding and accumulation are absent. "Folding" in ArkLib always means codeword folding.
   - Sorry-free: ToyProblem (ABF26 §6), KZG, Ajtai, native sumcheck (soundness only), the RS mutual-correlated-agreement and Johnson-bound developments, and BCIKS20 *unique-decoding* correlated agreement.
7. **[V] Build cost.**
   - In leanerVM's prebuilt environment, importing `ArkLib.OracleReduction.Security.RoundByRound` takes **≈7.5–9 s wall and ≈3.5 GB RSS**. The whole probe file elaborates in **≈10–12 s, 3.5 GB**.
   - A from-scratch build of the needed subset of ArkLib HEAD (`Security.Implications` and `R1CS`), with the Mathlib cache, took **5 min 09 s** wall (§7). `lake exe cache get` before it took 4 min 46 s.
8. **[I] The key definitional pitfall is that extractors are unbounded mathematical functions.** In ArkLib's information-theoretic setting, "knowledge" therefore adds little over soundness (see §3.6). This matters for recursion: the batcher theorem cannot lean on efficient extraction.

---

## 1. Two frameworks; which one recursion.fast should use

| | Legacy `OracleReduction` | Native `Interaction` |
|---|---|---|
| Carrier | `ProtocolSpec n` (vector of directions and types) | PolyFun `TypeTree` with role decorations and dependent residual trees |
| Status (`docs/design/00-current-status.md`, dated 2026-09-26) | "The legacy `OracleReduction` layer remains in use… several unrestricted stateful composition theorems remain admitted." | "No declaration under `ArkLib/Interaction/` … uses `sorry`." |
| Security notions | completeness, soundness, straight-line KS, RBR soundness, RBR KS (averaged and worst-case), SR (stated), CWSS, special soundness | ordinary RBR soundness ⇒ soundness (proved); RBR knowledge certificates; SR knowledge soundness (proved); composition soundness (proved) |
| Clients | sumcheck spec, FRI, STIR, Binius, RingSwitching, ToyProblem, Spartan, Hachi; **leanerVM** | native sumcheck (soundness and completeness only) |
| Readability | moderate (§3.7) | low: dependent type trees, cursors, handlers, runtime artifacts |

- **[V] Delta between pins.** `git diff --stat 7653a90 db7005f -- ArkLib/OracleReduction ArkLib/Interaction` shows **no change to `ArkLib/OracleReduction/**`**. All 3,855 added lines are in `ArkLib/Interaction/Oracle/Security/`:
  - `Knowledge.lean`, `KnowledgeAppend.lean`, `KnowledgeComposition.lean`, `RoundByRound.lean`, `Soundness.lean`, and `StateRestoration*.lean` (6 files).
  - The commits are #1259 to #1264, all on 2026-10-08.
  - Other deltas are STIR Lemma 4.4 (#1265), ProximityGenerator Thm 6.1 / Lemmas 6.2–6.6, and a VCVio pin bump `d7089e4 → d606eab`.
  - So every legacy-layer fact in this note holds identically for leanerVM's ArkLib 7653a90.
- **[V] VCVio pins.** leanerVM's VCVio `a4232d0` and ArkLib HEAD's VCVio `d606eab` are siblings, each one commit off their merge base.
- **[I] Recommendation.** Use the **legacy** layer for the recursion.fast contract:
  - It has the RBR KS definition the brief asks for, a readable shape, and leanerVM precedent.
  - Its sorried *general theorems* are not imported as trusted facts.
  - The native layer is the long-term direction. Its RBR-knowledge ⇒ SR-knowledge theorem is the only sorry-free bridge toward Fiat–Shamir, but it is not yet connected to a concrete FS transform or to the legacy layer.

---

## 2. Core protocol types (legacy layer) [V]

### 2.1 ProtocolSpec, directions, messages and challenges

`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:31`:
```lean
structure ProtocolSpec (n : ℕ) where
  dir : Fin n → Direction
  «Type» : Fin n → Type
```

`ArkLib/OracleReduction/Prelude.lean:66`:
```lean
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
```

- `MessageIdx` and `ChallengeIdx` are subtypes of `Fin n` by direction (`ProtocolSpec/Basic.lean:52,57`).
- `Message`, `Challenge`, `Messages`, `Challenges`, `FullTranscript pSpec := (i : Fin n) → pSpec.«Type» i` (:105), and the partial `Transcript k pSpec` for `k : Fin (n+1)` (:262).
- Notation: `!p[]` is the empty spec; a one-message spec is written `⟨!v[.P_to_V], !v[Msg]⟩`.
- Universe: message types live in `Type` (universe 0).

### 2.2 Prover (`ArkLib/OracleReduction/Basic.lean`)

- `ProverRound` (:155) has two fields:
  - `sendMessage (i : MessageIdx pSpec) : PrvState i.1.castSucc → OracleComp oSpec (pSpec.Message i × PrvState i.1.succ)`
  - `receiveChallenge (i : ChallengeIdx pSpec) : PrvState i.1.castSucc → OracleComp oSpec (pSpec.Challenge i → PrvState i.1.succ)`
- `Prover` (:223):
  ```lean
  structure Prover {ι : Type} (oSpec : OracleSpec ι)
      (StmtIn WitIn StmtOut WitOut : Type)
      {n : ℕ} (pSpec : ProtocolSpec n) extends
        ProverState n,
        ProverInput StmtIn WitIn (PrvState 0),
        ProverRound oSpec pSpec,
        ProverOutput oSpec (StmtOut × WitOut) (PrvState (Fin.last n))
  ```
- The state types `PrvState : Fin (n+1) → Type` are chosen by the prover. Adversaries are arbitrary Lean functions with no resource bounds.
- With `oSpec = []ₒ` the prover is deterministic. **[I]** This is w.l.o.g. for unbounded adversaries by averaging.
- A comment at :233–245 records that the rigid prover type makes "knowledge soundness implies soundness" "difficult (impossible?)". The lighter `ProverInteraction` and `ProverInteractionWithOutput` types exist but are not used by the security definitions.

### 2.3 Verifier, OracleVerifier and oracle access

- `Verifier` (:248):
  ```lean
  structure Verifier {ι : Type} (oSpec : OracleSpec ι)
      (StmtIn StmtOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
    verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut
  ```
  - The verifier sees the whole transcript, challenges included. **It does not sample its challenges**: the execution draws them (§2.5), so all protocols are public-coin.
  - `OptionT` failure means abort, which is treated as reject.
- `OracleVerifier` (:323):
  ```lean
    verify : StmtIn → pSpec.Challenges →
      OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut
    outputOracle :
      OracleOutputEmbedding OStmtIn pSpec.Message OStmtOut ⊕
        OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec
  ```
  - The verifier gets the challenges in full. It reaches the input oracle statements and prover messages only through queries.
- `OracleInterface` (`OracleReduction/OracleInterface.lean:55`):
  ```lean
  class OracleInterface (Message : Type u) where
    Query : Type v
    toOC : OracleContext Query (ReaderM Message)
  ```
  - `answer m q` evaluates the query against the message. `[v]ₒ` (:105) turns a family of interfaces into an `OracleSpec`.
  - Instances: polynomials answer evaluation queries (`instPolynomial`, :263, `Query := R`); `Vector α n` answers index queries (`instVector`, :317); a function type answers by application; and `instDefault` uses a `Unit` query that returns the whole message.
- **Query semantics** (`OracleVerifier.toVerifier`, `Basic.lean:490`): queries are answered deterministically from the actual messages via `simOracle2`. **All security notions for oracle reductions are defined through `toVerifier`**, a non-oracle verifier over `(StmtIn × ∀ i, OStmtIn i)` and full messages.
  - **[V]** The only security-relevant role of the oracle interface is restricting what the verifier can compute; nothing counts queries.
  - `OracleVerifier.numQueries` (`Basic.lean:505`) is literally `:= sorry`.
  - The `NonAdaptive` oracle verifier (:526) has `totalNumQueries`.

### 2.4 Reduction, OracleReduction, Proof

`Basic.lean:625` and `:633`:
```lean
structure Reduction ... where
  prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec
  verifier : Verifier oSpec StmtIn StmtOut pSpec
structure OracleReduction ... where
  prover : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec
  verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec
```

`Basic.lean:659`:
```lean
@[reducible] def Proof {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  Reduction oSpec Statement Witness Bool Unit pSpec
```

- `OracleProof` (:669) is an `OracleReduction` to `Bool` with an `Empty`-indexed output-oracle family and `Unit` witness.
- `NonInteractiveProver`, `NonInteractiveVerifier` and `NonInteractiveReduction` (one `P_to_V` message) are defined at about :730–742.
- Relations are `Set (StmtIn × WitIn)` with `Set.language rel := Prod.fst '' rel` (`Prelude.lean:108`).
- The output relation of proofs is `acceptRejectRel : Set (Bool × Unit) := { (true, ()) }` (`Prelude.lean:123`).

### 2.5 Execution and challenge sampling

- `Prover.processRound` (`Execution.lean:98`): at a `V_to_P` round it runs `let challenge ← pSpec.getChallenge ⟨j, hDir⟩`, which is a query to the challenge oracle `[pSpec.Challenge]ₒ`.
- `Reduction.run` (`Execution.lean:211`):
  ```lean
  def Reduction.run (stmt : StmtIn) (wit : WitIn) (reduction : Reduction ...) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) := do
    let proverResult ← reduction.prover.run stmt wit
    let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run
    return ⟨proverResult, ← stmtOut.getM⟩
  ```
- `Reduction.runWithLog` (:387) also returns the prover's and verifier's query logs, which the KS game uses.
- Challenges become random only in the security games: they interpret `[pSpec.Challenge]ₒ` with `challengeQueryImpl` (`ProtocolSpec/Basic.lean:732`): `fun q => $ᵗ (pSpec.Challenge q.1)`.
- `$ᵗ` is VCVio's `SampleableType.selectElem`. The class carries the law `𝒟[selectElem] = uniformOn Set.univ`, so challenges are provably uniform over the whole challenge type.
- **Every security definition is parameterized by `{σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))`**, the implementation of the shared oracle `oSpec` (for example, a random oracle).

### 2.6 Monads (VCVio)

- `OracleComp spec := PFunctor.FreeM spec.toPFunctor` (`VCVio/OracleComp/OracleComp.lean:27`): a free monad of oracle queries, with no built-in failure.
- `ProbComp := OracleComp unifSpec` (`VCVio/OracleComp/ProbComp/Basic.lean:31`).
- Failure is added with `OptionT`.
- `Pr{ doSeq }[ event ]` (`VCVio/EvalDist/ProbabilityNotation.lean:27`) is ENNReal-valued. It measures only `some` outputs: failure mass never satisfies the event.
- **[V]** This matters for direction:
  - In completeness (`≥ 1 − ε`), failure counts *against* the honest parties, which is correct.
  - In soundness and KS (`≤ ε`), verifier abort counts as reject, which is correct.
  - KS deliberately runs the extractor's `OptionT` *inside* the event, so extractor failure counts as an adversary win. The docstring at `Security/Basic.lean:310–330` explains the vacuity this avoids.

---

## 3. Security definitions, exactly as defined [V]

All are in `ArkLib/OracleReduction/Security/Basic.lean` (B) and `.../Security/RoundByRound.lean` (R).

**Error types.**
- Completeness, soundness and KS errors are `ℝ≥0`.
- RBR errors are per-challenge functions `pSpec.ChallengeIdx → ℝ≥0`.
- The probabilities themselves are `ℝ≥0∞`.
- The native layer uses `ℝ≥0∞` errors.

### 3.1 Completeness (B:87)

```lean
def completeness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ relIn →
    let pImpl := QueryImpl.addLift impl challengeQueryImpl
    Pr{let ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ ← OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)}[
        (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut] ≥ 1 - completenessError
```

- `perfectCompleteness` is `completeness … 0` (B:101).
- `perfectCompleteness_eq_prob_one` (B:163) restates it as probability exactly 1.
- **The proof route** is `perfectCompleteness_of_run_support` (B:191): every element of the support of the unsimulated run is `some result` with the relation holding. It needs nothing about the challenge distribution.
- `Proof.perfectCompleteness relation proof` (B:541) specializes `relOut := acceptRejectRel`.

### 3.2 Soundness (B:270)

```lean
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ stmtIn ∉ langIn,
    ... Pr{let ⟨_, stmtOut⟩ ← OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)}[
        stmtOut ∈ langOut] ≤ soundnessError
```

- The statement is non-adaptive: it is fixed before the run.
- The adversary is an arbitrary `Prover`, with no time or query bound.

### 3.3 Knowledge soundness: straight-line extractor (B:246, B:343)

```lean
def Straightline :=
  StmtIn → WitOut → FullTranscript pSpec → QueryLog oSpec → QueryLog oSpec →
  OptionT (OracleComp oSpec) WitIn
```

```lean
def knowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    ... Pr{...}[
        (∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∉ relIn) ∧
          (stmtOut, witOut) ∈ relOut] ≤ knowledgeError
```

- The extractor is **straight-line and non-rewinding**. It sees the statement, the prover's output witness, the transcript, and both query logs, but not the prover's code.
- The order is ∃E ∀P, so it is a universal extractor.
- `knowledgeSoundnessWith` (B:298) names the extractor in the type.
- A rewinding extractor is only sketched in comments (`Security/Rewinding.lean`).
- `Proof.knowledgeSoundness (relation : Set (Statement × Bool))` (B:552) has the **Bool-witness bug**; see §3.8.

### 3.4 Round-by-round soundness (R:135, R:357)

The state function, `StateFunction`:
```lean
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt default
  toFun_next : ∀ m, pSpec.dir m = .P_to_V → ∀ stmt tr, ¬ toFun m.castSucc stmt tr →
    ∀ msg, ¬ toFun m.succ stmt (tr.concat msg)
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    Pr{let stmtOut ← OptionT.mk do
      (simulateQ impl (verifier.run stmt tr)).run' (← init)}[stmtOut ∈ langOut] = 0
```

The definition, `rbrSoundness`:
```lean
  ∃ stateFunction, ∀ stmtIn ∉ langIn, ∀ WitIn WitOut, ∀ witIn, ∀ prover, ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge⟩ ← do (simulateQ (impl.addLift challengeQueryImpl) (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' (← init)}[
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤ rbrSoundnessError i
```

- **Averaged vs worst-case.** The default `rbrSoundness` and `rbrKnowledgeSoundness` *sample the prefix with the prover* and bound the mixture, which is weaker than the literature definition. The faithful **worst-case-per-prefix** forms exist:
  - `rbrSoundnessWorstCase` (R:523): `∀ transcript : Transcript i.1.castSucc pSpec, Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[…] ≤ ε i`.
  - `rbrKnowledgeSoundnessWorstCase` (R:539).
  - The proved implications are `rbrSoundnessWorstCase_implies_rbrSoundness` (R:592) and the knowledge analogue (R:609).
  - They have no prover quantifier, so they are the easier and more standard obligation.

### 3.5 Round-by-round knowledge soundness (R:77, R:165, R:424)

The extractor (R:77). It is a *pure function* chain with no logs and no randomness:
```lean
structure RoundByRound (oSpec) (StmtIn WitIn WitOut : Type) (pSpec : ProtocolSpec n)
    (WitMid : Fin (n + 1) → Type) where
  eqIn : WitMid 0 = WitIn
  extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec → WitMid m.succ → WitMid m.castSucc
  extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)
```

The knowledge state function (R:165):
```lean
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop
  toFun_empty : ∀ stmtIn witMid,
    ⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn ↔ toFun 0 stmtIn default witMid
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmtIn tr msg witMid, toFun m.succ stmtIn (tr.concat msg) witMid →
      toFun m.castSucc stmtIn tr (extractor.extractMid m stmtIn (tr.concat msg) witMid)
  toFun_full : ∀ stmtIn tr witOut,
    Pr{let stmtOut ← OptionT.mk do
      (simulateQ impl (verifier.run stmtIn tr)).run' (← init)}[
        (stmtOut, witOut) ∈ relOut] > 0 →
    toFun (.last n) stmtIn tr (extractor.extractOut stmtIn tr witOut)
```

The definition (R:424):
```lean
def rbrKnowledgeSoundness (relIn) (relOut) (verifier) (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :=
  ∃ WitMid, ∃ extractor : Extractor.RoundByRound ..., ∃ kSF : verifier.KnowledgeStateFunction ...,
  ∀ stmtIn witIn prover, ∀ i : pSpec.ChallengeIdx,
    Pr{… prover.runWithLogToRound i.1.castSucc … ; challenge ← getChallenge i …}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤ rbrKnowledgeError i
```

Related forms:
- `rbrKnowledgeSoundnessWith` (R:450), with the exact objects named.
- `rbrKnowledgeSoundnessOneShot` (R:402), the older definition with one-shot extractor `(m : Fin (n+1)) → StmtIn → Transcript m pSpec → QueryLog oSpec → WitIn`.

**Documented deviations from ABF26 Def. A.5**, from the docstring at R:155–164:
1. `extractMid` may transform the witness across a prover move.
2. `toFun_full` is one-directional ("positive-probability related verifier output implies the extracted final state"), whereas A.5 prints an iff.

**[V] What the definition really requires.** This is the useful reading for cryptographers.
- **No challenge rounds** (our toy protocol). The probabilistic clause quantifies over an empty type. RBR KS is *exactly* the existence of extractor maps with the three structural laws. For a single prover message, the laws force: if the verifier can accept `tr`, then `extractMid(extractOut(tr))` is a valid witness. That is perfect, deterministic extraction from the transcript.
- **With challenges.** Backward extraction can fail only at challenge rounds, and at each such round the "bad flip" probability over the fresh challenge is at most `ε i`.

### 3.6 Pitfalls and assessment of the definitions

- **P1 [V]: extractors are mathematical functions, not algorithms.**
  - `Extractor.RoundByRound` fields are plain Lean functions, and `Straightline` returns an `OracleComp` term. Neither carries a running-time or query bound.
  - ArkLib uses non-constructive extractors itself: `toRoundByRoundOfRel` (R:118) picks a valid witness by `Classical.choose` ("selecting a valid witness non-constructively preserves the property formalized here. It does not establish the extraction-time bounds…").
  - **[I] Consequence.** Take the extractor that returns `Classical.choose` of a valid witness whenever `stmtIn ∈ relIn.language`. Then straight-line KS reduces to soundness w.r.t. `relIn.language`, and RBR KS reduces to RBR soundness, with the same errors.
  - The proof sketch for RBR: put `kSF 0 s _ w := (s,w) ∈ rel`, `kSF m>0 := S m`, and let `extractMid` choose. The bad events then coincide.
  - So "knowledge" has no *computational* content in ArkLib's information-theoretic setting. It is still a strictly stronger *shape* (an explicit witness map), and the `…With` variants plus executable extractors (as in ToyProblem `Impl.IRS`) let a contract demand a named, computable extractor.
  - For recursion.fast this is acceptable for a single proof. For the **batcher** it means a theorem only guarantees witnesses that exist, not witnesses that are efficiently extractable. This is consistent with PLAN §1.7.
- **P2 [V]: the oracle model is a parameter.**
  - `init` and `impl` are arguments of every definition.
  - A trusted contract must either fix them (for example `oSpec = []ₒ` and quantify `∀ init impl`, as leanerVM does) or fix a specific random-oracle implementation.
  - Otherwise a submission could pick a degenerate `impl`, for example a non-random "random oracle" that makes FS trivially sound.
- **P3 [V]: `toFun_full` evaluates the verifier with a fresh `init` sample**, not the run's oracle state.
  - It is harmless for `oSpec = []ₒ`.
  - **[I]** For ROM verifiers it makes the knowledge-state function condition about "some oracle makes V accept", which may be unsatisfiable or awkward. This is another reason to keep the contract in the IOP/IR model with `[]ₒ`.
- **P4 [V]: the adversary is unbounded with non-adaptive statement choice.** `∀ stmtIn` precedes the prover. This is fine for information-theoretic IOPs. It is not a computational notion, and adaptivity is not modeled (the comment at B:220 notes it).
- **P5 [V]: the averaged RBR is weaker than the literature definition.** The contract should state the worst-case forms (§3.4).
- **P6 [V]: there are no query or cost semantics.** `numQueries` is `sorry`. Oracle security is defined through `toVerifier`, which sees full messages. Query-complexity accounting for the cost function must be done outside ArkLib's legacy definitions, for example with the RISC-V emulator or native `Data/OracleComp/QueryBounds`.
- **P7 [V]: the error budget is user-supplied.**
  - `rbrKnowledgeError` is chosen by the prover of the theorem, so the contract must separately constrain `∑ i, ε i ≤ 2^{-λ}` or `max`.
  - The theorem that turns RBR errors into a KS error (`rbrKnowledgeSoundness_implies_knowledgeSoundness`, error `∑ i, ε i`) is `sorry`.
  - The contract either proves it (for `[]ₒ`; **[I]** feasible), states RBR KS plus the error bound as the target directly, or proves KS directly as ToyProblem does.
- **P8 [V]: challenge types are submitter-chosen.** The uniformity law in `SampleableType` prevents biased samplers. A submission may still choose tiny challenge types, which then shows up honestly in `ε i`.
- **P9 [V]: universes.** Statements, witnesses, message and prover-state types are all in `Type`. This is no restriction for our use.

### 3.7 Readability for a non-Lean cryptographer [I]

- **Completeness and soundness.** These are readable once three conventions are explained:
  - `Pr{ do-block }[event]` with OptionT failure excluded;
  - `simulateQ (impl.addLift challengeQueryImpl)`, meaning "answer shared-oracle queries with `impl` and challenges uniformly";
  - `run' (← init)`.
- **RBR KS.** This needs a page of explanation. The `cast extractor.eqIn`, the `WitMid` family, `Transcript m.succ` vs `castSucc` indexing, and the `∃ witMid` inside the bad event are not standard notation.
- **Advice.** Re-state the *target* locally in a contract file that:
  - fixes `oSpec := []ₒ`;
  - uses the worst-case form, which has no prover quantifier and no `simulateQ`;
  - is phrased directly over `pSpec.Challenge i` and the transcript;
  - is accompanied by a proven lemma `local ↔ ArkLib.rbrKnowledgeSoundnessWorstCase`, or `→` the ArkLib form.

  This keeps the audited statement short and retains ArkLib compatibility.
- **The native layer is not suitable as audited text today.**

### 3.8 Known bugs, sorry and oddities in the definitions themselves [V]

| Item | Location | Effect |
|---|---|---|
| `Proof.knowledgeSoundness (relation : Set (Statement × Bool))` | B:552 | Witness type forced to `Bool`; unusable for R1CS. Workaround: `Verifier.knowledgeSoundness … rel acceptRejectRel`. |
| `Proof.rbrKnowledgeSoundness (relation : Set (Statement × Bool))` | R:780 | Same bug. Probe `ProofBoolBug.lean` reproduces: "Application type mismatch … `rel` has type `Set (S × W)` but is expected to have type `Set (S × Bool)`". (`OracleProof.*` variants use `Witness` correctly.) |
| `OracleVerifier.numQueries … := sorry` | Basic.lean:505 | A data-level `sorry`; any use taints. |
| `fiatShamir_completeness` states the FS challenge oracle as the constant `default` function | FiatShamir/Basic.lean:163 | Not the ROM statement **[I]**; also `sorry`. |
| `Extractor.Straightline.IsMonotone` | B:391 | Marked "Placeholder probability". Not used by the main definitions. |
| R1CS field comments | ConstraintSystem/R1CS.lean:32–33 | `m -- number of columns`, `n -- number of rows` are swapped relative to `Matrix (Fin m) (Fin n)`: m is constraints/rows, n is variables/columns. |

The core definitions (`completeness`, `soundness`, `knowledgeSoundness`, `rbr*`, `StateFunction`, `KnowledgeStateFunction`) contain **no `sorry`**. Per the subagent census, `Security/{Basic,RoundByRound,RbrGame}.lean` have 0 sorries and none of their definitions are in `scripts/axiom_baseline.json`.

---

## 4. Theorems relating the notions, and composition [V]

`scripts/axiom_baseline.json` is the committed output of `lake exe axiomsweep`. It lists the 281 `sorryAx`-tainted declarations at HEAD and has an empty `nonstandard` list. A name **not** in it is transitively sorry-free; this is **[I]** in that it assumes CI's `--check` was green at HEAD.

| Theorem | File:line | Status |
|---|---|---|
| `Verifier.rbrKnowledgeSoundness_implies_rbrSoundness` | Security/Implications.lean:87 | **proved** |
| `rbrSoundnessWorstCase_implies_rbrSoundness`, `rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`, `…With_implies_…With` | RoundByRound.lean:592, 609, 628 | **proved** (via `RbrGame.prEvent_simulateQ_addLift_getChallenge_bind_le`, RbrGame.lean:104) |
| `rbrKnowledgeSoundnessOneShot_implies_rbrKnowledgeSoundness` | RoundByRound.lean:660 | **proved** |
| `knowledgeSoundness_implies_soundness` | Implications.lean:49 | `sorry` |
| `rbrSoundness_implies_soundness` (error `∑ i, ε i`) | Implications.lean:79 | `sorry` |
| `rbrKnowledgeSoundness_implies_knowledgeSoundness` (error `∑ i, ε i`) | Implications.lean:193 | `sorry` |
| `srSoundness_implies_soundness`, `srKnowledgeSoundness_implies_knowledgeSoundness`, salt variants | Implications.lean:229–283 | `sorry` (some statements even contain `sorry` *in the statement*: `Verifier.StateRestoration.soundness sorry sorry …`) |
| `Verifier.append_{soundness, knowledgeSoundness, rbrSoundness, rbrKnowledgeSoundness}` | Composition/Sequential/Append/Security.lean:47, 58, 79, 94 | `sorry`; the docstring at :68–74 explains why the generic statements are likely missing hypotheses ("requires a pure, total first verifier… bounds after conditioning on the first transcript") |
| `Verifier.append_rbrSoundnessWorstCase_of_pure_first`, `append_rbrSoundness_of_worst_case_of_pure_first` (+ OracleVerifier) | Append/RoundByRound.lean:37, 97, 128 | **proved** (soundness only) |
| `Verifier.seqCompose_{soundness, knowledgeSoundness, rbrSoundness, rbrKnowledgeSoundness}` and OracleVerifier versions | Composition/Sequential/General.lean:362–533 | tainted (`sorry` at :438, :471; others via `append_*`) |
| `seqCompose_completeness_of_pure`, `append_perfectCompleteness_of_pure*` | Sequential/Completeness.lean:30,66; Append/Completeness.lean | **proved** (pure-verifier variants) |
| `liftContext_{completeness, soundness, knowledgeSoundness, rbr_soundness, rbr_knowledgeSoundness}` | LiftContext/Reduction.lean:355–554; OracleReduction.lean:250–325 | `sorry` (10 sorries in Reduction.lean) |

**Native layer** (`ArkLib/Interaction/**`, 39 files, 12,888 lines, **0 sorry**). Notable theorems:
- `executeStrategies_soundness_uniform` (`Interaction/Oracle/Security/Soundness.lean:186`): native RBR soundness ⇒ soundness with `count * error`, for arbitrary effectful prover strategies.
- `stateRestoration_knowledge_soundness` (`Interaction/Oracle/Security/StateRestorationGame.lean:102`): "Round-by-round knowledge bounds imply state-restoration knowledge soundness for the actual native verifier". Its conclusion is `Pr{…(simulateQ randomOracle (verificationGame …)).run' ∅}[…] ≤ (Q + rounds.length) * error`.
  - It is restricted to a fixed `List Round` presentation (prover oracle message, then uniform challenge, per round) with `Finite Message` and `Finite Challenge`.
  - The adversary is a total oracle program with total query bound `Q`.
- Knowledge composition: `KnowledgeAppend.lean` and `KnowledgeComposition.lean` (#1259, #1260).
- Composition soundness: `Interaction/CompositionSoundness.lean` and `Oracle/CompositionSoundness.lean`.
- None of these is connected to the legacy definitions. Only honest-execution correspondences exist, for sumcheck (`Sumcheck/Interaction/Legacy.lean:108`).

---

## 5. Fiat–Shamir and BCS [V]

- **BCS** (`OracleReduction/BCS/Basic.lean`, 84 lines). There is only a docstring and `ProtocolSpec.renameMessage` (:54). `BCSTransform` is commented out, and there are no theorems.
  - ArkLib has **no Merkle-tree formalization**.
  - Merkle trees live upstream in VCVio (`VCVio/CryptoFoundations/MerkleTree/**`, 52 files, about 14k lines, 0 sorries at VCVio a4232d0). That includes `extractability_rom_bound` (`Extractability.lean:591`) and binding.
  - ROADMAP: "upstream Merkle results alone do not complete ArkLib's commitment compiler."
- **Basic FS** (`OracleReduction/FiatShamir/Basic.lean`).
  - Defined: `Prover.fiatShamir` (:114), `Verifier.fiatShamir` (:130) and `Reduction.fiatShamir` (:140). Challenges come from `fsChallengeOracle StmtIn pSpec`, queried on the input statement and the messages so far.
  - The only theorem is `fiatShamir_completeness` (:163), which is `sorry`.
  - The file ends with "TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir".
  - **No FS soundness theorem exists in the legacy layer.**
- **Duplex-sponge FS** (`FiatShamir/DuplexSponge/**`). Defined in `Defs.lean` (0 sorries). The security files hold 19 sorries and 56 baseline entries. `KeyLemma.duplexSpongeToFSGameStatDist … : True := sorry` is a placeholder.
- **The path that exists [V].** The native `stateRestoration_knowledge_soundness` proves the Chiesa–Yogev/BCS-style step "RBR knowledge ⇒ SR knowledge soundness in the ROM" for the native fixed-round presentation. SR ⇒ FS is the remaining standard step. It is **not formalized**: no native FS transform, and no hash or sponge.
- **[I] For recursion.fast.** The contract cannot import a proven "RBR KS ⇒ FS-NARG KS in the ROM" theorem from ArkLib today. The honest framing is: the contract proves IOP-level RBR KS, and the BCS+FS step is cited from the literature (CY24, BCS16, CCHLRR18) and documented as a gap. Optionally, a future track can target the native SR theorem.

---

## 6. Concrete protocols and supporting math

This section consolidates a census subagent's report with my own spot-checks. The method:
- Source sorries were counted with a lexer that strips comments and docstrings: 169 real uses in `ArkLib/` vs 223 raw grep lines.
- Transitive taint comes from `scripts/axiom_baseline.json`.
- I re-verified a sample: the sumcheck `General.lean:223` statement, ToyProblem `General.lean:1371/1408`, the R1CS file, Implications, Append/Security, General, LiftContext and the FS/BCS files.

| Area | Files | Source `sorry` | Baseline entries | Key theorems (file:line) | Status |
|---|---|---|---|---|---|
| Sumcheck (legacy) | `ProofSystem/Sumcheck/Spec/*` | 13 (all `SingleRound.lean`) | 16 | `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` (General.lean:223, error `deg/|R|` per round); `Spec.reduction_perfectCompleteness` (:211) | **Stated, tainted** via `seqCompose_rbrKnowledgeSoundness` and `liftContext_rbr_knowledgeSoundness`; `SingleRound.verifier_rbrKnowledgeSoundness` (:932) is a direct `sorry`; only `Simple.*perfectCompleteness` proved |
| Sumcheck (native) | `Sumcheck/Interaction/*` (19 files) | 0 | 0 | `roundByRound_soundness` (RoundByRound.lean:662), `execute_soundness` (ProtocolSoundness.lean:201), `execute_perfectCompleteness` (ProtocolCompleteness.lean:110) | **Sorry-free; soundness and completeness only, no KS** (`count*deg/|F|`) |
| Spartan | `Spartan/Basic.lean` | 4 | 4 | none (empty `section Security`) | Skeleton |
| R1CS | `ConstraintSystem/R1CS.lean` | 0 | 0 | `R1CS.relation` (:64), `pad_preserves_relation` (:89) | Defined (§6.1) |
| FRI | `Fri/*`, security in `BatchedFri/Security.lean` | 4 (+3) | 11 | `Fri.fri_soundness` (:767), `fri_query_soundness` (:649) | Unproved; even the relation defs are `sorry` |
| BatchedFRI | `BatchedFri/*` | 6 | 3 | as above | Unproved |
| STIR | `Stir/*` | 3 | 4 | `stir_main` (MainThm:122), `stir_rbr_soundness` (:173) | Unproved; `quotienting` (Lemma 4.4) and out-of-domain lemmas proved |
| WHIR | none | n/a | n/a | n/a | **Absent** (citations only) |
| Binius (BinaryBasefold, FRIBinius) | `Binius/*` | 32 | 54 | `fullOracleVerifier_rbrKnowledgeSoundness` (BinaryBasefold/General:150) | Unproved |
| RingSwitching | `RingSwitching/*` | 14 (Packing) | 14 | Lift: `coordinateWiseSpecialSoundWithEscape` (Lift/Reduction:237) proved | Packing unproved |
| Ligero, Brakedown, generic Basefold | none | n/a | n/a | n/a | **Absent** (AHIV22 proximity lemma only) |
| Plonk | `Plonk/Basic.lean`, `ConstraintSystem/Plonk.lean` | 1 | 1 | none | Stub |
| ToyProblem (ABF26 §6) | `ToyProblem/*` (12 files, 6.8k lines) | 0 | 0 | `oracleVerifier_rbrKnowledgeSoundnessWorstCase` (Spec/General:1371), `oracleVerifier_rbrKnowledgeSoundness` (:1408), `oracleVerifier_knowledgeSoundness_winningSetUpperBound` (Spec/KnowledgeSoundness:455), `oracleReduction_perfectCompleteness` (Spec/Completeness:117) | **Fully proved**; the only multi-round legacy IOR with sorry-free RBR KS *and* KS (KS proved directly, not via the sorried implication) |
| Components | `ProofSystem/Component/*` | 2 | 2 | `SendWitness.reduction_completeness` (proved), `RandomQuery.oracleVerifier_rbrKnowledgeSoundness` (:261) | Mostly proved; `NoInteraction.reduction_completeness` and `SendSingleWitness.oracleReduction_completeness` (:403) are `sorry` |
| Merkle | VCVio upstream | 0 (VCVio a4232d0) | n/a | `extractability_rom_bound` | Proved upstream; not wired into ArkLib |
| KZG / Ajtai | `Commitments/Functional/KZG`, `Commitments/Ordinary/Ajtai` | 0 | 0 | `binding` (KZG/Binding:751, t-SDH), `bindingAdvantage_le_moduleSIS` | Proved under stated assumptions |
| Hachi | `Commitments/Functional/Hachi` | 13 | 25 | `hachiNonrecursive_perfectCorrectness` | Non-recursive part proved; recursion `sorry` |
| Accumulation, folding, IVC, PCD, Nova, WARP | none | n/a | n/a | n/a | **Absent**; only codeword folding (FRI, Basefold, `ProximityGap/Folding*`) and a WARP citation (BCFW25) |
| BCIKS20 proximity gaps | `Data/CodingTheory/ProximityGap/BCIKS20` (16 files) | 17 | most of 48 `CodingTheory` entries | `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` (AffineLines/UniqueDecoding:33) **proved**; `RS_correlatedAgreement_affineLines` (Johnson, Main:38) **sorry** ("TODO: theorem 5.1 for list-decoding regime"); `correlatedAgreement_affine_spaces` (:1148), `proximity_gap_RSCodes`, `correlatedAgreement_affine_curves` tainted or sorry | Unique decoding only |
| RS mutual correlated agreement (separate development) | `Data/CodingTheory/ReedSolomon/**`, `HiddenDerivative/**` | 0 | 0 | `mcaError_affineLine_johnson_le` (MCA/Johnson/Probability:41), `exists_capacity_mcaError` (Capacity:254, DKTZ26, large constants), `capacity_powerBatchingAgreement` | **Sorry-free**, including a Johnson-range MCA bound for lines |
| CapacityBounds, list-decoding bounds | `ProximityGap/CapacityBounds.lean`, `ListDecodability/Bounds/*` | 3 + 4 | in the `CodingTheory` entries | `rs_mcaError_le_in_johnson_range` (BCHKS25), `rs_random_domain_lambda_le` (AGL24) | External results admitted as `sorry` |
| Johnson bound, Guruswami–Sudan, Berlekamp–Welch, DG25 | respective directories | 0 | 0 | `johnson_bound` (JohnsonBound/Basic:198), GS decoder correctness, `decoder_eq_some`, DG25 interleaved/tensor gaps | Proved |
| ProximityGenerator | `ProximityGenerator/*` | 2 | about 5 | `isMCAGenerator_of_isMDSGenerator` (Thm 6.1, the HEAD commit) proved | Mostly proved |
| Legacy general theory | `OracleReduction/**` | 48 (Implications 11, LiftContext/Reduction 10, Append/Security 4, General 2, Basic 1, FS 20) | about 39 | §4 | Definitions sorry-free; most general theorems `sorry` |
| Native theory | `Interaction/**` | 0 | 0 | §4 | Sorry-free |

Pin comparison: at 7653a90 there were 171 source sorries and 286 baseline entries. The only deltas are STIR (4→3) and CodingTheory (27→26).

### 6.1 R1CS definition (verbatim, `ProofSystem/ConstraintSystem/R1CS.lean`) [V]

```lean
structure Size where
  m : ℕ -- number of columns
  n : ℕ -- number of rows
  n_w : ℕ -- number of witness variables
  n_w_le_n : n_w ≤ n := by omega
abbrev Size.n_x : ℕ := sz.n - sz.n_w
def Statement := Fin sz.n_x → R
def OracleStatement := fun _ : MatrixIdx => Matrix (Fin sz.m) (Fin sz.n) R
def Witness := Fin sz.n_w → R
def 𝕫 {R} {sz} (stmt : Statement R sz) (wit : Witness R sz) : Fin sz.n → R :=
  Fin.append stmt wit ∘ Fin.cast (by simp)
def relation :
    (Fin sz.n_x → R) → (MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R) → (Fin sz.n_w → R) → Prop :=
  fun stmt matrix wit =>
    letI 𝕫 := 𝕫 stmt wit
    (matrix .A *ᵥ 𝕫) * (matrix .B *ᵥ 𝕫) = (matrix .C *ᵥ 𝕫)
```

Pitfalls:
- `relation` is a curried `Prop` function, not a `Set`.
- The matrices are *oracle statements*, so this is the holographic form Spartan uses.
- `z = (x, w)` has **no constant-1 entry**, so affine constraints need a public input pinned to 1 by the verifier.
- The field comments for `m` and `n` are swapped.
- The ring is `[CommSemiring R]`.
- The only client is Spartan.
- **[I]** For recursion.fast, re-state R1CS locally with `z = (1, x, w)` and explicit dimensions, as the probe does. Optionally prove equivalence with `R1CS.relation` when `x₀ = 1`.

---

## 7. Build cost [V]

Machine: 32 cores, 62 GB RAM.

| Measurement | Result |
|---|---|
| `lake env lean` of a file importing only `ArkLib.OracleReduction.Security.RoundByRound` + one `#check` (leanerVM env, prebuilt `.lake`) | **7.6–9.3 s wall, 3.4–3.5 GB max RSS** (3 runs) |
| `ToyR1CS_leanerVM.lean` (imports RoundByRound; 3 theorems incl. RBR KS + non-vacuity; `#print axioms`) | **10.1–12.2 s wall, 3.5 GB max RSS** |
| leanerVM's ArkLib build is **partial** | only `Data/`, `OracleReduction/{Basic,Execution,OracleInterface,Prelude,ProtocolSpec,Composition/Sequential/*,Security/{Basic,RoundByRound,RbrGame,TranscriptTree,CoordinateWiseSpecialSoundness}}` and `ToMathlib/` oleans exist. `Security/Implications`, `ProofSystem/**` and `ConstraintSystem/R1CS` are **not** built, so importing `ArkLib.OracleReduction.Security.Implications` fails with "object file … does not exist". |
| Fresh clone of ArkLib db7005f → `lake exe cache get` (Mathlib cache present in `~/.cache/mathlib`; deps cloned from network) | **4 min 46 s wall** ("Already decompressed 8908 file(s)"); `.lake` = 8.2 GB |
| `lake build ArkLib.OracleReduction.Security.Implications ArkLib.ProofSystem.ConstraintSystem.R1CS` on that clone (VCVio, PolyFun, CompPoly, ArkLib subset from source; Mathlib from cache) | **5 min 09 s wall, 1190 s user CPU** (about 4 cores busy on average), max RSS of `lake` 1.6 GB. 3256 jobs; only **151 modules compiled**: ArkLib 48, VCVio 79, PolyFun 24 (CompPoly and Mathlib needed nothing beyond the cache). Slowest single module about 20 s. |

Elaborating the full `ToyR1CS.lean` in the clone takes 9.7 s warm, but 46.6 s on the first run with a cold page cache. `ImportRBR.lean` takes 9.0 s, 3.3 GB.

The build clone is at `/home/devops/CambridgePQ/recursion.fast/probes/arklib-probe/build/ArkLib-db7005f`. It is disposable (9.7 GB) and can be reused by probe P1. Logs are `build/cache-get.log` and `build/build-subset.log`.

- **[V] Toolchain mismatch.** ArkLib HEAD is on v4.34.0; leanerVM is on v4.34.1 with mathlib `v4.34.1`, and rebuilds ArkLib against that.
- **[I] Implication for the contract.** Prefer importing *only* `ArkLib.OracleReduction.Security.RoundByRound` (and `Basic`). This is about 8–9 s per file in a warm environment, and these modules are free of `sorry` in their definitions.

---

## 8. Probe: toy "prover sends witness, verifier checks R1CS" [V]

Files are in `/home/devops/CambridgePQ/recursion.fast/probes/arklib-probe/`:
- `ImportRBR.lean`: the import-time test.
- `ToyR1CS.lean`: the full probe, which also uses `Implications` and is compiled in the ArkLib-HEAD clone.
- `ToyR1CS_leanerVM.lean`: the same probe minus the `Implications` part, generated by `sed` and compiled in leanerVM.
- `ProofBoolBug.lean`: the Bool-witness signature bug.

Contents of `ToyR1CS.lean`:
- A local R1CS `Stmt` (A, B, C over `Fin (nx+nw+1)` columns, public `x`). Here `z = Fin.cons 1 (Fin.append x w)`, `Holds s w := (A *ᵥ z) * (B *ᵥ z) = C *ᵥ z`, and `rel := {p | Holds p.1 p.2}`.
- `pSpec := ⟨!v[.P_to_V], !v[Wit]⟩`; the prover sends `w`; the verifier is `pure (decide (Holds s (tr 0)))`; `proof : Proof []ₒ Stmt Wit pSpec`.
- A `SampleableType` instance for the empty challenge family is required: `| ⟨0, h⟩ => nomatch h`.

| Statement | Result |
|---|---|
| `perfectCompleteness : Proof.perfectCompleteness init impl (rel F m nx nw) (proof F m nx nw)` (∀ `init`, `impl` for `[]ₒ`) | **Compiles, proved.** `#print axioms`: `[propext, Classical.choice, Quot.sound]`. Proof via `perfectCompleteness_of_run_support` plus `rfl` on the run (about 12 lines). |
| `Proof.rbrKnowledgeSoundness init impl (rel …) verifier ε` | **Does not typecheck** (Bool-witness bug): "Application type mismatch: The argument `rel` has type `Set (S × W)` but is expected to have type `Set (S × Bool)`" |
| `rbrKnowledgeSoundness : (verifier …).rbrKnowledgeSoundness init impl (rel …) acceptRejectRel (fun _ => 0)` | **Compiles, proved.** Axioms are standard only. The extractor reads `tr 0`; the knowledge state function is `if k = 0 then Holds s w else Holds s (tr 0)`. The probability clause is discharged by `isEmptyElim i`. The `toFun_full` step needs a small lemma `pure_accept` (support of `pure (some b)`). About 35 lines. |
| `acceptAll_not_rbrKS`: the always-`true` verifier is not RBR KS for `rel` if some statement is unsatisfiable (for `init = pure ()`) | **Compiles, proved**, standard axioms. This is the non-vacuity check. |
| `knowledgeSoundness … 0` via `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` | **Compiles** (in the ArkLib-HEAD clone), but `#print axioms` shows **`sorryAx`**, inherited from the admitted library theorem. This demonstrates the trap: a contract that accepts this route accepts an unproved claim. |

**Usability friction observed:**
- `tr 0` on a `Transcript (Fin.last 1) pSpec` has type `pSpec⟦:↑(Fin.last 1)⟧.Type 0`, not `Wit`. That breaks `rw`, instance search (`Decidable (Holds s (tr ⟨0,_⟩))` fails to synthesize) and `classical` interplay. Workarounds were `simpa`, and `⟨0, Nat.succ_pos _⟩` instead of `0`.
- `OptionT` `pure` inside `simulateQ` does not simp directly. I restated it as `OracleComp` `pure (some b)` via `change`.
- `Pr{…}[…] > 0` is best handled with `OptionT.prEvent_mk_pos_iff` (VCVio `OracleComp/EvalDist/Measure.lean:412`) before simp turns it into `𝒟[…]`.
- **[I] Overall.** For simple pure verifiers the definitions are usable by an agent within minutes. Dependent transcript types are the main friction.

---

## 9. Implications for recursion.fast

1. **Import (trusted).** Import `ArkLib.OracleReduction.Security.RoundByRound`, which re-exports `Security.Basic`, `Execution` and `ProtocolSpec`. Use:
   - `Reduction` / `OracleReduction`, `Reduction.run`, `challengeQueryImpl`;
   - `Reduction.perfectCompleteness` (or `completeness` with an error) and `Verifier.rbrKnowledgeSoundnessWorstCase` (preferred) or `rbrKnowledgeSoundness`;
   - the `…With` variants if the contract wants the extractor named and executable.

   All are sorry-free definitions.
2. **Do not import or trust any general theorem in the sorry list (§4).** Particularly:
   - `rbrKnowledgeSoundness_implies_knowledgeSoundness`;
   - `append` / `seqCompose` / `liftContext` security;
   - FS and SR.

   If the contract's final claim is KS with error `∑ ε i`, the contract team must prove that implication for `[]ₒ` (**[I]** moderate effort) or state the target as RBR KS plus an error-budget inequality. Submissions using sorried library lemmas are caught by `#print axioms` / `lean4checker`, as in ots.golf and sig.golf. The 281 tainted ArkLib declarations make an axiom check mandatory.
3. **Fix the model in the contract.**
   - `oSpec := []ₒ` (IOP/IR model), with the statement universally quantified over `init` and `impl` as leanerVM does, or with `σ := Unit`.
   - `OracleProof` (oracle access to prover messages) vs `Proof` (full messages) must be decided. For RISC-V verifiers reading a serialized proof, `Proof` matches.
   - Never accept a submitter-chosen `impl`.
4. **Re-state locally for readability.**
   - R1CS: `z = (1, x, w)`, explicit dimensions, field fixed by the contract. Do not use ArkLib's `R1CS.relation` (no constant 1, swapped comments, curried Prop).
   - A short worst-case RBR KS statement with a proven bridge lemma to ArkLib's form.
   - Avoid `Proof.knowledgeSoundness` and `Proof.rbrKnowledgeSoundness` (Bool bug). Use `Verifier.* … acceptRejectRel`.
5. **Error accounting is the contract's job.** It must constrain the per-round error function (for example `∑ i, ε i ≤ 2^{-λ}`) and the challenge types. ArkLib does not tie the error to a security parameter.
6. **"Knowledge" is information-theoretic (P1).** Extractors are unbounded. For a single proof this is fine. For the batcher and recursion, a KS theorem certifies witness *existence*, not efficient extraction; this links to PLAN §1.7 and leanerVM's open recursion problem. If computational meaning is wanted, require an executable extractor, as ToyProblem's `Impl.IRS` does, and cost it.
7. **No library protocol to build on yet.**
   - ToyProblem is the only sorry-free multi-round RBR KS example; it is a good template.
   - Sumcheck RBR KS, Spartan, FRI, WHIR and BCS are not available sorry-free.
   - Submissions must prove protocol-specific RBR KS end-to-end themselves, without relying on library composition. This affects the MVP: the baseline should be a "send witness" protocol, which the probe shows takes about 50 lines of proof, or ToyProblem-like.
   - Proximity-gap results usable today without `sorry`: RS unique-decoding correlated agreement (BCIKS20 §4–6 UDR), the RS MCA Johnson-range bound for lines (`mcaError_affineLine_johnson_le`), DG25 tensor gaps, and the Johnson bound. The BCIKS20 list-decoding regime (Thm 5.1) is `sorry`.
8. **The cost function cannot use ArkLib query counting** (`numQueries` is `sorry`; oracle security is via full messages). Measure cost in the RISC-V emulator.
9. **Pin choice.** The legacy layer is identical in 7653a90 and db7005f. Pinning leanerVM's revision gives a prebuilt environment, but its build lacks `Implications` and `ProofSystem`. The native SR theorem exists only in db7005f.

---

## Appendix: verification commands

```sh
cd /home/devops/Verified-zkEVM/ArkLib
git diff --stat 7653a901ed46 HEAD -- ArkLib/OracleReduction ArkLib/Interaction
python3 -c "import json;d=json.load(open('scripts/axiom_baseline.json'));print(len(d['sorry']))"   # 281
cd /home/devops/Verified-zkEVM/leanerVM && lake env lean /home/devops/CambridgePQ/recursion.fast/probes/arklib-probe/ToyR1CS_leanerVM.lean
```
