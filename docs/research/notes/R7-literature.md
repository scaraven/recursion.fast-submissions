<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `notes/R7-literature.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# R7: Literature and deep-research note for recursion.fast

Task R7 (PLAN.md §2, Phase A). Compiled 2026-10-10. The note covers seven areas:
1. the theory of the security notions (IOP, BCS, RBR (knowledge) soundness, Fiat–Shamir, holography);
2. hash-based verifier costs;
3. proximity gaps as of 2026;
4. recursion and accumulation definitions, and recursive extraction;
5. recursion costs in practice;
6. formal verification of SNARKs and zkVMs;
7. Lean-checked autoresearch competitions and reward hacking.

Sections 1 and 3 were researched by the R7 agent. Sections 2 and 5 (costs), 4 (recursion) and 6–7
(formal methods and competitions) were researched by three helper agents and edited and
cross-checked here. A consolidated BibTeX block is at the end.

**Evidence tags.** Every claim carries one of these tags (the helper sections keep their own
tag spellings):
- **[P]** or **[verified]**: read in a primary source (paper PDF or ePrint page, official repo or docs).
- **[D]**: derived here from primary-source parameters.
- **[S]**: secondary source only.
- **[?]** or **[unverified]**: not confirmed.

Several ePrint PDFs returned HTTP 403 to direct fetches; the helpers read Wayback copies. The
Chiesa–Yogev book was read in full text, in its 2026-03-25 version from the authors' GitHub. The
BCHKS25 paper was read in full text from the Toronto mirror.

---

## 0. Decision-relevant findings (TL;DR)

1. **Use the CY-book chain as the security story, and state which link Lean proves.** The chain is
   RBR-KS of the IOP ⇒ state-restoration KS, with κ_sr(t) ≤ (t+k)·κ_rbr ⇒ BCS argument KS, with
   κ_BCS(t) ≤ (t+k)·κ_rbr + 3.5·t²/2^λ for t ≥ 2(log l+1)·l (CY Thm 26.1.1 + Thm 31.3.1). The
   holographic/COS variant adds a 4·l_0²/2^λ term. A per-round Lean bound of 2^{-λ_r} therefore
   yields only ≈ 2^{-(λ_r − log t)} against t RO queries.
   - Arbitrary R1CS with succinct verification needs the **indexed (holographic) model**: the
     verifier gets vik, the commitment to the matrices (§1.1).
   - The RBR-KS definition comes in several non-equivalent variants (CY; WARP / ArkLib backward
     per-round extractor; ArkLib one-shot). The contract must pin exactly one (§1.2).
2. **Fiat–Shamir instantiation attacks fall outside any IOP-level theorem and must be ruled out by
   contract rules.**
   - KRS25 (CRYPTO 2025) breaks FS-compiled GKR when the hash is computable by the proved circuit.
     That is always the case in recursion.
   - Fenzi (ePrint 2026/1838, Sep 2026) extends this to R1CS *generated from adversarial programs*.
     Spartan and Aurora variants are affected.
   - The proven fix is to absorb the generated statement (vik ‖ x) before the first challenge. The
     trusted harness, not the submission, should fix that initial absorption.
3. **Proximity gaps.** The "up to capacity" conjectures (BCIKS20 CA, WHIR MCA, DEEP-FRI list
   decoding) are **false** in at least some regimes: Diamond–Gruen (CRYPTO 2026), Crites–Stewart,
   BCHKS25, Krachun–Kazanin–Haböck (prime fields, η = Θ(1/log n) below capacity).
   - What is proven: unique decoding, and Johnson γ < 1−√ρ−η with a = O(n/η^5) exceptional points
     (BCHKS25, improving BCIKS20's O(n²/η^7)).
   - MCA for all polynomial generators is proven up to Johnson (BCGM25, CCC 2026). This makes
     WHIR's Johnson regime provable.
   - Capacity-achieving gaps are proven only for folded RS, multiplicity, subspace-design and
     *random* RS codes (GG25 / GGSW26), not for the smooth-domain RS codes that FRI/STIR/WHIR use.
   - **Lean proofs must use UDR or Johnson parameters.** These cost ≈1.5–2× (Johnson) or 2–4× (UDR)
     the queries of the conjectured parameters. The proximity-gap theorem itself will almost
     certainly have to be a named, human-audited trusted hypothesis transcribed from a proven
     theorem.
4. **Verifier-cost anchors (proven regime, 128-bit)** are below. Precompiles change rankings by
   10–100×, so the ISA/precompile policy is a first-order design decision.

   | Data point | Proof size | Hash compressions | Native verify time |
   |---|---|---|---|
   | WHIR-Johnson, 2^24 variables, ρ=1/2 | ≈299 KiB | ≈5.1k | ≈2.5 ms |
   | WHIR-UD, same setting | 621 KiB | 10k | — |

   | Recursion step | Cost |
   |---|---|
   | Plonky2 recursion circuit (conjectured 100-bit) | 2^12 gates, ≈75% of it Merkle hashing |
   | leanVM 2→1 recursion (128-bit, Johnson, no conjecture) | ≈5.6–6.9×10^5 cycles of its field-native ISA, ≈0.3–0.4 s on a laptop |
   | Jolt verifier in a Jolt RISC-V guest (with field and hash inlines) | ≈7×10^7 cycles |

   No published cycle count exists for a STARK verifier running as *plain* RV64IM guest code
   (estimate 10^7–10^8 cycles; measure in P4).
5. **The batcher should be specified as split accumulation / folding**, with RBR-KS of the
   interactive reduction R_acc × R_acc → R_acc as the Lean target (WARP Thm 2.8 gives the
   (t+k)·ε_rbr compilation).
   - Soundness of the *recursive* PCD tree is not a provable Lean theorem in the ROM. BCG24 (TCC
     2025) shows relativized succinct arguments in the ROM do not exist, and textbook PCD theorems
     cover only constant depth, whereas a 2-to-1 tree has depth log N.
   - The recursion heuristic should therefore be a named axiom, with the CGSY24-style bound
     κ_ARG(λ, q, s + O(N·t_E)) reported as the advertised level.
   - Bounded-depth schemes (BMNW24) have real attacks beyond depth d. For them, d and the decider
     chain must be declared and enforced.
6. **Formal-methods precedent.** No end-to-end machine-checked SNARK verifier *binary* with
   protocol-level KS exists yet. Existing work falls into three layers:
   - protocol soundness: ArkLib sumcheck, Isabelle/STARK, Lean FRI RBR;
   - circuit-to-ISA correctness: SP1, OpenVM, Jolt-QED, S-two AIR;
   - implementation equals model: the ZKsync EasyCrypt verifier.

   recursion.fast would be the first to join the first and third layers. ArkLib has the RBR-KS
   definitions, but its FS/BCS/duplex-sponge layers still contain `sorry`s (≈228 in total at
   db7005f).
7. **Competition hygiene.**
   - ots.golf's exact-refinement certificate (RV64IM image ≡ Lean verifier on every input), checked
     by comparator, is the template. Use the axiom whitelist {propext, Quot.sound,
     Classical.choice}, no `native_decide`, and external kernels.
   - Real failures have been *specification* failures: vacuous theorems (SP1 audit), cost-cap
     vacuity (ots.golf AUDIT), and statement rewriting via `local notation`.
   - Three Lean kernel proof-of-False bugs were fixed in 4.34.0 (Sep 2026), and nanoda shared some
     of them.
   - Completeness is mandatory, because an always-reject verifier is trivially sound.
   - **better.codes** (Yukon × zkSecurity, ArkLib-based, Lean-scored) is the closest live analogue.
     The EF Proximity Prize ($1M, deadline 2027-12-31) frames its grand challenges at ε* = 2^{-128}
     for rates 1/2–1/16.

---

## 1. Security notions: IOPs, BCS, round-by-round (knowledge) soundness

### 1.1 Objects

- **IOP** (Ben-Sasson–Chiesa–Spooner, TCC 2016-B [BCS16]; independently "probabilistically checkable
  interactive proofs" [RRR16]). k rounds; in round i the prover sends an oracle string Π_i (over alphabet
  Σ_i, length l_i) and the public-coin verifier replies with uniform ρ_i ∈ R_i; at the end the verifier
  queries the oracles and decides. Cost measures: round complexity k, proof length Σ l_i, query
  complexity q, verifier time.
- **IOPP** (IOP of proximity): the verifier has oracle access to the input itself (e.g. a function
  f: D → F) and must reject words δ-far from a code (Reed–Solomon) — FRI, STIR, WHIR are IOPPs.
  Soundness is parameterised by the proximity δ; it is *this* parameter that the proximity-gap
  results of §3 control.
- **Holographic IOP / preprocessing** ([CHMMVW20-Marlin] Marlin, [COS20] Fractal; CY book ch. 32). The
  relation is *indexed*: triples (i, x, w) with a large index i (here: the R1CS matrices A,B,C) and a
  small instance x (public inputs). An indexer I (deterministic, run once) produces an oracle encoding
  I(i) that the verifier may query; a preprocessing NARG has (pik, vik) := I^f(i), and V^f(vik, x, π) runs
  in time sublinear in |i|. The COS transformation (holographic analogue of BCS) commits to I(i) with a
  Merkle tree MT_0 whose root is part of vik. **This is the model needed for succinct verification of
  arbitrary R1CS** (PLAN §1 item 3): the verifier reads vik (a hash), not the matrices.
  Soundness of an indexed relation must quantify over *adversarially chosen* indices
  (CY Def. 32.4.2: the malicious prover outputs (i, aux)), which is exactly what a competition wants
  (agents should not choose the benchmark index, but the definition is stronger anyway).

### 1.2 Soundness notions (cleanest current statements: Chiesa–Yogev book, version of 2026-03-25)

The CY book [CY24-Book] (CC BY-SA, continuously updated; the copy fetched for this note is dated
**25 March 2026**) is the best single reference; the definitions below follow it.

- **State function** (Def. 31.1.1). A deterministic, possibly inefficient RBRState(x, trc) ∈ {0,1};
  value 0 means "doomed" (the verifier will reject), 1 means the prover has escaped. Axioms:
  (i) State(x, ∅) = 0; (ii) prover moves cannot un-doom: State(trc)=0 ⇒ State(trc‖Π)=0 for every
  Π; (iii) a full transcript with State = 0 is rejected by V. (Only verifier randomness can flip
  0 → 1; the RBR error bounds the probability of that flip.)
- **RBR soundness** (Def. 31.1.2): ∀ x ∉ L, ∀ i, ∀ P̃,
  Pr_ρ_i[State(x, trc_{≤i}‖ρ_i) = 1 | State(x, trc_{<i}‖Π_i) = 0] ≤ ε^rbr_i(x).
  Standard soundness ≤ Σ_i ε^rbr_i ≤ k·ε^rbr (Claim 31.1.3).
- **RBR knowledge soundness** (Def. 31.1.6): there are a state function and a *polynomial-time
  straight-line* extractor E such that ∀ x, i, P̃: Pr[(x, w) ∉ R ∧ State(trc_{≤i}‖ρ_i)=1 |
  State(trc_{<i}‖Π_i)=0, w ← E(x, (Π_j)_{j∈[k]})] ≤ κ^rbr_i(x). Note: in the CY formulation the extractor
  receives *all prover oracle strings including those sent after round i* (the continuation is run);
  ArkLib's formulation (see R4) should be checked against this — variants in which E only sees the
  partial transcript up to round i are stronger. Standard straight-line knowledge error ≤ Σ_i κ^rbr_i.
- **Variants in use (must be pinned by the contract).** (a) CY: one extractor E applied to the
  full list of prover strings. (b) WARP [BCFW25-WARP, Def. 2.6/2.7] and ArkLib's
  `KnowledgeStateFunction` (`ArkLib/OracleReduction/Security/RoundByRound.lean`, HEAD db7005f): a
  *per-round backward* extractor `extractMid` that maps a witness for round i+1 to one for round i,
  with the state function indexed by an intermediate witness; ArkLib's docstring states it
  deliberately generalises "ABF26 Definition A.5" in two ways (witness transformation across prover
  moves; one-directional full-transcript condition). ArkLib also has `rbrKnowledgeSoundnessOneShot`
  (extractor gets the partial transcript and the prover's query log). These are not obviously
  equivalent; the trusted spec should name exactly one, and the RBR ⇒ SR ⇒ NARG implication proved
  (or cited) must be for that one.
- **State-restoration (SR) soundness / knowledge** (Def. 23.2.2/23.2.3; originally [BCS16]): the
  malicious prover may rewind the verifier to any previously-seen state and request fresh randomness,
  with total budget of t moves; it wins if some complete transcript accepts (x ∉ L). This is the
  property that Fiat–Shamir and BCS *actually* need.
- **RBR ⇒ SR** (Thm 31.2.1, 31.3.1): ε^sr(t) ≤ (t + k)·ε^rbr and κ^sr(t) ≤ (t + k)·κ^rbr (straight-line).
  Holmgren [Hol19] shows RBR soundness and SR soundness are (qualitatively) equivalent for IPs, and
  that neither follows from FS soundness in the ROM. RBR soundness was introduced in
  [CCHLRRW19] ("Fiat–Shamir: from practice to theory", STOC 2019; merges ePrint 2018/1004 and
  Canetti–Lombardi–Wichs), RBR *knowledge* soundness in
  Chiesa–Manohar–Spooner [CMS19] (QROM) and Fractal [COS20].
- **Special soundness** is the other route: Attema–Fehr–Klooß [AFK22] (TCC 2022, JoC 2023): for
  (k_1,…,k_μ)-special-sound IPs, FS knowledge error grows only linearly in the number Q of RO queries
  (≈ (Q+1)·κ, κ the interactive knowledge error), rather than Q^μ. Block–Garreta–Tiwari–Zając
  [BGTZ23] relate the notions for IOPs: generalized special soundness ⇒ generalized RBR soundness;
  generalized RBR knowledge soundness ⇒ generalized special soundness, not conversely.
  For hash-based IOPs (FRI/STIR/WHIR) RBR (knowledge) soundness is the notion actually proven
  ([BGKTTZ23-FSFRI] for FRI's FS security; STIR [ACFY24-STIR] proves RBR soundness; WHIR [ACFY24-WHIR]
  proves RBR knowledge soundness).

### 1.3 Concrete bounds for the compilers (exact statements)

Let t be the adversary's RO-query budget, λ the RO output length (bits), k the round count,
l = max l_i the oracle length, s_FS the FS salt length.

- **FS for IPs** (CY Thm 14.3.1): ε_ARG(λ, n, t) ≤ ε^sr_IP(s, n, t) ≤ (t + k)·ε^rbr_IP.
- **BCS** (CY Thm 25.2.1, soundness):
  ε_ARG(λ, n, t) ≤ ε^sr_IOP(λ + s_FS, n, t) + κ^mm_MT(λ, (l_i), t, t+1) + t²/2^λ,
  and κ^mm_MT + t²/2^λ ≤ 3.5·t²/2^λ when t ≥ 2(log l + 1)·l. Combining with RBR ⇒ SR:

      ε_BCS(t) ≤ (t + k)·ε^rbr_IOP + 3.5·t²/2^λ.

- **BCS knowledge** (CY Thm 26.1.1, straight-line case): κ_ARG(λ,n,t) ≤ κ^sr_IOP(λ+s_FS,n,t) + κ^mm_MT +
  t²/2^λ, hence κ_BCS(t) ≤ (t + k)·κ^rbr_IOP + 3.5·t²/2^λ, with extraction time
  et^sr + et^mm_MT + O(r_max·k·t·log t). (A rewinding variant also exists.)
- **COS (holographic)** (CY Thm 32.8.9): ε ≤ ε^sr_HIOP + κ^mm_MT + t²/2^λ + 4·l_0²/2^λ ≤ … + 4.5·t²/2^λ
  (l_0 = index-oracle length), i.e. the indexer commitment costs one extra birthday-type term.
- **Reading for the competition**: "λ-bit security" of the NARG against t = 2^τ queries needs
  ε^rbr ≤ 2^{-(λ_target+τ)} (roughly) and RO output ≥ 2(λ_target + τ)-ish bits. *The factor (t + k)
  is the reason a Lean RBR-KS bound of, say, 2^{-100} per round only yields ~2^{-100+τ} against a
  2^τ-query adversary after compilation.* Grinding (proof-of-work) adds bits to individual rounds and
  is analysed in CY ch. 28/29 and ethSTARK [ethSTARK21]. Fiat–Shamir with a *duplex sponge*
  (what implementations actually do, e.g. spongefish) is analysed by Chiesa–Orrù [CO25-DuplexFS] (TCC 2025)
  with concrete bounds in the ideal-permutation model; CY's statements assume independent ROs/salts.

### 1.4 What RBR-in-the-IOP-model does *not* cover (FS instantiation attacks)

- Khovratovich–Rothblum–Soukhanov [KRS25] (CRYPTO 2025): practical attack on FS-compiled GKR-based
  protocols with *any* concrete hash, exploiting that the hash is computable by the circuit being
  proven — a ROM proof is no guarantee once the hash is inside the relation (exactly the recursion
  setting).
- Fenzi [Fen26-GenR1CS] (ePrint 2026/1838, Aug/Sep 2026, "How to prove more false statements: Fiat–Shamir
  limitations on (generated) R1CS"): extends this to protocols whose instances are *generated by a
  program* and compiled to R1CS; variants of **Spartan and Aurora for R1CS** are affected whenever a
  cheating prover can build an accepting transcript before the statement is bound. Mitigation with a
  proof: derive the first FS challenge from the *generated statement* (the full R1CS/index commitment
  and public input), not from the generating program.
  **Design consequence:** the trusted harness, not the submission, should fix the transcript's initial
  absorption: FS state := H(domain-sep ‖ vik ‖ x) (vik binding the R1CS). This is outside what an RBR-KS
  theorem in the interactive model can express, so it must be a rule of the contract.

---

## 2. Hash-based SNARK/PCS verifiers: concrete verifier costs

(Helper note, edited; tags [P]/[D]/[S]/[?].)

### 2.1 FRI vs STIR vs WHIR (same harness, from the WHIR paper Table 3) [P]

Setup: 192-bit prime field, λ=128, **CB (conjectured) parameters for all three**, ρ=1/2, single-threaded, Blake3 Merkle hash.

| Degree | FRI size / verify / hashes | STIR size / verify / hashes | WHIR-CB size / verify / hashes |
|---|---|---|---|
| 2^18 | 163 KiB / 2.0 ms / 2.5k | 114 KiB / 2.9 ms / 1.4k | 119 KiB / 0.7 ms / 1.6k |
| 2^20 | 211 / 2.6 / 3.5k | 131 / 3.2 / 1.8k | 133 / 0.8 / 2.0k |
| 2^22 | 257 / 3.2 / 4.5k | 143 / 3.4 / 2.2k | 143 / 0.9 / 2.3k |
| **2^24** | **306 / 3.9 / 5.6k** | **160 / 3.8 / 2.6k** | **157 / 1.0 / 2.7k** |
| 2^26 | 371 / 4.7 / 7.1k | 172 / 3.9 / 3.0k | 165 / 1.1 / 3.0k |
| 2^28 | 430 / 5.5 / 8.5k | 189 / 4.3 / 3.5k | 178 / 1.2 / 3.4k |
| 2^30 | 494 / 6.4 / 10k | 200 / 4.4 / 3.8k | 187 / 1.3 / 3.7k |

At ρ=1/4 and 2^24 the sizes are FRI 177, STIR 107 and WHIR 106 KiB, and the hash counts are 3.5k, 1.8k and 1.9k. Prover time at 2^24 and ρ=1/2 is FRI 28 s, STIR 36 s and WHIR 34 s, single-threaded.

STIR paper, Table 1 (128-bit, 192-bit field, conjectured) [P]:
- d=2^22, ρ=1/4: STIR 94 KiB and 1,521 verifier hashes, against FRI 154 KiB and 2,821 hashes.
- d=2^28, ρ=1/2: STIR 189 KiB and 3,451 hashes, against FRI 430 KiB and 8,479 hashes.
- Proof sizes improve by 1.25–2.46× and hash counts by 1.55–2.67×.
- Query complexity is O(log d + λ·log log d) for STIR, against O(λ·log d) for FRI.
- STIR and FRI verifier *time* are similar: 2.1 ms vs 1.9 ms at 2^22. WHIR's gain in time comes from fewer field operations, since its verifier does no divisions.

### 2.2 WHIR across regimes (WHIR paper Table 5) [P]

Setup: Goldilocks³ (cubic extension), λ=128, k=4, ρ=1/2.

| Variables m | UD size / verify / hashes | JB size / verify / hashes | CB size / verify / hashes |
|---|---|---|---|
| 2^18 | 399 KiB / 3.0 ms / 4.8k | 228 / 1.8 / 2.9k | 120 / 0.9 / 1.6k |
| 2^20 | 481 / 3.7 / 6.7k | 252 / 2.1 / 3.6k | 133 / 1.1 / 2.0k |
| 2^22 | 541 / 4.1 / 8.0k | 274 / 2.3 / 4.3k | 144 / 1.2 / 2.3k |
| **2^24** | **621 / 4.8 / 10k** | **299 / 2.5 / 5.1k** | **156 / 1.4 / 2.7k** |
| 2^28 | 770 / 6.7 / 14k | 339 / 2.9 / 6.4k | 177 / 1.6 / 3.4k |

At ρ=1/16 and 2^24 the sizes are UD 535, JB 140 and CB 74 KiB, and the hash counts are 10k, 2.7k and 1.4k. Lower rates help JB and CB a lot but barely help UD.

At λ=100 (Goldilocks², Table 2/§6.3.1) with m=24, ρ=1/2:
- WHIR-UD: 390 KiB, 2.39 ms.
- WHIR-CB: 101 KiB, 0.61 ms.
- BaseFold (ZCF24, unoptimised): 7.95 MiB, 24 ms.

The abstract's headline is 2^22, 100-bit: 63 KiB, 360 µs verify, 1.2 s commit plus open. This is the CB regime.

PCS verifier-time comparison (Table 4, m=24, CB) [P]:

| λ | Brakedown | Ligero | Greyhound | Hyrax | PST | KZG | WHIR ρ=1/2 | WHIR ρ=1/16 |
|---|---|---|---|---|---|---|---|---|
| 100 | 3500 ms | 733 | – | 100 | 7.81 | 2.42 | 0.61 | 0.29 |
| 128 | 3680 | 750 | 130 | 151 | 9.92 | 3.66 | 1.4 | 0.6 |

**Caveat.** WHIR-JB in the paper assumed MCA up to Johnson (Conjecture 4.12, item 1). That is now a theorem (BCGM25), so the **JB column is the best proven WHIR data point**: about 300 KiB, about 5k hashes and about 2.5 ms at 2^24 and 128 bits. The CB column has no proof.

### 2.3 FRI / DEEP-FRI / ethSTARK parameters [P]

**FRI (BBHR18) and DEEP-FRI (BGKS20).**
- DEEP-FRI improves the soundness of a single FRI query by sampling outside the box. Blaze uses its field-agnostic analysis and needs 329 queries at ρ=1/2 for 100 bits (Blaze §8.2).

**ethSTARK v1.2 (July 2023)** gives explicit query counts at ρ=1/4 with 20 bits of grinding:

| Target λ | Conjectured (toy problem, §5.10.1) | Provable (§5.10.2) |
|---|---|---|
| 80 | s=31, extension degree 2 | s=79 |
| 100 | s=41, extension degree 2 | s=104 |
| 128 | s=55, extension degree 3 | s=140, and needs extension degree 4 (|K|≥2^244) |

The provable column costs about 2.5× the queries. The original EF grant targets were 200 kB proofs for 100k Rescue hashes at 80 bits, and a 10 ms verifier.

**Superseded.** ethSTARK's provable analysis uses the BCIKS20 Johnson bounds. The newer BCHKS25 bounds reduce the provable query count.

### 2.4 BaseFold, FRI-Binius, Blaze, Ligerito, Brakedown, Orion, Ligero [P unless marked]

**BaseFold (ZCF24, CRYPTO 2024).**
- Multilinear PCS from foldable codes (FRI plus sumcheck).
- Query count is O(λ·m). Proven only in UDR in the original paper.
- At 2^24, 100 bits: 7.95 MiB and 24 ms (unoptimised).
- Used by SP1 Hypercube as the dense PCS under Jagged (§5).

**FRI-Binius / "Polylogarithmic proofs for multilinears over binary towers" (DP24, ePrint 2024/504).**
- 100-bit **provable** analysis over F_{2^128}.
- Higher-arity "oracle skipping" folding with ϑ=4.
- Proof sizes for F2-multilinears:

  | ℓ (variables) | ρ=1/2 | ρ=1/4 | ρ=1/8 |
  |---|---|---|---|
  | 24 | 0.202 MiB | 0.143 MiB | 0.129 MiB |
  | 28 | 0.342 MiB | 0.237 MiB | 0.210 MiB |
  | 32 | 0.514 MiB | 0.351 MiB | 0.336 MiB |

- For large-field multilinears in UD at 100 bits: 488 KiB at ℓ=24, against 390 KiB for WHIR-UD.
- 28 variables over F2: verifier under 1 ms, 0.351 MiB, commit/open 44/71 ms multithreaded. Plonky3's verifier on comparable data is about 20 ms.

**Binius (DP23, ePrint 2023/1784).** Towers of binary fields with a Brakedown-style PCS. **Superseded** for the PCS by DP24 (FRI-Binius) and Binius64.

**Blaze (BCFRRZ, ePrint 2024/1609).**
- RAA codes plus code-switching onto BaseFold.
- The RAA code has distance 0.19, which needs **1,059 column queries** for 100 bits. Brakedown with distance 0.07 needs about 2,953.
- The verifier is about 150 ms at all sizes; the row inner product dominates. Proof is about 2.5 MiB at ℓ=28 (as cited by DP24).
- The prover is fast: 30.5 s at 2^29, against 145.7 s for BaseFold.
- A poor fit for a cheap verifier.

**Ligerito (Novakovic–Angeris, ePrint 2025/1187, May 2025).**
- Ligero-style, repeated with sumcheck over any code whose generator rows are evaluable.
- Benchmark: λ=100, ρ=1/4, F_{2^128} with F_{2^32} as the first-round field, on an M1 laptop with 8 threads.
- Proof sizes are 145 KiB at 2^20, **255 KiB at 2^24**, 360 KiB at 2^28 and 420 KiB at 2^30. Proving takes 1.3 s at 2^24.
- The authors use |S_i| = 148 queries per round. That equals −100/log2(0.625), i.e. **UDR (proven)** [D].
- The leanVM README treats WHIR and Ligerito as the same PCS ("WHIR aka Ligerito").

**Brakedown (GLSTW, CRYPTO 2023, ePrint 2021/1043).**
- Linear-time prover with Spielman codes.
- The verifier is O(√N), which is very expensive: 3.5 s at 2^24 in WHIR Table 4.

**Orion (XZS22, CRYPTO 2022, ePrint 2022/1010).**
- Brakedown-like, with proof composition.
- 2^20 gates: 3.09 s prove, 1.5 MB proof. Verify time is not in the abstract [P].
- Orion+ (CBBZ23) composes with KZG.

**Ligero (AHIV17, CCS 2017).**
- O(√N) proof and verifier.
- 733–750 ms at 2^24 in WHIR Table 4.

### 2.5 SNARKs for R1CS

**Spartan (Setty, CRYPTO 2020, ePrint 2019/550).**
- Sumcheck-based R1CS SNARK. SPARK is its sparse-polynomial commitment compiler.
- The original instantiation uses curve-based PCSs. It reports sublinear verification for instances up to 2^20 constraints.
- The verifier is O(log² n) field operations plus PCS checks. **Pair with WHIR or BaseFold for a hash-based R1CS verifier.**
- WHIR §1 and STIR each build an R1CS SNARG on these lines. STIR estimates 220 KiB for n=2^24 R1CS at 128 bits and ρ=1/2.
- SuperSpartan (CCS) is used by leanVM and by Jolt's outer sumcheck.

**Circle STARKs (Haböck–Levit–Papini, ePrint 2024/278, rev. Dec 2024) / Stwo.**
- FRI over the circle curve over M31.
- Stwo's code computes `security_bits = log_blowup · n_queries + pow_bits` (`crates/stwo/src/core/pcs/mod.rs`). This is the **CB/conjectured formula** [P].
- l2beat reports production Stwo at "96 bits + 30 bits PoW", with Blake2s hashing [P, l2beat].

**Plonky3.** A toolkit (BabyBear, KoalaBear, M31 and Goldilocks fields; Poseidon2 and Keccak/Blake3 hashes; FRI and Circle-FRI).
- DP24 measured its verifier at about 20 ms on 2^28 F2-equivalent data.
- `Plonky3-recursion` (active Oct 2026, unaudited):
  - Defaults are a per-error-term target of "124" bits for FRI and 66 for WHIR, with FRI query PoW of 15 bits and a typical log_blowup of 3.
  - It publishes no recursion benchmark numbers [P/?].

**Jolt (AST24, EUROCRYPT 2024, ePrint 2023/1217) and Twist and Shout (Setty–Thaler, ePrint 2025/105).**
- Lookup- and memory-checking-based zkVM using sumcheck. Twist and Shout **supersedes Lasso/Spice** as Jolt's memory checking.
- The PCS changed over time: Hyrax, then Dory (BN254, not post-quantum), then 2026 "Lattice Jolt" with Akita (lattice, post-quantum).
- Lattice Jolt proofs are reportedly under 100 KB [S].
- See §5 for the recursion cost.

### 2.6 leanVM (formerly leanMultisig), leanEthereum [P, README read 2026-10-10]

**Two generations. Record both.**

**(a) Current `main`.**
- 192-bit binary field (degree-3 tower over a 64-bit field). WHIR/Ligerito PCS. BLAKE2s as a placeholder hash. SuperSpartan plus logup; Flock for hash proving.
- Security: "128-bit ROM (64-bit QROM) soundness, no proximity gap conjecture".
- The ISA is still leanISA. **A migration to RV64IM is planned.**
- Benchmarks on an M4 Max CPU:

  | Workload | Cycles | Proof | Prove | Verify |
  |---|---|---|---|---|
  | XMSS aggregation, 900 signatures | 995,578 | 317.4 KiB | 0.545 s | 3.98 ms |
  | **2→1 recursion over leaves of 900 XMSS** | **562,737 (2^19.1)** | **190.2 KiB** | **0.272 s** | **3.46 ms** (log_inv_rate=2, 8.4 GiB RAM) |
  | Fibonacci | – | – | – | – (6.18 M cycles/s) |
  | BLAKE2s | – | – | – | – (486k compressions/s) |

> **Cross-check (R7).** The local checkout `/home/devops/leanEthereum/leanVM` (commit a386121,
> 2026-09-03) README reports, for the same command (`recursion --n 2 --xmss-per-leaf 900
> --log-inv-rate 2`): 686,085 cycles (MUL 31%, DEREF 31%, XOR 25%, BLAKE2S 2.7%), 206.3 KiB,
> 0.394 s proving, 14.6 ms verifying, 10.4 GiB; security "128-bit (LDR Johnson, no proximity gaps
> conjecture)"; field: 192-bit binary tower of degree 3 over a 64-bit field; PCS WHIR (aka Ligerito);
> BLAKE2s proven via Flock. The figures above (562,737 cycles etc.) are from the live README on
> 2026-10-10 and supersede these.

**(b) Historical `koalabear` branch.**
- KoalaBear⁵ with Poseidon digests of 4 field elements (about 124 bits).
- "≈124 bits provable security (Johnson bound + degree 5 extension)". The proven regime is the default.
- Recursion with n=1, aggregating 700-XMSS proofs:

  | Rate | Proven (JB) | Conjectured (PGC) |
  |---|---|---|
  | 1/2 | 0.22 s, 268 KiB | 0.16 s, 136 KiB |
  | 1/4 | 0.25 s, 179 KiB | 0.18 s, 93 KiB |

  - n=2 at rate 1/4: proven 0.47 s and 187 KiB, against conjectured 0.34 s and 98 KiB.
  - Per-proof cost is about 0.22–0.26 s proven.
- XMSS aggregation: 1,027–1,426 sigs/s proven, against 1,049–1,481 conjectured. Proofs are about 2× larger in the proven regime.
- **This is the cleanest public measurement of "conjectured vs proven" cost on a real recursion step: about 1.4× time and about 1.9–2× size.**

---

## 3. Proximity gaps: status as of October 2026, and what can be *proven*

Notation: C = RS[F_q, D, k], n = |D|, rate ρ = k/n, relative distance δ = 1 − ρ (+1/n). A *proximity
gap* for lines at radius γ with "a exceptional points": for u_0, u_1, if |{z : Δ(u_0 + z·u_1, C) ≤ γ}| ≥ a
then (u_0, u_1) has *correlated agreement* (a common γ-agreement set). Batching/folding soundness
error ≈ a/q. *Mutual correlated agreement* (MCA, WHIR [ACFY24-WHIR]) strengthens this: the agreement
set of the random combination is itself shared. FRI/STIR/WHIR soundness = (batching/folding term,
∝ a/q) + (query term ≈ (1 − γ)^s for s queries) + (Fiat–Shamir term, §1.3).

### 3.1 Proven positive results (usable in a Lean proof, in principle)

| Regime | Result | Exceptional set a (error ≈ a/q) | Source |
|---|---|---|---|
| Unique decoding γ < δ/2 | BCIKS20 Thm (UDR) | a > n (error n/q), lossless | [BCIKS20] |
| γ ∈ (δ/3, δ/2 − 1/n) | BCHKS25 Thm 1.3 | a ≥ (δ/γ − 1)/(δ − 2γ) — **O(1)** with an arbitrarily small proximity loss ε* (a ≥ 1+γ/ε*); lossless (Cor. 1.4) for a > γn + 1 | [BCHKS25] |
| Johnson γ < 1 − √ρ − η | BCIKS20 | a > (m+½)^7 n² /(3ρ^{3/2}), m = max(⌈√ρ/(2η)⌉, 3): **O(n²/η^7)** | [BCIKS20] |
| Johnson γ < 1 − √ρ − η | BCHKS25 Thm 1.5 | a > [2(m+½)^5 + 3(m+½)γρ]/(3ρ^{3/2}) · n + (m+½)/√ρ: **O(n/η^5)** | [BCHKS25] |
| MCA up to Johnson | all polynomial generators (powers, lines, curves) for every RS code | O(m^7 n²/ρ^{3/2})·d/q per [secondary summary; not checked in PDF] | [BCGM25-MCA] (CCC 2026); also Haböck note [Hab25-MCA] |
| MCA a constant number of integer steps past Johnson | O_{r,h}(K^6/q); relative gain O(1/n) (negligible in practice) | | [Jo26-MCA] (preprint) |
| Up to 1 − R − η for *folded* RS, multiplicity codes, subspace-design codes, *random* RS/linear codes | optimal (capacity) proximity gaps | | [GG25] (ePrint 2025/2054), [GGSW26] arXiv 2607.08516 |

Notes. (i) The Johnson-regime results are what a "proven-security" deployment uses today (cf. EF
soundcalc). (ii) The [GG25]/[GGSW26] capacity results do **not** cover explicit RS codes on smooth
(FFT) domains, which is what FRI/STIR/WHIR use; they are an argument for designing IOPPs over folded
RS / multiplicity codes or random evaluation sets, a legitimate design-space axis for submissions.
(iii) Interleaved codes (Ligero/Brakedown/Binius-style): Diamond–Gruen [DG25-Interleaved] (IACR CiC
2025) give proximity gaps for interleaved codes.

### 3.2 Negative results (late 2025–2026): the "up to capacity" conjectures are false

- **Diamond–Gruen [DG25-Dist]** (ePrint 2025/2010, CRYPTO 2026): infinite families of RS codes whose
  radius-z Hamming balls cover more than n^{c*}/q of F_q^n; disproves the BCIKS20 capacity conjecture.
  Regime: rate → 0 and relative radius → 1. Suggest restricting the conjecture to rates bounded
  below by a constant.
- **Crites–Stewart [CS25-PGC]** (ePrint 2025/2046, Web3 Foundation): disproves the BCIKS20 correlated
  agreement up-to-capacity conjecture, the WHIR MCA up-to-capacity conjecture, and (via Elias's
  classical bound) the DEEP-FRI list-decodability-up-to-capacity conjecture; shows CA with small
  error ⇒ RS list-decodability; proposes the modified conjecture δ ≤ 1 − H_q(δ) − 1/n − η ("up to
  list-decoding capacity"), costing ≈ 1/log₂ q in radius (≈1/31 for a 31-bit field) [radius formula
  from a secondary summary; check PDF].
- **Ben-Sasson–Carmon–Haböck–Kopparty–Saraf [BCHKS25]** (ePrint 2025/2055): besides the positive
  results above: (a) at/beyond Johnson, for some RS codes over **characteristic-2** fields (δ = 15/16,
  γ = 3/4) loss < 1/8 needs a ≥ n^{2−ε} — i.e. the O(n) Johnson bound is essentially tight and
  beyond-Johnson gaps need much larger fields; (b) for any τ, codes needing n^τ exceptional points at
  δ − Ω_τ(1); (c) for all RS codes, improved proximity gaps ⇒ improved list decoding, so "better
  list-decoding bounds are a prerequisite for proximity gaps beyond Johnson"; (d) an attack on the
  basic and DEEP STARK (CYCLE-SUM AIR) showing the DEEP-ALI soundness is truly governed by list
  decodability (Thm 1.17), and an attack on the **ethSTARK toy problem**.
- **Krachun–Kazanin–Haböck [KKH26]** (ePrint 2026/782): RS codes on multiplicative subgroups of
  **prime fields**: an affine line not θ-close yet containing 2^{Ω(1/η)} codewords within θ = 1 − ρ − η,
  η = Θ_ρ(1/log n); Kambiré [Kam26] (arXiv 2604.09724) writes out the construction explicitly.
- **Gao–Yang–Xu–Kan [GYXK26]** (arXiv 2607.10572): list-decoding counterexamples ⇒ explicit lower
  bounds on MCA error.
- Survey/targets: Arnon–Boneh–Fenzi [ABF26] (ePrint 2026/680) "Open Problems in List Decoding and
  Correlated Agreement" (July 2026 revision adds the KKH comparison, concrete attack estimates and an
  MCA lower bound; PDF could not be fetched for this note).

### 3.3 Consequences for recursion.fast

1. **Lean proofs cannot assume conjectures**, and the conjectures most deployed systems used are now
   false in at least some regimes. The contract must therefore treat the proximity-gap bound as
   either (a) a *proved* lemma inside the submission (Johnson-regime results are deep: BCIKS20's
   Guruswami–Sudan-over-function-fields argument; ArkLib is formalizing this layer — R4 reports its
   sorry status), or (b) a *trusted, named hypothesis* in the verification repository, stated exactly
   as a proven theorem from the literature (e.g. "BCHKS25 Thm 1.5"), audited by humans, with a
   capped regime (γ ≤ 1 − √ρ − η, a as given). Option (b) mirrors better.codes/ArkLib's tagged sorries
   and is the only feasible MVP route; it must be clearly flagged in the trusted base.
2. **Query cost of proven vs conjectured regimes** (query term (1−γ)^s ≤ 2^{−λ}; s ≈ λ/(−log₂(1−γ)),
   λ = 128, ignoring η slack and grinding):

   | ρ | UDR γ=(1−ρ)/2 | Johnson γ≈1−√ρ | "capacity" γ≈1−ρ (now refuted in some regimes) |
   |---|---|---|---|
   | 1/2 | 309 | ≈257 | 128 |
   | 1/4 | 189 | ≈128 | 64 |
   | 1/8 | 155 | ≈86 | 43 |
   | 1/16 | 141 | ≈64 | 32 |

   Proven (Johnson) parameters cost ≈2× the queries of capacity-conjectured parameters; this
   directly doubles the dominant verifier cost (Merkle path hashing) of FRI/STIR/WHIR verifiers. The
   competition will reward (a) lower rates (more prover work), (b) grinding, (c) tighter proven
   analyses, (d) codes with provable capacity gaps — all legitimate if the prover budget is
   constrained (PLAN §1 item 5).
3. **Field size.** The Johnson-regime batching error a/q with a = O(n/η^5) (or O(n²/η^7)) forces
   q ≫ 2^λ·n/η^5: 31-bit fields need degree-4–6 extensions for challenges; this interacts with the
   RV64IM cost model (extension-field multiplication cost).
4. **Characteristic 2** (Binius-style towers): BCHKS25 Thm 1.6 shows beyond-Johnson gaps genuinely
   fail for some char-2 RS codes; proven regimes are needed there too.
5. **Ecosystem policy**: the Ethereum Foundation (Kadianakis, 18 Dec 2025, [EF25-zkEVMsec]) requires
   L1 zkVMs to reach 100-bit *provable* security (soundcalc-estimated) by end of May 2026
   ("Glamsterdam", proof ≤ 600 KiB, recursion-architecture soundness sketch) and 128-bit provable
   security by end of 2026 ("H-star", proof ≤ 300 KiB, *formal security argument for recursion
   soundness*). A competition objective of "128-bit proven RBR-KS in Lean" is aligned with this
   (and stricter). Whether teams met the May 2026 milestone was not confirmed.
6. **Proximity Prize** (EF, $1M, judges Boneh/Fenzi/Arnon; deadline 31 Dec 2027; Lean encouraged,
   not required): Grand MCA challenge and Grand list-decoding challenge for RS over smooth domains,
   rates {1/2,1/4,1/8,1/16}, target ε* = 2^{−128}. Companion **better.codes** (built by Yukon and
   zkSecurity) is a continuously scored, Lean-verified competition on soundness upper/lower bounds of
   the ABF26 Construction 6.9 toy IOP — the closest existing precedent to recursion.fast's format
   (see R3).

### 3.4 Query cost per regime at 80/100/112 bits, and EF policy (helper note)

Every hash-based PCS (FRI, STIR, WHIR, BaseFold, Ligero-style) sets its query count `s` from a per-query soundness term. With rate ρ, each query buys the following number of bits:

| Regime | Proximity δ | Bits per query | Status (Oct 2026) |
|---|---|---|---|
| UDR (unique decoding) | (1−ρ)/2 | −log2((1+ρ)/2) | **Proven** (BCIKS20 correlated agreement). |
| JBR (Johnson bound) | 1−√ρ−η | ≈ −log2(√ρ+η) | **Proven.** FRI-style correlated agreement up to Johnson is in BCIKS20, improved by BCHKS25. *Mutual* correlated agreement (the property WHIR needs) up to Johnson is proven in BCGM25 (ePrint 2025/2051, CCC 2026). In the WHIR paper (Nov 2024) it was still Conjecture 4.12, item 1. |
| CB ("up to capacity", the ethSTARK toy-problem conjecture) | 1−ρ−η | ≈ log2(1/ρ) | **Conjectured.** It is **disproven** in its general up-to-capacity form by Crites–Stewart (ePrint 2025/2046), and see also Diamond–Gruen 2025/2010. Deployed "conjectured" parameters therefore rest on a refuted conjecture or a weakened variant of it. |

Minimum queries to buy *b* bits after grinding [D]. JB values are lower bounds, since they ignore η and list-size factors.

| log2(1/ρ) | UD bits/q | JB bits/q | CB bits/q | Queries for 80 / 100 / 112 bits (UD; JB; CB) |
|---|---|---|---|---|
| 1 | 0.415 | 0.5 | 1 | UD 193 / 241 / 270; JB 161 / 201 / 225; CB 80 / 100 / 112 |
| 2 | 0.678 | 1.0 | 2 | UD 118 / 148 / 166; JB 80 / 100 / 112; CB 40 / 50 / 56 |
| 3 | 0.830 | 1.5 | 3 | UD 97 / 121 / 135; JB 54 / 67 / 75; CB 27 / 34 / 38 |
| 4 | 0.913 | 2.0 | 4 | UD 88 / 110 / 123; JB 40 / 50 / 56; CB 20 / 25 / 28 |

Rule of thumb: proven-UD costs about 2–4× the queries of CB, and proven-JB about 1.5–2×. Since verifier hashing is roughly linear in the number of queries, this is the single largest knob on verifier cost.

The Ethereum Foundation's targets (blog post, 2025-12-18) are measured with `soundcalc` and count only UDR and JBR as provable:
- 100-bit provable security and ≤600 KiB proofs by May 2026.
- **128-bit provable security and ≤300 KiB proofs by end of 2026**, plus a formal soundness argument for the recursion architecture.

**recursion.fast implication.** Fix the regime in the rules: UDR or JBR only, with a soundcalc-style accounting. Otherwise entrants will use CB parameters and win by about 2× on hashing. *[P for EF post and soundcalc; regime status per the cited papers' abstracts. I did not check the BCGM25 or Crites–Stewart proofs.]*

---

## 4. Recursion and accumulation: definitions and recursive extraction

(Helper note, edited; tags [verified]/[unverified].)

### 4.0 TL;DR for the batcher spec

1. **Specify the batcher as a reduction of knowledge, R_acc × R_acc → R_acc**, or as an accumulation step (R_in, R_acc) → R_acc. Prove **round-by-round (RBR) knowledge soundness** for the *interactive* (IOR / public-coin) version. This is the information-theoretic statement that compiles, via BCS/Fiat–Shamir in the ROM, into straightline state-restoration knowledge soundness of a non-interactive accumulation scheme (WARP Thm 2.8: ε_sr(t) ≤ (t+k)·ε_rbr) **[verified]**. It is also the cleanest object to state in Lean.
2. **Do not ask for a Lean proof that the recursive PCD/IVC is sound.** No such proof is possible without an explicit heuristic. The recursion circuit runs the accumulation verifier, and that verifier calls the hash/RO. *Relativized* succinct arguments in the ROM do not exist (BCG24) **[verified]**. Every hash-based PCD is therefore "provable accumulation in the ROM + heuristic RO instantiation + assumed extractor for the instantiated scheme". State that assumption as an explicit axiom in the spec.
3. **Depth matters.** Standard-model PCD analyses cover only **constant depth**, because extractor size compounds as n^{c^d} (BCMS20 Rmk 5.3) **[verified]**. A 2-to-1 binary tree over N steps has depth log₂N = ω(1), which is outside that regime. The only analysis without depth loss (CGSY24) needs straightline extraction in an oracle model where the SNARK is relativized. That holds only in an idealized, non-succinct model for hash-based systems. **Bounded-depth** schemes (BMNW24) have *concrete attacks* beyond depth d, so d must be a parameter of the spec, with a family of deciders D_0…D_d.
4. **Bind the generated statement into the transcript.** KRS25 and Fenzi 2026 show practical Fiat–Shamir breaks when the proved computation can evaluate the FS hash, or when the R1CS is *generated from an adversarial program*. Fenzi's proven mitigation is to derive the first challenge from the generated statement (the full R1CS instance), not from the program **[verified abstract]**. Both conditions hold by construction in recursion.fast: the circuit contains the hash, and the R1CS comes from RISC-V programs.

---

### 4.1 Formal definitions

#### 4.1.1 IVC and PCD

**IVC (Valiant 2008).** Fix F: (z, ω) ↦ z'. An IVC scheme (G, K, P, V) maps proof Π_{i−1} for "z_{i−1} = F^{(i−1)}(z_0)" plus (z_{i−1}, ω_{i−1}) to Π_i for z_i. Here is the KST22 phrasing **[verified]**:

- *Completeness:* if V(vk, i−1, z_0, z_{i−1}, Π_{i−1}) = 1 and z_i = F(z_{i−1}, ω_{i−1}), then Π_i ← P(pk, i, z_0, z_i; z_{i−1}, ω_{i−1}, Π_{i−1}) satisfies V(vk, i, z_0, z_i, Π_i) = 1 with probability 1.
- *Knowledge soundness:* **for every constant n**, and every expected-poly-time P*, there is an expected-poly-time E such that Pr[z_n = z ∧ ∀i z_{i+1} = F(z_i, ω_i) : (F,(z_0,z),Π) ← P*(pp; r), (ω_i) ← E(pp; r)] ≈ Pr[V(vk,(n,z_0,z),Π) = 1]. KST22 explicitly note that "n is a fixed environment variable", that this is required by all known recursive techniques, and that "there are no known attacks on arbitrary depth recursion" (for unbounded-depth schemes).
- *Succinctness:* |Π| is independent of n.

**PCD (Chiesa–Tromer 2010; BCCT13; BCMS20 formalisation, verified).**
- A *transcript* T is a DAG. Vertices carry local data z_loc^{(u)}, edges carry messages z^{(e)} ≠ ⊥, and the output o(T) is the message on the lexicographically first edge into a sink.
- Vertex u is **φ-compliant** if, for every outgoing edge e: either (base) u has no incoming edges and φ(z^{(e)}, z_loc, ⊥,…,⊥) accepts, or (recursive) u has incoming edges e_1..e_m and φ(z^{(e)}, z_loc, z^{(e_1)},…,z^{(e_m)}) accepts. T is φ-compliant if every vertex is.
- A PCD scheme (G, I, P, V) for a class 𝔽 of compliance predicates satisfies:
  - *Completeness:* ∀A: if φ ∈ 𝔽, and either all z_i = ⊥ or all V(ivk, z_i, π_i) = 1, and φ(z, z_loc, z_1..z_m) accepts, then V(ivk, z, P(ipk, z, z_loc, [z_i, π_i])) = 1 with probability 1.
  - *Knowledge soundness:* ∃ polynomial e such that for every poly-size P̃ there is an extractor E of size ≤ e(|P̃|) with Pr[φ ∈ 𝔽 ∧ V(ivk, o(T), π) = 1 ⇒ T is φ-compliant : (φ, π, T) ← E(pp)] ≥ 1 − negl. In addition, (φ, o, π) from P̃ and (φ, o(T), π) from E must be statistically close.
- *Depth* d(φ) is the maximum depth of any φ-compliant transcript. IVC is PCD on a path, with m = 1.

BCMS20 Theorem 5.2 and COS20 give PCD only **for constant-depth compliance predicates**. The obstacle is recursive extractor blow-up, n^{c^d}. Under subexponential knowledge assumptions d can rise to o(log n) (BCMS20 Rmk 5.3) **[verified]**. BCCT13 obtain polynomial-length IVC from constant-depth PCD with a **wide tree**: arity m = poly(λ) and depth d = O(1) cover m^d steps.

> **Implication for a 2-to-1 batcher:** arity 2 forces depth log₂ N. That is ω(1), so the textbook theorems do not cover it. A provable statement must either (a) be the one-step accumulation/folding property, or (b) use a CGSY24-style straightline analysis in an idealized model (§4.3.3).

#### 4.1.2 Accumulation schemes (atomic, BCMS20) [verified]

Let Φ^ρ(pp_Φ, i_Φ, q) be a predicate (ρ is the RO) with parameter sampler H. AS = (G, I, P, V, D), all with access to ρ:

- G(1^λ) → pp. I(pp, pp_Φ, i_Φ) → (apk, avk, dk) (deterministic).
- P(apk, [q_i]_{i=1}^n, [acc_j]_{j=1}^m) → (acc, π_V).
- V(avk, [q_i], [acc_j], acc, π_V) → {0,1}. D(dk, acc) → {0,1}.

**Completeness** (for all unbounded A, with probability = 1):
  (∀j D(dk,acc_j)=1 ∧ ∀i Φ(pp_Φ,i_Φ,q_i)=1) ⇒ (V(avk,[q_i],[acc_j],acc,π_V)=1 ∧ D(dk,acc)=1).
  For n = m = 0 the hypothesis holds vacuously. This is what forces an honest "empty accumulator" to exist.

**Soundness** (for poly-size A, with probability ≥ 1 − negl):
  (V(avk,[q_i],[acc_j],acc,π_V)=1 ∧ D(dk,acc)=1) ⇒ (∀j D(dk,acc_j)=1 ∧ ∀i Φ(pp_Φ,i_Φ,q_i)=1).

Specialising to an argument (Def 4.1) gives Φ_V((pp,i),(x,π)) := V(ivk,x,π). Note that *atomic* accumulation demands soundness, not knowledge, and short accumulators. PCD then needs the underlying ARG to be a **SNARK** (BCMS20 Thm 5.2). The accumulation verifier must be sublinear: v*(λ,m,N,ℓ) = O(N^{1−ε}·α(λ,m,ℓ)).

#### 4.1.3 Split accumulation (BCLMS21) — the definition modern schemes use [verified]

Accumulators split as acc = (acc.x, acc.w), and predicate inputs as q = (qx, qw). **V sees only instance parts**: V(avk, [qx_i], [acc_j.x], acc.x, pf). P and D see everything.

**Knowledge soundness.** There is an extractor E running in **expected** polynomial time such that, for every expected-poly-time P̃ and every auxiliary-input distribution 𝒟, with probability negligibly close to 1:
  V^ρ(avk,[qx_i],[acc_j.x],acc.x,pf)=1 ∧ D(dk,acc)=1
    ⇒ ∀i Φ(pp_Φ,i_Φ,qx_i,qw_i)=1 ∧ ∀j D(dk,(acc_j.x,acc_j.w))=1,
where ([qw_i],[acc_j.w]) ← E^{P̃,ρ}(pp,pp_Φ,ai,r) and (i_Φ,[qx_i],[acc_j.x],acc,pf; r) ← P̃^ρ(pp,pp_Φ,ai).

Points that matter for a spec:
- E gets P̃'s randomness r and oracle access to P̃. Rewinding is allowed, so the extractor need not be straightline.
- For PCD the guarantee must be **multi-instance witness-extended emulation with auxiliary input and output**. Extraction goes one layer at a time and a layer has many nodes. For IVC, single-instance extraction suffices (Rmk 2.3).
- Accumulation is proven in the ROM. PCD is built in the **standard model** and makes non-black-box use of V. The standard-model security of the accumulation scheme is therefore *an assumption* "conjectured based on a security proof in the ROM" (BCLMS21, verbatim gist).
- **Special case (§4.1): D ≡ Φ.** Accumulators and predicate inputs then have the same form, and the scheme *is* a folding scheme.
- BCLMS21 also states that the Halo Infinite theorem claiming PCD from PC accumulation (BDFG20, ePrint version) "is not known" to hold without extra heuristics. **Treat that claim as superseded.**

#### 4.1.4 Folding and reductions of knowledge

**Folding (Nova, KST22 Def 6) [verified].** For R over (pp, s, u, w): G(1^λ) → pp, K(pp, s) → (pk, vk), and an interactive ⟨P(pk, w_1, w_2), V(vk)⟩(u_1, u_2) → (u, w).
- *Completeness:* (pp,s,u_i,w_i) ∈ R for i = 1,2 ⇒ (pp,s,u,w) ∈ R.
- *Knowledge soundness:* for every expected-poly-time P* there is an expected-poly-time E with Pr[(u_1,w_1),(u_2,w_2) ∈ R] ≥ Pr[(pp,s,u,w) ∈ R] − negl.
- *Non-trivial:* V's work plus checking one witness is cheaper than checking both.
- Nova proves this for the interactive protocol through the **forking lemma** (rewinding). The non-interactive scheme, and hence IVC, rests on **Assumption 1, "RO instantiation"**.

**Reductions of knowledge (Kothapalli–Parno, CRYPTO 2023) [unverified details].** These generalise folding to R_1 → R_2 with sequential and parallel composition theorems. **Interactive Oracle Reductions (IORs; BMNW25b/Arc) [verified]** adapt them to oracle messages and implicit (oracle) instances. An IOR from R to R' with proximity radius δ* is the information-theoretic core. Compiling it with Merkle trees and FS gives a split accumulation scheme.

**RBR knowledge soundness for IORs (WARP Def 2.6/2.7, informal; verified).** There must be a knowledge state function KState_δ(x, y, tr, w) and a deterministic extractor E_rbr such that:
- *empty:* KState(x,y,∅,w) = 1 ⟺ ∃y* ∈ B_δ(y) with (x,y*,w) ∈ R;
- *prover moves:* KState(x,y,tr,w) = 0 ⇒ KState(x,y,tr‖π,w) = 0 for every π;
- *verifier moves:* Pr_ρ[∃w: KState(x,y,tr,E_rbr(x,y,tr‖ρ,w)) = 0 ∧ KState(x,y,tr‖ρ,w) = 1] ≤ ε_rbr;
- *full transcript:* KState(x,y,tr,w) = 1 ⟺ V outputs (x',y') with some y'* ∈ B_δ(y') and (x',y'*,w) ∈ R'.

This is a *per-round, backwards* extractor: it takes a witness for round i+1 and returns one for round i. It strictly relaxes the CMS19 "global extractor" notion, and that is what allows codes without efficient decoders. Theorem 2.8: **RBR knowledge soundness ⇒ straightline state-restoration knowledge soundness, ε_sr(t) ≤ (t+k)·ε_rbr.** For a Lean development this is the recommended target notion. It is local, has no rewinding, carries no expected-time arguments, and composes.

#### 4.1.5 How the notions differ

| notion | input → output | incremental? | output checked by | knowledge flavour |
|---|---|---|---|---|
| **Batching** (batch verification; BARGs) | n statements → one check or one proof for the conjunction | no; one shot over a fixed set | the verifier, once | soundness for ∧ x_i; BARGs give "somewhere" extraction |
| **Aggregation** (SnarkPack, aPlonk, STARKPack/DEEP-commitment batching) | n *finished* proofs of the same system → one short proof | usually not; the aggregate is not itself re-aggregable, or only with depth caveats | aggregate verifier, sublinear in n | soundness of each π_i; often needs a structured CRS or pairing (SnarkPack: log-size from inner-pairing products) |
| **Accumulation** (atomic or split) | (inputs q_i, old accs) → new acc + pf | yes; unbounded, or bounded-depth | V cheap per step, D expensive once at the end | split: extract (qw, acc.w) from a valid new acc |
| **Folding** | (u_1,w_1),(u_2,w_2) ∈ R → (u,w) ∈ R | yes | the relation R itself (D = R) | extract w_1, w_2 from w |
| **Recursive SNARK / PCD** | (z, z_loc, [z_i, π_i]) → π | yes | succinct V | full transcript extraction |

The key distinction: aggregation and batching compress a *fixed* set of proofs. Accumulation and folding define an **invariant** ("acc is D-valid ⇒ everything absorbed so far was valid") that is preserved step by step. Only the latter yields PCD with a small recursion circuit, because the circuit runs V_acc and never D.

#### 4.1.6 A Lean-shaped batcher specification (suggested)

```
-- R : indexed relation (index i = R1CS / CCS / PESAT structure), possibly with proximity radius δ
structure Batcher (R_in R_acc : Rel) where
  prove  : Idx → (Inst R_in × Wit R_in) → (Inst R_acc × Wit R_acc) → (Inst R_acc × Wit R_acc) × Proof
  verify : Idx → Inst R_in → Inst R_acc → Inst R_acc → Proof → Bool      -- instance parts only
  decide : Idx → Inst R_acc × Wit R_acc → Bool                           -- default: R_acc membership
-- Completeness: (x,w) ∈ R_in ∧ decide acc → verify ... ∧ decide acc'
-- Interactive core: an IOR  R_in × R_acc → R_acc  (or R_acc × R_acc → R_acc for 2-to-1)
-- Security target: RBR knowledge soundness of the IOR, with an explicit ε_rbr(λ, |F|, t, ℓ)
-- Optional (bounded depth): decider family D_0 ⊆ D_1 ⊆ … ⊆ D_d with
--   D_{s-1}(acc') ∧ verify ⇒ extract with D_s(acc), plus d as an explicit parameter
-- Efficiency side-conditions: |verify circuit| sublinear (or polylog) in |Idx|; |acc.x| independent of #steps
```

Put the *non-interactive / recursive* claim in a clearly named axiom, for example `RO_instantiation_extractable`, rather than in a theorem.

---

### 4.2 Accumulation without homomorphism (hash- and lattice-based)

| scheme | model / assumption | depth | prover | verifier (per step) | status |
|---|---|---|---|---|---|
| **BMNW24** "Accumulation without Homomorphism" (ITCS 2025, ePrint 2024/474) | ROM; any VC with local openings (Merkle) + any linear code | **bounded d = O(1)**, with a concrete attack beyond d | linear in encoding (any linear-time code) | O(d·λ) Merkle openings: t = λ/−log(1−d·δ_ud) per input | **superseded** by Arc/WARP for unbounded depth; still useful as a hybrid layer |
| **Arc** (CRYPTO 2025, ePrint 2024/1731) | ROM only; Reed–Solomon | **unbounded** (distance-preserving) | quasilinear (RS encoding, quotients) | t = 2λ/log(1/ρ) Merkle openings per input; λ/log(1/ρ) under list-decoding conjectures; accumulates up to the list-decoding radius 1−√ρ | verified |
| **WARP** "Linear-Time Accumulation Schemes" (TCC 2025, ePrint 2025/753) | ROM; any linear code over a large field (mutual correlated agreement); straightline extractor via **erasure correction** | unbounded | **O(ℓ·\|p̂\| + λ log k)** field ops, O(k) RO queries, one oracle of length O(n) | O(ℓ(log N + log M + λ) + λ log k) field ops; O(ℓλ log k) RO queries; (1+ℓ₂)·t openings | verified; knowledge error ≤ 2^−λ needs \|F\| ≈ 2^λ·poly; small fields work via extension challenges, which loses strict linearity |
| **FACS** (with FICS IOPP), Baweja–Mishra–Mopuri–Shtepel (ePrint 2025/737; page says CRYPTO 2026) | ROM implied; linear-time codes (systematic LDPC, tensor); new IOR knowledge notion for non-interactive security | unbounded (per WARP's comparison) | linear | O(λ) oracle queries per step; unique-decoding regime only; ≥ 3 oracles | verified abstract; WARP says FACS lacks a straightline extractor for codes without efficient decoders |
| **LatticeFold** (Boneh–Chen, ePrint 2024/257) | Module-SIS; Ajtai commitments | unbounded via per-step norm/range proofs | superlinear (range proofs, bit decomposition) | — | venue unverified (I believe ASIACRYPT 2025) |
| **LatticeFold+** (Boneh–Chen, CRYPTO 2025, ePrint 2025/247) | Module-SIS | unbounded | 5–10× faster than LatticeFold; algebraic range proof, double commitments | shorter proofs, simpler circuit | verified abstract; Cyclo (ePrint 2026/359) claims improvements, unverified |
| Group-based folding: **Nova** (2021/370), **HyperNova** (2023/573, CCS), **ProtoStar** (2023/620), **ProtoGalaxy** (2023/1106), **Multi-folding PCD** (Zhou et al., 2023/1282), **Mangrove** (Nguyen–Datta–Chen–Tyagi–Boneh, CRYPTO 2024, 2024/416) | DLog + ROM (heuristically instantiated); Pedersen/KZG | unbounded accumulation; IVC proven for constant n only | MSM-dominated, ω(n) group ops | ~10⁴ gates (Nova) | not post-quantum; Mangrove's authors are *not* Setty (correcting the prompt) |

Notes:
- **Blaze** (Brehm–Chen–Fisch–Resch–Rothblum–Zeilberger, EUROCRYPT 2025, ePrint 2024/1609) is a **PCS**, not an accumulation scheme. It is a code-switching IOPP with RAA codes over binary fields: 8n XORs + one Merkle tree to commit, O_λ(log² n) verifier. It matters to recursion only as the "final SNARK" for the decider, or as a code/IOPP building block (WARP cites RAA codes from BCFRRZ25).
- **The bounded-depth mechanism (BMNW24 §2.1–2.2, verified).** The spot-check linearity test only gives "acc' is δ-close to α·acc_1 + β·acc_2". Each recursive extraction therefore loses δ, and after k steps the extracted accumulators are only kδ-close to the code. The fix is a decider family {D_s}_{s≤d} with D_0 = D (exact codewords) and D_s accepting sδ-close words: D_{s−1}(acc') ∧ V(…) ⇒ extract acc with D_s(acc). When dδ exceeds the unique-decoding radius, a prover can move a bad codeword to a good one across steps. This is an actual attack, not a proof artefact. Polynomial-length IVC is still possible with arity m and depth d trees, giving m^d steps.
- **Hash-based PCD baselines** for comparison: Fractal/COS20 costs λ log n·|C_MT| of recursion overhead per step, about 10⁶ gates. STIR reduces that to (log n + λ log log n)·|C_MT|.
- Szepieniec's "DEEP Commitments and Their Applications" (ePrint 2024/1752) defers and batches FRI low-degree tests across proofs to get STARK aggregation. It is a preprint and its claims are unverified. It is the closest "aggregation of hash-based proofs" reference I found.

---

### 4.3 Recursive extraction subtleties

#### 4.3.1 Standard-model blow-up (BCCT13, COS20, BCMS20, BCLMS21)
Each layer invokes a *non-black-box* extractor for the instantiated SNARK or accumulation scheme. If |E| = |P̃|^c, depth d costs |P̃|^{c^d}, so only d = O(1) is polynomial. Nothing better is known for SNARKs whose extractors are merely *assumed*, for example via KEA-style assumptions or Assumption 1 in Nova. Expected-time, rewinding extractors (forking lemma in Nova; BCLMS21's expected-poly E) make it worse. The next layer must extract from an *expected-time* adversary, and PCD needs multi-instance extraction per layer.

#### 4.3.2 Why the ROM does not rescue recursion
- ROM SNARKs (Micali, BCS16) have **straightline** extractors that read the prover's query trace (Valiant 2008; BCS16; Chiesa–Yogev 2024 book). Composing straightline extractors costs only additive time.
- Recursion needs a SNARK for "V^ρ accepts". V queries ρ, so the SNARK must prove **oracle computations**, i.e. it must be *relativized*. **BCG24 (TCC 2025, ePrint 2024/728): relativized succinct arguments in the ROM do not exist**, even interactive ones and even with computational soundness. Black-box ROM IVC/PCD via relativized SNARGs is therefore ruled out **[verified]**. Chiesa–Liu 2020 had earlier ruled out relativized PCPs/IOPs.
- Practice therefore replaces ρ with a concrete hash h (Poseidon, Rescue, …) *inside the circuit*. That is the heuristic step. After it, the explicit extractor is gone, and the analysis falls back to §4.3.1 with an assumed extractor for the h-instantiated scheme (COS20 §; BCMS20 §3.3; BMNW24 fn 2) **[verified]**.

#### 4.3.3 Provable recursion in other oracle models
- **SROM** (signed RO; Chiesa–Tromer 2010), **LDROM** (low-degree RO; Chen–Chiesa–Spooner, EUROCRYPT 2022, ePrint 2022/383) and **AROM** (arithmetized RO; Chen–Chiesa–Gur–O'Connor–Spooner, EUROCRYPT 2023, ePrint 2023/587) all admit *relativized* SNARKs. The AROM paper gives PCD for **arbitrary-depth** compliance predicates from a standard-model CRH plus a plausible software instantiation of the ARO, using an accumulation scheme for AROM queries **[verified abstract]**. These models are costly to instantiate and not used in practice.
- **CGSY24** (Chiesa–Guan–Samocha–Yogev, TCC 2024, ePrint 2023/1646) **[verified]**. If a relativized ARG has a *straightline* extractor with error κ_ARG(λ,q,s) and time t_ARG, then canonical PCD has κ_PCD(λ,q,s,N) ≤ κ_ARG(λ,q,s + O(N·t_ARG)) and t_PCD ≤ O(N·t_ARG), with **no depth dependence** (N = number of nodes). For hash-based PCD they propose a non-succinct idealization: RO query-answer pairs of the proved computation go into the argument string and are checked by the verifier directly. This is offered as heuristic evidence for the practice of setting parameters as if recursion were free. **This is the best-justified "concrete security" story for a STARK-style batcher tree**, and it is explicitly heuristic.

#### 4.3.4 Fiat–Shamir soundness notions (what to prove)
- *State-restoration soundness* (BCS16) is the tight notion for BCS/FS in the ROM. *RBR soundness* (Canetti–Chen–Holmgren–Lombardi–Rothblum–Rothblum–Wichs, STOC 2019) implies it, and *RBR knowledge soundness* (CMS19) implies straightline SR knowledge soundness.
- **Block et al., "Fiat–Shamir Security of FRI and Related SNARKs"** (ASIACRYPT 2023, ePrint 2023/1071) **[verified abstract]** proves RBR (knowledge) soundness of FRI and batched FRI. For δ-correlated protocols (Plonky2, Redshift; ethSTARK and RISC Zero only sketched) it shows that RBR knowledge soundness against low-degree-only adversaries lifts to full RBR knowledge soundness.
- **WARP's relaxed RBR extraction** (§4.1.4) is the most composable current definition and is tailored to accumulation.

#### 4.3.5 Concrete attacks relevant to recursion
- **KRS25**, Khovratovich–Rothblum–Soukhanov, "How to Prove False Statements: Practical Attacks on Fiat–Shamir" (CRYPTO 2025, ePrint 2025/118) **[verified abstract]**. For *every* FS hash, there is an explicit circuit for which GKR-based FS (bounded-depth NP computation) is not adaptively sound. The circuit evaluates the hash on its own transcript-predicting input. Non-adaptive variants need very deep circuits or extra assumptions. Recursion structurally meets the precondition, because the proved circuit contains the FS hash. Polyhedra Expander shipped a patch.
- **Arnon–Yogev, "Towards a White-Box Secure Fiat–Shamir Transformation"** (CRYPTO 2025, ePrint 2025/329) **[verified abstract]** proposes XFS, which adds a proof-of-work-style step to FS. XFS is proven secure in a *relativized* ROM where the known diagonalization attacks have analogues. This is evidence, not a standard-model proof. Secondary sources say it requires the checked program to be less complex than the hash, which would conflict with recursion (unverified).
- **Fenzi, "How to prove more false statements: Fiat–Shamir limitations on (generated) R1CS"** (ePrint 2026/1838, Aug 2026 preprint) **[verified abstract]**. When R1CS instances are *generated by running an adversarial program* and the conversion is expressive enough, the program author can break FS soundness of any protocol where an accepting transcript can be prepared before the statement is bound. Variants of **Spartan and Aurora** fall in this class. **Proven mitigation:** derive the first FS challenge from the *generated statement*. Soundness then reduces to the underlying protocol for the non-generated relation. This applies directly to "arbitrary R1CS from RISC-V programs".
- **Implementation pitfall:** Nguyen–Boneh–Setty, "Revisiting the Nova Proof System on a Cycle of Curves" (AFT 2023, ePrint 2023/969) **[unverified details]** found a soundness break in the cycle-of-curves Nova implementation. The lesson is that the recursion wiring (which instance is hashed where) must be inside the spec.

#### 4.3.6 Standard-model alternatives
IVC for *deterministic* computation from falsifiable assumptions (LWE) via rate-1 BARGs exists: Paneth–Pass, FOCS 2022; Devadas–Goyal–Kalai–Vaikuntanathan, FOCS 2022 **[unverified bibliographic details]**. It does not cover NP steps such as RISC-V with nondeterministic advice and is not practical. It is mentioned only for completeness.

#### 4.3.7 What is provably achievable today
1. *Accumulation/folding step:* RBR knowledge soundness of the IOR (information-theoretic, concrete ε), and straightline knowledge soundness of the compiled non-interactive accumulation scheme in the ROM, unbounded depth for Arc/WARP/FACS. **Fully provable; the right Lean target.**
2. *PCD/IVC from (1):* standard-model theorem for **constant depth** under the assumption that the h-instantiated accumulation scheme is (multi-instance, auxiliary-input) knowledge sound (BCLMS21/BCMS20/BMNW24 theorems).
3. *Depth-free concrete security:* only in idealized relativized or straightline models (CGSY24). For ROM/hash-based systems this is heuristic by BCG24.
4. *Provable black-box PCD:* only in SROM, LDROM or AROM, which are impractical.

---

### 4.4 Recommendations for the recursion.fast batcher spec
- Require a *split accumulation or folding* interface with explicit (x, w) splitting. The accumulation verifier sees only x.
- The security theorem in Lean is **RBR knowledge soundness of the IOR R × R → R**, or (R_in, R_acc) → R_acc, with a closed-form ε_rbr in (λ, |F|, code distance, t). Optionally prove the generic implication RBR-KS ⇒ SR-KS once in a shared library.
- If a submission is bounded-depth, it must declare d and the decider chain, and the harness must enforce tree depth ≤ d.
- The FS transcript must absorb, first, a binding digest of the *generated* R1CS (matrices or their commitment) plus public IO (Fenzi 2026). Ban challenge derivation from program text alone.
- Name the heuristic "RO ↦ hash inside circuit preserves straightline extraction" as an axiom and report the CGSY24-style bound κ_ARG(λ, q, s + O(N·t_E)) as the advertised security level.

---

## 5. Recursion costs in practice

### 5.1 Summary table

| System | Base proof system | Recursion mechanism | Step cost (best public data) | Security of recursion layers | Source |
|---|---|---|---|---|---|
| **leanVM** (main) | WHIR + SuperSpartan, binary field | Verifier as a leanISA program | **2→1: 562,737 cycles, 0.27 s (M4 CPU), 190 KiB, 3.5 ms verify** | 128-bit, no PGC | [P] README |
| leanVM (koalabear) | WHIR, KoalaBear⁵, Poseidon | Same | 0.22–0.26 s per proof, 179–268 KiB | ≈124-bit JB | [P] |
| **Plonky2** | PLONK + FRI, Goldilocks, Poseidon | Recursive circuit | **Threshold 2^12 gates; about 300 ms (2021 MacBook Air, whitepaper) or about 170 ms (README/docs, MacBook Pro)**; about 75% of the circuit is Merkle verification; 43 KB proofs at ρ=1/256 in 11.6 s | 100 bits **conjectured** (ethSTARK); Poseidon config possibly about 95 bits (BBLP22) | [P] whitepaper, Sep 2022 |
| **SP1 Hypercube** (v6) | Jagged PCS over BaseFold/FRI, KoalaBear⁴, Poseidon2 | Recursion circuits: normalize, compress (arity 4, `DEFAULT_ARITY`), shrink, Groth16/PLONK wrap | No public per-step timing [?]. 16 RTX 5090s give 99.7% of L1 blocks under 12 s (Nov 2025) [P blog] | **100-bit UDR (proven)**: 124 queries at ρ=1/4 with 16-bit PoW (core and compress); shrink/wrap use 94 queries at ρ=1/8 with 22-bit PoW. soundcalc: core 918 KiB, compress 735 KiB, shrink 529 KiB expected | [P] `fri_params.rs`; soundcalc 2026-09 |
| SP1 Turbo/v4 (**superseded**) | uni-STARK FRI, BabyBear | lift, compress, shrink, wrap | – | Conjectured (pre-Hypercube) | [?] |
| **RISC Zero** (v3) | FRI-STARK, BabyBear⁴ | lift → join (2-to-1) / resolve → identity_p254 → Groth16 | Succinct receipt about 200 kB; no per-step timing published [?] | Docs: 96 bits (rv32im) / 99 bits (recursion), **Toy Problem Conjecture**. soundcalc on 50 queries, ρ=1/4, 0 grinding: **33 bits UDR / 48 bits JBR provable** | [P] dev.risczero.com; soundcalc |
| **OpenVM 2.0** (Jan 2026; production Jul 2026) | SWIRL = stacked WHIR + LogUp-GKR, BabyBear⁴ | app → leaf → internal_for_leaf → internal_recursive → hook → root | Root proof 270 KiB; proofs under 300 kB; 139 MHz RISC-V on 16× RTX 5090; L1 p99 11.8 s. No public per-step timing [?] | "100-bit provable". soundcalc: app/leaf UDR (193/88/81/81 WHIR queries, ρ=1/2, 20-bit PoW); internal/root JBR (68/30/20 queries at ρ=1/8; root 57/28/19 at ρ=1/16) | [P] blog, SWIRL pdf, soundcalc |
| **ZisK** (v0.16.1) | DEEP-ALI + FRI, Goldilocks³ (vadcop) | Per-chip compressors → Recursive2 (2-to-1) → Final → Final_Compressed | Final proof 253–292 KiB | **128-bit JBR** (proven). Main: 230 queries at ρ=1/2. Compressors: 110 queries at ρ=1/4. Recursive2: 73 at ρ=1/8. Final: 43 at ρ=1/32. In UDR the same parameters give only 63–111 bits | [P] soundcalc |
| **Airbender** (ZKsync) | DEEP-FRI, M31⁴, Blake2s delegation | **Verifier compiled to RISC-V and proven by Airbender itself** on a "reduced/recursion" machine (no MUL/DIV; MOP field ops; Blake2s delegation), pairwise 2-to-1, then Boojum compressor and FFLONK | Recursion verifier run with a `--cycles 10,000,000` budget in `recursion.sh`. This suggests a step **under 10M RISC-V cycles** [D, upper bound only]. Batches are about 2^22 cycles | Initial release targets 81 bits (l2beat). soundcalc: 87 queries, ρ=1/2, 28-bit PoW gives **64 bits UDR / 67 bits JBR** | [P] repo; l2beat; soundcalc |
| **Pico** (Brevis) | DEEP-ALI + FRI, KoalaBear⁴ | riscv → convert → combine → compress → embed | Embed proof 281 KiB worst case | soundcalc: riscv 84 queries, ρ=1/2, 16-bit PoW gives **53 bits JBR** | [P] soundcalc |
| **Stwo** (StarkWare) | Circle-FRI, M31/QM31, Blake2s | Cairo verifier in Cairo (stwo-cairo); SHARP aggregation | No public per-step trace size [?]. zkSecurity audited the Cairo verifier (Jul–Aug 2025) | 96 bits + 30-bit PoW, conjectured formula in code | [P] l2beat; stwo code |
| **Jolt** (a16z) | Sumcheck + Twist/Shout; Dory, then Akita | **Jolt verifier as a RISC-V guest proven by Jolt** (field-inline ISA extension, Blake2b, Keccak and NTT inlines) | Akita verifier guest: **67.6–77.3M verification cycles (66.8–79.3M rows), target 2^26 rows**. Draft PRs #1892/#1911, Sep 2026; no outer proof generated yet | Akita lattice assumptions (not hash-based) | [P] GitHub PRs |
| **Plonky3-recursion** | FRI/WHIR, BabyBear/KoalaBear | Native circuit recursion, 2-to-1 aggregation | No published numbers [?] | Configurable | [P] README |

### 5.2 Data points on "verify a proof inside a RISC-V guest"

1. **Jolt: verifier in a Jolt RISC-V guest** (Sep 2026) [P].
   - About **6.8–7.7×10^7 cycles** to verify one Jolt/Akita proof of a Fibonacci program.
   - This uses custom "field-inline" instructions for Fp128 arithmetic: a 64-term dot product costs about 520 rows, about 8 per element. A software reduced add costs about 24 rows, against 4 rows per term with the inline.
   - Sub-word memory ops expand: an `sw` costs about 9 rows. Removing the word-wise `memcpy`/`memset` overrides cost 3.6M rows.
   - **Lesson: without field and hash extensions, a RISC-V verifier is dominated by multiprecision field arithmetic and byte shuffling.**
2. **Airbender: verifier as a RISC-V binary** [P/D].
   - Executed with a 10M-cycle budget.
   - Uses Blake2s delegation and the custom MOP mod-p ops on the "recursion-only" machine. The docs say this "leads to both a smaller circuit and fewer cycles to prove".
3. **leanVM: 2→1 recursion in about 5.6×10^5 VM cycles** [P].
   - Its ISA is field-native, with hash precompiles. Hence it is about 100× cheaper per verification than the Jolt RISC-V figure.
   - This is a non-RISC-V reference for what a near-optimal recursion step costs.
4. **SP1 and RISC Zero** do *not* verify STARKs by running the verifier as a RISC-V guest.
   - In-guest verification (`verify_sp1_proof`, `env::verify`) is *deferred*. The guest records an assumption, and a dedicated recursion circuit (compress/resolve) discharges it.
   - **I could not find a published RISC-V cycle count for running the SP1, RISC Zero or Plonky3 STARK verifier as plain guest code [?].**
   - Expect 10^7–10^8 cycles without hash precompiles: about 3–10k hash invocations, each costing thousands of cycles in software Poseidon2 over a 31-bit field, plus extension-field arithmetic.
   - This is an estimate [D]. Measure it before relying on it.
5. **Plonky2** gives the classic circuit-recursion yardstick: a 2^12-gate PLONK verifier circuit at 100 bits conjectured, about 75% of it Merkle/Poseidon. That is about 3k gates of hashing [P].

### 5.3 What a "2-to-1 step" costs: synthesis for recursion.fast [D]

**Verifier work per child proof.** Take a proven-regime WHIR-JB proof at 2^20–2^24 and 128 bits. The verifier does about **3.6k–5.1k hash compressions** and about 2–2.5 ms native, and the proof is about 250–300 KiB (Table 5). A 2-to-1 step must do twice that, plus R1CS/sumcheck checks that are O(log n) extension-field operations each.

**Cost model.** Recursion cost is roughly (2 × verifier trace) × (prover cost per trace row). The verifier trace is dominated by:
- hash compressions: about 2×(3–10)k;
- extension-field multiplications: about 10^4–10^5 for WHIR, which is O(q·(2^k+m));
- Merkle-path data movement.

**Precompiles matter a lot.** Rules that allow RISC-V precompiles or ISA extensions (hash, field mul) will change rankings by 10–100× (Jolt inlines, Airbender delegation, leanVM's native ISA). recursion.fast should either fix the ISA (pure RV32IM/RV64IM) or price precompile rows explicitly.

**Best known proven-security step (public).** leanVM: about 0.27 s on a laptop CPU, about 5.6×10^5 VM cycles, 190 KiB child proofs, 128-bit, no proximity-gap conjecture.

---

## 6. Formal verification of SNARKs, verifiers and zkVMs

(Helper note, edited; tags [unverified]/[secondary source].)

### 6.0 TL;DR

1. **No one has yet machine-checked an end-to-end SNARK verifier binary against protocol-level knowledge soundness.** Existing results split into three layers that have never been joined:
   - (a) information-theoretic protocol soundness: ArkLib sum-check RBR soundness, Isabelle sum-check, Isabelle/STARK, Lean FRI RBR;
   - (b) circuit/constraint-to-ISA correctness: SP1, OpenVM, Jolt, S-two AIR, Clean;
   - (c) implementation-equals-model "honesty" of a verifier: ZKsync's EasyCrypt/Yul work.

   recursion.fast would require (a) and (c) together, over RISC-V, for arbitrary R1CS. That is new ground.
2. **The closest existing template is ots.golf's RISC-V track.** There the submitter supplies a fixed RV64IM image. A Lean certificate proves that the machine's oracle computation **exactly refines** a Lean verifier on every raw input, including that the program terminates without faults. Security is then proved about the Lean verifier. The machine model is `Verified-zkEVM/riscv-zkvm`, generated from Sail, and checking uses the Lean FRO **comparator** with an axiom whitelist `{propext, Quot.sound, Classical.choice}`.
3. **The gold-standard checker is comparator**, which runs sandboxed builds, `lean4export`, statement matching, an axiom whitelist and kernel replay, with optional external kernels (nanoda). Three 2026 cases show that external kernels and the official kernel can **share** bugs: nanoda accepted forged proofs in two of the Lean 4.34.0 kernel bugs and in the Brossard nested-inductive bug. Treat kernel diversity as defence-in-depth, not proof.
4. **The dominant real-world failures are specification failures, not proof-checker failures.** Examples:
   - SP1's announced 62-opcode verification had a vacuous theorem, wrong load widths, `sorry`s and a JALR spec mismatch.
   - An EasyCrypt LPZK proof was wrong.
   - Lean benchmarks contain 398 mechanically certified defects.
   - Agents in a 100-agent swarm used `local notation` to rewrite theorem statements.

   Budget human audit effort for the trusted statement: the R1CS relation, the RBR-KS definition, the error bound, the RISC-V semantics, and the binding of bytes to the Lean term.

---

### 6.1 Formal verification of SNARKs and verifiers

#### 6.1.1 Summary table

| Project | Assistant | What is proven | Protocol soundness or circuit-level? | Status (as of Oct 2026) |
|---|---|---|---|---|
| **ArkLib** (Verified-zkEVM) | Lean 4 | IOR/OracleReduction framework, with definitions of completeness, (knowledge) soundness, RBR soundness and RBR knowledge soundness (`rbrKnowledgeSoundness` in `OracleReduction/Security/RoundByRound.lean`), plus composition and lifting. Sum-check: `Sumcheck.Interaction.Native.roundByRound_soundness` bounds acceptance on a false claim by `count·deg/|F|`, with no `sorry` in `Sumcheck/Interaction/*`. | **Protocol (IOP) level** | Active. At commit `db7005f` (2026-10-08) a grep finds about 228 `sorry` occurrences in 75 files. Many sit in Binius (about 32), Fiat–Shamir duplex sponge (about 18), Commitments (about 21), Spartan (8), FRI (4), STIR (3) and BCS (2). The older `Sumcheck/Spec/SingleRound.lean` still has `sorry`s. The README status list is stale (dated 7 Aug 2025). R1CS is defined in `ProofSystem/ConstraintSystem/R1CS.lean`. |
| **VCVio** | Lean 4 | Oracle computations as free monads (`OracleComp`), `evalDist`, `simulateQ`, a relational program logic (Loom-based) and state-separating proofs. The 2024 paper covers the forking lemma and Fiat–Shamir. The 2026 paper covers Bellare–Neven forking without rewindability axioms and EUF-CMA for Schnorr. | Crypto-game level (supports protocol proofs) | Mature; ArkLib's main dependency. |
| **CompPoly** | Lean 4 | Computable uni-, bi- and multivariate polynomials, with `RingEquiv`s to Mathlib `Polynomial`/`MvPolynomial`. A Guruswami–Sudan implementation was reportedly integrated **[secondary source]**. | Executable spec support | Active (CompPoly P2 grant, Q2 2026). |
| **Isabelle sum-check** (Garvía Bosshard, Bootle, Sprenger) | Isabelle/HOL | Soundness and completeness of a generalised sum-check over an axiomatised structure, instantiated to multivariate polynomials. AFP entry `Sumcheck_Protocol`. | **Protocol level** (plain soundness, not RBR KS) | Done (CSF 2024). |
| **Isabelle/STARK** (Marmsoler) | Isabelle/HOL | Query-bounded soundness of a STARK-style protocol with Fiat–Shamir transcript producers, Merkle trees and FRI correlated agreement, plus honest completeness. Gives 2^-137 for specific parameters and a 2^20 oracle-call bound. | **Protocol level, non-interactive, ROM** | arXiv Aug 2026. Excludes knowledge extraction, ZK and deployed-hash correctness. |
| **simple-rbr-fri** (Hirai / zkSecurity) | Lean 4 | RBR soundness and perfect completeness of FRI, following Garreta–Mohnblatt–Wagner (ePrint 2025/1993). Largely AI-generated (Harmonic Aristotle plus Claude Code). | **Protocol level** | Jan 2026. One WHIR mutual-correlated-agreement result is cited as an axiom-like dependency and not formalised; it adds a `deg>0` assumption. |
| **Formal SNARKs project** (Bailey, Miller) | Lean 3, then Lean 4 | Soundness of linear-PCP SNARKs in the AGM/GGM style, including Groth16, with a decision procedure. | **Protocol level** (idealised model) | USENIX Security 2024. |
| **Zero-Knowledge in EasyCrypt** (Firsov, Unruh) | EasyCrypt | Soundness, proof of knowledge (with rewinding), ZK and sequential composition for Σ-protocols (Fiat–Shamir QR, Schnorr, Blum). | Protocol level (Σ-protocols, not SNARKs) | CSF 2023. |
| **SSProve** | Coq/Rocq | Foundational framework for state-separating proofs. | Framework | CSF 2021 / TOPLAS 2023. |
| **ZKsync verifier** (Nethermind + Matter Labs) | EasyCrypt (extended for Yul) | The on-chain Yul PLONK verifier is **"honest"**: it equals an abstract honest-verifier model. **Soundness, KS and completeness are not proven** and are listed as future work. | **Implementation ≡ model only** | Sep 2025. |
| **LPZK post-mortem** (Oechsner, Pereira, Scholl) | EasyCrypt | Shows that a published EasyCrypt soundness/ZK proof of LPZK was **wrong** (bad modelling), with exploitable consequences. | Cautionary | CiC 2025. |
| **SP1 Hypercube RV64 core** (Succinct + Nethermind) | Lean 4 + Clean + Sail | Claimed: 62 opcodes, with constraints implying Sail semantics. **EF audit (Gunton, 2026-05-20):** only 51 are complete and correct. SLTI was vacuous (contradictory hypotheses). LH/LHU/LW/LWU used width-1 specs. All loads depend on `sorry`. LUI/AUIPC/LD have no theorem. JALR omitted `& ~1`, a completeness bug. Results are single-step soundness only; there are axioms for HTIF, mprotect and PMP; the bus and memory are unverified. | **Circuit ↔ ISA, single step** | Partially fixed. |
| **OpenVM RV32IM** (Axiom + Nethermind) | Lean 4 + Sail | Claims all 45 RV32IM opcodes, with execution and memory consistency constrained per Sail and no circuit bugs found. Report: `openvm/audits/v1.5.0-nethermind-rv32im-fv-report.pdf`. | Circuit ↔ ISA | Feb 2026. Direction and assumptions are not in the blog **[read the report]**. |
| **Brevis Pico** (Nethermind) | Lean 4 + Sail | RISC-V constraints against Sail (EF grant, Q1 2026). | Circuit ↔ ISA | **[status unverified]** |
| **CertiPlonk** (Nethermind) | Lean 4 + cvc5 FF | Extracts Plonky3 AIRs into Lean; a finite-field Gröbner tactic with Lean reconstruction. Applied to SP1, OpenVM, Pico and Poseidon2. | Circuit level | Active. |
| **Clean** (zkSecurity) | Lean 4 | `FormalCircuit` = soundness (constraints ⇒ spec) + completeness (spec ⇒ satisfiable). The 2026 `Channel` work lifts local to global **soundness** for multi-table AIRs; completeness lifting is "future work". Targets AIR, PLONK and R1CS. | Circuit level | Active; basis of zk.golf. |
| **zkLean** (Galois) | Lean 4 (`Std.Do` Hoare triples) | DSL for R1CS, lookups, MLE lookups and RAM; a Jolt frontend extractor; SHA-3 circuit proven correct. Goal: Jolt frontend ≡ Sail. | Circuit level | Active. |
| **Jolt** | ACL2, then Lean 4 | ACL2: lookup semantics for RV32I (Kwan, Dao, Thaler 2024). Jolt-QED (Lean): 51 of 58 bytecode expansions proven equivalent to RISC-V, using a Lean translation of Sail. | ISA-level emulation | ePrint 2026/2157. |
| **S-two AIR** (StarkWare: Avigad et al.) | Lean 4 | AIR satisfiable (with logup and component-assembly hypotheses) ⇒ a Cairo execution exists. Found missing range checks and weak logup bounds. Earlier Stone/Cairo AIR work dates from CPP 2022. | Arithmetisation level (**not** the FRI/STARK verifier) | arXiv Jun 2026. |
| **RISC Zero + Veridise Picus** | SMT (Picus) | Determinism (no under-constraint) for the Keccak accelerator and "large parts" of the RISC-V circuit. | Circuit determinism only | RISC-V circuit **[completion unverified]** |
| **riscv-zkvm** (Verified-zkEVM) | Lean 4 | `RiscvZkvm.Sail` is **generated** from `riscv/sail-riscv` via Sail's Lean backend (`lean-sail`). `RiscvZkvm.Rv64` is a computable RV64IM model with 51 `*_sail_equiv` theorems plus step/run simulation, a separation-logic/WP program logic and an ELF interpreter. The trusted axiom set is 3 classical + 4 Sail platform axioms. | ISA semantics infrastructure | v0.3.1 (Lean 4.33.0). Used by ots.golf and evm-asm. Does **not** run the standard `riscv-tests` images (different memory map). |
| **evm-asm** (zkSecurity/Verified-zkEVM) | Lean 4 | A verified macro assembler: EVM opcodes written directly in RV64IM and proved in Lean. | Program level | Early experiment. The README says it is "not for anything of value". |
| **LNSym** (leanprover / AWS) | Lean 4 | Symbolic simulator for Armv8 machine code (AArch64 ISA formalisation). | Program level, Arm | The link to AWS-LC proofs is **[unverified]**. |
| **Rust→Lean pipeline** (Klaus, Conejero, Tolmach) | Lean 4 + Aeneas/Hax | Plonky3 FRI folding, field arithmetic, Horner and RISC Zero Merkle inclusion against ArkLib/CompPoly specs, with AI provers (Aristotle, Aleph). | Implementation ≡ spec (pieces) | AIMACS@CAV 2026. |

#### 6.1.2 Key observations

- **RBR knowledge soundness exists as a Lean definition today** (ArkLib `rbrKnowledgeSoundness`, with `…OneShot`, `…WorstCase` and `…With` variants). recursion.fast can import and pin it rather than re-define it. Caveats:
  1. ArkLib is in flux: there is a new `Interaction/*` framework next to the legacy `OracleReduction/*`, and the toolchain moves quickly.
  2. The **Fiat–Shamir / BCS layers that turn RBR-KS into non-interactive soundness still contain `sorry`s.** A RISC-V verifier is non-interactive, so the competition must either (i) state its target as RBR-KS of the *interactive* oracle verifier that the binary refines, with the FS/BCS step trusted on paper, or (ii) wait for, or fund, a sorry-free FS theorem. ots.golf avoids this by stating security directly in the ROM using VCVio.
- **The Sail→Lean path is real and production-used.** Verified-zkEVM `riscv-zkvm` is regenerated from pinned sail-riscv, with provenance in `sail-import/PROVENANCE.toml`. ots.golf pins it at `4634e41`. Generation is heavy (Sail 0.20.2, OCaml ≥ 5.2, about 7 GB of memory, 9–13 minutes), but consumers need only prebuilt oleans. The `RvfiDii` module alone is about 14 GiB to build.
- **The EF Verified-zkEVM programme** (verified-zkevm.org) lists 42 awarded grants across zkVM, EVM, Cryptography and Tooling tracks, and applications are closed. Recursion-relevant entries:
  - Cornell, "The recursive extraction problem" (Q4 2025).
  - Orrù / Chiesa / Nguyen, duplex-sponge Fiat–Shamir specification.
  - Nethermind, STIR/WHIR in ArkLib.
  - Hristova, proximity generators.
  - Logical Intelligence, AI proofs in ArkLib.

  The EF security roadmap (Kadianakis, Dec 2025) targets 128-bit provable security and a **"formal security argument for the recursion architecture's soundness" by end-2026**. That is directly aligned with recursion.fast. The headline "$20M" figure appears on an EF blog post (pq.ethereum.org) that now returns 404 **[amount unverified from a live primary source]**.
- **Circuit-level ≠ protocol-level.** Every zkVM result above proves constraints ⇒ ISA semantics (and sometimes the converse) **assuming** the proof system is a sound argument for "constraints satisfied", and usually also assuming bus/lookup balance. None proves the STARK/FRI verifier sound. Isabelle/STARK is the only machine-checked end-to-end non-interactive STARK-style soundness result, and it is about an abstract verifier, not a binary.

---

## 7. Autoresearch competitions with Lean-checked submissions; adversarial submissions and reward hacking

### 7.1 Autoresearch / AI-driven competitions with machine-checked submissions

#### 7.1.1 Lean-checked "golf" competitions (closest analogues)

| Competition | Operator | Submission and certificate | Checking | Notes relevant to us |
|---|---|---|---|---|
| **ots.golf** | leanEthereum (EF); repos `leanEthereum/ots.golf-dev`, `…-submissions` | Hash-based one-time signatures. Tracks: compressions, **RISC-V cycles**, leanISA cycles, hinted RISC-V, and a lower bound (whole-word DAGs, 90). RISC-V `Submission.Certificate C` covers: admissibility; 127-bit strong security in a shared ROM (VCVio `IsQueryBound` cost); **exact refinement of the Lean verifier by the machine's oracle computation on every raw input, with no trap or fuel exhaustion**; a cycle bound on every path (accepting or rejecting); and `image_size < 1 MiB`. | comparator `c0c5a52d`, lean4export, landrun + systemd; axioms `{propext, Classical.choice, Quot.sound}`; `native_decide` refused; flat `.lean` files; header-only import policy; 20 min / 24 GiB / no network. | `docs/AUDIT.md` is an exemplary trust-boundary write-up. Two subtle findings: (i) without a verification-cost cap, a scheme could make `B/2^127 ≥ 1` vacuous by hashing a 2^137-bit input; (ii) binding public input through a digest made `Sound` unsatisfiable, because the probability quantifies over oracle assignments. They admit that header import checks do **not** constrain runtime module loads by metaprograms, so they rely on comparator. Launched Sept 2026. |
| **sig.golf** | Yukon (Eigen Labs / Layr-Labs), with the EF as collaborator; repo `Layr-Labs/sig.golf-dev` | Stateless hash-based signatures. Score = signature bytes × proved verification-cycle bound. The certificate `SigGolf.Certificate submission C` covers admission, completeness ≥ 1−2^-128, Pr[win] ≤ Q·2^-127 and termination < 2^32 cycles, on RV64IM + HASH ecall. | Lean kernel; axiom whitelist as above. | Adversary modelled as finite truncations with a signing oracle. Faults count as reject. Excludes quantum and multi-user attacks. |
| **Proximity Prize / better.codes** | Yukon × zkSecurity, with the EF; repo `proximity-prize/proximity-prize` | Two tracks for an interleaved RS profile (`koalaIRS12`): certified lower bound on the ABF26 reduction threshold (maximise bits) and an upper/attack track. The lower certificate uses **ArkLib's** certified combination-round error (`winningSetDensity ≤ certifiedGammaError`). | comparator pinned at `777e7f5`, lean4export, landrun; "ranked results require the independent verifier to accept the exact commit". The interval is currently 68.15 to 116.13 bits. | Shows ArkLib already serves as a trusted spec library in a live adversarial competition. The README is explicit that the score "is not a full-protocol security claim". This is separate from the EF's $1M Proximity Prize on the Arnon–Boneh–Fenzi grand challenges. |
| **zk.golf** | zkSecurity | Minimise allocations + constraints of a Clean circuit meeting a formal interface (assumptions + spec). Requires soundness **and completeness**, proof that it is R1CS, and cost proofs; BN254. | comparator; `native_decide` banned; per-challenge `permitted_axioms`; 1200 s limit; trusted challenge repo `zksecurity/zk-golf-challenges`. | The authors note that completeness is what stops the trivial "unsatisfiable circuit is sound" win. |
| **precompile.fast**, **SNARK.fast (Flock)**, **HashSmash**, **Heesch** | Yukon | precompile.fast: cheaper MODEXP/RIPEMD-160, "Comparator must accept the Correct bytecode", same bytes must pass clean and dirty execution. SNARK.fast: Flock prover throughput, with proofs checked by a pinned trusted verifier (no Lean). | Mixed | Yukon's general model: the challenge creator supplies the verifier and baseline; a "deterministic gate" runs before merge; solver sandbox. |

**Not found:** "zk.golf" exists (above). I found **no** Shor "quantum circuit golf" competition. The closest is an agentic Lean formalisation of Shor resource bounds for RSA-2048/P-256 (Zhang et al., arXiv 2607.14082) and the `FormalRV` Lean package. There is no evidence of a Lean competition on yukon.org beyond those listed.

#### 7.1.2 AI-for-math systems and results (context)

- **AlphaEvolve** (Novikov et al., arXiv 2506.13131, 2025): an evolutionary LLM coding agent that searches against automated evaluators. In the math follow-up (Georgiev, Gómez-Serrano, Tao, Wagner, arXiv 2511.02864), 67 problems mostly matched and sometimes improved the state of the art. Its evaluators are programs, not Lean; reward hacking against evaluators is discussed there qualitatively **[details not re-verified]**.
- **AlphaProof** (Hubert et al., *Nature*, 2025, doi 10.1038/s41586-025-09833-y): RL in Lean on millions of auto-formalised problems; IMO 2024 silver together with AlphaGeometry 2.
- **Karpathy `autoresearch`** (github.com/karpathy/autoresearch, Mar 2026, MIT licence): an agent loop that edits `train.py`, runs a 5-minute budget and keeps changes that improve `val_bpb`. It popularised the term "autoresearch". There is no formal checking.
- **Erdős problems:** #728 was reported as the first AI-autonomous resolution (GPT-5.2 Pro + Harmonic Aristotle, Lean proof, Jan 2026; writeup by Sothanaphan, arXiv 2601.07421). #397 was marked "DISPROVED (LEAN)". The early statement on the website was **vague**, and the first formal proof resolved a different reading, which is a misformalisation risk even with Lean.
- **Equational Theories Project** (Bolan, Breitner, Brox, Carlini, Carneiro, … Tao; 34 authors; arXiv 2512.07087): all 22,028,942 implications between 4,694 magma laws, settled with Lean, using a mix of human and ATP/AI work. Lesson: large crowdsourced Lean projects use CI with axiom audits and tolerate untrusted automated contributors.

---

### 7.2 Adversarial submissions and reward hacking in Lean-checked settings

#### 7.2.1 Attack catalogue

| Vector | Mechanism | Caught by |
|---|---|---|
| `sorry`/`admit`, custom `axiom` | `sorryAx` or new axioms in the closure. Anthropic (2026) reports "define the proof as an axiom" as a common Lean reward hack. | `#print axioms`, comparator whitelist |
| `native_decide` / `decide +native` | Introduces `Lean.ofReduceBool` (and, since 4.35, one axiom per native computation). Trusts the compiler and every `@[implemented_by]`/`@[extern]`/`@[csimp]` in scope. | Whitelist (not permitted). External kernels cannot check it. |
| `implemented_by`, `extern`, `@[csimp]` | Change compiled behaviour, not kernel terms. They matter **only** if anything in the trust chain *executes* Lean code (native_decide, `#eval`-based CI checks, or extracting the RISC-V bytes by running Lean). | Kernel-only checking; never use compiled evaluation in the trust path |
| Environment manipulation | Metaprograms adding declarations through unchecked paths, `debug.skipKernelTC`, or `addDecl` exploits. The Lean 4.32.1 kernel bug (Hulin + GPT-5.6 Sol, #14484) needs in-process metaprograms. | Comparator's out-of-process export + replay ("not affected" per the 4.32.1 notes) |
| `.olean` tampering / build-time code execution | Lake and tactics run arbitrary code at build time. `lean4checker` trusts `.olean` well-formedness. | Sandboxed build (landrun), export-based replay; comparator never mmaps candidate oleans |
| Statement rewriting via notation/macros | `local notation "LinearIndependent" => fun _ _ => False`, or redefining `∧`/`↔`/`<` (seen in the DeepMind 100-agent swarm, arXiv 2609.04170). LongCat (Meituan) catalogued 9 cheating patterns that edit the formal context (imports, opens, instances). | Compare **elaborated kernel types** against a trusted Challenge environment (comparator), not text or regex |
| Instance/`Decidable` tricks | A submitter-supplied instance in a statement's elaboration changes meaning. | Statement elaborated only in the trusted Challenge file; comparator checks all declarations used in the statement are identical |
| **Definition holes** | The challenge leaves a `def` open (the verifier program!). Comparator checks name, type and safety only. A "RH ↔ ChallengeSolution" hole is solved by `rfl`. Comparator's README: holes "**must** always be checked with an additional (potentially human) verifier". | The theorems must pin the hole's semantics fully (soundness **and** completeness), plus human review |
| Vacuity | Contradictory hypotheses (SP1 SLTI), unsatisfiable assumptions (Clean `FalseChannel`), a spec parameterised wrongly (SP1 loads), bounds that are vacuous at the parameters (the ots.golf `B/2^127 ≥ 1` case). | Non-vacuity witnesses in the trusted base (ots.golf `Witnesses/`), completeness requirements, audit |
| Kernel bugs | Lean 4.34.0 (Sep 2026) fixed three proof-of-False routes found by Daniel Selsam (OpenAI) with internal models: `is_def_eq` cache (#14806), `is_prop` stuck types (#14807; **nanoda also accepted**) and a refcount overflow (#14838, needs ≥ 18 GB RAM). Brossard (oss-security, 2026-08-02): nested-inductive `.proj` not validated + hash collision ⇒ axiom-free `0 = 1` via checked `addDecl`, fixed in PR #14577, **also accepted by nanoda**; a public "Collatz disproof" exploited it. Earlier: DeepSeek-Prover reportedly exploited an `apply?` bug in Lean 4.9.0 **[second-hand, via arXiv 2608.28639]**. | Latest toolchain, multiple kernels (official + nanoda + lean4lean), memory caps, re-verification of records on toolchain bumps |
| Resource attacks | Huge `Nat` literals, heartbeat blow-ups, output flooding (ots.golf rejects output > 4 MiB). | Limits; Lean 4.34 caps kernel `Nat` literals at 128 MB |
| Benchmark/statement defects | Ammanamanchi, Bhat, Biderman (ICML 2026): 4,833 findings and 398 mechanically certified defects across 5 Lean benchmarks (counterexamples, vacuous theorems, unsound axioms). | Static checkers + semantic audit of the challenge itself |

#### 7.2.2 Tooling

- **comparator** (`leanprover/comparator`, Lean FRO, built for AIMO). Its assumptions are: trusted Challenge + lakefile; no prior compilation of the solution; landrun works (systemd-run guards a landrun bug fixed in Linux 7.1); the kernel or one external kernel is correct; and no privileged user. It guarantees same statement, axioms within the whitelist and kernel acceptance. The Lean reference ("Validating Proofs") calls it the **gold standard** for "proof marketplaces, high-reward proof competitions, unaligned AI".
- **lean4export** for plain-text export, **nanoda** (Rust, independent kernel), **lean4lean** (Carneiro, a Lean kernel in Lean; believed not affected by #14807), and **lean4checker** (environment replay from oleans; CI-grade, not adversarial-grade).
- **SafeVerify** (GasStationManager; Mistral's fork `LeanstralSafeVerify`) is a lean4checker-derived target-vs-submission comparison with axiom checks, used by PutnamBench and others. It is weaker than comparator's sandbox/export pipeline.

---

### 7.3 Recommendations for recursion.fast

1. **Adopt the ots.golf certificate shape.** Pin a Lean `Verifier` spec over ArkLib `OracleReduction` objects. Require (a) RBR-KS + completeness of the spec verifier for **every** R1CS instance (universally quantified; the R1CS relation is ArkLib's `R1CS.relation` or a trusted copy), with the error bound a trusted closed-form function of the parameters ≤ 2^-λ; and (b) **exact refinement**: on every raw input the RISC-V image (on pinned `riscv-zkvm`) terminates without fault within fuel, and its accept bit and oracle queries equal the spec's. Proofs are then about the spec, as in ots.golf.
2. **Fiat–Shamir is the gap.** Either state the target in the ROM directly with VCVio, as ots.golf and sig.golf do, or state RBR-KS of the IOP plus a trusted, pinned FS theorem. Do **not** let submitters supply the FS bridge.
3. **Bind bytes to terms.** The CI must run *exactly* the image whose Lean term was kernel-checked. Either inject the submitted bytes as a literal into the trusted Challenge (prove `image = trustedBytes`), or extract the image from the exported declaration with an independent deserializer. Never `#eval` candidate code in the trust path, because of `implemented_by`/`extern`/`csimp`.
4. **Use comparator with external kernels** (nanoda; consider lean4lean) on the latest patched toolchain. Use the axiom whitelist `{propext, Quot.sound, Classical.choice}` and ban `native_decide`/`bv_decide`-native. Build in landrun/systemd with no network, memory/time/output caps, and flat file layout. Re-verify all records on toolchain bumps (kernel bugs land roughly monthly in 2026).
5. **Treat the verifier as a definition hole, guarded by theorems.** Completeness is mandatory: an always-reject verifier is trivially RBR-sound. Also require a non-vacuity witness in the trusted base (a reference verifier that satisfies the certificate) and check that hypotheses are satisfiable.
6. **Audit the trusted surface, not the proofs:** the RBR-KS definition (which variant; how the state function and extractor are quantified), the error bound, the R1CS encoding (field, sizes, public-input layout), the RISC-V ABI/loader and cost model, and the 4 Sail platform axioms in riscv-zkvm. Publish an `AUDIT.md`-style trust table, following ots.golf.
7. **Expect reward hacking from capable agents.** Comparator handles kernel-level fraud. Spec-level fraud (vacuous parameters, cost-model loopholes such as free lookup tables when code-size caps are missing, a point ots.golf calls `maxProgramLogSize` "load-bearing") needs red-teaming of the challenge before launch. Run a bounty for challenge-statement bugs.

---

## 8. Consolidated implications for the recursion.fast design (inputs to D1/D2)

1. **Model.** Use an indexed relation for R1CS (index = matrices A, B, C; instance = public
   inputs), with a holographic IOP and an indexer.
   - The Lean target is RBR-KS of the interactive oracle verifier that the RISC-V binary refines.
   - The FS/BCS/COS step is a trusted, pinned theorem with the CY bounds (§1.3). It is never
     supplied by submitters.
   - The advertised security level is computed from κ_rbr, k, l and an assumed query budget t.
2. **Transcript binding rule** (KRS25 / Fen26). The harness absorbs H(dom ‖ vik ‖ x) before any
   challenge. Submissions cannot change this prefix.
3. **Proximity regime.** Only the UDR or Johnson regime is allowed. Any proximity-gap lemma not
   proved in the submission must be a trusted hypothesis transcribed verbatim from a proven
   theorem, for example BCIKS20 UDR, BCHKS25 Thm 1.5, or BCGM25 for MCA, and reviewed by humans.
   "Up to capacity" parameters are banned. Codes with proven capacity gaps (folded RS, random
   evaluation sets) are a legitimate design axis.
4. **Cost.**
   - Hashing dominates: ≈5k compressions per WHIR-JB proof at 2^24. With a plain RV64IM cost
     model, field arithmetic also dominates (Jolt in-guest data).
   - Decide the precompile policy up front. Either use pure RV64IM, or price a HASH ecall as
     sig.golf does, plus optional field-mul/clmul ecalls.
   - Report proven-regime numbers only.
5. **Batcher.** Use a split accumulation / folding interface: the verifier sees instance parts
   only, and an explicit decider is part of the final verifier.
   - Lean proves RBR-KS of the reduction and completeness.
   - Bounded-depth schemes must declare d, and the harness enforces it.
   - Recursive soundness is a named heuristic axiom, not a theorem.
6. **Trusted-base hygiene.**
   - Adopt ots.golf's certificate shape (exact refinement on every raw input) and checking stack
     (comparator, lean4export, landrun, external kernel, axiom whitelist, no `native_decide`).
   - Require completeness and a non-vacuity witness.
   - Re-verify all records on toolchain bumps.

## 9. Superseded items and open uncertainties

**Superseded or refuted.**
- The BCIKS20 *capacity* conjecture, the WHIR MCA-up-to-capacity conjecture and the DEEP-FRI
  list-decoding-up-to-capacity conjecture are refuted (§3.2).
- The ethSTARK v1.2 provable query counts use BCIKS20 Johnson bounds, which are superseded by
  BCHKS25.
- The WHIR paper's "Conjecture 4.12 (1)" (MCA up to Johnson) is now a theorem (BCGM25).
- Binius (DP23) PCS is superseded by FRI-Binius / Binius64.
- Jolt's Lasso/Spice memory checking is superseded by Twist and Shout.
- BMNW24 is superseded for unbounded depth by Arc, WARP and FACS.
- LatticeFold is superseded by LatticeFold+.
- The Halo Infinite (BDFG20, ePrint version) PCD theorem is disputed by BCLMS21.
- SP1 pre-Hypercube conjectured parameters are superseded by Hypercube (100-bit UDR).
- The local leanVM checkout (a386121, 2026-09-03) reports 2→1 recursion at 686,085 cycles,
  206.3 KiB, 0.394 s and 14.6 ms verify, with "128-bit (LDR Johnson)". The helper read
  562,737 cycles, 190.2 KiB, 0.272 s and 3.46 ms from the live README on 2026-10-10. Both are
  quoted; the live one is newer.

**Not confirmed from primary sources.**
- The exact radius formula in Crites–Stewart's modified conjecture.
- BCGM25's explicit error constant.
- The ABF26 PDF content (fetch blocked).
- Whether EF teams met the May 2026 "100-bit provable" milestone.
- The EF "$20M" Verified-zkEVM figure.
- Per-step recursion timings for SP1, RISC Zero, OpenVM, ZisK and Stwo.
- Any plain RISC-V-guest STARK-verifier cycle count.
- The AFK22 loss constant "(Q+1)" (stated from memory; the abstract confirms only that the loss is
  linear in Q).
- Various venues marked [unverified] in the BibTeX.
- The Jolt in-guest numbers come from draft PRs.

---

## References (consolidated BibTeX)

Keys are stable. Entries from the helper sections are merged and deduplicated. Where two keys
named the same work, one was kept: BCS16, BCFRRZ25-Blaze, EF25-zkEVMsec, ABF26.

```bibtex
@inproceedings{BCS16,
  author={Eli Ben-Sasson and Alessandro Chiesa and Nicholas Spooner},
  title={Interactive Oracle Proofs},
  booktitle={TCC 2016-B},
  year={2016},
  note={ePrint 2016/116},
  url={https://eprint.iacr.org/2016/116}}
@inproceedings{BBHR18-FRI,
  author={Eli Ben-Sasson and Iddo Bentov and Yinon Horesh and Michael Riabzev},
  title={Fast {Reed--Solomon} Interactive Oracle Proofs of Proximity},
  booktitle={ICALP},
  year={2018},
  note={ECCC TR17-134},
  url={https://eccc.weizmann.ac.il/report/2017/134/}}
@inproceedings{BGKS20-DEEPFRI,
  author={Eli Ben-Sasson and Lior Goldberg and Swastik Kopparty and Shubhangi Saraf},
  title={{DEEP-FRI}: Sampling Outside the Box Improves Soundness},
  booktitle={ITCS},
  year={2020},
  note={ePrint 2019/336},
  url={https://eprint.iacr.org/2019/336}}
@inproceedings{BCIKS20,
  author={Eli Ben-Sasson and Dan Carmon and Yuval Ishai and Swastik Kopparty and Shubhangi Saraf},
  title={Proximity Gaps for {Reed--Solomon} Codes},
  booktitle={FOCS},
  year={2020},
  note={JACM 2023; ePrint 2020/654},
  url={https://eprint.iacr.org/2020/654}}
@misc{ethSTARK21,
  author={{StarkWare Industries}},
  title={{ethSTARK} Documentation, Version 1.2},
  howpublished={Cryptology ePrint Archive, Paper 2021/582},
  year={2023},
  url={https://eprint.iacr.org/2021/582}}
@inproceedings{ACFY24-STIR,
  author={Gal Arnon and Alessandro Chiesa and Giacomo Fenzi and Eylon Yogev},
  title={{STIR}: {Reed--Solomon} Proximity Testing with Fewer Queries},
  booktitle={CRYPTO},
  year={2024},
  note={ePrint 2024/390},
  url={https://eprint.iacr.org/2024/390}}
@inproceedings{ACFY24-WHIR,
  author={Gal Arnon and Alessandro Chiesa and Giacomo Fenzi and Eylon Yogev},
  title={{WHIR}: {Reed--Solomon} Proximity Testing with Super-Fast Verification},
  booktitle={EUROCRYPT},
  year={2025},
  note={ePrint 2024/1586},
  url={https://eprint.iacr.org/2024/1586}}
@inproceedings{ZCF24-BaseFold,
  author={Hadas Zeilberger and Binyi Chen and Ben Fisch},
  title={{BaseFold}: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes},
  booktitle={CRYPTO},
  year={2024},
  note={ePrint 2023/1705},
  url={https://eprint.iacr.org/2023/1705}}
@misc{DP23-Binius,
  author={Benjamin E. Diamond and Jim Posen},
  title={Succinct Arguments over Towers of Binary Fields},
  howpublished={Cryptology ePrint Archive, Paper 2023/1784},
  year={2023},
  url={https://eprint.iacr.org/2023/1784}}
@misc{DP24-FRIBinius,
  author={Benjamin E. Diamond and Jim Posen},
  title={Polylogarithmic Proofs for Multilinears over Binary Towers},
  howpublished={Cryptology ePrint Archive, Paper 2024/504},
  year={2024},
  url={https://eprint.iacr.org/2024/504}}
@misc{NA25-Ligerito,
  author={Andrija Novakovic and Guillermo Angeris},
  title={Ligerito: A Small and Concretely Fast Polynomial Commitment Scheme},
  howpublished={Cryptology ePrint Archive, Paper 2025/1187},
  year={2025},
  url={https://eprint.iacr.org/2025/1187}}
@inproceedings{AHIV17-Ligero,
  author={Scott Ames and Carmit Hazay and Yuval Ishai and Muthuramakrishnan Venkitasubramaniam},
  title={Ligero: Lightweight Sublinear Arguments Without a Trusted Setup},
  booktitle={ACM CCS},
  year={2017}}
@inproceedings{GLSTW23-Brakedown,
  author={Alexander Golovnev and Jonathan Lee and Srinath Setty and Justin Thaler and Riad S. Wahby},
  title={Brakedown: Linear-time and Field-agnostic {SNARKs} for {R1CS}},
  booktitle={CRYPTO},
  year={2023},
  note={ePrint 2021/1043},
  url={https://eprint.iacr.org/2021/1043}}
@inproceedings{XZS22-Orion,
  author={Tiancheng Xie and Yupeng Zhang and Dawn Song},
  title={Orion: Zero Knowledge Proof with Linear Prover Time},
  booktitle={CRYPTO},
  year={2022},
  note={ePrint 2022/1010},
  url={https://eprint.iacr.org/2022/1010}}
@inproceedings{Set20-Spartan,
  author={Srinath Setty},
  title={Spartan: Efficient and General-Purpose {zkSNARKs} without Trusted Setup},
  booktitle={CRYPTO},
  year={2020},
  note={ePrint 2019/550},
  url={https://eprint.iacr.org/2019/550}}
@misc{HLP24-Circle,
  author={Ulrich Hab{\"o}ck and David Levit and Shahar Papini},
  title={Circle {STARKs}},
  howpublished={Cryptology ePrint Archive, Paper 2024/278},
  year={2024},
  url={https://eprint.iacr.org/2024/278}}
@inproceedings{AST24-Jolt,
  author={Arasu Arun and Srinath Setty and Justin Thaler},
  title={Jolt: {SNARKs} for Virtual Machines via Lookups},
  booktitle={EUROCRYPT},
  year={2024},
  note={ePrint 2023/1217},
  url={https://eprint.iacr.org/2023/1217}}
@misc{ST25-TwistShout,
  author={Srinath Setty and Justin Thaler},
  title={Twist and Shout: Faster Memory Checking Arguments via One-Hot Addressing and Increments},
  howpublished={Cryptology ePrint Archive, Paper 2025/105},
  year={2025},
  url={https://eprint.iacr.org/2025/105}}
@misc{Plonky2,
  author={{Polygon Zero Team}},
  title={Plonky2: Fast Recursive Arguments with {PLONK} and {FRI}},
  year={2022},
  note={Draft, 7 Sep 2022},
  url={https://github.com/0xPolygonZero/plonky2/blob/main/plonky2/plonky2.pdf}}
@misc{HJRRR25-Jagged,
  author={Tamir Hemo and Kevin Jue and Eugene Rabinovich and Gyumin Roh and Ron D. Rothblum},
  title={Jagged Polynomial Commitments (or: How to Stack Multilinears)},
  howpublished={Cryptology ePrint Archive, Paper 2025/917},
  year={2025},
  url={https://eprint.iacr.org/2025/917}}
@misc{SWIRL26,
  author={{OpenVM Contributors}},
  title={{SWIRL}: Stacked {WHIR} with Interaction Reductions via {LogUp}},
  year={2026},
  url={https://openvm.dev/swirl.pdf}}
@inproceedings{BCGM25-MCA,
  author={Sarah Bordage and Alessandro Chiesa and Ziyi Guan and Ignacio Manzur},
  title={All Polynomial Generators Preserve Distance with Mutual Correlated Agreement},
  booktitle={CCC},
  year={2026},
  note={ePrint 2025/2051},
  url={https://eprint.iacr.org/2025/2051}}
@misc{BCHKS25,
  author={Eli Ben-Sasson and Dan Carmon and Ulrich Hab{\"o}ck and Swastik Kopparty and Shubhangi Saraf},
  title={On Proximity Gaps for {Reed--Solomon} Codes},
  howpublished={ECCC TR25-169; ePrint 2025/2055},
  year={2025},
  url={https://eprint.iacr.org/2025/2055}}
@misc{CS25-PGC,
  author={Elizabeth Crites and Alistair Stewart},
  title={On {Reed--Solomon} Proximity Gaps Conjectures},
  howpublished={Cryptology ePrint Archive, Paper 2025/2046},
  year={2025},
  url={https://eprint.iacr.org/2025/2046}}
@misc{EF25-zkEVMsec,
  author={{Ethereum Foundation}},
  title={{zkEVM} Security Foundations},
  year={2025},
  note={Blog post, 18 Dec 2025},
  url={https://blog.ethereum.org/2025/12/18/zkevm-security-foundations}}
@misc{soundcalc,
  author={{Ethereum Foundation}},
  title={soundcalc: Soundness Calculator for Hash-Based {zkVMs}},
  year={2026},
  url={https://github.com/ethereum/soundcalc}}
@misc{leanVM,
  author={{leanEthereum}},
  title={{leanVM} (formerly {leanMultisig})},
  year={2026},
  url={https://github.com/leanEthereum/leanVM}}
@inproceedings{Val08,
  author={Paul Valiant}, title={Incrementally Verifiable Computation or Proofs of Knowledge Imply Time/Space Efficiency},
  booktitle={TCC 2008}, series={LNCS}, volume={4948}, pages={1--18}, year={2008}, publisher={Springer},
  doi={10.1007/978-3-540-78524-8_1}}  % volume/pages from memory [unverified]
@inproceedings{CT10,
  author={Alessandro Chiesa and Eran Tromer}, title={Proof-Carrying Data and Hearsay Arguments from Signature Cards},
  booktitle={ICS (ITCS) 2010}, pages={310--331}, year={2010}}
@inproceedings{BCCT13,
  author={Nir Bitansky and Ran Canetti and Alessandro Chiesa and Eran Tromer},
  title={Recursive Composition and Bootstrapping for {SNARKs} and Proof-Carrying Data},
  booktitle={STOC 2013}, pages={111--120}, year={2013}, note={ePrint 2012/095}}
@inproceedings{COS20,
  author={Alessandro Chiesa and Dev Ojha and Nicholas Spooner}, title={Fractal: Post-Quantum and Transparent Recursive Proofs from Holography},
  booktitle={EUROCRYPT 2020}, pages={769--793}, year={2020}, note={ePrint 2019/1076}, url={https://eprint.iacr.org/2019/1076}}
@inproceedings{BCMS20,
  author={Benedikt B{\"u}nz and Alessandro Chiesa and Pratyush Mishra and Nicholas Spooner},
  title={Recursive Proof Composition from Accumulation Schemes}, booktitle={TCC 2020}, year={2020},
  note={ePrint 2020/499 (titled ``Proof-Carrying Data from Accumulation Schemes'')}, url={https://eprint.iacr.org/2020/499}}
@inproceedings{BCLMS21,
  author={Benedikt B{\"u}nz and Alessandro Chiesa and William Lin and Pratyush Mishra and Nicholas Spooner},
  title={Proof-Carrying Data Without Succinct Arguments}, booktitle={CRYPTO 2021}, year={2021},
  note={ePrint 2020/1618}, url={https://eprint.iacr.org/2020/1618}}
@inproceedings{BDFG21,
  author={Dan Boneh and Justin Drake and Ben Fisch and Ariel Gabizon},
  title={Halo Infinite: Proof-Carrying Data from Additive Polynomial Commitments}, booktitle={CRYPTO 2021}, year={2021},
  note={ePrint 2020/1536; PCD-from-PC claim in early ePrint version disputed by BCLMS21}, url={https://eprint.iacr.org/2020/1536}}
@inproceedings{KST22-Nova,
  author={Abhiram Kothapalli and Srinath Setty and Ioanna Tzialla},
  title={Nova: Recursive Zero-Knowledge Arguments from Folding Schemes}, booktitle={CRYPTO 2022}, year={2022},
  note={ePrint 2021/370}, url={https://eprint.iacr.org/2021/370}}
@inproceedings{KS24-HyperNova,
  author={Abhiram Kothapalli and Srinath Setty}, title={HyperNova: Recursive Arguments for Customizable Constraint Systems},
  booktitle={CRYPTO 2024}, year={2024}, note={ePrint 2023/573}, url={https://eprint.iacr.org/2023/573}}
@inproceedings{KP23-RoK,
  author={Abhiram Kothapalli and Bryan Parno}, title={Algebraic Reductions of Knowledge},
  booktitle={CRYPTO 2023}, year={2023}, note={ePrint 2022/009 [unverified]}, url={https://eprint.iacr.org/2022/009}}
@inproceedings{BC23-ProtoStar,
  author={Benedikt B{\"u}nz and Binyi Chen}, title={ProtoStar: Generic Efficient Accumulation/Folding for Special-Sound Protocols},
  booktitle={ASIACRYPT 2023}, year={2023}, note={ePrint 2023/620}, url={https://eprint.iacr.org/2023/620}}
@misc{EG23-ProtoGalaxy,
  author={Liam Eagen and Ariel Gabizon}, title={ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances},
  howpublished={Cryptology ePrint Archive, Paper 2023/1106}, year={2023}, url={https://eprint.iacr.org/2023/1106}}
@misc{ZZZD23-MultiFold,
  author={Zibo Zhou and Zongyang Zhang and Zhiyu Zhang and Jin Dong}, title={Proof-Carrying Data from Multi-folding Schemes},
  howpublished={Cryptology ePrint Archive, Paper 2023/1282}, year={2023}, url={https://eprint.iacr.org/2023/1282}}
@inproceedings{NDCTB24-Mangrove,
  author={Wilson Nguyen and Trisha Datta and Binyi Chen and Nirvan Tyagi and Dan Boneh},
  title={Mangrove: A Scalable Framework for Folding-based {SNARKs}}, booktitle={CRYPTO 2024}, year={2024},
  note={ePrint 2024/416}, url={https://eprint.iacr.org/2024/416}}
@misc{NBS23-NovaCycle,
  author={Wilson Nguyen and Dan Boneh and Srinath Setty}, title={Revisiting the Nova Proof System on a Cycle of Curves},
  howpublished={AFT 2023; ePrint 2023/969 [unverified]}, year={2023}, url={https://eprint.iacr.org/2023/969}}
@misc{BC24-LatticeFold,
  author={Dan Boneh and Binyi Chen}, title={LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems},
  howpublished={Cryptology ePrint Archive, Paper 2024/257 (venue unverified)}, year={2024}, url={https://eprint.iacr.org/2024/257}}
@inproceedings{BC25-LatticeFoldPlus,
  author={Dan Boneh and Binyi Chen}, title={LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems},
  booktitle={CRYPTO 2025}, year={2025}, note={ePrint 2025/247}, url={https://eprint.iacr.org/2025/247}}
@inproceedings{BMNW24,
  author={Benedikt B{\"u}nz and Pratyush Mishra and Wilson Nguyen and William Wang}, title={Accumulation without Homomorphism},
  booktitle={ITCS 2025}, series={LIPIcs}, volume={325}, pages={23:1--23:?}, year={2025},
  doi={10.4230/LIPIcs.ITCS.2025.23}, note={ePrint 2024/474; cited as BMNW25a in WARP}, url={https://eprint.iacr.org/2024/474}}
@inproceedings{BMNW25-Arc,
  author={Benedikt B{\"u}nz and Pratyush Mishra and Wilson Nguyen and William Wang}, title={Arc: Accumulation for Reed--Solomon Codes},
  booktitle={CRYPTO 2025}, year={2025}, note={ePrint 2024/1731; cited as BMNW25b}, url={https://eprint.iacr.org/2024/1731}}
@inproceedings{BCFW25-WARP,
  author={Benedikt B{\"u}nz and Alessandro Chiesa and Giacomo Fenzi and William Wang}, title={Linear-Time Accumulation Schemes},
  booktitle={TCC 2025}, year={2025}, note={ePrint 2025/753 (WARP)}, url={https://eprint.iacr.org/2025/753}}
@inproceedings{BMMS25-FICSFACS,
  author={Anubhav Baweja and Pratyush Mishra and Tushar Mopuri and Matan Shtepel},
  title={{FICS} and {FACS}: Fast {IOPPs} and Accumulation via Code-Switching}, booktitle={CRYPTO 2026 (per ePrint page)}, year={2026},
  note={ePrint 2025/737}, url={https://eprint.iacr.org/2025/737}}
@inproceedings{BCFRRZ25-Blaze,
  author={Martijn Brehm and Binyi Chen and Ben Fisch and Nicolas Resch and Ron D. Rothblum and Hadas Zeilberger},
  title={Blaze: Fast {SNARKs} from Interleaved {RAA} Codes}, booktitle={EUROCRYPT 2025}, pages={123--152}, year={2025},
  note={ePrint 2024/1609}, url={https://eprint.iacr.org/2024/1609}}
@misc{Sze24-DEEP,
  author={Alan Szepieniec}, title={{DEEP} Commitments and Their Applications},
  howpublished={Cryptology ePrint Archive, Paper 2024/1752}, year={2024}, url={https://eprint.iacr.org/2024/1752}}
@inproceedings{GMN22-SnarkPack,
  author={Nicolas Gailly and Mary Maller and Anca Nitulescu}, title={SnarkPack: Practical {SNARK} Aggregation},
  booktitle={FC 2022}, year={2022}, note={ePrint 2021/529}, url={https://eprint.iacr.org/2021/529}}
@misc{ABST22-aPlonk,
  author={Miguel Ambrona and Marc Beunardeau and Anne-Laure Schmitt and Ra{\'u}l R. Toledo},
  title={{aPlonK}: Aggregated {PlonK} from Multi-Polynomial Commitment Schemes},
  howpublished={Cryptology ePrint Archive, Paper 2022/1352 (venue unverified)}, year={2022}, url={https://eprint.iacr.org/2022/1352}}
@inproceedings{CCS22,
  author={Megan Chen and Alessandro Chiesa and Nicholas Spooner}, title={On Succinct Non-interactive Arguments in Relativized Worlds},
  booktitle={EUROCRYPT 2022}, pages={336--366}, year={2022}, note={ePrint 2022/383}, url={https://eprint.iacr.org/2022/383}}
@inproceedings{CCGOS23-AROM,
  author={Megan Chen and Alessandro Chiesa and Tom Gur and Jack O'Connor and Nicholas Spooner},
  title={Proof-Carrying Data from Arithmetized Random Oracles}, booktitle={EUROCRYPT 2023}, series={LNCS}, volume={14005},
  pages={379--404}, year={2023}, note={ePrint 2023/587}, url={https://eprint.iacr.org/2023/587}}
@inproceedings{CGSY24,
  author={Alessandro Chiesa and Ziyi Guan and Shahar Samocha and Eylon Yogev},
  title={Security Bounds for Proof-Carrying Data from Straightline Extractors}, booktitle={TCC 2024}, pages={464--496}, year={2024},
  note={ePrint 2023/1646}, url={https://eprint.iacr.org/2023/1646}}
@inproceedings{BCG24-RelROM,
  author={Annalisa Barbara and Alessandro Chiesa and Ziyi Guan}, title={Relativized Succinct Arguments in the {ROM} Do Not Exist},
  booktitle={TCC 2025}, year={2025}, doi={10.1007/978-3-032-12287-2_14}, note={ePrint 2024/728}, url={https://eprint.iacr.org/2024/728}}
@inproceedings{CMS19,
  author={Alessandro Chiesa and Peter Manohar and Nicholas Spooner}, title={Succinct Arguments in the Quantum Random Oracle Model},
  booktitle={TCC 2019}, year={2019}, note={ePrint 2019/834 [number unverified]}, url={https://eprint.iacr.org/2019/834}}
@inproceedings{CCHLRRW19,
  author={Ran Canetti and Yilei Chen and Justin Holmgren and Alex Lombardi and Guy N. Rothblum and Ron D. Rothblum and Daniel Wichs},
  title={Fiat-Shamir: From Practice to Theory}, booktitle={STOC 2019}, year={2019}}
@inproceedings{BGKTTZ23-FSFRI,
  author={Alexander R. Block and Albert Garreta and Jonathan Katz and Justin Thaler and Pratyush Ranjan Tiwari and Micha{\l} Zaj{\c{a}}c},
  title={Fiat-Shamir Security of {FRI} and Related {SNARKs}}, booktitle={ASIACRYPT 2023}, year={2023},
  note={ePrint 2023/1071}, url={https://eprint.iacr.org/2023/1071}}
@inproceedings{KRS25,
  author={Dmitry Khovratovich and Ron D. Rothblum and Lev Soukhanov}, title={How to Prove False Statements: Practical Attacks on Fiat-Shamir},
  booktitle={CRYPTO 2025}, year={2025}, note={ePrint 2025/118}, url={https://eprint.iacr.org/2025/118}}
@inproceedings{AY25-XFS,
  author={Gal Arnon and Eylon Yogev}, title={Towards a White-Box Secure Fiat-Shamir Transformation},
  booktitle={CRYPTO 2025}, year={2025}, note={ePrint 2025/329}, url={https://eprint.iacr.org/2025/329}}
@misc{Fen26-GenR1CS,
  author={Giacomo Fenzi}, title={How to prove more false statements: Fiat--Shamir limitations on (generated) {R1CS}},
  howpublished={Cryptology ePrint Archive, Paper 2026/1838 (preprint, Aug/Sep 2026)}, year={2026}, url={https://eprint.iacr.org/2026/1838}}
@book{CY24-Book,
  author={Alessandro Chiesa and Eylon Yogev}, title={Building Cryptographic Proofs from Hash Functions}, year={2024},
  note={online book, https://github.com/hash-based-snargs-book [URL unverified]}}
@inproceedings{PP22,
  author={Omer Paneth and Rafael Pass}, title={Incrementally Verifiable Computation via Rate-1 Batch Arguments},
  booktitle={FOCS 2022}, year={2022}, note={[unverified]}}
@misc{arklib2026,
  author = {{ArkLib Contributors} and Dao, Quang and Tuma, Devon and others},
  title  = {{ArkLib}: Formally Verified Arguments of Knowledge in {Lean}},
  howpublished = {\url{https://github.com/Verified-zkEVM/ArkLib}},
  note   = {Commit db7005f, 2026-10-08. No standalone paper found},
  year   = {2026}}
@misc{tuma2024vcvio,
  author = {Tuma, Devon and Hopper, Nicholas},
  title  = {{VCVio}: A Formally Verified Forking Lemma and {Fiat-Shamir} Transform, via a Flexible and Expressive Oracle Representation},
  howpublished = {Cryptology ePrint Archive, Paper 2024/1819},
  year   = {2024}, url = {https://eprint.iacr.org/2024/1819}}
@misc{tuma2026vcvio,
  author = {Tuma, Devon and Dao, Quang and Waters, James and Hicks, Alexander and Hopper, Nicholas},
  title  = {{VCVio}: Verified Cryptography in {Lean} via Oracle Effects and Handlers},
  howpublished = {Cryptology ePrint Archive, Paper 2026/899},
  year   = {2026}, url = {https://eprint.iacr.org/2026/899}}
@misc{comppoly2026,
  author = {{Verified-zkEVM}},
  title  = {{CompPoly}: Computable Polynomials in {Lean}},
  howpublished = {\url{https://github.com/Verified-zkEVM/CompPoly}}, year = {2026}}
@inproceedings{garviabosshard2024sumcheck,
  author = {Garv{\'i}a Bosshard, Azucena and Bootle, Jonathan and Sprenger, Christoph},
  title  = {Formal Verification of the Sumcheck Protocol},
  booktitle = {IEEE Computer Security Foundations Symposium (CSF)},
  year   = {2024}, note = {arXiv:2402.06093; AFP entry Sumcheck\_Protocol}}
@misc{marmsoler2026isabellestark,
  author = {Marmsoler, Diego},
  title  = {{Isabelle/STARK}: A Formalization of {zk-STARK} in {Isabelle/HOL}},
  howpublished = {arXiv:2608.01965}, year = {2026}}
@misc{garreta2025simplefri,
  author = {Garreta, Albert and Mohnblatt, Nicolas and Wagner, Benedikt},
  title  = {A Simplified Round-by-round Soundness Proof of {FRI}},
  howpublished = {Cryptology ePrint Archive, Paper 2025/1993}, year = {2025}}
@misc{hirai2026leanfri,
  author = {Hirai, Yoichi},
  title  = {{Lean4} formalization of ``A Simplified Round-by-round Soundness Proof of {FRI}''},
  howpublished = {zkSecurity blog, \url{https://blog.zksecurity.xyz/posts/simple-rbr-fri/}; code \url{https://github.com/zksecurity/simple-rbr-fri}},
  year   = {2026}, note = {2026-01-26}}
@inproceedings{bailey2024linearpcp,
  author = {Bailey, Bolton and Miller, Andrew},
  title  = {Formalizing Soundness Proofs of Linear {PCP} {SNARKs}},
  booktitle = {33rd USENIX Security Symposium}, pages = {1489--1506}, year = {2024}}
@inproceedings{firsov2023zkeasycrypt,
  author = {Firsov, Denis and Unruh, Dominique},
  title  = {Zero-Knowledge in {EasyCrypt}},
  booktitle = {IEEE CSF}, year = {2023}, note = {ePrint 2022/926}}
@inproceedings{abate2021ssprove,
  author = {Abate, Carmine and Haselwarter, Philipp G. and Rivas, Exequiel and Van Muylder, Antoine and Winterhalter, Th{\'e}o and Hri{\c{t}}cu, C{\u{a}}t{\u{a}}lin and Maillard, Kenji and Spitters, Bas},
  title  = {{SSProve}: A Foundational Framework for Modular Cryptographic Proofs in {Coq}},
  booktitle = {IEEE CSF}, year = {2021}, note = {Extended version TOPLAS 2023}}
@misc{nethermind2025zksync,
  author = {{Nethermind Security Formal Verification Team}},
  title  = {We Verified the Verifier: A First for Zero-Knowledge Proof Systems},
  howpublished = {\url{https://www.nethermind.io/blog/we-verified-the-verifier-a-first-for-zero-knowledge-proof-systems}},
  year   = {2025}, note = {2025-09-02}}
@article{oechsner2025lpzk,
  author = {Oechsner, Sabine and Pereira, Vitor and Scholl, Peter},
  title  = {Who Verifies the Verifiers? Lessons Learned From Formally Verified Line-Point Zero-Knowledge},
  journal = {IACR Communications in Cryptology}, year = {2025}, note = {ePrint 2025/1835}}
@misc{succinct2025sp1lean,
  author = {{Succinct} and {Nethermind}},
  title  = {Formal Verification of {SP1 Hypercube}},
  howpublished = {\url{https://blog.succinct.xyz/nethermind-lean/}}, year = {2025}, note = {2025-10-09}}
@misc{gunton2026sp1bug,
  author = {Gunton, Cody},
  title  = {On Formal Verification and a Bug in {SP1 Hypercube}},
  howpublished = {Ethereum Foundation zkEVM blog, \url{https://zkevm.ethereum.foundation/blog/sp1-fv}},
  year   = {2026}, note = {2026-05-20}}
@misc{sun2026openvm,
  author = {Sun, Yi},
  title  = {Formally Verifying the {OpenVM} {RISC-V} Extension},
  howpublished = {Axiom blog, \url{https://axiom.xyz/blog/formal-verification}},
  year   = {2026}, note = {2026-02-10; report in openvm-org/openvm audits/}}
@misc{nethermind2025certiplonk,
  author = {{Nethermind}},
  title  = {Formally Verifying Zero-Knowledge Circuits: Introducing {CertiPlonk}},
  howpublished = {\url{https://www.nethermind.io/blog/formally-verifying-zero-knowledge-circuits-introducing-certiplonk}},
  year   = {2025}, note = {[date unverified]}}
@misc{dellimmagine2025clean,
  author = {Dell'Immagine, Giorgio},
  title  = {Introducing clean, a formal verification {DSL} for {ZK} circuits in {Lean4}},
  howpublished = {\url{https://blog.zksecurity.xyz/posts/clean/}}, year = {2025}, note = {2025-03-27}}
@misc{mitschabaude2026cleanzkvm,
  author = {Mitscha-Baude, Gregor},
  title  = {Clean: From Verified Circuits to Verified {zkVMs}},
  howpublished = {\url{https://blog.zksecurity.xyz/posts/clean-verified-zkvms/}}, year = {2026}, note = {2026-06-05}}
@misc{dellimmagine2026zkgolf,
  author = {Dell'Immagine, Giorgio and Hall-Andersen, Mathias},
  title  = {zk.golf: Fearless and Collaborative Optimization of Circuits},
  howpublished = {\url{https://blog.zksecurity.xyz/posts/zkgolf/}; \url{https://zk.golf}},
  year   = {2026}, note = {2026-07-02}}
@misc{galois2025zklean,
  author = {{Galois}},
  title  = {{zkLean}: A {DSL} for {ZK} statement verification},
  howpublished = {\url{https://www.galois.com/articles/zklean-a-dsl-for-zk-statement-verification}},
  year   = {2025}, note = {[date unverified]}}
@misc{parker2025verifiedjolt,
  author = {Parker, James},
  title  = {Towards a verified {Jolt} {zkVM}},
  howpublished = {\url{https://www.galois.com/articles/towards-a-verified-jolt-zkvm}},
  year   = {2025}, note = {2025-01-21}}
@misc{kwan2024joltlookup,
  author = {Kwan, Carl and Dao, Quang and Thaler, Justin},
  title  = {Verifying {Jolt} {zkVM} Lookup Semantics},
  howpublished = {Cryptology ePrint Archive, Paper 2024/1841}, year = {2024}}
@misc{biswas2026joltqed,
  author = {Biswas, Ari and Dao, Quang and Ross, Daniel and Thaler, Justin},
  title  = {{Jolt-QED}: Formally Verifying Bytecode Expansions In {Lean}},
  howpublished = {Cryptology ePrint Archive, Paper 2026/2157}, year = {2026}}
@inproceedings{avigad2022cairo,
  author = {Avigad, Jeremy and Goldberg, Lior and Levit, David and Seginer, Yoav and Titelman, Alon},
  title  = {A Verified Algebraic Representation of {Cairo} Program Execution},
  booktitle = {ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP)},
  year   = {2022}, note = {arXiv:2109.14534}}
@misc{avigad2026stwo,
  author = {Avigad, Jeremy and Ganor, Anat and Goldberg, Lior and Levit, David and Nir, Ohad and Seginer, Yoav and Titelman, Alon},
  title  = {Formal verification of the {S-two} {AIR}},
  howpublished = {arXiv:2606.04311}, year = {2026}}
@inproceedings{pailoor2023picus,
  author = {Pailoor, Shankara and Chen, Yanju and Wang, Franklyn and Rodr{\'i}guez, Clara and Van Geffen, Jacob and Morton, Jason and Chu, Michael and Gu, Brian and Feng, Yu and Dillig, I{\c{s}}{\i}l},
  title  = {Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs},
  journal = {Proc. ACM Program. Lang. (PLDI)}, volume = {7}, year = {2023}, doi = {10.1145/3591282},
  note   = {Full author list from memory [verify]}}
@misc{risczero2025picus,
  author = {{RISC Zero}},
  title  = {{RISC Zero}'s Path to The First Formally Verified {RISC-V} {zkVM}},
  howpublished = {\url{https://risczero.com/blog/RISCZero-formally-verified-zkvm}}, year = {2025}, note = {[date unverified]}}
@misc{riscvzkvm2026,
  author = {{Verified-zkEVM}},
  title  = {riscv-zkvm: {Lean} extraction of the {Sail} {RISC-V} specification for verified {zkVM} projects},
  howpublished = {\url{https://github.com/Verified-zkEVM/riscv-zkvm}}, year = {2026}, note = {v0.3.1}}
@misc{evmasm2026,
  author = {{zkSecurity} and {Verified-zkEVM}},
  title  = {evm.asm: A Verified Macro Assembler for building {zkEVM} in {Lean 4}},
  howpublished = {\url{https://github.com/Verified-zkEVM/evm-asm}}, year = {2026}}
@misc{lnsym,
  author = {{leanprover}},
  title  = {{LNSym}: Native Code Symbolic Simulator in {Lean}},
  howpublished = {\url{https://github.com/leanprover/LNSym}}, year = {2024}}
@misc{klaus2026rust2lean,
  author = {Klaus, Natalia and Conejero, Juan and Tolmach, Palina},
  title  = {A {Rust}-to-{Lean} Verification Pipeline with {AI} Provers: An Experience Report},
  howpublished = {arXiv:2605.30106 (AIMACS @ CAV 2026)}, year = {2026}}
@misc{kolozyan2026zkpsec,
  author = {Kolozyan, Arman and Sorger, Tom and Hicks, Alexander and Chaliasos, Stefanos},
  title  = {{ZKP} Security Tools and Verification: Coverage, Effectiveness, Adoption, and Challenges},
  howpublished = {arXiv:2607.23752}, year = {2026}}
@misc{verifiedzkevm,
  author = {{Ethereum Foundation}},
  title  = {Verified {zkEVM} Project: Grants},
  howpublished = {\url{https://verified-zkevm.org/grants/}}, year = {2026}}
@misc{otsgolf2026,
  author = {{leanEthereum}},
  title  = {ots.golf: optimal one-time signatures with {Lean}-certified bounds},
  howpublished = {\url{https://ots.golf}; \url{https://github.com/leanEthereum/ots.golf-dev} (docs/AUDIT.md, docs/upper-riscv.md)}, year = {2026}}
@misc{siggolf2026,
  author = {{Yukon (Eigen Labs)} and {Ethereum Foundation}},
  title  = {sig.golf},
  howpublished = {\url{https://www.yukon.org/sig.golf}; \url{https://github.com/Layr-Labs/sig.golf-dev}}, year = {2026}}
@misc{proximityprize2026,
  author = {{Yukon} and {zkSecurity}},
  title  = {The Proximity Prize: {IRS} reduction threshold},
  howpublished = {\url{https://better.codes}; \url{https://github.com/proximity-prize/proximity-prize}}, year = {2026}}
@misc{yukon2026,
  author = {{Eigen Labs}},
  title  = {Yukon: open autoresearch challenges},
  howpublished = {\url{https://www.yukon.org}}, year = {2026}}
@misc{novikov2025alphaevolve,
  author = {Novikov, Alexander and V{\~u}, Ng{\^a}n and Eisenberger, Marvin and others and Balog, Matej},
  title  = {{AlphaEvolve}: A coding agent for scientific and algorithmic discovery},
  howpublished = {arXiv:2506.13131}, year = {2025}}
@misc{georgiev2025mathscale,
  author = {Georgiev, Bogdan and G{\'o}mez-Serrano, Javier and Tao, Terence and Wagner, Adam Zsolt},
  title  = {Mathematical exploration and discovery at scale},
  howpublished = {arXiv:2511.02864}, year = {2025}}
@article{hubert2025alphaproof,
  author = {Hubert, Thomas and Mehta, Rishi and Sartran, Laurent and others and Silver, David},
  title  = {Olympiad-level formal mathematical reasoning with reinforcement learning},
  journal = {Nature}, year = {2025}, doi = {10.1038/s41586-025-09833-y}}
@misc{karpathy2026autoresearch,
  author = {Karpathy, Andrej},
  title  = {autoresearch},
  howpublished = {\url{https://github.com/karpathy/autoresearch}}, year = {2026}}
@misc{sothanaphan2026erdos728,
  author = {Sothanaphan, Nat},
  title  = {Resolution of {Erd\H{o}s} Problem \#728: a writeup of {Aristotle}'s {Lean} proof},
  howpublished = {arXiv:2601.07421}, year = {2026}}
@misc{bolan2025etp,
  author = {Bolan, Matthew and Breitner, Joachim and Brox, Jose and Carlini, Nicholas and Carneiro, Mario and others and Tao, Terence},
  title  = {The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale},
  howpublished = {arXiv:2512.07087}, year = {2025}}
@misc{zhang2026shorlean,
  author = {Zhang, Lei and Zhao, Yusheng and Yao, Hongshun and Wang, Xin},
  title  = {Building {Shor}'s Algorithm in {Lean}: An Agentic Formalization of Quantum Attacks on {RSA-2048} and {P-256}},
  howpublished = {arXiv:2607.14082}, year = {2026}}
@misc{comparator,
  author = {{Lean FRO}},
  title  = {comparator: a trustworthy judge for {Lean} proofs},
  howpublished = {\url{https://github.com/leanprover/comparator}}, year = {2025}}
@misc{lean4checker,
  author = {{Lean FRO}},
  title  = {lean4checker},
  howpublished = {\url{https://github.com/leanprover/lean4checker}}, year = {2023}}
@misc{lean4export,
  author = {{Lean FRO}},
  title  = {lean4export: plain-text declaration export for {Lean 4}},
  howpublished = {\url{https://github.com/leanprover/lean4export}}}
@misc{nanoda,
  author = {ammkrn},
  title  = {nanoda\_lib: an independent type checker for {Lean 4}},
  howpublished = {\url{https://github.com/ammkrn/nanoda_lib}}}
@misc{carneiro2024lean4lean,
  author = {Carneiro, Mario},
  title  = {{Lean4Lean}: Towards a formalized metatheory for the {Lean} theorem prover},
  howpublished = {arXiv:2403.14064}, year = {2024}}
@misc{safeverify,
  author = {{GasStationManager}},
  title  = {{SafeVerify}},
  howpublished = {\url{https://github.com/GasStationManager/SafeVerify}; fork \url{https://github.com/mistralai/LeanstralSafeVerify}}, year = {2024}}
@manual{leanref_validating,
  author = {{Lean FRO}},
  title  = {The {Lean} Language Reference: Validating Proofs},
  url    = {https://lean-lang.org/doc/reference/latest/ValidatingProofs/}, year = {2026}}
@manual{lean4321,
  author = {{Lean FRO}},
  title  = {{Lean} 4.32.1 release notes (kernel soundness fix, issue \#14484)},
  url    = {https://lean-lang.org/doc/reference/latest/releases/v4.32.1/}, year = {2026}}
@manual{lean4340,
  author = {{Lean FRO}},
  title  = {{Lean} 4.34.0 release notes (soundness fixes \#14806, \#14807, \#14838)},
  url    = {https://lean-lang.org/doc/reference/latest/releases/v4.34.0/}, year = {2026}}
@misc{brossard2026leanproj,
  author = {Brossard, Jonathan},
  title  = {Lean 4 kernel soundness bug: forging proofs via nested inductive projections},
  howpublished = {oss-security mailing list, \url{https://openwall.com/lists/oss-security/2026/08/02/1}}, year = {2026}}
@misc{dougherty2026lies,
  author = {Dougherty, Quinn and von Hippel, Max},
  title  = {Lies, Damned Lies, and Proofs: Formal Methods are not Slopless},
  howpublished = {LessWrong, \url{https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg}}, year = {2026}}
@inproceedings{ammanamanchi2026faults,
  author = {Ammanamanchi, Pawan Sasanka and Bhat, Siddharth and Biderman, Stella},
  title  = {Faults in Our Formal Benchmarking: Dataset Defects and Evaluation Failures in {Lean} Theorem Proving},
  booktitle = {ICML}, year = {2026}, note = {arXiv:2606.29493}}
@misc{paglieri2026swarm,
  author = {Paglieri, Davide and Cross, Logan and Genewein, Tim and Leibo, Joel Z. and Tomasev, Nenad and Vezhnevets, Alexander Sasha},
  title  = {A Case Study on Emergent Cheating and Whistleblowing in Autonomous Research Swarms},
  howpublished = {arXiv:2609.04170}, year = {2026}}
@misc{longcat2026prover,
  author = {Wang, Jianing and Zhang, Jianfei and Guo, Qi and others},
  title  = {{LongCat-Flash-Prover}: Advancing Native Formal Reasoning via Agentic Tool-Integrated Reinforcement Learning},
  howpublished = {arXiv:2603.21065 (Meituan LongCat Team)}, year = {2026}}
@misc{anthropic2026rewardseeker,
  author = {{Anthropic Alignment Science}},
  title  = {Training a Misaligned Reward Seeker},
  howpublished = {\url{https://alignment.anthropic.com/2026/reward-seeker/}}, year = {2026}, note = {[authors not checked]}}
@inproceedings{RRR16,
  author={Omer Reingold and Guy N. Rothblum and Ron D. Rothblum}, title={Constant-Round Interactive Proofs for Delegating Computation},
  booktitle={STOC 2016}, pages={49--62}, year={2016}, note={Independent introduction of IOPs as ``probabilistically checkable interactive proofs''}}
@inproceedings{CHMMVW20-Marlin,
  author={Alessandro Chiesa and Yuncong Hu and Mary Maller and Pratyush Mishra and Psi Vesely and Nicholas Ward},
  title={Marlin: Preprocessing {zkSNARKs} with Universal and Updatable {SRS}}, booktitle={EUROCRYPT 2020}, year={2020},
  note={ePrint 2019/1047}, url={https://eprint.iacr.org/2019/1047}}
@misc{Hol19,
  author={Justin Holmgren}, title={On Round-By-Round Soundness and State Restoration Attacks},
  howpublished={Cryptology {ePrint} Archive, Paper 2019/1261}, year={2019}, url={https://eprint.iacr.org/2019/1261}}
@inproceedings{AFK22,
  author={Thomas Attema and Serge Fehr and Michael Klo{\ss}}, title={Fiat-Shamir Transformation of Multi-Round Interactive Proofs},
  booktitle={TCC 2022}, year={2022}, note={ePrint 2021/1377; extended version in J. Cryptology 2023}, url={https://eprint.iacr.org/2021/1377}}
@misc{AFKR23,
  author={Thomas Attema and Serge Fehr and Michael Klo{\ss} and Nicolas Resch},
  title={The Fiat--Shamir Transformation of $(\Gamma_1,\dots,\Gamma_\mu)$-Special-Sound Interactive Proofs},
  howpublished={Cryptology {ePrint} Archive, Paper 2023/1945}, year={2023}, url={https://eprint.iacr.org/2023/1945}}
@inproceedings{BGTZ23,
  author={Alexander R. Block and Albert Garreta and Pratyush Ranjan Tiwari and Micha{\l} Zaj{\k{a}}c},
  title={On Soundness Notions for Interactive Oracle Proofs}, booktitle={Springer LNCS proceedings, 2023 (doi 10.1007/978-981-99-8724-5\_1; conference not confirmed)},
  year={2023}, note={ePrint 2023/1256}, url={https://eprint.iacr.org/2023/1256}}
@inproceedings{CY21-Micali,
  author={Alessandro Chiesa and Eylon Yogev}, title={Tight Security Bounds for {Micali}'s {SNARGs}},
  booktitle={TCC 2021}, year={2021}, note={ePrint 2021/188}, url={https://eprint.iacr.org/2021/188}}
@inproceedings{CO25-DuplexFS,
  author={Alessandro Chiesa and Michele Orr{\`u}}, title={A {Fiat--Shamir} Transformation From Duplex Sponges},
  booktitle={TCC 2025}, year={2025}, note={ePrint 2025/536}, url={https://eprint.iacr.org/2025/536}}
@misc{Hab25-MCA,
  author={Ulrich Hab{\"o}ck}, title={A note on mutual correlated agreement for {Reed--Solomon} codes},
  howpublished={Cryptology {ePrint} Archive, Paper 2025/2110}, year={2025}, url={https://eprint.iacr.org/2025/2110}}
@misc{Jo26-MCA,
  author={Sunghyeon Jo}, title={{Reed--Solomon} Mutual Correlated Agreement Beyond the {Johnson} Radius},
  howpublished={Cryptology {ePrint} Archive, Paper 2026/1432}, year={2026}, url={https://eprint.iacr.org/2026/1432}}
@misc{GG25,
  author={Rohan Goyal and Venkatesan Guruswami}, title={Optimal Proximity Gaps for Subspace-Design Codes and (Random) {Reed--Solomon} Codes},
  howpublished={Cryptology {ePrint} Archive, Paper 2025/2054}, year={2025}, url={https://eprint.iacr.org/2025/2054}}
@misc{GGSW26,
  author={Rohan Goyal and Venkatesan Guruswami and Yihang Sun and Mary Wootters}, title={Locality of Curve-Decoding and Improved Proximity Gaps},
  howpublished={arXiv:2607.08516}, year={2026}, url={https://arxiv.org/abs/2607.08516}}
@article{DG25-Interleaved,
  author={Benjamin E. Diamond and Angus Gruen}, title={Proximity Gaps in Interleaved Codes},
  journal={IACR Communications in Cryptology}, volume={1}, number={4}, year={2025}, doi={10.62056/a0ljbkrz}, url={https://cic.iacr.org/p/1/4/8}}
@inproceedings{DG25-Dist,
  author={Benjamin E. Diamond and Angus Gruen}, title={On the Distribution of the Distances of Random Words},
  booktitle={CRYPTO 2026}, year={2026}, doi={10.1007/978-3-032-35398-6_4}, note={ePrint 2025/2010}, url={https://eprint.iacr.org/2025/2010}}
@misc{KKH26,
  author={Dmitry Krachun and Stepan Kazanin and Ulrich Hab{\"o}ck}, title={Failure of Proximity Gaps Close to Capacity},
  howpublished={Cryptology {ePrint} Archive, Paper 2026/782}, year={2026}, url={https://eprint.iacr.org/2026/782}}
@misc{Kam26,
  author={Antonio Kambir{\'e}}, title={Proximity Gaps Conjecture Fails Near Capacity over Prime Fields},
  howpublished={arXiv:2604.09724}, year={2026}, url={https://arxiv.org/abs/2604.09724}}
@misc{GYXK26,
  author={Yiwen Gao and Hong Yang and Yang Xu and Haibin Kan}, title={List-Decoding Counterexamples Yield Lower Bounds on Mutual Correlated Agreement Error},
  howpublished={arXiv:2607.10572}, year={2026}, url={https://arxiv.org/abs/2607.10572}}
@misc{ABF26,
  author={Gal Arnon and Dan Boneh and Giacomo Fenzi}, title={Open Problems in List Decoding and Correlated Agreement},
  howpublished={Cryptology {ePrint} Archive, Paper 2026/680 (rev. 2026-07-06); companion to the EF Proximity Prize}, year={2026}, url={https://eprint.iacr.org/2026/680}}
@misc{ProximityPrize,
  author={{Ethereum Foundation}}, title={The Proximity Prize},
  howpublished={\url{https://proximityprize.org/}}, year={2026}, note={\$1M; judges Boneh, Fenzi, Arnon; deadline 2027-12-31; accessed 2026-10-10}}
```
