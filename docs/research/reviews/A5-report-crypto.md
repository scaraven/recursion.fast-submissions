<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `reviews/A5-report-crypto.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
# A5: adversarial cryptographic review of the report (sections 03, 04, 05, 08, 09, 11)

Reviewer: A5 (cryptography). Date: 2026-10-11. Object: `report/sections/{03-background,04-prior-competitions,05-brief-review,08-security,09-recursion,11-benchmark}.tex`.
Ground truth: `design/DESIGN.md` v0.3 (incl. §15), D1–D4, A1–A4, R1–R8.
No report file was edited.

**How the sources were checked.** I read these primary sources in full text:
- the Chiesa–Yogev book, version of 2026-03-25, from the authors' GitHub (printed page = PDF page − 16);
- WARP, ePrint 2025/753, version of 2025-05-28; a revision dated 2026-06-18 exists but could not be fetched;
- BCHKS25 (ePrint 2025/2055 = ECCC TR25-169), BCIKS20, BCGM25, Hab25, Jo26, GG25, DG25-Dist, CS25, Kam26;
- KRS25 (ePrint 2025/118), Holmgren 2019/1261, CMS19 (2019/834), BGTZ23, AFK22.

KKH26 and ABF26 were checked from their abstracts or landing pages only. Source texts are under the session scratchpad (`agentA/`, `agentB/`, `agentC/`, `krs/`).

Severity:
- **critical** = a stated security claim is false or unsupported in a way that changes what a record certifies;
- **major** = a wrong theorem, number or attribution that a referee would reject, or an inconsistency with DESIGN v0.3;
- **minor** = precision, wording or metadata.

There are no critical findings. The Lean-facing definitions (S-1, the counting form, the cap, the honest labelling) are sound and match DESIGN v0.3. The problems are in the cited meta-theory, the binary-field rationale, the Fiat–Shamir mitigation story, and a handful of numbers.

---

## Summary table

| ID | Sev. | Location | One-line |
|---|---|---|---|
| M1 | major | 08:258-262, 09:379-384, 05:86-87 | Statement binding does **not** mitigate KRS25; KRS25 attacks the *strong* FS transform |
| M2 | major | 03:523-527 (+ DESIGN §3 rationale) | "GF(2^128) cannot meet a 2^-128 per-round cap in any regime" is false: the `chal nE` shape allows in-round parallel repetition |
| M3 | major | 03:210-213, 03:288-289, 03:250-261, 03:719-721, 09:55-57 | Wrong theorem chain for knowledge (CY 31.3.1 / WARP 2.8 / CY 32.8.9 / "Thm 2.8 compiles to a NARG"); DESIGN v0.3 says WARP B.4 + CY 32.8.10, and compilation to the accumulation scheme is WARP Thm 10.3 |
| M4 | major | 03:251, 03:92, 08:191-193 | The CY simplification condition uses ℓ = **Σ** of oracle lengths (incl. ℓ₀ in ch. 32), not max; t* ≈ 2^41 is computed with the wrong ℓ, and idxLen is uncapped |
| M5 | major | 03:529, 03:543-544, 11:276, 08:172-173 | Johnson query counts wrong: η=0.011 gives **268** (not 272), η=0.0055 gives **262** (not 268); 11 is internally inconsistent (268 at l.229, 272 at l.276) |
| M6 | major | 03:391, 03:561-566 | BCHKS25 Thm 1.6/Cor 1.7 misdescribed: not "every rate", not "rules out gaps beyond Johnson over char 2", not "1/η^5 cannot be removed" |
| M7 | major | 08:294-319, 03:542 | The first hypothesis, `McaJohnson` = BCHKS25 Thm 4.6, fails S-5's own admission rule. The paper is a preprint, Thm 4.6 has only a proof sketch "restricted to the separable case", and the Lean stub hard-codes /2^192 over an unspecified field |
| M8 | major | 09:218-223 | A linear decider at 2^24 (≈6.7×10^9) violates the stated cap C_dec ≤ 2^32 ≈ 4.3×10^9, yet the text treats it as admissible-but-dominated; 10-cost.tex:535 says the cap bans it |
| M9 | major | 08:138-140, 03:177-180 | "WARP strictly relaxes the book's global extractor (CY Def 31.1.6)" is a misattribution: WARP relaxes its Def 2.5 (CMS19 prefix-only extractor), and strictness is asserted, not proved |
| M10 | major | 05:78 | Brief-review resolution 10 ("sig.golf weights, no field precompiles") contradicts DESIGN v0.2/v0.3 (Zbc machine, per-profile weights, latency board) |
| m1–m30 | minor | various | see below |

---

## Major findings

### M1 (major): KRS25 is not mitigated by statement binding
**Where.**
- 08-security.tex:258-262: "the attacks of KRS25 and Fen26 break Fiat–Shamir-compiled protocols exactly when an accepting transcript can be prepared before the statement is bound … Fenzi's mitigation is to derive the first challenge from the generated statement."
- 09-recursion.tex:379-384: "These are exactly the preconditions of the attacks in KRS25, Fen26. The harness's transcript prefix therefore absorbs …".
- 05-brief-review.tex:86-87: "Fiat–Shamir statement binding against recent attacks on generated R1CS [KRS25, Fen26]".

**Problem.** KRS25 attacks the strong (statement-hashing) Fiat–Shamir transform. Its §1.2 says: "In this work we consider the strong variant (which can be seen by the fact that the circuit description is included in the hash) and show that it is insecure when applied to the GKR-based argument-system". The attack is a diagonalisation: the circuit evaluates the FS hash itself. Absorbing `MTroot(IDX i) ‖ VK i ‖ x` does not prevent it. The S-4 prefix rule answers weak FS (BPW12) and Fenzi's generated-statement attack. KRS25 remains a pure deployment risk, which 03:308-312 correctly says.

The current text implies to a reader that the harness rule closes both attacks. That overstates the security of every deployed recursive record.

**Fix (08:258-262).**
> The compiler must preserve this binding. Two attack classes sit outside it. Weak Fiat–Shamir and Fenzi's generated-statement attacks \cite{BPW12-WeakFS,Fen26-GenR1CS} succeed when an accepting transcript can be prepared before the statement is bound; Fenzi proves that deriving the first challenge from the generated statement restores the soundness of the underlying protocol. The attack of \cite{KRS25} is different: it breaks the \emph{strong} transform, with the statement absorbed, whenever the proved relation can evaluate the Fiat--Shamir hash. No prefix rule prevents it, so it is covered only by the deployment assumption \lean{RecursionHeuristic}.

**Fix (09:379-384), first sentence.**
> The R1CS is generated from programs, which is the precondition of \cite{Fen26-GenR1CS}; the harness prefix answers it by absorbing … The recursion circuit also contains the Fiat--Shamir hash, the precondition of \cite{KRS25}; that attack is not answered by binding and is part of \lean{RecursionHeuristic}.

**Fix (05:86-87).** "… Fiat–Shamir statement binding against weak-FS and generated-R1CS attacks \cite{BPW12-WeakFS,Fen26-GenR1CS}, and the hash-in-circuit attack of \cite{KRS25} as a named deployment assumption …"

### M2 (major): the "GF(2^128) is too small" argument is false as stated
**Where.** 03-background.tex:523-527 says every round error has the form numerator/|E| with numerator ≥ 2, so "a 128-bit challenge field therefore cannot meet a 2^-128 per-round cap in any regime." The same rationale appears in DESIGN §3 ("a K challenge has error ≥ 2^-64 and cannot meet the cap") and 05:76.

**Problem.** The premise holds only when each round draws one field element. The contract's round shape `chal nE idx` (07-protocol-model.tex:166,219) lets a round carry n_E independent E-elements. A round that runs the same check with two independent challenges is doomed unless both are bad:
- a batching or proximity step then has error (a/|F|)², which over GF(2^128) at UD is about 2^-210;
- sumcheck run in two parallel copies has error (d/|F|)² per round.

This is standard practice: Plonky2 sets `num_challenges = 2` over Goldilocks, and small-field STARKs do the same. The arithmetic does not favour GF(2^192) either. Two GF(2^128) = K² Karatsuba products cost 2×3 = 6 K-products, the same as one GF(2^192) product. The real costs of repetition are the duplicated prover work, the duplicated oracles or answers, and protocol complexity. Those are arguments, not an impossibility. Likewise, three K-valued challenges in one round give d³/2^192.

**Fix (03:523-528).**
> \paragraph{Why $\mathrm{GF}(2^{192})$.} With a \emph{single} challenge per round, every round error has the form (numerator)$/|E|$ with numerator at least $2$ … so one $\mathrm{GF}(2^{128})$ element cannot meet a $2^{-128}$ cap. In-round repetition (several independent challenges in one \lean{chal} round) would meet it at roughly the same field cost, since two $\mathrm{GF}(2^{128})$ products cost as many $K$-products as one $\mathrm{GF}(2^{192})$ product, but it doubles the affected prover work and oracle answers and complicates every protocol. The design therefore fixes $E=\mathrm{GF}(2^{192})$, with one challenge per check, as the simpler option, not the only one.

Then retitle the paragraph and drop "in any regime". In DESIGN §3, the parenthetical "(a K challenge has error ≥ 2^-64 and cannot meet the cap)" should read "(a single K challenge …)". The menu restriction stays justified as a simplicity and hygiene rule.

### M3 (major): the knowledge-soundness theorem chain is cited inconsistently and partly wrongly
DESIGN v0.3 §5, adopted from A2-M1, says:
- soundness: CY Thm 31.2.1 + 32.8.9;
- knowledge: WARP Thm B.4 + CY Thm 32.8.10, with unbounded extraction at L1.

08-security.tex:180-190 follows this. The background and recursion sections do not.

1. **03:210-213 (Thm bg-rbr-sr, item 3).** "κ^sr(t) ≤ (t+k)κ_rbr with a straight-line SR extractor [CY Thm 31.3.1]" is correct only for the book's notion (Def 31.1.6). "For the backward-extractor variant, the same bound is [WARP Thm 2.8]" is acceptable only as a citation of the informal statement. The formal theorem is **WARP Thm B.4** with Construction B.5, p. 66: "IOR has straightline state-restoration knowledge soundness … ε^sr ≤ (t+k)·ε^rbr and extraction time et ≤ Σ et_i".
   Fix: "… is \cite[Thm.~2.8, formally Thm.~B.4 with Constr.~B.5]{BCFW25-WARP}, with extraction time $\sum_i\mathit{et}_i$."
2. **03:288-289 (Fig. bg-pipeline).** The arrow labels are "CY 31.3.1 / WARP 2.8" for IOP → SR and "CY 26.1.1 / CY 32.8.9" for SR → BCS/COS. The IOP box is the contract's notion, i.e. the WARP variant, so CY 31.3.1 does not apply to it (A2-M1 item 1). CY 32.8.9 is the holographic *soundness* theorem; holographic knowledge is 32.8.10.
   Fix: replace the labels with `CY 31.2.1 (sound)` / `WARP B.4 (knowl.)` and `CY 32.8.9 (sound)` / `CY 32.8.10 (knowl.)`.
3. **03:250-261 (Thm bg-bcs).** It cites "Thms 25.2.1, 26.1.1, 31.3.1" and then 32.8.9 for "soundness and straight-line knowledge" of COS. Three corrections:
   - Knowledge for COS is Thm 32.8.10, whose straight-line case is its "Moreover" clause; the main statement is rewinding (Def 32.6.6).
   - Thm 26.1.1's main statement is also rewinding (Def 23.2.5); straight-line is its "Moreover" clause.
   - The extraction-time formula is CY's, et^sr + et^mm_MT + O(r_max·k·t·log t) with r_max = max_i log|R_i|. The text writes O(r_max·k·t log t) without defining r_max.
   Fix: cite "[Thms 25.2.1 and 26.1.1 (straight-line clause)]" and "COS: Thm 32.8.9 (soundness), Thm 32.8.10 (knowledge, straight-line clause)". Define r_max.
4. **03:719-721.** "WARP's Theorem 2.8 then compiles RBR-KS of the reduction into straight-line SR knowledge soundness of a non-interactive accumulation scheme." Thm 2.8 gives SR-KS of the interactive IOR. The non-interactive accumulation scheme is **WARP Thm 10.3** (Construction 10.4). Its proof applies the adapted BCS compilation [BCS16; BMNW25b] and uses B.4 for the SR term.
   Fix: "WARP's Thm.~2.8 (formally B.4) turns RBR-KS of the reduction into straight-line SR knowledge soundness with error $(t+k)\eps_{\mathrm{rbr}}$, and its Thm.~10.3 compiles the result into a non-interactive accumulation scheme \cite{BCFW25-WARP}."
5. **09:55-57 (REC-1 rationale).** "compiles, via BCS and Fiat–Shamir, into a non-interactive split accumulation scheme … [Thm 2.8]" has the same error. Cite "[Thms B.4 and 10.3]".
6. **03:157 and 08:52.** "Defs 2.6–2.7" are WARP's *informal* overview definitions (§2.8, p. 21). The formal ones are **Defs 4.1–4.2** (p. 30, with extraction times et_i). For a definition the contract claims to transcribe, cite "Defs 4.1–4.2 (informally 2.6–2.7)".
7. The takeaway at 03:341-342 ("the compiled bound is … $(t+k)\eps+4.5t^2/2^\lambda$") also omits the side conditions. See M4.

### M4 (major): the side condition of the 3.5/4.5 simplification uses the total oracle length
**Where.**
- 03:92 defines ℓ = max_j ℓ_j, and 03:251 uses "t ≥ 2(log ℓ+1)·ℓ".
- 08:191-193: "With ℓ ≤ 2^34 at the top class this means t ≳ t* ≈ 2^41."

**Evidence.** CY Thm 25.2.1, p. 278: "We define l := Σ_{i∈[k]} l_i". In ch. 32, l := l_0 + Σ_i l_i (Thm 32.8.9, p. 419: "≤ 4.5·t²/2^λ if t ≥ 2·l_0 and t ≥ 2·(log l+1)·l").

**Problem.** With the admission caps, Σ_{j≥1} ℓ_j ≤ V_k·(N_k + 2^{k+4}) ≤ 2^8·(2^24+2^28) ≈ 2^36.1 K-elements at k = 24. The term ℓ₀ = idxLen comes on top, and DESIGN §7 caps neither idxLen nor ℓ₀: V_k explicitly excludes IDX. So:
- t* is at least about 2·37·2^36.1 ≈ 2^42.3, not 2^41;
- it is unbounded unless idxLen is capped.

The headline's numerical consequence is still negligible: the max(t,t*) term stays below 2^-160 for any t* ≤ 2^46. However, the headline is presented as exact ("stated with these conditions wherever it appears"), and its t* has to be a function of declared quantities.

**Fix (08:191-194).**
> The simplified hash term requires $t\ge 2\ell_0$ and $t\ge 2(\log\ell+1)\ell$, where $\ell=\ell_0+\sum_{j\ge1}\ell_j$ is the \emph{total} length of the index oracle and all prover oracles \cite[Thm.~32.8.9]{CY24-Book}. Set $t^*:=\max(2\ell_0,\,2(\log\ell+1)\ell)$. The Merkle and collision terms are non-decreasing in $t$, so for $t<t^*$ they are bounded by their value at $t^*$. Under the admission caps ($V_k\le2^8$, and an index-oracle cap such as $\ell_0\le2^{k+8}$) this gives $t^*<2^{43}$ at the top class.

DESIGN §7 should add an explicit idxLen cap; for example, 2^{k+8} K-elements would give t* ≈ 2^43. In 03:92, rename the max to ℓ_max or define ℓ as the sum. In 03:264-269 the worked example uses "t ≤ 2^120". Align it with the headline: "2k ≤ t ≤ 2^124, t ≥ t* (or max(t,t*))".

Also, "the bound is monotone in t, so t is replaced by max(t,t*)" (08:193-194) is ambiguous. Replacing t everywhere would also change the first term to (t*+k)·2^-128. The boxed formula replaces t only in the quadratic term, which is correct only via the monotonicity of the Merkle term, so say that.

### M5 (major): Johnson query counts are miscomputed (272/268 should be 268/262)
**Check.** With γ = 1−√ρ−η and s = ⌈128/(−log2(1−γ))⌉:

| ρ | η | s (report) | s (correct) |
|---|---|---|---|
| 1/2 | 0.0177 | 276 | 276 |
| 1/2 | 0.011 | 272 | **268** |
| 1/2 | 0.0055 | 268 | **262** |
| 1/4 | 0.0125 | 133 | 133 |

11-benchmark.tex:229 itself uses 268/133/67 for η = 0.011, which is correct and contradicts its own 11:276 ("272 at ρ = 1/2"). D3 is inconsistent in the same way: D3:79 says 272, D3:444 says 268.

**Fixes.**
- 03:529: "slack η≈0.011–0.018, i.e. 268–276 queries at ρ=1/2 instead of the slack-free 256 (+5–8%)".
- 03:543: "(268 queries)".
- 03:544: "(262 queries)".
- 11:276: "(268 at ρ=1/2)".
- If the trajectory model (D3 §6) used 272, re-run it or state which value it used.
- D3:22, 79 and 80 have the same error.

The 2^-131/2^-134 figures in 08:172-173 and table 03:542-544 are correct. With the exact Thm 4.6 formula at n = 2^25, log2 a = 52.61, 56.08 and 61.00, and the ρ = 1/4 row matches 55.11 at n = 2^26. Add "n = 2^24/ρ" to the caption of table 03:548, because the UD row uses n = 2^25 and the ρ = 1/4 row needs n = 2^26. At n = 2^25 it would be 2^54.1.

### M6 (major): BCHKS25 Thm 1.6 / Cor 1.7 are overstated
**Where.**
- 03:391 (table row): "at Johnson (η=0), char 2: some RS codes on F2-subspaces need a=Ω(n^{2−ε}) [Thm 1.6]".
- 03:561-566: "for every characteristic-2 field there are RS codes … at the Johnson radius … This rules out gaps beyond Johnson over characteristic 2 and shows that the 1/η^5 slack cannot be removed."
- 08:321-324 (milder).

**Evidence.**
- Thm 1.6 is a family indexed by τ, with λ_τ = 2^{-(τ+2)}, δ = 1−λ_τ and γ = 1−4λ_τ. This γ equals the Johnson radius only at τ = 2.
- Cor 1.7 is that case: δ = 15/16 (rate ≈ 1/16), γ = J(δ) = 3/4, with ≥ n^{2(1−ε)} close points and a *constant* proximity loss (Δ ≥ 7/8).
- For the other τ the theorem refutes the capacity conjecture *below capacity* for these char-2 codes.
- The paper says explicitly that versions of the conjecture "may still be true … for well chosen evaluation domains D over fields of characteristic 2".
- It says nothing about the exponent 5. Its only conclusion about η is that a cannot stay O(n) as γ crosses J(δ).

**Fix (03:561-566).**
> The characteristic-2 negative results are BCHKS25 Thm.~1.6 and Cor.~1.7. For every field of characteristic 2 there are RS codes on (essentially random) $\F_2$-subspaces, of rate about $1/16$, with $n^{2-o(1)}$ exceptional points at the Johnson radius ($\eta=0$) and a constant proximity loss; at higher rates the same family refutes the capacity conjecture below capacity. So no bound linear in $n$ can hold at $\eta=0$ for all such codes, and a beyond-Johnson gap over characteristic~2 would have to depend on the choice of domain (the paper leaves this open). Nothing is implied for $\eta>0$, which is exactly the proven-regime policy; whether the $1/\eta^5$ dependence is tight is open.

**Fix (03:391).** "at Johnson (η=0), char. 2, rate ≈1/16 | n^{2−o(1)} exceptional points on random F_2-subspaces [Thm 1.6, Cor 1.7]; beyond-Johnson refuted for these codes | lower bound".

In 08:321-323 add "(at rate ≈ 1/16, Cor. 1.7)".

### M7 (major): `McaJohnson` does not meet S-5's own admission criteria, and the stub mis-types the field
**Where.** 08:294-319 (Decision S-5 and the listing); 03:542 and 03:559-560.

**Problems.**
1. S-5 requires "the verbatim transcription of one published, peer-reviewed theorem". As of this review, BCHKS25 is an ePrint/ECCC preprint (ePrint 2025/2055, ECCC TR25-169, Nov 2025); I found no venue.
2. Thm 4.6, the MCA version, comes with a proof *sketch* that says "(for simplicity we restrict to the separable case)". Thm 1.5, plain CA for lines, handles the inseparable case by pointing to BCIKS20 App. C. In characteristic 2 inseparability is exactly the case that is skipped. So for K/E the MCA statement rests on a sketch. The background (03:559-560: "carry no characteristic restriction") is literally true of the statements but hides this.
3. The Lean stub reads `∀ (D : Finset K) … mcaError (RS D deg) γ ≤ johnsonA ρ η γ D.card / 2^192`. Two typing problems:
   - BCHKS25's error is a/|F| for the field F of the code and of the combination randomness. A bound with /2^192 needs the code to be RS[E, D, deg] with D ⊆ K ⊂ E and z ∈ E. If `RS D deg` is over K, the bound is a misstatement, since the theorem would give a/2^64.
   - Even over E, hard-coding the field size as a numeral, rather than `Fintype.card E`, invites a transcription error in the trusted text.
4. Thm 4.6's m is max(⌈√ρ/η⌉, 3), and the guard in 08:302 omits the max with 3. Thm 1.5 uses max(⌈√ρ/(2η)⌉, 3), which would give bounds about 4.9 bits smaller. The report should say it uses the conservative Thm 4.6 constant.

**Fix (08:297-302).**
> … Each is the verbatim transcription of one published theorem with a complete proof over the exact code family … The first, \lean{McaJohnson}, transcribes \cite[Thm.~4.6]{BCHKS25} (a preprint whose MCA proof is given as a sketch for the separable case; the inseparable case, relevant in characteristic 2, is argued for the line version by reference to BCIKS20 App.~C), with guard $\gamma\le1-\sqrt\rho-\eta$, $\eta>0$, $m=\max(\lceil\sqrt\rho/\eta\rceil,3)$. Its admission is an organiser exception, recorded as such, until a refereed version or a complete characteristic-2 proof exists.

**Fix (listing).** `mcaError (RS (F := E) (D.map ι) deg) γ ≤ johnsonA ρ η γ D.card / Fintype.card E`. Also say which generator (lines, or degree-ℓ curves with the factor ℓ−1) the 2^5 fold factor of 03:550 corresponds to. That factor is not in Thm 4.6 for M = 1; the M-term version gives M·(…).

Alternatively, cite BCGM25 (CCC 2026, peer-reviewed, any finite field) as the refereed MCA-to-Johnson theorem. Its n² dependence costs bits, so recompute table 03:542-545 under it.

### M8 (major): the linear-decider discussion contradicts the decider cap
**Where.** 09:218-223: "A linear (Arc/WARP-style) decider at 2^24 costs about 400·2^24 ≈ 6.7×10^9 cycles, so it contributes ≈10^8 after division and dominates. Between /64 and /1024 the ranking … flips only if …. The cap C_dec ≤ 2^32 bounds the decider outright."

**Problem.** 6.7×10^9 > 2^32 ≈ 4.29×10^9, and C_dec is a *weighted* cost, so the excess is larger still. Under the stated cap such a decider is inadmissible at k = 24, and the ranking comparison is moot there. 10-cost.tex:535 says the cap "keeps the /64 from admitting linear deciders [A1-m5]". The two sections disagree on whether Arc/WARP-style accumulation is in the design space at the top class.

**Fix.**
> A linear (Arc/WARP-style) decider at $2^{24}$ would cost about $400\cdot2^{24}\approx6.7\times10^9$ cycles, above the cap $C_{\mathrm{dec}}\le2^{32}$, so it is inadmissible at the top class and admissible but dominant ($\approx C_{\mathrm{dec}}/64$) at $k\le20$. The cap is therefore a design decision against linear deciders at $2^{24}$, not only a bound.

If that is not intended, raise the cap and say so. In both cases, state the position in 03-background (Arc/WARP are presented there as the post-quantum accumulation route).

### M9 (major): what WARP's notion relaxes is misattributed
**Where.**
- 08:138-140: "Versus the book's global extractor [CY Def 31.1.6] (… one polynomial-time extractor seeing all prover strings and no challenges): WARP's notion strictly relaxes it".
- 03:177-180: "WARP states that this strictly relaxes the global-extractor notion of CMS19".

**Evidence.**
- WARP p. 21: "Definition 2.7 is a (strict) relaxation of Definition 2.5 (see Appendix C)". Def 2.5 is the notion "introduced for IOPs in [CMS19] … adapted to IORs [BMNW25b]".
- In CMS19 (Def 8.5) the extractor sees **only the prefix** tr, so it is not a global extractor.
- The CY book's Def 31.1.6 is a *third* notion: one extractor that sees all k prover strings. WARP does not discuss it.
- WARP's App. C (Thm C.1, informal) proves only the implication old ⇒ new. Strictness is asserted in parentheses, and footnote 8 says only that its protocols "are not known to satisfy" Def 2.5.

So the report's taxonomy of "two inequivalent variants" (03:138-140) misses that CMS19 and CY differ, and it attributes a strictness result to WARP that WARP does not prove.

**Fix (03:138-140 and 03:176-181).**
> … comes in (at least) three variants: CMS19's, whose extractor sees the transcript prefix (CMS19 Def.~8.5); the book's, whose single extractor sees all prover strings of the continued execution \cite[Def.~31.1.6]{CY24-Book}; and WARP's per-round backward extractor \cite[Defs.~4.1--4.2]{BCFW25-WARP}. WARP shows that its notion is implied by the CMS19-style notion (adapted to reductions) and states that the relaxation is strict, which is what admits codes without efficient error-tolerant decoders.

**Fix (08:138-141).** Replace "WARP's notion strictly relaxes it" with:
> WARP's notion is implied by the prefix-extractor notion of CMS19 \cite[App.~C]{BCFW25-WARP}; its relation to the book's global extractor is not stated in either source, but WARP's erasure-correction extractor needs the next-round witness and so fits only the backward form.

Also, at 03:179 and 03:762, WARP's wording is "not known to have an efficient **error-tolerant** decoder", not "without efficient decoders".

### M10 (major): brief-review row 10 contradicts DESIGN v0.2/v0.3
**Where.** 05:78: "Field arithmetic in RV64IM unpriced → sig.golf weights, no field precompiles in v1, field fixed by the relation".

**Problem.** DESIGN v0.2 §4 adds Zbc (`clmul`, `clmulh`, `clmulr`), a binary-field multiplication assist, with a separate weight 4. DESIGN v0.3 §15.1 replaces uniform or sig.golf weights by four zkVM profiles plus a latency board. 11:235 calls the v0.2 weights "a display column". DESIGN §11 and 11:380 mention a T1-F `EMUL` board.

**Fix.**
> contract machine RV64IM+Zbc (carry-less multiply as the only field assist, priced separately); v0.3 per-profile zkVM cost vectors (recursion board) and a latency board; no hash or field syscall on T1 (a field-syscall board T1-F is planned); field fixed by the relation (\cref{sec:cost})

Row 9 should also say "18-counter cost vector" rather than imply one scalar.

---

## Minor findings

**03-background.tex**

- **m1 (03:142-149, Def bg-rbrks-cy).** The probability is written only over ρ_j, but the event involves Ext(i,x,Π⃗) on prover oracles sent *after* round j. CY Def 31.1.6 (p. 386) quantifies ∀P̃ and runs the continuation "(Π_j)_{j∈{i+1..k}} ← P̃(aux, ρ_i)". Replace with: "for every (i,x), every malicious prover P̃, every j and every prefix with St(tr‖Π_j)=0, Pr over ρ_j (and the continuation of P̃) […] ≤ κ_j". Also "straight-line" is not in Def 31.1.6. It is the conclusion of Claim 31.1.7 and Thm 31.3.1, so say "a polynomial-time extractor that sees only prover strings (hence straight-line)".
- **m2 (03:166-167).** The (full) law omits the output relation. The security section (08:68-69) has "V(s,tr)=some s′ ∧ (s′,w′)∈R_out ⇒ …". Use the same text, or a reader of 03 will think reductions are not covered.
- **m3 (03:271).** "Grinding … adds bits to individual rounds [CY chs 28–29]" is wrong. The book has no grinding or proof-of-work material: ch. 28 is "Setting parameters", ch. 29 is "Merkle commitment scheme optimizations". Cite only ethSTARK, or a grinding analysis such as CO25-DuplexFS if it covers it. Same error in R7 §1.3 and D1.
- **m4 (03:325).** The prefix is written "domsep ‖ contractId ‖ sizes ‖ MT(Ind(i)) ‖ vk_i ‖ x". DESIGN §5 and S-4 use `domSep ‖ contractId ‖ shapeHash ‖ claimHash ‖ k ‖ MTroot(IDX i) ‖ VK i ‖ x`. Use the same string, or "(abbreviated; see S-4)".
- **m5 (03:383, table).** BCHKS25 Thm 1.3 holds for γ ∈ (δ/3, δ/2 − 1/n), not (δ/3, δ/2), with a ≥ (δ/γ−1)/(δ−2γ). Correct the interval.
- **m6 (03:541, binary table, UD row).** "(γn+1)/|E| [BCIKS20, BCHKS25]": BCIKS20's UD bound is n/q (Thm 1.2/4.1). The (γn+1) form is **BCHKS25 Cor 1.4**, under δ ≥ 3√2/√n and γ < δ/2 − 3/(δn). Cite Cor 1.4 and note that γ = (1−ρ)/2 is the limit, not a point inside the range.
- **m7 (03:393).** KKH26 produces lines with 2^{Ω(1/η)} close *points z*, not "close codewords". Kam26 (arXiv 2604.09724) gives ≥ n^C close points for primes p ≡ 1 mod n at δ = (1−ρ) − Ω(1/log n).
- **m8 (03:404-405).** "We do not reproduce its radius, which we could not confirm". The radius is now confirmed: CS25 conjecture "list-decoding capacity", H_q(δ) ≤ 1−ρ−η, for prime q; the loss against capacity is ≤ 1/log2 q + 1/n. State it.
- **m9 (03:433-434, caption of query table).** "Proven Johnson parameters cost about 1.5–2× the capacity-conjectured queries, and unique decoding 2–4×." From the table, JB/CB is exactly 2× in every row, because bits per query halve, and UD/CB is 2.4–4.4×. Write "exactly 2× … and 2.4–4.4×". The same phrase appears in R7 TL;DR and 08:329.
- **m10 (03:136, 03:209).** Claim 31.1.3 is verified. Note that CY Thm 31.3.1's statement literally says "public-coin **IP**", an apparent typo in the book. No action is needed beyond an exact citation.
- **m11 (03:215, Hol19).** This is verified, but Holmgren's equivalence is asymptotic (negligible errors). Keep "qualitatively" and add "(asymptotically)".
- **m12 (03:233, BGTZ23).** The content is verified. The bib entry is wrong; see m27.
- **m13 (03:634-639, cost table).**
  - The Jolt row has no citation; add the source of "6.8–7.7×10^7 cycles … draft PRs".
  - In observation (3), 6.8–7.7×10^7 / 5.6×10^5 ≈ 120–140×, not "about 100×".
  - "proven (JB, via BCGM25)" for WHIR-JB: BCGM25's RS bound has n²-quality exceptional counts, O(m^7 n²/ρ^{3/2}·Σd_i/|F|). Whether WHIR's published JB parameters at Goldilocks³ (≈192-bit) still hold under that count should be stated or flagged "(parameters as published; not re-derived under BCGM25's constants)".
- **m14 (03:651-652).** "The MCA-to-Johnson conjecture it assumed is a theorem [BCGM25]" is correct, but BCGM25 answers ACFY's question with BCIKS20-quality constants. "Best proven WHIR data point" should be qualified as in m13.
- **m15 (03:496-497, and 09:455).** "An E multiplication … costs 139 cycles with Zbc at weight 4" mixes cycles with weighted cost. D3 says "139 (103 at clmul = 1)". Write "139 weighted units (103 instructions)". In 09:455, "a leanISA step is worth 1–139 RV64IM+Zbc cycles" has the same problem.
- **m16 (03:701).** "Both notions are instances of a reduction of knowledge" follows a sentence about batching and aggregation, so "both" is ambiguous. Write "Accumulation and folding are both instances …".
- **m17 (03:524-526).** Besides M2, "the γn+1 of a unique-decoding proximity step" should cite BCHKS25 Cor 1.4 (see m6).

**08-security.tex**

- **m18 (08:177).** "k ≤ n ≤ 2^14 the number of (message, challenge) round pairs" is garbled. n counts moves and k counts pairs, so write "k ≤ n/2 ≤ 2^13 the number of (message, challenge) pairs, n ≤ 2^14 the number of moves". Check that DESIGN's "rounds ≤ 2^14" means moves (= `n_le`) and say so once.
- **m19 (08:278-279).** "Reducing a 64-bit chunk modulo a 31-bit prime biases each element by about 2^-33" contradicts the report's own formula (03:331-332). The statistical distance is r(p−r)/(p·2^b) ≤ p/2^{b+2} = 2^{31−66} = 2^-35. Write "a statistical distance of up to $2^{-35}$".
- **m20 (08:180-181).** "the bad events coincide" should be "every flip event is a bad event". The reduction needs only inclusion, and the sets are not equal in general.
- **m21 (08:91-93).** "deterministic core of WARP's state-restoration theorem [Claim B.6]" is fine. Add "Thm B.4" so the reader can find the parent theorem.
- **m22 (08:257).** "[CY Def 32.6.4], [WARP Def B.1]" for adaptive choice of (i,x) is verified via A2. Def 32.6.4 is the straight-line holographic SR-knowledge definition; also cite Def 32.4.2 for the adaptive-index soundness game.
- **m23 (08:291-292).** "UD design pays about 1.7× the Johnson-regime design" matches B5/B1 = 8.74/5.26 = 1.66. Note that this holds at ρ = 1/2 only.

**09-recursion.tex**

- **m24 (09:9-11).** The footnote lists "A1 incentives, A2 definitions, A3 feasibility … D1–D3, DESIGN v0.2", but the section cites A4-F1 and DESIGN §15 (v0.3). Update it to "A1–A4 … D1–D4, DESIGN v0.3".
- **m25 (09:93 against 09:171).** "an uncompiled sketch against DESIGN v0.2; the compiled contract is open item O8" contradicts "Review A4 of the compiled v0.2 contract". Say which contract A4 compiled and what is still O8.
- **m26 (09:435-436).** "The best modelled design is about 11 times above that". The best modelled design in the table is B3 (4.8×10^6), which is 8.6× above 5.6×10^5 (r = 30) and 29× above 1.7×10^5 (r = 100). 11× is B1 at r = 30. Write "9–29× (B3) above that". The table entry B5 at r = 100 is log2(1.1×10^9) = 30.0, not 30.1.

**11-benchmark.tex**

- **m27 (11:207).** "ρ=2^-10 needs 64 GiB of oracles at 2^24" comes from A1 (prime field, 4-byte elements). With K = GF(2^64) (8 bytes), 2^34 elements are 128 GiB, and more if E-valued. Write "≈128 GiB".
- **m28 (11:273-276).** "B1 at 2^24 spends 52% of its 5.16 M cycles", but the table gives S_24 = 6.19M for B1. Say that 5.16M is c_24 before the FS, byte and blow-up terms.
- **m29 (11:318-320).**
  - "B2 and B3 … within 1–3% everywhere" is false in the table: the sp1 column has 65.0 vs 61.5 (5.7%), and r0 has 7.66 vs 7.40 (3.5%). Write "within 1–6%".
  - "The optimal rate is log2(1/ρ)=3 under all nine models" cannot be read off the table, which has no ρ = 1/8 row. Add "(ρ = 1/8, not tabulated; D4)".
- **m30 (11:150-155).** "Every family above has a public input that fixes the witness and can be false". This is not argued for the random sparse family, where C is chosen to make one instance satisfiable, or for chains with free inner message blocks. Either restrict the claim to the hash chains or explain why no random index is provably always-satisfiable.
- **m31 (11:254 and table header).** "T0 trivial baseline" collides with track T0 (the Lean-only QProg season, 11:368). Rename the row "trivial baseline (proof = z)" and the column "vs trivial".
- **m32 (11:367).** "UD saturates at about 128 queries, so rate barely matters": per the query table, UD goes 309 → 189 → 155 → 141 from ρ = 1/2 to 1/16. 1/4 → 1/16 is still −25%. Write "UD gains much less from rate than JB (−25% vs −50% from ρ=1/4 to 1/16)".

**04/05**

- **m33 (04:208-212).** In the lessons table, the numbering duplicates "(10)": "(9)–(10) Vacuous theorems …" and "(10) Declared errors", while the enumerated list has (10) = library-level traps and (11) = churn. Renumber: (9) vacuous theorems, (10) library-level traps incl. declared errors.
- **m34 (04:218-219).** "the baseline checks in under 15 min" does not match DESIGN §10 (≈8 min warm, 20–25 min cold). Write "≈8 min warm, 20–25 min cold".
- **m35 (05:52).** "leanerVM records the same gap as an open problem [verifiedzkevm]" cites the EF grants page. Cite the leanerVM repository, as in 03:790-791.
- **m36 (05:38).** "a theorem over every R1CS of every size in a class" is imprecise: certificates are proved at the fixed class shape, and smaller instances are padded (DESIGN §2, 11:157-160). Write "over every R1CS index of the class shape (smaller instances are padded)".

**Bibliography (refs.bib)**

- **m37 BGTZ23.** The entry gives a wrong venue and DOI. DOI 10.1007/978-981-99-8724-5_1 is BGKTTZ23 "Fiat–Shamir Security of FRI and Related SNARKs" (ASIACRYPT 2023). The ePrint 2023/1256 page itself says the publication details were added in error. Correct entry: Block, Garreta, Tiwari, Zając, "On Soundness Notions for Interactive Oracle Proofs", *Journal of Cryptology* 38(1), art. 4, 2025, DOI 10.1007/s00145-024-09520-7, ePrint 2023/1256.
- **m38 CY24-Book.** Drop "[URL unverified]". The URL is https://github.com/hash-based-snargs-book/hash-based-snargs-book. Add "version of 25 March 2026", because the theorem numbers cited are from that version.
- **m39 BCFW25-WARP.** This is correct (TCC 2025, LNCS pp. 369–399, DOI 10.1007/978-3-032-12287-2_13). Add "ePrint version of 2025-05-28" or the version actually used: ePrint lists a 2026-06-18 revision, and appendix numbering (B.4, B.5, B.6, 10.3) may have shifted.
- **m40 CMS19.** Remove any "[number unverified]" note (2019/834 is confirmed); TCC 2019, LNCS pp. 1–29.
- **Optional additions.** BCIKS20 J.ACM 70(5) art. 31 (2023); GG25 ECCC TR25-166; GGSW26 APPROX/RANDOM 2026 (LIPIcs 392, 61); CCHLRRW19 pp. 1082–1090.
- **Also.** The ArkLib KB note under `contract/.lake/packages/Arklib/docs/kb/papers/ABF26.md` says ABF26 has "no ePrint number". That is outdated (2026/680); not a report issue. The citation "ABF26 Def. A.5" in 03:184 is ArkLib's numbering against an April 2026 build. It could not be checked against the July revision, so say "(ArkLib's numbering)".

---

## Verified (no action)

**Chiesa–Yogev book.**
- Def 31.1.1, Def 31.1.2, Claim 31.1.3.
- Thm 31.2.1 (t+k) and Thm 31.3.1 (t+k, straight-line).
- Defs 23.2.2/23.2.3 (SR soundness / straight-line SR knowledge).
- Thm 25.2.1 and 26.1.1, with the 3.5·t²/2^λ simplification under t ≥ 2(log ℓ+1)ℓ (ℓ = sum).
- Thm 32.8.9 (+4ℓ₀²/2^λ, ≤ 4.5t²/2^λ if t ≥ 2ℓ₀ and the ℓ-condition).
- Thm 32.8.10 (holographic knowledge, with the same term), Def 32.4.2 (adversarial index), Thm 14.3.1.
- Ch. 32 formalises the COS transformation; the Fractal IOP itself is not presented, so "formalises it" at 03:76 is slightly loose.

**WARP.**
- Thm 2.8 = informal B.4 with (t+k) and et = Σ et_i.
- FACS remark (Remark 1.1).
- Linear-time accumulation for any linear code with MCA, extraction by erasure correction.
- The bib entry.

**Other primary sources.**
- Holmgren 2019: RBR ⇔ SR for IPs; neither implied by FS-ROM security.
- CMS19 introduced RBR-KS with a prefix extractor; CCHLRRW19 introduced RBR soundness.
- AFK22 (linear in Q); BGTZ23 content.

**Proximity gaps.**
- BCHKS25 Thm 1.5: O(n/η^5), m = max(⌈√ρ/(2η)⌉,3), no characteristic hypothesis, improves BCIKS20 Thm 5.1's n²/η^7.
- BCHKS25: "improved gaps ⇒ improved list decoding" (Thm 1.9); DEEP-ALI and ethSTARK toy-problem attacks (§8, Thm 1.17, Lemma 8.4).
- BCIKS20: UD n/q; Johnson Thm 5.1; any F and D.
- BCGM25 (CCC 2026, all polynomial generators, any finite field).
- Hab25; Jo26 (O(1/n) relative gain, integer rates only); GG25; GGSW26.
- DG25-Dist (rate → 0, radius → 1, CRYPTO 2026); CS25 (three conjectures refuted).
- KKH26 abstract; Kam26.
- Proximity Prize ($1M, rates 1/2–1/16, ε* = 2^-128 "as the example", deadline 2027-12-31).

**Arithmetic.**
- Query table (UD/JB/CB columns).
- Sampler-bias formula r(p−r)/(p·2^b) ≤ p/2^{b+2} and 2^-99 for b = 128.
- BabyBear 2^27, KoalaBear 2^24.
- y³+y+1 irreducible over K (order-7 argument, 2^64 ≡ 2 mod 7).
- The boxed headline inequality, including the max(t,t*) form for all t ≥ 1 with 2k ≤ t ≤ 2^124 (9t ≤ 2^128).
- The tree round count 430,080 ≈ 2^18.7 and 2^-109.3.
- Chain lengths L (399/24/1 and 268/16/1, from rows and columns).
- All "×" ratios in 11's readings except m29.
- The carry and majority identities over GF(2).
- The RBR-KS ⇒ RBR-soundness reduction (08:180-181).

[Agent C items (cost anchors, recursion and FS citations) are appended below.]
