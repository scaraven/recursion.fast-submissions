# `flock-recursive` BLUEPRINT: engineering review (contract, harness, Lean, plan)

Reviewed: `docs/v4/flock-recursive/BLUEPRINT.md` at `30b6999`, with `PLAN.md`, `phase0/*.md`,
`.contract` at `15dac52`, `AGENTS.md`, `submissions/spartan-srom/`, `docs/v4/flock-baseline/`.
Scope: conformance to the contract and the harness, Lean feasibility and budget, the prover plan,
and stage parallelism. The security arguments are another reviewer's. They are touched here only
where they collide with the Lean or the rules.

Probes (in this worktree, `.contract/.lake/packages → logs/pkgs`, every command under `timeout`):

- `logs/blueprint/probe/B8.lean`: the blueprint's own probe, re-run. Clean
  (`B8.rerun.log`, empty).
- `logs/blueprint/probe/BPeng.lean`: new. Clean (`BPeng.log` holds only `time` output), and a
  falsified copy fails as it should. It checks `seq` step costs, `Runs` exactness, the claim's
  rationals, the trace-digest byte offset, and name clashes.
- `logs/blueprint/probe/render.log`: `harness/render-challenge.py` on the blueprint's claim and on
  a fixed claim.
- `logs/blueprint/probe/closure.{py,log}`: the import closure of the Mathlib modules §5.3/§2.1
  need, measured against the badge's precompiled closure.

## Majors (must fix before implementation)

### BP-E-M1. The trace digest's tag byte breaks B-6's 16-byte alignment

§1.2 (l. 119–121) makes every field 16-aligned in `traceBytes`. The node, however, hashes
`0x54 ‖ traceBytes` (`Contract/Signature.lean`, `traceDigest`; `service/PROTOCOL.md` §2.2).
§4.4's T↔H identification (l. 526–531) equates the H block messages with T sub-cubes, so T must
be the *hashed* stream. In the hashed stream every payload and answer sits at 1 mod 16. Probe §(4):
`(tagTrace :: traceBytes [(q8, ans)]).drop 17 |>.take 16 = pay`, and the same at offset 16 is
`≠ pay`.

T can therefore be aligned for H (sub-cube identification) or for M (element reads of F values,
digests and K values), not both. An unaligned 128-bit window is GF(2)-linear in two packed
elements but not F-linear, so M cannot read it with one row.

**Fix.** Make the first query `|q₀| ≡ 7 mod 16` (a 7-byte seed tag) and every later one
`≡ 8 mod 16`, and let T hold `0x54 ‖ traceBytes`. Then every item from the second on starts at
0 mod 16 and its payload and answer are aligned. The seed's payload and answer are aligned too
(probe §(4): with a 7-byte tag the payload is at offset 16 and the answer at 32, and the first item
ends at 64). Restate §1.2's table and l. 119–121.

### BP-E-M2. The T↔H identification is not a pair of sub-cube claims, and T is under-sized 8×

- **Child 2's chain range is misaligned.** Child 2's chain occupies H blocks `[N₁, N₁+N₂)` with
  `N₁ = 20,113` (l. 438), but its T bytes start at element offset `2^17`, i.e. bit `2^24`
  (l. 440, 531).
- **One index map cannot cover both chains.** The maps `i ↦ 512 i` (child 1) and
  `i ↦ 2^24 + 512 (i − N₁)` (child 2) are different, so "the claim is `ẑ(θ_H) = ẑ(θ_T)` at two
  structured points for a random `θ` of `log₂ N_H + 9` coordinates" (l. 529–530) does not exist.
- **A whole power-of-two range does not work either.** Even with T contiguous, a claim over
  `[0, 2^⌈log₂ N_H⌉)` covers the WOTS blocks and the M/T/L/P blocks, whose message bits are not T's
  padding, so the honest witness fails it.
- **The same applies** to the `t̃`/`f̃`/padding claims of §4.2 (l. 418–420).
- **T is under-sized.** l. 440 sizes T as "2 × 2^17 elements = 2 × 2^21 bits = **256** blocks".
  2^17 elements of 128 bits are 2^24 bits, i.e. 1,024 blocks per child. `logs/blueprint/sizes.txt`
  itself prints `T bits 20595456 … blocks 1257`.

**Fix.**
- Split each chain's range into aligned sub-cubes (binary decomposition, at most about 15 per
  child) and make one claim pair per sub-cube. Or add a prefix-indicator sumcheck (`lt`-MLE,
  degree 2).
- Recount B1's claim number and row I1 of §5.2.
- Size T at about 1,260 blocks (2,048 with the `2^17`-element stride). It still fits between bases
  57,344 and 61,440.

### BP-E-M3. The node variants do not cover the tree and the stream, and NN is not sized

- **The variant set is too small.** B-2 has two variants, LL `(L32, L32)` and NN ("both
  children `m = 30`: nodes or stream leaves"). The circuit replays `vprog kindᵢ shapeᵢ variantᵢ`
  of each child (l. 464), a fixed program per child. The runs need at least:
  - in the tree, `(L32, L32)` at level 1, `(N-LL, N-LL)` at level 2 and `(N-NN, N-NN)` above;
  - in the stream, `(L30, L30)` for the first merge, then `(N, L30)` with the child node's own
    variant (`PROVER.md` §3: `node` merges the running proof with the new leaf).
  A node child's program includes `evalM` over *its* variant's matrices (l. 520–524), so the
  parent's circuit depends on the child's variant.
- **Only LL is counted.** §4.5 counts rows for LL children (a leaf's `V`: about 190 k rows per
  child). An NN parent replays a *node's* `V`: `Ã_M, B̃_M, C̃_M` with about 2 × 47 k irregular
  entries × 2 F at `m = 30` (§3.1 l. 339: 2.5·10^5 F per node `V`), the Lr sparse sums, E's
  sumchecks and "two more BLAKE2s walks" (l. 339).
  - Per child that is about 4–5·10^5 rows, `2^19.9` elements per node.
  - That breaks the per-child stride `child·2^17` (l. 499; LL already needs 190 k > 2^17),
    E1's `log₂ N_M ≤ 18` (l. 259) and §8.4's "M-region zerocheck ≤ 2^18 rows" (l. 988).
  - It exceeds K's node budget of `≤ 2^26.2` committed M bits (l. 45), on which the 0.81 s node
    measurement and the 13 % link margin rest.
- **The recursion fixpoint is open.** A node's `V` size depends on its own layout, which depends
  on the `V` it replays.

**Fix.**
- Enumerate the variants the tree and the stream need. Either give each its own `nodeLayout`,
  `vprog` and setup table, or make a node's `V` independent of its children's variants (for
  example an `evalM` whose op structure is uniform across variants).
- Extend `sizes.py` to all variants, with power-of-two template padding and the fixpoint. Re-derive
  E's dimension, §5.2's E rows, the M allotment and the P-side budget, and re-measure the node on
  the 7763 at the real M size before S-E.

### BP-E-M4. The IR's semantics are missing as a theorem, and `queries_le` relies on kernel evaluation of `gen`

- **No refinement theorem.** `V := runIR (vprog …)` (l. 308–316) and `gen` generates every check
  of every phase. `FRSoundnessFinal` (§5.4) needs facts like "the zerocheck round checks held",
  "the Merkle path was consistent" and "the consistency sums held". Getting them from
  `runIR (gen …) = true` takes a refinement theorem, per phase, from the generated op list to the
  protocol's equations. `node_sound` (c) needs the same theorem to identify `runIR` with
  `runSeq (V …)` on the replayed trace, plus the replay lemma that the circuit's tag, length,
  FS-chain and Merkle-half equalities give exactly `V`'s query bytes.
- **It is not in the plan.** §7 has `FRVIR` at 900 lines, holding ops, `runIR`, `semIR`, `gen`
  and counts. Nothing states or budgets the refinement.
- **The analog is large.** leanerVM's version of this layer is #149 (+2,691, "the executable
  verifier's front phases are the oracle verifiers'") and #150 (+2,346, "the compiled verifier
  accepts what the algebra accepts"), and #145 (+5,117) for the replay and query bound.
- **`queries_le` by kernel evaluation is not feasible.** "`queries_le` … by `gen`'s query count …
  (`decide` over the three cases)" (l. 324–326; also S-B, §5.6) asks the kernel to evaluate `gen`
  to a program of 10^5–10^6 ops. §3.1 counts 3.5·10^5 F products in a node's `V`. `decide +kernel`
  costs 59 s/kLoC on small KATs (M §7.1), and this is orders beyond that.

**Fix.**
- Add `FRVIRSpec`: structure `gen` per phase, with one semantic lemma per phase
  (`semIR (genPhase …) st = …`) and query counts as closed-form lemmas (`simp`, no `decide` over
  the full program).
- Alternatively, write `V` as structured Lean, as spartan-srom did, and prove
  `runIR (gen k s v) = V k s v` once, phase by phase.
- Budget it at 3–5 k lines, on the critical path ahead of `FRSoundnessFinal` and `FRNodeCircuit`.

### BP-E-M5. XIR's cost model cannot meet an affine fuel

- **A fixed cap breaks the fuel bound.** XIR's `for` has `cap : Nat`, and "a bound that is
  tape-dependent is still charged at cap" (l. 820, 826–827). The log index (§6.2 step 2) loops
  over `|L|` entries, which is up to about `2^61` on the domain of `Computes`. A fixed cap either
  truncates the index, and `final` then fails for long logs (it quantifies over
  `L.length ≤ logCap`), or charges `2^61 · body`. The second is not `≤ 2^46 + 2^12 t` for small
  `t`.
- **`compile_runs` states an exact count.** It claims
  `Runs tape (compile P) M #[] (cost P t) M′ o` (l. 829–830), but `Runs` is an *exact* step count
  (`Library/Machine.lean`, `Runs := ∀ m ks, exec (n+m) … = exec m …`). A loop whose bound is below
  its cap runs fewer steps (probe §(2): a loop with counter 0 is exactly 1 step).
- **Bad tapes need caps too.** l. 783–787 has the output loops over T items driven by item
  lengths read from the decoded `f⁽⁰⁾`. On a bad tape these are arbitrary words, so every such
  loop must be capped by region constants for `o.length ≤ outCap` to hold on every tape.

**Fix.**
- Let a `for` take `capFn : ℕ → ℕ`, affine in `t`, and a bound register loaded from the tape.
  Prove once that on `extractorInput c π L` the loaded value is `≤ capFn t` (for example
  `|L| ≤ t/5`).
- Make `cost` a function of `t` through `capFn`, and state `compile_runs` as
  `∃ n ≤ cost P t, Runs …`, closed by `run_of_runs` (probe `run_of_runs_le`).
- Cap the T and L output loops by region constants.

### BP-E-M6. The extractor's step count leaves out `seq`/`loop` steps; the fuel is short and the `m = 31` fallback exceeds the budget

- **Every `seq` costs a step.** `XStmt.exec` charges one step per `seq` node (and per `loop`/`ite`
  test). `k` statements in sequence cost `2k − 1` (probe §(1): 2 ops need 3 steps, 8 ops need
  15).
- **An F product costs about twice the blueprint's figure.** §6.3 charges one F product at 48
  statements: three BF64 products, adds, loads. The reduction `y² = y + β` also multiplies `a₁b₁`
  by `β`, a fourth BF64 product unless `β` is chosen cheap. With operand loads and the loop
  counter, an inner-product term is about 40–45 statements, i.e. about **85–95 steps**.
- **Consequences.**
  - Level-0 interpolation is `2^40.1 × ~90 ≈ 2^46.6`, over the declared `fuel_base = 2^46`
    (still under `B = 2^48`).
  - The `m = 31` fallback (FR-R7, l. 806, 1039) becomes `2^42.1 × ~90 ≈ 2^48.6 > 2^48`, so it is
    not available without another decoder.
  - The `Enc` step's "`kᵢ` K×F products per position" also leaves out the per-position
    inverses `1/(D[j] − S[p])`.

**Fix.**
- Count steps on the compiled `XStmt` of `mulF` and of the inner loop (a Lean `cost` lemma of
  the macro), not by hand, and declare `fuel_base` from it (about `2^47.2`).
- Use that `D` is an F₂-span: `D[j] − S[p] = D[j ⊕ p]`, so a single table `invD` (n inverses, one
  batch) replaces every per-position and per-`s` batch inversion.
- Strike the `m = 31` extractor fallback, or price a quasi-linear decoder for it.

### BP-E-M7. Completeness of the SNARK is under-budgeted and partly unplanned; the W kind already gives it at `δ = 0`

- **What the plan requires.** §5.5 makes `P` the Lean PIOP+Ligerito prover for leaves of
  `n ∈ {2^16, 2^18}` and for nodes with SNARK children. That requires:
  - the honest prover, `FRProver` (900 lines);
  - `complete_le` and `δ` (`FRCompleteness`, 800 lines);
  - `node_complete`/`nodeWitness` for every variant (M3);
  - a `compile_complete` theorem (the honest IR run yields satisfying rows), which §4.4/§7 never
    list;
  - computable twins of `Enc` and of every Mathlib object `P` touches, because gate rule 4 needs
    `P` compiled (m6).
- **The analog is larger.** leanerVM's honest prover and its completeness are #147 (+1,654) and
  #148 (+3,292), the latter "given the phases' agreement".
- **The W kind already suffices.** `V` decides the `W` kind exactly as `Rel` (l. 92–97, 312). So
  `P vk c w := .ret (WitnessSending.encode w)` is complete for every witness with `δ = 0`, the
  route spartan-srom took for nodes (D-5, `SpartanSromSubmission.lean` l. 55–59).
- **What the contract still asks.** Honest SNARK proofs passing `acc` is the harness's concrete
  check, not a theorem (`Contract/Security.lean`, completeness section).

**Fix.** Decide explicitly. Either set `P := encode` (claim `"completeness_error": "0"`), delete
`FRProver`/`FRCompleteness` from the certificate path, and keep `node_complete` as an optional
control, or keep SNARK completeness and budget it at leanerVM's scale with `compile_complete`
added. The first removes several thousand lines from the critical path (m9).

### BP-E-M8. Two tracks cannot start from this document: the shared constants and the IR are not normative, and the track order has a cycle

**Missing as values (hex) or tables:**
- `β`, `α` (l. 180–183: "fixed by the Lean module");
- the subspace basis of `D` (l. 187–189: "the exact list is a Lean constant");
- the GF(2^8) embedding and the skip sets `Λ`, `S_skip` (l. 292: "on the F₂-subfield points",
  which cannot be 64 points);
- `ρ₁…ρ₇` (l. 293);
- the element order of a column inside a Merkle leaf;
- the K coordinate-split bit (l. 199–201);
- `piSize` offsets (l. 114: "≈");
- the IR's op set, semantics and dump format (l. 320–322 ends with "`...`").

P (`field.rs`, `ntt.rs`, `ir.rs`, "line for line the Lean `gen`", l. 934) and L-field, L-piop and
L-circ each need these from day one.

**Other gaps:**
- `reassemble` is called "a fixed byte map" (l. 164–165). It is not: which half of a Merkle-node
  query is the sibling depends on the position bits, which come from squeeze answers. L-circ and
  L-ext both implement it, so it must be one shared definition.
- §7 (l. 870–873) says everything imports `FRVIR`, "L-circ's first module". But `FRVIR` depends on
  L-cert's `FRTranscript` (l. 899), and `gen` encodes every phase of L-piop and L-pcs at op level.
  So S-B is the whole verifier and gates every track.

**Fix.**
- Add a normative appendix: constants in hex with their certificates, the op table (name,
  operands, semantics, query effect, row cost), the per-phase challenge-to-answer map, the byte
  layout with exact offsets, and `reassemble`'s definition.
- Make `FRTranscript` + `FRFormat` + `FRVIR` (+ M4's spec) an "S-0 interfaces" stage owned by one
  implementer, before the tracks fork.

## Minors

- **BP-E-m1 (claim file).**
  - `"completeness_error": "1/2^100"` (l. 920–921) is refused by `render-challenge.py`
    (`render.log`): rationals are decimal `a/b`.
  - B-10's "declared as `1/2^120 · (2^-0.2)` rounded" mixes an irrational with its rational
    bound. Declare `S.ε := 15/2^124` and the claim `"15/21267647932558653966460912964485513216"`.
    The probe proves `epsR = 2⁻¹^120 − 2⁻¹^124` and `epsR ≤ errorCap` by `norm_num`.
  - With M7, `δ = "0"`.
- **BP-E-m2 (counts disagree).**
  - §1.2 gives `m = 32` 8,810 items and 7,924 siblings (l. 146). §0 gives 7,850 (l. 36), and
    `sizes.txt` gives 7,843 items and `Σ tᵢ(depthᵢ − capᵢ) = 6,922` siblings. 8,810 would exceed
    `qV = 8,192`.
  - §1.1's siblings row "5,934 → 110,592" and the columns figure 477,440 (the formula gives
    413,440) do not follow from the stated formulas.
  - §5.6's negative control "`qV − 1` not certified" (l. 713) is false unless `qV` equals the
    exact maximum. Set `qV` from the `queries_le` theorem, or make the control the exact
    count − 1.
- **BP-E-m3 (W-branch cost claims).**
  - "≈ 170 ms" for a `W` leaf of `2^20` steps (l. 96–97) uses `compressF`. `V` would run the
    contract's list-based chain, measured at 0.79 s for `2^20` steps on the VM
    (`flock-baseline/stages/F1-lean-RESULT.md` l. 368).
  - Nested `W` nodes multiply this, as in F1-M2, so "no branch is costlier than the honest run"
    (l. 353–354) is false.
  - The cap of D-6 is unavailable here (no SNARK leaf covers general `n`), but the exposure is
    small. The harness's DoS inputs carry no valid signature (`rfh/checks.py` `dos_inputs`). A
    run's keys die with its service. The native prover never signs an empty trace. Only the
    entrant's own prover could build such proofs, during the run.
  - Fix: state that argument, use a fast chain twin, and budget a byte-level `W` reader
    (spartan-srom `NodeBytes`, 180 lines).
- **BP-E-m4 (`T_V` estimate).** §3.2 prices the root's trace digest at `compressF` speed
  (2.8 ms). The compiled `acc` runs the contract's spec BLAKE2s over a materialised
  `List UInt8` of 1.12 MB, about 0.75 µs per compression on the VM (above), so about 15–25 ms on
  a runner. This is still within `T_V`. Run an early interpreter probe on a synthetic NN-size
  program after S-B instead of waiting for H1.
- **BP-E-m5 (controls that cannot run).**
  - "`ext` on a toy tape … `decide +kernel`" (l. 714) cannot run as stated. `XProg.run` allocates
    `Array.replicate (memFor t) 0` with `mem = 2^26` before the first statement. Parametrise the
    layout and memory and control a small instance, or control at `semXIR`.
  - "`ε = 2^-121` is not certified" (l. 713) is a non-existence theorem over all potentials, not
    a toy control. Replace it with "this `μ`'s step fails at `2^-121` on phase Z2".
  - Missing controls: `reassemble`/`readSigned`, `nodeLayout`, `tpl_mle`/`shift_mle`/`eq_incr`,
    `gen` (M4).
- **BP-E-m6 (statement shapes).**
  - `mca_ud_line` (l. 605–609) takes F-valued `u₀, u₁` and `C_F`. Fold rounds 2…ℓᵢ of a level act
    on K-valued words, so `fold_preserves` (l. 646–648) needs it over K-valued inputs. State it
    over K, with the F case as a corollary.
  - `Enc` is Mathlib's `Lagrange.interpolate`, which is `noncomputable`
    (`Mathlib/LinearAlgebra/Lagrange.lean` l. 134). `V`'s final-level evaluation (l. 277–279)
    needs a computable barycentric twin proved equal, budgeted in `FRRS`.
- **BP-E-m7 (names and DAG).**
  - `readSigned` and `readWit` (l. 480–485, 676) are contract names (`Extractor.lean`).
    Prefix them.
  - `node_sound` must state `acc` through a restated `accWith` (AGENTS.md: `Submission.acc` takes
    the submission). Otherwise `FRNodeCircuit` imports `FRSubmission`, which imports everything.
    Add the edge `FRNodeCircuit → FRVerifier` (for `accWith` and `runSeq_eq_runIR`) to §7's
    table.
- **BP-E-m8 (build plan).**
  - Five modules of 1,500–2,000 lines (`FRSoundnessStep`, `FRVIRCircuit`, `FRNodeCircuit`,
    `FRXDecode`, `FRProximity`) elaborate serially.
  - The critical path through §7's table (Field → Transcript → Merkle → Log → Soundness* → Final,
    joined by the L-circ chain at `FRSoundnessFinal`) is about 10 k lines. At about 30 CPU-s/kLoC
    on a runner (spartan-srom: 690 s user for 17.9 k on the VM, ÷ 1.28) that is about 300 s
    before contention.
  - With M4, M7 (if kept) and m3 the total is plausibly 45–50 k lines, i.e. a build of about
    450–500 s, inside 600 s but under M §7.1's 1.5× margin.
  - Fix: split modules to ≤ 800 lines, move FR-R4′'s VM measurement to the end of S-E, and log
    per-module times from S-A on.
- **BP-E-m9 (source rule vocabulary).** The raw scan rejects the whole words `partial`, `syntax`,
  `macro`, `elab`, `[init`/`, init`, `, export`, in comments and strings too
  (`scripts/source-rule.py`). The blueprint's "macros" and "partials" are safe only in the plural,
  and "partial sums" or "partial products" in a sumcheck docstring fail. Add a vocabulary note to
  §7.
- **BP-E-m10 (`progCap` and the cost proof).** "≈ 4–6 k statements" (l. 807–808) leaves out the
  macro expansion (about 40 statements per `mulF` use). `ext_halts` "by `norm_num` on the
  syntactic cost" and `body.size ≤ progCap` would unfold the whole compiled term. Prove
  `size (compile P) = sizeIR P` and per-phase `cost` lemmas.
- **BP-E-m11 (prover details).**
  - The Lean `gen` dump for the Rust KAT (l. 934, 1004) needs evaluation, which the source rule
    forbids in the entry. Name a dev-only tool outside `submissions/`, and dump every variant (M3),
    not "three shapes".
  - Service caps: a level-0 tree of an `m = 32` leaf sends about 1 GiB of column queries. With
    `QUERY` at ≤ 2^18 items and ≤ 2^24 B per request, that is at least 65 requests. State the
    connection plan (≤ 32; one per thread).

## Checked, no finding

- **Contract shapes match.** `Submission` fields and types, `acc` (conjunct order), `Rel`,
  `KState`/`KS`, `Computes`, `extractorInput`, `decodeWit`, `outCap` (a node witness is about
  `2^18.9` words with the corrected counts), `extractorBudget`, `CertificateR.bounds`,
  `failProb`.
- **B-8's `E`** typechecks with `Computes` following from halting and the output cap (B8 re-run).
- **The fuel shape is within budget** (`fuel_le`). The fixed rationals pass `CertificateR`'s
  `bounds`, and `epsR ≤ errorCap` and `deltaR ≤ completenessCap` are proved (`BPeng.lean`).
- **Imports.**
  - CompPoly's `Ext` framework is in the allowlist: `BF64/Ext3.lean` imports
    `CompPoly.Fields.Extension`. Its `Field` instance is computable (Fermat inverse) given
    `Finite`, `Fact (Nat.card F = q)` and irreducibility. This needs an `ExtensionParams` over an
    `Ext` base for K, so check those instances early in S-A.
  - RatFunc, `Matrix.Rank`, Lagrange, `Matrix.Polynomial` and `Adjugate` add **0** modules
    beyond the badge's precompiled closure (`closure.log`; `Mathlib.Tactic`'s closure is 8,913
    modules), so the badge's 180 s is not at risk from §5.3's imports.
- **Prover toolchain and runtime.** std Rust to one `.s` with CPUID dispatch, `-C
  target-cpu=x86-64-v2` and `#[target_feature]` kernels, the binutils 2.42 path (spartan-srom
  precedent), the arena within 11 GiB, start-up inside `stream_s`, and the tree-time arithmetic
  of §8.4 (64 × 4.24–4.58 + 63 × 0.94–1.10 s) as quoted from K.

## Verdict

**Not ready as the normative document for parallel implementation.** The architecture survives:
B-1, the IR-plus-compiled-circuit idea, B-8's `E`, the prover plan and the Lean budget order of
magnitude. Eight things need a revision pass first:
- two byte/bit layout errors that the node circuit cannot be built around (M1, M2);
- the variant set and the NN sizing, which drive the circuit, `E`'s dimension and the stream
  margin (M3);
- two unbudgeted research-grade layers (M4, and M7 unless `P := encode`);
- two errors in the extractor's machine model (M5, M6);
- missing normative interfaces (M8).

Re-run `sizes.py` with M2/M3's corrections before re-reviewing.
