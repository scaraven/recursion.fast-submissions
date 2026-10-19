# Baseline task: v3 stage S2, the witness-sending argument

This brief is for the agent that builds the v3 baseline, the first entry of this repository. It
is self-contained, but it cites the design (`docs/design/DESIGN-v3.md`, cited as §n) for every
rule. Read `../../AGENTS.md` (the submitter's rules) first, then this file.

Sources: design §7.3 (the baseline), §11 S2 (the stage), V3-9 (the decision), §7.4 (the library
field), §7.7 (where it lives), §3.2 and §4 (the obligations), §6.3 and §6.5 (what the harness runs
and why the baseline is unranked).

---

## 0. The task in one paragraph

Build the witness-sending argument as a certified v3 submission.

- **`V`.** `V c π` decodes `π` as a witness `Wit` and decides `Rel` directly, with zero oracle
  queries. In the node case it runs the verifier on the two child proofs recursively, so the root
  proof contains every chain start.
- **`P`, `E` and the image.** `P` serialises the witness, `E` deserialises it, and the extractor
  image copies its input to its output.
- **The obligations.** `KS` holds with `good := True`, `bad := False`, `ε := 0` and `qV := 0`.
  `Complete` holds for every oracle, by unfolding the decoder on the serialised witness.
  `ImageComputes` is a copy loop with a linear step count.

It must be certified, pass the comparator, the gate and the badge path, and prove the smoke tree.
It is **listed, unranked**, because at the ranked size its root check recomputes `2^8 · 2^14`
Blake2s compressions. That takes about 25 s by the design's numbers (§6.5), against the
succinctness cap `T_V = 2 s`. The exclusion is a measurement, not a theorem, and that measurement
is what calibrates `T_V` (§7.3).

## 1. Status and dependencies (2026-10-19)

| Dependency | State | What S2 does about it |
|---|---|---|
| **S1, the v3 contract** (`Oracle`, `Relation`, `Security`, `Extractor`, `Tree`, `Certificate`) | In review on the core's branch `v3/s1-contract`. The branch's committed head `5ad2115` holds the v3 **documents** only. The Lean contract was being written, uncommitted, in the core's working tree. The branch is **not on the remote**: `git ls-remote` shows only `main` (`77e550b`). | S2 starts when S1's contract is committed. Every Lean name in this brief comes from the design's sketches. Check each against `RecursionFast/Contract/*.lean` at the S1 commit, and record every difference in the RESULT. |
| **The `.contract` pin** | Pinned to the core's `main`, `77e550b` (v2). | Move it to the S1 commit (§8.1 below) in its own commit. Before this repository is pushed anywhere, the pinned commit must be reachable on the core's remote, or `git submodule update` fails for everyone else. |
| **S3, the v3 harness** (tree generator, `treeRoot` known-answer test, prover interface, succinctness cap, sample checks, liveness with `prove-lean` and the emulator, gate rule 4's fields, CI) | Not built. | S2 runs the **proof half** with the core's existing `scripts/harness.sh` (comparator, then the gate) on a v3 challenge. It also writes its own local smoke script for the tree, the canaries and the root-check timing (§9). The badge executables and the runner are S3's. The RESULT says what ran under which harness. |
| **The v3 challenge stub** (`RecursionFast/Challenge/*.lean.in`) | v2 stubs only (`L.lean.in`, `R.lean.in`), and they name v2 types. | Use the stub from S1 if it has one. Otherwise write a minimal v3 stub in the core-side pull request (§2): the rendered `declared` with the image, then `submission : Submission := sorry` and `certified : Certificate … := sorry`. S3 takes it over. |
| **S7, the intake** | Not built. `records.json` is empty. | Nothing. The baseline's root layout must fit what S7 will fix, so keep it flat (`../../submissions/README.md`). |

## 2. Where the work goes: two halves

1. **This repository: the entry.** `submissions/baseline/`, a flat root (§3 below). Also the
   stage's records: `docs/stages/V3-S2-RESULT.md`, `docs/reviews/V3-S2-review.md` and
   `docs/reviews/V3-S2-golf.md`. This mirrors the core's naming; the in-progress S1 used
   `docs/stages/V3-S1-RESULT.md` in the core's working tree.
2. **The core: a separate pull request**, following §11 S2 and §10. Check first what S1 has
   already done for each item: the in-progress S1 was moving v2-only files to `legacy/v2/`.
   - **The library field.** CompPoly's `BF64` and `Ext3` replace `Field.lean` in the library
     (§7.4). v2's `Contract/Field.lean` and `Library/Field.lean` are deleted, and their facts are
     imported from CompPoly. Check first what S1 already did: S1 deletes `Contract/Field.lean`
     (§11 S1).
   - **Regenerate the import allowlist and the olean manifest.** The allowlist comes from
     `gate --closure` inside `scripts/org-build.sh`, and the manifest from
     `scripts/olean-manifest.py gen` on a clean organiser build (`docs/core/harness-README.md`, "The
     olean manifest").
   - **Remove the v2 baseline from the core.** `submissions/baseline/` and the
     `RecursionFastCandidate` `[[lean_lib]]` block of `lakefile.toml` move here (§10: "moves to the
     submissions repository as its first entry").
   - **The v3 stub**, if S1 has none (§1 above).

   The core's `CLAUDE.md` governs that pull request (`docs/core/core-CLAUDE.md`). Never edit the
   core's working tree at `/home/devops/Verified-zkEVM/recursion.fast` while another agent works
   there. Use a fresh clone or a worktree on a new branch.

The baseline itself needs no field: it computes only Blake2s. `BF64` matters to S2 only through
the library and the allowlist.

## 3. The entry's files (`submissions/baseline/`, flat)

Proposed names. Any fresh module names work (`../../submissions/README.md` rule 4).

| File | What |
|---|---|
| `BaselineV3Format.lean` | the proof format: `ser : Wit → ByteArray`, `decode : ByteArray → Option Wit`, the round trip, strictness and size lemmas |
| `BaselineV3Verifier.lean` | `vcore`, `V`, `P`, `E` and the key lemma (§4.2) |
| `BaselineV3Extractor.lean` | the image literal (or its packed form), `fuel`, and the proof of `ImageComputes` |
| `BaselineV3Security.lean` | the `KState`, `KS`, `Complete`, the caps, and `submission` and `certificate` |
| `BaselineV3Negative.lean` | negative controls (§6 below) |
| `BaselineV3.lean` | the library root, which imports the above |
| `Solution.lean` | the solution module: the rendered challenge with its placeholders filled, generated by `make-solution.py` (the v2 name was `BaselineSolution`; S3 fixes the v3 one) |
| `claim.json` | the claim (v2 schema in `../../AGENTS.md` §8; S3 fixes v3's) |
| `extractor.S`, `build-extractor.sh`, `extractor.bin`, `extractor.data` | the image: source, build script and the two files the claim names |
| `prover.py` (or `Cargo.toml`, `main.rs`) | the native prover (§9.1 below) |
| `make-solution.py`, `check.sh`, `check-hygiene.sh`, `Axioms.lean`, `smoke.py` | the entry's checks (§9 below) |
| `comparator.json`, `comparator-nanoda.json` | the comparator configurations (v2's shape, §7 below) |
| `README.md` | the worked example for a submitter, as v2's README was: every certificate field, what the baseline puts there, and who checks it |
| `NOTES.md` | the journal (§7.7) |

## 4. The construction

The definitions below are sketches, written against the design's names.

### 4.1 Proof format: an injective, strict, unbounded serialisation of `Wit`

```
ser (leaf s n)           = 0x00 ‖ s (32 bytes) ‖ nat n
ser (node c₁ c₂ π₁ π₂)   = 0x01 ‖ c₁ ‖ c₂ ‖ nat |π₁| ‖ π₁ ‖ nat |π₂| ‖ π₂
nat                      = minimal unsigned LEB128 (the last byte < 0x80; no superfluous 0x80 bytes)
```

The serialisation is one level deep: a node's witness contains its children's proofs as opaque
bytes. The recursion is in `V`, not in the format. Requirements:

- **Unbounded `n` and lengths.** `Wit.leaf` has `n : ℕ` and the proofs are `ByteArray`s of any
  size. `Complete` quantifies over every witness of `Rel` (§4.3), so a fixed 8-byte field would make
  completeness false for `n ≥ 2^64`. `enc64` appears only inside `leafStmt`, which the contract
  computes, and you call it as it is.
- **Strict.** `decode π = some w → ser w = π`: no trailing bytes, no non-minimal numbers, nothing
  missing. The canaries append one byte and remove the last byte (§6.3 step 7), and strictness
  rejects both. The image (§4.5) may also depend on strictness.
- **If S1 exposes a computable witness serialisation** (for the extractor's output, §4.4), use it
  as the proof format, provided it is injective on `n` and on the lengths. Then the extractor's
  output can be the proof bytes themselves (§4.5). If it truncates (for example, `n` as 8 bytes),
  keep your own format, have the image translate, and report the truncation to the orchestrator.

The proof sizes of this format follow from the arithmetic. A leaf proof at `n = 2^14` is 36
bytes. A node proof at level `k` is `65 + 2·|nat(size_{k−1})| + 2·size_{k−1}`. So the root proof
is 339 bytes at `r = 2`, `n = 16`, and 26,555 bytes at `r = 8`, `n = 2^14`, far below `proofCap`
= 1 MiB (computed, not measured).

### 4.2 `V`: decide `Rel` on the decoded witness, zero queries

```lean
/-- Decides `Rel S.Vb c w` for the decoded `w`; `fuel ≥ π.size` suffices. -/
def vcore : ℕ → Digest → Proof → Bool
  | 0,     _, _ => false
  | f + 1, c, π => match decode π with
    | some (.leaf s n)          => c == leafStmt (chainEnd s n) n
    | some (.node c₁ c₂ π₁ π₂) =>
        c == nodeStmt c₁ c₂ && (π₁.size ≤ proofCap && vcore f c₁ π₁)
                            && (π₂.size ≤ proofCap && vcore f c₂ π₂)
    | none                      => false

def V (c : Digest) (π : Proof) : OProg Bool := .ret (vcore (π.size + 1) c π)
```

- **The child cap is part of `Rel`.** Rel's node case is `Vb c₁ π₁ = true`, and `Submission.Vb`
  rejects proofs above `proofCap` (§3.2). So `V` must check `π₁.size ≤ proofCap` itself. Without
  that check, the key lemma is false.
- **Recursion.** Structural recursion on an explicit fuel, as above, keeps the definition simple
  for the kernel and compiles to a loop. Well-founded recursion on `π.size` with `termination_by`
  also works, if you prove `π₁.size < π.size` from `decode`. `partial` is refused (gate rule 2,
  source rule). Prove that the result does not depend on the fuel once `fuel > π.size`.
- **Use the contract's own definitions** (`leafStmt`, `chainEnd`, `nodeStmt`) and its equality on
  `Digest`. Then the key lemma is unfolding, not a re-proof of Blake2s facts. Make the equality
  test executable and cheap: `Digest = Fin 32 → UInt8` has decidable equality through Mathlib's
  finite-function instance, or you can compare the 32 bytes. Kernel proofs never evaluate
  `chainEnd`; they reason about it.
- **Zero oracle queries.** `V` is `.ret`, so `tagRO` and the oracle play no part.
- **The key lemma** (the analogue of v2's `triv_accepts_iff`):
  `Submission.Vb S c π = true ↔ π.size ≤ proofCap ∧ ∃ w, decode π = some w ∧ Rel S.Vb c w`.

### 4.3 `P`: serialise

`P c w := .ret (ser w)`. Completeness follows from `decode (ser w) = some w` and unfolding `vcore`.
The node case uses the hypothesis `Vb c₁ π₁ = true` from `Rel`, which already contains the cap
check and `vcore` on the child (§4.2). This is what the design calls "`rfl` on the decoder", with
the round trip proved once.

### 4.4 `E`: deserialise

`E c π L := decode π`. It ignores `c` and `L`.

### 4.5 `img` and `fuel`: reconcile with S1's `ImageComputes` first

The design's sketch (§4.4) says: on the input tape `⟦c, |π|, π, |L|, L⟧` (bytes), the image halts
within `fuel |π| |L|` steps with **the serialisation of `E c π L`, or the empty output for
`none`**, for every `c`, every `π ≤ proofCap` and every `L` with at most `2^24` entries. Read S1's
`Extractor.lean` before writing the image. The following is this brief's analysis, not the
design's:

- **The case the design's sentence glosses.** "`img` copies its input to its output" (§7.3) is
  right whenever `π` decodes, because a strict `decode` gives `ser (decode π) = π`. For a `π`
  that does not decode, `E` returns `none` and the required output is empty. A pure copy outputs
  `π` instead.
- **If S1 compares outputs byte for byte with the empty output for `none`,** the image must
  validate the format and output nothing on failure. Validation is a linear scan: the tag, 32 or
  64 bytes, LEB128 lengths, the exact end. The copy (or in-place output) happens only on success.
  It is still linear, and still within `B p l = 2^40 + 2^8·(p + l)` with a wide margin.
- **If S1 states it through a contract decoder of the output** (as v2's `toExtractor` did with
  `decTables`), a pure copy works, provided the proof format is the contract's serialisation.
- **The output convention.** In v2, `HALT` returned `a1` doublewords from address `a0`. The
  baseline's 8-instruction `firstMsgImg` used that to output in place with constant fuel
  (`docs/baseline/v2-example/extractor/extractor.S`). If S1 keeps a range-returning `HALT` and
  `π` sits suitably aligned in the tape, in-place output may avoid the copy loop. Otherwise, use a
  byte copy loop.
- **What to prove.** A loop invariant on the vendored machine for the scan and copy, with a step
  count linear in `|π|`, and a tight `fuel` with a control that one step less fails (v2:
  `trivExtractor_fuel_tight`). The helpers are the core library's machine lemmas: v2's
  `Library/Extractor.lean` (`run_firstMsgImage`, `firstMsg_extractMid`) and whatever S1 keeps.
  This proof is the largest piece of S2. A verified decoder image is an organiser asset that does
  not exist yet (O-15 (2)).
- **The certificate binds the image** to the claim's files (`S.img = D.img`, §3.2). Render the
  image literal in the packed form the renderer emits. A naive `rfl` against a large image is
  expensive (v0.3 measured 80 s and 9 GB per word lookup in a 1 MiB image), but this image is
  small.

### 4.6 `ε`, `qV`, `fuel`, `cap`

`ε := 0`, `qV := 0`, and `fuel p l := a + b · p` from §4.5, with `a` and `b` as proved. The cap is
`0 ≤ errorCap ∧ 0 ≤ 2^16 ∧ ∀ p l, fuel p l ≤ B p l`.

## 5. The obligations, as the certificate's fields

These are the names of the design's sketches (§3.2, §4.2–4.4). The real field names are in the
core's `RecursionFast/Contract/*.lean` on branch `v3/s1-contract` once S1 is merged. Check them
there, and record every difference.

```lean
structure Certificate (S : Submission) : Prop where
  secure   : KS (Rel S.Vb) S.V S.E S.ε S.qV
  complete : Complete (Rel S.Vb) S.P S.V
  computes : ImageComputes S.img S.E S.fuel
  cap      : S.ε ≤ errorCap ∧ S.qV ≤ 2^16 ∧ ∀ p l, S.fuel p l ≤ B p l
-- plus the image binding `S.img = D.img` against the rendered `Declared` (§3.2)
```

| Field | Baseline discharge |
|---|---|
| `secure.1`: `∃ k : KState R V E, k.Bounded ε` | `good := fun _ => True`, `bad := fun _ _ _ => False`. `empty` and `step` are trivial. For `final`, `V c π = .ret b`, so `runLog L` gives `some b`, and `b = true` gives, by the key lemma, `E c π L = decode π = some w` with `Rel S.Vb c w`. `Bounded 0` holds because `Nat.card {a // False} = 0`. The design's vacuity controls name exactly this `KState` as the positive control (§4.2). Look in S1's `Controls/Security.lean` for it, and copy rather than import it: by convention a submission imports only the contract and the library. |
| `secure.2`: `∀ H c π, ((V c π).queries H).length ≤ qV` | `queries` of `.ret` is `[]`, and `0 ≤ 0`. |
| `complete` | §4.3. |
| `computes` | §4.5. |
| `cap` | §4.6. |
| the image binding | `rfl` against the rendered literal. The v2 solution was `⟨⟨rfl, rfl⟩, rfl⟩` (`docs/baseline/v2-example/scripts/make-solution.py`). |

Everything on the badge path must have compiled code: `V`, `P`, `E` and `img` (gate rule 4, §7.6).
If `submission` compiles as a whole, rule 4 passes outright, as v2's did. If `ε` or a proof term
makes it noncomputable, mark it `noncomputable def` and check that every badge field still
compiles.

## 6. Controls to write

Each definition the entry relies on gets a positive and a negative control (the workspace's
convention, which v2's baseline followed with `split0_not_secure`):

- **Format.** The round trip on a leaf and a node with known bytes (positive). `decode` rejects
  one appended byte, one removed byte, a non-minimal LEB128 and an unknown tag (negative).
- **Verifier.** It accepts the honest smoke-tree proofs (positive; a kernel-checked instance
  would evaluate Blake2s, so keep it to `n` = 1 or 2 if done in the kernel at all). It rejects a
  flipped statement bit, swapped children and a child above `proofCap` (negative).
- **Extractor.** `fuel − 1` fails `ImageComputes` on one small tape (negative, as v2's
  `trivExtractor_fuel_tight`).
- **Claim.** One image bit flipped, and the certificate no longer elaborates against the rendered
  challenge (negative, as v2's `check.sh` "negative claims").

## 7. The worked example: the v2 baseline (`docs/baseline/v2-example/`)

v2's `P_triv` is the template for how an entry is laid out, certified and checked. Its README §3
and §4 are the best explanation of who checks what.

**Copy:**

- **The `scripts/check.sh` flow:**
  1. reassemble the image byte for byte when `riscv64-unknown-elf-as` is installed;
  2. hygiene;
  3. build;
  4. render the challenge from `claim.json` with the core's `scripts/render-challenge.py`;
  5. `make-solution.py`;
  6. elaborate the challenge, which must have exactly its `sorry` placeholders, and the solution;
  7. the axiom audit (`Axioms.lean`, `#print axioms` of every theorem; only the three axioms
     pass);
  8. `leanchecker` on the solution's closure;
  9. negative claims;
  10. `loc.py`;
  11. with `HARNESS=1`, the production harness, which must print `HARNESS: ACCEPT`.
- **The claim rendering.** `make-solution.py` replaces the placeholders and asserts that no
  `sorry` remains.
- **The comparator configuration.** `challenge_module`, `solution_module`, `theorem_names`
  (`…certified`), `definition_names` (`…submission`), `permitted_axioms` (the three) and
  `enable_nanoda`.
- **The README structure.** The field-by-field table, the "who checks what" table, and a
  measurements table with log paths.
- **The prover README's structure:** the interface, the byte grammar and reference
  implementations.

**What changes in v3:**

- **No organiser compiler.** There are no layouts, no keys (`VK`, `IDX`), no index, no class `k`,
  no Merkle arity and no tape grammar (§10).
- **Statements are 32-byte digests**, not 32 field elements (§2).
- **Security is a `KState` over query logs**, not a `KSF` over rounds. Completeness is over every
  oracle `H` (§4).
- **The extractor.** `ImageComputes` with the budget `B p l` replaces the definitional
  `toExtractor` with `B(k)` (§4.4).
- **The prover interface** is `tree` and `node` over digests and starts, not `leaf` and `node`
  over `layout.json` and `vkc.bin` (§6.3).
- **The v3 baseline runs.** It has a native prover and goes through the badge path and the
  benchmark. v2's could not run at all (`triv_narg`). Its exclusion is now a measurement (§7.3).
- **The root is flat** and lives in this repository, not in the core's lakefile (§7.7).

## 8. Build setup

### 8.1 The core at the pin (`.contract`)

```sh
git submodule update --init                          # .contract at the pinned commit
# moving the pin to the S1 commit, while v3/s1-contract is not on the remote:
git -C .contract fetch /home/devops/Verified-zkEVM/recursion.fast v3/s1-contract
git -C .contract checkout <S1 commit>                # then: git add .contract && git commit
# once the branch or main has it: git -C .contract fetch origin && git -C .contract checkout <commit>
```

Then the core's fresh-clone set-up (`docs/core/core-CLAUDE.md`, "Toolchain"; measured in v2's S9
fix pass):

```sh
cd .contract
scripts/setup-clean.sh /home/devops/Verified-zkEVM/recursion.fast/ext/Clean   # offline; or no argument to clone upstream
mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages
lake build                                           # default targets
scripts/org-build.sh .lake/org                       # the organiser package the harness requires
python3 -I scripts/olean-manifest.py check --org .lake/org scripts/olean-manifest.sha256
```

- **The shared package tree** (`…/contract/.lake/packages`) is prebuilt and shared read-only.
  Never run `lake update` or `lake exe cache get` against it. The lake manifest at the pin must
  match it. At `77e550b` it does: every git package's revision equals the shared tree's `HEAD`,
  checked on 2026-10-19. Re-check after moving the pin:

  ```sh
  python3 -I -c "import json;[print(p['name'],p.get('rev')) for p in json.load(open('lake-manifest.json'))['packages']]"
  ```

  Away from this machine, `lake exe cache get` supplies Mathlib only, and CompPoly's cone and
  Clean are then built.
- **The external tools.** The comparator and nanoda are external: `COMPARATOR_HOME` and
  `COMPARATOR_NANODA`, with defaults and pins in `docs/core/tools.env` (comparator `d03acab` with
  lean4export `076e8e5`, nanoda `3a24072`).
- **What these steps write.** They write only gitignored paths inside the submodule (`ext/`,
  `.lake/`). Keep its tracked files clean: the pin is a commit, not a working tree.

### 8.2 Building the entry

Not tested in this repository: no v3 contract existed when this brief was written. Two routes,
both used in v2:

- **One module at a time, from the pinned core**, as v2's `check.sh` built the solution. This
  changes nothing in `.contract`:

  ```sh
  OUT=$(mktemp -d); cd .contract
  LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean -o $OUT/BaselineV3Format.olean ../submissions/baseline/BaselineV3Format.lean
  # … each module in import order, the same LEAN_PATH …
  ```

- **A scratch clone of the core with a `[[lean_lib]]` for the entry**, as v2's
  `RecursionFastCandidate` was (`srcDir` pointing at a symbolic link to `submissions/baseline`).
  Use it for iteration and for a local `[[lean_exe]]` that runs the compiled `Submission.Vb` for
  the smoke tree and the timing (§9). Never run `org-build.sh` in that clone: its organiser package
  would contain the entry. Build the organiser package in the clean `.contract` (§8.1).

## 9. Commands: checks and the harness

The v3 harness is stage S3 and does not exist yet. The commands below are v2's, from
`docs/core/core-CLAUDE.md` and `docs/core/harness-README.md`, and they show the shape. Run them
from `.contract` at the S1 pin.

```sh
# render the challenge and make the solution (v2 shape; the v3 stub's name is S1's or S3's)
python3 -I scripts/render-challenge.py RecursionFast/Challenge/<STUB>.lean.in ../submissions/baseline/claim.json CHALLENGE.lean
python3 -I ../submissions/baseline/make-solution.py CHALLENGE.lean ../submissions/baseline/Solution.lean

# the production harness, proof half: source rule, comparator (Lean kernel + nanoda), gate
scripts/harness.sh --org .lake/org --manifest scripts/olean-manifest.sha256 --work WORK \
  --gate RecursionFast.Challenge.certified --computable RecursionFast.Challenge.submission \
  CHALLENGE.lean SOLUTION_DIR ../submissions/baseline/comparator-nanoda.json
#   SOLUTION_DIR: a directory with the entry's .lean files and Solution.lean (v2 copied them to $T/sol)
#   the badge half (v2: --badge-build …) and the benchmark (--bench …) are S3's

# the source rule alone, on the entry
python3 -I scripts/source-rule.py ../submissions/baseline
```

The entry's own checks:

- **`check.sh`.** The v2 flow of §7, with paths relative to this repository and the core at
  `.contract`. Logs go to `logs/V3-S2/`, which is gitignored.
- **`smoke.py`, until S3 replaces it.**
  1. Draw 4 random starts and run `PROVER tree DIR` at `r = 2`, `n = 16`.
  2. Compute the leaf and node digests independently, with Python's `hashlib.blake2s` and the tag
     bytes and `enc64` read from S1's `Relation.lean`.
  3. Run the compiled `Vb` on the root and on every inner proof.
  4. Check the four canary kinds of §6.3 step 7.
  5. Run `PROVER node DIR` on the two level-1 children. Check that the proof sizes match §4.1.
- **The calibration measurement** (§6.5). The compiled `Vb` on the root of a tree at `r = 8`,
  `n = 2^14` (256 chains of `2^14` hashes, proved by the native prover), timed, with the machine
  described (CPU model, core count, `pclmulqdq` present or not, load). The development VM is not
  the reference machine (O-6), so the number is a placeholder that the season's calibration
  replaces. It must exceed `T_V = 2 s`. Record also whether it stays within `verify_s = 60 s`:
  the design's 22–29 s rests on v2's 5.3–7.0 µs per compiled compression (O-9).

### 9.1 The native prover

Any language, built from source in the sandbox. A dependency-free script is the simplest choice,
following v2's smoke prover `python3 -I harness/smoke/toy_prover.py`.

- **`tree`.** For each leaf, `h_i = chainEnd s_i n`: `n` times `blake2s256` of the 32 raw bytes,
  with no tag. Then `c_i = leafStmt h_i n`, and the proof is `ser (leaf s_i n)`.
- **The levels.** Pair adjacent digests with `nodeStmt`, as `treeRoot` does (§5.1). The proof of
  each node is `ser (node c₁ c₂ π₁ π₂)`.
- **Output.** `proofs/L<i>.bin`, `proofs/N<level>_<j>.bin` and `root.bin`.
- **`node`.** Read the two children's digests and proofs, and write `proof.bin`.

Cross-check its bytes against `ser` with a known-answer test:

- **Generate the answers from Lean.** Use a scratch file outside the root, where `#eval` is fine.
  Inside the root the source rule refuses `#eval` and `#guard`, and allows only `#check`,
  `#print`, `#reduce` and `#guard_msgs`.
- **Keep one kernel-checked equation in the root**, for example
  `example : ser w₀ = ⟨#[…]⟩ := by rfl` for a small witness `w₀`.

S3 fixes the file formats (`AGENTS.md` §7). The runner's sandbox exposes `/usr` and `/etc`, so a
system `python3` is available there, as it was in v2's runs.

## 10. Traps (from v2 and from this design)

- **Precomputations bound by `let` are recomputed per element.** The compiler eta-expands a
  definition that begins with a `let`, so the precomputation is redone on every call (v2 README §3.1,
  "The indexer", S9-A10). Keep hot code free of that shape.
- **Closed terms run at start-up.** A compiled executable evaluates every closed term of every
  imported module when it starts (S6b-A5, harness README "Start-up"). Do not put large closed
  terms, such as a big image literal or a table, in modules on the badge path.
- **The verifier's time is unbounded in `n`.** `Rel` has no cap on `n` (§2.2: `n` is a benchmark
  input). A complete witness-sending verifier must therefore accept every `n`, and its time is
  linear in the `n` a proof declares. Random proofs almost never decode, given the strict format
  (v2's DoS generator draws a uniform length up to 1 MiB and random bytes). An adversarial leaf
  with a huge `n` makes `Vb` run past `verify_s`. Say so in the README as a known property of this
  entry. It is one more reason the entry is unranked, and a data point for the review.
- **Names are the contract's, not the design's.** S1 may have renamed fields, changed `B`, or
  stated `ImageComputes` differently (§4.5). The RESULT lists every difference.
- **Statements are the organiser's.** Fill only the placeholders. The comparator rejects any other
  difference from the challenge.
- **No `Controls` imports.** By convention an entry imports only the contract and the library
  (v2 README §1). Copy what you need.

## 11. Definition of done

1. **The entry exists.** `submissions/baseline/` is flat and holds the files of §3, including
   `README.md` and `NOTES.md`.
2. **Certified.** `certified` is proved against the v3 challenge rendered from `claim.json` at the
   S1 pin:
   - the axioms are only `propext`, `Classical.choice` and `Quot.sound`;
   - there is no `sorry`;
   - `leanchecker` passes;
   - hygiene and the source rule pass;
   - the negative claims are rejected.
3. **Build green.** The entry builds against the pin. The core-side pull request's `lake build`,
   allowlist, manifest and CI are green as far as S1 left CI.
4. **Harness ACCEPT.** `scripts/harness.sh` prints `HARNESS: ACCEPT`, with the comparator under
   both kernels and then the gate. The RESULT says which harness ran. The badge path and the
   benchmark run when S3 exists. Until then the smoke tree, the canaries and the timing come from
   the entry's own scripts.
5. **The smoke tree is proved.** At `r = 2`, `n = 16`, the native prover's proofs are all accepted
   by the compiled `Vb` against independently computed digests, and all four canary kinds are
   rejected.
6. **Listed, unranked by the cap.** The root check at `r = 8`, `n = 2^14` is measured, logged and
   above `T_V`. The registry listing itself is the intake's (S7), so `records.json` stays empty.
7. **The pin.** `.contract` points at the S1 commit, which is reachable on the core's remote.
8. **The stage protocol was followed** (`../../CLAUDE.md`):
   - `docs/stages/V3-S2-RESULT.md`: what was built, file by file with `loc.py` counts; build and
     check times; the controls; the deviations from the design with reasons; the measurements
     with log paths; open questions;
   - the review and the golf report, and a fix pass appended to the RESULT.
9. **Pull requests opened**:
   - in this repository, against `main`, once it has a remote. It has none on 2026-10-19, and
     creating one is the user's decision;
   - the core-side pull request against the core.

## 12. Open items that touch the baseline (§12)

- **O-12** (badge executables regenerated from kernel terms): the baseline's `verify` is Lean-compiled code, trusted only up to the gate and the source rule until O-12 closes, and board T cannot open before then.
- **O-21** (error caps and budgets): the baseline has `ε = 0`, but its `fuel ≤ B` proof follows whatever extractor budget `B p l` S1 fixes, and `errorCap` may tighten to `2^-160`.
- **O-23** (counted-error completeness): the baseline proves perfect completeness and is unaffected, unless S1 changes the shape of the `Complete` field.
- **O-24** (intake): the baseline is the first root the intake processes, so its layout, claim, attribution and registry entry must fit what S7 fixes; keep it flat and small.

Also relevant: **O-6** (the reference machine; the calibration measurement of §9 is a placeholder
until it exists), **O-9** (compiled Blake2s speed sets the root-check time) and **O-18** (the
succinctness cap as a deterministic step count, which would replace the wall-time measurement).
