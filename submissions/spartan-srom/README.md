# `spartan-srom`: the v4 baseline entry

`spartan-srom` is the first entry under the v4 rules, the signed random oracle (SROM). It is v3's
honest SNARK entry `spartan-chain`, ported to the v4 contract, with a new node format.

- **Leaves.** A Spartan R1CS argument for a BLAKE2s chain, over GF(2^64) with challenges in
  GF(2^192), with ring switching and a Ligero commitment with unique-decoding proximity. The
  BLAKE2s circuit is leanerVM's transcription of leanVM's Flock circuit. All of this is v3's
  `spartan-chain`, with the Lean renamed `SpartanChain` → `SpartanSrom` (BLUEPRINT D-1, D-3).
- **Nodes** are **σ0-bundles** (D-2). A node proof is the node's whole subtree as a *clear* witness,
  whose every child slot carries an empty trace and one signature σ0 on the empty trace, followed by
  the leaves' SNARKs. The node's verifier checks the clear tree and σ0 with no query, then re-runs
  each leaf SNARK with fresh queries. Nothing is recursive: a node carries its leaves.
- **The native prover** is std Rust with no dependencies, emitted as one x86-64 GNU-as file,
  `prover/prover.s`, which the runner links (D-4). Every Merkle and Fiat–Shamir hash goes through
  the organiser's oracle service.

The entry's journal, for the next solver, is `NOTES.md`. Its records are in
`docs/v4/flock-baseline/` (repository root): `BLUEPRINT.md` (normative for this entry: decisions
D-1 … D-6, formats, the verifier branch by branch), the stage RESULTs F0–F3 and the reviews. The
report on the rules that this entry produced is `docs/v4/FLOCK-BASELINE-FEEDBACK.md`.

## Status (2026-10-23)

- **Certified.** `SpartanSrom.certificate` is a closed theorem on the three allowed axioms (F1
  RESULT §3).
- **Through the real harness** (stage F3, the frozen commit `8111b71`, core `a874f87`;
  `docs/v4/flock-baseline/stages/F3-harness-RESULT.md`):
  - **ACCEPT at the smoke shape** (`r = 2, n = 16, M = 4`), with two workarounds that the core
    has since fixed at the pin `81e1ebf`: `Solution` had to import every module (FIXLIST Q7), and
    CompPoly had to be added to the organiser's roots (Q2);
  - ACCEPT only where `2^r · n ≤ 4,096`: every larger tree root, and every stream after its fifth
    link at `n_f = 16`, is above `proofCap`;
  - **REJECT at the season shape**: the tree when the service refused a 1,572,898-byte query
    (`queryCap`), the stream when the 11 GiB cgroup killed the pre-golf leaf prover.
- **Since F3**: the prover's execution-time golf and fix pass (proofs byte-identical, leaves
  2.6–4.5× faster, a `2^16` leaf in 2.47 GiB instead of about 15 GiB; F2 golf §4), D-6, and the
  Lean fix pass.

  <!-- TODO(orchestrator): the entry's evaluation at the pin 81e1ebf (cert and smoke bench), after the F1 fix pass -->

## Proof formats

Every proof `π` is one of four formats, told apart from its bytes before any query (BLUEPRINT
§1–§2; `lean/SpartanSromNode.lean`, `V`). `encode w` is the library's
`WitnessSending.encode`; integers are little-endian.

| Format | Bytes of `π` | Made by | What `V vk c π` checks | Queries |
|---|---|---|---|---|
| **L**, SNARK leaf | `enc64 0 ‖ s ‖ enc64 n ‖ h ‖ π_S`, exactly `leafSize n` bytes (80 for `n = 0`) | the Lean `P` and the native prover, for every leaf | `n ≤ chainCap`, the size, `c = leafStmt h n`; then v3's SNARK verifier for `chainEnd s n = h` (`h = s` when `n = 0`) | `qBound (kap n) ≤ 2^14`; 3,533 at `n = 16` |
| **C**, clear leaf | `encode (.leaf s n)`, 48 bytes | the native prover, inside bundles only | `n ≤ 2^12` (D-6) and `c = leafStmt (chainEnd s n) n`, recomputed | none |
| **N**, plain node | `encode (.node c₁ c₂ p₁ p₂)`, exactly | the Lean `P`, for every node (D-5); the native prover only when a child cannot be bundled (`n = 0`, `n > 2^12`, or two different σ0) | `c = nodeStmt c₁ c₂` and the contract's `acc` on both signed children (restated as `accWith`) | none of its own |
| **B**, bundle | `encode W ‖ T`: `W` a clear tree, every slot with an empty trace and the same σ0; `T` holds `h_j ‖ π_S,j` for each clear leaf, left to right | the native prover, for every inner node, root and stream node | with no query: the clear tree, `SigOk vk (traceDigest []) σ0` once, `\|T\|` exactly, every `1 ≤ n_j ≤ 2^12`, `Σ qBound ≤ 2^16`, `c = nodeStmt c₁ c₂`; then each leaf's SNARK with fresh queries | `Σ_j qBound (kap n_j) ≤ 2^16` |

Anything else is rejected with no query. The trace of a bundle is its leaves' SNARK traces,
concatenated in `T`'s order. The extractor is the library's copy extractor, so a bundle extracts to
its clear tree `W` (`decode` stops before `T`).

Sizes at `n = 16` (F1 RESULT §5, F2 RESULT §3.3):

| Proof | `π` (bytes) | trace entries | signed file (bytes) |
|---|---|---|---|
| L, one leaf | 143,711 | 3,533 | 538,698 |
| C, one clear leaf | 48 | 0 | 4,840 |
| B, two leaves | 297,078 | 7,066 | 1,082,260 |
| B, four leaves (the smoke root) | 603,812 | 14,132 | 2,169,384 |
| N, two signed L leaves | 1,089,384, above `proofCap` | 0 | 1,094,176 |

## What is certified

- **`SpartanSrom.certificate : Certificate SpartanSrom.submission`** (module
  `SpartanSromFinal`). Its axioms are `propext`, `Classical.choice` and `Quot.sound`
  (`logs/lean/axioms-print-2.log`). For **every** public key `vk`:
  - **knowledge soundness** for `Rel (acc vk)`, with **ε = 2^-129** per fresh query and
    **qV = 2^16** (`KS.ks vk`). The potential is v3's. A bundle of `k` SNARKs costs no extra error:
    v3's `final` argument is about the log, and it gives `chainEnd s_j n_j = h_j` for every bundled
    leaf at once;
  - **completeness with δ = 0**: perfect completeness for every oracle function, through the
    library's `complete_withError_zero`.

  Also `Computes` (the library's `WitnessSending.computes`, fuel `8 t`) and the caps.
- **`RecursionFast.Challenge.certified : CertificateR declared submission`** (`lean/Solution.lean`),
  against the challenge rendered from `claim.json`:

  ```json
  {"error": "1/680564733841876926926749214863536422912", "completeness_error": "0",
   "qV": 65536, "fuel_base": 0, "fuel_per_word": 8}
  ```

  `error` is 2^-129. In Lean, `ε` is `εR1 = ((1 / 2^129 : ℚ≥0) : ℝ≥0)`, a cast from `ℚ≥0` so that
  the badge can compile the submission, and `εR1_eq` proves it equal to v3's `(2 : ℝ≥0)⁻¹ ^ 129`.
- **Controls.** v3's controls are carried over: field, circuit, MLE, RS, Ligero, the transcript and
  Merkle known answers, the log and PCS controls. `SpartanSromNodeControls` adds the node formats'
  controls: a clear tree signed by the library's reference signer is accepted; each bundle check
  rejects its negative with no query; the canaries `π ± 1` byte are rejected for `L`, `C`, `N` and
  `B`; the claims `ε = 2^-130`, `qV = 2^16 − 1` and fuel `7 t` are not certified (F1 RESULT §4).

**What is not certified.**

- **The native prover.** Nothing about it is proved, and nothing needs to be: `acc` is the only
  check. What checks it:
  - the compiled Lean `acc` (the harness's badge) on every proof the harness asks about (F3 §3);
  - known-answer tests: its leaf SNARK bytes equal the Lean `P`'s at `n = 1, 16` (F2 RESULT §3.5)
    and v3's cargo-built prover's at `n = 1, 2, 16, 64` (F2 RESULT, fix pass);
  - its own native `acc` (`prover/acc.rs`), which the F2 review compared with the Lean `V` branch by
    branch, and end-to-end tests against the real service (`prover/selftest.py`).
- **Costs.** No theorem bounds `V`'s running time, `T_V` or the DoS column. D-6 bounds the clear
  leaf's recomputation at 4,096 compressions.
- **`acc` on the Lean `P`'s nodes.** Completeness is a statement about `V`, not `acc`. The Lean `P`
  sends node witnesses plainly (format `N`, D-5), and with SNARK children those proofs are above
  `proofCap`. The proofs the harness accepts are the native prover's bundles.
- **The composition across the tree**, which uses the signature's unforgeability once, outside
  every certificate (design §2.4).

## Layout of the root

| Path | What |
|---|---|
| `claim.json` | the declared numbers (above) |
| `lean/Solution.lean` | the rendered challenge, `submission := SpartanSrom.submission`, `certified` |
| `lean/SpartanSrom*.lean` | the entry. `SpartanSromNode` holds the v4 verifier (branches `L`, `C`, `N`, `B`), `SpartanSromSubmission` and `SpartanSromFinal` the submission and certificate, `SpartanSromRun` the functions behind the development runner, and the `…Controls` modules the controls. `SpartanSrom` imports every module |
| `prover/*.rs`, `Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml` | the native prover's source (`prover/README.md`) |
| `prover/build-asm.sh`, `prover/sanitize-asm.py` | the assembly build |
| `prover/prover.s` | the submission: the generated assembly, the only file the runner builds |
| `prover/selftest.py` | end-to-end tests against the real service |
| `LICENSE-leanerVM` | the licence of the leanerVM-derived files |
| `NOTES.md` | the journal |

<!-- TODO(orchestrator): after the F1 fix pass, the module list (it adds `SpartanSromNodeBytes`, a byte-level node reader) and whether `Solution` imports `SpartanSrom`, so that the harness builds the controls (FIXLIST Q7) -->

## Building and checking it locally

The full recipe, with the reasons for each step, is the repository's `CLAUDE.md`, "Commands".
Local runs are not attested and are not results.

**The Lean, through the core's harness**, as CI runs it. Use an organiser checkout of the pin and a
**private, writable** package tree, never the shared read-only one: `org-setup.sh` and the badge
build write compiled objects into it.

```sh
git submodule update --init                                  # .contract at the pin
mkdir -p logs/org && git -C .contract archive HEAD | tar -x -C logs/org
# a built package tree at the manifest's revisions, copied to logs/pkgs (CLAUDE.md, "Commands")
mkdir -p logs/org/.lake && ln -s "$PWD/logs/pkgs" logs/org/.lake/packages
ORG=$PWD/logs/org; export RF_HARNESS_COMMIT=$(git -C .contract rev-parse HEAD)
timeout 14400 "$ORG/harness/org-setup.sh" "$ORG"             # CompPoly's field is a root at the pin
source "$ORG/scripts/tools.env"                              # the comparator and nanoda
timeout 7200 python3 -I "$ORG/harness/evaluate.py" cert --entry submissions/spartan-srom \
  --org "$ORG" --work logs/eval/srom/cert --out logs/eval/srom/cert.json
timeout 7200 python3 -I "$ORG/harness/evaluate.py" bench --entry submissions/spartan-srom \
  --cert logs/eval/srom/cert.json --season "$ORG/harness/smoke.toml" \
  --work logs/eval/srom/bench --out logs/eval/srom/result.json
```

- Measured at `a874f87` (F3 §1–§3): `org-setup.sh` 5 min 56 s (`logs/f3/org-setup.log`); the
  certificate job 14 min 22 s, peak RSS 4.11 GB, of which the comparator 8 min 33 s and the Lean
  kernel about 192 s (`logs/f3/cert-closure.log`); the smoke benchmark 54 s
  (`logs/f3/bench-smoke.log`). The VM is shared; see F3 for the conditions.
- `--nanoda` adds a second-kernel run. On this entry nanoda needs more than 20 GB (F3 §2.4); at the
  pin a memory kill of nanoda no longer changes the verdict (FIXLIST Q12).

  <!-- TODO(orchestrator): the certificate job and the build at the final pin 81e1ebf (time, peak memory, log) -->

**The native prover.**

```sh
prover/build-asm.sh /some/work/dir      # rewrites prover/prover.s; links WORK/build/prover
sha256sum prover/prover.s               # 7a30e654… (F2 RESULT, fix pass)
(cd prover && CARGO_TARGET_DIR=/elsewhere cargo test --release --offline)   # the pin applies here
python3 -I prover/selftest.py --prover /some/work/dir/build/prover \
  --service "$ORG/service/target/release/rf-oracle" --work DIR tree stream sizes
```

- The toolchain is pinned by `prover/rust-toolchain.toml` (rustc 1.99.0). Three clean builds gave
  the same `prover.s`, 9,238,056 bytes, and the same binary, SHA-256 `fecda6a0…`;
  `build-asm.sh` took 57.8–65.3 s (`logs/f2/fix/build-{a,b,c}.log`, `determinism.log`).
- The unit tests are compiled with cargo's own release profile (`codegen-units = 4`, no LTO), so
  they test the source, not the submitted binary; `selftest.py` runs the linked `prover.s`.
- `selftest.py keyed-kat` needs a service that accepts fixed keys. At the pin the release
  `rf-oracle` refuses `--insecure-test-keys` (RB-m5): build the test binary in the organiser
  checkout with `cargo build --release --features insecure-test-keys --target-dir
  target/test-keys` (in `$ORG/service`) and pass `target/test-keys/release/rf-oracle` as
  `--service` for that part.
- `prover/README.md` lists the development modes (`verify-native`, `prove-leaf`, `bench-leaf`, …)
  and the environment variables.

## Licences and provenance

- **leanerVM** (Apache-2.0, `LICENSE-leanerVM`): the BLAKE2s circuit and part of the ring
  switching. The Lean modules `SpartanSromBlake2sCircuit`, `SpartanSromBlake2sCompress`,
  `SpartanSromBlake2sWords` and `SpartanSromRingSwitch`, and the prover's `circuit.rs`, carry
  provenance headers naming the leanerVM commit and the files they were copied from, and say what
  was modified (Apache-2.0 §4(b)).
- **leanVM**: `prover/field.rs` follows leanVM's field conventions (modulus, limb order; MIT or
  Apache-2.0), with code written fresh.
- **v3's `spartan-chain`**: everything else is ported from it, at this repository's local `main`
  `1f59b38` (not pushed). Every Lean file's first line says so.
- The repository's own licence is Apache-2.0 (`LICENSE` at the root).
