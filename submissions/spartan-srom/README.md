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
D-1 … D-6, formats, the verifier branch by branch), the stage RESULTs F0–F4 and the reviews. The
report on the rules that this entry produced is `docs/v4/FLOCK-BASELINE-FEEDBACK.md`.

## Status (2026-10-27)

- **Under the amended rules** (stage F5, core `a283ff8`: V4-A9, the trim, and V4-A10, textbook
  knowledge soundness; `docs/v4/flock-baseline/stages/F5-ks-RESULT.md`):
  - the certificate reaches the contract's new `KS` through the library's bridge `KState.ks`
    (5 Lean files, no statement changed);
  - the certificate job is **ok** in 8 min 42 s on 4 CPUs of the development VM, within every cap:
    build 259.5 s of 600, kernel 182.3 s of 600, gate about 26 s of 120, badge build about 20 s of
    180;
  - **ACCEPT at the smoke shape**: `T_tree` 0.116 s, `t_leaf` 0.0560 s, `t_merge` 0.0106 s,
    `t_link` 0.0666 s, **`S` = 1.448**; root `acc` 392 ms; 9 statement canaries rejected; DoS 64
    inputs, none accepted, maximum 323 ms;
  - **REJECT at the season shape**, for F4's reasons (below).
- **Certified.** `SpartanSrom.certificate` is a closed theorem on the three allowed axioms (F1
  RESULT §3, §9.3). The entry is the commit `745c7d8`: the Lean fix pass at core `81e1ebf` (D-6,
  the pin's `acc`, the byte-level node reader, the golf), with the prover's golf and fix pass.
- **The verdict at the previous pins**: ACCEPT at `81e1ebf`; confirmed at `01a25b0`: **ACCEPT** (F4b: certificate ok with the Lean kernel in 9 min 51 s; smoke bench of the submitted `prover.s` `733b3a30…`: T_tree 0.142 s, t_link 0.0846 s, S 1.835; `prover.s` assembles with GNU Binutils 2.42 without error or warning; `docs/v4/flock-baseline/stages/F4-final-harness-RESULT.md`, F4b)
- **Through the fixed harness** (stage F4, `745c7d8` at core `81e1ebf`, no workaround;
  `docs/v4/flock-baseline/stages/F4-final-harness-RESULT.md`):
  - the certificate job: **ok** in 9 min 52 s. With `--nanoda` it is also ok: nanoda ran over its
    14 GiB budget, and the Lean kernel's verdict stands;
  - **ACCEPT at the smoke shape** (`r = 2, n = 16, M = 4`): `T_tree` 0.140 s, `t_leaf` 0.0689 s,
    `t_merge` 0.0138 s, `t_link` 0.0827 s, **`S` = 1.794**; root `acc` 416 ms; DoS maximum 312 ms;
  - **REJECT at the season shape**:
    - the tree, because the prover's 1,572,898-byte Fiat–Shamir query (the absorb of the Ligero row
      `ū` at `n = 2^18`) is above `queryCap`;
    - the stream, because its first leaf's `π` (2,791,559 B at `n_f = 2^16`) is above `proofCap`.
      The leaf itself now completes in 14.4 s at 2.64 GB.
- **Earlier** (stage F3, the frozen commit `8111b71` at core `a874f87`;
  `stages/F3-harness-RESULT.md`): smoke ACCEPT with two workarounds that the core has since fixed
  (`Solution` importing every module, FIXLIST Q7; CompPoly among the organiser's roots, Q2), with
  `S` = 6.666. The frontier F3 measured still holds: ACCEPT only where `2^r · n ≤ 4,096`. Every
  larger tree root, and every stream after its fifth link at `n_f = 16`, is above `proofCap`.

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
    **qV = 2^16** (`KS.ks vk`): the contract's textbook `KS` (V4-A10), from v3's potential, now the
    library's `KState` and the entry's intermediate artifact, through the library's bridge
    `KState.ks`. A bundle of `k` SNARKs costs no extra error: v3's `final` argument is about the
    log, and it gives `chainEnd s_j n_j = h_j` for every bundled leaf at once;
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
| `lean/SpartanSrom*.lean` | the entry, 65 modules. `SpartanSromNode` holds the v4 verifier (branches `L`, `C`, `N`, `B`), `SpartanSromNodeBytes` its byte-level node reader, `SpartanSromSubmission` and `SpartanSromFinal` the submission and certificate, `SpartanSromRun` the functions behind the development runner, and the `…Controls` modules the controls. `SpartanSrom` imports every module, and `Solution` imports `SpartanSrom`, so the harness builds and checks the controls too (FIXLIST Q7) |
| `prover/*.rs`, `Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml` | the native prover's source (`prover/README.md`) |
| `prover/build-asm.sh`, `prover/sanitize-asm.py` | the assembly build |
| `prover/prover.s` | the submission: the generated assembly, the only file the runner builds |
| `prover/selftest.py` | end-to-end tests against the real service |
| `LICENSE-leanerVM` | the licence of the leanerVM-derived files |
| `NOTES.md` | the journal |

With `Solution` the Lean is 66 files and 17,901 code lines (F1 §9.3).

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
timeout 1800 "$ORG/harness/org-setup.sh" "$ORG"              # CompPoly's field is a root at the pin
source "$ORG/scripts/tools.env"                              # the comparator and nanoda
timeout 1800 python3 -I "$ORG/harness/evaluate.py" cert --entry submissions/spartan-srom \
  --org "$ORG" --work logs/eval/srom/cert --out logs/eval/srom/cert.json
timeout 1800 python3 -I "$ORG/harness/evaluate.py" bench --entry submissions/spartan-srom \
  --cert logs/eval/srom/cert.json --season "$ORG/harness/smoke.toml" \
  --work logs/eval/srom/bench --out logs/eval/srom/result.json
```

- Measured at `a283ff8` (F5; `logs/f5/`): `org-setup.sh` 6 min 7 s, the `Mathlib.Tactic` objects
  included; the certificate job 8 min 42 s on 4 CPUs (the one build 259.5 s, the comparator's
  Lean-kernel run 182.3 s, the gate about 26 s, the badge build about 20 s); the smoke bench 14 s.
- Measured at `81e1ebf` (F4; the shared VM, lightly loaded):
  - `org-setup.sh` took 4 min 12 s (`logs/f4/org-setup.log`);
  - the certificate job took 9 min 52 s (`logs/f4/cert.log`). Of that, the comparator's Lean-kernel
    run took 354 s at a scope peak of 4.25 GB, the gate-tree build 173 s, the gate 18 s and the
    badge build 16 s.
- A clean build of the Lean alone takes 2 min 46 s on 8 cores, peak RSS 4.12 GB
  (`logs/lean/build-full-fix2.log`, F1 §9.3).
- The same job at `a874f87` took 14 min 22 s (F3 §2.3).
- `--nanoda` adds a separate second-kernel run (16 min 36 s for the whole job, F4). On this entry
  nanoda needs more than 20 GB (F3 §2.4). At the pin, its memory kill no longer changes the verdict
  (FIXLIST Q12).

**The native prover.**

```sh
prover/build-asm.sh /some/work/dir      # rewrites prover/prover.s; links WORK/build/prover
sha256sum prover/prover.s               # 733b3a30… (the connection-cap fix, logs/conncap/)
(cd prover && CARGO_TARGET_DIR=/elsewhere cargo test --release --offline)   # the pin applies here
python3 -I prover/selftest.py --prover /some/work/dir/build/prover \
  --service "$ORG/service/target/release/rf-oracle" --work DIR tree stream sizes
```

- The toolchain is pinned by `prover/rust-toolchain.toml` (rustc 1.99.0). The submitted `prover.s`
  is 9,238,056 bytes, SHA-256 `733b3a30…`, and links to a 2,818,664-byte binary, SHA-256
  `c5f5e1a8…`; two clean builds gave the same bytes (`logs/conncap/build-{a,b}.log`). It differs
  from the F2 fix pass's (`7a30e654…`, three identical builds, `logs/f2/fix/`) only by the
  connection pool's cap, 31 instead of 32, for the service's 32-connection cap at the pin.
- **The runner's `as` is GNU Binutils 2.42** (`ubuntu-24.04`; `.contract/harness/PROVER.md` §1,
  RF-M2); this VM's is 2.46. `sanitize-asm.py` drops what LLVM 23 emits and 2.42 rejects. The
  core's `harness/tools/asm-compat.py` merges its rules with GCC 15's `.base64`, and it is the
  organiser's helper for every entry. The confirmation run at the pin (Status, above) checks
  `prover.s` against 2.42.
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
