# `flock-recursive`: a recursive Flock-class entry

## The construction

**Proof system.** A Flock-class batch-R1CS argument over GF(2):
- a Ligerito commitment over F = GF(2^128), in the unique-decoding regime;
- fold challenges in K = GF(2^256);
- BLAKE2s for every hash.

The fields are built over CompPoly's `BF64`.

**Each step of the stream.** A step's new chain of `n ∈ [2^17, 2^20]` BLAKE2s compressions is split into
`k = ⌈n/2^18⌉ ≤ 4` segments.
- Each segment gets its own segment SNARK.
- The segment SNARKs are gathered into one signed aggregate leaf.
- **One recursive node proof** covers the previous step's node and the `k` segments:
  - kinds `N2` and `N4`;
  - the first step, which has no previous node and up to 8 segments, is kind `N8`.

**What a node does.**
- It commits to its children's signed traces as the message slots of its own BLAKE2s blocks.
- It checks one WOTS signature per child.
- It replays each child's verifier as field-element rows.

**Soundness.** Knowledge soundness goes through the contract's potential `KState` (`KState.ks`). The error per fresh query
is `εR = 15/2^124`, which is the `error` in `claim.json`.

**Design documents.** These live outside this root, under `docs/v4/flock-recursive/` on branch `v4/rev44`:
- `BLUEPRINT.md`, the normative design;
- `stages/`, one RESULT per stage, with its measurements and logs;
- `reviews/`.

## Layout

- **`lean/`** holds the certificate, the verifier `V`, the extractor `E` and the controls.
  - `Solution.lean` is the challenge's rendered stub. Its only filled placeholders are `submission` and `certified`.
  - `FR.lean` imports every module.
  - Every module builds: 263 modules.
- **`prover/`** holds the native prover.
  - It is std Rust with no dependencies, emitted as one x86-64 GNU-as file, `prover.s`, which the runner links.
  - `build-asm.sh` regenerates `prover.s`. Two clean builds are identical byte for byte.
  - `nodeblob.b64` holds the node circuit's tables, dumped from the Lean definitions.
  - Every Merkle and Fiat–Shamir hash goes through the organiser's oracle service.
- **`claim.json`** holds the claimed error, completeness error, `qV` and the extractor's fuel.

## The certificate

The certificate is the theorem `certified : CertificateR declared submission`.
- **No hypothesis:** the remaining verifier obligations, Gaps4, are discharged by `open4F_holds`.
- **Axioms:** `propext`, `Classical.choice` and `Quot.sound` only.
- **Source rule:** 0 findings.
- **Harness:** the comparator accepts `certified` with the Lean kernel.

## Status (2026-10-30)

**Full evaluation on the GitHub runners at core `422f2f9`:** two runs of the core's `evaluate.yml`.

| run | certificate | benchmark |
|---|---|---|
| 41012684797 | `ok`, Xeon 8573C | **ACCEPT**, EPYC 9V45: S = 29.05 (P̄ 4.52, V̄ 24.52), M = 96 |
| 41012684725 | `ok`, EPYC 7763 | **ACCEPT**, EPYC 9V74: S = 34.20 (P̄ 6.78, V̄ 27.42), M = 96 |

Both runs are attested, not truncated and comparable. They were measured on the prover of `37deb5c`, before the
build-time cut (G6) and the prover speed-up (P2r).

**Caps on the slower run.**

| cap | limit | measured | margin |
|---|---|---|---|
| `build_s` | 1,200 s | 968 s | 1.24× |
| `kernel_s` | 600 s | 378 s | 1.59× |
| `stream_s` | 1,920 s | 1,689 s | 1.14× |
| `step_s`, worst step drawn | 60 s | 24.5 s | 2.45× |

Every other cap holds by at least 1.4×.

Since that run:
- **G6** cut the certificate build's CPU by 28 % locally, with the same statements and definitions.
- **P2r** factored the node prover's arena rows. Its proofs are byte-identical to the old prover's.

The final runner evaluation, at this root's commit, is recorded in `docs/v4/flock-recursive/stages/`.
