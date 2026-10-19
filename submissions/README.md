# `submissions/`: one root per entry

Each entry is one directory `submissions/<root>/`. There is no entry yet. The first will be the
organiser's baseline, `submissions/baseline/` (stage S2, `docs/baseline/BASELINE-TASK.md`). The
rules a submitter reads are in `../AGENTS.md`. This file is the layout of a root. Section numbers
refer to `docs/design/DESIGN-v3.md`.

## Root rules

1. **One root per entry.** An entry pull request creates or changes only its own root (§7.7). It
   never touches `records.json`, `.contract`, `docs/` or another root.
2. **Root name.** Proposed until S7 fixes it: a lowercase identifier (`[a-z][a-z0-9-]*`), unique
   in this directory. The intake's submission id and the record refer to it.
3. **Flat.** §7.7 says the intake exports a root "as flat regular files". ots.golf, whose model §7.7
   adopts, reads that as no subdirectories, no symbolic links and only regular files. S7 fixes the
   rule. Until then, keep roots flat.
   - The v2 baseline (`docs/baseline/v2-example/`) used subdirectories, but it lived inside the
     core and predates the intake.
   - A Rust prover fits a flat root: `Cargo.toml` with `[[bin]] path = "main.rs"`, and the modules
     beside it.
4. **Lean modules.**
   - Every `.lean` file of the root becomes a module of one generated library. The harness ignores
     any lakefile, `leanOptions` and `moreLeanArgs` (`docs/core/harness-README.md`, "How the
     harness builds a solution").
   - In a flat root, a file `Foo.lean` is the module `Foo`.
   - Module names must be fresh: not `RecursionFast`, not `Mathlib`, and not the root of any
     package. Use a prefix that names the entry, such as `BaselineV3…`.
   - Imports: the allowlist and the hard rules of `AGENTS.md` §10 and §11.
5. **Files a root holds:**

   | File | Required | What |
   |---|---|---|
   | Lean sources (`*.lean`) | yes | `V`, `P`, `E`, the proofs, and the solution module that fills the challenge's `submission` and `certified` (§3.2) |
   | `claim.json` | yes | the declared data rendered into the challenge: v2 schema below, S3 fixes the v3 one |
   | extractor image | yes | `image.code` (little-endian 32-bit words) and `image.data` (little-endian 64-bit words), named by the claim, ≤ `2^20` bytes together (§4.4, §6.6) |
   | extractor source and build script | recommended | e.g. `extractor.S` and `build-extractor.sh`, so the image can be reassembled byte for byte (the v2 baseline's `check.sh` does this) |
   | native prover source and build script | yes | built from source in the sandbox with the pinned toolchains, ≤ 1 h (§3.2, §6.3 step 2) |
   | `README.md` | recommended | what the entry is, for a reader: the construction, what is proved, the measurements |
   | `NOTES.md` | expected (§7.7) | the untrusted journal: the idea, the result, what did not work and why, what to try next. Published whatever the verdict (§7.7) |
   | `check.sh` | recommended | the entry's own end-to-end check (the v2 baseline's `scripts/check.sh` is the model) |

6. **No secrets, no binaries the harness would trust.** The harness renders the image from your
   files and checks it against the certificate. It builds the prover from source. Prebuilt
   executables are not run.

## The claim (v2 schema; S3 fixes the v3 schema)

v2's leaf-board claim (`docs/baseline/v2-example/claim.json`):

```json
{"k": 24, "hash": "blake2s", "arity": 2,
 "image": {"code": "extractor/extractor.bin", "data": "extractor/extractor.data"}}
```

- **What v3 drops.** v3 has no class `k`, one hash at launch (V3-6) and no Merkle arity, because
  there is no organiser compiler. So `k`, `hash` and `arity` go.
- **What v3 keeps.** The image and "the declared numbers" stay. `Declared` carries over from v2,
  and the certificate requires `S.img = D.img` (§3.2).
- **Renderer rules** (v2 §3.3): the claim's keys equal the stub's placeholders exactly; there are no
  floats and no duplicate keys; paths are relative, inside the root, with no `..` and no symbolic
  link.

## Registry

`../records.json` is the registry (§7.7). Per board, it holds the standing entry with its contract
id, hardware id, `entry_id` and the verdict's commit. Only the intake writes it. Until S7 it is
empty: `{"version": 1, "records": {}}`.
