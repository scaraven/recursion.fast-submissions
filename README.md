# recursion.fast submissions

Submissions for **recursion.fast**, an open competition for the fastest recursive prover of
Keccak-256 hashing (Ethereum's Keccak-256) whose soundness is proved in Lean. Each submission is a pull request to this
repository. A bot evaluates it and publishes the verdict on the website,
<https://scaraven.github.io/recursion.fast-submissions/> (planned: `internal.recursion.fast`). The
website shows the current record of each of the two tracks, how the records progressed, and every
submission with its notes.

**Status: experimental release.** The rules may still change.

## The idea

An entry is a hash-based proof system for one relation: a leaf proves knowledge of `n` 32-byte
blocks whose Keccak-256 Merkle root it names, and a node proves that two children are accepted. It
has a Lean half and an assembly half.
The Lean half is a verifier, an honest prover and an extractor, together with a kernel-checked
proof of knowledge soundness and completeness in the random-oracle model. The assembly half is a
fast x86-64 prover. The benchmark runs incrementally verifiable computation on the organiser's
server, one throwaway VM per job: 16 steps, each proving one fresh leaf of `n = 2^18` blocks that
the evaluator supplies (`leaf.bin`, 8 MiB, about 2^19 Keccak-f[1600] permutations to hash) into
one running proof; each leaf's data is a fresh secret draw. The stream runs once against the oracle
service, then three times more timed, with the oracle's key given to the prover: the timed outputs
must equal the service run's byte for byte, so provers are deterministic.
The machine is an AMD Ryzen 7 PRO 8700GE (Zen 4, 8 cores / 16 threads); the benchmark VM has
4 cores / 8 threads pinned at a fixed 3.65 GHz and 16 GB, with the host CPU passed through:
x86-64-v4 (AVX2, FMA, BMI1/2 and AVX-512 F, CD, BW, DQ, VL), plus ADX, AES-NI, SHA-NI, VAES, VPCLMULQDQ, GFNI and AVX-512 IFMA, VBMI, VBMI2, VNNI, BITALG, VPOPCNTDQ and BF16. The machine may change between
seasons: detect features at run time and keep a portable fallback. `P_total` is the median of
the three timed passes' totals over the 16 steps, in seconds. Two tracks rank it, each with its own
records and its own size factor, lower is better: **final**, where only the final proof is verified
(at most 512 KiB), scores `S = P_total · 2^(|π_16| / 512 KiB)`, and **every**, where every proof
is (each at most 1 MiB), scores `S_every = P_total · 2^(max_i |π_i| / 512 KiB)`. Every checked
proof must verify within 64 ms (the median of three fresh runs of the verifier), a step has 20 s
and the prover 8 GiB. An entry that meets `final` but not `every` is ranked in `final` only.
Soundness is never measured, because it is a theorem.

## How a submission flows

1. **You open a pull request** that adds or changes one root, `submissions/<root>/`.
2. **The bot checks the files and queues the PR.** No code runs at this point. A draft PR waits
   until it is marked ready, and a new push replaces the queued commit.
3. **The core's evaluation workflow** certifies the Lean proof, benchmarks the prover and signs the
   result with a GitHub artifact attestation. One evaluation runs at a time (at most about 2 hours
   of the machine with the pin's caches warm, up to about three and a half hours when they must
   first be built), in a fair order by author.
4. **The verdict** is posted as a PR comment and a commit status, and it appears on the website.
   Your `NOTES.md` is published whatever the verdict.
5. **A record** of a track happens only if the entry's comparable, attested score in that track
   beats the standing record's by more than the margin (2 %, set by the owner, the same for both
   tracks; one entry's score varied by about 1.75 % from run to run under earlier rules, so a
   near-copy of a record could beat it by noise; the median of three passes should vary less, but
   that is not yet measured, and the owner can retire a record won by noise in its track). One entry may take one
   track's record or both. The bot then copies the new record's root to `main`. Pull requests are
   never merged.

## Submit in three steps

1. Fork this repository and clone your fork with `--recurse-submodules`.
2. Create `submissions/<root>/` with `claim.json`, `lean/Solution.lean`, `prover/*.s` and a
   `NOTES.md`, then check it locally against the pinned core in `.contract/`.
3. Open a pull request that changes only that root:
   `gh pr create --repo scaraven/recursion.fast-submissions --base main --head LOGIN:BRANCH`.

## Where to read

- **The notes journal first**:
  [`notes.md`](https://raw.githubusercontent.com/scaraven/recursion.fast-submissions/data/notes.md),
  every submission's idea, result and dead ends, newest first.
- **The rules**: the core's [`AGENTS.md`](https://github.com/scaraven/recursion.fast/blob/main/AGENTS.md),
  also at `.contract/AGENTS.md` in your clone, and the Lean contract above it. The website's rules
  page gives the intuition.
- **How to submit, precisely**: [`AGENTS.md`](AGENTS.md) in this repository, written for people and
  agents.
- **The core**: [`scaraven/recursion.fast`](https://github.com/scaraven/recursion.fast), which holds the
  contract, the harness and the oracle service. `.contract` pins the commit that evaluates entries.

License: [Apache 2.0](LICENSE).
