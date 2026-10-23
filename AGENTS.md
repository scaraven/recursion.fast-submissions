# recursion.fast: rules for submitters (v4)

This file is what a submitter, human or agent, reads before preparing an entry. It summarises the
v4 rules, the **signed-random-oracle (SROM)** design, and what the first v4 entry learned building
against them. Citations:

| Cited as | File |
|---|---|
| design §n | `.contract/docs/DESIGN-v4-srom.md` (normative) |
| BRIEF, V4-n, V4-An | `.contract/docs/v4/BRIEF.md` (the decisions and amendments) |
| A-RESULT, B-RESULT | `.contract/docs/v4/stages/A-contract-RESULT.md`, `B-harness-RESULT.md` |
| [CM] | `.contract/docs/DESIGN-cost-incentive-model.md` (the score and the stream) |
| PROVER.md, FORMAT.md | `.contract/harness/PROVER.md`, `.contract/harness/FORMAT.md` (normative) |
| PROTOCOL.md | `.contract/service/PROTOCOL.md` (normative for provers) |
| the contract | `.contract/RecursionFast/Contract/*.lean` |
| BLUEPRINT, F0 … F3 | `docs/v4/flock-baseline/BLUEPRINT.md`, `docs/v4/flock-baseline/stages/F<n>-…-RESULT.md` (the baseline entry `spartan-srom`) |
| F0-ideation, F2-review | `docs/v4/flock-baseline/reviews/F0-route-ideation.md`, `F2-prover-review.md` |

**What is binding.** The harness checks the Lean contract of the core at this repository's
`.contract` pin, and runs the harness and service of that same commit. The order of authority is:
the contract's Lean text; then the normative harness documents (PROVER.md, FORMAT.md, PROTOCOL.md)
and the season files (`.contract/harness/season.toml`, `smoke.toml`); then the design; then this
file. Where two of them disagree, the higher one is what is checked, and the disagreement is a bug
to report.

**Status on 2026-10-23.**

- **v4 is a proposal.** It is implemented on the core's branch `v4/srom-rules` and has not been
  adopted by the user. Every decision taken in the user's absence is listed in design §7, and each
  is reversible.
- **The pin.** `.contract` is at `a874f87`: the core's stages A (contract) and B (harness), merged.
- **One contract change is pending.** The fix pass of review RA (finding RA-M2) adds
  `p.tr.length ≤ S.qV` to `acc`. It moves the pin once more, before the core's pull request. Below
  it is marked **[pending RA-M2]**.
- **v3 is frozen.** Its rules no longer apply (`README.md`, "Status").

---

## 1. The competition

**The goal** ([CM] §0, the user's statement). The competition wants a very fast prover for BLAKE2s
hash chains first, and a recursion step that is good enough second. It is not after the most
succinct recursive verifier. The 100 ms and 200 ms per-merge targets are reference lines on the
board and do not enter the score (CM-7).

**What an entry is** (design §0). An entry is a hash-based non-interactive argument for one fixed
relation over 32-byte digests:

- a leaf digest commits to a BLAKE2s chain from a secret start;
- a node digest commits to two accepted children.

It consists of:

- **Lean**: a verifier `V` and an honest prover `P`, both query programs; an extractor
  specification `E` and its program `ext`; and a kernel-checked certificate of knowledge soundness
  and completeness in the random-oracle model, **for every public key**;
- **an x86-64 assembly prover**, timed on GitHub-hosted runners. It proves a tree of chains, and it
  extends a running proof chain by chain.

**The score** (V4-10, [CM] §3; seconds, lower is better):

```
S = T_tree + K · t_link
```

- **`T_tree`**, the chain term, is the wall time of one `prover tree` process proving `2^r` chains
  of `n` steps and every node up to the root. It is the median of the repeats. Anything goes inside
  the process: flattening, bundling, proof of parent, grinding (design §3.5).
- **`t_link`**, the recursion term, is measured on **the stream** ([CM] §3.3). `M` fresh chains of
  length `n_f` arrive one at a time. Each is proved by a `leaf` request and folded into the running
  proof by a `node` request. Every request is a fresh process: its start-up is untimed, and it is
  timed from its inputs to its output. Then:
  - `t_leaf` = (the sum of the `M + 1` leaf times) / `M`;
  - `t_merge` = (the sum of the `M` merge times) / `M`;
  - `t_link = t_leaf + t_merge`, the median of the repeats (`.contract/harness/rfh/bench.py`,
    `score`).

  A link may also be done 1→1: the `leaf` request outputs a cheap witness-sending leaf, and the
  `node` request proves the chain inside the step (CM-4). Under v4 that leaf output must still
  pass `acc`. Every link absorbs the running proof either way.
- **`K`** weights the two terms. It is 20, **provisional**: it is recomputed each season from the
  leading entry, so that recursion is a stated minority share of the leader's score ([CM] §3.4).
- **Published beside `S`**:
  - the recursion overhead `o_est = t_link − T_tree · n_f / (2^r · n)`;
  - the slowest merge;
  - the calibration columns (§5.2).

**The shapes** (V4-11; `.contract/harness/season.toml`, `smoke.toml`):

| Parameter | Season 1 | Smoke (CI) |
|---|---|---|
| tree depth `r`; leaves and nodes | 6; 64 leaves, 63 nodes | 2; 4 leaves, 3 nodes |
| chain length `n` | `2^18` (`2^24` compressions per tree) | 16 |
| stream: links `M`, chain length `n_f` | 512, `2^16` | 4, 16 |
| `K`; `T_V` ratio `R` | 20; 10, enforced | 20; 10, reported only |
| repeats (tree, stream); medians | 3, 3 | 1, 1 |
| samples; canaries per kind; DoS inputs | 16; 8; 1,000 | 16; 8; 64 |
| liveness shape | `r = 1`, `n = 16` | the same |

**What is ranked** (design §3.6, §7.3; V4-15).

- **What can be ranked.** Only a result with the verdict **ACCEPT** at the season shape can be
  ranked: its certificate checked, and every benchmark check passed. Records are taken only by a
  paired comparison within one job (§8).
- **PROVISIONAL** is the verdict of an entry whose Lean builds but whose certificate does not
  check. Its benchmark runs and is published, but it is marked `comparable: false` and is never
  ranked or recorded.
- **Today nothing is ranked.**
  - No certified entry can run the season-1 shape (design §0, §2.8, C-m10, and §7 below).
  - The first ranked shape is to be set from the first certified entry that runs (design §4.3,
    §7.3).
  - `K` is provisional.

## 2. The relation, acceptance and the oracle

### 2.1 The relation (`Relation.lean`)

```lean
abbrev Digest := Vector UInt8 32
abbrev Proof  := ByteArray
abbrev Trace  := List (ByteArray × Digest)    -- (query, answer), in the order the verifier asks

structure Sig where
  idx  : ℕ              -- the one-time key's index (below 2^16 for a valid signature)
  ots  : List Digest    -- the WOTS chain values (133 for a valid signature)
  path : List Digest    -- the Merkle siblings, leaf level first (16 for a valid signature)

structure Signed where
  π  : Proof            -- the proof
  tr : Trace            -- the oracle answers the verifier reads
  σ  : Sig              -- the service's signature on the digest of tr

inductive Wit
  | leaf (s : Digest) (n : ℕ)
  | node (c₁ c₂ : Digest) (p₁ p₂ : Signed)

def Rel (acc : Digest → Signed → Bool) : Digest → Wit → Prop
  | c, .leaf s n         => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ p₁ p₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true
```

**Byte layouts** (normative; the contract, the service and the runner hash the same bytes). Every
hash is public BLAKE2s-256, and the first byte is a tag:

| Hash | Input |
|---|---|
| `chainStep d` | `0x43 ‖ d` (`C`) |
| `leafStmt h n` | `0x4C ‖ h ‖ enc64 n` (`L`) |
| `nodeStmt c₁ c₂` | `0x4E ‖ c₁ ‖ c₂` (`N`) |
| `traceDigest tr` | `0x54 ‖ item₀ ‖ item₁ ‖ …`, with `itemᵢ = enc64 \|qᵢ\| ‖ qᵢ ‖ aᵢ` (`T`) |
| signature hashes | WOTS chain step `0x57` (`W`), key leaf `0x4B` (`K`), key-tree node `0x4D` (`M`) (design §1.3) |

- `enc64 n` is the 8 little-endian bytes of `n mod 2^64`.
- `chainCap = 2^20`.
- **What changed from v3** (V4-16):
  - the tree, the leaf clause and the statements are v3's;
  - the node clause is new: a child is judged by `acc` on a signed proof, not by running `V` on a
    public hash.

### 2.2 Acceptance (`Certificate.lean`, `Submission.acc`)

```lean
def Submission.acc (S : Submission) (vk c : Digest) (p : Signed) : Bool :=
  decide (p.π.size ≤ proofCap) &&                       -- 1. |π| ≤ 2^20 bytes
  -- [pending RA-M2]: decide (p.tr.length ≤ S.qV) &&   -- 1b. at most qV trace entries
  decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) &&           -- 2. every query ≤ 2^20 bytes
  SigOk vk (traceDigest p.tr) p.σ &&                    -- 3. σ signs the trace's digest under vk
  decide ((S.V vk c p.π).runSeq p.tr = some true)       -- 4. V accepts, reading its answers from tr
```

- **One predicate for everything** (V4-7). `acc` is used in four places:
  - the relation's node clause;
  - the harness's check of every proof it is given (root, samples, canaries, every stream output);
  - the badge `verify`;
  - any third party's later check with the published `vk`.

  It never evaluates the oracle and needs no service.
- **The order of the conjuncts** is cheapest rejection first (V4-A3, C-m5). A bogus proof costs a
  signature check, not a run of your verifier.
- **[pending RA-M2].** The fix pass of review RA inserts `decide (p.tr.length ≤ S.qV)` after the
  size cap.
  - It is not at `a874f87`.
  - The core's `harness/FORMAT.md` at the pin already describes it.
  - Once it lands, the pin moves (`CLAUDE.md`, "The pin").
  - A recursive verifier that restates `acc` must mirror it (F1 §7.3; the adaptation is the last
    entry of `docs/v4/flock-baseline/stages/F1-lean-JOURNAL.md`).

**`runSeq`, exact consumption** (`Oracle.lean`; V4-4, V4-A3). The `i`-th query is answered by the
`i`-th trace entry, which must be for that query. The result is `none`:

- on a mismatch;
- if the trace runs out;
- if entries are left over.

So the signed trace is exactly `V`'s query sequence on those answers, and nothing after it.

### 2.3 The oracle (V4-2, V4-3; design §3.2; PROTOCOL.md)

For every timed run the runner starts a **service**: one per tree repeat, one per stream repeat,
and one for the liveness run.

- **Keys.** It draws a fresh PRF key `k` and an **independent** signing seed. The seed gives
  `(sk, vk)`: a Merkle tree of `2^16` WOTS one-time keys (`w = 4`, 133 chains), with `vk` its root.
  Neither key leaves the service process.
- **Reaching it.** The prover reaches it only through the Unix socket in `RF_ORACLE`. It offers
  three operations, and nothing else:
  - **`QUERY`**: a batch of byte strings in, their answers `PRF_k(q)` out. `PRF_k` is BLAKE2s-256
    keyed by `k` (RFC 7693 keyed mode, a 32-byte key). Queries carry **no tag**; the empty query is
    allowed.
  - **`SIGN`**: a batch `q₀ … q_{m−1}` in. The service recomputes the answers and returns them,
    with a signature on `traceDigest [(q₀, a₀), …]` made with the next unused one-time key.
    `m = 0` is allowed: that is a signature on the digest of the **empty trace**.
  - **`VK`**: the public key. The runner also writes it to `DIR/vk.hex`.
- **What it does not do.**
  - It keeps no answer table, so no state passes between requests except the 16-bit signature
    index (V4-A5, C-m2).
  - It has no other operation. In liveness mode it logs every query it evaluates, and the prover
    cannot tell.

**Why it closes v3's O-25** (design §2.3). A backdoor needs a value about the deployed oracle that
`V` holds without asking it. With a key drawn after `V` is frozen, none exists: recognising
`PRF_k` would distinguish it from a random function. The v3 backdoor is still certified in the
model (`Controls/Backdoor.lean`, `backdoor`), and in deployment it never fires.

### 2.4 What the signature is, and what it is not (design §2.2)

- **It is** the service's statement that the answers in `tr` are `PRF_k`'s for this run.
  - `acc` trusts it, and so do the relation's node clause and the harness.
  - Unforgeability is used **once**, outside every certificate: in the composition argument
    across the tree (design §2.4, `Library/Compose.lean`).
- **It is not knowledge, and a certified `V` can never trust it.**
  - The certificate quantifies over **every** `vk`, against an unbounded adversary that may hold
    `sk`.
  - Suppose a branch of `V` accepts a false statement because the proof carries something that
    adversary can always produce: a valid signature, `sk`, or a signed answer that agrees with the
    oracle. Then the branch has no knowledge state below error `1/q`, where `q ≤ qV ≤ 2^16` is its
    number of queries. So it has none at `errorCap = 2^-128`.
  - Kernel controls: `Library/SigTrust.lean`, `sigTrust_kstate_iff`; `Controls/Certificate.lean`,
    `sigTrust_no_certificate`.
- **What `V` may do.** A node verifier may check signatures as part of proving its children's
  `acc`, but its extractor must still output the children. A signature may serve to make the
  extracted witness a member of `Rel`, never as a substitute for a witness. The σ0-bundle of §7.1
  is such a use: BLUEPRINT §5 explains why C-m1 does not bite there.

## 3. What you submit

### 3.1 The submission and the certificate (`Certificate.lean`)

```lean
structure Submission where
  V : Digest → Digest → Proof → OProg Bool     -- vk, statement, proof
  P : Digest → Digest → Wit → OProg Proof      -- vk, statement, witness
  E : Digest → Proof → Log → Option Wit        -- no vk (V4-6)
  ext : XProg                                  -- the extractor as a program of the contract's machine
  ε : ℝ≥0                                      -- knowledge error per fresh query
  δ : ℝ≥0                                      -- completeness error
  qV : ℕ                                       -- bound on V's queries
  fuel : ℕ → ℕ                                 -- ext's steps on a tape of t words

structure Certificate (S : Submission) : Prop where
  secure   : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV
  complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ
  computes : Computes S.ext S.E S.fuel
  cap      : S.ε ≤ errorCap ∧ S.δ ≤ completenessCap ∧ S.qV ≤ 2 ^ 16 ∧
             (∀ t, S.fuel t ≤ extractorBudget t) ∧ S.ext.body.size ≤ progCap

structure CertificateR (D : Declared) (S : Submission) : Prop extends Certificate S where
  bounds : S.ε ≤ D.ε ∧ S.δ ≤ D.δ ∧ S.qV ≤ D.qV ∧
           ∀ t, S.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t
```

The obligations, in words (`Security.lean`, `Extractor.lean`; v3's definitions word for word,
V4-1):

- **Knowledge soundness** (`KS`), for every `vk`. You exhibit a potential `μ` on query logs with
  three laws:
  - `empty`: it starts at 0;
  - `step`: on a log of fewer than `logCap = 2^96` entries, a fresh query raises it by at most `ε`
    on average over the `2^256` answers;
  - `final`: below 1, every proof `V` accepts reading the log (`runLog`) is extracted by `E` to a
    witness of `Rel (S.acc vk)`.

  Separately, `V` asks at most `qV` queries on every input and **every oracle function**. The
  paper theorem gives the error `(Q + qV)·ε` (`Library/PaperTheorem.lean`, `paper`).
- **Completeness with error** (`CompleteWithError`). On **every** statement and witness of the
  relation, for every `vk`, the honest proof is rejected with probability at most
  `δ ≤ completenessCap = 2^-128`. The proof is made by `P` and checked by `V` against one lazily
  sampled random oracle. Grinding is admitted.
- **`Computes`.** On every statement, every proof of at most `proofCap` bytes and every log whose
  tape the machine can address, `ext` halts within `fuel t` steps. Its output has at most
  `outCap = 2^24` words and decodes to `E`'s result. Also `fuel t ≤ B t = 2^48 + 2^16 · t`, and
  `ext` has at most `progCap = 2^20` statements.
- **Caps.**
  - `ε ≤ errorCap = 2^-128`;
  - `δ ≤ 2^-128`;
  - `qV ≤ 2^16`.

**What changed from v3.**

- `V` and `P` take `vk`; `E` does not (V4-6). A design that needs `vk` in the extractor writes it
  into `π`.
- The certificate holds **for every `vk`**.
- There is no RISC-V image: `ext` is a Lean term run by the compiled contract interpreter.
- `Vb`, `blake2sOracle` and `tagRO` are gone.

**The reference entry.** The organiser's library has a complete witness-sending entry,
`.contract/RecursionFast/Library/WitnessSending.lean`:

- `V` asks no query; `P` sends the witness;
- `E = decode`; `ext` is a 21-statement copy program, 8 steps per word;
- `certificate : Certificate submission` holds under every key.

Its `E`, `ext`, `fuel` and `computes` are reusable: `spartan-srom` uses them unchanged (BLUEPRINT
§4).

### 3.2 The claim and the challenge (`.contract/harness/challenge/Challenge.lean.in`, `render-challenge.py`)

`claim.json` holds the declared numbers, and nothing else:

```json
{"error": "1/680564733841876926926749214863536422912", "completeness_error": "0",
 "qV": 65536, "fuel_base": 0, "fuel_per_word": 8}
```

**Schema.**

- The key set is exactly these five.
- `error` and `completeness_error` are strings `"a"` or `"a/b"` of decimal digits, with `b > 0`.
  They are rendered as `ℝ≥0`.
- `qV`, `fuel_base` and `fuel_per_word` are JSON integers in `[0, 2^64)`.
- The declared fuel is `fuel t = fuel_base + fuel_per_word · t`.
- Floats, `NaN`, `Infinity` and duplicate keys are rejected.

**Rendering.** The harness renders the organiser's stub with the claim. The entry supplies no stub.
Your `lean/Solution.lean`:

- copies the rendered stub **verbatim**: `namespace RecursionFast.Challenge`, and
  `noncomputable def declared : Declared` exactly as rendered;
- defines `def submission : Submission`;
- proves `theorem certified : CertificateR declared submission`.

The comparator checks that `certified` proves exactly the rendered statement, with `submission`
the only definition that changed. The badge's liveness check runs `ext` with the declared fuel.
`submissions/spartan-srom/lean/Solution.lean` is a worked example.

### 3.3 The entry's layout (`.contract/harness/evaluate.py`, `harness/ci/fetch-entry.sh`)

```
submissions/<root>/
  claim.json               the declared numbers (§3.2)
  lean/Solution.lean       module `Solution`: `RecursionFast.Challenge.submission` and `certified`
  lean/<Prefix>….lean      your other modules, flat in lean/ (`lean/Foo.lean` is the module `Foo`)
  prover/*.s               the submission's prover: x86-64 GNU as, linked by the runner (§4)
  prover/…                 the sources the .s is generated from and the script that does it (unbuilt)
  README.md                recommended: what the entry is, what is proved, the measurements
  NOTES.md                 expected: the untrusted journal (§8)
  LICENSE-…                the licence of any code you derived from elsewhere
```

- **Lean modules.**
  - Every `.lean` file directly in `lean/` becomes a module of one generated library. The harness
    ignores any lakefile, `leanOptions` and `moreLeanArgs`, and it does not read subdirectories of
    `lean/`.
  - Module names must be fresh: no module root may exist in the organiser's build, the toolchain or
    any package, so not `RecursionFast`, `Mathlib`, `CompPoly` and so on. `Challenge` is the
    rendered stub's. Use a prefix that names the entry, as `SpartanSrom…` does.
- **Files.** The root holds only regular files and directories, so no symbolic link and no special
  file (`fetch-entry.sh`). An entry pull request changes exactly one root (§8).
- **The layout rules of a root** are in `submissions/README.md`.

### 3.4 The extractor's tape and output (`Extractor.lean`)

- **Input tape** `extractorInput c π L`, in 64-bit words, unchanged from v3:
  - the statement (4 words);
  - `|π|` and `π`, its bytes packed eight per word, little-endian;
  - `|L|`;
  - for each log entry: `|q|`, `q` packed, and the answer (4 words).
- **Output.** The words denote a witness through `decodeWit`, which reads **strictly** from the
  front: a field that runs past the end denotes nothing, and trailing words are ignored.
  - **A leaf** is 6 words: tag `0`, the start (4), the length (1).
  - **A node** is tag `1`, the two child digests (8 words), then each child's signed proof:
    - the proof: a length word, then the packed bytes;
    - the trace, laid out as a log: `1 + Σ (5 + ⌈|q|/8⌉)` words;
    - the signature: the index, then 133 chain values and 16 path digests. That is
      `1 + 4·133 + 4·16 = 597` words, **4,776 bytes, for every signed child**.
  - So a node witness is `9 + Σ_children ((1 + ⌈|π|/8⌉) + (1 + Σ_entries (5 + ⌈|q|/8⌉)) + 597)`
    words, and it must fit `outCap = 2^24`.
  - A node whose children's traces do not fit cannot be extracted, so its verifier cannot be
    certified (C-m11).

## 4. The prover

### 4.1 Interface (PROVER.md §3)

| Invocation | Inputs in the working directory | Outputs | Timed |
|---|---|---|---|
| `prover setup /setup` (optional) | none: no instance, no service, `/setup` writable | anything under `/setup`, read-only afterwards | no (`setup_s` = 1 h) |
| `prover tree /work` | `leaves.json` = `{"n": N, "starts": ["HEX", …]}`, `vk.hex`, the service | `proofs/L<i>.bin` for each leaf; `proofs/N<l>_<j>.bin` for each inner node (`l = 1 … r−1`; node `j` of level `l` joins nodes `2j`, `2j + 1` of level `l − 1`); `root.bin` | yes, from `exec` to exit (`tree_s`) |
| `prover leaf /work` | `leaf.json` = `{"n": N, "start": "HEX"}` | `proof.bin` | yes (`step_s`) |
| `prover node /work` | `child1.stmt`, `child1.bin` (the running statement and proof), `child2.stmt`, `child2.bin` (the new leaf's) | `proof.bin`, a signed proof of `nodeStmt child1 child2` | yes (`step_s`) |

- **The stream handshake** (CM-6).
  1. The process starts with `vk.hex` already present, loads its setup, and prints `ready`.
  2. The runner starts the clock, writes the inputs by atomic renames, and writes `go` on stdin.
  3. The clock stops when the prover prints `done` or exits.

  One request runs at a time, and nothing survives a request except the proof the runner copies.
- **What the runner never gives you.** It never passes a digest to `tree` and never passes a start
  to `node`. Compute statements with exactly the contract's `leafStmt`, `nodeStmt`, tags and
  `enc64` (§2.1). Statements and keys are 64 lowercase hex characters, with an optional newline.
- **Every output is a signed-proof file** (§4.4).

### 4.2 The sandbox (PROVER.md §2; B-RESULT §5.1)

The prover runs under `bubblewrap`, with:

- **namespaces**: new user, pid, network, ipc, uts and cgroup namespaces; no capabilities; an
  empty environment except `RF_ORACLE=/run/rf/oracle.sock`, `RF_SETUP=/setup`, `HOME=/work`,
  `TMPDIR=/tmp` and `PATH=/prover`;
- **a filesystem** that is a read-only root holding only:
  - the binary, `/setup` and `/work`;
  - the socket;
  - a private `/tmp`, which counts against the memory cap;
  - a minimal `/dev` and its own `/proc`;
  - the CPU topology.

  There is no `/usr`, no shell and no network.
- **a seccomp filter** that fails `ptrace`, `process_vm_*`, `bpf`, `perf_event_open`,
  `userfaultfd`, `io_uring`, keyrings, mounts, namespaces and module loading;
- **resources**:
  - every CPU of the machine, shared with the service;
  - a memory cgroup of `memory.prover` = `11G` in both season files (11 GiB, as a systemd size);
  - `oom_score_adj = 1000`, so under pressure the kernel kills the prover, never the service.

When a request ends, every process it started is killed. A GitHub-hosted `ubuntu-24.04` runner has
4 vCPU and 16 GB (design §3.1).

### 4.3 The service, from the prover's side (PROTOCOL.md)

- **Messages.** A 16-byte header, then a body; integers are little-endian.
- **Caps.** Each is refused as an error, which closes the connection and aborts that proof:
  - a query of at most `2^20` bytes;
  - a request body of at most `2^24` bytes (16 MiB);
  - at most `2^18` items per `QUERY` and `2^16` per `SIGN`;
  - at most 64 connections;
  - **`2^16` signatures per service lifetime**: a tree repeat, a stream repeat, the liveness run.
- **Batch, and use one connection per thread.**
  - One round trip costs about 31 µs (median; B-RESULT §3).
  - Batches of 4,096 queries of 64 bytes reach 6.6 M calls/s on one connection, and 25.3 M calls/s
    on 4 CPUs with 4 connections.
  - The service hashes eight equal-size queries at a time with AVX2.
  - It computes on **your** CPUs, so it is not a co-processor.
- **The trace you sign must be `V`'s exact query sequence on those answers.**
  - Obtain the answers through `QUERY` while proving.
  - Then send one `SIGN` per output with that sequence. The service recomputes every answer and
    signs.
  - The way that works: replay your native verifier against your answer table and record its
    queries in order. Compare the `SIGN` answers with the replay (F2 §1, "Traces").

### 4.4 The signed-proof file (FORMAT.md)

```
u64 |π| ‖ π ‖ u64 m ‖ (u64 |q_i| ‖ q_i ‖ a_i) for i < m ‖ u64 idx ‖ ots_0 … ots_132 ‖ path_0 … path_15
```

- **Integers** are `u64` little-endian; digests are 32 bytes.
- **Size**: the file is `8 + |π| + 8 + Σ (8 + |qᵢ| + 32) + 8 + 4,768` bytes.
- **Strict**: a file that is not exactly one encoding is rejected, whatever it holds.
- **File cap**: the runner does not read a file above 64 MiB (`file_cap`).
- **`SIGN`'s wire format** carries the index as `u32`; the file carries it as `u64`.
- **The extractor's word format** (§3.4) holds the same fields, but pads `π` and every query to
  whole words. The badge parses the file at byte level, in linear time.

### 4.5 The assembly route that works (V4-9, V4-A6; F0 §1, F2 §2, `submissions/spartan-srom/prover/`)

The runner builds only `prover/*.s`. Inside the build sandbox it runs:

```sh
gcc -static -O2 -pthread /build/*.s -o /build/prover -lm
```

It uses the runner image's `gcc`, `as`, `ld` and static glibc, and only copies of the `.s` files
are visible to it. Write the prover in any language and submit the compiler's output.

**std Rust with dependencies works.** The recipe is `submissions/spartan-srom/prover/build-asm.sh`:

```sh
cargo rustc --release --offline --locked --bin NAME \
  --config 'profile.release.lto="fat"' --config 'profile.release.codegen-units=1' \
  --config 'profile.release.panic="abort"' --config 'profile.release.debug=false' \
  -- --emit asm=WORK/raw.s -C target-cpu=x86-64-v2 -C llvm-args=-align-all-functions=4 \
     --remap-path-prefix "$PWD=NAME" --remap-path-prefix "$HOME=~"
python3 -I sanitize-asm.py WORK/raw.s prover/prover.s      # submissions/spartan-srom/prover/sanitize-asm.py
gcc -static -O2 -pthread prover/*.s -o WORK/prover -lm     # the runner's command, to test the link
```

The pitfalls, each measured:

- **Fat LTO and one codegen unit.** Together they put core, alloc, std and your crate into one
  LLVM module, so `--emit asm` prints the whole program.
  - rustc runs LTO only when it also links. Cargo asks for the link; bare rustc needs
    `--emit asm=X,link`. Plain `--emit asm` gives the pre-LTO crate, and `gcc` then reports
    undefined std symbols (F0 §1).
- **LLVM 23's output does not assemble with GNU `as`.**
  - `.prefalign` is unknown to `as`: `-C llvm-args=-align-all-functions=4` avoids it, and the
    filter rewrites it.
  - DWARF-5 `.file N "dir" "file"` lines come in from std's precompiled bitcode, and no stable flag
    removes them. The filter drops `.file N`, `.loc` and `.debug_*` sections, and it refuses
    `.incbin` and `.include`.
- **The result is deterministic.** Two clean builds, another target directory and a copied crate
  give the same `.s` and binary. The harness's sandboxed build gives the same binary hash (F2 §2).
  - Pin the toolchain with a file: F2-m2 notes `spartan-srom` has none.
  - Commit the `.s`, the sources and the script.
- **Sizes.** `spartan-srom`'s `prover.s` is 8,699,228 bytes and its binary 2,698,536 bytes. Its
  `build-asm.sh` took 60.3–61.8 s on the development VM (F2 §2, `logs/f2/build-asm-{a,b,c}.log`).
- **Untested on a runner.** Ubuntu 24.04's `as` is binutils 2.42; the route was run with 2.46. By
  reading, the filtered output uses only classic directives (F2-review §3).
  <!-- TODO(orchestrator): confirm that the runner's binutils 2.42 assembles prover.s (first CI run) -->
- **Other routes that link** (F0 §1): `no_std` with `no_main` on libc (it needs the same filter),
  and C via `gcc -S -O3`.

### 4.6 Run-time CPU dispatch (PROVER.md §1; F2 §2)

- **The runners' CPUs** are heterogeneous: AMD EPYC and Intel Xeon.
  - AVX2 and `pclmulqdq` are expected.
  - AVX-512 and GFNI are not guaranteed.
  - A `SIGILL` fails the run.

  <!-- TODO(orchestrator): the runners' CPU models and their AVX2/pclmulqdq coverage are unconfirmed (design §7.3, "runner facts"); fill in from the first CI runs -->
- **What to do.** Pin a baseline target CPU when you emit the `.s` (`-C target-cpu=x86-64-v2`).
  Choose wider instructions at run time: `is_x86_feature_detected!`, or `cpuid`, cached once, with
  each whole kernel under `#[target_feature]`.
  - Do not use `target-cpu=native`, which bakes in the build host's ISA. Flock and leanVM do this
    (F0 §1, "Caveat").
- **Test both paths.** If your machine lacks an instruction, run under `qemu-x86_64 -cpu Haswell`
  and `-cpu max`, as F2 did for `pclmulqdq` (F2 §2; F2-m7: the hardware path was validated under
  qemu only).
- **Do not debug glibc's start-up.** A static binary linked against glibc 2.43 needs AVX2 at
  start-up, in glibc's own `init_cpu_features`. The runner links with its own glibc (F2 §2).

## 5. The evaluation

### 5.1 The certificate job (`evaluate.py cert`; design §3.1, V4-A1, V4-A2)

It is deterministic and may run on any machine with the package tree. The organiser's checkout is
built, and its olean manifest and import allowlist are written (`harness/org-setup.sh`), before
any entry code is on the machine. Then:

1. **Render** the challenge from the stub and `claim.json`.
2. **The source rule** on `lean/*.lean` (§6), before anything is built.
3. **The comparator** in a fresh tree. It builds your solution **in the sandbox** and replays the
   exported proof of `certified` against the rendered statement.
   - **CI runs the Lean kernel only.** nanoda, the second kernel, does not fit a 16 GB runner: on
     the witness-sending entry it reached 17.6 GB after 10 min 51 s without finishing (B-RESULT
     §3).
   - The result's `kernels` field says which kernels ran, and `second_kernel` says why one did not.
   - The organiser's oleans are checked against the manifest before and after.
4. **Gate tree.** A second fresh tree at the same path rebuilds the solution, byte-identical to the
   comparator-verified build. Then the **gate** runs, rules 1–8 (§6), with `--computable` on the
   badge fields `V`, `P` and `ext`.
5. **The badge.** The executables `verify` (parse plus `accF`, proved equal to `acc`) and
   `liveness` (the contract interpreter on `ext`) are built from your `Solution` module, in the
   sandbox.

The status is one of three:

- `ok`;
- `provisional`: everything builds, and the only failures are an open certificate (the
  comparator's verdict, gate rule 1's `sorryAx`);
- `reject`.

### 5.2 The benchmark job (`evaluate.py bench`, `run-benchmark.py`; design §3.4)

It runs only on the GitHub-hosted runner. Untrusted code runs only in the sandbox. The steps, in
order:

1. **The machine and toolchain record.** The prover is built in the sandbox; the sources' and
   binary's hashes are recorded. Then `setup` runs.
2. **Calibration.**
   - `T_triv,best` is the best of `checker_runs` runs of the organiser's interleaved compiled-Lean
     chain checker over the tree's chains, on one pinned core.
   - The service's calls/s and compressions/s, published beside every score (V4-A5).
3. **The tree repeats.** Each has fresh starts from `os.urandom` and a fresh service. `prover tree`
   is timed. Then, offline:
   - the **root** check: `acc` on the runner's `treeRoot` digest;
   - 16 **samples**;
   - the **canaries** of 8 leaf and 8 node proofs (§7.6).
4. **The DoS column** (§7.6).
5. **The stream repeats.** Each has a fresh service, shared by its requests. Every output is
   checked with `acc`, within `T_V`.
6. **Liveness** at `r = 1`, `n = 16`.
   - The service runs in logging mode, so its log is the complete, authentic query log.
   - `ext` runs on the root's tape with that log, within the declared fuel. The output must decode
     to a witness: `Rel` for a leaf, and for a node `acc` on the extracted children, recursively.
7. **The score**, and the result JSON.

**`T_V`** (V4-12). One `acc` check must take at most `T_triv,best / R`, with `R = 10`.

- It is measured as the badge's in-process time of parsing the file plus `accF`, on one pinned
  core.
- It applies to the root, the samples and every stream output.
- It is enforced at the season shape and only reported at the smoke shape.
- On the development VM, `T_triv,best` = 3.097 s at the season shape, so `T_V` = 310 ms (B-RESULT
  §3).
  <!-- TODO(orchestrator): T_triv,best and T_V on a GitHub runner (no CI run yet) -->

**Splitting.** A GitHub-hosted job ends after 6 h. With `split` (the default), the benchmark is six
jobs:

1. calibration, one tree repeat, the DoS column and liveness;
2. one tree repeat;
3. one tree repeat;
4. one stream repeat;
5. one stream repeat;
6. one stream repeat.

Each job builds the prover and calibrates `T_V` on its own machine. `aggregate.py` takes the
medians and marks a result whose jobs ran on different CPU models `mixed_cpu`.

### 5.3 What fails a run (PROVER.md §5; B-RESULT §7)

The first failure ends the evaluation with REJECT:

- the prover does not build, or `setup` fails;
- `tree` exits non-zero;
- an output is missing, is not a regular file, or is over `file_cap`;
- `acc` rejects any output it is asked about: the root, a sample, or any stream output;
- `acc` accepts a canary;
- a check takes longer than `T_V` (season shape) or `verify_s`;
- a timeout (`tree_s`, `step_s`, `stream_s`);
- the service dies (it is never restarted: a restart is a new key);
- a stream link is not accepted. **The stream is pass/fail link by link**: every one of the `M`
  links must be accepted;
- liveness fails to extract a witness;
- a DoS input is accepted, or crashes the verifier.

### 5.4 Verdicts and attested results (design §2.7, §3.1; `.contract/.github/workflows/evaluate.yml`)

**The verdicts:**

- **ACCEPT**: the certificate is `ok` and the benchmark passes;
- **PROVISIONAL**: the certificate is `provisional` and the benchmark passes;
- **REJECT**: anything else;
- **ERROR**: a harness fault.

**The result JSON** (`recursion.fast/v4/result-1`) binds:

- the verdict;
- each run's `vk`, the CPU models and the runner image;
- the harness commit;
- the service, badge and prover hashes;
- the season and its hash;
- every measured number.

**The attestation.** A separate `attest` job, which runs no entry code, signs the JSON with a
GitHub artifact attestation. A result counts only if this passes:

```sh
gh attestation verify result.json --owner scaraven \
  --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml
```

**PROVISIONAL** (V4-15, C-m13).

- An entry whose Lean builds but whose certificate does not check (a `sorry`, a failed comparator)
  may be benchmarked when a maintainer approves.
- Its source rule, gate rules 2–8 and the sandbox stay mandatory.
- Its result says `comparable: false`, because a `T_V` calibration means nothing without a
  certified `qV`. It is never ranked or recorded.

### 5.5 Caps and limits

| Cap | Value | Where |
|---|---|---|
| `proofCap` (on `π` only) | `2^20` bytes | `acc` |
| `queryCap` (each trace query) | `2^20` bytes | `acc`, the service |
| trace length | `≤ qV` **[pending RA-M2]** | `acc` |
| `qV` | `≤ 2^16` | `Certificate.cap` |
| `ε` (`errorCap`), `δ` (`completenessCap`) | `≤ 2^-128` each | `Certificate.cap` |
| `logCap` (logs the knowledge laws cover) | `2^96` entries | `Security.lean` |
| extractor fuel | `fuel t ≤ B t = 2^48 + 2^16·t` | `Certificate.cap`, `CertificateR` |
| extractor program; output | `2^20` statements; `2^24` words | `progCap`, `outCap` |
| `chainCap` | `2^20` steps | `Rel` |
| signed-proof file the runner reads (`file_cap`) | 64 MiB | season file |
| one `acc` check (`verify_s`) | 60 s | season file |
| one `acc` check, season shape | `T_V = T_triv,best / 10` | §5.2 |
| prover build (`build_s`); `setup` (`setup_s`) | 1 h each | season file |
| tree run (`tree_s`) | 1 h (season), 300 s (smoke) | season files |
| stream request (`step_s`); stream repeat (`stream_s`) | 600 s and 4 h (season); 120 s and 30 min (smoke) | season files |
| memory | prover `11G`, service `2G`, badge `4G`, separate cgroups | `[memory]` of the season files |
| comparator run (both kernels) | `14G` cap; 1 h per Lean step | `evaluate.py` (`--cert-mem`, `--timeout`) |
| service | `2^16` signatures per lifetime; `2^18` items per `QUERY`, `2^16` per `SIGN`; 16 MiB body; 64 connections | PROTOCOL.md §3 |
| GitHub-hosted job | 6 h; 4 vCPU, 16 GB RAM, 14 GB disk | design §3.1 |

<!-- TODO(orchestrator): the certificate job's build caps from a runner measurement (design §3.1, TODO(B)); limits on files and bytes per root (none fixed) -->

## 6. Allowed imports and hard rules

The source rule (`.contract/scripts/source-rule.py`) and the gate
(`.contract/harness/lean-tools/Gate.lean`) check these, except where a rule says otherwise.

- **Axioms.** Only `propext`, `Classical.choice` and `Quot.sound` (gate rule 1, on `certified`).
  - **No `sorry`.** A `sorry` (`sorryAx`) in the certificate's closure makes the entry
    PROVISIONAL at best, never ACCEPT (§5.4).
  - **No `native_decide`**: it adds `Lean.ofReduceBool`.
- **No `unsafe`, `partial` or `opaque`** (gate rule 2; the source rule also rejects `unsafe` and
  `partial`). Your verifier and decoders are total by construction or by a termination proof.
- **No code-changing attributes**, anywhere in your modules (gate rule 3): `implemented_by`,
  `extern`, `export`, `init` and `builtin_init` (so no `initialize`), `csimp`, `cpass`,
  `computed_field`. `inline`, `noinline`, `specialize` and similar hints are fine.
- **No elaboration-time code** (the source rule). It runs before anything is built, with a lexer
  and a raw word scan that also covers comments and strings, so reword a rejected word in a
  comment. It rejects:
  - `#eval` and every `#`-command except `#check`, `#print`, `#reduce` and `#guard_msgs`;
  - `run_cmd`, `run_meta`, `elab`, `macro`, `syntax` and simprocs;
  - `initialize` and `register_…`;
  - compiler and debug `set_option`s;
  - `import Lean…`, `open Lean…`, `import Qq…`, `import Lake…`.
- **Imports** (gate rules 6–8).
  - **What you may import.** Your modules may import only modules in the import closure of
    `Mathlib`, `RecursionFast.Contract`, `RecursionFast.Library` and `RecursionFast.Controls` at the
    pin. `org-setup.sh` writes that closure to `ORG/.lake/rf/allowlist.txt`. You may also import
    your own modules.
  - **Not the compiler.** No definition of yours may refer to the compiler's or the environment's
    internals (rule 7). The module that declares `submission` may reach only your own modules and
    the allowlist closure (rule 8).
  - **CompPoly.** v3 admitted CompPoly's `BF64` and `Ext3` as the organiser's field library.
    - The v4 closure at the pin does not contain CompPoly, and the olean manifest covers only that
      closure. F3's `org-setup.sh` at the pin wrote an allowlist of 10,787 modules and a manifest
      with no CompPoly entry (`logs/f3/org-setup.log`, `logs/f3/org/.lake/rf/`).
    - So with the default `org-setup.sh` roots, the gate treats CompPoly's modules as untrusted.
    - `CompPoly.Fields.Binary.BF64.Ext3` reaches `CompPoly.Fields.Extension.Arithmetic`, which
      registers a `@[csimp]` lemma (gate rule 3).
    - `spartan-srom` imports `BF64.Bytes` and `BF64.Ext3`.

    <!-- TODO(orchestrator): confirm with the F3 harness run whether an entry may import CompPoly at the pin (and whether CI builds it), or whether the core adds it to the org-setup roots; until then, vendor what you need into your own modules, with its licence -->
- **Fresh module names** (§3.3).
- **The badge needs compiled code.**
  - Gate rule 4 requires compiled code for the badge-path fields `V`, `P` and `ext`.
  - **The badge also compiles `S.accF` with `S := RecursionFast.Challenge.submission`, so the whole
    `submission` must be computable**, its `ε` and `δ` included (F1 §7.1).
  - A `noncomputable` field that rule 4 accepts still fails the badge build (§7.5).
- **Statements are the organiser's.** You fill the challenge's `submission` and `certified`.
  Everything else in `Solution.lean` is the rendered stub, verbatim.
- **Bind the statement into every Fiat–Shamir seed** (C15). This is a rule of this rulebook, not
  of the contract; the statement-bit canary checks it (§7.6).
- **Controls.** Give every definition your certificate relies on a positive and a negative
  control, so that no statement is vacuous. `spartan-srom`'s `SpartanSromNodeControls` is the
  pattern.
- **The compiled code is what runs.** The comparator and the gate check kernel terms, while the
  badge runs what Lean's compiler emitted from your elaboration (O-12, design §2.7 item 5). Do not
  build on any gap between the two.

## 7. Consequences that bite

Each item below follows from the rules and was measured, proved or estimated by the first v4 entry
(`spartan-srom`: v3's Spartan+Ligero leaf SNARK over GF(2^64)/GF(2^192), with σ0-bundle nodes) or
by the core's stages. Times are from the shared development VM (32 vCPU QEMU, no `pclmulqdq`, under
load), not a runner, so read them as relative.

### 7.1 Size

- **Witness-sending dies at the first node, because of the traces.**
  - A signed child carries its trace, and the trace restates every byte the verifier hashed: the
    opened Merkle columns, the absorbed prover messages, every node preimage.
  - A signed `n = 16` leaf file is **538,698 bytes, 3.7× its π of 143,711** (F2 §3.3).
  - A plain witness-sending node of two such leaves is **1,089,384 bytes, above `proofCap`** (F1
    §5).
  - Only query-free children (clear leaves, the toy entry) survive plain witness-sending
    (F0-ideation point 1).
- **The σ0-bundle pattern for query-free children** (BLUEPRINT D-2 and §1.4; F1 §2–§3).
  - The shape:
    - the node proof is `encode W ‖ T`;
    - `W` is a clear tree, in which every child slot has an **empty trace** and the same
      signature `σ0`, one `SIGN` of the empty trace;
    - `T` holds the bundled leaves' SNARKs.
  - The verifier checks:
    - the clear tree, with no query;
    - `SigOk vk (traceDigest []) σ0`, **once**;
    - the static query bound `Σ qBound ≤ 2^16`;
    - then each leaf SNARK, with fresh queries.
  - The node's trace is the concatenation of the leaves' traces, and `E` is the library's copy
    extractor, unchanged.
  - `final` holds because the potential already covers every chain in the log, so a bundle of `k`
    SNARKs costs no extra error.
  - C-m1 does not bite: `σ0` serves only to make the extracted witness a member of `Rel`.
  - It grows by **153,367 bytes per leaf** at `n = 16`: 143,663 of SNARK and 9,704 of `W`.
- **`proofCap` bounds the stream.** Every stream output must be accepted. A growing bundle
  completes:

  | `n_f` | links accepted | first rejection |
  |---|---|---|
  | 16 | 5 | link 6 |
  | 1,024 | 1 | link 2 |
  | 4,096 | 0 | link 1 |
  | ≥ 16,384 | 0 | the leaf itself is above `proofCap` |

  (F2 §3.3, `logs/f2/links-n*.log`.) The season stream has `M = 512` links, so its running proof
  must stay bounded: a node that verifies its children and forgets them.
- **A √-size PCS cannot fit the season stream's leaf.**
  - A Ligero leaf proof is 1,464,107 bytes at `n = 2^14` and 2,791,559 bytes at `2^16`, both above
    `proofCap` (F0 §2, F2 §3.3).
  - The season's `n_f = 2^16` needs a polylogarithmic commitment. leanVM's BLAKE2s Flock (WHIR) is
    259,320 bytes at `2^14` compressions (F0 §4).
  - Under `errorCap = 2^-128` per query, GF(2^128) sumcheck rounds do not qualify (2^-127 per
    degree-2 round); GF(2^192) does (F0-ideation Q4, **estimate**).
- **The season shape needs recursion** (design §2.8, §4.2; C-m10).
  - One flat SNARK over the tree's `2^24` compressions is about `2^38` witness bits, 32 GiB
    (F0-ideation point 3, **estimate**), far above 11 GiB.
  - A bundle of 64 leaf SNARKs is far above `proofCap`.
  - The root check gets about a tenth of `T_triv,best` (CM-R7).
  - So the root and every stream output must be a genuine recursive node. Per child, that node
    proves:
    - `V`'s algebra under `runSeq`;
    - the trace's digest, about 1.6 compressions per 64-byte query;
    - one `SigOk`, about 300 compressions on average and 495 at most (design §4.2, **estimate**).
  - No certified entry does this yet, and none has been sized against the caps under v4 (design
    §7.3, C5).
- **4.8 KB per signature slot in `decodeWit`.**
  - Every signed child in an extractor output, and in any proof that uses the library's `encode`,
    carries a full signature: 597 words, 4,776 bytes (§3.4).
  - A clear tree pays this per slot: about 29 KB at `r = 2` and about 605 KB at `r = 6`
    (F0-ideation point 2, **estimate**). That is most of `proofCap` before any SNARK.
  - An extractor program that reads `σ0` once and expands it is possible, but not written
    (F0-ideation).

### 7.2 Memory

- **The prover's cgroup is 11 GiB, including `/tmp`.** The service has its own 2 GiB. At
  `oom_score_adj = 1000` the prover is killed first, and the run fails.
- **Real numbers.**
  - v3's Spartan+Ligero leaf prover peaks at **15.1 GiB at `n = 2^16`** and 3.8 GiB at `2^14` (F2
    §4, `logs/f2/bench-asm-n{16384,65536}.log`, in KiB; F2-m3 corrects the RESULT's units).
  - So at the season's `n = 2^18`, and for the stream's `n_f = 2^16` leaf, memory stops it before
    `proofCap` does.
- **The Lean build** of `spartan-srom` peaks at 4.12 GB (F1 §5). The comparator runs under a 14G
  cap.

### 7.3 The verifier's time: `T_V` is measured on your compiled Lean `V`

The cap is `T_triv,best / 10`, about 310 ms on the development VM, and it covers the parse plus
`acc`, in-process, on one pinned core (§5.2).

**What existing entries cost:**

| What | Time | Source |
|---|---|---|
| `spartan-srom` leaf, `n = 16` | 0.204–0.218 s | F1 §5 |
| `spartan-srom` bundle of two leaves | 0.45–0.50 s, above that cap | F1 §5 |
| the badge's parse plus `acc` on a `2^16`-query trace of 100-byte queries (9.18 MB) | 135–155 ms, of which the trace digest is about 72 ms and the parse about 30 ms | B-RESULT §3 |

So a long trace spends half the budget before your own verifier's work counts.

**How to make `V` fast:**

- **Use the library's word-level twins**, proved equal to the specification (`Library/Fast.lean`,
  `Library/Blake2sFast.lean`):

  | Function | Twin | Reference |
  |---|---|---|
  | one compression | `compressF`, 280 ns | 1,136 ns |
  | per compression, 1 MiB message | `digestB`, 402 ns | 5,488 ns |
  | one `SigOk` | `SigOkF`, 0.23 ms | 2.01 ms |

  (A-RESULT §4.)
- **Never read `π.data` in compiled code.** Compiled code turns `ByteArray.data` into a boxed copy
  of the whole array on every call.
  - v3's `digestFrom` used it 32 times per digest, which made parsing quadratic: 87.8 s for a
    539 KB file and 579 s for 1.08 MB.
  - Reading in place (`π[j]`, proved equal by `rfl`) made it linear (F1 §5; F2 §3.5).
- **Avoid list-based codecs.**
  - The library's `WitnessSending.decode` packs the whole proof into `List Word`, at about
    0.2–0.4 µs per byte: 60 ms for a 297 KB bundle, spent packing SNARK bytes it never reads (F1
    §7.4; A-RESULT §8).
  - `Word = BitVec 64` is a `Nat` at run time, a bignum above `2^63` (A-RESULT §8).
  - Parse bytes with `UInt64` reads, as the badge's `parseSigned` does.
- **Take each child's program lazily** (`Unit → OProg Bool`). A parent rejected by its size cap
  then does not first build its children's programs: 3–7 µs instead of 1.3 s (F1 §6.1 item 6).
- **Bound what a proof can make `V` do.** A clear-leaf branch that recomputes up to
  `chainCap = 2^20` steps costs 0.3–0.6 s at 280–594 ns per step (F1 §6.1 item 8; `chainEndF` at
  594 ns per step, A-RESULT §4), and the DoS column can reach it (§7.6).

### 7.4 The prover's cost under the service

- **Every Merkle hash is a service call** (V4-14). Every oracle query goes through the service:
  Fiat–Shamir and every Merkle hash of every commitment (F2 §4).
  - Merkle batches pushed 525,034 queries (1.09 GB) through the service in 0.594 s, on 16
    connections: about 1.8 GB/s.
  - The sequential Fiat–Shamir transcript costs one round trip per step, 57–78 µs each: 153 steps
    are 8.7 ms at `n = 16`.
  - The oracle was 1.4–10 % of proving, the most at `n = 16`. Going through the service rather than
    hashing in-process cost at most about 4 % at `n = 16`, and less than 1 % above (F2 §4, F2-m4).
  - On a 4-vCPU runner the service's hashing competes with your threads.
  - Batch in requests of hundreds to thousands of queries, keep one connection per thread, and
    stay well under 64 connections. A pool of 60 can race the previous request's closing sockets
    (F2-m6).
- **`SIGN` re-hashes the whole trace** (C-m4; PROTOCOL.md §2.2).
  - It re-evaluates every query of the trace and its digest.
  - A σ0-bundle merge asks no `QUERY`, but its one `SIGN` dominates it: 11–21 ms for 7,066–17,665
    queries, growing linearly with the bundle (F2 §4).
  - One `SIGN` per output.
  - A trace above `2^16` entries, or above 16 MiB of `Σ (4 + |q|)`, cannot be signed in one
    request, so it can never be accepted.

### 7.5 Lean and the toolchain

- **The second kernel, and big case splits.**
  - CI checks with the Lean kernel only (§5.1). A record says which kernels ran, and a later
    re-check with nanoda is possible.
  - In v3, one 64-way `interval_cases` over `BitVec` positions drove nanoda to 41.9–52 GB. A
    structural rewrite brought it to 0.76 s and 33 MB (`.contract/docs/v3-lessons-…md` §4.5).
  - Keep large case splits and `decide` over concrete words out of anything the comparator exports.
    Prove symbolically: kernel evaluation of BLAKE2s costs about 2.4 s per compression (BRIEF §6).
- **A stable `ε : ℝ≥0` against computability** (F1 §7.1; `logs/lean/noncomputable-probe.log`).
  - The badge compiles the whole `submission`. With `ε := (2 : ℝ≥0)⁻¹ ^ 129` or `errorCap` the
    badge build fails with `failed to compile definition, consider marking it as 'noncomputable'`,
    although the gate accepts it.
  - Define `ε` (and `δ`) as a cast from `ℚ≥0`, for example `((1 / 2^129 : ℚ≥0) : ℝ≥0)`, and prove
    it equal to the form your proofs use (`spartan-srom`'s `εR1`, `εR1_eq`).
- **Restating `acc`.** `Submission.acc` takes the submission, so a recursive `V` cannot call it.
  - It restates `acc` (`accWith`) and proves the two equal (`accV_eq_acc`).
  - Every change to `acc`'s conjuncts, RA-M2 included, must be mirrored (F1 §7.3).
- **`KS`'s query bound is over oracle functions** (`∀ H c π, (queries H).length ≤ qV`).
  - A non-functional trace follows no function's path.
  - Node completeness needs every accepted child's trace below `2^64` entries (`Signed.Fits`), so
    `spartan-srom` proved a path-uniform bound (`OProg.AtMost`, 150 lines).
  - RA-M2's conjunct removes that need (F1 §7.2).
  - `qV` must also be **static**: compute your query count from the proof's headers before the
    first query, and reject above the bound. That is the bundle's `Σ qBound ≤ 2^16`.
- **Completeness is for every witness, and the Lean `P` has no signer.**
  - `CompleteWithError` quantifies over every witness of `Rel (S.acc vk)`, for every `vk`. That
    includes node witnesses whose children are any accepted signed proofs of any size.
  - `P` cannot make a signature, so its node proofs send the witness plainly (BLUEPRINT D-5).
  - `V` need not enforce `proofCap` on its own input: completeness is about `V`, not `acc`.
- **Imports outside the closure.** See the CompPoly note in §6.
- **Build products.** A badge executable is about 140 MB (B-RESULT §3). It links every compiled
  object of your import closure, and objects outside the organiser's prebuilt closure are compiled
  in your badge build.

### 7.6 What the runner checks byte for byte

- **Canaries** (`.contract/harness/rfh/checks.py`, `canaries`). For 8 leaf and 8 node proofs, every
  mutation below must be rejected:
  - one byte appended to the file, or removed from it;
  - one bit of the statement flipped;
  - the sibling's statement;
  - one byte appended to `π`, or removed from it;
  - the first trace answer changed;
  - a trace entry appended;
  - a signature chain value changed;
  - the signature index changed.

  So decode strictly: exact lengths, no trailing data, one encoding per value. Exact consumption
  in `runSeq` rejects the appended entry for you.
- **The DoS column.** It runs 1,000 inputs (64 at the smoke shape), and any accept or crash
  rejects:
  - random bytes;
  - **random `π` with the root's genuine trace and signature**: `SigOk` passes, so your `V` runs on
    garbage;
  - bit flips in `π`;
  - bit flips and truncations of the whole file.

  The maximum time is published.
- **Statements bind the children** (C15). The canaries flip a statement bit and swap in the
  sibling, so every Fiat–Shamir seed should bind the statement.
- **Fresh instances.** Starts come from `os.urandom` per evaluation, `setup` sees no instance, and
  a stream process holds one start. Precomputation and proof of parent across requests do not pay
  ([CM] §3.3).
- **The native prover is never proved.** Only its signed proofs are checked, by `acc`. It need not
  agree with the Lean `P`. `spartan-srom` still checks its leaf bytes against the Lean `P` as a
  known-answer test (F2 §3.5).

### 7.7 Local testing

- **The socket path limit.** A Unix socket path must be shorter than 108 bytes (`sun_path`). Rust's
  `UnixStream::connect` fails beyond it, and a deep test directory reaches it.
  - The runner's `/run/rf/oracle.sock` is short.
  - For local tests, connect through `/proc/self/fd/<dir fd>/<name>`, as `spartan-srom`'s
    `service.rs` does for paths of 100 bytes or more (F2 §6 item 4).
- **The harness, run locally.** `CLAUDE.md`, "Commands", has the recipe. Local runs are not
  attested and are not results.

## 8. Submitting

- **One way in.** Open a pull request against this repository that changes files under exactly one
  `submissions/<root>/`, and nothing else.
  - Not `records.json`, `.contract`, `docs/`, another root, or the workflows.
  - The `select` job of `.github/workflows/evaluate-entry.yml` refuses anything else.

  <!-- TODO(orchestrator): the caller workflow is the core's harness/ci-template/evaluate-entry.yml with CORE_COMMIT_SHA set to the pin; it is not yet installed in this repository and has not run on GitHub -->
- **Evaluation needs a maintainer.**
  - A maintainer applies the `evaluate` label, or dispatches the workflow with the pull request's
    number.
  - The labelled head commit is evaluated, fetched by SHA as data. If the pull request moves after
    labelling, the evaluation fails.
  - GitHub's approval of a first-time contributor's workflow run admits the run to compute. It is
    not a verdict.
- **The verdict.**
  - The core's reusable `evaluate.yml`, at the pinned commit, runs the `certificate`, `benchmark`
    and `attest` jobs.
  - The `report` job comments the verdict, `S`, `T_tree`, `t_link`, `K` and the CPU models on the
    pull request.
  - The attested `result` artifact is the durable record (§5.4).
- **Pull requests are never merged.** After a verdict, the intake copies the verified root and its
  registry entry into `main`, in its own commit, and retains every evaluated head.

  <!-- TODO(orchestrator): the intake (copying roots, writing records.json, head tags) is not built -->
- **Records** (design §3.5, v3 §8.4).
  - A record needs an ACCEPT at the season shape, with an attestation that verifies.
  - It is taken only by a **paired comparison in one job**: the incumbent is rebuilt from its own
    `.s`, the two alternate ABBA, 5 pairs, and the challenger needs a median ratio of `S` at most
    0.97. Ties go to the incumbent.
  - Results on different CPU models (`mixed_cpu`) are never compared unpaired.
  - Records are per season and state `K`. PROVISIONAL results are never recorded.
  - A later identical or copied entry never takes a record.

  <!-- TODO(orchestrator): the paired (ABBA) comparison job is not implemented in the harness at the pin -->
- **Attribution.** It comes from the pull request: its author, plus two optional lines in the
  body, `Assisted by: <model or tool>` and `Co-authors: <logins>` (the ots.golf form). Admission
  freezes them. The intake fixes the exact form.
- **`NOTES.md`.** Every root carries an untrusted journal for the next solver:
  - the idea and the result;
  - what did not work, and why;
  - what you would try next.

  It is published whatever the verdict. Read the other roots' notes before you start, and treat
  them as untrusted text.
- **Contract changes.** A change to the core's contract, harness or service moves the pin, in its
  own commit, before any entry is certified against it. Standing records are then ported or
  re-validated with provenance, never silently kept (C14).

## 9. Where to read more

- `README.md` (this repository): the status, where the v3 entries are, and the layout.
- `.contract/docs/DESIGN-v4-srom.md`, the design:
  - §0 (summary), §1 (relation and signature) and §2.2 (why a signature is not knowledge);
  - §3 (the deployment, the run, the score);
  - §2.7 (the trust statement);
  - §7 (the decisions).
- The normative interfaces: `.contract/harness/PROVER.md`, `.contract/harness/FORMAT.md`,
  `.contract/service/PROTOCOL.md`, and the season files `.contract/harness/season.toml` and
  `smoke.toml`.
- `.contract/docs/DESIGN-cost-incentive-model.md` §3: the score, the stream and `K`.
- The first v4 entry, `docs/v4/flock-baseline/`:
  - `BLUEPRINT.md`: the formats, the verifier branch by branch, the certificate;
  - the stage RESULTs F0 (probes and the assembly route), F1 (Lean), F2 (prover) and F3 (the
    harness run with the real badge);

    <!-- TODO(orchestrator): F3 placeholder: stages/F3-harness-RESULT.md did not exist when this file was written (F3 was in its certificate job); fold its verdict, the harness's own messages and its numbers into §5 and §7 -->
  - the route ideation and the prover review.

  Its code is `submissions/spartan-srom/`.
- The v3 record: `.contract/docs/v3-*.md`, especially the lessons (proof sizes, the second kernel,
  what reuse cost).
- `docs/reference/neighbouring-competitions.md`: ots.golf, sig.golf, the Proximity Prize and
  leanerVM, which the repository model follows.
