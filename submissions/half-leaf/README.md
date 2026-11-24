# half-leaf

The SNARK of current leanVM (`leanEthereum/leanVM` at `fdb317982`, its experimental prover), ported to the v6 rules as
faithfully as the contract allows, with a Lean certificate at `ε = 2^-128`, at the season's leaf size `n = 2^17`. It
is #47 (`leanvm-faithful`, `n = 2^18`) re-instantiated at the shape `P17`. Each of the 16 steps is one proof. The
proof commits to the step's 2^17 blocks and proves their Keccak-256 Merkle root; from step 2 on, it also verifies the
previous signed proof inside a fixed circuit `Q`. There is no VM (Route B). `NOTES.md` has the design history, the
numbers and the dead ends.

This is a baseline, not a speed entry. Every leanVM phase that the contract leaves room for runs in its current
leanVM form, with leanVM's Rust code vendored. Where the contract forces a change, or certifiability called for one,
the change and its reason are listed in `NOTES.md`.

## What changed from #47

- **The port to `n = 2^17`.** The shape is `P17`: `logN = 17`, tree rows `κ = 18`, a stacked multilinear in
  `M = 24` variables (`P18`: 25), the WHIR levels at heights 20…16 with the same caps, folds and queries, 18 relayout
  rounds, and the query grinds `[19, 17, 18, 17, 18]`. `|π|` falls from 238,152 to **230,424 B** and `qS` from
  4,349 to **4,106**. The circuit `Q` is re-exported at `P17` (2.83 M entries; 2.87 M at `P18`), and its node blocks
  are re-placed for 2^18-word slots.
- **The generic `Place` record.** The literals of `Q`'s generators (where each node block sits in the stack) are one
  placement record with one decided `Ok`. The generators are generic over `(Place, Shape)`, and each deployed
  generator is proved equal to its `(place17, P17)` instance. The `P18` instance (`place18`) is kept on the
  development branch, outside this root. The prover has the matching table (`r3core::layout::Place`, one per shape).
- **The parametric framework.** Much of the shape-dependent code (the format and schedule, the plan, the extractor's
  descent and copy programs, the node output) is now defined over a `Shape` or over generic heights, with `P17` as
  the deployed instance; the soundness ledger is `Params17`. The port is not fully generic: some modules (the
  certificate's readers, parts of the extractor's induction) state `P17` values as literals, and some module names
  still say `18`. Declarations whose names still said `18` while holding `P17` values were renamed. The prover's shape is a build feature
  (`build-asm.sh --shape p17`), and the embedded circuit carries a shape tag that the build checks.

The claim, the relation, the guard's form, the certificate's chain and the trusted surface are #47's.

## What is proved

- **Relation.** Leaf mode (step 1): `c = leafStmt h 2^17`. Node mode (steps 2–16): `c = nodeStmt c' (leafStmt h 2^17)`.
  The SNARK proves knowledge of `xs` with `|xs| = 2^17` and `dataRoot xs = h`. In node mode it also proves
  `acc vk c' (π', tr', σ')` for the child, and `SigOk vk (traceDigest []) σ_leaf` for the witness-sending right leaf
  that the contract's `Rel` asks for.
- **One shape.** `V` accepts SNARK proofs only for `n = 2^17`. For every other `n ≤ leafCap` (0 and odd sizes
  included) the prover sends the witness (the core library's `WitnessSending`). That is the completeness route, with
  `δ = 0`. The smoke shape (`n = 6`) runs on it.
- **Claim** (`claim.json`): `ε = 2^-128`, `δ = 0`, `qV = 16384`, fuel `2^47 + 8192·t` (the contract's budget is
  `2^48 + 2^16·t`).

## The proof system

1. **Fields**: leanVM's, `K = GF(2^64)` and `E = GF(2^128)`. Each soundness group of size `c/|E|` is ground with
   `g = ⌈log₂(8c/7)⌉` bits, to `≤ 7·2^-131`. leanVM grinds to `2^-125`, which is above the contract's cap.
2. **Transcript**: a hash chain over the contract's signed random oracle. This is forced: the model has only a
   `ByteArray → Digest` oracle, with no permutation and no public hash. Grinds are least-nonce searches. A grind's
   answer is the group's first challenge, and short bind draws keep the grinds off long buffers.
3. **Commitment**: one stacked multilinear `q : {0,1}^24 → K` at rate ¼, with leanVM's largest-first stacking and
   46 lanes per level-0 leaf (43 occupied). The Merkle trees are hashed through the oracle and opened against caps
   (`2^7, 2^6, 2^5, 2^5, 2^5`); leanVM's pruned paths are dropped.
4. **Tree batch**: leanVM's Keccak-f GKR layers, unchanged (12 + 12 layers, RMFE 16-packs, normalized pack rounds),
   over the `2^18` rows of the data Merkle tree (`κ = 18`). Its start and input end are new: a tree-wiring
   sub-protocol connects the rows, a parent row commits its children's raw digests, and the one-byte domain tags
   (`0x48`, `0x44`) are handled in the input end only.
5. **Sponge batch**: a second leanVM Keccak GKR (`κ = 13`) for the hashes the node checks in-circuit: the child's
   trace digest, the WOTS chains of `σ'` and `σ_leaf`, and the statement hashes.
6. **Child verification (Route B)**: the fixed circuit `Q` (2.83 M entries) is the v6 verifier as a season-1 LoopIR
   program (`Q_link ++ Q_sig ++ Q_arith`), proved on season 1's typed backend over `E` (a zerocheck and a wiring
   sumcheck), with a mini-bus for data-addressed reads. `V` evaluates `Φ_Q`, the multilinear extension of `Q`, itself,
   behind season 1's self-fold accumulator: the header carries an evaluation claim `(pt, y)` of `Φ_Q`, and each step
   folds the child's claim with its own. This replaces leanVM's VM and its recursion guest.
7. **Ring switching**: leanVM's Frobenius-map switch. All 53 stacked claims are batched into one (`V` rejects more
   than `J₀ = 1024`; leanVM's bound is 512).
8. **Opening**: leanVM's stacked WHIR with the affine combiner, in the Johnson regime, with an out-of-domain sample per
   commitment. Queries per level are `[110, 45, 28, 21, 18]`. All parameters are frozen constants; the prover derives
   none of them from floating point at run time.
9. **Extractor**: season 1's agreement-set descent, with `FD1`, a quasi-linear one-error Reed–Solomon decoder in the
   contract's machine, at the `P17` heights. The total stays within the fuel `2^47 + 8192·t`.

**Sizes** [exact]: `|π|` = 230,424 B at every step, so the `final` and `every` tracks price the same proof. `V`'s
transcript has 4,106 oracle queries, with 854 nonces. `εFS ≤ 2^-128.09`.

## What is certified

`RecursionFast.Challenge.certified : CertificateR declared submission`, with `declared = Lvm6.declared6` by `rfl` and
`submission = Lvm6.Cert.submission6`. The proof is `Lvm6.Cert.certified6`. Its chain:

- **The shipped `V`.** `submission6` is `submissionOf VSc6 …` with `V := VwithT VSc6`, a byte-level fast parser proved
  equal to the reference one (`VwithT_eq`). `VSc6` reads the start-up constant `guard6 = staticOk6 base6`: if it is
  true, `V` runs the SNARK verifier `VS6` over the deployed circuit instance; otherwise it is `VSoff`, which rejects
  every SNARK proof and accepts only witness-sending ones. `VSc6_eq` (`rfl`) and `submission6_eq` (through
  `VwithT_eq`) identify the shipped term with the proved one.
- **Guard split** (`certified6_guard`). Off (`VSF6_off`): `certified_off`, the witness-sending certificate. On
  (`VSF6_on`): `V`'s SNARK branch equals `VSasm (Φ6 B h) P17`, the composed phase programs, and `certified_on`
  applies. Both cases give `CertificateR declared6`; the certificate does not depend on the guard's value.
  `certified6_tiOf6` holds for every class table `P`, and `certified6_base6` instantiates it at the shipped base.
- **Guard on** (`certified_on`, through `certified_ofD`): the six obligations of `Open6D`.
  - `queries`: at most `qS = 4,106 ≤ qV` queries (`queries_VSasm`, `queriesD`).
  - `refines`: the executable `V` refines the compiled scheme `schemeOf (prog6 Φ6) P17` (`refines6_asm`), with fast
    twins of the hot loops proved equal.
  - `sound`: `KS` at `εFS ≤ 2^-128` (`open6XD_Φ6`, the ledger `Params17.ledger_total`). It chains the phase
    specifications (`phaseSpecs6`: commit and OOD, the tree and sponge batches, the typed phases and mini-bus,
    `ringSpec6`, `openSpec6` on the affine MCA theorem `Lvm6Aff*`) through season 1's Fiat–Shamir compiler
    `KCert ⇒ KState ⇒ KS`. Its extractor obligation is `Xe6`: the per-group bad-event bounds (vacuous here:
    `BL := False`), and, on every accepting history with the good events, `ExtSpec6` returning a witness of `Rel`.
    This uses the node theorem `node6V_Φ6` (the deployed `Q` checks the child) and the reader equalities `child6_eq`,
    `sigLeaf6_eq`.
  - `wBranch`: the extractor decodes witness-sending proofs.
  - `computes`: the extractor program `extX6 DD` computes `EX6D` within `2^47 + 8192·t` (chain scan, `descend6`,
    `FD1`).
  - `size`: `extX6 DD` is within `progCap`.
- **The extractor's domain** (`EX6D`). The contract's `Computes` covers only logs with `|π| ≤ 8·outCap`, entries below
  `2^64` bytes and tapes of at most `2^64` words (`InDomW`). On that domain `EX6D` runs the descent above. Outside
  it, it falls back to season 1's `search`, where no cost is asked. Soundness asks, on every available log, for
  either a witness or the ideal extractor's answer (`ExtEqD`): on the domain `EX6D` equals the ideal extractor, and
  outside it `search` finds a witness.

`#print axioms RecursionFast.Challenge.certified`: `propext`, `Classical.choice`, `Quot.sound`.

## Trusted surface

- The contract at the pin (core `39d3216`), the Lean kernel (replayed by the comparator), and the axioms `propext`,
  `Classical.choice` and `Quot.sound`. There is no `sorry`, no `native_decide` and no code-changing attribute
  (`csimp`, `implemented_by`, `extern`): every fast twin is called directly, and is proved equal to its reference
  (`_eq`) or proved to imply the fact the reference gives (`_sound`, `grdB_of_grdBX`, `regsOkB_of_regsOkBH`).
- `V` is the Lean term `submission6.V` in `lean/`, compiled into the badge. The Rust prover is untrusted: a bug in it
  can only produce a rejected proof.
- **Data modules are untrusted.** `Lvm6DataPhi*` (the `Φ_Q` class table `P`), `Lvm6DataLay*` and `Lvm6LayP` (the
  layout of `Q`) and `Lvm6DataHint*` are decoded at start-up. The theorems quantify over the class table
  (`certified6_tiOf6`) and use no fact about the layout or hint data beyond what the guard checks, so wrong data either
  passes the checks, and the certificate covers it, or makes `guard6` false, after which every SNARK proof is
  rejected.
- **What the guard checks at start-up** (`staticOk6`, evaluated once as the global `guard6`; `staticOk6_ok` turns it
  into the named facts `StaticOk6`): the layout of `Q` is valid; the class table cancels against `Q`'s entries built
  from its rows, so `P` evaluates `Φ_Q` (`phiChkG`, `phiChk_ok`); the mini-bus tables are linear; the stream,
  signature and public regions are disjoint, placed and affine; the node's cells (PoW and bit auxiliary blocks,
  constants, public cells, commitment and Keccak register maps, Keccak aliases) are where the node theorem needs
  them; and the assembly facts hold (cell count, stream cells, per-row re-reads). That the guard is true on the
  shipped data is not proved; it is checked by running it (`NOTES.md`, "Result").
- **Not covered by the certificate**: that honest SNARK proofs are accepted (tested by the known-answer tests and the
  development verifier, not proved), and the time taken by `V`, by start-up and by the prover (the harness enforces
  those).
- The development verifiers in `prover/tools/` (`refv`, `r3v`) are test oracles; the certificate does not use them.

## Build and reproduce

**Lean.** The contract's toolchain (Lean v4.34.1, Mathlib v4.34.1 and the pinned libraries); no `lake update`. From a
core checkout at the pin (the submissions repository's `AGENTS.md` §5; `harness/smoke.toml` caps `build_s` at 600 s,
below #47's measured 1,016.6 s):

```sh
harness/org-setup.sh "$PWD"
set -a; eval "$(harness/ci/build-kernels.sh "$HOME/rf-kernels")"; set +a     # comparator + lean4export
python3 -I harness/local-season.py > /tmp/season-local.toml                  # the season's caps (build_s 1,200)
python3 -I harness/evaluate.py cert --entry ../submissions/half-leaf --org "$PWD" --work /tmp/rf-work-cert \
  --out /tmp/rf-cert.json --season /tmp/season-local.toml
```

It builds `lake build +Challenge +Solution`, replays the kernel, then builds and starts the badge.

**Prover.** `prover/` is a Cargo workspace (Rust 1.99.0, `rust-toolchain.toml`; fat LTO, one codegen unit,
`panic = "abort"`; offline, no crates.io dependency). leanVM's crates are vendored under `prover/crates/`, with
`src/` byte-identical to leanVM except the marked seams and the new files listed in `prover/PATCHES.md`
(`keccak_gkr/src/tree.rs`, `pcs/src/open6.rs`, `pcs/src/stack_open/basis/six.rs`); with the seams off they reproduce
leanVM's own proofs. The shape is a build feature: `build-asm.sh --shape p17` builds every tier with the feature
`p17`. `build-asm.sh` emits one `.s` per CPU tier (`prover-v2.s` x86-64-v2, `prover-v4p.s` AVX-512 with PCLMULQDQ,
`prover-v4.s` Zen 4 with GFNI and VPCLMULQDQ), plus the `cpuid` dispatcher `dispatch.s` and `qblob.s`.

`prover/qblob.s` is the circuit `Q` in compact form, embedded so that the binary reads no blob file. To reproduce it,
run `lvm6-prover qpack q6-p17.blob q6-p17.qbin` on the text blob (sha256
`857d6adcda829635a472de94218575e14a8cc776d9b913724fa46fce169f3eee`, Keccak-256
`fe3b8c272a45024925ebae6d6df90bc3d8b0b49ad784636023cf0958359774ad`), with a `p17` build of the prover. The qbin's
sha256 is `a24e97854017901d024c02da5ad9462ad3cc2a036df6c9efaab14163d3bc1c0a`; its header carries the shape tag 17,
and `build-asm.sh` refuses a qbin whose tag does not match `--shape`. Then run:

```sh
tools/gcc2404-setup.sh DEBDIR TC                    # the 28 noble .debs named in tools/debs.sha256
GCC=TC/gcc2404.sh prover/build-asm.sh --variants "v2 v4p v4" --shape p17 --q q6-p17.qbin OUT
```

This writes the five `.s` files to `OUT/build/`. `GCC` names the wrapper `tools/gcc2404.sh`, which runs Ubuntu
24.04's `x86_64-linux-gnu-gcc-13` (13.3.0-6ubuntu2~24.04.1) with binutils 2.42 and libc6-dev 2.39 (the evaluation
machine's) with `--sysroot` and `-B` pointing at a user-level sysroot. `tools/gcc2404-setup.sh` builds that sysroot:
it checks the 28 `.deb`s (fetched with `apt-get download` from noble) against `tools/debs.sha256` and unpacks them
with `dpkg -x`; its header gives the fetch and link commands. The `.s` sha256s:

| file | sha256 |
|---|---|
| `dispatch.s` | `a562a40a2e5017597d210f2c77cd511d5bceb7dc86cd5284f731a69bb41d4bd8` |
| `prover-v2.s` | `0bfb1d5ec15e8d34132e3a5a8b27722765f1bb2e4821c3941b52c821c06575fd` |
| `prover-v4.s` | `418e0369db5c0dc4631f095754b87a47bc7f496cc377ba7644d18bc8ecef0d32` |
| `prover-v4p.s` | `dbb0261742c74b8092f9fe2db53cb4d5aec24172532cae5a89c9a417bef98db3` |
| `qblob.s` | `1031deb9757b62e24a6e2072975260141aaf86d7d4d933b02379cb41ab49a327` |

The runner's link, `gcc -static -O2 -pthread *.s -o prover -lm`, with gcc 13.3 gives the binary
`8da0821d0c62d488b064e9548dd6ce5b9b3943058c70fe36099d3d01f722c1a2`. `prover kat` runs the known-answer tests (its
schedule line names `FORMAT6 v2.6 (P17)`), and `prover info` prints the tier and `embedded Q fe3b8c27…74ad`.

**Data.** The text blob, the class table and the layout come from one export of the Lean circuit at `P17`
(`q6-p17`; class table `c19b3498…0ce4`), written by a development exporter (a compiled Lean executable over the
definitions of `Q` and its layout). The exporter is a development tool and is not in this root. The encoder of the
`Lvm6DataPhi*` modules is `tools/phb.py` (`python3 tools/phb.py q6-p17.cls OUTDIR`); on the class table
`c19b3498…0ce4` it reproduces all 19 shipped `Lvm6DataPhi*` modules byte for byte. None of these files is trusted
(see above).

**Run.** `prover setup DIR` runs each tier's self-test and writes `DIR/lvm6-q.bin`, the raw form of `Q`. Each request
loads it and precomputes the witness plan before `ready`. Proofs are deterministic: development builds give
byte-identical proofs at 1, 4 and 8 threads, and the shipped binary gives the development builds' leaf and node proofs
on its v4p tier, and the same node proof on its v2 tier, at 8 threads. The v4 tier was checked under Intel SDE with a
development build and the GKR layers skipped (a full v4 proof under SDE does not fit its time limit on the
development host); the shipped binary's v4 tier passes `kat` under SDE.

## Numbers

All numbers here are measured on the development host, a shared VM; "load" is its 1-minute load average, mostly other
projects' jobs. Local season-shape run: not measured locally (host contention); CI measures it. The certificate rows
are from `evaluate.py cert` at core `39d3216` (run `c1`) and from its kernel and gate commands run on their own: `c1`
used a local season file in which `kernel_s` (600 → 1,200 s) and `gate_s` (120 → 240 s) are scaled by the measured
host/eval single-thread ratio (about 2×), every other cap being the season's, and it was stopped by the host's memory
guard during its kernel stage, after its build had completed. Figures marked [estimate] are not measured at
evaluation: `V` is scaled by #47's evaluation/host ratio at `P18` (41.7 ms in CI against 73 ms on this host, ×0.57),
the kernel and the gate by the host/eval ratio 2.0–2.6.

| | value | cap |
|---|---|---|
| verdict | not measured locally (host contention); CI measures it | |
| `P_total` (median of 3 passes) | not measured locally (host contention); CI measures it | |
| `S` (`final`) = `P_total · |π_16|` | not measured locally (host contention); CI measures it | |
| `S_every` = `P_total · max |π_i|` | not measured locally (host contention); CI measures it | |
| step, median | not measured locally (host contention); CI measures it (one node step alone: 5.49 s wall, 8 CPUs, R2; ≈ 2.6 s at evaluation [estimate]) | `step_s` 20 s |
| `V` per check, median / max | 85.6 / 207.8 ms on the host: the first check after the warm-up in 24 fresh badge `verify --serve` processes (12 node, 12 leaf, paired in random order; node 82.8, leaf 90.6 ms; load 15–17); ≈ 49 ms at evaluation [estimate]. In the season run: not measured locally (host contention); CI measures it | `v_cap_ms` 64 |
| badge start-up | not measured locally (host contention); CI measures it (the start-up guard alone: 6.08 s CPU median, 11 processes) | `badge_start_s` 16 s |
| prover peak RSS | not measured locally (host contention); CI measures it (one node step alone: 2.15 GiB, R2) | 8 GiB |
| `|π|`, every step | 230,424 B | `pi_cap` 1 MiB, `final_pi_cap` 512 KiB |
| certificate `build_s` | ≈ 1,090 s (run `c1`'s fresh build, from its log mtimes; not the harness's `build_s`; load 17–24) | 1,200 s |
| certificate `kernel_s` | 675.9 s (the comparator run on its own, accepted, load 7.8 → 8.9); ≈ 260–340 s at evaluation [estimate] | 600 s (1,200 s in the local run) |
| certificate `gate_s` | 150.0–163.9 s (the sandboxed gate on its own on `c1`'s built tree, 2 runs, PASS, load 15.9–16.6); ≈ 58–82 s at evaluation [estimate] | 120 s (240 s in the local run) |
| `badge_s` | not measured locally (host contention); CI measures it | 180 s |

The development host is a VM without GFNI and VPCLMULQDQ, whose cpuid also hides PCLMULQDQ (which it does execute:
the setup's self-test enables the v4p tier), so its timings are indicative only; the evaluation's numbers are the
ones that count.

## Layout

| Path | What |
|---|---|
| `claim.json` | the declared numbers |
| `lean/` | `Solution`'s import closure: #47's tree (season 1's certified leanVM port, #11 through #35; the 16-pack Keccak modules from #34, the `KS` reduction at `E` from #26; the v6 modules `Lvm6*`), ported to `P17`, with the data modules `Lvm6Data*` of the `P17` export |
| `prover/*.s` | `dispatch.s`, the three tiers and `qblob.s` (the embedded `Q`), built with `--shape p17` |
| `prover/` (other files) | the Rust workspace the `.s` files come from: leanVM's crates (`PATCHES.md` lists every edit), the v6 crates (`fs6`, `r3core`, `r3sponge`, `r3typed`, `r3mb`), the binary, `build-asm.sh` and its tools |
| `tools/` | development scripts, ignored by the evaluation: `phb.py` (the `Lvm6DataPhi*` encoder) and the Ubuntu 24.04 toolchain recipe (`gcc2404-setup.sh`, `gcc2404.sh`, `debs.sha256`) |
| `LICENSE-*` | leanVM (MIT / Apache-2.0); ArkLib and CompPoly (Apache-2.0; the affine MCA port); longfellow-zk (Apache-2.0; `LvmJB*`) |
