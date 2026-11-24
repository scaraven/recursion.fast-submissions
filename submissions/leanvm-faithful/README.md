# leanvm-faithful

The SNARK of current leanVM (`leanEthereum/leanVM` at `fdb317982`, its experimental prover), ported to the v6 rules as
faithfully as the contract allows, with a Lean certificate at `ε = 2^-128`. Each of the 16 steps is one proof. The
proof commits to the step's 2^18 blocks and proves their Keccak-256 Merkle root; from step 2 on, it also verifies the
previous signed proof inside a fixed circuit `Q`. There is no VM (Route B). `NOTES.md` has the design history, the
numbers and the dead ends.

This is a baseline, not a speed entry. Every leanVM phase that the contract leaves room for runs in its current
leanVM form, with leanVM's Rust code vendored. Where the contract forces a change, or certifiability called for one,
the change and its reason are listed in `NOTES.md`.

## What is proved

- **Relation.** Leaf mode (step 1): `c = leafStmt h 2^18`. Node mode (steps 2–16): `c = nodeStmt c' (leafStmt h 2^18)`.
  The SNARK proves knowledge of `xs` with `|xs| = 2^18` and `dataRoot xs = h`. In node mode it also proves
  `acc vk c' (π', tr', σ')` for the child, and `SigOk vk (traceDigest []) σ_leaf` for the witness-sending right leaf
  that the contract's `Rel` asks for.
- **One shape.** `V` accepts SNARK proofs only for `n = 2^18`. For every other `n ≤ leafCap` (0 and odd sizes
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
3. **Commitment**: one stacked multilinear `q : {0,1}^25 → K` at rate ¼, with leanVM's largest-first stacking and
   46 occupied lanes per level-0 leaf. The Merkle trees are hashed through the oracle and opened against caps
   (`2^7, 2^6, 2^5, 2^5, 2^5`); leanVM's pruned paths are dropped.
4. **Tree batch**: leanVM's Keccak-f GKR layers, unchanged (12 + 12 layers, RMFE 16-packs, normalized pack rounds),
   over the `2^19` rows of the data Merkle tree (`κ = 19`). Its start and input end are new: a tree-wiring
   sub-protocol connects the rows, a parent row commits its children's raw digests, and the one-byte domain tags
   (`0x48`, `0x44`) are handled in the input end only.
5. **Sponge batch**: a second leanVM Keccak GKR (`κ = 13`) for the hashes the node checks in-circuit: the child's
   trace digest, the WOTS chains of `σ'` and `σ_leaf`, and the statement hashes.
6. **Child verification (Route B)**: the fixed circuit `Q` (2.87 M entries) is the v6 verifier as a season-1 LoopIR
   program (`Q_link ++ Q_sig ++ Q_arith`), proved on season 1's typed backend over `E` (a zerocheck and a wiring
   sumcheck), with a mini-bus for data-addressed reads. `V` evaluates `Φ_Q`, the multilinear extension of `Q`, itself,
   behind season 1's self-fold accumulator: the header carries an evaluation claim `(pt, y)` of `Φ_Q`, and each step
   folds the child's claim with its own. This replaces leanVM's VM and its recursion guest.
7. **Ring switching**: leanVM's Frobenius-map switch. All 53 stacked claims are batched into one (`V` rejects more
   than `J₀ = 1024`; leanVM's bound is 512).
8. **Opening**: leanVM's stacked WHIR with the affine combiner, in the Johnson regime, with an out-of-domain sample per
   commitment. Queries per level are `[110, 45, 28, 21, 18]`. All parameters are frozen constants; the prover derives
   none of them from floating point at run time.
9. **Extractor**: season 1's agreement-set descent, with `FD1`, a new quasi-linear one-error Reed–Solomon decoder in
   the contract's machine. The descent costs about `2^44.6` steps; the total stays within the fuel `2^47 + 8192·t`.

**Sizes** [exact]: `|π|` = 238,152 B at every step, so the `final` and `every` tracks price the same proof. `V`'s
transcript has 4,349 oracle queries, with 868 nonces. `εFS ≤ 2^-128.09`.

## What is certified

`RecursionFast.Challenge.certified : CertificateR declared submission`, with `declared = Lvm6.declared6` by `rfl` and
`submission = Lvm6.Cert.submission6`. The proof is `Lvm6.Cert.certified6`. Its chain:

- **The shipped `V`.** `submission6` is `submissionOf VSc6 …` with `V := VwithT VSc6`, a byte-level fast parser proved
  equal to the reference one (`VwithT_eq`). `VSc6` reads the start-up constant `guard6 = staticOk6 base6`: if it is
  true, `V` runs the SNARK verifier `VS6` over the deployed circuit instance; otherwise it is `VSoff`, which rejects
  every SNARK proof and accepts only witness-sending ones. `VSc6_eq` (`rfl`) and `submission6_eq` (through
  `VwithT_eq`) identify the shipped term with the proved one.
- **Guard split** (`certified6_guard`). Off (`VSF6_off`): `certified_off`, the witness-sending certificate. On
  (`VSF6_on`): `V`'s SNARK branch equals `VSasm (Φ6 B h) P18`, the composed phase programs, and `certified_on`
  applies. Both cases
  give `CertificateR declared6`; the certificate does not depend on the guard's value. `certified6_tiOf6` holds for
  every class table `P`, and `certified6_base6` instantiates it at the shipped base.
- **Guard on** (`certified_on`, through `certified_ofD`): the six obligations of `Open6D`.
  - `queries`: at most `qS = 4,349 ≤ qV` queries (`queries_VSasm`, `queries18`).
  - `refines`: the executable `V` refines the compiled scheme `schemeOf (prog6 Φ6) P18` (`refines6_asm`), with fast
    twins of the hot loops proved equal.
  - `sound`: `KS` at `εFS ≤ 2^-128` (`open6X18D_Φ6`). It chains the phase specifications (`phaseSpecs6`: commit and OOD,
    the tree and sponge batches, the typed phases and mini-bus, `ringSpec6`, `openSpec6` on the affine MCA theorem
    `Lvm6Aff*`) through season 1's Fiat–Shamir compiler `KCert ⇒ KState ⇒ KS`. Its extractor obligation is `Xe6`:
    the per-group bad-event bounds (vacuous here: `BL := False`), and, on every accepting history
    with the good events, `ExtSpec6` returning a witness of `Rel`. This uses the node
    theorem `node6V_Φ6` (the deployed `Q` checks the child) and the reader equalities `child6_eq`, `sigLeaf6_eq`.
  - `wBranch`: the extractor decodes witness-sending proofs.
  - `computes`: the extractor program `extX6 D18` computes `EX6D` within `2^47 + 8192·t` (chain scan, `descend6`,
    `FD1`).
  - `size`: `extX6 D18` is within `progCap`.
- **The extractor's domain** (`EX6D`). The contract's `Computes` covers only logs with `|π| ≤ 8·outCap`, entries below
  `2^64` bytes and tapes of at most `2^64` words (`InDomW`). On that domain `EX6D` runs the descent above. Outside
  it, it falls back to season 1's `search`, where no cost is asked. Soundness asks, on every available log, for
  either a witness or the ideal extractor's answer (`ExtEqD`): on the domain `EX6D` equals the ideal extractor, and
  outside it `search` finds a witness.

`#print axioms RecursionFast.Challenge.certified`: `propext`, `Classical.choice`, `Quot.sound`.

## Trusted surface

- The contract at the pin (core `b7aa873`), the Lean kernel (replayed by the comparator), and the axioms `propext`,
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
  them; and the assembly facts hold (cell count, stream cells, per-row re-reads).
- The development verifiers in `prover/tools/` (`refv`, `r3v`) are test oracles; the certificate does not use them.

## Build and reproduce

**Lean.** The contract's toolchain (Lean v4.34.1, Mathlib v4.34.1 and the pinned libraries); no `lake update`. From a
core checkout at the pin (the submissions repository's `AGENTS.md` §5; `harness/smoke.toml` caps `build_s` at 600 s,
below this entry's build):

```sh
harness/org-setup.sh "$PWD"
set -a; eval "$(harness/ci/build-kernels.sh "$HOME/rf-kernels")"; set +a     # comparator + lean4export
python3 -I harness/local-season.py > /tmp/season-local.toml                  # the season's caps (build_s 1,200)
python3 -I harness/evaluate.py cert --entry ../submissions/leanvm-faithful --org "$PWD" --work /tmp/rf-work-cert \
  --out /tmp/rf-cert.json --season /tmp/season-local.toml
```

It builds `lake build +Challenge +Solution`, replays the kernel, then builds and starts the badge.

**Prover.** `prover/` is a Cargo workspace (Rust 1.99.0, `rust-toolchain.toml`; fat LTO, one codegen unit,
`panic = "abort"`; offline, no crates.io dependency). leanVM's crates are vendored under `prover/crates/`, with
`src/` byte-identical to leanVM except the marked seams and the new files listed in `prover/PATCHES.md`
(`keccak_gkr/src/tree.rs`, `pcs/src/open6.rs`, `pcs/src/stack_open/basis/six.rs`); with the seams off they reproduce
leanVM's own proofs. `build-asm.sh` emits one `.s` per CPU tier (`prover-v2.s` x86-64-v2,
`prover-v4p.s` AVX-512 with PCLMULQDQ, `prover-v4.s` Zen 4 with GFNI and VPCLMULQDQ), plus the `cpuid` dispatcher
`dispatch.s` and `qblob.s`.

`prover/qblob.s` is the circuit `Q` in compact form, embedded so that the binary reads no blob file. To reproduce it,
run `lvm6-prover qpack q6-node4.blob q6-node4.qbin` on the text blob (sha256
`0a32728fa09941acb7d9f96774578d429c42d36796e58d1ece4c4402ca24e097`, Keccak-256
`eba679c325133bbd713b1819f83ad9dd3270c2eb5db51b0fa949bc05028be580`). The qbin's sha256 is
`d29f2a20987ebcf9b0dbe0aeaa0ce24768665cdb87594f7fa1e67ef0b6b08a74`. Then run:

```sh
tools/gcc2404-setup.sh DEBDIR TC                    # the 28 noble .debs named in tools/debs.sha256
GCC=TC/gcc2404.sh prover/build-asm.sh --variants "v2 v4p v4" --q q6-node4.qbin OUT
```

This writes the five `.s` files to `OUT/build/`. `GCC` names the wrapper `tools/gcc2404.sh`, which runs Ubuntu
24.04's `x86_64-linux-gnu-gcc-13` (13.3.0-6ubuntu2~24.04.1) with binutils 2.42 and libc6-dev 2.39 (the evaluation
machine's) with `--sysroot` and `-B` pointing at a user-level sysroot. `tools/gcc2404-setup.sh` builds that sysroot:
it checks the 28 `.deb`s (fetched with `apt-get download` from noble) against `tools/debs.sha256` and unpacks them
with `dpkg -x`; its header gives the fetch and link commands. The `.s` sha256s:

| file | sha256 |
|---|---|
| `dispatch.s` | `a562a40a2e5017597d210f2c77cd511d5bceb7dc86cd5284f731a69bb41d4bd8` |
| `prover-v2.s` | `0fe131ad35c0643e326fbb517a116b56a1d4bf86a8eb45a66e28e5b08f7acf76` |
| `prover-v4.s` | `68a4617ac9a24114a3cb8fbb61b1602695cf72f7cccb9ec0653bc282b61716d9` |
| `prover-v4p.s` | `4c76fe3113b91c587b2da1c38757de4eafde15a5042fee915b0ee3d0ca4d35a5` |
| `qblob.s` | `195855bdb2822684141c670fcc11bf5eb7f56462f723dc3d00ed20bc86c61ece` |

The runner's link, `gcc -static -O2 -pthread *.s -o prover -lm`, with gcc 13.3 gives the binary
`1bbcafe1197e3f42ef37db5302e3c2bcbcb9f48b8ae57d76dd3f9a248d42933d`. `prover kat` runs the known-answer tests, and
`prover info` prints the tier and `embedded Q eba679c3…e580`.

**Data.** The text blob, the class table and the layout come from one export of the Lean circuit (`q6-node4`; class
table `9b198083…b124`), written by a development exporter (a compiled Lean executable over the definitions of `Q` and
its layout). The exporter is a development tool and is not in this root. The encoder of the `Lvm6DataPhi*` modules
is `tools/phb.py` (`python3 tools/phb.py q6-node4.cls OUTDIR`); on the class table `9b198083…b124` it reproduces all 19
shipped `Lvm6DataPhi*` modules byte for byte. None of these files is trusted (see above).

**Run.** `prover setup DIR` runs each tier's self-test and writes `DIR/lvm6-q.bin`, the raw form of `Q`. Each request
loads it and precomputes the witness plan before `ready`. Proofs are deterministic: development builds give
byte-identical proofs at 1, 4 and 8 threads, and the shipped binary gives the same proofs on its v4p and v2 tiers at
8 threads. The v4 tier was checked under Intel SDE with a development build and the GKR layers skipped (a full v4
proof under SDE does not fit its time limit on the development host); the shipped binary's v4 tier passes `kat`
under SDE.

## Numbers

All numbers here are measured on the development host, a shared VM; "load" is its 1-minute load average, mostly other
projects' jobs. Local season-shape run: not measured locally (host contention); CI measures it. The certificate rows
are `evaluate.py cert` at core `b7aa873`. The local certificate run used a local season file in which `kernel_s` (600
→ 1,200 s) and `gate_s` (120 → 240 s) are scaled by the measured host/eval single-thread ratio (about 2×), as approved
for the kernel; every other cap is the season's.

| | value | cap |
|---|---|---|
| verdict | not measured locally (host contention); CI measures it |  |
| `P_total` (median of 3 passes) | not measured locally (host contention); CI measures it |  |
| `S` (`final`) = `P_total · |π_16|` | not measured locally (host contention); CI measures it |  |
| `S_every` = `P_total · max |π_i|` | not measured locally (host contention); CI measures it |  |
| step, median | not measured locally (host contention); CI measures it | `step_s` 20 s |
| `V` per check, median / max | not measured locally (host contention); CI measures it | `v_cap_ms` 64 |
| badge start-up | not measured locally (host contention); CI measures it | `badge_start_s` 16 s |
| prover peak RSS | not measured locally (host contention); CI measures it | 8 GiB |
| `|π|`, every step | 238,152 B | `pi_cap` 1 MiB, `final_pi_cap` 512 KiB |
| certificate `build_s` | 1,016.6 s (fresh build, run c1, load 7–17) | 1,200 s |
| certificate `kernel_s` | 856.3 s (the comparator run on its own, accepted, load 7–14) | 600 s (1,200 s in the local run) |
| certificate `gate_s` | 101.5–106.3 s (the gate on its own, 2 runs, PASS, load 6–7) | 120 s (240 s in the local run) |
| `badge_s` | not measured locally (host contention); CI measures it | 180 s |

The development host is a VM without GFNI and VPCLMULQDQ, whose cpuid also hides PCLMULQDQ (which it does execute:
the setup's self-test enables the v4p tier), so its timings are indicative only; the evaluation's numbers are the
ones that count.

## Layout

| Path | What |
|---|---|
| `claim.json` | the declared numbers |
| `lean/` | `Solution`'s import closure: season 1's certified leanVM port (#11 through #35; the 16-pack Keccak modules from #34, the `KS` reduction at `E` from #26), restored to current leanVM form phase by phase, plus the v6 modules `Lvm6*` and the data modules `Lvm6Data*` |
| `prover/*.s` | `dispatch.s`, the three tiers and `qblob.s` (the embedded `Q`) |
| `prover/` (other files) | the Rust workspace the `.s` files come from: leanVM's crates (`PATCHES.md` lists every edit), the v6 crates (`fs6`, `r3core`, `r3sponge`, `r3typed`, `r3mb`), the binary, `build-asm.sh` and its tools |
| `tools/` | development scripts, ignored by the evaluation: `phb.py` (the `Lvm6DataPhi*` encoder) and the Ubuntu 24.04 toolchain recipe (`gcc2404-setup.sh`, `gcc2404.sh`, `debs.sha256`) |
| `LICENSE-*` | leanVM (MIT / Apache-2.0); ArkLib and CompPoly (Apache-2.0; the affine MCA port); longfellow-zk (Apache-2.0; `LvmJB*`) |
