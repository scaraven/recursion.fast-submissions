# Vendored leanVM code (leanVM fdb317982, MIT OR Apache-2.0; LICENSE-MIT, LICENSE-APACHE copied from its root)

| crate here | leanVM path | `src/` |
|---|---|---|
| `crates/parallel` (`experimental_parallel`) | `crates/experimental_prover/parallel` | byte-identical |
| `crates/primitives` (`experimental_primitives`) | `crates/experimental_prover/primitives` | byte-identical |
| `crates/pcs` (`experimental_pcs`) | `crates/experimental_prover/pcs` | byte-identical |
| `crates/keccak_gkr` (`experimental_keccak_gkr`) | `crates/experimental_prover/keccak_gkr` | byte-identical |
| `crates/verifier` | `crates/verifier` | byte-identical |
| `crates/keccak256` | `crates/keccak256` | byte-identical |
| `crates/fiat_shamir_prover` | `crates/fiat_shamir_prover` | byte-identical |

Check: `diff -r ~/leanEthereum/leanVM/crates/experimental_prover/pcs/src crates/pcs/src` (and so on) prints nothing.
File headers (the flock-core / Hashcaster credits and copyright lines) are kept as written.

Edits outside `src/` only:

| file | edit | why |
|---|---|---|
| `crates/*/Cargo.toml` | `[dev-dependencies]`, `[[bench]]` dropped; `license` added; features `test-util` (primitives) and `bench` (keccak_gkr) kept as empty names, never enabled; the macOS-only `libc` of `parallel` dropped | offline, std-only: no crates.io dependency (rand, sha3, bench_harness, isa, allocator/jemalloc, tracing-subscriber stay out) |
| `crates/tracing` (new) | a no-op `info_span!` with `.in_scope`/`.entered`/`.enter`, fields evaluated by reference | leanVM's only `tracing` use (35 sites); the real crate would pull `tracing-core` and its global dispatcher into the `.s` |
| workspace `Cargo.toml` | `[profile.release]` fat LTO, one codegen unit, `panic = "abort"` | one LLVM module per tier for `--emit asm` |

Not vendored: `lean_vm_core` (Route B has no VM) and `stable_prover/*`.

## Edits to vendored `src/` (from R0, 2026-11-22)

The table above held until R0; these crates' `src/` now differ from leanVM by the edits below only, each marked
`lvm6` in a comment at the site. Every edit is a seam: with `fs6::v6()` off (the default) leanVM's flows are
byte-identical to leanVM's (checked: `smoke 14` gives P1's proof hash `20706a33…e5c7` and verifies natively).
`diff -r` against leanVM shows exactly these hunks.

| file | edit | why |
|---|---|---|
| `fiat_shamir_prover/src/transcript.rs` | `ProverState` holds `Backend::{Sponge, Chain}`; new `ProverState::v6(fs6::Transcript)` (sets `fs6::set_v6(true)`), `into_v6`, `chain`, `add_commitment`; every method dispatches: chain mode absorbs scalars/caps into `BODY`, `grind(g)` = `G(g)` (least nonce; `g = 0` nothing), `sample` = the pending ground draw, else `G(1)` if anything is pending or no group is open, else `D(1)`; `grind_sample` = least nonce that passes and is usable; `hint_merkle` writes leaf ‖ siblings to `BODY` and records V's leaf/node queries; `add_root` panics in chain mode | FORMAT6 §3–§5 (M1 D1/D2) behind leanVM's API, so pcs/keccak_gkr call sites are unchanged |
| `fiat_shamir_prover/src/lib.rs` | `grinding_bits` is a fn: v6 mode → `fs6::params::grind_for` (least `g ≥ 1` with `8c ≤ 7·2^g`, PARAM's rule), else `verifier::grinding_bits` (leanVM's `⌈log₂c⌉−3`); no longer `const` | FORMAT6 §6 grinds (`s` G(6), rounds G(2), `β` G(2), `r_seg/r_lane` G(3)) from the same call sites (R2's request) |
| `fiat_shamir_prover/Cargo.toml`, `pcs/Cargo.toml` | `fs6` path dependency | the seams |
| `pcs/src/merkle.rs` | `MerkleBuilder::new_committed`; v6 mode (`o6`): no cut, leaves = the trailing committed words of a row (no zero image) hashed through the oracle on the absorbing worker's connection, `finish` builds whole levels up to `fs6::log_cap_for_height` (P18: caps 2^7,6,5,5,5); `CutTree::commitment()` (root or cap), `open` returns committed-word leaves and siblings below the cap; `root()` panics in v6 mode | FORMAT6 §5 (368 B / 256 B leaves, caps, no root), oracle Merkle batched by levels |
| `pcs/src/whir.rs` | `config_for_rate`: v6 mode → `fs6::params::frozen_whir` (params6.json) or an error, never the f64 search; `Commitment.cap`; `commit` passes `n_lanes` as the committed words; the level commitment is sent with `add_commitment(tree.commitment())`; `LigeroWitness::root` `allow(dead_code)` | D1 frozen parameters (P1 §5); caps |
| `pcs/src/whir_config.rs` | `TAIL_GRINDING_BITS` uses `verifier::grinding_bits` | `fiat_shamir::grinding_bits` is no longer `const` |
| `keccak_gkr/src/batch_bench.rs` | `add_commitment(&commitment.cap)` | caps |
| `keccak_gkr/src/lib.rs` | one line: `pub mod tree;` (R2) | the tree batch |
| `keccak_gkr/src/tree.rs` (new, R2) | FORMAT6 §6.2: heap witness (`Tree`: rows, raw slots 0–7, middle at 8–32), the start (`δ`, `ρ`, `D^b`, `u`, `o₄…o₂₄`, then `Witness::prove`'s first claim with the middle at slot `8+l`), the middle opening on slots `8+l`, the input opening (constants off with the post-layer `r'_seg`, 4 low + top + 6 slot rounds, `pw^P/pw^L/pw^M`, 64 slices); calls leanVM's `prover::prove_layer` and `crate::first` unchanged; `open.rs`'s private round helpers copied verbatim; dev `Tamper`, `Tree::forge` | BLUEPRINT §2.3 v3; `prover.rs`, `open.rs`, `witness.rs`, `protocol.rs` untouched |

New crate `crates/fs6` (lvm6's own, not leanVM's): FORMAT6's codec, oracle (moved from the binary), transcript,
Merkle, frozen params, schedule and KATs. Binary: `oracle.rs` re-exports `fs6::oracle`; `stream.rs` is R4's driver;
`smoke6` mode; `kat` runs FORMAT6 KATs.

## Changelog

- 2026-11-22 (P1): vendored, src byte-identical; scaffold.
- 2026-11-22 (R0/R4): `crates/fs6`; the seams above; frozen WHIR table; driver with the two `SIGN`s (FORMAT6 §8),
  `W` default/fallback, `skel` mode; `grinding_bits` v6 rule (R2's request). Notes: `docs/lvm6/stages/RT-transcript.md`.
- 2026-11-22 (RT, FORMAT6 v2.2): `fs6` follows v2.2 (bind `B`, `vk` in `HDR`, seed `a₀ ‖ c ‖ HDR`, high part before
  cap, OOD grind index `i+1`, generic level count); driver and KATs updated; no change to vendored leanVM files.
- 2026-11-22 (R2): `keccak_gkr/src/tree.rs` (FORMAT6 §6.2 prover, the two ends around the unchanged layers); binary mode
  `tree6` (`prover/src/tree6.rs`); `refv` §6.2 check (`tools/refv/src/tree.rs`, bin `refv-tree`). Notes:
  `docs/lvm6/stages/R2-tree.md`.
- 2026-11-22 (R3): new crates, lvm6's own (no vendored `src/` edited): `crates/r3core` (stack layout, prover-side
  stack claims, FORMAT6 §6.1/§6.5/§6.6 prover, the WHIR part transcribed from R1's KAT generator), `crates/r3sponge`
  (§6.3), `crates/r3typed` (§6.4a), `crates/r3mb` (§6.4b; vendors leanVM's `lean_vm_core/src/{gkr.rs, leaf.rs}`
  with the patches listed in its own section when they land), `tools/r3v` (bin `refv-full`, dev). Workspace members
  added; binary mode `full6` (`prover/src/full6.rs`, `r3core` dependency). Notes: `docs/lvm6/stages/R3-node.md`.
- 2026-11-23 (R5, `docs/lvm6/stages/R5-perf.md`): proofs byte-identical (leaf `6b3fd130…` = R1's `kat-full`, node
  `4b61596d…`; 1/4/8 threads; tiers v2/v4p/v4). Vendored `src/` hunks, each marked `lvm6 (R5…)`, additive only:
  `pcs/src/lib.rs` `pub mod open6;`, `pcs/src/stack_open.rs` `pub(crate) use basis::six;`,
  `pcs/src/stack_open/basis.rs` `pub(crate) mod six;`. New lvm6 files inside `pcs`: `src/open6.rs` (public wrappers of
  leanVM's `whir_lanes::LaneRounds`, `whir::Dense`, `whir_induce::induce_basis_auto`, unchanged) and
  `src/stack_open/basis/six.rs` (`initial_basis6`: leanVM's `initial_basis` for FORMAT6 §6.5's list: point terms as
  leanVM's, ring terms at their own offsets with their own map's coordinate weights, "lane terms" `low ⊗ gamma` on one
  lane for the dense weights; `Low::from_table`). lvm6 crates: `r3core/src/open6.rs` (`open` drives those pieces through
  the v6 transcript; R3/R1's naive dense opening kept as `open_naive`, `LVM6_OPEN=naive`; `LVM6_OPEN=cmp` dev check of
  level 0's first table, naive vs terms, per claim kind), `fs6/src/oracle.rs` (`Local` batches through
  `keccak256::hash_many_from_state`, 8-way on AVX-512; scalar fallback `LVM6_KECCAK=scalar` or `LANES = 1`; test
  `r5_tests`), `r3typed/src/circuit.rs` (`phi_q_many`: `Φ_Q` at the 44 line points in one pass, eight points per `F128x8`; test
  `tests/r5_phi.rs`) and `prove.rs` (§6.4a calls it; dev `LVM6_R5_LAPS`), and, dev only and NOT applied here (the driver is R3's):
  `LVM6_STOP_AFTER=node.<phase>` in R5's copy of `prover/src/prove6.rs` (`/home/devops/scratch-lvm6/R5/src`, branch `r5`).
- 2026-11-23 (R6, `docs/lvm6/stages/R6-perf.md`): proofs byte-identical (leaf `6b3fd130…`, node `4b61596d…`; 1/4/8
  threads; tiers v2/v4p/v4). No vendored leanVM `src/` file changed (`diff -r` against leanVM shows only the R0–R5
  hunks above). lvm6 files: `keccak_gkr/src/tree.rs` (§6.2): `Tree::new` permutes each level eight states at a time
  with leanVM's `keccak_f_many` (`keccak256` lanes) and keeps every row's whole output state (`Tree::outputs`);
  `Tree::output_claim` replaces `OutputClaim::of_inputs` in `prove_tree` (no second pass of 2^19 permutations; each
  lane's words through leanVM's MLE kernel, `packed_eq` of the low 10 variables and `dot_base`, scaled by `eq` of the
  high ones: the same field elements); `Tree::witness` writes the raw slots a column at a time (no forgery lookup when
  there is none); `instance_slices` tests a chunk for zero 64 words at a time. New test `keccak_gkr/tests/r6_tree.rs`
  (outputs, digests, raw slots and `output_claim` = `of_inputs` at 2^12 blocks). `r3typed/src/prove.rs` (§6.4a): the
  folds and the zerocheck / product-sumcheck round sums eight pairs at a time in leanVM's `F128x8` (`even_odd`,
  `mul_unreduced`, one reduction per sum) on the AVX-512 + VPCLMULQDQ tier (`PACKED`), the scalar loops elsewhere.
  Dev knobs (`LVM6_R6_LAPS`, `LVM6_STOP_AFTER=tree.<sub>`/`sponge`/`typed`, `LVM6_R6_SKIP_TREE`,
  `LVM6_R6_SKIP_LAYERS`) are in R6's copy only (`/home/devops/scratch-lvm6/R6/src`, branch `r6`), NOT applied here.
- 2026-11-23 (R7, `docs/lvm6/stages/R7-int.md`): the deployed circuit `Q` (NODE3's exporter blob). No vendored leanVM
  `src/` file changed. Stub-`Q` proofs byte-identical (leaf `6b3fd130…`, node `4b61596d…`; `refv kat-full` on the stub
  leaf reproduces R1's `kat-full` byte for byte). lvm6 files: `r3typed/src/circuit.rs` (blob sections in any order:
  `MINIBUS`, `POWBITS`, new `BITS` (`y nb d_0 … d_{nb−1}`: word `d_i` = bit `i` of word `y`) and `BOUT` (`y k a d`:
  `LvmBits.BOut.word` shl/shr/bit/fld), checked: every derived word a `com` word defined once; the blob's `MINIBUS`
  kept for r3mb, `minibus()`), `r3typed/src/witness.rs` (`solve_plan`: `OUT` rows, BITS rows and BOUT lines in one
  Kahn order, ties rows-then-BITS-then-BOUT; BITS filled at `b = 0` too; dev `diagnose`: every violated slot, the
  accumulator tie rows), new `r3mb/src/export.rs` (the blob's `MINIBUS` tables: seed arrays over `STREAM` cells,
  read tables over `T` words, `fin`/`cnt` at the export's stack words; `tables_in_use`/`witness_in_use`, stub
  otherwise), `r3mb/src/{tables.rs,prove.rs,typed_mb.rs}` (committed columns anywhere on the stack; r3mb writes only
  `MB_LO..MB_HI` and checks the others are already on the stack; claims 50–52 dense on the aligned block holding every
  column, `claim_block`, the same polynomial as Lean's `mbClaimsG` parts; `tables_unchecked` for the verifier),
  `prover/src/prove6.rs` (`r3mb::export::witness_in_use`; dev `LVM6_TY_DIAG`), `prover/src/full6.rs` (dev
  `LVM6_LEAF_FROM=DIR`: step 1 from a saved leaf), `tools/refv/src/{full.rs,main.rs}` (`tables_in_use`; `kat-full`
  records the mode from `HDR.b` and the blob's Keccak). Tests: `r3typed/tests/r7_bits.rs`, refv `tests/mb.rs`
  `export_round_trip` (columns in slots 33/36/38, block `2^22`).
- 2026-11-23 (R7, second merge, `docs/lvm6/stages/R7-int.md` §2b): node proofs on q6-node4. `r3typed/src/witness.rs`:
  the sponge link (`SpongeLink`, `sponge_link`, `witness_linked`; `Q` reads `X`/`Y` of the rows from `split` through
  `ks`: `X` from `XSRC` or the copy rows, the rows run as Kahn steps, the caller writes `X` and regenerates the sponge
  rows, every `ks` word asserted), `CSUM` steps (Q_sig's WOTS checksum bits), `Readd` steps (every mini-bus read value
  word = its seeded cell's value at the solved address, MBT's/season 1's semantics; the `OUT` entry moves to the row's
  W word), every derived word defined once (asserted); `r3typed/src/circuit.rs`: `CSUM`, `XSRC` sections;
  `prover/src/prove6.rs`: `witness_linked`, `X` write and sponge regeneration, dev `LVM6_X_CHECK`;
  `r3mb/src/export.rs`: dev `LVM6_MB_DIAG`. Stub proofs byte-identical (`6b3fd130…`, `4b61596d…`); q6-node4 leaf
  `cfc24373…`, node `d14a552f…`, 1/4/8 threads, `refv-full` ACCEPT.
- 2026-11-23 (R8, `docs/lvm6/stages/R8-rel.md`): the circuit `Q` is embedded; no vendored leanVM `src/` file changed.
  New `r3typed/src/qbin.rs`: `Loaded` (the normalized, checked circuit with its POWBITS/BITS/BOUT/CSUM/XSRC/MINIBUS
  sections) in one layout, two encodings: compact (`LVM6QC2`, LEB128 varints, entries as `Δx·4+o`, zigzag `Δy`, a
  coefficient-table index) and raw (`LVM6QR2`, fixed 8-byte words); header = magic, the text blob's Keccak-256, `src`
  (raw: the Keccak-256 of the compact file), a 64-bit payload checksum, the length; `decode` bounds every count.
  Feature `embedded-q` (r3typed, forwarded by the prover): `extern` symbols `lvm6_qblob`/`lvm6_qblob_len`, defined
  by `qblob.s` (`tools/qblob-asm.py`: `.rodata` `.quad` lines; no `.incbin`), one file linked beside the tiers.
  `r3typed/src/circuit.rs`: `load()` = embedded (the setup's raw `$RF_SETUP/lvm6-q.bin` if its `src` and checksum
  match, else the embedded compact form decoded and checked; `$LVM6_Q_BLOB` ignored) → `$LVM6_Q_BLOB` text (dev,
  `load_text`) → the stub. `r3typed/src/witness.rs`: `prewarm` computes the witness plan of the circuit in use once
  (`solve_plan_aux` with its aux rows, its sponge link, the static mini-bus read pairs `readd_pairs`); `solve_z` uses
  it only when `cached_plan` finds the same inputs, else computes as before. `prover`: `qpack BLOB OUT` (dev: the
  compact form, round-trips both forms), `setup` writes `lvm6-q.bin` after the tier self-test (a write failure is
  logged, not fatal), `stream` calls `prove6::preload` (load `Q` + plan) before `ready`, `full6` before step 1
  (`LVM6_NO_PRELOAD=1` dev skip), `info` prints the embedded `Q`'s identity. `build-asm.sh --q QBIN` (feature
  `embedded-q`, `qblob.s` into `build/`, cargo's discarded link gets `qblob.o`) and `GCC=` (the link's driver). Test
  `r3typed/tests/r8_qbin.rs`. Proofs byte-identical: q6-node4 leaf `cfc24373…`, node `d14a552f…`.
- 2026-11-24 (R9 = PORT17 package R1, `docs/lvm6/stages/R1.md`): the shape is a build choice; no vendored leanVM
  `src/` file changed except `pcs/src/merkle.rs` (one call: `log_cap_for_height` takes the shape). `fs6`: feature
  `p17` (forwarded by `lvm6-prover/p17`, `refv/p17`, `r3v/p17`), `params::P17` (FORMAT6 v2.6, P17-freeze §1.1) and
  `params::SHAPE` (`P18` by default); `Shape` gains `relayout`, `trace_rows`, `qs`, `pi_len`; `typed_phases` reads
  `sh.relayout`; `frozen_whir` and `log_cap_for_height` take the build's/the given shape. `r3core::layout`: one
  `Place` slot map per shape (`P17`: STREAM 33 with `sB = 2^17`, SP 34–35 at block offset 17, com 36–39, Y 40,
  mini-bus 41, X 42) and `const` asserts tying every block to its slot; `SP_MU` is 19 at both shapes, `y_off` uses
  `2^(κ−13)` lane blocks a slot. `r3sponge::TRACE_ROWS` = the shape's `B`, checked against the child's trace stream
  in `prove6` (node mode with the sponge part). `r3typed`: the stub's σ/S_flat/com from the layout, `TY_SENT`/
  `TY_DRAWS` (176/84, 174/83), `Circuit::check` requires the σ region at `sB`, the qbin magics' last byte is a shape
  tag (0 = `P18`, unchanged; 17 = `P17`). `prover`: `kat` checks the shape's tally (v2.6: 205,912 B / 3,806 / 561)
  and the v2.6 positions examples; `selftest` exits 3 on a KAT failure and `setup` then fails instead of capping
  every tier at v2. refv: `shape::p17`, `shape::active`, `FULL_QS` = the shape's `qS`, the typed tamper item
  `106 + 2·relayout`. `P18` proofs byte-identical: q6-node4 leaf `cfc24373…`, node `d14a552f…`.
- 2026-11-24 (R9 = PORT17 package R2, `docs/lvm6/stages/R2.md`): the release build at `P17` on the real `Q`; no
  vendored leanVM `src/` file changed. `build-asm.sh --shape p18|p17` (default `p18`, whose cargo line is
  unchanged): `p17` builds every tier with the feature `p17` (`embedded-q,p17` under `--q`), and the qbin's shape tag
  (its magic's last byte, 0 or 17) must match the shape. refv `tests/mb.rs` reads the build's `SHAPE` (no `P18`
  alias); `export_round_trip`'s claim block is (4, 22) at `P18` and (2, 22) at `P17`; 9 pass and 1 is ignored at both shapes.
  `P17` proofs on q6-p17 (blob sha256 `857d6adc…3eee`, Keccak `fe3b8c27…74ad`): leaf `ce5ad442…d8dd`, node
  `44b51fd6…3f08` (Keccak-256 of `full6.signed`), 1/4/8 threads and the shipped binary at v4p and v2 identical,
  `refv-full` ACCEPT, 65 tampers each rejected.
