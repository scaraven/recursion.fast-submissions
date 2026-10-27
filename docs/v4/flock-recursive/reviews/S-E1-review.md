# S-E1 (L-circ, first half): adversarial review

Reviewed: `docs/v4/flock-recursive/stages/S-E1-RESULT.md` and the ten modules
`submissions/flock-recursive/lean/{FRBlake2sCircuit, FRBlake2sWords, FRBlake2sCompress,
FRBlake2sGeneric, FRBlake2sWalk, FRBlake2sWitness, FRBlockLayout, FRBlockChain, FRBlockStream,
FRLeafCircuit}.lean` (uncommitted, on `84ca1d7`). Spec: BLUEPRINT revision 3.2 (frozen), §4, §4.1,
§4.2, §4.4, §2.3 steps 2–4, §5.4, A.6, A.7, and fix passes 3–4. Checklists: adversarial-review
(spec tightness, vacuity, trust, hygiene) and lean4:review.

The sources were hashed at the start of the review (`logs/S-E1-review/sources.sha256`) and
re-checked after the build: unchanged. A golf pass (`logs/S-E1-golf`) is under way in parallel,
and this review is pinned to those hashes.

## Evidence

| Check | Result | Log |
|---|---|---|
| Build of the ten modules in a fresh tree (`logs/S-E1-review/`, copy of `logs/fr-build/gen.sh`, `timeout 1500`) | green, no warnings, 1 min 44 s wall on the shared VM | `logs/S-E1-review/build.log` |
| Axioms of 13 main theorems and controls | `propext`, `Classical.choice`, `Quot.sound` at most | `logs/S-E1-review/axioms.log` (`Axioms.lean`) |
| Source rule (whole `lean/`) | 35 files, 0 findings | `logs/S-E1-review/source-rule.log` |
| Hygiene grep | no `sorry`, `native_decide`, `set_option`, `partial`, `unsafe`; one `decide +kernel` (the KAT); attributes `@[simp]`, `@[irreducible]`, `@[never_extract]` (allowed, gate rule 3) | — |
| KAT independence | `chainStep_zero_kat`'s value equals Python `hashlib.blake2s(b'\x43' + bytes(32))` = `954ac2a4…cd418d8d` (computed here) | — |
| Provenance | headers name spartan-srom at `783328c` and leanerVM `532ebb4`; `LICENSE-leanerVM` present. "No other change" holds for `Circuit` and `Words`: the diff is the namespace and the comments. `Compress`'s diff is exactly the six layout constants and the input set | `diff` in this review |
| Re-basing against A.6 | `constPos 1152`, `msgBase 512`, `counterLo 1024`, `counterHi 1056`, `finalFlag 1088`, `lastNodeFlag 1120`, inputs `0…255 ∪ 512…1151`, gates from `1280`, outputs `256…511`, zero rows `1153…1279`, `16000…` (`rowOf_zero`). Matches A.6, and the prover's `params.rs` | — |

The kernel cost is the RESULT's measurement: 28.3 s over the ten modules, the KAT 1.7 s
(`logs/S-E1/profile-*.log`). It is consistent with the build above and well inside FR-R4′.

## The statements, as written

**`holdsE_sound` / `holdsE_complete`: true, non-vacuous, sufficient.**
- `TargetOk` (`one ↦ true`, and otherwise only input positions) is the right side condition.
  Pinning a gate or an output would delete its constraint, and `TargetOk` excludes that.
- The claim that the target forces `one = 1` is `ht.1` plus the `(0,0)` row reading
  `z = E` in characteristic 2. It is kernel-checked.
- `zero_not_holdsE`, `Chain.zero_control`, `Stream.zero_control` and `Leaf.zero_table_control` show
  the target is load-bearing. Without it, `leaf_sound` is false for the all-zero table.

**`walkE_eq_sum`: true; sufficient for the lincheck.**
- The pinned rows of `blockR1CS tgt` are identically zero, so masking the row weights is exact.
  Columns are untouched, which is correct: gates still read `h_in`.
- Row weights are arbitrary, which covers the quirky `λ` coordinate.
- The verifier op must apply the kind's mask (m3).

**`leaf_sound`: true, non-vacuous (`leaf_complete` for every `s`, `n ≥ 1`), sufficient for `final`.**
- Its hypotheses are restricted to the used blocks. They are exactly what §5.4 step 3 delivers for
  a leaf, where `Sel` is all blocks:
  - `IsBool`, from `unpack`;
  - `HoldsE (blockR1CS chainTarget)`, the zerocheck with `E`;
  - `ChainLinks`, from P1-D5's shift with `s`, `h` in the target. Its links are
    `d(i+1) = out(i)` on `520…775` / `256…511`, plus the two endpoints.
- The bit order of `digestBit` (byte `j/8`, bit `j mod 8`, low first) agrees with A.7's pack map,
  so the shift's target encoding of `s` and `h` is the same object.
- The form `n ≥ 1`, used blocks only, deviates from §4.1's displayed statement (`∀ i`,
  `n = 2^(m−14)`). It is stronger and is documented (deviation 6).

**`blake2s_chain` / `traceDigest_chain` / `stream_sound` / `stream_traceDigest`: true for every byte string and every trace.**
- They are proved against the contract's `compressInput`, not assumed. There is no length bound:
  `nBlocks 0 = 1`, and the counter's high word is pinned from `t.toUInt64 >>> 32`. So they hold for
  every trace, within `queryCap` or not.
- `stream_complete` instantiates every hypothesis for every `B`.
- The node can discharge every hypothesis:
  - `hE` per block from the zerocheck (one stream layout, `L = 1,440,336`);
  - `hstart` from the shift's `h0` endpoint (§2.3 step 4);
  - `hl` from the shift's links;
  - `Padded` from the three padding cells per chain, point claims on `f`. The last block holds
    `1,440,336 − 64·22,505 = 16` bytes, so 48 padding bytes, i.e. exactly elements 5–7;
  - `htr` from the item asserts (L-cert).

**`block_sound_gen`: true for every `(t, fin)`.** It is the right lemma for a block whose `h_in` and
message are free inputs. It is **not sufficient for `hashStmt` as the blueprint specifies
`hashStmt`** (S-E1-M1).

## Majors

### S-E1-M1. `hashStmt` cannot be built on `block_sound_gen` as BLUEPRINT §4.2 specifies it, and the node's `A = I ⊗ A₀` cannot hold once it is fixed (owner: blueprint, S-E2)

The Lean of S-E1 is correct. The gap is in what the blueprint asks the next stage to do with it.
`hashStmt_sound` (§4.2: `out_A = leafStmt h n ∧ out_B2 = nodeStmt c₁ c₂`) needs, besides
`block_sound_gen`, the following:

- **(a) `h_in(A) = h_in(B1) = h0`.** `blockTarget` pins nothing below 1024
  (`blockTarget_low`). §2.3 step 4 puts `h0` in the shift's target only "at each chain's first
  block", meaning the two digest chains. Nothing in §4.2 or §4.3 pins the `h_in` of the
  `hashStmt` blocks. With `h_in` free, `out_A = compress(h_in, …)` says nothing about
  `leafStmt h n`, and the implication is unprovable.
- **(b) The constant message bytes**: the tag `0x4C`/`0x4E` at byte 0, the zeros `41…63` (A) and
  `1…63` (B2). `blockTarget` leaves the message free, and §4.2 states no constraint on these
  bytes.
- **(c) The wiring from item 1.**
  - §4.2 wires the messages "from item 1's payload … the same 64 bytes read two ways". But
    §1.1's `stmt` for leaf kinds is `enc64 n ‖ h ‖ zero(24)`, while `leafStmt`'s preimage is
    `tagLeaf ‖ h ‖ enc64 n`: a different field order and a one-byte tag offset.
  - The message's 16-byte elements are then byte-shifted windows of item 1's 16-aligned elements.
    Such a window is GF(2)-linear in two elements but not F-linear, so it cannot be an element
    equality. This is the BP-E-M1 problem again, inside `hashStmt`.
  - The node message `tagNode ‖ c₁ ‖ c₂` has the same one-byte offset.
- **(d) Consequence for the node's lincheck.**
  - Pinning (a) and (b) through the public target, the mechanism S-E1 built (`TargetOk` allows
    `h_in` and message bytes), gives the `hashStmt` blocks a `(0,0)`-row support different from
    the chain blocks', and the WOTS blocks a third. In the chain blocks `h_in` is the previous
    output and cannot be pinned.
  - So the node's matrix is `Σ_kind (Ind_kind ⊗ A₀^kind)`, not §2.3's "`A = I ⊗ A₀`, `B = I ⊗ B₀`".
  - Pinning (a) by point claims on `f` instead costs 2 claims per fresh-hash block. With WOTS that
    is about 418 blocks per slot, about 1,670 claims per node, and it breaks B′'s `(J−1)/2^128`
    batching row: about `2^-117.3`.
  - The RESULT's open question 1 ("WOTS blocks (S-E2) will need their own") is this problem.

**Fix** (blueprint revision, before S-E2):
- Give the node per-kind block matrices. Make the lincheck evaluate
  `Σ_kind Ĩnd_kind(r_blk) · walk_kind`, with one walk per kind and interval-indicator MLEs: a few
  walks, `O(log)` each for the indicators. Or extend the shift argument to pin `h_in = h0` at every
  fresh-hash block through a public indicator.
- Lay out `stmt` as the statement hash's padded message blocks
  (`tagLeaf ‖ h ‖ enc64 n ‖ 0^23` and `tagNode ‖ c₁ ‖ c₂ ‖ 0^63`, kind-selected), so that the
  `hashStmt` messages equal item 1's elements.
- State `hashStmt`'s target (`h_in = h0`, the tag, the zero bytes, `(t, fin)`) in §4.2/A.6.

### S-E1-M2. The leaf's `A₀` and `E` are not pinned in A.6, and the P2 prover uses a different convention from the Lean (owner: blueprint A.6, prover)

- **The Lean convention.** `chainTarget` makes every pinned position a `(0,0)` row with `E` its
  bit. That is the support `0…255`, `512…519`, `776…1023`, `1024…1152`; the circuit's own zero rows
  are `1153…1279` and `16000…`. This is what fix pass 3 adopted ("rows `(0,0)` with `E` = the
  constant").
- **The prover's convention.** The committed prover (`prover/circuit.rs`, `build`/`const_bit`,
  since P1 `081ae9b`) builds the leaf block with **`(one, one)` rows for the 1-bits** of `h0`, the
  tag, `t = 33` and `f0`. It uses `(0,0)` rows for the 0-bits and `E` = the indicator of position
  1152 only (`leaf.rs` `skip_eval`: "`e` = the one position in every block").
- **Why it matters.** Both encode the same Boolean constraints, but the matrices `A₀`, `B₀` and the
  target `E` differ:
  - the Lean `V`'s walk (`walkE_eq_sum` with `chainTarget`'s mask) gives one `Â₀`, and the
    prover's lincheck another;
  - the zerocheck's `Ê(λ, r′)` differs too.
  So honest P2 leaf proofs will fail the Lean verifier, or the reverse.
- **The node's support is unpinned too.** A.6 does not pin the stream/`hashStmt` support
  (`1024…1152` in the Lean), and A.8 does not say how `walkA`/`walkB` mask it (open question 2).
- **Fix.**
  - Add to A.6 a table: per block kind, the `(0,0)`-row positions with their `E` values, and the
    rows of the circuit's own zero positions.
  - Make the prover follow it, with `E` at every pinned position (the Lean's form, which the
    blueprint text already states). Alternatively re-target the Lean to `(one, one)` rows for
    constant 1-bits. Either is fine, but one must be normative.
  - Add a cross-check: the prover's `A₀`/`B₀` rows and its `E` vector for one leaf block, against
    a dump of `blockR1CS chainTarget` / `targetVal` (the dump tool of §8.1), as a KAT in P2.
  - Give A.8's walk ops the mask.

## Minors

- **S-E1-m1.** `item_aligned` is weaker than the RESULT says.
  - Its first conjunct `1 + 8 + 7 = 16` is a numeral fact. Nothing ties "7" to the seed's tag
    length: `h₀` only says `|q₀| ≡ 7 mod 16`.
  - The second conjunct gives item starts `≡ 0 mod 16`. The RESULT's "every payload" and the
    answers follow only with the A.2 tag lengths (payload at item start + 16) and
    `|q| ≡ 8 mod 16` (answer at item start + 8 + `|q|`), and neither is stated.
  - Fix: state the payload and answer offsets of item `k` as `≡ 0 mod 16` under "first tag 7
    bytes, other tags 8 bytes, payloads `≡ 0 mod 16`", or reword the RESULT. FRFormat/FRVIRSpec
    must discharge the size facts from A.4 in either case. The dummy queries (`0^64` Merkle nodes,
    zero absorbs) are `≡ 8 mod 16`, so they qualify.
- **S-E1-m2.** A.6 gives `one` (bit 1152) as slot 8. Bit 1152 is element `1152/128 = 9`, as
  `FRBlockLayout`'s docstring says. Correct A.6 (and A.7's element addressing of `one`, if any
  point claim or template uses it).
- **S-E1-m3.** The RESULT §4 says `stream_complete` "covers `hashStmt`'s `(41, final)`,
  `(64, ¬final)`, `(65, final)` targets". That is true of the targets: `|B| = 41` and `|B| = 65`
  produce them. It does not cover `hashStmt`, which also needs `h_in = h0` and the constant
  message bytes (S-E1-M1). Reword.
- **S-E1-m4.** BLUEPRINT §4.1 still displays
  `leaf_sound : ∀ z s h, Boolean z → (∀ i, …) → ChainLinks z s h → chainEnd s (2^(m−14)) = h`.
  The proved form (`1 ≤ n`, hypotheses on used blocks, `[DecidableEq R]`) is the one L-cert will
  call. Update the blueprint text when it next revises, so `final`'s author does not code against
  the displayed shape.
- **S-E1-m5.** There is one value-level KAT, single-block; I verified it independently against
  `hashlib`. Multi-block behaviour (counters, final flag, padding) rests on `blake2s_chain`'s proof
  against the contract's `compressInput`, plus the contract's own multi-block controls
  (`Controls/Blake2s.lean`), which is adequate. Optionally add a two-block stream KAT
  (`stream_complete` on a 65-byte `B`, output against `hashlib`) as a compiled-side test in the
  dump tool, not by `decide +kernel`.

## Verdict

**S-E1's Lean is accepted.** The ten modules build in a fresh tree with the three standard axioms
and a clean source rule. The provenance is accurate and the re-basing matches A.6. Every statement
under review is true as written:
- `leaf_sound`, `stream_traceDigest`/`blake2s_chain`, `block_sound_gen`, `holdsE_sound` (including
  `one = 1`) and `walkE_eq_sum`;
- each has a positive and, where meaningful, a negative control;
- `leaf_sound` and the stream lemmas are sufficient for `final` with hypotheses (`Padded`,
  `h_in(0) = h0`, links, `IsBool`, `item_aligned`'s sizes) that the protocol discharges as
  §2.3/§4.3 describe.

The two majors are interface defects that S-E1 exposed, not errors in its proofs:
- `hashStmt` as specified is not buildable on `block_sound_gen`, and fixing it breaks
  `A = I ⊗ A₀` (M1);
- the leaf's `(0,0)`/`E` convention is unpinned and the P2 prover disagrees with the Lean (M2).

Both must be settled, by a blueprint revision and a prover alignment, before S-E2 (`FRWots`,
`hashStmt_sound`, `node_sound`) and before P2's leaf proofs are checked against the Lean `acc`.
S-E1 can be committed after its minors are answered.
