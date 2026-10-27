# S-E1 (track L-circ, first half): RESULT

Stage S-E, first half: the BLAKE2s circuit, the block layout, the chain and stream blocks, and the
leaf circuit of `submissions/flock-recursive`. 2026-10-27, branch `v4/flock-recursive`
(uncommitted on top of `8ff873c`), against BLUEPRINT **revision 3.2** (`2709159`; this work began
on revision 2 and was adapted to revision 3.1's public target and revision 3.2's `hashStmt`
constants, see §5). Build tree `logs/fr-build-circ` (copy of `logs/fr-build/gen.sh`), logs under
`logs/S-E1/`. Evidence tags as in the blueprint: **kernel** (theorem name), **measured** (log).

## 1. What was built

Code lines by the core's `scripts/loc.py` (`logs/S-E1/loc.txt`):

| Module | code (total) | Budget (§7) | Content |
|---|---|---|---|
| `FRBlake2sCircuit` | 450 (677) | | **R**: spartan-srom's product circuits and `BlockR1CS`, renamed; unchanged |
| `FRBlake2sWords` | 630 (859) | | **R**: the word gadgets, renamed; unchanged |
| `FRBlake2sCompress` | 463 (645) | | **R**, **re-based** to A.6 (§2): `blake2sCircuit`, `blake2s_sound`, `blake2s_complete` |
| `FRBlake2sGeneric` | 337 (486) | | **R**: the generic gadget simulation; one input range re-based |
| `FRBlake2sWalk` | 194 (266) | | **R**, retargeted: `walkAB`, `walk_eq_sum` over **every** row of the circuit (general row weights `e`, column weights `wt`), `rowOf_cpos` |
| `FRBlake2sWitness` | 188 (266) | | **R**, retargeted: `fastTrace inp` (any input block), `fastTrace_eq`, `blockAt`, `circuitRows_eq` |
| BLAKE2s subtotal | **2,262** | 1,550 + 730 = 2,280 | |
| `FRBlockLayout` | 319 (508) | 350 | **N**: A.6 positions; `circuitR1CS`; the **public target** (`Target`, `blockR1CS tgt`, `targetVal`, `HoldsE`, `TargetOk`, `holdsE_sound`, `holdsE_complete`, `zero_not_holdsE`, `walkE_eq_sum`); rows `rowOf_one`/`rowOf_input`/`rowOf_zero`; readers `hIn`, `hOut`, `msgBytes`, `readDigest`; `compress_sound`; BLAKE2s facts `blake2sDigest_eq`, `block_congr` |
| `FRBlockChain` | 180 (278) | (new, §5) | **A/N**: `chainTarget`, `chainStep_eq`, `block_sound`, `block_complete`, controls |
| `FRBlockStream` | 269 (408) | 600 | **A/N**: `chainState`, `blake2s_chain`, `traceDigest_chain`; `blockTarget t fin`, `block_sound_gen`, `streamTarget`, `block_sound`; `stream_sound`, `stream_traceDigest`; `item_aligned`, `elem_slot`; controls `stream_complete`, `zero_control` |
| `FRLeafCircuit` | 94 (165) | 1,200 | **A**: `ChainLinks`, `leaf_sound`, `chain_of_blocks`, `leafWitness`, `leafBlockBits`, `leaf_complete`, `zero_table_control` |
| **total** | **3,124** (4,558) | | |

Provenance: each copied module's first lines name its source (`submissions/spartan-srom/lean/
SpartanSromBlake2s*.lean` at `783328c`) and what changed; the leanerVM provenance in the module
docstrings is kept. spartan-srom's `SpartanSromBlake2sR1CS` (the chain block with constant rows)
is not copied as a module: its reusable part (`h0`, `leDigest`, the readers, `block_getLsbD`, the
one-block lemma) is in `FRBlockLayout`, its chain-specific part is rewritten in `FRBlockChain`.

### Main statements (all **kernel**; axioms `propext`, `Classical.choice`, `Quot.sound` at most, 40 declarations, `logs/S-E1/axioms.log`, script `logs/S-E1/Axioms.lean`)

The block R1CS with the public target (BLUEPRINT §4, revision 3.1): for a `Target`
`tgt : Pos → Option Bool`, `blockR1CS tgt` is the circuit's R1CS with `(0, 0)` rows at the pinned
positions, `targetVal R tgt` is `E`, and

```
HoldsE C E z := ∀ k, (A z)_k · (B z)_k = z_k + E_k.
```

- `Block.holdsE_sound : TargetOk tgt → HoldsE (blockR1CS tgt) (targetVal R tgt) (liftBlock R w) →
  circuitR1CS.Holds (liftBlock R w) ∧ w onePos = true ∧ MeetsB tgt w` (and `holdsE_complete`).
  `TargetOk`: the target pins `one` to `1` and otherwise only inputs; so `one = 1` is delivered by
  the target, as revision 3.1 says.
- `Block.walkE_eq_sum`: `walkAB (e masked to 0 on the pinned rows) wt = (Σ_k e k (A₀ wt)_k,
  Σ_k e k (B₀ wt)_k)` for `A₀, B₀ = blockR1CS tgt`, any row weights `e` (the skip coordinate's
  Lagrange weights at `λ` times `eq`) and column weights `wt`.
- `Chain.block_sound : HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R w) →
  readDigest w 256 = chainStep (readDigest w 520)`.
- `Stream.blake2s_chain : blake2sDigest B = leDigest (chainState B (nBlocks B.length))` and
  `Stream.traceDigest_chain : traceDigest tr = leDigest (chainState (0x54 :: traceBytes tr) …)`:
  the contract's BLAKE2s as the chain of compressions, proved against `compressInput`, not
  assumed.
- `Stream.block_sound_gen : HoldsE (blockR1CS (blockTarget t fin)) … → hOut w = compress (hIn w)
  (block (msgBytes w)) t.toUInt64 (flagOf fin) 0`, general in the counter `t` and the final flag
  (the node's `hashStmt` instantiates `(41, final)`, `(64, ¬ final)`, `(65, final)`, revision 3.2);
  `Stream.block_sound` is the case `streamTarget L i = blockTarget (ctrAt L i) (i + 1 = nBlocks L)`.
- `Stream.stream_sound`: `nBlocks L` Boolean blocks with `HoldsE` under their stream targets,
  `h_in(0) = h0` (`hstart`), links `h_out(i) = h_in(i + 1)` (`hl`, bitwise) and zero padding past
  `L` bytes (`Padded`) carry `blake2sDigest (streamBytes w L)` at the last block's `h_out`;
  `Stream.stream_traceDigest`: equal to `traceDigest tr` when the slots hold `0x54 ‖ traceBytes tr`.
- `Stream.item_aligned`: with the first query `≡ 7 mod 16` (7-byte seed tag) and the others
  `≡ 8 mod 16`, every item after the first starts at an offset `≡ 0 mod 16` of the hashed stream;
  `Stream.elem_slot`: stream element `e` is message slot `4 + e mod 4` of block `⌊e/4⌋`.
- **`Leaf.leaf_sound`**:

  ```
  leaf_sound (hn : 1 ≤ n) (z : ℕ → Pos → R) (s h : Digest)
      (hbool : ∀ i < n, ∀ k, IsBool (z i k))
      (hE : ∀ i < n, HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (z i))
      (hlinks : ChainLinks n z s h) : chainEnd s n = h
  ```

  over any `[CommRing R] [CharP R 2] [Nontrivial R] [DecidableEq R]`; `ChainLinks n z s h` = the
  links `z (i+1) [520 + j] = z i [256 + j]` for `i + 1 < n`, `z 0 [520 + j] = s_j`,
  `z (n−1) [256 + j] = h_j`. Every hypothesis is about the **used blocks `i < n` only**.
- `Leaf.leaf_complete`: for `n ≥ 1`, the honest table `leafWitness s` (block `i` =
  `chainTrace (chainEnd s i)`) meets `hbool`, `hE` and `ChainLinks n z s (chainEnd s n)`;
  `leafBlockBits d` is the same block computed (`fastTrace`, `leafBlockBits_eq`).

## 2. The re-basing (Appendix A.6)

Only the six layout constants and the input set of `FRBlake2sCompress` moved:
`constPos 512 → 1152`, `msgBase 640 → 512`, `counterLo 1152 → 1024`, `counterHi 1184 → 1056`,
`finalFlag 1216 → 1088`, `lastNodeFlag 1248 → 1120`, inputs `0…255 ∪ 512…1151`. The gate
positions (`1280…15999`) and leanVM's gadget order are unchanged; every proof went through with
only the range numerals edited (the gadgets read inputs through `inW msgBase …`). The output rows
`(out form, one)` at `256…511` and the zero rows at `1153…1279`, `16000…` are as A.6
(`rowOf_zero`).

## 3. Build and check times (development VM, QEMU, 32 vCPU, shared, load 4–13)

| Measure | Value | Log |
|---|---|---|
| clean build of the ten modules, lake parallel | **74 s wall** (Circuit 4.2, Words 7.3, Compress 12, Generic 9.2, Walk 3.4, Witness 10, Layout 6.4, Stream 4.7, Chain 15, Leaf 3.3 s) | `logs/S-E1/build-clean.log` |
| source rule (whole entry) | 33 files, 0 findings | `logs/S-E1/source-rule.log` |

Per module, `lake env lean --profile` pinned to one core (`taskset -c 5`), "kernel" = the
profiler's cumulative `type checking`:

| Module | kernel | elaboration | wall | Log |
|---|---|---|---|---|
| `FRBlake2sCircuit` | 0.82 s | 3.8 s | 11.0 s | `logs/S-E1/profile-FRBlake2sCircuit.log` |
| `FRBlake2sWords` | 4.98 s | 4.1 s | 18.8 s | `profile-FRBlake2sWords.log` |
| `FRBlake2sCompress` | 3.65 s | 2.9 s | 25.2 s | `profile-FRBlake2sCompress.log` |
| `FRBlake2sGeneric` | 0.97 s | 2.0 s | 16.9 s | `profile-FRBlake2sGeneric.log` |
| `FRBlake2sWalk` | 0.25 s | 1.0 s | 7.7 s | `profile-FRBlake2sWalk.log` |
| `FRBlake2sWitness` | 7.22 s | 0.8 s | 13.6 s | `profile-FRBlake2sWitness.log` |
| **BLAKE2s modules** | **17.9 s** | | | (target: spartan-srom's ≈ 30 s) |
| `FRBlockLayout` | 4.04 s | 1.7 s | 14.8 s | `profile-FRBlockLayout.log` |
| `FRBlockChain` | 3.74 s | 1.0 s | 19.5 s | `profile-FRBlockChain.log` |
| `FRBlockStream` | 2.39 s | 1.4 s | 11.7 s | `profile-FRBlockStream.log` |
| `FRLeafCircuit` | 0.27 s | 0.2 s | 6.2 s | `profile-FRLeafCircuit.log` |
| **all ten** | **28.3 s** | | | |

The largest single kernel cost is `fastTrace_eq` (5.5 s, the generic simulation over the 14,720
gates, as in spartan-srom). The one `decide +kernel` (`chainStep_zero_kat`, one BLAKE2s
compression of the contract's spec function) costs 1.7 s.

## 4. Controls (all **kernel**)

| Control | Kind | What it shows |
|---|---|---|
| `Chain.chainStep_zero_kat` | positive KAT | the contract's `chainStep` (BLAKE2s-256 of `0x43 ‖ 0^32`) equals Python's `hashlib.blake2s` known answer (`decide +kernel`) |
| `Chain.chainTrace_zero_kat` | positive KAT | **the circuit on one block**: the honest chain block of the zero digest satisfies the block R1CS with its target and carries that known answer at `256…511` |
| `Chain.not_holds_flip` | negative | flipping any output bit of a satisfying block breaks the R1CS (so every honest block is pinned) |
| `Block.zero_holds` + `Block.zero_not_holdsE`, `Chain.zero_control`, `Stream.zero_control` | negative (BP-C-M5) | **the all-zero block (`one = 0`) satisfies the circuit's R1CS but not the block R1CS with the target**: the target is what excludes it |
| `Leaf.zero_table_control` | negative (BP-C-M5, leaf level) | the all-zero one-block table with `s = h = 0` has `0`/`1` entries, satisfies the circuit's R1CS and `ChainLinks`, yet `chainEnd 0 1 ≠ 0`; it fails `hE`, so `leaf_sound` would be false without the target |
| `Leaf.leaf_complete` | positive (non-vacuity) | the honest table meets every hypothesis of `leaf_sound`, for every `s` and `n ≥ 1` |
| `Stream.stream_complete` | positive (non-vacuity) | for every byte string `B`, the honest blocks meet every hypothesis of `stream_sound` (and hold `B`); with `|B| = 41` and `|B| = 65` this covers `hashStmt`'s `(41, final)`, `(64, ¬final)`, `(65, final)` targets |
| `Chain.block_complete`, `Block.holdsE_complete`, `blake2s_complete` | positive | the honest block satisfies each R1CS |

`walk_eq_sum`/`walkE_eq_sum` are equalities of definitions (no control needed beyond the proof);
the walk's row weights are arbitrary.

## 5. Deviations from the blueprint, with reasons

1. **Revision changes absorbed mid-stage.** The stage started on revision 2 (patterns as
   hypotheses, `one = 1` explicit, BP-E-R2-M1). Revision 3.1 replaced patterns by the public
   target; the statements were rewritten to `HoldsE` + `ChainLinks` (no `Patterns`/`IOHolds`, no
   separate `one` hypothesis). Revision 3.2: `block_sound_gen` is general in `(t, fin)`.
2. **Two R1CS, one circuit.** `circuitR1CS` (the re-based BLAKE2s circuit, where `t`, `f` and the
   chain constants are *inputs* with rows `(var k, var one)` and `one` has `(one, one)`) is the
   gate-level object the proofs run on; the entry's block R1CS is `blockR1CS tgt`: the same rows
   with `(0, 0)` at the target's positions. `holdsE_sound` bridges them. This keeps the copied
   circuit and its boundedness proof unchanged.
3. **`A₀` depends on the target's support**, which is per circuit kind: the leaf's chain blocks pin
   `h_in`, the tag, the zero bytes, `t`, `f`, `one` (`chainTarget`); the node's stream blocks pin
   `t`, `f`, `one` (`blockTarget`, same support for every block and every `(t, fin)`, only `E`
   varies). So `A = Sel ⊗ A₀` holds within each circuit; the leaf's `A₀` and the node's differ.
   **Blueprint/prover note:** A.6 should state the `(0, 0)`-row set of each kind (the prover's row
   generator and the walk's mask depend on it). The zero rows `1153…1279`, `16000…` have `E = 0`
   and are equivalent to pinned-to-`0` positions.
4. **`FRBlockChain` is a separate module** (the §7 table has `FRBlockLayout`, `FRBlockStream`,
   `FRLeafCircuit`); the task named it. The leaf's chain block is not "the stream block with a
   constant pattern" as revision 2 §4.1 said: its target also pins `h_in` and message bytes.
5. **`stream_sound`'s `h_in(0) = h0` and padding are hypotheses** (`hstart`, `Padded`), as revision
   3.1 says they are the shift argument's endpoint and point claims on `f`.
6. **`leaf_sound` is stated for every `n ≥ 1`**, not only `2^(m−14)`, over a ring with
   `[DecidableEq R]` (needed to read bits off `0`/`1` entries; `ZMod 2` and `F` have it).
7. **The IO dump functions of spartan-srom's witness module are dropped** (§8.1 puts the dump tool
   outside `submissions/`); the pure `circuitRows`, `rowLine`, `hexForm` remain for it to call.

## 6. Open questions

1. A.6 / §4: please pin the `(0, 0)`-row set per kind (deviation 3): leaf = `chainTarget`'s
   support (`0…255`, `512…519`, `776…1023`, `1024…1152`); node stream, `hashStmt`: `1024…1152`.
   WOTS blocks (S-E2) will need their own.
2. `walkE_eq_sum` takes the masked row weights; the verifier's IR op `walkA`/`walkB` should mask
   by the kind's support (one `if` per position, or a closed form: the support is a few
   intervals). S-0/S-E2 to decide.
3. `item_aligned` assumes the query sizes `≡ 7` (first) and `≡ 8 mod 16`; `FRFormat`/`FRVIRSpec`
   must provide these facts for the shapes' item sequences.
