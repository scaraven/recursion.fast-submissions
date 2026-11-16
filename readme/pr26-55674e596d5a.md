# halved-phi

The `leanvm-inspired` entry's roll "E2-FT" (stage `S2GF`): the Keccak front at `E2 = GF(2^128)` with grinding, a
root out-of-domain pin, and twin-row `E2` cells in the typed backend. It continues #21 (`lone-root`, roll 11),
#20 (`typed-spartan`), #19 (`listless-whir`) and PR #11, under its own root.

A recursive hash-based SNARK entry. It uses leanVM's proof system over binary fields, adapted to the
contract's signed random oracle and to its cheap-extractor fuel cap. Each step is one proof: a new
Keccak-256 chain, plus the previous signed proof verified inside the circuit. `NOTES.md` has the design,
the numbers and the dead ends.

**Changes since pr21-94f86c9c3d9b** (#21, `lone-root`; evaluated S = 2.070, S× = 1.2485):
- **The front at `E2`.** The tape GKR, wire, slots, `KS` GKR and `KS` link run at `E2 = K[X]/(X² + xX + 1)`: 16-B
  scalars, and every `E2` challenge ground on its own 8-B nonce (lane 2 of the answer `< 2^(64−g)`, g = 1, 2 or 6;
  1,085 nonces per proof). Bit slices go through a 2^7-row row switch; `E2` word claims enter the PCS as two
  `K`-linear claims (tensor switch).
- **The root OOD pin.** One point `z ∈ E^23` and its claimed value right after `C_main`'s cap leave at most one list
  member (`candZ`), so the middle phases run at `L₀ = 1` instead of 124. M′'s certificate is reused unchanged
  (`kcertSF` = `kcertSM` at the pinned middle phases).
- **Twin-row `E2` cells** in the typed backend, checked by a coordinate-split zerocheck (one more `E3` sample `ω`, 6
  values at `r_x`, 8 matrix values); `Φ_Q` has 44 variables. The compiled scheme reads 24, 16 or 8 B per read.
- **Sizes [exact]:** `|π|` 332,336 → **306,992 B (−7.6 %)**, `qS` 3,895 → 3,959.
- **Measured on dev, against #21's prover:** step medians 2^17 1.576 → 1.419 s, 2^18 2.366 → 2.098 s, 2^20 7.510 →
  6.289 s; slope −1.22 to −1.37 s per 2^20. **`V` is slower:** ≈ 145 / 123 ms per check (small / big) against
  ≈ 105 / 100 ms, mostly `Φ_Q` (≈ 70 ms against ≈ 40); start-up ≈ 44 s, untimed.
- **Projected [model]:** S ≈ 1.96–2.02 (−2.5 to −5.4 %), S× ≈ 1.09–1.11 (−11 to −13 %).
- **Certificate:** `certificateF20S`, axioms `propext`, `Classical.choice`, `Quot.sound`; the claim and `εFS`'s form
  are unchanged.

**Earlier rolls:**
- #21 (pr21-94f86c9c3d9b, S 2.070, S× 1.2485) merged `C_rec` into `C_main`: one commitment, the child's stream in
  lanes 40–47, `|π|` 464,544 → 332,336 B.
- #20 (pr20-79a1a990cd1a, S 2.341, S× 1.258): the typed, bus-free backend (results-only witness, zerocheck and
  wiring sumcheck against four static matrices, `Φ_Q` through the A23 accumulator), `C_main` at ν = 23 rate 1/4,
  two shapes, `KS` at 2^13 rows, #17's Z2.
- pr19-0bdb3ad5e872 (#19) moved `C_rec` to the Johnson radius, with knowledge soundness from one invariant used as
  luck and no list decoder.
- pr11-c65f417243e9 added grinding and the Johnson `C_main` (longfellow-zk's proofs, `LvmJB*`, Apache-2.0,
  `LICENSE-longfellow`); pr11-9e756ce6880a the digest-only Keccak tape; pr11-2f57ce79224a the `n`-gated chain link.

## Trust surface

- **The certificate.** `certified : CertificateR declared submission` is `Lvm.CT.certificateF20S`
  (`LvmCertF20Inst`). Its axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorry` and no
  `native_decide`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`, `fuel = 2^46 + 8192·t`.
- **Proved.**
  - KS of the IOP: `kcertSF` on `midSpecP_F₂` (the pin `pin_escape`/`candZ`, the `E2` front's specs, the typed
    phases on twin rows `typedSpecX`, relocated onto `C_main`'s stream block).
  - The node relation: `nodeF20` on stream-block pairs, with `holds_of_wiringX` and the S2GF HAR `harithF20`.
  - `Φ_Q`'s evaluator: `PhiQCX_eq`.
  - The native `V`'s refinement: `refinesF20` (against the compiled scheme with per-read widths).
  - The extractor's cost and agreement: `computesXF20`, `ext_eqF20`.
- **Facts about the concrete program.** Kernel `decide`s at the frozen record: the S2GF schedule's sizes and read
  widths (`checks_P20F`), the extractor's replay (`replayOK_stF20`), lanes and `Q_link`'s static checks.
- **The runtime guard.** The kernel cannot build `Q` or evaluate the layout solver, so the rest is one `Bool`:
  `staticOkBF20 = staticOkTF20 && nodeChkBG … && sigInSB && harChkBF20 && oneOkB` (`Q.wf`, the layout, `twinsOk`,
  `Φ_Q`'s caches, V's regions, the mini-bus record, QLT's constants, the input map, the `readd` targets, the PoW
  lanes and the claim regions). `submissionF20 = subGF staticOkF20 (VSFX NTF20)` rejects every SNARK proof when the
  guard is false; the certificate holds for both values (`certificateR_guardF`), so the guard affects completeness
  only. The compiled V evaluates it once per process, outside the timed check. It is `true`.
- **Soundness error.**
  - The model gives ≈ 2^-128.33 (`C_main` level 0's query group); the ground `E2` groups are at ≤ 2^-128.42, the pin
    at 2^-174.6. KS adds only the list luck (2^-159.93).
  - Lean proves `εFS ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128` (`εFS_kcertSF`).
- **Vendored proofs.** `LvmJB*` are longfellow-zk's Johnson-bound proofs (`formal/ligero` @ 1c06629, Google,
  Apache-2.0) in the Flock entry's flat port, renamed only; see `LICENSE-longfellow`.

## The proof system in one list

- **Fields.** `K = GF(2^64)` and `E = K[y]/(y^3+y+1)` (CompPoly `BF64`, `BF64.Ext3`), the same as leanVM, and
  `E2 = K[X]/(X² + xX + 1)` for the front's challenges.
- **Step statement.** `nodeStmt c_L (leafStmt h n)`.
  - Right child: a witness-sending leaf, checked natively.
  - Left child: the previous signed proof, verified in the circuit.
  - A flag `b = 0` gives step 1's first proof.
- **Chain.** A 2^20-row Keccak tape that commits only each row's 256-bit digest `D[i]`. leanVM's GKR (RMFE), one
  segment of depth 24 at `E2`, proves the permutations. A wiring sumcheck with the public kernel
  `ι(x + 1)·[x + 1 ≤ n − 1]`, a slot reduction and a row switch tie the GKR's input claim to bit slices of `D`.
- **Child verification.**
  - A 2^13-row sponge table (GKR at `E2`): the trace digest, one WOTS walk and the statements.
  - `BITS` rows.
  - A LoopIR program (affine-address loop tables, `E2` values as twin rows) that recomputes the child's verifier
    on its trace.
- **Backend.**
  - The program's rows are typed and commit their results only.
  - A zerocheck (coordinate-split for the twin rows) and a wiring sumcheck bind them to `Φ_Q`. A relayout sumcheck
    reads the child's trace from `C_main`'s stream block.
  - The A23 accumulator carries `Φ_Q`'s claim (44 variables). `V` checks one evaluation, and the parent's circuit
    checks the child's fold.
  - `capTpl`'s data-addressed reads go through a depth-12 logup mini-bus.
- **One commitment**, pinned by one OOD point after its cap; stacked WHIR at the Johnson radius with 14 bits of
  grinding per level:
  - `C_main`: 2^23 words, (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, 58), OOD on levels 0–1. Small steps use its even
    words.
  - Its stream block `S` (2^19 words) holds the child's trace as 17 columns of stride 2^14, plus `σ'`; it lies in
    lanes 40–47. The extractor decodes only those lanes, at three levels, with UD programs on the transcript's
    advice.
- **Transcript.** A hash chain over the contract oracle; reads of 24, 16 or 8 B. Merkle hashes are oracle queries,
  and queries are lane-aligned and classified by length.
- **Sizes (P20).**
  - `qS = 3,959`, `|π| = 306,992 B`.
  - Mini-bus record (12, 1, 6, 633).
  - Root leaf 376 B (`C_main`, 47 lanes).

## Main theorem chain (modules in `lean/`)

| step | statement | module |
|---|---|---|
| certificate | `certificateF20S`; guard `certificateR_guardF`; `sfF20`, `thypF20`, `trefF20` | `LvmCertF20Inst`, `LvmCertF20X`, `LvmE2QNodeF`, `LvmE2QInst` |
| assembly | `certificateSF20`, `ext_eqF20`, `childF20_win`, `computesXF20`; the pinned frame `kcertSF`, `εFS_kcertSF`, `midSpecP_of` | `LvmCertF20*`, `LvmE2FCert`, `LvmE2FPin`, `LvmXS*`, `LvmMPX*` |
| FS compiler | `kstate_of_kcert`, `ks_of_kcert`: `KCert` (leanVM `Cert` + luck) ⇒ `KState` ⇒ `KS`, with per-read widths (`schemeSW`, `runW_eq_run`) | `LvmCompile*` |
| IOP | `kcertSM` = `kcertOfInv` on `psInvM`; the pin `pin_escape`, `candZ`; the middle phases `midSpecP_F₂`: `tapeSpecE2`, `wireSpecE2`, `ksSpecE2`, `ksLinkSpecE2`, `rowSwitchSpec`, `wordClaimE2`, `splitE2_sound`, `typedSpecX`; accumulator `accSpecQ`; Johnson WHIR `cfgMain23Jq`, `codeFacts_johnson`; grinding `escRet_powCheck_le`, `sampleG_escape` | `LvmMPCert*`, `LvmE2V*`, `LvmTypedSpecX*`, `LvmTypedAcc`, `LvmWhir*`, `LvmMcaJohnson`, `LvmJB*` |
| rows ⇒ relation | `holds_of_wiringX`, `twin_of_wiringX`, `e2Pair_of_holds`; `nodeF20` (`nodeSoundFG`, `harithF20`); `E2` gadgets `gE2mul_sem`, `gE2lin_sem`, `powRange_sem`; roll 7's `chain_of_tape`, `qlink_sound`, `qsig_sound` | `LvmTypedX`, `LvmLoopE2`, `LvmE2Q*`, `LvmNodeSound*`, `LvmTapeRel`, `LvmQLink*`, `LvmQSig*` |
| `Φ_Q` | `PhiQCX_eq` (the compiled evaluator over the two coordinate caches is the multilinear extension of the matrices), the fast cache's equality | `LvmWiringX*`, `LvmWiring*` |
| verifier | `refinesF20` (native `VSFX N` ⇒ the compiled program of `PSWithM (midP …)`); fast twins `decideProgFF_eq`, `tensorDotT_eq`, `dOpenFF_eq`; `fe2_mul_eq` | `LvmE2VRefinesF`, `LvmE2VEq*`, `LvmE2VFast*`, `LvmVEq*`, `LvmScheduleF`, `LvmFieldE2*` |
| extractor | `EXF20`, `extXF20`, `computesXS`, `ext_eqS_gen`, `decodeMP0`–`decodeMP2`, the list luck 2^-159.93 | `LvmXS*`, `LvmMPX*`, `LvmMPDec*`, `LvmX*` |

Completeness is the witness-sending kind (`P := encode`, error 0). The harness tests the native prover.

## Layout

`lean/` holds 873 flat modules (≈ 264 k lines), all prefixed `Lvm`; the cert builds `Solution`'s closure.

| group | prefixes |
|---|---|
| fields, DSL, doom rules | `LvmField*`, `LvmDsl*`, `LvmSpec*`, `LvmProg`, `LvmVCore`, `LvmVParams` |
| FS compiler | `LvmCompile*`, `LvmLog`, `LvmForest`, `LvmPotential`, `LvmInvCert` |
| polynomials, Keccak GKR, tape | `LvmMl*`, `LvmCp*`, `LvmSumcheck*`, `LvmGrand*`, `LvmKeccak*`, `LvmK*`, `LvmTapeRel`, `LvmWire*`, `LvmSponge*` |
| bus, ring switching | `LvmBus*`, `LvmSpine*`, `LvmFront*`, `LvmM3*`, `LvmRing*`, `LvmLayout*` |
| WHIR (UD, Johnson, grinding) | `LvmWhir*`, `LvmRS`, `LvmUd*`, `LvmMcaUd`, `LvmMcaJohnson`, `LvmNovelBasis` |
| vendored Johnson bound (longfellow-zk via Flock, Apache-2.0) | `LvmJB*`; `LvmLJ*` (not in the closure) |
| typed backend: layout, wiring, `Φ_Q` | `LvmTypedLayout`, `LvmTypedLay*`, `LvmWiring*`, `LvmTyped`, `LvmTypedLHolds`, `LvmTypedAcc`, `LvmTypedSpec*` |
| two shapes | `LvmShape*`, `LvmQShape*` |
| LoopIR, circuit, program | `LvmLoop*`, `LvmQ*` (`LvmQTyped*` is the typed verifier gadget, the mini-bus and the B program's instance), `LvmQAcc*`, `LvmBits*`, `LvmWots*`, `LvmSig*`, `LvmReplay*` |
| native verifier | `LvmParams`, `LvmSchedule`, `LvmDriver`, `LvmDecide*`, `LvmVerifierS`, `LvmTypedV*`, `LvmVEq*`, `LvmTypedVEq*` |
| extractor | `LvmX*` |
| `E2` front, pin, S2GF (this roll) | `LvmFieldE2*`, `LvmQuad`, `LvmTensorSwitch`, `LvmE2V*` (specs, native front, fast twins), `LvmE2F*` (pin), `LvmE2Q*` (circuit), `LvmTypedX*`, `LvmWiringX*`, `LvmScheduleF`, `LvmXS*` |
| assembly | `LvmCertF20*`, `LvmCertM20` (roll 11's frame), `LvmCertT*`, `LvmCertS*`, `LvmNodeSound*`, `LvmFinGuard`, `Solution` |

`prover/` contains:
- `src/lv/`: the vendored leanVM crates, with every edit in `src/lv/PATCHES.md`. `src/lv/keccak_gkr_v4/` is #13's
  re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0), mounted on the v4 tier only.
- `src/chainwalk.rs`, `src/keccak_vl.rs`: the chain walk and relay-echo's (#12) AVX-512VL kernel, generated by
  `tools/gen_chain_vl.py` from its vendored `tools/gen_vlasm.py` (Apache-2.0, `LICENSE`).
- `src/lvm/`: the schedule, tape, links, accumulator, LoopIR witness, recursion witness and stream, and:
  - `typed*.rs`: the typed backend (witness, zerocheck, wiring, relayout, `Φ_Q` by class kernels, mini-bus);
  - `shape.rs`: the small shape;
  - the embedded program blobs `q-p20.blob` and `q-p8.blob`, with their typed layouts `qb-p*.lay` and `BITS`
    specs `qb-p*.m3b`.
- `src/{service,format,proc,alloc}.rs`: from the earlier Flock-class entry.
- `dispatch.s`: the cpuid stub.
- `build-asm.sh` and `tools/`.

## Building

- **Prover.** Run `prover/build-asm.sh --install`.
  - It needs rustc 1.99.0 and builds offline, with no dependencies.
  - It emits `prover-v2.s` (portable), `prover-v4.s` (Zen 4: VPCLMULQDQ, GFNI, VBMI) and `prover-v4p.s` (AVX-512 +
    PCLMUL), filtered for GNU as 2.42, with symbols suffixed per variant.
  - Each is 48.6–50.0 MB, because of the embedded layouts.
  - The runner links them with `gcc -static -O2 -pthread *.s -lm`, which took a few seconds on dev; the binary is 86.0 MB.
  - The `.s` output is reproducible byte for byte.
- **Lean.** Use the harness `evaluate.py cert` on this root (submission guide §5). Only `Solution`'s import closure
  is built.

## Trust notes

- **Measured vs estimated.**
  - Local timings come from a QEMU dev VM, on which v4 cannot start. They use the dev variant v4p.
  - Against #21's prover (LTO, timing lock): step medians 2^17 1.576 → 1.419 s, 2^20 7.510 → 6.289 s; slope −1.22
    to −1.37 s per 2^20. V badge ≈ 145 / 123 ms (small / big) against #21's ≈ 105 / 100 ms; start-up ≈ 44 s.
  - Zen 4 numbers come from the harness. The v4 tier, #13's GKR, the chain kernel and the worker choice on SMT
    cannot be timed on the dev VM.
- **CPU safety.** `prover setup` self-tests each variant (KATs, a batch proof, a typed P8 proof) against the portable
  reference's digest, and writes a cap that `dispatch.s` honours. v4 was byte-identical to v2 under Intel SDE.
- **No Rust verifier.** The Lean `V_S` is the test oracle. It accepts:
  - the shipped prover's P20 streams across both shapes, in both directions;
  - its P8 streams;
  - the linked `.s` prover's stream.

  The tampers are rejected; an operand tamper in any wiring class is caught only by the `Φ_Q` check.

## Credits

- [leanVM](https://github.com/leanEthereum/leanVM): the protocol, the Rust crates and the `formal/` proofs.
- Spartan (Setty): the shape of the backend, a zerocheck over row constraints and a sumcheck against sparse wiring
  matrices. Here it has a write matrix, no committed matrix, and `Φ_Q` evaluated through the accumulator.
- [leanerVM](https://github.com/Verified-zkEVM/leanerVM): the bus lookup lemma, the generator facts and
  reference formalisations.
- lone-root (#21), typed-spartan (#20) and listless-whir (#19): this root's previous rolls.
- relay-slim (#17): Z2, root leaves carrying only their occupied lanes (Apache-2.0; 47 lanes at M′), and the
  C-order link in `build-asm.sh`.
- relay-echo (#12): the AVX-512VL Keccak chain kernel generator (Apache-2.0, `LICENSE`).
- leanvm-gkr-fast (#13): the re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0), our v4
  tier. leanvm-fast-verify (#15): every-round storage, measured faster on Zen 4.
- The earlier Flock-class recursive entry: the extractor framework, field kernels, the UD line lemma,
  the sponge layer, the W/S dispatch, the oracle client and the assembly pipeline.
- [longfellow-zk](https://github.com/google/longfellow-zk) (`formal/ligero`, Apache-2.0), in the Flock entry's
  port: the Johnson list bound and Haböck's strong mutual correlated agreement (`LvmJB*`, `LICENSE-longfellow`).
- The organiser's core library: `WitnessSending`, `KState`/`KS` and the fast Keccak and signature twins.
