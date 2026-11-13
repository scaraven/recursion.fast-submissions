# typed-spartan

A typed, bus-free recursion backend: rolls 7 and 8 of the `leanvm-inspired` entry (PR #11; roll 6 is #19,
`listless-whir`), submitted under their own root.

A recursive hash-based SNARK entry. It uses leanVM's proof system over binary fields, adapted to the
contract's signed random oracle and to its cheap-extractor fuel cap. Each step is one proof: a new
Keccak-256 chain, plus the previous signed proof verified inside the circuit. `NOTES.md` has the design,
the numbers and the dead ends.

**Changes since pr19-0bdb3ad5e872** (evaluated S = 3.088, S× = 1.555):
- **A typed backend for the recursion circuit.** The node program commits only its row results: one word per `K`
  result, three per `E` result. Four static matrices (write `W`, factors `A` and `B`, addend `D`) give one relation
  per row, `Az·Bz + Dz + Wz = 0`. It is checked by:
  - a degree-3 zerocheck (20 rounds);
  - a degree-2 wiring sumcheck (21 rounds);
  - a 19-round relayout of the child's trace from `C_rec`'s stride-17 order.

  `V` evaluates the program's wiring polynomial `Φ_Q` once per proof, natively, through the A23 accumulator at 43
  variables. It uses bit-map, shift and record-read kernels, the last by a carry automaton. The committed table
  region is 842,060 words, against roll 7's 5.38 M.
- **A mini-bus (depth 13)** keeps leanVM's logup bus only for `capTpl`'s data-addressed reads. `Q_link`'s lane-check
  constants (QLT) are constants of `Φ_Q`.
- **`C_main` at 2^23 words, rate 1/4:** `(6,2,115)(4,3,77)(4,4,58)`. `L₀ = 124·304 = 37,696` candidate pairs; worst
  group 2^-128.33.
- **Two shapes split at `n = 2^18`** (roll 7's SH2-Z). Small steps commit their tables on the even words: half the
  NTT and half the level-0 hashing, with the same proof size and queries.
- **The sponge table at 2^13 rows** (KS14 in roll 7, then KS13).
- **#17's Z2 at 46/35 lanes** (`C_main` root leaf 368 B, `C_rec` 280 B).
- **A new certificate on the typed objects** (`certificateT20`), with `kcertSJ` unchanged. The runtime guard is
  `staticOkB20`. The dead bus path is pruned from `certified`'s closure.
- **Sizes:** `|π|` 644,576 → **464,544 B**, `qS` 7,426 → 5,464.
- **Measured on dev, against roll 7:**
  - V badge 218.5/206.5 → **140/138 ms** (small/big);
  - step medians −0.32 to −0.75 s on a real stream.
- **Local season shape:** S 3.655, S× 2.577, mean `V` 120.2 ms [measured, dev, host loaded].

Earlier:
- pr19-0bdb3ad5e872 (#19) moved `C_rec` to the Johnson radius. Its knowledge soundness comes from one invariant
  used as luck, and it extracts with no list decoder. It also ported #17's Z2 and shared address columns.
- pr11-c65f417243e9 added grinding and the Johnson `C_main` (longfellow-zk's proofs, `LvmJB*`, Apache-2.0,
  `LICENSE-longfellow`).
- pr11-9e756ce6880a replaced the chain table by a digest-only Keccak tape.
- pr11-2f57ce79224a gated the chain link by `n`.

## Trust surface

- **The certificate.** `certified : CertificateR declared submission` is `Lvm.CT.certificateT20` (`LvmCertT20`).
  Its axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorry` and no `native_decide`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`, `fuel = 2^46 + 8192·t`.
- **Proved.**
  - KS of the IOP: `kcertSJ` on the typed front end (`typedSpecR` via `midSpecR_T₂`).
  - The node relation: `nodeT20B`, with `holds_of_wiring` and the typed HAR `harithT20`.
  - `Φ_Q`'s evaluator: `PhiQC_eq`.
  - The native `V`'s refinement: `refines_VST`.
  - The extractor's cost: `computesX`.
- **Facts about the concrete program.** Kernel `decide`s at the frozen record: sizes, lanes, the mini-bus's read
  blocks, the position lanes and `Q_link`'s static checks.
- **The runtime guard.** The kernel cannot build `Q` or evaluate the layout solver, so the rest is one `Bool`:
  `staticOkB20 = staticOkT20 && oneOkB && nodeChkB && harChkB`. It covers:
  - `Q.wf` and the layout;
  - `Φ_Q`'s cache check;
  - V's regions;
  - the mini-bus record;
  - QLT's constants;
  - the input map;
  - the `readd` targets;
  - the claim lists of both shapes.

  `submission = subG staticOkB20 VSB20` rejects every SNARK proof when the guard is false. The certificate holds for
  both values (`certificateR_guardV`, `certificateR_reject`), so the guard affects completeness only. The compiled V
  evaluates it once per process: 16.4–16.9 s on dev, outside the timed check. It is `true`.
- **Soundness error.**
  - The model gives ≈ 2^-128.33 (`C_main` level 0's query group). KS adds only the list luck (2^-165.4).
  - Lean proves `εFS ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128` (`εFS_kcertSJ`): no doom; luck = the invariant's
    escapes (every group `≤ 7·2^-131`, over `L₀ = 37,696` pairs) plus the extractor's list luck (`≤ 2^-132`); hash.
- **Vendored proofs.** `LvmJB*` are longfellow-zk's Johnson-bound proofs (`formal/ligero` @ 1c06629, Google,
  Apache-2.0) in the Flock entry's flat port, renamed only; see `LICENSE-longfellow`.

## The proof system in one list

- **Fields.** `K = GF(2^64)` and `E = K[y]/(y^3+y+1)` (CompPoly `BF64`, `BF64.Ext3`), the same as leanVM.
- **Step statement.** `nodeStmt c_L (leafStmt h n)`.
  - Right child: a witness-sending leaf, checked natively.
  - Left child: the previous signed proof, verified in the circuit.
  - A flag `b = 0` gives step 1's first proof.
- **Chain.** A 2^20-row Keccak tape that commits only each row's 256-bit digest `D[i]`. leanVM's GKR (RMFE), one
  segment of depth 24, proves the permutations. A wiring sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ n − 1]`,
  a slot reduction and one ring switch tie the GKR's input claim to bit slices of `D`.
- **Child verification.**
  - A 2^13-row sponge table: the trace digest, one WOTS walk and the statements.
  - `BITS` rows.
  - A LoopIR program (affine-address loop tables) that recomputes the child's verifier on its trace.
- **Backend.**
  - The program's rows are typed and commit their results only.
  - A zerocheck and a wiring sumcheck bind them to `Φ_Q`. A relayout sumcheck reads the child's trace from `C_rec`.
  - The A23 accumulator carries `Φ_Q`'s claim. `V` checks one evaluation, and the parent's circuit checks the
    child's fold.
  - `capTpl`'s data-addressed reads go through a depth-13 logup mini-bus.
- **Commitments**, both stacked WHIR at the Johnson radius with 14 bits of grinding per level:
  - `C_main`: 2^23 words, (6, 1/4, 115), (4, 1/8, 77), (4, 1/16, 58), OOD on levels 0–1, never decoded. Small steps
    use its even words.
  - `C_rec`: 2^19 words holding the child's trace and signature; (6, 1/4, 115), (4, 1/8, 77), OOD after level 0,
    final 2^9. The extractor decodes it with UD programs on the transcript's advice.
- **Transcript.** A hash chain over the contract oracle. Merkle hashes are oracle queries, and queries are
  lane-aligned and classified by length.
- **Sizes (P20).**
  - `qS = 5,464`, `|π| = 464,544 B`.
  - Mini-bus record (13, 1, 6, 936).
  - Root leaves 368 B (`C_main`, 46 lanes) and 280 B (`C_rec`, 35 lanes).

## Main theorem chain (modules in `lean/`)

| step | statement | module |
|---|---|---|
| certificate | `certificateT20`; guard `certificateR_guardV`, `certificateR_reject`; `sf20`, `staticFactsT20` | `LvmCertT20`, `LvmCertT`, `LvmFinGuard`, `LvmCertTInst`, `LvmQTypedInst`, `LvmQTypedGuard` |
| assembly | `openT20`, `thyp20` (`THyp`), `certificateR_openV`, `ext_eqV` | `LvmCertT20`, `LvmCertTHyp`, `LvmCertT` |
| FS compiler | `kstate_of_kcert`, `ks_of_kcert`: `KCert` (leanVM `Cert` + luck) ⇒ `KState` ⇒ `KS` | `LvmCompileKS` |
| IOP | `kcertSJ` = `kcertOfInv` on `psInv`; typed front end `typedSpecR`, `midSpecR_T₂`, `midShape_T₂` (with `specKgS₂` on the view `Good₂`); accumulator `accSpecQ`, `phiQ_fold`; Johnson WHIR `cfgMain23Jq`, `eps_main23Jq`, `whirEps_rec20Jp`, `codeFacts_johnson`; grinding `escRet_powCheck_le` | `LvmTypedSpec*`, `LvmTypedAcc`, `LvmShape`, `LvmInvCert`, `LvmCertS*`, `LvmWhir*`, `LvmWhirParamsJ23`, `LvmMcaJohnson`, `LvmJB*` |
| rows ⇒ relation | `holds_of_wiring`, `rowDef_of_wiring`, `auxRow_of_wiring`; `nodeT20B` (`nodeSoundT`, `inMapT`, `readdOk_of_chk`, `mbRead_seeded`, `outT_sound`, `decideFT_of`); typed HAR `harithT20`; roll 7's `chain_of_tape`, `qlink_sound`, `qsig_sound` | `LvmTyped`, `LvmTypedLHolds`, `LvmNodeSoundT*`, `LvmQTypedHar*`, `LvmQTypedBitsS`, `LvmTapeRel`, `LvmQLink*`, `LvmQSig*` |
| `Φ_Q` | `PhiQC_eq` (the compiled evaluator is the multilinear extension of the four matrices), `compileT_eq`, `compileTF_eq`, `cacheT20_eq` | `LvmWiring*`, `LvmQTypedInst` |
| verifier | `refines_VST`, `refinesT20L`, `midFollowsT20L` (native `VST` ⇒ the compiled typed program); closed forms `regClaim_rel`, `relayKernF_rel`, `virtEF_rel` | `LvmTypedVEq*`, `LvmTypedV*`, `LvmVerifierS` |
| extractor | `computesX` (cost at the declared fuel), `extJ`, `decode_SJ`, `esc_luckJ_le_132` | `LvmXTop`, `LvmXSpec`, `LvmCertSExtJ*`, `LvmCertSLuckJ`, `LvmXDec*` |

Completeness is the witness-sending kind (`P := encode`, error 0). The harness tests the native prover.

## Layout

`lean/` holds 663 flat modules (≈ 203 k lines), all prefixed `Lvm`; `Solution`'s closure is 599 of them.

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
| assembly | `LvmCertT*`, `LvmCertS*`, `LvmNodeSound*`, `LvmSubmissionST*`, `LvmFinGuard`, `LvmFinPos`, `Solution` |

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
  - Each is ≈ 33 MB, because of the embedded layouts.
  - The runner links them with `gcc -static -O2 -pthread *.s -lm`, which took 5.3 s on dev.
  - The `.s` output is reproducible byte for byte.
- **Lean.** Use the harness `evaluate.py cert` on this root (submission guide §5). Only `Solution`'s import closure
  is built.

## Trust notes

- **Measured vs estimated.**
  - Local timings come from a QEMU dev VM, on which v4 cannot start. They use the dev variant v4p.
  - Against roll 7 on the same stream: steps −0.32 to −0.75 s; V badge 140/138 ms. Local season: steps 1.61–8.15 s,
    fit 0.729 s + 6.84 µs per permutation, peak RSS 6.66 GiB, mean `V` 120.2 ms.
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
- listless-whir (#19): this root's previous roll.
- relay-slim (#17): Z2, root leaves carrying only their occupied lanes (Apache-2.0), and the C-order link in
  `build-asm.sh`.
- relay-echo (#12): the AVX-512VL Keccak chain kernel generator (Apache-2.0, `LICENSE`).
- leanvm-gkr-fast (#13): the re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0), our v4
  tier. leanvm-fast-verify (#15): every-round storage, measured faster on Zen 4.
- The earlier Flock-class recursive entry: the extractor framework, field kernels, the UD line lemma,
  the sponge layer, the W/S dispatch, the oracle client and the assembly pipeline.
- [longfellow-zk](https://github.com/google/longfellow-zk) (`formal/ligero`, Apache-2.0), in the Flock entry's
  port: the Johnson list bound and Haböck's strong mutual correlated agreement (`LvmJB*`, `LICENSE-longfellow`).
- The organiser's core library: `WitnessSending`, `KState`/`KS` and the fast Keccak and signature twins.
