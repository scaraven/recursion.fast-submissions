# listless-whir

Johnson-radius WHIR with no list decoder: roll 6 of the `leanvm-inspired` entry (PR #11), submitted under its own root.

A recursive hash-based SNARK entry. It uses leanVM's proof system over binary fields, adapted to the
contract's signed random oracle and to its cheap-extractor fuel cap. Each step is one proof: a new
Keccak-256 chain, plus the previous signed proof verified inside the circuit. `NOTES.md` has the design,
the numbers and the dead ends.

**Changes since pr11-c65f417243e9** (evaluated S = 3.508, S× = 1.738):
- **`C_rec` at the Johnson radius**: (fold 6, rate 1/4, 115 queries) then (fold 4, rate 1/8, 77), one OOD sample,
  final 2^9; lists of at most 304 and 311 members. **Knowledge soundness from one invariant used as the `KCert`'s
  luck** ("every non-good candidate pair fails a running claim", which holds on honest runs): no doom, so
  `ε = 0`, and every escape from the invariant has the bound of the matching soundness escape (`kcertOfInv`,
  `kcertSJ`).
  **No list decoder**: off list luck the transcript is advice that singles out the good member, and the
  extractor runs the same UD decoder programs (`extSJ`, `decode_SJ`) at the same fuel;
- **root leaves of occupied lanes only** (#17's Z2, ported): V and the extractor read the absent lanes as zero;
  `C_main`'s root leaf 512 → 384 B, `C_rec`'s → 280 B;
- **shared address columns**: a `BITS` class's leading outputs with consecutive cells read their addresses from one fixed column
  (`g^j·col`); table evaluations 2,851 → 2,576;
- **prover plumbing** (proofs byte-identical): the `Readd` tables cached per program, the opening basis's setup in
  parallel, and `prover setup` picks the worker count (`min(CPUs, 8)`, ¾ or ½ of it) by timing a whole P20 step.
  The LoopIR table build starts beside the chain walk: only the `BITS` cone is re-run, and with H-taint the build
  begins with `h = 0` and patches the 4 cells `h` reaches. The commitment buffers are prepared before `ready`, the
  tape witness runs behind the walk, and opened leaf groups are rehashed in parallel;
- `|π|` 783,192 → 644,576 B, `qS` 8,295 → 7,426;
- local season shape (dev VM): ACCEPT, S 5.24 → 4.99, S× 3.49 → 3.40, mean `V` 196.9 → 184.6 ms.

Earlier: pr11-c65f417243e9 added grinding (g = 14) on every WHIR level, moved `C_main` to the Johnson radius
with longfellow-zk's proofs (`LvmJB*`, Apache-2.0, `LICENSE-longfellow`), gave `C_rec` a second UD level, shared
the position-bit tables, shipped a faster native verifier (`VS20G`) and #12/#13/#15's prover kernels;
pr11-9e756ce6880a replaced the chain table by a digest-only Keccak tape (`C_main` 2^26 → 2^24);
pr11-2f57ce79224a gated the chain link by `n`, sped up the prover plumbing and made the native verifier faster
(fast twins in `LvmVFast`, proved equal to the specified `VS20`).

## Trust surface

- **The certificate.** `certified : CertificateR declared submission` is `Lvm.Fin.certificateFin`
  (`LvmFinCert`), after `VS20G_eq : VS20G = VS20F`. Its axioms are `propext`, `Classical.choice` and `Quot.sound`, with no `sorry` and no
  `native_decide`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`, `fuel = 2^46 + 8192·t`.
- **Facts about the concrete program.** They are kernel `decide`s at the frozen record (`LvmQAsmFacts*`,
  `LvmFinDec`), except five that the kernel cannot reach within the caps: `Q.wf`, grouping,
  injectivity, no computed-address read in `Q_arith`, and claim-list well-formedness.
- **The runtime guard.** Those five facts form `staticOkB : Bool`, and `submission = subG staticOkB VS20G`
  rejects every SNARK proof when the guard is false. The certificate holds for both values
  (`certificateR_guard`, `certificateR_reject`), so the guard affects completeness only. The compiled V
  evaluates it once per process (1.5 s); it is `true`.
- **Soundness error.** The model is ≈ 2^-128.30 (`C_main` level 0's query group); KS adds only the list luck (2^-165.4). Lean
  proves `εFS ≤ 0 + (7·2^-131 + 2^-132) + 2^-139 ≤ 2^-128` (`εFS_kcertSJ`): no doom; luck = the invariant's
  escapes (every group `≤ 7·2^-131`) plus the extractor's list luck (`≤ 2^-132`); hash.
- **Vendored proofs.** `LvmJB*` are longfellow-zk's Johnson-bound proofs (`formal/ligero` @ 1c06629, Google,
  Apache-2.0) in the Flock entry's flat port, renamed only; see `LICENSE-longfellow`.

## The proof system in one list

- **Fields.** `K = GF(2^64)` and `E = K[y]/(y^3+y+1)` (CompPoly `BF64`, `BF64.Ext3`), the same as leanVM.
- **Step statement.** `nodeStmt c_L (leafStmt h n)`.
  - Right child: a witness-sending leaf, checked natively.
  - Left child: the previous signed proof, verified in the circuit.
  - A flag `b = 0` gives step 1's first proof.
- **Chain.** A 2^20-row Keccak tape that commits only each row's 256-bit digest `D[i]`. Row `i`'s input is
  `Pad43(D[i−1])` (`Pad43(s)` at row 0, zero for rows `≥ n`), never committed. leanVM's GKR (RMFE), one segment
  of depth 24, proves the permutations; a wiring sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ n − 1]`, a
  slot reduction and one ring switch tie its input claim to bit slices of `D`. `V` evaluates the kernel in closed
  form from `n`'s bits.
- **Child verification.**
  - A 2^15-row sponge table: the trace digest, one WOTS walk and the statements.
  - BITS tables.
  - A LoopIR program (affine-address loop tables) that recomputes the child's verifier on its trace.
- **Fixed columns.** A self-fold accumulator: each proof folds its incoming claim with its own fixed
  claims, `V` checks one evaluation, and the parent's circuit checks the child's fold.
- **Memory.** leanVM's `g`-power logup bus, a grand-product GKR and a table sumcheck.
- **Commitments**, both stacked WHIR with 14 bits of grinding per level:
  - `C_main`: 2^24 words, 3 levels at the Johnson radius (folds 6/4/4, 230/115/77 queries, OOD on levels 0–1),
    never decoded;
  - `C_rec`: 2^19 words holding the child's trace and signature; 2 levels at the Johnson radius (115/77 queries,
    OOD after level 0, final 2^9), decoded by the extractor with UD programs on the transcript's advice.
- **Transcript.** A hash chain over the contract oracle. Merkle hashes are oracle queries, and queries are
  lane-aligned and classified by length.
- **Sizes (P20).** `qS = 7,426`, `|π| = 644,576 B`, 2,576 table evaluations; root leaves 384 B (`C_main`, 48 lanes) and 280 B (`C_rec`, 35 lanes).

## Main theorem chain (modules in `lean/`)

| step | statement | module |
|---|---|---|
| certificate | `certificateFin`; guard `certificateR_guard`, `certificateR_reject`; `staticFacts` | `LvmFinCert`, `LvmFinGuard`, `LvmFinStatic` |
| assembly | `openFin`, `certificateR_open`, `sSound_of_openS` | `LvmFinCert`, `LvmSubmissionS` |
| FS compiler | `kstate_of_kcert`, `ks_of_kcert`: `KCert` (leanVM `Cert` + luck) ⇒ `KState` ⇒ `KS` | `LvmCompileKS` |
| IOP | `kcertSJ` = `kcertOfInv` on `psInv` (the invariant through roots, front end `midSpecR_midSA`, openings `openInv`); Johnson WHIR `whirSpecJ`, relativised `stackedPrefixSpecR`/`finSuffixSpecR`, `codeFacts_johnson`, `whirEps_main24J`, `whirEps_rec20Jp`; grinding `escRet_powCheck_le`; tape and `KS` phases `kgSpecS`; wiring `wireChSpec`; Keccak `callerSpec`, `kgSpec`; bus `midBusTableSpecS`; accumulator | `LvmInvCert`, `LvmCertS*`, `LvmWhir*`, `LvmMcaUd`, `LvmMcaJohnson`, `LvmJB*`, `LvmWireSpec`, `LvmWireKernel`, `LvmKeccakCaller*`, `LvmM3Mid*`, `LvmAccSpec*` |
| tables ⇒ relation | `chain_of_tape`, `traceDigest_of_KS`, `loopir_sound`, `qlink_sound`, `qsig_sound`, `qacc_replays`, `tape_spec`, `wire_spec`, `harith_core`/`harith20`, `nodeSound_of` | `LvmTapeRel`, `LvmSpongeTable`, `LvmLoopSound`, `LvmQ*`, `LvmQAcc*`, `LvmQEqKeccakTape`, `LvmQWireSound`, `LvmQAsmHarMain`, `LvmFinHB`, `LvmNodeSound*` |
| verifier | `VS20G_eq`, `VS20F_eq` (compiled = specified); `refines_VSL` (native ⇒ compiled IOP); `Vwith`, `complete` | `LvmVFast2`, `LvmVFast`, `LvmVEqRefines`, `LvmVerifier` |
| extractor | `computesX` (cost at the declared fuel), `EX_node`, `extJ` (`extJ_ext`: the UD decoder chain), `decode_SJ`, `esc_luckJ_le_132`, `decodeRec1_of_ud`, `decodeRec_of_mem` | `LvmXTop`, `LvmXSpec`, `LvmCertSExtJ*`, `LvmCertSLuckJ`, `LvmXDec1*`, `LvmXDecUd` |

Completeness is the witness-sending kind (`P := encode`, error 0). The harness tests the native prover.

## Layout

`lean/` holds 576 flat modules, all prefixed `Lvm` (`Solution`'s import closure holds 545; it still imports pr11-983bdcfa21d6's
chain-table and shift-link modules, `LvmChainTable*`, `LvmShift`, `LvmQLinkArithCH*`, which the certificate no
longer uses):

| group | prefixes |
|---|---|
| fields, DSL, doom rules | `LvmField*`, `LvmDsl*`, `LvmSpec*`, `LvmProg`, `LvmVCore`, `LvmVParams` |
| FS compiler | `LvmCompile*`, `LvmLog`, `LvmForest`, `LvmPotential`, `LvmInvCert` |
| polynomials, Keccak GKR, tape | `LvmMl*`, `LvmCp*`, `LvmSumcheck*`, `LvmGrand*`, `LvmKeccak*`, `LvmK*`, `LvmTapeRel`, `LvmWire*`, `LvmChain*`, `LvmSponge*`, `LvmShift` |
| bus, M3, ring switching | `LvmBus*`, `LvmSpine*`, `LvmFront*`, `LvmM3*`, `LvmRing*`, `LvmLayout*` |
| WHIR (UD, Johnson, grinding) | `LvmWhir*`, `LvmRS`, `LvmUd*`, `LvmMcaUd`, `LvmMcaJohnson`, `LvmNovelBasis` |
| vendored Johnson bound (longfellow-zk via Flock, Apache-2.0) | `LvmJB*`; `LvmLJ*` (not in the closure) |
| LoopIR, circuit, program | `LvmLoop*`, `LvmQ*` (`LvmQAsm*` assembles the real `Q`), `LvmQAcc*`, `LvmBits*`, `LvmWots*`, `LvmSig*`, `LvmReplay*` |
| native verifier | `LvmParams`, `LvmSchedule`, `LvmDriver`, `LvmDecide*`, `LvmVerifierS`, `LvmVEq*`, `LvmVF*` |
| extractor | `LvmX*` |
| assembly | `LvmAcc*`, `LvmCertS*`, `LvmNodeSound*`, `LvmSubmission*`, `LvmFin*`, `Solution` |

`prover/` contains:
- `src/lv/`: the vendored leanVM crates, with every edit in `src/lv/PATCHES.md`; `src/lv/keccak_gkr_v4/` is
  #13's re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0), mounted on the v4 tier only;
- `src/chainwalk.rs`, `src/keccak_vl.rs`: the chain walk and relay-echo's (#12) AVX-512VL kernel, generated by
  `tools/gen_chain_vl.py` from its vendored `tools/gen_vlasm.py` (Apache-2.0, `LICENSE`);
- `src/lvm/`: the schedule, tables, links, bus, accumulator, LoopIR witness, recursion witness and stream,
  plus the embedded program blobs `q-p20.blob` and `q-p8.blob`;
- `src/{service,format,proc,alloc}.rs`: from the earlier Flock-class entry;
- `dispatch.s`: the cpuid stub;
- `build-asm.sh` and `tools/`.

## Building

- **Prover.** Run `prover/build-asm.sh --install`. It needs rustc 1.99.0 and builds offline, with no
  dependencies. It emits `prover-v2.s` (portable), `prover-v4.s` (Zen 4: VPCLMULQDQ, GFNI, VBMI) and
  `prover-v4p.s` (AVX-512 + PCLMUL), filtered for GNU as 2.42, with symbols suffixed per variant. The
  runner links them with `gcc -static -O2 -pthread *.s -lm`. The `.s` output is reproducible byte for
  byte.
- **Lean.** Use the harness `evaluate.py cert` on this root (submission guide §5). Only `Solution`'s import
  closure is built.

## Trust notes

- **Measured vs estimated.** Local timings come from a QEMU dev VM on which v4 cannot start. They use the
  dev variant v4p: 2.5–8.7 s per step (`≈ 1.68 + 6.93·n/2^20` s), 5.6 s for step 1, 6.81 GiB
  peak, and `V` ≈ 0.185 s per check. Zen 4 numbers come from the harness; the v4 tier, #13's GKR, the chain
  kernel and the worker choice on SMT cannot be timed on the dev VM.
- **CPU safety.** `prover setup` self-tests each variant (KATs, a batch proof, a full P8 proof) against
  the portable reference's digest, and writes a cap that `dispatch.s` honours. v4 was byte-identical to
  v2 under Intel SDE.
- **No Rust verifier.** The Lean `V_S` is the test oracle. It accepts the shipped prover's P8 and P20
  streams (`b = 0`; `b = 1` over both child flags).

## Credits

- [leanVM](https://github.com/leanEthereum/leanVM): the protocol, the Rust crates and the `formal/` proofs.
- [leanerVM](https://github.com/Verified-zkEVM/leanerVM): the bus lookup lemma, the generator facts and
  reference formalisations.
- relay-slim (#17): Z2, root leaves carrying only their occupied lanes (Apache-2.0), ported onto the Johnson
  `C_rec`, and the C-order link in `build-asm.sh`.
- relay-echo (#12): the AVX-512VL Keccak chain kernel generator (Apache-2.0, `LICENSE`).
- leanvm-gkr-fast (#13): the re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0), our v4
  tier; leanvm-fast-verify (#15): every-round storage, measured faster on Zen 4.
- The earlier Flock-class recursive entry: the extractor framework, field kernels, the UD line lemma,
  the sponge layer, the W/S dispatch, the oracle client and the assembly pipeline.
- [longfellow-zk](https://github.com/google/longfellow-zk) (`formal/ligero`, Apache-2.0), in the Flock entry's
  port: the Johnson list bound and Haböck's strong mutual correlated agreement (`LvmJB*`, `LICENSE-longfellow`).
- The organiser's core library: `WitnessSending`, `KState`/`KS` and the fast Keccak and signature twins.
