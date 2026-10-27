# S-0 (interfaces): adversarial review

Reviewed: `stages/S-0-RESULT.md`; `FRTranscriptDefs` (352 code lines), `FRFormat` (123), `FRVIR`
(406), `FRVIRSpec` (683), committed in `40b2f81`; the dumps `logs/S-0/dump/`. Spec: BLUEPRINT
revision 3.4, §1–§3, §7, §9, Appendix A. Checklists: adversarial-review, lean4:review.

## Evidence

| Check | Result |
|---|---|
| Build of the four modules in a fresh tree (`logs/S-0-review/`, `timeout 1500`) | green, 1 min 51 s; sources unchanged (`sources.sha256`); one `sorry` (`exec_genPhase`, declared); about 23 warnings (deprecated `if_pos`/`if_neg`, unused simp arguments) |
| `items.json` against A.4 | per phase: seed 1, stmt 1, cap₀ 1, Z1 10, Z2 1+1, Z3 26×2, Zend 1, L1 1, L2 14×2, L3 1+1, S1 15, S2 28×2, Lr1 8, Lr2 15×2, Lr3 1, Lr4 15×2, RS0 1, RS1 4, E1 11, E2 21×2, E3 1, B′ 1. Ligerito per level: `ℓᵢ`×2, C 1, P2 25/13/10/8/6, Q `tᵢ` columns and 11/10/8/6/5 nodes each, P3 1. Pf 7×2. **8,852 items, 429 FS items, stream 1,435,888 B. All agree with A.3/A.4 except A.4's heading "473 FS items" (stale: 429)** |
| query sizes | `qlen mod 16` = 7 for the seed, 8 for all 8,851 others (dump and `qlen_mod`) |
| `fieldSizes` | equal to A.3's 16 rows; `piSize_eq = 755,568` |
| ops dumps | 61,753 ops for L, P, N and M alike, so the mux shares the list literally. 8,852 asks = items. The histogram has no `walkA`, `mbp`, `evalM`, `tensorW`, `selWeight` or `targetMLE`: **the dumps are of `gen []`, with no phase-final checks** (S-0-M1) |

## What is right

- **One phase table drives everything.** `items`, `fieldSizes`/`piSize`, `reassemble` and `gen`
  all come from `phases`, with `items_gen`/`queries_gen` proved structurally, never by evaluating
  `gen`.
- **`runSeq_runIR` is an equality** with `semIR`. `semIR_mux` holds by definition. A **single op
  list with a mode** removes the per-kind circuit problem at the IR level.
- **Assertions as a flag** keep the query sequence independent of the proof's validity. That is
  right for `qV`, for the node circuit (one replay shape) and for DoS.
- **`exec_phaseZ` is proved end to end**: the 10 squeezes, the univariate round, 26 rounds with
  P30's dummies, and the `â ‖ b̂` absorb. Its reference `refZ` is an independent structured
  reading, not a restatement of the ops. The `exec_app` trick (36.9 s → 0.07 s of kernel time per
  round) is recorded for successors.
- **`stmt`.** `refPhase` checks the tag, `enc64 n` (leaf kinds), the zero bytes and
  `stmtDigest κ m = c`, as revision 3.3's `stmt` layout requires.
- **`kindSel` + `assertOneHot` + `assertEq`** on `hdr`'s first 16 bytes: the kind is pinned by the
  header, bound through the seed.
- **The MerkleEnc laws** S-D needs (`parseNode_nodeQ`, `nodeQ_of_parseNode`, `parseCol_colQ`,
  `carried_nodeQ`, `carried_absorb`) hold, and the full 8-byte tag with the level byte is checked
  (S-D-M1).
- **A.6.** `zeroRows` equals A.6's table, interval for interval. I spot-checked the byte
  arithmetic:
  - `hashA` zero from byte 41 → bit 840;
  - `w43`: `i`, `s` at bytes 9–10 → 584…599; zero from byte 43 → 856;
  - `streamEnd41`: 4,265 = 66·64 + 41.

## Majors

### S-0-M1. `V` is not yet defined: the phase-final checks are an unowned parameter, and nothing makes their completeness checkable (owner: orchestrator/S-F, with S-C, L-pcs)

**The design is sound.** Moving the finals into `fin : Finals` (deviation 4) does not lose
soundness silently: `KState.final` must be proved for `gen fin`, so a missing check surfaces as an
unprovable `final`.

**But the delivered `V` (`gen []`, the dumps) checks no phase's final relation.** It has round
consistency, Merkle paths, caps, `stmt` and kind, but not:
- Z's `ŵ(â b̂ + ẑ) + Ŵ_E` (`finZ` exists but is not plugged in);
- Lc's walk and `v_kind`;
- Sh's target and `slotW`;
- Lr's and E's matrix evaluations;
- RS's `ẑ` claims;
- B′, Ligerito's consistency and `Enc₄` checks, and Pf.

Deviation 5 also makes the initial claims of every degree-2 and K phase **free**: L2, S2, Lr4, E2
(stated as zero, check), P1.i and Pf take their first claim from the prover's message. Each must
be bound by a final check, or the sumcheck proves nothing.

**What depends on the full program now:**
- S-E2's `compile (gen fin)`;
- the native prover's `acc.rs` and its KAT against the dump;
- S-F's `V`;
- the M-row count of `nodeLayout`: the finals' ops (walks, `evalM`, `mbp`) are a large share of
  the replay rows, and the current dumps contain none of them.

`Finals := Array (List Reg) → ℕ → List Op` is untyped, so a missing phase is not even a type error.

**Fix.**
- Make `Finals` a structure with one field per phase (`finZ`, `finLc`, `finSh`, `finLr`, `finRS`,
  `finE`, `finB′`, `finP i`, `finPf`). Each field takes that phase's output registers and comes
  with its semantic lemma (`exec_finX` against a `refFinX`).
- Name a stage that delivers all of them before S-E2's `nodeLayout` decide and P2's dump KAT (S-F,
  or an "S-0b"). List the free initial claims each field must bind (above).
- Re-dump `ops-*.txt` with the full `fin` for the prover's KAT.

### S-0-M2. A.6's WOTS, key-leaf and path blocks have their variable data at offsets that "element equalities" cannot wire (owner: blueprint §4.2/A.6, S-E2)

**A.6's parenthesis**: "`h_in` … wired … by element equalities (`hashStmt`, key leaf, path);
`w43`'s `x` and `j`, … variable bytes … are inputs". Revision 3.3 fixed `hashStmt` by laying out
`stmt` as the hash message. But the WOTS messages are fixed by the contract
(`Contract/Signature.lean`), and their variable fields are not 16-byte aligned in the message
slots (bits 512…1023):
- `w43` (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x`): `j` at bytes 1–8, `x` at bytes 11–42 (bits 600…855);
- key leaf (`tagWotsLeaf ‖ enc64 j ‖ end₀ ‖ …`): the ends at bytes `9 + 32k`;
- path (`tagSigNode ‖ l ‖ r`): `l` at bytes 1–32, `r` at 33–64 across two blocks.

**Why the wiring fails:**
- **`x_s` cannot be read from the previous step by element rows.** The `x_s` of step `s + 1` is the
  previous block's `h_out` (elements 2–3, aligned) or the signature's `ots_i` (an L element). A
  byte-shifted 256-bit window is GF(2)-linear in neighbouring elements but not F-linear (the
  BP-E-M1 / S-E1-M1 problem).
- **Bit decomposition is too large for L.** Decomposing the affected message elements into L
  bit-elements costs about 3 × 128 bits × 498 blocks per slot, about 2^17.5 per node, far over
  `N_L = 2^15`.
- **Selectors.** WOTS chains are also selector-dependent
  (`x_{s+1} = [d_i ≤ s] ? F(x_s) : x_s`), so the input of a step is a mux of two aligned sources
  before it is placed at the unaligned offset.

**Fix** (design, before S-E2).
- Route these links through the shift argument, whose collapse already takes an arbitrary slot map
  (S-C-m1's direct `slotW` sum). Lay out each WOTS chain's three steps, the key leaf's 67 blocks and
  each path's 2 blocks consecutively. Add the needed slot maps (`h_out → x` at bits 600…855,
  `end_k → 520 + 256k + 72…`, `l/r` at 520…) as further batched chains in the Sh phase.
- Resolve the selector mux on the aligned side, in M rows, before the shift link.
- Check that S2's error row and `qV` are unchanged (one batched sumcheck), and state it in §4.2
  and A.6.

### S-0-M3. `exec_genPhase` is provable but not enough to compose phases into the `final` walk (owner: S-0)

- **What it states.** The statement equates a phase's ops with `refPhase` and returns the appended
  values.
- **What it omits.** It says nothing about the **context** `(genPhase n p c).2`: the next phase's
  `st` register, `uni`, `posAns`, `foldR`, and the `outs` indices.
- **Why that blocks composition.** Without
  `genPhase_ctx : (genPhase n p c).2.st = r.size + iSt ∧ rd (r ++ x.1) that = the phase's last
  answer` (and likewise for `outs`), the next phase's hypotheses (`hb`, `hst`, `hd`) cannot be
  discharged. So no `exec_skeleton` (the whole skeleton against a `refSkeleton`) can be derived,
  and S-G's `final` needs exactly that composed form. `exec_phaseZ` has the same gap.
- **Fix.** Add the context half to the statement (or a companion lemma per shape) and
  `exec_skeleton` by induction over `phases`. This is also the right place to state
  `ok = true → every phase's flag`.

## Minors

- **S-0-m1 (`windows` for the seed).** `windows` takes query offsets `8 + 16k`, which is
  stream-aligned only for 8-byte tags. The seed (7-byte tag, starting at stream offset 9) has its
  stream-aligned windows at query offsets `7 + 16k`, so `inPlay` omits `vk`, `c` and `hdr`'s
  windows. The docstring's "16-byte-aligned windows of the hashed stream" is false for the seed.
  Either define `windows` by stream offset, or record why `Bad` does not need the seed's windows.
  The seed's `carried` (`[vk, c]` at 7 and 39) is outside `windows` for the same reason.
- **S-0-m2 (`OpSpec := OpImpl`, `Meets` = function equality).**
  - Equality of total functions on `Array`s forces implementations to agree with the
    specification on malformed lengths too.
  - Nothing yet gives `OpSpec` mathematical content: no concrete spec, no lemmas.
  - State `Meets` per op under length preconditions (`rw.size = 2^14 → impl.walkA rw cw = Σ …`),
    or require each spec to be defined totally. Assign the concrete `spec` and its lemmas
    (S-C: `lagrangeS`, `tensorW`, `mbp`, `shiftTarget`, `slotW`, `kindFoldWeight`; S-E1/2:
    `walkA/B`, `evalM/L`, `kindInd`; `FRPubTarget`: `selWeight`, `targetMLE`).
- **S-0-m3 (stale blueprint text).** BLUEPRINT's header still says "revision 3.2, frozen". A.4's
  heading says "473 FS items" (429). A.2's final-message sentence is stale (deviation 11).
- **S-0-m4 (`parseCol` width).** `parseCol` checks the tag only, while `MerkleEnc`'s docstring says
  "and check its width". This is harmless (a wrong-width first preimage is a collision, charged),
  but make the docstring or the code agree.
- **S-0-m5 (`kindOf`).** The `W` branch is chosen by the first **byte** 0/1, and the empty proof is
  `W`. This is harmless, since the `W` branch decides `Rel` and misparses reject, but it differs
  from §1.1's "tag word" and should be stated.
- **S-0-m6 (serial path, deviation 14).** `FRTranscriptDefs` imports `FRRS` and `FRMLE` only for
  `eqBits_eq_eq`, which puts `FRRS` (388 lines) on the serial path ahead of every S-0 module. Move
  `eqBits_eq_eq` to `FRRS` or to `FRSoundnessLigerito`, its consumer.
- **S-0-m7 (budget).** I agree with judging `FRVIRSpec` per shape. Z took 373 lines. The remaining
  shapes are about 540 (RESULT estimate), plus S-0-M3's context lemmas and `exec_skeleton` (about
  100–150), so about 1,400–1,550 against 1,500. That is tight, so keep the FR-R10 check after the
  queries shape. The finals' semantic lemmas (S-0-M1) are not in any budget yet; add them to §7
  under their owners.
- **S-0-m8.** About 23 warnings (deprecated lemma names, unused simp arguments, one `<;>`); clean
  them in golf.

## Verdict

**Not yet sufficient to build on; the foundations are right.**
- **Sound and kernel-checked:** the phase table, `items`/`piSize`/`parse_serialise`/`qlen_mod`
  (all agreeing with A.3/A.4 and the dumps), `runSeq_runIR`, `queries_gen`, the mux-by-mode, phase
  Z's semantics and the MerkleEnc laws.
- **Before S-E2, P's dump KAT and S-G build on S-0:**
  - the full `V` must exist, as a typed `Finals` with an owner and with the free initial claims
    bound (M1);
  - the WOTS/key-leaf/path wiring must be redesigned for the contract's unaligned offsets (M2,
    blueprint);
  - `exec_genPhase` needs its context half so the phases compose into `final`'s walk (M3).
