# S-F RESULT: the verifier and S-F's phase-final checks

Branch `v4/flock-recursive`, built on HEAD `b1579e9` and its other-track modules (blueprint revision
3.7 `gen`). `finRS` was then adapted to revision 3.8 (`J_z = 4`, see §4). Not committed.

## 1. What was built

| File | Code lines (`loc.py`) | Content |
|---|---|---|
| `lean/FRVIRFinalsSF.lean` (new) | 740 | S-F's A.9 fields `finRS`, `finE`, `finB'`, with `exec_finRS`, `flag_finE`, `flag_finB'`; the no-ask lemmas; `sfFinals p pf = s0Finals finRS finE finB' p pf` |
| `lean/FRVerifier.lean` (new) | 138 | `qV`, `accWith`, `Vwith impl fin`, `accV`, `acc_eq`, the branch lemmas, `V_W_sound`, `complete`, `runSeq_length`, controls |

Total 878 code lines (`loc.py`). No other module was edited.

### `FRVIRFinalsSF`

- **Proof kit** for straight-line ops that ask nothing:
  - `pureRun_append`, `pr_op`, `pr_app'`, `rdX`, `rdL`;
  - blocks run by induction on their generators, never on a concrete op list: `sqOps`
    (squarings), `phiOps` (the staged map Φ; `run_phiOps` gives `frobMap (stages s fs) a`, the
    `Phi` of `FRRingSwitch`), `elemOps`/`elemsOps` (one claim's 128 slice values; `run_elemsOps`
    gives `Σ_k c_k s_k` and `Σ_k bitBasis k · Φ(s_k)` over `Finset.range`), `prodOps`/`lagAll` (the
    64 skip Lagrange weights), `claimOps`, `rsTail`.
- **`finRS`** (revision 3.8, `J_z = 4`, claims in order Z, Lc, Sh, Lr):
  - `α_j = Σ_i c_{j,i} s_{j,i}`. The low weights `c` are those of `rs_column`:
    - Z: `L_{i mod 64}(λ) · eq(r₀, ⌊i/64⌋)`, from `quirky_claim_split`;
    - Lc: `eq` at the first 7 of L2's challenges;
    - Sh: `eq` at the first 7 position challenges of S2;
    - Lr: `eq` at the first 7 of Lr4's challenges.
  - `v_RS = T₀ + κ(T₁ + κ(T₂ + κ·T₃'))` with `T_j = Σ_i bitBasis i · Φ_{f₀…f₆}(s_{j,i})`. This is
    FRRingSwitch's `rsT` at RS1's stage coefficients.
  - A leaf's fourth claim (Lr) has its slice values asserted zero, and `T₃' = 0`.
  - Exports `[α_Z, α_Lc, α_Sh, α_Lr, v_RS]`; `v_RS` is at index `nRS = 4`.
- **`exec_finRS`**: under `∀ x ∈ rsRefs κ fi, x < r.size`, `pureRun` of `finRS` gives
  `some (L, relRS κ inp)`. Its exports read `rsAlpha κ inp fi r j` (`j < 4`) and `rsV κ inp fi r`.
- **`finE`** (node): the E-end absorb's `â_M, b̂_M, ĉ_M`; asserts `c_{E2} = eq(r_E, r)·(â_M b̂_M + ĉ_M)`;
  exports `v_E = â_M + κ_E b̂_M + κ_E² ĉ_M` and E2's point `r`. **`flag_finE`**: the flag is `relE`,
  and the exports are `vE` and `r`.
- **`finB′`**: `v* = v_RS + κ′ v_E + [node]·κ′²·pubH`, embedded in `K` (`mulKF` by `1`), equals P1.0's
  initial claim. `pubH` is `Σ_k κ′^k pub_k` in this order:
  - M's `one` cell `= 1` (revision 3.6);
  - slot 0's `vk` (lo, hi), then `c₁` (lo, hi);
  - slot 1's `vk` (lo, hi), then `c₂` (lo, hi).

  The halves are `splitDigest`'s. The zero padding cells come after these and add nothing to
  `v*`. **`flag_finB'`**: the flag is `relB`, and the export is `vStar`.
- `noAsk_finRS/E/B'`: each field asks nothing (`items_gen`'s hypothesis).

### `FRVerifier`

- `Vwith impl fin vk c π` branches on `kindOf π`:
  - `snark k` runs `runIR impl (gen fin (.fixed k))`;
  - `bad` returns `false` with no query;
  - `W` runs the library's strict witness-sending decision with the fast twins. A node's children
    are checked by `accWith vk p (fun _ => Vwith …)`, by well-founded recursion on `|π|`. There is
    no size cap (§3.3).
- `accWith`: `Submission.acc` with `qV = 10240` and the fast hashes; `V` is delayed.
- `accV impl fin vk c p := accWith vk p (fun _ => Vwith impl fin vk c p.π)`.
- **`acc_eq`**: `S.V = Vwith impl fin → S.qV = qV → S.acc = accV impl fin`.
- `V_bad`, `V_snark`, `V_W` (the `W` branch with the specification functions).
- **`V_W_sound`**: an accepted `W` proof is `encode w` for some `w` with `decode π = some w` and
  `Rel (accV impl fin vk) c w`.
- **`complete`**: with `S.P = fun _ _ w => .ret (encodeF w)`, `CompleteWithError (Rel (S.acc vk))
  (S.P vk) (S.V vk) 0` for every `vk` (§5.5, through `complete_withError_zero`). Its supporting
  lemmas are `kindOf_encode` (a witness proof's first byte is `0` or `1`), `fits_of_rel` and
  `V_encode`.
- **`runSeq_length`** (with `exec_length`): an accepting SNARK run uses exactly one trace entry
  per ask op of `gen`.

### What `node_sound` (S-E2) needs from S-F

It needs the conclusion **`accV impl fin vk c p = true`**, where

```lean
def accWith (vk : Digest) (p : Signed) (v : Unit → OProg Bool) : Bool :=
  decide (p.π.size ≤ proofCap) && decide (p.tr.length ≤ qV) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ &&
    decide ((v ()).runSeq p.tr = some true)
def accV (impl : OpImpl) (fin : Finals) (vk c : Digest) (p : Signed) : Bool :=
  accWith vk p fun _ => Vwith impl fin vk c p.π
```

`acc_eq` turns this into `S.acc`. For a SNARK child, `V_snark` and `runSeq_runIR` reduce the last
conjunct to `semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true`. `semIR_mux` relates it to
`node_m_sound`'s `gen fin .mux`. For a `W` child, `V_W` applies.

## 2. Build and kernel times

**Measured.** Sequential runs (`lake env lean -DElab.async=false --profile`), one process each,
in the 16 GB scope. Logs: `logs/S-F/profile-*.log`, `logs/S-F/time-*.log`.

| Module | wall | import | elaboration | tactic exec. | simp | type checking (kernel) | peak RSS |
|---|---|---|---|---|---|---|---|
| `FRVIRFinalsSF` | 32.9 s | 3.75 s | 3.01 s | 8.06 s | 7.65 s | 3.07 s | 2.7 GB |
| `FRVerifier` | 8.3 s | 3.59 s | 0.13 s | 0.19 s | 1.06 s | 0.10 s | 2.6 GB |

Axioms: `logs/S-F/axioms.txt` lists the theorems of §1. Every one depends on exactly `propext`,
`Classical.choice` and `Quot.sound`. Source rule: 46 files, 0 findings.

**HEAD's `FRVIRSpec` (S-0) contains two `sorry`s** (lines 818 and 828, build warnings). My
modules import it, so they inherit them through the import, though none of the theorems listed in
§1 uses them.

## 3. Controls

| Control | Shows |
|---|---|
| `ctrl_W_leaf` (+) | The honest proof `encode (.leaf s 1)` of a one-step leaf is accepted with no query, for every `s`, through `V_encode`. |
| `ctrl_bad_size` (−) | Kind byte `N` with a 1-byte proof gives `ret false` with no query (`kindOf = bad`). |
| `ctrl_bad_byte` (−) | First byte `2`, not a kind byte, goes to the `W` branch; the decoder fails and the result is `ret false` with no query (kernel `rfl`). |
| `ctrl_truncated` (−) | A SNARK-kind proof with a trace shorter than `gen`'s ask ops is rejected (`runSeq_length`). |
| `V_W_sound` / `complete` | The `W` branch decides exactly `Rel (accV …)` on canonical encodings. |
| `exec_finRS`, `flag_finE`, `flag_finB'` | The fields' flags and exports are A.9's relations, adapted as in §4. |

The compiled-`V` timing probe was not done. It is optional, and `V` is not yet concrete (open 1).

## 4. Deviations, with reasons

1. **Module.** S-F's fields are in the new `FRVIRFinalsSF`, not in `FRVIRFinals`, so that S-G can
   edit that file at the same time. `sfFinals` assembles them.
2. **`v_RS` follows `FRRingSwitch`, not A.9's text.**
   - A.9 says `v_RS = Σ_j κ^j Σ_u eq(r″,u) s_u`. That form matches neither `rs1_joint` (whose
     switched claim is `rsT = Σ_i bitBasis i · Phi fs (s_i)`) nor `mbp` (`weightEval`, the
     Frobenius weight). I implemented `rsT`.
   - **Cost:** per slice value, Φ is 127 squarings plus 7 stages, i.e. 136 `mulF` with `c·s` and
     `bitBasis·Φ`. That is 4 × 128 × 136 = 69,632 `mulF` and 4 × 128 × 148 = 75,776 ops.
   - Z's Lagrange weights add 64 × 63 = 4,032 `mulF`.
   - About 74 k extra M rows per slot (≈ 148 k per node), so the node's M rows go from 1,089,908
     to ≈ 1.24 M of `2^21` (1.69×). This is my count from the generator, not a measurement.
   - **S-E2's `mRowModel` and the verifier-cost figures (§3.1) need updating.**
3. **`α_j` are computed, not asserted.** A.9's op shape lists "`assertEq` ×5". The claim values are
   *defined* by the column check and bound where they are used: `finZ`, `finLc` (asserts
   `v_β = α_Lc`), `finSh` and `finLr`. This is `rs_column`'s form.
4. **Revision 3.8 adaptation (coordinator message).**
   - `J_z = 4`, with claims Z, Lc, Sh, Lr; RS0's slice values are read at `16·(128 j + i)`.
   - The Z claim's `eq` coordinate is `zLow fi = (coordsR fi "Z1").headD 0`, Z1's first coordinate.
     It must be the coordinate of bit 6 of the packed index under A.1's pinned layout. **S-0 should
     confirm it** (a one-line change).
   - The `zhat` layout is `[α_Z, α_Lc, α_Sh, α_Lr, v_RS]`. HEAD's `finSh` reads `zhat[2], zhat[3]`
     and `finLr` reads `zhat[4]` (3.7 layout); **S-0's 3.8 `finSh`/`finLr` must read `zhat[2]` and
     `zhat[3]`**.
   - The claim count is not symbolic in `exec_finRS`, which is written for 4 claims. Making it a
     list is a refactor of the composition step only, since the blocks are generic.
5. **Leaf's fourth claim.** Its slice values are asserted zero and `T₃` is left out of `v_RS`
   (ratified in 3.8, item 6). **S-G's `finPf`/`mbp` must leave `B₃` out of `W` for leaf kinds as
   well.**
6. **`finE`'s weight point.** A.9 writes `evalM(r_E, ρ)`. The E claims `(A_M f)̂(·)` are at E2's
   sumcheck point `r`, not at E1's `r_E`, so `finE` exports `r` (export 1) for `finPf`.
7. **`finB′`'s public cells.**
   - The order and values are those of §1. S-E2's `PubCells` currently has only the `one` cell; the
     `vk` and `cᵢ` cells are `input` imports.
   - `finPf`'s `eq(cell_k, ρ)` weights, the prover and S-E2 must use the same order and cell
     positions, and the positions are not fixed anywhere yet.
8. **Concrete `OpImpl` not assembled.** `V` is `Vwith impl fin`. The reasons:
   - The interface is changing under 3.8: `lagrangeS` gains an operand and two outputs, and
     `selWeight`/`targetMLE` are removed.
   - Most computable twins (`rowW`, `shiftEq`, `slotW`, `linkW`, `kindFoldWeight`, `shiftTarget`,
     `tensorW`, `mbp`) do not exist yet (S-C/L-pcs).
   - Two signatures cannot express their op: **`mbp r κ pt` has no argument for the claims' points
     or weights**, and **`shiftTarget τ θ` has no argument for a leaf's boundary values `s, h`**.

   Only `walkA/B`, `kindInd` and `evalM fin` (FRVIREval) and `lagrangeS` (FRSkip, old signature)
   exist.

## 5. Open questions

1. Who assembles the concrete `impl`, and when? The two signature gaps in §4.8 (`mbp`,
   `shiftTarget`) are S-0's or S-C's to resolve. After that, `V := Vwith impl (sfFinals finP finPf)`
   is a one-liner in `FRSubmission`.
2. The bridge lemma `lagV l lo = lagrangeWeight (S's nodes) l lo` (char 2: `l − x = l + x`, with
   the constants `wInv`) is not proved. `final` (S-G) needs it to match `quirky_claim_split`.
3. `zLow`'s coordinate, the `zhat` indices and the public cell order (§4.4, §4.7) need agreement
   from S-0, S-E2 and P2.
4. Should the blueprint (A.9, §3.1) adopt the Φ-based `v_RS` and its row cost (§4.2)?

## Revision 3.9 follow-up (coordinator: eqZ, concrete `OpImpl`, timing probe)

### Done: `finRS` on revision 3.9's op set (item 1)

`finRS` now has A.9 revision 3.9's op shape. It was built against HEAD `81f19b2` (S-0's 3.9 `FRVIR`/`FRVIRFinals`).

- **Inner weights.**
  - Z: `getF` of `eqZ λ ρ₁`, with `ρ₁ = pinnedRho 0` as a constant register.
  - Lc, Sh, Lr: `getF` of `eqTable` at the claim's low 7 coordinates.
- **Switched claims.** `T_j = Σ_i bitBasis i · phiRS r″ s_{j,i}`, with `r″` packed once (`packF`
  of RS1's coordinates 0–6). Each slice value is 8 ops: `piElem`, the weight, `mulF`, `addF`,
  `phiRS`, `const`, `mulF`, `addF`.
- **What was removed.** The in-IR squaring chain (`sqOps`/`phiOps`) and the in-IR Lagrange
  products (`prodOps`/`lagAll`) are gone. `zLow` is gone; deviation 4's open coordinate question
  is closed by A.2 (bit 6 is `ρ₁`).
- **What was kept.** `xS`, `others`, `wInv` and `lagV`. S-G's `lagV_eq_lagrangeWeight` uses them,
  and they are the natural computable `eqZ`.
- **Size.** About 4,100 ops (4 × 1,025 plus setup and tail), down from about 76 k. Deviation 2's
  M-row cost now depends on how `phiRS` is compiled, which is S-E2's choice.
- **`exec_finRS`, restated.** With `rsRefs κ fi` in range, `finRS` returns `some (L, relRS κ inp)`.
  Its exports are `rsAlpha impl κ inp fi r j` (`j < 4`) and `rsV impl κ inp fi r`, where:
  - `rsW impl κ fi r 0 i = (impl.eqZ λ ρ₁).getD i 0`;
  - `rsTv impl inp fi r j = Σ_k bb k · impl.phiRS (ptF r (rsFsRegs fi)) (sv inp j k)`.

  These now mention `impl`. `OpImpl.Meets` turns them into `Phi` and `lagrangeWeight`.
- `nRS = 4`, the export layout, `finE`, `finB′`, `FRVerifier` and every control are unchanged.
  `FRVerifier`, `FRVIRFinalsSG` and `FRNodeCircuit` build against the new module.
- **Measurements** (`logs/S-F/profile-FRVIRFinalsSF-3.9.log`, `time-…-3.9.log`, sequential, 16 GB
  scope): wall 23.4 s, kernel 1.52 s, peak 2.7 GB. Code lines: `FRVIRFinalsSF` 467 (was 740),
  `FRVerifier` 138.
- **Checks.** Axioms (`logs/S-F/axioms-3.9.txt`): the standard three or fewer (`noAsk_finRS`:
  `propext`, `Quot.sound`). Source rule: 64 files, 0 findings.

### Not done: the concrete `OpImpl` (item 2) and the compiled-`V` timing probe (item 3)

I stopped here under TRACK-RULES' pace rule: this agent's context is long. Item 2 is the larger
part of the remaining work, and the following inventory is the plan for whoever takes it.

**Prerequisite: an `OpSpec` record.**
- No `OpSpec` value exists yet. Every spec is stated over `Fin n → R`, in the owners' modules.
- `Meets impl spec` needs, per op, a spec in `OpImpl`'s `Array` signature that is defined from the
  owner's math, plus a computable implementation, plus the equality.
- The spec record is the owners' (S-0-m2's table). A neutral home would be a new module
  `FRVerifierImpl` (L-cert, importing FRVIREval, FRSpartan, FRShift, FRPubTarget, FRRingSwitch and
  FRRSEval) holding the Array adapters, `specC`, `implC` and the per-op `Meets` lemmas.

**Per op: what exists and what is missing.**

| Op | Computable code that exists | Spec, and its owner | `Meets` |
|---|---|---|---|
| `phiRS` | `FRRingSwitch.phiApply` | `Phi` (S-C) | immediate: `phiApply_eq` |
| `eqZ` | `lagV` (here) | `lagrangeWeight · eq(ρ₁, ·)` (FRSkip, S-C) | from S-G's `lagV_eq_lagrangeWeight`; the spec needs defining |
| `rsWeight` | `weightEval` (over lists) | `weight_mle`/`mleEval_weightTable` (S-C) | adapter to K points and `κ` batching; to write |
| `walkA`, `walkB`, `kindInd`, `evalM`, `evalL` | `FRVIREval` | `FRVIREval` (S-E2) | proved: `walkA_eq`, `walkB_eq`, `kindInd_eq`, `evalM_eq`, `evalL_eq` (L's row list still a parameter) |
| `evalMK` | none | S-E2 | missing |
| `lagrangeS` (3.9 signature) | `FRSkip.lagrangeS` (old signature) | FRSkip (S-C) | adapter for `pe` and the two outputs; missing |
| `targetS` | `FRPubTarget.targetS` (over `Fin`) | FRPubTarget | adapter |
| `shiftTarget` (with `bnd`) | `FRShift.shiftTarget` (over `Fin`) | FRShift (S-C) | adapter |
| `shiftEq` | `FRShift.shiftMle` | FRShift (S-C) | adapter |
| `slotW` | `FRShift.slotW` (generic slot map) | FRShift (S-C) | adapter, plus the slot maps (A.6) as data |
| `rowW` | `FRSpartan.rowW` (over `Fin`) | FRSpartan (S-C) | adapter |
| `linkW` | none | FRShift (S-C) | missing |
| `kindFoldWeight` | none | FRRingSwitch (S-C) | missing |
| `tensorW` | `FRRSEval`'s twins, partly | FRRS (L-pcs) | missing |

**Item 3 (timing probe).** It needs `implC`. With stub implementations, a probe would only time the
interpreter and the inline F/K arithmetic of about 150 k ops. It would leave out `walk`, `evalM` and
`rsWeight`, which dominate §3.1, so it would not be `T_V` evidence. I did not run it.
