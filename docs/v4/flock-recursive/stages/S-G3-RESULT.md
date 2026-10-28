# S-G3 RESULT: `hAcc`

Base HEAD `625cc36`. HEAD moved to `5b2fb93` (S-H2 part 19, `FRX*` only) during the stage. The
final build and checks ran on a snapshot of `5b2fb93`'s modules with S-G3's three modules
symlinked in (`logs/fr-build-SG3/snap.sh`), because the worktree's `FRVIR*`, `FRVerifierImpl*`
and `FRX*` are being edited.

**Status.**
- `lake build FRSoundnessAcc` is green (2,328 jobs; `logs/S-G3/build12.log`). There is no sorry.
- Axioms (`logs/S-G3/axioms.log`, 33 declarations): only `propext`, `Classical.choice` and
  `Quot.sound`. Some use fewer: `runLog_trace`, `mem_fsOf`, `fsItems_getElem` and `padV_L32` use
  `propext` and `Quot.sound`; `mLog_four` and `size_of_snark` use only `propext`.
- Source rule: `python3 -I .contract/scripts/source-rule.py submissions/flock-recursive` reports
  128 files, 0 findings (`logs/S-G3/source-rule.log`).
- Items 1, 2 and 4 are proved. In item 3, the math bridges (log checks ⇒ `AcceptTail`) are proved.
  The register-to-log part is not; it is left as one named hypothesis, **`hFin`** (§5).
- `¬ RejF` is the named hypothesis **`hFront`**, as instructed, because the front's `RejF` is
  not concrete yet.

## 1. What was built (code lines from the core's `scripts/loc.py`)

| File | Total / code / theorems | Content |
|---|---|---|
| `FRSoundnessAccRun.lean` | 274 / 214 / 18 | Items 1–2. `runLog_trace`, `path_of_links`, `mem_fsOf`, `fsItems_getElem`, `msgOk_getD`, `size_extract_of_le`, `fsCheck_absorbQ`/`squeezeQ`/`seedQ`, `fsCheck_fsQ`, `matches_fsQ`, **`runLog_chain`**, `chain_len_468`; the `W` branch: `length_flatMap_le`, `signedWords_length_lt`, **`size_encode_lt`**, **`acc_W`**, `not_acc_bad` |
| `FRSoundnessAccFin.lean` | 234 / 134 / 19 | Item 3. `rSum`, `rVal`, **`FinLog`**; `y_eq_foldAtN`, `p1_of_finLog`, `pf_of_finLog`, `lvl4_of_finLog`, **`acceptTail_of_finLog`**; controls; Part C register-side bridges `extract40_absorbQ`, **`msgAt_fsQ`**, `bytesAt_extract_of_le`, **`readK_fsQ`**, `mLog_four`, **`padV_eq`** |
| `FRSoundnessAcc.lean` | 105 / 69 / 4 | Item 4. `size_of_snark`, **`hAcc_of`**, `hAcc_of_E` (with `X.E`, `X.ext_W`), **`finalLaw_of_run`** |

**Request to the owner of `FR.lean`:** add `import FRSoundnessAcc`. It imports the other two
modules, and also `FRXSpec`.

## 2. The statements

### Item 1: `runLog_chain`

```lean
theorem runLog_chain (impl : OpImpl) (fin : Finals) {k : Kind} {vk c : Digest} {π : Proof}
    {L : Log} (hb : ¬ Bad L) (hπ : π.size = piSize)
    (hrun : (runIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩).runLog L = some true) :
    ∃ tr : Trace, semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true ∧
      (∀ e ∈ tr, e ∈ L) ∧ ∃ j, IsChain L j ∧ entriesOf L (pathOf L j) = fsOf tr items ∧
        (entriesOf L (pathOf L j)).length = 468
```

This is stronger than asked. Besides `IsChain` and the length (`chain_len_468`:
`p3S0 4 < 468` and `pfStart + 14 ≤ 468`), it identifies the chain's entries with the run's
Fiat–Shamir entries, and it returns the trace together with `semIR`'s verdict. The register
bridges need both.

The steps:
- **`runLog_trace`**: an accepted log run is a `runSeq` run on a trace of the log's entries.
- `runSeq_runIR`, then `fsQ_gen`: the 468 FS entries satisfy `es[p].1 = fsQ vk c π p es[p−1].2`.
- **`matches_fsQ`**: these entries `Matches`:
  - a seed first;
  - each later entry's state is the previous answer (`X.stateIn_fsQ`);
  - each passes its item's `fsCheck` (`fsCheck_fsQ`). This uses three existing certificates:
    `fsMsgs_items` (the kinds), `fsMsgs_aligned` (`o + len ≤ piSize`, so the extract has length
    `len`) and `fsMsgs_ctl` (position 0 is `hdr`, 48 bytes).
- **`path_of_links`**: on a log with `¬ Bad`, entries linked state to previous answer, starting
  from an entry with no state, are the forest path of the last one. The proof is by induction,
  using `predIdx = ansIdx (stateIn …)`, `ansIdx_self` (distinct answers) and `predIdx_lt`.

### Item 2: the `W` branch

```lean
theorem acc_W (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    {vk c : Digest} {π : Proof} {L : Log} (hW : FR.kindOf π = .W)
    (hrun : (S.V vk c π).runLog L = some true) :
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w
```

- The proof uses `V_W`/`V_W_sound` (FRVerifier) and `acc_eq`.
- `E_W` needs `|π| < 2^64`. **`size_encode_lt`** derives this from `Rel (accV …) c w`:
  - a leaf encodes to 48 bytes;
  - each accepted child has fewer than `2^32` words (`signedWords_length_lt`), from `accWith`'s
    caps (`|π| ≤ 2^20`, `|tr| ≤ qV = 10240`, queries `≤ 2^20` bytes) and the signature's fixed
    lengths (`fits_of_accWith`).
- `hAcc_of_E` instantiates `hE` with the entry's `X.E` (`X.ext_W`).

### Item 3: the finals on the log (`FinLog`) and `acceptTail_of_finLog`

`FinLog W₀ c₀ L es y` collects what the accepted verifier's checks say. It is written with the
log's reads, and `y i q` stands for the verifier's column folds. One field per check:

| Field | The verifier's check (A.9, `roundsT`) | Used for |
|---|---|---|
| `rnd`, `rndPf` | in-phase K round checks, rounds `l ≥ 1`: `g_l(0)+g_l(1) = g_{l−1}(r_{l−1})` | `Chk2` at `l ≥ 1` (`chk2_succ`, independent of the claim) |
| `start` | `claim0 P1.0 = v*` (the front: `finRS`/`finB′`) | `Chk2 (p1Start 0) … 0` with `lvC 0 = c₀` |
| `cols` | P2.i's openings: a path to the cap entry and `y_q = Σ_r eq(sᵢ, r)·col[r]` | `y_eq_foldAtN` (`foldAt_of_cols`) |
| `link` | `finP i`, `i < 4`: `claim0 P1.(i+1) = claimN P1.i + Σ_q eq(κ_c, q)·y_q` | `Chk2 (p1Start (i+1)) … 0` via `lvC_succ`, `vNext` |
| `pf0` | `finP 4`'s `assertEq (claim0 Pf) (claimN P1.4)` | Pf's round 0 (`pf_round0_agree`) |
| `enc` | `finP 4`'s `encFlag`s: `y_q = Enc₄(final)[p_q]` | `lvl4` (`truthP3_four_of_cols`) |
| `fin` | `finPf`'s `relPf`, at the spec | `AcceptTail.fin` |

```lean
theorem acceptTail_of_finLog {RejF : Log → Log → Prop} {L : Log} {j : ℕ} {y : ℕ → ℕ → K}
    (hb : ¬ Bad L) (hci : IsChain L j) (hlen : (entriesOf L (pathOf L j)).length = 468)
    (hR : ¬ RejF L (entriesOf L (pathOf L j))) (h : FinLog W₀ c₀ L (entriesOf L (pathOf L j)) y) :
    AcceptTail RejF W₀ c₀ L j
```

Part C proves three register-side bridges for later use:
- **`msgAt_fsQ`**, **`readK_fsQ`**: on the run's FS entries, an absorb's log message is π's bytes
  at its `fsMsgs` range. So a `readK` on the log is the verifier's `K.ofBytes (bytesAt π …)`.
- **`padV_eq`**: with Pf's challenge registers holding `pfP`,
  `padV = Π_{mLog₄ ≤ v < 7} (1 − ρ_v)` (characteristic 2; `mLog_four`: 7 for L32, 5 otherwise).

### Item 4: `hAcc` assembled

```lean
theorem hAcc_of (impl : OpImpl) (fin : Finals) (S : Submission) (vk : Digest)
    {RejF : Log → Log → Prop} (hV : S.V = Vwith impl fin) (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    (hFin : ∀ k c π L tr j, ¬ Bad L → π.size = piSize →
      semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true → (∀ e ∈ tr, e ∈ L) →
      IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ∃ y, FinLog W₀ c₀ L (entriesOf L (pathOf L j)) y)
    (hFront : ∀ k c π L tr j, (the same premises) → ¬ RejF L (entriesOf L (pathOf L j))) :
    ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨ ∃ j, AcceptTail RejF W₀ c₀ L j
```

The proof splits on `kindOf π`:
- `W`: `acc_W`;
- `bad`: `not_acc_bad`;
- `snark k`: `size_of_snark`, `V_snark`, `runLog_chain`, then `acceptTail_of_finLog`.

**`finalLaw_of_run`** composes this with `finalLaw_of`. It gives
`FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀)` from `S.V = Vwith impl fin`, `S.qV = qV`,
`S.E = X.E`, `FrontLocal`, `FrontChainStab`, `hFin`, `hFront` and `hExt`.

**What remains for `kstate`** (with `kstate_of_front`): `FrontObl`, `FrontChainStab`, `hFin`,
`hFront`, `hExt`.
- `FrontObl`, `FrontChainStab` and `hExt` are unchanged from S-G2 pass 2, §P2.3.
- `hFin` is the verifier's run semantics on the tail (§5).
- `hFront` is `¬ RejF` (the front, after INT-3).

## 3. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile`), logs in
`logs/S-G3/time-*.log`:

| Module | Wall (incl. ≈ 3.5–4 s import) | Type checking | Tactic execution | Max RSS |
|---|---|---|---|---|
| `FRSoundnessAccRun` | 7.7 s | 334 ms | 485 ms | 2.77 GB |
| `FRSoundnessAccFin` | 7.4 s | 164 ms | 141 ms | 2.77 GB |
| `FRSoundnessAcc` | 6.0 s | 7 ms | 29 ms | 2.75 GB |

- No single declaration takes more than 100 ms (`profile-*.log` are empty).
- One `congr 1` over K sums took 2.65 s; it was replaced by `congrArg`.
- `decide` appears only in these places:
  - `mLog_four`: `cases κ <;> decide`, the same form as `mLog4_le`;
  - `Ico 5 7 = {5, 6}`;
  - `0 < hEll 0`, in a control;
  - `padV_P30_one`: on `Kind`.
- No `decide` runs over a program, a table or the item list. The FS table facts come from the
  existing certificates `fsMsgs_items`, `fsMsgs_aligned` and `fsMsgs_ctl`.

## 4. Controls

| Control | Kind | Shows |
|---|---|---|
| `finLog_rounds_of_acceptTail` | converse | `AcceptTail` gives back `FinLog`'s `rnd`, `rndPf`, `start`, `pf0` and `fin`: these fields ask no more than the tail reads |
| `not_finLog_of_start` | negative | a wrong first claim refutes `FinLog` |
| `not_finLog_nil` | negative | on the empty log no column opens, so `FinLog` fails whenever level 0 has a query (`cols` is not vacuous) |
| `rSum_nil` | value | `rSum = rVal = 0` on the empty chain |
| `padV_L32`, `padV_P30_one` | value / negative | no padding at L32; at P30 the padding is `0` when `ρ₅ = 1` |
| `matches_fsQ`, `runLog_chain` | — | the run's FS entries satisfy the existing `Matches` (whose controls are `matches_seed` and `not_matches_squeeze`) |

**Not built: a positive instance of `FinLog`.** It needs a log carrying Merkle openings at every
level, which means an honest proof's run. Its satisfiability is the completeness side. The
converse control shows that the round and final fields are exactly the tail's.

## 5. Deviations and what is left (`hFin`), in order

1. **`hFin` is a hypothesis.** It is the verifier's run semantics on the tail. Discharging it
   means, in order:
   1. **Finals' flags.** From `semIR … = some true`, `exec_skeleton` gives the phases' registers
      `r = refPhases …` with every phase flag true (`skeleton_ok`). The finals' fold
      (`Finals.ops`, via `exec_field` per field) must give each field's flag true:
      `flag_finPLow`, `flag_finP4` (`relP4`) and `flag_finPf` (`relPf`). No lemma yet composes
      `Finals.ops` over `rest`.
   2. **Outs to values.** The registers that `FinIn.outs = skeleton.2.outs` names must hold
      `refPhase`'s values:
      - `p1Claim0` and `p1ClaimN` of `.rounds`: `initVals`' `c₁ + c₂`, and the last running
        claim;
      - `ysOf` of `.queries i`: `dotKF (eqTab foldR) col_q`, plus `posAllT`'s Merkle flags;
      - `kcOf` of P3's `.coords`: `chF`;
      - `chals` of Pf.

      This is per shape, along `genPhase`. S-0's `refPhase_chain` is the model.
   3. **Values to log.** Use `msgAt_fsQ`/`readK_fsQ` (built here), together with a position lemma
      for the tail's positions. That lemma must give `fsMsgs[p1Start i + 2l]` as P1.i's
      round-`l` range, and likewise for Pf, P2.i and `phStart 47`. It should come from
      `fsMsgs_eq : fsMsgs = msgsFrom phases 0`, not from a new `decide`. The answers come from
      `fsOf`.
   4. **Arithmetic.** `roundKVals`' last value is `peval (g2At …) (rch2 …)`. `elemKAt` is
      `readK`. `(Val.k a).eqv (Val.k b) ↔ a = b`.
   5. **`impl` meets the spec.** This is needed for `dotKF`, `eqTable` (`eqTab` ↔ `eqBits`),
      `tensorW` (`encVal ↔ encAt 4 finalAt`, the `tensorTwin` in `wHatL`) and `rsWeight`.
      The concrete `impl` is S-E8's.
   6. **`relPf` to `fin`:**
      - `wV ↦ wHatL 4`: `lvStepV` against `wHatL`'s step, with `tailRegs ↦ ptL`;
      - `w0V ↦ mleP (nrP 0) W₀ (ptL 0)`: the front's `weight_mle`, `mleN_w0F`;
      - `padV`: done here (`padV_eq`);
      - `finHat ↦ mleN 7 finalAt pfPt`: `fhVal_eq` plus `eqTab` ↔ `mle`'s `eq`;
      - `claimN Pf ↦ clR2 … 7`.
   7. **`start`**: the front's `c₀` is the register `v*` that `finRS`/`finB′` assert equal to
      `claim0 P1.0`. This belongs to the front.
2. **`hFront` (`¬ RejF`) is a hypothesis**, as instructed. The front's `RejF` is not concrete.
3. **`hE` is a hypothesis in `hAcc_of`.** `hAcc_of_E` discharges it for `X.E` with `X.ext_W`.
   This keeps `FRSoundnessAccRun` free of the extractor's modules, which S-H2j is editing.
4. **`runLog_chain` is stronger than asked**: it adds the trace, the verdict, and the equality
   of the chain's entries with `fsOf tr items`. The register bridges need these.

No statement elsewhere was found wrong. No other track's module was edited.

## 6. Open questions

1. Who takes `hFin`'s steps 1–6? They are run semantics (S-0/S-F style) on S-G's log side, and
   step 5 depends on the concrete `impl` (S-E8).
2. The owner of `FR.lean` should add `import FRSoundnessAcc`.
3. The `start` field and `hFront` should go to the front's owner, after INT-3, together with
   `FrontObl`.
