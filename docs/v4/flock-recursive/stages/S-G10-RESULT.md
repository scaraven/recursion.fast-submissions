# S-G10 RESULT (pass 1): `hStart` discharged; the run-fact infrastructure; a stop point on `hW0` (3.16); handover

- **Base.** HEAD `feca303`, moved to **`9d1f906`** (INT-5) during the pass. Everything below is
  built and checked against `9d1f906`.
- **Build tree.** `logs/fr-build-SG10`: a copy of `fr-build-orch` with its `.lake`; `snap.sh` with
  `MINE="FRSoundnessFrRun FRSoundnessFrRnd"` (HEAD's sources, my two modules symlinked).
- **Records.** Logs in `logs/S-G10/`; journal `S-G10-JOURNAL.md`.
- **Constraints.** Every lean/lake command ran in a capped scope (16G builds, 12G single files)
  under a `timeout`. No sub-agents. Nothing committed. No existing module edited.

## Status

**Done:**
- **Item 1, `hStart`: discharged** (`start_run`), for any `impl` whose `phiRS` meets its spec
  (`implC_meets` gives it). It is stronger than `kstate_front_of`'s `hStart` (it does not use
  `¬ Bad L`, `π.size`, or `tr ⊆ L`), so it instantiates it directly.
- **Infrastructure for items 2–3:** `accept_chain` (the fields' register files kept), the register
  views by name (`coordsR_view`, `oneR_view`, `chalsF_view`, `outsR_lt`, `phaseIx_vals`), the
  log ↔ input readers (`vkL_fsQ`, `stL_fsQ`, `msgAt_abs`, `sliceL_fsQ`), `rsV_eq`.

**Not done:**
- **Item 2, `hW0`: blocked at 3.16** (§4: with the current `W₀L` it is false for N30).
- **Items 3–4** (`hFrontV`, `kstate_front`), and the node's Lc (INT-5's message): §5 is the ordered
  handover.

**Checks:**
- `lake build FRSoundnessFrRnd` green on `9d1f906` (2,389 jobs, no `sorry`;
  `logs/S-G10/build-FrRnd.log`). It builds `FRSoundnessFrK` (S-G9's `kstate_front_of`) at
  `9d1f906` too.
- **Axioms** (`logs/S-G10/axioms.log`, all 36 theorems): only `propext`, `Classical.choice`,
  `Quot.sound` (19 all three, 9 `[propext, Quot.sound]`, 8 `[propext]`).
- **Source rule** (`logs/S-G10/source-rule.log`): 178 files, 0 findings.
- **Name clashes.** Every new name grepped against all `FR*.lean`. `initVals_length` clashed with
  `FRVIRSpec`'s (other namespace): renamed `initValsF_length`.

**Imports for `FR.lean`'s owner.** `import FRSoundnessFrRnd` (it imports `FRSoundnessFrRun` →
`FRSoundnessFrK`).

## 1. What was built (code lines from `scripts/loc.py`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrRun` | 466 / 365 / 30 | **`fields_chain`**, `chain_ext`, **`accept_chain`**; `genPhase_one`, **`one_view`**; `bytesAt_extract_n`, **`msgAt_abs`**, **`vkL_fsQ`**, `phaseOff_stmt`, `phaseOff_rs0`, **`stL_fsQ`**, **`sliceL_fsQ`**; `phaseIx_piop`, **`phaseIx_vals`**; `getD_lt_of`, `skel_pos`, `outsR_lt`, **`coordsR_view`**, **`oneR_view`**; `opsOut_append`, `opsOut_elemsOps`, `opsOut_claimOps`, `opsOut_finRS` (= 4117), **`finRS_ex_lt`**; `K.smulF_one`, `val_eqv_k`, `rest_get`, `rs1_val`, **`rsV_eq`**, **`start_run`** |
| `FRSoundnessFrRnd` | 127 / 102 / 6 | `roundF_spec`, **`roundsT_chalF`**, `refPhase_roundsF`, `initValsF_length`, `genPhase_roundsF`, **`chalsF_view`** |
| **Total** | 593 / 467 / 36 | |

### The statements that matter

```lean
theorem accept_chain (fin : Finals) {tr} (hna : …noAsk…) (h : semIR impl (gen fin (.fixed κ)) inp tr = some true) :
    ∃ y, refPhases impl κ inp phases 0 ctx₀ #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      skeleton.2.next = (#[] ++ y.1.toArray).size ∧
      ∃ L₀, pureRun impl κ inp (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).1 (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
        ∃ Rs : ℕ → Array Val, Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray ∧
          ∀ k (hk : k < fin.rest.length), ∃ L, pureRun impl κ inp ((fin.rest[k]'hk) ⟨outs, zh, exAt … k⟩ (Rs k).size).1
            (Rs k) [] = some (L, true) ∧ Rs (k + 1) = Rs k ++ L.toArray
theorem start_run (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a) (vk : Digest) :
    ∀ k c π L tr y, FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀L L (fsOf tr items))
theorem chalsF_view (h : SkRun impl κ inp tr y) (hn : n < phases.length)
    (hsh : phases[n].shape = .rounds f K deg false real) (hf : f ≤ nFields) (hn0 : 0 < n)
    (hfi : fi.outs = skeleton.2.outs) (hix : phaseIx name = n) (hR : ExtA (#[] ++ y.1.toArray) R) (hj : j < K) :
    (chals fi name K).getD j 0 < (#[] ++ y.1.toArray).size ∧
      rd R ((chals fi name K).getD j 0) = .f (rch (phStart n) (fsOf tr items) j)
```
`coordsR_view`/`oneR_view` are the same shape for `.coords` (`fAt es (phStart n + p/2) (p%2)`) and
`.one` (`fAt es (phStart n) 0`) phases.

### Why `accept_chain` (a finding about `accept_fields`)

`accept_fields`' rest part gives each field only `ExtA R₀ Rk`. The fields read registers outside
the skeleton: `finB′`, `finZ`, `finLc`, `finSh`, `finE` read `zhat` (finRS's exports, in `L₀`), and
`finE` reads `lrEx` (finLr's exports). With only `ExtA R₀ Rk` those reads have no known value, so
none of `relB` (iii), `relZ`'s c-claim, `relLc` (iii), `relSh`'s second check, `relE` (iii)–(v) can be
turned into a log fact. `accept_chain` keeps the files (`Rs (k+1) = Rs k ++ L_k`, `finRS` from `R₀`
itself). It is a new theorem in my module; `accept_fields` is untouched.

### `hStart`'s proof

`relB` on `Rs 5` (`finB′`, `rest_get`) gives P1.0's claim register `= .k (K.smulF v* 1)`
(`val_eqv_k`), and that register is a skeleton register, so it is the same in `R₀`. Then
`v* = vStarL k es`: `v_RS` is `exec_finRS`'s export on `R₀` (the run is deterministic, so `L₁ = L₀`;
the export is below `R₀.size + 4117`, `finRS_ex_lt`), and `rsV_eq` turns it into `vRSL`
(`phiRS` spec, RS1's coordinates `rs1_val`, RS0's slices `sliceL_fsQ`). `κ′` is B′'s register
(`oneR_view`). `pubH` is `pubHL` (`vkL_fsQ`, `stL_fsQ`). `K.smulF v 1 = ι v`.

## 2. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`; `logs/S-G10/time-<module>.log` / `.rss`):

| Module | Wall (import ≈ 4–5 s) | Type checking ≥ 100 ms | Max RSS |
|---|---|---|---|
| `FRSoundnessFrRun` | 10.7 s | 0.16 s + 0.37 s | 2.94 GB |
| `FRSoundnessFrRnd` | 8.1 s | none | 2.91 GB |

`decide` uses: `phaseIx_vals` (17 `findIdx` over `piopPhases`' 26 names), `phaseOff_stmt`,
`phaseOff_rs0` (byte counts of the phase rows before 1 and 23, as S-G4's `phaseOff_47`),
`absOff_eq`'s `f ≤ nFields`, `phStart 1 = 1`. None runs over a program, a table or the item list.

## 3. Controls

No new definition was introduced (only theorems), so no new control is owed. `start_run`,
`chalsF_view`, `coordsR_view`, `oneR_view` are positive facts about accepted runs; their
negative counterparts would need an accepted run (completeness, S-I), as `AccFront`'s does.

## 4. Stop point: `hW0` is false for N30 at 3.16 with the current `W₀L`

- **The verifier (`9d1f906`).** `w0V` (`FRVIRFinalsSG:1399`) =
  `rsWeight r″ (rsPtsV) κ (if node then β_{L3β} else 1) P₀ + [node] cells`, and
  `rsWeightS`'s claim index 1 (RS claim 2, Lc) is `Σ_k c_k(r″)·kwSL(β^{2^k}, p₁^{2^k}, P₀)`, the
  kind-weighted extension (`rsWeight_kind_eq`).
- **The front.** `wHatL W₀L L es 0 = mle(ι ∘ w0F (wrsL κ es) cells κ′)(P₀)`, and `wrsL`'s claim-2
  term is `Φ_{r″}(eq(p₁, cube y))` with no kind factor (`FRSoundnessFrW0.wrsL`; the same in
  `FRSoundnessFrRS.gL`, so in `trueL κ L es 1`).
- For a node the two differ whenever `β ≠ 1`: INT-5's `kwS_hashA_ne_plain` is a block where they
  differ. So `hW0` as `kstate_front_of` states it (with `W₀L` fixed) cannot be proved for N30.
  For L32/P30 `β = 1` and `kwS_one` makes them agree.
- **The fix (a definition change in S-G5's `FRSoundnessFrW0`/`FRSoundnessFrRS`, not done here).**
  - Claim 2's weight on a node becomes `gL κ es 1 u = eq(p₁, cube u)·kindFac Ind β (hiIdx u)`,
    with `β = fAt es 98 0` (L3β), `Ind := selOf (ivsQ …)` (0/1, the hypothesis of
    `rsWeight_kind_eq`). `wrsL` takes the factor as well, through `gL` (`wrsL_eq`).
  - The leaf stays as it is (factor `1`, `kwS_one`).
  - What follows: `W₀L`'s node part matches `w0V`. `trueL κ L es 1` on a node becomes
    `⟨W_β, z⟩ = Σ_i β^i v_i`'s truth (`lin_beta_claim`), so **the node's `oLc` binding is the
    leaf's, `v = vBetaL es`**, and `NodeLF.leaf` extends to all kinds.
  - Proofs to repair: `wrsL_eq`, `fipL_eq` (FrRS); `trueL_one` (FrZM: its statement holds only
    for a leaf after the change); `pendLc_pendBad`, `zfL_leaf`.
  - `ExtIface` and `kstate_front_of` keep their text. Their meaning moves with `W₀L`.
- **The orchestrator's call.** Who changes `gL`/`wrsL`: S-G (front modules) or INT? I did not
  change them: the change touches S-G5/S-G8 statements (`trueL_one`) and the RS1 doom accounting.

## 5. Handover: what is left, in order

1. **`gL`/`wrsL` with the kind factor (§4).** Do this first. `hW0` and the node's claim 2 both
   depend on it.
2. **The node's L (INT-5's message: fold it into the discharge).** Once item 1 is in:
   - Instantiate `NodeLF` for the node: L3 at 97 and L3β at 98, the leaf's units in FRSoundnessFrL
     (`l3_habs`, `l3b_single`, `RejLc2`, `L3Bad`, `PendLc`) extended to a node. The node's `RejLc2`
     is `finLc` (ii) at 3.16: `c_Lc = walk(maskRows [0, v₀…v₆, 0]) + (1+α)·v_free·Σ_s L_s(λ)
     eq(r_k[0..5], s)·eq(r′_hi, r_k[6..13])`. Its truth is `lin_final_kinds` + `linM_free_mle`.
   - `pendLc_pendBad` for the node at claim 2, with `oLc κ es v := v = vBetaL es` for all kinds.
   - Then `NodeL` is no longer a hypothesis. `kstate_front` keeps only `ExtIface`, `hfit`, `hE` and
     the `implC` facts.
3. **`hW0`** (`kstate_front_of`'s form), after item 1:
   - `implC_meets` for `rsWeight` needs `r″.size = 7` (`ptF` of 7) and `23 ≤ P₀.size`
     (`p0Regs`: `m − 7` ≥ 23).
   - **Points.** `rsPtsV κ fi r' = (rsPtsL κ es).map (ι ·)`, through `pfPts`/`rsPtIx`. For Z1's
     coordinates use `coordsR_view` (`phaseIx "Z1" = 3`). For L2/Z3/S2/E4's challenges use
     `chalsF_view` (`5, 8, 12, 21`; `rch 15/69/114/265`). `zSrc`'s `ρ₂…ρ₇` are `.c` constants.
     `β`: `oneR_view` at 10 (`fAt es 98 0`).
   - `p0V κ fi r' = ptL es 0` from `p1_facts` (`s₀`) and `tail_vals` (k = 1).
   - **Algebra.** Lift `Phi`/`phiTable` through `ι : F → K` (`frobMap`/`stages` commute with ring
     homs). Then use `weight_mle` (claims ≠ 2) or `rsWeight_kind_eq` (claim 2), `eqPts_eq`, and
     `mleN_w0F` (cells: `cellsVal_eq`, `eqCellK_eq`, `K.smulF a x = ι a · x`, `pfCells_eq`).
4. **`hFrontV`**, check by check, each from `accept_chain`'s file `Rs k` (rest index: Z 0, Lc 1,
   Sh 2, Lr 3, E 4, B′ 5). Each step uses the flag lemma (`flag_finZ`, …), `pureRun_det`, then the
   views.
   - **Missing view:** an F rounds phase's `claim0`/`claimN` registers on the log. These are the
     init claim (`.zero`, `.free`'s `c₁ + c₂`, `.uni`'s Z2 value) and the last round's
     `g2`/`round3V` value. Prove an `roundsT` analogue of `roundsT_vals`' `rVal`, and identify it
     with the front's `clR`/`clR2` (FRSoundnessRows, StepE).
   - `RejZ`: `relZ_iff` (needs Z2's `uni` outs: a `.uni` view, `uniVals`).
   - `RejL2`/`RejLc2`: `relLc` at 3.16.
   - `RejS2`: `relSh` (`implC_meets` for `shiftTarget`/`shiftMask`/`slotW`/`linkWAll`/`shiftEq`;
     `c0S`, `wSumL` were written in these ops' terms).
   - `RejEnd`: `relLr`, `relE` (ii).
   - `RejInE`: E4's in-phase round checks (the rounds' flags).
   - `RejE4`: `relE` (iv), with `evalM`/`evalL` at spec, `lrEx` from `Rs 3`'s output.
   - `RejRS (okF oLc)`:
     - claim 0: `relZ`'s c-claim, with `exec_finRS`'s `rsAlpha 0` = `alphaL … 0`;
     - claim 1: `relLc` (iii);
     - claim 2: `relSh`'s second check;
     - claim 3: `relE` (v).
     - In each case `rsAlpha j = alphaL κ es j` needs `eqZ` at spec (`eqZS`) and the `eqTab`
       points from `chalsF_view`.
5. **`kstate_front`**: `kstate_front_of` with `start_run implC… (phiRS from implC_meets)`, item 3
   and item 4. Then rerun the axioms and the source rule.

## 6. Open questions

1. §4: who redefines `gL`/`wrsL` for 3.16's kind factor, and is the node's `oLc := v = vBetaL es`
   (as for a leaf) the intended binding? It is what `lin_beta_claim` gives.
2. `accept_chain` duplicates `accept_fields`' proof with the files kept. Should it replace
   `accept_fields`? Its statement only adds information.
