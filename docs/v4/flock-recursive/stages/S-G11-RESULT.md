# S-G11 RESULT (pass 1): the 3.16 kind factor, the node's L, `hW0` discharged; handover

- **Base.** HEAD `aa805c4`, which moved to **`549797e`** (S-N1, rulings O0 and O1) during item 1. Every
  result below was built and checked against `549797e`.
- **Build tree.** `logs/fr-build-SG11` is a copy of `fr-build-orch` with its `.lake`. `snap.sh` takes
  HEAD's sources and symlinks `MINE` = every `FRSoundnessFr*`. Logs are in `logs/S-G11/`. The
  journal is `S-G11-JOURNAL.md`.
- **Constraints.**
  - Every lean/lake command ran in a capped scope (16G for builds, 12G for single files) under a
    `timeout`.
  - No sub-agents. Nothing committed.
  - No `FRVIR*`, `FRVerifierImpl*`, `FRKindWeight`, `FRX*`, `FRNode*`, L-circ, `BLUEPRINT.md` or
    `FR.lean` file was edited.

## Status

**Done:**
- **Item 1.** `gL`/`wrsL` carry the kind factor. The dependent proofs are repaired. RS1's row is
  unchanged.
- **Item 2.** The node's L: **`nodeLF : NodeLF oLcV RejLcN L3BadN PendLcN`**, with the binding
  `oLcV κ es v := v = vBetaL es` for every kind. `NodeL` now needs only its accepted-run field
  `front`, which is `AccFront … RejLcN` and belongs to item 4.
- **Item 3. `hW0` is discharged: `w0V_run`**, in `kstate_front_of(R)`'s exact `hW0` form, for any
  `impl` whose `rsWeight` meets `rsWeightS`. `implC_meets` supplies that.

**Not done:**
- **Item 4 (`hFrontV`, plus the node's `NodeL.front`).** §7 is the ordered handover.
- **Item 5 (`kstate_front`).** Your second message says not to do the final composition. A
  composition through `kstate_front_ofR` was drafted and built green (`build b12.log`, axioms
  clean), then removed from the entry. The draft is kept at `logs/S-G11/FRSoundnessFrKS.lean.draft`
  (§7 item 2).
- **Item 6.** Done for this pass's theorems (below).

**Checks:**
- Builds:
  - `lake build FR` is green on `549797e` with my modules: 2,405 jobs (`build-FR.log`).
  - `FRSoundnessFrW0V` is green: 2,391 jobs (`b11.log`). It builds `FRSoundnessFrLN`.
  - No `sorry`.
- **Axioms** (`axioms.log`, 76 names, including the drafted `kstate_front_W`): only `propext`,
  `Classical.choice` and `Quot.sound`. 69 use all three, 2 `[propext, Quot.sound]`, 5 `[propext]`.
- **Source rule** (`source-rule.log`): 184 files, 0 findings.
- **Name clashes.** Every new declaration was grepped against all `FR*.lean`, untracked files
  included. Each has exactly one declaration. (`nodeBK_ne_chain` clashed with `FRSoundnessFrZM`'s;
  I reuse that one.)

**Imports for `FR.lean`'s owner.** Add `import FRSoundnessFrW0V`. It imports `FRSoundnessFrLN` and
`FRSoundnessFrRnd`.

## 1. What was built (code lines from `loc.py`, `logs/S-G11/loc.log`)

| Module | total / code / thm | Change |
|---|---|---|
| `FRSoundnessFrW0` | 267 / 145 / 20 | `import FRKindWeight`. **`indKW`**, **`kfT`**, `kfT_congr`. **`wrsL`** (claim index 1 × `kfT`). `wrsL_congr` repaired. |
| `FRSoundnessFrRS` | 163 / 110 / 12 | **`gL`** (claim index 1 × `kfT`). `gL_congr` repaired. |
| `FRSoundnessFrZM` | 590 / 452 / 53 | **`trueL_one`** restated (the `kfT` factor). `zfL_leaf` repaired. |
| `FRSoundnessFrPend`, `FrBind`, `FrS` | 82 / 99 / 522 code | Proof repairs in `trueL_three`, `trueL_zero`, `trueL_two`: `if_neg`, `mul_one`. |
| **`FRSoundnessFrLN`** (new) | 354 / 264 / 27 | The node's L3/L3β (§2) |
| **`FRSoundnessFrW0V`** (new) | 456 / 374 / 38 | `hW0` (§3) |

### Statement and definition changes (all from 3.16, as ruled)

- **`gL κ es j u`**: claim index 1 (RS claim 2) is now
  `eqPts p₁ (bitsL …) * kfT κ es (u / 2^7)`. The other claims are unchanged.
  - `kfT κ es t` on a node is `kindFac indKW (fAt es 98 0) ⟨t % 2^16⟩`.
  - `indKW i t` is `selOf (KW.ivsQ 16 (KW.nodeKinds.getD i .free)) t`, the ruling's
    `Ind := selOf (ivsQ …)`.
  - On a leaf `kfT` is `1`.
- **`wrsL`**: the same factor on claim index 1. As a result `W₀L` (text unchanged) matches `w0V`'s
  node part.
- **`trueL_one`**: the summand `eqAtR rk j * eqAtR rb t * zW …` becomes
  `eqAtR rk j * eqAtR rb t * kfT (kindOf es) es t * zW …`. It is stated for every kind; a leaf
  takes `kfT = 1`.
- **Unchanged in text:**
  - `wrsL_eq`, `fipL_eq`, `zfL_leaf`, `pendLc_pendBad`, `hfin_RS1` (still `c := 10`, §5.2's
    `10/2^128`: the RS1 proof is generic in `gL`);
  - `frontLocal_W0`, `trueL_zero`, `trueL_two`, `trueL_three`;
  - `kstate_front_of`, `finalLaw_of`, `hAcc_of_fin`, `kstate_of_front`, `ligerito_final`,
    `ExtIface`, `NodeLF`, `NodeL`, `DF`, `RejF`.
- **`accept_chain` does not replace `accept_fields`.** Nothing needed it.

## 2. The node's L (`FRSoundnessFrLN`)

```lean
theorem indKW_eq (i : Fin 8) {t : ℕ} (ht : t < 2 ^ 16) :
    indKW i ⟨t, ht⟩ = if KW.nodeKinds.getD i .free = nodeBK t then 1 else 0
theorem trueL_node {L es : Log} (hn : (kindOf es).isNode = true) :
    trueL (kindOf es) L es 1 = ∑ i : Fin 8, fAt es 98 0 ^ i.val * tN L es i   -- tN i = zfL zlmFR L es i.succ
def RejLcN (L es) := 98 ≤ es.length ∧ PLc true L es     -- clR2 … 14 ≠ Σ_j vM_j · M̃_j(r_k), node
def L3BadN (L es) := 98 ≤ es.length ∧ isNode ∧ ∃ j, vM (kindOf es) es j ≠ zfL zlmFR L es j
def PendLcN (L es) := 99 ≤ es.length ∧ isNode ∧ vBetaL es ≠ ∑ i : Fin 8, fAt es 98 0 ^ i.val * tN L es i
def oLcV (_ : Kind) (es : Log) (v : F) : Prop := v = vBetaL es
theorem nodeLF (hp : fsItems[97]? ≠ some .squeeze) : NodeLF oLcV RejLcN L3BadN PendLcN
```

- **How `indKW_eq` is proved.** The proof works over ℤ:
  - `part_one` gives `Σ_i sel_i(t) = 1`;
  - every `sel_i(t) ≥ 0`;
  - the block's own class has `sel ≥ 1`, by `ind_nodeBK`, or for `free` because `t ≥ wmBase`;
  - so it is the indicator. No `decide` runs over the layout.
- **`trueL_node`** is `trueL_one` with the factor expanded into `zlmFR`'s node indicators, which is
  `lin_beta_claim`'s `W_β`.
- **The units are the leaf's units, stated for a node:**
  - `l3N_habs` (from `lin_final_kinds`);
  - `l3bN_single`, which counts `7·2^128 ≤ 8·2^128` by `batch_count`; kind 0 is `0` on a node by
    `zlmFR_indKinds`;
  - the reads lemmas;
  - `rejLcN_ok` (`rejOK_at` at 97).
- **`RejLcN` keeps `RejLc2`'s form `Σ_j v′_j M̃_j(r_k)`** with `zlmFR`, whose `free` kind is the
  identity. 3.16's split into walk plus `free` term is on the verifier's side. Item 4 matches it
  through `linM_free_mle` (§7).

## 3. `hW0` (`FRSoundnessFrW0V`)

```lean
theorem wHat0_spec (L es : Log) (ρ : List K) (hρ : ρ.length = nrP 0 (kindOf es))
    (hρv : ∀ v < nrP 0 (kindOf es), ρ.getD v 0 = ptL es 0 v) :
    wHatL W₀L L es 0 =
      rsWeightS (rsRL es).toArray ((rsPtsL (kindOf es) es).map fun p => (p.map (algebraMap F K)).toArray)
          (rsKL es) (if (kindOf es).isNode then fAt es 98 0 else 1) ρ.toArray +
        (if (kindOf es).isNode then cellsVal ρ.toArray (kpL es) pfCells (kpL es * kpL es) 0 else 0)
theorem w0V_run {impl : OpImpl}
    (hrs : ∀ r ps k β p, r.size = 7 → 23 ≤ p.size → impl.rsWeight r ps k β p = rsWeightS r ps k β p)
    (vk : Digest) : <hW0's exact form in kstate_front_of / kstate_front_ofR, for impl>
```

**The spec side (no run).**
- `mleN_w0F` splits off the cells. `mleW_spec` handles the RS part, through `mle_zipIdx`, one claim
  at a time (`termW`):
  - **plain claims, `termP`:** `Phi_eq_table` in F pushed through `ι`, then `eq_frob` and
    `eq_mle`;
  - **claim 2 on a node, `termK`:** `kindFac_frob` with the 0/1 indicators (`indK_bit`, from
    `indKW_eq`), then `mle_kind0` (`rsWeight_kind_eq` at `fs = []`), then `kwSL_eq` (`KW.kwS`
    unfolded);
  - **claim 2 on a leaf:** `kwSL_one` (`KW.kwS_one`; `|ρ| ≥ 23`).
- The cells use `cellsVal_eq`, `eqCellK_eq` and `K.smulF_eq_mul`.

**The run side.**
- **The claim points**, `rsPtsV_eq` (`pfPts`/`rsPtIx`):
  - Z1's coordinates: `coordsR_view`;
  - L2, Z3, S2 and E4's challenges: `chalsF_view`, through `chalsW`/`chalsW'`;
  - `ρ₂…ρ₇` and the zeros are `.c` constants;
  - the `take`/`drop` windows are read by `map_window`.
- **The other registers:**
  - `r″` and `κ`: `rs1_val`;
  - `β`: `oneR_view` at 10;
  - `κ′`: `oneR_view` at 25;
  - `P₀`: `p0_vals`, from `p1_facts` at level 0 and `tail_vals` at k = 1.
- **The kind:** `kindOf_fsQ`.

## 4. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `time-<m>.log/.rss`)

| Module | wall (import ≈ 4–5 s) | type checking ≥ 100 ms | max RSS |
|---|---|---|---|
| `FRSoundnessFrW0` | 7.7 s | none | 2.79 GB |
| `FRSoundnessFrRS` | 7.7 s | none | 2.79 GB |
| `FRSoundnessFrZM` | 53.9 s (S-G8: 40.6 s; the `pins_*` `simp`s dominate) | 0.12 s, 2.12 s | 3.13 GB |
| `FRSoundnessFrLN` | 9.6 s | none | 2.85 GB |
| `FRSoundnessFrW0V` | 12.0 s | none | 2.93 GB |

**`decide` uses**, none over a program or a table:
- `nodeKinds_cover`, per `BlockKind`: `∃ i < 8`;
- `nodeKinds_inj` (8 × 8);
- `nodeBK_free`'s branch facts;
- `kfT_node_zero`'s single kind inequality;
- `phStart_10`;
- literal bounds (`23 ≤ |ρ|` per kind, `f ≤ nFields`).

## 5. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `kfT` / `indKW` | `kfT_leaf` (1 on a leaf); `kfT_node_one` (`β = 1` gives 1: the kinds partition) | `kfT_node_zero` (`β = 0`: hashA's block `stmtBase` gets 0, so the weight is not the plain `eq`) |
| `oLcV` | `nodeLF` (it meets `NodeLF`) | `not_oLcV` (it refuses `v_β + 1`) |
| `RejLcN` / `L3BadN` / `PendLcN` | `nodeLF`'s fields | `not_rejLcN_leaf` (no node check on a leaf) |
| claim 2's weight | `kwSL_leaf` (a leaf's is the plain one) | INT-5's `kwS_hashA_ne_plain` (a node's is not) |

## 6. Deviations and findings

1. **`NodeL` is not constructed.** Its `front` field (`AccFront … RejLcN`) is the node's `finLc` (ii)
   on an accepted run. That is an item-4 check (§7).
2. **No bridge exists from the verifier's walk to `zlmFR`.** No lemma relates
   `walkAB`/`walkABS` + `maskRows` + `rowW` (A.8) to `Σ_j v′_j mle(linM (zlmFR.Ak j) (zlmFR.Bk j)
   (rwL es) α)(r_k)`. `RejLc2` (leaf) and `RejLcN` (node) both need it in item 4. It is the main
   piece of missing infrastructure (§7).
3. **O1 seam: the S-G declarations that mention `Layout.nodeRows`.** These carry the E truth over
   the untemplated rows:
   - `FRSoundnessPIOP`: `truthE`, `truthE_iff`;
   - `FRSoundnessFrDF`: `nE`, `D3E`, `DF`, `RejF`, `rejE4_ok`, `stmt_split`;
   - `FRSoundnessFrStab`: `df_ss`, `ss_rejF`;
   - `FRSoundnessFrObl`: `obl_habs`, `obl_single`, `obl_hfin`, `frontObl`;
   - `FRSoundnessFrK`: `kstate_front_of`'s `hfit`;
   - S-N1's `kstate_front_ofR`/`kstate_front_ofE` (`hfit`).

   Nothing in this pass's new modules mentions `nodeRows`.

## 7. Handover: the remaining items, in order

1. **Item 4: the front's checks on an accepted run.** You need `AccFront (implC (finC finPf)
   Layout.lRows κs₀) vk C` for `C := RejLcN` and for each disjunct of `RejF (finC finPf) oLcV
   (fun _ _ => False)`. Start every check from `accept_chain`'s `Rs k` (rest index: Z 0, Lc 1, Sh 2,
   Lr 3, E 4, B′ 5), the flag lemma, `pureRun_det`, and then the views. `start_run` and `w0V_run`
   are the templates: `SkRun` from `accept_chain`/`fsQ_gen`, the kind from `kindOf_fsQ`.

   a. **Missing view: a rounds phase's `claim0`/`claimN`.** Prove that `rd R (claim0 fi name)` and
      `rd R (claimN fi name)` equal the front's `clR`/`clR2` initial and last claims (FRSoundnessRows,
      StepE). This is the `roundsT` analogue of `roundsT_vals`' `rVal`, in `chalsF_view`'s style
      (`refPhase_roundsF`, `genPhase_roundsF`: the out list is `cl :: chals ++ [last]`). Z2's
      `.uni` view (`uniVals`) is in the same group.

   b. **The walk bridge (§6.2).** Show that `walkABS (maskRows w (rowWS λ r′_hi)) (eqTab r_k)`,
      with `w = nodeKindW v` or `v₀ :: 0^8`, is `Σ_{j ≠ free} v′_j·mle(linM (zlmFR.Ak j)
      (zlmFR.Bk j) (rwL es) α)(r_k)`. Then show that the `free` term
      `(1 + α)·lcFree = v_free·mle(linM I I (rwL es) α)(r_k)`, using `linM_free_mle`, `dotAcc_eq`,
      `eqZ` at `eqZS`, and `eqTab`/`eqPoint` at spec. With (a) this gives
      `¬ RejLcN` / `¬ RejLc2` from `relLc` (ii). `RejL2`'s round 0 is `relLc` (i). `oLcV` at
      `alphaL … 1` is `relLc` (iii): `v_β` = `fi.zhat[1]`, `exec_finRS`'s `rsAlpha 1`.

   c. The rest, as S-G10 §5.4 lists them:
      - `RejZ`: `relZ_iff`, Z2's `.uni`;
      - `RejS2`: `relSh`, with `implC_meets` for `shiftTarget`, `shiftMask`, `slotW`, `linkWAll`,
        `shiftEq`;
      - the `RejEnd`s: `relLr`, `relE` (ii);
      - `RejInE`: E4's round flags;
      - `RejE4`: `relE` (iv);
      - `RejRS (okF oLcV)`, claims 0–3: `relZ`'s c-claim, `relLc` (iii), `relSh`'s second check,
        `relE` (v). In each, `rsAlpha j = alphaL κ es j` comes from `eqZS` and the `eqTab` points,
        via `chalsW` (now in `FRSoundnessFrW0V`, reusable).

2. **Item 5: `kstate_front`** (deferred by your ruling; its target may change with core PR #20).
   The drafted composition at the current pin (`logs/S-G11/FRSoundnessFrKS.lean.draft`, built
   green) is:
   ```lean
   kstate_front_ofR S vk κs₀ hV hq hE hI hOut { nodeLF (nsq nsq_mem.2.1) with front := hLcN } hfit
     (fun k c π L tr y _ _ hk hsem _ hy =>
       start_run (fun r a hr => (implC_meets _ _ _).2.2.2.2.2.1 r a hr) vk k c π L tr y hk hsem hy)
     (w0V_run (fun r ps k β p hr hp => (implC_meets _ _ _).2.2.2.2.1 r ps k β p hr hp) vk)
     hFrontV
   ```
   Its hypotheses are exactly:
   - `hV`, `hq`;
   - `hE` (the `W` branch);
   - `hI : ExtIfaceR …` (`extIfaceR_of` gives it from S-N1's `hRes`, with `hE : S.E = X.E` and
     `ImplT`);
   - `hOut` (O3);
   - `hfit` (S-E's static row count);
   - `hLcN`, `hFrontV` (item 4).

   Once item 4 is done, only `hV`, `hq`, `hE`, `hI`/`hRes`, `hOut` and `hfit` remain.

3. **Item 6** for whatever item 4 and 5 add: the axioms of the final theorem, and the source rule.

## 8. Open questions

1. **O1.** `truthE` over the templated rows changes the §6.3 declarations. The new modules here do
   not depend on it.
2. **The walk bridge (§6.2).** Is it S-G's, or should S-C/S-F2 state `walkABS`'s meaning as a
   lincheck sum?
