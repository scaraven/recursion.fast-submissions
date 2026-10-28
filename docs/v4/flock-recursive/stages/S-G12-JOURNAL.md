# S-G12′ JOURNAL: the knowledge-soundness proof on revision 4.1's verifier

- Base: HEAD `43b34e1` (branch `v4/flock-recursive`). Build tree `logs/fr-build-SG12` (scripts from
  `fr-build-INT6`, `.lake` copied from `fr-build-SF4` as a cache; `logs/org20`). Logs `logs/S-G12/`.
- `lake build FR` on HEAD in the new tree: green, 2,419 jobs, all cached (`build-0.log`).
- Every lean/lake command in the 16G scope under `timeout`. No sub-agents. Nothing committed.

## 0. Plan table

What the 3.x chain (`kstate_front_ofE'` → `ks_of_front`) is made of, and what each piece becomes on
`V4with VsegC VnodeC`.

**How the 3.x proof is built.** The potential `muG` (`FRSoundnessDefs`) is generic in the doom `D`
and the weights `φ`. Everything above it is pinned to 3.x's item list: `fsItems`, the literal
`fsRanges`, `phStart`, `p1Start`, and the absolute log positions in every doom (`69`, `97`, `98`,
`169`, `209`, `311`, `312`, …), plus the 3-constructor `Kind` (`kindOf es`, `lvl κ i`, `Kind.m`).
`seq4` is one item list for all six revision-4 programs (S-0′), so the Rev4 potential is one
re-instantiation at `seq4`'s positions with the kind type `SegKind ⊕ NodeKind`, not six.

| 3.x piece | Rev4 | Why |
|---|---|---|
| `muG`, `muG_step`, `hloc_of`, `muG_step_of`, `card_bad_le`, `condCount*`, `ext*` (`FRSoundnessDefs`) | **unchanged** | generic in `D`, `φ`, `rnd` |
| `KState` assembly `kstate_of_front`, `ks_of_front` (`FRSoundnessCompose`) | **generalised** (`FrontObl`'s phase list, `front_check`, `tailCls_check` are `decide`s over 3.x positions) | positions |
| `fsRanges`, `fsRnd_ok`, `phStart`, `p1Start`, `cStart`, `p3S0`, `pfStart` | **generalised over `Seq`** (`phaseOffOf`, `itemsOf`) | positions |
| The truths and dooms per phase (`FrZ`, `FrZM`, `FrL`, `FrLN`, `FrS`, `FrSh`, `FrE`, `FrB`, `FrRS0`, `FrRS`, `FrW0`, `FrPend`, `FrBind`, `FrDF`, `FrObl`, `FrStab`, `Rows`, `Truths`, `PIOP`, the Ligerito tail `Tail*`, `Fold`, `LigFinal`, `Hide`) | **generalised over `Seq`/kind**: the algebra (`lin_*`, `bz_*`, `batch_*`, `linM_free_mle`, `quirky_claim_split`, the Ligerito/MCA lemmas) is position-free and **unchanged**; the doom definitions, their `Reads n` and the `single`/`habs` counts are restated at `phaseOffOf seq4` | positions, `N_M`/`τ`/`σ`, Lr 17, E2 23, E4 25 |
| `kfT`/`indKW`/`nodeKinds` (3.16 kind factor) | **generalised**: N2/N4/N8 layouts (`FRNodeLayout4`) | 1 + k slots |
| `zlmFR`, `kMat`, `walk bridge` (item 1) | **unchanged** (per block; the block circuit is the same) | spec algebra |
| `accept_chain`, `fields_chain`, the views (`one_view`, `chalsF_view`, `coordsR_view`, `oneR_view`, `rs1_val`, …) | **generalised**: `gen4`'s skeleton (`genPhase4`, `seedOps4`, `stmtOps4`) and `finOps4` (relocated fields) | program |
| `flag_finZ` … `flag_finPf` | **generalised over `FinP`** (S-F4 §3.1 left them; at `seq3` they are 3.x's by `finalsOf_seq3`) | sizes |
| `hFrontV` (item 1), `start_run`, `w0V_run` | 3.x: **completed here**; Rev4: re-run on the generalised flags | |
| `kstate_front_ofE'` | 3.x: composed here (item 1); Rev4: **new** `kstate4` over `V4with` | |
| `truthE`, `nE`, `RejE4`, `hfit` over `Layout.nodeRows` (O1) | **restated over `nodeIRows (planOf fin)`** (item 2) | ruling O1 |
| `ExtIfaceE`, `extIfaceE_of`, `X.E` (B-15) | **generalised**: `Eout` dispatch on Rev4 kinds (`A` → `aggWit`, node → search) | B-15 |
| `SegKSOn` (S-F4), `VA_extract_on` | **replaced (ruling R-4-M1/M2)** by `SegSoundLog` (`runLog` on a good log, `1 ≤ n`) and `VA_extract_log` (`FRSoundness4Agg`); the per-kind `SegSoundLog` is new (item 3) | new kind `A` |
| node relation over `{N2, N4, N8}` × `{L30, L31, L32}` | **new** (generalises N30's two slots; `hRes` stays S-E's) | B-13 |

## Log

### Item 1b, the walk bridge (done): `FRSoundnessFrWalk`

- `maskOf_eq` (maskOf as `Σ_{j<9} [j does not pin k] w_j`), `kMat_of_ne`, `mulVec_ofBool`,
  `rowAB`/`colK_eq`/`walk_alg` (the algebra over an abstract `Fin N` and kind type),
  **`walk_bridge`** (spec level: `walkSpecA + α walkSpecB` at `maskRows (ofFn w) (rowWS λ r′_hi)`,
  `eqTab r_k` is `Σ_j w_j M̃_j(r_k)` when `w_free = 0`), `zlmFR_free` (free's matrices are `I`),
  `eqZS_lo`, **`free_term`** (`y + α y = v_free·M̃_free(r_k)`, via `linM_free_mle`),
  `lcWts` (the verifier's `packFK` weights), `lcWts_vM` (with `v_free` at `free` they are `vM`'s
  shape), **`lc_bridge`** (the verifier's `finLc` (ii) right side, for any `impl` whose `walkAB`,
  `rowW`, `eqZ` meet their specs, is `Σ_j v′_j M̃_j(r_k)`). Controls `maskOf_row0` (+),
  `maskOf_chain_row0` (−), `lcWts_leaf_ctl` (+).
- Lessons: `congr 1` and `set` on goals with `Fin (2^14)` sums hit max recursion / whnf timeouts;
  `congrArg₂`, explicit `getD` lemmas (`maskRows_getD`, `rowWS_getD`) and an algebra lemma over
  abstract `Fin N` avoid them.

### Coordinator redirect (R-4-M1/M2, mid-pass): done, `FRSoundness4Agg`

- Adopted R-4's probe: `runLog_bind`, `runLog_seqAll`, `VA_sound_log`, **`SegSoundLog`** (with
  `1 ≤ n`), `mapM_segView_forall₂`, `compose_viewsL` (composition on the views' fields only, so
  it is independent of the in-progress `SegView.stmt` change in the worktree), **`VA_extract_log`**,
  `VA_rel_log`, **`V4_agg_extract_log`**. Controls `not_segSound_lucky` (−, R-4's), `segSoundLog_lucky`
  (+), `not_segSoundLog_true` (−, new: an accept-all verifier fails `SegSoundLog`).
- Independently found before the redirect: `SegKSOn`/`SegSoundOn` lack `1 ≤ v.n` while `SegHolds`
  requires it (= R-4-M2).

### Item 1, the views and `finLc` (ii) on accepted runs (done): `FRSoundnessFrRndV`, `FRSoundnessFrLc`

- `roundsF2_view` (degree-2 F rounds with a free first claim: `claim0` = round 0's `g(0)+g(1)`, the
  last register = last round's `g(r)`, the round checks), `uni_view` (Z2's `λ`).
- `lc_rk`, `lc_rhi`, `lc_lam`, `lc_alpha`, `lc_claimN`, `lc_v`: `finLc`'s registers on the log.
- **`lc_ii_run`**: on an accepted run (with `FR.kindOf π = .snark k`), `clR2 69 … 14 = Σ_j vM_j M̃_j(r_k)`,
  from `accept_chain` (rest field 1), `flag_finLc`, `relLc`'s (ii), `lc_bridge`, the views.
- **Finding F2**: `AccFront` has no kind-byte hypothesis, so a check comparing `kindOf es` with the
  program's kind cannot hold in that form. New `AccFrontK`; `accFrontK_rejLcN(_C)`, `accFrontK_rejLc2(_C)`.
- `specC`'s array-valued fields: `rfl` against `eqZS`/`rowWS` hits max recursion; `dsimp only [specC,
  specCWith]` works (`specC_rowW`, `specC_eqZ`).

### Item 1c, the composition (done): `FRSoundnessFrKS`

- `hAcc_of_finRK` (`hAcc_of_finR` with `AccFrontK`), **`kstate_front_K`**, **`ks_front_K`**: hypotheses
  `hV`, `hq`, `hE`, `hRes`, `hfit`, `hFrontV` (`AccFrontK`), and `hQ` for `ks`.

### INT-7 committed (`76c0d78`), coordinator's source-rule finding

- Re-snapshotted; `lake build FR` + my five modules green, 2,424 jobs (`build-final.log`).
- `#queries` in a comment of `FRSoundness4Agg` reworded; source rule 200 files, 0 findings.
- Axioms (36 names) clean; profiles in `prof-summary.txt`. RESULT written with the handover (§6).
