# S-G12′ RESULT (pass 1): the walk bridge, `finLc` (ii) on accepted runs, the 3.x composition, the aggregate's log form; handover

- **Base.** HEAD `43b34e1` at the start. HEAD moved to `633ab78` (R-4) and then to **`76c0d78`** (INT-7)
  during the pass. The final build is on `76c0d78`.
- **Build tree.** `logs/fr-build-SG12`: scripts from `fr-build-INT6`, `.lake` copied from `fr-build-SF4`
  as a cache, `logs/org20`. `MINE.txt` lists the five new modules. Logs are in `logs/S-G12/`. Journal:
  `S-G12-JOURNAL.md` (its §0 is the plan table).
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under `timeout`.
  No sub-agents. Nothing was committed. No existing module was edited, and no existing statement changed.

## Status

| Item | State |
|---|---|
| Plan table | **Done** (journal §0). |
| 1. 3.x completion | **Partly done.** **The walk bridge is done** (`walk_bridge`, `free_term`, `lc_bridge`). **`finLc` (ii) holds on every accepted run** (`lc_ii_run`), so `RejLcN` and `RejLc2` fail on accepted runs. This is `NodeL.front` and one `RejF` disjunct. **The composition is done**: `kstate_front_K` / `ks_front_K`, through `kstate_front_ofE'`'s route. The other `hFrontV` checks are not done (§6, item 1). |
| 2. O1 (`truthE` over `nodeIRows`) | **Not started.** It is not a substitution (§5, F3). |
| 3. Rev4 per-kind soundness | **Redirected and started.** R-4-M1/M2 adopted: `FRSoundness4Agg` holds the `runLog` form (`SegSoundLog` with `1 ≤ n`, `VA_extract_log`, `V4_agg_extract_log`). The per-kind potential at `seq4` is not started (§6). |
| 4. Final Rev4 theorem | **Not started.** The 3.x one is `ks_front_K` (§3). The Rev4 target is stated in §6. |

**Checks:**
- `lake build FR` plus the five modules: green, 2,424 jobs on `76c0d78` (`build-final.log`).
- **Axioms** (`axioms.log`, 36 names): only `propext`, `Classical.choice`, `Quot.sound`. 32 use all
  three; `runLog_seqAll`, `VA_sound_log`, `compose_viewsL` and `segSoundLog_lucky` use `[propext, Quot.sound]`.
  No `sorryAx`.
- **Source rule:** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive` gives
  200 files, 0 findings (`source-rule.log`). The coordinator's `#queries` finding is fixed.
- **Names.** Every new declaration was grepped against all `FR*.lean`, untracked files included. Each is
  declared once.

**Imports for `FR.lean`.** Add `import FRSoundness4Agg` and `import FRSoundnessFrKS`. `FRSoundnessFrKS`
pulls in `FRSoundnessFrLc`, `FRSoundnessFrWalk` and `FRSoundnessFrRndV`.

## 1. What was built (`loc.py`, `logs/S-G12/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrWalk` | 315 / 228 / 21 | `maskOf_eq`, `kMat_of_ne`, `mulVec_ofBool`, `maskRows_getD`, `rowWS_getD`; `rowAB`, `colK_eq`, `walk_alg` (the algebra over an abstract `Fin N`); **`walk_bridge`**; `zlmFR_free`, `eqZS_lo`, **`free_term`**; `lcWts`, `lcWts_vM`, **`lc_bridge`**; controls |
| `FRSoundnessFrRndV` | 273 / 215 / 16 | `rSumF`, `rValF`, `rValF_eq_clR2`, `chk2_iff`, `readF_fsQ`, `roundsT2F_vals`, `roundsT2F_chk`, `rSumF_fsQ`, `rValF_fsQ`, `genPhase_roundsF2`, **`roundsF2_view`** (S-G11 §7 1a); `genPhase_uni`, **`uni_view`** (Z2's `λ`) |
| `FRSoundnessFrLc` | 298 / 230 / 21 | views `lc_rk`, `lc_rhi`, `lc_lam`, `lc_alpha`, `lc_claimN`, `lc_v`; **`lc_ii_run`**; **`AccFrontK`**, `accFrontK_of`, **`accFrontK_rejLcN`**, `accFrontK_rejLc2`, the `implC` instances `accFrontK_rejLcN_C` / `accFrontK_rejLc2_C`; `specC_rowW`/`eqZ`/`walkAB`; controls |
| `FRSoundnessFrKS` | 109 / 75 / 2 | **`hAcc_of_finRK`**, **`kstate_front_K`**, **`ks_front_K`** |
| `FRSoundness4Agg` | 213 / 141 / 12 | R-4's probe, adopted (ruling R-4-M1/M2): `runLog_bind`, `runLog_seqAll`, `VA_sound_log`, **`SegSoundLog`**, `mapM_segView_forall₂`, `compose_viewsL`, **`VA_extract_log`**, `VA_rel_log`, **`V4_agg_extract_log`**; controls |
| **total** | 1,208 / 889 / 72 | |

## 2. The main statements

```lean
-- the walk bridge at the specification (w_free = 0)
theorem walk_bridge (w : Fin 9 → F) (hw : w 8 = 0) (l α : F) (rhi rk : Array F) (hrk : rk.size = 14) :
    Eval.walkSpecA (maskRows (Array.ofFn w) (rowWS l rhi)) (eqTab rk) +
        α * Eval.walkSpecB (maskRows (Array.ofFn w) (rowWS l rhi)) (eqTab rk) =
      ∑ j, w j * mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rowW (p := 8) l (ptA 8 rhi)) α) (fun v : Fin 14 => rk.getD v 0)
-- the free term: (1 + α)·y is v_free·M̃_free(r_k)
theorem free_term (l α vf : F) (rhi : Array F) (hrhi : rhi.size = 8) (rk : List F) (hrk : rk.length = 14) :
    let y := vf * (dotAcc 0 (eqZS l 0) (eqTab (rk.take 6).toArray) 64 * eqPoint rhi (rk.drop 6).toArray)
    y + α * y = vf * mle (linM (zlmFR.Ak 8) (zlmFR.Bk 8) (rowW (p := 8) l (ptA 8 rhi)) α) (fun v : Fin 14 => rk.getD v 0)
-- finLc (ii) on an accepted run
theorem lc_ii_run (hW : walkAB meets) (hR : rowW meets) (hZ : eqZ meets) (L : Log)
    (hk : FR.kindOf π = .snark k) (hsem : semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr items) 14 =
      ∑ j, vM (kindOf (fsOf tr items)) (fsOf tr items) j *
        mle (linM (zlmFR.Ak j) (zlmFR.Bk j) (rwL (fsOf tr items)) (alL (fsOf tr items))) (ptOf 14 (rkL (fsOf tr items)))
def AccFrontK impl vk R := ∀ k c π L tr j, ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
    semIR … = some true → (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
    ¬ R L (entriesOf L (pathOf L j))
theorem accFrontK_rejLcN_C (κs₀ : F) (vk : Digest) : AccFrontK (implC (finC finPf) Layout.lRows κs₀) vk RejLcN
-- the aggregate (R-4-M1/M2)
def SegSoundLog (Vseg : SegProgs) (vk : Digest) (Good : Log → Prop) : Prop :=
  ∀ L π v, Good L → segView π = some v → 1 ≤ v.n → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true → chainEnd v.start v.n = v.h
theorem V4_agg_extract_log (hk : kindOf4 π = .agg) (hS : SegSoundLog Vseg vk Good) (hG : Good L)
    (h : (V4with Vseg Vnode vk c π).runLog L = some true) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
```

## 3. The 3.x final theorem as it stands

```lean
theorem ks_front_K (S : Submission) (vk : Digest) (κs₀ : F)
    (hV : S.V = VC finPf Layout.lRows κs₀) (hq : S.qV = qV) (hE : S.E = X.E S.acc)
    (hRes : ∀ L es, StmtN (finC finPf) .N30 L es →
      NodeResid (implC (finC finPf) Layout.lRows κs₀) (sfFinals finP finPf) (vkL es) (fF .N30 L es))
    (hfit : RowsFit (Layout.nodeRows (finC finPf)) 21 23)
    (hFrontV : AccFrontK (implC (finC finPf) Layout.lRows κs₀) vk (RejF (finC finPf) oLcV fun _ _ => False))
    (hQ : ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV) :
    KS (Rel (S.acc vk)) (S.V vk) S.E epsR S.qV
```

Its hypotheses, exactly:
- `hV`, `hq`: the verifier's form;
- `hE : S.E = X.E S.acc`: B-15 (`hE_of_accV` shows it is satisfiable);
- `hRes`: S-E's residual;
- `hfit`: S-E's row counts (O1, §6);
- `hFrontV`: the front's remaining checks (§6, item 1). Its `RejLc2` disjunct is proved (`accFrontK_rejLc2_C`);
- `hQ`: the verifier's query bound, which no module proves yet.

`hStart`, `hW0`, `NodeL` (`nodeLF` + `accFrontK_rejLcN_C`), `hWB` and `hOut` are gone.

## 4. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`, `prof-*.log`)

| Module | wall (import ≈ 5 s) | type checking | max RSS |
|---|---|---|---|
| `FRSoundnessFrWalk` | 11.8 s | 0.11 s | 2.90 GB |
| `FRSoundness4Agg` | 17.6 s | 0.97 s | 2.79 GB |
| `FRSoundnessFrRndV` | 10.3 s | < 0.1 s | 2.96 GB |
| `FRSoundnessFrLc` | 8.7 s | < 0.1 s | 2.95 GB |
| `FRSoundnessFrKS` | 6.8 s | < 0.1 s | 2.92 GB |

- `FRSoundness4Agg`'s time is R-4's control `badSeg_view` (`decide +kernel` on 96 bytes) and four
  `contradiction` calls of 0.66–0.78 s each.
- `decide` uses: `phStart_lc`, `phaseIx_L3`, `mm6_ge8` (per kind), field bounds, `badSeg_view`. None runs
  over a program or a table.

## 5. Findings and deviations

- **F1 (= R-4-M2, found before the redirect).** `SegKSOn`/`SegSoundOn` do not have `1 ≤ v.n`, while
  `SegHolds` requires it. `SegSoundLog` has it. I adopted R-4's form as ruled. `SegSoundOn`/`VA_extract_on`
  are left in place and nothing builds on them.
- **F2. `AccFront` lacks the proof's kind byte.** `AccFront` quantifies over every program kind `k` with
  no `FR.kindOf π = .snark k`. The log's kind (`kindOf es`, the seed's byte) is the program's `k` only
  under that hypothesis (`kindOf_fsQ`). So no check that reads `kindOf es` against the program's
  kind-specific registers can be proved in `AccFront` form, and `RejLcN` is such a check (node weights
  against `vM (kindOf es)`).
  - `hAcc_of_finR` only calls `hFront` under `hk`.
  - **Fix, in new declarations:** `AccFrontK` (with `hk`), `accFrontK_of`, and `hAcc_of_finRK`
    (`hAcc_of_finR` with `AccFrontK`, the same proof, `hk` passed on). The route `kstate_front_K` uses them.
  - `AccFront`, `NodeL` and `kstate_front_ofE'` are unchanged. The forbidden statements cannot take
    `AccFrontK`, so `kstate_front_K` copies `kstate_front_ofE'`'s 14-line body.
  - **Ask:** at the next integration, retire `AccFront` for `AccFrontK`, or keep both.
- **F3. O1 is not a substitution.** `nodeIRows (planOf fin) : List (ℕ × Row)` gives indexed rows, with the
  row index explicit, as `evalMS`/`nodeV_eq` read them (`rowsVal … (nodeIRows pl)`). S-G's E chain reads
  `List Row` by position: `rowMat`, `mA`/`mB`/`mC`, `RowsBad`, `wE4`, `RowsFit`, `truthE_iff`.
  - Restating `truthE`/`nE`/`RejE4`/`hfit` therefore needs the E chain generalised from `rows : List Row`
    to an entries source that both list forms instantiate (`Eval.entriesOf` with explicit row indices).
  - That generalisation touches `FRSoundnessRows`, `FrE`, `FrDF`, `FrStab`, `FrObl`, `PIOP` and
    `Weights` (`wE`). Most of them already take `rows` as a parameter.
  - Not started: it is the next item after `hFrontV` (§6).
- **No value is missing from the finals** for what this pass proved. The Lc check reads only registers
  that the finals assert (`relLc`'s three conjuncts).
- **Lessons** (journal): `congr 1`, `set` and `rfl` against `specC`'s array-valued fields
  (`eqZS`, `rowWS`) hit max recursion or `whnf` timeouts. `congrArg₂`, the `getD` lemmas,
  `dsimp only [specC, specCWith]` and algebra over an abstract `Fin N` avoid them.

## 6. Handover: the remaining items, in order

1. **`hFrontV`'s other checks** (3.x, in `AccFrontK` form; template `lc_ii_run`). The views are now
   all present: `roundsF2_view`, `uni_view`, `chalsF_view`, `oneR_view`, `coordsR_view`, `msgAt_abs`,
   `lc_*`. In order:
   - **`RejL2`.**
     - Rounds `l ≥ 1`: `roundsF2_view`'s round checks, at `n = 8`, through `chk2_iff`.
     - Round 0: `relLc` (i) (`hrel.1.1` in `lc_ii_run`'s proof), with `vZ` (`msgAt_abs` at Zend,
       phase 6, `phStart` 67) and `lc_alpha`. `lc_claimN` already gives `claim0 L2 < size`. A view of
       `claim0 L2` holding `rSumF 69 es 0` is in `roundsF2_view`.
   - **`RejRS (okF oLcV)`, claim 1**: `relLc` (iii), `v_β` = `zhat[1]`, `exec_finRS`'s `rsAlpha 1`. Claims 0,
     2, 3 come from `relZ`'s c-claim, `relSh`'s second check and `relE` (v). In each,
     `rsAlpha j = alphaL κ es j`, from `eqZS` and the `eqTab` points (`chalsW`).
   - **`RejZ`**: `relZ_iff` and Z2's message (`uni_view` gives `λ`; `pzL` is `msgAt es 13`).
   - **`RejS2`**: `roundsF2_view` at `n = 12` (S2 is degree 2), `relSh` with `implC_meets`
     (`shiftTarget`, `shiftMask`, `slotW`, `linkWAll`, `shiftEq`).
   - **`RejEnd` ×2**: `relLr`, `relE` (ii). Lr2 and E2 have `initClaim .zero`, and Lr2 is degree 3, so they
     need a degree-3 / `.zero` sibling of `roundsF2_view` (`round3V`'s last register).
   - **`RejInE`, `RejE4`**: E4's round flags, `relE` (iv). `RejE4` is the O1 item below.
2. **O1** (F3): generalise the E chain over an entries source, then restate `truthE`, `nE`, `RejE4` and
   `hfit` at `nodeIRows (planOf fin)`. The error row is unchanged.
3. **`hQ`** (3.x): the verifier's query bound (the item count, `items_length`).
4. **Rev4** (plan table, journal §0):
   - **(a)** Port the potential to `seq4`. One port serves all six programs: `fsRanges`, `phStart`, the
     dooms' absolute positions at `phaseOffOf seq4`, and the kind type `SegKind ⊕ NodeKind`.
   - **(b)** `flag_fin*` over `FinP`, and `accept_chain`/views over `gen4`. The views of this pass are
     written against `phases`/`skeleton`; they port by replacing `phStart`'s literals.
   - **(c)** `SegSoundLog (VsegC impl₀) vk Good` with `Good L := L.length ≤ logCap ∧ μ L < 1`. It comes
     from the port's extraction (`SegHolds`, then `seg_sound`), with `1 ≤ n` used by the segment's
     `lastOps` (R-4-M2).
   - **(d)** The nodes `{N2, N4, N8}`: slot 1 over `{N2, N4, N8}`, sub-slots over `{L30, L31, L32}`,
     `childOk4` as a truth of N2's relation. `hRes` per node kind names the aggregate's padding and
     byte-counter claim explicitly (R-4-m2: unaligned at `k = 2, 3, 4`).
   - **(e)** The per-program query bounds `qS = 8,905` for `VsegC`/`VnodeC`, for INT-7's `ks_queries4`.
   - **(f)** The Rev4 `E` (B-15 with `A` → `aggWit`, a node → search).
   - **(g)** **The final Rev4 theorem**, target form: `KS (Rel (S.acc vk)) (S.V vk) S.E εR qV4` from
     `hV : S.V = VC4 impl₀ implN cells`, `hq : S.qV = qV4`, `hE : S.E = X.E4 S.acc`, `hRes` (per node
     kind), `hfit` (per node kind's plan), `implSegC_meets` and the node kinds' `Meets`. Every other
     hypothesis is to be discharged.

## 7. Controls

| Definition | Positive | Negative |
|---|---|---|
| `maskOf` / `maskRows` | `maskOf_row0`: only `stream`, `streamEnd41`, `hashB2` and `free` count at row 0 | `maskOf_chain_row0`: a weight on `chain` alone is masked to 0 at its pinned row 0 |
| `lcWts` | `lcWts_leaf_ctl`: a leaf's weights are `v₀` on `chain` | (`lcWts_vM`: the node's `chain` weight is 0) |
| `AccFrontK` | `accFrontK_false` | `not_accFrontK_true`: refuted by any accepted run |
| `SegSoundLog` | `segSoundLog_lucky`: a one-query verifier meets it on the logs without a zero answer | `not_segSoundLog_true`: an accept-all verifier fails it at the `0 → 0` one-step view. `not_segSound_lucky` (R-4's): `SegSound` fails for the same verifier |

## 8. Open questions

1. F2: replace `AccFront` by `AccFrontK` everywhere at the next integration?
2. F3: is the E-chain generalisation over an entries source (several S-G modules, statements
   generalised) ruled as O1's restatement?
3. `hQ` for 3.x, or only the Rev4 bounds (`qS`)?
