# A3′ JOURNAL: restating the Rev4 chain for CapChk (β)

Track A3′, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `f853d37`
(A2′'s WIP). Build tree `logs/fr-build-A3`, logs `logs/A3p/`. No sub-agents, nothing committed.

## 1. Setup

- `logs/fr-build-A3` is a copy of `logs/fr-build-orch`. Its `.lake/build` was copied from the main
  worktree's `logs/fr-build-A2/.lake/build` (read only), so the unchanged modules' oleans are reused.
- `snap.sh`: `packagesDir` and the `RecursionFast` path are fixed to the main worktree's
  `logs/pkgs` and `logs/org20`. These are the paths the copied oleans were built against; the
  rev44 symlinks point at the same directories.
- `b.sh` is copied from `fr-build-A2`. It runs `lake build` in the 16G scope under `timeout`.
- Baseline: `MINE="FRSoundness4TailD FRSoundness4R4Run" ./snap.sh; ./b.sh FR`
  (`logs/A3p/build-0-baseline.log`). It reproduces A2′'s state: 2,575 jobs, red in exactly
  `FRSoundness4R4Run` (lines 28, 70, 110, 169) and `FRSoundness4TailD` (lines 287, 288, 311).

## 2. Reading (A2′ RESULT §5, PACK-4.4 §3.3, §7.1, §9.1)

PACK §9.1 asks for these:
- `pathDig es i q`, "a function of the log", which replaces the path-to-`capDig` conjunct of
  `FinRest4.cols`;
- `D_ζ es`, a doom charged at P3.4's first squeeze: `∃ i q, pathDig ≠ capDig` and
  `Σ ζ^r (pathDig − capDig) = 0`;
- `D_z`, at CapChkZ (phase 53, FS 483);
- `cap_of_chk : capChk4 → ¬D_ζ → ¬D_z → truthCap`.

The doom framework (`StepObl` in `FRSoundness4TailStep`) needs every doom to be a predicate on
`(L, es)` that is fixed when its squeeze is answered. Two obligations enforce this:
- `hsingle`/`hround`, which count the answers that newly doom;
- `hstab`, which says `D (L.take i) X ↔ D L X`.

For `D_ζ` this means every coefficient `pathDig − capDig` must be fixed by the log before ζ's
squeeze.

## 3. The blocker

**What V checks.** `posOps4` reads π's column (`piField 0 (co + p·colBytes)`) and π's siblings
(`merkleOps4 … (so + p·sib·32)`). It hashes them up to `cur = curOfY`, and no compare follows.
`capChkOps` then reads `ζ = chK` of P3.4's first answer and `z = chK` of CapChkZ's answer, and
accumulates `ζ^r·lo(cur_r)` and `ζ^r·hi(cur_r)` (`splitDigest`, `mulKF`, `addK`).

**`cur_r` is fixed by nothing before ζ.**
- `fsItems4` is "the item sequence without the column and node queries" (`FRSoundness4Pos`).
- Q.i has no Fiat–Shamir item: `fsStarts4` gives Q.i the same start as P3.i (370, 397, 421, 443,
  463).
- So no item of the chain absorbs a column, a sibling or a path digest. ζ, z and every challenge
  are functions of the chain alone, and the prover picks π's columns and siblings after seeing
  them.

**Hence no function `pathDig (L, es)` exists that equals V's `cur_r`.** `cur_r` is a function of π.
`D_ζ` as written in §9.1 cannot meet `hstab`/`hround`. This is not a gap in the proof: the
statement is false (§4).

## 4. The attack (characteristic 2, Bellare–Micciancio's XHASH attack)

`F = GF(2^128)` (`FRField128`, `CharP F 2`) and `K = GF(2^256)`. For a fixed ζ, the map
`d ↦ (ζ^r·lo d, ζ^r·hi d) ∈ K²` is GF(2)-linear in the 256 bits of `d`. Identity (I) is therefore
512 GF(2)-linear equations in the path digests.

The attack:
1. Run any prover until ζ and z are known.
   - For example, a cheating prover with a far or uncommitted word. It answers each query with a
     column whose fold is the value that its fake next level needs. A level-0 column has 62
     free F elements after the fold's 2 F constraints, and a level ≥ 1 column has 14.
2. For each read `r`, make two openings with the required fold. The cheapest way is to change one
   sibling at the top of the path: one extra compression. This gives roots `d_r⁰` and `d_r¹`.
3. Set `Δ_r := φ_r(d_r¹ − d_r⁰)`.
4. Solve `Σ_r b_r·Δ_r = T − Σ_r φ_r(d_r⁰)` for `b ∈ GF(2)^871`. Here
   `T = Σ_k A_k·(lo cap_k, hi cap_k)`, and `A` is the honest one for ζ and the fixed `k_r`, so
   (II) holds exactly.
5. There are 871 unknowns and 512 equations. The `Δ_r` are uniform in the 256-dimensional
   subspaces `ζ^r·(F × F)`, and `V_r + V_{r'} = K²` whenever `ζ^{r−r'} ∉ F`. So
   `Pr[rank < 512] ≤ 2^512 · 2^{−870} = 2^{−358}`.
6. Open read `r` with `d_r^{b_r}`. Then (I) and (II) hold, and every fold check holds by
   construction.

**Cost.** About `871·(sib + 2)` compressions (≈ 20 k), plus Gaussian elimination on a
512 × 871 GF(2) matrix. The Merkle commitment therefore binds nothing: a false statement has an
accepting proof. `KS … epsR` at the new V is false for any ε below a constant, with
`logCap = 2^96` queries to spare.

**Any per-read additive check fails the same way.** Choosing one of two openings per read always
linearises the sum. A logUp variant fails as well, and it is worse in characteristic 2: a repeated
fake digest cancels mod 2. The coefficients must be bound in the chain before the challenge.

## 5. ε (asked, independent of §4)

- `D_z` sits at a single squeeze (phase 53). Its count is 1,407 ≤ `N = 239·2^128` (`N_le`), so it
  fits.
- `D_ζ` sits in P3.4's 5-squeeze phase, whose final doom is `finP2 4` today (no κ_c row at level 4).
  `870/2^256 ≪ deltaR = epsD − 2^{-142}`, so it fits.
- `εR = 15/2^124` would stand. But `D_ζ` cannot be stated (§3), so this is moot.

## 6. Stop

I stopped before editing any source, following the brief's stop rule (a construction that cannot
reach the same ε). No module of the worktree is changed. The build tree and the baseline log are
kept for the restart.

# Run 2 (2026-10-29): (β′) on A2″'s V, HEAD `394f6ce`

Build tree `logs/fr-build-A3b` (a copy of `fr-build-A2pp`, re-snapshotted on HEAD), logs `logs/A3b/`.

## R2.1 Baseline

- `snap.sh` with empty `MINE`, then `b.sh FR Solution FRSubmission4Cert FRSoundness4XCtrl FRNodeSound4Ctrl
  FRSoundness4TailShift` (`logs/A3b/build-0-baseline.log`): red in exactly `FRSoundness4TailD` (287, 288, 311)
  and `FRSoundness4R4Run` (29, 71, 111, 170), as A2″ §5 says; everything below them is unbuilt.

## R2.2 A gap in PB-M1's chain: `RejT` under `¬truthCap`

- PB-M1's final split refutes the three disjuncts of `DT 55` under acceptance, but the composed doom is
  `DC (RejC …) (Dp DkC)`, and `RejC ∋ RejT`. `RejT`'s round-0 check of P1.(i+1) (`Chk2` against
  `lvC (i+1) = vNext … (c1 i)`, i.e. the batched folds `foldAtN` of the **committed** words) holds on an
  accepted run only if the opened columns are the committed ones: `y_eq_foldAtN4` needs
  `openPath … = some (capDig …)`, which is `truthCap` now.
- So under `¬truthCap` an accepted chain can carry `RejT` from P1.1 on, `DC` holds at the end through
  `RejT`, and `hend` (`¬DC` at the end) cannot be proved. The potential does not charge the `ζ`/`z`
  events in that case either (`stepObl_compose` counts no escape once `Rej` holds).
- Fix (no ε change): guard the composed `Rej` by the cap truth once `D` is in the chain:
  `RejG RejF c₀ L es := RejC RejF c₀ L es ∧ capOK es`, `capOK es := es.length ≤ phStart4 52 ∨ truthCap es`.
  `RejG` is not monotone at the `CapD` absorb (a `RejC` log can lose `capOK`), so `PhaseObl`'s `rej`
  drops `mono` (a `RejSq`: `sq` and `stab`) and its `habs` covers `Rej ∨ Dk → Rej ∨ Dk`; at the `CapD`
  absorb a lost `capOK` is `¬truthCap`, which is `DT 52`. The generic `StepObl` only needs the composed
  `DC` to be monotone at absorbs, which holds.
- At the end: `truthCap` gives `¬RejC` (the old `AcceptTail` argument); `¬truthCap` gives `¬capOK`.

## R2.3 Tail side (T4)

- New `FRSoundness4TailCap`: the log values (`dAt`, `zetaK`, `aAt`, `zK`, `kCap`, `capG`, `loD`/`hiD`),
  `capChk4` (V's three asserts), `truthCap`, the escape sets `DZeta`/`DZ`, `cap_of_chk`, the counts
  `card_dZeta ≤ 870`, `card_dZ ≤ 1535` (SZ over `K` via `card_chK_fiber`), congruences along the chain.
- `TailD`: `DT` = levels (`DTl`) / Pf / cap (`DCap`: PB-M1's chain `DCapD`, `DCapZeta`, `DCapA`, `DCapZ`);
  `phOf_check` to 486, `phOf_ge` split by `phStart4 52 … 55`, `phOf_bounds ≤ 55`, `rounds_check` 486.
- `TailStep`: `RejSq`, `PhaseObl.rej : RejSq`, new `PhaseObl.hrej`; `stepObl_compose` takes `hrej`.
- `TailM`: `DPf_append`, `DCap_stab`, `DT_stab` to 55. `TailC`: `cap_items`, `cdOK`, `RejG`, `rejG_sq`,
  `hrej_G`, `habs_cap`, `single_cap`; `phaseObl_of`/`muT_laws_of_front`/`chainStab_of` at `RejG`;
  `tailCls_check` up to `phStart4 52`; `front_check` to 30 phases.
- `TailLig`: `AcceptTail` (`len` to `phStart4 55 + 1`, `p1`/`lvl4` under `truthCap`, new `cap`);
  `not_DC_end` = PB-M1's final split + the `cdOK` guard; the bridges `colOf_of_dpath`, `foldAt_of_dcols`,
  `truthP3_four_of_dcols` (take `truthCap`).

## R2.4 R4 side

- `R4Run`: 486; `capF`, `opsOfFields`, `runFields_snoc`, `opsOfFields_snoc`, `finOps4_eq` (fields ++ capF),
  `accept_chain4` over `opsOfFields rs fs`. `R4Acc`/`R4Ex`/`R4Fld` over `rest ++ [capF]`; `Fields4.cap`.
- `R4PosT`/`R4Qv`: `capO` → `dO`, the reference compares `cur` with `D_r` (π at `dO + 32·p`); the views
  give the cap-index and `D_r` registers. `R4Cols`: `dMsg4`, `dAt_eq4`, `cols4_of_run` to `dAt`.
- New `FRSoundness4R4Cap`: `reloc_capChk`, the families (`run_head`, `run_powChain`, `run_bitPows`,
  `run_macDs`, `run_macAs`, `run_asserts`), `capChk_run` (the three asserts on register values),
  `reads_view4`, `one_ans4`, `aAt_eq4`, `capG_eq4`, `capChk4_of_fields`. `R4LinkP` adds `cap`.
- Traps met: `omega` ignores hypotheses whose type is `Reg`; the kernel recurses on `X.size + n` vs
  `X.size + m` defeq with large literals (prove sizes with `omega`, not `rfl`/`simp`-closing);
  `simp` with `Finset.sum_range_succ` unfolds 870 steps (use `sumLo_succ` once).
- `R4PfRun.gLvsOps_4`: `seq4_ell_star` (`ell` agrees at every level; the cap does not).
- Build 3 (`logs/A3b/build-3.log`): `FR Solution FRSubmission4Cert FRSoundness4XCtrl FRNodeSound4Ctrl
  FRSoundness4TailShift` green, 2,588 jobs.
- Other agents (RSV-V, B2′) edit V-side modules in this worktree; this tree links only this track's
  modules (`mymods.txt`), so it builds HEAD's V.

## R2.5 Controls and checks

- `TailCap`: `capChk_pos`, `capChk_neg`, `dZeta_ctl`, `dZeta_neg`, `dz_ctl`. New `FRSoundness4CapCtrl`:
  `dZeta_inst` (two reads committed to `d₁` under zero caps, `ζ = 1`), imported by `FR`.
- Build 5 green (2,589 jobs). Axioms: 41 theorems, standard three only. Source rule: 377 files, 0.
- Profiles: `logs/A3b/profile-summary.txt` (24 modules, ≈ 303 s wall sequential).
