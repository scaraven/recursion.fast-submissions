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
