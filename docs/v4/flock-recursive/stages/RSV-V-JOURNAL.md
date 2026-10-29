# RSV-V JOURNAL: the reserve's V side (the child's `evalM` claim in the parent's E-phase)

Track RSV-V, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `394f6ce`.
Build tree `logs/fr-build-RSV` (copy of `fr-build-A2pp`, re-snapshotted on HEAD; `MINE.txt` lists the
modules linked to the worktree). Logs `logs/RSV/`. No sub-agents, nothing committed.
A3′ runs in the same worktree (its `FRSoundness4Tail*` edits are not linked into this tree: the
tree builds HEAD's `FRSoundness4*`).

## 0. Reading (D1p-RESULT §3, A2pp-RESULT, PACK §6.4/§8)

Spec (D1p §3): E2 `+ η·eq(r̄*_x, x)·M̃*_η(x, r̄*_y)`, E4 `+ κ_E⁴·W*(y)·eq(r̄*_y, y)`, finE (ii)/(iv) one
term each, B′/finPf 52 cells at `κ′^{j+2}`, fields `fLrEnd` 880 B, `fEEnd` 112 B, gated off for N8 and
leaves.

### Three points the spec leaves open (decided here, reported in the RESULT)

1. **E2's initial claim.** E2's `initClaim` is `.zero` (a skeleton op, `const 0`); the spec's
   `c₀ = η·v*` would need a skeleton change (a new init form, every later register moves). Instead
   the child term is written as `η·eq(r̄*_x, x)·(M̃*_η(x, r̄*_y) − v*)`, whose sum over the cube is
   `η(M̃*_η(r̄*) − v*)` (`Σ_x eq(r̄*_x, x) = 1`): E2 stays a zerocheck with claim 0, and finE (ii)
   becomes `eq(τ, r)(âb̂ − ĉ) + η·eq(r̄*_x, r)·(m̂* − v*)`. Same soundness: own sum `S(τ)` plus
   `η·D` with `D = M̃*_η(r̄*) − v*` fixed before E1 and `η` independent of `τ`: `+1/|F|` (E1's row
   `(e2 + 3)/2^128`). The prover's E2 summand changes accordingly (For P2).
2. **Kinds of different dimensions.** An `N2` parent (E2 22 real rounds, E4 24) may have an `N4`
   or `N8` child (23/25). The parent sums only over its own coordinates; the coordinates above are
   fixed at the child's: the **mixed point** `x̂ = r_E2 ‖ r̄*_x[n_x, 23)`, `ŷ = r′ ‖ r̄*_y[n_y, 25)`.
   Every node's `M̃` is the **constant extension** in the coordinates above its own (`evalMT4` and
   `evalMS4`/`ptOf` read only the kind's coordinates), so an `N2` child's dummy 23rd E2 challenge is
   harmless and needs no zeroing. `W* = M̃*_{κ*}(x̂, ŷ)`.
3. **`W*` when the kinds differ.** The op set has one `evalM (τ σ)` and the node impl evaluates its
   own kind. `W*` is computed as `own + D`, `D` a second `evalM` whose `τ` carries a kind tag
   (`x̂ ‖ kindElem*`, 24 entries): the node impl returns `M̃_{κ*}(x̂, ŷ) − M̃_ν(x̂, ŷ)`, `0` without
   evaluating when `κ* = ν` (the same-kind child is free, as the spec prices it).

## 1. Build tree, baseline

- `fr-build-RSV` re-snapshotted on HEAD with `MINE.txt` (20 modules linked). Baseline `lake build
  FRVerifierImplNode4F FRNodeCircuit4 FRX4Ext FRNodeSound4R FRVIR4Uni FRVerifierImplNode4T`: green
  (2,461 jobs) before any edit.

## 2. Edits, in order

1. `FRShape4`: `Seq.lrEnd`/`Seq.eEnd` (defaults 48), `seq4` 880/112; `phasesOf` reads them; literals
   `fieldSizesOf_seq4`, `piSizeOf_seq4 876176`, `streamBytesOf_seq4 1550976`, `chainLenOf_seq4 24234`.
   Green at once (`decide +kernel` as before).
2. `FRVIRFinals4`: `FinP.rsvOps/rsv/rcells/nrcell` (defaults off); `rsvEOps` (87 registers after
   finE's own 38), `gFinE0` (finE's own ops, asserts gated by a parameter), `gFinE` (exports the 52
   values after `r′`); `rsvBOps` (B′'s values, Horner, `κ′^{11}`); `gFinPf`'s second cell chain and
   `keep rsv`. `finalsOf_seq3` still proves (the reserve is off at `fin3P`).
3. `FRVerifierC4`: `rsvRel` (placeholder until the probe), `rsvCells`, `nodeFinP … true κ.hasPrev
   (rsvCells κ) 52`, `segFinP … false false [] 0`.
4. `FRNodeLayout4`/`FRNodeKinds4`/`FRX4*`/`FRVIRTpl4Bridge`/`FRVerifierImplNode4T`: literals
   (`aggChainLen` 48,468/72,702/96,936; `hUsed` 74,007/122,481/195,192; `hEnd` +2; `segB` 1,550,976,
   `cLen` 24,234; `|π|` 876,176; `aggB 1 = 0x17AA80`, bits 13/12 unchanged). `regions_need_levers`'
   no-L2 stream is now 1,556,928 (still does not fit).
5. `FRVIR4At`: `SameCounts` gains `rsvOps`, `nrcell`; `map_at_gFinE`/`_gFinB'`/`_gFinPf` by cases on
   `rsvOps`; new `gFinE_ex`. `FRVIR4Uni`: the two `SameCounts` proofs.
6. `FRVerifierImplNode4F`: `kindElemN`, `kindOfElem`, `evalMD4`/`evalMDS4` (+ `_eq`), `evalMN4`
   (dispatch on `τ.size = 24`), `implN4F`/`specN4F` re-pointed, `implN4F_meets`, `implN4F_hM`
   (an `e2R`-sized point is not 24), `implN4F_ctl` restated, `evalMD4_ctl`.
7. `FRNodeCircuit4`: `PubCellsR4`.
8. `FRNodeRows4Hint`: regenerated (`laydump4`); HEAD's hint was stale (the merge note), which made
   `pl.inR` fail and `evalMT4` fall back to the sparse sum (650 ms in the first timing run).

## 3. Scan (build tree only, `logs/RSV/scan/`)

10 rounds (two hand edits, A2″'s: `fsCheck_qOf`'s bound, `gLvsOps_4` whole proof) to a green
`lake build FR Solution FRSoundness4TailShift FRSoundness4XCtrl FRNodeSound4Ctrl` (2,586 jobs). 17
declarations sorried, of which 10 are A3′'s (A2″'s list) and 7 this track's.

## 4. KAT (`probe/RsvKat.lean`, `logs/RSV/rsvkat-1.log`, 34 s)

All 13 cases as expected (honest N4←N4/N2/N8, N2←N2/N4/N8 accepted by the three reserve asserts and
every E-phase round assert; wrong `m̂*` rejected at (ii′) and E4's `c₀′`; wrong child point rejected
at (ii′); N8 zero fields pass, junk rejected at the zero assert). The other 874 failing ops are the
zero proof's PIOP checks, identical in every case.

## 5. After A3′ run 2 (`e14db30`) and B2′ (`21ade15`)

- `rsvRel` read off `nodedump4`'s `mregs-p0.txt` (the probe `RsvCells` was too slow: >25 min, killed);
  `rsvCells_ctl` added. Re-snapshot on `e14db30`: the scan gives the same 7 (A3′'s 10 are gone).
- V(N4) with another-kind child: two `evalMT4` (+610 ms) → `evalMPair` with one `protoV4` (+320 ms
  before B2′, +190 ms after).
- B2′'s hoist applied; re-snapshot on `21ade15`; scan: same 7; hint regenerated with `mkhint.py`,
  `inR true`; cells unchanged; plan-form KAT, reserve KAT, cap-check KAT all pass; V(N4) paired against
  B2′'s binary.
- Not mine in the worktree: `FR.lean` (stale vs HEAD), `FRVIRTpl{Build,Ext,Plan,Set}` (B2″). A
  `git checkout -- FR.lean` was refused by the sandbox; left as found.
