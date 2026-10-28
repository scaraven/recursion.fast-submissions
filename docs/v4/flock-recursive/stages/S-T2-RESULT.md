# S-T2 RESULT: `rsWeight` at the 4.1 node layouts, fast. V(N4) 204.4–204.7 → 173.2–177.7 ms best on the VM

Stage S-T2, 2026-10-28. HEAD `036eb7e` (S-E12d). Build tree `logs/fr-build-T2`, a copy of
`fr-build-SE12d` against `logs/org20`, with `MINE` = `FRKindWeight FRVerifierImplOps
FRKindWeight4 FRVerifierImplOps4`. Logs are in `logs/T2/`; the journal is `S-T2-JOURNAL.md`. Every
lean, lake and probe command ran in the 16G scope with a `timeout`. Nothing is committed.

**No existing statement changed.** `FRKindWeight` and `FRVerifierImplOps` are not edited at all, so
`rsWeight_meets`, `kwI_eq` and `rsWeightF_eq` keep their text and proofs. Everything is in two new
modules.

## 1. The finding that shaped the design

No 4.1 `rsWeight` existed. `implN4 base tS ν` inherits `rsWeight` from `base ν`, which is 3.x's
`rsWeightF`. Its specification `rsWeightS` weights claim 2 by **3.x's** node layout (`KW.kwS`,
`Layout.nodeLayout`, `free` extended to `2^18`), and that is not the 4.1 kind factor. So the lever
is two things at once:
- a 4.1 specification, `rsWeightS4 ν`, with claim 2 weighted by `N4c.kf4 ν` over `nodeLayout4 ν`;
- a fast implementation proved equal to it.

The control `kwS4_ne_3x` shows that the two weights differ (§4).

## 2. What was built (code lines from the core's `loc.py`)

| Module | New | Content | Code |
|---|---|---|---|
| `FRKindWeight4` | yes | **Spec `kwS4 ν n β q ρ = Σ_{t<2^n} kf4 ν β t · eq(q,t) · eq(ρ,t)`**. `ex` (a kind's exponent), `ends4` (each layout interval's two ends with its exponent, plus the `free` tail `[blocks, 2^n)`), `allKeys4`, `selL`/`grpL`, **`skel4 ν n`** (merged dyadic blocks per level), `kwKS` (a skeleton's Horner stage value). Proofs: `contig_sum` (on a tiling list, a block's interval sum is its `ivAt`), **`kf4_ends`** (`kf4` = `Σ β^i [t < x]` over the endpoints, characteristic 2, from `layout_contig`), `kwS4_ends`, `kwS4_keys`, `allKeys4_lvl`, `grpL_sum`, **`kwS4_eq`** (spec = skeleton, any claim point in `K`), **`kwS4_fast`** (the `F`/`K` split through `KW.mkEnt`). Controls in §4. | 180 (16 thm) |
| `FRVerifierImplOps4` | yes | **Spec `kwSL4`, `rsWeightS4 ν`** (`rsWeightS` with claim 2's stage weight `kwSL4 ν (β^(2^k))`). Implementation: the cached skeletons `skelN2` (17 bits) and `skelN4`/`skelN8` (18 bits); `skelAt` (`skelAt_eq`); `kfStep4`; **`wEvalKF4`** (claim point in `F`); `kwSL4I`/`wEvalKC4` (the `K` fallback); **`rsWeightF4 ν`**. Proofs: `kf_fold4`, **`wEvalKF4_eq`**, `kwSL4I_eq`, **`rsWeightF4_meets`**. Wiring: **`withRS4 base ν`**, `withRS4S spec ν`, **`withRS4_meets`**. Controls `skelAt_pos`/`skelAt_neg`. | 140 (10 thm) |

**Statements:**

- `rsWeightF4_meets (ν) (r ps κ β ρ) (hr : r.size = 7) : rsWeightF4 ν r ps κ β ρ = rsWeightS4 ν r ps κ β ρ`.
  The only hypothesis is `|r″| = 7`, which the spec's fixed `range 128` needs and `Meets` provides.
  Unlike 3.x's `rsWeight_meets`, there is no bound on `|ρ|`, and no claim or `ρ` size is assumed.
- `wEvalKF4_eq` and `kwSL4I_eq` hold for every input. `kwS4_eq` and `kwS4_fast` hold for every
  `n`, with `s` the per-level sums, which is how the fold defines them.
- `withRS4_meets ν : base.Meets spec → (withRS4 base ν).Meets (withRS4S spec ν)`.

**The method.** `kf4 ν β t = Σ_{(i,x) ∈ ends4} β^i [t < x]` on `[0, 2^n)`: in characteristic 2
each interval is `[t < hi] + [t < lo]`, and the `free` tail is `[t < 2^n] + [t < blocks]`. So a
stage is `Σ β^i psum(x)`, and each `psum(x)` is a sum over dyadic blocks (S-T1's
`KW.psum_cubes`). The blocks of all endpoints, merged by key, form the skeleton:

| | N2 (17 bits) | N4 (18 bits) | N8 (18 bits) |
|---|---|---|---|
| kind-change endpoints | 89 | 95 | 106 |
| blocks in the skeleton | 114 | 118 | 138 |

Patterns (S-T1's `Item.pat`) are not needed: the WOTS path runs add only about 30 blocks. A stage
then costs one `F.sq` and one `smulF` per block, one Horner sum over the levels, and `eq` on the 7
high coordinates, all through S-T1's `KW.mkEnt`/`gsum`/`sqG`/`gmK`/`sqG_gmK`, unchanged.

## 3. Measurements (VM; S-E8's method: best and median of 21 warm `runSeq` runs; probe `VTime4`)

**V(N4).** "Before" is mode `cn4` (S-E12d's `NI4.implN4` with 3.x stand-ins). "After" is mode `t2`,
the same with `base := fun ν => Impl.withRS4 implN4 ν`.

| Run | before: best / median (ms) | after: best / median (ms) | Δ best | log |
|---|---|---|---|---|
| sequential, core 29, load ≈ 7 | 216.5 / 232.3 | 186.9 / 204.5 | −29.6 | `vtime4-cn4-19835`, `vtime4-t2-15924` |
| sequential, core 29, load ≈ 7 | 209.8 / 235.4 | 177.3 / 192.8 | −32.5 | `vtime4-cn4-19671`, `vtime4-t2-23835` |
| **A/B, two cores at once, then swapped** | **204.7 / 218.3 (c29), 204.4 / 216.9 (c28)** | **177.7 / 184.3 (c28), 173.2 / 183.3 (c29)** | **−27 to −31** | `ab-*.log` |

At S-E12d's ratio of 1.19, the A/B best is ≈ 146–149 ms on the 7763, against the 206 ms cap. The VM
median is 183–184 ms.

**Per op in the N4 program** (`prof`, 7 runs; `prof4-cn4.log`, `prof4-t2.log`): `rsWeight`
**44.9 → 9.2 ms**. The other ops are unchanged within noise: `evalM` 93 / 83, `walkAB` 9.8 / 9.2,
`tensorW` 8.9 / 8.3.

**`rsWeight` per node kind** (`rsw 11`: random operands at the kind's sizes; `|r″| = 7`; four claims
in `F` of `7 + nbN`; `ρ` in `K`; best / median of 11, ms; `rsw-1.log`):

| Kind | 3.x `rsWeightF` (fallback `wEvalKC`) | **`rsWeightF4 ν`** | of which claim 2 `wEvalKF4` |
|---|---|---|---|
| N2 (24 coords) | 38.3 / 41.4 | **8.7 / 9.6** | 5.3 |
| N4 (25) | 41.6 / 42.9 | **8.9 / 9.2** | 7.2 |
| N8 (25) | 44.6 / 46.4 | **10.1 / 11.7** | 6.5 |

The probe prints hundredths without zero padding, so "10.1" may be 10.01.

**Numeric cross-checks** (same log; each is also a theorem):
- per kind, `wEvalKF4` equals the `K` fallback `wEvalKC4` (253–316 ms);
- at one stage, the specification's direct sum over all `2^17`/`2^18` blocks (`kwS4`, 15–40 s)
  equals the skeleton's `kwKS`;
- `rsWeightF` (3.x) and `rsWeightF4` give different values, as expected (see §1).

## 4. Controls

| Definition | (+) | (−) |
|---|---|---|
| `kwS4` (spec) | `kwS4_cube`: at a Boolean point it is `kf4 ν β t₀`. `kwS4_hashA`: `β^3` at `N4`'s `c_A` block (`hashA`) | **`kwS4_ne_3x`**: at `β = 0` and block 50000 of `N4` (a `stream` block), the 4.1 weight is `1`; 3.x's `KW.kwS 18` (the stand-in) is `0` (`free`) |
| `skel4` | `skel4_levels`: `n + 1` levels. Numerically equal to the spec's direct sum (§3) | — (`kwS4_eq` holds for every input) |
| `skelAt` cache | `skelAt_pos`: `N4` at 18 bits reads `skelN4` | `skelAt_neg`: at 17 bits it builds `skel4` on the call |
| `rsWeightF4` guard | the guard is 3.x's (`p.all (·.f₁ == 0)`): S-T1's `rsF_guard_pos`/`rsF_guard_neg` apply verbatim; the measured claims are in `F` (`F-points [true ×4]`) | |

## 5. Checks

- **Build:** `lake build FR FRNodeRows4Fit FRNodeRows4Model FRVIRTplSet FRKindWeight4 FRVerifierImplOps4`
  is green on HEAD plus the two new modules: 2,506 jobs (`build-final.log`).
- **Axioms** (`axioms.log`, `ax/AxT2.lean`, 22 names): the new theorems and controls, plus
  `rsWeight_meets`, `rsWeightF_eq` and `kwI_eq`. Each uses only `propext`, `Classical.choice` and
  `Quot.sound`; `skel4_levels` and `skelAt_*` use only `propext` and `Quot.sound`.
- **Source rule** (`python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`): 293
  files, 0 findings (`source-rule.log`).
- **Sequential profiles** (one core, `-DElab.async=false --profile`):

| Module | wall | type checking | tactics | max RSS |
|---|---|---|---|---|
| `FRKindWeight4` | 8.8 s | 0.33 s | 0.37 s | 2.75 GB |
| `FRVerifierImplOps4` | 7.5 s | 0.04 s | 0.43 s | 2.73 GB |

## 6. Wiring (for S-CN4b / INT-8): no edit to `FRVerifierImplNode4*` is needed

`implN4 base tS ν` takes `rsWeight` from `base ν`. Wherever the 4.1 node's `base` and `spec` are
instantiated, pass:

```lean
implN4 (fun ν => Impl.withRS4 (base ν) ν) tS ν          -- rsWeight := rsWeightF4 ν
specN4 (fun ν => Impl.withRS4S (spec ν) ν) ν            -- rsWeight := rsWeightS4 ν
-- Meets: implN4_meets ν (Impl.withRS4_meets ν (h : (base ν).Meets (spec ν))) htS
```

This is what the probe's `implN4T2` does. The alternative is an in-place edit of
`FRVerifierImplNode4.lean`:
- add `import FRVerifierImplOps4`;
- add `rsWeight := Impl.rsWeightF4 ν` to `implN4`'s record and `rsWeight := Impl.rsWeightS4 ν` to
  `specN4`'s;
- in `implN4_meets`, drop `h5` (`obtain ⟨h1, h2, h3, h4, -, h6, …⟩`) and supply
  `fun r ps k b p hr _ => Impl.rsWeightF4_meets ν r ps k b p hr` in its place.

Both forms change `specN4`'s `rsWeight` from 3.x's `rsWeightS` to `rsWeightS4 ν`.

## 7. Deviations and open questions

1. **New spec, not just a faster op.** The brief said to keep the existing `rsWeightF_eq`. Its spec
   is 3.x's layout, so a 4.1 fast path proved against it would compute the wrong kind factor. The
   4.1 claim-2 weight `rsWeightS4 ν` is defined from `kf4`, which is P4b's `kf`
   (`FRSoundness4P4aNZ.kfInd4`). The 4.1 soundness side does not yet consume an `rsWeight` spec
   (`FRSoundness4P4bB.wrsL4` has `kfT4 kf` as a table). **For R4/the orchestrator:** the RS
   front's bridge should state `wrsL4`'s Φ form against `rsWeightS4 ν`, as 3.x's
   `rsWeight_kind_eq` does against `rsWeightS`.
2. **No pattern items.** The 4.1 skeleton uses plain interval endpoints (114–138 blocks). This is
   simpler than S-T1's `plan`/`Item.pat` route and needs no hand-written plan: the items come from
   `nodeLayout4` itself, and correctness rests on `layout_contig`.
3. **The fast path is not gated on sizes.** `wEvalKF4` handles any `|ρ|`. The skeleton is cached at
   the kind's block bits (`skelAt`), and other sizes build it on the call, correctly but more slowly.
4. **`FR.lean`** does not import the two new modules, and I may not edit it. The build lists them
   explicitly. They enter `FR`'s closure once `FRVerifierImplNode4` (or its instantiation) imports
   `FRVerifierImplOps4`.
5. **Probe** (outside the entry): `logs/fr-build-T2/probe/VTime4.lean` gains mode `t2`
   (`implN4T2`) and mode `rsw` (the per-kind benchmark and cross-checks).
