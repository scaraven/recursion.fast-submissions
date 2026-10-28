# G1: build-time golf of S-0/S-F/S-G's verifier finals and spec

Track G1 (golf for the H-cert build cap: 611–712 s on the EPYC 7763 against `build_s = 600`). Scope:
`FRVIRFinalsSG`, `FRVIRSpec`, `FRVIRFinals`, `FRVIRFinalsSF`, and `FRVIRFinals4`. No other module was
edited. The work is uncommitted, in the worktree, against `logs/org20` (build tree
`logs/fr-build-G1`, copied from `logs/fr-build-INT6`; `MINE` = the five modules).

## 1. Result

Sequential elaboration, one core: `lean -DElab.async=false --profile`, no trace. CPU time is user + sys.
The VM is shared, and single runs vary by up to 30 %, so each figure is the **minimum** over the runs
listed. "before" is the saved original source (`logs/G1/before/`), run against the same tree. Logs:
`logs/G1/measure-{m1,final1,final2,spec3}/` (`summary.txt` has one line per run).

| module | before: CPU s (min; runs) | after: CPU s (min; runs) | change | kernel ("type checking") before → after |
|---|---|---|---|---|
| FRVIRFinalsSG | **80.4** (80.4 / 93.3 / 83.4) | **40.5** (40.5 / 51.6) | −50 % | 4.9–5.2 → 3.2–3.7 s |
| FRVIRSpec | **55.4** (55.4 / 72.9 / 55.4 / 70.2 / 59.1) | **52.2** (57.8 / 62.4 / 57.0 / 52.2) | −6 % | 5.4–5.9 → 5.4–5.9 s |
| FRVIRFinals | **40.0** (54.1 / 42.3 / 40.0) | **21.2** (23.4 / 21.2) | −47 % | 2.4–3.0 → 3.3–3.4 s |
| FRVIRFinalsSF | **25.6** (35.5 / 25.6 / 26.0) | **19.5** (20.5 / 19.5) | −24 % | 1.5–1.8 → 1.7–1.9 s |
| FRVIRFinals4 | **50.8** (55.9 / 50.8 / 70.8) | **11.3** (11.3 / 13.0) | −78 % | 0.5–0.6 → 0.6 s |
| **total** | **252.1** | **144.6** | **−43 %** | ≈ 14.9 → ≈ 14.2 s |

With medians instead of minima, the total is 266.7 → 157 s (−41 %). In Lake's own job times (parallel
build, `logs/G1/build0.log` → `logs/G1/build-FR.log`), `FRVIRFinalsSG` is 72 → 27 s and `FRVIRFinals4`
is 55 → 8.2 s. The two-thirds of the cut that comes from the definitions (§2.1) is paid in every
build, including the comparator's.

Code lines (`logs/org20/scripts/loc.py`): Spec 1285 → 1293, Finals 542 → 548, SF 508 → 508,
SG 1493 → 1499, Finals4 366 → 369. The extra lines are type ascriptions and two new lemmas.

**Checks.**

- `lake build FR` is green: 2,449 jobs (`logs/G1/build-FR2.log`).
- Source rule: `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive` reports 0
  findings.
- Axioms (`logs/G1/Axioms.lean`, `logs/G1/axioms.log`):
  - `acc_eq`, `Impl.implC_meets`, every `flag_fin*` (Z, Lc, Sh, Lr, E, B′, PLow, P4, Pf),
    `exec_finRS`, `lagV_eq_lagrangeWeight`, `genPhase_ctx`, `finOps4_seq3` and `rd_appT` use only
    `propext`, `Classical.choice` and `Quot.sound`;
  - `noAsk_finE`, `noAsk_finB'` and `finalsOf_seq3` use a subset of these.
- **No statement changed.** I compared every `theorem`, `def`, `abbrev` and `instance` header, up to
  `:=`, in the five modules before and after: all 464 are unchanged, and none was removed. The two new
  declarations are `rd_appT` and `rd_appT0`.
- **No definition changed.** `logs/G1/tools/defcheck.py` re-declares each edited `def` from the saved
  original as `X_old` and compares the elaborated `Expr`s. Logs: `logs/G1/defcheck1.log`, and
  `logs/G1/defcheck-final.log`.
  - All 33 edited definitions are identical once the abbreviation `FR.Reg` (`abbrev Reg := ℕ`) is
    read as `ℕ`.
  - 25 of them are byte-identical.
  - The others differ in two ways:
    - in the recursive ones, only by the `_old` name of their own recursor and matchers;
    - in `finRS`, `gFinRS`, `finPf` and `gFinPf`, by the elaborator choosing `List.map ℕ Reg` where it
      used to choose `List.map ℕ ℕ`.
  - In the combined check file `gFinRS` shows a spurious difference: the `_old` copy reuses an
    auxiliary proof that an earlier `_old` copy declared. Checked alone, it is identical
    (`logs/G1/scratch/defcheck4.lean`).

## 2. What changed

### 2.1 Definitions: failed elaborations of `.ctor` list leaves (about 100 s of the cut)

S-F4's RESULT attributed `FRVIRFinals4`'s 45 s to the `gFinX_3` `rfl`s. In fact it is the
**definitions** `gFinPf` (18.8 s), `gLcHead` (12.9 s) and `gShCore` (5.9 s). The same pattern costs
`finPf` 23 s, `lcHead` 12 s, `finSh` 5.5 s, `finP4` 3 s, `lvOps` 2.9 s, `finPLow` 2.6 s and
`uniVals` 3 s.

The cause: in `A ++ B ++ C`, the `binop%` elaborator elaborates each leaf **without an expected type**.
A leaf such as `[.const …, .keep …]` or `(List.range n).map (fun v => .getK …)` then fails, because the
dot constructor has no type. The elaborator postpones the leaf and retries it later. Each failure
costs 0.15–0.19 s here (`💥` in `trace.profiler`), and `finPf` alone had 127 of them.

The fix ascribes each such leaf, as `([.const …, …] : List Op)`, `((List.range n).map … : List Op)`,
`(… : List PtSrc)` or `(… : List Val)`. With the ascription, `finPf` elaborates in under 0.5 s. The
mechanical part was done by `logs/G1/tools/ascribe.py`.

Edited definitions:

- **SG:** `accOps`, `finPLow`, `layerOps`, `encOps`, `finP4`, `ptOps`, `zSrc`, `lcSrc`, `shSrc`,
  `pfPts`, `cellOps`, `lvOps`, `fhOps`, `finPf`.
- **Finals4:** `gFinZ`, `gLcHead`, `gShCore`, `gFinRS`, `gEncOps`, `gFinPTop`, `gCellOps`, `gLvOps`,
  `gFinPf`, `gLcSrc`, `gShSrc`, `gPfPts`, `padOps`.
- **Finals:** `dotOps`, `dotVals`, `finZ`, `lcHead`, `finSh`.
- **SF:** `finRS`.
- **Spec:** `uniVals`.

### 2.2 `flag_finPf`: omega's search over the whole register-file context (21 → 9 s)

About 30 `omega` calls of the form `x < Rk.size` ran with some 25 linear facts in context
(`sR1 … sR11`, the `x < b` bounds, the `set` variables). Each call took 0.3–2.5 s; together they took
8.8 s (`logs/G1/tools/omegas.py`, `trace.omega`). The goal was never closed by normalisation, so
omega searched.

The fix rewrites the size first, `by rw [sRk]; omega`, or `by rw [List.length_nil, Nat.add_zero, sRk];
omega` where the goal has the `+ [].length` form. After the rewrite, omega's negated goal normalises to
`False` at once. The edits are listed in `logs/G1/tools/fpf_edits.py`.

### 2.3 Register reads in one step: `rd_appT` (Finals, SF)

The `flag_fin*` proofs `simp` through `pureRun` and read registers with `rd_app`:
`rd (r ++ L.toArray) (r.size + k) = L.getD k default`. On a 60-value literal list, `List.getD_cons_succ`
then fired 2,924 times in `flag_finSh` alone (`set_option diagnostics true`).

The fix adds `rd_appT`/`rd_appT0` (`FRVIRSpec`, new):
`rd (r ++ L.toArray) (r.size + k) = (L.toArray[k]?).getD default`. Core's
`Array.reduceGetElem?` (a `dsimp` procedure on array literals) then reads entry `k` in one step. They
are used in the simp sets of:

- `flag_finZ`, `flag_finLc` (head and tail), `flag_finSh` and `flag_finLr`;
- `flag_finE` and `flag_finB'`.

`flag_finSh` drops from 10.6 to 7.8 s. The kernel pays part of it back, because it checks the
`dsimp` steps by unfolding `List.get`: `flag_finSh` goes from 1.6 to 2.35 s, and Finals' type checking
rises by about 0.9 s.

The rest of `flag_finSh`'s cost is `List.cons_append` (2,564 rewrites): `pureRun` accumulates
`L ++ [v]`, which is quadratic. That needs a different accumulation lemma, and I declined it (§3).

### 2.4 Smaller proof edits

- `noAsk_finE`, `noAsk_finB'` (SF): `by simp [finE, Op.item?]` becomes `rfl`. This takes 4.7 → 0.12 s and
  3.3 → 0.10 s, kernel included. The op lists are literals, with no computed `bif`/`if` guard, so
  S-E13's kernel trap does not apply.
- `noAsk_finPf` (SG): the final `rfl` (2.6 s of whnf through `++`/`map`) becomes
  `simp only [List.filterMap_cons, List.filterMap_nil, Op.item?, List.append_nil]`. This takes 1.7 →
  0.4 s.
- `lagV_eq_lagrangeWeight` (SG): `congr 1` spent about 4 s trying `rfl` on `∏ (l + xS j) =?=
  ∏ (l - sNodeF j)` down through `Multiset`/`Quot`. It is replaced by one `Finset.prod_congr` fact
  `hp` and `rw [hp, hp]`: 3.9 s → under 0.1 s.
- `item?_of_vals` (Spec): `simp_all [evalOp, Op.item?]` becomes `first | rfl | simp [evalOp] at h`,
  0.76 → 0.14 s.

## 3. Declined, and why

- **`FRVIRSpec`'s large proofs.** These are `genPhase_ctx` (≈ 10 s), `exec_genPhase` (≈ 5 s),
  `rounds3T_spec`, `roundsT_length`, `items_genPhase` and `exec_phaseZ` (3–4 s each). Their cost is
  broad `simp`/`simp_all` per constructor case, followed by `first | trivial | omega | exact (hm …) …`
  cascades. Reordering the cascades did not help (`logs/G1/scratch/gc*.lean`: 9.3 vs 10.2 s, which is
  noise). A real cut needs `simp only` normal forms per `Shape` case, which means rewriting each case.
  This is the largest remaining target in scope, about 20 s sequential.
- **The quadratic `List.cons_append` in the `pureRun` flag proofs.** It affects `flag_finSh` (≈ 3 s
  per kind), `flag_finLc` and `flag_finE`. The fix is a `pureRun` lemma that keeps the accumulator as
  an array or reversed list. That changes the proof architecture of every `flag_fin*`, so it is not a
  golf.
- **`flag_finPf`'s remaining 9 s.** The 13 blocks are each 0.3–0.8 s, and none dominates.
- **Remaining SG loop lemmas.** `run_lvOps` (≈ 3–7 s), `run_cellsOps`, `run_fhOps`, `run_accOps` and
  `evalOp_outs_len` cost 1.5–3 s each. Their cost is `set … : Val := .k …` steps, `simp` over
  `evalOp`, and a few omega calls. Each would gain about 1 s.
- **Mathlib linters.** `-Dlinter.all=false` saves about 1.3 s on SG. I did not pursue it: it is a
  build-option question, not a golf.
- **Exactness of 4 definitions.** `finRS`, `gFinRS`, `finPf` and `gFinPf` are equal to the originals
  only up to `Reg ≡ ℕ` (§1). Making them byte-identical would need odd inner ascriptions, such as
  `(rs1.getD p 0 : ℕ)`. Every downstream module builds (`lake build FR`), so I left them.

## 4. For the orchestrator

- The same `binop%` pattern, `[.ctor …] ++ …` and `(List.range n).map (fun _ => .ctor …) ++ …` without
  an ascription, very likely costs time in other tracks' modules too: the `FRX*` DSL programs and the
  `FRVIRTpl*` templates. A trace with `-Dtrace.profiler=true -Dtrace.profiler.threshold=50`, grepped
  for `💥`, finds them. `logs/G1/tools/ascribe.py <file> <decl>…` applies the fix, and
  `logs/G1/tools/defcheck.py` checks that the definitions are unchanged.
- R4's untracked modules are not in HEAD, so my build did not cover them. `FRSoundness4R4Acc` and
  `FRSoundness4R4FinRS` use `finRS`/`finPf`, which are unchanged up to `Reg ≡ ℕ`, so they should
  still build. They should be rebuilt against these sources before the merge.
- Measuring with `trace.profiler` inflates times by 30–50 % (SG: 52.8 s plain, 75.8 s traced). Before
  and after numbers should be taken without it.
- Tools are in `logs/G1/tools/`:
  - `measure.sh`: before/after, no trace;
  - `prof.sh`: traced per-command profile;
  - `extract.py`, `try.sh`: one theorem in a scratch file;
  - `steps.sh`, `omegas.py`, `top.sh`: trace readers.
