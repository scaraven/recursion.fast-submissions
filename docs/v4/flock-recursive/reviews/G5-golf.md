# G5 golf: kernel time in the certificate's closure

Track G5 cut kernel time without changing any statement. Worktree `recursion.fast-submissions-flock`, branch
`v4/flock-recursive` at `e840553`. Build tree `logs/fr-build-G5`; every log is in `logs/G5/`. The running record is
`stages/G5-JOURNAL.md`.

## Verdict

Runner probes (`probe/cert2`, comparator on `certified` + `submission`). There were two runs on the branch
`probe/g5-a`, which has since been deleted. Their artifacts are in `logs/G5/run-*`:

| run | CPU | change set | comparator cert | upper | KReplay cert / upper | peak cert |
|---|---|---|---|---|---|---|
| H-cert3 40884567814 | 7763 | before | 413.8 s (1.45×) | 531.8 s (1.13×) | 240.8 / 311.7 s | 8.72 GiB |
| H-cert3 40884559372 | 7763 | before | 461.7 s (1.30×) | 566.5 s (1.06×) | 260.6 / 336.7 s | 8.74 GiB |
| H-cert3 40884563974 | 9V74 | before | 401.0 s (1.50×) | 514.1 s (1.17×) | 217.3 / 272.5 s | 8.70 GiB |
| G5-a 40903282273 | 9V74 | `realign_sem` + `FRXNd4` | **344.5 s (1.74×)** | 455.6 s (1.32×) | 155.6 / 217.9 s | **4.56 GiB** |
| G5-b 40918540267 | **7763** | all, incl. `FRSkip`'s variant | **379.7 s (1.58×)** | **480.2 s (1.25×)** | 192.2 / 251.4 s | **4.54 GiB** |

- **Measured cut.**
  - Same CPU model, 9V74, partial set: −56.5 s on the comparator, −61.7 s on KReplay.
  - 7763: −34.1 s and −82.0 s raw against the two H-cert3 hosts, which themselves differed by 11 %. KReplay of the
    FR modules went 205.5 / 224.3 s → 154.8 s, i.e. **−51 to −70 s**.
  - Host speed, read off the unchanged non-FR replay (35.4 / 36.4 → 37.3 s): G5-b's host was 3–5 % slower than
    either H-cert3 host. The normalized cut is ≈ −53 to −91 s on the comparator and −59 to −73 s on KReplay.
- **Against the target.** The brief's target was a cut of at least 150 s. That is **not reached**. In the cert set
  (9V74, G5-a), after these fixes:
  - the editable FR modules hold 81 s of KReplay, of which 52.8 s is 17,560 declarations under 50 ms each;
  - `FRSoundness4*` and `FRNodeRows4*` hold 44 s;
  - non-FR declarations hold 30 s, of which `BF64.basePoly_irreducible` alone is 14.5 s.

  The comparator's time outside the replay is ≈ 111–115 s on the 9V74, unchanged. It is not driven by
  `realign_sem`'s term, which has 9,381 objects.
- **Memory halved:** 8.7 → 4.5 GiB. The H-cert3 spike was `realign_sem`'s kernel evaluation.
- **`realign_sem` separately** (it is deleted on rev44): 44.54 s → 0.03 s of KReplay (7763). Without it, the
  surviving fixes cut **≈ 45.8 s** of KReplay on the 7763. The kernel table below separates the two.

- **Root cause.** A single kernel trap accounts for the large items. In `is_def_eq`, the kernel unfolds instance
  projections (`HAdd.hAdd`, `Add.add`) before user definitions. A closed `ℕ` sum therefore reaches `Nat.add` with
  closed arguments, and `reduce_nat` whnf's both arguments to literals: it evaluates them. Any defeq step that
  relates two differently-shaped closed arithmetic forms evaluates every expensive constant inside them. Such steps
  come from:
  - a `simp` rfl-lemma unfolding of `cost`, `sizeIR`, `hUsed` or `xRows`;
  - an `rfl` closing a goal after `rw`;
  - `x + 0` against `x`.

  The fixes keep these steps off closed terms:
  - rewrite with proof-carrying lemmas (`rw`, or structural lemmas stated on variables);
  - make the expensive part an opaque variable first (`generalize`, or `obtain ⟨P, hP⟩ : ∃ P, e = P`);
  - keep the parameter (`κ`) a variable until the arithmetic is done.
- **`realign_sem` is reported separately.** The orchestrator's note says the rev44 decoder port deletes `realign`,
  `realign_sem`, `cso_realign`, `FRXOut4C` and `FRXOut4Ctrl`. The `realign_sem` fix is one line. Its gain does not
  survive on rev44.

## Changes (statements unchanged; `logs/G5/hash-diff.txt`)

| module | declaration | change | lines ± |
|---|---|---|---|
| `FRXOut4R` | `realign_sem` | the field `n` of `h0`: `by rw [vn]; rfl` → `by rw [Nat.add_zero]; exact vn` (the `rfl` made the kernel decide `D / 8 + 0 ≡ D / 8` by unfolding `D := i * 1482751` and `Nat.mul`'s recursion on the literal) | 1 / 1 |
| `FRXNd4` | `sizeIR_decF04` | chain size from `sizeIR_chainIR` + `chTab4_length` (the Fiat–Shamir table is not built); `rw [decF04, sizeIR_seq ×3, hc]`, then `decide +kernel` | +6 / −1 |
| `FRXNd4` | `decOk4_nd` (`size`) | `rw [nd, sizeIR_ndK4, sizeIR_seq ×3, …]`, `generalize` the three `sizeIR (outIR4 _)`, `omega` | +4 / −1 |
| `FRXNd4` | `nd_ne_ndNone` | `rw [nd, sizeIR_ndK4] at this`, then `Nat.add_right_cancel` / `Nat.add_eq_zero_iff` / `Nat.add_one_ne_zero` (still the size argument) | +2 / −3 |
| `FRXNd4` | new `sizeIR_seq`, `sizeIR_ndK4` | structural helpers (`rfl` on variables) | +7 |
| `FRNodeLayout4` | `aggChainLen_eq`, `aggChainLen_k3` | `rw [aggChainLen…, streamBytesOf_seq4]; decide` | 2 / 2 |
| `FRNodeLayout4` | `hUsed_eq` | rewrites only (`hUsed`, `if_pos`/`if_neg`, `segSlots`/`vslots` equations, `chainLenOf_seq4.1`, `aggChainLen_eq`), then `decide` | +6 / −2 |
| `FRNodeLayout4` | `regions_fit` | `rw [NodeKind.lBase, h2/h4/h8]` before the `simp only` | +3 / −3 |
| `FRXChainFlock` | new `map_range_getD`; `fsMsgs_items` | `(List.range l.length).map (f · (l.getD · d)) = l.zipIdx.map …`; the control decides the linear form | +9 / −1 |
| `FRXChain4` | `fsMsgs4_items` | the same through `map_range_getD` | 1 / 1 |
| `FRXOut4O` | `cso_outIR4` | `κ` stays a variable; `pfIR`, `bufSeg (trSeg4 seq4)`, `bufSeg (trBody4 seq4)` opaque; split on `κ.hasPrev` only | +12 / −7 |
| `FRNodeRows4Ext` | `xRows_length` | per conjunct `generalize hk : NodeKind.N2 = k`; unfold the rows and take lengths, then `subst hk` and the small layout numbers | +9 / −3 |

**Code lines:** 66 inserted, 28 deleted over 7 files (`git diff --stat`, after reverting `FRSkip`).

## Kernel table (KReplay, upper set; s)

Before = H-cert3 run 40884567814 (7763); after = G5-b run 40918540267 (7763, a 3–5 % slower host).

| declaration | before | after |
|---|---|---|
| `FR.X.realign_sem` (**deleted on rev44**) | 44.54 | 0.03 |
| `FR.X.X4.decOk4_nd` | 6.43 | 0.01 |
| `FR.X.X4.sizeIR_decF04._proof_1_1` (after: `_1_1 … _1_4`) | 5.52 | 0.02 + 0.41 + 0.43 + 0.43 |
| `FR.X.X4.nd_ne_ndNone` | 6.45 | 0.00 |
| `FR.Rev4.hUsed_eq` | 1.16 | 0.00 |
| `FR.Rev4.aggChainLen_eq` | 1.19 | 0.00 |
| `FR.Rev4.aggChainLen_k3` | 1.17 | 0.00 |
| `FR.Rev4.regions_fit` | 1.18 | 0.00 |
| `FR.X.cso_outIR4` | 1.45 | 0.05 |
| `FR.W4.xRows_length` | 4.51 | 0.07 |
| `FR.X.fsMsgs4_items._proof_1_1` | 5.83 | 1.25 |
| `FR.X.fsMsgs_items._proof_1_1` | 5.63 | 1.17 |
| `FR.pinnedW_eq._proof_1_1` (variant, **reverted**) | 5.32 | 4.74 |
| **total of the kept changes** (without `realign_sem`, `pinnedW_eq`) | **46.52** | **3.84** |

Per module (the same runs): `FRXOut4R` 45.58 → 1.19, `FRXNd4` 18.50 → 1.39, `FRNodeLayout4` 4.71 → 0.02,
`FRXChain4` 7.68 → 3.41, `FRXChainFlock` 6.87 → 2.59, `FRXOut4O` 3.18 → 1.99, `FRNodeRows4Ext` 4.53 → 0.09.

`FRSkip`'s `pinnedW_eq` variant measured 14.2 s → 8.0 s locally. On the runner it gave only 5.32 → 4.74 s, against a
host noise of +0.8 s on the unchanged `pinned_cert`. It needed 31 lines of copied lemmas, so it was **reverted**.
The variant is kept in `logs/G5/FRSkip-pinnedW-variant.lean`. The G5-b run still includes it.

## Local sequential profiles (`-DElab.async=false --profile`, one core; `logs/G5/prof-*`)

| module | type checking before → after | wall before → after |
|---|---|---|
| `FRXOut4R` | 80.0 → 2.59 | 121.4 → 42.5 |
| `FRXNd4` | 36.6 → 2.55 | 43.5 → 9.6 |
| `FRXChain4` | 16.7 → 6.38 | 30.7 → 17.0 |
| `FRXChainFlock` | 14.6 → 6.91 | 24.7 → 16.0 |
| `FRXOut4O` | 14.7 → 8.67 | 34.0 → 28.2 |
| `FRNodeLayout4` | 10.3 → 0.035 | 18.0 → 7.9 |
| `FRNodeRows4Ext` | 9.93 → 0.16 | 18.6 → 13.2 |
| **sum** | **182.8 → 27.3** | |

Elaboration did not rise. `simp` time in `FRXOut4R` fell from 23.7 s to 20.5 s. The other elaboration figures moved
by less than 0.3 s.

## Declined, and why

- **`FRSoundness4Pos.rangesOK4_eq`** (2.85 s). Rewriting `fsRanges4` and `fsRnd4` to their literals first made it
  slower: 9.0 s → 12.5–14.2 s here (`exp10.lean`). The cost is `fsItems4[k]?` over the `itemsOf seq4` filter.
- **The other `FRSoundness4*` checks** (`phOf_check`, `rounds_check`, `p1_sq_check`, `tailCls_check`,
  `front_check`, …; 0.5–2.4 s each) are `decide +kernel` evaluations of `seq4`'s layout. The same holds for
  `streamBytesOf_seq4`, `itemsOf_seq4_length`, `cso_pfIR`, `trOk4_seq4`, `qlen_mod` and `okSeg_pf` (0.6–1.1 s
  each). These are genuine computations over 8,905 items and 482 positions. A cut would need the layout as shipped
  literals or a cheaper evaluation order.
- **`FRSkip.pinnedW_eq`**: the shared-table variant was reverted (see the kernel table).
- **`FRSkip.pinned_cert`** (3.1 s): 128 rows × 128 bit tests and `F.add`s. The work is inherent at the kernel's
  per-step cost.
- **`BF64.basePoly_irreducible`** (14.5 s) is core-owned.
- **The tail.** In the cert set, 17,560 editable FR declarations take under 50 ms each, 52.8 s in all on the 9V74.
  No single pattern dominates.
- **The comparator outside the replay** (≈ 111–115 s on a 9V74) is unchanged. The comparator's memory timeline
  (`comparator-cert-ps.log`) shows the parse ending ≈ 25 s after the second export. The rest is its own replay,
  ≈ 1.5× KReplay's figure. KReplay cuts therefore carry over ≈ 1:1 (G5-a: −61.7 s KReplay, −56.5 s comparator).
  `realign_sem`'s term is small (9,381 objects). The memory spike was its kernel evaluation.
