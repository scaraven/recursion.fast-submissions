# G5 journal: kernel time in the certificate's closure

Brief: cut the comparator's kernel time (H-cert3: `certified` 461.7 s on a 7763 vs `kernel_s` 600), target ≥ 150 s,
without changing any statement. Worktree `recursion.fast-submissions-flock`, branch `v4/flock-recursive` at `e840553`.
Build tree `logs/fr-build-G5` (copy of `logs/fr-build-orch`). Logs in `logs/G5/`.

1. **Baseline.** `lake build FR Solution FRSubmission4Fin` up to date in the copied tree (2,623 jobs). H-cert3's
   KReplay (cert set, 7763): total 240.8 s, FR modules 205.5 s; `realign_sem` 44.8 s, `decOk4_nd` 6.5 s,
   `sizeIR_decF04._proof_1_1` 5.6 s, `pinnedW_eq` 5.5 s, `pinned_cert` 3.2 s, `xRows_length` 4.5 s (`FRNodeRows4Ext`:
   not mine to edit), then a long tail under 3.1 s.
2. **`FRXOut4R` sequential profile** (`-DElab.async=false --profile`, one core): type checking 77.7 s, simp 23.7 s,
   wall 121 s (`prof-FRXOut4R-before.log`). `realign_sem`'s proof term has only **9,381 objects**: the cost is a
   kernel defeq trap, not term size.
3. **Tool `logs/G5/tool/KProf.lean` (+ `kprof.sh MOD DECL`)**: walks a proof term's spine; type-checks every side
   component alone (closed over its context, let-bound variables kept as `let`) and every application node with
   its components replaced by variables (the node's own defeq checks); prints the checks over 0.05 s.
4. **`FRXNd4`: the trap.** Tool on `nd_ne_ndNone`/`decOk4_nd`: each cost sits in one `congrArg` node of a `simp only
   [nd, ndK4, sizeIR, …]` proof whose proof argument has type `sizeIR (decF04 N2) + sizeIR (outIR4 N2) + 1 = …` while the
   node expects `sizeIR (.seq (decF04 N2) (outIR4 N2))`: simp used `sizeIR`'s equation lemmas **definitionally** (rfl
   lemmas leave no proof), so the kernel must decide `sizeIR (.seq a b) ≡ sizeIR a + sizeIR b + 1` on **closed**
   terms. On closed `Nat.add` terms the kernel's `reduce_nat` whnf's both arguments to literals, i.e. evaluates the
   57,067-statement programs. Micro-experiments (`tool/exp1.lean`): the same `congrArg` on a hypothesis of the
   exact form costs 0.2 ms. Components (`tool/exp2.lean`, `exp3.lean`): `sizeIR (decF04 κ)` = 294 (`idxIR4`) + 570
   (`readK4`) + 18,943 (`chainIR`, of which 10 · 1,828 table words) + 37,257 (`decLevels4`) + 3; the kernel
   evaluation is **10.4 s for the chain** (it builds `chTab4 seq4 nRep4`, the Fiat–Shamir table) and 0.72 s for
   `decLevels4`; with `sizeIR_chainIR` + `chTab4_length` the chain's size costs nothing.
5. **`FRXNd4` fix** (statements unchanged): new helpers `sizeIR_seq` and `sizeIR_ndK4` (structural, `rfl` on
   variables); `sizeIR_decF04` = chain size via `sizeIR_chainIR`/`chTab4_length`, then `rw [decF04, sizeIR_seq ×3, hc]`
   and `decide +kernel` on the rest; `decOk4_nd.size` by `rw [nd, sizeIR_ndK4, sizeIR_seq ×3, z2, z4, z8, k]`, the
   three `sizeIR (outIR4 _)` generalized, `omega`; `nd_ne_ndNone` by `rw [nd, sizeIR_ndK4] at this` and
   `Nat.add_right_cancel`/`Nat.add_eq_zero_iff`/`Nat.add_one_ne_zero` (two `omega`/`Nat.succ.inj` attempts made the
   elaborator recurse into the closed sizes: max recursion). Sequential profile: **type checking 36.6 s → 2.55 s**
   (11.0 + 12.6 + 12.7 s → 3 × 0.77 s), wall 43.5 s → 9.6 s (`prof-FRXNd4-{before,after1}.log`).
6. **`realign_sem`: the trap** (tool, `kprof-realign.log`, 23 min with the tool's re-checks): all the time is in the
   `let h0 : RlInv … (D % 8) (D / 8) 0 …` value, in its field `n : rd … qN = toWord (D / 8 + 0)`, proved
   `by rw [vn]; rfl` from `vn : … = toWord (D / 8)`. The closing `rfl` asks the kernel `D / 8 + 0 ≡ D / 8` with
   `D := i * (N4c.segB - 1)` a `set` (let) variable; the kernel unfolds the right side first (`Nat.div`, then
   `D`'s value `i * 1482751`) and `Nat.mul`'s recursion on the literal `1482751` — the same shape as S-H4's
   `kStep_sem` trap (`x + 0` against `x`). Fix: `by rw [Nat.add_zero]; exact vn` (the field's statement is
   unchanged). Sequential profile of `FRXOut4R`: **type checking 80.0 s → 2.59 s**, wall 121 s → 42 s, simp 23.7 s →
   20.5 s (`prof-FRXOut4R-{before,after1}.log`).
7. **Build** `lake build FR Solution FRSubmission4Fin`: green, 2,623 jobs (`build1.log`). **Statement hashes**
   (`tool/StmtHash.lean`, 11 modules, before = `logs/fr-build-orch` at HEAD, after = this tree): only
   `decOk4_nd._proof_1_4`, `sizeIR_decF04._proof_1_*`, `nd_ne_ndNone._proof_1_2` (auxiliary proofs) differ, plus the
   new `sizeIR_seq`, `sizeIR_ndK4` (`hash-{before,after}.txt`).
8. **Probe `probe/g5-a`** (commit `0dc2cb5` = HEAD + the two modules + `probe.conf = cert2`, made with a temporary
   index; no commit on `v4/flock-recursive`): run 40903282273.
9. **`FRNodeLayout4`** (cert: `hUsed_eq` 1.23 s, `aggChainLen_eq` 1.22 s, `regions_fit` 1.18 s): the same family. A
   simp/`rfl` step compares closed `ℕ` sums that contain `streamBytesOf seq4` (via `chainLenOf`, `aggChainLen`). When
   the two sides differ in shape (an `ite` against a sum), the kernel unfolds `HAdd` down to `Nat.add`, and
   `reduce_nat` evaluates the stream layout (≈ 1.2 s on the 7763, 2.5 s here). Variants (`tool/exp4.lean`,
   `G5.whole`): `aggChainLen_eq` by `rw [aggChainLen, aggChainLen, streamBytesOf_seq4]; decide` costs 0.001 s
   (was 2.55 s); `regions_fit` with `rw [NodeKind.lBase, h…]` instead of `simp only [… h]` costs 0.004 s (was 2.6 s);
   `hUsed_eq`: `rfl`-stated unfoldings (`N2.hUsed = chainLenOf seq4 + aggChainLen 2 + …`) still cost 3 s each.
10. **`FRNodeLayout4` fix**: `aggChainLen_eq`, `aggChainLen_k3` by `rw [aggChainLen…, streamBytesOf_seq4]; decide`;
    `hUsed_eq` by rewrites only (`NodeKind.hUsed` ×3, `if_pos`/`if_neg` on `hasPrev`, `segSlots`/`vslots` by `rfl`
    equations, `chainLenOf_seq4.1`, `aggChainLen_eq`), then `decide` on literals; `regions_fit` with
    `rw [NodeKind.lBase, h2|h4|h8]` before the `simp only` of the small definitions. Profile: **type checking 10.3 s →
    0.035 s** (`prof-FRNodeLayout4-{before,after}.log`).
11. **`FRXChain4`/`FRXChainFlock`** (upper set: `fsMsgs4_items` 5.8 s, `fsMsgs_items` 5.6 s): `decide +kernel` on
    `(List.range n).map (fun p => f p (l.getD p none))` walks the list from the head at every `p` (quadratic, and
    `fsMsgs` is a layout computation). New `map_range_getD` (`FRXChainFlock`): that map is `l.zipIdx.map …`; the
    controls now `rw [← fsMsgs_length, map_range_getD]` (resp. `fsMsgs4_length`) and decide the linear form. Profiles:
    `FRXChainFlock` 14.6 s → 6.9 s, `FRXChain4` 16.7 s → 6.4 s of type checking; the controls' aux proofs 12.25 s →
    3.1 s and ≈ 12 s → 2.5 s (`modtop-t1`, `exp5.lean`).
12. **Tool `G5.modTop`** (`tool/modtop.sh TAG MOD…`): re-checks every declaration of the modules in the kernel (one
    `import FR`), prints each module's total and the declarations over 0.1 s.
13. **`FRSkip`**: a kernel `F` product costs ≈ 17 ms (`exp6.lean`); `pinnedW_eq` (14.2 s here) evaluates the 128
    entries' 7-factor products without sharing: `eqTable`'s `t[u/2]'h` carries a different proof `h` per `u`, so the
    kernel's whnf cache never hits. Through `eqTable_toList_cons` (`FRVIRTplTab`: the table as nested `flatMap`s)
    it is 8.0 s (`exp7.lean`). `pinned_cert` (8.6 s here): 128 rows × 128 bit tests and `F.add`s, inherent.
14. **`FRSkip` fix**: `pinnedW_eq` now rewrites `List.ofFn pinnedRho` to its seven entries and the table through the
    new `eqTable_cons_toList` (with `getElem_flatMap_two`; copies of `FRVIRTplTab`'s `eqTable_toList_cons` and
    `getElem_flatMap_pair`, which `FRSkip` does not import), then `decide +kernel`. Profile: type checking 19.6 s →
    15.8 s (`prof-FRSkip-{before,after}.log`).
15. **Probe `g5-a` result** (run 40903282273; the runner was an **EPYC 9V74**, not a 7763; artifacts in
    `logs/G5/run-40903282273/`). Against H-cert3's 9V74 run (40884563974), same CPU model:
    - comparator `certified`: **401.0 → 344.5 s** (−56.5 s); without export 1: 377 → 321 s;
    - comparator upper: 514.1 → 455.6 s (−58.5 s);
    - KReplay cert 217.3 → 155.6 s (−61.7 s), upper 272.5 → 217.9 s (−54.6 s);
    - **peak memory 8.70 → 4.56 GiB** (cert), 8.87 → 4.77 GiB (upper): the 8.5 GiB spike in H-cert3's
      `comparator-cert-ps.log` was `realign_sem`'s kernel check (the `Nat.mul` unfolding), not its term size;
    - the comparator's time outside the replay is unchanged: after the last export 328 s − KReplay 217 s = 111 s
      before, 271 − 156 = 115 s now. The H-cert3 hypothesis (that `realign_sem`'s proof term drives it) does not
      hold: the term has 9,381 objects. `tool/Sizes.lean` (`sizes.log`): the FR declarations hold 21.6 M expression
      objects in 40,895 declarations, the largest 68 k (`flag_gFinSh`); no single term dominates.
16. **Root cause, general form.** In `is_def_eq` the kernel unfolds instance projections (`HAdd.hAdd`, `Add.add`,
    abbreviation-like) before user definitions; a closed `ℕ` sum thus reaches `Nat.add` with closed arguments, and
    `reduce_nat` whnf's both arguments to literals, i.e. evaluates them. Every defeq step that relates two closed
    arithmetic forms of different shape (a `simp` rfl-lemma unfolding — `cost`, `sizeIR`, a layout definition —, an
    `rfl` after `rw`, an `x + 0` against `x`) evaluates whatever expensive constants they contain. The fixes keep such
    steps off closed terms: rewrite with proof-carrying lemmas (`rw`, structural lemmas stated on variables), make
    the expensive part a variable first (`generalize`, `obtain ⟨P, hP⟩ : ∃ P, e = P`), or keep the parameter (`κ`)
    a variable until the arithmetic is done.
17. **`FRXOut4O.cso_outIR4`** (cert 1.43 s on the 7763): the same trap through `simp [cost, outs, sizeIR, …]` on the
    closed programs. New proof keeps `κ` a variable (component facts for `σ := N4c.aggChild κ a`, `hm :
    (toWord κ.maxK).toNat ≤ 4`), makes `pfIR`, `bufSeg (trSeg4 seq4)`, `bufSeg (trBody4 seq4)` opaque
    (`obtain ⟨PF, hF⟩ : ∃ P, pfIR = P`), unfolds the programs, then splits on `κ.hasPrev` only. Kernel 3.08 s →
    0.105 s (`exp8.lean`, `G5.whole`); module type checking 14.7 s → 8.67 s (`prof-FRXOut4O-*`). Note: it uses
    `cso_realign`, which rev44 deletes; the port must drop `r1 r2 r3` and the realign terms.
18. **Orchestrator note (mid-track):** on rev44 the decoder port deletes `realign`/`realign_sem`, `cso_realign`,
    `FRXOut4C`, `FRXOut4Ctrl`; targets should be those that survive on rev44 (`FRSoundness4*`, `FRNodeRows4*`,
    `FRVIR*`). The `realign_sem` fix (item 6) was already done (one line); its gain is reported separately.
19. **`FRNodeRows4Ext.xRows_length`** (cert 4.47 s on the 7763, 4.33 s on the 9V74): `simp [xRows, wotsRows, …]` on
    the closed kinds made the kernel evaluate the ≈ 8,000-row lists. New proof generalizes the kind
    (`generalize hk : NodeKind.N2 = k`, per conjunct), unfolds the rows and takes lengths (`List.length_*`), then
    `subst hk` and finishes on the small layout numbers. Kernel 11.8 s → 0.14 s (`exp9.lean`); module type checking
    9.93 s → 0.16 s (`prof-FRNodeRows4Ext-*`).
20. **`FRSoundness4Pos.rangesOK4_eq`** (2.85 s): rewriting `fsRanges4` (and `fsRnd4`) to its literal before
    `decide +kernel` made it slower (9.0 s → 14.2 s / 12.5 s here, `exp10.lean`): the cost is `fsItems4[k]?`, i.e.
    the filter over `itemsOf seq4`. Left unchanged. The remaining `FRSoundness4*` checks (`phOf_check`,
    `rounds_check`, `p1_sq_check`, …) are `decide +kernel` evaluations of the `seq4` layout, 0.5–2.4 s each.
21. **Final checks.** `lake build FR Solution FRSubmission4Fin` green, 2,623 jobs (`build3.log`); axioms
    (`axioms.log`): `certified`, `certificate_sub4F` and every touched theorem within `propext`, `Classical.choice`,
    `Quot.sound`; source rule 398 files, 0 findings (`source-rule.log`); statement hashes over 12 modules
    (`hash-diff.txt`): only auxiliary `_proof_*`/`eq_*`/`splitter` declarations and the new helpers differ.
22. **Probe `g5-b`** (commit `00ba730` on `probe/g5-a`, all eight modules): run 40918540267.
23. **Probe `g5-b` result** (run 40918540267, **EPYC 7763**, all changes incl. the `FRSkip` variant;
    `logs/G5/run-40918540267/`): comparator cert **379.7 s** (1.58×; H-cert3 7763 hosts 413.8 / 461.7 s), upper
    480.2 s (1.25×; 531.8 / 566.5 s), KReplay cert 192.2 s (FR 154.8 s; before 205.5 / 224.3 s), upper 251.4 s; peak
    4.54 GiB. This host's unchanged non-FR replay is 37.3 s vs 35.4 / 36.4 s (3–5 % slower). Per declaration
    (`table.py`): the kept changes 46.52 s → 3.84 s, `realign_sem` 44.54 s → 0.03 s, `pinnedW_eq` 5.32 → 4.74 s
    (with `pinned_cert`, unchanged, at +0.8 s of host noise).
24. **`FRSkip` reverted**: the runner gain of the `pinnedW_eq` variant is within noise and it costs 31 lines of copied
    lemmas; the variant is kept in `logs/G5/FRSkip-pinnedW-variant.lean`. Rebuilt (`build4.log`). Probe branch
    `probe/g5-a` deleted.
