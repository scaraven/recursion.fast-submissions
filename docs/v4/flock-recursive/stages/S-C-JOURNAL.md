# S-C (track L-piop): journal

Running notes for a successor. Build tree `logs/fr-build-piop/` (`gen.sh` copied from
`logs/fr-build/`; `b.sh` builds the given targets and prints errors only).

## 2026-10-27

- Read TRACK-RULES, BLUEPRINT rev. 2 (§2.3, §5.2, §7, §9, A), BP-E Round 2 (R2-M1, R2-M3 (a)),
  BP-C (M2; Round 2 R2-M4, R2-m1, R2-m2), S-A RESULT, I-reuse §2.3–2.4.
- `FRMLE`, `FRSumcheck`, `FRRingSwitch`, `FRMLEControls`: copied from spartan-srom at `783328c`
  (sed: namespace `SpartanSrom` → `FR`, imports). `FRMLE` gains `mle_sub`, `mle_sum`, `fixLow`,
  `mle_fixLow`. `FRSumcheck` gains `batch_pow_bad_le` (k+1 claims, ≤ k bad), `batch2_bad_le`
  (≤ 1), `pair_bad_le` (two coordinates per squeeze answer, BLUEPRINT A.2).
- Rev. 3 (0d513c9) then rev. 3.1 (c38bda1) arrived mid-stage. `FRShift` was written three times:
  (1) range-restricted, all-multilinear; (2) rev. 3 with skip slices + univariate (a generic
  `sliced` framework in `FRSumcheck`, now removed as dead code); (3) **rev. 3.1 / P1-D5**:
  `ChainLinks` with both endpoints, `chainD`/`chainD0`, `chainLinks_iff`, `shift_sound`,
  `shift_coord_le`, `shift_kappa_le`, block rounds `shift2Expr` (deg 2) with `shift_trueSum`
  (`= target + D̃(θ,τ) + κ D̃₀(θ)`, proved by `linear_combination … * two_eq_zero`), `shW_mle`,
  `shift_final`, collapse rounds `collapse_mle`, `slotW_mle_aligned`, `collapse_final`, and
  `chainLinks_batch` (two chains by `1, y`, `bits_y_inj` by `decide` on 16 F cases).
- `FRSumcheck`: `innerExpr`, `prod_trueSum`, `tbl_ofFn`, `bindT` moved in from SR's
  `SoundnessSpartan`; `uni_bad_le` (Z2).
- `FRRingSwitch`: `ring_inj_basis` (any GF(2)-basis, Moore matrix → linearised polynomial vanishing
  on all `2^n` subset sums, `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`), `bitF`, `bitBasis`
  (A.7's pack), `bitBasis_indep`, `ring_inj_F`, `unpack_boolean`, `pack_unpack`, `rsDoom` chain
  generalised from `x^i` to `b i`, `rs_start_F`.
- Pitfalls: `split_ifs` after unfolding `dbl` leaves `ite`s whose `Decidable` instance mentions
  `(dbl u b).val` — rewrite conditions with `if_congr` instead; `ring` silently degrades to
  `ring_nf` (use `ring1` inside `first`); `λ` is a keyword (use `l`).
- Rev. 3.2 (2709159, frozen): `FRSpartan` written against it: block zerocheck with the weight
  `ŵ = eq(r,·)·Sel` (degree 3), `A = I ⊗ A₀`, public target `E`; `prefixP` (prefix sums of
  product weights, `O(n²)`), `selWeight_eq` (over `Sel`'s intervals), `selWeight_split`;
  `bzPoly` (degree ≤ 126 via `skipExt`), `bz_skip_le` (Z2, 127), `bz_trueSum`, `bz_final`;
  lincheck `linA`/`linM`/`zfold`, `lin_trueSum`, `lin_final` (claim `ẑ(r_k, r_blk)`);
  `quirky_claim_split`. SR's sparse Spartan (`Sat`, `zc_*`, `outer*`, `inner*`) kept for Lr/E.
  `FRShift`'s `ltMle`/`rangeMle` removed (`prefixP` subsumes them).
- `FRSkip`: generic interpolation (leanerVM, on functions), `ζ`, `gW`, `skipNode` (+ injectivity
  by additivity and a 128-case `decide`), `lagrangeS`, `skip_bad_le`, `zcMsg`, `zc_skip_bad_le`,
  `zc_skip_complete`, `skipExt` (+ `_natDegree`, `_node`, `_eval`); `PinnedIndep`,
  `pinned_sound`; A.1's two-level set with the shipped inverse (`probe/fr-piop/gen_skip.py two`,
  rendered by `render.py` from `FRSkip.template`): `pinnedRho_spec`, `pinnedW_eq` (254 F products
  in the kernel, 9.8 s), `pinned_cert` (`rowGo` walks the inverse once per row: 7.1 s; with
  `List.getD` per bit it was 14 s; a Nat-level check was 9.7 s), `pinned_rank`;
  `not_pinnedIndep_of_base` (pigeonhole, 2^128 subsets into 2^64 words) and `rev2Rho_not_pinned`.
  The one-level set `y^(2^j)` also has rank 128 (`gen_skip.py one` inverts it); not kernel-checked
  since rev. 3.1 pins the two-level set.
- `FRSumcheck`: `seq_bad_le` (sequential union bound with a doomed-prefix escape count per
  coordinate), `pair_bad_le` generalised to `α × β`.
- `FRRingSwitch`: `rs_column`, `ml_claim_split`, `rsJDoom`, `rsJ_escape_le`, `rs1_joint`
  (`≤ (7 + J − 1)·|F|^7` of `F^8`).
- Controls appended to `FRMLEControls` (shift KAT, chain links ±, prefix sums ±, `ŵ ≠ eq·Sẽl`,
  interpolation ± over `ZMod 7` with `decide +kernel`, the pack bit 64, `GF2Indep` negative,
  `ring_inj_F` instance, `BHolds` ± and the `Sel` control).
- Measurements: `logs/S-C/profile-*.log`, `logs/S-C/build.log` (57.9 s for the 7 modules),
  `logs/S-C/axioms.log` (51 declarations, ≤ the three axioms). Source rule: 0 findings.
