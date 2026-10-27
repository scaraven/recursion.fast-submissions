# S-D (track L-pcs): journal

Stage S-D of `flock-recursive` (BLUEPRINT §9: `mca_ud_line` over K with `C_mca` fixed and
`≤ 2^60`; `fold_preserves`, `interp_F`, `positions_bad_le`, `cap_binding`; `FRRS`'s triangularity
and tensor identity). Build tree `logs/fr-build-pcs` (copy of `logs/fr-build/gen.sh`), logs
under `logs/S-D/`.

## 2026-10-27

- Read TRACK-RULES, BLUEPRINT §2.1–2.2, §5.2–5.6, §7, §9, App. A, §10; BP-crypto-review M4, M8,
  Round 2 (M8 closed; R2-M3: repeated positions are opened again, which `positions_bad_le`'s
  model (indices with repetition) already assumes).
- **Probe of the exact statement first** (`logs/S-D/mca_exact_probe.py`, log
  `mca_exact_probe.log`): K = GF(256), D ⊂ GF(16), exhaustive over z, the line
  `u₀ + z(u₁ − u₀)`, the conclusion "∃ v₀ v₁ ∈ C with joint agreement set = agreeSet(u_z, w)"
  checked literally. Random, structured (codeword + errors) and adversarial (errors on a line)
  words, 25 trials each, 7 parameter sets up to n = 12, e at the full UD radius. Worst bad count
  `e + 1`; no counterexample.
- **A shorter proof than §5.3's plan.** The plan's step 2 (rank over `K(Z)`, every maximal minor
  vanishes) needs "many close z" and a division in `K(Z)[X]`. Instead, choose the error-locator
  degree `a := n − k − e` (≥ e) and Z-degree `e`: the homogeneous system
  `N(x_j, Z) = E(x_j, Z)(u₀_j + Z(u₁_j − u₀_j))` has `(a+1)(e+1) + (n−e)(e+2)` unknowns against
  `n(e+2)` equations, so a nonzero solution exists **unconditionally** (GS-style counting).
  `E ≠ 0`; `E(x_j, Z) ≢ 0` at `≥ k + e` positions; on `k` of them `J`, for `z` off `≤ k e` roots,
  Berlekamp–Welch uniqueness (`deg N < a + k = n − e`) forces the close codeword to agree with
  `u_z` on `J`, so it is the interpolated line `v₀ + z(v₁ − v₀)`. The `≤ n` positions'
  affine roots finish the mutual part. No division, no rational functions, no threshold.
  Result: `C_mca(n, k, e) = k e + n` (2^37 + 2^20 at level 0, m = 32), far below `2^60`.
- `FRRS` (generic RS code, `agreeSet`, `rs_eq_of_agree`, `rs_interp`, `rs_minDist`),
  `FRProximityBW` (`close_unique`, `bw_unique`), `FRProximityLine` (`mca_ud_line_cover`,
  `mca_ud_line`) compile; `#print axioms`: the three standard ones.
- `FRRS` novel basis: `subW`/`normW`/`novelX` over a generic domain `pt` injective on
  `[0, 2^N)`; degree exactly `x` (non-monic `Ŵ`, so `natDegree_mul` with nonzero factors instead
  of spartan-srom's monic argument); block-triangularity is immediate from the definition
  (`Ŵ_v` vanishes on `pt [0, 2^v)`); the tensor identity is proved over any commutative ring for
  arbitrary values `w_v`, then specialised. `W_linear` needs char 2 and
  `pt (a xor b) = pt a + pt b`: the recursion `W_{v+1}(y) = W_v(y)(W_v(y) − W_v(pt 2^v))` from
  `2^v + a = 2^v xor a`, and additivity by induction (the cross term is `2 W(y) W(z) = 0`).
- `Enc` and `C_K = RS[K, D, k]` (`encCode_eq_rsCode`, adapting spartan-srom's `exists_encPoly`
  to leading coefficients instead of monic); `D j = F.ofB64 ⟨UInt64.ofNat j⟩`, `D_xor` by
  `Nat.xor_mod_two_pow`, `D_injOn` below `2^64`.
- `FRProximityFold`: `fold_preserves` as an iff for one round with an arbitrary pairing (the bit
  order is S-0's), `fold_lift`, `interp_F` (generic and on `D`), `positions_bad_le` via
  `Fintype.piFinset`.
- Controls: `decide` fails on `ℚ` (Rat operations do not reduce), so the toy codes are over
  `ZMod 5`. The `2e = d` negative is for `close_unique` (§5.6); a probe at `2e = d`
  (`mca_beyond_ud_probe.log`) found no violation of the `k e + n` bound at `n = 4`, so no
  negative for `mca_ud_line` itself is claimed.
- S-0's `FRTranscriptDefs` appeared mid-stage (blueprint revision 3.1 committed, `c38bda1`);
  `FRMerkle` stays parametric (`MerkleEnc`), with a toy encoding proving the laws satisfiable and
  the collision negative control. Noted the window-alignment question for `colL_prefix`.
- `FRRSEval`: table rows by the LCH recursion on values (`normW_succ`), `Ŵ_v(pt j)` by bits,
  `encTwin`, `tensorTwin`, proved equal; instance `D`, `N = 20`.
- TRACK-RULES changed mid-stage (sequential elaboration for profiles): profiles re-run with
  `-DElab.async=false` on one core.
- Final: 6 modules, 1,246 code lines; build 20 s; kernel ≈ 4.2 s total; 46 declarations with the
  three axioms; source rule clean. RESULT written.

## Fix pass and S-D2 (2026-10-27, from golfed `1705d97`)

- m2: `fold_preserves_fails_at_bad` (reviewer's probe), `D_not_injOn_succ`; `novel_D_ok` → remark.
- m5: `logNMax`/`nMax` in `FRRS` (FRTranscriptDefs imports FRRS, so the constant lives here);
  D-instances re-stated with `nMax`; GF(5) `Fact` as a local instance; the A.5 sentence demoted to a
  remark.
- m3: S-0's laws instantiate `MerkleEnc` exactly (scratch `frEnc` elaborates); level byte checked.
- S-D2: the inverse additive NTT on cosets (`coeffsAt`, `coeffsAt_spec`) instead of the half-split
  back-substitution: the coset offset `s` with `pt (s + j) = pt s + pt j` makes the induction
  close; `coeffsOfValues`, `coeffs_spec`, `coeffs_unique`, `interpF` (= `Lagrange.interpolate`),
  `decode_row(_D)`, `encF`. RESULT "## Fix pass" appended.
