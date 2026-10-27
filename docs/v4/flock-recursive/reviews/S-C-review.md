# S-C (L-piop core): adversarial review

Reviewed: `stages/S-C-RESULT.md` and the modules `FRMLE`, `FRMLEControls`, `FRSumcheck`,
`FRShift`, `FRRingSwitch`, `FRSkip`, `FRSpartan` (committed in `f7c51e1`), plus
`probe/fr-piop/`. Spec: BLUEPRINT revision 3.3 (§2.3, §5.2, A.1, A.6, fix passes 3–4,
stage-review changes 1). S-C was written against revision 3.2.

## Evidence

| Check | Result | Log |
|---|---|---|
| Build of the seven modules in a fresh tree (`logs/S-C-review/`, copy of `gen.sh`, `timeout 1500`) | green; sources unchanged before and after (`sources.sha256`) | `logs/S-C-review/build.log` |
| Warnings | about 40 in the seven modules: deprecations (`if_pos`/`if_neg`/`dif_pos`/`if_true`, `Fin.coe_*`), one unused simp argument, one unused variable (`FRSpartan` l. 338) | same |
| Hygiene | no `sorry`, `native_decide`, `set_option`; `decide +kernel` only for the field and pinned-point certificates | — |
| Axioms | the RESULT's `logs/S-C/axioms.log` (51 declarations, the standard three). I did not re-run it; the build shows no `sorry` | — |

## The rows of §5.2 against the lemmas

Every row the stage owns has a counting lemma with exactly the table's count:
- **Z1:** `zerocheck_bad_le` / `seq_bad_le` / `pair_bad_le` for 17 (19 at `m = 32`); `pinned_sound`
  for the 7 pinned coordinates, at 0.
- **Z2:** `bz_skip_le`, 127.
- **Z3:** `round_escape_le`, 3 per round.
- **L1 / L2:** `lin_alpha_le`, 1; then 2 per round.
- **S1 / S2:** `shift_coord_le`, `shift_kappa_le`, 27; `shift_round_le`, 2.
- **Lr, E:** spartan-srom's.
- **RS1:** `rs1_joint`, `(7 + J − 1)·|F|^7` of `F^8`, i.e. `10/2^128` at `J = 4`.
- **B′:** `batch_pow_bad_le`, `J_f − 1`.

Each is a `card (filter …) ≤ c` over `F`, or over `F^k` for multi-coordinate phases. That is the
form `KState.step` consumes through the fiber counts (`card_chF_fiber`) and `extCount_split` for
phases spread over several squeezes.

**`pinned_rank` is genuinely checked.** Every link is kernel-verified:
- `pinnedG_spec` ties `g` to A.1's definition (`ζ, ζ², ζ⁴, y, y², y⁴, y⁸`);
- `pinnedRho_spec` fixes `ρ(1 + g) = g`;
- `pinnedW_eq` evaluates the 128 products from `ρ`;
- `pinned_cert` shows each row times `Minv` equals a distinct basis vector, by a computable fold
  that `rowMulC_eq` proves equal to the specification;
- `rowMulHom` is additive, so a zero subset sum maps to a zero sum of distinct basis vectors, i.e.
  the empty set.

The shipped inverse is used, not trusted. `rev2Rho_not_pinned` / `not_pinnedIndep_of_base` are a
real negative.

**`ring_inj_basis`** is the right general statement (any `GF(2)`-independent packing basis of a
`2^n` field). `ring_inj_F` instantiates A.7's pack, and `bitBasis_neg` controls the limb order.

## Majors

### S-C-M1. Revision 3.3's per-kind lincheck is not an identity, so `FRSpartan`'s lincheck cannot be moved to it as written (owner: blueprint §2.3 step 3, then `FRSpartan`)

**The blueprint's formula.** §2.3 step 3 (3.3) checks
`Σ_kind Ĩnd_kind(r′_blk)·Â₀^kind(r_row, r_k)` by one walk with
`rowW′[k] = rowW[k]·Σ_{kind ∌ k} Ĩnd_kind(r′_blk)`, and ends with the single claim
`ẑ(r′_blk, r_k)`.

**The true value.** For `A = Σ_kind Ind_kind ⊗ A₀^kind`, the true `â` is
`Σ_t eq(r′,t) Σ_k rowW(k)·[k ∉ pinned(kind(t))]·(A₀ z_t)(k)`. The indicator sits **inside** the
block sum, and `MLE(Ind·g)(r′) ≠ Ĩnd(r′)·ĝ(r′)`.

**Counterexample.** One row and one column with `A₀ = 1`, two blocks, the row pinned in block 0's
kind and free in block 1's:
- true `â = r′·z₁`;
- the blueprint's final value is `Ĩnd_Y(r′)·ẑ(r′) = r′((1−r′)z₀ + r′z₁)`.

They differ for `z₀ = 0` and any `r′ ∉ {0,1}`. So the honest prover's `â` (the zerocheck's quirky
claim) fails the lincheck: completeness breaks for the node. The leaf, one kind with `Ind = 1`,
is unaffected. `lin_trueSum` (`I ⊗ A₀`) is correct for 3.2 and cannot be restated to 3.3's
formula.

**Fix (keeps one walk and 14 rounds).**
- Run the lincheck on per-kind folded columns `zfold_kind(j) = Σ_t eq(r′,t)·Ind_kind(t)·z(j,t)`.
  The true sum is `Σ_kind Σ_j M_kind(j)·zfold_kind(j)`, where `M_kind(j) = Σ_k rowW(k)[k ∉
  pinned(kind)](A₀ + αB₀)(k,j)`.
- After the 14 rounds the prover claims `v_kind = zfold_kind(r_k)`. The verifier checks the final
  value by **one** walk with `rowW′[k] = rowW[k]·Σ_{kind ∌ k} v_kind`.
- It hands the `v_kind` claims to ring switching, as weighted claims on `z` with public weights
  `W_kind(t) = eq(r′,t)·Ind_kind(t)`. `W̃_kind` at the RS point is a tensor prefix sum over the
  kind's intervals, like `ŵ`.
- `J_z` grows by up to 7, and RS1 becomes `(7 + J_z − 1)/2^128 ≤ 17/2^128`, still far below
  `εR`.
- In Lean: `lin_trueSum_kinds` and `lin_final_kinds` (per-kind `M`, `zfold`), with the
  walk-adjustment identity `Σ_kind v_kind·M̃_kind(r_k) = walkMasked(…)`.
- Alternative: a full-column lincheck (32 rounds), at more prover cost.

### S-C-M2. Exactly what `FRSpartan`/`FRSkip` must change for revision 3.3 (owner: S-C, with S-0)

1. **Z3's summand (3.3: final value `ŵ(r′)(â b̂ − ẑ) − Ê_w(λ, r′)`).**
   - `bzExpr = w·(ab + z + E)` (3.2's `ŵ·Ê` product) becomes `w·(ab + z) + W_E` over a fifth
     table `W_E := eq(r,·)·Sel·E`. Restate `bzTables`, `bz_trueSum`, `bz_final` and
     `bz_triple_wrong` accordingly; degree 3 is unchanged.
   - `bzPoly` (Z2) is unchanged: the same `P*`.
   - Add `targetMLE_eq`: the verifier's per-kind, per-pinned-position sum equals `Ŵ_E(λ, r′)`.
   - The blueprint's `Ê_w` formula must state the position factor exactly: `posW` must include
     `eq(r_pos, pos)·eq(r′_pos, pos)` on the non-skip position bits and the skip slice's
     `L_i(λ)`·`eq` structure. As written, only `eq(r′,blk)eq(r,blk)` is explicit.
2. **The lincheck** as S-C-M1.
3. **Z2's message form** (open Q2). `gen` will use the 3.2/3.3 form:
   - `P^z` on `Λ` (degree ≤ 63, so interpolated over `Λ` alone);
   - `P^{ab}` on `Λ`;
   - `P^{ab}|_S` reconstructed as `P^z|_S + P^e|_S`.
   `skip_bad_le` covers the `P^{ab}` side, and `card_interpolateAt_eq_le` covers the `P^z` side.
   Add a 20-line `z2_pair_bad_le`: if the residual is nonzero on `S`, or the `P^z` message is
   wrong, at most 127 `λ` make both reconstructed values agree with the truth. `zcMsg` (leanerVM's
   form) is then unused by `gen` and can stay as a control.
4. **`E` per kind.** `BHolds`/`bzRes` already take a generic `E` table, so there is no change. Only
   `Sel = ∪ Ind_kind` must be bit-valued, which `bzRes_bit` needs and the layout gives.

## Minors

- **S-C-m1 (open Q3, the unaligned `d` slot).** It needs no closed form. `collapse_mle` is
  already generic in the slot map `pos`, and the verifier can evaluate
  `mle (slotW pos θ) r = Σ_σ eq(θ,σ)·eq(cube (pos σ), r)` directly: 256 terms × about 14
  products, about 3.6 k products, negligible against `T_V`. Add that 3-line general lemma
  (`slotW_mle`) and let `gen` use the direct sum for the chain block's `d` at 520…775. Keep
  `slotW_mle_aligned` for `h_in`/`h_out`. §2.3 says 10 collapse coordinates over positions
  `< 1024`, and `slotW`'s `s` must be that (not 8).
- **S-C-m2 (open Q1).** `FR.lean` imports none of the S-C modules. Until it does, neither the
  controls nor the lemmas are in `Solution`'s closure, so the gate and the kernel replay never see
  them. Add `import FRMLEControls`, or each module (owner: orchestrator).
- **S-C-m3.** About 40 deprecation and linter warnings (above). Fix them before the modules enter
  the certificate's build log.
- **S-C-m4.** `FRSumcheck` is 444 lines against 350 and `FRMLEControls` 95 against 50; the stage
  is under its total (2,430 / 2,850). Fine, but record it in §7's table.
- **S-C-m5 (kernel cost).** `FRSkip` takes 18.7 s of kernel time (`pinnedW_eq` 9.8 s,
  `pinned_cert` 7.1 s). That is acceptable at FR-R4′'s margin, but it is the stage's single
  largest item. See the golf suggestions.
- **S-C-m6.** RS1's count is over `F^8` (7 coordinates and `κ`); the mapping to 4 answers × 2
  coordinates is L-cert's (`pair_bad_le`). State in the RESULT that `rs1_joint` is consumed
  through `extCount_split` across the phase's 4 squeezes, as the potential must charge
  conditional counts per answer.

## Golf suggestions (for the implementer; no statement changes)

- `pinnedW_eq`: evaluate the 254 products through S-A's fast two-`UInt64` twin. Rewrite with
  `toExt_mul` / the twin's equality, then `decide +kernel` on the twin, whose kernel path is
  `UInt64`/`Nat` (GMP) rather than CompPoly's generic `Ext` multiplication. That should cut most
  of the 9.8 s.
- `pinned_cert`: checking `M·Minv = I` row by row folds 128 × 128 `F` additions. Shipping `Minv`
  as 128 `UInt64` pairs and computing the row product with `UInt64` xor (proved equal to
  `rowMul` once) would also cut the 7.1 s.
- Replace the deprecated lemma names (`ite_eq_left`/`ite_eq_right`, `dite_eq_left`,
  `Fin.val_castLE`, `Fin.val_natAdd`, `ite_true`), and remove the unused simp argument
  (`FRShift` l. 80) and the unreferenced `hSel` (`FRSpartan` l. 338).
- `FRSkip`'s `skipNode_eq_zero` and `S_disjoint_Λ` use `decide +kernel` over 128 nodes. Both
  follow from `GF2Indep gW` (`zeta_order`), with a one-line linear-independence argument instead
  of enumeration, if kernel time matters.

## Verdict

**S-C's lemmas are correct and non-vacuous for revision 3.2:**
- every §5.2 row has its exact count in a `KState`-consumable form;
- `pinned_rank`'s certificate is really checked;
- the controls cover every definition (`BHolds`, `ChainLinks`, `prefixP`, `ŵ`, the pack,
  `PinnedIndep`, `ζ`, `interpolateAt`, `shiftPair`).

**Not yet acceptable for revision 3.3.** The per-kind lincheck the blueprint prescribes is not an
identity (S-C-M1), so `FRSpartan` cannot follow it. A corrected form (per-kind folded columns,
one masked walk with the claimed `v_kind`, extra RS claims) is proposed. The other 3.3 changes to
Z3's summand and Z2's message form are listed in S-C-M2. Fix the blueprint's step 3 first, then
apply M1–M2 and the minors; Z, L-free rows, Sh, RS1, Lr, E and B′ need no other change.
