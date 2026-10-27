# S-D (track L-pcs): adversarial review

Reviewed: `docs/v4/flock-recursive/stages/S-D-RESULT.md` and the Lean of
`submissions/flock-recursive/lean/{FRRS,FRRSEval,FRProximityBW,FRProximityLine,FRProximityFold,
FRMerkle}.lean` (statements read in the source, not the RESULT's paraphrase), against BLUEPRINT
revision 3.1 (§2.1–2.2, §5.2–5.4, §6, A.1–A.2) and the crypto review's rounds 1–4. The build
tree `logs/fr-build-pcs` rebuilds the six modules (`Build completed successfully`); a probe under
`logs/S-D-review/probe.lean` (log `probe.log`) adds a negative control for `fold_preserves` and
re-checks the axioms of `mca_ud_line_K` and `fold_preserves` (the three standard ones).

## The headline: `mca_ud_line` with `C_mca = k e + n`

The statement (`FRProximityLine.lean` 200–224) is, for any field `K`, injective `x : Fin n → K`,
`2e + k ≤ n` and any `u₀ u₁ : Fin n → K`:

```
∃ B : Finset K, B.card ≤ k * e + n ∧ lineBad (rsCode x k) e u₀ u₁ ⊆ B
lineBad C e u₀ u₁ = {z | ∃ w ∈ C, n − e ≤ #agreeSet (u₀ + z • (u₁ − u₀)) w ∧
                        ¬ ∃ v₀ ∈ C, ∃ v₁ ∈ C, agreeSet₂ u₀ u₁ v₀ v₁ = agreeSet (u₀ + z • (u₁ − u₀)) w}
```

This is §5.3's set verbatim: the line is `(1 − z) u₀ + z u₁` (the sumcheck fold `eq(z, ·)` over
one row bit), the words are K-valued, the code is `RS[K, x, k]` (equal to `C_K = Enc_k(K^k)` on `D`
by `encCode_D`), and "bad" is: some codeword is `e`-close to the line point but no codeword pair's
joint agreement with `(u₀, u₁)` is that agreement set. Under `2e + k ≤ n` (`2e ≤ n − k`, i.e.
`2e < d`), which is the integer form of §5.3's `2e < n − k + 1`, the close codeword is unique
(`close_unique`), so the quantifier `∃ w` is harmless.

The proof is checked line by line and is correct; it is simpler and tighter than §5.3's plan:

1. `bw_exists`: the bivariate Berlekamp–Welch system `N(x_j, Z) = E(x_j, Z)·(u₀_j + Z(u₁_j − u₀_j))`
   with `deg_X E ≤ a := n − k − e`, `deg_Z E ≤ e`, `deg_X N < n − e`, `deg_Z N ≤ e + 1` has
   `(a+1)(e+1) + (n−e)(e+2)` unknowns against `n(e+2)` equations; `a ≥ e` gives `(a+1)(e+1) ≥
   (e+1)² > e(e+2)`, so a nonzero solution exists for **every** `(u₀, u₁)` (no threshold on the
   number of close `z`, which is where §5.3's rank-over-`K(Z)` and long-division steps came from).
2. `bw_E_ne` (`E = 0` forces `N = 0`, as `deg_X N < n`), `bw_few_zero_cols` (`E(x_j, Z) ≡ 0` at
   `≤ a` positions), so `k` positions `J` with `E(x_j, Z) ≢ 0` exist; `v₀, v₁` interpolate there.
3. For `z` off the `≤ k e` roots of the `E(x_j, Z)`, `j ∈ J`, `bw_unique` (`a + k = n − e ≤` the
   agreement) gives `N(X, z) = E(X, z) P`, hence `P = u_z` on `J`, hence `w = v₀ + z (v₁ − v₀)`.
4. `line_eq_root`: a position outside the joint agreement set agrees with the line's codeword for
   at most one `z` (`≤ n` values; Lean's `x/0 = 0` only adds a harmless element to the cover).

So `C_mca = k e + n` is a theorem, `2^37 + 2^20` at level 0, `m = 32` (`cMca (2^20) (2^19) (2^18) =
2^37 + 2^20` by `decide` in the probe), and the P1 row is `≤ 2^-214`. `pcsLevels_ok` checks
`2e + k ≤ n ≤ 2^64`, `C_mca ≤ 2^60` and the row at all ten levels by `decide`; `lineBad_nonempty`
(GF(5), `n = 3`, `k = e = 1`, bad at `z = 0`) shows the set is not always empty and
`lineBad_codewords` that it is empty on a line of codewords. The RESULT's exhaustive probe at
`K = GF(256)` found a worst count of `e + 1`; mine in round 1 found `e`. Nothing is vacuous.

**What it gives downstream.** `fold_lift`/`fold_preserves` use exactly the conclusion (a pair
`(v₀, v₁)` whose joint agreement with `(u₀, u₁)` **equals** the fold's agreement set), which is
what §5.4 step 2 and the extractor's agreement set need: on `A` every row equals its codeword, so
any `k` positions of `A` interpolate it (`rs_eq_of_agree`).

## `fold_preserves`, `fold_lift`, `round_bad_cover`

`JointClose C e U A := n − e ≤ #A ∧ ∃ V, (∀ i, V i ∈ C) ∧ jointAgree U V = A` ("the rows agree with
codeword rows **exactly** on `A`"). `fold_preserves` (`FRProximityFold.lean` 114) is an iff between
the pair rows `(U₀ c, U₁ c)` and the folded rows `U₀ c + z (U₁ c − U₀ c)` with the same `A`, under
`hz : ∀ c, z ∉ lineBad (rsCode x k) e (U₀ c) (U₁ c)`; `fold_lift` is the direction `final` uses
(fold close with agreement `A` ⇒ the pairs jointly close with `A`, with codewords that fold to the
given ones). Both proofs are correct: the backward direction is `good_line` per pair; the forward
one identifies the lifted pair with the given one by `rs_eq_of_agree` on `A` (`|A| ≥ n − e ≥ k`).
`round_bad_cover` takes the union of the `m` lines' covers: `≤ m · C_mca`, the P1 row's count
(`pcsLevels_ok` uses `2^6 ≥ 32` lines). One round for an arbitrary pairing is the right
granularity: the row-bit order per round is the transcript's.

My probe adds the missing negative control: at the bad `z = 0` of `lineBad_nonempty`, the fold
`(0,0,1)` is jointly close with `A = {0, 1}` while the pair rows are not
(`fold_preserves_fails_at_bad`, `logs/S-D-review/probe.lean`): the `hz` hypothesis is needed.

## `interp_F`, `positions_bad_le`, the novel basis

- `interp_F`: a codeword of `RS[M, ι ∘ x, k]` that is `L`-valued on `k` positions is `ι` of an
  `L`-codeword (interpolate over `L`, compare over `M` on `k` points). `interp_F_D`: in `C_K` on
  `D`, `F`-valued on `|A| ≥ k` ⇒ `Enc_K` of an `F`-message. Correct and exactly §5.4's
  "F-valuedness once per level".
- `positions_bad_le`: `#S + e < n ⇒ #{f : Fin t → Fin n | ∀ i, f i ∈ S}/n^t ≤ (1 − e/n)^t`, i.e.
  tuples with repetition (R2-M3) and the bad condition `|A_c| ≤ n − e − 1`, the complement of
  `JointClose`'s `n − e ≤ |A|`. Right; the per-answer fibers and the martingale across answers
  are L-cert's.
- `FRRS`: `subW`, `normW`, `novelX` are LCH14's; `novelX_natDegree` (degree exactly `x`),
  `exists_encPoly` (every polynomial of degree `< k` is `Σ c_x X_x`), `encCode_eq_rsCode`
  (`C_M = RS[M, pt, k]`), `rs_minDist`, `enc_injective`; `novelX_eval_zero`/`_lt_msb` is the
  block-triangularity the half-split back-substitution needs; `subW_add`, `normW_succ` the LCH
  recursion on the additive domain `D` (`D_xor`, `D_injOn` on `[0, 2^64)`).
- **The tensor identity is the verifier's weight.** `novelX_tensor`: `Σ_{x<2^ℓ} eqBits r ℓ x ·
  X_x(y) = Π_{v<ℓ} (1 − r_v + r_v Ŵ_v(y))`; with `y = D[j]` this is `Ĝ_j(r)` for the consistency
  functional `Enc(f)[j] = Σ_x f(x) X_x(D[j])` (`G_j(x) = X_x(D[j])`, multilinear in the bits of `x`),
  and `tensorTwin`/`tensorTwin_eq` is A.8's `tensorW j r` (`r` over `K`, `Ŵ_v(D[j])` over `F`
  through `algebraMap`). `eqBits` is little-endian (bit `v` ↔ `r_v`); the bridge to `FRMLE.eq` and
  to the sumcheck's variable order is L-cert's (S-D-m4).

## `FRMerkle.cap_binding` and the hashing windows

`openPath E col j ss` is the verifier's path (column query, then `nodeQ` with the running digest
on the right iff bit `t` of `j`); `colL E L d h j` reads top-down from `d` by first preimages,
descending by bit `h − 1`, …; consistent with each other and with A.2 (left child `2d`, so the
running digest is the left child iff bit `t` of `j` is `0`). `cap_binding`: `¬ Collision L` and
`openPath … runLog L = some d` ⇒ `colL E L d |ss| j = some col`. Correct (`pre_of_mem`: without
collisions the first entry answering `e.2` has `e`'s query). `colL_append` and `colL_prefix`
(under `¬ Hit`, a column read under a digest carried by an input of the prefix is read off the
prefix; `pre_none_append`: an erasure stays an erasure) give what `cap_binding` in §5.4 step 1
needs: the word `W⁽ⁱ⁾` is fixed when the cap is absorbed, read the same way by the verifier (at
queried positions) and by the extractor (everywhere). `Collision` and `Hit` are §5.1's "digest
collision" and "fresh answer equal to an in-play digest", with the in-play digests abstracted as
`E.carried` of the inputs.

**The alignment question is serious, and it is the blueprint's.** §5.1 defines `Bad`'s hits over
"16-byte-aligned 32-byte windows of any logged query or answer". In the node query `"FRMNOD" ‖ i ‖
0 ‖ left ‖ right` the children sit at **query** offsets 8 and 40, in the cap absorb `"FRABS000" ‖
st ‖ msg` the state at 8 and the cap entries at `40 + 32·idx`: all `≡ 8 (mod 16)` relative to the
query, `≡ 0 (mod 16)` only in the hashed stream (where each query starts at offset `≡ 8`). If
`FRLog.bad_step_le` takes the windows literally (offsets `0, 16, 32, …` of the query bytes), no
child digest and no cap entry is in play, a fresh answer equal to an inner node is not `Bad`, the
`¬ Hit` hypothesis of `colL_prefix` does not follow from `¬ Bad`, and the potential undercharges
the one event the Merkle argument lives on. S-D's `carried` parameter is the right interface; the
fix is one definition (S-D-M1).

## Findings

### S-D-M1. The in-play windows must be at query offsets `≡ 8 (mod 16)` (blueprint §5.1, `FRLog`)

As above. **Fix** (not in S-D's code): state in §5.1 and implement in `FRLog`'s `Bad`: "every
32-byte window at an offset `≡ 8 (mod 16)` of a logged query (the payload's 16-byte elements,
pairs of them), and every answer"; the count `≤ 2^16 · logCap` is unchanged (`2^-144`). S-0's
`MerkleEnc` instance must then set `carried (nodeQ a b) = [a, b]` and `carried (absorbQ st msg) =
st :: (the 32-byte elements of msg)`, and add a law `carried_absorb` so that `colL_prefix`'s `∃ e ∈
L, d ∈ carried e.1` is dischargeable at the cap (today only `carried_nodeQ` is a law; with an
instance whose `carried` of an absorb is `[]`, `colL_prefix` is true but unusable at the cap).

### S-D-m1. `coeffs_of_values` and `interpF` are not delivered

§5.4 step 2 and §6.5 (`coeffs_spec`, `interp_spec`) name `coeffs_of_values` (the novel coefficients
from values on `D[0…k)` by the half-split back-substitution) and the computable barycentric twin
`interpF`; §7 lists both under `FRRS`/`FRRSEval`. S-D proves the ingredients (`novelX_eval_lt_msb`,
`enc_injective`, `normW_eval_self`) but defines neither function nor its spec lemma. L-ext's
`coeffs_spec` is blocked until an owner is named (S-D or L-ext); the algorithm's correctness
(`T(k) = 2T(k/2) + k²/4`) rests on `Ŵ_{κ−1} = 1` on the upper coset (`normW_eval_self` plus
`normW_add`) and vanishing on the lower half (`novelX_eval_lt_msb`), both available.

### S-D-m2. Controls that cannot fail

`D_two_pow_64 : D (2^64) = D 0 := rfl` is definitional (the `UInt64` wrap) and `novel_D_ok` only
instantiates two lemmas: neither can fail once the definitions type-check. Keep them as remarks
or replace `D_two_pow_64` by a control that uses `D_injOn`'s bound (`D_injOn` fails to extend to
`2^64 + 1` points). Add the probe's `fold_preserves_fails_at_bad` as the negative control of
`fold_preserves` (it is the one theorem of the module with a hypothesis that could, in principle,
be unsatisfiable).

### S-D-m3. `cap_binding` leaves the cap comparison and the level to the consumer

`openPath`'s result is compared with `cap[j / 2^h]` by the verifier, and `MerkleEnc` is "one
Merkle tree" (one level's tags). Both are right as a parametrisation, but the RESULT should say
that `pre L d` searches the **whole** log (all levels, all kinds of queries): a first preimage of
the wrong level or kind parses to `none` (an erasure) and never to a wrong column, because
`parseNode`/`parseCol` are level-specific and `pre_of_mem` + `¬ Collision` give the verifier's
own entry. The instance's `parseNode` must therefore check the level byte, not only the kind.

### S-D-m4. `eqBits` against the sumcheck's variable order

`eqBits r ℓ x` reads bit `v` of `x` against `r_v`, little-endian. The consistency weight's
`r` is the Ligerito point whose coordinates are the fold challenges in **round order**; if the
transcript folds the high row bit first, the bridge to `FRMLE.eq` is a reversal, not the identity.
A one-line `eqBits_eq_FRMLE_eq` with the order fixed by `FRTranscriptDefs` is owed (L-cert), and
`tensorW`'s operand order in A.8 should say which.

### S-D-m5. Small things

- `mca_ud_line_K` takes `hn : n ≤ 2^64`, `hk : k ≤ 2^64`; the levels have `n ≤ 2^20` and the
  computable twins are instantiated at `N = 20` (`wAtD`, `encD`): the two bounds should be the same
  constant in `FRTranscriptDefs` so that `encD_eq`'s `hn : n ≤ 2^20` and `encCode_D`'s `2^64`
  never disagree in a consumer.
- `FRProximityFold` declares `instance fact_prime_five` globally for the controls; scope it
  (`local instance`) so it cannot leak into L-cert's modules.
- The RESULT's "`cap_binding` is the semantics of A.5's `askCol`, `askNode`, `bitOf`,
  `selectHalf`" is a claim about `FRVIR`'s `gen`, which S-D does not import; `runSeq_eq_runIR`
  will have to prove it. Fine as a remark, not as a result.

## Verdict

**S-D's theorems are true, non-vacuous and sufficient.** `mca_ud_line` is stated exactly as §5.3
(K-valued words, `C_K`, the line `(1−z)u₀ + z u₁`, joint agreement set equal to the fold's), proved
for every pair of words with `C_mca = k e + n` by a counting argument that is strictly better than
the planned one; `fold_preserves`/`fold_lift` give the agreement-set lift `final` and the
extractor need; `interp_F_D`, `positions_bad_le`, `encCode_D`, the block-triangularity and the
tensor identity (the verifier's `tensorW`) are the right statements; `cap_binding`/`colL_prefix`
are the binding the potential needs, parametric in the encodings. No `sorry`, three axioms, the
controls real (two trivial ones noted). **Accept**, with one blueprint/L-cert change required
before `FRLog` (S-D-M1: in-play windows at query offsets `≡ 8 mod 16`, `carried` for absorbs) and
the owner of `coeffs_of_values`/`interpF` to be named (S-D-m1). Blueprint changes requested by the
RESULT (`C_mca = k e + n`, the counting proof in §5.3, FR-R8 closed) should be applied.
