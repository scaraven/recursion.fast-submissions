# R-V: adversarial review of the verifier's finals (2026-10-28)

Track R-V. Worktree `v4/flock-recursive` at HEAD `750ab01` (INT-4). Program reviewed: the dump
`logs/INT-4/dump/` (105,839 ops, `ops-{L,P,N,M}.txt`, `items.json`), against `FRVIR`, `FRVIRSpec`,
`FRVIRFinals`, `FRVIRFinalsSF`, `FRVIRFinalsSG` and `FRVerifierImpl*`, and against BLUEPRINT
§2.3, A.6, A.8–A.10, §10. No Lean, blueprint or code file was edited. No Lean probe was run.

**Method.** Six small scripts over the dump: `logs/R-V/scripts/*.py`, run with `python3 -I`; their
outputs are in `logs/R-V/*.txt`.

- `parse.py` reads each op's input and output registers. A `keep` reads only the operand its
  fixed-kind flag selects. An inactive assert (`act = false` for the kind) is not a sink.
- `live.py` computes liveness for each kind, backward from the active `assertEq`, `assertZero` and
  `assertOneHot`.
  - `askSeed`, `askAbsorb` and `askSqueeze` do **not** pass liveness to their operands. So "live"
    means *checked by an assert*, not merely hashed into Fiat–Shamir.
  - `askNode` and `askCol` do pass it, because their answers meet the cap `assertEq`.
  - Output: `dead-{L,P,N}.txt`.
- `claims.py` finds each rounds phase's `claim0`/`claimN` and the first active assert they reach
  (`claims-*.txt`).
- `cover.py` checks that every proof read lies inside an absorbed, seeded or queried byte range,
  and that every byte of fields 0–15 is read (`cover-*.txt`).
- `types.py` checks that both operands of every active `assertEq` have the same scalar kind
  (`types.txt`).
- Array ops are treated conservatively: a packed point makes all its entries live. So the dummy
  coordinates of Z1 (read whole by `targetS`) were checked by reading the ops, not by the script.

Line numbers `NNNNN` below are lines of `ops-N.txt` (the other kinds share the numbering). `file:line`
refers to `submissions/flock-recursive/lean/`.

## Summary

- **No unbound value of the `finZ` kind was found.** For each of L32, P30 and N30:
  - every register outside the dummies reaches an active assert;
  - so do every `claim0`/`claimN` of every rounds phase, every RS claim value `α_j` and `v_RS`,
    every export that has a reader, and every squeeze used as a point;
  - every byte of fields 0–15 is read, and every read is absorbed before the challenges it is
    combined with.
- **Two major defects, both on the node path (`N30`) and both in the Lc claim:**
  - **R-V-M1**: RS claim 2 lost `W_β`'s kind factor.
  - **R-V-M2**: the `free` kind is folded into the circuit walk.
- **Neither is a soundness hole.** I could not build an accepted false N30 proof. With either
  defect, V certifies a relation that no node witness satisfies (M1) or that is stronger than
  intended (M2).
- **Each defect is still major:**
  - V rejects every honest N30 proof. Leaves are unaffected, and the leaf tests of P2 cannot see
    this.
  - Each makes A.10's Lc/L3 hand-off unprovable, so S-G will meet them as dead ends.
- **Three minor findings** (m1–m3).

## 1. Findings

### R-V-M1 — RS claim 2 (Lc's `v_β`) is weighted by a plain `eq`; `W_β`'s kind factor is missing (node)

- **Where.**
  - `FRVIRFinalsSG.lean:642` (`lcSrc`: L2's challenges 7–13, then Z3's from 8, all coordinates
    of an `eq` point), `:668` (`rsPtIx .N30 = [1, 3, 5, 6]`), `:771` (`.rsWeight wb … (rsPtIx κ)`).
  - `FRVerifierImplOps.lean:221` (`rsWeightS` = `Σ_j κ^j Σ_k c_k(r″) eq(r_j^{2^k}, ρ)`, with no
    other factor).
  - `FRVerifierImpl.lean:47` (`kindFoldWeight _ _ _ := 0`). Neither `kindFoldWeight` nor
    `kindInd` occurs in any dump (count 0 in `ops-{L,P,N,M}`).
  - Dump: `101800` (Lc's point, `packK r92945 …`); `102047` `rsWeight r93214 [r92918 r92968
    r93018 r93042] r2172 r93213`; `66130` `assertEq r57439 r55324` (`v_β = α_Lc`, every kind).
  - The soundness side mirrors V: `FRSoundnessFrRS.lean:25` (`gL` is `eqPts` at `rsPtsL`),
    `FRSoundnessFrW0.lean:45` (`lcPtL`), and `FRSoundnessFrPend.lean:26` (`okRS … 1 v := v =
    vBetaL`).
- **What the blueprint asks.**
  - §2.3 step 3 (lines 199–201): `Σ_kind β^kind v_kind = ⟨W_β, z⟩` with
    `W_β(t, j) = eq(r′_blk, t)·(Σ_kind β^kind Ind_kind(t))·eq(r_k, j)`.
  - A.8 `kindFoldWeight` (line 1140) and A.9 `finLc` (iii) (line 1167: "becomes RS claim 2 with
    weight `W_β`").
  - S-C's `lin_beta_claim` (`FRSpartan.lean:585`) proves exactly this form.
  - Revision 3.9 replaced the MBP by `rsWeight` (A.8 line 1125: "Lc: `(r′_blk, r_k,hi)`") and
    `kindFoldWeight` was never wired (S-F2 RESULT §4 item 3: "not used by revision 3.9's `gen`").
- **What V checks.**
  - RS and Ligerito bind `α_Lc` to `Σ_t eq(r′_blk, t)·ẑ_t(r_k) = Σ_κ zfold_κ(r_k)` (`Sel ≡ 1`:
    each block has exactly one kind).
  - `finLc` (iii) asserts `Σ_{i<8} β^i v_i = α_Lc`.
- **Consequence.**
  - **Completeness.** Take the honest `v_κ = zfold_κ(r_k)`. The check holds only if
    `Σ_{i≥1} (β^i − 1)·zfold_{κ_i}(r_k) = 0`, a nonzero polynomial of degree 7 in `β` on any node
    (stream, WOTS, hash and `free` blocks all have nonzero folds). Every honest N30 proof fails,
    except with probability `7/2^128`.
  - **Soundness: no hole.**
    - The `v_i` are absorbed (L3) before `β` (L3β), so the check forces `v = (S, 0^7)` by
      Schwartz–Zippel, with `S = Σ_κ zfold_κ`.
    - Then `finLc` (ii) certifies `â, b̂` against the **`stream`** matrix (pins only
      1024…1152) on every block.
    - Z then certifies `(A^stream z)∘(B^stream z) = z + E` with the true per-kind `E`. On a
      `streamStart` block, the input rows `(var k, var one)` with `z_1152 = 1` force
      `E_k = 0`, but `E_k` is an `h0` bit that is 1. No `z` satisfies this, so V rejects every N30
      proof with high probability.
  - **Proof plan.** On a log whose L3 values are true, `PendBad (okRS …)` at `j = 1`
    (`trueL 1 ≠ vBetaL`) holds deterministically. A.10's hand-off from L3 to E4 end/RS0 (L3's
    truth implies `¬ PendBad`) is false for nodes, and S-G7 cannot discharge it.
- **Severity: M** (completeness of every node proof, and a soundness-proof blocker; not an attack).
- **Minimal fix.** Restore `W_β` in RS claim 2 for nodes. Leaves already have it: one kind,
  `Ind_chain ≡ 1`, so `W_β = eq`. Either:
  - **(a)** Give `rsWeight` claim 2's kind factor in Φ form.
    - With `g = eq(p, ·)·B_β` and `Ind ∈ {0,1}`,
      `Φ(g)(u) = Σ_k c_k(r″)·eq(p^{2^k}, u)·Σ_κ β^{i(κ)·2^k} Ind_κ(t(u))`.
    - So
      `Ŵ₂(ρ) = Σ_k c_k Σ_κ β^{i(κ)2^k}·eq(p_hi^{2^k}, ρ_hi)·Σ_{t∈I_κ} eq(p_blk^{2^k}, t) eq(ρ_blk, t)`.
      This is A.8's `kindFoldWeight` made Φ-aware: interval prefix sums, about
      `128 · #intervals · 16` products.
    - Mirror it in `gL`/`trueL`.
  - **(b)** Add a block sumcheck after L3β: `m* − 14 = 18` degree-3 rounds (P30/N30: 16 real)
    on `eq(r′_blk, t)·B_β(t)·ẑ_t(r_k)`.
    - It ends in a plain point claim `ẑ(r_k, r″_blk)`, so `rsWeight` is unchanged, plus one
      `kindInd`-style evaluation of `B̃_β(r″_blk)`.
    - Cost: items +36, π +864 B, error `3·18/2^128`.
  - Either way the node circuit's replay of `finPf`/`finLc` follows.

### R-V-M2 — `finLc` (ii) puts `v_free` into the circuit walk; the `free` kind's term is `(1 + α)·rowW` (node)

- **Where.**
  - `FRVIRFinals.lean:168–173`: the node's `packFK (b+14) :: v` puts `v_7 = v_free` at
    `blockKinds` index 8, then `.maskRows (b+15) (b+5)` and `.walkAB`. The same at `relLc`
    `:345–349`.
  - `FRVIR.lean:452` (`maskOf` sums over every kind not pinning row `k`), with
    `FRTranscriptDefs.lean:666` (`zeroRows .free = []`). So `v_free` is in every row's mask.
  - The kernel control `maskOf_pos` (`FRVIR.lean:939`) already shows it: row 0's mask is
    `2 + 8 + 64 + 256`, and 256 is `free`'s weight.
  - Dump: `66108` `packFK [r57417 r57409 … r57416]`, `66109` `maskRows`, `66112` `walkAB`,
    `66115` the assert.
- **What the blueprint asks.**
  - A.6 (line 1077): `A₀^{free} = B₀^{free} = I`.
  - §10 changes 6 (line 1523): "`M_free = (1 + α)·rowW`, no walk". Changes 7 (line 1543): "The
    lincheck's free term is `(1 + α)·rowW`". Changes 8 (line 1551): `v_free` exists for this
    term.
  - S-C: `linM_free` (`FRSpartan.lean:617`). `lin_walk_adjust` (`:599`) needs
    `A₀^κ(k, j) = free_κ(k)·A₀(k, j)`, which the identity is not.
  - A.9's `finLc` row (ii), "`Σ_{kind ∌ k} v_kind`", literally includes `free`. It is stale
    against 3.8.1, and the Lean follows the stale text.
- **Consequence.**
  - **Completeness.** V uses `v_free·(Â₀ + αB̂₀)(rowW, eq(r_k))`, with the Blake2s circuit's
    matrices. The true term is `(1 + α)·v_free·Σ_j rowW[j] eq(r_k, j)`. Honest M, L and `WM` data
    give `v_free ≠ 0`, so every honest N30 proof fails `66115`.
  - **Soundness: no hole.** The walk binds `â, b̂` to the circuit's rows on `free` blocks. That
    relation is stronger there than the intended `z_k² = z_k` (vacuous on bits), and the hash
    blocks are unchanged.
  - **Proof plan.** `lin_final_kinds` with `A₀^free = I` is not what `finLc` checks, so S-G's
    `truthLc` for a node cannot meet `relLc`.
- **Severity: M** (completeness of every node proof, and a soundness-proof blocker).
- **Minimal fix.**
  1. Give `free` weight 0 in the mask: the node's `packFK` entry 8 becomes the zero register
     `b + 14`.
  2. Add `(1 + α)·v_free·⟨rowW, eq(r_k, ·)⟩` to the walk's `Â + αB̂` before `66115`. In closed
     form, `⟨rowW, eq(r_k,·)⟩ = (Σ_{s<64} L_s(λ)·eq(r_k[0..5], s))·eq(r′_hi, r_k[6..13])`: one
     `eqPt` and a 64-term sum.
  3. Update `relLc`/`flag_finLc` and A.9's row. The node templates replay the new ops.

### R-V-m1 — `assertBit` checks nothing

- **Where.** `FRVIR.lean:577`: `| .assertBit _ _ => .vals [] true`. A.8 (line 1143) lists
  `assertBit b` as a check ("a failure returns `false`").
- **Effect.** No op of `gen` uses it (count 0 in every dump), so V is unaffected today. A future
  use would assert nothing, which is the `finZ` failure mode.
- **Fix.** Make it clear `ok` unless the operand is a bit (`.bit _`, or the F value 0 or 1)
  wherever `act κ` holds, or delete the op.

### R-V-m2 — `accept_fields` does not pin `zhat` or `ex` (soundness-side interface)

- **Where.** `FRSoundnessAccSem.lean:153–161`: `∃ zh, ∀ k, ∃ Rk exk L, ExtA … Rk ∧ pureRun
  ((fin.rest[k]) ⟨outs, zh, exk⟩ Rk.size).1 Rk [] = some (L, true)`.
- **Effect.** A field's flag is meaningful only for `zh` = `finRS`'s exports and `exk` = the
  earlier fields' exports.
  - From this statement alone, `relZ` (ii) is satisfied by `zh[0] :=` Z2's own `P^z*(λ)`
    register.
  - Likewise `finLc` (iii), `finSh` (ii), `finE` (iv)–(v), `finB′` and `finE`'s `v_L`/`r_Lr`
    carry no binding.
  - Today's users (`FRSoundnessAccLog.lean:292`, `AccVal:121`) read only `finP`/`finPf` or the
    skeleton, so nothing is wrong yet.
- **Suspected relevance:** S-G7's `oZ`/`oSh` bindings must not be built on this lemma. That is
  settled when S-G7 states `hFront`'s bindings.
- **Fix.** State the lemma with `zh := (fin.finRS ⟨outs, [], #[]⟩ b).2` and `exk` the fold's
  accumulated exports. The proof already uses these witnesses (`AccSem.lean:196`).

### R-V-m3 — stale A.8/A.9/A.10 rows (documentation)

| Row | Stale text | Now |
|---|---|---|
| A.9 `finLc` (ii) | `Σ_{kind ∌ k} v_kind` (includes `free`) | M2 |
| A.9 `finLc` (iii), A.8 `kindFoldWeight`/`kindInd` | weight `W_β` | not implemented (M1) |
| A.9 `finSh` (i), outputs | "`h0` per chain for a node; batched by `1, y`"; "outputs RS claims 3–4"; `linkW` ×≤8 | node `bnd = 0` with the chain-masked start term (INT-3 D3: `streamStart` pins `h0`, sound); one RS claim; `linkWAll` + 8 `getF` |
| A.9 `finRS` | inner weights "… Lr"; "bound … `finLr`" | claim 3 is E4's `f̂(r′)` with the packing basis; bound in `finE` |
| A.9 `finLr` | "(i) `c₀ = 0` … `assertEq` ×2" | (i) by `initClaim`; one assert |
| A.10 Lr row | "`finLr` (iv): the claim `α_Lr` is RS's" | no Lr RS claim since 3.13 |
| A.8 `shiftTarget` | `AF 4` | `AF 22` (INT-4 D1) |
| A.8 `rsWeight` | "Lr: its point" | E4's `r′` (node only) |
| A.8 `walkA`, `walkB` | two ops | one `walkAB` |
| A.8 `assertBit` | a check | no-op (m1) |

## 2. Dataflow table

"Asserted at" lists the first active assert(s) the value reaches (`claims-*.txt`, `dead-*.txt`).
"All" means L32, P30 and N30.

| Value | Produced | Asserted at (kinds) | Note |
|---|---|---|---|
| `hdr` bytes 0–15 (kind, `m`, zeros) | 5 `r5` | 7 (all) | `kindOf` checks byte 0 and the size; `assertOneHot` 4 |
| `hdr.pub` (16–47) | N: 23 `r17`; L/P: 66132–33 | N: 25 (`= vk`); L/P: `bnd` → `shiftTarget` → 66143 | a leaf's `s` is witness, bound as `In(0)`; seeded at 2 |
| `vk` (`input 0`) | 2 (seed), 24, 66258 | N: 25 and 66288 (cells) | leaves: seed only (correct) |
| `c` (`input 1`) | 11 | 12 (all), `= hashStmt stmt` | seeded |
| `stmt` tag, leaf `n`, zero tails | 13, 16, 19, 21 | 15 (all), 18 (L,P), 20 (L,P), 22 (N) | |
| `stmt` `h` (leaf) / `c₁`, `c₂` (node) | 66134–35 / 66260, 66262 | 66143 (L,P) / 66288 (N); both also through 12 | |
| Z2: `P^z|_Λ`, `P^{ab}|_{Λ₀…₆₂}` | 60–186 → `lagrangeS` 192: `r185`, `r186` | `r185` = Z3 `claim0` → 66089; **`r186` → 66090** (all, INT-4) | padding 193 → 194 (all) |
| `λ` `r55` | 62 | `eqZ` 61957 → 66090; `rowW` 66098 → 66115 | |
| Z3 `claimN` `r603` | 636 | 66089 (all) | m = 30: rounds 24–25 dummy, zero-asserted |
| Zend `â`, `b̂` | 66085–86, 66092–93 | 66089, 66096 (all) | |
| L1 `α` `r607` | 640 | 66096, 66115 | |
| L2 `claim0` `r610` / `claimN` `r792` | 643 / 853 | 652 and 66096 / 66115 (all) | |
| L3 `v_0 … v_7` | 66099–66106 | walk 66115, `v_β` 66130 (all) | leaf `v_1…v_7` reach only `v_β` (bound by SZ in `β`, inside L3's `8/2^128`); node: **M1, M2** |
| L3β `β` `r796` | 857 | 66130 | |
| S1 `τ`, `θ`, `κ_s` | 858–901 | 66143, 66200 | dummies: coordinate 29; 16–17 for m = 30 (zero-padded) |
| S2 `claim0` `r845` / `claimN` `r1209` | 906 / 1326 | 915 and 66143 / 66200 (all) | m = 30: rounds 26–27 dummy |
| Lr1/Lr2/Lrend/Lr3 | 1328–1612 | 66211 (N); `v_L` `r57522` 66216 → 66236; `r_Lr` `r57513` → `evalL` 66243 → 66252 | leaves: Lr2 messages and Lr end zero-asserted |
| E1/E2/Eend/E3 | 1614–2012 | 66227, 66236 (N) | leaves: zero-asserted |
| E4 `claim0` `r1857` / `claimN` `r2156` | 2012 / 2357 | 2021 and 66236 / 66252 (N) | leaf `claim0` = 0 (zero message) |
| E4 `r′` (23) | 2016–2346 | `evalM`/`evalL` → 66252; `eSrc` → 105851 (N) | |
| E4 end `f̂(r′) ‖ 0^16` | 66253, 66255 | 66254, 66256 (all) | `relE_e4end` |
| RS0 slices (512) | 61964 … (`piElem 11 ·`) | through `α_j` and `T_j`; leaf claim 3 zero 66073 (L,P) | |
| `α_Z` `r54299` | 62983 | 66090 (all) | the INT-4 fix |
| `α_Lc` `r55324` | 64008 | 66130 (all) | weight: **M1** |
| `α_Sh` `r56349` | 65033 | 66200 (all) | |
| `α_E` `r57374` | 66058 | 66252 (N), 66254 (all) | |
| `v_RS` `r57387` | 66071 | 66288 (all) | leaf: `T₃` omitted |
| RS1 `r″`, `κ` | 2363–2373 | `T_j` → 66288; `rsWeight` 102047 → 105851 | RS1's packed array unused |
| B′ `κ′` `r2175`; public cells | 2376; 66258–63 | 66288; cells in `finPf` → 105851 (N) | leaves: `keep` gives 0 (no cells), so `κ′` is unused |
| P1.0 `claim0` `r2178` | 2379 | 2388 and 66288 (all) | |
| P1.i `claimN` (i = 0…4) | 2469, 26937, 40739, 49967, 56526 | 67164, 67704, 68145, 68547 (`finP` 0–3); 101696 (`finP 4`) | |
| P1.(i+1) `claim0` | 26877, 40679, 49907, 56466 | the same four asserts (and each round 0) | |
| caps, P2.i positions, columns, siblings | C.i, P2.i, Q.i | 872 cap `assertEq` (D = D); dummy siblings zero-asserted (1,742, P/N) | every index opened; `idx` per kind |
| column folds `y_q` | `dotKF` in Q.i | `finP i<4` through `v_{i+1}`; `finP 4`: 126 asserts (68549–101695) | |
| P3.i `κ_c` (9 of 10) | | `finP i<4`, `finPf`'s level steps | **P3.4 unused by design** (level 4 checked directly) |
| final message (128 K) | C.4 | `finP 4`, 105851; padding 56530 (P,N) | |
| Pf `claim0` `r53180` / `claimN` `r53271` | 61849 / 61954 | 61858 and 101696 / 105851 (all) | |
| Exports `ex` | | `finLr`'s `v_L`, `r_Lr` → `finE` | the other fields' exports have no reader and need none |

**Dead registers** are all by design (`dead-*.txt`):

- the dummy rounds and coordinates above;
- the kind alternatives of `keep`: a leaf's `eqPt`/`shiftEq`/`slotW 1`, a node's `shiftMask`/
  `slotW 2`, `finPf`'s points for the other `m`, a leaf's `T₃` (512 ops of `finRS`);
- the extra power `κ_s^{10}` (66197);
- for leaves, the whole of Lr and E apart from their zero checks.

No assert is fed from a wrong register. I checked by hand:

- every `outsOf … getD/headD` in the finals: Z2's `λ` (`r55`) and `P^z*` (`r186`); S1's
  `κ_s` (`r840`); RS1's `κ` (`r2172`); B′, L1, L3β, Lr3 and E3 (`r2175`, `r607`, `r796`,
  `r1479`, `r1854`);
- `zhat` 0–4 (the five registers above) and `lrEx` 0/1;
- `p1Claim0`/`p1ClaimN`, `claim0 "Pf"`, `oE4end` (`piElem 9 2112`) and `oL3` (`piElem 5 672…`).

`types.txt`: every active `assertEq` compares F/F, K/K, D/D or B/B. None compares an array, which
`Val.eqv` would reject.

## 3. Per-field table (A.9 against `relX`)

| Field | A.9 row | Lean relation (`flag_*`) | Discrepancy |
|---|---|---|---|
| `finRS` | `α_j = Σ_i w_i^{(j)} s_{j,i}`; `T_j`; `v_RS = Σ κ^j T_j`; a leaf has 3 claims, the 4th zero | `relRS = isNode ∨ rsLeafZero`; exports `rsAlpha j`, `rsV` (`exec_finRS`); inner weights `eqZ λ ρ₁`, `eq(r_k[0..6])`, `eq(r_pos[0..6])`, `bb i` | claim 2's **outer** weight (fixed by `finPf`) lacks `W_β`: **M1**; "Lr" text stale (m3) |
| `finZ` | `eq(r, r′)·â·b̂ = c_Z`; `ẑ(r, λ) = P^z*(λ)` (RS claim 1) | `relZ` (i) ∧ (ii) | none (INT-4) |
| `finLc` | (i) `c₀ = â + αb̂`; (ii) walk with `rowW′`; (iii) `v_β` is RS claim 2 with `W_β` | `relLc` (i) ∧ (ii) ∧ `v_β = α_Lc` | (ii): `free` in the walk, **M2**; (iii)'s value is right, its weight is wrong, **M1** |
| `finSh` | (i) `c₀ = shiftTarget`; (ii) `c_Sh = (w_out + w_in)·ẑ_Sh` | `relSh` (i) ∧ (ii); 18-coordinate `τ`; node masked weights; `κ_s^{f+2}` | node boundary is 0 (INT-3 D3, sound); text stale (m3) |
| `finLr` | (ii) end check; exports `v_L`, `r_Lr` | `relLr` (node) and both exports | none (text m3) |
| `finE` | (ii)–(iv) node; (v) E4 end `= α₄ ‖ 0^16` | `relE` | none |
| `finB′` | `v* = v_RS + Σ_{k<9} κ′^{k+2} pub_k = c₀^{P1.0}` | `relB` (`pubH`, `keep` for nodes) | none; cell order equals `pfCells` |
| `finP i<4` | `v_{i+1} = v_i + Σ_q eq(κ_c, q) y_q` | `relPLow` | none |
| `finP 4` | `y_q = Enc₄(final)[p_q]`; `c₀^{Pf} = c_{P1.4}` | `relP4` | none |
| `finPf` | `c_Pf = Ŵ(ρ)·final̂(ρ)`; `Ŵ` = `rsWeight` + cells + tensor terms; P30/N30 factor | `flag_finPf` | `rsWeight`'s Lc point: **M1** |

## 4. Acceptance and gating

- **Acceptance.** There are no per-field flags in the program. Each assert clears `ok`
  (`runOps`), and `semIR` returns `ok`. `gen`'s finals are `finRS` followed by `rest` (all 12 other
  fields); the dump shows all 13 sections. The finals contain 141 `assertEq` active for every
  kind, 4 node-only `assertEq` (`finLr`; `finE` (ii)–(iv)) and 2 `assertZero` (E4 end's zero half
  for every kind, RS0 claim 3 for leaves). The skeleton holds the rest; `ops-M.txt` gives each
  assert's activity per kind.
- **Kind selection** (`keep`, `packFK`, KC `act`).
  - **`finRS`:** the Sh inner point by `m`, `T₃` and the claim-3 zero check by `isNode`.
  - **`finZ`/`finSh`:** point lengths by `m`, `padB`, the boundary, the masked weights and the
    In slot.
  - **`finLc`:** the `v` layout.
  - **`finB′`, `finPf`:** cells by `isNode`; tails, points and the P30/N30 padding factor by
    `is32`; `rsPtIx`.
  - All match the blueprint's kinds.
- **Leaf dummies.**
  - All asserted zero: Lr2, E2 and E4 messages (59), Lr end and E end, RS0 claim 3, and E4 end
    through `α₄ = 0`.
  - A leaf's E4 `claim0` is `c₁ + c₂` of a zero message, so 0.
- **P30/N30 dummies.** Z3 rounds 24–25, S2 rounds 26–27, the Merkle depths `≥ sib_κ` (1,742) and
  the final message's padding: all asserted zero.

## 5. Transcript binding

- `items.json` order is revision 3.13's: `… Lr3@209, E1@210, E2@221, Eend@263, E3@264, E4@265,
  E4end@311, RS0@312, RS1@313, B′@317, P1.0@318 …`.
- Every proof read is inside an absorbed range (or the seed, or a column or Merkle query), and
  every byte of fields 0–15 is read (`cover-*.txt`).
- Each final combines messages only with challenges squeezed after them:

| Check | Pairing |
|---|---|
| `finZ` | Zend after Z3 |
| `finLc` | `α` after Zend; `β` after L3 |
| `finSh` | `hdr`/`stmt` before S1 |
| `finLr` | `κ_L` after Lr end |
| `finE` | `κ_E` after E end; `v_L` before E3; E4 end before RS0 |
| `finRS` | every claim point before RS0; `r″`, `κ` after RS0 |
| `finB′` | `κ′` after RS1 |
| `finP` | `κ_c` after Q.i |
| `finP 4` | final message before P2.4 |

## 6. Format and parse

- `Vwith` (`FRVerifier.lean:50`) runs the SNARK branch only for `kindOf π = .snark k`: byte 0 a
  kind byte and `|π| = piSize`. A kind byte with another size is `.bad` (rejected, no query).
  Any other first byte goes to the `W` branch.
- In the program:
  - bytes 0–15 of `hdr` are asserted equal to `hdrBytes κ` (kind byte, `m`, 14 zeros; line 7);
  - a node's `hdr.pub = vk` (line 25, N only);
  - a leaf's `pub = s` is a witness, bound by `finSh`'s boundary and seeded;
  - the statement is fully checked (lines 12–22).
- No read crosses a field boundary (`cover.py`).

## 7. Verdict

**Not ready for N30; ready for L32/P30.**

- The leaf path is clean:
  - every value V derives is asserted;
  - every `relX` matches its A.9 row;
  - the transcript order is right;
  - the format checks are complete.
- The node path has two defects in the Lc claim, R-V-M1 (`W_β`) and R-V-M2 (`free` in the walk).
  - They do not admit a false proof.
  - Each one alone makes V reject every honest N30 proof.
  - Each one alone contradicts the identity S-G's planned proof needs (`lin_beta_claim`,
    `linM_free`).
  - Both need a blueprint ruling (A.9 `finLc`, A.8 `rsWeight`/`kindFoldWeight`) and an S-0/S-G
    change before S-G7 states the L3/RS0 bindings and before the N30 prover is tested.
- m1–m3 are hygiene. m2 should be fixed before S-G7 uses `accept_fields` for any binding.
- **For S-G7 now:** the untracked `FRSoundnessFrL.lean` (in progress) defines `PendLc`
  against `Σ_i β^i t_i`.
  - M1 surfaces where `PendLc` must meet RS0's `PendBad` at `j = 1`, whose `trueL 1` uses the
    plain-`eq` `gL`.
  - M2 surfaces in whichever `M̃_free` its `ZLM` matrices use: the circuit walk matches V; the
    identity matches A.6 and `linM_free`.
