# S-G6 RESULT (pass 1): RS0, E, Lr, the E4 end → RS0 link, `ExtIface`; a verifier finding

Base HEAD `d332644`. Build tree `logs/fr-build-SG6` (copied from `fr-build-SG5`; `snap.sh` takes
HEAD's sources and symlinks `FRSoundnessFr*` to the worktree). Logs in `logs/S-G6/`. Journal:
`S-G6-JOURNAL.md`. Every lean/lake command ran in a capped scope (16G for builds, 8–12G for the
scratch bisections) with a `timeout`. Nothing is committed. No existing module was edited.

**Status.** Multi-pass stage. Pass 1 delivers item 1 (RS0 and `RejF`'s slice part), item 2 (E,
all six phases), item 3 (Lr), the E4 end → RS0 link, and ruling 1's `ExtIface` with
`hExt_of_iface`. Items 4–9 remain (§5). **Z is blocked by a verifier defect** (§4.1).

`lake build FRSoundnessFrPend FRSoundnessFrExt` is green (2,312 jobs; it builds all four new
modules). No `sorry`.

- **Axioms** (`logs/S-G6/axioms.log`, all 74 theorems of the four modules): `propext`,
  `Classical.choice`, `Quot.sound` only (65 use all three, 4 `[propext, Quot.sound]`, 2
  `[propext]`, 3 none).
- **Source rule** (`logs/S-G6/source-rule.log`): 156 files, 0 findings.
- **Imports for `FR.lean`** (its owner): add `import FRSoundnessFrPend` and
  `import FRSoundnessFrExt` (they import `FRSoundnessFrE` → `FRSoundnessFrRS0` →
  `FRSoundnessFrRS`). Every new declaration name was grepped against every `FR*.lean`: no clash.

## 1. What was built (code lines from `scripts/loc.py`, `logs/S-G6/loc.log`)

| Module | Total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrRS0` | 228 / 137 / 18 | the inner weights **`cwL`** (`rsW` on the log, through the value-level `cwF`), **`alphaL`** (`α_j` from the slices), **`trueL`** (the same weights on the true slices); a claim's **binding** `ok κ es j v` with `OkReads`; **`PendBad`**, **`DPend`** (E4 end's doom: far, `¬PubOK`, a pending claim false), **`RejRS`** (`RejF`'s slice part, from 313); **`habs_RS0`**; `rejOK_at` (a check from a position on is a `RejOK`), **`rejRS_ok`**; reads (`dPend_reads`, `rejRS_reads`, `fF_same`, `pubOK_same`, `farL0_same`, `trueL_same`) |
| `FRSoundnessFrE` | 443 / 307 / 39 | `e_unit_pos`; the outer half at E (`e_zc_hfin`, `e_habs_outer`, `e_single_outer`, `e_habs_end`, `e_rejEnd_ok`) and at Lr (`lr_habs_outer`, `lr_single_outer`, `lr_habs_end`); the inner half with Lr batched in: **`c4E`**, `wInn`, **`wE4`**, **`T4E`**, `trueSum_T4E`, **`BatBadE`**, **`D4E`**, **`RejInE`**; **`single_batchE`** (E3, via `batch_count4`), **`habs_innerE`**, **`single_innerE`**, `inner_appendE`, **`rejInE_ok`**, **`D4E_reads`**; E4 end: `okE`, `rE4`, **`RejE4`**, **`PendE`**, **`habs_E4end`**; `card_filter_imp` |
| `FRSoundnessFrPend` | 123 / 81 / 9 | **`okRS oZ oSh`** (Lc `v = v_β` with `vBetaL`, E `okE`; Z, Sh parameters), `okRS_reads`; **`trueL_three`** (RS claim 4's true value is `ẑ(r′)`), **`pendE_pendBad`** |
| `FRSoundnessFrExt` | 125 / 73 / 8 | **`StmtN`**, **`Stmt`**, `stmt_reads`; **`ExtIface`**; **`hExt_of_iface`** |
| **Total** | 919 / 598 / 74 | |

### The statements

```lean
-- FrontObl.habs at RS0's absorb (312), for any bindings that read before 312
theorem habs_RS0 {ok : Kind → Log → ℕ → F → Prop} (hok : OkReads ok) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = 312) (hd : DPend ok L es) :
    RejRS ok L (es ++ [x]) ∨ DRS0 L (es ++ [x])
theorem rejRS_ok {ok} (hok : OkReads ok) (hp : fsItems[312]? ≠ some .squeeze) : RejOK (RejRS ok)

-- E3 (264): a wrong M triple or a false Lr claim (pending since Lr3) escapes for ≤ 3·2^128 κ_E
theorem single_batchE (L es : Log) (hl : es.length = 264) :
    (univ.filter fun d => (EndBad rows 21 23 lrOn 221 L es ∨
        BatBad Layout.lRows 15 23 lrOn 178 L es) ∧ ¬ BatBadE rows L (ext1 es d)).card ≤ 3 * 2 ^ 128
theorem habs_innerE {L es : Log} (x) (hl : es.length = 265) (hb : BatBadE rows L es) :
    D4E rows L (es ++ [x])
theorem single_innerE (L es : Log) (hchk : …Chk2 265 … c4E L es j) :
    (univ.filter fun d => D4E rows L es ∧ ¬ D4E rows L (ext1 es d)).card ≤ 2 * 2 ^ 128
theorem habs_E4end {L es : Log} (x) (hl : es.length = 311) (hd : D4E rows L es) :
    RejE4 rows L (es ++ [x]) ∨ PendE L (es ++ [x])
theorem pendE_pendBad {oZ oSh} {L es : Log} (h : PendE L es) : PendBad (okRS oZ oSh) L es

-- ruling 1
def ExtIface (S : Submission) (vk : Digest) (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)
    (St : Log → Log → Prop) : Prop :=
  ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
    IsChain L j → pfStart + 14 ≤ (entriesOf L (pathOf L j)).length →
    ¬ farL (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) 0 →
    St L (entriesOf L (pathOf L j)) → LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w
theorem hExt_of_iface (hI : ExtIface S vk W₀ c₀ St) (hSt : Reads 3 St)
    (hD2 : DF 2 = fun L es => farL (kindOf es) L es 0 ∨ ¬ St L es) : <finalLaw_of's hExt>
```

`St` for the front is `Stmt fin SL`: a node's `StmtN fin κ L es = truthZN ∧ truthS1N ∧ truthLr ∧
truthE fin ∧ PubOK`; a leaf's part `SL` is a parameter (§6, question 2).

## 2. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile
-Dprofiler.threshold=100`), logs `logs/S-G6/time-<module>.log`, wall and max RSS in
`time-<module>.rss`:

| Module | Wall (≈ 3.6 s import) | Type checking | Max RSS |
|---|---|---|---|
| `FRSoundnessFrRS0` | 7.5 s | 186 ms | 2.77 GB |
| `FRSoundnessFrE` | 9.9 s | 498 ms | 2.78 GB |
| `FRSoundnessFrPend` | 6.5 s | 34 ms | 2.76 GB |
| `FRSoundnessFrExt` | 6.3 s | 64 ms | 2.76 GB |

No `decide` over a program, table or the item list. The `decide`s: `rsPtsL_length`'s bounds
(`3 < 4`), `not_batBadE_leaf` (`P30.isNode ≠ true`), `trueL_three`'s `(3 : Fin 4) < 4`.
Positions come from `fsStarts_eq`/`fsRanges_eq` by `rfl`; the item shapes at 263, 265 + 2j and
312 are hypotheses (`e_rejEnd_ok`, `rejInE_ok`, `rejRS_ok`), for the assembly's classification.

**The OOM** (journal, item 2): the first `FRSoundnessFrE` was killed by the 16G scope. Cause: the
**kernel**, not the elaborator. `simp` with `rfl`-lemmas (`Matrix.cons_val_*`, full `simp` on
`#[a, b].getD i`) leaves definitional casts; checking them against a concrete `trueSum … 23`
lazily unfolds the true sum over `2^23` cells. Fixed by doing the algebra over abstract values
(`batch_count4`) and rewriting with generic `rfl` lemmas (`innerExpr_eval2`, `arrGetD_pair0/1`,
`rE4_def`). The same lesson as S-G5's `congr 1`: never let a concrete claim meet a cast.

## 3. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `alphaL`, `trueL` | `alphaL_true`: with RS0's truth, `α_j` is the true value | `alphaL_zero`: zero slices give `0` |
| `cwL` | `cwL_three`: claim 4's weight is the packing basis | (`alphaL_zero`) |
| `PendBad` | `not_pendBad_true`: bindings at the true values never fail | `pendBad_false`: a refusing binding fails at claim 1 |
| `RejRS` | (`habs_RS0`'s `RejRS` branch) | `rejRS_false`: from 313 a refusing binding is rejected |
| `BatBadE` | `not_batBadE_leaf`: never on a leaf | `batBadE_of_ne`: a false batched claim on a node is E3's doom |
| `c4E` | `c4E_of_lr_zero`: with `v_L = 0` it is the unit's three-claim batch | — |
| `PendE` | — | `not_pendE`: E4 end's value `= ẑ(r′)` is not pending |
| `okRS` | `okRS_one`: Lc's binding accepts `v_β` | `not_okRS_one`: it refuses any other value |
| `vBetaL` | — | `vBetaL_zero`: a zero L3 message gives `0` |
| `ExtIface` | `extIface_false`: it asks for a witness only where `St` holds | — |
| `Stmt` | `stmt_node`: on a node it is `StmtN` | `not_stmt_leaf`: a false leaf part makes a leaf's statement false |
| positions | `e_unit_pos` (`fsStarts_eq`, `fsRanges_eq`), `phOf_two` | — |

## 4. Findings, deviations and decisions

1. **Verifier defect: `finZ` binds nothing to RS claim 1 (blocking for Z; not this track's
   module).** BLUEPRINT A.9's `finZ` row (line 1126) and the "Claim values" ratification (line
   1512) say the `α_j` "are computed, not asserted, and bound where they are used: `finZ`
   (`α_Z = P^z*(λ)`)". The implemented `finZ` (`FRVIRFinals.lean:140`) ends with `.assertEq
   (b + 13) (claimN fi "Z3")` (the `eq·â·b̂ = c_Z` check) and exports `(outsOf fi "Z2").getD 2 0`
   (`P^z*(λ)`), but no later field reads `ex[1]` (only `lrEx` reads `ex`, at index 4), and no
   field reads `fi.zhat.getD 0 0` (`α_Z`). So on an accepted run nothing relates RS claim 1's
   slices to Z2's message: **the Z c-claim `ẑ(r, λ) = P^z*(λ)` is never checked.** A cheating
   prover can send any `P^z*` that makes Z2's skip check pass, and RS0's slices for claim 1 are
   then unconstrained. The fix is one op in `finZ`: `.assertEq ((outsOf fi "Z2").getD 2 0)
   (fi.zhat.getD 0 0) allK` (then `flag_finZ`/`exec_finZ`, the program dumps and `piSize`-free
   controls follow). Until then RS0's binding for claim 1 is a parameter `oZ` of `okRS`, and the
   Z phases' `DF` cannot be completed (`hFront` would need a check the verifier does not make).
2. **E3 batches four claims, not six.** `κ_L` is drawn at Lr3, before E, so Lr's three claims
   enter `finE` (iii) as one value `v_L = â_L + κ_L b̂_L + κ_L² ĉ_L`; as a polynomial in `κ_E`
   the batch has degree 3. Lr's pending doom is its `BatBad` (`v_L` false), which `single_batchE`
   consumes. The count is `3·2^128`, below §5.2's row (S-G5 planned `k = 5`).
3. **`D4E` is guarded by `lrOn`.** On a leaf E4's rounds are dummies and `D2`'s claim is the
   (asserted-zero) end message's batch; no doom produces `D4E` there, and the guard makes
   `habs_E4end` hold for every kind.
4. **RS0 is generic in the bindings.** `habs_RS0` and `rejRS_ok` take any `ok` that reads before
   312. `okRS` fixes Lc's and E's; Z's waits for finding 1, Sh's for item 4 (it is
   `c_Sh = (w_out + w_in)·v`, `finSh` (ii)).
5. **`ExtIface` keeps `¬ far₀`** although `LigeritoOut.close 0` implies it: it matches ruling 1's
   wording (`¬ far₀ ∧ Stmt ∧ LigeritoOut`), and it costs the extractor nothing.

## 5. Handover: what is left, in order

Positions: Z1 3–12, Z2 13–14, Z3 15–66, Zend 67, L1 68, L2 69–96, L3 97, L3β 98, S1 99–113,
S2 114–169, Lr1 170–177, Lr2 178–207, Lrend 208, Lr3 209, E1 210–220, E2 221–262, Eend 263,
E3 264, E4 265–310, E4end 311, RS0 312, RS1 313–316, B′ 317, P1.0 318.

Done (pass 1 of S-G5 and S-G6): RS0, RS1, B′, the handoff, E1–E4 end, Lr1–Lr3, the E4 end → RS0
link, `ExtIface`.

1. **S (11–12)**: `truthS1N`/`shift_sound_node`; the `eqAtR` → `mle`/`shWM` bridge (INT-3 open
   item 3), in a new module; S1's `hfin` by `hfin_seq` (`26 + 9`); S2's rounds with
   `D2_single` (use `card_filter_imp`/`batch_count4`-style abstract lemmas against the kernel
   lesson of §2); S2's end: the binding `oSh κ es v := c_Sh = (w_out + w_in)·v` on the log and its
   `OkReads`; the pending-claim bridge `S's doom ⇒ PendBad (okRS oZ oSh)` at claim 3 (as
   `pendE_pendBad`: `trueL` at claim 3 is `ml_claim_split` of `ẑ` at Sh's point).
2. **L (7–10)**: L1 `batch_count` at `k = 1`; L2 `D2_single`; L3 `lin_final_kinds`; L3β
   `batch_count` at `k = 8`; the pending Lc claim's bridge to `PendBad` at claim 2 (`v_β` vs
   `trueL … 1`, `ml_claim_split` with `cwL`'s `eqTab` of L2's challenges 0–6).
3. **Z (3–6)**: blocked on finding 1 for the c-claim. The rest (zerocheck over `targetS`,
   `skip_pair_bad_le` at Z2, `D3_single`/`z3_phase` at Z3, `finZ` at Zend) can proceed; the
   binding `oZ κ es v := v = P^z*(λ)` once `finZ` asserts it.
4. **Assembly**: `DF k` (26 cases; `DF 2 := far₀ ∨ ¬ Stmt fin SL`, `DF 22 := DPend (okRS oZ oSh)`
   with the earlier pending parts, `DF 23 := DRS0`, `DF 24 := msD DRS0 DRS1 312 4`,
   `DF 25 := DB`); `RejF` by `rejOK_or` of `RejEnd`s, `RejInE`, `RejE4`, `RejRS (okRS …)`, the
   Z/L/S checks; `FrontObl`'s fields by one checked classification of positions `0 … 317` (as
   `tailCls_check`), discharging the `fsItems` hypotheses of `e_rejEnd_ok`, `rejInE_ok`,
   `rejRS_ok`; `FrontChainStab` from `Reads.chain` (`dPend_reads`, `D4E_reads`, `batBadE_reads`,
   `rejRS_reads`, `stmt_reads`). E's phases plug in as: 17 `e_zc_hfin`; 18 `e_habs_outer`,
   `e_single_outer`; 19 `e_habs_end`; 20 `single_batchE`; 21 `habs_innerE`, `single_innerE`
   (its `hchk` from `chk_of_not_rejInE`); 22 `habs_E4end` + `pendE_pendBad`; 23 `habs_RS0`;
   24 `hfin_RS1`; 25 `single_B`, `handoff_B`.
5. **`hW0`**, **`hStart`**, **`hFront`** (S-G5 §5 items 8–10; `hFront` now also needs: `finE`
   (iv)–(v) ⇒ `¬ RejE4`, `finLc` (iii) and `finE` (v) ⇒ `¬ RejRS (okRS …)` via `exec_finRS`'s
   `rsAlpha` = `alphaL` (register views of RS0's message and of `rsW` = `cwL`, with
   `impl.eqZ = eqZS` from `implC_meets`)).
6. **`kstate_front`**: `kstate_of_front` with `FrontObl`, and `finalLaw_of` with
   `hExt_of_iface` (leaving `ExtIface`) and `hAcc_of_fin` (`hFront`, `hStart`, `hW0`).

## 6. Open questions

1. **Finding 1** (`finZ`): who fixes it (S-F / S-0's `FRVIRFinals`)? Until then the Z part of the
   front cannot be closed, and the entry's verifier is unsound for the Z c-claim.
2. **The leaf's statement** in `Stmt`: S-H2l/S-E should fix `SL` (the leaf's Z truth with chain
   targets, `truthZ (fun _ => Chain.chainTarget) n`, and its chain links/shift truth on the log),
   with `Reads 3`. `ExtIface` is stated for any `St`, so they can target it now.
3. `FR.lean`'s owner: add `import FRSoundnessFrPend` and `import FRSoundnessFrExt`.
