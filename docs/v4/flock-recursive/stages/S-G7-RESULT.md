# S-G7 RESULT (pass 1): S proved (with the `eqAtR` bridge and `oSh`), Z and the leaf's L as units; handover

- **Base.** HEAD `3175db2`.
- **Build trees.**
  - `logs/fr-build-SG7`: `snap.sh` symlinks every `FRSoundnessFr*` to the worktree. Its `.lake` came from `fr-build-INT4`, so nothing was rebuilt.
  - `logs/fr-build-SG7z`: the fork's tree for items 2–3.
- **Records.** Logs are in `logs/S-G7/`. The journal is `S-G7-JOURNAL.md`; the fork's notes are `logs/S-G7/ZL-notes.md`.
- **Constraints.** Every lean/lake command ran in a capped scope with a `timeout`. Nothing is committed.

## Status

This is a multi-pass stage.

**Delivered:**
- **Item 1 (S): complete.**
  - S1's charge.
  - S2's `habs`, rounds, checks and reads.
  - The `eqAtR` → weight bridge (INT-3 open item 3).
  - The concrete binding **`oSh`**.
  - S's pending claim into RS0's `PendBad`.
- **Item 3 (Z): its phase units** (Z1, Z2, Z3, Zend) and the concrete **`oZ`**. `pendZ_pendBad` is open.
- **Item 2 (L): the leaf's units** (L1, L2, L3, L3β).
  - The node's L3/L3β bindings are parked under R-V-M1/M2, now blueprint 3.16, which INT-5 implements.
  - `pendLc_pendBad` is open.
- **Item 7:** done (the headers).

**Not done:** items 4–6 (assembly, `hW0`/`hStart`/`hFront`, `kstate_front`) and the `accept_fields` strengthening (R-V-m2). See §5.

**Build.** `lake build FRSoundnessFrS FRSoundnessFrL FRSoundnessFrExt` is green (2,343 jobs, no `sorry`). `FR.lean` is untouched.

**Imports for `FR.lean`'s owner.** Add:
- `import FRSoundnessFrS`, which imports `FRSoundnessFrSh` → `FRSoundnessFrPend`, `FRSoundnessFrExt`, `FRVerifierImplNode`, `FRSoundnessAccEq`;
- `import FRSoundnessFrL`, which imports `FRSoundnessFrZ`.

## 1. What was built (code lines from `scripts/loc.py`, `logs/S-G7/loc.log`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundnessFrSh` (new) | 762 / 613 / 46 | S2's weights `wLeaf`, `wNode` (`slotT`, `shL`, `lkW`, `shN`, `famW`), the residuals `resSum`, `resLeaf`, `resNode`; **`sh_sum_leaf`**, **`sh_sum_node`**; **`ShHoldsL`**, **`res_ne_leaf`**, **`res_ne_node`** (`resNode_src`, `srcB_inj`); **`mle_ofFn_split`**; **`final_leaf`**, **`final_node`** (`sum_chainLk`, `linkSum_eq`, `shiftEqS_eq`); S1's Schwartz–Zippel row `selC`, `DoomS`, `bS`, **`doomS_step`**, `sum_bS` |
| `FRSoundnessFrS` (new) | 692 / 522 / 55 | readers (`tauL`, `thL`, `ksL`, `rbL`, `rpL`, `bndL`, `sbL`, `hbL`); **`c0S`**, `c0S_eq`; **`TS`**, **`trueSum_TS`**; **`truthSK`**, **`S2Bad`**, **`s1_hfin`**; **`D2S`**, **`habs_S2`**, **`single_S2`**, **`RejS2`**, **`rejS2_ok`**, **`D2S_reads`**; **`wSumL`**, **`oSh`**, `wSumL_eq`, **`trueL_two`**, **`endS`**, **`pendS_pendBad`**, `oSh_reads`; controls |
| `FRSoundnessFrZ` (new, fork) | 633 / 426 / 53 | Z1–Zend as units over the matrices parameter `ZLM` (`ZHolds`, `ZEnd`, `Z2D`, `Z2Bad`, `D3Z`, `PendZ`, `ZendBad`, `RejZ`); **`oZ`** (`v = P^z*(λ)`), `oZ_reads`; `aStar_eq`/`bStar_eq` (Zend → L1) |
| `FRSoundnessFrL` (new, fork) | 473 / 335 / 38 | L1–L3β (`L1Bad`, `D2L`, `RejL2`, `RejLc2`, `L3Bad`, `PendLc`; L3/L3β leaf only) |
| `FRSoundnessFrPend`, `FRSoundnessFrRS0` | header text only | item 7 |
| **Total new** | 2,560 / 1,896 / 192 | |

### S's statements (the forms the assembly plugs in)

```lean
-- S1 (range (98, 15), positions 99…113): §5.2 row (nb + 10 + J − 1)/2^128 — 35 on a node
theorem s1_hfin {Dk} {Bg} (hBg : Reads 99 Bg)
    (hprev : Dk (phOf 98) = fun L es => Bg L es ∨ ¬ truthS L es)
    (hfin : Dk (phOf 99) = msD (Dk (phOf 98)) (fun L es => Bg L es ∨ S2Bad L es) 98 15)
    (L es₀ : Log) (hl : es₀.length = 99) : condCount (DPos (Dp Dk)) L es₀ 15 [] ≤ deltaR
-- S2 (rounds from 114; nrS κ = m − 4 real rounds)
theorem habs_S2 {L es} (x) (hl : es.length = 114) (hb : S2Bad L es) : D2S L (es ++ [x])
theorem single_S2 (L es) (hchk : ∀ j, es.length = 114 + 2 * j + 1 → j < nrS (kindOf es) →
    Chk2 114 16 readF (fun d => chF d 0) c0SL L es j) :
    (univ.filter fun d => D2S L es ∧ ¬ D2S L (ext1 es d)).card ≤ 2 * 2 ^ 128
theorem rejS2_ok (habs2 : ∀ j < 28, fsItems[114 + 2 * j]? ≠ some .squeeze) : RejOK RejS2
theorem D2S_reads : Reads 170 D2S
-- S2's end: the pending Sh claim is RS0's PendBad at claim 3
def oSh (κ : Kind) (es : Log) (v : F) : Prop := claimSL κ es = wSumL κ es * v
theorem endS {L es} (h : D2S L es) (hl : 170 ≤ es.length) :
    ¬ oSh (kindOf es) es (trueL (kindOf es) L es 2)
theorem pendS_pendBad {oZ} {L es} (h : D2S L es) (hl : 170 ≤ es.length) :
    PendBad (okRS oZ oSh) L es
theorem oSh_reads : ∀ κ es es', Agree es es' 312 → oSh κ es = oSh κ es'
```

- **`truthS`.**
  - A node: `truthS1N` (INT-3).
  - A leaf: `ShHoldsL (m−14) (zNode …) (sbL …) (hbL …)`. Block `y+1`'s `d` (positions `520 + σ`) is block `y`'s `h_out` (`256 + σ`); block 0's `d` is the start `s` (`hdr` bytes 16–47); the last block's `h_out` is `h` (`stmt` bytes 1–32). This is exactly what `finSh` checks for a leaf.
- **`D2S` as background.** `D2S` past S2's end reads before 170. It can therefore stay in the background terms from Lr1 on, and be converted to `PendBad` at RS0 by `pendS_pendBad`. The DF design is the same as E's `PendE`.
- **`wSumL` and `c0S`.** Both are written as `relSh` writes them, with `specC`'s operations: `shiftMaskS`, `eqPoint`, `shiftEqS`, `slotWS`, `linkWAllS` or `0^8`, `linkSum`, `shiftTargetS`. So `hFront` reduces to register views plus `implC_meets`.

### Z and L (fork): the phase lemmas

Exact statements are in `logs/S-G7/ZL-notes.md`.

| Phase | Lemma | Shape | Count |
|---|---|---|---|
| Z1 | `z1_hfin` | `Reads 3 Bg`, `hprev : Dk (phOf 2) → Bg ∨ ¬ZHolds M`, `msD` `hfin`, `hfinI` | 19/2^128 |
| Z2 | `z2_habs` (13), `z2_single` (14) | `ZEnd ⇒ Z2D`; `Z2D` escapes | 126·2^128 |
| Z3 | `z3_habs` (15), `z3_single` | `Z2Bad ⇒ D3Z ∨ PendZ`; rounds | 3·2^128 |
| Zend | `zend_habs` (67) | `D3Z ⇒ RejZ ∨ ZendBad` | — |
| L1 | `l1_single` (68) | `ZendBad ∧ ¬L1Bad` | 1·2^128 |
| L2 | `l2_habs` (69), `l2_single` | `L1Bad ⇒ D2L`; `D2_single` with `chk_of_not_rejL2` | 2·2^128 |
| L3 | `l3_habs` (97, leaf) | `D2L ⇒ RejLc2 ∨ L3Bad` | — |
| L3β | `l3b_single` (98, leaf) | `L3Bad ∧ ¬PendLc` | 7·2^128 |

- No phase exceeds its §5.2 row.
- The Rej parts mirror the following relations (for `hFront`):
  - `RejZ`: `relZ`'s first conjunct.
  - `RejL2`: `finLc` (i) and L2's round asserts.
  - `RejLc2`: `finLc` (ii) on a leaf.
- The fork's design is parametric in `ZLM` (the kinds' block matrices `Ak`, `Bk`, `Ind`, and the target bits `Et`), with hypotheses `ZLM.Bits` and `ZLM.IndKinds`. Instantiating it is §5, item 2.

## 2. Build and kernel times

Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile -Dprofiler.threshold=100`). Logs are `logs/S-G7/time-<module>.log` / `.rss`.

| Module | Wall (≈ 3.9 s import) | Type checking | Max RSS |
|---|---|---|---|
| `FRSoundnessFrSh` | 17.3 s | < 0.1 s (below threshold) | 2.86 GB |
| `FRSoundnessFrS` | 19.6 s | 2.13 s | 3.10 GB |
| `FRSoundnessFrZ` (fork) | 11.7 s | 0.68 s | 2.79 GB |
| `FRSoundnessFrL` (fork) | 11.0 s | 0.40 s | 2.78 GB |

- **No `decide` over a program, table or the item list.** Positions come from `fsStarts_eq`/`fsRanges_eq` by `rfl`. The `decide`s that remain are small and local:
  - `e2` in `sum_bS` (a 30-element range filter);
  - `eqAtR_zeros4` (16 cases of a 4-bit `testBit`);
  - `nbS_le`;
  - `nJ ≥ 1`;
  - `rsPtsL_length` bounds.
- **No concrete table meets a cast.** All the algebra is over abstract `range` sums.

## 3. Controls

| Definition | Positive | Negative (non-vacuous) |
|---|---|---|
| `ShHoldsL` | `shHoldsL_zero` (zero table, zero digests) | `not_shHoldsL_start` (start bit 1 against a zero table) |
| `slotT` (S2's slot weight) | `slotT_cube` (at a cube `θ = σ₀` it picks `b + σ₀`) | `slotT_off` (`0` below the slot) |
| `c0S` | `c0S_node` (a node's target is `0`) | (`c0S_eq`: a leaf's is `eq(τ,last) h̃ + κ s̃`) |
| `oSh` | (`endS`/`pendS_pendBad`: it fails at the true value on a doomed chain) | `oSh_unique` (with nonzero weight it accepts one value) |
| `D2S` | `habs_S2` | `not_D2S_short` |
| `resLeaf`/`resNode` | `sh_sum_*` (the residual is the true sum minus the target) | `res_ne_*` (a failed truth gives a nonzero table) |
| Z, L (fork) | `zHolds_id`, `zEnd_one`, `oZ_self`, `indKinds_ex` | `not_zHolds_one`, `not_zEnd_id`, `not_oZ`, `not_indKinds_id`, `not_pendLc_node`, `not_l3Bad_node` |

## 4. Findings, deviations and decisions

1. **The node's Lc claim (R-V-M1/M2, ruled in blueprint 3.16).**
   - The fork found it independently.
   - The node's L3/L3β bindings (`RejLc2`, `L3Bad`, `PendLc`) carry `isNode = false` and are not stated for a node.
   - INT-5 makes the verifier side (`finLc`, `relLc`, `rsWeight`'s `β` operand, `linM_free`). Write the node's L against those relations.
2. **R-V-m2: `accept_fields` does not pin `zh`/`exk`.**
   - `oZ` and `oSh` are defined on the log (`v = P^z*(λ)`; `c_Sh = (w_out + w_in)·v`), not on `accept_fields`.
   - Their `hFront` discharge needs `accept_fields` restated with `zh := (fin.finRS ⟨outs, [], #[]⟩ b).2` and `exk` as the fold's exports. That is a statement change in `FRSoundnessAccSem`, an S-G module; it only adds information.
   - Not done this pass (§5, item 3).
3. **S1's charge counts only the read coordinates.**
   - P30/N30 draw 18 `τ` coordinates and read 16.
   - Charging all 30 drawn coordinates with a degree-9 `κ_s` would give 37 on a node, against §5.2's `26 + 9`.
   - `selC`/`bS` give 0 to the unread ones, so the node's charge is 35 (= the row), L32's 29 and P30's 27.
4. **The leaf's statement `SL`** (S-G6 open question 2). Proposal, all on the log:
   - `ShHoldsL` (this pass) for S;
   - the fork's `ZHolds M` with a leaf's `ZLM` for Z;
   - no separate L truth.
   - Both read before 3, so `Stmt fin SL` keeps `Reads 3`.
5. **`truthS` versus `StmtN`.** `StmtN` already has `truthS1N`, which is `truthSK` on a node, so no change is needed there.
6. **No phase exceeds its §5.2 row**, and every doom read is local (`Reads`/`Same` lemmas). There is no stability obstruction.

## 5. Handover: what is left, in order

Positions: Z1 3–12, Z2 13–14, Z3 15–66, Zend 67, L1 68, L2 69–96, L3 97, L3β 98, S1 99–113, S2 114–169, Lr1 170–177, Lr2 178–207, Lrend 208, Lr3 209, E1 210–220, E2 221–262, Eend 263, E3 264, E4 265–310, E4end 311, RS0 312, RS1 313–316, B′ 317, P1.0 318.

1. **Z's bridge: `pendZ_pendBad`.**
   - Prove `trueL κ L es 0 = (pzT L es).eval (lamL es)`. The split is `u′ = b + 2v` against `σ + 64b + 128v`, as in `quirky_claim_split`; follow `trueL_two`/`trueL_three`'s pattern.
   - Then `PendZ ⇒ PendBad (okRS oZ oSh)` at index 0.
2. **Instantiate `ZLM` for the node and the leaf.**
   - Prove `truthZN ↔ ZHolds` and `peL = targetS`.
   - Prove `ZLM.Bits` and `ZLM.IndKinds`.
   - Match `RejLc2` to `walkAB`/`maskRows` (`lin_walk_adjust`) and package its `RejOK`.
   - The leaf's `pendLc_pendBad` needs `Ind κ 0 ≡ 1` on a leaf's blocks; then `Σβ^i tL = zfL 0 = trueL 1`.
   - The node's L waits for INT-5 (3.16).
3. **`accept_fields` (R-V-m2).** Restate it with the witnesses its proof uses (`AccSem:196`), and list it as a statement change.
4. **Assembly.**
   - **`DF k`.** For each phase, `DF k := Bg_k ∨ U_k`.
     - Backgrounds: `far₀`, `¬PubOK`, the not-yet-reduced statement parts (`¬truthS`, `¬truthLr`, `¬truthE`), and the pending parts.
     - Pending parts: `PendZ` from Z3 on (`Reads 15`); the leaf's `PendLc` from L3β on (`Reads 99`); `D2S` from Lr1 on (`Reads 170`); Lr's `BatBad` into E3; `PendE` at E4 end.
     - Each lemma's `hprev`/`hfin` is a function equality or implication. Prove the equalities by `funext` and `propext` reordering of the disjunction.
     - At 312, `DF 22 → DPend (okRS oZ oSh)` by `pendZ_pendBad`, `pendLc_pendBad`, `pendS_pendBad` and `pendE_pendBad`. `habs_RS0` takes `DPend` as a hypothesis, not an equality.
   - **`RejF`.** `rejOK_or` of `RejZ`, `RejL2`, the leaf's `RejLc2`, `RejS2`, the `RejEnd`s, `RejInE`, `RejE4` and `RejRS (okRS oZ oSh)`.
   - **`FrontObl`.**
     - Classify positions 0 … 317 with one checked list, as `tailCls_check` does.
     - Discharge the `fsItems` hypotheses of `rejS2_ok`, `rejZ_ok`, `rejL2_ok`, `rejInE_ok`, `e_rejEnd_ok` and `rejRS_ok` from it.
   - **`FrontChainStab`.** From `Reads.chain`, using `D2S_reads`, the fork's `*_reads`/`zDooms_log`/`lDooms_log`, `D4E_reads`, `dPend_reads` and `stmt_reads`.
5. **`hW0`, `hStart`, `hFront`** (S-G5 §5, items 8–10). `hFront` additionally needs:
   - `relSh` ⇒ `¬ RejS2` and `oSh` at `alphaL … 2`. `relSh`'s first conjunct is `c0S` and its second is `claimSL = wSumL·α`. Use `implC_meets` for `shiftTarget`, `shiftMask`, `linkWAll`, `slotW` and `shiftEq`, and the register views of S1/S2.
   - `relZ` ⇒ `¬ RejZ` and `oZ`.
   - `finE` (iv)–(v) ⇒ `¬ RejE4`.
   - `finLc` ⇒ L's parts.
   - All of these through the strengthened `accept_fields`.
6. **`kstate_front`.** Compose `kstate_of_front` with `FrontObl`, and `finalLaw_of_run`/`hAcc_of_fin` with `hExt_of_iface`. Only `ExtIface` (with `SL`) and the `implC` facts should remain.
7. **Final checks.** Run the axiom check (`kstate_front`) and the source rule.

## 6. Checks

- Axioms (`logs/S-G7/axioms.log`): all 101 theorems of `FRSoundnessFrSh`/`FRSoundnessFrS` use only `propext`, `Classical.choice` and `Quot.sound` (73 use all three, 18 `[propext, Quot.sound]`, 10 `[propext]`).
- The fork's 91 theorems are in `axioms-ZL.log`, with the same three only.
- Source rule (`logs/S-G7/source-rule.log`): 163 files, 0 findings.
- Name clashes: every new declaration was grepped against every `FR*.lean`.
  - Fixed `sum_range_mul` → `sum_range_mul_split`.
  - The fork fixed `rbL` → `rbLc`.

## 7. Open questions

1. Is `ShHoldsL` the leaf statement S-H2l/S-E want in `SL`? It is what `finSh` checks for a leaf: `d` at 520 against `h_out` at 256, with `s` and `h` as boundaries.
2. Who strengthens `accept_fields`: S-G7's next pass, or INT-5 together with `relLc`?
