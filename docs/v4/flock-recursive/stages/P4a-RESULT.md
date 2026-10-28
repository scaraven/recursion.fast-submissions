# P4a RESULT (pass 1): Z, L, S, Sh at revision 4.1: the names, the segment deltas, `lastOps`; handover

- **Base.** HEAD `7e14be6`. **Build tree** `logs/fr-build-P4a` (a copy of `fr-build-SG13`;
  `MINE.txt` lists the four new modules; `b.sh` = `snap.sh` + capped build). Logs in `logs/P4a/`.
  Journal: `P4a-JOURNAL.md` (§0 is the names table, written first for R4).
- **Constraints.** Every lean/lake command ran in the 16G scope (12G for single files) under
  `timeout`. No sub-agents. Nothing committed. No existing module was edited and no statement
  changed. All new names are in namespace **`FR.Snd.P4a`** (no other file uses it).

## Status

| Item | State |
|---|---|
| The `Rej*`/doom names for R4 (stub module first) | **Done**: `FRSoundness4P4aNames`. Real definitions, no placeholders (§2). |
| `SegHolds` from the truths | **Done**: `segHolds_of_truths`, `chainEnd_of_truths`. |
| `targetS` range factor: Z's statement on a segment's used blocks | **Done**: `EtSeg`, `zlm4`, `zHolds_seg_block`. The `P^e` = `targetSSegS` bridge is open (§6, item 5). |
| Sh: successor masked at `L` | **Done**: `wSeg`, `resSeg`, `ShHoldsSeg`, `sh_sum_seg`, `shHoldsSeg_of_res`, `res_ne_seg`, `chainLinks_of_shHoldsSeg`. The `c0S` and `final` bridges are open (§6, items 1–4). |
| `pureRun` lemma for `lastOps` (S-F4 §7 Q3) | **Done**: `run_lastOps`, `lastVals_bit`, `lastSum`, `lastL_sum`. |
| The doom obligations (`Reads`, `habs`, `single`, `RejOK`, `hfin`, `stab`) for Z/L/S/Sh at `CKind` | **Not started**: they need the CKind foundation, which T4 is now building (§6, item 6). |
| Node half | Parametric (`indN`, `etN`, `wN`, `truthSN`) until S-E's Rev4 node maps exist (S-G13 F3). |

**Checks:**
- `lake build FR FRSoundness4P4aCtrl`: green (`logs/P4a/build-last.log`).
- **Axioms** (`logs/P4a/axioms.log`, 44 theorems): within `propext`, `Classical.choice`,
  `Quot.sound`; no `sorryAx`.
- **Source rule:** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`: 224
  files, 0 findings (`logs/P4a/source-rule.log`).

**Imports for `FR.lean`:** `import FRSoundness4P4aCtrl` (it pulls `FRSoundness4P4aSeg`,
`FRSoundness4P4aLast`, `FRSoundness4P4aNames`).

## 1. What was built (`loc.py`, `logs/P4a/loc.txt`)

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4P4aNames` | 355 / 163 / 0 | `mC`, `nbC`, `Wit`, `ZLM4` (+`Bits`, `IndKinds`), `nStmt`, `lastL`, `borrow`, `lb`, `bF`, `lastBits`, `EtSeg`, **`zlm4`**; `ansN`, `Wrong3n`, `D3n`, `Wrong2n`, `D2n`; Z: `zBk`, `mvZ`, `aZ`/`bZ`/`zZ`/`eZ`, `ZHolds`, `zres`, `zrL`, `ZEnd`, `peL`, `c0Z`, `pabT`, `pzT`, `PendZ`, `Z2Bad`, `Z2D`, `TZ`, `D3Z`, `rZ`, `aStar`, `bStar`, **`RejZ`**, `ZendBad`, `oZ`; L: `qL`, `rhiL`, `rbLc`, `IndF`, `rwL`, `zN`, `aLin`, `bLin`, `L1Bad`, `TL`, `D2L`, **`RejL2`**, `vM`, `zfL`, `PLc`, **`RejLc2`**, **`RejLcN`**, `L3Bad`, `tL`, `PendLc`; S: `tauL`, `rbL`, `rpL`, `bndL`, `sbL`, `hbL`, `pad18`, `endBits`, `c0S`, `nrS`, `c0SL`, **`RejS2`** |
| `FRSoundness4P4aSeg` | 325 / 229 / 16 | `shSeg`, `wSeg`, `resSeg`, **`ShHoldsSeg`**, **`sh_sum_seg`**, `shHoldsSeg_of_res`, `res_ne_seg`; `zBlkC`, `zNodeC`, `sbL_seg`, `hbL_seg`, **`chainLinks_of_shHoldsSeg`**; `mC6_q`, **`zHolds_blocks`**, `mvZ_seg`, **`zHolds_seg_block`**, `lastL_eq`, **`segHolds_of_truths`**, **`chainEnd_of_truths`**; `wS`, `TS`, `S2Bad`, `D2S`, `truthS` |
| `FRSoundness4P4aLast` | 277 / 212 / 19 | `bF_add`, `bF_mul`, `decMod`, **`borrow_inv`**, **`lastSum`**, `lastSum_eq`; `bitVals`, `chainVals`, `headVals`, `lastVals`, `length_flatMap_const`, `getD_flatMap`, `rd_vals`, `pureRun_flatMap`, `run_bits`, `rd_borrow`, `run_chain`, **`run_lastOps`**, `lastVals_zero`, **`lastVals_bit`**, `lastL_sum` |
| `FRSoundness4P4aCtrl` | 108 / 54 / 16 | the controls (§4) |
| **total** | 1,065 / 658 / 51 | |

## 2. The names (for R4), and how they differ from 3.x

All read the **chain kind** `kindOfC es` (`CKind`, byte 71) in place of 3.x's `kindOf es`. Positions
are 3.x's (S-G13 §0.1).

- **`P4a.RejZ M`**, **`P4a.RejL2`** (`= FR.Snd.RejL2`: kind-free), **`P4a.RejLc2 M`** (a segment),
  **`P4a.RejLcN M`** (a node), **`P4a.RejS2`**. Each reads only the log (and `M.Ak`, `M.Bk`, and
  through `c0Z`/`peL` `M.Et`); none reads the witness. R4 instantiates
  `M := zlm4 indN etN`.
- **`ZLM4.Et κ es t p` reads the log**: a segment's target is `EtSeg (lastL es)`, the chain target on
  blocks `t ≤ L`, `0` past (B-12). 3.x's `ZLM.Et κ t p` did not read the log.
- **`c0S`** has `endBits` in place of 3.x's `lastPad`: a segment's `L` bits (`lastBits`, the values
  `lastOps` computes), a node's `lastPad (nb) (18 − nb)` (as 3.x).
- **`nStmt es = idxOfF 24 (digestAt (msgAt es 1) 33) 0`** (what `lastOps` computes from `stmt`) and
  **`lastL es = (nStmt es + 2^18 − 1) mod 2^18`**.
- The dooms take **`zw : Wit`** (`CKind → Log → Log → ℕ → F`, T4's decoded `z = unpack f⁽⁰⁾`).
- **`D3n`/`D2n`** are 3.x's `D3`/`D2` with the round count read from the log (`nr : Log → ℕ`), since
  3.x's take `nr : Kind → ℕ` at the 3-kind `kindOf`. With `nr := fun es => r (kindOfC es)` they are
  `T4.D3 … r …`/`T4.D2 … r …` if T4's `ans3` reads `kindOfC` (I have not imported T4's unfinished
  modules; check at integration).

## 3. The main statements

```lean
theorem sh_sum_seg {Lb : ℕ} (hL : Lb < 2 ^ nb) (τ : Fin nb → F) (θ : Fin 10 → F) (κ : F) (z : ℕ → ℕ → F) (sb hb : ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), wSeg τ θ κ Lb y q * z y q =
      eqAtR τ Lb * thS θ hb + κ * thS θ sb + resSum nb 2 (resSeg nb Lb z sb hb) τ θ κ
theorem zHolds_seg_block (hk : kindOfC es = .seg κ) (h : ZHolds (zlm4 indN etN) zw L es)
    (ht : t < 2 ^ qL (.seg κ)) (hL : t ≤ lastL es) :
    Block.HoldsE (Block.blockR1CS Chain.chainTarget) (Block.targetVal F Chain.chainTarget) (zBlkC zw (.seg κ) L es t)
theorem segHolds_of_truths (hk : kindOfC es = .seg κ) (hbool : ∀ b, BlockR1CS.IsBool (zw (.seg κ) L es b))
    (hn : 1 ≤ n) (hcap : n ≤ κ.cap) (hL : lastL es = n - 1) (hZ : ZHolds (zlm4 indN etN) zw L es)
    (hS : ShHoldsSeg (nbC (.seg κ)) (n - 1) (zNodeC zw (.seg κ) L es) (sbL (.seg κ) es) (hbL (.seg κ) es)) :
    Rev4.SegHolds κ ⟨bytesAt (entAt es 0).1 87 32, bytesAt (msgAt es 1) 1 32, n⟩ (zBlkC zw (.seg κ) L es)
theorem chainEnd_of_truths … : chainEnd (bytesAt (entAt es 0).1 87 32) n = bytesAt (msgAt es 1) 1 32
theorem run_lastOps (so : ℕ) (R : Array Val) :
    pureRun impl κ inp (Rev4.lastOps so R.size) R [] = some (lastVals (digestAt inp.π (absOff 0 (so + 33))), true)
theorem lastVals_bit (D : Digest) (hk : k < 18) :
    (lastVals D).getD (40 + 3 * k) default = .f (bF (lb (idxOfF 24 D 0) k))
theorem lastSum (N : ℕ) : (∑ k ∈ range 18, if lb N k then 2 ^ k else 0) = (N + (2 ^ 18 - 1)) % 2 ^ 18
theorem lastL_eq (h : nStmt es = n) (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 18) : lastL es = n - 1
```

**Interface for X4.** `SegSoundLog (VsegC impl₀)` comes from `chainEnd_of_truths` once the chain
`¬ doom ⇒ ZHolds ∧ truthS` is in place, with:
- `hk` and `hbool` (T4's `zW` is `unpack`, so `unpack_boolean`);
- `hcap`/`hn` from `SegSoundLog`'s own hypotheses (`V_A`'s `1 ≤ nᵢ ≤ cap`);
- `hL` from `lastL_eq` with `nStmt es = v.n`, which R4 must read off the run: the segment program's
  `lastOps` digest is `digestAt π (absOff 0 (so + 33))` (`run_lastOps`), `segView`'s `n` is
  `rdLE64 π 81`, and since `n ≤ 2^18` both are `n` once `absOff 0 (so + 33) = 81` and the log's
  `msgAt es 1` is that `stmt`;
- `truthS` (at a segment) is exactly `ShHoldsSeg (nbC κ) (lastL es) …`, which `hL` turns into
  `hS`.

## 4. Controls (`FRSoundness4P4aCtrl`)

| Definition | Positive | Negative |
|---|---|---|
| `ShHoldsSeg` | `shHoldsSeg_zero` (the zero table); `shHoldsSeg_cut` (block `L + 1`'s inputs free: the mask) | `not_shHoldsL_cut` (3.x's unmasked `ShHoldsL` refuses the same table); `not_shHoldsSeg_start` |
| `EtSeg` | `etSeg_le` (chain target on `t ≤ L`) | `etSeg_past` (`0` past `L`) |
| `zlm4` | `zlm4_indKinds` (for node maps without a `chain` block) | `zlm4_seg_ind` (a segment refuses every kind but `chain`) |
| `lastL` / `lb` / `borrow` | `lastL_eq`, `lastSum_one` (`n = 1 ↦ 0`), `lastSum_top` (`2^18 ↦ 2^18 − 1`) | `lastL_zero` (`n = 0` wraps to `2^18 − 1`: only `V_A`'s `1 ≤ n` excludes it) |
| `RejZ`, `RejLc2`, `RejLcN`, `RejS2` | (on accepted runs: R4) | `not_rejZ_short`, `not_rejLc2_short`, `not_rejLcN_short`, `not_rejS2_short`; `not_rejLc2_node` |
| `segHolds_of_truths` | — (its hypotheses are the truths) | `Rev4.seg_bad_n`, `seg_wrong_end` (S-0′) apply to its conclusion |

## 5. Times (sequential: `taskset -c 0 lake env lean -DElab.async=false --profile`; `logs/P4a/prof-*.log`)

| Module | wall (import ≈ 4 s) | type checking | max RSS |
|---|---|---|---|
| `FRSoundness4P4aNames` | 7.7 s | 18 ms | 2.87 GB |
| `FRSoundness4P4aSeg` | 9.3 s | 0.49 s | 2.95 GB |
| `FRSoundness4P4aLast` | 9.9 s | 0.70 s | 2.89 GB |
| `FRSoundness4P4aCtrl` | 7.2 s | 0.13 s | 2.93 GB |

The one `decide` is `BlockKind.chain ≠ .free` (a constructor inequality, as in 3.x). No `simp` runs near a concrete `trueSum`.

## 6. Handover: the remaining items, in order

1. **`testBit_lastL`**: `k < 18 → (lastL es).testBit k = lb (nStmt es) k`, from `lastSum` (a sum of
   distinct powers). It makes `lastBits` the cube bits of `lastL`.
2. **`c0S_seg`**: a segment's `c0S es = eqAtR τ (lastL es) · thS θ hb + κ_s · thS θ sb`
   (3.x's `c0S_eq` with `shiftTargetS` on `endBits`; needs item 1 and `lastL es < 2^nb`).
3. **`trueSum_TS`** for the segment branch (3.x's proof with `sh_sum_seg`; the node branch takes a
   sum law for `wN` as a hypothesis); then `S2Bad` ⇔ a nonzero residual (`tr_ne`), S1's `hfin`.
4. **`final_seg`**: `W̃_seg(r_blk, r_pos)` is the verifier's `w_out + w_in` with `shiftSegS`
   (3.x's `final_leaf`); the S end's `claimSL`/`oSh` at a segment.
5. **`peL_seg`**: Z2's `P^e` at a segment is `targetSSegS` at the verifier's operand (`segPtOp`: Z1's
   point zero-padded to 18 block coordinates, then `L`'s bits). It goes through `lastAt r 19 =
   lastL es` (`lastL_sum`, `lastVals_bit`). The padded coordinates sum out with `eqAtR` of `0`.
6. **The doom obligations** for Z, L, S, Sh (`Reads`, `*_habs`, `*_single`, `rej*_ok`, `s1_hfin`,
   stability, `z_unit_pos`/`s_unit_pos` at `fsRanges4`/`phOf4`). Copy them from 3.x's
   `FrZ`/`FrL`/`FrS`/`FrSh`/`FrBind`/`FrZM` with `kindOf → kindOfC` and `mm → mC`. They need the
   `CKind` foundation, which T4 now provides in `FR.Snd.T4`: `Same`, `RejOK`, `D3`, `D2`, `ans3`,
   `StepObl`, `PhaseObl`. Restate `D3Z`/`D2L`/`D2S` over `T4.D3`/`T4.D2` (see §2) so T4's
   `D3_single`/`rounds3_obl` apply. `zw`'s `Same`-congruence (3.x `zW_same`) is T4's.
7. **The node half** (`RejLcN`'s dooms `L3BadN`/`PendLcN`, `truthSN`, `wN`, `indN`, `etN`), once
   S-E's Rev4 node maps exist (S-G13 F3).

## 7. Deviations and findings

- **D1.** `RejL2` is not copied: 3.x's is kind-free, so `P4a.RejL2` is an `abbrev` for it.
- **D2.** `D3n`/`D2n` (log-read round count) instead of T4's `CKind` copies. T4 ran in parallel,
  and its modules were unfinished, so I did not import them. They should be unified at integration.
  There are now three variants: P4a's `D3n`, T4's `T4.D3`, and P4b's `P4b.D3G`.
- **D3.** The witness is a parameter (`zw : Wit`). P4a does not depend on T4's decoding (`fTab`,
  `wordK`, `farL` at `CKind`).
- **F1 (no value missing from the finals).** The segment program does not check `1 ≤ n ≤ cap`, nor
  `L < 2^nb`. Both follow from `V_A`'s check (`SegSoundLog`'s hypotheses), and `lastL_zero` shows
  that `n = 0` would wrap. This only holds if `V_A` and the segment program read the same `stmt`
  bytes: `segView`'s `rdLE64 π 81` and `lastOps`' `digestAt π (absOff 0 (so + 33))`, low 24 bits.
  R4/X4 must prove that the offsets agree.

## 8. Open questions

1. Should P4a's `D3n`/`D2n` be replaced by T4's `T4.D3`/`T4.D2` before the obligations are ported
   (item 6)? I recommend yes, and porting the obligations against T4's foundation.
2. Should R4 take `M := zlm4 indN etN` with the node maps as parameters for now? If so, the
   segment `Rej*`s are final and the node ones wait for F3.

## Pass 2 (after the coordinator's rulings; HEAD `4acc3b3`, T4 committed)

**Done:**
- **Switched to T4's foundation (ruling 1).** `D3Z`, `D2L` and `D2S` are now `T4.D3`/`T4.D2`, whose
  `ans3` reads `kindOfC`. P4a's `D3n`/`D2n`/`ansN`/`Wrong*n` are deleted (no other module used them),
  and `FRSoundness4P4aNames` imports `FRSoundness4TailStep`. Deviation D2 is closed. The dooms keep
  `zw : Wit` as a parameter; T4's `T4.zW` has that type, and X4 instantiates `zw := T4.zW`.
- **New module `FRSoundness4P4aBridge`** (§6 items 1–2):
  - `sum_bits_lt`, `testBit_sum_bits`;
  - **`testBit_lastL`** (bit `k < 18` of `lastL es` is `lb (nStmt es) k`), `lastL_lt`,
    **`lastBits_getD`** (`lastBits` are the cube bits of `lastL`);
  - `pad_getD`, **`eq_pad_last`** (`eq((τ ‖ 0^(18−nb)), bits L) = eqAtR τ L` for `L < 2^nb`),
    `nbC_le`;
  - **`c0S_seg`**: a segment's `c0S es = eqAtR τ (lastL es) · thS θ hb + κ_s · thS θ sb`;
  - **`zW_bool`** (T4's witness is Boolean: `segHolds_of_truths`' `hbool` at `zw := T4.zW`).
- Lesson: `simp [lastBits, …]` over `List.range 18` produced a proof that hit the kernel's
  deep-recursion limit. Explicit `getElem?_map`/`getElem?_range` rewrites avoid it.

**Checks (pass 2):**
- `lake build FR FRSoundness4P4aBridge`: green (`logs/P4a/build-last.log`).
- Axioms: 54 theorems within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`
  (`logs/P4a/axioms.log`).
- Source rule: 234 files, 0 findings.
- `FRSoundness4P4aBridge`: 7.9 s wall, 0.21 s type checking, 2.96 GB peak memory, sequential
  (`logs/P4a/prof-FRSoundness4P4aBridge.log`).
- `loc.py` over the five modules: 1,168 total / 741 code / 61 theorems (`logs/P4a/loc.txt`).

**Imports for `FR.lean`:** `import FRSoundness4P4aBridge`. It pulls in the four modules of pass 1.

**Handover (replaces §6), in order:**
1. **`trueSum_TS` at a segment.** Follow 3.x's proof: `prod_trueSum`, the `idx_split` sum,
   `sh_sum_seg` (needs `lastL es < 2^nb`), then `c0S_seg`. The result is
   `trueSum innerExpr (TS wN zw L es) (nrS κ) = c0S es + resSum nb 2 (resSeg nb (lastL es) …)`.
   Then `S2Bad` ⇔ a nonzero residual (3.x's `TR`, `TR_mle`, `tr_ne`, with `res_ne_seg`), and S1's
   `hfin` against T4's `hfin_*`/`esc_msD`.
2. **`final_seg`** (3.x's `final_leaf`): `W̃_seg(r_blk, r_pos)` is `slotW … · eq(τ, r) +
   (shiftSegS's successor + κ_s eq(r, 0)) · slotW …`. It needs the 18-coordinate padding of
   `shiftSegS` against `nb` (as `eq_pad_last`) and `lastAt τL 18 = lastL es` (`lastL_sum`,
   `lastVals_bit`).
3. **`peL_seg`**: Z2's `P^e` at a segment is `targetSSegS` at `segPtOp`'s operand. Use
   `lastAt r 19 = lastL es`, then sum out the zero-padded block coordinates with `eqAtR` at `0`
   (as in 3.x's `peL_leaf`).
4. **The doom obligations for Z, L, S and Sh, against `FR.Snd.T4.FrontObl`.** These are `Reads`
   (T4's, through `T4.Same`), `*_habs`, `*_single`, `rej*_ok` (`T4.RejOK`), `s1_hfin`, stability, and
   the position facts at `fsRanges4`/`phOf4`. Copy them from 3.x's `FrZ`, `FrL`, `FrS`, `FrSh`,
   `FrBind` and `FrZM`, mapping `kindOf → kindOfC`, `mm d → mC d`, `zW → T4.zW` and `Same → T4.Same`.
   The congruence `zW_same` comes from T4's `fF_same`/`*_same`. The rounds lemmas are T4's
   (`D3_single`, `rounds3_obl`, `RoundsPhase` at Z3 15/26, S2 114/28), with Z3's and S2's
   squeeze-position certificates on `fsItems4`. The `FrontObl` handoff targets T4's `D1 W₀ c₀ 0`.
   That handoff is B′'s, so it is P4b's; P4a contributes phases 0–12 of `DF`.
5. **The node half** (`L3BadN`, `PendLcN`, `truthSN`, `wN`, `indN`, `etN`) waits for S-E's Rev4 node
   maps (S-G13 F3).

## Pass 3 (track P4c; HEAD `8b1ffe5`)

- **Build tree** `logs/fr-build-P4c` (a copy of `fr-build-P4a`; `MINE.txt` lists the nine P4a
  modules; `b.sh` logs to `logs/P4c/build-last.log`). Logs in `logs/P4c/`. Journal: `P4a-JOURNAL.md`,
  "Pass 3".
- Every lean/lake command ran in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. Only P4a's modules were edited (`FRSoundness4P4aSeg`: `truthS`, see
  D4). Four new modules, all in `FR.Snd.P4a` (every new name grepped first). No `Rej*` name changed.

**Done** (handover items 1–3, and the S part of item 4):

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4P4aS` | 311 / 228 / 23 | `ZwSame`, `capPos_zero4`, **`zwSame_zW`**; `resSegL`, `sum_TS`, **`trueSum_TS_seg`**; **`SNode`** (the node's S2 law, a parameter); `nJ4`, `resS4`, `TR4`, `TR4_size`, `TR4_mle`, **`trueSum_TS4`**, **`tr_ne4`**; reads (`nStmt_congr`, `lastL_congr`, `bndL_congr4`, `sbL_congr4`, `hbL_congr4`, `s1_congr4`, `endBits_congr4`, `c0S_agree4`, `zNodeC_same`, `resSegL_same`, `resS4_same`, **`truthS_same4`**); `s_unit_pos4`, `selC_coords4`, **`s1_hfin4`** |
| `FRSoundness4P4aFin` | 318 / 254 / 13 | `eqAtR_padN`, `sum_eqAtR_padN`; `shSeg_eq`, `eqPoint_zero18`, **`final_seg`**; `tauLL`, **`wSumSeg`**, `sum_bits_self`, `lastAt_tauLL`, **`wSumSeg_eq`**, `wSumL4`, `claimSL4`, **`oSh4`**; `peL_range4`, `zrL_length`, `zrL_getD4`, `segPt_eq`, **`peL_seg`** |
| `FRSoundness4P4aS2` | 223 / 159 / 17 | `absOKP4a`/`absOKP4a_eq` (one `seq4` certificate), **`p4a_abs`**; `WNLocal`, `wS_agree`, `TS_same4`, **`TS_local4`**, `TS_size4`, `nrS_le4`, **`habs_S2_4`**, **`single_S2_4`**, `chk_of_not_rejS2_4`, `append_S2_4`, `chkS_same4`, `rejS2_mono4`, **`rejS2_ok4`**, **`D2S_reads4`**; `rchsS_pts4`, `zS2`, **`endS4`** |
| `FRSoundness4P4aCtrl3` | 75 / 39 / 9 | controls (below) |
| P4a total (9 modules) | 2,097 / 1,422 / 123 | `logs/P4c/loc.txt` |

**Main statements:**

```lean
theorem trueSum_TS_seg (hn : (kindOfC es).isNode = false) (hL : lastL es < 2 ^ nbC (kindOfC es)) :
    trueSum innerExpr (TS wN zw L es) (nrS (kindOfC es)) = c0S es +
      resSum (nbC (kindOfC es)) 2 (resSegL zw (kindOfC es) L es) (ptOf _ (tauL _ es)) (ptOf 10 (thL es)) (ksL es)
theorem s1_hfin4 (hN : SNode wN truthSN zw) (hz : ZwSame zw) (hBg : T4.Reads 99 Bg)
    (hprev : Dk (phOf4 98) = fun L es => Bg L es ∨ ¬ truthS truthSN zw L es)
    (hfin : Dk (phOf4 99) = msD (Dk (phOf4 98)) (fun L es => Bg L es ∨ S2Bad wN zw L es) 98 15)
    (L es₀) (hl : es₀.length = 99) : condCount (DPos (T4.Dp Dk)) L es₀ 15 [] ≤ deltaR
theorem final_seg (hnb : nb ≤ 18) (τs rb bits) (hτ : τs.length = nb) (hrb : rb.length = nb) (hL : Lb < 2 ^ nb)
    (hbits : Rev4.lastAt (τs ++ 0^(18−nb) ++ bits).toArray 18 = Lb) (θ rp κ) :
    Σ_q Σ_y eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q =
      sm.1 * slotWS 0 θ rp + (sm.2.1 + κ * sm.2.2) * slotWS 1 θ rp   -- sm := shiftSegS (τs‖0‖bits) (rb‖0)
theorem peL_seg (hn : (kindOfC es).isNode = false)
    (hr : ∀ l < (kindOfC es).m - 13, r.getD l 0 = coordAt es 2 l)
    (hz : ∀ l, (kindOfC es).m - 13 ≤ l → l < 19 → r.getD l 0 = 0) (hL : Rev4.lastAt r 19 = lastL es) :
    Rev4.targetSSegS r = Array.ofFn (peL (zlm4 indN etN) es)
theorem endS4 (hNS : node → wNS κ es = Σ_q Σ_y eqAtR rb y * eqAtR rp q * wN κ es y q)
    (hL : seg → lastL es < 2 ^ nbC κ) (h : D2S wN zw L es) (hl : 170 ≤ es.length) :
    ¬ oSh4 wNS (kindOfC es) es (zS2 zw L es)
```

**Controls** (`FRSoundness4P4aCtrl3`):

| Definition | Positive | Negative |
|---|---|---|
| `ZwSame` | `zwSame_zW` (T4's `zW`) | `not_zwSame_len` (a witness of the log's length) |
| `truthS` (the guard) | `truthS_seg_out` (past the blocks it holds); `truthS_seg_in` (inside, it is `ShHoldsSeg`) | 3.x/pass 1's `not_shHoldsSeg_start` on the inside form |
| `shSeg` (in `final_seg`) | `shSeg_link` (links `y ≠ L` kept) | `shSeg_cut` (no link out of `L`) |
| `eqAtR_padN` | `eqAtR_padN_in` | `eqAtR_padN_out` (`0` past `2^a`) |
| `oSh4` | `oSh4_self` (accepts `c_Sh / w`) | `oSh4_unique` (one value when `w ≠ 0`) |
| `SNode`, `WNLocal` | parameters (S-E's node law); no instance yet | — |

**Checks (pass 3):**
- `lake build FR FRSoundness4P4aCtrl3`: green, 2,463 jobs (`logs/P4c/build-final.log`).
- Axioms (`logs/fr-build-P4c/ax/AxP4c.lean`, `logs/P4c/axioms.log`): all 224 declarations of the
  nine P4a modules within `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Source rule: 243 files, 0 findings (`logs/P4c/source-rule.log`).
- Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile`,
  `logs/P4c/prof-*.log`):

  | Module | wall (import ≈ 4 s) | type checking | max RSS |
  |---|---|---|---|
  | `FRSoundness4P4aSeg` (edited) | 9.6 s | 0.49 s | 2.96 GB |
  | `FRSoundness4P4aS` | 9.2 s | 0.38 s | 2.99 GB |
  | `FRSoundness4P4aFin` | 13.2 s | 0.66 s | 2.98 GB |
  | `FRSoundness4P4aS2` | 12.3 s | 0.75 s (`absOKP4a_eq`'s certificate ≈ 0.4 s) | 3.00 GB |
  | `FRSoundness4P4aCtrl3` | 6.7 s | 0.05 s | 2.95 GB |

  The one new `decide` is `absOKP4a_eq` (`decide +kernel` over `seq4`'s items, P4b's
  `absOK4_eq` pattern). No `trueSum` is evaluated at a concrete size.

**Imports for `FR.lean`:** replace `import FRSoundness4P4aBridge` by `import FRSoundness4P4aCtrl3`
(it pulls `S2` → `Fin` → `S` → `Bridge`).

**Deviations and findings (pass 3):**
- **D4. `truthS` at a segment is guarded by `lastL es < 2^nb`.** Without the guard, a log whose `n`
  exceeds the kind's cap (so `L ≥ 2^nb`) fails the truth (block `L` does not exist), but its
  residual (`resSeg` never meets `u = L`) can vanish, so S1 could not be charged (`tr_ne4` would
  be false). Past the blocks S2's initial claim has no end term; nothing on the log refuses such an
  `n`, and only `V_A`'s `n ≤ cap` (`SegSoundLog`'s hypotheses, F1) excludes it. On accepted runs,
  `lastL_eq` gives the guard. No other module reads `truthS`.
- **D5. The node's S law and weight are parameters**: `SNode wN truthSN zw` (the `J` residual
  tables, the sum law, `ne`, congruence), `WNLocal wN`, and `endS4`'s `hNS` (a node's
  `wNS` is its weight's extension). These are S-E's (S-G13 F3), as is the node half generally.
- **F2 (for R4).** `wSumSeg` is the segment's `finSh` (ii) value as `E·slotW₀ + (Sh + κ_s E₀)·slotW₁`
  over `shiftSegS (τ ‖ 0 ‖ L) (r_blk ‖ 0)`, with no link term. `gShCore` still runs
  `linkWAll`/`linkOps` for a segment (3.x's leaf form was `linkSum (replicate nLinkFam 0) …`, which
  is the same value by `linkSum_eq`). R4 must check that the Rev4 segment program's link weights
  are zero (or add them to `wSumSeg` if they are not). `peL_seg`'s `hr`/`hz`/`hL` are what R4 must
  read off `segPtOp`.

**Handover (the rest of item 4, then item 5), in order:**
1. **S1's entry and the Sh truth's congruence for nodes.** `s1_hfin4` is done for any `Bg` that
   reads before 99. What remains is L3β → S1's entry, the 3.x `l3b_single` analogue at `CKind`.
2. **Z (positions 2 … 68)** from 3.x's `FrZ` against T4: `zHolds_same`, `zHolds_reads`
   (`T4.Reads 3`), `zEnd_reads`, **`z1_hfin`** (T4's `hfin_ml` at `(2, 10)`; needs `ZLM4.Bits`
   for `zlm4`: S-E's `indN`/`etN` bit facts), `z2_habs`, `z2_single`, `z3_habs`, `z3_single`
   (T4's `D3_single` with `TZ_local`), `zend_habs`, **`rejZ_ok`** (`p4a_abs.1`), `pendZ_reads`,
   `z2Bad_reads`, `zendBad_reads`. Rename `kindOf → kindOfC`, `mm 6 → mC 6`, `Same/Reads/RejOK →
   T4.*`, `fsItems/phOf → fsItems4/phOf4`. `ZLM4.Et` reads the log (a segment's `lastL`), so
   `eZ`'s congruence needs `lastL_congr` (positions < 2) and the target maps' locality.
3. **L (68 … 98)** from `FrL`/`FrLc`: `l1_single`, `l2_habs`, `l2_single`, **`rejL2_ok`** at
   `T4.RejOK` (`p4a_abs.2.2.1`; 3.x's `RejL2` is kind-free but its `RejOK` is 3.x's), `l3_habs`,
   `l3b_single` (needs `ZLM4.IndKinds`), `RejLc2`/`RejLcN` checks' `RejOK`, `pendLc_reads`,
   `l3Bad_reads`.
4. **The S/Z/L background and `DF` phases 0 … 12** at `seq4`, with the node parts and P4b's later
   pending claims as parameters (3.x's `FrDF` `bgZ`/`bg5`/`bg10`, `D2F`, `D10F`, `DF 0 … 12`), and
   the `FrontObl` fields restricted to phases 0 … 12 (`habs`, `hsingle`, `hfin`, `hstab` by
   `T4.Reads.stab`). P4b's phases 13 … 25 join them; whoever composes `DF` needs both.
5. **`trueL_two` at revision 4.1**: P4b's `trueL4` at claim 3 is `zS2` (3.x's proof with `nbC`),
   so that `endS4` gives `PendBad4` (3.x's `pendS_pendBad`).
6. **The node half** (`SNode`, `WNLocal`, `wNS`, `L3BadN`, `PendLcN`, `truthSN`, `indN`, `etN`)
   from S-E12a's `FRNodeKinds4` (untracked at this pass: `indN4`, `etN4`, `kf4`, `cells4`).
