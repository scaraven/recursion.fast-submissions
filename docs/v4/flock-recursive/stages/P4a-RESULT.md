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

## Pass 4 (track P4d; HEAD `ed98f9e` → `60b65cc` during the pass)

- **Build tree** `logs/fr-build-P4d` (a copy of `fr-build-P4c`; `MINE.txt` lists the fourteen P4a
  modules). Logs in `logs/P4d/`. Journal: `P4a-JOURNAL.md`, "Pass 4".
- Every lean/lake command ran in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. No existing module was edited and no statement changed. Five new
  modules, all in `FR.Snd.P4a`. Every new name was grepped first. No `Rej*` name changed.

**Done:** handover items 1–5. Item 1 is `l3b_single4`. Item 2 is Z, item 3 is L, item 4 is
`DF4a` and the `FrontObl` fields for phases 0 … 12, and item 5 is `trueL4_two`.

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4P4aZ` | 462 / 341 / 43 | **`ZLM4.EtLocal`**, `zlm4_etLocal`; **`WitBits`**, `witBits_zW`; **`z_unit_pos4`**, `mC6_eq4`, `m13_le4`, `mC6_le`, `same_ext1_4`, **`rejOK_at4`**; the reads (`zrL_agree4`, `zBk/aZ/bZ/zZ_same4`, `eZ_agree4`, `zHolds_same4`, `zHolds_reads4`, `zEnd_of4`, `zEnd_reads4`, `z2_agree14_4`, `z2_agree4`, `peL_agree4`, `c0Z_agree4`, `pzT_same4`, `pabT_same4`, `pendZ_reads4`, `z2Bad_reads4`, `TZ_same4`, `TZ_local4`, `TZ_size4`, `zDooms_log4`, `rZ_agree4`, `zendBad_reads4`, `rejZ_reads4`); `mvZ_bit4`, `zres_bit4`; `Z1Doom4`, **`z1_hfin4`**; **`z2_habs4`**, `z2_ext1_4`, **`z2_single4`**; **`z3_habs4`**, **`z3_single4`**, **`zend_habs4`**, **`rejZ_ok4`** |
| `FRSoundness4P4aL` | 400 / 299 / 33 | `aStar_eq4`, `bStar_eq4`; the node's **`L3BadN`**, `tNL`, **`PendLcN`**; the reads (`lin_agree4`, `zN_same4`, `aLin_same4`, `l1Bad_reads4`, `TL_same4`, **`TL_local4`**, `TL_size4`, `rkL_agree4`, `zfL_same4`, `vM_agree4`, `l3Bad_reads4`, `l3BadN_reads4`, `vBetaL_agree4`, `pendLc_reads4`, `pendLcN_reads4`, `pLc_reads4`, `lDooms_log4`); **`l1_single4`**, **`l2_habs4`**, **`l2_single4`**, `append_L2_4`, **`rejL2_ok4`**; `l3_core`, **`l3_habs4`**, **`l3N_habs4`**, `l3b_ext1`, `vBetaL_ext1`, **`l3b_single4`**, **`l3bN_single4`**, **`rejLc2_ok4`**, **`rejLcN_ok4`** |
| `FRSoundness4P4aT` | 139 / 116 / 3 | **`WitOf`**, `rpL_length4`, **`trueL4_two`**, **`pendS4_pendBad4`** |
| `FRSoundness4P4aDF` | 526 / 395 / 37 | **`Front4a`**, **`Front4a.OK`**; `bgZ4`, `bg5_4`, `bg10_4`, `D2F4`, `D10F4`, **`DF4a`**; **`RejF4a`**, **`rejF4a_ok`**; the position certificates `frontCls4a_check` (items) and `ph_check4a` (phases), `phStart4_mono`, **`phOf4_eq`**, `abs_cls4a`, `sq_cls4a`, `fsRanges4_front`; `rd_bgZ4`, `rd_bg5_4`, `rd_bg10_4`, `card_frame2_4`, `card_or_le4`; **`ms4a`**, **`habs4a`**, **`hsingle4a`**, **`hfin4a`**; `SameStab4` (+ `up`/`or`/`not`, `ss_reads4`, `ss_log4`, `ss_msD4`), `df_ss4a`, **`hstab4a`** |
| `FRSoundness4P4aCtrl4` | 131 / 70 / 16 | controls (below) |
| P4a total (14 modules) | 3,755 / 2,643 / 255 | `loc.py` |

**Main statements:**

```lean
theorem z1_hfin4 (hM : M.Bits) (hb : WitBits zw) (hz : ZwSame zw) (hE : M.EtLocal)
    (hBg : T4.Reads 3 Bg) (hprev : ∀ L es, Dk (phOf4 2) L es → Bg L es ∨ ¬ ZHolds M zw L es)
    (hfin : Dk (phOf4 3) = msD (Dk (phOf4 2)) fin 2 10) (hfinI : ∀ L es, Bg L es ∨ ZEnd M zw L es → fin L es)
    (L es₀) (hl : es₀.length = 3) : condCount (DPos (T4.Dp Dk)) L es₀ 10 [] ≤ deltaR
theorem l3b_single4 (hz : ZwSame zw) (hI : M.IndKinds) (L es) (hl : es.length = 98) :
    (univ.filter fun a => L3Bad M zw L es ∧ ¬ PendLc M zw L (ext1 es a)).card ≤ 7 * 2 ^ 128
theorem rejZ_ok4 (hE : M.EtLocal) : T4.RejOK (RejZ M)        -- also rejL2_ok4, rejLc2_ok4, rejLcN_ok4
theorem trueL4_two (R : P4b.FSrc) (kf) (hzw : WitOf R zw) (L es) :
    P4b.trueL4 R kf (kindOfC es) L es 2 = zS2 zw L es
theorem habs4a (hP : P.OK) (hN : SNode P.wN P.truthSN P.zw) (L es x len)
    (hit : fsItems4[es.length]? = some (.absorb len)) (hp : es.length < 170)
    (hd : DF4a P (phOf4 (es.length - 1)) L es) :
    RejF4a P.M L (es ++ [x]) ∨ DF4a P (phOf4 es.length) L (es ++ [x])
theorem hsingle4a … (hr : ¬ RejF4a P.M L es) : (univ.filter …).card ≤ 239 * 2 ^ 128
theorem hfin4a : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < 170 → ∀ L es₀, es₀.length = s0 + 1 →
    condCount (DPos (T4.Dp (DF4a P))) L es₀ r [] ≤ deltaR
theorem hstab4a : ∀ k ≤ 12, ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X, StabExt fsRnd4 … X →
    phOf4 (X.length - 1) = k → (DF4a P k (L.take i) X ↔ DF4a P k L X)
```

**For the composer of `FrontObl` (X4, with P4b's phases 13 … 25):**
- Take `DF k := if k ≤ 12 then DF4a P k else (P4b's)` and `RejF := RejF4a M ∨ (P4b's checks) ∨ …`
  (`rejF4a_ok` with `T4.rejOK_or`).
- `ms`, `habs` (positions `< 170`), `hsingle` (`< 170`), `hfin` (`s0 + 1 < 170`) and `hstab`
  (`k ≤ 12`) are `ms4a`, `habs4a`, `hsingle4a`, `hfin4a` and `hstab4a`.
- At 170, Lr1's `msD` entry reads `DF4a P 12 = bg10_4 ∨ D2S`.
- **`BgA`** is the background that phases 0 … 12 carry: far at level 0, a false public cell, and
  Lr's and E's rows (3.x's `far0 ∨ nPub ∨ nLr ∨ nE`, P4b's parts). `Front4a.OK.bgA` asks that it
  read before 3.
- **Phase 2's doom is the split statement** `bgZ4 ∨ ¬ ZHolds` (deviation D6). The composer proves
  revision 4.1's `stmt_split`: far, or `¬ Stmt`, implies `DF4a P 2`.
- Instantiate `M := zlm4 indN etN` (`zlm4_etLocal`; `Bits`/`IndKinds` from the node maps,
  `zlm4_indKinds`), `zw := T4.zW` (`witBits_zW`, `zwSame_zW`; `WitOf` by `witOf_of`), and
  `hN : SNode …` (the node's S law: S-E's).

**Controls** (`FRSoundness4P4aCtrl4`):

| Definition | Positive | Negative |
|---|---|---|
| `ZLM4.EtLocal` | `zlm4_etLocal` | `not_etLocal_len` (a target reading the log's length) |
| `WitBits` | `witBits_zW` | `not_witBits` (a constant non-bit; `exists_not_bit` by `|F| = 2^128`) |
| `WitOf` | `witOf_of` (any source with `fz = fF`) | — (a hypothesis; `trueL4_two` uses it) |
| `rejOK_at4` | `rejZ_ok4`, `rejLc2_ok4`, `rejLcN_ok4` | `not_rejOK_at_sq` (from Z1's squeeze 3 it is no `RejOK`) |
| `RejF4a` | `rejF4a_of_rejS2` | `not_rejF4a_short` (nothing before 68) |
| `L3BadN`, `PendLcN` | `l3BadN_of` (a node's wrong masked value) | `not_l3BadN_seg`, `not_pendLcN_seg` |
| `DF4a` | `DF4a_of_bgA` (the background dooms phases 2 … 12 but `msD`'s) | `not_DF4a_out` (phases 0, 1, ≥ 13 are `False`) |
| `frontCls4a` | `frontCls4a_pos` | `frontCls4a_neg` (the classes separate absorbs and squeezes) |
| `SameStab4` | `ss_false4_ctrl` | `not_ss_log4` (a predicate of `L` itself) |

**Checks (pass 4):**
- `lake build FR FRSoundness4P4aCtrl4`: green, 2,471 jobs at HEAD `60b65cc`
  (`logs/P4d/build-final.log`).
- Axioms: all 154 declarations of the five new modules use only `propext`, `Classical.choice`
  and `Quot.sound`; no `sorryAx` (`logs/fr-build-P4d/ax/AxP4d.lean`, `logs/P4d/axioms.log`).
- Source rule: 257 files, 0 findings (`logs/P4d/source-rule.log`).
- Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile`,
  `logs/P4d/prof-*.log`):

  | Module | wall (import ≈ 4–5 s) | type checking | max RSS |
  |---|---|---|---|
  | `FRSoundness4P4aZ` | 12.2 s | 0.81 s | 2.98 GB |
  | `FRSoundness4P4aL` | 8.6 s | 0.24 s | 2.97 GB |
  | `FRSoundness4P4aT` | 7.9 s | 0.22 s | 2.98 GB |
  | `FRSoundness4P4aDF` | 11.3 s | 1.34 s (`frontCls4a_check` ≈ 0.5 s) | 3.00 GB |
  | `FRSoundness4P4aCtrl4` | 8.3 s | 0.12 s | 2.97 GB |

  The `decide`s are all `decide +kernel` position certificates: `frontCls4a_check`, `ph_check4a`,
  `frontCls4a_neg`/`_pos`, and `fsRnd4 3` in `not_rejOK_at_sq`. No `trueSum` is evaluated at a
  concrete size.
- **Kernel lessons** (recorded for G1/golf):
  1. **`show` against `cwL4`.** `trueL4_two` first cost 2.2–4.5 s in the kernel. The cause was a
     `show (eqTab xS.toArray).getD i 0 = _` against `P4b.cwL4 κ es ↑2 i`.
     `rw [P4b.cwL4, show ((2 : Fin 4) : ℕ) = 2 from rfl, cwF]` followed by `change` costs 0.2 s.
     3.x's `trueL_two` (`FRSoundnessFrS`) and `trueL_one` (`FRSoundnessFrZM`) use the same
     `show` and probably pay the same.
  2. **`phOf4` per position.** It costs about 8 ms per position in the kernel (1.4 s over 170
     positions). The classification therefore checks only the items. The phases come from
     `phOf4_eq` (any position between phase `k`'s start and the next is in phase `k`, from T4's
     `phOf_bounds` and `phStart4_mono`), which took `DF4a` from 3.55 s to 1.34 s.

**Imports for `FR.lean`:** replace `import FRSoundness4P4aCtrl3` with
`import FRSoundness4P4aCtrl4`. It pulls `T` (and so `P4bRS`), `DF`, `L`, `Z`, and pass 3's chain.

**Deviations and findings (pass 4):**
- **D6. Phase 2's doom is the split statement** `bgZ4 ∨ ¬ ZHolds`, not 3.x's `far0 ∨ ¬ Stmt`.
  Revision 4.1's statement (`StmtN4`, S-E12a, and the segment's) is not P4a's, so the split
  (3.x's `stmt_split`) belongs to the composer, and `z1_hfin4`'s `hprev` is `id`.
- **D7. The background is a parameter `BgA`**, the parts reduced after 169: far, the public cells,
  and Lr's and E's rows. These are P4b's or T4's.
- **D8. The node's L3 dooms are concrete.** `L3BadN`/`PendLcN` need only the matrices
  (`IndKinds`), so they replace 3.x's `NodeLF` parameters `L3N`/`PendN`. `RejLcN M` is in
  `RejF4a`. What stays with the node half is binding `PendLcN` to RS claim 2 (3.x's `trueL_node`,
  through the kind factor).
- **D9. Two hypotheses are new:** `ZLM4.EtLocal` (a segment's target reads `L` from `stmt`; 3.x's
  targets did not read the log) and `WitBits` (3.x used `unpack_boolean` inline). Both are
  discharged at the instance.
- **No value asserted by no final.** Every check here is one of P4a's `Rej*` names, which R4
  proves from the finals.

**Handover (remaining, in order):**
1. **RS0's pending-claim bridges for Z and Lc** (as `pendS4_pendBad4` for S).
   - 3.x's `okF_pendZ` (`trueL_zero`) gives `PendZ zw → PendBad4` at claim 1.
   - 3.x's `pendLc_pendBad` (`trueL_one` + `zfL_leaf`) gives a segment's `PendLc → PendBad4` at
     claim 2: there `kfT4 = 1`, and the indicator is `chain` everywhere.
   - Port both over `WitOf` (use `rw`/`change`, not `show`, against `cwL4`; see the kernel
     lessons). Together with `pendS4_pendBad4` and P4b's `pendE4_pendBad4`, this gives E4 end's
     `DPend4` (3.x's `dPend_of`).
2. **The node half.** S-E12a is now committed (`60b65cc`): `FRNodeKinds4` (`nodeLayout4`, `Ind4`,
   `Sel4`, `nodeBK4`, `nodeKind4`, the kind factor, `hcells4`) and `FRNodeCircuit4` (`truthZ4`,
   `truthS4`, `StmtN4`, `NodeResid4`, `node_sound4`). The work is:
   - `indN := Ind4`-based indicators and `etN` from `nodeKind4`'s targets;
   - `ZLM4.Bits`/`IndKinds` for `zlm4 indN etN` (`layout_no_chain`, as 3.x's `zlmFR_bits`/
     `zlmFR_indKinds`);
   - `SNode` (the node's S2 law: `wN`, `res`, the sum law, `ne`), `WNLocal`, `wNS`/`hNS`;
   - `PendLcN`'s binding (`trueL_node` with S-E's kind factor as P4b's `kf`);
   - `zHolds_iff_truthZN` against `truthZ4`.
3. **Revision 4.1's `stmt_split`** (D6). It needs `StmtN4` and the segment statement (X4's).

## Pass 5 (track P4e; HEAD `4919027`)

- **Build tree** `logs/fr-build-P4e` (a copy of `fr-build-P4d`; `MINE.txt` lists the fourteen P4a
  modules and the five new ones). Logs in `logs/P4e/`. Journal: `P4a-JOURNAL.md`, "Pass 5".
- Every lean/lake command ran in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. No existing module was edited and no statement changed. Five new
  modules, all in `FR.Snd.P4a`. Every new name was grepped first. No `Rej*` name changed. HEAD did
  not move during the pass, so the final build is on a fresh snapshot of `4919027` (RET-1's
  uncommitted worktree edits are not in it).

**Done:** P4d's handover items 1–3 (the RS0 bridges for Z and Lc, the node half, 4.1's
`stmt_split`).

| Module | total / code / thm | Content |
|---|---|---|
| `FRSoundness4P4aRS` | 361 / 286 / 19 | `zZ_eq4`, `cwF_zero`, `cwF_one`, `cwL4_zero`, `zPtL_length4`, `zrL_drop4`, **`trueL4_zero`**, **`pendZ4_pendBad4`**; `ptOf_rkL4`, `ptOf_rbLc4`, **`trueL4_one`**, **`zfL_eq4`**; **`oLc4`**, **`SegInd`**, **`KfInd`**, `segInd_zlm4`, `zfL_seg4`, **`pendLc4_pendBad4`**, **`trueL4_node`**, **`pendLcN4_pendBad4`**; **`pendF4a_pendBad4`**, **`dF4a12_pendBad4`** |
| `FRSoundness4P4aNZ` | 138 / 96 / 9 | `zlm4_bits`, **`zlm4_bits4`**, **`kfInd4`**; `bkIdx4_eq`, `kindTgt_pins`, `zHolds_of_blocks4`, `mvZ_node4`, `zBk_zB4`, **`zHolds_iff_truthZ4`** |
| `FRSoundness4P4aNS` | 433 / 331 / 23 | layout bounds (`nodeBK4_lt`, `chainLk4_lt`, `chLen0_lt`, `hUsedN_lt`, `fam_mir_lt`, `srcB4_lt`, `mirB4_lt`, `srcB4_inj`); **`ShHoldsN4`**, **`truthSN4`**, `zNodeC_zN4`, **`truthS4_iff`**; `lkW4`, `shN4`, `famW4`, **`wNode4`**, **`resNode4`**; `sum_swap22`, `sum_delta2`, `sum_famW4`, `sum_resF4`, `chainLk4_top`, **`sh_sum_node4`**; `resNode4_src`, `shHoldsN4_of_res`, **`res_ne_node4`**; **`wN4`**, `resN4`, **`wNS4`**, `hNS4`, **`wNLocal4`**, **`c0S_node4`**, `sum_wS_node`, **`sNode4`** |
| `FRSoundness4P4aSplit` | 97 / 60 / 5 | **`front4`**, **`front4_ok`**; **`Stmt4`**, `NodeRest4`, **`stmt_split4`**; controls `stmt4_seg_iff`, `stmt4_node_iff`, `not_stmt4_seg` |
| `FRSoundness4P4aCtrl5` | 68 / 31 / 9 | controls (below) |
| pass 5 total | 1,097 / 804 / 65 | `loc.py`, `logs/P4e/loc.txt` |

**Main statements:**

```lean
theorem trueL4_zero (R : P4b.FSrc) (kf) {zw : Wit} (hzw : WitOf R zw) (L es : Log) :
    P4b.trueL4 R kf (kindOfC es) L es 0 = (pzT zw L es).eval (lamL es)
theorem pendZ4_pendBad4 … (hzw : WitOf R zw) (h : PendZ zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ oLc oSh) L es
theorem trueL4_one … : P4b.trueL4 R kf (kindOfC es) L es 1 = ∑ t ∈ range (2 ^ qL (kindOfC es)), ∑ j ∈ range (2 ^ 14),
    eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * P4b.kfT4 kf (kindOfC es) es t * zw (kindOfC es) L es (j + 2 ^ 14 * t)
def oLc4 (_κ : CKind) (es : Log) (v : F) : Prop := v = vBetaL es
def SegInd (M : ZLM4) : Prop := ∀ σ t, M.Ind (.seg σ) 0 t = 1
def KfInd (M : ZLM4) (kf) : Prop := ∀ ν β t, kf ν β t = ∑ i : Fin 8, β ^ i.val * M.Ind (.node ν) i.succ t
theorem pendLc4_pendBad4 … (hS : SegInd M) (hzw : WitOf R zw) (h : PendLc M zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ' oLc4 oSh) L es
theorem pendLcN4_pendBad4 … (hkf : KfInd M kf) (hzw : WitOf R zw) (h : PendLcN M zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ' oLc4 oSh) L es
theorem dF4a12_pendBad4 (hS : SegInd P.M) (hkf : KfInd P.M kf) (hzw : WitOf R P.zw) (hNS : …) (hL : …)
    (hl : 170 ≤ es.length) (h : DF4a P 12 L es) : P.BgA L es ∨ P4b.PendBad4 R kf (P4b.okRS4 oZ oLc4 (oSh4 wNS)) L es
theorem kfInd4 : KfInd (zlm4 N4c.indN4 N4c.etN4) N4c.kf4
theorem zHolds_iff_truthZ4 (hzw : WitOf R zw) (hb : WitBits zw) (hν : kindOfC es = .node ν) :
    ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ↔ N4c.truthZ4 ν (R.fz L es)
theorem truthS4_iff (hzw : WitOf R zw) (hν : kindOfC es = .node ν) : N4c.truthS4 ν (R.fz L es) ↔ truthSN4 zw (kindOfC es) L es
theorem sh_sum_node4 (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (κ : F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), wNode4 ν τ θ κ y q * z y q = resSum (nbC (.node ν)) 10 (resNode4 ν z) τ θ κ
theorem res_ne_node4 (h : ¬ ShHoldsN4 ν z) : ∃ j < 10, ∃ u < 2 ^ nbC (.node ν), ∃ q < 2 ^ 10, resNode4 ν z j u q ≠ 0
def sNode4 (hz : ZwSame zw) : SNode wN4 (truthSN4 zw) zw
theorem wNLocal4 : WNLocal wN4
theorem front4_ok (hb : WitBits zw) (hz : ZwSame zw) (hBg : T4.Reads 3 BgA) : (front4 zw BgA).OK
theorem stmt_split4 (hzw : WitOf R zw) (hb : WitBits zw)
    (hBg : ∀ ν, kindOfC es = .node ν → ¬ NodeRest4 R lr er pv ν L es → BgA L es)
    (h : ¬ Stmt4 R zw lr er pv L es) : DF4a (front4 zw BgA) 2 L es
```

**For the composer (X4):**
- `P := front4 T4.zW BgA` (`front4_ok witBits_zW zwSame_zW hBgA`), `hN := sNode4 zwSame_zW`,
  `wNS := wNS4` (`hNS4` is `rfl`), P4b's `kf := N4c.kf4` (`kfInd4`), `SegInd` by
  `segInd_zlm4`, `WitOf` by `witOf_of`.
- RS0's bindings: `P4b.okRS4 oZ oLc4 (oSh4 wNS4)`. E4 end's `DPend4` from phase 12's carried doom:
  `dF4a12_pendBad4` (Z, Lc on both kinds, S2) together with P4b's `pendE4_pendBad4` (E); `BgA`'s far
  and public parts are `DPend4`'s `F0`/`¬ Pub`.
- Phase 2's entry: `stmt_split4` turns `¬ Stmt4` into `DF4a (front4 …) 2`, given that `BgA` holds
  when a node's L rows, M rows or public cells fail (`NodeRest4`; P4b's parts).
- `hL` (a segment's `lastL < 2^nb`) stays a hypothesis of `pendS4_pendBad4`/`dF4a12_pendBad4`
  (`V_A`'s `n ≤ cap`, P4c's deviation).

**Controls** (`FRSoundness4P4aCtrl5`, `FRSoundness4P4aSplit`):

| Definition | Positive | Negative |
|---|---|---|
| `oLc4` | `oLc4_vBeta` | `not_oLc4_succ` |
| `SegInd` | `segInd_zlm4` | `not_segInd_zero` (all-zero segment indicators) |
| `KfInd` | `kfInd4` | `not_kfInd_zero` (a zero kind factor: `N2`'s block 0 has `B_1 = 1`) |
| `ShHoldsN4`, `truthSN4` | `shHoldsN4_zero`, `truthSN4_seg` | `not_shHoldsN4_link` (block 1's `h_in` is not block 0's `h_out`) |
| `resNode4` | `resNode4_zero_tbl` | `res_ne_node4` (a failed truth leaves a nonzero table) |
| `Stmt4` | `stmt4_seg_iff`, `stmt4_node_iff` | `not_stmt4_seg` |
| `front4` | `front4_ok` | — (parameters) |

**Checks (pass 5):**
- `lake build FR FRSoundness4P4aCtrl5`: green, 2,480 jobs at HEAD `4919027`
  (`logs/P4e/build-final.log`).
- Axioms: all 82 declarations of the five new modules use only `propext`, `Classical.choice` and
  `Quot.sound`; no `sorryAx` (`logs/fr-build-P4e/ax/AxP4e.lean`, `logs/P4e/axioms.log`).
- Source rule: 270 files, 0 findings (`logs/P4e/source-rule.log`).
- Sequential profiles (`taskset -c 0 lake env lean -DElab.async=false --profile`,
  `logs/P4e/prof-*.log`):

  | Module | wall (import ≈ 4 s) | type checking | max RSS |
  |---|---|---|---|
  | `FRSoundness4P4aRS` | 10.6 s | 0.47 s | 2.99 GB |
  | `FRSoundness4P4aNZ` | 8.2 s | 0.06 s | 2.97 GB |
  | `FRSoundness4P4aNS` | 13.1 s | 0.57 s (simp 1.9 s) | 3.00 GB |
  | `FRSoundness4P4aSplit` | 6.2 s | 0.01 s | 2.95 GB |
  | `FRSoundness4P4aCtrl5` | 6.5 s | 0.02 s | 2.96 GB |

  The only `decide` is `1 ≤ nAgg ν * ν.maxK` per node kind (`hUsedN_lt`, three small constants).
  No `trueSum` is evaluated at a concrete size.
- **Kernel lesson** (for G1): `cwF_zero`/`cwF_one` by `rfl` cost 1.1 s in the kernel (it unfolds
  `eqZS`/`eqTab` on the right before the match on the left); by `rw [cwF]` they cost nothing
  (RS 1.57 s → 0.47 s). 3.x's `cwL_zero` (`FRSoundnessFrBind`) states the same `show` and may pay
  the same.

**Imports for `FR.lean`:** replace `import FRSoundness4P4aCtrl4` with
`import FRSoundness4P4aCtrl5`. It pulls `Ctrl4`, `Split`, `NS`, `NZ`, `RS`, and through `NZ`
`FRNodeCircuit4` (already imported by `FRNodeCircuit4Dig`).

**Deviations and findings (pass 5):**
- **D10. The node's S2 weight keeps the start term.** S-E12a's `truthS4` drops 3.x's start
  conjunct (its D4: both chain starts are `streamStart`, pinned by Z). `wNode4` keeps the
  blueprint's A.9 `finSh` (ii) form, `κ_s([y = 0] + [y = chLen₀])` (power 1) and the families at
  `κ_s^(f+2)`, so `resNode4` has `J = 10` tables, table 1 being `h_in(0) + h_in(chLen₀)`. This is
  sound (an extra table only adds a check: `SNode.ne` needs a nonzero table when `truthS4` fails)
  and complete (both starts' `h_in` are `h0`). If `implN`'s `finSh` drops the start term, drop it
  from `wNode4`/`resNode4` too (`J = 9`); nothing else changes.
- **D11. `wNS4` is the weight's extension by definition** (`hNS4 := rfl`). On a node the value the
  verifier binds in `finSh` (ii) is computed by `implN κ`'s `shiftMask`/`slotW`/`linkWAll`
  (`VnodeC`; parametric). R4 needs `implN κ`'s specification to compute `wNS4`: the chain mask at
  `chainLk4` (two chains, `chLen ν 0` and `chLen ν 1` blocks, `nb = 17/18` coordinates) and the
  families at `srcB4`/`mirB4`. 3.x's `shiftMaskS` (`chainN`, 16 coordinates) and `linkWAllS`
  (3.x's `srcB`) do **not** compute it. **This is the one value here that no final is yet shown to
  assert** (finSh (ii) asserts it only through `implN κ`, whose node specification does not exist
  yet). I stopped on it rather than fix a specification that belongs to the node ops' owner.
- **D12. `oLc4` (claim 2's binding) is `v = v_β` for every kind**, as 3.x's `oLcV` (ruling 3.16).
  `gFinLc` reuses 3.x's `lcTail`, so R4 discharges `¬ RejRS4` at claim 2 as 3.x did.
- **D13. `Stmt4`** (the composer's statement) is defined here: a node's `StmtN4` with its rows and
  public digests as parameters, a segment's `ZHolds ∧ truthS` (what `segHolds_of_truths` reads).
  X4 may prefer its own; `stmt_split4` only needs the node's parts to be `NodeRest4`.

**Open questions:**
1. D11: who specifies `implN κ`'s `shiftMask`/`linkWAll` at the 4.1 node layout (S-E12c? L-circ?),
   and should it keep the start term (D10)?
2. Should `Stmt4` move to X4 (with `pv` read from the log: `vk`, `c₁`, `c₂` from entry 0 / `stmt`)?

**Handover (remaining for the P4a front, in order):** none of P4d's items remain. What is left
belongs to other tracks:
1. (R4 / the node ops' owner) `implN κ`'s `finSh` (ii) computes `wNS4` (D11), and `finLc` (iii)
   asserts `oLc4` on both kinds (D12).
2. (X4) Compose `FrontObl` with `front4`, `sNode4`, `dF4a12_pendBad4` + `pendE4_pendBad4`,
   `stmt_split4`; supply `BgA`'s `NodeRest4` cover from P4b's row dooms.
