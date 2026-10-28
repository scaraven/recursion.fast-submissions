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
