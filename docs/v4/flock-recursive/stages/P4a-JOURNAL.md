# P4a JOURNAL: the soundness front's Z, L, S, Sh at revision 4.1 (positions < 170)

- Base: HEAD `7e14be6` (branch `v4/flock-recursive`). Build tree `logs/fr-build-P4a` (a copy of
  `fr-build-SG13` with its `.lake`; `snap.sh` + `MINE.txt`; `logs/org20`). Logs `logs/P4a/`.
- Every lean/lake command runs in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. Parallel tracks: T4 (Ligerito tail), P4b (Lr/E/RS/B′/W0/O1),
  S-H3 (extractor). New names live in namespace **`FR.Snd.P4a`** (modules `FRSoundness4P4a*`).

## 0. The names for R4 (fixed first; module `FRSoundness4P4aNames`)

All in namespace `FR.Snd.P4a`, over the chain kind `CKind` (`kindOfC`, byte 71). Positions are
3.x's (identity below 170, S-G13 §0.1). **The `Rej*` predicates read the log only** (they are the
verifier's asserted checks); the dooms read the witness through a parameter `zw : Wit` (T4/X4
supply `z = unpack f⁽⁰⁾` at `CKind`).

| Name | What | 3.x original |
|---|---|---|
| `mC d κ`, `nbC κ` | `κ.m − d`, `κ.m − 14` | `mm`, `nbS` |
| `ZLM4` (`Ak`, `Bk`, `Ind κ j t`, `Et κ es t p`) | the kinds' matrices; the target reads the log (a segment's `L`) | `ZLM` |
| `nStmt es`, `lastL es` | `n mod 2^24` from `stmt` bytes 33–35 (`idxOfF 24`), `L = (n − 1) mod 2^18` | new (B-12) |
| `EtSeg Lb t p` | the segment target: `chainE p` on blocks `t ≤ Lb`, `0` past | new |
| `zrL`, `rZ`, `peL M`, `c0Z M` | Z1's point, Z3's challenges, `P^e`, Z3's initial claim | same names |
| **`RejZ M`** | `relZ`'s first conjunct fails (from 68) | `RejZ` |
| `oZ` | claim 1's binding `v = P^z*(λ)` | `oZ` |
| **`RejL2`** | 3.x's verbatim (kind-free: 14 rounds from 69): `FR.Snd.RejL2` | `RejL2` |
| `rhiL`, `rbLc`, `rwL`, `vM` | L's readers | same |
| **`RejLc2 M`** | a segment's `finLc` (ii) fails (from 98) | `RejLc2` |
| **`RejLcN M`** | a node's `finLc` (ii) fails (from 98) | `RejLcN` |
| `tauL`, `rbL`, `rpL`, `bndL`, `sbL`, `hbL`, `c0S`, `nrS` | S's readers; a segment's `c0S` has `L`'s bits in place of `lastPad` | same |
| **`RejS2`** | S2's round checks fail (`nb + 10` rounds from 114) | `RejS2` |
| doom names | `ZHolds`, `ZEnd`, `PendZ`, `Z2Bad`, `Z2D`, `D3Z`, `ZendBad`, `L1Bad`, `D2L`, `L3Bad`, `PendLc`, `S2Bad`, `D2S`, `truthS` (with `ShHoldsSeg`) | same |

## Log

### Names module (done, green): `FRSoundness4P4aNames`

- Built in `logs/fr-build-P4a` (4.8 s). Every name of §0 is a real definition (no placeholder):
  the `Rej*` are the verifier's checks on the log; the dooms take `M : ZLM4` and `zw : Wit`.
- `zlm4 indN etN`: 3.x's `kMat` matrices; a segment's indicator (all `chain`) and target
  (`EtSeg (lastL es)`); a node's indicators and targets are parameters (S-G13 F3).
- `D3n`/`D2n`/`ansN`: 3.x's `D3`/`D2`/`ans3` with the round count read from the log (`nr : Log → ℕ`),
  since 3.x's take `nr : Kind → ℕ` at the 3-kind `kindOf`. Used by `D3Z`, `D2L`; T4 may own the
  generic lemmas (`D3_single` etc.) at `CKind`: these are stated once here if T4 has none.
- **For R4**: `P4a.RejZ M`, `P4a.RejL2` (= `FR.Snd.RejL2`), `P4a.RejLc2 M`, `P4a.RejLcN M`,
  `P4a.RejS2`, with `M := zlm4 indN etN` (the `Rej*` read only `M.Ak`, `M.Bk` and, through
  `c0Z`/`peL`, `M.Et`; none reads `zw`).

### Segment truths (done, green): `FRSoundness4P4aSeg`

- `shSeg`/`wSeg`/`resSeg`/**`ShHoldsSeg`**, **`sh_sum_seg`** (3.x's `sh_sum_leaf` with the successor
  masked at `L` and the end at `L`), `shHoldsSeg_of_res`, `res_ne_seg`.
- `zBlkC`/`zNodeC`, `sbL_seg`/`hbL_seg` (3.x's `digBit_readF`), **`chainLinks_of_shHoldsSeg`**.
- `mC6_q`, **`zHolds_blocks`**, `mvZ_seg`, **`zHolds_seg_block`** (Z at `zlm4` gives the used blocks'
  chain R1CS), `lastL_eq`, **`segHolds_of_truths`**, **`chainEnd_of_truths`** (`Rev4.seg_sound`).
- S2's doom names: `wS wN`, `TS wN zw`, `S2Bad`, `D2S`, `truthS truthSN zw` (node parts parameters).
- Lesson: `Rev4.seg_sound (segHolds_of_truths …)` against an expected `chainEnd … = …` timed out at
  `whnf` (the unifier unfolds `chainEnd` to solve `?st.start =?= …`); pinning `(st := ⟨…⟩)` fixes it.

### `lastOps` (done, green): `FRSoundness4P4aLast` (S-F4 §7 Q3)

- `borrow`, `lb`, `bF` (moved to the names module, so that `lastBits` is the run's values);
  `decMod`, **`borrow_inv`**, **`lastSum`** (`Σ_k [L_k] 2^k = (N + 2^18 − 1) mod 2^18`), `lastSum_eq`.
- `bitVals`/`chainVals`/`headVals`/`lastVals`, `length_flatMap_const`, `getD_flatMap`, `rd_vals`,
  `pureRun_flatMap`, `run_bits`, `rd_borrow`, `run_chain`, **`run_lastOps`**, `lastVals_zero`,
  **`lastVals_bit`**, `lastL_sum`.
- Lesson: with `set N := idxOfF 24 D 0` the kernel hit deep recursion on `run_bits`; stating the
  step lemmas for an arbitrary `N` and specialising once fixed it.

### Controls (done, green): `FRSoundness4P4aCtrl` — see RESULT §4.

### Checks

- `lake build FR FRSoundness4P4aCtrl` green (`logs/P4a/build-last.log`); axioms of 44 theorems within
  `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx` (`logs/P4a/axioms.log`); source rule 224
  files, 0 findings (`logs/P4a/source-rule.log`); sequential profiles `logs/P4a/prof-*.log`.

### Pass 2 (rulings: use T4's `D3`/`D2`; continue §6 items 1–5)

- HEAD moved to `4acc3b3` (T4 committed). `D3Z`/`D2L`/`D2S` now use `T4.D3`/`T4.D2`; P4a's copies
  are deleted.
- `FRSoundness4P4aBridge`: `testBit_lastL`, `lastBits_getD`, `eq_pad_last`, `c0S_seg`, `zW_bool`.
  Items 3–5 of the old §6 and the obligations are in the RESULT's pass-2 handover; my context ran
  short, so I stopped there.
