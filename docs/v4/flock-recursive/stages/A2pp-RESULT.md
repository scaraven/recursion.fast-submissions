# A2″ RESULT: (β′), the sound batched cap check, with levers L1 + L2 (PACK-4.4 §11)

Track A2″, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `e4b7d5f`
(A2′'s tree with main merged). Build tree `logs/fr-build-A2pp` (copied from `logs/fr-build-A3`), logs
`logs/A2pp/`. Journal: `stages/A2pp-JOURNAL.md`. No sub-agents, nothing committed.

Spec: PACK-4.4 §11.1, §11.2, §11.4, corrected by `reviews/PACK-4.4-b2-review.md` (PB-M2, PB-m1 … m5,
m12).

## 0. Summary

- **Done.** V is now (β′):
  - Every position ends with a **static** read of its committed path digest `D_r` and
    `assertEq cur D_r`.
  - Four phases follow `Pf`: `CapD` (absorb `D`, field 18), `CapZeta` (squeeze `ζ`), `CapChk`
    (absorb `A`, field 19), `CapChkZ` (squeeze `z`), at FS entries 482–485.
  - `capChkOps` takes `ζ` from `CapZeta`'s answer and `z` from `CapChkZ`'s. It runs (I)/(II) on the
    committed `D`.
  - No dynamic cap read remains: `piDigestAt` occurs 0 times in every `ops-*.txt`.
- **L1 and L2 are in, and both are needed.**
  - L1: one `WM` per signed child, so H drops 876 blocks in N8.
  - L2: level 4's cap at depth 8, through a new `Seq.cap4` field. `seq3`, 3.x's ladder and every
    `lvlStar` module are untouched.
  - N8: `hUsed` 195,080, `hEnd` 195,088, `lBase` 195,328 ≤ 195,584. That leaves 256 blocks of
    `lBase` slack and 496 blocks of `hUsed` headroom.
  - The new kernel control `regions_need_levers` shows that N8 does not fit without L1, nor without
    L2.
- **The KAT passes on full V runs** of `progNode .N4` under a programmable oracle
  (`dump/capkat.txt`). It covers:
  - an honest `D`/`A`;
  - a wrong `A_k`;
  - a wrong `D_r`, which fails exactly at its own position's assert;
  - **A3′'s two-opening attack, replayed.** The GF(2) solve forges (I) in A2′'s model. Under (β′) it
    is rejected in both orders.
- **Measured: interim, skeleton ops, not quotable.**
  - V(N4) best **423 / 434 ms**. For comparison, A2′'s was 513 / 517 and pre-A2′'s 233 / 238.
  - `evalMT4 N4` **304 / 294 ms**.
  - `plan4t init` **5.2–5.4 s**, `inR true`.
  - The prototypes' Merkle instances are back (5,396). The cap check's ≈ 64 k sparse rows per
    prototype wait for B2′'s templates.
- **Literal corrections to the memo.**
  - `|π|` is **875,280**, not 875,312. The memo kept A2′'s 32-byte pad in `A` while dropping it.
  - The item numbers are `D` 8,779, `ζ` 8,780, `A` 8,781, `z` 8,782 (0-based, as PB-m3 says).
- **The red set for A3′ is 10 declarations in 6 modules**, found by a build-tree-only scan that
  reaches a green build. It is listed in §5, with the statements that are now false but compile.
- **Deviation: `reloc`'s bound stays 19 (PB-m1).** The cap check reads field 19 by absolute offset
  instead (§8).

## 1. What was built (code lines by the core's `loc.py`, HEAD → now)

| Module | Change | code |
|---|---|---|
| `FRTranscriptDefs` | `fD := 18`, `fA := 19` (3.x's `nFields` 18 untouched) | 384 → 385 |
| `FRShape4` | `Seq.cap4 : ℕ := 7` (PB-M2 (ii)); `ladderOfR ell0 cap4 m`; `Seq.lvK` reads `S.cap4`; `seq4 … cap4 := 8`; `ladderOf m := ladderOfR 6 7 m` (3.x's; `ladderOf_32/30` stay `rfl`); `lvOf m i := seq4.lvK m i`; `lvOf_32` restated (levels 0–3 = `lvlStar`; level 4 cap 8 vs 7); `ladder_sq_sib` restated for `m = 32/31/30` (level-4 `sib` 4/3/2); `capReadsBelow`, `capReadsN`, `dBytes`; `aBytes` without pad; `capChkPh` = the four phases; `nFields4 := 20`; `piSizeOf_seq3` over two empty fields; literals `itemsOf_seq4_length 8783`, `capEntries_seq4` (871 reads, `D` 27,872, 1,536 entries, `A` 49,152), `capChkPh_ctl`, `capChk_aligned` (CapD‖CapZeta ≡ 0, CapChk‖CapChkZ ≡ 32 mod 64), `fieldSizesOf_seq4` (20 fields), `piSizeOf_seq4 875280`, `streamBytesOf_seq4 1550080`, `chainLenOf_seq4 24220` | 219 → 239 |
| `FRVIR4` | `posOps4 … dO …`: `shrN`, `piDigest 0 (dO + 32p)`, `assertEq (curOfY sL (b+3)) (b+4+6sL+1)`; `posW4 = 4 + 6 sL + 2` (PB-m2); `dOfY`; `dOff4 S i = fieldOffOf S fD + 32·capReadsBelow S i` (absolute, PB-m4); control `dOff4_ctl` | 136 → 141 |
| `FRVIR4Mux` | `posOpsG` the same; the queries phase passes `dOff4 S i` | 150 → 151 |
| `FRVIRFinals4` | `capChkOps` rebuilt as five regular families (§6, "For B2′"): `powChainOps`, `powReg`, `CapRead` (`d`, `k`, `w`), `bitPowOps`, `macDOps`, `macAOps`, `capReads` on `dOfY`; `ζ` = `CapZeta`'s answer, `z` = `CapChkZ`'s; `noAsk_capChkOps`, `capChkOps_off/_head` reproved; `fin3P_S` literal; `reloc`'s doc (bound kept, §8) | 528 → 519 |
| `FRVIR4At` | `map_at_capChkOps` reproved (the two helper lemmas removed) | 340 → 326 |
| `FRVIR4Uni` | `map_at_posOpsG` and `genPhaseG_at` (signature, `dO`) | 241 → 241 |
| `FRSoundness4Pos` | `fsItems4_length 486`; `fsStarts4_eq` gains 484, 485; `CKind.lv κ i := seq4.lvK κ.m i` (= `lvOf κ.m i` by definition) | 97 → 97 |
| `FRSoundness4Qry` | 8,783; `items_posOps4`'s `dO` | 173 → 173 |
| `FRX4Prog`, `FRX4Ext` | `843280` → `875280` (the literal only) | 169, 543 |
| `FRNodeLayout4` | L1 in `hUsed` (`wmSlot4 * 2`); `aggChainLen_eq/_k3` (48,440 / 96,880 / 72,660); `hUsed_eq` (73,965 / 122,411 / 195,080); new `hUsedN8At`, **`regions_need_levers`** | 52 → 59 |
| `FRNodeKinds4` | `segB 1550080`, `cLen 24220`; L1 in `hUsedN`; `hEnd_eq` (73,967 / 122,415 / 195,088) | 393 → 393 |
| `FRVIRTpl4Bridge` | `protoR_ctl` `(24220, 96880)`, `(24220, 48440)`, `(96880, 96880)` | 65 |
| `FRNodeRows4Pack`, `FRNodeRows4`, `FRNodeSound4R` | 8,783 (`wfSeg_length`, `packRows4_length_le ≤ 8784`, `segTr_length`, `slotTr4_length`) | 83, 152, 287 |
| `FRVerifierImplNode4T` | `nodeE4_ctrl`: `aggB 1 = 0x17A700` reads bit 13 as `1`, bit 12 as `0` | 404 |
| `FRNodeRows4Hint` | regenerated with `laydump4` (`logs/A2pp/laydump4.log`) | 36 → 35 |

- Touched: 19 modules, 4,452 → 4,462 code lines (+10).
- `FRNodeRead4`, which PB-M2 names, has no item literal at this HEAD. The 8,907 → 8,783 literals are
  in `FRNodeSound4R` (`segTr_length`/`slotTr4_length`).
- `ladderOfR` (the `m = 31` ladder), `ladder_sq_sib`, `seg_ladder_fits`/`node_ladder_fits`
  (unchanged statements, re-decided) and `FRX4Prog.szPs` are the other PB-M2 items. All are covered.

## 2. Build and kernel times

- **Build.** All 19 modules build. `lake build FR Solution FRSoundness4TailShift FRSoundness4XCtrl
  FRNodeSound4Ctrl` (`logs/A2pp/build-1.log`) fails in exactly A2′'s two first-round modules,
  `FRSoundness4TailD` and `FRSoundness4R4Run`, both A3′'s. The scan (§5) reaches a green build.
- **CPU-s per touched module.** Sequential profile (`lean -DElab.async=false --profile`, one core
  (26), load ≈ 10; `logs/A2pp/profile-*.log`, `profile-summary.txt`). CPU = user + system from
  `/usr/bin/time`, so it includes ≈ 4 s of import and ≈ 3 s of system per module. "S-I" is S-I's
  per-module figure as quoted in A2′'s RESULT.

| Module | CPU-s | wall | type checking | tactic | S-I |
|---|---|---|---|---|---|
| `FRTranscriptDefs` | 25.7 | 25.7 | 8.70 | 2.72 | 17.0 |
| `FRShape4` | 21.1 | 21.2 | 7.97 | 0.92 | 23.0 (A2′ paired: 24.3) |
| `FRVIR4` | 19.4 | 19.4 | 1.15 | 0.02 | 11.0 |
| `FRVIR4Mux` | 12.1 | 12.1 | 0.06 | 0.34 | 8.1 |
| `FRVIRFinals4` | 26.4 | 26.4 | 1.87 | 5.40 | 25.0 (A2′ paired: 20.3) |
| `FRVIR4At` | 13.7 | 13.8 | 0.63 | 2.02 | 8.2 |
| `FRVIR4Uni` | 12.0 | 12.1 | 0.14 | 0.81 | — |
| `FRX4Prog` | 12.3 | 12.4 | 0.47 | 0.92 | 5.0 |
| `FRX4Ext` | 15.5 | 15.6 | 1.46 | 2.32 | 9.2 |
| `FRSoundness4Pos` | 20.1 | 20.1 | 11.5 | 0.45 | 16.0 |
| `FRSoundness4Qry` | 35.5 | 35.5 | 0.49 | 0.59 (`simp` 24.8) | 18.0 |
| `FRNodeLayout4` | 16.4 | 16.5 | 9.58 | 0.07 | 14.0 |
| `FRNodeKinds4` | 18.6 | 18.6 | 2.27 | 2.43 | 14.0 |
| `FRVIRTpl4Bridge` | 7.2 | 7.3 | 0.11 | 0.20 | 4.1 |
| `FRNodeRows4Pack` | 7.3 | 7.4 | 0.15 | 0.22 | — |
| `FRVerifierImplNode4T` | 13.0 | 13.0 | 1.59 | 1.58 | 10.0 |
| `FRNodeRows4` | 9.7 | 9.7 | 0.18 | 0.23 | 6.9 |
| `FRNodeSound4R` | 8.9 | 8.9 | 0.24 | 0.49 | — |
| `FRNodeRows4Hint` | 6.1 | 6.2 | 0.00 | — | — |
| **total** | **301.0** | | | | |

- The S-I column was measured on another machine, without the import/system share, so it is not a
  paired comparison.
- The new decisions are cheap: `FRShape4` 21.1 against A2′'s paired 24.3; `FRNodeLayout4`'s
  `regions_need_levers` is a `decide` on six numbers.
- `FRSoundness4Qry`'s 24.8 s of `simp` is the outlier. Its proofs are unchanged except for the `dO`
  argument, so this is the `simp` over `posOps4`'s two extra ops per position. A2′ measured
  1:29.85 wall for it at load ≈ 20, so this is not new with this track; I did not bisect it.

## 3. Measurements (interim, skeleton ops, not quotable)

The cap check is still compiled as skeleton ops. **None of these figures may be quoted as the
design's V**: B2′'s templates replace the cap check's rows (PACK §11.7).

| | pre-A2′ (A2′'s base) | A2′ (β) | **A2″ (β′), now** | log |
|---|---|---|---|---|
| V(N4) `vtime4 21 n4f` best (core 30) | 233.3 / 237.6 ms | 513.2 / 516.5 ms | **423.3 / 434.5 ms** (median 447.7 / 453.6), load ≈ 16 | `vtime4-{a,b}.log` |
| `evalMT4 N4` (in `vtime4`) | 132.0 / 121.9 ms | 365.8 / 355.9 ms | **304.4 / 294.5 ms** | same |
| `evalMT4` N2 / N4 / N8 (`plan4t check`) | — | — | **309.0 / 306.4 / 189.3 ms**, each `equal true` against the sparse sum | `plan4t-check.log` |
| `plan4t init` (core 29) | 2.22 / 2.57 / 2.48 s | 4.17 / 5.27 / 4.59 s | **5.43 / 5.22 / 5.19 s**, `inR true` | `plan4t-init-{1,2,3}.log` |
| prototype rows in region (p0 / p1) | 730,493 / 725,885 | 787,837 / 783,229 | **791,933 / 791,421** | `nodedump4-run.log` |
| plan pieces p0: sparse rows / instances | 40,064 / 5,396 | 133,803 / 4,530 | **103,872 / 5,396** | `planform4-run.log` |
| `progNode .N4`: ops / registers | 106,485 / 97,657 | 147,211 / 140,122 | **151,474 / 143,640** | `protodump-run.log`, `dump/fsummary.txt` |
| `|π|` | 798,192 | 843,280 | **875,280** | `dump/summary.txt` |

- **Reading the numbers.**
  - The per-position assert reads the path root inside its Merkle block again. So the 866 Merkle
    instance groupings A2′ lost come back: 5,396 instances, as before A2′. This confirms A2′'s
    reading.
  - What remains is the cap check itself, untemplated: ≈ 63.8 k sparse rows per prototype
    (103,872 − 40,064). That is B2′'s.
  - V(N4) is still ≈ +190 ms over pre-A2′, nearly all of it `evalMT4`.
- **`evalMT4` with and without the cap-check rows.**
  - Without (pre-A2′): 132.0 / 121.9 ms, A2′'s base measured on this VM (main worktree
    `logs/A2p/vtime4-base-*.log`).
  - With: 304.4 / 294.5 ms.
  - I did not build a variant program without the cap check on this tree.
- `plan4t init` is over its 2 s bound (PK-m6) until B2′'s templates land.

## 4. Controls, KATs, dumps

**Kernel controls, new or restated.**

- `lvOf_32`:
  - (+) levels 0–3 are 3.x's;
  - (−) level 4's cap is 8 at `seq4` and 7 at `lvlStar`.
- `ladder_sq_sib`: the squeezes and siblings of the three ladders, with level-4 siblings 4/3/2.
- `capEntries_seq4`: 871 reads, `D` 27,872 B, 1,536 entries, `A` 49,152 B.
- `capChkPh_ctl`:
  - (+) `seq4` has the four phases;
  - (−) `seq3` has none.
- `capChk_aligned`: `CapD‖CapZeta` is whole blocks; `CapChk‖CapChkZ` is half a block over, and L2's
  Q.4 gives it back (`chainLenOf_seq4`: 1,550,080 = 64 · 24,220).
- `dOff4_ctl` (+): `D`'s reads start at `fD`'s offset and end exactly at `fA`'s.
- `regions_need_levers`:
  - (+) N8 fits with L1 + L2;
  - (−) it does not fit without L1 (8 `WM` sub-regions);
  - (−) it does not fit without L2 (the 1,556,032-byte stream).
- `capChkOps_off` (−) and `capChkOps_head` (+) are reproved. `nodeE4_ctrl` is at `0x17A700`.

**The cap-check KAT** (`logs/A2pp/dump/capkat.txt`; tool `probe/IRDumpA2pp.lean`, compiled;
3 min 50 s).

*Setting:*
- The full `progNode .N4` (151,474 ops) runs op by op through `evalOp`, on a pseudo-random π (caps
  random).
- The oracle is consistent (a query's answer is fixed at its first ask) and pseudo-random. It is
  **programmable** at the top `askNode` of each position, which is how an honest tree's root is made
  to equal the cap entry.
- The reads are found in the program by their static `D` reads: 871 reads, 290/178/145/132/126 per
  level.
- Each case runs the real Fiat–Shamir order:
  1. positions from the chain;
  2. openings and `D` written;
  3. `ζ` read from the run, which depends on the absorbed `D`;
  4. `A` computed and written;
  5. the final run.
- The 237 other failing ops are the PIOP checks on a random π. That count is identical in every case,
  and the KAT reads only the 871 position asserts and the three cap-check asserts.

*Results:*

| Case | Position asserts failing | (I lo, I hi, II) failing | Verdict |
|---|---|---|---|
| (+) honest `D`, `A` (every path root = `D_r`; 672 nonzero `A_k`) | 0 | none | accepted |
| (−) `A_0 + 1` | 0 | all three | rejected |
| (−) `D_100` one byte off | exactly `[100]` | I lo | rejected at its position |
| A3′'s attack, the forgery in A2′'s model | — | (I) holds at `ζ₀` with the chosen roots | **forges**, which confirms A3′ |
| (−) attack in (β′)'s order: `D = d⁰` committed, openings chosen after `ζ₀` | 259 (exactly the flipped reads) | I lo, I hi | rejected |
| (−) attack in A3′'s order: `D :=` the chosen roots | 0 | I lo, I hi (`ζ` moved) | rejected |

How the attack replay is built:
- Each read has two fake openings, roots `d⁰ ≠ d¹` (the top sibling changed). Neither root is a cap
  entry.
- At `ζ₀`, 512 GF(2) equations in 871 unknowns are solved for the choice. The solution flips 259
  reads.
- This is PB-m12's `attack_neg` as a V-run control, together with the A3′-order case.

**Dumps** (`logs/A2pp/dump/`, `SHA256SUMS`; script `logs/A2pp/dump.sh`):
- the files: `ops-{L30,L31,L32,N2,N4,N8}.txt`, `group-{N,S}.txt`, `items.json`, `summary.txt`,
  `fsummary.txt`, `last.txt`, `capkat.txt`;
- `asks = items: true` for all six kinds;
- `piDigestAt`: 0 everywhere;
- `fsItems` 486.

| Kind | ops | skeleton | finals (incl. the cap check) | registers | items |
|---|---|---|---|---|---|
| L30 / L31 / L32 | 151,226 | 61,269 | 89,956 | 143,392 | 8,783 |
| N2 / N4 / N8 | 151,474 | 61,177 | 90,296 | 143,640 | 8,783 |

Against A2′ (N4 147,211): +4,263 ops.
- **Skeleton, +864:**
  - +1,742: two more ops per position;
  - −882: 126 fewer Merkle steps at level 4 (L2);
  - +4: the two new phases' `piField`/`askAbsorb` and `askSqueeze`/`chF`.
- **Finals, +3,399:** the cap check is now 45,863 ops.

`items.json` ends:

| Item (0-based) | Phase | Kind | Bytes |
|---|---|---|---|
| 8,778 | `Pf` | squeeze | |
| 8,779 | `CapD` | absorb | `len` 27,872, `qlen` 27,912 |
| 8,780 | `CapZeta` | squeeze | |
| 8,781 | `CapChk` | absorb | `len` 49,152, `qlen` 49,192 |
| 8,782 | `CapChkZ` | squeeze | |

**Node dumps** (`logs/A2pp/nodedump/`; `nodedump4`, `planform4`, `protodump` with the regenerated
hint; `SHA256SUMS`):
- the plan-form KAT `planform_kat.py`:
  - prototype 0: 667,209 rows rebuilt, 0 differ;
  - prototype 1: 657,301 rows rebuilt, 0 differ;
  - **KAT PASS** (`planform-kat.log`).
- `FRNodeRows4Hint` is regenerated in the worktree (`laydump4`, `logs/A2pp/laydump4.log`). Its
  `.maskN` route carries the new chain lengths (24,220 / 96,880 / 48,440).

**Source rule.** `python3 -I logs/org20/scripts/source-rule.py submissions/flock-recursive`: 364 files,
0 findings (`logs/A2pp/source-rule.log`).

**Axioms** (`logs/A2pp/Axioms.lean`, `axioms.log`). 64 theorems of the touched modules, the new
controls included: `propext`, `Classical.choice`, `Quot.sound` or fewer. No `sorryAx`. The worktree
has no `sorry`.

## 5. For A3′: the red set, exactly

**Method.** I used A2′'s scan (`logs/A2pp/scan/scan.sh`, `errdecls.py`, `sorry.py`), in the build tree
only:
- Each failing declaration of a module that is not this track's had its proof replaced by `sorry`,
  round by round (`round-*.txt`, `build-*.log`).
- After 7 rounds, `lake build FR Solution FRSoundness4TailShift FRSoundness4XCtrl FRNodeSound4Ctrl`
  is **green** (`build-7.log`, 2,581 jobs).
- Two declarations needed a hand edit in the scan copy (`copies/*.diff`):
  - † `fsCheck_qOf`'s statement carries a bound, `q < 482` → `486`;
  - ‡ `gLvsOps_4` is an equation-compiler proof, so the whole proof was sorried.
- The build tree was then re-snapshotted, so `src/` is HEAD + worktree again.

**The build failures. The complete list: with these 10 sorried, the build is green.**

| Module | Declaration | Why |
|---|---|---|
| `FRSoundness4TailD` | `phOf_ge` | `468 ≤ p → phOf4 p = 51` is false: phases 52–55 at 482–485 |
| `FRSoundness4TailD` | `rounds_check` | `fsItems4.length == 482` → 486 |
| `FRSoundness4TailC` | `tailCls_check` | positions 482–485 are in no class |
| `FRSoundness4R4Run` | `fsMsgs4_len` | 482 → 486 |
| `FRSoundness4R4Run` | `fsCheck_qOf` † | the statement's bound (`q < 482` against `fsItems4_length = 486`) |
| `FRSoundness4R4Run` | `matches_fsQ4` | `es.length = 482` |
| `FRSoundness4R4Run` | `finOps4_eq` | false: `finOps4 P = (relocFin …).ops ++ capChkOps …` (as at A2′) |
| `FRSoundness4R4PosT` | `exec_posOps4` | false: the reference `posT4` compares `cur` with the cap entry at `capO + 32k`; V now reads `D_r` statically and asserts `cur = D_r` |
| `FRSoundness4R4Qv` | `genPhase4_queries_ops` | false: the queries phase passes `dOff4 S i`, not `fieldOffOf S fCaps + capOff4 S i` |
| `FRSoundness4R4PfRun` | `gLvsOps_4` ‡ | **proof only, statement still true**: its `have h : seq4.lv = lvlStar` is false at level 4 (cap 8), but `gLvOps` reads only `(S.lv k).ell`, which L2 does not change |

**Statements that are now false but compile behind those sorries.** The scan cannot see these; I
derived them from their statements and the dependency graph.

1. **The arity coincidence.** HEAD's R4 modules still call `posOps4 S k i co so capO …` (A2′ did not
   restate them). `posOps4`'s fifth number is now `dO`, so these calls typecheck with `capO` in the
   `dO` slot, and say something false. This is why A2′'s `opsOut_posOps4` and `genPhase4_out_lt` no
   longer fail: `opsOut_posOps4` is **true** (`posW4` is `4 + 6·sL + 2`, and it counts ops, not
   offsets).

   Affected: `R4PosT.exec_posAll4` (from `exec_posOps4`); `R4Qv.exec_queries4`,
   `queries_view4` (its last conjunct, a path on `L` to π's cap entry, is no longer what the run
   checks); `R4PosT.posT4`/`posAllT4` as references.

   Restate them with `dO := dOff4 seq4 i`, and the per-position tail as `piDigest` then
   `assertEq cur D_r`.
2. **The `cols` chain** (as at A2′):
   - `FRSoundness4R4Cols.ys_facts4` → `cols4_of_run` → `FRSoundness4R4LinkP.finRest4_of_fields`,
     `link4_of_fields`, which give `(openPath …).runLog L = some (capDig …)`.
   - Now the run gives `= some (dAt es i q)`, the committed digest (PACK §11.5). `capDig` follows only
     under `truthCap`.
3. **`≤ 51` and the phase table** (A2′'s list, now with phases 52–55):
   - `FRSoundness4TailD.phOf_bounds`;
   - `FRSoundness4TailC` (`chainStab_of`, `phOf_ge_26`, `phOf_lt_26`, `phaseObl_of`, `tail_cls`);
   - `FRSoundness4TailM.DT_stab`;
   - `FRSoundness4TailStep.phOf_examples`;
   - `FRSoundness4P4aDF` (`hstab4a`, `phOf4_eq`);
   - `FRSoundness4P4fObl` (`chain_hi`, `hstab_hi`);
   - `FRSoundness4XFront` (`frontChainStab_X`, `phOf4_le12`).
4. **Every `482` in an R4 statement becomes `486`:** `R4At.SkRun4` (`len`, `hq`),
   `R4Run.runLog_chain4`, `R4Tail.acceptTail4_of_finLog` (`hlen`). At 482 these are vacuous (an
   accepted run has 486 entries). `R4FrE.msg_abs4 (hq : q < 482)` stays true.
5. `R4Acc.fields_of_accept4`, `R4Fld.fields4_of_accept` and `R4Ex.fields_ex4` use `finOps4_eq`:
   - their statements stay true;
   - their proofs must split off the appended ops (as at A2′).

**What A3′ needs from this track, by name.**

- **Ladder.**
  - `CKind.lv κ i = seq4.lvK κ.m i = lvOf κ.m i`. All three agree by definition, and
    `R4Cols.lvK_eq4` still holds by `rfl`.
  - `lvOf` is now revision 4.4.1's ladder: level 4's cap is 8, `sib` is 4/3/2 at `m = 32/31/30`.
  - 3.x's `lvlStar`/`ladder32` keep cap 7, so `seq4.lv ≠ lvlStar` at level 4. Wherever a proof used
    `seq4.lv = lvlStar` (`gLvsOps_4`), use the `ell`/`t`/`sq` equalities, which hold at every level.
- **Registers of a position** (from its column fold `y`, `ysOf fi i`'s entry):
  - `curOfY sL y`: the path root;
  - `kOfY sL y = y + 6sL + 1`: the cap index;
  - **`dOfY sL y = y + 6sL + 2`**: `D_r`, read by `.piDigest 0 (dOff4 seq4 i + 32p)`.
- **The position's tail:** `[.shrN b sib, .piDigest 0 (dO + 32p), .assertEq (curOfY sL (b+3)) (b + 4 + 6 sL + 1) allK]`.
- **Phases:** `CapD` 52 (FS 482, absorb `fD`, 27,872 B), `CapZeta` 53 (FS 483), `CapChk` 54 (FS 484,
  absorb `fA`, 49,152 B), `CapChkZ` 55 (FS 485).
  - `phOf_ge`'s split: `468 ≤ p < 482 → 51`, then `482 → 52`, `483 → 53`, `484 → 54`, `485 → 55`.
- **`dAt es i q`:** the 32 bytes at offset `32·r(i,q)` of the CapD absorb's message, with
  `r(i,q) = capReadsBelow seq4 i + q`.
- **`ζ` and `z`:**
  - `ζ = chK` of phase 53's answer; `z = chK` of phase 55's answer.
  - In `capChkOps` these are `(outs[nP − 3]).head − 1` and `(outs[nP − 1]).head − 1`, with
    `nP = (phasesOf seq4).length = 56`.
- **`A_k`:**
  - `A_k = K.ofBytes` of π at `fieldOffOf seq4 fA + 32k = 826,128 + 32k`, for `k < 1,536`;
  - caps at `fieldOffOf seq4 fCaps + 32k = 19,872 + 32k`;
  - `offᵢ = capEntriesBelow seq4 i = 0, 512, 768, 1024, 1280`.
- **Escape-set counts** (PB-M1's chain; not restated here):
  - `D_ζ ≤ 870`;
  - `D_z ≤ 1,535`, the degree being `< capEntries seq4 = 1,536`.
- **`finOps4`:** `finOps4 P outs b Q = ((finalsOf P Q).ops outs b ++ capChkOps P.S outs (b + opsOut …)).map (reloc P.S)`,
  as at A2′. `capChkOps`'s internal layout is closed-form (§6).

## 6. For B2′: the interim form, and what to template

`capChkOps S outs b` (registers from `b`; `M = capMax = 9`, `R = 871`, `E = 1,536`) is five regular
families, each a run of equal-width blocks at a constant stride:

| Family (future key) | Ops | Registers | Inputs |
|---|---|---|---|
| head (`tplSqChain` + weights) | `const 1`, `const 0`, `chK ζ`, `chK z`, `M` squarings `z^{2^t}` (`b+3+t`), 4 level weights `z^{offᵢ}` (`wb + i − 1`, `wb = b + 4 + M`) | 17 | the two squeeze answers |
| ζ chain (`tplPowChain`) | `mulK (powReg b pb r) ζ` for `r < R − 1`: `ζ^{r+1}` at `pb + r`, `pb = wb + 4` | 870 | `ζ` |
| z chain (`tplPowChain`) | the same for `z`, `E − 1` steps from `qb = pb + R − 1` | 1,535 | `z` |
| bit power (`tplBitPow`), per read `r` | `bitOf k_r t`, `selectHalf bit 1 z^{2^t}`, `mulK` running product from `z^{offᵢ}`, `t < M` (**uniform `M = 9` bits for every level**) | 27 per read, stride 27 from `bb = qb + E − 1` | `k_r` register (`kOfY`), `z^{2^t}`, weight |
| MAC-D (`tplMacD`), per read | `splitDigest D_r`, `mulKF ζ^r lo`, `addK`, `mulKF ζ^r hi`, `addK`, `mulK ζ^r zk_r`, `addK` | 8 registers (7 ops) per read, stride 8 from `db = bb + 27R` | `D_r` register (`dOfY`), `ζ^r`, the bit power's output |
| MAC-A (`tplMacA`), per entry `k` | `piElemK 0 (aO + 32k)`, `piElem 0 (cO + 32k)`, `piElem 0 (cO + 32k + 16)`, `mulKF`, `addK`, `mulKF`, `addK`, `mulK A_k z^k`, `addK` | 9 per entry, stride 9 from `ab = db + 8R` | `z^k`; `aO`, `cO` absolute |
| asserts | `assertEq aL sL`, `aH sH`, `aZ sZ` | 0 | the last block of each MAC family |

- Total: 45,863 ops per program.
- Running sums start at the `0` register (`b + 1`). Every register base is closed-form in `r`/`k`
  (`aD r j = db + 8(r − 1) + j`, `aA k j = ab + 9(k − 1) + j`), so one key per family covers every
  instance.
- The per-position change is two ops in the position block: a static `piDigest` (a fixed arena alias
  once the arenas exist) and an `assertEq`.
- **What the plan sees now.** The Merkle instances are back (5,396). The remaining
  ≈ 63.8 k sparse rows per prototype are this check, in the order above.
- `FRNodeRows4Hint` is regenerated at this program (`laydump4`). B2′ regenerates it again after its
  templates.

## 7. For P2 (`prover/`)

- **The format.** `|π| = 875,280`; field offsets in `dump/summary.txt` (`fieldOffs`).

  | Field | Offset | Bytes | Content |
  |---|---|---|---|
  | 18 `D` | 798,256 | 27,872 | read `r`'s path root, 32 bytes each, `r` in item order (levels 0–4: 290, 178, 145, 132, 126 positions) |
  | 19 `A` | 826,128 | 49,152 | `A_k = K.toBytes (Σ_{r : offᵢ₍ᵣ₎ + k_r = k} ζ^r)`, `k < 1,536`, **no pad** |

  - `k_r = j_r >>> sib_κ(i)`.
  - Level 4's cap has **256** entries. It is absorbed in level 3's `C` phase (8,192 B; caps field
    49,152 B).
  - Level 4's siblings are 4, 3 and 2 at `m = 32`, 31 and 30. The sibling field is 237,632 B.
- **The transcript.** After `Pf`'s last squeeze:
  1. absorb `D` (`|q| = 27,912`);
  2. squeeze `ζ` (`ζ = K.ofBytes` of the answer);
  3. absorb `A` (`|q| = 49,192`);
  4. squeeze `z`.

  The stream is 1,550,080 = 64 · 24,220 bytes, whole blocks. There are 8,783 items, and
  `qV ≥ 4 · 8,783 + 3 = 35,135`.
- **The honest-witness KAT.** `dump/capkat.txt`; its reference computation of `A` is `honestA` in
  `probe/IRDumpA2pp.lean`.
- **The node.**
  - `segB 1,550,080`, `cLen 24,220`.
  - `aggB k = 1 + k · 1,550,079` (no spacers: A1′'s are not in this tree, PB-m11).
  - `hUsed` N2 / N4 / N8 = 73,965 / 122,411 / 195,080, with L1: one `WM` per signed child.

## 8. Deviations

1. **`reloc` keeps `f < 19` (PB-m1 asked for 20).**
   - `fieldOffA` (FRVIR, 3.x) has 19 entries, so `absOff 19 o = o`, while `fieldOffOf seq3 19 + o =
     797,904 + o`. With `f < 20`, `evalOp_reloc_seq3` (3.x's fidelity control, and through it
     `finOps4_seq3`) would be false at `f = 19`.
   - The cap check therefore reads `fA` and `fCaps` by absolute offset (`macAOps`), as the positions
     read `fD` (`dOff4`, PB-m4). PB-m1's failure, an honest proof rejected, does not arise: the KAT
     accepts the honest run.
   - If the orchestrator prefers the literal fix, `evalOp_reloc_seq3` needs a hypothesis on field 19.
2. **`lvOf` is redefined to `seq4.lvK`** (it was 3.x-capped `ladderOf`), and `CKind.lv` is re-pointed
   to `seq4.lvK`.
   - The two are equal by definition, so T4's `rfl`s (`hLk : CKind.lv κ i = lvOf κ.m i`) and
     `lvK_eq4` keep working.
   - `lvOf_32`, which had no users, is restated (levels 0–3 only, plus the level-4 control).
   - This is PB-M2 (ii) "or an equivalent".
3. **The bit power is uniform, 9 bits for every read** (A2′: the level's cap bits). This costs
   +3 × 581 ops for levels 1–4. It gives one key and one stride for every read (item 3 of the brief).
4. **The memo's `|π|` 875,312 is 32 B too large.** The kernel value is 875,280 (`piSizeOf_seq4`).
5. **`FRNodeRows4Hint` is written to the worktree** (B0's module), as the brief asks. B0's
   uncommitted hint in the main worktree is a different file at a different program. Whichever lands
   second reruns `laydump4`.
6. **The KAT is a full V run under a programmable oracle**, not `capChkOps` alone (A2′'s form). The
   other 237 failing ops are the random π's PIOP checks, constant across the cases.

## 9. Open questions

1. PB-m1: accept the absolute-read form (deviation 1), or restate `evalOp_reloc_seq3` for a 20-field
   `reloc`?
2. `FRSoundness4Qry`'s ≈ 25 s of `simp` (A2′ saw it too): worth a golf pass before the certificate's
   600 s budget is re-measured?
3. A1′'s spacers move `aggL`/`hUsed` by +6 blocks per aggregate (N8 195,092). The fit holds (484
   blocks of headroom, per PB-m5). A1′ and this track both edit `FRNodeKinds4`/`FRNodeLayout4`
   literals and must be sequenced (PB-m11).
