# A2″ journal: (β′), the sound batched cap check, and levers L1 + L2 (PACK-4.4 §11)

Track A2″, 2026-10-29. Worktree `recursion.fast-submissions-rev44`, branch `v4/rev44`, HEAD `e4b7d5f`
(A2′'s tree with main merged). Build tree `logs/fr-build-A2pp` (copied from `logs/fr-build-A3`, A3′'s
tree with A2′'s oleans), logs `logs/A2pp/`. No sub-agents, nothing committed.

## 0. Reading

- PACK-4.4 §11 (β′) and its review `reviews/PACK-4.4-b2-review.md` (adopt with fixes): PB-M2 (L2's
  scope, `Seq.cap4`), PB-m1 (`reloc`), PB-m2 (`posW4 + 2`), PB-m3 (item numbers), PB-m4 (absolute
  `D` offset), PB-m5 (both levers needed), PB-m12 (`attack_neg` as a V-run control).
- A2′'s RESULT/JOURNAL (the construction this delta applies to), A3′'s RESULT (the attack).

## 1. Setup

- `logs/fr-build-A2pp` := `cp -a logs/fr-build-A3`; `snap.sh` rewritten (A3′'s fixed package paths,
  INT-9's `MINE.txt` and probe executables, and removal of files HEAD no longer has: `FRXRead4`).
  The probes (`probe/`), the dump tool (`dump/IRDumpA2.lean`), `run.sh`, `prof.sh`, `chk.sh` copied
  from the main worktree's `logs/fr-build-A2` (read only).

## 2. The change, in order

1. `FRTranscriptDefs`: `fD := 18`, `fA := 19` (3.x's `nFields` 18 untouched).
2. `FRShape4`:
   - `Seq.cap4 : ℕ := 7` (PB-M2 (ii)), threaded into `ladderOfR ell0 cap4 m`; `Seq.lvK` reads
     `S.cap4`; `seq4` sets `cap4 := 8`; `seq3` keeps 7, so `itemsOf_seq3`, `piSizeOf_seq3`, 3.x's
     `ladder32`/`lvlStar` and every module on them are untouched. `ladderOf m := ladderOfR 6 7 m`
     (3.x's; `ladderOf_32/30` stay `rfl`). `lvOf m i := seq4.lvK m i` (revision 4.4.1's ladder).
   - `lvOf_32` restated: levels 0–3 equal `lvlStar`, level 4's cap 8 vs 7 (it had no users).
     `ladder_sq_sib` restated over `lvOf` for `m = 32, 31, 30`: siblings at level 4 are 4, 3, 2.
   - `capReadsBelow`, `capReadsN`, `dBytes`; `aBytes` without the pad; `capChkPh` = the four phases
     `CapD` (absorb `fD`, 27,872), `CapZeta`, `CapChk` (absorb `fA`, 49,152), `CapChkZ`.
   - `nFields4 := 20`; `piSizeOf_seq3` reproved over two empty fields.
   - First build: every literal I predicted held at once: items 8,783, `piSize` **875,280**,
     stream 1,550,080 = 64·24,220, field sizes (caps 49,152, sibs 237,632, `D` 27,872, `A` 49,152).
   - **The memo's `|π|` 875,312 is 32 B too large**: it adds 4,096 to A2′'s 45,088 (pad
     included), while §11.4 item 1 drops the pad. 875,280 is consistent with the whole-block stream.
3. `FRVIR4`: `posOps4 … (dO)` ends `shrN`, `piDigest 0 (dO + 32p)`, `assertEq (curOfY sL (b+3))
   (b + 4 + 6 sL + 1)`; `posW4 = 4 + 6 sL + 2` (PB-m2); `dOfY`; `dOff4 S i := fieldOffOf S fD + 32 ·
   capReadsBelow S i` (absolute, PB-m4); control `dOff4_ctl` (the reads tile `D` exactly).
   `FRVIR4Mux.posOpsG` the same; `FRVIR4Uni` signatures.
4. `FRVIRFinals4.capChkOps` rebuilt in five regular families (head; two power chains; per-read bit
   power of uniform width `3·capMax`; per-read MAC-D of width 8; per-entry MAC-A of width 9), with
   closed-form register bases, `ζ` from `CapZeta` (phase `nP − 3`), `z` from `CapChkZ` (`nP − 1`),
   reads on the `D` registers (`dOfY`). π reads of `fA`/`fCaps` absolute.
   - PB-m1: `reloc`'s bound is **kept at 19**. Field 19 has no 3.x offset (`fieldOffA` has 19
     entries), so `f < 20` makes `evalOp_reloc_seq3` false at `f = 19`. The cap check reads `fA`
     absolutely instead, so the honest-proof failure PB-m1 describes cannot occur (KAT).
5. Literals: `FRSoundness4Pos` (486, `fsStarts4_eq` + 484, 485; `CKind.lv := seq4.lvK κ.m i`),
   `FRSoundness4Qry` (8,783; `items_posOps4`'s `dO`), `FRX4Prog`/`FRX4Ext` (875,280),
   `FRNodeKinds4` (`segB`, `cLen`, `hUsedN` with L1, `hEnd_eq`), `FRNodeLayout4` (`hUsed` with L1,
   `aggChainLen`, `hUsed_eq`, new `regions_need_levers`), `FRVIRTpl4Bridge`, `FRNodeRows4Pack`,
   `FRNodeRows4`, `FRNodeSound4R`, `FRVerifierImplNode4T` (`aggB 1 = 0x17A700`: bit 13 is `1`,
   bit 12 `0`).

## 3. First full build (`logs/A2pp/build-1.log`)

- All 19 touched modules build. `FR Solution FRSoundness4TailShift FRSoundness4XCtrl FRNodeSound4Ctrl`
  fails in `FRSoundness4TailD` and `FRSoundness4R4Run` only, A2′'s first-round pair (A3′'s).
- One slip on the way: `FRVIRFinals4.fin3P_S`'s anonymous `Seq` needed the new `cap4` field.

## 4. The KAT (`probe/IRDumpA2pp.lean`, compiled as `irdumpa2pp`)

- A2′'s KAT ran `capChkOps` on synthetic registers. (β′)'s questions are about the positions and the
  Fiat–Shamir order, so the new KAT runs the **whole `progNode .N4`** op by op (`evalOp`) under a
  consistent pseudo-random oracle, programmable at each position's top `askNode`. That is how an
  honest tree is made to end at the cap entry, which is absorbed before the positions exist.
- The reads are located in the op list by their static `D` reads, with their `idx`, `shrN`, column
  and sibling offsets and top ask. Each case follows the chain: positions → openings and `D` → `ζ`
  read from the run → `A` → the final run.
- First run (`capkat-1.log`, 3 min 50 s): **PASS**, in all six cases.
  - The attack's GF(2) solve flips 259 of 871 reads, and (I) holds at `ζ₀`: A3′'s forgery, confirmed.
  - Under (β′): with `D = d⁰` committed, the 259 flipped reads fail their asserts and (I) fails.
  - With `D :=` the chosen roots, `ζ` moves and (I) fails.

## 5. Dumps, hint, measurements

- `dump.sh` (`dump-run.log`, 4 min 29 s): ops 151,474 (N) / 151,226 (L); 0 `piDigestAt`;
  `asks = items` for all six kinds; items 8,783.
  - The last four items are `CapD` 8,779, `CapZeta` 8,780, `CapChk` 8,781, `CapChkZ` 8,782.
    PB-m3's numbering is confirmed.
- `laydump4` → `FRNodeRows4Hint` (worktree). The `.maskN` route's chain lengths change, so a stale
  hint would not fit.
- `vtime4 21 n4f` ×2 (core 30, load ≈ 16): best 423.3 / 434.5 ms; `evalMT4` 304.4 / 294.5 ms.
- `plan4t init` ×3 (core 29): 5.43 / 5.22 / 5.19 s, `inR true`.
- `plan4t check`: `equal true` for N2 / N4 / N8.
- `nodedump4`: 791,933 / 791,421 rows in region.
- `planform4`: sparse 103,872 / 100,468, instances 5,396. The Merkle instances are back, as A2′
  predicted.
- `planform_kat.py`: 0 differ, PASS.

## 6. The scan (`logs/A2pp/scan/`)

- Round 1: `TailD.{phOf_ge, rounds_check}` and `R4Run.{fsMsgs4_len, fsCheck_qOf, matches_fsQ4,
  finOps4_eq}`.
- Round 2: `TailC.tailCls_check`, and `fsCheck_qOf` again. That second failure is a statement break
  (its bound `q < 482`), edited to 486 in the copy.
- Round 3: `R4PosT.exec_posOps4`.
- Round 4: `R4Qv.genPhase4_queries_ops`, whose statement names the old `capO` offset.
- Rounds 5–6: `R4PfRun.gLvsOps_4`. `sorry.py` caught the inner `have`, so the whole proof was
  sorried by hand. Its statement is still true; only `seq4.lv = lvlStar` fails.
- Round 7: **green**, 2,581 jobs. Ten declarations in all.
- Fewer than A2′'s 13. HEAD's R4 calls `posOps4 … capO …` still typecheck, because the new `dO`
  argument sits in the old `capO` slot. So `opsOut_posOps4`/`genPhase4_out_lt` pass, `opsOut_posOps4`
  true, and the rest are listed as compiling-but-false in the RESULT §5.
- `src/` re-snapshotted afterwards.

## 7. Profiles, axioms, source rule

- `prof.sh` on core 26, load ≈ 10: 19 modules, 301.0 CPU-s in total (RESULT §2).
- `FRSoundness4Qry`'s `simp` (24.8 s) is the outlier, not new (A2′: 1:29 at load 20).
- Axioms: 64 theorems, standard only. Source rule: 364 files, 0 findings.

## For A3′ / For B2′ / For P2

See RESULT §5 (the red set, the false-but-compiling statements, the registers and offsets by name),
§6 (the five op families with their closed-form register bases) and §7 (the format, the transcript,
the node constants).
