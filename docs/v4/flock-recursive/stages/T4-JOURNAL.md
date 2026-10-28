# T4 JOURNAL: the Ligerito tail (P1.i … Pf) at revision 4.1's `seq4`

- Base: HEAD `7e14be6` (branch `v4/flock-recursive`, S-G13 pass 1). Build tree `logs/fr-build-T4`
  (a copy of `fr-build-SG13` with its `.lake`, `logs/org20`; `MINE.txt` lists T4's modules). Logs
  in `logs/T4/`. `lake build FR` on HEAD in the new tree: green, 2,428 jobs, cached (`build-0.log`).
- Every lean/lake command runs in the 16G scope (12G for single files) under `timeout`. No
  sub-agents. Nothing committed. No existing module edited.

## 1. Method: a mechanical copy-port with a dependency audit

1. **Which declarations to copy** (`logs/T4/deps.txt`, script `fr-build-T4/scratch/Deps.lean`, run
   outside the entry): a 3.x tail declaration is copied iff its statement (type, plus the value of a
   definition), followed transitively through definitions, reaches a 3.x root: `fsItems`, `items`,
   `fsStarts`, `fsRanges` or `Kind` (`lvlStar` is a leaf: the item sequence's level, kind-free). Of
   the 17 tail modules (`StepA…E`, `Truths`, `Hide`, `Walk`, `Phases`, `Weights`, `Fold`, `Tail*`,
   `Compose`, `LigFinal`, `Ligerito`), 195 user declarations are position-free (`keep.txt`:
   imported, not copied) and 489 are copied (`copy.txt`, including structure projections).
2. **The port** (`logs/T4/port/port.py`, `gen.sh`, `patches/*.py`): split each module into
   declaration chunks, drop the position-free ones and a short list of 3.x-only ones, rename the
   namespace to `FR.Snd.T4`, then rename:
   - everywhere: `phStart → phStart4`, `fsStarts → fsStarts4`, `fsItems → fsItems4`,
     `fsRanges → fsRanges4`, `fsRnd → fsRnd4` (and their `_eq`/`_ok`/`_zero`), `phOf → phOf4`,
     `rangesOK → rangesOK4`, `kindOf → kindOfC`;
   - in code: `Kind → CKind`, `lvl → CKind.lv`, the generic chain names of `FR.Snd.G`
     (`Matches`, `IsChain`, `chains`, `EscG`, `muG`, `muG_step_of`, …) to `G.*` (at `fsSeq4`), and
     `cases κ <;>` to the six-kind `rcases κ with (_|_|_) | (_|_|_) <;>`.
   Inside `FR.Snd.T4` a copied name shadows its 3.x original (Lean resolves the innermost
   namespace first; checked on a toy file), so every unchanged proof reads T4's copies and 3.x's
   position-free lemmas.
3. **Patches** (the semantic deltas, marked `T4:` in the sources): positions from P1.0 on `+14`
   (`capPos_eq`, `p1Start` table, `pfStart_eq = 468`, `phOf_examples`, `phOf_check`/`phOf_ge`/
   `rounds_check` at 482 items); the six-kind tables (`mLog_eq`, `cap_check`); `lv31_ok` (the
   `m = 31` ladder meets `mca_ud_line`'s hypotheses; `pcsLevels` is 3.x's two ladders); `fs_eq4`
   where a `G.Matches` unfolding meets `fsItems4` (two sites in `Hide`).
4. **Not copied**: the front's round phases `z3_*`, `lr2_phase`, `e2_phase` (P4's); 3.x's
   `kindOf_P30`/`kindOf_default` (S-G13's `kindOfC_ctrl`); `truthP1_zero` (B′'s handoff, unused,
   needs PIOP's `truthB'`); `stream_padded` (3.x's node stream); `kstate_of_front`, `ks_of_front`,
   `finalLaw_of` (3.x's verifier and `FinalLaw`), replaced by `muT_laws_of_front`,
   `tail_of_accept`, `ks4_of_front`. Copied from PIOP (not a tail module): `fF`, `msgOf_F`,
   `fTab_F` (`LigeritoOut.claim0` reads `fF`).
5. **Audit after the port** (`scratch/DepsT4.lean`, `logs/T4/deps-t4.log`): every one of the 568
   declarations of the T4 modules has a statement free of the 3.x roots. The one finding was
   `stream_padded` (via `FR.streamBytes`), which was then dropped.

## 2. Log

- Step module: 3 compile rounds (chunker fixes: `omit … in`/`open … in` prefixes travel with
  their declaration). Truths, Hide (two `fs_eq4` sites), Fold (`fF` from PIOP), Tail, TailD
  (`468 → 482`, `454 → 468`), TailO, TailM, TailC (`rangesOK4`), TailLig: each green after at
  most two rounds.
- Added (patches): `muT_laws_of_front` (TailC), `tail_of_accept`, `ks4_of_front` and T4's
  controls `tail_shift`, `nrP_kind`, `muT_laws_false` (TailLig). The first `tail_shift` proof
  unfolded 3.x's `p1Start`/`pfStart` with `simp`, which realized `FR.Snd.p1Start.eq_1`/
  `FR.Snd.pfStart.eq_1` inside a T4 module (a possible clash with any other module realizing
  them); rewritten with `show` and `phStart4_shift`. A `rfl` on `capPos 0` hit the recursion
  limit (it evaluates `fsStarts4`); replaced by `phStart4_shift.1`.
- HEAD moved to `4841734` (P4a, P4b pass 1) during the stage; `snap.sh` picked it up and the
  build stayed green. P4a/P4b's RESULTs ask T4 for `zW` (P4a) and for `Reads`/`card_frame`/
  `esc_msD_frame` (P4b, `FRSoundnessFront` Part A): both added (`zW`, `zBlk`, `zBlk_elem`,
  `zBlk_bool` in TailFold; new module `FRSoundness4TailFront`).
- Final: `lake build FR FRSoundness4TailFront` green (2,448 jobs); axioms over all 1,247
  constants of the 11 modules within `propext`, `Classical.choice`, `Quot.sound`; the source rule
  0 findings (229 files); the dependency audit leaves two intended hits (`tail_shift` compares
  with 3.x's positions; `ks4_of_front` mentions `FR.OpImpl`, whose `targetS` takes 3.x's `Kind`).
