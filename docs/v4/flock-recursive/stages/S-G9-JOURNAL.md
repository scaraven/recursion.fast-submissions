# S-G9 JOURNAL: the front's assembly (`DF`, `FrontObl`, `FrontChainStab`, `NodeL`, `kstate_front`)

- Base HEAD `62a25fb`. Build tree `logs/fr-build-SG9` (a copy of `fr-build-SG8`, `.lake` included;
  `snap.sh` re-reads HEAD and symlinks `FRSoundnessFr*`, `FRSoundnessAccSem`, `FRSoundnessAccLog`).
  Logs in `logs/S-G9/`. No sub-agents; every lean/lake command capped (16G builds, 12G single files)
  under `timeout`. Nothing committed.
- The tree builds the base modules from cache (`b.sh FRSoundnessFrZM FRSoundnessCompose
  FRSoundnessFrExt FRSoundnessAccSem`: 2,345 jobs, 3.4 s).

## 1. Positions (checked by `#eval` in a scratch file, `logs/fr-build-SG9/scratch/Items.lean`)

`A` absorb, `S` squeeze, `r` inside a multi-squeeze range (`fsRnd ≠ none`); `/k` is `phOf`.

| k | positions | items | phase |
|---|---|---|---|
| 0 | 0 | seed | — |
| 1 | 1 | A | hdr |
| 2 | 2 | A | cap₀ (range (2,10) starts) |
| 3 | 3–12 | S r | Z1 |
| 4 | 13, 14 | A, S | Z2 |
| 5 | 15–66 | A (odd), S (even) | Z3 rounds (b = 15) |
| 6 | 67 | A | Zend |
| 7 | 68 | S | L1 |
| 8 | 69–96 | A (odd), S (even) | L2 rounds (b = 69) |
| 9 | 97 | A | L3 |
| 10 | 98 | S | L3β (range (98,15) starts) |
| 11 | 99–113 | S r | S1 |
| 12 | 114–169 | A (even), S (odd) | S2 rounds (b = 114); range (169,8) starts at 169 |
| 13 | 170–177 | S r | Lr1 |
| 14 | 178–207 | A (even), S (odd) | Lr2 (b2 = 178) |
| 15 | 208 | A | Lr end |
| 16 | 209 | S | Lr3 `κ_L` (range (209,11) starts) |
| 17 | 210–220 | S r | E1 |
| 18 | 221–262 | A (odd), S (even) | E2 (b2 = 221) |
| 19 | 263 | A | E end |
| 20 | 264 | S | E3 `κ_E` |
| 21 | 265–310 | A (odd), S (even) | E4 (b = 265) |
| 22 | 311 | A | E4 end |
| 23 | 312 | A | RS0 (range (312,4) starts) |
| 24 | 313–316 | S r | RS1 |
| 25 | 317 | S | B′ |

## 2. The phase lemmas (exact statements extracted by grep; `M := zlmFR`)

| Phase | Lemma | Hypotheses | Conclusion |
|---|---|---|---|
| Z1 (2→3) | `z1_hfin` | `M.Bits`, `Reads 3 Bg`, `hprev : Dk (phOf 2) → Bg ∨ ¬ZHolds M`, `hfin : Dk (phOf 3) = msD (Dk (phOf 2)) fin 2 10`, `hfinI : Bg ∨ ZEnd M → fin`, `es₀.length = 3` | `condCount … 10 [] ≤ deltaR` |
| Z2 abs 13 | `z2_habs` | `len 13`, `ZEnd M` | `Z2D M (es++[x])` |
| Z2 sq 14 | `z2_single` | `len 14` | `card (Z2D ∧ ¬Z2D ext1) ≤ 126·2^128` |
| Z3 abs 15 | `z3_habs` | `len 15`, `Z2Bad M` | `D3Z M ∨ PendZ` |
| Z3 rounds | `z3_single`; `D3_append_iff` (`TZ_local`) | — | `≤ 3·2^128`; absorbs keep `D3Z` |
| Zend 67 | `zend_habs` | `len 67`, `D3Z M` | `RejZ M ∨ ZendBad M` |
| L1 68 | `l1_single` | `len 68` | `card (ZendBad ∧ ¬L1Bad ext1) ≤ 1·2^128` |
| L2 abs 69 | `l2_habs` | `len 69`, `L1Bad M` | `D2L M` |
| L2 rounds | `l2_single` (hchk from `chk_of_not_rejL2`); `D2_append_iff` (`TL_local`) | — | `≤ 2·2^128` |
| L3 97 (leaf) | `l3_habs` | `len 97`, `isNode = false`, `D2L M` | `RejLc2 M ∨ L3Bad M` |
| L3β 98 (leaf) | `l3b_single` | `M.IndKinds`, `len 98` | `card (L3Bad ∧ ¬PendLc ext1) ≤ 7·2^128` |
| S1 (98→99) | `s1_hfin` | `Reads 99 Bg`, `hprev : Dk (phOf 98) = Bg ∨ ¬truthS` (equality), `hfin : Dk (phOf 99) = msD … (Bg ∨ S2Bad) 98 15`, `len 99` | `condCount … 15 [] ≤ deltaR` |
| S2 abs 114 | `habs_S2` | `len 114`, `S2Bad` | `D2S (es++[x])` |
| S2 rounds | `single_S2` (hchk from `chk_of_not_rejS2`), `append_S2` | — | `≤ 2·2^128` |
| Lr1 (169→170) | `lr_zc_hfin` | `Reads 170 Bg`, `hprev : Dk (phOf 169) = Bg ∨ RowsBad lRows 15 23 lrOn` (eq), `hfin` msD `(Bg ∨ ZCw … 169) 169 8`, `len 170` | `≤ deltaR` |
| Lr2 abs 178 | `lr_habs_outer` | `len 178`, `ZCw lRows … 169` | `D3 178 …` |
| Lr2 rounds | `lr_single_outer`, `outer_append` | — | `≤ 3·2^128` |
| Lr end 208 | `lr_habs_end` | `len 208`, `D3 178 …` | `RejEnd 15 lrOn 169 178 ∨ EndBad lRows … 178` |
| Lr3 209 | `lr_single_batch` | `len 209` | `card (EndBad ∧ ¬BatBad lRows ext1) ≤ 2·2^128` |
| E1 (209→210) | `e_zc_hfin` | `Reads 210 Bg`, `hprev : Dk (phOf 209) = Bg ∨ RowsBad rows 21 23 lrOn` (eq), msD `(Bg ∨ ZCw rows … 209) 209 11`, `len 210` | `≤ deltaR` |
| E2 abs 221 | `e_habs_outer` | `len 221`, `ZCw rows … 209` | `D3 221 …` |
| E2 rounds | `e_single_outer`, `outer_append` | — | `≤ 3·2^128` |
| E end 263 | `e_habs_end` | `len 263`, `D3 221 …` | `RejEnd 21 lrOn 209 221 ∨ EndBad rows … 221` |
| E3 264 | `single_batchE` | `len 264` | `card ((EndBad rows ∨ BatBad lRows) ∧ ¬BatBadE ext1) ≤ 3·2^128` |
| E4 abs 265 | `habs_innerE` | `len 265`, `BatBadE` | `D4E` |
| E4 rounds | `single_innerE` (hchk `chk_of_not_rejInE`), `inner_appendE` | — | `≤ 2·2^128` |
| E4 end 311 | `habs_E4end` | `len 311`, `D4E` | `RejE4 ∨ PendE` |
| RS0 312 | `habs_RS0` | `OkReads ok`, `len 312`, `DPend ok` | `RejRS ok ∨ DRS0` |
| RS1 (312→313) | `hfin_RS1` | `hprev : Dk (phOf 312) = DRS0`, `hfin : … = msD … DRS1 312 4`, `len 313` | `≤ deltaR` |
| B′ 317 | `single_B` | `len 317` | `card (DRS1 ∧ ¬DB ext1) ≤ 10·2^128` |
| handoff 318 | `handoff_B` | `len 318`, `DB` | `D1 W₀L c₀L 0 (es++[x])` |
| bridges | `trueL_zero` (Z), `endS` (S), `trueL_three` (E), `zfL_leaf` (leaf Lc) | | claim `j`'s true value |
| Rej | `rejZ_ok` (67), `rejL2_ok` (69+2j), `rejLc2_ok` (97), `rejS2_ok` (114+2j), `e_rejEnd_ok` (263), `lr_rejEnd_ok`, `rejInE_ok` (265+2j), `rejRS_ok` (312) | item shapes | `RejOK` |

`RejE4 rows`: no `RejOK` lemma yet (reads 312, guarded `312 ≤ len`): `rejOK_at (p := 311)`.

## 3. Design of `DF` (backgrounds)

`A := far₀ ∨ ¬PubOK ∨ RowsBad lRows ∨ RowsBad (nodeRows fin)`; `NS := ¬truthS`.
`¬ Stmt fin SL → ¬ZHolds zlmFR ∨ NS ∨ A-parts` needs `RowsFit (nodeRows fin) 21 23` for E
(`truthE_iff`; QUEUE lists it as S-E's per-generator row count). It is a hypothesis.

| k | `DF k` |
|---|---|
| 0, 1 | `False` |
| 2 | `far₀ ∨ ¬Stmt fin SL` |
| 3 | `msD (DF 2) ((A ∨ NS) ∨ ZEnd) 2 10` |
| 4 | `(A ∨ NS) ∨ Z2D` |
| 5–9 | `B5 ∨ U` with `B5 := (A ∨ NS) ∨ PendZ`, `U` = `D3Z`, `ZendBad`, `L1Bad`, `D2L`, `L3Bad ∨ L3N` |
| 10 | `B10 ∨ NS`, `B10 := (A ∨ PendZ) ∨ (PendLc ∨ PendN)` |
| 11 | `msD (DF 10) (B10 ∨ S2Bad) 98 15` |
| 12 | `B12 ∨ RowsBad lRows`, `B12 := (A' ∨ PendZ ∨ PendLc ∨ PendN) ∨ D2S`, `A' := far₀ ∨ ¬PubOK ∨ RowsBad E` |
| 13 | `msD (DF 12) (B12 ∨ ZCw lRows 169) 169 8` |
| 14, 15 | `B12 ∨ D3 178 …`, `B12 ∨ EndBad lRows 178` |
| 16 | `B16 ∨ RowsBad E`, `B16 := B20 ∨ BatBad lRows 178` |
| 17 | `msD (DF 16) (B16 ∨ ZCw E 209) 209 11` |
| 18, 19 | `B16 ∨ D3 221 …`, `B16 ∨ EndBad E 221` |
| 20–22 | `B20 ∨ U`, `B20 := far₀ ∨ ¬PubOK ∨ PendZ ∨ PendLc ∨ PendN ∨ D2S`, `U` = `BatBadE`, `D4E`, `PendE` |
| 23 | `DRS0` |
| 24 | `msD DRS0 DRS1 312 4` |
| 25 | `DB` |

Stability: the front's dooms read `L` only through `f⁽⁰⁾` (word 0, `capPos 0 = 2`); every
`hstab`/`FrontChainStab` hypothesis is `Same L X L' X X.length`, so each part is shown stable under
it on logs at least as long as its phase start.

## 4. Log

- `FRSoundnessFrDF` (SLeaf, okF + bridges, NodeLF, DF, stmt_split, dPend_of, rejE4_ok, RejF):
  green. Lessons: section `variable` order fixes argument order (put `fin` first in its own
  section); `rcases` patterns must mirror the Or nesting, else it destructs the last atom.
- `FRSoundnessFrStab` (`SS q P`, df_ss, df_stab, ss_rejF, frontChainStab): green. Every part is
  stable under `Same L X L' X X.length` on `X` of at least its phase start; `D3_same` etc. need
  explicit thresholds (`SS.up`).
- `FRSoundnessFrObl`: `frontCls_check` (one pass over `(fsItems.take 318).zipIdx`, `decide
  +kernel`, cheap), `nsq_check` (the absorbs the `RejOK`s ask about), `obl_habs`, `obl_single`,
  `obl_ms`, `obl_hfin`, `frontObl`: green. Lessons: `tauto` blows the recursion limit on these
  dooms (it unfolds them): use explicit `Or` injections. A compound `U` in `card_frame2` gives a
  `propDecidable (A ∨ B)` instance against the unit lemma's `instDecidableOr`: close by
  `convert … using 3`.
- `FRSoundnessFrK` (`AccFront`, `NodeL`, `rejF_split`, `kstate_front_of`): green.
- The snapshot no longer symlinks `FRSoundnessAccSem`/`FRSoundnessAccLog`: INT-5 edits
  `FRSoundnessAccLog` in the worktree (it names INT-5's in-progress `dotOps_noAsk`, `lcHead`); HEAD's
  versions are used.
- Item 5 (`hStart`, `hW0`, `hFrontV`) is not discharged: `kstate_front_of` takes them as named
  hypotheses in `hAcc_of_fin`'s exact form. Handover in the RESULT.
- Controls added to all four modules; `SS` renamed `SameStab` (clash with `FR.X.SS`). Final
  build green (2,384 jobs); axioms 122 decls standard only; source rule 173 files, 0 findings;
  sequential profiles in `logs/S-G9/time-*.log` (`FRSoundnessFrObl` 28.8 s wall, 11.4 s type
  checking; a 15 s `omega` over `fsRanges`' 15-way disjunction replaced by `rcases`).
- Stopped after items 1–4 and the composition (`kstate_front_of`); item 5 handed over in the
  RESULT §5.
